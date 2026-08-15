import DominatorTree.Reducible
import Std.Data.HashMap

/-!
# Computing the dominator tree

For a graph carrying a topological rank — a DAG, or the back-edge-free part of a
reducible graph — every predecessor of `v` is ranked below `v`, so the tree can
be built in one pass with no fixpoint iteration.

`idom?` builds the tree directly: the parent of `v` is the lowest common
ancestor of `v`'s predecessors in the tree built so far, found by climbing
parent pointers. No lists of dominators are ever formed.

The climb terminates because the parent lookup returns a vertex *paired with a
proof* that its rank dropped, so the measure decreases by typing.

Dominance is not stored either: `domWalk` recomputes it by climbing from `v`
and looking for `u`.
-/

namespace DominatorTree

namespace DepGraph

variable {V : Type} {verts : List V}

/-- A rank that strictly increases along every edge: a topological numbering. -/
def TopoRank (g : DepGraph verts) (rank : Vertex verts → Nat) : Prop :=
  ∀ v u, u ∈ g.out v → rank v < rank u

/-- Checking a topological rank only needs the vertices actually listed, so this
form is decidable. -/
theorem topoRank_of_forall_mem {g : DepGraph verts} {rank : Vertex verts → Nat}
    (h : ∀ v ∈ verts.attach, ∀ u ∈ g.out v, rank v < rank u) : g.TopoRank rank :=
  fun v u hu => h v (List.mem_attach _ _) u hu

/-- A topological rank grows by at least the length of any path. -/
theorem topoRank_add_le {g : DepGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.TopoRank rank) :
    ∀ {u w : Vertex verts} (p : Path g u w), rank u + p.length ≤ rank w := by
  intro u w p
  induction p with
  | nil v => simp [Path.length]
  | @cons a b c hedge p' ih =>
    have hlt : rank a < rank b := htopo a b hedge
    simp only [Path.length]
    omega

/-- On a connected graph a strict dominator has strictly smaller rank, so the
dominance order agrees with the rank order. -/
theorem rank_lt_of_dominates {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {u v : Vertex verts}
    (hdom : g.Dominates u v) (hne : u ≠ v) : rank u < rank v := by
  obtain ⟨P⟩ := g.reach v
  obtain ⟨-, R, -, -, -⟩ := P.exists_split u (hdom P)
  have hRpos : 0 < R.length := by
    rcases Nat.eq_zero_or_pos R.length with h0 | h
    · exact absurd (Path.eq_of_length_zero R h0) hne
    · exact h
  have hle := topoRank_add_le htopo R
  omega

variable [DecidableEq V] [Hashable V]

/-- The predecessors of `v`. -/
def preds (g : DepGraph verts) (v : Vertex verts) : List (Vertex verts) :=
  verts.attach.filter (fun u => decide (v ∈ g.out u))

omit [Hashable V] in
@[simp] theorem mem_preds {g : DepGraph verts} {u v : Vertex verts} :
    u ∈ g.preds v ↔ g.Edge u v := by
  simp [preds, List.mem_filter, List.mem_attach, Edge]

omit [Hashable V] in
/-- On a connected graph every non-root vertex has a predecessor. -/
theorem preds_ne_nil {g : ConnectedGraph verts} {v : Vertex verts} (hv : v ≠ g.root) :
    g.preds v ≠ [] := by
  obtain ⟨P⟩ := g.reach v
  have hpos : 0 < P.length := by
    rcases Nat.eq_zero_or_pos P.length with h0 | h
    · exact absurd (Path.eq_of_length_zero P h0).symm hv
    · exact h
  obtain ⟨x, -, he, -⟩ := P.exists_last_edge_path hpos
  intro hnil
  have : x ∈ g.preds v := mem_preds.mpr he
  rw [hnil] at this
  simp at this

/-- Vertices hash by their label. -/
instance instHashableVertex [Hashable V] : Hashable (Vertex verts) := ⟨fun v => hash v.val⟩

instance [Hashable V] : LawfulHashable (Vertex verts) where
  hash_eq a b h := by
    have hab : a = b := Subtype.ext (by simpa using h)
    rw [hab]

/-- A dominator tree under construction: a map from each processed vertex to its
parent, or to `none` at the root. -/
abbrev Table (verts : List V) (_rank : Vertex verts → Nat) : Type :=
  Std.HashMap (Vertex verts) (Option (Vertex verts))

/-- The empty tree. -/
def Table.empty {rank : Vertex verts → Nat} : Table verts rank := ∅

/-- The recorded parent of `v`, paired with the proof that its rank dropped —
recovered by a check, which the correctness invariant shows always passes.

The proof is what makes climbing the tree terminate. -/
def Table.get {rank : Vertex verts → Nat} (tbl : Table verts rank) (v : Vertex verts) :
    Option {u : Vertex verts // rank u < rank v} :=
  match tbl[v]? with
  | none => none
  | some none => none
  | some (some u) => if h : rank u < rank v then some ⟨u, h⟩ else none

/-- Record the parent of `v`. -/
def Table.insert {rank : Vertex verts → Nat} (tbl : Table verts rank) (v : Vertex verts)
    (p : Option {u : Vertex verts // rank u < rank v}) : Table verts rank :=
  Std.HashMap.insert tbl v (p.map Subtype.val)

@[simp] theorem Table.get_insert_self {rank : Vertex verts → Nat} (tbl : Table verts rank)
    (v : Vertex verts) (p : Option {u : Vertex verts // rank u < rank v}) :
    (tbl.insert v p).get v = p := by
  simp only [Table.get, Table.insert, Std.HashMap.getElem?_insert_self]
  cases p with
  | none => rfl
  | some u =>
    obtain ⟨u, hu⟩ := u
    simp [hu]

theorem Table.get_insert_ne {rank : Vertex verts → Nat} (tbl : Table verts rank)
    {v x : Vertex verts} (p : Option {u : Vertex verts // rank u < rank v}) (h : x ≠ v) :
    (tbl.insert v p).get x = tbl.get x := by
  have hne : (v == x) ≠ true := fun hh => h (eq_of_beq hh).symm
  simp only [Table.get, Table.insert, Std.HashMap.getElem?_insert, if_neg hne]

/-- Climb `a` and `b` to their lowest common ancestor.

Terminates by typing: the table hands back a parent together with the proof that
its rank is smaller, so the measure visibly falls. -/
def lca {rank : Vertex verts → Nat} (tbl : Table verts rank) (a b : Vertex verts) :
    Option (Vertex verts) :=
  if a = b then some a
  else if rank b < rank a then
    match tbl.get a with
    | none => none
    | some ⟨a', _⟩ => lca tbl a' b
  else
    match tbl.get b with
    | none => none
    | some ⟨b', _⟩ => lca tbl a b'
termination_by rank a + rank b
decreasing_by
  · omega
  · omega

/-- Fold `lca` over a list of vertices. -/
def lcaAll {rank : Vertex verts → Nat} (tbl : Table verts rank) (a : Vertex verts) :
    List (Vertex verts) → Option (Vertex verts)
  | [] => some a
  | q :: qs =>
      match lca tbl a q with
      | none => none
      | some m => lcaAll tbl m qs

/-- A table is correct below `B` when it gives the immediate dominator of every
vertex of smaller rank. -/
def Correct {rank : Vertex verts → Nat} (g : ConnectedGraph verts) (tbl : Table verts rank)
    (B : Nat) : Prop :=
  ∀ x, rank x < B →
    (∀ u hu, tbl.get x = some ⟨u, hu⟩ → g.IsIdom u x) ∧ (x ≠ g.root → (tbl.get x).isSome)

/-- The climb returns the greatest common dominator of `a` and `b`.

Each step replaces the deeper of the two by its parent, which is sound because
any common dominator is a *strict* dominator of the deeper one — it is at most
as deep as the other — and so dominates that parent. -/
theorem lca_spec {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {B : Nat} {tbl : Table verts rank}
    (hok : Correct g tbl B) :
    ∀ (n : Nat) (a b : Vertex verts), rank a < B → rank b < B → rank a + rank b = n →
      ∃ m, lca tbl a b = some m ∧ rank m ≤ rank a ∧
        g.Dominates m a ∧ g.Dominates m b ∧
        ∀ w, g.Dominates w a → g.Dominates w b → g.Dominates w m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b ha hb hn
    rw [lca]
    by_cases hab : a = b
    · subst hab
      exact ⟨a, by simp, Nat.le_refl _, g.dominates_refl a, g.dominates_refl a, fun w hw _ => hw⟩
    · rw [if_neg hab]
      by_cases hlt : rank b < rank a
      · rw [if_pos hlt]
        have haroot : a ≠ g.root := by
          rintro rfl
          by_cases hbr : b = g.root
          · exact hab hbr.symm
          · have := rank_lt_of_dominates htopo (g.root_dominates b) (Ne.symm hbr)
            omega
        cases hpa : tbl.get a with
        | none => exact absurd ((hok a ha).2 haroot) (by rw [hpa]; simp)
        | some val =>
          obtain ⟨a', h'⟩ := val
          have hidom : g.IsIdom a' a := (hok a ha).1 a' h' hpa
          obtain ⟨m, hlca, hmle, hma', hmb, huniv⟩ :=
            ih (rank a' + rank b) (by omega) a' b (Nat.lt_trans h' ha) hb rfl
          refine ⟨m, hlca, by omega, hma'.trans hidom.1.1, hmb, fun w hwa hwb => ?_⟩
          have hwne : w ≠ a := by
            rintro rfl
            exact absurd (rank_lt_of_dominates htopo hwb hab) (by omega)
          exact huniv w (hidom.2 w ⟨hwa, hwne⟩) hwb
      · rw [if_neg hlt]
        have hbroot : b ≠ g.root := by
          rintro rfl
          by_cases har : a = g.root
          · exact hab har
          · have := rank_lt_of_dominates htopo (g.root_dominates a) (Ne.symm har)
            omega
        cases hpb : tbl.get b with
        | none => exact absurd ((hok b hb).2 hbroot) (by rw [hpb]; simp)
        | some val =>
          obtain ⟨b', h'⟩ := val
          have hidom : g.IsIdom b' b := (hok b hb).1 b' h' hpb
          obtain ⟨m, hlca, hmle, hma, hmb', huniv⟩ :=
            ih (rank a + rank b') (by omega) a b' ha (Nat.lt_trans h' hb) rfl
          refine ⟨m, hlca, hmle, hma, hmb'.trans hidom.1.1, fun w hwa hwb => ?_⟩
          have hwne : w ≠ b := by
            rintro rfl
            exact absurd (rank_lt_of_dominates htopo hwa (fun hh => hab hh.symm)) (by omega)
          exact huniv w hwa (hidom.2 w ⟨hwb, hwne⟩)

/-- Folding the climb gives the greatest common dominator of the whole list. -/
theorem lcaAll_spec {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {B : Nat} {tbl : Table verts rank}
    (hok : Correct g tbl B) :
    ∀ (qs : List (Vertex verts)) (a : Vertex verts), rank a < B → (∀ q ∈ qs, rank q < B) →
      ∃ m, lcaAll tbl a qs = some m ∧ rank m ≤ rank a ∧
        g.Dominates m a ∧ (∀ q ∈ qs, g.Dominates m q) ∧
        ∀ w, g.Dominates w a → (∀ q ∈ qs, g.Dominates w q) → g.Dominates w m := by
  intro qs
  induction qs with
  | nil =>
    intro a ha hq
    exact ⟨a, by simp [lcaAll], Nat.le_refl _, g.dominates_refl a, by simp, fun w hw _ => hw⟩
  | cons q qs ih =>
    intro a ha hq
    rw [lcaAll]
    obtain ⟨m1, hlca, hm1le, hm1a, hm1q, huniv1⟩ :=
      lca_spec htopo hok _ a q ha (hq q (by simp)) rfl
    rw [hlca]
    obtain ⟨m, hrec, hmle, hma, hmqs, huniv⟩ :=
      ih m1 (by omega) (fun x hx => hq x (by simp [hx]))
    refine ⟨m, hrec, by omega, hma.trans hm1a, ?_, ?_⟩
    · intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq''
      · exact hma.trans hm1q
      · exact hmqs q' hq''
    · intro w hwa hwall
      exact huniv w (huniv1 w hwa (hwall q (by simp))) (fun q' hq' => hwall q' (by simp [hq']))

/-- The parent of `v`, computed from a table already correct below `rank v`. -/
def parentOf (g : DepGraph verts) (rank : Vertex verts → Nat) (tbl : Table verts rank)
    (v : Vertex verts) : Option {u : Vertex verts // rank u < rank v} :=
  if v = g.root then none
  else
    match g.preds v with
    | [] => none
    | p :: ps =>
        match lcaAll tbl p ps with
        | none => none
        | some m => if h : rank m < rank v then some ⟨m, h⟩ else none

/-- `parentOf` returns the immediate dominator, and returns one whenever the
vertex has a parent to find. -/
theorem parentOf_spec {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {tbl : Table verts rank} {v : Vertex verts}
    (hok : Correct g tbl (rank v)) :
    (∀ u hu, parentOf g.toDepGraph rank tbl v = some ⟨u, hu⟩ → g.IsIdom u v) ∧
      (v ≠ g.root → (parentOf g.toDepGraph rank tbl v).isSome) := by
  rw [parentOf]
  by_cases hroot : v = g.root
  · rw [if_pos hroot]
    exact ⟨by simp, fun h => absurd hroot h⟩
  · rw [if_neg hroot]
    split
    · rename_i hp
      exact absurd hp (preds_ne_nil hroot)
    · rename_i p ps hp
      have hpv : g.Edge p v := mem_preds.mp (by rw [hp]; exact List.mem_cons_self)
      have hqv : ∀ q ∈ ps, g.Edge q v := fun q hq =>
        mem_preds.mp (by rw [hp]; exact List.mem_cons_of_mem _ hq)
      obtain ⟨m, heq, hmle, hmp, hmqs, huniv⟩ :=
        lcaAll_spec htopo hok ps p (htopo p v hpv) (fun q hq => htopo q v (hqv q hq))
      have hmall : ∀ q, g.Edge q v → g.Dominates m q := by
        intro q hq
        rcases List.mem_cons.mp (show q ∈ p :: ps from hp ▸ mem_preds.mpr hq) with rfl | hq'
        · exact hmp
        · exact hmqs q hq'
      have hmv : g.Dominates m v := (dominates_iff_preds hroot m).mpr (Or.inr hmall)
      have hmlt : rank m < rank v := Nat.lt_of_le_of_lt hmle (htopo p v hpv)
      have hmne : m ≠ v := by intro h; rw [h] at hmlt; omega
      rw [heq]
      dsimp only
      rw [dif_pos hmlt]
      refine ⟨fun u hu hres => ?_, fun _ => by simp⟩
      have hum : u = m := by simpa using hres.symm
      subst hum
      refine ⟨⟨hmv, hmne⟩, fun w hw => ?_⟩
      have hwall : ∀ q, g.Edge q v → g.Dominates w q := by
        intro q hq
        rcases (dominates_iff_preds hroot w).mp hw.1 with h | h
        · exact absurd h hw.2
        · exact h q hq
      exact huniv w (hwall p hpv) (fun q' hq' => hwall q' (hqv q' hq'))

/-! ## Building the tree incrementally

Vertices are processed in order of rank, each one's parent computed from the
table built so far and stored in it. Every parent is computed exactly once. -/

/-- Insert parents for a list of vertices, in order. -/
def levelStep (g : DepGraph verts) (rank : Vertex verts → Nat) (tbl : Table verts rank)
    (vs : List (Vertex verts)) : Table verts rank :=
  vs.foldl (fun t v => t.insert v (parentOf g rank t v)) tbl

/-- The vertices of rank exactly `n`. -/
def atRank (rank : Vertex verts → Nat) (n : Nat) : List (Vertex verts) :=
  verts.attach.filter (fun v => decide (rank v = n))

omit [DecidableEq V] [Hashable V] in
theorem mem_atRank {rank : Vertex verts → Nat} {n : Nat} {v : Vertex verts} :
    v ∈ atRank rank n ↔ rank v = n := by
  simp [atRank, List.mem_filter, List.mem_attach]

/-- The dominator tree for every vertex of rank below `n`. -/
def buildUpTo (g : DepGraph verts) (rank : Vertex verts → Nat) : Nat → Table verts rank
  | 0 => Table.empty
  | n + 1 => levelStep g rank (buildUpTo g rank n) (atRank rank n)

theorem levelStep_not_mem {rank : Vertex verts → Nat} (g : DepGraph verts) :
    ∀ (vs : List (Vertex verts)) (tbl : Table verts rank) (x : Vertex verts),
      x ∉ vs → (levelStep g rank tbl vs).get x = tbl.get x := by
  intro vs
  induction vs with
  | nil => intro tbl x _; rfl
  | cons v vs ih =>
    intro tbl x hx
    simp only [List.mem_cons, not_or] at hx
    rw [levelStep, List.foldl_cons, ← levelStep]
    rw [ih _ x hx.2, Table.get_insert_ne _ _ hx.1]

/-- Processing a batch of equal-rank vertices keeps the table correct below that
rank, and makes it correct at every vertex of the batch. -/
theorem levelStep_correct {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) :
    ∀ (vs : List (Vertex verts)) (tbl : Table verts rank) (n : Nat),
      Correct g tbl n → (∀ v ∈ vs, rank v = n) →
      Correct g (levelStep g.toDepGraph rank tbl vs) n ∧
      ∀ x ∈ vs,
        (∀ u hu, (levelStep g.toDepGraph rank tbl vs).get x = some ⟨u, hu⟩ → g.IsIdom u x) ∧
          (x ≠ g.root → ((levelStep g.toDepGraph rank tbl vs).get x).isSome) := by
  intro vs
  induction vs with
  | nil => intro tbl n hok _; exact ⟨hok, by simp⟩
  | cons v vs ih =>
    intro tbl n hok hvs
    have hvn : rank v = n := hvs v (by simp)
    have hstep : levelStep g.toDepGraph rank tbl (v :: vs)
        = levelStep g.toDepGraph rank (tbl.insert v (parentOf g.toDepGraph rank tbl v)) vs := by
      rw [levelStep, List.foldl_cons, ← levelStep]
    -- the extended table is still correct below `n`
    have hok' : Correct g (tbl.insert v (parentOf g.toDepGraph rank tbl v)) n := by
      intro x hx
      have hne : x ≠ v := by intro h; rw [h, hvn] at hx; omega
      rw [Table.get_insert_ne _ _ hne]
      exact hok x hx
    obtain ⟨hrest, hvsok⟩ := ih _ n hok' (fun q hq => hvs q (by simp [hq]))
    refine ⟨by rw [hstep]; exact hrest, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · by_cases hmem : x ∈ vs
      · rw [hstep]; exact hvsok x hmem
      · rw [hstep, levelStep_not_mem _ _ _ _ hmem, Table.get_insert_self]
        exact parentOf_spec htopo (hvn ▸ hok)
    · rw [hstep]; exact hvsok x hx'

/-- **Correctness of the construction**: after building up to `n`, the table
holds the immediate dominator of every vertex of rank below `n`. -/
theorem buildUpTo_correct {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) :
    ∀ n : Nat, Correct g (buildUpTo g.toDepGraph rank n) n := by
  intro n
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    obtain ⟨hbelow, hlevel⟩ :=
      levelStep_correct htopo (atRank rank n) (buildUpTo g.toDepGraph rank n) n ih
        (fun v hv => mem_atRank.mp hv)
    intro x hx
    rcases Nat.lt_or_ge (rank x) n with h | h
    · exact hbelow x h
    · have hxn : rank x = n := by omega
      exact hlevel x (mem_atRank.mpr hxn)

/-- The dominator tree: the parent of `v`, or `none` at the root. -/
def idom? (g : DepGraph verts) (rank : Vertex verts → Nat) (N : Nat) (v : Vertex verts) :
    Option (Vertex verts) :=
  ((buildUpTo g rank N).get v).map Subtype.val

/-- **Soundness**: what `idom?` returns is the immediate dominator. -/
theorem isIdom_of_idom? {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {N : Nat} {v u : Vertex verts} (hN : rank v < N)
    (h : idom? g.toDepGraph rank N v = some u) : g.IsIdom u v := by
  rw [idom?] at h
  cases h' : (buildUpTo g.toDepGraph rank N).get v with
  | none => rw [h'] at h; simp at h
  | some val =>
    obtain ⟨u', hu'⟩ := val
    rw [h'] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact (buildUpTo_correct htopo N v hN).1 u' hu' h'

/-- **Totality**: on a connected graph every non-root vertex gets a parent. -/
theorem idom?_isSome {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {N : Nat} {v : Vertex verts} (hN : rank v < N)
    (hv : v ≠ g.root) : (idom? g.toDepGraph rank N v).isSome := by
  rw [idom?, Option.isSome_map]
  exact (buildUpTo_correct htopo N v hN).2 hv

/-- Is `u` on the path from `v` to the root of the dominator tree?

Terminates by typing: the table's parent comes with its rank proof. -/
def domWalk {rank : Vertex verts → Nat} (tbl : Table verts rank) (u v : Vertex verts) : Bool :=
  if u = v then true
  else
    match tbl.get v with
    | none => false
    | some ⟨m, _⟩ => domWalk tbl u m
termination_by rank v
decreasing_by assumption

/-- **Correctness**: climbing the tree decides dominance.

One way it is transitivity — the parent dominates `v`, so anything dominating
the parent dominates `v`. The other way it is the defining property of an
immediate dominator: every strict dominator of `v` also dominates `v`'s
parent. -/
theorem domWalk_iff {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {N : Nat} {tbl : Table verts rank} (hok : Correct g tbl N) :
    ∀ (n : Nat) (v : Vertex verts), rank v = n → rank v < N → ∀ u : Vertex verts,
      domWalk tbl u v = true ↔ g.Dominates u v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv hvN u
    rw [domWalk]
    by_cases huv : u = v
    · subst huv
      simp [g.dominates_refl u]
    · rw [if_neg huv]
      cases h : tbl.get v with
      | none =>
        have hroot : v = g.root := by
          apply Classical.byContradiction
          intro hne
          have hsome := (hok v hvN).2 hne
          rw [h] at hsome
          simp at hsome
        subst hroot
        simp only [dominates_root_iff]
        exact ⟨fun hf => absurd hf (by simp), fun hu => absurd hu huv⟩
      | some val =>
        obtain ⟨m, hm⟩ := val
        have hidom : g.IsIdom m v := (hok v hvN).1 m hm h
        rw [ih (rank m) (by omega) m rfl (by omega) u]
        exact ⟨fun hum => hum.trans hidom.1.1, fun huv' => hidom.2 u ⟨huv', huv⟩⟩

end DepGraph

end DominatorTree
