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

/-- A connected graph together with a topological rank: the input the algorithm
is verified against.

The computation itself needs only a `DepGraph` and a rank — connectivity is what
makes the *answers* meaningful, so it is bundled here rather than demanded to
run the algorithm. -/
structure RankedGraph {V : Type} (verts : List V) where
  /-- The graph. -/
  graph : ConnectedGraph verts
  /-- A topological numbering of it. -/
  rank : Vertex verts → Nat
  /-- The numbering increases along every edge. -/
  topo : graph.toDepGraph.TopoRank rank

/-- The underlying graph, forgetting connectivity. -/
abbrev RankedGraph.dep {verts : List V} (R : RankedGraph verts) : DepGraph verts := R.graph.toDepGraph

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

/-- The deepest common dominator of a list of vertices. -/
def lcaOf {rank : Vertex verts → Nat} (tbl : Table verts rank) :
    List (Vertex verts) → Option (Vertex verts)
  | [] => none
  | [p] => some p
  | p :: q :: qs =>
      match lca tbl p q with
      | none => none
      | some m => lcaOf tbl (m :: qs)
termination_by qs => qs.length

/-- A table is correct below `B` when it gives the immediate dominator of every
vertex of smaller rank. -/
def Correct (R : RankedGraph verts) (tbl : Table verts R.rank) (B : Nat) : Prop :=
  ∀ x, R.rank x < B →
    (∀ u hu, tbl.get x = some ⟨u, hu⟩ → R.graph.IsIdom u x) ∧
      (x ≠ R.graph.root → (tbl.get x).isSome)

/-- `m` is the deepest common dominator of `a` and `b`. -/
def IsGCD (R : RankedGraph verts) (m a b : Vertex verts) : Prop :=
  R.graph.Dominates m a ∧ R.graph.Dominates m b ∧
    ∀ w, R.graph.Dominates w a → R.graph.Dominates w b → R.graph.Dominates w m

theorem IsGCD.symm {R : RankedGraph verts} {m a b : Vertex verts} (h : IsGCD R m a b) :
    IsGCD R m b a :=
  ⟨h.2.1, h.1, fun w hwb hwa => h.2.2 w hwa hwb⟩

/-- Replacing `a` by its parent preserves the deepest common dominator, provided
no common dominator of `a` and `b` is `a` itself: such a dominator is then a
*strict* dominator of `a`, so it dominates `a`'s parent. -/
theorem IsGCD.step {R : RankedGraph verts} {m a b a' : Vertex verts} (hidom : R.graph.IsIdom a' a)
    (hne : ∀ w, R.graph.Dominates w a → R.graph.Dominates w b → w ≠ a) (h : IsGCD R m a' b) :
    IsGCD R m a b :=
  ⟨h.1.trans hidom.1.1, h.2.1,
    fun w hwa hwb => h.2.2 w (hidom.2 w ⟨hwa, hne w hwa hwb⟩) hwb⟩

/-- The climb returns the deepest common dominator of `a` and `b`. -/
theorem lca_spec (R : RankedGraph verts) {B : Nat} {tbl : Table verts R.rank}
    (hok : Correct R tbl B) :
    ∀ (n : Nat) (a b : Vertex verts), R.rank a < B → R.rank b < B → R.rank a + R.rank b = n →
      ∃ m, lca tbl a b = some m ∧ R.rank m ≤ R.rank a ∧ IsGCD R m a b := by
  -- the deeper of two distinct vertices is not the root, so it has a parent
  have parent : ∀ c d : Vertex verts, R.rank c < B → R.rank d ≤ R.rank c → c ≠ d →
      ∃ c' h', tbl.get c = some ⟨c', h'⟩ ∧ R.graph.IsIdom c' c := by
    intro c d hc hle hcd
    have hcroot : c ≠ R.graph.root := by
      rintro rfl
      by_cases hdr : d = R.graph.root
      · exact hcd hdr.symm
      · have := rank_lt_of_dominates R.topo (R.graph.root_dominates d) (Ne.symm hdr)
        omega
    cases hpc : tbl.get c with
    | none => exact absurd ((hok c hc).2 hcroot) (by rw [hpc]; simp)
    | some val =>
      obtain ⟨c', h'⟩ := val
      exact ⟨c', h', rfl, (hok c hc).1 c' h' hpc⟩
  -- no common dominator of two distinct vertices is the deeper one
  have notDeeper : ∀ c d w : Vertex verts, R.rank d ≤ R.rank c → c ≠ d →
      R.graph.Dominates w c → R.graph.Dominates w d → w ≠ c := by
    rintro c d w hle hcd _ hwd rfl
    exact absurd (rank_lt_of_dominates R.topo hwd hcd) (by omega)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b ha hb hn
    rw [lca]
    by_cases hab : a = b
    · subst hab
      exact ⟨a, by simp, Nat.le_refl _,
        R.graph.dominates_refl a, R.graph.dominates_refl a, fun w hw _ => hw⟩
    · rw [if_neg hab]
      by_cases hlt : R.rank b < R.rank a
      · rw [if_pos hlt]
        obtain ⟨a', h', hpa, hidom⟩ := parent a b ha (by omega) hab
        rw [hpa]
        obtain ⟨m, hlca, hmle, hgcd⟩ :=
          ih (R.rank a' + R.rank b) (by omega) a' b (by omega) hb rfl
        exact ⟨m, hlca, by omega, hgcd.step hidom (notDeeper a b · (by omega) hab)⟩
      · rw [if_neg hlt]
        obtain ⟨b', h', hpb, hidom⟩ := parent b a hb (by omega) (fun h => hab h.symm)
        rw [hpb]
        obtain ⟨m, hlca, hmle, hgcd⟩ :=
          ih (R.rank a + R.rank b') (by omega) a b' ha (by omega) rfl
        refine ⟨m, hlca, hmle, ?_⟩
        exact (hgcd.symm.step hidom
          (notDeeper b a · (by omega) (fun h => hab h.symm))).symm

/-- The deepest common dominator of a non-empty list. -/
theorem lcaOf_spec (R : RankedGraph verts) {B : Nat} {tbl : Table verts R.rank}
    (hok : Correct R tbl B) :
    ∀ (n : Nat) (qs : List (Vertex verts)), qs.length = n → qs ≠ [] → (∀ q ∈ qs, R.rank q < B) →
      ∃ m, lcaOf tbl qs = some m ∧ (∃ q ∈ qs, R.rank m ≤ R.rank q) ∧
        (∀ q ∈ qs, R.graph.Dominates m q) ∧ ∀ w, (∀ q ∈ qs, R.graph.Dominates w q) → R.graph.Dominates w m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro (_ | ⟨p, _ | ⟨q, qs⟩⟩) hlen hne hq
    · exact absurd rfl hne
    · exact ⟨p, by rw [lcaOf], ⟨p, by simp, Nat.le_refl _⟩, by simp [R.graph.dominates_refl],
        fun w hw => hw p (by simp)⟩
    · rw [lcaOf]
      obtain ⟨m₁, hlca, hm₁le, hgcd⟩ :=
        lca_spec R hok _ p q (hq p (by simp)) (hq q (by simp)) rfl
      rw [hlca]
      obtain ⟨m, heq, ⟨r, hr, hmr⟩, hall, huniv⟩ :=
        ih (qs.length + 1) (by simp at hlen; omega) (m₁ :: qs) (by simp) (by simp)
          (by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact Nat.lt_of_le_of_lt hm₁le (hq p (by simp))
            · exact hq x (by simp [hx']))
      have hmm₁ : R.graph.Dominates m m₁ := hall m₁ (by simp)
      refine ⟨m, heq, ?_, ?_, fun w hw => huniv w ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨p, by simp, Nat.le_trans hmr hm₁le⟩
        · exact ⟨r, by simp [hr'], hmr⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hmm₁.trans hgcd.1
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · exact hmm₁.trans hgcd.2.1
          · exact hall x (by simp [hx''])
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hgcd.2.2 w (hw p (by simp)) (hw q (by simp))
        · exact hw x (by simp [hx'])

/-- The parent of `v`, computed from a table already correct below `rank v`. -/
def parentOf (g : DepGraph verts) (rank : Vertex verts → Nat) (tbl : Table verts rank)
    (v : Vertex verts) : Option {u : Vertex verts // rank u < rank v} :=
  if v = g.root then none
  else
    match lcaOf tbl (g.preds v) with
    | none => none
    | some m => if h : rank m < rank v then some ⟨m, h⟩ else none

/-- `parentOf` returns the immediate dominator, and returns one whenever the
vertex has a parent to find. -/
theorem parentOf_spec (R : RankedGraph verts) {tbl : Table verts R.rank} {v : Vertex verts}
    (hok : Correct R tbl (R.rank v)) :
    (∀ u hu, parentOf R.dep R.rank tbl v = some ⟨u, hu⟩ → R.graph.IsIdom u v) ∧
      (v ≠ R.graph.root → (parentOf R.dep R.rank tbl v).isSome) := by
  rw [parentOf]
  by_cases hroot : v = R.graph.root
  · rw [if_pos hroot]
    exact ⟨by simp, fun h => absurd hroot h⟩
  · rw [if_neg hroot]
    obtain ⟨m, heq, ⟨q₀, hq₀, hmle⟩, hmall, huniv⟩ :=
      lcaOf_spec R hok _ (R.graph.preds v) rfl (preds_ne_nil hroot)
        (fun q hq => R.topo q v (mem_preds.mp hq))
    have hmv : R.graph.Dominates m v :=
      (dominates_iff_preds hroot m).mpr (Or.inr fun q hq => hmall q (mem_preds.mpr hq))
    have hmlt : R.rank m < R.rank v :=
      Nat.lt_of_le_of_lt hmle (R.topo q₀ v (mem_preds.mp hq₀))
    rw [heq]
    dsimp only
    rw [dif_pos hmlt]
    refine ⟨fun u hu hres => ?_, fun _ => by simp⟩
    have hum : u = m := by simpa using hres.symm
    subst hum
    refine ⟨⟨hmv, by intro h; rw [h] at hmlt; omega⟩, fun w hw => huniv w fun q hq => ?_⟩
    rcases (dominates_iff_preds hroot w).mp hw.1 with h | h
    · exact absurd h hw.2
    · exact h q (mem_preds.mp hq)

/-! ## Building the tree incrementally

Vertices are processed in order of rank, each parent stored in the table, so
every parent is computed exactly once. A whole rank can be done against the
table from the ranks below it, since predecessors rank strictly lower. -/

/-- Record `f v` for every `v` in the list. -/
def insertAll {rank : Vertex verts → Nat}
    (f : (v : Vertex verts) → Option {u : Vertex verts // rank u < rank v}) :
    List (Vertex verts) → Table verts rank → Table verts rank
  | [], tbl => tbl
  | v :: vs, tbl => insertAll f vs (tbl.insert v (f v))

theorem get_insertAll {rank : Vertex verts → Nat}
    {f : (v : Vertex verts) → Option {u : Vertex verts // rank u < rank v}} :
    ∀ (vs : List (Vertex verts)) (tbl : Table verts rank) (x : Vertex verts),
      (insertAll f vs tbl).get x = if x ∈ vs then f x else tbl.get x := by
  intro vs
  induction vs with
  | nil => intro tbl x; simp [insertAll]
  | cons v vs ih =>
    intro tbl x
    rw [insertAll, ih]
    by_cases hx : x ∈ vs
    · simp [hx]
    · by_cases hxv : x = v
      · subst hxv; simp [hx]
      · simp [hx, hxv, Table.get_insert_ne _ _ hxv]

/-- The vertices of rank exactly `n`. -/
def atRank (rank : Vertex verts → Nat) (n : Nat) : List (Vertex verts) :=
  verts.attach.filter (fun v => decide (rank v = n))

omit [DecidableEq V] [Hashable V] in
@[simp] theorem mem_atRank {rank : Vertex verts → Nat} {n : Nat} {v : Vertex verts} :
    v ∈ atRank rank n ↔ rank v = n := by
  simp [atRank, List.mem_filter, List.mem_attach]

/-- The dominator tree for every vertex of rank below `n`. -/
def buildUpTo (g : DepGraph verts) (rank : Vertex verts → Nat) : Nat → Table verts rank
  | 0 => ∅
  | n + 1 =>
      let tbl := buildUpTo g rank n
      insertAll (parentOf g rank tbl) (atRank rank n) tbl

/-- **Correctness of the construction**: after building up to `n`, the table
holds the immediate dominator of every vertex of rank below `n`. -/
theorem buildUpTo_correct (R : RankedGraph verts) :
    ∀ n : Nat, Correct R (buildUpTo R.dep R.rank n) n := by
  intro n
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    intro x hx
    rw [buildUpTo, get_insertAll]
    rcases Nat.lt_or_ge (R.rank x) n with h | h
    · rw [if_neg (by simp; omega)]
      exact ih x h
    · rw [if_pos (by simp; omega)]
      exact parentOf_spec R (by rwa [show R.rank x = n by omega])

/-- The dominator tree: the parent of `v`, or `none` at the root. -/
def idom? (g : DepGraph verts) (rank : Vertex verts → Nat) (N : Nat) (v : Vertex verts) :
    Option (Vertex verts) :=
  ((buildUpTo g rank N).get v).map Subtype.val

/-- **Soundness**: what `idom?` returns is the immediate dominator. -/
theorem isIdom_of_idom? (R : RankedGraph verts) {N : Nat} {v u : Vertex verts} (hN : R.rank v < N)
    (h : idom? R.dep R.rank N v = some u) : R.graph.IsIdom u v := by
  rw [idom?] at h
  cases h' : (buildUpTo R.dep R.rank N).get v with
  | none => rw [h'] at h; simp at h
  | some val =>
    obtain ⟨u', hu'⟩ := val
    rw [h'] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact (buildUpTo_correct R N v hN).1 u' hu' h'

/-- **Totality**: on a connected graph every non-root vertex gets a parent. -/
theorem idom?_isSome (R : RankedGraph verts) {N : Nat} {v : Vertex verts} (hN : R.rank v < N)
    (hv : v ≠ R.graph.root) : (idom? R.dep R.rank N v).isSome := by
  rw [idom?, Option.isSome_map]
  exact (buildUpTo_correct R N v hN).2 hv

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
theorem domWalk_iff (R : RankedGraph verts) {N : Nat} {tbl : Table verts R.rank}
    (hok : Correct R tbl N) :
    ∀ (n : Nat) (v : Vertex verts), R.rank v = n → R.rank v < N → ∀ u : Vertex verts,
      domWalk tbl u v = true ↔ R.graph.Dominates u v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv hvN u
    rw [domWalk]
    by_cases huv : u = v
    · subst huv
      simp [R.graph.dominates_refl u]
    · rw [if_neg huv]
      cases h : tbl.get v with
      | none =>
        have hroot : v = R.graph.root := by
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
        have hidom : R.graph.IsIdom m v := (hok v hvN).1 m hm h
        rw [ih (R.rank m) (by omega) m rfl (by omega) u]
        exact ⟨fun hum => hum.trans hidom.1.1, fun huv' => hidom.2 u ⟨huv', huv⟩⟩

end DepGraph

end DominatorTree
