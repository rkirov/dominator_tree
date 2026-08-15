import DominatorTree.Reducible

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

variable [DecidableEq V]

/-- The predecessors of `v`. -/
def preds (g : DepGraph verts) (v : Vertex verts) : List (Vertex verts) :=
  verts.attach.filter (fun u => decide (v ∈ g.out u))

@[simp] theorem mem_preds {g : DepGraph verts} {u v : Vertex verts} :
    u ∈ g.preds v ↔ g.Edge u v := by
  simp [preds, List.mem_filter, List.mem_attach, Edge]

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

/-- Climb `a` and `b` to their lowest common ancestor, using a parent lookup
whose type guarantees the rank drops at every step — which is exactly what makes
this recursion well founded. -/
def lca (rank : Vertex verts → Nat) (B : Nat)
    (par : (x : Vertex verts) → rank x < B → Option {u : Vertex verts // rank u < rank x})
    (a b : Vertex verts) (ha : rank a < B) (hb : rank b < B) :
    Option {u : Vertex verts // rank u < B} :=
  if a = b then some ⟨a, ha⟩
  else if rank b < rank a then
    match par a ha with
    | none => none
    | some ⟨a', h⟩ => lca rank B par a' b (Nat.lt_trans h ha) hb
  else
    match par b hb with
    | none => none
    | some ⟨b', h⟩ => lca rank B par a b' ha (Nat.lt_trans h hb)
termination_by rank a + rank b
decreasing_by
  · omega
  · omega

/-- Fold `lca` over a list of vertices. -/
def lcaAll (rank : Vertex verts → Nat) (B : Nat)
    (par : (x : Vertex verts) → rank x < B → Option {u : Vertex verts // rank u < rank x})
    (a : Vertex verts) (ha : rank a < B) :
    (qs : List (Vertex verts)) → (∀ q ∈ qs, rank q < B) →
      Option {u : Vertex verts // rank u < B}
  | [], _ => some ⟨a, ha⟩
  | q :: qs, hq =>
      match lca rank B par a q ha (hq q (by simp)) with
      | none => none
      | some ⟨m, hm⟩ => lcaAll rank B par m hm qs (fun x hx => hq x (by simp [hx]))

/-- The immediate dominator of `v`, as the lowest common ancestor of its
predecessors — carrying the proof that its rank is smaller, so that callers may
climb again. -/
def idomLt (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : Option {u : Vertex verts // rank u < rank v} :=
  if v = g.root then none
  else
    match hp : g.preds v with
    | [] => none
    | p :: ps =>
        lcaAll rank (rank v) (fun x _ => idomLt g rank htopo x) p
          (htopo p v (mem_preds.mp (by rw [hp]; exact List.mem_cons_self)))
          ps (fun q hq => htopo q v (mem_preds.mp (by rw [hp]; exact List.mem_cons_of_mem _ hq)))
termination_by rank v
decreasing_by assumption

/-- The climb returns the greatest common dominator of `a` and `b`.

Each step replaces the deeper of the two by its parent, which is sound because
any common dominator is a *strict* dominator of the deeper one — it is at most
as deep as the other — and so dominates that parent. -/
theorem lca_spec {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {B : Nat}
    {par : (x : Vertex verts) → rank x < B → Option {u : Vertex verts // rank u < rank x}}
    (hpar : ∀ x hx u hu, par x hx = some ⟨u, hu⟩ → g.IsIdom u x)
    (hsome : ∀ x hx, x ≠ g.root → (par x hx).isSome) :
    ∀ (n : Nat) (a b : Vertex verts) (ha : rank a < B) (hb : rank b < B), rank a + rank b = n →
      ∃ m hm, lca rank B par a b ha hb = some ⟨m, hm⟩ ∧
        g.Dominates m a ∧ g.Dominates m b ∧
        ∀ w, g.Dominates w a → g.Dominates w b → g.Dominates w m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b ha hb hn
    rw [lca]
    by_cases hab : a = b
    · subst hab
      exact ⟨a, ha, by simp, g.dominates_refl a, g.dominates_refl a, fun w hw _ => hw⟩
    · rw [if_neg hab]
      by_cases hlt : rank b < rank a
      · rw [if_pos hlt]
        have haroot : a ≠ g.root := by
          rintro rfl
          by_cases hbr : b = g.root
          · exact hab hbr.symm
          · have := rank_lt_of_dominates htopo (g.root_dominates b) (Ne.symm hbr)
            omega
        cases hpa : par a ha with
        | none => exact absurd (hsome a ha haroot) (by rw [hpa]; simp)
        | some val =>
          obtain ⟨a', h'⟩ := val
          have hidom : g.IsIdom a' a := hpar a ha a' h' hpa
          obtain ⟨m, hm, hlca, hma', hmb, huniv⟩ :=
            ih (rank a' + rank b) (by omega) a' b (Nat.lt_trans h' ha) hb rfl
          refine ⟨m, hm, hlca, hma'.trans hidom.1.1, hmb, fun w hwa hwb => ?_⟩
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
        cases hpb : par b hb with
        | none => exact absurd (hsome b hb hbroot) (by rw [hpb]; simp)
        | some val =>
          obtain ⟨b', h'⟩ := val
          have hidom : g.IsIdom b' b := hpar b hb b' h' hpb
          obtain ⟨m, hm, hlca, hma, hmb', huniv⟩ :=
            ih (rank a + rank b') (by omega) a b' ha (Nat.lt_trans h' hb) rfl
          refine ⟨m, hm, hlca, hma, hmb'.trans hidom.1.1, fun w hwa hwb => ?_⟩
          have hwne : w ≠ b := by
            rintro rfl
            exact absurd (rank_lt_of_dominates htopo hwa (fun hh => hab hh.symm)) (by omega)
          exact huniv w hwa (hidom.2 w ⟨hwb, hwne⟩)

/-- Folding the climb gives the greatest common dominator of the whole list. -/
theorem lcaAll_spec {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {B : Nat}
    {par : (x : Vertex verts) → rank x < B → Option {u : Vertex verts // rank u < rank x}}
    (hpar : ∀ x hx u hu, par x hx = some ⟨u, hu⟩ → g.IsIdom u x)
    (hsome : ∀ x hx, x ≠ g.root → (par x hx).isSome) :
    ∀ (qs : List (Vertex verts)) (a : Vertex verts) (ha : rank a < B)
      (hq : ∀ q ∈ qs, rank q < B),
      ∃ m hm, lcaAll rank B par a ha qs hq = some ⟨m, hm⟩ ∧
        g.Dominates m a ∧ (∀ q ∈ qs, g.Dominates m q) ∧
        ∀ w, g.Dominates w a → (∀ q ∈ qs, g.Dominates w q) → g.Dominates w m := by
  intro qs
  induction qs with
  | nil =>
    intro a ha hq
    exact ⟨a, ha, by simp [lcaAll], g.dominates_refl a, by simp, fun w hw _ => hw⟩
  | cons q qs ih =>
    intro a ha hq
    rw [lcaAll]
    obtain ⟨m1, hm1, hlca, hm1a, hm1q, huniv1⟩ :=
      lca_spec htopo hpar hsome _ a q ha (hq q (by simp)) rfl
    rw [hlca]
    obtain ⟨m, hm, hrec, hma, hmqs, huniv⟩ := ih m1 hm1 (fun x hx => hq x (by simp [hx]))
    refine ⟨m, hm, hrec, hma.trans hm1a, ?_, ?_⟩
    · intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq''
      · exact hma.trans hm1q
      · exact hmqs q' hq''
    · intro w hwa hwall
      exact huniv w (huniv1 w hwa (hwall q (by simp))) (fun q' hq' => hwall q' (by simp [hq']))

/-- **Correctness**: the lowest common ancestor of the predecessors really is
the immediate dominator, and on a connected graph it always exists.

The dataflow equation turns "dominates every predecessor" into "dominates `v`",
so the greatest common dominator of the predecessors is the deepest strict
dominator of `v`. -/
theorem idomLt_spec {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) :
    ∀ (n : Nat) (v : Vertex verts), rank v = n →
      (∀ u hu, idomLt g.toDepGraph rank htopo v = some ⟨u, hu⟩ → g.IsIdom u v) ∧
      (v ≠ g.root → (idomLt g.toDepGraph rank htopo v).isSome) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv
    rw [idomLt]
    by_cases hroot : v = g.root
    · rw [if_pos hroot]
      exact ⟨by simp, fun h => absurd hroot h⟩
    · rw [if_neg hroot]
      split
      · rename_i hp
        exact absurd hp (preds_ne_nil hroot)
      · rename_i p ps hp
        have hpar : ∀ x (hx : rank x < rank v) u hu,
            idomLt g.toDepGraph rank htopo x = some ⟨u, hu⟩ → g.IsIdom u x :=
          fun x hx u hu h => (ih (rank x) (hv ▸ hx) x rfl).1 u hu h
        have hsome : ∀ x (hx : rank x < rank v), x ≠ g.root →
            (idomLt g.toDepGraph rank htopo x).isSome :=
          fun x hx hne => (ih (rank x) (hv ▸ hx) x rfl).2 hne
        obtain ⟨m, hm, heq, hmp, hmqs, huniv⟩ :=
          lcaAll_spec (par := fun x (_ : rank x < rank v) => idomLt g.toDepGraph rank htopo x)
            htopo hpar hsome ps p _ _
        have hmall : ∀ q, g.Edge q v → g.Dominates m q := by
          intro q hq
          rcases List.mem_cons.mp (show q ∈ p :: ps from hp ▸ mem_preds.mpr hq) with rfl | hq'
          · exact hmp
          · exact hmqs q hq'
        have hmv : g.Dominates m v := (dominates_iff_preds hroot m).mpr (Or.inr hmall)
        have hmne : m ≠ v := by intro h; rw [h] at hm; omega
        constructor
        · intro u hu hres
          rw [heq] at hres
          have hum : u = m := by simpa using hres.symm
          subst hum
          refine ⟨⟨hmv, hmne⟩, fun w hw => ?_⟩
          have hwall : ∀ q, g.Edge q v → g.Dominates w q := by
            intro q hq
            rcases (dominates_iff_preds hroot w).mp hw.1 with h | h
            · exact absurd h hw.2
            · exact h q hq
          refine huniv w (hwall p ?_) (fun q' hq' => hwall q' ?_)
          · exact mem_preds.mp (by rw [hp]; exact List.mem_cons_self)
          · exact mem_preds.mp (by rw [hp]; exact List.mem_cons_of_mem _ hq')
        · intro _
          rw [heq]
          simp

/-- The dominator tree: the parent of `v`, or `none` at the root. -/
def idom? (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : Option (Vertex verts) :=
  (idomLt g rank htopo v).map Subtype.val

/-- **Soundness**: what `idom?` returns is the immediate dominator. -/
theorem isIdom_of_idom? {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v u : Vertex verts}
    (h : idom? g.toDepGraph rank htopo v = some u) : g.IsIdom u v := by
  rw [idom?] at h
  cases h' : idomLt g.toDepGraph rank htopo v with
  | none => rw [h'] at h; simp at h
  | some val =>
    obtain ⟨u', hu'⟩ := val
    rw [h'] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact (idomLt_spec htopo (rank v) v rfl).1 u' hu' h'

/-- **Totality**: on a connected graph every non-root vertex gets a parent. -/
theorem idom?_isSome {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v : Vertex verts} (hv : v ≠ g.root) :
    (idom? g.toDepGraph rank htopo v).isSome := by
  rw [idom?, Option.isSome_map]
  exact (idomLt_spec htopo (rank v) v rfl).2 hv

/-- Is `u` on the path from `v` to the root of the dominator tree?

Well founded because each parent has strictly smaller rank — the theorems above
are what make this definition legal. -/
def domWalk (g : ConnectedGraph verts) (rank : Vertex verts → Nat)
    (htopo : g.toDepGraph.TopoRank rank) (u v : Vertex verts) : Bool :=
  if u = v then true
  else
    match h : idom? g.toDepGraph rank htopo v with
    | none => false
    | some m => domWalk g rank htopo u m
termination_by rank v
decreasing_by
  have hidom := isIdom_of_idom? h
  exact rank_lt_of_dominates htopo hidom.1.1 hidom.1.2

/-- **Correctness**: climbing the tree decides dominance.

One way it is transitivity — the parent dominates `v`, so anything dominating
the parent dominates `v`. The other way it is the defining property of an
immediate dominator: every strict dominator of `v` also dominates `v`'s
parent. -/
theorem domWalk_iff {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} (u v : Vertex verts) :
    domWalk g rank htopo u v = true ↔ g.Dominates u v := by
  suffices H : ∀ n (v : Vertex verts), rank v = n →
      ∀ u, domWalk g rank htopo u v = true ↔ g.Dominates u v from H _ v rfl u
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv u
    rw [domWalk]
    by_cases huv : u = v
    · subst huv
      simp [g.dominates_refl u]
    · rw [if_neg huv]
      cases h : idom? g.toDepGraph rank htopo v with
      | none =>
        have hroot : v = g.root := by
          apply Classical.byContradiction
          intro hne
          have hsome := idom?_isSome (htopo := htopo) hne
          rw [h] at hsome
          simp at hsome
        subst hroot
        simp only [dominates_root_iff]
        exact ⟨fun hf => absurd hf (by simp), fun hu => absurd hu huv⟩
      | some m =>
        have hidom := isIdom_of_idom? (htopo := htopo) h
        have hlt : rank m < n := by
          rw [← hv]; exact rank_lt_of_dominates htopo hidom.1.1 hidom.1.2
        rw [ih (rank m) hlt m rfl u]
        exact ⟨fun hum => hum.trans hidom.1.1, fun huv' => hidom.2 u ⟨huv', huv⟩⟩

end DepGraph

end DominatorTree
