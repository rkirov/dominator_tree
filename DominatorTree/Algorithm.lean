import DominatorTree.Reducible

/-!
# Computing dominators on a topologically ordered graph

For a graph whose edges all increase some rank — a DAG, or the back-edge-free
part of a reducible graph — dominators need no fixpoint iteration. Every
predecessor of `v` is ranked below `v`, so a single recursive pass computes

    dom v = {v} ∪ ⋂ { dom p | p → v }

with `dom root = {root}`.
-/

namespace DominatorTree

namespace DepGraph

variable {V : Type} {verts : List V} [DecidableEq V]

/-- The predecessors of `v`. -/
def preds (g : DepGraph verts) (v : Vertex verts) : List (Vertex verts) :=
  verts.attach.filter (fun u => decide (v ∈ g.out u))

@[simp] theorem mem_preds {g : DepGraph verts} {u v : Vertex verts} :
    u ∈ g.preds v ↔ g.Edge u v := by
  simp [preds, List.mem_filter, List.mem_attach, Edge]

/-! ### The dataflow equation

The equation every dominator algorithm is proved against, here derived directly
from paths. -/

omit [DecidableEq V] in
/-- Only the root dominates the root. -/
theorem dominates_root_iff {g : DepGraph verts} {w : Vertex verts} :
    g.Dominates w g.root ↔ w = g.root := by
  constructor
  · intro h
    have := h (.nil _)
    simpa [Path.vertices] using this
  · rintro rfl
    exact g.dominates_refl _

omit [DecidableEq V] in
/-- `w` dominates `v` exactly when it is `v`, or dominates every predecessor of
`v`. Extending a path to a predecessor by one edge adds only `v` itself, and
conversely every path to a non-root `v` ends with an edge from a predecessor. -/
theorem dominates_iff_preds {g : DepGraph verts} {v : Vertex verts} (hv : v ≠ g.root)
    (w : Vertex verts) :
    g.Dominates w v ↔ (w = v ∨ ∀ p, g.Edge p v → g.Dominates w p) := by
  constructor
  · intro hdom
    by_cases hwv : w = v
    · exact Or.inl hwv
    refine Or.inr fun p hp P => ?_
    -- walk to `p`, then take the edge to `v`
    have hmem := hdom (P.append (.cons hp (.nil v)))
    rcases Path.mem_vertices_append P _ hmem with h | h
    · exact h
    · simp [Path.vertices] at h
      rcases h with rfl | rfl
      · exact P.end_mem_vertices
      · exact absurd rfl hwv
  · rintro (rfl | hall) P
    · exact P.end_mem_vertices
    · -- a path to a non-root vertex has a final edge
      have hpos : 0 < P.length := by
        rcases Nat.eq_zero_or_pos P.length with h0 | h
        · exact absurd (Path.eq_of_length_zero P h0).symm hv
        · exact h
      obtain ⟨x, q, he, hqv⟩ := P.exists_last_edge_path hpos
      exact hqv w (hall x he q)

/-! ### The single-pass algorithm -/

/-- A rank that strictly increases along every edge: a topological numbering.
Existence of one is exactly acyclicity, for a finite graph. -/
def TopoRank (g : DepGraph verts) (rank : Vertex verts → Nat) : Prop :=
  ∀ v u, u ∈ g.out v → rank v < rank u

omit [DecidableEq V] in
/-- Checking a topological rank only needs the vertices actually listed, so this
form is decidable. -/
theorem topoRank_of_forall_mem {g : DepGraph verts} {rank : Vertex verts → Nat}
    (h : ∀ v ∈ verts.attach, ∀ u ∈ g.out v, rank v < rank u) : g.TopoRank rank :=
  fun v u hu => h v (List.mem_attach _ _) u hu

/-- Intersect a family of lists, starting from a universe list. An empty family
gives the whole universe, which is the right answer for a vertex with no
predecessors: everything dominates it vacuously. -/
def interAll (univ : List (Vertex verts)) : List (List (Vertex verts)) → List (Vertex verts)
  | [] => univ
  | l :: ls => interAll (univ.filter (fun x => decide (x ∈ l))) ls

theorem mem_interAll {univ : List (Vertex verts)} :
    ∀ {ls : List (List (Vertex verts))} {x : Vertex verts},
      x ∈ interAll univ ls ↔ x ∈ univ ∧ ∀ l ∈ ls, x ∈ l := by
  intro ls
  induction ls generalizing univ with
  | nil => intro x; simp [interAll]
  | cons l ls ih =>
    intro x
    simp only [interAll, ih, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨⟨hu, hl⟩, hrest⟩
      refine ⟨hu, fun m hm => ?_⟩
      rcases hm with rfl | hm
      · exact hl
      · exact hrest m hm
    · rintro ⟨hu, hall⟩
      exact ⟨⟨hu, hall l (Or.inl rfl)⟩, fun m hm => hall m (Or.inr hm)⟩

/-- The dominators of `v`, computed in one pass.

Terminates because every predecessor of `v` has a strictly smaller rank — this
is where acyclicity in the direction of the edges is used, and why no fixpoint
iteration is needed. -/
def domSet (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : List (Vertex verts) :=
  if v = g.root then [v]
  else
    v :: interAll verts.attach ((g.preds v).attach.map (fun p => domSet g rank htopo p.val))
termination_by rank v
decreasing_by
  exact htopo _ _ (mem_preds.mp p.property)

/-- **Correctness**: the one-pass computation returns exactly the dominators.

By strong induction on the rank: the predecessors of `v` are already settled
when `v` is reached, so the dataflow equation turns their answers into `v`'s. -/
theorem mem_domSet {g : DepGraph verts} {rank : Vertex verts → Nat} {htopo : g.TopoRank rank}
    (v w : Vertex verts) : w ∈ domSet g rank htopo v ↔ g.Dominates w v := by
  suffices H : ∀ n (v : Vertex verts), rank v = n →
      ∀ w, w ∈ domSet g rank htopo v ↔ g.Dominates w v from H _ v rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv w
    rw [domSet]
    by_cases hroot : v = g.root
    · subst hroot
      rw [if_pos rfl]
      simp only [List.mem_singleton]
      exact dominates_root_iff.symm
    · rw [if_neg hroot, dominates_iff_preds hroot w]
      simp only [List.mem_cons, mem_interAll, List.mem_map, List.mem_attach, true_and]
      constructor
      · rintro (rfl | hall)
        · exact Or.inl rfl
        · refine Or.inr fun p hp => ?_
          have hlt : rank p < n := by rw [← hv]; exact htopo p v hp
          exact (ih (rank p) hlt p rfl w).mp (hall _ ⟨⟨p, mem_preds.mpr hp⟩, rfl⟩)
      · rintro (rfl | hall)
        · exact Or.inl rfl
        · refine Or.inr ?_
          rintro l ⟨⟨p, hpp⟩, rfl⟩
          have hp : g.Edge p v := mem_preds.mp hpp
          have hlt : rank p < n := by rw [← hv]; exact htopo p v hp
          exact (ih (rank p) hlt p rfl w).mpr (hall p hp)

/-! ### The immediate dominator tree

The tree is the artifact worth producing: the dominators of `v` are just the
vertices on the path from `v` to the root, so they are recoverable from it. -/

variable {g : DepGraph verts} {rank : Vertex verts → Nat} {htopo : g.TopoRank rank}

/-- The strict dominators of `v`. -/
def strictDoms (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : List (Vertex verts) :=
  (domSet g rank htopo v).filter (fun u => decide (u ≠ v))

theorem mem_strictDoms {v u : Vertex verts} :
    u ∈ strictDoms g rank htopo v ↔ g.StrictlyDominates u v := by
  simp [strictDoms, List.mem_filter, mem_domSet, StrictlyDominates]

/-- The immediate dominator of `v`: the strict dominator that every strict
dominator dominates. `none` at the root. -/
def idom? (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : Option (Vertex verts) :=
  let ds := strictDoms g rank htopo v
  ds.find? (fun u => ds.all (fun w => decide (w ∈ domSet g rank htopo u)))

/-- **Soundness**: whatever `idom?` returns really is the immediate dominator. -/
theorem isIdom_of_idom? {v u : Vertex verts} (h : idom? g rank htopo v = some u) :
    g.IsIdom u v := by
  have hmem : u ∈ strictDoms g rank htopo v := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  refine ⟨mem_strictDoms.mp hmem, fun w hw => ?_⟩
  have hwmem : w ∈ strictDoms g rank htopo v := mem_strictDoms.mpr hw
  have := List.all_eq_true.mp hpred w hwmem
  exact (mem_domSet u w).mp (by simpa using this)

/-- **Completeness**: on a connected graph every non-root vertex gets one. -/
theorem idom?_isSome {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v : Vertex verts} (hv : v ≠ g.root) :
    (idom? g.toDepGraph rank htopo v).isSome := by
  obtain ⟨u, hu⟩ := g.exists_isIdom v hv
  rcases hfind : idom? g.toDepGraph rank htopo v with _ | w
  · exfalso
    have hnone := List.find?_eq_none.mp hfind u (mem_strictDoms.mpr hu.1)
    refine hnone (List.all_eq_true.mpr fun x hx => ?_)
    simpa using (mem_domSet u x).mpr (hu.2 x (mem_strictDoms.mp hx))
  · rfl

end DepGraph

end DominatorTree
