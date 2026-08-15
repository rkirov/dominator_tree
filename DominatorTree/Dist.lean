import DominatorTree.Basic

namespace DominatorTree

namespace DepGraph

variable {V : Type} {verts : List V} {g : DepGraph verts}

/-- `d` is the distance from the root to `v`: some path from the root reaches
`v` in `d` edges, and none reaches it in fewer. -/
def IsDist (g : DepGraph verts) (v : Vertex verts) (d : Nat) : Prop :=
  (∃ p : Path g g.root v, p.length = d) ∧ ∀ p : Path g g.root v, d ≤ p.length

/-- A vertex has at most one distance. -/
theorem IsDist.unique {v : Vertex verts} {d d' : Nat}
    (h : g.IsDist v d) (h' : g.IsDist v d') : d = d' := by
  obtain ⟨⟨p, hp⟩, hmin⟩ := h
  obtain ⟨⟨p', hp'⟩, hmin'⟩ := h'
  exact Nat.le_antisymm (hp' ▸ hmin p') (hp ▸ hmin' p)

/-- A dominator is never further from the root than the vertex it dominates.

Every path to `y` runs through `x`, so truncating a shortest path to `y` at `x`
gives a path to `x` that is no longer. -/
theorem dominates_dist_le {x y : Vertex verts} {dx dy : Nat}
    (hd : g.Dominates x y) (hx : g.IsDist x dx) (hy : g.IsDist y dy) : dx ≤ dy := by
  obtain ⟨⟨p, hp⟩, -⟩ := hy
  obtain ⟨q, hq⟩ := Path.exists_prefix p x (hd p)
  exact Nat.le_trans (hx.2 q) (hp ▸ hq)

/-- A *strict* dominator is strictly closer to the root: it sits before the end
of a shortest path, so its prefix is strictly shorter. -/
theorem dominates_dist_lt {x y : Vertex verts} {dx dy : Nat}
    (hd : g.Dominates x y) (hne : x ≠ y) (hx : g.IsDist x dx) (hy : g.IsDist y dy) : dx < dy := by
  obtain ⟨⟨p, hp⟩, -⟩ := hy
  obtain ⟨q, hq⟩ := Path.exists_prefix_lt p x (hd p) hne
  exact Nat.lt_of_le_of_lt (hx.2 q) (hp ▸ hq)

/-- Mutual dominators are equal, so dominance is a partial order on the
vertices that have a distance (i.e. the reachable ones). -/
theorem Dominates.antisymm {u w : Vertex verts} {du dw : Nat}
    (huw : g.Dominates u w) (hwu : g.Dominates w u)
    (hu : g.IsDist u du) (hw : g.IsDist w dw) : u = w := by
  apply Classical.byContradiction
  intro hne
  have h1 : du < dw := dominates_dist_lt huw hne hu hw
  have h2 : dw < du := dominates_dist_lt hwu (Ne.symm hne) hw hu
  omega

/-- A reachable vertex has a distance: among the lengths of paths reaching it
there is a least one. -/
theorem exists_isDist {v : Vertex verts} (p : Path g g.root v) : ∃ d, g.IsDist v d := by
  suffices h : ∀ n : Nat, ∀ q : Path g g.root v, q.length = n → ∃ d, g.IsDist v d from
    h p.length p rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q hq
    -- either no path is shorter than `q`, or recurse on one that is
    rcases Classical.em (∀ r : Path g g.root v, n ≤ r.length) with hmin | hnot
    · exact ⟨n, ⟨q, hq⟩, hmin⟩
    · obtain ⟨r, hr⟩ := Classical.not_forall.mp hnot
      exact ih r.length (Nat.lt_of_not_le hr) r rfl

/-- A dominator of a reachable vertex is itself reachable, hence has a distance. -/
theorem exists_isDist_of_dominates {u v : Vertex verts} (hv : Path g g.root v)
    (h : g.Dominates u v) : ∃ d, g.IsDist u d := by
  obtain ⟨q, -⟩ := Path.exists_prefix hv u (h hv)
  exact exists_isDist q

/-- A reachable vertex has at most one immediate dominator — so the dominator
"parent" is well defined and the relation is a tree, not a DAG. -/
theorem IsIdom.unique {u u' v : Vertex verts} (hv : Path g g.root v)
    (h : g.IsIdom u v) (h' : g.IsIdom u' v) : u = u' := by
  obtain ⟨du, hdu⟩ := exists_isDist_of_dominates hv h.1.1
  obtain ⟨du', hdu'⟩ := exists_isDist_of_dominates hv h'.1.1
  exact Dominates.antisymm (h'.2 u h.1) (h.2 u' h'.1) hdu hdu'

/-- The dominator parent is strictly closer to the root, so following parents
strictly decreases distance and cannot cycle. -/
theorem IsIdom.dist_lt {u v : Vertex verts} {du dv : Nat}
    (h : g.IsIdom u v) (hu : g.IsDist u du) (hv : g.IsDist v dv) : du < dv :=
  dominates_dist_lt h.1.1 h.1.2 hu hv

end DepGraph

namespace ConnectedGraph

variable {V : Type} {verts : List V} {g : ConnectedGraph verts}

/-- Every vertex of a connected graph has a distance from the root. -/
theorem exists_isDist (g : ConnectedGraph verts) (v : Vertex verts) : ∃ d, g.IsDist v d :=
  (g.reach v).elim DepGraph.exists_isDist

/-- Distance from the root, as a total function.

Not the same as `DepGraph.dist?`, which computes distance by BFS; the two are
not yet proved to agree. -/
noncomputable def dist (g : ConnectedGraph verts) (v : Vertex verts) : Nat :=
  Classical.choose (g.exists_isDist v)

theorem isDist_dist (g : ConnectedGraph verts) (v : Vertex verts) : g.IsDist v (g.dist v) :=
  Classical.choose_spec (g.exists_isDist v)

/-- On a connected graph every vertex has at most one immediate dominator, with
no reachability side condition — so "the dominator parent" is well defined. -/
theorem isIdom_unique {u u' v : Vertex verts} (h : g.IsIdom u v) (h' : g.IsIdom u' v) : u = u' :=
  (g.reach v).elim fun p => DepGraph.IsIdom.unique p h h'

/-- Dominance is antisymmetric, hence a partial order on the whole graph. -/
theorem dominates_antisymm {u w : Vertex verts}
    (huw : g.Dominates u w) (hwu : g.Dominates w u) : u = w :=
  DepGraph.Dominates.antisymm huw hwu (g.isDist_dist u) (g.isDist_dist w)

/-- A dominator is no further from the root. -/
theorem dist_le_of_dominates {u v : Vertex verts} (h : g.Dominates u v) :
    g.dist u ≤ g.dist v :=
  DepGraph.dominates_dist_le h (g.isDist_dist u) (g.isDist_dist v)

/-- The dominator parent is strictly closer to the root, so the parent chain
strictly decreases and cannot cycle. -/
theorem dist_lt_of_isIdom {u v : Vertex verts} (h : g.IsIdom u v) : g.dist u < g.dist v :=
  DepGraph.IsIdom.dist_lt h (g.isDist_dist u) (g.isDist_dist v)

end ConnectedGraph

end DominatorTree
