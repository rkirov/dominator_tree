import DominatorTree.Idom

namespace DominatorTree

variable {V : Type} {verts : List V}

/-- No directed cycles: the only path from a vertex back to itself is the empty
one. This is what "acyclic" actually means. -/
def DepGraph.Acyclic (g : DepGraph verts) : Prop :=
  ∀ (v : Vertex verts) (p : DepGraph.Path g v v), p.length = 0

/-- Some rank strictly decreases along every edge. This is a *witness* for
acyclicity, not its definition; `Ranked.acyclic` derives the real property. -/
def DepGraph.Ranked (g : DepGraph verts) : Prop :=
  ∃ rank : Vertex verts → Nat, ∀ v u, u ∈ g.out v → rank u < rank v

namespace DepGraph

/-- Walking a path drops the rank by at least its length. -/
theorem rank_add_length_le {g : DepGraph verts} {rank : Vertex verts → Nat}
    (h : ∀ v u, u ∈ g.out v → rank u < rank v) :
    ∀ {u w : Vertex verts} (p : Path g u w), rank w + p.length ≤ rank u := by
  intro u w p
  induction p with
  | nil v => simp [Path.length]
  | @cons a b c hedge p' ih =>
    have hlt : rank b < rank a := h a b hedge
    simp only [Path.length]
    omega

/-- A ranked graph has no cycles: going around one would have to lower the rank
of a vertex below itself. -/
theorem Ranked.acyclic {g : DepGraph verts} (hr : g.Ranked) : g.Acyclic := by
  obtain ⟨rank, hrank⟩ := hr
  intro v p
  have := rank_add_length_le hrank p
  omega

end DepGraph

/-- A tree: a graph whose root has no out-edge, whose every other vertex has
exactly one — its parent — and which is ranked, hence acyclic (`Tree.acyclic`).

The root must be exempt from the out-degree-one rule: in a finite graph where
every vertex had an out-edge, following edges would have to repeat a vertex, so
"out-degree one everywhere" and acyclicity are together impossible. -/
structure Tree {V : Type} (verts : List V) extends DepGraph verts where
  /-- The root has no parent. -/
  out_root : out root = []
  /-- Every other vertex has exactly one parent. -/
  out_single : ∀ v, v ≠ root → ∃ u, out v = [u]
  /-- A rank decreases along every edge, which forbids cycles. -/
  ranked : toDepGraph.Ranked

namespace Tree

/-- A tree has no cycles. -/
theorem acyclic (t : Tree verts) : t.toDepGraph.Acyclic := t.ranked.acyclic

/-- The parent of a non-root vertex. -/
noncomputable def parent (t : Tree verts) (v : Vertex verts) (h : v ≠ t.root) : Vertex verts :=
  Classical.choose (t.out_single v h)

theorem out_eq_parent (t : Tree verts) (v : Vertex verts) (h : v ≠ t.root) :
    t.out v = [t.parent v h] :=
  Classical.choose_spec (t.out_single v h)

/-- Every vertex has a path to the root: following parents terminates there.

This is what makes the structure a tree rather than a forest — the rank
decreases at every step, and the root is the only vertex without a parent. -/
theorem exists_path_to_root (t : Tree verts) :
    ∀ v : Vertex verts, Nonempty (DepGraph.Path t.toDepGraph v t.root) := by
  obtain ⟨rank, hrank⟩ := t.ranked
  suffices h : ∀ n : Nat, ∀ v : Vertex verts, rank v = n →
      Nonempty (DepGraph.Path t.toDepGraph v t.root) from fun v => h _ v rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv
    rcases Classical.em (v = t.root) with rfl | hne
    · exact ⟨.nil _⟩
    · obtain ⟨u, hu⟩ := t.out_single v hne
      have hmem : u ∈ t.out v := by rw [hu]; simp
      have hlt : rank u < n := hv ▸ hrank v u hmem
      obtain ⟨p⟩ := ih (rank u) hlt u rfl
      exact ⟨.cons hmem p⟩

end Tree

namespace ConnectedGraph

open Classical

variable {g : ConnectedGraph verts}

/-- The out-edges of the dominator tree: the immediate dominator of `v`, and
nothing at all for the root.

Total because immediate dominators always exist (`exists_isIdom`) and are
unique (`isIdom_unique`). -/
noncomputable def idomOut (g : ConnectedGraph verts) (v : Vertex verts) : List (Vertex verts) :=
  if hv : v = g.root then [] else [Classical.choose (g.exists_isIdom v hv)]

@[simp] theorem idomOut_root : idomOut g g.root = [] := dif_pos rfl

theorem idomOut_eq {v : Vertex verts} (hv : v ≠ g.root) :
    idomOut g v = [Classical.choose (g.exists_isIdom v hv)] := dif_neg hv

/-- Whatever the tree points at is an immediate dominator. -/
theorem isIdom_of_mem_idomOut {u v : Vertex verts} (hu : u ∈ idomOut g v) : g.IsIdom u v := by
  by_cases hv : v = g.root
  · rw [idomOut, dif_pos hv] at hu; simp at hu
  · rw [idomOut_eq hv] at hu
    have hueq : u = Classical.choose (g.exists_isIdom v hv) := by simpa using hu
    subst hueq
    exact Classical.choose_spec (g.exists_isIdom v hv)

/-- Conversely, an immediate dominator is what the tree points at. -/
theorem mem_idomOut_of_isIdom {u v : Vertex verts} (hu : g.IsIdom u v) : u ∈ idomOut g v := by
  have hv : v ≠ g.root := by
    rintro rfl
    exact hu.1.2 (g.dominates_antisymm hu.1.1 (g.root_dominates u))
  rw [idomOut_eq hv, g.isIdom_unique hu (Classical.choose_spec (g.exists_isIdom v hv))]
  simp

/-- The dominator tree: each non-root vertex points to its immediate dominator.

It is well defined because immediate dominators exist and are unique, and it is
a tree because they are strictly closer to the root (`dist_lt_of_isIdom`),
which supplies the decreasing rank. -/
noncomputable def domTree (g : ConnectedGraph verts) : Tree verts where
  out := idomOut g
  root := g.root
  out_root := idomOut_root
  out_single := fun _ hv => ⟨Classical.choose (g.exists_isIdom _ hv), idomOut_eq hv⟩
  ranked := ⟨g.dist, fun _ _ hu => g.dist_lt_of_isIdom (isIdom_of_mem_idomOut hu)⟩

@[simp] theorem domTree_root : (domTree g).root = g.root := rfl

@[simp] theorem domTree_out (v : Vertex verts) : (domTree g).out v = idomOut g v := rfl

/-- The dominator tree's edges are exactly the immediate-dominator relation. -/
theorem mem_domTree_out_iff {u v : Vertex verts} :
    u ∈ (domTree g).out v ↔ g.IsIdom u v :=
  ⟨isIdom_of_mem_idomOut, mem_idomOut_of_isIdom⟩

/-- The dominator tree has no cycles: no vertex is its own strict ancestor. -/
theorem domTree_acyclic (g : ConnectedGraph verts) : (domTree g).toDepGraph.Acyclic :=
  (domTree g).acyclic

/-- Following immediate dominators from any vertex reaches the root. -/
theorem domTree_exists_path_to_root (g : ConnectedGraph verts) (v : Vertex verts) :
    Nonempty (DepGraph.Path (domTree g).toDepGraph v (domTree g).root) :=
  (domTree g).exists_path_to_root v

end ConnectedGraph

end DominatorTree
