namespace DominatorTree

/-- A vertex of a graph on `verts`: a label together with a proof it occurs. -/
abbrev Vertex {V : Type} (verts : List V) : Type := {v // v ∈ verts}

/-- A directed graph on the vertices listed in `verts`.

Typing keeps edges inside `verts`. Successor lists may repeat an entry, so this
is really a multigraph. -/
structure Digraph {V : Type} (verts : List V) where
  /-- The out-neighbours of each vertex. -/
  out : Vertex verts → List (Vertex verts)

/-- A `Digraph` with a distinguished root, the entry point dominance is
measured from. -/
structure DepGraph {V : Type} (verts : List V) extends Digraph verts where
  /-- The entry vertex. -/
  root : Vertex verts

namespace DepGraph

variable {V : Type} {verts : List V}

/-- `w` is a successor of `v`. -/
def Edge (g : DepGraph verts) (v w : Vertex verts) : Prop := w ∈ g.out v

/-- A directed path from `u` to `w`. Vertices may repeat: these are walks.

In `Type` rather than `Prop` so that `vertices` can be extracted. -/
inductive Path (g : DepGraph verts) : Vertex verts → Vertex verts → Type where
  /-- The empty path from `v` to itself. -/
  | nil (v : Vertex verts) : Path g v v
  /-- Extend a path at the front by an edge `u → v`. -/
  | cons {u v w : Vertex verts} (h : g.Edge u v) (p : Path g v w) : Path g u w

namespace Path

variable {g : DepGraph verts}

/-- The vertices visited, in order, including both endpoints. -/
def vertices : {u w : Vertex verts} → Path g u w → List (Vertex verts)
  | u, _, .nil _ => [u]
  | u, _, .cons _ p => u :: p.vertices

/-- The number of edges. -/
def length : {u w : Vertex verts} → Path g u w → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ p => p.length + 1

/-- A path visits its start vertex. -/
theorem start_mem_vertices : ∀ {u w : Vertex verts} (p : Path g u w), u ∈ p.vertices := by
  intro u w p
  cases p with
  | nil _ => simp [vertices]
  | cons _ _ => simp [vertices]

/-- A path visits its end vertex. -/
theorem end_mem_vertices : ∀ {u w : Vertex verts} (p : Path g u w), w ∈ p.vertices := by
  intro u w p
  induction p with
  | nil _ => simp [vertices]
  | cons _ _ ih => simp [vertices, ih]

/-- Every vertex on a path is the endpoint of a prefix of it, which is no
longer than the whole path. -/
theorem exists_prefix : ∀ {u w : Vertex verts} (p : Path g u w) (x : Vertex verts),
    x ∈ p.vertices → ∃ q : Path g u x, q.length ≤ p.length := by
  intro u w p
  induction p with
  | nil v =>
    intro x hx
    simp [vertices] at hx
    subst hx
    exact ⟨.nil _, Nat.le_refl _⟩
  | cons h p' ih =>
    intro x hx
    simp [vertices] at hx
    rcases hx with rfl | hx
    · exact ⟨.nil _, Nat.zero_le _⟩
    · obtain ⟨q, hq⟩ := ih x hx
      exact ⟨.cons h q, by simpa [length] using hq⟩

/-- A vertex on a path, other than its endpoint, ends a strictly shorter
prefix — it has to occur before the last position. -/
theorem exists_prefix_lt : ∀ {u w : Vertex verts} (p : Path g u w) (x : Vertex verts),
    x ∈ p.vertices → x ≠ w → ∃ q : Path g u x, q.length < p.length := by
  intro u w p
  induction p with
  | nil v =>
    intro x hx hne
    simp [vertices] at hx
    exact absurd hx hne
  | cons h p' ih =>
    intro x hx hne
    simp [vertices] at hx
    rcases hx with rfl | hx
    · exact ⟨.nil _, by simp [length]⟩
    · obtain ⟨q, hq⟩ := ih x hx hne
      exact ⟨.cons h q, by simpa [length] using hq⟩

/-- Concatenation of paths. -/
def append : {u v w : Vertex verts} → Path g u v → Path g v w → Path g u w
  | _, _, _, .nil _, q => q
  | _, _, _, .cons h p, q => .cons h (p.append q)

@[simp] theorem length_append : ∀ {u v w : Vertex verts} (p : Path g u v) (q : Path g v w),
    (p.append q).length = p.length + q.length := by
  intro u v w p
  induction p with
  | nil _ => intro q; simp [append, length]
  | cons _ p' ih => intro q; simp [append, length, ih]; omega

/-- A vertex of a concatenation comes from one of the two halves. -/
theorem mem_vertices_append : ∀ {u v w : Vertex verts} (p : Path g u v) (q : Path g v w)
    {x : Vertex verts}, x ∈ (p.append q).vertices → x ∈ p.vertices ∨ x ∈ q.vertices := by
  intro u v w p
  induction p with
  | nil _ => intro q x hx; exact Or.inr hx
  | cons _ p' ih =>
    intro q x hx
    simp [append, vertices] at hx
    rcases hx with rfl | hx
    · exact Or.inl (by simp [vertices])
    · rcases ih q hx with h | h
      · exact Or.inl (by simp [vertices, h])
      · exact Or.inr h

/-- A path with no edges connects a vertex to itself. -/
theorem eq_of_length_zero : ∀ {u w : Vertex verts} (p : Path g u w), p.length = 0 → u = w := by
  intro u w p
  cases p with
  | nil _ => intro _; rfl
  | cons _ _ => intro h; simp [length] at h

/-- A path can be cut at any vertex it visits, into a prefix and a suffix whose
lengths add up to the whole and which visit only vertices of the original. -/
theorem exists_split : ∀ {u w : Vertex verts} (p : Path g u w) (x : Vertex verts),
    x ∈ p.vertices → ∃ (q : Path g u x) (r : Path g x w),
      q.length + r.length = p.length ∧
      (∀ y ∈ q.vertices, y ∈ p.vertices) ∧ (∀ y ∈ r.vertices, y ∈ p.vertices) := by
  intro u w p
  induction p with
  | nil v =>
    intro x hx
    simp [vertices] at hx
    subst hx
    exact ⟨.nil _, .nil _, rfl, fun _ h => h, fun _ h => h⟩
  | cons h p' ih =>
    intro x hx
    simp [vertices] at hx
    rcases hx with rfl | hx
    · refine ⟨.nil _, .cons h p', by simp [length], ?_, fun _ hy => hy⟩
      intro y hy
      simp [vertices] at hy ⊢
      exact Or.inl hy
    · obtain ⟨q, r, hqr, hqv, hrv⟩ := ih x hx
      refine ⟨.cons h q, r, by simp [length]; omega, ?_, ?_⟩
      · intro y hy
        simp [vertices] at hy ⊢
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (hqv y hy)
      · intro y hy
        simp [vertices]
        exact Or.inr (hrv y hy)

/-- A path with at least one edge has a last edge, whose source it visits. -/
theorem exists_last_edge : ∀ {u w : Vertex verts} (p : Path g u w), 0 < p.length →
    ∃ x, x ∈ p.vertices ∧ g.Edge x w := by
  intro u w p
  induction p with
  | nil v => intro h; simp [length] at h
  | @cons a b c hedge p' ih =>
    intro _
    rcases Nat.eq_zero_or_pos p'.length with h0 | hpos
    · have hbc : b = c := eq_of_length_zero p' h0
      subst hbc
      exact ⟨a, by simp [vertices], hedge⟩
    · obtain ⟨x, hxmem, hxe⟩ := ih hpos
      exact ⟨x, by simp [vertices, hxmem], hxe⟩

end Path

/-- Every path from the root to `v` passes through `u`. -/
def Dominates (g : DepGraph verts) (u v : Vertex verts) : Prop :=
  ∀ p : Path g g.root v, u ∈ p.vertices

/-- Dominance is reflexive. -/
theorem dominates_refl (g : DepGraph verts) (v : Vertex verts) : g.Dominates v v :=
  fun p => p.end_mem_vertices

/-- The root dominates every vertex. -/
theorem root_dominates (g : DepGraph verts) (v : Vertex verts) : g.Dominates g.root v :=
  fun p => p.start_mem_vertices

/-- A vertex unreachable from the root is dominated by everything, vacuously.

So the dominator relation is a tree only on the reachable vertices. -/
theorem dominates_of_unreachable (g : DepGraph verts) {v : Vertex verts}
    (h : Path g g.root v → False) (u : Vertex verts) : g.Dominates u v :=
  fun p => (h p).elim

/-- `u` dominates `v` and is not `v` itself. -/
def StrictlyDominates (g : DepGraph verts) (u v : Vertex verts) : Prop :=
  g.Dominates u v ∧ u ≠ v

/-- `u` is the immediate dominator of `v`, its parent in the dominator tree: it
strictly dominates `v`, and is the closest such vertex in the sense that every
strict dominator of `v` also dominates `u`.

At most one vertex can satisfy this (`IsIdom.unique`), which is what makes
"parent" well defined. -/
def IsIdom (g : DepGraph verts) (u v : Vertex verts) : Prop :=
  g.StrictlyDominates u v ∧ ∀ w, g.StrictlyDominates w v → g.Dominates w u

/-- The root strictly dominates every other vertex. -/
theorem root_strictlyDominates (g : DepGraph verts) {v : Vertex verts} (hne : g.root ≠ v) :
    g.StrictlyDominates g.root v :=
  ⟨g.root_dominates v, hne⟩

end DepGraph

/-- A `DepGraph` in which every vertex is reachable from the root.

Dominance is only tree-shaped on reachable vertices — an unreachable vertex is
dominated by everything and so has no closest dominator — so the theory is
stated here, where that hypothesis is discharged once and for all. -/
structure ConnectedGraph {V : Type} (verts : List V) extends DepGraph verts where
  /-- Every vertex is reachable from the root. -/
  reach : ∀ v : Vertex verts, Nonempty (DepGraph.Path toDepGraph toDepGraph.root v)

namespace DepGraph

end DepGraph

end DominatorTree
