import DominatorTree.Tree

namespace DominatorTree

namespace DepGraph

variable {V : Type} {verts : List V}

/-- A back edge: one whose target dominates its source, i.e. an edge jumping
back to a loop header that controls it. -/
def IsBackEdge (g : DepGraph verts) (u v : Vertex verts) : Prop :=
  g.Edge u v ∧ g.Dominates v u

/-- A graph is reducible when every cycle has a single header controlling it:
some vertex on the cycle dominates every vertex of the cycle.

This is the Hecht–Ullman characterisation. Irreducibility is its negation, and
means some loop can be entered at two different places. -/
def Reducible (g : DepGraph verts) : Prop :=
  ∀ (v : Vertex verts) (p : Path g v v), 0 < p.length →
    ∃ h, h ∈ p.vertices ∧ ∀ x ∈ p.vertices, g.Dominates h x

open Classical in
/-- The graph with every back edge deleted. -/
noncomputable def forward (g : DepGraph verts) : DepGraph verts where
  out := fun v => (g.out v).filter (fun w => !decide (g.Dominates w v))
  root := g.root

/-- The other standard characterisation of reducibility: deleting the back
edges leaves a directed acyclic graph, i.e. every cycle uses a back edge.

`forwardAcyclic_of_reducible` proves one direction. The converse — the
Hecht–Ullman theorem — is not proved here, and is harder than it looks: knowing
a cycle contains *some* back edge `x → h` does not make `h` a header. In nested
loops with outer header `1` and inner header `2`, the cycle through both
contains the inner back edge, yet `2` does not dominate `1`. The header is
instead the vertex of the cycle closest to the root — necessarily unique, since
strict dominance strictly decreases distance — but identifying it needs a
topological order on `forward`, which `Acyclic` does not directly supply. -/
def ForwardAcyclic (g : DepGraph verts) : Prop :=
  (g.forward).Acyclic

theorem forward_out_subset {g : DepGraph verts} {v w : Vertex verts}
    (h : w ∈ (g.forward).out v) : w ∈ g.out v := by
  simp [forward, List.mem_filter] at h
  exact h.1

/-- A path of the forward graph is a path of the original. -/
def forwardPath {g : DepGraph verts} :
    {u w : Vertex verts} → Path (g.forward) u w → Path g u w
  | _, _, .nil v => .nil v
  | _, _, .cons h p => .cons (forward_out_subset h) (forwardPath p)

@[simp] theorem length_forwardPath {g : DepGraph verts} :
    ∀ {u w : Vertex verts} (p : Path (g.forward) u w), (forwardPath p).length = p.length := by
  intro u w p
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [forwardPath, Path.length, ih]

theorem mem_forward_out {g : DepGraph verts} {v w : Vertex verts} :
    w ∈ (g.forward).out v ↔ w ∈ g.out v ∧ ¬ g.Dominates w v := by
  simp [forward, List.mem_filter]

@[simp] theorem vertices_forwardPath {g : DepGraph verts} :
    ∀ {u w : Vertex verts} (p : Path (g.forward) u w),
      (forwardPath p).vertices = p.vertices := by
  intro u w p
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [forwardPath, Path.vertices, ih]

/-- A reducible graph loses all its cycles when back edges are deleted.

A cycle surviving in `forward` would still have a header `h` dominating it, and
the cycle's own edge into `h` would then be a back edge — but back edges are
exactly what `forward` removed. -/
theorem forwardAcyclic_of_reducible {g : DepGraph verts} (hred : g.Reducible) :
    g.ForwardAcyclic := by
  intro v p
  rcases Nat.eq_zero_or_pos p.length with h0 | hpos
  · exact h0
  · exfalso
    -- the same cycle in `g` has a header dominating all of it
    have hgp : 0 < (forwardPath p).length := by simpa using hpos
    obtain ⟨hd, hdmem, hdall⟩ := hred v (forwardPath p) hgp
    rw [vertices_forwardPath] at hdmem hdall
    -- cut the cycle at the header and take the edge arriving there
    obtain ⟨q, r, hlen, hqv, hrv⟩ := p.exists_split hd hdmem
    rcases Nat.eq_zero_or_pos q.length with hq0 | hqpos
    · have hvhd : v = hd := Path.eq_of_length_zero q hq0
      subst hvhd
      obtain ⟨x, hxmem, hxe⟩ := r.exists_last_edge (by omega)
      exact (mem_forward_out.mp hxe).2 (hdall x (hrv x hxmem))
    · obtain ⟨x, hxmem, hxe⟩ := q.exists_last_edge hqpos
      exact (mem_forward_out.mp hxe).2 (hdall x (hqv x hxmem))

/-- An acyclic graph is reducible: there are no cycles to control. -/
theorem reducible_of_acyclic {g : DepGraph verts} (h : g.Acyclic) : g.Reducible := by
  intro v p hp
  exact absurd (h v p) (by omega)

/-- An acyclic graph stays acyclic when back edges are removed. -/
theorem forwardAcyclic_of_acyclic {g : DepGraph verts} (h : g.Acyclic) : g.ForwardAcyclic := by
  intro v p
  have := h v (forwardPath p)
  simpa using this

end DepGraph

/-! ### An irreducible graph

The smallest irreducible example: a two-vertex loop that can be entered at
either vertex, so neither one controls it.

```
      0
     / \
    v   v
    1 <-> 2
```
-/
namespace TwoEntryLoop

open DepGraph

/-- Vertices `0`, `1`, `2`. -/
abbrev verts : List (Fin 3) := List.finRange 3

/-- A vertex from its index. -/
def vtx (i : Fin 3) : Vertex verts := ⟨i, List.mem_finRange i⟩

/-- `0 → 1`, `0 → 2`, and `1 ↔ 2`. -/
def g : DepGraph verts where
  out := fun v => (([[1, 2], [2], [1]] : List (List (Fin 3))).getD v.val.val []).map vtx
  root := vtx 0

theorem e01 : g.Edge (vtx 0) (vtx 1) := by show _ ∈ _; decide
theorem e02 : g.Edge (vtx 0) (vtx 2) := by show _ ∈ _; decide
theorem e12 : g.Edge (vtx 1) (vtx 2) := by show _ ∈ _; decide
theorem e21 : g.Edge (vtx 2) (vtx 1) := by show _ ∈ _; decide

/-- Reaching `2` directly from the root shows `1` does not dominate it. -/
theorem not_dominates_1_2 : ¬ g.Dominates (vtx 1) (vtx 2) := by
  intro hd
  have := hd (.cons e02 (.nil _))
  simp [Path.vertices, g, vtx] at this

/-- And symmetrically. -/
theorem not_dominates_2_1 : ¬ g.Dominates (vtx 2) (vtx 1) := by
  intro hd
  have := hd (.cons e01 (.nil _))
  simp [Path.vertices, g, vtx] at this

/-- The cycle `1 → 2 → 1`. -/
def cyc : Path g (vtx 1) (vtx 1) := .cons e12 (.cons e21 (.nil _))

theorem cyc_vertices : cyc.vertices = [vtx 1, vtx 2, vtx 1] := rfl

/-- The graph is not reducible: the cycle `1 → 2 → 1` has no header, because
neither vertex dominates the other. -/
theorem not_reducible : ¬ g.Reducible := by
  intro hred
  obtain ⟨h, hmem, hall⟩ := hred (vtx 1) cyc (by decide)
  rw [cyc_vertices] at hmem hall
  have h1 : h = vtx 1 ∨ h = vtx 2 := by
    simp at hmem
    rcases hmem with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact Or.inl a
  rcases h1 with rfl | rfl
  · exact not_dominates_1_2 (hall (vtx 2) (by simp))
  · exact not_dominates_2_1 (hall (vtx 1) (by simp))

/-- Neither edge of the cycle is a back edge, so both survive in `forward`. -/
theorem fe12 : (g.forward).Edge (vtx 1) (vtx 2) := by
  have hmem : vtx 2 ∈ g.out (vtx 1) := e12
  simp [DepGraph.Edge, DepGraph.forward, List.mem_filter, hmem, not_dominates_2_1]

theorem fe21 : (g.forward).Edge (vtx 2) (vtx 1) := by
  have hmem : vtx 1 ∈ g.out (vtx 2) := e21
  simp [DepGraph.Edge, DepGraph.forward, List.mem_filter, hmem, not_dominates_1_2]

/-- The same cycle, still present after deleting back edges. -/
def fcyc : Path (g.forward) (vtx 1) (vtx 1) := .cons fe12 (.cons fe21 (.nil _))

/-- The graph is irreducible under the other characterisation too: deleting
back edges does not break the cycle, because it contains none. -/
theorem not_forwardAcyclic : ¬ g.ForwardAcyclic := by
  intro hacyc
  have := hacyc (vtx 1) fcyc
  simp [fcyc, Path.length] at this

end TwoEntryLoop

end DominatorTree
