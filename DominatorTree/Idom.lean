import DominatorTree.Dist

namespace DominatorTree

variable {V : Type} {verts : List V}

/-- A nonempty, bounded set of naturals has a greatest element. -/
theorem exists_max {P : Nat → Prop} (hne : ∃ n, P n) :
    ∀ B : Nat, (∀ n, P n → n ≤ B) → ∃ m, P m ∧ ∀ n, P n → n ≤ m := by
  intro B
  induction B with
  | zero =>
    intro hB
    obtain ⟨n, hn⟩ := hne
    have hn0 : n = 0 := Nat.le_zero.mp (hB n hn)
    subst hn0
    exact ⟨0, hn, hB⟩
  | succ B ih =>
    intro hB
    rcases Classical.em (P (B + 1)) with hP | hP
    · exact ⟨B + 1, hP, hB⟩
    · refine ih (fun n hn => ?_)
      have hnB := hB n hn
      by_cases hEq : n = B + 1
      · exact absurd (hEq ▸ hn) hP
      · omega

namespace ConnectedGraph

variable {g : ConnectedGraph verts}

/-- A strict dominator is strictly closer to the root. -/
theorem dist_lt_of_strictlyDominates {u v : Vertex verts} (h : g.StrictlyDominates u v) :
    g.dist u < g.dist v :=
  DepGraph.dominates_dist_lt h.1 h.2 (g.isDist_dist u) (g.isDist_dist v)

/-- Every vertex but the root has an immediate dominator.

Take the strict dominator `u` of `v` that is *furthest* from the root; it is
the immediate one. For any other strict dominator `w`, a shortest path to `v`
splits at `u` into `Q ++ R`, and `w` cannot lie on `R`: a vertex there would be
at distance `dist u + (its offset)`, which exceeds `dist u` unless it is `u`
itself. So if some path `P` to `u` avoided `w`, then `P ++ R` would reach `v`
while avoiding `w`, contradicting that `w` dominates `v`. -/
theorem exists_isIdom (g : ConnectedGraph verts) (v : Vertex verts) (hv : v ≠ g.root) :
    ∃ u, g.IsIdom u v := by
  -- the distances of the strict dominators of `v` are bounded by `dist v`
  have hbound : ∀ d, (∃ u, g.StrictlyDominates u v ∧ g.dist u = d) → d ≤ g.dist v := by
    rintro d ⟨u, hu, rfl⟩
    exact Nat.le_of_lt (dist_lt_of_strictlyDominates hu)
  -- and the root is one of them, so the set is nonempty
  have hne : ∃ d, ∃ u, g.StrictlyDominates u v ∧ g.dist u = d :=
    ⟨g.dist g.root, g.root, g.root_strictlyDominates (Ne.symm hv), rfl⟩
  obtain ⟨m, ⟨u, hu, hum⟩, hmax⟩ := exists_max hne _ hbound
  refine ⟨u, hu, ?_⟩
  intro w hw P
  -- suppose some path `P : root → u` misses `w`
  apply Classical.byContradiction
  intro hwP
  -- cut a shortest path to `v` at `u`
  obtain ⟨S, hS⟩ := (g.isDist_dist v).1
  obtain ⟨Q, R, hQR⟩ := S.exists_split u (hu.1 S)
  have hQ : g.dist u ≤ Q.length := (g.isDist_dist u).2 Q
  have hRlow : g.dist v ≤ g.dist u + R.length := by
    obtain ⟨Su, hSu⟩ := (g.isDist_dist u).1
    have hle := (g.isDist_dist v).2 (Su.append R)
    simpa [hSu] using hle
  have hQlen : Q.length = g.dist u := by omega
  -- `w` cannot lie on the second half
  have hwR : w ∉ R.vertices := by
    intro hmem
    obtain ⟨R1, R2, hR⟩ := R.exists_split w hmem
    have h1 : g.dist w ≤ Q.length + R1.length := by
      have hle := (g.isDist_dist w).2 (Q.append R1)
      simpa using hle
    have h2 : g.dist v ≤ g.dist w + R2.length := by
      obtain ⟨Sw, hSw⟩ := (g.isDist_dist w).1
      have hle := (g.isDist_dist v).2 (Sw.append R2)
      simpa [hSw] using hle
    have hwmax : g.dist w ≤ m := hmax _ ⟨w, hw, rfl⟩
    have hR1 : R1.length = 0 := by omega
    have huw : u = w := DepGraph.Path.eq_of_length_zero R1 hR1
    exact hwP (huw ▸ P.end_mem_vertices)
  -- then `P ++ R` reaches `v` while avoiding `w`, contradicting `w` dominating `v`
  rcases DepGraph.Path.mem_vertices_append P R (hw.1 (P.append R)) with hmem | hmem
  · exact hwP hmem
  · exact hwR hmem

/-- Immediate dominators always exist, so the dominator tree is total. -/
theorem hasIdoms (g : ConnectedGraph verts) :
    ∀ v : Vertex verts, v ≠ g.root → ∃ u, g.IsIdom u v :=
  g.exists_isIdom

/-- Every vertex but the root has exactly one immediate dominator. -/
theorem existsUnique_isIdom (g : ConnectedGraph verts) (v : Vertex verts) (hv : v ≠ g.root) :
    ∃ u, g.IsIdom u v ∧ ∀ u', g.IsIdom u' v → u' = u := by
  obtain ⟨u, hu⟩ := g.exists_isIdom v hv
  exact ⟨u, hu, fun u' hu' => g.isIdom_unique hu' hu⟩

end ConnectedGraph

end DominatorTree
