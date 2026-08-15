# dominator_tree

A Lean 4 formalization of dominator trees for dependency graphs. Core Lean only —
no Mathlib, no dependencies.

A vertex `u` **dominates** `v` when every path from the root to `v` passes through
`u`. The main result is that immediate dominators exist, are unique, and form a
tree.

## Layout

| File | Contents |
| --- | --- |
| `Basic.lean` | `Digraph`, `DepGraph`, `ConnectedGraph`, paths and path surgery, `Dominates`, `IsIdom` |
| `Dist.lean` | shortest-path distance `IsDist`, dominance ordering, antisymmetry |
| `Idom.lean` | existence of immediate dominators |
| `Tree.lean` | `Tree`, acyclicity, the dominator tree |
| `BFS.lean` | executable breadth-first levels, distance and visit order |

## Main results

- `ConnectedGraph.exists_isIdom` — every vertex but the root has an immediate
  dominator, found by taking the strict dominator furthest from the root.
- `ConnectedGraph.isIdom_unique` — and at most one, so the parent is well defined.
- `ConnectedGraph.domTree` — the dominator tree, with
  `mem_domTree_out_iff` showing its edges are exactly the immediate-dominator
  relation, `domTree_acyclic` that it has no cycles, and
  `domTree_exists_path_to_root` that following parents reaches the root.
- `DepGraph.dominates_dist_le` / `dominates_dist_lt` — a dominator is never
  further from the root, and a strict dominator is strictly closer.

Everything is proved: no `sorry`, no custom axioms. Some results use
`Classical.choice`, which enters through choosing a least path length.

## Design notes

- Vertices are `{v // v ∈ verts}` for a list `verts`, so edges cannot leave the
  declared vertex set — `out ⊆ verts` holds by typing. The label type `V` need
  not be finite.
- `Path` lives in `Type`, not `Prop`, so that the vertices a path visits can be
  extracted. Paths are walks: vertices may repeat.
- Acyclicity is defined as "the only path from a vertex to itself is empty", and
  proved from a rank that decreases along edges (`DepGraph.Ranked.acyclic`).

## Not done yet

`BFS.lean` is executable but is not yet proved to agree with `IsDist`, so
`domTree` is noncomputable — it is the mathematical object, not an algorithm.
Closing that gap is what a verified, computable dominator tree would need.

## Build

```
lake build
```

Requires the toolchain in `lean-toolchain` (Lean 4.33.0).
