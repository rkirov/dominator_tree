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
| `Reducible.lean` | back edges, reducibility, and an irreducible example |
| `Algorithm.lean` | the dataflow equation, and a verified single-pass construction of the dominator tree |

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
- `DepGraph.idom?` — a computable immediate-dominator tree for graphs carrying a
  topological rank (a DAG, or a reducible graph's forward part), proved sound
  (`isIdom_of_idom?`) and, on a connected graph, total (`idom?_isSome`). It rests
  on `dominates_iff_preds`, the dataflow equation `dom v = {v} ∪ ⋂ dom (preds v)`,
  derived here directly from paths.
- `DepGraph.domWalk` — dominance is not stored but recomputed by climbing that
  tree, and `domWalk_iff` proves the climb decides it. Its own termination
  relies on the tree's parents having smaller rank, so the theory is what makes
  the definition legal.
- `ConnectedGraph.dominates_total` — the dominators of a vertex are linearly
  ordered, which is what lets the immediate dominator be found by a single scan
  for the deepest one.
- `DepGraph.Reducible` — every cycle has a header dominating all of it — with
  `forwardAcyclic_of_reducible` proving a reducible graph loses every cycle
  when back edges are deleted, and `TwoEntryLoop.not_reducible` exhibiting the
  smallest irreducible graph, a loop entered at two places. The converse
  (Hecht–Ullman) is not proved.

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

## Next steps

`ConnectedGraph.domTree` is noncomputable — it is the mathematical object, not
an algorithm. `Algorithm.lean` closes part of that gap: `idom?` computes the
tree in one pass, verified against this specification, for any graph supplied
with a topological rank. Two limits remain. The rank has to be given by the
caller, because deriving one from acyclicity is a topological sort we have not
formalised. And `idom?` still materialises dominator sets on the way to the tree, so it is
`O(n²)`; the textbook `O(n·depth)` version computes each parent as the nearest
common ancestor of the predecessors, never building a set at all.

For graphs with no topological rank — irreducible ones — the remaining
algorithms are, in increasing order of both speed and difficulty:

- **Purdom–Moore**, `O(n·(n+m))`. `u` dominates `v` exactly when deleting `u`
  makes `v` unreachable, so one reachability search per vertex decides
  dominance, and the immediate dominator is read straight off the definition of
  `IsIdom`. Cheapest to verify: the algorithm mirrors the existing proof, and
  the only real obligation is that the search agrees with `Dominates`.
- **Cooper–Harvey–Kennedy**, iterative dataflow. Fast in practice and the usual
  choice in compilers. Needs predecessors, which this representation does not
  store, and a vertex numbering in which every dominator has a smaller index —
  `dominates_dist_lt` supplies one. Verifying it means proving the dataflow
  equation `dom(v) = {v} ∪ ⋂ dom(preds v)` characterises path dominance, and
  that the iteration reaches that fixpoint.
- **Lengauer–Tarjan**, near-linear. Semidominators are defined relative to a DFS
  tree, so this needs DFS and its numbering first. By far the largest proof.

Proving the first would already give a computable dominator tree; the other two
are then refinements that can be checked against it.

## Build

```
lake build
```

Requires the toolchain in `lean-toolchain` (Lean 4.33.0).
