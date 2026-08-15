# dominator_tree

A Lean 4 formalization of dominator trees for dependency graphs, with a verified
algorithm that computes them. Uses only what ships with the toolchain — core Lean
and `Std` — and has no external dependencies.

A vertex `u` **dominates** `v` when every path from the root to `v` passes through
`u`. The main theoretical result is that immediate dominators exist, are unique,
and form a tree; the main practical one is that `idom?` computes that tree and is
proved to meet the specification.

## Layout

| File | Contents |
| --- | --- |
| `Basic.lean` | `Digraph`, `DepGraph`, `ConnectedGraph`, paths and path surgery, `Dominates`, `IsIdom`, the dataflow equation |
| `Dist.lean` | shortest-path distance `IsDist`, dominance ordering, antisymmetry |
| `Idom.lean` | existence of immediate dominators, and that dominators are linearly ordered |
| `Tree.lean` | `Tree`, acyclicity, the (noncomputable) dominator tree |
| `Reducible.lean` | back edges, reducibility, and an irreducible example |
| `Algorithm.lean` | the verified construction of the dominator tree |

## The theory

- `ConnectedGraph.exists_isIdom` — every vertex but the root has an immediate
  dominator: the strict dominator furthest from the root.
- `ConnectedGraph.isIdom_unique` — and at most one, so the parent is well defined.
- `ConnectedGraph.dominates_total` — the dominators of a vertex are linearly
  ordered, so they form a chain rather than a partial order.
- `ConnectedGraph.domTree` — the dominator tree, with `mem_domTree_out_iff`
  showing its edges are exactly the immediate-dominator relation,
  `domTree_acyclic` that it has no cycles, and `domTree_exists_path_to_root`
  that following parents reaches the root.
- `DepGraph.dominates_dist_le` / `dominates_dist_lt` — a dominator is never
  further from the root, and a strict dominator is strictly closer.
- `DepGraph.dominates_iff_preds` — the dataflow equation
  `dom v = {v} ∪ ⋂ dom (preds v)`, derived directly from paths. Every dominator
  algorithm is proved against this.
- `DepGraph.Reducible` — every cycle has a header dominating all of it — with
  `forwardAcyclic_of_reducible` proving a reducible graph loses every cycle when
  back edges are deleted, and `TwoEntryLoop.not_reducible` exhibiting the
  smallest irreducible graph, a loop entered at two places.

## The algorithm

For a graph carrying a topological rank — a DAG, or the back-edge-free part of a
reducible graph — every predecessor of a vertex is ranked below it, so the tree
is built in one pass with no fixpoint iteration.

- `DepGraph.idom?` — the immediate dominator tree, proved sound
  (`isIdom_of_idom?`) and, on a connected graph, total (`idom?_isSome`).
- `DepGraph.buildUpTo` / `buildUpTo_correct` — the construction: vertices are
  processed in rank order and each parent is stored in a `Table`, so every
  parent is computed exactly once.
- `DepGraph.lca` / `lca_spec` — the parent of `v` is the lowest common ancestor
  of `v`'s predecessors, found by climbing parent pointers. Each step replaces
  the deeper vertex by its parent, which is sound because a common dominator is
  a *strict* dominator of the deeper one and so dominates that one's parent.
- `DepGraph.domWalk` / `domWalk_iff` — dominance is not stored but recomputed by
  climbing the tree, and the climb is proved to decide it.

The caller supplies the rank and a proof it increases along edges;
`topoRank_of_forall_mem` reduces that obligation to `by decide` for concrete
graphs. The algorithm needs `[DecidableEq V]` and `[Hashable V]`.

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
- The climb terminates *by typing*: `Table.get` returns
  `{u // rank u < rank v}`, so the recursion measure falls out of the result
  type rather than needing an invariant about the table.
- The `Table` must be data — it is a `Std.HashMap`. A function-valued table
  looks like memoization but is a partial application that recomputes the whole
  construction on every lookup; that version was exponential, and measurably
  slower than doing no memoization at all. Only `Table.get`, `Table.insert` and
  two lemmas about them touch the representation, so swapping it out is local.

## Next steps

Ordered by how much they are worth.

- **Precompute predecessors.** `preds v` rescans every vertex and every out-list
  on each call, so building the tree costs `O(n·(n+m))` where it should cost
  `O(m·depth)`. Inverting the adjacency once would fix the dominant term.
- **Topological sort.** The rank has to be supplied by the caller, because
  deriving one from acyclicity — `Acyclic → Ranked` for a finite graph — is not
  formalized. The same lemma is what the Hecht–Ullman converse needs.
- **Hecht–Ullman.** `forwardAcyclic_of_reducible` is proved; the converse is not.
  It is harder than it looks: knowing a cycle contains *some* back edge does not
  make that edge's head a header. See the note on `ForwardAcyclic`.
- **Irreducible graphs.** The construction here needs a topological rank, so it
  does not apply. The options are Purdom–Moore (`O(n·(n+m))`, cheapest to verify
  since it mirrors the existing existence proof), Cooper–Harvey–Kennedy
  (iterative dataflow, needs a fixpoint argument on top of the dataflow
  equation), and Lengauer–Tarjan (near-linear, but semidominators need a DFS
  tree first, so by far the largest proof).

## Build

```
lake build
```

Requires the toolchain in `lean-toolchain` (Lean 4.33.0).
