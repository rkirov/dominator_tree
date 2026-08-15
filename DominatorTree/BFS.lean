import DominatorTree.Basic

namespace DominatorTree

namespace DepGraph

variable {V : Type} [DecidableEq V] {verts : List V}

/-- One level-synchronous BFS pass: emits `frontier`, then recurses on the
successors of `frontier` not already `visited`.

`fuel` is what makes the recursion structural; since every level is nonempty
and disjoint from the previous ones, `verts.length` levels always suffice. -/
def bfsLevelsGo (g : DepGraph verts) :
    Nat → List (Vertex verts) → List (Vertex verts) → List (List (Vertex verts))
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, visited, frontier =>
      -- Filter against `acc` too, since `out` may repeat a successor.
      let next := (frontier.flatMap g.out).foldl
        (fun acc w => if visited.contains w || acc.contains w then acc else acc ++ [w]) []
      frontier :: bfsLevelsGo g fuel (visited ++ next) next

/-- The vertices reachable from the root, grouped by distance from it: entry `i`
holds the vertices at distance exactly `i`. Level `0` is `[g.root]`. -/
def bfsLevels (g : DepGraph verts) : List (List (Vertex verts)) :=
  bfsLevelsGo g verts.length [g.root] [g.root]

/-- Distance from the root to `v`: the number of edges on a shortest path, or
`none` if `v` is unreachable. -/
def dist? (g : DepGraph verts) (v : Vertex verts) : Option Nat :=
  g.bfsLevels.findIdx? (·.contains v)

/-- The vertices reachable from the root, in breadth-first visit order. -/
def bfsOrder (g : DepGraph verts) : List (Vertex verts) :=
  g.bfsLevels.flatten

end DepGraph

end DominatorTree
