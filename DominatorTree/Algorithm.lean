import DominatorTree.Reducible

/-!
# Computing the dominator tree

For a graph carrying a topological rank — a DAG, or the back-edge-free part of a
reducible graph — every predecessor of `v` is ranked below `v`, so dominators
need no fixpoint iteration.

The output is the immediate dominator tree, `idom?`. Dominance itself is not
stored but recomputed on demand by `domWalk`, which climbs the tree from `v`
looking for `u` — the dominators of `v` are exactly the vertices on its path to
the root.

`domSet` is an intermediate step, not the intended output.
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
/-- The dataflow equation: `w` dominates `v` exactly when it is `v`, or
dominates every predecessor of `v`. Extending a path to a predecessor by one
edge adds only `v` itself, and conversely every path to a non-root `v` ends with
an edge from a predecessor. -/
theorem dominates_iff_preds {g : DepGraph verts} {v : Vertex verts} (hv : v ≠ g.root)
    (w : Vertex verts) :
    g.Dominates w v ↔ (w = v ∨ ∀ p, g.Edge p v → g.Dominates w p) := by
  constructor
  · intro hdom
    by_cases hwv : w = v
    · exact Or.inl hwv
    refine Or.inr fun p hp P => ?_
    have hmem := hdom (P.append (.cons hp (.nil v)))
    rcases Path.mem_vertices_append P _ hmem with h | h
    · exact h
    · simp [Path.vertices] at h
      rcases h with rfl | rfl
      · exact P.end_mem_vertices
      · exact absurd rfl hwv
  · rintro (rfl | hall) P
    · exact P.end_mem_vertices
    · have hpos : 0 < P.length := by
        rcases Nat.eq_zero_or_pos P.length with h0 | h
        · exact absurd (Path.eq_of_length_zero P h0).symm hv
        · exact h
      obtain ⟨x, q, he, hqv⟩ := P.exists_last_edge_path hpos
      exact hqv w (hall x he q)

/-- A rank that strictly increases along every edge: a topological numbering. -/
def TopoRank (g : DepGraph verts) (rank : Vertex verts → Nat) : Prop :=
  ∀ v u, u ∈ g.out v → rank v < rank u

omit [DecidableEq V] in
/-- Checking a topological rank only needs the vertices actually listed, so this
form is decidable. -/
theorem topoRank_of_forall_mem {g : DepGraph verts} {rank : Vertex verts → Nat}
    (h : ∀ v ∈ verts.attach, ∀ u ∈ g.out v, rank v < rank u) : g.TopoRank rank :=
  fun v u hu => h v (List.mem_attach _ _) u hu

omit [DecidableEq V] in
/-- A topological rank grows by at least the length of any path. -/
theorem topoRank_add_le {g : DepGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.TopoRank rank) :
    ∀ {u w : Vertex verts} (p : Path g u w), rank u + p.length ≤ rank w := by
  intro u w p
  induction p with
  | nil v => simp [Path.length]
  | @cons a b c hedge p' ih =>
    have hlt : rank a < rank b := htopo a b hedge
    simp only [Path.length]
    omega

omit [DecidableEq V] in
/-- On a connected graph a strict dominator has strictly smaller rank, so the
dominance order agrees with the rank order. -/
theorem rank_lt_of_dominates {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    (htopo : g.toDepGraph.TopoRank rank) {u v : Vertex verts}
    (hdom : g.Dominates u v) (hne : u ≠ v) : rank u < rank v := by
  obtain ⟨P⟩ := g.reach v
  obtain ⟨-, R, -, -, -⟩ := P.exists_split u (hdom P)
  have hRpos : 0 < R.length := by
    rcases Nat.eq_zero_or_pos R.length with h0 | h
    · exact absurd (Path.eq_of_length_zero R h0) hne
    · exact h
  have hle := topoRank_add_le htopo R
  omega

/-! ## Step one: dominator sets, an intermediate the tree is read off from -/

/-- Intersect a family of lists, starting from a universe list. An empty family
gives the whole universe, the right answer for a vertex with no predecessors:
everything dominates it vacuously. -/
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

/-- The dominators of `v`, in one pass. Terminates because every predecessor of
`v` has strictly smaller rank, which is why no iteration is needed. -/
def domSet (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : List (Vertex verts) :=
  if v = g.root then [v]
  else
    v :: interAll verts.attach ((g.preds v).attach.map (fun p => domSet g rank htopo p.val))
termination_by rank v
decreasing_by
  exact htopo _ _ (mem_preds.mp p.property)

/-- The one-pass computation returns exactly the dominators. -/
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

/-! ## Step two: the immediate dominator tree -/

variable {g : DepGraph verts} {rank : Vertex verts → Nat} {htopo : g.TopoRank rank}

/-- The strict dominators of `v`. -/
def strictDoms (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : List (Vertex verts) :=
  (domSet g rank htopo v).filter (fun u => decide (u ≠ v))

theorem mem_strictDoms {v u : Vertex verts} :
    u ∈ strictDoms g rank htopo v ↔ g.StrictlyDominates u v := by
  simp [strictDoms, List.mem_filter, mem_domSet, StrictlyDominates]

/-- The largest-ranked of `a` and the elements of `l`. -/
def maxByRank (rank : Vertex verts → Nat) (a : Vertex verts) :
    List (Vertex verts) → Vertex verts
  | [] => a
  | b :: bs => if rank a ≤ rank b then maxByRank rank b bs else maxByRank rank a bs

omit [DecidableEq V] in
theorem maxByRank_mem {rank : Vertex verts → Nat} :
    ∀ (l : List (Vertex verts)) (a : Vertex verts), maxByRank rank a l ∈ a :: l := by
  intro l
  induction l with
  | nil => intro a; simp [maxByRank]
  | cons b bs ih =>
    intro a
    simp only [maxByRank]
    by_cases h : rank a ≤ rank b
    · rw [if_pos h]
      have hb := ih b
      simp only [List.mem_cons] at hb ⊢
      rcases hb with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rw [if_neg h]
      have ha := ih a
      simp only [List.mem_cons] at ha ⊢
      rcases ha with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)

omit [DecidableEq V] in
theorem le_maxByRank {rank : Vertex verts → Nat} :
    ∀ (l : List (Vertex verts)) (a x : Vertex verts), x ∈ a :: l →
      rank x ≤ rank (maxByRank rank a l) := by
  intro l
  induction l with
  | nil =>
    intro a x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [maxByRank]
  | cons b bs ih =>
    intro a x hx
    have hself : ∀ c : Vertex verts, rank c ≤ rank (maxByRank rank c bs) :=
      fun c => ih c c (by simp)
    simp only [maxByRank]
    by_cases h : rank a ≤ rank b
    · rw [if_pos h]
      rcases List.mem_cons.mp hx with h1 | h1
      · rw [h1]; exact Nat.le_trans h (hself b)
      · exact ih b x h1
    · rw [if_neg h]
      rcases List.mem_cons.mp hx with h1 | h1
      · rw [h1]; exact hself a
      · rcases List.mem_cons.mp h1 with h2 | h2
        · rw [h2]; exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_not_le h)) (hself a)
        · exact ih a x (by simp [h2])

/-- The immediate dominator of `v`: the strict dominator of largest rank.

One linear scan, no pairwise dominance tests. Correct because the dominators of
a vertex are linearly ordered (`ConnectedGraph.dominates_total`) and that order
agrees with rank (`rank_lt_of_dominates`), so the deepest strict dominator is
the immediate one. -/
def idom? (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : Option (Vertex verts) :=
  match strictDoms g rank htopo v with
  | [] => none
  | a :: as => some (maxByRank rank a as)

/-- **Soundness**: what `idom?` returns is the immediate dominator. -/
theorem isIdom_of_idom? {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v u : Vertex verts}
    (h : idom? g.toDepGraph rank htopo v = some u) : g.IsIdom u v := by
  rw [idom?] at h
  cases hds : strictDoms g.toDepGraph rank htopo v with
  | nil => rw [hds] at h; simp at h
  | cons a as =>
    rw [hds] at h
    simp only [Option.some.injEq] at h
    subst h
    have hmem : maxByRank rank a as ∈ strictDoms g.toDepGraph rank htopo v := by
      rw [hds]; exact maxByRank_mem as a
    have hmax : ∀ x ∈ strictDoms g.toDepGraph rank htopo v,
        rank x ≤ rank (maxByRank rank a as) := by
      rw [hds]; exact fun x hx => le_maxByRank as a x hx
    have hu : g.StrictlyDominates (maxByRank rank a as) v := mem_strictDoms.mp hmem
    refine ⟨hu, fun w hw => ?_⟩
    rcases ConnectedGraph.dominates_total hu.1 hw.1 with huw | hwu
    · by_cases heq : maxByRank rank a as = w
      · subst heq; exact g.dominates_refl _
      · have hlt := rank_lt_of_dominates htopo huw heq
        have hle := hmax w (mem_strictDoms.mpr hw)
        omega
    · exact hwu

/-- **Totality**: on a connected graph every non-root vertex gets a parent. -/
theorem idom?_isSome {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v : Vertex verts} (hv : v ≠ g.root) :
    (idom? g.toDepGraph rank htopo v).isSome := by
  have hroot : g.root ∈ strictDoms g.toDepGraph rank htopo v :=
    mem_strictDoms.mpr (g.root_strictlyDominates (Ne.symm hv))
  rw [idom?]
  cases hds : strictDoms g.toDepGraph rank htopo v with
  | nil => rw [hds] at hroot; simp at hroot
  | cons a as => simp

/-! ## Step three: dominance by walking the tree

Nothing about dominance needs storing: climb from `v` towards the root, and look
for `u` on the way. -/

/-- Is `u` on the path from `v` to the root of the dominator tree?

Well founded because each parent has strictly smaller rank — the theorems above
are what make this definition legal. -/
def domWalk (g : ConnectedGraph verts) (rank : Vertex verts → Nat)
    (htopo : g.toDepGraph.TopoRank rank) (u v : Vertex verts) : Bool :=
  if u = v then true
  else
    match h : idom? g.toDepGraph rank htopo v with
    | none => false
    | some m => domWalk g rank htopo u m
termination_by rank v
decreasing_by
  have hidom := isIdom_of_idom? h
  exact rank_lt_of_dominates htopo hidom.1.1 hidom.1.2

/-- **Correctness**: walking the tree decides dominance.

One way it is transitivity — the parent dominates `v`, so anything dominating
the parent dominates `v`. The other way it is the defining property of an
immediate dominator: every strict dominator of `v` also dominates `v`'s
parent. -/
theorem domWalk_iff {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} (u v : Vertex verts) :
    domWalk g rank htopo u v = true ↔ g.Dominates u v := by
  suffices H : ∀ n (v : Vertex verts), rank v = n →
      ∀ u, domWalk g rank htopo u v = true ↔ g.Dominates u v from H _ v rfl u
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv u
    rw [domWalk]
    by_cases huv : u = v
    · subst huv
      simp [g.dominates_refl u]
    · rw [if_neg huv]
      cases h : idom? g.toDepGraph rank htopo v with
      | none =>
        -- no parent means `v` is the root, which only itself dominates
        have hroot : v = g.root := by
          apply Classical.byContradiction
          intro hne
          have hsome := idom?_isSome (htopo := htopo) hne
          rw [h] at hsome
          simp at hsome
        subst hroot
        simp only [dominates_root_iff]
        exact ⟨fun hf => absurd hf (by simp), fun hu => absurd hu huv⟩
      | some m =>
        have hidom := isIdom_of_idom? (htopo := htopo) h
        have hlt : rank m < n := by
          rw [← hv]; exact rank_lt_of_dominates htopo hidom.1.1 hidom.1.2
        rw [ih (rank m) hlt m rfl u]
        exact ⟨fun hum => hum.trans hidom.1.1, fun huv' => hidom.2 u ⟨huv', huv⟩⟩

end DepGraph

end DominatorTree
