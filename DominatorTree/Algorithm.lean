import DominatorTree.Reducible

/-!
# Computing the dominator tree

For a graph carrying a topological rank — a DAG, or the back-edge-free part of a
reducible graph — every predecessor of `v` is ranked below `v`, so the tree can
be built in one pass with no fixpoint iteration.

`anc v` is the path from `v` up to the root. It is built by intersecting the
paths of `v`'s predecessors, which are already known: nothing here ever forms a
dominator set over all vertices, and each list is only as long as the tree is
deep.

The tree itself is `idom?`. Dominance is not stored: `domWalk` recomputes it by
climbing from `v` and looking for `u`.
-/

namespace DominatorTree

namespace DepGraph

variable {V : Type} {verts : List V}

/-- A rank that strictly increases along every edge: a topological numbering. -/
def TopoRank (g : DepGraph verts) (rank : Vertex verts → Nat) : Prop :=
  ∀ v u, u ∈ g.out v → rank v < rank u

/-- Checking a topological rank only needs the vertices actually listed, so this
form is decidable. -/
theorem topoRank_of_forall_mem {g : DepGraph verts} {rank : Vertex verts → Nat}
    (h : ∀ v ∈ verts.attach, ∀ u ∈ g.out v, rank v < rank u) : g.TopoRank rank :=
  fun v u hu => h v (List.mem_attach _ _) u hu

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

/-- The largest-ranked of `a` and the elements of `l`. -/
def maxByRank (rank : Vertex verts → Nat) (a : Vertex verts) :
    List (Vertex verts) → Vertex verts
  | [] => a
  | b :: bs => if rank a ≤ rank b then maxByRank rank b bs else maxByRank rank a bs

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

variable [DecidableEq V]

/-- The predecessors of `v`. -/
def preds (g : DepGraph verts) (v : Vertex verts) : List (Vertex verts) :=
  verts.attach.filter (fun u => decide (v ∈ g.out u))

@[simp] theorem mem_preds {g : DepGraph verts} {u v : Vertex verts} :
    u ∈ g.preds v ↔ g.Edge u v := by
  simp [preds, List.mem_filter, List.mem_attach, Edge]

/-- On a connected graph every non-root vertex has a predecessor. -/
theorem preds_ne_nil {g : ConnectedGraph verts} {v : Vertex verts} (hv : v ≠ g.root) :
    g.preds v ≠ [] := by
  obtain ⟨P⟩ := g.reach v
  have hpos : 0 < P.length := by
    rcases Nat.eq_zero_or_pos P.length with h0 | h
    · exact absurd (Path.eq_of_length_zero P h0).symm hv
    · exact h
  obtain ⟨x, -, he, -⟩ := P.exists_last_edge_path hpos
  intro hnil
  have : x ∈ g.preds v := mem_preds.mpr he
  rw [hnil] at this
  simp at this

omit [DecidableEq V] in
/-- Checking a property of every element of a list, with membership evidence
attached so recursive calls can justify termination. -/
theorem attach_all_iff {ps : List (Vertex verts)} {P : Vertex verts → Prop} [DecidablePred P] :
    (ps.attach.all (fun q => decide (P q.val)) = true) ↔ ∀ q ∈ ps, P q := by
  constructor
  · intro h q hq
    have := List.all_eq_true.mp h ⟨q, hq⟩ (List.mem_attach _ _)
    simpa using this
  · intro h
    refine List.all_eq_true.mpr fun x _ => ?_
    simpa using h x.val x.property

/-- The path from `v` up to the root of the dominator tree.

Built by taking the path of one predecessor and keeping only the vertices lying
on every other predecessor's path — the tree paths meet exactly at the
dominators shared by all predecessors. -/
def anc (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : List (Vertex verts) :=
  if v = g.root then [v]
  else
    match hp : g.preds v with
    | [] => []
    | p :: ps =>
        v :: (anc g rank htopo p).filter
          (fun m => ps.attach.all (fun q => decide (m ∈ anc g rank htopo q.val)))
termination_by rank v
decreasing_by
  · exact htopo _ _ (mem_preds.mp (by rw [hp]; exact List.mem_cons_of_mem _ q.property))
  · exact htopo _ _ (mem_preds.mp (by rw [hp]; exact List.mem_cons_self))

/-- **Correctness**: the path from `v` holds exactly the dominators of `v`.

By strong induction on the rank. A vertex other than `v` lies on every
predecessor's path exactly when it dominates every predecessor, which by the
dataflow equation is what it means to dominate `v`. -/
theorem mem_anc {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} (v u : Vertex verts) :
    u ∈ anc g.toDepGraph rank htopo v ↔ g.Dominates u v := by
  suffices H : ∀ n (v : Vertex verts), rank v = n →
      ∀ u, u ∈ anc g.toDepGraph rank htopo v ↔ g.Dominates u v from H _ v rfl u
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv u
    rw [anc]
    by_cases hroot : v = g.root
    · subst hroot
      rw [if_pos rfl]
      simpa using dominates_root_iff.symm
    · rw [if_neg hroot, dominates_iff_preds hroot u]
      -- every non-root vertex of a connected graph has a predecessor
      cases hp : g.preds v with
      | nil => exact absurd hp (preds_ne_nil hroot)
      | cons p ps =>
        have hpv : g.Edge p v := mem_preds.mp (by rw [hp]; exact List.mem_cons_self ..)
        have hqv : ∀ q ∈ ps, g.Edge q v := fun q hq =>
          mem_preds.mp (by rw [hp]; exact List.mem_cons_of_mem _ hq)
        have hrk : ∀ q : Vertex verts, g.Edge q v → rank q < n := by
          intro q hq; rw [← hv]; exact htopo q v hq
        rw [List.mem_cons, List.mem_filter]
        constructor
        · rintro (rfl | ⟨hmp, hmall⟩)
          · exact Or.inl rfl
          · have hall' :=
              (attach_all_iff (P := fun x => u ∈ anc g.toDepGraph rank htopo x)).mp hmall
            refine Or.inr fun q hq => ?_
            rcases List.mem_cons.mp (show q ∈ p :: ps from hp ▸ mem_preds.mpr hq) with rfl | hq'
            · exact (ih (rank q) (hrk q hq) q rfl u).mp hmp
            · exact (ih (rank q) (hrk q hq) q rfl u).mp (hall' q hq')
        · rintro (rfl | hall)
          · exact Or.inl rfl
          · refine Or.inr ⟨(ih (rank p) (hrk p hpv) p rfl u).mpr (hall p hpv), ?_⟩
            refine (attach_all_iff (P := fun x => u ∈ anc g.toDepGraph rank htopo x)).mpr fun q hq => ?_
            exact (ih (rank q) (hrk q (hqv q hq)) q rfl u).mpr (hall q (hqv q hq))

/-- The strict dominators of `v`: its tree path minus itself. -/
def strictAnc (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : List (Vertex verts) :=
  (anc g rank htopo v).filter (fun u => decide (u ≠ v))

theorem mem_strictAnc {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v u : Vertex verts} :
    u ∈ strictAnc g.toDepGraph rank htopo v ↔ g.StrictlyDominates u v := by
  simp [strictAnc, List.mem_filter, mem_anc, StrictlyDominates]

/-- The immediate dominator of `v`: the deepest vertex on its tree path.

Correct because the dominators of a vertex are linearly ordered
(`ConnectedGraph.dominates_total`) and that order agrees with rank
(`rank_lt_of_dominates`), so the deepest strict dominator is the immediate
one. -/
def idom? (g : DepGraph verts) (rank : Vertex verts → Nat) (htopo : g.TopoRank rank)
    (v : Vertex verts) : Option (Vertex verts) :=
  match strictAnc g rank htopo v with
  | [] => none
  | a :: as => some (maxByRank rank a as)

/-- **Soundness**: what `idom?` returns is the immediate dominator. -/
theorem isIdom_of_idom? {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v u : Vertex verts}
    (h : idom? g.toDepGraph rank htopo v = some u) : g.IsIdom u v := by
  rw [idom?] at h
  cases hds : strictAnc g.toDepGraph rank htopo v with
  | nil => rw [hds] at h; simp at h
  | cons a as =>
    rw [hds] at h
    simp only [Option.some.injEq] at h
    subst h
    have hmem : maxByRank rank a as ∈ strictAnc g.toDepGraph rank htopo v := by
      rw [hds]; exact maxByRank_mem as a
    have hmax : ∀ x ∈ strictAnc g.toDepGraph rank htopo v,
        rank x ≤ rank (maxByRank rank a as) := by
      rw [hds]; exact fun x hx => le_maxByRank as a x hx
    have hu : g.StrictlyDominates (maxByRank rank a as) v := mem_strictAnc.mp hmem
    refine ⟨hu, fun w hw => ?_⟩
    rcases ConnectedGraph.dominates_total hu.1 hw.1 with huw | hwu
    · by_cases heq : maxByRank rank a as = w
      · subst heq; exact g.dominates_refl _
      · have hlt := rank_lt_of_dominates htopo huw heq
        have hle := hmax w (mem_strictAnc.mpr hw)
        omega
    · exact hwu

/-- **Totality**: on a connected graph every non-root vertex gets a parent. -/
theorem idom?_isSome {g : ConnectedGraph verts} {rank : Vertex verts → Nat}
    {htopo : g.toDepGraph.TopoRank rank} {v : Vertex verts} (hv : v ≠ g.root) :
    (idom? g.toDepGraph rank htopo v).isSome := by
  have hroot : g.root ∈ strictAnc g.toDepGraph rank htopo v :=
    mem_strictAnc.mpr (g.root_strictlyDominates (Ne.symm hv))
  rw [idom?]
  cases hds : strictAnc g.toDepGraph rank htopo v with
  | nil => rw [hds] at hroot; simp at hroot
  | cons a as => simp

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

/-- **Correctness**: climbing the tree decides dominance.

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
