module

public import Matroid.Graph.TopologicalMinor
public import Matroid.Graph.Walk.Cycle

@[expose] public section

variable {α β : Type*}

open Set WList Function
open scoped Sym2

namespace Graph

/-! ### One-off topological-minor constructors -/

private lemma nat_cases3 {i : ℕ} (hi : i < 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  omega

private lemma nat_cases5 {i : ℕ} (hi : i < 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  omega

/-- The four alternating arcs of a cycle, together with two adjacent outside vertices, give a
topological `K₃,₃`.

The route table and the finite verification for `CompleteBipartiteGraph 3 3` are deliberately hidden
in this theorem. -/
theorem isTopologicalMinor_completeBipartiteGraph_of_alternating_cycle
    {G : Graph α β} {W p₀₀ p₁₀ p₁₁ p₀₁ : WList α β} {u v : α} [Inhabited α]
    (hW : G.IsCyclicWalk W) (hdec : W.DecomposeTo [p₀₀, p₁₀, p₁₁, p₀₁])
    (h₀₀ : p₀₀.Nonempty) (h₁₀ : p₁₀.Nonempty) (h₁₁ : p₁₁.Nonempty)
    (h₀₁ : p₀₁.Nonempty) (huW : u ∉ V(W)) (hvW : v ∉ V(W)) (huv : u ≠ v)
    (hu₀ : G.Adj u p₀₀.first) (hu₁ : G.Adj u p₁₀.last)
    (hv₀ : G.Adj v p₀₀.last) (hv₁ : G.Adj v p₁₁.last) (huv_adj : G.Adj u v) :
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G := by
  have hne : ∀ P ∈ [p₀₀, p₁₀, p₁₁, p₀₁], P.Nonempty := by simp [h₀₀, h₁₀, h₁₁, h₀₁]
  have hp₀₀ : G.IsPath p₀₀ := hW.isPath_of_mem_decomposeTo hdec hne (by simp) (by simp)
  have hp₁₀ : G.IsPath p₁₀ := hW.isPath_of_mem_decomposeTo hdec hne (by simp) (by simp)
  have hp₁₁ : G.IsPath p₁₁ := hW.isPath_of_mem_decomposeTo hdec hne (by simp) (by simp)
  have hp₀₁ : G.IsPath p₀₁ := hW.isPath_of_mem_decomposeTo hdec hne (by simp) (by simp)
  have hjunctions : (([p₀₀, p₁₀, p₁₁, p₀₁].map WList.first)).Nodup :=
    hW.map_first_nodup_of_decomposeTo hdec hne
  have hpieces_internal : [p₀₀, p₁₀, p₁₁, p₀₁].Pairwise
      fun P Q ↦ Disjoint P.internalVertexSet Q.internalVertexSet :=
    hW.pairwise_disjoint_internalVertexSet_of_decomposeTo hdec hne
  have hpieces_junctions : ∀ P ∈ [p₀₀, p₁₀, p₁₁, p₀₁], Disjoint P.internalVertexSet
      {x | x ∈ [p₀₀, p₁₀, p₁₁, p₀₁].map WList.first} :=
  fun P ↦ hW.internalVertexSet_disjoint_map_first_of_decomposeTo hdec hne
  let L := [u, p₀₀.last, p₁₁.last, v, p₀₀.first, p₁₀.last]
  let sideIndex : V(CompleteBipartiteGraph 3 3) ↪ Fin 3 ⊕ Fin 3 :=
    { toFun := fun
        | ⟨Sum.inl i, hi⟩ =>
          Sum.inl ⟨i, by simpa [CompleteBipartiteGraph] using hi⟩
        | ⟨Sum.inr j, hj⟩ =>
          Sum.inr ⟨j, by simpa [CompleteBipartiteGraph] using hj⟩
      inj' := by
        rintro ⟨i | i, hi⟩ ⟨j | j, hj⟩ h
        · simp only [Sum.inl.injEq] at h
          apply Subtype.ext
          exact congrArg Sum.inl (congrArg Fin.val h)
        · simp at h
        · simp at h
        · simp only [Sum.inr.injEq] at h
          apply Subtype.ext
          exact congrArg Sum.inr (congrArg Fin.val h) }
  let idx : V(CompleteBipartiteGraph 3 3) ↪ Fin 6 :=
    sideIndex.trans finSumFinEquiv.toEmbedding
  have idx_inl (i : ℕ) (hi : Sum.inl i ∈ V(CompleteBipartiteGraph 3 3)) :
      idx ⟨Sum.inl i, hi⟩ = Fin.castAdd 3 ⟨i, by simpa [CompleteBipartiteGraph] using hi⟩ :=
    finSumFinEquiv_apply_left _
  have idx_inr (j : ℕ) (hj : Sum.inr j ∈ V(CompleteBipartiteGraph 3 3)) :
      idx ⟨Sum.inr j, hj⟩ = Fin.natAdd 3 ⟨j, by simpa [CompleteBipartiteGraph] using hj⟩ :=
    finSumFinEquiv_apply_right _
  let branch : V(CompleteBipartiteGraph 3 3) → α := L.get ∘ idx
  let adjWalk {x y : α} (h : G.Adj x y) : WList α β := cons x h.choose (nil y)
  let route : E(CompleteBipartiteGraph 3 3) → WList α β
    | ⟨⟨i, j⟩, hi, hj⟩ => (![![adjWalk huv_adj, adjWalk hu₀, adjWalk hu₁], ![adjWalk hv₀, p₀₀, p₁₀],
        ![adjWalk hv₁, p₀₁, p₁₁]] : Fin 3 → Fin 3 → WList α β) ⟨i, hi⟩ ⟨j, hj⟩
  have branch_mem : ∀ x, branch x ∈ V(G) := by
    rintro ⟨x | x, hx⟩ <;>
      obtain rfl | rfl | rfl := nat_cases3 (by simpa [CompleteBipartiteGraph] using hx)
    · simpa [branch, L, idx_inl] using hu₀.left_mem
    · simpa [branch, L, idx_inl] using hv₀.right_mem
    · simpa [branch, L, idx_inl] using hv₁.right_mem
    · simpa [branch, L, idx_inr] using hv₀.left_mem
    · simpa [branch, L, idx_inr] using hu₀.right_mem
    · simpa [branch, L, idx_inr] using hu₁.right_mem
  have hchain : p₀₀.last = p₁₀.first ∧ p₁₀.last = p₁₁.first ∧ p₁₁.last = p₀₁.first := by
    simpa [List.isChain_cons] using hdec.chain_eq
  have hmemW {x} (hx : x ∈ [p₀₀.first, p₀₀.last, p₁₀.last, p₁₁.last]) : x ∈ V(W) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl | rfl | rfl := hx
    · exact (hdec.isSublist_of_mem (by simp : p₀₀ ∈ _)).mem first_mem
    · exact (hdec.isSublist_of_mem (by simp : p₀₀ ∈ _)).mem last_mem
    · exact (hdec.isSublist_of_mem (by simp : p₁₀ ∈ _)).mem last_mem
    · exact (hdec.isSublist_of_mem (by simp : p₁₁ ∈ _)).mem last_mem
  have hu_ne (x) (hx : x ∈ [p₀₀.first, p₀₀.last, p₁₀.last, p₁₁.last]) : u ≠ x :=
    fun h ↦ huW (h ▸ hmemW hx)
  have hv_ne (x) (hx : x ∈ [p₀₀.first, p₀₀.last, p₁₀.last, p₁₁.last]) : v ≠ x :=
    fun h ↦ hvW (h ▸ hmemW hx)
  have hnodup : L.Nodup := by
    have hjunc : List.Nodup [p₀₀.first, p₀₀.last, p₁₀.last, p₁₁.last] := by
      convert hjunctions
      simp [hchain.1.symm, hchain.2.1.symm, hchain.2.2.symm]
    simp only [L, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    grind
  have branch_injective : Injective branch := by
    simpa [branch] using hnodup.injective_get.comp idx.injective
  have hadjWalk_isPath {x y : α} (h : G.Adj x y) (hne : x ≠ y) : G.IsPath (adjWalk h) :=
    IsLink.walk_isPath h.choose_spec hne
  have route_isPath : ∀ e, G.IsPath (route e) := by
    rintro ⟨⟨i, j⟩, hi, hj⟩
    obtain rfl | rfl | rfl := nat_cases3 hi <;>
      obtain rfl | rfl | rfl := nat_cases3 hj <;>
      first
      | assumption
      | exact hadjWalk_isPath (by assumption) (by grind)
  have hclose : p₀₁.last = p₀₀.first :=
    (show p₀₁.last = W.last by simpa using hdec.getLast_isSuffix.last_eq).trans
      (hW.isClosed.symm.trans <| by simpa using hdec.head_first_eq_first.symm)
  have route_ends : ∀ e, Sym2.map branch ((CompleteBipartiteGraph 3 3).ends e) =
      s((route e).first, (route e).last) := by
    rintro ⟨⟨i, j⟩, hi, hj⟩
    have hlink : (CompleteBipartiteGraph 3 3).IsLink (i, j) (Sum.inl i) (Sum.inr j) :=
      ⟨hi, hj, Or.inl ⟨rfl, rfl⟩⟩
    rw [hlink.ends_eq, Sym2.map_mk]
    obtain rfl | rfl | rfl := nat_cases3 hi
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · have hr : route ⟨⟨0, 0⟩, hi, hj⟩ = adjWalk huv_adj := rfl
        simp [hr, branch, L, idx_inl, idx_inr, adjWalk]
      · have hr : route ⟨⟨0, 1⟩, hi, hj⟩ = adjWalk hu₀ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, adjWalk]
      · have hr : route ⟨⟨0, 2⟩, hi, hj⟩ = adjWalk hu₁ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, adjWalk]
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · have hr : route ⟨⟨1, 0⟩, hi, hj⟩ = adjWalk hv₀ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, adjWalk, Sym2.eq]
      · have hr : route ⟨⟨1, 1⟩, hi, hj⟩ = p₀₀ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, Sym2.eq]
      · have hr : route ⟨⟨1, 2⟩, hi, hj⟩ = p₁₀ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, hchain.1]
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · have hr : route ⟨⟨2, 0⟩, hi, hj⟩ = adjWalk hv₁ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, adjWalk, Sym2.eq]
      · have hr : route ⟨⟨2, 1⟩, hi, hj⟩ = p₀₁ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, hchain.2.2, hclose]
      · have hr : route ⟨⟨2, 2⟩, hi, hj⟩ = p₁₁ := rfl
        simp [hr, branch, L, idx_inl, idx_inr, hchain.2.1, Sym2.eq]
  have hadj_internal {x y : α} (h : G.Adj x y) : (adjWalk h).internalVertexSet = ∅ := by
    simp [adjWalk, internalVertexSet]
  have hJ : {p₀₀.first, p₀₀.last, p₁₀.last, p₁₁.last} =
      {x | x ∈ [p₀₀, p₁₀, p₁₁, p₀₁].map WList.first} := by
    ext x
    simp [hchain.1.symm, hchain.2.1.symm, hchain.2.2.symm]
  have hrange : range branch ⊆ insert u (insert v {p₀₀.first, p₀₀.last, p₁₀.last, p₁₁.last}) := by
    rintro y ⟨⟨x | x, hx⟩, rfl⟩
    · obtain rfl | rfl | rfl :=
        nat_cases3 (by simpa [CompleteBipartiteGraph] using hx)
      · simp [branch, L, idx_inl]
      · simp [branch, L, idx_inl]
      · simp [branch, L, idx_inl]
    · obtain rfl | rfl | rfl :=
        nat_cases3 (by simpa [CompleteBipartiteGraph] using hx)
      · simp [branch, L, idx_inr]
      · simp [branch, L, idx_inr]
      · simp [branch, L, idx_inr]
  have hpiece {P} (hP : P ∈ [p₀₀, p₁₀, p₁₁, p₀₁]) :
      Disjoint P.internalVertexSet (range branch) := by
    refine Disjoint.mono_right hrange ?_
    simp only [disjoint_insert_right, hJ]
    exact ⟨fun hx ↦ huW ((hdec.isSublist_of_mem hP).internalVertexSet_subset hx),
      fun hx ↦ hvW ((hdec.isSublist_of_mem hP).internalVertexSet_subset hx),
      hpieces_junctions P hP⟩
  have route_internal_disjoint_branch : ∀ e,
      Disjoint (route e).internalVertexSet (range branch) := by
    rintro ⟨⟨i, j⟩, hi, hj⟩
    obtain rfl | rfl | rfl := nat_cases3 hi
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · simp [show route ⟨⟨0, 0⟩, hi, hj⟩ = adjWalk huv_adj from rfl, hadj_internal]
      · simp [show route ⟨⟨0, 1⟩, hi, hj⟩ = adjWalk hu₀ from rfl, hadj_internal]
      · simp [show route ⟨⟨0, 2⟩, hi, hj⟩ = adjWalk hu₁ from rfl, hadj_internal]
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · simp [show route ⟨⟨1, 0⟩, hi, hj⟩ = adjWalk hv₀ from rfl, hadj_internal]
      · simpa [show route ⟨⟨1, 1⟩, hi, hj⟩ = p₀₀ from rfl] using hpiece (by simp)
      · simpa [show route ⟨⟨1, 2⟩, hi, hj⟩ = p₁₀ from rfl] using hpiece (by simp)
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · simp [show route ⟨⟨2, 0⟩, hi, hj⟩ = adjWalk hv₁ from rfl, hadj_internal]
      · simpa [show route ⟨⟨2, 1⟩, hi, hj⟩ = p₀₁ from rfl] using hpiece (by simp)
      · simpa [show route ⟨⟨2, 2⟩, hi, hj⟩ = p₁₁ from rfl] using hpiece (by simp)
  let routeInterior : ℕ × ℕ → Set α
    | (1, 1) => p₀₀.internalVertexSet
    | (1, 2) => p₁₀.internalVertexSet
    | (2, 1) => p₀₁.internalVertexSet
    | (2, 2) => p₁₁.internalVertexSet
    | _ => ∅
  have route_internal_eq (e : E(CompleteBipartiteGraph 3 3)) :
      (route e).internalVertexSet = routeInterior e.1 := by
    rcases e with ⟨⟨i, j⟩, hi, hj⟩
    obtain rfl | rfl | rfl := nat_cases3 hi
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · simp [show route ⟨⟨0, 0⟩, hi, hj⟩ = adjWalk huv_adj from rfl, routeInterior,
          hadj_internal]
      · simp [show route ⟨⟨0, 1⟩, hi, hj⟩ = adjWalk hu₀ from rfl, routeInterior,
          hadj_internal]
      · simp [show route ⟨⟨0, 2⟩, hi, hj⟩ = adjWalk hu₁ from rfl, routeInterior,
          hadj_internal]
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · simp [show route ⟨⟨1, 0⟩, hi, hj⟩ = adjWalk hv₀ from rfl, routeInterior,
          hadj_internal]
      · simp [show route ⟨⟨1, 1⟩, hi, hj⟩ = p₀₀ from rfl, routeInterior]
      · simp [show route ⟨⟨1, 2⟩, hi, hj⟩ = p₁₀ from rfl, routeInterior]
    · obtain rfl | rfl | rfl := nat_cases3 hj
      · simp [show route ⟨⟨2, 0⟩, hi, hj⟩ = adjWalk hv₁ from rfl, routeInterior,
          hadj_internal]
      · simp [show route ⟨⟨2, 1⟩, hi, hj⟩ = p₀₁ from rfl, routeInterior]
      · simp [show route ⟨⟨2, 2⟩, hi, hj⟩ = p₁₁ from rfl, routeInterior]
  have route_internal_cases (e : E(CompleteBipartiteGraph 3 3)) :
      (route e).internalVertexSet = ∅ ∨
        ((route e).internalVertexSet = p₀₀.internalVertexSet ∧ e.1 = (1, 1)) ∨
        ((route e).internalVertexSet = p₁₀.internalVertexSet ∧ e.1 = (1, 2)) ∨
        ((route e).internalVertexSet = p₀₁.internalVertexSet ∧ e.1 = (2, 1)) ∨
        ((route e).internalVertexSet = p₁₁.internalVertexSet ∧ e.1 = (2, 2)) := by
    rw [route_internal_eq]
    rcases e with ⟨⟨i, j⟩, hi, hj⟩
    obtain rfl | rfl | rfl := nat_cases3 hi <;>
      obtain rfl | rfl | rfl := nat_cases3 hj <;>
      simp [routeInterior]
  have route_internal_disjoint : ∀ e f, e ≠ f →
      Disjoint (route e).internalVertexSet (route f).internalVertexSet := by
    obtain ⟨⟨h₀₀₁₀, h₀₀₁₁, h₀₀₀₁⟩, ⟨h₁₀₁₁, h₁₀₀₁⟩, h₁₁₀₁⟩ :
        (Disjoint p₀₀.internalVertexSet p₁₀.internalVertexSet ∧
        Disjoint p₀₀.internalVertexSet p₁₁.internalVertexSet ∧
        Disjoint p₀₀.internalVertexSet p₀₁.internalVertexSet) ∧
      (Disjoint p₁₀.internalVertexSet p₁₁.internalVertexSet ∧
        Disjoint p₁₀.internalVertexSet p₀₁.internalVertexSet) ∧
      Disjoint p₁₁.internalVertexSet p₀₁.internalVertexSet := by
      simpa using hpieces_internal
    rintro e f hef
    obtain he | ⟨he, he2⟩ | ⟨he, he2⟩ | ⟨he, he2⟩ | ⟨he, he2⟩ :=
      route_internal_cases e
    · simp [he]
    · obtain hf | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ :=
        route_internal_cases f
      · simp [hf]
      · exact (hef (Subtype.ext (he2.trans hf2.symm))).elim
      · simpa [he, hf] using h₀₀₁₀
      · simpa [he, hf] using h₀₀₀₁
      · simpa [he, hf] using h₀₀₁₁
    · obtain hf | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ :=
        route_internal_cases f
      · simp [hf]
      · simpa [he, hf] using h₀₀₁₀.symm
      · exact (hef (Subtype.ext (he2.trans hf2.symm))).elim
      · simpa [he, hf] using h₁₀₀₁
      · simpa [he, hf] using h₁₀₁₁
    · obtain hf | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ :=
        route_internal_cases f
      · simp [hf]
      · simpa [he, hf] using h₀₀₀₁.symm
      · simpa [he, hf] using h₁₀₀₁.symm
      · exact (hef (Subtype.ext (he2.trans hf2.symm))).elim
      · simpa [he, hf] using h₁₁₀₁.symm
    · obtain hf | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ :=
        route_internal_cases f
      · simp [hf]
      · simpa [he, hf] using h₀₀₁₁.symm
      · simpa [he, hf] using h₁₀₁₁.symm
      · simpa [he, hf] using h₁₁₀₁
      · exact (hef (Subtype.ext (he2.trans hf2.symm))).elim
  exact ⟨TopologicalModel.ofPathRoutes (H := CompleteBipartiteGraph 3 3) (G := G) branch
      branch_mem branch_injective route route_isPath route_ends route_internal_disjoint_branch
      route_internal_disjoint⟩

/-- Three consecutive arcs of a cycle through three common neighbors of two adjacent outside
vertices give a topological `K₅`.

The route table and the finite verification for `CompleteGraph 5` are deliberately hidden in this
theorem. -/
theorem isTopologicalMinor_completeGraph_of_three_common_neighbors
    {G : Graph α β} {W pxy pyz pzx : WList α β} {u v : α} [Inhabited α]
    (hW : G.IsCyclicWalk W) (hdec : W.DecomposeTo [pxy, pyz, pzx])
    (hxy : pxy.Nonempty) (hyz : pyz.Nonempty) (hzx : pzx.Nonempty)
    (huW : u ∉ V(W)) (hvW : v ∉ V(W)) (huv : u ≠ v)
    (hux : G.Adj u pxy.first) (huy : G.Adj u pxy.last) (huz : G.Adj u pyz.last)
    (hvx : G.Adj v pxy.first) (hvy : G.Adj v pxy.last) (hvz : G.Adj v pyz.last)
    (huv_adj : G.Adj u v) : (CompleteGraph 5).IsTopologicalMinor G := by
  have hne : ∀ P ∈ [pxy, pyz, pzx], P.Nonempty := by simp [hxy, hyz, hzx]
  have hpxy : G.IsPath pxy :=
    hW.isPath_of_mem_decomposeTo hdec hne (by simp) (by simp)
  have hpyz : G.IsPath pyz :=
    hW.isPath_of_mem_decomposeTo hdec hne (by simp) (by simp)
  have hpzx : G.IsPath pzx :=
    hW.isPath_of_mem_decomposeTo hdec hne (by simp) (by simp)
  have hjunctions : (([pxy, pyz, pzx].map WList.first)).Nodup :=
    hW.map_first_nodup_of_decomposeTo hdec hne
  have hpieces_internal :
      [pxy, pyz, pzx].Pairwise
        (fun P Q ↦ Disjoint P.internalVertexSet Q.internalVertexSet) :=
    hW.pairwise_disjoint_internalVertexSet_of_decomposeTo hdec hne
  have hpieces_junctions : ∀ P ∈ [pxy, pyz, pzx],
      Disjoint P.internalVertexSet {x | x ∈ [pxy, pyz, pzx].map WList.first} := by
    intro P hP
    exact hW.internalVertexSet_disjoint_map_first_of_decomposeTo hdec hne hP
  -- The branch vertices are `[u, v, pxy.first, pxy.last, pyz.last]`. The ten routes are the three
  -- cycle pieces, the six selected spokes from `u` and `v`, and the selected `u`-`v` edge.
  let L := [u, v, pxy.first, pxy.last, pyz.last]
  let branch : V(CompleteGraph 5) → α := fun ⟨i, hi⟩ ↦
    L.get ⟨i, by simpa [CompleteGraph, L] using hi⟩
  let adjWalk {x y : α} (h : G.Adj x y) : WList α β := cons x h.choose (nil y)
  let routeOf (a b : ℕ) : WList α β :=
    match min a b, max a b with
    | 0, 1 => adjWalk huv_adj
    | 0, 2 => adjWalk hux
    | 0, 3 => adjWalk huy
    | 0, 4 => adjWalk huz
    | 1, 2 => adjWalk hvx
    | 1, 3 => adjWalk hvy
    | 1, 4 => adjWalk hvz
    | 2, 3 => pxy
    | 2, 4 => pzx
    | 3, 4 => pyz
    | _, _ => nil u
  let route : E(CompleteGraph 5) → WList α β := fun e ↦
    Sym2.lift ⟨routeOf, fun a b ↦ by simp [routeOf, min_comm a b, max_comm a b]⟩ e.1
  have branch_mem : ∀ x, branch x ∈ V(G) := by
    rintro ⟨x, hx⟩
    obtain rfl | rfl | rfl | rfl | rfl :=
      nat_cases5 (by simpa [CompleteGraph] using hx)
    · simpa [branch, L] using hux.left_mem
    · simpa [branch, L] using hvx.left_mem
    · simpa [branch, L] using hux.right_mem
    · simpa [branch, L] using huy.right_mem
    · simpa [branch, L] using huz.right_mem
  have hchain : pxy.last = pyz.first ∧ pyz.last = pzx.first := by
    simpa [List.isChain_cons] using hdec.chain_eq
  have hmemW {x} (hx : x ∈ [pxy.first, pxy.last, pyz.last]) : x ∈ V(W) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl | rfl := hx
    · exact (hdec.isSublist_of_mem (by simp : pxy ∈ _)).mem first_mem
    · exact (hdec.isSublist_of_mem (by simp : pxy ∈ _)).mem last_mem
    · exact (hdec.isSublist_of_mem (by simp : pyz ∈ _)).mem last_mem
  have hu_ne (x) (hx : x ∈ [pxy.first, pxy.last, pyz.last]) : u ≠ x :=
    fun h ↦ huW (h ▸ hmemW hx)
  have hv_ne (x) (hx : x ∈ [pxy.first, pxy.last, pyz.last]) : v ≠ x :=
    fun h ↦ hvW (h ▸ hmemW hx)
  have hnodup : L.Nodup := by
    have hjunc : List.Nodup [pxy.first, pxy.last, pyz.last] := by
      convert hjunctions
      simp [hchain.1.symm, hchain.2.symm]
    simp only [L, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    grind
  have branch_injective : Injective branch := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    refine Subtype.ext <| congrArg Fin.val <|
      hnodup.injective_get (a₁ := ⟨i, by simpa [CompleteGraph, L] using hi⟩)
        (a₂ := ⟨j, by simpa [CompleteGraph, L] using hj⟩) ?_
    simpa [branch, L] using h

  have hadjWalk_isPath {x y : α} (h : G.Adj x y) (hne : x ≠ y) : G.IsPath (adjWalk h) :=
    IsLink.walk_isPath h.choose_spec hne
  have route_isPath : ∀ e, G.IsPath (route e) := by
    rintro ⟨e, -⟩
    induction e with
    | h i j =>
      simp only [route, Sym2.lift_mk, routeOf]
      split <;>
        first
        | assumption
        | exact hadjWalk_isPath (by assumption) (by grind)
        | exact nil_isPath hux.left_mem
  have hclose : pzx.last = pxy.first :=
    (show pzx.last = W.last by simpa using hdec.getLast_isSuffix.last_eq).trans
      (hW.isClosed.symm.trans <| by simpa using hdec.head_first_eq_first.symm)
  have hsym2_minmax (a b : ℕ) : s(a, b) = s(min a b, max a b) := by
    rcases le_total a b with hab | hba
    · simp [min_eq_left hab, max_eq_right hab]
    · simp [min_eq_right hba, max_eq_left hba, Sym2.eq]
  have routeOf_ends_of_lt (i j : ℕ) (hij : i < j) (hj : j < 5) :
      s(branch ⟨i, hij.trans hj⟩, branch ⟨j, hj⟩) =
        s((routeOf i j).first, (routeOf i j).last) := by
    obtain rfl | rfl | rfl | rfl | rfl := nat_cases5 (hij.trans hj) <;>
      obtain rfl | rfl | rfl | rfl | rfl := nat_cases5 hj <;>
      first
      | omega
      | simp [routeOf, branch, L, adjWalk, hchain.1, hchain.2, hclose, Sym2.eq]
  have routeOf_ends (i j : ℕ) (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
      s(branch ⟨i, hi⟩, branch ⟨j, hj⟩) =
        s((routeOf i j).first, (routeOf i j).last) := by
    obtain hij | hji := lt_or_gt_of_ne hij
    · simpa using routeOf_ends_of_lt i j hij hj
    · rw [show routeOf i j = routeOf j i by
        simp [routeOf, min_comm i j, max_comm i j]]
      calc
        s(branch ⟨i, hi⟩, branch ⟨j, hj⟩) =
            s(branch ⟨j, hj⟩, branch ⟨i, hi⟩) := Sym2.eq_swap
        _ = _ := by simpa using routeOf_ends_of_lt j i hji hi
  have route_ends : ∀ e, Sym2.map branch ((CompleteGraph 5).ends e) =
      s((route e).first, (route e).last) := by
    rintro ⟨e, he⟩
    induction e with
    | h i j =>
      simp only [edgeSet_CompleteGraph, mem_ofPred_eq, Sym2.ball, Sym2.mk_isDiag_iff] at he
      obtain ⟨⟨hi, hj⟩, hneij⟩ := he
      have hlink : (CompleteGraph 5).IsLink s(i, j) i j := ⟨hi, hj, hneij, rfl⟩
      change Sym2.map branch ((CompleteGraph 5).ends ⟨_, hlink.edge_mem⟩) = _
      rw [hlink.ends_eq, Sym2.map_mk]
      simpa [route, Sym2.lift_mk] using routeOf_ends i j hi hj hneij

  have hadj_internal {x y : α} (h : G.Adj x y) : (adjWalk h).internalVertexSet = ∅ := by
    simp [adjWalk, internalVertexSet]
  have hJ : {pxy.first, pxy.last, pyz.last} =
      {x | x ∈ [pxy, pyz, pzx].map WList.first} := by
    ext x
    simp [hchain.1.symm, hchain.2.symm]
  have hrange : range branch ⊆ insert u (insert v {pxy.first, pxy.last, pyz.last}) := by
    rintro y ⟨⟨x, hx⟩, rfl⟩
    obtain rfl | rfl | rfl | rfl | rfl :=
      nat_cases5 (by simpa [CompleteGraph] using hx)
    all_goals simp [branch, L]
  have hpiece {P} (hP : P ∈ [pxy, pyz, pzx]) :
      Disjoint P.internalVertexSet (range branch) := by
    refine Disjoint.mono_right hrange ?_
    simp only [disjoint_insert_right, hJ]
    exact ⟨fun hx ↦ huW ((hdec.isSublist_of_mem hP).internalVertexSet_subset hx),
      fun hx ↦ hvW ((hdec.isSublist_of_mem hP).internalVertexSet_subset hx),
      hpieces_junctions P hP⟩
  have route_internal_cases (e : E(CompleteGraph 5)) :
      (route e).internalVertexSet = ∅ ∨
        ((route e).internalVertexSet = pxy.internalVertexSet ∧ e.1 = s(2, 3)) ∨
        ((route e).internalVertexSet = pzx.internalVertexSet ∧ e.1 = s(2, 4)) ∨
        ((route e).internalVertexSet = pyz.internalVertexSet ∧ e.1 = s(3, 4)) := by
    dsimp only [route]
    refine Sym2.inductionOn e.1 fun i j ↦ ?_
    simp only [Sym2.lift_mk, routeOf]
    split
    · simp [adjWalk, internalVertexSet]
    · simp [adjWalk, internalVertexSet]
    · simp [adjWalk, internalVertexSet]
    · simp [adjWalk, internalVertexSet]
    · simp [adjWalk, internalVertexSet]
    · simp [adjWalk, internalVertexSet]
    · simp [adjWalk, internalVertexSet]
    · refine Or.inr (Or.inl ⟨rfl, (hsym2_minmax i j).trans ?_⟩)
      simp [*]
    · refine Or.inr (Or.inr (Or.inl ⟨rfl, (hsym2_minmax i j).trans ?_⟩))
      simp [*]
    · refine Or.inr (Or.inr (Or.inr ⟨rfl, (hsym2_minmax i j).trans ?_⟩))
      simp [*]
    · simp [internalVertexSet]
  have route_internal_disjoint_branch : ∀ e,
      Disjoint (route e).internalVertexSet (range branch) := by
    rintro e
    obtain h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ := route_internal_cases e
    · simp [h]
    · simpa [h] using hpiece (by simp : pxy ∈ _)
    · simpa [h] using hpiece (by simp : pzx ∈ _)
    · simpa [h] using hpiece (by simp : pyz ∈ _)
  have route_internal_disjoint : ∀ e f, e ≠ f →
      Disjoint (route e).internalVertexSet (route f).internalVertexSet := by
    obtain ⟨⟨hxy_yz, hxy_zx⟩, hyz_zx⟩ :
        (Disjoint pxy.internalVertexSet pyz.internalVertexSet ∧
          Disjoint pxy.internalVertexSet pzx.internalVertexSet) ∧
        Disjoint pyz.internalVertexSet pzx.internalVertexSet := by
      simpa using hpieces_internal
    rintro e f hef
    obtain he | ⟨he, he2⟩ | ⟨he, he2⟩ | ⟨he, he2⟩ := route_internal_cases e
    · simp [he]
    · obtain hf | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ := route_internal_cases f
      · simp [hf]
      · exact (hef (Subtype.ext (he2.trans hf2.symm))).elim
      · simpa [he, hf] using hxy_zx
      · simpa [he, hf] using hxy_yz
    · obtain hf | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ := route_internal_cases f
      · simp [hf]
      · simpa [he, hf] using hxy_zx.symm
      · exact (hef (Subtype.ext (he2.trans hf2.symm))).elim
      · simpa [he, hf] using hyz_zx.symm
    · obtain hf | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ | ⟨hf, hf2⟩ := route_internal_cases f
      · simp [hf]
      · simpa [he, hf] using hxy_yz.symm
      · simpa [he, hf] using hyz_zx
      · exact (hef (Subtype.ext (he2.trans hf2.symm))).elim
  have hmodel : (CompleteGraph 5).TopologicalModel G :=
    TopologicalModel.ofPathRoutes (H := CompleteGraph 5) (G := G) branch branch_mem
      branch_injective route route_isPath route_ends route_internal_disjoint_branch
      route_internal_disjoint
  exact ⟨hmodel⟩

end Graph
