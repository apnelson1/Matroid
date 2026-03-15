import Matroid.Axioms.Circuit
import Matroid.Minor.Contract
import Matroid.Graph.AcyclicSet
import Matroid.Graph.Minor.Conn
import Matroid.Graph.Connected.Minor
import Matroid.Connectivity.Skew
import Matroid.Connectivity.ConnSystem.Matroid
import Matroid.Graph.Matrix
import Matroid.Binary.Representation

open Set WList Matroid Function

attribute [grind →] IsCocircuit.subset_ground

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {B F F' R R': Set β} {C w P Q : WList α β}

/-- The cycle matroid of a graph `G`. Its circuits are the edge sets of cycles of `G`,
and its independent sets are the edge sets of forests. -/
@[simps! (attr := grind =) E]
def cycleMatroid (G : Graph α β) : Matroid β :=
  FiniteCircuitMatroid.matroid <| FiniteCircuitMatroid.mk
    (E := E(G))
    (IsCircuit := G.IsCycleSet)
    (by
      simp only [IsCycleSet, not_exists, not_and]
      exact fun C hC hCe ↦ by simpa [hCe] using hC.nonempty.edgeSet_nonempty )
    (by
      rintro _ ⟨C₁, hC₁, rfl⟩ _ ⟨C₂, hC₂, rfl⟩ hne (hss : E(C₁) ⊆ E(C₂))
      have h_eq := hC₂.toGraph_eq_of_le hC₁ <|
        hC₁.isWalk.le_of_edgeSet_subset hC₁.nonempty hC₂.isWalk hss
      exact hne <| by simpa using congrArg Graph.edgeSet h_eq )
    (by
      rintro _ _ e ⟨C₁, hC₁, rfl⟩ ⟨C₂, hC₂, rfl⟩ hne he₁ he₂
      obtain ⟨x, y, hxy₁⟩ := C₁.exists_isLink_of_mem_edge he₁
      have hxy₂ := (hC₁.isWalk.isLink_iff_isLink_of_mem he₁).1 hxy₁
      rw [← hC₂.isWalk.isLink_iff_isLink_of_mem he₂] at hxy₂
      obtain ⟨P₁, hP₁, hP₁C₁, hx₁, hy₁⟩ := hC₁.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy₁
      obtain ⟨P₂, hP₂, hP₂C₂, hx₂, hy₂⟩ := hC₂.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy₂
      by_cases h_eq : P₁ = P₂
      · apply_fun (fun P : WList α β ↦ insert e E(P)) at h_eq
        simp [← P₁.toGraph_edgeSet, ← P₂.toGraph_edgeSet, hP₁C₁, hP₂C₂, edgeDelete_edgeSet,
          WList.toGraph_edgeSet, Set.insert_eq_of_mem he₁, Set.insert_eq_of_mem he₂, hne] at h_eq
      obtain ⟨C, hC, hCE⟩ := twoPaths hP₁ hP₂ h_eq (by rw [hx₁, hx₂]) (by rw [hy₁, hy₂])
      have hss : E(C) ⊆ (E(C₁) ∪ E(C₂)) \ {e} := by
        apply_fun Graph.edgeSet at hP₁C₁ hP₂C₂
        simp only [WList.toGraph_edgeSet, edgeDelete_edgeSet] at hP₁C₁ hP₂C₂
        rwa [union_diff_distrib, ← hP₁C₁, ← hP₂C₂]
      refine ⟨E(C), ⟨C, hC, rfl⟩, notMem_subset hss (by simp), fun x hx ↦ ?_⟩
      simpa using (hss.trans diff_subset) hx )
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact C.edgeSet_finite )
    (by
      rintro _ ⟨C, hC, rfl⟩
      simpa using edgeSet_mono hC.isWalk.toGraph_le )

@[simp, grind =]
lemma cycleMatroid_isCircuit : G.cycleMatroid.IsCircuit = G.IsCycleSet := by
  simp [cycleMatroid]

@[simp, grind =]
lemma cycleMatroid_indep : G.cycleMatroid.Indep = G.IsAcyclicSet := by
  ext I
  simp only [cycleMatroid, FiniteCircuitMatroid.matroid_indep_iff, IsCycleSet, IsAcyclicSet]
  aesop

lemma cycleMatroid_isBase : G.cycleMatroid.IsBase = G.IsMaximalAcyclicSet := by
  ext B
  rw [isBase_iff_maximal_indep, cycleMatroid_indep]
  rfl

lemma isBase_iff_indep_spanning {M : Matroid α} {X : Set α} :
    M.IsBase X ↔ M.Indep X ∧ M.Spanning X :=
  ⟨fun h => ⟨h.indep, h.spanning⟩, fun ⟨hI, hC⟩ => hC.isBase_of_indep hI⟩

lemma exists_isMaximalAcyclicSet (G : Graph α β) : ∃ F, G.IsMaximalAcyclicSet F := by
  simpa [cycleMatroid_isBase] using (cycleMatroid G).exists_isBase

lemma cycleMatroid_coindep : G.cycleMatroid.Coindep F ↔
    F ⊆ E(G) ∧ (∀ x y, G.ConnBetween x y ↔ (G ＼ F).ConnBetween x y) := by
  wlog hFE : F ⊆ G.cycleMatroid.E
  · grind
  simp only [coindep_iff_exists hFE, isBase_iff_maximal_indep, cycleMatroid_indep, cycleMatroid_E,
    (show F ⊆ E(G) from hFE), true_and]
  refine ⟨fun ⟨B, hB, hBF⟩ x y ↦ ⟨fun hxy ↦ ?_, fun hxy ↦ hxy.mono edgeDelete_le⟩, fun h ↦ ?_⟩
  · rw [← IsMaximalAcyclicSet.connBetween_iff hB] at hxy
    rw [subset_diff] at hBF
    exact hxy.mono <| by simp [inter_eq_right.mpr hBF.1, hBF.2]
  obtain ⟨B, hB⟩ := (G ＼ F).exists_isMaximalAcyclicSet
  have hBF := by simpa [subset_diff] using hB.prop.subset
  use B, ⟨hB.prop.mono edgeDelete_le, fun R hR hBR ↦ ?_⟩, hB.prop.1
  by_contra! hRB
  obtain ⟨e, heR, heB⟩ := not_subset.mp hRB
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet (hR.subset heR)
  have hRexy : ¬((G ↾ R) ＼ {e}).ConnBetween x y := hR.isBridge heR |>.not_connBetween_of_isLink
    ⟨heR, hxy⟩ rfl
  rw [edgeRestrict_edgeDelete] at hRexy
  have := (IsMaximalAcyclicSet.connBetween_iff hB).mpr <| (h x y).mp hxy.connBetween
  simp only [edgeDelete_edgeRestrict, hBF.2.sdiff_eq_left] at this
  exact hRexy <| this.mono <| edgeRestrict_mono_right _ <| by simpa [subset_diff, heB]

lemma cycleMatroid_spanning : G.cycleMatroid.Spanning F ↔
    F ⊆ E(G) ∧ (∀ x y, G.ConnBetween x y ↔ (G ↾ F).ConnBetween x y) := by
  wlog hFE : F ⊆ E(G)
  · grind
  rw [spanning_iff_compl_coindep, cycleMatroid_coindep, cycleMatroid_E]
  simp only [diff_subset, true_and, hFE, edgeDelete_eq_edgeRestrict, diff_diff_cancel_left]

@[simp, grind =]
lemma cycleMatroid_cocircuit (G : Graph α β) (C : Set β) :
    G.cycleMatroid.IsCocircuit C ↔ G.IsBond C := by
  wlog hCE : C ⊆ G.cycleMatroid.E
  · grind
  rw [← dual_dual G.cycleMatroid, dual_isCocircuit_iff, isCircuit_iff_minimal_not_indep (by simpa)]
  conv in (G.cycleMatroid✶).Indep _ => rw [← dual_coindep_iff, dual_dual, cycleMatroid_coindep]
  simp only [not_and, not_forall]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨x, y, hxy⟩ := h.1 hCE
    rw [iff_def, and_comm, not_and, Classical.not_imp] at hxy
    obtain ⟨hxy, hCxy⟩ := hxy <| ConnBetween.mono edgeDelete_le
    obtain ⟨B, hBC, hB, hBxy⟩ := exists_isBond_subset_of_not_connBetween hxy hCxy
    have hBiff : B ⊆ E(G) → ∃ x x_1, ¬(G.ConnBetween x x_1 ↔ (G ＼ B).ConnBetween x x_1) :=
      fun _ ↦ ⟨x, y, by simp [hxy, hBxy]⟩
    rwa [← h.eq_of_subset hBiff hBC]
  obtain ⟨x, y, hxy, hnxy⟩ := h.exists_minimal_not_connBetween
  refine ⟨fun _ ↦ ⟨x, y, by simp [hxy, hnxy.1]⟩, fun B hB hBC ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := hB (hBC.trans h.subset)
  rw [iff_comm, iff_def, not_and, Classical.not_imp] at huv
  obtain ⟨huv, hnuv⟩ := huv (ConnBetween.mono edgeDelete_le)
  obtain ⟨F, hF, hFB, hFne, hFuv⟩ := isEdgeCut_subset_of_not_connBetween huv hnuv
  exact h.2 ⟨hF, hFne⟩ (hFB.trans hBC) |>.trans hFB

lemma IsEdgeCut.cycleMatroid_dual_cyclic (hF : G.IsEdgeCut F) : (G.cycleMatroid✶).Cyclic F := by
  refine ((cyclic_tfae (M := G.cycleMatroid✶) (A := F)).out 0 2).mpr fun e heF ↦ ?_
  obtain ⟨x, y, he⟩ := G.exists_isLink_of_mem_edgeSet <| hF.subset heF
  obtain ⟨B, hBF, hB, hBxy⟩ := exists_isBond_subset_of_not_connBetween he.connBetween
  <| hF.not_connBetween_of_isLink he heF
  use B, hBF, by simpa, ?_
  contrapose! hBxy
  exact IsLink.connBetween ⟨he, hBxy⟩

lemma IsMaximalAcyclicSet.isTree (hG : G.Connected) (hF : G.IsMaximalAcyclicSet F) :
    (G ↾ F).IsTree where
  isForest := isAcyclicSet_iff.mp hF.prop |>.2
  connected := by
    obtain ⟨hFE, hF⟩ := cycleMatroid_spanning.mp (cycleMatroid_isBase ▸ hF).spanning
    rw [connected_iff, Preconnected] at hG ⊢
    simpa [hG.1, ← hF] using hG.2

@[simp]
lemma cycleMatroid_edgeRestrict (G : Graph α β) (F : Set β) :
    (G ↾ F).cycleMatroid = G.cycleMatroid ↾ (E(G) ∩ F) := by
  refine ext_isCircuit rfl fun I hI ↦ ?_
  obtain ⟨hI, hIF⟩ := by simpa using hI
  simp [restrict_isCircuit_iff, hI, hIF]

lemma cycleMatroid_restrict (hF : F ⊆ E(G)) :
    G.cycleMatroid ↾ F = (G ↾ F).cycleMatroid := by
  rw [cycleMatroid_edgeRestrict, inter_eq_right.mpr hF]

@[simp]
lemma cycleMatroid_edgeDelete (G : Graph α β) (F : Set β) :
    (G ＼ F).cycleMatroid = G.cycleMatroid ＼ F :=
  ext_isCircuit rfl fun I hI ↦ by simp

lemma cycleMatroid_contract {φ} (hφ : H.connPartition.IsRepFun φ) (hHG : H ≤ G) :
    (G /[φ, E(H)]).cycleMatroid = G.cycleMatroid ／ E(H) := by
  apply_fun dual using dual_injective
  refine ext_indep rfl fun I hI ↦ ?_
  simp only [dual_ground, cycleMatroid_E, contract_edgeSet, subset_diff] at hI
  have hHGI : H ≤ G ＼ I := by simpa [hI.2.symm]
  simp only [← coindep_def, cycleMatroid_coindep, contract_edgeSet, subset_diff, hI.1, hI.2,
    and_self, true_and, dual_contract, delete_indep_iff, and_true]
  refine ⟨fun h x y ↦ ?_, fun h x y ↦ ?_⟩
  · rw [← contract_connBetween_iff hφ hHG, h, contract_edgeDelete_comm,
      contract_connBetween_iff hφ hHGI]
  wlog h : x ∈ φ '' V(G) ∧ y ∈ φ '' V(G)
  · grind
  obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩ := h
  rw [contract_connBetween_iff hφ hHG, h, contract_edgeDelete_comm,
    contract_connBetween_iff hφ hHGI]

@[simp]
lemma cycleMatroid_vertexDelete_isolatedSet (G : Graph α β) :
    (G - Isol(G)).cycleMatroid = G.cycleMatroid := by
  refine ext_isCircuit ?_ fun I hI ↦ ?_
  · rw [cycleMatroid_E, cycleMatroid_E, vertexDelete_edgeSet_diff, setincEdges_isolatedSet,
      diff_empty]
  rw [cycleMatroid_isCircuit, cycleMatroid_isCircuit]
  refine ⟨fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_), fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_)⟩
  · exact hxy.1
  simp [hxy, hxy.left_not_isolated, hxy.right_not_isolated]

lemma cycleMatroid_isRestriction_of_isLink (hl : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) :
    G.cycleMatroid ≤r H.cycleMatroid := by
  have hsu : E(G) ⊆ E(H) := by
    intro e he
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact (hl hxy).edge_mem
  use E(G), hsu, ext_isCircuit rfl fun I hI ↦ ?_
  rw [← inter_eq_right.mpr hsu, ← cycleMatroid_edgeRestrict]
  simp only [cycleMatroid_isCircuit]
  refine ⟨fun h ↦ h.of_isLink (fun e x y hxy ↦ (hl hxy).of_le_of_mem edgeRestrict_le ?_),
    fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_)⟩
  · simp [hxy.edge_mem, (hl hxy).edge_mem]
  obtain ⟨-, he⟩ := by simpa using hxy.edge_mem
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl huv |>.eq_and_eq_or_eq_and_eq (hxy.of_le edgeRestrict_le)
  · exact huv
  exact huv.symm

lemma cycleMatroid_isRestriction_of_le (h : G ≤ H) : G.cycleMatroid ≤r H.cycleMatroid :=
  cycleMatroid_isRestriction_of_isLink h.2

lemma cycleMatroid_isBasis :
    G.cycleMatroid.IsBasis B F ↔ F ⊆ E(G) ∧ (G ↾ F).IsMaximalAcyclicSet B := by
  wlog hFE : F ⊆ E(G)
  · grind
  simp only [hFE, true_and]
  rw [← isBase_restrict_iff, ← cycleMatroid_isBase, cycleMatroid_edgeRestrict,
    inter_eq_right.mpr hFE]

lemma cycleMatroid_eRk_add_one (hG : (G ↾ R).Connected) :
    G.cycleMatroid.eRk R + 1 = V(G).encard := by
  wlog hRE : R ⊆ E(G)
  · rw [← edgeRestrict_edgeSet_inter] at hG
    specialize this hG inter_subset_left
    rwa [← cycleMatroid_E, eRk_ground_inter] at this
  obtain ⟨B, hB⟩ := (G ↾ R).exists_isMaximalAcyclicSet
  rw [cycleMatroid_isBasis.mpr ⟨hRE, hB⟩ |>.eRk_eq_encard, eq_comm]
  obtain ⟨hBE, hBR⟩ := by simpa using hB.subset
  have := hB.isTree hG
  rw [edgeRestrict_edgeRestrict, inter_eq_right.mpr hBR] at this
  simpa [inter_eq_right.mpr hBE] using this.encard_vertexSet

lemma cycleMatroid_eRank_add_one (hG : G.Connected) :
    G.cycleMatroid.eRank + 1 = V(G).encard := by
  rw [← eRk_ground, cycleMatroid_eRk_add_one (by simpa)]

lemma Preconnected.cycleMatroid_dual_girth (hG : G.Preconnected) (n : ℕ) :
    n ≤ G.cycleMatroid✶.girth ↔ G.EdgeConnGE n := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp [EdgeConnGE]
  rw [edgeConnGE_iff_isBond hn, and_iff_right hG, le_girth_iff]
  simp_rw [cycleMatroid_cocircuit]

lemma cycleMatroid_loops : G.cycleMatroid.loops = ⋃ x, G.loopSet x := by
  ext e
  rw [← isLoop_iff, ← singleton_isCircuit, cycleMatroid_isCircuit, isCycleSet_singleton_iff]
  simp

lemma cycleMatroid_loopless_iff : G.cycleMatroid.Loopless ↔ G.Loopless := by
  refine ⟨fun ⟨h⟩ ↦ ⟨fun e x hex ↦ ?_⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  · rw [cycleMatroid_loops] at h
    simp only [loopSet, Set.ext_iff, mem_iUnion, mem_setOf_eq, mem_empty_iff_false, iff_false,
      not_exists] at h
    exact h _ _ hex
  simp [cycleMatroid_loops, loopSet]

instance [G.Loopless] : G.cycleMatroid.Loopless := cycleMatroid_loopless_iff.mpr ‹G.Loopless›

-- def edgeBasedVertexSep (G : Graph α β) (F : Set β) : Set α := V(G, F) ∩ V(G, E(G) \ F)

lemma IsClosedSubgraph.cycleMatroid_skew (h : H ≤c G) : G.cycleMatroid.Skew E(H) (E(G) \ E(H)) := by
  rw [skew_iff_exist_isBases, union_diff_cancel h.edgeSet_mono]
  obtain ⟨I, hI⟩ := exists_isBasis G.cycleMatroid E(H) h.edgeSet_mono
  obtain ⟨J, hJ⟩ := exists_isBasis G.cycleMatroid (E(G) \ E(H)) diff_subset
  use I, J, disjoint_sdiff_right.mono hI.subset hJ.subset, ?_
  rw [← union_diff_cancel h.edgeSet_mono]
  refine hI.union_isBasis_union hJ ?_
  have hIH : I ⊆ E(H) := by simpa using hI.subset
  have hJH : J ⊆ E(G) \ E(H) := by simpa using hJ.subset
  have hIindep := hI.indep
  have hJindep := hJ.indep
  rw [cycleMatroid_indep] at hIindep hJindep ⊢
  exact h.isAcyclicSet_union hIindep hJindep hIH hJH

lemma Compatible.cycleMatroid_union_skew (h : (V(G) ∩ V(H)).Subsingleton)
    (hcompat : G.Compatible H) : (G ∪ H).cycleMatroid.Skew E(G) E(H) := by
  have hinter : E(G) ∩ E(H) ⊆ (G ∪ H).cycleMatroid.loops := by
    obtain h_empty | ⟨x, hx⟩ := h.eq_empty_or_singleton
    · rw [← disjoint_iff_inter_eq_empty] at h_empty
      rw [(hcompat.edgeSet_disjoint_of_vertexSet_disjoint h_empty).inter_eq]
      exact empty_subset _
    · rw [cycleMatroid_loops]
      exact hcompat.edgeSet_inter_subset_loopSet_union hx |>.trans <| subset_iUnion ..
  rw [skew_iff_forall_isCircuit_of_inter_subset_loops]
  use hinter, fun C hC hC_sub ↦ ?_
  simp only [cycleMatroid_isCircuit, IsCycleSet] at hC hC_sub
  obtain ⟨W, hW, rfl⟩ := hC
  obtain (hW_G | hW_H) := hW.isCyclicWalk_or_isCyclicWalk_of_union_of_subsingleton_inter h
  · exact Or.inl (hW_G.isWalk.edgeSet_subset)
  · exact Or.inr (hW_H.isWalk.edgeSet_subset)

lemma cycleMatroid_disjointSum (h : (V(G) ∩ V(H)).Subsingleton) (hdj : Disjoint E(G) E(H)) :
    (G ∪ H).cycleMatroid = G.cycleMatroid.disjointSum H.cycleMatroid hdj := by
  have hc := Compatible.of_disjoint_edgeSet hdj
  have := (skew_iff_restrict_union_eq (by simp) (by simp) hdj).mp <| hc.cycleMatroid_union_skew h
  rw [restrict_eq_self_iff.mpr (by simp)] at this
  convert this
  · exact (cycleMatroid_isRestriction_of_le (G.left_le_union H)).eq_restrict.symm
  · exact (cycleMatroid_isRestriction_of_le hc.right_le_union).eq_restrict.symm

@[simp]
lemma isNonloop_iff_of_loopless {M : Matroid β} [M.Loopless] : M.IsNonloop e ↔ e ∈ M.E := by
  rw [isNonloop_iff_mem_compl_loops, loops_eq_empty]
  simp

@[simp]
lemma cycleMatroid_parallel [G.Loopless] : G.cycleMatroid.Parallel e f ↔ G.parallel e f := by
  obtain (rfl | hef) := eq_or_ne e f
  · simp
  rw [parallel_iff_isCircuit hef, cycleMatroid_isCircuit, isCycleSet_pair_iff_parallel hef]

lemma cycleMatroid_parallelClasses [G.Loopless] :
    G.cycleMatroid.parallelClasses = G.parallelClasses := by
  ext e f
  exact Partition.rel_ofRel_eq (r := G.parallel) ▸ cycleMatroid_parallel

@[simp]
lemma cycleMatroid_simple : G.cycleMatroid.Simple ↔ G.Simple := by
  rw [simple_iff_loopless_eq_of_parallel_forall, simple_iff, cycleMatroid_loopless_iff]
  refine and_congr_right fun hL ↦ ⟨fun h e f x y hel hfl ↦ ?_, fun h e f hp ↦ ?_⟩
  · refine h e f <| cycleMatroid_parallel.mpr ⟨hel.edge_mem, hfl.edge_mem, ?_⟩
    ext u v
    rw [hel.isLink_iff_sym2_eq, hfl.isLink_iff_sym2_eq]
  · obtain ⟨he, hf, hl⟩ := cycleMatroid_parallel.mp hp
    obtain ⟨x, y, hel⟩ := exists_isLink_of_mem_edgeSet he
    exact h hel (hl ▸ hel)

instance [G.Simple] : G.cycleMatroid.Simple := cycleMatroid_simple.mpr ‹G.Simple›

lemma cycleMatroid_isFlat (hFE : F ⊆ E(G)) (hF : ∀ H : Graph α β, H.IsCompOf (G ↾ F) → H ≤i G) :
    G.cycleMatroid.IsFlat F := by
  rw [isFlat_iff_forall_isCircuit hFE]
  intro C e hC heC hCss
  obtain ⟨W, hW, rfl⟩ := cycleMatroid_isCircuit ▸ hC
  obtain ⟨x, y, hxy_W⟩ := W.exists_isLink_of_mem_edge (by simpa using heC)
  obtain ⟨P, hP, hP_eq, rfl, rfl⟩ := hW.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy_W
  have hP_walk : (G ↾ F).IsWalk P := by
    simp only [isWalk_edgeRestrict_iff, hP.isWalk, true_and]
    rwa [← toGraph_edgeSet, hP_eq, edgeDelete_edgeSet, toGraph_edgeSet, diff_subset_iff]
  set H := (G ↾ F).walkable P.first
  have hH_comp : H.IsCompOf (G ↾ F) := walkable_isCompOf hP_walk.first_mem
  have hxH : P.first ∈ V(H) := mem_walkable_self_iff.mpr hP_walk.first_mem
  have hyH : P.last ∈ V(H) := hP_walk.connBetween_first_last
  have he_link : G.IsLink e P.first P.last := by
    rw [← hW.isWalk.wellFormed.toGraph_isLink] at hxy_W
    exact hxy_W.of_le hW.isWalk.toGraph_le
  have heH := (hF H hH_comp).isLink_of_mem_mem he_link hxH hyH
  exact edgeSet_mono hH_comp.le heH.edge_mem |>.2

open Finset

lemma orientation.isAcyclicSet_linearIndepOn {𝔽 : Type*} [Field 𝔽] [DecidableEq α]
    [DecidablePred (· ∈ E(G))] {I : Set β} (hI : G.IsAcyclicSet I) (D : orientation G) :
    LinearIndepOn 𝔽 (signedIncMatrix D 𝔽) I := by
  classical
  rw [linearIndepOn_iff'']
  rintro t g htI hg₀ hgI
  induction ht : t.card generalizing t with
  | zero =>
    intro i hit
    simp [card_eq_zero.mp ht] at hit
  | succ k ih =>
    intro i hit
    have hF : (G ↾ (t : Set β)).IsForest := (isAcyclicSet_iff.mp (hI.anti htI)).2
    have hne : E(G ↾ (t : Set β)).Nonempty := ⟨i, hI.subset (htI hit), hit⟩
    haveI : (G ↾ (t : Set β)).EdgeFinite := by
      constructor
      rw [edgeRestrict_edgeSet]
      exact (finite_toSet t).subset inter_subset_right
    obtain ⟨e₀, x₀, hPendant⟩ := hF.exists_isPendant hne
    have het := hPendant.isNonloopAt.edge_mem
    simp only [edgeRestrict_edgeSet, mem_inter_iff, SetLike.mem_coe] at het
    rw [← insert_sdiff_self_of_mem het.2, sum_insert (by simp)] at hgI
    have hgI' := congr_fun hgI x₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_apply, Pi.zero_apply] at hgI'
    rw [← (signedIncMatrix D 𝔽).col_apply x₀] at hgI'
    let D' : (G ↾ (t : Set β)).orientation := D.anti edgeRestrict_le
    have := D'.signedIncMatrix_pendent_col_support (𝔽 := 𝔽) hPendant
    simp only [support_eq_iff, mem_singleton_iff, Matrix.col_apply, forall_eq, ← ne_eq] at this
    rw [signedIncMatrix_anti_submatrix _ hPendant.edge_mem] at this
    have hforall : ∀ x ∈ t \ {e₀}, g x * signedIncMatrix D 𝔽 x x₀ = 0 := by
      simp only [mem_sdiff, Finset.mem_singleton, and_imp]
      rintro x hxt hxe₀
      suffices D.signedIncMatrix 𝔽 x x₀ = 0 by rw [this, mul_zero]
      by_cases hxG : x ∈ E(G)
      · have := this.2 x hxe₀
        rw [signedIncMatrix_anti_submatrix _ (by simp [hxt, hxG])] at this
        convert this
      simp [signedIncMatrix_apply_of_not_mem hxG]
    rw [sum_eq_zero hforall, add_zero, mul_eq_zero, Matrix.col_apply] at hgI'
    replace hgI' : g e₀ = 0 := hgI'.resolve_right (by convert this.1)
    simp only [hgI', zero_smul, zero_add, sdiff_singleton_eq_erase] at hgI
    specialize ih (t.erase e₀) (by simp [subset_insert_iff.mpr (Or.inl htI)]) ?_ hgI
      (by simp [het.2, ht])
    · intro j hj
      simp only [mem_erase, ne_eq, not_and_or, not_not] at hj
      obtain rfl | hj := hj
      · exact hgI'
      exact hg₀ j hj
    obtain rfl | hie := eq_or_ne i e₀
    · exact hgI'
    simp only [mem_erase, ne_eq, and_imp] at ih
    exact ih i hie hit

end Graph
namespace Graph
variable {α β : Type*} {G : Graph α β}

open Finset

noncomputable def cycleMatroidRep (𝔽 : Type*) [Field 𝔽] : G.cycleMatroid.Rep 𝔽 (α → 𝔽) where
  to_fun := by
    have hD := G.orientation_nonempty
    classical
    exact hD.some.signedIncMatrix 𝔽
  indep_iff' I := by
    classical
    generalize_proofs hD
    rw [cycleMatroid_indep]
    refine ⟨hD.some.isAcyclicSet_linearIndepOn, fun h ↦ ?_⟩
    rw [linearIndepOn_iff''] at h
    wlog hIE : I ⊆ E(G)
    · obtain ⟨e₀, he₀I, he₀E⟩ := not_subset.mp hIE
      let g₀ : β → 𝔽 := fun x₀ => if x₀ = e₀ then 1 else 0
      have h_finset : (↑({e₀} : Finset β) : Set β) ⊆ I := by
        simpa only [coe_singleton, Set.singleton_subset_iff, forall_const]
      have h_sum : ∑ i ∈ ({e₀} : Finset β), g₀ i • hD.some.signedIncMatrix 𝔽 i = 0 := by
        simp [g₀, hD.some.signedIncMatrix_apply_of_not_mem he₀E]
      absurd (by simp [g₀] : g₀ e₀ ≠ 0)
      exact h {e₀} g₀ h_finset (by simp [g₀]) h_sum e₀ (mem_singleton.mpr rfl)
    by_contra! hI
    obtain ⟨C₀, hC₀, hCG, hCI⟩ := (not_isAcyclicSet_iff hIE).mp hI
    obtain ⟨C'₀, hC'₀, rfl⟩ := isCycle_iff_exists_isCyclicWalk_eq.mp hC₀
    have hC'₀_G := hC'₀.of_le hCG
    obtain ⟨e₀, he₀⟩ := hC'₀.nonempty.edgeSet_nonempty
    have he₀_finset : e₀ ∈ C'₀.edge.toFinset := by simpa using he₀
    let g₀ := fun e₀ ↦ if e₀ ∈ C'₀.edge.toFinset then hD.some.coeff_walk hC'₀_G.isWalk 𝔽 e₀ else 0
    have hh : ∑ i ∈ C'₀.edge.toFinset, g₀ i • hD.some.signedIncMatrix 𝔽 i = 0 := by
      convert hD.some.signedIncMatrix_isCyclicWalk (𝔽 := 𝔽) hC'₀_G using 1
      refine sum_congr rfl (fun x₀ hx₀ ↦ ?_)
      simp only [g₀, hx₀, ↓reduceIte]
    have h_zero := h C'₀.edge.toFinset g₀ (by simpa using hCI) (fun i hi ↦ if_neg hi) hh e₀
      he₀_finset
    simp only [g₀, he₀_finset, ↓reduceIte] at h_zero
    exact hD.some.coeff_isCycleWalk_not_zero hC'₀_G he₀ 𝔽 h_zero

lemma cycleMatroid_representable (𝔽 : Type*) [Field 𝔽] :
    G.cycleMatroid.Representable 𝔽 := (G.cycleMatroidRep 𝔽).representable

end Graph
