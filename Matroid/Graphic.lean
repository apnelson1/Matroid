import Matroid.Axioms.Circuit
import Matroid.Minor.Contract
import Matroid.Graph.Spanning
import Matroid.Graph.Minor.Conn
import Matroid.Graph.Connected.Minor
import Matroid.Connectivity.Skew
import Matroid.Connectivity.ConnSystem.Matroid

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {B F F' R R': Set β} {C w P Q : WList α β}

open Set WList Matroid Function

attribute [grind →] IsCocircuit.subset_ground

namespace Graph

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

lemma IsMaximalAcyclicSet.exists (G : Graph α β) : ∃ F, G.IsMaximalAcyclicSet F := by
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
  obtain ⟨B, hB⟩ := IsMaximalAcyclicSet.exists (G ＼ F)
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
    rw [iff_def, and_comm, not_and, _root_.not_imp] at hxy
    obtain ⟨hxy, hCxy⟩ := hxy <| ConnBetween.mono edgeDelete_le
    obtain ⟨B, hBC, hB, hBxy⟩ := exists_isBond_subset_of_not_connBetween hxy hCxy
    have hBiff : B ⊆ E(G) → ∃ x x_1, ¬(G.ConnBetween x x_1 ↔ (G ＼ B).ConnBetween x x_1) :=
      fun _ ↦ ⟨x, y, by simp [hxy, hBxy]⟩
    rwa [← h.eq_of_subset hBiff hBC]
  obtain ⟨x, y, hxy, hnxy⟩ := h.exists_minimal_not_connBetween
  refine ⟨fun _ ↦ ⟨x, y, by simp [hxy, hnxy.1]⟩, fun B hB hBC ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := hB (hBC.trans h.subset_edgeSet)
  rw [iff_comm, iff_def, not_and, _root_.not_imp] at huv
  obtain ⟨huv, hnuv⟩ := huv (ConnBetween.mono edgeDelete_le)
  obtain ⟨F, hF, hFB, hFne, hFuv⟩ := isEdgeCut_subset_of_not_connBetween huv hnuv
  exact h.2 ⟨hF, hFne⟩ (hFB.trans hBC) |>.trans hFB

@[simp]
lemma cycleMatroid_edgeRestrict (G : Graph α β) (F : Set β) :
    (G ↾ F).cycleMatroid = G.cycleMatroid ↾ (E(G) ∩ F) := by
  refine ext_isCircuit rfl fun I hI ↦ ?_
  obtain ⟨hI, hIF⟩ := by simpa using hI
  simp [restrict_isCircuit_iff, hI, hIF]

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

-- lemma exists_connected_eq_cycleMatroid (G : Graph α β) :
--     ∃ H : Graph α β, H.Preconnected ∧ H.cycleMatroid = G.cycleMatroid := by
--   obtain rfl | hG := G.eq_bot_or_vertexSet_nonempty
--   · use ⊥
--     simp
--   let f1 : G.Components → α := fun H ↦ H.prop.nonempty.some
--   have hf1 : Injective f1 := by
--     intro H₁ H₂ hH
--     have := mt <| G.components_pairwise_disjoint H₁.prop H₂.prop
--     rw [disjoint_iff_vertexSet_disjoint, ne_eq, not_not, ← Subtype.ext_iff,
--       not_disjoint_iff] at this
--     exact this ⟨f1 H₁, H₁.prop.nonempty.some_mem, hH ▸ H₂.prop.nonempty.some_mem⟩
--   let x := f1 ⟨G.components_nonempty hG |>.some, G.components_nonempty hG |>.some_mem⟩
--   classical
--   let f : α → α := fun v ↦ if v ∈ range f1 then x else v
--   use f ''ᴳ G, ?_, ext_isCircuit (by simp) fun I hI ↦ ?_
--   · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
--     refine ConnBetween.trans (y := x) ?_ ?_
--     · let Ca : G.Components := ⟨G.walkable a, G.walkable_isCompOf ha⟩
--       have hx : f (f1 Ca) = x := by
--         convert ite_true _ _
--         simp
--       rw [← hx]
--       exact Ca.prop.nonempty.some_mem.map f
--     let Cb : G.Components := ⟨G.walkable b, G.walkable_isCompOf hb⟩
--     have hy : f (f1 Cb) = x := by
--       convert ite_true _ _
--       simp
--     rw [← hy]
--     exact Cb.prop.nonempty.some_mem.map f |>.symm
--   simp_rw [cycleMatroid_isCircuit, IsCycleSet]
--   constructor <;> rintro ⟨C, hC, rfl⟩ <;> rw [cycleMatroid_E, map_edgeSet] at hI
--   · sorry
--   use C.map f, hC.map (fun a ha b hb hfab ↦ ?_), by simp
--   unfold f at hfab
--   split_ifs at hfab with hfa hfb hfb
--   · obtain ⟨Ca, rfl⟩ := hfa
--     obtain ⟨Cb, rfl⟩ := hfb
--     rw [hf1.eq_iff, ← Subtype.coe_inj]
--     apply Ca.prop.eq_of_mem_mem Cb.prop (x := f1 Ca) Ca.prop.nonempty.some_mem
--     rw [Cb.prop.eq_walkable_of_mem_walkable Cb.prop.nonempty.some_mem]
--     exact hC.isWalk.connBetween_of_mem_of_mem hb ha
--   all_goals subst hfab
--   · simp [x] at hfb
--   · simp [x] at hfa
--   rfl

lemma cycleMatroid_isFlat (hFE : F ⊆ E(G)) (hF : ∀ H : Graph α β, H.IsCompOf (G ↾ F) → H ≤i G) :
    G.cycleMatroid.IsFlat F := by
  sorry
/-
From Flat
- flat iff cycle almost included is included
- take a compOf G \upr F
- this is clearly a subgraph so why is it induced?
- induced is defined as any edge, e, between x and y s.t. x and y are in the subgraph then e must also be in the subgraph.
- Suppose there is an edge e that is not in F and between x and y belonging to some connected component of G \upr F. Then, since connected, there is some path between x and y inside F.
- Together with e, we have a cycle which is almost included in F, so e is in F. contradiction

To Flat
- Take a cycle that is almost included in F.
- Every vertex of this cycle must be in some connected component of G \upr F.
- So the only edge possibly not included in F, e, is between two vertices in the component.
- This component is an induced subgraph so e is included in F.
-/
