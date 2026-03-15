import Matroid.Graph.Forest

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α}
  {F F' I J : Set β} {P C Q : WList α β}
open Set WList

namespace Graph

/-- `G.IsCycleSet C` means that `C` is the edge set of a cycle of `G`. -/
def IsCycleSet (G : Graph α β) (C : Set β) : Prop := ∃ C₀, G.IsCyclicWalk C₀ ∧ E(C₀) = C

lemma isCycleSet_iff {C' : Set β} : G.IsCycleSet C' ↔ ∃ C ≤ G, C.IsCycle ∧ C' = E(C) := by
  simp_rw [isCycle_iff_exists_isCyclicWalk_eq]
  refine ⟨fun ⟨C₀, hC₀, h⟩ ↦ ?_, ?_⟩
  · use C₀.toGraph, hC₀.isWalk.toGraph_le, ?_, by simp [h.symm]
    use C₀, hC₀.isCyclicWalk_toGraph
  rintro ⟨_, hCG, ⟨C, hCC, rfl⟩, rfl⟩
  use C, hCC.of_le hCG, by simp

@[simp]
lemma edgeRestrict_isCycleSet_iff (C : Set β) :
    (G ↾ F).IsCycleSet C ↔ G.IsCycleSet C ∧ C ⊆ F := by
  refine ⟨fun ⟨C₀, hC₀, h⟩ ↦ ?_, fun ⟨⟨C₀, hC₀, hss⟩, hsF⟩ ↦
    ⟨C₀, (G.edgeRestrict_isCyclicWalk_iff ..).mpr ⟨hC₀, hss ▸ hsF⟩, hss⟩⟩
  rw [edgeRestrict_isCyclicWalk_iff] at hC₀
  exact ⟨⟨C₀, hC₀.1, h ▸ rfl⟩, h ▸ hC₀.2⟩

@[simp]
lemma edgeDelete_isCycleSet_iff (C : Set β) :
    (G ＼ F).IsCycleSet C ↔ G.IsCycleSet C ∧ Disjoint C F := by
  refine ⟨fun ⟨C₀, hC₀, h⟩ ↦ ?_, fun ⟨⟨C₀, hC₀, hss⟩, hdisj⟩ ↦
    ⟨C₀, (edgeDelete_isCyclicWalk_iff ..).mpr ⟨hC₀, hss ▸ hdisj⟩, hss⟩⟩
  rw [edgeDelete_isCyclicWalk_iff] at hC₀
  exact ⟨⟨C₀, hC₀.1, h⟩, h ▸ hC₀.2⟩

@[simp]
lemma induce_isCycleSet_iff (C : Set β) :
    G[X].IsCycleSet C ↔ ∃ C₀, G.IsCyclicWalk C₀ ∧ V(C₀) ⊆ X ∧ E(C₀) = C := by
  simp only [IsCycleSet, induce_isCyclicWalk_iff, and_assoc]

@[simp]
lemma vertexDelete_isCycleSet_iff (C : Set β) :
    (G - X).IsCycleSet C ↔ ∃ C₀, G.IsCyclicWalk C₀ ∧ Disjoint V(C₀) X ∧ E(C₀) = C := by
  simp only [IsCycleSet, vertexDelete_isCyclicWalk_iff, and_assoc]

lemma IsCycleSet.of_isLink {C : Set β} (h : G.IsCycleSet C)
    (he : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) : H.IsCycleSet C := by
  obtain ⟨C₀, hC₀, h⟩ := h
  exact ⟨C₀, hC₀.of_forall_isLink he, h⟩

lemma IsClosedSubgraph.isCycleSet {C : Set β} (hC : G.IsCycleSet C) (hHG : H ≤c G) :
    H.IsCycleSet C ∨ (G - V(H)).IsCycleSet C := by
  simp_rw [isCycleSet_iff] at hC ⊢
  obtain ⟨C, hCG, hC, rfl⟩ := hC
  obtain h | h := hHG.le_or_le_of_preconnected hC.connected.pre hCG
  · left
    use C
  right
  use C

lemma IsLoopAt.isCycleSet (h : G.IsLoopAt e x) : G.IsCycleSet {e} := by
  refine ⟨.cons x e (.nil x), ⟨⟨⟨h.walk_isWalk, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩ <;> simp

lemma isCycleSet_singleton_iff : G.IsCycleSet {e} ↔ ∃ x, G.IsLoopAt e x := by
  refine ⟨fun ⟨C, hC, hCe⟩ ↦ ?_, fun ⟨x, hx⟩ ↦ hx.isCycleSet⟩
  match C with
  | .nil u => simp at hCe
  | .cons u e (nil v) =>
    obtain rfl := by simpa using hCe
    obtain ⟨hv, rfl⟩ := by simpa [isTour_iff] using hC.isTour
    use u, hv.2
  | .cons u f1 (cons v f2 w) =>
    exfalso
    have := by simpa using hC.isTrail
    obtain ⟨h', heuv, hf12, hf1w⟩ := this
    simp only [cons_edgeSet] at hCe
    obtain rfl := hCe ▸ (show f1 ∈ insert f1 (insert f2 E(w)) by simp)
    obtain rfl := hCe ▸ (show f2 ∈ insert f1 (insert f2 E(w)) by simp)
    simp only [not_true_eq_false] at hf12

lemma isCycleSet_pair_iff_parallel [G.Loopless] {e f : β} (hef : e ≠ f) :
    G.IsCycleSet {e, f} ↔ G.parallel e f := by
  refine ⟨fun ⟨C₀, hC₀, hC₀_eq⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hlen : C₀.length = 2 := by
      apply_fun encard at hC₀_eq
      rw [encard_pair hef, (show E(C₀) = {x | x ∈ C₀.edge} by rfl), hC₀.edge_nodup.encard_toSet_eq,
        length_edge] at hC₀_eq
      exact ENat.coe_inj.mp hC₀_eq
    obtain ⟨x, y, e', f', hxy, he'f', rfl⟩ := hC₀.length_eq_two_iff.1 hlen
    simp only [cons_edgeSet, nil_edgeSet, insert_empty_eq, pair_eq_pair_iff] at hC₀_eq
    have hl1 : G.IsLink e' x y := by grind [cons_isWalk_iff, hC₀.isWalk]
    have hl2 : G.IsLink f' y x := by grind [cons_isWalk_iff, hC₀.isWalk]
    obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := hC₀_eq <;>
      [use hl1.edge_mem, hl2.edge_mem; use hl2.edge_mem, hl1.edge_mem] <;> ext u v <;>
      rw [hl1.isLink_iff_sym2_eq, hl2.isLink_iff_sym2_eq, Sym2.eq_swap]
  · obtain ⟨he, hf, hl⟩ := G.parallel_iff_inc_eq e f |>.mp h
    obtain ⟨x, y, hexy⟩ := G.exists_isLink_of_mem_edgeSet he
    have hfxy : G.IsLink f x y := by rwa [← inc_eq_inc_iff.mp hl]
    let C₀ : WList α β := cons x e (cons y f (nil x))
    use C₀
    have hwalk : G.IsWalk C₀ := cons_isWalk_iff.mpr ⟨hexy, hfxy.symm.walk_isWalk⟩
    refine ⟨⟨⟨⟨hwalk, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩ <;> simp [C₀, hef, hexy.ne.symm]

/-- `G.IsAcyclicSet X` means that the subgraph `G ↾ X` is a forest. -/
def IsAcyclicSet (G : Graph α β) (I : Set β) : Prop :=
  I ⊆ E(G) ∧ ∀ C₀, G.IsCyclicWalk C₀ → ¬ (E(C₀) ⊆ I)

lemma edgeRestrict_isForest_iff' :
    (G ↾ F).IsForest ↔ ∀ (C : WList α β), E(C) ⊆ F → ¬ G.IsCyclicWalk C := by
  rw [isForest_iff_not_isCyclicWalk]
  refine ⟨fun h C hCF hC ↦ h C ?_, fun h C hC ↦ h C ?_ (hC.of_le <| by simp)⟩
  · exact hC.isCycle_of_le (by simp) <| by simp [hCF, hC.isWalk.edgeSet_subset]
  exact hC.isWalk.edgeSet_subset.trans inter_subset_right

lemma edgeRestrict_isForest_iff (hF : F ⊆ E(G)) : (G ↾ F).IsForest ↔ G.IsAcyclicSet F := by
  rw [edgeRestrict_isForest_iff', IsAcyclicSet]
  aesop

lemma isAcyclicSet_iff : G.IsAcyclicSet F ↔ F ⊆ E(G) ∧ (G ↾ F).IsForest := by
  by_cases hF : F ⊆ E(G)
  · rw [edgeRestrict_isForest_iff hF, and_iff_right hF]
  exact iff_of_false (mt (fun h ↦ h.1) hF) (by simp [hF])

lemma not_isAcyclicSet_iff (hF : F ⊆ E(G)) :
    ¬ G.IsAcyclicSet F ↔ ∃ C, C.IsCycle ∧ C ≤ G ∧ E(C) ⊆ F := by
  simp [isAcyclicSet_iff, hF, not_isForest_iff_exists_isCycle]

namespace IsAcyclicSet

lemma subset (hF : G.IsAcyclicSet F) : F ⊆ E(G) := hF.1

lemma mono (hGH : G ≤ H) (hF : G.IsAcyclicSet F) : H.IsAcyclicSet F := by
  use hF.1.trans (edgeSet_mono hGH)
  intro C₀ hC₀ heC₀
  exact hF.2 _ (hC₀.isCycle_of_le hGH (heC₀.trans hF.1)) heC₀

lemma anti_inter (hGH : G ≤ H) (hF : H.IsAcyclicSet F) : G.IsAcyclicSet (E(G) ∩ F) := by
  obtain ⟨hF, hF'⟩ := hF
  use inter_subset_left
  intro C hC heC
  rw [subset_inter_iff] at heC
  exact hF' C (hC.of_le hGH) heC.2

lemma anti (hsu : F' ⊆ F) (hF : G.IsAcyclicSet F) : G.IsAcyclicSet F' :=
  ⟨hsu.trans hF.1, fun C hC heC ↦ hF.2 C (hC.of_le (by simp)) (heC.trans hsu)⟩

lemma isBridge (hF : G.IsAcyclicSet F) (he : e ∈ F) : (G ↾ F).IsBridge e := by
  rw [isAcyclicSet_iff] at hF
  exact hF.2 ⟨hF.1 he, he⟩

lemma of_edgeDelete_isBond {B} (hB : G.IsBond B) (hF : (G ＼ B).IsAcyclicSet F)
    (he : e ∈ B) : G.IsAcyclicSet (insert e F) := by
  have hFE := hF.1.trans diff_subset
  simp only [isAcyclicSet_iff, edgeDelete_edgeSet, subset_diff, hFE, true_and,
    edgeDelete_edgeRestrict, insert_subset_iff, hB.subset he, and_self] at hF ⊢
  obtain ⟨hFB, hFf⟩ := hF
  replace hFf : ((G ↾ insert e F) ＼ {e}).IsForest := by
    rw [hFB.sdiff_eq_left] at hFf
    simpa [hFB.mono_right (by simpa : {e} ⊆ B) |>.sdiff_eq_left]
  apply hFf.of_edgeDelete_singleton ?_
  have := by simpa using hB.prop.1.anti (edgeRestrict_le (E₀ := insert e F))
  rwa [(inter_eq_right (s := E(G))).mpr (by simpa [hB.subset he, insert_subset_iff]),
    insert_inter_of_mem he, hFB.inter_eq, insert_empty_eq] at this

end IsAcyclicSet

lemma IsClosedSubgraph.isAcyclicSet_union (hI : G.IsAcyclicSet I) (hJ : G.IsAcyclicSet J)
    (hIH : I ⊆ E(H)) (hJH : J ⊆ E(G) \ E(H)) (h : H ≤c G): G.IsAcyclicSet (I ∪ J) := by
  simp only [isAcyclicSet_iff, hI.subset, IsForest,
    edgeRestrict_edgeSet, mem_inter_iff, and_imp, true_and, hJ.subset,
    union_subset_iff, and_self, mem_union] at hI hJ ⊢
  rintro e he heIJ
  wlog heI : e ∈ I
  · rw [or_comm] at heIJ
    rw [union_comm]
    refine this (H := G - V(H)) (I := J) (J := I) ?_ ?_ h.compl hJ hI he heIJ
      (heIJ.resolve_right heI) <;> simpa [h.compl_edgeSet, diff_diff_cancel_left h.edgeSet_mono]
  refine hI he heI |>.anti_of_mem (edgeRestrict_mono_left h.le I) (by simp [heI, hIH heI])
  |>.of_isClosedSubgraph ?_
  convert h.inter_le edgeRestrict_le
  refine ext_of_le_le edgeRestrict_le H.inter_le_left (by simp [h.vertexSet_mono]) ?_
  have hcompat : Compatible H (G ↾ (I ∪ J)) := compatible_of_le_le h.le edgeRestrict_le
  rw [subset_diff, disjoint_comm] at hJH
  simp [hcompat.inter_edgeSet, inter_union_distrib_left, ← inter_assoc, hJH.2.inter_eq,
    inter_eq_left.mpr h.edgeSet_mono]

def IsMaximalAcyclicSet (G : Graph α β) (F : Set β) : Prop :=
  Maximal G.IsAcyclicSet F

lemma IsMaximalAcyclicSet.isAcyclicSet (hF : G.IsMaximalAcyclicSet F) : G.IsAcyclicSet F := hF.prop

@[simp, grind →]
lemma IsMaximalAcyclicSet.subset (hF : G.IsMaximalAcyclicSet F) : F ⊆ E(G) := hF.prop.1

lemma IsMaximalAcyclicSet.insert_not_isBridge (he : e ∈ E(G) \ F) (hF : G.IsMaximalAcyclicSet F) :
    ¬ (G ↾ insert e F).IsBridge e := by
  intro hb
  have hef : G.IsAcyclicSet (insert e F) := by
    rw [isAcyclicSet_iff]
    simp only [insert_subset_iff, he.1, hF.prop.1, and_self, true_and]
    refine IsForest.of_edgeDelete_singleton hb ?_
    simp only [edgeRestrict_edgeDelete, mem_singleton_iff, insert_diff_of_mem, he.2,
      not_false_eq_true, diff_singleton_eq_self]
    exact isAcyclicSet_iff.mp hF.prop |>.2
  exact he.2 <| insert_eq_self.mp (hF.eq_of_subset hef (by grind)).symm

lemma IsMaximalAcyclicSet.connBetween_iff (hF : G.IsMaximalAcyclicSet F) :
    (G ↾ F).ConnBetween x y ↔ G.ConnBetween x y := by
  refine ⟨fun h ↦ h.mono edgeRestrict_le, ?_⟩
  rintro ⟨w, hw, rfl, rfl⟩
  by_contra h'
  let S := V((G ↾ F).walkable w.first)
  obtain ⟨e, heS, x, hxS, y, ⟨hy, hyS⟩, hxy⟩ :=
    hw.inter_setLinkEdges_nonempty ((G ↾ F).mem_walkable hw.first_mem) h'
  have heF : e ∉ F := by
    contrapose! hyS
    exact ConnBetween.trans hxS (IsLink.connBetween ⟨hyS, hxy⟩)
  have := hF.insert_not_isBridge ⟨hxy.edge_mem, heF⟩
  rw [IsLink.isBridge_iff_not_connBetween (by simpa), not_not] at this
  simp only [edgeRestrict_edgeDelete, mem_singleton_iff, insert_diff_of_mem, heF, not_false_eq_true,
    diff_singleton_eq_self] at this
  exact hyS (ConnBetween.trans hxS this)
