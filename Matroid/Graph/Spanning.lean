import Matroid.Graph.Forest

variable {α β : Type*} {G H : Graph α β} {x y z : α} {e f : β} {F : Set β}

open Set

namespace Graph

/-! ### Maximal Acyclic Sets -/

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

-- lemma IsBond.not_disjoint_of_maximal_isAcyclicSet {B} (hF : Maximal G.IsAcyclicSet F)
--     (hB : G.IsBond B) : ¬ Disjoint F B := by
--   rintro hdj
--   have : ∀ ⦃x : β⦄, x ∈ B → x ∉ F := by rwa [disjoint_comm, disjoint_iff_forall_notMem] at hdj
--   obtain ⟨e, heB⟩ := hB.prop.2
--   have he := hB.subset_edgeSet heB
--   apply not_isBridge_of_maximal_isAcyclicSet hF ⟨he, this heB⟩
--   have := by simpa using hB.prop.1.anti (edgeRestrict_le (E₀ := insert e F))
--   rwa [(inter_eq_right (s := E(G))).mpr (by simp [hF.prop.1, insert_subset_iff, he]),
--     insert_inter_of_mem heB, hdj.inter_eq, insert_empty_eq] at this

-- lemma isForest_of_maximal_isAcyclicSet (hF : Maximal G.IsAcyclicSet F) : (G ↾ F).IsForest := by
--   rw [show G.IsAcyclicSet = fun X ↦ X ⊆ E(G) ∧ (G ↾ X).IsForest by
--     ext; exact isAcyclicSet_iff] at hF
--   exact hF.prop.2

-- lemma IsAcyclicSet.eq_of_connBetween_iff {R} (hRF : R ⊆ F)
--     (hR : ∀ x y, G.ConnBetween x y ↔ (G ↾ R).ConnBetween x y) (hF : G.IsAcyclicSet F) : R = F := by
--   by_contra! h
--   obtain ⟨e, heF, heR⟩ := ssubset_iff_of_subset hRF |>.mp <| hRF.ssubset_of_ne h
--   obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet <| hF.1 heF
--   have hxyF : (G ↾ F).IsLink e x y := ⟨heF, hxy⟩
--   apply hxyF.isBridge_iff_not_connBetween.mp <| hF.isBridge heF
--   refine hR x y |>.mp hxy.connBetween |>.mono ?_
--   rw [edgeRestrict_edgeDelete]
--   exact edgeRestrict_mono_right _ <| by simpa [subset_diff, heR]

-- lemma maximal_isAcyclicSet_iff_minimal_connBetween : Maximal G.IsAcyclicSet F ↔
--     Minimal (fun F ↦ ∀ x y, G.ConnBetween x y ↔ (G ↾ F).ConnBetween x y) F := by
--   refine ⟨fun hF ↦ ⟨fun _ _ ↦ connBetween_iff_of_maximal_isAcyclicSet hF |>.symm,
--     fun R hR hRF ↦ hF.prop.eq_of_connBetween_iff hRF hR |>.ge⟩, fun hF ↦ ⟨?_,
--       fun R hR hRF ↦ hR.eq_of_connBetween_iff hRF hF.prop |>.ge⟩⟩
--   have hFE := by simpa [hF.prop] using hF.2 (y := E(G) ∩ F)
--   rw [isAcyclicSet_iff]
--   refine ⟨hFE, fun e ⟨he, heF⟩ ↦ ?_⟩
--   by_contra! hb
--   have h : ∀ x y, G.ConnBetween x y ↔ (G ↾ (F \ {e})).ConnBetween x y := by
--     refine fun x y ↦ ⟨fun h ↦ ?_, fun h ↦ h.mono edgeRestrict_le⟩
--     rw [← edgeRestrict_edgeDelete]
--     exact (hF.prop x y |>.mp h).edgeDelete_singleton_connBetween hb
--   simpa [heF, subset_diff_singleton_iff] using hF.2 h
