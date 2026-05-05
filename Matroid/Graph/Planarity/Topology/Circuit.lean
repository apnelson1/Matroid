import Mathlib.Topology.Order.IntermediateValue
import Matroid.Graph.Planarity.Topology.Circle

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a b c u v w x y z : α}
  {C X Y : Set α}

open Set Function TopologicalSpace Topology Metric Nat unitInterval Set.Notation

def IsCircuit {α} [TopologicalSpace α] (C : Set α) : Prop :=
  ∃ f : Circle → α, Topology.IsEmbedding f ∧ range f = C

lemma IsCircuit.isPathConnected (hC : IsCircuit C) : IsPathConnected C := by
  obtain ⟨f, hf, rfl⟩ := hC
  exact isPathConnected_range hf.continuous

lemma circle_isCircuit : IsCircuit (univ : Set Circle) := ⟨id, IsEmbedding.id, by simp⟩

-- lemma isCircuit_of_exists_paths (P : Path x x) (hP : InjOn P (Ioc 0 1)) :
--     IsCircuit (range P) := by
--   let g' := AddCircle.liftIoc (1 : ℝ) 0 P.extend
--   have hisOpenEmb : IsOpenEmbedding ((Ioc 0 (0 + 1)).restrict ⇑P.extend) := by
--     rw [Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap]
--     refine ⟨Pi.continuous_restrict_apply (Ioc 0 (0 + 1)) P.extend.continuous, ?_, ?_⟩
--     · rintro ⟨i, hi1, hi2⟩ ⟨j, hj1, hj2⟩ hij
--       simp only [restrict_apply, zero_add] at hij hi1 hj1 hi2 hj2
--       rw [P.extend_apply ⟨hi1.le, hi2⟩, P.extend_apply ⟨hj1.le, hj2⟩] at hij
--       simpa using hP ⟨hi1, hi2⟩ ⟨hj1, hj2⟩ hij
--     sorry
--   let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
--   use g' ∘ e.symm, ?_, ?_
--   · apply IsOpenEmbedding.isEmbedding
--     apply IsOpenEmbedding.comp ?_ e.symm.isOpenEmbedding
--     apply IsOpenEmbedding.comp hisOpenEmb ?_
--     sorry
--   simp only [AddCircle.liftIoc, EquivLike.range_comp, range_restrict, zero_add, g']
--   rw [← image_univ, ← unitInterval.Icc_eq_univ]
--   sorry

lemma IsCircuit.twoConnected (hC : IsCircuit C) : ∀ x, IsPathConnected (C \ {x}) := by
  rintro x
  obtain ⟨f, hf, rfl⟩ := hC
  by_cases hx : x ∈ range f
  · obtain ⟨i, rfl⟩ := hx
    convert Circle.isPathConnected_compl_singleton i |>.image hf.continuous
    rw [image_compl_eq_range_diff_image hf.injective, image_singleton]
  simp only [hx, not_false_eq_true, diff_singleton_eq_self]
  exact isPathConnected_range hf.continuous

lemma IsCircuit.image (hC : IsCircuit C) {f : α → β} (hf : Topology.IsEmbedding f) :
    IsCircuit (f '' C) := by
  obtain ⟨f', hf', rfl⟩ := hC
  exact ⟨f ∘ f', hf.comp hf', by simp [range_comp]⟩

lemma IsCircuit.restrictSubtype (hC : IsCircuit C) (hCX : C ⊆ X) : IsCircuit (X ↓∩ C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  rw [range_subset_iff] at hCX
  exact ⟨_, hf.codRestrict X hCX, by rw [← Set.range_codRestrict hCX]⟩

lemma not_isCircuit_real (S : Set ℝ) : ¬ IsCircuit S := by
  rintro ⟨f, hf, rfl⟩
  let f1 := f ∘ Circle.path (-1) 1
  let f2 := f ∘ Circle.path 1 (-1)
  have hf1 : IsEmbedding f1 :=
    hf.comp (Circle.path_isClosedEmbedding_of_ne <| Circle.neg_ne_self 1).isEmbedding
  have hf2 : IsEmbedding f2 :=
    hf.comp (Circle.path_isClosedEmbedding_of_ne (Circle.neg_ne_self 1).symm).isEmbedding
  have hne : (-1 : Circle) ≠ 1 := Circle.neg_ne_self 1
  have hpaths {t : I} (ht : f1 t = f2 t) (ht0 : t ≠ 0) (ht1 : t ≠ 1) : False := by
    have hp : Circle.path (-1) 1 t = Circle.path 1 (-1) t :=
      hf.injective (by simpa [f1, f2, comp_apply] using ht)
    have hm : Circle.path (-1) 1 t ∈ range (Circle.path (-1) 1) ∩ range (Circle.path 1 (-1)) :=
      ⟨mem_range_self t, ⟨t, hp.symm⟩⟩
    rw [Circle.range_path_inter_range_path hne] at hm
    rcases hm with hm | hm
    · exact ht0 (Circle.path_injective_of_ne hne (by simpa [Path.source] using hm))
    · exact ht1 (Circle.path_injective_of_ne hne (by simpa [Path.target] using hm))
  obtain h | h := lt_or_gt_of_ne (hf.injective.ne hne)
  · have h1 : f1 0 < f2 0 := by simpa [f1, f2, -Circle.coe_path]
    have h2 : f1 1 > f2 1 := by simpa [f1, f2, -Circle.coe_path]
    obtain ⟨t, ht⟩ := intermediate_value_univ₂ hf1.continuous hf2.continuous h1.le (le_of_lt h2)
    refine hpaths ht ?_ ?_
    · rintro rfl; linarith [ht, h1]
    · rintro rfl; linarith [ht, h2]
  · have h1 : f2 0 < f1 0 := by simpa [f1, f2, -Circle.coe_path]
    have h2 : f2 1 > f1 1 := by simpa [f1, f2, -Circle.coe_path]
    obtain ⟨t, ht⟩ := intermediate_value_univ₂ hf2.continuous hf1.continuous h1.le (le_of_lt h2)
    refine hpaths ht.symm ?_ ?_
    · rintro rfl; linarith [ht, h1]
    · rintro rfl; linarith [ht, h2]

-- -- A set is a circuit iff it is a simple closed curve.
-- lemma isCircuit_iff_range_path_injOn_Ico :
--     IsCircuit C ↔ ∃ x, ∃ P : Path x x, InjOn P (Ico 0 1) ∧ range P = C := by
--   refine ⟨fun h ↦ ?_, fun ⟨x, h⟩ ↦ ?_⟩ <;> obtain ⟨f, hf, rfl⟩ := h
--   · let P := ((Circle.path 1 (-1)).trans (Circle.path (-1) 1)).map hf.continuous
--     have hPinj : InjOn P (Ico 0 1) := by
--       refine hf.injective.comp_injOn ?_
--       sorry
--     use f 1, P, hPinj
--     change range (f ∘ ((Circle.path 1 (-1)).trans (Circle.path (-1) 1))) = range f
--     rw [Surjective.range_comp]
--     intro i
--     sorry


--   sorry
