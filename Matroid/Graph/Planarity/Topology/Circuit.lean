import Mathlib.Topology.Order.IntermediateValue
import Matroid.Graph.Planarity.Topology.Circle

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a b c u v w x y z : α}
  {C X Y : Set α}

open Set Function TopologicalSpace Topology Metric Nat unitInterval Set.Notation AddCircle

def IsCircuit {α} [TopologicalSpace α] (C : Set α) : Prop :=
  ∃ f : C(Circle, α), Injective f ∧ range f = C

lemma IsCircuit.isPathConnected (hC : IsCircuit C) : IsPathConnected C := by
  obtain ⟨f, hf, rfl⟩ := hC
  exact isPathConnected_range f.continuous

lemma circle_isCircuit : IsCircuit (univ : Set Circle) :=
  ⟨ContinuousMap.id Circle, injective_id, by simp⟩

lemma IsCircuit.twoConnected (hC : IsCircuit C) : ∀ x, IsPathConnected (C \ {x}) := by
  rintro x
  obtain ⟨f, hf, rfl⟩ := hC
  by_cases hx : x ∈ range f
  · obtain ⟨i, rfl⟩ := hx
    convert Circle.isPathConnected_compl_singleton i |>.image f.continuous
    rw [image_compl_eq_range_diff_image hf, image_singleton]
  simp only [hx, not_false_eq_true, diff_singleton_eq_self]
  exact isPathConnected_range f.continuous

lemma IsCircuit.image (hC : IsCircuit C) {f : C(α, β)} (hf : Injective f) :
    IsCircuit (f '' C) := by
  obtain ⟨f', hf', rfl⟩ := hC
  exact ⟨⟨f.comp f', f.continuous.comp f'.continuous⟩, hf.comp hf', by simp [range_comp]⟩

lemma IsCircuit.restrictSubtype (hC : IsCircuit C) (hCX : C ⊆ X) : IsCircuit (X ↓∩ C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  rw [range_subset_iff] at hCX
  refine ⟨⟨codRestrict f.toFun X hCX, f.continuous.codRestrict hCX⟩, hf.codRestrict hCX, ?_⟩
  rw [← Set.range_codRestrict hCX]
  rfl

lemma not_isCircuit_real (S : Set ℝ) : ¬ IsCircuit S := by
  rintro ⟨f, hf, rfl⟩
  let f1 := f.comp (Circle.path (-1) 1).toContinuousMap
  let f2 := f.comp (Circle.path 1 (-1)).toContinuousMap
  have hne : (-1 : Circle) ≠ 1 := Circle.neg_ne_self 1
  have hpaths {t : I} (ht : f1 t = f2 t) (ht0 : t ≠ 0) (ht1 : t ≠ 1) : False := by
    have hp : Circle.path (-1) 1 t = Circle.path 1 (-1) t :=
      hf (by simpa [f1, f2, comp_apply] using ht)
    have hm : Circle.path (-1) 1 t ∈ range (Circle.path (-1) 1) ∩ range (Circle.path 1 (-1)) :=
      ⟨mem_range_self t, ⟨t, hp.symm⟩⟩
    rw [Circle.range_path_inter_range_path hne] at hm
    rcases hm with hm | hm
    · exact ht0 (Circle.path_injective_of_ne hne (by simpa [Path.source] using hm))
    · exact ht1 (Circle.path_injective_of_ne hne (by simpa [Path.target] using hm))
  obtain h | h := lt_or_gt_of_ne (hf.ne hne)
  · have h1 : f1 0 < f2 0 := by simpa [f1, f2, -Circle.coe_path]
    have h2 : f1 1 > f2 1 := by simpa [f1, f2, -Circle.coe_path]
    obtain ⟨t, ht⟩ := intermediate_value_univ₂ f1.continuous f2.continuous h1.le (le_of_lt h2)
    refine hpaths ht ?_ ?_
    · rintro rfl; linarith [ht, h1]
    · rintro rfl; linarith [ht, h2]
  · have h1 : f2 0 < f1 0 := by simpa [f1, f2, -Circle.coe_path]
    have h2 : f2 1 > f1 1 := by simpa [f1, f2, -Circle.coe_path]
    obtain ⟨t, ht⟩ := intermediate_value_univ₂ f2.continuous f1.continuous h1.le (le_of_lt h2)
    refine hpaths ht.symm ?_ ?_
    · rintro rfl; linarith [ht, h1]
    · rintro rfl; linarith [ht, h2]

noncomputable def Path.onCircle (P : Path x x) : C(Circle, α) where
  toFun t := ((AddCircle.homeoIccQuot (1 : ℝ) 0) <| (AddCircle.homeomorphCircle (by simp)).symm t)
    |>.liftOn (P.toFun ∘ iccHomeoI 0 (0 + 1) (by simp)) <| by
    intro i j ⟨⟩
    simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, comp_apply, zero_add]
    change P ⟨((0 : ℝ) - 0) / _, by simp⟩ = P ⟨((1 : ℝ) - 0) / _, by simp⟩
    simp
  continuous_toFun := by
    refine Continuous.comp' ?_ <| (Homeomorph.continuous _).comp (Homeomorph.continuous _)
    exact continuous_quot_lift _ (P.continuous.comp (Homeomorph.continuous _))

@[simp]
lemma Path.range_onCircle (P : Path x x) : range (Path.onCircle P) = range P := by
  ext y
  simp only [Path.onCircle, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, ContinuousMap.coe_mk,
    mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := Quot.exists_rep (homeoIccQuot 1 0 (homeomorphCircle (by simp) |>.symm t))
    rw [← hs]
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    use (homeomorphCircle (by simp)) (homeoIccQuot 1 0 |>.symm (Quot.mk _ (iccHomeoI 0 (0 + 1)
      (by simp) |>.symm s)))
    simp

noncomputable def Path.ofCircle (f : C(Circle, α)) : Path (f 1) (f 1) where
  toFun := fun t ↦ f (homeomorphCircle (T := 1) (by simp) t)
  source' := by simp [homeomorphCircle_apply]
  target' := by
    suffices f ((homeomorphCircle _) 0) = f 1 by
      convert this
      simp
    simp [homeomorphCircle_apply]

@[simp]
lemma Path.onCircle_ofCircle (f : C(Circle, α)) : (Path.ofCircle f).onCircle = f := by
  ext c
  simp only [onCircle, ofCircle, ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk]
  -- `homeoIccQuot 1 0 a` is a quotient element. Let's pick a representative `s ∈ Icc 0 1`.
  obtain ⟨s, hs⟩ := Quot.exists_rep (homeoIccQuot (1 : ℝ) 0 ((homeomorphCircle (by simp)).symm c))
  -- Finally, we know `Quot.mk s = homeoIccQuot a`, which means `↑s = a` in `AddCircle 1`.
  -- `homeoIccQuot.symm` applied to `Quot.mk s` gives `↑s`.
  have h_a : (homeomorphCircle (T := 1) (by simp)).symm c = ↑(s : ℝ) := by
    rw [← (homeoIccQuot (1 : ℝ) 0).symm_apply_apply ((homeomorphCircle (by simp)).symm c), ← hs]
    rfl
  simp [← hs, ← h_a]

@[simp]
lemma Path.ofCircle_onCircle_toFun (P : Path x x) : ⇑(Path.ofCircle P.onCircle) = ⇑P := by
  ext t
  wlog ht : t ≠ 1
  · simp at ht
    subst t
    conv_rhs => rw [P.target, ← P.source]
    convert this P 0 (by simp) using 1
    simp
  simp only [onCircle, ContinuousMap.toFun_eq_coe, coe_toContinuousMap, ContinuousMap.coe_mk,
    ofCircle, Homeomorph.symm_apply_apply]
  generalize_proofs h1
  change ((homeoIccQuot 1 0) ↑↑t).liftOn (⇑P ∘ ⇑(iccHomeoI 0 (0 + 1) onCircle._proof_3)) h1 = _

  have ht_mem : (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by
    simp only [zero_add, mem_Ico, lt_iff_le_and_ne, ne_eq, Icc.coe_eq_one, ht, not_false_eq_true,
      and_true]
    exact t.prop

  calc (homeoIccQuot 1 0 t).liftOn _ h1 = (Quot.mk _ ⟨t, Ico_subset_Icc_self ht_mem⟩).liftOn _ h1 :=
    by {change (Quot.mk _ _).liftOn _ _ = (Quot.mk _ _).liftOn _ _; congr 2; simpa using ht_mem}
    _ = P ((iccHomeoI 0 (0 + 1) (by simp)) ⟨(t : ℝ), Ico_subset_Icc_self ht_mem⟩) := rfl
    _ = P t := by congr 1; simp [iccHomeoI_apply_coe, Subtype.ext_iff]

lemma Path.onCircle_injective {P : Path x x} (hP : InjOn P (Ico 0 1)) :
    Injective (Path.onCircle P) := by
  intro t₁ t₂ ht
  -- Since `homeomorphCircle` is a homeomorphism, it suffices to show equality in `AddCircle 1`.
  apply (homeomorphCircle (T := 1) (by simp)).symm.injective
  set a₁ := (homeomorphCircle (T := 1) (by simp)).symm t₁
  set a₂ := (homeomorphCircle (T := 1) (by simp)).symm t₂
  -- Pick representatives in `Ico 0 1` for `a₁` and `a₂`
  obtain ⟨s₁, hs₁, has₁⟩ := eq_coe_Ico a₁
  obtain ⟨s₂, hs₂, has₂⟩ := eq_coe_Ico a₂
  -- We want to show `(s₁ : AddCircle 1) = (s₂ : AddCircle 1)`. By `coe_eq_coe_iff_of_mem_Ico`,
  -- this is equivalent to `s₁ = s₂` in `ℝ`.
  rw [← has₁, ← has₂, coe_eq_coe_iff_of_mem_Ico (a := 0) (by simpa using hs₁) (by simpa using hs₂)]
  -- Apply this evaluation to our hypothesis `ht`
  have ht' : P ⟨s₁, Ico_subset_Icc_self hs₁⟩ = P ⟨s₂, Ico_subset_Icc_self hs₂⟩ := by
    rw [← P.ofCircle_onCircle_toFun]
    convert ht <;> simp [ofCircle, has₁, has₂, a₁, a₂]
  -- Now use the injectivity of `P` on `Ico 0 1`
  exact Subtype.mk.inj (hP hs₁ hs₂ ht')

@[simp]
lemma Path.range_ofCircle (f : C(Circle, α)) : range (Path.ofCircle f) = range f := by
  conv_rhs => rw [← Path.onCircle_ofCircle f]
  rw [Path.range_onCircle]

lemma Path.ofCircle_injOn (f : C(Circle, α)) (hf : Injective f) :
    InjOn (Path.ofCircle f) (Ico 0 1) := by
  intro s₁ hs₁ s₂ hs₂ ht
  simp only [ofCircle, coe_mk', ContinuousMap.coe_mk] at ht
  exact Subtype.ext <| (coe_eq_coe_iff_of_mem_Ico ⟨s₁.prop.1, by grind⟩ ⟨s₂.prop.1, by grind⟩).mp
    <| (homeomorphCircle (T := 1) (by simp)).injective (hf ht)

-- A set is a circuit iff it is a simple closed curve.
lemma isCircuit_iff_range_path_injOn_Ico :
    IsCircuit C ↔ ∃ x, ∃ P : Path x x, InjOn P (Ico 0 1) ∧ range P = C := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    use f 1, Path.ofCircle f, (Path.ofCircle_injOn f hf), ?_
    rw [Path.range_ofCircle f]
  rintro ⟨x, P, hPinj, rfl⟩
  use P.onCircle, Path.onCircle_injective hPinj, by simp

lemma IsCircuit.exists_path_injOn_Ico (hC : IsCircuit C) (hx : x ∈ C) :
    ∃ P : Path x x, InjOn P (Ico 0 1) ∧ range P = C := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨t, rfl⟩ := hx
  let g := f.comp ⟨_, (Homeomorph.mulRight t).continuous⟩
  use (Path.ofCircle g).cast (by simp [g]) (by simp [g]), ?_
  · simp only [Path.cast_coe, Path.range_ofCircle]
    apply EquivLike.range_comp
  exact Path.ofCircle_injOn g <| (EquivLike.injective_comp ..).mpr hf
