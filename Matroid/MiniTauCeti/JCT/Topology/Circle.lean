module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Topology.Homotopy.Contractible
public import Matroid.MiniTauCeti.JCT.Topology.Path

@[expose] public section

open Set Function TopologicalSpace Topology Metric Nat Complex Real

instance (x : ℝ) : LocallyPathConnectedSpace (AddCircle x) := LocallyPathConnectedSpace.coinduced _

instance : LocallyPathConnectedSpace Circle := by
  convert LocallyPathConnectedSpace.coinduced AddCircle.homeomorphCircle'
  exact AddCircle.homeomorphCircle'.coinduced_eq.symm

namespace Circle

variable {x y z : Circle} {a b : ℝ} {s : Set ℝ}

/-- The circle is not contractible because its fundamental group is nontrivial. -/
theorem not_contractibleSpace : ¬ ContractibleSpace Circle := by
  intro h
  have : ContractibleSpace (AddCircle (1 : ℝ)) :=
    (AddCircle.homeomorphCircle one_ne_zero).contractibleSpace
  have : SimplyConnectedSpace (AddCircle (1 : ℝ)) :=
    SimplyConnectedSpace.ofContractible _
  let e := AddCircle.windingNumberIso (0 : AddCircle (1 : ℝ))
  have h01 : (Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) =
      Multiplicative.ofAdd (1 : ℤ) := by
    let a := e.symm (Multiplicative.ofAdd (0 : ℤ))
    let b := e.symm (Multiplicative.ofAdd (1 : ℤ))
    exact (e.apply_symm_apply _).symm.trans ((congrArg e (Subsingleton.elim a b)).trans
      (e.apply_symm_apply _))
  change (0 : ℤ) = 1 at h01
  exact zero_ne_one h01

@[simp]
lemma im_val_eq_zero_iff (x : Circle) : x.val.im = 0 ↔ x = 1 ∨ x = -1 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  suffices x.val = 1 ∨ x.val = -1 by
    obtain h | h := this
    · replace h := OneMemClass.coe_eq_one.mp h
      tauto
    simp_rw [← neg_eq_iff_eq_neg, ← coe_neg] at h
    exact Or.inr <| neg_eq_iff_eq_neg.mp <| OneMemClass.coe_eq_one.mp h
  have hreal : (x.val.re : ℂ) = x.val :=
    Complex.conj_eq_iff_re.mp ((Complex.im_eq_zero_iff_isSelfAdjoint x.val).mp h)
  have hnorm : ‖x.val‖ = 1 := norm_coe x
  rw [← hreal] at hnorm ⊢
  simp_rw [← neg_eq_iff_eq_neg, ← ofReal_neg, ofReal_eq_one, neg_eq_iff_eq_neg]
  simpa [abs_eq] using hnorm

@[simp]
lemma angleDiff_neg (x : Circle) : angleDiff x (-x) = π := by
  simp only [angleDiff, coe_neg]
  obtain h | h | h := lt_trichotomy x.val.im 0
  · simp [x.val.arg_neg_eq_arg_add_pi_of_im_neg h, pi_pos.not_gt]
  · obtain rfl | rfl := (im_val_eq_zero_iff x).mp h <;> simp [pi_pos.not_ge, two_mul, pi_nonneg]
  simp only [x.val.arg_neg_eq_arg_sub_pi_of_im_pos h, le_sub_self_iff, pi_pos.not_ge, ↓reduceIte]
  ring

@[simp]
lemma angleDiff_neg' (x : Circle) : angleDiff (-x) x = π := by
  nth_rw 2 [← neg_neg x]
  exact angleDiff_neg ..

noncomputable def fullPath (x : Circle) : Path x x :=
  (Path.segment x.val.arg <| x.val.arg + 2 * π).map exp.continuous
    |>.cast (by simp) (by simp)

lemma coe_fullPath (x : Circle) : (fullPath x : _ → _) =
    exp ∘ ⇑(Path.segment x.val.arg (x.val.arg + 2 * π)) := by
  ext t
  simp [fullPath]

lemma fullPath_eq_path_trans_path (x : Circle) :fullPath x = (path x (-x)).trans (path (-x) x) := by
  ext t
  simp only [fullPath, Path.cast_coe, Path.map_coe, comp_apply, Path.segment_apply, coe_exp,
    Path.trans_apply, one_div, path_apply, angleDiff_neg, coe_neg]
  split_ifs with hle <;> simp only [coe_exp]
  · congr 3
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    ring
  obtain h1 | h2 : (x.val.im < 0 ∨ x.val.im = 0 ∧ 0 < x.val.re) ∨
      (0 < x.val.im ∨ x.val.im = 0 ∧ x.val.re < 0) := by
    have : x.val.re ≠ 0 ∨ x.val.im ≠ 0 := by_contra fun h ↦ coe_ne_zero x <| Complex.ext_iff.mpr
      (by tauto)
    grind
  · congr 3
    conv_rhs => exact Path.segment_apply (-x.val).arg ..
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul, vadd_eq_add,
      angleDiff_neg', add_sub_cancel_right, x.val.arg_neg_eq_arg_add_pi_iff.mpr h1]
    ring
  conv_rhs => apply (mul_one _).symm
  rw [← exp_two_pi_mul_I, ← Complex.exp_add]
  congr 3
  conv_rhs => left; left; args; exact Path.segment_apply ..
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul, vadd_eq_add,
    ofReal_add, ofReal_mul, ofReal_ofNat, angleDiff_neg', add_sub_cancel, sub_sub_cancel,
    ofReal_sub, ofReal_one, x.val.arg_neg_eq_arg_sub_pi_iff.mpr h2]
  ring

-- lemma fullPath_injOn_Ico (x : Circle) : InjOn (fullPath x) (Ico 0 1) := by
--   sorry

end Circle

open unitInterval AddCircle

variable {α : Type*} [TopologicalSpace α] {x : α} {C : Set α}

noncomputable def Path.ofCircle (f : C(Circle, α)) : Path (f 1) (f 1) where
  toFun := fun t ↦ f (homeomorphCircle (T := 1) (by simp) t)
  source' := by simp [homeomorphCircle_apply]
  target' := by
    trans f ((homeomorphCircle (by simp : (1 : ℝ) ≠ 0)) 0)
    · congr 2
      simp
    simp [homeomorphCircle_apply]

private lemma circleParam_bijOn :
    BijOn (Path.ofCircle (ContinuousMap.id Circle)) (Ico 0 1) univ := by
  refine ⟨mapsTo_univ _ _, fun s hs t ht hst ↦ ?_, fun z _ ↦ ?_⟩
  · change (homeomorphCircle (T := 1) _) (s : ℝ) = (homeomorphCircle (T := 1) _) (t : ℝ) at hst
    exact Subtype.ext <| (coe_eq_coe_iff_of_mem_Ico ⟨s.prop.1, by grind⟩ ⟨t.prop.1, by grind⟩).mp
      <| (homeomorphCircle (T := 1) (by simp)).injective hst
  obtain ⟨t, ht, heq⟩ := eq_coe_Ico ((homeomorphCircle (T := 1) (by simp)).symm z)
  refine ⟨⟨t, ht.1, ht.2.le⟩, ⟨ht.1, ht.2⟩, ?_⟩
  change homeomorphCircle (T := 1) _ (t : AddCircle (1 : ℝ)) = z
  rw [heq, Homeomorph.apply_symm_apply]

noncomputable def Path.onCircle (P : Path x x) : C(Circle, α) where
  toFun := liftIco 1 0 P.extend ∘ (homeomorphCircle (T := 1) (by norm_num)).symm
  continuous_toFun :=
    (liftIco_zero_continuous (by simp) P.continuous_extend.continuousOn).comp
      (Homeomorph.continuous _)

private lemma onCircle_apply_of_lt (P : Path x x) (t : I) (ht : t < 1) :
    P.onCircle (Path.ofCircle (ContinuousMap.id Circle) t) = P t := by
  change liftIco 1 0 P.extend ((homeomorphCircle (T := 1) _).symm
    ((homeomorphCircle (T := 1) _) (t : ℝ))) = P t
  rw [Homeomorph.symm_apply_apply,
    liftIco_zero_coe_apply (p := (1 : ℝ)) ⟨t.property.1, ht⟩, P.extend_extends']

/-- Descending a loop to the circle recovers its values along the standard parametrization. -/
lemma Path.onCircle_apply (P : Path x x) (t : I) :
    P.onCircle (Path.ofCircle (ContinuousMap.id Circle) t) = P t := by
  obtain rfl | ht := eq_or_lt_of_le (show t ≤ 1 from t.property.2)
  · have hends := (Path.ofCircle (ContinuousMap.id Circle)).target.trans
      (Path.ofCircle (ContinuousMap.id Circle)).source.symm
    rw [hends, onCircle_apply_of_lt P 0 (by simp)]
    exact P.source.trans P.target.symm
  exact onCircle_apply_of_lt P t ht

@[simp]
lemma Path.range_onCircle (P : Path x x) : range (Path.onCircle P) = range P := by
  rw [← circleParam_bijOn.surjOn.surjective.range_comp P.onCircle]
  congr 1
  exact funext P.onCircle_apply

@[simp]
lemma Path.onCircle_ofCircle (f : C(Circle, α)) : (Path.ofCircle f).onCircle = f := by
  ext z
  obtain ⟨t, rfl⟩ := circleParam_bijOn.surjOn.surjective z
  exact (Path.ofCircle f).onCircle_apply t

@[simp]
lemma Path.ofCircle_onCircle_toFun (P : Path x x) : ⇑(Path.ofCircle P.onCircle) = ⇑P :=
  funext P.onCircle_apply

lemma Path.onCircle_injective {P : Path x x} (hP : InjOn P (Ico 0 1)) :
    Injective (Path.onCircle P) := by
  intro a b hab
  obtain ⟨s, hs, rfl⟩ := circleParam_bijOn.surjOn (mem_univ a)
  obtain ⟨t, ht, rfl⟩ := circleParam_bijOn.surjOn (mem_univ b)
  rw [P.onCircle_apply, P.onCircle_apply] at hab
  exact congrArg (Path.ofCircle (ContinuousMap.id Circle)) (hP hs ht hab)

@[simp]
lemma Path.range_ofCircle (f : C(Circle, α)) : range (Path.ofCircle f) = range f := by
  conv_rhs => rw [← Path.onCircle_ofCircle f]
  rw [Path.range_onCircle]

lemma Path.ofCircle_injOn (f : C(Circle, α)) (hf : Injective f) :
    InjOn (Path.ofCircle f) (Ico 0 1) :=
  hf.injOn.comp circleParam_bijOn.injOn circleParam_bijOn.mapsTo

/-- Simple-loop witnesses and injective continuous circle-map witnesses have the same ranges. -/
lemma exists_isSimpleLoop_iff_exists_injective_circle_map :
    (∃ x, ∃ P : Path x x, P.IsSimpleLoop ∧ range P = C) ↔
      ∃ f : C(Circle, α), Injective f ∧ range f = C := by
  constructor
  · rintro ⟨x, P, hP, rfl⟩
    exact ⟨P.onCircle, P.onCircle_injective hP, P.range_onCircle⟩
  rintro ⟨f, hf, rfl⟩
  exact ⟨f 1, Path.ofCircle f, Path.ofCircle_injOn f hf, Path.range_ofCircle f⟩

/-- Rotate a loop's circle parametrization so that it starts at `P t`. This construction
preserves the full parametrization when the cut is at either endpoint. -/
noncomputable def Path.rebase (P : Path x x) (t : I) : Path (P t) (P t) :=
  let g := P.onCircle.comp
    ⟨_, (Homeomorph.mulRight (Path.ofCircle (ContinuousMap.id Circle) t)).continuous⟩
  (Path.ofCircle g).cast
    (by simpa [g] using (P.onCircle_apply t).symm)
    (by simpa [g] using (P.onCircle_apply t).symm)

lemma Path.rebase_apply (P : Path x x) (t s : I) :
    P.rebase t s = P.onCircle (Path.ofCircle (ContinuousMap.id Circle) s *
      Path.ofCircle (ContinuousMap.id Circle) t) := rfl

lemma Path.onCircle_rebase_apply (P : Path x x) (t : I) (z : Circle) :
    (P.rebase t).onCircle z =
      P.onCircle (z * Path.ofCircle (ContinuousMap.id Circle) t) := by
  obtain ⟨s, rfl⟩ := circleParam_bijOn.surjOn.surjective z
  rw [Path.onCircle_apply, Path.rebase_apply]

@[simp]
lemma Path.range_rebase (P : Path x x) (t : I) : range (P.rebase t) = range P := by
  simp only [Path.rebase, Path.cast_coe, Path.range_ofCircle]
  exact (EquivLike.range_comp ..).trans P.range_onCircle

@[simp]
lemma Path.isSimpleLoop_rebase_iff (P : Path x x) (t : I) :
    (P.rebase t).IsSimpleLoop ↔ P.IsSimpleLoop := by
  constructor
  · intro h
    have hinj := Path.onCircle_injective h
    have heq : ⇑(P.rebase t).onCircle =
        P.onCircle ∘ Homeomorph.mulRight (Path.ofCircle (ContinuousMap.id Circle) t) :=
      funext (P.onCircle_rebase_apply t)
    rw [heq] at hinj
    have hP : Injective P.onCircle := (EquivLike.injective_comp ..).mp hinj
    simpa only [Path.IsSimpleLoop, Path.ofCircle_onCircle_toFun] using
      Path.ofCircle_injOn P.onCircle hP
  intro hP
  unfold Path.rebase Path.IsSimpleLoop
  simp only [Path.cast_coe]
  apply Path.ofCircle_injOn
  exact (EquivLike.injective_comp ..).mpr (Path.onCircle_injective hP)

lemma Path.IsSimpleLoop.rebase {P : Path x x} (hP : P.IsSimpleLoop) (t : I) :
    (P.rebase t).IsSimpleLoop :=
  (P.isSimpleLoop_rebase_iff t).mpr hP

@[simp]
lemma Path.rebase_zero (P : Path x x) : P.rebase 0 = P.cast P.source P.source := by
  ext s
  rw [Path.rebase_apply, (Path.ofCircle (ContinuousMap.id Circle)).source]
  simpa only [ContinuousMap.id_apply, mul_one, Path.cast_coe] using P.onCircle_apply s

@[simp]
lemma Path.rebase_one (P : Path x x) : P.rebase 1 = P.cast P.target P.target := by
  ext s
  rw [Path.rebase_apply, (Path.ofCircle (ContinuousMap.id Circle)).target]
  simpa only [ContinuousMap.id_apply, mul_one, Path.cast_coe] using P.onCircle_apply s
