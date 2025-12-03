import Matroid.Connectivity.Separation
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Matroid.Constructions
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.ForMathlib.Tactic.TautoSet
import Mathlib.Tactic.Peel


lemma add_one_add_one {R : Type*} [AddMonoidWithOne R] (a : R) : (a + 1) + 1 = a + 2 := by
  rw [add_assoc, one_add_one_eq_two]

lemma ENat.eq_zero_or_exists_eq_add_one (a : ℕ∞) : a = 0 ∨ ∃ b, a = b + 1 := by
  obtain (a | a | a) := a
  · exact .inr ⟨⊤, rfl⟩
  · exact .inl rfl
  exact .inr ⟨a, rfl⟩

open Set Matroid.Partition

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b d k : ℕ∞} {A X Y : Set α} {P : M.Partition}

namespace Matroid

variable {dg dg' dg_l dg_r : Matroid α → Set α → Prop}

namespace Partition

/-! ### Abstract Separations -/

/-- An abstract notion of nondegenerate separation : given a predicate on sets in `M`,
`P.IsPredSeparation` means that neither side of `P` satisfies the degeneracy predicate. -/
@[mk_iff]
structure IsPredSeparation (degen_left degen_right : Matroid α → Set α → Prop)
    (P : M.Partition) :  Prop where
    not_degen_left : ¬ degen_left M P.left
    not_degen_right : ¬ degen_right M P.right

lemma IsPredSeparation.dual (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M✶ X)
    (hP : P.IsPredSeparation dg dg) : P.dual.IsPredSeparation dg' dg' :=
  ⟨fun h ↦ hP.not_degen_left (by simpa using hdg (M := M✶) P.left_subset_ground h),
    fun h ↦ hP.not_degen_right (by simpa using hdg (M := M✶) P.right_subset_ground h)⟩

lemma IsPredSeparation.dual_compl (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M✶ (M.E \ X))
    (hP : P.IsPredSeparation dg dg) : P.dual.IsPredSeparation dg' dg' :=
  ⟨fun h ↦ hP.not_degen_right <| by simpa using hdg (M := M✶) P.left_subset_ground h,
    fun h ↦ hP.not_degen_left <| by simpa using hdg (M := M✶) P.right_subset_ground h⟩

lemma IsPredSeparation.of_dual (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg M X → dg M✶ X)
    (hP : P.dual.IsPredSeparation dg dg) : P.IsPredSeparation dg dg :=
  ⟨by simpa using (hP.dual hdg).1, by simpa using (hP.dual hdg).2⟩

lemma isPredSeparation_dual_iff (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg M X → dg M✶ X) :
    P.dual.IsPredSeparation dg dg ↔ P.IsPredSeparation dg dg :=
  ⟨IsPredSeparation.of_dual hdg, IsPredSeparation.dual hdg⟩

lemma isPredSeparation_ofDual_iff {P : M✶.Partition} (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg M X → dg M✶ X) :
    P.ofDual.IsPredSeparation dg dg ↔ P.IsPredSeparation dg dg := by
  rw [← isPredSeparation_dual_iff hdg, ofDual_dual]

lemma IsPredSeparation.symm (hP : P.IsPredSeparation dg dg') : P.symm.IsPredSeparation dg' dg :=
  ⟨hP.2, hP.1⟩

lemma IsPredSeparation.of_symm (hP : P.symm.IsPredSeparation dg dg') : P.IsPredSeparation dg' dg :=
  ⟨hP.2, hP.1⟩

lemma isPredSeparation_symm_eq : P.symm.IsPredSeparation dg dg'= P.IsPredSeparation dg' dg := by
  ext
  exact ⟨IsPredSeparation.of_symm, IsPredSeparation.symm⟩

lemma isPredSeparation_symm_iff : P.symm.IsPredSeparation dg dg' ↔ P.IsPredSeparation dg' dg :=
  ⟨IsPredSeparation.of_symm, IsPredSeparation.symm⟩

lemma IsPredSeparation.mono {dg dg' : Matroid α → Set α → Prop}
    (h_imp : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M X) (hP : P.IsPredSeparation dg dg) :
    P.IsPredSeparation dg' dg' :=
  ⟨fun h ↦ hP.not_degen_left <| h_imp P.left_subset_ground h,
    fun h ↦ hP.not_degen_right <| h_imp P.right_subset_ground h⟩

lemma IsPredSeparation.mono_symm {dg dg' : Matroid α → Set α → Prop}
    (h_imp : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M (M.E \ X)) (hP : P.IsPredSeparation dg dg) :
    P.IsPredSeparation dg' dg' := by
  simpa [isPredSeparation_iff] using (hP.mono (dg' := fun M X ↦ dg' M (M.E \ X))
    (fun M X hX h' ↦ diff_diff_cancel_left hX ▸ h_imp diff_subset h')).symm

/- If degeneracy is monotone under taking subsets and minors, then a separation in a minor
-- gives a separation in the matroid. -/
-- lemma IsPredSeparation.of_minor {dg} {N M : Matroid α} {Q : N.Partition} {P : M.Partition}
--     (hNM : N ≤m M) (h_mono : ∀ ⦃M X Y⦄, dg M X → Y ⊆ X → dg M Y)
--     (h_minor : ∀ ⦃N M X⦄, N ≤m M → X ⊆ N.E → dg M X → dg N X)
--     (hQ : Q.IsPredSeparation dg dg) (subset_left : Q.1 ⊆ P.1) (subset_right : Q.2 ⊆ P.2) :
--     P.IsPredSeparation dg dg :=
--   ⟨fun hdg ↦ hQ.1 <| h_minor hNM Q.left_subset_ground <| h_mono hdg subset_left,
--     fun hdg ↦ hQ.2 <| h_minor hNM Q.right_subset_ground <| h_mono hdg subset_right⟩

/-! ### Tutte Separations -/

abbrev IsTutteSeparation (P : M.Partition) :=
    IsPredSeparation (fun M X ↦ M.Indep X ∧ M.Coindep X) (fun M X ↦ M.Indep X ∧ M.Coindep X) P

lemma isTutteSeparation_iff :
    P.IsTutteSeparation ↔ (M.Dep P.left ∨ M.Codep P.left) ∧ (M.Dep P.right ∨ M.Codep P.right) := by
  simp [IsTutteSeparation, isPredSeparation_iff, imp_iff_not_or]

lemma isTutteSeparation_iff' : P.IsTutteSeparation ↔
    (M.Dep P.left ∨ M.Nonspanning P.right) ∧ (M.Dep P.right ∨ M.Nonspanning P.left) := by
  rw [isTutteSeparation_iff, P.codep_left_iff, P.codep_right_iff]

@[simp]
lemma isTutteSeparation_dual_iff : P.dual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_dual_iff <| by simp [and_comm]

alias ⟨IsTutteSeparation.of_dual, IsTutteSeparation.dual⟩ := isTutteSeparation_dual_iff

@[simp]
lemma isTutteSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_ofDual_iff <| by simp [and_comm]

@[simp]
lemma isTutteSeparation_symm_iff : P.symm.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_symm_iff

lemma IsTutteSeparation.symm (h : P.IsTutteSeparation) : P.symm.IsTutteSeparation :=
  IsPredSeparation.symm h

lemma IsTutteSeparation.codep_of_indep_left (hP : P.IsTutteSeparation) (hi : M.Indep P.1) :
    M.Codep P.1 := by
  by_contra hcon
  simp [IsTutteSeparation, isPredSeparation_iff, hi, hcon] at hP

lemma IsTutteSeparation.codep_of_indep_right (hP : P.IsTutteSeparation) (hi : M.Indep P.2) :
    M.Codep P.2 :=
  hP.symm.codep_of_indep_left hi

lemma IsTutteSeparation.nonspanning_of_indep_left (hP : P.IsTutteSeparation) (hi : M.Indep P.1) :
    M.Nonspanning P.2 := by
  obtain ⟨hd : M.Codep P.left, -⟩ := by simpa [IsTutteSeparation, isPredSeparation_iff, hi] using hP
  rwa [← P.codep_left_iff]

lemma IsTutteSeparation.nonspanning_of_indep_right (hP : P.IsTutteSeparation) (hi : M.Indep P.2) :
    M.Nonspanning P.1 :=
  hP.symm.nonspanning_of_indep_left hi

lemma IsTutteSeparation.dep_of_spanning_left (hP : P.IsTutteSeparation) (hs : M.Spanning P.1) :
    M.Dep P.2 := by
  rw [← P.coindep_right_iff] at hs
  simpa using hP.dual.nonspanning_of_indep_right hs

lemma IsTutteSeparation.dep_of_spanning_right (hP : P.IsTutteSeparation) (hs : M.Spanning P.2) :
    M.Dep P.1 :=
  hP.symm.dep_of_spanning_left hs

lemma isTutteSeparation_iff_lt_encard (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ P.eConn < P.left.encard ∧ P.eConn < P.right.encard := by
  rw [← M.eConn_add_nullity_add_nullity_dual P.left, ← M.eConn_add_nullity_add_nullity_dual P.right]
  simp [add_assoc, hP, IsTutteSeparation, isPredSeparation_iff]

lemma isTutteSeparation_iff_add_one_le_encard (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ P.eConn + 1 ≤ P.left.encard ∧ P.eConn + 1 ≤ P.right.encard := by
  rw [isTutteSeparation_iff_lt_encard hP, ENat.add_one_le_iff hP, ENat.add_one_le_iff hP]

lemma isTutteSeparation_iff_nullity : P.IsTutteSeparation ↔
    1 ≤ M.nullity P.left + M✶.nullity P.left ∧ 1 ≤ M.nullity P.right + M✶.nullity P.right := by
  simp only [isTutteSeparation_iff, ENat.one_le_iff_ne_zero, ne_eq, add_eq_zero, nullity_eq_zero,
    not_and, dual_ground, Partition.left_subset_ground, not_indep_iff, dep_dual_iff,
    Partition.right_subset_ground]
  rw [← not_indep_iff, ← not_coindep_iff, ← not_coindep_iff, ← not_indep_iff]
  grind

lemma not_isTutteSeparation_iff : ¬ P.IsTutteSeparation ↔
    (M.Indep P.left ∧ M.Coindep P.left) ∨ (M.Indep P.right ∧ M.Coindep P.right) := by
  rw [isTutteSeparation_iff, ← not_indep_iff, ← not_coindep_iff, ← not_indep_iff, ← not_coindep_iff]
  tauto

lemma not_isTutteSeparation_iff' : ¬ P.IsTutteSeparation ↔
    (M.Indep P.left ∧ M.Spanning P.right) ∨ (M.Spanning P.left ∧ M.Indep P.right) := by
  rw [isTutteSeparation_iff', ← not_spanning_iff, ← not_indep_iff, ← not_spanning_iff,
    ← not_indep_iff]
  tauto

lemma isTutteSeparation_of_encard (h_left : P.eConn < P.left.encard)
    (h_right : P.eConn < P.right.encard) : P.IsTutteSeparation := by
  rwa [isTutteSeparation_iff_lt_encard (by intro h; simp [h] at h_left), and_iff_left h_right]

lemma IsTutteSeparation.nonempty_left (h : P.IsTutteSeparation) : P.left.Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro he
  refine (h.dep_of_spanning_right ?_).not_indep (by simp [he])
  rw [← compl_left, he, diff_empty]
  exact M.ground_spanning

lemma IsTutteSeparation.nonempty_right (h : P.IsTutteSeparation) : P.right.Nonempty :=
  h.symm.nonempty_left

lemma IsTutteSeparation.left_ssubset (h : P.IsTutteSeparation) : P.left ⊂ M.E := by
  refine P.left_subset_ground.eq_or_ssubset.elim (fun h_eq ↦ (h.nonempty_right.ne_empty ?_).elim) id
  rw [← compl_left, h_eq, diff_eq_empty]

lemma IsTutteSeparation.right_ssubset (h : P.IsTutteSeparation) : P.right ⊂ M.E :=
  h.symm.left_ssubset

lemma IsTutteSeparation.exists_of_indep_left (h : P.IsTutteSeparation) (hi : M.Indep P.left) :
    ∃ Q : M.Partition, Q.IsTutteSeparation ∧ Q.left ⊆ P.left ∧
      M.IsCocircuit Q.left ∧ Q.eConn ≤ P.eConn := by
  obtain ⟨C, hCP, hC⟩ := (h.codep_of_indep_left hi).exists_isCocircuit_subset
  refine ⟨M.partition C, ?_, hCP, hC, ?_⟩
  · rw [Partition.isTutteSeparation_iff, partition_left .., partition_right ..,
      and_iff_right (.inr hC.codep), codep_compl_iff, ← not_spanning_iff, ← imp_iff_or_not]
    intro hCs
    obtain rfl : C = P.left := hi.eq_of_spanning_subset hCs hCP
    simp [h.dep_of_spanning_left hCs]
  grw [← Partition.eConn_left, partition_left .., (hi.subset hCP).eConn_eq, ← P.eConn_left,
    hi.eConn_eq]
  exact M✶.eRk_mono hCP

/-! ### Vertical Separations -/

/-- A vertical separation is one with both sides nonspanning. -/
abbrev IsVerticalSeparation (P : M.Partition) : Prop :=
  IsPredSeparation Matroid.Coindep Matroid.Coindep P

@[simp]
lemma isVerticalSeparation_symm_iff : P.symm.IsVerticalSeparation ↔ P.IsVerticalSeparation :=
  isPredSeparation_symm_iff

lemma IsVerticalSeparation.symm (hP : P.IsVerticalSeparation) : P.symm.IsVerticalSeparation :=
  IsPredSeparation.symm hP

lemma IsVerticalSeparation.of_symm (hP : P.symm.IsVerticalSeparation) : P.IsVerticalSeparation :=
  IsPredSeparation.symm hP

lemma IsVerticalSeparation.isTutteSeparation (h : P.IsVerticalSeparation) :
    P.IsTutteSeparation :=
  h.mono fun _ _ _ ↦ And.right

lemma isVerticalSeparation_iff : P.IsVerticalSeparation ↔ M.Codep P.left ∧ M.Codep P.right := by
  simp [IsVerticalSeparation, isPredSeparation_iff]

lemma isVerticalSeparation_iff_nonspanning :
    P.IsVerticalSeparation ↔ M.Nonspanning P.left ∧ M.Nonspanning P.right := by
  rw [isVerticalSeparation_iff, P.codep_left_iff, P.codep_right_iff, and_comm]

lemma not_isVerticalSeparation_iff :
    ¬ P.IsVerticalSeparation ↔ M.Coindep P.left ∨ M.Coindep P.right := by
  simp only [IsVerticalSeparation, isPredSeparation_iff, dual_ground, Partition.left_subset_ground,
    not_indep_iff, dep_dual_iff, Partition.right_subset_ground, not_and, not_codep_right_iff]
  rw [← not_coindep_iff]
  tauto

lemma not_isVerticalSeparation_iff' :
    ¬ P.IsVerticalSeparation ↔ M.Spanning P.left ∨ M.Spanning P.right := by
  rw [not_isVerticalSeparation_iff, coindep_left_iff, coindep_right_iff, or_comm]

lemma IsVerticalSeparation.nonspanning_left (h : P.IsVerticalSeparation) : M.Nonspanning P.left :=
  (isVerticalSeparation_iff_nonspanning.1 h).1

lemma IsVerticalSeparation.nonspanning_right (h : P.IsVerticalSeparation) : M.Nonspanning P.right :=
  (isVerticalSeparation_iff_nonspanning.1 h).2

lemma IsVerticalSeparation.codep_left (h : P.IsVerticalSeparation) : M.Codep P.left :=
  P.codep_left_iff.2 h.nonspanning_right

lemma IsVerticalSeparation.codep_right (h : P.IsVerticalSeparation) : M.Codep P.right :=
  h.symm.codep_left

lemma isVerticalSeparation_iff_eRk (h : P.eConn ≠ ⊤) :
    P.IsVerticalSeparation ↔ P.eConn < M.eRk P.left ∧ P.eConn < M.eRk P.right := by
  simp [IsVerticalSeparation, isPredSeparation_iff, ← M.eConn_add_nullity_dual_eq_eRk P.left,
    ← M.eConn_add_nullity_dual_eq_eRk P.right, h, ← nonspanning_compl_iff, and_comm]

lemma isVerticalSeparation_iff_nullity_dual :
    P.IsVerticalSeparation ↔ 1 ≤ M✶.nullity P.left ∧ 1 ≤ M✶.nullity P.right := by
  simp [ENat.one_le_iff_ne_zero, isVerticalSeparation_iff_nonspanning, Partition.codep_left_iff,
    Partition.codep_right_iff, and_comm]

lemma isVerticalSeparation_of_lt_lt (h_left : P.eConn < M.eRk P.left)
    (h_right : P.eConn < M.eRk P.right) : P.IsVerticalSeparation := by
  rwa [isVerticalSeparation_iff_eRk (fun h ↦ by simp [h] at h_left), and_iff_left h_right]

lemma IsVerticalSeparation.eRk_left_ge (h : P.IsVerticalSeparation) :
    P.eConn + 1 ≤ M.eRk P.left := by
  grw [← M.eConn_add_nullity_dual_eq_eRk P.left, h.codep_left.one_le_nullity, P.eConn_left]

lemma IsVerticalSeparation.eRk_right_ge (h : P.IsVerticalSeparation) :
    P.eConn + 1 ≤ M.eRk P.right :=
  P.eConn_symm ▸ h.symm.eRk_left_ge

/-! ### Cyclic Separations -/

/-- A cyclic separation is one with both sides dependent. -/
abbrev IsCyclicSeparation (P : M.Partition) : Prop := IsPredSeparation Matroid.Indep Matroid.Indep P

@[simp]
lemma isCyclicSeparation_symm_iff : P.symm.IsCyclicSeparation ↔ P.IsCyclicSeparation :=
  isPredSeparation_symm_iff

alias ⟨IsCyclicSeparation.of_symm, IsCyclicSeparation.symm⟩ := isCyclicSeparation_symm_iff

lemma IsVerticalSeparation.dual (h : P.IsVerticalSeparation) : P.dual.IsCyclicSeparation :=
  IsPredSeparation.dual (by simp) h

lemma IsCyclicSeparation.dual (h : P.IsCyclicSeparation) : P.dual.IsVerticalSeparation :=
  IsPredSeparation.dual (by simp) h

lemma IsCyclicSeparation.isTutteSeparation (h : P.IsCyclicSeparation) :
    P.IsTutteSeparation :=
  h.dual.isTutteSeparation.of_dual

lemma isCyclicSeparation_iff : P.IsCyclicSeparation ↔ M.Dep P.left ∧ M.Dep P.right := by
  simp [IsCyclicSeparation, isPredSeparation_iff]

lemma IsCyclicSeparation.dep_left (h : P.IsCyclicSeparation) : M.Dep P.left :=
  (isCyclicSeparation_iff.1 h).1

lemma IsCyclicSeparation.dep_right (h : P.IsCyclicSeparation) : M.Dep P.right :=
  (isCyclicSeparation_iff.1 h).2

@[simp]
lemma isCyclicSeparation_dual_iff : P.dual.IsCyclicSeparation ↔ P.IsVerticalSeparation := by
  simp [isCyclicSeparation_iff, isVerticalSeparation_iff_nonspanning, ← nonspanning_compl_iff,
    and_comm]

@[simp]
lemma isVerticalSeparation_dual_iff : P.dual.IsVerticalSeparation ↔ P.IsCyclicSeparation := by
  simp [isCyclicSeparation_iff, isVerticalSeparation_iff_nonspanning, nonspanning_dual_iff,
    and_comm]

@[simp]
lemma isCyclicSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsCyclicSeparation ↔ P.IsVerticalSeparation := by
  rw [← isVerticalSeparation_dual_iff, ofDual_dual]

@[simp]
lemma isVerticalSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsVerticalSeparation ↔ P.IsCyclicSeparation := by
  rw [← isCyclicSeparation_dual_iff, ofDual_dual]

lemma isCyclicSeparation_iff_eRk_dual (h : P.eConn ≠ ⊤) :
    P.IsCyclicSeparation ↔ P.eConn < M✶.eRk P.left ∧ P.eConn < M✶.eRk P.right := by
  rw [← isVerticalSeparation_dual_iff, isVerticalSeparation_iff_eRk (by simpa), P.eConn_dual]
  rfl

lemma isCyclicSeparation_iff_nullity :
    P.IsCyclicSeparation ↔ 1 ≤ M.nullity P.left ∧ 1 ≤ M.nullity P.right := by
  simp [ENat.one_le_iff_ne_zero, isCyclicSeparation_iff]

lemma not_isCyclicSeparation_iff : ¬ P.IsCyclicSeparation ↔ M.Indep P.left ∨ M.Indep P.right := by
  simp only [IsCyclicSeparation, isPredSeparation_iff, Partition.left_subset_ground, not_indep_iff,
    Partition.right_subset_ground, not_and, not_dep_iff]
  rw [← not_indep_iff]
  tauto

lemma IsCyclicSeparation.eRk_dual_left_ge (h : P.IsCyclicSeparation) :
    P.eConn + 1 ≤ M✶.eRk P.left := by
  grw [← M.eConn_add_nullity_eq_eRk_dual P.left, P.eConn_left, h.dep_left.one_le_nullity]

lemma IsCyclicSeparation.eRk_dual_right_ge (h : P.IsCyclicSeparation) :
    P.eConn + 1 ≤ M✶.eRk P.right :=
  P.eConn_symm ▸ h.symm.eRk_dual_left_ge

/-! ### Strong Separations -/

/-- A strong separation is one where both sides are dependent and nonspanning. -/
abbrev IsStrongSeparation (P : M.Partition) : Prop :=
  IsPredSeparation (fun M X ↦ M.Indep X ∨ M.Coindep X) (fun M X ↦ M.Indep X ∨ M.Coindep X) P

@[simp]
lemma isStrongSeparation_symm_iff : P.symm.IsStrongSeparation ↔ P.IsStrongSeparation :=
  isPredSeparation_symm_iff

alias ⟨IsStrongSeparation.of_symm, IsStrongSeparation.symm⟩ := isStrongSeparation_symm_iff

@[simp]
lemma isStrongSeparation_dual_iff : P.dual.IsStrongSeparation ↔ P.IsStrongSeparation :=
  isPredSeparation_dual_iff <| by simp [or_comm]

@[simp]
lemma isStrongSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsStrongSeparation ↔ P.IsStrongSeparation := by
  rw [← isStrongSeparation_dual_iff, ofDual_dual]

alias ⟨IsStrongSeparation.of_dual, IsStrongSeparation.dual⟩ := isStrongSeparation_dual_iff

lemma IsStrongSeparation.isCyclicSeparation (h : P.IsStrongSeparation) : P.IsCyclicSeparation :=
  h.mono <| by simp +contextual

lemma IsStrongSeparation.isVerticalSeparation (h : P.IsStrongSeparation) :
    P.IsVerticalSeparation := by
  simpa using h.dual.isCyclicSeparation

lemma IsStrongSeparation.isTutteSeparation (h : P.IsStrongSeparation) : P.IsTutteSeparation :=
  h.isVerticalSeparation.isTutteSeparation

lemma isStrongSeparation_iff : P.IsStrongSeparation ↔
    M.Dep P.left ∧ M.Codep P.left ∧ M.Dep P.right ∧ M.Codep P.right := by
  simp [IsStrongSeparation, isPredSeparation_iff, and_assoc]

lemma isStrongSeparation_iff' : P.IsStrongSeparation ↔
    M.Dep P.left ∧ M.Dep P.right ∧ M.Nonspanning P.left ∧ M.Nonspanning P.right := by
  rw [isStrongSeparation_iff, P.codep_left_iff, P.codep_right_iff]
  tauto

lemma IsStrongSeparation.dep_left (h : P.IsStrongSeparation) : M.Dep P.left :=
  h.isCyclicSeparation.dep_left

lemma IsStrongSeparation.dep_right (h : P.IsStrongSeparation) : M.Dep P.right :=
  h.isCyclicSeparation.dep_right

lemma IsStrongSeparation.codep_left (h : P.IsStrongSeparation) : M.Codep P.left :=
  h.isVerticalSeparation.codep_left

lemma IsStrongSeparation.codep_right (h : P.IsStrongSeparation) : M.Codep P.right :=
  h.isVerticalSeparation.codep_right

lemma IsStrongSeparation.encard_left_ge (h : P.IsStrongSeparation) :
    P.eConn + 2 ≤ P.left.encard := by
  grw [← P.eConn_left, ← M.eConn_add_nullity_add_nullity_dual P.left, add_assoc,
    ← h.dep_left.one_le_nullity, ← h.codep_left.one_le_nullity, one_add_one_eq_two]

lemma IsStrongSeparation.encard_right_ge (h : P.IsStrongSeparation) :
    P.eConn + 2 ≤ P.right.encard :=
  P.eConn_symm ▸ h.symm.encard_left_ge

lemma isStrongSeparation_iff_eRk (hP : P.eConn ≠ ⊤) : P.IsStrongSeparation ↔
    P.eConn < M.eRk P.left ∧ P.eConn < M.eRk P.right ∧
    P.eConn < M✶.eRk P.left ∧ P.eConn < M✶.eRk P.right := by
  rw [← M.eConn_add_nullity_dual_eq_eRk P.left, ← M.eConn_add_nullity_dual_eq_eRk P.right,
    ← M.eConn_add_nullity_eq_eRk_dual P.left, ← M.eConn_add_nullity_eq_eRk_dual P.right,
    P.eConn_left, P.eConn_right]
  grind [ENat.lt_add_left_iff, not_false_eq_true, nullity_eq_zero, dual_ground,
    Partition.left_subset_ground, not_indep_iff, dep_dual_iff,
    Partition.right_subset_ground, isStrongSeparation_iff]

-- lemma IsTutteSeparation.isStrong_separation_or_small (h : P.IsTutteSeparation)
--     (hPconn : P.eConn ≠ ⊤) :
--     P.IsStrongSeparation ∨
--       (M.eRk P.left ≤ P.eConn ∨ M.eRk P.right ≤ P.eConn ∨
--       M✶.eRk P.left ≤ P.eConn ∨ M✶.eRk P.right ≤ P.eConn)


-- lemma IsTutte (hP : P.eConn = 0) :
--     P.IsTutteSeparation ↔ P.IsStrongSeparation ∨ (P.left.Nonempty ∧ P.right.Nonempty ∧
--       (M.eRk P.left = P.eConn ∨ P.left ⊆ M.coloops ∨ P.right ⊆ M.loops ∨ P.right ⊆ M.coloops))

/-- A Tutte separation with connectivity zero is either a strong separation, or has one side
only loops or coloops. -/
lemma isTutteSeparation_iff_isStrongSeparation_of_zero (hP : P.eConn = 0) :
    P.IsTutteSeparation ↔ P.IsStrongSeparation ∨ (P.left.Nonempty ∧ P.right.Nonempty ∧
      (P.left ⊆ M.loops ∨ P.left ⊆ M.coloops ∨ P.right ⊆ M.loops ∨ P.right ⊆ M.coloops)) := by
  rw [isStrongSeparation_iff_eRk (by simp [hP]), isTutteSeparation_iff_lt_encard (by simp [hP]),
    hP, ← not_iff_not]
  simp only [← not_le, nonpos_iff_eq_zero, encard_eq_zero, not_and, not_not,
    Partition.left_subset_ground, eRk_eq_zero_iff, Partition.right_subset_ground, dual_ground,
    dual_loops, nonempty_iff_ne_empty]
  by_cases h : P.left = ∅ <;> grind

/-- An internal separation is the type of separation required by internal connectivity.
For finite connectivity, is it equivalent to both sides of the separation having cardinality
exceeding the connectivity by at least two. -/
def IsInternalSeparation (P : M.Partition) := P.IsPredSeparation
  (fun M X ↦ M.nullity X + M✶.nullity X ≤ 1) (fun M X ↦ M.nullity X + M✶.nullity X ≤ 1)

lemma isInternalSeparation_iff : P.IsInternalSeparation ↔
    1 < M.nullity P.left + M✶.nullity P.left ∧ 1 < M.nullity P.right + M✶.nullity P.right := by
  simp [IsInternalSeparation, isPredSeparation_iff]

lemma IsStrongSeparation.isInternalSeparation (h : P.IsStrongSeparation) :
    P.IsInternalSeparation := by
  refine IsPredSeparation.mono (fun N X hX hle ↦ ?_) h
  rw [← nullity_eq_zero, coindep_def, ← nullity_eq_zero]
  enat_to_nat!; omega

lemma isInternalSeparation_iff_encard (hP : P.eConn ≠ ⊤) :
    P.IsInternalSeparation ↔ P.eConn + 1 < P.left.encard ∧ P.eConn + 1 < P.right.encard := by
  rw [← M.eConn_add_nullity_add_nullity_dual P.left, P.eConn_left, add_assoc,
    ← M.eConn_add_nullity_add_nullity_dual P.right, P.eConn_right, add_assoc,
    WithTop.add_lt_add_iff_left hP, WithTop.add_lt_add_iff_left hP,
    IsInternalSeparation, isPredSeparation_iff, not_le, not_le]

lemma IsInternalSeparation.isTutteSeparation (h : P.IsInternalSeparation) :
    P.IsTutteSeparation := by
  rw [isTutteSeparation_iff_nullity]
  rw [isInternalSeparation_iff] at h
  exact ⟨h.1.le, h.2.le⟩

lemma IsInternalSeparation.encard_eq_or_eq_of_not_isTutteSeparation (h : P.IsInternalSeparation)
    (h_not : ¬ P.IsTutteSeparation) :
    P.left.encard = P.eConn + 1 ∨ P.right.encard = P.eConn + 1 := by
  obtain htop | hne := eq_or_ne P.eConn ⊤
  · rw [← M.eConn_add_nullity_add_nullity_dual P.left, P.eConn_left]
    simp [htop]
  simp [isTutteSeparation_iff_lt_encard hne] at h_not
  rw [isInternalSeparation_iff_encard hne] at h
  grw [← h_not (le_self_add.trans_lt h.1)] at h
  exact (h.2.not_ge le_self_add).elim
  -- enat_to_nat is again being weird here.

lemma IsInternalSeparation.encard_left_ge (hP : P.IsInternalSeparation) :
    P.eConn + 1 + 1 ≤ P.left.encard := by
  grw [← M.eConn_add_nullity_add_nullity_dual P.left, P.eConn_left]
  rw [isInternalSeparation_iff] at hP
  obtain ⟨hP1, hP2⟩ := hP
  eomega

lemma IsInternalSeparation.encard_right_ge (hP : P.IsInternalSeparation) :
    P.eConn + 1 + 1 ≤ P.right.encard := by
  simpa using IsInternalSeparation.encard_left_ge hP.symm

lemma IsInternalSeparation.symm (hP : P.IsInternalSeparation) : P.symm.IsInternalSeparation :=
  IsPredSeparation.symm hP

lemma IsInternalSeparation.dual (hP : P.IsInternalSeparation) : P.dual.IsInternalSeparation :=
  IsPredSeparation.dual (by simp +contextual [add_comm]) hP

lemma IsInternalSeparation.of_dual (hP : P.dual.IsInternalSeparation) : P.IsInternalSeparation :=
  IsPredSeparation.of_dual (by simp +contextual [add_comm]) hP

@[simp]
lemma isInternalSeparation_dual_iff : P.dual.IsInternalSeparation ↔ P.IsInternalSeparation :=
  ⟨IsInternalSeparation.of_dual, IsInternalSeparation.dual⟩

@[simp]
lemma isInternalSeparation_symm_iff : P.symm.IsInternalSeparation ↔ P.IsInternalSeparation :=
  ⟨IsInternalSeparation.symm, IsInternalSeparation.symm⟩

end Partition

lemma Dep.partition_isTutteSeparation_of_nonspanning (hX : M.Dep X) (hX' : M.Nonspanning X) :
    (M.partition X).IsTutteSeparation := by
  simp [Partition.isTutteSeparation_iff', hX, hX']

lemma Nonspanning.partition_isVerticalSeparation (hX : M.Nonspanning X)
    (hXc : M.Nonspanning (M.E \ X)) : (M.partition X).IsVerticalSeparation := by
  simp [Partition.isVerticalSeparation_iff_nonspanning, hX, hXc]

lemma Codep.partition_isVerticalSeparation (hX : M.Codep X) (hXc : M.Nonspanning X) :
    (M.partition X).IsVerticalSeparation := by
  simp [Partition.isVerticalSeparation_iff_nonspanning, hXc, hX.nonspanning_compl]

lemma Codep.partition_isTutteSeparation_of_dep_compl (hX : M.Codep X) (hXc : M.Dep (M.E \ X)) :
    (M.partition X).IsTutteSeparation := by
  simp [Partition.isTutteSeparation_iff, hX, hXc]

lemma Dep.partition_isCyclicSeparation (hX : M.Dep X) (hXc : M.Dep (M.E \ X)) :
    (M.partition X).IsCyclicSeparation := by
  simp [Partition.isCyclicSeparation_iff, hX, hXc]

lemma Dep.partition_isStrongSeparation (hX : M.Dep X) (hns : M.Nonspanning X)
    (hXc : M.Dep (M.E \ X)) (hXsc : M.Nonspanning (M.E \ X)) :
    (M.partition X).IsStrongSeparation := by
  simp_all [Partition.isStrongSeparation_iff']

variable {dg dg' : ℕ∞ → Matroid α → Set α → Prop}

/-! ### Abstract Connectivity -/

/-- An abstract notion of connectivity. `dg` is a predicate-valued function that for each `t`,
specifies what it means for a set `X` with connectivity `t` to be degenerate in a matroid `M`.
`PredConnected dg M` means that in `M`, every set of connectivity `t` either satisfies
`dg t`, or its complement satisfies `dg t`.
`
For instance, for `k`-Tutte-connectivity, sets of connectivity `k-1` or higher are not degenerate,
and sets of connectivity `k-2` or less are degenerate iff they are independent and coindependent. -/
def PredConnected (dg dg' : ℕ∞ → Matroid α → Set α → Prop) (M : Matroid α) :=
    ∀ P : M.Partition, dg P.eConn M P.left ∨ dg' P.eConn M P.right

lemma not_predConnected_iff : ¬ M.PredConnected dg dg' ↔
    ∃ P : M.Partition, P.IsPredSeparation (dg P.eConn) (dg' P.eConn ):= by
  simp [PredConnected, Partition.isPredSeparation_iff]

lemma PredConnected.not_IsPredSeparation (h : M.PredConnected dg dg') (P : M.Partition) :
    ¬ P.IsPredSeparation (dg P.eConn) (dg' P.eConn) := by
  contrapose! h
  rw [not_predConnected_iff]
  exact ⟨P, h⟩

lemma PredConnected.mono' (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → (dg' k M X ∨ dg' k M (M.E \ X)))
    (h : M.PredConnected dg dg) : M.PredConnected dg' dg' := by
  refine fun P ↦ ?_
  obtain h1 | h2 := h P
  · exact P.compl_left ▸ hdegen P.left_subset_ground h1
  rw [or_comm]
  exact P.compl_right ▸ hdegen P.right_subset_ground h2

lemma PredConnected.mono (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M X)
    (h : M.PredConnected dg dg) : M.PredConnected dg' dg' :=
  h.mono' fun _ _ _ hX h' ↦ .inl (hdegen hX h')

lemma PredConnected.mono_compl (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M (M.E \ X))
    (h : M.PredConnected dg dg) : M.PredConnected dg' dg' :=
  h.mono' fun _ _ _ hX h' ↦ .inr (hdegen hX h')

lemma PredConnected.dual' (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X →
    (dg' k M✶ X ∨ dg' k M✶ (M.E \ X))) (h : M.PredConnected dg dg) :
    M✶.PredConnected dg' dg' :=
  fun P ↦ by simpa using h.mono' (dg' := fun k N Y ↦ dg' k N✶ Y) (by simpa) P.ofDual

lemma PredConnected.dual_compl (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M✶ (M.E \ X))
    (h : M.PredConnected dg dg) : M✶.PredConnected dg' dg' :=
  fun P ↦ by simpa using h.mono_compl (dg' := fun k N Y ↦ dg' k N✶ Y) (by simpa) P.ofDual

lemma PredConnected.dual (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M✶ X)
    (h : M.PredConnected dg dg) : M✶.PredConnected dg' dg' :=
  fun P ↦ by simpa using h.mono (dg' := fun k N Y ↦ dg' k N✶ Y) (by simpa) P.ofDual


/-- A slightly more concrete notion of connectivity that still abstracts Tutte, vertical and cyclic
connectivity. `M.numConnected dg (k+1)` means that every separation of connectivity less than `k`
has a degenerate side in the of a specified `dg`.
Unlike `PredConnected`, this is required to be symmetric in the two sides.
Internal connectivity is not an example of this, since it has a nondegeneracy condition that
depends on the connectivity. -/
def NumConnected (M : Matroid α) (dg : Matroid α → Set α → Prop) (k : ℕ∞) : Prop :=
    M.PredConnected (fun j M X ↦ j + 1 + 1 ≤ k → dg M X) (fun j M X ↦ j + 1 + 1 ≤ k → dg M X)

lemma NumConnected.mono {dg} (h : M.NumConnected dg k) (hjk : j ≤ k) : M.NumConnected dg j :=
  PredConnected.mono (fun _ _ _ _ h hle ↦ h (hle.trans hjk)) h

/-- A version with `k`-connectedness rather than `(k+1)`. Usually the latter is preferred-/
lemma numConnected_iff_forall' {dg} : M.NumConnected dg k ↔
    ∀ (P : M.Partition), P.eConn + 1 + 1 ≤ k → ¬ P.IsPredSeparation dg dg := by
  simp only [NumConnected, PredConnected, ← imp_or, isPredSeparation_iff, not_and, not_not]
  simp_rw [or_iff_not_imp_left]

lemma numConnected_iff_forall {dg} : M.NumConnected dg (k+1) ↔
    ∀ (P : M.Partition), P.eConn + 1 ≤ k → ¬ P.IsPredSeparation dg dg := by
  simp [numConnected_iff_forall']

lemma numConnected_iff_forall_set {dg} : M.NumConnected dg (k+1) ↔
    ∀ ⦃X⦄, X ⊆ M.E → M.eConn X + 1 ≤ k → dg M X ∨ dg M (M.E \ X) := by
  simp only [numConnected_iff_forall, isPredSeparation_iff, Classical.not_and_iff_not_or_not]
  exact ⟨fun h X hXE hX ↦ by simpa using h (M.partition X) (by simpa),
    fun h P hP ↦ by simpa using h P.left_subset_ground (by simpa)⟩

lemma numConnected_top_iff {dg} : M.NumConnected dg ⊤ ↔ ∀ (P : M.Partition),
    ¬ P.IsPredSeparation dg dg := by
  simp [numConnected_iff_forall']

lemma numConnected_top_iff' {dg} :
    M.NumConnected dg ⊤ ↔ ∀ ⦃X⦄, X ⊆ M.E → dg M X ∨ dg M (M.E \ X) := by
  rw [← top_add (a := 1), numConnected_iff_forall_set]
  simp

lemma NumConnected.not_isPredSeparation {dg} (h : M.NumConnected dg (k+1)) (hP : P.eConn + 1 ≤ k) :
    ¬ P.IsPredSeparation dg dg := by
  rw [numConnected_iff_forall] at h
  exact h P hP

lemma exists_of_not_numConnected {dg} (h : ¬ M.NumConnected dg (k+1)) :
    ∃ (P : M.Partition), P.eConn + 1 ≤ k ∧ P.IsPredSeparation dg dg := by
  simpa [numConnected_iff_forall] using h

/-- By symmetry, we can choose a separation so that the LHS is 'smaller' in some specified sense.
Maybe useful for reducing case analysis.  -/
lemma exists_left_le_of_not_numConnected {β : Type*} [LinearOrder β] {dg}
    (h : ¬ M.NumConnected dg (k+1)) (f : Set α → β) :
    ∃ (P : M.Partition), P.eConn + 1 ≤ k ∧ P.IsPredSeparation dg dg ∧ f P.left ≤ f P.right := by
  obtain ⟨P', hP'le, hP'⟩ := exists_of_not_numConnected h
  obtain hle | hlt := le_or_gt (f P'.left) (f P'.right)
  · exact ⟨P', hP'le, hP', hle⟩
  exact ⟨P'.symm, by simpa, hP'.symm, hlt.le⟩

lemma exists_right_le_of_not_numConnected {β : Type*} [LinearOrder β] {dg}
    (h : ¬ M.NumConnected dg (k+1)) (f : Set α → β) :
    ∃ (P : M.Partition), P.eConn + 1 ≤ k ∧ P.IsPredSeparation dg dg ∧ f P.right ≤ f P.left := by
  obtain ⟨P, hPle, hP, hPf⟩ := exists_left_le_of_not_numConnected h f
  exact ⟨P.symm, by simpa, hP.symm, by simpa⟩

lemma not_numConnected_iff_exists {dg} : ¬ M.NumConnected dg (k+1) ↔
    ∃ (P : M.Partition), P.eConn + 1 ≤ k ∧ P.IsPredSeparation dg dg := by
  simp [numConnected_iff_forall]

lemma Partition.IsPredSeparation.not_numConnected {dg} (h : P.IsPredSeparation dg dg) :
    ¬ M.NumConnected dg (P.eConn + 1 + 1) :=
  fun hM ↦ hM.not_isPredSeparation rfl.le h

@[simp]
lemma numConnected_zero (M : Matroid α) (dg) : M.NumConnected dg 0 := by
  simp [NumConnected, PredConnected]

@[simp]
lemma numConnected_one (M : Matroid α) (dg) : M.NumConnected dg 1 := by
  simp [NumConnected, PredConnected]

lemma NumConnected.compl_degen {dg} (h : M.NumConnected dg k) :
    M.NumConnected (fun M X ↦ dg M (M.E \ X)) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simpa [numConnected_iff_forall, isPredSeparation_iff, not_imp_comm] using h

lemma NumConnected.mono_degen {dg dg'} (h : M.NumConnected dg k)
    (hdg : ∀ ⦃X⦄, X ⊆ M.E → dg M X → dg' M X) : M.NumConnected dg' k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [numConnected_iff_forall] at h ⊢
  exact fun P hPc hP ↦ h P hPc ⟨mt (hdg P.left_subset_ground) hP.1,
    mt (hdg P.right_subset_ground) hP.2⟩

lemma NumConnected.congr_degen {dg dg'} (hdg : ∀ ⦃X⦄, X ⊆ M.E → (dg M X ↔ dg' M X)) :
    M.NumConnected dg = M.NumConnected dg' := by
  ext k
  exact ⟨fun h ↦ h.mono_degen fun X hX ↦ (hdg hX).1, fun h ↦ h.mono_degen fun X hX ↦ (hdg hX).2⟩

lemma NumConnected.dual {dg} (h : M.NumConnected dg k) : M✶.NumConnected (fun M X ↦ dg M✶ X) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [numConnected_iff_forall] at h ⊢
  exact fun P hPc hP ↦ h P.ofDual (by simpa) ⟨(by simpa using hP.1), (by simpa using hP.2)⟩

lemma NumConnected.of_dual {dg} (h : M✶.NumConnected dg k) :
    M.NumConnected (fun M X ↦ dg M✶ X) k := by
  simpa using h.dual

lemma numConnected_of_subsingleton {dg} (h : M.E.Subsingleton) (k : ℕ∞) (hdg : dg M ∅) :
    M.NumConnected dg k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [numConnected_iff_forall]
  refine fun P hPconn hP ↦ ?_
  obtain hl | hr := P.trivial_of_ground_subsingleton h
  · exact hP.1 (by rwa [hl])
  exact hP.2 (by rwa [hr])

/-! ### Tutte Connectivity -/

/-- `M` is `k`-connected if the connectivity of every Tutte separation strictly exceeds `k - 2`.
The term has always been defined this way, but the difference of two is very awkward to work with;
`(k+1)`-connectedness is much more natural than `k`-connectedness.

For this reason, we use `TutteConnected (k+1)` in the API in all places except where
no convenience is lost. Vertical and Cyclic connectivities have the same issues. -/
def TutteConnected (M : Matroid α) (k : ℕ∞) := M.NumConnected (fun M X ↦ M.Indep X ∧ M.Coindep X) k


lemma not_tutteConnected_iff_exists : ¬ M.TutteConnected (k + 1) ↔
    ∃ P : M.Partition, P.eConn + 1 ≤ k ∧ P.IsTutteSeparation :=
  not_numConnected_iff_exists

lemma tutteConnected_iff_forall : M.TutteConnected (k + 1) ↔
    ∀ (P : M.Partition), P.eConn + 1 ≤ k → ¬ P.IsTutteSeparation :=
  numConnected_iff_forall

lemma tutteConnected_top_iff_forall : M.TutteConnected ⊤ ↔
    ∀ (P : M.Partition), ¬ P.IsTutteSeparation :=
  numConnected_top_iff ..

lemma TutteConnected.dual (h : M.TutteConnected k) : M✶.TutteConnected k :=
  (NumConnected.dual h).mono_degen <| by simp +contextual [coindep_def]

lemma TutteConnected.of_dual (h : M✶.TutteConnected k) : M.TutteConnected k :=
  M.dual_dual ▸ h.dual

lemma TutteConnected.mono (h : M.TutteConnected k) (hjk : j ≤ k) : M.TutteConnected j :=
  NumConnected.mono h hjk

@[gcongr]
lemma TutteConnected.mono'
    (hjk : j ≤ k) (h : M.TutteConnected k) : M.TutteConnected j := h.mono hjk

@[simp]
lemma tutteConnected_one (M : Matroid α) : M.TutteConnected 1 :=
  numConnected_one M _

@[simp]
lemma tutteConnected_zero (M : Matroid α) : M.TutteConnected 0 :=
  numConnected_zero M _

lemma tutteConnected_of_le_one (M : Matroid α) (hk : k ≤ 1) : M.TutteConnected k := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by enat_to_nat; omega
  · simp
  simp

@[simp]
lemma tutteConnected_dual_iff : M✶.TutteConnected = M.TutteConnected := by
  ext k
  exact ⟨TutteConnected.of_dual, TutteConnected.dual⟩

lemma Partition.IsTutteSeparation.not_tutteConnected (hP : P.IsTutteSeparation) :
    ¬ M.TutteConnected (P.eConn + 1 + 1) := by
  rw [not_tutteConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma TutteConnected.not_isTutteSeparation (h : M.TutteConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ¬ P.IsTutteSeparation :=
  fun h' ↦ h'.not_tutteConnected <| h.mono <| add_left_mono hP

lemma TutteConnected.not_isCyclicSeparation (h : M.TutteConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ¬ P.IsCyclicSeparation :=
  fun hP' ↦ h.not_isTutteSeparation hP hP'.isTutteSeparation

lemma TutteConnected.not_isVerticalSeparation (h : M.TutteConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ¬ P.IsVerticalSeparation :=
  fun hP' ↦ h.not_isTutteSeparation hP hP'.isTutteSeparation

lemma tutteConnected_of_subsingleton (h : M.E.Subsingleton) (k : ℕ∞) : M.TutteConnected k :=
  numConnected_of_subsingleton h _ <| by simp

/-- In a matroid that isn't `(k + 1)`-connected, there is either a strong separation, or
a separation arising from a small circuit or cocircuit. -/
lemma exists_strong_or_small_of_not_tutteConnected (h : ¬ M.TutteConnected (k + 1)) :
    ∃ P : M.Partition, P.eConn + 1 ≤ k ∧ P.IsTutteSeparation ∧ (P.IsStrongSeparation ∨
    (P.left.encard ≤ k ∧ ((M.Indep P.left ∧ M.IsHyperplane P.right) ∨
      (M.IsCircuit P.left ∧ M.Spanning P.right)))) := by
  obtain ⟨P, hP⟩ := not_tutteConnected_iff_exists.1 h
  revert hP
  apply Partition.wlog_symm_dual (property := Matroid.Indep) (P₀ := P)
  · exact fun N P aux hP ↦ aux (by simpa using hP)
  · refine fun N P aux hP ↦ ?_
    obtain ⟨Q, hQk, hQ⟩ := aux (by simpa using hP)
    rw [← Q.coindep_left_iff, dual_coindep_iff, ← Q.isCocircuit_left_iff, dual_isCocircuit_iff,
      ← isCocircuit_def, ← Q.ofDual_left, ← coindep_def, Q.ofDual.coindep_left_iff,
      Q.ofDual.isCocircuit_left_iff, ← Partition.isStrongSeparation_ofDual_iff,
      ← Partition.isTutteSeparation_ofDual_iff] at hQ
    exact ⟨Q.ofDual, by simpa, by grind⟩
  · rintro N P hi ⟨hPconn, hP⟩
    obtain ⟨Q, hQ, hQP, hQ1, hQle⟩ := hP.exists_of_indep_left hi
    refine ⟨Q, by grw [hQle, hPconn], hQ, .inr ⟨?_, .inl ⟨(hi.subset hQP),
      by rwa [← Q.isCocircuit_left_iff]⟩⟩⟩
    grw [← N.eConn_add_nullity_add_nullity_dual Q.left, hQ1.nullity_eq, (hi.subset hQP).nullity_eq,
      add_zero, Q.eConn_left, hQle]
    exact hPconn
  refine fun N Q h1 h2 h3 h4 ⟨hQconn, hQ⟩ ↦ ⟨Q, hQconn, hQ, .inl ?_⟩
  simp only [Partition.left_subset_ground, not_indep_iff, Partition.right_subset_ground,
    dual_ground, dep_dual_iff, Q.codep_left_iff, Q.codep_right_iff] at h1 h2 h3 h4
  simp [Partition.isStrongSeparation_iff', h1, h2, h3, h4]

lemma tutteConnected_iff_numConnected_encard (hk : k ≠ ⊤) :
    M.TutteConnected k ↔ M.NumConnected (fun M X ↦ X.encard ≤ M.eConn X) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp only [tutteConnected_iff_forall, numConnected_iff_forall,
    isPredSeparation_iff (degen_left := fun M X ↦ X.encard ≤ M.eConn X), eConn_left, not_le,
    eConn_right]
  refine ⟨fun h P hPle hP ↦ h P hPle ?_, fun h P hPle hP ↦ h P hPle ?_⟩
  · rwa [isTutteSeparation_iff_lt_encard (by enat_to_nat!)]
  rwa [← isTutteSeparation_iff_lt_encard (by enat_to_nat!)]

/-! ### Vertical Connectivity -/

def VerticallyConnected (M : Matroid α) := M.NumConnected Matroid.Coindep

lemma VerticallyConnected.mono (h : M.VerticallyConnected k) (hjk : j ≤ k) :
    M.VerticallyConnected j :=
  NumConnected.mono h hjk

@[gcongr]
lemma VerticallyConnected.mono' (hjk : j ≤ k) (h : M.VerticallyConnected k) :
    M.VerticallyConnected j := h.mono hjk

lemma TutteConnected.verticallyConnected (h : M.TutteConnected k) : M.VerticallyConnected k :=
  NumConnected.mono_degen h <| fun _ _ ↦ And.right

lemma not_verticallyConnected_iff_exists : ¬ M.VerticallyConnected (k+1) ↔
    ∃ P : M.Partition, P.eConn + 1 ≤ k ∧ P.IsVerticalSeparation :=
  not_numConnected_iff_exists

lemma verticallyConnected_iff_forall : M.VerticallyConnected (k + 1) ↔
    ∀ (P : M.Partition), P.eConn + 1 ≤ k → ¬ P.IsVerticalSeparation := by
  rw [← not_iff_not]
  simp [not_verticallyConnected_iff_exists]

lemma Partition.IsVerticalSeparation.not_verticallyConnected (hP : P.IsVerticalSeparation) :
    ¬ M.VerticallyConnected (P.eConn + 1 + 1) := by
  rw [not_verticallyConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma VerticallyConnected.not_isVerticalSeparation (h : M.VerticallyConnected k)
    (hP : P.eConn + 1 + 1 ≤ k) : ¬ P.IsVerticalSeparation :=
  fun h' ↦ h'.not_verticallyConnected <| h.mono hP

lemma VerticallyConnected.compl_spanning_of_nonspanning_of_eConn_le
    (h : M.VerticallyConnected (k+1))
    (hX : M.Nonspanning X) (hconn : M.eConn X + 1 ≤ k) : M.Spanning (M.E \ X) := by
  have hnv := h.not_isVerticalSeparation (P := M.partition X) (by simpa)
  rwa [not_isVerticalSeparation_iff', partition_left .., or_iff_right hX.not_spanning] at hnv

lemma verticallyConnected_top_iff :
    M.VerticallyConnected ⊤ ↔ ∀ X ⊆ M.E, M.Spanning X ∨ M.Spanning (M.E \ X) := by
  rw [← top_add (a := 1), verticallyConnected_iff_forall]
  simp only [le_top, isVerticalSeparation_iff_nonspanning, forall_const,
    Classical.not_and_iff_not_or_not, not_nonspanning_left_iff, not_nonspanning_right_iff]
  exact ⟨fun h X hX ↦ by simpa using h (M.partition X),
    fun h P ↦ by simpa using h _ P.left_subset_ground⟩

@[simp]
lemma verticallyConnected_loopyOn (E : Set α) (k : ℕ∞) : (loopyOn E).VerticallyConnected k :=
  VerticallyConnected.mono (by simp +contextual [verticallyConnected_top_iff]) le_top

@[simp]
lemma verticallyConnected_zero (M : Matroid α) : M.VerticallyConnected 0 :=
    M.tutteConnected_zero.verticallyConnected

@[simp]
lemma verticallyConnected_one (M : Matroid α) : M.VerticallyConnected 1 :=
    M.tutteConnected_one.verticallyConnected

@[simp]
lemma verticallyConnected_of_le_one (M : Matroid α) (hk : k ≤ 1) : M.VerticallyConnected k :=
    (M.tutteConnected_of_le_one hk).verticallyConnected

@[simp]
lemma verticallyConnected_freeOn_iff (E : Set α) (k : ℕ∞) :
    (freeOn E).VerticallyConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  obtain hE | hE := E.subsingleton_or_nontrivial
  · simp [((freeOn E).tutteConnected_of_subsingleton hE (k + 1)).verticallyConnected, hE]
  obtain (rfl | ⟨k,rfl⟩) := k.eq_zero_or_exists_eq_add_one; simp
  simp only [hE.not_subsingleton, add_eq_zero, one_ne_zero, and_false, or_self, iff_false]
  intro h
  obtain ⟨x, hx, y, hy, hne⟩ := hE
  refine h.not_isVerticalSeparation (P := (freeOn E).partition {x} (by simpa))
    (by simp [← loopyOn_dual_eq]) ?_
  suffices ¬ {x} = E by simpa [Partition.isVerticalSeparation_iff_nonspanning, nonspanning_iff, hx]
  rintro rfl
  exact hne.symm (by simpa using hy)

@[simp]
lemma uniqueBaseOn_tutteConnected_iff {B E : Set α} :
    (uniqueBaseOn B E).TutteConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  obtain hE | hE := E.subsingleton_or_nontrivial
  · simp [(uniqueBaseOn B E).tutteConnected_of_subsingleton hE, hE]
  obtain (rfl | ⟨k,rfl⟩) := k.eq_zero_or_exists_eq_add_one; simp
  refine iff_of_false (fun ht ↦ ?_) (by simp [hE.not_subsingleton])
  obtain ⟨e, he⟩ := hE.nonempty
  refine ht.not_isTutteSeparation (P := Matroid.partition _ {e}) (by simp) ?_
  rw [isTutteSeparation_iff_add_one_le_encard (by simp [← Partition.eConn_left])]
  simp [hE.diff_singleton_nonempty e]

@[simp]
lemma loopyOn_tutteConnected_iff (E : Set α) :
    (loopyOn E).TutteConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  simp [← uniqueBaseOn_empty]

@[simp]
lemma freeOn_tutteConnected_iff (E : Set α) :
    (freeOn E).TutteConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  rw [← tutteConnected_dual_iff, freeOn_dual_eq, loopyOn_tutteConnected_iff]

lemma tutteConnected_two_iff [M.Nonempty] : M.TutteConnected 2 ↔ M.Connected := by
  rw [← not_iff_not, exists_partition_iff_not_connected, ← one_add_one_eq_two,
    not_tutteConnected_iff_exists]
  simp only [ENat.add_le_right_iff, ENat.one_ne_top, or_false]
  refine ⟨fun ⟨P, hP0, hP⟩ ↦ ⟨P, hP.nonempty_left, hP.nonempty_right, hP0⟩,
    fun ⟨P, hPl, hPr, hP⟩ ↦ ⟨P, hP, ?_⟩⟩
  rwa [isTutteSeparation_iff_lt_encard (by enat_to_nat!), hP, encard_pos,
    and_iff_left hPr.encard_pos]

lemma TutteConnected.connected [M.Nonempty] (hM : M.TutteConnected k) (hk : 2 ≤ k) :
    M.Connected :=
  tutteConnected_two_iff.1 (hM.mono hk)

@[simp]
lemma emptyOn_tutteConnected (α : Type*) (k : ℕ∞) : (emptyOn α).TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp [← freeOn_empty, freeOn_tutteConnected_iff]

lemma Connected.tutteConnected_two (hM : M.Connected) : (M.TutteConnected 2) := by
  obtain rfl | hne := M.eq_emptyOn_or_nonempty; simp
  rwa [tutteConnected_two_iff]

lemma Connected.tutteConnected_one_add_one (hM : M.Connected) : (M.TutteConnected (1 + 1)) :=
  hM.tutteConnected_two

/-! ### Cyclic connectivity -/

def CyclicallyConnected (M : Matroid α) := M.NumConnected Matroid.Indep

lemma CyclicallyConnected.dual_verticallyConnected (h : M.CyclicallyConnected k) :
    M✶.VerticallyConnected k :=
  NumConnected.dual h

lemma VerticallyConnected.dual_cyclicallyConnected (h : M.VerticallyConnected k) :
    M✶.CyclicallyConnected k :=
  (NumConnected.dual h).mono_degen <| by simp

@[simp]
lemma verticallyConnected_dual_iff : M✶.VerticallyConnected k ↔ M.CyclicallyConnected k :=
  ⟨fun h ↦ dual_dual M ▸ h.dual_cyclicallyConnected, CyclicallyConnected.dual_verticallyConnected⟩

@[simp]
lemma cyclicallyConnected_dual_iff : M✶.CyclicallyConnected k ↔ M.VerticallyConnected k := by
  rw [← verticallyConnected_dual_iff, dual_dual]

lemma CyclicallyConnected.mono (h : M.CyclicallyConnected k) (hjk : j ≤ k) :
    M.CyclicallyConnected j :=
  dual_dual M ▸ (h.dual_verticallyConnected.mono hjk).dual_cyclicallyConnected

@[gcongr]
lemma CyclicallyConnected.mono' (hjk : j ≤ k) (h : M.CyclicallyConnected k) :
  M.CyclicallyConnected j := h.mono hjk

lemma TutteConnected.cyclicallyConnected (h : M.TutteConnected k) : M.CyclicallyConnected k := by
  simpa using h.dual.verticallyConnected

lemma not_cyclicallyConnected_iff_exists : ¬ M.CyclicallyConnected (k + 1) ↔
    ∃ P : M.Partition, P.eConn + 1 ≤ k ∧ P.IsCyclicSeparation :=
  not_numConnected_iff_exists

lemma cyclicallyConnected_iff_forall : M.CyclicallyConnected (k + 1) ↔
    ∀ (P : M.Partition), P.eConn + 1 ≤ k → ¬ P.IsCyclicSeparation :=
  numConnected_iff_forall

lemma Partition.IsCyclicSeparation.not_cyclicallyConnected (hP : P.IsCyclicSeparation) :
    ¬ M.CyclicallyConnected (P.eConn + 1 + 1) := by
  rw [not_cyclicallyConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma CyclicallyConnected.not_isCyclicSeparation (h : M.CyclicallyConnected k)
    (hP : P.eConn + 1 + 1 ≤ k) : ¬ P.IsCyclicSeparation :=
  fun h' ↦ h'.not_cyclicallyConnected <| h.mono hP

lemma CyclicallyConnected.compl_indep_of_dep_of_eConn_le (h : M.CyclicallyConnected (k + 1))
    (hX : M.Dep X) (hXconn : M.eConn X + 1 ≤ k) : M.Indep (M.E \ X) := by
  have h' := h.not_isCyclicSeparation (P := M.partition X) (by simpa)
  simpa [isCyclicSeparation_iff, hX] using h'

@[simp]
lemma cyclicallyConnected_zero (M : Matroid α) : M.CyclicallyConnected 0 :=
    M.tutteConnected_zero.cyclicallyConnected

@[simp]
lemma cyclicallyConnected_one (M : Matroid α) : M.CyclicallyConnected 1 :=
    M.tutteConnected_one.cyclicallyConnected

@[simp]
lemma cyclicallyConnected_of_le_one (M : Matroid α) (hk : k ≤ 1) : M.CyclicallyConnected k :=
    (M.tutteConnected_of_le_one hk).cyclicallyConnected

lemma IsLoop.not_tutteConnected {e : α} (he : M.IsLoop e) (hME : M.E.Nontrivial) (hk : 1 ≤ k) :
    ¬ M.TutteConnected (k + 1) := by
  have hM : M.Nonempty := ⟨hME.nonempty⟩
  exact fun h ↦ he.not_connected hME <| tutteConnected_two_iff.1 <| h.mono <| add_left_mono hk

lemma IsColoop.not_tutteConnected {e : α} (he : M.IsColoop e) (hME : M.E.Nontrivial) (hk : 1 ≤ k) :
    ¬ M.TutteConnected (k + 1) := by
  simpa using he.dual_isLoop.not_tutteConnected hME hk

/-- This needs the lower bound on co-rank; otherwise an extenssion of a large free matroid by
a loop would be a counterexample for any `k`. -/
lemma CyclicallyConnected.le_girth (h : M.CyclicallyConnected k) (hlt : k ≤ M✶.eRank) :
    k ≤ M.girth := by
  obtain (rfl | ⟨k, rfl⟩) := k.eq_zero_or_exists_eq_add_one; simp
  rw [← not_lt, girth_lt_iff, not_exists]
  rintro C ⟨hC, hCcard⟩
  refine h.not_isCyclicSeparation (P := M.partition C) ?_ ?_
  · grw [eConn_partition, hC.eConn_add_one_eq, eRk_le_encard]
    exact Order.add_one_le_of_lt hCcard
  suffices ¬ M.Indep (M.E \ C) by simpa [Partition.isCyclicSeparation_iff, hC.dep]
  intro hi
  rw [← dual_coindep_iff, ← dual_ground, ← spanning_iff_compl_coindep] at hi
  grw [← M✶.eRk_le_encard, hi.eRk_eq] at hCcard
  exact hCcard.not_ge hlt

lemma TutteConnected.le_girth (h : M.TutteConnected (k + 1)) (hlt : 2 * k ≤ M.E.encard) :
    k + 1 ≤ M.girth := by
  obtain hle | hltr := le_or_gt (k + 1) M✶.eRank
  · exact h.cyclicallyConnected.le_girth hle
  rw [← not_lt, girth_lt_iff, not_exists]
  rintro C ⟨hC, hCcard⟩
  refine h.not_isTutteSeparation (P := M.partition C) ?_ ?_
  · grw [eConn_partition, eConn_le_eRk, hC.eRk_add_one_eq]
    exact Order.le_of_lt_add_one hCcard
  refine hC.dep.partition_isTutteSeparation_of_nonspanning ?_
  grw [← eRank_add_eRank_dual] at hlt
  have hle : k ≤ M.eRank := by eomega
  grw [hle, ← hC.eRk_add_one_eq, ENat.add_one_lt_add_one_iff] at hCcard
  exact nonspanning_of_eRk_ne hCcard.ne

/-- This needs the strict inequality in the hypothesis, since nothing like this can be true
for `k = ⊤`. This is also false for matroids like `U₂,₅` if there is no lower bound on size. -/
lemma tutteConnected_iff_verticallyConnected_girth (hlt : 2 * k < M.E.encard + 1) :
    M.TutteConnected (k + 1) ↔ M.VerticallyConnected (k + 1) ∧ k + 1 ≤ M.girth := by
  have hk : k ≠ ⊤ := by rintro rfl; simp at hlt
  refine ⟨fun h ↦ ⟨h.verticallyConnected, h.le_girth (by eomega)⟩,
    fun ⟨h', hle⟩ ↦ by_contra fun h ↦ ?_⟩
  obtain ⟨P, hPconn, hP, (hPs | ⟨hcard, ⟨hi, hh⟩ | ⟨hc, hs⟩⟩)⟩ :=
    exists_strong_or_small_of_not_tutteConnected h
  · exact h'.not_isVerticalSeparation (by simpa) hPs.isVerticalSeparation
  · refine h'.not_isVerticalSeparation (by simpa) ?_
    rw [P.isVerticalSeparation_iff_nonspanning, and_iff_left hh.nonspanning, ← not_spanning_iff]
    intro hPs
    obtain ⟨C, hCP, hC⟩ := (hP.dep_of_spanning_left hPs).exists_isCircuit_subset
    grw [hC.girth_le_card, ← hC.eRk_add_one_eq, M.eRk_mono hCP, ← hcard, hh.eRk_add_one_eq,
      ← hPs.eRk_eq, hi.eRk_eq_encard] at hle
    simp [Infinite.encard_eq (by simpa using hle), hk] at hcard
  grw [hc.girth_le_card, ← hcard] at hle
  simp [Infinite.encard_eq (by simpa using hle), hk] at hcard

lemma tutteConnected_iff_verticallyConnected_cyclicallyConnected (hlt : 2 * k < M.E.encard) :
    M.TutteConnected (k + 1) ↔ M.VerticallyConnected (k + 1) ∧ M.CyclicallyConnected (k + 1) := by
  refine ⟨fun h ↦ ⟨h.verticallyConnected, h.cyclicallyConnected⟩,
    fun ⟨hv, hc⟩ ↦ by_contra fun h ↦ ?_⟩
  obtain ⟨P, hPconn, hP, (hPs | ⟨hcard, hP'⟩)⟩ := exists_strong_or_small_of_not_tutteConnected h
  · exact hv.not_isVerticalSeparation (by simpa) hPs.isVerticalSeparation
  wlog hi : M.Indep P.left generalizing M P with aux
  · rw [or_iff_right (by simp [hi])] at hP'
    specialize aux (M := M✶) (by simpa) (by simp [hc, hv]) (by simpa) (by simpa) (by simpa) P.dual
      (by simpa) (by simpa) (by simpa)
    simp [hi, ← coindep_def, P.coindep_left_iff, hP'.2, isHyperplane_dual_iff, hP'.1] at aux
  rw [or_iff_left (fun h ↦ h.1.not_indep hi), and_iff_right hi] at hP'
  have hnv := hv.not_isVerticalSeparation (by simpa)
  have hnc := hc.not_isCyclicSeparation (by simpa)
  have hPconn_ne : P.eConn ≠ ⊤ := fun h ↦ by enat_to_nat!
  simp only [P.isCyclicSeparation_iff, not_and, Partition.right_subset_ground, not_dep_iff] at hnc
  simp only [P.isVerticalSeparation_iff_nonspanning, not_and,
    Partition.not_nonspanning_right_iff] at hnv
  rw [imp_iff_not hP'.not_spanning, not_nonspanning_iff] at hnv
  obtain ⟨C, hCr, hC⟩ := (hP.dep_of_spanning_left hnv).exists_isCircuit_subset
  have hb := hi.isBase_of_spanning hnv
  refine hc.not_isCyclicSeparation (P := M.partition C) ?_ ?_
  · grw [eConn_partition, eConn_le_eRk, eRk_mono _ hCr, hP'.eRk_add_one_eq, ← hb.encard_eq_eRank]
    simpa
  obtain rfl | hssu := hCr.eq_or_ssubset
  · rw [← P.union_eq, encard_union_eq P.disjoint] at hlt
    have := hb.encard_eq_eRank ▸ hP'.eRk_add_one_eq ▸ hC.eRk_add_one_eq
    eomega
  refine hC.dep.partition_isCyclicSeparation (hb.dep_of_ssubset ?_)
  exact P.compl_right ▸ diff_ssubset_diff_right P.right_subset_ground hssu

/-- Every `(k + 1)`-connected matroid on at most `2k` elements is uniform. -/
lemma TutteConnected.isUniform_of_encard_le (h : M.TutteConnected (k + 1))
    (hle : M.E.encard ≤ 2 * k) : M.IsUniform := by
  intro X hXE
  by_contra! hnot
  rw [not_indep_iff, not_spanning_iff] at hnot
  wlog hXcard : X.encard ≤ k generalizing M X with aux
  · refine aux h.dual (by simpa) (X := M.E \ X) diff_subset ?_ ?_
    · rwa [dep_dual_iff, codep_compl_iff, nonspanning_compl_dual_iff, and_comm]
    have := encard_diff_add_encard_of_subset hXE
    enat_to_nat!
    omega
  have hXconn : M.eConn X + 1 ≤ k := by grw [eConn_le_eRk, hnot.1.eRk_add_one_le_encard, hXcard]
  refine h.not_isTutteSeparation (P := M.partition X) (by simpa) ?_
  simp [isTutteSeparation_iff', hnot.1, hnot.2]

/-! ### Internal and Weak Connectivity -/

/-- A weakly `(k+1)`-connected matroid is one with no strong separation of order less than `k`.
Weak `3`-connectedness is `3`-connectedness up to series/parallel pairs (TODO).  -/
def WeaklyConnected (M : Matroid α) := M.NumConnected (fun M X ↦ M.Indep X ∨ M.Coindep X)

lemma weaklyConnected_iff_forall : M.WeaklyConnected (k + 1) ↔
    ∀ (P : M.Partition), P.eConn + 1 ≤ k → ¬ P.IsStrongSeparation := by
  simp [WeaklyConnected, numConnected_iff_forall]

@[simp]
lemma weaklyConnected_zero (M : Matroid α) : M.WeaklyConnected 0 := by
  simp [WeaklyConnected]

@[simp]
lemma weaklyConnected_one (M : Matroid α) : M.WeaklyConnected 1 := by
  simp [WeaklyConnected]

lemma WeaklyConnected.mono (h : M.WeaklyConnected k) (hjk : j ≤ k) : M.WeaklyConnected j :=
  NumConnected.mono h hjk

lemma weaklyConnected_dual_iff : M✶.WeaklyConnected k ↔ M.WeaklyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp only [weaklyConnected_iff_forall]
  exact ⟨fun h P hP hP' ↦ h P.dual (by simpa) (by simpa),
    fun h P hP hP' ↦ h P.ofDual (by simpa) (by simpa)⟩

alias ⟨WeaklyConnected.of_dual, WeaklyConnected.dual⟩ := weaklyConnected_dual_iff

lemma CyclicallyConnected.weaklyConnected (h : M.CyclicallyConnected k) : M.WeaklyConnected k :=
  NumConnected.mono_degen h fun _ _ ↦ Or.inl

lemma VerticallyConnected.weaklyConnected (h : M.VerticallyConnected k) : M.WeaklyConnected k :=
  NumConnected.mono_degen h fun _ _ ↦ Or.inr

lemma TutteConnected.weaklyConnected (h : M.TutteConnected k) : M.WeaklyConnected k :=
  h.verticallyConnected.weaklyConnected

lemma WeaklyConnected.not_isStrongSeparation (h : M.WeaklyConnected (k + 1))
    (hPconn : P.eConn + 1 ≤ k) : ¬ P.IsStrongSeparation :=
  h.not_isPredSeparation hPconn

/-- A weakly 2-connected matroid having both a loop and a coloop is structurally trivial. -/
lemma WeaklyConnected.eq_uniqueBaseOn_of_isLoop_isColoop {e f : α} (hM : M.WeaklyConnected 2)
    (he : M.IsLoop e) (hf : M.IsColoop f) :
    ∃ E, e ∈ E ∧ f ∈ E ∧ (M = uniqueBaseOn {f} E ∨ M = uniqueBaseOn (E \ {e}) E) := by
  rw [← one_add_one_eq_two] at hM
  replace hM := hM.not_isStrongSeparation (P := M.partition {e,f})
  simp only [eConn_partition, ENat.add_le_right_iff, ENat.one_ne_top, or_false,
    isStrongSeparation_iff, partition_left, partition_right, not_and, not_codep_compl_iff] at hM
  have heE := he.mem_ground
  have hfE := hf.mem_ground
  rw [eConn_of_subset_loops_union_coloops
    (by simp [pair_subset_iff, show e ∈ M.loops from he, show f ∈ M.coloops from hf]),
    imp_iff_right rfl, imp_iff_right (he.dep_of_mem (by simp)), ← dep_dual_iff,
    imp_iff_right (hf.dual_isLoop.dep_of_mem (by simp))] at hM
  obtain h1 | h2 := M.indep_or_dep (X := M.E \ {e,f})
  · refine ⟨M.E, heE, hfE, .inr <| ext_indep rfl fun I hIE ↦ ?_⟩
    simp +contextual only [uniqueBaseOn_indep_iff', subset_inter_iff, subset_diff_singleton_iff,
      and_right_comm, and_self, iff_def, Indep.subset_ground, true_and, and_imp]
    refine ⟨fun hI heI ↦ (he.not_indep_of_mem heI) hI, fun hIE heI ↦ ?_⟩
    rw [← diff_indep_iff_indep_of_subset_coloops (K := {f}) (by simpa)]
    exact h1.subset <| by simp [subset_diff, heI, hIE.trans <| subset_insert ..]
  refine ⟨M.E, heE, hfE, .inl <| ext_indep rfl fun I hI ↦ ?_⟩
  rw [uniqueBaseOn_indep_iff (by simpa)]
  specialize hM h2
  refine ⟨fun h x hxI ↦ ?_, fun h ↦ hf.isNonloop.indep.subset h⟩
  rw [← spanning_iff_compl_coindep, spanning_iff, pair_comm,
    closure_insert_congr_right he.closure, insert_empty_eq, closure_eq_of_subset_coloops
    (by simpa), singleton_union] at hM
  have hx := hM.1 ▸ (h.subset_ground hxI)
  rwa [mem_insert_iff, ← isLoop_iff, or_iff_left (h.isNonloop_of_mem hxI).not_isLoop] at hx

lemma WeaklyConnected.subsingleton_loops_or_coloops (h : M.WeaklyConnected 2) :
    M.loops.Subsingleton ∨ M.coloops.Subsingleton := by
  by_contra! hcon
  obtain ⟨e, he⟩ := hcon.1.nonempty
  obtain ⟨f, hf⟩ := hcon.2.nonempty
  obtain ⟨E, heE, hfE, rfl | rfl⟩ := h.eq_uniqueBaseOn_of_isLoop_isColoop he hf
  · simp [uniqueBaseOn_coloops_eq', ← not_subsingleton_iff,
      subsingleton_singleton.anti inter_subset_left] at hcon
  simp [uniqueBaseOn_loops_eq, ← not_subsingleton_iff,
      subsingleton_singleton.anti inter_subset_right] at hcon

lemma weaklyConnected_uniqueBaseOn_iff {B E : Set α} (hBE : B ⊆ E) (hk : k ≠ 0) :
    (uniqueBaseOn B E).WeaklyConnected (k + 1) ↔ B.Subsingleton ∨ (E \ B).Subsingleton := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simpa [inter_eq_self_of_subset_left hBE, uniqueBaseOn_loops_eq] using
      (h.mono (show 2 ≤ k + 1 by eomega)).subsingleton_loops_or_coloops.symm
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp at hk
  simp only [weaklyConnected_iff_forall, ENat.add_le_add_right_iff, ENat.one_ne_top, or_false,
    isStrongSeparation_iff, uniqueBaseOn_dep_iff, ← dep_dual_iff, uniqueBaseOn_dual_eq, not_and,
    and_imp]
  simp +contextual only [not_subset, mem_diff, not_and, not_not, ← compl_left, uniqueBaseOn_ground,
    diff_nonempty, forall_exists_index, and_imp, forall_const]
  rintro (hB | hB)
  · rintro P - - - - - - x hx hxB - - - - - - - - y hy hy1 hyB
    obtain rfl := hB.elim hyB (hxB (P.left_subset_ground hx))
    contradiction
  rintro P - - x hx hxB - - - - - - - y hyE hy hyB
  obtain rfl := hB.elim ⟨P.left_subset_ground hx, hxB⟩ ⟨hyE, hyB⟩
  contradiction

lemma TutteConnected.weaklyConnected_add_one_iff (h : M.TutteConnected (k + 1)) :
    M.WeaklyConnected (k + 1 + 1) ↔ ∀ (P : M.Partition), P.eConn = k → ¬ P.IsStrongSeparation := by
  simp only [weaklyConnected_iff_forall, ENat.add_le_add_right_iff, ENat.one_ne_top, or_false]
  refine ⟨fun h' P hPconn ↦ h' P hPconn.le, fun h' P hPconn hP ↦ h' P ?_ hP⟩
  obtain rfl | hlt := hPconn.eq_or_lt
  · rfl
  exact False.elim <| h.not_isTutteSeparation (Order.add_one_le_of_lt hlt) hP.isTutteSeparation

lemma TutteConnected.weaklyConnected_of_delete_of_subset_loops {D : Set α}
    (h : (M ＼ D).TutteConnected 2) (hD : D ⊆ M.loops) : M.WeaklyConnected 2 := by
  rw [show (2 : ℕ∞) = 1 + 1 from rfl] at *
  simp only [weaklyConnected_iff_forall, ENat.add_le_right_iff, ENat.one_ne_top, or_false]
  intro P hP0 hP
  refine h.not_isTutteSeparation (P := P.delete D) (by grw [P.eConn_delete_le, hP0, zero_add]) ?_
  simp only [isTutteSeparation_iff, delete_left, delete_dep_iff, disjoint_sdiff_left, delete_right]
  rw [isStrongSeparation_iff] at hP
  have hcd := hP.2.1.contract_of_indep (I := D)
    (M✶.coloops_indep.subset (by grw [dual_coloops, inter_subset_right, hD]))
  have hcd' := hP.2.2.2.contract_of_indep (I := D)
    (M✶.coloops_indep.subset (by grw [dual_coloops, inter_subset_right, hD]))
  rw [← dual_delete, dep_dual_iff] at hcd hcd'
  simp [hcd, hcd']

/-- A matroid is weakly 2-connected if and only if it is 2-connected after removing the
loops or coloops. -/
lemma weaklyConnected_two_iff :
    M.WeaklyConnected 2 ↔ M.removeLoops.TutteConnected 2 ∨ M.removeColoops.TutteConnected 2 := by
  rw [← one_add_one_eq_two, iff_comm]
  refine ⟨fun h ↦ h.elim (fun h' ↦ ?_) (fun h' ↦ ?_), fun h ↦ ?_⟩
  · rw [removeLoops_eq_delete] at h'
    exact TutteConnected.weaklyConnected_of_delete_of_subset_loops h' rfl.subset
  · rw [← tutteConnected_dual_iff, removeColoops_dual, removeLoops_eq_delete] at h'
    exact (h'.weaklyConnected_of_delete_of_subset_loops rfl.subset).of_dual
  wlog hlps : M.loops.Nonempty → M.coloops.Nonempty generalizing M with aux
  · rw [← tutteConnected_dual_iff, removeLoops_dual, or_comm, ← tutteConnected_dual_iff,
      removeColoops_dual]
    exact aux h.dual (by simp [Classical.not_imp.1 hlps])
  obtain hLe | hLne := M.loops.eq_empty_or_nonempty
  · right
    simp only [removeColoops_eq_delete, tutteConnected_iff_forall, ENat.add_le_right_iff,
      ENat.one_ne_top, or_false]
    rintro P hP0 hP
    refine h.not_isStrongSeparation (P := P.ofDeleteLeft) ?_ ?_
    · simpa [eConn_ofDeleteLeft, ← dual_loops, loops, eLocalConn_closure_right]
    simp only [isStrongSeparation_iff, ofDeleteLeft_left, union_coloops_dep_iff, ofDeleteLeft_right]
    obtain hs | h0 := (isTutteSeparation_iff_isStrongSeparation_of_zero hP0).1 hP
    · refine ⟨hs.dep_left.of_delete, hs.codep_left.of_delete, hs.dep_right.of_delete, ?_⟩
      have h' := hs.codep_right
      simp_rw [← removeColoops_eq_delete, removeColoops_eq_contract] at h'
      exact h'.of_contract
    simp only [nonempty_iff_ne_empty, ne_eq, ← removeColoops_eq_delete, removeColoops_loops_eq, hLe,
      subset_empty_iff, removeColoops_coloops, or_self, or_self_left] at h0
    tauto
  obtain ⟨f, hf : M.IsColoop f⟩ := hlps hLne
  obtain ⟨e, he : M.IsLoop e⟩ := hLne
  obtain ⟨E, heE, hfE, rfl | rfl⟩ := h.eq_uniqueBaseOn_of_isLoop_isColoop he hf
  · refine .inl <| tutteConnected_of_subsingleton ?_ _
    simp [removeLoops_eq_delete, uniqueBaseOn_loops_eq,
      subsingleton_singleton.anti inter_subset_right]
  refine .inr <| tutteConnected_of_subsingleton ?_ _
  simp [removeColoops_eq_delete, subsingleton_singleton.anti inter_subset_right]


-- /-- This lemma is most relevant when `k = 1`; it means that a connected matroid is weakly
-- three-connected if and only if it is three-connected up to simplification and cosimplification.
-- lemma TutteConnected.weaklyConnected_add_one_iff (h : M.TutteConnected (k + 1)) :
--     M.WeaklyConnected (k + 1 + 1) ↔ ∀ (P : M.Partition), P.eConn = k → M.eRk P.left = k ∨
--         M.eRk P.right = k ∨ M✶.eRk P.left = k ∨ M✶.eRk P.right = k := by
--   obtain rfl | hne := eq_or_ne k ⊤
--   · simp_rw [top_add, ← top_le_iff]
--     refine iff_of_true h.weaklyConnected fun P hP ↦ ?_
--     by_contra! hcon
--     grw [← eConn_le_eRk, P.eConn_left] at hcon
--     exact hP.not_gt hcon.1
--   simp only [weaklyConnected_iff_forall, ENat.add_le_add_right_iff, ENat.one_ne_top, or_false]
--   refine ⟨fun h' ↦ ?_, fun h' P hPconn hP ↦ ?_⟩
--   · rintro P rfl
--     specialize h' P rfl.le
--     simp only [isStrongSeparation_iff_eRk hne, not_and, not_lt] at h'
--     nth_rw 1 [← P.eConn_left, ← P.eConn_right, ← P.eConn_left, ← P.eConn_right]
--     simp only [le_antisymm_iff, eConn_le_eRk .., eConn_le_eRk_dual, and_true]
--     simp only [eConn_left, eConn_right]
--     grind
--   obtain hlt | rfl := hPconn.lt_or_eq
--   · exact h.not_isTutteSeparation (P := P) (Order.add_one_le_of_lt hlt) hP.isTutteSeparation
--   rw [isStrongSeparation_iff_eRk (by eomega)] at hP
--   grind

-- lemma TutteConnected.exists_of_not_weaklyConnected_add_one (h : M.TutteConnected (k + 1))
--     (h' : ¬ M.WeaklyConnected (k + 1 + 1)) :
--     ∃ (P : M.Partition), P.eConn = k ∧ k < M.eRk P.left ∧ k < M.eRk P.right ∧
--       k < M✶.eRk P.left ∧ k < M✶.eRk P.right := by
--   simp only [h.weaklyConnected_add_one_iff, not_forall, exists_prop, not_or] at h'
--   obtain ⟨P, rfl, h1, h2, h3, h4⟩ := h'
--   refine ⟨P, rfl, lt_of_le_of_ne' ?_ h1, lt_of_le_of_ne' ?_ h2, lt_of_le_of_ne' ?_ h3,
--   lt_of_le_of_ne' ?_ h4⟩
--   · grw [← P.eConn_left, eConn_le_eRk]
--   · grw [← P.eConn_right, eConn_le_eRk]
--   · grw [← P.eConn_left, eConn_le_eRk_dual]
--   grw [← P.eConn_right, eConn_le_eRk_dual]

/-- A matroid is weakly internally `(k+1)` connected if all separations of order at most `k-1`
are degenerate in the sense that one side is 'nearly' independent and coindependent.
Internal `(k+1)`-connectivity is the conjunction of weak internal `(k+1)`-connectivity and
Tutte `k`-connectivity. -/
def WeaklyInternallyConnected (M : Matroid α) :=
    M.NumConnected (fun M X ↦ M.nullity X + M✶.nullity X ≤ 1)

lemma weaklyInternallyConnected_iff_forall : M.WeaklyInternallyConnected (k + 1) ↔
    ∀ P : M.Partition, P.eConn + 1 ≤ k → ¬ P.IsInternalSeparation :=
  numConnected_iff_forall

lemma TutteConnected.weaklyInternallyConnected (h : M.TutteConnected k) :
    M.WeaklyInternallyConnected k :=
  NumConnected.mono_degen h <| by simp +contextual [← nullity_eq_zero]

lemma weaklyInternallyConnected_iff_numConnected_encard (hk : k ≠ ⊤) :
    M.WeaklyInternallyConnected k ↔ M.NumConnected (fun M X ↦ X.encard ≤ M.eConn X + 1) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp [WeaklyInternallyConnected]
  simp only [weaklyInternallyConnected_iff_forall, numConnected_iff_forall, isPredSeparation_iff,
    eConn_left, not_le, eConn_right]
  refine ⟨fun h P hPk hP ↦ h P hPk ?_, fun h P hPk hP ↦ h P hPk ?_⟩
  · rwa [isInternalSeparation_iff_encard (by enat_to_nat!)]
  rwa [← isInternalSeparation_iff_encard (by enat_to_nat!)]

/-- `M` is internally `(k+1)`-connected if it is weakly `(k+1)`-connected and `k`-Tutte-connected.-/
structure InternallyConnected (M : Matroid α) (k : ℕ∞) : Prop where
    weaklyInternallyConnected : M.WeaklyInternallyConnected k
    tutteConnected' : M.TutteConnected (k-1)

lemma InternallyConnected.tutteConnected (h : M.InternallyConnected (k+1)) :
    M.TutteConnected k := by
  have h' := h.2
  enat_to_nat <;> simpa using h'

lemma internallyConnected_iff' :
    M.InternallyConnected k ↔ M.NumConnected (fun M X ↦ M.nullity X + M✶.nullity X ≤ 1) k ∧
      M.TutteConnected (k-1) :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma internallyConnected_iff :
    M.InternallyConnected (k + 1) ↔ M.WeaklyInternallyConnected (k + 1) ∧ M.TutteConnected k := by
  rw [internallyConnected_iff', ENat.add_sub_cancel_right _ (by simp)]
  rfl

@[simp]
lemma internallyConnected_zero (M : Matroid α) : M.InternallyConnected 0 := by
  simp [internallyConnected_iff']

@[simp]
lemma internallyConnected_one (M : Matroid α) : M.InternallyConnected 1 := by
  simp [internallyConnected_iff']

lemma internallyConnected_iff_forall : M.InternallyConnected (k + 1) ↔
    ∀ (P : M.Partition), (P.eConn + 1 + 1 ≤ k → ¬ P.IsTutteSeparation) ∧
      (P.eConn + 1 = k → ¬ P.IsInternalSeparation) := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp only [ENat.add_one_le_add_one_iff, ENat.add_one_inj, internallyConnected_iff,
    tutteConnected_iff_forall, weaklyInternallyConnected_iff_forall]
  refine ⟨fun h P ↦ ⟨fun hPc ↦ h.2 P hPc, fun hPc ↦ h.1 P hPc.le⟩,
    fun h ↦ ⟨fun P hP hPi ↦ ?_, fun P hP ↦ (h P).1 hP⟩⟩
  obtain rfl | hlt := hP.eq_or_lt
  · simpa [hPi] using h P
  exact (h P).1 (Order.add_one_le_of_lt hlt) hPi.isTutteSeparation

lemma InternallyConnected.not_isTutteSeparation (h : M.InternallyConnected (k + 1))
    (hP : P.eConn + 1 + 1 ≤ k) : ¬ P.IsTutteSeparation :=
  ((internallyConnected_iff_forall.1 h) P).1 hP

lemma InternallyConnected.not_isInternalSeparation (h : M.InternallyConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ¬ P.IsInternalSeparation := by
  obtain hlt | rfl := hP.lt_or_eq
  · exact fun h' ↦ h.not_isTutteSeparation (Order.add_one_le_of_lt hlt) h'.isTutteSeparation
  rw [internallyConnected_iff_forall] at h
  exact (h P).2 rfl

lemma TutteConnected.internallyConnected (h : M.TutteConnected k) : M.InternallyConnected k :=
  ⟨h.weaklyInternallyConnected, h.mono tsub_le_self⟩

lemma TutteConnected.internallyConnected_iff_forall (h : M.TutteConnected k) :
    M.InternallyConnected (k + 1) ↔
    ∀ P : M.Partition, P.eConn + 1 = k → ¬ P.IsInternalSeparation := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [tutteConnected_iff_forall] at h
  simp only [internallyConnected_iff_forall, ENat.add_one_le_add_one_iff, ENat.add_one_inj,
    forall_and, and_iff_right_iff_imp]
  exact fun _ ↦ h

lemma WeaklyConnected.weaklyConnected_of_isRestriction {N : Matroid α} (h : M.WeaklyConnected k)
    (hN : N ≤r M) (hNM : ∀ e, M.IsNonloop e → e ∉ N.E → ∃ f ∈ N.E, e ∈ M.closure {f}) :
    N.WeaklyConnected k := by
  obtain rfl | ⟨k,rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  obtain hNe | ⟨f₀, hf₀⟩ := N.E.eq_empty_or_nonempty
  · exact numConnected_of_subsingleton (by simp [hNe]) _ (by simp)
  replace hNM : ∀ e ∈ M.E, ∃ f ∈ N.E, e ∈ M.closure {f} ∧ (e ∈ N.E → e = f) := by
    intro e he
    by_cases heN : e ∈ N.E
    · exact ⟨e, heN, M.mem_closure_of_mem rfl, by simp⟩
    obtain he' | he' := M.isLoop_or_isNonloop e
    · exact ⟨f₀, hf₀, he'.mem_closure {f₀}, by simp [heN]⟩ 
    obtain ⟨f, hf, hef⟩ := hNM e he' heN 
    exact ⟨f, hf, hef, by simp [heN]⟩ 
  choose! φ hφ using hNM
  rw [weaklyConnected_iff_forall] at *
  intro P hPk hP
  let Q := M.partition (φ ⁻¹' P.1 ∩ M.E)
  have hQl : Q.1 = φ ⁻¹' P.1 ∩ M.E := rfl
  have h' : φ ⁻¹' N.E ∩ M.E = M.E := inter_eq_right.2 fun x hx ↦ (hφ x hx).1
  have hQr : Q.2 = φ ⁻¹' P.2 ∩ M.E := by
    rw [← Q.compl_left, hQl, diff_inter_self_eq_diff, ← P.compl_left, preimage_diff,
      diff_inter_right_comm, h']
  have hss1 : P.1 ⊆ φ ⁻¹' P.1 := fun x hx ↦ by rwa [mem_preimage,
    ← (hφ x (hN.subset (P.left_subset_ground hx))).2.2 (P.left_subset_ground hx)]
  have hss2 : P.2 ⊆ φ ⁻¹' P.2 := fun x hx ↦ by rwa [mem_preimage,
    ← (hφ x (hN.subset (P.right_subset_ground hx))).2.2 (P.right_subset_ground hx)]
  have hcl2 : Q.2 ⊆ M.closure P.2 := by
    rw [hQr]
    rintro x ⟨hx : φ x ∈ P.right, hxE : x ∈ M.E⟩
    grw [← singleton_subset_iff.2 hx]
    exact (hφ x hxE).2.1
  have hcl1 : Q.1 ⊆ M.closure P.1 := by
    rintro x ⟨hx : φ x ∈ P.left, hxE : x ∈ M.E⟩
    grw [← singleton_subset_iff.2 hx]
    exact (hφ x hxE).2.1
  refine h Q ?_ ?_
  · grw [← hPk, Partition.eConn_eq_eLocalConn, eLocalConn_mono _ hcl1 hcl2,
      eLocalConn_closure_closure, P.eConn_eq_eLocalConn, hN.eLocalConn_eq_of_subset]
  rw [isStrongSeparation_iff']
  refine ⟨(hP.dep_left.of_isRestriction hN).superset ?_,
    (hP.dep_right.of_isRestriction hN).superset ?_, 
    (hP.isVerticalSeparation.nonspanning_left.of_isRestriction hN).closure_nonspanning.subset hcl1, 
    (hP.isVerticalSeparation.nonspanning_right.of_isRestriction hN).closure_nonspanning.subset hcl2⟩
  · grw [hQl, subset_inter_iff, and_iff_right hss1, P.left_subset_ground, hN.subset]
  grw [hQr, subset_inter_iff, and_iff_right hss2, P.right_subset_ground, hN.subset]

lemma WeaklyConnected.delete_of_forall_exists_parallel (h : M.WeaklyConnected k)
    {D : Set α} (hD : ∀ e ∈ D, M.IsNonloop e → ∃ f ∉ D, M.Parallel e f) :
    (M ＼ D).WeaklyConnected k := by
  by_cases hDE : M.E ⊆ D
  · exact numConnected_of_subsingleton (by simp [diff_eq_empty.2 hDE]) _ (by simp)
  obtain ⟨f', hf'⟩ := not_subset.1 hDE  
  refine h.weaklyConnected_of_isRestriction (delete_isRestriction ..) fun e henl heD ↦ ?_
  replace heD := show e ∈ D by simpa [henl.mem_ground] using heD
  obtain ⟨f, hf⟩ := hD e heD henl
  exact ⟨f, ⟨hf.2.mem_ground_right, hf.1⟩, hf.2.mem_closure⟩  

lemma WeaklyConnected.delete_weaklyConnected_of_parallel {e f : α} (h : M.WeaklyConnected k)
    (hef : M.Parallel e f) (hne : e ≠ f) : (M ＼ {e}).WeaklyConnected k :=
  h.delete_of_forall_exists_parallel <| by grind

lemma WeaklyConnected.weaklyConnected_of_isSimplification {N : Matroid α} (h : M.WeaklyConnected k)
    (hN : N.IsSimplification M) : N.WeaklyConnected k := by
  refine h.weaklyConnected_of_isRestriction hN.isRestriction fun e henl _ ↦ ?_
  obtain ⟨f, hf, -⟩ := hN.exists_unique henl
  exact ⟨f, hf.1, hf.2.mem_closure⟩ 

  
  
  





      -- P.right_subset_ground, inter_subset_left, delete_ground,
      -- diff_union_of_subset hDE, and_iff_right rfl.subset, subset_diff, inter_subset_left,
      -- P.right_subset_ground, delete_ground]
  --   rw [← compl_left, subset_antisymm_iff, diff_subset_iff, ← P.compl_left, delete_ground, hQ]
  --   simp


-- lemma foo (h : M.InternallyConnected (k+1)) (hnot : ¬ M.TutteConnected (k+1)) :











-- def IsInternallyConnected' (M : Matroid α) (k : ℕ∞) :=
--     M.PredConnected (fun j M X ↦ ((j+3 ≤ k) → M.Indep X ∧ M.Coindep X))
--                     (fun j M X ↦ ((j+3 ≤ k) → M.Indep X ∧ M.Coindep X))
--                     ∧ (j + 2 = k → M.nullity X + M✶.nullity X ≤ 1)





end Matroid
