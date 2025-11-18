import Matroid.Connectivity.Separation
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Matroid.Constructions
import Mathlib.Tactic.Peel

open Set

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b d k : ℕ∞} {A X Y : Set α} {P : M.Partition}

namespace Matroid



section abstract

variable {dg dg' : Matroid α → Set α → Prop}

namespace Partition

/-! ### Abstract Separations -/

/-- An abstract notion of nondegenerate separation : given a predicate on sets in `M`,
`P.IsPredSeparation` means that neither side of `P` satisfies the degeneracy predicate. -/
@[mk_iff]
structure IsPredSeparation (degen : Matroid α → Set α → Prop) (P : M.Partition) : Prop where
    not_degen_left : ¬ degen M P.left
    not_degen_right : ¬ degen M P.right

lemma IsPredSeparation.dual (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M✶ X)
    (hP : P.IsPredSeparation dg) : P.dual.IsPredSeparation dg' :=
  ⟨fun h ↦ hP.not_degen_left (by simpa using hdg (M := M✶) P.left_subset_ground h),
    fun h ↦ hP.not_degen_right (by simpa using hdg (M := M✶) P.right_subset_ground h)⟩

lemma IsPredSeparation.dual_compl (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M✶ (M.E \ X))
    (hP : P.IsPredSeparation dg) : P.dual.IsPredSeparation dg' :=
  ⟨fun h ↦ hP.not_degen_right <| by simpa using hdg (M := M✶) P.left_subset_ground h,
    fun h ↦ hP.not_degen_left <| by simpa using hdg (M := M✶) P.right_subset_ground h⟩

lemma IsPredSeparation.of_dual (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg M X → dg M✶ X)
    (hP : P.dual.IsPredSeparation dg) : P.IsPredSeparation dg :=
  ⟨by simpa using (hP.dual hdg).1, by simpa using (hP.dual hdg).2⟩

lemma isPredSeparation_dual_iff (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg M X → dg M✶ X) :
    P.dual.IsPredSeparation dg ↔ P.IsPredSeparation dg :=
  ⟨IsPredSeparation.of_dual hdg, IsPredSeparation.dual hdg⟩

lemma isPredSeparation_ofDual_iff {P : M✶.Partition} (hdg : ∀ ⦃M X⦄, X ⊆ M.E → dg M X → dg M✶ X) :
    P.ofDual.IsPredSeparation dg ↔ P.IsPredSeparation dg := by
  rw [← isPredSeparation_dual_iff hdg, ofDual_dual]

lemma IsPredSeparation.symm (hP : P.IsPredSeparation dg) : P.symm.IsPredSeparation dg :=
  ⟨hP.2, hP.1⟩

lemma IsPredSeparation.of_symm (hP : P.symm.IsPredSeparation dg) : P.IsPredSeparation dg :=
  ⟨hP.2, hP.1⟩

lemma isPredSeparation_symm {dg} : P.symm.IsPredSeparation dg = P.IsPredSeparation dg := by
  ext
  exact ⟨IsPredSeparation.of_symm, IsPredSeparation.symm⟩

lemma IsPredSeparation.mono {dg dg' : Matroid α → Set α → Prop}
    (h_imp : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M X) (hP : P.IsPredSeparation dg) :
    P.IsPredSeparation dg' :=
  ⟨fun h ↦ hP.not_degen_left <| h_imp P.left_subset_ground h,
    fun h ↦ hP.not_degen_right <| h_imp P.right_subset_ground h⟩

lemma IsPredSeparation.mono_symm {dg dg' : Matroid α → Set α → Prop}
    (h_imp : ∀ ⦃M X⦄, X ⊆ M.E → dg' M X → dg M (M.E \ X)) (hP : P.IsPredSeparation dg) :
    P.IsPredSeparation dg' := by
  simpa [isPredSeparation_iff] using (hP.mono (dg' := fun M X ↦ dg' M (M.E \ X))
    (fun M X hX h' ↦ diff_diff_cancel_left hX ▸ h_imp diff_subset h')).symm

/-! ### Tutte Separations -/

abbrev IsTutteSeparation (P : M.Partition) := IsPredSeparation (fun M X ↦ M.Indep X ∧ M.Coindep X) P

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
lemma isTutteSeparation_symm : P.symm.IsTutteSeparation = P.IsTutteSeparation :=
  isPredSeparation_symm

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
  simp [add_assoc, ENat.lt_add_right_iff, hP, IsTutteSeparation, isPredSeparation_iff]

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

/-! ### Vertical Separations -/

/-- A vertical separation is one with both sides nonspanning. -/
abbrev IsVerticalSeparation (P : M.Partition) := IsPredSeparation Matroid.Spanning P

@[simp]
lemma isVerticalSeparation_symm : P.symm.IsVerticalSeparation = P.IsVerticalSeparation :=
  isPredSeparation_symm

lemma IsVerticalSeparation.isTutteSeparation (h : P.IsVerticalSeparation) :
    P.IsTutteSeparation :=
  h.mono_symm fun _ _ _ hsp ↦ hsp.2.compl_spanning

lemma isVerticalSeparation_iff :
    P.IsVerticalSeparation ↔ M.Nonspanning P.left ∧ M.Nonspanning P.right := by
  simp [IsVerticalSeparation, isPredSeparation_iff]

lemma IsVerticalSeparation.nonspanning_left (h : P.IsVerticalSeparation) : M.Nonspanning P.left :=
  (isVerticalSeparation_iff.1 h).1

lemma IsVerticalSeparation.nonspanning_right (h : P.IsVerticalSeparation) : M.Nonspanning P.right :=
  (isVerticalSeparation_iff.1 h).2

/-! ### Cyclic Separations -/

/-- A cyclic separation is one with both sides dependent. -/
abbrev IsCyclicSeparation (P : M.Partition) := IsPredSeparation Matroid.Indep P

@[simp]
lemma isCyclicSeparation_symm : P.symm.IsCyclicSeparation = P.IsCyclicSeparation :=
  isPredSeparation_symm

lemma IsVerticalSeparation.dual (h : P.IsVerticalSeparation) : P.dual.IsCyclicSeparation :=
  h.dual_compl fun _ _ _ hsp ↦ hsp.coindep.compl_spanning

lemma IsCyclicSeparation.dual (h : P.IsCyclicSeparation) : P.dual.IsVerticalSeparation :=
  h.dual_compl fun _ _ _ hd ↦ hd.compl_coindep

lemma IsCyclicSeparation.IsTutteSeparation (h : P.IsCyclicSeparation) :
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
  simp [isCyclicSeparation_iff, isVerticalSeparation_iff, ← nonspanning_compl_iff, and_comm]

@[simp]
lemma isVerticalSeparation_dual_iff : P.dual.IsVerticalSeparation ↔ P.IsCyclicSeparation := by
  simp [isCyclicSeparation_iff, isVerticalSeparation_iff, nonspanning_dual_iff, and_comm]

@[simp]
lemma isCyclicSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsCyclicSeparation ↔ P.IsVerticalSeparation := by
  rw [← isVerticalSeparation_dual_iff, ofDual_dual]

@[simp]
lemma isVerticalSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsVerticalSeparation ↔ P.IsCyclicSeparation := by
  rw [← isCyclicSeparation_dual_iff, ofDual_dual]

/-! ### Strong Separations -/

/-- A strong separation is one where both sides are dependent and nonspanning. -/
abbrev IsStrongSeparation (P : M.Partition) :=
  IsPredSeparation (fun M X ↦ M.Indep X ∨ M.Coindep X) P

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
    M.Dep P.left ∧ M.Dep P.right ∧ M.Nonspanning P.left ∧ M.Nonspanning P.right := by
  simp only [IsStrongSeparation, isPredSeparation_iff, not_or, Partition.left_subset_ground,
    not_indep_iff, dual_ground, dep_dual_iff, ← nonspanning_compl_iff, compl_left,
    Partition.right_subset_ground, compl_right]
  tauto

end Partition

lemma Dep.partition_isTutteSeparation_of_nonspanning (hX : M.Dep X) (hX' : M.Nonspanning X) :
    (M.partition X).IsTutteSeparation := by
  simp [Partition.isTutteSeparation_iff', hX, hX']

lemma Nonspanning.partition_isVerticalSeparation (hX : M.Nonspanning X)
    (hXc : M.Nonspanning (M.E \ X)) : (M.partition X).IsVerticalSeparation := by
  simp [Partition.isVerticalSeparation_iff, hX, hXc]

lemma Dep.partition_isCyclicSeparation (hX : M.Dep X) (hXc : M.Dep (M.E \ X)) :
    (M.partition X).IsCyclicSeparation := by
  simp [Partition.isCyclicSeparation_iff, hX, hXc]

lemma Dep.partition_isStrongSeparation (hX : M.Dep X) (hns : M.Nonspanning X)
    (hXc : M.Dep (M.E \ X)) (hXsc : M.Nonspanning (M.E \ X)) :
    (M.partition X).IsStrongSeparation := by
  simp_all [Partition.isStrongSeparation_iff]

variable {dg dg' : ℕ∞ → Matroid α → Set α → Prop}

/-! ### Abstract Connectivity -/

/-- An abstract notion of connectivity. `dg` is a predicate-valued function that for each `t`,
specifies what it means for a set `X` with connectivity `t` to be degenerate in a matroid `M`.
`PredConnected dg M` means that in `M`, every set of connectivity `t` either satisfies
`dg t`, or its complement satisfies `dg t`.

For instance, for `k`-Tutte-connectivity, sets of connectivity `k-1` or higher are not degenerate,
and sets of connectivity `k-2` or less are degenerate iff they are independent and coindependent. -/
def PredConnected (dg : ℕ∞ → Matroid α → Set α → Prop) (M : Matroid α) :=
    ∀ P : M.Partition, dg P.eConn M P.left ∨ dg P.eConn M P.right

lemma not_predConnected_iff :
    ¬ M.PredConnected dg ↔ ∃ P : M.Partition, P.IsPredSeparation (dg P.eConn) := by
  simp [PredConnected, Partition.isPredSeparation_iff]

lemma PredConnected.not_IsPredSeparation (h : M.PredConnected dg) (P : M.Partition) :
    ¬ P.IsPredSeparation (dg P.eConn) := by
  contrapose! h
  rw [not_predConnected_iff]
  exact ⟨P, h⟩

lemma PredConnected.mono' (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → (dg' k M X ∨ dg' k M (M.E \ X)))
    (h : M.PredConnected dg) : M.PredConnected dg' := by
  refine fun P ↦ ?_
  obtain h1 | h2 := h P
  · exact P.compl_left ▸ hdegen P.left_subset_ground h1
  rw [or_comm]
  exact P.compl_right ▸ hdegen P.right_subset_ground h2

lemma PredConnected.mono (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M X)
    (h : M.PredConnected dg) : M.PredConnected dg' :=
  h.mono' fun _ _ _ hX h' ↦ .inl (hdegen hX h')

lemma PredConnected.mono_compl (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M (M.E \ X))
    (h : M.PredConnected dg) : M.PredConnected dg' :=
  h.mono' fun _ _ _ hX h' ↦ .inr (hdegen hX h')

lemma PredConnected.dual' (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X →
    (dg' k M✶ X ∨ dg' k M✶ (M.E \ X))) (h : M.PredConnected dg) :
    M✶.PredConnected dg' :=
  fun P ↦ by simpa using h.mono' (dg' := fun k N Y ↦ dg' k N✶ Y) (by simpa) P.ofDual

lemma PredConnected.dual_compl (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M✶ (M.E \ X))
    (h : M.PredConnected dg) : M✶.PredConnected dg' :=
  fun P ↦ by simpa using h.mono_compl (dg' := fun k N Y ↦ dg' k N✶ Y) (by simpa) P.ofDual

lemma PredConnected.dual (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → dg k M X → dg' k M✶ X)
    (h : M.PredConnected dg) : M✶.PredConnected dg' :=
  fun P ↦ by simpa using h.mono (dg' := fun k N Y ↦ dg' k N✶ Y) (by simpa) P.ofDual

/-! ### Tutte Connectivity -/

def TutteConnected (M : Matroid α) (k : ℕ∞) :=
    M.PredConnected (fun j M X ↦ j + 2 ≤ k → M.Indep X ∧ M.Coindep X)

lemma not_tutteConnected_iff_exists :
    ¬ M.TutteConnected k ↔ ∃ P : M.Partition, P.eConn + 2 ≤ k ∧ P.IsTutteSeparation := by
  simp [TutteConnected, not_predConnected_iff, Partition.IsTutteSeparation,
    Partition.isPredSeparation_iff, ← and_and_left]

lemma TutteConnected.dual (h : M.TutteConnected k) : M✶.TutteConnected k := by
  refine PredConnected.dual (fun t N X hX h' hle ↦ ?_) h
  rw [dual_coindep_iff, and_comm]
  exact h' hle

lemma TutteConnected.of_dual (h : M✶.TutteConnected k) : M.TutteConnected k :=
  M.dual_dual ▸ h.dual

lemma TutteConnected.mono (h : M.TutteConnected k) (hjk : j ≤ k) : M.TutteConnected j :=
  PredConnected.mono (fun _ _ _ _ h' hle ↦ h' (hle.trans hjk)) h

@[simp]
lemma tutteConnected_one (M : Matroid α) : M.TutteConnected 1 := by
  by_contra! hcon
  obtain ⟨P, hPle, -⟩ := not_tutteConnected_iff_exists.1 hcon
  generalize P.eConn = b at *
  enat_to_nat
  linarith

@[simp]
lemma tutteConnected_zero (M : Matroid α) : M.TutteConnected 0 :=
  M.tutteConnected_one.mono <| zero_le ..

lemma tutteConnected_of_le_one (M : Matroid α) (hk : k ≤ 1) : M.TutteConnected k := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by enat_to_nat; omega <;> simp

@[simp]
lemma tutteConnected_dual_iff : M✶.TutteConnected = M.TutteConnected := by
  ext k
  exact ⟨TutteConnected.of_dual, TutteConnected.dual⟩

lemma Indep.exists_IsTutteSeparation_of_codep {I : Set α} (hI : M.Indep I) (hd : M.Codep I) :
    ∃ P : M.Partition, P.left ⊆ I ∧ M.IsCocircuit P.left ∧ P.eConn ≤ M.eConn I := by
  obtain ⟨C, hCI, hC⟩ := hd.exists_isCocircuit_subset
  refine ⟨M.partition C, hCI, hC, ?_⟩
  grw [← Partition.eConn_left, partition_left _ _, (hI.subset hCI).eConn_eq, hI.eConn_eq]
  exact M✶.eRk_mono hCI

lemma Partition.IsTutteSeparation.not_tutteConnected (hP : P.IsTutteSeparation) :
    ¬ M.TutteConnected (P.eConn + 2) := by
  rw [not_tutteConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma TutteConnected.not_isTutteSeparation (h : M.TutteConnected k)
    (hP : P.eConn + 2 ≤ k) : ¬ P.IsTutteSeparation :=
  fun h' ↦ h'.not_tutteConnected <| h.mono hP

lemma tutteConnected_of_subsingleton (h : M.E.Subsingleton) (k : ℕ∞) : M.TutteConnected k := by
  by_contra! hcon
  obtain ⟨P, -, hP⟩ := not_tutteConnected_iff_exists.1 hcon
  grw [← encard_le_one_iff_subsingleton,
    ← encard_diff_add_encard_of_subset P.left_subset_ground, P.compl_left] at h
  have h1 := hP.nonempty_left.encard_pos
  have h2 := hP.nonempty_right.encard_pos
  generalize P.left.encard = a at *
  generalize P.right.encard = b at *
  -- This is a bad case for `enat_to_nat`, which doesn't correctly simplify away the infinite cases.
  enat_to_nat
  · simp at h
  · omega
  · simp at h
  omega

/-- In a matroid that isn't `k`-connected, there is either a strong separation, or
a separation arising from a small circuit or cocircuit. -/
lemma exists_strong_or_small_of_not_tutteConnected (h : ¬ M.TutteConnected k) :
    ∃ P : M.Partition, P.eConn + 2 ≤ k ∧ (P.IsStrongSeparation ∨
        (M.Indep P.left ∧ M.IsHyperplane P.right ∧ P.left.encard + 1 ≤ k) ∨
        (M.IsCircuit P.left ∧ M.Spanning P.right ∧ P.left.encard + 1 ≤ k)) := by
  obtain ⟨P, hP⟩ := not_tutteConnected_iff_exists.1 h
  revert hP
  apply Partition.wlog_symm_dual (property := Matroid.Indep) (P₀ := P)
  · exact fun N P aux hP ↦ aux (by simpa using hP)
  · refine fun N P aux hP ↦ ?_
    obtain ⟨Q, hQk, hQ⟩ := aux (by simpa using hP)
    rw [← Q.coindep_left_iff, dual_coindep_iff, ← Q.isCocircuit_left_iff, dual_isCocircuit_iff,
      ← isCocircuit_def, ← Q.ofDual_left, ← coindep_def, Q.ofDual.coindep_left_iff,
      Q.ofDual.isCocircuit_left_iff,  ← and_assoc, ← and_assoc, and_comm (b := Indep ..),
      or_comm (b := _ ∧ _), and_comm (b := IsCircuit ..), and_assoc, and_assoc] at hQ
    exact ⟨Q.ofDual, by simpa, by simpa⟩
  · rintro N P hi ⟨hPconn, hP⟩
    obtain ⟨Q, hQP, hQ1, hQle⟩ := hi.exists_IsTutteSeparation_of_codep (hP.codep_of_indep_left hi)
    grw [← P.eConn_left, ← hQle] at hPconn
    rw [Q.isCocircuit_left_iff] at hQ1
    refine ⟨Q, hPconn, .inr (.inl ⟨hi.subset hQP, hQ1, ?_⟩)⟩
    grw [← N.eConn_add_nullity_add_nullity_dual _ Q.left_subset_ground, Q.eConn_left,
      (Q.isCocircuit_left_iff.2 hQ1).nullity_eq, (hi.subset hQP).nullity_eq, add_zero, add_assoc]
    exact hPconn
  refine fun N Q h1 h2 h3 h4 ⟨hQconn, hQ⟩ ↦ ⟨Q, hQconn, .inl ?_⟩
  simp only [Partition.left_subset_ground, not_indep_iff, Partition.right_subset_ground,
    dual_ground, dep_dual_iff, Q.codep_left_iff, Q.codep_right_iff] at h1 h2 h3 h4
  simp [Partition.isStrongSeparation_iff, h1, h2, h3, h4]

lemma exists_strong_or_small_of_not_tutteConnected' (h : ¬ M.TutteConnected k) :
    ∃ P : M.Partition, P.eConn + 2 ≤ k ∧ (P.IsStrongSeparation ∨
      (M.Indep P.left ∧ M.IsHyperplane P.right ∧ M.Dep P.right ∧ P.left.encard + 1 ≤ k) ∨
      (M.IsCircuit P.left ∧ M.Nonspanning P.left ∧ M.Spanning P.right ∧ P.left.encard + 1 ≤ k)) := by
  obtain ⟨P, hP⟩ := not_tutteConnected_iff_exists.1 h
  revert hP
  apply Partition.wlog_symm_dual (property := Matroid.Indep) (P₀ := P)
  · exact fun N P aux hP ↦ aux (by simpa using hP)
  · refine fun N P aux hP ↦ ?_
    obtain ⟨Q, hQk, hQ⟩ := aux (by simpa using hP)
    rw [← Q.coindep_left_iff, dual_coindep_iff, ← Q.isCocircuit_left_iff, dual_isCocircuit_iff,
      ← isCocircuit_def, ← Q.ofDual_left, ← coindep_def, Q.ofDual.coindep_left_iff,
      Q.ofDual.isCocircuit_left_iff, Partition.nonspanning_dual_left_iff, ← Q.ofDual_right,
      dep_dual_iff, Q.ofDual.codep_right_iff, ← Partition.isStrongSeparation_ofDual_iff] at hQ
    exact ⟨Q.ofDual, by simpa, by tauto⟩
  · rintro N P hi ⟨hPconn, hP⟩
    obtain ⟨Q, hQP, hQ1, hQle⟩ := hi.exists_IsTutteSeparation_of_codep (hP.codep_of_indep_left hi)
    grw [← P.eConn_left, ← hQle] at hPconn
    rw [Q.isCocircuit_left_iff] at hQ1
    refine ⟨Q, hPconn, .inr (.inl ⟨hi.subset hQP, hQ1, ?_⟩)⟩
    grw [← N.eConn_add_nullity_add_nullity_dual _ Q.left_subset_ground, Q.eConn_left,
      (Q.isCocircuit_left_iff.2 hQ1).nullity_eq, (hi.subset hQP).nullity_eq, add_zero, add_assoc]
    have:= hP.dep_of_spanning_left
    exact hPconn
  refine fun N Q h1 h2 h3 h4 ⟨hQconn, hQ⟩ ↦ ⟨Q, hQconn, .inl ?_⟩
  simp only [Partition.left_subset_ground, not_indep_iff, Partition.right_subset_ground,
    dual_ground, dep_dual_iff, Q.codep_left_iff, Q.codep_right_iff] at h1 h2 h3 h4
  simp [Partition.isStrongSeparation_iff, h1, h2, h3, h4]


/-! ### Vertical Connectivity -/

def VerticallyConnected (M : Matroid α) (k : ℕ∞) :=
    M.PredConnected (fun j M X ↦ j + 2 ≤ k → M.Spanning X)

lemma VerticallyConnected.mono (h : M.VerticallyConnected k) (hjk : j ≤ k) :
    M.VerticallyConnected j :=
  PredConnected.mono (fun _ _ _ _ h' hle ↦ h' (hle.trans hjk)) h

lemma TutteConnected.verticallyConnected (h : M.TutteConnected k) : M.VerticallyConnected k :=
  PredConnected.mono_compl (fun _ _ _ _ h1 h2 ↦ (h1 h2).2.compl_spanning) h

lemma not_verticallyConnected_iff_exists :
    ¬ M.VerticallyConnected k ↔ ∃ P : M.Partition, P.eConn + 2 ≤ k ∧ P.IsVerticalSeparation := by
  simp [VerticallyConnected, not_predConnected_iff, Partition.IsVerticalSeparation,
    Partition.isPredSeparation_iff, ← and_and_left]

lemma Partition.IsVerticalSeparation.not_verticallyConnected (hP : P.IsVerticalSeparation) :
    ¬ M.VerticallyConnected (P.eConn + 2) := by
  rw [not_verticallyConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma VerticallyConnected.not_isVerticalSeparation (h : M.VerticallyConnected k)
    (hP : P.eConn + 2 ≤ k) : ¬ P.IsVerticalSeparation :=
  fun h' ↦ h'.not_verticallyConnected <| h.mono hP

lemma verticallyConnected_top_iff :
    M.VerticallyConnected ⊤ ↔ ∀ X ⊆ M.E, M.Spanning X ∨ M.Spanning (M.E \ X) := by
  simp only [VerticallyConnected, PredConnected, le_top, forall_const]
  exact ⟨fun h X hX ↦ by simpa using h (M.partition X),
    fun h P ↦ by simpa [P.compl_left] using h _ P.left_subset_ground⟩

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
    (freeOn E).VerticallyConnected k ↔ E.Subsingleton ∨ k ≤ 1 := by
  obtain hE | hE := E.subsingleton_or_nontrivial
  · simp [((freeOn E).tutteConnected_of_subsingleton hE k).verticallyConnected, hE]
  obtain hle | hlt : k ≤ 1 ∨ 2 ≤ k := by enat_to_nat; simp; omega
  · simp [hle]
  simp only [show ¬(k ≤ 1) by enat_to_nat; omega, or_false, hE.not_subsingleton, iff_false]
  intro h
  obtain ⟨x, hx, y, hy, hne⟩ := hE
  refine h.not_isVerticalSeparation (P := (freeOn E).partition {x} (by simpa))
    (by simpa [← loopyOn_dual_eq]) ?_
  suffices ¬ {x} = E by simpa [Partition.isVerticalSeparation_iff, nonspanning_iff, hx]
  rintro rfl
  exact hne.symm (by simpa using hy)

@[simp]
lemma loopyOn_tutteConnected_iff (E : Set α) :
    (loopyOn E).TutteConnected k ↔ E.Subsingleton ∨ k ≤ 1 := by
  rw [← tutteConnected_dual_iff, loopyOn_dual_eq]
  refine ⟨fun h ↦ (verticallyConnected_freeOn_iff E k).1 h.verticallyConnected, ?_⟩
  rintro (h | h)
  · exact tutteConnected_of_subsingleton h _
  exact tutteConnected_of_le_one _ h

@[simp]
lemma freeOn_tutteConnected_iff (E : Set α) :
    (freeOn E).TutteConnected k ↔ E.Subsingleton ∨ k ≤ 1 := by
  rw [← tutteConnected_dual_iff, freeOn_dual_eq, loopyOn_tutteConnected_iff]

lemma foo (hnt : M.E.Nontrivial) :
    M.TutteConnected k ↔ M.VerticallyConnected k ∧ k ≤ M.girth := by
  obtain ⟨E, rfl⟩ | hpos := M.exists_eq_freeOn_or_rankPos_dual
  · simp
  rw [← not_iff_not]
  refine ⟨fun h ⟨h', hlt⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨P, hPconn, (hP | ⟨hi, hh, hcard⟩ | hP)⟩ :=
      exists_strong_or_small_of_not_tutteConnected h
    · exact h'.not_isVerticalSeparation hPconn hP.isVerticalSeparation
    · refine h'.not_isVerticalSeparation hPconn ?_
      rw [Partition.isVerticalSeparation_iff, and_iff_left hh.nonspanning, ← not_spanning_iff]
      intro hsp
      grw [← hcard, girth_le_eRank_add_one, ← hi.eRk_eq_encard, hsp.eRk_eq] at hlt
      exact hlt.ne rfl
    grw [← hP.2.2, hP.1.girth_le_card, ← le_self_add] at hlt
    exact hlt.ne rfl
  intro htutte

      -- obtain h1 | h2 := M✶.eq_loopyOn_or_rankPos
      -- · obtain ⟨E, rfl⟩ : ∃ E, M = freeOn E := ⟨M.E, by simpa [← eq_dual_iff_dual_eq] using h1⟩
      --   simp at h'


      -- grw [← hcard, ENat.add_one_lt_add_one_iff, ] at


--     have := M.eq_loopyOn_or_rankPos
--     grw [← hP.2.2, hP.1.girth_le_card] at hlt
--     exact hlt.ne rfl


/-! #-/



-- lemma TutteConnected.deleteElem (h : M.TutteConnected (k+1)) (e : α) :
--     (M ＼ {e}).TutteConnected k := by
--   contrapose h
--   rw [not_TutteConnected_iff_exists]
--   obtain ⟨X, hXss, hXconn, hX⟩ := exists_dep_nonspanning_or_small_of_not_tutteConnected h
--   obtain ⟨hXE : X ⊆ M.E, heX : e ∉ X⟩ := subset_diff_singleton_iff.1 hXss
--   obtain (hX | hX | hX) := hX
--   ·
--     refine ⟨X, hXE, ?_, fun _ ↦ ?_, ?_⟩
-- lemma exists_dep_nonspanning_of_not_tutteConnected (hM : k ≤ M.eRank + 2)
-- (hMd : k ≤ M✶.eRank + 2)
--     (h : ¬ M.TutteConnected k) : ∃ X ⊆ M.E, M.eConn X + 2 ≤ k ∧
--       ((M.Dep X ∧ M.Dep (M.E \ X) ∧ ¬ M.Spanning X ∧ ¬ M.Spanning (M.E \ X))) := by
--   obtain ⟨X, hXE, hXconn, h1 | ⟨hXi, hXc, hle⟩ | h3⟩ :=
--     exists_dep_nonspanning_or_small_of_not_tutteConnected h
--   · exact ⟨X, hXE, hXconn, h1⟩
--   · rw []
    -- grw [← hXc.compl_isHyperplane.eRk_add_one_eq] at hM








def IsInternallyConnected' (M : Matroid α) (k : ℕ∞) :=
    M.PredConnected (fun j M X ↦ ((j+3 ≤ k) → M.Indep X ∧ M.Coindep X)
      ∧ (j + 2 = k → M.nullity X + M✶.nullity X ≤ 1))


end abstract


end Matroid
