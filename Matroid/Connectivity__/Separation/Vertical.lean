import Matroid.Connectivity.Separation.Tutte


variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Separation}
  {b : Bool}


open Set Matroid Matroid.Separation

namespace Matroid.Separation

/-! ### Vertical Separations -/

/-- A vertical separation is one with both sides nonspanning. -/
abbrev IsVerticalSeparation (P : M.Separation) : Prop :=
  IsPredSeparation (fun _ ↦ Matroid.Coindep) P

@[simp]
lemma isVerticalSeparation_symm_iff : P.symm.IsVerticalSeparation ↔ P.IsVerticalSeparation :=
  isPredSeparation_symm_iff

lemma IsVerticalSeparation.symm (hP : P.IsVerticalSeparation) : P.symm.IsVerticalSeparation :=
  IsPredSeparation.symm hP

lemma IsVerticalSeparation.of_symm (hP : P.symm.IsVerticalSeparation) : P.IsVerticalSeparation := by
  simpa using IsPredSeparation.symm hP

lemma IsVerticalSeparation.isTutteSeparation (h : P.IsVerticalSeparation) :
    P.IsTutteSeparation :=
  h.mono <| by simp [tutteDegen_iff]

lemma isVerticalSeparation_iff_forall : P.IsVerticalSeparation ↔ ∀ b, M.Codep (P b) := by
  simp [IsVerticalSeparation, IsPredSeparation]

lemma isVerticalSeparation_iff : P.IsVerticalSeparation ↔ M.Codep (P false) ∧ M.Codep (P true) := by
  simp [isVerticalSeparation_iff_forall]

lemma isVerticalSeparation_iff_forall_nonspanning :
    P.IsVerticalSeparation ↔ ∀ b, M.Nonspanning (P b) := by
  simp_rw [isVerticalSeparation_iff_forall, Bool.forall_bool (p := fun _ ↦ M.Codep _),
    Bool.forall_bool' !false, nonspanning_not_iff, Bool.not_false]

lemma not_isVerticalSeparation_iff_exists : ¬ P.IsVerticalSeparation ↔ ∃ b, M.Coindep (P b) := by
  simp_rw [isVerticalSeparation_iff_forall, not_forall, P.not_codep_iff]

lemma not_isVerticalSeparation_iff_exists_spanning :
    ¬ P.IsVerticalSeparation ↔ ∃ b, M.Spanning (P b) := by
  simp_rw [isVerticalSeparation_iff_forall_nonspanning, not_forall, P.not_nonspanning_iff]

lemma IsVerticalSeparation.nonspanning (h : P.IsVerticalSeparation) (b : Bool) :
    M.Nonspanning (P b) :=
  (isVerticalSeparation_iff_forall_nonspanning.1 h) b

lemma IsVerticalSeparation.codep (h : P.IsVerticalSeparation) (b : Bool) : M.Codep (P b) :=
  (isVerticalSeparation_iff_forall.1 h) b

lemma isVerticalSeparation_iff_eRk (h : P.eConn ≠ ⊤) :
    P.IsVerticalSeparation ↔ ∀ b, P.eConn < M.eRk (P b) := by
  convert isVerticalSeparation_iff_forall with b
  rw [← P.eConn_eq b, ← M.eConn_add_nullity_dual_eq_eRk (P b), ENat.lt_add_left_iff]
  simp [h]

lemma isVerticalSeparation_iff_nullity_dual :
    P.IsVerticalSeparation ↔ ∀ b, 1 ≤ M✶.nullity (P b) := by
  convert isVerticalSeparation_iff_forall with b
  simp [ENat.one_le_iff_ne_zero]

lemma isVerticalSeparation_of_lt_lt (h : P.eConn < M.eRk (P b)) (h' : P.eConn < M.eRk (P !b)) :
    P.IsVerticalSeparation := by
  rwa [isVerticalSeparation_iff_eRk (fun h0 ↦ by simp [h0] at h), b.forall_bool', and_iff_left h']

lemma IsVerticalSeparation.eRk_ge (h : P.IsVerticalSeparation) (b : Bool) :
    P.eConn + 1 ≤ M.eRk (P b) := by
  grw [← M.eConn_add_nullity_dual_eq_eRk (P b), (h.codep b).one_le_nullity, P.eConn_eq]

/-! ### Cyclic Separations -/

/-- A cyclic separation is one with both sides dependent. -/
abbrev IsCyclicSeparation (P : M.Separation) : Prop := IsPredSeparation (fun _ ↦ Matroid.Indep) P

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

lemma isCyclicSeparation_iff_forall : P.IsCyclicSeparation ↔ ∀ b, M.Dep (P b) := by
  simp [IsCyclicSeparation, IsPredSeparation]

lemma IsCyclicSeparation.dep (h : P.IsCyclicSeparation) (b : Bool) : M.Dep (P b) :=
  (isCyclicSeparation_iff_forall.1 h) b

@[simp]
lemma isCyclicSeparation_dual_iff : P.dual.IsCyclicSeparation ↔ P.IsVerticalSeparation := by
  simp [isCyclicSeparation_iff_forall, isVerticalSeparation_iff_forall]

@[simp]
lemma isVerticalSeparation_dual_iff : P.dual.IsVerticalSeparation ↔ P.IsCyclicSeparation := by
  simp [isCyclicSeparation_iff_forall, isVerticalSeparation_iff_forall]

@[simp]
lemma isCyclicSeparation_ofDual_iff {P : M✶.Separation} :
    P.ofDual.IsCyclicSeparation ↔ P.IsVerticalSeparation := by
  rw [← isVerticalSeparation_dual_iff, ofDual_dual]

@[simp]
lemma isVerticalSeparation_ofDual_iff {P : M✶.Separation} :
    P.ofDual.IsVerticalSeparation ↔ P.IsCyclicSeparation := by
  rw [← isCyclicSeparation_dual_iff, ofDual_dual]

lemma isCyclicSeparation_iff_eRk_dual (h : P.eConn ≠ ⊤) :
    P.IsCyclicSeparation ↔ ∀ b, P.eConn < M✶.eRk (P b) := by
  rw [← isVerticalSeparation_dual_iff, isVerticalSeparation_iff_eRk (by simpa)]
  simp

lemma isCyclicSeparation_iff_nullity : P.IsCyclicSeparation ↔ ∀ b, 1 ≤ M.nullity (P b) := by
  rw [← isVerticalSeparation_dual_iff, isVerticalSeparation_iff_nullity_dual]
  simp

lemma not_isCyclicSeparation_iff : ¬ P.IsCyclicSeparation ↔ ∃ b, M.Indep (P b) := by
  simp_rw [isCyclicSeparation_iff_forall, not_forall, P.not_dep_iff]

lemma IsCyclicSeparation.eRk_dual_ge (h : P.IsCyclicSeparation) : P.eConn + 1 ≤ M✶.eRk (P b) := by
  simpa using h.dual.eRk_ge b

/-! ### Strict Separations -/

/-- A strict separation is one where both sides are dependent and nonspanning. -/
abbrev IsStrictSeparation (P : M.Separation) : Prop :=
  IsPredSeparation (fun _ M X ↦ M.Indep X ∨ M.Coindep X) P

@[simp]
lemma isStrictSeparation_symm_iff : P.symm.IsStrictSeparation ↔ P.IsStrictSeparation :=
  isPredSeparation_symm_iff

@[simp]
lemma isStrictSeparation_dual_iff : P.dual.IsStrictSeparation ↔ P.IsStrictSeparation :=
  isPredSeparation_dual_iff <| by simp [or_comm]

@[simp]
lemma isStrictSeparation_ofDual_iff {P : M✶.Separation} :
    P.ofDual.IsStrictSeparation ↔ P.IsStrictSeparation := by
  rw [← isStrictSeparation_dual_iff, ofDual_dual]

alias ⟨IsStrictSeparation.of_dual, IsStrictSeparation.dual⟩ := isStrictSeparation_dual_iff

lemma IsStrictSeparation.isCyclicSeparation (h : P.IsStrictSeparation) : P.IsCyclicSeparation :=
  h.mono <| by simp +contextual

lemma IsStrictSeparation.isVerticalSeparation (h : P.IsStrictSeparation) :
    P.IsVerticalSeparation := by
  simpa using h.dual.isCyclicSeparation

lemma IsStrictSeparation.isTutteSeparation (h : P.IsStrictSeparation) : P.IsTutteSeparation :=
  h.isVerticalSeparation.isTutteSeparation

lemma isStrictSeparation_iff : P.IsStrictSeparation ↔ (∀ b, M.Dep (P b)) ∧ ∀ b, M.Codep (P b) := by
  simp_rw [IsStrictSeparation, IsPredSeparation, not_or, P.not_indep_iff, P.not_coindep_iff,
    forall_and]

lemma not_isStrictSeparation_iff :
    ¬ P.IsStrictSeparation ↔ ∃ b, M.Indep (P b) ∨ M.Coindep (P b) := by
  simp_rw [isStrictSeparation_iff, Classical.not_and_iff_not_or_not, ← P.not_indep_iff,
    ← P.not_coindep_iff, not_forall_not, exists_or]

lemma isStrictSeparation_iff' :
    P.IsStrictSeparation ↔ (∀ b, M.Dep (P b)) ∧ (∀ b, M.Nonspanning (P b)) := by
  rw [isStrictSeparation_iff, and_congr_right_iff]
  rintro -
  rw [true.forall_bool', (!true).forall_bool', nonspanning_not_iff, nonspanning_not_iff]

lemma IsStrictSeparation.dep (h : P.IsStrictSeparation) (b : Bool) : M.Dep (P b) :=
  h.isCyclicSeparation.dep b

lemma IsStrictSeparation.codep (h : P.IsStrictSeparation) (b : Bool) : M.Codep (P b) :=
  h.isVerticalSeparation.codep b

lemma IsStrictSeparation.nonspanning (h : P.IsStrictSeparation) (b : Bool) : M.Nonspanning (P b) :=
  h.isVerticalSeparation.nonspanning b

lemma IsStrictSeparation.encard_ge (h : P.IsStrictSeparation) : P.eConn + 2 ≤ (P b).encard := by
  grw [← P.eConn_eq b, ← M.eConn_add_nullity_add_nullity_dual (P b), ← (h.dep b).one_le_nullity,
    ← (h.codep b).one_le_nullity, add_assoc, one_add_one_eq_two]

lemma isStrictSeparation_iff_eRk (hP : P.eConn ≠ ⊤) : P.IsStrictSeparation ↔
    (∀ b, P.eConn < M.eRk (P b)) ∧ (∀ b, P.eConn < M✶.eRk (P b)) := by
  rw [and_comm]
  convert isStrictSeparation_iff with b b
  · rw [← ENat.add_one_le_iff hP, ← M.eConn_add_nullity_eq_eRk_dual (P b)]
    simp [hP, ENat.one_le_iff_ne_zero]
  rw [← ENat.add_one_le_iff hP, ← M.eConn_add_nullity_dual_eq_eRk (P b)]
  simp [hP, ENat.one_le_iff_ne_zero]

/-- A Tutte separation with connectivity zero is either strict,
or has one side only loops or coloops. -/
lemma isTutteSeparation_iff_isStrictSeparation_of_zero (hP : P.eConn = 0) : P.IsTutteSeparation ↔
    P.IsStrictSeparation ∨ ((∀ b, (P b).Nonempty) ∧ (∃ b, P b ⊆ M.loops ∨ P b ⊆ M.coloops)) := by
  rw [isStrictSeparation_iff_eRk (by simp [hP]), isTutteSeparation_iff_lt_encard (by simp [hP]), hP]
  simp_rw [pos_iff_ne_zero, encard_ne_zero, Ne, eRk_eq_zero_iff', dual_ground,
    inter_eq_self_of_subset_left P.subset_ground, dual_loops]
  by_cases hne : ∀ b, (P b).Nonempty
  · grind
  rw [iff_false_intro hne, false_iff, false_and, or_false, Classical.not_and_iff_not_or_not,
    not_forall_not, not_forall_not]
  simp_rw [nonempty_iff_ne_empty, not_forall_not] at hne
  obtain ⟨b, hb⟩ := hne
  exact .inl ⟨b, by simp [hb]⟩

end Separation

lemma Dep.ofSetSep_isTutteSeparation_of_nonspanning (hX : M.Dep X) (hX' : M.Nonspanning X)
    (b : Bool) : (M.ofSetSep X b).IsTutteSeparation := by
  rw [isTutteSeparation_iff' b, ofSetSep_apply_self, ofSetSep_apply_not, and_iff_left (.inr hX')]
  exact .inl hX

lemma Nonspanning.ofSetSep_isVerticalSeparation (hX : M.Nonspanning X)
    (hXc : M.Nonspanning (M.E \ X)) (b : Bool) : (M.ofSetSep X b).IsVerticalSeparation := by
  rwa [Separation.isVerticalSeparation_iff_forall_nonspanning, b.forall_bool', ofSetSep_apply_self,
    ofSetSep_apply_not, and_iff_right hX]

lemma Codep.ofSetSep_isVerticalSeparation (hX : M.Codep X) (hXc : M.Nonspanning X) (b : Bool) :
    (M.ofSetSep X b).IsVerticalSeparation := by
  rw [Separation.isVerticalSeparation_iff_forall_nonspanning, b.forall_bool']
  simp [hXc, hX.nonspanning_compl]

lemma Codep.ofSetSep_isTutteSeparation_of_dep_compl (hX : M.Codep X) (hXc : M.Dep (M.E \ X)) :
    (M.ofSetSep X b).IsTutteSeparation := by
  rw [Separation.isTutteSeparation_iff_forall, b.forall_bool']
  simp [hX, hXc]

lemma Dep.ofSetSep_isCyclicSeparation (hX : M.Dep X) (hXc : M.Dep (M.E \ X)) :
    (M.ofSetSep X b).IsCyclicSeparation := by
  rw [Separation.isCyclicSeparation_iff_forall, b.forall_bool']
  simp [hX, hXc]

lemma Dep.ofSetSep_isStrictSeparation (hX : M.Dep X) (hns : M.Nonspanning X)
    (hXc : M.Dep (M.E \ X)) (hXsc : M.Nonspanning (M.E \ X)) :
    (M.ofSetSep X b).IsStrictSeparation := by
  rw [Separation.isStrictSeparation_iff, b.forall_bool', b.forall_bool']
  rw [nonspanning_compl_iff] at hXsc
  simp [hXc, hX, hns.codep_compl, hXsc]

lemma TutteConnected.not_isCyclicSeparation (h : M.TutteConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ¬ P.IsCyclicSeparation :=
  fun hP' ↦ h.not_isTutteSeparation hP hP'.isTutteSeparation

lemma TutteConnected.not_isVerticalSeparation (h : M.TutteConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ¬ P.IsVerticalSeparation :=
  fun hP' ↦ h.not_isTutteSeparation hP hP'.isTutteSeparation

/-- In a matroid that isn't `(k + 1)`-connected, there is either a strong separation, or
a separation arising from a small circuit or cocircuit. -/
lemma exists_strong_or_small_of_not_tutteConnected (h : ¬ M.TutteConnected (k + 1)) (b : Bool) :
    ∃ P : M.Separation, P.eConn + 1 ≤ k ∧ P.IsTutteSeparation ∧
    (P.IsStrictSeparation ∨ ((P b).encard ≤ k ∧
    ((M.Indep (P b) ∧ M.IsHyperplane (P !b)) ∨ (M.IsCircuit (P b) ∧ M.Spanning (P !b))))) := by
  obtain ⟨P, hPconn, hP⟩ := not_tutteConnected_iff_exists.1 h
  by_cases hPs : P.IsStrictSeparation
  · exact ⟨P, hPconn, hP, .inl hPs⟩
  wlog hi : M.Indep (P b) generalizing P M with aux
  · obtain ⟨i, (hi | hci)⟩ := Separation.not_isStrictSeparation_iff.1 hPs
    · obtain rfl | rfl := i.eq_or_eq_not b
      · contradiction
      exact aux h P.symm (by simpa) (by simpa) (by simpa) hi
    suffices aux' : ∃ Q : M✶.Separation,
        Q.eConn + 1 ≤ k ∧ Q.IsTutteSeparation ∧ ¬ Q.IsStrictSeparation ∧ M✶.Indep (Q b) by
      obtain ⟨Q, hQconn, hQsep, hQsep', hQb⟩ := aux'
      obtain ⟨P', hP'k, hP't, hP' | hP'⟩ :=
        aux (by simpa) Q (by simpa) (by simpa) (by simpa) (by simpa)
      · exact ⟨P'.ofDual, by simpa, by simpa, .inl (by simpa)⟩
      rw [or_comm, isHyperplane_not_iff, spanning_not_iff, ← isCocircuit_def,
        ← isHyperplane_compl_iff_isCocircuit, ← coindep_def, coindep_iff_compl_spanning,
        ← dual_ground, P'.compl_eq, dual_isCocircuit_iff, spanning_not_iff, dual_coindep_iff,
        and_comm (b := Indep ..), and_comm (b := IsCircuit ..), ← Separation.ofDual_apply,
          ← spanning_not_iff, Separation.ofDual_apply] at hP'
      exact ⟨P'.ofDual, by simpa, by simpa, .inr (by simpa)⟩
    obtain rfl | rfl := i.eq_or_eq_not b
    · exact ⟨P.dual, by simpa, by simpa, by simpa, by simpa⟩
    exact ⟨P.symm.dual, by simpa, by simpa, by simpa, by simpa⟩
  obtain ⟨Q, hQt, hQP, hQb, hQconn⟩ := hP.exists_of_indep hi
  grw [← hQconn] at hPconn
  replace hi := hi.subset hQP
  have hQcard : (Q b).encard ≤ k := by
    grw [← M.eConn_add_nullity_add_nullity_dual (Q b), hi.nullity_eq, add_zero,
      hQb.isCircuit.nullity_eq, Q.eConn_eq, hPconn]
  rw [← isHyperplane_not_iff] at hQb
  exact ⟨Q, hPconn, hQt, .inr ⟨hQcard, .inl ⟨hi, hQb⟩⟩⟩


/-! ### Vertical Connectivity -/

def VerticallyConnected (M : Matroid α) := M.NumConnected Matroid.Coindep

lemma VerticallyConnected.mono (h : M.VerticallyConnected k) (hjk : j ≤ k) :
    M.VerticallyConnected j :=
  NumConnected.mono h hjk

@[gcongr]
lemma VerticallyConnected.mono' (hjk : j ≤ k) (h : M.VerticallyConnected k) :
    M.VerticallyConnected j := h.mono hjk

lemma TutteConnected.verticallyConnected (h : M.TutteConnected k) : M.VerticallyConnected k :=
  NumConnected.mono_degen h <| fun _ _ ↦ TutteDegen.coindep

lemma not_verticallyConnected_iff_exists : ¬ M.VerticallyConnected (k+1) ↔
    ∃ P : M.Separation, P.eConn + 1 ≤ k ∧ P.IsVerticalSeparation :=
  not_numConnected_iff_exists

lemma verticallyConnected_iff_forall : M.VerticallyConnected (k + 1) ↔
    ∀ (P : M.Separation), P.eConn + 1 ≤ k → ¬ P.IsVerticalSeparation := by
  rw [← not_iff_not]
  simp [not_verticallyConnected_iff_exists]

lemma VerticallyConnected.exists_eRk_eq (h : M.VerticallyConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ∃ i, M.eRk (P i) = P.eConn := by
  by_contra! hcon
  replace hcon := fun i ↦ (hcon i).symm.lt_of_le <| by grw [← P.eConn_eq i, eConn_le_eRk]
  rw [verticallyConnected_iff_forall] at h
  exact h P hP <| by rwa [isVerticalSeparation_iff_eRk (fun h ↦ by simpa [h] using hcon true)]

lemma verticallyConnected_iff_forall_exists_eRk_le (hk : k ≠ ⊤) : M.VerticallyConnected (k + 1) ↔
    ∀ (P : M.Separation), P.eConn + 1 ≤ k → ∃ i, M.eRk (P i) ≤ P.eConn := by
  refine ⟨fun h P hPk ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨i, hi⟩ := h.exists_eRk_eq hPk
    exact ⟨i, hi.le⟩
  rw [verticallyConnected_iff_forall]
  intro P hPk hP
  obtain ⟨i, hle⟩ := h P hPk
  rw [isVerticalSeparation_iff_eRk (by enat_to_nat!)] at hP
  exact (hP i).not_ge hle

lemma VerticallyConnected.exists_spanning (h : M.VerticallyConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ∃ i, M.Spanning (P i) := by
  by_contra! hcon
  refine verticallyConnected_iff_forall.1 h P hP ?_
  rw [isVerticalSeparation_iff_forall_nonspanning]
  simpa using hcon

lemma VerticallyConnected.exists_coindep (h : M.VerticallyConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ∃ i, M.Coindep (P i) := by
  obtain ⟨i, hi⟩ := h.exists_spanning hP
  exact ⟨!i, by simpa using hi.compl_coindep⟩

lemma Separation.IsVerticalSeparation.not_verticallyConnected (hP : P.IsVerticalSeparation) :
    ¬ M.VerticallyConnected (P.eConn + 1 + 1) := by
  rw [not_verticallyConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma VerticallyConnected.not_isVerticalSeparation (h : M.VerticallyConnected (k + 1))
    (hP : P.eConn + 1 ≤ k) : ¬ P.IsVerticalSeparation :=
  fun h' ↦ h'.not_verticallyConnected <| h.mono <| by simpa

lemma VerticallyConnected.compl_spanning_of_nonspanning_of_eConn_le
    (h : M.VerticallyConnected (k + 1)) (hX : M.Nonspanning X) (hconn : M.eConn X + 1 ≤ k) :
    M.Spanning (M.E \ X) := by
  replace h := h.exists_spanning (P := M.ofSetSep X true) (by simpa)
  simpa [hX.not_spanning] using h

lemma verticallyConnected_top_iff :
    M.VerticallyConnected ⊤ ↔ ∀ X ⊆ M.E, M.Spanning X ∨ M.Spanning (M.E \ X) := by
  rw [← top_add (a := 1), verticallyConnected_iff_forall]
  simp only [le_top, isVerticalSeparation_iff_forall_nonspanning, Bool.forall_bool, not_and,
    Separation.not_nonspanning_iff, forall_const]
  refine ⟨fun h X hX ↦ ?_,
    fun h P hP ↦ by simpa [hP.not_spanning] using h (P false) P.subset_ground⟩
  rw [or_iff_not_imp_right, not_spanning_iff]
  simpa using h (M.ofSetSep X true)

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
  refine h.not_isVerticalSeparation (P := (freeOn E).ofSetSep {x} true (by simpa))
    (by simp [← loopyOn_dual_eq]) ?_
  suffices ¬ {x} = E by simpa [Separation.isVerticalSeparation_iff_forall_nonspanning,
    nonspanning_iff, hx]
  rintro rfl
  exact hne.symm (by simpa using hy)

lemma verticallyConnected_iff_seqConnected : M.VerticallyConnected (k + 1) ↔
    M.SeqConnected (fun M ↦ M✶.nullity) (indicator {i | k < i + 1} ⊤) := by
  simp_rw [verticallyConnected_iff_forall, isVerticalSeparation_iff_forall, not_forall,
    Separation.not_codep_iff, seqConnected_iff_exists]
  convert Iff.rfl with P
  obtain h | h := le_or_gt (P.eConn + 1) k <;>
  simp [h]

/-! ### Cyclic connectivity -/

def CyclicallyConnected (M : Matroid α) (k : ℕ∞) := M.NumConnected Matroid.Indep k

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
    ∃ P : M.Separation, P.eConn + 1 ≤ k ∧ P.IsCyclicSeparation :=
  not_numConnected_iff_exists

lemma cyclicallyConnected_iff_forall : M.CyclicallyConnected (k + 1) ↔
    ∀ (P : M.Separation), P.eConn + 1 ≤ k → ¬ P.IsCyclicSeparation :=
  numConnected_iff_forall

lemma cyclicallyConnected_iff_seqConnected : M.CyclicallyConnected (k + 1) ↔
    M.SeqConnected Matroid.nullity (indicator {i | k < i + 1} ⊤) := by
  rw [← verticallyConnected_dual_iff, verticallyConnected_iff_seqConnected, seqConnected_dual_iff]
  simp

lemma Separation.IsCyclicSeparation.not_cyclicallyConnected (hP : P.IsCyclicSeparation) :
    ¬ M.CyclicallyConnected (P.eConn + 1 + 1) := by
  rw [not_cyclicallyConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma CyclicallyConnected.not_isCyclicSeparation (h : M.CyclicallyConnected k)
    (hP : P.eConn + 1 + 1 ≤ k) : ¬ P.IsCyclicSeparation :=
  fun h' ↦ h'.not_cyclicallyConnected <| h.mono hP

lemma CyclicallyConnected.compl_indep_of_dep_of_eConn_le (h : M.CyclicallyConnected (k + 1))
    (hX : M.Dep X) (hXconn : M.eConn X + 1 ≤ k) : M.Indep (M.E \ X) := by
  have h' := h.not_isCyclicSeparation (P := M.ofSetSep X true) (by simpa)
  simpa [isCyclicSeparation_iff_forall, hX] using h'

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

/-- This needs the lower bound on co-rank; otherwise an extension of a large free matroid by
a loop would be a counterexample for any `k`. -/
lemma CyclicallyConnected.le_girth (h : M.CyclicallyConnected k) (hlt : k ≤ M✶.eRank) :
    k ≤ M.girth := by
  obtain (rfl | ⟨k, rfl⟩) := k.eq_zero_or_exists_eq_add_one; simp
  rw [← not_lt, girth_lt_iff, not_exists]
  rintro C ⟨hC, hCcard⟩
  refine h.not_isCyclicSeparation (P := M.ofSetSep C true) ?_ ?_
  · grw [eConn_ofSetSep, hC.eConn_add_one_eq, eRk_le_encard]
    exact Order.add_one_le_of_lt hCcard
  suffices ¬ M.Indep (M.E \ C) by simpa [Separation.isCyclicSeparation_iff_forall, hC.dep]
  intro hi
  rw [← dual_coindep_iff, ← dual_ground, ← spanning_iff_compl_coindep] at hi
  grw [← M✶.eRk_le_encard, hi.eRk_eq] at hCcard
  exact hCcard.not_ge hlt






  -- obtain ⟨P, hPconn, hP⟩ := not_cyclicallyConnected_iff_exists.1 hM
  -- have := hN.not_isCyclicSeparation (P := P.induce h.subset)
  -- grw [eConn_induce_le_of_isMinor h.isRestriction.isMinor] at this


-- lemma CyclicallyConnected.exists_isCircuit_of_delete {e : α}
-- (h : (M ＼ {e}).CyclicallyConnected k)
--     (hM : ¬ M.CyclicallyConnected k) : ∃ C, M.IsCircuit C ∧ e ∈ C ∧ C.encard = k := by
--   obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp at hM
--   have heE : e ∈ M.E := by_contra fun heE ↦ hM <| by rwa [← deleteElem_eq_self heE]
--   obtain ⟨P, hPconn, hP⟩ := not_cyclicallyConnected_iff_exists.1 hM
--   obtain ⟨i, hi⟩ := P.exists_mem heE

lemma VerticallyConnected.tutteConnected_of_girth_ge (h : M.VerticallyConnected k) (hk : k ≠ ⊤)
    (h_girth : k ≤ M.girth) : M.TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [tutteConnected_iff_forall_exists_encard_le (by simpa using hk)]
  intro P hPconn
  obtain ⟨i, hi⟩ := h.exists_eRk_eq hPconn
  use i
  rw [← hi, Indep.eRk_eq_encard]
  exact indep_of_eRk_add_one_lt_girth <| by enat_to_nat!; lia

/-- This needs the strict inequality in the hypothesis, since nothing like this can be true
for `k = ⊤`. This is also false for matroids like `U₂,₅` if there is no lower bound on size. -/
lemma tutteConnected_iff_verticallyConnected_girth (hlt : 2 * k < M.E.encard + 1) :
    M.TutteConnected (k + 1) ↔ M.VerticallyConnected (k + 1) ∧ k + 1 ≤ M.girth :=
  ⟨fun h ↦ ⟨h.verticallyConnected, h.girth_ge (by enat_to_nat! <;> lia)⟩,
    fun h ↦ h.1.tutteConnected_of_girth_ge (by enat_to_nat!) h.2⟩

lemma tutteConnected_iff_verticallyConnected_cyclicallyConnected (hlt : 2 * k < M.E.encard) :
    M.TutteConnected (k + 1) ↔ M.VerticallyConnected (k + 1) ∧ M.CyclicallyConnected (k + 1) := by
  wlog hcon : k + 1 ≤ M✶.eRank generalizing M with aux
  · have hle' : k + 1 ≤ M.eRank := by
      rw [← eRank_add_eRank_dual] at hlt
      enat_to_nat! <;> lia
    rw [← tutteConnected_dual_iff, aux (by simpa) (by simpa), and_comm]
    simp
  exact ⟨fun h ↦ ⟨h.verticallyConnected, h.cyclicallyConnected⟩,
    fun ⟨hv, hc⟩ ↦ hv.tutteConnected_of_girth_ge (by enat_to_nat!) <| hc.le_girth hcon⟩

lemma VerticallyConnected.contract {C : Set α} (h : M.VerticallyConnected (k + M.eRk C)) :
    (M ／ C).VerticallyConnected k := by
  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← M.contract_inter_ground_eq]
    exact aux (h.mono (by grw [eRk_mono _ inter_subset_left])) inter_subset_right
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [add_right_comm] at h
  refine verticallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  refine h.not_isVerticalSeparation (P := P.ofContract true) ?_ ?_
  · grw [eConn_ofContract, Bool.not_true, eLocalConn_le_eRk_right, add_right_comm, hPconn]
  rw [isVerticalSeparation_iff_forall_nonspanning, Bool.forall_bool, ofContract_true_false,
    ofContract_apply_self]
  rw [isVerticalSeparation_iff_forall_nonspanning, Bool.forall_bool, contract_nonspanning_iff,
    contract_nonspanning_iff] at hP
  exact ⟨hP.1.1.subset subset_union_left, hP.2.1⟩

lemma VerticallyConnected.contract_of_top (h : M.VerticallyConnected ⊤) (C : Set α) :
    (M ／ C).VerticallyConnected ⊤ :=
  (h.mono le_top).contract

lemma VerticallyConnected.of_isSpanningRestriction (h : N.VerticallyConnected k) (hNM : N ≤sr M) :
    M.VerticallyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine verticallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  obtain ⟨i, hsp⟩ := h.exists_spanning (P := P.induce hNM.subset)
    <| by grw [eConn_induce_le_of_isMinor _ hNM.isRestriction.isMinor, hPconn]
  exact (hP.nonspanning i).not_spanning <| (hNM.spanning_of_spanning hsp).superset <| by simp

lemma VerticallyConnected.of_simplifies (h : M.VerticallyConnected k) (hNM : N ≤si M) :
    N.VerticallyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine verticallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  obtain ⟨Q, hQP, hQconn⟩ := Separation.exists_of_simplifies P hNM
  obtain ⟨i, hi⟩ := h.exists_spanning (P := Q) (by grw [hQconn, hPconn])
  refine (hP.nonspanning i).not_spanning ?_
  rw [hNM.isSpanningRestriction.spanning_iff, spanning_iff, ← (hQP i).2, hi.closure_eq]
  simp [P.subset.trans hNM.isRestriction.subset]

lemma Simplifies.verticallyConnected_iff (hNM : N ≤si M) :
    N.VerticallyConnected k ↔ M.VerticallyConnected k :=
  ⟨fun h ↦ h.of_isSpanningRestriction hNM.isSpanningRestriction, fun h ↦ h.of_simplifies hNM⟩

lemma verticallyConnected_two_iff : M.VerticallyConnected 2 ↔ M.removeLoops.TutteConnected 2 :=
  ⟨fun h ↦ (h.of_simplifies M.removeLoops_simplifies).tutteConnected_of_girth_ge (by simp)
    (by simp [removeLoops_loopless]), fun h ↦ h.verticallyConnected.of_isSpanningRestriction
    M.removeLoops_simplifies.isSpanningRestriction⟩

/-- `M` is vertically `3`-connected if and only if its simplification is `3`-connected. -/
lemma IsSimplification.verticallyConnected_three_iff (hNM : N.IsSimplification M) :
    M.VerticallyConnected 3 ↔ N.TutteConnected 3 :=
  ⟨fun h ↦ (h.of_simplifies hNM.simplifies).tutteConnected_of_girth_ge (by simp)
    <| three_le_girth_iff.2 hNM.simple,
    fun h ↦ h.verticallyConnected.of_isSpanningRestriction hNM.isSpanningRestriction⟩

lemma IsSimplification.tutteConnected_of_verticallyConnected_three (hNM : N.IsSimplification M)
    (hM : M.VerticallyConnected 3) : N.TutteConnected 3 := by
  rwa [← hNM.verticallyConnected_three_iff]

@[simp]
lemma verticallyConnected_three_iff [M.Simple] : M.VerticallyConnected 3 ↔ M.TutteConnected 3 :=
  isSimplification_self.verticallyConnected_three_iff

lemma TutteConnected.contract {C : Set α} (h : M.TutteConnected (k + M.eRk C + 1))
    (hnt : 2 * (k + M.eRk C) < M.E.encard + 1) : (M ／ C).TutteConnected (k + 1) := by
  obtain rfl | hne := eq_or_ne k 0; simp
  wlog hCE : C ⊆ M.E generalizing C with aux
  · specialize aux (C := C ∩ M.E)
    grw [M.eRk_mono inter_subset_left, imp_iff_right inter_subset_right,
      contract_inter_ground_eq] at aux
    exact aux h hnt
  have hnt' := Order.le_of_lt_add_one hnt
  have hgirth := h.girth_ge hnt'
  have hC : M.Indep C := indep_of_eRk_add_one_lt_girth (by enat_to_nat! <;> lia) hCE
  have hfin : C.Finite := not_infinite.1 fun hinf ↦ by
    simp [hC.eRk_eq_encard, hinf.encard_eq] at hnt
  refine VerticallyConnected.tutteConnected_of_girth_ge ?_ (by enat_to_nat!) ?_
  · rw [add_right_comm] at h
    exact h.verticallyConnected.contract
  grw [M.girth_le_girth_contract_add C, add_right_comm,
    WithTop.add_le_add_iff_right ((M.isRkFinite_of_finite hfin).eRk_lt_top.ne)] at hgirth
  assumption

lemma TutteConnected.delete {D : Set α} (h : M.TutteConnected (k + M✶.eRk D + 1))
    (hnt : 2 * (k + M✶.eRk D) < M.E.encard + 1) : (M ＼ D).TutteConnected (k + 1) :=
  dual_contract_dual .. ▸ (h.dual.contract (by simpa)).dual

lemma TutteConnected.contractElem (h : M.TutteConnected (k + 1)) (hnt : 2 * k < M.E.encard + 1)
    (e : α) : (M ／ {e}).TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine TutteConnected.contract (h.mono (by grw [eRk_singleton_le])) ?_
  grw [eRk_singleton_le]
  assumption

lemma TutteConnected.deleteElem (h : M.TutteConnected (k + 1)) (hnt : 2 * k < M.E.encard + 1)
    (e : α) : (M ＼ {e}).TutteConnected k := by
  simpa using (h.dual.contractElem hnt e).dual


end Matroid
