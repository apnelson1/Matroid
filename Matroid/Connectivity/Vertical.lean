import Matroid.Connectivity.Tutte


variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Partition}
  {b : Bool}


open Set Matroid Matroid.Partition

namespace Matroid.Partition

/-! ### Vertical Separations -/

/-- A vertical separation is one with both sides nonspanning. -/
abbrev IsVerticalSeparation (P : M.Partition) : Prop :=
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
  h.mono <| by simp

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
abbrev IsCyclicSeparation (P : M.Partition) : Prop := IsPredSeparation (fun _ ↦ Matroid.Indep) P

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
lemma isCyclicSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsCyclicSeparation ↔ P.IsVerticalSeparation := by
  rw [← isVerticalSeparation_dual_iff, ofDual_dual]

@[simp]
lemma isVerticalSeparation_ofDual_iff {P : M✶.Partition} :
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

/-! ### Strong Separations -/

/-- A strong separation is one where both sides are dependent and nonspanning. -/
abbrev IsStrongSeparation (P : M.Partition) : Prop :=
  IsPredSeparation (fun _ M X ↦ M.Indep X ∨ M.Coindep X) P

@[simp]
lemma isStrongSeparation_symm_iff : P.symm.IsStrongSeparation ↔ P.IsStrongSeparation :=
  isPredSeparation_symm_iff

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

lemma isStrongSeparation_iff : P.IsStrongSeparation ↔ (∀ b, M.Dep (P b)) ∧ ∀ b, M.Codep (P b) := by
  simp_rw [IsStrongSeparation, IsPredSeparation, not_or, P.not_indep_iff, P.not_coindep_iff,
    forall_and]

lemma not_isStrongSeparation_iff :
    ¬ P.IsStrongSeparation ↔ ∃ b, M.Indep (P b) ∨ M.Coindep (P b) := by
  simp_rw [isStrongSeparation_iff, Classical.not_and_iff_not_or_not, ← P.not_indep_iff,
    ← P.not_coindep_iff, not_forall_not, exists_or]

lemma isStrongSeparation_iff' :
    P.IsStrongSeparation ↔ (∀ b, M.Dep (P b)) ∧ (∀ b, M.Nonspanning (P b)) := by
  rw [isStrongSeparation_iff, and_congr_right_iff]
  rintro -
  rw [true.forall_bool', (!true).forall_bool', nonspanning_not_iff, nonspanning_not_iff]

lemma IsStrongSeparation.dep (h : P.IsStrongSeparation) (b : Bool) : M.Dep (P b) :=
  h.isCyclicSeparation.dep b

lemma IsStrongSeparation.codep (h : P.IsStrongSeparation) (b : Bool) : M.Codep (P b) :=
  h.isVerticalSeparation.codep b

lemma IsStrongSeparation.nonspanning (h : P.IsStrongSeparation) (b : Bool) : M.Nonspanning (P b) :=
  h.isVerticalSeparation.nonspanning b

lemma IsStrongSeparation.encard_ge (h : P.IsStrongSeparation) : P.eConn + 2 ≤ (P b).encard := by
  grw [← P.eConn_eq b, ← M.eConn_add_nullity_add_nullity_dual (P b), ← (h.dep b).one_le_nullity,
    ← (h.codep b).one_le_nullity, add_assoc, one_add_one_eq_two]

lemma isStrongSeparation_iff_eRk (hP : P.eConn ≠ ⊤) : P.IsStrongSeparation ↔
    (∀ b, P.eConn < M.eRk (P b)) ∧ (∀ b, P.eConn < M✶.eRk (P b)) := by
  rw [and_comm]
  convert isStrongSeparation_iff with b b
  · rw [← ENat.add_one_le_iff hP, ← M.eConn_add_nullity_eq_eRk_dual (P b)]
    simp [hP, ENat.one_le_iff_ne_zero]
  rw [← ENat.add_one_le_iff hP, ← M.eConn_add_nullity_dual_eq_eRk (P b)]
  simp [hP, ENat.one_le_iff_ne_zero]


/-- A Tutte separation with connectivity zero is either a strong separation, or has one side
only loops or coloops. -/
lemma isTutteSeparation_iff_isStrongSeparation_of_zero (hP : P.eConn = 0) : P.IsTutteSeparation ↔
    P.IsStrongSeparation ∨ ((∀ b, (P b).Nonempty) ∧ (∃ b, P b ⊆ M.loops ∨ P b ⊆ M.coloops)) := by
  rw [isStrongSeparation_iff_eRk (by simp [hP]), isTutteSeparation_iff_lt_encard (by simp [hP]), hP]
  simp_rw [pos_iff_ne_zero, encard_ne_zero, Ne, eRk_eq_zero_iff', dual_ground,
    inter_eq_self_of_subset_left (P.subset_ground _), dual_loops]
  by_cases hne : ∀ b, (P b).Nonempty
  · grind
  rw [iff_false_intro hne, false_iff, false_and, or_false, Classical.not_and_iff_not_or_not,
    not_forall_not, not_forall_not]
  simp_rw [nonempty_iff_ne_empty, not_forall_not] at hne
  obtain ⟨b, hb⟩ := hne
  exact .inl ⟨b, by simp [hb]⟩

end Partition

lemma Dep.partition_isTutteSeparation_of_nonspanning (hX : M.Dep X) (hX' : M.Nonspanning X)
    (b : Bool) : (M.partition X b).IsTutteSeparation := by
  rw [isTutteSeparation_iff' b, partition_apply, partition_apply_not, and_iff_left (.inr hX')]
  exact .inl hX

lemma Nonspanning.partition_isVerticalSeparation (hX : M.Nonspanning X)
    (hXc : M.Nonspanning (M.E \ X)) (b : Bool) : (M.partition X b).IsVerticalSeparation := by
  rwa [Partition.isVerticalSeparation_iff_forall_nonspanning, b.forall_bool', partition_apply,
    partition_apply_not, and_iff_right hX]

lemma Codep.partition_isVerticalSeparation (hX : M.Codep X) (hXc : M.Nonspanning X) (b : Bool) :
    (M.partition X b).IsVerticalSeparation := by
  rw [Partition.isVerticalSeparation_iff_forall_nonspanning, b.forall_bool']
  simp [hXc, hX.nonspanning_compl]

lemma Codep.partition_isTutteSeparation_of_dep_compl (hX : M.Codep X) (hXc : M.Dep (M.E \ X)) :
    (M.partition X b).IsTutteSeparation := by
  rw [Partition.isTutteSeparation_iff_forall, b.forall_bool']
  simp [hX, hXc]

lemma Dep.partition_isCyclicSeparation (hX : M.Dep X) (hXc : M.Dep (M.E \ X)) :
    (M.partition X b).IsCyclicSeparation := by
  rw [Partition.isCyclicSeparation_iff_forall, b.forall_bool']
  simp [hX, hXc]

lemma Dep.partition_isStrongSeparation (hX : M.Dep X) (hns : M.Nonspanning X)
    (hXc : M.Dep (M.E \ X)) (hXsc : M.Nonspanning (M.E \ X)) :
    (M.partition X b).IsStrongSeparation := by
  rw [Partition.isStrongSeparation_iff, b.forall_bool', b.forall_bool']
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
    ∃ P : M.Partition, P.eConn + 1 ≤ k ∧ P.IsTutteSeparation ∧
    (P.IsStrongSeparation ∨ ((P b).encard ≤ k ∧
    ((M.Indep (P b) ∧ M.IsHyperplane (P !b)) ∨ (M.IsCircuit (P b) ∧ M.Spanning (P !b))))) := by
  obtain ⟨P, hPconn, hP⟩ := not_tutteConnected_iff_exists.1 h
  by_cases hPs : P.IsStrongSeparation
  · exact ⟨P, hPconn, hP, .inl hPs⟩
  wlog hi : M.Indep (P b) generalizing P M with aux
  · obtain ⟨i, (hi | hci)⟩ := Partition.not_isStrongSeparation_iff.1 hPs
    · obtain rfl | rfl := i.eq_or_eq_not b
      · contradiction
      exact aux h P.symm (by simpa) (by simpa) (by simpa) hi
    suffices aux' : ∃ Q : M✶.Partition,
        Q.eConn + 1 ≤ k ∧ Q.IsTutteSeparation ∧ ¬ Q.IsStrongSeparation ∧ M✶.Indep (Q b) by
      obtain ⟨Q, hQconn, hQsep, hQsep', hQb⟩ := aux'
      obtain ⟨P', hP'k, hP't, hP' | hP'⟩ :=
        aux (by simpa) Q (by simpa) (by simpa) (by simpa) (by simpa)
      · exact ⟨P'.ofDual, by simpa, by simpa, .inl (by simpa)⟩
      rw [or_comm, isHyperplane_not_iff, spanning_not_iff, ← isCocircuit_def,
        ← isHyperplane_compl_iff_isCocircuit, ← coindep_def, coindep_iff_compl_spanning,
        ← dual_ground, P'.compl_eq, dual_isCocircuit_iff, spanning_not_iff, dual_coindep_iff,
        and_comm (b := Indep ..), and_comm (b := IsCircuit ..), ← Partition.ofDual_apply,
          ← spanning_not_iff, Partition.ofDual_apply] at hP'
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
  have hnv := h.not_isVerticalSeparation (P := M.partition X true) (by simpa)
  rwa [not_isVerticalSeparation_iff_exists, Bool.exists_bool, partition_apply,
    ← Bool.not_true, partition_apply_not, or_iff_right hX.codep_compl.not_coindep,
    coindep_iff_compl_spanning] at hnv

lemma verticallyConnected_top_iff :
    M.VerticallyConnected ⊤ ↔ ∀ X ⊆ M.E, M.Spanning X ∨ M.Spanning (M.E \ X) := by
  rw [← top_add (a := 1), verticallyConnected_iff_forall]
  simp only [le_top, isVerticalSeparation_iff_forall_nonspanning, Bool.forall_bool, not_and,
    Partition.not_nonspanning_iff, forall_const]
  refine ⟨fun h X hX ↦ ?_, fun h P hP ↦ by simpa [hP.not_spanning] using h _ (P.subset_ground true)⟩
  rw [or_iff_not_imp_right, not_spanning_iff]
  simpa using h (M.partition X true)

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
  refine h.not_isVerticalSeparation (P := (freeOn E).partition {x} true (by simpa))
    (by simp [← loopyOn_dual_eq]) ?_
  suffices ¬ {x} = E by simpa [Partition.isVerticalSeparation_iff_forall_nonspanning,
    nonspanning_iff, hx]
  rintro rfl
  exact hne.symm (by simpa using hy)


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
  have h' := h.not_isCyclicSeparation (P := M.partition X true) (by simpa)
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

/-- This needs the lower bound on co-rank; otherwise an extenssion of a large free matroid by
a loop would be a counterexample for any `k`. -/
lemma CyclicallyConnected.le_girth (h : M.CyclicallyConnected k) (hlt : k ≤ M✶.eRank) :
    k ≤ M.girth := by
  obtain (rfl | ⟨k, rfl⟩) := k.eq_zero_or_exists_eq_add_one; simp
  rw [← not_lt, girth_lt_iff, not_exists]
  rintro C ⟨hC, hCcard⟩
  refine h.not_isCyclicSeparation (P := M.partition C true) ?_ ?_
  · grw [eConn_partition, hC.eConn_add_one_eq, eRk_le_encard]
    exact Order.add_one_le_of_lt hCcard
  suffices ¬ M.Indep (M.E \ C) by simpa [Partition.isCyclicSeparation_iff_forall, hC.dep]
  intro hi
  rw [← dual_coindep_iff, ← dual_ground, ← spanning_iff_compl_coindep] at hi
  grw [← M✶.eRk_le_encard, hi.eRk_eq] at hCcard
  exact hCcard.not_ge hlt

/-- This needs the strict inequality in the hypothesis, since nothing like this can be true
for `k = ⊤`. This is also false for matroids like `U₂,₅` if there is no lower bound on size. -/
lemma tutteConnected_iff_verticallyConnected_girth (hlt : 2 * k < M.E.encard + 1) :
    M.TutteConnected (k + 1) ↔ M.VerticallyConnected (k + 1) ∧ k + 1 ≤ M.girth := by
  have hk : k ≠ ⊤ := by rintro rfl; simp at hlt
  refine ⟨fun h ↦ ⟨h.verticallyConnected, h.le_girth (by eomega)⟩,
    fun ⟨h', hle⟩ ↦ by_contra fun h ↦ ?_⟩
  obtain ⟨P, hPconn, hP, (hPs | ⟨hcard, ⟨hi, hh⟩ | ⟨hc, hs⟩⟩)⟩ :=
    exists_strong_or_small_of_not_tutteConnected h true
  · exact h'.not_isVerticalSeparation (by simpa) hPs.isVerticalSeparation
  · refine h'.not_isVerticalSeparation (by simpa) ?_
    simp_rw [P.isVerticalSeparation_iff_forall_nonspanning, ← P.not_spanning_iff, Bool.forall_bool,
      ← Bool.not_true, and_iff_right hh.not_spanning]
    intro hPs
    obtain ⟨C, hCP, hC⟩ := (hP.dep_of_spanning hPs).exists_isCircuit_subset
    grw [hC.girth_le_card, ← hC.eRk_add_one_eq, M.eRk_mono hCP, ← hcard, hh.eRk_add_one_eq,
      ← hPs.eRk_eq, hi.eRk_eq_encard] at hle
    simp [Infinite.encard_eq (by simpa using hle), hk] at hcard
  grw [hc.girth_le_card, ← hcard] at hle
  simp [Infinite.encard_eq (by simpa using hle), hk] at hcard

lemma tutteConnected_iff_verticallyConnected_cyclicallyConnected (hlt : 2 * k < M.E.encard) :
    M.TutteConnected (k + 1) ↔ M.VerticallyConnected (k + 1) ∧ M.CyclicallyConnected (k + 1) := by
  refine ⟨fun h ↦ ⟨h.verticallyConnected, h.cyclicallyConnected⟩,
    fun ⟨hv, hc⟩ ↦ by_contra fun h ↦ ?_⟩
  obtain ⟨P, hPconn, hP, (hPs | ⟨hcard, hP'⟩)⟩ :=
    exists_strong_or_small_of_not_tutteConnected h true
  · exact hv.not_isVerticalSeparation (by simpa) hPs.isVerticalSeparation
  wlog hi : M.Indep (P true) generalizing M P with aux
  · rw [or_iff_right (by simp [hi]), P.spanning_not_iff, and_comm, coindep_def] at hP'
    exact aux (M := M✶) (by simpa) (by simp [hc, hv]) (by simpa) (by simpa) (by simpa) P.dual
      (by simpa) (by simpa) (by simpa) (.inl (by simpa [isHyperplane_dual_iff])) hP'.1
  rw [or_iff_left (fun h ↦ h.1.not_indep hi), and_iff_right hi] at hP'
  have hnv := hv.not_isVerticalSeparation (by simpa)
  have hPconn_ne : P.eConn ≠ ⊤ := fun h ↦ by enat_to_nat!
  simp_rw [P.not_isVerticalSeparation_iff_exists_spanning, Bool.exists_bool, ← Bool.not_true,
    or_iff_right hP'.not_spanning] at hnv
  obtain ⟨C, hCr, hC⟩ := (hP.dep_of_spanning hnv).exists_isCircuit_subset
  have hb := hi.isBase_of_spanning hnv
  refine hc.not_isCyclicSeparation (P := M.partition C true) ?_ ?_
  · grw [eConn_partition, eConn_le_eRk, eRk_mono _ hCr, hP'.eRk_add_one_eq, ← hb.encard_eq_eRank]
    simpa
  obtain rfl | hssu := hCr.eq_or_ssubset
  · rw [← P.union_eq, encard_union_eq P.disjoint] at hlt
    have := Bool.not_true ▸ hb.encard_eq_eRank ▸ hP'.eRk_add_one_eq ▸ hC.eRk_add_one_eq
    eomega
  refine hC.dep.partition_isCyclicSeparation (hb.dep_of_ssubset ?_)
  exact P.compl_false ▸ diff_ssubset_diff_right (P.subset_ground _) hssu


lemma VerticallyConnected.contract {C : Set α} (h : M.VerticallyConnected (k + M.eRk C)) :
    (M ／ C).VerticallyConnected k := by
  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← M.contract_inter_ground_eq]
    exact aux (h.mono (by grw [eRk_mono _ inter_subset_left])) inter_subset_right
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [add_right_comm] at h
  refine verticallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  refine h.not_isVerticalSeparation (P := P.ofContract true) ?_ ?_
  · grw [ENat.add_one_le_add_one_iff, eConn_ofContract, Bool.not_true, eLocalConn_le_eRk_right,
      add_right_comm, hPconn]
  rw [isVerticalSeparation_iff_forall_nonspanning, Bool.forall_bool, ofContract_true_false,
    ofContract_apply_self]
  rw [isVerticalSeparation_iff_forall_nonspanning, Bool.forall_bool, contract_nonspanning_iff,
    contract_nonspanning_iff] at hP
  exact ⟨hP.1.1.subset subset_union_left, hP.2.1⟩

lemma VerticallyConnected.contract_of_top (h : M.VerticallyConnected ⊤) (C : Set α) :
    (M ／ C).VerticallyConnected ⊤ :=
  (h.mono le_top).contract


end Matroid
