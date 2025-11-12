import Matroid.Connectivity.Separation
import Matroid.Connectivity.Minor

open Set

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b : α} {A : Set α} {P : M.Partition}

namespace Matroid.Partition

/-! ### Conditional Connectivity -/

/-- A Tutte separation is one where both sides exceed the connectivity in size -/
@[mk_iff]
structure IsTutteSeparation (P : M.Partition) : Prop where
  eConn_lt_left : P.eConn < P.left.encard
  eConn_lt_right : P.eConn < P.right.encard

lemma IsTutteSeparation.dual (hP : P.IsTutteSeparation) : P.dual.IsTutteSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

lemma IsTutteSeparation.of_dual {P : M✶.Partition} (hP : P.IsTutteSeparation) :
    P.ofDual.IsTutteSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

@[simp]
lemma IsTutteSeparation.dual_iff : P.dual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  ⟨fun h ↦ ⟨by simpa using h.1, by simpa using h.2⟩, Partition.IsTutteSeparation.dual⟩

@[mk_iff]
structure IsVerticalSeparation (P : M.Partition) : Prop where
  eConn_lt_left : P.eConn < M.eRk P.left
  eConn_lt_right : P.eConn < M.eRk P.right

@[mk_iff]
structure IsInternalSeparation (P : M.Partition) : Prop where
  eConn_lt_left : P.eConn + 1 < P.left.encard
  eConn_lt_right : P.eConn + 1 < P.right.encard

lemma IsInternalSeparation.dual (hP : P.IsInternalSeparation) : P.dual.IsInternalSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

lemma IsInternalSeparation.of_dual {P : M✶.Partition} (hP : P.IsInternalSeparation) :
    P.ofDual.IsInternalSeparation :=
  ⟨by simpa using hP.eConn_lt_left, by simpa using hP.eConn_lt_right⟩

lemma IsInternalSeparation.IsTutteSeparation (hP : P.IsInternalSeparation) : P.IsTutteSeparation :=
  ⟨(le_self_add ..).trans_lt hP.1, (le_self_add ..).trans_lt hP.2⟩

lemma IsVerticalSeparation.IsTutteSeparation (hP : P.IsVerticalSeparation) : P.IsTutteSeparation :=
  ⟨hP.1.trans_le (M.eRk_le_encard ..), hP.2.trans_le (M.eRk_le_encard ..)⟩

@[simp]
lemma IsInternalSeparation.dual_iff : P.dual.IsInternalSeparation ↔ P.IsInternalSeparation :=
  ⟨fun h ↦ ⟨by simpa using h.1, by simpa using h.2⟩, Partition.IsInternalSeparation.dual⟩

lemma IsCircuit.isTutteSeparation {C : Set α} (hC : M.IsCircuit C) (hfin : C.Finite)
    (hcard : 2 * C.encard ≤ M.E.encard) : (M.partition C).IsTutteSeparation := by
  have hfinr : M.eRk C ≠ ⊤ := by simp [isRkFinite_of_finite _ hfin]
  simp only [Partition.isTutteSeparation_iff, eConn_partition, partition_left, partition_right]
  grw [eConn_le_eRk, ← ENat.add_one_le_iff hfinr, ← ENat.add_one_le_iff hfinr, hC.eRk_add_one_eq]
  grw [← encard_diff_add_encard_of_subset hC.subset_ground, two_mul,
    WithTop.add_le_add_iff_right (show C.encard ≠ ⊤ by simpa)] at hcard
  simp [hcard]

lemma IsCocircuit.isTutteSeparation {C : Set α} (hC : M.IsCocircuit C) (hfin : C.Finite)
    (hcard : 2 * C.encard ≤ M.E.encard) : (M.partition C).IsTutteSeparation := by
  simpa using (IsCircuit.isTutteSeparation hC hfin (by simpa)).of_dual

end Partition

/- ### Abstract Connectivity -/

/-- Every separation of `M` satisfying condition `cond` has connectivity at least `k-1`. -/
def IsPredConnected (cond : {M : Matroid α} → M.Partition → Prop) (M : Matroid α) (k : ℕ∞) : Prop :=
    ∀ ⦃P : M.Partition⦄, cond P → k ≤ P.eConn + 1

lemma IsPredConnected.mono {cond} {j k : ℕ∞} (h : IsPredConnected cond M k) (h_le : j ≤ k) :
    IsPredConnected cond M j :=
  fun _ hP ↦ h_le.trans <| h hP

lemma IsPredConnected.dual {cond} {k} (h : IsPredConnected cond M k)
    (h_cond : ∀ ⦃N : Matroid α⦄ ⦃P : N.Partition⦄, cond P → cond P.dual) :
    IsPredConnected cond M✶ k := by
  intro P hP
  rw [← P.ofDual_eConn]
  -- this is weird fighting with type theory; is there a better way to do this?
  have aux {M₀ M₁ : Matroid α} (h_eq : M₀ = M₁) {P : M₀.Partition} (hP : cond P) :
      cond (P.copy (show M₀.E = M₁.E by rw [h_eq])) := by
    subst h_eq
    convert hP
  exact h <| aux M.dual_dual <| h_cond hP

lemma IsPredConnected.ofDual {cond} {k} (h : IsPredConnected cond M✶ k)
    (h_cond : ∀ ⦃N : Matroid α⦄ ⦃P : N.Partition⦄, cond P → cond P.dual) :
    IsPredConnected cond M k := by
  simpa using h.dual h_cond

lemma IsPredConnected.mono_prop {cond cond' : {M : Matroid α} → M.Partition → Prop} {k}
    (h : IsPredConnected cond M k)
    (h_cond : ∀ ⦃M : Matroid α⦄ ⦃P : M.Partition⦄, cond' P → cond P) :
    IsPredConnected cond' M k :=
  fun _ hP ↦ h <| h_cond hP

lemma isPredConnected_two_iff (cond : {M : Matroid α} → M.Partition → Prop) :
    IsPredConnected cond M 2 ↔ ∀ (P : M.Partition), P.eConn = 0 → ¬ cond P := by
  refine ⟨fun h P hP hP' ↦ by simpa [hP] using h hP', fun h P hP ↦ ?_⟩
  have hle : 1 ≤ P.eConn := ENat.one_le_iff_ne_zero.2 <| mt (h P) (by simpa)
  rwa [← ENat.add_one_le_add_one_iff] at hle

lemma not_isPredConnected_iff (cond : {M : Matroid α} → M.Partition → Prop) :
    ¬ IsPredConnected cond M k ↔ ∃ (P : M.Partition), cond P ∧ P.eConn + 1 < k := by
  simp [IsPredConnected]

/- ### Tutte Connectivity -/

/-- Every Tutte separation has connectivity at least `k-1`. -/
def IsTutteConnected (M : Matroid α) (k : ℕ∞) : Prop :=
  IsPredConnected Partition.IsTutteSeparation M k

/-- Every vertical separation has connectivity at least `k-1`. -/
def IsVerticallyConnected (M : Matroid α) (k : ℕ∞) : Prop :=
  IsPredConnected Partition.IsVerticalSeparation M k

/-- Every internal separation, and every Tutte separation of order at most `k-2`,
 has connectivity at least `k-1` -/
def IsInternallyConnected (M : Matroid α) (k : ℕ∞) : Prop :=
    IsPredConnected (fun P ↦ P.IsInternalSeparation ∨ (P.IsTutteSeparation ∧ P.eConn + 2 ≤ k)) M k

lemma IsTutteConnected.dual (h : M.IsTutteConnected k) : M✶.IsTutteConnected k :=
  IsPredConnected.dual h fun _ _ ↦ Partition.IsTutteSeparation.dual

lemma IsTutteConnected.of_dual (h : M✶.IsTutteConnected k) : M.IsTutteConnected k := by
  simpa using h.dual

@[simp]
lemma isTutteConnected_dual_iff : M✶.IsTutteConnected k ↔ M.IsTutteConnected k :=
  ⟨IsTutteConnected.of_dual, IsTutteConnected.dual⟩

lemma isTutteConnected_two_iff [M.Nonempty] : M.IsTutteConnected 2 ↔ M.Connected := by
  simp_rw [IsTutteConnected, isPredConnected_two_iff, Partition.eConn_eq_zero_iff_eq_disjointSum,
    Partition.isTutteSeparation_iff, not_and]
  refine ⟨fun h ↦ by_contra fun hconn ↦ ?_, fun h P hM hlt hlt' ↦ ?_⟩
  · obtain ⟨M₁, M₂, hdj, h₁, h₂, rfl⟩ := eq_disjointSum_of_not_connected hconn
    simpa [hdj.sdiff_eq_right, h₁.ground_nonempty, h₂.ground_nonempty] using
      h ((M₁.disjointSum M₂ hdj).partition M₁.E)
  rw [hM] at h
  grw [← zero_le P.eConn, encard_pos] at hlt hlt'
  refine disjointSum_not_connected ?_ ?_ _ h
  <;> simpa [← ground_nonempty_iff]

lemma not_isTutteConnected_iff : ¬ M.IsTutteConnected k ↔ ∃ (P : M.Partition) (j : ℕ),
    j + 2 ≤ k ∧ P.eConn = j ∧ j < P.left.encard ∧ j < P.right.encard := by
  simp only [IsTutteConnected, not_isPredConnected_iff, Partition.isTutteSeparation_iff,
    ← one_add_one_eq_two, ← add_assoc]
  constructor
  · rintro ⟨P, ⟨h1, h2⟩, hlt⟩
    refine ⟨P, P.eConn.toNat, ?_⟩
    rwa [ENat.coe_toNat (by intro h; simp [h] at hlt), and_iff_left h2, and_iff_left h1,
      and_iff_left rfl, ENat.add_one_le_iff (hlt.trans_le le_top).ne]
  rintro ⟨P, j, hlt, h0, h1, h2⟩
  rw [ENat.add_one_le_iff (by simp)] at hlt
  use P
  simp [h0, h1, h2, hlt]

lemma not_isTutteConnected_iff' {k : ℕ∞} : ¬ M.IsTutteConnected k ↔ ∃ (X : Set α) (j : ℕ),
    j + 2 ≤ k ∧ X ⊆ M.E ∧ M.eConn X = j ∧ j < X.encard ∧ j < (M.E \ X).encard := by
  rw [not_isTutteConnected_iff]
  constructor
  · rintro ⟨P, j, hlt, hconn, h1, h2⟩
    exact ⟨P.left, j, by norm_cast at hlt, P.left_subset_ground, by rwa [← P.eConn_eq_left], h1,
      by rwa [P.compl_left]⟩
  rintro ⟨X, j, hlt, hX, hconn, h1, h2⟩
  exact ⟨M.partition X, j, by norm_cast, by simpa, by simpa, by simpa⟩

lemma not_isTutteConnected_iff'' {k : ℕ∞} : ¬ M.IsTutteConnected k ↔ ∃ (X : Set α) (j : ℕ∞),
    j + 2 ≤ k ∧ X ⊆ M.E ∧ M.eConn X = j ∧ j < X.encard ∧ j < (M.E \ X).encard := by
  rw [not_isTutteConnected_iff']
  refine ⟨fun ⟨X, j, h⟩ ↦ ⟨X, j, h⟩, fun ⟨X, j, h⟩ ↦ ?_⟩
  lift j to ℕ using (h.2.2.2.1.trans_le le_top).ne
  exact ⟨X, j, h⟩

lemma not_isTutteConnected_iff''' {k : ℕ∞} : ¬ M.IsTutteConnected k ↔ ∃ X ⊆ M.E,
    M.eConn X + 2 ≤ k ∧ M.eConn X < X.encard ∧ M.eConn X < (M.E \ X).encard := by
  rw [not_isTutteConnected_iff'']
  refine ⟨fun ⟨X, j, h⟩ ↦ ⟨X, ?_⟩, fun ⟨X, h⟩ ↦ ⟨X, M.eConn X, by tauto⟩⟩
  obtain rfl := h.2.2.1
  tauto

/-- This is probably the best version for exploiting non-connectivity,
since the `<` works better with `k` infinite.  -/
lemma not_isTutteConnected_iff_with_lt {k : ℕ∞} : ¬ M.IsTutteConnected k ↔ ∃ X ⊆ M.E,
    M.eConn X + 1 < k ∧ M.eConn X < X.encard ∧ M.eConn X < (M.E \ X).encard := by
  simp_rw [IsTutteConnected, not_isPredConnected_iff, Partition.isTutteSeparation_iff]
  refine ⟨fun ⟨P, hP, hPk⟩ ↦ ⟨P.left, P.left_subset_ground, ?_⟩, fun ⟨X, hXE, hX⟩ ↦ ?_⟩
  · rw [← P.eConn_eq_left, P.compl_left]
    exact ⟨hPk, hP⟩
  exact ⟨M.partition X, by simp [hX.2.1, hX.2, hX.1]⟩

lemma exists_of_not_isTutteConnected (h : ¬ M.IsTutteConnected k) :
    ∃ X ⊆ M.E, M.eConn X + 1 < k ∧ M.eConn X < X.encard ∧ X.encard ≤ (M.E \ X).encard := by
  rw [not_isTutteConnected_iff_with_lt] at h
  obtain ⟨Y, hY, hYconn, hYcard, hYc⟩ := h
  obtain hle | hgt := le_or_gt Y.encard (M.E \ Y).encard
  · exact ⟨Y, hY, hYconn, hYcard, hle⟩
  exact ⟨M.E \ Y, diff_subset, by simpa, by simpa, by simpa [diff_diff_cancel_left hY] using hgt.le⟩

lemma IsTutteConnected.encard_compl_lt (h : M.IsTutteConnected k) {X : Set α} (hXE : X ⊆ M.E)
    (hX : M.eConn X + 1 < k) (hcard : M.eConn X < X.encard) : (M.E \ X).encard ≤ M.eConn X := by
  contrapose! h
  rw [not_isTutteConnected_iff_with_lt]
  exact ⟨X, hXE, hX, hcard, h⟩

lemma IsTutteConnected.encard_lt (h : M.IsTutteConnected k) {X : Set α} (hXE : X ⊆ M.E)
    (hX : M.eConn X + 1 < k) (hcard : M.eConn X < (M.E \ X).encard) : X.encard ≤ M.eConn X := by
  contrapose! h
  rw [not_isTutteConnected_iff_with_lt]
  exact ⟨X, hXE, hX, h, hcard⟩

/- ### Internal Connectivity -/

lemma IsInternallyConnected.dual (h : M.IsInternallyConnected k) : M✶.IsInternallyConnected k :=
  IsPredConnected.dual h fun N P hP ↦ by simpa

lemma IsInternallyConnected.of_dual (h : M✶.IsInternallyConnected k) :
    M.IsInternallyConnected k := by
  simpa using h.dual

lemma isInternallyConnected_dual_iff : M✶.IsInternallyConnected k ↔ M.IsInternallyConnected k :=
  ⟨IsInternallyConnected.of_dual, IsInternallyConnected.dual⟩

lemma IsTutteConnected.isInternallyConnected (hM : M.IsTutteConnected k) :
    M.IsInternallyConnected k :=
  IsPredConnected.mono_prop hM fun _ _ h ↦
    Or.elim h Partition.IsInternalSeparation.IsTutteSeparation And.left

lemma IsTutteConnected.isVerticallyConnected (hM : M.IsTutteConnected k) :
    M.IsVerticallyConnected k :=
  IsPredConnected.mono_prop hM <| fun _ _ ↦ Partition.IsVerticalSeparation.IsTutteSeparation

lemma IsInternallyConnected.IsTutteConnected (hM : M.IsInternallyConnected (k+1)) :
    M.IsTutteConnected k := by
  refine fun P hP ↦ ?_
  obtain h_le | h_lt := le_or_gt (P.eConn + 2) (k+1)
  · have h' : k ≤ P.eConn := by simpa [hP, h_le] using hM (P := P)
    exact h'.trans (by simp)
  rw [← ENat.add_one_le_add_one_iff, add_assoc, one_add_one_eq_two]
  exact h_lt.le

/-- This needs the cardinality hypothesis,
since otherwise a triangle with `k = 2` would be a counterexample. -/
lemma IsTutteConnected.contractElem (h : M.IsTutteConnected (k + 1)) (hcard : 2 * k ≤ M.E.encard)
    (e : α) : (M ／ {e}).IsTutteConnected k := by
  wlog heE : e ∈ M.E with aux
  · rw [← contract_inter_ground_eq, singleton_inter_eq_empty.2 heE, contract_empty]
    apply h.mono (by simp)
  by_contra hcon
  obtain ⟨X, hX, hXk, hXconn, hXcard⟩ := exists_of_not_isTutteConnected hcon
  rw [contract_ground] at hXcard hX
  obtain ⟨hXE, heX⟩ := subset_diff_singleton_iff.1 hX
  have hXlt' : M.eConn X < k := by
    grw [← eConn_le_eConn_contract_singleton_add_one] at hXk; assumption
  have heXlt' : M.eConn (insert e X) < k := by
    grw [← eConn_insert_le_eConn_contract_add_one] at hXk; assumption
  have hconX := h.encard_compl_lt hXE (by simpa)
  have hconXe := h.encard_compl_lt (insert_subset heE hXE) (by simpa)
  obtain hX_eq | hX_lt := (M.eConn_le_encard X).eq_or_lt
  · grw [← ENat.add_one_lt_add_one_iff, ← eConn_insert_le_eConn_contract_add_one,
      ← encard_insert_of_notMem heX] at hXconn
    have hne_top : M.eConn X + 1 ≠ ⊤ := by simpa using (hXlt'.trans_le le_top).ne
    have hcon' := (ENat.add_lt_add_iff_left hne_top).2 heXlt'
    nth_grw 1 [hX_eq, ← encard_insert_of_notMem heX, ← hconXe hXconn, add_comm,
      encard_diff_add_encard_of_subset (insert_subset heE hXE), ← hcard,
      Order.add_one_le_of_lt hXlt', two_mul] at hcon'
    exact hcon'.ne rfl
  grw [← hconX hX_lt, hXcard, diff_diff_comm] at hX_lt
  exact hX_lt.not_ge <| encard_le_encard diff_subset

lemma IsTutteConnected.deleteElem (h : M.IsTutteConnected (k + 1)) (hcard : 2 * k ≤ M.E.encard)
    (e : α) : (M ＼ {e}).IsTutteConnected k := by
  simpa [← isTutteConnected_dual_iff (M := M ＼ {e})] using h.dual.contractElem hcard e

lemma IsTutteConnected.delete {D : Set α} (h : M.IsTutteConnected (k + D.encard))
    (hDfin : D.Finite) (hcard : 2 * (k + D.encard) ≤ M.E.encard + 2) :
    (M ＼ D).IsTutteConnected k := by
  induction D, hDfin using Set.Finite.induction_on generalizing M with
  | empty => simpa using h
  | @insert e D heD hfin IH =>
    rw [encard_insert_of_notMem heD, ← add_assoc] at h
    rw [← singleton_union, ← delete_delete]
    rw [encard_insert_of_notMem heD, ← add_assoc, mul_add, mul_one,
      WithTop.add_le_add_iff_right (by simp)] at hcard
    refine (IH <| h.deleteElem hcard e) ?_
    grw [delete_ground, hcard, ← encard_diff_add_encard_inter (t := {e}),
      encard_le_encard inter_subset_right, encard_singleton, show (1 : ℕ∞) ≤ 2 by norm_num]

lemma IsTutteConnected.contract {C : Set α} (h : M.IsTutteConnected (k + C.encard))
    (hCfin : C.Finite) (hcard : 2 * (k + C.encard) ≤ M.E.encard + 2) :
    (M ／ C).IsTutteConnected k := by
  simpa using (h.dual.delete hCfin (by simpa)).dual

section Internal

lemma IsTutteConnected.not_isInternallyConnected_iff (h : M.IsTutteConnected k) (hk : k ≠ ⊤) :
    ¬ M.IsInternallyConnected (k + 1) ↔
      ∃ X ⊆ M.E, M.eConn X + 1 = k ∧ k ≤ X.encard ∧ k ≤ (M.E \ X).encard := by
  simp only [IsInternallyConnected, ← one_add_one_eq_two, ← add_assoc, ENat.add_one_le_add_one_iff,
    not_isPredConnected_iff, ENat.add_one_lt_add_one_iff]
  constructor
  · rintro ⟨P, hP, hPk⟩
    have ht : P.IsTutteSeparation :=
      hP.elim Partition.IsInternalSeparation.IsTutteSeparation And.left
    obtain rfl : k = P.eConn + 1 := (h ht).antisymm (Order.add_one_le_of_lt hPk)
    exact ⟨P.left, P.left_subset_ground,
      by rw [P.eConn_eq_left], Order.add_one_le_of_lt ht.eConn_lt_left,
      by grw [Order.add_one_le_of_lt ht.eConn_lt_right, P.compl_left]⟩
  rintro ⟨X, hXE, rfl, hkX, hkXc⟩
  simp only [ne_eq, ENat.add_eq_top, ENat.one_ne_top, or_false] at hk
  rw [ENat.add_one_le_iff hk] at hkX hkXc
  exact ⟨M.partition X, by simpa [Partition.isTutteSeparation_iff, eConn_partition, hkX, hkXc]⟩

-- lemma isTutteConnected_top_iff :
--     M.IsTutteConnected ⊤ ↔
--       ∀ X ⊆ M.E, M.eConn X < ⊤ → X.encard ≤ M.eConn X ∨ (M.E \ X).encard ≤ M.eConn X := by
--   rw [← not_iff_not]
--   simp [not_isTutteConnected_iff_with_lt]



-- lemma not_isInternallyConnected_iff :
--     (¬ M.IsInternallyConnected (k + 1)) ↔ ¬ M.IsTutteConnected k ∨
--     ∃ X ⊆ M.E, M.eConn X + 1 = k ∧ k ≤ X.encard ∧ k ≤ (M.E \ X).encard := by
--   _



-- lemma not_internallyConnected_iff_with_lt {k : ℕ∞} : ¬ M.IsInternallyConnected k ↔ ∃ X ⊆ M.E,
--     M.eConn X + 1 < k ∧ M.eConn X + 1 < X.encard ∧ M.eConn X + 1 < (M.E \ X).encard := by
--   simp only [IsInternallyConnected, Partition.isInternalSeparation_iff,
--     Partition.isTutteSeparation_iff, not_isPredConnected_iff, Partition.eConn_eq_left]
--   constructor
--   · rintro ⟨P, ⟨hPleft, hPright⟩ | ⟨⟨hPleft, hPright⟩, hPk⟩, hPconn⟩
--     · exact ⟨P.left, P.left_subset_ground, hPconn, hPleft, by simpa [P.compl_left]⟩
--     refine ⟨P.left, P.left_subset_ground, ?_, ?_, ?_⟩


end Internal
