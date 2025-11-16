import Matroid.Connectivity.Separation
import Matroid.Connectivity.Minor
import Mathlib.Tactic.Peel

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

-- lemma isVerticalSeparation_iff_of_eConn_ne_top (hP : P.eConn ≠ ⊤) :
--     P.IsVerticalSeparation ↔ ¬ M.Spanning P.left ∧ ¬ M.Spanning P.right := by
--   sorry

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

lemma IsInternallyConnected.isTutteConnected (hM : M.IsInternallyConnected (k+1)) :
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

lemma spanning_dual_compl_iff {X : Set α} (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Spanning (M.E \ X) ↔ M.Indep X := by
  rw [← dual_coindep_iff, coindep_iff_compl_spanning, dual_ground]

lemma spanning_dual_iff {X : Set α} (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Spanning X ↔ M.Indep (M.E \ X) := by
  rw [← spanning_dual_compl_iff, diff_diff_cancel_left hXE]

/-- An infinitely Tutte-Connected matroid needs to be weird. -/
lemma isTutteConnected_top_iff : M.IsTutteConnected ⊤ ↔ ∀ X ⊆ M.E, M.eConn X ≠ ⊤ →
      (M.Indep X ∧ M.Coindep X) ∨ (M.Spanning X ∧ M.Indep (M.E \ X)) := by
  rw [← not_iff_not]
  simp only [not_isTutteConnected_iff_with_lt,
    lt_iff_le_and_ne (b := encard ..), eConn_le_encard, ne_eq, true_and, not_forall,
    not_or, exists_and_left, exists_prop, lt_top_iff_ne_top,
    show ∀ Y, M.eConn Y ≤ (M.E \ Y).encard from fun Y ↦ by grw [← eConn_compl, eConn_le_encard]]
  simp only [ENat.add_eq_top, ENat.one_ne_top, or_false, not_and]
  refine ⟨fun ⟨X, hXE, hXconn, h1, h2⟩ ↦ ⟨X, fun hi hid ↦ h1 (hi.eConn_eq_encard_of_coindep hid),
    hXconn, hXE, fun hs hi ↦ h2 ?_⟩, fun ⟨X, h1, hconn, hXE, h2⟩ ↦ ⟨X, hXE, hconn, ?_⟩⟩
  · rwa [← eConn_compl, Indep.eConn_eq_encard_of_coindep]
    rwa [coindep_iff_compl_spanning, diff_diff_cancel_left hXE]
  rw [eConn_eq_encard_iff' hconn, ← eConn_compl, eConn_eq_encard_iff' (by simpa)]
  rw [spanning_iff_compl_coindep] at h2
  tauto

lemma isUniform_of_isTutteConnected_top [M.RankFinite] (h : M.IsTutteConnected ⊤) :
    M.IsUniform := by
  rw [isTutteConnected_top_iff] at h
  refine fun X hX ↦ (h X hX ?_).elim (.inl ∘ And.left) (.inr ∘ And.left)
  grw [← lt_top_iff_ne_top, eConn_le_eRk]
  exact eRk_lt_top

/-- Todo : a version for when the Tutte Connectivity is much larger than the rank. -/
lemma eq_unifOn_of_isTutteConnected_top [M.RankFinite] (h : M.IsTutteConnected ⊤) :
    ∃ (E : Set α) (k : ℕ), M = unifOn E k ∧ E.encard ≤ 2 * k + 1 ∧ 2 * k ≤ E.encard + 1 := by
  obtain ⟨E, k, hkE, rfl⟩ := (isUniform_of_isTutteConnected_top h).exists_eq_unifOn
  refine ⟨E, k, rfl, ?_⟩
  rw [isTutteConnected_top_iff] at h
  simp +contextual [diff_subset, unifOn_coindep_iff'' hkE, unifOn_spanning_iff'' hkE] at h
  refine ⟨le_of_not_gt fun hlt ↦ ?_, le_of_not_gt fun hlt ↦ ?_⟩
  · obtain ⟨X, hXE, hXcard⟩ := exists_subset_encard_eq (k := k + 1) (s := E)
      (by
        generalize hl : E.encard = l at *
        enat_to_nat
        linarith)
    have hEX : (E \ X).encard ≤ k := by simpa [hXcard] using h X hXE
    grw [← encard_diff_add_encard_of_subset hXE, hXcard, hEX, ← add_assoc, two_mul] at hlt
    exact hlt.ne rfl
  obtain rfl | k := k
  · simp at hlt
  obtain ⟨X, hXE, hX⟩ := exists_subset_encard_eq (k := k) (s := E) (by grw [← hkE]; simp)
  have hle : k + 1 ≤ (E \ X).encard := by simpa [hX] using h X hXE
  grw [← encard_diff_add_encard_of_subset hXE, ← hle, hX] at hlt
  enat_to_nat
  linarith

lemma isInternallyConnected_top_iff : M.IsInternallyConnected ⊤ ↔ M.IsTutteConnected ⊤ :=
  ⟨fun h ↦ IsInternallyConnected.isTutteConnected (by simpa),
    IsTutteConnected.isInternallyConnected⟩

-- lemma not_isVerticallyConnected_iff :
--     ¬ M.IsVerticallyConnected k ↔ ∃ X ⊆ M.E, M.eConn X + 1 < k ∧
--     ¬ M.Spanning X ∧ ¬ M.Spanning (M.E \ X) := by

--   simp_rw [IsVerticallyConnected, not_isPredConnected_iff, Partition.isVerticalSeparation_iff]
--   refine ⟨fun ⟨P, ⟨hP1', hP2'⟩, hPconn⟩ ↦ ⟨_, P.left_subset_ground, by rwa [← P.eConn_eq_left],
--     fun hsp ↦ ?_, fun hsp ↦ ?_⟩,
--     fun ⟨X, hXE, hXconn, hX⟩ ↦ ?_⟩
--   ·
--   · by_contra! hcon
--     have hP1 : M.Spanning P.left := hcon _ P.left_subset_ground (by rwa [← P.eConn_eq_left])
--     have hP2 : M.Spanning P.right := hcon _ P.right_subset_ground (by rwa [← P.eConn_eq_right])
--     obtain ⟨I1, hI1⟩ := M.exists_isBasis P.left
--     grw [P.eConn_eq_left, hI1.eConn_eq_nullity_contract, P.compl_left, nullity_eq_encard,
--       (hI1.isBase_of_spanning hP1).encard_eq_eRank] at hPconn
--     · have h0 := hcon ∅ (empty_subset _) (lt_of_le_of_lt (by simp) hPconn)
--       obtain ⟨E, rfl⟩ := spanning_empty_iff_eq_loopyOn.1 h0
--       simp at hP1'
--     simp [hP2.closure_eq, P.compl_right, hI1.subset]
--   refine ⟨M.partition X hXE, ⟨lt_of_not_ge fun hle ↦ ?_, lt_of_not_ge fun hle ↦ ?_⟩, hXconn⟩
--   · simp only [partition_left, eConn_partition] at hle
--     have := (eConn_eq_eRk_iff ?_).1 (hle.antisymm' ?_)

--     rw [eConn_eq_eRk_iff]

      -- rw [spanning_empty_iff] at h0
      -- rw [h0] at hP1'



    -- obtain ⟨B1, hB1⟩ := M.exists_is


  --   specialize h (B \ {e}) (diff_subset.trans hBE)
  --   rw [← hBcard, ← encard_diff_singleton_add_one heB, or_iff_left] at h

  --   ENat.add_le_left_iff,
  --     ENat.add_le_left_iff, or_iff_left one_ne_zero, encard_diff_singleton_of_mem heB] at h


  -- obtain rfl | hssu := hB.subset_ground.eq_or_ssubset
  -- · obtain rfl | ⟨e, heB⟩ := B.eq_empty_or_nonempty
  --   · simp [show k = 0 by simpa using hkE]
  --   have := h (B \ {e}) diff_subset
  --   rw [diff_diff_cancel_left (by simpa)] at this

  -- · obtain rfl | hssu := hB.subset_ground.eq_or_ssubset
    -- obtain h_empt | ⟨f, heB⟩ := (B.eq_empty_or_nonempty
    -- rw [unifOn_isBase_iff hkE (by simp)] at hB
    -- simp [unifOn_isBase_iff] at hB
  -- obtain rfl | ⟨e, heE⟩ := E.eq_empty_or_nonempty
  -- · simp [show k = 0 by simpa using h]
  -- obtain h1 | h2 := h {e} (by simpa)
  -- ·


  -- obtain (hEk | hklt) := hkE.eq_or_lt
  -- · obtain (rfl | rfl | k) := k
  --   · simp [hEk.symm]
  --   · simp [show E.encard = 1 by simpa using hEk.symm, one_add_one_eq_two]
  --   obtain rfl | ⟨e, heE⟩ := E.eq_empty_or_nonempty
  --   · simp at hEk
  --   have := h {e}
  --   simp at this
    -- obtain rfl | ⟨e, heE⟩ := E.eq_empty_or_nonempty
    -- · simp [show k = 0 by simpa using hEk]
    -- have := h {e}
    -- simp [heE, hEk] at this
    -- simp at hEk
    -- simp [he]
    -- have := h ∅
    -- simp [hEk] at this
    -- cases k with
    -- | zero => simp [← hEk]
    -- | succ n =>
    --   specialize h ∅
    --   simp at h
  -- by_contra! hcon

  -- have h1 := h B hB.subset_ground (by simp)
  --   -- (by grw [← lt_top_iff_ne_top, eConn_le_encard, hB.encard_eq_eRank]; simp)
  -- rw [and_iff_right hB.indep, and_iff_right hB.spanning, unifOn_ground_eq] at h1
  -- rw [unifOn_coindep_iff hBE hkE] at h1
  -- have h2 := h (E \ B) diff_subset (by simp)
  -- rw [unifOn_indep_iff, and_iff_left diff_subset, unifOn_coindep_iff diff_subset hkE,
  --   unifOn_spanning_iff hkE diff_subset, unifOn_ground_eq, diff_diff_cancel_left hBE,
  --   ] at h2
  -- simp [diff_subset, hBE, disjoint_iff_inter_eq_empty,
  --   inter_eq_self_of_subset_right] at h2

  -- have h2 := h (E \ B) diff_subset ?_





  -- obtain hlt | hge := lt_or_ge E.encard (2 * k)
  -- · obtain ⟨
  -- wlog hle : 2 * k ≤ E.encard generalizing k with aux
  -- · rw [not_le] at hle
  --   obtain ⟨c, hc⟩ := exists_add_of_le hle.le
  --   have hlt : c ≠ ⊤ := by rintro rfl; simp [two_mul] at hc
  --   lift c to ℕ using hlt
  --   specialize aux c






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
