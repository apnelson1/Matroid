import Matroid.Minor.Order

namespace Matroid

-- notation for a `Bool`-indexed pair, with the `false` entry first.
-- so for `f : Bool → α` we have `f = b[f false, f true]`.
notation "b[" x "," y "]" => fun i ↦ bif i then y else x

open Set Bool

variable {i b : Bool} {α : Type*} {e f g : α} {C K T X Y : Set α} {M : Matroid α}

/-- Dualize `M` if `b` is `true`, otherwise don't. This is useful in self-dual settings. -/
def bDual (M : Matroid α) (b : Bool) : Matroid α := bif b then M✶ else M

@[simp]
lemma bDual_true (M : Matroid α) : M.bDual true = M✶ := rfl

@[simp]
lemma bDual_false (M : Matroid α) : M.bDual false = M := rfl

@[simp, grind =]
lemma bDual_ground (M : Matroid α) (b : Bool) : (M.bDual b).E = M.E := by
  cases b <;> rfl

@[simp]
lemma bDual_dual (M : Matroid α) (b : Bool) : M✶.bDual b = M.bDual !b := by
  cases b with | _ => simp

@[simp]
lemma dual_bDual (M : Matroid α) (b : Bool) : (M.bDual b)✶ = M.bDual !b := by
  cases b with | _ => simp

lemma bDual_not_dual (M : Matroid α) (b : Bool) : M✶.bDual (!b) = M.bDual b := by
  simp

@[simp]
lemma bDual_isCocircuit_iff : (M.bDual b).IsCocircuit X ↔ (M.bDual (!b)).IsCircuit X := by
  simp [isCocircuit_def]

lemma bDual_coindep_iff : (M.bDual b).Coindep X ↔ (M.bDual (!b)).Indep X := by
  simp [coindep_def]

@[simp]
lemma bDual_bDual {c} : (M.bDual b).bDual c = M.bDual (b != c) := by
  cases b <;> simp [bDual]

lemma bDual_bDual_self (M : Matroid α) (b : Bool) : (M.bDual b).bDual b = M := by
  simp

lemma eq_bDual_iff_bDual_eq (M N : Matroid α) (d : Bool) : M.bDual d = N ↔ M = N.bDual d := by
  cases d with simp [eq_dual_iff_dual_eq]

lemma bDual_isMinor_iff {d : Bool} {N : Matroid α} : N.bDual d ≤m M ↔ N ≤m M.bDual d := by
  cases d with simp [isMinor_dual_iff_dual_isMinor]

/-- If `b` is false, then `M ＼ X`, and if `b` is true, then `M ／ X`. Used in self-dual settings. -/
def remove (M : Matroid α) (b : Bool) (X : Set α) := bif b then M ／ X else M ＼ X

@[simp, grind =]
lemma remove_false (M : Matroid α) (X : Set α) : M.remove false X = M ＼ X := rfl

@[simp, grind =]
lemma remove_true (M : Matroid α) (X : Set α) : M.remove true X = M ／ X := rfl

@[simp]
lemma remove_dual (M : Matroid α) (X : Set α) (b : Bool) : (M.remove b X)✶ = M✶.remove (!b) X := by
  cases b <;> simp

lemma dual_remove (M : Matroid α) (X : Set α) (b : Bool) : M✶.remove b X = (M.remove (!b) X)✶ := by
  rw [remove_dual, Bool.not_not]

@[simp]
lemma bDual_remove (M : Matroid α) (X : Set α) (b c : Bool) :
    (M.remove c X).bDual b = (M.bDual b).remove (b != c) X := by
  cases c <;> cases b <;> simp

@[simp, grind =]
lemma remove_ground (M : Matroid α) (X : Set α) (b : Bool) : (M.remove b X).E = M.E \ X := by
  cases b <;> rfl

@[simp]
lemma remove_remove (M : Matroid α) (X Y : Set α) (b : Bool) :
    (M.remove b X).remove b Y = M.remove b (X ∪ Y) := by
  cases b <;> simp

lemma remove_comm (M : Matroid α) (hXY : Disjoint X Y) (b c : Bool) :
    (M.remove b X).remove c Y = (M.remove c Y).remove b X := by
  cases b <;> cases c <;>
  simp [union_comm, M.contract_delete_comm hXY.symm, M.contract_delete_comm hXY]

lemma remove_isMinor (M : Matroid α) (X : Set α) (b : Bool) : M.remove b X ≤m M := by
  cases b
  · apply delete_isMinor
  apply contract_isMinor

@[simp]
lemma remove_inter_ground (M : Matroid α) (X : Set α) (b : Bool) :
    M.remove b (X ∩ M.E) = M.remove b X := by
  cases b <;> simp

@[simp]
lemma remove_singleton_eq_self : M.remove b {e} = M ↔ e ∉ M.E := by
  cases b <;> simp [contract_eq_self_iff]

lemma remove_singleton_of_notMem (he : e ∉ M.E) : M.remove b {e} = M := by
  simpa

lemma IsStrictMinor.exists_isMinor_removeElem {N : Matroid α} (hNM : N <m M) :
    ∃ e ∈ M.E, ∃ i, N ≤m M.remove i {e} := by
  obtain ⟨C, D, hC, hD, hCD, hne, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  obtain ⟨e, heC⟩ | ⟨e, heD⟩ : C.Nonempty ∨ D.Nonempty := by simpa using hne
  · exact ⟨e, hC heC, true, (delete_isMinor ..).trans (contract_isMinor_of_subset _ (by simpa))⟩
  refine ⟨e, hD heD, false,
    (delete_isMinor_delete_of_subset (D := {e}) (D' := D) _ (by simpa)).trans ?_⟩
  exact contract_delete_isMinor_delete _ <| hCD.mono_right <| by simpa

lemma IsStrictMinor.exists_eq_remove_singleton {N : Matroid α} (hNM : N <m M)
    (hE : (M.E \ N.E).Subsingleton) : ∃ b e, N = M.remove b {e} := by
  obtain ⟨e, he, b, h⟩ := hNM.exists_isMinor_removeElem
  refine ⟨b, e, Eq.symm <| h.eq_of_ground_subset ?_⟩
  grw [remove_ground, diff_subset_comm]
  exact hE.subset_of_nonempty_inter ⟨e, ⟨he, by grind⟩, rfl⟩
