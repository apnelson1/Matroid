import Matroid.Minor.Order


namespace Matroid

open Set Bool

variable {i b : Bool} {α : Type*} {e f g : α} {C K T X Y : Set α} {M : Matroid α}

/-- Dualize `M` if `b` is `true`, otherwise don't. This is useful in self-dual settings. -/
def bDual (M : Matroid α) (b : Bool) : Matroid α := bif b then M✶ else M

@[simp]
lemma bDual_true (M : Matroid α) : M.bDual true = M✶ := rfl

@[simp]
lemma bDual_false (M : Matroid α) : M.bDual false = M := rfl

@[simp, grind =]
lemma bDual_ground (M : Matroid α) (b : Bool) : (M.bDual b).E = M.E := by cases b <;> simp

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

/-- If `b` is false, then `M ＼ X`, and if `b` is true, then `M ／ X`. Used in self-dual settings. -/
def remove (M : Matroid α) (X : Set α) (b : Bool) := bif b then M ／ X else M ＼ X

@[simp, grind =]
lemma remove_false (M : Matroid α) (X : Set α) : M.remove X false = M ＼ X := rfl

@[simp, grind =]
lemma remove_true (M : Matroid α) (X : Set α) : M.remove X true = M ／ X := rfl

@[simp]
lemma remove_dual (M : Matroid α) (X : Set α) (b : Bool) : (M.remove X b)✶ = M✶.remove X !b := by
  cases b <;> simp

lemma dual_remove (M : Matroid α) (X : Set α) (b : Bool) : M✶.remove X b = (M.remove X !b)✶ := by
  rw [remove_dual, Bool.not_not]

lemma bDual_remove (M : Matroid α) (X : Set α) (b c : Bool) :
    (M.remove X c).bDual b = (M.bDual b).remove X (b != c) := by
  cases c <;> cases b <;> simp

@[simp]
lemma remove_ground (M : Matroid α) (X : Set α) (b : Bool) : (M.remove X b).E = M.E \ X := by
  cases b <;> simp

@[simp]
lemma remove_remove (M : Matroid α) (X Y : Set α) (b : Bool) :
    (M.remove X b).remove Y b = M.remove (X ∪ Y) b := by
  cases b <;> simp

lemma remove_comm (M : Matroid α) (hXY : Disjoint X Y) (b c : Bool) :
    (M.remove X b).remove Y c = (M.remove Y c).remove X b := by
  cases b <;> cases c <;> simp [union_comm, M.contract_delete_comm hXY.symm,
    M.contract_delete_comm hXY]

lemma remove_isMinor (M : Matroid α) (X : Set α) (b : Bool) : M.remove X b ≤m M := by
  cases b; apply delete_isMinor; apply contract_isMinor

@[simp]
lemma remove_inter_ground (M : Matroid α) (X : Set α) (b : Bool) :
    M.remove (X ∩ M.E) b = M.remove X b := by
  cases b <;> simp

@[simp]
lemma remove_singleton_eq_self : M.remove {e} b = M ↔ e ∉ M.E := by
  cases b <;> simp [contract_eq_self_iff]

lemma remove_singleton_of_notMem (he : e ∉ M.E) : M.remove {e} b = M := by
  simpa
