import Matroid.Order.Quotient

variable {α : Type*} {M : Matroid α} {X Y I J B : Set α}

namespace Matroid

open Set

def project (M : Matroid α) (X : Set α) := (M ／ X) ↾ M.E

@[simp] lemma project_ground_eq (M : Matroid α) (X : Set α) : (M.project X).E = M.E := rfl

lemma Indep.project_indep_iff (hI : M.Indep I) :
    (M.project I).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint J I := by
  rw [project, restrict_indep_iff, hI.contract_indep_iff, and_assoc, and_comm (b := Disjoint _ _),
    ← and_assoc, and_iff_left_iff_imp, and_imp]
  exact fun _ h ↦ (h.subset subset_union_left).subset_ground
