import Mathlib.Data.Matroid.IndepAxioms

variable {α : Type*}

namespace Matroid

def ofExistsMatroidIndep (E : Set α) (Indep : Set α → Prop)
    (hM : ∃ M : Matroid α, E = M.E ∧ ∀ I, M.Indep I ↔ Indep I) : Matroid α :=
  (IndepMatroid.ofExistsMatroid E Indep hM).matroid

@[simp] theorem ofExistsMatroidIndep_indep_iff {E I : Set α} {Indep : Set α → Prop} {hM} :
    (ofExistsMatroidIndep E Indep hM).Indep I ↔ Indep I := by
  simp [ofExistsMatroidIndep, IndepMatroid.ofExistsMatroid]

@[simp] theorem ofExistsMatroidIndep_ground_eq {E : Set α} {Indep : Set α → Prop} {hM} :
    (ofExistsMatroidIndep E Indep hM).E = E := rfl
