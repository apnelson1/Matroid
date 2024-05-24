import Matroid.Closure
import Mathlib.SetTheory.Ordinal.Basic

variable {α : Type*}


open Set


lemma cl_iInter_eq_iInter_cl'.{u} {M : Matroid α} {Xs : Ordinal.{u} → Set α}
    (h : ∀ ⦃i j⦄, Xs i ⊆ Xs j ∨ Xs j ⊆ Xs i) (b : Ordinal.{u}) :
      M.cl (⋂ i ∈ Iic b, Xs i) = ⋂ i ∈ Iic b, M.cl (Xs i) := by
  sorry


lemma foo.{u} {ι : Type u} {M : Matroid α} (P : Set ι → Prop) (h_empty : P ∅): P univ := by
  set r : ι → ι → Prop := WellOrderingRel
  suffices hwin : ∀ (o : Ordinal.{u}) (ho : o ≤ Ordinal.type r),
      P (range (fun p : Iio o ↦ Ordinal.enum r p.1 (lt_of_lt_of_le p.2 ho))) by
    convert hwin (Ordinal.type r) rfl.le
    rw [eq_comm, eq_univ_iff_forall]
    refine fun i ↦ ⟨⟨Ordinal.typein r i, Ordinal.typein_lt_type r i⟩, Ordinal.enum_typein _ _⟩
  intro o
  induction' o using Ordinal.induction with p hp
  intro hpr



    -- M.cl (⋂ (o' : Ordinal.{u}) (ho' : o' < o), Xs (Ordinal.enum r o' (ho'.trans ho))) = {k}

lemma cl_iInter_eq_iInter_cl.{u} {ι : Type u} {M : Matroid α} {Xs : ι → Set α} {k : α}
    (h : ∀ ⦃i j⦄, Xs i ⊆ Xs j ∨ Xs j ⊆ Xs i) : M.cl (⋂ i, Xs i) = {k} := by
  set r : ι → ι → Prop := WellOrderingRel
  -- set ords := {o : Ordinal.{u} // o ≤ Ordinal.type r}
  -- set setList : ords → Set ι := fun p ↦ Ordinal.enum r p.1 p.2

  set P : Set ι → Prop := fun I ↦ M.cl (⋂ i ∈ I, Xs i) = ⋂ i ∈ I, M.cl (Xs i)

  -- set setlist := fun p : Iio o ↦ Ordinal.enum r p.1 (lt_of_lt_of_le p.2 ho)


  suffices hwin : ∀ (o : Ordinal.{u}) (ho : o ≤ Ordinal.type r),
      P (range (fun p : Iio o ↦ Ordinal.enum r p.1 (lt_of_lt_of_le p.2 ho))) by

    convert hwin (Ordinal.type r) rfl.le
    -- rw [eq_comm, eq_univ_iff_forall]
    -- refine fun i ↦ ⟨⟨Ordinal.typein r i, Ordinal.typein_lt_type r i⟩, Ordinal.enum_typein _ _⟩

  -- set P : Iic (Ordinal.type r) → Prop :=
  --   fun ⟨p,ple⟩ ↦ M.cl (⋂ o ∈ Iic p, Xs (enum o)) = ⋂ o ∈ Iic p, M.cl (Xs (enum o))






  set r : ι → ι → Prop := WellOrderingRel
  suffices : ∀ (o : Ordinal.{u}) (ho : o < Ordinal.type r),
    M.cl (⋂ (o' : Ordinal.{u}) (ho' : o' < o), Xs (Ordinal.enum r o' (ho'.trans ho))) = {k}
  sorry
