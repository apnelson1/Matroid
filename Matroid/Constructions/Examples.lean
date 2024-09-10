import Matroid.Constructions.NonSpanningCircuits
import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual

-- import Matroid.Equiv

-- import Matroid.Flat
-- import Matroid.Constructions.Relax

open Set


namespace Matroid
-- M(K₄) in p640 of Oxley, vertices numbered in a Z pattern
def M_K₄ : Matroid (Fin 6) := by
  set Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {1, 3, 5}, {0, 4, 5}} : Set (Finset (Fin 6)))
  set rk := 3
  set E := @univ (Fin 6)
  set Circuit := fun C ↦ Circuit' C ∨ C.card = rk + 1 ∧ (∀ ⦃C'⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C

  exact FinsetCircuit'Matroid.matroid <| FinsetCircuit'Matroid.mk
    (Circuit := Circuit)
    (circuit_iff := by refine fun _ ↦ by simp only [Circuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := @univ (Fin 6))
    (rk := 3)
    (Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {1, 3, 5}, {0, 4, 5}} : Set (Finset (Fin 6))))
    (empty_not_circuit' := by simp only; tauto)
    (circuit'_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      simp only [Fin.isValue, mem_setOf_eq] at hs ht
      obtain hs | hs | hs | hs := hs
        <;> obtain ht | ht | ht | ht := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (circuit'_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry) -- aesop works here, but it's slow
    (circuit'_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_circuit'less_rk_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true
      ,Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
      -- uhmmm long simps
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])

lemma hyperplane_stuff :1= 1 := by sorry



-- W³ in p641 of Oxley, vertices numbered from the top in the clock-wise order
def W3 :  Matroid (Fin 6) := by
  set Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {0, 4, 5}} : Set (Finset (Fin 6)))
  set rk := 3
  set E := @univ (Fin 6)
  set Circuit := fun C ↦ Circuit' C ∨ C.card = rk + 1 ∧ (∀ ⦃C'⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C

  exact FinsetCircuit'Matroid.matroid <| FinsetCircuit'Matroid.mk
    (Circuit := Circuit)
    (circuit_iff := by refine fun _ ↦ by simp only [Circuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rk := 3)
    (Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {0, 4, 5}} : Set (Finset (Fin 6))))
    (empty_not_circuit' := by simp only; tauto)
    (circuit'_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      simp only [Fin.isValue, mem_setOf_eq] at hs ht
      obtain hs | hs | hs := hs
        <;> obtain ht | ht | ht := ht
        <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction
      )
    (circuit'_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry)-- aesop also works here, and also slow
    (circuit'_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_circuit'less_rk_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])



-- lemma relax M_K₄ = W3



-- Q₆ in p641 of Oxley, vertices numbered from the top in the counterclock-wise order
def Q₆ :  Matroid (Fin 6) := by
  set Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}} : Set (Finset (Fin 6)))
  set rk := 3
  set E := @univ (Fin 6)
  set Circuit := fun C ↦ Circuit' C ∨ C.card = rk + 1 ∧ (∀ ⦃C'⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C

  exact FinsetCircuit'Matroid.matroid <| FinsetCircuit'Matroid.mk
    (Circuit := Circuit)
    (circuit_iff := by refine fun _ ↦ by simp only [Circuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rk := 3)
    (Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}} : Set (Finset (Fin 6))))
    (empty_not_circuit' := by simp only; tauto)
    (circuit'_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      simp only [Fin.isValue, mem_setOf_eq] at hs ht
      obtain hs | hs := hs
        <;> obtain ht | ht := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction
    )
    (circuit'_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry)-- aesop still works here, a bit faster though
    (circuit'_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_circuit'less_rk_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])

-- lemma relax W3 = Q₆

-- Q₆ in p641 of Oxley, vertices numbered from the top in the counterclock-wise order
def P₆ :  Matroid (Fin 6) := by
  set Circuit' := fun I ↦ I = ({2, 3, 4} : (Finset (Fin 6)))
  set rk := 3
  set E := @univ (Fin 6)
  set Circuit := fun C ↦ Circuit' C ∨ C.card = rk + 1 ∧ (∀ ⦃C'⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C

  exact FinsetCircuit'Matroid.matroid <| FinsetCircuit'Matroid.mk
    (Circuit := Circuit)
    (circuit_iff := by refine fun _ ↦ by simp only [Circuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rk := 3)
    (Circuit' := fun I ↦ I = ({2, 3, 4} : (Finset (Fin 6))))
    (empty_not_circuit' := by simp only; tauto)
    (circuit'_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff, Fin.isValue,
      setOf_eq_eq_singleton, pairwise_singleton])
    (circuit'_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ ?_
      subst h1 h2
      simp_all only [Fin.isValue, ne_eq, not_true_eq_false])
    (circuit'_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_circuit'less_rk_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, forall_eq, Finset.mem_insert, Fin.reduceEq,
      Finset.mem_singleton, or_self, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd, le_refl])


-- R₆ in p642 of Oxley, vertices numbered from the top left in the clock-wise order
def R₆ :  Matroid (Fin 6) := by
  set Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {3, 4, 5}} : Set (Finset (Fin 6)))
  set rk := 3
  set E := @univ (Fin 6)
  set Circuit := fun C ↦ Circuit' C ∨ C.card = rk + 1 ∧ (∀ ⦃C'⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C

  exact FinsetCircuit'Matroid.matroid <| FinsetCircuit'Matroid.mk
    (Circuit := Circuit)
    (circuit_iff := by refine fun _ ↦ by simp only [Circuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rk := 3)
    (Circuit' := fun I ↦ I ∈ ({{0, 1, 2}, {3, 4, 5}} : Set (Finset (Fin 6))))
    (empty_not_circuit' := by simp only; tauto)
    (circuit'_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      simp only [Fin.isValue, mem_setOf_eq] at hs ht
      obtain hs | hs := hs
        <;> obtain ht | ht := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (circuit'_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry)
    (circuit'_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_circuit'less_rk_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])




lemma R₆_id_self_dual : R₆✶ = R₆ := by
  have h : R₆.rk = 3 := FinsetCircuit'Matroid.matroid_rk_eq
  have : R₆.E.ncard = 6 := by
    simp only [R₆, FinsetCircuit'Matroid.matroid_E, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain h' := this ▸ h ▸ rk_add_dual_rk R₆
  have : R₆✶.rk = 3 := by linarith
  refine eq_of_circuit'_iff_circuit'_forall rfl (fun C hC ↦ ?_) ?_
  · have : R₆✶.Circuit' C ↔ (C = {0, 1, 2} ∨ C = {3, 4, 5}) := by
      refine Iff.intro ?_ fun hc ↦ ?_
      · sorry
      · simp [Circuit', cocircuit_iff_minimal_compl_nonspanning, this]
        refine ⟨?_, by aesop⟩
        · obtain hc | hc := hc
          sorry
          sorry
    sorry
  · linarith





-- Fano matroid in p643 of Oxley, vertices numbered from the top top-down left-right
def F₇ :  Matroid (Fin 7) := by
  set Circuit' := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6},
    {1, 3, 5}} : Set (Finset (Fin 7)))
  set rk := 3
  set E := @univ (Fin 7)
  set Circuit := fun C ↦ Circuit' C ∨ C.card = rk + 1 ∧ (∀ ⦃C'⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C

  exact FinsetCircuit'Matroid.matroid <| FinsetCircuit'Matroid.mk
    (Circuit := Circuit)
    (circuit_iff := by refine fun _ ↦ by simp only [Circuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rk := 3)
    (Circuit' := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6},
      {1, 3, 5}} : Set (Finset (Fin 7))))
    (empty_not_circuit' := by simp only; tauto)
    (circuit'_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      obtain hs | hs | hs | hs | hs | hs | hs := hs
        <;> obtain ht | ht | ht | ht | ht | ht | ht := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (circuit'_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry) -- takes too long for aesop :(
    (circuit'_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_circuit'less_rk_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])



-- non Fano matroid in p643 of Oxley, vertices numbered from the top top-down left-right
def nonF₇ :  Matroid (Fin 7) := by
  set Circuit' := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6}}
    : Set (Finset (Fin 7)))
  set rk := 3
  set E := @univ (Fin 7)
  set Circuit := fun C ↦ Circuit' C ∨ C.card = rk + 1 ∧ (∀ ⦃C'⦄, Circuit' C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬Circuit C

  exact FinsetCircuit'Matroid.matroid <| FinsetCircuit'Matroid.mk
    (Circuit := Circuit)
    (circuit_iff := by refine fun _ ↦ by simp only [Circuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rk := 3)
    (Circuit' := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6}}
      : Set (Finset (Fin 7))))
    (empty_not_circuit' := by simp only; tauto)
    (circuit'_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      obtain hs | hs | hs | hs | hs | hs  := hs
        <;> obtain ht | ht | ht | ht | ht | ht  := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (circuit'_elimination := by
      refine fun C₁ C₂ e hs ht hne hin hcard ↦ by
        obtain hs | hs | hs | hs | hs | hs  := hs
        <;> obtain ht | ht | ht | ht | ht | ht  := ht
          <;> subst ht hs
          <;> simp only [Fin.isValue, ne_eq, not_true_eq_false] at hne

        <;> sorry  ) -- takes too long for aesop :(
    (circuit'_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_circuit'less_rk_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])
