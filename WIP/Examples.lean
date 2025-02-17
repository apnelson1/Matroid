import Matroid.Constructions.NonSpanningIsCircuits
import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual


open Set


namespace Matroid
-- M(K₄) in p640 of Oxley, vertices numbered in a Z pattern
def M_K₄ : Matroid (Fin 6) := by
  set NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {1, 3, 5}, {0, 4, 5}} : Set (Finset (Fin 6)))
  set rank := 3
  set E := @univ (Fin 6)
  set IsCircuit := fun C ↦ NonspanningIsCircuit C ∨ C.card = rank + 1 ∧ (∀ ⦃C'⦄, NonspanningIsCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C

  exact FinsetNonspanningCircuitMatroid.matroid <| FinsetNonspanningCircuitMatroid.mk
    (IsCircuit := IsCircuit)
    (circuit_iff := by refine fun _ ↦ by simp only [IsCircuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := @univ (Fin 6))
    (rank := 3)
    (NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {1, 3, 5}, {0, 4, 5}} : Set (Finset (Fin 6))))
    (empty_not_NonspanningIsCircuit := by simp only; tauto)
    (NonspanningIsCircuit_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      simp only [Fin.isValue, mem_setOf_eq] at hs ht
      obtain hs | hs | hs | hs := hs
        <;> obtain ht | ht | ht | ht := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (NonspanningIsCircuit_elimination := by

      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by
        obtain rfl | rfl | rfl | rfl := h1 <;>
        · obtain rfl | rfl | rfl | rfl := h2 <;>
          · simp at hin
            aesop ) -- aesop works here, but it's slow
    (NonspanningIsCircuit_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_NonspanningIsCircuitless_rank_set := by exact ⟨{0, 1, 3}, by simp, by simp; tauto⟩)
      -- uhmmm long simps
    (non_spanning := by simp)

    -- only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
    --   Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
    --   not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
    --   le_refl, forall_eq, and_self])

lemma isHyperplane_stuff : 1= 1 := by sorry



-- W³ in p641 of Oxley, vertices numbered from the top in the clock-wise order
def W3 :  Matroid (Fin 6) := by
  set NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {0, 4, 5}} : Set (Finset (Fin 6)))
  set rank := 3
  set E := @univ (Fin 6)
  set IsCircuit := fun C ↦ NonspanningIsCircuit C ∨ C.card = rank + 1 ∧ (∀ ⦃C'⦄, NonspanningIsCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C

  exact FinsetNonspanningCircuitMatroid.matroid <| FinsetNonspanningCircuitMatroid.mk
    (IsCircuit := IsCircuit)
    (circuit_iff := by refine fun _ ↦ by simp only [IsCircuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rank := 3)
    (NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}, {0, 4, 5}} : Set (Finset (Fin 6))))
    (empty_not_NonspanningIsCircuit := by simp only; tauto)
    (NonspanningIsCircuit_antichain := by
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
    (NonspanningIsCircuit_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry)-- aesop also works here, and also slow
    (NonspanningIsCircuit_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_NonspanningIsCircuitless_rank_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])



-- lemma relax M_K₄ = W3



-- Q₆ in p641 of Oxley, vertices numbered from the top in the counterclock-wise order
def Q₆ :  Matroid (Fin 6) := by
  set NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}} : Set (Finset (Fin 6)))
  set rank := 3
  set E := @univ (Fin 6)
  set IsCircuit := fun C ↦ NonspanningIsCircuit C ∨ C.card = rank + 1 ∧ (∀ ⦃C'⦄, NonspanningIsCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C

  exact FinsetNonspanningCircuitMatroid.matroid <| FinsetNonspanningCircuitMatroid.mk
    (IsCircuit := IsCircuit)
    (circuit_iff := by refine fun _ ↦ by simp only [IsCircuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rank := 3)
    (NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {2, 3, 4}} : Set (Finset (Fin 6))))
    (empty_not_NonspanningIsCircuit := by simp only; tauto)
    (NonspanningIsCircuit_antichain := by
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
    (NonspanningIsCircuit_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry)-- aesop still works here, a bit faster though
    (NonspanningIsCircuit_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_NonspanningIsCircuitless_rank_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])

-- lemma relax W3 = Q₆

-- Q₆ in p641 of Oxley, vertices numbered from the top in the counterclock-wise order
def P₆ :  Matroid (Fin 6) := by
  set NonspanningIsCircuit := fun I ↦ I = ({2, 3, 4} : (Finset (Fin 6)))
  set rank := 3
  set E := @univ (Fin 6)
  set IsCircuit := fun C ↦ NonspanningIsCircuit C ∨ C.card = rank + 1 ∧ (∀ ⦃C'⦄, NonspanningIsCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C

  exact FinsetNonspanningCircuitMatroid.matroid <| FinsetNonspanningCircuitMatroid.mk
    (IsCircuit := IsCircuit)
    (circuit_iff := by refine fun _ ↦ by simp only [IsCircuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rank := 3)
    (NonspanningIsCircuit := fun I ↦ I = ({2, 3, 4} : (Finset (Fin 6))))
    (empty_not_NonspanningIsCircuit := by simp only; tauto)
    (NonspanningIsCircuit_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff, Fin.isValue,
      setOf_eq_eq_singleton, pairwise_singleton])
    (NonspanningIsCircuit_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ ?_
      subst h1 h2
      simp_all only [Fin.isValue, ne_eq, not_true_eq_false])
    (NonspanningIsCircuit_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_NonspanningIsCircuitless_rank_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, forall_eq, Finset.mem_insert, Fin.reduceEq,
      Finset.mem_singleton, or_self, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd, le_refl])


-- R₆ in p642 of Oxley, vertices numbered from the top left in the clock-wise order
def R₆ :  Matroid (Fin 6) := by
  set NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {3, 4, 5}} : Set (Finset (Fin 6)))
  set rank := 3
  set E := @univ (Fin 6)
  set IsCircuit := fun C ↦ NonspanningIsCircuit C ∨ C.card = rank + 1 ∧ (∀ ⦃C'⦄, NonspanningIsCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C

  exact FinsetNonspanningCircuitMatroid.matroid <| FinsetNonspanningCircuitMatroid.mk
    (IsCircuit := IsCircuit)
    (circuit_iff := by refine fun _ ↦ by simp only [IsCircuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rank := 3)
    (NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 2}, {3, 4, 5}} : Set (Finset (Fin 6))))
    (empty_not_NonspanningIsCircuit := by simp only; tauto)
    (NonspanningIsCircuit_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      simp only [Fin.isValue, mem_setOf_eq] at hs ht
      obtain hs | hs := hs
        <;> obtain ht | ht := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (NonspanningIsCircuit_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry)
    (NonspanningIsCircuit_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_NonspanningIsCircuitless_rank_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])




lemma R₆_id_self_dual : R₆✶ = R₆ := by
  have h : R₆.rank = 3 := FinsetNonspanningCircuitMatroid.matroid_rank_eq
  have : R₆.E.ncard = 6 := by
    simp only [R₆, FinsetNonspanningCircuitMatroid.matroid_E, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain h' := this ▸ h ▸ rank_add_dual_rank R₆
  have : R₆✶.rank = 3 := by linarith
  refine eq_of_NonspanningIsCircuit_iff_NonspanningIsCircuit_forall rfl (fun C hC ↦ ?_) ?_
  · have : R₆✶.NonspanningIsCircuit C ↔ (C = {0, 1, 2} ∨ C = {3, 4, 5}) := by
      refine Iff.intro ?_ fun hc ↦ ?_
      · sorry
      · simp [nonspanningIsCircuit_iff, cocircuit_iff_minimal_compl_nonspanning, this]
        refine ⟨?_, by aesop⟩
        · obtain hc | hc := hc
          sorry
          sorry
    sorry
  · linarith





-- Fano matroid in p643 of Oxley, vertices numbered from the top top-down left-right
def F₇ :  Matroid (Fin 7) := by
  set NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6},
    {1, 3, 5}} : Set (Finset (Fin 7)))
  set rank := 3
  set E := @univ (Fin 7)
  set IsCircuit := fun C ↦ NonspanningIsCircuit C ∨ C.card = rank + 1 ∧ (∀ ⦃C'⦄, NonspanningIsCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C

  exact FinsetNonspanningCircuitMatroid.matroid <| FinsetNonspanningCircuitMatroid.mk
    (IsCircuit := IsCircuit)
    (circuit_iff := by refine fun _ ↦ by simp only [IsCircuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rank := 3)
    (NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6},
      {1, 3, 5}} : Set (Finset (Fin 7))))
    (empty_not_NonspanningIsCircuit := by simp only; tauto)
    (NonspanningIsCircuit_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      obtain hs | hs | hs | hs | hs | hs | hs := hs
        <;> obtain ht | ht | ht | ht | ht | ht | ht := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (NonspanningIsCircuit_elimination := by
      refine fun C₁ C₂ e h1 h2 hne hin hcard ↦ by sorry) -- takes too long for aesop :(
    (NonspanningIsCircuit_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_NonspanningIsCircuitless_rank_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])



-- non Fano matroid in p643 of Oxley, vertices numbered from the top top-down left-right
def nonF₇ :  Matroid (Fin 7) := by
  set NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6}}
    : Set (Finset (Fin 7)))
  set rank := 3
  set E := @univ (Fin 7)
  set IsCircuit := fun C ↦ NonspanningIsCircuit C ∨ C.card = rank + 1 ∧ (∀ ⦃C'⦄, NonspanningIsCircuit C' → ¬C' ⊆ C) ∧ ↑C ⊆ E
  set Indep := fun I ↦ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C

  exact FinsetNonspanningCircuitMatroid.matroid <| FinsetNonspanningCircuitMatroid.mk
    (IsCircuit := IsCircuit)
    (circuit_iff := by refine fun _ ↦ by simp only [IsCircuit])

    (Indep := Indep)
    (indep_iff := by refine fun _ ↦ by simp only [Indep])

    (E := univ)
    (rank := 3)
    (NonspanningIsCircuit := fun I ↦ I ∈ ({{0, 1, 4}, {0, 2, 5}, {0, 3, 6}, {4, 5, 6}, {2, 3, 4}, {1, 2, 6}}
      : Set (Finset (Fin 7))))
    (empty_not_NonspanningIsCircuit := by simp only; tauto)
    (NonspanningIsCircuit_antichain := by
      simp only [IsAntichain, Fin.isValue, mem_insert_iff, mem_singleton_iff]
      refine fun s hs t ht hne ↦ ?_
      obtain hs | hs | hs | hs | hs | hs  := hs
        <;> obtain ht | ht | ht | ht | ht | ht  := ht
          <;> simp only [hs, Fin.isValue, ht, Pi.compl_apply, compl_iff_not]
          <;> tauto
          <;> subst ht hs
          <;> contradiction)
    (NonspanningIsCircuit_elimination := by
      refine fun C₁ C₂ e hs ht hne hin hcard ↦ by
        obtain hs | hs | hs | hs | hs | hs  := hs
        <;> obtain ht | ht | ht | ht | ht | ht  := ht
          <;> subst ht hs
          <;> simp only [Fin.isValue, ne_eq, not_true_eq_false] at hne

        <;> sorry  ) -- takes too long for aesop :(
    (NonspanningIsCircuit_subset_ground := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff,
      subset_univ, implies_true])
    (exists_NonspanningIsCircuitless_rank_set := by exact ⟨{0, 1, 3}, by simp only [Fin.isValue,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd], by simp; tauto⟩)
    (non_spanning := by simp only [Fin.isValue, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      Finset.mem_insert, zero_ne_one, Finset.mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd,
      le_refl, forall_eq, and_self])
