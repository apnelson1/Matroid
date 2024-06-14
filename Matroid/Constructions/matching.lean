import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Fintype.Basic
import Matroid.Rank

variable {α β : Type*}

def matching (G : α → β → Prop) (IM :Set α) (JM : Set β)(f : β → α) :=  Set.BijOn f JM IM ∧ (∀ v ∈ JM, G (f v) v)

lemma invFunOn_subset_mem {A :Set β } {B : Set β}{f : β → α}{e : α}(hB : Set.BijOn f B  (f '' B))(hs : A ⊆ B)(he :e ∈ f '' A)[Nonempty β]: Function.invFunOn f B e ∈ A := by
  have : Function.invFunOn f B e = Function.invFunOn f A e := by
    have : f (Function.invFunOn f B e) = f (Function.invFunOn f A e) := by
      rw [Function.invFunOn_eq (Set.BijOn.surjOn hB ((Set.monotone_image hs) he))]
      rw [Function.invFunOn_eq (Set.surjOn_image f A he)]
    apply Set.BijOn.injOn hB (Function.invFunOn_mem (Set.BijOn.surjOn hB ((Set.monotone_image hs) he))) (hs (Function.invFunOn_mem (Set.surjOn_image f A he))) this
  rw [this]
  apply Function.invFunOn_mem (Set.surjOn_image f A he)

def Matroid_from_bipartite [Fintype α] [Fintype β][Nonempty β] (MA: Matroid α) (G : α → β → Prop) : ∀ I J f,
matching G I J f → IndepMatroid β := by
  refine fun IM JM f hM ↦ ?_
  rw [matching] at hM

  set Bmatch := fun (I : Set α) (J : Set β) ↦ I ⊆ IM ∧ J ⊆ JM ∧ f '' J = I with hBM
  set BIndep := fun (J : Set β) ↦ ∃ I : Set α, MA.Indep I ∧ Bmatch I J  with hBI

  have h_indep_empty : BIndep ∅ := by
    rw [hBI, hBM]
    simp only [Set.empty_subset, Set.image_empty, true_and, exists_eq_right_right',
      Matroid.empty_indep, and_self]

  exact IndepMatroid.ofFinite
    Set.finite_univ
    (Indep := fun I => BIndep I)
    (indep_empty := h_indep_empty)
    (indep_subset := by
      refine fun I J hJ hIJ ↦ ?_
      rw [hBI, hBM]
      rw [hBI, hBM] at hJ
      obtain ⟨JA, hJA, h₁, h₂, hJA'⟩ := hJ
      set IA := f '' I with hIA'
      have:  IA ⊆ JA := by
        rw [hIA', ← hJA']
        apply Set.image_subset f hIJ
      refine ⟨IA, Matroid.Indep.subset hJA this, subset_trans this h₁, subset_trans hIJ h₂, hIA'⟩
      )
    (indep_aug := by
      refine fun I J hI hJ hIJ ↦ ?_
      obtain ⟨ IA, hIAI, hIAM⟩ := hI
      obtain ⟨ JA, hJAI, hJAM⟩ := hJ
      rw [hBM] at hIAM hJAM
      have : IA.ncard < JA.ncard := by
        have hI : IA.ncard = I.ncard := by
          rw [← hIAM.right.right]
          apply Set.ncard_image_of_injOn (Set.InjOn.mono hIAM.right.left (Set.BijOn.injOn hM.left))
        have hJ : JA.ncard = J.ncard := by
          rw [← hJAM.right.right]
          apply Set.ncard_image_of_injOn (Set.InjOn.mono hJAM.right.left (Set.BijOn.injOn hM.left))
        rw [hI, hJ] ; assumption
      obtain ⟨e, he, heIA⟩ := Matroid.Indep.exists_insert_of_ncard_lt hIAI hJAI this
      set c := Function.invFunOn f JM e with hc
      refine ⟨c, ?_, ?_, ?_⟩
      · rw [hc]
        apply invFunOn_subset_mem (Set.InjOn.bijOn_image (Set.BijOn.injOn hM.left)) hJAM.right.left
        rw [hJAM.right.right]; exact Set.mem_of_mem_diff he
      · contrapose! he
        have hIbij: Set.BijOn f I (f '' I) := by
          refine ⟨Set.mapsTo_image f I, Set.InjOn.mono hIAM.right.left (Set.BijOn.injOn hM.left), Set.surjOn_image f I⟩
        simp only [Set.mem_diff, not_and, not_not]
        refine fun hJe ↦ ?_
        rw [hc] at he
        have h: f (Function.invFunOn f JM e) ∈ f '' I := Set.mem_image_of_mem f he
        have : f (Function.invFunOn f JM e) = e := Function.invFunOn_eq (Set.BijOn.surjOn hM.left (hJAM.left hJe))
        rw [← this,← hIAM.right.right]; exact h
      · refine ⟨(insert e IA), heIA, Set.insert_subset (hJAM.left (Set.mem_of_mem_diff he)) hIAM.left, Set.insert_subset (Function.invFunOn_mem (Set.BijOn.surjOn hM.left (hJAM.left (Set.mem_of_mem_diff he)))) hIAM.right.left, ?_⟩
        rw [Set.image_insert_eq, hIAM.right.right, Function.invFunOn_eq (Set.BijOn.surjOn hM.left (hJAM.left (Set.mem_of_mem_diff he)))]
    )

    (subset_ground := by
      refine fun I _ ↦ Set.subset_univ I
      )
