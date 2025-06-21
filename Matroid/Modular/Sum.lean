import Matroid.Modular.Flat

open Set Function

variable {ι α : Type*} {M : Matroid α} {B I J X X' Y Y' F F' F₀ F₁ F₂ : Set α} {e : α}

namespace Matroid

structure ModularSumFamily (ι α : Type*) where
  M : ι → Matroid α
  S : Matroid α
  F : Set α
  ground_s_eq : S.E = F
  restriction_eq : ∀ i, (M i) ↾ F = S
  modular : ∀ i, (M i).IsModularFlat F
  pairwise_inter : ∀ ⦃i j⦄, i ≠ j → (M i).E ∩ (M j).E = F

namespace ModularSumFamily

variable {U : ModularSumFamily ι α} {i j : ι}

@[simp]

lemma pairwiseDisjoint (U : ModularSumFamily ι α) :
    Pairwise (Disjoint on (fun i ↦ (U.M i).E \ U.F)) := by
  intro i j hij
  simp [disjoint_iff_inter_eq_empty, diff_inter_diff_right, U.pairwise_inter hij, U.ground_s_eq]

protected def E (U : ModularSumFamily ι α) : Set α := ⋃ i, (U.M i).E

lemma ground_subset (U : ModularSumFamily ι α) (i : ι) : (U.M i).E ⊆ U.E :=
  subset_iUnion (fun i ↦ (U.M i).E) i

-- def interAt (U : ModularSumFamily ι α) (i : ι) (X : Set α) : Set α := (U.M i).closure X ∩ U.F

-- lemma interAt_mono (U : ModularSumFamily ι α) (i : ι) (hXY : X ⊆ Y) :
--     U.interAt i X ⊆ U.interAt i Y :=
--   inter_subset_inter_left _ <| closure_mono _ hXY

-- def IndepAt (U : ModularSumFamily ι α) (i : ι) (I : Set α) : Prop :=
--     (U.M i ／ ⋃ j ∈ ({i} : Set ι)ᶜ, (U.interAt j I)).Indep (I ∩ (U.M i).E)

-- def Indep (U : ModularSumFamily ι α) (I : Set α) : Prop := ∀ i, U.IndepAt i I

-- lemma IndepAt.subset (hI : U.IndepAt i I) (hJI : J ⊆ I) : U.IndepAt i J := by
--   refine (Matroid.Indep.subset hI (inter_subset_inter_left _ hJI)).of_isMinor ?_
--   exact contract_isMinor_of_subset _ <| iUnion₂_mono fun i hi ↦ U.interAt_mono _ hJI

-- lemma Indep.subset (hI : U.Indep I) (hJI : J ⊆ I) : U.Indep J :=
--   fun i ↦ (hI i).subset hJI

protected def proj (U : ModularSumFamily ι α) (X : Set α) (i : ι) : Set α :=
    (U.M i).closure X ∩ U.F

@[mk_iff]
protected structure Indep (U : ModularSumFamily ι α) (I : Set α) : Prop where
  subset_ground : I ⊆ U.E
  forall_indep : ∀ i, (U.M i).Indep (I ∩ (U.M i).E)
  skew : U.S.IsSkewFamily (fun i ↦ ((U.M i).closure (I \ U.F)) ∩ U.F)

lemma Indep.subset (hI : U.Indep I) (hJI : J ⊆ I) : U.Indep J := by
  obtain ⟨hIE, hIi, hsk⟩ := hI
  refine ⟨hJI.trans hIE, fun i ↦ (hIi i).subset (inter_subset_inter_left _ hJI), hsk.mono ?_⟩
  exact fun i ↦ inter_subset_inter_left _ <| closure_subset_closure _ <| diff_subset_diff_left hJI

lemma maximal_foo (I : Set α) (hI : U.Indep I) (hIX : I ⊆ X) (hX : X ⊆ U.E) :
    Maximal (fun J ↦ U.Indep J ∧ J ⊆ X) I ↔
    ∀ i, X ∩ (U.M i).E ⊆ (U.M i).closure (⋃ j, (U.M j).closure I) := by
  refine ⟨fun h i e ⟨heX, hei⟩ ↦ ?_, fun h ↦ ?_⟩
  · by_cases heI : e ∈ I
    · refine mem_of_mem_of_subset (mem_inter heI hei) (subset_closure_of_subset' _ ?_)
      exact subset_iUnion_of_subset i <| inter_ground_subset_closure (U.M i) I
    have hni := h.not_prop_of_ssuperset (ssubset_insert heI)
    rw [and_iff_left (insert_subset heX hIX), indep_iff,
      and_iff_right ((insert_subset_insert hIX).trans (by rwa [insert_eq_of_mem heX]))] at hni
    simp only [not_and] at hni
    by_cases hecl : ∃ j, e ∈ (U.M j).closure I
    · obtain ⟨j, hj⟩ := hecl
      rw [← closure_closure] at hj
      refine mem_of_mem_of_subset hj ?_


    by_cases heIcl : e ∈ (U.M i).closure I
    · rw [← closure_closure] at heIcl
      exact mem_of_mem_of_subset heIcl <| closure_subset_closure _ <|
        subset_iUnion (fun j ↦ (U.M j).closure I) i
    rw [← closure_inter_ground, (hI.forall_indep i).notMem_closure_iff_of_notMem (by simp [heI]),
      ← insert_inter_of_mem hei] at heIcl

    by_cases heF : e ∈ U.F
    · rw [insert_diff_of_mem _ heF, imp_not_comm, imp_iff_right hI.skew, not_forall] at hni
      obtain ⟨j, hj⟩ := hni

    -- specialize hni (fun j ↦ ?_)
    -- · obtain rfl | hne := eq_or_ne i j
    --   · assumption
    --   rw [insert_inter_of_notMem]


lemma Indep.exists_augment_of_not_maximal (hI : U.Indep I) (hnotmax : ¬ Maximal U.Indep I)
    (hmax : Maximal U.Indep B) : ∃ e ∈ B \ I, U.Indep (insert e I) := by
  by_contra! hcon
  obtain ⟨x, hx, hxI⟩ := exists_insert_of_not_maximal (fun _ _ ↦ Indep.subset) hI hnotmax

  obtain ⟨i, hxi⟩ := show ∃ i, x ∈ (U.M i).E by
    simpa [ModularSumFamily.E, mem_iUnion] using hxI.subset_ground <| mem_insert ..

  have hxB : x ∉ B := fun hxB ↦ hcon _ ⟨hxB, hx⟩ hxI
  have hxBni := hmax.not_prop_of_ssuperset (ssubset_insert hxB)

  simp only [indep_iff, insert_subset_iff, U.ground_subset i hxi, hmax.prop.subset_ground, and_self,
    true_and, not_and] at hxBni
  specialize hxBni (fun j ↦ ?_)
  · sorry
  sorry








-- lemma indep_iff_foo {I : Set α} (J : ι → Set α)
--     (hJ : ∀ i, (U.M i).IsBasis (J i) ((U.M i).closure I)) :
--     U.Indep' I ↔ ∀ i, (U.M i).Indep (I ∩ (U.M i).E) ∧
