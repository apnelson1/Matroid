import Matroid.Constructions.Basic
import Matroid.ForMathlib.Other

open Set Function

variable {α β : Type _} {f : α → β} {E I s : Set α}

namespace Matroid
  
/-- Given a `Matroid` `M` on `β` and a function `f : α → β`, this is the matroid on `α` 
  obtained by replacing each `x ∈ M.E` by the fiber `f ⁻¹' {x}` of pairwise parallel elements -/
def parallel_preimage (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := matroid_of_indep
  E ( fun I ↦ M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E ) ( by simp )
  ( fun I J ⟨h, h', hE⟩ hIJ ↦ ⟨h.subset (image_subset _ hIJ), InjOn.mono hIJ h', hIJ.trans hE⟩ )
  ( by
    rintro I J ⟨hI, hIinj, hIE⟩ hImax hJmax

    simp only [mem_maximals_iff, mem_setOf_eq, and_imp, hI, hIinj, hIE, and_self, true_and, 
      not_forall, exists_prop, exists_and_left] at hJmax hImax 
    
    obtain ⟨B', hB', hB'inj, hB'E, hIB', hne⟩ := hImax 
    obtain ⟨⟨hJ, hJinj, hJE⟩, hJmax⟩ := hJmax
  
    have hi : (M ↾ f '' E).Indep (f '' I) := hI.indep_restrict_of_subset (image_subset f hIE)

    have h1 : ¬(M ↾ f '' E).Base (f '' I)
    · exact fun hB ↦ hne <| (hB'inj.image_eq_image_iff_of_subset hIB' Subset.rfl).1
        (hB.eq_of_subset_indep (hB'.indep_restrict_of_subset (image_subset _ hB'E))
        (image_subset _ hIB'))
      
    have h2 : (M ↾ f '' E).Base (f '' J)
    · apply (hJ.indep_restrict_of_subset (image_subset _ hJE)).base_of_maximal
      simp_rw [restrict_indep_iff]
      rintro K' ⟨hK', hK'E⟩ hJK'
      obtain ⟨K, hJK, hKE, hKinj, rfl⟩ := hJinj.exists_injOn_superset_image hJE hJK' hK'E
      rw [hJmax hK' hKinj hKE]
      rwa [←hKinj.image_subset_image_iff_of_subset hJK Subset.rfl]
    
    obtain ⟨_, ⟨⟨e, heJ, rfl⟩, heI⟩, hi⟩ := hi.exists_insert_of_not_base h1 h2
    have heI' : e ∉ I := fun heI' ↦ heI (mem_image_of_mem f heI')
    refine' ⟨e, ⟨heJ, heI'⟩, _, _, insert_subset (hJE heJ) hIE⟩ 
    · rw [image_insert_eq]
      exact hi.of_restrict
    rwa [injOn_insert heI', and_iff_right hIinj] )
  ( by
    rintro X hXE I ⟨hI, hIinj, hIE⟩ hIX
    set M' := M ↾ (f '' E)
    have hI' : M'.Indep (f '' I) := restrict_indep_iff.2 ⟨hI, image_subset f hIE⟩ 
    obtain ⟨J, hJX, hIJ⟩ := hI'.subset_basis_of_subset (image_subset f hIX) (image_subset f hXE)
    obtain ⟨J, hIJ', hJX', hJinj, rfl⟩ := hIinj.exists_injOn_superset_image hIX hIJ hJX.subset    
    refine ⟨J, ⟨⟨hJX.indep.of_restrict, hJinj, hJX'.trans hXE⟩, hIJ', hJX'⟩, ?_⟩ 
    rintro B ⟨⟨hB, hBinj, hBE⟩, -, hBX⟩ (hJB : J ⊆ B) b hb
    have hB' : M'.Indep (f '' B) := restrict_indep_iff.2 ⟨hB, image_subset f hBE⟩ 
    have hb' := mem_image_of_mem f hb
    rw [←hJX.eq_of_subset_indep hB' (image_subset f hJB) (image_subset f hBX)] at hb'
    exact hBinj.mem_of_mem_image hJB hb hb' )
  ( fun I h ↦ h.2.2 )

@[simp] theorem parallel_preimage_indep_iff {M : Matroid β} : 
    (M.parallel_preimage E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by 
  simp [parallel_preimage]

@[simp] theorem parallel_preimage_ground_eq {M : Matroid β} : 
    (M.parallel_preimage E f).E = E := rfl 
  
section Image 

/-- Map a matroid to a copy in another type using an injection from the ground set -/
def image (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β := matroid_of_indep
  ( f '' M.E )
  ( fun I ↦ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀) 
  ⟨ ∅, by simp ⟩
  ( by
    rintro I _ ⟨J, hJ, rfl⟩ hIJ 
    refine ⟨f ⁻¹' I ∩ M.E, hJ.subset ?_, ?_⟩ 
    · refine (inter_subset_inter_left M.E (preimage_mono hIJ)).trans ?_ 
      rw [hf.preimage_image_inter hJ.subset_ground]
    simp only [subset_antisymm_iff, image_subset_iff, inter_subset_left, and_true]
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hIJ hx
    exact ⟨_, ⟨hx, hJ.subset_ground hy⟩, rfl⟩ )
  ( by 
    rintro _ B ⟨I, hI, rfl⟩ hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, forall_exists_index, and_imp, image_subset_iff,
      not_and, not_forall, exists_prop, exists_and_left] at hBmax hImax 
    obtain ⟨⟨B, hB, rfl⟩, hmax⟩ := hBmax 
    obtain ⟨_, I', hI', rfl, hII', hne⟩ := hImax _ hI rfl 

    have hIb : ¬ M.Base I
    · refine fun hIb ↦ hne ?_
      rw [hIb.eq_of_subset_indep ?_ (subset_inter hII' hI.subset_ground), 
        hf.preimage_image_inter hI'.subset_ground]
      rwa [hf.preimage_image_inter hI'.subset_ground]
    
    have hB : M.Base B
    · refine hB.base_of_maximal (fun J hJ hBJ ↦ ?_)
      have h_image := hmax  _ hJ rfl (image_subset _ hBJ)
      rwa [hf.image_eq_image_iff_of_subset hB.subset_ground hJ.subset_ground] at h_image
      
    obtain ⟨e, he, hi⟩ := hI.exists_insert_of_not_base hIb hB
    refine ⟨f e, ⟨mem_image_of_mem f he.1, fun h ↦ he.2 ?_⟩, ⟨_, hi, by rw [image_insert_eq]⟩⟩ 
    rwa [hf.mem_image_iff hI.subset_ground (hB.subset_ground he.1)] at h )
  ( by 
    rintro X hX I ⟨I, hI, rfl⟩ hIX 
    obtain ⟨X, hXE, rfl⟩ := exists_eq_image_subset_of_subset_image hX 
    rw [hf.image_subset_image_iff_of_subset hI.subset_ground hXE] at hIX 
    
    obtain ⟨B, hB, hIB⟩ := hI.subset_basis_of_subset hIX 
    refine ⟨f '' B, ?_⟩ 
    simp only [image_subset_iff, mem_maximals_iff, mem_setOf_eq, and_imp, forall_exists_index]
    refine ⟨⟨⟨B, hB.indep, rfl⟩, hIB.trans <| subset_preimage_image _ _, 
      hB.subset.trans <| subset_preimage_image _ _⟩, ?_⟩ 
    rintro _ K hK rfl - hKX hBK
    
    rw [hB.eq_of_subset_indep hK]
    · have hss := subset_inter hBK hB.left_subset_ground
      rwa [hf.preimage_image_inter hK.subset_ground] at hss
    rwa [hf.image_subset_image_iff_of_subset hK.subset_ground hXE] at hKX )
  ( by rintro _ ⟨I, hI, rfl⟩; exact image_subset _ hI.subset_ground )


end Image
  

