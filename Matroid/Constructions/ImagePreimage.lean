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

def image (M : Matroid α) (f : α ↪ β) : Matroid β := matroid_of_base 
  ( f '' M.E )
  ( fun B ↦ M.Base (f ⁻¹' B) ∧ B ⊆ f '' M.E ) 
  ( by 
    obtain ⟨B, hB⟩ := M.exists_base
    exact ⟨f '' B, (by rwa [preimage_image_eq _ f.injective] : M.Base (f ⁻¹' (f '' B))), 
      image_subset _ hB.subset_ground⟩ )
  ( by 
    rintro B B' ⟨(hB : M.Base _), hBE⟩ ⟨(hB' : M.Base _), hB'E⟩ b hb
    obtain ⟨a,ha,rfl⟩ := hBE hb.1
    obtain ⟨y, ⟨(hyB' : f y ∈ B'), (hyB : f y ∉ B)⟩, hy'⟩ := hB.exchange hB' (e := a) (by aesop)
    exact ⟨_, ⟨hyB', hyB⟩, by convert hy'; ext; aesop, insert_subset (hB'E hyB')
      ((diff_subset _ _).trans hBE)⟩ )
  ( by 
    intro X hX I hI hIX 

    )
  sorry

def image' (M : Matroid α) (f : α ↪ β) : Matroid β := matroid_of_indep
  ( f '' M.E )
  ( fun I ↦ M.Indep (f ⁻¹' I) ∧ I ⊆ f '' M.E ) 
  ( by simp )
  ( fun I J ⟨hJ, hJE⟩ hIJ ↦ ⟨hJ.subset (preimage_mono hIJ), hIJ.trans hJE⟩ )
  ( by 
    intro I B hI hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, and_imp, iff_true_intro hI, true_and, 
      not_forall, exists_prop, exists_and_left] at hBmax hImax 
    obtain ⟨J, hJ, (hJE : J ⊆ f '' M.E) , hIJ, hne⟩ := hImax 
    obtain ⟨⟨hBi, (hBss : B ⊆ f '' M.E)⟩, hmax⟩ := hBmax 
    obtain ⟨B, rfl⟩ := subset_range_iff_exists_image_eq.1 (hBss.trans (image_subset_range _ _))
    obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.1 (hJE.trans (image_subset_range _ _))
    obtain ⟨I, rfl⟩ := subset_range_iff_exists_image_eq.1 (hI.2.trans (image_subset_range _ _))
    simp_rw [preimage_subset_preimage_]
    have hIb : ¬ M.Base I
    · refine fun hIb ↦ hne ?_
      -- have := hIb.eq_of_subset_indep hJ 
      sorry
      -- sorryhave := 
    have hIb : ¬ M.Base (f ⁻¹' I)
    · refine fun hIb ↦ hne ?_  
      have he := hIb.eq_of_subset_indep hJ (preimage_mono hIJ)
      rwa [preimage_eq_preimage' (hI.2.trans (image_subset_range _ _))
        (hJE.trans (image_subset_range _ _))] at he 
    have hBb : M.Base (f ⁻¹' B)
    · refine hBi.base_of_maximal (fun K hK hBK ↦ ?_) 
      rw [hmax (y := f '' K) (by convert hK; aesop) (image_subset _ hK.subset_ground), 
        f.injective.preimage_image]
      

      -- have := image_subset f hBK 
    have' := hI.1.exists_insert_of_not_base (B := f ⁻¹' B) ?_ ?_ 


    )
  
  -- ( by 
  --   rintro B B' ⟨(hB : M.Base _), hBE⟩ ⟨(hB' : M.Base _), hB'E⟩ b hb
  --   obtain ⟨a,ha,rfl⟩ := hBE hb.1
  --   obtain ⟨y, ⟨(hyB' : f y ∈ B'), (hyB : f y ∉ B)⟩, hy'⟩ := hB.exchange hB' (e := a) (by aesop)
  --   exact ⟨_, ⟨hyB', hyB⟩, by convert hy'; ext; aesop, insert_subset (hB'E hyB')
  --     ((diff_subset _ _).trans hBE)⟩ )
  ( by 
    intro X hX I hI hIX 
    sorry 
    )
  sorry
  sorry 


end Image
  

