import Matroid.Constructions.Basic



open Set Function

variable {α β : Type _} {f : α → β} {s : Set α}

lemma Function.invFunOn_injOn_image_preimage [_root_.Nonempty α] (f : α → β) (S : Set α) : 
    InjOn f ((invFunOn f S) '' (f '' S)) := by
  rintro _ ⟨_,⟨x,hx, rfl⟩,rfl⟩ _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ h
  rw [invFunOn_eq (f := f) ⟨x, hx, rfl⟩, invFunOn_eq (f := f) ⟨y,hy,rfl⟩] at h
  rw [h]

lemma Set.InjOn.exists_injOn_superset {f : α → β} {s t : Set α} (hinj : InjOn f s) (hst : s ⊆ t) : 
    ∃ r, s ⊆ r ∧ r ⊆ t ∧ InjOn f r ∧ f '' r = f '' t := by 
  
  obtain (hα | hα) := isEmpty_or_nonempty α
  · exact ⟨∅, by simp [eq_empty_of_isEmpty]⟩ 
  set d := t ∩ (f ⁻¹' (f '' t \ f '' s)) with hd
  set g := invFunOn f d with hg
  
  have hdj : Disjoint (f '' s) (f '' d)
  · rw [disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he  
    rw [hd, mem_inter_iff, mem_preimage, ←he] at hb
    exact hb.2.2 (mem_image_of_mem f ha)
  
  refine ⟨s ∪ g '' (f '' d), subset_union_left _ _, union_subset hst ?_, ?_, ?_⟩ 
  · exact (f.invFunOn_image_image_subset _).trans (inter_subset_left _ _)
  · rw [injOn_union, and_iff_right hinj, and_iff_right (f.invFunOn_injOn_image_preimage _)]
    · rintro x hx _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ he
      rw [hg, invFunOn_apply_eq (f := f) hy] at he
      rw [disjoint_iff_forall_ne] at hdj
      exact hdj (mem_image_of_mem f hx) (mem_image_of_mem f hy) he
    · exact disjoint_of_subset_right (f.invFunOn_image_image_subset _) hdj.of_image 
  rw [image_union, subset_antisymm_iff, union_subset_iff, and_iff_right (image_subset _ hst), 
    and_iff_right (image_subset _ _)]
  · rintro _ ⟨x, hxt, rfl⟩
    rw [mem_union]
    by_cases h : f x ∈ f '' s
    · left; assumption
    have hxd : x ∈ d
    · rw [hd, mem_inter_iff, and_iff_right hxt]
      exact ⟨mem_image_of_mem f hxt, h⟩  
    right
    
    refine ⟨g (f x), ⟨f x, ⟨g (f x), ?_, ?_⟩, rfl⟩, ?_⟩  
    · exact mem_of_mem_of_subset (invFunOn_apply_mem (f := f) hxd) Subset.rfl
    · rwa [invFunOn_apply_eq (f := f)]
    · rwa [invFunOn_apply_eq (f := f)]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact mem_of_mem_of_subset (invFunOn_apply_mem (f := f) hx) (inter_subset_left _ _)

lemma Set.InjOn.exists_injOn_superset_image {f : α → β} {s s' : Set α} {t : Set β} 
    (hss' : s ⊆ s') (hinj : InjOn f s) (hst : f '' s ⊆ t) (ht : t ⊆ f '' s') : 
    ∃ r, s ⊆ r ∧ r ⊆ s' ∧ InjOn f r ∧ f '' r = t := by 
  rw [image_subset_iff] at hst
  obtain ⟨r, hsr, hrs', hinj, heq⟩ := hinj.exists_injOn_superset (subset_inter hss' hst)
  rw [subset_inter_iff] at hrs'
  refine ⟨r, hsr, hrs'.1, hinj, ?_⟩ 
  rw [heq, subset_antisymm_iff, image_subset_iff, and_iff_right (inter_subset_right _ _)]
  intro x hxt
  obtain ⟨y, hy, rfl⟩ := ht hxt 
  exact ⟨y, ⟨hy, hxt⟩, rfl⟩  
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
    have hI' : M'.Indep (f '' I)
    · exact restrict_indep_iff.2 ⟨hI, image_subset f hIE⟩ 
    obtain ⟨J, hJX, hIJ⟩ := hI'.subset_basis_of_subset (image_subset f hIX) (image_subset f hXE)
    obtain ⟨J, hIJ', hJX', hJinj, rfl⟩ := hIinj.exists_injOn_superset_image hIX hIJ hJX.subset    
    refine ⟨J, ⟨⟨hJX.indep.of_restrict, hJinj, hJX'.trans hXE⟩, hIJ', hJX'⟩, ?_⟩ 
    rintro B ⟨⟨hB, hBinj, hBE⟩, -, hBX⟩ (hJB : J ⊆ B) b hb
    have hB' : M'.Indep (f '' B)
    · refine restrict_indep_iff.2 ⟨hB, image_subset f hBE⟩ 
    have hb' := mem_image_of_mem f hb
    rw [←hJX.eq_of_subset_indep hB' (image_subset f hJB) (image_subset f hBX)] at hb'
    exact hBinj.mem_of_mem_image hJB hb hb' )
  ( fun I h ↦ h.2.2 )

@[simp] theorem parallel_preimage_indep_iff {M : Matroid β} {E : Set α} {f : α → β} {I : Set α} : 
    (M.parallel_preimage E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by 
  simp [parallel_preimage]

@[simp] theorem parallel_preimage_ground_eq {M : Matroid β} {E : Set α} {f : α → β} : 
    (M.parallel_preimage E f).E = E := rfl 
  
  
