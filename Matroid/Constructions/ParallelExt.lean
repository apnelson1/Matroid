import Matroid.Constructions.Basic



open Set Function

variable {α β : Type _}
 
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
  obtain (hα | hα) := isEmpty_or_nonempty α
  · simp only [eq_empty_of_isEmpty, injOn_empty, image_empty, empty_subset, true_and, 
      exists_const, subset_empty_iff, eq_comm (a := t)] at *
    assumption 
  set d := s' ∩ f ⁻¹' (t \ f '' s) with hd
  set g := f.invFunOn d with hg
  have hds' : d ⊆ s' \ s
  · rw [hd, preimage_diff, subset_diff, and_iff_right (inter_subset_left _ _), 
      disjoint_iff_forall_ne]
    rintro a ⟨has', ha, ha'⟩ b hb rfl 
    exact ha' (mem_image_of_mem _ hb)

  refine ⟨s ∪ (g '' (f '' d)), subset_union_left _ _, union_subset hss' ?_, ?_, ?_⟩
  · refine (invFunOn_image_image_subset _ _).trans (subset_diff.1 hds').1
  · rw [injOn_union, and_iff_right hinj, and_iff_right (invFunOn_injOn_image_preimage _ _)]
    · rintro x hxs _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ he
      rw [invFunOn_apply_eq (f := f) hy] at he
      apply hy.2.2
      rw [←he]
      exact mem_image_of_mem f hxs
    exact disjoint_of_subset_right (invFunOn_image_image_subset _ _) (subset_diff.1 hds').2.symm
  
  rw [image_union, subset_antisymm_iff, union_subset_iff, and_iff_right hst, and_iff_left]
  · rintro _ ⟨_, ⟨_, ⟨ x, hx, rfl⟩, rfl⟩, rfl⟩  
    refine mem_of_mem_of_subset (mem_image_of_mem f (invFunOn_apply_mem (f := f) hx)) ?_
    rintro _ ⟨y, ⟨-, hy⟩, rfl⟩  
    exact hy.1 
  
  · sorry 
  
  -- refine ht.trans ?_
  -- rintro _ ⟨x, hx, rfl⟩ 
  -- by_cases h : f x ∈ f '' s
  -- · left; assumption
  -- rw [mem_union]; right
  -- refine ⟨g (f x), ?_, ?_⟩ 
  -- · rw [invFunOn_]


    
  -- obtain ⟨r, hsr, h', hi, hr⟩ := hinj.exists_injOn_superset (image_subset_iff.1 hst)
  -- refine ⟨r, hsr, ?_, hi, ?_⟩ 
  -- refine ⟨r, hsr, hi, by rwa [hr, image_preimage_eq_iff]⟩  
  
  

  

namespace Matroid
  
def parallel_preimage (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := matroid_of_indep
  E 
  ( fun I ↦ M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E )
  ( by simp )
  ( fun I J ⟨h, h', hE⟩ hIJ ↦ ⟨h.subset (image_subset _ hIJ), InjOn.mono hIJ h', hIJ.trans hE⟩ )
  ( by
    rintro I J ⟨hI, hIinj, hIE⟩ hImax hJmax

    have hI1 : ¬M.Base (f '' I)
    · refine fun hI' ↦ hImax ⟨⟨hI, hIinj, hIE⟩, fun B ⟨hB, hBinj, hBE⟩ (hB' : _ ⊆ _) x hxB ↦ 
        hBinj.mem_of_mem_image hB' hxB ?_⟩
      rw [hI'.eq_of_subset_indep hB (image_subset _ hB')]
      exact mem_image_of_mem _ hxB
    simp only [mem_maximals_iff, mem_setOf_eq, and_imp] at hJmax hImax
    simp only [not_and, not_forall, exists_prop, exists_and_left, and_imp, hI, hIinj, hIE, 
      forall_true_left] at hImax 
    obtain ⟨⟨hJ, hJinj, hJE⟩, hJmax⟩ := hJmax
    
    set M' := (M ↾ f '' E) with hM'

    have hi : M'.Indep (f '' I)
    · exact hI.indep_restrict_of_subset (image_subset f hIE)

    have h1 : ¬M'.Base (f '' I)
    · sorry 
    
    have h2 : M'.Base (f '' J)
    · sorry


    obtain ⟨_, ⟨⟨e, heJ, rfl⟩, heI⟩, hi⟩ := hi.exists_insert_of_not_base h1 h2
    have heI' : e ∉ I := fun heI' ↦ heI (mem_image_of_mem f heI')
    refine' ⟨e, ⟨heJ, heI'⟩, _, _, insert_subset (hJE heJ) hIE⟩ 
    · rw [image_insert_eq]
      exact hi.of_restrict
    rw [injOn_insert heI', and_iff_right hIinj]
    assumption 


    -- have h1 : ¬M.Basis (f '' I) (f '' E ∩ M.E) 
    -- · obtain ⟨I', hI', hI'inj, hI'E, hII', hne⟩ := hImax
    --   refine fun hb ↦ hne <| hII'.antisymm <| fun x hx ↦ ?_
    --   apply hI'inj.mem_of_mem_image hII' hx
    --   rw [hb.eq_of_subset_indep hI' (image_subset _ hII') 
    --     (subset_inter (image_subset _ hI'E) hI'.subset_ground) ]
    --   exact mem_image_of_mem _ hx
      
    -- have h2 : M.Basis (f '' J) (f '' E ∩ M.E)
    -- · refine hJ.basis_of_maximal_subset (subset_inter (image_subset _ hJE) (hJ.subset_ground)) 
    --     (fun K hK hJK hKE ↦ ?_) (inter_subset_right _ _)
    --   have' := hJinj.exists_injOn_superset_image 
    --   -- rw [subset_inter_iff] at hKE
      -- have := image_subset_iff.1 hJK
      -- have := hJinj.exists_injOn_superset hJE
      
      
    -- obtain ⟨K', hJK', hKinj', rfl⟩ := hJinj.exists_injOn_superset_image hJK ?_
      
        -- (subset_inter (image_subset_iff.1 hJK) hJE)
      
      -- rw [hJmax hK hKinj' _ hJK']
      -- · rw [h_eq]
      --   intro x hxk

      --   exact hKE.trans ((inter_subset_left _ _).trans (image_subset_range _ _))
      
        
      
      -- have := hJmax (y := (f ⁻¹' K ∩ E)) 
      --   (hK.subset (subset_trans (image_subset _ (inter_subset_left _ _)) 
      --     (image_preimage_subset f _)))

      -- have hA : ∃ A, J ⊆ A ∧ A ⊆ E ∧ InjOn f A ∧ f '' A = K
      -- · set D := K \ f '' J with hD
      --   set S := f ⁻¹' D ∩ E with hS 
      --   set g : β → α := Function.invFunOn f S with hg
        
      --   have hdj : Disjoint J (g '' (f '' S))
      --   · refine' disjoint_of_subset_right (invFunOn_image_image_subset ?_ ?_) ?_ 
      --     simp_rw [hS, hD, disjoint_iff_forall_ne, mem_inter_iff, mem_preimage]
      --     rintro a haJ b ⟨⟨-,hb⟩,-⟩ rfl 
      --     exact hb (mem_image_of_mem _ haJ)

      --   refine ⟨J ∪ g '' (f '' S), subset_union_left _ _, union_subset hJE ?_, ?_, ?_⟩ 
      --   · exact (Function.invFunOn_image_image_subset f _).trans (inter_subset_right _ _)
      --   · rw [injOn_union, and_iff_right hJinj, and_iff_right (invFunOn_injOn_image_preimage _ _)]
      --     · rintro x hxJ _ ⟨_, ⟨⟨y, hy', rfl⟩, hy, rfl⟩⟩ he 
      --       have hmem := mem_image_of_mem f <| invFunOn_mem (f := f) (s := S) ⟨y, hy', rfl⟩
      --       rw [←hg, ←he, hS, hD] at hmem
      --       obtain ⟨a, ha, he⟩:= hmem
      --       rw [mem_inter_iff, mem_preimage, he] at ha
      --       exact ha.1.2 (mem_image_of_mem _ hxJ)
      --     exact hdj
        
          
          

          
          

      --     -- union_subset hJE (inter_subset_right _ _), ?_, ?_⟩ 
      --   -- · rw [injOn_union, and_iff_right hJinj]
        
   
      
      
      


    

    -- obtain ⟨_, ⟨⟨x,hx,rfl⟩,h'⟩, he'⟩ := hI.exists_insert_of_not_basis (image_subset f hIE) h1 h2
    -- refine' ⟨x, ⟨hx, fun hxI ↦ h' (mem_image_of_mem f hxI)⟩, _, _, _⟩ 
    -- · rwa [image_insert_eq]
    -- · rw [injOn_insert (fun hxI ↦ h' (mem_image_of_mem f hxI))]
    --   exact ⟨hIinj, h'⟩ 

    -- exact insert_subset (hJE hx) hIE





    -- have hB1 : M.Base (f '' J)
    -- · simp only [mem_maximals_iff, mem_setOf_eq, and_imp] at hJmax 
    --   refine hJmax.1.1.base_of_maximal (fun K hK hss ↦ ?_)
    --   have := hJmax.2 (y := (f ⁻¹' K) ∩ E) (hK.subset ?_)

    --   rw [hJmax.2 (y := (f ⁻¹' K) ∩ E)]
      
      
    

    --
    -- simp [mem_maximals_iff, iff_true_intro hI, iff_true_intro hIinj, iff_true_intro hIE] at hImax
    
  )
  ( by
    rintro X hXE I ⟨hI, hIinj, hIE⟩ hIX
    set M' := M ↾ (f '' E) with hM'
    have hI' : M'.Indep (f '' I)
    · exact restrict_indep_iff.2 ⟨hI, image_subset f hIE⟩ 
    obtain ⟨J, hJX, hIJ⟩ := hI'.subset_basis_of_subset (image_subset f hIX) (image_subset f hXE)
    obtain ⟨J, hIJ', hJX', hJinj, rfl⟩ := hIinj.exists_injOn_superset_image hIX hIJ hJX.subset    
    refine ⟨J, ⟨⟨hJX.indep.of_restrict, hJinj, hJX'.trans hXE⟩, hIJ', hJX'⟩, ?_⟩ 
    rintro B ⟨⟨hB, hBinj, hBE⟩,  hIB, hBX⟩ (hJB : J ⊆ B) b hb
    have hB' : M'.Indep (f '' B)
    · refine restrict_indep_iff.2 ⟨hB, image_subset f hBE⟩ 
    have hb' := mem_image_of_mem f hb
    rw [←hJX.eq_of_subset_indep hB' (image_subset f hJB) (image_subset f hBX)] at hb'
    exact hBinj.mem_of_mem_image hJB hb hb' )
  ( fun I h ↦ h.2.2 )



@[simp] theorem parallel_preimage_indep_iff {M : Matroid β} {E : Set α} {f : α → β} {I : Set α} : 
    (M.parallel_preimage E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by 
  sorry 

@[simp] theorem parallel_preimage_ground_eq {M : Matroid β} {E : Set α} {f : α → β} : 
    (M.parallel_preimage E f).E = E := rfl 
  
  
