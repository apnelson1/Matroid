import Matroid.Flat
import Mathlib.LinearAlgebra.FiniteDimensional

variable {α β W W' 𝔽 : Type _} {e f x : α} {I B X : Set α} {M : Matroid α} [Field 𝔽] 
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule

namespace Matroid

structure Rep (M : Matroid α) (𝔽 W : Type _) [Field 𝔽] [AddCommMonoid W] [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (valid' : ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict to_fun))
 
instance : FunLike (M.Rep 𝔽 W) α (fun _ ↦ W) where
  coe φ := φ.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp 
  
instance coeFun : CoeFun (M.Rep 𝔽 W) fun _ ↦ (α → W) :=
  ⟨FunLike.coe⟩

@[simp] theorem Rep.to_fun_eq_coe (φ : M.Rep 𝔽 W) : φ.to_fun = (φ : α → W) := rfl

theorem Rep.eq_zero_iff_not_indep {φ : M.Rep 𝔽 W} : φ e = 0 ↔ ¬ M.Indep {e} := by
  simp [φ.valid',linearIndependent_unique_iff, -indep_singleton]
  
theorem Rep.eq_zero_of_not_mem_ground (φ : M.Rep 𝔽 W) (he : e ∉ M.E) : φ e = 0 := by 
  rw [φ.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

theorem Rep.support_subset_ground (φ : M.Rep 𝔽 W) : support φ ⊆ M.E := 
  fun _ he ↦ by_contra <| fun h' ↦ he (φ.eq_zero_of_not_mem_ground h')

theorem Rep.indep_iff (φ : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (I.restrict φ) := 
  φ.valid' I

theorem Rep.linear_indep (φ : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (I.restrict φ) := 
  φ.indep_iff.1 hI 

theorem Rep.injOn_of_indep (φ : M.Rep 𝔽 W) (hI : M.Indep I) : InjOn φ I :=
  injOn_iff_injective.2 ((φ.linear_indep hI).injective)
  
theorem Rep.linear_indep_image (φ : M.Rep 𝔽 W) (hI : M.Indep I) : 
    LinearIndependent 𝔽 ((↑) : φ '' I → W) := by
  rw [←linearIndependent_image (φ.injOn_of_indep hI)]
  exact φ.linear_indep hI 

theorem Rep.indep_iff_image (φ : M.Rep 𝔽 W) (h_inj : InjOn φ I) :
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : φ '' I → W) := by 
  refine ⟨φ.linear_indep_image, fun hi ↦ ?_⟩ 
  rw [φ.indep_iff, restrict_eq]
  exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

/-- A function with support contained in `M.E` that gives the correct independent sets 
  within the ground set gives a representation -/
def rep_of_ground (f : α → W) (h_support : support f ⊆ M.E) 
    (hf : ∀ {I}, I ⊆ M.E → (M.Indep I ↔ LinearIndependent 𝔽 (I.restrict f))) : M.Rep 𝔽 W where
  to_fun := f
  valid' := ( by 
    intro I
    obtain (hI | hI) := em (I ⊆ M.E)
    · rw [hf hI]
    rw [←not_iff_not, iff_true_left (fun hi ↦ hI hi.subset_ground)]
    intro h_ind
    obtain ⟨e, heI, heE⟩ := not_subset.1 hI
    have h0 := h_ind.ne_zero ⟨e, heI⟩ 
    simp only [comp_apply, ne_eq] at h0  
    apply not_mem_subset h_support heE
    exact h0 )

@[simp] theorem rep_of_ground_coe_eq (f : α → W) (h_support : support f ⊆ M.E) 
  (hf : ∀ {I}, I ⊆ M.E → (M.Indep I ↔ LinearIndependent 𝔽 (f ∘ ((↑) : I → α)))) : 
  (rep_of_ground f h_support hf : α → W) = f := rfl 

/-- Compose a representation with a linear injection. -/
def Rep.map (φ : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) : M.Rep 𝔽 W' where
  to_fun := ψ ∘ φ  
  valid' := fun _ ↦ by 
    rw [φ.indep_iff, restrict_eq, restrict_eq, comp.assoc, ψ.linearIndependent_iff hψ]
  
@[simp] theorem Rep.map_apply (φ : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) (e : α) : 
    (φ.map ψ hψ) e = ψ (φ e) := rfl 

/-- Each function from a type to a module defines a matroid on a finite superset of its support -/
def matroid_of_fun (f : α → W) (E : Set α) (hf : f.support ⊆ E) (hfin : E.Finite) : Matroid α := 
  matroid_of_indep_of_finite 
  hfin 
  ( fun I ↦ LinearIndependent 𝔽 (I.restrict f) ) 
  ( linearIndependent_empty_type )
  ( fun I J hI hJI ↦ by convert hI.comp _ (inclusion_injective hJI) )
 
  ( by 
    intro I J hI hJ hIJ
    have hIinj : InjOn f I := by rw [injOn_iff_injective]; exact hI.injective

    have : Fintype I
    · refine Finite.fintype (hfin.subset (subset_trans (fun _ hxI ↦ ?_) hf))
      exact hI.ne_zero ⟨_, hxI⟩
      
    have : Fintype J 
    · refine Finite.fintype (hfin.subset (subset_trans (fun _ hxJ ↦ ?_) hf))
      exact hJ.ne_zero ⟨_, hxJ⟩

    have h : ¬ (f '' J ⊆ span 𝔽 (f '' I))
    · refine fun hss ↦ hIJ.not_le ?_
      rw [←range_restrict, ←range_restrict] at hss
      
      have : FiniteDimensional 𝔽 {x // x ∈ span 𝔽 (range (restrict I f))}
      · apply FiniteDimensional.span_of_finite
        rw [range_restrict]
        apply I.toFinite.image
      
      have hle := span_mono hss (R := 𝔽)
      simp only [span_coe_eq_restrictScalars, restrictScalars_self] at hle  
      have hrank := finrank_le_finrank_of_le hle 
      rwa [finrank_span_eq_card hI, finrank_span_eq_card hJ, 
        ←Nat.card_eq_fintype_card, ←Nat.card_eq_fintype_card, 
        Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hrank
  
    obtain ⟨_, ⟨e, he, rfl⟩, heI⟩ := not_subset.1 h
    have' heI' : f e ∉ f '' I := fun h ↦ heI (Submodule.subset_span h)
    have heI'' : e ∉ I := fun h' ↦ heI' (mem_image_of_mem f h') 
    refine' ⟨e, he, heI'', _⟩
    simp only
    have hi : LinearIndependent 𝔽 ((↑) : f '' I → W)
    · rwa [← linearIndependent_image hIinj]

    have hins := (linearIndependent_insert heI').2 ⟨hi, heI⟩
    
    apply hins.comp (Equiv.setCongr image_insert_eq ∘ (imageFactorization f (insert e I)))
    simp only [EmbeddingLike.comp_injective]
    apply imageFactorization_injective
    rwa [injOn_insert heI'', and_iff_left (fun h ↦ heI (Submodule.subset_span h))] ) 
  ( by 
    refine fun I hI ↦ subset_trans (fun e heI ↦ ?_) hf
    exact hI.ne_zero ⟨_, heI⟩ )

@[simp] theorem matroid_of_fun_indep_iff (f : α → W) (E : Set α) (hf : f.support ⊆ E) 
  (hfin : E.Finite) (I : Set α) : 
    (matroid_of_fun (𝔽 := 𝔽) f E hf hfin).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) := by
  simp [matroid_of_fun, matroid_of_indep_of_finite] 

def rep_of_fun (f : α → W) (E : Set α) (hf : f.support ⊆ E) (hfin : E.Finite) :
    (matroid_of_fun (𝔽 := 𝔽) f E hf hfin).Rep 𝔽 W where 
  to_fun := f
  valid' := by simp 

theorem linearIndependent_subtype_congr {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M] 
  {s s' : Set M} (h_eq : s = s') : 
    LinearIndependent R ((↑) : s → M) ↔ LinearIndependent R ((↑) : s' → M) := by 
  subst h_eq; rfl 

theorem Rep.range_subset_span_base (φ : M.Rep 𝔽 W) (hB : M.Base B) : range φ ⊆ span 𝔽 (φ '' B) := by 
  rintro _ ⟨e, he ,rfl⟩ 
  
  obtain (heB | heB) := em (e ∈ B)
  · exact subset_span (mem_image_of_mem _ heB)
  by_contra h'
  have hind := LinearIndependent.insert ?_ h'
  
  · rw [←linearIndependent_subtype_congr image_insert_eq, ←φ.indep_iff_image] at hind
    · exact heB (hB.mem_of_insert_indep hind) 
    rw [injOn_insert heB, and_iff_right (φ.injOn_of_indep hB.indep)]
    exact fun h'' ↦ h' <| mem_of_mem_of_subset h'' subset_span
  exact φ.linear_indep_image hB.indep
  
theorem Rep.span_range_eq_span_base (φ : M.Rep 𝔽 W) (hB : M.Base B) : 
    span 𝔽 (range φ) = span 𝔽 (range (restrict B φ)) := by 
  rw [range_restrict]
  exact span_eq_of_le _ (φ.range_subset_span_base hB) (span_mono (image_subset_range _ _))

/-- A representation is `FullRank` if its vectors span the space -/
def Rep.FullRank (φ : M.Rep 𝔽 W) : Prop := span 𝔽 (range φ) = ⊤ 

-- noncomputable def BaseBasis (φ : M.Rep 𝔽 W) (hB : M.Base B) : 
--     _root_.Basis B 𝔽 (span 𝔽 (range (B.restrict φ))) :=
--   Basis.mk (linearIndependent_span (φ.linear_indep hB.indep))
--   (by 
--     rintro ⟨x, hx⟩ -


--   ) 


--   -- -- set v : B → span 𝔽 (range φ) := fun e ↦ ⟨φ e, _⟩  
--   -- have h := linearIndependent_span (φ.linear_indep hB.indep)

--   -- apply Basis.mk h
--   -- simp only [restrict_apply]
--   -- rintro ⟨x, hx⟩ -
  
  



  
  


  
  
  


def Rep.toStandardRep (φ : M.Rep 𝔽 W) (hB : M.Base B) : M.Rep 𝔽 (B → 𝔽) := by
  
  have hb1 := (Basis.span (φ.linear_indep hB.indep))
  
  -- .map 
    -- (LinearEquiv.ofEq _ _ (φ.span_range_eq_span_base hB).symm)
  set W₀ := span 𝔽 (φ '' B) with hW₀ 
  sorry 

  -- refine' φ.map (𝔽 := 𝔽) _ _
