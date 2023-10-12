import Matroid.Flat
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Matrix.Rank

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X : Set α} {M : Matroid α} [Field 𝔽] 
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional


theorem linearIndependent_subtype_congr {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M] 
  {s s' : Set M} (h_eq : s = s') : 
    LinearIndependent R ((↑) : s → M) ↔ LinearIndependent R ((↑) : s' → M) := by 
  subst h_eq; rfl 

namespace Matroid

/-- A function `φ : α → W` represents `M` over `𝔽` if independence in `M` corresponds to linear
  independence in `W` of the image. -/
def IsRep (M : Matroid α) (𝔽 : Type _) [Field 𝔽] [AddCommMonoid W] [Module 𝔽 W] (φ : α → W) := 
  ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict φ)

@[pp_dot] structure Rep (M : Matroid α) (𝔽 W : Type _) [Field 𝔽] [AddCommMonoid W] 
  [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (valid' : M.IsRep 𝔽 to_fun)
 
instance : FunLike (M.Rep 𝔽 W) α (fun _ ↦ W) where
  coe φ := φ.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp 
  
instance coeFun : CoeFun (M.Rep 𝔽 W) fun _ ↦ (α → W) :=
  ⟨FunLike.coe⟩

@[simp] theorem Rep.to_fun_eq_coe (φ : M.Rep 𝔽 W) : φ.to_fun = (φ : α → W) := rfl

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

theorem Rep.indep_iff_image_of_inj (φ : M.Rep 𝔽 W) (h_inj : InjOn φ I) :
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : φ '' I → W) := by 
  refine ⟨φ.linear_indep_image, fun hi ↦ ?_⟩ 
  rw [φ.indep_iff, restrict_eq]
  exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

theorem Rep.indep_iff_image (φ : M.Rep 𝔽 W) : 
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : φ '' I → W) ∧ InjOn φ I :=
  ⟨fun h ↦ ⟨φ.linear_indep_image h, φ.injOn_of_indep h⟩, 
    fun h ↦ (φ.indep_iff_image_of_inj h.2).2 h.1⟩    
 
theorem Rep.eq_zero_iff_not_indep {φ : M.Rep 𝔽 W} : φ e = 0 ↔ ¬ M.Indep {e} := by
  simp [φ.indep_iff, linearIndependent_unique_iff, -indep_singleton]
  
theorem Rep.eq_zero_of_not_mem_ground (φ : M.Rep 𝔽 W) (he : e ∉ M.E) : φ e = 0 := by 
  rw [φ.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

theorem Rep.support_subset_ground (φ : M.Rep 𝔽 W) : support φ ⊆ M.E := 
  fun _ he ↦ by_contra <| fun h' ↦ he (φ.eq_zero_of_not_mem_ground h')

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

def Rep.map (φ : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') 
    (h_inj : Disjoint (span 𝔽 (range φ)) (LinearMap.ker ψ)) : M.Rep 𝔽 W' where 
  to_fun := ψ ∘ φ
  valid' := fun I ↦ by 
    rw [φ.indep_iff, restrict_eq, restrict_eq, comp.assoc] 
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply h.map (h_inj.mono_left (span_mono _))
      rw [range_comp]
      exact image_subset_range _ _
    exact LinearIndependent.of_comp _ h

/-- Compose a representation with a linear injection. -/
def Rep.map' (φ : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) := φ.map ψ (by simp [hψ])

/-- Compose a representation with a linear equivalence. -/
def Rep.map_equiv (φ : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') : M.Rep 𝔽 W' := φ.map' ψ ψ.ker

@[simp] theorem Rep.map'_apply (φ : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) (e : α) : 
    (φ.map' ψ hψ) e = ψ (φ e) := rfl 

@[simp] theorem Rep.map_equiv_apply (φ : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') (e : α) : 
    (φ.map_equiv ψ) e = ψ (φ e) := rfl 

def Rep.subtype_ofEq {W₁ W₂ : Submodule 𝔽 W} (φ : M.Rep 𝔽 W₁) (h : W₁ = W₂) : M.Rep 𝔽 W₂ := 
  φ.map_equiv <| LinearEquiv.ofEq _ _ h

-- @[simp] theorem Rep.subtype_ofEq_apply {W₁ W₂ : Submodule 𝔽 W} (φ : M.Rep 𝔽 W₁) (h : W₁ = W₂) 
--   (e : α) : (φ.subtype_ofEq h) e = ⟨φ e, h ▸ (φ e).prop⟩ := rfl 

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
  valid' := by simp [IsRep]

theorem Rep.range_subset_span_base (φ : M.Rep 𝔽 W) (hB : M.Base B) : range φ ⊆ span 𝔽 (φ '' B) := by 
  rintro _ ⟨e, he ,rfl⟩ 
  
  obtain (heB | heB) := em (e ∈ B)
  · exact subset_span (mem_image_of_mem _ heB)
  by_contra h'
  have hind := LinearIndependent.insert ?_ h'
  
  · rw [←linearIndependent_subtype_congr image_insert_eq, ←φ.indep_iff_image_of_inj] at hind
    · exact heB (hB.mem_of_insert_indep hind) 
    rw [injOn_insert heB, and_iff_right (φ.injOn_of_indep hB.indep)]
    exact fun h'' ↦ h' <| mem_of_mem_of_subset h'' subset_span
  exact φ.linear_indep_image hB.indep
  
theorem Rep.span_range_eq_span_base (φ : M.Rep 𝔽 W) (hB : M.Base B) : 
     span 𝔽 (range (restrict B φ)) = span 𝔽 (range φ) := by 
  rw [range_restrict, eq_comm]
  exact span_eq_of_le _ (φ.range_subset_span_base hB) (span_mono (image_subset_range _ _))

/-- A representation is `FullRank` if its vectors span the space -/
def Rep.FullRank (φ : M.Rep 𝔽 W) : Prop := ⊤ ≤ span 𝔽 (range φ)

/-- Restrict a representation to the submodule spanned by its image -/
def Rep.restrict_span (φ : M.Rep 𝔽 W) : M.Rep 𝔽 (span 𝔽 (range φ)) where
  to_fun := inclusion subset_span ∘ rangeFactorization φ
  valid' := (by 
    intro I
    rw [φ.indep_iff]
    refine ⟨fun h ↦ LinearIndependent.of_comp (Submodule.subtype _) (by rwa [coeSubtype]), 
      fun h ↦ h.map' (Submodule.subtype _) (ker_subtype _)⟩ )

theorem Rep.FullRank.span_range {φ : M.Rep 𝔽 W} (h : φ.FullRank) : span 𝔽 (range φ) = ⊤ := by 
  rwa [eq_top_iff]

theorem Rep.fullRank_iff {φ : M.Rep 𝔽 W} : φ.FullRank ↔ span 𝔽 (range φ) = ⊤ := by
  rw [FullRank, eq_top_iff]

@[simp] theorem Rep.restrict_span_apply (φ : M.Rep 𝔽 W) (e : α) : 
  φ.restrict_span e = inclusion subset_span (rangeFactorization φ e) := rfl 

theorem Rep.restrict_span_fullRank (φ : M.Rep 𝔽 W) : 
    φ.restrict_span.FullRank := by
  change _ ≤ span 𝔽 (range (inclusion subset_span ∘ _))
  rw [range_comp, surjective_onto_range.range_eq, image_univ, range_inclusion]
  change _ ≤ span 𝔽 ((Submodule.subtype (span 𝔽 (range ↑φ))) ⁻¹' _) 
  simp

/-- A base of `M` gives a linear basis in a full-rank representation -/
noncomputable def Rep.FullRank.basis_of_base {φ : M.Rep 𝔽 W} (h : φ.FullRank) (hB : M.Base B) : 
    _root_.Basis B 𝔽 W := 
  Basis.mk (φ.linear_indep hB.indep) 
    ( by rw [←h.span_range, φ.span_range_eq_span_base hB] )

theorem Rep.FullRank.map_equiv {φ : M.Rep 𝔽 W} (h : φ.FullRank) (ψ : W ≃ₗ[𝔽] W') : 
    (φ.map_equiv ψ).FullRank := by 
  rw [Rep.fullRank_iff, map_equiv, map', map, ←Rep.to_fun_eq_coe]
  simp [LinearEquiv.coe_coe, range_comp, h.span_range]
  
/-- A base of `M` gives a linear basis for the span of the range of a representation -/
noncomputable def Rep.basis_of_base (φ : M.Rep 𝔽 W) (hB : M.Base B) : 
    _root_.Basis B 𝔽 (span 𝔽 (range φ)) := 
  (Basis.span (φ.linear_indep hB.indep)).map <| LinearEquiv.ofEq _ _ (φ.span_range_eq_span_base hB)

/-- The natural representation with rows indexed by a base -/
noncomputable def Rep.to_standard_rep (φ : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B →₀ 𝔽) :=
  φ.restrict_span.map_equiv (φ.restrict_span_fullRank.basis_of_base hB).repr 

/-- A matroid is representable if it has a representation -/  
def Representable (M : Matroid α) (𝔽 : Type _) [Field 𝔽] : Prop := 
    ∃ (X : Set α), _root_.Nonempty (M.Rep 𝔽 (X →₀ 𝔽))

theorem Rep.representable (φ : M.Rep 𝔽 W) : M.Representable 𝔽 :=
  have ⟨_, hB⟩ := M.exists_base
  ⟨_, ⟨φ.to_standard_rep hB⟩⟩ 

theorem Rep.standard_rep_eq_one (φ : M.Rep 𝔽 W) (hB : M.Base B) (e : B) : 
    (φ.to_standard_rep hB) e e = 1 := by 
  simp only [Rep.to_standard_rep, Rep.FullRank.basis_of_base, Rep.map_equiv_apply, 
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  simp
  
theorem Rep.standard_rep_eq_zero (φ : M.Rep 𝔽 W) (hB : M.Base B) (e f : B) (hef : e ≠ f) : 
    (φ.to_standard_rep hB) e f = 0 := by 
  simp [Rep.to_standard_rep, Rep.FullRank.basis_of_base, Rep.map_equiv_apply, 
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  exact Finsupp.single_eq_of_ne hef

theorem Rep.standard_rep_fullRank (φ : M.Rep 𝔽 W) (hB : M.Base B) : 
    (φ.to_standard_rep hB).FullRank := 
  φ.restrict_span_fullRank.map_equiv _ 
  
/-- The natural representation with rows indexed by a base -/
noncomputable def Rep.to_standard_rep' [FiniteRk M] (φ : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B → 𝔽) :=
  have := hB.finite.to_subtype
  (φ.to_standard_rep hB).map_equiv (Finsupp.linearEquivFunOnFinite 𝔽 𝔽 B)
  
theorem Rep.standard_rep_eq_one' [FiniteRk M] (φ : M.Rep 𝔽 W) (hB : M.Base B) (e : B) : 
    (φ.to_standard_rep' hB) e e = 1 := by 
  classical 
  have := hB.finite.to_subtype
  simp [to_standard_rep', φ.standard_rep_eq_one hB]
  
theorem Rep.standard_rep_eq_zero' [FiniteRk M] (φ : M.Rep 𝔽 W) (hB : M.Base B) (e f : B) 
  (hef : e ≠ f) : (φ.to_standard_rep' hB) e f = 0 := by 
  classical
  have := hB.finite.to_subtype 
  simp [to_standard_rep', φ.standard_rep_eq_zero hB _ _ hef]

theorem Representable.exists_standard_rep (h : Representable M 𝔽) (hB : M.Base B) : 
    ∃ φ : M.Rep 𝔽 (B →₀ 𝔽), φ.FullRank  :=
  let ⟨_, ⟨φ⟩⟩ := h; ⟨φ.to_standard_rep hB, φ.standard_rep_fullRank hB⟩
  
theorem Representable.exists_standard_rep' [FiniteRk M] (h : Representable M 𝔽) (hB : M.Base B) : 
    ∃ φ : M.Rep 𝔽 (B → 𝔽), φ.FullRank := 
  let ⟨_, ⟨φ⟩⟩ := h; ⟨φ.to_standard_rep' hB, (φ.standard_rep_fullRank hB).map_equiv _⟩ 
  
theorem Representable.exists_fin_rep [FiniteRk M] (h : Representable M 𝔽) : 
    ∃ φ : M.Rep 𝔽 (Fin M.rk → 𝔽), φ.FullRank := by
  obtain ⟨B, hB⟩ := M.exists_base
  have _ := hB.finite.fintype
  obtain ⟨φ, hφ⟩ := h.exists_standard_rep' hB 
  have hcard := hB.ncard
  rw [←Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hcard
  use φ.map_equiv <| LinearEquiv.piCongrLeft' 𝔽 (fun _ ↦ 𝔽) (Fintype.equivFinOfCardEq hcard) 
  exact hφ.map_equiv _
  
theorem Rep.subset_span_of_basis (φ : M.Rep 𝔽 W) (h : M.Basis I X) : φ '' X ⊆ span 𝔽 (φ '' I) := by 
  rintro _ ⟨e, he, rfl⟩
  obtain (heI | heI) := em (φ e ∈ φ '' I)
  · exact subset_span heI
  obtain (heI' | heI') := em (e ∈ I)
  · exact (heI (mem_image_of_mem _ heI')).elim 
  have hi := (h.insert_dep ⟨he, heI'⟩).not_indep 
  rw [φ.indep_iff_image, injOn_insert heI', and_iff_left heI, 
    and_iff_left (φ.injOn_of_indep h.indep), linearIndependent_subtype_congr image_insert_eq, 
    (linearIndependent_insert heI), not_and,  not_not] at hi 
  exact hi <| φ.linear_indep_image h.indep 

theorem Rep.span_eq_span_inter_ground (φ : M.Rep 𝔽 W) (X : Set α) : 
    span 𝔽 (φ '' X) = span 𝔽 (φ '' (X ∩ M.E)) := by 
  refine le_antisymm ?_ (span_mono (image_subset φ <| inter_subset_left _ _))
  rw [←span_insert_zero (s := φ '' (X ∩ M.E)), ←inter_union_diff X M.E, image_union, 
    inter_union_diff]
  apply span_mono (union_subset (subset_insert _ _) _)
  rintro _ ⟨e, he, rfl⟩ 
  left 
  rw [←nmem_support]
  exact not_mem_subset φ.support_subset_ground he.2

theorem Rep.cl_eq (φ : M.Rep 𝔽 W) (X : Set α) : M.cl X = M.E ∩ φ ⁻¹' (span 𝔽 (φ '' X)) := by 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [cl_eq_cl_inter_ground, ←hI.cl_eq_cl, φ.span_eq_span_inter_ground, 
    subset_antisymm_iff, subset_inter_iff, and_iff_right (cl_subset_ground _ _), 
    ←image_subset_iff, and_iff_left]
  · exact (φ.subset_span_of_basis hI.indep.basis_cl).trans (span_mono (image_subset _ hI.subset))
  rintro x ⟨hxE, hx⟩  
  rw [mem_preimage] at hx
  
  
  have := φ.subset_span_of_basis hI hx  
  -- refine subset_antisymm (subset_inter (cl_subset_ground _ _) ?_) ?_ 
  -- · rw [←image_subset_iff]

  -- · 
  --   refine subset_trans ?_ subset_span


  --   (fun x hx ↦ ?_)) ?_ 
  -- · rw [mem_preimage]
  --   have := φ.subset_span_of_basis hI

     
  -- · have := φ.subset_span_of_basis hI

  -- have := hI.indep.mem_cl_iff_of_not_mem

structure MatrixRep (M : Matroid α) (𝔽 R : Type _) [Field 𝔽] where 
  (to_matrix : Matrix R M.E 𝔽)
  (as_rep : M.Rep 𝔽 (Matrix R Unit 𝔽))
  (compatible : ∀ e : M.E, as_rep e = Matrix.of (fun x _ ↦ to_matrix x e) )

instance {R : Type _} : Coe (M.MatrixRep 𝔽 R) (Matrix R M.E 𝔽) := ⟨MatrixRep.to_matrix⟩ 

noncomputable def Rep.to_matrixRep (φ : M.Rep 𝔽 (R → 𝔽)) : MatrixRep M 𝔽 R where 
  to_matrix := Matrix.of (fun e x ↦ φ ((x : M.E) : α) e)
  as_rep := φ.map_equiv (Matrix.col_linearEquiv _ _)
  compatible := fun _ ↦ funext fun _ ↦ funext fun _ ↦ by simp 

noncomputable def Rep.to_matrixRep_of_base [FiniteRk M] (φ : M.Rep 𝔽 W) (hB : M.Base B) : 
    MatrixRep M 𝔽 B := 
  (φ.to_standard_rep' hB).to_matrixRep 
  
theorem MatrixRep.representable (A : M.MatrixRep 𝔽 R) : M.Representable 𝔽 := A.as_rep.representable      
    
noncomputable def Representable.fin_matrixRep [FiniteRk M] (hM : M.Representable 𝔽) : 
    M.MatrixRep 𝔽 (Fin M.rk) := 
  (Classical.choose hM.exists_fin_rep).to_matrixRep

-- noncomputable instance [Finite M] (X : Set M.E) : Fintype X := by 
--   have := M.ground_finite.fintype
--   exact Fintype.ofFinite ↑X

-- instance [Fintype α] (X : Set α) : Fintype X := by
--   

  


-- theorem MatrixRep.r_eq [Finite M] (A : MatrixRep M 𝔽 R) (X : Set α) [Fintype X] (hX : X ⊆ M.E) : 
--     M.r X = (Matrix.submatrix (A : Matrix R M.E 𝔽) id (inclusion hX)).rank (R := 𝔽) := by 
--   rw [M.r_def]
  -- sorry 

