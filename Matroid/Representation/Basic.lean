import Matroid.Flat
import Matroid.Representation.ForMathlib

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽] 
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional

theorem linearIndependent_subtype_congr {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M] 
  {s s' : Set M} (h_eq : s = s') : 
    LinearIndependent R ((↑) : s → M) ↔ LinearIndependent R ((↑) : s' → M) := by 
  subst h_eq; rfl 
namespace Matroid

/-- A function `φ : α → W` represents `M` over `𝔽` if independence in `M` corresponds to linear
  independence in `W` of the image. -/
def IsRep (M : Matroid α) (𝔽 : Type _) [CommSemiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] 
    (φ : α → W) := 
  ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict φ)

@[pp_dot] structure Rep (M : Matroid α) (𝔽 W : Type _) [CommSemiring 𝔽] [AddCommMonoid W] 
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
    simp only [Function.comp_apply, ne_eq] at h0  
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
      rw [Set.range_comp]
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

def matroid_of_fun (f : α → W) (E : Set α) (hf : f.support ⊆ E) 
  (hfin : Module.Finite 𝔽 (span 𝔽 (range f))) : Matroid α := 
  have hlem  : ∀ {I}, LinearIndependent 𝔽 (I.restrict f) → Set.Finite I := by
    intro I hI 
    obtain ⟨i, hi⟩ := LinearMap.exists_leftInverse_of_injective 
      (Submodule.subtype (span 𝔽 (range f))) (by simp)
     
    have _ := (hI.map (f := i) ?_).finite_index
    · exact I.toFinite
    simp only [range_restrict, disjoint_def', LinearMap.mem_ker]
    rintro x hx y hy rfl 
    have h := LinearMap.congr_fun hi ⟨x, span_mono (image_subset_range _ _) hx⟩ 
    simp only [LinearMap.coe_comp, coeSubtype, comp_apply, hy, LinearMap.id_coe, id_eq] at h
    simpa using (congr_arg Subtype.val h).symm 
  matroid_of_indep_of_bdd_augment 
  E
  ( fun I ↦ LinearIndependent 𝔽 (I.restrict f) ) 
  ( linearIndependent_empty_type )
  ( fun I J hI hJI ↦ by convert hI.comp _ (inclusion_injective hJI) )
  ( by 
    intro I J hI hJ hIJ
    have hIinj : InjOn f I := by rw [injOn_iff_injective]; exact hI.injective

    have := (hlem hI).fintype 
    have := (hlem hJ).fintype 

    have h : ¬ (f '' J ⊆ span 𝔽 (f '' I))
    · refine fun hss ↦ hIJ.not_le ?_
      rw [←range_restrict, ←range_restrict] at hss
      
      have : FiniteDimensional 𝔽 {x // x ∈ span 𝔽 (Set.range (I.restrict f))}
      · apply FiniteDimensional.span_of_finite
        rw [range_restrict]
        apply I.toFinite.image
        
      have hle := span_mono hss (R := 𝔽)
      simp only [span_coe_eq_restrictScalars, restrictScalars_self] at hle  
      have hrank := finrank_le_finrank_of_le hle 
      rw [←I.toFinite.cast_ncard_eq, ←J.toFinite.cast_ncard_eq, Nat.cast_le]
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
    refine ⟨FiniteDimensional.finrank 𝔽 (span 𝔽 (range f)), fun I (hI : LinearIndependent _ _) ↦ ?_⟩
    have _ := (hlem hI).fintype
    rw [←(hlem hI).cast_ncard_eq, Nat.cast_le, ←Nat.card_coe_set_eq, Nat.card_eq_fintype_card, 
      ←finrank_span_eq_card hI, range_restrict]
    exact finrank_le_finrank_of_le (span_mono <| image_subset_range _ _) )
  ( by 
    refine fun I hI ↦ subset_trans (fun e heI ↦ ?_) hf
    exact hI.ne_zero ⟨_, heI⟩ )


-- Each function from a type to a module defines a matroid on a finite superset of its support -
def matroid_of_fun_of_finite (f : α → W) (E : Set α) (hf : f.support ⊆ E) (hfin : E.Finite) : 
  Matroid α := matroid_of_fun (𝔽 := 𝔽) f E hf (by 
    rw [←Submodule.span_diff_zero]
    
    have _ := (FiniteDimensional.span_of_finite 𝔽 (hfin.image f))
    apply Submodule.finiteDimensional_of_le 
    -- have : Module.Finite 𝔽 (span 𝔽 (f '' E))
    
    )
  

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
  
theorem Rep.subset_span_of_basis' (φ : M.Rep 𝔽 W) (h : M.Basis' I X) : 
    φ '' X ⊆ span 𝔽 (φ '' I) := by 
  rintro _ ⟨e, he, rfl⟩
  obtain (heI | heI) := em (φ e ∈ φ '' I)
  · exact subset_span heI
  obtain (heI' | heI') := em (e ∈ I)
  · exact (heI (mem_image_of_mem _ heI')).elim 
  have hi := h.insert_not_indep ⟨he, heI'⟩ 
  rw [φ.indep_iff_image, injOn_insert heI', and_iff_left heI, 
    and_iff_left (φ.injOn_of_indep h.indep), linearIndependent_subtype_congr image_insert_eq, 
    (linearIndependent_insert heI), not_and,  not_not] at hi 
  exact hi <| φ.linear_indep_image h.indep 

theorem Rep.subset_span_of_basis (φ : M.Rep 𝔽 W) (h : M.Basis I X) : φ '' X ⊆ span 𝔽 (φ '' I) :=
  φ.subset_span_of_basis' h.basis'

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

@[simp] theorem Rep.span_eq_span_cl (φ : M.Rep 𝔽 W) (X : Set α) : 
    span 𝔽 (φ '' M.cl X) = span 𝔽 (φ '' X) := by 
  rw [φ.span_eq_span_inter_ground X, cl_eq_cl_inter_ground, le_antisymm_iff, 
    and_iff_left (span_mono (image_subset _ (M.subset_cl _)))]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E) 
  rw [←hI.cl_eq_cl]
  exact (span_mono <| φ.subset_span_of_basis hI.indep.basis_cl).trans <| 
    span_le.2 (span_mono (image_subset _ hI.subset))

theorem Rep.span_eq_span_of_basis' (φ : M.Rep 𝔽 W) (h : M.Basis' I X) : 
    span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
  le_antisymm (span_mono (image_subset _ h.subset)) (span_le.2 (φ.subset_span_of_basis' h)) 

theorem Rep.span_eq_span_of_basis (φ : M.Rep 𝔽 W) (h : M.Basis I X) : 
    span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
  φ.span_eq_span_of_basis' h.basis' 

theorem Rep.span_le_span_of_cl_subset_cl (φ : M.Rep 𝔽 W) (h : M.cl X ⊆ M.cl Y) :
    span 𝔽 (φ '' X) ≤ span 𝔽 (φ '' Y) := by 
  obtain ⟨I, hI⟩ := M.exists_basis' X 
  refine span_le.2 <| (φ.subset_span_of_basis' hI).trans <| span_le.2 ?_
  rw [←φ.span_eq_span_cl]
  exact (image_subset _ (hI.basis_cl_right.subset.trans h)).trans subset_span 
  
theorem Rep.subset_span_iff (φ : M.Rep 𝔽 W) (hX : X ⊆ M.E := by aesop_mat) : 
    φ '' X ⊆ span 𝔽 (φ '' Y) ↔ X ⊆ M.cl Y := by 
  -- obtain ⟨I, hI⟩ := M.exists_basis' X

  refine ⟨fun h e heX ↦ ?_, fun h ↦ ?_⟩ 
  · obtain ⟨I, hI⟩ := M.exists_basis' Y 
    -- have hsp := h (mem_image_of_mem _ heX)
    rw [←φ.span_eq_span_of_basis' hI] at h
    rw [←hI.cl_eq_cl, hI.indep.mem_cl_iff', and_iff_right (hX heX)]
    
    specialize h (mem_image_of_mem _ heX)
    refine fun hi ↦ by_contra fun heI ↦ ?_
    have hind := φ.linear_indep_image hi 
    rw [linearIndependent_subtype_congr image_insert_eq, linearIndependent_insert] at hind
    · exact (hind.2 h).elim  
    refine fun heI' ↦ heI ?_ 
    rwa [←(φ.injOn_of_indep hi).mem_image_iff (subset_insert _ _) (mem_insert _ _)]
  rw [←φ.span_eq_span_cl]
  exact (image_subset φ h).trans subset_span
    

-- Ugly proof in the second part 
theorem Rep.cl_eq (φ : M.Rep 𝔽 W) (X : Set α) : M.cl X = M.E ∩ φ ⁻¹' (span 𝔽 (φ '' X)) := by 
  obtain ⟨I, hI⟩ := M.exists_basis' (X)
  rw [←hI.cl_eq_cl, subset_antisymm_iff, subset_inter_iff, and_iff_right (cl_subset_ground _ _), 
    ←image_subset_iff, and_iff_left]
  · exact (φ.subset_span_of_basis hI.indep.basis_cl).trans (span_mono (image_subset _ hI.subset))
  rintro x ⟨hxE, hx⟩  
  rw [mem_preimage] at hx
  
  rw [hI.indep.mem_cl_iff, or_iff_not_imp_right, dep_iff, 
    and_iff_left <| insert_subset hxE hI.indep.subset_ground]
  refine fun hxI hi ↦ ?_
  apply (φ.linear_indep hi).not_mem_span_image (s := Subtype.val ⁻¹' I) 
    (x := ⟨x, mem_insert _ _⟩) (by simpa)
  simp only [restrict_apply] 

  have hsp := span_mono (φ.subset_span_of_basis' hI) hx
  
  rw [span_coe_eq_restrictScalars, restrictScalars_self] at hsp 
  convert hsp 
  ext
  aesop

theorem Rep.span_eq_span_of_cl_eq_cl (φ : M.Rep 𝔽 W) (h : M.cl X = M.cl Y) : 
    span 𝔽 (φ '' X) = span 𝔽 (φ '' Y) := by 
  rw [span_eq_span_inter_ground, span_eq_span_inter_ground _ Y]
  simp_rw [le_antisymm_iff, span_le, φ.subset_span_iff (inter_subset_right _ _), 
    ←cl_eq_cl_inter_ground]
  constructor
  · rw [←h, cl_eq_cl_inter_ground]; exact subset_cl _ _
  rw [h, cl_eq_cl_inter_ground]
  exact subset_cl _ _

-- theorem Rep.r_eq [FiniteRk M] (φ : M.Rep 𝔽 W) (X : Set α) : 
--     M.r X = finrank 𝔽 (span 𝔽 (φ '' X)) := by
--   obtain ⟨I, hI⟩ := M.exists_basis' X 
--   rw [←hI.r]

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

-- Subspace representations 

def Rep.subspaceRep (φ : M.Rep 𝔽 W) : Submodule 𝔽 (α → 𝔽) := Submodule.ofFun 𝔽 φ

/-- The 'row space' corresponding to the representation `φ` -/
def Rep.projSet (φ : M.Rep 𝔽 W) (X : Set α) : Submodule 𝔽 (X → 𝔽) := ofFun 𝔽 (φ ∘ ((↑) : X → α))
  
theorem Rep.indep_iff_projSet_eq_top (φ : M.Rep 𝔽 W) : M.Indep I ↔ φ.projSet I = ⊤ := by 
  rw [φ.indep_iff, Rep.projSet, ofFun_eq_top_iff]; rfl  
  
-- example (h : Module.Finite 𝔽 (α → 𝔽)) : _root_.Finite α := by 
  
-- def matroid' (U : Submodule 𝔽 (α → 𝔽)) : Matroid α := matroid_of_indep 
--     univ 
--     ( fun I ↦ Submodule.map (LinearMap.fun_subtype 𝔽 I) U = ⊤ )
--     ( by simp )
--     ( by 
--       refine fun I J (hJ : _ = ⊤) hIJ ↦ eq_top_iff'.2 fun (x : I → 𝔽) ↦ mem_map.2 ?_  
--       simp_rw [eq_top_iff', mem_map] at hJ
--       obtain ⟨y, hy, hy'⟩ := hJ <| LinearMap.extend_subset 𝔽 hIJ x
--       exact ⟨y, hy, funext fun i ↦ by simpa using congr_fun hy' (inclusion hIJ i)⟩ )
--     ( by 
--       intro I B hI hInotmax hBmax
--       simp only [mem_maximals_setOf_iff, not_and, not_forall, exists_prop, exists_and_left, 
--         iff_true_intro hI, true_imp_iff] at hInotmax hBmax
--       by_contra h
--       push_neg at h

      
      
--       )
--     sorry 
--     ( fun _ _ ↦ subset_univ _ ) 


theorem matroid_of_subspace_aux {U : Submodule 𝔽 (α → 𝔽)} {I : Set α} [FiniteDimensional 𝔽 U]
  (hI : Submodule.map (LinearMap.fun_subtype 𝔽 I) U = ⊤) : 
  Set.Finite I ∧ finrank 𝔽 (Submodule.map (LinearMap.fun_subtype 𝔽 I) U) = I.ncard := sorry 

theorem matroid_of_subspace_aux' {U : Submodule 𝔽 (α → 𝔽)} {I : Set α}
    (hI : Submodule.map (LinearMap.fun_subtype 𝔽 I) U = ⊤) 
    (b : Basis ): 
  ∃ (f : I → U) , LinearIndependent 𝔽 f ∧ 



-- def matroid_of_subspace (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : Matroid α := 
--   matroid_of_indep_of_bdd_augment univ 
--   ( fun I ↦ Submodule.map (LinearMap.fun_subtype 𝔽 I) U = ⊤) 
--   ( by simp )
--   ( by 
--     refine fun I J (hJ : _ = ⊤) hIJ ↦ eq_top_iff'.2 fun (x : I → 𝔽) ↦ mem_map.2 ?_  
--     simp_rw [eq_top_iff', mem_map] at hJ
--     obtain ⟨y, hy, hy'⟩ := hJ <| LinearMap.extend_subset 𝔽 hIJ x
--     exact ⟨y, hy, funext fun i ↦ by simpa using congr_fun hy' (inclusion hIJ i)⟩ )
--   ( by 
--       intro I J hI hJ hcard 
      
--       obtain ⟨hIfin, hI'⟩ := matroid_of_subspace_aux hI 
--       obtain ⟨hJfin, hJ'⟩ := matroid_of_subspace_aux hJ 
--       have _ := hIfin.fintype 
--       have _ := hJfin.fintype 
--       set e : (⊤ : Submodule 𝔽 (I → 𝔽)) ≃ₗ[𝔽] (I → 𝔽) := by exact?
--       set b : _root_.Basis I 𝔽 (I → 𝔽) := by exact?
--       -- set b' : _root_.Basis I 𝔽 (⊤ : Submodule 𝔽 (I → 𝔽)):= 
--       set b' :=  (Pi.basisFun 𝔽 I).map (LinearEquiv.ofTop ⊤ rfl).symm with hb' 
--       have := b'.linearIndependent

      
--       -- have := Basis.exists_basis ()
--       -- apply_fun (finrank 𝔽) at hI hJ 
--       -- simp at hI 
--       sorry )
--   ( by 
--     refine ⟨finrank 𝔽 U, fun I (hI : _ = ⊤) ↦ 
--       encard_le_coe_iff_finite_ncard_le.2 (matroid_of_subspace_aux hI)⟩ 
     
--     -- obtain ⟨ hfin, hcard⟩ := 
--     -- 
--     -- have : Fintype I
--     -- · have hfin := Module.Finite.map U (LinearMap.fun_subtype 𝔽 I)
--     --   rw [hI] at hfin
      
--     --   sorry 
--     -- rw [encard_le_coe_iff_finite_ncard_le, and_iff_right <| toFinite I, ←Nat.card_coe_set_eq, 
--     --   Nat.card_eq_fintype_card]
    
--     -- have hle := Submodule.finrank_map_le (LinearMap.fun_subtype 𝔽 I) U 
--     -- rw [hI] at hle
--     -- convert hle
--     -- simp 
     
--     )
--   ( fun _ _ ↦ subset_univ _ ) 
  
  