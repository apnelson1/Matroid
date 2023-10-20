import Matroid.Flat
import Matroid.ForMathlib.Representation

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽] 
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional

namespace Matroid

/-- A function `v : α → W` represents `M` over `𝔽` if independence of `I` in `M` corresponds to 
  linear independence of `v '' I` in `W`. -/
def IsRep (M : Matroid α) (𝔽 : Type _) [CommSemiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] 
    (v : α → W) := 
  ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v)

@[pp_dot] structure Rep (M : Matroid α) (𝔽 W : Type _) [CommSemiring 𝔽] [AddCommMonoid W] 
  [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (valid' : M.IsRep 𝔽 to_fun)
 
instance : FunLike (M.Rep 𝔽 W) α (fun _ ↦ W) where
  coe v := v.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp 
  
instance coeFun : CoeFun (M.Rep 𝔽 W) fun _ ↦ (α → W) :=
  ⟨FunLike.coe⟩

@[simp] theorem Rep.to_fun_eq_coe (v : M.Rep 𝔽 W) : v.to_fun = (v : α → W) := rfl

theorem Rep.indep_iff (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v) := 
  v.valid' I

theorem Rep.linear_indep (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (I.restrict v) := 
  v.indep_iff.1 hI 

theorem Rep.injOn_of_indep (v : M.Rep 𝔽 W) (hI : M.Indep I) : InjOn v I := 
  injOn_iff_injective.2 ((v.linear_indep hI).injective)
  
theorem Rep.linear_indep_image (v : M.Rep 𝔽 W) (hI : M.Indep I) : 
    LinearIndependent 𝔽 ((↑) : v '' I → W) := by
  rw [←linearIndependent_image (v.injOn_of_indep hI)]
  exact v.linear_indep hI 

theorem Rep.indep_iff_image_of_inj (v : M.Rep 𝔽 W) (h_inj : InjOn v I) :
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : v '' I → W) := by 
  refine ⟨v.linear_indep_image, fun hi ↦ ?_⟩ 
  rw [v.indep_iff, restrict_eq]
  exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

theorem Rep.indep_iff_image (v : M.Rep 𝔽 W) : 
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : v '' I → W) ∧ InjOn v I :=
  ⟨fun h ↦ ⟨v.linear_indep_image h, v.injOn_of_indep h⟩, 
    fun h ↦ (v.indep_iff_image_of_inj h.2).2 h.1⟩    
 
theorem Rep.eq_zero_iff_not_indep {v : M.Rep 𝔽 W} : v e = 0 ↔ ¬ M.Indep {e} := by
  simp [v.indep_iff, linearIndependent_unique_iff, -indep_singleton]
  
theorem Rep.eq_zero_of_not_mem_ground (v : M.Rep 𝔽 W) (he : e ∉ M.E) : v e = 0 := by 
  rw [v.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

theorem Rep.support_subset_ground (v : M.Rep 𝔽 W) : support v ⊆ M.E := 
  fun _ he ↦ by_contra <| fun h' ↦ he (v.eq_zero_of_not_mem_ground h')

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

def Rep.map (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') 
    (h_inj : Disjoint (span 𝔽 (range v)) (LinearMap.ker ψ)) : M.Rep 𝔽 W' where 
  to_fun := ψ ∘ v
  valid' := fun I ↦ by 
    rw [v.indep_iff, restrict_eq, restrict_eq, comp.assoc] 
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply h.map (h_inj.mono_left (span_mono _))
      rw [Set.range_comp]
      exact image_subset_range _ _
    exact LinearIndependent.of_comp _ h

/-- Compose a representation with a linear injection. -/
def Rep.map' (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) := v.map ψ (by simp [hψ])

/-- Compose a representation with a linear equivalence. -/
def Rep.map_equiv (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') : M.Rep 𝔽 W' := v.map' ψ ψ.ker

@[simp] theorem Rep.map'_apply (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) (e : α) : 
    (v.map' ψ hψ) e = ψ (v e) := rfl 

@[simp] theorem Rep.map_equiv_apply (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') (e : α) : 
    (v.map_equiv ψ) e = ψ (v e) := rfl 

def Rep.subtype_ofEq {W₁ W₂ : Submodule 𝔽 W} (v : M.Rep 𝔽 W₁) (h : W₁ = W₂) : M.Rep 𝔽 W₂ := 
  v.map_equiv <| LinearEquiv.ofEq _ _ h

/-- A function from `α` to a module gives rise to a finitary matroid on `α` -/
def matroid_on_univ_of_fun (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (v : α → W) : Matroid α := 
    matroid_of_indep_of_compact univ 
    (fun I ↦ LinearIndependent 𝔽 (I.restrict v)) 
    linearIndependent_empty_type
    ( fun I J hI hJI ↦ by convert hI.comp _ (inclusion_injective hJI) )
    ( by 
      intro I J hI hIfin hJ hJfin hcard
      have hIinj : InjOn v I := by rw [injOn_iff_injective]; exact hI.injective
      have h : ¬ (v '' J ⊆ span 𝔽 (v '' I))
      · refine fun hle ↦ hcard.not_le ?_ 
        rw [←span_le, ←range_restrict, ←range_restrict] at hle
        have _ := hIfin.fintype; have _ := hJfin.fintype
        have _ : FiniteDimensional 𝔽 (span 𝔽 (Set.range (I.restrict v)))
        · apply FiniteDimensional.span_of_finite; simpa using hIfin.image v
        
        convert finrank_le_finrank_of_le hle 
        <;> rw [finrank_span_eq_card (by assumption), 
          ←Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
        
      obtain ⟨_, ⟨e, he, rfl⟩, heI⟩ := not_subset.1 h
      have' heI' : v e ∉ v '' I := fun h ↦ heI (Submodule.subset_span h)
      have heI'' : e ∉ I := fun h' ↦ heI' (mem_image_of_mem v h') 
      refine' ⟨e, he, heI'', _⟩
      simp only
      have hi : LinearIndependent 𝔽 ((↑) : v '' I → W)
      · rwa [← linearIndependent_image hIinj]
      have h_end := hi.insert heI
      rwa [←linearIndependent_subtype_congr image_insert_eq, 
        ←linearIndependent_image <| (injOn_insert heI'').2 ⟨hIinj, heI'⟩] at h_end )
    ( by 
        refine fun I hI ↦ linearIndependent_of_finite_index _ (fun t ht ↦ ?_)
        have hi : LinearIndependent _ _ := hI (Subtype.val '' t) (by aesop) (ht.image Subtype.val)
        have h_im : LinearIndependent 𝔽 _ := hi.image
        apply LinearIndependent.of_subtype_range _  
        · exact (linearIndependent_equiv (Equiv.Set.ofEq (by ext; simp : v '' _ = _))).1 h_im  
        rintro ⟨⟨x,hx⟩,hx'⟩ ⟨⟨y ,hy⟩, hy'⟩ (hxy : v x = v y) 
        simp only [Subtype.mk.injEq]
        convert (hi.injective.eq_iff (a := ⟨x,by aesop⟩) (b := ⟨y,by aesop⟩)).1 hxy
        simp only [Subtype.mk.injEq] )
    ( fun _ _ ↦ subset_univ _ )

@[simp] theorem matroid_on_univ_of_fun_apply (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) 
  (I : Set α) :
   (matroid_on_univ_of_fun 𝔽 f).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) := 
   by simp [matroid_on_univ_of_fun]

@[simp] theorem matroid_on_univ_of_fun_ground (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) : 
  (matroid_on_univ_of_fun 𝔽 f).E = univ := rfl 

instance matroid_on_univ_of_fun_finitary (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) : 
    Finitary (matroid_on_univ_of_fun 𝔽 f) := by
  rw [matroid_on_univ_of_fun]; infer_instance 

def matroid_of_fun (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) := 
  (matroid_on_univ_of_fun 𝔽 f) ↾ E 

theorem matroid_of_fun_indep_iff' (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E I : Set α) :
    (matroid_of_fun 𝔽 f E).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) ∧ I ⊆ E := by 
  simp [matroid_of_fun]

theorem matroid_of_fun_indep_iff (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) 
    (E : Set α) (hf : support f ⊆ E) (I : Set α) : 
    (matroid_of_fun 𝔽 f E).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) := by 
  simp only [matroid_of_fun_indep_iff', and_iff_left_iff_imp]
  exact fun hli ↦ subset_trans (fun x hxI ↦ by exact hli.ne_zero ⟨x, hxI⟩) hf
   
@[simp] theorem matroid_of_fun_ground (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :     
    (matroid_of_fun 𝔽 f E).E = E := rfl 

instance matroid_of_fun_finitary (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) : 
    Finitary (matroid_of_fun 𝔽 f E) := by 
  rw [matroid_of_fun]; infer_instance  

theorem matroid_of_fun_finite (f : α → W) (E : Set α) (hfin : E.Finite) : 
    (matroid_of_fun 𝔽 f E ).Finite :=
  ⟨hfin⟩ 

def rep_of_fun_univ (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) : 
    (matroid_on_univ_of_fun 𝔽 f).Rep 𝔽 W where
  to_fun := f
  valid' := by simp [IsRep]

def rep_of_fun (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) (hf : support f ⊆ E) : 
    (matroid_of_fun 𝔽 f E).Rep 𝔽 W where 
  to_fun := f
  valid' := by simp [IsRep, matroid_of_fun_indep_iff _ _ _ hf] 

@[simp] theorem matroid_of_fun_indicator_eq (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) 
    (E : Set α) : matroid_of_fun 𝔽 (indicator E f) E = matroid_of_fun 𝔽 f E := by 
  simp only [eq_iff_indep_iff_indep_forall, matroid_of_fun_ground, true_and]
  intro I hIE 
  rw [matroid_of_fun_indep_iff', and_iff_left hIE, matroid_of_fun_indep_iff', and_iff_left hIE]
  convert Iff.rfl using 2
  ext ⟨x, hx⟩
  simp only [restrict_apply, indicator_of_mem (hIE hx)]  

noncomputable def rep_of_fun' (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) : 
    (matroid_of_fun 𝔽 f E).Rep 𝔽 W where
      to_fun := indicator E f
      valid' := (by 
      rw [←matroid_of_fun_indicator_eq, IsRep]
      intro I
      rw [matroid_of_fun_indep_iff _ _ _ support_indicator_subset] )

theorem Rep.range_subset_span_base (v : M.Rep 𝔽 W) (hB : M.Base B) : range v ⊆ span 𝔽 (v '' B) := by 
  rintro _ ⟨e, he ,rfl⟩ 
  
  obtain (heB | heB) := em (e ∈ B)
  · exact subset_span (mem_image_of_mem _ heB)
  by_contra h'
  have hind := LinearIndependent.insert ?_ h'
  
  · rw [←linearIndependent_subtype_congr image_insert_eq, ←v.indep_iff_image_of_inj] at hind
    · exact heB (hB.mem_of_insert_indep hind) 
    rw [injOn_insert heB, and_iff_right (v.injOn_of_indep hB.indep)]
    exact fun h'' ↦ h' <| mem_of_mem_of_subset h'' subset_span
  exact v.linear_indep_image hB.indep
  
theorem Rep.span_range_eq_span_base (v : M.Rep 𝔽 W) (hB : M.Base B) : 
     span 𝔽 (range (restrict B v)) = span 𝔽 (range v) := by 
  rw [range_restrict, eq_comm]
  exact span_eq_of_le _ (v.range_subset_span_base hB) (span_mono (image_subset_range _ _))

/-- A representation is `FullRank` if its vectors span the space -/
def Rep.FullRank (v : M.Rep 𝔽 W) : Prop := ⊤ ≤ span 𝔽 (range v)

/-- Restrict a representation to the submodule spanned by its image -/
def Rep.restrict_span (v : M.Rep 𝔽 W) : M.Rep 𝔽 (span 𝔽 (range v)) where
  to_fun := inclusion subset_span ∘ rangeFactorization v
  valid' := (by 
    intro I
    rw [v.indep_iff]
    refine ⟨fun h ↦ LinearIndependent.of_comp (Submodule.subtype _) (by rwa [coeSubtype]), 
      fun h ↦ h.map' (Submodule.subtype _) (ker_subtype _)⟩ )

theorem Rep.FullRank.span_range {v : M.Rep 𝔽 W} (h : v.FullRank) : span 𝔽 (range v) = ⊤ := by 
  rwa [eq_top_iff]

theorem Rep.fullRank_iff {v : M.Rep 𝔽 W} : v.FullRank ↔ span 𝔽 (range v) = ⊤ := by
  rw [FullRank, eq_top_iff]

@[simp] theorem Rep.restrict_span_apply (v : M.Rep 𝔽 W) (e : α) : 
  v.restrict_span e = inclusion subset_span (rangeFactorization v e) := rfl 

theorem Rep.restrict_span_fullRank (v : M.Rep 𝔽 W) : 
    v.restrict_span.FullRank := by
  change _ ≤ span 𝔽 (range (inclusion subset_span ∘ _))
  rw [range_comp, surjective_onto_range.range_eq, image_univ, range_inclusion]
  change _ ≤ span 𝔽 ((Submodule.subtype (span 𝔽 (range ↑v))) ⁻¹' _) 
  simp

/-- A base of `M` gives a linear basis in a full-rank representation -/
noncomputable def Rep.FullRank.basis_of_base {v : M.Rep 𝔽 W} (h : v.FullRank) (hB : M.Base B) : 
    _root_.Basis B 𝔽 W := 
  Basis.mk (v.linear_indep hB.indep) 
    ( by rw [←h.span_range, v.span_range_eq_span_base hB] )

theorem Rep.FullRank.map_equiv {v : M.Rep 𝔽 W} (h : v.FullRank) (ψ : W ≃ₗ[𝔽] W') : 
    (v.map_equiv ψ).FullRank := by 
  rw [Rep.fullRank_iff, map_equiv, map', map, ←Rep.to_fun_eq_coe]
  simp [LinearEquiv.coe_coe, range_comp, h.span_range]
  
/-- A base of `M` gives a (linear) basis for the span of the range of a representation -/
noncomputable def Rep.basis_of_base (v : M.Rep 𝔽 W) (hB : M.Base B) : 
    _root_.Basis B 𝔽 (span 𝔽 (range v)) := 
  (Basis.span (v.linear_indep hB.indep)).map <| LinearEquiv.ofEq _ _ (v.span_range_eq_span_base hB)

/-- The natural representation with rows indexed by a base -/
noncomputable def Rep.to_standard_rep (v : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B →₀ 𝔽) :=
  v.restrict_span.map_equiv (v.restrict_span_fullRank.basis_of_base hB).repr 

/-- A matroid is representable if it has a representation -/  
def Representable (M : Matroid α) (𝔽 : Type _) [Field 𝔽] : Prop := 
    ∃ (X : Set α), _root_.Nonempty (M.Rep 𝔽 (X →₀ 𝔽))

theorem Rep.representable (v : M.Rep 𝔽 W) : M.Representable 𝔽 :=
  have ⟨_, hB⟩ := M.exists_base
  ⟨_, ⟨v.to_standard_rep hB⟩⟩ 

theorem matroid_of_fun_representable (𝔽 : Type _) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) : 
    (matroid_of_fun 𝔽 f E).Representable 𝔽 := 
  (rep_of_fun' 𝔽 f E).representable

theorem Rep.standard_rep_eq_one (v : M.Rep 𝔽 W) (hB : M.Base B) (e : B) : 
    (v.to_standard_rep hB) e e = 1 := by 
  simp only [Rep.to_standard_rep, Rep.FullRank.basis_of_base, Rep.map_equiv_apply, 
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  simp
  
theorem Rep.standard_rep_eq_zero (v : M.Rep 𝔽 W) (hB : M.Base B) (e f : B) (hef : e ≠ f) : 
    (v.to_standard_rep hB) e f = 0 := by 
  simp [Rep.to_standard_rep, Rep.FullRank.basis_of_base, Rep.map_equiv_apply, 
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  exact Finsupp.single_eq_of_ne hef

theorem Rep.standard_rep_fullRank (v : M.Rep 𝔽 W) (hB : M.Base B) : 
    (v.to_standard_rep hB).FullRank := 
  v.restrict_span_fullRank.map_equiv _ 
  
/-- The natural representation with rows indexed by a base -/
noncomputable def Rep.to_standard_rep' [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B → 𝔽) :=
  have := hB.finite.to_subtype
  (v.to_standard_rep hB).map_equiv (Finsupp.linearEquivFunOnFinite 𝔽 𝔽 B)
  
theorem Rep.standard_rep_eq_one' [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) (e : B) : 
    (v.to_standard_rep' hB) e e = 1 := by 
  classical 
  have := hB.finite.to_subtype
  simp [to_standard_rep', v.standard_rep_eq_one hB]
  
theorem Rep.standard_rep_eq_zero' [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) (e f : B) 
  (hef : e ≠ f) : (v.to_standard_rep' hB) e f = 0 := by 
  classical
  have := hB.finite.to_subtype 
  simp [to_standard_rep', v.standard_rep_eq_zero hB _ _ hef]

theorem Representable.exists_standard_rep (h : Representable M 𝔽) (hB : M.Base B) : 
    ∃ v : M.Rep 𝔽 (B →₀ 𝔽), v.FullRank  :=
  let ⟨_, ⟨v⟩⟩ := h; ⟨v.to_standard_rep hB, v.standard_rep_fullRank hB⟩
  
theorem Representable.exists_standard_rep' [FiniteRk M] (h : Representable M 𝔽) (hB : M.Base B) : 
    ∃ v : M.Rep 𝔽 (B → 𝔽), v.FullRank := 
  let ⟨_, ⟨v⟩⟩ := h; ⟨v.to_standard_rep' hB, (v.standard_rep_fullRank hB).map_equiv _⟩ 
  
theorem Representable.exists_fin_rep [FiniteRk M] (h : Representable M 𝔽) : 
    ∃ v : M.Rep 𝔽 (Fin M.rk → 𝔽), v.FullRank := by
  obtain ⟨B, hB⟩ := M.exists_base
  have _ := hB.finite.fintype
  obtain ⟨v, hv⟩ := h.exists_standard_rep' hB 
  have hcard := hB.ncard
  rw [←Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hcard
  use v.map_equiv <| LinearEquiv.piCongrLeft' 𝔽 (fun _ ↦ 𝔽) (Fintype.equivFinOfCardEq hcard) 
  exact hv.map_equiv _
  
theorem Rep.subset_span_of_basis' (v : M.Rep 𝔽 W) (h : M.Basis' I X) : 
    v '' X ⊆ span 𝔽 (v '' I) := by 
  rintro _ ⟨e, he, rfl⟩
  obtain (heI | heI) := em (v e ∈ v '' I)
  · exact subset_span heI
  obtain (heI' | heI') := em (e ∈ I)
  · exact (heI (mem_image_of_mem _ heI')).elim 
  have hi := h.insert_not_indep ⟨he, heI'⟩ 
  rw [v.indep_iff_image, injOn_insert heI', and_iff_left heI, 
    and_iff_left (v.injOn_of_indep h.indep), linearIndependent_subtype_congr image_insert_eq, 
    (linearIndependent_insert heI), not_and,  not_not] at hi 
  exact hi <| v.linear_indep_image h.indep 

theorem Rep.subset_span_of_basis (v : M.Rep 𝔽 W) (h : M.Basis I X) : v '' X ⊆ span 𝔽 (v '' I) :=
  v.subset_span_of_basis' h.basis'

theorem Rep.span_eq_span_inter_ground (v : M.Rep 𝔽 W) (X : Set α) : 
    span 𝔽 (v '' X) = span 𝔽 (v '' (X ∩ M.E)) := by 
  refine le_antisymm ?_ (span_mono (image_subset v <| inter_subset_left _ _))
  rw [←span_insert_zero (s := v '' (X ∩ M.E)), ←inter_union_diff X M.E, image_union, 
    inter_union_diff]
  apply span_mono (union_subset (subset_insert _ _) _)
  rintro _ ⟨e, he, rfl⟩ 
  left 
  rw [←nmem_support]
  exact not_mem_subset v.support_subset_ground he.2

@[simp] theorem Rep.span_eq_span_cl (v : M.Rep 𝔽 W) (X : Set α) : 
    span 𝔽 (v '' M.cl X) = span 𝔽 (v '' X) := by 
  rw [v.span_eq_span_inter_ground X, cl_eq_cl_inter_ground, le_antisymm_iff, 
    and_iff_left (span_mono (image_subset _ (M.subset_cl _)))]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E) 
  rw [←hI.cl_eq_cl]
  exact (span_mono <| v.subset_span_of_basis hI.indep.basis_cl).trans <| 
    span_le.2 (span_mono (image_subset _ hI.subset))

theorem Rep.span_eq_span_of_basis' (v : M.Rep 𝔽 W) (h : M.Basis' I X) : 
    span 𝔽 (v '' I) = span 𝔽 (v '' X) :=
  le_antisymm (span_mono (image_subset _ h.subset)) (span_le.2 (v.subset_span_of_basis' h)) 

theorem Rep.span_eq_span_of_basis (v : M.Rep 𝔽 W) (h : M.Basis I X) : 
    span 𝔽 (v '' I) = span 𝔽 (v '' X) :=
  v.span_eq_span_of_basis' h.basis' 

theorem Rep.span_le_span_of_cl_subset_cl (v : M.Rep 𝔽 W) (h : M.cl X ⊆ M.cl Y) :
    span 𝔽 (v '' X) ≤ span 𝔽 (v '' Y) := by 
  obtain ⟨I, hI⟩ := M.exists_basis' X 
  refine span_le.2 <| (v.subset_span_of_basis' hI).trans <| span_le.2 ?_
  rw [←v.span_eq_span_cl]
  exact (image_subset _ (hI.basis_cl_right.subset.trans h)).trans subset_span 
  
theorem Rep.subset_span_iff (v : M.Rep 𝔽 W) (hX : X ⊆ M.E := by aesop_mat) : 
    v '' X ⊆ span 𝔽 (v '' Y) ↔ X ⊆ M.cl Y := by 
  -- obtain ⟨I, hI⟩ := M.exists_basis' X

  refine ⟨fun h e heX ↦ ?_, fun h ↦ ?_⟩ 
  · obtain ⟨I, hI⟩ := M.exists_basis' Y 
    -- have hsp := h (mem_image_of_mem _ heX)
    rw [←v.span_eq_span_of_basis' hI] at h
    rw [←hI.cl_eq_cl, hI.indep.mem_cl_iff', and_iff_right (hX heX)]
    
    specialize h (mem_image_of_mem _ heX)
    refine fun hi ↦ by_contra fun heI ↦ ?_
    have hind := v.linear_indep_image hi 
    rw [linearIndependent_subtype_congr image_insert_eq, linearIndependent_insert] at hind
    · exact (hind.2 h).elim  
    refine fun heI' ↦ heI ?_ 
    rwa [←(v.injOn_of_indep hi).mem_image_iff (subset_insert _ _) (mem_insert _ _)]
  rw [←v.span_eq_span_cl]
  exact (image_subset v h).trans subset_span
    

-- Ugly proof in the second part 
theorem Rep.cl_eq (v : M.Rep 𝔽 W) (X : Set α) : M.cl X = M.E ∩ v ⁻¹' (span 𝔽 (v '' X)) := by 
  obtain ⟨I, hI⟩ := M.exists_basis' (X)
  rw [←hI.cl_eq_cl, subset_antisymm_iff, subset_inter_iff, and_iff_right (cl_subset_ground _ _), 
    ←image_subset_iff, and_iff_left]
  · exact (v.subset_span_of_basis hI.indep.basis_cl).trans (span_mono (image_subset _ hI.subset))
  rintro x ⟨hxE, hx⟩  
  rw [mem_preimage] at hx
  
  rw [hI.indep.mem_cl_iff, or_iff_not_imp_right, dep_iff, 
    and_iff_left <| insert_subset hxE hI.indep.subset_ground]
  refine fun hxI hi ↦ ?_
  apply (v.linear_indep hi).not_mem_span_image (s := Subtype.val ⁻¹' I) 
    (x := ⟨x, mem_insert _ _⟩) (by simpa)
  simp only [restrict_apply] 

  have hsp := span_mono (v.subset_span_of_basis' hI) hx
  
  rw [span_coe_eq_restrictScalars, restrictScalars_self] at hsp 
  convert hsp 
  ext
  aesop

theorem Rep.span_eq_span_of_cl_eq_cl (v : M.Rep 𝔽 W) (h : M.cl X = M.cl Y) : 
    span 𝔽 (v '' X) = span 𝔽 (v '' Y) := by 
  rw [span_eq_span_inter_ground, span_eq_span_inter_ground _ Y]
  simp_rw [le_antisymm_iff, span_le, v.subset_span_iff (inter_subset_right _ _), 
    ←cl_eq_cl_inter_ground]
  constructor
  · rw [←h, cl_eq_cl_inter_ground]; exact subset_cl _ _
  rw [h, cl_eq_cl_inter_ground]
  exact subset_cl _ _

-- theorem Rep.r_eq [FiniteRk M] (v : M.Rep 𝔽 W) (X : Set α) : 
--     M.r X = finrank 𝔽 (span 𝔽 (v '' X)) := by
--   obtain ⟨I, hI⟩ := M.exists_basis' X 
--   rw [←hI.r]