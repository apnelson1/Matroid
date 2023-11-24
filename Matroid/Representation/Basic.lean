import Matroid.Minor.Iso
import Matroid.Simple
import Matroid.Extension
import Matroid.ForMathlib.Card
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.Vandermonde
import Matroid.Constructions.ImagePreimage
import Matroid.Constructions.Uniform
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace


variable {α β W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix

set_option autoImplicit false

namespace Matroid

/-- A function `v : α → W` represents `M` over `𝔽` if independence of `I` in `M` corresponds to
  linear independence of `v '' I` in `W`. -/
def IsRep (M : Matroid α) (𝔽 : Type*) [CommSemiring 𝔽] [AddCommMonoid W] [Module 𝔽 W]
    (v : α → W) :=
  ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v)

@[pp_dot] structure Rep (M : Matroid α) (𝔽 W : Type*) [CommSemiring 𝔽] [AddCommMonoid W]
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

@[simp] theorem Rep.coe_mk (f : α → W) (valid' : M.IsRep 𝔽 f) : (Rep.mk f valid' : α → W) = f := rfl

theorem Rep.isRep (v : M.Rep 𝔽 W) : M.IsRep 𝔽 v := v.valid'

theorem Rep.indep_iff (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v) :=
  v.valid' I

theorem Rep.onIndep (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (I.restrict v) :=
  v.indep_iff.1 hI

theorem Rep.injOn_of_indep (v : M.Rep 𝔽 W) (hI : M.Indep I) : InjOn v I :=
  injOn_iff_injective.2 ((v.onIndep hI).injective)

theorem Rep.indep_image (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (v '' I).incl := by
  rw [←linearIndependent_image <| v.injOn_of_indep hI]
  exact v.onIndep hI

theorem Rep.indep_iff_image_of_inj (v : M.Rep 𝔽 W) (h_inj : InjOn v I) :
    M.Indep I ↔ LinearIndependent 𝔽 (v '' I).incl := by
  refine ⟨v.indep_image, fun hi ↦ ?_⟩
  rw [v.indep_iff, restrict_eq]
  exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

theorem Rep.indep_iff_image (v : M.Rep 𝔽 W) :
    M.Indep I ↔ LinearIndependent 𝔽 (v '' I).incl ∧ InjOn v I :=
  ⟨fun h ↦ ⟨v.indep_image h, v.injOn_of_indep h⟩,
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

/-- A function from `M.E` to a module determines a representation -/
noncomputable def repOfSubtypeFun (f : M.E → W) [DecidablePred (· ∈ M.E)]
    (hf : ∀ {I : Set M.E}, M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f)) :
    M.Rep 𝔽 W :=
  rep_of_ground
  ( fun a ↦ if ha : a ∈ M.E then f ⟨a,ha⟩ else 0 )
  ( by aesop )
  ( by
    intro I hI
    rw [←Subtype.range_val (s := M.E), subset_range_iff_exists_image_eq] at hI
    obtain ⟨I, rfl⟩ := hI
    rw [hf]
    apply linearIndependent_equiv' <| Equiv.Set.image _ _ Subtype.val_injective
    ext ⟨⟨x,hx⟩, hx'⟩
    simp [dif_pos hx] )

@[simp] theorem repOfSubtypeFun_apply (f : M.E → W) [DecidablePred (· ∈ M.E)]
    (hf : ∀ {I : Set M.E}, M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f))
    (e : M.E) : repOfSubtypeFun f hf e = f e := by
  simp [repOfSubtypeFun, rep_of_ground]

theorem repOfSubtypeFun_apply_mem (f : M.E → W) [DecidablePred (· ∈ M.E)]
    (hf : ∀ {I : Set M.E}, M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f))
    {e : α} (he : e ∈ M.E) : repOfSubtypeFun f hf e = f ⟨e,he⟩ := by
  simp [repOfSubtypeFun, rep_of_ground, dif_pos he]

theorem repOfSubtypeFun_apply_not_mem (f : M.E → W) [DecidablePred (· ∈ M.E)]
    (hf : ∀ {I : Set M.E}, M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f))
    {e : α} (he : e ∉ M.E) : repOfSubtypeFun f hf e = 0 := by
  simp [repOfSubtypeFun, rep_of_ground, dif_neg he]

theorem rep_of_ground_coe_eq (f : α → W) (h_support : support f ⊆ M.E)
  (hf : ∀ {I}, I ⊆ M.E → (M.Indep I ↔ LinearIndependent 𝔽 (f ∘ ((↑) : I → α)))) :
  (rep_of_ground f h_support hf : α → W) = f := rfl

/-- Compose a representation `v` with a linear map that is injective on the range of `v`-/
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
def Rep.mapEquiv (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') : M.Rep 𝔽 W' := v.map' ψ ψ.ker

@[simp] theorem Rep.map'_apply (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) (e : α) :
    (v.map' ψ hψ) e = ψ (v e) := rfl

@[simp] theorem Rep.mapEquiv_apply (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') (e : α) :
    (v.mapEquiv ψ) e = ψ (v e) := rfl

/--  Compose a representation with a module equality -/
def Rep.subtype_ofEq {W₁ W₂ : Submodule 𝔽 W} (v : M.Rep 𝔽 W₁) (h : W₁ = W₂) : M.Rep 𝔽 W₂ :=
  v.mapEquiv <| LinearEquiv.ofEq _ _ h

@[simp] theorem Rep.subtype_ofEq_apply {W₁ W₂ : Submodule 𝔽 W} (v : M.Rep 𝔽 W₁) (h : W₁ = W₂)
    (e : α) : v.subtype_ofEq h e = LinearEquiv.ofEq _ _ h (v e) := rfl

/-- A representation gives a representation of any restriction -/
noncomputable def Rep.restrict (v : M.Rep 𝔽 W) (X : Set α) : (M ↾ X).Rep 𝔽 W :=
  rep_of_ground (indicator X v) ( by simp )
  ( by
    simp only [restrict_ground_eq, restrict_indep_iff]
    intro I hIX
    rw [v.indep_iff, and_iff_left hIX]
    convert Iff.rfl using 2
    ext ⟨e, he⟩
    simp [hIX he] )

@[simp] theorem Rep.restrict_apply (v : M.Rep 𝔽 W) (X : Set α) :
    (v.restrict X : α → W) = indicator X v := rfl

/-- A representation gives a representation of a preimage -/
def Rep.preimage {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) : (M.preimage f).Rep 𝔽 W :=
  rep_of_ground (v ∘ f)
  ( by
    simp only [preimage_ground_eq, support_subset_iff, comp_apply, ne_eq, mem_preimage]
    exact fun x ↦ Not.imp_symm <| Rep.eq_zero_of_not_mem_ground _ )
  ( by
    intro I _
    rw [preimage_indep_iff, v.indep_iff, restrict_eq, restrict_eq, comp.assoc]
    refine' ⟨fun ⟨h,hInj⟩ ↦ _, fun h ↦ ⟨LinearIndependent.image_of_comp _ _ _ h, ?_⟩⟩
    · exact h.comp (imageFactorization f I) (hInj.imageFactorization_injective)
    rintro x hx y hy hxy
    have hi := h.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩)
    simpa only [comp_apply, Subtype.mk.injEq, hxy, true_imp_iff] using hi )

@[simp] theorem Rep.preimage_apply {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) :
    (v.preimage f : α → W) = v ∘ f := rfl


-- /- this proof is a mess. -/
-- theorem Rep.matroidOfFun_restrict_eq_onGround (v : M.Rep 𝔽 W) :
--     matroidOfFun 𝔽 (M.E.restrict v) univ = M.onGround M.E := by
--   rw [eq_iff_indep_iff_indep_forall, matroidOfFun_ground, onGround_ground Subset.rfl,
--     and_iff_right rfl, onGround]
--   simp only [subset_univ, preimage_indep_iff, forall_true_left, matroidOfFun_indep_iff,
--     v.indep_iff, and_iff_left (Subtype.val_injective.injOn _)]
--   refine fun I ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · refine (linearIndependent_image ?_).2 ?_
--     · rintro _ ⟨a, ha, rfl⟩ _ ⟨b,hb,rfl⟩ hab
--       have := (h.injective.eq_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).1 hab
--       simp only [Subtype.mk.injEq] at this
--       rw [this]
--     convert h.image <;> simp [restrict_eq, ← image_comp]
--   refine (linearIndependent_image ?_).2 ?_
--   · rw [restrict_eq]
--     rintro ⟨a,ha⟩ ha' ⟨b,hb⟩ hb' (hab : v a = v b)
--     have := (h.injective.eq_iff (a := ⟨a, by aesop⟩) (b := ⟨b,by aesop⟩)).1 hab
--     simp only [Subtype.mk.injEq] at this
--     simpa only [Subtype.mk.injEq]
--   convert h.image <;> simp [restrict_eq, ← image_comp]

def Rep.ofEq {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) : N.Rep 𝔽 W :=
  rep_of_ground v
  ( v.support_subset_ground.trans_eq (congr_arg _ h) )
  ( by intro I _; rw [←h, v.indep_iff] )

@[simp] theorem Rep.ofEq_apply {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) :
  (v.ofEq h : α → W) = v := rfl

def Rep.onGround (v : M.Rep 𝔽 W) : (M.onGround M.E).Rep 𝔽 W := v.preimage (incl M.E)

def Rep.onGround' (v : M.Rep 𝔽 W) (E : Set α) : (M.onGround E).Rep 𝔽 W := v.preimage (incl E)

/-- Carry a representation across a matroid isomorphism -/
noncomputable def Rep.iso {M : Matroid α} {N : Matroid β} (v : M.Rep 𝔽 W) (i : Iso M N) :
    N.Rep 𝔽 W :=
  ((v.preimage i.symm).restrict N.E).ofEq i.symm.eq_preimage.symm

theorem Rep.iso_apply {M : Matroid α} {N : Matroid β} (v : M.Rep 𝔽 W) (i : Iso M N) {x : β}
    (hx : x ∈ N.E) : v.iso i x = v (i.symm x) := by
  simp [iso, indicator_of_mem hx]


/-- A function from `α` to a module gives rise to a finitary matroid on `α` -/
def matroidOnUnivOfFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (v : α → W) : Matroid α :=
    matroid_of_indep_of_finitary univ
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
      have hi : LinearIndependent 𝔽 (v '' I).incl := (linearIndependent_image hIinj).1 hI
      have h_end : LinearIndependent 𝔽 (incl _) := hi.insert heI
      rwa [←image_insert_eq,
        ←linearIndependent_image <| (injOn_insert heI'').2 ⟨hIinj, heI'⟩] at h_end
        )
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

@[simp] theorem matroidOnUnivOfFun_apply (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W)
  (I : Set α) :
   (matroidOnUnivOfFun 𝔽 f).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) :=
   by simp [matroidOnUnivOfFun]

@[simp] theorem matroidOnUnivOfFun_ground (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) :
  (matroidOnUnivOfFun 𝔽 f).E = univ := rfl

instance matroidOnUnivOfFun_finitary (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) :
    Finitary (matroidOnUnivOfFun 𝔽 f) := by
  rw [matroidOnUnivOfFun]; infer_instance

def matroidOfFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :=
  (matroidOnUnivOfFun 𝔽 f) ↾ E

theorem matroidOfFun_indep_iff' (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E I : Set α) :
    (matroidOfFun 𝔽 f E).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) ∧ I ⊆ E := by
  simp [matroidOfFun]

theorem matroidOfFun_indep_iff (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W)
    (E : Set α) (hf : support f ⊆ E) (I : Set α) :
    (matroidOfFun 𝔽 f E).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) := by
  simp only [matroidOfFun_indep_iff', and_iff_left_iff_imp]
  exact fun hli ↦ subset_trans (fun x hxI ↦ by exact hli.ne_zero ⟨x, hxI⟩) hf

@[simp] theorem matroidOfFun_ground (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    (matroidOfFun 𝔽 f E).E = E := rfl

instance matroidOfFun_finitary (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    Finitary (matroidOfFun 𝔽 f E) := by
  rw [matroidOfFun]; infer_instance

theorem matroidOfFun_finite (f : α → W) (E : Set α) (hfin : E.Finite) :
    (matroidOfFun 𝔽 f E).Finite :=
  ⟨hfin⟩

def repOfFunUniv (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) :
    (matroidOnUnivOfFun 𝔽 f).Rep 𝔽 W where
  to_fun := f
  valid' := by simp [IsRep]

def repOfFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) (hf : support f ⊆ E) :
    (matroidOfFun 𝔽 f E).Rep 𝔽 W where
  to_fun := f
  valid' := by simp [IsRep, matroidOfFun_indep_iff _ _ _ hf]

@[simp] theorem matroidOfFun_indicator_eq (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W)
    (E : Set α) : matroidOfFun 𝔽 (indicator E f) E = matroidOfFun 𝔽 f E := by
  simp only [eq_iff_indep_iff_indep_forall, matroidOfFun_ground, true_and]
  intro I hIE
  rw [matroidOfFun_indep_iff', and_iff_left hIE, matroidOfFun_indep_iff', and_iff_left hIE]
  convert Iff.rfl using 2
  ext ⟨x, hx⟩
  simp only [restrict_apply, indicator_of_mem (hIE hx)]

def matroidOfSubtypeFun {E : Set α} (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : E → W) :
    Matroid α := matroidOfFun 𝔽 (Function.extend Subtype.val f 0) E

@[simp] theorem matroidOfSubtypeFun_indep_iff {E : Set α} (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W]
    (f : E → W) (I : Set α) : (matroidOfSubtypeFun 𝔽 f).Indep I
      ↔ ∃ (I₀ : Set E), LinearIndependent 𝔽 (I₀.restrict f) ∧ I = (↑) '' I₀ := by
  simp only [matroidOfSubtypeFun, matroidOfFun._eq_1, restrict_indep_iff, matroidOnUnivOfFun_apply]
  refine ⟨fun ⟨h,hIE⟩ ↦ ?_, ?_⟩
  · rw [←Subtype.range_val (s := E), subset_range_iff_exists_image_eq] at hIE
    obtain ⟨I₀, rfl⟩ := hIE
    refine ⟨_, ?_, rfl⟩
    convert h.comp (imageFactorization Subtype.val I₀) _
    ext x
    simp only [restrict_apply, comp_apply, Subtype.exists, exists_prop, exists_eq_right,
      imageFactorization, exists_apply_eq_apply, not_true, Subtype.val_injective.extend_apply]
    apply (Subtype.val_injective.injOn _).imageFactorization_injective
  rintro ⟨I, hI, rfl⟩
  simp only [image_subset_iff, Subtype.coe_preimage_self, subset_univ, and_true]
  set  g : (Subtype.val '' I) → I := fun x ↦ ⟨⟨x,
    ( by obtain ⟨_,⟨x,hx,rfl⟩⟩ := x; simp)⟩, (by obtain ⟨_,⟨x,hx,rfl⟩⟩ := x; simpa )⟩
  convert hI.comp g ?_
  · ext x
    obtain ⟨_,⟨x,hx,rfl⟩⟩ := x
    simp [Subtype.val_injective.extend_apply]
  rintro ⟨_,⟨⟨x,hxE⟩,hx,rfl⟩⟩ ⟨_,⟨⟨y,hyE⟩,hy,rfl⟩⟩ hxy
  simpa using hxy

noncomputable def repOfFun' (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    (matroidOfFun 𝔽 f E).Rep 𝔽 W where
  to_fun := indicator E f
  valid' := ( by
    rw [←matroidOfFun_indicator_eq, IsRep]
    intro I
    rw [matroidOfFun_indep_iff _ _ _ support_indicator_subset] )

@[simp] theorem matroidOfSubtypeFun_ground {E : Set α} (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W]
    (f : E → W) : (matroidOfSubtypeFun 𝔽 f).E = E := rfl

noncomputable def matroidOfSubtypeFun_rep {E : Set α} (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W]
    (f : E → W) : (matroidOfSubtypeFun 𝔽 f).Rep 𝔽 W where
      to_fun := Subtype.val.extend f 0
      valid' := (by
        refine' (repOfFun 𝔽 (Subtype.val.extend f 0) E (fun x hx ↦ by_contra fun hxE ↦ ?_)).isRep
        rw [mem_support, extend_apply'] at hx
        · exact hx rfl
        rintro ⟨⟨a,ha⟩,rfl⟩
        exact hxE ha )

@[simp] theorem matroidOfSubtypeFun_rep_apply {E : Set α} (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W]
    (f : E → W) (e : E) : matroidOfSubtypeFun_rep 𝔽 f e = f e := by
  change Subtype.val.extend f 0 e = f e
  rw [Function.Injective.extend_apply Subtype.val_injective]





theorem Rep.range_subset_span_base (v : M.Rep 𝔽 W) (hB : M.Base B) : range v ⊆ span 𝔽 (v '' B) := by
  rintro _ ⟨e, he ,rfl⟩

  obtain (heB | heB) := em (e ∈ B)
  · exact subset_span (mem_image_of_mem _ heB)
  by_contra h'
  have hind : LinearIndependent 𝔽 ((insert (v e) (v '' B)).incl) :=
    (LinearIndependent.insert ?_ h')


  · rw [←image_insert_eq, ←v.indep_iff_image_of_inj] at hind
    · exact heB (hB.mem_of_insert_indep hind)
    rw [injOn_insert heB, and_iff_right (v.injOn_of_indep hB.indep)]
    exact fun h'' ↦ h' <| mem_of_mem_of_subset h'' subset_span
  exact v.indep_image hB.indep

theorem Rep.span_range_eq_span_base (v : M.Rep 𝔽 W) (hB : M.Base B) :
     span 𝔽 (range (Set.restrict B v)) = span 𝔽 (range v) := by
  rw [range_restrict, eq_comm]
  exact span_eq_of_le _ (v.range_subset_span_base hB) (span_mono (image_subset_range _ _))

/-- A representation is `FullRank` if its vectors span the space -/
def Rep.FullRank (v : M.Rep 𝔽 W) : Prop := ⊤ ≤ span 𝔽 (range v)

/-- Restrict a representation to the submodule spanned by its image -/
def Rep.restrict_span (v : M.Rep 𝔽 W) : M.Rep 𝔽 (span 𝔽 (range v)) where
  to_fun := codRestrict v _ (fun x ↦ subset_span (mem_range_self _))
  valid' := (by
    intro I
    rw [v.indep_iff]
    refine ⟨fun h ↦ LinearIndependent.of_comp (Submodule.subtype _) (by rwa [coeSubtype]),
      fun h ↦ h.map' (Submodule.subtype _) (ker_subtype _)⟩ )

theorem Rep.FullRank.span_range {v : M.Rep 𝔽 W} (h : v.FullRank) : span 𝔽 (range v) = ⊤ := by
  rwa [eq_top_iff]

theorem Rep.fullRank_iff {v : M.Rep 𝔽 W} : v.FullRank ↔ span 𝔽 (range v) = ⊤ := by
  rw [FullRank, eq_top_iff]

theorem Rep.restrict_span_eq_inclusion (v : M.Rep 𝔽 W) :
  (v.restrict_span : α → _) = Set.inclusion subset_span ∘ rangeFactorization v := by ext; rfl

@[simp] theorem Rep.restrict_span_apply (v : M.Rep 𝔽 W) (e : α) :
  v.restrict_span e = Set.inclusion subset_span (rangeFactorization v e) := rfl

theorem Rep.restrict_span_fullRank (v : M.Rep 𝔽 W) :
    v.restrict_span.FullRank := by
  change _ ≤ span 𝔽 _
  rw [restrict_span_eq_inclusion]
  change _ ≤ span 𝔽 (range (Set.inclusion subset_span ∘ _))
  rw [range_comp, surjective_onto_range.range_eq, image_univ, Set.range_inclusion]
  change _ ≤ span 𝔽 ((Submodule.subtype (span 𝔽 (range ↑v))) ⁻¹' _)
  simp

/-- A base of `M` gives a linear basis in a full-rank representation -/
noncomputable def Rep.FullRank.basis_of_base {v : M.Rep 𝔽 W} (h : v.FullRank) (hB : M.Base B) :
    _root_.Basis B 𝔽 W :=
  Basis.mk (v.onIndep hB.indep) ( by rw [←h.span_range, v.span_range_eq_span_base hB] )

theorem Rep.FullRank.mapEquiv {v : M.Rep 𝔽 W} (h : v.FullRank) (ψ : W ≃ₗ[𝔽] W') :
    (v.mapEquiv ψ).FullRank := by
  rw [Rep.fullRank_iff, Rep.mapEquiv, map', map, ←Rep.to_fun_eq_coe]
  simp [LinearEquiv.coe_coe, range_comp, h.span_range]

/-- A base of `M` gives a (linear) basis for the span of the range of a representation -/
noncomputable def Rep.basis_of_base (v : M.Rep 𝔽 W) (hB : M.Base B) :
    _root_.Basis B 𝔽 (span 𝔽 (range v)) :=
  (Basis.span (v.onIndep hB.indep)).map <| LinearEquiv.ofEq _ _ (v.span_range_eq_span_base hB)

/-- The natural representation with rows indexed by a base with `Finsupp` -/
noncomputable def Rep.standardRep' (v : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B →₀ 𝔽) :=
  v.restrict_span.mapEquiv (v.restrict_span_fullRank.basis_of_base hB).repr

theorem Rep.standardRep_eq_one' (v : M.Rep 𝔽 W) (hB : M.Base B) (e : B) :
    (v.standardRep' hB) e e = 1 := by
  simp only [Rep.standardRep', Rep.FullRank.basis_of_base, Rep.mapEquiv_apply,
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  simp

theorem Rep.standardRep_eq_zero' (v : M.Rep 𝔽 W) (hB : M.Base B) (e f : B) (hef : e ≠ f) :
    (v.standardRep' hB) e f = 0 := by
  simp [Rep.standardRep', Rep.FullRank.basis_of_base, Rep.mapEquiv_apply,
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  exact Finsupp.single_eq_of_ne hef

theorem Rep.standardRep_fullRank' (v : M.Rep 𝔽 W) (hB : M.Base B) : (v.standardRep' hB).FullRank :=
  v.restrict_span_fullRank.mapEquiv _

/-- The natural representation with rows indexed by a base -/
noncomputable def Rep.standardRep [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B → 𝔽) :=
  have := hB.finite.to_subtype
  (v.standardRep' hB).mapEquiv (Finsupp.linearEquivFunOnFinite 𝔽 𝔽 B)

theorem Rep.standardRep_eq_one [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) (e : B) :
    (v.standardRep hB) e e = 1 := by
  classical
  have := hB.finite.to_subtype
  simp [standardRep, v.standardRep_eq_one' hB]

theorem Rep.standardRep_eq_zero [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) (e f : B)
  (hef : e ≠ f) : (v.standardRep hB) e f = 0 := by
  classical
  have := hB.finite.to_subtype
  simp [standardRep, v.standardRep_eq_zero' hB _ _ hef]

theorem Rep.standardRep_fullRank [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) :
    (v.standardRep hB).FullRank :=
  (v.standardRep_fullRank' hB).mapEquiv _

section Constructions

-- Loopy matroids are trivially representable over every field.
def loopyRep (E : Set α) (𝔽 : Type*) [Field 𝔽] : (loopyOn E).Rep 𝔽 𝔽 where
  to_fun := 0
  valid' := by
    refine fun I ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain rfl := loopyOn_indep_iff.1 h
      apply linearIndependent_empty_type
    rw [loopyOn_indep_iff, eq_empty_iff_forall_not_mem]
    exact fun x hxI ↦ h.ne_zero ⟨x, hxI⟩ rfl

-- The empty matroid is trivially representable over every field.
def emptyRep (α : Type*) (𝔽 : Type*) [Field 𝔽] : (emptyOn α).Rep 𝔽 𝔽 :=
  (loopyRep ∅ 𝔽).ofEq <| loopyOn_empty _

-- TODO: The free matroid is trivially representable over every field.
-- def freeRep [DecidableEq α] (E : Set α) [DecidablePred (· ∈ E)] (𝔽 : Type*) [Field 𝔽] :
--     (freeOn E).Rep 𝔽 (α → 𝔽) where
--   to_fun e := if e ∈ E then Pi.single e 1 else 0
--   valid' := by
--     intro I
--     simp




end Constructions

section Representable

/-- A matroid is representable if it has a representation -/
def Representable (M : Matroid α) (𝔽 : Type*) [Field 𝔽] : Prop := Nonempty (M.Rep 𝔽 (α → 𝔽))

/-- Noncomputably extract a representation from proof of representability -/
noncomputable def Representable.rep (h : M.Representable 𝔽) : M.Rep 𝔽 (α → 𝔽) :=
  Nonempty.some h

theorem Rep.representable (v : M.Rep 𝔽 W) : M.Representable 𝔽 := by
  have ⟨B, hB⟩ := M.exists_base
  set v' := v.standardRep' hB
  refine ⟨(v'.map' Finsupp.lcoeFun ?_).map'
    (Function.ExtendByZero.linearMap _ Subtype.val) ?_⟩
  · rw [Submodule.eq_bot_iff]; rintro x hx; simpa [Finsupp.lcoeFun] using hx
  rw [Submodule.eq_bot_iff]
  rintro x hx
  ext i
  simp only [ExtendByZero.linearMap, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk] at hx
  convert congr_fun hx i
  rw [Subtype.val_injective.extend_apply]

theorem IsRep.representable {v : α → W} (h : M.IsRep 𝔽 v) : M.Representable 𝔽 :=
  Rep.representable ⟨v, h⟩

theorem matroidOfFun_representable (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    (matroidOfFun 𝔽 f E).Representable 𝔽 :=
  (repOfFun' 𝔽 f E).representable

theorem Representable.exists_standardRep' (h : Representable M 𝔽) (hB : M.Base B) :
    ∃ v : M.Rep 𝔽 (B →₀ 𝔽), v.FullRank :=
  let ⟨v⟩ := h; ⟨v.standardRep' hB, v.standardRep_fullRank' hB⟩

theorem Representable.exists_standardRep [FiniteRk M] (h : Representable M 𝔽) (hB : M.Base B) :
    ∃ v : M.Rep 𝔽 (B → 𝔽), v.FullRank  :=
  let ⟨v⟩ := h; ⟨v.standardRep hB, v.standardRep_fullRank hB⟩

theorem Representable.exists_fin_rep [FiniteRk M] (h : Representable M 𝔽) :
    ∃ v : M.Rep 𝔽 (Fin M.rk → 𝔽), v.FullRank := by
  obtain ⟨B, hB⟩ := M.exists_base
  have _ := hB.finite.fintype
  obtain ⟨v, hv⟩ := h.exists_standardRep hB
  have hcard := hB.ncard
  rw [←Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hcard
  use v.mapEquiv <| LinearEquiv.piCongrLeft' 𝔽 (fun _ ↦ 𝔽) (Fintype.equivFinOfCardEq hcard)
  exact hv.mapEquiv _

theorem representable_emptyOn (α 𝔽 : Type*) [Field 𝔽] : (emptyOn α).Representable 𝔽 :=
  (emptyRep α 𝔽).representable

theorem representable_loopyOn (E : Set α) (𝔽 : Type*) [Field 𝔽] :
    (loopyOn E).Representable 𝔽 :=
  (loopyRep E 𝔽).representable

theorem Representable.of_isIso {α β : Type*} {M : Matroid α} {N : Matroid β}
    (h : M.Representable 𝔽) (hMN : M ≅ N) : N.Representable 𝔽 := by
  obtain (⟨-, rfl⟩ | ⟨⟨e⟩⟩) := hMN
  · apply representable_emptyOn
  exact (h.rep.iso e).representable

theorem IsIso.representable_iff {α β : Type*} {M : Matroid α} {N : Matroid β} (hMN : M ≅ N) :
    M.Representable 𝔽 ↔ N.Representable 𝔽 :=
  ⟨fun h ↦ h.of_isIso hMN, fun h ↦ h.of_isIso hMN.symm⟩

theorem invariant_representable (𝔽 : Type*) [Field 𝔽] :
    Invariant (fun M ↦ M.Representable 𝔽) := by
  refine fun {α} {β} M N hMN ↦ ?_
  simp only [eq_iff_iff, hMN.representable_iff]

end Representable

theorem Rep.subset_span_of_basis' (v : M.Rep 𝔽 W) (h : M.Basis' I X) :
    v '' X ⊆ span 𝔽 (v '' I) := by
  rintro _ ⟨e, he, rfl⟩
  obtain (heI | heI) := em (v e ∈ v '' I)
  · exact subset_span heI
  obtain (heI' | heI') := em (e ∈ I)
  · exact (heI (mem_image_of_mem _ heI')).elim
  have hi := h.insert_not_indep ⟨he, heI'⟩
  rw [v.indep_iff_image, injOn_insert heI', and_iff_left heI,
    and_iff_left (v.injOn_of_indep h.indep), image_insert_eq, (linearIndependent_insert heI),
    not_and, not_not] at hi
  exact hi <| v.indep_image h.indep

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
    have hind := v.indep_image hi
    rw [image_insert_eq, linearIndependent_insert] at hind
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
  apply (v.onIndep hi).not_mem_span_image (s := Subtype.val ⁻¹' I)
    (x := ⟨x, mem_insert _ _⟩) (by simpa)

  have hsp := span_mono (v.subset_span_of_basis' hI) hx

  rw [span_coe_eq_restrictScalars, restrictScalars_self] at hsp
  convert hsp
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

section Simple

theorem Rep.eq_zero_iff (v : M.Rep 𝔽 W) (e : α) (he : e ∈ M.E := by aesop_mat) :
    v e = 0 ↔ M.Loop e := by
  rw [←singleton_not_indep he, v.indep_iff, linearIndependent_unique_iff]
  simp only [default_coe_singleton, Set.restrict_apply, ne_eq, not_not]

theorem Rep.eq_zero_of_loop (v : M.Rep 𝔽 W) (h : M.Loop e) : v e = 0 :=
  (v.eq_zero_iff e).2 h

theorem Rep.ne_zero_of_nonloop (v : M.Rep 𝔽 W) (h : M.Nonloop e) : v e ≠ 0 := by
  rw [Ne.def, v.eq_zero_iff e]; exact h.not_loop

theorem Rep.ne_zero_iff_nonloop (v : M.Rep 𝔽 W) (e : α) (he : e ∈ M.E := by aesop_mat) :
    v e ≠ 0 ↔ M.Nonloop e :=
  ⟨fun h ↦ by rwa [←not_loop_iff, ←v.eq_zero_iff e], v.ne_zero_of_nonloop⟩

theorem Rep.loopless_iff (v : M.Rep 𝔽 W) : M.Loopless ↔ ∀ e ∈ M.E, v e ≠ 0 := by
  rw [loopless_iff_forall_nonloop]
  exact ⟨fun h e he ↦ (v.ne_zero_iff_nonloop e he).2 (h e he),
    fun h e he ↦ (v.ne_zero_iff_nonloop e he).1 (h e he)⟩

theorem Rep.parallel_iff (v : M.Rep 𝔽 W) (he : M.Nonloop e) :
    M.Parallel e f ↔ ∃ (c : 𝔽), c ≠ 0 ∧ v e = c • v f := by
  obtain (hfE | hfE) := em' (f ∈ M.E)
  · refine iff_of_false (fun h ↦ hfE h.mem_ground_right) ?_
    simp [v.eq_zero_of_not_mem_ground hfE, iff_true_intro (v.ne_zero_of_nonloop he)]
  obtain (hf | hf) := M.loop_or_nonloop f
  · refine iff_of_false (fun h ↦ h.nonloop_right.not_loop hf) ?_
    simp [v.eq_zero_of_loop hf, iff_true_intro (v.ne_zero_of_nonloop he)]

  obtain (rfl | hef) := eq_or_ne e f
  · exact iff_of_true hf.parallel_self ⟨1, one_ne_zero, (one_smul _ _).symm⟩

  rw [he.parallel_iff_dep hf hef, ←not_indep_iff, v.indep_iff, not_iff_comm,
    linearIndependent_restrict_pair_iff _ hef (v.ne_zero_of_nonloop he)]
  simp only [ne_eq, not_exists, not_and]
  refine ⟨fun h c h' ↦ ?_, fun h c hc h_eq ↦
    h c⁻¹ (by rw [h_eq, smul_smul, inv_mul_cancel hc, one_smul])⟩
  have hc : c ≠ 0 := by rintro rfl; exact v.ne_zero_of_nonloop hf (by simp [←h'])
  exact h c⁻¹ (by simpa) <| by rw [←h', smul_smul, inv_mul_cancel hc, one_smul]

theorem Rep.simple_iff [RkPos M] (v : M.Rep 𝔽 W) :
    M.Simple ↔ ∀ {e f} (_ : e ∈ M.E) (_ : f ∈ M.E) (c : 𝔽), v e = c • (v f) → e = f := by
  simp_rw [simple_iff_loopless_eq_of_parallel_forall, v.loopless_iff]
  refine ⟨fun ⟨h0,h1⟩ e f he _ c h_eq ↦ h1 e f ?_, fun h ↦ ⟨fun e he h0 ↦ ?_, fun e f hef ↦ ?_⟩⟩
  · refine (v.parallel_iff ?_).2 ⟨c, ?_, h_eq⟩
    · rw [←v.ne_zero_iff_nonloop e]; exact h0 _ he
    rintro rfl
    exact h0 e he <| by simp [h_eq]
  · obtain ⟨f, hf⟩ := M.exists_nonloop
    obtain rfl := h he hf.mem_ground 0 (by simp [h0])
    exact v.ne_zero_of_nonloop hf h0
  obtain ⟨c,-,h_eq⟩ := (v.parallel_iff hef.symm.nonloop_right).1 hef
  exact h (by aesop_mat) (by aesop_mat) c h_eq

theorem Rep.injOn_of_simple (v : M.Rep 𝔽 W) (h : M.Simple) : InjOn v M.E := by
  obtain (hl | hpos) := M.eq_loopyOn_or_rkPos
  · rw [hl, simple_loopyOn_iff] at h; simp [h]
  exact fun e he f hf h_eq ↦ (v.simple_iff.1 h) he hf 1 <| by rwa [one_smul]

end Simple
section Uniform

/-- A uniform matroid on at most `|𝔽|+1` elements is `𝔽`-representable -/
theorem uniform_rep_of_le {a b : ℕ} {𝔽 : Type*} [Field 𝔽] (hb : b ≤ encard (univ : Set 𝔽) + 1) :
    Representable (unif a b) 𝔽 := by
  have hinj : Nonempty (Fin b ↪ (Option 𝔽))
  · refine ⟨Embedding.trans (Nonempty.some ?_) (Equiv.Set.univ (Option 𝔽)).toEmbedding⟩
    rw [Fin.nonempty_embedding_iff_le_encard]
    convert hb
    rw [encard_univ, PartENat.card_option, encard_univ]
    convert PartENat.withTopAddEquiv.map_add (PartENat.card 𝔽) 1
    exact (PartENat.withTopEquiv_natCast 1).symm
  obtain ⟨i,hi⟩ := hinj
  set A := Matrix.rectProjVandermonde i a
  exact IsRep.representable (v := A.rowFun)
    (fun I ↦ by rw [Matrix.rectProjVandermonde_rowSet_linearIndependent_iff hi, unif_indep_iff])

end Uniform

section Minor

/-- Contracting a set preserves representability. -/
def Rep.contract (v : M.Rep 𝔽 W) (C : Set α) : (M ⟋ C).Rep 𝔽 (W ⧸ (span 𝔽 (v '' C))) where
    to_fun := Submodule.Quotient.mk ∘ v
    valid' :=
  ( by
    intro J
    obtain ⟨I,hI⟩ := M.exists_basis' C
    rw [hI.contract_eq_contract_delete, delete_indep_iff, hI.indep.contract_indep_iff,
      (show Submodule.Quotient.mk = Submodule.mkQ _ by ext; rfl), union_comm, v.indep_iff,
      and_right_comm, ← disjoint_union_right, union_diff_self,
      union_eq_self_of_subset_left hI.subset]
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_,(v.indep_iff.1 hI.indep).union_index' ?_⟩⟩
    · refine (h.2.mono_index _ (subset_union_right _ _)).map ?_
      simp only [range_restrict, ker_mkQ, ← v.span_eq_span_of_cl_eq_cl hI.cl_eq_cl]
      convert h.2.disjoint_span_image (s := (↑) ⁻¹' J) (t := (↑) ⁻¹' I) ?_
      · rw [restrict_eq, image_comp, Subtype.image_preimage_coe,
          inter_comm, union_inter_cancel_right]
      · rw [restrict_eq, image_comp, Subtype.image_preimage_coe,
          inter_comm, union_inter_cancel_left]
      exact (h.1.mono_right hI.subset).preimage _
    · rw [disjoint_iff_forall_ne]
      rintro i hiJ _ hiI rfl
      apply h.ne_zero ⟨i, hiJ⟩
      simp only [Set.restrict_apply, comp_apply, mkQ_apply, Quotient.mk_eq_zero]
      exact subset_span (mem_image_of_mem _ hiI)
    rwa [v.span_eq_span_of_cl_eq_cl hI.cl_eq_cl] )

theorem Rep.delete (v : M.Rep 𝔽 W) (D : Set α) : (M ⟍ D).Rep 𝔽 W :=
  v.restrict (M.E \ D)

theorem Representable.minor {M N : Matroid α} (hM : M.Representable 𝔽) (hNM : N ≤m M) :
    N.Representable 𝔽 := by
  rw [minor_iff_exists_contract_delete] at hNM
  obtain ⟨C, D, rfl⟩ := hNM
  obtain ⟨v⟩ := hM
  exact ((v.contract C).delete D).representable

theorem minorClosed_representable (𝔽 : Type*) [Field 𝔽] :
    MinorClosed (fun M ↦ M.Representable 𝔽) := by
  intro α N M hNM (h : M.Representable 𝔽)
  exact h.minor hNM

theorem representable_isoMinorClosed (𝔽 : Type*) [Field 𝔽] :
    IsoMinorClosed (fun M ↦ M.Representable 𝔽) :=
  ⟨minorClosed_representable 𝔽, invariant_representable 𝔽⟩

end Minor

section Dual

variable {ι η 𝔽 : Type*} [Field 𝔽]

abbrev Rep.toMatrix {M : Matroid α} {η 𝔽 : Type*} [Field 𝔽] (v : M.Rep 𝔽 (η → 𝔽)) : Matrix η α 𝔽 :=
  (Matrix.of v)ᵀ

theorem Rep.colBasis_eq_base (v : M.Rep 𝔽 (η → 𝔽)) : v.toMatrix.ColBasis = M.Base := by
  ext B
  change _ ↔ B ∈ {B | M.Base B}
  simp_rw [setOf_base_eq_maximals_setOf_indep, colBasis_iff_maximal_linearIndependent, v.indep_iff]
  rfl


theorem eq_dual_of_rowSpace_eq_nullSpace_on_univ [Fintype α] {M N : Matroid α}
    (hM : M.E = univ) (hN : N.E = univ) (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : vM.toMatrix.rowSpace = vN.toMatrix.nullSpace) : N = M﹡ := by
  apply eq_of_base_iff_base_forall (by rw [hN, dual_ground, hM]) (fun B _ ↦ ?_)
  rw [← vN.colBasis_eq_base, dual_base_iff, ← vM.colBasis_eq_base, hM, ← compl_eq_univ_diff,
    colBasis_iff_colBasis_compl_of_orth h, compl_compl]

theorem eq_dual_of_rowSpace_eq_nullSpace {M N : Matroid α} {E : Set α} (hE : E.Finite)
    (hME : M.E = E) (hNE : N.E = E) (vM : M.Rep 𝔽 (ι → 𝔽)) (vN : N.Rep 𝔽 (η → 𝔽))
    (h : (vM.toMatrix.colSubmatrix E).rowSpace = (vN.toMatrix.colSubmatrix E).nullSpace) :
    N = M﹡ := by
  apply eq_of_onGround_eq hNE (by rwa [dual_ground])
  rw [← onGround_dual]
  have _ := hE.fintype
  have _ := (hNE.symm ▸ hE).fintype
  have _ := (hME.symm ▸ hE).fintype
  apply eq_dual_of_rowSpace_eq_nullSpace_on_univ (onGround_ground hME.symm.subset)
    (onGround_ground hNE.symm.subset) (vM.onGround' E) (vN.onGround' E)
  convert h
  exact hME

/-- The dual of a representable matroid is representable -/
theorem Representable.dual [M.Finite] (h : M.Representable 𝔽) : M﹡.Representable 𝔽 := by
  obtain ⟨v⟩ := h
  set ns : Submodule 𝔽 (M﹡.E → 𝔽) := (v.toMatrix.colSubmatrix M.E).nullSpace
  obtain b := Basis.ofVectorSpace 𝔽 ns
  have : Fintype M﹡.E := M.ground_finite.fintype
  set Mdrep := (matroidOfSubtypeFun_rep 𝔽 b.toRowMatrix.colFun)
  have Mdrep' := Mdrep.representable
  rwa [← eq_dual_of_rowSpace_eq_nullSpace (ground_finite M) rfl (by simp) v Mdrep]
  have hbs := b.toRowMatrix_rowSpace
  change _ = nullSpace _ at hbs
  rw [← orthSpace_nullSpace_eq_rowSpace, eq_comm, eq_orthSpace_comm,
    orthSpace_nullSpace_eq_rowSpace] at hbs
  rw [← hbs]
  apply congr_arg
  ext
  simp

@[simp] theorem dual_representable_iff [M.Finite] : M﹡.Representable 𝔽 ↔ M.Representable 𝔽 :=
  ⟨fun h ↦ dual_dual M ▸ h.dual, Representable.dual⟩


-- TODO  : if [I|A] represents M, then [Aᵀ|I] represents M﹡

end Dual

section Extension

variable [DecidableEq α]

noncomputable def Rep.addLoop (v : M.Rep 𝔽 W) (e : α) : (M.addLoop e).Rep 𝔽 W :=
  v.restrict (insert e M.E)

noncomputable def Rep.parallelExtend (v : M.Rep 𝔽 W) (e f : α) : (M.parallelExtend e f).Rep 𝔽 W :=
  (v.preimage (update id f e)).restrict (insert f M.E)

theorem Rep.parallelExtend_apply (v : M.Rep 𝔽 W) (e f : α) {x : α} (hx : x ≠ f) :
    v.parallelExtend e f x = v x := by
  rw [Rep.parallelExtend, Rep.restrict_apply, indicator, Rep.preimage_apply]
  simp only [mem_insert_iff, comp_apply, ne_eq]
  split_ifs with h
  · rw [update_noteq hx, id]
  rw [v.eq_zero_of_not_mem_ground (not_mem_subset (subset_insert _ _) h)]

@[simp] theorem Rep.parallelExtend_apply_same (v : M.Rep 𝔽 W) (e f : α) :
    v.parallelExtend e f f = v e := by
  rw [Rep.parallelExtend, Rep.restrict_apply, indicator, if_pos (mem_insert _ _)]
  simp

theorem Representable.parallelExtend (h : M.Representable 𝔽) (e f : α) :
    (M.parallelExtend e f).Representable 𝔽 :=
  (h.rep.parallelExtend e f).representable

/-- This doesn't actually need finiteness; constructing the obvious explicit
  representation for the series extension is TODO. -/
theorem Representable.seriesExtend [M.Finite] (v : M.Rep 𝔽 W) (e f : α) :
    (M.seriesExtend e f).Representable 𝔽 := by
  rw [← dual_representable_iff, seriesExtend_dual]
  apply Representable.parallelExtend
  exact v.representable.dual


end Extension
