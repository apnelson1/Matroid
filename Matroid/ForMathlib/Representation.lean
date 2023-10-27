import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Finrank

open Submodule Set Module

theorem LinearIndependent.exists_extend {K V ι : Type _} [DivisionRing K] [AddCommGroup V] 
    [Module K V] {f : ι → V} {s₀ t : Set ι} (hli : LinearIndependent (s₀.restrict f)) 
    (hst : s₀ ⊆ t) :
    ∃ s, s₀ ⊆ s ∧ s ⊆ t ∧ LinearIndependent (s.restrict f) ∧ span K (f '' s) = span K (f '' t) := by 
  

@[simp] theorem Module.piEquiv_apply_symm [Field 𝔽] [Fintype α] [DecidableEq α]
    (y : Module.Dual 𝔽 (α → 𝔽)) (i : α) :
    (Module.piEquiv α 𝔽 𝔽).symm y i = y (Pi.single i 1) := by
  simp only [piEquiv, Basis.constr, Pi.basisFun_apply, LinearMap.stdBasis_apply,
    LinearEquiv.coe_symm_mk]; rfl

@[simp]
theorem LinearEquiv.dualMap_apply_symm {R : Type u} [CommSemiring R] {M₁ : Type v} {M₂ : Type v'}
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] (f : M₁ ≃ₗ[R] M₂)
    (g : Module.Dual R M₁) : f.symm.dualMap g = g.comp (f.symm : M₂ →ₗ[R] M₁) := rfl

@[simp] theorem LinearEquiv.dualAnnihilator_map_eq {R : Type u} {M : Type v} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (e : M ≃ₗ[R] M')
    (U : Submodule R M) :
    dualAnnihilator (U.map e) = (dualAnnihilator U).map e.symm.dualMap :=  by
  ext x
  simp only [mem_dualAnnihilator, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    dualMap_apply_symm]
  refine ⟨fun h ↦ ⟨e.dualMap x, h, by ext; simp⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩ x hxu
  simpa using hy x hxu

theorem LinearEquiv.map_coe {R M₁ M₂ : Type _} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (e : M₁ ≃ₗ[R] M₂)
    (U : Submodule R M₁):
  U.map (e : M₁ →ₗ[R] M₂) = U.map e := rfl

@[simp] theorem LinearEquiv.map_trans {R M₁ M₂ M₃ : Type _} [CommSemiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁]
    [Module R M₂] [Module R M₃] (e₁₂ : M₁ ≃ₗ[R] M₂) (e₂₃ : M₂ ≃ₗ[R] M₃)
    (U : Submodule R M₁) :
    U.map (e₁₂.trans e₂₃) = (U.map e₁₂).map e₂₃ := by
  rw [←LinearEquiv.map_coe,  LinearEquiv.coe_trans, Submodule.map_comp]; rfl

/-- Unlike the unprimed version, `f` isn't coerced here, so the simplifier can find it. -/
@[simp] theorem LinearEquiv.finrank_map_eq' {R M M₂ : Type _} [Ring R] [AddCommGroup M]
    [AddCommGroup M₂] [Module R M] [Module R M₂] (f : M ≃ₗ[R] M₂) (p : Submodule R M) :
    FiniteDimensional.finrank R (p.map f) = FiniteDimensional.finrank R p :=
  finrank_map_eq f p

theorem linearIndependent_subtype_congr {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
  {s s' : Set M} (h_eq : s = s') :
    LinearIndependent R ((↑) : s → M) ↔ LinearIndependent R ((↑) : s' → M) := by
  subst h_eq; rfl

@[simp]
theorem Submodule.span_diff_zero {R : Type u_1} {M : Type u_4} [Semiring R] [AddCommMonoid M]
    [Module R M] {s : Set M} : Submodule.span R (s \ {0}) = Submodule.span R s := by
  simp [←Submodule.span_insert_zero]

theorem LinearIndependent.finite_index {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {f : α → V} (h : LinearIndependent K f) :
    _root_.Finite α :=
  Cardinal.lt_aleph0_iff_finite.1 <| FiniteDimensional.lt_aleph0_of_linearIndependent h

noncomputable def LinearIndependent.fintype_index {K : Type u} {V : Type v} [DivisionRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : α → V} (h : LinearIndependent K f) :
    Fintype α :=
  have _ := h.finite_index
  Fintype.ofFinite α
section coords

def LinearMap.fun_subtype (R : Type _) [Semiring R] (s : Set α) : (α → R) →ₗ[R] (s → R) :=
  LinearMap.funLeft R R Subtype.val

@[simp] theorem LinearMap.fun_subtype_apply (R : Type _) [Semiring R] (s : Set α) (x : α → R)
    (y : s) : LinearMap.fun_subtype R s x y = x y := rfl

def LinearMap.fun_subset (R : Type _) [Semiring R] {s t : Set α} (hst : s ⊆ t) :
    (t → R) →ₗ[R] (s → R) :=
  LinearMap.funLeft R R (Set.inclusion hst)

@[simp] theorem LinearMap.fun_subset_apply (R : Type _) [Semiring R] {s t : Set α} (hst : s ⊆ t)
    (f : t → R) (y : s) : LinearMap.fun_subset R hst f y = f (Set.inclusion hst y) := rfl

noncomputable def LinearMap.extend_subtype (R : Type _) [Semiring R] (s : Set α) :
    (s → R) →ₗ[R] (α → R)  :=
  Function.ExtendByZero.linearMap R Subtype.val

theorem Function.ExtendByZero.linearMap_injective (R : Type _) {ι η : Type _} [Semiring R]
  {s : ι → η} (hs : Function.Injective s) :
    LinearMap.ker (Function.ExtendByZero.linearMap R s) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro g (hg : _ = 0)
  ext i
  have h := congr_fun hg (s i)
  simp only [linearMap_apply, exists_apply_eq_apply, not_true, Pi.zero_apply] at h
  rw [Pi.zero_apply, ←h, hs.extend_apply]

@[simp] theorem LinearMap.extend_subtype_inj (R : Type _) [Semiring R] (s : Set α) :
    LinearMap.ker (LinearMap.extend_subtype R s) = ⊥ :=
  Function.ExtendByZero.linearMap_injective _ Subtype.coe_injective

@[simp] theorem LinearMap.extend_subtype_apply (R : Type _) [Semiring R] (s : Set α) (f : s → R)
    (y : s) : LinearMap.extend_subtype R s f y = f y := by
  rw [extend_subtype, Function.ExtendByZero.linearMap_apply, Subtype.coe_injective.extend_apply]

@[simp] theorem LinearMap.fun_subtype_extend_subtype (R : Type _) [Semiring R] (s : Set α) :
    (LinearMap.fun_subtype R s).comp (LinearMap.extend_subtype R s) = LinearMap.id := by
  ext; simp

noncomputable def LinearMap.extend_subset (R : Type _) [Semiring R] {s t : Set α} (hst : s ⊆ t) :
    (s → R) →ₗ[R] (t → R) := Function.ExtendByZero.linearMap R (Set.inclusion hst)

@[simp] theorem LinearMap.extend_subset_apply (R : Type _) [Semiring R] {s t : Set α} (hst : s ⊆ t)
    (f : s → R) (x : s) : LinearMap.extend_subset R hst f (Set.inclusion hst x) = f x := by
  rw [extend_subset, Function.ExtendByZero.linearMap_apply, (inclusion_injective hst).extend_apply]

theorem LinearMap.extend_subset_inj (R : Type _) [Semiring R] {s t : Set α} (hst : s ⊆ t) :
    LinearMap.ker (LinearMap.extend_subset R hst) = ⊥ :=
  Function.ExtendByZero.linearMap_injective _ <| inclusion_injective hst

theorem Module.dom_finite_of_finite (R : Type _) [DivisionRing R] (hfin : Module.Finite R (α → R)) :
    _root_.Finite α := by
  have := FiniteDimensional.of_injective (Finsupp.lcoeFun : (α →₀ R) →ₗ[R] (α → R))
    (fun f g h ↦ by ext x; simpa using congr_fun h x)
  exact Fintype.finite <| FiniteDimensional.fintypeBasisIndex
    (Finsupp.basisSingleOne : Basis α R (α →₀ R))

end coords

variable {α W W' R : Type _} [AddCommGroup W] [Field R] [Module R W] [AddCommGroup W'] [Module R W']

@[simp] theorem Basis.total_comp_repr (f : Basis α R W) (g : α → R) :
    ((Finsupp.total α R R g).comp f.repr.toLinearMap) ∘ f = g := by
  ext; simp

theorem linearIndependent_iff_forall_exists_eq_dual_comp {f : α → W} :
    LinearIndependent R f ↔ ∀ (g : α → R), ∃ (φ : Dual R W), φ ∘ f = g := by
  refine ⟨fun h g ↦ ?_, fun h ↦ linearIndependent_iff.2 fun l hl ↦ Finsupp.ext fun a ↦ ?_⟩
  · obtain ⟨i, hi⟩ := (span R (range f)).subtype.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (injective_subtype _))
    set ψ := (Finsupp.total α R R g).comp (Basis.span h).repr.toLinearMap with hψ
    refine ⟨ψ.comp i, funext fun a ↦ ?_⟩
    rw [←(Basis.span h).total_comp_repr g, ←hψ, Function.comp_apply, Function.comp_apply,
      ψ.coe_comp, Function.comp_apply]
    refine congr_arg _ <| Subtype.coe_injective ?_
    have hrw := LinearMap.congr_fun hi ⟨f a, subset_span (mem_range_self a)⟩
    simp only [LinearMap.coe_comp, coeSubtype, Function.comp_apply, LinearMap.id_coe, id_eq] at hrw
    simp only [hrw, Basis.span_apply]

  classical
  obtain ⟨φ, hφ⟩ := h <| Function.update 0 a (1 : R)
  have hc := φ.congr_arg hl
  rw [Finsupp.apply_total, hφ] at hc
  simpa [Finsupp.total_apply, Function.update_apply] using hc


-- theorem Fintype.linearIndependent_iff'' {ι R M : Type _} {v : ι → M} [Field R]
--     [AddCommGroup M] [Module R M] [Fintype ι] [FiniteDimensional R M] :
--     LinearIndependent R v ↔ ∀ φ : Module.Dual R M, φ ∘ v = 0 → φ = 0 := by
--   rw [Fintype.linearIndependent_iff]
--   refine ⟨fun h φ h0 ↦ ?_, fun h ↦ ?_⟩
--   · obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis R M
--     have : Fintype s := FiniteDimensional.fintypeBasisIndex b
--     have := b.sum_dual_apply_smul_coord φ
--     -- rw [← b.sum_dual_apply_smul_coord φ] at h0





 /-- For each function `f` to a module `W` over `r`, composition with `f` is a linear map from
  `Dual W` to `α → R` -/
def Submodule.dual_comp (f : α → W) (R : Type _) [CommSemiring R] [Module R W] :
    Dual R W →ₗ[R] (α → R) where
  toFun φ := φ ∘ f
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

@[simp] theorem Submodule.dual_comp_apply (f : α → W) (R : Type _) [CommSemiring R] [Module R W]
  (φ : Module.Dual R W) :
    Submodule.dual_comp f R φ = φ ∘ f := rfl

/-- Each function `f` to a module `W` gives a submodule obtained by composing each `φ ∈ Dual W`
  with f -/
def Submodule.ofFun (R : Type _) [CommSemiring R] [Module R W] (f : α → W) : Submodule R (α → R) :=
  LinearMap.range (dual_comp f R)

theorem Submodule.ofFun_map (f : α → W) (e : W →ₗ[R] W')
    (h_inj : Disjoint (span R (range f)) (LinearMap.ker e)) : ofFun R (e ∘ f) = ofFun R f := by
  ext w
  simp only [ofFun, dual_comp_apply, LinearMap.mem_range, LinearMap.coe_mk, AddHom.coe_mk]
  refine ⟨by rintro ⟨φ, _, rfl⟩; exact ⟨φ.comp e, rfl⟩, ?_⟩

  rintro ⟨φ, _, rfl⟩
  have hker : LinearMap.ker (LinearMap.domRestrict e (span R (range f))) = ⊥
  · rwa [LinearMap.ker_eq_bot, LinearMap.injective_domRestrict_iff, ←disjoint_iff]

  obtain ⟨einv, hinv⟩ := (e.domRestrict (span R (Set.range f))).exists_leftInverse_of_injective hker

  use φ.comp ((Submodule.subtype _).comp einv)
  ext x
  simp [(by simpa using LinearMap.congr_fun hinv ⟨f x, subset_span (by simp)⟩ : einv (e (f x)) = _)]

theorem Submodule.ofFun_map' (f : α → W) (e : W →ₗ[R] W') (h_inj : LinearMap.ker e = ⊥) :
    ofFun R (e ∘ f) = ofFun R f :=
  ofFun_map _ _ (by simp [h_inj])

@[simp] theorem Submodule.ofFun_map_equiv (f : α → W) (e : W ≃ₗ[R] W') :
    ofFun R (e ∘ f) = ofFun R f :=
  ofFun_map' _ _ e.ker

@[simp] theorem mem_ofFun_iff : x ∈ ofFun R f ↔ ∃ φ : Dual R W, φ ∘ f = x := Iff.rfl

theorem Submodule.ofFun_eq_top_iff (f : α → W) : ofFun R f = ⊤ ↔ LinearIndependent R f := by
  simp [linearIndependent_iff_forall_exists_eq_dual_comp, eq_top_iff']

theorem ofFun_comp_coe (f : α → W) (s : Set α) :
    ofFun R (f ∘ ((↑) : s → α)) = (ofFun R f).map (LinearMap.fun_subtype R s) := by
  ext; aesop

-- noncomputable def foo {f : α → W} (b : Basis ι R (span R (range f)))

def ofFun_repr (f : α → W) (b : Basis ι R W) : ι → ofFun R f :=
  fun i ↦ ⟨fun a ↦ (b.repr ∘ f) a i, ( by
        simp only [Function.comp_apply, mem_ofFun_iff]
        exact ⟨b.coord i, funext fun _ ↦ rfl⟩ ) ⟩

-- noncomputable def foo'' {f : α → (ι →₀ R)} (hf : span R (range f) = ⊤) :
--     Basis ι R (ofFun R f) :=
--   let v : ι → α → R := fun i a ↦ f a i
--   Basis.mk (v := (⟨v, sorry⟩ : ofFun R f))
--   ( by
--     simp [linearIndependent_iff]
--     intro c

--   ) sorry
--   -- Basis.mk (v := f) sorry sorry



-- noncomputable def foo' {f : α → W} (b : Basis ι R W) :
--   Basis ι R (ofFun R f) :=
--   let v : ι → ofFun R f :=
--     fun i ↦ ⟨fun a ↦ (b.repr ∘ f) a i, ( by
--         simp only [Function.comp_apply, mem_ofFun_iff]
--         exact ⟨b.coord i, funext fun _ ↦ rfl⟩ ) ⟩

--   Basis.mk (v := v)

--     ( by
--       simp only [linearIndependent_iff]

--       intro l h


--       use g
--     )
--     sorry


-- Inverses


  -- _

/-- For every `ι`-indexed basis of a subspace `U` of `α → R`, there is a canonical
  `f : α → (ι → R)` for which `U = ofFun R f`. I think this breaks if `U` isn't
    finite-dimensional -/
theorem Basis.eq_ofFun {U : Submodule R (α → R)} [FiniteDimensional R U] (b : Basis ι R U) :
    ofFun R (fun a i ↦ (b i).1 a) = U := by
  have _ := FiniteDimensional.fintypeBasisIndex b
  ext x
  rw [mem_ofFun_iff]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨φ, rfl⟩
    set φ' : ι → R := (piEquiv ι R R).symm φ  with hφ'
    convert (b.equivFun.symm φ').prop
    ext x
    rw [Function.comp_apply, (piEquiv ι R R).symm_apply_eq.1 hφ', piEquiv_apply_apply]
    simp only [Basis.equivFun_symm_apply, AddSubmonoid.coe_finset_sum,
      coe_toAddSubmonoid, Finset.sum_apply]
    exact Finset.sum_congr rfl fun y _ ↦ mul_comm _ _
  use (piEquiv ι R R) <| b.equivFun ⟨x, h⟩
  ext i
  simp only [Basis.equivFun_apply, Function.comp_apply, piEquiv_apply_apply]
  convert congr_fun (congr_arg Subtype.val (b.sum_repr ⟨x, h⟩)) i
  simp only [smul_eq_mul, AddSubmonoid.coe_finset_sum, coe_toAddSubmonoid, SetLike.val_smul,
    Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl  fun y _ ↦ mul_comm _ _

theorem linearIndependent_of_finite_index {R M ι : Type _} [Field R] [AddCommGroup M]
    [Module R M] (f : ι → M) (h : ∀ (t : Set ι), t.Finite → LinearIndependent R (t.restrict f)) :
    LinearIndependent R f := by
  have hinj : f.Injective
  · intro x y hxy
    have hli := (h {x,y} (toFinite _))
    have h : (⟨x, by simp⟩ : ({x,y} : Set ι)) = ⟨y, by simp⟩
    · rw [←hli.injective.eq_iff]; simpa
    simpa using h

  rw [←linearIndependent_subtype_range hinj]
  refine linearIndependent_of_finite _ fun t ht htfin ↦ ?_
  obtain ⟨t, rfl⟩ := subset_range_iff_exists_image_eq.1 ht
  exact (linearIndependent_image (injOn_of_injective hinj t)).1 <|
    h t (htfin.of_finite_image (injOn_of_injective hinj t))

-- noncomputable def Basis.mk_submodule {ι R M : Type _} {v : ι → M} [Ring R] [AddCommGroup M]
--   [Module R M]
--   (hli : LinearIndependent R v) (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
-- Basis ι R M

-- Todo; the span of the range of f and (ofFun f) should have the same dimension. I don't know if
-- there is a natural map from bases of one to the other, though.

-- theorem foo1 (f : α → R) (hf : Module.Finite R (ofFun R f)) : Module.Finite R (span R (range f))
--   := by
--   sorry


-- def exists_basis (f : α → W) :
--     ∃ (I : Set α) (b : Basis I R (span R (range f))), ∀ i, (b i : W) = f (i : α) := by
--   obtain ⟨I, (hI : LinearIndependent R (I.restrict f)), hmax⟩ := exists_maximal_independent' R f
--   have hsp : span R (range (I.restrict f)) = span R (range f)
--   · refine le_antisymm (span_mono ?_) ?_
--     · rw [range_restrict]; apply image_subset_range
--     refine fun x hx ↦ by_contra fun hx' ↦ ?_

--     -- have :+ linearIndependent

--   have hss : ∀ a, f a ∈ span R (range (I.restrict f))
--   · intro a; rw [hsp]; exact subset_span (mem_range_self _)
--   have hi := (linearIndependent_span hI)
--   refine ⟨I, (Basis.mk hi ?_).map (LinearEquiv.ofEq _ _ hsp), fun i ↦ by simp⟩

--   simp_rw [←Submodule.map_le_map_iff_of_injective (injective_subtype _),
--     Submodule.map_top, range_subtype, range_restrict, restrict_apply, Submodule.map_span]
--   apply span_mono
--   rintro _ ⟨x, hx, rfl⟩
--   simp only [coeSubtype, mem_image, mem_range, Subtype.exists, Subtype.mk.injEq, exists_prop,
--     range_restrict, exists_and_left, exists_exists_and_eq_and]
--   exact ⟨f x, subset_span <| mem_image_of_mem _ hx, ⟨_, hx, rfl⟩, rfl⟩






  -- rw [←Submodule.map_le_map_iff_of_injective (M := span R (range (I.restrict f))) (f := Submodule.subtype) sorry ⊤ (span R _)]
  -- rw [top_le_iff, eq_top_iff']
  -- rintro ⟨x,hx⟩
  -- rw [Submodule.mem_span] at *
  -- intro P hP
  -- have := image_subset_image (Submodule.subtype) hP


  -- rw [mem_span_set] at *
  -- obtain ⟨c, hc, rfl⟩:= hx
  -- use fun x ↦ c x





  -- ·


-- theorem rank_of_fun (f : α → R) (hf : Module.Finite R (span R (range f))) :
--     FiniteDimensional.finrank R (ofFun R f) = FiniteDimensional.finrank R (span R (range f)) := by
--     sorry
  -- have : ∃ I : Set α, Nonempty (Basis I R (span R (range f)))

  -- have : Basis _ R (span R (range f)) := by exact?
--   ·

-- theorem Basis.foo {U : Submodule R (α → R)} [FiniteDimensional R U] (b : Basis ι R U) :
--     span R (range (fun a i ↦ (b i).1 a)) = ⊤ := by
--   _
