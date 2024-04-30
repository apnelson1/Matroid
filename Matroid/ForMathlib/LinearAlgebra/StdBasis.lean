
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dual
import Matroid.ForMathlib.LinearAlgebra.FiniteDimensional
import Matroid.ForMathlib.LinearAlgebra.Dual
import Matroid.ForMathlib.Other

variable {α R η ι : Type*}

open Set BigOperators Submodule Function

@[simp] theorem Fintype.sum_pi_single {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [(a : α) → AddCommMonoid (β a)] (a : α) (f : (a : α) → β a) :
    ∑ a', Pi.single a' (f a') a = f a := by
  convert Finset.sum_pi_single a f Finset.univ; simp

@[simp] theorem Module.piEquiv_apply_symm [CommSemiring R] [Fintype α] [DecidableEq α]
    (y : Module.Dual R (α → R)) (i : α) : (Module.piEquiv α R R).symm y i = y (Pi.single i 1) := by
  simp only [piEquiv, Basis.constr, Pi.basisFun_apply, LinearMap.stdBasis_apply,
    LinearEquiv.coe_symm_mk]; rfl

@[simp] theorem Module.Dual.sum_update [Field R] [Fintype α] [DecidableEq α]
  (y : Module.Dual R (α → R)) (x : α → R) : ∑ i, y (Function.update 0 i 1) * x i = y x := by
  rw [← LinearMap.congr_fun ((Pi.basisFun R α).sum_dual_apply_smul_coord y) x]
  simp [LinearMap.stdBasis_apply]

@[simp] theorem Module.Dual.sum_pi_single [Field R] [Fintype α] [DecidableEq α]
  (y : Module.Dual R (α → R)) (x : α → R) : ∑ i, y (Pi.single i 1) * x i = y x :=
  Module.Dual.sum_update y x

-- theorem ExtendByZero.linearMap_incl_eq {R : Type*} [Semiring R] (s : Set η) (x : s → R) (i : η)
--   [Decidable (i ∈ s)] :
--     ExtendByZero.linearMap R s.incl x i = if h : i ∈ s then x ⟨i,h⟩ else 0 := by
--   split_ifs
--   simp



section extend

variable {R : Type*} [Semiring R] {s : Set α}

noncomputable def LinearMap.extendSubtype (R : Type*) [Semiring R] (s : Set α) :
    (s → R) →ₗ[R] (α → R)  :=
  Function.ExtendByZero.linearMap R s.incl

theorem Function.ExtendByZero.linearMap_injective (R : Type*) {ι η : Type _} [Semiring R]
  {s : ι → η} (hs : Function.Injective s) :
    Injective <| Function.ExtendByZero.linearMap R s := by
  intro x x' h
  ext i
  replace h := _root_.congr_fun h (s i)
  simp only [linearMap_apply, exists_apply_eq_apply, not_true] at h
  rwa [hs.extend_apply, hs.extend_apply] at h

@[simp] theorem LinearMap.extendSubtype_inj (R : Type*) [Semiring R] (s : Set α) :
    Injective <| LinearMap.extendSubtype R s :=
  Function.ExtendByZero.linearMap_injective _ Subtype.coe_injective

@[simp] theorem LinearMap.extendSubtype_apply {R : Type*} [Semiring R] {s : Set α} (f : s → R)
    (y : s) : LinearMap.extendSubtype R s f y = f y := by
  rw [extendSubtype, Function.ExtendByZero.linearMap_apply, Subtype.coe_injective.extend_apply]

theorem LinearMap.extendSubtype_apply_not_mem {R : Type*} [Semiring R] {s : Set α} (f : s → R)
    {i : α} (hi : i ∉ s) : LinearMap.extendSubtype R s f i = 0 := by
  rw [extendSubtype, ExtendByZero.linearMap_apply, extend_apply', Pi.zero_apply]
  rintro ⟨a, rfl⟩
  exact hi a.2

theorem LinearMap.extendSubtype_eq_ite {R : Type*} [Semiring R] (s : Set η) (x : s → R)
  [DecidablePred (· ∈ s)] :
    LinearMap.extendSubtype R s x = fun i ↦ if h : i ∈ s then x ⟨i,h⟩ else 0 := by
  ext i
  split_ifs with h
  · exact extendSubtype_apply x ⟨i,h⟩
  simp only [extendSubtype._eq_1, ExtendByZero.linearMap_apply, Subtype.exists, not_exists]
  rw [extend_apply', Pi.zero_apply]
  rintro ⟨a,rfl⟩
  exact h a.2

@[simp] theorem LinearMap.extendSubtype_restrict (x : s → R) :
    s.restrict (LinearMap.extendSubtype R s x) = x := by
  ext; simp

theorem LinearMap.extendSubtype_support_subset (x : s → R) :
    support (LinearMap.extendSubtype R s x) ⊆ s := by
  classical
  refine fun i (hi : _ ≠ 0) ↦ by_contra fun his ↦ ?_
  simp_rw [LinearMap.extendSubtype_eq_ite, dif_neg his] at hi
  exact hi rfl

def LinearMap.funSubtype (R : Type*) [Semiring R] (s : Set α) : (α → R) →ₗ[R] (s → R) :=
  LinearMap.funLeft R R Subtype.val

@[simp] theorem LinearMap.fun_Subtype_apply (R : Type*) [Semiring R] (s : Set α) (x : α → R)
    (y : s) : LinearMap.funSubtype R s x y = x y := rfl

@[simp] theorem LinearMap.funSubtype_extendSubtype (R : Type*) [Semiring R] (s : Set α) :
    (LinearMap.funSubtype R s).comp (LinearMap.extendSubtype R s) = LinearMap.id := by
  ext; simp

@[simp] theorem LinearMap.funSubtype_extendSubtype_apply (R : Type*) [Semiring R] (s : Set α)
  (x : s → R) :
    (LinearMap.funSubtype R s) ((LinearMap.extendSubtype R s) x) = x := by
  ext; simp

theorem LinearMap.extendSubtype_funSubtype_apply {R : Type*} [Semiring R] {s : Set η} {x : η → R}
  (hx : support x ⊆ s) :
    (LinearMap.extendSubtype R s) ((LinearMap.funSubtype R s) x) = x := by
  classical
  ext i
  simp only [extendSubtype_eq_ite, fun_Subtype_apply, dite_eq_ite, ite_eq_left_iff]
  exact fun his ↦ Eq.symm <| by simpa using mt (support_subset_iff.1 hx i) his

noncomputable def LinearMap.extendSubset (R : Type*) [Semiring R] {s t : Set α} (hst : s ⊆ t) :
    (s → R) →ₗ[R] (t → R) := Function.ExtendByZero.linearMap R (Set.inclusion hst)

@[simp] theorem LinearMap.extendSubset_apply (R : Type*) [Semiring R] {s t : Set α} (hst : s ⊆ t)
    (f : s → R) (x : s) : LinearMap.extendSubset R hst f (Set.inclusion hst x) = f x := by
  rw [extendSubset, Function.ExtendByZero.linearMap_apply, (inclusion_injective hst).extend_apply]

theorem LinearMap.extend_subset_inj (R : Type*) [Semiring R] {s t : Set α} (hst : s ⊆ t) :
    Injective (LinearMap.extendSubset R hst) :=
  Function.ExtendByZero.linearMap_injective _ <| inclusion_injective hst




end extend


section supportedFun

variable {R η : Type*} [Semiring R] {s : Set η} {x : η → R}

/-- The submodule of vectors in `η → R` with support contained in some `s : Set η`. -/
noncomputable def Set.supportedFun (s : Set η)  (R : Type*) [Semiring R] : Submodule R (η → R) :=
  LinearMap.range <| LinearMap.extendSubtype R s

@[simp] theorem mem_supportedFun_iff : x ∈ s.supportedFun R ↔ x.support ⊆ s := by
  classical
  simp only [supportedFun, LinearMap.mem_range, ne_eq]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨y, rfl⟩ i hi
    simp only [mem_support, ne_eq, LinearMap.extendSubtype_eq_ite, dite_eq_right_iff,
      not_forall] at hi
    obtain ⟨h,-⟩ := hi
    exact h
  exact ⟨LinearMap.funSubtype R s x, LinearMap.extendSubtype_funSubtype_apply h⟩

@[simp] theorem supportedFun_univ (R η : Type*) [Semiring R] :
    (univ : Set η).supportedFun R = ⊤ := by
  ext; simp

@[simp] theorem supportedFun_empty (R η : Type*) [Semiring R] :
    (∅ : Set η).supportedFun R = ⊥ := by
  ext x;
  simp only [mem_supportedFun_iff, support_subset_iff, ne_eq, mem_empty_iff_false, mem_bot,
    imp_false, not_not]
  exact Iff.symm funext_iff

/-- `s.supportedFun R` is equivalent to `s → R` -/
noncomputable def Set.supportedFunEquiv (s : Set η) (R : Type*) [Semiring R] :
    (s → R) ≃ₗ[R] s.supportedFun R  :=
  LinearEquiv.ofInjective _ (LinearMap.extendSubtype_inj R s)

@[simp] theorem Set.supportedFunEquiv_apply (s : Set η) (R : Type*) [Semiring R] (x : s → R) :
    s.supportedFunEquiv R x = LinearMap.extendSubtype R s x := rfl

@[simp] theorem Set.supportedFunEquiv_apply_symm (s : Set η) (R : Type*) [Semiring R]
    (x : s.supportedFun R) :
    (s.supportedFunEquiv R).symm x = LinearMap.funSubtype R s x := by
  classical
  obtain ⟨x, hx⟩ := x
  rw [(s.supportedFunEquiv R).symm_apply_eq]
  ext i
  simp only [supportedFunEquiv_apply, LinearMap.extendSubtype_eq_ite, LinearMap.fun_Subtype_apply,
    dite_eq_ite]
  rw [eq_comm, ite_eq_left_iff, not_imp_comm, eq_comm]
  rw [mem_supportedFun_iff, support_subset_iff] at hx
  apply hx

@[simp] theorem Submodule.MapSubtype.relIso_apply {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) (U : Submodule R p) :
    (MapSubtype.relIso p U).1 = U.map p.subtype := rfl

@[simp] theorem Submodule.MapSubtype.relIso_apply_mem {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) (U : Submodule R p) (x : M):
    x ∈ (MapSubtype.relIso p U).1 ↔ x ∈ U.map p.subtype := Iff.rfl

@[simp] theorem Submodule.MapSubtype.relIso_apply_symm {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) (U : {U // U ≤ p}):
    (MapSubtype.relIso p).symm U = U.1.comap p.subtype := rfl

/-- For a set `s` in `η`, submodules of `s → R` are equivalent to submodules of `η → R`
  whose members are supported on `s` -/
noncomputable def Set.subtypeFunEquiv (s : Set η) (R : Type*) [Semiring R] :
    Submodule R (s → R) ≃o {U : Submodule R (η → R) // U ≤ s.supportedFun R} :=
  (orderIsoMapComap <| LinearEquiv.ofInjective _ (LinearMap.extendSubtype_inj R s)).trans
    (MapSubtype.relIso (LinearMap.range <| LinearMap.extendSubtype R s))

set_option pp.proofs.withType false

@[simp] theorem Set.mem_subtypeFunEquiv_iff {U : Submodule R (s → R)} :
    x ∈ (s.subtypeFunEquiv R U).1 ↔ x.support ⊆ s ∧ s.restrict x ∈ U := by
  classical
  change (x ∈ (MapSubtype.relIso _ _).1 ↔ _)
  simp only [RelIso.coe_fn_toEquiv, orderIsoMapComap_apply, MapSubtype.relIso_apply, mem_map,
    coeSubtype, exists_exists_and_eq_and, LinearEquiv.ofInjective_apply, support_subset_iff,
    LinearMap.extendSubtype_eq_ite]
  refine ⟨?_, fun ⟨hxs, hxU⟩ ↦ ?_⟩
  · rintro ⟨a, ha, rfl⟩
    constructor
    · simp only [ne_eq, dite_eq_right_iff, not_forall, forall_exists_index]
      exact fun i hi _ ↦ hi
    convert ha; ext; simp
  refine ⟨_, hxU, ?_⟩
  ext i
  simp_rw [restrict_apply, dite_eq_ite, ite_eq_left_iff, eq_comm (b := x i)]
  rw [not_imp_comm]
  apply hxs

@[simp] theorem Set.mem_subtypeFunEquivSymm_iff
    {U : {U : Submodule R (η → R) // U ≤ s.supportedFun R}} {x : s → R} :
    x ∈ (s.subtypeFunEquiv R).symm U ↔ LinearMap.extendSubtype R s x ∈ U.1 := Iff.rfl


end supportedFun

section orthSpace

variable {η : Type*} [CommRing R] {x : η → R} {U V : Submodule R (η → R)}

/-- `(l : η →₀ R)` gives rise canonically to a functional on `η → R` via `Finsupp.total`. -/
noncomputable def Finsupp.toDual (l : η →₀ R) : Module.Dual R (η → R) where
  toFun := fun x ↦ Finsupp.total _ _ _ x l
  map_add' := fun _ _ ↦ by simp [Finsupp.total, Finsupp.sum, mul_add, Finset.sum_add_distrib]
  map_smul' := fun c x ↦ by
    simp [Finsupp.total, Finsupp.sum, Finset.mul_sum, ← mul_assoc, mul_comm _ c]

@[simp] theorem Finsupp.toDual_apply (l : η →₀ R) (x : η → R) :
    l.toDual x = Finsupp.total _ _ _ x l := rfl

noncomputable def Finsupp.toDualLin (η R : Type*) [CommRing R] :
    (η →₀ R) →ₗ[R] Module.Dual R (η → R) where
  toFun := Finsupp.toDual
  map_add' := fun _ _ ↦ by ext; simp
  map_smul' := fun _ _ ↦ by ext; simp

@[simp] theorem Finsupp.toDualLin_coe (η R : Type*) [CommRing R] (l : η →₀ R) :
    toDualLin η R l = Finsupp.toDual l := rfl

-- noncomputable def Finsupp.biLin (η R : Type*) [CommRing R] : BilinForm R (η →₀ R) where
--   bilin := fun x y ↦ Finsupp.total _ _ _ x y
--   bilin_add_left := fun _ _ _ ↦ by simp [Finsupp.total_apply, Finsupp.sum, mul_add,
--     Finset.sum_add_distrib]
--   bilin_smul_left := fun c y z ↦ by
--     simp_rw [coe_smul, total_apply, Finsupp.sum, Finset.mul_sum]
--     refine Finset.sum_congr rfl fun x _ ↦ ?_
--     rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm c, mul_assoc]
--     rfl
--   bilin_add_right := by simp
--   bilin_smul_right := by simp

noncomputable def Submodule.orthSpace' (U : Submodule R (η → R)) : Submodule R (η →₀ R) :=
  (Submodule.dualAnnihilator U).comap (Finsupp.toDualLin η R)

@[simp] theorem mem_orthSpace'_iff {U : Submodule R (η → R)} {l : η →₀ R} :
    l ∈ U.orthSpace' ↔ ∀ x ∈ U, Finsupp.total _ _ _ x l = 0 := by
  simp [orthSpace']

/-- The space of vectors 'orthogonal' to all vectors in `U`, in the sense of having a
  dot product of zero. This doesn't require `Fintype η`;
  its members are always finitely supported. -/
noncomputable def Submodule.orthSpace (U : Submodule R (η → R)) := U.orthSpace'.map Finsupp.lcoeFun

@[simp] theorem mem_orthSpace_iff' [Fintype η] : x ∈ U.orthSpace ↔ ∀ y ∈ U, ∑ i, x i * y i = 0 := by
  classical
  simp only [orthSpace, orthSpace', mem_map, mem_comap, Finsupp.toDualLin_coe, mem_dualAnnihilator,
    Finsupp.toDual_apply, Finsupp.total_apply, Finsupp.sum, smul_eq_mul]
  refine ⟨fun h y hyU ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨c, hc, rfl⟩ := h
    simp only [Finsupp.lcoeFun_apply]
    convert hc y hyU using 1
    rw [eq_comm, Finset.sum_subset (Finset.subset_univ _)]
    simp only [Finset.mem_univ, Finsupp.mem_support_iff, ne_eq, not_not, forall_true_left]
    exact fun x hx ↦ by simp [hx]
  refine ⟨Finsupp.equivFunOnFinite.2 x, fun w hw ↦ ?_, by ext; simp⟩
  convert h w hw using 1
  simp only [Equiv.invFun_as_coe, Finsupp.equivFunOnFinite_symm_apply_support,
    Finite.toFinset_setOf, ne_eq, Finset.mem_univ, forall_true_left, not_not,
    Finsupp.equivFunOnFinite_symm_apply_toFun]
  apply Finset.sum_subset (Finset.subset_univ _)
  simp only [Finset.mem_univ, forall_true_left, not_not, Finset.mem_filter, true_and]
  exact fun x hx ↦ by simp [hx]

@[simp] theorem mem_orthSpace_iff [Fintype η] :
    x ∈ U.orthSpace ↔ ∀ y ∈ U, Matrix.dotProduct x y = 0 :=
  mem_orthSpace_iff'


theorem mem_orthSpace_iff'' {U : Submodule R (ι → R)} {w : ι → R}:
    w ∈ U.orthSpace ↔ ∃ (l : ι →₀ R), l = w ∧ ∀ y ∈ U, Finsupp.total _ _ _ y l = 0 := by
  simp_rw [orthSpace, mem_map, mem_orthSpace'_iff]
  aesop

theorem orthSpace_eq [Fintype η] (U : Submodule R (η → R)) :
    U.orthSpace = U.dualAnnihilator.map (Module.piEquiv η R R).symm := by
  classical
  ext x
  simp only [mem_orthSpace_iff', mem_map, mem_dualAnnihilator]
  refine ⟨fun h ↦ ⟨Module.piEquiv η R R x, ?_, by simp⟩, fun h ↦ ?_⟩
  · simpa [Module.piEquiv_apply_apply, h, mul_comm]
  obtain ⟨w, h, rfl⟩ := h
  intro y hy
  convert h y hy using 1
  simp [Module.piEquiv_apply_symm]
  convert DFunLike.congr_fun ((Pi.basisFun R η).sum_dual_apply_smul_coord w) y using 1
  simp only [Pi.basisFun_apply, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
    Basis.coord_apply, Pi.basisFun_repr, smul_eq_mul]
  rfl

variable {K : Type*} [Field K] [Fintype η] {U V : Subspace K (η → K)}

@[simp] theorem orthSpace_orthSpace (U : Subspace K (η → K)) : U.orthSpace.orthSpace = U := by
  classical
  refine (FiniteDimensional.eq_of_le_of_finrank_le (fun x hxU ↦ ?_) (le_of_eq ?_)).symm
  · simp_rw [mem_orthSpace_iff']
    intro y hy
    simpa [mul_comm] using hy x hxU

  rw [orthSpace_eq, orthSpace_eq, LinearEquiv.finrank_map_eq', LinearEquiv.dualAnnihilator_map_eq,
    LinearEquiv.finrank_map_eq', ← Subspace.finrank_dualCoannihilator_eq,
    Subspace.dualAnnihilator_dualCoannihilator_eq]

theorem orthSpace_injective (η K : Type*) [Fintype η] [Field K] :
    Injective (Submodule.orthSpace : Subspace K (η → K) → Subspace K (η → K)) :=
  fun U U' h ↦ by simpa using congr_arg Submodule.orthSpace h

theorem eq_orthSpace_comm : U = V.orthSpace ↔ V = U.orthSpace :=
  ⟨fun h ↦ by rw [h, orthSpace_orthSpace], fun h ↦ by rw [h, orthSpace_orthSpace]⟩

@[simp] theorem orthSpace_bot : (⊥ : Subspace K (η → K)).orthSpace = ⊤ :=
  by rw [orthSpace_eq]; simp

@[simp] theorem orthSpace_top : (⊤ : Subspace K (η → K)).orthSpace = ⊥ := by
  rw [orthSpace_eq]; simp

/-- Orthogonal spaces gives an isomorphism from the subspace lattice to its order dual -/
noncomputable def orthSpace_orderIso (η K : Type*) [Fintype η] [Field K] :
  Subspace K (η → K) ≃o (Subspace K (η → K))ᵒᵈ where
    toFun := orthSpace
    invFun := orthSpace
    left_inv := orthSpace_orthSpace
    right_inv := orthSpace_orthSpace
    map_rel_iff' := (by
      refine fun {U} {V} ↦ ⟨fun (h : V.orthSpace ≤ U.orthSpace) x hx ↦ ?_,
        fun h ↦ fun x hx ↦ mem_orthSpace_iff.2 fun y hyU ↦ mem_orthSpace_iff.1 hx y <| h hyU⟩
      rw [← orthSpace_orthSpace V, mem_orthSpace_iff]
      intro y hy
      have hdp := (mem_orthSpace_iff.1 <| h hy) _ hx
      rwa [Matrix.dotProduct_comm] at hdp )

theorem orthSpace_strictAnti (η K : Type*) [Fintype η] [Field K] :
    StrictAnti (Submodule.orthSpace : Subspace K (η → K) → Subspace K (η → K)) :=
  (orthSpace_orderIso η K).strictMono

theorem orthSpace_le_iff_le : V.orthSpace ≤ U.orthSpace ↔ U ≤ V :=
  (orthSpace_orderIso η K).le_iff_le

theorem orthSpace_lt_iff_lt : V.orthSpace < U.orthSpace ↔ U < V :=
  (orthSpace_orderIso η K).lt_iff_lt


-- theorem mem_relOrthSpace_iff (hs : s.Finite) {x : ι → K} {U : Subspace K (ι → K)}:
--     x ∈ s.relOrthSpace U ↔ x.support ⊆ s ∧ ∀ y ∈ U, ∑ i : hs.toFinset, x i * y i = 0 := by
--   have _ := hs.fintype
--   rw [relOrthSpace, mem_inf]

-- theorem relOrthSpace_relOrthSpace {U : Subspace K (η → K)} {s : Set η} (hU : U ≤ s.supportedFun K) :
--     s.relOrthSpace (s.relOrthSpace U) = U := by

--   -- rw [relOrthSpace, relOrthSpace]



end orthSpace

section relOrthSpace

variable {R K η ι : Type*} [CommRing R] [Field K] [Fintype η]

/-- The subspace of vectors in `U.orthSpace` with support contained in `s`. -/
def Set.relOrthSpace (s : Set ι) (U : Submodule R (ι → R)) : Submodule R (ι → R) :=
    U.orthSpace ⊓ (s.supportedFun R)

theorem Set.mem_relOrthSpace_iff {s : Set ι} {U : Submodule R (ι → R)} {w : ι → R}:
    w ∈ s.relOrthSpace U ↔
      ∃ (l : Finsupp.supported R R s), l = w ∧ ∀ x ∈ U, Finsupp.total _ _ _ x l.1 = 0 := by
  rw [relOrthSpace, mem_inf, mem_orthSpace_iff'', mem_supportedFun_iff]
  constructor
  · rintro ⟨⟨l, rfl, hl⟩, hsupp⟩
    exact ⟨⟨l, by simpa using hsupp⟩, by simpa⟩
  rintro ⟨l, rfl, hl⟩
  refine ⟨⟨l, rfl, hl⟩, ?_⟩
  rw [Finsupp.fun_support_eq]
  exact l.2

theorem Set.relOrthSpace_subtypeFunEquiv (s : Set ι) (U : Submodule K (s → K)) :
    s.relOrthSpace (s.subtypeFunEquiv K U).1 = s.subtypeFunEquiv K U.orthSpace := by
  ext x
  simp_rw [mem_relOrthSpace_iff, mem_subtypeFunEquiv_iff, mem_orthSpace_iff'']
  refine ⟨?_, fun ⟨hsupp, l, hlrs, hl⟩ ↦ ?_⟩
  · rintro ⟨l, rfl, h⟩
    rw [Finsupp.fun_support_eq]
    refine ⟨l.2, Finsupp.restrictSupportEquiv s _ l, ?_, fun y hy ↦ ?_⟩
    · ext; simp [Finsupp.restrictSupportEquiv]
    specialize h (LinearMap.extendSubtype K s y)
    simp only [LinearMap.extendSubtype_restrict, hy, and_true,
      LinearMap.extendSubtype_support_subset, forall_true_left] at h
    convert h
    simp only [Finsupp.restrictSupportEquiv, Equiv.coe_fn_mk, Finsupp.total_apply, Finsupp.sum,
      Finsupp.subtypeDomain_apply, smul_eq_mul]
    convert (Finset.sum_map _ (Embedding.subtype (· ∈ s)) _).symm
    · simp only [Embedding.coe_subtype, LinearMap.extendSubtype_apply]
    ext i
    simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_map, Finsupp.subtypeDomain_apply,
      Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right,
      iff_self_and]
    rw [not_imp_comm]
    exact (Finsupp.mem_supported' _ _).1 l.2 _
  refine ⟨⟨Finsupp.mapDomain s.incl l, ?_⟩, ?_, ?_⟩
  · rw [Finsupp.mem_supported']
    intro i hi
    rw [Finsupp.mapDomain_notin_range _ _ (by simpa)]
  · ext i
    simp only
    obtain (his | his) := em (i ∈ s)
    · convert Finsupp.mapDomain_apply Subtype.val_injective l ⟨i,his⟩
      simp [hlrs]
    rw [Finsupp.mapDomain_notin_range, eq_comm]
    · simpa using not_mem_subset hsupp his
    simpa
  simp only [Finsupp.total_mapDomain, and_imp]
  exact fun _ _ hyU ↦ hl _ hyU

-- theorem Set.Finite.mem_relOrthSpace_iff {s : Set ι} (hs : s.Finite) {U : Submodule K (ι → K)} :
--     x ∈ s.relOrthSpace U ↔
--       ∃ (hsupp : support x ⊆ s), ∀ y ∈ U, ∑ i in (hs.subset hsupp).toFinset, x i * y i = 0 := by
--   rw [s.mem_relOrthSpace_iff]
--   sorry
--   -- this should be ok to prove

theorem Set.Finite.relOrthSpace_relOrthSpace {s : Set ι} (hs : s.Finite) (U : Submodule K (ι → K))
    (hU : U ≤ s.supportedFun K) : s.relOrthSpace (s.relOrthSpace U) = U := by
  set U' : {U : Submodule K (ι → K) // U ≤ s.supportedFun K} := ⟨U,hU⟩
  have := hs.fintype
  rw [(show U = U' from rfl), ← Subtype.val_inj.2 <| (s.subtypeFunEquiv K).apply_symm_apply U',
    s.relOrthSpace_subtypeFunEquiv, s.relOrthSpace_subtypeFunEquiv, orthSpace_orthSpace]



-- theorem mem_relOrthSpace_iff_exists_finsupp (s : Set ι) (U : Submodule R (ι → R)) :
--     x ∈ s.relOrthSpace U ↔ x.support ⊆ s ∧
--       (∃ l : s →₀ R, (∀ x ∈ U, (Finsupp.total _ _ _ (x ∘ s.incl) l = 0) ∧ ∀ i, l i = x i)) := by
--   rw [relOrthSpace, mem_inf]


-- theorem relOrthSpace_eq_relOrthSpace_inf (s : Set ι) (U : Submodule R (ι → R)) :
--     s.relOrthSpace U = s.relOrthSpace (U ⊓ (s.supportedFun R)) := by
--   classical
--   ext x
--   rw [relOrthSpace, relOrthSpace, mem_inf, mem_supportedFun_iff, mem_inf, mem_supportedFun_iff,
--     and_congr_left_iff, orthSpace, mem_map, orthSpace, mem_map]
--   simp only [mem_orthSpace'_iff, ge_iff_le, mem_inf,
--     mem_supportedFun_iff, and_imp]
--   intro hx
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · obtain ⟨y, hy, rfl⟩ := h
--     refine ⟨y, fun x hxU _↦ hy x hxU, rfl⟩
--   obtain ⟨y, hy, rfl⟩ := h
--   refine ⟨y, fun x hxU ↦  ?_, rfl⟩
--   rw [Finsupp.total_apply, Finsupp.sum]



-- theorem Set.Finite.relOrthSpace_eq {s : Set ι} (hs : s.Finite) {U : Submodule R (ι → R)}:
--     s.relOrthSpace U =
--       (U.map (LinearMap.funLeft R R s.incl)).orthSpace.map (ExtendByZero.linearMap R s.incl) := by
--   have _ := hs.fintype
--   rw [relOrthSpace, orthSpace]
--   ext x
--   simp only [ge_iff_le, mem_inf, mem_map, mem_orthSpace'_iff, mem_supportedFun_iff,
--     mem_orthSpace_iff', forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂, LinearMap.funLeft_apply, Finsupp.lcoeFun,
--     LinearMap.coe_mk, AddHom.coe_mk]
--   constructor
--   · rintro ⟨⟨y, hy, rfl⟩, h⟩
--     use Finsupp.lsubtypeDomain (R := R) (s := s) y
--     simp only [Finsupp.lsubtypeDomain, Finsupp.subtypeDomain, LinearMap.coe_mk, AddHom.coe_mk,
--       Finsupp.coe_mk, comp_apply]
--     refine ⟨fun a ha ↦ ?_, ?_⟩
--     · convert hy a ha
--       have hss : y.support ⊆ s.toFinset
--       · rwa [Set.subset_toFinset, ← Finsupp.fun_support_eq]
--       rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_subset hss (by aesop)]
--       · simp_rw [(show ∀ i : s, a (incl s i) = a i from fun _↦ rfl)]
--         exact Finset.sum_set_coe (s := s) (f := fun x ↦ y x * a x)
--     · ext i
--       simp only [ExtendByZero.linearMap_apply, Subtype.exists, not_exists]
--       obtain (hi | hi) := em (i ∈ s)
--       · rw [← Subtype.coe_mk i hi, Subtype.val_injective.extend_apply]
--         simp
--       rw [extend_apply', eq_comm]
--       · rw [support_subset_iff] at h
--         simpa using (mt <| h i) hi
--       rintro ⟨i, rfl⟩
--       exact hi i.2







end relOrthSpace
