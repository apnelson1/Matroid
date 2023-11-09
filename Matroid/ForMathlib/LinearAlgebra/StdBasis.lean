
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dual
import Matroid.ForMathlib.LinearAlgebra.FiniteDimensional
import Matroid.ForMathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.BilinearForm

open Set BigOperators Submodule Function

@[simp] theorem Fintype.sum_pi_single {α : Type v} {β : α → Type u_2} [DecidableEq α] [Fintype α]
    [(a : α) → AddCommMonoid (β a)] (a : α) (f : (a : α) → β a) :
    ∑ a', Pi.single a' (f a') a = f a := by
  convert Finset.sum_pi_single a f Finset.univ; simp

@[simp] theorem Module.piEquiv_apply_symm [CommSemiring R] [Fintype α] [DecidableEq α]
    (y : Module.Dual R (α → R)) (i : α) : (Module.piEquiv α R R).symm y i = y (Pi.single i 1) := by
  simp only [piEquiv, Basis.constr, Pi.basisFun_apply, LinearMap.stdBasis_apply,
    LinearEquiv.coe_symm_mk]; rfl

@[simp] theorem Module.Dual.sum_update [Field R] [Fintype α] [DecidableEq α]
  (y : Module.Dual R (α → R)) (x : α → R) : ∑ i, y (Function.update 0 i 1) * x i = y x := by
  rw [←LinearMap.congr_fun ((Pi.basisFun R α).sum_dual_apply_smul_coord y) x]
  simp [LinearMap.stdBasis_apply]

@[simp] theorem Module.Dual.sum_pi_single [Field R] [Fintype α] [DecidableEq α]
  (y : Module.Dual R (α → R)) (x : α → R) : ∑ i, y (Pi.single i 1) * x i = y x :=
  Module.Dual.sum_update y x
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
  convert FunLike.congr_fun ((Pi.basisFun R η).sum_dual_apply_smul_coord w) y using 1
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
    LinearEquiv.finrank_map_eq', ←Subspace.finrank_dualCoannihilator_eq,
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
      rw [←orthSpace_orthSpace V, mem_orthSpace_iff]
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

end orthSpace
