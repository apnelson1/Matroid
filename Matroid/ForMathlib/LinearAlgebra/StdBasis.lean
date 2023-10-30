
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dual
import Matroid.ForMathlib.LinearAlgebra.FiniteDimensional
import Matroid.ForMathlib.LinearAlgebra.Dual

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

section orthspace

variable [Field R] [Fintype ι] {U V : Subspace R (ι → R)} {x : ι → R}

/-- The space of vectors 'orthogonal' to all vectors in `U`, in the sense of having a
  dot product of zero. -/
@[pp_dot] noncomputable def Submodule.orthspace (U : Subspace R (ι → R)) : Subspace R (ι → R) :=
  U.dualAnnihilator.map (Module.piEquiv ι R R).symm

@[simp] theorem mem_orthspace_iff' : x ∈ U.orthspace ↔ ∀ y ∈ U, ∑ i, x i * y i = 0 := by
  classical
  simp only [orthspace, mem_map, mem_dualAnnihilator]
  refine ⟨?_, fun h ↦ ⟨Module.piEquiv ι R R x, fun w hw ↦ ?_, by simp⟩⟩
  · rintro ⟨y, hy, rfl⟩ x hxU; convert hy x hxU using 1; simp
  convert h w hw using 1
  simp_rw [Module.piEquiv_apply_apply, smul_eq_mul, mul_comm]

@[simp] theorem mem_orthspace_iff : x ∈ U.orthspace ↔ ∀ y ∈ U, Matrix.dotProduct x y = 0 :=
    mem_orthspace_iff'

@[simp] theorem orthspace_orthspace (U : Subspace R (ι → R)) : U.orthspace.orthspace = U := by
  classical
  refine (FiniteDimensional.eq_of_le_of_finrank_le (fun x hxU ↦ ?_) (le_of_eq ?_)).symm
  · simp_rw [mem_orthspace_iff']
    intro y hy
    simpa [mul_comm] using hy x hxU
  have := (Module.piEquiv ι R R).symm.finrank_map_eq'

  rw [orthspace, orthspace, LinearEquiv.finrank_map_eq', LinearEquiv.dualAnnihilator_map_eq,
    LinearEquiv.finrank_map_eq', ←Subspace.finrank_dualCoannihilator_eq,
    Subspace.dualAnnihilator_dualCoannihilator_eq]

theorem orthspace_injective (ι R : Type _) [Fintype ι] [Field R] :
    Injective (Submodule.orthspace : Subspace R (ι → R) → Subspace R (ι → R)) :=
  fun _ _ h ↦ by simpa using congr_arg Submodule.orthspace h

theorem eq_orthspace_comm : U = V.orthspace ↔ V = U.orthspace :=
  ⟨fun h ↦ by rw [h, orthspace_orthspace], fun h ↦ by rw [h, orthspace_orthspace]⟩

end orthspace
