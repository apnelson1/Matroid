import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Defs

variable {α R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {s : Set α}

open Function

/-- The `R`-submodule of all functions from `α` to `M` with support contained in `s : Set α`. -/
@[simps]
def Function.supported (M R : Type*) [Semiring R] [AddCommMonoid M] [Module R M] (s : Set α) :
    Submodule R (α → M) where
  carrier := {f | ∀ i ∉ s, f i = 0}
  add_mem' := @fun f g hf hg i his ↦ by simp [hf i his, hg i his]
  zero_mem' := by simp
  smul_mem' := @fun c x hc i his ↦ by simp [hc i his]

@[simp]
lemma Function.mem_supported_iff {x : α → M} : x ∈ supported M R s ↔ ∀ i ∉ s, x i = 0 := Iff.rfl

lemma Function.mem_supported {x : α → M} :
    x ∈ Function.supported M R s ↔ x.support ⊆ s := by
  simp only [supported, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, Function.support_subset_iff, ne_eq]
  -- `grind` works.
  exact ⟨fun h i hi ↦ by_contra fun h' ↦ hi (h _ h'), fun h i his ↦ by_contra fun h' ↦ his (h _ h')⟩

/-- `Function.supported M R s` is linearly equivalent to the type `↥s → M`. -/
noncomputable def Function.supportedEquivFun (M R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (s : Set α) : Function.supported M R s ≃ₗ[R] (s → M) where
  toFun x i := x.1 i
  map_add' := by aesop
  map_smul' := by aesop
  invFun x := ⟨Function.extend Subtype.val x 0,
    fun i his ↦ by rw [Function.extend_apply' _ _ _ (by simpa), Pi.zero_apply]⟩
  left_inv x := by
    ext i
    simp only
    by_cases hi : i ∈ s
    · exact Subtype.val_injective.extend_apply (g := fun (i : s) ↦ x.1 i) 0 ⟨i, hi⟩
    rw [Function.extend_apply' _ _ _ (by simpa)]
    exact mem_supported_iff.1 x.2 _ hi |>.symm
  right_inv x := by simp

@[simp]
lemma Function.supportedEquivFun_apply (M R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (s : Set α) (i : s) (x : Function.supported M R s) :
    (Function.supportedEquivFun M R s x) i = x.1 i := rfl

lemma Function.supportedEquivFun_symm_apply_mem {i : α} (hi : i ∈ s) (x : s → M) :
    ((Function.supportedEquivFun M R s).symm x).1 i = x ⟨i, hi⟩ := by
  simp only [supportedEquivFun, LinearEquiv.coe_symm_mk]
  exact Subtype.val_injective.extend_apply (g := fun (i : s) ↦ x i) 0 ⟨i, hi⟩

lemma Function.supportedEquivFun_symm_apply_notMem {i : α} (hi : i ∉ s) (x : s → M) :
    ((Function.supportedEquivFun M R s).symm x).1 i = 0 := by
  simp only [supportedEquivFun, LinearEquiv.coe_symm_mk]
  rw [extend_apply' _ _ _ (by simpa), Pi.zero_apply]

open Finsupp

/-- Forget that a function in `Finsupp.supported M R s` has finite support. -/
@[simps] def Finsupp.supportedCoeFunSupported (M R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (s : Set α) : Finsupp.supported M R s →ₗ[R] Function.supported M R s where
  toFun x := ⟨Finsupp.lcoeFun (R := R) x.1, (Finsupp.mem_supported' ..).1 x.2 ⟩
  map_add' := by aesop
  map_smul' := by aesop

lemma Finsupp.supportedCoeFunSupported_injective (M R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (s : Set α) : Function.Injective (Finsupp.supportedCoeFunSupported M R s) := by
  simp [Function.Injective, Finsupp.supportedCoeFunSupported, lcoeFun]

/-- If `s` is finite, then `Finsupp.supported M R s` and `Function.supported M R s` are the same. -/
noncomputable def Finsupp.supportedEquivFunSupported (M R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (hs : s.Finite) : Finsupp.supported M R s ≃ₗ[R] Function.supported M R s :=
  let e1 := Finsupp.supportedEquivFinsupp (M := M) (R := R) s
  let e2 : (s →₀ M) ≃ₗ[R] (s → M) := @linearEquivFunOnFinite R M ↑s hs.to_subtype ..
  let e3 := (Function.supportedEquivFun M R s).symm
  (e1.trans e2).trans e3

@[simp] lemma Finsupp.supportedEquivFunSupported_apply {hs : s.Finite}
    (x : Finsupp.supported M R s) (i : α) :
    (Finsupp.supportedEquivFunSupported M R hs x).1 i = x.1 i := by
  simp_rw [Finsupp.supportedEquivFunSupported, LinearEquiv.trans_apply]
  by_cases hi : i ∈ s
  · simp [supportedEquivFun_symm_apply_mem hi]
  simp only [supportedEquivFun_symm_apply_notMem hi]
  exact (Finsupp.mem_supported' ..).1 x.2 _ hi |>.symm

@[simp] lemma Finsupp.supportedEquivFunSupported_apply_symm {hs : s.Finite}
    (x : Function.supported M R s) (i : α) :
    ((Finsupp.supportedEquivFunSupported M R hs).symm x).1 i = x.1 i := by
  by_cases hi : i ∈ s
  · simp [linearEquivFunOnFinite, hi, supportedEquivFunSupported]
  simp [supportedEquivFunSupported, hi, Function.mem_supported_iff.1 x.2 _ hi]

@[simps]
def Finsupp.lExtendDomain {M : Type*} (R : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    (P : α → Prop) [DecidablePred P] : ((Subtype P) →₀ M) →ₗ[R] α →₀ M where
  toFun x := Finsupp.extendDomain x
  map_add' x y := by aesop
  map_smul' := by aesop

@[simps]
noncomputable def Finsupp.lEmbDomain {α β M : Type*} (R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (f : α ↪ β) : (α →₀ M) →ₗ[R] β →₀ M where
  toFun := Finsupp.embDomain f
  map_add' := by simp
  map_smul' m x := by
    ext b
    simp only [RingHom.id_apply, coe_smul, Pi.smul_apply]
    obtain ⟨a, rfl⟩ | hb := em <| b ∈ Set.range f
    · simp
    simp [embDomain_notin_range _ _ _ hb]

@[simp]
lemma Finsupp.toENat_rank_supported (R : Type*) [Semiring R] [StrongRankCondition R] (s : Set α) :
    (Module.rank R (Finsupp.supported R R s)).toENat = s.encard := by
  rw [(Finsupp.supportedEquivFinsupp ..).rank_eq]
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    simp
  simp

@[simp]
lemma Finsupp.finrank_supported (R : Type*) [Semiring R] [StrongRankCondition R] (s : Set α) :
    Module.finrank R (Finsupp.supported R R s) = s.ncard := by
  simp [Module.finrank, ← Cardinal.toNat_toENat, s.ncard_def]

@[simp]
lemma Function.toENat_rank_supported (R : Type*) [Semiring R] [StrongRankCondition R] (s : Set α) :
    (Module.rank R (Function.supported R R s)).toENat = s.encard := by
  obtain hs | hs := s.finite_or_infinite
  · rw [← (Finsupp.supportedEquivFunSupported _ _ hs).rank_eq]
    simp
  simp only [hs.encard_eq, Cardinal.toENat_eq_top]
  refine le_trans (by simpa [← Cardinal.toENat_eq_top])
    (LinearMap.rank_le_of_injective _ <| Finsupp.supportedCoeFunSupported_injective R R s)

@[simp]
lemma Function.finrank_supported (R : Type*) [Semiring R] [StrongRankCondition R] (s : Set α) :
    Module.finrank R (Function.supported R R s) = s.ncard := by
  simp [Module.finrank, ← Cardinal.toNat_toENat, s.ncard_def]

section Dual

@[simps] noncomputable def Function.dualEvalSingle (α R : Type*) [DecidableEq α] [CommSemiring R] :
    Module.Dual R (α → R) →ₗ[R] (α → R) where
  toFun φ a := φ (Pi.single a 1)
  map_add' := by simp [Pi.add_def]
  map_smul' := by simp [Pi.smul_def]

@[simps] noncomputable def Finsupp.dualEvalSingle (α R : Type*) [CommSemiring R] :
    Module.Dual R (α →₀ R) →ₗ[R] (α → R) where
  toFun φ a := φ (Finsupp.single a 1)
  map_add' := by simp [Pi.add_def]
  map_smul' := by simp [Pi.smul_def]

noncomputable def Function.supportedDualEvalSingle {α : Type*} [DecidableEq α] (R : Type*)
    [CommSemiring R] (s : Set α) :
    Module.Dual R (Function.supported R R s) →ₗ[R] (Function.supported R R s) :=
  let e1 := Function.supportedEquivFun R R s
  let e2 := Function.dualEvalSingle s R
  e1.symm ∘ₗ (e2 ∘ₗ e1.symm.dualMap.toLinearMap)

-- noncomputable def Finsupp.supportedDualEvalSingle {α : Type*} [DecidableEq α] (R : Type*)
--     [CommSemiring R] (s : Set α) :
--     Module.Dual R (Finsupp.supported R R s) →ₗ[R] (Finsupp.supported R R s) where
--   toFun x :=
--     _
--   map_add' := _
--   map_smul' := _

end Dual
