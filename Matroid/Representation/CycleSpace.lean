import Mathlib.LinearAlgebra.Projectivization.Basic -- inefficient import
import Matroid.Representation.Minor
import Matroid.ForMathlib.LinearAlgebra.Finsupp

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I C E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] {c : α →₀ 𝔽}

open Set Function Submodule

namespace Matroid

/-- The `cycleSpace` of an `𝔽`-representation `v` of `M : Matroid α` is the set of vectors
in `α →₀ 𝔽` that are supported on a finite subset of `M.E` and give a linear combination of
zero with the elements of `v`. This space contains a vector supported on every circuit.
This is the right null space of a matrix representation of `M`. -/
noncomputable def Rep.cycleSpace (v : M.Rep 𝔽 W) : Submodule 𝔽 (α →₀ 𝔽) :=
    (LinearMap.ker (Finsupp.linearCombination 𝔽 v) ⊓ Finsupp.supported 𝔽 𝔽 M.E)

/-- `supportedCycleSpace` is the cycle space as a subspace of `Finsupp.supported 𝔽 𝔽 M.E`.-/
noncomputable def Rep.supportedCycleSpace (v : M.Rep 𝔽 W) :
    Submodule 𝔽 (Finsupp.supported 𝔽 𝔽 M.E) :=
    (LinearMap.ker (Finsupp.linearCombinationOn _ _ 𝔽 v M.E))

lemma Rep.supported_finiteDimensional [M.Finite] (_ : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 <| Finsupp.supported 𝔽 𝔽 M.E :=
  have := M.ground_finite.to_subtype
  Module.Finite.equiv (Finsupp.supportedEquivFinsupp M.E).symm

instance Rep.cycleSpace_finiteDimensional [M.Finite] (v : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 v.cycleSpace := by
  have := v.supported_finiteDimensional
  exact Submodule.finiteDimensional_inf_right ..

instance Rep.supportedCycleSpace_finiteDimensional' [M.Finite] (v : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 v.supportedCycleSpace := by
  have := v.supported_finiteDimensional
  infer_instance

lemma Rep.mem_cycleSpace_iff (v : M.Rep 𝔽 W) :
    c ∈ v.cycleSpace ↔ c.linearCombination 𝔽 v = 0 ∧ support c ⊆ M.E := by
  simp [Rep.cycleSpace, Finsupp.mem_supported]

lemma Rep.mem_supportedCycleSpace_iff (v : M.Rep 𝔽 W) {c : Finsupp.supported 𝔽 𝔽 M.E} :
    c ∈ v.supportedCycleSpace ↔ c.1.linearCombination 𝔽 v = 0 := by
  simp [supportedCycleSpace, Finsupp.linearCombinationOn, LinearMap.codRestrict]

lemma Rep.support_subset_ground_of_mem_cycleSpace (v : M.Rep 𝔽 W) (hc : c ∈ v.cycleSpace) :
    support c ⊆ M.E :=
  (v.mem_cycleSpace_iff.1 hc).2

@[simps]
noncomputable def Rep.cycleSpaceEquiv (v : M.Rep 𝔽 W) :
    v.cycleSpace ≃ₗ[𝔽] v.supportedCycleSpace where
  toFun x := ⟨⟨x.1,x.2.2⟩, v.mem_supportedCycleSpace_iff.2 (v.mem_cycleSpace_iff.1 x.2).1⟩
  map_add' := by simp
  map_smul' := by simp
  invFun x := ⟨x.1.1, v.mem_cycleSpace_iff.2 ⟨v.mem_supportedCycleSpace_iff.1 x.2,
    by simpa using (Finsupp.mem_supported ..).1 x.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma Rep.supportedCycleSpace_comp (v : M.Rep 𝔽 W) (φ : W →ₗ[𝔽] W') (hφ) :
    (v.comp φ hφ).supportedCycleSpace = v.supportedCycleSpace := by
  simp_rw [disjoint_def, ← image_univ, Finsupp.mem_span_image_iff_linearCombination] at hφ
  simp_rw [SetLike.ext_iff, mem_supportedCycleSpace_iff, comp_coeFun,
    ← LinearMap.map_finsupp_linearCombination, ← LinearMap.mem_ker (f := φ)]
  exact fun x ↦ ⟨fun h ↦ hφ _ ⟨_, by simp, rfl⟩ h, fun h ↦ by simp [h]⟩

@[simp]
lemma Rep.cycleSpace_comp (v : M.Rep 𝔽 W) (φ : W →ₗ[𝔽] W') (hφ) :
    (v.comp φ hφ).cycleSpace = v.cycleSpace := by
  simp_rw [disjoint_def] at hφ
  ext x
  simp only [mem_cycleSpace_iff, comp_coeFun, Finsupp.fun_support_eq, and_congr_left_iff]
  rw [← LinearMap.map_finsupp_linearCombination, ← LinearMap.mem_ker]
  refine fun h ↦ ⟨fun h0 ↦ hφ _ ?_ h0, fun h0 ↦ by simp [h0]⟩
  rw [← image_univ, Finsupp.mem_span_image_iff_linearCombination]
  exact ⟨x, by simp, rfl⟩

@[simp]
lemma Rep.cycleSpace_comp' (v : M.Rep 𝔽 W) (φ : W →ₗ[𝔽] W') (hφ) :
    (v.comp' φ hφ).cycleSpace = v.cycleSpace := by
  simp [comp']

@[simp]
lemma Rep.cycleSpace_compEquiv (v : M.Rep 𝔽 W) (φ : W ≃ₗ[𝔽] W') :
    (v.compEquiv φ).cycleSpace = v.cycleSpace := by
  simp [compEquiv]

@[simp]
lemma Rep.restrictSpan_cycleSpace (v : M.Rep 𝔽 W) :
    v.restrictSpan.cycleSpace = v.cycleSpace := by
  simpa using congr_arg Rep.cycleSpace v.restrictSpan_comp

@[simp]
lemma Rep.standardRep'_cycleSpace (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep' hB).cycleSpace = v.cycleSpace := by
  simp [standardRep']

@[simp]
lemma Rep.standardRep_cycleSpace (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep hB).cycleSpace = v.cycleSpace := by
  simp [standardRep]

/-- If some linear combination of columns of `M.E` is zero, the nonzero indices form a cyclic set.-/
lemma Rep.cyclic_of_linearCombination (v : M.Rep 𝔽 W) (c : α →₀ 𝔽) (hcE : (c.support : Set α) ⊆ M.E)
    (hcv : c.linearCombination 𝔽 v = 0) : M.Cyclic c.support := by
  rw [cyclic_iff_forall_mem_closure_diff_singleton]
  intro e he
  rw [v.mem_closure_iff (hcE he), Finsupp.mem_span_image_iff_linearCombination]
  have hce : c e ≠ 0 := by simpa using he
  use - (c e)⁻¹ • (c - Finsupp.single e (c e))
  suffices ∀ (x : α), (¬c x = 0 → x = e) → c x - (Finsupp.single e (c e)) x = 0 by
    simpa [Finsupp.mem_supported', hcv, hce, ← smul_assoc]
  intro x
  obtain rfl | hne := eq_or_ne x e
  · simp
  simp +contextual [hne]

lemma Rep.support_cyclic_of_mem_cycleSpace (v : M.Rep 𝔽 W) {c : α →₀ 𝔽} (hc : c ∈ v.cycleSpace) :
    M.Cyclic c.support := by
  simp only [cyclic_iff_forall_mem_closure_diff_singleton, Finset.mem_coe, Finsupp.mem_support_iff,
    ne_eq, v.mem_closure_iff', Finsupp.mem_span_image_iff_linearCombination, Finsupp.mem_supported]
  rw [mem_cycleSpace_iff] at hc
  refine fun e he ↦ ⟨⟨- (c e)⁻¹ • (c - Finsupp.single e (c e)), fun x ↦ ?_,
    by simp [hc.1, inv_smul_smul₀ he]⟩, hc.2 (by simpa)⟩
  obtain rfl | hne := eq_or_ne x e
  · simp
  simp [he, hne]

lemma Rep.exists_finsupp_of_isCircuit (v : M.Rep 𝔽 W) (hC : M.IsCircuit C) :
    ∃ c : α →₀ 𝔽, c.support = C ∧ c.linearCombination 𝔽 v = 0 := by
  have hC' := hC.not_indep
  rw [v.indep_iff, linearDepOn_iff'] at hC'
  obtain ⟨c, hcsupp, hc, hc0⟩ := hC'
  refine ⟨c, subset_antisymm (by simpa using hcsupp) fun e heC ↦ ?_, hc⟩
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
  refine fun hc' ↦ hc0 <| (linearIndepOn_iff.1 <| v.onIndep <| hC.diff_singleton_indep heC) c ?_ hc
  simpa [Finsupp.mem_supported, subset_diff_singleton_iff, hc']

lemma Rep.exists_mem_cycleSpace_of_isCircuit (v : M.Rep 𝔽 W) (hC : M.IsCircuit C) :
    ∃ w ∈ v.cycleSpace, w.support = C := by
  obtain ⟨c, rfl, hc⟩ := v.exists_finsupp_of_isCircuit hC
  exact ⟨c, ⟨hc, by simp [Finsupp.mem_supported, hC.subset_ground]⟩, rfl⟩

variable {𝔽 W : Type*} [Field 𝔽] [AddCommGroup W] [Module 𝔽 W] [Module 𝔽 W']

/-- For a member `φ` of the dual module of `α →₀ R`,
the vector in `α → R` whose `i`th entry is the value of `φ` at `Finsupp.single a i`. -/
@[simps] noncomputable def Finsupp.dualFunMap : Module.Dual 𝔽 (α →₀ 𝔽) →ₗ[𝔽] (α → 𝔽) where
  toFun φ a := φ (Finsupp.single a 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mySupported (𝔽 : Type*) [Field 𝔽] (s : Set α) : Submodule 𝔽 (α → 𝔽) where
  carrier := {f | ∀ i ∉ s, f i = 0}
  add_mem' := @fun f g hf hg i his ↦ by simp [hf i his, hg i his]
  zero_mem' := by simp
  smul_mem' := @fun c x hc i his ↦ by simp [hc i his]

/-- For `s : Set α`, and a member `φ` of the dual module of `Finsupp.supported R R s`,
the vector in `α → R` whose `i`th entry is the value of `φ` at `Finsupp.single a i`. -/
noncomputable def Finsupp.dualSupportedFunMap {α : Type*} (R : Type*) [CommSemiring R] (s : Set α)
    [DecidablePred (· ∈ s)] : Module.Dual R ↥(Finsupp.supported R R s) →ₗ[R] (α → R) where
  toFun φ a := φ (Finsupp.restrictDom R R s (Finsupp.single a 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- lemma Finsupp.dualSupportedFunMap_eq_comp {α : Type*} (R : Type*) [CommSemiring R] {s : Set α}
--     (hs : s.)
--     [DecidablePred (· ∈ s)]

lemma Finsupp.dualSupportedFunMap_apply_notMem {α R : Type*} [CommSemiring R] {s : Set α}
    [DecidablePred (· ∈ s)] (φ) {a} (ha : a ∉ s) : Finsupp.dualSupportedFunMap R s φ a = 0 := by
  simp only [Finsupp.dualSupportedFunMap, LinearMap.coe_mk, AddHom.coe_mk]
  convert φ.map_zero
  aesop

lemma Finsupp.dualSupportedFunMap_apply_mem {α R : Type*} [CommSemiring R] {s : Set α}
    [DecidablePred (· ∈ s)] (φ) {a} (ha : a ∈ s) :
    Finsupp.dualSupportedFunMap R s φ a =
    φ ⟨Finsupp.single a 1, Finsupp.single_mem_supported R 1 ha⟩  := by
  simp [Finsupp.dualSupportedFunMap]
  congr
  aesop

lemma Finsupp.dualSupportedFunMap_apply {α : Type*} (R : Type*) [CommSemiring R] (s : Set α)
    [DecidablePred (· ∈ s)] (φ) (a) : Finsupp.dualSupportedFunMap R s φ a =
    if has : a ∈ s then φ ⟨Finsupp.single a 1, Finsupp.single_mem_supported R 1 has⟩ else 0 := by
  split_ifs with h
  · rwa [Finsupp.dualSupportedFunMap_apply_mem]
  rwa [Finsupp.dualSupportedFunMap_apply_notMem]

@[simp]
lemma mem_mySupported_iff {s : Set α} {x : α → 𝔽} :
    x ∈ mySupported 𝔽 s ↔ support x ⊆ s := by
  simp [mySupported, not_imp_comm]

@[simp]
lemma coe_restrictDom {α M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (s : Set α)
    [DecidablePred fun (x : α) => x ∈ s] (f : Finsupp.supported M R s) :
    (Finsupp.restrictDom M R s f : α →₀ M) = f.1 := by
  ext i
  simp only [Finsupp.restrictDom_apply, Finsupp.filter_apply, ite_eq_left_iff]
  exact fun hi ↦ by rw [show f.1 i = 0 by simpa using notMem_subset f.2 hi]

-- noncomputable def thing (v : M.Rep 𝔽 W) :=
--   (dualAnnihilator v.supportedCycleSpace)

/-- The `cocycleSpace` of an `𝔽`-representation of `M : Matroid α` is the set of vectors
in `α → 𝔽` that are supported on `M.E`, and are orthogonal to every vector in the `cycleSpace`.
If `M` is finite, this corresponds to the row space of a matrix representation of `M`.  -/
noncomputable def Rep.cocycleSpace (v : M.Rep 𝔽 W) : Submodule 𝔽 (α → 𝔽) :=
  ((dualAnnihilator v.cycleSpace).map Finsupp.dualFunMap ⊓ mySupported 𝔽 M.E)

lemma Rep.cocycleSpace_eq' (v : M.Rep 𝔽 W) [DecidablePred (· ∈ M.E)] :
  v.cocycleSpace =
    (dualAnnihilator v.supportedCycleSpace).map (Finsupp.dualSupportedFunMap 𝔽 M.E) := by
  classical
  ext x
  simp only [cocycleSpace, Finsupp.dualFunMap, mem_inf, mem_map, mem_dualAnnihilator,
    mem_cycleSpace_iff, Finsupp.fun_support_eq, and_imp, LinearMap.coe_mk, AddHom.coe_mk,
    mem_mySupported_iff, support_subset_iff, ne_eq, not_imp_comm, mem_supportedCycleSpace_iff]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hsupp : ∀ x ∉ M.E, c _ = 0⟩
    refine ⟨(Finsupp.supported 𝔽 𝔽 M.E).dualRestrict c, fun a ha0 ↦ hc _ (by simpa) a.2, ?_⟩
    ext a
    simpa [Finsupp.dualSupportedFunMap_apply, dualRestrict_apply, Finsupp.restrictDom_apply,
      eq_comm (a := (0 : 𝔽))] using hsupp a
  rintro ⟨c, hc, rfl⟩
  refine ⟨⟨c.comp (Finsupp.restrictDom 𝔽 𝔽 M.E),
    fun w h hsupp ↦ hc (Finsupp.restrictDom 𝔽 𝔽 M.E w) ?_, by simp [Finsupp.dualSupportedFunMap]⟩,
    fun x ↦ Finsupp.dualSupportedFunMap_apply_notMem _⟩
  convert h
  exact coe_restrictDom (R := 𝔽) (M := 𝔽) (s := M.E) ⟨w, hsupp⟩

@[simp]
lemma Rep.cocycleSpace_comp (v : M.Rep 𝔽 W) (φ : W →ₗ[𝔽] W') (hφ) :
    (v.comp φ hφ).cocycleSpace = v.cocycleSpace := by
  simp [cocycleSpace]

@[simp]
lemma Rep.cocycleSpace_comp' (v : M.Rep 𝔽 W) (φ : W →ₗ[𝔽] W') (hφ) :
    (v.comp' φ hφ).cocycleSpace = v.cocycleSpace := by
  simp [comp']

@[simp]
lemma Rep.cocycleSpace_compEquiv (v : M.Rep 𝔽 W) (φ : W ≃ₗ[𝔽] W') :
    (v.compEquiv φ).cocycleSpace = v.cocycleSpace := by
  simp [compEquiv]

@[simp]
lemma Rep.restrictSpan_cocycleSpace (v : M.Rep 𝔽 W) :
    v.restrictSpan.cocycleSpace = v.cocycleSpace := by
  simp [cocycleSpace]

@[simp]
lemma Rep.standardRep'_cocycleSpace (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep' hB).cocycleSpace = v.cocycleSpace := by
  simp [cocycleSpace]

@[simp]
lemma Rep.standardRep_cocycleSpace (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep hB).cocycleSpace = v.cocycleSpace := by
  simp [cocycleSpace]

lemma Rep.mem_cocycleSpace_iff_of_support (v : M.Rep 𝔽 W) {x : α → 𝔽} (hx : support x ⊆ M.E) :
    x ∈ v.cocycleSpace ↔ ∀ y ∈ v.cycleSpace, Finsupp.linearCombination 𝔽 x y = 0 := by
  simp only [Rep.cocycleSpace, Finsupp.dualFunMap, mem_inf, mem_map, mem_dualAnnihilator,
    Rep.mem_cycleSpace_iff, and_imp, LinearMap.coe_mk, AddHom.coe_mk, mem_mySupported_iff]
  refine ⟨fun h y hy hyE ↦ ?_, fun h ↦ ⟨⟨_, h, by simp⟩, hx⟩⟩
  obtain ⟨⟨z,hz, rfl⟩, hsupp⟩ := h
  rw [← hz y hy hyE]
  convert (z.map_finsupp_linearCombination (g := fun a : α ↦ Finsupp.single a 1) y).symm
  simp [Finsupp.linearCombination]

lemma Rep.mem_cocycleSpace_iff (v : M.Rep 𝔽 W) {x : α → 𝔽} :
    x ∈ v.cocycleSpace ↔
      (∀ y ∈ v.cycleSpace, Finsupp.linearCombination 𝔽 x y = 0) ∧ support x ⊆ M.E := by
  by_cases hsupp : support x ⊆ M.E
  · rw [mem_cocycleSpace_iff_of_support v hsupp, and_iff_left hsupp]
  simp [Rep.cocycleSpace, hsupp]

lemma Rep.row_mem_cocycleSpace (v : M.Rep 𝔽 (β → 𝔽)) (b : β) : (v · b) ∈ v.cocycleSpace := by
  refine v.mem_cocycleSpace_iff.2 ⟨fun y hy ↦ ?_, ?_⟩
  · simpa [Finsupp.linearCombination, Finsupp.sum] using congr_fun (v.mem_cycleSpace_iff.1 hy).1 b
  exact subset_trans (by simp +contextual [not_imp_not]) v.support_subset_ground

lemma Rep.mem_cycleSpace_iff_forall_of_support (v : M.Rep 𝔽 W) {y : α →₀ 𝔽} (hy : support y ⊆ M.E) :
    y ∈ v.cycleSpace ↔ ∀ x ∈ v.cocycleSpace, Finsupp.linearCombination 𝔽 x y = 0 := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← v.standardRep_cycleSpace hB, ← v.standardRep_cocycleSpace hB]
  set v' := v.standardRep hB
  simp +contextual only [mem_cocycleSpace_iff, and_imp]
  refine ⟨fun hy x h hx ↦ h y hy, fun h ↦ ?_⟩
  rw [mem_cycleSpace_iff, and_iff_left hy]
  ext i
  specialize h (v' · i) (fun y hy ↦ ?_)   ?_
  · simpa [Finsupp.linearCombination, Finsupp.sum] using congr_fun (v'.mem_cycleSpace_iff.1 hy).1 i
  · exact subset_trans (by simp +contextual [not_imp_not]) v'.support_subset_ground
  simpa [Finsupp.linearCombination, Finsupp.sum] using h

lemma Rep.mem_cycleSpace_iff_forall (v : M.Rep 𝔽 W) {y : α →₀ 𝔽} :
    y ∈ v.cycleSpace ↔
      (∀ x ∈ v.cocycleSpace, Finsupp.linearCombination 𝔽 x y = 0) ∧ support y ⊆ M.E  := by
  by_cases hsupp : support y ⊆ M.E
  · rw [mem_cycleSpace_iff_forall_of_support _ hsupp, and_iff_left hsupp]
  simp only [mem_cycleSpace_iff, and_congr_left_iff, hsupp, false_imp_iff]

instance Rep.cocycleSpace_finiteDimensional [M.Finite] (v : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 v.cocycleSpace := by
  classical
  rw [cocycleSpace_eq']
  have := v.supported_finiteDimensional
  exact Module.Finite.map v.supportedCycleSpace.dualAnnihilator (Finsupp.dualSupportedFunMap 𝔽 M.E)

-- lemma foo [M.Finite] (v : M.Rep 𝔽 W) :
--     Module.finrank 𝔽 v.cocycleSpace + Module.finrank 𝔽 v.cycleSpace = M.E.ncard := by
--   classical
--   have := v.supported_finiteDimensional
--   rw [add_comm, v.cycleSpaceEquiv.finrank_eq, v.cocycleSpace_eq']
--   convert Subspace.finrank_add_finrank_dualAnnihilator_eq v.supportedCycleSpace
--   · sorry
--   sorry




-- lemma cocycleSpace_eq_span [Fintype β] (v : M.Rep 𝔽 (β → 𝔽)) :
--     v.cocycleSpace = span 𝔽 (range fun b ↦ (v · b)) := by
--   apply Submodule.eq_of_le_of_finrank_le ?_ ?_
--   simp only [le_antisymm_iff, span_le, range_subset_iff, SetLike.mem_coe, and_iff_left
--     (fun y ↦ v.row_mem_cocycleSpace y)]
