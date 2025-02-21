import Matroid.Representation.Minor

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I C E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] {c : α →₀ 𝔽}

open Set Function Submodule

namespace Matroid

/-- The `cycleSpace` of an `𝔽`-representation `v` of `M : Matroid α` is the set of vectors
in `α →₀ 𝔽` that are supported on a finite subset of `M.E` and give a linear combination of
zero with the elements of `v`. This space contains a vector supported on every circuit.
This is the right null space of a matrix representation of `M`. -/
noncomputable def Rep.cycleSpace (v : M.Rep 𝔽 W) :=
    (LinearMap.ker (Finsupp.linearCombination 𝔽 v) ⊓ Finsupp.supported 𝔽 𝔽 M.E)

lemma Rep.supported_finiteDimensional [M.Finite] (_ : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 <| Finsupp.supported 𝔽 𝔽 M.E :=
  have := M.ground_finite.to_subtype
  Module.Finite.equiv (Finsupp.supportedEquivFinsupp M.E).symm

lemma Rep.cycleSpace_finiteDimensional [M.Finite] (v : M.Rep 𝔽 W) :
    FiniteDimensional 𝔽 v.cycleSpace := by
  have := v.supported_finiteDimensional
  exact Submodule.finiteDimensional_inf_right ..

lemma Rep.mem_cycleSpace_iff (v : M.Rep 𝔽 W) :
    c ∈ v.cycleSpace ↔ c.linearCombination 𝔽 v = 0 ∧ support c ⊆ M.E := by
  simp [Rep.cycleSpace, Finsupp.mem_supported]

lemma Rep.support_subset_ground_of_mem_cycleSpace (v : M.Rep 𝔽 W) (hc : c ∈ v.cycleSpace) :
    support c ⊆ M.E :=
  (v.mem_cycleSpace_iff.1 hc).2

@[simp]
lemma Rep.cycleSpace_comp (v : M.Rep 𝔽 W) (φ : W →ₗ[𝔽] W') (hφ) :
    (v.comp φ hφ).cycleSpace = v.cycleSpace := by
  rw [disjoint_def] at hφ
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
  simp +contextual [hne, Finsupp.single_apply_eq_zero]

lemma Rep.support_cyclic_of_mem_cycleSpace (v : M.Rep 𝔽 W) {c : α →₀ 𝔽} (hc : c ∈ v.cycleSpace) :
    M.Cyclic c.support := by
  simp only [cyclic_iff_forall_mem_closure_diff_singleton, Finset.mem_coe, Finsupp.mem_support_iff,
    ne_eq, v.mem_closure_iff', Finsupp.mem_span_image_iff_linearCombination, Finsupp.mem_supported]
  rw [mem_cycleSpace_iff] at hc
  refine fun e he ↦ ⟨⟨- (c e)⁻¹ • (c - Finsupp.single e (c e)), fun x ↦ ?_,
    by simp [hc.1, inv_smul_smul₀ he]⟩, hc.2 (by simpa)⟩
  obtain rfl | hne := eq_or_ne x e
  · simp
  simp [he, hne, sub_eq_zero, Finsupp.single_eq_of_ne hne.symm]

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

-- These next two definitions are presumably somewhere in mathlib.
@[simps] noncomputable def myLinMap : Module.Dual 𝔽 (α →₀ 𝔽) →ₗ[𝔽] (α → 𝔽) where
  toFun φ a := φ (Finsupp.single a 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mySupported (𝔽 : Type*) [Field 𝔽] (s : Set α) : Submodule 𝔽 (α → 𝔽) where
  carrier := {f | ∀ i ∉ s, f i = 0}
  add_mem' := @fun f g hf hg i his ↦ by simp [hf i his, hg i his]
  zero_mem' := by simp
  smul_mem' := @fun c x hc i his ↦ by simp [hc i his]

@[simp]
lemma mem_mySupported_iff {s : Set α} {x : α → 𝔽} :
    x ∈ mySupported 𝔽 s ↔ support x ⊆ s := by
  simp [mySupported, not_imp_comm]

/-- The `cocycleSpace` of an `𝔽`-representation of `M : Matroid α` is the set of vectors
in `α → 𝔽` that are supported on `M.E`, and are orthogonal to every vector in the `cycleSpace`.
This corresponds to the 'row space' of a matrix representation.  -/
noncomputable def Rep.cocycleSpace (v : M.Rep 𝔽 W) : Submodule 𝔽 (α → 𝔽) :=
  ((dualAnnihilator v.cycleSpace).map myLinMap ⊓ mySupported 𝔽 M.E)

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
  simp only [Rep.cocycleSpace, myLinMap, mem_inf, mem_map, mem_dualAnnihilator,
    Rep.mem_cycleSpace_iff, and_imp, LinearMap.coe_mk, AddHom.coe_mk, mem_mySupported_iff,
     ne_eq, not_imp_comm]
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

lemma Rep.mem_cycleSpace_iff_forall_of_support (v : M.Rep 𝔽 W) {y : α →₀ 𝔽} (hy : support y ⊆ M.E) :
    y ∈ v.cycleSpace ↔ ∀ x ∈ v.cocycleSpace, Finsupp.linearCombination 𝔽 x y = 0 := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← v.standardRep_cycleSpace hB, ← v.standardRep_cocycleSpace hB]
  set v' := v.standardRep hB
  simp +contextual only [mem_cocycleSpace_iff, ne_eq, and_imp]
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
