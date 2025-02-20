import Matroid.Representation.Minor

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I C E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] {c : α →₀ 𝔽}

open Set Function Submodule

namespace Matroid

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
    c ∈ v.cycleSpace ↔ c.linearCombination 𝔽 v = 0 ∧ (c.support : Set α) ⊆ M.E := by
  simp [Rep.cycleSpace, Finsupp.mem_supported]

lemma Rep.support_subset_ground_of_mem_cycleSpace (v : M.Rep 𝔽 W) (hc : c ∈ v.cycleSpace) :
    (c.support : Set α) ⊆ M.E :=
  (v.mem_cycleSpace_iff.1 hc).2

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

/- Every finite cyclic set is the support of a vector in the cycle space. -/
-- I don't know if this is true for larger fields than GF(2).
-- lemma Rep.exists_eq_support_mem_cycleSpace_of_cyclic_of_finite (v : M.Rep 𝔽 W) (hX : M.Cyclic X)
--     (hfin : X.Finite) : ∃ c, c ∈ v.cycleSpace ∧ X = support c := by
--   obtain rfl | hne := X.eq_empty_or_nonempty
--   · exact ⟨0, by simp, by simp⟩
--   obtain ⟨C, X₀, hCX, hA₀X, hC, hA₀, rfl⟩ := hX.exists_eq_union_isCircuit_cyclic_ssubset hne
