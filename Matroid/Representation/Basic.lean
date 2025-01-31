import Mathlib.LinearAlgebra.LinearIndependent
import Matroid.Simple
-- import Matroid.ForMathlib.Function

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

section ForMathlib

@[simp] lemma linearIndependent_zero_iff : LinearIndependent 𝔽 (0 : α → W) ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun a ↦ h.ne_zero a rfl⟩, fun _ ↦ linearIndependent_empty_type⟩

@[simp] lemma restrict_zero (X : Set α) : X.restrict (0 : α → W) = 0 := rfl

-- lemma foo : LinearIndependent 𝔽 (fun x : I ↦ v x)
--       ∀ c : α →₀ 𝔽, Finsupp.linearCombination 𝔽 v c = 0 → (c.support : Set α) ⊆ I → c = 0 := by

end ForMathlib

namespace Matroid

/-- `M.Rep 𝔽 W` is a function from `α` to a module `W` that represents `M`. -/
structure Rep (M : Matroid α) (𝔽 W : Type*) [Semiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (valid' : ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict to_fun))

/-- A `Representable` matroid is one that has a representation over `𝔽` -/
def Representable (M : Matroid α) (𝔽 : Type*) [Semiring 𝔽] : Prop :=
  ∃ (B : Set α), Nonempty (M.Rep 𝔽 (B →₀ 𝔽))

instance : FunLike (M.Rep 𝔽 W) α W where
  coe v := v.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

@[simp] lemma Rep.to_fun_eq_coe (v : M.Rep 𝔽 W) : v.to_fun = (v : α → W) := rfl

lemma Rep.indep_iff_restrict (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v) :=
  v.valid' I

lemma Rep.indep_iff (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (v ∘ ((↑) : I → α)) :=
  v.valid' I

lemma Rep.indep_iff' (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (fun x : I ↦ v x) :=
  v.valid' I

lemma Rep.onIndep (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (I.restrict v) :=
  v.indep_iff.1 hI

lemma Rep.injOn_of_indep (v : M.Rep 𝔽 W) (hI : M.Indep I) : InjOn v I :=
  injOn_iff_injective.2 ((v.onIndep hI).injective)

lemma Rep.indep_image (v : M.Rep 𝔽 W) (hI : M.Indep I) :
    LinearIndependent 𝔽 ((↑) : (v '' I) → W) := by
  rw [← linearIndependent_image <| v.injOn_of_indep hI]
  exact v.onIndep hI

lemma Rep.indep_iff_image_of_inj (v : M.Rep 𝔽 W) (h_inj : InjOn v I) :
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : (v '' I) → W) := by
  refine ⟨v.indep_image, fun hi ↦ ?_⟩
  rw [v.indep_iff]
  exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

lemma Rep.indep_iff_image (v : M.Rep 𝔽 W) :
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : (v '' I) → W) ∧ InjOn v I :=
  ⟨fun h ↦ ⟨v.indep_image h, v.injOn_of_indep h⟩,
    fun h ↦ (v.indep_iff_image_of_inj h.2).2 h.1⟩

-- lemma Rep.indep_iff_forall_finsupp (v : M.Rep 𝔽 W) : M.Indep I ↔
--       ∀ c : α →₀ 𝔽, Finsupp.linearCombination 𝔽 v c = 0 → (c.support : Set α) ⊆ I → c = 0 := by
--   classical
--   rw [v.indep_iff']

--   refine ⟨fun h c hc hc0 ↦ h c hc0 hc, fun h c hc hcs ↦ h c hcs hc⟩
  -- rw [v.indep_iff', linearIndependent_iff]
  -- refine ⟨fun h c hc hcs ↦ ?_, fun h c hc0 ↦ ?_⟩
  -- · specialize h <| Finsupp.subtypeDomain (· ∈ I) c
  --   rw [Finsupp.subtypeDomain_eq_zero_iff hcs] at h
  --   refine h ?_
  --   rw [← hc]
  --   simp [Finsupp.linearCombination, Finset.sum_subtype_of_mem (f := fun x ↦ c x • v x) hcs,
  --     Finsupp.sum]
  -- have h' : (Finsupp.linearCombination 𝔽 (v ∘ Subtype.val)) c = 0 → c = 0 := by
  --   simpa using h (c.embDomain (Embedding.subtype (· ∈ I)))
  -- exact h' hc0

-- lemma Rep.exists_finsupp_of_not_indep (v : M.Rep 𝔽 W) (hX : ¬ M.Indep X) :
--     ∃ c : α →₀ 𝔽, Finsupp.linearCombination 𝔽 v c = 0 ∧ (c.support : Set α) ⊆ X ∧ c ≠ 0 := by
--   rw [v.indep_iff'] at hX
--   simpa [v.indep_iff_forall_finsupp] using hX

lemma Rep.eq_zero_iff_not_indep {v : M.Rep 𝔽 W} : v e = 0 ↔ ¬ M.Indep {e} := by
  simp [v.indep_iff, linearIndependent_unique_iff, -indep_singleton]

lemma Rep.eq_zero_of_not_mem_ground (v : M.Rep 𝔽 W) (he : e ∉ M.E) : v e = 0 := by
  rw [v.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

lemma Rep.support_subset_ground (v : M.Rep 𝔽 W) : support v ⊆ M.E :=
  fun _ he ↦ by_contra <| fun h' ↦ he (v.eq_zero_of_not_mem_ground h')

lemma Rep.mem_ground_of_apply_ne_zero {v : M.Rep 𝔽 W} (hv : v e ≠ 0) : e ∈ M.E :=
  v.support_subset_ground hv

lemma Indep.rep_apply_ne_zero_of_mem {v : M.Rep 𝔽 W} (hI : M.Indep I) (heI : e ∈ I) :
    v e ≠ 0 := by
  rw [Ne, Rep.eq_zero_iff_not_indep, not_not]
  exact hI.subset (by simpa)

lemma Rep.closure_eq (v : M.Rep 𝔽 W) (X : Set α) : M.closure X = (v ⁻¹' span 𝔽 (v '' X)) ∩ M.E := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  ext e
  by_cases heI : e ∈ I
  · refine iff_of_true ?_ (mem_inter ?_ ?_)
    · exact mem_closure_of_mem' _ (hI.subset heI) (hI.indep.subset_ground heI)
    exact subset_span (mem_image_of_mem v (hI.subset heI))
    exact hI.indep.subset_ground heI
  simp only [← hI.closure_eq_closure, hI.indep.mem_closure_iff', v.indep_iff_restrict, restrict_def,
    linearIndependent_insert' heI, and_comm, heI, imp_false, not_and, mem_inter_iff, mem_preimage,
    SetLike.mem_coe, and_congr_right_iff]
  rw [← v.indep_iff', iff_true_intro hI.indep, not_true, imp_false, not_not]
  refine fun he ↦ ⟨fun h ↦ mem_of_mem_of_subset h (span_mono (image_subset v hI.subset)),
    fun h ↦ span_le.2 ?_ h⟩
  rintro _ ⟨f, hf, rfl⟩
  refine (em (f ∈ I)).elim (fun hfI ↦ subset_span <| mem_image_of_mem v hfI) (fun hfI ↦ ?_)
  have hni := hI.insert_not_indep ⟨hf, hfI⟩
  rwa [v.indep_iff_restrict, restrict_def, linearIndependent_insert' hfI, ← v.indep_iff',
    and_iff_right hI.indep, not_not] at hni

lemma Rep.mem_closure_iff (v : M.Rep 𝔽 W) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ v e ∈ span 𝔽 (v '' X) := by
  rw [v.closure_eq, mem_inter_iff, and_iff_left heE]
  rfl

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

lemma Rep.exists_finsupp_of_circuit (v : M.Rep 𝔽 W) {C : Finset α} (hC : M.Circuit C) :
    ∃ c : α →₀ 𝔽, c.support = C ∧ c.linearCombination 𝔽 v = 0 := by
  have hC' := hC.not_indep
  rw [v.indep_iff'] at hC'
  obtain ⟨c, h, hc, h0⟩ := linearDependent_comp_subtype'.1 hC'
  refine ⟨c, subset_antisymm (by simpa using h) fun e heC ↦ ?_, hc⟩
  contrapose! h0
  refine (linearIndependent_comp_subtype.1 <| v.indep_iff'.1 <| hC.diff_singleton_indep heC) _ ?_ hc
  simpa [Finsupp.mem_supported, subset_diff_singleton_iff, h0] using h

lemma Rep.span_le_of_closure_subset (v : M.Rep 𝔽 W) (hXY : M.closure X ⊆ M.closure Y) :
    span 𝔽 (v '' X) ≤ span 𝔽 (v '' Y) := by
  rw [span_le]
  rintro _ ⟨e, he, rfl⟩
  obtain heE | heE := em' (e ∈ M.E)
  · simp [v.eq_zero_of_not_mem_ground heE]
  rw [v.closure_eq Y] at hXY
  exact (hXY (M.mem_closure_of_mem' he heE)).1

lemma Rep.span_closure_congr (v : M.Rep 𝔽 W) (hXY : M.closure X = M.closure Y) :
    span 𝔽 (v '' X) = span 𝔽 (v '' Y) :=
  (v.span_le_of_closure_subset hXY.subset).antisymm (v.span_le_of_closure_subset hXY.symm.subset)
