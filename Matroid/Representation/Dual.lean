module

public import Matroid.Representation.StandardRep
public import Matroid.Order.Quotient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic -- inefficient import
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs -- inefficient import

@[expose] public section

-- Experiments with getting duality to work nicely.

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Function Submodule

namespace Matroid

lemma ofFun_comp_quotient (v : α → W) (ψ : W →ₗ[𝔽] W') (E : Set α) :
    Matroid.ofFun 𝔽 E (ψ ∘ v) ≤q Matroid.ofFun 𝔽 E v := by
  wlog h : v.support ⊆ E generalizing v with aux
  · rw [← ofFun_indicator, ← ofFun_indicator (v := v), indicator_comp_of_zero (by simp)]
    exact aux _ (by simp)
  refine quotient_of_forall_closure_subset_closure rfl fun X (hX : X ⊆ E) ↦ ?_
  rw [ofFun_closure_eq h, ofFun_closure_eq_of_subset_ground hX, preimage_comp, image_comp]
  refine inter_subset_inter_left _ <| preimage_mono ?_
  rw [← image_subset_iff]
  exact Submodule.image_span_subset_span ψ (v '' X)

/-- Build a matroid on `α ⊕ β` represented by an `α × β` matrix where `α` is a basis
and `β` is a cobasis. -/
def ofReducedMatrix {m n : Type*} [DecidableEq m] (P : n → m → 𝔽) : Matroid (m ⊕ n) :=
    Matroid.ofFun 𝔽 univ (Sum.elim (Pi.single · 1) P)




lemma foo (M : Matroid α) [Finitary M] [DecidableEq α] (hB : M.IsBase B) (hM : M.Representable 𝔽) :
    ∃ P : ↥(M.E \ B) → B → 𝔽,
      M = (ofReducedMatrix P).mapEmbedding (Embedding.sumSet disjoint_sdiff_right) := by
  obtain ⟨v, hv⟩ := hM.exists_isStandard_rep hB
  use fun x y ↦ v x y
  refine ext_indep ?_ ?_
  · suffices M.E = B ∪ {x | x ∈ M.E ∧ x ∉ B} by simpa [ofReducedMatrix]
    simp [← mem_sdiff, union_eq_self_of_subset_left hB.subset_ground]
  simp only [ofReducedMatrix, mapEmbedding_indep_iff, ofFun_indep_iff, subset_univ, and_true,
    Embedding.sumSet_range, union_sdiff_self]
  intro I hIE
  rw [v.indep_iff]
  sorry
