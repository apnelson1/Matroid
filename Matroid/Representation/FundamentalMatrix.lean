import Mathlib.LinearAlgebra.LinearIndependent
import Matroid.Simple
import Matroid.Representation.StandardRep
import Matroid.Binary.Crossing
import Matroid.Order.Quotient
import Mathlib.Data.Finsupp.Indicator

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
[DivisionRing R]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] [M.Finitary]

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

namespace Matroid

/-- The intersection of `M.fundCircuit e B` with `B` as a `Finset B` in a finitary matroid.
Defined hackishly to equal `{e}` for `e ∈ B`, and equal `∅` if `e ∉ M.e` -/
noncomputable def Base.fundCircuit_finset_inter (hB : M.Base B) (e : α) : Finset B :=
  Finite.toFinset (s := (B ↓∩ M.fundCircuit e B) ∩ {x | e ∈ M.E})
  (by
    by_cases heE : e ∈ M.E
    · refine Finite.inter_of_left (Finite.preimage Subtype.val_injective.injOn ?_) _
      by_cases heB : e ∈ B
      · simp [fundCircuit_eq_of_mem heB]
      exact (hB.fundCircuit_circuit heE heB).finite
    simp [heE])

lemma Base.fundCircuit_finset_inter_of_mem (hB : M.Base B) (he : e ∈ B) :
    hB.fundCircuit_finset_inter e = {⟨e, he⟩} := by
  ext ⟨x, hx⟩
  simp [fundCircuit_finset_inter, hB.subset_ground he, fundCircuit_eq_of_mem' he]

lemma Base.fundCircuit_finset_inter_of_not_mem_ground (hB : M.Base B) (heE : e ∉ M.E) :
    hB.fundCircuit_finset_inter e = ∅ := by
  ext ⟨x, hx⟩
  simp [fundCircuit_finset_inter, heE]

lemma Base.fundCircuit_finset_inter_toSet (hB : M.Base B) (heE : e ∈ M.E) :
    (hB.fundCircuit_finset_inter e : Set B) = B ↓∩ (M.fundCircuit e B) := by
  simp [fundCircuit_finset_inter, heE]

lemma Base.fundCircuit_eq_insert_map [DecidableEq α] (hB : M.Base B) (heE : e ∈ M.E) :
    M.fundCircuit e B = insert e ((hB.fundCircuit_finset_inter e).map (Embedding.setSubtype B)) :=
    by
  simp only [Finset.coe_insert, Finset.coe_map, Embedding.setSubtype_apply,
    hB.fundCircuit_finset_inter_toSet heE]
  ext x
  simp only [fundCircuit_eq_sInter <| show e ∈ M.closure B by rwa [hB.closure_eq], mem_insert_iff,
    mem_sInter, mem_setOf_eq, and_imp, Subtype.image_preimage_coe, mem_inter_iff]
  by_cases hxB : x ∈ B
  · simp [hxB]
  simp only [hxB, false_and, or_false, or_iff_left_iff_imp]
  exact fun h ↦ False.elim <| hxB (h _ rfl.subset (by rwa [hB.closure_eq]))

/-- The column of the `B`-fundamental matrix of `M` corresponding to `e`, as a `Finsupp`. -/
noncomputable def Base.fundCoord (hB : M.Base B) (R : Type*) [Semiring R] (e : α) :
    B →₀ R :=
  Finsupp.indicator (hB.fundCircuit_finset_inter e) (fun _ _ ↦ 1)

variable {R : Type*} [DivisionRing R]

lemma Base.fundCoord_of_mem (hB : M.Base B) (he : e ∈ B) :
    hB.fundCoord R e = Finsupp.single ⟨e, he⟩ 1 := by
  rw [fundCoord, fundCircuit_finset_inter_of_mem hB he, Finsupp.single_eq_indicator]

@[simp] lemma Base.fundCoord_mem (hB : M.Base B) (e : B) : hB.fundCoord R e = Finsupp.single e 1 :=
  hB.fundCoord_of_mem e.2

lemma Base.fundCoord_of_not_mem_ground (hB : M.Base B) (he : e ∉ M.E) :
    hB.fundCoord R e = 0 := by
  rw [fundCoord, fundCircuit_finset_inter_of_not_mem_ground hB he]
  rfl

-- lemma Base.fundCoord_eqOn (hB : M.Base B) : EqOn (hB.fundCoord R) (Finsupp)

-- lemma Base.support_fundCoord_toSet (hB : M.Base B) (he : e ∈ M.E) :
--     (Finsupp.support (hB.fundCoord R e) : Set α) = (M.fundCircuit e B) ∩ B := by
--   sorry


lemma Base.support_fundCoord_subset (hB : M.Base B) : support (hB.fundCoord R) ⊆ M.E :=
  support_subset_iff'.2 fun _ ↦ hB.fundCoord_of_not_mem_ground

lemma Base.fundCoord_base (hB : M.Base B) : (Matroid.ofFun R M.E (hB.fundCoord R)).Base B :=
  Finsupp.basisSingleOne.ofFun_base (by simp) hB.subset_ground

lemma Base.fundCoord_eq_linearCombination (hB : M.Base B) :
    hB.fundCoord R e = Finsupp.linearCombination R (Finsupp.single · 1) (hB.fundCoord R e) := by
  rw [Base.fundCoord, Finsupp.linearCombination_apply, Finsupp.indicator_eq_sum_single]
  simp

-- theorem Finsupp.mem_span_iff_linearCombinationOn {M α : Type*} (R : Type*) [Semiring R]
--     [AddCommMonoid M] [Module R M] {v : α → M} (s : Set α) (x : M) :
--     x ∈ Submodule.span R (v '' s) ↔ ∃ l, Finsupp.linearCombinationOn α M R v s l = x := by
--   _

lemma funCoord_fundCircuit (hB : M.Base B) (heB : e ∉ B) (heE : e ∈ M.E) :
    (Matroid.ofFun R M.E (hB.fundCoord R)).Circuit (M.fundCircuit e B) := by
  classical
  simp_rw [hB.fundCircuit_eq_insert_map heE, Finset.coe_insert, Finset.coe_map,
    Embedding.setSubtype_apply]
  refine Indep.insert_circuit_of_forall ?_ ?_ ?_ ?_
  · exact hB.fundCoord_base.indep.subset (by simp)
  · simp [heB]
  · rw [hB.fundCircuit_finset_inter_toSet heE, Matroid.ofFun_closure_eq hB.support_fundCoord_subset,
      mem_inter_iff, and_iff_left heE, Subtype.image_preimage_coe, mem_preimage, SetLike.mem_coe,
      Finsupp.mem_span_image_iff_linearCombination, hB.fundCoord_eq_linearCombination]
    refine ⟨(hB.fundCoord R e).embDomain (Embedding.setSubtype B), ?_, ?_⟩
    · simp only [Base.fundCoord, Finsupp.mem_supported, Finsupp.support_embDomain, Finset.coe_map,
        Embedding.setSubtype_apply, subset_inter_iff, image_subset_iff, Subtype.coe_preimage_self,
        subset_univ, true_and]
      refine (Finsupp.support_indicator_subset ..).trans ?_
      rw [hB.fundCircuit_finset_inter_toSet heE]
    simp only [Finsupp.linearCombination_embDomain]
    convert rfl with _ x
    simp
  simp
  -- rw [fundCircuit_eq_sInter (by rwa [hB.closure_eq])]
  -- refine Indep.insert_circuit_of_forall ?_ ?_ ?_ ?_
  -- · exact hB.fundCoord_base.indep.subset inter_subset_left
  -- · simp [heB]
  -- · rw [ofFun_closure_eq_of_subset_ground (inter_subset_left.trans hB.subset_ground),
  --     mem_inter_iff, and_iff_left heE]
  --   simp
  --   rw [hB.fundCoord_eq_linearCombination, Finsupp.mem_span_image_iff_linearCombination]
  --   use (hB.fundCoord R e).embDomain (Embedding.setSubtype B)
  --   rw [Base.fundCoord]
  --   simp






  -- have := (Finsupp.basisSingleOne (ι := B) (R := R)).ofFun_base (E := M.E) (v := hB.fundCoord R)
  -- refine Indep.base_of_ground_subset_closure ?_ ?_
  -- · rw [ofFun_indep_iff, and_iff_left hB.subset_ground]
  --   convert (Finsupp.basisSingleOne (ι := B) (R := R)).linearIndependent
  --   ext ⟨i, hi⟩ ⟨j, hj⟩
  --   simp [hB.fundCoord_of_mem hi]
  -- rw [ofFun_ground_eq, ofFun_closure_eq (hB.support_fundCoord_subset)]
