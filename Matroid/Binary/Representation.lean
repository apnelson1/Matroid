import Matroid.Representation.Projective
import Matroid.Representation.FundamentalMatrix
import Matroid.Binary.Crossing
import Matroid.Order.Quotient


variable {α β W W' 𝔽 R ι : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
[DivisionRing R] [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

@[simp] lemma ne_one_iff {x : ZMod 2} : x ≠ 1 ↔ x = 0 := by
  induction' x using Fin.cases with x hx
  · simp
  obtain rfl : x = 0 := by exact Fin.fin_one_eq_zero x
  simp

@[simp] lemma ne_zero_iff {x : ZMod 2} : x ≠ 0 ↔ x = 1 := by
  rw [not_iff_comm, ← ne_one_iff]

namespace Matroid

/-- If every row of the submatrix induced by `C` has even support, then `C` is cyclic. -/
lemma Rep.cyclic_of_forall_row_even {C : Finset α} (v : M.Rep (ZMod 2) (ι →₀ ZMod 2))
    (hCE : (C : Set α) ⊆ M.E) (h_even : ∀ i, Even {x ∈ C | v x i = 1}.card) : M.Cyclic C := by
  classical
  convert v.cyclic_of_linearCombination (Finsupp.indicator C (fun _ _ ↦ 1))
    (fun x hx ↦ hCE <| by simpa using hx) ?_
  · ext
    simp
  ext i
  suffices ∑ x ∈ C.attach, v ↑x i = 0 by simpa [Finsupp.linearCombination]
  rw [C.sum_attach (f := fun x ↦ (v x) i), ← C.sum_filter_of_ne (p := fun x ↦ (v x) i = 1),
    Finset.sum_congr rfl (g := fun _ ↦ 1) (by simp)]
  · simp [ZMod.eq_zero_iff_even.2 (h_even i)]
  simp

/-- If `C` is a circuit, then every row of the corresponding submatrix has even support. -/
lemma Rep.row_even_of_isCircuit (v : M.Rep (ZMod 2) (ι →₀ ZMod 2)) {C : Finset α} (hC : M.IsCircuit C)
    (i : ι) : Even {x ∈ C | v x i = 1}.card := by
  obtain ⟨c, rfl, hc⟩ := v.exists_finsupp_of_isCircuit hC
  apply_fun fun f ↦ f i at hc
  replace hc := show ∑ x ∈ c.support, c x * (v x) i = 0 by
    simpa [Finsupp.linearCombination, Finsupp.sum] using hc
  rw [← Finset.sum_filter_of_ne (p := fun x ↦ (v x) i = 1),
    Finset.sum_congr rfl (g := 1)] at hc
  · exact ZMod.eq_zero_iff_even.mp (by simpa using hc)
  · simp
  simp

variable [Finitary M] {C : Set α}

/-- The Binary matroid that should be `M`. -/
def IsBase.BinaryProxy (hB : M.IsBase B) := (Matroid.ofFun (ZMod 2) M.E (hB.fundCoord (ZMod 2)))

noncomputable def IsBase.binaryProxyRep (hB : M.IsBase B) :
    (hB.BinaryProxy.Rep (ZMod 2) (B →₀ ZMod 2)) :=
  repOfFun (ZMod 2) M.E (hB.fundCoord (ZMod 2))

instance {hB : M.IsBase B} : hB.BinaryProxy.Finitary :=
  matroidOfFun_finitary ..

lemma IsBase.binaryProxyRep_finitaryBase (hB : M.IsBase B) : hB.binaryProxyRep.FinitaryBase := by
  apply hB.fundCoord_finitaryBase

lemma Binary.eq_binaryProxy (hM : M.Binary) (hB : M.IsBase B) :
    M = hB.BinaryProxy := by
  refine Eq.symm <| Quotient.eq_of_isBase_indep ?_ hB hB.fundCoord_isBase.indep
  refine quotient_of_forall_cyclic_of_isCircuit rfl fun C hC ↦ ?_
  obtain ⟨C, rfl⟩ := hC.finite.exists_finset_coe
  refine hB.binaryProxyRep.cyclic_of_forall_row_even hC.subset_ground fun e ↦ ?_
  have hcc := M.fundCocircuit_cocircuit e.2 hB

  rw [← hB.fundCoord_row_support (ZMod 2) e] at hcc
  convert hM.even_of_finite (hC.crossing_inter hcc) (hC.finite.subset (by simp))
  ext x
  simp only [Base.binaryProxyRep, Finset.mem_filter, Finite.mem_toFinset, mem_inter_iff,
    Finset.mem_coe, mem_support, ne_eq, ne_zero_iff, and_congr_right_iff]
  intro hxC
  rw [repOfFun_coeFun_eq, indicator_of_mem (hC.subset_ground hxC)]

theorem representable_iff_no_U24_minor : M.Representable (ZMod 2) ↔ M.NoUniformMinor 2 4 := by
  refine ⟨fun h ↦ by simpa using h.noUniformMinor, fun h ↦ ?_⟩
  rw [← binary_iff_no_U24_minor] at h
  obtain ⟨B, hB⟩ := M.exists_isBase
  exact (hB.binaryProxyRep.ofEq (h.eq_binaryProxy hB).symm).representable

theorem binary_iff_representable : M.Binary ↔ M.Representable (ZMod 2) := by
  rw [binary_iff_no_U24_minor, representable_iff_no_U24_minor]
