import Matroid.Representation.StandardRep

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
[DivisionRing R]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W'] [M.Finitary]


open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

namespace Matroid

/-- The intersection of `M.fundCircuit e B` with `B` as a `Finset B` in a finitary matroid. -/
noncomputable def Base.coords (hB : M.Base B) (e : α) : Finset B :=
  Finite.toFinset (s := (B ↓∩ M.fundCircuit e B))
  (by
    refine Finite.preimage Subtype.val_injective.injOn ?_
    by_cases heB : e ∈ B
    · rw [fundCircuit_eq_of_mem heB]
      simp
    by_cases heE : e ∈ M.E
    · exact (hB.fundCircuit_circuit heE heB).finite
    rw [fundCircuit_eq_of_not_mem_ground heE]
    simp )

lemma Base.coords_of_mem (hB : M.Base B) (he : e ∈ B) :
    hB.coords e = {⟨e, he⟩} := by
  ext ⟨x, hx⟩
  simp [coords, hB.subset_ground he, fundCircuit_eq_of_mem he]

lemma Base.coords_of_not_mem_ground (hB : M.Base B) (heE : e ∉ M.E) : hB.coords e = ∅ := by
  suffices ∀ a ∈ B, a ≠ e by
    simpa [coords, fundCircuit_eq_of_not_mem_ground heE, eq_empty_iff_forall_not_mem]
  rintro x hxB rfl
  exact heE <| hB.subset_ground hxB

lemma Base.coords_toSet (hB : M.Base B) : (hB.coords e : Set B) = B ↓∩ (M.fundCircuit e B) := by
  simp [coords]

lemma Base.fundCircuit_eq_insert_map [DecidableEq α] (hB : M.Base B) :
    M.fundCircuit e B = insert e ((hB.coords e).map (Embedding.setSubtype B)) := by
  by_cases heB : e ∈ B
  · simp [fundCircuit_eq_of_mem heB, Set.ext_iff, coords]
  simp [hB.coords_toSet, inter_comm B, ← fundCircuit_diff_eq_inter _ heB,
    insert_eq_of_mem (mem_fundCircuit ..)]

/-- The column of the `B`-fundamental matrix of `M` corresponding to `e`, as a `Finsupp`. -/
noncomputable def Base.fundCoord (hB : M.Base B) (R : Type*) [Semiring R] (e : α) :
    B →₀ R :=
  Finsupp.indicator (hB.coords e) (fun _ _ ↦ 1)

variable {R : Type*} [DivisionRing R]

lemma Base.fundCoord_of_mem (hB : M.Base B) (he : e ∈ B) :
    hB.fundCoord R e = Finsupp.single ⟨e, he⟩ 1 := by
  rw [fundCoord, coords_of_mem hB he, Finsupp.single_eq_indicator]

@[simp] lemma Base.fundCoord_mem (hB : M.Base B) (e : B) : hB.fundCoord R e = Finsupp.single e 1 :=
  hB.fundCoord_of_mem e.2

lemma Base.fundCoord_of_not_mem_ground (hB : M.Base B) (he : e ∉ M.E) :
    hB.fundCoord R e = 0 := by
  rw [fundCoord, coords_of_not_mem_ground hB he]
  rfl

lemma Base.support_fundCoord_subset (hB : M.Base B) : support (hB.fundCoord R) ⊆ M.E :=
  support_subset_iff'.2 fun _ ↦ hB.fundCoord_of_not_mem_ground

lemma Base.fundCoord_support (hB : M.Base B) :
    (↑) '' ((hB.fundCoord R e).support : Set B) = (M.fundCircuit e B) ∩ B := by
  simp [Set.ext_iff, fundCoord, Base.coords, Finsupp.indicator]

lemma Base.mem_fundCoord_support (hB : M.Base B) (e : B) {f : α} :
    e ∈ (hB.fundCoord R f).support ↔ e.1 ∈ M.fundCircuit f B := by
  rw [show e.1 ∈ M.fundCircuit f B ↔ e.1 ∈ (M.fundCircuit f B) ∩ B by simp [e.2],
    ← hB.fundCoord_support (R := R)]
  simp

lemma Base.fundCoord_base (hB : M.Base B) : (Matroid.ofFun R M.E (hB.fundCoord R)).Base B :=
  Finsupp.basisSingleOne.ofFun_base (by simp) hB.subset_ground

lemma Base.fundCoord_eq_linearCombination (hB : M.Base B) :
    hB.fundCoord R e = Finsupp.linearCombination R (Finsupp.single · 1) (hB.fundCoord R e) := by
  rw [Base.fundCoord, Finsupp.linearCombination_apply, Finsupp.indicator_eq_sum_single]
  simp

lemma Base.fundCoord_finitaryBase (hB : M.Base B) (R : Type*) [DivisionRing R] :
    (Matroid.repOfFun R M.E (hB.fundCoord R)).FinitaryBase := by
  intro e
  simp only [repOfFun_coeFun_eq]
  rw [indicator_of_mem (hB.subset_ground e.2), fundCoord_of_mem]

lemma fundCoord_fundCircuit (hB : M.Base B) (heB : e ∉ B) (heE : e ∈ M.E) :
    (Matroid.ofFun R M.E (hB.fundCoord R)).Circuit (M.fundCircuit e B) := by
  classical
  convert (hB.fundCoord_finitaryBase R).circuit_insert_support heB heE using 1
  rw [hB.fundCircuit_eq_insert_map]
  simp only [Finset.coe_insert, Finset.coe_map, Embedding.setSubtype_apply, repOfFun_coeFun_eq]
  convert rfl
  ext x
  simp only [Finsupp.mem_support_iff, ne_eq]
  rw [Set.indicator_of_mem heE]
  rw [Base.fundCoord]
  simp

lemma Base.fundCoord_row_support (hB : M.Base B) (R : Type*) [DivisionRing R] (e : B) :
    (hB.fundCoord R · e).support = M.fundCocircuit e B := by
  ext f
  simp only [mem_support]
  rw [← Finsupp.mem_support_iff, Base.mem_fundCoord_support,
    hB.mem_fundCocircuit_iff_mem_fundCircuit]
