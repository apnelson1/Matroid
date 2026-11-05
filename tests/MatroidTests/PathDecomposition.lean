module

public import Matroid.ForMathlib.Topology.PrimitiveLink

/-!
# Path excursion and two-subarc decomposition tests

The concrete paths below have an additional intersection, a whole shared subarc, or opposite
orientations. Parameter-specific tests retain the selected subpaths; geometric tests use the
`IsPrimitiveLink` decomposition and circuit API without unpacking parametrizations. No graph or
Jordan separation theorem is imported.
-/

open Set Function unitInterval

namespace PathDecompositionTests

noncomputable section

private def axis : Path ((0, 0) : ℝ × ℝ) (1, 0) where
  toFun t := ((t : ℝ), 0)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def twoDetours : Path ((0, 0) : ℝ × ℝ) (1, 0) where
  toFun t := ((t : ℝ), (t : ℝ) * (1 - t) * (t - 1 / 2))
  continuous_toFun := by fun_prop
  source' := by norm_num
  target' := by norm_num

private def sharedTail : Path ((0, 0) : ℝ × ℝ) (1, 0) where
  toFun t := ((t : ℝ), (t : ℝ) * max 0 ((1 / 2 : ℝ) - (t : ℝ)))
  continuous_toFun := by fun_prop
  source' := by norm_num
  target' := by norm_num

private lemma axis_injective : Injective axis :=
  fun _ _ h ↦ Subtype.ext (congrArg Prod.fst h)

private lemma twoDetours_injective : Injective twoDetours :=
  fun _ _ h ↦ Subtype.ext (congrArg Prod.fst h)

private lemma sharedTail_injective : Injective sharedTail :=
  fun _ _ h ↦ Subtype.ext (congrArg Prod.fst h)

private lemma axis_mem_twoDetours_iff (t : I) :
    axis t ∈ range twoDetours ↔ t = 0 ∨ t = half ∨ t = 1 := by
  constructor
  · rintro ⟨s, h⟩
    have hst : s = t := Subtype.ext (congrArg Prod.fst h)
    subst s
    have hy : (t : ℝ) * (1 - t) * (t - 1 / 2) = 0 := congrArg Prod.snd h
    rcases mul_eq_zero.mp hy with hy | hy
    · rcases mul_eq_zero.mp hy with hy | hy
      · exact Or.inl (Subtype.ext hy)
      exact Or.inr (Or.inr (Subtype.ext (by change (t : ℝ) = 1; linarith)))
    exact Or.inr (Or.inl (Subtype.ext (by change (t : ℝ) = 2⁻¹; linarith)))
  rintro (rfl | rfl | rfl)
  · exact ⟨0, by norm_num [axis, twoDetours]⟩
  · exact ⟨half, by norm_num [axis, twoDetours, half]⟩
  exact ⟨1, by norm_num [axis, twoDetours]⟩

-- An additional intersection produces separate excursions, not a false whole-path cycle.
example : (0, half) ∈ axis.excursions (range twoDetours) ∧
    (half, 1) ∈ axis.excursions (range twoDetours) := by
  have h0 := (axis_mem_twoDetours_iff 0).2 (Or.inl rfl)
  have hm := (axis_mem_twoDetours_iff half).2 (Or.inr (Or.inl rfl))
  have h1 := (axis_mem_twoDetours_iff 1).2 (Or.inr (Or.inr rfl))
  constructor
  · refine ⟨zero_lt_half, h0, hm, ?_⟩
    intro t ht hh
    rcases (axis_mem_twoDetours_iff t).mp hh with rfl | rfl | rfl <;>
      grind [half_lt_one]
  refine ⟨half_lt_one, hm, h1, ?_⟩
  intro t ht hh
  rcases (axis_mem_twoDetours_iff t).mp hh with rfl | rfl | rfl <;>
    grind [zero_lt_half]

private lemma quarter_mem_axis : ((1 / 4, 0) : ℝ × ℝ) ∈ range axis :=
  ⟨⟨1 / 4, by norm_num⟩, rfl⟩

private lemma quarter_notMem_twoDetours : ((1 / 4, 0) : ℝ × ℝ) ∉ range twoDetours := by
  rintro ⟨t, ht⟩
  have hx : (t : ℝ) = 1 / 4 := congrArg Prod.fst ht
  have hy : (t : ℝ) * (1 - t) * (t - 1 / 2) = 0 := congrArg Prod.snd ht
  norm_num [hx] at hy

-- The result exposes the actual subpath parameters, not just two arbitrary subsets.
example : ∃ u v s t : I, u < v ∧ s ≠ t ∧ axis u = twoDetours s ∧
    axis v = twoDetours t ∧ ((1 / 4, 0) : ℝ × ℝ) ∈ axis '' Ioo u v ∧
    range (axis.subpath u v) ∩ range (twoDetours.subpath s t) = {axis u, axis v} := by
  obtain ⟨u, v, s, t, huv, hs, ht, hc, -, hQ, hinter⟩ :=
    Path.exists_subpaths_inter_eq_pair axis_injective (.of_injective twoDetours_injective)
      ((isCompact_range twoDetours.continuous).isClosed.preimage axis.continuous)
      twoDetours.source_mem_range
      twoDetours.target_mem_range ⟨quarter_mem_axis, quarter_notMem_twoDetours⟩
  exact ⟨u, v, s, t, huv.1, (Path.injective_subpath_iff.mp hQ).1, hs, ht, hc, hinter⟩

-- Geometric decomposition exposes the sublinks and avoidance of the whole second arc.
example : ∃ u v, u ≠ v ∧ ∃ A ⊆ range axis, ∃ B ⊆ range twoDetours,
    IsPrimitiveLink A u v ∧ IsPrimitiveLink B v u ∧
    ((1 / 4, 0) : ℝ × ℝ) ∈ A \ {u, v} ∧
    A ∩ range twoDetours = {u, v} ∧ A ∩ B = {u, v} :=
  (IsPrimitiveLink.of_injective axis_injective).exists_sublinks_inter_eq_pair
    (.of_injective twoDetours_injective) (isCompact_range twoDetours.continuous).isClosed
    (by norm_num) twoDetours.source_mem_range twoDetours.target_mem_range
    ⟨quarter_mem_axis, quarter_notMem_twoDetours⟩

-- The circuit can be based at the selected point without unpacking a path witness.
example : ∃ C ⊆ range axis ∪ range twoDetours,
    IsPrimitiveLink C ((1 / 4, 0) : ℝ × ℝ) (1 / 4, 0) := by
  obtain ⟨C, hsub, hC, hc⟩ :=
    (IsPrimitiveLink.of_injective axis_injective).exists_isCircuit_of_mem_diff
      (.of_injective twoDetours_injective) (isCompact_range twoDetours.continuous).isClosed
      twoDetours.source_mem_range twoDetours.target_mem_range
      ⟨quarter_mem_axis, quarter_notMem_twoDetours⟩
  exact ⟨C, hsub, isPrimitiveLink_iff_isCircuit.mpr ⟨hC, hc⟩⟩

-- Reversing the second link changes its endpoint indices, not the geometric conclusion.
example : ∃ C ⊆ range axis ∪ range twoDetours,
    IsCircuit C ∧ ((1 / 4, 0) : ℝ × ℝ) ∈ C :=
  (IsPrimitiveLink.of_injective axis_injective).exists_isCircuit_of_mem_diff
    (IsPrimitiveLink.of_injective twoDetours_injective).symm
    (isCompact_range twoDetours.continuous).isClosed twoDetours.source_mem_range
    twoDetours.target_mem_range ⟨quarter_mem_axis, quarter_notMem_twoDetours⟩

-- Distinct sets with common endpoints produce a circuit, without selecting a point first.
example : ∃ C ⊆ range axis ∪ range twoDetours, IsCircuit C := by
  apply (IsPrimitiveLink.of_injective axis_injective).exists_isCircuit_of_ne
    (.of_injective twoDetours_injective) (isCompact_range axis.continuous).isClosed
    (isCompact_range twoDetours.continuous).isClosed
  intro h
  exact quarter_notMem_twoDetours (h ▸ quarter_mem_axis)

-- The images can agree on a whole subarc: no finite-intersection hypothesis is available.
example : axis '' Icc half 1 ⊆ range sharedTail := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t, ?_⟩
  have hhalf : (1 / 2 : ℝ) ≤ t := by
    simpa only [one_div] using (show (2⁻¹ : ℝ) ≤ (t : ℝ) from ht.1)
  have hmax : max (0 : ℝ) ((1 / 2 : ℝ) - (t : ℝ)) = 0 := max_eq_left (by linarith)
  change ((t : ℝ), (t : ℝ) * max 0 ((1 / 2 : ℝ) - (t : ℝ))) = ((t : ℝ), 0)
  rw [hmax, mul_zero]

example : ∃ C ⊆ range axis ∪ range sharedTail,
    IsCircuit C ∧ ((1 / 4, 0) : ℝ × ℝ) ∈ C := by
  apply (IsPrimitiveLink.of_injective axis_injective).exists_isCircuit_of_mem_diff
    (.of_injective sharedTail_injective) (isCompact_range sharedTail.continuous).isClosed
    sharedTail.source_mem_range sharedTail.target_mem_range
  refine ⟨quarter_mem_axis, ?_⟩
  rintro ⟨t, ht⟩
  have hx : (t : ℝ) = 1 / 4 := congrArg Prod.fst ht
  have hy : (t : ℝ) * max 0 ((1 / 2 : ℝ) - (t : ℝ)) = 0 := congrArg Prod.snd ht
  norm_num [hx] at hy

-- Equal images have no excursions; reparametrizing an arc does not manufacture a circle.
example : axis.excursions (range axis) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro uv huv
  obtain ⟨t, ht⟩ := exists_between huv.1
  exact huv.2.2.2 t ht (mem_range_self t)

-- The global decomposition applies to arbitrary paths, not just injective ones.
example {X : Type*} [TopologicalSpace X] {x y : X} (P : Path x y) {S : Set X}
    (hS : IsClosed S) (hx : x ∈ S) (hy : y ∈ S) :
    range P \ S = ⋃ uv ∈ P.excursions S, P '' Ioo uv.1 uv.2 :=
  P.range_diff_eq_biUnion_excursions (hS.preimage P.continuous) hx hy

example {X : Type*} [TopologicalSpace X] {x y : X} (P : Path x y) (S : Set X) :
    (P.excursions S).Countable ∧
      (P.excursions S).PairwiseDisjoint (fun uv ↦ Ioo uv.1 uv.2) :=
  ⟨P.countable_excursions S, P.excursions_pairwiseDisjoint S⟩

end

end PathDecompositionTests

#print axioms Path.exists_mem_excursions
#print axioms Path.preimage_compl_eq_biUnion_excursions
#print axioms Path.range_diff_eq_biUnion_excursions
#print axioms Path.exists_subpaths_inter_eq_pair
#print axioms IsPrimitiveLink.exists_sublinks_inter_eq_pair
#print axioms IsPrimitiveLink.exists_isCircuit_of_mem_diff
#print axioms IsPrimitiveLink.exists_isCircuit_of_ne
