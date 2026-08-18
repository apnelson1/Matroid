module

public import Matroid.ForMathlib.Geometry.PolygonalPath.Basic
public import Matroid.ForMathlib.List.Basic
public import Mathlib.Topology.UniformSpace.Path
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Approximating paths by polygonal paths

Uniform continuity turns any path into a polygonal path with the same endpoints staying inside any
given thickening of its image, and hence inside any open set containing the image. The construction
samples the path at a sufficiently fine uniform partition and joins consecutive samples.

## Main statements

* `Path.exists_polygonalPath_of_thickening`
* `JoinedIn.exists_polygonalPath_of_open`
* `JoinedIn.exists_isSimple_polygonalPath_of_open`
-/

@[expose] public section

open Set Function

namespace PolygonalPath

variable {α : Type*} {x y : α}

/-! ### Approximating paths by polygonal paths -/

section Normed

variable [SeminormedAddCommGroup α] [NormedSpace ℝ α] {X : Set α} {N : ℕ}

private noncomputable def uniform (hN : 0 < N) : List unitInterval :=
  List.finRange (N + 1) |>.map (fun (i : Fin (N + 1)) => ⟨(i : ℝ) / N,
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), by
    rw [div_le_one (Nat.cast_pos.mpr hN)]
    exact Nat.cast_le.mpr (Nat.le_of_lt_succ i.is_lt)⟩)

@[simp] private lemma uniform_head? (hN : 0 < N) : (uniform hN).head? = some 0 := by
  simp [uniform, List.finRange]

@[simp] private lemma uniform_getLast? (hN : 0 < N) : (uniform hN).getLast? = some 1 := by
  rw [uniform, List.finRange_succ_last]
  simp [hN.ne']

@[simp] private lemma uniform_length (hN : 0 < N) : (uniform hN).length = N + 1 := by
  simp [uniform]

@[simp] private lemma uniform_isChain (hN : 0 < N) :
    (uniform hN).IsChain (dist · · = 1 / N) := by
  simp only [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, one_div, uniform,
    List.finRange_eq_pmap_range, List.isChain_map, List.isChain_pmap, Order.lt_add_one_iff,
    exists_prop, List.isChain_and_iff, List.isChain_range, add_tsub_cancel_right,
    Nat.succ_eq_add_one, Order.add_one_le_iff, imp_self, implies_true, Nat.cast_add, Nat.cast_one,
    true_and]
  simp +contextual only [le_of_lt, implies_true, true_and]
  intro m hmN
  simp [div_sub_div_same, abs_div]

private lemma uniform_eq_cons_concat (hN : 0 < N) :
    uniform hN = 0 :: (uniform hN).tail.dropLast ++ [1] := by
  rw [List.cons_append]
  rw [List.dropLast_append_getLast?, List.cons_head?_tail (by simp)]
  rw [List.getLast?_tail]
  simp [hN.ne']

/-- Any path can be approximated to within `δ` by a polygonal path with the same endpoints. -/
lemma _root_.Path.exists_polygonalPath_of_thickening (P : Path x y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : PolygonalPath x y, L.toSet ⊆ Metric.thickening δ (range P) := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.uniformContinuous_iff.mp P.uniformContinuous δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos' : 0 < (N : ℝ) := lt_trans (by simpa) hN
  have hNpos : 0 < N := by norm_cast at hNpos'
  have hN' : 1 / (N : ℝ) < ε := (one_div_lt hεpos hNpos').mp hN
  set L : List α := (uniform hNpos).map P with hL
  use ofList x L.tail.dropLast y
  have hxLy : L = x :: L.tail.dropLast ++ [y] := by
    rw [hL, uniform_eq_cons_concat hNpos]
    simp
  have hpos : 0 < (ofList x L.tail.dropLast y).length := by simp
  rw [toSet_eq_biUnion (P := ofList x L.tail.dropLast y) hpos]
  simp only [edges_eq_zip, ofList_vertices, ← hxLy, iUnion_subset_iff, Prod.forall]
  refine fun a b hab q hq => Metric.mem_thickening_iff.mpr ⟨b, ?_, ?_⟩
  · simp only [Set.mem_range, Subtype.exists, mem_Icc]
    obtain ⟨i, hi, -, hhi⟩ := by
      simpa [L] using List.mem_of_mem_tail (List.of_mem_zip hab |>.2)
    exact ⟨i, hi, hhi⟩
  have hchain : L.IsChain (dist · · < δ) := by
    unfold L
    rw [List.isChain_map]
    exact (uniform_isChain hNpos).imp fun a b hab => hε (by rw [hab]; exact hN')
  rw [List.isChain_iff_all_zip_tail] at hchain
  have hdist := by simpa using hchain _ hab
  have hseg : segment ℝ a b ⊆ Metric.ball b δ :=
    (convex_ball b δ).segment_subset (by simpa) (by simpa)
  simpa using hseg hq

/-- Two points joined by a path inside an open set are joined by a polygonal path inside it. -/
lemma _root_.JoinedIn.exists_polygonalPath_of_open (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ P : PolygonalPath x y, P.toSet ⊆ X := by
  obtain ⟨P, hP⟩ := h
  have hPc : IsCompact (range P) := isCompact_range P.continuous
  have hPr : range P ⊆ X := by
    rintro q ⟨t, rfl⟩
    exact hP t
  obtain ⟨δ, hδpos, hδ⟩ := hPc.exists_thickening_subset_open hX hPr
  obtain ⟨L, hL⟩ := P.exists_polygonalPath_of_thickening hδpos
  exact ⟨L, hL.trans hδ⟩

/-- ... and by a *simple* polygonal path, by `exists_isSimple_toSet_subset`. -/
lemma _root_.JoinedIn.exists_isSimple_polygonalPath_of_open (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ P : PolygonalPath x y, P.IsSimple ∧ P.toSet ⊆ X := by
  obtain ⟨P, hPX⟩ := h.exists_polygonalPath_of_open hX
  obtain ⟨Q, hQ, hQP⟩ := P.exists_isSimple_toSet_subset
  exact ⟨Q, hQ, hQP.trans hPX⟩

end Normed

end PolygonalPath
