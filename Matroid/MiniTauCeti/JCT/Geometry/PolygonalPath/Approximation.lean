module

public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.Basic
public import Matroid.ForMathlib.List.Basic
public import Mathlib.Topology.UniformSpace.Path
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Approximating paths by polygonal paths

Uniform continuity turns any path into a polygonal path with the same endpoints staying inside any
given thickening of its image, and hence inside any open set containing the image. The construction
samples the path at a sufficiently fine uniform partition and joins consecutive samples.

## Main statements

* `Path.polygonalSample` and `Path.exists_polygonalSample_subset_thickening`
* `JoinedIn.exists_polygonalPath_of_open`
* `JoinedIn.exists_isSimple_polygonalPath_of_open`
-/

@[expose] public section

open Set Function

namespace Path

variable {α : Type*} [TopologicalSpace α] {x y : α}

/-- The `i`-th internal parameter of a uniform partition with `n + 1` intervals. -/
noncomputable def polygonalSampleTime (n : ℕ) (i : Fin n) : unitInterval :=
  ⟨((i : ℝ) + 1) / (n + 1),
    div_nonneg (by positivity) (by positivity),
    (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.succ_le_succ i.isLt.le)⟩

/-- Join the endpoints through the `n` uniformly spaced internal samples of `P`. -/
noncomputable def polygonalSample (P : Path x y) (n : ℕ) : PolygonalPath x y :=
  PolygonalPath.ofList x (List.ofFn fun i : Fin n ↦ P (polygonalSampleTime n i)) y

@[simp] lemma polygonalSample_zero (P : Path x y) :
    P.polygonalSample 0 = PolygonalPath.direct x y := rfl

@[simp] lemma polygonalSample_length (P : Path x y) (n : ℕ) :
    (P.polygonalSample n).length = n + 1 := by simp [polygonalSample]

lemma polygonalSample_vertices (P : Path x y) (n : ℕ) :
    (P.polygonalSample n).vertices =
      x :: (List.ofFn fun i : Fin n ↦ P (polygonalSampleTime n i)) ++ [y] := by
  simp [polygonalSample]

@[simp] lemma polygonalSample_internal (P : Path x y) (n : ℕ) :
    (P.polygonalSample n).internal =
      List.ofFn fun i : Fin n ↦ P (polygonalSampleTime n i) := by
  simp [polygonalSample]

@[simp] lemma polygonalSample_internal_get (P : Path x y) (n : ℕ) (i : Fin n) :
    (P.polygonalSample n).internal[i.val]'(by simp [polygonalSample]) =
      P (polygonalSampleTime n i) := by simp

end Path

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

/-- Uniform control at the sampling mesh keeps the specified sample inside a thickening. -/
lemma _root_.Path.polygonalSample_subset_thickening (P : Path x y) (n : ℕ) {δ : ℝ}
    (hmesh : ∀ s t : unitInterval,
      dist s t ≤ 1 / ((n : ℝ) + 1) → dist (P s) (P t) < δ) :
    (P.polygonalSample n).toSet ⊆ Metric.thickening δ (range P) := by
  have hδ : 0 < δ := by
    simpa using hmesh 0 0 (by simp only [dist_self]; positivity)
  let N := n + 1
  have hNpos : 0 < N := Nat.succ_pos n
  set L : List α := (uniform hNpos).map P with hL
  have hsample : P.polygonalSample n = ofList x L.tail.dropLast y := by
    unfold Path.polygonalSample
    congr 1
    apply List.ext_getElem
    · simp [L, N]
    intro i hi₁ hi₂
    simp only [List.getElem_ofFn, List.getElem_dropLast, List.getElem_tail]
    simp only [L, uniform, List.getElem_map, ← List.ofFn_id, List.getElem_ofFn]
    congr 1
    apply Subtype.ext
    simp [Path.polygonalSampleTime, N, Nat.cast_add, Nat.cast_one]
  rw [hsample]
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
    exact (uniform_isChain hNpos).imp fun a b hab ↦ hmesh a b
      (by rw [hab]; simp [N, Nat.cast_add, Nat.cast_one])
  rw [List.isChain_iff_all_zip_tail] at hchain
  have hdist := by simpa using hchain _ hab
  have hseg : segment ℝ a b ⊆ Metric.ball b δ :=
    (convex_ball b δ).segment_subset (by simpa) (by simpa)
  simpa using hseg hq

/-- Any path can be approximated to within `δ` by a polygonal sample with the same endpoints. -/
lemma _root_.Path.exists_polygonalSample_subset_thickening (P : Path x y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, (P.polygonalSample n).toSet ⊆ Metric.thickening δ (range P) := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.uniformContinuous_iff.mp P.uniformContinuous δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hN : 1 / ε < (n : ℝ) + 1 := by linarith
  have hstep : 1 / ((n : ℝ) + 1) < ε :=
    (one_div_lt hεpos (by positivity)).mp hN
  exact ⟨n, P.polygonalSample_subset_thickening n fun _ _ hst ↦ hε (hst.trans_lt hstep)⟩

/-- Two points joined by a path inside an open set are joined by a polygonal path inside it. -/
lemma _root_.JoinedIn.exists_polygonalPath_of_open (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ P : PolygonalPath x y, P.toSet ⊆ X := by
  obtain ⟨P, hP⟩ := h
  have hPc : IsCompact (range P) := isCompact_range P.continuous
  have hPr : range P ⊆ X := by
    rintro q ⟨t, rfl⟩
    exact hP t
  obtain ⟨δ, hδpos, hδ⟩ := hPc.exists_thickening_subset_open hX hPr
  obtain ⟨n, hn⟩ := P.exists_polygonalSample_subset_thickening hδpos
  exact ⟨P.polygonalSample n, hn.trans hδ⟩

/-- Two points joined inside an open set have a simple polygonal representative inside it. -/
lemma _root_.JoinedIn.exists_isSimple_polygonalPath_of_open (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ P : PolygonalPath x y, P.IsSimple ∧ P.toSet ⊆ X := by
  obtain ⟨P, hPX⟩ := h.exists_polygonalPath_of_open hX
  exact ⟨P.simpleArc, P.isSimple_simpleArc, P.toSet_simpleArc_subset.trans hPX⟩

end Normed

end PolygonalPath
