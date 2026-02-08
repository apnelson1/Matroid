import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Path
import Mathlib.Geometry.Polygon.Basic
import Matroid.Graph.Subgraph.Lemma

variable {α β : Type*} {x y : EuclideanSpace ℝ (Fin 2)} {C L : List (EuclideanSpace ℝ (Fin 2))}
  {X Y : Set (EuclideanSpace ℝ (Fin 2))}

open Set Function

def List.drawing (L : List (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ x ∈ L.dropLast.zip L.tail, segment ℝ x.1 x.2

def List.cdrawing (C : List (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ x ∈ C.zip (C.rotate 1), segment ℝ x.1 x.2
  -- C.zip (C.rotate 1) |>.map (fun (x, y) ↦ segment ℝ x y) |>.foldl (· ∪ ·) ∅

-- def List.toPath (L : List (EuclideanSpace ℝ (Fin 2))) (hL : L ≠ []) : Path x y := by

lemma List.drawing_compact (L : List (EuclideanSpace ℝ (Fin 2))) : IsCompact (drawing L) := by
  simp only [drawing]
  induction L.dropLast.zip L.tail with
  | nil => simp
  | cons a as ih =>
    simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
    apply IsCompact.union _ ih
    rw [← convexHull_pair]
    apply Set.Finite.isCompact_convexHull
    simp

lemma List.cdrawing_compact (C : List (EuclideanSpace ℝ (Fin 2))) : IsCompact (cdrawing C) := by
  simp only [cdrawing]
  induction C.zip (C.rotate 1) with
  | nil => simp
  | cons a as ih =>
    simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
    apply IsCompact.union _ ih
    rw [← convexHull_pair]
    apply Set.Finite.isCompact_convexHull
    simp

noncomputable def t {N : ℕ} (hN : 0 < N) (i : Fin (N + 1)) : unitInterval :=
  ⟨(i : ℝ) / N, by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [div_le_one (Nat.cast_pos.mpr hN)]
      exact Nat.cast_le.mpr (Nat.le_of_lt_succ i.is_lt)⟩

lemma Path.exists_drawing_of_thickening (P : Path x y) {δ : ℝ} (hδ : 0 < δ) : ∃ L : List _,
    L.drawing ⊆ Metric.thickening δ (range P) ∧ L.head? = some x ∧ L.getLast? = some y := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.uniformContinuous_iff.mp P.uniformContinuous δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos : 0 < (N : ℝ) := lt_trans (by simpa) hN
  have hN' : 1 / ↑N < ε := (one_div_lt hεpos hNpos).mp hN
  let L : List (EuclideanSpace ℝ (Fin 2)) := List.ofFn (P ∘ (t <| by norm_cast at hNpos))
  use L, ?_, by simp [L, t], ?_
  · unfold List.drawing
    simp only [iUnion_subset_iff, Prod.forall]
    intro x y hxy
    have hdxy : dist x y < δ := 
      sorry
    have hx : x ∈ range P := by
      have hxL : x ∈ L := by
        sorry
      rw [List.mem_ofFn] at hxL
      obtain ⟨i, rfl⟩ := hxL
      simp
    refine subset_trans ?_ <| Metric.ball_subset_thickening hx _
    exact (convex_ball x δ).segment_subset (Metric.mem_ball_self hδ) (by simp [dist_comm, hdxy])
  unfold L
  rw [List.ofFn_succ_last]
  simp [t, div_self hNpos.ne']

lemma JoinedIn.exists_drawing (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ L : List _, L.drawing ⊆ X ∧ L.head? = some x ∧ L.getLast? = some y := by
  obtain ⟨P, hP⟩ := h
  have hPc : IsCompact (range P) := isCompact_range P.continuous
  have hPr : range ⇑P ⊆ X := by
    intro i hi
    simp only [mem_range, Subtype.exists] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    exact hP ⟨t, ht⟩
  obtain ⟨δ, hδpos, hδ⟩ := hPc.exists_thickening_subset_open hX hPr
  obtain ⟨L, hL, hLh, hLl⟩ := P.exists_drawing_of_thickening hδpos
  use L, hL.trans hδ, hLh, hLl

noncomputable def List.foo : List ℝ  → List ℝ
| [] => []
| [x] => [x]
| x :: y :: [] => [x, y]
| x :: y :: z :: L => by
  classical
  exact if Wbtw ℝ x y z then List.foo (x :: z :: L) else x :: List.foo (y :: z :: L)
