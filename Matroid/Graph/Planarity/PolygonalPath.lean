import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Path
import Matroid.ForMathlib.List

variable {α β : Type*} {x y z w : EuclideanSpace ℝ (Fin 2)} {C L : List (EuclideanSpace ℝ (Fin 2))}
  {X Y : Set (EuclideanSpace ℝ (Fin 2))} {N : ℕ}

open Set Function TopologicalSpace Topology List Metric

inductive PolygonalPath : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Type* where
| direct (x y : EuclideanSpace ℝ (Fin 2)) : PolygonalPath x y
| cons (a b : EuclideanSpace ℝ (Fin 2)) {c} (as : PolygonalPath b c) :
  PolygonalPath a c

namespace PolygonalPath

def ofList (x) (L : List (EuclideanSpace ℝ (Fin 2))) (y) : PolygonalPath x y :=
  match L with
  | [] => direct x y
  | a :: as => cons x a (ofList a as y)

-- Get all vertices including start and end
@[simp]
def vertices : ∀ {x y : _}, PolygonalPath x y → List (EuclideanSpace ℝ (Fin 2))
  | a, b, direct _ _ => [a, b]
  | _, _, cons a _ as => a :: as.vertices

lemma two_le_vertices_length (P : PolygonalPath x y) : 2 ≤ P.vertices.length := by
  induction P with
  | direct _ _ => simp [vertices]
  | cons _ _ as ih =>
    simp only [vertices, length_cons, Nat.reduceLeDiff]
    omega

@[simp]
lemma vertices_ne_nil (P : PolygonalPath x y) : P.vertices ≠ [] := by
  refine ne_nil_of_length_pos ?_
  have := P.two_le_vertices_length
  omega

@[simp]
lemma vertices_head? (P : PolygonalPath x y) : P.vertices.head? = some x := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp

@[simp]
lemma vertices_getLast? (P : PolygonalPath x y) : P.vertices.getLast? = some y := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp [List.getLast?_cons, ih]

@[simp]
lemma ofList_vertices (x) (L : List (EuclideanSpace ℝ (Fin 2))) (y) :
    (ofList x L y).vertices = x :: L ++ [y] := by
  induction L generalizing x y with
  | nil => simp [ofList]
  | cons a as ih => simp [ofList, ih]

-- Get the list of internal vertices (excluding start and end)
@[simp]
def internal : ∀ {x y : _}, PolygonalPath x y → List (EuclideanSpace ℝ (Fin 2))
  | _, _, direct a b => []
  | _, _, cons _ b as => b :: as.internal

@[simp]
lemma cons_internal_concat (P : PolygonalPath x y) : x :: (P.internal ++ [y]) = P.vertices := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simpa

@[simp]
lemma cons_internal (P : PolygonalPath x y) : x :: P.internal = P.vertices.dropLast := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp [ih, dropLast_cons_of_ne_nil]

@[simp]
lemma internal_concat (P : PolygonalPath x y) : P.internal ++ [y] = P.vertices.tail := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp [dropLast_append_getLast?]

@[simp]
lemma ofList_internal (x) (L : List (EuclideanSpace ℝ (Fin 2))) (y) :
    (ofList x L y).internal = L := by
  induction L generalizing x y with
  | nil => simp [ofList]
  | cons a as ih => simp [ofList, ih]

-- Append two polygonal paths
def append : ∀ {x y z : _}, PolygonalPath x y → PolygonalPath y z → PolygonalPath x z
  | _, _, _, direct x y, p => cons x y p
  | _, _, _, cons x w as, p => cons x w (as.append p)

@[simp]
lemma append_vertices (P : PolygonalPath x y) (Q : PolygonalPath y z) :
    (P.append Q).vertices = P.vertices ++ Q.vertices.tail := by
  induction P with
  | direct x y =>
    rw [← cons_internal_concat]
    simp only [append, internal, cons_append, internal_concat, vertices, nil_append]
  | cons x w as ih => simp [append, ih]

@[simp]
lemma append_internal (P : PolygonalPath x y) (Q : PolygonalPath y z) :
    (P.append Q).internal = P.internal ++ y :: Q.internal := by
  induction P with
  | direct x y => simp [append]
  | cons x w as ih => simp only [append, internal, cons_append, ih]

-- Convert to a Path
noncomputable def toPath : ∀ {x y : _}, PolygonalPath x y → Path x y
  | _, _, direct x y => Path.segment x y
  | _, _, cons x w as => (Path.segment x w).trans as.toPath

@[simp]
lemma toPath_range (P : PolygonalPath x y) :
    range (P.toPath) = ⋃ s ∈ P.vertices.zip (P.internal ++ [y]), segment ℝ s.1 s.2 := by
  induction P with
  | direct x y => simp [toPath]
  | cons x w as ih =>
    simp only [toPath, Path.trans_range, Path.range_segment, ih, internal, cons_append]
    simp

lemma toPath_range_compact (P : PolygonalPath x y) : IsCompact (range P.toPath) := by
  simp only [toPath_range]
  induction P.vertices.zip (P.internal ++ [y]) with
  | nil => simp
  | cons head tail ih =>
    simp only [mem_cons, iUnion_iUnion_eq_or_left]
    apply IsCompact.union _ ih
    rw [← convexHull_pair]
    apply Set.Finite.isCompact_convexHull
    simp

def simple (P : PolygonalPath x y) : Prop := Injective P.toPath

end PolygonalPath

open PolygonalPath

noncomputable def List.uniform (hN : 0 < N) : List unitInterval :=
  List.finRange (N + 1) |>.map (fun (i : Fin (N + 1)) ↦ ⟨(i : ℝ) / N,
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), by
    rw [div_le_one (Nat.cast_pos.mpr hN)]
    exact Nat.cast_le.mpr (Nat.le_of_lt_succ i.is_lt)⟩)

@[simp]
lemma List.uniform_head? (hN : 0 < N) : (List.uniform hN).head? = some 0 := by
  simp [uniform, finRange]

@[simp]
lemma List.uniform_getLast? (hN : 0 < N) : (List.uniform hN).getLast? = some 1 := by
  rw [uniform, finRange_succ_last]
  simp [hN.ne']

lemma List.uniform_isChain (hN : 0 < N) : (List.uniform hN).IsChain (dist · · = 1 / N) := by
  simp only [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, one_div, uniform,
    finRange_eq_pmap_range, isChain_map, isChain_pmap, Order.lt_add_one_iff, exists_prop,
    isChain_and_iff, isChain_range, add_tsub_cancel_right, Nat.succ_eq_add_one,
    Order.add_one_le_iff, imp_self, implies_true, Nat.cast_add, Nat.cast_one, true_and]
  simp +contextual only [le_of_lt, implies_true, true_and]
  intro m hmN
  simp [div_sub_div_same, abs_div]

@[simp]
lemma List.uniform_length (hN : 0 < N) : (List.uniform hN).length = N + 1 := by
  simp [uniform]

@[simp]
lemma List.uniform_get (hN : 0 < N) (i : Fin (N + 1)) :
    (List.uniform hN).get (i.cast (by simp)) = (i : ℝ) / N := by
  simp [uniform]

lemma List.uniform_eq_cons_concat (hN : 0 < N) :
    List.uniform hN = 0 :: (List.uniform hN).tail.dropLast ++ [1] := by
  simp only [cons_append]
  rw [dropLast_append_getLast?, cons_head?_tail (by simp)]
  rw [getLast?_tail]
  simp [hN.ne']

lemma Path.exists_polygonalPath_of_thickening (P : Path x y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : PolygonalPath x y, range L.toPath ⊆ Metric.thickening δ (range P) := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.uniformContinuous_iff.mp P.uniformContinuous δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos' : 0 < (N : ℝ) := lt_trans (by simpa) hN
  have hNpos : 0 < N := by norm_cast at hNpos'
  have hN' : 1 / ↑N < ε := (one_div_lt hεpos hNpos').mp hN
  set L : List (EuclideanSpace ℝ (Fin 2)) := (List.uniform hNpos) |>.map P with hL
  use ofList x L.tail.dropLast y
  have hxLy : L = x :: L.tail.dropLast ++ [y] := by
    rw [hL, uniform_eq_cons_concat hNpos]
    simp
  have hLtail : L.tail = L.tail.dropLast ++ [y] := by
    rw [hxLy]
    simp
  simp only [toPath_range, ofList_vertices, ← hxLy, ofList_internal, ← hLtail, iUnion_subset_iff,
    Prod.forall]
  refine fun a b hab x hx ↦ mem_thickening_iff.mpr ⟨b, ?_, ?_⟩
  · simp only [Set.mem_range, Subtype.exists, mem_Icc]
    obtain ⟨i, hi, -, hhi⟩ := by simpa [L] using mem_of_mem_tail (of_mem_zip hab |>.2)
    use i, hi, hhi
  have hchain : L.IsChain (dist · · < δ) := by
    unfold L
    rw [isChain_map]
    apply uniform_isChain hNpos |>.imp fun a b hab ↦ hε (hab ▸ hN')
  rw [isChain_iff_all_zip_tail] at hchain
  have hdist := by simpa using hchain _ hab
  have hseg : segment ℝ a b ⊆ ball b δ := (convex_ball b δ).segment_subset (by simpa) (by simpa)
  simpa using hseg hx

lemma JoinedIn.exists_polygonalPath_of_open (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ P : PolygonalPath x y, range P.toPath ⊆ X := by
  obtain ⟨P, hP⟩ := h
  have hPc : IsCompact (range P) := isCompact_range P.continuous
  have hPr : range ⇑P ⊆ X := by
    intro i hi
    simp only [Set.mem_range, Subtype.exists, mem_Icc] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    exact hP ⟨t, ht⟩
  obtain ⟨δ, hδpos, hδ⟩ := hPc.exists_thickening_subset_open hX hPr
  obtain ⟨L, hL⟩ := P.exists_polygonalPath_of_thickening hδpos
  use L, hL.trans hδ


lemma foo {x y : EuclideanSpace ℝ (Fin 2)} (P : PolygonalPath x y) :
    ∃ (ε : ℝ) (R₀ R₁ : Set (EuclideanSpace ℝ (Fin 2))),
    0 < ε ∧ Metric.thickening ε (range P.toPath) = R₀ ∪ R₁ ∧
    IsPathConnected R₀ ∧ IsPathConnected R₁ :=
  sorry
