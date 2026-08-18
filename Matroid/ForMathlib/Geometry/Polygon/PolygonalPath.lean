module

public import Matroid.ForMathlib.Geometry.Polygon.Basic
public import Matroid.ForMathlib.Geometry.PolygonalPath.SimpleLoop
public import Matroid.ForMathlib.List.Basic
public import Matroid.ForMathlib.Topology.Path
public import Matroid.ForMathlib.Geometry.PolygonalPath.Basic

/-!
# Polygons and polygonal paths

This file is the dictionary between `Polygon α n` (a cyclic list of vertices, with no base point)
and `PolygonalPath x x` (a closed polygonal path, which does have a base point).

`Polygon.IsSimple` describes the cyclic vertex sequence, while
`PolygonalPath.IsSimpleLoop` describes the parametrized closed path. The dictionary provides:

* `Polygon.IsSimple`, invariant under `Polygon.rotate` and `Polygon.reverse`;
* `PolygonalPath.IsSimpleLoop`, the parametrized notion used by topology;
* equivalences between the two notions and the corresponding arc decompositions.

## Main definitions

* `Polygon.toPolygonalPath p i` : traverse `p` starting at vertex `i`.
* `Polygon.arc p i j` : the arc of `p` from vertex `i` to vertex `j`, in the direction of
  increasing index.
* `PolygonalPath.toPolygon` : the polygon underlying a closed polygonal path.

## Main statements

* `Polygon.toSet_toPolygonalPath` : `(p.toPolygonalPath i).toSet = p.boundary ℝ` for every `i`.
  Everything base-point-free about a closed path factors through this.
* `Polygon.isSimple_iff_isSimpleLoop` : `p.IsSimple ℝ ↔ (p.toPolygonalPath i).IsSimpleLoop`,
  for any (equivalently, every) `i`.
* `Polygon.IsSimple.exists_arcs` : a simple polygon can be cut at any two points of its boundary
  into two simple arcs meeting exactly at those two points.

-/

@[expose] public section

open Set Function unitInterval

namespace PolygonalPath

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] {x y b : α}

/-! ### From closed polygonal paths to polygons -/

/-- The polygon underlying a closed polygonal path: its vertex list with the repeated final vertex
removed. For `nil x` this is the empty polygon, which is the reason `Polygon P 0` is worth
allowing. -/
def toPolygon (P : PolygonalPath x x) : Polygon α P.vertices.dropLast.length :=
  Polygon.ofList P.vertices.dropLast

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma toPolygon_length (P : PolygonalPath x x) :
    P.vertices.dropLast.length = P.length := by
  simp [List.length_dropLast]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma toPolygon_apply_zero (P : PolygonalPath x x) (h : 0 < P.length) :
    P.toPolygon ⟨0, by simp [h]⟩ = x := by
  simp [toPolygon, Polygon.ofList, ← P.cons_internal h]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
private lemma getElem_vertices_zip_eq_toPolygon (P : PolygonalPath x x) (h : 0 < P.length)
    (i : Fin P.length) :
    (P.vertices.zip P.vertices.tail)[i] =
      (P.toPolygon ⟨i, by simp⟩,
        P.toPolygon (finRotate P.vertices.dropLast.length ⟨i, by simp⟩)) := by
  let _ : NeZero P.vertices.dropLast.length := ⟨by simpa using h.ne'⟩
  have hzip : (P.vertices.zip P.vertices.tail)[i] =
      (P.vertices[i], P.vertices.tail[i]) := List.getElem_zip
  rw [hzip]
  have htail : P.vertices.tail[i] = P.vertices[i.val + 1] := List.getElem_tail _
  rw [htail]
  apply Prod.ext
  · change P.vertices[i] = P.vertices.dropLast.get ⟨i, by simp⟩
    rw [List.get_eq_getElem, List.getElem_dropLast]
    rfl
  · change P.vertices[i.val + 1] = P.vertices.dropLast.get
      (finRotate P.vertices.dropLast.length ⟨i, by simp⟩)
    by_cases hi : i.val + 1 = P.length
    · have hidx : finRotate P.vertices.dropLast.length
          (⟨i, by simp⟩ : Fin P.vertices.dropLast.length) = 0 := by
        apply Fin.ext
        simp [finRotate_apply, Fin.val_add, hi]
      rw [hidx]
      have hind : i.val + 1 = P.vertices.length - 1 := by simp [hi]
      have hleft : P.vertices[i.val + 1] = x := by
        have hlast : P.vertices.getLast P.vertices_ne_nil = x := by
          have hx := P.vertices_getLast?
          rw [List.getLast?_eq_getLast_of_ne_nil P.vertices_ne_nil] at hx
          exact Option.some.inj hx
        exact (by simpa only [hind] using
          (List.getLast_eq_getElem P.vertices_ne_nil).symm.trans hlast)
      rw [hleft]
      simp [← P.cons_internal h]
    · have hi' : i.val + 1 < P.length := by omega
      let k : Fin P.vertices.dropLast.length := ⟨i.val + 1, by simpa using hi'⟩
      have hidx : finRotate P.vertices.dropLast.length
          (⟨i, by simp⟩ : Fin P.vertices.dropLast.length) = k := by
        apply Fin.ext
        simp [k, finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt, hi']
      rw [hidx]
      have hi'' : i.val + 1 < P.vertices.dropLast.length := by simpa using hi'
      exact (List.getElem_dropLast hi'').symm

omit [TopologicalSpace α] [ContinuousSMul ℝ α] [ContinuousAdd α] in
@[simp] lemma boundary_toPolygon (P : PolygonalPath x x) (h : 0 < P.length) :
    P.toPolygon.boundary ℝ = P.toSet := by
  rw [P.toSet_eq_biUnion h]
  ext a
  simp only [Polygon.boundary, Polygon.edgeSet, mem_iUnion, P.edges_eq_zip, Prod.exists]
  constructor
  · rintro ⟨i, hai⟩
    let j : Fin P.length := ⟨i, by simpa using i.isLt⟩
    refine ⟨P.toPolygon i, P.toPolygon (finRotate P.vertices.dropLast.length i), ?_, ?_⟩
    · have hget := getElem_vertices_zip_eq_toPolygon P h j
      have hget' : (P.vertices.zip P.vertices.tail)[j] =
          (P.toPolygon i, P.toPolygon (finRotate P.vertices.dropLast.length i)) := by
        simpa [j] using hget
      rw [← hget']
      exact List.getElem_mem (by simp [← P.edges_eq_zip])
    · simpa [affineSegment_eq_segment] using hai
  · rintro ⟨u, v, huv, ha⟩
    obtain ⟨k, hk⟩ := List.get_of_mem huv
    let j : Fin P.length := ⟨k, by simpa [← P.edges_eq_zip] using k.isLt⟩
    let i : Fin P.vertices.dropLast.length := ⟨j, by simp⟩
    refine ⟨i, ?_⟩
    have hget := getElem_vertices_zip_eq_toPolygon P h j
    have hij : i = (⟨j, by simp⟩ : Fin P.vertices.dropLast.length) := Fin.ext rfl
    subst i
    have hk' : (P.vertices.zip P.vertices.tail)[j] = (u, v) := by
      simpa [List.get_eq_getElem, j] using hk
    have ha' : a ∈ segment ℝ ((P.vertices.zip P.vertices.tail)[j]).1
        ((P.vertices.zip P.vertices.tail)[j]).2 := by
      rw [hk']
      exact ha
    rw [hget] at ha'
    simpa [affineSegment_eq_segment] using ha'

end PolygonalPath

namespace Polygon

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] {n : ℕ} {p : Polygon α n} {i j : Fin n} {a b : α}

/-! ### From polygons to polygonal paths -/

/-- The vertices of `p`, listed cyclically starting at vertex `i`. -/
def cycleFrom (p : Polygon α n) (i : Fin n) : List α := List.ofFn fun k : Fin n => p (i + k)

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma cycleFrom_length (p : Polygon α n) (i : Fin n) : (p.cycleFrom i).length = n := by
  simp [cycleFrom]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma cycleFrom_head? [NeZero n] (p : Polygon α n) (i : Fin n) :
    (p.cycleFrom i).head? = some (p i) := by
  rw [List.head?_eq_getElem?]
  simp [cycleFrom]
  exact NeZero.ne n

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
lemma cycleFrom_zero [NeZero n] (p : Polygon α n) : p.cycleFrom 0 = p.toList := by
  simp [cycleFrom, toList]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
lemma cycleFrom_rotate (p : Polygon α n) (i j : Fin n) :
    (p.rotate i).cycleFrom j = p.cycleFrom (i + j) := by
  simp [cycleFrom, add_assoc]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
private lemma cycleFrom_eq_rotate (p : Polygon α n) (i j : Fin n) :
    p.cycleFrom j = (p.cycleFrom i).rotate (j - i).val := by
  apply List.ext_getElem
  · simp
  intro k hk₁ hk₂
  rw [List.getElem_rotate]
  simp only [cycleFrom, List.length_ofFn, List.getElem_ofFn]
  apply congr_arg p
  have := i.neZero
  let k' : Fin n := ⟨k, by simpa [cycleFrom] using hk₁⟩
  have hki : ⟨(k + (j - i).val) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ =
      k' + (j - i) := by
    apply Fin.ext
    simp [Fin.val_add, k']
  rw [hki]
  abel

private lemma fin_rev_add_rev (i k : Fin n) : (i.rev + k).rev = i - k := by
  rw [Fin.rev_add, Fin.rev_rev]

private lemma fin_rev_add_mk (i : Fin n) {k : ℕ} (hk : k < n) (hk0 : k ≠ 0) :
    (i.rev + ⟨k, hk⟩).rev = i + ⟨n - k, by omega⟩ := by
  rw [fin_rev_add_rev]
  apply Fin.ext
  simp [Fin.sub_def, Fin.val_add, Nat.add_comm]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
private lemma cycleFrom_reverse_append (p : Polygon α n) (i : Fin n) :
    List.ofFn (fun k : Fin n ↦ p (i.rev + k).rev) ++ [p i] =
      (List.ofFn (fun k : Fin n ↦ p (i + k)) ++ [p i]).reverse := by
  apply List.ext_getElem
  · simp
  intro k hk₁ hk₂
  rw [List.getElem_reverse]
  simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk₁ hk₂ ⊢
  by_cases hkn : k < n
  · rw [List.getElem_append_left (by simpa using hkn)]
    simp only [List.getElem_ofFn]
    by_cases hk : k = 0
    · subst k
      rw [List.getElem_append_right (by simp)]
      simp only [List.getElem_singleton]
      let _ := i.neZero
      apply congr_arg p
      simp
    · have hr : n + 1 - 1 - k < (List.ofFn fun k : Fin n ↦ p (i + k)).length := by
        simp
        omega
      rw [List.getElem_append_left hr]
      simp only [List.getElem_ofFn]
      congr 1
      exact fin_rev_add_mk i hkn hk
  · have hk : k = n := by omega
    subst k
    rw [List.getElem_append_right (by simp)]
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    rw [List.getElem_append_left (by simpa using hn)]
    let _ := i.neZero
    simp

/-- The closed polygonal path that traverses `p` once, starting and ending at vertex `i`. -/
def toPolygonalPath (p : Polygon α n) (i : Fin n) : PolygonalPath (p i) (p i) :=
  PolygonalPath.ofList (p i) (p.cycleFrom i).tail (p i)

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma toPolygonalPath_vertices (p : Polygon α n) (i : Fin n) :
    (p.toPolygonalPath i).vertices = p.cycleFrom i ++ [p i] := by
  let _ : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  rw [toPolygonalPath, PolygonalPath.ofList_vertices]
  nth_rw 2 [← List.cons_head?_tail (by simp : (p.cycleFrom i).head? = some (p i))]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma toPolygonalPath_length (p : Polygon α n) (i : Fin n) :
    (p.toPolygonalPath i).length = n := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  simp [toPolygonalPath, List.length_tail]
  omega

omit [TopologicalSpace α] [ContinuousSMul ℝ α] [ContinuousAdd α] in
/-- The key bridge lemma: the set traced out by the closed path is the boundary of the polygon,
whichever vertex is used as a base point. -/
@[simp] lemma toSet_toPolygonalPath (p : Polygon α n) (i : Fin n) :
    (p.toPolygonalPath i).toSet = p.boundary ℝ := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  rw [← PolygonalPath.boundary_toPolygon (p.toPolygonalPath i) (by simp [hn])]
  have hlen : (p.toPolygonalPath i).vertices.dropLast.length = n := by simp
  have heq : (p.toPolygonalPath i).toPolygon.cast hlen = p.rotate i := by
    apply Polygon.ext
    intro k
    simp [PolygonalPath.toPolygon, Polygon.ofList, cycleFrom]
  rw [← Polygon.boundary_cast (p.toPolygonalPath i).toPolygon hlen, heq,
    Polygon.boundary_rotate]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
lemma toPolygonalPath_rotate (p : Polygon α n) (i j : Fin n) :
    (p.rotate i).toPolygonalPath j = p.toPolygonalPath (i + j) := by
  simp [toPolygonalPath, cycleFrom_rotate]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
/-- Reversing a polygon reverses the closed path through it. The `cast` is needed because the two
sides are indexed by `p.reverse i.rev` and by `p i`, which agree only up to `Fin.rev_rev`. -/
lemma toPolygonalPath_reverse (p : Polygon α n) (i : Fin n) (h : p.reverse i.rev = p i) :
    p.reverse.toPolygonalPath i.rev = (p.toPolygonalPath i).reverse.cast h.symm h.symm := by
  apply PolygonalPath.ext_vertices
  rw [toPolygonalPath_vertices, PolygonalPath.cast_vertices,
    PolygonalPath.reverse_vertices, toPolygonalPath_vertices]
  simpa [cycleFrom, h] using cycleFrom_reverse_append p i

/-- The arc of `p` from vertex `i` to vertex `j`, traversed in the direction of increasing index.
For `i = j` this is `nil`, which is what makes `arc_length` hold unconditionally. -/
def arc (p : Polygon α n) (i j : Fin n) : PolygonalPath (p i) (p j) :=
  if h : i = j then (PolygonalPath.nil (p i)).cast rfl (congrArg p h) else
    PolygonalPath.ofList (p i) ((p.cycleFrom i).tail.take ((j - i : Fin n).val - 1)) (p j)

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma arc_length (p : Polygon α n) (i j : Fin n) :
    (p.arc i j).length = (j - i : Fin n).val := by
  let _ : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  rw [arc]
  split
  · subst j
    simp
  · simp only [PolygonalPath.ofList_length]
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    have hji : 0 < (j - i : Fin n).val := by
      apply Nat.pos_of_ne_zero
      intro hval
      apply sub_ne_zero.mpr ‹i ≠ j›.symm
      apply Fin.ext
      simpa using hval
    simp [List.length_take, List.length_tail]
    omega

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
@[simp] lemma arc_self (p : Polygon α n) (i : Fin n) :
    p.arc i i = (PolygonalPath.nil (p i)).cast rfl rfl := by
  simp [arc]

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
/-- Cutting a polygon at two vertices gives two arcs whose concatenation is the whole closed
path. -/
lemma arc_append_arc (p : Polygon α n) (i j : Fin n) (hij : i ≠ j) :
    (p.arc i j).append (p.arc j i) = p.toPolygonalPath i := by
  let _ := i.neZero
  have hdpos : 0 < (j - i : Fin n).val := by
    apply Nat.pos_of_ne_zero
    intro hd
    apply sub_ne_zero.mpr hij.symm
    apply Fin.ext
    exact hd
  have hepos : 0 < (i - j : Fin n).val := by
    apply Nat.pos_of_ne_zero
    intro he
    apply sub_ne_zero.mpr hij
    apply Fin.ext
    exact he
  have hsum : (j - i : Fin n).val + (i - j : Fin n).val = n := by
    have hz : (j - i : Fin n) + (i - j) = 0 := by abel
    have hv := congr_arg Fin.val hz
    rw [Fin.val_add_eq_ite] at hv
    split at hv
    · simp_all
      omega
    · simp_all
  apply PolygonalPath.ext_vertices
  simp [arc, hij, hij.symm]
  rw [cycleFrom_eq_rotate p i j, List.rotate_eq_drop_append_take (by simp)]
  refine List.append_arc (p.cycleFrom i) (p i) (p j) _ _ hdpos hepos ?_ ?_ ?_
  · simpa using hsum
  · exact cycleFrom_head? p i
  · simp only [cycleFrom, List.getElem_ofFn]
    change p (i + (j - i)) = p j
    abel_nf

omit [TopologicalSpace α] [ContinuousSMul ℝ α] [ContinuousAdd α] in
@[simp] lemma toSet_arc_union_toSet_arc (p : Polygon α n) (i j : Fin n) (hij : i ≠ j) :
    (p.arc i j).toSet ∪ (p.arc j i).toSet = p.boundary ℝ := by
  rw [← PolygonalPath.toSet_append, arc_append_arc p i j hij, toSet_toPolygonalPath]

private def CompatibleEdges (s t : α × α) : Prop :=
  segment ℝ s.1 s.2 ∩ segment ℝ t.1 t.2 ⊆ ({s.1, s.2} ∩ {t.1, t.2} : Set α)

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
private lemma edges_toPolygonalPath (p : Polygon α n) (i : Fin n) :
    (p.toPolygonalPath i).edges = List.ofFn fun k : Fin n ↦
      (p (i + k), p (i + finRotate n k)) := by
  apply List.ext_get (by simp)
  intro k hk₁ hk₂
  let q := p.toPolygonalPath i
  let k' : Fin q.length := ⟨k, by simpa [q] using hk₁⟩
  have hq : 0 < q.length := by simp [q, Nat.zero_lt_of_lt i.isLt]
  have hget := PolygonalPath.getElem_vertices_zip_eq_toPolygon q hq k'
  simp only [List.get_ofFn]
  have hget' : (p.toPolygonalPath i).edges.get ⟨k, hk₁⟩ =
      (q.toPolygon ⟨k, by simpa [q] using hk₁⟩,
        q.toPolygon (finRotate q.vertices.dropLast.length ⟨k, by simpa [q] using hk₁⟩)) := by
    change q.edges.get _ = _
    rw [List.get_of_eq q.edges_eq_zip]
    convert hget using 1
    apply congr_arg (List.get (q.vertices.zip q.vertices.tail))
    apply Fin.ext
    rfl
  rw [hget']
  apply Prod.ext
  · simp [q, PolygonalPath.toPolygon, Polygon.ofList, cycleFrom]
  · simp [q, PolygonalPath.toPolygon, Polygon.ofList, cycleFrom]
    apply congr_arg p
    apply Fin.ext
    simp [Fin.val_add]

private lemma PolygonalPath.isSimpleLoop_iff_pairwise {P : PolygonalPath a a} :
    P.IsSimpleLoop ↔ 3 ≤ P.length ∧ P.vertices.dropLast.Nodup ∧
      P.edges.Pairwise CompatibleEdges := by
  constructor
  · intro h
    refine ⟨h.three_le_length, h.vertices_dropLast_nodup, ?_⟩
    cases P with
    | nil => simp at h
    | @cons a b _ Q =>
      obtain ⟨hab, hQ, hinter⟩ := PolygonalPath.isSimpleLoop_cons_iff.mp h
      rw [PolygonalPath.edges_cons, List.pairwise_cons]
      refine ⟨?_, hQ.2⟩
      intro t ht u hu
      have huQ := Q.segment_subset_toSet ht hu.2
      rcases hinter ⟨hu.1, huQ⟩ with rfl | rfl
      · exact ⟨by simp, (hQ.mem_segment_iff_of_mem_vertices Q.last_mem_vertices ht).mp hu.2⟩
      · exact ⟨by simp, (hQ.mem_segment_iff_of_mem_vertices Q.first_mem_vertices ht).mp hu.2⟩
  · rintro ⟨hlen, hv, he⟩
    cases P with
    | nil => simp at hlen
    | @cons a b _ Q =>
      have hQlen : 0 < Q.length := by simp at hlen ⊢; omega
      have hv' : (a :: Q.vertices.dropLast).Nodup := by
        rw [PolygonalPath.vertices_cons, List.dropLast_cons_of_ne_nil Q.vertices_ne_nil] at hv
        exact hv
      have hQv : Q.vertices.Nodup := by
        rw [Q.vertices_eq_concat]
        rw [List.nodup_append]
        refine ⟨(List.nodup_cons.mp hv').2, by simp, ?_⟩
        intro z hz w hw
        simp only [List.mem_singleton] at hw
        subst w
        exact fun hza ↦ (List.nodup_cons.mp hv').1 (hza ▸ hz)
      rw [PolygonalPath.edges_cons, List.pairwise_cons] at he
      have hQ : Q.IsSimple := ⟨hQv, he.2⟩
      apply PolygonalPath.isSimpleLoop_cons_iff.mpr
      refine ⟨?_, hQ, ?_⟩
      · intro hab
        subst b
        have ha : a ∈ Q.vertices.dropLast := by
          rw [← Q.cons_internal hQlen]
          simp
        exact (List.nodup_cons.mp hv').1 ha
      · intro u hu
        obtain ⟨t, ht, hut⟩ := (Q.mem_toSet_iff hQlen).mp hu.2
        exact (he.1 t ht ⟨hu.1, hut⟩).1

/-! ### Simplicity -/

/-- The bridge between the cyclic and the parametrized notions of a simple closed curve. The
right-hand side does not depend on `i`, by `isSimpleLoop_toPolygonalPath_congr`. -/
lemma isSimple_iff_isSimpleLoop (p : Polygon α n) (i : Fin n) :
    p.IsSimple ℝ ↔ (p.toPolygonalPath i).IsSimpleLoop := by
  rw [PolygonalPath.isSimpleLoop_iff_pairwise, edges_toPolygonalPath]
  simp only [toPolygonalPath_length, toPolygonalPath_vertices, List.dropLast_concat,
    List.pairwise_ofFn]
  constructor
  · intro h
    refine ⟨h.three_le, ?_, ?_⟩
    · rw [cycleFrom, List.nodup_ofFn]
      intro k l hkl
      apply add_left_cancel (a := i)
      exact h.injective hkl
    · intro k l hkl
      have hne : i + k ≠ i + l := fun heq ↦ Fin.ne_of_lt hkl (add_left_cancel heq)
      have hs := h.edgeSet_inter_subset hne
      simpa only [CompatibleEdges, Polygon.edgeSet_eq_segment, Polygon.edgeVertices,
        Polygon.mem_edgeVertices, ← add_finRotate] using hs
  · rintro ⟨hn, hv, he⟩
    let _ : NeZero n := ⟨by omega⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [cycleFrom, List.nodup_ofFn] at hv
      intro k l hkl
      have := i.neZero
      have heq : p (i + (k - i)) = p (i + (l - i)) := by simpa using hkl
      have hsub := hv heq
      simpa using congr_arg (fun t : Fin n ↦ i + t) hsub
    · intro k l hkl
      let k' : Fin n := k - i
      let l' : Fin n := l - i
      have hk : i + k' = k := by dsimp [k']; rw [add_comm, sub_add_cancel]
      have hl : i + l' = l := by dsimp [l']; rw [add_comm, sub_add_cancel]
      have hne : k' ≠ l' := by
        intro heq
        apply hkl
        rw [← hk, ← hl, heq]
      have hc : CompatibleEdges (p (i + k'), p (i + finRotate n k'))
          (p (i + l'), p (i + finRotate n l')) := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact he hlt
        · intro u hu
          have hu' := he hgt ⟨hu.2, hu.1⟩
          exact ⟨hu'.2, hu'.1⟩
      simpa only [CompatibleEdges, Polygon.edgeSet_eq_segment, Polygon.edgeVertices,
        Polygon.mem_edgeVertices, add_finRotate, hk, hl] using hc

lemma isSimple_iff_forall_isSimpleLoop [NeZero n] (p : Polygon α n) :
    p.IsSimple ℝ ↔ ∀ i, (p.toPolygonalPath i).IsSimpleLoop := by
  constructor
  · exact fun h i ↦ (isSimple_iff_isSimpleLoop p i).mp h
  · intro h
    exact (isSimple_iff_isSimpleLoop p 0).mpr (h 0)

lemma isSimple_iff_exists_isSimpleLoop (p : Polygon α n) :
    p.IsSimple ℝ ↔ ∃ i, (p.toPolygonalPath i).IsSimpleLoop := by
  constructor
  · intro h
    let _ := h.neZero
    exact ⟨0, (isSimple_iff_isSimpleLoop p 0).mp h⟩
  · rintro ⟨i, hi⟩
    exact (isSimple_iff_isSimpleLoop p i).mpr hi

/-- Closed simplicity does not depend on the base point. -/
lemma isSimpleLoop_toPolygonalPath_congr (p : Polygon α n) (i j : Fin n) :
    (p.toPolygonalPath i).IsSimpleLoop ↔ (p.toPolygonalPath j).IsSimpleLoop := by
  rw [← isSimple_iff_isSimpleLoop p i, ← isSimple_iff_isSimpleLoop p j]

/-- A simple polygon is the union of two simple arcs meeting exactly at the two vertices where it
was cut. -/
lemma IsSimple.arcs (h : p.IsSimple ℝ) (hij : i ≠ j) :
    (p.arc i j).IsSimple ∧ (p.arc j i).IsSimple ∧
      (p.arc i j).toSet ∩ (p.arc j i).toSet = {p i, p j} := by
  have hpij : p i ≠ p j := h.injective.ne hij
  have hloop := (isSimple_iff_isSimpleLoop p i).mp h
  rw [← arc_append_arc p i j hij, PolygonalPath.isSimpleLoop_append_iff hpij] at hloop
  exact hloop

/-- The same, at arbitrary distinct points of the boundary rather than at vertices: this is the
statement the Jordan curve argument consumes. Obtained from `IsSimple.arcs` by subdividing at `a`
and `b`. -/
lemma IsSimple.exists_arcs (h : p.IsSimple ℝ) (ha : a ∈ p.boundary ℝ) (hb : b ∈ p.boundary ℝ)
    (hab : a ≠ b) : ∃ (A : PolygonalPath a b) (B : PolygonalPath b a), A.IsSimple ∧ B.IsSimple ∧
      A.toSet ∩ B.toSet = {a, b} ∧ A.toSet ∪ B.toSet = p.boundary ℝ := by
  let _ := h.neZero
  let i : Fin n := 0
  let P := p.toPolygonalPath i
  have hP : P.IsSimpleLoop := (isSimple_iff_isSimpleLoop p i).mp h
  have haP : a ∈ P.toSet := by
    change a ∈ (p.toPolygonalPath i).toSet
    rw [toSet_toPolygonalPath]
    exact ha
  let C := (P.breakAt haP).1
  let D := (P.breakAt haP).2
  let Q : PolygonalPath a a := D.append C
  have hCD : (C.append D).IsSimpleLoop := by
    have := (PolygonalPath.isSimpleLoop_subdivide_iff haP).mpr hP
    simpa [C, D, PolygonalPath.subdivide] using this
  have hQ : Q.IsSimpleLoop := by
    exact PolygonalPath.isSimpleLoop_append_comm.mp hCD
  have hQset : Q.toSet = P.toSet := by
    change (D.append C).toSet = P.toSet
    rw [PolygonalPath.toSet_append, union_comm]
    exact PolygonalPath.breakAt_toSet_union (P := P) (ha := haP)
  have hbP : b ∈ P.toSet := by
    change b ∈ (p.toPolygonalPath i).toSet
    rw [toSet_toPolygonalPath]
    exact hb
  have hbQ : b ∈ Q.toSet := hQset.symm ▸ hbP
  let A := (Q.breakAt hbQ).1
  let B := (Q.breakAt hbQ).2
  have hABloop : (A.append B).IsSimpleLoop := by
    have := (PolygonalPath.isSimpleLoop_subdivide_iff hbQ).mpr hQ
    simpa [A, B, PolygonalPath.subdivide] using this
  obtain ⟨hA, hB, hinter⟩ := (PolygonalPath.isSimpleLoop_append_iff hab).mp hABloop
  refine ⟨A, B, hA, hB, hinter, ?_⟩
  change (Q.breakAt hbQ).1.toSet ∪ (Q.breakAt hbQ).2.toSet = p.boundary ℝ
  rw [PolygonalPath.breakAt_toSet_union, hQset]
  change (p.toPolygonalPath i).toSet = p.boundary ℝ
  exact Polygon.toSet_toPolygonalPath p i

end Polygon

namespace PolygonalPath

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] {x : α}

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
lemma toPolygonalPath_toPolygon (P : PolygonalPath x x) (h : 0 < P.length) :
    P.toPolygon.toPolygonalPath ⟨0, by simp [h]⟩ =
      P.cast (toPolygon_apply_zero P h).symm (toPolygon_apply_zero P h).symm := by
  let _ : NeZero P.vertices.dropLast.length := ⟨by simpa using h.ne'⟩
  apply ext_vertices
  rw [Polygon.toPolygonalPath_vertices, PolygonalPath.cast_vertices]
  change P.toPolygon.cycleFrom 0 ++ [P.toPolygon 0] = P.vertices
  rw [Polygon.cycleFrom_zero]
  rw [show P.toPolygon.toList = P.vertices.dropLast by simp [toPolygon],
    show P.toPolygon 0 = x from toPolygon_apply_zero P h]
  exact P.vertices_eq_concat.symm

/-- A closed polygonal path is a simple loop exactly when the polygon underlying it is simple. Both
sides are false for `nil x`, whose polygon is the empty one. -/
@[simp] lemma isSimple_toPolygon (P : PolygonalPath x x) :
    P.toPolygon.IsSimple ℝ ↔ P.IsSimpleLoop := by
  by_cases hP : P.length = 0
  · rw [P.eq_nil_of_length_eq_zero hP]
    simp [toPolygon, Polygon.IsSimple]
  · have hpos : 0 < P.length := Nat.pos_of_ne_zero hP
    let i : Fin P.vertices.dropLast.length := ⟨0, by simp [hpos]⟩
    rw [Polygon.isSimple_iff_isSimpleLoop P.toPolygon i]
    rw [toPolygonalPath_toPolygon P hpos]
    exact isSimpleLoop_cast_self P _

end PolygonalPath
