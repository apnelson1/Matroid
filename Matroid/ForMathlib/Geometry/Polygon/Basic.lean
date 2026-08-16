module

public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Topology
public import Matroid.ForMathlib.Logic.Equiv.Fin.Rotate
public import Matroid.ForMathlib.Analysis.Convex.Segment

/-!
# Extra API for `Polygon`

`Mathlib.Geometry.Polygon.Basic` defines `Polygon P n` as a `Fin n`-indexed family of vertices,
together with `edgePath`, `edgeSet`, `boundary`, `HasNondegenerateEdges` and
`HasNondegenerateVertices`. This file adds the API that is needed to treat a polygon as a
*closed polygonal curve*:

* the operations `rotate`, `reverse` and `subdivide`, which are exactly the operations that make
  sense for closed curves but not for paths with distinct endpoints;
* the predicate `IsSimple`, saying that distinct edges meet only in shared endpoints;
* the local structure of the boundary of a simple polygon: each point of the boundary that is not
  a vertex lies on a unique edge, and each vertex lies on exactly two edges.

## Design notes

* `Mathlib.Geometry.Polygon.Basic` uses `finRotate n i` for "the vertex after `i`". We keep that
  convention. Use `finRotate_apply` to rewrite it to `i + 1` when a `NeZero n` instance is around.
* `HasNondegenerateVertices` (three consecutive vertices affinely independent) is *stronger* than
  what a simple closed curve needs: it forbids collinear adjacent edges, which is what happens at
  a subdivided vertex. `IsSimple` below is the correct notion for curve-theoretic purposes, and is
  implied by neither `HasNondegenerateVertices` nor implies it.
* `IsSimple` asserts `2 ≤ n` rather than `HasNondegenerateEdges`. Given injectivity of the
  vertices the two are equivalent for `n ≠ 1`, but neither the injectivity nor the edge condition
  can see the degenerate cases `n = 0` (no edges at all) and `n = 1` (one edge from a point to
  itself, where `finRotate 1 = id`), both of which pass vacuously. Asserting `2 ≤ n` rules out
  both, so no `[NeZero n]` instance argument is needed. That `3 ≤ n` is then a theorem, since the
  digon is excluded by the edge condition (`IsSimple.three_le`).

The operations and incidence lemmas are proved at the stated level of generality; results that
split an edge or exclude digons use the stronger ordered-field hypotheses needed for interior
points of segments.
-/

@[expose] public section

open Set Function

namespace Polygon

variable {R V P : Type*} {n : ℕ}

@[ext]
lemma ext {p q : Polygon P n} (h : ∀ i, p i = q i) : p = q := by
  cases p
  cases q
  congr
  funext i
  exact h i

/-! ### Reindexing -/

/-- Reindexing a polygon along an equality of vertex counts. -/
def cast (p : Polygon P n) {m : ℕ} (h : n = m) : Polygon P m := ⟨fun i => p (i.cast h.symm)⟩

@[simp] lemma cast_apply (p : Polygon P n) {m : ℕ} (h : n = m) (i : Fin m) :
    p.cast h i = p (i.cast h.symm) := rfl

@[simp] lemma cast_rfl (p : Polygon P n) : p.cast rfl = p := rfl

/-! ### Conversion to and from lists -/

/-- The vertices of a polygon, as a list, starting at index `0`. -/
def toList (p : Polygon P n) : List P := List.ofFn p.vertices

/-- The polygon whose vertices are the entries of a list, in order. -/
def ofList (L : List P) : Polygon P L.length := ⟨L.get⟩

@[simp] lemma toList_length (p : Polygon P n) : p.toList.length = n := by
  simp [toList]

@[simp] lemma ofList_toList (p : Polygon P n) : ofList p.toList = p.cast p.toList_length.symm := by
  ext i
  let i' : Fin (List.ofFn p.vertices).length := ⟨i, by simpa [toList] using i.isLt⟩
  suffices (ofList p.toList).vertices i = (List.ofFn p.vertices).get i' by
    rw [this, List.get_ofFn]
    congr
  congr

@[simp] lemma toList_ofList (L : List P) : (ofList L).toList = L := by
  simp [ofList, toList]

/-! ### Rotation

Rotation is the operation that makes the "base point" of a closed curve irrelevant; it has no
analogue for paths with distinct endpoints. -/

/-- `p.rotate i` is `p` with its vertices relabelled so that vertex `i` comes first. -/
def rotate (p : Polygon P n) (i : Fin n) : Polygon P n := ⟨fun k => p (i + k)⟩

@[simp] lemma rotate_apply (p : Polygon P n) (i k : Fin n) : p.rotate i k = p (i + k) := rfl

@[simp] lemma rotate_zero [NeZero n] (p : Polygon P n) : p.rotate 0 = p := by
  ext
  simp

lemma rotate_rotate (p : Polygon P n) (i j : Fin n) : (p.rotate i).rotate j = p.rotate (i + j) := by
  ext
  simp [add_assoc]

@[simp] lemma range_rotate (p : Polygon P n) (i : Fin n) :
    range (p.rotate i).vertices = range p.vertices := by
  have := i.neZero
  refine subset_antisymm (fun a ⟨k, hk⟩ ↦ ⟨i + k, hk⟩) ?_
  rintro a ⟨k, rfl⟩
  exact ⟨k - i, by simp⟩

lemma rotate_surjective (p q : Polygon P n) : (∃ i, p.rotate i = q) ↔ (∃ i, q.rotate i = p) := by
  constructor <;>
  · rintro ⟨i, rfl⟩
    have := i.neZero
    exact ⟨-i, by simp [rotate_rotate]⟩

/-! ### Reversal -/

/-- `p.reverse` traverses the vertices of `p` in the opposite order. -/
def reverse (p : Polygon P n) : Polygon P n := ⟨fun k => p k.rev⟩

@[simp] lemma reverse_apply (p : Polygon P n) (k : Fin n) : p.reverse k = p k.rev := rfl

@[simp] lemma reverse_reverse (p : Polygon P n) : p.reverse.reverse = p := by
  ext
  simp

@[simp] lemma range_reverse (p : Polygon P n) : range p.reverse.vertices = range p.vertices :=
  subset_antisymm (fun a ⟨i, hk⟩ ↦ ⟨i.rev, hk⟩) (fun a ⟨i, hk⟩ ↦ ⟨i.rev, by simp [hk]⟩)

/-! ### Subdivision

Inserting a point of an edge as a new vertex. This is the tool that reduces statements about
arbitrary points of `boundary` to statements about vertices. -/

/-- `p.subdivide i a` inserts `a` into the vertex list immediately after vertex `i`. -/
def subdivide (p : Polygon P n) (i : Fin n) (a : P) : Polygon P (n + 1) :=
  ⟨Fin.insertNth i.succ a p.vertices⟩

@[simp] lemma subdivide_apply_succ (p : Polygon P n) (i : Fin n) (a : P) :
    p.subdivide i a i.succ = a := by
  simp [subdivide]

lemma range_subdivide (p : Polygon P n) (i : Fin n) (a : P) :
    range (p.subdivide i a).vertices = insert a (range p.vertices) := by
  apply Subset.antisymm
  · rintro x ⟨j, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove i.succ j with rfl | ⟨j, rfl⟩
    · simp
    · exact mem_insert_of_mem _ ⟨j, by simp [subdivide]⟩
  · rintro x (rfl | ⟨j, rfl⟩)
    · exact ⟨i.succ, by simp⟩
    · exact ⟨i.succ.succAbove j, by simp [subdivide]⟩

/-! ### Edges and the boundary -/

section Edges

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] [PartialOrder R]
  [IsOrderedRing R]

/-- The set of the two endpoints of the `i`-th edge of a polygon. -/
def edgeVertices (p : Polygon P n) (i : Fin n) : Set P := {p i, p (finRotate n i)}

omit [IsOrderedRing R] in
private lemma edgeSet_rotate_eq (p : Polygon P n) (i k : Fin n) :
    (p.rotate i).edgeSet R k = p.edgeSet R (i + k) := by
  simp only [Polygon.edgeSet, rotate_apply, add_finRotate]

private lemma edgeVertices_rotate_eq (p : Polygon P n) (i k : Fin n) :
    (p.rotate i).edgeVertices k = p.edgeVertices (i + k) := by
  simp only [edgeVertices, rotate_apply, add_finRotate]

private lemma edgeSet_reverse_eq (p : Polygon P n) (k : Fin n) :
    p.reverse.edgeSet R k = p.edgeSet R (finRotate n k).rev := by
  rw [Polygon.edgeSet, Polygon.edgeSet]
  simp only [reverse_apply, finRotate_rev_finRotate]
  exact affineSegment_comm R _ _

private lemma edgeVertices_reverse_eq (p : Polygon P n) (k : Fin n) :
    p.reverse.edgeVertices k = p.edgeVertices (finRotate n k).rev := by
  simp only [edgeVertices, reverse_apply, finRotate_rev_finRotate]
  rw [pair_comm]

@[simp] lemma mem_edgeVertices (p : Polygon P n) (i : Fin n) {a : P} :
    a ∈ p.edgeVertices i ↔ a = p i ∨ a = p (finRotate n i) := Iff.rfl

lemma edgeVertices_subset_edgeSet (p : Polygon P n) (i : Fin n) :
    p.edgeVertices i ⊆ p.edgeSet R i := by
  rintro a (rfl | rfl)
  · exact left_mem_affineSegment R _ _
  · exact right_mem_affineSegment R _ _

omit [IsOrderedRing R] in
lemma edgeSet_subset_boundary (p : Polygon P n) (i : Fin n) :
    p.edgeSet R i ⊆ p.boundary R := subset_iUnion (fun i ↦ p.edgeSet R i) i

omit [IsOrderedRing R] in
lemma mem_boundary_iff (p : Polygon P n) {a : P} : a ∈ p.boundary R ↔ ∃ i, a ∈ p.edgeSet R i := by
  simp [Polygon.boundary]

lemma range_vertices_subset_boundary (p : Polygon P n) : range p.vertices ⊆ p.boundary R := by
  rintro a ⟨i, rfl⟩
  exact edgeSet_subset_boundary (R := R) p i (edgeVertices_subset_edgeSet (R := R) p i (Or.inl rfl))

omit [IsOrderedRing R] in
@[simp] lemma boundary_rotate (p : Polygon P n) (i : Fin n) :
    (p.rotate i).boundary R = p.boundary R := by
  ext a
  simp only [mem_boundary_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨i + k, edgeSet_rotate_eq (R := R) p i k ▸ hk⟩, fun ⟨k, hk⟩ ↦ ⟨k - i, ?_⟩⟩
  have := i.neZero
  rw [edgeSet_rotate_eq (R := R), add_comm, sub_add_cancel]
  exact hk

omit [IsOrderedRing R] in
lemma edgeSet_rotate (p : Polygon P n) (i k : Fin n) :
    (p.rotate i).edgeSet R k = p.edgeSet R (i + k) := edgeSet_rotate_eq p i k

@[simp] lemma boundary_reverse (p : Polygon P n) : p.reverse.boundary R = p.boundary R := by
  ext a
  simp only [mem_boundary_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨(finRotate n k).rev, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨(finRotate n k).rev, ?_⟩⟩
    <;> change a ∈ affineSegment R (p <| Fin.rev _) _
  · rwa [finRotate_rev_finRotate, affineSegment_comm]
  · rw [finRotate_rev_finRotate, Fin.rev_rev, affineSegment_comm]
    simpa only [reverse_apply, Fin.rev_rev, finRotate_apply, edgeSet] using hk

end Edges

section Subdivide

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
  [AddTorsor V P]

omit [IsStrictOrderedRing R] in
private lemma edgeSet_subdivide_succAbove (p : Polygon P n) (i j : Fin n) (a : P) :
    (p.subdivide i a).edgeSet R (i.succ.succAbove j) =
      if j = i then affineSegment R (p i) a else p.edgeSet R j := by
  simp only [Polygon.edgeSet, subdivide, Fin.insertNth_apply_succAbove,
    finRotate_succAbove_insert]
  split_ifs with hji
  · subst j
    simp
  · simp

omit [IsStrictOrderedRing R] in
private lemma edgeSet_subdivide_insert (p : Polygon P n) (i : Fin n) (a : P) :
    (p.subdivide i a).edgeSet R i.succ = affineSegment R a (p (finRotate n i)) := by
  rw [Polygon.edgeSet, finRotate_insert]
  simp [subdivide]

@[simp] lemma boundary_subdivide (p : Polygon P n) {i : Fin n} {a : P}
    (ha : a ∈ p.edgeSet R i) : (p.subdivide i a).boundary R = p.boundary R := by
  have hsplit : affineSegment R (p i) a ∪ affineSegment R a (p (finRotate n i)) =
      p.edgeSet R i := by
    simpa [Polygon.edgeSet] using affineSegment_union_eq_affineSegment ha
  ext x
  simp only [mem_boundary_iff]
  constructor
  · rintro ⟨k, hk⟩
    rcases Fin.eq_self_or_eq_succAbove i.succ k with rfl | ⟨j, rfl⟩
    · refine ⟨i, ?_⟩
      rw [edgeSet_subdivide_insert] at hk
      exact hsplit ▸ Or.inr hk
    · by_cases hji : j = i
      · subst j
        refine ⟨i, ?_⟩
        rw [edgeSet_subdivide_succAbove, ite_eq_left rfl] at hk
        exact hsplit ▸ Or.inl hk
      · refine ⟨j, ?_⟩
        simpa [edgeSet_subdivide_succAbove, hji] using hk
  · rintro ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rw [← hsplit] at hj
      rcases hj with hj | hj
      · refine ⟨i.succ.succAbove i, ?_⟩
        rw [edgeSet_subdivide_succAbove, ite_eq_left rfl]
        exact hj
      · refine ⟨i.succ, ?_⟩
        rw [edgeSet_subdivide_insert]
        exact hj
    · refine ⟨i.succ.succAbove j, ?_⟩
      rw [edgeSet_subdivide_succAbove, ite_eq_right hji]
      exact hj

end Subdivide

section Edges

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] [PartialOrder R]
  [IsOrderedRing R]

omit [IsOrderedRing R] in
@[simp] lemma boundary_cast (p : Polygon P n) {m : ℕ} (h : n = m) :
    (p.cast h).boundary R = p.boundary R := by
  subst m
  simp

/-! ### Nondegeneracy -/

@[simp] lemma hasNondegenerateEdges_rotate (p : Polygon P n) (i : Fin n) :
    (p.rotate i).HasNondegenerateEdges ↔ p.HasNondegenerateEdges := by
  constructor
  · intro h k
    have := i.neZero
    have hk := h (k - i)
    change p (i + (k - i)) ≠ p (i + finRotate n (k - i)) at hk
    rw [add_comm i, sub_add_cancel, add_finRotate, add_comm i, sub_add_cancel] at hk
    exact hk
  · intro h k
    change p (i + k) ≠ p (i + finRotate n k)
    rw [add_finRotate]
    exact h (i + k)

@[simp] lemma hasNondegenerateEdges_reverse (p : Polygon P n) :
    p.reverse.HasNondegenerateEdges ↔ p.HasNondegenerateEdges := by
  constructor <;> intro h k
  · have hk := h (finRotate n k).rev
    change p (finRotate n k).rev.rev ≠
      p (finRotate n (finRotate n k).rev).rev at hk
    rw [Fin.rev_rev, finRotate_rev_finRotate, Fin.rev_rev] at hk
    exact hk.symm
  · have hk := h (finRotate n k).rev
    change p k.rev ≠ p (finRotate n k).rev
    rw [finRotate_rev_finRotate] at hk
    exact hk.symm

/-! ### Simple polygons -/

variable (R) in
/-- A polygon is *simple* if it has at least two vertices, its vertices are distinct, and any two
distinct edges meet only in endpoints common to both. This is the polygonal form of the statement
that the closed curve traced out by the polygon is injective on `[0, 1)`; see
`Polygon.isSimple_iff_isSimpleLoop`. -/
def IsSimple (p : Polygon P n) : Prop :=
  2 ≤ n ∧ Injective p.vertices ∧
    ∀ i j : Fin n, i ≠ j → p.edgeSet R i ∩ p.edgeSet R j ⊆ p.edgeVertices i ∩ p.edgeVertices j

variable {p : Polygon P n} {i j : Fin n} {a : P}

omit [IsOrderedRing R] in
lemma IsSimple.two_le (h : p.IsSimple R) : 2 ≤ n := h.1

omit [IsOrderedRing R] in
lemma IsSimple.injective (h : p.IsSimple R) : Injective p.vertices := h.2.1

omit [IsOrderedRing R] in
lemma IsSimple.edgeSet_inter_subset (h : p.IsSimple R) (hij : i ≠ j) :
    p.edgeSet R i ∩ p.edgeSet R j ⊆ p.edgeVertices i ∩ p.edgeVertices j := h.2.2 i j hij

omit [IsOrderedRing R] in
lemma IsSimple.neZero (h : p.IsSimple R) : NeZero n := ⟨by have := h.two_le; omega⟩

omit [IsOrderedRing R] in
/-- Nondegeneracy of the edges is a consequence: it is `Injective p.vertices` together with
`2 ≤ n`, which is what makes `i ≠ finRotate n i`. -/
lemma IsSimple.hasNondegenerateEdges (h : p.IsSimple R) : p.HasNondegenerateEdges := by
  intro i
  exact h.injective.ne (finRotate_ne_self_of_two_le h.two_le i).symm

omit [IsOrderedRing R] in
private lemma IsSimple.rotate (h : p.IsSimple R) (i : Fin n) : (p.rotate i).IsSimple R := by
  refine ⟨h.two_le, ?_, ?_⟩
  · intro j k hjk
    apply h.injective at hjk
    have := i.neZero
    exact add_left_cancel hjk
  · intro j k hjk
    rw [edgeSet_rotate_eq (R := R), edgeSet_rotate_eq (R := R),
      edgeVertices_rotate_eq, edgeVertices_rotate_eq]
    apply h.edgeSet_inter_subset
    have := i.neZero
    exact fun hjk' ↦ hjk (add_left_cancel hjk')

omit [IsOrderedRing R] in
@[simp] lemma isSimple_rotate (i : Fin n) : (p.rotate i).IsSimple R ↔ p.IsSimple R := by
  constructor
  · intro h
    have := i.neZero
    simpa [rotate_rotate] using h.rotate (-i)
  · exact fun h ↦ h.rotate i

private lemma IsSimple.reverse (h : p.IsSimple R) : p.reverse.IsSimple R := by
  refine ⟨h.two_le, h.injective.comp Fin.rev_injective, ?_⟩
  intro i j hij
  rw [edgeSet_reverse_eq (R := R), edgeSet_reverse_eq (R := R),
    edgeVertices_reverse_eq, edgeVertices_reverse_eq]
  apply h.edgeSet_inter_subset
  intro heq
  apply hij
  apply Fin.rev_injective
  apply (finRotate n).injective
  simpa using congr_arg Fin.rev heq

@[simp] lemma isSimple_reverse : p.reverse.IsSimple R ↔ p.IsSimple R := by
  constructor
  · intro h
    simpa using h.reverse
  · exact IsSimple.reverse

omit [IsOrderedRing R] in
/-- Two distinct *nonadjacent* edges of a simple polygon are disjoint. -/
lemma IsSimple.edgeSet_disjoint (h : p.IsSimple R) (hij : i ≠ j) (h1 : finRotate n i ≠ j)
    (h2 : finRotate n j ≠ i) : Disjoint (p.edgeSet R i) (p.edgeSet R j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hx := h.edgeSet_inter_subset hij ⟨hxi, hxj⟩
  simp only [mem_inter_iff, mem_edgeVertices] at hx
  rcases hx with ⟨hxi | hxi, hxj | hxj⟩
  · exact hij (h.injective (hxi.symm.trans hxj))
  · exact h2 (h.injective (hxj.symm.trans hxi))
  · exact h1 (h.injective (hxi.symm.trans hxj))
  · exact hij ((finRotate n).injective (h.injective (hxi.symm.trans hxj)))

end Edges

section StrictOrderedEdges

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]
  {p : Polygon P n} {i : Fin n}

private lemma IsSimple.three_le_aux (h : p.IsSimple R) : 3 ≤ n := by
  by_contra hn
  have hn' : n = 2 := by have := h.two_le; omega
  subst n
  have hp : p 0 ≠ p 1 := h.injective.ne (by decide)
  have hm := sbtw_midpoint_of_ne R hp
  have hmem := h.edgeSet_inter_subset (i := 0) (j := 1) (by decide)
  have hm0 : midpoint R (p 0) (p 1) ∈ p.edgeSet R 0 := by
    simpa [Polygon.edgeSet, Wbtw] using hm.wbtw
  have hm1 : midpoint R (p 0) (p 1) ∈ p.edgeSet R 1 := by
    simpa [Polygon.edgeSet, Wbtw, affineSegment_comm R] using hm.wbtw
  have hend := (hmem ⟨hm0, hm1⟩).1
  rcases hend with hend | hend
  · exact hm.ne_left hend
  · exact hm.ne_right hend

/-- Two *adjacent* edges of a simple polygon meet exactly in their shared vertex. -/
lemma IsSimple.edgeSet_inter_edgeSet (h : p.IsSimple R) (hne : i ≠ finRotate n i) :
    p.edgeSet R i ∩ p.edgeSet R (finRotate n i) = {p (finRotate n i)} := by
  apply Subset.antisymm
  · intro x hx
    have hs := h.edgeSet_inter_subset hne hx
    simp only [mem_inter_iff, mem_edgeVertices] at hs
    have hn := h.three_le_aux
    rcases hs with ⟨hxi | hxi, hxj | hxj⟩
    · exact (hne (h.injective (hxi.symm.trans hxj))).elim
    · exact (finRotate_finRotate_ne_self_of_three_le hn i
        (h.injective (hxi.symm.trans hxj)).symm).elim
    · simpa using hxi
    · exact (finRotate_ne_self_of_two_le h.two_le (finRotate n i)
        (h.injective (hxi.symm.trans hxj)).symm).elim
  · rintro x rfl
    exact ⟨right_mem_affineSegment R _ _, left_mem_affineSegment R _ _⟩

end StrictOrderedEdges

section Edges


variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] [PartialOrder R]
  [IsOrderedRing R]

variable {p : Polygon P n} {i j : Fin n} {a : P}

/-- A vertex of a simple polygon lies on exactly two edges: the one it starts and the one it
ends. This is the statement that is impossible to formulate for a based closed path. -/
lemma IsSimple.mem_edgeSet_iff_of_vertex (h : p.IsSimple R) :
    p i ∈ p.edgeSet R j ↔ j = i ∨ finRotate n j = i := by
  constructor
  · intro hij
    by_cases hji : j = i
    · exact Or.inl hji
    · have hi : p i ∈ p.edgeSet R i := left_mem_affineSegment R _ _
      have hs := h.edgeSet_inter_subset hji ⟨hij, hi⟩
      rcases hs.1 with hs | hs
      · exact Or.inl (h.injective hs).symm
      · exact Or.inr (h.injective hs).symm
  · rintro (rfl | hj)
    · exact left_mem_affineSegment R _ _
    · rw [← hj]
      exact right_mem_affineSegment R _ _

omit [IsOrderedRing R] in
/-- A point of the boundary of a simple polygon that is not a vertex lies on a unique edge. -/
lemma IsSimple.existsUnique_edge (h : p.IsSimple R) (ha : a ∈ p.boundary R)
    (hav : a ∉ range p.vertices) : ∃! i, a ∈ p.edgeSet R i := by
  obtain ⟨i, hi⟩ := (mem_boundary_iff p).mp ha
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  have hs := h.edgeSet_inter_subset hij ⟨hj, hi⟩
  rcases hs.1 with hs | hs
  · exact hav ⟨j, hs.symm⟩
  · exact hav ⟨finRotate n j, hs.symm⟩

end Edges

/-! ### Polygons in a module

Over a module, `edgeSet` agrees with `segment`, which is the form used by the polygonal path API.
-/

section Module

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup V] [Module R V]
  {p : Polygon V n} {i : Fin n}

lemma edgeSet_eq_segment (p : Polygon V n) (i : Fin n) :
    p.edgeSet R i = segment R (p i) (p (finRotate n i)) :=
  affineSegment_eq_segment R _ _

lemma boundary_eq_iUnion_segment (p : Polygon V n) :
    p.boundary R = ⋃ i, segment R (p i) (p (finRotate n i)) := by
  simp_rw [Polygon.boundary, edgeSet_eq_segment]

end Module

/-! ### Degeneracy bounds

A simple polygon has at least three vertices: `n = 1` is excluded by nondegeneracy of edges and
`n = 2` by the fact that the two edges of a digon share more than their endpoints. The latter
needs enough points in `R` to produce an interior point of a segment. -/

section StrictOrdered

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [hDense : DenselyOrdered R]
  [AddCommGroup V] [Module R V] [hTorsion : Module.IsTorsionFree R V] {p : Polygon V n}

lemma IsSimple.three_le (h : p.IsSimple R) : 3 ≤ n := by
  let _ := hDense
  let _ := hTorsion
  exact h.three_le_aux

end StrictOrdered

/-! ### Topology of the boundary -/

section Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {p : Polygon V n} {i : Fin n} {a : V}

private lemma isCompact_edgeSet (p : Polygon V n) (i : Fin n) :
    IsCompact (p.edgeSet ℝ i) := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

private lemma isConnected_edgeSet (p : Polygon V n) (i : Fin n) :
    IsConnected (p.edgeSet ℝ i) := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  exact (isConnected_Icc zero_le_one).image _ AffineMap.lineMap_continuous.continuousOn

lemma isCompact_boundary (p : Polygon V n) : IsCompact (p.boundary ℝ) := by
  rw [Polygon.boundary]
  exact isCompact_iUnion fun i ↦ isCompact_edgeSet p i

lemma isClosed_boundary [T2Space V] (p : Polygon V n) : IsClosed (p.boundary ℝ) :=
  (isCompact_boundary p).isClosed

lemma isConnected_boundary [NeZero n] (p : Polygon V n) : IsConnected (p.boundary ℝ) := by
  rw [Polygon.boundary]
  apply IsConnected.iUnion_of_reflTransGen (fun i ↦ isConnected_edgeSet p i)
  intro i j
  let r : Fin n → Fin n → Prop := fun i j ↦ (p.edgeSet ℝ i ∩ p.edgeSet ℝ j).Nonempty
  have hstep (k : Fin n) : r k (finRotate n k) := by
    exact ⟨p (finRotate n k), right_mem_affineSegment ℝ _ _, left_mem_affineSegment ℝ _ _⟩
  have hiter (k : ℕ) : Relation.ReflTransGen r i ((finRotate n)^[k] i) := by
    induction k with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ k hk =>
      rw [Function.iterate_succ_apply']
      exact hk.tail (hstep _)
  have := i.neZero
  have hcycle : finCycle (j - i) = (finRotate n)^[(j - i).val] :=
    finCycle_eq_finRotate_iterate
  have heq : (finRotate n)^[(j - i).val] i = j := by
    rw [← congr_fun hcycle i]
    simp [finCycle_apply]
  rw [← heq]
  exact hiter (j - i).val

/-- Near a point of the boundary of a simple polygon which is not a vertex, the boundary looks
like the unique edge containing that point. This is the local structure lemma that the
Jordan curve argument runs on; it has nothing to do with simplicity beyond the uniqueness of the
edge, so it is stated using only that. -/
lemma exists_nhds_inter_boundary_eq [T2Space V]
    (h : ∃! i, a ∈ p.edgeSet ℝ i) (hi : a ∈ p.edgeSet ℝ i) :
    ∃ U ∈ nhds a, U ∩ p.boundary ℝ = U ∩ p.edgeSet ℝ i := by
  let C : Set V := ⋃ j : {j : Fin n // j ≠ i}, p.edgeSet ℝ j
  have hCa : a ∉ C := by
    simp only [C, mem_iUnion, Subtype.exists, exists_prop, not_exists, not_and]
    intro j hji haj
    exact hji (h.unique hi haj).symm
  have hCclosed : IsClosed C := by
    exact isClosed_iUnion_of_finite fun j ↦ (isCompact_edgeSet p j).isClosed
  refine ⟨Cᶜ, hCclosed.isOpen_compl.mem_nhds hCa, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_compl_iff, mem_boundary_iff]
  constructor
  · rintro ⟨hxC, j, hxj⟩
    refine ⟨hxC, ?_⟩
    by_cases hji : j = i
    · simpa [hji] using hxj
    · exact (hxC (mem_iUnion_of_mem ⟨j, hji⟩ hxj)).elim
  · rintro ⟨hxC, hxi⟩
    exact ⟨hxC, i, hxi⟩

/-- Near a vertex of a simple polygon, the boundary looks like the union of the two edges at that
vertex. -/
lemma IsSimple.exists_nhds_inter_boundary_eq_of_vertex [T2Space V]
    (h : p.IsSimple ℝ) (i : Fin n) :
    ∃ U ∈ nhds (p i), ∃ j, finRotate n j = i ∧
      U ∩ p.boundary ℝ = U ∩ (p.edgeSet ℝ i ∪ p.edgeSet ℝ j) :=
  by
  let _ := h.neZero
  let j := (finRotate n).symm i
  have hj : finRotate n j = i := (finRotate n).apply_symm_apply i
  let C : Set V := ⋃ k : {k : Fin n // k ≠ i ∧ k ≠ j}, p.edgeSet ℝ k
  have hCa : p i ∉ C := by
    simp only [C, mem_iUnion, Subtype.exists, exists_prop, not_exists, not_and]
    intro k hkij hik
    rcases (h.mem_edgeSet_iff_of_vertex).mp hik with rfl | hk
    · exact hkij.1 rfl
    · exact hkij.2 ((finRotate n).injective (hk.trans hj.symm))
  have hCclosed : IsClosed C := by
    exact isClosed_iUnion_of_finite fun k ↦ (isCompact_edgeSet p k).isClosed
  refine ⟨Cᶜ, hCclosed.isOpen_compl.mem_nhds hCa, j, hj, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_compl_iff, mem_boundary_iff, mem_union]
  constructor
  · rintro ⟨hxC, k, hxk⟩
    refine ⟨hxC, ?_⟩
    by_cases hki : k = i
    · exact Or.inl (hki ▸ hxk)
    · by_cases hkj : k = j
      · exact Or.inr (hkj ▸ hxk)
      · exact (hxC (mem_iUnion_of_mem ⟨k, hki, hkj⟩ hxk)).elim
  · rintro ⟨hxC, hxi | hxj⟩
    · exact ⟨hxC, i, hxi⟩
    · exact ⟨hxC, j, hxj⟩

end Topology

end Polygon
