module

public import Matroid.ForMathlib.Geometry.PolygonalPath.SimpleLoop

/-!
# Paths that are either a simple arc or a simple loop

`IsSimpleArcOrLoop` is the disjunction of a positive-length simple path and a simple closed path.
It describes an embedding of an interval or a circle, allowing the endpoints to coincide only in
the loop case. The shared consequences of the two branches include uniqueness of the segment
through every nonvertex point and the corresponding local neighborhood description.

## Main definitions

* `PolygonalPath.IsSimpleArcOrLoop`

## Main statements

* `PolygonalPath.IsSimpleArcOrLoop.existsUnique_edge`
* `PolygonalPath.IsSimpleArcOrLoop.exists_nhds_inter_toSet_eq`
-/

@[expose] public section

open Set Function
open scoped unitInterval

namespace PolygonalPath

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
   {x y a : α} {P : PolygonalPath x y} [ContinuousAdd α]

/-- `P` is an embedded arc or an embedded circle: either `P.IsSimple` with at least one segment
(so `x ≠ y` and `toPath` is injective), or `P` is closed and `P.IsSimpleLoop`. The equality of
endpoints in the second branch is only propositional — an edge of a graph is a loop by a *proof*
that its ends agree — so the branch is stated with an explicit `cast`. -/
def IsSimpleArcOrLoop (P : PolygonalPath x y) : Prop :=
  (P.IsSimple ∧ 0 < P.length) ∨ ∃ h : y = x, (P.cast rfl h).IsSimpleLoop

@[simp]
lemma isSimpleArcOrLoop_cast {x' y' : α} (hx : x = x') (hy : y = y') :
    (P.cast hx hy).IsSimpleArcOrLoop ↔ P.IsSimpleArcOrLoop := by
  subst x'
  subst y'
  rfl

lemma IsSimple.isSimpleArcOrLoop (h : P.IsSimple) (hP : 0 < P.length) : P.IsSimpleArcOrLoop :=
  Or.inl ⟨h, hP⟩

lemma IsSimpleLoop.isSimpleArcOrLoop {P : PolygonalPath x x} (h : P.IsSimpleLoop) :
    P.IsSimpleArcOrLoop := Or.inr ⟨rfl, by rwa [cast_rfl]⟩

/-- With distinct endpoints there is no loop branch, so the disjunction collapses. -/
lemma isSimpleArcOrLoop_iff_isSimple (hxy : x ≠ y) : P.IsSimpleArcOrLoop ↔ P.IsSimple := by
  refine ⟨fun h ↦ h.elim And.left fun ⟨hyx, _⟩ ↦ absurd hyx.symm hxy,
    fun h ↦ h.isSimpleArcOrLoop ?_⟩
  cases P with
  | nil => exact (hxy rfl).elim
  | cons => simp

/-- With equal endpoints the arc branch is degenerate: a simple path from `x` to `x` is `nil x`.
So on a loop the content is `IsSimpleLoop`, up to the trivial path. -/
lemma isSimpleArcOrLoop_iff_isSimpleLoop {P : PolygonalPath x x} (hP : 0 < P.length) :
    P.IsSimpleArcOrLoop ↔ P.IsSimpleLoop := by
  refine ⟨fun h ↦ ?_, IsSimpleLoop.isSimpleArcOrLoop⟩
  obtain ⟨h, _⟩ | ⟨w, h⟩ := h
  · exact (h.ne hP rfl).elim
  · rwa [Subsingleton.elim w (rfl : x = x), cast_rfl] at h

/-- A point of the image which is not a vertex lies on a unique segment. This is the single
statement that both branches supply and everything downstream consumes. -/
lemma IsSimpleArcOrLoop.existsUnique_edge (h : P.IsSimpleArcOrLoop) (ha : a ∈ P.toSet)
    (hav : a ∉ P.vertices) : ∃! s ∈ P.edges, a ∈ segment ℝ s.1 s.2 := by
  obtain ⟨h, _⟩ | ⟨rfl, h⟩ := h
  · exact h.existsUnique_edge ha hav
  · rw [cast_rfl] at h
    exact h.existsUnique_edge ha hav

private lemma toSet_diff_endpoints_of_injective (h : Injective P.toPath) :
    P.toSet \ {x, y} = P.toPath '' Ioo (0 : I) 1 := by
  have hI : (univ : Set I) \ {0, 1} = Ioo 0 1 := by
    ext t
    simp [Ioo, unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one]
  rw [toSet_eq_range_toPath, ← image_univ, ← hI, h.injOn.image_sdiff_subset (subset_univ _),
    image_insert_eq, image_singleton, Path.source, Path.target]

private lemma toSet_diff_endpoints_of_isSimpleLoop {P : PolygonalPath x x} (h : P.IsSimpleLoop) :
    P.toSet \ {x, x} = P.toPath '' Ioo (0 : I) 1 := by
  have hI : Ico (0 : I) 1 \ {0} = Ioo 0 1 := by
    ext t
    simp [Ico, Ioo, unitInterval.pos_iff_ne_zero, and_comm]
  have hrange : range P.toPath = P.toPath '' Ico 0 1 := by
    refine subset_antisymm ?_ (image_subset_range _ _)
    rintro _ ⟨t, rfl⟩
    by_cases ht : t = 1
    · exact ⟨0, by simp, by rw [ht, Path.source, Path.target]⟩
    · exact ⟨t, ⟨t.2.1, lt_of_le_of_ne t.2.2 ht⟩, rfl⟩
  have himg := h.image_sdiff_subset (singleton_subset_iff.mpr (mem_Ico.mpr ⟨le_rfl, zero_lt_one⟩))
  rw [toSet_eq_range_toPath, hrange, show ({x, x} : Set α) = {x} from by simp, ← hI, himg,
    image_singleton, Path.source]

/-- The image of an embedded arc or circle, with its endpoints removed, is the image of the open
interval. -/
lemma IsSimpleArcOrLoop.toSet_diff_endpoints (h : P.IsSimpleArcOrLoop) :
    P.toSet \ {x, y} = P.toPath '' Ioo (0 : I) 1 := by
  obtain ⟨hs, hlen⟩ | ⟨rfl, h⟩ := h
  · exact toSet_diff_endpoints_of_injective ((injective_toPath_iff P).2 ⟨hs, hlen⟩)
  · rw [cast_rfl] at h
    exact toSet_diff_endpoints_of_isSimpleLoop h

/-- An embedded arc or circle is injectively parametrized on the open interval. -/
lemma IsSimpleArcOrLoop.injOn_toPath_Ioo (h : P.IsSimpleArcOrLoop) :
    InjOn P.toPath (Ioo (0 : I) 1) := by
  obtain ⟨hs, hlen⟩ | ⟨rfl, h⟩ := h
  · exact ((injective_toPath_iff P).2 ⟨hs, hlen⟩).injOn
  · rw [cast_rfl] at h
    exact (show Path.IsSimpleLoop P.toPath from h).injOn_ioo

/-! ### Splitting a simple arc or loop at an interior vertex

Cutting at a vertex other than the source leaves two simple pieces meeting only at the shared
endpoints — whichever branch of `IsSimpleArcOrLoop` holds. -/

section Append

variable {x p y : α} {A : PolygonalPath x p} {B : PolygonalPath p y}

@[grind →]
lemma IsSimpleArcOrLoop.isSimple_left {x p y : α}
    {A : PolygonalPath x p} {B : PolygonalPath p y}
    (h : (A.append B).IsSimpleArcOrLoop) (hxp : x ≠ p) : A.IsSimple := by
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.of_append_left
  · subst y
    rw [cast_rfl] at hL
    exact IsSimpleLoop.isSimple_of_append_left hxp hL

@[grind →]
lemma IsSimpleArcOrLoop.isSimple_right {x p y : α}
    {A : PolygonalPath x p} {B : PolygonalPath p y}
    (h : (A.append B).IsSimpleArcOrLoop) (hxp : x ≠ p) : B.IsSimple := by
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.of_append_right
  · subst y
    rw [cast_rfl] at hL
    exact (isSimpleLoop_append_iff hxp).mp hL |>.2.1

@[grind →]
lemma IsSimpleArcOrLoop.toSet_inter_subset {x p y : α}
    {A : PolygonalPath x p} {B : PolygonalPath p y}
    (h : (A.append B).IsSimpleArcOrLoop) (hxp : x ≠ p) :
    A.toSet ∩ B.toSet ⊆ ({x, p} : Set α) := by
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · intro u hu
    exact Or.inr ((isSimple_append_iff.mp hS).2.2 hu)
  · subst y
    rw [cast_rfl] at hL
    exact ((isSimpleLoop_append_iff hxp).mp hL).2.2.le

end Append

end PolygonalPath

namespace PolygonalPath

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  {x y a : α} {P : PolygonalPath x y}

/-- Locally, an embedded polygonal arc or circle looks like the unique segment through the given
point. -/
lemma IsSimpleArcOrLoop.exists_nhds_inter_toSet_eq [IsTopologicalAddGroup α] [T2Space α]
    (h : P.IsSimpleArcOrLoop) (ha : a ∈ P.toSet) (hav : a ∉ P.vertices) {s : α × α}
    (hs : s ∈ P.edges) (has : a ∈ segment ℝ s.1 s.2) :
    ∃ U ∈ nhds a, U ∩ P.toSet = U ∩ segment ℝ s.1 s.2 :=
  P.exists_nhds_inter_toSet_eq (h.existsUnique_edge ha hav) hs has

end PolygonalPath
