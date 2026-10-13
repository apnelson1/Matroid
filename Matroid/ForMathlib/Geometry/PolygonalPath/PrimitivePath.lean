module

public import Matroid.ForMathlib.Geometry.PolygonalPath.SimpleLoop
public import Matroid.ForMathlib.Topology.PrimitivePath

/-!
# Primitive polygonal paths

This file owns only polygonal-specific characterizations and consequences of `Path.IsPrimitive`:
simplicity/length, segment uniqueness, append decomposition, and local segment structure.
-/

@[expose] public section

open Set Function
open scoped unitInterval

namespace PolygonalPath

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  {x y a : α} {P : PolygonalPath x y} [ContinuousAdd α]

/-- Polygonal characterization of topological primitiveness: a positive-length simple arc or a
simple closed polygonal path. -/
theorem isPrimitive_iff : P.toPath.IsPrimitive ↔
    (P.IsSimple ∧ 0 < P.length) ∨ ∃ h : y = x, (P.cast rfl h).IsSimpleLoop := by
  constructor
  · intro h
    obtain rfl | hxy := eq_or_ne x y
    · exact Or.inr ⟨rfl, h.isSimpleLoop⟩
    · exact Or.inl ((injective_toPath_iff P).mp (h.injective hxy))
  · rintro (⟨h, hlen⟩ | ⟨rfl, h⟩)
    · exact Path.IsPrimitive.of_injective ((injective_toPath_iff P).mpr ⟨h, hlen⟩)
    · exact (show Path.IsSimpleLoop P.toPath from h).isPrimitive

lemma isPrimitive_iff_isSimpleLoop {P : PolygonalPath x x} :
    P.toPath.IsPrimitive ↔ P.IsSimpleLoop :=
  Path.isPrimitive_iff_isSimpleLoop

@[simp]
lemma isPrimitive_cast {x' y' : α} (hx : x = x') (hy : y = y') :
    (P.cast hx hy).toPath.IsPrimitive ↔ P.toPath.IsPrimitive := by
  subst x' y'
  rfl

lemma IsSimple.isPrimitive (h : P.IsSimple) (hP : 0 < P.length) :
    P.toPath.IsPrimitive := by
  rw [isPrimitive_iff]
  exact Or.inl ⟨h, hP⟩

lemma IsSimpleLoop.isPrimitive {P : PolygonalPath x x} (h : P.toPath.IsSimpleLoop) :
    P.toPath.IsPrimitive := by
  rw [isPrimitive_iff]
  exact Or.inr ⟨rfl, h⟩

lemma isPrimitive_iff_isSimple (hxy : x ≠ y) : P.toPath.IsPrimitive ↔ P.IsSimple := by
  rw [Path.isPrimitive_iff]
  simp [hxy, injective_toPath_iff, P.length_pos_of_ne hxy]

/-- A nonvertex point of a primitive polygonal path lies on a unique polygonal segment. -/
lemma existsUnique_edge_of_isPrimitive (h : P.toPath.IsPrimitive) (ha : a ∈ P.toSet)
    (hav : a ∉ P.vertices) : ∃! s ∈ P.edges, a ∈ segment ℝ s.1 s.2 := by
  rw [isPrimitive_iff] at h
  obtain ⟨h, _⟩ | ⟨rfl, h⟩ := h
  · exact h.existsUnique_edge ha hav
  · rw [cast_rfl] at h
    exact IsSimpleLoop.existsUnique_edge h ha hav

/-- Removing the endpoints from a primitive polygonal path gives the image of the open parameter
interval. -/
lemma toSet_diff_endpoints_of_isPrimitive (h : P.toPath.IsPrimitive) :
    P.toSet \ {x, y} = P.toPath '' Ioo (0 : I) 1 := by
  rw [toSet_eq_range_toPath]
  exact h.range_diff_endpoints

lemma toSet_diff_endpoints_nonempty_of_isPrimitive (h : P.toPath.IsPrimitive) :
    (P.toSet \ {x, y}).Nonempty := by
  rw [toSet_diff_endpoints_of_isPrimitive h]
  exact (nonempty_Ioo.2 (zero_lt_one : (0 : I) < 1)).image _

/-- The open part of a primitive polygonal path is path-connected. -/
lemma isPathConnected_toSet_diff_endpoints_of_isPrimitive (h : P.toPath.IsPrimitive) :
    IsPathConnected (P.toSet \ {x, y}) := by
  rw [toSet_diff_endpoints_of_isPrimitive h]
  exact (unitInterval.isPathConnected_Ioo (zero_lt_one : (0 : I) < 1)).image P.toPath.continuous

lemma isConnected_toSet_diff_endpoints_of_isPrimitive (h : P.toPath.IsPrimitive) :
    IsConnected (P.toSet \ {x, y}) :=
  isPathConnected_toSet_diff_endpoints_of_isPrimitive h |>.isConnected

lemma injOn_toPath_Ioo_of_isPrimitive (h : P.toPath.IsPrimitive) :
    InjOn P.toPath (Ioo (0 : I) 1) :=
  h.injOn_Ioo

/-! ### Splitting at an interior polygonal vertex -/

section Append

variable {x p y : α} {A : PolygonalPath x p} {B : PolygonalPath p y}

@[grind →]
lemma isSimple_left_of_isPrimitive (h : (A.append B).toPath.IsPrimitive) (hxp : x ≠ p) :
    A.IsSimple := by
  rw [isPrimitive_iff] at h
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.of_append_left
  · subst y
    rw [cast_rfl] at hL
    exact IsSimpleLoop.isSimple_of_append_left hxp hL

@[grind →]
lemma isSimple_right_of_isPrimitive
    (h : (A.append B).toPath.IsPrimitive) (hxp : x ≠ p) : B.IsSimple := by
  rw [isPrimitive_iff] at h
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.of_append_right
  · subst y
    rw [cast_rfl] at hL
    exact (isSimpleLoop_append_iff hxp).mp hL |>.2.1

@[grind →]
lemma toSet_inter_subset_of_isPrimitive
    (h : (A.append B).toPath.IsPrimitive) (hxp : x ≠ p) :
    A.toSet ∩ B.toSet ⊆ ({x, p} : Set α) := by
  rw [isPrimitive_iff] at h
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · intro u hu
    exact Or.inr ((isSimple_append_iff.mp hS).2.2 hu)
  · subst y
    rw [cast_rfl] at hL
    exact ((isSimpleLoop_append_iff hxp).mp hL).2.2.le

end Append

private lemma symm_of_isPrimitive (h : P.toPath.IsPrimitive) :
    P.reverse.toPath.IsPrimitive := by
  rw [isPrimitive_iff] at h ⊢
  rcases h with ⟨hP, hlen⟩ | ⟨rfl, hloop⟩
  · exact Or.inl ⟨isSimple_reverse.mpr hP, by simpa using hlen⟩
  · exact Or.inr ⟨rfl, by simpa using isSimpleLoop_reverse.mpr hloop⟩

lemma isPrimitive_reverse_iff :
    P.reverse.toPath.IsPrimitive ↔ P.toPath.IsPrimitive := by
  refine ⟨fun h ↦ ?_, symm_of_isPrimitive⟩
  have := symm_of_isPrimitive h
  rwa [reverse_reverse] at this

end PolygonalPath

namespace PolygonalPath

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  {x y a : α} {P : PolygonalPath x y}

/-- Locally, a primitive polygonal arc or circle agrees with its unique segment through a nonvertex
point. -/
lemma exists_nhds_inter_toSet_eq_of_isPrimitive [IsTopologicalAddGroup α] [T2Space α]
    (h : P.toPath.IsPrimitive) (ha : a ∈ P.toSet) (hav : a ∉ P.vertices) {s : α × α}
    (hs : s ∈ P.edges) (has : a ∈ segment ℝ s.1 s.2) :
    ∃ U ∈ nhds a, U ∩ P.toSet = U ∩ segment ℝ s.1 s.2 :=
  P.exists_nhds_inter_toSet_eq (existsUnique_edge_of_isPrimitive h ha hav) hs has

end PolygonalPath
