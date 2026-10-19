module

public import Matroid.ForMathlib.Geometry.PolygonalPath.SimpleLoop
public import Matroid.ForMathlib.Topology.PrimitivePath
public import Mathlib.Topology.Connected.Clopen

/-!
# Primitive polygonal paths

This file owns only polygonal-specific characterizations and consequences of `Path.IsPrimitive`:
simplicity/length, subdivision, segment uniqueness, append decomposition, polygonal subarcs,
and local segment structure.
-/

@[expose] public section

open Set Function Topology Set.Notation
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

/-- Inserting a point of the image as a vertex preserves primitivity. -/
@[simp]
lemma isPrimitive_subdivide_iff (ha : a ∈ P.toSet) :
    (P.subdivide ha).toPath.IsPrimitive ↔ P.toPath.IsPrimitive := by
  obtain rfl | hxy := eq_or_ne x y
  · rw [isPrimitive_iff_isSimpleLoop, isPrimitive_iff_isSimpleLoop, isSimpleLoop_subdivide_iff]
  rw [isPrimitive_iff_isSimple hxy, isPrimitive_iff_isSimple hxy, isSimple_subdivide_iff]

/-- A nonvertex point of a primitive polygonal path lies on a unique polygonal segment. -/
lemma existsUnique_edge_of_isPrimitive (h : P.toPath.IsPrimitive) (ha : a ∈ P.toSet)
    (hav : a ∉ P.vertices) : ∃! s ∈ P.edges, a ∈ segment ℝ s.1 s.2 := by
  obtain ⟨h, _⟩ | ⟨rfl, h⟩ := isPrimitive_iff.mp h
  · exact h.existsUnique_edge ha hav
  rw [cast_rfl] at h
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

lemma injOn_toPath_Ioo_of_isPrimitive (h : P.toPath.IsPrimitive) : InjOn P.toPath (Ioo (0 : I) 1) :=
  h.injOn_Ioo

/-! ### Splitting at an interior polygonal vertex -/

section Append

variable {x p y : α} {A : PolygonalPath x p} {B : PolygonalPath p y}

/-- With a junction distinct from the source, an append is primitive exactly when its pieces
are simple and meet only at endpoints common to both pieces. -/
lemma isPrimitive_append_iff (hxp : x ≠ p) :
    (A.append B).toPath.IsPrimitive ↔ A.IsSimple ∧ B.IsSimple ∧
      A.toSet ∩ B.toSet ⊆ ({x, p} : Set α) ∩ {p, y} := by
  obtain rfl | hxy := eq_or_ne x y
  · rw [isPrimitive_iff_isSimpleLoop, isSimpleLoop_append_iff hxp]
    refine ⟨fun ⟨hA, hB, hAB⟩ ↦ ⟨hA, hB, ?_⟩,
      fun ⟨hA, hB, hAB⟩ ↦ ⟨hA, hB, (hAB.trans inter_subset_left).antisymm ?_⟩⟩
    · rw [hAB, pair_comm p x, inter_self]
    rintro z (rfl | rfl)
    · exact ⟨A.mem_toSet_of_mem_vertices A.first_mem_vertices,
        B.mem_toSet_of_mem_vertices B.last_mem_vertices⟩
    exact ⟨A.mem_toSet_of_mem_vertices A.last_mem_vertices,
      B.mem_toSet_of_mem_vertices B.first_mem_vertices⟩
  rw [isPrimitive_iff_isSimple hxy, isSimple_append_iff]
  refine ⟨fun ⟨hA, hB, hAB⟩ ↦ ⟨hA, hB, fun z hz ↦ ?_⟩,
    fun ⟨hA, hB, hAB⟩ ↦ ⟨hA, hB, fun z hz ↦ ?_⟩⟩
  · obtain rfl : z = p := hAB hz
    simp
  grind [hAB hz]

@[grind →]
lemma isSimple_left_of_isPrimitive (h : (A.append B).toPath.IsPrimitive) (hxp : x ≠ p) :
    A.IsSimple :=
  (isPrimitive_append_iff hxp).mp h |>.left

@[grind →]
lemma isSimple_right_of_isPrimitive (h : (A.append B).toPath.IsPrimitive) (hxp : x ≠ p) :
    B.IsSimple :=
  (isPrimitive_append_iff hxp).mp h |>.right.left

@[grind →]
lemma toSet_inter_subset_of_isPrimitive (h : (A.append B).toPath.IsPrimitive) (hxp : x ≠ p) :
    A.toSet ∩ B.toSet ⊆ ({x, p} : Set α) :=
  ((isPrimitive_append_iff hxp).mp h).right.right.trans inter_subset_left

end Append

private lemma symm_of_isPrimitive (h : P.toPath.IsPrimitive) :
    P.reverse.toPath.IsPrimitive := by
  rw [isPrimitive_iff] at h ⊢
  obtain ⟨hP, hlen⟩ | ⟨rfl, hloop⟩ := h
  · exact Or.inl ⟨isSimple_reverse.mpr hP, by simpa using hlen⟩
  · exact Or.inr ⟨rfl, by simpa using isSimpleLoop_reverse.mpr hloop⟩

lemma isPrimitive_reverse_iff : P.reverse.toPath.IsPrimitive ↔ P.toPath.IsPrimitive := by
  refine ⟨fun h ↦ ?_, symm_of_isPrimitive⟩
  have := symm_of_isPrimitive h
  rwa [reverse_reverse] at this

/-! ### Connected subsets and polygonal subarcs -/

/-- A connected subset of a primitive polygonal path that avoids its vertices lies in a
unique edge segment. -/
lemma existsUnique_edge_of_isConnected {X : Type*} [TopologicalSpace X] [AddCommGroup X]
    [Module ℝ X] [ContinuousSMul ℝ X] [ContinuousAdd X] {x y : X} (P : PolygonalPath x y)
    (hP : P.toPath.IsPrimitive) [T2Space P.toSet] {K : Set X} (hK : IsConnected K)
    (hsub : K ⊆ P.toSet) (havoid : ∀ z ∈ K, z ∉ P.vertices) :
    ∃! s, s ∈ P.edges ∧ K ⊆ segment ℝ s.1 s.2 := by
  let ι := {s // s ∈ P.edges}
  have : _root_.Finite ι := P.edges.finite_toSet.to_subtype
  have : ConnectedSpace K := isConnected_iff_connectedSpace.mp hK
  let U (i : ι) : Set K := Subtype.val ⁻¹' segment ℝ i.val.fst i.val.snd
  have huniq (z : K) : ∃! i : ι, z ∈ U i := by
    obtain ⟨s, hs, huniq⟩ := P.existsUnique_edge_of_isPrimitive hP (hsub z.prop) (havoid _ z.prop)
    exact ⟨⟨s, hs.1⟩, hs.2, fun j hj ↦ Subtype.ext (huniq j.val ⟨j.prop, hj⟩)⟩
  have hclosed (i : ι) : IsClosed (U i) := by
    have hcompact : IsCompact (segment ℝ i.val.fst i.val.snd : Set X) := by
      rw [← Path.range_segment]
      exact isCompact_range (Path.segment i.val.fst i.val.snd).continuous
    have hcompact' : IsCompact (P.toSet ↓∩ segment ℝ i.val.fst i.val.snd) :=
      IsInducing.subtypeVal.isCompact_preimage' hcompact (by
        simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using P.segment_subset_toSet i.prop)
    exact hcompact'.isClosed.preimage (continuous_inclusion hsub)
  obtain ⟨z, hz⟩ := hK.nonempty
  obtain ⟨i, hi, _⟩ := huniq ⟨z, hz⟩
  have hopen : IsOpen (U i) := by
    suffices U i = (⋃ j : {j // j ≠ i}, U j)ᶜ from
      this ▸ (isClosed_iUnion_of_finite fun j : {j // j ≠ i} ↦ hclosed j).isOpen_compl
    ext z
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    refine ⟨fun h j hj ↦ j.prop ((huniq z).unique hj h), fun h ↦ ?_⟩
    obtain ⟨j, hj, _⟩ := huniq z
    obtain rfl : j = i := by
      by_contra hji
      exact h ⟨j, hji⟩ hj
    simpa using hj
  have heq : U i = univ := IsClopen.eq_univ ⟨hclosed i, hopen⟩ ⟨⟨z, hz⟩, hi⟩
  refine ⟨i.1, ⟨i.2, fun z hz ↦ show (⟨z, hz⟩ : K) ∈ U i from heq ▸ mem_univ _⟩,
    fun j hj ↦  (P.existsUnique_edge_of_isPrimitive hP (hsub hz) (havoid z hz)).unique
    ⟨hj.1, hj.2 hz⟩ ⟨i.2, hi⟩⟩

/-- A polygonal path lying on an injective path with the same endpoints has a primitive
polygonal representative covering that entire path. -/
theorem _root_.Path.exists_primitive_polygonalPath_of_toSet_subset {W : Type*} [TopologicalSpace W]
    [AddCommGroup W] [Module ℝ W] [ContinuousSMul ℝ W] [ContinuousAdd W] {x y : W} {γ : Path x y}
    (hinj : Injective γ) [T2Space ↥(range γ)] (P : PolygonalPath x y) (hP : P.toSet ⊆ range γ) :
    ∃ Q : PolygonalPath x y, Q.toPath.IsPrimitive ∧ Q.toSet = range γ := by
  obtain ⟨Q, hQ, hQP⟩ := P.exists_isSimple_toSet_subset
  have hxy : x ≠ y := by
    rintro rfl
    exact zero_ne_one <| hinj <| γ.source.trans γ.target.symm
  refine ⟨Q, hQ.isPrimitive (Q.length_pos_of_ne hxy), ?_⟩
  rw [toSet_eq_range_toPath]
  refine Path.range_eq_of_subset_injective hinj ?_
  rw [← toSet_eq_range_toPath]
  exact hQP.trans hP

/-- An injective path contained in a primitive polygonal path has a polygonal representative
with exactly the same range. -/
lemma exists_polygonalPath_of_injective {X : Type*} [TopologicalSpace X] [AddCommGroup X]
    [Module ℝ X] [ContinuousSMul ℝ X] [ContinuousAdd X] {a b x y : X} (P : PolygonalPath a b)
    (hP : P.toPath.IsPrimitive) [T2Space P.toSet] (γ : Path x y) (hinj : Injective γ)
    (hsub : range γ ⊆ P.toSet) : ∃ Q : PolygonalPath x y, Q.toSet = range γ := by
  have hfin : (γ ⁻¹' {z | z ∈ P.vertices}).Finite :=
    P.vertices.finite_toSet.preimage hinj.injOn
  refine γ.exists_polygonalPath_of_finite_cuts hfin fun s t hst hcut ↦ ?_
  have havoid : ∀ z ∈ γ '' Ioo s t, z ∉ P.vertices := by
    rintro z ⟨u, hu, rfl⟩ huz
    exact hcut u hu huz
  obtain ⟨v, ⟨hv, hseg⟩, -⟩ := P.existsUnique_edge_of_isConnected hP
    ((isConnected_Ioo hst).image γ γ.continuous.continuousOn)
    (fun z hz ↦ hsub (image_subset_range _ _ hz)) havoid
  have hcompact : IsCompact (segment ℝ v.fst v.snd : Set X) := by
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment v.fst v.snd).continuous
  have hclosed : IsClosed (P.toSet ↓∩ segment ℝ v.fst v.snd) :=
    (IsInducing.subtypeVal.isCompact_preimage' hcompact (by
      simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using
        P.segment_subset_toSet hv)).isClosed
  have hpreclosed : IsClosed (γ ⁻¹' segment ℝ v.fst v.snd) :=
    hclosed.preimage (γ.continuous.subtype_mk (fun u ↦ hsub (mem_range_self u)))
  have hsubpath : range (γ.subpath s t) ⊆ segment ℝ v.fst v.snd := by
    rw [γ.range_subpath_of_le _ _ hst.le]
    rintro z ⟨u, hu, rfl⟩
    refine hpreclosed.closure_subset <| closure_mono
      (show Ioo s t ⊆ γ ⁻¹' segment ℝ _ _ from fun u hu ↦ hseg (mem_image_of_mem _ hu)) ?_
    rwa [closure_Ioo hst.ne]
  have : T2Space ↥(segment ℝ v.fst v.snd) :=
    (IsEmbedding.inclusion (P.segment_subset_toSet hv)).t2Space
  exact ⟨PolygonalPath.direct (γ s) (γ t), (PolygonalPath.toSet_direct _ _).trans
    (Path.range_eq_segment_of_subset (γ.injective_subpath hinj hst.ne) hsubpath).symm⟩

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
