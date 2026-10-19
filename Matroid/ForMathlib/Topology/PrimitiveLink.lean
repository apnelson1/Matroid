module

public import Matroid.ForMathlib.Topology.PrimitivePath
public import Matroid.ForMathlib.Topology.Circuit

/-!
# Primitive links

A **primitive link** is the image of a `Path.IsPrimitive` with specified endpoints.
In a Hausdorff target, it is an embedded arc when the endpoints are distinct and an embedded
loop when they coincide.
-/

@[expose] public section

open Set Function unitInterval
open scoped Sym2

variable {X : Type*} [TopologicalSpace X] {x y : X} {L : Set X}

/-- A set `L` is a primitive link from `x` to `y` if it is the image of a primitive path with
those endpoints. -/
def IsPrimitiveLink (L : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, γ.IsPrimitive ∧ range γ = L

lemma Path.IsPrimitive.isPrimitiveLink {γ : Path x y} (h : γ.IsPrimitive) :
    IsPrimitiveLink (range γ) x y :=
  ⟨γ, h, rfl⟩

lemma IsPrimitiveLink.of_injective {γ : Path x y} (h : Injective γ) :
    IsPrimitiveLink (range γ) x y :=
  (Path.IsPrimitive.of_injective h).isPrimitiveLink

lemma IsPrimitiveLink.of_isSimpleLoop {γ : Path x x} (h : γ.IsSimpleLoop) :
    IsPrimitiveLink (range γ) x x :=
  (Path.isPrimitive_iff_isSimpleLoop.mpr h).isPrimitiveLink

namespace IsPrimitiveLink

@[symm]
lemma symm (h : IsPrimitiveLink L x y) : IsPrimitiveLink L y x := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact ⟨γ.symm, hγ.symm, γ.symm_range⟩

lemma left_mem (h : IsPrimitiveLink L x y) : x ∈ L := by
  obtain ⟨γ, -, rfl⟩ := h
  exact γ.source_mem_range

lemma right_mem (h : IsPrimitiveLink L x y) : y ∈ L :=
  h.symm.left_mem

lemma nonempty (h : IsPrimitiveLink L x y) : L.Nonempty :=
  ⟨x, h.left_mem⟩

lemma isCompact (h : IsPrimitiveLink L x y) : IsCompact L := by
  obtain ⟨γ, -, rfl⟩ := h
  exact isCompact_range γ.continuous

lemma isPathConnected (h : IsPrimitiveLink L x y) : IsPathConnected L := by
  obtain ⟨γ, -, rfl⟩ := h
  exact γ.range_isPathConnected

lemma isConnected (h : IsPrimitiveLink L x y) : IsConnected L :=
  h.isPathConnected.isConnected

lemma isArc (h : IsPrimitiveLink L x y) (hxy : x ≠ y) : IsArc L := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact range_path_isArc γ ((Path.isPrimitive_iff_injective hxy).mp hγ)

lemma image {Y : Type*} [TopologicalSpace Y] {f : X → Y} (h : IsPrimitiveLink L x y)
    (hf : ContinuousOn f L) (hinj : InjOn f L) : IsPrimitiveLink (f '' L) (f x) (f y) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  refine ⟨γ.map' hf, hγ.map hf hinj, ?_⟩
  change range (f ∘ γ) = f '' range γ
  exact range_comp f γ

lemma of_isArc [T2Space X] (hL : IsArc L) (hends : hL.ends = s(x, y)) :
    IsPrimitiveLink L x y := by
  obtain ⟨γ, hinj, hrange⟩ := hL.exists_path_between hends
  exact ⟨γ, .of_injective hinj, hrange⟩

end IsPrimitiveLink

lemma isPrimitiveLink_iff_exists_injective (hxy : x ≠ y) :
    IsPrimitiveLink L x y ↔ ∃ γ : Path x y, Injective γ ∧ range γ = L := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, (Path.isPrimitive_iff_injective hxy).mp hγ, rfl⟩
  · rintro ⟨γ, hinj, rfl⟩
    exact .of_injective hinj

lemma isPrimitiveLink_iff_exists_isSimpleLoop :
    IsPrimitiveLink L x x ↔ ∃ γ : Path x x, γ.IsSimpleLoop ∧ range γ = L := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, Path.isPrimitive_iff_isSimpleLoop.mp hγ, rfl⟩
  · rintro ⟨γ, hloop, rfl⟩
    exact .of_isSimpleLoop hloop

lemma isPrimitiveLink_iff_isCircuit : IsPrimitiveLink L x x ↔ IsCircuit L ∧ x ∈ L := by
  refine ⟨fun h ↦ ?_, fun ⟨hC, hx⟩ ↦ ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := isPrimitiveLink_iff_exists_isSimpleLoop.mp h
    exact ⟨isCircuit_iff_range_path_injOn_Ico.2 ⟨x, γ, hγ, rfl⟩, γ.source_mem_range⟩
  · obtain ⟨γ, hγ, rfl⟩ := hC.exists_path_injOn_Ico hx
    exact .of_isSimpleLoop hγ

/-- The endpoints of a primitive link belong to every closed set containing its relative interior,
because they are limits of interior points. -/
lemma IsPrimitiveLink.endpoints_mem_of_diff_subset (h : IsPrimitiveLink L x y) {S : Set X}
    (hS : IsClosed S) (hsub : L \ {x, y} ⊆ S) : x ∈ S ∧ y ∈ S := by
  obtain ⟨γ, hγ, rfl⟩ := h
  rw [hγ.range_diff_endpoints] at hsub
  have hmem : ∀ t : I, γ t ∈ S :=
    fun t ↦ hS.closure_subset (closure_mono hsub (γ.range_subset_closure_interior ⟨t, rfl⟩))
  exact ⟨by simpa using hmem 0, by simpa using hmem 1⟩

variable {L M : Set X} {x y z : X}

theorem IsPrimitiveLink.union (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M y z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hinter : L ∩ M = {y}) : IsPrimitiveLink (L ∪ M) x z := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  refine ⟨P.trans Q, Path.IsPrimitive.of_injective ?_, P.trans_range Q⟩
  rw [Path.trans_injective_iff]
  exact ⟨hP.injective hxy, hQ.injective hyz,
    disjoint_left.mpr fun a ha haQ ↦ ha.right (hinter ▸ ⟨ha.1, haQ⟩)⟩

theorem IsPrimitiveLink.union_loop (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M y x)
    (hxy : x ≠ y) (hinter : L ∩ M = {x, y}) : IsPrimitiveLink (L ∪ M) x x := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  refine ⟨P.trans Q, Path.IsSimpleLoop.isPrimitive ?_, P.trans_range Q⟩
  rw [Path.IsSimpleLoop, Path.trans_injOn_ico_iff]
  refine ⟨hP.injective hxy, hQ.injective hxy.symm, disjoint_left.mpr fun a ha haQ ↦ ?_⟩
  grind [show a ∈ ({x, y} : Set X) from hinter ▸ ⟨ha.left, haQ.left⟩]

/-- Join two arcs meeting only at their common endpoints. The union is an arc or a loop
according to whether the outer endpoints differ. -/
theorem IsPrimitiveLink.union_of_inter_subset (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M y z) (hxy : x ≠ y) (hyz : y ≠ z)
    (hinter : L ∩ M ⊆ ({x, y} : Set X) ∩ {y, z}) : IsPrimitiveLink (L ∪ M) x z := by
  obtain rfl | hxz := eq_or_ne x z
  · refine hL.union_loop hM hxy <| (hinter.trans inter_subset_left).antisymm ?_
    rintro w (rfl | rfl)
    · exact ⟨hL.left_mem, hM.right_mem⟩
    exact ⟨hL.right_mem, hM.left_mem⟩
  refine hL.union hM hxy hyz <| Subset.antisymm (fun w hw ↦ by grind) ?_
  rintro w rfl
  exact ⟨hL.right_mem, hM.left_mem⟩

/-- Split a primitive link at an interior point into two arcs. For a loop the arcs also
meet at the original basepoint. -/
theorem IsPrimitiveLink.exists_split (hL : IsPrimitiveLink L x y) :
    ∃ m ∈ L \ {x, y}, ∃ A B : Set X, IsPrimitiveLink A x m ∧ IsPrimitiveLink B m y ∧
      A ∪ B = L ∧ A ∩ B = {m} ∪ ({x} ∩ {y}) := by
  obtain ⟨γ, hγ, rfl⟩ := hL
  refine ⟨γ half, ⟨mem_range_self _, ?_⟩, range γ.firstHalf, range γ.secondHalf,
    .of_injective hγ.injective_firstHalf, .of_injective hγ.injective_secondHalf,
    γ.firstHalf_range_union_secondHalf_range, hγ.firstHalf_range_inter_secondHalf_range⟩
  simpa only [mem_insert_iff, mem_singleton_iff, not_or] using
    And.intro hγ.half_ne_source hγ.half_ne_target
