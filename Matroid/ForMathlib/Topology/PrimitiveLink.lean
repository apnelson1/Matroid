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

open Set Function unitInterval Path
open scoped Sym2

variable {X : Type*} [TopologicalSpace X] {x y z : X} {L M : Set X}

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

lemma diff_endpoints_nonempty (h : IsPrimitiveLink L x y) : (L \ {x, y}).Nonempty := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact hγ.isPathConnected_range_diff_endpoints.nonempty

lemma nontrivial (h : IsPrimitiveLink L x y) : L.Nontrivial := by
  obtain ⟨z, hzL, hz⟩ := h.diff_endpoints_nonempty
  exact ⟨x, h.left_mem, z, hzL, fun hxz ↦ hz (.inl hxz.symm)⟩

lemma infinite (h : IsPrimitiveLink L x y) : L.Infinite := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact ((Ioo_infinite (show (0 : I) < 1 from zero_lt_one)).image hγ.injOn_Ioo).mono
    (image_subset_range ..)

lemma isCompact (h : IsPrimitiveLink L x y) : IsCompact L := by
  obtain ⟨γ, -, rfl⟩ := h
  exact isCompact_range γ.continuous

lemma isClosed [T2Space X] (h : IsPrimitiveLink L x y) : IsClosed L :=
  h.isCompact.isClosed

lemma isPathConnected (h : IsPrimitiveLink L x y) : IsPathConnected L := by
  obtain ⟨γ, -, rfl⟩ := h
  exact γ.range_isPathConnected

lemma isConnected (h : IsPrimitiveLink L x y) : IsConnected L :=
  h.isPathConnected.isConnected

lemma isPathConnected_diff_endpoints (h : IsPrimitiveLink L x y) :
    IsPathConnected (L \ {x, y}) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact hγ.isPathConnected_range_diff_endpoints

lemma isConnected_diff_endpoints (h : IsPrimitiveLink L x y) : IsConnected (L \ {x, y}) :=
  h.isPathConnected_diff_endpoints.isConnected

/-- The endpoints of a primitive link are limits of its other points. -/
lemma subset_closure_diff_endpoints (h : IsPrimitiveLink L x y) : L ⊆ closure (L \ {x, y}) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  rw [hγ.range_diff_endpoints]
  exact γ.range_subset_closure_interior

lemma closure_diff_endpoints [T2Space X] (h : IsPrimitiveLink L x y) :
    closure (L \ {x, y}) = L :=
  (closure_minimal sdiff_subset h.isClosed).antisymm h.subset_closure_diff_endpoints

lemma image {Y : Type*} [TopologicalSpace Y] {f : X → Y} (h : IsPrimitiveLink L x y)
    (hf : ContinuousOn f L) (hinj : InjOn f L) : IsPrimitiveLink (f '' L) (f x) (f y) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  refine ⟨γ.map' hf, hγ.map hf hinj, ?_⟩
  change range (f ∘ γ) = f '' range γ
  exact range_comp f γ

lemma isArc (h : IsPrimitiveLink L x y) (hxy : x ≠ y) : IsArc L := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact range_path_isArc γ ((isPrimitive_iff_injective hxy).mp hγ)

lemma ends_isArc [T2Space X] (h : IsPrimitiveLink L x y) (hxy : x ≠ y) :
    IsArc.ends L (h.isArc hxy) = s(x, y) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact IsArc.ends_eq_path_source_target γ (hγ.injective hxy) rfl _

lemma of_isArc (hL : IsArc L) (hends : hL.ends = s(x, y)) : IsPrimitiveLink L x y := by
  obtain ⟨γ, hinj, hrange⟩ := hL.exists_path_between hends
  exact ⟨γ, .of_injective hinj, hrange⟩

end IsPrimitiveLink

lemma isPrimitiveLink_comm : IsPrimitiveLink L x y ↔ IsPrimitiveLink L y x :=
  ⟨.symm, .symm⟩

lemma isPrimitiveLink_iff_exists_injective (hxy : x ≠ y) :
    IsPrimitiveLink L x y ↔ ∃ γ : Path x y, Injective γ ∧ range γ = L := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, (isPrimitive_iff_injective hxy).mp hγ, rfl⟩
  · rintro ⟨γ, hinj, rfl⟩
    exact .of_injective hinj

lemma isPrimitiveLink_iff_isArc [T2Space X] (hxy : x ≠ y) :
    IsPrimitiveLink L x y ↔ ∃ hL : IsArc L, hL.ends = s(x, y) :=
  ⟨fun h ↦ ⟨h.isArc hxy, h.ends_isArc hxy⟩, fun ⟨hL, hends⟩ ↦ .of_isArc hL hends⟩

lemma isPrimitiveLink_iff_exists_isSimpleLoop :
    IsPrimitiveLink L x x ↔ ∃ γ : Path x x, γ.IsSimpleLoop ∧ range γ = L := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, isPrimitive_iff_isSimpleLoop.mp hγ, rfl⟩
  · rintro ⟨γ, hloop, rfl⟩
    exact .of_isSimpleLoop hloop

lemma isPrimitiveLink_iff_isCircuit : IsPrimitiveLink L x x ↔ IsCircuit L ∧ x ∈ L := by
  refine ⟨fun h ↦ ?_, fun ⟨hC, hx⟩ ↦ ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := isPrimitiveLink_iff_exists_isSimpleLoop.mp h
    exact ⟨isCircuit_iff_range_path_injOn_Ico.2 ⟨x, γ, hγ, rfl⟩, γ.source_mem_range⟩
  · obtain ⟨γ, hγ, rfl⟩ := hC.exists_path_injOn_Ico hx
    exact .of_isSimpleLoop hγ

/-! ### Joining links -/

theorem IsPrimitiveLink.union (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M y z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hinter : L ∩ M ⊆ {y}) : IsPrimitiveLink (L ∪ M) x z := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  refine ⟨P.trans Q, IsPrimitive.of_injective ?_, P.trans_range Q⟩
  rw [trans_injective_iff]
  exact ⟨hP.injective hxy, hQ.injective hyz,
    disjoint_left.mpr fun a ha haQ ↦ ha.right (hinter ⟨ha.1, haQ⟩)⟩

theorem IsPrimitiveLink.union_loop (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M y x)
    (hxy : x ≠ y) (hinter : L ∩ M ⊆ {x, y}) : IsPrimitiveLink (L ∪ M) x x := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  refine ⟨P.trans Q, IsSimpleLoop.isPrimitive ?_, P.trans_range Q⟩
  rw [IsSimpleLoop, trans_injOn_ico_iff]
  refine ⟨hP.injective hxy, hQ.injective hxy.symm, disjoint_left.mpr fun a ha haQ ↦ ?_⟩
  grind [show a ∈ ({x, y} : Set X) from hinter ⟨ha.left, haQ.left⟩]

/-- Join two arcs meeting only at their common endpoints. The union is an arc or a loop
according to whether the outer endpoints differ. -/
theorem IsPrimitiveLink.union_of_inter_subset (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M y z) (hxy : x ≠ y) (hyz : y ≠ z)
    (hinter : L ∩ M ⊆ ({x, y} : Set X) ∩ {y, z}) : IsPrimitiveLink (L ∪ M) x z := by
  obtain rfl | hxz := eq_or_ne x z
  · exact hL.union_loop hM hxy (hinter.trans inter_subset_left)
  exact hL.union hM hxy hyz fun w hw ↦ by grind [hinter hw]

/-! ### Splitting at a point -/

namespace IsPrimitiveLink

variable {m : X}

/-- The part of `L` from `x` to `m` along a fixed primitive parametrization of `L`.
For an arc with Hausdorff carrier this is the unique sublink from `x` to `m`
(`IsPrimitiveLink.eq_splitLeft`). For a loop, `splitLeft` and `splitRight` are the two arcs
between `x` and `m`; which of them is `splitLeft` depends on the parametrization. -/
noncomputable def splitLeft (hL : IsPrimitiveLink L x y) (m : X) : Set X :=
  range (hL.choose.subpath 0 (invFun hL.choose m))

/-- The part of `L` from `m` to `y` along the parametrization defining `splitLeft`. -/
noncomputable def splitRight (hL : IsPrimitiveLink L x y) (m : X) : Set X :=
  range (hL.choose.subpath (invFun hL.choose m) 1)

private lemma choose_invFun (hL : IsPrimitiveLink L x y) (hm : m ∈ L) :
    hL.choose (invFun hL.choose m) = m :=
  invFun_eq (hL.choose_spec.2.symm ▸ hm : m ∈ range hL.choose)

lemma left_mem_splitLeft (hL : IsPrimitiveLink L x y) (m : X) : x ∈ hL.splitLeft m := by
  rw [splitLeft]
  exact ⟨0, (hL.choose.subpath 0 _).source.trans hL.choose.source⟩

lemma right_mem_splitRight (hL : IsPrimitiveLink L x y) (m : X) : y ∈ hL.splitRight m := by
  rw [splitRight]
  exact ⟨1, (hL.choose.subpath _ 1).target.trans hL.choose.target⟩

lemma mem_splitLeft (hL : IsPrimitiveLink L x y) (hm : m ∈ L) : m ∈ hL.splitLeft m := by
  rw [splitLeft]
  exact ⟨1, (hL.choose.subpath 0 _).target.trans (hL.choose_invFun hm)⟩

lemma mem_splitRight (hL : IsPrimitiveLink L x y) (hm : m ∈ L) : m ∈ hL.splitRight m := by
  rw [splitRight]
  exact ⟨0, (hL.choose.subpath _ 1).source.trans (hL.choose_invFun hm)⟩

@[simp]
lemma splitLeft_union_splitRight (hL : IsPrimitiveLink L x y) (m : X) :
    hL.splitLeft m ∪ hL.splitRight m = L := by
  rw [splitLeft, splitRight, range_subpath_of_le _ _ _ nonneg', range_subpath_of_le _ _ _ le_one',
    ← image_union, Icc_union_Icc_eq_Icc nonneg' le_one', unitInterval.Icc_eq_univ, image_univ,
    hL.choose_spec.2]

@[simp]
lemma splitRight_union_splitLeft (hL : IsPrimitiveLink L x y) (m : X) :
    hL.splitRight m ∪ hL.splitLeft m = L := by
  rw [union_comm, splitLeft_union_splitRight]

lemma splitLeft_subset (hL : IsPrimitiveLink L x y) (m : X) : hL.splitLeft m ⊆ L :=
  subset_union_left.trans (hL.splitLeft_union_splitRight m).subset

lemma splitRight_subset (hL : IsPrimitiveLink L x y) (m : X) : hL.splitRight m ⊆ L :=
  subset_union_right.trans (hL.splitLeft_union_splitRight m).subset

/-- The two pieces meet at `m` and, for a loop, at the basepoint. -/
lemma splitLeft_inter_splitRight (hL : IsPrimitiveLink L x y) (hm : m ∈ L) :
    hL.splitLeft m ∩ hL.splitRight m = {m} ∪ {x} ∩ {y} := by
  rw [splitLeft, splitRight, hL.choose_spec.1.subpath_range_inter_subpath_range,
    hL.choose_invFun hm]

lemma isPrimitiveLink_splitLeft (hL : IsPrimitiveLink L x y) (hm : m ∈ L) (hmx : m ≠ x) :
    IsPrimitiveLink (hL.splitLeft m) x m := by
  have ht := hL.choose_invFun hm
  refine ⟨(hL.choose.subpath 0 _).cast hL.choose.source.symm ht.symm,
    fun _ _ h ↦ hL.choose_spec.1.subpath (fun h0 ↦ hmx ?_) h, rfl⟩
  rw [← ht, ← h0, Path.source]

lemma isPrimitiveLink_splitRight (hL : IsPrimitiveLink L x y) (hm : m ∈ L) (hmy : m ≠ y) :
    IsPrimitiveLink (hL.splitRight m) m y := by
  have ht := hL.choose_invFun hm
  refine ⟨(hL.choose.subpath _ 1).cast ht.symm hL.choose.target.symm,
    fun _ _ h ↦ hL.choose_spec.1.subpath (fun h1 ↦ hmy ?_) h, rfl⟩
  rw [← ht, h1, Path.target]

/-! ### Sublinks of an arc -/

private lemma eq_of_subset_of_ne [T2Space M] {A B : Set X} {a b u v : X}
    (hM : IsPrimitiveLink M a b) (hab : a ≠ b) (hA : IsPrimitiveLink A u v)
    (hB : IsPrimitiveLink B u v) (huv : u ≠ v) (hAM : A ⊆ M) (hBM : B ⊆ M) : A = B := by
  obtain ⟨γ, hγ, rfl⟩ := hM
  obtain ⟨s, rfl⟩ := hAM hA.left_mem
  obtain ⟨t, rfl⟩ := hAM hA.right_mem
  obtain ⟨P, hP, rfl⟩ := hA
  obtain ⟨Q, hQ, rfl⟩ := hB
  rw [range_eq_image_uIcc_of_subset_injective (hγ.injective hab) (hP.injective huv) hAM,
    range_eq_image_uIcc_of_subset_injective (hγ.injective hab) (hQ.injective huv) hBM]

/-- A primitive link contained in an arc with Hausdorff carrier has distinct endpoints. -/
lemma endpoints_ne_of_subset [T2Space M] {a b : X} (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M a b) (hab : a ≠ b) (hLM : L ⊆ M) : x ≠ y := by
  rintro rfl
  obtain ⟨m, hmL, hm⟩ := hL.diff_endpoints_nonempty
  have hmx : m ≠ x := fun h ↦ hm (Or.inl h)
  have hA := hL.isPrimitiveLink_splitLeft hmL hmx
  have heq := eq_of_subset_of_ne hM hab hA (hL.isPrimitiveLink_splitRight hmL hmx).symm
    hmx.symm ((hL.splitLeft_subset m).trans hLM) ((hL.splitRight_subset m).trans hLM)
  obtain ⟨z, hzA, hz⟩ := hA.diff_endpoints_nonempty
  have hzAB : z ∈ hL.splitLeft m ∩ hL.splitRight m := ⟨hzA, heq ▸ hzA⟩
  simp only [hL.splitLeft_inter_splitRight hmL, inter_self, mem_union, mem_singleton_iff]
    at hzAB
  exact hz (hzAB.elim Or.inr Or.inl)

/-- In an arc with Hausdorff carrier, a sublink is determined by its endpoints. -/
lemma eq_of_subset [T2Space M] {A B : Set X} {a b u v : X} (hM : IsPrimitiveLink M a b)
    (hab : a ≠ b) (hA : IsPrimitiveLink A u v) (hB : IsPrimitiveLink B u v) (hAM : A ⊆ M)
    (hBM : B ⊆ M) : A = B :=
  eq_of_subset_of_ne hM hab hA hB (hA.endpoints_ne_of_subset hM hab hAM) hAM hBM

/-- In an arc with Hausdorff carrier, every sublink from `x` to `m` is `splitLeft`. -/
lemma eq_splitLeft [T2Space L] (hL : IsPrimitiveLink L x y) (hxy : x ≠ y) {A : Set X}
    (hA : IsPrimitiveLink A x m) (hAL : A ⊆ L) : A = hL.splitLeft m :=
  hL.eq_of_subset hxy hA (hL.isPrimitiveLink_splitLeft (hAL hA.right_mem)
    (hA.endpoints_ne_of_subset hL hxy hAL).symm) hAL (hL.splitLeft_subset m)

/-- In an arc with Hausdorff carrier, every sublink from `m` to `y` is `splitRight`. -/
lemma eq_splitRight [T2Space L] (hL : IsPrimitiveLink L x y) (hxy : x ≠ y) {B : Set X}
    (hB : IsPrimitiveLink B m y) (hBL : B ⊆ L) : B = hL.splitRight m :=
  hL.eq_of_subset hxy hB (hL.isPrimitiveLink_splitRight (hBL hB.left_mem)
    (hB.endpoints_ne_of_subset hL hxy hBL)) hBL (hL.splitRight_subset m)

end IsPrimitiveLink

/-! ### Geometric decomposition of two links -/

/-- If both endpoints of an arc `L` lie on a closed primitive link `M`, every point of `L \ M`
lies in a sublink of `L` meeting `M` exactly at its endpoints. A sublink of `M` joins those
endpoints in the reverse direction. The two sublinks therefore meet exactly at their distinct
endpoints. -/
theorem IsPrimitiveLink.exists_sublinks_inter_eq_pair {a b c : X}
    (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M a b) (hMc : IsClosed M) (hxy : x ≠ y)
    (hx : x ∈ M) (hy : y ∈ M) (hc : c ∈ L \ M) :
    ∃ u v, u ≠ v ∧ ∃ A ⊆ L, ∃ B ⊆ M,
      IsPrimitiveLink A u v ∧ IsPrimitiveLink B v u ∧ c ∈ A \ {u, v} ∧
      A ∩ M = {u, v} ∧ A ∩ B = {u, v} := by
  obtain ⟨P, hP, rfl⟩ := isPrimitiveLink_iff_exists_injective hxy |>.mp hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  obtain ⟨u, v, s, t, huv, hs, ht, hcP, hPu, hQt, hinter⟩ :=
    Path.exists_subpaths_inter_eq_pair hP hQ (hMc.preimage P.continuous) hx hy hc
  have hB : IsPrimitiveLink (range (Q.subpath s t)) (P v) (P u) := by
    rw [hs, ht]
    exact (IsPrimitiveLink.of_injective hQt).symm
  refine ⟨P u, P v, hP.ne huv.1.ne, range (P.subpath u v), ?_,
    range (Q.subpath s t), ?_, .of_injective hPu, hB, ⟨?_, ?_⟩,
    P.range_subpath_inter_of_mem_excursions huv, hinter⟩
  · rw [range_subpath]
    exact image_subset_range _ _
  · rw [range_subpath]
    exact image_subset_range _ _
  · rw [P.range_subpath_of_le u v huv.1.le]
    exact image_mono Ioo_subset_Icc_self hcP
  rintro (rfl | rfl)
  · exact hc.2 huv.2.1
  exact hc.2 huv.2.2.1

/-- If both endpoints of a primitive link `L` lie on a closed primitive link `M`, each point of
`L \ M` lies on a circuit in `L ∪ M`. For an arc `L`, the circuit is the union of the sublinks
from `IsPrimitiveLink.exists_sublinks_inter_eq_pair`; a loop `L` is itself the circuit. -/
theorem IsPrimitiveLink.exists_isCircuit_of_mem_diff {a b c : X}
    (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M a b) (hMc : IsClosed M)
    (hx : x ∈ M) (hy : y ∈ M) (hc : c ∈ L \ M) :
    ∃ C ⊆ L ∪ M, IsCircuit C ∧ c ∈ C := by
  obtain rfl | hxy := eq_or_ne x y
  · exact ⟨L, subset_union_left, (isPrimitiveLink_iff_isCircuit.mp hL).1, hc.1⟩
  obtain ⟨u, v, huv, A, hAL, B, hBM, hA, hB, hcA, -, hAB⟩ :=
    hL.exists_sublinks_inter_eq_pair hM hMc hxy hx hy hc
  exact ⟨A ∪ B, union_subset_union hAL hBM,
    (isPrimitiveLink_iff_isCircuit.mp (hA.union_loop hB huv hAB.subset)).1, Or.inl hcA.1⟩

/-- Distinct closed primitive links with the same endpoints contain a circuit in their union. -/
theorem IsPrimitiveLink.exists_isCircuit_of_ne (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M x y) (hLc : IsClosed L) (hMc : IsClosed M) (hne : L ≠ M) :
    ∃ C ⊆ L ∪ M, IsCircuit C := by
  by_cases hLM : L ⊆ M
  · obtain ⟨c, hcM, hcL⟩ := not_subset.mp fun hML ↦ hne (hLM.antisymm hML)
    obtain ⟨C, hC, hCc, -⟩ :=
      hM.exists_isCircuit_of_mem_diff hL hLc hL.left_mem hL.right_mem ⟨hcM, hcL⟩
    exact ⟨C, union_comm M L ▸ hC, hCc⟩
  obtain ⟨c, hcL, hcM⟩ := not_subset.mp hLM
  obtain ⟨C, hC, hCc, -⟩ :=
    hL.exists_isCircuit_of_mem_diff hM hMc hM.left_mem hM.right_mem ⟨hcL, hcM⟩
  exact ⟨C, hC, hCc⟩

/-! ### Segments -/

variable [AddCommGroup X] [Module ℝ X] [ContinuousAdd X] [ContinuousSMul ℝ X]

/-- A nondegenerate segment is a primitive link between its endpoints. -/
lemma isPrimitiveLink_segment (hxy : x ≠ y) : IsPrimitiveLink (segment ℝ x y) x y :=
  ⟨Path.segment x y, .of_injective (segment_injective_of_ne hxy), range_segment x y⟩

variable {a b : X} [T2Space ↥(segment ℝ a b)]

omit [ContinuousAdd X] [ContinuousSMul ℝ X] in
private lemma IsPrimitiveLink.ne_of_subset_segment (hL : IsPrimitiveLink L x y)
    (hsub : L ⊆ segment ℝ a b) : a ≠ b := by
  rintro rfl
  exact hL.nontrivial.not_subset_singleton (segment_same ℝ a ▸ hsub)

/-- A primitive link contained in a Hausdorff segment cannot be a loop. -/
lemma IsPrimitiveLink.endpoints_ne_of_subset_segment (hL : IsPrimitiveLink L x y)
    (hsub : L ⊆ segment ℝ a b) : x ≠ y :=
  have hab := hL.ne_of_subset_segment hsub
  hL.endpoints_ne_of_subset (isPrimitiveLink_segment hab) hab hsub

/-- A primitive link contained in a Hausdorff segment fills the segment between its endpoints. -/
lemma IsPrimitiveLink.eq_segment_of_subset (hL : IsPrimitiveLink L x y)
    (hsub : L ⊆ segment ℝ a b) : L = segment ℝ x y :=
  have hab := hL.ne_of_subset_segment hsub
  (isPrimitiveLink_segment hab).eq_of_subset hab hL
    (isPrimitiveLink_segment (hL.endpoints_ne_of_subset_segment hsub)) hsub
    ((convex_segment a b).segment_subset (hsub hL.left_mem) (hsub hL.right_mem))
