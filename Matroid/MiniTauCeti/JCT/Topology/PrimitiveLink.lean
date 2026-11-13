module

public import Matroid.MiniTauCeti.JCT.Topology.PrimitivePath
public import Matroid.MiniTauCeti.JCT.Topology.Arc
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Parametrization

/-!
# Primitive links

A **primitive link** is the image of a `Path.IsPrimitive` with specified endpoints.
In a Hausdorff target, it is an embedded arc when the endpoints are distinct and an embedded
loop when they coincide.
-/

@[expose] public section

open Set Function unitInterval Path
open scoped Sym2

variable {X Y : Type*} [TopologicalSpace X] {x y z : X} {L M : Set X}

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

lemma closure_diff_endpoints [T2Space X] (h : IsPrimitiveLink L x y) : closure (L \ {x, y}) = L :=
  (closure_minimal sdiff_subset h.isClosed).antisymm h.subset_closure_diff_endpoints

lemma image [TopologicalSpace Y] {f : X → Y} (h : IsPrimitiveLink L x y)
    (hf : ContinuousOn f L) (hinj : InjOn f L) : IsPrimitiveLink (f '' L) (f x) (f y) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  refine ⟨γ.map' hf, hγ.map hf hinj, ?_⟩
  change range (f ∘ γ) = f '' range γ
  exact range_comp f γ

/-- A primitive link remains a primitive link in any subspace containing it. -/
lemma restrictSubtype {U : Set X} (hL : IsPrimitiveLink L x y) (hLU : L ⊆ U) :
    IsPrimitiveLink (Subtype.val ⁻¹' L : Set U) ⟨x, hLU hL.left_mem⟩ ⟨y, hLU hL.right_mem⟩ := by
  obtain ⟨P, hP, rfl⟩ := hL
  exact ⟨P.codRestrict hLU, (isPrimitive_codRestrict_iff hLU).mpr hP, P.range_codRestrict hLU⟩

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

section Recognition

open Topology Set.Notation

variable {S Z e : Set X} {a b : X}

/-- A relatively open primitive-link interior is a component of the vertex complement. -/
theorem connectedComponentIn_sdiff_eq [T2Space S] (hl : IsPrimitiveLink e a b) (heS : e ⊆ S)
    (hv : e ∩ Z = {a, b}) (ho : IsOpen (S ↓∩ (e \ Z))) (hx : x ∈ e \ Z) :
    connectedComponentIn (S \ Z) x = e \ Z := by
  have hc : IsClosed (S ↓∩ e) :=
    (IsInducing.subtypeVal.isCompact_preimage' hl.isCompact
      (by simpa only [Subtype.range_coe] using heS)).isClosed
  have hcl : IsClopen ((S \ Z) ↓∩ (e \ Z)) := by
    refine ⟨?_, ho.preimage (continuous_inclusion sdiff_subset)⟩
    convert hc.preimage (continuous_inclusion sdiff_subset) using 1
    ext y
    exact and_iff_left y.2.2
  have hconn : IsPreconnected (e \ Z) := by
    rw [← sdiff_self_inter, hv]
    exact hl.isConnected_diff_endpoints.isPreconnected
  refine subset_antisymm ?_ (hconn.subset_connectedComponentIn hx (sdiff_subset_sdiff_left heS))
  have hxS : x ∈ S \ Z := ⟨heS hx.1, hx.2⟩
  rw [connectedComponentIn_eq_image hxS]
  rintro _ ⟨y, hy, rfl⟩
  exact hcl.connectedComponent_subset hx hy

/-- Closing a primitive link away from its boundary recovers the link inside its carrier. -/
theorem inter_closure_sdiff_eq [T2Space S] (hl : IsPrimitiveLink e a b) (heS : e ⊆ S)
    (hv : e ∩ Z = {a, b}) : S ∩ closure (e \ Z) = e := by
  have hc : IsClosed (S ↓∩ e) :=
    (IsInducing.subtypeVal.isCompact_preimage' hl.isCompact
      (by simpa only [Subtype.range_coe] using heS)).isClosed
  rw [← sdiff_self_inter, hv]
  refine subset_antisymm ?_ (subset_inter heS hl.subset_closure_diff_endpoints)
  rintro x ⟨hxS, hx⟩
  apply IsInducing.subtypeVal.isClosed_iff'.mp hc ⟨x, hxS⟩
  simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr heS] using
    closure_mono (sdiff_subset : e \ {a, b} ⊆ e) hx

end Recognition

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

/-- A primitive link with coincident endpoints and Hausdorff carrier is an intrinsic circuit. -/
lemma IsPrimitiveLink.isCircuit_of_eq [T2Space L] (hL : IsPrimitiveLink L x y) (hxy : x = y) :
    IsCircuit L := by
  subst y
  obtain ⟨γ, hγ, rfl⟩ := isPrimitiveLink_iff_exists_isSimpleLoop.mp hL
  exact hγ.isCircuit

/-! ### Joining links -/

theorem IsPrimitiveLink.union (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M y z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hinter : L ∩ M ⊆ {y}) : IsPrimitiveLink (L ∪ M) x z := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  refine ⟨P.trans Q, IsPrimitive.of_injective ?_, P.trans_range Q⟩
  rw [trans_injective_iff]
  exact ⟨hP.injective hxy, hQ.injective hyz,
    disjoint_left.mpr fun a ha haQ ↦ ha.right (hinter ⟨ha.1, haQ⟩)⟩

theorem IsPrimitiveLink.exists_isSimpleLoop_union (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M y x) (hxy : x ≠ y) (hinter : L ∩ M ⊆ {x, y}) :
    ∃ P : Path x x, P.IsSimpleLoop ∧ range P = L ∪ M := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  refine ⟨P.trans Q, ?_, P.trans_range Q⟩
  rw [IsSimpleLoop, trans_injOn_ico_iff]
  refine ⟨hP.injective hxy, hQ.injective hxy.symm, disjoint_left.mpr fun a ha haQ ↦ ?_⟩
  grind [show a ∈ ({x, y} : Set X) from hinter ⟨ha.left, haQ.left⟩]

/-- Two arcs meeting only at their common endpoints form a circuit. -/
theorem IsPrimitiveLink.isCircuit_union [T2Space ↥(L ∪ M)] (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M y x) (hxy : x ≠ y) (hinter : L ∩ M ⊆ {x, y}) :
    IsCircuit (L ∪ M) := by
  obtain ⟨P, hP, hPrange⟩ := hL.exists_isSimpleLoop_union hM hxy hinter
  let : T2Space ↥(range P) := hPrange.symm ▸ inferInstance
  exact hPrange ▸ hP.isCircuit

/-- Join two arcs meeting only at their common endpoints. The union is an arc or a loop
according to whether the outer endpoints differ. -/
theorem IsPrimitiveLink.union_of_inter_subset (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M y z) (hxy : x ≠ y) (hyz : y ≠ z)
    (hinter : L ∩ M ⊆ ({x, y} : Set X) ∩ {y, z}) : IsPrimitiveLink (L ∪ M) x z := by
  obtain rfl | hxz := eq_or_ne x z
  · exact isPrimitiveLink_iff_exists_isSimpleLoop.mpr
      (hL.exists_isSimpleLoop_union hM hxy (hinter.trans inter_subset_left))
  exact hL.union hM hxy hyz fun w hw ↦ by grind [hinter hw]

/-! ### First contact -/

/-- A primitive link from outside a closed set to a point of the set has an initial sublink
meeting that set only at its terminal point. -/
theorem IsPrimitiveLink.exists_initial_sublink {L A : Set X} {x y : X}
    (hL : IsPrimitiveLink L x y) (hA : IsClosed A) (hx : x ∉ A) (hy : y ∈ A) :
    ∃ b ∈ A, ∃ M ⊆ L, IsPrimitiveLink M x b ∧ M ∩ A = {b} := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨t, htpos, ht, hbefore⟩ := P.exists_first_contact
    (hA.preimage P.continuous) hx ⟨y, P.target_mem_range, hy⟩
  refine ⟨P t, ht, range (P.subpath 0 t), ?_, ?_, ?_⟩
  · rw [P.range_subpath_of_le _ _ t.property.1]
    exact image_subset_range ..
  · exact ⟨(P.subpath 0 t).cast P.source.symm rfl, hP.subpath htpos.ne, rfl⟩
  · rw [P.range_subpath_of_le _ _ t.property.1]
    apply subset_antisymm
    · rintro z ⟨⟨s, hs, rfl⟩, hsA⟩
      rcases hs.2.lt_or_eq with hst | rfl
      · exact (connectedComponentIn_subset _ _ (hbefore ⟨s, ⟨hs.1, hst⟩, rfl⟩) hsA).elim
      · rfl
    · rintro z rfl
      exact ⟨⟨t, ⟨t.property.1, le_rfl⟩, rfl⟩, ht⟩

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

/-- A point of a primitive link outside a closed link containing its endpoints lies on a
supplied simple loop in their union. -/
theorem IsPrimitiveLink.exists_isSimpleLoop_of_mem_diff {a b c : X}
    (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M a b) (hMc : IsClosed M)
    (hx : x ∈ M) (hy : y ∈ M) (hc : c ∈ L \ M) :
    ∃ z, ∃ P : Path z z, P.IsSimpleLoop ∧ range P ⊆ L ∪ M ∧ c ∈ range P := by
  obtain rfl | hxy := eq_or_ne x y
  · obtain ⟨P, hP, rfl⟩ := isPrimitiveLink_iff_exists_isSimpleLoop.mp hL
    exact ⟨x, P, hP, subset_union_left, hc.1⟩
  obtain ⟨u, v, huv, A, hAL, B, hBM, hA, hB, hcA, -, hAB⟩ :=
    hL.exists_sublinks_inter_eq_pair hM hMc hxy hx hy hc
  obtain ⟨P, hP, hPAB⟩ := hA.exists_isSimpleLoop_union hB huv hAB.subset
  exact ⟨u, P, hP, hPAB.symm ▸ union_subset_union hAL hBM, hPAB.symm ▸ Or.inl hcA.1⟩

/-- In a Hausdorff union of two links, an exterior point of a link whose endpoints lie on the
other belongs to a compact circuit in the union. Ambient closedness is not required. -/
theorem IsPrimitiveLink.exists_isCircuit_of_mem_diff {a b c : X} [T2Space ↥(L ∪ M)]
    (hL : IsPrimitiveLink L x y) (hM : IsPrimitiveLink M a b)
    (hx : x ∈ M) (hy : y ∈ M) (hc : c ∈ L \ M) :
    ∃ C ⊆ L ∪ M, IsCircuit C ∧ IsCompact C ∧ c ∈ C := by
  let U := L ∪ M
  have hL' := hL.restrictSubtype (show L ⊆ U from subset_union_left)
  have hM' := hM.restrictSubtype (show M ⊆ U from subset_union_right)
  obtain ⟨z, P, hP, _, hcP⟩ := hL'.exists_isSimpleLoop_of_mem_diff hM' hM'.isClosed
    (show (⟨x, Or.inl hL.left_mem⟩ : U) ∈ Subtype.val ⁻¹' M from hx)
    (show (⟨y, Or.inl hL.right_mem⟩ : U) ∈ Subtype.val ⁻¹' M from hy)
    (show (⟨c, Or.inl hc.1⟩ : U) ∈ (Subtype.val ⁻¹' L) \ (Subtype.val ⁻¹' M) from hc)
  refine ⟨Subtype.val '' range P, ?_, ?_,
    (isCompact_range P.continuous).image continuous_subtype_val, ⟨_, hcP, rfl⟩⟩
  · rintro w ⟨v, _, rfl⟩
    exact v.property
  · exact hP.isCircuit.image (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)

/-- Distinct closed primitive links with the same endpoints contain a supplied simple loop. -/
theorem IsPrimitiveLink.exists_isSimpleLoop_of_ne (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M x y) (hLc : IsClosed L) (hMc : IsClosed M) (hne : L ≠ M) :
    ∃ z, ∃ P : Path z z, P.IsSimpleLoop ∧ range P ⊆ L ∪ M := by
  by_cases hLM : L ⊆ M
  · obtain ⟨c, hcM, hcL⟩ := not_subset.mp fun hML ↦ hne (hLM.antisymm hML)
    obtain ⟨z, P, hP, hsub, -⟩ :=
      hM.exists_isSimpleLoop_of_mem_diff hL hLc hL.left_mem hL.right_mem ⟨hcM, hcL⟩
    exact ⟨z, P, hP, union_comm M L ▸ hsub⟩
  obtain ⟨c, hcL, hcM⟩ := not_subset.mp hLM
  obtain ⟨z, P, hP, hsub, -⟩ :=
    hL.exists_isSimpleLoop_of_mem_diff hM hMc hM.left_mem hM.right_mem ⟨hcL, hcM⟩
  exact ⟨z, P, hP, hsub⟩

/-- Distinct primitive links with the same endpoints and Hausdorff union contain a
compact circuit. -/
theorem IsPrimitiveLink.exists_isCircuit_of_ne [T2Space ↥(L ∪ M)] (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M x y) (hne : L ≠ M) :
    ∃ C ⊆ L ∪ M, IsCircuit C ∧ IsCompact C := by
  by_cases hLM : L ⊆ M
  · obtain ⟨c, hcM, hcL⟩ := not_subset.mp fun hML ↦ hne (hLM.antisymm hML)
    let : T2Space ↥(M ∪ L) := (Homeomorph.setCongr (union_comm M L)).isEmbedding.t2Space
    obtain ⟨C, hC, hCcircuit, hCcompact, -⟩ :=
      hM.exists_isCircuit_of_mem_diff hL hL.left_mem hL.right_mem ⟨hcM, hcL⟩
    exact ⟨C, union_comm M L ▸ hC, hCcircuit, hCcompact⟩
  obtain ⟨c, hcL, hcM⟩ := not_subset.mp hLM
  obtain ⟨C, hC, hCcircuit, hCcompact, -⟩ :=
    hL.exists_isCircuit_of_mem_diff hM hM.left_mem hM.right_mem ⟨hcL, hcM⟩
  exact ⟨C, hC, hCcircuit, hCcompact⟩

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
