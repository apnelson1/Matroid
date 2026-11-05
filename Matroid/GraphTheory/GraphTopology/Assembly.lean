module

public import Matroid.GraphTheory.GraphTopology.Basic

/-! # Assembly from primitive links

`GraphLike.ofLinks` assembles a family of primitive links whose interiors are relatively open,
with a relatively closed, totally separated vertex set. Neither family nor vertex set need be
finite. `GraphLike.ofFiniteLinks` derives these topological hypotheses from finiteness.
The supplied link indices correspond to component edges through explicit equivalences.
-/

@[expose] public section

open Set Function Topology Set.Notation

namespace GraphLike

variable {X ι : Type*} [TopologicalSpace X]

section Components

variable (Z : Set X) (L : ι → Set X)

private def linkParts (i : ι) : Set ↥((Z ∪ ⋃ j, L j) \ Z) := Subtype.val ⁻¹' L i

omit [TopologicalSpace X] in
private lemma linkParts_image (i : ι) :
    Subtype.val '' linkParts Z L i = L i \ Z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2.2⟩
  · rintro ⟨hx, hxZ⟩
    exact ⟨⟨x, Or.inr (mem_iUnion.mpr ⟨i, hx⟩), hxZ⟩, hx, rfl⟩

omit [TopologicalSpace X] in
private lemma linkParts_disjoint
    (hd : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z)) :
    Pairwise (Disjoint on linkParts Z L) := by
  intro i j hij
  exact disjoint_left.mpr fun x hi hj ↦
    (hd hij).notMem_of_mem_left ⟨hi, x.2.2⟩ ⟨hj, x.2.2⟩

omit [TopologicalSpace X] in
private lemma linkParts_cover : ⋃ i, linkParts Z L i = univ := by
  apply eq_univ_of_forall
  rintro ⟨x, hx, hxZ⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hx.resolve_left hxZ)
  exact mem_iUnion.mpr ⟨i, hi⟩

private lemma linkParts_isClopen
    (hd : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z))
    (ho : ∀ i, IsOpen ((Z ∪ ⋃ j, L j) ↓∩ (L i \ Z))) (i : ι) :
    IsClopen (linkParts Z L i) := by
  have hopen (j : ι) : IsOpen (linkParts Z L j) := by
    convert (ho j).preimage
      (continuous_subtype_val.subtype_mk fun x : ↥((Z ∪ ⋃ j, L j) \ Z) ↦ x.2.1) using 1
    ext x
    exact (and_iff_left x.2.2).symm
  have heq : (linkParts Z L i)ᶜ = ⋃ j : {j // j ≠ i}, linkParts Z L j := by
    simpa [iUnion_subtype] using biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ
      (linkParts_cover Z L) (linkParts_disjoint Z L hd) {i}
  refine ⟨isOpen_compl_iff.mp ?_, hopen i⟩
  rw [heq]
  exact isOpen_iUnion fun j ↦ hopen j.1

private lemma linkParts_isConnected (hc : ∀ i, IsConnected (L i \ Z)) (i : ι) :
    IsConnected (linkParts Z L i) := by
  refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
  · rw [← image_nonempty, linkParts_image]
    exact (hc i).nonempty
  · rw [linkParts_image]
    exact (hc i).isPreconnected

private noncomputable def linkComponents
    (hd : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z))
    (ho : ∀ i, IsOpen ((Z ∪ ⋃ j, L j) ↓∩ (L i \ Z)))
    (hc : ∀ i, IsConnected (L i \ Z)) :
    ι ≃ ConnectedComponents ↥((Z ∪ ⋃ i, L i) \ Z) :=
  (ConnectedComponents.equivOfIsClopenOfIsConnected (linkParts_isClopen Z L hd ho)
    (linkParts_disjoint Z L hd) (linkParts_cover Z L) (linkParts_isConnected Z L hc)).symm

private lemma linkComponents_interior
    (hd : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z))
    (ho : ∀ i, IsOpen ((Z ∪ ⋃ j, L j) ↓∩ (L i \ Z)))
    (hc : ∀ i, IsConnected (L i \ Z)) (i : ι) :
    Subtype.val '' (linkComponents Z L hd ho hc i).toSet = L i \ Z := by
  rw [ConnectedComponents.toSet, linkComponents,
    ConnectedComponents.preimage_singleton_equivOfIsClopenOfIsConnected_symm]
  exact linkParts_image Z L i

end Components

section Links

variable (Z : Set X) (a b : ι → Z) (L : ι → Set X)
  [T2Space ↥(Z ∪ ⋃ i, L i)]
  (hlink : ∀ i, IsPrimitiveLink (L i) (a i).1 (b i).1)
  (hvertices : ∀ i, L i ∩ Z = {(a i).1, (b i).1})

omit [TopologicalSpace X] [T2Space ↥(Z ∪ ⋃ i, L i)] in
private lemma link_subset_carrier (i : ι) : L i ⊆ Z ∪ ⋃ j, L j :=
  fun _ hx ↦ Or.inr (mem_iUnion.mpr ⟨i, hx⟩)

include hlink in
private lemma link_isClosed (i : ι) : IsClosed ((Z ∪ ⋃ j, L j) ↓∩ L i) :=
  (IsInducing.subtypeVal.isCompact_preimage' (hlink i).isCompact
    (by simpa only [Subtype.range_coe] using link_subset_carrier Z L i)).isClosed

omit [TopologicalSpace X] [T2Space ↥(Z ∪ ⋃ i, L i)] in
include hvertices in
private lemma link_sdiff_vertices (i : ι) : L i \ Z = L i \ {(a i).1, (b i).1} := by
  rw [← hvertices]
  ext x
  simp only [mem_sdiff, mem_inter_iff]
  tauto

omit [T2Space ↥(Z ∪ ⋃ i, L i)] in
include hlink hvertices in
private lemma linkInterior_isConnected (i : ι) : IsConnected (L i \ Z) := by
  rw [link_sdiff_vertices Z a b L hvertices]
  exact (hlink i).isConnected_diff_endpoints

include hlink hvertices in
private lemma linkInterior_closure (i : ι) :
    (Z ∪ ⋃ j, L j) ∩ closure (L i \ Z) = L i := by
  apply Subset.antisymm
  · rintro x ⟨hxS, hxcl⟩
    have hx : (⟨x, hxS⟩ : ↥(Z ∪ ⋃ j, L j)) ∈
        closure ((Z ∪ ⋃ j, L j) ↓∩ (L i \ Z)) := by
      apply closure_subtype.mpr
      simpa only [image_preimage_eq_inter_range, Subtype.range_coe,
        inter_eq_left.mpr (sdiff_subset.trans (link_subset_carrier Z L i))] using hxcl
    exact (link_isClosed Z a b L hlink i).closure_subset
      (closure_mono (show (Z ∪ ⋃ j, L j) ↓∩ (L i \ Z) ⊆
        (Z ∪ ⋃ j, L j) ↓∩ L i from fun _ h ↦ h.1) hx)
  · intro x hx
    refine ⟨link_subset_carrier Z L i hx, ?_⟩
    rw [link_sdiff_vertices Z a b L hvertices]
    exact (hlink i).subset_closure_diff_endpoints hx

variable (hdisj : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z))
  (hZclosed : IsClosed ((Z ∪ ⋃ i, L i) ↓∩ Z))
  (hZsep : IsTotallySeparated ((Z ∪ ⋃ i, L i) ↓∩ Z))
  (hopen : ∀ i, IsOpen ((Z ∪ ⋃ j, L j) ↓∩ (L i \ Z)))

/-- Assemble primitive links with open interiors and a closed, totally separated vertex set.
All separation and openness assumptions are relative to the resulting carrier. -/
noncomputable def ofLinks : GraphLike X where
  carrier := Z ∪ ⋃ i, L i
  vertexSet := Z
  t2Space := inferInstance
  subset := subset_union_left
  isClosed := hZclosed
  isTotallySeparated := hZsep
  interior_isOpen' := by
    intro e
    obtain ⟨i, rfl⟩ := (linkComponents Z L hdisj hopen
      (linkInterior_isConnected Z a b L hlink hvertices)).surjective e
    rw [linkComponents_interior]
    exact hopen i
  boundary_isPair' := by
    intro e
    obtain ⟨i, rfl⟩ := (linkComponents Z L hdisj hopen
      (linkInterior_isConnected Z a b L hlink hvertices)).surjective e
    dsimp only
    rw [linkComponents_interior, linkInterior_closure Z a b L hlink hvertices]
    exact ⟨a i, b i, by rw [sdiff_sdiff_right_self, hvertices], hlink i⟩

@[simp] lemma ofLinks_carrier :
    (ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen).carrier = Z ∪ ⋃ i, L i := rfl

@[simp] lemma ofLinks_vertexSet :
    (ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen).vertexSet = Z := rfl

@[simp] lemma ofLinks_edgeSet :
    E(ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen) = range L := by
  let q := linkComponents Z L hdisj hopen (linkInterior_isConnected Z a b L hlink hvertices)
  have hr (i) : (Z ∪ ⋃ j, L j) ∩ closure (Subtype.val '' (q i).toSet) = L i := by
    rw [linkComponents_interior, linkInterior_closure Z a b L hlink hvertices]
  ext e
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨i, rfl⟩ := q.surjective c
    exact ⟨i, (hr i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨q i, hr i⟩

lemma ofLinks_mem_edgeSet (i : ι) :
    L i ∈ E(ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen) := by
  rw [ofLinks_edgeSet]
  exact mem_range_self i

@[simp] lemma ofLinks_edgeInterior (i : ι) :
    (ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen).edgeInterior (L i) =
      L i \ Z := rfl

@[simp] lemma ofLinks_edgeBoundary (i : ι) :
    (ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen).edgeBoundary (L i) =
      {(a i).1, (b i).1} := hvertices i

/-- The optional typed correspondence sends each supplied index to its point set. -/
noncomputable def ofLinksEdgeEquiv :
    ι ≃ ↥E(ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen) :=
  Equiv.ofBijective (fun i ↦ ⟨L i, ofLinks_mem_edgeSet Z a b L hlink hvertices hdisj
    hZclosed hZsep hopen i⟩) (by
      constructor
      · intro i j h
        by_contra hij
        have heq : L i = L j := congrArg Subtype.val h
        obtain ⟨x, hx⟩ := (linkInterior_isConnected Z a b L hlink hvertices i).nonempty
        exact (hdisj hij).notMem_of_mem_left hx ⟨heq ▸ hx.1, hx.2⟩
      · intro e
        have hm : e.1 ∈ range L := by
          rw [← ofLinks_edgeSet Z a b L hlink hvertices hdisj hZclosed hZsep hopen]
          exact e.2
        obtain ⟨i, hi⟩ := hm
        exact ⟨i, Subtype.ext hi⟩)

@[simp] lemma ofLinksEdgeEquiv_coe (i : ι) :
    (ofLinksEdgeEquiv Z a b L hlink hvertices hdisj hZclosed hZsep hopen i).1 = L i := rfl

/-- Finiteness is a property of the resulting object, not an assumption of assembly. -/
lemma ofLinks_finite_iff :
    (ofLinks Z a b L hlink hvertices hdisj hZclosed hZsep hopen).Finite ↔
      Z.Finite ∧ _root_.Finite ι := by
  constructor
  · intro h
    let := h
    exact ⟨h.vertexSet_finite, _root_.Finite.of_equiv _
      (ofLinksEdgeEquiv Z a b L hlink hvertices hdisj hZclosed hZsep hopen).symm⟩
  · rintro ⟨hZ, hi⟩
    let := hi
    refine ⟨hZ, ?_⟩
    rw [ofLinks_edgeSet]
    exact finite_range L

end Links

section FiniteLinks

private lemma finite_isTotallySeparated [T2Space X] {Z : Set X} (hZ : Z.Finite) :
    IsTotallySeparated Z := by
  intro x hx y hy hxy
  obtain ⟨U, V, hU, hV, hxU, hrestV, hd⟩ :=
    SeparatedNhds.of_finite (finite_singleton x) (hZ.sdiff (t := {x}))
      (Set.disjoint_left.mpr fun z hz hrest ↦ hrest.2 hz)
  refine ⟨U, V, hU, hV, hxU (by simp), hrestV ⟨hy, by simpa using hxy.symm⟩, ?_, hd⟩
  intro z hz
  by_cases hzx : z = x
  · exact Or.inl (hxU (by simp [hzx]))
  · exact Or.inr (hrestV ⟨hz, hzx⟩)

variable [_root_.Finite ι] (Z : Set X) (hZ : Z.Finite) (a b : ι → Z) (L : ι → Set X)
  [T2Space ↥(Z ∪ ⋃ i, L i)]
  (hlink : ∀ i, IsPrimitiveLink (L i) (a i).1 (b i).1)
  (hvertices : ∀ i, L i ∩ Z = {(a i).1, (b i).1})
  (hdisj : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z))

omit [_root_.Finite ι] in
include hZ in
private lemma finiteLinks_vertexSet_isClosed : IsClosed ((Z ∪ ⋃ i, L i) ↓∩ Z) :=
  (hZ.preimage Subtype.val_injective.injOn).isClosed

omit [_root_.Finite ι] in
include hZ in
private lemma finiteLinks_vertexSet_isTotallySeparated :
    IsTotallySeparated ((Z ∪ ⋃ i, L i) ↓∩ Z) :=
  finite_isTotallySeparated (hZ.preimage Subtype.val_injective.injOn)

include hZ hlink hdisj in
private lemma finiteLinks_interior_isOpen (i : ι) :
    IsOpen ((Z ∪ ⋃ j, L j) ↓∩ (L i \ Z)) := by
  have heq : ((Z ∪ ⋃ j, L j) ↓∩ (L i \ Z)) =
      ((Z ∪ ⋃ j, L j) ↓∩ (Z ∪ ⋃ j : {j // j ≠ i}, L j))ᶜ := by
    ext x
    change (x.1 ∈ L i ∧ x.1 ∉ Z) ↔ ¬ (x.1 ∈ Z ∨ x.1 ∈ ⋃ j : {j // j ≠ i}, L j)
    constructor
    · rintro ⟨hx, hxZ⟩ (hz | hother)
      · exact hxZ hz
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hother
        exact (hdisj j.2.symm).notMem_of_mem_left ⟨hx, hxZ⟩ ⟨hj, hxZ⟩
    · intro hx
      have hxZ : x.1 ∉ Z := fun h ↦ hx (Or.inl h)
      obtain ⟨j, hj⟩ := mem_iUnion.mp (x.2.resolve_left hxZ)
      refine ⟨?_, hxZ⟩
      by_cases hji : j = i
      · simpa [hji] using hj
      · exact (hx (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩))).elim
  rw [heq, preimage_union, preimage_iUnion]
  exact ((finiteLinks_vertexSet_isClosed Z hZ L).union
    (isClosed_iUnion_of_finite fun j : {j // j ≠ i} ↦
      link_isClosed Z a b L hlink j.1)).isOpen_compl

/-- Finite assembly supplies the topological hypotheses of `ofLinks` automatically. -/
noncomputable def ofFiniteLinks : GraphLike X := by
  exact ofLinks Z a b L hlink hvertices hdisj
    (by exact finiteLinks_vertexSet_isClosed Z hZ L)
    (by exact finiteLinks_vertexSet_isTotallySeparated Z hZ L)
    (by exact finiteLinks_interior_isOpen Z hZ a b L hlink hdisj)

@[simp] lemma ofFiniteLinks_carrier :
    (ofFiniteLinks Z hZ a b L hlink hvertices hdisj).carrier = Z ∪ ⋃ i, L i := rfl

@[simp] lemma ofFiniteLinks_vertexSet :
    (ofFiniteLinks Z hZ a b L hlink hvertices hdisj).vertexSet = Z := rfl

/-- The edge correspondence for finite assembly. -/
noncomputable def ofFiniteLinksEdgeEquiv :
    ι ≃ ↥E(ofFiniteLinks Z hZ a b L hlink hvertices hdisj) := by
  exact ofLinksEdgeEquiv Z a b L hlink hvertices hdisj
    (by exact finiteLinks_vertexSet_isClosed Z hZ L)
    (by exact finiteLinks_vertexSet_isTotallySeparated Z hZ L)
    (by exact finiteLinks_interior_isOpen Z hZ a b L hlink hdisj)

@[simp] lemma ofFiniteLinksEdgeEquiv_coe (i : ι) :
    (ofFiniteLinksEdgeEquiv Z hZ a b L hlink hvertices hdisj i).1 = L i := rfl

@[simp] lemma ofFiniteLinks_edgeSet :
    E(ofFiniteLinks Z hZ a b L hlink hvertices hdisj) = range L := ofLinks_edgeSet ..

lemma ofFiniteLinks_mem_edgeSet (i : ι) :
    L i ∈ E(ofFiniteLinks Z hZ a b L hlink hvertices hdisj) := ofLinks_mem_edgeSet ..

@[simp] lemma ofFiniteLinks_edgeInterior (i : ι) :
    (ofFiniteLinks Z hZ a b L hlink hvertices hdisj).edgeInterior (L i) = L i \ Z := rfl

@[simp] lemma ofFiniteLinks_edgeBoundary (i : ι) :
    (ofFiniteLinks Z hZ a b L hlink hvertices hdisj).edgeBoundary (L i) =
      {(a i).1, (b i).1} := hvertices i

instance ofFiniteLinks_finite : (ofFiniteLinks Z hZ a b L hlink hvertices hdisj).Finite :=
  (ofLinks_finite_iff ..).mpr ⟨hZ, inferInstance⟩

end FiniteLinks

end GraphLike
