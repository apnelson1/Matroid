import Matroid.Graph.Topology.Defs
import Matroid.ForMathlib.Topology.PrimitiveLink
import Matroid.ForMathlib.Geometry.PolygonalPath.PrimitivePath
import Matroid.ForMathlib.Geometry.PrimitiveLinkReplacement
import Matroid.Graph.Finite
import Matroid.Graph.Hom.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Finset.Interval

/-!
# Finite polygonalization of graph-like spaces

Finite graph-like spaces in real normed spaces have polygonal replacements preserving
vertices and incidence, with an arbitrarily small error on each edge. The proof uses the
simultaneous primitive-link replacement theorem in `Geometry/PrimitiveLinkReplacement.lean`.

Definitions are imported from `Topology.Defs`. The separate `PolygonalizationSketch`
still declares overlapping proof targets and should be imported independently.
-/

open Set Function TopologicalSpace Metric Topology Graph symmDiff Set.Notation

variable {X : Type*} [TopologicalSpace X] {S Z : Set X}

private abbrev edgeComponent (S Z : Set X) := ConnectedComponents ↥(S \ Z)

private def edgeComponent.interior (e : edgeComponent S Z) : Set X :=
  Subtype.val '' (ConnectedComponents.mk ⁻¹' {e})

private def edgeComponent.range (e : edgeComponent S Z) : Set X :=
  S ∩ closure e.interior

private def edgeComponent.boundary (e : edgeComponent S Z) : Set X :=
  e.range \ e.interior

namespace Graph

variable {V E : Type*}

theorem IsDrawing.t2Space {G : Graph V E} {S : Set X} (h : G.IsDrawing S) : T2Space S := by
  obtain ⟨D, rfl, rfl⟩ := h
  infer_instance

theorem Drawing.boundary_eq (D : Drawing V E X) {e : E(D.graph)} {u v : V(D.graph)}
    (h : D.graph.IsLink e.1 u.1 v.1) : (D.edge e).boundary = {D.vertex u, D.vertex v} :=
  D.iso.map_isLink h

end Graph

namespace GraphLike.edge

variable {G : GraphLike X} (e : G.edge) {x : X}

lemma interior_subset : e.interior ⊆ G.carrier \ G.vertexSet := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

lemma interior_subset_range : e.interior ⊆ e.range :=
  fun _ hx ↦ ⟨(e.interior_subset hx).1, subset_closure hx⟩

lemma range_subset : e.range ⊆ G.carrier := inter_subset_left

lemma interior_nonempty : e.interior.Nonempty := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
  exact ⟨x.1, x, rfl, rfl⟩

lemma mem_interior_iff (hx : x ∈ G.carrier \ G.vertexSet) :
    x ∈ e.interior ↔ ConnectedComponents.mk ⟨x, hx⟩ = e := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

lemma interior_disjoint {f : G.edge} (hef : e ≠ f) : Disjoint e.interior f.interior := by
  refine disjoint_left.mpr fun x he hf ↦ hef ?_
  exact ((e.mem_interior_iff (e.interior_subset he)).mp he).symm.trans
    ((f.mem_interior_iff (e.interior_subset he)).mp hf)

lemma interior_isConnected : IsConnected e.interior := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
  change IsConnected (Subtype.val '' (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x}))
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

lemma range_diff_vertexSet : e.range \ G.vertexSet = e.interior := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxZ⟩
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe e
    have hcl : IsClosed (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk y}) := by
      rw [connectedComponents_preimage_singleton]
      exact isClosed_connectedComponent
    apply (mem_interior_iff _ ⟨hx.1, hxZ⟩).mpr
    apply hcl.closure_subset
    exact (closure_subtype).mpr hx.2
  · intro x hx
    exact ⟨e.interior_subset_range hx, (e.interior_subset hx).2⟩

lemma boundary_eq_inter_vertexSet : e.boundary = e.range ∩ G.vertexSet := by
  rw [boundary, ← e.range_diff_vertexSet]
  ext x
  simp only [mem_sdiff, mem_inter_iff]
  tauto

lemma mem_boundary_iff_of_mem_vertexSet (hx : x ∈ G.vertexSet) :
    x ∈ e.boundary ↔ x ∈ e.range := by
  rw [e.boundary_eq_inter_vertexSet, mem_inter_iff, and_iff_left hx]

lemma range_eq_interior_union_boundary : e.range = e.interior ∪ e.boundary := by
  exact (union_sdiff_cancel e.interior_subset_range).symm

lemma range_diff_boundary : e.range \ e.boundary = e.interior := by
  rw [boundary]
  exact sdiff_sdiff_cancel_left e.interior_subset_range

lemma range_inter_subset_vertexSet {f : G.edge} (hef : e ≠ f) :
    e.range ∩ f.range ⊆ G.vertexSet := by
  intro x hx
  by_contra hxZ
  apply (e.interior_disjoint hef).notMem_of_mem_left (a := x)
  · rw [← e.range_diff_vertexSet]
    exact ⟨hx.1, hxZ⟩
  · rw [← f.range_diff_vertexSet]
    exact ⟨hx.2, hxZ⟩

end GraphLike.edge

namespace GraphLike

class Finite (G : GraphLike X) : Prop where
  vertexSet_finite : G.vertexSet.Finite
  edge_finite : _root_.Finite (G.edge)

instance (G : GraphLike X) [G.Finite] : _root_.Finite G.vertexSet :=
  Finite.vertexSet_finite.to_subtype

instance (G : GraphLike X) [G.Finite] : _root_.Finite (G.edge) :=
  Finite.edge_finite

instance (G : GraphLike X) [G.Finite] : G.toGraph.Finite where
  vertexSet_finite := Finite.vertexSet_finite
  edgeSet_finite := Set.toFinite _

@[simp]
lemma toGraph_finite_iff (G : GraphLike X) : G.toGraph.Finite ↔ G.Finite := by
  constructor
  · intro h
    exact ⟨h.vertexSet_finite, Set.finite_univ_iff.mp h.edgeSet_finite⟩
  · intro h
    infer_instance

@[ext]
lemma ext {G H : GraphLike X} (hS : G.carrier = H.carrier)
    (hZ : G.vertexSet = H.vertexSet) : G = H := by
  cases G
  cases H
  cases hS
  cases hZ
  rfl

instance : PartialOrder (GraphLike X) where
  le G H := G.carrier ⊆ H.carrier ∧ G.vertexSet ⊆ H.vertexSet
  le_refl _ := ⟨Subset.rfl, Subset.rfl⟩
  le_trans _ _ _ hGH hHK := ⟨hGH.1.trans hHK.1, hGH.2.trans hHK.2⟩
  le_antisymm _ _ hGH hHG := ext (hGH.1.antisymm hHG.1) (hGH.2.antisymm hHG.2)

/-- `G.finer H` means that `H` has the same carrier and contains every vertex of `G`. -/
structure finer (G H : GraphLike X) : Prop where
  carrier_eq : G.carrier = H.carrier
  vertices_subset : G.vertexSet ⊆ H.vertexSet

instance : IsPartialOrder (GraphLike X) GraphLike.finer where
  refl _ := ⟨rfl, Subset.rfl⟩
  trans _ _ _ hGH hHK := ⟨hGH.1.trans hHK.1, hGH.2.trans hHK.2⟩
  antisymm _ _ hGH hHG := ext hGH.1 (hGH.2.antisymm hHG.2)

variable (G : GraphLike X)

lemma carrier_eq_vertexSet_union_ranges :
    G.carrier = G.vertexSet ∪ ⋃ e : G.edge, e.range := by
  apply Subset.antisymm
  · intro x hx
    by_cases hxZ : x ∈ G.vertexSet
    · exact Or.inl hxZ
    · let e : G.edge := ConnectedComponents.mk ⟨x, hx, hxZ⟩
      exact Or.inr (mem_iUnion.mpr ⟨e, e.interior_subset_range ⟨⟨x, hx, hxZ⟩, rfl, rfl⟩⟩)
  · rintro x (hx | hx)
    · exact G.subset hx
    · obtain ⟨e, he⟩ := mem_iUnion.mp hx
      exact e.range_subset he

lemma edgeRange_isCompact (e : G.edge) : IsCompact e.range := by
  obtain ⟨x, y, _, h⟩ := G.boundary_isPair e
  exact h.isCompact

lemma isCompact_iff_vertexSet_isCompact [_root_.Finite (G.edge)] :
    IsCompact G.carrier ↔ IsCompact G.vertexSet := by
  constructor
  · intro hG
    have := isCompact_iff_compactSpace.mp hG
    simpa only [image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.mpr G.subset] using G.isClosed.isCompact.image continuous_subtype_val
  · intro hV
    rw [G.carrier_eq_vertexSet_union_ranges]
    exact hV.union (isCompact_iUnion G.edgeRange_isCompact)

lemma isCompact [G.Finite] : IsCompact G.carrier :=
  G.isCompact_iff_vertexSet_isCompact.mpr Finite.vertexSet_finite.isCompact

private noncomputable def edgeSource (e : G.edge) : G.vertexSet :=
  (G.boundary_isPair e).choose

private noncomputable def edgeTarget (e : G.edge) : G.vertexSet :=
  (G.boundary_isPair e).choose_spec.choose

private lemma edgeBoundary (e : G.edge) :
    e.boundary = {(G.edgeSource e).1, (G.edgeTarget e).1} :=
  (G.boundary_isPair e).choose_spec.choose_spec.1

private lemma edgeLink (e : G.edge) :
    IsPrimitiveLink e.range (G.edgeSource e).1 (G.edgeTarget e).1 :=
  (G.boundary_isPair e).choose_spec.choose_spec.2

private noncomputable def edgePath (e : G.edge) :
    Path (G.edgeSource e).1 (G.edgeTarget e).1 :=
  (G.edgeLink e).choose

private lemma edgePath_isPrimitive (e : G.edge) :
    (G.edgePath e).IsPrimitive := (G.edgeLink e).choose_spec.1

private lemma range_edgePath (e : G.edge) :
    range (G.edgePath e) = e.range := (G.edgeLink e).choose_spec.2

private lemma edgePath_interior (e : G.edge) :
    (G.edgePath e).Interior = e.interior := by
  rw [← (G.edgePath_isPrimitive e).range_diff_endpoints, G.range_edgePath,
    ← G.edgeBoundary, e.range_diff_boundary]

private lemma midpoint_mem_interior (e : G.edge) :
    G.edgePath e unitInterval.half ∈ e.interior := by
  rw [← G.edgePath_interior]
  exact ⟨unitInterval.half, ⟨unitInterval.zero_lt_half, unitInterval.half_lt_one⟩, rfl⟩

end GraphLike

section FiniteAssembly

private lemma partition_component_fiber {ι : Type*} {U : ι → Set X}
    (hclopen : ∀ i, IsClopen (U i)) (hdisj : Pairwise (Disjoint on U))
    (hcover : ⋃ i, U i = univ) (hconn : ∀ i, IsConnected (U i)) (i : ι) :
    ConnectedComponents.mk ⁻¹'
      {(ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hcover hconn).symm i} =
        U i := by
  let q := ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hcover hconn
  ext x
  change ConnectedComponents.mk x = q.symm i ↔ x ∈ U i
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover x
    have hq : q (ConnectedComponents.mk x) = j :=
      ConnectedComponents.equivOfIsClopenOfIsConnected_mk hclopen hdisj hcover hconn x hj
    have hji : j = i := by simpa [hx] using hq.symm
    exact hji ▸ hj
  · intro hx
    exact q.injective (by simpa using
      ConnectedComponents.equivOfIsClopenOfIsConnected_mk hclopen hdisj hcover hconn x hx)

private theorem finiteFamily_components {X ι : Type*} [TopologicalSpace X]
    [Finite ι] (Z : Set X) (L : ι → Set X)
    (hclosed : ∀ i, IsClosed ((Z ∪ ⋃ j, L j) ↓∩ L i))
    (hconn : ∀ i, IsConnected (L i \ Z))
    (hdisj : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z)) :
    ∃ e : ι ≃ ConnectedComponents ↥((Z ∪ ⋃ i, L i) \ Z),
      ∀ i, Subtype.val '' (ConnectedComponents.mk ⁻¹' {e i}) = L i \ Z := by
  classical
  let S := (Z ∪ ⋃ i, L i) \ Z
  let U (i : ι) : Set S := Subtype.val ⁻¹' L i
  have himage (i : ι) : Subtype.val '' U i = L i \ Z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2.2⟩
    · rintro ⟨hx, hxZ⟩
      exact ⟨⟨x, Or.inr (mem_iUnion.mpr ⟨i, hx⟩), hxZ⟩, hx, rfl⟩
  have hUdisj : Pairwise (Disjoint on U) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hi hj ↦
      (hdisj hij).notMem_of_mem_left ⟨hi, x.2.2⟩ ⟨hj, x.2.2⟩
  have hcover : ⋃ i, U i = univ := by
    apply eq_univ_of_forall
    rintro ⟨x, hx, hxZ⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hx.resolve_left hxZ)
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hUclopen (i : ι) : IsClopen (U i) := by
    have heq : (U i)ᶜ = ⋃ j : {j // j ≠ i}, U j := by
      simpa [iUnion_subtype] using
        biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ hcover hUdisj {i}
    have hclosedU (j : ι) : IsClosed (U j) :=
      (hclosed j).preimage (continuous_subtype_val.subtype_mk fun x : S ↦ x.2.1)
    refine ⟨hclosedU i, isClosed_compl_iff.mp ?_⟩
    rw [heq]
    exact isClosed_iUnion_of_finite fun j ↦ hclosedU j.1
  have hUconn (i : ι) : IsConnected (U i) := by
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · rw [← image_nonempty, himage]
      exact (hconn i).nonempty
    · rw [himage]
      exact (hconn i).isPreconnected
  let e := ConnectedComponents.equivOfIsClopenOfIsConnected hUclopen hUdisj hcover hUconn
  refine ⟨e.symm, fun i ↦ ?_⟩
  rw [partition_component_fiber hUclopen hUdisj hcover hUconn]
  exact himage i

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

private theorem exists_graphLike_of_finite_links {ι : Type*} [_root_.Finite ι]
    (Z : Set X) (hZ : Z.Finite) (a b : ι → Z) (L : ι → Set X)
    [T2Space ↥(Z ∪ ⋃ i, L i)]
    (hlink : ∀ i, IsPrimitiveLink (L i) (a i).1 (b i).1)
    (hvertices : ∀ i, L i ∩ Z = {(a i).1, (b i).1})
    (hdisj : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z)) :
    ∃ (G : GraphLike X) (e : ι ≃ G.edge),
      G.carrier = Z ∪ ⋃ i, L i ∧ G.vertexSet = Z ∧
      ∀ i, (e i).interior = L i \ Z ∧ (e i).range = L i ∧
        (e i).boundary = {(a i).1, (b i).1} := by
  classical
  let S := Z ∪ ⋃ i, L i
  have hLS (i : ι) : L i ⊆ S := fun _ hx ↦ Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  have hclosed (i : ι) : IsClosed (S ↓∩ L i) :=
    (IsInducing.subtypeVal.isCompact_preimage' (hlink i).isCompact
      (by simpa only [Subtype.range_coe] using hLS i)).isClosed
  have hZclosed : IsClosed (S ↓∩ Z) :=
    (hZ.preimage Subtype.val_injective.injOn).isClosed
  have hdiff (i : ι) : L i \ Z = L i \ {(a i).1, (b i).1} := by
    rw [← hvertices]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hconn (i : ι) : IsConnected (L i \ Z) := by
    obtain ⟨γ, hγ, hγL⟩ := hlink i
    rw [hdiff, ← hγL]
    exact hγ.isConnected_range_diff_endpoints
  have hclosure (i : ι) : S ∩ closure (L i \ Z) = L i := by
    apply Subset.antisymm
    · rintro x ⟨hxS, hxcl⟩
      have hx : (⟨x, hxS⟩ : S) ∈ closure (S ↓∩ (L i \ Z)) := by
        apply closure_subtype.mpr
        simpa only [image_preimage_eq_inter_range, Subtype.range_coe,
          inter_eq_left.mpr (sdiff_subset.trans (hLS i))] using hxcl
      exact (hclosed i).closure_subset (closure_mono (fun _ h ↦ h.1) hx)
    · intro x hx
      refine ⟨hLS i hx, ?_⟩
      obtain ⟨γ, hγ, hγL⟩ := hlink i
      rw [hdiff, ← hγL, hγ.range_diff_endpoints]
      exact γ.range_subset_closure_interior (hγL.symm ▸ hx)
  obtain ⟨e, he⟩ := finiteFamily_components Z L hclosed hconn hdisj
  change ι ≃ edgeComponent S Z at e
  have hrange (i : ι) : (e i).range = L i := by
    change S ∩ closure (Subtype.val '' (ConnectedComponents.mk ⁻¹' {e i})) = L i
    rw [he, hclosure]
  have hboundary (i : ι) : (e i).boundary = {(a i).1, (b i).1} := by
    change (e i).range \ (e i).interior = _
    rw [hrange, show (e i).interior = L i \ Z from he i, sdiff_sdiff_right_self,
      hvertices]
  have hopen (i : ι) : IsOpen (S ↓∩ (L i \ Z)) := by
    have heq : (S ↓∩ (L i \ Z)) =
        (S ↓∩ (Z ∪ ⋃ j : {j // j ≠ i}, L j))ᶜ := by
      ext x
      change (x.1 ∈ L i ∧ x.1 ∉ Z) ↔ ¬ (x.1 ∈ Z ∨
        x.1 ∈ ⋃ j : {j // j ≠ i}, L j)
      constructor
      · rintro ⟨hx, hxZ⟩ (hZ | hother)
        · exact hxZ hZ
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
    exact (hZclosed.union (isClosed_iUnion_of_finite
      (fun j : {j // j ≠ i} ↦ hclosed j))).isOpen_compl
  let G : GraphLike X := {
    carrier := S
    vertexSet := Z
    t2Space := inferInstance
    subset := subset_union_left
    isClosed := hZclosed
    isTotallySeparated := finite_isTotallySeparated (hZ.preimage Subtype.val_injective.injOn)
    interior_isOpen := by
      intro C
      obtain ⟨i, rfl⟩ := e.surjective C
      change IsOpen (S ↓∩ (Subtype.val '' (ConnectedComponents.mk ⁻¹' {e i})))
      rw [he]
      exact hopen i
    boundary_isPair := by
      intro C
      obtain ⟨i, rfl⟩ := e.surjective C
      refine ⟨a i, b i, hboundary i, ?_⟩
      change IsPrimitiveLink (e i).range (a i).1 (b i).1
      rw [hrange]
      exact hlink i }
  exact ⟨G, e, rfl, rfl, fun i ↦ ⟨he i, hrange i, hboundary i⟩⟩

end FiniteAssembly

namespace GraphLike

theorem exists_vertexRadius {Y : Type*} [MetricSpace Y] (G : GraphLike Y) [Finite G] :
    ∃ r : G.vertexSet → ℝ, (∀ x, 0 < r x) ∧
    (Pairwise fun x y ↦ Disjoint (closedBall x.1 (r x)) (closedBall y.1 (r y))) ∧
    ∀ x, closedBall x.1 (r x) ∩ G.carrier ⊆ {x.1} ∪
      ⋃ e ∈ {e : G.edge | x.1 ∈ e.boundary}, e.range := by
  classical
  obtain ⟨r, hpos, _, hdisj, havoid⟩ := exists_disjoint_closedBall_avoiding
    (fun e : G.edge ↦ e.range)
    (fun e ↦ (G.edgeRange_isCompact e).isClosed)
    (fun _ : G.vertexSet ↦ 1) (fun _ ↦ zero_lt_one)
  refine ⟨r, hpos, hdisj, ?_⟩
  rintro x z ⟨hzball, hzG⟩
  rw [G.carrier_eq_vertexSet_union_ranges, mem_union, mem_iUnion] at hzG
  obtain hz | ⟨e, he⟩ := hzG
  · let y : G.vertexSet := ⟨z, hz⟩
    by_cases hyx : y = x
    · exact Or.inl (congrArg Subtype.val hyx)
    exact ((hdisj hyx).notMem_of_mem_left (mem_closedBall_self (hpos y).le) hzball).elim
  by_cases hinc : x.1 ∈ e.boundary
  · exact Or.inr <| mem_biUnion hinc he
  exact ((havoid e x ((e.mem_boundary_iff_of_mem_vertexSet x.2).not.mp hinc)).notMem_of_mem_left
    he hzball).elim

end GraphLike

namespace Graph.Drawing

variable {V E : Type*} (D : Drawing V E X)

instance [D.graph.Finite] : D.toGraphLike.Finite where
  vertexSet_finite := by
    let : _root_.Finite V(D.graph) := D.graph.vertexSet_finite.to_subtype
    let : _root_.Finite D.vertexSet := _root_.Finite.of_equiv V(D.graph) D.iso.vertEquiv
    exact Set.toFinite _
  edge_finite := by
    let : _root_.Finite E(D.graph) := D.graph.edgeSet_finite.to_subtype
    exact _root_.Finite.of_equiv E(D.graph) D.edge

end Graph.Drawing

section PolygonalCarrierInvariance

private lemma finite_edge_inter_other_vertices (G H : GraphLike X)
    (hfinite : ((H.carrier ∩ G.vertexSet) \ H.vertexSet).Finite)
    (e : H.edge) :
    (e.range ∩ G.vertexSet).Finite := by
  obtain ⟨x, y, hends, _⟩ := H.boundary_isPair e
  change e.boundary = {x.1, y.1} at hends
  have hb : e.boundary.Finite := hends ▸ (finite_singleton _).insert _
  refine (hb.union hfinite).subset fun z hz ↦ ?_
  by_cases hzH : z ∈ H.vertexSet
  · exact Or.inl (e.boundary_eq_inter_vertexSet.symm ▸ ⟨hz.1, hzH⟩)
  · exact Or.inr ⟨⟨e.range_subset hz.1, hz.2⟩, hzH⟩

private lemma exists_edge_of_isConnected (G : GraphLike X) {K : Set X} (hK : IsConnected K)
    (hsub : K ⊆ G.carrier \ G.vertexSet) : ∃ e : G.edge, K ⊆ e.interior := by
  obtain ⟨x, hx⟩ := hK.nonempty
  let x' : ↥(G.carrier \ G.vertexSet) := ⟨x, hsub hx⟩
  let e : G.edge := ConnectedComponents.mk x'
  refine ⟨e, fun y hy ↦ ?_⟩
  apply (e.mem_interior_iff (hsub hy)).mpr
  apply ConnectedComponents.coe_eq_coe'.mpr
  have hpre : IsPreconnected (Subtype.val ⁻¹' K : Set ↥(G.carrier \ G.vertexSet)) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
    exact hK.isPreconnected
  exact hpre.subset_connectedComponent hx hy

private lemma exists_edgePiece_of_no_vertex_crossing (G : GraphLike X) {x y : X}
    (γ : Path x y) (hcarrier : range γ ⊆ G.carrier) {s t : unitInterval} (hst : s < t)
    (hvertices : ∀ u ∈ Ioo s t, γ u ∉ G.vertexSet) :
    ∃ e : G.edge, γ '' Ioo s t ⊆ e.interior ∧
      range (γ.subpath s t) ⊆ e.range := by
  have hc : IsConnected (γ '' Ioo s t) :=
    (isConnected_Ioo hst).image γ γ.continuous.continuousOn
  obtain ⟨e, he⟩ := exists_edge_of_isConnected G hc (by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨hcarrier (mem_range_self u), hvertices u hu⟩)
  refine ⟨e, he, ?_⟩
  rw [γ.range_subpath_of_le _ _ hst.le]
  rintro z ⟨u, hu, rfl⟩
  refine ⟨hcarrier (mem_range_self u), ?_⟩
  apply closure_mono he
  apply image_closure_subset_closure_image γ.continuous
  exact ⟨u, by rwa [closure_Ioo hst.ne], rfl⟩

end PolygonalCarrierInvariance

section GraphLikeSubdivision

open unitInterval

namespace GraphLike

variable (G : GraphLike X)

private def splitVertexSet : Set X :=
  G.vertexSet ∪ range (fun e : G.edge ↦ G.edgePath e half)

private lemma splitVertexSet_finite [G.Finite] : G.splitVertexSet.Finite :=
  Finite.vertexSet_finite.union (finite_range _)

private lemma splitVertexSet_subset : G.splitVertexSet ⊆ G.carrier := by
  rintro x (hx | ⟨e, rfl⟩)
  · exact G.subset hx
  · exact e.range_subset (e.interior_subset_range (G.midpoint_mem_interior e))

private noncomputable def splitSource :
    G.edge × Bool → G.splitVertexSet
  | (e, false) => ⟨(G.edgeSource e).1, Or.inl (G.edgeSource e).2⟩
  | (e, true) => ⟨G.edgePath e half, Or.inr ⟨e, rfl⟩⟩

private noncomputable def splitTarget :
    G.edge × Bool → G.splitVertexSet
  | (e, false) => ⟨G.edgePath e half, Or.inr ⟨e, rfl⟩⟩
  | (e, true) => ⟨(G.edgeTarget e).1, Or.inl (G.edgeTarget e).2⟩

private noncomputable def splitPath (i : G.edge × Bool) :
    Path (G.splitSource i).1 (G.splitTarget i).1 :=
  match i with
  | (e, false) => (G.edgePath e).firstHalf
  | (e, true) => (G.edgePath e).secondHalf

private lemma splitPath_injective (i : G.edge × Bool) :
    Injective (G.splitPath i) := by
  rcases i with ⟨e, b⟩
  cases b
  · exact (G.edgePath_isPrimitive e).injective_firstHalf
  · exact (G.edgePath_isPrimitive e).injective_secondHalf

private lemma splitSource_ne_splitTarget (i : G.edge × Bool) :
    G.splitSource i ≠ G.splitTarget i := by
  rcases i with ⟨e, b⟩
  cases b
  · intro h
    exact (G.edgePath_isPrimitive e).half_ne_source (congrArg Subtype.val h).symm
  · intro h
    exact (G.edgePath_isPrimitive e).half_ne_target (congrArg Subtype.val h)

private lemma splitPath_range_union (e : G.edge) :
    range (G.splitPath (e, false)) ∪ range (G.splitPath (e, true)) = e.range := by
  rw [← G.range_edgePath]
  exact (G.edgePath e).firstHalf_range_union_secondHalf_range

private lemma splitPath_range_subset (i : G.edge × Bool) :
    range (G.splitPath i) ⊆ i.1.range := by
  rcases i with ⟨e, b⟩
  rw [← G.splitPath_range_union e]
  cases b
  · exact subset_union_left
  · exact subset_union_right

private lemma firstHalf_range_inter_vertexSet (e : G.edge) :
    range (G.edgePath e).firstHalf ∩ G.vertexSet = {(G.edgeSource e).1} := by
  apply Subset.antisymm
  · rw [Path.range_firstHalf]
    rintro z ⟨⟨t, ht, rfl⟩, hz⟩
    have ht0 : t = 0 := by
      by_contra ht0
      have hI : G.edgePath e t ∈ e.interior := by
        rw [← G.edgePath_interior]
        exact ⟨t, ⟨lt_of_le_of_ne zero_le (Ne.symm ht0), ht.2.trans_lt half_lt_one⟩, rfl⟩
      exact (e.interior_subset hI).2 hz
    simp [ht0]
  · rintro z rfl
    exact ⟨(G.edgePath e).firstHalf.source_mem_range, (G.edgeSource e).2⟩

private lemma secondHalf_range_inter_vertexSet (e : G.edge) :
    range (G.edgePath e).secondHalf ∩ G.vertexSet = {(G.edgeTarget e).1} := by
  apply Subset.antisymm
  · rw [Path.range_secondHalf]
    rintro z ⟨⟨t, ht, rfl⟩, hz⟩
    have ht1 : t = 1 := by
      by_contra ht1
      have hI : G.edgePath e t ∈ e.interior := by
        rw [← G.edgePath_interior]
        exact ⟨t, ⟨zero_lt_half.trans_le ht.1, lt_of_le_of_ne t.2.2 ht1⟩, rfl⟩
      exact (e.interior_subset hI).2 hz
    simp [ht1]
  · rintro z rfl
    exact ⟨(G.edgePath e).secondHalf.target_mem_range, (G.edgeTarget e).2⟩

private lemma midpoint_mem_range_iff (e f : G.edge) :
    G.edgePath f half ∈ e.range ↔ e = f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ f.interior_subset_range (G.midpoint_mem_interior f)⟩
  by_contra hef
  exact (f.interior_subset (G.midpoint_mem_interior f)).2
    (e.range_inter_subset_vertexSet hef ⟨h, f.interior_subset_range (G.midpoint_mem_interior f)⟩)

private lemma splitPath_range_inter_vertexSet (i : G.edge × Bool) :
    range (G.splitPath i) ∩ G.splitVertexSet = {(G.splitSource i).1, (G.splitTarget i).1} := by
  apply Subset.antisymm
  · rintro z ⟨hz, hzV | ⟨f, rfl⟩⟩
    · rcases i with ⟨e, b⟩
      cases b
      · exact Or.inl (mem_singleton_iff.mp
          (show z ∈ {(G.edgeSource e).1} from G.firstHalf_range_inter_vertexSet e ▸ ⟨hz, hzV⟩))
      · exact Or.inr (G.secondHalf_range_inter_vertexSet e ▸ ⟨hz, hzV⟩)
    · have hef : i.1 = f := (G.midpoint_mem_range_iff _ _).mp (G.splitPath_range_subset i hz)
      rcases i with ⟨e, b⟩
      dsimp at hef
      subst f
      cases b
      · exact Or.inr rfl
      · exact Or.inl rfl
  · rintro z (rfl | hz)
    · exact ⟨(G.splitPath i).source_mem_range, (G.splitSource i).2⟩
    · rw [mem_singleton_iff] at hz
      subst z
      exact ⟨(G.splitPath i).target_mem_range, (G.splitTarget i).2⟩

private lemma splitPath_range_pairwise : Pairwise fun i j : G.edge × Bool ↦
    range (G.splitPath i) ∩ range (G.splitPath j) ⊆ G.splitVertexSet := by
  intro i j hij z hz
  by_cases hef : i.1 = j.1
  · rcases i with ⟨e, b⟩
    rcases j with ⟨f, c⟩
    dsimp at hef
    subst f
    have hbc : b ≠ c := fun h ↦ hij (h ▸ rfl)
    have hinter : range (G.edgePath e).firstHalf ∩ range (G.edgePath e).secondHalf ⊆
        G.splitVertexSet := by
      rw [Path.range_firstHalf, Path.range_secondHalf]
      rintro z ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩
      obtain hst | hp := G.edgePath_isPrimitive e (hsz.trans htz.symm)
      · have hs : s = half := hs.2.antisymm (hst ▸ ht.1)
        exact Or.inr ⟨e, (congrArg (G.edgePath e) hs).symm.trans hsz⟩
      · rcases pair_eq_pair_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (hsz ▸ (by simpa only [Path.source] using (G.edgeSource e).2))
        · exact Or.inl (hsz ▸ (by simpa only [Path.target] using (G.edgeTarget e).2))
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hinter hz
    · exact hinter ⟨hz.2, hz.1⟩
    · exact (hbc rfl).elim
  · exact Or.inl (i.1.range_inter_subset_vertexSet hef
      ⟨G.splitPath_range_subset i hz.1, G.splitPath_range_subset j hz.2⟩)

private lemma splitPath_carrier :
    G.splitVertexSet ∪ ⋃ i : G.edge × Bool, range (G.splitPath i) =
      G.carrier := by
  apply Subset.antisymm
  · rintro z (hz | hz)
    · exact G.splitVertexSet_subset hz
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact i.1.range_subset (G.splitPath_range_subset i hi)
  · intro z hz
    rw [G.carrier_eq_vertexSet_union_ranges] at hz
    rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · obtain ⟨e, he⟩ := mem_iUnion.mp hz
      rw [← G.splitPath_range_union e] at he
      rcases he with he | he
      · exact Or.inr (mem_iUnion.mpr ⟨(e, false), he⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨(e, true), he⟩)

end GraphLike

end GraphLikeSubdivision

section FinitePointSeparation

private theorem isTotallySeparated_union_finite_of_closed_neighborhoods {S M : Set X}
    (hS : IsTotallySeparated S) (hM : M.Finite)
    (hsep : ∀ m ∈ M, ∃ U K : Set X, IsOpen U ∧ IsClosed K ∧ m ∈ U ∧ U ⊆ K ∧
      K ∩ (S ∪ M) ⊆ {m}) : IsTotallySeparated (S ∪ M) := by
  classical
  let : _root_.Finite M := hM.to_subtype
  choose U K hU hK hmU hUK htrace using fun m : M ↦ hsep m.1 m.2
  have hpoint (m : M) {y : X} (hy : y ∈ S ∪ M) (hmy : m.1 ≠ y) :
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ m.1 ∈ A ∧ y ∈ B ∧
        S ∪ M ⊆ A ∪ B ∧ Disjoint A B := by
    refine ⟨U m, (K m)ᶜ, hU m, (hK m).isOpen_compl, hmU m, ?_, ?_, ?_⟩
    · exact fun hyK ↦ hmy (mem_singleton_iff.mp (htrace m ⟨hyK, hy⟩)).symm
    · intro z hz
      by_cases hzK : z ∈ K m
      · have hzm : z = m.1 := htrace m ⟨hzK, hz⟩
        exact Or.inl (hzm ▸ hmU m)
      · exact Or.inr hzK
    · exact disjoint_left.mpr fun z hzU hzK ↦ hzK (hUK m hzU)
  let A : Set X := ⋃ m : M, U m
  let C : Set X := ⋃ m : M, K m
  have hA : IsOpen A := isOpen_iUnion hU
  have hC : IsClosed C := isClosed_iUnion_of_finite hK
  have hAC : A ⊆ C := iUnion_mono hUK
  have hMA : M ⊆ A := fun m hm ↦ mem_iUnion.mpr ⟨⟨m, hm⟩, hmU ⟨m, hm⟩⟩
  have htraceC : C ∩ (S ∪ M) ⊆ M := by
    rintro z ⟨hzC, hz⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp hzC
    have hzm : z = m.1 := htrace m ⟨hm, hz⟩
    exact hzm ▸ m.2
  intro x hx y hy hxy
  by_cases hxM : x ∈ M
  · exact hpoint ⟨x, hxM⟩ hy hxy
  by_cases hyM : y ∈ M
  · obtain ⟨B, A, hB, hA, hyB, hxA, hcover, hd⟩ := hpoint ⟨y, hyM⟩ hx hxy.symm
    exact ⟨A, B, hA, hB, hxA, hyB, hcover.trans (by rw [union_comm]), hd.symm⟩
  obtain ⟨U₀, V₀, hU₀, hV₀, hxU₀, hyV₀, hcover, hd⟩ :=
    hS (hx.resolve_right hxM) (hy.resolve_right hyM) hxy
  refine ⟨(U₀ \ C) ∪ A, V₀ \ C, (hU₀.sdiff hC).union hA, hV₀.sdiff hC,
    Or.inl ⟨hxU₀, fun hxC ↦ hxM (htraceC ⟨hxC, hx⟩)⟩,
    ⟨hyV₀, fun hyC ↦ hyM (htraceC ⟨hyC, hy⟩)⟩, ?_, ?_⟩
  · intro z hz
    by_cases hzC : z ∈ C
    · exact Or.inl (Or.inr (hMA (htraceC ⟨hzC, hz⟩)))
    have hzS : z ∈ S := hz.resolve_right fun hzM ↦ hzC (hAC (hMA hzM))
    exact (hcover hzS).elim (fun hzU ↦ Or.inl (Or.inl ⟨hzU, hzC⟩))
      (fun hzV ↦ Or.inr ⟨hzV, hzC⟩)
  · refine disjoint_left.mpr ?_
    rintro z (⟨hzU, _⟩ | hzA) ⟨hzV, hzC⟩
    · exact hd.notMem_of_mem_left hzU hzV
    · exact hzC (hAC hzA)

end FinitePointSeparation

section GeneralSubdivision

open unitInterval

namespace GraphLike

variable (G : GraphLike X)

private def splitInterior (i : G.edge × Bool) : Set X :=
  range (G.splitPath i) \ G.splitVertexSet

private lemma splitInterior_eq (i : G.edge × Bool) :
    G.splitInterior i = i.1.interior \ range (G.splitPath (i.1, !i.2)) := by
  have hi : i ≠ (i.1, !i.2) := by rcases i with ⟨e, b⟩; cases b <;> simp
  have hmid : G.edgePath i.1 half ∈ range (G.splitPath (i.1, !i.2)) := by
    rcases i with ⟨e, b⟩
    cases b
    · exact (G.edgePath e).secondHalf.source_mem_range
    · exact (G.edgePath e).firstHalf.target_mem_range
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    refine ⟨?_, fun hz' ↦ hzV (G.splitPath_range_pairwise hi ⟨hz, hz'⟩)⟩
    rw [← i.1.range_diff_vertexSet]
    exact ⟨G.splitPath_range_subset i hz, fun h ↦ hzV (Or.inl h)⟩
  · rintro ⟨hz, hz'⟩
    have hzrange := i.1.interior_subset_range hz
    have hzF : z ∈ range (G.splitPath i) := by
      rcases i with ⟨e, b⟩
      rw [← G.splitPath_range_union e] at hzrange
      cases b
      · exact hzrange.resolve_right hz'
      · exact hzrange.resolve_left hz'
    refine ⟨hzF, ?_⟩
    rintro (hzV | ⟨f, hf⟩)
    · exact (i.1.interior_subset hz).2 hzV
    · change G.edgePath f half = z at hf
      have hef : i.1 = f := (G.midpoint_mem_range_iff _ _).mp (hf.symm ▸ hzrange)
      exact hz' (hf ▸ (hef ▸ hmid))

private lemma splitPath_range_relatively_closed (i : G.edge × Bool) :
    IsClosed (G.carrier ↓∩ range (G.splitPath i)) := by
  apply IsCompact.isClosed
  apply IsInducing.subtypeVal.isCompact_preimage' (isCompact_range (G.splitPath i).continuous)
  simpa only [Subtype.range_coe] using
    (G.splitPath_range_subset i).trans i.1.range_subset

private lemma splitInterior_isOpen (i : G.edge × Bool) :
    IsOpen (G.carrier ↓∩ G.splitInterior i) := by
  rw [G.splitInterior_eq, preimage_sdiff]
  exact (G.interior_isOpen i.1).sdiff (G.splitPath_range_relatively_closed (i.1, !i.2))

private lemma splitVertexSet_isClosed : IsClosed (G.carrier ↓∩ G.splitVertexSet) := by
  have heq : (G.carrier ↓∩ G.splitVertexSet)ᶜ =
      ⋃ i : G.edge × Bool, G.carrier ↓∩ G.splitInterior i := by
    ext z
    constructor
    · intro hz
      have hzC : z.1 ∈ G.splitVertexSet ∪ ⋃ i, range (G.splitPath i) :=
        G.splitPath_carrier.symm ▸ z.2
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hzC.resolve_left hz)
      exact mem_iUnion.mpr ⟨i, hi, hz⟩
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hi.2
  exact isOpen_compl_iff.mp (heq ▸ isOpen_iUnion G.splitInterior_isOpen)

private lemma splitInterior_isConnected (i : G.edge × Bool) :
    IsConnected (G.splitInterior i) := by
  have heq : G.splitInterior i = range (G.splitPath i) \
      {(G.splitSource i).1, (G.splitTarget i).1} := by
    rw [splitInterior, ← G.splitPath_range_inter_vertexSet]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [heq]
  exact (Path.IsPrimitive.of_injective (G.splitPath_injective i)).isConnected_range_diff_endpoints

private theorem exists_splitEdgeEquiv :
    ∃ e : (G.edge × Bool) ≃ edgeComponent G.carrier G.splitVertexSet,
      ∀ i, (e i).interior = G.splitInterior i ∧ (e i).range = range (G.splitPath i) ∧
        (e i).boundary = {(G.splitSource i).1, (G.splitTarget i).1} := by
  classical
  let S := G.carrier \ G.splitVertexSet
  let U (i : G.edge × Bool) : Set S :=
    Subtype.val ⁻¹' G.splitInterior i
  have himage (i) : Subtype.val '' U i = G.splitInterior i := by
    apply image_preimage_eq_of_subset
    simpa only [Subtype.range_coe] using
      (show G.splitInterior i ⊆ S from fun x hx ↦
        ⟨i.1.range_subset (G.splitPath_range_subset i hx.1), hx.2⟩)
  have hUopen (i) : IsOpen (U i) :=
    (G.splitInterior_isOpen i).preimage
      (continuous_subtype_val.subtype_mk fun x : S ↦ x.2.1)
  have hUdisj : Pairwise (Disjoint on U) := by
    intro i j hij
    exact disjoint_left.mpr fun z hzi hzj ↦
      z.2.2 (G.splitPath_range_pairwise hij ⟨hzi.1, hzj.1⟩)
  have hcover : ⋃ i, U i = univ := by
    apply eq_univ_of_forall
    intro z
    have hzC : z.1 ∈ G.splitVertexSet ∪ ⋃ i, range (G.splitPath i) :=
      G.splitPath_carrier.symm ▸ z.2.1
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hzC.resolve_left z.2.2)
    exact mem_iUnion.mpr ⟨i, hi, z.2.2⟩
  have hUclopen (i) : IsClopen (U i) := by
    refine ⟨?_, hUopen i⟩
    have heq : (U i)ᶜ = ⋃ j : {j // j ≠ i}, U j := by
      simpa [iUnion_subtype] using
        biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ hcover hUdisj {i}
    exact isOpen_compl_iff.mp (heq ▸ isOpen_iUnion fun j ↦ hUopen j.1)
  have hUconn (i) : IsConnected (U i) := by
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · rw [← image_nonempty, himage]
      exact (G.splitInterior_isConnected i).nonempty
    · rw [himage]
      exact (G.splitInterior_isConnected i).isPreconnected
  let q := ConnectedComponents.equivOfIsClopenOfIsConnected hUclopen hUdisj hcover hUconn
  change edgeComponent G.carrier G.splitVertexSet ≃
    (G.edge × Bool) at q
  have he (i) : (q.symm i).interior = G.splitInterior i := by
    unfold edgeComponent.interior
    rw [partition_component_fiber hUclopen hUdisj hcover hUconn]
    exact himage i
  have hrange (i) : (q.symm i).range = range (G.splitPath i) := by
    change G.carrier ∩ closure (q.symm i).interior = _
    rw [he]
    apply Subset.antisymm
    · rintro z ⟨hzC, hzcl⟩
      have hsub : G.splitInterior i ⊆ G.carrier := fun x hx ↦
        i.1.range_subset (G.splitPath_range_subset i hx.1)
      have hz : (⟨z, hzC⟩ : G.carrier) ∈ closure (G.carrier ↓∩ G.splitInterior i) := by
        apply closure_subtype.mpr
        simpa only [image_preimage_eq_inter_range, Subtype.range_coe,
          inter_eq_left.mpr hsub] using hzcl
      exact (G.splitPath_range_relatively_closed i).closure_subset
        (closure_mono (fun x hx ↦ hx.1) hz)
    · intro z hz
      refine ⟨i.1.range_subset (G.splitPath_range_subset i hz), ?_⟩
      have hprim := Path.IsPrimitive.of_injective (G.splitPath_injective i)
      have hdiff : G.splitInterior i = (G.splitPath i).Interior := by
        rw [← hprim.range_diff_endpoints, splitInterior,
          ← G.splitPath_range_inter_vertexSet]
        ext x
        simp only [mem_sdiff, mem_inter_iff]
        tauto
      rw [hdiff]
      exact (G.splitPath i).range_subset_closure_interior hz
  refine ⟨q.symm, fun i ↦ ⟨he i, hrange i, ?_⟩⟩
  rw [edgeComponent.boundary, he, hrange, splitInterior, Set.sdiff_sdiff_right_self,
    G.splitPath_range_inter_vertexSet]

private lemma exists_splitMidpoint_neighborhood (m : G.carrier)
    (hm : m.1 ∈ range (fun e : G.edge ↦ G.edgePath e half)) :
    ∃ U K : Set G.carrier, IsOpen U ∧ IsClosed K ∧ m ∈ U ∧ U ⊆ K ∧
      K ∩ (G.carrier ↓∩ G.splitVertexSet) ⊆ {m} := by
  obtain ⟨e, he⟩ := hm
  change G.edgePath e half = m.1 at he
  have hmE : m ∈ G.carrier ↓∩ e.interior := by
    change m.1 ∈ e.interior
    rw [← he]
    exact G.midpoint_mem_interior e
  have hcompact : IsCompact (G.carrier ↓∩ e.range) := by
    apply IsInducing.subtypeVal.isCompact_preimage' (G.edgeRange_isCompact e)
    simpa only [Subtype.range_coe] using e.range_subset
  have hnhds : G.carrier ↓∩ e.range ∈ 𝓝 m :=
    Filter.mem_of_superset ((G.interior_isOpen e).mem_nhds hmE)
      (fun _ hx ↦ e.interior_subset_range hx)
  obtain ⟨K, hKm, hKc, hKE⟩ :=
    exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds continuous_id
      ((G.interior_isOpen e).mem_nhds hmE) hcompact hnhds
  obtain ⟨U, hUK, hUo, hmU⟩ := mem_nhds_iff.mp hKm
  refine ⟨U, K, hUo, hKc.isClosed, hmU, hUK, ?_⟩
  rintro x ⟨hxK, hxZ⟩
  have hxE : x.1 ∈ e.interior := hKE hxK
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  rcases hxZ with hxV | ⟨f, hf⟩
  · exact ((e.interior_subset hxE).2 hxV).elim
  · change G.edgePath f half = x.1 at hf
    have hef : e = f := (G.midpoint_mem_range_iff e f).mp (by
      rw [hf]
      exact e.interior_subset_range hxE)
    rw [← hf, ← hef, he]

/-- Subdivision preserves the graph-like axioms when the enlarged vertex set is ambiently
totally separated. -/
private theorem exists_graphLike_split_of_separated
    (hsep : IsTotallySeparated (G.carrier ↓∩ G.splitVertexSet)) :
    ∃ (H : GraphLike X), G.finer H ∧ H.vertexSet = G.splitVertexSet ∧
      Nonempty ((G.edge × Bool) ≃ H.edge) ∧
      ∀ e : H.edge,
        ∃ (x y : H.vertexSet) (P : Path x.1 y.1),
          Injective P ∧ range P = e.range ∧ e.boundary = {x.1, y.1} := by
  obtain ⟨q, hq⟩ := G.exists_splitEdgeEquiv
  let H : GraphLike X := {
    carrier := G.carrier
    vertexSet := G.splitVertexSet
    t2Space := G.t2Space
    subset := G.splitVertexSet_subset
    isClosed := G.splitVertexSet_isClosed
    isTotallySeparated := hsep
    interior_isOpen := by
      intro e
      obtain ⟨i, rfl⟩ := q.surjective e
      change IsOpen (G.carrier ↓∩ (q i).interior)
      rw [(hq i).1]
      exact G.splitInterior_isOpen i
    boundary_isPair := by
      intro e
      obtain ⟨i, rfl⟩ := q.surjective e
      refine ⟨G.splitSource i, G.splitTarget i, (hq i).2.2, ?_⟩
      change IsPrimitiveLink (q i).range (G.splitSource i).1 (G.splitTarget i).1
      rw [(hq i).2.1]
      exact IsPrimitiveLink.of_injective (G.splitPath_injective i) }
  refine ⟨H, ⟨rfl, subset_union_left⟩, rfl, ⟨q⟩, ?_⟩
  intro e
  obtain ⟨i, rfl⟩ := q.surjective e
  exact ⟨G.splitSource i, G.splitTarget i, G.splitPath i,
    G.splitPath_injective i, (hq i).2.1.symm, (hq i).2.2⟩

/-- Refining finitely many edge pieces adds finitely many vertices and retains finitely many
edge pieces, with injective parametrizations at their boundary vertices. -/
theorem exists_finer_with_injective_edges [_root_.Finite (G.edge)] :
    ∃ (H : GraphLike X), G.finer H ∧ (H.vertexSet ∆ G.vertexSet).Finite ∧
      _root_.Finite (H.edge) ∧
      ∀ e : H.edge,
        ∃ (x y : H.vertexSet) (P : Path x.1 y.1),
          Injective P ∧ range P = e.range ∧ e.boundary = {x.1, y.1} := by
  have hsep : IsTotallySeparated (G.carrier ↓∩ G.splitVertexSet) := by
    rw [splitVertexSet, preimage_union]
    refine isTotallySeparated_union_finite_of_closed_neighborhoods G.isTotallySeparated
      ((finite_range (fun e : G.edge ↦ G.edgePath e half)).preimage
        Subtype.val_injective.injOn) ?_
    intro m hm
    exact G.exists_splitMidpoint_neighborhood m hm
  obtain ⟨H, hGH, hV, ⟨q⟩, hpaths⟩ := G.exists_graphLike_split_of_separated hsep
  refine ⟨H, hGH, ?_, _root_.Finite.of_equiv _ q, hpaths⟩
  apply (finite_range (fun e : G.edge ↦ G.edgePath e half)).subset
  rintro z (⟨hzH, hzG⟩ | ⟨hzG, hzH⟩)
  · have hz : z ∈ G.splitVertexSet := hV ▸ hzH
    exact hz.resolve_left hzG
  · exact (hzH (hGH.vertices_subset hzG)).elim

/-- With finitely many edge pieces, there is a refinement with injective edge parametrizations.
The vertex set need not be finite. -/
theorem exists_graphLike_edgePiece_inj [_root_.Finite (G.edge)] :
    ∃ (H : GraphLike X), G.finer H ∧
      ∀ e : H.edge,
        ∃ (x y : X) (P : Path x y), Injective P ∧ range P = e.range := by
  obtain ⟨H, hGH, _, _, hpaths⟩ := G.exists_finer_with_injective_edges
  refine ⟨H, hGH, fun e ↦ ?_⟩
  obtain ⟨x, y, P, hP, hrange, _⟩ := hpaths e
  exact ⟨x.1, y.1, P, hP, hrange⟩

end GraphLike

end GeneralSubdivision

namespace GraphLike

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Polygonality depends only on the edge ranges, independently of their parametrizations. -/
theorem isPolygonal_iff_isSegmentFigure (G : GraphLike W) :
    G.IsPolygonal ↔ ∀ e : G.edge, IsSegmentFigure e.range := by
  constructor
  · intro h e
    obtain ⟨x, y, hb, -⟩ := G.boundary_isPair e
    obtain ⟨P, -, hP⟩ := h hb
    exact hP ▸ P.isSegmentFigure_toSet
  · intro h e x y he
    obtain ⟨a, b, hb, hlink⟩ := G.boundary_isPair e
    have hp := pair_eq_pair_iff.mp (hb.symm.trans he)
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hlink.exists_polygonalPath (h e)
    · exact hlink.symm.exists_polygonalPath (h e)

/-- Replace every edge in a prescribed open neighborhood, preserving the vertices and
edge boundaries, including those of loops. -/
theorem exists_polygonalization (G : GraphLike W) [G.Finite]
    (U : G.edge → Set W) (hU : ∀ e, IsOpen (U e)) (hGU : ∀ e, e.range ⊆ U e) :
    ∃ (H : GraphLike W) (e : G.edge ≃ H.edge),
      H.vertexSet = G.vertexSet ∧ H.IsPolygonal ∧
        ∀ f, (e f).boundary = f.boundary ∧ (e f).range ⊆ U f := by
  obtain ⟨L, hL, hpoly, hV, hLL, hLU⟩ := exists_polygonal_primitiveLink_family
    G.edgeLink (fun e ↦ by rw [← e.boundary_eq_inter_vertexSet, G.edgeBoundary])
    (fun i j hij ↦ i.range_inter_subset_vertexSet hij) U hU hGU
  obtain ⟨H, e, -, hvertices, he⟩ := exists_graphLike_of_finite_links G.vertexSet
    Finite.vertexSet_finite G.edgeSource G.edgeTarget L hL hV
    (fun i j hij ↦ disjoint_left.mpr fun w hi hj ↦ hi.2 (hLL hij ⟨hi.1, hj.1⟩))
  refine ⟨H, e, hvertices, ?_, fun f ↦ ⟨(he f).2.2.trans (G.edgeBoundary f).symm,
    (he f).2.1 ▸ hLU f⟩⟩
  apply H.isPolygonal_iff_isSegmentFigure.mpr
  intro f
  obtain ⟨i, rfl⟩ := e.surjective f
  exact (he i).2.1 ▸ hpoly i

open Classical in
private noncomputable def positiveTolerance (ε : ℝ) : ℝ := if 0 < ε then ε else 1

private lemma positiveTolerance_pos (ε : ℝ) : 0 < positiveTolerance ε := by
  unfold positiveTolerance
  split_ifs with h
  · exact h
  · exact zero_lt_one

private noncomputable def polygonalize_aux (G : GraphLike W) [G.Finite] (ε : ℝ) :
    Σ H : GraphLike W, G.edge ≃
      H.edge :=
  let h := G.exists_polygonalization (fun e ↦ thickening (positiveTolerance ε) e.range)
    (fun _ ↦ isOpen_thickening) (fun _ ↦ self_subset_thickening (positiveTolerance_pos ε) _)
  ⟨h.choose, h.choose_spec.choose⟩

/-- Replace the edges by polygonal paths while preserving vertices and incidence.
For positive `ε`, each new edge lies in the `ε`-thickening of the original edge.
For nonpositive `ε`, the construction uses tolerance `1`. -/
noncomputable def polygonalize (G : GraphLike W) [G.Finite] (ε : ℝ) : GraphLike W :=
  (polygonalize_aux G ε).1

noncomputable def polygonalizeEdgeEquiv (T : GraphLike W) [T.Finite] (ε : ℝ) :
    T.edge ≃
      (T.polygonalize ε).edge :=
  (T.polygonalize_aux ε).2

theorem polygonalize_spec (T : GraphLike W) [T.Finite] (ε : ℝ) :
    (T.polygonalize ε).vertexSet = T.vertexSet ∧
    (T.polygonalize ε).IsPolygonal ∧
      ∀ e, (polygonalizeEdgeEquiv T ε e).boundary = e.boundary ∧
        (0 < ε → (polygonalizeEdgeEquiv T ε e).range ⊆ thickening ε e.range) := by
  have h := (T.exists_polygonalization (fun e ↦ thickening (positiveTolerance ε) e.range)
    (fun _ ↦ isOpen_thickening)
    (fun _ ↦ self_subset_thickening (positiveTolerance_pos ε) _)).choose_spec.choose_spec
  refine ⟨h.1, h.2.1, fun e ↦ ⟨(h.2.2 e).1, fun hε ↦ ?_⟩⟩
  refine (h.2.2 e).2.trans ?_
  rw [positiveTolerance, ite_eq_left hε]

@[simp]
lemma polygonalize_vertexSet (G : GraphLike W) [G.Finite] (ε : ℝ) :
    (G.polygonalize ε).vertexSet = G.vertexSet :=
  (G.polygonalize_spec ε).1

lemma polygonalize_isPolygonal (G : GraphLike W) [G.Finite] (ε : ℝ) :
    (G.polygonalize ε).IsPolygonal :=
  (G.polygonalize_spec ε).2.1

@[simp]
lemma polygonalizeEdgeEquiv_boundary (G : GraphLike W) [G.Finite] (ε : ℝ)
    (e : G.edge) :
    (G.polygonalizeEdgeEquiv ε e).boundary = e.boundary :=
  ((G.polygonalize_spec ε).2.2 e).1

lemma polygonalizeEdgeEquiv_range_subset (G : GraphLike W) [G.Finite] {ε : ℝ}
    (hε : 0 < ε) (e : G.edge) :
    (G.polygonalizeEdgeEquiv ε e).range ⊆ thickening ε e.range :=
  ((G.polygonalize_spec ε).2.2 e).2 hε

instance polygonalize_finite (G : GraphLike W) [G.Finite] (ε : ℝ) :
    (G.polygonalize ε).Finite where
  vertexSet_finite := G.polygonalize_vertexSet ε ▸ Finite.vertexSet_finite (G := G)
  edge_finite := _root_.Finite.of_equiv _ (G.polygonalizeEdgeEquiv ε)

/-- Polygonalization preserves the abstract graph, with each vertex fixed in the ambient space. -/
noncomputable def polygonalizeIso (G : GraphLike W) [G.Finite] (ε : ℝ) :
    Graph.Iso G.toGraph (G.polygonalize ε).toGraph :=
  Graph.Iso.ofEquivs (Set.equivOfEq (G.polygonalize_vertexSet ε).symm)
    (((Equiv.Set.univ _).trans (G.polygonalizeEdgeEquiv ε)).trans (Equiv.Set.univ _).symm)
    (by
      intro e u v h
      change (G.polygonalizeEdgeEquiv ε e.1).boundary = {u.1, v.1}
      rwa [G.polygonalizeEdgeEquiv_boundary])

@[simp]
lemma polygonalizeIso_vertex (G : GraphLike W) [G.Finite] (ε : ℝ)
    (v : V(G.toGraph)) : ((G.polygonalizeIso ε).vertEquiv v).1 = v.1 := rfl

@[simp]
lemma polygonalizeIso_edge (G : GraphLike W) [G.Finite] (ε : ℝ)
    (e : E(G.toGraph)) :
    ((G.polygonalizeIso ε).edgeEquiv e).1 = G.polygonalizeEdgeEquiv ε e.1 := rfl

end GraphLike

section PolygonalCarrierInvarianceCompletion

private lemma polygonal_path_of_finite_vertex_hits [AddCommGroup X] [Module ℝ X]
    [ContinuousSMul ℝ X] [ContinuousAdd X] (G : GraphLike X) (hG : G.IsPolygonal)
    {x y : X} (γ : Path x y) (hinj : Injective γ) (hcarrier : range γ ⊆ G.carrier)
    (hfin : (γ ⁻¹' G.vertexSet).Finite) :
    ∃ Q : PolygonalPath x y, Q.toPath.IsPrimitive ∧ Q.toSet = range γ := by
  classical
  obtain ⟨Q, hQ⟩ := γ.exists_polygonalPath_of_finite_cuts hfin (by
    intro s t hst hcut
    obtain ⟨e, _, he⟩ := exists_edgePiece_of_no_vertex_crossing G γ hcarrier hst (by
      intro u hu hγu
      exact hcut u hu hγu)
    obtain ⟨a, b, hab, _⟩ := G.boundary_isPair e
    obtain ⟨P, hP, hPset⟩ := hG hab
    have : T2Space P.toSet := (IsEmbedding.inclusion (show P.toSet ⊆ G.carrier by
      rw [hPset]
      exact e.range_subset)).t2Space
    exact P.exists_polygonalPath_of_injective hP (γ.subpath s t)
      (Path.injective_subpath hinj hst.ne) (hPset ▸ he))
  have : T2Space ↥(range γ) := (IsEmbedding.inclusion hcarrier).t2Space
  exact Path.exists_primitive_polygonalPath_of_toSet_subset hinj Q hQ.subset

/-- Polygonality passes to a graph-like subspace if each edge meets only finitely many
vertices of the original graph-like space. -/
theorem GraphLike.IsPolygonal.of_carrier_subset {G H : GraphLike X} [AddCommGroup X]
    [Module ℝ X] [ContinuousSMul ℝ X] [ContinuousAdd X] (hG : G.IsPolygonal)
    (hH : H.carrier ⊆ G.carrier)
    (hfinite : ∀ e : H.edge, (e.range ∩ G.vertexSet).Finite) :
    H.IsPolygonal := by
  intro e x y hends
  have hlink : IsPrimitiveLink e.range x y := by
    obtain ⟨a, b, hab, hlink⟩ := H.boundary_isPair e
    rcases pair_eq_pair_iff.mp (hab.symm.trans hends) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hlink
    · exact hlink.symm
  obtain ⟨γ, hγ, hrange⟩ := hlink
  have hfirst : range γ.firstHalf ⊆ e.range := by
    rw [← hrange, ← γ.firstHalf_range_union_secondHalf_range]
    exact subset_union_left
  have hsecond : range γ.secondHalf ⊆ e.range := by
    rw [← hrange, ← γ.firstHalf_range_union_secondHalf_range]
    exact subset_union_right
  have hcut {u v : X} (δ : Path u v) (hinj : Injective δ) (hsub : range δ ⊆ e.range) :
      (δ ⁻¹' G.vertexSet).Finite :=
    ((hfinite e).preimage hinj.injOn).subset
      (fun t ht ↦ ⟨hsub (mem_range_self t), ht⟩)
  have heG : e.range ⊆ G.carrier := e.range_subset.trans hH
  obtain ⟨A, hA, hAset⟩ := polygonal_path_of_finite_vertex_hits G hG γ.firstHalf
    hγ.injective_firstHalf (hfirst.trans heG) (hcut _ hγ.injective_firstHalf hfirst)
  obtain ⟨B, hB, hBset⟩ := polygonal_path_of_finite_vertex_hits G hG γ.secondHalf
    hγ.injective_secondHalf (hsecond.trans heG) (hcut _ hγ.injective_secondHalf hsecond)
  refine ⟨A.append B, ?_, ?_⟩
  · apply (PolygonalPath.isPrimitive_append_iff hγ.half_ne_source.symm).2
    refine ⟨(PolygonalPath.isPrimitive_iff_isSimple hγ.half_ne_source.symm).mp hA,
      (PolygonalPath.isPrimitive_iff_isSimple hγ.half_ne_target).mp hB, ?_⟩
    rw [hAset, hBset, hγ.firstHalf_range_inter_secondHalf_range]
    rintro z (rfl | ⟨rfl, hxy⟩)
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
    · exact ⟨Or.inl rfl, Or.inr hxy⟩
  · rw [PolygonalPath.toSet_append, hAset, hBset,
      γ.firstHalf_range_union_secondHalf_range, hrange]

/-- It suffices that the subspace omits only finitely many original vertices within its carrier. -/
theorem GraphLike.IsPolygonal.of_finite_vertexSet_diff {G H : GraphLike X} [AddCommGroup X]
    [Module ℝ X] [ContinuousSMul ℝ X] [ContinuousAdd X] (hG : G.IsPolygonal)
    (hH : H.carrier ⊆ G.carrier)
    (hfinite : ((H.carrier ∩ G.vertexSet) \ H.vertexSet).Finite) : H.IsPolygonal :=
  hG.of_carrier_subset hH (finite_edge_inter_other_vertices G H hfinite)

theorem GraphLike.isPolygonal_of_carrier_eq {G H : GraphLike X} [AddCommGroup X]
    [Module ℝ X] [ContinuousSMul ℝ X] [ContinuousAdd X] (hG : G.IsPolygonal)
    (hH : G.carrier = H.carrier) (hH' : (H.vertexSet ∆ G.vertexSet).Finite) :
    H.IsPolygonal :=
  hG.of_finite_vertexSet_diff hH.symm.subset
    (hH'.subset (fun _ hx ↦ Or.inr ⟨hx.1.2, hx.2⟩))

end PolygonalCarrierInvarianceCompletion

section DrawingCompletion

variable {V E W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable abbrev drawingPolygonalize (D : Graph.Drawing V E W) [D.graph.Finite]
    (ε : ℝ) : Graph.Drawing V E W :=
  { toGraphLike := D.toGraphLike.polygonalize ε
    graph := D.graph
    iso := D.iso.comp (D.toGraphLike.polygonalizeIso ε) }

@[simp]
lemma drawingPolygonalize_graph (D : Graph.Drawing V E W) [D.graph.Finite] (ε : ℝ) :
    (drawingPolygonalize D ε).graph = D.graph := rfl

@[simp]
lemma drawingPolygonalize_vertex (D : Graph.Drawing V E W) [D.graph.Finite] (ε : ℝ) :
    (drawingPolygonalize D ε).vertex = D.vertex := rfl

lemma drawingPolygonalize_isPolygonal (D : Graph.Drawing V E W) [D.graph.Finite] (ε : ℝ) :
    (drawingPolygonalize D ε).IsPolygonal := D.toGraphLike.polygonalize_isPolygonal ε

lemma drawingPolygonalize_edgeRange_subset (D : Graph.Drawing V E W) [D.graph.Finite]
    {ε : ℝ} (hε : 0 < ε) (e : E(D.graph)) :
    (drawingPolygonalize D ε).edgeRange e ⊆ thickening ε (D.edgeRange e) :=
  D.toGraphLike.polygonalizeEdgeEquiv_range_subset hε (D.edge e)

theorem drawingPolygonalize_spec (D : Graph.Drawing V E W) [D.graph.Finite]
    (ε : ℝ) :
    (drawingPolygonalize D ε).graph = D.graph ∧ (drawingPolygonalize D ε).IsPolygonal ∧
      (∀ v, (drawingPolygonalize D ε).vertex v = D.vertex v) ∧
      ∀ e, 0 < ε → (drawingPolygonalize D ε).edgeRange e ⊆ thickening ε (D.edgeRange e) :=
  ⟨rfl, drawingPolygonalize_isPolygonal D ε, fun _ ↦ rfl,
    fun e hε ↦ drawingPolygonalize_edgeRange_subset D hε e⟩

theorem Graph.isDrawable_iff_isPolygonallyDrawable (G : Graph V E) [G.Finite] :
    G.IsDrawable W ↔ G.IsPolygonallyDrawable W := by
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨drawingPolygonalize D 1, rfl, drawingPolygonalize_isPolygonal D 1⟩
  · rintro ⟨D, hD, _⟩
    exact ⟨D, hD⟩

theorem planar_iff_isPolygonallyDrawable (G : Graph V E) [G.Finite] :
    G.Planar ↔ G.IsPolygonallyDrawable ℂ :=
  G.isDrawable_iff_isPolygonallyDrawable

end DrawingCompletion

/-
The sketch's unrestricted `exists_graphLike_edgePiece_inj` is false with these
`GraphLike` axioms. The following counterexample is mathematical, not formalized.

Fix a free ultrafilter ℱ on ℕ. Let D be the linearly ordered ultrapower
`(0,1)^ℕ / ℱ`. For each f ∈ D introduce two vertices f⁻ < f⁺.
Let Z consist of these vertices and one additional vertex p. The remaining
points are (n,t), where n ∈ ℕ and 0 < t < 1; these form loops based at p.

Give each loop interior its usual open subsets. Add these open generators:
choose a < b in D, representatives α, β, and A ∈ ℱ with αₙ < βₙ on A.
Let C be the vertex interval [a⁺, b⁻], excluding p. The two generators have
vertex traces C and Z \ C, respectively, and loop-interior traces:
* on n ∈ A: (αₙ, βₙ) and (0, αₙ) ∪ (βₙ, 1);
* on n ∉ A: ∅ and (0,1).
Use every such choice of representatives and A.

These generators are disjoint and cover Z. Their cuts separate any two
vertices of Z, including f⁻ and f⁺, so Z is ambiently totally separated.
The space is Hausdorff: distinct vertices have these separators; a fixed
loop can be omitted from A to separate its interior from a vertex other
than p. To separate p from an interior point, change α and β at that
coordinate so the point lies between them, and include the coordinate in A.
Finite changes preserve the germs and membership in the free ultrafilter.

Each loop map [0,1] → S, identifying both endpoints with p, is continuous:
generator preimages are open intervals, endpoint neighborhoods, ∅, or [0,1].
Z is closed, and the components of S \ Z are exactly the open loop interiors.
Each has closure equal to its interior together with p; other vertices have
neighborhoods omitting that loop. Thus S with vertex set Z satisfies GraphLike.

Every neighborhood of f⁻ contains intervals immediately to the left of fₙ
on ℱ-many loops; every neighborhood of f⁺ contains right intervals there.
This holds for generators and is preserved under finite intersections.

Suppose a finer GraphLike on the same carrier has injectively parametrized
edge ranges. Its vertex set must meet every loop interior: otherwise that
whole loop remains an edge whose range is a circle, not an injective interval
image. Choose an added vertex (n,qₙ) on each loop and let f = [qₙ] ∈ D.
Disjoint open separators of f⁻ and f⁺ covering the enlarged vertex set contain
opposing left and right intervals at qₙ on ℱ-many loops. For any such n,
(n,qₙ) cannot belong to either separator: openness in its loop would force
intersection with the other separator. This contradicts coverage.
-/

section GraphLikeOrder

/-! ## Order and finite refinements

The carrier-and-vertex inclusion order has an empty bottom element. On a fixed carrier it
agrees with `finer`. For finite `G`, `G.FiniteRefinement` is a locally finite generalized Boolean
algebra and a conditionally complete lattice, ordered like finite sets of additional vertices.
Its binary bounds are also bounds in the full graph-like order. If `G` has an edge, this
refinement order has no maximal element.
-/

open unitInterval

namespace GraphLike

@[simp]
lemma le_iff {G H : GraphLike X} :
    G ≤ H ↔ G.carrier ⊆ H.carrier ∧ G.vertexSet ⊆ H.vertexSet := Iff.rfl

instance : OrderBot (GraphLike X) where
  bot := {
    carrier := ∅
    vertexSet := ∅
    t2Space := inferInstance
    subset := Subset.rfl
    isClosed := by simp
    isTotallySeparated := by simpa using (isTotallySeparated_empty (α := (∅ : Set X)))
    interior_isOpen := by
      intro e
      obtain ⟨x, _⟩ := ConnectedComponents.surjective_coe e
      exact x.2.1.elim
    boundary_isPair := by
      intro e
      obtain ⟨x, _⟩ := ConnectedComponents.surjective_coe e
      exact x.2.1.elim }
  bot_le _ := ⟨empty_subset _, empty_subset _⟩

@[simp] lemma bot_carrier : (⊥ : GraphLike X).carrier = ∅ := rfl
@[simp] lemma bot_vertexSet : (⊥ : GraphLike X).vertexSet = ∅ := rfl

@[simp]
lemma carrier_eq_empty_iff {G : GraphLike X} : G.carrier = ∅ ↔ G = ⊥ := by
  refine ⟨fun h ↦ ext h (subset_empty_iff.mp (h ▸ G.subset)), ?_⟩
  rintro rfl
  rfl

@[simp]
lemma vertexSet_eq_empty_iff {G : GraphLike X} : G.vertexSet = ∅ ↔ G = ⊥ := by
  refine ⟨fun h ↦ carrier_eq_empty_iff.mp ?_, ?_⟩
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    let e : G.edge := ConnectedComponents.mk ⟨x, hx, by simp [h]⟩
    obtain ⟨a, _, _⟩ := G.boundary_isPair e
    simpa [h] using a.2
  · rintro rfl
    rfl

lemma finer.le {G H : GraphLike X} (h : G.finer H) : G ≤ H :=
  ⟨h.carrier_eq.subset, h.vertices_subset⟩

lemma finer_iff_le_and_carrier_eq {G H : GraphLike X} :
    G.finer H ↔ G ≤ H ∧ G.carrier = H.carrier :=
  ⟨fun h ↦ ⟨h.le, h.carrier_eq⟩, fun h ↦ ⟨h.2, h.1.2⟩⟩

@[refl] lemma finer.refl (G : GraphLike X) : G.finer G := ⟨rfl, Subset.rfl⟩

@[trans]
lemma finer.trans {G H K : GraphLike X} (hGH : G.finer H) (hHK : H.finer K) : G.finer K :=
  ⟨hGH.carrier_eq.trans hHK.carrier_eq, hGH.vertices_subset.trans hHK.vertices_subset⟩

lemma finer.antisymm {G H : GraphLike X} (hGH : G.finer H) (hHG : H.finer G) :
    G = H := le_antisymm hGH.le hHG.le

lemma finer_iff_le_of_carrier_eq {G H : GraphLike X} (h : G.carrier = H.carrier) :
    G.finer H ↔ G ≤ H := by
  rw [finer_iff_le_and_carrier_eq, and_iff_left h]

end GraphLike

private def parameterGaps (F : Set I) :=
  {st : I × I // st.1 ∈ F ∧ st.2 ∈ F ∧ st.1 < st.2 ∧ Disjoint (Ioo st.1 st.2) F}

private lemma parameterGaps_finite {F : Set I} (hF : F.Finite) :
    Finite (parameterGaps F) :=
  ((hF.prod hF).subset fun _ h ↦ ⟨h.1, h.2.1⟩).to_subtype

private lemma exists_parameterGap {F : Set I} (hF : F.Finite) (h0 : 0 ∈ F) (h1 : 1 ∈ F)
    {u : I} (hu : u ∉ F) : ∃ g : parameterGaps F, u ∈ Ioo g.1.1 g.1.2 := by
  let A := F ∩ Iic u
  let B := F ∩ Ici u
  have hA : sSup A ∈ A :=
    ((hF.inter_of_left _).isClosed).sSup_mem ⟨0, h0, show (0 : I) ≤ u from bot_le⟩
  have hB : sInf B ∈ B :=
    ((hF.inter_of_left _).isClosed).sInf_mem ⟨1, h1, show u ≤ (1 : I) from le_top⟩
  have ha : sSup A < u := lt_of_le_of_ne hA.2 (fun h ↦ hu (h ▸ hA.1))
  have hb : u < sInf B := lt_of_le_of_ne hB.2 (fun h ↦ hu (h.symm ▸ hB.1))
  refine ⟨⟨(sSup A, sInf B), hA.1, hB.1, ha.trans hb, ?_⟩, ha, hb⟩
  apply disjoint_left.mpr
  intro t ht htF
  rcases le_total t u with htu | hut
  · exact ht.1.not_ge (le_sSup (show t ∈ A from ⟨htF, htu⟩))
  · exact ht.2.not_ge (sInf_le (show t ∈ B from ⟨htF, hut⟩))

private lemma parameterGap_eq_of_mem {F : Set I} {g h : parameterGaps F} {u : I}
    (hg : u ∈ Ioo g.1.1 g.1.2) (hh : u ∈ Ioo h.1.1 h.1.2) : g = h := by
  have hleft : g.1.1 = h.1.1 := by
    apply le_antisymm
    · by_contra hn
      exact (disjoint_left.mp h.2.2.2.2) ⟨lt_of_not_ge hn, hg.1.trans hh.2⟩ g.2.1
    · by_contra hn
      exact (disjoint_left.mp g.2.2.2.2) ⟨lt_of_not_ge hn, hh.1.trans hg.2⟩ h.2.1
  have hright : g.1.2 = h.1.2 := by
    apply le_antisymm
    · by_contra hn
      exact (disjoint_left.mp g.2.2.2.2) ⟨hg.1.trans hh.2, lt_of_not_ge hn⟩ h.2.2.1
    · by_contra hn
      exact (disjoint_left.mp h.2.2.2.2) ⟨hh.1.trans hg.2, lt_of_not_ge hn⟩ g.2.2.1
  exact Subtype.ext (Prod.ext hleft hright)

namespace GraphLike

/-- A finite vertex superset subdivides a finite graph-like space without changing its carrier. -/
private theorem exists_finite_refinement (G : GraphLike X) [G.Finite]
    (Z : Set X) (hZ : Z.Finite) (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) :
    ∃ H : GraphLike X, H.carrier = G.carrier ∧ H.vertexSet = Z ∧ H.Finite := by
  classical
  let C (e : G.edge) := G.edgePath e ⁻¹' Z
  have hC (e : G.edge) : (C e).Finite := (G.edgePath_isPrimitive e).finite_preimage hZ
  have h0 (e : G.edge) : 0 ∈ C e := by
    change G.edgePath e 0 ∈ Z
    simpa using hGZ (G.edgeSource e).2
  have h1 (e : G.edge) : 1 ∈ C e := by
    change G.edgePath e 1 ∈ Z
    simpa using hGZ (G.edgeTarget e).2
  let ι := (e : G.edge) × parameterGaps (C e)
  let (e : G.edge) : _root_.Finite (parameterGaps (C e)) := parameterGaps_finite (hC e)
  let a (i : ι) : Z := ⟨G.edgePath i.1 i.2.1.1, i.2.2.1⟩
  let b (i : ι) : Z := ⟨G.edgePath i.1 i.2.1.2, i.2.2.2.1⟩
  let P (i : ι) : Path (a i).1 (b i).1 := (G.edgePath i.1).subpath i.2.1.1 i.2.1.2
  have hrange (i : ι) : range (P i) = G.edgePath i.1 '' Icc i.2.1.1 i.2.1.2 :=
    (G.edgePath i.1).range_subpath_of_le _ _ i.2.2.2.2.1.le
  have hsub (i : ι) : range (P i) ⊆ i.1.range := by
    rw [hrange, ← G.range_edgePath]
    exact image_subset_range _ _
  have hlink (i : ι) : IsPrimitiveLink (range (P i)) (a i).1 (b i).1 :=
    ((G.edgePath_isPrimitive i.1).subpath i.2.2.2.2.1.ne).isPrimitiveLink
  have hvertices (i : ι) : range (P i) ∩ Z = {(a i).1, (b i).1} := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxZ⟩
      rw [hrange] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hu with rfl | rfl | hu
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact ((disjoint_left.mp i.2.2.2.2.2) hu hxZ).elim
    · rintro x (rfl | rfl)
      · exact ⟨(P i).source_mem_range, (a i).2⟩
      · exact ⟨(P i).target_mem_range, (b i).2⟩
  have hdisj : Pairwise fun i j : ι ↦ Disjoint (range (P i) \ Z) (range (P j) \ Z) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hi hj
    have hiE : x ∈ i.1.interior := by
      rw [← i.1.range_diff_vertexSet]
      exact ⟨hsub i hi.1, fun h ↦ hi.2 (hGZ h)⟩
    have hjE : x ∈ j.1.interior := by
      rw [← j.1.range_diff_vertexSet]
      exact ⟨hsub j hj.1, fun h ↦ hj.2 (hGZ h)⟩
    have hef : i.1 = j.1 := by
      by_contra h
      exact (i.1.interior_disjoint h).notMem_of_mem_left hiE hjE
    rcases i with ⟨e, g⟩
    rcases j with ⟨f, k⟩
    dsimp only at hef
    subst f
    obtain ⟨u, hu, hux⟩ := (hrange ⟨e, g⟩).subset hi.1
    obtain ⟨v, hv, hvx⟩ := (hrange ⟨e, k⟩).subset hj.1
    have huC : u ∉ C e := fun h ↦ hi.2 (hux ▸ h)
    have hvC : v ∉ C e := fun h ↦ hj.2 (hvx ▸ h)
    have huI : u ∈ Ioo (0 : I) 1 :=
      ⟨lt_of_le_of_ne u.2.1 (fun h ↦ huC (h ▸ h0 e)),
        lt_of_le_of_ne u.2.2 (fun h ↦ huC (h.symm ▸ h1 e))⟩
    have hvI : v ∈ Ioo (0 : I) 1 :=
      ⟨lt_of_le_of_ne v.2.1 (fun h ↦ hvC (h ▸ h0 e)),
        lt_of_le_of_ne v.2.2 (fun h ↦ hvC (h.symm ▸ h1 e))⟩
    have huv : u = v := (G.edgePath_isPrimitive e).injOn_Ioo huI hvI (hux.trans hvx.symm)
    subst v
    have hug : u ∈ Ioo g.1.1 g.1.2 :=
      ⟨lt_of_le_of_ne hu.1 (fun h ↦ huC (h ▸ g.2.1)),
        lt_of_le_of_ne hu.2 (fun h ↦ huC (h.symm ▸ g.2.2.1))⟩
    have huk : u ∈ Ioo k.1.1 k.1.2 :=
      ⟨lt_of_le_of_ne hv.1 (fun h ↦ huC (h ▸ k.2.1)),
        lt_of_le_of_ne hv.2 (fun h ↦ huC (h.symm ▸ k.2.2.1))⟩
    exact hij (by cases parameterGap_eq_of_mem hug huk; rfl)
  have hcarrier : Z ∪ ⋃ i, range (P i) = G.carrier := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact hZG hx
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact i.1.range_subset (hsub i hi)
    · intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inl hxZ
      have hxG : x ∉ G.vertexSet := fun h ↦ hxZ (hGZ h)
      obtain ⟨e, he⟩ := mem_iUnion.mp ((G.carrier_eq_vertexSet_union_ranges ▸ hx).resolve_left hxG)
      obtain ⟨u, rfl⟩ := (G.range_edgePath e).symm ▸ he
      obtain ⟨g, hg⟩ := exists_parameterGap (hC e) (h0 e) (h1 e) hxZ
      exact Or.inr (mem_iUnion.mpr ⟨⟨e, g⟩, (hrange ⟨e, g⟩).symm ▸
        mem_image_of_mem _ ⟨hg.1.le, hg.2.le⟩⟩)
  have : T2Space ↥(Z ∪ ⋃ i, range (P i)) := hcarrier.symm ▸ G.t2Space
  obtain ⟨H, e, hS, hV, _⟩ := exists_graphLike_of_finite_links Z hZ a b
    (fun i ↦ range (P i)) hlink hvertices hdisj
  exact ⟨H, hS.trans hcarrier, hV, hV ▸ hZ, _root_.Finite.of_equiv ι e⟩

/-- Subdivide at the prescribed finite vertex set, retaining the carrier. -/
noncomputable def refineVertices (G : GraphLike X) [G.Finite]
    (Z : Set X) (hZ : Z.Finite) (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) : GraphLike X :=
  (exists_finite_refinement G Z hZ hGZ hZG).choose

@[simp]
lemma refineVertices_carrier (G : GraphLike X) [G.Finite]
    (Z : Set X) (hZ : Z.Finite) (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) :
    (G.refineVertices Z hZ hGZ hZG).carrier = G.carrier :=
  (exists_finite_refinement G Z hZ hGZ hZG).choose_spec.1

@[simp]
lemma refineVertices_vertexSet (G : GraphLike X) [G.Finite]
    (Z : Set X) (hZ : Z.Finite) (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) :
    (G.refineVertices Z hZ hGZ hZG).vertexSet = Z :=
  (exists_finite_refinement G Z hZ hGZ hZG).choose_spec.2.1

instance refineVertices_finite (G : GraphLike X) [G.Finite]
    (Z : Set X) (hZ : Z.Finite) (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) :
    (G.refineVertices Z hZ hGZ hZG).Finite :=
  (exists_finite_refinement G Z hZ hGZ hZG).choose_spec.2.2

lemma finer_refineVertices (G : GraphLike X) [G.Finite]
    (Z : Set X) (hZ : Z.Finite) (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) :
    G.finer (G.refineVertices Z hZ hGZ hZG) :=
  ⟨(G.refineVertices_carrier Z hZ hGZ hZG).symm, by simpa using hGZ⟩

/-- Refinements of `G` with finitely many vertices, ordered by vertex inclusion.
For finite `G`, these are precisely its subdivisions at finitely many additional points. -/
def FiniteRefinement (G : GraphLike X) :=
  {H : GraphLike X // G.finer H ∧ H.vertexSet.Finite}

namespace FiniteRefinement

variable {G : GraphLike X}

instance : PartialOrder G.FiniteRefinement :=
  inferInstanceAs (PartialOrder {H : GraphLike X // G.finer H ∧ H.vertexSet.Finite})

@[simp]
lemma carrier_eq (H : G.FiniteRefinement) : H.1.carrier = G.carrier := H.2.1.carrier_eq.symm

lemma vertices_subset (H : G.FiniteRefinement) : G.vertexSet ⊆ H.1.vertexSet :=
  H.2.1.vertices_subset

@[ext]
lemma ext {H K : G.FiniteRefinement} (h : H.1.vertexSet = K.1.vertexSet) : H = K :=
  Subtype.ext (GraphLike.ext (H.carrier_eq.trans K.carrier_eq.symm) h)

@[simp]
lemma le_iff {H K : G.FiniteRefinement} : H ≤ K ↔ H.1.vertexSet ⊆ K.1.vertexSet := by
  change H.1.carrier ⊆ K.1.carrier ∧ H.1.vertexSet ⊆ K.1.vertexSet ↔ _
  rw [H.carrier_eq, K.carrier_eq, and_iff_right Subset.rfl]

lemma le_iff_finer {H K : G.FiniteRefinement} : H ≤ K ↔ H.1.finer K.1 :=
  (finer_iff_le_of_carrier_eq (H.carrier_eq.trans K.carrier_eq.symm)).symm

/-- The additional vertices determine a refinement uniquely. -/
def addedVertices (H : G.FiniteRefinement) : Set X := H.1.vertexSet \ G.vertexSet

lemma addedVertices_le_iff {H K : G.FiniteRefinement} :
    H.addedVertices ⊆ K.addedVertices ↔ H ≤ K := by
  rw [le_iff]
  constructor
  · intro h x hx
    by_cases hxG : x ∈ G.vertexSet
    · exact K.vertices_subset hxG
    · exact (h ⟨hx, hxG⟩).1
  · intro h x hx
    exact ⟨h hx.1, hx.2⟩

lemma addedVertices_injective : Injective (addedVertices (G := G)) := by
  intro H K h
  exact le_antisymm (addedVertices_le_iff.mp h.subset) (addedVertices_le_iff.mp h.symm.subset)

variable [G.Finite]

/-- Construct a refinement from its full finite vertex set. -/
noncomputable def ofVertexSet (Z : Set X) (hZ : Z.Finite)
    (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) : G.FiniteRefinement :=
  ⟨G.refineVertices Z hZ hGZ hZG, G.finer_refineVertices Z hZ hGZ hZG,
    by simpa using hZ⟩

@[simp]
lemma ofVertexSet_vertexSet (Z : Set X) (hZ : Z.Finite)
    (hGZ : G.vertexSet ⊆ Z) (hZG : Z ⊆ G.carrier) :
    (ofVertexSet Z hZ hGZ hZG).1.vertexSet = Z :=
  G.refineVertices_vertexSet Z hZ hGZ hZG

noncomputable instance : Max G.FiniteRefinement where
  max H K := ofVertexSet (H.1.vertexSet ∪ K.1.vertexSet) (H.2.2.union K.2.2)
    (H.vertices_subset.trans subset_union_left)
    (union_subset (H.1.subset.trans H.carrier_eq.subset) (K.1.subset.trans K.carrier_eq.subset))

noncomputable instance : Min G.FiniteRefinement where
  min H K := ofVertexSet (H.1.vertexSet ∩ K.1.vertexSet) (H.2.2.inter_of_left _)
    (subset_inter H.vertices_subset K.vertices_subset)
    (inter_subset_left.trans (H.1.subset.trans H.carrier_eq.subset))

instance : Bot G.FiniteRefinement where
  bot := ⟨G, finer.refl G, GraphLike.Finite.vertexSet_finite⟩

noncomputable instance : SDiff G.FiniteRefinement where
  sdiff H K := ofVertexSet (G.vertexSet ∪ (H.1.vertexSet \ K.1.vertexSet))
    (GraphLike.Finite.vertexSet_finite.union H.2.2.sdiff) subset_union_left
    (union_subset G.subset (sdiff_subset.trans (H.1.subset.trans H.carrier_eq.subset)))

@[simp] lemma sup_vertexSet (H K : G.FiniteRefinement) :
    (H ⊔ K).1.vertexSet = H.1.vertexSet ∪ K.1.vertexSet := by
  exact ofVertexSet_vertexSet _ _ _ _

@[simp] lemma inf_vertexSet (H K : G.FiniteRefinement) :
    (H ⊓ K).1.vertexSet = H.1.vertexSet ∩ K.1.vertexSet := by
  exact ofVertexSet_vertexSet _ _ _ _

@[simp] lemma bot_val : (⊥ : G.FiniteRefinement).1 = G := rfl

@[simp] lemma sdiff_vertexSet (H K : G.FiniteRefinement) :
    (H \ K).1.vertexSet = G.vertexSet ∪ (H.1.vertexSet \ K.1.vertexSet) := by
  exact ofVertexSet_vertexSet _ _ _ _

noncomputable instance : GeneralizedBooleanAlgebra G.FiniteRefinement :=
  addedVertices_injective.generalizedBooleanAlgebra addedVertices
    addedVertices_le_iff
    (by intro H K; simp only [lt_iff_le_not_ge, addedVertices_le_iff])
    (by intro H K; ext x; simp only [Set.sup_eq_union, addedVertices, sup_vertexSet, mem_sdiff,
        mem_union]; tauto)
    (by intro H K; ext x; simp only [Set.inf_eq_inter, addedVertices, inf_vertexSet, mem_sdiff,
        mem_inter_iff]; tauto)
    (by ext x; simp [addedVertices])
    (by
      intro H K
      ext x
      simp only [addedVertices, sdiff_vertexSet, mem_sdiff, mem_union]
      tauto)

instance (H : G.FiniteRefinement) : H.1.Finite := by
  have heq : G.refineVertices H.1.vertexSet H.2.2 H.vertices_subset
      (H.1.subset.trans H.carrier_eq.subset) = H.1 :=
    GraphLike.ext ((G.refineVertices_carrier _ _ _ _).trans H.carrier_eq.symm)
      (G.refineVertices_vertexSet _ _ _ _)
  rw [← heq]
  infer_instance

/-- The refinement join is also a least upper bound in the full graph-like order. -/
lemma isLUB_pair (H K : G.FiniteRefinement) : IsLUB {H.1, K.1} (H ⊔ K).1 := by
  refine ⟨?_, ?_⟩
  · rintro L (rfl | rfl)
    · exact (show H ≤ H ⊔ K from le_sup_left)
    · exact (show K ≤ H ⊔ K from le_sup_right)
  · intro L hL
    have hH := hL (show H.1 ∈ ({H.1, K.1} : Set (GraphLike X)) from Or.inl rfl)
    have hK := hL (show K.1 ∈ ({H.1, K.1} : Set (GraphLike X)) from Or.inr rfl)
    refine ⟨?_, ?_⟩
    · rw [(H ⊔ K).carrier_eq, ← H.carrier_eq]
      exact hH.1
    · rw [sup_vertexSet]
      exact union_subset hH.2 hK.2

/-- The refinement meet is also a greatest lower bound in the full graph-like order. -/
lemma isGLB_pair (H K : G.FiniteRefinement) : IsGLB {H.1, K.1} (H ⊓ K).1 := by
  refine ⟨?_, ?_⟩
  · rintro L (rfl | rfl)
    · exact (show H ⊓ K ≤ H from inf_le_left)
    · exact (show H ⊓ K ≤ K from inf_le_right)
  · intro L hL
    have hH := hL (show H.1 ∈ ({H.1, K.1} : Set (GraphLike X)) from Or.inl rfl)
    have hK := hL (show K.1 ∈ ({H.1, K.1} : Set (GraphLike X)) from Or.inr rfl)
    refine ⟨?_, ?_⟩
    · rw [(H ⊓ K).carrier_eq, ← H.carrier_eq]
      exact hH.1
    · rw [inf_vertexSet]
      exact subset_inter hH.2 hK.2

omit [G.Finite] in
private lemma finite_union_vertexSet {A : Set G.FiniteRefinement} (hA : BddAbove A) :
    (G.vertexSet ∪ ⋃ H ∈ A, H.1.vertexSet).Finite := by
  obtain ⟨K, hK⟩ := hA
  apply K.2.2.subset
  refine union_subset K.vertices_subset ?_
  exact iUnion₂_subset fun H hH ↦ le_iff.mp (hK hH)

omit [G.Finite] in
private lemma union_vertexSet_subset (A : Set G.FiniteRefinement) :
    (G.vertexSet ∪ ⋃ H ∈ A, H.1.vertexSet) ⊆ G.carrier :=
  union_subset G.subset (iUnion₂_subset fun H _ ↦ H.1.subset.trans H.carrier_eq.subset)

/-- A family of finite refinements is bounded exactly when its collected vertices are finite. -/
lemma bddAbove_iff_finite_iUnion_vertexSet {A : Set G.FiniteRefinement} :
    BddAbove A ↔ (⋃ H ∈ A, H.1.vertexSet).Finite := by
  refine ⟨fun hA ↦ (finite_union_vertexSet hA).subset subset_union_right, fun hA ↦ ?_⟩
  refine ⟨ofVertexSet (G.vertexSet ∪ ⋃ H ∈ A, H.1.vertexSet)
    (GraphLike.Finite.vertexSet_finite.union hA) subset_union_left
    (union_vertexSet_subset A), fun H hH ↦ le_iff.mpr ?_⟩
  rw [ofVertexSet_vertexSet]
  exact fun x hx ↦ Or.inr (mem_iUnion₂.mpr ⟨H, hH, hx⟩)

open Classical in
/-- Bounded suprema collect all vertices in the family. Unbounded families are assigned bottom. -/
noncomputable instance : SupSet G.FiniteRefinement where
  sSup A := if hA : BddAbove A then
    ofVertexSet (G.vertexSet ∪ ⋃ H ∈ A, H.1.vertexSet)
      (finite_union_vertexSet hA) subset_union_left (union_vertexSet_subset A)
    else ⊥

lemma sSup_vertexSet {A : Set G.FiniteRefinement} (hA : BddAbove A) :
    (sSup A).1.vertexSet = G.vertexSet ∪ ⋃ H ∈ A, H.1.vertexSet := by
  classical
  change (dite _ _ _ : G.FiniteRefinement).1.vertexSet = _
  rw [dite_eq_left hA, ofVertexSet_vertexSet]

lemma isLUB_sSup {A : Set G.FiniteRefinement} (hA : BddAbove A) : IsLUB A (sSup A) := by
  refine ⟨fun H hH ↦ le_iff.mpr ?_, fun K hK ↦ le_iff.mpr ?_⟩
  · rw [sSup_vertexSet hA]
    exact fun x hx ↦ Or.inr (mem_iUnion₂.mpr ⟨H, hH, hx⟩)
  · rw [sSup_vertexSet hA]
    exact union_subset K.vertices_subset (iUnion₂_subset fun H hH ↦ le_iff.mp (hK hH))

noncomputable instance : ConditionallyCompleteLattice G.FiniteRefinement :=
  conditionallyCompleteLatticeOfLatticeOfsSup _ fun _ hA _ ↦ isLUB_sSup hA

lemma sInf_vertexSet {A : Set G.FiniteRefinement} (hA : A.Nonempty) :
    (sInf A).1.vertexSet = ⋂ H ∈ A, H.1.vertexSet := by
  obtain ⟨K, hK⟩ := hA
  have hsub : (⋂ H ∈ A, H.1.vertexSet) ⊆ K.1.vertexSet := iInter₂_subset K hK
  let L : G.FiniteRefinement := ofVertexSet (⋂ H ∈ A, H.1.vertexSet)
    (K.2.2.subset hsub) (subset_iInter₂ fun H _ ↦ H.vertices_subset)
    (hsub.trans (K.1.subset.trans K.carrier_eq.subset))
  have hL : IsGLB A L := by
    refine ⟨fun H hH ↦ le_iff.mpr ?_, fun H hH ↦ le_iff.mpr ?_⟩
    · change (ofVertexSet _ _ _ _).1.vertexSet ⊆ _
      rw [ofVertexSet_vertexSet]
      exact iInter₂_subset H hH
    · change _ ⊆ (ofVertexSet _ _ _ _).1.vertexSet
      rw [ofVertexSet_vertexSet]
      exact subset_iInter₂ fun K hK ↦ le_iff.mp (hH hK)
  rw [← hL.unique (isGLB_csInf ⟨K, hK⟩ ⟨⊥, fun _ _ ↦ bot_le⟩)]
  exact ofVertexSet_vertexSet _ _ _ _

/-- The finite set of vertices added to the base graph-like space. -/
noncomputable def addedVerticesFinset (H : G.FiniteRefinement) :
    Finset ↥(G.carrier \ G.vertexSet) :=
  (H.2.2.preimage (f := (Subtype.val : ↥(G.carrier \ G.vertexSet) → X))
    Subtype.val_injective.injOn).toFinset

omit [G.Finite] in
@[simp]
lemma mem_addedVerticesFinset (H : G.FiniteRefinement) (x : ↥(G.carrier \ G.vertexSet)) :
    x ∈ H.addedVerticesFinset ↔ x.1 ∈ H.1.vertexSet := Set.Finite.mem_toFinset _

/-- Add the specified points to the vertex set of the base graph-like space. -/
noncomputable def ofFinset (A : Finset ↥(G.carrier \ G.vertexSet)) : G.FiniteRefinement :=
  ofVertexSet (G.vertexSet ∪ Subtype.val '' (A : Set ↥(G.carrier \ G.vertexSet)))
    (GraphLike.Finite.vertexSet_finite.union (A.finite_toSet.image _)) subset_union_left
    (union_subset G.subset (by rintro _ ⟨x, _, rfl⟩; exact x.2.1))

@[simp]
lemma ofFinset_vertexSet (A : Finset ↥(G.carrier \ G.vertexSet)) :
    (ofFinset A).1.vertexSet = G.vertexSet ∪ Subtype.val '' (A : Set ↥(G.carrier \ G.vertexSet)) :=
  ofVertexSet_vertexSet _ _ _ _

/-- Finite refinements are exactly finite sets of additional vertices, with the same order. -/
noncomputable def orderIsoFinset : G.FiniteRefinement ≃o Finset ↥(G.carrier \ G.vertexSet) where
  toFun := addedVerticesFinset
  invFun := ofFinset
  left_inv H := by
    apply ext
    rw [ofFinset_vertexSet]
    apply Subset.antisymm
    · refine union_subset H.vertices_subset ?_
      rintro x ⟨y, hy, rfl⟩
      exact (mem_addedVerticesFinset H y).mp hy
    · intro x hx
      by_cases hxG : x ∈ G.vertexSet
      · exact Or.inl hxG
      · let y : ↥(G.carrier \ G.vertexSet) :=
          ⟨x, H.carrier_eq ▸ H.1.subset hx, hxG⟩
        exact Or.inr ⟨y, (mem_addedVerticesFinset H y).mpr hx, rfl⟩
  right_inv A := by
    ext x
    rw [mem_addedVerticesFinset, ofFinset_vertexSet]
    constructor
    · rintro (hx | ⟨y, hy, hyx⟩)
      · exact (x.2.2 hx).elim
      · exact Subtype.val_injective hyx ▸ hy
    · intro hx
      exact Or.inr ⟨x, hx, rfl⟩
  map_rel_iff' := by
    intro H K
    constructor
    · intro h
      apply addedVertices_le_iff.mp
      intro x hx
      let y : ↥(G.carrier \ G.vertexSet) :=
        ⟨x, H.carrier_eq ▸ H.1.subset hx.1, hx.2⟩
      exact ⟨(mem_addedVerticesFinset K y).mp (h ((mem_addedVerticesFinset H y).mpr hx.1)), hx.2⟩
    · intro h x hx
      exact (mem_addedVerticesFinset K x).mpr (le_iff.mp h ((mem_addedVerticesFinset H x).mp hx))

open Classical in
noncomputable instance : LocallyFiniteOrder G.FiniteRefinement :=
  (orderIsoFinset (G := G)).toOrderEmbedding.locallyFiniteOrder

end FiniteRefinement

lemma edge.interior_infinite {G : GraphLike X} (e : G.edge) : e.interior.Infinite := by
  rw [← G.edgePath_interior e]
  exact (Ioo_infinite (show (0 : I) < 1 from zero_lt_one)).image
    (G.edgePath_isPrimitive e).injOn_Ioo

/-- If the base has an edge, every finite refinement admits a strict finite refinement. -/
instance FiniteRefinement.noMaxOrder (G : GraphLike X) [G.Finite] [Nonempty G.edge] :
    NoMaxOrder G.FiniteRefinement := by
  classical
  obtain ⟨e⟩ := ‹Nonempty G.edge›
  have : Infinite ↥(G.carrier \ G.vertexSet) :=
    (e.interior_infinite.mono e.interior_subset).to_subtype
  constructor
  intro H
  let q := FiniteRefinement.orderIsoFinset (G := G)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (q H)
  refine ⟨q.symm (insert x (q H)), q.lt_iff_lt.mp ?_⟩
  rw [q.apply_symm_apply]
  exact Finset.ssubset_insert hx

end GraphLike

end GraphLikeOrder
