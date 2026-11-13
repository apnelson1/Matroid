module

public import Matroid.GraphTheory.GraphTopology.Basic

/-! # Recognizing geometric edges

A decomposition certifies that supplied primitive links are exactly the edges determined by a
carrier and vertex set. Finite geometry discharges the same predicate; label correspondences
are independent of how the graph-like space was constructed.
-/

@[expose] public section

open Set Function Topology Set.Notation
open scoped GraphLike

namespace GraphLike

variable {X : Type*} [TopologicalSpace X]

/-- `D` is the geometric edge set determined by carrier `S` and vertices `Z`.
Closedness of `Z` and disjointness of interiors are consequences, not fields.
`T2Space S` stays an external hypothesis: it is not implied by these four facts. -/
structure IsLinkDecomposition (S Z : Set X) (D : Set (Set X)) : Prop where
  cover : S = Z ∪ ⋃₀ D
  link : ∀ e ∈ D, ∃ a b, IsPrimitiveLink e a b ∧ e ∩ Z = {a, b}
  separated : IsTotallySeparated (S ↓∩ Z)
  interior_open : ∀ e ∈ D, IsOpen (S ↓∩ (e \ Z))

variable {S Z e : Set X} {G : GraphLike X} {D : Set (Set X)} {x a b : X}

theorem IsLinkDecomposition.subset_carrier (h : IsLinkDecomposition S Z D) (he : e ∈ D) :
    e ⊆ S := by
  rw [h.cover]
  exact (subset_sUnion_of_mem he).trans subset_union_right

/-- With a cover and open interiors, vertices are relatively closed. No finiteness. -/
theorem IsLinkDecomposition.vertices_isClosed (h : IsLinkDecomposition S Z D) :
    IsClosed (S ↓∩ Z) := by
  apply isOpen_compl_iff.mp
  convert isOpen_biUnion h.interior_open
  ext y
  simp only [mem_compl_iff, mem_preimage, mem_iUnion, mem_sdiff]
  refine ⟨fun hyZ ↦ ?_, fun ⟨_, _, _, hyd⟩ ↦ hyd⟩
  obtain ⟨d, hd, hyd⟩ := (h.cover ▸ y.2 : y.1 ∈ Z ∪ ⋃₀ D).resolve_left hyZ
  exact ⟨d, hd, hyd, hyZ⟩

variable [T2Space S]

/-- The component of a point outside the vertices is the interior of a supplied piece. -/
private theorem component_spec (h : IsLinkDecomposition S Z D) (hx : x ∈ S \ Z) :
    ∃ d ∈ D, connectedComponentIn (S \ Z) x = d \ Z ∧
      S ∩ closure (connectedComponentIn (S \ Z) x) = d := by
  obtain ⟨d, hd, hxd⟩ := (h.cover ▸ hx.1 : x ∈ Z ∪ ⋃₀ D).resolve_left hx.2
  obtain ⟨a, b, hl, hv⟩ := h.link d hd
  have hc := hl.connectedComponentIn_sdiff_eq (h.subset_carrier hd) hv
    (h.interior_open d hd) ⟨hxd, hx.2⟩
  exact ⟨d, hd, hc, by rw [hc]; exact hl.inter_closure_sdiff_eq (h.subset_carrier hd) hv⟩

/-- Supplied pieces are exactly the edges of any graph-like space with this carrier and
these vertices, including one that already exists. This equality is not definitional. -/
theorem edgeSet_eq (h : IsLinkDecomposition G.carrier V(G) D) : E(G) = D := by
  ext d
  refine ⟨?_, fun hd ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨e, he, -, hclosure⟩ := component_spec h hx
    exact hclosure.symm ▸ he
  obtain ⟨a, b, hl, hv⟩ := h.link d hd
  obtain ⟨x, hxd, hxV⟩ : (d \ V(G)).Nonempty := by
    rw [← sdiff_self_inter, hv]
    exact hl.diff_endpoints_nonempty
  refine ⟨x, ⟨h.subset_carrier hd hxd, hxV⟩, ?_⟩
  rw [hl.connectedComponentIn_sdiff_eq (h.subset_carrier hd) hv
    (h.interior_open d hd) ⟨hxd, hxV⟩,
    hl.inter_closure_sdiff_eq (h.subset_carrier hd) hv]

/-- Disjoint interiors follow from recognition. They are not a general hypothesis.
Indexed injectivity does not yield this fact: distinct primitive links may cross. -/
theorem IsLinkDecomposition.pairwise_disjoint_interior (h : IsLinkDecomposition S Z D) :
    D.Pairwise fun d f ↦ Disjoint (d \ Z) (f \ Z) := by
  intro d hd f hf hdf
  rw [Set.disjoint_left]
  intro y hyd hyf
  obtain ⟨p, q, hl, hv⟩ := h.link d hd
  obtain ⟨p', q', hl', hv'⟩ := h.link f hf
  have hdcomp := hl.connectedComponentIn_sdiff_eq (h.subset_carrier hd) hv
    (h.interior_open d hd) hyd
  have hfcomp := hl'.connectedComponentIn_sdiff_eq (h.subset_carrier hf) hv'
    (h.interior_open f hf) hyf
  have hpiece : d = f := by
    rw [← hl.inter_closure_sdiff_eq (h.subset_carrier hd) hv,
      ← hl'.inter_closure_sdiff_eq (h.subset_carrier hf) hv', ← hdcomp, ← hfcomp]
  exact hdf hpiece

def IsLinkDecomposition.toGraphLike (h : IsLinkDecomposition S Z D) :
    GraphLike X where
  carrier := S
  vertexSet := Z
  t2Space := inferInstance
  subset := by rw [h.cover]; exact subset_union_left
  isClosed := h.vertices_isClosed
  isTotallySeparated := h.separated
  interior_isOpen' := fun x hx => by
    obtain ⟨d, hd, hcomponent, -⟩ := component_spec h hx
    exact hcomponent ▸ h.interior_open d hd
  boundary_isPair' := fun x hx => by
    obtain ⟨d, hd, hcomponent, hclosure⟩ := component_spec h hx
    obtain ⟨a, b, hl, hv⟩ := h.link d hd
    have ha : a ∈ Z := (show a ∈ d ∩ Z from hv.symm ▸ mem_insert _ _).2
    have hb : b ∈ Z := (show b ∈ d ∩ Z from hv.symm ▸ mem_insert_of_mem _ rfl).2
    dsimp only
    rw [hclosure, hcomponent]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by rw [sdiff_sdiff_right_self, hv], hl⟩

@[simp] theorem IsLinkDecomposition.toGraphLike_carrier (h : IsLinkDecomposition S Z D) :
    (h.toGraphLike).carrier = S := rfl

@[simp] theorem IsLinkDecomposition.toGraphLike_vertexSet (h : IsLinkDecomposition S Z D) :
    V(h.toGraphLike) = Z := rfl

@[simp] theorem IsLinkDecomposition.toGraphLike_edgeSet (h : IsLinkDecomposition S Z D) :
    E(h.toGraphLike) = D := edgeSet_eq (G := h.toGraphLike) h

/-- Any two decompositions of the same carrier and vertices name the same pieces. -/
theorem IsLinkDecomposition.unique {D' : Set (Set X)} (h : IsLinkDecomposition S Z D)
    (h' : IsLinkDecomposition S Z D') : D = D' := by
  let G := h.toGraphLike
  exact (edgeSet_eq (G := G) h).symm.trans (edgeSet_eq (G := G) h')

omit [TopologicalSpace X] in
/-- Nonempty pairwise-disjoint interiors make an indexed family injective.
The converse is false without a recognition hypothesis. -/
theorem injective_of_pairwise_disjoint_interior {ι : Type*} {L : ι → Set X}
    (hdisj : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z))
    (hne : ∀ i, (L i \ Z).Nonempty) : Injective L := by
  intro i j hij
  by_contra hneij
  obtain ⟨y, hy⟩ := hne i
  exact (hdisj hneij).notMem_of_mem_left hy (hij ▸ hy)

/-- Identify supplied labels with geometric edges, retaining each supplied image. -/
noncomputable def edgeEquivOfRange (G : GraphLike X) {ι : Type*} {L : ι → Set X}
    (hE : E(G) = range L) (hL : Injective L) : ι ≃ ↥E(G) :=
  (Equiv.ofInjective L hL).trans (Set.equivOfEq hE.symm)

@[simp] lemma edgeEquivOfRange_coe (G : GraphLike X) {ι : Type*} {L : ι → Set X}
    (hE : E(G) = range L) (hL : Injective L) (i : ι) :
    (G.edgeEquivOfRange hE hL i).1 = L i := rfl

section Finite

variable {S Z : Set X} {D : Set (Set X)} [T2Space S]

private theorem isTotallySeparated_preimage_of_finite (hZ : Z.Finite) :
    IsTotallySeparated (S ↓∩ Z) := by
  have hZ' : (S ↓∩ Z).Finite := hZ.preimage Subtype.val_injective.injOn
  intro x hx y hy hxy
  obtain ⟨U, V, hU, hV, hxU, hrestV, hd⟩ :=
    SeparatedNhds.of_finite (finite_singleton x) (hZ'.sdiff (t := {x}))
      (Set.disjoint_left.mpr fun z hz hrest ↦ hrest.2 hz)
  refine ⟨U, V, hU, hV, hxU (by simp), hrestV ⟨hy, by simpa using hxy.symm⟩, ?_, hd⟩
  intro z hz
  obtain rfl | hzx := eq_or_ne z x
  · exact Or.inl (hxU (by simp))
  · exact Or.inr (hrestV ⟨hz, hzx⟩)

/-- Finitely many compact pieces meeting only in a finite vertex set have relatively open
interiors. This is where disjointness of interiors is used. -/
private theorem isOpen_preimage_sdiff_of_finite (hZ : Z.Finite) (hD : D.Finite)
    (hcover : S = Z ∪ ⋃₀ D) (hcompact : ∀ d ∈ D, IsCompact d)
    (hdisj : D.Pairwise fun d d' ↦ Disjoint (d \ Z) (d' \ Z)) (he : e ∈ D) :
    IsOpen (S ↓∩ (e \ Z)) := by
  have hsub (d) (hd : d ∈ D) : d ⊆ S :=
    hcover ▸ subset_union_of_subset_right (subset_sUnion_of_mem hd) Z
  have heq : S ↓∩ (e \ Z) = (S ↓∩ Z ∪ ⋃ d ∈ D \ {e}, S ↓∩ d)ᶜ := by
    ext x
    simp only [mem_preimage, mem_sdiff, mem_compl_iff, mem_union, mem_iUnion,
      mem_singleton_iff, not_or, not_exists]
    refine ⟨fun ⟨hxe, hxZ⟩ ↦ ?_, fun ⟨hxZ, hother⟩ ↦ ?_⟩
    · exact ⟨hxZ, fun d hd hxd ↦ (hdisj hd.1 he hd.2).notMem_of_mem_left ⟨hxd, hxZ⟩ ⟨hxe, hxZ⟩⟩
    obtain ⟨d, hd, hxd⟩ := ((hcover ▸ x.2 : x.1 ∈ Z ∪ ⋃₀ D).resolve_left hxZ)
    obtain rfl | hde := eq_or_ne d e
    · exact ⟨hxd, hxZ⟩
    · exact (hother d ⟨hd, hde⟩ hxd).elim
  rw [heq]
  refine (IsClosed.union ?_ ?_).isOpen_compl
  · exact (hZ.preimage Subtype.val_injective.injOn).isClosed
  exact (hD.subset sdiff_subset).isClosed_biUnion fun d hd ↦
    (IsInducing.subtypeVal.isCompact_preimage' (hcompact d hd.1)
      (by simpa only [Subtype.range_coe] using hsub d hd.1)).isClosed

end Finite

/-- Finite vertices and finitely many pieces whose interiors are disjoint discharge
separation and relative openness. Disjointness is an input here because it proves
openness; the general predicate then derives disjointness again. One edge law follows
from `edgeSet_eq`, with no finite copy of the constructor equations. -/
theorem IsLinkDecomposition.ofFinite (hZ : Z.Finite) (hD : D.Finite) (hS : S = Z ∪ ⋃₀ D)
    (hlink : ∀ e ∈ D, ∃ a b, IsPrimitiveLink e a b ∧ e ∩ Z = {a, b})
    (hdisj : D.Pairwise fun d f ↦ Disjoint (d \ Z) (f \ Z)) : IsLinkDecomposition S Z D := by
  refine ⟨hS, hlink, isTotallySeparated_preimage_of_finite hZ, fun e he ↦ ?_⟩
  refine isOpen_preimage_sdiff_of_finite hZ hD hS (fun d hd ↦ ?_) hdisj he
  obtain ⟨a, b, hl, -⟩ := hlink d hd
  exact hl.isCompact

/-- Indexed finite families reduce to `ofFinite` on `range L`.
The equivalence is separate: `edgeEquivOfRange`. -/
theorem IsLinkDecomposition.ofFiniteIndexed {ι : Type*} [_root_.Finite ι] {L : ι → Set X}
    (hZ : Z.Finite) (hS : S = Z ∪ ⋃ i, L i)
    (hlink : ∀ i, ∃ a b, IsPrimitiveLink (L i) a b ∧ L i ∩ Z = {a, b})
    (hdisj : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z)) :
    IsLinkDecomposition S Z (range L) := by
  refine ofFinite hZ (finite_range L) ?_ ?_ ?_
  · rw [hS, sUnion_range]
  · rintro _ ⟨i, rfl⟩
    exact hlink i
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hdf
  exact hdisj fun hij ↦ hdf (congrArg L hij)

/-- Finite vertices and pieces give a finite graph-like space. -/
theorem IsLinkDecomposition.toGraphLike_finite (h : IsLinkDecomposition S Z D)
    (hZ : Z.Finite) (hD : D.Finite) : h.toGraphLike.Finite := by
  refine ⟨hZ, ?_⟩
  rw [h.toGraphLike_edgeSet]
  exact hD

end GraphLike
