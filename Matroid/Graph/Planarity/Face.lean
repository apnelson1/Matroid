module

public import Matroid.Graph.Planarity.Drawing
public import Matroid.ForMathlib.Topology.OnePoint
public import Matroid.ForMathlib.Topology.JordanCurve
public import Matroid.ForMathlib.Topology.ConnectedComponent

/-!
# Faces of a drawing

A face is a connected component of the complement of the support of a drawing.

The API defines faces and their carriers, identifies faces from open connected sets, and transports
drawings and supports to the one-point compactification.
-/

open Function Set Topology

namespace Graph

public noncomputable section

universe u v

variable {α β γ δ : Type*} {G H : Graph α β}
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {W : Set X}

namespace Drawing

/-! ### Faces, with no hypotheses -/

/-- The faces of a drawing are the connected components of its complement. -/
@[expose]
def Face (D : Drawing G X) : Type u := ConnectedComponents ↑(D.supportᶜ)

/-- The subset of the ambient space belonging to a face. -/
@[expose]
def faceSet (D : Drawing G X) (F : D.Face) : Set X :=
  Subtype.val '' ConnectedComponents.mk ⁻¹' {F}

/-- Every face contains a point. -/
lemma faceSet_nonempty (D : Drawing G X) (F : D.Face) : (D.faceSet F).Nonempty := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe F
  exact ⟨x.1, x, rfl, rfl⟩

/-- A face is disjoint from the drawing. -/
lemma faceSet_disjoint_support (D : Drawing G X) (F : D.Face) :
    Disjoint (D.faceSet F) D.support := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨⟨_, hx⟩, -, rfl⟩
  exact hx

/-- The face containing `x` is its connected component in the complement of the drawing. -/
lemma faceSet_eq_connectedComponentIn (D : Drawing G X) (F : D.Face) {x : X}
    (hx : x ∈ D.faceSet F) : D.faceSet F = connectedComponentIn D.supportᶜ x := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hF : F = ConnectedComponents.mk y := (mem_singleton_iff.mp hy).symm
  subst F
  change (↑) '' (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk y}) =
    connectedComponentIn D.supportᶜ ↑y
  rw [connectedComponentIn_eq_image y.2]
  congr 1
  ext w
  exact ConnectedComponents.coe_eq_coe'

/-- A face is connected. -/
lemma faceSet_isConnected (D : Drawing G X) (F : D.Face) : IsConnected (D.faceSet F) := by
  obtain ⟨x, hx⟩ := D.faceSet_nonempty F
  rw [D.faceSet_eq_connectedComponentIn F hx]
  exact isConnected_connectedComponentIn_iff.mpr <|
    (D.faceSet_disjoint_support F).notMem_of_mem_left hx

/-- The face containing a point off the drawing. -/
def faceAt (D : Drawing G X) {x : X} (hx : x ∉ D.support) : D.Face :=
  ConnectedComponents.mk ⟨x, hx⟩

lemma mem_faceSet_faceAt (D : Drawing G X) {x : X} (hx : x ∉ D.support) :
    x ∈ D.faceSet (D.faceAt hx) :=
  ⟨⟨x, hx⟩, rfl, rfl⟩

lemma faceSet_faceAt (D : Drawing G X) {x : X} (hx : x ∉ D.support) :
    D.faceSet (D.faceAt hx) = connectedComponentIn D.supportᶜ x :=
  D.faceSet_eq_connectedComponentIn _ (D.mem_faceSet_faceAt hx)

/-- **Recognising a face.** An open connected set off the drawing whose frontier lies in the
drawing is a face. -/
lemma exists_faceSet_eq (D : Drawing G X) (hW : IsOpen W) (hWc : IsConnected W)
    (hWD : Disjoint W D.support) (hfr : frontier W ⊆ D.support) :
    ∃ F : D.Face, D.faceSet F = W := by
  obtain ⟨a, ha⟩ := hWc.nonempty
  refine ⟨D.faceAt (hWD.notMem_of_mem_left ha), ?_⟩
  rw [D.faceSet_faceAt]
  exact (eq_connectedComponentIn_of_frontier_subset hW hWc.isPreconnected hWD hfr ha).symm

/-! ### Openness and frontier -/

/-- Components of an open set in a locally connected space are open. -/
lemma faceSet_isOpen [LocallyConnectedSpace X] (D : Drawing G X) (hD : IsClosed D.support)
    (F : D.Face) : IsOpen (D.faceSet F) := by
  obtain ⟨x, hx⟩ := D.faceSet_nonempty F
  rw [D.faceSet_eq_connectedComponentIn F hx]
  exact hD.isOpen_compl.connectedComponentIn

/-- The frontier of a face lies in the drawing.

The actual topology is the graph-free theorem
`IsClosed.frontier_connectedComponentIn_compl_subset`; this is only the face-API corollary. -/
lemma frontier_faceSet_subset_support [LocallyConnectedSpace X] (D : Drawing G X)
    (hD : IsClosed D.support) (F : D.Face) : frontier (D.faceSet F) ⊆ D.support := by
  obtain ⟨x, hx⟩ := D.faceSet_nonempty F
  rw [D.faceSet_eq_connectedComponentIn F hx]
  exact hD.frontier_connectedComponentIn_compl_subset

/-- A subgraph is facial in `D` if its drawing is exactly the frontier of a face. -/
def IsFacialSubgraph (D : Drawing G X) (h : H ≤ G) : Prop :=
  ∃ F : D.Face, frontier (D.faceSet F) = (D.restrict h).support

/-! ### Transport to the sphere -/

/-- A drawing in `X` read as a drawing in `OnePoint X`. -/
def onePoint (D : Drawing G X) : Drawing G (OnePoint X) :=
  D.postcomp ⟨(↑), OnePoint.continuous_coe⟩ OnePoint.coe_injective

@[simp]
lemma support_onePoint (D : Drawing G X) : D.onePoint.support = (↑) '' D.support := by
  ext y
  simp only [support, onePoint, mem_range, mem_image, postcomp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨D x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- On the sphere the support of a drawing of a finite graph is closed. -/
lemma isClosed_support_onePoint [G.Finite] [T2Space X] [LocallyCompactSpace X] (D : Drawing G X) :
    IsClosed D.onePoint.support := by
  rw [support_onePoint]
  exact (D.support_isCompact.image OnePoint.continuous_coe).isClosed

end Drawing

end

end Graph
