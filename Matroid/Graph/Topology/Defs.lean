import Matroid.ForMathlib.Geometry.PolygonalPath.Basic
import Matroid.Graph.Bipartite
import Matroid.Graph.Presentation.Quotient
import Matroid.Graph.Immersion.Basic
import Matroid.Graph.Hom.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Path

-- Standalone bundled variant of Defs.lean; do not import both files.

open Set Function TopologicalSpace Set.Notation Graph
open scoped Sym2

variable {V ι E V' E' X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {G : Graph V E}
  {P : Presentation V ι E} {e : E(G)} {u v : V(G)} {S Z : Set X} [T2Space S] {x y : X}


section Realization

namespace Graph.Presentation

instance (P : Presentation V ι E) : TopologicalSpace P.vertexSet := ⊥

abbrev PreRealization (P : Presentation V ι E) := P.vertexSet ⊕ Σ (_ : ι), unitInterval

inductive RealizationRel (P : Presentation V ι E) : P.PreRealization → P.PreRealization → Prop
  | attach (i) : RealizationRel P (.inl ⟨P.attach i, P.attach_mem i⟩) (.inr ⟨i, 0⟩)
  | other (i) : RealizationRel P (.inr ⟨i, 1⟩) (.inr ⟨P.other i, 1⟩)

abbrev Realization (P : Presentation V ι E) :=
  Quotient (Relation.EqvGen.setoid (RealizationRel P))

def Realization.vertex (v : P.vertexSet) : P.Realization := Quotient.mk _ (.inl v)

end Graph.Presentation

end Realization

def Path.IsPrimitive (γ : Path x y) : Prop :=
  ∀ ⦃s t : unitInterval⦄, γ s = γ t → s = t ∨ ({s, t} : Set unitInterval) = {0, 1}

def IsPrimitiveLink (L : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, γ.IsPrimitive ∧ range γ = L

section GraphLike

abbrev edgePiece (S Z : Set X) := ConnectedComponents ↥(S \ Z)

def edgePiece.interior (e : edgePiece S Z) : Set X :=
  Subtype.val '' (ConnectedComponents.mk ⁻¹' {e})

def edgePiece.Range (e : edgePiece S Z) : Set X :=
  S ∩ closure e.interior

def edgePiece.boundary (e : edgePiece S Z) : Set X :=
  e.Range \ e.interior

structure GraphLike (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  vertexSet : Set X
  t2Space : T2Space carrier
  subset : vertexSet ⊆ carrier
  isClosed : IsClosed (carrier ↓∩ vertexSet)
  isTotallySeparated : IsTotallySeparated (carrier ↓∩ vertexSet)
  interior_isOpen (e : edgePiece carrier vertexSet) : IsOpen (carrier ↓∩ e.interior)
  boundary_isPair (e : edgePiece carrier vertexSet) :
    ∃ x y : vertexSet, e.boundary = {x.1, y.1} ∧ IsPrimitiveLink e.Range x.1 y.1

attribute [instance] GraphLike.t2Space

def IsGraphLike (S : Set X) [T2Space S] : Prop := ∃ T : GraphLike X, T.carrier = S

namespace IsGraphLike

def degreeTwo (S : Set X) (p : X) : Prop :=
  ∃ U : Set X, U ⊆ S ∧ IsOpen (S ↓∩ U) ∧ p ∈ U ∧ Nonempty (U ≃ₜ ℝ)

end IsGraphLike

def GraphLike.toGraph (hZ : GraphLike X) : Graph X (edgePiece hZ.carrier hZ.vertexSet) where
  vertexSet := hZ.vertexSet
  edgeSet := univ
  IsLink e x y := e.boundary = {x, y}
  isLink_symm e _ := ⟨fun x y h ↦ h.trans (pair_comm x y)⟩
  eq_or_eq_of_isLink_of_isLink e x y v w h h' := by
    have : x ∈ ({v, w} : Set X) := h' ▸ h.symm ▸ mem_insert x {y}
    simpa using this
  edge_mem_iff_exists_isLink e := by
    obtain ⟨x, y, h, -⟩ := hZ.boundary_isPair e
    exact ⟨fun _ ↦ ⟨x, y, h⟩, fun _ ↦ mem_univ e⟩
  left_mem_of_isLink e x y h := by
    obtain ⟨v, w, h', -⟩ := hZ.boundary_isPair e
    have : x ∈ ({v.1, w.1} : Set X) := h' ▸ h.symm ▸ mem_insert x {y}
    rcases mem_insert_iff.mp this with rfl | hx
    · exact v.2
    · exact mem_singleton_iff.mp hx ▸ w.2

def GraphLike.IsPolygonal [AddCommGroup X] [Module ℝ X] [ContinuousSMul ℝ X] [ContinuousAdd X]
    (T : GraphLike X) : Prop :=
  ∀ {e : edgePiece T.carrier T.vertexSet} {x y : X}, e.boundary = {x, y} →
    ∃ P : PolygonalPath x y, P.toPath.IsPrimitive ∧ P.toSet = e.Range

end GraphLike

section Drawing

namespace Graph

structure Drawing (V E X : Type*) [TopologicalSpace X] extends GraphLike X where
  graph : Graph V E
  iso : Graph.Iso graph toGraphLike.toGraph

def IsDrawing (G : Graph V E) (S : Set X) [T2Space S] : Prop :=
  ∃ D : Drawing V E X, D.graph = G ∧ D.carrier = S

def Drawing.vertex (D : Drawing V E X) : V(D.graph) ↪ X :=
  D.iso.vertEquiv.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

def Drawing.edge (D : Drawing V E X) : E(D.graph) ≃ edgePiece D.carrier D.vertexSet :=
  D.iso.edgeEquiv.trans (Equiv.Set.univ _)

theorem Drawing.boundary_eq (D : Drawing V E X) {e : E(D.graph)} {u v : V(D.graph)}
    (h : D.graph.IsLink e.1 u.1 v.1) : (D.edge e).boundary = {D.vertex u, D.vertex v} :=
  D.iso.map_isLink h

def Drawing.edgeInterior (D : Drawing V E X) (e : E(D.graph)) : Set X :=
  (D.edge e).interior

def Drawing.edgeRange (D : Drawing V E X) (e : E(D.graph)) : Set X :=
  (D.edge e).Range

def Drawing.edgeBoundary (D : Drawing V E X) (e : E(D.graph)) : Set X :=
  (D.edge e).boundary

noncomputable def GraphLike.drawing (hZ : GraphLike X) :
    Drawing X (edgePiece hZ.carrier hZ.vertexSet) X where
  toGraphLike := hZ
  graph := hZ.toGraph
  iso := Graph.Iso.id _

theorem Drawing.isGraphLike (D : Drawing V E X) : IsGraphLike D.carrier :=
  ⟨D.toGraphLike, rfl⟩

def Drawing.support (D : Drawing V E X) (K : Graph V E) (hK : K ≤ D.graph) : Set X :=
  range (fun v : V(K) ↦ D.vertex ⟨v.1, hK.vertexSet_mono v.2⟩) ∪
    ⋃ e : E(K), D.edgeRange ⟨e.1, hK.edgeSet_mono e.2⟩

instance Drawing.support_t2Space (D : Drawing V E X) (K : Graph V E) (hK : K ≤ D.graph) :
    T2Space (D.support K hK) := by
  have hsub : D.support K hK ⊆ D.carrier := by
    rintro x (⟨v, rfl⟩ | hx)
    · exact D.subset (D.iso.vertMap _).2
    · obtain ⟨e, he⟩ := mem_iUnion.mp hx
      exact he.1
  exact (Topology.IsEmbedding.inclusion hsub).t2Space

noncomputable def Drawing.restrict (D : Drawing V E X) (K : Graph V E) (hK : K ≤ D.graph) :
    Drawing V E X :=
  let vertex : V(K) ↪ X := ⟨fun v ↦ D.vertex ⟨v.1, hK.vertexSet_mono v.2⟩, by
    intro v w h
    exact Subtype.ext (congrArg (fun v : V(D.graph) ↦ v.1) (D.vertex.injective h))⟩
  let edge : E(K) ≃ edgePiece (D.support K hK) (range vertex) := {
    toFun := fun e ↦
      ConnectedComponents.mk
        ⟨(Quotient.out (D.edge ⟨e.1, hK.edgeSet_mono e.2⟩)).1, by sorry⟩
    invFun := fun C ↦
      let p := Quotient.out C
      (mem_iUnion.mp (p.2.1.resolve_left p.2.2)).choose
    left_inv := by sorry
    right_inv := by sorry }
  { carrier := D.support K hK
    vertexSet := range vertex
    t2Space := inferInstance
    subset := fun _ hx ↦ Or.inl hx
    isClosed := by sorry
    isTotallySeparated := by sorry
    interior_isOpen := by sorry
    boundary_isPair := by sorry
    graph := K
    iso := Graph.Iso.ofEquivs (Equiv.ofInjective vertex vertex.injective)
      (edge.trans (Equiv.Set.univ _).symm) (by sorry) }

open Classical in
noncomputable def Drawing.addEdge [T2Space X] {e : E} (D : Drawing V E X)
    (G : Graph V E) (hG : G ＼ {e} = D.graph)
    (hS : IsClosed D.carrier) {u v : V(G)} (he : G.IsLink e u.1 v.1) (L : Set X)
    (hL : IsPrimitiveLink L (D.vertex ⟨u.1, hG ▸ u.2⟩) (D.vertex ⟨v.1, hG ▸ v.2⟩))
    (hinter : L ∩ D.carrier =
      {D.vertex ⟨u.1, hG ▸ u.2⟩, D.vertex ⟨v.1, hG ▸ v.2⟩}) : Drawing V E X :=
  let vertex : V(G) ↪ X := ⟨fun w ↦ D.vertex ⟨w.1, hG ▸ w.2⟩, by
    intro w z h
    exact Subtype.ext (congrArg (fun w : V(D.graph) ↦ w.1) (D.vertex.injective h))⟩
  let edge : E(G) ≃ edgePiece (D.carrier ∪ L) (range vertex) := {
    toFun := fun f ↦ if h : f.1 = e then
      ConnectedComponents.mk ⟨hL.choose unitInterval.half, by sorry⟩
    else
      ConnectedComponents.mk ⟨(Quotient.out (D.edge ⟨f.1, hG ▸ ⟨f.2, h⟩⟩)).1, by sorry⟩
    invFun := fun C ↦
      let p := Quotient.out C
      if h : p.1 ∈ D.carrier then
        let f := D.edge.symm (ConnectedComponents.mk ⟨p.1, h, by
          intro hp
          let w := D.iso.vertEquiv.symm ⟨p.1, hp⟩
          have hw : D.vertex w = p.1 :=
            congrArg Subtype.val (D.iso.vertEquiv.apply_symm_apply ⟨p.1, hp⟩)
          exact p.2.2 ⟨⟨w.1, show w.1 ∈ V(G ＼ {e}) from hG.symm ▸ w.2⟩, hw⟩⟩)
        ⟨f.1, (show f.1 ∈ E(G ＼ {e}) from hG.symm ▸ f.2).1⟩
      else ⟨e, he.edge_mem⟩
    left_inv := by sorry
    right_inv := by sorry }
  { carrier := D.carrier ∪ L
    vertexSet := range vertex
    t2Space := inferInstance
    subset := by rintro _ ⟨w, rfl⟩; exact Or.inl (D.subset (D.iso.vertMap _).2)
    isClosed := by sorry
    isTotallySeparated := by sorry
    interior_isOpen := by sorry
    boundary_isPair := by sorry
    graph := G
    iso := Graph.Iso.ofEquivs (Equiv.ofInjective vertex vertex.injective)
      (edge.trans (Equiv.Set.univ _).symm) (by sorry) }

open Classical in
noncomputable def Drawing.precompSubdivision {H : Graph V' E'} [H.Finite] (D : Drawing V E X)
    (M : Immersion H D.graph) (hM : M.Topological) (hSurj : M.Surjective) : Drawing V' E' X :=
  let vertex := M.vertex.trans D.vertex
  let edge : E(H) ≃ edgePiece D.carrier (range vertex) := {
    toFun := fun e ↦
      let f : E(D.graph) := ⟨(M.route_nonempty e).firstEdge, by
        exact (M.route_isTrail e).isWalk.edgeSet_subset (M.route_nonempty e).firstEdge_mem⟩
      ConnectedComponents.mk ⟨(Quotient.out (D.edge f)).1, by sorry⟩
    invFun := fun C ↦ by
      let p := Quotient.out C
      by_cases hp : p.1 ∈ D.vertexSet
      · let v := D.iso.vertEquiv.symm ⟨p.1, hp⟩
        have hvp : D.vertex v = p.1 :=
          congrArg Subtype.val (D.iso.vertEquiv.apply_symm_apply ⟨p.1, hp⟩)
        have hv : v.1 ∈ V(M.Image) := hSurj.symm ▸ v.2
        have hv' : v.1 ∈ range (Subtype.val ∘ M.vertex) ∪
            ⋃ e : E(H), (M.route e).vertexSet := by
          simpa only [Immersion.Image, vertexSet_restrict, vertexSet_induce] using hv
        have hn : v.1 ∉ range (Subtype.val ∘ M.vertex) := by
          rintro ⟨w, hw⟩
          exact p.2.2 ⟨w, (congrArg D.vertex (Subtype.ext hw)).trans hvp⟩
        exact (mem_iUnion.mp (hv'.resolve_left hn)).choose
      · let e := D.edge.symm (ConnectedComponents.mk ⟨p.1, p.2.1, hp⟩)
        have he : e.1 ∈ E(M.Image) := hSurj.symm ▸ e.2
        change e.1 ∈ E(D.graph[range (Subtype.val ∘ M.vertex) ∪
          ⋃ f : E(H), (M.route f).vertexSet]) ∩ ⋃ f : E(H), (M.route f).edgeSet at he
        exact (mem_iUnion.mp he.2).choose
    left_inv := by sorry
    right_inv := by sorry }
  { carrier := D.carrier
    vertexSet := range vertex
    t2Space := inferInstance
    subset := by rintro _ ⟨w, rfl⟩; exact D.subset (D.iso.vertMap _).2
    isClosed := by sorry
    isTotallySeparated := by sorry
    interior_isOpen := by sorry
    boundary_isPair := by sorry
    graph := H
    iso := Graph.Iso.ofEquivs (Equiv.ofInjective vertex vertex.injective)
      (edge.trans (Equiv.Set.univ _).symm) (by sorry) }

noncomputable def Drawing.precomp {H : Graph V' E'} [H.Finite] (D : Drawing V E X)
    (M : Immersion H D.graph) (hM : M.Topological) : Drawing V' E' X :=
  (D.restrict M.Image M.image_le).precompSubdivision M.toImage (by sorry) (by
    change M.Image[V(M.Image)] ↾ (⋃ e : E(H), (M.route e).edgeSet) = M.Image
    rw [induce_vertexSet]
    exact restrict_of_superset _ inter_subset_right)

noncomputable def Drawing.postcomp (D : Drawing V E X) (φ : X → Y)
    (hφ : Topology.IsEmbedding (fun x : D.carrier ↦ φ x.1)) : Drawing V E Y :=
  let vertex : V(D.graph) ↪ Y := ⟨φ ∘ D.vertex, by
    intro u v huv
    apply D.vertex.injective
    exact congrArg (fun x : D.carrier ↦ x.1) (hφ.injective (a₁ :=
      ⟨D.vertex u, D.subset (D.iso.vertMap u).2⟩) (a₂ :=
      ⟨D.vertex v, D.subset (D.iso.vertMap v).2⟩) huv)⟩
  let edge : E(D.graph) ≃ edgePiece (φ '' D.carrier) (range vertex) := {
    toFun := fun e ↦
      ConnectedComponents.mk ⟨φ (Quotient.out (D.edge e)).1, by sorry⟩
    invFun := fun C ↦
      let p := Quotient.out C
      let x := p.2.1.choose
      D.edge.symm (ConnectedComponents.mk ⟨x, p.2.1.choose_spec.1, by
        intro hx
        let v := D.iso.vertEquiv.symm ⟨x, hx⟩
        have hv : D.vertex v = x :=
          congrArg Subtype.val (D.iso.vertEquiv.apply_symm_apply ⟨x, hx⟩)
        exact p.2.2 ⟨v, (congrArg φ hv).trans p.2.1.choose_spec.2⟩⟩)
    left_inv := by sorry
    right_inv := by sorry }
  { carrier := φ '' D.carrier
    vertexSet := range vertex
    t2Space := (hφ.toHomeomorph.trans (Homeomorph.setCongr
      (show range (fun x : D.carrier ↦ φ x.1) = φ '' D.carrier by ext y; simp))).t2Space
    subset := by rintro _ ⟨w, rfl⟩; exact ⟨D.vertex w, D.subset (D.iso.vertMap w).2, rfl⟩
    isClosed := by sorry
    isTotallySeparated := by sorry
    interior_isOpen := by sorry
    boundary_isPair := by sorry
    graph := D.graph
    iso := Graph.Iso.ofEquivs (Equiv.ofInjective vertex vertex.injective)
      (edge.trans (Equiv.Set.univ _).symm) (by sorry) }

end Graph

end Drawing

section Faces

namespace Graph.Drawing

def Face (D : Drawing V E X) := ConnectedComponents ↥(D.carrierᶜ)

def faceSet (D : Drawing V E X) (F : D.Face) : Set X :=
  Subtype.val '' ConnectedComponents.mk ⁻¹' {F}

def faceAt (D : Drawing V E X) {x : X} (hx : x ∉ D.carrier) : D.Face :=
  ConnectedComponents.mk ⟨x, hx⟩

def faceBoundary (D : Drawing V E X) (F : D.Face) : Set X := frontier (D.faceSet F)

def VertexFaceInc (D : Drawing V E X) (v : V(D.graph)) (F : D.Face) : Prop :=
  D.vertex v ∈ D.faceBoundary F

def edgeFaceBoundary (D : Drawing V E X) (e : E(D.graph)) (F : D.Face) : Set X :=
  D.edgeInterior e ∩ D.faceBoundary F

def EdgeFaceInc (D : Drawing V E X) (e : E(D.graph)) (F : D.Face) : Prop :=
  (D.edgeFaceBoundary e F).Nonempty

def IsBoundaryEdge (D : Drawing V E X) (e : E(D.graph)) (F : D.Face) : Prop :=
  D.edgeRange e ⊆ D.faceBoundary F

def FaceBoundaryComponent (D : Drawing V E X) (F : D.Face) :=
  ConnectedComponents ↥(D.faceBoundary F)

def faceBoundaryComponentSet (D : Drawing V E X) {F : D.Face}
    (C : D.FaceBoundaryComponent F) : Set X :=
  Subtype.val '' ConnectedComponents.mk ⁻¹' {C}

end Graph.Drawing

end Faces


section Theorems

namespace Graph

variable {V E : Type*} {X : Type*} [TopologicalSpace X] {G : Graph V E}

theorem realization_drawing {P : Presentation V ι E} [P.toGraph.Finite] (S : Set X)
    [T2Space S] : IsDrawing P.toGraph S ↔ Nonempty (P.Realization ≃ₜ S) := by
  sorry

theorem EdgeFaceInc_iff_IsBoundaryEdge {D : Drawing V E ℂ} [D.graph.Finite]
    {e : E(D.graph)} {F : D.Face} : D.EdgeFaceInc e F ↔ D.IsBoundaryEdge e F := by
  sorry

theorem exists_polygonalPath_in_face {V E : Type*} {D : Drawing V E ℂ} [D.graph.Finite]
    (hD : D.IsPolygonal) {F : D.Face} {x y : ℂ}
    (hx : x ∈ D.faceBoundary F) (hy : y ∈ D.faceBoundary F) :
    ∃ Q : PolygonalPath x y, Q.toPath.IsPrimitive ∧ Q.toSet \ {x, y} ⊆ D.faceSet F := by
  sorry

end Graph

end Theorems
