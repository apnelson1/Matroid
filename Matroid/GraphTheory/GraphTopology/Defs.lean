module

public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink
public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent

/-! # Graph-like spaces

Topological carriers with a vertex set and primitive-link geometric edges.
-/

@[expose] public section

open Set Function TopologicalSpace Set.Notation

variable {X : Type*} [TopologicalSpace X]

structure GraphLike (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  vertexSet : Set X
  t2Space : T2Space carrier
  subset : vertexSet ⊆ carrier
  isClosed : IsClosed (carrier ↓∩ vertexSet)
  isTotallySeparated : IsTotallySeparated (carrier ↓∩ vertexSet)
  interior_isOpen' (p : X) (hp : p ∈ carrier \ vertexSet) :
    IsOpen (carrier ↓∩ connectedComponentIn (carrier \ vertexSet) p)
  boundary_isPair' (p : X) (hp : p ∈ carrier \ vertexSet) :
    let U := connectedComponentIn (carrier \ vertexSet) p
    ∃ x y : vertexSet, (carrier ∩ closure U) \ U = {x.1, y.1} ∧
      IsPrimitiveLink (carrier ∩ closure U) x.1 y.1

attribute [instance] GraphLike.t2Space

def IsGraphLike (S : Set X) : Prop := ∃ G : GraphLike X, G.carrier = S

variable {G : GraphLike X}

namespace GraphLike

-- The carrier forgets the vertex set, so its coercion is not injective.
instance : CoeTC (GraphLike X) (Set X) := ⟨GraphLike.carrier⟩

instance : Membership X (GraphLike X) := ⟨fun G x ↦ x ∈ (G : Set X)⟩

instance : CoeSort (GraphLike X) (Type _) := ⟨fun G ↦ {x : X // x ∈ G}⟩

/-- `V(G)` denotes the vertex set of a graph-like space. -/
scoped notation "V(" G ")" => GraphLike.vertexSet G

/-- The edges of a graph-like space, regarded as subsets of the ambient space.
Ordinary edge statements use `e : Set X` and `e ∈ E(G)`, not component indices. -/
def edgeSet (G : GraphLike X) : Set (Set X) :=
  {e | ∃ p ∈ G.carrier \ V(G), G.carrier ∩ closure (connectedComponentIn (G.carrier \ V(G)) p) = e}

/-- `E(G)` denotes the set of geometric edges of `G`. -/
scoped notation "E(" G ")" => GraphLike.edgeSet G

/-- The interior of an edge relative to the graph's vertex set, not ambient interior. -/
def edgeInterior (G : GraphLike X) (e : Set X) : Set X := e \ V(G)

/-- The boundary vertices of an edge, not its ambient frontier. -/
def edgeBoundary (G : GraphLike X) (e : Set X) : Set X := e ∩ V(G)

/-- An edge with the indicated pair of boundary vertices; coincident vertices give a loop. -/
def IsLink (G : GraphLike X) (e : Set X) (x y : X) : Prop :=
  e ∈ E(G) ∧ G.edgeBoundary e = {x, y}

class Finite (G : GraphLike X) : Prop where
  vertexSet_finite : G.vertexSet.Finite
  edgeSet_finite : E(G).Finite

instance (G : GraphLike X) [G.Finite] : _root_.Finite G.vertexSet :=
  Finite.vertexSet_finite.to_subtype

instance (G : GraphLike X) [G.Finite] : _root_.Finite E(G) :=
  Finite.edgeSet_finite.to_subtype

/-- `G.finer H` means that `H` has the same carrier and contains every vertex of `G`. -/
structure finer (G H : GraphLike X) : Prop where
  carrier_eq : G.carrier = H.carrier
  vertices_subset : G.vertexSet ⊆ H.vertexSet

/-- The set of faces. Use its subtype when a construction needs a type of faces. -/
def faceSet (G : GraphLike X) : Set (Set X) :=
  {F | ∃ x ∈ G.carrierᶜ, connectedComponentIn G.carrierᶜ x = F}

scoped notation "F(" G ")" => GraphLike.faceSet G

/-- The complementary component of a point. This is a face when the point is outside
the carrier, and is empty otherwise. -/
noncomputable def faceAt (G : GraphLike X) (x : X) : Set X :=
  connectedComponentIn G.carrierᶜ x

/-- Connected components of the ambient frontier of a face region. -/
def FaceBoundaryComponent (F : Set X) := ConnectedComponents ↥(frontier F)

def FaceInc (G : GraphLike X) (v : X) (F : Set X) : Prop :=
  F ∈ F(G) ∧ v ∈ V(G) ∧ v ∈ frontier F

def IsBoundaryEdge (G : GraphLike X) (e F : Set X) : Prop :=
  F ∈ F(G) ∧ e ∈ E(G) ∧ (G.edgeInterior e ∩ frontier F).Nonempty

end GraphLike
