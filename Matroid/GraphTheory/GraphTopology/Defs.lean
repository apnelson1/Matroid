module

public import Matroid.ForMathlib.Topology.PrimitiveLink
public import Matroid.ForMathlib.Topology.ConnectedComponent

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
  interior_isOpen' (e : ConnectedComponents ↥(carrier \ vertexSet)) :
    IsOpen (carrier ↓∩ (Subtype.val '' e.toSet))
  boundary_isPair' (e : ConnectedComponents ↥(carrier \ vertexSet)) :
    let U := Subtype.val '' e.toSet
    ∃ x y : vertexSet, (carrier ∩ closure U) \ U = {x.1, y.1} ∧
      IsPrimitiveLink (carrier ∩ closure U) x.1 y.1

attribute [instance] GraphLike.t2Space

def IsGraphLike (S : Set X) : Prop := ∃ G : GraphLike X, G.carrier = S

variable {G : GraphLike X}

namespace GraphLike

/-- `V(G)` denotes the vertex set of a graph-like space. -/
scoped notation "V(" G ")" => GraphLike.vertexSet G

/-- The edges of a graph-like space, regarded as subsets of the ambient space.
Ordinary edge statements use `e : Set X` and `e ∈ E(G)`, not component indices. -/
def edgeSet (G : GraphLike X) : Set (Set X) :=
  range (fun c : ConnectedComponents ↥(G.carrier \ V(G)) ↦
    G.carrier ∩ closure (Subtype.val '' c.toSet))

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

def Face (G : GraphLike X) := ConnectedComponents ↥(G.carrierᶜ)

def faceAt (G : GraphLike X) {x : X} (hx : x ∉ G.carrier) : G.Face :=
  ConnectedComponents.mk ⟨x, hx⟩

namespace Face

variable {G : GraphLike X} (F : G.Face)

def set (F : G.Face) : Set X :=
  Subtype.val '' F.toSet

def boundary : Set X := frontier F.set

def FaceBoundaryComponent := ConnectedComponents ↥F.boundary

end Face

def FaceInc (G : GraphLike X) (v : X) (F : G.Face) : Prop :=
  v ∈ V(G) ∧ v ∈ F.boundary

def IsBoundaryEdge (G : GraphLike X) (e : Set X) (F : G.Face) : Prop :=
  e ∈ E(G) ∧ (G.edgeInterior e ∩ F.boundary).Nonempty

end GraphLike
