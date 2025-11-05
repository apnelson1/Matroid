import Matroid.Graph.Connected.Subgraph


open Set Function Nat WList

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

/-! ### Vertex-Connectivity -/

structure VertexCut (G : Graph α β) where
  carrier : Set α
  subset_vertexSet : carrier ⊆ V(G)
  disconnects : ¬ (G - carrier).Connected

instance : SetLike G.VertexCut α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [VertexCut.mk.injEq]
