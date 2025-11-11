import Matroid.Graph.Connected.Defs


open Set Function Nat WList

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

def internallyDisjoint (s t : α) {ι : Type*} (f : ι → G.Subgraph) : Prop :=
  Pairwise (fun i j => V((f i).val) ∩ V((f j).val) = {s, t})

structure VertexEnsemble (G : Graph α β) (s t : α) (ι : Type*) where
  f : ι → G.Subgraph
  internallyDisjoint : G.internallyDisjoint s t f
  stConnected : ∀ i, (f i).val.VertexConnected s t

def VertexEnsemble.of_le (P : H.VertexEnsemble s t ι) (hle : H ≤ G) : G.VertexEnsemble s t ι :=
  ⟨(P.f ·|>.of_le hle), P.internallyDisjoint, P.stConnected⟩

def stEmsemble.precomp (P : G.VertexEnsemble s t ι) (f : ι' ↪ ι) : G.VertexEnsemble s t ι' :=
  ⟨P.f ∘ f, P.internallyDisjoint.comp_of_injective f.injective, (P.stConnected <| f ·)⟩





def STVxConnectivity (G : Graph α β) (s t : α) (n : Cardinal) :=
  IsGreatest {m | m ≤ #V(G) ∧ G.stVxPreConn s t m} n
