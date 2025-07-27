import Matroid.Graph.Basic

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

namespace Graph

def VertexConnected (G : Graph α β) : Prop :=
  G.Dup ⊔ ofRel (Relation.TransGen ())
