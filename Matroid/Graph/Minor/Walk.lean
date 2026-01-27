import Matroid.Graph.Minor.Defs

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ I : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)}

open Set Function

namespace Graph

lemma IsCycle.contract (h : G.IsCycle C) (φ : (G ↾ C).connPartition.RepFun) :

end Graph
