import Matroid.Graph.Tree


variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

open Set

namespace Graph

def IsPlanar (G : Graph α β) : Prop :=
  ∃ H : Graph α β, G.cycleMatroid.dual = H.cycleMatroid




end Graph
