import Matroid.Graph.Connected.Basic


variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

namespace Graph

/-! # Minor -/

/-! ## Vertex Identification -/

/-- Vertex identification -/
def VertexIdentification (G : Graph α β) (S : Set α) : Graph α β :=
  Repartition G (G.Dup ⊔ (Partition.indiscrete' S)) le_sup_left

/-! ## Contraction -/

-- needs connected partition

/-- Contraction -/
def Contract (G : Graph α β) (C : Set β) : Graph α β :=
  sorry
