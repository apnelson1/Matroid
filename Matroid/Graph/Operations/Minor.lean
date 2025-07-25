import Matroid.Graph.Connected.Basic


variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

namespace Graph

/-! # Minor -/

/-! ## Vertex Identification -/

/-- Repartition -/
def Repartition (G : Graph α β) (P : Partition (Set α)) (hP : G.Dup ≤ P) : Graph α β :=
  mk_of_domp P G.IsLink (fun hlab hlcd ↦ by
    rw [← Partition.rel_le_iff_le] at hP
    exact (G.dup_or_dup_of_isLink_of_isLink hlab hlcd).imp (hP _ _ ·) (hP _ _ ·))

/-- Vertex identification -/
def VertexIdentification (G : Graph α β) (S : Set α) : Graph α β :=
  Repartition G (G.Dup ⊔ (Partition.indiscrete' S)) le_sup_left

/-! ## Contraction -/

-- needs connected partition

/-- Contraction -/
def Contract (G : Graph α β) (C : Set β) : Graph α β :=
  sorry
