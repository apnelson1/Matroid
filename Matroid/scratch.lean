import Mathlib.Data.Set.Card

variable {α β : Type*}

structure Multigraph (α β : Type*) where
  V : Set α
  E : Set β
  inc : β → α → Prop
  inc_mem_edge : ∀ e v, inc e v → e ∈ E
  inc_mem_vx : ∀ e v, inc e v → v ∈ V
  inc_exists : ∀ e, ∃ v ∈ V, inc e v
  inc_card : ∀ e, {v | inc e v}.encard ≤ 2

namespace Multigraph

def deleteEdges (G : Multigraph α β) (F : Set β) : Multigraph α β where
  V := G.V
  E := G.E \ F
  inc e v := e ∉ F ∧ G.inc e v
  inc_mem_edge := sorry
  inc_mem_vx := sorry
  inc_exists := sorry
  inc_card := sorry

-- identify a set of `S` vertices to a vertex named `z`, which can be inside or outside `V`.
def identify (G : Multigraph α β) (S : Set α) (z : α) : Multigraph α β where
  V := insert z (G.V \ S)
  E := G.E
  inc e v := (v ∉ S ∧ G.inc e v) ∨ (v = z ∧ ∃ x ∈ S, G.inc e x)
  inc_mem_edge := sorry
  inc_mem_vx := sorry
  inc_exists := sorry
  inc_card := sorry

-- contract an edge `e` to a vertex `z`. We can choose `z` as an existing end of `e`, or
-- give it a new name from a vertex outside `V`.
def contractEdge (G : Multigraph α β) (e : β) (z : α) : Multigraph α β :=
  (G.identify {v | G.inc e v} z).deleteEdges {e}
