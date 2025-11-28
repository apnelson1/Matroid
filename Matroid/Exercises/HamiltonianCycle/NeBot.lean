import Mathlib.Tactic
import Matroid.Graph.Connected.Basic

open Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}

-- TODO: EVERYTHING HAVING TO DO WITH NEBOT SHOULD BE REPLACED WITH GRAPH.NONEMPTY (itself a TODO)

def NeBot (G : Graph α β) : Prop :=
  G ≠ ⊥

@[simp]
lemma NeBot_iff_vertexSet_nonempty : G.NeBot ↔ V(G).Nonempty := by
  simp [NeBot, ne_bot_iff]

lemma vertexSet_nonempty_of_NeBot (h : G.NeBot) : V(G).Nonempty := by
  rwa [←NeBot_iff_vertexSet_nonempty]

lemma NeBot_iff_encard_positive : G.NeBot ↔ 0 < V(G).encard := by
  simp

lemma NeBot_of_ncard_positive (h : 0 < V(G).ncard) : G.NeBot := by
  rw [NeBot, ne_eq, ←vertexSet_eq_empty_iff, ←ne_eq, ←Set.nonempty_iff_ne_empty]
  apply nonempty_of_ncard_ne_zero
  linarith
