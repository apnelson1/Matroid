import Matroid.ForMathlib.Graph.Connected

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β}

namespace Graph

def Acyclic (G : Graph α β) : Prop := ¬ ∃ C, G.IsCycle C

structure IsTree (T : Graph α β) : Prop where
  acyclic : T.Acyclic
  connected : T.Connected

lemma Connected.isTree_of_maximal_acyclic_le (hG : G.Connected)
    (h : Maximal (fun H ↦ H.Acyclic ∧ H ≤ G) T) : T.IsTree := by
  refine ⟨h.prop.1, by_contra fun hnc ↦ ?_⟩
  have := exists_of_not_connected hnc
