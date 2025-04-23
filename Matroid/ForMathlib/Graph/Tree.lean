import Matroid.ForMathlib.Graph.Connected
import Matroid.ForMathlib.Graph.Subgraph
import Mathlib.Data.Set.Subsingleton

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β}

open Set

namespace Graph

def Acyclic (G : Graph α β) : Prop := ¬ ∃ C, G.IsCycle C

/-- The union of two acyclic graphs that intersect in at most one vertex is acyclic.  -/
lemma Acyclic.union_acyclic_of_subsingleton_inter (hG : G.Acyclic) (hH : H.Acyclic)
    (hi : (G.V ∩ H.V).Subsingleton) : (G ∪ H).Acyclic := by
  rintro ⟨C, hC⟩




-- structure IsTree (T : Graph α β) : Prop where
--   acyclic : T.Acyclic
--   connected : T.Connected

-- lemma Connected.isTree_of_maximal_acyclic_le (hG : G.Connected)
--     (h : Maximal (fun H ↦ H.Acyclic ∧ H ≤ G) T) : T.IsTree := by
--   refine ⟨h.prop.1, by_contra fun hnc ↦ ?_⟩
--   have hV : T.V = G.V := by
--     refine (vxSet_subset_of_le h.prop.2).
--   have := exists_of_not_connected hnc
