import Matroid.Graph.Finite.Basic

variable {α β : Type*} {G H T F : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α}
{P C Q : WList α β}
open Set WList

namespace Graph

lemma IsTree.exists_isLeafVertex [T.Finite] (hT : T.IsTree) : ∃ x, T.IsLeafVertex x := by
  obtain ⟨x, hx⟩ := hT.connected.nonempty
  obtain ⟨P, hP⟩ := T.isPath_finite.exists_maximalFor WList.length _ ⟨WList.nil x, by simpa⟩
  refine ⟨P.first, ?_⟩
  sorry

  -- · sorry
  -- refine

lemma foo_tree [G.Finite] (hT : T.IsTree) :
    Set.ncard E(G) + 1 = Set.ncard V(G) := by
  sorry

lemma foo [G.Finite] (hG : G.IsForest) :
    Set.ncard E(G) + Nat.card {H | IsComponent H G} = Set.ncard V(G) := by
  sorry
