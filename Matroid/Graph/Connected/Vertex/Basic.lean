import Matroid.Graph.Lattice
import Matroid.Graph.Connected.Vertex.Defs

open Set Function Nat WList

variable {α β ι ι' : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph


lemma IsWalk.isWalk_or_isWalk_compl_of_closedSubgraph (H : G.ClosedSubgraph) (hW : G.IsWalk W) :
    H.val.IsWalk W ∨ Hᶜ.val.IsWalk W := by
  by_cases hx : W.first ∈ V(H.val)
  · exact .inl <| hW.isWalk_isClosedSubgraph_of_first_mem H.prop hx
  exact .inr <| hW.isWalk_isClosedSubgraph_of_first_mem Hᶜ.prop <| by simp [hx, hW.first_mem]

lemma ConnectedBetween.mem_vertexSet_iff (H : G.ClosedSubgraph) :
    ∀ {x y : α}, G.ConnectedBetween x y → (x ∈ V(H.val) ↔ y ∈ V(H.val)) := by
  suffices ∀ x y, G.ConnectedBetween x y → x ∈ V(H.val) → y ∈ V(H.val) by
    exact fun x y h => ⟨fun hx => this x y h hx, fun hy => this y x h.symm hy⟩
  rintro x y ⟨w, hw, rfl, rfl⟩ hx
  refine hw.isWalk_or_isWalk_compl_of_closedSubgraph H |>.resolve_right (fun h ↦ ?_) |>.last_mem
  simpa [hx] using h.first_mem

lemma IsWalk.isWalk_or_isWalk_of_union_of_disjoint (h : G.StronglyDisjoint H)
    (hW : (G ∪ H).IsWalk W) : G.IsWalk W ∨ H.IsWalk W := by
  obtain hCG | hCH := hW.isWalk_or_isWalk_compl_of_closedSubgraph ⟨G, h.isClosedSubgraph_union_left⟩
  · exact .inl hCG
  rw [ClosedSubgraph.compl_eq_of_stronglyDisjoint_union h] at hCH
  exact .inr hCH
