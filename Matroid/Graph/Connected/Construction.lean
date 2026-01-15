import Matroid.Graph.Connected.Defs

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

@[simp]
lemma Set.pair_subsingleton_iff {x y : α} : ({x, y} : Set α).Subsingleton ↔ x = y := by
  refine ⟨fun h => h (by simp) (by simp), ?_⟩
  rintro rfl
  simp

namespace Graph

example (n : ℕ) : (⊥ : Graph α β).PreconnGE n := by simp

@[simp]
lemma ConnBetweenGE_bouquet_self (n : ℕ) : (bouquet v F).ConnBetweenGE v v n :=
  connBetweenGE_self (by simp) n

example : (bouquet v F).Preconnected := by simp only [bouquet_isComplete, IsComplete.preconnected]
example : (bouquet v F).Connected := by simp
example : (bouquet v F).IsSepSet S ↔ S = {v} := by simp
example (n : ℕ) : (bouquet v F).PreconnGE n := by simp
example (n : ℕ) : (bouquet v F).ConnGE n ↔ n ≤ 1 := by simp

example : (Graph.singleEdge u v e).Preconnected := by simp
example : (Graph.singleEdge u v e).Connected := by simp

lemma preconnected_iff_of_edgeSet_empty (hE : E(G) = ∅) : G.Preconnected ↔ V(G).Subsingleton := by
  refine ⟨fun h u hu v hv↦ ?_, fun h u v hu hv ↦ ?_⟩
  · obtain ⟨w, hw, rfl, rfl⟩ := h u v hu hv
    match w with
    | .nil u => simp
    | .cons u e w => simpa [hE] using hw.edge_mem_of_mem (e := e) (by simp)
  obtain rfl := h hu hv
  simpa

lemma connected_iff_of_edgeSet_empty (hE : E(G) = ∅) : G.Connected ↔ ∃ v, V(G) = {v} := by
  rw [connected_iff, preconnected_iff_of_edgeSet_empty hE,
    exists_eq_singleton_iff_nonempty_subsingleton]

@[simps]
def singleEdge_edgeCut (hne : u ≠ v) : EdgeCut (Graph.singleEdge u v e) where
  carrier := {e}
  carrier_subset := by simp
  not_connected' h := by
    rw [connected_iff_of_edgeSet_empty (by simp),
      exists_eq_singleton_iff_nonempty_subsingleton] at h
    exact hne <| h.2 (by simp : u ∈ _) (by simp : v ∈ _)

example : (Graph.singleEdge u v e).IsSepSet S ↔ S = {u, v} := by simp
example (n : ℕ) : (Graph.singleEdge u v e).PreconnGE n := by simp

@[simp]
lemma singleEdge_connGE (hne : u ≠ v) (n : ℕ) : (Graph.singleEdge u v e).ConnGE n ↔ n ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConnGE.anti_right h (by simp)⟩
  have := by simpa [hne, encard_pair] using h.le_card
  omega


@[simp]
lemma banana_preconnGE (hF : F.Nonempty) (n : ℕ) : (banana u v F).PreconnGE n := by
  obtain rfl | hne := eq_or_ne u v
  · simp
  apply IsComplete.preconnGE
  simp [hne, hF]
