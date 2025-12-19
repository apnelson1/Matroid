import Matroid.Graph.Connected.Defs

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

@[simp]
lemma ConnBetweenGe_bouquet_self (n : ℕ) : (bouquet v F).ConnBetweenGe v v n :=
  connBetweenGe_self (by simp) n

@[simp]
lemma bouquet_vertexDelete : (bouquet v F) - {v} = ⊥ :=
  (vertexDelete_eq_bot_iff (bouquet v F) {v}).mpr <| by simp

-- @[simp]
-- lemma bouquet_preconnected : (bouquet v F).Preconnected := by
--   simp

-- @[simp]
-- lemma bouquet_connected : (bouquet v F).Connected := by
--   simp

@[simps]
def bouquet_cut : Cut (bouquet v F) where
  carrier := {v}
  carrier_subset := by simp
  not_connected' := by simp

-- @[simp]
-- lemma singleEdge_preconnected : (Graph.singleEdge u v e).Preconnected := by
--   simp

-- @[simp]
-- lemma singleEdge_connected : (Graph.singleEdge u v e).Connected := by
--   simp

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

example (n : ℕ) : (⊥ : Graph α β).PreconnGe n := by simp

example (n : ℕ) : (bouquet v F).PreconnGe n := by simp



@[simp]
lemma banana_preconnGe (hF : F.Nonempty) (n : ℕ) : (banana u v F).PreconnGe n := by
  obtain rfl | hne := eq_or_ne u v
  · simp
  apply IsComplete.preconnGe
  simp [hne, hF]

example (n : ℕ) : (Graph.singleEdge u v e).PreconnGe n := by simp

@[simp]
lemma singleEdge_connGe (hne : u ≠ v) (n : ℕ) : (Graph.singleEdge u v e).ConnGe n ↔ n ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConnGe.anti_right h fun C ↦ ?_⟩
  · simpa using h (mixedCut_of_edgeCut <| singleEdge_edgeCut hne)
  by_contra! hcd
  have := by simpa using ENat.lt_one_iff_eq_zero.mp hcd
  simpa [this.1, this.2] using C.not_conn'
