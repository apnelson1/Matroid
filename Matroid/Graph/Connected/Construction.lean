import Matroid.Graph.Connected.Menger
import Matroid.Graph.Connected.Bond

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

example (n : ℕ) : (⊥ : Graph α β).PreconnGE n := by simp

@[simp]
lemma ConnBetweenGE_bouquet_self (n : ℕ) : (bouquet v F).ConnBetweenGE v v n :=
  connBetweenGE_self (by simp) n

example : (bouquet v F).Preconnected := by simp only [bouquet_isComplete, IsComplete.preconnected]
example : (bouquet v F).Connected := by simp
example : (bouquet v F).IsSep S ↔ S = {v} := by simp
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

@[simps (attr := grind =)]
def singleEdge_isEdgeSep (hne : u ≠ v) : (Graph.singleEdge u v e).IsEdgeSep {e} where
  subset_edgeSet := by simp
  not_connected h := by
    rw [connected_iff_of_edgeSet_empty (by simp),
      exists_eq_singleton_iff_nonempty_subsingleton] at h
    exact hne <| h.2 (by simp : u ∈ _) (by simp : v ∈ _)

example : (Graph.singleEdge u v e).IsSep S ↔ S = {u, v} := by simp
example (n : ℕ) : (Graph.singleEdge u v e).PreconnGE n := by simp

@[simp]
lemma singleEdge_connGE (hne : u ≠ v) (n : ℕ) : (Graph.singleEdge u v e).ConnGE n ↔ n ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConnGE.anti_right h (by simp)⟩
  obtain ⟨rfl, hlt⟩ := by simpa [encard_pair hne] using h.le_card
  all_goals lia

@[simp]
lemma banana_preconnected_iff : (banana u v F).Preconnected ↔ u = v ∨ F.Nonempty := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_nonempty_iff_eq_empty]
    rintro rfl
    simpa using h u v (by simp) (by simp)
  rintro (rfl | hF)
  · simp
  simp [hF]

@[simp]
lemma banana_connected_iff : (banana u v F).Connected ↔ u = v ∨ F.Nonempty := by
  rw [connected_iff]
  simp

@[simp]
lemma banana_preconnGE_iff : (banana u v F).PreconnGE n ↔ n = 0 ∨ u = v ∨ F.Nonempty := by
  refine ⟨fun hcon => ?_, fun h => ?_⟩
  · rw [or_iff_not_imp_right]
    simp only [← ne_eq, not_or, not_nonempty_iff_eq_empty]
    rintro ⟨hne, rfl⟩
    simpa [hne.symm] using hcon
  rw [← banana_isComplete_iff] at h
  obtain rfl | hc := h
  · simp
  simp [hc]

@[simp]
lemma banana_connGE_iff : (banana u v F).ConnGE n ↔ n = 0 ∨ (n = 1 ∧ (u = v ∨ F.Nonempty)) := by
  obtain hc | hc := em ((banana u v F).IsComplete) |>.symm
  · simp [← banana_isComplete_iff, hc, ← preconnGE_iff_connGE_of_not_isComplete hc]
  simp only [hc.connGE_iff, vertexSet_banana, pair_subsingleton_iff, ← banana_isComplete_iff, hc,
    and_true]
  constructor
  · rintro (⟨rfl, hle⟩ | hlt)
    · simp only [mem_singleton_iff, insert_eq_of_mem, encard_singleton, ENat.coe_le_one] at hle
      lia
    have := encard_pair_le u v
    enat_to_nat!
    omega
  rintro (rfl | rfl)
  · simp
  obtain (rfl | hne) := eq_or_ne u v
  · simp
  simp [encard_pair hne]

lemma completeGraph_preconnected (n : ℕ) : (CompleteGraph n).Preconnected := by
  rintro u v hu hv
  simp only [vertexSet_CompleteGraph, mem_Iio] at hu hv
  obtain rfl | hne := eq_or_ne u v
  · simpa
  exact Adj.connBetween <| by simp [hu, hv, hne]

open Classical in
@[simps (attr := grind =)]
noncomputable def IsComplete.VertexEnsemble (h : G.IsComplete) (hs : s ∈ V(G)) (ht : t ∈ V(G))
    (hne : s ≠ t) : G.VertexEnsemble s t ↑(V(G) \ {s}) where
  f x := if hxt : x = t then (h s hs t ht hne).choose_spec.walk else
    cons s ((h s hs x x.prop.1 (Ne.symm x.prop.2)).choose)
    (h x x.prop.1 t ht hxt).choose_spec.walk
  isPath x := by
    split_ifs with hxt
    · exact IsLink.walk_isPath (Exists.choose_spec (h s hs t ht hne)) hne
    generalize_proofs h1 h2 h3
    simp [h1.choose_spec, h3.walk_isPath hxt, hne, Ne.symm x.prop.2]
  first_eq x := by split_ifs with hxt <;> simp
  last_eq x := by split_ifs with hxt <;> simp
  internallyDisjoint i j hne := by
    simp only
    split_ifs <;> grind [IsLink.walk_vertexSet, IsLink.walk_last, IsLink.walk_first]

lemma IsComplete.edgeConnGE [G.Finite] (h : G.IsComplete) : G.EdgeConnGE (V(G).ncard - 1) := by
  obtain h1 | ⟨v, hv⟩ := V(G).eq_empty_or_nonempty
  · simp_all
  have hV : V(G).encard ≠ ⊤ := by simp
  rw [Menger'sTheorem_edge (ι := ↑(V(G) \ {v}))
    (by simp [encard_diff_singleton_of_mem hv, ncard, ENat.coe_toNat])]
  intro s t hs ht
  obtain rfl | hne := eq_or_ne s t
  · exact ⟨G.edgePathEnsemble_nil hs _⟩
  classical
  let e : ↑(V(G) \ {v}) ≃ ↑(V(G) \ {s}) := by
    refine BijOn.equiv (fun x ↦ if x = s then v else x) ⟨by grind [MapsTo], by grind [InjOn], ?_⟩
    intro x hx
    obtain rfl | hne := eq_or_ne x v <;> [use s; use x] <;> grind
  let A : G.EdgePathEnsemble s t ↑(V(G) \ {s}) :=
    EdgePathEnsemble.ofVertexEnsemble (h.VertexEnsemble hs ht hne) ?_
  refine ⟨A.comp e.toEmbedding⟩
  intro i hi j hj
  simp at hi hj
  split_ifs at hi hj
  · grind
  all_goals simp [IsLink.walk] at hi hj

@[simp]
lemma IsComplete.edgeConnGE_iff [G.Finite] [G.Simple] (h : G.IsComplete) (hnt : V(G).Nontrivial)
    (k : ℕ) : G.EdgeConnGE k ↔ k + 1 ≤ V(G).encard := by
  refine ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
  · obtain ⟨u, hu, v, hv, hne⟩ := hnt
    obtain rfl | h1k := (Nat.zero_le k).eq_or_lt
    · simp only [cast_zero, zero_add, one_le_encard_iff_nonempty]
      use u
    simp only [edgeConnGE_iff_isEdgeCut h1k, h.preconnected, true_and] at hk
    obtain ⟨e, he⟩ := h u hu v hv hne
    specialize hk _ (IsEdgeCut.of_vert u) ⟨e, by grind⟩
    rw [setLinkEdges_singleton_compl_eq_incEdges, encard_incEdges, h.neighbors hu,
      encard_diff_singleton_of_mem hu] at hk
    eomega
  apply h.edgeConnGE |>.anti_right (n := k)
  have := G.vertexSet_finite.encard_lt_top.ne
  rw [ncard]
  enat_to_nat!
  rw [ENat.toNat_coe]
  grind

@[simp]
lemma completeGraph_edgeConnGE_iff {n : ℕ} (hn : 1 < n) (k : ℕ) :
    (CompleteGraph n).EdgeConnGE k ↔ k + 1 ≤ n := by
  rw [completeGraph_isComplete n |>.edgeConnGE_iff (by use 0, by grind, 1, by grind, by simp) k]
  simp only [↓encard_vertexSet_completeGraph, Order.add_one_le_iff]
  eomega

lemma completeBipartiteGraph_connected {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (CompleteBipartiteGraph m n).Connected := by
  rw [connected_iff_exists_connBetween (by simp [pos_of_ne_zero hm] : Sum.inl 0 ∈ _)]
  rintro v hv
  match v with
  | .inl v =>
    have hul : (CompleteBipartiteGraph m n).Adj (Sum.inl 0) (Sum.inr 0) := by
      simp [pos_of_ne_zero hn, pos_of_ne_zero hm]
    have hlv : (CompleteBipartiteGraph m n).Adj (Sum.inr 0) (Sum.inl v) := by
      simpa [pos_of_ne_zero hn] using hv
    exact hul.connBetween.trans hlv.connBetween
  | .inr v => exact Adj.connBetween <| by simpa [pos_of_ne_zero hm] using hv

-- @[simp]
-- lemma completeBipartiteGraph_edgeConnGE (m n : ℕ) :
--     (CompleteBipartiteGraph m n).EdgeConnGE (min m n) := by
--   sorry

-- @[simp]
-- lemma completeBipartiteGraph_edgeConnGE_iff {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (k : ℕ) :
--     (CompleteBipartiteGraph m n).EdgeConnGE k ↔ k ≤ m ∧ k ≤ n := by
--   sorry
