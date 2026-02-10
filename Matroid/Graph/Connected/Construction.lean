import Matroid.ForMathlib.Card
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
lemma noEdge_isComplete_iff : (Graph.noEdge X β).IsComplete ↔ X.Subsingleton := by
  refine ⟨fun h x hx y hy => ?_, fun h x hx y hy hne => (hne <| h hx hy).elim⟩
  by_contra! hne
  obtain ⟨e, he⟩ := h x hx y hy hne
  simpa using he.edge_mem

@[simp]
lemma IsWalk.nil_of_noEdge (h : (Graph.noEdge X β).IsWalk W) : W.Nil := by
  match W with
  | .nil u => simp
  | .cons u e w => simp at h

@[simp]
lemma connBetween_noEdge_iff : (Graph.noEdge X β).ConnBetween x y ↔ x = y ∧ x ∈ X := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw, rfl, rfl⟩
    match hw.nil_of_noEdge with | .nil x => simp_all
  rintro ⟨rfl, hx⟩
  simpa

@[simp]
lemma noEdge_preconnected_iff : (Graph.noEdge X β).Preconnected ↔ X.Subsingleton := by
  refine ⟨fun h => ?_, fun h x y hx hy => ?_⟩
  · by_contra! ht
    obtain ⟨x, hx, y, hy, hne⟩ := ht
    simpa [hne] using h x y hx hy
  simp only [noEdge_vertexSet] at hx hy
  obtain rfl := h hx hy
  simpa

@[simp]
lemma noEdge_connected_iff : (Graph.noEdge X β).Connected ↔ ∃ v, X = {v} := by
  rw [connected_iff, noEdge_preconnected_iff, noEdge_vertexSet]
  simp only [exists_eq_singleton_iff_nonempty_subsingleton]

@[simp]
lemma IsSepBetween.ne_of_noEdge (h : (Graph.noEdge X β).IsSepBetween x y Y) (hx : x ∈ X) :
    x ≠ y := by
  rintro rfl
  simpa [hx, h.left_not_mem] using h.not_connBetween

lemma isSepBetween_noEdge_of_ne (hne : x ≠ y) (hY : Y ⊆ X \ {x, y}) :
    (Graph.noEdge X β).IsSepBetween x y Y where
  subset := subset_diff.mp hY |>.1
  left_not_mem := (disjoint_iff_forall_notMem ..).mp (subset_diff.mp hY).2.symm (by simp)
  right_not_mem := (disjoint_iff_forall_notMem ..).mp (subset_diff.mp hY).2.symm (by simp)
  not_connBetween := by
    rintro ⟨W, hW, rfl, rfl⟩
    rw [isWalk_vertexDelete_iff] at hW
    exact hne hW.1.nil_of_noEdge.first_eq_last

@[simp]
lemma isEdgeSep_noEdge_iff : (Graph.noEdge X β).IsEdgeSep F ↔ F = ∅ ∧ X.encard ≠ 1 := by
  refine ⟨fun ⟨hF, h⟩ => ?_, ?_⟩
  · obtain rfl := by simpa using hF
    simpa [encard_eq_one] using h
  rintro ⟨rfl, hne⟩
  simpa [encard_eq_one] using hne

@[simp]
lemma isEdgeSep_bot_iff : (⊥ : Graph α β).IsEdgeSep F ↔ F = ∅ := by
  rw [← noEdge_empty, isEdgeSep_noEdge_iff]
  simp

@[simp]
lemma noEdge_connBetweenGE_iff (n : ℕ) : (Graph.noEdge X β).ConnBetweenGE x y n ↔
    n = 0 ∨ (x = y ∧ x ∈ X) := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_and']
    rintro hne
    by_cases hxX : x ∈ X
    · simpa using h (isSepBetween_noEdge_of_ne (hne hxX) (by simp : ∅ ⊆ _))
    simpa [hxX] using h.left_mem
  rintro (rfl | ⟨rfl, hx⟩)
  · simp
  exact connBetweenGE_self hx n

@[simp]
lemma noEdge_preconnGE_iff (n : ℕ) : (Graph.noEdge X β).PreconnGE n ↔ n = 0 ∨ X.Subsingleton := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_right, not_subsingleton_iff]
    rintro ⟨x, hx, y, hy, hne⟩
    simpa using h hx hy (isSepBetween_noEdge_of_ne hne (by simp : ∅ ⊆ _))
  rintro (rfl | hss) u v hu hv C hC
  · simp
  obtain rfl := hss hu hv
  exact (hC.ne_of_noEdge hu rfl).elim

@[simp]
lemma noEdge_ConnGE_iff (n : ℕ) : (Graph.noEdge X β).ConnGE n ↔ n = 0 ∨ (n = 1 ∧ ∃ x, X = {x}):= by
  obtain hc | hc := em ((Graph.noEdge X β).IsComplete) |>.symm
  · rw [← preconnGE_iff_connGE_of_not_isComplete hc, noEdge_preconnGE_iff]
    constructor
    · rintro (rfl | hss)
      · tauto
      simp [hss] at hc
    rintro (rfl | ⟨rfl, x, rfl⟩) <;> simp
  rw [hc.connGE_iff]
  rw [noEdge_isComplete_iff] at hc
  simp only [noEdge_vertexSet, hc, true_and]
  obtain (rfl | ⟨x, rfl⟩) := hc.eq_empty_or_singleton
  · simp
  simp only [encard_singleton, cast_le_one, cast_lt_one, singleton_eq_singleton_iff, exists_eq',
    and_true]
  omega

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
  have := by simpa [hne, encard_pair] using h.le_card
  omega

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
    simpa [hne] using hcon
  rw [← banana_isComplete_iff] at h
  obtain rfl | hc := h
  · simp
  simp [hc]

@[simp]
lemma banana_connGE_iff : (banana u v F).ConnGE n ↔ n = 0 ∨ (n = 1 ∧ (u = v ∨ F.Nonempty)) := by
  obtain hc | hc := em ((banana u v F).IsComplete) |>.symm
  · simp [← banana_isComplete_iff, hc, ← preconnGE_iff_connGE_of_not_isComplete hc]
  simp only [hc.connGE_iff, banana_vertexSet, pair_subsingleton_iff, ← banana_isComplete_iff, hc,
    and_true]
  constructor
  · rintro (⟨rfl, hle⟩ | hlt)
    · simp only [mem_singleton_iff, insert_eq_of_mem, encard_singleton, cast_le_one] at hle
      omega
    have := encard_pair_le u v
    enat_to_nat!
    omega
  rintro (rfl | rfl)
  · simp
  obtain (rfl | hne) := eq_or_ne u v
  · simp
  simp [encard_pair hne]
