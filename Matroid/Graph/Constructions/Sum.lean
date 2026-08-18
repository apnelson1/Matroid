module

public import Matroid.Graph.Bipartite

@[expose] public section

open Set Function Option

namespace Graph


variable {α α' β β' α₁ α₂ β₁ β₂ γ : Type*} {x y : α} {e f : β} {G : Graph α β}

section directSum

variable {α₁ α₂ β₁ β₂ : Type*} {G₁ : Graph α₁ β₁} {G₂ : Graph α₂ β₂}

lemma stronglyDisjoint_map_inl_map_inr :
    StronglyDisjoint ((Sum.inl ''ᴳ G₁).edgeMap Sum.inl) ((.inr ''ᴳ G₂).edgeMap Sum.inr) :=
  ⟨by simp [disjoint_left], by simp [disjoint_left]⟩

/-- The direct sum of graphs with arbitrary vertex and edge types. TODO : direct `sigma` .-/
@[simps! vertexSet edgeSet]
def directSum (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) :
    Graph (α₁ ⊕ α₂) (β₁ ⊕ β₂) := Graph.copy
    (vertexSet := Sum.inl '' V(G₁) ∪ Sum.inr '' V(G₂))
    (edgeSet := Sum.inl '' E(G₁) ∪ Sum.inr '' E(G₂))
    (IsLink := fun e x y ↦
      match e, x, y with
      | .inl e, .inl x, .inl y => G₁.IsLink e x y
      | .inr e, .inr x, .inr y => G₂.IsLink e x y
      | _, _, _ => False)
    ((G₁.map Sum.inl).edgeMap Sum.inl (by simp +contextual) ∪
      (G₂.map Sum.inr).edgeMap Sum.inr (by simp +contextual))
    (by simp)
    (by simp)
    (by simp [stronglyDisjoint_map_inl_map_inr.compatible.union_isLink_iff])


lemma directSum_isLink_eq_match : (directSum G₁ G₂).IsLink = fun e x y ↦ match e, x, y with
  | .inl e, .inl x, .inl y => G₁.IsLink e x y
  | .inr e, .inr x, .inr y => G₂.IsLink e x y
  | _, _, _ => False := rfl

lemma directSum_inc_eq_match : (G₁.directSum G₂).Inc = fun e x ↦ match e, x with
    | .inl e, .inl x => G₁.Inc e x
    | .inr e, .inr x => G₂.Inc e x
    | _, _ => False := by
  ext e z
  cases e with cases z with simp [Inc, directSum_isLink_eq_match]

lemma directSum_isLink_inl_inl_iff_exists {e} {x y} :
    (G₁.directSum G₂).IsLink e (.inl x) (.inl y) ↔ ∃ e₀, e = .inl e₀ ∧ G₁.IsLink e₀ x y := by
  cases e with simp [directSum_isLink_eq_match]

lemma directSum_isLink_inl_iff_exists {e} {x y} :
    (G₁.directSum G₂).IsLink (.inl e) x y ↔
      (∃ x₀ y₀, G₁.IsLink e x₀ y₀ ∧ x = .inl x₀ ∧ y = .inl y₀) := by
  cases x with cases y with simp [directSum_isLink_eq_match]

lemma directSum_isLink_inr_iff_exists {e x y} :
    (G₁.directSum G₂).IsLink (.inr e) x y ↔
      (∃ x₀ y₀, G₂.IsLink e x₀ y₀ ∧ x = .inr x₀ ∧ y = .inr y₀) := by
  cases x with cases y with simp [directSum_isLink_eq_match]

@[simp]
lemma directSum_not_isLink_inl_inr_right {e x y} :
    ¬ (G₁.directSum G₂).IsLink (.inl e) x (.inr y) := by
  cases x with simp [directSum_isLink_eq_match]

@[simp]
lemma directSum_not_isLink_inl_inr_left {e x y} :
    ¬ (G₁.directSum G₂).IsLink (.inl e) (.inr x) y  := by
  simp [directSum_isLink_inl_iff_exists]

@[simp]
lemma directSum_not_isLink_inr_inl_right {e x y} :
    ¬ (G₁.directSum G₂).IsLink (.inr e) x (.inl y) := by
  cases x with simp [directSum_isLink_eq_match]

@[simp]
lemma directSum_not_isLink_inr_inl_left {e x y} :
    ¬ (G₁.directSum G₂).IsLink (.inr e) (.inl x) y  := by
  cases y with simp [directSum_isLink_eq_match]

@[simp]
lemma directSum_not_isLink_inl_inr {e x y} :
    ¬ (G₁.directSum G₂).IsLink e (.inl x) (.inr y)  := by
  cases e with simp

@[simp]
lemma directSum_not_isLink_inr_inl {e x y} :
    ¬ (G₁.directSum G₂).IsLink e (.inr x) (.inl y) := by
  cases e with simp

@[simp]
lemma directSum_isLink_inl_inl_inl_iff {e x y} :
    (G₁.directSum G₂).IsLink (.inl e) (.inl x) (.inl y) ↔ G₁.IsLink e x y := by
  simp [directSum_isLink_inl_inl_iff_exists]

@[simp]
lemma directSum_isLink_inr_inr_inr_iff {e x y} :
    (G₁.directSum G₂).IsLink (.inr e) (.inr x) (.inr y) ↔ G₂.IsLink e x y := by
  simp [directSum_isLink_eq_match]

lemma directSum_inc_iff {e x} :
    (G₁.directSum G₂).Inc e x ↔ (∃ e₀ x₀, G₁.Inc e₀ x₀ ∧ e = .inl e₀ ∧ x = .inl x₀) ∨
      (∃ e₀ x₀, G₂.Inc e₀ x₀ ∧ e = .inr e₀ ∧ x = .inr x₀) := by
  cases e with cases x with simp [directSum_inc_eq_match]

lemma directSum_inc_inl_iff {e x} :
    (G₁.directSum G₂).Inc (.inl e) x ↔ ∃ x₀, G₁.Inc e x₀ ∧ x = .inl x₀ := by
  simp [directSum_inc_iff]

lemma directSum_inc_inr_iff {e x} :
    (G₁.directSum G₂).Inc (.inr e) x ↔ ∃ x₀, G₂.Inc e x₀ ∧ x = .inr x₀ := by
  simp [directSum_inc_iff]

@[simp]
lemma directSum_not_inc_inl_inr {e x} : ¬ (G₁.directSum G₂).Inc (.inl e) (.inr x) := by
  simp [directSum_inc_iff]

@[simp]
lemma directSum_inc_inl_inl_iff {e x} : (G₁.directSum G₂).Inc (.inl e) (.inl x) ↔ G₁.Inc e x := by
  simp [directSum_inc_eq_match]

@[simp]
lemma directSum_inc_inr_inr_iff {e x} : (G₁.directSum G₂).Inc (.inr e) (.inr x) ↔ G₂.Inc e x := by
  simp [directSum_inc_eq_match]

@[simp]
lemma directSum_adj_inl_inl_iff {x y} : (G₁.directSum G₂).Adj (.inl x) (.inl y) ↔ G₁.Adj x y := by
  simp [Adj]

@[simp]
lemma directSum_adj_inr_inr_iff {x y} : (G₁.directSum G₂).Adj (.inr x) (.inr y) ↔ G₂.Adj x y := by
  simp [Adj]

@[simp]
lemma directSum_not_adj_inr_inl {x y} : ¬ (G₁.directSum G₂).Adj (.inr x) (.inl y) := by
  simp [Adj]

@[simp]
lemma directSum_not_adj_inl_inr {x y} : ¬ (G₁.directSum G₂).Adj (.inl x) (.inr y) := by
  simp [Adj]

lemma directSum_isLoopAt_iff {e x} : (G₁.directSum G₂).IsLoopAt e x ↔
    (∃ e₀ x₀, G₁.IsLoopAt e₀ x₀ ∧ e = .inl e₀ ∧ x = .inl x₀) ∨
    (∃ e₀ x₀, G₂.IsLoopAt e₀ x₀ ∧ e = .inr e₀ ∧ x = .inr x₀) := by
  simp_rw [IsLoopAt, directSum_isLink_eq_match]
  cases e with cases x with simp

lemma directSum_isNonLoopAt_iff {e x} : (G₁.directSum G₂).IsNonloopAt e x ↔
    (∃ e₀ x₀, G₁.IsNonloopAt e₀ x₀ ∧ e = .inl e₀ ∧ x = .inl x₀) ∨
    (∃ e₀ x₀, G₂.IsNonloopAt e₀ x₀ ∧ e = .inr e₀ ∧ x = .inr x₀) := by
  simp_rw [IsNonloopAt, directSum_isLink_eq_match]
  cases e with cases x with simp

@[simp]
lemma directSum_loopless_iff : (G₁.directSum G₂).Loopless ↔ G₁.Loopless ∧ G₂.Loopless := by
  simp +contextual [loopless_iff_forall_ne_of_adj]

@[simp]
lemma directSum_simple_iff : (G₁.directSum G₂).Simple ↔ G₁.Simple ∧ G₂.Simple := by
  simp +contextual only [simple_iff, directSum_loopless_iff, Sum.forall,
    directSum_not_isLink_inl_inr, forall_const, IsEmpty.forall_iff, implies_true, and_true,
    directSum_not_isLink_inr_inl, true_and, directSum_isLink_inl_inl_inl_iff,
    directSum_not_isLink_inl_inr_right, directSum_not_isLink_inr_inl_right,
    directSum_isLink_inr_inr_inr_iff, Sum.inl.injEq, reduceCtorEq, imp_false, Sum.inr.injEq]
  grind

instance Loopless.directSum_loopless [hG₁ : G₁.Loopless] [hG₂ : G₂.Loopless] :
    (G₁.directSum G₂).Loopless :=
  directSum_loopless_iff.2 ⟨hG₁, hG₂⟩

instance Simple.directSum_simple [hG₁ : G₁.Simple] [hG₂ : G₂.Simple] :
    (G₁.directSum G₂).Simple :=
  directSum_simple_iff.2 ⟨hG₁, hG₂⟩

lemma directSum_deleteVerts (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) (X : Set (α₁ ⊕ α₂)) :
    (G₁.directSum G₂) - X = (G₁ - (.inl ⁻¹' X)).directSum (G₂ - (.inr ⁻¹' X)) := by
  ext e x y
  · cases e with simp
  cases e with cases x with cases y with simp

lemma directSum_deleteVerts_left (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) (X : Set α₁) :
    (G₁.directSum G₂) - (.inl '' X) = (G₁ - X).directSum G₂ := by
  simp [directSum_deleteVerts]

lemma directSum_deleteVerts_right (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) (X : Set α₂) :
    (G₁.directSum G₂) - (.inr '' X) = G₁.directSum (G₂ - X) := by
  simp [directSum_deleteVerts]

lemma directSum_map_swap (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) :
    ((G₁.directSum G₂).map Sum.swap).edgeMap Sum.swap (by simp +contextual) = G₂.directSum G₁ :=
  ext_inc (by simp [image_union, image_image, union_comm]) (by simp [directSum_inc_eq_match])

@[simp]
lemma bot_directSum (G₂ : Graph α₂ β₂):
    (⊥ : Graph α₁ β₁).directSum G₂ = (G₂.map Sum.inr).edgeMap .inr :=
  ext_inc (by simp) <| by simp [directSum_inc_eq_match]

@[simp]
lemma directSum_bot (G₁ : Graph α₁ β₁) :
    G₁.directSum (⊥ : Graph α₂ β₂) = (G₁.map Sum.inl).edgeMap .inl  :=
  ext_inc (by simp) <| by simp [directSum_inc_eq_match]

lemma directSum_map (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) {φ : α₁ ⊕ α₂ → α} :
    (G₁.directSum G₂).map φ = ((G₁.map (φ ∘ Sum.inl)).directSum (G₂.map (φ ∘ Sum.inr))).map
      (Sum.elim id id) := by
  refine Graph.ext ?_ ?_
  · simp [Set.ext_iff]
  simp [directSum_isLink_eq_match]


lemma directSum_map_left (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) {φ : α₁ → α} :
    (φ ''ᴳ G₁).directSum G₂ = (G₁.directSum G₂).map (Sum.map φ id) := by
  ext e x y
  · simp
  cases e with cases x with cases y with simp

lemma directSum_map_right (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) {φ : α₂ → α} :
    G₁.directSum (φ ''ᴳ G₂) = (Sum.map id φ) ''ᴳ (G₁.directSum G₂) := by
  ext e x y
  · simp
  cases e with cases x with cases y with simp

@[simp]
lemma directSum_eq_bot_iff : G₁.directSum G₂ = ⊥ ↔ G₁ = ⊥ ∧ G₂ = ⊥ := by
  simp [← vertexSet_eq_empty_iff]

lemma directSum_connected_iff : (G₁.directSum G₂).Connected ↔
    (G₁ = ⊥ ∧ G₂.Connected) ∨ (G₁.Connected ∧ G₂ = ⊥) := by
  simp only [directSum, copy_eq]
  rw [connected_union_iff_of_disjoint (by simp), connected_edgeMap_iff, connected_edgeMap_iff,
    connected_map_iff_of_injOn (by simp), connected_map_iff_of_injOn (by simp)]
  simp

lemma directSum_preconnected_iff : (G₁.directSum G₂).Preconnected ↔
    (G₁ = ⊥ ∧ G₂.Preconnected) ∨ (G₁.Preconnected ∧ G₂ = ⊥) := by
  simp only [preconnected_iff, directSum_eq_bot_iff, directSum_connected_iff]
  tauto

lemma directSum_isComplete_iff :
    (G₁.directSum G₂).IsComplete ↔ G₁.IsComplete ∧ G₂ = ⊥ ∨ G₁ = ⊥ ∧ G₂.IsComplete := by
  obtain rfl | hne₁ := eq_or_ne G₁ ⊥
  · simp +contextual [isComplete_map_iff Sum.inr_injective.injOn, bot_isComplete]
  obtain rfl | hne₂ := eq_or_ne G₂ ⊥
  · simp +contextual [isComplete_map_iff Sum.inl_injective.injOn, bot_isComplete]
  refine iff_of_false (fun hc ↦ ?_) (by simp [hne₁, hne₂])
  simpa [directSum_preconnected_iff, hne₁, hne₂] using hc.preconnected

lemma directSum_eDegree_inl (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) (x : α₁) :
    (G₁.directSum G₂).eDegree (.inl x) = G₁.eDegree x := by
  simp only [eDegree_eq_encard_add_encard, directSum_isLoopAt_iff, Sum.inl.injEq,
    exists_eq_right_right', reduceCtorEq, and_false, exists_false, or_false]
  rw [← encard_preimage_of_injective_subset_range (@Sum.inl_injective β₁ β₂),
    ← encard_preimage_of_injective_subset_range (@Sum.inl_injective β₁ β₂)]
  · simp [directSum_isNonLoopAt_iff]
  · simp [subset_def, directSum_isNonLoopAt_iff]
  simp [subset_def]

lemma directSum_eDegree_inr (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) (x : α₂) :
    (G₁.directSum G₂).eDegree (.inr x) = G₂.eDegree x := by
  rw [← directSum_map_swap, eDegree_edgeMap _ _ (by simp [InjOn]), ← Sum.swap_inl,
    eDegree_map_of_injective _ _ (by simp [Function.Injective]), directSum_eDegree_inl]

end directSum

section directEdgeSum

variable {β₁ β₂ : Type*} {G₁ : Graph α β₁} {G₂ : Graph α β₂}

/-- The edge-union of two graphs with the same vertex type, where the edge type is a sum. -/
@[simps! vertexSet edgeSet]
def directEdgeSum (G₁ : Graph α β₁) (G₂ : Graph α β₂) : Graph α (β₁ ⊕ β₂) :=
    Graph.copy (vertexSet := V(G₁) ∪ V(G₂)) (edgeSet := Sum.inl '' E(G₁) ∪ Sum.inr '' E(G₂))
    (IsLink := fun e x y ↦ match e, x, y with
      | .inl e, x, y => G₁.IsLink e x y
      | .inr e, x, y => G₂.IsLink e x y )
    ((G₁.edgeMap Sum.inl) ∪ (G₂.edgeMap Sum.inr))
    (by simp)
    (by simp)
    (by
      intro e x y
      rw [(Compatible.of_disjoint_edgeSet (by simp)).union_isLink_iff]
      cases e with simp)

lemma directEdgeSum_isLink_eq_match (G₁ : Graph α β₁) (G₂ : Graph α β₂) :
    (G₁.directEdgeSum G₂).IsLink = fun e x y ↦ match e, x, y with
      | .inl e, x, y => G₁.IsLink e x y
      | .inr e, x, y => G₂.IsLink e x y := rfl

@[simp]
lemma directEdgeSum_isLink_inl_iff {e x y} :
    (G₁.directEdgeSum G₂).IsLink (.inl e) x y ↔ G₁.IsLink e x y := by
  simp [directEdgeSum_isLink_eq_match]

@[simp]
lemma directEdgeSum_isLink_inr_iff {e x y} :
    (G₁.directEdgeSum G₂).IsLink (.inr e) x y ↔ G₂.IsLink e x y := by
  simp [directEdgeSum_isLink_eq_match]

@[simp]
lemma directEdgeSum_inc_inl_iff {e x} : (G₁.directEdgeSum G₂).Inc (.inl e) x ↔ G₁.Inc e x := by
  simp [Inc]

@[simp]
lemma directEdgeSum_inc_inr_iff {e x} : (G₁.directEdgeSum G₂).Inc (.inr e) x ↔ G₂.Inc e x := by
  simp [Inc]

@[simp]
lemma directEdgeSum_adj_iff {x y} : (G₁.directEdgeSum G₂).Adj x y ↔ G₁.Adj x y ∨ G₂.Adj x y := by
  simp [Adj]

@[simp]
lemma directEdgeSum_isNonloopAt_inl_iff {e x} :
    (G₁.directEdgeSum G₂).IsNonloopAt (.inl e) x ↔ G₁.IsNonloopAt e x := by
  simp [IsNonloopAt]

@[simp]
lemma directEdgeSum_isNonloopAt_inr_iff {e x} :
    (G₁.directEdgeSum G₂).IsNonloopAt (.inr e) x ↔ G₂.IsNonloopAt e x := by
  simp [IsNonloopAt]

@[simp]
lemma directEdgeSum_isLoopAt_inl_iff {e x} :
    (G₁.directEdgeSum G₂).IsLoopAt (.inl e) x ↔ G₁.IsLoopAt e x := by
  simp_rw [IsLoopAt, directEdgeSum_isLink_inl_iff]

@[simp]
lemma directEdgeSum_isLoopAt_inr_iff {e x} :
    (G₁.directEdgeSum G₂).IsLoopAt (.inr e) x ↔ G₂.IsLoopAt e x := by
  simp_rw [IsLoopAt, directEdgeSum_isLink_inr_iff]

lemma directEdgeSum_comm (G₁ : Graph α β₁) (G₂ : Graph α β₂) :
    (G₁.directEdgeSum G₂) = (G₂.directEdgeSum G₁).edgeMap Sum.swap := by
  ext e x y
  · simp [or_comm]
  cases e with simp

@[simp]
lemma directSum_map_elim (G₁ : Graph α₁ β₁) (G₂ : Graph α₂ β₂) {φ₁ : α₁ → α} {φ₂ : α₂ → α} :
    (G₁.directSum G₂).map (Sum.elim φ₁ φ₂) = (φ₁ ''ᴳ G₁).directEdgeSum (φ₂ ''ᴳ G₂) := by
  ext e x y
  · simp
  cases e with simp

@[simp]
lemma directEdgeSum_eDegree (G₁ : Graph α β₁) (G₂ : Graph α β₂) (x : α) :
    (G₁.directEdgeSum G₂).eDegree x = G₁.eDegree x + G₂.eDegree x := by
  rw [eDegree_eq_encard_add_encard,
    ← image_preimage_inl_union_image_preimage_inr {e | (G₁.directEdgeSum G₂).IsLoopAt e x},
    ← image_preimage_inl_union_image_preimage_inr {e | (G₁.directEdgeSum G₂).IsNonloopAt e x},
    encard_union_eq disjoint_image_inl_image_inr, encard_union_eq disjoint_image_inl_image_inr,
    mul_add, Sum.inl_injective.encard_image, Sum.inl_injective.encard_image,
      Sum.inr_injective.encard_image, Sum.inr_injective.encard_image]
  simp only [preimage_ofPred_eq, directEdgeSum_isLoopAt_inl_iff, directEdgeSum_isLoopAt_inr_iff,
    directEdgeSum_isNonloopAt_inl_iff, directEdgeSum_isNonloopAt_inr_iff,
    eDegree_eq_encard_add_encard]
  enat_to_nat!
  lia

@[simp]
lemma directEdgeSum_loopless_iff : (G₁.directEdgeSum G₂).Loopless ↔ G₁.Loopless ∧ G₂.Loopless := by
  simp only [loopless_iff_forall_ne_of_adj, directEdgeSum_adj_iff, ne_eq]
  grind

@[simp]
lemma directEdgeSum_deleteVerts (G₁ : Graph α β₁) (G₂ : Graph α β₂) (X : Set α) :
    (G₁.directEdgeSum G₂) - X = (G₁ - X).directEdgeSum (G₂ - X) :=
  ext_inc (by simp [union_sdiff_distrib]) <| by rintro (e | e) <;> simp

lemma directEdgeSum_simple_iff :
    (G₁.directEdgeSum G₂).Simple ↔ G₁.Simple ∧ G₂.Simple ∧ ∀ x y, ¬ (G₁.Adj x y ∧ G₂.Adj x y) := by
  simp only [simple_iff, directEdgeSum_loopless_iff, Sum.forall, directEdgeSum_isLink_inl_iff,
    directEdgeSum_isLink_inr_iff, Sum.inl.injEq, reduceCtorEq, imp_false, Sum.inr.injEq, Adj,
    not_and, not_exists, forall_exists_index]
  grind

lemma directEdgeSum_isComplete_iff :
    (G₁.directEdgeSum G₂).IsComplete ↔ ∀ x y, x ∈ V(G₁) ∪ V(G₂) → y ∈ V(G₁) ∪ V(G₂) → x ≠ y →
      G₁.Adj x y ∨ G₂.Adj x y := by
  simp only [IsComplete, vertexSet_directEdgeSum, mem_union, ne_eq, directEdgeSum_adj_iff]
  grind

@[simp]
lemma directEdgeSum_noEdge_right (G₁ : Graph α β₁) (V : Set α) :
    G₁.directEdgeSum (noEdge V β₂) = (G₁.edgeMap Sum.inl)[V(G₁) ∪ V] := by
  ext e x y
  · simp
  obtain (e | e) := e
  · suffices G₁.IsLink e x y → (x ∈ V(G₁) ∨ x ∈ V) ∧ (y ∈ V(G₁) ∨ y ∈ V) by simpa
    exact fun h ↦ ⟨.inl h.left_mem, .inl h.right_mem⟩
  simp

@[simp]
lemma directEdgeSum_noEdge_left (G₂ : Graph α β₂) (V : Set α) :
    (noEdge V β₁).directEdgeSum G₂ = (G₂.edgeMap Sum.inr)[V(G₂) ∪ V] := by
  ext e x y
  · simp [or_comm]
  obtain (e | e) := e
  · simp
  suffices G₂.IsLink e x y → (x ∈ V(G₂) ∨ x ∈ V) ∧ (y ∈ V(G₂) ∨ y ∈ V) by simpa
  exact fun h ↦ ⟨.inl h.left_mem, .inl h.right_mem⟩

lemma le_directEdgeSum_left (G₁ : Graph α β₁) (G₂ : Graph α β₂) :
    (G₁.edgeMap Sum.inl) ≤ G₁.directEdgeSum G₂ := by
  constructor <;> simp

lemma le_directEdgeSum_right (G₁ : Graph α β₁) (G₂ : Graph α β₂) :
    (G₂.edgeMap Sum.inr) ≤ G₁.directEdgeSum G₂ := by
  constructor <;> simp

lemma isSpanningSubgraph_directEdgeSum_left (hG : V(G₂) ⊆ V(G₁)) :
    (G₁.edgeMap Sum.inl) ≤s G₁.directEdgeSum G₂ := by
  rw [isSpanningSubgraph_iff, and_iff_right (by simpa using le_directEdgeSum_left ..)]
  simp [union_eq_self_of_subset_right hG]

lemma isSpanningSubgraph_directEdgeSum_right (hG : V(G₁) ⊆ V(G₂)) :
    (G₂.edgeMap Sum.inr) ≤s G₁.directEdgeSum G₂ := by
  rw [isSpanningSubgraph_iff, and_iff_right (by simpa using le_directEdgeSum_right ..)]
  simp [union_eq_self_of_subset_left hG]

lemma Preconnected.directEdgeSum_preconnected_right (hG₁ : G₁.Preconnected) (hG₂ : V(G₂) ⊆ V(G₁)) :
    (G₁.directEdgeSum G₂).Preconnected :=
  Preconnected.of_isSpanningSubgraph (by simpa) (isSpanningSubgraph_directEdgeSum_left hG₂)

lemma Preconnected.directEdgeSum_preconnected_left (hG₂ : G₂.Preconnected) (hG₁ : V(G₁) ⊆ V(G₂)) :
    (G₁.directEdgeSum G₂).Preconnected :=
  Preconnected.of_isSpanningSubgraph (by simpa) (isSpanningSubgraph_directEdgeSum_right hG₁)

end directEdgeSum

variable {γ : Type*} {A : Set γ}

def multiApex (G : Graph α β) (A : Set γ) : Graph (α ⊕ γ) (β ⊕ (α × γ)) := Graph.directEdgeSum
    ((G.directSum (noEdge A Empty)).edgeMap (Sum.elim id Empty.elim))
    (completeBipartiteGraphOn V(G) A)

@[simp]
lemma multiApex_vertexSet (G : Graph α β) (A : Set γ) :
    V(G.multiApex A) = .inl '' V(G) ∪ .inr '' A := by
  simp [multiApex]

@[simp]
lemma multiApex_edgeSet (G : Graph α β) (A : Set γ) :
    E(G.multiApex A) = .inl '' E(G) ∪ .inr '' (V(G) ×ˢ A) := by
  simp [multiApex, Set.ext_iff]

lemma multiApex_isLink_eq_match : (multiApex G A).IsLink = fun e x y ↦ match e, x, y with
    | .inl e, .inl x, .inl y => G.IsLink e x y
    | .inr ⟨u, a⟩, .inl x, .inr y => u ∈ V(G) ∧ a ∈ A ∧ x = u ∧ y = a
    | .inr ⟨u, a⟩, .inr x, .inl y => u ∈ V(G) ∧ a ∈ A ∧ y = u ∧ x = a
    | _, _, _ => False := by
  simp only [multiApex, directEdgeSum_isLink_eq_match, edgeMap_isLink, directSum_isLink_eq_match,
    edgeSet_noEdge, mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet,
    Sum.exists, Sum.elim_inl, id_eq, exists_eq_left, Sum.elim_inr, Sum.inr.injEq, imp_false,
    IsEmpty.forall_iff, and_false, IsEmpty.exists_iff, or_false, completeBipartiteGraphOn_isLink]
  ext e x y
  cases e with cases x with cases y with grind

lemma multiApex_isLink_inl_eq_match {e x y} : (multiApex G A).IsLink (.inl e) x y ↔ match x, y with
    | .inl x, .inl y => G.IsLink e x y
    | _, _ => false := by
  cases x with cases y with simp [multiApex_isLink_eq_match]

lemma multiApex_isLink_inr_eq_match {e x y} : (multiApex G A).IsLink (.inr e) x y ↔ match x, y with
    | .inl x, .inr y => e.1 ∈ V(G) ∧ e.2 ∈ A ∧ x = e.1 ∧ y = e.2
    | .inr x, .inl y => e.1 ∈ V(G) ∧ e.2 ∈ A ∧ x = e.2 ∧ y = e.1
    | _, _ => False := by
  cases e with cases x with cases y with simp +contextual [multiApex_isLink_eq_match, iff_def]

lemma multiApex_inc_eq : (multiApex G A).Inc = fun e x ↦ match e, x with
    | .inl e, .inl x => G.Inc e x
    | .inr ⟨u, a⟩, .inl x => u ∈ V(G) ∧ a ∈ A ∧ x = u
    | .inr ⟨u, a⟩, .inr x => u ∈ V(G) ∧ a ∈ A ∧ x = a
    | _, _ => False := by
  ext e z
  cases e with cases z with simp [Inc, multiApex_isLink_eq_match]

@[simp]
lemma multiApex_loopless_iff : (G.multiApex A).Loopless ↔ G.Loopless := by
  simp [multiApex, completeBipartiteGraphOn_loopless]

@[simp]
lemma multiApex_simple_iff : (G.multiApex A).Simple ↔ G.Simple := by
  simp [multiApex, directEdgeSum_simple_iff, edgeMap_simple_iff_of_injOn]

@[simp]
lemma multiApex_empty : (G.multiApex (∅ : Set γ)) = (G.map Sum.inl).edgeMap Sum.inl :=
  ext_inc (by simp [multiApex]) (by simp [multiApex_inc_eq])

lemma multiApex_preconnected_iff :
    (G.multiApex A).Preconnected ↔ ((G = ⊥ → A.Subsingleton) ∧ (A = ∅ → G.Preconnected)) := by
  obtain rfl | hne := eq_or_ne G ⊥
  · simp [multiApex, Sum.inr_injective.subsingleton_image_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp [preconnected_map_iff_of_injOn Sum.inl_injective.injOn]
  refine iff_of_true ?_ (by simp [hne, hA.ne_empty])
  refine Preconnected.directEdgeSum_preconnected_left ?_ (by simp)
  simp [completeBipartiteGraphOn_preconnected_iff, hA.ne_empty, hne]

lemma multiApex_connected_iff :
    (G.multiApex A).Connected ↔ (A = ∅ → G.Connected) ∧ (G = ⊥ → A.Subsingleton) := by
  obtain rfl | hne := A.eq_empty_or_nonempty
  · simp [connected_iff, preconnected_map_iff_of_injOn]
  simp [hne.ne_empty, connected_iff, multiApex_preconnected_iff, hne]

@[simp]
lemma multiApex_isComplete_iff : (G.multiApex A).IsComplete ↔ G.IsComplete ∧ A.Subsingleton := by
  simp_rw [multiApex, directEdgeSum_isComplete_iff]
  simp only [vertexSet_edgeMap, vertexSet_directSum, vertexSet_noEdge,
    vertexSet_completeBipartiteGraphOn, union_self, mem_union, mem_image, ne_eq, edgeMap_adj_iff,
    Sum.forall, Sum.inl.injEq, exists_eq_right, reduceCtorEq, Sum.inr.injEq,
    directSum_adj_inl_inl_iff, completeBipartiteGraphOn_not_adj_inl_inl,
    directSum_not_adj_inl_inr, completeBipartiteGraphOn_adj_inl_inr_iff,
    directSum_not_adj_inr_inl, completeBipartiteGraphOn_adj_inr_inl_iff,
    directSum_adj_inr_inr_iff, noEdge_not_adj, completeBipartiteGraphOn_not_adj_inr_inr,
    IsComplete, Set.Subsingleton]
  grind

lemma multiApex_deleteVerts_left (G : Graph α β) (X : Set α) :
    (G - X).multiApex A = (G.multiApex A) - (.inl '' X) := by
  rw! [multiApex, multiApex, ← directSum_deleteVerts_left,
    edgeMap_deleteVerts _ (by simp +contextual), vertexSet_deleteVerts,
    completeBipartiteGraphOn_sdiff_left, ← directEdgeSum_deleteVerts]
  rfl

lemma multiApex_sdiff_right (G : Graph α β) (X : Set γ) :
    G.multiApex (A \ X) = G.multiApex A - (.inr '' X) := by
  simp only [multiApex, directEdgeSum_deleteVerts, ← noEdge_deleteVerts,
    ← directSum_deleteVerts_right, completeBipartiteGraphOn_sdiff_right]
  rw [edgeMap_deleteVerts]

lemma multiApex_eDegree_inr (G : Graph α β) {a} (ha : a ∈ A) :
    (G.multiApex A).eDegree (.inr a) = V(G).encard := by
  simp [multiApex, completeBipartiteGraphOn_eDegree_inr ha, eDegree_edgeMap, directSum_eDegree_inr]

lemma multiApex_eDegree_inl (G : Graph α β) {x} (ha : x ∈ V(G)) :
    (G.multiApex A).eDegree (.inl x) = G.eDegree x + A.encard := by
  simp [multiApex, completeBipartiteGraphOn_eDegree_inl ha, eDegree_edgeMap, directSum_eDegree_inl]

/-- The graph with vertices `V(G) ∪ {none}` and edges `E(G) ∪ V(G)`,
where the new edges go to the apex vertex. -/
@[simps! vertexSet edgeSet]
def apex (G : Graph α β) : Graph (Option α) (β ⊕ α) := Graph.copy
  (vertexSet := insert none (some '' V(G)))
  (edgeSet := .inl '' E(G) ∪ .inr '' V(G))
  (IsLink := fun e x y ↦ match e, x, y with
    | Sum.inl e, some x, some y => G.IsLink e x y
    | Sum.inr e, some x, none => x ∈ V(G) ∧ e = x
    | Sum.inr e, none, some x => x ∈ V(G) ∧ e = x
    | _, _, _ => False)
  (G := ((G.multiApex (univ : Set Unit)).map (Sum.elim some (fun _ ↦ none))).edgeMap
    (Sum.elim Sum.inl (fun x ↦ .inr x.1)))
  (by simp [Set.ext_iff, multiApex, or_comm, eq_comm (a := none)])
  (by simp [Set.ext_iff, multiApex])
  (by
    suffices  ∀ (b x : α), x = b ∧ x ∈ V(G) ↔ x ∈ V(G) ∧ b = x by
      simpa [multiApex_isLink_eq_match, Option.forall]
    grind )

lemma apex_isLink_eq_match (G : Graph α β) : G.apex.IsLink = fun e x y ↦ match e, x, y with
    | Sum.inl e, some x, some y => G.IsLink e x y
    | Sum.inr e, some x, none => x ∈ V(G) ∧ e = x
    | Sum.inr e, none, some x => x ∈ V(G) ∧ e = x
    | _, _, _ => False := rfl

@[simp]
lemma apex_isLink_inl_iff {e : β} {x y : α} :
    G.apex.IsLink (.inl e) (some x) (some y) ↔ G.IsLink e x y := by
  simp [apex_isLink_eq_match]

@[simp]
lemma apex_isLink_inr_left_iff {e : α} {x : α} :
    G.apex.IsLink (.inr e) (some x) none ↔ x ∈ V(G) ∧ e = x := by
  simp [apex_isLink_eq_match]

@[simp]
lemma apex_isLink_inr_right_iff {e : α} {x : α} :
    G.apex.IsLink (.inr e) none (some x) ↔ x ∈ V(G) ∧ e = x := by
  rw [isLink_comm, apex_isLink_inr_left_iff]

@[simp]
lemma apex_isLoopAt_none {e} : ¬ G.apex.IsLoopAt e none := by
  simp_rw [IsLoopAt, apex_isLink_eq_match]
  simp

@[simp]
lemma apex_not_isLink_inl_none_left {e : β} {x : Option α} :
    ¬ G.apex.IsLink (.inl e) none x := by
  simp [apex_isLink_eq_match]

@[simp]
lemma apex_not_isLink_inl_none_right {e : β} {x : Option α} :
    ¬ G.apex.IsLink (.inl e) x none := by
  simp [apex_isLink_eq_match]

@[simp]
lemma apex_not_isLink_inr_some_some {e : α} {x y : α} :
    ¬ G.apex.IsLink (.inr e) (some x) (some y) := by
  simp [apex_isLink_eq_match]

lemma apex_inc_eq_match : G.apex.Inc = fun e x ↦ match e, x with
    | .inl e, some x => G.Inc e x
    | .inr y, some x => x ∈ V(G) ∧ x = y
    | .inr y, none => y ∈ V(G)
    | _, _ => False := by
  ext e x
  cases e with cases x with simp [Inc, apex_isLink_eq_match, Option.exists, eq_comm]

@[simp]
lemma apex_adj_some_some_iff {x y : α} :
    G.apex.Adj (some x) (some y) ↔ G.Adj x y := by
  simp [Adj]

@[simp]
lemma apex_adj_some_none {x : α} :
    G.apex.Adj (some x) none ↔ x ∈ V(G) := by
  simp [Adj]

@[simp]
lemma apex_adj_none_some {x : α} :
    G.apex.Adj none (some x) ↔ x ∈ V(G) := by
  simp [Adj]

@[simp]
lemma apex_isLoopAt_inl {e : β} {x : α} :
    G.apex.IsLoopAt (.inl e) (some x) ↔ G.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma apex_not_isLoopAt_inr (G : Graph α β) {y : Option α} {e} :
    ¬ G.apex.IsLoopAt (.inr e) y := by
  cases y with simp [← isLink_self_iff, apex_isLink_eq_match]

@[simp]
lemma apex_not_isLoopAt_none (G : Graph α β) {e : β ⊕ α} :
    ¬ G.apex.IsLoopAt e none := by
  obtain b | a := e
  · rw [← isLink_self_iff]
    exact apex_not_isLink_inl_none_right
  simp

@[simp]
lemma apex_not_adj_none (G : Graph α β) : ¬ G.apex.Adj none none := by
  simp [Adj]

@[simp]
lemma apex_loopless_iff : G.apex.Loopless ↔ G.Loopless := by
  rw [apex, copy_eq, edgeMap_loopless_iff, map_loopless_iff_of_injOn (by simp),
    multiApex_loopless_iff]

alias ⟨_, Loopless.apex_loopless⟩ := apex_loopless_iff

@[simp]
lemma apex_simple_iff : G.apex.Simple ↔ G.Simple := by
  simp [apex, edgeMap_simple_iff_of_injOn, map_simple_iff_of_injOn]

alias ⟨_, Simple.apex_simple⟩ := apex_simple_iff

lemma apex_connected (G : Graph α β) : G.apex.Connected := by
  simp [apex, multiApex_connected_iff, subsingleton_iff]

lemma apex_delete_none (G : Graph α β) : G.apex - {none} = (G.map Option.some).edgeMap Sum.inl := by
  refine eq_map_edgeMap_of_forall_inc (by simp) (by simp) ?_ ?_
  · simp [apex_inc_eq_match]
  simp [apex_inc_eq_match, Option.forall]

lemma apex_deleteVerts (G : Graph α β) (X : Set α) : (G - X).apex = G.apex - (some '' X) := by
  rw! [apex, copy_eq, multiApex_deleteVerts_left, map_deleteVerts_of_injective
    (by simp [Injective]), edgeMap_deleteVerts _ (by simp +contextual), apex, copy_eq,
    image_image]
  simp

lemma apex_eDegree {v : α} (hv : v ∈ V(G)) : G.apex.eDegree v = G.eDegree v + 1 := by
  simp [apex, eDegree_edgeMap]
  rw [show some v = (Sum.elim some fun x ↦ none) (.inl v : α ⊕ Unit) from rfl,
    eDegree_map_of_injective, multiApex_eDegree_inl _ hv]
  · simp
  simp [some_injective, subsingleton_iff]

lemma PreconnGE.apex {n : ℕ} (hG : G.PreconnGE n) : G.apex.PreconnGE (n + 1) := by
  refine PreconnGE.preconnGE_add_one_of_delete_of_forall_adj (v := none) ?_ <| by simp
  rwa [apex_delete_none, preconnGE_edgeMap_iff, preconnGE_map_iff_of_injOn (by simp)]

lemma ConnGE.apex {n : ℕ} (hG : G.ConnGE n) (hnt : V(G).Nontrivial) : G.apex.ConnGE (n + 1) := by
  refine ConnGE.connGE_add_one_of_delete_of_forall_adj (v := none) ?_ ?_ (by simp)
  · rwa [apex_delete_none, connGE_edgeMap_iff, connGE_map_iff_of_injOn (by simp)]
  simp only [vertexSet_apex]
  grw [encard_insert_of_notMem (by simp), (Option.some_injective _).encard_image,
  ← two_le_encard_iff_nontrivial.2 hnt, show (3 : ℕ∞) = 2 + 1 from rfl]

lemma IsWalk.isWalk_apex {W} (hW : G.IsWalk W) :
    G.apex.IsWalk ((W.map Option.some).edgeMap Sum.inl) := by
  replace hW := (hW.map some).edgeMap (@Sum.inl β α) (by simp +contextual)
  rw [← apex_delete_none] at hW
  exact hW.of_le (by simp)

lemma IsPath.isPath_apex {P} (hP : G.IsPath P) :
    G.apex.IsPath ((P.map Option.some).edgeMap Sum.inl) := by
  replace hP := (hP.map (some_injective _).injOn).edgeMap (@Sum.inl β α) (by simp)
  rw [← apex_delete_none] at hP
  exact hP.of_le (by simp)

/-- Any nontrivial path in `G` can be extended to a cycle of `G.apex` via the apex. -/
lemma IsPath.isCyclicWalk_apex {P} (hP : G.IsPath P) (hPne : P.Nonempty) :
    G.apex.IsCyclicWalk <|
    (((P.map Option.some).edgeMap Sum.inl).cons none (.inr P.first)).concat (.inr P.last) none := by
  have hP' := hP.isPath_apex.cons (x := none) (e := Sum.inr P.first) (by simp [hP.isWalk.first_mem])
    (by simp)
  exact hP'.concat_isCyclicWalk (by simp [hP.isWalk.last_mem]) <| by
    simpa [eq_comm, hP.first_eq_last_iff]

lemma apex_isBond_setLinkEdges_singleton (G : Graph α β) (hx : x ∈ V(G)) :
    G.apex.IsBond (δ(G.apex, {some x})) := by
  refine isBond_of_conn (by simpa) (preconnected_of_vertexSet_subsingleton (by simp)) ?_ ?_
  · rw [← image_singleton, ← apex_deleteVerts]
    exact (apex_connected ..).pre
  refine ⟨.inr x, ?_⟩
  simp only [vertexSet_apex, mem_setLinkEdges_iff, mem_singleton_iff, mem_sdiff, mem_insert_iff,
    mem_image, exists_eq_left]
  refine ⟨none, by simpa⟩
