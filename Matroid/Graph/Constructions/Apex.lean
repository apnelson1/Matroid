module

public import Matroid.Graph.Bipartite

@[expose] public section

open Set

namespace Graph


variable {α α' β β' γ : Type*} {x y : α} {e f : β} {G : Graph α β}

-- def completeJoin_disjoint_aux (G : Graph α β) (G' : Graph α' β') :
--     Disjoint ()

-- def completeJoin (G : Graph α β) (G' : Graph α' β') : Graph (α ⊕ α') (β ⊕ β ⊕ (α × α')) :=



-- def multiApex (G : Graph α β) (γ : Type*) : Graph (α ⊕ γ) (β ⊕ (α × γ)) :=
    -- ((G.map Sum.inl).edgeMap Sum.inl) (by simp +contextual) ∪
    --   (((completeBipartiteGraphOn V(G) γ).map (Sum.map Subtype.val id)).edgeMap
    --   (Sum.inr ∘ Prod.map Subtype.val id)) (by simp +contextual)

@[simp]
lemma multiApex_compatible (G : Graph α β) (γ : Type*) :
    Graph.Compatible (((G.map Sum.inl).edgeMap Sum.inl) (by simp +contextual))
      (((completeBipartiteGraphOn V(G) γ).map (Sum.map Subtype.val id)).edgeMap
        (Sum.inr ∘ Prod.map Subtype.val id) (by simp +contextual)) := by
  rintro e he ⟨a, -, rfl⟩
  simp at he

/-- Add some new vertices to a graph that are adjacent to all existing vertices.
The new vertices are identified with a type `γ`, and the new edges with terms in `α × γ`. -/
@[simps! vertexSet edgeSet]
def multiApex (G : Graph α β) (γ : Type*) : Graph (α ⊕ γ) (β ⊕ (α × γ)) := Graph.copy
  (G :=
    ((G.map Sum.inl).edgeMap Sum.inl) (by simp +contextual) ∪
    (((completeBipartiteGraphOn V(G) γ).map (Sum.map Subtype.val id)).edgeMap
    (Sum.inr ∘ Prod.map Subtype.val id)) (by simp +contextual))
  (vertexSet := Sum.inl '' V(G) ∪ Set.range .inr)
  (edgeSet := Sum.inl '' E(G) ∪ (.inr '' (Prod.fst ⁻¹' V(G))))
  (IsLink := fun e x y ↦ match e, x, y with
    | .inl e, .inl x, .inl y => G.IsLink e x y
    | .inr e, .inl x, .inr y => x ∈ V(G) ∧ x = e.1 ∧ y = e.2
    | .inr e, .inr x, .inl y => y ∈ V(G) ∧ x = e.2 ∧ y = e.1
    | _, _, _ => False)
  (by simp [Set.ext_iff])
  (by simp [Set.ext_iff])
  (by
    simp_rw [(G.multiApex_compatible γ).union_isLink_iff]
    simp
    suffices aux : ∀ (a : α) (b c : γ), ∀ x ∈ V(G), x = a ∧ c = b ↔ c = b ∧ x = a by simpa
    simp [and_comm])

lemma multiApex_isLink_eq : (multiApex G γ).IsLink = fun e x y ↦ match e, x, y with
    | .inl e, .inl x, .inl y => G.IsLink e x y
    | .inr e, .inl x, .inr y => x ∈ V(G) ∧ x = e.1 ∧ y = e.2
    | .inr e, .inr x, .inl y => y ∈ V(G) ∧ x = e.2 ∧ y = e.1
    | _, _, _ => False := rfl

lemma multiApex_inc_eq : (multiApex G γ).Inc = fun e x ↦ match e, x with
    | .inl e, .inl x => G.Inc e x
    | .inr e, .inl x => x ∈ V(G) ∧ x = e.1
    | .inr e, .inr x => e.1 ∈ V(G) ∧ x = e.2
    | _, _ => False := by
  ext e z
  cases e with cases z with simp [Inc, multiApex_isLink_eq]

lemma multiApex_isLink_inl_inl_iff_exists {e} {x y : α} :
    (G.multiApex γ).IsLink e (.inl x) (.inl y) ↔ ∃ e₀, e = .inl e₀ ∧ G.IsLink e₀ x y := by
  cases e with simp [multiApex_isLink_eq]

lemma multiApex_isLink_inl_iff_exists {e} {x y} :
    (G.multiApex γ).IsLink (.inl e) x y ↔ (∃ x₀ y₀, G.IsLink e x₀ y₀ ∧ x = .inl x₀ ∧ y = .inl y₀) := by
  cases x with cases y with simp [multiApex_isLink_eq]

@[simp]
lemma multiApex_not_isLink_inl_inr_right {e x y} :
    ¬ (G.multiApex γ).IsLink (.inl e) x (.inr y) := by
  cases x with simp [multiApex_isLink_eq]

@[simp]
lemma multiApex_not_isLink_inl_inr {e x y} :
    ¬ (G.multiApex γ).IsLink (.inl e) (.inr x) y  := by
  simp [multiApex_isLink_inl_iff_exists]

@[simp]
lemma multiApex_isLink_inl_inl_inl_iff {e : β} {x y : α} :
    (G.multiApex γ).IsLink (.inl e) (.inl x) (.inl y) ↔ G.IsLink e x y := by
  simp [multiApex_isLink_inl_inl_iff_exists]

@[simp]
lemma multiApex_not_isLink_inr_inl_inl {e} {x y : α} :
    ¬ (G.multiApex γ).IsLink (.inr e) (.inl x) (.inl y) := by
  simp [multiApex_isLink_inl_inl_iff_exists]

lemma multiApex_isLink_inr_iff {e} {x y : α ⊕ γ} : (G.multiApex γ).IsLink (.inr e) x y ↔
      (x = .inl e.1 ∧ e.1 ∈ V(G) ∧ y = .inr e.2) ∨ (x = .inr e.2 ∧ y = .inl e.1 ∧ e.1 ∈ V(G)) := by
  cases x with cases y with cases e with (simp only [multiApex_isLink_eq]; grind)

@[simp]
lemma multiApex_isLink_inr_inl_iff {e} {x : α} {y : α ⊕ γ} :
    (G.multiApex γ).IsLink (.inr e) (.inl x) y ↔ x = e.1 ∧ x ∈ V(G) ∧ y = .inr e.2 := by
  simp +contextual [multiApex_isLink_inr_iff]

@[simp]
lemma multiApex_isLink_inr_inl_iff' {e} {x : α ⊕ γ} {y : α} :
    (G.multiApex γ).IsLink (.inr e) x (.inl y) ↔ x = .inr e.2 ∧ y = e.1 ∧ y ∈ V(G) := by
  simp +contextual [multiApex_isLink_inr_iff]

@[simp]
lemma multiApex_isLink_inr_inr_iff {e} {x : γ} {y : α ⊕ γ} :
    (G.multiApex γ).IsLink (.inr e) (.inr x) y ↔ x = e.2 ∧ y = .inl e.1 ∧ e.1 ∈ V(G) := by
  simp [multiApex_isLink_inr_iff]

@[simp]
lemma multiApex_isLink_inr_inr_iff' {e} {x : α ⊕ γ} {y : γ} :
    (G.multiApex γ).IsLink (.inr e) x (.inr y) ↔ x = .inl e.1 ∧ e.1 ∈ V(G) ∧ y = e.2 := by
  simp [multiApex_isLink_inr_iff]

@[simp]
lemma multiApex_not_isLink_inr_right {e} {x y} : ¬ (G.multiApex γ).IsLink e (.inr x) (.inr y) := by
  cases e with simp

lemma multiApex_inc_iff {e x} :
    (G.multiApex γ).Inc e x ↔ (∃ e₀ x₀, x₀ ∈ V(G) ∧ G.Inc e₀ x₀ ∧ e = .inl e₀ ∧ x = .inl x₀) ∨
      (∃ (x₀ : α) (y : γ), x₀ ∈ V(G) ∧ e = .inr (x₀, y) ∧ (x = .inl x₀ ∨ x = .inr y)) := by
  obtain e | ⟨y, a⟩ := e
  · obtain (x | b) := x
    · simpa [multiApex_inc_eq] using Inc.vertex_mem
    simp [multiApex_inc_eq]
  obtain (x | b) := x
  · simp [multiApex_inc_eq, eq_comm]
  simp [multiApex_inc_eq]

lemma multiApex_inc_inl_iff {e x} :
    (G.multiApex γ).Inc (.inl e) x ↔ ∃ x₀ ∈ V(G), G.Inc e x₀ ∧ x = .inl x₀ := by
  simp [multiApex_inc_iff]

@[simp]
lemma multiApex_inc_inr_iff {e x} :
    (G.multiApex γ).Inc (.inr e) x ↔ e.1 ∈ V(G) ∧ (x = .inl e.1 ∨ x = .inr e.2) := by
  cases e with simp [multiApex_inc_iff, and_comm]

@[simp]
lemma multiApex_not_inc_inl_inr {e x} : ¬ (G.multiApex γ).Inc (.inl e) (.inr x) := by
  simp [multiApex_inc_iff]

@[simp]
lemma multiApex_inc_inl_inl_iff {e x} : (G.multiApex γ).Inc (.inl e) (.inl x) ↔ G.Inc e x := by
  simpa [multiApex_inc_iff] using @Inc.vertex_mem _

@[simp]
lemma multiApex_adj_inl_inl_iff {x y} : (G.multiApex γ).Adj (.inl x) (.inl y) ↔ G.Adj x y := by
  simp [Adj]

@[simp]
lemma multiApex_adj_inr_inr {x y} : (G.multiApex γ).Adj (.inl x) (.inr y) ↔ x ∈ V(G) := by
  simp [Adj, multiApex_isLink_inl_iff_exists]

@[simp]
lemma multiApex_adj_inr_inl {x y} : (G.multiApex γ).Adj (.inr x) (.inl y) ↔ y ∈ V(G) := by
  simp [Adj, multiApex_isLink_inl_iff_exists]

@[simp]
lemma multiApex_not_adj_inr_inr {x y} : ¬ (G.multiApex γ).Adj (.inr x) (.inr y) := by
  simp [Adj]

@[simp]
lemma multiApex_isLoopAt_iff {e x} :
    (G.multiApex γ).IsLoopAt e x ↔ ∃ e₀ x₀, G.IsLoopAt e₀ x₀ ∧ e = .inl e₀ ∧ x = .inl x₀ := by
  obtain e | ⟨a, b⟩ := e
  · simp_rw [IsLoopAt, multiApex_isLink_inl_iff_exists]
    cases x with simp
  simp_rw [IsLoopAt, multiApex_isLink_inr_iff]
  simp +contextual

lemma Loopless.multiApex_loopless (hG : G.Loopless) (γ : Type*) : (G.multiApex γ).Loopless := by
  rw [loopless_iff_forall_ne_of_adj]
  simp +contextual [Adj.ne (G := G)]

lemma multiApex_delete_range_inr (G : Graph α β) :
    (G.multiApex γ) - Set.range .inr = (G.map Sum.inl).edgeMap Sum.inl (by simp +contextual) :=
  ext_inc (by simp) fun e x ↦ by cases e with cases x with simp

@[simp]
lemma multiApex_empty (G : Graph α β) (γ : Type*) [IsEmpty γ] :
    G.multiApex γ = (G.map Sum.inl).edgeMap Sum.inl (by simp +contextual) :=
  eq_map_edgeMap_of_forall_inc (by simp) (by simp [← image_univ]) (fun _ _ _ ↦ by simpa) (by simp)

@[simp]
lemma bot_multiApex (γ : Type*) : (⊥ : Graph α β).multiApex γ = noEdge (range .inr) _ :=
  ext_inc (by simp) <| by simp

@[simp]
lemma multiApex_loopless_iff : (G.multiApex γ).Loopless ↔ G.Loopless := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.multiApex_loopless γ⟩
  have hsG := h.mono (deleteVerts_le (X := Set.range .inr))
  simpa [multiApex_delete_range_inr, map_loopless_iff_of_injOn Sum.inl_injective.injOn] using hsG

lemma Simple.multiApex_simple (hG : G.Simple) (γ : Type*) : (G.multiApex γ).Simple := by
  obtain ⟨hl, hG⟩ := (simple_iff ..).1 hG
  rw [simple_iff, and_iff_right (hl.multiApex_loopless γ)]
  rintro (e | ⟨a, b⟩) (f | ⟨c, d⟩) (x | x) (y | y)
  · simpa using @hG e f x y
  all_goals simp +contextual [multiApex_isLink_inl_iff_exists]

@[simp]
lemma multiApex_simple_iff : (G.multiApex γ).Simple ↔ G.Simple := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.multiApex_simple γ⟩
  have hsG := h.mono (deleteVerts_le (X := Set.range .inr))
  simpa [multiApex_delete_range_inr, edgeMap_simple_iff_of_injOn,
    map_simple_iff_of_injOn, Sum.inl_injective.injOn] using hsG

lemma multiApex_connected [Nonempty γ] {G : Graph α β} (hG : V(G).Nonempty) :
    (G.multiApex γ).Connected := by
  obtain a := Classical.arbitrary γ
  obtain ⟨x₀, hx₀⟩ := hG
  refine connected_of_vertex (u := .inr a) (by simp) ?_
  rintro (x | x) hx
  · exact Adj.connBetween <| by simpa using hx
  exact (Adj.connBetween (y := .inl x₀) (by simpa)).trans <| Adj.connBetween <| by simpa

lemma multiApex_preconnected_iff {G : Graph α β} {γ : Type*} :
    (G.multiApex γ).Preconnected ↔ ((G = ⊥ → Subsingleton γ) ∧ (IsEmpty γ → G.Preconnected)) := by
  refine ⟨fun h ↦ ⟨?_, fun he ↦ ?_⟩, fun ⟨h, h'⟩ ↦ ?_⟩
  · rintro rfl
    simp only [bot_multiApex, noEdge_preconnected_iff] at h
    exact ⟨fun a b ↦ by simpa using h (mem_range_self a) (mem_range_self b)⟩
  · simpa [preconnected_map_iff_of_injOn] using h
  obtain hγ | hγ := isEmpty_or_nonempty γ
  · simpa [preconnected_map_iff_of_injOn] using h' hγ
  obtain rfl | hne := eq_or_ne G ⊥
  · refine preconnected_of_vertexSet_subsingleton ?_
    suffices ∀ a b : γ, a = b by simpa [bot_multiApex, vertexSet_noEdge, Set.Subsingleton]
    exact fun a b ↦ (h rfl).1 a b
  exact (multiApex_connected (ne_bot_iff.1 hne)).pre

lemma multiApex_connected_iff : (G.multiApex γ).Connected ↔
    ((G = ⊥ → (Subsingleton γ ∧ Nonempty γ)) ∧ (IsEmpty γ → G.Connected)) := by
  simp only [vertexSet_multiApex, union_nonempty, image_nonempty, range_nonempty_iff_nonempty,
    connected_iff, multiApex_preconnected_iff, ← ne_bot_iff]
  obtain rfl | hne := eq_or_ne G ⊥
  · simp [and_comm]
  simp [hne]

@[simp]
lemma multiApex_isComplete_iff : (G.multiApex γ).IsComplete ↔ G.IsComplete ∧ Subsingleton γ := by
  refine ⟨fun h ↦ ⟨fun x hx y hy hne ↦ ?_, ⟨fun a b ↦ ?_⟩⟩, fun h ↦ ?_⟩
  · exact multiApex_adj_inl_inl_iff.1 <| h (.inl x) (by simpa) (.inl y) (by simpa) (by simpa)
  · exact by_contra fun hcon ↦ by simpa using h (.inr a) (by simp) (.inr b) (by simp) (by simpa)
  rintro (x | a) hx (y | b) hy hne
  · simpa using h.1 x (by simpa using hx) y (by simpa using hy) (by simpa using hne)
  · simpa using hx
  · simpa using hy
  exact False.elim <| hne <| by simpa using h.2.1 a b

lemma multiApex_deleteVerts_left (G : Graph α β) (X : Set α) (γ : Type*) :
    (G - X).multiApex γ = (G.multiApex γ) - (.inl '' X) := by
  refine Graph.ext_inc ?_ ?_
  · simp [image_sdiff Sum.inl_injective, union_sdiff_distrib,
      disjoint_image_inl_range_inr.symm.sdiff_eq_left]
  rintro (e | ⟨x, a⟩) (y | b)
  · simp
  · simp
  · by_cases hx : x ∈ X <;> simp [hx]
  by_cases hx : x ∈ X <;> simp [hx]

/-- deleting a subset of the apices gives a graph equivalent to an smaller apexed graph-/
lemma multiApex_deleteVerts_right (G : Graph α β) {γ : Type*} (A : Set γ) :
    G.multiApex γ - (.inr '' A) = ((G.multiApex (Aᶜ : Set γ)).map (Sum.map id Subtype.val)).edgeMap
      (Sum.map id (Prod.map id Subtype.val)) (by simp +contextual) := by
  refine eq_map_edgeMap_of_forall_inc (by simp) ?_ ?_ ?_
  · ext (x | y) <;> simp
  · simp_rw [deleteVerts_inc_iff, multiApex_inc_eq, Sum.forall]
    suffices aux : ∀ (a : α), ∀ x ∉ A, ∀ y ∈ V(G), y = a → a ∈ V(G) by simpa +contextual
    grind
  simp_rw [deleteVerts_inc_iff, multiApex_inc_eq, Sum.forall]
  suffices aux : ∀ (a : α) (b : γ), ∀ x ∈ V(G), x = a → (b ∈ A → a ∉ V(G)) → a ∈ V(G) ∧ b ∉ A by
    simpa +contextual
  grind

-- /-- This should be proved using the fact that it is a union-/
-- lemma multiApex_eDegree_inl (G : Graph α β) (γ : Type*) (hx : x ∈ V(G)) :
--     (G.multiApex γ).eDegree (.inl x) = G.eDegree x + ENat.card γ := by
--   rw [multiApex, copy_eq, union_eDegree_eq, eDegree_edgeMap _ _ (by simp),
--     eDegree_edgeMap, eDegree_map_of_injective _ _ Sum.inl_injective,
--     show Sum.inl x = Sum.map Subtype.val id (.inl (⟨x, hx⟩ : V(G))) from rfl,
--     eDegree_map_of_injective _ _]
--   have hinjl := @Sum.inl_injective β (α × γ)
--   have hinjr := @Sum.inr_injective β (α × γ)
--   rw [eDegree_eq_encard_add_encard, eDegree_eq_encard_add_encard, eq_comm, add_assoc,
--     ← inter_univ {e | (G.multiApex γ).IsNonloopAt e (Sum.inl x)},
--     ← range_inl_union_range_inr, inter_union_distrib_left,
--       encard_union_eq (by simp [disjoint_left]),
--       ← encard_preimage_of_injective_subset_range hinjl (by grind [multiApex_isLoopAt_iff]),
--       ← encard_preimage_of_injective_subset_range hinjl inter_subset_right,
--       ← encard_preimage_of_injective_subset_range hinjr inter_subset_right,
--       ← InjOn.encard_image (f := Prod.snd) (by simp [InjOn, IsNonloopAt]), ← encard_univ]
--   convert rfl
--   · simp
--   · simp [IsNonloopAt]
--   simp [Set.ext_iff, IsNonloopAt, hx]

lemma multiApex_eDegree_inr (G : Graph α β) (γ : Type*) (a : γ) :
    (G.multiApex γ).eDegree (.inr a) = V(G).encard := by
  -- rw [eDegree_eq_encard_add_encard]
  simp only [eDegree_eq_encard_add_encard, multiApex_isLoopAt_iff, reduceCtorEq, and_false,
    exists_false, ofPred_false, encard_empty, mul_zero, zero_add]
  rw [← encard_preimage_of_injective_subset_range (@Sum.inr_injective β (α × γ))
    (by simp [IsNonloopAt, subset_def]), ← InjOn.encard_image (f := Prod.fst)
    (by simp [InjOn, IsNonloopAt])]

  sorry




  -- rw [e]



    -- rw [← image_univ, Sum.inr_injective.encard_image, encard_univ]


    -- rw [← Function.Injective.encard_image (@Sum.inl_injective β (α × γ)))]








-- todo : apices where the new vertices are pairwise adjacent, and interactions with connectivity.

/-- The graph with vertices `V(G) ∪ {none}` and edges `E(G) ∪ V(G)`,
where the new edges go to the apex vertex. -/
def apex (G : Graph α β) : Graph (Option α) (β ⊕ α) :=
  ((G.multiApex Unit).map (Sum.elim some (fun _ ↦ none))).edgeMap
    (Sum.elim Sum.inl (fun x ↦ .inr x.1)) (by simp +contextual)

@[simp]
lemma apex_vertexSet (G : Graph α β) : V(G.apex) = insert Option.none (Option.some '' V(G)) := by
  ext x
  simp [apex, or_comm, eq_comm (a := x)]

@[simp]
lemma apex_edgeSet (G : Graph α β) : E(G.apex) = .inl '' E(G) ∪ .inr '' V(G) := by
  ext e
  simp [apex]

@[simp]
lemma apex_isLink_inl_iff {e : β} {x y : α} :
    G.apex.IsLink (.inl e) (some x) (some y) ↔ G.IsLink e x y := by
  simp [apex]

@[simp]
lemma apex_isLink_inr_left_iff {e : α} {x : α} :
    G.apex.IsLink (.inr e) (some x) none ↔ x ∈ V(G) ∧ e = x := by
  simp +contextual [apex, and_comm, eq_comm (a := e)]

@[simp]
lemma apex_isLink_inr_right_iff {e : α} {x : α} :
    G.apex.IsLink (.inr e) none (some x) ↔ x ∈ V(G) ∧ e = x := by
  rw [isLink_comm, apex_isLink_inr_left_iff]

@[simp]
lemma apex_isLoopAt_none {e} : ¬ G.apex.IsLoopAt e none := by
  simp_rw [apex, IsLoopAt, edgeMap_isLink, map_isLink]
  simp

@[simp]
lemma apex_not_isLink_inl_none_left {e : β} {x : Option α} :
    ¬ G.apex.IsLink (.inl e) none x := by
  simp [apex, multiApex_isLink_inl_iff_exists]

@[simp]
lemma apex_not_isLink_inl_none_right {e : β} {x : Option α} :
    ¬ G.apex.IsLink (.inl e) x none := by
  simp [apex, multiApex_isLink_inl_iff_exists]

@[simp]
lemma apex_not_isLink_inr_some_some {e : α} {x y : α} :
    ¬ G.apex.IsLink (.inr e) (some x) (some y) := by
  simp [apex]

lemma apex_isLink_eq_match : G.apex.IsLink = fun e x y ↦ match e, x, y with
    | .inl e, some x, some y => G.IsLink e x y
    | .inr e, some x, none => x = e ∧ x ∈ V(G)
    | .inr e, none, some x => x = e ∧ x ∈ V(G)
    | _, _, _ => False := by
  ext e x y
  cases e with cases x with cases y with simp [and_comm, eq_comm]

lemma apex_inc_eq_match : G.apex.Inc = fun e x ↦ match e, x with
    | .inl e, some x => G.Inc e x
    | .inr y, some x => x = y ∧ x ∈ V(G)
    | .inr y, none => y ∈ V(G)
    | _, _ => False := by
  ext e x
  cases e with cases x with simp [Inc, apex_isLink_eq_match, Option.exists]

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
  cases y with simp [← isLink_self_iff, apex]

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
  rw [apex, edgeMap_loopless_iff, map_loopless_iff_of_injOn (by simp), multiApex_loopless_iff]

alias ⟨_, Loopless.apex_loopless⟩ := apex_loopless_iff

@[simp]
lemma apex_simple_iff : G.apex.Simple ↔ G.Simple := by
  rw [apex, edgeMap_simple_iff_of_injOn (by simp), map_simple_iff_of_injOn (by simp),
    multiApex_simple_iff]

alias ⟨_, Simple.apex_simple⟩ := apex_simple_iff

lemma apex_connected (G : Graph α β) : G.apex.Connected := by
  refine connected_of_vertex (u := none) (by simp) ?_
  rintro (rfl | y) hy
  · simp
  exact Adj.connBetween <| by simpa using hy

lemma apex_delete_none (G : Graph α β) : G.apex - {none} =
    (G.map Option.some).edgeMap Sum.inl (by simp +contextual) := by
  refine eq_map_edgeMap_of_forall_inc (by simp) (by simp) ?_ ?_
  · simp [apex_inc_eq_match]
  simp [apex_inc_eq_match, Option.forall]

lemma PreconnGE.apex {n : ℕ} (hG : G.PreconnGE n) : G.apex.PreconnGE (n + 1) := by
  refine PreconnGE.preconnGE_add_one_of_delete_of_forall_adj (v := none) ?_ <| by simp
  rwa [apex_delete_none, preconnGE_edgeMap_iff, preconnGE_map_iff_of_injOn (by simp)]

lemma ConnGE.apex {n : ℕ} (hG : G.ConnGE n) (hnt : V(G).Nontrivial) : G.apex.ConnGE (n + 1) := by
  refine ConnGE.connGE_add_one_of_delete_of_forall_adj (v := none) ?_ ?_ (by simp)
  · rwa [apex_delete_none, connGE_edgeMap_iff, connGE_map_iff_of_injOn (by simp)]
  simp only [apex_vertexSet]
  grw [encard_insert_of_notMem (by simp), (Option.some_injective _).encard_image,
  ← two_le_encard_iff_nontrivial.2 hnt, show (3 : ℕ∞) = 2 + 1 from rfl]
