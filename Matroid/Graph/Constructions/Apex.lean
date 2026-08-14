module

public import Matroid.Graph.Bipartite

@[expose] public section

open Set

namespace Graph

variable {α α' β β' γ : Type*} {x y : α} {e f : β} {G : Graph α β}

lemma Adj.map (hG : G.Adj x y) (φ : α → α') : (G.map φ).Adj (φ x) (φ y) := by
  obtain ⟨e, he⟩ := hG
  exact ⟨e, he.map φ⟩

lemma map_adj_iff_of_injective {φ : α → α'} {x y : α} (hφ : φ.Injective) :
    (G.map φ).Adj (φ x) (φ y) ↔ G.Adj x y :=
  ⟨fun ⟨e, he⟩ ↦ ⟨e, by simpa [hφ.eq_iff] using he⟩, fun h ↦ h.map φ⟩

lemma map_adj_iff_of_injOn {φ : α → α'} {x y : α} (hφ : InjOn φ V(G))
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) : (G.map φ).Adj (φ x) (φ y) ↔ G.Adj x y := by
  refine ⟨fun ⟨e, he⟩ ↦ ⟨e, ?_⟩, fun h ↦ h.map φ⟩
  obtain ⟨x', y', h, hx', hy'⟩ := he
  rw [hφ.eq_iff hx h.left_mem] at hx'
  rw [hφ.eq_iff hy h.right_mem] at hy'
  rwa [hx', hy']

@[simp]
lemma edgeMap_adj_iff {φ : β → β'} {hφ} : (G.edgeMap φ hφ).Adj x y ↔ G.Adj x y := by
  simp [Adj]

lemma edgeMap_adj_eq {φ : β → β'} {hφ} : (G.edgeMap φ hφ).Adj = G.Adj := by
  simp [funext_iff]

lemma Loopless.map (hG : G.Loopless) (f : α → β) (hf : InjOn f V(G)) : (G.map f).Loopless := by
  simp only [loopless_iff_forall_ne_of_adj, ne_eq]
  rintro x _ ⟨e, he⟩ rfl



/-- Add some new vertices to a graph that are adjacent to all existing vertices.
The new vertices are identified with a type `γ`, and the new edges with terms in `α × γ`. -/
def apexOf (G : Graph α β) (γ : Type*) : Graph (α ⊕ γ) (β ⊕ (α × γ)) :=
    ((G.map Sum.inl).edgeMap Sum.inl) (by simp +contextual) ∪
      (((completeBipartiteGraphOn V(G) γ).map (Sum.map Subtype.val id)).edgeMap
      (Sum.inr ∘ Prod.map Subtype.val id)) (by simp +contextual)

@[simp]
lemma apexOf_compatible (G : Graph α β) (γ : Type*) :
    Graph.Compatible (((G.map Sum.inl).edgeMap Sum.inl) (by simp +contextual))
      (((completeBipartiteGraphOn V(G) γ).map (Sum.map Subtype.val id)).edgeMap
        (Sum.inr ∘ Prod.map Subtype.val id) (by simp +contextual)) := by
  rintro e he ⟨a, -, rfl⟩
  simp at he

@[simp]
lemma apexOf_vertexSet (G : Graph α β) (γ : Type*) :
    V(G.apexOf γ) = .inl '' V(G) ∪ Set.range .inr := by
  simp [apexOf, vertexSet_union, vertexSet_edgeMap, vertexSet_map,
    vertexSet_completeBipartiteGraphOn, Sum.map, Set.range_comp]

@[simp]
lemma apexOf_edgeSet (G : Graph α β) (γ : Type*) :
    E(G.apexOf γ) = .inl '' E(G) ∪ (.inr '' (Prod.fst ⁻¹' V(G))) := by
  simp [apexOf, Set.ext_iff]

lemma apexOf_isLink_inl_inl_iff_exists {e} {x y : α} :
    (G.apexOf γ).IsLink e (.inl x) (.inl y) ↔ ∃ e₀, e = .inl e₀ ∧ G.IsLink e₀ x y := by
  rw [Graph.apexOf, Compatible.union_isLink_iff (by simp)]
  cases e with simp

lemma apexOf_isLink_inl_iff_exists {e} {x y} :
    (G.apexOf γ).IsLink (.inl e) x y ↔ (∃ x₀ y₀, G.IsLink e x₀ y₀ ∧ x = .inl x₀ ∧ y = .inl y₀) := by
  rw [Graph.apexOf, Compatible.union_isLink_iff (by simp)]
  simp

@[simp]
lemma apexOf_isLink_inl_inl_inl_iff {e : β} {x y : α} :
    (G.apexOf γ).IsLink (.inl e) (.inl x) (.inl y) ↔ G.IsLink e x y := by
  simp [apexOf_isLink_inl_inl_iff_exists]

@[simp]
lemma apexOf_not_isLink_inr_inl_inl {e} {x y : α} :
    ¬ (G.apexOf γ).IsLink (.inr e) (.inl x) (.inl y) := by
  simp [apexOf_isLink_inl_inl_iff_exists]

lemma apexOf_isLink_inr_iff {e} {x y : α ⊕ γ} : (G.apexOf γ).IsLink (.inr e) x y ↔
      (x = .inl e.1 ∧ e.1 ∈ V(G) ∧ y = .inr e.2) ∨ (x = .inr e.2 ∧ y = .inl e.1 ∧ e.1 ∈ V(G)) := by
  rw [Graph.apexOf, Compatible.union_isLink_iff (by simp)]
  obtain ⟨a, b⟩ := e
  cases x with simp [and_comm]

@[simp]
lemma apexOf_isLink_inr_inl_iff {e} {x : α} {y : α ⊕ γ} :
    (G.apexOf γ).IsLink (.inr e) (.inl x) y ↔ x = e.1 ∧ x ∈ V(G) ∧ y = .inr e.2 := by
  simp +contextual [apexOf_isLink_inr_iff]

@[simp]
lemma apexOf_isLink_inr_inl_iff' {e} {x : α ⊕ γ} {y : α} :
    (G.apexOf γ).IsLink (.inr e) x (.inl y) ↔ x = .inr e.2 ∧ y = e.1 ∧ y ∈ V(G) := by
  simp +contextual [apexOf_isLink_inr_iff]

@[simp]
lemma apexOf_isLink_inr_inr_iff {e} {x : γ} {y : α ⊕ γ} :
    (G.apexOf γ).IsLink (.inr e) (.inr x) y ↔ x = e.2 ∧ y = .inl e.1 ∧ e.1 ∈ V(G) := by
  simp [apexOf_isLink_inr_iff]

@[simp]
lemma apexOf_isLink_inr_inr_iff' {e} {x : α ⊕ γ} {y : γ} :
    (G.apexOf γ).IsLink (.inr e) x (.inr y) ↔ x = .inl e.1 ∧ e.1 ∈ V(G) ∧ y = e.2 := by
  simp [apexOf_isLink_inr_iff]

lemma apexOf_inc_iff {e x} :
    (G.apexOf γ).Inc e x ↔ (∃ e₀ x₀, x₀ ∈ V(G) ∧ G.Inc e₀ x₀ ∧ e = .inl e₀ ∧ x = .inl x₀) ∨
      (∃ (x₀ : α) (y : γ), x₀ ∈ V(G) ∧ e = .inr (x₀, y) ∧ (x = .inl x₀ ∨ x = .inr y)) := by
  rw [Graph.apexOf, Compatible.union_inc_iff (by simp)]
  obtain e | ⟨a, b⟩ := e
  · suffices (∃ v, G.Inc e v ∧ x = Sum.inl v) ↔ ∃ x₀ ∈ V(G), G.Inc e x₀ ∧ x = Sum.inl x₀ by simpa
    grind
  simp

lemma apexOf_inc_inl_iff {e x} :
    (G.apexOf γ).Inc (.inl e) x ↔ ∃ x₀ ∈ V(G), G.Inc e x₀ ∧ x = .inl x₀ := by
  simp [apexOf_inc_iff]

@[simp]
lemma apexOf_inc_inr_iff {e x} :
    (G.apexOf γ).Inc (.inr e) x ↔ e.1 ∈ V(G) ∧ (x = .inl e.1 ∨ x = .inr e.2) := by
  cases e with simp [apexOf_inc_iff, and_comm]

@[simp]
lemma apexOf_not_inc_inl_inr {e x} : ¬ (G.apexOf γ).Inc (.inl e) (.inr x) := by
  simp [apexOf_inc_iff]

@[simp]
lemma apexOf_inc_inl_inl_iff {e x} : (G.apexOf γ).Inc (.inl e) (.inl x) ↔ G.Inc e x := by
  simpa [apexOf_inc_iff] using @Inc.vertex_mem _

@[simp]
lemma apexOf_adj_inl_inl_iff {x y} : (G.apexOf γ).Adj (.inl x) (.inl y) ↔ G.Adj x y := by
  simp [Adj]

@[simp]
lemma apexOf_adj_inr_inr {x y} : (G.apexOf γ).Adj (.inl x) (.inr y) ↔ x ∈ V(G) := by
  simp [Adj, apexOf_isLink_inl_iff_exists]

@[simp]
lemma apexOf_adj_inr_inl {x y} : (G.apexOf γ).Adj (.inr x) (.inl y) ↔ y ∈ V(G) := by
  simp [Adj, apexOf_isLink_inl_iff_exists]

@[simp]
lemma apexOf_not_adj_inr_inr {x y} : ¬ (G.apexOf γ).Adj (.inr x) (.inr y) := by
  simp [Adj, apexOf_isLink_inl_iff_exists]

@[simp]
lemma apexOf_isLoopAt_iff {e x} :
    (G.apexOf γ).IsLoopAt e x ↔ ∃ e₀ x₀, G.IsLoopAt e₀ x₀ ∧ e = .inl e₀ ∧ x = .inl x₀ := by
  obtain e | ⟨a, b⟩ := e
  · simp_rw [IsLoopAt, apexOf_isLink_inl_iff_exists]
    cases x with simp
  simp_rw [IsLoopAt, apexOf_isLink_inr_iff]
  simp +contextual

lemma Loopless.apexOf_loopless (hG : G.Loopless) (γ : Type*) : (G.apexOf γ).Loopless := by
  rw [loopless_iff_forall_ne_of_adj]
  simp +contextual [Adj.ne (G := G)]

lemma apexOf_delete_range_inr (G : Graph α β) :
    (G.apexOf γ) - Set.range .inr = (G.map Sum.inl).edgeMap Sum.inl (by simp +contextual) :=
  ext_inc (by simp) fun e x ↦ by cases e with cases x with simp

@[simp]
lemma apexOf_loopless_iff : (G.apexOf γ).Loopless ↔ G.Loopless := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.apexOf_loopless γ⟩
  have := h.mono (deleteVerts_le (X := Set.range .inr))
  simp [apexOf_delete_range_inr] at this


lemma Simple.apexOf_simple (hG : G.Simple) : (G.apexOf γ).Simple := by
  obtain ⟨hl, hG⟩ := (simple_iff ..).1 hG
  rw [simple_iff, and_iff_right hl.apexOf_loopless]
  rintro (e | ⟨a, b⟩) (f | ⟨c, d⟩) (x | x) (y | y)
  · simpa using @hG e f x y
  all_goals simp +contextual [apexOf_isLink_inl_iff_exists]

lemma singleApex_connected [Nonempty γ] {G : Graph α β} (hG : V(G).Nonempty) :
    (G.apexOf γ).Connected := by
  obtain a := Classical.arbitrary γ
  obtain ⟨x₀, hx₀⟩ := hG
  refine connected_of_vertex (u := .inr a) (by simp) ?_
  rintro (x | x) hx
  · exact Adj.connBetween <| by simpa using hx
  exact (Adj.connBetween (y := .inl x₀) (by simpa)).trans <| Adj.connBetween <| by simpa

/-- The graph with vertices `V(G) ∪ {none}` and edges `E(G) ∪ V(G)`,
where the new edges go to the apex vertex. -/
def singleApex (G : Graph α β) : Graph (Option α) (β ⊕ α) :=
  ((G.apexOf Unit).map (Sum.elim some (fun _ ↦ none))).edgeMap
    (Sum.elim Sum.inl (fun x ↦ .inr x.1)) (by simp +contextual)

@[simp]
lemma singleApex_vertexSet (G : Graph α β) :
    V(G.singleApex) = insert Option.none (Option.some '' V(G)) := by
  ext x
  simp [singleApex, or_comm, eq_comm (a := x)]

@[simp]
lemma singleApex_edgeSet (G : Graph α β) :
    E(G.singleApex) = .inl '' E(G) ∪ .inr '' V(G) := by
  ext e
  simp [singleApex]

@[simp]
lemma singleApex_isLink_inl_iff {e : β} {x y : α} :
    G.singleApex.IsLink (.inl e) (some x) (some y) ↔ G.IsLink e x y := by
  simp [singleApex]

@[simp]
lemma singleApex_isLink_inr_left_iff {e : α} {x : α} :
    G.singleApex.IsLink (.inr e) (some x) none ↔ x ∈ V(G) ∧ e = x := by
  simp +contextual [singleApex, and_comm, eq_comm (a := e)]

@[simp]
lemma singleApex_isLink_inr_right_iff {e : α} {x : α} :
    G.singleApex.IsLink (.inr e) none (some x) ↔ x ∈ V(G) ∧ e = x := by
  rw [isLink_comm, singleApex_isLink_inr_left_iff]

@[simp]
lemma singleApex_not_isLink_inl_none_left {e : β} {x : Option α} :
    ¬ G.singleApex.IsLink (.inl e) none x := by
  simp [singleApex, apexOf_isLink_inl_iff_exists]

@[simp]
lemma singleApex_not_isLink_inl_none_right {e : β} {x : Option α} :
    ¬ G.singleApex.IsLink (.inl e) x none := by
  simp [singleApex, apexOf_isLink_inl_iff_exists]

@[simp]
lemma singleApex_not_isLink_inr_some_some {e : α} {x y : α} :
    ¬ G.singleApex.IsLink (.inr e) (some x) (some y) := by
  simp [singleApex]

@[simp]
lemma singleApex_adj_some_some_iff {x y : α} :
    G.singleApex.Adj (some x) (some y) ↔ G.Adj x y := by
  simp [Adj]

@[simp]
lemma singleApex_adj_some_none {x : α} :
    G.singleApex.Adj (some x) none ↔ x ∈ V(G) := by
  simp [Adj]

@[simp]
lemma singleApex_adj_none_some {x : α} :
    G.singleApex.Adj none (some x) ↔ x ∈ V(G) := by
  simp [Adj]

@[simp]
lemma singleApex_isLoopAt_inl {e : β} {x : α} :
    G.singleApex.IsLoopAt (.inl e) (some x) ↔ G.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma singleApex_not_isLoopAt_inr (G : Graph α β) {y : Option α} {e} :
    ¬ G.singleApex.IsLoopAt (.inr e) y := by
  cases y with simp [← isLink_self_iff, singleApex]

@[simp]
lemma singleApex_not_isLoopAt_none (G : Graph α β) {e : β ⊕ α} :
    ¬ G.singleApex.IsLoopAt e none := by
  obtain b | a := e
  · rw [← isLink_self_iff]
    exact singleApex_not_isLink_inl_none_right
  simp

@[simp]
lemma singleApex_not_adj_none (G : Graph α β) : ¬ G.singleApex.Adj none none := by
  simp [Adj]

lemma Loopless.singleApex_loopless (hG : G.Loopless) : G.singleApex.Loopless := by
  rw [loopless_iff_forall_ne_of_adj]
  simp +contextual [Option.forall, Adj.ne (G := G)]

lemma Simple.singleApex_simple (hG : G.Simple) : G.singleApex.Simple := by
  rw [simple_iff, and_iff_right hG.singleApex_loopless]
  rintro (e | e) (f | f)
  · simpa [Option.forall] using fun _ _ h h' ↦ hG.eq_of_isLink h h'
  · simp [Option.forall]
  · simp [Option.forall]
  simp +contextual [Option.forall]

lemma singleApex_connected (G : Graph α β) : G.singleApex.Connected := by
  refine connected_of_vertex (u := none) (by simp) ?_
  rintro (rfl | y) hy
  · simp
  exact Adj.connBetween <| by simpa using hy
