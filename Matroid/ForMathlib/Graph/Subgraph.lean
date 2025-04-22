import Matroid.ForMathlib.Graph.Walk.Defs

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}

namespace Graph

structure IsSubgraph (H G : Graph α β) : Prop where
  vx_subset : H.V ⊆ G.V
  inc₂_of_inc₂ : ∀ e x y, H.Inc₂ e x y → G.Inc₂ e x y

/-- The subgraph order -/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨rfl.le, by simp⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 _ _ _ (h₁.2 _ _ _ h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1) fun e x y ↦ ⟨h₁.2 e x y, h₂.2 e x y⟩

lemma Inc₂.of_le (h : H.Inc₂ e x y) (hle : H ≤ G) : G.Inc₂ e x y :=
  hle.2 _ _ _ h

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  (h.choose_spec.of_le hle).inc_left

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma vxSet_subset_of_le (h : H ≤ G) : H.V ⊆ G.V :=
  h.1

lemma edgeSet_subset_of_le (h : H ≤ G) : H.E ⊆ G.E := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_inc₂_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps] def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  V := G.V
  E := E₀ ∩ G.E
  Inc₂ e x y := e ∈ E₀ ∧ G.Inc₂ e x y
  inc₂_symm e x y h := by rwa [G.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ _ _ _ _ _ h h' := h.2.left_eq_or_eq_of_inc₂ h'.2
  edge_mem_iff_exists_inc₂ e := ⟨fun h ↦ by simp [h, G.exists_inc₂_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  vx_mem_left_of_inc₂ _ _ _ h := h.2.vx_mem_left

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
@[simps] def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  V := f '' G.V
  E := G.E
  Inc₂ e x' y' := ∃ x y, G.Inc₂ e x y ∧ x' = f x ∧ y' = f y
  inc₂_symm := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩
  eq_or_eq_of_inc₂_of_inc₂ := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq_of_inc₂ hzw <;> simp
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet h
      exact ⟨_, _, _, _, hxy, rfl, rfl⟩
    rintro ⟨-, -, x, y, h, rfl, rfl⟩
    exact h.edge_mem
  vx_mem_left_of_inc₂ := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.vx_mem_left


/-- The graph with vertex set `V` and no edges -/
@[simps] def noEdgeGraph (V : Set α) (β : Type*) : Graph α β where
  V := V
  E := ∅
  Inc₂ _ _ _ := False
  inc₂_symm := by simp
  eq_or_eq_of_inc₂_of_inc₂ := by simp
  edge_mem_iff_exists_inc₂ := by simp
  vx_mem_left_of_inc₂ := by simp

@[simps]
protected def union (H G : Graph α β)
    (h_inter : ∀ ⦃e x y⦄, e ∈ H.E → e ∈ G.E → (H.Inc₂ e x y ↔ G.Inc₂ e x y)) : Graph α β where
  V := H.V ∪ G.V
  E := H.E ∪ G.E
  Inc₂ e x y := G.Inc₂ e x y ∨ H.Inc₂ e x y
  inc₂_symm e x y h := by rwa [G.inc₂_comm, H.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ := by
    rintro e x y v w (h | h) (h' | h')
    · exact h.left_eq_or_eq_of_inc₂ h'
    · exact h.left_eq_or_eq_of_inc₂ <| (h_inter h'.edge_mem h.edge_mem).1 h'
    · exact h.left_eq_or_eq_of_inc₂ <| (h_inter h.edge_mem h'.edge_mem).2 h'
    exact h.left_eq_or_eq_of_inc₂ h'
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨?_, fun ⟨x, y, h⟩ ↦ h.elim (fun h' ↦ .inr h'.edge_mem) (fun h' ↦ .inl h'.edge_mem)⟩
    rintro (he | he) <;>
    · obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet he
      exact ⟨x, y, by simp [h]⟩
  vx_mem_left_of_inc₂ := by
    rintro e x y (h | h)
    · exact .inr h.vx_mem_left
    exact .inl h.vx_mem_left

-- def Walk.toGraph : Walk α β → Graph α β
--   | nil u => noEdgeGraph {u} β
--   | cons u e w => sorry

  -- V := _
  -- E := _
  -- Inc₂ := _
  -- inc₂_symm := _
  -- eq_or_eq_of_inc₂_of_inc₂ := _
  -- edge_mem_iff_exists_inc₂ := _
  -- vx_mem_left_of_inc₂ := _
