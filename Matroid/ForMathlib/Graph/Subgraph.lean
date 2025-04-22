import Matroid.ForMathlib.Graph.Basic

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
