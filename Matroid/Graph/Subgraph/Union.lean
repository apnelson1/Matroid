import Matroid.Graph.Subgraph.Compatible

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function Partition

namespace Graph


/-! ### Set unions -/

variable {s : Set (Graph α β)} {G : Graph α β}

/-- The union of a set of pairwise compatible graphs. -/
@[simps! vertexSet]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β where
  vertexPartition := ⨆ G ∈ s, P(G)
  IsLink e x y := ∃ (u v : Set α) (h : ∃ G ∈ s, G.IsLink e u v),
    Partition.foo (⨆ G ∈ s, P(G)) u h.choose_spec.2.left_mem_vertexPartition = x ∧
    Partition.foo (⨆ G ∈ s, P(G)) v h.choose_spec.2.right_mem_vertexPartition = y
  isLink_symm e he u v := by
    rintro ⟨u, v, ⟨G, hG, huv⟩, rfl, rfl⟩
    exact ⟨v, u, ⟨G, hG, huv.symm⟩, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink e a b c d := by
    rintro ⟨u, v, ⟨G, hG, huv⟩, rfl, rfl⟩ ⟨u', v', ⟨G', hG', hvw⟩, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := G.eq_or_eq_of_isLink_of_isLink huv <|
      hvw.of_compatible (hs.of_refl hG' hG) huv.edge_mem <;> tauto
  left_mem_of_isLink e a b := by
    rintro ⟨u, v, ⟨G, hG, huv⟩, rfl, rfl⟩
    refine Partition.foo_mem _ fun a ha ↦ ?_
    simp only [iSup_supp, iSup_supp_prop, mem_iUnion, exists_prop]
    exact ⟨G, hG, mem_supp_iff.mpr ⟨u, huv.left_mem_vertexPartition, ha⟩⟩

protected lemma le_sUnion (hs : s.Pairwise Graph.Compatible) (hG : G ∈ s) :
    G ≤ Graph.sUnion s hs := by
  sorry

@[simp]
protected lemma sUnion_le_iff (hs : s.Pairwise Graph.Compatible) :
    Graph.sUnion s hs ≤ H ↔ ∀ G ∈ s, G ≤ H := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_inc_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).Inc e x ↔ ∃ G ∈ s, G.Inc e x := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_isLoopAt_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).IsLoopAt e x ↔ ∃ G ∈ s, G.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma sUnion_isNonloopAt_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).IsNonloopAt e x ↔ ∃ G ∈ s, G.IsNonloopAt e x := by
  simp [Graph.sUnion]

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} (by simp) = G := by
  ext <;> simp

protected lemma sUnion_image {s : Set ι} {f : ι → Graph α β}
    (hs : s.Pairwise (Graph.Compatible on f)) :
    Graph.sUnion (f '' s) hs.image = .iUnion (f · : s → _) (Pairwise.restrict.mpr hs) := by
  rw [Graph.sUnion]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  exact Graph.iUnion_comp_eq_of_surj (f := f') _ (fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩)

protected lemma sUnion_range {f : ι → Graph α β} (h : Pairwise (Graph.Compatible on f)) :
    Graph.sUnion (Set.range f) h.range_pairwise = .iUnion f h := by
  unfold Graph.sUnion
  exact Graph.iUnion_comp_eq_of_surj (f := Set.rangeFactorization f) _ surjective_onto_range
