import Matroid.Graph.Subgraph.Defs

variable {α β ι ι' : Type*} {a b c : α} {x y z u v w : α} {e f : β} {Gι Hι : ι → Graph α β}
  {G G₁ G₂ H H₁ H₂ : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)}

open Set Function

namespace Graph
/-! ### Indexed Intersections -/

@[simp]
protected lemma iInter_const [Nonempty ι] (G : Graph α β) :
    Graph.iInter (fun (_ : ι) ↦ G) = G := by
  apply le_antisymm (Graph.iInter_le (Classical.arbitrary ι))
  rw [le_iInter_iff]
  exact fun i ↦ le_refl G

protected lemma iInter_comp_le [Nonempty ι] [Nonempty ι'] {f : ι' → ι}
    {G : ι → Graph α β} : Graph.iInter G ≤ Graph.iInter (fun i ↦ G (f i)) := by
  rw [Graph.le_iInter_iff]
  exact fun i ↦ Graph.iInter_le (f i)

lemma iInter_comp_eq_of_surj [Nonempty ι] [Nonempty ι'] {f : ι' → ι}
    {G : ι → Graph α β} (hf : Function.Surjective f) :
    Graph.iInter G = Graph.iInter (fun i ↦ G (f i)) :=
  le_antisymm (Graph.iInter_comp_le) <| by
  rw [Graph.le_iInter_iff]
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.iInter_le i'

lemma iInter_range [Nonempty ι'] {f : ι' → ι} {G : (Set.range f) → Graph α β} :
    Graph.iInter G = Graph.iInter (fun i ↦ G (Set.rangeFactorization f i)) :=
  iInter_comp_eq_of_surj rangeFactorization_surjective

@[simp]
lemma iInter_inc_iff [Nonempty ι] {G : ι → Graph α β} :
    (Graph.iInter G).Inc e x ↔ ∃ y, ∀ i, (G i).IsLink e x y := by
  simp only [Inc, iInter_isLink]

@[simp]
lemma iInter_isLoopAt_iff [Nonempty ι] {G : ι → Graph α β} :
    (Graph.iInter G).IsLoopAt e x ↔ ∀ i, (G i).IsLoopAt e x := by
  simp only [IsLoopAt, iInter_isLink]

@[simp]
lemma iInter_isNonloopAt_iff [Nonempty ι] {G : ι → Graph α β} :
    (Graph.iInter G).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ i, (G i).IsLink e x y := by
  simp only [IsNonloopAt, iInter_isLink]

@[simp]
lemma induce_iInter [Nonempty ι] {G : ι → Graph α β} (X : Set α) :
    (Graph.iInter G)[X] = .iInter (fun i ↦ (G i)[X]) :=
  Graph.ext (iInter_const X).symm fun e x y ↦ by
  simp [forall_and_right]

@[simp]
lemma vertexDelete_iInter [Nonempty ι] {G : ι → Graph α β} (X : Set α) :
    (Graph.iInter G) - X = .iInter (fun i ↦ (G i) - X) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, iInter_isLink, iff_def, not_false_eq_true,
    and_self, implies_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).right

@[simp]
lemma edgeDelete_iInter [Nonempty ι] {G : ι → Graph α β} (F : Set β) :
    (Graph.iInter G) ＼ F = .iInter (fun i ↦ (G i) ＼ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, iInter_isLink, iff_def, not_false_eq_true, and_self,
    implies_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).right

@[simp]
lemma edgeRestrict_iInter [Nonempty ι] {G : ι → Graph α β} (F : Set β) :
    (Graph.iInter G) ↾ F = .iInter (fun i ↦ (G i) ↾ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, iInter_isLink, iff_def, and_self, implies_true,
    and_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).left

/-! ### Set Intersections -/

protected lemma sInter_anti (hne : Gs.Nonempty) (hne' : Hs.Nonempty) (hle : Gs ⊆ Hs) :
    Graph.sInter Hs hne' ≤ Graph.sInter Gs hne := by
  rw [Graph.le_sInter_iff hne]
  exact fun G hGs ↦ Graph.sInter_le (hle hGs)

def Equiv.insert_option {s : Set α} [DecidablePred fun (x : α) => x ∈ s] (a : α) (has : a ∉ s) :
    Option s ≃ (insert a s : Set α) :=
  (Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm

protected lemma sInter_insert_eq_iInter [DecidablePred (· ∈ Gs)]
    (hGs : G ∉ Gs) : Graph.sInter (insert G Gs) (by simp) = Graph.iInter
    ((fun G : (insert G Gs : Set _) ↦ G.1) ∘ (Equiv.insert_option G hGs)) :=
  Graph.iInter_comp_eq_of_surj <| Equiv.surjective (Equiv.insert_option G hGs)

protected lemma sInter_image {s : Set ι} (hne : s.Nonempty) (f : ι → Graph α β) :
    Graph.sInter (f '' s) (by simpa) = @Graph.iInter _ _ _ hne.to_subtype (f · : s → _) := by
  rw [Graph.sInter]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  have := hne.to_subtype
  exact Graph.iInter_comp_eq_of_surj (f := f') fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩

protected lemma sInter_range [Nonempty ι] {f : ι → Graph α β} :
    Graph.sInter (Set.range f) (range_nonempty f) = .iInter f := by
  rw [Graph.sInter]
  exact Graph.iInter_comp_eq_of_surj (f := Set.rangeFactorization f) rangeFactorization_surjective

@[simp]
protected lemma sInter_singleton (G : Graph α β) : Graph.sInter {G} (by simp) = G := by
  apply le_antisymm (Graph.sInter_le (by simp))
  rw [Graph.le_sInter_iff (by simp)]
  exact fun G_2 a ↦ Eq.ge a

@[simp]
lemma sInter_inc_iff (hs : Gs.Nonempty) :
    (Graph.sInter Gs hs).Inc e x ↔ ∃ y, ∀ G ∈ Gs, G.IsLink e x y := by
  simp only [Inc, sInter_isLink]

@[simp]
lemma sInter_isLoopAt_iff (hs : Gs.Nonempty) :
    (Graph.sInter Gs hs).IsLoopAt e x ↔ ∀ G ∈ Gs, G.IsLoopAt e x := by
  simp only [IsLoopAt, sInter_isLink]

@[simp]
lemma sInter_isNonloopAt_iff (hs : Gs.Nonempty) :
    (Graph.sInter Gs hs).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ G ∈ Gs, G.IsLink e x y := by
  simp only [IsNonloopAt, sInter_isLink]

@[simp]
lemma induce_sInter (hs : Gs.Nonempty) (X : Set α) :
    (Graph.sInter Gs hs)[X] = .sInter ((·[X]) '' Gs) (by simpa) := by
  refine Graph.ext (by simp; exact (biInter_const hs X).symm) fun e x y ↦ ?_
  simp +contextual only [induce_isLink, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma vertexDelete_sInter (hs : Gs.Nonempty) (X : Set α) :
    (Graph.sInter Gs hs) - X = .sInter ((· - X) '' Gs) (by simpa) := by
  refine Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ ?_
  simp +contextual only [vertexDelete_isLink_iff, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeDelete_sInter (hs : Gs.Nonempty) (F : Set β) :
    (Graph.sInter Gs hs) ＼ F = .sInter ((· ＼ F) '' Gs) (by simpa) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeRestrict_sInter (hs : Gs.Nonempty) (F : Set β) :
    (Graph.sInter Gs hs) ↾ F = .sInter ((· ↾ F) '' Gs) (by simpa) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, and_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).left

/-! ### Intersections -/

lemma inter_edgeSet_subset : E(G ∩ H) ⊆ E(G) ∩ E(H) := by
  simp +contextual [inter_edgeSet, subset_def]

@[simp]
lemma inter_inc_iff : (G ∩ H).Inc e x ↔ ∃ y, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [Inc]

@[simp]
lemma inter_isLoopAt_iff : (G ∩ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma inter_isNonloopAt_iff :
    (G ∩ H).IsNonloopAt e x ↔ ∃ y ≠ x, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [IsNonloopAt]

@[simp]
lemma inf_eq_inter : H₁ ⊓ H₂ = H₁ ∩ H₂ := rfl

@[simp]
lemma inter_eq_bot_iff : H₁ ∩ H₂ = ⊥ ↔ V(H₁) ∩ V(H₂) = ∅ := by
  rw [← vertexSet_eq_empty_iff, inter_vertexSet]

lemma disjoint_iff_inter_eq_bot : Disjoint H₁ H₂ ↔ H₁ ∩ H₂ = ⊥ := by
  rw [disjoint_iff, inf_eq_inter]

@[simp]
lemma disjoint_iff_vertexSet_inter_eq_empty : Disjoint H₁ H₂ ↔ V(H₁) ∩ V(H₂) = ∅ := by
  rw [disjoint_iff_inter_eq_bot, inter_eq_bot_iff]

lemma disjoint_iff_vertexSet_disjoint : Disjoint H₁ H₂ ↔ Disjoint V(H₁) V(H₂) := by
  rw [disjoint_iff_inter_eq_bot, inter_eq_bot_iff, Set.disjoint_iff_inter_eq_empty]

alias ⟨Disjoint.vertex_disjoint, _⟩ := disjoint_iff_vertexSet_disjoint

lemma Compatible.inter_edgeSet (h : G.Compatible H) : E(G ∩ H) = E(G) ∩ E(H) := by
  rw [Graph.inter_edgeSet]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, h he⟩

lemma inter_eq_iInter : G ∩ H = Graph.iInter (fun b ↦ bif b then G else H) :=
  Graph.ext (by simp [Bool.apply_cond]) (by simp [and_comm])

lemma le_inter_iff : H ≤ G₁ ∩ G₂ ↔ H ≤ G₁ ∧ H ≤ G₂ := by
  simp [inter_eq_iInter, and_comm]

lemma inter_eq_self_of_le (hle : G ≤ H) : G ∩ H = G :=
  le_antisymm Graph.inter_le_left <| by simpa [le_inter_iff]

lemma le_of_inter_eq_self (h : G ∩ H = G) : G ≤ H := by
  rw [← h]
  exact Graph.inter_le_right

@[gcongr]
lemma inter_mono_left (hle : G₁ ≤ G₂) : G₁ ∩ H ≤ G₂ ∩ H := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left.trans hle, Graph.inter_le_right⟩

@[gcongr]
lemma inter_mono_right (hle : H₁ ≤ H₂) : G ∩ H₁ ≤ G ∩ H₂ := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left, Graph.inter_le_right.trans hle⟩

lemma inter_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) : G₁ ∩ H₁ ≤ G₂ ∩ H₂ :=
  (inter_mono_right hleH).trans (inter_mono_left hleG)

lemma edgeSet_induce_inter_eq_edgeSet_induce_of_le (h : G ≤ H) : E(G) ∩ E(H[X]) = E(G[X]) :=
  Set.ext fun _ ↦ ⟨fun ⟨he, x, y, hl, hx, hy⟩ => ⟨x, y, hl.of_le_of_mem h he, hx, hy⟩,
    fun ⟨x, y, hl, hx, hy⟩ => ⟨hl.edge_mem, x, y, hl.of_le h, hx, hy⟩⟩

lemma induce_inter (X Y : Set α) : G[X ∩ Y] = G[X] ∩ G[Y] :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [induce_isLink, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
    implies_true]

lemma induce_inter_distrib (X : Set α) : (G ∩ H)[X] = G[X] ∩ H[X] :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [induce_isLink, inter_isLink_iff, iff_def, and_self, implies_true]

lemma vertexDelete_union (X Y : Set α) : G - (X ∪ Y) = (G - X) ∩ (G - Y) :=
  Graph.ext (by simp [diff_inter_diff]) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, mem_union, not_or, inter_isLink_iff, iff_def,
    not_false_eq_true, and_self, implies_true]

lemma vertexDelete_inter_distrib (X : Set α) : (G ∩ H) - X = (G - X) ∩ (H - X) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, inter_isLink_iff, iff_def, not_false_eq_true,
    and_self, implies_true]

lemma edgeDelete_union (F₁ F₂ : Set β) : G ＼ (F₁ ∪ F₂) = (G ＼ F₁) ∩ (G ＼ F₂) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, mem_union, not_or, inter_isLink_iff, iff_def,
    not_false_eq_true, and_self, implies_true]

lemma edgeDelete_inter_distrib (F : Set β) : (G ∩ H) ＼ F = (G ＼ F) ∩ (H ＼ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, inter_isLink_iff, iff_def, not_false_eq_true, and_self,
    implies_true]

lemma edgeRestrict_inter (F₁ F₂ : Set β) : (G ↾ (F₁ ∩ F₂)) = (G ↾ F₁) ∩ (G ↾ F₂) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
    implies_true]

lemma edgeRestrict_inter_distrib (F : Set β) : (G ∩ H) ↾ F = (G ↾ F) ∩ (H ↾ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, inter_isLink_iff, iff_def, and_self, implies_true]

protected lemma inter_distrib_iInter [Nonempty ι] {H : ι → Graph α β} :
    G ∩ (Graph.iInter H) = Graph.iInter (fun i ↦ G ∩ (H i)) :=
  Graph.ext (by simp [inter_iInter]) (by
    simp only [inter_isLink_iff, iInter_isLink]
    rintro i x y
    rw [forall_and_left])

protected lemma inter_distrib_sInter [Nonempty ι] {s : Set (Graph α β)} (hne : s.Nonempty) :
    G ∩ (Graph.sInter s hne) = Graph.sInter ((G ∩ ·) '' s) (by simpa) := by
  rw [Graph.sInter_image hne]
  unfold Graph.sInter
  have := hne.to_subtype
  rw [Graph.inter_distrib_iInter]

protected lemma sInter_inter_sInter {s t : Set (Graph α β)} (hs : s.Nonempty) (ht : t.Nonempty) :
    Graph.sInter s hs ∩ .sInter t ht = .sInter (s ∪ t) (by simp [hs]) := by
  ext <;> aesop

protected lemma iInter_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
    {H : ι' → Graph α β} : Graph.iInter (Sum.elim G H) = .iInter G ∩ .iInter H := by
  ext <;> aesop

protected lemma iInter_option [Nonempty ι] {G₁ : Graph α β} {G : ι → Graph α β} :
    Graph.iInter (Option.elim · G₁ G) = G₁ ∩ Graph.iInter G :=
  Graph.ext (by simp [Set.iInter_option]) (by simp [Option.forall])

protected lemma sInter_insert {s : Set (Graph α β)} (G : Graph α β) (hne : s.Nonempty) :
    Graph.sInter (insert G s) (by simp) = G ∩ Graph.sInter s hne := by
  ext v <;> simp

protected lemma iInter_le_of_forall_le [Nonempty ι] (h : ∀ i : ι, Hι i ≤ G) :
    Graph.iInter Hι ≤ G :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| h _

protected lemma sInter_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) (hne : Gs.Nonempty) :
    Graph.sInter Gs hne ≤ G :=
  have := hne.to_subtype
  Graph.iInter_le_of_forall_le (by simpa)

/-- A nonempty intersection of induced subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isInducedSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤i G) :
    Graph.iInter Hι ≤i G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  isLink_of_mem_mem := by
    simp only [iInter_vertexSet, mem_iInter, iInter_isLink]
    exact fun e x y he hx hy i ↦ (h i).isLink_of_mem_mem he (hx i) (hy i)

/-- A nonempty intersection of spanning subgraphs of `G` is a spanning subgraph of `G`.-/
lemma iInter_isSpanningSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤s G) :
    Graph.iInter Hι ≤s G where
  vertexSet_eq := iInter_eq_const fun i ↦ (h i).vertexSet_eq
  isLink_of_isLink := (Graph.iInter_le_of_forall_le fun i ↦ (h i).le).isLink_of_isLink

/-- A nonempty intersection of closed subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isClosedSubgraph [Nonempty ι] (h : ∀ i, Hι i ≤c G) :
    Graph.iInter Hι ≤c G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  closed e x he := by
    simp only [iInter_vertexSet, mem_iInter, iInter_edgeSet, mem_setOf_eq]
    rintro hx
    obtain ⟨y, hy⟩ := he
    use x, y, fun i ↦ by rwa [(h i).isLink_iff_of_mem (hx i)]

lemma sInter_isInducedSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤i G) (hne : Gs.Nonempty) :
    Graph.sInter Gs hne ≤i G :=
  have := hne.to_subtype
  iInter_isInducedSubgraph <| by simpa

lemma sInter_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ Gs → H ≤c G) (hne : Gs.Nonempty) :
    Graph.sInter Gs hne ≤c G :=
  have := hne.to_subtype
  iInter_isClosedSubgraph <| by simpa

end Graph
