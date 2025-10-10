import Matroid.Graph.Subgraph.Compatible
import Matroid.ForMathlib.Partition.Lattice

@[simp]
lemma Set.forall_mem_const {α : Type*} {p : Prop} {s : Set α} (hs : s.Nonempty) :
    (∀ x ∈ s, p) ↔ p := ⟨fun h ↦ h _ hs.some_mem, fun hp _ _ ↦ hp⟩

@[simp]
lemma Set.forall_mem_and {α : Type*} {p q : α → Prop} {s : Set α} :
    (∀ x ∈ s, p x ∧ q x) ↔ (∀ x ∈ s, p x) ∧ (∀ x ∈ s, q x) :=
  ⟨fun h ↦ ⟨fun x hx ↦ (h x hx).1, fun x hx ↦ (h x hx).2⟩,
    fun ⟨hp, hq⟩ x hx ↦ ⟨hp x hx, hq x hx⟩⟩

variable {α β ι ι' : Type*} [CompleteLattice α] {a b c : α} {x y z u v w : α} {e f : β}
  {G G₁ G₂ H H₁ H₂ : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}
  {P Q : Partition (Set α)}

open Set Function

namespace Graph

/-! ### Indexed Intersections -/

/-- The intersection of a nonempty family of pairwise compatible graphs.
  Remove any disagreeing edges. -/
@[simps vertexPartition vertexSet isLink]
protected def iInter [Nonempty ι] (G : ι → Graph α β) : Graph α β where
  vertexPartition := Partition.iInter fun i ↦ P(G i)
  vertexSet := ⋂ i, V(G i)
  vertexSet_eq_parts := by simp
  IsLink e x y := ∀ i, (G i).IsLink e x y
  isLink_symm e he x y := by simp [isLink_comm]
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' :=
    (h (Classical.arbitrary ι)).left_eq_or_eq (h' (Classical.arbitrary ι))
  left_mem_of_isLink e x y h := by
    rw [mem_iInter]
    exact fun i ↦ (G i).left_mem_of_isLink (h i)

variable {G : ι → Graph α β} [Nonempty ι]

@[simp]
lemma iInter_isLink_eq : (Graph.iInter G).IsLink e = fun x y ↦ ∀ i, (G i).IsLink e x y := by
  ext x y
  simp

@[simp]
lemma iInter_edgeSet (hG : Pairwise (Compatible on G)) : E(Graph.iInter G) = ⋂ i, E(G i) := by
  ext e
  simp only [Graph.iInter, mem_setOf_eq, mem_iInter, edge_mem_iff_exists_isLink]
  refine ⟨fun ⟨x, y, h⟩ i ↦ ⟨x, y, h i⟩, fun h ↦ ?_⟩
  obtain ⟨x, y, h'⟩ := h (Classical.arbitrary ι)
  use x, y, fun i ↦ h'.of_compatible (hG.of_refl (Classical.arbitrary ι) i)
    (h i).choose_spec.choose_spec.edge_mem

lemma iInter_edgeSet_not_compatible : E(Graph.iInter G) = {e | ∃ u v, ∀ i, (G i).IsLink e u v} := by
  simp [Graph.iInter]

protected lemma iInter_le (i : ι) : Graph.iInter G ≤ G i where
  vertexSet_subset := by
    rw [← vertexSet_eq_parts, ← (G i).vertexSet_eq_parts]
    exact Partition.iInter_subset _ _
  isLink_of_isLink _ _ _ h := h i

@[simp]
lemma le_iInter_iff : H ≤ Graph.iInter G ↔ ∀ i, H ≤ G i := by
  let j := Classical.arbitrary ι
  refine ⟨fun h i ↦ h.trans <| Graph.iInter_le .., fun h ↦ ?_⟩
  apply le_of_le_le_subset_subset (h j) (Graph.iInter_le ..) ?_ fun e he ↦ ?_
  · rw [← vertexPartition_subset_iff]
    apply Partition.subset_iInter_iff.mpr
    simp [fun i ↦ vertexSet_mono (h i)]
  simp only [iInter_edgeSet_not_compatible, mem_setOf_eq]
  obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet he
  use x, y, fun i ↦ hbtw.of_le (h i)

@[simp]
protected lemma iInter_const (G : Graph α β) : Graph.iInter (fun (_ : ι) ↦ G) = G := by
  apply le_antisymm (Graph.iInter_le (Classical.arbitrary ι))
  rw [le_iInter_iff]
  exact fun i ↦ le_refl G

protected lemma iInter_comp_le [Nonempty ι'] {f : ι' → ι} :
    Graph.iInter G ≤ Graph.iInter (fun i ↦ G (f i)) := by
  rw [Graph.le_iInter_iff]
  exact fun i ↦ Graph.iInter_le (f i)

lemma iInter_comp_eq_of_surj [Nonempty ι'] {f : ι' → ι} (hf : Function.Surjective f) :
    Graph.iInter G = Graph.iInter (fun i ↦ G (f i)) :=
  le_antisymm (Graph.iInter_comp_le) <| by
  rw [Graph.le_iInter_iff]
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.iInter_le i'

omit [Nonempty ι] in
lemma iInter_range [Nonempty ι'] {f : ι' → ι} {G : (Set.range f) → Graph α β} :
    Graph.iInter G = Graph.iInter (fun i ↦ G (Set.rangeFactorization f i)) :=
  iInter_comp_eq_of_surj rangeFactorization_surjective

@[simp]
lemma iInter_inc : (Graph.iInter G).Inc e x ↔ ∃ y, ∀ i, (G i).IsLink e x y := by
  simp only [Inc, iInter_isLink]

@[simp]
lemma iInter_isLoopAt : (Graph.iInter G).IsLoopAt e x ↔ ∀ i, (G i).IsLoopAt e x := by
  simp only [IsLoopAt, iInter_isLink]

@[simp]
lemma iInter_isNonloopAt : (Graph.iInter G).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ i, (G i).IsLink e x y := by
  simp only [IsNonloopAt, iInter_isLink]

@[simp]
lemma induce_iInter (X : Set α) : (Graph.iInter G)[X] = .iInter (fun i ↦ (G i)[X]) :=
    Graph.ext (by simp [iInter_inter]) fun e x y ↦ by simp [forall_and_right]

@[simp]
lemma vertexDelete_iInter (X : Set α) : (Graph.iInter G) - X = .iInter (fun i ↦ (G i) - X) :=
  Graph.ext (by ext; simp [forall_and_right]) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, iInter_isLink, iff_def, not_false_eq_true,
    and_self, implies_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).right

@[simp]
lemma edgeDelete_iInter (F : Set β) : (Graph.iInter G) ＼ F = .iInter (fun i ↦ (G i) ＼ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, iInter_isLink, iff_def, not_false_eq_true, and_self,
    implies_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).right

@[simp]
lemma edgeRestrict_iInter (F : Set β) : (Graph.iInter G) ↾ F = .iInter (fun i ↦ (G i) ↾ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, iInter_isLink, iff_def, and_self, implies_true,
    and_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).left

/-! ### Set Intersections -/

/-- The intersection of a nonempty set of pairwise compatible graphs. -/
@[simps! isLink edgeSet]
protected def sInter (s : Set (Graph α β)) (hne : s.Nonempty) : Graph α β :=
  @Graph.iInter α _ _ _ hne.to_subtype (fun G : s ↦ G.1)

variable {s t : Set (Graph α β)} {G H : Graph α β}

@[simp]
lemma sInter_vertexPartition (hne : s.Nonempty) :
    P(Graph.sInter s hne) = Partition.sInter (Graph.vertexPartition '' s) (by simpa) :=
  Partition.ext fun x ↦ by simp [Graph.sInter]

@[simp]
lemma sInter_vertexSet (hne : s.Nonempty) : V(Graph.sInter s hne) = ⋂ G ∈ s, V(G) := by
  rw [← (Graph.sInter s hne).vertexSet_eq_parts, sInter_vertexPartition hne]
  ext
  simp

protected lemma sInter_le (hG : G ∈ s) : Graph.sInter s ⟨G, hG⟩ ≤ G := by
  rw [Graph.sInter]
  generalize_proofs h
  exact Graph.iInter_le (⟨G, hG⟩ : s)

@[simp]
protected lemma le_sInter_iff (hne : s.Nonempty) : H ≤ Graph.sInter s hne ↔ ∀ G ∈ s, H ≤ G := by
  simp [Graph.sInter]

protected lemma sInter_anti (hne : s.Nonempty) (hne' : t.Nonempty) (hle : s ⊆ t) :
    Graph.sInter t hne' ≤ Graph.sInter s hne := by
  rw [Graph.le_sInter_iff hne]
  exact fun G hGs ↦ Graph.sInter_le (hle hGs)

def Equiv.insert_option {s : Set α} [DecidablePred fun (x : α) => x ∈ s] (has : a ∉ s) :
    Option s ≃ (insert a s : Set α) :=
  (Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm

protected lemma sInter_insert_eq_iInter [DecidablePred (· ∈ s)] (hGs : G ∉ s) :
    Graph.sInter (insert G s) (by simp) = Graph.iInter
    ((fun G : (insert G s : Set _) ↦ G.1) ∘ (Equiv.insert_option hGs)) :=
  Graph.iInter_comp_eq_of_surj <| Equiv.surjective (Equiv.insert_option hGs)

omit [Nonempty ι] in
protected lemma sInter_image {s : Set ι} (hne : s.Nonempty) (f : ι → Graph α β) :
    Graph.sInter (f '' s) (by simpa) = @Graph.iInter  _ _ _ _ hne.to_subtype (f · : s → _) := by
  rw [Graph.sInter]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  have := hne.to_subtype
  exact Graph.iInter_comp_eq_of_surj (f := f') fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩

protected lemma sInter_range {f : ι → Graph α β} :
    Graph.sInter (Set.range f) (range_nonempty f) = .iInter f := by
  rw [Graph.sInter]
  exact Graph.iInter_comp_eq_of_surj rangeFactorization_surjective

@[simp]
protected lemma sInter_singleton (G : Graph α β) : Graph.sInter {G} (by simp) = G := by
  apply le_antisymm (Graph.sInter_le (by simp))
  rw [Graph.le_sInter_iff (by simp)]
  exact fun G_2 a ↦ Eq.ge a

@[simp]
lemma sInter_inc (hs : s.Nonempty) :
    (Graph.sInter s hs).Inc e x ↔ ∃ y, ∀ G ∈ s, G.IsLink e x y := by
  simp only [Inc, sInter_isLink]

@[simp]
lemma sInter_isLoopAt (hs : s.Nonempty) :
    (Graph.sInter s hs).IsLoopAt e x ↔ ∀ G ∈ s, G.IsLoopAt e x := by
  simp only [IsLoopAt, sInter_isLink]

@[simp]
lemma sInter_isNonloopAt (hs : s.Nonempty) :
    (Graph.sInter s hs).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ G ∈ s, G.IsLink e x y := by
  simp only [IsNonloopAt, sInter_isLink]

@[simp]
lemma induce_sInter (hs : s.Nonempty) (X : Set α) :
    (Graph.sInter s hs)[X] = .sInter ((·[X]) '' s) (by simpa) :=
  Graph.ext (by ext x; simp [hs]) fun e x y ↦ by
  simp +contextual only [induce_isLink, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma vertexDelete_sInter (hs : s.Nonempty) (X : Set α) :
    (Graph.sInter s hs) - X = .sInter ((· - X) '' s) (by simpa) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · ext x
    have : (∀ a ∈ s, x ∈ V(a)) ∧ x ∉ X ↔ ∀ a ∈ s, x ∈ V(a) ∧ x ∉ X :=
      ⟨fun ⟨ha, hx⟩ a has ↦ ⟨ha a has, hx⟩, fun h ↦ ⟨fun a b ↦ (h a b).1, (h _ hs.some_mem).2⟩⟩
    simpa
  simp +contextual only [vertexDelete_isLink_iff, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeDelete_sInter (hs : s.Nonempty) (F : Set β) :
    (Graph.sInter s hs) ＼ F = .sInter ((· ＼ F) '' s) (by simpa) :=
  Graph.ext (by ext; simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeRestrict_sInter (hs : s.Nonempty) (F : Set β) :
    (Graph.sInter s hs) ↾ F = .sInter ((· ↾ F) '' s) (by simpa) :=
  Graph.ext (by ext; simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, and_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).left

/-! ### Intersections -/

/-- The intersection of two graphs `G` and `H`. There seems to be no good way to
defined junk values so that this has the right edge and vertex set, so the
edges are precisely those on which `G` and `H` agree, and the edge set is a subset
of `E(G) ∩ E(H)`,
with equality if `G` and `H` are compatible.   -/
protected def inter (G H : Graph α β) : Graph α β :=
  Graph.sInter {G, H} (by simp)

instance : Inter (Graph α β) where inter := Graph.inter

@[simp]
lemma sInter_pair (G H : Graph α β) : Graph.sInter {G, H} (by simp) = G ∩ H := rfl

@[simp]
lemma inter_vertexSet (G H : Graph α β) : V(G ∩ H) = V(G) ∩ V(H) := by
  rw [← sInter_pair, sInter_vertexSet]
  simp

@[simp]
lemma inter_vertexPartition (G H : Graph α β) : P(G ∩ H) = P(G) ∩ P(H) :=
  Partition.ext fun x ↦ by simp

@[simp]
lemma inter_isLink : (G ∩ H).IsLink e = G.IsLink e ⊓ H.IsLink e := by
  ext
  rw [← sInter_pair, sInter_isLink]
  simp

protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G := by
  refine Graph.ext ?_ <| by simp [and_comm]
  rw [inter_vertexSet, inter_vertexSet, V(G).inter_comm]

lemma inter_edgeSet (G H : Graph α β) :
    E(G ∩ H) = {e ∈ E(G) ∩ E(H) | G.IsLink e = H.IsLink e} := by
  simp only [edgeSet_eq_setOf_exists_isLink, inter_isLink, mem_inter_iff, mem_setOf_eq,
    funext_iff, eq_iff_iff, Set.ext_iff]
  exact fun e ↦ ⟨fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
    fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩,
    fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩⟩

@[simp]
lemma Compatible.inter_edgeSet (h : G.Compatible H) : E(G ∩ H) = E(G) ∩ E(H) := by
  ext e
  simp only [Graph.inter_edgeSet, mem_inter_iff, mem_setOf_eq, and_iff_left_iff_imp]
  exact (h ·)

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
protected lemma inter_le_left : G ∩ H ≤ G where
  vertexSet_subset := (inter_vertexSet G H) ▸ inter_subset_left
  isLink_of_isLink := by simp +contextual

@[simp]
protected lemma inter_le_right : G ∩ H ≤ H :=
  Graph.inter_comm G H ▸ Graph.inter_le_left

protected lemma le_inter (h₁ : H ≤ G₁) (h₂ : H ≤ G₂) : H ≤ G₁ ∩ G₂ where
  vertexSet_subset := (inter_vertexSet G₁ G₂) ▸ subset_inter (vertexSet_mono h₁) (vertexSet_mono h₂)
  isLink_of_isLink e x y h := by simp [h.of_le h₁, h.of_le h₂]

instance : SemilatticeInf (Graph α β) where
  inf := Graph.inter
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter

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

lemma inter_eq_iInter : G ∩ H = Graph.iInter (fun b ↦ bif b then G else H) :=
  Graph.ext (by ext; simp [and_comm]) (by simp [and_comm])

lemma le_inter_iff : H ≤ G₁ ∩ G₂ ↔ H ≤ G₁ ∧ H ≤ G₂ := by
  simp [inter_eq_iInter, and_comm]

lemma inter_eq_self_of_le (hle : G ≤ H) : G ∩ H = G :=
  le_antisymm Graph.inter_le_left <| by simpa [le_inter_iff]

lemma le_of_inter_eq_self (h : G ∩ H = G) : G ≤ H := by
  rw [← h]
  exact Graph.inter_le_right

lemma inter_mono_left (hle : G₁ ≤ G₂) : G₁ ∩ H ≤ G₂ ∩ H := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left.trans hle, Graph.inter_le_right⟩

lemma inter_mono_right (hle : H₁ ≤ H₂) : G ∩ H₁ ≤ G ∩ H₂ := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left, Graph.inter_le_right.trans hle⟩

lemma inter_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) : G₁ ∩ H₁ ≤ G₂ ∩ H₂ :=
  (inter_mono_right hleH).trans (inter_mono_left hleG)

lemma edgeSet_induce_inter_eq_edgeSet_induce_of_le (h : G ≤ H) : E(G) ∩ E(H[X]) = E(G[X]) :=
  Set.ext fun _ ↦ ⟨fun ⟨he, x, y, hl, hx, hy⟩ => ⟨x, y, hl.of_le_of_mem h he, hx, hy⟩,
    fun ⟨x, y, hl, hx, hy⟩ => ⟨hl.edge_mem, x, y, hl.of_le h, hx, hy⟩⟩

lemma induce_inter (X Y : Set α) : G[X ∩ Y] = G[X] ∩ G[Y] :=
  Graph.ext (by simp; exact inter_inter_distrib_left V(G) X Y) fun e x y ↦ by
  simp +contextual only [induce_isLink, mem_inter_iff, inter_isLink, Pi.inf_apply, inf_Prop_eq]
  tauto

lemma induce_inter_distrib (X : Set α) : (G ∩ H)[X] = G[X] ∩ H[X] :=
  Graph.ext (by simp; exact inter_inter_distrib_right V(G) V(H) X) fun e x y ↦ by
  simp +contextual only [induce_isLink, inter_isLink, Pi.inf_apply, inf_Prop_eq]
  tauto

lemma vertexDelete_union (X Y : Set α) : G - (X ∪ Y) = (G - X) ∩ (G - Y) :=
  Graph.ext (by simp [diff_inter_diff]) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, mem_union, not_or, inter_isLink, Pi.inf_apply,
    inf_Prop_eq, iff_def, not_false_eq_true, and_self, implies_true]

lemma vertexDelete_inter_distrib (X : Set α) : (G ∩ H) - X = (G - X) ∩ (H - X) :=
  Graph.ext (by simp [diff_inter_distrib_right]) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, inter_isLink, Pi.inf_apply, inf_Prop_eq, iff_def,
    not_false_eq_true, and_self, implies_true]

lemma edgeDelete_union (F₁ F₂ : Set β) : G ＼ (F₁ ∪ F₂) = (G ＼ F₁) ∩ (G ＼ F₂) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, mem_union, not_or, inter_isLink, Pi.inf_apply,
    inf_Prop_eq, iff_def, not_false_eq_true, and_self, implies_true]

lemma edgeDelete_inter_distrib (F : Set β) : (G ∩ H) ＼ F = (G ＼ F) ∩ (H ＼ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, inter_isLink, Pi.inf_apply, inf_Prop_eq, iff_def,
    not_false_eq_true, and_self, implies_true]

lemma edgeRestrict_inter (F₁ F₂ : Set β) : (G ↾ (F₁ ∩ F₂)) = (G ↾ F₁) ∩ (G ↾ F₂) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, mem_inter_iff, inter_isLink, Pi.inf_apply,
    inf_Prop_eq, iff_def, and_self, implies_true]

lemma edgeRestrict_inter_distrib (F : Set β) : (G ∩ H) ↾ F = (G ↾ F) ∩ (H ↾ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, inter_isLink, Pi.inf_apply, inf_Prop_eq, iff_def,
    and_self, implies_true]

protected lemma inter_distrib_iInter {H : ι → Graph α β} :
    G ∩ (Graph.iInter H) = Graph.iInter (fun i ↦ G ∩ (H i)) :=
  Graph.ext (by ext; simp [forall_and_left]) (by
    simp only [inter_isLink, iInter_isLink_eq, Pi.inf_apply, inf_Prop_eq, iInter_isLink]
    rintro i x y
    rw [forall_and_left])

protected lemma inter_distrib_sInter (hne : s.Nonempty) :
    G ∩ (Graph.sInter s hne) = Graph.sInter ((G ∩ ·) '' s) (by simpa) := by
  rw [Graph.sInter_image hne]
  unfold Graph.sInter
  have := hne.to_subtype
  rw [Graph.inter_distrib_iInter]

protected lemma sInter_inter_sInter {s t : Set (Graph α β)} (hs : s.Nonempty) (ht : t.Nonempty) :
    Graph.sInter s hs ∩ .sInter t ht = .sInter (s ∪ t) (by simp [hs]) := by
  ext <;> aesop

protected lemma iInter_sum [Nonempty ι'] {G : ι → Graph α β}
    {H : ι' → Graph α β} : Graph.iInter (Sum.elim G H) = .iInter G ∩ .iInter H := by
  ext <;> aesop

@[simp]
protected lemma iInter_option {G₁ : Graph α β} {G : ι → Graph α β} :
    Graph.iInter (Option.elim · G₁ G) = G₁ ∩ Graph.iInter G :=
  Graph.ext (by ext; simp [Option.forall]) (by simp [Option.forall])

protected lemma sInter_insert {s : Set (Graph α β)} (G : Graph α β) (hne : s.Nonempty) :
    Graph.sInter (insert G s) (by simp) = G ∩ Graph.sInter s hne := by
  ext v <;> simp

end Graph
namespace Graph

lemma iInter_option_eq_sInter_insert {G₁ : Graph α β} {G : ι → Graph α β} :
    Graph.iInter (Option.elim · G₁ G) = Graph.sInter (insert G₁ (range G)) (by simp) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · suffices (fun x : Option ι ↦ x.elim G₁ G) = fun _ ↦ G₁ by simp [range_eq_empty G]
    refine funext fun x ↦ ?_
    cases x with | none => rfl | some val => exact (IsEmpty.false val).elim
  rw [Graph.sInter_insert _ (range_nonempty _), Graph.sInter_range, Graph.iInter_option]

-- protected lemma union_iInter [Nonempty ι] {H : ι → Graph α β} (hc : ∀ i, G.Compatible (H i))
--     (hH : Pairwise (Compatible on H)) :
--     G ∪ (Graph.iInter H hH) = Graph.iInter (fun i ↦ G ∪ (H i))
--     (by
--       refine fun i j hij ↦ (h)
--     )

--     := by
--   _

  -- rw [Graph.sUnion, Graph.sUnion]
  -- generalize_proofs h₁ h₂
  -- rw [Graph.inter_distrib_iUnion _]
