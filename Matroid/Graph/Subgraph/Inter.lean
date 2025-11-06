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

variable {α β ι ι' : Type*} {a b c : α} {x y z u v w : α} {e f : β}
  {G G₁ G₂ H H₁ H₂ : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

namespace Graph
/-! ### Indexed Intersections -/

/-- The intersection of a nonempty family of pairwise compatible graphs.
  Remove any disagreeing edges. -/
@[simps]
protected def iInter [Nonempty ι] (G : ι → Graph α β) : Graph α β where
  vertexSet := ⋂ i, V(G i)
  edgeSet := {e | ∃ x y, ∀ i, (G i).IsLink e x y}
  IsLink e x y := ∀ i, (G i).IsLink e x y
  isLink_symm e he x y := by simp [isLink_comm]
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' :=
    (h (Classical.arbitrary ι)).left_eq_or_eq (h' (Classical.arbitrary ι))
  edge_mem_iff_exists_isLink e := by simp
  left_mem_of_isLink e x y h := mem_iInter.2 fun i ↦ (h i).left_mem

protected lemma iInter_le {G : ι → Graph α β} [Nonempty ι] (i : ι) : Graph.iInter G ≤ G i where
  vertex_subset := iInter_subset (fun i ↦ V(G i)) i
  isLink_of_isLink _ _ _ h := h i

@[simp]
lemma le_iInter_iff [Nonempty ι] {G : ι → Graph α β} :
    H ≤ Graph.iInter G ↔ ∀ i, H ≤ G i := by
  let j := Classical.arbitrary ι
  refine ⟨fun h i ↦ h.trans <| Graph.iInter_le .., fun h ↦ ?_⟩
  apply le_of_le_le_subset_subset (h j) (Graph.iInter_le ..) ?_ fun e he ↦ ?_
  · simp [fun i ↦ vertexSet_mono (h i)]
  simp only [iInter_edgeSet, mem_setOf_eq]
  obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet he
  use x, y, fun i ↦ hbtw.of_le (h i)

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

/-- The intersection of a nonempty set of pairwise compatible graphs. -/
@[simps!]
protected def sInter (s : Set (Graph α β)) (hne : s.Nonempty) : Graph α β :=
  @Graph.iInter _ _ _ hne.to_subtype (fun G : s ↦ G.1)

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

def Equiv.insert_option {s : Set α} [DecidablePred fun (x : α) => x ∈ s] (a : α) (has : a ∉ s) :
    Option s ≃ (insert a s : Set α) :=
  (Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm

protected lemma sInter_insert_eq_iInter [DecidablePred (· ∈ s)]
    (hGs : G ∉ s) : Graph.sInter (insert G s) (by simp) = Graph.iInter
    ((fun G : (insert G s : Set _) ↦ G.1) ∘ (Equiv.insert_option G hGs)) :=
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
lemma sInter_inc_iff (hs : s.Nonempty) :
    (Graph.sInter s hs).Inc e x ↔ ∃ y, ∀ G ∈ s, G.IsLink e x y := by
  simp only [Inc, sInter_isLink]

@[simp]
lemma sInter_isLoopAt_iff (hs : s.Nonempty) :
    (Graph.sInter s hs).IsLoopAt e x ↔ ∀ G ∈ s, G.IsLoopAt e x := by
  simp only [IsLoopAt, sInter_isLink]

@[simp]
lemma sInter_isNonloopAt_iff (hs : s.Nonempty) :
    (Graph.sInter s hs).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ G ∈ s, G.IsLink e x y := by
  simp only [IsNonloopAt, sInter_isLink]

@[simp]
lemma induce_sInter (hs : s.Nonempty) (X : Set α) :
    (Graph.sInter s hs)[X] = .sInter ((·[X]) '' s) (by simpa) := by
  refine Graph.ext (by simp; exact (biInter_const hs X).symm) fun e x y ↦ ?_
  simp +contextual only [induce_isLink_iff, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma vertexDelete_sInter (hs : s.Nonempty) (X : Set α) :
    (Graph.sInter s hs) - X = .sInter ((· - X) '' s) (by simpa) := by
  refine Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ ?_
  simp +contextual only [vertexDelete_isLink_iff, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeDelete_sInter (hs : s.Nonempty) (F : Set β) :
    (Graph.sInter s hs) ＼ F = .sInter ((· ＼ F) '' s) (by simpa) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeRestrict_sInter (hs : s.Nonempty) (F : Set β) :
    (Graph.sInter s hs) ↾ F = .sInter ((· ↾ F) '' s) (by simpa) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, and_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).left

/-! ### Intersections -/

/-- The intersection of two graphs `G` and `H`. There seems to be no good way to
defined junk values so that this has the right edge and vertex set, so the
edges are precisely those on which `G` and `H` agree, and the edge set is a subset
of `E(G) ∩ E(H)`,
with equality if `G` and `H` are compatible.   -/
protected def inter (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∩ V(H)
  IsLink e x y := G.IsLink e x y ∧ H.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1.symm, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  edge_mem_iff_exists_isLink e := by simp
  left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩

instance : Inter (Graph α β) where inter := Graph.inter

@[simp]
lemma inter_vertexSet (G H : Graph α β) : V(G ∩ H) = V(G) ∩ V(H) := rfl

@[simp]
lemma inter_isLink_iff : (G ∩ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G :=
  Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

lemma inter_edgeSet (G H : Graph α β) :
    E(G ∩ H) = {e ∈ E(G) ∩ E(H) | G.IsLink e = H.IsLink e} := by
  simp only [edgeSet_eq_setOf_exists_isLink, inter_isLink_iff, mem_inter_iff, mem_setOf_eq,
    funext_iff, eq_iff_iff, Set.ext_iff]
  exact fun e ↦ ⟨fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
    fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩,
    fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩⟩

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
  vertex_subset := inter_subset_left
  isLink_of_isLink := by simp +contextual

@[simp]
protected lemma inter_le_right : G ∩ H ≤ H :=
  Graph.inter_comm _ _ ▸ Graph.inter_le_left

protected lemma le_inter (h₁ : H ≤ G₁) (h₂ : H ≤ G₂) : H ≤ G₁ ∩ G₂ where
  vertex_subset := subset_inter (vertexSet_mono h₁) (vertexSet_mono h₂)
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

lemma inter_mono_left (hle : G₁ ≤ G₂) : G₁ ∩ H ≤ G₂ ∩ H := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left.trans hle, Graph.inter_le_right⟩

lemma inter_mono_right (hle : H₁ ≤ H₂) : G ∩ H₁ ≤ G ∩ H₂ := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left, Graph.inter_le_right.trans hle⟩

lemma inter_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) : G₁ ∩ H₁ ≤ G₂ ∩ H₂ :=
  (inter_mono_right hleH).trans (inter_mono_left hleG)

lemma stronglyDisjoint_iff_disjoint_of_compatible (h : H₁.Compatible H₂) :
    StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ := by
  rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible, Set.disjoint_iff_inter_eq_empty,
    disjoint_iff, ← vertexSet_eq_empty_iff]
  simp [h]

lemma edgeSet_induce_inter_eq_edgeSet_induce_of_le (h : G ≤ H) : E(G) ∩ E(H[X]) = E(G[X]) :=
  Set.ext fun _ ↦ ⟨fun ⟨he, x, y, hl, hx, hy⟩ => ⟨x, y, hl.of_le_of_mem h he, hx, hy⟩,
    fun ⟨x, y, hl, hx, hy⟩ => ⟨hl.edge_mem, x, y, hl.of_le h, hx, hy⟩⟩

lemma induce_inter (X Y : Set α) : G[X ∩ Y] = G[X] ∩ G[Y] :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [induce_isLink_iff, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
    implies_true]

lemma induce_inter_distrib (X : Set α) : (G ∩ H)[X] = G[X] ∩ H[X] :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [induce_isLink_iff, inter_isLink_iff, iff_def, and_self, implies_true]

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

lemma iInter_option_eq_sInter_insert {G₁ : Graph α β} {G : ι → Graph α β} :
    Graph.iInter (Option.elim · G₁ G) = Graph.sInter (insert G₁ (range G)) (by simp) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [range_eq_empty G]
  rw [Graph.sInter_insert _ (range_nonempty _), Graph.sInter_range, Graph.iInter_option]

end Graph

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
