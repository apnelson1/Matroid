import Matroid.Graph.Compatible
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

namespace Graph

/-! ### Indexed Intersections -/

/-- The intersection of a nonempty family of pairwise compatible graphs.
  Remove any disagreeing edges. -/
@[simps dup isLink edgeSet]
protected def iInter [Nonempty ι] (G : ι → Graph α β) : Graph α β where
  Dup := ⨅ i, (G i).Dup
  IsLink e x y :=
    let j := Classical.arbitrary ι
    ∀ i, (G i).Dup x = (G j).Dup x ∧ (G i).Dup y = (G j).Dup y ∧ (G i).IsLink e x y
  isLink_symm e he a b hl i := by
    obtain ⟨ha, hb, h⟩ := hl i
    exact ⟨hb, ha, h.symm⟩
  dup_or_dup_of_isLink_of_isLink e a b c d hlab' hlcd' := by
    let j := Classical.arbitrary ι
    simp_all only [Partition.iInf_rel, iInf_apply, ciInf_const]
    obtain ⟨ha, hb, hlab⟩ := hlab' j
    obtain ⟨hc, hd, hlcd⟩ := hlcd' j
    exact (G j).dup_or_dup_of_isLink_of_isLink hlab hlcd
  mem_vertexSet_of_isLink e a b hl := by
    simp only [Partition.iInf_supp, vertexSet_def, mem_iInter] at hl ⊢
    exact fun i ↦ (hl i).2.2.left_mem
  isLink_of_dup e a b c hdab hlbc i := by
    let j := Classical.arbitrary ι
    simp_all only [Partition.iInf_rel, iInf_apply, iInf_Prop_eq, true_and]
    obtain ⟨hc, hd, h⟩ := hlbc i
    use ?_, trans' (hdab i) h
    ext d
    rw [(G i).dup_left_rw (hdab i), hc, (G j).dup_left_rw (hdab j)]

@[simp]
lemma iInter_vertexSet [Nonempty ι] (G : ι → Graph α β) : V(Graph.iInter G) = ⋂ i, V(G i) := by
  rw [vertexSet_eq]
  simp

lemma iInter_dup_le [Nonempty ι] (G : ι → Graph α β) (i : ι) :
    (Graph.iInter G).Dup ≤ (G i).Dup := iInf_le _ i

protected lemma iInter_le {G : ι → Graph α β} [∀ i, Nodup (G i)] [Nonempty ι] (i : ι) :
    Graph.iInter G ≤ G i where
  dup_subset := by
    rw [(dup_atomic (G i)).subset_iff_le]
    exact iInter_dup_le G i
  isLink_of_isLink _ _ _ h := (h i).2.2

-- @[simp]
-- lemma le_iInter_iff [Nonempty ι] {G : ι → Graph α β} [∀ i, Nodup (G i)] :
--     H ≤ Graph.iInter G ↔ ∀ i, H ≤ G i := by
--   let j := Classical.arbitrary ι
--   refine ⟨fun h i ↦ h.trans <| Graph.iInter_le .., fun h ↦ ?_⟩
--   apply le_of_le_isLabelSubgraph_subset_subset (h j) (isLabelSubgraph_of_le (Graph.iInter_le ..)) ?_ fun e he ↦ ?_
--   · simp [fun i ↦ vertexSet_mono (h i)]
--   simp only [iInter_edgeSet, mem_setOf_eq]
--   obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet he
--   use x, y, fun i ↦ hbtw.of_le (h i)

-- @[simp]
-- protected lemma iInter_const [Nonempty ι] (G : Graph α β) :
--     Graph.iInter (fun (_ : ι) ↦ G) = G := by
--   apply le_antisymm (Graph.iInter_le (Classical.arbitrary ι))
--   rw [le_iInter_iff]
--   exact fun i ↦ le_refl G

-- lemma iInter_le_iUnion [Nonempty ι] {G : ι → Graph α β} (hG : Pairwise (Compatible on G)) :
--     Graph.iInter G ≤ Graph.iUnion G hG :=
--   (Graph.iInter_le (Classical.arbitrary ι)).trans <| Graph.le_iUnion ..

-- protected lemma iInter_comp_le [Nonempty ι] [Nonempty ι'] {f : ι' → ι}
--     {G : ι → Graph α β} : Graph.iInter G ≤ Graph.iInter (fun i ↦ G (f i)) := by
--   rw [Graph.le_iInter_iff]
--   exact fun i ↦ Graph.iInter_le (f i)

-- lemma iInter_comp_eq_of_surj [Nonempty ι] [Nonempty ι'] {f : ι' → ι}
--     {G : ι → Graph α β} (hf : Function.Surjective f) :
--     Graph.iInter G = Graph.iInter (fun i ↦ G (f i)) :=
--   le_antisymm (Graph.iInter_comp_le) <| by
--   rw [Graph.le_iInter_iff]
--   rintro i
--   obtain ⟨i', rfl⟩ := hf i
--   exact Graph.iInter_le i'

-- lemma iInter_range [Nonempty ι'] {f : ι' → ι} {G : (Set.range f) → Graph α β} :
--     Graph.iInter G = Graph.iInter (fun i ↦ G (Set.rangeFactorization f i)) :=
--   iInter_comp_eq_of_surj surjective_onto_range

-- @[simp]
-- lemma iInter_inc_iff [Nonempty ι] {G : ι → Graph α β} :
--     (Graph.iInter G).Inc e x ↔ ∃ y, ∀ i, (G i).IsLink e x y := by
--   simp only [Inc, iInter_isLink]

-- @[simp]
-- lemma iInter_isLoopAt_iff [Nonempty ι] {G : ι → Graph α β} :
--     (Graph.iInter G).IsLoopAt e x ↔ ∀ i, (G i).IsLoopAt e x := by
--   simp only [IsLoopAt, iInter_isLink]

-- @[simp]
-- lemma iInter_isNonloopAt_iff [Nonempty ι] {G : ι → Graph α β} :
--     (Graph.iInter G).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ i, (G i).IsLink e x y := by
--   simp only [IsNonloopAt, iInter_isLink]

-- @[simp]
-- lemma induce_iInter [Nonempty ι] {G : ι → Graph α β} (X : Set α) :
--     (Graph.iInter G)[X] = .iInter (fun i ↦ (G i)[X]) :=
--   Graph.ext (iInter_const X).symm fun e x y ↦ by
--   simp [forall_and_right]

-- @[simp]
-- lemma vertexDelete_iInter [Nonempty ι] {G : ι → Graph α β} (X : Set α) :
--     (Graph.iInter G) - X = .iInter (fun i ↦ (G i) - X) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [vertexDelete_isLink_iff, iInter_isLink, iff_def, not_false_eq_true,
--     and_self, implies_true, true_and]
--   exact fun h ↦ (h <| Classical.arbitrary ι).right

-- @[simp]
-- lemma edgeDelete_iInter [Nonempty ι] {G : ι → Graph α β} (F : Set β) :
--     (Graph.iInter G) ＼ F = .iInter (fun i ↦ (G i) ＼ F) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeDelete_isLink, iInter_isLink, iff_def, not_false_eq_true, and_self,
--     implies_true, true_and]
--   exact fun h ↦ (h <| Classical.arbitrary ι).right

-- @[simp]
-- lemma edgeRestrict_iInter [Nonempty ι] {G : ι → Graph α β} (F : Set β) :
--     (Graph.iInter G) ↾ F = .iInter (fun i ↦ (G i) ↾ F) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeRestrict_isLink, iInter_isLink, iff_def, and_self, implies_true,
--     and_true, true_and]
--   exact fun h ↦ (h <| Classical.arbitrary ι).left

-- /-! ### Set Intersections -/

-- /-- The intersection of a nonempty set of pairwise compatible graphs. -/
-- @[simps!]
-- protected def sInter (s : Set (Graph α β)) (hne : s.Nonempty) :
--     Graph α β :=
--   @Graph.iInter _ _ _ hne.to_subtype (fun G : s ↦ G.1)

-- protected lemma sInter_le {s : Set (Graph α β)} (hG : G ∈ s) :
--     Graph.sInter s ⟨G, hG⟩ ≤ G := by
--   rw [Graph.sInter]
--   generalize_proofs h
--   exact Graph.iInter_le (⟨G, hG⟩ : s)

-- @[simp]
-- protected lemma le_sInter_iff {s} (hne : s.Nonempty) :
--     H ≤ Graph.sInter s hne ↔ ∀ G ∈ s, H ≤ G := by
--   simp [Graph.sInter]

-- protected lemma sInter_anti {s t : Set (Graph α β)} (hne : s.Nonempty) (hne' : t.Nonempty)
--     (hle : s ⊆ t) : Graph.sInter t hne' ≤ Graph.sInter s hne := by
--   rw [Graph.le_sInter_iff hne]
--   exact fun G hGs ↦ Graph.sInter_le (hle hGs)

-- def Equiv.insert_option {s : Set α} [DecidablePred fun (x : α) => x ∈ s] (a : α) (has : a ∉ s) :
--     Option s ≃ (insert a s : Set α) :=
--   (Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm

-- protected lemma sInter_insert_eq_iInter {s : Set (Graph α β)} [DecidablePred (· ∈ s)]
--     (hGs : G ∉ s) : Graph.sInter (insert G s) (by simp) = Graph.iInter
--     ((fun G : (insert G s : Set _) ↦ G.1) ∘ (Equiv.insert_option G hGs)) :=
--   Graph.iInter_comp_eq_of_surj <| Equiv.surjective (Equiv.insert_option G hGs)

-- protected lemma sInter_image {s : Set ι} (hne : s.Nonempty) (f : ι → Graph α β) :
--     Graph.sInter (f '' s) (by simpa) = @Graph.iInter _ _ _ hne.to_subtype (f · : s → _) := by
--   rw [Graph.sInter]
--   let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
--   have := hne.to_subtype
--   exact Graph.iInter_comp_eq_of_surj (f := f') fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩

-- protected lemma sInter_range [Nonempty ι] {f : ι → Graph α β} :
--     Graph.sInter (Set.range f) (range_nonempty f) = .iInter f := by
--   rw [Graph.sInter]
--   exact Graph.iInter_comp_eq_of_surj (f := Set.rangeFactorization f) surjective_onto_range

-- @[simp]
-- protected lemma sInter_singleton (G : Graph α β) : Graph.sInter {G} (by simp) = G := by
--   apply le_antisymm (Graph.sInter_le (by simp))
--   rw [Graph.le_sInter_iff (by simp)]
--   exact fun G_2 a ↦ Eq.ge a

-- @[simp]
-- lemma sInter_inc_iff {s : Set (Graph α β)} (hs : s.Nonempty) :
--     (Graph.sInter s hs).Inc e x ↔ ∃ y, ∀ G ∈ s, G.IsLink e x y := by
--   simp only [Inc, sInter_isLink]

-- @[simp]
-- lemma sInter_isLoopAt_iff {s : Set (Graph α β)} (hs : s.Nonempty) :
--     (Graph.sInter s hs).IsLoopAt e x ↔ ∀ G ∈ s, G.IsLoopAt e x := by
--   simp only [IsLoopAt, sInter_isLink]

-- @[simp]
-- lemma sInter_isNonloopAt_iff {s : Set (Graph α β)} (hs : s.Nonempty) :
--     (Graph.sInter s hs).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ G ∈ s, G.IsLink e x y := by
--   simp only [IsNonloopAt, sInter_isLink]

-- @[simp]
-- lemma induce_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (X : Set α) :
--     (Graph.sInter s hs)[X] = .sInter ((·[X]) '' s) (by simpa) := by
--   refine Graph.ext (by simp; exact (biInter_const hs X).symm) fun e x y ↦ ?_
--   simp +contextual only [induce_isLink_iff, sInter_isLink, mem_image, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, true_and]
--   exact fun h ↦ (h _ hs.some_mem).right

-- @[simp]
-- lemma vertexDelete_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (X : Set α) :
--     (Graph.sInter s hs) - X = .sInter ((· - X) '' s) (by simpa) := by
--   refine Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ ?_
--   simp +contextual only [vertexDelete_isLink_iff, sInter_isLink, mem_image, forall_exists_index,
--     and_imp, forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
--   exact fun h ↦ (h _ hs.some_mem).right

-- @[simp]
-- lemma edgeDelete_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (F : Set β) :
--     (Graph.sInter s hs) ＼ F = .sInter ((· ＼ F) '' s) (by simpa) :=
--   Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ by
--   simp +contextual only [edgeDelete_isLink, sInter_isLink, mem_image, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
--   exact fun h ↦ (h _ hs.some_mem).right

-- @[simp]
-- lemma edgeRestrict_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (F : Set β) :
--     (Graph.sInter s hs) ↾ F = .sInter ((· ↾ F) '' s) (by simpa) :=
--   Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ by
--   simp +contextual only [edgeRestrict_isLink, sInter_isLink, mem_image, forall_exists_index,
--     and_imp, forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, and_true, true_and]
--   exact fun h ↦ (h _ hs.some_mem).left

-- /-! ### Intersections -/

-- /-- The intersection of two graphs `G` and `H`. There seems to be no good way to
-- defined junk values so that this has the right edge and vertex set, so the
-- edges are precisely those on which `G` and `H` agree, and the edge set is a subset
-- of `E(G) ∩ E(H)`,
-- with equality if `G` and `H` are compatible.   -/
-- protected def inter (G H : Graph α β) : Graph α β where
--   vertexSet := V(G) ∩ V(H)
--   IsLink e x y := G.IsLink e x y ∧ H.IsLink e x y
--   isLink_symm _ _ _ _ h := ⟨h.1.symm, h.2.symm⟩
--   dup_or_dup_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
--   edge_mem_iff_exists_isLink e := by simp
--   left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩

-- instance : Inter (Graph α β) where inter := Graph.inter

-- @[simp]
-- lemma inter_vertexSet (G H : Graph α β) : V(G ∩ H) = V(G) ∩ V(H) := rfl

-- @[simp]
-- lemma inter_isLink_iff : (G ∩ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

-- protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G :=
--   Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

-- lemma inter_edgeSet (G H : Graph α β) :
--     E(G ∩ H) = {e ∈ E(G) ∩ E(H) | G.IsLink e = H.IsLink e} := by
--   simp only [edgeSet_eq_setOf_exists_isLink, inter_isLink_iff, mem_inter_iff, mem_setOf_eq,
--     funext_iff, eq_iff_iff, Set.ext_iff]
--   exact fun e ↦ ⟨fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
--     fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩,
--     fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩⟩

-- lemma inter_edgeSet_subset : E(G ∩ H) ⊆ E(G) ∩ E(H) := by
--   simp +contextual [inter_edgeSet, subset_def]

-- @[simp]
-- lemma inter_inc_iff : (G ∩ H).Inc e x ↔ ∃ y, G.IsLink e x y ∧ H.IsLink e x y := by
--   simp [Inc]

-- @[simp]
-- lemma inter_isLoopAt_iff : (G ∩ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x := by
--   simp [← isLink_self_iff]

-- @[simp]
-- lemma inter_isNonloopAt_iff :
--     (G ∩ H).IsNonloopAt e x ↔ ∃ y ≠ x, G.IsLink e x y ∧ H.IsLink e x y := by
--   simp [IsNonloopAt]

-- @[simp]
-- protected lemma inter_le_left : G ∩ H ≤ G where
--   vertex_subset := inter_subset_left
--   isLink_of_isLink := by simp +contextual

-- @[simp]
-- protected lemma inter_le_right : G ∩ H ≤ H :=
--   Graph.inter_comm _ _ ▸ Graph.inter_le_left

-- protected lemma le_inter (h₁ : H ≤ G₁) (h₂ : H ≤ G₂) : H ≤ G₁ ∩ G₂ where
--   vertex_subset := subset_inter (vertexSet_mono h₁) (vertexSet_mono h₂)
--   isLink_of_isLink e x y h := by simp [h.of_le h₁, h.of_le h₂]

-- instance : SemilatticeInf (Graph α β) where
--   inf := Graph.inter
--   inf_le_left _ _ := Graph.inter_le_left
--   inf_le_right _ _ := Graph.inter_le_right
--   le_inf _ _ _ := Graph.le_inter

-- @[simp]
-- lemma inf_eq_inter : H₁ ⊓ H₂ = H₁ ∩ H₂ := rfl

-- @[simp]
-- lemma inter_eq_bot_iff : H₁ ∩ H₂ = ⊥ ↔ V(H₁) ∩ V(H₂) = ∅ := by
--   rw [← vertexSet_eq_empty_iff, inter_vertexSet]

-- lemma disjoint_iff_inter_eq_bot : Disjoint H₁ H₂ ↔ H₁ ∩ H₂ = ⊥ := by
--   rw [disjoint_iff, inf_eq_inter]

-- @[simp]
-- lemma disjoint_iff_vertexSet_inter_eq_empty : Disjoint H₁ H₂ ↔ V(H₁) ∩ V(H₂) = ∅ := by
--   rw [disjoint_iff_inter_eq_bot, inter_eq_bot_iff]

-- lemma disjoint_iff_vertexSet_disjoint : Disjoint H₁ H₂ ↔ Disjoint V(H₁) V(H₂) := by
--   rw [disjoint_iff_inter_eq_bot, inter_eq_bot_iff, Set.disjoint_iff_inter_eq_empty]

-- alias ⟨Disjoint.vertex_disjoint, _⟩ := disjoint_iff_vertexSet_disjoint

-- lemma Compatible.inter_edgeSet (h : G.Compatible H) : E(G ∩ H) = E(G) ∩ E(H) := by
--   rw [Graph.inter_edgeSet]
--   exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, h he⟩

-- lemma inter_eq_iInter : G ∩ H = Graph.iInter (fun b ↦ bif b then G else H) :=
--   Graph.ext (by simp [Set.inter_eq_iInter, Bool.apply_cond]) (by simp [and_comm])

-- lemma le_inter_iff : H ≤ G₁ ∩ G₂ ↔ H ≤ G₁ ∧ H ≤ G₂ := by
--   simp [inter_eq_iInter, and_comm]

-- lemma inter_eq_self_of_le (hle : G ≤ H) : G ∩ H = G :=
--   le_antisymm Graph.inter_le_left <| by simpa [le_inter_iff]

-- lemma le_of_inter_eq_self (h : G ∩ H = G) : G ≤ H := by
--   rw [← h]
--   exact Graph.inter_le_right

-- lemma inter_mono_left (hle : G₁ ≤ G₂) : G₁ ∩ H ≤ G₂ ∩ H := by
--   rw [le_inter_iff]
--   exact ⟨Graph.inter_le_left.trans hle, Graph.inter_le_right⟩

-- lemma inter_mono_right (hle : H₁ ≤ H₂) : G ∩ H₁ ≤ G ∩ H₂ := by
--   rw [le_inter_iff]
--   exact ⟨Graph.inter_le_left, Graph.inter_le_right.trans hle⟩

-- lemma inter_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) : G₁ ∩ H₁ ≤ G₂ ∩ H₂ :=
--   (inter_mono_right hleH).trans (inter_mono_left hleG)

-- lemma stronglyDisjoint_iff_disjoint_of_compatible (h : H₁.Compatible H₂) :
--     StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ := by
--   rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible, Set.disjoint_iff_inter_eq_empty,
--     disjoint_iff, ← vertexSet_eq_empty_iff]
--   simp [h]

-- lemma edgeSet_induce_inter_eq_edgeSet_induce_of_le (h : G ≤ H) : E(G) ∩ E(H[X]) = E(G[X]) :=
--   Set.ext fun _ ↦ ⟨fun ⟨he, x, y, hl, hx, hy⟩ => ⟨x, y, hl.of_le_of_mem h he, hx, hy⟩,
--     fun ⟨x, y, hl, hx, hy⟩ => ⟨hl.edge_mem, x, y, hl.of_le h, hx, hy⟩⟩

-- lemma induce_inter (X Y : Set α) : G[X ∩ Y] = G[X] ∩ G[Y] :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [induce_isLink_iff, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
--     implies_true]

-- lemma induce_inter_distrib (X : Set α) : (G ∩ H)[X] = G[X] ∩ H[X] :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [induce_isLink_iff, inter_isLink_iff, iff_def, and_self, implies_true]

-- lemma vertexDelete_union (X Y : Set α) : G - (X ∪ Y) = (G - X) ∩ (G - Y) :=
--   Graph.ext (by simp [diff_inter_diff]) fun e x y ↦ by
--   simp +contextual only [vertexDelete_isLink_iff, mem_union, not_or, inter_isLink_iff, iff_def,
--     not_false_eq_true, and_self, implies_true]

-- lemma vertexDelete_inter_distrib (X : Set α) : (G ∩ H) - X = (G - X) ∩ (H - X) :=
--   Graph.ext (by simp [diff_inter_distrib_right]) fun e x y ↦ by
--   simp +contextual only [vertexDelete_isLink_iff, inter_isLink_iff, iff_def, not_false_eq_true,
--     and_self, implies_true]

-- lemma edgeDelete_union (F₁ F₂ : Set β) : G ＼ (F₁ ∪ F₂) = (G ＼ F₁) ∩ (G ＼ F₂) :=
--   Graph.ext (by simp [diff_inter_diff]) fun e x y ↦ by
--   simp +contextual only [edgeDelete_isLink, mem_union, not_or, inter_isLink_iff, iff_def,
--     not_false_eq_true, and_self, implies_true]

-- lemma edgeDelete_inter_distrib (F : Set β) : (G ∩ H) ＼ F = (G ＼ F) ∩ (H ＼ F) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeDelete_isLink, inter_isLink_iff, iff_def, not_false_eq_true, and_self,
--     implies_true]

-- lemma edgeRestrict_inter (F₁ F₂ : Set β) : (G ↾ (F₁ ∩ F₂)) = (G ↾ F₁) ∩ (G ↾ F₂) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeRestrict_isLink, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
--     implies_true]

-- lemma edgeRestrict_inter_distrib (F : Set β) : (G ∩ H) ↾ F = (G ↾ F) ∩ (H ↾ F) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeRestrict_isLink, inter_isLink_iff, iff_def, and_self, implies_true]

-- protected lemma inter_distrib_iInter [Nonempty ι] {H : ι → Graph α β} :
--     G ∩ (Graph.iInter H) = Graph.iInter (fun i ↦ G ∩ (H i)) :=
--   Graph.ext (by simp [inter_iInter]) (by
--     simp only [inter_isLink_iff, iInter_isLink]
--     rintro i x y
--     rw [forall_and_left])

-- protected lemma inter_distrib_sInter [Nonempty ι] {s : Set (Graph α β)} (hne : s.Nonempty) :
--     G ∩ (Graph.sInter s hne) = Graph.sInter ((G ∩ ·) '' s) (by simpa) := by
--   rw [Graph.sInter_image hne]
--   unfold Graph.sInter
--   have := hne.to_subtype
--   rw [Graph.inter_distrib_iInter]

-- protected lemma inter_distrib_iUnion {H : ι → Graph α β} (hH : Pairwise (Compatible on H)) :
--     G ∩ (Graph.iUnion H hH) = Graph.iUnion (fun i ↦ G ∩ (H i))
--       (fun _ _ hne ↦ (hH hne).mono Graph.inter_le_right Graph.inter_le_right) :=
--   Graph.ext (by simp [inter_iUnion]) (by simp)

-- protected lemma inter_distrib_sUnion (hs : s.Pairwise Compatible) :
--     G ∩ (Graph.sUnion s hs) = Graph.sUnion ((fun K ↦ G ∩ K) '' s) (by
--       rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
--       exact (hs.of_refl hK₁ hK₂).mono Graph.inter_le_right Graph.inter_le_right) := by
--   ext <;> aesop

-- lemma Pairwise.union_compatible {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
--     (Graph.sUnion s (hst.mono subset_union_left)).Compatible
--     (Graph.sUnion t (hst.mono subset_union_right)) := by
--   refine compatible_of_le_le (G := Graph.sUnion (s ∪ t) hst) ?_ ?_ <;> rw [Graph.sUnion_le_iff]
--   <;> exact fun G hG ↦ Graph.le_sUnion hst (by simp [hG])

-- lemma sUnion_union_sUnion {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
--     Graph.sUnion s (hst.mono subset_union_left) ∪ Graph.sUnion t (hst.mono subset_union_right) =
--     Graph.sUnion (s ∪ t) hst := by
--   have hs : s.Pairwise Compatible := hst.mono subset_union_left
--   have ht : t.Pairwise Compatible := hst.mono subset_union_right
--   refine Graph.ext (by aesop) fun e x y ↦ ?_
--   rw [(Pairwise.union_compatible hst).union_isLink_iff]
--   aesop

-- protected lemma sInter_inter_sInter {s t : Set (Graph α β)} (hs : s.Nonempty) (ht : t.Nonempty) :
--     Graph.sInter s hs ∩ .sInter t ht = .sInter (s ∪ t) (by simp [hs]) := by
--   ext <;> aesop

-- lemma Compatible.sum_compatible {G : ι → Graph α β} {H : ι' → Graph α β}
--     (hGH : Pairwise (Compatible on (Sum.elim G H))) :
--     (Graph.iUnion G (hGH.sum_left)).Compatible (Graph.iUnion H (hGH.sum_right)) :=
--   compatible_of_le_le (iUnion_left_le_iUnion_sum hGH) <| iUnion_right_le_iUnion_sum hGH

-- protected lemma iUnion_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
--     {H : ι' → Graph α β} (hGH : Pairwise (Compatible on (Sum.elim G H))) :
--     Graph.iUnion (Sum.elim G H) hGH = (.iUnion G hGH.sum_left) ∪ (.iUnion H hGH.sum_right) := by
--   refine le_antisymm ?_ <| Graph.union_le (iUnion_left_le_iUnion_sum hGH)
--     (iUnion_right_le_iUnion_sum hGH)
--   rw [Graph.iUnion_le_iff]
--   rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
--   · exact le_trans (Graph.le_iUnion hGH.sum_left i) (Graph.left_le_union _ _)
--   · exact le_trans (Graph.le_iUnion hGH.sum_right i)
--       (Compatible.right_le_union (Compatible.sum_compatible hGH))

-- protected lemma iInter_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
--     {H : ι' → Graph α β} : Graph.iInter (Sum.elim G H) = .iInter G ∩ .iInter H := by
--   ext <;> aesop

-- protected lemma iInter_option [Nonempty ι] {G₁ : Graph α β} {G : ι → Graph α β} :
--     Graph.iInter (Option.elim · G₁ G) = G₁ ∩ Graph.iInter G :=
--   Graph.ext (by simp [Set.iInter_option]) (by simp [Option.forall])

-- protected lemma sInter_insert {s : Set (Graph α β)} (G : Graph α β) (hne : s.Nonempty) :
--     Graph.sInter (insert G s) (by simp) = G ∩ Graph.sInter s hne := by
--   ext v <;> simp

-- lemma iInter_option_eq_sInter_insert {G₁ : Graph α β} {G : ι → Graph α β} :
--     Graph.iInter (Option.elim · G₁ G) = Graph.sInter (insert G₁ (range G)) (by simp) := by
--   obtain hι | hι := isEmpty_or_nonempty ι
--   · simp [range_eq_empty G]
--   rw [Graph.sInter_insert _ (range_nonempty _), Graph.sInter_range, Graph.iInter_option]

-- -- protected lemma union_iInter [Nonempty ι] {H : ι → Graph α β} (hc : ∀ i, G.Compatible (H i))
-- --     (hH : Pairwise (Compatible on H)) :
-- --     G ∪ (Graph.iInter H hH) = Graph.iInter (fun i ↦ G ∪ (H i))
-- --     (by
-- --       refine fun i j hij ↦ (h)
-- --     )

-- --     := by
-- --   _

--   -- rw [Graph.sUnion, Graph.sUnion]
--   -- generalize_proofs h₁ h₂
--   -- rw [Graph.inter_distrib_iUnion _]





-- section Subgraph

-- /-! ### Subgraphs -/

-- variable {H : ι → Graph α β} {H₁ H₂ : Graph α β}

-- lemma pairwise_compatible_of_subgraph {H : ι → Graph α β} (h : ∀ i, H i ≤ G) :
--     Pairwise (Compatible on H) :=
--   fun i j _ ↦ compatible_of_le_le (h i) (h j)

-- lemma set_pairwise_compatible_of_subgraph (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
--     s.Pairwise Compatible :=
--   fun _ hi _ hj _ ↦ compatible_of_le_le (h hi) (h hj)

-- protected lemma iUnion_le_of_forall_le (h : ∀ i, H i ≤ G) :
--     Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤ G := by
--   simpa

-- protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
--     Graph.sUnion s (set_pairwise_compatible_of_subgraph h) ≤ G := by
--   simpa

-- protected lemma iInter_le_of_forall_le [Nonempty ι] (h : ∀ i, H i ≤ G) :
--     Graph.iInter H ≤ G :=
--   (Graph.iInter_le (Classical.arbitrary ι)).trans <| h _

-- protected lemma sInter_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) (hne : s.Nonempty) :
--     Graph.sInter s hne ≤ G :=
--   have := hne.to_subtype
--   Graph.iInter_le_of_forall_le (by simpa)

-- /-- A union of closed subgraphs of `G` is a closed subgraph of `G`. -/
-- lemma iUnion_isClosedSubgraph (h : ∀ i, H i ≤c G) :
--     Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤c G where
--   le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
--   closed e x he := by
--     simp only [iUnion_vertexSet, mem_iUnion, iUnion_edgeSet, forall_exists_index]
--     exact fun i hxi ↦ ⟨_, (he.of_isClosedSubgraph_of_mem (h i) hxi).edge_mem⟩

-- /-- A nonempty union of spanning subgraphs of `G` is a spanning subgraph of `G`. -/
-- lemma iUnion_isSpanningSubgraph [Nonempty ι] (h : ∀ i, H i ≤s G) :
--     Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤s G where
--   le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
--   vertexSet_eq := by simp [(h _).vertexSet_eq, iUnion_const]

-- -- A weakening of the previous lemma.
-- lemma iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le [Nonempty ι]
--     (h : ∀ i, H i ≤ G) (hH : ∃ i, H i ≤s G) :
--     Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤s G where
--   le := Graph.iUnion_le_of_forall_le h
--   vertexSet_eq := by
--     apply le_antisymm
--     · simp only [iUnion_vertexSet, le_eq_subset, iUnion_subset_iff]
--       exact fun i ↦ (h i).vertex_subset
--     obtain ⟨i, hi⟩ := hH
--     rw [← hi.vertexSet_eq]
--     exact subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a

-- /-- A nonempty intersection of induced subgraphs `G` is an induced subgraph of `G`-/
-- lemma iInter_isInducedSubgraph [Nonempty ι] (h : ∀ i, H i ≤i G) :
--     Graph.iInter H ≤i G where
--   le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
--   isLink_of_mem_mem := by
--     simp only [iInter_vertexSet, mem_iInter, iInter_isLink]
--     exact fun e x y he hx hy i ↦ (h i).isLink_of_mem_mem he (hx i) (hy i)

-- /-- A nonempty intersection of spanning subgraphs of `G` is a spanning subgraph of `G`.-/
-- lemma iInter_isSpanningSubgraph [Nonempty ι] (h : ∀ i, H i ≤s G) :
--     Graph.iInter H ≤s G where
--   le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
--   vertexSet_eq := iInter_eq_const fun i ↦ (h i).vertexSet_eq

-- /-- A nonempty intersection of closed subgraphs `G` is an induced subgraph of `G`-/
-- lemma iInter_isClosedSubgraph [Nonempty ι] (h : ∀ i, H i ≤c G) :
--     Graph.iInter H ≤c G where
--   le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
--   closed e x he := by
--     simp only [iInter_vertexSet, mem_iInter, iInter_edgeSet, mem_setOf_eq]
--     rintro hx
--     obtain ⟨y, hy⟩ := he
--     use x, y, fun i ↦ by rwa [(h i).isLink_iff_of_mem (hx i)]

-- lemma sUnion_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) :
--     Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤c G :=
--   iUnion_isClosedSubgraph <| by simpa

-- lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤s G) (hne : s.Nonempty) :
--     Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤s G :=
--   have := hne.to_subtype
--   iUnion_isSpanningSubgraph <| by simpa

-- lemma sInter_isInducedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤i G) (hne : s.Nonempty) :
--     Graph.sInter s hne ≤i G :=
--   have := hne.to_subtype
--   iInter_isInducedSubgraph <| by simpa

-- lemma sInter_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) (hne : s.Nonempty) :
--     Graph.sInter s hne ≤c G :=
--   have := hne.to_subtype
--   iInter_isClosedSubgraph <| by simpa

-- lemma isClosedSubgraph_iUnion_of_stronglyDisjoint (h : Pairwise (StronglyDisjoint on H)) (i : ι) :
--     H i ≤c Graph.iUnion H (h.mono fun _ _ ↦ StronglyDisjoint.compatible) where
--   le := Graph.le_iUnion ..
--   closed e x he hx := by
--     obtain ⟨j, hj : (H j).Inc e x⟩ := (iUnion_inc_iff ..).1 he
--     obtain rfl | hne := eq_or_ne i j
--     · exact hj.edge_mem
--     exact False.elim <| (h hne).vertex.notMem_of_mem_left hx hj.vertex_mem

-- lemma isClosedSubgraph_sUnion_of_stronglyDisjoint (s : Set (Graph α β))
--     (hs : s.Pairwise StronglyDisjoint) (hG : G ∈ s) : G ≤c Graph.sUnion s (hs.mono' (by simp)) :=
--   isClosedSubgraph_iUnion_of_stronglyDisjoint ((pairwise_subtype_iff_pairwise_set ..).2 hs) ⟨G, hG⟩

-- lemma isClosedSubgraph_union_left_of_vertexSet_disjoint (h : Disjoint V(H₁) V(H₂)) :
--     H₁ ≤c H₁ ∪ H₂ := by
--   refine ⟨Graph.left_le_union H₁ H₂, fun e x hinc hx₁ => ?_⟩
--   have hninc : ¬ H₂.Inc e x := fun hinc ↦ h.notMem_of_mem_left hx₁ hinc.vertex_mem
--   simp only [union_inc_iff, hninc, false_and, or_false] at hinc
--   exact hinc.edge_mem

-- lemma Disjoint.isClosedSubgraph_union_left (h : Disjoint H₁ H₂) : H₁ ≤c H₁ ∪ H₂ :=
--   isClosedSubgraph_union_left_of_vertexSet_disjoint <| Disjoint.vertex_disjoint h

-- lemma StronglyDisjoint.isClosedSubgraph_union_left (h : StronglyDisjoint H₁ H₂) :
--     H₁ ≤c H₁ ∪ H₂ := by
--   rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
--   exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

-- lemma StronglyDisjoint.isClosedSubgraph_union_right (h : StronglyDisjoint H₁ H₂) :
--     H₂ ≤c H₁ ∪ H₂ := by
--   rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
--   exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

-- lemma IsClosedSubgraph.union (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∪ H₂ ≤c G := by
--   rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
--   exact iUnion_isClosedSubgraph <| by simp [h₁,h₂]

-- lemma IsSpanningSubgraph.union (h₁ : H₁ ≤s G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
--   exact iUnion_isSpanningSubgraph <| by simp [h₁,h₂]

-- lemma IsSpanningSubgraph.union_left (h₁ : H₁ ≤s G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁.le h₂).union_eq_iUnion]
--   exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁.le, h₂])
--     ⟨True, h₁⟩

-- lemma IsSpanningSubgraph.union_right (h₁ : H₁ ≤ G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
--   rw [(compatible_of_le_le h₁ h₂.le).union_eq_iUnion]
--   exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁, h₂.le])
--     ⟨False, h₂⟩

-- lemma IsInducedSubgraph.inter (h₁ : H₁ ≤i G) (h₂ : H₂ ≤i G) : H₁ ∩ H₂ ≤i G := by
--   rw [inter_eq_iInter]
--   exact iInter_isInducedSubgraph <| by simp [h₁,h₂]

-- lemma IsClosedSubgraph.inter (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∩ H₂ ≤c G := by
--   rw [inter_eq_iInter]
--   exact iInter_isClosedSubgraph <| by simp [h₁,h₂]

-- lemma IsClosedSubgraph.inter_le {K G H : Graph α β} (hKG : K ≤c G) (hle : H ≤ G) : K ∩ H ≤c H where
--   le := Graph.inter_le_right
--   closed e x hex hx := by
--     rw [inter_vertexSet] at hx
--     have heK := ((hex.of_le hle).of_isClosedSubgraph_of_mem hKG hx.1).edge_mem
--     rw [(compatible_of_le_le hKG.le hle).inter_edgeSet]
--     exact ⟨heK, hex.edge_mem⟩

-- @[simp]
-- lemma le_bot_iff : G ≤ ⊥ ↔ G = ⊥ := _root_.le_bot_iff

-- @[simp]
-- lemma isClosedSubgraph_bot_iff : G ≤c ⊥ ↔ G = ⊥ :=
--   ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isClosedSubgraph ⊥⟩

-- @[simp]
-- lemma isSpanningSubgraph_bot_iff : G ≤s ⊥ ↔ G = ⊥ :=
--   ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ ⟨le_rfl, rfl⟩⟩

-- @[simp]
-- lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
--   ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isInducedSubgraph ⊥⟩

-- @[simp]
-- lemma induce_empty : G[∅] = ⊥ := by
--   rw [← vertexSet_eq_empty_iff, induce_vertexSet]

-- end Subgraph

-- /-! ### Adding one edge -/

-- @[simp]
-- lemma singleEdge_compatible_iff :
--     Compatible (Graph.singleEdge u v e) G ↔ (e ∈ E(G) → G.IsLink e u v) := by
--   refine ⟨fun h he ↦ by simp [← h ⟨by simp, he⟩], fun h f ⟨hfe, hf⟩ ↦ ?_⟩
--   obtain rfl : f = e := by simpa using hfe
--   ext x y
--   simp only [singleEdge_isLink, (h hf).isLink_iff]
--   tauto

-- /-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
-- its ends change to `a` and `b`. -/
-- @[simps! edgeSet vertexSet]
-- protected def addEdge (G : Graph α β) (e : β) (a b : α) : Graph α β :=
--   Graph.singleEdge a b e ∪ G

-- lemma addEdge_isLink (G : Graph α β) (e : β) (a b : α) : (G.addEdge e a b).IsLink e a b := by
--   simp [Graph.addEdge, union_isLink_iff]

-- lemma addEdge_isLink_of_ne (hf : G.IsLink f x y) (hne : f ≠ e) (a b : α) :
--     (G.addEdge e a b).IsLink f x y := by
--   simpa [Graph.addEdge, union_isLink_iff, hne]

-- lemma addEdge_isLink_iff {a b : α} (he : e ∉ E(G)) :
--     (G.addEdge e a b).IsLink f x y ↔ (f = e ∧ s(a,b) = s(x,y)) ∨ G.IsLink f x y := by
--   have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
--   simp only [Graph.addEdge, union_isLink_iff, singleEdge_isLink, singleEdge_edgeSet,
--     mem_singleton_iff, edgeDelete_isLink, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
--   obtain rfl | hne := eq_or_ne e f
--   · have hl : ¬ G.IsLink e x y := fun h ↦ he h.edge_mem
--     simp only [true_and, not_true_eq_false, hl, and_self, or_false]
--     tauto
--   simp [hne.symm]

-- lemma addEdge_deleteEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
--     (G.addEdge e x y) ＼ {e} = G := by
--   have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
--   simp only [Graph.addEdge, Graph.ext_iff, edgeDelete_vertexSet, union_vertexSet,
--     singleEdge_vertexSet, union_eq_right, insert_subset_iff, hx, singleton_subset_iff, hy, and_self,
--     edgeDelete_isLink, hc.union_isLink_iff, singleEdge_isLink, mem_singleton_iff, true_and]
--   intro f p q
--   obtain rfl | hne := eq_or_ne f e
--   · suffices ¬ G.IsLink f p q by simpa
--     exact fun hf ↦ he hf.edge_mem
--   simp [hne]

-- lemma addEdge_le (hle : H ≤ G) (he : G.IsLink e x y) : H.addEdge e x y ≤ G :=
--   Graph.union_le (by simpa) hle

-- lemma le_addEdge (he : e ∉ E(G)) : G ≤ G.addEdge e x y :=
--   Compatible.right_le_union <| by simp [he]

-- lemma addEdge_mono (hle : H ≤ G) : H.addEdge e x y ≤ G.addEdge e x y :=
--   union_mono_right hle

-- lemma deleteEdge_le_addEdge : G ＼ {e} ≤ G.addEdge e x y := by
--   rw [Graph.addEdge, union_eq_union_edgeDelete]
--   simp only [singleEdge_edgeSet]
--   exact Compatible.right_le_union <| by simp

-- lemma deleteEdge_addEdge : (G ＼ {e}).addEdge e x y = G.addEdge e x y := by
--   refine le_antisymm (addEdge_mono edgeDelete_le) ?_
--   unfold Graph.addEdge
--   rw [union_le_iff]
--   refine ⟨Graph.left_le_union (Graph.singleEdge x y e) (G ＼ {e}), Compatible.right_le_union ?_⟩
--   simp

-- lemma addEdge_eq_self (hbtw : G.IsLink e x y) : G.addEdge e x y = G :=
--   le_antisymm (addEdge_le (by simp) hbtw) <| Compatible.right_le_union <| by simp [hbtw]

-- lemma addEdge_idem : (G.addEdge e x y).addEdge e x y = G.addEdge e x y :=
--   addEdge_eq_self <| addEdge_isLink G e x y

-- lemma isSpanningSubgraph_addEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
--     G ≤s G.addEdge e x y := by
--   nth_rw 1 [← addEdge_deleteEdge he hx hy]
--   exact edgeDelete_isSpanningSubgraph

-- lemma IsLink.deleteEdge_addEdge (h : G.IsLink e x y) : (G ＼ {e}).addEdge e x y = G :=
--   ext_of_le_le (addEdge_le (by simp) h) le_rfl (by simp [pair_subset_iff, h.left_mem, h.right_mem])
--     <| by simp [h.edge_mem]
