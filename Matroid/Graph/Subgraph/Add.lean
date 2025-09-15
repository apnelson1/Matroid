import Matroid.Graph.Subgraph.Union
import Matroid.Graph.Constructions.Basic

variable {α β ι ι' : Type*} {a b c x y z u v w : Set α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set (Set α)} {s t : Set (Graph α β)} {P Q : Partition (Set α)}

open Set Function

namespace Graph


/-! ### Adding one edge -/

-- @[simp]
-- lemma singleEdge_compatible_iff : Compatible (Graph.singleEdge u v e) G ↔
--     (e ∈ E(G) → G.IsLink e u v ∧ ({{u}, {v}} : Set (Set α)) ⊆ V(G)) := by
--   rw [pair_subset_iff]
--   refine ⟨fun h he ↦ ?_, fun h f a b ⟨hfe, hf⟩ ↦ ?_⟩
--   · simp only [← h ⟨by simp, he⟩, singleEdge_isLink, and_self, true_or, IsLink.symm, true_and]

--     sorry
--   obtain rfl : f = e := by simpa using hfe
--   obtain ⟨hfuv, hu, hv⟩ := h hf
--   simp only [singleEdge_isLink, true_and]
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
--     · exact hfuv
--     · exact symm hfuv
--   obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := h.isLink_iff_dup_and_dup_or_dup_and_dup.mp hfuv
--   · obtain rfl : a = u := sorry
--     obtain rfl : b = v := sorry
--     simp
--   · obtain rfl : a = v := sorry
--     obtain rfl : b = u := sorry
--     simp

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
protected def addEdge (G : Graph α β) (e : β) (a b : Set α) (ha : a ∈ V(G)) (hb : b ∈ V(G)) :
    Graph α β := Graph.singleEdge e a b () ∪ G

@[simp]
lemma addEdge_labelSet (ha : a ≠ ∅) (hb : b ≠ ∅) (hab : Disjoint a b):
    V(G.addEdge e a b ha hb hab) = {a, b} ∪ V(G) := by
  simp [Graph.addEdge]

@[simp]
lemma left_mem_addEdge_labelSet : a ∈ L(G.addEdge e a b) := by
  simp

@[simp]
lemma right_mem_addEdge_labelSet : b ∈ L(G.addEdge e a b) := by
  simp

@[simp]
lemma addEdge_vertexSet : V(G.addEdge e a b) = V(Graph.singleEdge a b e) ⊔ V(G) := by
  simp [Graph.addEdge]

@[simp↓]
lemma addEdge_vertexSet_of_mem (ha : a ∈ L(G)) (hb : b ∈ L(G)) : V(G.addEdge e a b) = V(G) := by
  simp [addEdge_vertexSet, pair_subset_iff, ha, hb]

@[simp]
lemma addEdge_dup : V(G.addEdge e a b) x y ↔ (x = y ∧ (x = a ∨ x = b)) ∨ V(G) x y := by
  simp only [Graph.addEdge, union_vertexSet, singleEdge_vertexSet, Partition.sup_rel,
    Partition.rel_discrete_eq, mem_insert_iff, mem_singleton_iff]
  have : IsTrans α ((fun a_1 b_1 ↦ a_1 = b_1 ∧ (a_1 = a ∨ a_1 = b)) ⊔ ⇑V(G)) := ⟨by
    rintro a b c (⟨rfl, hor⟩ | h) (⟨rfl, hor⟩ | h')
    on_goal 4 => simp [h.trans h']
    all_goals simp_all⟩
  rw [Relation.transClosure_eq_self]
  rfl

lemma subset_addEdge_vertexSet : V(G) ⊆ V(G.addEdge e a b) := by
  rw [Partition.subset_iff_rel]
  rintro x y hx
  rw [addEdge_dup]
  simp only [iff_or_self, and_imp]
  rintro rfl (rfl | rfl) <;> exact Partition.rel_self_of_mem_supp hx

lemma addEdge_isLink_of_edge (G : Graph α β) (e : β) (a b : α) :
    (G.addEdge e a b).IsLink e a b := by
  rw [Graph.addEdge]
  exact IsLink.le_union_left isLink_singleEdge

lemma IsLink.addEdge_of_ne (hf : G.IsLink f x y) (hne : f ≠ e) (a b : α) :
    (G.addEdge e a b).IsLink f x y := by
  rw [Graph.addEdge]
  exact hf.le_union_right_of_not_mem hne

-- You probably want addEdge_isLink_of_ne instead. So much so that it is not a simp lemma.
lemma addEdge_isLink : (G.addEdge e a b).IsLink f x y ↔ Relation.Domp V(G.addEdge e a b)
    ((Graph.singleEdge a b e).IsLink f) x y ∨ G.IsLink f x y ∧ f ≠ e := by
  conv_lhs => rw [Graph.addEdge, union_isLink]
  change Relation.Domp V(G.addEdge e a b) (fun x y ↦ (Graph.singleEdge a b e).IsLink f x y ∨
    G.IsLink f x y ∧ f ≠ e) x y ↔ _
  rw [Relation.domp_or, or_congr_right]
  refine ⟨fun ⟨hl, hne⟩ => ?_, fun ⟨a, ha, b, ⟨hlba, hne⟩, hb⟩ => ⟨?_, hne⟩⟩
  · refine ⟨x, Partition.rel_self_of_mem_supp ?_, y, ⟨hl.symm, hne⟩,
      Partition.rel_self_of_mem_supp ?_⟩ <;> simp [hl.left_mem, hl.right_mem]
  obtain ⟨rfl, hor⟩ | h1 := addEdge_dup.mp ha <;> obtain ⟨rfl, hor⟩ | h2 := addEdge_dup.mp hb
  · exact hlba.symm
  · exact trans' hlba.symm h2
  · exact trans' h1 hlba.symm
  · exact trans' (trans' h1 hlba.symm) h2

lemma addEdge_isLink_of_not_mem (he : e ∉ E(G)) : (G.addEdge e a b).IsLink f x y ↔
    Relation.Domp V(G.addEdge e a b) ((Graph.singleEdge a b e).IsLink f) x y ∨ G.IsLink f x y := by
  rw [addEdge_isLink, or_congr_right]
  rw [and_iff_left_iff_imp]
  rintro hf rfl
  exact he hf.edge_mem

@[simp]
lemma addEdge_isLink_of_ne (hne : f ≠ e) : (G.addEdge e a b).IsLink f x y ↔ G.IsLink f x y := by
  simp +contextual only [addEdge_isLink, ne_eq, hne, not_false_eq_true, and_true, iff_def,
    IsLink.symm, or_true, implies_true, or_imp]
  rintro ⟨_, _, _, ⟨rfl, _⟩, _⟩
  simp at hne

lemma addEdge_isLink_of_edge_iff : (G.addEdge e a b).IsLink e x y ↔
    (a = x ∨ V(G) a x) ∧ (b = y ∨ V(G) b y) ∨ (a = y ∨ V(G) a y) ∧ (b = x ∨ V(G) b x) := by
  simp only [addEdge_isLink, ne_eq, not_true_eq_false, and_false, or_false]
  refine ⟨fun ⟨u, hxu, v, h, hvy⟩ => ?_, fun h => ?_⟩
  · simp only [Relation.flip_apply, singleEdge_isLink, true_and] at h
    rw [addEdge_dup] at hxu hvy
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> obtain ⟨rfl, hor⟩ | h1 := hxu <;>
      obtain ⟨rfl, hor⟩ | h2 := hvy <;> simp_all [symm_of V(G)]
  · obtain ⟨(rfl | hax), (rfl | hby)⟩ | h := h; rotate_right
    · obtain ⟨(rfl | hay), (rfl | hbx)⟩ := h <;> use b, ?_, a, isLink_singleEdge <;>
      (try refine Partition.rel_self_of_mem_supp <| by simp) <;>
      exact V(G).rel_le_of_subset subset_addEdge_vertexSet _ _ <| by simp_all only [symm_of V(G)]
    all_goals use a, ?_, b, isLink_singleEdge.symm <;>
      (try refine Partition.rel_self_of_mem_supp <| by simp) <;>
      exact V(G).rel_le_of_subset subset_addEdge_vertexSet _ _ <| by simp_all only [symm_of V(G)]

@[simp]
lemma addEdge_isLink_of_edge_iff_of_mem (ha : a ∈ L(G)) (hb : b ∈ L(G)) :
    (G.addEdge e a b).IsLink e x y ↔ V(G) a x ∧ V(G) b y ∨ V(G) a y ∧ V(G) b x := by
  rw [addEdge_isLink_of_edge_iff, or_congr] <;> rw [and_congr] <;> rw [or_iff_right_iff_imp] <;>
    rintro rfl <;> exact V(G).rel_self_of_mem_supp (by assumption)

-- This seems useful but not yet in mathlib?
lemma assume_common_imp_of_iff {P1 P2 : Prop} (Q : Prop) (h1 : P1 → Q) (h2 : P2 → Q) :
    (P1 ↔ P2) ↔ (Q → (P1 ↔ P2)) := by
  tauto

lemma addEdge_deleteEdge (he : e ∉ E(G)) (ha : a ∈ L(G)) (hb : b ∈ L(G)) :
    (G.addEdge e a b) ＼ {e} = G :=
  Graph.ext (by simp [ha, hb]) fun f x y => by
  have h : G.IsLink f x y → f ≠ e := by
    rintro hl rfl
    exact he hl.edge_mem
  rw [edgeDelete_isLink, assume_common_imp_of_iff (f ≠ e) (fun h ↦ h.2) h]
  simp +contextual

-- still not true
-- lemma addEdge_isLabelSubgraph (hle : H ≤l G) (he : G.IsLink e a b) : H.addEdge e a b ≤l G where
--   vertexSet_isInducedSubpartition := by
--     simp [Partition.isInducedSubpartition]
--     ext x y

--   isLink_of_isLink f x y hl := by
--     rw [addEdge_isLink]
--     simp [hle.isLink_of_isLink hl]

lemma le_addEdge (he : e ∉ E(G)) : G ≤ G.addEdge e a b where
  vertexSet_subset := subset_addEdge_vertexSet
  isLink_of_isLink f x y hl := by
    have hne : f ≠ e := by
      rintro rfl
      exact he hl.edge_mem
    rw [addEdge_isLink_of_ne hne]
    exact hl

lemma addEdge_mono_of_mem (hle : H ≤ G) (ha : a ∈ L(H)) (hb : b ∈ L(H)) :
    H.addEdge e a b ≤ G.addEdge e a b where
  vertexSet_subset := by
    rw [Partition.subset_iff_rel]
    rintro x y hx
    simp only [ha, hb, ↓addEdge_vertexSet_of_mem] at hx
    simp only [addEdge_dup, dup_iff_dup_of_le hle hx]
  isLink_of_isLink f x y hl := by
    by_cases hne : f = e
    · subst f
      simp only [ha, hb, addEdge_isLink_of_edge_iff_of_mem] at hl
      simp only [labelSet_mono hle ha, labelSet_mono hle hb, addEdge_isLink_of_edge_iff_of_mem]
      apply hl.imp <;> refine fun ⟨h1, h2⟩ => ⟨?_, ?_⟩ <;> apply (dup_iff_dup_of_le hle _).mpr <;>
        assumption
    rw [addEdge_isLink_of_ne hne] at hl ⊢
    exact hl.of_le hle

lemma deleteEdge_le_addEdge : G ＼ {e} ≤ G.addEdge e x y := by
  rw [Graph.addEdge, union_eq_union_edgeDelete, singleEdge_edgeSet]
  apply le_addEdge
  simp

lemma deleteEdge_addEdge : (G ＼ {e}).addEdge e a b = G.addEdge e a b :=
  Graph.ext (by simp) fun f x y => by simp [addEdge_isLink]

lemma addEdge_eq_self (hbtw : G.IsLink e a b) : G.addEdge e a b = G :=
  Graph.ext (by simp [hbtw.left_mem, hbtw.right_mem]) fun f x y => by
    by_cases hne : f = e
    · subst f
      simp [hbtw.left_mem, hbtw.right_mem, hbtw.isLink_iff_dup_and_dup_or_dup_and_dup]
    simp [hne]

lemma addEdge_idem : (G.addEdge e x y).addEdge e x y = G.addEdge e x y :=
  addEdge_eq_self <| addEdge_isLink_of_edge G e x y

lemma isSpanningSubgraph_addEdge (he : e ∉ E(G)) (ha : a ∈ L(G)) (hb : b ∈ L(G)) :
    G ≤s G.addEdge e a b := by
  nth_rw 1 [← addEdge_deleteEdge he ha hb]
  exact edgeDelete_isSpanningSubgraph

lemma IsLink.deleteEdge_addEdge (h : G.IsLink e a b) : (G ＼ {e}).addEdge e a b = G :=
  Graph.ext (by simp [h.left_mem, h.right_mem]) fun f x y => by
    by_cases hne : f = e
    · subst f
      simp [h.left_mem, h.right_mem, h.isLink_iff_dup_and_dup_or_dup_and_dup]
    simp [hne]

end Graph
