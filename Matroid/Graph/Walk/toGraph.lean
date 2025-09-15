import Matroid.Graph.Walk.Basic
import Matroid.Graph.Subgraph.Union

variable {α β ι ι' : Type*} {x y z u v : Set α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set (Set α)} {s t : Set (Graph α β)} {W w : WList (Set α) β}

open scoped Sym2 Graph
open WList Set Function

namespace Graph

lemma IsWalk.isWalk_left_of_subset (hw : (G ∪ H).IsWalk w) (hG : G.Dup_agree H) (hE : E(w) ⊆ E(G))
    (h1 : w.first ∈ V(G)) : G.IsWalk w := by
  induction hw with
  | nil => simp_all
  | @cons x e w hw h ih =>
    simp_all only [union_isLink hG, cons_edgeSet, insert_subset_iff, first_cons, cons_isWalk_iff,
      not_true_eq_false, and_false, or_false, forall_const, true_and]
    exact ih h.right_mem

lemma IsWalk.isWalk_left_of_subset_of_nonempty (hw : (G ∪ H).IsWalk w) (hG : G.Dup_agree H)
    (hE : E(w) ⊆ E(G)) (hne : w.Nonempty) : G.IsWalk w := by
  by_cases h1 : w.first ∈ V(G)
  · exact hw.isWalk_left_of_subset hG hE h1
  cases w with
  | nil => simp_all
  | cons u e w =>
  simp only [cons_edgeSet, insert_subset_iff] at hE
  simp only [cons_isWalk_iff, union_isLink hG, hE.1, not_true_eq_false, and_false, or_false] at hw
  rw [first_cons] at h1
  exact (h1 hw.1.left_mem).elim

end Graph

namespace WList

/-- Turn `w : WList (Set α) β` into a `Graph α β`. If the list is not well-formed
(i.e. it contains an edge appearing twice with different ends),
then the first occurence of the edge determines its ends in `w.toGraph`. -/
protected def toGraph : ∀ (w : WList (Set α) β), ∅ ∉ V(w) → Graph α β
  | nil u, h => Graph.noEdge (Partition.indiscrete u (by rintro rfl; simp at h)) β
  | cons u e w, h => w.toGraph (by simp_all) ∪ (Graph.singleEdge e u w.first
    (by rintro rfl; simp at h) sorry sorry)

@[simp]
lemma toGraph_nil : (WList.nil u (β := β)).toGraph = Graph.noEdge {u} β := rfl

lemma toGraph_cons : (w.cons u e).toGraph = w.toGraph ∪ (Graph.singleEdge u w.first e) := rfl

lemma toGraph_concat (w : WList α β) (e u) :
    (w.concat e u).toGraph = (Graph.singleEdge u w.last e) ∪ w.toGraph := by
  induction w with
  | nil v =>
    refine Graph.ext (by simp [toGraph_cons, pair_comm]) fun f x y ↦ ?_
    simp only [nil_concat, toGraph_cons, toGraph_nil, nil_first, union_isLink_iff, noEdge_isLink,
      noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true, singleEdge_isLink, true_and, false_or,
      singleEdge_edgeSet, mem_singleton_iff, and_false, or_false, and_congr_right_iff]
    tauto
  | cons v f w ih =>
    ext a x y
    · simp only [cons_concat, toGraph_cons, ih, concat_first, union_vertexSet, singleEdge_vertexSet,
      union_insert, union_singleton, mem_union, mem_insert_iff, mem_singleton_iff, or_true, true_or,
      insert_eq_of_mem, first_cons]
      tauto
    simp only [cons_concat, toGraph_cons, ih, concat_first, union_isLink_iff, singleEdge_isLink,
      singleEdge_edgeSet, mem_singleton_iff, union_edgeSet, singleton_union, mem_insert_iff, not_or,
      first_cons]
    tauto

@[simp]
lemma toGraph_vertexSet (w : WList α β) : V(w.toGraph) = V(w) := by
  induction w with simp_all [toGraph_cons]

@[simp]
lemma toGraph_edgeSet (w : WList α β) : E(w.toGraph) = E(w) := by
  induction w with simp_all [toGraph_cons]

lemma toGraph_vertexSet_nonempty (w : WList α β) : V(w.toGraph).Nonempty := by
  simp

lemma WellFormed.toGraph_isLink (h : w.WellFormed) : w.toGraph.IsLink = w.IsLink := by
  ext e x y
  induction w with
  | nil => simp
  | cons u f w ih =>
    rw [cons_wellFormed_iff] at h
    rw [toGraph_cons, union_isLink_iff, isLink_cons_iff, ih h.1, toGraph_edgeSet, mem_edgeSet_iff,
      singleEdge_isLink_iff, eq_comm (a := e), iff_def, or_imp, and_iff_right (by tauto), or_imp,
      and_iff_left (by tauto)]
    rintro ⟨rfl, h_eq⟩
    rw [and_iff_right rfl, and_iff_right h_eq, ← imp_iff_or_not]
    intro hf
    obtain ⟨y₁, y₂, hinc⟩ := exists_isLink_of_mem_edge hf
    rw [← h.2 y₁ y₂ hinc] at h_eq
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Sym2.eq_iff.1 h_eq
    · assumption
    exact hinc.symm

lemma IsSublist.toGraph_le (h : w₁.IsSublist w₂) (hw₂ : w₂.WellFormed) :
    w₁.toGraph ≤ w₂.toGraph where
  vertex_subset := by
    refine fun x hx ↦ ?_
    simp only [toGraph_vertexSet, mem_vertexSet_iff] at hx ⊢
    exact h.mem hx
  isLink_of_isLink e x y h' := by
    rw [hw₂.toGraph_isLink]
    rw [(hw₂.sublist h).toGraph_isLink] at h'
    exact h'.of_isSublist h

lemma WellFormed.reverse_toGraph (h : w.WellFormed) : w.reverse.toGraph = w.toGraph :=
    Graph.ext (by simp) fun e x y ↦ by
    rw [h.toGraph_isLink, h.reverse.toGraph_isLink, isLink_reverse_iff]

lemma WellFormed.isWalk_toGraph (hw : w.WellFormed) : w.toGraph.IsWalk w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    rw [cons_wellFormed_iff] at hw
    refine ((ih hw.1).of_le (by simp [toGraph_cons])).cons ?_
    suffices w.toGraph.IsLink e u w.first ∨ e ∉ w.edge by simpa [toGraph_cons, union_isLink_iff]
    rw [← imp_iff_or_not]
    intro he
    obtain ⟨y₁, y₂, h⟩ := exists_isLink_of_mem_edge he
    rw [((ih hw.1).isLink_of_isLink h).isLink_iff_sym2_eq, hw.2 _ _ h]

end WList

namespace Graph

lemma IsWalk.toGraph_le (h : G.IsWalk w) : w.toGraph ≤ G := by
  induction w with
  | nil u => simpa [WList.toGraph] using h
  | cons u e W ih =>
    simp only [cons_isWalk_iff] at h
    exact Graph.union_le (ih h.2) (by simpa using h.1)

lemma _root_.WList.WellFormed.toGraph_le_iff (hW : W.WellFormed) : W.toGraph ≤ G ↔ G.IsWalk W := by
  refine ⟨fun hle ↦ ?_, IsWalk.toGraph_le⟩
  induction W with
  | nil => simpa using hle
  | cons u e W IH =>
    simp_all only [cons_isWalk_iff]
    rw [cons_wellFormed_iff] at hW
    rw [toGraph_cons, Compatible.union_le_iff] at hle
    · simp only [singleEdge_le_iff] at hle
      refine ⟨hle.2, IH hW.1 hle.1⟩
    rw [compatible_comm, singleEdge_compatible_iff, toGraph_edgeSet, mem_edgeSet_iff]
    intro he
    obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edge he
    have := hW.2 _ _ hexy
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := this
    · rwa [hW.1.toGraph_isLink]
    rw [hW.1.toGraph_isLink]
    exact hexy.symm

lemma IsWalk.edgeSet_subset_induce_edgeSet (hw : G.IsWalk w) : E(w) ⊆ E(G[V(w)]) := by
  intro e hew
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edge hew
  rw [(hw.isLink_of_isLink h).mem_induce_iff]
  exact ⟨h.left_mem, h.right_mem⟩

lemma IsWalk.toGraph_eq_induce_restrict (h : G.IsWalk w) : w.toGraph = G[V(w)] ↾ E(w) := by
  induction w with
  | nil => ext <;> simp
  | cons u e w ih =>
    have hss' := h.edgeSet_subset_induce_edgeSet
    simp_all only [cons_isWalk_iff, cons_vertexSet, cons_edgeSet, forall_const]
    rw [toGraph_cons, ih]
    refine G.ext_of_le_le (Graph.union_le ?_ ?_) ?_ (by simp) ?_
    · exact (edgeRestrict_le ..).trans (induce_le h.2.vertexSet_subset)
    · simpa using h.1
    · refine (edgeRestrict_le ..).trans (induce_le ?_)
      simp [insert_subset_iff, h.1.left_mem, h.2.vertexSet_subset]
    simp only [union_edgeSet, edgeRestrict_edgeSet, singleEdge_edgeSet, union_singleton]
    rw [inter_eq_self_of_subset_left h.2.edgeSet_subset_induce_edgeSet,
      inter_eq_self_of_subset_left hss']

lemma IsWalk.le_of_edgeSet_subset (hw₁ : G.IsWalk w₁) (hne : w₁.Nonempty) (hw₂ : G.IsWalk w₂)
    (hss : E(w₁) ⊆ E(w₂)) : w₁.toGraph ≤ w₂.toGraph := by
  have h₁ := hw₁.toGraph_le
  have h₂ := hw₂.toGraph_le
  refine G.le_of_le_le_subset_subset h₁ h₂ (fun x hxV ↦ ?_) (by simpa using hss)
  rw [toGraph_vertexSet, mem_vertexSet_iff, hne.mem_iff_exists_isLink] at hxV
  obtain ⟨y, e, h⟩ := hxV
  have hew₂ := hss h.edge_mem
  rw [hw₁.isLink_iff_isLink_of_mem h.edge_mem, ← hw₂.isLink_iff_isLink_of_mem hew₂] at h
  simpa using h.left_mem

end Graph
