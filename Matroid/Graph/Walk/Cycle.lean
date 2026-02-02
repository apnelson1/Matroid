import Matroid.Graph.Walk.Path
import Matroid.Graph.WList.Cycle

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ C C₁ C₂ : WList α β} {S T : Set α}

open Set WList

lemma WList.WellFormed.rotate_toGraph (hw : w.WellFormed) (h_closed : w.IsClosed) (n : ℕ) :
    (w.rotate n).toGraph = w.toGraph := by
  refine Graph.ext (by simp [h_closed.rotate_vertexSet]) fun e x y ↦ ?_
  rw [(hw.rotate h_closed n).toGraph_isLink, h_closed.isLink_rotate_iff, hw.toGraph_isLink]

namespace Graph

lemma IsWalk.rotate (hw : G.IsWalk w) (hc : w.IsClosed) (n) : G.IsWalk (w.rotate n) := by
  have aux {w'} (hw' : G.IsWalk w') (hc' : w'.IsClosed) : G.IsWalk (w'.rotate 1) := by
    induction hw' with
    | nil => simpa
    | @cons x e w hw h ih =>
      simp only [rotate_cons_succ, rotate_zero]
      obtain rfl : x = w.last := by simpa using hc'
      exact hw.concat h
  induction n with
  | zero => simpa
  | succ n IH => simpa [← rotate_rotate] using aux IH (hc.rotate n)

lemma IsWalk.intRotate (hw : G.IsWalk w) (hc : w.IsClosed) (n) : G.IsWalk (w.intRotate n) :=
  hw.rotate hc _

@[simp]
lemma IsClosed.isWalk_rotate_iff (hc : w.IsClosed) {n} : G.IsWalk (w.rotate n) ↔ G.IsWalk w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.rotate hc _⟩
  have h' := h.intRotate (hc.rotate _) (-n)
  rwa [← hc.intRotate_eq_rotate, hc.intRotate_intRotate, add_neg_cancel, intRotate_zero] at h'


/-- `G.IsTour C` means that `C` is a nonempty closed walk with no repeated edges
(but possibly repeated vertices). -/
@[mk_iff]
structure IsTour (G : Graph α β) (C : WList α β) : Prop extends G.IsTrail C where
  nonempty : C.Nonempty
  /-- The start and end vertex are the same -/
  isClosed : C.IsClosed

/-- `G.IsCyclicWalk C` means that `C` is a nonempty closed walk with no repeated vertices or
edges. -/
@[mk_iff]
structure IsCyclicWalk (G : Graph α β) (C : WList α β) : Prop extends G.IsTour C where
  /-- There are no repeated vertices except for the first and last. -/
  nodup : C.tail.vertex.Nodup

/-- If `C` has at least three edges, then the assumption that `C` has distinct edges follows
from its distinct vertices, so is not needed. -/
lemma IsWalk.isCyclicWalk_of_closed_nodup (hC : G.IsWalk C) (hlen : 2 < C.length)
    (h_closed : C.IsClosed) (nodup : C.tail.vertex.Nodup) : G.IsCyclicWalk C where
  isWalk := hC
  edge_nodup := by
    cases C with | nil  => simp | cons u e W =>
    simp only [cons_edge, List.nodup_cons]
    simp only [cons_isWalk_iff] at hC
    simp only [tail_cons] at nodup
    obtain rfl : u = W.last := h_closed
    refine ⟨fun heW ↦ ?_, IsTrail.edge_nodup (G := G) (IsPath.isTrail ⟨hC.2, nodup⟩)⟩
    cases W with | nil => simp at hlen | cons v f W =>
    simp only [cons_vertex, List.nodup_cons, mem_vertex] at nodup
    have hne : W.first ≠ W.last := by simpa [← first_ne_last_iff nodup.2] using hlen
    simp only [last_cons, first_cons, cons_isWalk_iff] at hC
    obtain (rfl : e = f) | (heW : e ∈ W.edge) := by simpa using heW
    · exact hne <| hC.2.1.right_unique hC.1.symm
    exact nodup.1 <| hC.2.2.vertex_mem_of_edge_mem heW hC.1.inc_right
  nonempty := by cases C with simp_all
  isClosed := h_closed
  nodup := nodup

lemma IsTour.isTrail (hC : G.IsTour C) : G.IsTrail C where
  isWalk := hC.isWalk
  edge_nodup := hC.edge_nodup

@[simp]
lemma not_isTour_nil (x : α) : ¬ G.IsTour (nil x : WList α β) :=
  fun h ↦ by simpa using h.nonempty

lemma IsTour.rotate (hC : G.IsTour C) (n : ℕ) : G.IsTour (C.rotate n) where
  nonempty := by simpa using hC.nonempty
  isWalk := hC.isWalk.rotate hC.isClosed n
  edge_nodup := by simpa using hC.edge_nodup
  isClosed := hC.isClosed.rotate n

lemma IsTour.intRotate (hC : G.IsTour C) (n : ℤ) : G.IsTour (C.intRotate n) :=
  hC.rotate ..

lemma IsTour.reverse (hC : G.IsTour C) : G.IsTour C.reverse where
  isWalk := hC.isWalk.reverse
  edge_nodup := by simpa using hC.edge_nodup
  nonempty := by simp [hC.nonempty]
  isClosed := by simp [hC.isClosed]

lemma IsTour.of_le (hC : H.IsTour C) (hle : H ≤ G) : G.IsTour C where
  isWalk := hC.isWalk.of_le hle
  edge_nodup := hC.edge_nodup
  nonempty := hC.nonempty
  isClosed := hC.isClosed

lemma IsTour.of_le_of_subset (h : G.IsTour w) (hle : H ≤ G) (hE : E(w) ⊆ E(H)) :
    H.IsTour w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE h.nonempty
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed

lemma IsTour.isTour_toGraph (hC : G.IsTour C) : C.toGraph.IsTour C :=
  hC.of_le_of_subset hC.isWalk.toGraph_le <| by simp

lemma IsTour.of_forall_isLink (h : G.IsTour C) (he : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) :
    H.IsTour C where
  isWalk := h.isWalk.of_forall_isLink he h.nonempty
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed

@[simp]
lemma edgeRestrict_isTour_iff (F : Set β) (C : WList α β) :
    (G ↾ F).IsTour C ↔ G.IsTour C ∧ E(C) ⊆ F := by
  refine ⟨fun h ↦ ⟨h.of_le edgeRestrict_le, ?_⟩,
    fun ⟨h, hss⟩ ↦ h.of_le_of_subset (by simp) (by simp [hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma edgeDelete_isTour_iff (F : Set β) (C : WList α β) :
    (G ＼ F).IsTour C ↔ G.IsTour C ∧ Disjoint E(C) F := by
  refine ⟨fun h ↦ ⟨h.of_le edgeDelete_le, ?_⟩, fun ⟨h, hss⟩ ↦
    h.of_le_of_subset (by simp) (by simp [subset_diff, hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa [subset_diff] using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma induce_isTour_iff (X : Set α) (C : WList α β) : (G[X]).IsTour C ↔ G.IsTour C ∧ V(C) ⊆ X := by
  refine ⟨fun h ↦ ⟨?_, h.isWalk.vertexSet_subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩
  · refine ⟨⟨?_, h.edge_nodup⟩, h.nonempty, h.isClosed⟩
    obtain ⟨x, hx, rfl⟩ | ⟨hC, hCX⟩ := by simpa [isWalk_induce_iff] using h.isWalk
    · simpa using h.nonempty
    exact hC
  refine ⟨⟨?_, h.edge_nodup⟩, h.nonempty, h.isClosed⟩
  simp [isWalk_induce_iff, h.isWalk, hss]

@[simp]
lemma vertexDelete_isTour_iff (X : Set α) (C : WList α β) :
    (G - X).IsTour C ↔ G.IsTour C ∧ Disjoint V(C) X := by
  refine ⟨fun h ↦ ⟨⟨⟨?_, h.edge_nodup⟩, h.nonempty, h.isClosed⟩,
    h.isWalk.disjoint_of_vertexDelete⟩, fun ⟨h, hdisj⟩ ↦
    ⟨⟨by simp [h.isWalk, hdisj], h.edge_nodup⟩, h.nonempty, h.isClosed⟩⟩
  have := by simpa using h.isWalk
  exact this.1

/-- Dedup preserves being a trail (walk with distinct edges). -/
lemma IsTrail.dedup [DecidableEq α] (hC : G.IsTrail C) : G.IsTrail C.dedup where
  isWalk := hC.isWalk.dedup
  edge_nodup := hC.edge_nodup.sublist C.dedup_isSublist.edge_sublist

/-- Applying dedup to the tail of a tour gives a cycle. -/
lemma IsTour.dedup_tail_isCyclicWalk [DecidableEq α] (hC : G.IsTour (cons x e w)) :
    G.IsCyclicWalk (cons x e w.dedup) where
  toIsTrail := hC.isTrail.sublist <| w.dedup_isSublist.cons₂ x e (by simp)
  nonempty := by simp
  isClosed := by
    have := hC.isClosed
    simp_all
  nodup := w.dedup_vertex_nodup

/-- Every tour contains a cycle as a sublist. -/
lemma IsTour.exists_isCyclicWalk (hC : G.IsTour C) : ∃ C', G.IsCyclicWalk C' ∧ C'.IsSublist C := by
  classical
  obtain ⟨x, e, w, rfl⟩ := hC.nonempty.exists_cons
  exact ⟨cons x e w.dedup, hC.dedup_tail_isCyclicWalk, w.dedup_isSublist.cons₂ x e <| by simp⟩

lemma IsCyclicWalk.isTour (hC : G.IsCyclicWalk C) : G.IsTour C where
  isWalk := hC.isWalk
  edge_nodup := hC.edge_nodup
  nonempty := hC.nonempty
  isClosed := hC.isClosed

lemma IsCyclicWalk.idxOf_get [DecidableEq α] (hC : G.IsCyclicWalk C) {n} (hn : n < C.length) :
    C.idxOf (C.get n) = n := hC.isClosed.idxOf_get hC.nodup hn

lemma IsCyclicWalk.isTrail (hC : G.IsCyclicWalk C) : G.IsTrail C where
  isWalk := hC.isWalk
  edge_nodup := hC.edge_nodup

lemma IsCyclicWalk.rotate (hC : G.IsCyclicWalk C) (n : ℕ) : G.IsCyclicWalk (C.rotate n) where
  nonempty := by simpa using hC.nonempty
  isWalk := hC.isWalk.rotate hC.isClosed n
  edge_nodup := by simpa using hC.edge_nodup
  isClosed := hC.isClosed.rotate n
  nodup := by simpa [rotate_vertex_tail, List.nodup_rotate] using hC.nodup

@[simp]
lemma not_isCyclicWalk_nil (x : α) : ¬ G.IsCyclicWalk (nil x : WList α β) :=
  fun h ↦ by simpa using h.nonempty

lemma IsTour.edgeRemove {F : Set β} [DecidablePred (· ∈ F)] (hw : G.IsTour w)
    (hF : ∀ e ∈ w.edge, e ∈ F → ∃ x, G.IsLoopAt e x) (hne : ∃ e, e ∈ w.edge ∧ e ∉ F) :
    G.IsTour (w.edgeRemove F) where
  toIsTrail := hw.toIsTrail.edgeRemove hF
  nonempty := by
    rw [nonempty_iff_exists_edge]
    obtain ⟨e, he, heF⟩ := hne
    use e
    simp only [edgeRemove_edge, decide_not, List.mem_filter, he, heF, decide_false, Bool.not_false,
      and_self]
  isClosed := by
    rw [IsClosed, edgeRemove_first hF hw.isWalk, edgeRemove_last]
    exact hw.isClosed

lemma IsCyclicWalk.intRotate (hC : G.IsCyclicWalk C) (n : ℤ) : G.IsCyclicWalk (C.intRotate n) :=
  hC.rotate ..

lemma IsCyclicWalk.tail_isPath (hC : G.IsCyclicWalk C) : G.IsPath C.tail where
  isWalk := hC.isWalk.suffix <| tail_isSuffix C
  nodup := hC.nodup

lemma IsCyclicWalk.dropLast_isPath (hC : G.IsCyclicWalk C) : G.IsPath C.dropLast := by
  have h := (hC.intRotate (-1)).isClosed.rotate_one_dropLast
  rw [← IsClosed.intRotate_eq_rotate, hC.isClosed.intRotate_intRotate] at h
  · simp only [Int.reduceNeg, Int.cast_ofNat_Int, neg_add_cancel, intRotate_zero] at h
    rw [h]
    exact (hC.intRotate (-1)).tail_isPath
  exact (hC.intRotate _).isClosed

lemma IsCyclicWalk.tail_dropLast_isPath (hC : G.IsCyclicWalk C) : G.IsPath C.tail.dropLast :=
  hC.tail_isPath.prefix C.tail.dropLast_isPrefix

lemma IsCyclicWalk.mem_tail_dropLast_of_ne_first (hC : G.IsCyclicWalk C) (hxC : x ∈ C)
    (hx : x ≠ C.first) : x ∈ C.tail.dropLast := by
  rwa [mem_iff_eq_first_or_mem_tail, or_iff_right hx, mem_iff_eq_mem_dropLast_or_eq_last,
    tail_last, ← hC.isClosed, or_iff_left hx] at hxC

lemma IsCyclicWalk.tail_dropLast_vertexSet (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) :
    V(C.tail.dropLast) = V(C) \ {C.first} := by
  cases C with
  | nil => simp at hC
  | cons u e w =>
    simp only [tail_cons, cons_vertexSet, first_cons, Set.mem_singleton_iff, Set.insert_diff_of_mem]
    rw [dropLast_vertexSet_of_nodup (by simpa using hC.tail_isPath.nodup) (by simpa using hnt),
      show u = w.last from hC.isClosed]

lemma IsCyclicWalk.reverse (hC : G.IsCyclicWalk C) : G.IsCyclicWalk C.reverse where
  isWalk := hC.isWalk.reverse
  edge_nodup := by simpa using hC.edge_nodup
  nonempty := by simp [hC.nonempty]
  isClosed := by simp [hC.isClosed]
  nodup := by simp [hC.dropLast_isPath.nodup]

lemma IsCyclicWalk.of_le (hC : H.IsCyclicWalk C) (hle : H ≤ G) : G.IsCyclicWalk C where
  isWalk := hC.isWalk.of_le hle
  edge_nodup := hC.edge_nodup
  nonempty := hC.nonempty
  isClosed := hC.isClosed
  nodup := hC.nodup

lemma IsCyclicWalk.isCycle_of_le (h : G.IsCyclicWalk w) (hle : H ≤ G) (hE : E(w) ⊆ E(H)) :
    H.IsCyclicWalk w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE h.nonempty
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed
  nodup := h.nodup

lemma IsCyclicWalk.eq_loop_of_isLink_self (h : G.IsCyclicWalk C) (hC : C.IsLink e x x) :
    C = cons x e (nil x) := by
  cases C with
  | nil u => simp at hC
  | cons u f w =>
    have hnd : w.vertex.Nodup := by simpa using h.tail_isPath.nodup
    rw [isLink_iff_dInc, or_self, dInc_cons_iff] at hC
    obtain rfl : u = w.last := by simpa using h.isClosed
    obtain ⟨rfl, rfl, hu⟩ | h' := hC
    · cases w with simp_all
    rw [List.nodup_iff_sublist] at hnd
    exact False.elim <| hnd x h'.sublist

lemma IsCyclicWalk.isCyclicWalk_toGraph (hC : G.IsCyclicWalk C) : C.toGraph.IsCyclicWalk C :=
  hC.isCycle_of_le hC.isWalk.toGraph_le <| by simp

lemma IsCyclicWalk.ne_of_isLink (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial)
    (hinc : C.IsLink e x y) : x ≠ y := by
  rintro rfl
  obtain ⟨x, e, rfl⟩ := hC.eq_loop_of_isLink_self hinc
  simp at hnt

lemma IsCyclicWalk.length_eq_one_iff (h : G.IsCyclicWalk C) :
    C.length = 1 ↔ ∃ x e, C = cons x e (nil x) := by
  cases C with
  | nil => simp
  | cons u e w =>
    suffices w.Nil → w = nil u by simpa +contextual [iff_def]
    rw [show u = w.last from h.isClosed]
    exact Nil.eq_nil_last

lemma IsCyclicWalk.length_eq_two_iff (h : G.IsCyclicWalk C) :
    C.length = 2 ↔ ∃ x y e f, x ≠ y ∧ e ≠ f ∧ C = cons x e (cons y f (nil x)) := by
  cases C with
  | nil => simp
  | cons u e' w => cases w with
    | nil => simp
    | cons v e'' w =>
      obtain ⟨⟨he : e' ≠ e'', -⟩, -⟩ := by simpa using h.edge_nodup
      obtain ⟨hvw : v ∉ w, -⟩ := by simpa using h.tail_isPath.nodup
      suffices w.Nil ↔ w = nil w.last by
        simpa [he, show u = w.last from h.isClosed, show w.last ≠ v by rintro rfl; simp_all]
      exact ⟨Nil.eq_nil_last, fun h ↦ by rw [h]; simp⟩

lemma IsCyclicWalk.encard_vxSet (h : G.IsCyclicWalk C) : V(C).encard = C.length := by
  rw [← h.nonempty.cons_tail, cons_length, cons_vertexSet, Set.insert_eq_of_mem,
    encard_vxSet_of_nodup h.nodup, Nat.cast_add, Nat.cast_one]
  rw [h.isClosed.eq, ← tail_last, mem_vertexSet_iff]
  exact last_mem

lemma IsCyclicWalk.loop_or_noloop (h : G.IsCyclicWalk C) :
    (∃ x e, C = cons x e (nil x)) ∨ C.NoLoop := by
  classical
  cases h.nonempty with | cons x e w =>
  obtain ⟨u, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · left
    use x, e
    simp [show x = u from h.isClosed]
  cases hne with | cons y f w =>
  refine Or.inr ⟨?_, h.tail_isPath.noloop⟩
  rintro rfl
  obtain rfl := by simpa using h.isClosed
  simpa using h.nodup

lemma IsCyclicWalk.noloop_of_nontrivial (h : G.IsCyclicWalk C) (hnt : C.Nontrivial) : C.NoLoop := by
  obtain ⟨x, e, rfl⟩ | h := h.loop_or_noloop
  · simp at hnt
  exact h

@[simp]
lemma rotate_toGraph {n : ℕ} (hC : C.IsClosed) (hCwf : C.WellFormed) :
    (C.rotate n).toGraph = C.toGraph := by
  ext a b c
  · simp [hC.mem_rotate]
  simp [hCwf.toGraph_isLink, (hCwf.rotate hC n).toGraph_isLink, hC]

@[simp]
lemma edgeRestrict_isCyclicWalk_iff (F : Set β) (C : WList α β) :
    (G ↾ F).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ E(C) ⊆ F := by
  refine ⟨fun h ↦ ⟨h.of_le edgeRestrict_le, ?_⟩,
    fun ⟨h, hss⟩ ↦ h.isCycle_of_le (by simp) (by simp [hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma edgeDelete_isCyclicWalk_iff (F : Set β) (C : WList α β) :
    (G ＼ F).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ Disjoint E(C) F := by
  refine ⟨fun h ↦ ⟨h.of_le edgeDelete_le, ?_⟩,
    fun ⟨h, hss⟩ ↦ h.isCycle_of_le (by simp) (by simp [subset_diff, hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa [subset_diff] using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma induce_isCyclicWalk_iff (X : Set α) (C : WList α β) :
    (G[X]).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ V(C) ⊆ X := by
  rw [isCyclicWalk_iff, isCyclicWalk_iff, induce_isTour_iff]
  tauto

@[simp]
lemma vertexDelete_isCyclicWalk_iff (X : Set α) (C : WList α β) :
    (G - X).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ Disjoint V(C) X := by
  rw [isCyclicWalk_iff, isCyclicWalk_iff, vertexDelete_isTour_iff]
  tauto

lemma IsCyclicWalk.of_forall_isLink (h : G.IsCyclicWalk C)
    (he : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) : H.IsCyclicWalk C where
  isWalk := h.isWalk.of_forall_isLink he h.nonempty
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed
  nodup := h.nodup

def IsCycleGraph (G : Graph α β) := ∃ C, G.IsCyclicWalk C ∧ V(G) ⊆ V(C) ∧ E(G) ⊆ E(C)

lemma IsCyclicWalk.toGraph_isCycleGraph (hC : G.IsCyclicWalk C) : C.toGraph.IsCycleGraph :=
  ⟨C, hC.isCyclicWalk_toGraph, by simp, by simp⟩

lemma isCycleGraph_iff_toGraph_isCyclicWalk :
    G.IsCycleGraph ↔ ∃ C, G.IsCyclicWalk C ∧ G = C.toGraph := by
  refine ⟨fun ⟨C, hC, hV, hE⟩ ↦ ?_, fun ⟨C, hC, heq⟩ ↦ heq ▸ hC.toGraph_isCycleGraph⟩
  use C, hC, ext_of_le_le le_rfl hC.isWalk.toGraph_le
    (antisymm (by simpa) <| vertexSet_mono hC.isWalk.toGraph_le)
    (antisymm (by simpa) <| edgeSet_mono hC.isWalk.toGraph_le)

lemma IsCycleGraph.exists_cycle_from (hG : G.IsCycleGraph) (hx : x ∈ V(G)) :
    ∃ C, G.IsCyclicWalk C ∧ V(G) ⊆ V(C) ∧ E(G) ⊆ E(C) ∧ C.first = x := by
  obtain ⟨C, hC, hV, hE⟩ := hG
  obtain ⟨n, hn, rfl⟩ := hC.isClosed.exists_rotate_first_eq hC.nonempty (hV hx)
  use (C.rotate n), hC.rotate n
  simp [hC.isClosed.rotate_vertexSet, hE, hV]

/-- Given a cycle graph, it can be oriented to a cyclic walk with an arbitrary starting vertex and
  arbitrary starting edge. -/
lemma IsCycleGraph.exists_cycle_of_isLink (hG : G.IsCycleGraph) (he : G.IsLink e x y) :
    ∃ C, G.IsCyclicWalk (cons x e C) ∧ V(G) ⊆ V(cons x e C) ∧ E(G) ⊆ E(cons x e C) ∧
    C.first = y := by
  obtain ⟨C, hC, hV, hE⟩ := hG
  rw [← hC.isWalk.isLink_iff_isLink_of_mem <| hE he.edge_mem, isLink_iff_dInc] at he
  obtain h | h := he
  · obtain ⟨w', n, h', rfl⟩ := hC.isClosed.exists_first_of_dInc h
    use w'
    rw [← h', rotate_edgeSet, hC.isClosed.rotate_vertexSet]
    use hC.rotate n
  rw [← dInc_reverse_iff] at h
  obtain ⟨w', n, h', rfl⟩ := reverse_isClosed_iff.mpr hC.isClosed |>.exists_first_of_dInc h
  use w'
  rw [← h', rotate_edgeSet, reverse_edgeSet, hC.reverse.isClosed.rotate_vertexSet,
    reverse_vertexSet]
  use hC.reverse.rotate n

-- lemma IsCycleGraph.exists_cycle_of_adj (hG : G.IsCycleGraph) (hadj : G.Adj x y) :
--     ∃ C, G.IsCyclicWalk C ∧ V(G) ⊆ V(C) ∧ E(G) ⊆ E(C) ∧ C.first = x ∧ C.get 1 = y := by
--   obtain ⟨e, he⟩ := hadj
--   obtain ⟨C, hC, hV, hE, rfl⟩ := hG.exists_cycle_of_isLink he
--   use (cons x e C), hC, hV, hE, by simp, by simp

/-- List of vertices in the cycle graph is the cyclic order-/
noncomputable def IsCycleGraph.vertices (hG : G.IsCycleGraph) (hx : x ∈ V(G)) : List α :=
  hG.exists_cycle_from hx |>.choose.vertex.dropLast

lemma IsCyclicWalk.exists_isPath (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) : ∃ P u e f,
    G.IsPath P ∧ u ∉ P ∧ e ∉ P.edge ∧ f ∉ P.edge ∧ e ≠ f ∧ C = cons u e (P.concat f u) := by
  refine ⟨C.tail.dropLast, C.first, hC.nonempty.firstEdge, hC.nonempty.lastEdge,
    hC.tail_dropLast_isPath, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dropLast_first, hnt.tail_dropLast]
    exact first_notMem_tail_of_nodup hC.dropLast_isPath.nodup hnt.dropLast_nonempty
  · refine mt (fun h ↦ ?_) (hC.nonempty.firstEdge_notMem_tail hC.edge_nodup)
    exact List.IsPrefix.mem h <| by simpa using List.dropLast_prefix C.tail.edge
  · refine mt (fun h ↦ ?_) (hC.nonempty.lastEdge_notMem_dropLast hC.edge_nodup)
    refine List.IsSuffix.mem h ?_
    simp only [dropLast_edge, tail_edge, ← List.tail_dropLast]
    exact List.tail_suffix C.edge.dropLast
  · refine mt (fun h_eq ↦ ?_) <| hC.nonempty.firstEdge_notMem_tail hC.edge_nodup
    rw [h_eq, ← hnt.tail_lastEdge]
    exact (Nontrivial.tail_nonempty hnt).lastEdge_mem
  cases C with
  | nil => simp at hnt
  | cons u e w =>
    have hw : w.Nonempty := hnt.tail_nonempty
    simpa [show u = w.last from hC.isClosed, hw.lastEdge_cons] using hw.concat_dropLast.symm

/-- An alternative version of `IsCyclicWalk.exists_isPath` where the tail and the head
of the cycle are explictly given as paths. -/
lemma IsCyclicWalk.exists_isPath' (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) : ∃ P u e f,
    G.IsPath (cons u e P) ∧ G.IsPath (P.concat f u) ∧ e ≠ f ∧ C = cons u e (P.concat f u) := by
  obtain ⟨P, u, e, f, hP, huP, heP, hfP, hef, rfl⟩ := hC.exists_isPath hnt
  use P, u, e, f
  have ht := hC.tail_isPath
  simp only [tail_cons, concat_isPath_iff] at ht
  have ht' := hC.reverse.tail_isPath
  simp only [reverse_cons, concat_reverse, cons_concat, tail_cons, concat_isPath_iff,
    reverse_isPath_iff, reverse_last, mem_reverse] at ht'
  simp [cons_isPath_iff, hP, huP, ht'.2.1.symm, ht.2.1, hef]

lemma IsCyclicWalk.exists_isPath_vertex [DecidableEq α] (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial)
    (hu : u ∈ C) : ∃ P e f, G.IsPath P ∧ u ∉ P ∧ e ∉ P.edge ∧ f ∉ P.edge ∧ e ≠ f ∧
    C.rotate (C.idxOf u) = cons u e (P.concat f u) := by
  obtain ⟨n, hn, rfl⟩ := hC.isClosed.exists_rotate_first_eq hnt.nonempty hu
  obtain ⟨P, u, e, f, hP, huP, heP, hfP, hne, hP'⟩ := (hC.rotate n).exists_isPath (hnt.rotate n)
  use P, e, f, hP, ?_, heP, hfP, hne, ?_
  · simpa [hP']
  rw [hP', first_cons, ← hP']
  congr
  apply_fun WList.first at hP'
  obtain rfl := by simpa [first_cons] using hP'
  rw [C.rotate_first _ hn.le]
  exact hC.idxOf_get hn

lemma IsCyclicWalk.exists_isPath_edge (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial)
    (he : e ∈ C.edge) : ∃ n P, G.IsPath P ∧ e ∉ P.edge ∧ C.rotate n = cons P.last e P := by
  obtain ⟨n, hn, hCne, rfl⟩ := exists_rotate_firstEdge_eq he
  obtain ⟨P, u, e, f, heP, hPf, hne, hC'⟩ := (hC.rotate n).exists_isPath' (hnt.rotate n)
  use n, P.concat f u, hPf, ?_, ?_
  · have := by simpa using heP.edge_nodup
    simp [hC', hne, this.1]
  convert hC' using 1
  simp [hC']

lemma IsCyclicWalk.loop_or_nontrivial (hC : G.IsCyclicWalk C) :
    (∃ x e, C = cons x e (nil x)) ∨ C.Nontrivial := by
  cases hC.nonempty with
  | cons x e w => cases w with | nil u => simp [show x = u from hC.isClosed] | cons => simp

lemma IsCyclicWalk.toGraph_vertexDelete_first_eq (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) :
    C.toGraph - ({C.first} : Set α) = C.tail.dropLast.toGraph := by
  obtain ⟨P, u, e, f, hP, huP, heP, hfP, hef, rfl⟩ := hC.exists_isPath hnt
  refine Graph.ext (by simpa) fun g x y ↦ ?_
  have h1 : P.IsLink g x y → x ∈ P := fun h ↦ h.left_mem
  have h2 : P.IsLink g x y → y ∈ P := fun h ↦ h.right_mem
  simp only [vertexDelete_isLink_iff, hC.isWalk.wellFormed.toGraph_isLink, isLink_cons_iff',
    concat_first, isLink_concat_iff, tail_cons, dropLast_concat,
    hP.isWalk.wellFormed.toGraph_isLink]
  aesop

lemma IsCyclicWalk.vertexSet_nontrivial (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) :
    V(C).Nontrivial := by
  obtain ⟨P, u, -, -, -, huP, -, -, -, rfl⟩ := hC.exists_isPath hnt
  refine Set.nontrivial_of_exists_ne (x := u) (by simp) ⟨P.first, ?_⟩
  simp [show P.first ≠ u by rintro rfl; simp at huP]

/-- Deleting a vertex from the graph of a nontrivial cycle gives the graph of a path. -/
lemma IsCyclicWalk.exists_isPath_toGraph_eq_delete_vertex (hC : G.IsCyclicWalk C)
    (hnt : C.Nontrivial) (hx : x ∈ C) :
    ∃ P, G.IsPath P ∧ P.toGraph = C.toGraph - ({x} : Set α) := by
  wlog hxC : x = C.first generalizing C with aux
  · obtain ⟨n, -, rfl⟩ := exists_rotate_first_eq hx
    obtain ⟨P, hP, hP'⟩ := aux (C := C.rotate n) (hC.rotate n) (hnt.rotate n) (by simp) rfl
    exact ⟨P, hP, by rw [hP', WellFormed.rotate_toGraph hC.isWalk.wellFormed hC.isClosed]⟩
  exact ⟨_, hC.tail_dropLast_isPath, by rw [hxC, hC.toGraph_vertexDelete_first_eq hnt]⟩

lemma IsCyclicWalk.exists_isPath_toGraph_eq_delete_edge_of_isLink (hC : G.IsCyclicWalk C)
    (he : C.IsLink e x y) :
    ∃ P, G.IsPath P ∧ P.toGraph = C.toGraph ＼ {e} ∧ P.first = x ∧ P.last = y := by
  wlog he' : C.DInc e y x with aux
  · obtain hxy | hxy := isLink_iff_dInc.1 he.symm
    · exact aux hC he hxy
    obtain ⟨P, hP, hPC, rfl, rfl⟩ := aux hC he.symm hxy
    exact ⟨P.reverse, hP.reverse, by rwa [hP.isWalk.wellFormed.reverse_toGraph], by simp⟩
  clear he
  wlog hxC : e = hC.nonempty.firstEdge generalizing C with aux
  · obtain ⟨n, -, _, rfl⟩ := exists_rotate_firstEdge_eq he'.edge_mem
    simpa [hC.isWalk.wellFormed.rotate_toGraph hC.isClosed] using
      aux (hC.rotate n) (hC.isClosed.dInc_rotate he' n) rfl
  refine ⟨C.tail, hC.tail_isPath, Graph.ext (by simp [hC.isClosed.vertexSet_tail])
    fun f z z' ↦ ?_, ?_⟩
  · rw [hC.tail_isPath.isWalk.wellFormed.toGraph_isLink, edgeDelete_isLink, Set.mem_singleton_iff,
      hC.isWalk.wellFormed.toGraph_isLink, hC.nonempty.tail_isLink_iff hC.edge_nodup, ← hxC]
  rw [tail_last, ← hC.isClosed.eq, and_comm, ← hC.toIsTrail.dInc_iff_eq_of_dInc he', hxC]
  cases C with | _ => simp_all

/-- Deleting an edge from the graph of a cycle gives the graph of a path. -/
lemma IsCyclicWalk.exists_isPath_toGraph_eq_delete_edge (hC : G.IsCyclicWalk C) (heC : e ∈ C.edge) :
    ∃ P, G.IsPath P ∧ P.toGraph = C.toGraph ＼ {e} := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edge heC
  obtain ⟨P, hP, hPC, -, -⟩ := hC.exists_isPath_toGraph_eq_delete_edge_of_isLink h
  exact ⟨P, hP, hPC⟩

lemma IsPath.cons_isCyclicWalk {P : WList α β} (hP : G.IsPath P) (he : G.IsLink e P.first P.last)
    (heP : e ∉ P.edge) : G.IsCyclicWalk (cons P.last e P) where
  isWalk := by simp [he.symm, hP.isWalk]
  edge_nodup := by simp [heP, hP.edge_nodup]
  nonempty := by simp
  isClosed := by simp
  nodup := by simp [hP.nodup]

/-- If `P` is nontrivial, then the edge assumption from `IsPath.cons_isCyclicWalk` isn't needed. -/
lemma IsPath.cons_isCyclicWalk_of_nontrivial {P : WList α β} (hP : G.IsPath P)
    (he : G.IsLink e P.first P.last) (hPnt : P.Nontrivial) : G.IsCyclicWalk (cons P.last e P) := by
  refine IsWalk.isCyclicWalk_of_closed_nodup (by simp [he.symm, hP.isWalk]) ?_ (by simp)
    (by simp [hP.nodup])
  have := hPnt.one_lt_length
  rw [cons_length]
  omega

lemma IsPath.concat_isCyclicWalk {P : WList α β} (hP : G.IsPath P) (he : G.IsLink e P.last P.first)
    (heP : e ∉ P.edge) : G.IsCyclicWalk (P.concat e P.first) := by
  simpa using (hP.reverse.cons_isCyclicWalk (e := e) (by simpa using he) (by simpa)).reverse

end Graph
