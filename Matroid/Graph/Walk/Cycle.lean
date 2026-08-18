module

public import Matroid.Graph.Walk.Path
public import Matroid.Graph.WList.Cycle
import all Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Delete


@[expose] public section

variable {α β : Type*} {x y z u v a b : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ C C₁ C₂ : WList α β} {S T : Set α} {n : ℕ}

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

lemma IsTour.isCyclicWalk_of_dropLast_nodup (h : G.IsTour C) (hC : C.dropLast.vertex.Nodup) :
    G.IsCyclicWalk C := by
  refine ⟨h, ?_⟩
  induction C using WList.concat_induction with
  | nil u => simp
  | concat w e x hw =>
    simp only [dropLast_concat] at hC
    simp only [concat_nonempty, Nonempty.vertex_tail, concat_vertex, ne_eq, vertex_ne_nil,
      not_false_eq_true, List.tail_append_of_ne_nil]
    rwa [← List.concat_eq_append, List.nodup_concat, ← List.nodup_cons, ← show w.first = x by
      simpa using h.isClosed.eq, ← vertex_head, List.cons_head_tail]

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

lemma IsCyclicWalk.reverse (hC : G.IsCyclicWalk C) : G.IsCyclicWalk C.reverse := by
  refine hC.toIsTour.reverse.isCyclicWalk_of_dropLast_nodup ?_
  simpa using hC.nodup

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
lemma restrict_isTour_iff (F : Set β) (C : WList α β) :
    (G ↾ F).IsTour C ↔ G.IsTour C ∧ E(C) ⊆ F := by
  refine ⟨fun h ↦ ⟨h.of_le restrict_le, ?_⟩,
    fun ⟨h, hss⟩ ↦ h.of_le_of_subset (by simp) (by simp [hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa only [edgeSet_restrict, subset_inter_iff] using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma deleteEdges_isTour_iff (F : Set β) (C : WList α β) :
    (G ＼ F).IsTour C ↔ G.IsTour C ∧ Disjoint E(C) F := by
  refine ⟨fun h ↦ ⟨h.of_le deleteEdges_le, ?_⟩, fun ⟨h, hss⟩ ↦
    h.of_le_of_subset (by simp) (by simp [subset_sdiff, hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa only [edgeSet_deleteEdges, subset_sdiff] using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma induce_isTour_iff (X : Set α) (C : WList α β) : (G[X]).IsTour C ↔ G.IsTour C ∧ V(C) ⊆ X := by
  refine ⟨fun h ↦ ⟨?_, h.isWalk.vertexSet_subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩
  · refine ⟨⟨?_, h.edge_nodup⟩, h.nonempty, h.isClosed⟩
    obtain ⟨x, hx, rfl⟩ | ⟨hC, hCX⟩ := by
      simpa only [isWalk_induce_iff, mem_sdiff] using h.isWalk
    · simpa using h.nonempty
    exact hC
  refine ⟨⟨?_, h.edge_nodup⟩, h.nonempty, h.isClosed⟩
  simp [isWalk_induce_iff, h.isWalk, hss]

@[simp]
lemma deleteVerts_isTour_iff (X : Set α) (C : WList α β) :
    (G - X).IsTour C ↔ G.IsTour C ∧ Disjoint V(C) X := by
  refine ⟨fun h ↦ ⟨⟨⟨?_, h.edge_nodup⟩, h.nonempty, h.isClosed⟩,
    h.isWalk.disjoint_of_deleteVerts⟩, fun ⟨h, hdisj⟩ ↦
    ⟨⟨by simp [h.isWalk, hdisj], h.edge_nodup⟩, h.nonempty, h.isClosed⟩⟩
  have := by simpa only [isWalk_deleteVerts_iff] using h.isWalk
  exact this.1

/-- Dedup preserves being a trail (walk with distinct edges). -/
lemma IsTrail.dedup [DecidableEq α] (hC : G.IsTrail C) : G.IsTrail C.dedup :=
  hC.isWalk.dedup.isTrail

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

lemma IsCyclicWalk.rotate_one (hC : G.IsCyclicWalk C) :
    ∃ e, C.rotate 1 = C.tail.concat e C.tail.first :=
  hC.nonempty.rotate_one

lemma IsCyclicWalk.idxOf_rotate_one [DecidableEq α] (hC : G.IsCyclicWalk C) (h1 : C.first ≠ a)
    (ha : a ∈ C) : (C.rotate 1).idxOf a + 1 = C.idxOf a :=
  hC.nonempty.idxOf_rotate_one h1 ha

lemma IsCyclicWalk.idxOf_rotate_first [DecidableEq α] (_ : G.IsCyclicWalk C) (hlt : n < C.idxOf a) :
    (C.rotate n).first ≠ a :=
  idxOf_rotate_first_ne_of_lt hlt

lemma IsCyclicWalk.idxOf_rotate_n_le [DecidableEq α] (_ : G.IsCyclicWalk C) (ha : a ∈ C)
    (hle : n ≤ C.idxOf a) : (C.rotate n).idxOf a + n = C.idxOf a :=
  C.idxOf_rotate_add_of_le_idxOf ha hle

lemma IsCyclicWalk.idxOf_rotate_one_first' [DecidableEq α] (hC : G.IsCyclicWalk C) :
    (C.rotate 1).idxOf C.first + 1 = C.length := by
  obtain ⟨e, hrC⟩ := hC.rotate_one
  rw [hrC, idxOf_concat_of_mem, hC.isClosed.eq, ← tail_last, idxOf_last _ hC.nodup, tail_length,
    Nat.sub_add_cancel hC.nonempty.length_pos]
  rw [hC.isClosed.mem_tail_iff]
  exact first_mem

lemma IsCyclicWalk.idxOf_rotate_one_first [DecidableEq α] (hC : G.IsCyclicWalk C) (h1 : C.first = a)
    (ha : a ∈ C) : (C.rotate 1).idxOf a + 1 = C.length := by
  obtain ⟨e, hrC⟩ := hC.rotate_one
  have hft := h1 ▸ hC.isClosed.eq
  rw [hrC, idxOf_concat_of_mem (hC.isClosed.mem_tail_iff.2 ha), hft, (tail_last C).symm,
    idxOf_last C.tail hC.nodup, tail_length]
  have := hC.nonempty.length_pos
  omega

lemma IsCyclicWalk.idxOf_rotate_untilfirst [DecidableEq α] (hC : G.IsCyclicWalk C) (ha : a ∈ C) :
    (C.rotate (C.idxOf a + 1)).idxOf a + 1 = C.length := by
  rw [← rotate_rotate C (C.idxOf a) 1, (hC.rotate (C.idxOf a)).idxOf_rotate_one_first
    (rotate_idxOf_first ha) (hC.isClosed.mem_rotate.mpr ha), length_rotate]

lemma IsCyclicWalk.idxOf_rotate_idxOf [DecidableEq α] (hC : G.IsCyclicWalk C) (ha : a ∈ C) :
    (C.rotate (C.idxOf a)).idxOf a = 0 := by
  simpa using hC.idxOf_rotate_n_le ha le_rfl

lemma IsCyclicWalk.idxOf_rotate_n [DecidableEq α] (hC : G.IsCyclicWalk C) (ha : a ∈ C)
    (hn : n < C.length) (hle : C.idxOf a < n) :
    (C.rotate n).idxOf a + n = C.length + C.idxOf a := by
  obtain ⟨x, rfl⟩ | hnt := exists_eq_nil_or_nonempty C
  · simp_all
  induction n with | zero => simp_all | succ n hi =>
  obtain han | hu := eq_or_ne (C.idxOf a) n
  · rw [← han]
    have hle' : C.idxOf a < C.length := by
      rw [han]
      exact Nat.lt_of_succ_lt hn
    have := hC.idxOf_rotate_untilfirst ha
    omega
  rw [← C.rotate_rotate n 1]
  have hg : n < C.length := Nat.lt_of_succ_lt hn
  have hii := hi hg (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hle) hu)
  have hnf : (C.rotate n).first ≠ a := by
    by_contra hc
    have hia : (C.rotate n).idxOf a = 0 := by
      rw [← hc]
      exact idxOf_first (C.rotate n)
    rw [hia, zero_add] at hii
    rw [hii] at hg
    omega
  have ha' : a ∈ C.rotate n := (IsClosed.mem_rotate hC.isClosed).mpr ha
  have hf := (rotate_nonempty_iff.mpr hnt).idxOf_rotate_one hnf ha'
  omega

lemma IsCyclicWalk.idxOf_adj [DecidableEq α] (hC : G.IsCyclicWalk C) (ha : a ∈ C) (hb : b ∈ C)
    (he : C.idxOf b = C.idxOf a + 1) : G.Adj a b :=
  hC.isTrail.idxOf_adj ha hb he

lemma IsCyclicWalk.idxOf_adj_first [DecidableEq α] (hC : G.IsCyclicWalk C) (hab : a ≠ b)
    (ha : C.idxOf a = 0) (hb : C.idxOf b = C.length - 1) : G.Adj a b := by
  have haC : a ∈ C := by
    have hlea : C.idxOf a ≤ C.length := by
      rw [ha]
      exact Nat.zero_le C.length
    exact idxOf_le_length_iff_mem.mp hlea
  have hbC : b ∈ C := by
    have hle : C.idxOf b ≤ C.length := by
      rw [hb]
      omega
    exact idxOf_le_length_iff_mem.mp hle
  obtain h0 | hnt := DecidableNonempty C
  · simp only [WList.not_nonempty_iff] at h0
    rw [length_eq_zero.2 h0, zero_tsub, ← ha] at hb
    exact hab (C.idxOf_inj_of_left_mem haC hb.symm) |>.elim
  obtain h1 | hle := le_or_gt C.length 1
  · rw [h1.antisymm (one_le_length_iff.mpr hnt), tsub_self, ← ha] at hb
    exact hab (C.idxOf_inj_of_left_mem haC hb.symm) |>.elim
  have hn : C.idxOf b < C.length := by
    rw [hb]
    omega
  have hab : C.idxOf a < C.idxOf b := by
    rw [ha, hb]
    exact Nat.zero_lt_sub_of_lt hle
  have := hC.idxOf_rotate_idxOf hbC
  have hf := hC.idxOf_rotate_n haC hn hab
  rw [ha, ← this] at hf
  nth_rw 2 [hb] at hf
  have hlast : (C.rotate (C.idxOf b)).idxOf a = (C.rotate (C.idxOf b)).idxOf b + 1 := by omega
  exact ((hC.rotate (C.idxOf b)).idxOf_adj (hC.isClosed.mem_rotate.2 hbC)
    (hC.isClosed.mem_rotate.2 haC) hlast).symm

lemma IsCyclicWalk.idxOf_rotate [DecidableEq α] (hC : G.IsCyclicWalk C) (ha : a ∈ C)
    (hn : n < C.length) : ((C.rotate n).idxOf a + n) % C.length = C.idxOf a := by
  obtain ⟨x, rfl⟩ | hne := exists_eq_nil_or_nonempty C
  · simp_all
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  · rw [hC.idxOf_rotate_n_le ha hle]
    exact Nat.mod_eq_of_lt (hC.isClosed.idxOf_lt_length ha hne)
  rw [hC.idxOf_rotate_n ha hn hlt]
  simp only [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (hC.isClosed.idxOf_lt_length ha hne)

lemma IsCyclicWalk.idxOf_adj_rotate [DecidableEq α] (hC : G.IsCyclicWalk C) (ha : a ∈ C)
    (hb : b ∈ C) (hn : n < C.length) :
    C.idxOf b = C.idxOf a + 1 ∨ (C.idxOf b = 0 ∧ C.idxOf a = C.length - 1)
    ↔ (C.rotate n).idxOf b = (C.rotate n).idxOf a + 1 ∨
    ((C.rotate n).idxOf b = 0 ∧ (C.rotate n).idxOf a = C.length - 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  have := hC.idxOf_rotate_n_le ha hle
  · obtain hleb | hltb := le_or_gt n (C.idxOf b)
    · have := hC.idxOf_rotate_n_le hb hleb
      omega
    have := hC.idxOf_rotate_n hb hn hltb
    omega
  obtain hleb | hltb := le_or_gt n (C.idxOf b)
  · have := hC.idxOf_rotate_n ha hn hlt
    have := hC.idxOf_rotate_n_le hb hleb
    omega
  have := hC.idxOf_rotate_n ha hn hlt
  have := hC.idxOf_rotate_n hb hn hltb
  omega
  have hne := hC.nonempty
  have hh : (C.rotate n).idxOf b + n = (C.rotate n).idxOf a + n + 1 ∨
      (C.rotate n).idxOf b + n = n ∧ (C.rotate n).idxOf a + n = (C.length - 1) + n := by
    omega
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  rw [hC.idxOf_rotate_n_le ha hle] at hh
  · obtain hleb | hltb := le_or_gt n (C.idxOf b)
    · rw [hC.idxOf_rotate_n_le hb hleb] at hh
      obtain hgood | hf := hh
      · omega
      have := hC.isClosed.idxOf_lt_length ha hne
      rw [hf.2] at this
      by_contra
      omega
    rw [hC.idxOf_rotate_n hb hn hltb] at hh
    have := hC.isClosed.idxOf_lt_length ha hne
    have : C.length ≤ C.length + C.idxOf b := Nat.le_add_right C.length (C.idxOf b)
    obtain haa | haaa : C.length + C.idxOf b = C.length ∨ C.length + C.idxOf b = C.length + 1 := by
      omega
    · simp only [Nat.add_eq_left] at haa
      rw [haa] at hh
      omega
    simp only [Nat.add_left_cancel_iff] at haaa
    simp only [haaa, Nat.add_right_cancel_iff] at hh
    omega
  obtain hleb | hltb := le_or_gt n (C.idxOf b)
  rw [hC.idxOf_rotate_n_le hb hleb] at hh
  · rw [hC.idxOf_rotate_n ha hn hlt] at hh
    have := hC.isClosed.idxOf_lt_length hb hne
    omega
  rw [hC.idxOf_rotate_n ha hn hlt, hC.idxOf_rotate_n hb hn hltb] at hh
  omega

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

lemma IsCyclicWalk.eq_cons_concat (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) :
    ∃ x e f P, G.IsPath P ∧ x ∉ P ∧ e ∉ P.edge ∧ f ∉ P.edge ∧ C = cons x e (P.concat f x) := by
  obtain ⟨x, e, P, f, y, rfl⟩ := hnt.exists_cons_concat
  obtain rfl : x = y := by simpa using hC.isClosed.eq
  refine ⟨x, e, f, P, ?_, fun hxP ↦ ?_, fun heP ↦ ?_, by grind [hC.edge_nodup], rfl⟩
  · simpa using hC.tail_dropLast_isPath
  · simpa [hxP] using hC.dropLast_isPath
  simpa [heP] using hC.edge_nodup

lemma IsCyclicWalk.mem_tail_dropLast_of_ne_first (hC : G.IsCyclicWalk C) (hxC : x ∈ C)
    (hx : x ≠ C.first) : x ∈ C.tail.dropLast := by
  rwa [mem_iff_eq_first_or_mem_tail, or_iff_right hx, mem_iff_eq_mem_dropLast_or_eq_last,
    tail_last, ← hC.isClosed, or_iff_left hx] at hxC

lemma IsCyclicWalk.tail_dropLast_vertexSet (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) :
    V(C.tail.dropLast) = V(C) \ {C.first} := by
  cases C with
  | nil => simp at hC
  | cons u e w =>
    simp only [tail_cons, cons_vertexSet, first_cons, mem_singleton_iff, insert_sdiff_of_mem]
    rw [dropLast_vertexSet_of_nodup (by simpa using hC.tail_isPath.nodup) (by simpa using hnt),
      show u = w.last from hC.isClosed]

lemma IsCyclicWalk.eq_or_nil_of_isSublist_of_first_last_eq (hC : G.IsCyclicWalk C) (h : w ≤ C)
    (hfirst : w.first = C.first) (hlast : w.last = C.last) : w = C ∨ w = nil w.first := by
  induction h with
  | nil hmem => exact Or.inr rfl
  | @cons x e w₁ w₂ h ih =>
    have hw := hC.tail_isPath.sublist (by simpa using h)
    have hfl : w₁.first = w₁.last := (hfirst.trans hC.isClosed).trans hlast.symm
    exact Or.inr ((first_eq_last_iff hw.nodup).mp hfl).eq_nil_first
  | @cons₂ x e w₁ w₂ h h_eq ih =>
    have htail : w₁ = w₂ := by
      simpa using hC.tail_isPath.eq_of_sublist_of_first_eq_last_eq h h_eq (by simpa using hlast)
    exact Or.inl (by simp [htail])

lemma IsCyclicWalk.ne_iff_isPath_of_isSublist (hC : G.IsCyclicWalk C) (h : w ≤ C) :
    w ≠ C ↔ G.IsPath w := by
  obtain hfirst | hfirst := eq_or_ne w.first C.first |>.symm
  · simp only [ne_eq, hC.tail_isPath.sublist (h.le_tail_of_ne_first hfirst), iff_true]
    grind
  obtain hlast | hlast := eq_or_ne w.last C.last |>.symm
  · simp only [ne_eq, hC.dropLast_isPath.sublist (h.le_dropLast_of_ne_last hlast), iff_true]
    grind
  obtain rfl | hw := hC.eq_or_nil_of_isSublist_of_first_last_eq h hfirst hlast
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact (hC.nonempty.not_nil <| ·.first_eq_last_iff.mp hC.isClosed)
  have hne : w ≠ C := fun h ↦ hC.nonempty.not_nil <| h ▸ hw ▸ nil_nil
  simp only [ne_eq, hne, not_false_eq_true, true_iff]
  exact hw ▸ nil_isPath <| hC.vertexSet_subset (IsSublist.subset h first_mem)

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
      obtain ⟨⟨he : e' ≠ e'', -⟩, -⟩ := by
        simpa only [cons_edge, List.nodup_cons, List.mem_cons, not_or] using h.edge_nodup
      obtain ⟨hvw : v ∉ w, -⟩ := by
        simpa only [tail_cons, cons_vertex, List.nodup_cons, mem_vertex] using h.tail_isPath.nodup
      suffices w.Nil ↔ w = nil w.last by
        simpa [he, show u = w.last from h.isClosed, show w.last ≠ v by rintro rfl; simp_all]
      exact ⟨Nil.eq_nil_last, fun h ↦ by rw [h]; simp⟩

lemma IsCyclicWalk.encard_vertexSet (h : G.IsCyclicWalk C) : V(C).encard = C.length := by
  rw [← h.nonempty.cons_tail, cons_length, cons_vertexSet, Set.insert_eq_of_mem,
    encard_vxSet_of_nodup h.nodup, Nat.cast_add, Nat.cast_one]
  rw [h.isClosed.eq, ← tail_last, mem_vertexSet_iff]
  exact last_mem

lemma IsCyclicWalk.ncard_vertexSet (h : G.IsCyclicWalk C) : V(C).ncard = C.length := by
  have := h.encard_vertexSet
  rw [← C.vertexSet_finite.cast_ncard_eq] at this
  norm_cast at this

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
  obtain rfl : x = w.last := by simpa using h.isClosed
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
lemma restrict_isCyclicWalk_iff (F : Set β) (C : WList α β) :
    (G ↾ F).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ E(C) ⊆ F := by
  refine ⟨fun h ↦ ⟨h.of_le restrict_le, ?_⟩,
    fun ⟨h, hss⟩ ↦ h.isCycle_of_le (by simp) (by simp [hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa only [edgeSet_restrict, subset_inter_iff] using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma deleteEdges_isCyclicWalk_iff (F : Set β) (C : WList α β) :
    (G ＼ F).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ Disjoint E(C) F := by
  refine ⟨fun h ↦ ⟨h.of_le deleteEdges_le, ?_⟩,
    fun ⟨h, hss⟩ ↦ h.isCycle_of_le (by simp) (by simp [subset_sdiff, hss, h.isWalk.edgeSet_subset])⟩
  have := by simpa only [edgeSet_deleteEdges, subset_sdiff] using h.isWalk.edgeSet_subset
  use this.2

@[simp]
lemma induce_isCyclicWalk_iff (X : Set α) (C : WList α β) :
    (G[X]).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ V(C) ⊆ X := by
  rw [isCyclicWalk_iff, isCyclicWalk_iff, induce_isTour_iff]
  tauto

@[simp]
lemma deleteVerts_isCyclicWalk_iff (X : Set α) (C : WList α β) :
    (G - X).IsCyclicWalk C ↔ G.IsCyclicWalk C ∧ Disjoint V(C) X := by
  rw [isCyclicWalk_iff, isCyclicWalk_iff, deleteVerts_isTour_iff]
  tauto

lemma IsCyclicWalk.of_forall_isLink (h : G.IsCyclicWalk C)
    (he : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) : H.IsCyclicWalk C where
  isWalk := h.isWalk.of_forall_isLink he h.nonempty
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed
  nodup := h.nodup

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
  obtain rfl := by simpa only [first_cons] using hP'
  rw [C.rotate_first _ hn.le]
  exact hC.idxOf_get hn

lemma IsCyclicWalk.exists_isPath_edge (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial)
    (he : e ∈ C.edge) : ∃ n P, G.IsPath P ∧ e ∉ P.edge ∧ C.rotate n = cons P.last e P := by
  obtain ⟨n, hn, hCne, rfl⟩ := exists_rotate_firstEdge_eq he
  obtain ⟨P, u, e, f, heP, hPf, hne, hC'⟩ := (hC.rotate n).exists_isPath' (hnt.rotate n)
  use n, P.concat f u, hPf, ?_, ?_
  · have := by simpa only [cons_edge, List.nodup_cons] using heP.edge_nodup
    simp [hC', hne, this.1]
  convert hC' using 1
  simp [hC']

lemma IsCyclicWalk.loop_or_nontrivial (hC : G.IsCyclicWalk C) :
    (∃ x e, C = cons x e (nil x)) ∨ C.Nontrivial := by
  cases hC.nonempty with
  | cons x e w => cases w with | nil u => simp [show x = u from hC.isClosed] | cons => simp

lemma IsCyclicWalk.toGraph_deleteVerts_first_eq (hC : G.IsCyclicWalk C) (hnt : C.Nontrivial) :
    C.toGraph - ({C.first} : Set α) = C.tail.dropLast.toGraph := by
  obtain ⟨P, u, e, f, hP, huP, heP, hfP, hef, rfl⟩ := hC.exists_isPath hnt
  refine Graph.ext (by simpa) fun g x y ↦ ?_
  have h1 : P.IsLink g x y → x ∈ P := fun h ↦ h.left_mem
  have h2 : P.IsLink g x y → y ∈ P := fun h ↦ h.right_mem
  simp only [deleteVerts_isLink_iff, hC.isWalk.wellFormed.toGraph_isLink, isLink_cons_iff',
    concat_first, isLink_concat_iff, tail_cons, dropLast_concat,
    hP.isWalk.wellFormed.toGraph_isLink]
  aesop

lemma IsCyclicWalk.nontrivial_iff_vertexSet_nontrivial (hC : G.IsCyclicWalk C) :
    C.Nontrivial ↔ V(C).Nontrivial := by
  refine ⟨fun hnt ↦ ?_, fun hV ↦ (hC.loop_or_nontrivial).resolve_left ?_⟩
  · obtain ⟨P, u, -, -, -, huP, -, -, -, rfl⟩ := hC.exists_isPath hnt
    refine Set.nontrivial_of_exists_ne (x := u) (by simp) ⟨P.first, ?_⟩
    simp [show P.first ≠ u by rintro rfl; simp at huP]
  grind [insert_eq_of_mem, not_nontrivial_singleton]

lemma IsCyclicWalk.nontrivial_iff_edgeSet_nontrivial (hC : G.IsCyclicWalk C) :
    C.Nontrivial ↔ E(C).Nontrivial := by
  refine ⟨fun hnt ↦ ?_, fun hE ↦ (hC.loop_or_nontrivial).resolve_left ?_⟩
  · obtain ⟨_, e, _, f, _⟩ := hnt
    exact Set.nontrivial_of_exists_ne (x := e) (by simp) ⟨f, by simp, by grind [hC.edge_nodup]⟩
  grind [insert_empty_eq, not_nontrivial_singleton]

/-- Deleting a vertex from the graph of a nontrivial cycle gives the graph of a path. -/
lemma IsCyclicWalk.exists_isPath_toGraph_eq_delete_vertex (hC : G.IsCyclicWalk C)
    (hnt : C.Nontrivial) (hx : x ∈ C) :
    ∃ P, G.IsPath P ∧ P.toGraph = C.toGraph - ({x} : Set α) := by
  wlog hxC : x = C.first generalizing C with aux
  · obtain ⟨n, -, rfl⟩ := exists_rotate_first_eq hx
    obtain ⟨P, hP, hP'⟩ := aux (C := C.rotate n) (hC.rotate n) (hnt.rotate n) (by simp) rfl
    exact ⟨P, hP, by rw [hP', WellFormed.rotate_toGraph hC.isWalk.wellFormed hC.isClosed]⟩
  exact ⟨_, hC.tail_dropLast_isPath, by rw [hxC, hC.toGraph_deleteVerts_first_eq hnt]⟩

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
  · rw [hC.tail_isPath.isWalk.wellFormed.toGraph_isLink, deleteEdges_isLink, Set.mem_singleton_iff,
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

/-! ### Decompositions of cyclic walks -/

/-- A member of a nontrivial decomposition of a cyclic walk is a path. -/
lemma IsCyclicWalk.isPath_of_mem_decomposeTo {P : WList α β} {L : List (WList α β)}
    [Inhabited α] (hC : G.IsCyclicWalk C) (hdec : C.DecomposeTo L)
    (hne : ∀ P ∈ L, P.Nonempty) (hcard : 1 < L.length) (hP : P ∈ L) :
    G.IsPath P := by
  refine (hC.ne_iff_isPath_of_isSublist (hdec.isSublist_of_mem hP)).mp ?_
  rintro rfl
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hP
  obtain ⟨m, hm, hnm⟩ : ∃ m < L.length, m ≠ n := by
    match n with
    | 0 => exact ⟨1, hcard, by omega⟩
    | _ + 1 => exact ⟨0, by omega, by omega⟩
  have hdisj : Disjoint E(L[n]) E(L[m]) := by
    have hpw := List.pairwise_iff_getElem.mp (hdec.disjoint_of_edge_nodup hC.edge_nodup)
    obtain hgt | hlt := lt_or_gt_of_ne hnm
    · exact (hpw m n hm hn hgt).symm
    exact hpw n m hn hm hlt
  obtain ⟨f, hf⟩ := (hne _ (List.getElem_mem hm)).edgeSet_nonempty
  exact hdisj.notMem_of_mem_right hf <|
    (hdec.isSublist_of_mem (List.getElem_mem hm)).edge_subset hf

/-- The index in `C` of the initial vertex of the `i`th piece of a decomposition of a cyclic walk
into nonempty pieces, together with bounds for the indices of the internal vertices of that
piece. Here `((L.take i)⁺).length` is the number of edges in the first `i` pieces. -/
private lemma IsCyclicWalk.decomposeTo_idxOf [DecidableEq α] [Inhabited α]
    {L : List (WList α β)} (hC : G.IsCyclicWalk C) (hdec : C.DecomposeTo L)
    (hne : ∀ P ∈ L, P.Nonempty) {i : ℕ} (hi : i < L.length) :
    C.idxOf L[i].first = ((L.take i)⁺).length ∧
    ∀ x ∈ L[i].internalVertexSet, ((L.take i)⁺).length < C.idxOf x ∧
      C.idxOf x < ((L.take (i + 1))⁺).length := by
  have hne' : L.drop i ≠ [] := by simpa using hi
  have hsucc := WList.length_appendList_take_succ hi
  have hL := (hne _ (List.getElem_mem hi)).length_pos
  have hCl : ((L.take L.length)⁺).length = C.length := by
    rw [List.take_length, ← hdec.append]
  have hlen : ((L.take (i + 1))⁺).length ≤ C.length := by
    rw [← hCl]
    exact WList.length_appendList_take_mono L (by omega)
  have hsplit : ∀ m, C.get (((L.take i)⁺).length + m) = ((L.drop i)⁺).get m := by
    rintro m
    have h : L⁺ = (L.take i)⁺ ++ (L.drop i)⁺ := by
      rw [← WList.appendList_append _ hne', List.take_append_drop]
    rw [hdec.append, h, WList.get_append_add]
  have hfirst : C.get ((L.take i)⁺).length = L[i].first := by
    simpa [appendList_first hne' (hdec.chain_eq.drop i)] using hsplit 0
  refine ⟨by rw [← hfirst, hC.idxOf_get (by omega)], fun x hx ↦ ?_⟩
  obtain ⟨m, hm0, hml, rfl⟩ := WList.exists_get_of_mem_internalVertexSet hx
  have hpre : L[i].IsPrefix ((L.drop i)⁺) := by
    simpa using DecomposeTo.head_isPrefix ⟨hne', rfl, hdec.chain_eq.drop i⟩
  have hidx : C.idxOf (L[i].get m) = ((L.take i)⁺).length + m := by
    rw [hpre.get_eq_of_length_ge hml.le, ← hsplit m, hC.idxOf_get (by omega)]
  omega

/-- The initial vertices of the pieces in a nonempty decomposition of a cyclic walk are distinct. -/
lemma IsCyclicWalk.map_first_nodup_of_decomposeTo {L : List (WList α β)} [Inhabited α]
    (hC : G.IsCyclicWalk C) (hdec : C.DecomposeTo L) (hne : ∀ P ∈ L, P.Nonempty) :
    (L.map WList.first).Nodup := by
  classical
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij ↦ ?_
  simp only [List.length_map, List.getElem_map, ne_eq] at hi hj ⊢
  rintro heq
  have h1 := (hC.decomposeTo_idxOf hdec hne hi).1
  rw [heq, (hC.decomposeTo_idxOf hdec hne hj).1] at h1
  exact absurd h1.symm (WList.length_appendList_take_lt hne hij hj.le).ne

/-- Distinct pieces in a nonempty decomposition of a cyclic walk have disjoint interiors. -/
lemma IsCyclicWalk.pairwise_disjoint_internalVertexSet_of_decomposeTo
    {L : List (WList α β)} [Inhabited α] (hC : G.IsCyclicWalk C)
    (hdec : C.DecomposeTo L) (hne : ∀ P ∈ L, P.Nonempty) :
    L.Pairwise (fun P Q ↦ Disjoint P.internalVertexSet Q.internalVertexSet) := by
  classical
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij ↦ ?_
  refine Set.disjoint_left.mpr fun x hx hx' ↦ ?_
  obtain ⟨-, hlt⟩ := (hC.decomposeTo_idxOf hdec hne hi).2 x hx
  obtain ⟨hgt, -⟩ := (hC.decomposeTo_idxOf hdec hne hj).2 x hx'
  have hle : ((L.take (i + 1))⁺).length ≤ ((L.take j)⁺).length :=
    WList.length_appendList_take_mono L (by omega)
  omega

/-- No internal vertex of a piece in a nonempty cyclic decomposition is the initial vertex of
another piece. -/
lemma IsCyclicWalk.internalVertexSet_disjoint_map_first_of_decomposeTo
    {P : WList α β} {L : List (WList α β)} [Inhabited α] (hC : G.IsCyclicWalk C)
    (hdec : C.DecomposeTo L) (hne : ∀ P ∈ L, P.Nonempty) (hP : P ∈ L) :
    Disjoint P.internalVertexSet {x | x ∈ L.map WList.first} := by
  classical
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
  refine Set.disjoint_left.mpr fun x hx hx' ↦ ?_
  simp only [Set.mem_ofPred_eq, List.mem_map] at hx'
  obtain ⟨Q, hQ, rfl⟩ := hx'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hQ
  obtain ⟨hlt1, hlt2⟩ := (hC.decomposeTo_idxOf hdec hne hi).2 _ hx
  have heq := (hC.decomposeTo_idxOf hdec hne hj).1
  obtain hij | hji := lt_or_ge i j
  · have hle : ((L.take (i + 1))⁺).length ≤ ((L.take j)⁺).length :=
      WList.length_appendList_take_mono L (by omega)
    omega
  have hle : ((L.take j)⁺).length ≤ ((L.take i)⁺).length :=
    WList.length_appendList_take_mono L (by omega)
  omega

end Graph
