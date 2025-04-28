import Matroid.ForMathlib.Graph.Walk.Path
-- import Matroid.ForMathlib.Graph.Connected
import Matroid.ForMathlib.Graph.WList.Cycle

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ C C₁ C₂ : WList α β} {S T : Set α}

open WList

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

/-- `G.IsCycle C` means that `C` is a nonempty closed walk with no repeated vertices or edges. -/
@[mk_iff]
structure IsCycle (G : Graph α β) (C : WList α β) : Prop extends G.IsTrail C where
  nonempty : C.Nonempty
  /-- The start and end vertex are the same -/
  isClosed : C.IsClosed
  /-- There are no repeated vertices except for the first and last. -/
  nodup : C.tail.vx.Nodup

lemma IsCycle.rotate (hC : G.IsCycle C) (n : ℕ) : G.IsCycle (C.rotate n) where
  nonempty := by simpa using hC.nonempty
  isWalk := hC.isWalk.rotate hC.isClosed n
  edge_nodup := by simpa using hC.edge_nodup
  isClosed := hC.isClosed.rotate n
  nodup := by simpa [rotate_vx_tail, List.nodup_rotate] using hC.nodup

@[simp]
lemma not_isCycle_nil (x : α) : ¬ G.IsCycle (nil x : WList α β) :=
  fun h ↦ by simpa using h.nonempty

lemma IsCycle.intRotate (hC : G.IsCycle C) (n : ℤ) : G.IsCycle (C.intRotate n) :=
  hC.rotate ..

lemma IsCycle.tail_isPath (hC : G.IsCycle C) : G.IsPath C.tail where
  isWalk := hC.isWalk.suffix <| tail_isSuffix C
  nodup := hC.nodup

lemma IsCycle.dropLast_isPath (hC : G.IsCycle C) : G.IsPath C.dropLast := by
  have h := (hC.intRotate (-1)).isClosed.rotate_one_dropLast
  rw [← IsClosed.intRotate_eq_rotate, hC.isClosed.intRotate_intRotate] at h
  · simp only [Int.reduceNeg, Int.cast_ofNat_Int, neg_add_cancel, intRotate_zero] at h
    rw [h]
    exact (hC.intRotate (-1)).tail_isPath
  exact (hC.intRotate _).isClosed

lemma IsCycle.tail_dropLast_isPath (hC : G.IsCycle C) : G.IsPath C.tail.dropLast :=
  hC.tail_isPath.prefix C.tail.dropLast_isPrefix

lemma IsCycle.mem_tail_dropLast_of_ne_first (hC : G.IsCycle C) (hxC : x ∈ C) (hx : x ≠ C.first) :
    x ∈ C.tail.dropLast := by
  rwa [mem_iff_eq_first_or_mem_tail, or_iff_right hx, mem_iff_eq_mem_dropLast_or_eq_last,
    tail_last, ← hC.isClosed, or_iff_left hx] at hxC

lemma IsCycle.tail_dropLast_vxSet (hC : G.IsCycle C) (hnt : C.Nontrivial) :
    C.tail.dropLast.V = C.V \ {C.first} := by
  cases C with
  | nil => simp at hC
  | cons u e w =>
    simp only [tail_cons, cons_vxSet, first_cons, Set.mem_singleton_iff, Set.insert_diff_of_mem]
    rw [dropLast_vxSet_of_nodup (by simpa using hC.tail_isPath.nodup) (by simpa using hnt),
      show u = w.last from hC.isClosed]

lemma IsCycle.reverse (hC : G.IsCycle C) : G.IsCycle C.reverse where
  isWalk := hC.isWalk.reverse
  edge_nodup := by simpa using hC.edge_nodup
  nonempty := by simp [hC.nonempty]
  isClosed := by simp [hC.isClosed]
  nodup := by simp [hC.dropLast_isPath.nodup]

lemma IsCycle.isCycle_of_ge (h : H.IsCycle w) (hle : H ≤ G) : G.IsCycle w where
  isWalk := h.isWalk.of_le hle
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed
  nodup := h.nodup

lemma IsCycle.isCycle_of_le (h : G.IsCycle w) (hle : H ≤ G) (hE : w.E ⊆ H.E) :
    H.IsCycle w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE h.nonempty
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed
  nodup := h.nodup

lemma IsCycle.eq_loop_of_inc₂_self (h : G.IsCycle C) (hC : C.Inc₂ e x x) :
    C = cons x e (nil x) := by
  cases C with
  | nil u => simp at hC
  | cons u f w =>
    have hnd : w.vx.Nodup := by simpa using h.tail_isPath.nodup
    rw [inc₂_iff_dInc, or_self, dInc_cons_iff] at hC
    obtain rfl : u = w.last := by simpa using h.isClosed
    obtain ⟨rfl, rfl, hu⟩ | h' := hC
    · cases w with simp_all
    rw [List.nodup_iff_sublist] at hnd
    exact False.elim <| hnd x h'.sublist

lemma IsCycle.ne_of_inc₂ (hC : G.IsCycle C) (hnt : C.Nontrivial) (hinc : C.Inc₂ e x y) : x ≠ y := by
  rintro rfl
  obtain ⟨x, e, rfl⟩ := hC.eq_loop_of_inc₂_self hinc
  simp at hnt

lemma IsCycle.length_eq_one_iff (h : G.IsCycle C) : C.length = 1 ↔ ∃ x e, C = cons x e (nil x) := by
  cases C with
  | nil => simp
  | cons u e w =>
    suffices w.Nil → w = nil u by simpa +contextual [iff_def]
    rw [show u = w.last from h.isClosed]
    exact Nil.eq_nil_last

lemma IsCycle.length_eq_two_iff (h : G.IsCycle C) :
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



lemma IsCycle.exists_isPath (hC : G.IsCycle C) (hnt : C.Nontrivial) : ∃ P u e f,
    G.IsPath P ∧ u ∉ P ∧ e ∉ P.edge ∧ f ∉ P.edge ∧ e ≠ f ∧ C = cons u e (P.concat f u) := by
  refine ⟨C.tail.dropLast, C.first, hC.nonempty.firstEdge, hC.nonempty.lastEdge,
    hC.tail_dropLast_isPath, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dropLast_first, hnt.tail_dropLast]
    exact first_not_mem_tail_of_nodup hC.dropLast_isPath.nodup hnt.dropLast_nonempty
  · refine mt (fun h ↦ ?_) (hC.nonempty.firstEdge_not_mem_tail hC.edge_nodup)
    exact List.IsPrefix.mem h <| by simpa using List.dropLast_prefix C.tail.edge
  · refine mt (fun h ↦ ?_) (hC.nonempty.lastEdge_not_mem_dropLast hC.edge_nodup)
    refine List.IsSuffix.mem h ?_
    simp only [dropLast_edge, tail_edge, ← List.tail_dropLast]
    exact List.tail_suffix C.edge.dropLast
  · refine mt (fun h_eq ↦ ?_) <| hC.nonempty.firstEdge_not_mem_tail hC.edge_nodup
    rw [h_eq, ← hnt.tail_lastEdge]
    exact (Nontrivial.tail_nonempty hnt).lastEdge_mem
  cases C with
  | nil => simp at hnt
  | cons u e w =>
    have hw : w.Nonempty := hnt.tail_nonempty
    simpa [show u = w.last from hC.isClosed, hw.lastEdge_cons] using hw.concat_dropLast.symm

lemma IsCycle.loop_or_nontrivial (hC : G.IsCycle C) :
    (∃ x e, C = cons x e (nil x)) ∨ C.Nontrivial := by
  cases hC.nonempty with
  | cons x e w => cases w with | nil u => simp [show x = u from hC.isClosed] | cons => simp

lemma IsCycle.toGraph_vxDelete_first_eq (hC : G.IsCycle C) (hnt : C.Nontrivial) :
      C.toGraph.vxDelete {C.first} = C.tail.dropLast.toGraph := by
    obtain ⟨P, u, e, f, hP, huP, heP, hfP, hef, rfl⟩ := hC.exists_isPath hnt
    refine Graph.ext (by simpa) fun g x y ↦ ?_
    have h1 : P.Inc₂ g x y → x ∈ P := fun h ↦ h.vx_mem_left
    have h2 : P.Inc₂ g x y → y ∈ P := fun h ↦ h.vx_mem_right
    simp only [vxDelete_inc₂, hC.isWalk.wellFormed.toGraph_inc₂, inc₂_cons_iff',
      concat_first, inc₂_concat_iff, tail_cons, dropLast_concat, hP.isWalk.wellFormed.toGraph_inc₂]
    aesop






  -- refine ⟨fun h ↦ ?_, ?_⟩
  -- · sorry
  -- rintro ⟨x, e, ?_⟩



-- lemma IsCycle.rotate (hC : G.IsCycle C) (n : ℕ) : G.IsCycle (C.rotate n) where
--   isClosed := hC.isClosed.rotate n
--   isTrail := {
--     isWalk := hC.isTrail.isWalk.rotate
--     edge_nodup := _
--   }
--   nodup := _





end Graph
