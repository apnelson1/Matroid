import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Qq
-- TODO: remember to remove this Loogle import at the end of the project
import Loogle.Find

import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.Graph.Independent
import Matroid.Graph.Tree
import Matroid.Graph.Walk.Cycle
import Matroid.ForMathlib.Minimal

open Qq Lean Meta Elab Tactic
open WList Set

section NonGraphThings

variable {α β : Type*} {P P₀ P₁ w w₁ w₂ p C : WList α β} {a b x y u v : α} {e f : β}

namespace WList

@[simp]
lemma suffixFromVertex_from_first_eq [DecidableEq α] (w : WList α β) :
    w.suffixFromVertex w.first = w := by
  induction w with (simp_all [suffixFromVertex])

lemma suffixFromVertex_from_second_eq [DecidableEq α] (e) (hx : x ≠ w.first) :
    (cons x e w).suffixFromVertex w.first = w := by
  simp only [suffixFromVertex, suffixFrom_cons, hx, ↓reduceIte]
  exact suffixFromVertex_from_first_eq w

@[simp]
lemma suffixFromVertex_nil [DecidableEq α] : (nil (β := β) u).suffixFromVertex x = nil u := by
  simp [suffixFromVertex]

lemma suffixFromVertex_cons_or [DecidableEq α] (u e) (w : WList α β) (x) :
    (u = x ∧ (cons u e w).suffixFromVertex x = cons u e w) ∨
    (u ≠ x ∧ (cons u e w).suffixFromVertex x = w.suffixFromVertex x) := by
  obtain (h|h) := Classical.em (u = x) <;> simp_all [suffixFromVertex]

lemma IsSublist.mem_edge (h : w₁.IsSublist w₂) (he : e ∈ w₁.edge) : e ∈ w₂.edge :=
  h.edgeSet_subset he

lemma IsSuffix.mem_edge (h : w₁.IsSuffix w₂) (he : e ∈ w₁.edge) : e ∈ w₂.edge :=
  h.isSublist.mem_edge he

lemma IsPrefix.mem_edge (h : w₁.IsPrefix w₂) (he : e ∈ w₁.edge) : e ∈ w₂.edge :=
  h.isSublist.mem_edge he

-- in a WList with no repeated edges, each edge is part of exactly one DInc triplet
lemma dInc_iff_eq_of_dInc_of_edge_nodup (hw : w.edge.Nodup) (he : w.DInc e u v) :
    w.DInc e x y ↔ x = u ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil => simp_all
  | cons z f w IH =>
    simp at hw h he
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨rfl, he, rfl⟩ | he := he; try tauto
      exact hw.1 he.edge_mem |>.elim
    obtain ⟨rfl, rfl, rfl⟩ | he := he
    · exact hw.1 h.edge_mem |>.elim
    apply IH <;> first | assumption | tauto

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_left (hw : w.vertex.Nodup) (hu : w.DInc e u v) :
    w.DInc f u y ↔ f = e ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil _ => simp_all
  | cons u' f' w IH =>
    simp_all only [cons_vertex, List.nodup_cons, mem_vertex, dInc_cons_iff, forall_const]
    obtain ⟨rfl, rfl, rfl⟩ | h := h <;> obtain ⟨hu, rfl, rfl⟩ | hu := hu
    · tauto
    · exact hw.1 hu.left_mem |>.elim
    · exact hw.1 (hu ▸ h.left_mem) |>.elim
    apply IH <;> assumption

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_right (hw : w.vertex.Nodup) (hv : w.DInc e u v) :
    w.DInc f x v ↔ f = e ∧ x = u := by
  generalize hw_def' : w.reverse = w'
  have hw' : w'.vertex.Nodup := by rwa [← hw_def', reverse_vertex, List.nodup_reverse]
  have hv' : w'.DInc e v u := by simpa [← hw_def']
  have := dInc_iff_eq_of_dInc_of_vertex_nodup_left (f := f) (v := u) (y := x) hw' hv'
  rwa [← hw_def', dInc_reverse_iff] at this

lemma exists_left_edge (hyw : y ∈ w) (hy : y ≠ w.first) : ∃ e x, w.DInc e x y := by
  induction w generalizing y with simp_all
  | cons u e w IH =>
    obtain (rfl | hne) := eq_or_ne y w.first
    · use e, u
      tauto
    · obtain ⟨f, x, h⟩ := IH hyw hne
      use f, x, Or.inr h

lemma exists_right_edge (hxw : x ∈ w) (hx : x ≠ w.last) : ∃ e y, w.DInc e x y := by
  generalize hw'_def : w.reverse = w'; symm at hw'_def
  have hx' : x ≠ w'.first := by simp_all
  have hxw' : x ∈ w' := by simp_all
  obtain ⟨e, y, h⟩ := exists_left_edge hxw' hx'
  use e, y
  simp_all

--From main

lemma Cycle_conc_index [DecidableEq α] (huv : v ≠ u) (hCP : v ∈ cons u e (P.concat f u)) :
    v ∈ P ∧ (cons u e (P.concat f u)).idxOf v = P.idxOf v + 1 := by
  simp only [mem_cons_iff, mem_concat] at hCP
  obtain (rfl | h2 | rfl) := hCP
  · contradiction
  · exact ⟨h2, by simp [idxOf_cons_ne huv.symm, idxOf_concat_of_mem h2]⟩
  · contradiction

lemma prefixUntilVertex_edge [DecidableEq α] (w : WList α β) (x : α) :
    E(w.prefixUntilVertex x) ⊆ E(w) :=
  (prefixUntilVertex_isPrefix w x).isSublist.edgeSet_subset

lemma suffixFromVertex_edge [DecidableEq α] (w : WList α β) (x : α) :
    E(w.suffixFromVertex x) ⊆ E(w) :=
  (suffixFromVertex_isSuffix w x).isSublist.edgeSet_subset

lemma prefixUntilVertex_vertex [DecidableEq α] (w : WList α β) (x : α) :
    V(w.prefixUntilVertex x) ⊆ V(w) :=
  (prefixUntilVertex_isPrefix w x).isSublist.vertex_subset

lemma suffixFromVertex_vertex [DecidableEq α] (w : WList α β) (x : α) :
    V(w.suffixFromVertex x) ⊆ V(w) :=
  (suffixFromVertex_isSuffix w x).isSublist.vertex_subset

lemma prefixUntilVertex_index [DecidableEq α] (hx : x ∈ w) (hle : w.idxOf y ≤ w.idxOf x) :
    w.idxOf y = (w.prefixUntilVertex x).idxOf y := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · obtain rfl | hxy := eq_or_ne x y
    · simp only [idxOf_cons_self]
      have h1 : ((cons x e w).prefixUntilVertex x).first = x :=
        prefixUntilVertex_first (cons x e w) x
      nth_rw 3 [←h1]
      exact (idxOf_first ((cons x e w).prefixUntilVertex x)).symm
    · simp only [idxOf_cons_self, nonpos_iff_eq_zero, idxOf_cons_ne hxy] at hle
      omega
  simp_all only [prefixUntilVertex, mem_cons_iff, false_or, idxOf_cons_ne hu.symm, ne_eq,
    prefixUntil_cons, hu.symm, ↓reduceIte, forall_const]
  obtain rfl | huy := eq_or_ne y u
  · simp
  simp_all [idxOf_cons_ne huy.symm]

lemma prefixUntilVertex_Nil [DecidableEq α] (w : WList α β) (x : α) :
    Nil ((cons x e w).prefixUntilVertex x) :=
  length_eq_zero.mp (by simp [prefixUntilVertex_length, idxOf_cons_self])

lemma prefixUntilVertex_nil [DecidableEq α] (w : WList α β) (x : α) :
    (cons x e w).prefixUntilVertex x = .nil x := by
  refine (prefixUntilVertex_Nil w x).eq_nil_of_mem ?_
  convert first_mem
  simp

lemma prefixUntilVertex_index_iff [DecidableEq α] (hx : x ∈ w) (hy : y ∈ w) :
    y ∈ (w.prefixUntilVertex x) ↔  w.idxOf y ≤ w.idxOf x := by
  refine ⟨fun hyP ↦ ?_, fun hle ↦ ?_⟩
  · induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
    obtain rfl | hu := eq_or_ne x u
    · rw [prefixUntilVertex_nil w x, mem_nil_iff] at hyP
      rw [hyP]
    simp only [mem_cons_iff, hu, false_or] at hx
    obtain rfl | huy := eq_or_ne y u
    · simp
    simp only [mem_cons_iff, huy, false_or] at hy
    simp only [prefixUntilVertex_cons_of_ne w hu.symm, mem_cons_iff, huy, false_or] at hyP
    simp [idxOf_cons u e w, huy.symm, hu.symm, ih hx hy hyP]
  by_contra hc
  have h1 := idxOf_notMem hc
  rw [prefixUntilVertex_length hx, ←prefixUntilVertex_index hx hle] at h1
  linarith

lemma idx_Of_tail [DecidableEq α] (hw : w.Nonempty) (haf : w.first ≠ a) (ha : a ∈ w) :
    (w.tail).idxOf a + 1 = w.idxOf a := by
  induction w with
  | nil w => simp [(mem_nil_iff.1 ha).symm] at haf
  | cons u e w ih =>
    obtain rfl | hu := eq_or_ne a u
    · simp at haf
    simp [hu.symm]

lemma idx_Of_dropLast [DecidableEq α] (hw : w.Nonempty) (ha : a ∈ w) :
    (w.dropLast).idxOf a = w.idxOf a := by
  induction w with
  | nil w => rfl
  | cons u e w ih =>
    obtain ⟨x, rfl⟩ | hwN := exists_eq_nil_or_nonempty w
    · obtain rfl | hu := eq_or_ne u a
      · simp
      obtain rfl := by simpa [hu.symm] using ha
      simp [hu]
    rw [hwN.dropLast_cons]
    obtain rfl | hu := eq_or_ne u a
    · simp_all
    simp_all [hu.symm]

lemma rotate_one (hCne : C.Nonempty) : ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  use hCne.firstEdge
  nth_rw 1 [Eq.symm (Nonempty.cons_tail hCne)]
  rw [cons_rotate_one]

end WList

namespace Graph

variable {G H : Graph α β} {n : ℕ}

lemma Prefix_Suffix_int [DecidableEq α] (hP : G.IsPath P) (hp : b ∈ P.prefixUntilVertex x)
    (hs : b ∈ P.suffixFromVertex x) (hx : x ∈ P) : x = b := by
  rw [← prefixUntilVertex_append_suffixFromVertex P x] at hP
  have hPf : x = (P.suffixFromVertex x).first := (suffixFromVertex_first hx).symm
  nth_rw 1 [(prefixUntilVertex_last hx).symm] at hPf
  have hint : b ∈ V(P.prefixUntilVertex x) ∩ V(P.suffixFromVertex x) := mem_inter hp hs
  rw [hP.inter_eq_singleton_of_append hPf] at hint
  simp only [prefixUntilVertex_last hx, mem_singleton_iff] at hint
  exact hint.symm

lemma IsCycle.rotate_one (hC : G.IsCycle C) :
    ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  use hC.nonempty.firstEdge
  nth_rw 1 [Eq.symm (Nonempty.cons_tail hC.nonempty)]
  rw [cons_rotate_one]

lemma IsCycle.idxOf_rotate_one [DecidableEq α] (hC : G.IsCycle C) (hnt : C.Nonempty)
    (h1 : C.first ≠ a) (ha : a ∈ C) : (C.rotate 1).idxOf a + 1 = C.idxOf a := by
  obtain ⟨e, h⟩ := hC.rotate_one
  have hat : a ∈ C.tail := by
    obtain hfirst | h1 := eq_first_or_mem_tail ha
    · by_contra
      exact h1 hfirst.symm
    exact h1
  have := idx_Of_tail hnt h1 ha
  rwa [h, idxOf_concat_of_mem hat]

lemma IsCycle.idxOf_rotate_first [DecidableEq α] (hC : G.IsCycle C) (hn : n < C.length)
    (hle : n + 1 ≤ C.idxOf a ) : (C.rotate n).first ≠ a := by
  rw [C.rotate_first n (Nat.le_of_succ_le hn)]
  by_contra hc
  rw [← hc, idxOf_get hC hn] at hle
  linarith

lemma IsCycle.idxOf_rotate_n_le [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C)
    (hle : n ≤ C.idxOf a) : (C.rotate n).idxOf a + n = C.idxOf a := by
  have hn := hle.trans_lt <| hC.isClosed.idxOf_lt_length ha hC.nonempty
  induction n with | zero => simp_all | succ n hi =>
  rw [← rotate_rotate C n 1]
  have han : (C.rotate n).first ≠ a := by
    rw [rotate_first C n (by linarith)]
    by_contra hc
    rw [← hc, idxOf_get hC (Nat.lt_of_succ_lt hn)] at hle
    linarith
  have hf := (rotate hC n).idxOf_rotate_one ((rotate_nonempty_iff n).mpr hC.nonempty) han
    (hC.isClosed.mem_rotate.2 ha)
  have := hi (by linarith) (by linarith)
  linarith

lemma IsCycle.idxOf_rotate_one_first' [DecidableEq α] (hC : G.IsCycle C) :
    (C.rotate 1).idxOf C.first + 1 = C.length := by
  obtain ⟨e, hrC⟩ := hC.rotate_one
  rw [hrC, idxOf_concat_of_mem, hC.isClosed.eq, ← tail_last, idxOf_last _ hC.nodup, tail_length,
    Nat.sub_add_cancel hC.nonempty.length_pos]
  rw [hC.isClosed.mem_tail_iff]
  exact first_mem

lemma IsCycle.idxOf_rotate_one_first [DecidableEq α] (hC : G.IsCycle C) (h1 : C.first = a)
    (ha : a ∈ C) : (C.rotate 1).idxOf a + 1 = C.length := by
  obtain ⟨e, hrC⟩ := hC.rotate_one
  have hft := h1 ▸ hC.isClosed.eq
  rw [hrC, idxOf_concat_of_mem (hC.isClosed.mem_tail_iff.2 ha), hft, (tail_last C).symm,
    idxOf_last C.tail (hC.nodup), tail_length]
  have := hC.nonempty.length_pos
  omega

lemma IsCycle.idxOf_rotate_untilfirst [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) :
    (C.rotate (C.idxOf a + 1)).idxOf a + 1 = C.length := by
  rw [← rotate_rotate C (C.idxOf a) 1, (hC.rotate (C.idxOf a)).idxOf_rotate_one_first
    (rotate_idxOf_first ha) (hC.isClosed.mem_rotate.mpr ha), length_rotate]

--@[simp]
lemma IsCycle.idxOf_rotate_idxOf [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) :
    (C.rotate (C.idxOf a)).idxOf a = 0 := by
  simpa using hC.idxOf_rotate_n_le ha le_rfl

lemma idxOf_eq [DecidableEq α] (hx : x ∈ w) (heq : w.idxOf x = w.idxOf y) : x = y := by
  have hy : y ∈ w := idxOf_le_length_iff_mem.mp (heq ▸ idxOf_le_length_iff_mem.mpr hx)
  rw [← get_idxOf w hx, ← get_idxOf w hy, heq]

--get_idxOf (w : WList α β) (hxw : x ∈ w) : w.get (w.idxOf x) = x := by
/-! #EXAMPLE of wlog tactic
-- example (M : Matroid α) (hconn : M.TutteConnected 17) : 100 < M.E.encard := by
--   -- we may assume that `M` has lower rank than corank, because the statement is self-dual
--   wlog hle : M.eRank ≤ M✶.eRank generalizing M with aux
--   · specialize aux M✶ (by simpa) ?_
--     · simp
--       exact (not_le.1 hle).le
--     simpa using aux
--   -- prove the theorem with an added assumption
-/

lemma IsCycle.idxOf_rotate_n [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) (hn : n < C.length)
    (hle : C.idxOf a < n) : (C.rotate n).idxOf a + n = C.length + C.idxOf a := by
  obtain ⟨x, rfl⟩ | hnt := exists_eq_nil_or_nonempty C
  · simp_all
  induction n with | zero => simp_all | succ n hi =>
  obtain han | hu := eq_or_ne (C.idxOf a) n
  · rw [← han]
    have hle' : C.idxOf a < C.length := by
      rw [han]
      exact Nat.lt_of_succ_lt hn
    have := hC.idxOf_rotate_untilfirst ha
    linarith
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
    linarith
  have ha' : a ∈ C.rotate n := (IsClosed.mem_rotate (hC.isClosed)).mpr ha
  have hf := (rotate hC n).idxOf_rotate_one ((rotate_nonempty_iff n).mpr hnt) hnf ha'
  linarith

lemma idxOf_Adj [DecidableEq α] (hw : G.IsTrail w) (ha : a ∈ w) (hb : b ∈ w)
    (he : w.idxOf b = w.idxOf a + 1) : G.Adj a b := by
  induction w with | nil w => simp_all | cons u e w ih =>
  simp_all only [cons_isTrail_iff, mem_cons_iff, forall_const]
  obtain rfl | hu := eq_or_ne a u
  · simp_all only [true_or, idxOf_cons_self, zero_add]
    obtain rfl | hbb := eq_or_ne a b
    · simp at he
    simp [idxOf_cons a e w, hbb] at he
    simp [hbb.symm] at hb
    have : b = w.first := by
      have h1 := w.get_idxOf hb
      rw[he ] at h1
      --have : w.first ∈ w := by exact first_mem
      have h2 := w.get_idxOf first_mem
      rw [idxOf_first w, h1] at h2
      exact h2
    rw [this]
    use e
    exact hw.2.1
  simp only [hu, false_or] at ha
  obtain rfl | hau := eq_or_ne b u
  simp_all
  simp [hau] at hb
  simp [idxOf_cons_ne hu.symm, idxOf_cons_ne hau.symm ] at he
  exact ih ha hb he

lemma IsCycle.idxOf_Adj_first [DecidableEq α] (hC : G.IsCycle C) (hab : a ≠ b) (ha : C.idxOf a = 0)
    (hb : C.idxOf b = C.length - 1) : G.Adj a b := by
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
    exact hab (idxOf_eq haC hb.symm) |>.elim
  obtain h1 | hle := le_or_gt C.length 1
  · rw [h1.antisymm (one_le_length_iff.mpr hnt), tsub_self, ← ha] at hb
    exact hab (idxOf_eq haC hb.symm) |>.elim
  have hn : C.idxOf b < C.length := by
    rw [hb]
    omega
  have hab : C.idxOf a < C.idxOf b := by
    rw [ha, hb]
    exact Nat.zero_lt_sub_of_lt hle
  have := hC.idxOf_rotate_idxOf hbC
  have hf := hC.idxOf_rotate_n haC hn hab
  rw [ha, ←this] at hf
  nth_rw 2 [hb] at hf
  have hlast : (C.rotate (C.idxOf b)).idxOf a  = (C.rotate (C.idxOf b)).idxOf b + 1 := by omega
  exact (idxOf_Adj ((hC.rotate (C.idxOf b)).isTrail) (hC.isClosed.mem_rotate.2 hbC)
    (hC.isClosed.mem_rotate.2 haC) hlast).symm

lemma IsCycle.idxOf_rotate [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) (hn : n < C.length) :
    ((C.rotate n).idxOf a + n) % C.length = C.idxOf a := by
  obtain ⟨x, rfl⟩ | hne := exists_eq_nil_or_nonempty C
  · simp_all
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  · rw [hC.idxOf_rotate_n_le ha hle]
    exact Nat.mod_eq_of_lt (hC.isClosed.idxOf_lt_length ha hne)
  rw [hC.idxOf_rotate_n ha hn hlt]
  simp only [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (hC.isClosed.idxOf_lt_length ha hne)

lemma IsCycle.idxOf_Adj_rotate [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) (hb : b ∈ C)
    (hn : n < C.length) : C.idxOf b = C.idxOf a + 1 ∨ (C.idxOf b = 0 ∧ C.idxOf a = C.length - 1)
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
  have hh : (C.rotate n).idxOf b + n = (C.rotate n).idxOf a + n + 1
      ∨ (C.rotate n).idxOf b + n = n ∧ (C.rotate n).idxOf a + n = C.length - 1 + n := by
    omega
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  rw [hC.idxOf_rotate_n_le ha hle] at hh
  · obtain hleb | hltb := le_or_gt n (C.idxOf b)
    · rw [hC.idxOf_rotate_n_le hb hleb] at hh
      obtain hgood | hf := hh
      · omega
      have := (hC.isClosed).idxOf_lt_length ha hne
      rw[hf.2] at this
      by_contra
      omega
    rw [hC.idxOf_rotate_n hb hn hltb] at hh
    have := (hC.isClosed).idxOf_lt_length ha hne
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
    have := (hC.isClosed).idxOf_lt_length hb hne
    omega
  rw [hC.idxOf_rotate_n ha hn hlt, hC.idxOf_rotate_n hb hn hltb] at hh
  omega

  lemma get_rotate (w : WList α β) {a b : ℕ} (hab : a + b ≤ w.length) :
    (w.rotate a).get b = w.get (a + b) := by
  induction w generalizing a b with simp_all
  | cons u e w IH =>
    sorry
