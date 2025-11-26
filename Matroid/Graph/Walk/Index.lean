import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Qq
-- TODO: remember to remove this Loogle import at the end of the project
import Loogle.Find

import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.Graph.Connected.Basic
import Matroid.Graph.Connected.Component
import Matroid.Graph.Connected.Separating
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Basic
import Matroid.Graph.Independent
import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Tree
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Walk.Path
import Matroid.Graph.WList.Defs
import Matroid.Graph.WList.Cycle
import Matroid.ForMathlib.Minimal

open Qq Lean Meta Elab Tactic
open WList Set

section NonGraphThings

variable {α β : Type*} {P₀ P₁ : WList α β} {e f : β}

namespace WList


variable {α β : Type*}  {P₀ P₁ w p : WList α β} {x y u v : α} {e f : β}

--This is in Oops in the main brand
lemma idxOf_concat_of_mem [DecidableEq α] (hx : x ∈ w) : (w.concat e y).idxOf x = w.idxOf x := by
  induction w with
  | nil u => simp_all
  | cons u f w ih =>
  rw [cons_concat]
  obtain rfl | hu := eq_or_ne x u
  · rw [idxOf_cons_self, idxOf_cons_self]
  rw[idxOf_cons_ne hu.symm, idxOf_cons_ne hu.symm ]
  simp_all

--This one is in WList Cycle
lemma IsClosed.idxOf_lt_length {C : WList α β} [DecidableEq α] (hC : C.IsClosed) (hx : x ∈ C)
    (hne : C.Nonempty) : C.idxOf x < C.length := by
  induction C using concat_induction with
  | nil u => simp at hne
  | @concat w f y ih =>
  · obtain rfl : y = w.first := by simpa using hC
    have hxw : x ∈ w := by
      obtain hxw | rfl := mem_concat.1 hx
      · assumption
      simp
    grw [idxOf_concat_of_mem hxw, concat_length, idxOf_mem_le hxw]
    exact Nat.lt_add_one w.length

lemma suffixFromVertex_from_first_eq
    [DecidableEq α]
    (w : WList α β) :
    w.suffixFromVertex w.first = w := by
  induction w with (simp_all [suffixFromVertex])

lemma suffixFromVertex_from_second_eq
    [DecidableEq α]
    (w : WList α β) (e) (hx : x ≠ w.first) :
    (cons x e w).suffixFromVertex w.first = w := by
  simp_all [suffixFromVertex]
  exact suffixFromVertex_from_first_eq w

lemma suffixFromVertex_nil
    [DecidableEq α]
    {u x : α} : (nil (β := β) u).suffixFromVertex x = nil u := by
  simp [suffixFromVertex]

lemma suffixFromVertex_cons_or
    [DecidableEq α]
    (u e) (w : WList α β) (x) :
    (u = x ∧ (cons u e w).suffixFromVertex x = cons u e w) ∨
    (u ≠ x ∧ (cons u e w).suffixFromVertex x = w.suffixFromVertex x) := by
  obtain (h|h) := Classical.em (u = x) <;>
    simp_all [suffixFromVertex]

lemma IsSublist.mem_edge
    {w₁ w₂ : WList α β}
    (h : w₁.IsSublist w₂) (he : e ∈ w₁.edge) :
    e ∈ w₂.edge := by
  have := h.edgeSet_subset
  exact this he

lemma IsSuffix.mem_edge
    {w₁ w₂ : WList α β}
    (h : w₁.IsSuffix w₂) (he : e ∈ w₁.edge) :
    e ∈ w₂.edge := by
  refine IsSublist.mem_edge ?_ he
  exact h.isSublist

lemma IsPrefix.mem_edge
    {w₁ w₂ : WList α β}
    (h : w₁.IsPrefix w₂) (he : e ∈ w₁.edge) :
    e ∈ w₂.edge := by
  refine IsSublist.mem_edge ?_ he
  exact h.isSublist

-- in a WList with no repeated edges, each edge is part of exactly one DInc triplet
lemma dInc_iff_eq_of_dInc_of_edge_nodup {w : WList α β} (hw : w.edge.Nodup) (he : w.DInc e u v) :
    w.DInc e x y ↔ x = u ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil => simp_all
  | cons z f w IH =>
    simp at hw h he
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨rfl, he, rfl⟩ | he := he; try tauto
      exfalso; apply hw.1; apply he.edge_mem
    obtain ⟨rfl, rfl, rfl⟩ | he := he
    · exfalso; apply hw.1; apply h.edge_mem
    apply IH <;> first | assumption | tauto

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_left
    {w : WList α β} (hw : w.vertex.Nodup) (hu : w.DInc e u v) :
    w.DInc f u y ↔ f = e ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil _ => simp_all
  | cons u' f' w IH =>
    simp_all
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨hu, rfl, rfl⟩ | hu := hu; try tauto
      exfalso; apply hw.1; apply hu.left_mem
    obtain ⟨rfl, rfl, rfl⟩ | hu := hu
    · exfalso; apply hw.1; apply h.left_mem
    apply IH <;> assumption

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_right
    {w : WList α β} (hw : w.vertex.Nodup) (hv : w.DInc e u v) :
    w.DInc f x v ↔ f = e ∧ x = u := by
  generalize hw_def' : w.reverse = w'
  have hw' : w'.vertex.Nodup := by rwa [← hw_def', reverse_vertex, List.nodup_reverse]
  have hv' : w'.DInc e v u := by simpa [← hw_def']
  have := dInc_iff_eq_of_dInc_of_vertex_nodup_left (f := f) (v := u) (y := x) hw' hv'
  rwa [← hw_def', dInc_reverse_iff] at this

lemma exists_left_edge
    (w : WList α β) {y : α} (hyw : y ∈ w) (hy : y ≠ w.first) :
    ∃ e x, w.DInc e x y := by
  induction w generalizing y with simp_all
  | cons u e w IH =>
    obtain (hne|heq) := Classical.decEq _ y w.first
    · obtain ⟨f, x, h⟩ := IH hyw hne
      use f, x
      right; assumption
    use e, u
    left; tauto

lemma exists_right_edge
    (w : WList α β) {x : α} (hxw : x ∈ w) (hx : x ≠ w.last) :
    ∃ e y, w.DInc e x y := by
  generalize hw'_def : w.reverse = w'; symm at hw'_def
  have hx' : x ≠ w'.first := by simp_all
  have hxw' : x ∈ w' := by simp_all
  obtain ⟨e, y, h⟩ := exists_left_edge w' hxw' hx'
  use e, y
  simp_all

--From main

lemma Cycle_conc_index [DecidableEq α]
    (huv : v ≠ u) {P : WList α β} (hCP : v ∈ cons u e (P.concat f u))
    : v ∈ P ∧ (cons u e (P.concat f u)).idxOf v = P.idxOf v + 1 := by
  simp at hCP
  obtain (rfl | h2 | rfl) := hCP
  · exact False.elim (huv rfl)
  · refine ⟨ h2, ?_ ⟩
    rw [idxOf_cons_ne huv.symm e (P.concat f u) ]
    simp
    rwa [idxOf_concat_of_mem]
  · exact False.elim (huv rfl)

lemma prefixUntilVertex_edge [DecidableEq α] (w : WList α β) (x : α) :
  E(w.prefixUntilVertex x) ⊆ E(w) := by
exact (prefixUntilVertex_isPrefix w x).isSublist.edgeSet_subset

lemma suffixFromVertex_edge [DecidableEq α] (w : WList α β) (x : α) :
  E(w.suffixFromVertex x) ⊆ E(w) := by
exact (suffixFromVertex_isSuffix w x).isSublist.edgeSet_subset

lemma prefixUntilVertex_vertex [DecidableEq α] (w : WList α β) (x : α) :
  V(w.prefixUntilVertex x) ⊆ V(w) := by
exact (prefixUntilVertex_isPrefix w x).isSublist.vertex_subset

lemma suffixFromVertex_vertex [DecidableEq α] (w : WList α β) (x : α) :
  V(w.suffixFromVertex x) ⊆ V(w) := by
exact (suffixFromVertex_isSuffix w x).isSublist.vertex_subset

lemma prefixUntilVertex_index [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w)
    (hle : w.idxOf y ≤ w.idxOf x ) :
    w.idxOf y = (w.prefixUntilVertex x).idxOf y := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  simp at hx
  obtain rfl | hu := eq_or_ne x u
  · obtain rfl | hxy := eq_or_ne x y
    simp
    have h1 : (cons x e w).first = x := by exact rfl
    rw [←prefixUntilVertex_first (cons x e w) x] at h1
    have h := idxOf_first ((cons x e w).prefixUntilVertex x)
    nth_rw 3 [←h1]
    exact id (Eq.symm h)
    · simp at hle
      rw [hle]
      rw [idxOf_cons_ne hxy] at hle
      by_contra!
      have hcon : 0 ≤ w.idxOf y := by exact Nat.zero_le (w.idxOf y)
      rw [←hle ] at hcon
      linarith
  simp_all [prefixUntilVertex, hu.symm, idxOf_cons_ne hu.symm]
  obtain rfl | huy := eq_or_ne y u
  · simp
  simp_all [ idxOf_cons_ne huy.symm]

lemma prefixUntilVertex_Nil [DecidableEq α] (w : WList α β) (x : α) :
    Nil ((cons x e w).prefixUntilVertex x) := by
  refine length_eq_zero.mp ?_
  rw [prefixUntilVertex_length (w := cons x e w)]
  exact idxOf_cons_self x e w
  simp

lemma prefixUntilVertex_nil [DecidableEq α] (w : WList α β) (x : α) :
    (cons x e w).prefixUntilVertex x = .nil x := by
  refine Nil.eq_nil_of_mem (prefixUntilVertex_Nil w x) ?_
  have h1 : x = ((cons x e w).prefixUntilVertex x).first := by
    rw [prefixUntilVertex_first (cons x e w) x]
    exact rfl
  have h2 : ((cons x e w).prefixUntilVertex x).first ∈ (cons x e w).prefixUntilVertex x := by
    exact first_mem
  rwa [←h1 ] at h2

lemma prefixUntilVertex_index_iff [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w) (hy : y ∈ w)
    : y ∈ (w.prefixUntilVertex x) ↔  w.idxOf y ≤ w.idxOf x := by
refine ⟨ ?_, ?_ ⟩
· intro hyP
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp
    rw [prefixUntilVertex_nil w x] at hyP
    simp at hyP
    rw[hyP]
    simp
  simp [hu] at hx
  obtain rfl | huy := eq_or_ne y u
  · simp
  simp [huy] at hy
  simp [idxOf_cons u e w, huy.symm, hu.symm]
  rw [prefixUntilVertex_cons_of_ne w hu.symm] at hyP
  simp only [mem_cons_iff, huy, false_or] at hyP
  exact ih hx hy hyP
intro hle
by_contra hc
have h1 := idxOf_notMem hc
rw [prefixUntilVertex_length hx, ←prefixUntilVertex_index w x hx hle] at h1
linarith

lemma idx_Of_tail [DecidableEq α] {w : WList α β} {a : α} (hw : w.Nonempty) (haf : w.first ≠ a)
    (ha : a ∈ w) :
    (w.tail).idxOf a + 1 = w.idxOf a := by
  induction w with
  | nil w =>
  simp
  rw [nil_first] at haf
  exact haf (mem_nil_iff.1 ha).symm
  | cons u e w ih =>
  simp
  obtain rfl | hu := eq_or_ne a u
  simp
  exact haf rfl
  simp [hu.symm]

lemma idx_Of_dropLast [DecidableEq α] {w : WList α β} {a : α} (hw : w.Nonempty) (ha : a ∈ w) :
    (w.dropLast).idxOf a = w.idxOf a := by
  induction w with
  | nil w => rfl
  | cons u e w ih =>
  obtain he | hwN := exists_eq_nil_or_nonempty w
  obtain ⟨x, hx ⟩ := he
  rw [hx]
  obtain rfl | hu := eq_or_ne a u
  simp
  simp [hu.symm]
  simp [hu, hx] at ha
  exact id (Eq.symm ha)
  rw [hwN.dropLast_cons]
  obtain rfl | hu := eq_or_ne a u
  simp_all
  simp [hu.symm ]
  simp_all

lemma rotate_one {C : WList α β} (hCne : C.Nonempty)
    : ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  set e := hCne.firstEdge
  use e
  have hCn : C = cons C.first e C.tail := by
    exact Eq.symm (Nonempty.cons_tail hCne)
  nth_rw 1 [hCn]
  rw [cons_rotate_one ]

end WList

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {P₀ P₁ w p C : WList α β}

lemma Prefix_Sufix_int [DecidableEq α] {P : WList α β} {x b : α} (hP : G.IsPath P)
    (hp : b ∈ P.prefixUntilVertex x)
    (hs : b ∈ P.suffixFromVertex x) (hx : x ∈ P) : x = b := by
  rw[←prefixUntilVertex_append_suffixFromVertex P x] at hP
  have hPf : x = (P.suffixFromVertex x).first := by exact (suffixFromVertex_first hx).symm
  nth_rw 1 [(prefixUntilVertex_last hx).symm] at hPf
  have := hP.inter_eq_singleton_of_append hPf
  have hint : b ∈  V(P.prefixUntilVertex x) ∩ V(P.suffixFromVertex x) := by exact mem_inter hp hs
  rw[hP.inter_eq_singleton_of_append hPf ] at hint
  simp at hint
  rw[← ((prefixUntilVertex_last hx).symm)] at hint
  exact id (Eq.symm hint)

lemma IsCycle.rotate_one {C : WList α β} (hC : G.IsCycle C)
    : ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  set e := hC.nonempty.firstEdge
  use e
  have hCn : C = cons C.first e C.tail := by
    exact Eq.symm (Nonempty.cons_tail hC.nonempty)
  nth_rw 1 [hCn]
  rw [cons_rotate_one ]

lemma IsCycle.idxOf_rotate_one [DecidableEq α] {a  : α} {C : WList α β} (hC : G.IsCycle C)
    (hnt : C.Nonempty) (h1 : C.first ≠ a ) (ha : a ∈ C) :
    (C.rotate 1).idxOf a + 1 = C.idxOf a := by
  obtain ⟨e, h ⟩ :=  hC.rotate_one
  have hat : a ∈ C.tail := by
    obtain hfirst | h1 := eq_first_or_mem_tail ha
    · by_contra
      exact h1 (id (Eq.symm hfirst))
    exact h1
  have := idx_Of_tail hnt h1 ha
  rwa [h, idxOf_concat_of_mem hat]

lemma IsCycle.idxOf_rotate_first [DecidableEq α] {a  : α} {n : ℕ} {C : WList α β} (hC : G.IsCycle C)
    (hn : n < C.length) (hle : n + 1 ≤ C.idxOf a ) : (C.rotate n).first ≠ a := by
  rw [rotate_first C n (Nat.le_of_succ_le hn) ]
  by_contra hc
  rw[←hc] at hle
  rw [idxOf_get hC hn ] at hle
  linarith

lemma IsCycle.idxOf_rotate_n_le [DecidableEq α] {a  : α} {n : ℕ} {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) (hle : n ≤ C.idxOf a) : (C.rotate n).idxOf a + n  = C.idxOf a := by
  have hn := hle.trans_lt <| hC.isClosed.idxOf_lt_length ha hC.nonempty
  induction n with
  | zero =>
  simp_all
  | succ n hi =>
  rw[←rotate_rotate C n 1]
  have hlen : n ≤ C.length := by
    linarith
  have hle' : n ≤ C.idxOf a := by
    linarith
  have han : (C.rotate n).first ≠ a := by
    rw [rotate_first C n hlen ]
    by_contra hc
    rw[←hc, idxOf_get hC (Nat.lt_of_succ_lt hn) ] at hle
    linarith
  have hf := (rotate hC n ).idxOf_rotate_one ((rotate_nonempty_iff n).mpr hC.nonempty )
      han (((hC.isClosed).mem_rotate).2 ha)
  have := hi hle' (by linarith)
  linarith


lemma IsCycle.idxOf_rotate_one_first' [DecidableEq α] {C : WList α β} (hC : G.IsCycle C) :
    (C.rotate 1).idxOf C.first + 1 = C.length := by
  obtain ⟨e, hrC⟩ := hC.rotate_one
  rw [hrC, idxOf_concat_of_mem, hC.isClosed.eq, ← tail_last, idxOf_last _ hC.nodup, tail_length,
    Nat.sub_add_cancel hC.nonempty.length_pos]
  rw [hC.isClosed.mem_tail_iff]
  exact first_mem

lemma IsCycle.idxOf_rotate_one_first [DecidableEq α] {a  : α} {C : WList α β} (hC : G.IsCycle C)
    (h1 : C.first = a) (ha : a ∈ C) : (C.rotate 1).idxOf a + 1 = C.length := by
  obtain ⟨e, hrC ⟩ := hC.rotate_one
  have hft : C.first = C.last := (hC.isClosed).eq
  rw [h1] at hft
  rw [hrC, idxOf_concat_of_mem ((hC.isClosed).mem_tail_iff.2 ha ), hft, (tail_last C).symm ,
  idxOf_last C.tail (hC.nodup), tail_length]
  have := hC.nonempty.length_pos
  omega

lemma IsCycle.idxOf_rotate_untilfirst [DecidableEq α] {a  : α} {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) : (C.rotate (C.idxOf a + 1)).idxOf a + 1 = C.length := by
  have hfirst : a = (C.rotate (C.idxOf a)).first := by
    exact Eq.symm (rotate_idxOf_first ha)
  have ha' : a ∈ (C.rotate (C.idxOf a)) := by
    refine (IsClosed.mem_rotate (hC.isClosed)).mpr ha
  rw[←rotate_rotate C (C.idxOf a) 1, (rotate hC (C.idxOf a)).idxOf_rotate_one_first
    (Eq.symm (rotate_idxOf_first ha)).symm ha' ]
  simp

--@[simp]
lemma IsCycle.idxOf_rotate_idxOf [DecidableEq α] {a  : α} {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) : (C.rotate (C.idxOf a)).idxOf a  = 0 := by
  have := hC.idxOf_rotate_n_le ha (Nat.le_refl (C.idxOf a))
  simp at this
  exact this

lemma idxOf_eq [DecidableEq α] (w : WList α β) (hx : x ∈ w) (heq : w.idxOf x = w.idxOf y)
    : x = y := by
  have hy : y ∈ w := by
    have h := idxOf_le_length_iff_mem.2 hx
    rw[heq] at h
    exact idxOf_le_length_iff_mem.1 h
  rw[←get_idxOf w hx, ←get_idxOf w hy, heq ]

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

lemma IsCycle.idxOf_rotate_n [DecidableEq α] {a  : α} {n : ℕ} {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) (hn : n < C.length)
    (hle : C.idxOf a < n ) : (C.rotate n).idxOf a + n = C.length + C.idxOf a := by

  obtain he | hnt := exists_eq_nil_or_nonempty C
  · obtain ⟨x, hx ⟩ := he
    rw[hx]
    simp_all
  induction n with
  | zero =>
  simp_all
  | succ n hi =>
  obtain han | hu := eq_or_ne (C.idxOf a) n
  · rw [←han]
    have hle' : C.idxOf a < C.length := by
      rw[han]
      exact Nat.lt_of_succ_lt hn
    have := hC.idxOf_rotate_untilfirst ha
    linarith
  rw[←rotate_rotate C n 1]
  have hg : n < C.length := by exact Nat.lt_of_succ_lt hn
  have hii := hi hg (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hle ) hu )
  have hnf : (C.rotate n).first ≠ a := by
    by_contra hc
    have hia : (C.rotate n).idxOf a = 0 := by
      rw[←hc]
      exact idxOf_first (C.rotate n)
    rw [hia] at hii
    simp at hii
    rw [hii] at hg
    linarith
  have ha' : a ∈ C.rotate n := by
    refine (IsClosed.mem_rotate (hC.isClosed)).mpr ha
  have hf := (rotate hC n ).idxOf_rotate_one ((rotate_nonempty_iff n).mpr hnt) hnf ha'
  linarith

lemma idxOf_Adj [DecidableEq α] {a b : α} {w : WList α β} (hw : G.IsTrail w)
    (ha : a ∈ w) (hb : b ∈ w) (he : w.idxOf b = w.idxOf a + 1) : G.Adj a b := by
  induction w with
  | nil w =>
  simp_all
  | cons u e w ih =>
  simp_all
  obtain rfl | hu := eq_or_ne a u
  · simp_all
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
    rw[this]
    use e
    exact hw.2.1
  simp [hu] at ha
  obtain rfl | hau := eq_or_ne b u
  simp_all
  simp [hau] at hb
  simp [idxOf_cons_ne hu.symm, idxOf_cons_ne hau.symm ] at he
  exact ih ha hb he

lemma IsCycle.idxOf_Adj_first [DecidableEq α] {a b : α} {C : WList α β} (hC : G.IsCycle C)
    (hab : a ≠ b)
    (ha : C.idxOf a = 0 ) (hb : C.idxOf b = C.length - 1): G.Adj a b := by

  have haC : a ∈ C := by
    have hlea : C.idxOf a ≤ C.length := by
      rw[ha]
      exact Nat.zero_le C.length
    exact idxOf_le_length_iff_mem.1 hlea
  have hbC : b ∈ C := by
    have hle : C.idxOf b ≤ C.length := by
      rw[hb]
      omega
    exact idxOf_le_length_iff_mem.1 hle
  obtain h0 | hnt := DecidableNonempty C
  · simp at h0
    by_contra
    have := length_eq_zero.2 h0
    rw[this] at hb
    simp at hb
    rw[←ha ] at hb
    exact hab (idxOf_eq C haC hb.symm)
  obtain h1 | hle := le_or_gt C.length 1
  · rw[Eq.symm (Nat.le_antisymm (one_le_length_iff.mpr hnt ) h1)] at hb
    simp at hb
    rw[← ha] at hb
    by_contra
    exact hab (idxOf_eq C haC hb.symm)
  have hn : C.idxOf b < C.length := by
    rw[hb]
    omega
  have hab : C.idxOf a < C.idxOf b := by
    rw[ha,hb]
    refine Nat.zero_lt_sub_of_lt hle
  have := hC.idxOf_rotate_idxOf hbC
  have hf := hC.idxOf_rotate_n haC hn hab
  rw[ha, ←this] at hf
  nth_rw 2 [hb] at hf
  have hlast : (C.rotate (C.idxOf b)).idxOf a  = (C.rotate (C.idxOf b)).idxOf b + 1 := by omega
  exact (idxOf_Adj ((hC.rotate (C.idxOf b)).isTrail) (hC.isClosed.mem_rotate.2 hbC )
    (hC.isClosed.mem_rotate.2 haC) hlast).symm

lemma IsCycle.idxOf_rotate [DecidableEq α] {a  : α} {n : ℕ} {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) (hn : n < C.length)
    : ((C.rotate n).idxOf a + n) % C.length = C.idxOf a := by
  obtain he | hne := exists_eq_nil_or_nonempty C
  · obtain ⟨x, hx ⟩ := he
    rw[hx]
    simp_all
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  · rw [hC.idxOf_rotate_n_le ha hle ]
    refine Nat.mod_eq_of_lt ?_
    exact (hC.isClosed).idxOf_lt_length ha hne
  rw [hC.idxOf_rotate_n ha hn hlt ]
  simp
  refine Nat.mod_eq_of_lt ?_
  exact (hC.isClosed).idxOf_lt_length ha hne

lemma IsCycle.idxOf_Adj_rotate [DecidableEq α] {a b : α} {n : ℕ } {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) (hb : b ∈ C) (hn : n < C.length ):
    C.idxOf b = C.idxOf a + 1 ∨ (C.idxOf b = 0 ∧ C.idxOf a = C.length - 1)
    ↔ (C.rotate n).idxOf b = (C.rotate n).idxOf a + 1 ∨
    ((C.rotate n).idxOf b = 0 ∧ (C.rotate n).idxOf a = C.length - 1) := by
  have hne : C.Nonempty := by exact hC.nonempty
  refine ⟨ ?_, ?_ ⟩
  intro h
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

  intro h
  have hh : (C.rotate n).idxOf b + n = (C.rotate n).idxOf a + n + 1
      ∨ (C.rotate n).idxOf b + n = n ∧ (C.rotate n).idxOf a + n = C.length - 1 + n
      := by
    omega
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  rw [hC.idxOf_rotate_n_le ha hle] at hh
  · obtain hleb | hltb := le_or_gt n (C.idxOf b)
    · rw [ hC.idxOf_rotate_n_le hb hleb ] at hh
      obtain hgood | hf := hh
      · omega
      have := (hC.isClosed).idxOf_lt_length ha hne
      rw[hf.2] at this
      by_contra
      omega
    rw [hC.idxOf_rotate_n hb hn hltb] at hh
    have := (hC.isClosed).idxOf_lt_length ha hne
    have : C.length ≤ C.length + C.idxOf b := by exact Nat.le_add_right C.length (C.idxOf b)
    have : C.length + C.idxOf b = C.length ∨ C.length + C.idxOf b = C.length + 1 := by omega
    obtain haa | haaa := this
    · simp at haa
      rw [haa] at hh
      omega
    simp at haaa
    rw[haaa] at hh
    simp at hh
    omega
  obtain hleb | hltb := le_or_gt n (C.idxOf b)
  rw [hC.idxOf_rotate_n_le hb hleb ] at hh
  · rw [hC.idxOf_rotate_n ha hn hlt ] at hh
    have := (hC.isClosed).idxOf_lt_length hb hne
    by_contra
    omega
  rw [hC.idxOf_rotate_n ha hn hlt] at hh
  rw [hC.idxOf_rotate_n hb hn hltb] at hh
  omega

  lemma get_rotate (w : WList α β) {a b : ℕ} (hab : a + b ≤ w.length) :
    (w.rotate a).get b = w.get (a + b) := by
  induction w generalizing a b with simp_all
  | cons u e w IH =>
    sorry
