import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic
import Matroid.Graph.Walk.Cycle
import Matroid.ForMathlib.Tactic.ENatToNat

-- This file contains all relevant lemmas on WLists by themselves, without reference to graphs.

open WList Set

namespace WList

variable {α β ι : Type*} {x y z u v a b : α} {e f : β} {w w₁ w₂ p q P Q C : WList α β} {m n : ℕ}

---- prefix / suffix lemmas

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

lemma prefixUntilVertex_concat_of_exists [DecidableEq α] (w : WList α β)
    (h : v ∈ w) : (w.concat e x).prefixUntilVertex v = w.prefixUntilVertex v:= by
  have hrw : (w.concat e x).prefixUntilVertex v = (w.concat e x).prefixUntil (· = v) := by exact rfl
  have h : ∃ u ∈ w, (· = v) u := by use v
  have hrw' : (w.prefixUntil fun x ↦ x = v) = w.prefixUntilVertex v := by exact rfl
  rw [hrw, prefixUntil_concat_of_exists w (· = v) h, hrw' ]

lemma prefixUntilVertex_cons [DecidableEq α] (w) :
    (cons x e w).prefixUntilVertex v = if x = v then nil x else cons x e (w.prefixUntilVertex v) :=
    by
  have hrw :  (cons x e w).prefixUntilVertex v = (cons x e w).prefixUntil (· = v) := by exact rfl
  have hrw' : (w.prefixUntil fun x ↦ x = v) = w.prefixUntilVertex v := by exact rfl
  rw [hrw, prefixUntil_cons w, hrw' ]

--No
lemma prefixUntilVertex_last_eq_self [DecidableEq α] (w : WList α β) (hw : w.vertex.Nodup) :
    w.prefixUntilVertex w.last = w := by
  induction w with
  | nil u =>
  simp only [nil_last]
  exact rfl
  | cons u e w ih =>
  simp only [last_cons]
  have hlu : u ≠ w.last := by sorry
  rw[prefixUntilVertex_cons ]
  simp [hlu]
  exact ih (List.Nodup.of_cons hw)

lemma prefixUntilVertex_tail [DecidableEq α] (w : WList α β) (hv : v ≠ w.first) (hvw : v ∈ w)
  (hw : w.vertex.Nodup) :
    w.tail.prefixUntilVertex v = (w.prefixUntilVertex v).tail := by
  induction w using concat_induction with
    | nil u =>
    simp only [tail_nil]
    by_contra hc
    exact hc rfl
    | @concat w f y ih =>
    simp only [mem_concat] at hvw
    obtain he | hwne := (exists_eq_nil_or_nonempty w)
    · obtain ⟨x, hx ⟩ := he
      rw[hx]
      simp only [nil_concat, tail_cons]
      have h : (nil y (β := β)).prefixUntilVertex v = (nil y (β := β)).prefixUntil (· = v) := rfl
      rw[h, prefixUntil_nil]
      simp only [concat_first, ne_eq] at hv
      rw[hx] at hv
      have : x ≠ v := by
        by_contra hc
        rw[hc] at hx
        have : v = w.first := by
          rw[hx]
          exact rfl
        exact hv (id (Eq.symm hc))
      rw[prefixUntilVertex_cons (nil y)]
      simp [this]
      exact h
    obtain heasy | rfl := hvw
    · have hw' : w.vertex.Nodup := by sorry
      rw[concat_first] at hv
      have hvtail : v ∈ w.tail := by
        refine (mem_tail_iff_of_nodup hw' hwne).mpr ?_
        exact Decidable.not_imp_iff_and_not.mp fun a ↦ hv (a heasy)
      rw[tail_concat hwne, prefixUntilVertex_concat_of_exists w heasy ,
      prefixUntilVertex_concat_of_exists w.tail hvtail, ih hv heasy hw' ]
    have hw' : (w.concat f v).tail.vertex.Nodup := by sorry
    have : v = (w.concat f v).tail.last := by
      simp only [tail_last, concat_last]
    nth_rw 2 [this]
    have : v = (w.concat f v).last := by exact Eq.symm concat_last
    rw[prefixUntilVertex_last_eq_self (w.concat f v).tail hw' ]
    nth_rw 3 [this]
    rw[prefixUntilVertex_last_eq_self (w.concat f v) hw ]

-- lemma IsCycle.prefixUntilVertex_tail [DecidableEq α] {C : WList α β} (hC : G.IsCycle C)
--     (hv : v ≠ C.first) (hvC : v ∈ C) :
--     C.tail.prefixUntilVertex v = (C.prefixUntilVertex v).tail := by sorry

lemma suffixFromVertex_concat_of_exists [DecidableEq α]  (w : WList α β) (hb : v ∈ w ):
    (w.concat e x).suffixFromVertex v = (w.suffixFromVertex v).concat e x := by
  have hrw : (w.concat e x).suffixFromVertex v = (w.concat e x).suffixFrom (· = v) := by exact rfl
  have h : ∃ u ∈ w, (· = v) u := by use v
  have hrw' : (w.suffixFrom fun x ↦ x = v) = w.suffixFromVertex v := by exact rfl
  rw[hrw, suffixFrom_concat_of_exists w (· = v) h, hrw' ]

lemma suffixFromVertex_concat_of_forall [DecidableEq α]  (w : WList α β) (hb : x ∉ w ):
    (w.concat e x).suffixFromVertex x = nil x := by
  have hrw : (w.concat e x).suffixFromVertex x = (w.concat e x).suffixFrom (· = x) := by exact rfl
  have h : ∀ u ∈ w, ¬ (· = x) u := by
    exact fun u a ↦ ne_of_mem_of_not_mem a hb
  rw[hrw, suffixFrom_concat_of_forall w (· = x) h ]

lemma suffixFromVertex_cons [DecidableEq α]  (w : WList α β):
    (cons x e w).suffixFromVertex v = if x = v then cons x e w else w.suffixFromVertex v := rfl

lemma suffixFromLastVertex [DecidableEq α] {u : α} (w : WList α β) (hw : w.vertex.Nodup) :
   w.suffixFromVertex w.last = nil w.last := by
  induction w with
  | nil u =>
  simp
  | cons y e w ih =>
  have hyn : y ≠ (cons y e w).last := by
    sorry
    --refine List.nodup_iff_pairwise_ne.mpr ?_
  rw[suffixFromVertex_cons ]
  split_ifs
  (expose_names; exact hyn h)
  simp only [last_cons]
  exact ih (List.Nodup.of_cons hw )

lemma SuffixFromVertex_get [DecidableEq α] (w : WList α β) {a : ℕ } (hne : w.Nonempty)
    (hla : a + 1 ≤ w.length) (hw : w.vertex.Nodup)  :
    w.suffixFromVertex (w.get (a + 1)) = (w.suffixFromVertex (w.get a)).tail := by
  induction w using concat_induction with
  | nil u => simp at hne
  | @concat w f y ih =>
  simp at hla
  have hgeta : (w.concat f y).get a ∈ (w.concat f y) := by
    rw[get_concat w f y hla]
    refine mem_concat.mpr ?_
    left
    exact get_mem w a
  have hgetaa : w.get a ∈ w := by exact get_mem w a
  have hwe' : w.vertex.Nodup := by
      sorry
  obtain haalength | hhlt := le_or_gt (a + 1) w.length
  --have haalength : a + 1 ≤ w.length := by sorry
  · obtain he | hwne := (exists_eq_nil_or_nonempty w)
    · obtain ⟨x, hx ⟩ := he
      rw[hx]
      simp only [nil_concat, get_cons_add, get_nil]
      rw[hx] at hla
      simp only [nil_length, nonpos_iff_eq_zero] at hla
      rw[hla]
      simp only [get_zero, first_cons]
      rw[suffixFromVertex_cons ]
      have : x ≠ y := by sorry
      simp [this ]
      have hrw : (nil y (β := β)).suffixFromVertex y = (nil y (β := β)).suffixFrom (· = y) := by
        exact rfl
      have : (nil y (β := β)).suffixFrom (· = y) = nil y := by exact hrw
      rw[ suffixFromVertex_cons ]
      simp
    have hb : (w.concat f y).get (a + 1) ∈ w := by
      rw[get_concat w f y haalength]
      exact get_mem w (a + 1)
    rw[suffixFromVertex_concat_of_exists w hb, get_concat w f y hla,
    suffixFromVertex_concat_of_exists w hgetaa,get_concat w f y haalength, tail_concat sorry,
    ←(ih hwne haalength hwe')  ]
  have hex : a = w.length := by exact Eq.symm (Nat.eq_of_le_of_lt_succ hla hhlt)
  have hrw : ((w.concat f y).get (a + 1)) = y := by
    rw [hex]
    have : (w.concat f y).length = w.length + 1 := by exact concat_length
    rw[←this, get_length (w.concat f y) ]
    exact concat_last
  have hrw' : (w.concat f y).get a = w.last := by
    rw[hex, get_concat w f y (Nat.le_refl w.length)]
    exact get_length w
  rw[hrw, hrw' ]
  have hyw : y ∉ w := by
    sorry
  rw[suffixFromVertex_concat_of_forall w hyw  ]
  have h2 : ((w.concat f y).suffixFromVertex w.last).tail = nil y := by
    have h1 : (w.concat f y).suffixFromVertex w.last = (nil w.last).concat f y := by
      have hb : w.last ∈ w := by exact last_mem
      rwa[suffixFromVertex_concat_of_exists w hb, suffixFromLastVertex w hwe' ]

    rw[h1]
    simp only [nil_concat, tail_cons]
  rw[h2]

lemma suffixFromVertex_index [DecidableEq α] (hx : x ∈ w) (hle : w.idxOf x ≤ w.idxOf y) :
    w.idxOf y = (w.suffixFromVertex x).idxOf y + w.idxOf x := by
  induction w with
  | nil u =>
  simp only [idxOf_nil, suffixFromVertex_nil, Nat.left_eq_add, ite_eq_left_iff, one_ne_zero,
    imp_false, Decidable.not_not]
  simp only [mem_nil_iff] at hx
  exact hx.symm
  | cons a e w ih =>
  simp only [mem_cons_iff] at hx
  obtain rfl | haw := eq_or_ne x a
  · obtain rfl | hxy := eq_or_ne y x
    · rw[idxOf_cons, suffixFromVertex_cons]
      simp only [↓reduceIte, add_zero, idxOf_cons_self]
    rw[idxOf_cons, suffixFromVertex_cons]
    simp only [↓reduceIte, idxOf_cons_self, add_zero, hxy.symm]
    rw[idxOf_cons]
    simp [hxy.symm]
  rw[idxOf_cons, suffixFromVertex_cons]
  simp [haw.symm]
  obtain rfl | hay := eq_or_ne y a
  · simp only [↓reduceIte]
    simp only [idxOf_cons_self, nonpos_iff_eq_zero] at hle
    rw[idxOf_cons] at hle
    simp [haw.symm] at hle
  simp [hay.symm]
  rw[idxOf_cons,idxOf_cons] at hle
  simp [haw.symm, hay.symm] at hle
  simp [haw] at hx
  rw[ih hx hle]
  omega

-------- DInc lemmas


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

---- IdxOf

lemma Cycle_conc_index [DecidableEq α] (huv : v ≠ u) (hCP : v ∈ cons u e (P.concat f u)) :
    v ∈ P ∧ (cons u e (P.concat f u)).idxOf v = P.idxOf v + 1 := by
  simp only [mem_cons_iff, mem_concat] at hCP
  obtain (rfl | h2 | rfl) := hCP
  · contradiction
  · exact ⟨h2, by simp [idxOf_cons_ne huv.symm, idxOf_concat_of_mem h2]⟩
  · contradiction

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

lemma idxOf_eq [DecidableEq α] (hx : x ∈ w) (heq : w.idxOf x = w.idxOf y) :
    x = y := by
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

--------- rotate lemmas

lemma rotate_one (hCne : C.Nonempty) : ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  use hCne.firstEdge
  nth_rw 1 [Eq.symm (Nonempty.cons_tail hCne)]
  rw [cons_rotate_one]

lemma get_rotate [DecidableEq α] (w : WList α β) {a b : ℕ} (hab : a + b ≤ w.length) :
    (w.rotate a).get b = w.get (a + b) := by
  induction b generalizing w a with
  | zero => simp_all; exact w.rotate_first a hab
  | succ b IH =>
      show (w.rotate a).get (b + 1) = w.get (a + (b + 1))
      calc
        (w.rotate a).get (b + 1) = (w.rotate a).get (1 + b) := by
          rw [add_comm]
        _ = (w.rotate (a + 1)).get b := by
          rw [← IH (w.rotate a) (by simp; omega), w.rotate_rotate]
        _ = w.get ((a + 1) + b) := by
          rw [IH _ (by omega)]
        _ = w.get (a + (b + 1)) := by
          rw [show ((a + 1) + b = a + (b + 1)) by omega]

lemma rotate_pre_suff [DecidableEq α] (w : WList α β) {a : ℕ} (hnt : w.Nonempty)
    (hla : a ≤ w.length) (hw : w.vertex.Nodup) :
    (w.rotate a).prefixUntilVertex (w.last ) = w.suffixFromVertex (w.get a) := by
  induction a with
  | zero =>
  simp
  rw [ prefixUntilVertex_last_eq_self w hw ]
  | succ n IH =>
  have hwnd : (w.rotate n).vertex.Nodup := by sorry
  have hwnt : (w.rotate n).Nonempty := by sorry
  rw[←rotate_rotate w n 1, SuffixFromVertex_get w hnt hla hw ]
  obtain ⟨e, hC ⟩ := rotate_one hwnt
  rw[hC]
  set w' := (w.rotate n) with h_w'
  have : ((w.rotate n).tail.concat e (w.rotate n).tail.first).prefixUntilVertex w.last
      = ((w.rotate n).prefixUntilVertex w.last).tail := by
    rw[←h_w']
    have hlin : w.last ∈ w'.tail := by sorry
    rw[prefixUntilVertex_concat_of_exists w'.tail hlin, prefixUntilVertex_tail w']
    rw[h_w']
    sorry
    sorry
    exact hwnd
  sorry
