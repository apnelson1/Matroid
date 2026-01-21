import Matroid.Graph.Walk.Cycle
import Matroid.ForMathlib.Tactic.ENatToNat

-- This file contains all relevant lemmas on WLists by themselves, without reference to graphs.

open WList Set

namespace WList

variable {α β ι : Type*} {x y z u v : α} {e f : β} {w w₁ w₂ p q P Q C : WList α β} {m n : ℕ}

---- IdxOf

lemma cycle_cons_index [DecidableEq α] (huv : v ≠ u) (hCP : v ∈ cons u e (P.concat f u)) :
    v ∈ P ∧ (cons u e (P.concat f u)).idxOf v = P.idxOf v + 1 := by
  simp only [mem_cons_iff, mem_concat] at hCP
  obtain (rfl | h2 | rfl) := hCP
  · contradiction
  · exact ⟨h2, by simp [idxOf_cons_ne huv.symm, idxOf_concat_of_mem h2]⟩
  · contradiction

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

---- prefix / suffix lemmas

lemma prefixUntilVertex_idxOf [DecidableEq α] (hx : x ∈ w) (hle : w.idxOf y ≤ w.idxOf x) :
    w.idxOf y = (w.prefixUntilVertex x).idxOf y := by
  simp only [prefixUntilVertex]
  fun_induction WList.prefixUntil with simp_all [idxOf_eq_zero_iff]
  | case3 u e w hne IH =>
    replace hx : x ∈ w := by tauto
    obtain rfl | hne' := em (u = y) <;> simp_all

lemma prefixUntilVertex_concat_of_exists [DecidableEq α] (h : v ∈ w) :
    (w.concat e x).prefixUntilVertex v = w.prefixUntilVertex v :=
  prefixUntil_concat_of_exists w (· = v) (by use v)

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

lemma prefixUntilVertex_tail [DecidableEq α] (w : WList α β) (hv : v ≠ w.first) (hvw : v ∈ w) :
    w.tail.prefixUntilVertex v = (w.prefixUntilVertex v).tail := by
  induction w with simp_all
  | cons u e w IH =>
    simp only [prefixUntilVertex]
    fun_induction WList.prefixUntil with
    | case1 | case2 => simp_all; split_ifs <;> simp
    | case3 x f w hne IH =>
      replace hvw : v ∈ w := by simp at hvw; tauto
      simp [hvw] at IH
      split_ifs at IH <;> [tauto; skip]
      simp_all

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
  simp only [suffixFromVertex]
  fun_induction WList.suffixFrom with simp_all
  | case3 u e w hne IH =>
    replace hx : x ∈ w := by tauto
    obtain (rfl|hne') := em (u = y) <;> simp_all
    omega

 --------- rotate lemmas

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
  obtain ⟨e, hC⟩ := hwnt.rotate_one
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
    -- exact hwnd
  sorry
