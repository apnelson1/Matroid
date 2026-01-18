import Matroid.Graph.Walk.Cycle
import Matroid.ForMathlib.Tactic.ENatToNat

-- This file contains all relevant lemmas on WLists by themselves, without reference to graphs.

open WList Set

namespace WList

variable {α β ι : Type*} {x y z u v : α} {e f : β} {w w₁ w₂ p q P Q C : WList α β} {m n : ℕ}

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

lemma idx_Of_tail [DecidableEq α] (hw : w.Nonempty) (hxf : w.first ≠ x) (hx : x ∈ w) :
    (w.tail).idxOf x + 1 = w.idxOf x := by
  fun_induction WList.idxOf with simp_all

lemma idx_Of_dropLast [DecidableEq α] (hw : w.Nonempty) (hx : x ∈ w) :
    (w.dropLast).idxOf x = w.idxOf x := by
  induction w using concat_induction with simp_all
  | concat w e u IH =>
     obtain (h_mem|h_notMem) := em (x ∈ w)
     · exact (idxOf_concat_of_mem h_mem).symm
     replace hx : x = u := by tauto
     fun_induction w.idxOf x with simp_all

-- idxOf is injective if either element is in the list
lemma idxOf_inj_of_left_mem [DecidableEq α] (hx : x ∈ w) (heq : w.idxOf x = w.idxOf y) : x = y := by
  have hy : y ∈ w := idxOf_le_length_iff_mem.mp (heq ▸ idxOf_le_length_iff_mem.mpr hx)
  rw [← get_idxOf w hx, ← get_idxOf w hy, heq]

lemma idxOf_inj_of_right_mem [DecidableEq α] (hy : y ∈ w) (heq : w.idxOf x = w.idxOf y) :
    x = y := by
  symm at heq ⊢
  exact idxOf_inj_of_left_mem hy heq

lemma idxOf_inj [DecidableEq α] (hmem : x ∈ w ∨ y ∈ w) : w.idxOf x = w.idxOf y ↔ x = y :=
  ⟨hmem.elim idxOf_inj_of_left_mem idxOf_inj_of_right_mem, by tauto⟩

lemma idxOf_get_le [DecidableEq α] (w : WList α β) (n : ℕ) : w.idxOf (w.get n) ≤ n := by
  generalize x_def : w.get n = x
  fun_induction w.get n with simp_all
  | case3 u e w n IH =>
      simp [w.idxOf_cons u e]
      obtain (rfl|hne) := em (u = x) <;> simp_all

-- idxOf is the first occurence of a value; all values before it must not be equal
lemma ne_of_idx_lt_idxOf [DecidableEq α] (hlt : n < w.idxOf x) : w.get n ≠ x := by
  rintro rfl
  have := w.idxOf_get_le n; omega

-- this is somehow not present??
lemma idxOf_le [DecidableEq α] (w : WList α β) (x : α) : w.idxOf x ≤ w.length + 1 := by
  fun_induction w.idxOf x with simp_all

lemma idxOf_eq_zero_iff [DecidableEq α] : w.idxOf x = 0 ↔ x = w.first := by
  fun_induction WList.idxOf with simp_all [Ne.symm]

lemma idxOf_cons_eq_one_iff [DecidableEq α] : (cons u e w).idxOf x = 1 ↔ u ≠ x ∧ x = w.first := by
  generalize w'_def : cons u e w = w'
  fun_induction WList.idxOf with simp_all [idxOf_eq_zero_iff]

lemma idxOf_eq_succ_length_iff [DecidableEq α] : w.idxOf x = w.length + 1 ↔ x ∉ w := by
  fun_induction WList.idxOf with simp_all [Ne.symm]

lemma idxOf_eq_length [DecidableEq α] (h : w.idxOf x = w.length) : x = w.last := by
  fun_induction WList.idxOf with simp_all

lemma idxOf_eq_length_iff [DecidableEq α] (h : w.vertex.Nodup) :
    w.idxOf x = w.length ↔ x = w.last := by
  fun_induction WList.idxOf with simp_all [Ne.symm]
  | case3 e w u => rintro rfl; exact h.1 w.last_mem

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

-- lemma idxOf_get_lt [DecidableEq α] (hlt : n < w.idxOf x) : w.idxOf

------ reverse lemmas

lemma nodup_reverse_vertex_iff : w.reverse.vertex.Nodup ↔ w.vertex.Nodup := by
  simp only [reverse_vertex, List.nodup_reverse]

lemma idxOf_reverse [DecidableEq α] (hw : w.vertex.Nodup) (hx : x ∈ w) :
    w.reverse.idxOf x = w.length - w.idxOf x := by
  fun_induction WList.idxOf with simp_all
  | case3 e w x =>
    have heq : (w.reverse.concat e x).vertex = w.vertex.reverse.concat x := by simp
    have hw' : (w.reverse.concat e x).vertex.Nodup := by
      rw [heq, List.nodup_concat]
      simp; tauto
    rw [← reverse_length, ← @concat_length _ _ x e w.reverse, idxOf_eq_length_iff hw']
    simp
  | case4 u e w x hne IH =>
    replace hx : x ∈ w := by tauto
    rw [← IH hx]
    refine idxOf_concat_of_mem (by simpa)

lemma idxOf_reverse_add_idxOf [DecidableEq α] (hw : w.vertex.Nodup) (hx : x ∈ w) :
    w.reverse.idxOf x + w.idxOf x = w.length := by
  have h₁ := idxOf_reverse hw hx
  have h₂ : w.idxOf x ≤ w.length := idxOf_mem_le hx
  omega

lemma idxOf_add_idxOf_reverse [DecidableEq α] (hw : w.vertex.Nodup) (hx : x ∈ w) :
    w.idxOf x + w.reverse.idxOf x = w.length := by
  rw [add_comm]; exact idxOf_reverse_add_idxOf hw hx

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
  simp only [prefixUntilVertex]
  fun_induction WList.prefixUntil with simp_all [idxOf_eq_zero_iff]
  | case3 u e w hne IH =>
    replace hx : x ∈ w := by tauto
    obtain (rfl|hne') := em (u = y) <;> simp_all

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
  simp only [prefixUntilVertex]
  fun_induction WList.prefixUntil with simp_all [idxOf_eq_zero_iff]
  | case3 u e w hne IH =>
    replace hx : x ∈ w := by tauto
    obtain (rfl|hne') := em (u = y)
    · simp
    replace hy : y ∈ w := by tauto
    simp_all
    tauto

lemma prefixUntilVertex_concat_of_exists [DecidableEq α] (w : WList α β)
    (h : v ∈ w) : (w.concat e x).prefixUntilVertex v = w.prefixUntilVertex v:= by
  have hrw : (w.concat e x).prefixUntilVertex v = (w.concat e x).prefixUntil (· = v) := by exact rfl
  have h : ∃ u ∈ w, (· = v) u := by use v
  have hrw' : (w.prefixUntil fun x ↦ x = v) = w.prefixUntilVertex v := by exact rfl
  rw [hrw, prefixUntil_concat_of_exists w (· = v) h, hrw' ]

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

lemma Nonempty.rotate_one (hCne : C.Nonempty) :
    ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  use hCne.firstEdge
  nth_rw 1 [Eq.symm (Nonempty.cons_tail hCne)]
  rw [cons_rotate_one]

lemma Nonempty.idxOf_rotate_one [DecidableEq α] (hw : w.Nonempty) (h1 : w.first ≠ x) (hx : x ∈ w) :
    (w.rotate 1).idxOf x + 1 = w.idxOf x := by
  obtain ⟨e, h⟩ := hw.rotate_one
  have hxt : x ∈ w.tail := by
    obtain hfirst | h1 := eq_first_or_mem_tail hx
    · by_contra
      exact h1 hfirst.symm
    exact h1
  have := idx_Of_tail hw h1 hx
  rwa [h, idxOf_concat_of_mem hxt]

lemma mem_rotate_n_of_n_le_idxOf [DecidableEq α] (hx : x ∈ w) (hle : n ≤ w.idxOf x) :
    x ∈ w.rotate n := by
  fun_induction WList.rotate with simp_all
  | case3 u e w n IH =>
    obtain (rfl|hne) := em (u = x)
    · simp at hle
    replace hx : x ∈ w := by tauto
    refine IH (Or.inl hx) ?_
    simp_all
    rwa [idxOf_concat_of_mem hx]

lemma idxOf_rotate_n_of_n_le_idxOf [DecidableEq α] (hx : x ∈ w) (hle : n ≤ w.idxOf x) :
    (w.rotate n).idxOf x + n = w.idxOf x := by
  obtain (h | hNonempty) := em' w.Nonempty
  · simp only [WList.not_nonempty_iff, nil_iff_eq_nil] at h
    -- TODO: nil_iff_eq_nil should be made into a @[simp] lemma.
    obtain ⟨y, rfl⟩ := h
    simp_all
  fun_induction w.rotate n with simp_all
  | case3 u e w n IH =>
    obtain (rfl|hne) := em (u = x)
    · simp at hle
    replace hx : x ∈ w := by tauto
    simp_all
    -- TODO: idxOf_concat_of_mem should be made into a @[simp] lemma.
    simp only [← add_assoc, IH (by rwa [idxOf_concat_of_mem hx]), idxOf_concat_of_mem hx]

lemma idxOf_rotate_first_ne_of_lt [DecidableEq α] (hlt : n < w.idxOf x) :
    (w.rotate n).first ≠ x := by
  rw [w.rotate_first n (by have := w.idxOf_le x; omega)]
  exact ne_of_idx_lt_idxOf hlt

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
  obtain ⟨e, hC ⟩ := hwnt.rotate_one
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
