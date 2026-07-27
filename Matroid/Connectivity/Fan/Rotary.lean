import Matroid.Connectivity.Fan.Circuit
import Matroid.Connectivity.Separation.Tutte

open Set List

namespace Matroid

variable {α β : Type*} {F : List α} {b c d : Bool} {M : Matroid α}

structure IsRotaryFan (M : Matroid α) (F : List α) (b : Bool) : Prop where
  isFan : M.IsFan F b (!b)
  isTriangle : (M.bDual b).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]}
  isTriad : (M.bDual (!b)).IsTriangle {F[F.length - 1], F[0], F[1]}

@[grind! .]
lemma IsRotaryFan.length_ge (h : M.IsRotaryFan F b) : 4 ≤ F.length := by
  cases h.isFan with
  | of_pair b e f he hf hne => simpa using h.isTriangle
  | cons_triangle e x y F b c h heF hT =>
    cases F with
    | nil =>
      have hcon := h.length_bodd_eq
      simp at hcon
    | cons y F => simp

lemma IsRotaryFan.rotate (h : M.IsRotaryFan F b) (n : ℕ) :
    M.IsRotaryFan (F.rotate n) (b != n.bodd) := by
  suffices aux : ∀ {F b}, M.IsRotaryFan F b → M.IsRotaryFan (F.rotate 1) (!b) by
    induction n with
    | zero => simpa
    | succ n ih => simpa using aux ih
  refine @fun J d hJ ↦ ⟨?_, ?_, ?_⟩
  · rw [isFan_iff_forall (by grw [length_rotate, ← hJ.length_ge]; simp),
      and_iff_right (by simp [hJ.isFan.length_bodd_eq]),
      and_iff_right (by simpa using hJ.isFan.nodup)]
    intro i hi
    simp only [length_rotate] at hi
    simp only [Bool.not_bne, getElem_rotate, Nat.mod_eq_of_lt (show i + 1 < J.length by lia),
      Nat.mod_eq_of_lt (show i + 1 + 1 < J.length from hi)]
    by_cases hi' : i + 3 = J.length
    · simp only [add_assoc, Nat.reduceAdd, hi', Nat.mod_self]
      have hi : i.bodd = true := by
        have hwin := hJ.isFan.length_bodd_eq ▸ congr_arg Nat.bodd hi'
        simpa using hwin
      convert hJ.isTriangle
      · simp [hi]
      · lia
      lia
    simp_rw [Nat.mod_eq_of_lt (show i + 2 + 1 < J.length by lia), add_right_comm _ 2]
    exact (hJ.isFan.bDual _).isTriangle_getElem_of_eq _ _ (by simp)
  · simp only [length_rotate, getElem_rotate, zero_add]
    simp_rw [Nat.mod_eq_of_lt (show J.length - 2 + 1 < J.length by grind),
      Nat.sub_add_cancel (show 1 ≤ J.length by grind), Nat.mod_self,
      Nat.one_mod_eq_one.2 (show J.length ≠ 1 by grind)]
    convert hJ.isTriad
    grind [hJ.isFan]
  simp only [Bool.not_not, length_rotate, getElem_rotate, zero_add, Nat.reduceAdd]
  simp_rw [Nat.sub_add_cancel (show 1 ≤ J.length by grind), Nat.mod_self,
    Nat.mod_eq_of_lt (show 1 < J.length by grind), Nat.mod_eq_of_lt (show 2 < J.length by grind)]
  exact hJ.isFan.isTriangle_bDual (by grind)

lemma IsRotaryFan.reverse (h : M.IsRotaryFan F b) : M.IsRotaryFan F.reverse (!b) := by
  refine ⟨by simpa using h.isFan.reverse, ?_, ?_⟩
  · simp only [length_reverse, getElem_reverse, tsub_self, tsub_zero,
      show F.length - 1 - (F.length - 2) = 1 by grind]
    exact h.isTriad.reverse
  simp only [Bool.not_not, length_reverse, getElem_reverse, tsub_self, tsub_zero, Nat.sub_sub]
  exact h.isTriangle.reverse

lemma IsRotaryFan.dual (h : M.IsRotaryFan F b) : M✶.IsRotaryFan F (!b) :=
  ⟨by simpa using h.isFan.dual, by simpa using h.isTriangle, by simpa using h.isTriad⟩

@[simp]
lemma isRotaryFan_dual_iff : M✶.IsRotaryFan F b ↔ M.IsRotaryFan F (!b) :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

lemma IsRotaryFan.bDual (h : M.IsRotaryFan F b) (c : Bool) :
    (M.bDual c).IsRotaryFan F (b != c) := by
  obtain rfl | rfl := c
  · simpa
  simpa using h.dual

lemma IsRotaryFan.of_bDual (h : (M.bDual c).IsRotaryFan F b) : M.IsRotaryFan F (b != c) := by
  simpa using h.bDual c

/-- A fan on the ground set of a simple, cosimple matroid is rotary. -/
lemma IsFan.isRotaryFan_of_ground_eq (hF : M.IsFan F b c) (hM : M.Simple) (hM' : M✶.Simple)
    (hE : {e | e ∈ F} = M.E) : c = !b ∧ M.IsRotaryFan F b := by
  obtain ⟨h_even, hT⟩ := hF.isTriangle_bDual_of_simple (n := F.length - 2) (by grind) hM hM' hE
  obtain ⟨-, hT'⟩ := hF.reverse.dual.isTriangle_bDual_of_simple (n := F.length - 2) (by grind) hM'
    (by simpa) (by simpa)
  rw [← Nat.not_odd_iff_even, ← Nat.bodd_eq_odd, Bool.not_eq_true, hF.length_bodd_eq] at h_even
  obtain rfl : c = !b := by grind [cases Bool]
  refine ⟨rfl, ⟨hF, by grind, ?_⟩⟩
  simpa [show F.length - 1 - (F.length - 2) = 1 by grind,
    show F.length - 1 - (F.length - 2 + 1) = 0 by lia] using hT'.reverse

/-- A rotary fan in a `2`-connected matroid is the entire ground set. -/
lemma IsRotaryFan.setOf_eq_ground (h : M.IsRotaryFan F b) (hM : M.TutteConnected 2) :
    {e | e ∈ F} = M.E := by
  have hne : M.Nonempty := ⟨F[0], h.isFan.subset_ground (by simp)⟩
  refine (hM.connected rfl.le).eq_ground_of_eConn_eq_zero ?_ ⟨F[0], by simp⟩ h.isFan.subset_ground
  refine h.isFan.eConn_eq_zero_of_mem_closure_mem_closure ?_ ?_
  · refine mem_of_mem_of_subset h.isTriad.mem_closure₂ <| closure_subset_closure _ ?_
    simp [insert_subset_iff, getElem_mem_tail, show F.length - 1 ≠ 0 by grind]
  refine mem_of_mem_of_subset h.isTriangle.mem_closure₂ <| closure_subset_closure _ ?_
  simp [insert_subset_iff, getElem_mem_dropLast (show F.length - 2 < F.length - 1 by grind),
    getElem_mem_dropLast (show 0 < F.length - 1 by grind)]

/-- An even fan in a three-connected matroid whose initial element is (co)spanned by the
other elements is a rotary fan -/
lemma IsFan.isRotaryFan_of_tutteConnected_three_of_mem_closure (h : M.IsFan F b (!b))
    (hM : M.TutteConnected 3) (h4 : 4 ≤ M.E.encard)
    (hcl : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail}) : M.IsRotaryFan F b := by
  refine (h.isRotaryFan_of_ground_eq (hM.simple h4) (hM.dual.simple (by simpa)) ?_).2
  rw [show (3 : ℕ∞) = 2 + 1 from rfl] at hM
  have hle := h.eConn_le_one_of_mem_closure hcl
  have hne : M.Nonempty := ⟨F[0], h.subset_ground (by simp)⟩
  obtain h0 | hconn : M.eConn {e | e ∈ F} = 0 ∨ M.eConn {e | e ∈ F} = 1 := by enat_to_nat! <;> lia
  · exact (hM.connected (by simp)).eq_ground_of_eConn_eq_zero h0 (by simp [h.ne_nil])
      h.subset_ground
  obtain h1 | h1 := hM.encard_eq_or_encard_compl_eq (by grw [hle, one_add_one_eq_two])
    h.subset_ground
  · simp only [h.nodup.encard_toSet_eq, hconn, Nat.cast_eq_one] at h1
    simpa [h1] using h.two_le_length
  suffices aux : F[F.length - 1] ∈ (M.bDual b).closure {x | x ∈ F.dropLast} by
    simp [h.eConn_eq_zero_of_mem_closure_mem_closure hcl aux] at hconn
  have := ((hM.bDual b).dual.simple (by simpa))
  have h2 : (M.E \ {x | x ∈ F.dropLast}).encard ≤ 2 := by
    grw [h.nodup.toSet_dropLast_eq h.ne_nil, sdiff_sdiff_right, inter_subset_right,
      encard_union_le, h1, hle, encard_singleton, one_add_one_eq_two]
  have hss := coindep_iff_subset_closure_compl.1 <| (M.bDual b)✶.indep_of_encard_le_two h2
  rw [bDual_ground, sdiff_sdiff_cancel_left (subset_trans
    (by grind [mem_of_mem_dropLast]) h.subset_ground)] at hss
  refine mem_of_mem_of_subset ?_ hss
  simp [h.get_mem_ground, mem_dropLast_iff h.nodup h.ne_nil, getLast_eq_getElem]
