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

-- lemma IsRotaryFan.rotate' (h : M.IsRotaryFan F b) (n : ℕ) :
--     M.IsRotaryFan (F.rotateLeft n) (n.bodd != b) := by
--   rw [rotateLeft_eq]

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

lemma IsRotaryFan.restrict_connected (hF : M.IsRotaryFan F b) : (M ↾ {e | e ∈ F}).Connected := by
  wlog hb : b = false generalizing F b with aux
  · obtain rfl : b = true := by grind
    simpa using aux hF.reverse rfl
  subst hb
  refine connected_iff_exists.2 ⟨F[0], by simp, fun f hf ↦ ?_⟩
  obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem hf
  · simp
  suffices hC : ∃ C ⊆ {e | e ∈ F}, M.IsCircuit C ∧ F[0] ∈ C ∧ F[i + 1] ∈ C by
    obtain ⟨C, hCss, hC, h0C, hiC⟩ := hC
    exact (hC.isCircuit_restrict_of_subset hCss).mem_connectedTo_mem h0C hiC
  obtain hi' | hne := eq_or_ne (i + 2) F.length
  · exact ⟨_, by simp [insert_subset_iff], hF.isTriangle.isCircuit, by simp, by simp [← hi']⟩
  have hC := hF.isFan.isCircuit_interval (p := 0) (q := i + 1 + (!i.bodd).toNat) (by lia) (by grind)
    rfl (by simp) (by simp)
  refine ⟨_, getElems_subset_toSet .., hC, by simp [hF.isFan.nodup], ?_⟩
  cases h : i.bodd with simp [hF.isFan.nodup, h]

/-- A rotary fan is the entire matroid iff the matroid is connected. -/
lemma IsRotaryFan.setOf_eq_ground_iff (hF : M.IsRotaryFan F b) :
    {e | e ∈ F} = M.E ↔ M.Connected := by
  refine ⟨fun h ↦ ?_, fun h ↦ hF.setOf_eq_ground h.tutteConnected_two⟩
  rw [← M.restrict_ground_eq_self]
  exact h ▸ hF.restrict_connected

#check List.rotate

lemma IsRotaryFan.parallel_iff_eq (h : M.IsRotaryFan F b) {i j} {hi : i < F.length}
    {hj : j < F.length} : M.Parallel F[i] F[j] ↔ i = j := by

  wlog hij : i < j generalizing i j with aux
  · obtain rfl | hne := eq_or_ne i j
    · simp [h.isFan.isNonloop (show F[i] ∈ F by simp)]
    rw [parallel_comm, aux (hj := hi) (hi := hj) (by lia), eq_comm]
  wlog hb : b = false generalizing b with aux
  · _
  obtain rfl | j := j; lia
  induction i generalizing F j b with
  | zero =>
    suffices ¬ M.Parallel F[0] F[j + 1] by simpa
    intro hp
    obtain rfl | rfl := b
    ·
    -- obtain rfl | j := j; lia
    -- simp only [Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, iff_false]
    -- sorry
  | succ i ih =>
    obtain rfl | j := j; lia
    have hwin := ih (h.rotate 1) (j := j) (hj := by grind [length_rotate])
      (hi := by grind [length_rotate]) (by lia)
    simpa [getElem_rotate, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hwin

  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij

  wlog hi1 : i = 1 generalizing i j F b with aux
  · convert aux (h.rotate (F.length - 1 + i)) (i := 1) (j := (j + F.length + 1 - i) % F.length)
      (hi := by grind [length_rotate])
      (hj := by grw [length_rotate, Nat.mod_lt _ (by grind)]) rfl using 1
    · sorry
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hi
    simp [hk, show j + (i + k + 1) + 1 - i = j + k + 2 by lia]


    rw []
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' h.length_ge

    -- simp [hn, ← add_assoc, add_comm _ n] at this


lemma IsRotaryFan.contract_delete (h : M.IsRotaryFan F false) (hlen : 4 < F.length) :
    (M ＼ {F[0]} ／ {F[1]}).IsRotaryFan F.tail.tail false := by
  have h6 : 6 ≤ F.length := sorry
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' h6

  refine ⟨?_, ?_, ?_⟩
  · have := (h.isFan.delete_head' (by lia) ?_ (by simp)).contract_head' (by grind) ?_ (by simp)
  have := (h.isFan.contract_head (by lia) (by simp)).delete_head (by grind) (fun _ ↦ ?_)
  · simpa
  · suffices ¬M✶.Parallel F[1] F[F.length - 1 - 1 + 1] by
      simpa [delete_parallel_iff, h.isFan.nodup.getElem_inj_iff]
    exact fun hp ↦ by simpa using h.dual.isFan.eq_eq_of_parallel h6 (by lia) hp
  · suffices (M ／ {F[0]}).IsTriangle {F[n + 4], F[n + 5], F[2]} by
      simpa [hn, add_assoc, h.isFan.nodup.getElem_inj_iff]

  sorry

lemma IsRotaryFan.eRk_eq (hF : M.IsRotaryFan F b) : 2 * M.eRk {e | e ∈ F} = F.length := by
  wlog hb : b = false generalizing F b with aux
  · simpa using aux hF.reverse (by grind)
  subst hb
  have := (hF.isFan.tail (by grind)).eRk_eq
  simp at this

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

lemma IsRotaryFan.exists_btw_of_isNonspanningCircuit (h : M.IsRotaryFan F b) {C : Set α}
    (hM : M.TutteConnected 2) (hC : M.IsNonspanningCircuit C)
    (hnss : C ≠ F.getElems {i | i.bodd = !b}) : ∃ (p q r : ℕ) (hpq : p < q)
    (hq : q < F.length) (hr : r < F.length), p.bodd = !b ∧ q.bodd = !b ∧ r.bodd = !b ∧
    F[p] ∉ C ∧ F[q] ∉ C ∧ F[r] ∈ C := by
  _

    -- p.bodd = !b) p < q
    -- ∃ (p q r : ZMod n), btw p q r ∧ p ≠ q ∧ p ≠ r ∧ J true p ∉ C ∧ J true q ∈ C ∧ J true r ∉ C := by

lemma IsRotaryFan.foo (h : M.IsRotaryFan F b) (hM : M.TutteConnected 2) {C : Set α}
    (hC : M.IsNonspanningCircuit C) (hne : C ≠ F.getElems {i | i.bodd = !b}) :
    ∃ (p q : ℕ) (hp : p < F.length) (hpq : p < q) (hq : q < F.length) (hpb : p.bodd = b)
    (hqb : q.bodd = b), C = F.getElems (insert p <| insert q <| {i ∈ Ico p q | i.bodd = !b})
    ∨ C = F.getElems (insert p <| insert q <| {i ∈ Iio p ∪ Ico q F.length | i.bodd = !b}) := by
  _
