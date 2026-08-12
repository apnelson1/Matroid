import Matroid.Connectivity.Fan.Circuit
import Matroid.Connectivity.Fan.Minor
import Matroid.Connectivity.Separation.Tutte
import Mathlib.Logic.Equiv.Fin.Rotate

open Set List Nat Fin

lemma Set.preimage_singleton {α β : Type*} (f : α → β) (y : β) : f ⁻¹' {y} = {x | f x = y} := rfl

namespace Matroid

variable {α β : Type*} {F : List α} {b c d : Bool} {M : Matroid α}



variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

structure IsRotaryFan (M : Matroid α) (F : List α) (b : Bool) : Prop where
  isFan : M.IsFan F b (!b)
  isTriangle_end : (M.bDual b).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]}
  isTriad_end : (M.bDual (!b)).IsTriangle {F[F.length - 1], F[0], F[1]}

attribute [grind →] IsRotaryFan.isFan

-- macro_rules
--   | `(tactic| get_elem_tactic_extensible) =>
--     `(tactic| exact @ZMod.val_lt _ ⟨by grind⟩ ..)

-- macro_rules
--   | `(tactic| get_elem_tactic_extensible) =>
--     `(tactic| exact Nat.mod_lt _ (by grind))


-- @[grind =>]
-- lemma IsFan.mod_lt (hF : M.IsFan F b c) (i : ℕ) : i % F.length < F.length :=
--   Nat.mod_lt _ (by grind)

-- attribute [grind =>] Nat.mod_lt

@[grind! .]
lemma IsRotaryFan.length_ge (h : M.IsRotaryFan F b) : 4 ≤ F.length := by
  cases h.isFan with
  | of_pair b e f he hf hne => simpa using h.isTriangle_end
  | cons_triangle e x y F b c h heF hT =>
    cases F with
    | nil =>
      have hcon := h.length_bodd_eq
      simp at hcon
    | cons y F => simp

lemma IsRotaryFan.even (h : M.IsRotaryFan F b) : F.length.bodd = false := by
  simpa using h.isFan.length_bodd_eq

lemma IsRotaryFan.length_sub_one_bodd (h : M.IsRotaryFan F b) : (F.length - 1).bodd = true := by
  simpa using h.isFan.length_sub_one_bodd_eq

lemma IsRotaryFan.length_sub_two_bodd (h : M.IsRotaryFan F b) : (F.length - 2).bodd = false := by
  rw [bodd_sub (by grind)]
  simp [h.even]

lemma IsRotaryFan.isTriangle_getElem_fin' [NeZero F.length] (h : M.IsRotaryFan F b)
    (i : Fin F.length) :
    (M.bDual (b == i.1.bodd)).IsTriangle {F[(i - 1).1], F[i.1], F[(i + 1).1]} := by
  obtain rfl | hi0 := eq_or_ne i 0
  · rw! [val_zero, bodd_zero, zero_sub, neg_one, val_top, zero_add, h.isFan.val_one, beq_false]
    exact h.isTriad_end
  rw! [Fin.val_sub_one_of_ne_zero hi0]
  obtain rfl | htop := eq_or_ne i ⊤
  · rw! [top_add_one, val_top, h.length_sub_one_bodd, beq_true, val_zero, Nat.sub_sub,
      one_add_one_eq_two]
    exact h.isTriangle_end
  rw! [Fin.val_add_one_of_ne_top htop]
  obtain ⟨rfl | i, hi⟩ := i
  · simp at hi0
  have hiF : i + 1 ≠ F.length - 1 := by simpa [← Fin.val_inj] using htop
  cases b with simpa using h.isFan.isTriangle_getElem i

lemma IsRotaryFan.isTriangle_getElem_fin [NeZero F.length] (h : M.IsRotaryFan F b)
    (i : Fin F.length) :
    (M.bDual (b != i.1.bodd)).IsTriangle {F[i.1], F[(i + 1).1], F[(i + 2).1]} := by
  have _ := h.isFan.fact_one_lt_length
  cases b with simpa [add_assoc, bodd_val_add_of_even h.even] using
    h.isTriangle_getElem_fin' (i + 1)

lemma isRotaryFan_of_forall (M : Matroid α) (F : List α) [NeZero F.length] (b : Bool)
    (hF : 4 ≤ F.length) (hnd : F.Nodup) (hmod : ∀ i : Fin F.length,
      (M.bDual (b != i.1.bodd)).IsTriangle {F[i.1], F[(i + 1).1], F[(i + 2).1]}) :
    M.IsRotaryFan F b := by
  have : Fact (1 < F.length) := ⟨by lia⟩
  have hT : (M.bDual (b != F.length.bodd)).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]} := by
    specialize hmod (-2)
    rw! [Fin.val_neg', coe_ofNat_eq_mod, mod_eq_of_lt (show 2 < F.length by lia),
      mod_eq_of_lt (by lia), bodd_sub (by lia), bodd_two, Bool.bne_false,
        show (-2 : Fin F.length) + 1 = -1 by grind, Fin.neg_one, Fin.val_top,
        neg_add_cancel, val_zero] at hmod
    assumption
  obtain hodd | heven := F.length.bodd.eq_false_or_eq_true
  · obtain h4 | h5 := hF.eq_or_lt
    · simp [← h4] at hodd
    have hT' : (M.bDual b).IsTriangle {F[0], F[1], F[2]} := by
      simpa [Nat.mod_eq_of_lt (show 2 < F.length by lia)] using hmod 0
    have := hT.reverse.mem_or_mem_of_isCircuit_bDual (K := {F[0], F[1], F[2]})
      (by simpa [hodd] using hT'.isCircuit)
    simp only [Set.mem_insert_iff, hnd.getElem_inj_iff, _root_.zero_ne_one, mem_singleton_iff,
      OfNat.zero_ne_ofNat, or_self, or_false, pred_eq_succ_iff, zero_add, Nat.reduceAdd,
      forall_const] at this
    lia
  refine ⟨?_, by simpa [heven] using hT, ?_⟩
  · refine isFan_of_eq_of_forall_triangle_get (by lia) hnd (by simp [heven]) (by lia)
      fun i hi hi' ↦ ?_
    have hT := hmod (i - 1)
    rw! [Fin.bodd_val_sub_one hi, show i - 1 + 2 = i + 1 by grind, sub_add_cancel] at hT
    cases b with simpa using hT
  have hT := hmod ⊤
  rw! [val_top, bodd_sub (by lia), bodd_one, heven, Bool.false_bne, Bool.bne_true,
    ← Fin.one_add_one, ← add_assoc, top_add_one, val_zero, zero_add, Fin.val_one',
    one_mod'] at hT
  assumption

open Fin.NatCast in
lemma IsRotaryFan.rotate (h : M.IsRotaryFan F b) (n : ℕ) :
    M.IsRotaryFan (F.rotate n) (b != n.bodd) := by
  have _ : NeZero (F.rotate n).length := by simpa using h.isFan.neZero
  have _ := h.isFan.neZero
  refine isRotaryFan_of_forall _ _ _ (by simpa using h.length_ge) (by simpa using h.isFan.nodup)
    fun i ↦ ?_
  rw [rotate_getElem_fin, rotate_getElem_fin, rotate_getElem_fin, Fin.cast_add, Fin.cast_one,
    Fin.cast_add, Fin.cast_ofNat, add_right_comm, add_right_comm _ 2, Bool.bne_assoc,
    bne_comm (a := n.bodd)]
  have := h.isTriangle_getElem_fin (i.cast (by simp) + (n : Fin _))
  simpa [Fin.bodd_val_add_of_even h.even, mod_bodd h.even, Bool.bne_eq_xor] using this

lemma IsRotaryFan.reverse (h : M.IsRotaryFan F b) : M.IsRotaryFan F.reverse (!b) := by
  refine ⟨by simpa using h.isFan.reverse, ?_, ?_⟩
  · simp only [length_reverse, getElem_reverse, tsub_self, tsub_zero,
      show F.length - 1 - (F.length - 2) = 1 by grind]
    exact h.isTriad_end.reverse
  simp only [Bool.not_not, length_reverse, getElem_reverse, tsub_self, tsub_zero, Nat.sub_sub]
  exact h.isTriangle_end.reverse

lemma IsRotaryFan.dual (h : M.IsRotaryFan F b) : M✶.IsRotaryFan F (!b) :=
  ⟨by simpa using h.isFan.dual, by simpa using h.isTriangle_end, by simpa using h.isTriad_end⟩

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

lemma IsRotaryFan.eConn_eq (h : M.IsRotaryFan F b) : M.eConn {e | e ∈ F} = 0 := by
  refine h.isFan.eConn_eq_zero_of_mem_closure_mem_closure ?_ ?_
  · refine mem_of_mem_of_subset h.isTriad_end.mem_closure₂ <| closure_subset_closure _ ?_
    exact pair_subset (getElem_mem_tail _ (by grind) _) (getElem_mem_tail _ (by grind) _)
  refine mem_of_mem_of_subset h.isTriangle_end.mem_closure₂ <| closure_subset_closure _ ?_
  exact pair_subset (getElem_mem_dropLast (by grind)) (getElem_mem_dropLast (by grind))

/-- A rotary fan in a `2`-connected matroid is the entire ground set. -/
lemma IsRotaryFan.setOf_eq_ground (h : M.IsRotaryFan F b) (hM : M.TutteConnected 2) :
    {e | e ∈ F} = M.E := by
  have hne : M.Nonempty := ⟨F[0], h.isFan.subset_ground (by simp)⟩
  exact (hM.connected rfl.le).eq_ground_of_eConn_eq_zero h.eConn_eq ⟨F[0], by simp⟩
    h.isFan.subset_ground

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
  · exact ⟨_, by simp [insert_subset_iff], hF.isTriangle_end.isCircuit, by simp, by simp [← hi']⟩
  have hC := hF.isFan.isCircuit_interval (p := 0) (q := i + 1 + (!i.bodd).toNat) (by lia) (by grind)
    rfl (by simp) (by simp)
  refine ⟨_, by simp, hC, ?_, ?_⟩ <;>
  exact getElem_mem_image_getElem_preimage_val <| by simp

/-- A rotary fan is the entire matroid iff the matroid is connected. -/
lemma IsRotaryFan.setOf_eq_ground_iff (hF : M.IsRotaryFan F b) :
    {e | e ∈ F} = M.E ↔ M.Connected := by
  refine ⟨fun h ↦ ?_, fun h ↦ hF.setOf_eq_ground h.tutteConnected_two⟩
  rw [← M.restrict_ground_eq_self]
  exact h ▸ hF.restrict_connected

lemma IsRotaryFan.restrict_self (h : M.IsRotaryFan F b) : (M ↾ {e | e ∈ F}).IsRotaryFan F b := by
  have aux {c : Bool} {T} (hTF : T ⊆ {e | e ∈ F}) (hT : (M.bDual c).IsTriangle T) :
      ((M ↾ {e | e ∈ F}).bDual c).IsTriangle T := by
    obtain rfl | rfl := c
    · rwa [bDual_false, isTriangle_restrict_iff, and_iff_left hTF]
    rw [← Skew.contract_restrict_eq (X := M.E \ {e | e ∈ F}), restrict_eq_self_iff.2]
    · grw [bDual_true, dual_contract, isTriangle_delete_iff, and_iff_right (by simpa),
        sdiff_subset_compl, disjoint_compl_right_iff, hTF]
    · exact Eq.symm <| sdiff_sdiff_cancel_left h.isFan.subset_ground
    rw [skew_comm, ← eConn_eq_zero_iff_skew_compl h.isFan.subset_ground, h.eConn_eq]
  refine ⟨(isFan_iff_forall (by grind)).2 ?_, aux (by grind) h.isTriangle_end,
    aux (by grind) h.isTriad_end⟩
  simp only [Bool.beq_not_self, h.isFan.length_bodd_eq, h.isFan.nodup, true_and]
  exact fun i hi ↦ aux (by grind) <| h.isFan.isTriangle_getElem i hi

/-- This needs the length hypothesis, since a `4`-whirl has a weird parallel pair. -/
lemma IsRotaryFan.parallel_iff_eq (h : M.IsRotaryFan F b) (h4 : 4 < F.length) {i j}
    {hi : i < F.length} {hj : j < F.length} : M.Parallel F[i] F[j] ↔ i = j := by
  wlog hij : i < j generalizing i j with aux
  · obtain rfl | hne := eq_or_ne i j
    · simp [h.isFan.isNonloop (show F[i] ∈ F by simp)]
    rw [parallel_comm, aux (hj := hi) (hi := hj) (by lia), eq_comm]
  obtain rfl | j := j; lia
  induction i generalizing F j b with
  | zero =>
    suffices ¬ M.Parallel F[0] F[j + 1] by simpa
    intro hp
    obtain rfl | rfl := b
    · obtain ⟨hj0, hj1⟩ : j ≠ 0 ∧ j ≠ 1 := by simpa [h.isFan.nodup.getElem_inj_iff] using
        (h.isFan.isTriangle_getElem_of_eq 0 rfl).notMem_of_mem_of_parallel hp (by simp)
      obtain hjl : j + 1 = F.length - 1 := by
        simpa [h.isFan.nodup.getElem_inj_iff, hj0] using
        h.isTriad_end.isCircuit.mem_iff_mem_of_parallel_bDual hp
      have hwin := h.isTriangle_end.notMem_of_mem_of_parallel hp
      grind [h.isFan.nodup.getElem_inj_iff]
    have h1 := (h.isFan.isTriangle_bDual (by grind)).isCircuit.mem_iff_mem_of_parallel_bDual hp
    have h2 := h.isTriad_end.notMem_of_mem_of_parallel hp (by simp)
    have h3 := h.isTriangle_end.isCircuit.mem_iff_mem_of_parallel_bDual hp
    obtain ⟨rfl, h4⟩ : j = 1 ∧ F.length = 4 := by grind [h.isFan.nodup.getElem_inj_iff]
    have h4' := (h.isFan.isTriangle_getElem 2 (by lia)).isCircuit.mem_iff_mem_of_parallel_bDual
      hp.symm
    simp [h.isFan.nodup.getElem_inj_iff] at h4'
  | succ i ih =>
    obtain rfl | j := j; lia
    have hwin := ih (h.rotate 1) (j := j) (hj := by grind [length_rotate])
      (hi := by grind [length_rotate]) (by simpa) (by lia)
    simpa [getElem_rotate, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hwin

lemma IsRotaryFan.simple (h : M.IsRotaryFan F b) (h2 : M.TutteConnected 2) (h4 : 4 < F.length) :
    M.Simple := by
  simp only [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_not_isLoop,
    ← h.setOf_eq_ground h2, mem_ofPred_eq]
  refine ⟨fun e hf ↦ (h.isFan.isNonloop hf).not_isLoop, fun e f hef ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem (h.setOf_eq_ground h2 ▸ hef.mem_ground_left)
  obtain ⟨j, hj, rfl⟩ := getElem_of_mem (h.setOf_eq_ground h2 ▸ hef.mem_ground_right)
  simp_rw [(h.parallel_iff_eq h4).1 hef]

lemma IsRotaryFan.contract_delete (h : M.IsRotaryFan F false) (hlen : 4 < F.length) :
    (M ＼ {F[0]} ／ {F[1]}).IsRotaryFan F.tail.tail false := by
  obtain h5 | h6 := (show 5 ≤ F.length by lia).eq_or_lt
  · simpa [← congr_arg Nat.bodd h5] using h.even
  have hgr := @h.isFan.nodup.getElem_inj_iff
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' h6
  have hnb : n.bodd = false := by
    simpa [h.isFan.length_bodd_eq] using congr_arg Nat.bodd hn
  refine ⟨?_, ?_, ?_⟩
  ·
    have hwin := (h.isFan.delete_head (by lia) ?_ (by simp)).contract_head (by grind) ?_ (by simp)
      (by grind) (by grind)
    · simpa using hwin
    · simp [h.dual.parallel_iff_eq hlen]
    simp [delete_parallel_iff, h.parallel_iff_eq hlen]
  · simp only [bDual_false, length_tail, hn, Nat.add_one_sub_one, Nat.reduceSubDiff, getElem_tail,
      add_assoc, Nat.reduceAdd, zero_add]
    rw [isTriangle_iff, encard_insert_of_notMem (by grind), encard_pair (by grind),
      and_iff_left (show (2 : ℕ∞) + 1 = 3 from rfl)]
    refine IsCircuit.isCircuit_contractElem_of_insert ?_ (by grind) (by simp)
    rw [delete_isCircuit_iff, and_iff_left (by grind)]
    let k : ℕ := 0
    have hFr := (h.rotate (n + 4)).isFan
    rw [insert_comm, insert_comm F[1]]
    have hwin := hFr.isCircuit_quad 0 (by simpa) (by simpa) (by simp [show F.length ≠ 5 by lia])
    simpa [Nat.mod_eq_of_lt, (show n + 4 < F.length by lia),
      show 3 + (n + 4) = F.length + 1 by lia,
      show 4 + (n + 4) = F.length + 2 by lia, show 1 < F.length by lia,
      show 2 < F.length by lia, show 1 + (n + 4) = n + 5 by lia,
      show n + 5 < F.length by lia] using hwin
  suffices aux : (M✶ ／ {F[0]}).IsTriangle {F[n + 5], F[2], F[3]} by
    simpa [hn, add_assoc, h.isFan.nodup.getElem_inj_iff]
  rw [isTriangle_iff, encard_insert_of_notMem (by simp [h.isFan.nodup.getElem_inj_iff]),
    encard_pair (by simp [h.isFan.nodup.getElem_inj_iff]), and_iff_left two_add_one_eq_three]
  refine IsCircuit.isCircuit_contractElem_of_insert ?_ (by simp [h.isFan.nodup.getElem_inj_iff])
    (by simp)
  rw [insert_comm]
  have hFr := (h.rotate (n + 5)).isFan.dual
  have hC := hFr.isCircuit_quad 0 (by simpa) (by simpa) (by simp [show F.length ≠ 5 by lia])
  simpa [Nat.mod_eq_of_lt, show n + 5 < F.length by lia, show 1 + (n + 5) = F.length by lia,
    show 3 + (n + 5) = F.length + 2 by lia, show 4 + (n + 5) = F.length + 3 by lia,
    show 2 < F.length by lia, show 3 < F.length by lia] using hC

lemma IsRotaryFan.eRk_eq (hF : M.IsRotaryFan F b) : 2 * M.eRk {e | e ∈ F} = F.length := by
  have h1 := hF.isFan.eRk_ge
  have h2 := hF.dual.isFan.eRk_ge
  simp only [hF.even, Bool.toNat_false, Nat.cast_zero, add_zero] at h1 h2
  have heq := M.eRk_add_eRk_dual_eq _ hF.isFan.subset_ground
  rw [hF.eConn_eq, zero_add, hF.isFan.nodup.encard_toSet_eq] at heq
  enat_to_nat!; lia

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
  · exact (hM.connected (by simp)).eq_ground_of_eConn_eq_zero h0 ⟨F[0], by simp⟩ h.subset_ground
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
  simp [h.getElem_mem_ground, mem_dropLast_iff h.nodup h.ne_nil, getLast_eq_getElem]

lemma IsRotaryFan.joints_indep (h : M.IsRotaryFan F b) :
    M.Indep ((fun x ↦ F[x.1]) '' Fin.val ⁻¹' Nat.bodd ⁻¹' {b}) :=
  h.isFan.joints_indep (by simp +contextual)

def IsFanCircuit (F : List α) (b : Bool) (C : Set α) : Prop :=
    ∃ (k d : Fin F.length), k.1.bodd = b ∧ d.1.bodd = false ∧ d.1 ≠ 0
      ∧ C = (fun x ↦ F[(x + k).1]) '' Fin.val ⁻¹' ({0, d.1} ∪ (Iic d.1 ∩ Nat.bodd ⁻¹' {true}))

lemma isFanCircuit_iff [NeZero F.length] : IsFanCircuit F b C ↔
    ∃ (k d : Fin F.length), k.1.bodd = b ∧ d.1.bodd = false ∧ d.1 ≠ 0
      ∧ C = (fun x ↦ F[(x + k).1]) '' ({0, d} ∪ (Iic d) ∩ {i | i.1.bodd = true}) := by
  rw [IsFanCircuit]
  convert Iff.rfl with k d
  rw [show (0 : ℕ) = (0 : Fin F.length) from rfl, ← image_pair, ← image_val_Iic, preimage_union,
    preimage_inter, preimage_image_eq _ Fin.val_injective, preimage_image_eq _ Fin.val_injective,
    preimage_singleton, preimage_ofPred_eq]

open Fin.NatCast in
lemma IsFanCircuit.rotate (hF : F.length.bodd = false) (h : IsFanCircuit F b C) (s : ℕ) :
    IsFanCircuit (F.rotate s) (b != s.bodd) C := by
  obtain ⟨k, d, hkb, hd, hdF, hd0, hC⟩ := h
  have := k.neZero
  refine ⟨(k - s).cast (by simp), d.cast (by simp), ?_, by simpa, by simpa using hdF, ?_⟩
  · rw [val_cast, Fin.bodd_val_sub_of_even hF, Fin.val_natCast, mod_bodd hF, hkb]
  generalize_proofs hlt hlen h'
  have hrw : (fun x ↦ (F.rotate s)[(x + Fin.cast hlen (k - ↑s)).1]) =
      (fun x : Fin F.length ↦ F[(x + k).1]) ∘ (Fin.cast hlen.symm) := by
    ext i
    rw [rotate_getElem_fin]
    simp [Fin.cast_add, add_sub]
  rw! [hrw, image_comp, image_cast, ← preimage_comp, val_comp_cast, val_cast]
  rfl

lemma isFanCircuit_rotate_iff {s : ℕ} (hF : F.length.bodd = false) :
    IsFanCircuit (F.rotate s) b C ↔ IsFanCircuit F (b != s.bodd) C := by
  obtain h0 | hpos := _root_.eq_zero_or_pos F.length
  · simp [IsFanCircuit, length_eq_zero_iff.1 h0, Fin.exists_iff]
  wlog hle : s < F.length generalizing s with aux
  · simp_rw [← F.rotate_mod s, aux (mod_lt s hpos), mod_bodd hF]
  lift s to Fin F.length using hle
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using h.rotate (by simpa) s⟩
  replace h := h.rotate (by simpa) (-s).1
  rwa [List.rotate_rotate_neg_fin_self, Fin.bodd_val_neg_of_even hF] at h

lemma IsFanCircuit.reverse (hF : IsFanCircuit F b C) (hFodd : F.length.bodd = false) :
    IsFanCircuit F.reverse (!b) C := by
  obtain ⟨k, d, hkb, hdb, hd0, hC_eq⟩ := hF
  have := k.neZero
  have hl : Fact (1 < F.length) := ⟨by grind⟩
  -- define the equivalence that maps a circuit interval to itself.
  set eqv : Equiv.Perm (Fin F.length) := Fin.revPerm.trans (Equiv.addRight (d + 1)) with heqv
  have heqv1 : eqv.symm ⁻¹' (Fin.val ⁻¹' ({0, d.1} ∪ Iic d.1 ∩ bodd ⁻¹' {true})) =
      (Fin.val ⁻¹' ({0, d.1} ∪ Iic d.1 ∩ bodd ⁻¹' {true})) := by
    simp_rw [preimage_union, show (0 : ℕ) = (0 : Fin F.length) from rfl, ← image_pair,
      preimage_inter, ← Fin.image_val_Iic, Fin.val_injective.preimage_image]
    rw [← Equiv.image_eq_preimage_symm, image_pair, pair_comm]
    simp only [revPerm,  Equiv.trans_apply, Function.Involutive.coe_toPerm, Equiv.coe_addRight, eqv,
      ← add_assoc, rev_add_self, add_right_comm _ d, rev_zero_eq_top, top_add_one, zero_add,
      Equiv.symm_trans, Function.Involutive.toPerm_symm, Equiv.coe_trans,
      Function.Involutive.coe_toPerm, preimage_comp, preimage_rev_Iic, Equiv.addRight_symm]
    rw [Fin.preimage_add_Ici (by simp [rev_eq_neg, sub_eq_add_neg]), sub_neg_eq_add, ← add_assoc,
      rev_add_self, top_add_one, rev_neg, add_sub_cancel_right, Icc_zero_left]
    convert rfl
    simp only [preimage, mem_singleton_iff, mem_ofPred_eq, hFodd, bodd_val_rev_of_even,
      bodd_val_add_of_even, bodd_val_neg_of_even, hdb]
    simp
  refine ⟨(d + k).rev.cast (by simp), d.cast (by simp), ?_, by simpa, by simpa using hd0, ?_⟩
  · rw [val_cast, bodd_val_rev_of_even hFodd, bodd_val_add_of_even hFodd]
    simpa [hdb]
  generalize_proofs h1 h2
  have hrw : (fun x ↦ F.reverse[(x + Fin.cast h1 (d + k).rev).1]) =
      (fun x ↦ F[(x + k).1]) ∘ eqv ∘ (Fin.cast h1.symm) := by
    ext i

    simp only [Function.comp_apply, List.reverse_getElem_fin, Fin.rev_add,
      Fin.cast_sub, Fin.cast_cast, cast_eq_self, ← sub_add, Fin.cast_rev, heqv, rev_eq_neg,
      Equiv.addRight_add, Equiv.trans_apply, revPerm_apply, Equiv.Perm.coe_mul, Equiv.coe_addRight,
      Function.comp_apply]
    grind
  rw [hrw, hC_eq, image_comp, image_comp, Equiv.image_eq_preimage_symm, image_cast_fun, val_cast,
    ← preimage_comp, ← preimage_comp, ← Function.comp_assoc, val_comp_cast, preimage_comp,
    heqv1]

lemma isFanCircuit_reverse_iff (hF : F.length.bodd = false) :
    IsFanCircuit F.reverse b C ↔ IsFanCircuit F (!b) C :=
  ⟨fun h ↦ by simpa using h.reverse (by simpa), fun h ↦ by simpa using h.reverse hF⟩

lemma IsRotaryFan.exists_cojoint_notMem (hF : M.IsRotaryFan F b) (hM : M.TutteConnected 2)
    {C : Set α} (hC : M.IsNonspanningCircuit C)
    (hne : C ≠ (fun x ↦ F[x.1]) '' Fin.val ⁻¹' (Nat.bodd ⁻¹' {!b})) :
    ∃ k : Fin F.length, k.1.bodd = !b ∧ F[k.1] ∉ C := by
  by_contra! hcon
  have hss : (fun x ↦ F[x.1]) '' Fin.val ⁻¹' (Nat.bodd ⁻¹' {!b}) ⊂ C :=
    ssubset_of_subset_of_ne (by simpa [preimage]) hne.symm
  have hlt := Finite.encard_lt_encard (Finite.subset (by simp) (image_subset_range ..)) hss
  grw [← hC.isCircuit.eRk_add_one_eq, hC.nonspanning.eRk_add_one_le,
      ← M.eRk_ground, ← hF.setOf_eq_ground hM,
    ← ENat.mul_lt_mul_left_iff (c := 2) (by simp) (by simp), hF.eRk_eq,
    hF.isFan.nodup.injective_getElem_fin.encard_image, ← preimage_inter_range,
    encard_preimage_of_injective_subset_range Fin.val_injective (by simp), range_val, inter_comm,
    Set.preimage_singleton, encard_Iio_inter_bodd_of_even hF.even] at hlt
  exact hlt.ne rfl

open Fin.NatCast in
lemma IsRotaryFan.exists_joint_mem_cojoint_notMem [NeZero F.length] (hF : M.IsRotaryFan F b)
    (hM : M.TutteConnected 2) {C : Set α} (hC : M.IsNonspanningCircuit C)
    (hne : C ≠ (fun x ↦ F[x.1]) '' Fin.val ⁻¹' (Nat.bodd ⁻¹' {!b})) :
    ∃ (i : Fin F.length), i.1.bodd = b ∧ F[i.1] ∈ C ∧ F[(i - 1).1] ∉ C := by
  replace hne : ∃ k : Fin F.length, k.1.bodd = !b ∧ F[k.1] ∉ C := hF.exists_cojoint_notMem hM hC hne
  have hnz := hF.isFan.neZero
  have hex1 : ∃ i : Fin F.length, i.1.bodd = b ∧ F[i.1] ∈ C := by
    by_contra! hcon
    obtain ⟨k, hkb, hkC⟩ := hne
    have hi := hF.isFan.indep_of_ssubset_cojoints
      (I := (fun x ↦ F[x.1]) '' Fin.val ⁻¹' (Nat.bodd ⁻¹' {!b} \ {k.1})) ?_
    · refine (hi.subset ?_).not_dep hC.isCircuit.dep
      intro e heC
      obtain ⟨i, hi, rfl⟩ := get_of_mem
        ((hC.subset_ground.trans_eq (hF.setOf_eq_ground hM).symm) heC)
      exact getElem_mem_image_getElem_preimage_val ⟨by grind, by grind⟩
    rw [← hF.isFan.nodup.image_getElem_preimage_val_sdiff_singleton _ k.2]
    exact sdiff_singleton_ssubset.2 <| getElem_mem_image_getElem_preimage_val hkb
  obtain ⟨i₀, hi₀, hi₀C⟩ := hex1
  contrapose! hne
  suffices aux : ∀ (u : ℕ), u.bodd = true → F[(i₀ - u).1] ∈ C by
    intro k hk
    simpa using aux (i₀ - k).1 (by simp [bodd_val_sub_of_even hF.even, hk, hi₀])
  intro u hu
  induction u using Nat.twoStepInduction with
  | zero => simp at hu
  | one => exact hne i₀ hi₀ hi₀C
  | more n ih _ =>
    have hwin := (hF.isTriangle_getElem_fin (i₀ - n - 2)).reverse.mem_or_mem_of_isCircuit_bDual
      (K := C)
    simp only [bodd_succ, Bool.not_not] at hu
    obtain h | h : F[(i₀ - n - 2 + 1).1] ∈ C ∨ F[(i₀ - n - 2).1] ∈ C := by
      simpa [hF.even, bodd_val_sub_of_even, mod_bodd, hu, hi₀, hC.isCircuit, ih hu] using hwin
    · simpa [← sub_sub] using hne _
        (by simpa [hF.even, bodd_val_add_of_even, bodd_val_sub_of_even, mod_bodd, hu]) h
    simpa [sub_sub] using h

lemma IsRotaryFan.isFanCircuit_of_isNonspanningCircuit [NeZero F.length] (hF : M.IsRotaryFan F b)
    (hM : M.TutteConnected 2) {C : Set α} (hC : M.IsNonspanningCircuit C)
    (hne : C ≠ (fun x ↦ F[x.1]) '' Fin.val ⁻¹' (Nat.bodd ⁻¹' {!b})) : IsFanCircuit F b C := by
  obtain ⟨i, hib, hiC, hiC'⟩ := hF.exists_joint_mem_cojoint_notMem hM hC hne
  clear hne
  wlog hi : i = 1 generalizing F b with aux
  · have hnz := (hF.rotate (i - 1).1).isFan.neZero
    have := hF.isFan.fact_one_lt_length
    specialize aux (hF.rotate (i - 1).1) 1 (by simp [bodd_val_sub_of_even hF.even, hib]) ?_
      (by simpa) rfl
    · rw [rotate_getElem_fin]
      simpa
    simpa [isFanCircuit_rotate_iff hF.even] using aux
  have := hF.isFan.fact_one_lt_length
  subst hi
  simp at hib
  obtain rfl : b = true := by simpa using hib
  by_cases! hex : ∃ (j : Fin F.length), j ≠ 1 ∧ j.1.bodd = true ∧ F[j.1] ∈ C
  · obtain ⟨j, hj1, hj, hjC⟩ := hex
    have hC_eq := hF.isFan.eq_interval_of_notMem_mem_mem
      sorry j.2 rfl (by simpa [bodd_val_neg_of_even, hF.even]) hC.isCircuit
        (by simpa using hiC') (by simpa using hiC) hjC
    rw [show true = (false != bodd (1 : Fin F.length)) by simp, ← isFanCircuit_rotate_iff hF.even]
    have := (hF.rotate (1 : Fin F.length)).isFan.fact_one_lt_length
    have hj1 : 1 ≤ (j - 1).rev := by
      simp [rev_eq_neg, show - 1 - (j - 1) = - j by grind, Fin.one_le_iff_ne_zero]
      grind
    refine ⟨0, (j - 1).cast (by simp), by simp, by simpa [hF.even, bodd_val_sub_of_even],
      (by simpa [sub_eq_zero]), ?_⟩
    simp_rw [add_zero]
    rw [preimage_union, image_union, val_cast, List.image_getElem_preimage_val_rotate,
      preimage_inter, image_inter (hF.rotate _).isFan.nodup.injective_getElem_fin,
      List.image_getElem_preimage_val_rotate', List.image_getElem_preimage_val_rotate',
      show (0 : ℕ) = (0 : Fin F.length) from rfl, ← image_pair,  ← Fin.image_val_Iic,
      preimage_image_eq _ Fin.val_injective, preimage_image_eq _ Fin.val_injective,
      preimage_singleton, preimage_ofPred_eq, preimage_ofPred_eq, image_pair,
      preimage_sub_Iic hj1, sub_add_cancel, ← image_inter hF.isFan.nodup.injective_getElem_fin,
      ← image_union, zero_add]
    rw [preimage_union, show (0 + 1 : ℕ) = (1 : Fin F.length) by simp, ← image_pair,
      preimage_inter, ← image_val_Icc, preimage_image_eq _ Fin.val_injective,
      preimage_image_eq _ Fin.val_injective, preimage_singleton, Bool.not_true] at hC_eq
    simpa [hF.even, bodd_val_sub_of_even]

  -- have := (hF.isFan.cojoint_mem_of_subsingleton_joint_mem_le (p := 1)


#exit

lemma IsRotaryFan.aegahjkdsf (h : M.IsRotaryFan F b) (hM : M.TutteConnected 2) {C : Set α}
    (hC : M.IsNonspanningCircuit C) (hne : C ≠ F.getElems {i | i.bodd = !b}) :
    ∃ (k d : ℕ), k.bodd = b ∧ d.bodd = false ∧ d < F.length
    ∧ C = ((F.rotate k).getElems (insert 0 (insert d (Iio d ∩ {i | i.bodd = true})))) := by
  wlog h0 : F[0] ∈ C ∧ b = false generalizing F b with aux
  · have hnss : ¬ C ⊆ F.getElems {i | i.bodd = !b} := fun hnss ↦ hC.isCircuit.not_indep <|
      h.isFan.indep_of_ssubset_cojoints <| hnss.ssubset_of_ne hne
    obtain ⟨a, ha, hab⟩ := not_subset.1 hnss
    obtain ⟨i, hi, rfl⟩ := getElem_of_mem <|
      hC.subset_ground.trans_eq (h.setOf_eq_ground hM).symm ha
    obtain hib : i.bodd = b := by simpa [h.isFan.nodup.getElem_mem_getElems_iff] using hab
    obtain ⟨k, d, hkb, hd, hdF, hC_eq⟩ := aux (h.rotate i)
      (by cases b with simpa [getElems_rotate_bodd _ _ _ h.even]) <|
      by simpa [hib, Nat.mod_eq_of_lt hi]
    exact ⟨i + k, d, by simp [hkb], hd, by simpa using hdF, by simpa using hC_eq⟩
  obtain ⟨h0C, rfl⟩ := h0
  -- have hnss : ¬ (F.getElems {i | i.bodd = true}) ⊆ C := sorry
  -- simp only [getElems_subset_iff, mem_ofPred_eq, not_forall, Classical.not_imp,
  --   exists_and_left] at hnss
  -- by_cases h1 : F[1] ∈ C
  -- · refine False.elim <| hnss <| getElems_subset_iff.2 fun i hi hib ↦ ?_
  --   refine h.isFan.cojoint_mem_of_subsingleton_joint_mem_le (by grind)
  --     rfl hC.isCircuit ?_ h1 (by grind) hi (by simpa using hib)




  wlog h1 : F[1] ∈ C generalizing F with aux
  · have hlC : F[F.length - 1] ∈ C :=
      by rwa [h.isTriad_end.reverse.mem_iff_mem_of_isCircuit_bDual hC.isCircuit h1] at h0C

    specialize aux (h.rotate 1).reverse ?_ ?_ ?_
    · rw [getElems_reverse_bodd, getElems_rotate_bodd _ _ _ h.even]
      simpa [h.even]
    · simpa [Nat.sub_add_cancel (show 1 ≤ F.length by grind)]
    · simpa [show F.length - 1 - 1 + 1 = F.length - 1 by grind]
    obtain ⟨k, d, hk, hd, hdlt, hC_eq⟩ := aux
    simp_rw [reverse_rotate, Nat.mod_eq_of_lt (show 1 < F.length by grind), rotate_rotate] at hC_eq
    rw [getElems_insert _ _ (by grind), getElems_insert _ _ (by simpa using hdlt)] at hC_eq

    rw! [getElem_rotate, getElem_rotate, length_reverse, zero_add, Nodup.getElems_inter,
      getElem_reverse' (j := k % F.length), getElems_rotate_bodd, getElems_reverse_bodd,
        getElems_rotate, length_reverse, getElem_reverse' (j := (d + k) % F.length)] at hC_eq

    rw! [rotate_reverse, getElem_reverse, Nat.sub_zero, length_rotate, getElem_rotate] at hC_eq

      -- getElems_insert _ _ (by grind), getElems_insert _ _ (by simpa using hdlt),
      -- getElem_rotate] at hC_eq
    refine ⟨41, d, sorry, hd, (by simpa using hdlt), ?_⟩
    -- rw [rotate_reverse, length_rotate, rotate_rotate, getElems_insert] at hC_eq

    simp at hC_eq
    rw [getElems_rotate_of_subset sorry]



      -- simp_rw [Nat.sub_add_cancel (show 1 ≤ F.length by lia)]



  -- wlog h0 : F[0] ∈ C ∧ F[1] ∈ C ∧ b = false generalizing F b with aux
  -- · have hnss : ¬ C ⊆ F.getElems {i | i.bodd = !b} := fun hnss ↦ hC.isCircuit.not_indep <|
  --     h.isFan.indep_of_ssubset_cojoints <| hnss.ssubset_of_ne hne
  --   obtain ⟨a, ha, hab⟩ := not_subset.1 hnss
  --   obtain ⟨i, hi, rfl⟩ := getElem_of_mem <|
  --     hC.subset_ground.trans_eq (h.setOf_eq_ground hM).symm ha
  --   obtain hib : i.bodd = b := by simpa [h.isFan.nodup.getElem_mem_getElems_iff] using hab
  --   by_cases hi1 : F[(i + 1) % F.length] ∈ C
  --   · obtain ⟨k, d, hk, hd, hdlt, hC_eq⟩ :=
  --       aux (h.rotate i) (by cases b with simpa [getElems_rotate_bodd _ _ _ h.even])
  --       ⟨by simpa [mod_eq_of_lt hi], by simp [add_comm, hi1], by simp [hib]⟩
  --     exact ⟨i + k, d, (by simp [hk]), hd, by simpa using hdlt, by simpa using hC_eq⟩
  --   have hT := (h.isTriangle (i + (F.length - 1))).reverse
  --   simp only [bodd_add, hib, h.length_sub_one_bodd, Bool.bne_true, Bool.bne_not, bne_self_eq_false,
  --     Bool.not_false, bDual_true, dual_isTriangle_iff] at hT
  --   have hmem := hT.mem_iff_mem_of_isCircuit hC.isCircuit
  --   simp only [show i + (F.length - 1) + 2 = i + 1 + F.length by lia, add_mod_right, hi1,
  --     not_false_eq_true, show i + (F.length - 1) + 1 = i + F.length by lia, mod_eq_of_lt hi, ha,
  --     true_iff, forall_const] at hmem
  --   obtain ⟨j, hj⟩ := exists_add_of_le (show i + 1 ≤ F.length by lia)
  --   have auxj1 : (0 + j) % F.reverse.length + i + 1 = F.length := by
  --     rw [Nat.mod_eq_of_lt (by grind), zero_add, hj, add_assoc, add_comm]
  --   have auxj : (1 + j) % F.reverse.length + (i + (F.length - 1)) % F.length + 1 = F.length := by
  --     obtain rfl | i := i
  --     · simp [show F.length = 1 + j by grind, add_comm]
  --     rw [length_reverse, Nat.mod_eq_of_lt (by grind),
  --       show (i + 1 + (F.length - 1)) = F.length + i by lia, add_mod_left,
  --       Nat.mod_eq_of_lt (by lia)]
  --     lia
  --   have hjb : j.bodd = !b := sorry
  --   obtain ⟨k, d, hkb, hdb, hd, hC_eq⟩ := aux (h.reverse.rotate j) ?_ ⟨?_, ?_, ?_⟩
  --   · refine ⟨17, d, sorry, hdb, (by simpa using hd), ?_⟩
  --     _
  --   · simpa [hib, getElems_rotate_bodd _ _ _ h.reverse.even, getElems_reverse_bodd,
  --       h.even]
  --   · rwa [getElem_rotate, getElem_reverse' auxj1]
  --   · rwa [getElem_rotate, getElem_reverse' auxj]
  --   simp [hjb]


#exit
    -- · sorry
    -- · simpa [hib, getElems_rotate_bodd _ _ _ h.reverse.even, getElems_reverse_bodd,
    --     h.even, getElem_reverse' (show j + i + 1 = F.length by lia)]
    -- ·
    --   simpa [getElem_rotate, zero_add, length_reverse,
    --     Nat.mod_eq_of_lt (show j < F.length by lia), getElem_reverse' auxj]
    -- · sorry

    -- · simp_rw [getElem_rotate, zero_add, length_reverse,
    --     Nat.mod_eq_of_lt (show j < F.length by lia), ]
    -- simp_rw [getElem_rotate, zero_add, length_reverse,
    --   Nat.mod_eq_of_lt (show j < F.length by lia),
    --     getElem_reverse' (show j + i + 1 = F.length by lia)]
    -- simp_rw [getElem_rotate, zero_add, length_reverse, Nat.mod_eq_of_lt,
    --   show F.length - 1 - i < F.length by lia]
    -- simp_rw [rotate_reverse, mod_eq_of_lt (show F.length - 1 - i < F.length by lia),
    --   show F.length - (F.length - 1 - i) = i + 1 by lia, getElem_reverse, length_rotate,
    --   getElem_rotate]
    -- -- show F.length - (F.length - 1 - i)]

    -- ·
    --   _
    -- convert hi1 using 3
    -- rw [show i + (F.length - 1) + 2 = i + 1 + F.length by lia, add_mod_right]












  -- have hcard : 2 * C.encard ≤ F.length := by
  --   grw [← hC.isCircuit.eRk_add_one_eq, hC.nonspanning.eRk_add_one_le, ← eRk_ground,
  --     ← h.setOf_eq_ground hM, h.eRk_eq]
  -- replace hnss : ¬ (F.getElems {i | i.bodd = !b}) ⊆ C := by
  --   contrapose! hnss
  --   refine Eq.symm <| Finite.eq_of_subset_of_encard_le ?_ hnss ?_
  --   · exact (finite_toSet F).subset <| getElems_subset_toSet ..
  --   rwa [← ENat.mul_le_mul_left_iff (show 2 ≠ 0 by simp) (by simp),
  --     h.isFan.nodup.getElems_bodd_encard_of_even _ h.even]


  -- by_cases! h1 : ∃ (p : ℕ) (hpb : p.bodd = b),
  --     ∀ i (hi : i < F.length), i.bodd = b → F[i] ∈ C → i = p
  -- ·


    -- wlog hp2 : p = 2 generalizing F b p with aux
    -- · have hrw := bodd_sub (show 2 ≤ F.length + p by grind)
    --   have aux' :
    --     (∀ (i : ℕ) (hi : i < F.length), i.bodd = false →
    --       F[(i + (F.length + p - 2)) % F.length] ∈ C → i = 2) := by
    --     refine fun i hi hodd hiC ↦ ?_
    --     have := hp _ (mod_lt _ (by grind)) ?_ hiC
    --     ·
    --     simp [mod_bodd, hrw, hpb, h.even, hodd]



    --   specialize aux (p := 2) (h.rotate (F.length + p - 2))
    --   simp [getElems_rotate_bodd, hrw, hpb, hnss, h.even, mod_bodd] at aux
    --     -- (by simpa [getElems_rotate_bodd _ _ _ h.even, hrw, hpb])
    --     -- (by simp [hpb, hrw, h.even]) ?_ rfl





    --   sorry

    --   sorry

    --   have := aux (p := 2) (h.rotate (F.length + p - 2)) sorry sorry
    --   simp [bodd_sub (show 2 ≤ F.length + p by grind), hpb, h.even] at this
    --   -- simp [getElems_rotate_bodd, bodd_sub (show 2 ≤ F.length + p by grind), hpb,
    --   --   h.even, hnss] at this
    have foo : ∀



    grw [← hC.isCircuit.eRk_add_one_eq, hC.nonspanning.eRk_add_one_le,
      ← ENat.mul_le_mul_left_iff (show 2 ≠ 0 by simp) (by simp),
      h.isFan.nodup.getElems_bodd_encard_of_even _ h.even, ← eRk_ground,
      ← h.setOf_eq_ground hM, h.eRk_eq]
  simp only [getElems_subset_iff, mem_ofPred_eq, not_forall, exists_prop, exists_and_left] at hnss
  obtain ⟨p, hp, hpn, hpC⟩ := hnss
  wlog hp0 : p = 0 generalizing F b p with aux
  · obtain ⟨k, d, hk, hd, hdF, rfl⟩ := aux (h.rotate p) 0 (by simp [hp]) (by grind [length_rotate])
      (by simpa [mod_eq_of_lt hpn]) rfl
    have hkb : k.bodd = true := by simpa [hp] using hk
    refine ⟨p + k, d, (by simp [hp, hkb]), hd, by simpa using hdF, by simp⟩
  subst hp0
  obtain rfl : b = true := by simpa using hp




    -- simp [hp, mod_eq_of_lt hlen] at this
    -- simp [hp, Nat.bodd_sub hlen.le, h.even] at this
  -- wlog hb : b = false generalizing F b with aux
  -- · obtain ⟨k, d, hkb, hdb, hd, rfl⟩ :=
  --     aux (h.rotate 1) (by simpa [getElems_rotate_bodd _ _ _ h.even]) (by grind)
  --   exact ⟨k + 1, d, by simpa using hkb, hdb, by simpa using hd, by simp [add_comm 1]⟩
  -- subst hb








  wlog foo : b = false ∧ F[F.length - 1] ∉ C generalizing F with aux
  ·

/-- Any nonspanning circuit in a rotary fan will contain some cojoint, and not contain
two other cojoints. -/
lemma IsRotaryFan.exists_btw_of_isNonspanningCircuit (h : M.IsRotaryFan F b) {C : Set α}
    (hM : M.TutteConnected 2) (hC : M.IsNonspanningCircuit C)
    (hnss : C ≠ F.getElems {i | i.bodd = !b}) : ∃ (p q r : ℕ) (hpq : p < q)
    (hq : q < F.length) (hr : r < F.length), p.bodd = !b ∧ q.bodd = !b ∧ r.bodd = !b ∧
    F[p] ∉ C ∧ F[q] ∉ C ∧ F[r] ∈ C := by
  wlog hb : b = false generalizing F b with aux
  · obtain ⟨p, q, r, hpq, hq, hr, hpb, hqb, hrb, hpC, hqC, hrC⟩ :=
      aux h.reverse (by simpa [getElems_reverse_bodd, h.even]) (by grind)
    simp only [getElem_reverse, Nat.sub_sub] at hpC hrC hqC
    simp only [length_reverse] at hq hr
    refine ⟨F.length - (1 + q), F.length - (1 + p), F.length - (1 + r), by lia, by lia,
      by lia, ?_⟩
    rw [bodd_sub (by lia), bodd_sub (by lia), bodd_sub (by lia)]
    simp [hpC, hrC, hqC, h.even, hpb, hqb, hrb]
  obtain rfl := hb








  -- obtain ⟨I, hI, rfl⟩ :=
  --   exists_eq_getElems <| hC.subset_ground.trans_eq <| (h.setOf_eq_ground hM).symm
  -- simp_rw [h.isFan.nodup.getElem_mem_getElems_iff]
  -- obtain ⟨r, hrI, hrb⟩ : ∃ r ∈ I, r.bodd = !b := by
  --   by_contra! hcon
  --   exact hC.isCircuit.not_indep <| h.joints_indep.subset <| getElems_mono _ <| by grind
  -- have hiF (d) : 2 * (Iio F.length ∩ {i | i.bodd = d}).encard = ↑F.length := by
  --   simpa [h.even] using encard_Iio_inter_bodd F.length d
  -- have hIcard := hC.nonspanning.eRk_add_one_le
  -- rw [hC.isCircuit.eRk_add_one_eq, ← eRk_ground, ← h.setOf_eq_ground hM,
  --     ← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), h.eRk_eq,
  --     h.isFan.nodup.getElems_encard_eq, inter_eq_self_of_subset_left hI] at hIcard
  -- -- grw [← encard_sdiff_add_encard_inter (t := {i | i.bodd = b})] at hIcard
  -- obtain ⟨p, hp, hpb, hpI⟩ : ∃ p < F.length, p.bodd = !b ∧ p ∉ I := by
  --   contrapose! hnss
  --   rw [h.isFan.nodup.getElems_eq_getElems_iff, inter_eq_self_of_subset_left hI, eq_comm]
  --   refine ((finite_Iio _).inter_of_right _).eq_of_subset_of_encard_le (by grind) ?_
  --   grw [← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), hIcard, inter_comm, ← hiF]

  -- suffices aux : ∃ q ≠ p, q < F.length ∧ q.bodd = !b ∧ q ∉ I by
  --   obtain ⟨q, hqp, hq, hqb, hqI⟩ := aux
  --   exact ⟨min p q, max p q, r, by grind⟩

  -- by_contra! hcon
  -- have hss : ((Iio F.length) ∩ {i | i.bodd = !b}) \ {p} ⊆ I := by grind
  -- have hss' : ((Iio F.length) ∩ {i | i.bodd = !b}) \ {p} ⊆ I ∩ {i | i.bodd = !b} := by grind
  -- -- have hcard : 2 * (((Iio F.length) ∩ {i | i.bodd = !b}) \ {p}).encard + 2 = 17 := by
  -- --   rw [← mul_]
  -- grw [← encard_sdiff_add_encard_inter (t := {i | i.bodd = !b}), ← hss',
  --   ← ENat.add_le_add_iff_right (k := 2 * 1) (by simp), ← mul_add, add_assoc,
  --   encard_sdiff_singleton_add_one (by grind), mul_add, hiF, add_comm,
  --   add_le_add_iff_right_of_ne_top (by simp), ENat.mul_le_mul_left_iff (by simp) (by simp),
  --   encard_le_one_iff_subsingleton] at hIcard

  -- have hC1 := h.isTriangle p
  -- have hC2 := h.isTriangle (p + (F.length - 2))

  -- have himp1 : (p + 2) % F.length ∈ I → (p + 1) % F.length ∈ I := by
  --   simpa [h.isFan.nodup.getElem_mem_getElems_iff, Nat.mod_eq_of_lt hp, hpI] using
  --     hC1.reverse.mem_or_mem_of_isCircuit_bDual (K := F.getElems I)
  --     (by simpa [hpb] using hC.isCircuit)
  -- have := hC2.mem_or_mem_of_isCircuit_bDual (K := F.getElems I)
  --     (by simpa [hpb, h.length_sub_two_bodd] using hC.isCircuit)
  -- simp [h.isFan.nodup.getElem_mem_getElems_iff] at this


  --   -- grw [← inter_eq_self_of_subset_left hI] at hIcard
  --   -- grw [← encard_sdiff_add_encard_inter (t := {i | i.bodd = b}),
  --   --   ← encard_le_encard (s := {r}) (by simp [hrI, hrb]),
  --   --   ← inter_eq_self_of_subset_left hI, inter_assoc] at hIcard
  --   -- sorry


  --   _

  -- suffices aux : ∃ p q, p < F.length ∧ q < F.length ∧
  --     p.bodd = !b ∧ q.bodd = !b ∧ p ∉ I ∧ q ∉ I ∧ p ≠ q by
  --   obtain ⟨p, q, hplt, hqlt, hp, hq, hpI, hqI, hpq⟩ := aux
  --   exact ⟨min p q, max p q, r, by grind⟩

  -- obtain hss | hnt := ((Iio F.length \ {i | i.bodd = !b}) \ I).subsingleton_or_nontrivial
  -- · have hiF : 2 * (Iio F.length ∩ {i | i.bodd = b}).encard = ↑F.length := by
  --     simpa [h.even] using encard_Iio_inter_bodd F.length b
  --   have hc := (encard_sdiff_add_encard_inter (Iio F.length \ {i | i.bodd = !b}) I).ge

  --   grw [encard_le_one_iff_subsingleton.2 hss,
  --     sdiff_eq, compl_ofPred, ← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp)] at hc
  --   simp only [Bool.not_eq_not, mul_add, mul_one, hiF] at hc

  --   -- rw [hiF] at hc
  --   have hr := hC.nonspanning.eRk_add_one_le
  --   rw [hC.isCircuit.eRk_add_one_eq, ← eRk_ground, ← h.setOf_eq_ground hM,
  --     ← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), h.eRk_eq,
  --     h.isFan.nodup.getElems_encard_eq, inter_eq_self_of_subset_left hI] at hr
  --   grw [← hr] at hc
  --   -- have hrw := (encard_sdiff_add_encard_inter (Iio F.length \ I) {i | i.bodd = !b}).ge
  --   -- replace hrw := add_le_add_left hrw I.encard

  --   -- have := encard_le_one_iff_subsingleton.2 hss
  --   -- grw [this, encard_sdiff_add_encard_of_subset hI, Nat.encard_Iio, ← hr] at hrw

  --   -- have foo := encard_sdiff_add_encard (t := (Iio F.length \ I))
  --   --   (s := (Iio F.length \ I) ∩ {i | i.bodd = !b}) (by simp)



  --   -- grw [← encard_le_encard (s := I ∩ {i |  i.bodd = !b}) (by simp)] at hr
  --   -- rw [← encard_sdiff_add_encard_of_subset (s := {i ∈ I | i.bodd = !b}) (by simp)] at hr



  -- -- have hr : ∃ (r : ℕ) (hr : r < F.length), r.bodd = !b ∧ F[r] ∈ C
  -- -- ·

  --   -- p.bodd = !b) p < q
    -- ∃ (p q r : ZMod n), btw p q r ∧ p ≠ q ∧ p ≠ r ∧ J true p ∉ C ∧ J true q ∈ C ∧ J true r ∉ C := by

lemma IsRotaryFan.foo (h : M.IsRotaryFan F b) (hM : M.TutteConnected 2) {C : Set α}
    (hC : M.IsNonspanningCircuit C) (hne : C ≠ F.getElems {i | i.bodd = !b}) :
    ∃ (p q : ℕ) (hp : p < F.length) (hpq : p < q) (hq : q < F.length) (hpb : p.bodd = b)
    (hqb : q.bodd = b), C = F.getElems (insert p <| insert q <| {i ∈ Ico p q | i.bodd = !b})
    ∨ C = F.getElems (insert p <| insert q <| {i ∈ Iio p ∪ Ico q F.length | i.bodd = !b}) := by
  _
