import Matroid.Connectivity.Fan.Circuit
import Matroid.Connectivity.Separation.Tutte
import Mathlib.Data.ZMod.Basic

open Set List Nat

namespace Matroid

variable {α β : Type*} {F : List α} {b c d : Bool} {M : Matroid α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

structure IsRotaryFan (M : Matroid α) (F : List α) (b : Bool) : Prop where
  isFan : M.IsFan F b (!b)
  isTriangle_end : (M.bDual b).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]}
  isTriad_end : (M.bDual (!b)).IsTriangle {F[F.length - 1], F[0], F[1]}

attribute [grind →] IsRotaryFan.isFan

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| exact @ZMod.val_lt _ ⟨by grind⟩ ..)

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| exact Nat.mod_lt _ (by grind))

-- @[grind =>]
-- lemma foo (F : List α) (hF : 0 < F.length) (i : ZMod F.length) : i.val < F.length := by
--   have : NeZero F.length := ⟨hF.ne.symm⟩
--   apply ZMod.val_lt

@[grind =>]
lemma IsFan.mod_lt (hF : M.IsFan F b c) (i : ℕ) : i % F.length < F.length :=
  Nat.mod_lt _ (by grind)

-- attribute [grind =>] Nat.mod_lt

lemma Nat.mod_add_sub {b n : ℕ} (a : ℕ) (hb : b ≤ n) (hb0 : b ≠ 0) :
    (a + n - (a + b) % n) % n + b = n := by
  have aux {i} : i % n < n := Nat.mod_lt (y := n) i (by lia)
  rw [Nat.add_sub_assoc aux.le, ← mod_add_mod, ← mod_add_mod a]
  obtain hlt | hle := lt_or_ge (a % n + b) n
  · rw [Nat.mod_eq_of_lt hlt, show a % n + (n - (a % n + b)) = n - b by lia,
      Nat.mod_eq_of_lt (by lia), Nat.sub_add_cancel hb]
  obtain ⟨d, hd⟩ := exists_add_of_le hle
  have hdn : d < n := by grw [← add_lt_add_iff_left (a := n), ← hd, aux, hb]
  rw [hd, Nat.add_mod_left, Nat.mod_eq_of_lt hdn, ← Nat.add_sub_cancel (a % n + (n - d)) b,
    add_right_comm, hd, show n + d + (n - d) - b = n + (n - b) by lia, Nat.add_mod_left,
    mod_eq_of_lt (by lia), Nat.sub_add_cancel hb]

lemma ZMod.val_ofNat_of_lt {i n : ℕ} [i.AtLeastTwo] (hin : i < n) :
    (ofNat(i) : ZMod n).val = i := by
  rw [ZMod.val_ofNat, Nat.mod_eq_of_lt (by simpa)]
  exact Nat.add_zero i

lemma ZMod.ofNat_eq_zero {i n : ℕ} [i.AtLeastTwo] : (ofNat(i) : ZMod n) = 0 ↔ (n ∣ i) := by
  rw [← ZMod.val_eq_zero, ZMod.val_ofNat, ← Nat.dvd_iff_mod_eq_zero]
  simp [OfNat.ofNat]

lemma ZMod.ofNat_ne_zero_of_lt {i n : ℕ} [i.AtLeastTwo] (hin : i < n) :
    (ofNat(i) : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.ofNat_eq_zero]
  contrapose! hin
  exact Nat.le_of_dvd (Nat.pos_of_neZero i) hin

lemma ZMod.val_succ [NeZero n] (i : ZMod n) (hi : i ≠ -1) : (i + 1).val = i.val + 1 := by
  obtain rfl | rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact False.elim <| hi <| Subsingleton.elim (α := Fin 1) ..
  rw [ZMod.val_add, ZMod.val_one'' (by simp), Nat.mod_eq_of_lt]
  obtain heq | hne := (Nat.add_one_le_of_lt i.val_lt).eq_or_lt
  · contrapose! hi
    refine ZMod.val_injective _ ?_
    rw [ZMod.val_neg_one]
    lia
  assumption

@[simp]
lemma ZMod.one_eq_zero {n : ℕ} : (1 : ZMod n) = 0 ↔ n = 1 := by
  simp [← ZMod.val_eq_zero, ZMod.val_one_eq_one_mod]

lemma ZMod.val_neg_eq_sub {n : ℕ} [NeZero n] (a : ZMod n) (ha : a ≠ 0) : (-a).val = n - a.val :=
  @ZMod.val_neg_of_ne_zero n _ a ⟨ha⟩

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

lemma IsRotaryFan.length_bodd (h : M.IsRotaryFan F b) : F.length.bodd = false := by
  simpa using h.isFan.length_bodd_eq

lemma IsRotaryFan.length_sub_one_bodd (h : M.IsRotaryFan F b) : (F.length - 1).bodd = true := by
  simpa using h.isFan.length_sub_one_bodd_eq

lemma IsRotaryFan.length_sub_two_bodd (h : M.IsRotaryFan F b) : (F.length - 2).bodd = false := by
  rw [bodd_sub (by grind)]
  simp [h.length_bodd]

lemma isRotaryFan_of_forall (M : Matroid α) (F : List α) (b : Bool) (hF : 4 ≤ F.length)
    (hnd : F.Nodup) (hmod : ∀ i, (M.bDual (b != i.bodd)).IsTriangle
        {F[i % F.length], F[(i + 1) % F.length], F[(i + 2) % F.length]}) : M.IsRotaryFan F b := by
  have hT : (M.bDual (b != F.length.bodd)).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]} := by
    specialize hmod (F.length - 2)
    rw [bodd_sub (by lia), bodd_two, Bool.bne_false] at hmod
    convert hmod
    · rw [mod_eq_of_lt (by lia)]
    · rw [mod_eq_of_lt (by lia)]
      lia
    rw [Nat.sub_add_cancel (by lia), mod_self]
  obtain hodd | hodd := F.length.bodd.eq_false_or_eq_true
  · obtain h4 | h5 := hF.eq_or_lt
    · simp [← h4] at hodd
    have hT' : (M.bDual b).IsTriangle {F[0], F[1], F[2]} := by
      simpa [mod_eq_of_lt (show 1 < F.length by lia), mod_eq_of_lt (show 2 < F.length by lia)]
        using hmod 0
    have hwin := hT'.mem_or_mem_of_isCircuit_bDual (by simpa [hodd] using hT.isCircuit)
    simp only [Set.mem_insert_iff, hnd.getElem_inj_iff, mem_singleton_iff, or_true, one_ne_zero,
      or_false, OfNat.ofNat_ne_zero, forall_const] at hwin
    lia
  refine ⟨isFan_of_eq_of_forall_triangle (by lia) hnd (by simpa) (by lia) fun i hi ↦ ?_, ?_, ?_⟩
  · convert hmod i
    <;> rw [mod_eq_of_lt (by lia)]
  · simpa [hodd] using hT
  convert hmod (F.length - 1)
  · simp [Nat.bodd_sub (show 1 ≤ F.length by lia), hodd]
  · rw [mod_eq_of_lt (by lia)]
  · simp [Nat.sub_add_cancel (show 1 ≤ F.length by lia)]
  rw [← Nat.sub_add_comm (by lia), Nat.add_one_sub_one, add_mod_left, mod_eq_of_lt (by lia)]

lemma IsRotaryFan.isTriangle (h : M.IsRotaryFan F b) (i : ℕ) :
    (M.bDual (b != i.bodd)).IsTriangle
      {F[i % F.length], F[(i + 1) % F.length], F[(i + 2) % F.length]} := by
  obtain hlt | hge := lt_or_ge (i % F.length + 2) F.length
  · have hwin := h.isFan.isTriangle_getElem (i % F.length) hlt
    rw [mod_bodd h.length_bodd] at hwin
    convert hwin
    <;> rw [← Nat.mod_add_mod, mod_eq_of_lt (by lia)]
  have hle := add_one_le_of_lt <| Nat.mod_lt (x := i) (show 0 < F.length by grind)
  simp_rw [← Nat.mod_add_mod i F.length 1, ← Nat.mod_add_mod i F.length 2]
  obtain h1 | h2 : i % F.length + 1 = F.length ∨ i % F.length + 2 = F.length := by lia
  · convert h.isTriad_end
    · simp [show i.bodd = !F.length.bodd by
        simpa [mod_bodd h.length_bodd] using congr_arg Nat.bodd h1, h.length_bodd]
    · lia
    · simp [h1]
    rw [← one_add_one_eq_two, ← add_assoc, h1, add_mod_left, mod_eq_of_lt (by grind)]
  have hiF : i.bodd = F.length.bodd := by simpa [mod_bodd h.length_bodd] using congr_arg Nat.bodd h2
  convert h.isTriangle_end
  · simp [hiF, h.length_bodd]
  · lia
  · rw [mod_eq_of_lt (by grind)]
    lia
  simp [h2]

lemma IsRotaryFan.rotate (h : M.IsRotaryFan F b) (n : ℕ) :
    M.IsRotaryFan (F.rotate n) (b != n.bodd) := by
  refine isRotaryFan_of_forall _ _ _ (by simpa using h.length_ge)
    (nodup_rotate.2 h.isFan.nodup) fun i ↦ ?_
  simp only [Bool.bne_assoc, length_rotate, getElem_rotate, mod_add_mod]
  convert h.isTriangle (i + n) using 3
  · simp [bne_comm]
  · simp_rw [add_right_comm]
  simp_rw [add_right_comm]

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
  refine ⟨_, getElems_subset_toSet .., hC, by simp [hF.isFan.nodup], ?_⟩
  cases h : i.bodd with simp [hF.isFan.nodup, h]

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
        (h.isFan.isTriangle_getElem_of_eq 0 (by grind) rfl).notMem_of_mem_of_parallel hp (by simp)
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
  · simpa [← congr_arg Nat.bodd h5] using h.length_bodd
  have hgr := @h.isFan.nodup.getElem_inj_iff
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' h6
  have hnb : n.bodd = false := by
    simpa [h.isFan.length_bodd_eq] using congr_arg Nat.bodd hn
  refine ⟨?_, ?_, ?_⟩
  · have hwin := (h.isFan.delete_head' (by lia) ?_ (by simp)).contract_head' (by grind) ?_ (by simp)
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
  simp only [hF.length_bodd, Bool.toNat_false, CharP.cast_eq_zero, add_zero] at h1 h2
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

lemma IsRotaryFan.joints_indep (h : M.IsRotaryFan F b) : M.Indep (F.getElems {i | i.bodd = b}) :=
  h.isFan.joints_indep (by simp +contextual)

def IsFanCircuit (F : List α) (b : Bool) (C : Set α) : Prop :=
    ∃ (k d : ℕ), k.bodd = b ∧ k < F.length ∧ d.bodd = false ∧ d < F.length ∧ d ≠ 0 ∧
      C = (F.rotate k).getElems ({0, d} ∪ (Iio d ∩ {i | i.bodd = true}))

lemma isFanCircuit_iff_zmod : IsFanCircuit F b C ↔
    ∃ (k : ZMod F.length) (d : ℕ), k.val.bodd = b ∧ d.bodd = false ∧ d ≠ 0 ∧ d < F.length ∧
    C = F.getElems ((fun i : ℕ ↦ ((k + (i : ZMod F.length)).val : ℕ)) ''
          ({0, d} ∪ {i : ℕ | i < d ∧ i.bodd = true})) := by
  by_cases hF : F.length = 0
  · simp [length_eq_zero_iff.1 hF, IsFanCircuit]
  have _ : NeZero F.length := ⟨hF⟩
  constructor
  · rintro ⟨k, d, hkb, hklen, hd, hdlt, hd0, hC_eq⟩
    refine ⟨k, d, by rwa [ZMod.val_natCast_of_lt hklen], hd, hd0, hdlt, ?_⟩
    rw [image_union, image_pair]
    rw [getElems_rotate_of_subset (by grind), image_union, image_pair, zero_add] at hC_eq
    simp only [cast_zero, add_zero, ZMod.val_natCast, ← cast_add, add_comm k]
    convert hC_eq
    rfl
  rintro ⟨k, d, hkb, hdb, hd0, hdlen, hC_eq⟩
  refine ⟨k.val, d, hkb, ZMod.val_lt k, hdb, hdlen, hd0, ?_⟩
  rw [getElems_rotate_of_subset (by grind)]
  convert hC_eq with i
  · simp [ZMod.val_add, add_comm]
  rfl

lemma isFanCircuit_rotate_iff {s : ℕ} (hF : F.length.bodd = false) :
    IsFanCircuit (F.rotate s) b C ↔ IsFanCircuit F (b != s.bodd) C := by
  obtain hF0 | hlt := _root_.eq_zero_or_pos F.length
  · simp [IsFanCircuit, length_eq_zero_iff.1 hF0]
  suffices aux : ∀ F t b, F.length.bodd = false →
    IsFanCircuit (F.rotate t) b C → IsFanCircuit F (b != t.bodd) C by
    refine ⟨aux _ s b hF, fun h ↦ ?_⟩
    have hrw : F.length = s % F.length + (F.length - (s % F.length)):= by
      rw [Nat.add_sub_cancel' (Nat.mod_lt _ hlt).le]
    rw [← F.rotate_length, hrw, ← rotate_rotate] at h
    simpa [rotate_mod, bodd_sub (Nat.mod_lt _ hlt).le, mod_bodd hF, hF] using aux _ _ _ (by simpa) h
  clear! F
  rintro F t b hF ⟨k, d, hkb, hklt, hd, hC_eq⟩
  exact ⟨(t + k) % F.length, d, by simp [mod_bodd hF, hkb, bne_comm],
    Nat.mod_lt _ (by grind [length_rotate]), hd, by simpa using hC_eq⟩

lemma isFanCircuit_reverse_iff' {s : ℕ} (hF : F.length.bodd = false) (hnd : F.Nodup) :
    IsFanCircuit F.reverse b C ↔ IsFanCircuit F (!b) C := by

  suffices aux : ∀ F b, 0 < F.length → F.Nodup → F.length.bodd = false →
      IsFanCircuit F b C → IsFanCircuit F.reverse (!b) C by
    obtain hF0 | hpos := _root_.eq_zero_or_pos F.length
    · simp [IsFanCircuit, length_eq_zero_iff.1 hF0]
    refine ⟨fun h ↦ ?_, fun h ↦ by simpa using aux _ _ hpos (by simpa) hF h ⟩
    simpa using aux F.reverse b (by simpa using hpos) (by simpa) (by simpa) h
  clear! F
  intro F b hF hnd hFlen

  have _ : NeZero F.length := ⟨hF.ne.symm⟩
  have _ : NeZero F.reverse.length := ⟨by simpa using hF.ne.symm⟩
  have : Fact (1 < F.reverse.length) := sorry
  have : Fact (1 < F.length) := sorry
  simp only [isFanCircuit_iff_zmod, ne_eq, exists_and_left, length_reverse, forall_exists_index,
    and_imp]
  intro k hkb d hd hd0 hdlen hC
  obtain rfl | hk0 := eq_or_ne k 0
  · refine ⟨1 + d, ?_, d, hd, hd0, hdlen, ?_⟩
    sorry
    rw [getElems]
  -- refine ⟨- (ZMod.ringEquivCongr (by simp) k) + (1 + d : ZMod _), ?_, d, hd, hd0, hdlen, ?_⟩
  -- · simp only [ZMod.val_add, ZMod.val_natCast, length_reverse, add_mod_mod, mod_bodd hFlen,
  --     bodd_add, hd, Bool.bne_false]
  --   obtain rfl | hk0 := eq_or_ne k 0
  --   · simpa [ZMod.val_one] using hkb
  --   rw [ZMod.val_neg_eq_sub _ (by simpa), ZMod.ringEquivCongr_val, length_reverse,
  --     Nat.bodd_sub k.val_le]
  --   simpa [hFlen, ZMod.val_one]



lemma isFanCircuit_reverse_iff {s : ℕ} (hF : F.length.bodd = false) (hnd : F.Nodup) :
    IsFanCircuit F.reverse b C ↔ IsFanCircuit F (!b) C := by

  suffices aux : ∀ F b, 0 < F.length → F.Nodup → F.length.bodd = false →
      IsFanCircuit F b C → IsFanCircuit F.reverse (!b) C by
    obtain hF0 | hpos := _root_.eq_zero_or_pos F.length
    · simp [IsFanCircuit, length_eq_zero_iff.1 hF0]
    refine ⟨fun h ↦ ?_, fun h ↦ by simpa using aux _ _ hpos (by simpa) hF h ⟩
    simpa using aux F.reverse b (by simpa using hpos) (by simpa) (by simpa) h
  clear! F
  rintro F b h0F hF hFodd ⟨k, rfl | d, hkb, hklen, hd, hdlen, hd0, hC_eq⟩
  · simp at hd0
  simp only [bodd_succ, Bool.not_eq_eq_eq_not, Bool.not_false] at hd hdlen
  set r : ℕ := sorry
  have hrlen : r ≤ F.length := sorry
  have hr1 : (d + 1 + r) % F.length + k % F.length + 1 = F.length := sorry
  have hr2 : r % F.length + (d + 1 + k) % F.length + 1 = F.length := sorry
  have hrk : r.bodd = !k.bodd := sorry
  refine ⟨r, d + 1, sorry, sorry, by simpa, by simpa, by simp, ?_⟩

  rw [← insert_inter_of_notMem (a := d + 1) (by simpa using hd), Iio_insert,
    getElems_insert _ _ (by simpa), getElems_insert _ _ (by simpa),
    Nodup.getElems_inter (by simpa), getElems_rotate_bodd _ _ _ (by simpa),
    getElem_rotate, getElem_rotate, zero_add] at hC_eq ⊢
  rw! [length_reverse, insert_comm, getElem_reverse' hr1, getElem_reverse' hr2,
    getElems_reverse_bodd, hFodd, beq_false, Bool.true_bne, Bool.not_not, hrk]
  rw [Bool.true_bne] at hC_eq
  convert hC_eq using 4
  rw! [getElems_rotate' (by simpa), length_reverse, getElems_rotate' hklen.le,
    getElems_reverse, preimage_preimage, hF.getElems_eq_getElems_iff]

  ext i

  simp only [Set.mem_inter_iff, mem_preimage, mem_Iic, mem_Iio, and_congr_left_iff]
  intro hi
  clear! C hd hkb hFodd hF h0F hrk
  -- obtain hr_eq | hlt := hrlen.eq_or_lt
  -- · simp [hr_eq] at hr2
  --   simp [hr_eq]
  induction k with
  | zero =>
    simp [Nat.mod_eq_of_lt hdlen] at hr1 hr2
    obtain hr_eq | hlt := hrlen.eq_or_lt
    · simp only [hr_eq, mod_self, zero_add] at hr2
      simp only [← hr2, add_tsub_cancel_right, hr_eq, tsub_self, add_zero, tsub_zero, add_mod_right]
      rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
      lia
    rw [Nat.mod_eq_of_lt hlt] at hr2
    rw [Nat.sub_zero, add_mod_right, Nat.mod_eq_of_lt hi]

    obtain rfl | r := r
    · simp at *
      rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia), ← hr2]
      lia

    _
  | succ k ih => sorry
  --   simp at hr1

  --   _
  -- | succ n _ => sorry
  -- by_cases hle : 1 + i + r ≤ F.length
  -- ·
  --   rw [show F.length - 1 - i + (F.length - r) = F.length + (F.length - (1 + i + r)) by lia,
  --     add_mod_left, Nat.mod_eq_of_lt (by lia), Nat.sub_le_iff_le_add]
  --   by_cases hik : i < k
  --   · rw [Nat.mod_eq_of_lt (by lia), add_comm i, ← Nat.sub_add_comm hklen.le,
  --       Nat.sub_le_iff_le_add]
  --     rw [Nat.mod_eq_of_lt (by lia)] at hr2

  --   --   add_mod_left, Nat.mod_eq_of_lt _ (by lia)]
  --   sorry
  -- sorry
  --   -- rw [show F.length - 1 - i + (F.length - r) = 2 * F.length - (1 + i + r) by lia]


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
      (by cases b with simpa [getElems_rotate_bodd _ _ _ h.length_bodd]) <|
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
    · rw [getElems_reverse_bodd, getElems_rotate_bodd _ _ _ h.length_bodd]
      simpa [h.length_bodd]
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
  --       aux (h.rotate i) (by cases b with simpa [getElems_rotate_bodd _ _ _ h.length_bodd])
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
  --   · simpa [hib, getElems_rotate_bodd _ _ _ h.reverse.length_bodd, getElems_reverse_bodd,
  --       h.length_bodd]
  --   · rwa [getElem_rotate, getElem_reverse' auxj1]
  --   · rwa [getElem_rotate, getElem_reverse' auxj]
  --   simp [hjb]


#exit
    -- · sorry
    -- · simpa [hib, getElems_rotate_bodd _ _ _ h.reverse.length_bodd, getElems_reverse_bodd,
    --     h.length_bodd, getElem_reverse' (show j + i + 1 = F.length by lia)]
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
  --     h.isFan.nodup.getElems_bodd_encard_of_even _ h.length_bodd]


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
    --     simp [mod_bodd, hrw, hpb, h.length_bodd, hodd]



    --   specialize aux (p := 2) (h.rotate (F.length + p - 2))
    --   simp [getElems_rotate_bodd, hrw, hpb, hnss, h.length_bodd, mod_bodd] at aux
    --     -- (by simpa [getElems_rotate_bodd _ _ _ h.length_bodd, hrw, hpb])
    --     -- (by simp [hpb, hrw, h.length_bodd]) ?_ rfl





    --   sorry

    --   sorry

    --   have := aux (p := 2) (h.rotate (F.length + p - 2)) sorry sorry
    --   simp [bodd_sub (show 2 ≤ F.length + p by grind), hpb, h.length_bodd] at this
    --   -- simp [getElems_rotate_bodd, bodd_sub (show 2 ≤ F.length + p by grind), hpb,
    --   --   h.length_bodd, hnss] at this
    have foo : ∀



    grw [← hC.isCircuit.eRk_add_one_eq, hC.nonspanning.eRk_add_one_le,
      ← ENat.mul_le_mul_left_iff (show 2 ≠ 0 by simp) (by simp),
      h.isFan.nodup.getElems_bodd_encard_of_even _ h.length_bodd, ← eRk_ground,
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
    -- simp [hp, Nat.bodd_sub hlen.le, h.length_bodd] at this
  -- wlog hb : b = false generalizing F b with aux
  -- · obtain ⟨k, d, hkb, hdb, hd, rfl⟩ :=
  --     aux (h.rotate 1) (by simpa [getElems_rotate_bodd _ _ _ h.length_bodd]) (by grind)
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
      aux h.reverse (by simpa [getElems_reverse_bodd, h.length_bodd]) (by grind)
    simp only [getElem_reverse, Nat.sub_sub] at hpC hrC hqC
    simp only [length_reverse] at hq hr
    refine ⟨F.length - (1 + q), F.length - (1 + p), F.length - (1 + r), by lia, by lia,
      by lia, ?_⟩
    rw [bodd_sub (by lia), bodd_sub (by lia), bodd_sub (by lia)]
    simp [hpC, hrC, hqC, h.length_bodd, hpb, hqb, hrb]
  obtain rfl := hb








  -- obtain ⟨I, hI, rfl⟩ :=
  --   exists_eq_getElems <| hC.subset_ground.trans_eq <| (h.setOf_eq_ground hM).symm
  -- simp_rw [h.isFan.nodup.getElem_mem_getElems_iff]
  -- obtain ⟨r, hrI, hrb⟩ : ∃ r ∈ I, r.bodd = !b := by
  --   by_contra! hcon
  --   exact hC.isCircuit.not_indep <| h.joints_indep.subset <| getElems_mono _ <| by grind
  -- have hiF (d) : 2 * (Iio F.length ∩ {i | i.bodd = d}).encard = ↑F.length := by
  --   simpa [h.length_bodd] using encard_Iio_inter_bodd F.length d
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
  --     simpa [h.length_bodd] using encard_Iio_inter_bodd F.length b
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
