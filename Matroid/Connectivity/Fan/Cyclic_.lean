module

public import Matroid.Connectivity.Fan.Circuit
public import Matroid.Connectivity.Fan.Minor
public import Matroid.Connectivity.Separation.Tutte
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

open Set List Nat Fin

namespace Matroid

variable {α β : Type*} {F : List α} {b c d : Bool} {M : Matroid α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

@[mk_iff]
structure IsCyclicFan (M : Matroid α) (F : List α) (b : Bool) : Prop where
  isFan : M.IsFan F b (!b)
  isTriangle_end : (M.bDual b).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]}
  isTriad_end : (M.bDual (!b)).IsTriangle {F[F.length - 1], F[0], F[1]}

attribute [grind →] IsCyclicFan.isFan

@[grind! .]
lemma IsCyclicFan.length_ge (h : M.IsCyclicFan F b) : 4 ≤ F.length := by
  cases h.isFan with
  | of_pair b e f he hf hne => simpa using h.isTriangle_end
  | cons_triangle e x y F b c h heF hT =>
    cases F with
    | nil =>
      have hcon := h.length_bodd_eq
      simp at hcon
    | cons y F => simp

lemma IsCyclicFan.even (h : M.IsCyclicFan F b) : F.length.bodd = false := by
  simpa using h.isFan.length_bodd_eq

lemma IsCyclicFan.length_sub_one_bodd (h : M.IsCyclicFan F b) : (F.length - 1).bodd = true := by
  simpa using h.isFan.length_sub_one_bodd_eq

lemma IsCyclicFan.length_sub_two_bodd (h : M.IsCyclicFan F b) : (F.length - 2).bodd = false := by
  rw [bodd_sub (by grind)]
  simp [h.even]

lemma IsCyclicFan.isTriangle_getElem_fin' [NeZero F.length] (h : M.IsCyclicFan F b)
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

lemma IsCyclicFan.isTriangle_getElem_fin [NeZero F.length] (h : M.IsCyclicFan F b)
    (i : Fin F.length) :
    (M.bDual (b != i.1.bodd)).IsTriangle {F[i.1], F[(i + 1).1], F[(i + 2).1]} := by
  have _ := h.isFan.fact_one_lt_length
  cases b with simpa [add_assoc, bodd_val_add_of_even h.even] using
    h.isTriangle_getElem_fin' (i + 1)

lemma isCyclicFan_of_forall (M : Matroid α) (F : List α) [NeZero F.length] (b : Bool)
    (hF : 4 ≤ F.length) (hnd : F.Nodup) (hmod : ∀ i : Fin F.length,
        ((M.bDual (b != i.1.bodd)).IsCircuit {F[i.1], F[(i + 1).1], F[(i + 2).1]})) :
    M.IsCyclicFan F b := by
  have : Fact (1 < F.length) := ⟨by lia⟩
  replace hmod : ∀ (i : Fin F.length), (M.bDual (b != i.1.bodd)).IsTriangle
      {F[i.1], F[(i + 1).1], F[(i + 2).1]} := by
    refine fun i ↦ ⟨hmod i, ?_⟩
    rw [encard_insert_of_notMem, encard_pair, show (2 : ℕ∞) + 1 = 3 from rfl]
    · simp only [ne_eq, hnd.getElem_inj_iff, val_inj, add_right_inj]
      simp [← Fin.val_inj, show 2 < F.length by lia, Nat.mod_eq_of_lt]
    simp only [Set.mem_insert_iff, hnd.getElem_inj_iff, val_inj, left_eq_add, one_eq_zero_iff,
      show F.length ≠ 1 by lia, mem_singleton_iff, false_or]
    simp [← Fin.val_inj, show 2 < F.length by lia, Nat.mod_eq_of_lt]
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

/-- A version of `isCyclicFan_of_forall` that doesn't use `NeZero`. -/
lemma isCyclicFan_of_forall_get {M : Matroid α} {F : List α} {b : Bool} (hF : 4 ≤ F.length)
    (hnd : F.Nodup) (hmod : ∀ i : Fin F.length, ((M.bDual (b != i.1.bodd)).IsCircuit
      {F.get i, F.get (finRotate _ i), F.get (finRotate _ (finRotate _ i))})) :
    M.IsCyclicFan F b := by
  have hnz : NeZero F.length := ⟨by lia⟩
  exact isCyclicFan_of_forall _ _ _ hF hnd <| by simpa [add_assoc] using hmod

open Fin.NatCast in
lemma IsCyclicFan.rotate (h : M.IsCyclicFan F b) (n : ℕ) :
    M.IsCyclicFan (F.rotate n) (b != n.bodd) := by
  have _ : NeZero (F.rotate n).length := by simpa using h.isFan.neZero
  have _ := h.isFan.neZero
  refine isCyclicFan_of_forall _ _ _ (by simpa using h.length_ge) (by simpa using h.isFan.nodup)
    fun i ↦ ?_
  rw! [rotate_getElem_fin, rotate_getElem_fin, rotate_getElem_fin, Fin.cast_add, Fin.cast_one,
    Fin.cast_add, Fin.cast_one, add_right_comm, Fin.cast_add i 2, Fin.cast_ofNat (k := 2),
    add_right_comm _ 2, Bool.bne_assoc, bne_comm (a := n.bodd)]
  have := (h.isTriangle_getElem_fin (i.cast (by simp) + (n : Fin _))).isCircuit
  simpa [Fin.bodd_val_add_of_even h.even, mod_bodd h.even, Bool.bne_eq_xor] using this

open Fin.NatCast in
lemma IsCyclicFan.map (h : M.IsCyclicFan F b) {β : Type*} {φ : α → β} (hφ : InjOn φ M.E) :
    (M.map φ hφ).IsCyclicFan (F.map φ) b := by
  have hrw (b : Bool) : (M.map φ hφ).bDual b = (M.bDual b).map φ (by simpa) := by
    cases b with simp
  have : NeZero F.length := ⟨by grind⟩
  have : NeZero (F.map φ).length := ⟨by grind⟩
  apply isCyclicFan_of_forall
  · simp [h.length_ge]
  · rw [nodup_map_iff_inj_on h.isFan.nodup]
    refine fun x hx y hy hxy ↦ ?_
    rwa [hφ.eq_iff (h.isFan.subset_ground hx) (h.isFan.subset_ground hy)] at hxy
  refine fun i ↦ (IsTriangle.isCircuit ?_)
  convert ((h.rotate i).isFan.map hφ).isTriangle_getElem 0
    (by simp [show 2 < F.length by grind]) using 2
  · simp
  · simp [Nat.mod_eq_of_lt (show i.1 < F.length by simpa using i.2)]
  simp [getElem_map, map_rotate, zero_add, getElem_rotate, length_map, Fin.val_add, add_comm i.1]

lemma IsCyclicFan.reverse (h : M.IsCyclicFan F b) : M.IsCyclicFan F.reverse (!b) := by
  refine ⟨by simpa using h.isFan.reverse, ?_, ?_⟩
  · simp only [length_reverse, getElem_reverse, tsub_self, tsub_zero,
      show F.length - 1 - (F.length - 2) = 1 by grind]
    exact h.isTriad_end.reverse
  simp only [Bool.not_not, length_reverse, getElem_reverse, tsub_self, tsub_zero, Nat.sub_sub]
  exact h.isTriangle_end.reverse

lemma IsCyclicFan.dual (h : M.IsCyclicFan F b) : M✶.IsCyclicFan F (!b) :=
  ⟨by simpa using h.isFan.dual, by simpa using h.isTriangle_end, by simpa using h.isTriad_end⟩

@[simp]
lemma isCyclicFan_dual_iff : M✶.IsCyclicFan F b ↔ M.IsCyclicFan F (!b) :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

lemma IsCyclicFan.bDual (h : M.IsCyclicFan F b) (c : Bool) :
    (M.bDual c).IsCyclicFan F (b != c) := by
  obtain rfl | rfl := c
  · simpa
  simpa using h.dual

lemma IsCyclicFan.of_bDual (h : (M.bDual c).IsCyclicFan F b) : M.IsCyclicFan F (b != c) := by
  simpa using h.bDual c

/-- A fan on the ground set of a simple, cosimple matroid is cyclic. -/
lemma IsFan.isCyclicFan_of_ground_eq (hF : M.IsFan F b c) (hM : M.Simple) (hM' : M✶.Simple)
    (hE : {e | e ∈ F} = M.E) : c = !b ∧ M.IsCyclicFan F b := by
  obtain ⟨h_even, hT⟩ := hF.isTriangle_bDual_of_simple (n := F.length - 2) (by grind) hM hM' hE
  obtain ⟨-, hT'⟩ := hF.reverse.dual.isTriangle_bDual_of_simple (n := F.length - 2) (by grind) hM'
    (by simpa) (by simpa)
  rw [← Nat.not_odd_iff_even, ← Nat.bodd_eq_odd, Bool.not_eq_true, hF.length_bodd_eq] at h_even
  obtain rfl : c = !b := by grind [cases Bool]
  refine ⟨rfl, ⟨hF, by grind, ?_⟩⟩
  simpa [show F.length - 1 - (F.length - 2) = 1 by grind,
    show F.length - 1 - (F.length - 2 + 1) = 0 by lia] using hT'.reverse

lemma IsCyclicFan.eConn_eq (h : M.IsCyclicFan F b) : M.eConn {e | e ∈ F} = 0 := by
  refine h.isFan.eConn_eq_zero_of_mem_closure_mem_closure ?_ ?_
  · refine mem_of_mem_of_subset h.isTriad_end.mem_closure₂ <| closure_subset_closure _ ?_
    exact pair_subset (getElem_mem_tail _ (by grind) _) (getElem_mem_tail _ (by grind) _)
  refine mem_of_mem_of_subset h.isTriangle_end.mem_closure₂ <| closure_subset_closure _ ?_
  exact pair_subset (getElem_mem_dropLast (by grind)) (getElem_mem_dropLast (by grind))

/-- A cyclic fan in a `2`-connected matroid is the entire ground set. -/
lemma IsCyclicFan.setOf_eq_ground (h : M.IsCyclicFan F b) (hM : M.TutteConnected 2) :
    {e | e ∈ F} = M.E := by
  have hne : M.Nonempty := ⟨F[0], h.isFan.subset_ground (by simp)⟩
  exact (hM.connected rfl.le).eq_ground_of_eConn_eq_zero h.eConn_eq ⟨F[0], by simp⟩
    h.isFan.subset_ground

lemma IsCyclicFan.restrict_connected (hF : M.IsCyclicFan F b) : (M ↾ {e | e ∈ F}).Connected := by
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

/-- A cyclic fan is the entire matroid iff the matroid is connected. -/
lemma IsCyclicFan.setOf_eq_ground_iff (hF : M.IsCyclicFan F b) :
    {e | e ∈ F} = M.E ↔ M.Connected := by
  refine ⟨fun h ↦ ?_, fun h ↦ hF.setOf_eq_ground h.tutteConnected_two⟩
  rw [← M.restrict_ground_eq_self]
  exact h ▸ hF.restrict_connected

lemma IsCyclicFan.restrict_self (h : M.IsCyclicFan F b) : (M ↾ {e | e ∈ F}).IsCyclicFan F b := by
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
lemma IsCyclicFan.parallel_iff_eq (h : M.IsCyclicFan F b) (h4 : 4 < F.length) {i j}
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

lemma IsCyclicFan.simple (h : M.IsCyclicFan F b) (h2 : M.TutteConnected 2) (h4 : 4 < F.length) :
    M.Simple := by
  simp only [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_not_isLoop,
    ← h.setOf_eq_ground h2, mem_ofPred_eq]
  refine ⟨fun e hf ↦ (h.isFan.isNonloop hf).not_isLoop, fun e f hef ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem (h.setOf_eq_ground h2 ▸ hef.mem_ground_left)
  obtain ⟨j, hj, rfl⟩ := getElem_of_mem (h.setOf_eq_ground h2 ▸ hef.mem_ground_right)
  simp_rw [(h.parallel_iff_eq h4).1 hef]

lemma IsCyclicFan.finite (h : M.IsCyclicFan F b) (h2 : M.TutteConnected 2) : M.Finite := by
  refine ⟨?_⟩
  rw [← h.setOf_eq_ground h2]
  simp

lemma IsCyclicFan.contract_delete (h : M.IsCyclicFan F false) (hlen : 4 < F.length) :
    (M ＼ {F[0]} ／ {F[1]}).IsCyclicFan F.tail.tail false := by
  obtain h5 | h6 := (show 5 ≤ F.length by lia).eq_or_lt
  · simpa [← congr_arg Nat.bodd h5] using h.even
  have hgr := @h.isFan.nodup.getElem_inj_iff
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' h6
  have hnb : n.bodd = false := by
    simpa [h.isFan.length_bodd_eq] using congr_arg Nat.bodd hn
  refine ⟨?_, ?_, ?_⟩
  · have hwin := (h.isFan.delete_head (by lia) ?_ (by simp)).contract_head (by grind) ?_ (by simp)
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

lemma IsCyclicFan.eRk_eq (hF : M.IsCyclicFan F b) : 2 * M.eRk {e | e ∈ F} = F.length := by
  have h1 := hF.isFan.eRk_ge
  have h2 := hF.dual.isFan.eRk_ge
  simp only [hF.even, Bool.toNat_false, Nat.cast_zero, add_zero] at h1 h2
  have heq := M.eRk_add_eRk_dual_eq _ hF.isFan.subset_ground
  rw [hF.eConn_eq, zero_add, hF.isFan.nodup.encard_toSet_eq] at heq
  enat_to_nat!; lia

lemma IsCyclicFan.two_mul_div2 (hF : M.IsCyclicFan F b) : 2 * F.length.div2 = F.length := by
  nth_rw 1 [eq_comm, ← bodd_add_div2 F.length, hF.even, Bool.toNat_false, zero_add]

lemma IsCyclicFan.eRk_eq' (hF : M.IsCyclicFan F b) : M.eRk {e | e ∈ F} = F.length.div2 := by
  rw [← (ENat.mul_right_strictMono (show 2 ≠ 0 by simp) (by simp)).injective.eq_iff,
    hF.eRk_eq, ← hF.two_mul_div2]
  simp

lemma IsCyclicFan.eRank_eq (hF : M.IsCyclicFan F b) (hM : M.TutteConnected 2) :
    2 * M.eRank = F.length := by
  rw [← eRk_ground, ← hF.setOf_eq_ground hM, hF.eRk_eq]

lemma IsCyclicFan.eRank_eq' (hF : M.IsCyclicFan F b) (hM : M.TutteConnected 2) :
    M.eRank = F.length.div2 := by
  rw [← eRk_ground, ← hF.setOf_eq_ground hM, hF.eRk_eq']

/-- An even fan in a three-connected matroid whose initial element is (co)spanned by the
other elements is a cyclic fan -/
lemma IsFan.isCyclicFan_of_tutteConnected_three_of_mem_closure (h : M.IsFan F b (!b))
    (hM : M.TutteConnected 3) (h4 : 4 ≤ M.E.encard)
    (hcl : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail}) : M.IsCyclicFan F b := by
  refine (h.isCyclicFan_of_ground_eq (hM.simple h4) (hM.dual.simple (by simpa)) ?_).2
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

lemma IsCyclicFan.joints_indep (h : M.IsCyclicFan F b) :
    M.Indep ((fun x : Fin F.length ↦ F[x.1]) '' Fin.val ⁻¹' {i | i.bodd = b}) :=
  h.isFan.joints_indep (by simp +contextual)

/-- `IsFanCircuit F b C` means that `C` consists of a pair of joints `F[p], F[q]` of `C`,
together with all the cojoints between `F[p]` and `F[q]` in the cyclic order. -/
def IsFanCircuit (F : List α) (b : Bool) (C : Set α) : Prop :=
    ∃ (p q : Fin F.length), p ≠ q ∧ p.1.bodd = b ∧ q.1.bodd = b
    ∧ C = (fun x ↦ F[x.1]) '' ({p, q} ∪ {i | btw p i q ∧ i.1.bodd = !b})

lemma IsFanCircuit.rotate (hF : F.length.bodd = false) (h : IsFanCircuit F b C) (s : ℕ) :
    IsFanCircuit (F.rotate s) (b != s.bodd) C := by
  have hnz := (Exists.choose h).neZero
  wlog hs : s < F.length generalizing s with aux
  · rw [← rotate_mod, ← mod_bodd hF]
    exact aux _ <| Nat.mod_lt' ..
  lift s to Fin F.length using hs
  have := s.neZero
  obtain ⟨p, q, hpq, hpb, hqb, hC⟩ := h
  refine ⟨(p - s).cast (by simp), (q - s).cast (by simp), by simpa,
    by simpa [hF, bodd_val_sub_of_even], by simpa [hF, bodd_val_sub_of_even], ?_⟩
  simp_rw [image_getElem_fin_rotate', ← image_pair, preimage_union,
    preimage_image_eq _ (Fin.cast_injective _), preimage_ofPred_eq, hC, image_union, image_pair]
  cases b with cases hs : s.1.bodd with simp [← sub_eq_add_neg, bodd_val_sub_of_even hF, hs]

lemma IsFanCircuit.reverse (hF : F.length.bodd = false) (h : IsFanCircuit F b C) :
    IsFanCircuit F.reverse (!b) C := by
  obtain ⟨p, q, hpq, hpb, hqb, hC⟩ := h
  refine ⟨q.rev.cast (by simp), p.rev.cast (by simp), by simpa using hpq.symm,
    by simp_rw [val_cast, bodd_val_rev_of_even hF, hqb],
    by simp_rw [val_cast, bodd_val_rev_of_even hF, hpb], ?_⟩
  simp_rw [image_getElem_fin_reverse, preimage_union, ← image_pair,
    preimage_image_eq _ (Fin.cast_injective _), preimage_image_eq _ Fin.rev_injective,
    preimage_ofPred_eq, btw_cast_iff, btw_rev_iff, val_cast, bodd_val_rev_of_even hF,
    Bool.not_inj_iff, pair_comm (a := q), hC]

lemma IsFanCircuit.isCircuit (h : M.IsCyclicFan F b) (hC : IsFanCircuit F b C) : M.IsCircuit C := by
  obtain ⟨p, q, hpq, hpb, hqb, hC⟩ := hC
  have hnz := p.neZero
  have hlt : 0 < q - p := by
    rwa [lt_iff_le_and_ne, Ne, eq_comm, sub_eq_zero, eq_comm, and_iff_right (by simp)]
  convert (h.rotate p).isFan.isCircuit_interval hlt (by simp) (by simp [hpb])
    (by simpa [bodd_val_sub_of_even h.even]) (by simp [hpb])
  simp_rw [image_getElem_fin_rotate, ← preimage_comp, val_comp_cast, preimage_comp,
    ← image_pair, ← image_val_Icc, preimage_union, preimage_inter,
    preimage_image_eq _ Fin.val_injective, preimage_singleton,
    preimage_ofPred_eq, bodd_val_sub_of_even h.even, hpb, sub_eq_add_neg,
    ← image_add_right, image_pair, image_add_right,
    ← sub_eq_add_neg, ← ofPred_btw_of_lt hlt, ← btw_add_right_iff (a := 0) (k := p)]
  cases b with simpa

lemma IsCyclicFan.isFanCircuit_of_isNonspanningCircuit [NeZero F.length] (hF : M.IsCyclicFan F b)
    (hM : M.TutteConnected 2) {C : Set α} (hC : M.IsNonspanningCircuit C)
    (hne : C ≠ (fun x : Fin F.length ↦ F[x.1]) '' Fin.val ⁻¹' {i | i.bodd = !b}) :
    IsFanCircuit F b C := by
  -- `C` isn't contained in the cojoints, because it would be a proper subset and hence independent.
  by_cases hssu : C ⊆ (fun x ↦ F[↑x]) '' val ⁻¹' bodd ⁻¹' {!b}
  · exact False.elim <| (hF.isFan.indep_of_ssubset_cojoints (hssu.ssubset_of_ne hne)).not_dep
      hC.isCircuit.dep
  -- Choose a joint `F[p]` in `C`.
  obtain ⟨e, heC, hpb⟩ := not_subset.1 hssu
  obtain ⟨p, rfl : F[p.1] = e⟩ :=
    get_of_mem (hC.subset_ground.trans_eq (hF.setOf_eq_ground hM).symm heC)
  replace hpb : p.1.bodd = b := by simpa [hF.isFan.nodup.getElem_inj_iff, val_inj] using hpb
  clear hne hssu
  -- Some cojoint next to `p` must be in `C`; we may assume that it is to the right.
  wlog hp1 : F[(p + 1).1] ∈ C generalizing F p b with aux
  · have hnz := hF.reverse.isFan.neZero
    specialize aux hF.reverse (p.rev.cast (by simp)) ?_ ?_ ?_
    · simpa only [reverse_getElem_fin, cast_rev, rev_rev, Fin.cast_cast, Fin.val_cast]
    · simp only [val_cast, bodd_val_rev_of_even hF.even, hpb]
    · rw [(hF.isTriangle_getElem_fin' p).reverse.mem_iff_mem_of_isCircuit_bDual ?_ hp1] at heC
      · rw! [reverse_getElem_fin, Fin.cast_rev, Fin.cast_rev, ← neg_eq_rev_add_one, ← Fin.cast_neg]
        simpa
      simpa [hpb] using hC.isCircuit
    simpa using aux.reverse (by simpa using hF.even)
  wlog hp0 : p = 0 generalizing F b p with aux
  · have := (hF.rotate p).isFan.neZero
    specialize aux (hF.rotate p) 0 (by simpa) (by simp [hpb])
      (by simpa only [zero_add, rotate_getElem_fin, Fin.cast_one, add_comm, cast_val_eq_self]) rfl
    replace aux := aux.rotate (by simpa using hF.even) (-p).1
    rw [rotate_rotate_fin] at aux
    simpa [hpb, bodd_val_neg_of_even hF.even] using aux
  obtain rfl := hp0
  obtain rfl : false = b := by simpa using hpb
  -- `C` doesn't contain all the cojoints, because it would be too big.
  by_cases! hss : ∀ (i : Fin F.length), i.1.bodd = true → F[i.1] ∈ C
  · have hssu : (fun i ↦ F[i.1]) '' {i : Fin F.length | i.1.bodd = true} ⊂ C :=
      ssubset_of_subset_not_subset (image_subset_iff.2 fun i hi ↦ hss _ hi)
      fun hCss ↦ by simpa [hF.isFan.nodup.getElem_inj_iff] using hCss heC
    replace hssu := ((F.finite_toSet ..).subset <| by grind).encard_lt_encard hssu
    grw [hF.isFan.nodup.injective_getElem_fin.encard_image, ← ENat.mul_lt_mul_left_iff (c := 2)
      (by simp) (by simp), encard_setOf_bodd_of_even hF.even, ← hC.isCircuit.eRk_add_one_eq,
      hC.nonspanning.eRk_add_one_le, ← eRk_ground, ← hF.setOf_eq_ground hM, hF.eRk_eq] at hssu
    exact False.elim <| hssu.ne rfl
  have := hF.isFan.fact_one_lt_length
  -- if `C` contains a joint other than `F[0]`, then we can conclude that `C` is an interval.
  by_cases! hq : ∃ q : Fin F.length, 0 < q ∧ F[q.1] ∈ C ∧ q.1.bodd = false
  · obtain ⟨q, hq0, hqC, hqb⟩ := hq
    have hC_eq := hF.isFan.eq_interval_of_mem_mem_mem hq0 q.2 (by simp) hqb hC.isCircuit heC
      (by simpa using hp1) hqC
    simp_rw [preimage_union, ← image_pair, ← image_val_Icc, preimage_inter,
      preimage_image_eq _ val_injective, preimage_singleton, preimage_ofPred_eq,
      ← ofPred_btw_of_lt hq0, ← ofPred_and] at hC_eq
    exact ⟨0, q, hq0.ne, by simp, hqb, hC_eq⟩
  -- otherwise, we can conclude that `C` contains all cojoints, a contradiction.
  obtain ⟨q, hqt, hqC⟩ := hss
  refine False.elim <| hqC <|
    hF.isFan.cojoint_mem_of_subsingleton_joint_mem_le (p := (0 : Fin F.length).1)
    (by grind) (by grind) hC.isCircuit ?_ (by simpa using hp1) (by grind) q.2 hqt
  exact fun i hi hib hiC ↦ by_contra fun h0 ↦ hq ⟨i, hi⟩ (by grind) (by simpa) (by simpa)

lemma IsCyclicFan.isNonspanningCircuit_iff (hF : M.IsCyclicFan F b) (hM : M.TutteConnected 2)
    {C : Set α} (hne : C ≠ (fun x : Fin F.length ↦ F[x.1]) '' Fin.val ⁻¹' {i | i.bodd = !b}) :
    M.IsNonspanningCircuit C ↔ (IsFanCircuit F b C ∧ 2 * C.encard ≤ F.length)  := by
  have := hF.isFan.neZero
  refine ⟨fun h ↦ ⟨hF.isFanCircuit_of_isNonspanningCircuit hM h hne, ?_⟩, fun h ↦ ?_⟩
  · grw [← h.isCircuit.eRk_add_one_eq, h.nonspanning.eRk_add_one_le, hF.eRank_eq hM]
  have hC := h.1.isCircuit hF
  refine ⟨nonspanning_of_eRk_ne (ne_of_lt ?_), hC⟩
  grw [← ENat.add_one_lt_add_one_iff, hC.eRk_add_one_eq,
    ← ENat.mul_lt_mul_left_iff (c := 2) (by simp) (by simp), mul_add, hF.eRank_eq hM, h.2]
  simp

lemma IsCyclicFan.isCircuitHyperplane_or_isBase_cojoints (hF : M.IsCyclicFan F b)
    (hM : M.TutteConnected 2) : M.IsCircuitHyperplane
    (F.get '' {i | i.1.bodd = !b}) ∨ M.IsBase (F.get '' {i | i.1.bodd = !b}) := by
  have := hF.finite hM
  have hnz := hF.isFan.neZero
  set J := ((fun x ↦ F[x.1]) '' Fin.val ⁻¹' {i | i.bodd = !b}) with hJ
  have hcard : J.encard = M.eRank := by
    grw [hJ, hF.isFan.nodup.injective_getElem_fin.encard_image,
      ← preimage_inter_range, encard_preimage_of_injective_subset_range val_injective (by simp),
      range_val, inter_comm,
      ← (ENat.mul_right_strictMono (a := 2) (by simp) (by simp)).injective.eq_iff,
      encard_Iio_inter_bodd_of_even hF.even, hF.eRank_eq hM]
  have hJF : J ⊆ {e | e ∈ F} := by grind
  have hJE : J ⊆ M.E := hJF.trans hF.isFan.subset_ground
  obtain hi | hd := M.indep_or_dep hJE
  · exact .inr <| hi.isBase_of_eRk_ge (Finite.subset (by simp) hJF) <|
      by rw [hi.eRk_eq_encard, hcard]
  have hnsp := nonspanning_of_eRk_ne (hd.eRk_lt_encard.trans_eq hcard).ne
  obtain ⟨C, hCJ, hC⟩ := hd.exists_isCircuit_subset
  obtain rfl | hssu := hCJ.eq_or_ssubset
  · refine .inl ⟨hC, ?_⟩
    rw [isHyperplane_iff_maximal_nonspanning, maximal_iff_forall_ssuperset]
    refine ⟨hnsp, fun X hJX hX ↦ hX.not_spanning ?_⟩
    rw [spanning_iff_compl_coindep]
    refine hF.dual.isFan.indep_of_ssubset_cojoints ?_
    refine (sdiff_ssubset_sdiff_right hX.subset_ground hJX).trans_subset ?_
    rw [sdiff_subset_iff, ← image_union, preimage_singleton, preimage_ofPred_eq, ← ofPred_or]
    simp [Bool.eq_not, em', hF.setOf_eq_ground hM]
  obtain ⟨p, q, -, hp, -, rfl⟩ :=
    hF.isFanCircuit_of_isNonspanningCircuit hM ⟨hnsp.subset hCJ, hC⟩ hssu.ne
  rw [image_subset_iff, Set.subset_def, hJ,
    hF.isFan.nodup.injective_getElem_fin.preimage_image] at hCJ
  simpa [hp] using hCJ (x := p)

/-- If `F` is a cyclic fan on distinct matroids `M` and `N`,
and the cojoints are at least as free in `M` as they are in `N`,
then `M` is obtained from `N` by relaxing the cojoints. -/
lemma IsCyclicFan.eq_relax {M N : Matroid α} (hFM : M.IsCyclicFan F b) (hFN : N.IsCyclicFan F b)
    (hM : M.TutteConnected 2) (hN : N.TutteConnected 2) (hMN : M ≠ N)
    (hI : N.Indep (F.get '' Fin.val ⁻¹' {i | i.bodd = !b}) →
      M.Indep (F.get '' Fin.val ⁻¹' {i | i.bodd = !b})) :
    ∃ (h : N.IsCircuitHyperplane (F.get '' Fin.val ⁻¹' {i | i.bodd = !b})),
      M = N.relax _ (IsLawfulRelaxation.single h) := by
  have hJM := hFM.isCircuitHyperplane_or_isBase_cojoints hM
  have hJN := hFN.isCircuitHyperplane_or_isBase_cojoints hN
  set J := (F.get '' Fin.val ⁻¹' {i | i.bodd = !b}) with hJ
  have := hFM.finite hM
  have hE : M.E = N.E := by rw [← hFM.setOf_eq_ground hM, hFN.setOf_eq_ground hN]
  have hr : M.eRank = N.eRank := by rw [hFM.eRank_eq' hM, hFN.eRank_eq' hN]
  by_cases! hi : M.Indep J ↔ N.Indep J
  · contrapose! hMN
    refine ext_isNonspanningCircuit hE hr fun C hC ↦ ?_
    obtain rfl | hne := eq_or_ne C J
    · obtain (hJ | hJ) := hJM
      · obtain (hJ' | hJ') := hJN
        · exact iff_of_true ⟨hJ.isHyperplane.nonspanning, hJ.isCircuit⟩
            ⟨hJ'.isHyperplane.nonspanning, hJ'.isCircuit⟩
        exact False.elim <| (hi.2 hJ'.indep).not_dep hJ.isCircuit.dep
      obtain (hJ' | hJ') := hJN
      · exact False.elim <| (hi.1 hJ.indep).not_dep hJ'.isCircuit.dep
      exact iff_of_false (fun h ↦ h.isCircuit.not_indep hJ.indep)
        (fun h ↦ h.isCircuit.not_indep hJ'.indep)
    rw [hFM.isNonspanningCircuit_iff hM hne, hFN.isNonspanningCircuit_iff hN hne]
  rw [or_iff_left (by grind), hJ] at hi
  rw [or_iff_left (fun h ↦ hi.2 h.indep)] at hJN
  refine ⟨hJN, ext_isNonspanningCircuit hE (by simpa) fun C hC ↦ ?_⟩
  rw [relax_isNonspanningCircuit_iff]
  obtain rfl | hne := eq_or_ne C J
  · exact iff_of_false (fun h ↦ h.isCircuit.not_indep hi.1) (by simp)
  rw [and_iff_left (by simpa), hFM.isNonspanningCircuit_iff hM hne,
    hFN.isNonspanningCircuit_iff hN hne]
