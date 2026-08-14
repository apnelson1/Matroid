module

public import Matroid.Connectivity.Fan.Circuit
public import Matroid.Connectivity.Separation.Tutte
public import Mathlib.Data.ZMod.Basic

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

lemma mod_bodd {n : ℕ} (hn : n.bodd = false) (i) : (i % n).bodd = i.bodd := by
  sorry

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

lemma isRotaryFan_of_forall' (M : Matroid α) (F : List α) (b : Bool)
    (hF : 4 ≤ F.length) (hnd : F.Nodup)
    (hmod : ∀ i,
      (M.bDual (b != i.bodd)).IsTriangle
        {F[i % F.length], F[(i + 1) % F.length], F[(i + 2) % F.length]}) :
    M.IsRotaryFan F b := by
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

lemma IsRotaryFan.isTriangle (h : M.IsRotaryFan F b) (i : ZMod F.length) :
    (M.bDual (b != i.val.bodd)).IsTriangle {F[i.val], F[(i + 1).val], F[(i + 2).val]} := by
  have : NeZero F.length := ⟨by grind⟩
  have : Fact (1 < F.length) := ⟨by grind⟩
  obtain hlt | hge := lt_or_ge (i.val + 2) F.length
  · convert h.isFan.isTriangle_getElem i.val hlt
    · rw [ZMod.val_add, ZMod.val_one'' (by grind), Nat.mod_eq_of_lt (by lia)]
    rw [ZMod.val_add, ZMod.val_ofNat_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
  obtain h2 | h1 : i.val + 2 = F.length ∨ i.val + 1 = F.length := by grind
  · convert h.isTriangle_end
    · apply_fun Nat.bodd at h2
      simp [show i.val.bodd = false by simpa [h.isFan.length_bodd_eq] using h2]
    · lia
    · simp_rw [← h2, ZMod.val_add, ZMod.val_one,
        Nat.mod_eq_of_lt (show i.val + 1 < F.length by lia)]
      lia
    rw [ZMod.val_add, ZMod.val_ofNat_of_lt (show 2 < F.length by grind), h2, Nat.mod_self]
  convert h.isTriad_end
  · apply_fun Nat.bodd at h1
    simp [show i.val.bodd = true by simpa [h.length_bodd] using h1]
  · lia
  · rw [ZMod.val_add, ZMod.val_one, h1, Nat.mod_self]
  rw [ZMod.val_add, ZMod.val_ofNat_of_lt (by grind), show (nat_lit 2 : ℕ) = 1 + 1 from rfl,
    ← add_assoc, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by grind)]

-- lemma IsRotaryFan.isTriangle (h : M.IsRotaryFan F b) (i : ZMod F.length) :
--     (M.bDual (b != i.val.bodd)).IsTriangle {F[i.val], F[(i + 1).val], F[(i + 2).val]} := by
--   have : NeZero F.length := ⟨by grind⟩
--   have : Fact (1 < F.length) := ⟨by grind⟩
--   obtain hlt | hge := lt_or_ge (i.val + 2) F.length
--   · convert h.isFan.isTriangle_getElem i.val hlt
--     · rw [ZMod.val_add, ZMod.val_one'' (by grind), Nat.mod_eq_of_lt (by lia)]
--     rw [ZMod.val_add, ZMod.val_ofNat_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
--   obtain h2 | h1 : i.val + 2 = F.length ∨ i.val + 1 = F.length := by grind
--   · convert h.isTriangle_end
--     · apply_fun Nat.bodd at h2
--       simp [show i.val.bodd = false by simpa [h.isFan.length_bodd_eq] using h2]
--     · lia
--     · simp_rw [← h2, ZMod.val_add, ZMod.val_one,
--         Nat.mod_eq_of_lt (show i.val + 1 < F.length by lia)]
--       lia
--     rw [ZMod.val_add, ZMod.val_ofNat_of_lt (show 2 < F.length by grind), h2, Nat.mod_self]
--   convert h.isTriad_end
--   · apply_fun Nat.bodd at h1
--     simp [show i.val.bodd = true by simpa [h.length_bodd] using h1]
--   · lia
--   · rw [ZMod.val_add, ZMod.val_one, h1, Nat.mod_self]
--   rw [ZMod.val_add, ZMod.val_ofNat_of_lt (by grind), show (nat_lit 2 : ℕ) = 1 + 1 from rfl,
--     ← add_assoc, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by grind)]


  --   simp only [CharP.cast_eq_zero, zero_sub, neg_add_cancel, ZMod.val_zero] at hmod
  --   have h2 : NeZero (1 : ZMod F.length) := ⟨by simp⟩
  --   have h2 : NeZero (2 : ZMod F.length) := ⟨ZMod.ofNat_ne_zero_of_lt (by lia)⟩
  --   simpa [ZMod.val_neg_of_ne_zero, ZMod.val_ofNat_of_lt (show 2 < F.length by lia),
  --     show (-2 : ZMod F.length) + 1 = -1 by ring, ZMod.val_neg_of_ne_zero, ZMod.val_one,
  --     Nat.bodd_sub (show 2 ≤ F.length by lia)] using hmod
  -- obtain hodd | hodd := F.length.bodd.eq_false_or_eq_true
  -- · have hT' : (M.bDual b).IsTriangle {F[0], F[1], F[2]} := by
  --     simpa [ZMod.val_one, ZMod.val_ofNat_of_lt (show 2 < F.length by lia)] using hmod 0
  --   have hwin := hT.mem_iff_mem_of_isCircuit_bDual (by simpa [hodd] using hT'.isCircuit)
  --   obtain h4 | h5 := hF.eq_or_lt
  --   · simp [← h4] at hodd
  --   simp only [Set.mem_insert_iff, hnd.getElem_inj_iff, Nat.sub_eq_zero_iff_le, mem_singleton_iff,
  --     Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd, OfNat.zero_ne_ofNat] at hwin
  --   lia
  -- refine ⟨isFan_of_eq_of_forall_triangle (by lia) hnd (by simpa) (by lia) fun i hi ↦ ?_, ?_, ?_⟩
  -- · specialize hmod i
  --   simp only [ZMod.val_natCast, ZMod.val_add, Nat.mod_eq_of_lt (show i < F.length by lia)] at hmod
  --   convert hmod
  --   · rw [ZMod.val_one'' (by lia), Nat.mod_eq_of_lt (by lia)]
  --   rw [ZMod.val_ofNat, Nat.mod_eq_of_lt (a := 2) (by lia), Nat.mod_eq_of_lt hi]
  -- · specialize hmod (F.length - 2)
  --   simp only [CharP.cast_eq_zero, zero_sub, neg_add_cancel, ZMod.val_zero] at hmod
  --   have h2 : NeZero (1 : ZMod F.length) := ⟨by simp⟩
  --   have h2 : NeZero (2 : ZMod F.length) := ⟨ZMod.ofNat_ne_zero_of_lt (by lia)⟩
  --   simpa [ZMod.val_neg_of_ne_zero, ZMod.val_ofNat_of_lt (show 2 < F.length by lia),
  --     show (-2 : ZMod F.length) + 1 = -1 by ring, ZMod.val_neg_of_ne_zero, ZMod.val_one,
  --     Nat.bodd_sub (show 2 ≤ F.length by lia), hodd] using hmod
  -- specialize hmod (-1)
  -- simpa [show (-1 : ZMod F.length) + 2 = 1 by ring, ZMod.val_neg_of_ne_zero, ZMod.val_one,
  --   Nat.bodd_sub (show 1 ≤ F.length by lia), hodd] using hmod

-- lemma isRotaryFan_of_forall (M : Matroid α) (F : List α) (b : Bool)
--     (hF : 4 ≤ F.length) (hnd : F.Nodup)
--     (hmod : ∀ (i : ZMod F.length),
--       (M.bDual (b != i.val.bodd)).IsTriangle {F[i.val], F[(i + 1).val], F[(i + 2).val]}) :
--     M.IsRotaryFan F b := by
--   have : NeZero F.length := ⟨by grind⟩
--   have h' : Fact (1 < F.length) := ⟨by grind⟩
--   have hT : (M.bDual (b != F.length.bodd)).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]} := by
--     specialize hmod (F.length - 2)
--     simp only [CharP.cast_eq_zero, zero_sub, neg_add_cancel, ZMod.val_zero] at hmod
--     have h2 : NeZero (1 : ZMod F.length) := ⟨by simp⟩
--     have h2 : NeZero (2 : ZMod F.length) := ⟨ZMod.ofNat_ne_zero_of_lt (by lia)⟩
--     simpa [ZMod.val_neg_of_ne_zero, ZMod.val_ofNat_of_lt (show 2 < F.length by lia),
--       show (-2 : ZMod F.length) + 1 = -1 by ring, ZMod.val_neg_of_ne_zero, ZMod.val_one,
--       Nat.bodd_sub (show 2 ≤ F.length by lia)] using hmod
--   obtain hodd | hodd := F.length.bodd.eq_false_or_eq_true
--   · have hT' : (M.bDual b).IsTriangle {F[0], F[1], F[2]} := by
--       simpa [ZMod.val_one, ZMod.val_ofNat_of_lt (show 2 < F.length by lia)] using hmod 0
--     have hwin := hT.mem_iff_mem_of_isCircuit_bDual (by simpa [hodd] using hT'.isCircuit)
--     obtain h4 | h5 := hF.eq_or_lt
--     · simp [← h4] at hodd
--     simp only [Set.mem_insert_iff, hnd.getElem_inj_iff, Nat.sub_eq_zero_iff_le, mem_singleton_iff,
--       Nat.pred_eq_succ_iff, zero_add, Nat.reduceAdd, OfNat.zero_ne_ofNat] at hwin
--     lia
--   refine ⟨isFan_of_eq_of_forall_triangle (by lia) hnd (by simpa) (by lia) fun i hi ↦ ?_, ?_, ?_⟩
--   · specialize hmod i
--     simp only [ZMod.val_natCast, ZMod.val_add, Nat.mod_eq_of_lt (show i < F.length by lia)] at hmod
--     convert hmod
--     · rw [ZMod.val_one'' (by lia), Nat.mod_eq_of_lt (by lia)]
--     rw [ZMod.val_ofNat, Nat.mod_eq_of_lt (a := 2) (by lia), Nat.mod_eq_of_lt hi]
--   · specialize hmod (F.length - 2)
--     simp only [CharP.cast_eq_zero, zero_sub, neg_add_cancel, ZMod.val_zero] at hmod
--     have h2 : NeZero (1 : ZMod F.length) := ⟨by simp⟩
--     have h2 : NeZero (2 : ZMod F.length) := ⟨ZMod.ofNat_ne_zero_of_lt (by lia)⟩
--     simpa [ZMod.val_neg_of_ne_zero, ZMod.val_ofNat_of_lt (show 2 < F.length by lia),
--       show (-2 : ZMod F.length) + 1 = -1 by ring, ZMod.val_neg_of_ne_zero, ZMod.val_one,
--       Nat.bodd_sub (show 2 ≤ F.length by lia), hodd] using hmod
--   specialize hmod (-1)
--   simpa [show (-1 : ZMod F.length) + 2 = 1 by ring, ZMod.val_neg_of_ne_zero, ZMod.val_one,
--     Nat.bodd_sub (show 1 ≤ F.length by lia), hodd] using hmod



lemma IsRotaryFan.rotate (h : M.IsRotaryFan F b) (n : ℕ) :
    M.IsRotaryFan (F.rotate n) (b != n.bodd) := by
  have _ : NeZero F.length := ⟨by grind⟩
  have _ : NeZero (F.rotate n).length := ⟨by grind [length_rotate]⟩
  refine isRotaryFan_of_forall _ _ _ (by simpa using h.length_ge)
    (nodup_rotate.2 h.isFan.nodup) fun i ↦ ?_
  simp
  have := h.isTriangle (i.val + n)
  convert h.isTriangle (i.val + n)
  · simp_rw [← Nat.cast_add, ZMod.val_natCast, mod_bodd h.length_bodd, bne_comm (a := n.bodd),
      Nat.bodd_add]
  · rw [← Nat.cast_add, ZMod.val_natCast]
  · simp [← ZMod.val_natCast, Nat.cast_add, add_right_comm]
  simp only [← ZMod.val_natCast, Nat.cast_add, ZMod.natCast_val, length_rotate, dvd_refl,
    ZMod.cast_add, add_right_comm]
  convert rfl
  rw [ZMod.cast_eq_val, ZMod.val_ofNat_of_lt (by grind [length_rotate]), ← Nat.cast_ofNat]

lemma IsRotaryFan.reverse (h : M.IsRotaryFan F b) : M.IsRotaryFan F.reverse (!b) := by
  refine isRotaryFan_of_forall _ _ _ (by simpa using h.length_ge) (by simpa using h.isFan.nodup) ?_
  simp
  -- refine ⟨by simpa using h.isFan.reverse, ?_, ?_⟩
  -- · simp only [length_reverse, getElem_reverse, tsub_self, tsub_zero,
  --     show F.length - 1 - (F.length - 2) = 1 by grind]
  --   exact h.isTriad.reverse
  -- simp only [Bool.not_not, length_reverse, getElem_reverse, tsub_self, tsub_zero, Nat.sub_sub]
  -- exact h.isTriangle.reverse

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

lemma IsRotaryFan.eConn_eq (h : M.IsRotaryFan F b) : M.eConn {e | e ∈ F} = 0 := by
  refine h.isFan.eConn_eq_zero_of_mem_closure_mem_closure ?_ ?_
  · refine mem_of_mem_of_subset h.isTriad.mem_closure₂ <| closure_subset_closure _ ?_
    exact pair_subset (getElem_mem_tail _ (by grind) _) (getElem_mem_tail _ (by grind) _)
  refine mem_of_mem_of_subset h.isTriangle.mem_closure₂ <| closure_subset_closure _ ?_
  exact pair_subset (getElem_mem_dropLast (by grind)) (getElem_mem_dropLast (by grind))

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
  refine ⟨(isFan_iff_forall (by grind)).2 ?_, aux (by grind) h.isTriangle, aux (by grind) h.isTriad⟩
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
        h.isTriad.isCircuit.mem_iff_mem_of_parallel_bDual hp
      have hwin := h.isTriangle.notMem_of_mem_of_parallel hp
      grind [h.isFan.nodup.getElem_inj_iff]
    have h1 := (h.isFan.isTriangle_bDual (by grind)).isCircuit.mem_iff_mem_of_parallel_bDual hp
    have h2 := h.isTriad.notMem_of_mem_of_parallel hp (by simp)
    have h3 := h.isTriangle.isCircuit.mem_iff_mem_of_parallel_bDual hp
    obtain ⟨rfl, h4⟩ : j = 1 ∧ F.length = 4 := by grind [h.isFan.nodup.getElem_inj_iff]
    have h4' := (h.isFan.isTriangle_getElem 2 (by lia)).isCircuit.mem_iff_mem_of_parallel_bDual
      hp.symm
    simp [h.isFan.nodup.getElem_inj_iff] at h4'
  | succ i ih =>
    obtain rfl | j := j; lia
    have hwin := ih (h.rotate 1) (j := j) (hj := by grind [length_rotate])
      (hi := by grind [length_rotate]) (by simpa) (by lia)
    simpa [getElem_rotate, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hwin

lemma IsRotaryFan.contract_delete (h : M.IsRotaryFan F false) (hlen : 4 < F.length) :
    (M ＼ {F[0]} ／ {F[1]}).IsRotaryFan F.tail.tail false := by

  have h6 : 6 ≤ F.length := sorry
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
    convert (h.rotate (n + 2)).isFan.isCircuit_interval (show 0 < 4 by lia)
      (by grind [length_rotate]) (by simp [hnb]) (by simp [hnb]) (by simp [hnb])
    simp +contextual [Set.ext_iff, iff_def, or_imp,
      h.isFan.nodup.getElem_mem_getElems_rotate_iff _ sorry, hn, add_assoc]

    -- simp [hnb, getElems_ro] at hC
    rw [getElems_insert _ _ (by grind [length_rotate]),
      getElems_insert _ _ (by grind [length_rotate]),
      (h.rotate 1).isFan.nodup.getElems_ofPred_and, show Ico 0 4 = {0, 1, 2, 3} by grind] at hC
    simp [hnb] at hC

  -- have := (h.isFan.contract_head (by lia) (by simp)).delete_head (by grind) (fun _ ↦ ?_)
  -- · simpa
  -- · suffices ¬M✶.Parallel F[1] F[F.length - 1 - 1 + 1] by
  --     simpa [delete_parallel_iff, h.isFan.nodup.getElem_inj_iff]
  --   exact fun hp ↦ by simpa using h.dual.isFan.eq_eq_of_parallel h6 (by lia) hp
  -- · suffices (M ／ {F[0]}).IsTriangle {F[n + 4], F[n + 5], F[2]} by
  --     simpa [hn, add_assoc, h.isFan.nodup.getElem_inj_iff]

  -- sorry



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
