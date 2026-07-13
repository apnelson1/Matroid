import Matroid.Connectivity.Fan.Circuit
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Circular.ZMod

open Set Function

theorem btw_iff_sbtw {α : Type*} [CircularOrder α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : btw a b c ↔ sbtw a b c := by
  refine ⟨fun h ↦ by_contra fun hcon ↦ ?_, fun h ↦ h.btw⟩
  rw [← btw_iff_not_sbtw] at hcon
  grind [h.antisymm hcon]

theorem btw_iff_not_btw {α : Type*} [CircularOrder α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : btw a b c ↔ ¬ btw a c b := by
  rw [btw_iff_sbtw hab hbc hac, sbtw_iff_not_btw, btw_cyclic]

theorem SBtw.sbtw.ne₁₂ {α : Type*} [CircularPreorder α] {a b c : α} (habc : sbtw a b c) :
    a ≠ b := by
  rintro rfl
  exact sbtw_irrefl_left habc

theorem SBtw.sbtw.ne₂₃ {α : Type*} [CircularPreorder α] {a b c : α} (habc : sbtw a b c) :
    b ≠ c := by
  rintro rfl
  exact sbtw_irrefl_right habc

theorem SBtw.sbtw.ne₁₃ {α : Type*} [CircularPreorder α] {a b c : α} (habc : sbtw a b c) :
    a ≠ c := by
  rintro rfl
  exact sbtw_irrefl_left_right habc

theorem ZMod.induction_aux {n : ℕ} [NeZero n] {motive : ZMod n → Prop} {i : ZMod n} (hi : motive i)
    (ih : ∀ s, motive s → motive (s + 1)) (a : ZMod n) : motive a := by
  obtain rfl | hne := eq_or_ne a i
  · exact hi
  suffices hlt : ((a - 1) - i).val < (a - i).val by
    simpa using ih _ <| ZMod.induction_aux (a := a - 1) hi ih
  obtain rfl | rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact False.elim <| hne <| Subsingleton.elim (α := Fin 1) a i
  have aux := ZMod.val_add (a - 1 - i) 1
  rw [ZMod.val_one'' (by simp), sub_right_comm, sub_add_cancel, Nat.mod_eq_of_lt] at aux
  · rw [aux, sub_right_comm]
    exact lt_add_one ..
  simp only [Order.lt_add_one_iff, add_le_add_iff_right]
  rw [ZMod.val_sub, ZMod.val_one'' (by simp)]
  · grind
  rwa [ZMod.val_one'' (by simp), Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero, sub_eq_zero]
termination_by (a - i).val

@[elab_as_elim]
theorem ZMod.induction {n : ℕ} [NeZero n] {motive : ZMod n → Prop} (h0 : ∃ i, motive i)
    (add_one : ∀ s, motive s → motive (s + 1)) (a : ZMod n) : motive a :=
  ZMod.induction_aux h0.choose_spec add_one _

theorem ZMod.btw_iff {n : ℕ} [NeZero n] {a b c : ZMod n} :
    btw a b c ↔ a.val ≤ b.val ∧ b.val ≤ c.val ∨ b.val ≤ c.val ∧ c.val ≤ a.val ∨
      c.val ≤ a.val ∧ a.val ≤ b.val := by
  obtain rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  exact Fin.btw_iff

theorem ZMod.sbtw_iff {n : ℕ} [NeZero n] {a b c : ZMod n} :
    sbtw a b c ↔ a.val < b.val ∧ b.val < c.val ∨ b.val < c.val ∧ c.val < a.val ∨
      c.val < a.val ∧ a.val < b.val := by
  obtain rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  exact Fin.sbtw_iff

theorem ZMod.btw_iff_zero_left {n : ℕ} [NeZero n] {a b : ZMod n} (hb : b ≠ 0) :
    btw 0 a b ↔ a.val ≤ b.val := by
  simp [ZMod.btw_iff, hb]

theorem ZMod.sbtw_iff_zero_left {n : ℕ} [NeZero n] {a b : ZMod n} :
    sbtw 0 a b ↔ 0 < a.val ∧ a.val < b.val := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [ZMod.sbtw_iff]
  obtain rfl | hb := eq_or_ne b 0
  · simp [ZMod.sbtw_iff]
  rw [sbtw_iff_not_btw, btw_cyclic, ZMod.btw_iff_zero_left ha, Nat.pos_iff_ne_zero, Ne,
    ZMod.val_eq_zero, and_iff_right ha, not_le]

theorem ZMod.sbtw_add_iff {n : ℕ} [NeZero n] {a b c r : ZMod n} :
    sbtw (a + r) (b + r) (c + r) ↔ sbtw a b c := by
  suffices aux : ∀ {x y z : ZMod n}, sbtw (x - 1) (y - 1) (z - 1) → sbtw x y z by
    have aux2 : ∀ {x y z d : ZMod n}, sbtw (x - d) (y - d) (z - d) → sbtw x y z := by
      intro x y z d
      induction d using ZMod.induction generalizing x y z with
      | h0 => exact ⟨0, by simp⟩
      | add_one s h' => exact fun h ↦ aux <| h' <| by rwa [sub_sub, sub_sub, sub_sub, add_comm]
    exact ⟨fun h ↦ aux2 (d := -r) (by simpa), fun h ↦ aux2 (d := r) (by simpa)⟩
  intro x y z hxyz
  have hxy : x ≠ y := by simpa using hxyz.ne₁₂
  have hyz : y ≠ z := by simpa using hxyz.ne₂₃
  have hxz : x ≠ z := by simpa using hxyz.ne₁₃
  obtain rfl | rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact False.elim <| hxy <| Subsingleton.elim (α := Fin 1) x y
  wlog h0 : y ≠ 0 ∧ z ≠ 0 generalizing x y z with aux
  · obtain rfl | rfl : y = 0 ∨ z = 0 := by grind
    · rw [← sbtw_cyclic] at hxyz ⊢; grind
    rw [sbtw_cyclic] at hxyz ⊢; grind
  have aux (a : ZMod (n + 2)) : val (1 : ZMod (n + 2)) ≤ a.val ↔ a ≠ 0 := by
    rw [ZMod.val_one'' (by simp), Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]
  rw [← aux, ← aux] at h0
  rw [sbtw_iff, ZMod.val_sub h0.1, ZMod.val_sub h0.2, ZMod.val_one'' (by simp)] at hxyz
  obtain rfl | hx0 := eq_or_ne x 0
  · rw [sbtw_iff_zero_left]
    rw [zero_sub, val_neg_one] at hxyz
    grind [val_one'' (n := n + 2) (by simp)]
  rw [ZMod.val_sub (by rwa [aux])] at hxyz
  rw [sbtw_iff]
  grind [val_one'' (n := n + 2) (by simp)]

theorem ZMod.btw_add_iff {n : ℕ} [NeZero n] {a b c r : ZMod n} :
    btw (a + r) (b + r) (c + r) ↔ btw a b c := by
  rw [btw_iff_not_sbtw, ZMod.sbtw_add_iff, btw_iff_not_sbtw]

namespace Matroid
set_option linter.style.longLine false


variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

/-- A cyclic fan is an injective function `J` from `{0,1} × (ZMod n)` to `E(M)` so that
for all `i`, the triple `J 0 i, J 0 (i + 1), J 1 i` is a triangle, and the triple
`J 1 i, J 0 (i + 1), J 1 (i + 1)` is a triad.

We do not insist that `n ≠ 0`, and thereby allow for infinite fans.  -/
structure IsCyclicFan (M : Matroid α) (n : ℕ) (J : Bool → ZMod n → α) : Prop where
  isTriangle_bDual : ∀ b i, (M.bDual b).IsTriangle {J b i, J b (i + 1), J (!b) (i + b.toNat)}
  inj : ∀ b b' i i', J b i = J b' i' → i = i' ∧ b = b'

lemma IsCyclicFan.injective {J} (h : M.IsCyclicFan n J) {b : Bool} : Function.Injective (J b) :=
  fun _ _ hii' ↦ (h.inj _ _ _ _ hii').1

lemma IsCyclicFan.disjoint_range {J} (h : M.IsCyclicFan n J) :
    Disjoint (range (J false)) (range (J true)) := by
  grind [h.inj]

lemma IsCyclicFan.apply_ne {J} (h : M.IsCyclicFan n J) (i j) : J false i ≠ J true j := by
  grind [h.inj]

lemma IsCyclicFan.apply_ne' {J} (h : M.IsCyclicFan n J) (i j) : J true i ≠ J false j := by
  grind [h.inj]

lemma IsCyclicFan.mem_ground {J} (h : M.IsCyclicFan n J) (b : Bool) (i : ZMod n) :
    J b i ∈ M.E := by
  simpa using (h.isTriangle_bDual b i).mem_ground₁

lemma IsCyclicFan.subset_ground {J} (h : M.IsCyclicFan n J) :
    range (J true) ∪ range (J false) ⊆ M.E := by
  grind [h.mem_ground]

lemma IsCyclicFan.iUnion_subset_ground {J} (h : M.IsCyclicFan n J) : ⋃ b, range (J b) ⊆ M.E := by
  simpa [and_comm] using h.subset_ground

lemma IsCyclicFan.nonempty (h : M.IsCyclicFan n J) : M.Nonempty := by
  grw [← ground_nonempty_iff, ← h.iUnion_subset_ground]
  simp [range_nonempty]

@[simp]
lemma IsCyclicFan.encard_range [NeZero n] {J} (h : M.IsCyclicFan n J) {b} :
    (range (J b)).encard = n := by
  rw [← image_univ, h.injective.encard_image]
  simp [ENat.card_eq_coe_fintype_card]

@[simp]
lemma IsCyclicFan.encard_iUnion_range [NeZero n] {J} (h : M.IsCyclicFan n J) :
    (⋃ b, range (J b)).encard = 2 * n := by
  rw [iUnion_bool, encard_union_eq h.disjoint_range.symm, h.encard_range, h.encard_range, two_mul]

lemma IsCyclicFan.isTriangle {J} (h : M.IsCyclicFan n J) (i : ZMod n) :
    M.IsTriangle {J false i, J false (i + 1), J true i} := by
  simpa using h.isTriangle_bDual false i

lemma IsCyclicFan.isTriad {J} (h : M.IsCyclicFan n J) (i : ZMod n) :
    M.IsTriad {J true i, J true (i + 1), J false (i + 1)} := by
  simpa using h.isTriangle_bDual true i

lemma IsCyclicFan.ne_one {J} (h : M.IsCyclicFan n J) : n ≠ 1 := by
  rintro rfl
  exact (h.isTriangle 0).ne₁₂ rfl

lemma IsCyclicFan.two_le [NeZero n] {J} (h : M.IsCyclicFan n J) : 2 ≤ n := by
  grind [h.ne_one, NeZero.ne n]

lemma IsCyclicFan.neg {J} (h : M.IsCyclicFan n J) :
    M.IsCyclicFan n (fun b i ↦ J b (- b.toNat - i)) := by
  refine ⟨fun b i ↦ ?_, by grind [h.inj]⟩
  have hwin := insert_comm .. ▸ h.isTriangle_bDual b (- 1 - b.toNat - i)
  cases b
  · simpa [sub_add_eq_add_sub, sub_eq_add_neg] using hwin
  simpa [sub_add_eq_add_sub, ← sub_sub, show - i - 1 = - 1 - i by ring,
    show - 1 - i - 1 = -1 - 1 - i by ring] using hwin

lemma IsCyclicFan.dual_neg {J} (h : M.IsCyclicFan n J) :
    M✶.IsCyclicFan n (fun b i ↦ J (!b) (- i)) := by
  refine ⟨fun b i ↦ ?_, by grind [h.inj]⟩
  have hwin := bDual_dual .. ▸ insert_comm .. ▸ h.isTriangle_bDual (!b) ((- 1) + (- i))
  simp_rw [← singleton_union] at hwin ⊢
  convert hwin using 4
  · ring
  · simp
  cases b with simp

lemma IsCyclicFan.add {J} (h : M.IsCyclicFan n J) (d : ZMod n) :
    M.IsCyclicFan n (fun b i ↦ J b (i + d)) :=
  ⟨fun b i ↦ by simpa [add_right_comm] using h.isTriangle_bDual b (i + d), by grind [h.inj]⟩

lemma IsCyclicFan.dual {J} (h : M.IsCyclicFan n J) :
    M✶.IsCyclicFan n (fun b i ↦ J (!b) (i + b.toNat)) :=
  ⟨fun b i ↦ by simpa [add_right_comm] using h.isTriangle_bDual (!b) (i + b.toNat),
    fun b b' i i' h_eq ↦ by grind [h.inj]⟩

lemma IsCyclicFan.dual_sub {J} (h : M.IsCyclicFan n J) :
    M✶.IsCyclicFan n (fun b i ↦ J (!b) (i - (!b).toNat)) := by
  refine ⟨fun b i ↦ ?_, fun b b' i i' h_eq ↦ by grind [h.inj]⟩
  cases b
  · simpa using h.isTriad (i - 1)
  simpa using h.isTriangle i

lemma IsCyclicFan.exists_isCyclicFan_dual (h : M.IsCyclicFan n J) :
    ∃ J', M✶.IsCyclicFan n J' ∧ ∀ b, range (J' b) = range (J !b) := by
  refine ⟨_, h.dual_neg, fun b ↦ ?_⟩
  convert range_comp (Equiv.neg (ZMod n)) (g := J (!b)) using 1
  rw [Equiv.range_eq_univ, image_univ]

lemma IsCyclicFan.exists_isCyclicFan_dual' (h : M.IsCyclicFan n J) :
    ∃ J', M✶.IsCyclicFan n J' ∧ ⋃ b, range (J' b) = ⋃ b, range (J b) := by
  refine Exists.imp (fun K hK ↦ ?_) h.exists_isCyclicFan_dual
  simp [hK.2, iUnion_bool, union_comm, hK.1]

lemma isCyclicFan_aux_lt {F : List α} (hn : 2 ≤ n) (hF : 2 * n = F.length) {i : ZMod n} {d : Bool} :
    2 * i.val + d.toNat < F.length := by
  grind [Nat.add_one_le_of_lt <| @ZMod.val_lt _ (NeZero.of_gt hn) i]

lemma isCyclicFan_aux_inj {n : ℕ} (hn : 2 ≤ n) {i i' : ZMod n} {d d' : Bool}
    (h_eq : 2 * i.val + d.toNat = 2 * i'.val + d'.toNat) :
    i = i' ∧ d = d' := by
  have := NeZero.of_gt (show 1 < n from hn)
  obtain rfl | rfl := d.eq_or_eq_not d'
  · exact ⟨(ZMod.val_injective (n := n)) (by simpa using h_eq), rfl⟩
  cases d' with grind

/-- The cojoints of a cyclic fan are spanned by the joints. -/
lemma IsCyclicFan.range_true_subset_closure {J} (h : M.IsCyclicFan n J) :
    range (J true) ⊆ M.closure (range (J false)) := by
  rintro _ ⟨i, hi, rfl⟩
  exact mem_of_mem_of_subset (h.isTriangle i).mem_closure₃ <| M.closure_subset_closure (by grind)

/-- Any proper superset of the cojoints spans the fan. -/
lemma IsCyclicFan.subset_closure_of_ssubset [NeZero n] (h : M.IsCyclicFan n J)
    (hXJ : X ⊆ ⋃ i, range (J i)) (hX : range (J true) ⊂ X) : ⋃ i, range (J i) ⊆ M.closure X := by
  have hXE : X ⊆ M.E := hXJ.trans h.iUnion_subset_ground
  suffices aux (i) : J false i ∈ M.closure X
  · grw [iUnion_subset_iff, Bool.forall_bool, hX, and_iff_left (M.subset_closure X)]
    grind
  obtain ⟨y, hyX, hy⟩ := exists_of_ssubset hX
  obtain ⟨d, rfl⟩ : ∃ d, J false d = y := by grind [mem_iUnion, Bool.exists_bool]
  induction i using ZMod.induction with
  | h0 => exact ⟨d, M.mem_closure_of_mem hyX⟩
  | add_one s ih =>
    refine mem_of_mem_of_subset (h.isTriangle s).mem_closure₂ <|
      M.closure_subset_closure_of_subset_closure <| insert_subset ih ?_
    grw [← M.subset_closure X, ← hX]
    simp

lemma IsCyclicFan.contract {J} (h : M.IsCyclicFan n J) {X : Set α}
    (hX : ∀ b, Disjoint X (range (J b))) : (M ／ X).IsCyclicFan n J := by
  have h10 : (1 : ZMod n) ≠ 0 := by simp [ZMod.one_eq_zero_iff, h.ne_one]
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← contract_inter_ground_eq]; grind
  refine ⟨fun b i ↦ ?_, h.inj⟩
  cases b
  · simp only [bDual_false, Bool.not_false, Bool.toNat_false, Nat.cast_zero, add_zero]
    rw [isTriangle_iff, and_iff_left (h.isTriangle i).three_elements,
      isCircuit_iff_restr_eq_circuitOn (by simp) (by grind [h.mem_ground]),
      Skew.contract_restrict_eq, ← isCircuit_iff_restr_eq_circuitOn (by simp)
      (by grind [h.mem_ground])]
    · exact (h.isTriangle i).isCircuit
    rw [skew_iff_forall_isCircuit (by grind) hXE (h.isTriangle i).subset_ground]
    intro C hC hCss
    by_contra! hcon
    have hCtrue {j} (hjC : J true j ∈ C) : j = i := by
      grind [h.apply_ne', h.injective.eq_iff, hCss hjC]
    have h_or : J false i ∈ C ∨ J false (i + 1) ∈ C ∨ J true i ∈ C := by grind
    have h_iff1 : J false i ∈ C ↔ J true i ∈ C := by
      rw [show i = i - 1 + 1 by simp,
        (h.isTriad _).dual_isTriangle.swap_right.mem_iff_mem_of_isCocircuit (by simpa)]
      exact fun h ↦ by simpa [h10] using hCtrue h
    have h_iff2 : J true i ∈ C ↔ J false (i + 1) ∈ C := by
      rw [(h.isTriad i).dual_isTriangle.swap_left.mem_iff_mem_of_isCocircuit (by simpa)]
      exact fun h ↦ by simpa [h10] using hCtrue h
    by_cases hiC : J true i ∈ C
    · grind [hC.eq_of_superset_isCircuit (h.isTriangle i).isCircuit (by grind)]
    grind
  simp only [bDual_true, dual_contract, Bool.not_true, Bool.toNat_true, Nat.cast_one,
    isTriangle_iff, delete_isCircuit_iff, (h.isTriad i).isCocircuit, (h.isTriad i).three_elements]
  grind

lemma IsCyclicFan.minor {J N} (h : M.IsCyclicFan n J) (hNM : N ≤m M)
    (hJN : ∀ i, range (J i) ⊆ N.E) : N.IsCyclicFan n J := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  simpa using ((h.contract (X := C) (by grind)).dual_neg.contract (X := D) (by grind)).dual_neg

lemma IsCyclicFan.delete {J} (h : M.IsCyclicFan n J) {X : Set α}
    (hJN : ∀ b, Disjoint (range (J b)) X) : (M ＼ X).IsCyclicFan n J :=
  h.minor (delete_isMinor ..) fun b ↦ by grind [h.mem_ground]

lemma IsCyclicFan.eRk_eq [NeZero n] {J} (h : M.IsCyclicFan n J) : M.eRk (⋃ i, range (J i)) = n := by
  have aux' (N : Matroid α) {K} (hK : N.IsCyclicFan n K) : N.eRk (⋃ b, range (K b)) ≤ n := by
    grw [iUnion_bool, ← eRk_union_closure_right_eq, union_eq_self_of_subset_left, eRk_closure_eq,
      eRk_le_encard, hK.encard_range]
    exact hK.range_true_subset_closure
  refine (aux' _ h).antisymm ?_
  have h' : (M ↾ ⋃ b, range (J b)).IsCyclicFan n J :=
    h.minor (restrict_isRestriction _ _ h.iUnion_subset_ground).isMinor <| by simp [iUnion_bool]
  obtain ⟨F', hF', hFF'⟩ := h'.exists_isCyclicFan_dual'
  have hr := ((M ↾ (⋃ b, Set.range (J b))).eRank_add_eRank_dual)
  rw [restrict_ground_eq, h'.encard_iUnion_range, eRank_restrict, ← eRk_ground,
    dual_ground, restrict_ground_eq] at hr
  have := hFF' ▸ aux' _ hF'
  enat_to_nat!; lia

/-- The joints of a cyclic fan are independent. -/
lemma IsCyclicFan.indep [NeZero n] {J} (h : M.IsCyclicFan n J) : M.Indep (range (J false)) := by
  grw [indep_iff_eRk_eq_encard_of_finite (finite_range (J false)), le_antisymm_iff,
    and_iff_right (eRk_le_encard ..), h.encard_range, ← h.eRk_eq, iUnion_bool,
    ← eRk_closure_eq, ← closure_union_closure_right_eq, union_eq_self_of_subset_left
    h.range_true_subset_closure, closure_closure, eRk_closure_eq]

/-- A cyclic fan in a connected matroid must be the entire ground set. -/
lemma IsCyclicFan.eq_ground_of_connected [NeZero n] {J} (h : M.IsCyclicFan n J) (hM : M.Connected) :
    ⋃ b, range (J b) = M.E := by
  suffices aux : M.eConn (⋃ b, range (J b)) = 0 by
    exact hM.eq_ground_of_eConn_eq_zero aux (by simp [range_nonempty ..]) h.iUnion_subset_ground
  refine IsRankFinite.eConn_eq_zero_of_eRk_dual_le_dual_restrict_eRank ?_ ?_ h.iUnion_subset_ground
  · exact isRkFinite_of_finite _ <| by simp [finite_range .., iUnion_bool]
  obtain ⟨K, hK, hJK⟩ := h.exists_isCyclicFan_dual'
  rw [← hJK, hK.eRk_eq, ← eRk_ground, dual_ground, restrict_ground_eq,
    (hK.minor _ (by simp [iUnion_bool])).eRk_eq]
  exact (restrict_isRestriction _ _ (by simpa using hK.iUnion_subset_ground)).isMinor.dual

lemma IsCyclicFan.finite_of_connected [NeZero n] (h : M.IsCyclicFan n J) (hM : M.Connected) :
    M.Finite := by
  rw [finite_iff, ← h.eq_ground_of_connected hM]
  simp [iUnion_bool, finite_range]

/-- If `F` is a fan on the entire ground set of a simple, cosimple matroid that starts with a joint,
then `F` determines a cyclic fan. We insist that `F` starts with a joint so that the description
of the cyclic fan doesn't involve wrapping indices around. -/
lemma IsFan.isCyclicFan_of_ground_eq (hF : M.IsFan F false c) (hM : M.Simple) (hM' : M✶.Simple)
    (hFE : {e | e ∈ F} = M.E) : ∃ (n : ℕ) (hn : 2 ≤ n) (hnF : 2 * n = F.length),
    M.IsCyclicFan n <| fun d i ↦ F[2 * i.val + d.toNat]'(isCyclicFan_aux_lt hn hnF) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' <| hF.length_ge_four_of_eq_ground hFE
  obtain ⟨hml, ht⟩ := hF.isTriangle_bDual_of_simple (n := m + 2) (by lia) hM hM' hFE
  rw [hm, even_iff_exists_two_mul] at hml
  obtain ⟨n, hmn⟩ := hml
  have hn1 : Fact (1 < n) := ⟨by grind⟩
  refine ⟨n, by lia, by lia, fun d i ↦ ?_, fun d d' i i' h ↦ ?_⟩
  · obtain hin | hin := (show i.val + 1 ≤ n from i.val_lt).eq_or_lt
    · have hi1 : (i + 1).val = 0 := by simp [ZMod.val_add, ZMod.val_one, hin]
      cases d
      · simp only [bDual_false, show 2 * i.val = m + 2 by lia, Bool.toNat_false, add_zero, hi1,
          mul_zero, Nat.cast_zero, Bool.not_false, Bool.toNat_true]
        rwa [pair_comm]
      simp only [bDual_true, Bool.toNat_true, hi1, mul_zero, zero_add, Nat.cast_one, Bool.not_true,
        Bool.toNat_false, add_zero, dual_isTriangle_iff, show 2 * i.val + 1 = m + 3 by lia]
      obtain rfl : c = true := by simpa [hm, hmn, Nat.bodd_two] using hF.length_bodd_eq
      refine (IsTriangle.rotate_left ?_).rotate_left
      simpa [hm] using
        (hF.reverse.isTriangle_bDual_of_simple (n := m + 2) (by simpa) hM hM' (by simpa)).2
    have hrw : (i + 1).val = i.val + 1 := by
      rw [ZMod.val_add_of_lt (by simpa [ZMod.val_one]), ZMod.val_one]
    have hwin := pair_comm .. ▸ hF.isTriangle_getElem (i := 2 * i.val + d.toNat) (by grind)
    cases d with simp_all [mul_add]
  exact isCyclicFan_aux_inj (by lia) (by rwa [hF.getElem_inj_iff] at h)

/-- Any fan on the ground set of a simple, cosimple matroid gives a cyclic fan. -/
lemma IsFan.exists_isCyclicFan_of_ground_eq (hF : M.IsFan F b c) (hM : M.Simple) (hM' : M✶.Simple)
    (hFE : {e | e ∈ F} = M.E) : ∃ n J, 2 * n = F.length ∧ M.IsCyclicFan n J := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' <| hF.length_ge_four_of_eq_ground hFE
  cases b
  · obtain ⟨n, hn, hnF, h⟩ := hF.isCyclicFan_of_ground_eq hM hM' hFE
    exact ⟨n, _, hnF, h⟩
  obtain ⟨n, hn, hnF, h⟩ := hF.dual.isCyclicFan_of_ground_eq hM' (by simpa) hFE
  exact ⟨n, _, hnF, M.dual_dual ▸ h.dual⟩

/-- Every cyclic fan gives a fan. -/
lemma IsCyclicFan.isFan [NeZero n] {J} (h : M.IsCyclicFan n J) :
    M.IsFan ((List.range (2 * n)).map fun i ↦ J i.bodd i.div2) false true := by
  have h2 := h.two_le
  refine isFan_of_eq_of_forall_triangle (by grind) ?_ (by simp) ?_
  · simp [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hlt hj h_eq
    rw [List.getElem?_eq_getElem (by grind), List.getElem?_eq_getElem (by grind)] at h_eq
    simp only [List.getElem_range, Option.map_some, Option.some.injEq] at h_eq
    obtain ⟨hij, hij'⟩ := h.inj _ _ _ _ h_eq
    rw [ZMod.natCast_eq_natCast_iff] at hij
    grind [i.bodd_add_div2, j.bodd_add_div2, hij.eq_of_lt_of_lt]
  simp only [List.length_map, List.length_range, Bool.false_bne, List.getElem_map,
    List.getElem_range, Nat.bodd_succ, Nat.div2_succ, Nat.succ_eq_add_one, Bool.not_not,
    Bool.cond_not]
  intro i hi
  cases hd : i.bodd
  · simpa [hd, pair_comm (J true _)] using h.isTriangle_bDual i.bodd i.div2
  simpa [hd, pair_comm (J false _)] using h.isTriangle_bDual i.bodd i.div2

/-- Every cyclic fan gives a fan for any desired starting point.  -/
lemma IsCyclicFan.isFan_rotate [NeZero n] {J} (h : M.IsCyclicFan n J) (b : Bool) (p : ZMod n) :
    M.IsFan ((List.range (2 * n)).map fun i ↦ J (i.bodd != b) (p + (i + b.toNat).div2)) b (!b) := by
  cases b
  · simpa [add_comm] using (h.add p).isFan
  convert M.dual_dual ▸ ((h.dual.add p).isFan).dual using 4 with v w
  · simp
  cases hv : v.bodd with simp [hv, add_comm, add_assoc]

lemma IsCyclicFan.restrict_connected [NeZero n] (h : M.IsCyclicFan n J) :
    (M ↾ (⋃ i, range (J i))).Connected := by
  have hT1 {i b} : (M ↾ (⋃ i, range (J i))).ConnectedTo (J b i) (J false i) :=
    ((h.isTriangle i).isCircuit.isCircuit_restrict_of_subset
      (by simp [insert_subset_iff])).mem_connectedTo_mem (by cases b with simp) (by simp)
  suffices aux : ∀ b i, (M ↾ (⋃ i, range (J i))).ConnectedTo (J false 0) (J b i) by
    rw [connected_iff, and_iff_right (by simp [← ground_nonempty_iff, range_nonempty])]
    simp only [restrict_ground_eq, mem_iUnion, mem_range]
    rintro _ _ ⟨i, a, rfl⟩ ⟨j, b, rfl⟩
    exact (aux ..).symm.trans (aux ..)
  intro b i
  induction i  using ZMod.induction generalizing b with
  | h0 => exact ⟨0, fun b ↦ hT1.symm⟩
  | add_one s ih =>
    refine ((ih false).trans ?_).trans hT1.symm
    exact ((h.isTriangle s).isCircuit.isCircuit_restrict_of_subset
      (by simp [insert_subset_iff])).mem_connectedTo_mem (by simp) (by simp)

/-- Any two joints of a cyclic fan form a circuit with either interval of cojoints between them. -/
lemma IsCyclicFan.isCircuit (h : M.IsCyclicFan n J) {d : ℕ} (hd : d + 1 < n) (i : ZMod n) :
    M.IsCircuit <| insert (J false i) <| insert (J false (i + d + 1)) <|
      ((fun (x : ℕ) ↦ J true (i + x)) '' Iic d) := by
  have hn : NeZero n := ⟨by lia⟩
  convert (h.isFan_rotate true (i.val - 1)).isCircuit_interval (i := 1) (j := 2 * d + 3)
    (by simp) (by simp [show 2 * d + 3 < 2 * n by lia]) (by grind) (by simp) (by simp)
  · simp
  · simp [add_assoc i d 1]
  ext e
  simp only [mem_image, mem_Iic, List.altBetween, Bool.not_true, Bool.bne_true, ZMod.natCast_val,
    ZMod.cast_id', id_eq, Bool.toNat_true, Nat.div2_succ, Nat.succ_eq_add_one, List.getElem_map,
    List.getElem_range, List.length_map, List.length_range, exists_and_left, exists_prop,
    mem_setOf_eq]
  constructor
  · rintro ⟨j, hjd, rfl⟩
    exact ⟨2 * j + 2, by lia, by lia, by simp, by lia, by simp⟩
  rintro ⟨rfl | rfl | i, hi1, hilt, hib, hin, rfl⟩
  · lia
  · simp at hib
  exact ⟨i.div2, by grind, by simp [show i.bodd = false by simpa using hib]⟩

lemma IsCyclicFan.isHyperplane_rim_of_isCircuit_rim [NeZero n] (h : M.IsCyclicFan n J)
    (hJM : ⋃ i, range (J i) = M.E) (hC : M.IsCircuit (range (J true))) :
    M.IsHyperplane (range (J true)) := by
  rw [isHyperplane_iff_maximal_nonspanning, maximal_iff_forall_ssuperset]
  have hfin : M.RankFinite := by
    grw [← eRank_lt_top_iff, ← eRk_ground, ← hJM, h.eRk_eq]
    simp
  refine ⟨?_, ?_⟩
  · rw [nonspanning_iff_eRk_lt, ← ENat.add_one_lt_add_one_iff, hC.eRk_add_one_eq,
      h.encard_range, ← eRk_ground, ← hJM, h.eRk_eq]
    simp
  refine fun X hXT hnsp ↦ hnsp.not_spanning ?_
  grw [spanning_iff_ground_subset_closure, ← hJM, h.subset_closure_of_ssubset (by grind) hXT]

/-- If `C` is a nonspanning circuit in a cyclic fan that is not the set of all cojoints,
then there are two cojoints outside `C`, and a cojoint inside `C` between them. -/
lemma IsCyclicFan.exists_btw_of_isNonspanningCircuit [NeZero n] (h : M.IsCyclicFan n J)
    (hE : ⋃ i, range (J i) = M.E) (hC : M.IsNonspanningCircuit C) (hnss : C ≠ (range (J true))) :
    ∃ (p q r : ZMod n), btw p q r ∧ p ≠ q ∧ p ≠ r ∧ J true p ∉ C ∧ J true q ∈ C ∧ J true r ∉ C := by
  have hle : C.encard ≤ n := by
    grw [← h.eRk_eq, hE, eRk_ground, ← hC.isCircuit.eRk_add_one_eq, hC.nonspanning.eRk_add_one_le]
  obtain ⟨p, hp⟩ : ∃ a, J true a ∉ C := by
    contrapose! hnss
    rw [(finite_range ..).eq_of_subset_of_encard_le (t := C) (by grind)]
    rwa [h.encard_range]
  obtain ⟨q, hq⟩ : ∃ q, J true q ∈ C :=
    by_contra fun hcon ↦ (h.indep.subset (by grind [iUnion_bool])).not_dep hC.isCircuit.dep
  by_cases! hr : ∃ r ≠ p, J true r ∉ C
  · obtain ⟨r, hrp, hr⟩ := hr
    obtain rfl | hpq := eq_or_ne p q
    · exact ⟨r, p, p, btw_refl_right .., hrp, hrp, hr, hq, hp⟩
    obtain rfl | hrq := eq_or_ne r q
    · exact ⟨_, _, _, btw_refl_right .., hpq, hpq, hp, hq, hr⟩
    obtain hpqr | hpqr := btw_total p q r
    · exact ⟨p, q, r, hpqr, hpq, hrp.symm, hp, hq, hr⟩
    exact ⟨r, q, p, hpqr, hrq, hrp, hr, hq, hp⟩
  have hn : (1 : ZMod n) ≠ 0 := by simp [ZMod.one_eq_zero_iff, h.ne_one]
  have h1 : J false (p + 1) ∈ C := (h.isTriad p).swap_left.mem_of_mem_of_notMem_of_is_Cocircuit
    hC.isCircuit.isCocircuit (hr _ (by simpa)) hp
  have h0 : J false p ∈ C := by
    simpa using (h.isTriad (p - 1)).mem_of_mem_of_notMem_of_is_Cocircuit hC.isCircuit.isCocircuit
      (hr _ (by simpa)) (by simpa)
  have hne : p ≠ p + 1 := by simpa
  have hssC : insert (J false p) (insert (J false (p + 1)) (range (J true) \ {J true p})) ⊆ C := by
    grind
  grw [← hssC, encard_insert_of_notMem (by grind [h.inj]), encard_insert_of_notMem
    (by grind [h.disjoint_range]), ← encard_le_encard_diff_singleton_add_one, h.encard_range] at hle
  simp at hle

lemma IsCyclicFan.eq_of_isNonspanningCircuit [NeZero n] (h : M.IsCyclicFan n J)
    (hE : ⋃ i, range (J i) = M.E) {C : Set α} (hC : M.IsNonspanningCircuit C)
    (hne : C ≠ range (J true)) :
    ∃ (i : ZMod n) (d : ℕ), d + 1 < n ∧ C = insert (J false i) (insert (J false (i + d + 1))
      ((fun (x : ℕ) ↦ J true (i + x)) '' Iic d)) := by
  obtain ⟨p, q, r, hpqr, hpq, hpr, hp, hq, hr⟩ :=
    h.exists_btw_of_isNonspanningCircuit hE hC hne
  obtain ⟨p', q', h1p', hp'q', hq', hp'e, hq'e, hC⟩ :=
    (h.isFan_rotate false p).exists_eq_interval_of_notMem_mem_notMem (s := 1)
      (i := 2 * (q - p).val + 1) (t := 2 * (r - p).val + 1)
      (by grind [show (q - p).val ≠ 0 by simpa [sub_eq_zero] using hpq.symm])
      (by
        rw [← ZMod.btw_add_iff (r := -p), add_neg_cancel, ← sub_eq_add_neg, ← sub_eq_add_neg,
          ZMod.btw_iff_zero_left (by rwa [Ne, sub_eq_zero, eq_comm])] at hpqr
        simp [hpqr.lt_iff_ne, (ZMod.val_injective _).eq_iff, sub_left_inj, show q ≠ r by grind])
      (by grind) (by simp) (by simp) hC.isCircuit (by simpa) (by simpa) (by simpa)
  obtain ⟨p', rfl⟩ := (show Even p' by grind [Nat.bodd_eq_ite]).exists_two_nsmul
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hp'q'.le
  obtain ⟨rfl | d, rfl⟩ := (show Even d by grind [Nat.bodd_eq_ite]).exists_two_nsmul
  · simp at hp'q'
  refine ⟨p + p', d, by grind, ?_⟩
  convert hC
  · simp
  · simp [← mul_add, ← add_assoc]
  clear! C M  hq'e hp'e
  induction d with
  | zero =>
    rw [zero_add, smul_eq_mul, smul_eq_mul, mul_one, altBetween_add_two rfl.le (by simp) (by grind)]
    simp [Iic]
  | succ d ih =>
    rw [← Order.succ_eq_add_one, Order.Iic_succ, Order.succ_eq_add_one, image_insert_eq, ih
      (by grind) (by grind), eq_comm, smul_eq_mul, smul_eq_mul, mul_add, mul_one, ← add_assoc,
      altBetween_add_two (by grind) (by simp) (by grind)]
    simp [← mul_add, ← add_assoc]

/-- Any two cyclic fans have the same nonspanning circuits, except possibly the rim-/
lemma IsCyclicFan.isNonspanningCircuit_iff_isNonspanningCircuit {N : Matroid α} [NeZero n]
    (hM : M.Connected) (hN : N.Connected) (hJM : M.IsCyclicFan n J) (hJN : N.IsCyclicFan n J)
    (hne : C ≠ range (J true)) : M.IsNonspanningCircuit C ↔ N.IsNonspanningCircuit C := by
  wlog hC : M.IsNonspanningCircuit C generalizing M N with aux
  · rw [iff_false_intro hC, false_iff]
    exact fun hNC ↦ hC <| (aux hN hM hJN hJM hNC).1 hNC
  refine iff_of_true hC ?_
  have hE : M.E = N.E := by rw [← hJM.eq_ground_of_connected hM, ← hJN.eq_ground_of_connected hN]
  have hMr : M.eRank = n := by rw [← eRk_ground, ← hJM.eq_ground_of_connected hM, hJM.eRk_eq]
  have hNr : N.eRank = n := by rw [← eRk_ground, ← hJN.eq_ground_of_connected hN, hJN.eRk_eq]
  obtain ⟨i, d, hd, hC_eq⟩ := hJM.eq_of_isNonspanningCircuit (hJM.eq_ground_of_connected hM) hC hne
  have hCc : N.IsCircuit C := hC_eq ▸ hJN.isCircuit hd i
  have hNfin : N.RankFinite := by
    rw [← eRank_lt_top_iff, hNr]
    simp
  have hMfin : M.RankFinite := by
    rw [← eRank_lt_top_iff, hMr]
    simp
  refine ⟨?_, hCc⟩
  rw [nonspanning_iff_eRk_lt hCc.subset_ground, hNr, ← ENat.add_one_lt_add_one_iff,
    hCc.eRk_add_one_eq, ← hC.isCircuit.eRk_add_one_eq, ENat.add_one_lt_add_one_iff, ← hMr,
    ← nonspanning_iff_eRk_lt hC.subset_ground]
  exact hC.nonspanning

lemma foo {N : Matroid α} [NeZero n] (hM : M.Connected) (hN : N.Connected) (hJM : M.IsCyclicFan n J)
    (hJN : N.IsCyclicFan n J) :
      (M = N)
    ∨ (∃ (h : M.IsCircuitHyperplane (range (J true))), N = M.relax _ (IsLawfulRelaxation.single h))
    ∨ (∃ (h : N.IsCircuitHyperplane (range (J true))), M = N.relax _ (IsLawfulRelaxation.single h))
    := by
  wlog hC : M.IsNonspanningCircuit (range (J true)) → N.IsNonspanningCircuit (range (J true))
    generalizing M N with aux
  · grind [aux hN hM hJN hJM (by grind)]
  have hNE := hJN.eq_ground_of_connected hN
  have hME := hJM.eq_ground_of_connected hM
  have hMr : M.eRank = n := by rw [← eRk_ground, ← hJM.eq_ground_of_connected hM, hJM.eRk_eq]
  have hNr : N.eRank = n := by rw [← eRk_ground, ← hJN.eq_ground_of_connected hN, hJN.eRk_eq]
  have hMfin : M.RankFinite := by
    rw [← eRank_lt_top_iff, hMr]
    simp
  have hNfin : N.RankFinite := by rwa [← eRank_lt_top_iff, hNr, ← hMr, eRank_lt_top_iff]
  by_cases hCM : M.IsNonspanningCircuit (range (J true))
  · left
    refine ext_isNonspanningCircuit (by rw [← hNE, hME]) (by rw [hMr, hNr]) fun C hCE ↦ ?_
    obtain rfl | hne := eq_or_ne C (range (J true))
    · grind
    rw [hJM.isNonspanningCircuit_iff_isNonspanningCircuit hM hN hJN hne]
  by_cases hCN : N.IsNonspanningCircuit (range (J true))
  · right; right
    have hch : N.IsCircuitHyperplane (range (J true)) :=
      ⟨hCN.isCircuit, hJN.isHyperplane_rim_of_isCircuit_rim hNE hCN.isCircuit⟩
    refine ⟨hch, ext_isNonspanningCircuit (by simp [← hME, ← hNE]) (by simp [hMr, hNr])
      fun C hCE ↦ ?_⟩
    rw [relax_isNonspanningCircuit_iff, mem_singleton_iff]
    obtain rfl | hne := eq_or_ne C (range (J true))
    · grind
    rw [and_iff_left hne, hJM.isNonspanningCircuit_iff_isNonspanningCircuit hM hN hJN hne]
  left
  refine ext_isNonspanningCircuit (by rwa [← hME]) (by rwa [hNr]) fun C hC ↦ ?_
  obtain rfl | hne := eq_or_ne C (range (J true))
  · grind
  rw [hJM.isNonspanningCircuit_iff_isNonspanningCircuit hM hN hJN hne]
