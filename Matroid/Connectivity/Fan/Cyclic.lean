import Matroid.Connectivity.Fan.Circuit
import Mathlib.Data.ZMod.Basic

open Set Function


namespace Matroid
set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

structure IsCyclicFan (M : Matroid α) (n : ℕ) (J : Bool → ZMod n → α) : Prop where
  isTriangle_bDual : ∀ b i, (M.bDual b).IsTriangle {J b i, J b (i + 1), J (!b) (i + b.toNat)}
  inj : ∀ b b' i i', J b i = J b' i' → i = i' ∧ b = b'

lemma IsCyclicFan.injective {J} (h : M.IsCyclicFan n J) {b : Bool} :
    Function.Injective (J b) :=
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
  simpa using h.subset_ground

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
  simp [hK.2, union_comm, hK.1]

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

lemma IsCyclicFan.range_true_subset_closure {J} (h : M.IsCyclicFan n J) :
    range (J true) ⊆ M.closure (range (J false)) := by
  rintro _ ⟨i, hi, rfl⟩
  exact mem_of_mem_of_subset (h.isTriangle i).mem_closure₃ <| M.closure_subset_closure (by grind)

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
    h.minor (restrict_isRestriction _ _ h.iUnion_subset_ground).isMinor <| by simp
  obtain ⟨F', hF', hFF'⟩ := h'.exists_isCyclicFan_dual'
  have hr := ((M ↾ (⋃ b, Set.range (J b))).eRank_add_eRank_dual)
  rw [restrict_ground_eq, h'.encard_iUnion_range, eRank_restrict, ← eRk_ground,
    dual_ground, restrict_ground_eq] at hr
  have := hFF' ▸ aux' _ hF'
  enat_to_nat!; lia

/-- A cyclic fan in a connected matroid must be the entire ground set. -/
lemma IsCyclicFan.eq_ground_of_connected [NeZero n] {J} (h : M.IsCyclicFan n J) (hM : M.Connected) :
    ⋃ b, range (J b) = M.E := by
  suffices aux : M.eConn (⋃ b, range (J b)) = 0 by
    exact hM.eq_ground_of_eConn_eq_zero aux (by simp [range_nonempty ..]) h.iUnion_subset_ground
  refine IsRankFinite.eConn_eq_zero_of_eRk_dual_le_dual_restrict_eRank ?_ ?_ h.iUnion_subset_ground
  · exact isRkFinite_of_finite _ <| by simp [finite_range ..]
  obtain ⟨K, hK, hJK⟩ := h.exists_isCyclicFan_dual'
  rw [← hJK, hK.eRk_eq, ← eRk_ground, dual_ground, restrict_ground_eq,
    (hK.minor _ (by simp)).eRk_eq]
  exact (restrict_isRestriction _ _ (by simpa using hK.iUnion_subset_ground)).isMinor.dual

/-- If `F` is a fan on the entire ground set that starts with a joint, then `F` determines
a cyclic fan. We insist that `F` starts with a joint so that the description of the cyclic
fan doesn't involve wrapping indices around. -/
lemma IsFan.isCyclicFan_of_ground_eq (hF : M.IsFan F false c) (hM : M.Simple) (hM' : M✶.Simple)
    (hFE : {e | e ∈ F} = M.E) : ∃ (n : ℕ) (hn : 2 ≤ n) (hnF : 2 * n = F.length), M.IsCyclicFan n <|
    fun d i ↦ F[2 * i.val + d.toNat]'(isCyclicFan_aux_lt hn hnF) := by
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

/-- Any fan on the ground set of a simple, cosimple matroid is a cyclic fan. -/
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

lemma IsCyclicFan.isCircuit (h : M.IsCyclicFan n J) {d : ℕ} (hd : d + 1 < n) (i : ZMod n) :
    M.IsCircuit <| insert (J false i) <| insert (J false (i + d + 1)) <|
      ((fun (x : ℕ) ↦ J true (i + x)) '' Iic d) := by
  have hn : NeZero n := ⟨by lia⟩
  convert (h.isFan_rotate true (i.val - 1)).isCircuit_interval (i := 1) (j := 2 * d + 3)
    (by simp) (by lia) (by grind) rfl (by simp)
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







  -- · simp
  -- · simp
  -- ext j
  -- simp only [zero_add, mem_image, mem_Iic, List.valsBetween, Bool.not_true, Bool.bne_true,
  --   Bool.toNat_true, Nat.div2_succ, Nat.succ_eq_add_one, List.getElem_map, List.getElem_range,
  --   List.length_map, List.length_range, exists_and_left, exists_prop, mem_setOf_eq]
  -- refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  -- · obtain ⟨x, hxd, rfl⟩ := h'
  --   exact ⟨2 * x + 2, by lia, by lia, by simp, by grind, by simp⟩
  -- obtain ⟨i, h1i, hid, hi', hin, rfl⟩ := h'
  -- obtain rfl | rfl | i := i; lia; simp at hi'
  -- exact ⟨i.div2, by grind [i.bodd_add_div2], by simp [show i.bodd = false by simpa using hi']⟩
  -- simp

-- lemma IsCyclicFan.eq_of_isCircuit (h : M.IsCyclicFan n J) {d : ℕ} (hC : M.IsCircuit C)
--     (hCJ : C ⊆ ⋃ b, Set.range (J b)) : C = Set.range (J false) ∨
--     ∃ (i : ZMod n) (d : ℕ), d + 1 < n ∧
--       C = insert (J false i) (insert (J false (i + d + 1)) ({J true (i + x) | x ∈ Iic d})) := by
--   obtain ⟨i₀, hi₀C⟩ | nojoint := exists_or_forall_not (fun i ↦ J false i ∈ C)
--   ·





-- (hd : d + 1 < n) (i : ZMod n) :
--     M.IsCircuit <| insert (J false i) <| insert (J false (i + d + 1)) <|
--       ((fun (x : ℕ) ↦ J true (i + x)) '' Iic d) := by
