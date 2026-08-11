import Matroid.Connectivity.Fan.Basic
import Matroid.Connectivity.Triangle
import Matroid.Connectivity.Separation.Vertical
import Mathlib.Order.Interval.Set.Fin
-- import Matroid.ForMathlib.List.Set


set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j p q r : ℕ} {F J : List α} {b c : Bool}



open Set List

lemma Icc_zero_left {α : Type*} [Preorder α] [Bot α] [Zero α] [IsBotZeroClass α] (a : α) :
    Icc 0 a = Iic a := by
  simp [Icc, Iic]

lemma Ico_zero_left {α : Type*} [Preorder α] [Bot α] [Zero α] [IsBotZeroClass α] (a : α) :
    Ico 0 a = Iio a := by
  simp [Ico, Iio]

lemma Fin.reverse_getElem {α : Type*} {L : List α} {i : Fin L.reverse.length} :
    L.reverse[i] = L[(i.rev.cast (by simp) : Fin L.length)] := by
  simp [Nat.sub_sub, add_comm 1]

lemma Fin.getElem_rev {α : Type*} {L : List α} {i : Fin L.length} :
    L[i.rev] = L.reverse[(i.cast (by simp) : Fin L.reverse.length)] := by
  rw! [Fin.reverse_getElem]
  simp

lemma List.Nodup.injective_getElem_fin {α : Type*} {L : List α} (hL : L.Nodup) :
    Function.Injective fun (i : Fin L.length) ↦ L[i.1] :=
  hL.injective_get

lemma image_getElem_preimage_val_insert {α : Type*} {L : List α} (s : Set ℕ) {i : ℕ}
    (hi : i < L.length) : (fun x : Fin L.length ↦ L[x.1]'x.2) '' (Fin.val ⁻¹' (insert i s)) =
      insert L[i] ((fun x : Fin L.length ↦ L[x.1]'x.2) '' (Fin.val ⁻¹' s)) := by
  rw [← singleton_union, preimage_union, image_union, show Fin.val ⁻¹' {i} = {⟨i, hi⟩} by
    grind, image_singleton, singleton_union]

lemma image_getElem_preimage_val_singleton {α : Type*} {L : List α} {i : ℕ}
    (hi : i < L.length) : (fun x : Fin L.length ↦ L[x.1]'x.2) '' (Fin.val ⁻¹' {i}) = {L[i]} := by
  rw [← insert_empty_eq, image_getElem_preimage_val_insert _ hi]
  simp

lemma Fin.range_val_eq_Iic (n : ℕ) [NeZero n] : range (Fin.val (n := n)) = Iic (n - 1) := by
  obtain rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  rw [Fin.range_val, Nat.add_sub_cancel]
  simp [Iio, Iic]

lemma Fin.eq_rev_iff {n : ℕ} (a b : Fin n) : a = rev b ↔ a.1 + b.1 + 1 = n := by
  rw [← Fin.val_inj, Fin.val_rev]
  lia

lemma Fin.rev_add_self {n : ℕ} [NeZero n] (a : Fin n) : a.rev + a = ⊤ := by
  rw [← Fin.val_inj, Fin.val_add_eq_ite, if_neg]
  · simp only [val_rev, val_top]
    lia
  simp only [val_rev, not_le]
  lia

lemma Fin.neg_one {n : ℕ} [NeZero n] : (-1 : Fin n) = ⊤ := by
  obtain rfl | rfl | n := n
  · grind
  · grind
  simp [← Fin.val_inj, val_top, val_neg]

lemma Fin.rev_eq_neg {n : ℕ} [NeZero n] (a : Fin n) : a.rev = - 1 - a := by
  rw [← add_left_inj a, sub_add_cancel, Fin.rev_add_self, Fin.neg_one]

lemma Fin.neg_eq_rev_add_one {n : ℕ} [NeZero n] (a : Fin n) : - a = a.rev + 1 := by
  simp only [rev_eq_neg]
  grind

lemma Fin.add_eq_top_iff {n} [NeZero n] {a b : Fin n} : a + b = ⊤ ↔ a = rev b := by
  rw [Fin.rev_eq_neg, eq_sub_iff_add_eq, Fin.neg_one]

@[simp]
lemma Fin.one_ne_zero {n : ℕ} [hn : Fact (1 < n)] : (1 : Fin n) ≠ 0 := by
  simp [hn.1.ne']

@[simp]
lemma Fin.zero_ne_one'' {n : ℕ} [hn : Fact (1 < n)] : 0 ≠ (1 : Fin n) := by
  simp [hn.1.ne']

@[simp]
lemma Fin.zero_ne_top {n : ℕ} [hn : Fact (1 < n)] : 0 ≠ (⊤ : Fin n) := by
  simp [hn.1.ne']

@[simp]
lemma Fin.top_ne_zero {n : ℕ} [hn : Fact (1 < n)] : (⊤ : Fin n) ≠ 0 := by
  simp [hn.1.ne']

lemma Fin.one_ne_top {n : ℕ} [NeZero n] (hn : 2 < n) : (1 : Fin n) ≠ ⊤ := by
  rw [Ne, ← Fin.val_inj, val_top, coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by lia)]
  lia

lemma Fin.ofNat_ne_top {n k : ℕ} [NeZero n] [k.AtLeastTwo] (hn : k + 1 < n) :
    (ofNat(k) : Fin n) ≠ ⊤ := by
  rw [Ne, ← Fin.val_inj, coe_ofNat_eq_mod, val_top, Nat.mod_eq_of_lt (by grind)]
  change ¬ (k = n - 1)
  lia

lemma Fin.ofNat_add' {n k l : ℕ} [NeZero n] :
    (ofNat(k) : Fin n) + ofNat(l) = ofNat(k + l) := by
  rw [← Fin.val_inj, Fin.val_add, Fin.coe_ofNat_eq_mod, Fin.coe_ofNat_eq_mod, Fin.coe_ofNat_eq_mod]
  change (k % n + l % n) % n = (k + l) % n
  simp

@[simp]
lemma Fin.one_add_one {n : ℕ} [NeZero n] : (1 : Fin n) + 1 = 2 := by
  exact ofNat_add'

@[simp]
lemma Fin.cast_eq_top_iff {m n : ℕ} [NeZero n] [NeZero m] {hmn : m = n} (i : Fin m) :
    (i.cast hmn) = ⊤ ↔ i = ⊤ := by
  simp [← Fin.val_inj, hmn]

@[simp]
lemma Fin.rev_eq_top_iff {n : ℕ} [NeZero n] (i : Fin n) :
    i.rev = ⊤ ↔ i = 0 := by
  rw [← Fin.val_inj, ← Fin.val_inj, val_rev, val_top, val_zero]
  lia

@[simp]
lemma Fin.rev_eq_zero_iff {n : ℕ} [NeZero n] (i : Fin n) :
    i.rev = 0 ↔ i = ⊤ := by
  rw [← Fin.rev_eq_top_iff, rev_rev]

lemma Fin.cast_add_one {m n : ℕ} [NeZero n] [NeZero m] {hmn : m = n} (i : Fin m) :
    (i + 1).cast hmn = i.cast hmn + 1 := by
  subst hmn
  rfl

lemma Fin.cast_add_ofNat {m n k : ℕ} [NeZero n] [NeZero m] [k.AtLeastTwo] {hmn : m = n}
    (i : Fin m) :
    (i + ofNat(k)).cast hmn = i.cast hmn + ofNat(k) := by
  subst hmn
  rfl

lemma Fin.cast_sub_ofNat {m n k : ℕ} [NeZero n] [NeZero m] [k.AtLeastTwo] {hmn : m = n}
    (i : Fin m) :
    (i - ofNat(k)).cast hmn = i.cast hmn - ofNat(k) := by
  subst hmn
  rfl

lemma Fin.cast_sub_one {m n k : ℕ} [NeZero n] [NeZero m] [k.AtLeastTwo] {hmn : m = n}
    (i : Fin m) :
    (i - 1).cast hmn = i.cast hmn - 1 := by
  subst hmn
  rfl

-- lemma Fin.cast_add_one {m n : ℕ} [NeZero n] [NeZero m] {hmn : m = n} (i : Fin m) :
--     i.cast hmn + 1 = (i + 1).cast hmn := by
--   subst hmn
--   rfl

lemma Fin.top_eq_neg_one {n : ℕ} [NeZero n] : (⊤ : Fin n) = - 1 := by
  obtain rfl | rfl | n := n <;> simp [← Fin.val_inj, Fin.val_neg]

lemma Fin.top_add {n : ℕ} [NeZero n] (a : Fin n) : (⊤ : Fin n) + a = a - 1 := by
  rw [add_comm, Fin.top_eq_neg_one, sub_eq_add_neg]

@[simp]
lemma Fin.top_add_one {n : ℕ} [NeZero n] : (⊤ : Fin n) + 1 = 0 := by
  simp [Fin.top_add]

lemma Fin.add_top {n : ℕ} [NeZero n] (a : Fin n) : a + ⊤ = a - 1 := by
  rw [Fin.top_eq_neg_one, sub_eq_add_neg]

lemma Fin.le_add_right_iff {n : ℕ} (i k : Fin n) : i ≤ i + k ↔ i.val + k.val < n := by
  rw [Fin.le_def, Fin.val_add_eq_ite]
  split_ifs <;> grind

lemma Fin.bodd_val_sub_one {n} [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    (i - 1).1.bodd = !i.1.bodd := by
  rw [Fin.val_sub_one_of_ne_zero hi, Nat.bodd_sub (by grind)]
  simp only [Nat.bodd_succ, Nat.bodd_zero, Bool.not_false, Bool.bne_true]

lemma Fin.bodd_val_add_one {n} [NeZero n] {i : Fin n} (hi : i ≠ ⊤) :
    (i + 1).1.bodd = !i.1.bodd := by
  rw [Fin.val_add_one_of_lt' (by grind), Nat.bodd_succ]

lemma Fin.bodd_val_top {n} [NeZero n] : (⊤ : Fin n).1.bodd = !n.bodd := by
  have := NeZero.ne n
  simp [Nat.bodd_sub (show 1 ≤ n by lia)]

lemma Fin.val_add_one_of_ne_top {n} [NeZero n] {a : Fin n} (ha : a ≠ ⊤) :
    (a + 1).val = a.val + 1 := by
  obtain rfl | rfl | n := n
  · grind
  · grind
  rw [← lt_top_iff_ne_top, Fin.lt_def, Fin.val_top] at ha
  rw [Fin.val_add_eq_of_add_lt (by simp [show a.1 ≤ n by lia])]
  simp

lemma Fin.val_add_two_of_ne {n} [NeZero n] {a : Fin n} (ha : a ≠ ⊤) (ha' : a ≠ Fin.rev 1) :
    (a + 2).val = a.val + 2 := by
  rw [show a + 2 = (a + 1 + 1) by simp [add_assoc], val_add_one_of_ne_top
    (by simpa [add_eq_top_iff]), val_add_one_of_ne_top ha]

lemma Fin.val_sub_two_of_ne {n} [NeZero n] {a : Fin n} (ha : a ≠ 0) (ha' : a ≠ 1) :
    (a - 2).val = a.val - 2 := by
  rw [show a - 2 = a - 1 - 1 by simp [sub_sub], val_sub_one_of_ne_zero (by simpa [sub_eq_zero]),
    val_sub_one_of_ne_zero ha]
  lia

lemma Fin.lt_iff_le_sub_one {n : ℕ} [NeZero n] {a b : Fin n} (hb : b ≠ 0) :
    a < b ↔ a ≤ b - 1 := by
  obtain rfl | rfl | n := n
  · grind
  · grind [cases Fin]
  rw [lt_def, le_def, Fin.sub_val_of_le (Fin.one_le_of_ne_zero hb), Fin.val_one',
    Nat.mod_eq_of_lt (by lia)]
  lia

lemma Fin.add_one_le_of_lt' {n : ℕ} [NeZero n] {a b : Fin n} (hab : a < b) : a + 1 ≤ b := by
  obtain rfl | n := n
  · grind
  exact add_one_le_of_lt hab

lemma Fin.lt_iff_add_one_le {n : ℕ} [NeZero n] {a b : Fin n} (ha : a ≠ ⊤) :
    a < b ↔ a + 1 ≤ b := by
  obtain rfl | rfl | n := n
  · grind
  · grind [cases Fin]
  rw [lt_def, le_def, Fin.val_add_one_of_lt' (by grind)]
  lia

lemma Fin.lt_add_one_iff_le {n : ℕ} [NeZero n] {a b : Fin n} (hb : b ≠ ⊤) : a < b + 1 ↔ a ≤ b := by
  rw [Fin.lt_iff_le_sub_one, add_sub_cancel_right]
  simpa [add_eq_zero_iff_eq_neg, neg_eq_rev_add_one, rev_add_self]

@[simp]
lemma Fin.le_add_one_self_iff {n : ℕ} {b : Fin (n + 2)} : b ≤ b + 1 ↔ b ≠ ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  simpa [Fin.le_def, Fin.val_add_one_of_ne_top hb]

@[simp]
lemma Fin.le_add_one_self_iff' {n : ℕ} [Fact (1 < n)] {b : Fin n} : b ≤ b + 1 ↔ b ≠ ⊤ := by
  obtain rfl | rfl | n := n
  · grind
  · grind [Fact.elim]
  simp

lemma Fin.Icc_add_one_right_eq_insert {n : ℕ} [NeZero n] {a b : Fin n} (hab : a ≤ b) (hb : b ≠ ⊤) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  obtain rfl | rfl | n := n
  · grind
  · grind
  rw! [Icc, ofPred_and, Icc, ofPred_and, ← inter_insert_of_mem]
  · convert rfl
    ext i
    simp only [Set.mem_insert_iff, mem_ofPred_eq, le_iff_lt_or_eq (b := b + 1),
      Fin.lt_add_one_iff_le hb, or_comm]
  exact (hab.trans (by simpa))



namespace Matroid

-- lemma IsFan.mem_iff_mem₁₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i] ∉ C) : F[i + 1] ∈ C ↔ F[i + 2] ∈ C := by
--   rw [(hF.isTriangle_getElem _ hi).mem_iff_mem_of_isCircuit_bDual _ heC]
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma IsFan.mem_iff_mem₀₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 1] ∉ C) : F[i] ∈ C ↔ F[i + 2] ∈ C := by
--   refine (hF.isTriangle_getElem i hi).swap_left.mem_iff_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma IsFan.mem_iff_mem₀₁ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 2] ∉ C) : F[i] ∈ C ↔ F[i + 1] ∈ C := by
--   rw [(hF.isTriangle_getElem i hi).reverse.mem_iff_mem_of_isCircuit_bDual ?_ heC]
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma IsFan.mem_or_mem₀₁ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 2] ∈ C) : F[i] ∈ C ∨ F[i + 1] ∈ C := by
--   refine (hF.isTriangle_getElem i hi).reverse.swap_right.mem_or_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma IsFan.mem_or_mem₀₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 1] ∈ C) : F[i] ∈ C ∨ F[i + 2] ∈ C := by
--   refine (hF.isTriangle_getElem i hi).swap_left.mem_or_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma IsFan.mem_or_mem₁₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i] ∈ C) : F[i + 1] ∈ C ∨ F[i + 2] ∈ C := by
--   refine (hF.isTriangle_getElem i hi).mem_or_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC
lemma IsFan.isTriangle_get [NeZero F.length] (hF : M.IsFan F b c) (i : Fin F.length)
    (hi : i.val + 2 < F.length) :
    (M.bDual (b != i.1.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  have := hF.isTriangle_getElem i hi
  rw! [Fin.getElem_fin, Fin.getElem_fin, Fin.getElem_fin, Fin.val_add_eq_of_add_lt,
    Fin.val_add_eq_of_add_lt (b := 2), hF.val_one, hF.val_two (by lia)]
  · assumption
  · rwa [hF.val_two (by lia)]
  grw [← hi, hF.val_one]
  lia

lemma IsFan.isTriangle_get' [NeZero F.length] (hF : M.IsFan F b c) (i : Fin F.length)
    (hitop : i ≠ ⊤) (hi' : i + 1 ≠ ⊤) :
    (M.bDual (b != i.1.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  refine hF.isTriangle_get i ?_
  simp only [Ne, ← Fin.val_inj, Fin.val_top] at hi' hitop
  rw [Fin.val_add_eq_of_add_lt, hF.val_one] at hi'
  · grind
  grind [hF.val_one]

lemma IsFan.isTriangle_get_sub_add [NeZero F.length] (hF : M.IsFan F b c) (i : Fin F.length)
    (hi0 : i ≠ 0) (hitop : i ≠ ⊤) :
    (M.bDual (b == i.1.bodd)).IsTriangle {F[i - 1], F[i], F[i + 1]} := by
  simpa [ne_eq, sub_eq_iff_eq_add, Fin.top_add, hi0, hitop, show i - 1 + 2 = i + 1 by grind,
    Fin.bodd_val_sub_one hi0] using hF.isTriangle_get' (i - 1)

lemma IsFan.image_getElem_Icc_subset_closure (hF : M.IsFan F b c) {p q : ℕ}
    (hp : p.bodd = b) (hq : q.bodd = b) : (fun x ↦ F[x.1]) '' (Fin.val ⁻¹' (Icc p q)) ⊆
      M.closure ((fun x ↦ F[x.1]) '' Fin.val ⁻¹' ((Icc p q) ∩ Nat.bodd ⁻¹' {b})) := by
  have := hF.neZero
  wlog hq : q + 1 ≤ F.length generalizing q with aux
  · rw [inter_comm, ← preimage_inter_range, Fin.range_val_eq_Iic, ← Icc_zero_left,
      Icc_inter_Icc, max_eq_left zero_le, min_eq_right (by lia)]
  rintro _ ⟨⟨i, hi⟩, ⟨hpi : p ≤ i, hiq : i ≤ q⟩, rfl⟩
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  · exact M.mem_closure_of_mem' (mem_image_of_mem _ (by simp [hpi, hiq])) hF.getElem_mem_ground
  obtain rfl | i := i
  · grind





    -- simp [hpi, hiq.    ]

    -- exact mem_closure_of_mem' _ (mem_image_of_mem _ ⟨⟨hpi, hiq⟩, rfl⟩) <| hF.get_mem_ground i


  -- have hi0 : i ≠ 0 := by grind
  -- have hitop : i ≠ ⊤ := by
  --   rintro rfl
  --   simp at hiq
  --   _



lemma IsFan.getElems_Icc_subset_closure (hF : M.IsFan F b c) {p q : Fin F.length}
    (hp : p.1.bodd = b) (hq : q.1.bodd = b) :
    (fun x ↦ F[x]) '' (Icc p q) ⊆ M.closure ((fun x ↦ F[x]) '' {i ∈ Icc p q | i.1.bodd = b}) := by
  have := hF.neZero
  rintro _ ⟨i, hi, rfl⟩
  obtain rfl | rfl := b.eq_or_eq_not i.1.bodd
  · exact mem_closure_of_mem' _ (mem_image_of_mem _ ⟨hi, rfl⟩) <| hF.get_mem_ground i
  have hi0 : i ≠ 0 := by grind
  have hitop : i ≠ ⊤ := by grind
  have hT : M.IsTriangle {F[(i - 1)], F[i], F[(i + 1)]} := by
    simpa using hF.isTriangle_get_sub_add i hi0 hitop
  refine mem_of_mem_of_subset hT.mem_closure₂ <| M.closure_subset_closure <| pair_subset
    (mem_image_of_mem _ ⟨⟨?_, le_trans ?_ hi.2⟩, Fin.bodd_val_sub_one hi0⟩) <|
    mem_image_of_mem _ ⟨⟨hi.1.trans ?_, ?_⟩, Fin.bodd_val_add_one hitop⟩
  · rw [← Fin.lt_iff_le_sub_one (by grind), lt_iff_le_and_ne, and_iff_right hi.1]
    grind
  · simp [show 1 ≤ i from Fin.one_le_of_ne_zero (by grind)]
  · rw [Fin.le_add_right_iff, hF.val_one]
    grind
  rw [← Fin.lt_iff_add_one_le hitop, lt_iff_le_and_ne, and_iff_right hi.2]
  grind

/-- Under an appropriate nondegeneracy assumption, any interval of joints or cojoints
is independent. -/
lemma IsFan.joints_Icc_indep (hF : M.IsFan F b c) {p q : ℕ}
    (hpq : p = 0 → F.length ≤ q + 1 → b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep ((fun x ↦ F[x.1]) '' Fin.val ⁻¹' (Icc p q ∩ Nat.bodd ⁻¹' {b})) := by
  have := hF.neZero
  rw [indep_iff_forall_subset_not_isCircuit (by grind)]
  simp only [subset_image_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro C hCodd hC
  by_cases hss : C ⊆ {0, ⊤}
  · obtain rfl : C = {0, ⊤} := by
      rw [← hF.nodup.injective_getElem_fin.image_injective.eq_iff,
        hC.dep.eq_of_subset_pair (by grw [hss, image_pair])
        (hF.isNonloop_getElem_fin (i := 0)) (hF.isNonloop_getElem_fin (i := ⊤)),
        image_pair]
    obtain ⟨⟨rfl, rfl⟩, hq, rfl⟩ : (p = 0 ∧ b = false) ∧ F.length ≤ q + 1 ∧ c = false := by
      simp only [preimage_inter, subset_inter_iff, pair_subset_iff, mem_preimage,
        Fin.coe_ofNat_eq_mod, Nat.zero_mod, mem_Icc, nonpos_iff_eq_zero, zero_le, and_true,
        Fin.val_top, tsub_le_iff_right, Nat.bodd_zero, mem_singleton_iff, Bool.false_eq,
        hF.length_sub_one_bodd_eq] at hCodd
      grind
    rw [image_pair, ← parallel_iff_isCircuit (by simp [hF.getElem_zero_ne_last])] at hC
    exact hpq rfl hq rfl rfl <| by simpa using hC
  obtain ⟨x, hxC, hne⟩ := not_subset.1 hss
  have hT := (hF.isTriangle_get_sub_add x (by grind) (by grind)).swap_left
  obtain h := hT.mem_or_mem_of_isCircuit_bDual (K := F.get '' C)
    (by simpa [show x.1.bodd = b from (hCodd hxC).2]) (mem_image_of_mem _ hxC)
  simp_rw [Fin.getElem_fin, ← get_eq_getElem, hF.nodup.injective_get.mem_set_image] at h
  have hxb : x.1.bodd = b := by grind
  obtain h | h := h
  · simpa [Fin.bodd_val_sub_one (show x ≠ 0 by grind), hxb] using hCodd h
  simpa [Fin.bodd_val_add_one (show x ≠ ⊤ by grind), hxb] using hCodd h

/-- Under an appropriate nondegeneracy assumption, any interval of joints or cojoints
is independent. -/
lemma IsFan.joints_Icc_fin_indep [NeZero F.length] (hF : M.IsFan F b c) {p q : Fin F.length}
    (hpq : p = 0 → q = ⊤ → b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep ((fun x ↦ F[x]) '' {x ∈ Icc p q | x.1.bodd = b}) := by
  convert hF.joints_Icc_indep (p := p) (q := q) ?_ using 2
  · simp
  · rw [preimage_inter, ofPred_and, ofPred_mem_eq, ← Fin.image_val_Icc,
      preimage_image_eq _ Fin.val_injective, preimage_preimage]
    simp [preimage]
  convert hpq
  · simp
  simp only [← Fin.val_inj, Fin.val_top]
  grind

/-- The joints are always independent, unless the first and last element are parallel joints. -/
lemma IsFan.joints_indep (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep ((fun x ↦ F[x.1]) '' Fin.val ⁻¹' (Nat.bodd ⁻¹' {b})) := by
  have hnz := hF.neZero
  have hwin := hF.joints_Icc_indep (p := 0) (q := F.length - 1) (by grind)
  simp_rw [Icc_zero_left, ← Fin.range_val_eq_Iic, inter_comm, preimage_inter_range] at hwin
  assumption

lemma IsFan.eRk_ge (hF : M.IsFan F b c) :
    F.length ≤ 2 * M.eRk ({e | e ∈ F}) + F.length.bodd.toNat := by
  wlog hbc : b = false → c = false generalizing F b c with aux
  · simpa using aux hF.reverse (by grind)
  obtain h2 | h3 := hF.two_le_length.eq_or_lt
  · grw [← eRk_subset_le (X := {F[0]}) _ (by simp), (hF.isNonloop (by simp)).eRk_eq]
    simp [h2.symm]
  obtain rfl | rfl := b
  · grw [← eRk_subset_le (X := (fun x ↦ F.tail[x.1]) '' (Fin.val ⁻¹' Nat.bodd ⁻¹' {!false}))
      _ (by simp), ((hF.tail (by lia)).joints_indep (by simp)).eRk_eq_encard, hF.length_bodd_eq,
      hF.nodup.tail.injective_getElem_fin.encard_image]
    simpa [preimage, hF.length_sub_one_bodd_eq, hbc rfl]
      using (Fin.encard_setOf_bodd F.tail.length true).ge
  grw [← eRk_subset_le (X := (fun i ↦ F[i.1]) '' Fin.val ⁻¹' Nat.bodd ⁻¹' {true}) _ (by simp),
    (hF.joints_indep (by simp)).eRk_eq_encard, hF.nodup.injective_getElem_fin.encard_image]
  cases c with simpa [preimage,hF.length_bodd_eq] using (Fin.encard_setOf_bodd F.length true).ge

lemma IsFan.eRk_eq (hF : M.IsFan F b b) (hpara : ¬ (M.bDual b).Parallel F[0] (F[F.length - 1])) :
    2 * (M.bDual b).eRk {e | e ∈ F} = F.length + 1 := by
  obtain h2 | h3 := hF.two_le_length.eq_or_lt
  · have hcon := h2 ▸ hF.bool_right_eq
    simp at hcon
  refine le_antisymm (by simpa using (hF.bDual b).eRk_le (by lia)) ?_
  grw [← ((hF.bDual b).joints_indep (by simpa)).encard_le_eRk_of_subset (by simp),
    hF.nodup.injective_getElem_fin.encard_image]
  simpa [hF.length_bodd_eq, preimage] using (Fin.encard_setOf_bodd F.length (b != b)).ge

/- Contractions preserve the property of being a fan, unless one of the ends is a joint
spanned by the contract-set. -/
lemma IsFan.contract (hF : M.IsFan F b c) (X : Set α) (hX : _root_.Disjoint {e | e ∈ F} X)
    (h0 : b = false → F[0] ∉ M.closure X) (hlast : c = false → F[F.length - 1] ∉ M.closure X)
    (h2 : F.length = 2 → F[(!b).toNat] ∉ M.closure X := by lia)
    (h3 : F.length = 3 → b = false → c = false → M.Skew {e | e ∈ F} (X ∩ M.E) := by lia) :
    (M ／ X).IsFan F b c := by
  refine isFan_of_eq_of_forall_triangle hF.two_le_length hF.nodup (by simp [hF.length_bodd_eq])
    ?_ fun i hi ↦ ?_
  · rintro hF2 (rfl | rfl) i hi
    · obtain rfl | rfl := b
      · obtain rfl | rfl : i = 0 ∨ i = 1 := by grind
        · simp [h0, hF.getElem_mem_ground]
        simpa [hF.getElem_mem_ground] using h2 hF2
      obtain rfl | rfl : i = 0 ∨ i = 1 := by grind
      · simpa [hF.getElem_mem_ground] using h2 hF2
      have h1cl : F[1] ∉ M.closure X := by simpa [hF.bool_right_eq, hF2] using hlast
      simpa [hF.getElem_mem_ground]
    simpa [hX.notMem_of_mem_left] using hF.isNonloop_bDual (e := F[i]) (by simp) true
  obtain rfl | hb := b.eq_or_eq_not !i.bodd
  · simpa [hX.notMem_of_mem_left] using hF.isTriangle_getElem i (by lia)
  suffices hsk : M.Skew {F[i], F[i + 1], F[i + 2]} (X ∩ M.E) by
    simpa [hb] using (hF.isTriangle_getElem_of_eq i (by lia) (by simp [hb])).contract_isTriangle
      hsk.symm
  clear h2
  wlog h1 : i + 3 ≠ F.length generalizing i F b c with aux
  · replace h1 : i + 3 = F.length := by simpa using h1
    obtain rfl | i := i
    · exact (h3 (by simp [← h1]) (by simp [hb])
        (by simp [hF.bool_right_eq, hb, ← h1])).mono_left <| by simp [insert_subset_iff]
    specialize aux hF.reverse (by simpa) (by simpa) (by simpa)
      (fun h hc hb ↦ by simpa using h3 (by simpa using h) hb hc) 0 (by grind)
      (by simp [hF.bool_right_eq, hb, ← h1]) (by grind)
    rw [pair_comm, insert_comm, pair_comm]
    cases b with simpa [hF.bool_right_eq, ← h1] using aux
  by_contra hnsk
  have hT := hF.isTriangle_getElem_of_eq i (by lia) (by simp [hb])
  obtain ⟨C, hC, hCss, hiC, hne⟩ := hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew
    (e := F[i]) (hX.mono (by simp [insert_subset_iff]) inter_subset_left) hnsk (by simp)
  have hi2C : F[i + 3] ∉ C :=
    fun h ↦ by simpa [hX.notMem_of_mem_left, hF.nodup.getElem_inj_iff, add_assoc] using hCss h
  have hT' := hF.isTriad_getElem_of_eq (i + 1) (by lia) (by simp [hb])
  obtain ⟨hi2, hi1⟩ | ⟨hi2, hi1⟩ := iff_iff_and_or_not_and_not.1
    <| hT'.reverse.mem_iff_mem_of_isCircuit hC (by simpa)
  · obtain rfl := hT.isCircuit.eq_of_subset_isCircuit hC
      (by simp [insert_subset_iff, hiC, hi1, hi2])
    exact hne.ne_empty <| (hX.mono (by simp [insert_subset_iff]) inter_subset_left).inter_eq
  obtain rfl | i := i
  · grw [insert_comm, insert_union, subset_insert_iff_of_notMem hi1, pair_comm,
      insert_union, subset_insert_iff_of_notMem hi2, ← sdiff_subset_iff, inter_subset_left] at hCss
    exact h0 (by simpa) <| mem_of_mem_of_subset (hC.mem_closure_sdiff_singleton_of_mem hiC) <|
      M.closure_subset_closure hCss
  rw [(hF.isTriad_getElem_of_eq i (by lia) (by simp [hb])).reverse.mem_iff_mem_of_isCircuit hC hi1]
    at hiC
  simpa [hX.notMem_of_mem_left, hF.nodup.getElem_inj_iff, add_assoc] using hCss hiC

lemma IsFan.contract_head (hF : M.IsFan F b c) (hF3 : 3 ≤ F.length)
    (h_init : b = true → ¬ M.Parallel F[0] F[1])
    (h_false : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1])
    (h4 : ∀ (hF : F.length = 4), b = true → ¬ F[0] ∈ M.closure {F[1], F[2]} := by lia)
    (h3 : ∀ (hF : F.length = 3), b = true → ¬ M.Parallel F[0] F[2] := by lia) :
    (M ／ {F[0]}).IsFan F.tail (!b) c := by
  have aux := @IsFan.contract _ M F.tail _ _ (hF.tail hF3) {F[0]}
    (by simp [getElem_zero_eq_head, hF.nodup.head_notMem_tail])
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, getElem_tail, zero_add, getElem_mem,
    ← IsNonloop.parallel_iff_mem_closure (hF.isNonloop _), parallel_comm (f := F[0]), length_tail,
    show F.length - 1 - 1 + 1 = F.length - 1 by lia, Nat.pred_eq_succ_iff, Nat.reduceAdd,
    Bool.not_not, singleton_inter_of_mem hF.getElem_mem_ground] at aux
  refine aux h_init ?_ ?_ ?_
  · rintro rfl hpara
    obtain rfl | rfl := b
    · exact h_false rfl rfl hpara
    have hwin := (hF.isTriangle_getElem 0 (by lia)).isCircuit.mem_iff_mem_of_parallel_bDual hpara
    obtain h3' : F.length = 3 := by simpa
      [hF.nodup.getElem_inj_iff, show F.length - 1 ≠ 0 by lia, show F.length ≠ 2 by lia] using hwin
    exact h3 h3' rfl <| by simpa [h3'] using hpara
  · obtain rfl | rfl := b
    · exact fun h3 hpara ↦ by simpa [hF.nodup.getElem_inj_iff] using
        (hF.isTriangle_getElem 0 (by lia)).notMem_of_mem_of_parallel hpara
    simpa using h3
  rintro hF4 rfl rfl
  rw! [(hF.isNonloop (by simp)).skew_right_iff (hF.tail hF3).subset_ground,
    (eq_of_length_eq_three (l := F.tail)) (by grind), getElem_tail, getElem_tail, getElem_tail]
  refine notMem_subset ?_ (h4 hF4 rfl)
  suffices M.closure {F[3], F[2], F[1]} ⊆ M.closure {F[1], F[2]} by simpa [ofPred_or]
  rw [pair_comm, closure_insert_eq_of_mem_closure]
  exact (hF.isTriangle_getElem_of_eq 1 (by lia) rfl).mem_closure₃

lemma IsFan.delete_head (hF : M.IsFan F b c) (h5 : 5 ≤ F.length)
    (h_init : b = false → ¬ M✶.Parallel F[0] F[1])
    (h_pair : b = true → c = true → ¬ M✶.Parallel F[0] F[F.length - 1]) :
    (M ＼ {F[0]}).IsFan F.tail (!b) c := by
  simpa using (hF.dual.contract_head (by lia) (by simpa) (by simpa)).dual

lemma IsFan.remove_head (hF : M.IsFan F b c) (h5 : 5 ≤ F.length) {d : Bool}
    (h_init : b = d → ¬ (M.bDual !d).Parallel F[0] F[1])
    (h_pair : b = !d → c = !d → ¬ (M.bDual !d).Parallel F[0] F[F.length - 1]) :
    (M.remove d {F[0]}).IsFan F.tail (!b) c := by
  obtain rfl | rfl := d
  · exact hF.delete_head h5 (by simpa) (by simpa)
  exact hF.contract_head (by lia) (by simpa) (by simpa)

-- /-
-- The nondegeracy hypothesis has some redundancy, since `i = 0` and `q + 1 = F.length` implies that
-- `b = c = false`; we include it so it is easier to discharge quickly in various cases.  -/
-- lemma IsFan.isCircuit_interval' (hF : M.IsFan F b c) (hpq : p < q) (hqF : q < F.length)
--     (hpb : p.bodd = b) (hqb : q.bodd = b)
--     (hdg : b = false → c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F[F.length - 1]) :
--     M.IsCircuit <| insert F[p] (insert F[q] (F.get '' {i | p < i ∧ i < q ∧ i.1.bodd = !b})) := by
--   induction q using Nat.strong_induction_on with | h q ih =>
--   obtain ⟨q, hqlt, rfl, rfl | hlt⟩ : ∃ q' < q, q' + 2 = q ∧ (q' = p ∨ p < q') := by
--     obtain ⟨rfl | rfl | d, rfl⟩ := exists_add_of_le hpq.le
--     · lia
--     · simp [hpb] at hqb
--     exact ⟨p + d, by grind⟩
--   · have hrw {i : Fin F.length} : (q < i ∧ i < q + 2 ∧ i.1.bodd = !b) ↔ i = ⟨q + 1, by lia⟩ := by
--       grind [Nat.bodd_succ]
--     simpa [hrw] using (hF.isTriangle_getElem_of_eq q (by lia) hpb).swap_right.isCircuit
--   simp only [Nat.bodd_succ, Bool.not_not] at hqb
--   specialize ih q hqlt hlt (by lia) hqb (by grind)

--   -- rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia)] at ih ⊢
--   have hT := (hF.isTriangle_getElem_of_eq q (by lia) hqb).swap_right
--   convert hT.union_diff_singleton_isCircuit ih (by simp) ?_ using 1
--   -- convert hT.union_diff_singleton_isCircuit ih (by simp [hF.nodup]) ?_ using 1
--   · rw [insert_comm F[p] F[q], insert_sdiff_self_of_notMem
--       (by simp +contextual [hF.nodup.getElem_inj_iff, hlt.ne', ne_of_lt]),
--       ← insert_comm F[p], ← insert_comm F[p], show F[q + 1] = F.get ⟨q + 1, by lia⟩ by simp,
--       ← image_insert_eq]
--     convert rfl
--     rw [ofPred_and, ← inter_insert_of_mem (by grind), ofPred_and,
--       ← insert_inter_of_notMem (show ⟨q, by lia⟩ ∉ {a : Fin F.length | a.1.bodd = !b} by grind),
--       ← insert_inter_of_mem (by grind [Nat.bodd_succ]), ofPred_and, ofPred_and]
--     convert rfl
--     ext i
--     simp only [mem_ofPred_eq, Set.mem_insert_iff, Nat.lt_add_one_iff, Nat.le_iff_lt_or_eq,
--       ← Fin.val_inj]
--     tauto
--   have := hF.neZero
--   have := hF.joints_Icc_indep (q := q + 3)
--   sorry

  --   simp_rw [insert_comm F[p], ← one_add_one_eq_two, ← add_assoc,
  --     hF.nodup.getElems_ofPred_and, getElems_Ico]
  --   rw [extract_add_one_right _ (by lia) (by lia), extract_add_one_right _ (by lia) (by lia),
  --     insert_sdiff_self_of_notMem (by simp [hF.nodup, hF.nodup.getElem_inj_iff, hlt.ne.symm])]
  --   simp only [append_assoc, cons_append, nil_append, mem_append, mem_cons, ofPred_or,
  --     not_mem_nil, or_false, ofPred_eq_eq_singleton, union_singleton, union_insert]
  --   rw [insert_inter_of_mem (by simpa [hF.nodup]), insert_inter_of_notMem (by simpa [hF.nodup])]
  --   grind
  -- grw [hF.nodup.getElems_ofPred_and, inter_subset_left,
  --   insert_eq_of_mem (by simp [hF.nodup, hlt]), getElems_Ico, ← toSet_concat_eq,
  --   ← extract_add_one_right _ hlt.le, ← getElems_Ico,
  --   hF.getElems_Ico_subset_closure hpb (by simpa) (by lia), M.closure_closure,
  --   (hF.joints_Ico_indep <| by grind).notMem_closure_iff_of_notMem (by simp [hF.nodup])]
  -- exact (hF.joints_Ico_indep (p := p) (q := q + 3) (by grind)).subset
  --   <| insert_subset (by simpa [hF.nodup, hpq.le]) <| getElems_mono _ <| by grind


/-- Let `F[p]` and `F[q]` be joints of a fan, and `K` be the set of cojoints between `p` and `q`.
If `F[p]` and `F[q]` are not parallel and at the beginning and the end of the fan,
then `{F[p], F[q]} ∪ K` is a circuit.

The nondegeracy hypothesis has some redundancy, since `i = 0` and `q + 1 = F.length` implies that
`b = c = false`; we include it so it is easier to discharge quickly in various cases.  -/
lemma IsFan.isCircuit_interval [NeZero F.length] (hF : M.IsFan F b c) {p q : ℕ}
    (hpq : p < q) (hq : q < F.length) (hpb : p.bodd = b) (hqb : q.bodd = b)
    (hdg : b = false → c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.IsCircuit <| (fun x ↦ F[x.1]) '' Fin.val ⁻¹' ({p, q} ∪ (Icc p q ∩ Nat.bodd ⁻¹' {!b})) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq.le
  -- · simp [hpb] at hqb

  rw! [preimage_union, image_union, image_getElem_preimage_val_insert _ (by lia),
    image_getElem_preimage_val_singleton (by lia)]
  induction d using Nat.twoStepInduction with
  | zero => simp at hpq
  | one => simp [hpb] at hqb
  | more d ih _ =>
    replace hqb : d.bodd = false := sorry
    rw! [show p + (d + 2) = (p + d) + 1 + 1 by lia, ← insert_Icc_right_eq_Icc_add_one (by lia),
      insert_inter_of_notMem (by simp [hpb, hqb]), ← insert_Icc_right_eq_Icc_add_one (by lia),
      insert_inter_of_mem (by simp [hpb, hqb]), image_getElem_preimage_val_insert _ (by lia)]
    have hT := (hF.isTriangle_getElem_of_eq (p + d) hq (by simp [hpb, hqb])).swap_right
    obtain rfl | hne := eq_or_ne d 0
    · rw! [add_zero, Icc_self, singleton_inter_of_notMem (by simpa), preimage_empty, image_empty,
        insert_empty_eq, union_singleton]
      simpa using hT.reverse.swap_right.isCircuit


    generalize hC₀ : (fun x : Fin F.length ↦ F[↑x]) '' Fin.val ⁻¹'
      (Icc p (p + d) ∩ Nat.bodd ⁻¹' {!b}) = C₀ at ⊢ ih





    specialize ih (by lia) (by lia) (by simp [hpb, hqb]) (by lia)
    convert hT.union_diff_singleton_isCircuit ih (by simp) ?_
    · rw! [add_assoc, one_add_one_eq_two, pair_comm, insert_union, union_insert, pair_comm,
      insert_union, insert_sdiff_self_of_notMem]
      · rfl
      rw [← Ico_insert_right (by lia), insert_inter_of_notMem (by simp [hpb, hqb])] at hC₀
      simp +contextual [← hC₀, hF.nodup.getElem_inj_iff, hne, ne_of_lt]
    rw [← closure_union_closure_right_eq, ← hC₀,
      ]
    _


  -- induction d using Nat.twoStepInduction with
  -- | zero => simp [hpb] at hqb
  -- | one =>
  --   rw [← insert_Icc_right_eq_Icc_add_one (by lia), insert_inter_of_notMem (by simpa),
  --     ← insert_Icc_right_eq_Icc_add_one (by lia), insert_inter_of_mem (by simpa), Icc_self,
  --     singleton_inter_of_notMem (by simpa), insert_empty_eq, image_getElem_preimage_val_singleton
  --     (by lia), union_singleton, insert_comm]
  --   exact (hF.isTriangle_getElem_of_eq p hq hpb).isCircuit
  -- | more d ih _ =>
  --   replace hqb : d.bodd = true := by cases b with simpa [hpb] using hqb
  --   rw [← insert_Icc_right_eq_Icc_add_one]

  -- induction q using Nat.strong_induction_on with | h q' ih =>

  --   -- (insert p (insert q (Icc p q ∩ {i | i.1.bodd = !b}))) := by
  -- induction hq : q.val using Nat.strong_induction_on generalizing q with | h q' ih =>
  -- have hptop : p ≠ ⊤ := by
  --   rintro rfl
  --   simp at hpq
  -- rw [Fin.lt_iff_add_one_le (by grind)] at hpq
  -- have := hF.fact_one_lt_length


  -- obtain rfl | hlt := hpq.eq_or_lt
  -- · simp [Fin.bodd_val_add_one hptop, hpb] at hqb
  -- replace hlt := Fin.add_one_le_of_lt' hlt
  -- obtain ⟨q, rfl, hpq', hqb, hq1, hq2⟩ : ∃ q', q' + 1 + 1 = q ∧ p ≤ q' ∧
  --     q'.1.bodd = b ∧ q' ≠ ⊤ ∧ q' + 1 ≠ ⊤ := by
  --   refine ⟨q - 2, by grind, ?_, ?_⟩
  --   rw [Fin.le_def] at ⊢ hlt
  --   rw [Fin.val_add]

  --   _
  -- rw [Fin.Icc_add_one_right_eq_insert (hpq'.trans (by simpa)) hq2,
  --   insert_inter_of_notMem (by simpa),
  --   Fin.Icc_add_one_right_eq_insert hpq' hq1, insert_inter_of_mem
  --   (by simpa [Fin.bodd_val_add_one hq1] using hqb)]

  -- -- sorry
  -- -- ·
  -- -- · exact hq1
  -- -- · simpa
  -- -- refine
  -- obtain rfl | hlt' := hlt.eq_or_lt
  -- · rw [Fin.Icc_add_one_right_eq_insert (by simpa) (by simpa using hpq),
  --     insert_inter_of_notMem (by simpa), Fin.Icc_add_one_right_eq_insert rfl.le hptop,
  --     insert_inter_of_mem (by simpa [Fin.bodd_val_add_one hptop]), Icc_self,
  --     singleton_inter_of_notMem (by simpa), insert_empty_eq]
  --   simpa [image_insert_eq, hpb, add_assoc] using
  --     (hF.isTriangle_get' p hptop (by simpa using hpq)).swap_right.isCircuit
  -- obtain ⟨q, rfl, hpq⟩ : ∃ q', q' + 2 = q ∧ p < q' := sorry



    -- simp_rw [Icc, le_iff_lt_or_eq (b := p + 1 + 1)]
    -- rw! [Fin.lt_add_one_iff_le]

  -- rw [Fin.lt_iff_add_one_le] at hlt
  -- specialize ih (q.val - 2) (by lia) (q := q - 2)
  -- sorry
  -- obtain ⟨q, hqlt, rfl, rfl | hlt⟩ : ∃ q' < q, q' + 2 = q ∧ (q' = p ∨ p < q') := by
  --   obtain ⟨rfl | rfl | d, rfl⟩ := exists_add_of_le hpq.le
  --   · lia
  --   · simp [hpb] at hqb
  --   exact ⟨p + d, by grind⟩
  -- · rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia), hF.nodup.getElems_ofPred_and,
  --     getElems_Ico_eq_pair _ _ (by lia), insert_inter_of_notMem (by simpa [hF.nodup]),
  --     singleton_inter_of_mem (by simpa [hF.nodup]), pair_comm]
  --   exact (hF.isTriangle_getElem_of_eq q (by lia) hpb).isCircuit
  -- simp only [Nat.bodd_succ, Bool.not_not] at hqb
  -- specialize ih q hqlt hlt (by lia) hqb (by grind)
  -- rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia)] at ih ⊢
  -- have hT := (hF.isTriangle_getElem_of_eq q (by lia) hqb).swap_right
  -- convert hT.union_diff_singleton_isCircuit ih (by simp [hF.nodup]) ?_ using 1
  -- · simp_rw [insert_comm F[p], ← one_add_one_eq_two, ← add_assoc,
  --     hF.nodup.getElems_ofPred_and, getElems_Ico]
  --   rw [extract_add_one_right _ (by lia) (by lia), extract_add_one_right _ (by lia) (by lia),
  --     insert_sdiff_self_of_notMem (by simp [hF.nodup, hF.nodup.getElem_inj_iff, hlt.ne.symm])]
  --   simp only [append_assoc, cons_append, nil_append, mem_append, mem_cons, ofPred_or,
  --     not_mem_nil, or_false, ofPred_eq_eq_singleton, union_singleton, union_insert]
  --   rw [insert_inter_of_mem (by simpa [hF.nodup]), insert_inter_of_notMem (by simpa [hF.nodup])]
  --   grind
  -- grw [hF.nodup.getElems_ofPred_and, inter_subset_left,
  --   insert_eq_of_mem (by simp [hF.nodup, hlt]), getElems_Ico, ← toSet_concat_eq,
  --   ← extract_add_one_right _ hlt.le, ← getElems_Ico,
  --   hF.getElems_Ico_subset_closure hpb (by simpa) (by lia), M.closure_closure,
  --   (hF.joints_Ico_indep <| by grind).notMem_closure_iff_of_notMem (by simp [hF.nodup])]
  -- exact (hF.joints_Ico_indep (p := p) (q := q + 3) (by grind)).subset
  --   <| insert_subset (by simpa [hF.nodup, hpq.le]) <| getElems_mono _ <| by grind

#exit



/-- Let `F[p]` and `F[q]` be joints of a fan, and `K` be the set of cojoints between `p` and `q`.
If `F[p]` and `F[q]` are not parallel and at the beginning and the end of the fan,
then `{F[p], F[q]} ∪ K` is a circuit.

The nondegeracy hypothesis has some redundancy, since `i = 0` and `q + 1 = F.length` implies that
`b = c = false`; we include it so it is easier to discharge quickly in various cases.  -/
lemma IsFan.isCircuit_interval (hF : M.IsFan F b c) (hpq : p < q) (hqF : q < F.length)
    (hpb : p.bodd = b) (hqb : q.bodd = b)
    (hdg : b = false → c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.IsCircuit <| F.getElems (insert p (insert q {i ∈ Ico p q | i.bodd = !b})) := by
  induction q using Nat.strong_induction_on with | h q ih =>
  obtain ⟨q, hqlt, rfl, rfl | hlt⟩ : ∃ q' < q, q' + 2 = q ∧ (q' = p ∨ p < q') := by
    obtain ⟨rfl | rfl | d, rfl⟩ := exists_add_of_le hpq.le
    · lia
    · simp [hpb] at hqb
    exact ⟨p + d, by grind⟩
  · rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia), hF.nodup.getElems_ofPred_and,
      getElems_Ico_eq_pair _ _ (by lia), insert_inter_of_notMem (by simpa [hF.nodup]),
      singleton_inter_of_mem (by simpa [hF.nodup]), pair_comm]
    exact (hF.isTriangle_getElem_of_eq q (by lia) hpb).isCircuit
  simp only [Nat.bodd_succ, Bool.not_not] at hqb
  specialize ih q hqlt hlt (by lia) hqb (by grind)
  rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia)] at ih ⊢
  have hT := (hF.isTriangle_getElem_of_eq q (by lia) hqb).swap_right
  convert hT.union_diff_singleton_isCircuit ih (by simp [hF.nodup]) ?_ using 1
  · simp_rw [insert_comm F[p], ← one_add_one_eq_two, ← add_assoc,
      hF.nodup.getElems_ofPred_and, getElems_Ico]
    rw [extract_add_one_right _ (by lia) (by lia), extract_add_one_right _ (by lia) (by lia),
      insert_sdiff_self_of_notMem (by simp [hF.nodup, hF.nodup.getElem_inj_iff, hlt.ne.symm])]
    simp only [append_assoc, cons_append, nil_append, mem_append, mem_cons, ofPred_or,
      not_mem_nil, or_false, ofPred_eq_eq_singleton, union_singleton, union_insert]
    rw [insert_inter_of_mem (by simpa [hF.nodup]), insert_inter_of_notMem (by simpa [hF.nodup])]
    grind
  grw [hF.nodup.getElems_ofPred_and, inter_subset_left,
    insert_eq_of_mem (by simp [hF.nodup, hlt]), getElems_Ico, ← toSet_concat_eq,
    ← extract_add_one_right _ hlt.le, ← getElems_Ico,
    hF.getElems_Ico_subset_closure hpb (by simpa) (by lia), M.closure_closure,
    (hF.joints_Ico_indep <| by grind).notMem_closure_iff_of_notMem (by simp [hF.nodup])]
  exact (hF.joints_Ico_indep (p := p) (q := q + 3) (by grind)).subset
    <| insert_subset (by simpa [hF.nodup, hpq.le]) <| getElems_mono _ <| by grind

lemma IsFan.isCircuit_quad (hF : M.IsFan F b c) (p) (hp : p + 4 < F.length) (hpb : p.bodd = b)
    (h5 : ∀ (h : F.length = 5), ¬ M.Parallel F[0] F[4]) :
    M.IsCircuit {F[p], F[p + 1], F[p + 3], F[p + 4]} := by
  have aux :
      b = false → c = false → p = 0 → p + 4 + 1 = F.length → ¬M.Parallel F[0] F[F.length - 1] := by
    rintro rfl rfl rfl h5'
    simpa [← h5'] using h5 h5'.symm
  have hC := hF.isCircuit_interval (show p < p + 4 by lia) hp hpb (by simpa) aux
  rw [pair_comm, insert_comm F[p + 1]]
  rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia), ofPred_and, ofPred_mem_eq,
    ← insert_Ico_add_one_left_eq_Ico (by lia), insert_inter_of_notMem (by simpa),
    ← insert_Ico_add_one_left_eq_Ico (by lia), insert_inter_of_mem (by simpa),
    ← insert_Ico_add_one_left_eq_Ico (by lia), insert_inter_of_notMem (by simpa),
    ← insert_Ico_add_one_left_eq_Ico (by lia), insert_inter_of_mem (by simpa),
    getElems_insert _ _ (by lia), getElems_insert _ _ (by lia)] at hC
  simpa [add_assoc] using hC

/-- If a circuit of a matroid contains joints `F[p + 1], F[q]` of a fan `F`,
and does not contain the cojoint `F[p]`,
then it comprises precisely `F[p + 1], F[q]`, and the cojoints between them.  -/
lemma IsFan.eq_interval_of_notMem_mem_mem (hF : M.IsFan F b c) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !b) (hqb : q.bodd = b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∈ C) :
    C = (F.getElems (insert (p + 1) <| insert q <| {i ∈ Ico (p + 1) q | i.bodd = !b})) := by
  induction q using Nat.strong_induction_on with | h q ihq =>
  suffices aux : (F.getElems (insert (p + 1) <| insert q <| {i ∈ Ico (p + 1) q | i.bodd = !b})) ⊆ C
  · exact hC.eq_of_superset_isCircuit (hF.isCircuit_interval (by lia) hqF (by simpa) hqb (by simp))
      aux
  suffices ∀ i (hi : i + 1 < F.length), p < i → i < q → i.bodd = !b → F[i] ∈ C from
    getElems_subset_iff.2 <| fun i hi ↦ by grind
  intro i hi hpi hiq hib
  have hp2 : F[p + 2] ∈ C := by rwa [← hF.mem_iff_mem₁₂ (C := C) p (by lia) (by simpa [hpb]) hpC]
  induction i using Nat.twoStepInduction with
  | zero => grind
  | one => grind
  | more i ih =>
    obtain rfl | rfl := b.eq_or_eq_not i.bodd
    · simp at hib
    obtain rfl | hne := eq_or_ne p i
    · assumption
    obtain rfl | hne := eq_or_ne p (i + 1)
    · simp at hpb
    by_cases h1 : F[i + 1] ∈ C
    · rw [ihq (i + 1) (by lia) (by grind) (by lia) (by simp) hpC hp1C h1] at hqC
      simp [hF.nodup, hqb, show q ≠ i + 1 by lia, hpq.ne.symm] at hqC
    rw [← hF.mem_iff_mem₀₂ _ _ (by lia) (by simpa) h1]
    exact ih (by lia) (by lia) (by lia) (by simp)

lemma IsFan.exists_eq_interval_of_notMem_mem_add_one (hF : M.IsFan F b c) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !b) (hqb : q.bodd = !b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∉ C) :
    ∃ (r : ℕ) (_ : p + 1 < r) (_ : r < q), r.bodd = b ∧
    C = F.getElems (insert (p + 1) <| insert r <| {i ∈ Ico (p + 1) r | i.bodd = !b}) := by
  by_cases! hr : ¬ (∀ r (hr : r < q), p + 1 < r → r.bodd = !p.bodd → F[r] ∉ C)
  · push Not at hr
    obtain ⟨r, hrq, hpr, hrb, hrC⟩ := hr
    exact ⟨r, hpr, by lia, (by simpa [hrb] using hpb),
      hF.eq_interval_of_notMem_mem_mem hpr (by lia) hpb (by simpa [hrb] using hpb) hC hpC hp1C hrC⟩
  refine False.elim <| hqC ?_
  clear hqC
  obtain ⟨d, rfl⟩ := exists_add_of_le (show p + 2 ≤ q by lia)
  induction d using Nat.twoStepInduction with
  | zero => grind [hF.mem_or_mem₀₂ p C (by lia) (by simpa [hpb]) hp1C]
  | one => simp [hpb] at hqb
  | more d ih =>
    simp_rw [← add_assoc]
    simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_not] at hqb
    rw [← hF.mem_iff_mem₀₂ _ _ (by simpa) (by simpa [hqb])]
    · exact ih (by lia) (by lia) (by simpa) hpC hp1C (by grind)
    apply hr _ (by lia) (by lia)
    rw [Nat.bodd_succ, Bool.not_inj_iff, hpb]
    simpa

/-- If a circuit doesn't contain two particular cojoints `F[s], F[t]` of a fan `F`,
but it contains something between them, then it is an interval. -/
lemma IsFan.exists_eq_interval_of_notMem_mem_notMem {s t r : ℕ} (hF : M.IsFan F b c) (hsr : s < r)
    (hrt : r < t) (ht : t < F.length) (hsb : s.bodd = !b) (htb : t.bodd = !b)
    (hC : M.IsCircuit C) (hsC : F[s] ∉ C) (hrC : F[r] ∈ C) (htC : F[t] ∉ C) :
    ∃ (p q : ℕ) (_ : s < p) (_ : p < q) (_ : q < t), p.bodd = b ∧ q.bodd = b ∧
    C = F.getElems (insert p <| insert q <| {i ∈ Ico p q | i.bodd = !b}) := by
  induction h : r - s using Nat.strong_induction_on generalizing r s with | h d ih =>
  by_cases hs1 : F[s + 1] ∈ C
  · obtain ⟨j, hsj, hjt, rfl, rfl⟩ :=
      hF.exists_eq_interval_of_notMem_mem_add_one (by lia) ht hsb htb hC hsC hs1 htC
    exact ⟨s + 1, j, by simp [hsb, hsj, hjt]⟩
  have hs1i : s + 1 < r := by grind
  rw [hF.mem_iff_mem₁₂ _ _ (by lia) (by simpa [hsb]) hsC] at hs1
  obtain ⟨p, q, hpq⟩ := ih (r - (s + 2)) (by lia) (by grind) hrt (by simpa) hs1 hrC rfl
  exact ⟨p, q, by grind⟩

/-- If the set of joints of a circuit `C` is contained in `F[p]`, and `C` contains the cojoint
`F[p + 1]`, then `C` contains all subsequent cojoints. -/
lemma IsFan.cojoint_mem_of_subsingleton_joint_mem_le (hF : M.IsFan F b c) (hpF : p + 1 < F.length)
    (hpb : p.bodd = b) (hC : M.IsCircuit C)
    (hpC : ∀ i (hi : i < F.length), i.bodd = b → F[i] ∈ C → i = p) (hp1 : F[p + 1] ∈ C)
    (hpq : p < q) (hq : q < F.length) (hqb : q.bodd = !b) : F[q] ∈ C := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hpq
  induction d using Nat.twoStepInduction with
  | zero => simpa
  | one => simp [hpb] at hqb
  | more d ih _ =>
    obtain hdb : d.bodd = false := by cases b with simpa [hpb] using hqb
    obtain h | h := (hF.isTriangle_getElem (p + d + 1) (by lia)).mem_or_mem_of_isCircuit_bDual
      (K := C) (by simpa [hpb, hdb]) (ih (by lia) (by lia) (by simp [hpb, hdb]))
    · simpa [add_assoc] using hpC _ (by lia) (by simp [hpb, hdb]) h
    simpa [add_assoc]

/-- If the set of joints of a circuit `C` is contained in `F[p]`, and `C` contains the cojoint
`F[p + 1]`, then `C` contains all earlier cojoints. -/
lemma IsFan.cojoint_mem_of_subsingleton_joint_mem_ge (hF : M.IsFan F b c) (hpF : p + 1 < F.length)
    (hpb : p.bodd = !b) (hC : M.IsCircuit C)
    (hpC : ∀ i (hi : i < F.length), i.bodd = b → F[i] ∈ C → i = p + 1) (hp1 : F[p] ∈ C)
    (hqp : q ≤ p) (hqb : q.bodd = !b) : F[q] ∈ C := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hqp
  induction d using Nat.twoStepInduction generalizing q with
  | zero => simpa using hp1
  | one => simp [hqb] at hpb
  | more d ih _ =>
    obtain hdb : d.bodd = false := by cases b with simpa [hqb] using hpb
    specialize ih (q := q + 2) (by simpa) (by lia) (by simpa using hpb) (by grind)
      (by simpa [add_right_comm, add_assoc]) (by lia)
    obtain h | h := (hF.isTriangle_getElem q (by lia)).reverse.mem_or_mem_of_isCircuit_bDual
      (K := C) (by simpa [hdb, hqb]) ih
    · simpa using hpC (q + 1) (by lia) (by simpa) h
    assumption

/-- If `F[p]` is the unique joint in a circuit `C`, then `C` contains either all earlier cojoints
or all subsequent cojoints. -/
lemma IsFan.forall_cojoint_mem_le_or_forall_cojoint_mem_le (hF : M.IsFan F b c) (hpF : p < F.length)
    (hpb : p.bodd = b) (hpC : F[p] ∈ C) (hC : M.IsCircuit C)
    (hpC' : ∀ i (hi : i < F.length), i.bodd = b → F[i] ∈ C → i = p) :
    (∀ q (hq : q < p), q.bodd = !b → F[q] ∈ C) ∨
    (∀ q (hq : q < F.length), p < q → q.bodd = !b → F[q] ∈ C) := by
  obtain rfl | p := p
  · simp
  obtain h_eq | hlt := (show p + 2 ≤ F.length by lia).eq_or_lt
  · grind
  have hpb : p.bodd = !b := by simpa using hpb
  obtain h | h := (hF.isTriangle_getElem p (by lia)).swap_left.mem_or_mem_of_isCircuit_bDual
    (by simpa [hpb]) hpC
  · exact .inl fun q hq hqb ↦
      hF.cojoint_mem_of_subsingleton_joint_mem_ge hpF hpb hC hpC' h (by lia) hqb
  exact .inr fun q hq hqF hqb ↦ hF.cojoint_mem_of_subsingleton_joint_mem_le (by lia) (by simpa)
    hC hpC' h hqF hq hqb

/-- Each proper subset of the cojoints is independent. -/
lemma IsFan.indep_of_ssubset_cojoints (hF : M.IsFan F b c) {I : Set α}
    (hI : I ⊂ F.getElems {i | i.bodd = !b}) : M.Indep I := by
  have hss : F.getElems {i | i.bodd = !b} ⊆ {e | e ∈ F} := getElems_subset_toSet ..
  rw [indep_iff_forall_subset_not_isCircuit (hI.subset.trans (hss.trans hF.subset_ground))]
  refine fun C hCI hC ↦ hI.not_subset ?_
  have hCb : ∀ {i} {hi : i < F.length}, F[i] ∈ C → i.bodd = !b :=
    @fun i hi hiC ↦ by simpa [hF.nodup.getElem_mem_getElems_iff] using hI.subset (hCI hiC)
  simp only [getElems_subset_iff, mem_ofPred_eq]
  by_cases! hi : ∃ (i : ℕ) (hi : i + 2 < F.length), F[i + 1] ∈ C
  · obtain ⟨i, hi, hiC⟩ := hi
    have hib : i.bodd = b := by
      simpa [hF.nodup.getElem_mem_getElems_iff] using hI.subset <| hCI hiC
    refine fun q hq hqb ↦ hCI ?_
    obtain hiq | hiq := le_or_gt (i + 1) q
    · exact hF.cojoint_mem_of_subsingleton_joint_mem_le (by lia) (by simpa) hC (by grind) hiC
        (by lia) (by lia) hqb
    exact hF.cojoint_mem_of_subsingleton_joint_mem_ge hi (by simpa) hC (by grind) hiC hiq.le hqb
  obtain hss | hnt := C.subsingleton_or_nontrivial
  · obtain ⟨e, heC⟩ := hC.nonempty
    obtain ⟨i, hiF, hib, rfl⟩ := hI.subset (hCI heC)
    obtain rfl := hss.eq_singleton_of_mem (x := F[i]) heC
    exact False.elim <| (hF.isNonloop (e := F[i]) (by simp)).not_isLoop (by simpa using hC)
  obtain ⟨f, hfC, hfne⟩ := hnt.exists_ne (F[F.length - 1])
  obtain ⟨j, hjF, hjb, rfl⟩ := hI.subset (hCI hfC)
  obtain hne | rfl := ne_or_eq j 0
  · obtain rfl | j := j <;> grind
  obtain rfl : b = true := by simpa using hCb hfC
  obtain ⟨e, heC, he0⟩ := hnt.exists_ne F[0]
  obtain ⟨rfl | rfl | i, hiF, hib, rfl⟩ := hI.subset (hCI heC)
  · simp at he0
  · simpa using hCb heC
  obtain h | h :=
    (hF.isTriangle_getElem 0 (by grind)).mem_or_mem_of_isCircuit_bDual (by simpa) hfC
  · simpa using hCb h
  obtain h2 | h3 := (show 3 ≤ F.length by lia).eq_or_lt
  · grind
  exact False.elim <| hi _ h3 h

/-- A parallel pair in a fan is hard to find; it must either comprise both ends, or two consecutive
elements at one of the ends. The upper bound of 6 is best-possible,
since the `5`-fan `[0, 1, 2, 3, 4]` can have the pairs `[0, 2]` and `[1, 3]` both parallel. -/
lemma IsFan.eq_eq_of_parallel (h : M.IsFan F b c) (hF : 6 ≤ F.length) {hi : i < F.length}
    {hj : j < F.length} (hij : i < j) (hC : M.Parallel F[i] F[j]) :
    (b = true ∧ i = 0 ∧ j = 1) ∨ (c = true ∧ i + 2 = F.length ∧ j + 1 = F.length) ∨
    b = false ∧ c = false ∧ i = 0 ∧ j + 1 = F.length := by
  replace hC := hC.isCircuit_of_ne (by grind)
  obtain ⟨rfl | rfl | d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  · obtain rfl | i := i
    · obtain rfl | rfl := b
      · exact False.elim <| (h.isTriangle_bDual (by lia)).indep₁₂.not_dep hC.dep
      simp
    obtain hib | hib := i.bodd.eq_or_eq_not b
    · exact False.elim <| (h.isTriangle_getElem_of_eq i (by lia) hib).indep₂₃.not_dep hC.dep
    by_cases hle : i + 3 < F.length
    · exact False.elim <| (h.isTriangle_getElem_of_eq (i + 1) (by lia) (by simpa)).indep₁₂.not_dep
        hC.dep
    simp [h.bool_right_eq, (show F.length = i + 3 by lia), hib]
  · obtain hib | hib := i.bodd.eq_or_eq_not b
    · exact False.elim <| (h.isTriangle_getElem_of_eq i (by lia) hib).indep₁₃.not_dep hC.dep
    by_cases! h2i : i < 2
    · have hcon := h.mem_or_mem₁₂ (i + 2) (C := {F[i], F[i + 2]}) (by lia) (by simpa [hib] using hC)
      simp [h.nodup.getElem_inj_iff, add_assoc] at hcon
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' h2i
    have hwin := h.mem_or_mem₀₁ i {F[i + 2], F[i + 4]} (by lia) <| by
      simpa [show i.bodd = !b by simpa using hib]
    simp [h.nodup.getElem_inj_iff] at hwin
  obtain rfl | i := i
  · obtain rfl | rfl := b
    · cases hdb : d.bodd
      · have hcon := h.mem_or_mem₀₁ (d + 1) {F[0], F[d + 3]} (by lia) (by simpa [hdb] using hC)
        simp [h.nodup.getElem_inj_iff] at hcon
      obtain h_eq | hne := eq_or_ne (d + 4) F.length
      · simpa [← h_eq, h.bool_right_eq]
      have hcon := h.mem_or_mem₀₂ (d + 2) {F[0], F[d + 3]} (by lia) (by simpa [hdb] using hC)
      simp [h.nodup.getElem_inj_iff] at hcon
    have hcon := h.mem_or_mem₁₂ 0 {F[0], F[d + 3]} (by lia) (by simpa using hC)
    simp [h.nodup.getElem_inj_iff] at hcon
  exfalso
  simp only [add_assoc, add_comm 1, Nat.reduceAdd] at hC
  obtain hib | hib := i.bodd.eq_or_eq_not b
  · have hcon := h.mem_or_mem₁₂ (i + 1) {F[i + 1], F[i + (d + 4)]} (by lia) (by simpa [hib])
    grind [h.nodup.getElem_inj_iff]
  have hcon := h.mem_or_mem₀₂ i {F[i + 1], F[i + (d + 4)]} (by lia) (by simpa [hib])
  simp [h.nodup.getElem_inj_iff] at hcon

-- lemma IsFan.delete_head'' (hF : M.IsFan F b c) (h3 : 3 ≤ F.length)
--     -- (h3 : F.length = 2 → ¬ )
--     (h_tri : b = true → ¬ M✶.Parallel F[0] F[1])
--     (h4 : b = false → F.length = 4 → ¬ M✶.Parallel F[0] F[2])
--     (h_pair : b = false → c = false → ¬ M✶.Parallel F[0] F[F.length - 1]) :
--     (M ＼ {F[0]}).IsFan F.tail (!b) c := by
--   match F with
--   | [] => simp at h3
--   | [_] => simp at h3
--   | [_, _] => simp at h3
--   | e :: f :: g :: F =>
--   simp only [getElem_cons_zero, getElem_cons_succ, length_cons, add_tsub_cancel_right,
--     tail_cons] at *
--   induction F using List.reverseRecOn generalizing c with
--   | nil =>
--     sorry
--   | append_singleton F a ih =>

--     specialize ih (by simpa [dropLast_cons_of_ne_nil] using hF.dropLast (by simp)) (by simp)
-- ?_ ?_
--     · rintro rfl hFl hpara
--       obtain ⟨y, rfl⟩ := (length_eq_one_iff (l := F)).1 (by lia)
--       have := (hF.isTriangle_getElem_of_eq 2 (by simp) rfl).isCircuit.mem_iff_mem_of_parallel_du
--         hpara
--       grind [hF.nodup]
--     · simp
--       rintro rfl rfl hpara
--       cases F with
--       | nil => exact h4 rfl rfl hpara
--       | cons y F =>
--         have hTP := (hF.isTriangle_bDual (by simp)).isCircuit.mem_iff_mem_of_parallel_bDual hpara
--         simp only [length_cons, getElem_cons_succ] at hTP
--         grind [hF.nodup]
--     have := ih.concat (e := a)
--     simp at this
--     _






  --

lemma IsFan.delete_head (hF : M.IsFan F true c) (h3 : 3 ≤ F.length)
    (h_pair : c = true → ¬ M✶.Parallel F[0] F[F.length - 1]) :
    (M ＼ {F[0]}).IsFan F.tail false c := by
  simpa using (hF.dual.contract_head h3 (by simpa)).dual

lemma IsFan.contract_head_three (hF : M.IsFan F b c) (h3 : F.length = 3)
    (hnp₁ : b = true → ¬ M.Parallel F[0] F[1]) (hnp₂ : b = true → ¬ M.Parallel F[0] F[2]) :
    (M ／ {F[0]}).IsFan F.tail (!b) c := by
  rw [length_eq_three] at h3
  obtain ⟨e, f, g, rfl⟩ := h3
  obtain rfl : b = c := by simpa using hF.bool_left_eq
  suffices (M ／ {e}).IsFan [f, g] (!b) (!!b) by simpa
  have hT : (M.bDual b).IsTriangle {e, f, g} := by simpa using hF.isTriangle_getElem 0 (by lia)
  refine IsFan.of_pair _ _ _ _ ?_ ?_ hT.ne₂₃
  · rintro (rfl | rfl)
    · obtain rfl | rfl := b
      · exact hT.parallel_contract₁.isNonloop_left
      simp only [bDual_false, contract_isNonloop_iff, mem_sdiff]
      rw [← hT.isNonloop_of_bDual₂.parallel_iff_mem_closure, parallel_comm,
        and_iff_right (IsTriad.mem_ground₂ hT)]
      exact hnp₁ rfl
    simpa [hT.ne₁₂.symm] using hT.isNonloop_bDual₂ (b := !b)
  rintro (rfl | rfl)
  · obtain rfl | rfl := b
    · exact hT.parallel_contract₁.isNonloop_right
    replace baz : ¬ M.Parallel e g := by simpa using hnp₂
    rw [parallel_comm, hT.isNonloop_of_bDual₃.parallel_iff_mem_closure] at baz
    simp [baz, IsTriad.mem_ground₃ hT]
  simpa [hT.ne₁₃.symm] using hT.isNonloop_bDual₃ (b := !b)

@[grind .]
lemma IsFan.length_ge_four_of_eq_ground [M.Simple] [M✶.Simple] (hF : M.IsFan F b c)
    (hFE : {e | e ∈ F} = M.E) : 4 ≤ F.length := by
  have hF2 := hF.two_le_length
  have hr := M.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.get_mem_ground (i := 0)) (hF.get_mem_ground (i := 1))
  have hr1 := M✶.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.get_mem_ground (i := 0)) (hF.get_mem_ground (i := 1))
  have hle := encard_le_encard hFE.symm.subset
  grw [← eRank_add_eRank_dual, F.encard_toSet_le, ← M.eRk_le_eRank {F[0], F[1]},
    ← M✶.eRk_le_eRank {F[0], F[1]}, hr, hr1] at hle
  enat_to_nat!; lia

/-- If `F` is a fan whose ends are joints, and `C` is a circuit containing the first but not
the second element of `F`, then `M` has a circuit containing the first element of `F`,
and no other elements of `F` except possibly the last.  -/
lemma IsFan.exists_isCircuit_subset_first_last (hF : M.IsFan F false false)
    (hC : M.IsCircuit C) (h0C : F[0] ∈ C) (h1C : F[1] ∉ C) :
    ∃ C₀ ⊆ insert F[F.length - 1] C, M.IsCircuit C₀ ∧ F[0] ∈ C₀ := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF.two_le_length
  suffices aux : ∀ k ≤ n, ∃ C₀, M.IsCircuit C₀ ∧ F[0] ∈ C₀ ∧ C₀ ⊆ C ∪ {e | e ∈ F} ∧
      ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C₀ → k ≤ i by
    refine Exists.imp ?_ <| aux n rfl.le
    simp only [and_imp]
    refine fun C₀ hC₀ h0C₀ hC₀ss h ↦ ⟨?_, hC₀, h0C₀⟩
    refine fun e heC₀ ↦ ?_
    by_cases heC : e ∈ C
    · exact .inr heC
    obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem (show e ∈ F by grind)
    · grind
    obtain rfl : n = i := by grind
    simp [hn, add_comm]
  rintro (rfl | k) hk
  · use C; grind
  induction k with
  | zero => use C; grind
  | succ k ih =>
    obtain ⟨C₀', hC₀', h0C₀', hC₀'ss, hClt⟩ := ih (by lia)
    obtain hkC | hkC := em' (F[k + 2] ∈ C₀')
    · exact ⟨C₀', by grind⟩
    cases hb : !k.bodd
    · have hT' := (hF.isTriad_getElem_of_eq k (by lia) (by simpa using hb)).reverse
      obtain h1 | h2 := hT'.mem_or_mem_of_isCocircuit (K := C₀') (by simpa) hkC
      · grind [hClt _ _ h1]
      obtain rfl | k := k
      · grind
      grind [hClt _ _ h2]
    obtain rfl | hlt := hk.eq_or_lt
    · simpa [hn, ← hb] using hF.length_bodd_eq
    have hT := hF.isTriangle_getElem_of_eq (k + 2) (by lia) (by simpa using hb)
    have elim := hC₀'.strong_elimination hT.isCircuit (e := F[k + 2]) (f := F[0]) hkC (by simp)
      h0C₀' (by simp [hF.nodup.getElem_inj_iff])
    obtain ⟨C₀, hC₀ss, hC₀, h0C₀⟩ := elim
    refine ⟨C₀, hC₀, h0C₀, ?_, fun i hi hiC₀ ↦ by grind [hF.nodup.getElem_inj_iff]⟩
    grw [hC₀ss, hC₀'ss, sdiff_subset]
    grind [Set.union_subset_iff, insert_subset_iff]

/-- For any fan `F = [a, b, ..., z]` whose ends are joints and for which `{a, b}` isn't series,
there is a circuit `C` with `a ∈ C ∩ F ⊆ {a, z}`. -/
lemma IsFan.exists_isCircuit_first_mem_of_length_odd (hF : M.IsFan F false c)
    (h_odd : Odd F.length) (h01 : ¬ M✶.Parallel (F[0]'(by grind)) (F[1]'hF.two_le_length)) :
    ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧ ∀ i (hi : i + 1 < F.length),
      F[i + 1] ∈ C → i + 2 = F.length := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF.two_le_length
  suffices aux : ∀ k ≤ n, ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧
      ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C → k ≤ i from
    Exists.imp (by grind) <| aux n rfl.le
  rw [parallel_dual_iff_forall_circuit (hF.dual.isNonloop (by simp)) hF.get_mem_ground] at h01
  simp_rw [not_forall, exists_prop] at h01
  intro k hk
  induction k with
  | zero => exact Exists.imp (by grind) h01
  | succ k ih =>
    obtain rfl | k := k
    · exact Exists.imp (by grind) h01
    obtain ⟨C, hC, h0C, hClt⟩ := ih (by lia)
    obtain hkC | hkC := em' (F[k + 2] ∈ C)
    · exact ⟨C, by grind⟩
    by_cases hb : k.bodd = true
    · obtain hwin | hwin := (hF.isTriangle_getElem k (by lia)).reverse.mem_or_mem_of_isCircuit_bDual
        (by simpa [hb]) hkC
      · grind
      obtain rfl | k := k; simp at hb
      grind
    have hnk : n ≠ k + 2 := fun hnk ↦ by simpa [hn, hnk, hb] using h_odd.bodd
    have hT : M.IsTriangle {F[k + 2], F[k + 2 + 1], F[k + 2 + 2]} := by
      simpa [hb] using hF.isTriangle_getElem (k + 2) (by grind)
    obtain ⟨C', hC'ss, hC', h0C'⟩ := hC.strong_elimination hT.isCircuit hkC (by simp) h0C
      (by simp [hF.nodup.getElem_inj_iff])
    refine ⟨C', hC', h0C', fun i hilt hiC' ↦ ?_⟩
    obtain ⟨(rfl | rfl | hiC), hik⟩ : (i = k + 2 ∨ i = k + 3 ∨ F[i + 1] ∈ C) ∧ ¬i = k + 1 := by
      simpa [hF.nodup.getElem_inj_iff] using hC'ss hiC'
    all_goals grind

/-- If `M` is a simple, cosimple matroid whose ground set is a fan, then the fan is even
and wraps around its own beginning.  -/
lemma IsFan.isTriangle_of_simple (hF : M.IsFan F false c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) :
      Even F.length ∧ M.IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  obtain rfl | rfl | n := n
  · grind [hF.length_ge_four_of_eq_ground hFE]
  · grind [hF.length_ge_four_of_eq_ground hFE]
  have hnp : ¬M✶.Parallel F[0] F[1] := by
    rw [hM'.parallel_iff_eq (hF.dual.subset_ground (getElem_mem ..))]
    simp [hF.nodup.getElem_inj_iff]
  set m := if Odd n then n + 3 else n + 2 with hm
  have hmlt : m < F.length := by lia
  have hm_odd : Odd (m + 1) := by simp [hm, Nat.odd_add_one, apply_ite]
  -- Take away the last element if the fan is even, then find a circuit containing `F[0]`
  -- that intersects the fan in only possibly the last element.
  obtain ⟨C, hC, h0C, hlt⟩ :=
    (hF.take (show 2 ≤ m + 1 by grind) (by lia)).exists_isCircuit_first_mem_of_length_odd
    (by rwa [length_take_of_le (by lia)]) (by rwa [getElem_take, getElem_take])
  simp_rw [length_take_of_le (show m + 1 ≤ F.length by lia), getElem_take] at hlt
  have hss : C ⊆ {F[m], F[n + 3], F[0]} := by
    intro e he
    obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem <| hC.subset_ground.trans hFE.symm.subset he
    · simp
    obtain hlt | hle := lt_or_ge i m
    all_goals grind
  obtain hn | hn := Nat.even_or_odd n
  · simp_rw [hm, if_neg (show ¬ Odd n by simpa)] at hss
    refine ⟨by grind, isTriangle_of_dep_of_encard_le
      (hC.dep.superset hss (by simp [insert_subset_iff, hF.get_mem_ground])) ?_⟩
    grw [encard_insert_le, encard_pair_le, show (2 : ℕ∞) + 1 = 3 from rfl]
  have hcard := encard_le_encard hss
  simp_rw [hm, if_pos hn] at hcard
  grw [insert_eq_of_mem (by simp), encard_pair_le, ← hC.girth_le_card, ← M.three_le_girth] at hcard
  norm_num at hcard

lemma IsFan.isTriangle_bDual_of_simple (hF : M.IsFan F b c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) : Even F.length ∧
      (M.bDual b).IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  simpa using IsFan.isTriangle_of_simple (M := M.bDual (b)) (F := F) (c := c != b) (by simpa) h3
    (by cases b with simpa) (by cases b with simpa) (by simpa)

lemma IsFan.eConn_le_two (h : M.IsFan F b c) : M.eConn {e | e ∈ F} ≤ 2 := by
  obtain hFl | hFl := lt_or_ge F.length 3
  · grw [eConn_le_encard, encard_toSet_le]
    enat_to_nat! <;> lia
  grw [← ENat.add_le_add_iff_right (k := F.length) (by simp), ← h.nodup.encard_toSet_eq,
    ← eRk_add_eRk_dual_eq _ _ h.subset_ground,
    ← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), mul_add, h.eRk_le hFl,
    h.dual.eRk_le hFl, h.nodup.encard_toSet_eq]
  cases b with cases c with (simp; enat_to_nat!; lia)

/-- If the head is spanned by the tail in the appropriate dual of `b`, then the fan
has connectivity one. -/
lemma IsFan.eConn_le_one_of_mem_closure (h : M.IsFan F b c)
    (hcl : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail}) : M.eConn {e | e ∈ F} ≤ 1 := by
  cases h with
  | of_pair b e f he hf hne =>
    grw [← eConn_bDual M (!b), eConn_le_eRk, show {x | x ∈ [e, f]} = {e, f} by grind,
      eRk_insert_of_mem_closure (by simpa using hcl), eRk_singleton_le]
  | cons_triangle e x y F b c h heF hT =>
    have hcl' : e ∈ (M.bDual (!b)).closure {z | z ∈ x :: y :: F} :=
      mem_of_mem_of_subset hT.mem_closure₁ <| closure_subset_closure _ <| by grind
    grw [← ENat.add_one_le_add_one_iff, ← eConn_bDual M !b, one_add_one_eq_two,
      ← (h.bDual !b).eConn_le_two,
      ← (M.bDual !b).eConn_insert_add_one_eq hcl' (by simpa using hcl) (by grind)]
    convert rfl.le
    grind

/-- TODO : I think this should hold even if the fan has odd length. -/
lemma IsFan.eConn_eq_zero_of_mem_closure_mem_closure (h : M.IsFan F b (!b))
    (hcl : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail})
    (hcl' : F[F.length - 1] ∈ (M.bDual b).closure {x | x ∈ F.dropLast}) :
    M.eConn {e | e ∈ F} = 0 := by
  wlog hb : b = false generalizing F b with aux
  · obtain rfl : b = true := by simpa using hb
    simpa using aux (F := F.reverse) (b := false) (by simpa using h.reverse) (by simpa using hcl')
      (by simpa using hcl) rfl
  subst hb
  have hr := (M.eRk_add_eRk_dual_eq {e | e ∈ F} h.subset_ground).ge
  replace hcl' := eRk_insert_of_mem_closure hcl'
  rw [← toSet_concat_eq, ← getLast_eq_getElem h.ne_nil, dropLast_concat_getLast, bDual_false]
    at hcl'
  replace hcl := eRk_insert_of_mem_closure hcl
  rw [← toSet_cons_eq, getElem_zero, cons_head_tail, Bool.not_false, bDual_true] at hcl
  grw [← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), mul_add, mul_add, hcl, hcl',
    h.nodup.encard_toSet_eq] at hr
  obtain h2 | h3 := le_or_gt F.length 2
  · grw [eRk_le_encard, eRk_le_encard, encard_toSet_le, encard_toSet_le] at hr
    simp only [length_dropLast, ENat.natCast_sub, Nat.cast_one, length_tail] at hr
    enat_to_nat! <;> lia
  grw [(h.tail (by lia)).dual.eRk_le (by grind [h.length_even]),
    (h.dropLast (by lia)).eRk_le (by grind [h.length_even])] at hr
  simp only [length_dropLast, ENat.natCast_sub, Nat.cast_one, Bool.toNat_false,
    Bool.not_false, Bool.not_true, length_tail] at hr
  enat_to_nat! <;> lia
