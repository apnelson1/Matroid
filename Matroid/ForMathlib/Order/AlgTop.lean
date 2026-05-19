import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Ring.WithTop
-- import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Ring.Subring.Defs
-- import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.Archimedean.Defs

set_option linter.style.longLine false

-- #check add_right_inj_of_ne_top

-- missing to_dual tags
attribute [to_dual self] mul_le_mul_iff_left add_le_add_iff_left le_of_mul_le_mul_left'
  le_of_mul_le_mul_right' le_of_add_le_add_right le_of_add_le_add_left mul_lt_mul_left
  mul_lt_mul_right add_lt_add_left add_lt_add_right mul_le_mul_right mul_le_mul_left
  add_le_add_right add_le_add_left

section Order

variable {α : Type*} {a b : α}

class BotUniqueClass (α : Type*) [LE α] : Prop where
  protected unique (a b : α) (ha : IsBot a) (hb : IsBot b) : a = b

/-- A class for the property that there is at most one top element. -/
@[to_dual]
class TopUniqueClass (α : Type*) [LE α] : Prop where
  protected unique (a b : α) (ha : IsTop a) (hb : IsTop b) : a = b

@[to_dual]
instance (α : Type*) [PartialOrder α] : TopUniqueClass α where
  unique a b ha hb := (hb a).antisymm (ha b)

@[to_dual]
lemma IsTop.eq [LE α] [TopUniqueClass α] (ha : IsTop a) (hb : IsTop b) : a = b :=
  TopUniqueClass.unique _ _ ha hb

@[to_dual]
lemma IsTop.eq_top' [LE α] [TopUniqueClass α] [OrderTop α] (ha : IsTop a) : a = ⊤ :=
  ha.eq isTop_top

@[to_dual (attr := simp)]
lemma isTop_iff [LE α] [OrderTop α] [TopUniqueClass α] : IsTop a ↔ a = ⊤ :=
  ⟨fun h ↦ h.eq isTop_top, fun h ↦ by simp [h]⟩

@[to_dual bot_lt_iff_ne_bot']
lemma lt_top_iff_ne_top' [Preorder α] [OrderTop α] [TopUniqueClass α] : a < ⊤ ↔ a ≠ ⊤ := by
  rw [lt_iff_le_not_ge, and_iff_right le_top, Ne, not_iff_not]
  exact ⟨fun h ↦ (isTop_top.mono h).eq_top', fun h ↦ h.symm.le⟩

@[to_dual eq_bot_or_bot_lt']
lemma eq_top_or_lt_top' [Preorder α] [OrderTop α] [TopUniqueClass α] (a : α) : a = ⊤ ∨ a < ⊤ := by
  simp [lt_top_iff_ne_top', em]

@[to_dual (attr := simp) le_bot_iff']
lemma top_le_iff' [Preorder α] [OrderTop α] [TopUniqueClass α] : ⊤ ≤ a ↔ a = ⊤ := by
  obtain rfl | hlt := eq_top_or_lt_top' a
  · simp
  simp [hlt.ne, hlt.not_ge]

end Order

variable {M α : Type*} {a b : M}

/-- A class for the property that `0` is not a bottom element. -/
class ZeroNotBotClass (M : Type*) [Zero M] [LE M] : Prop where
  protected not_isBot_zero : ¬ IsBot (0 : M)

/-- A class for the property that `1` is not a bottom element. -/
class OneNotBotClass (M : Type*) [One M] [LE M] : Prop where
  protected not_isBot_one : ¬ IsBot (1 : M)

/-- A class for the property that `0` is not a top element. -/
class ZeroNotTopClass (M : Type*) [Zero M] [LE M] : Prop where
  protected not_isTop_zero : ¬ IsTop (0 : M)

/-- A class for the property that `1` is not a top element. -/
@[to_additive (attr := to_dual)]
class OneNotTopClass (M : Type*) [One M] [LE M] : Prop where
  protected not_isTop_one : ¬ IsTop (1 : M)

@[to_additive (attr := to_dual (attr := simp))]
lemma one_ne_top [One M] [LE M] [OrderTop M] [OneNotTopClass M] : (1 : M) ≠ ⊤ :=
  fun h ↦ (OneNotTopClass.not_isTop_one (M := M)) <| by simp [h]

@[to_additive (attr := to_dual (attr := simp))]
lemma one_lt_top [One M] [Preorder M] [OrderTop M] [TopUniqueClass M] [OneNotTopClass M] :
    (1 : M) < ⊤ := by
  rw [lt_top_iff_ne_top']
  simp

class AddIsTopClass (M : Type*) [LE M] [AddZero M] extends ZeroNotTopClass M where
  isTop_or_isTop (a b : M) (hab : IsTop (a + b)) : IsTop a ∨ IsTop b

class AddIsBotClass (M : Type*) [LE M] [AddZero M] extends ZeroNotBotClass M where
  isBot_or_isBot (a b : M) (hab : IsBot (a + b)) : IsBot a ∨ IsBot b

class MulIsBotClass (M : Type*) [LE M] [MulOne M] extends OneNotBotClass M where
  isBot_or_isBot (a b : M) (hab : IsBot (a * b)) : IsBot a ∨ IsBot b

@[to_additive (attr := to_dual)]
class MulIsTopClass (M : Type*) [LE M] [MulOne M] extends OneNotTopClass M where
  protected isTop_or_isTop (a b : M) (hab : IsTop (a * b)) : IsTop a ∨ IsTop b

@[to_additive (attr := to_dual)]
lemma eq_or_eq_of_mul_eq_top [MulOne M] [Preorder M] [OrderTop M] [TopUniqueClass M]
    [MulIsTopClass M] (h : a * b = ⊤) : a = ⊤ ∨ b = ⊤ := by
  simp_rw [← isTop_iff] at *
  exact MulIsTopClass.isTop_or_isTop _ _ h

@[to_additive]
lemma exists_of_prod_eq_top [Preorder M] [OrderTop M] [TopUniqueClass M] [CommMonoid M]
    [MulIsTopClass M] {s : Finset α} {f : α → M} (h : ∏ x ∈ s, f x = ⊤) : ∃ x, f x = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert a s has ih =>
    rw [Finset.prod_insert has] at h
    obtain (ha | hs) := eq_or_eq_of_mul_eq_top h
    · exact ⟨a, ha⟩
    exact ih hs

class IsTopAddClass (M : Type*) [LE M] [AddZero M] where
  protected isTop_mul_right (a : M) (ha : IsTop a) (b : M) : IsTop (a + b)
  protected isTop_mul_left (a : M) (ha : IsTop a) (b : M) : IsTop (b + a)

class IsBotAddClass (M : Type*) [LE M] [AddZero M] where
  protected isBot_add_right (a : M) (ha : IsBot a) (b : M) : IsBot (a + b)
  protected isBot_add_left (a : M) (ha : IsBot a) (b : M) : IsBot (b + a)

class IsBotMulClass (M : Type*) [LE M] [MulOne M] where
  protected isBot_mul_right (a : M) (ha : IsBot a) (b : M) : IsBot (a * b)
  protected isBot_mul_left (a : M) (ha : IsBot a) (b : M) : IsBot (b * a)

@[to_additive (attr := to_dual)]
class IsTopMulClass (M : Type*) [LE M] [MulOne M] where
  protected isTop_mul_right (a : M) (ha : IsTop a) (b : M) : IsTop (a * b)
  protected isTop_mul_left (a : M) (ha : IsTop a) (b : M) : IsTop (b * a)

@[to_additive (attr := to_dual (attr := simp))]
lemma mul_top {M : Type*} [LE M] [OrderTop M] [MulOne M] [IsTopMulClass M] [TopUniqueClass M]
    (a : M) : a * ⊤ = ⊤ :=
  isTop_iff.1 <| IsTopMulClass.isTop_mul_left _ isTop_top _

@[to_additive (attr := to_dual (attr := simp))]
lemma top_mul {M : Type*} [LE M] [OrderTop M] [MulOne M] [IsTopMulClass M] [TopUniqueClass M]
    (a : M) : ⊤ * a = ⊤ :=
  isTop_iff.1 <| IsTopMulClass.isTop_mul_right _ isTop_top _

@[to_additive (attr := to_dual)]
lemma mul_ne_top [MulOne M] [Preorder M] [OrderTop M] [TopUniqueClass M] [MulIsTopClass M]
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b ≠ ⊤ := by
  contrapose! ha
  exact (or_iff_left hb).1 (eq_or_eq_of_mul_eq_top ha)

@[to_additive (attr := to_dual (attr := simp))]
lemma mul_eq_top_iff [MulOne M] [Preorder M] [OrderTop M] [TopUniqueClass M] [MulIsTopClass M]
    [IsTopMulClass M] : a * b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  ⟨eq_or_eq_of_mul_eq_top, by rintro (rfl | rfl) <;> simp⟩

class IsBotMulPosClass (M : Type*) [Preorder M] [MulZeroOneClass M] where
  protected isBot_mul_right (a : M) (ha : IsBot a) (b : M) (hb : 0 < b) : IsBot (a * b)
  protected isBot_mul_left (a : M) (ha : IsBot a) (b : M) (hb : 0 < b) : IsBot (b * a)

@[to_dual]
class IsTopMulPosClass (M : Type*) [Preorder M] [MulZeroOneClass M] where
  protected isTop_mul_right (a : M) (ha : IsTop a) (b : M) (hb : 0 < b) : IsTop (a * b)
  protected isTop_mul_left (a : M) (ha : IsTop a) (b : M) (hb : 0 < b) : IsTop (b * a)

lemma mul_top_of_pos [Preorder M] [OrderTop M] [TopUniqueClass M] [MulZeroOneClass M]
    [IsTopMulPosClass M] (ha : 0 < a) : a * ⊤ = ⊤ :=
  isTop_iff.1 <| IsTopMulPosClass.isTop_mul_left _ isTop_top _ ha

lemma top_mul_of_pos [Preorder M] [OrderTop M] [TopUniqueClass M] [MulZeroOneClass M]
    [IsTopMulPosClass M] (ha : 0 < a) : ⊤ * a = ⊤ :=
  isTop_iff.1 <| IsTopMulPosClass.isTop_mul_right _ isTop_top _ ha

/-- The set of non-top elements in a `MulIsTopClass` is a submonoid. -/
@[to_additive (attr := to_dual (attr := simps))]
def Submonoid.notTop (M : Type*) [Monoid M] [LE M] [MulIsTopClass M] : Submonoid M where
  carrier := {x | ¬ IsTop x}
  mul_mem' := fun ha hb hab ↦ (MulIsTopClass.isTop_or_isTop _ _ hab).elim ha hb
  one_mem' := OneNotTopClass.not_isTop_one

@[to_additive (attr := to_dual (attr := simp))]
lemma Submonoid.mem_notTop_iff [Monoid M] [Preorder M] [OrderTop M] [MulIsTopClass M]
    [TopUniqueClass M] {x : M} : x ∈ Submonoid.notTop M ↔ x < ⊤ := by
  simp [Submonoid.notTop, lt_top_iff_ne_top']

instance {M : Type*} [CommMonoidWithZero M] [Preorder M] [MulIsTopClass M] [ZeroNotTopClass M] :
    CommMonoidWithZero (Submonoid.notTop M) where
  zero := ⟨0, ZeroNotTopClass.not_isTop_zero⟩
  zero_mul a := Subtype.val_inj.1 <| zero_mul a.1
  mul_zero a := Subtype.val_inj.1 <| mul_zero a.1

@[to_additive (attr := to_dual)]
lemma top_pow [Monoid M] [LE M] [OrderTop M] [TopUniqueClass M] [IsTopMulClass M]
    {n : ℕ} (hn : n ≠ 0) : (⊤ : M) ^ n = ⊤ := by
  obtain rfl | rfl | n := n
  all_goals simp_all [pow_succ]

@[to_additive (attr := to_dual (attr := simp))]
lemma pow_eq_top_iff [Monoid M] [Preorder M] [OrderTop M] [IsTopMulClass M] [MulIsTopClass M]
    [TopUniqueClass M] {n : ℕ} : a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h.1, top_pow h.2]⟩
  induction n with
  | zero => simp at h
  | succ n ih =>
    simp only [pow_succ, mul_eq_top_iff] at h
    exact h.elim (fun h' ↦ ⟨(ih h').1, by simp⟩) (by simp)

@[to_additive (attr := to_dual (attr := simp))]
theorem pow_lt_top_iff [Monoid M] [Preorder M] [OrderTop M] [IsTopMulClass M]
    [MulIsTopClass M] [TopUniqueClass M] {n : ℕ} : a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0 := by
  rw [lt_top_iff_ne_top', Ne, pow_eq_top_iff, and_comm, lt_top_iff_ne_top']
  tauto

def Subsemiring.notBot (α : Type*) [DecidableEq α] [Semiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] [NoZeroDivisors α] [MulIsBotClass α] [AddIsBotClass α] :
    Subsemiring α where
  carrier := {x | ¬ IsBot x}
  mul_mem' ha hb hab := (MulIsBotClass.isBot_or_isBot _ _ hab).elim ha hb
  one_mem' := OneNotBotClass.not_isBot_one
  add_mem' ha hb hab := (AddIsBotClass.isBot_or_isBot _ _ hab).elim ha hb
  zero_mem' := ZeroNotBotClass.not_isBot_zero

/-- The set of non-top elements in a ring with `MulEqTopClass`, `AddEqTopClass` is a subring. -/
def Subsemiring.notTop (α : Type*) [DecidableEq α] [Semiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] [NoZeroDivisors α] [MulIsTopClass α] [AddIsTopClass α] :
    Subsemiring α where
  carrier := {x | ¬ IsTop x}
  mul_mem' ha hb hab := (MulIsTopClass.isTop_or_isTop _ _ hab).elim ha hb
  one_mem' := OneNotTopClass.not_isTop_one
  add_mem' ha hb hab := (AddIsTopClass.isTop_or_isTop _ _ hab).elim ha hb
  zero_mem' := ZeroNotTopClass.not_isTop_zero


section CommMonoidWithZero

section StrictMono

variable {M : Type*} [CommMonoidWithZero M]

variable [Preorder M] [OrderTop M] [MulIsTopClass M] [ZeroNotTopClass M] [IsTopMulPosClass M]
    [PosMulStrictMono (Submonoid.notTop M)] [TopUniqueClass M] {a : M}

theorem mul_right_strictMono_of_pos_of_ne_top (h₀ : 0 < a) (hinf : a ≠ ⊤) : StrictMono (a * ·) := by
  intro x y hxy
  obtain rfl | hy := eq_or_ne y ⊤
  · simp [mul_top_of_pos h₀, lt_top_iff_ne_top', mul_ne_top hinf hxy.ne]
  exact mul_lt_mul_of_pos_left (α := Submonoid.notTop M)
    (a := ⟨a, by simpa [lt_top_iff_ne_top']⟩)
    (b := ⟨x, Submonoid.mem_notTop_iff.2 <| hxy.trans_le le_top⟩)
    (c := ⟨y, by simpa [lt_top_iff_ne_top']⟩) (by simpa) (by simpa)

theorem mul_left_strictMono_of_pos_of_ne_top (h₀ : 0 < a) (hinf : a ≠ ⊤) : StrictMono (· * a) := by
  simp_rw [mul_comm _ a]
  exact mul_right_strictMono_of_pos_of_ne_top h₀ hinf

end StrictMono

section Mono

variable {M : Type*} [Monoid M] [Preorder M] [OrderTop M] [MulIsTopClass M] [TopUniqueClass M]
    [IsTopMulClass M] {x y z : M}

@[to_additive (attr := to_dual)]
lemma mul_right_inj_of_ne_top [IsRightCancelMul (Submonoid.notTop M)] (hz : z ≠ ⊤) :
    x * z = y * z ↔ x = y := by
  obtain rfl | hy := eq_top_or_lt_top' y
  · simp [hz]
  obtain rfl | hx := eq_top_or_lt_top' x
  · simp [eq_comm, hz]
  rw [← lt_top_iff_ne_top'] at hz
  convert mul_left_inj (G := Submonoid.notTop M) (a := ⟨z, by simpa⟩) (b := ⟨x, by simpa⟩)
    (c := ⟨y, by simpa⟩) <;> simp

@[to_additive (attr := to_dual)]
lemma mul_left_inj_of_ne_top [IsLeftCancelMul (Submonoid.notTop M)] (hz : z ≠ ⊤) :
    z * x = z * y ↔ x = y := by
  obtain rfl | hy := eq_top_or_lt_top' y
  · simp [hz]
  obtain rfl | hx := eq_top_or_lt_top' x
  · simp [eq_comm, hz]
  rw [← lt_top_iff_ne_top'] at hz
  convert mul_right_inj (G := Submonoid.notTop M) (a := ⟨z, by simpa⟩) (b := ⟨x, by simpa⟩)
    (c := ⟨y, by simpa⟩) <;> simp

@[to_additive (attr := to_dual)]
lemma mul_right_cancel_of_ne_top [IsRightCancelMul (Submonoid.notTop M)] (hz : z ≠ ⊤)
    (h : x * z = y * z) : x = y := by
  rwa [mul_right_inj_of_ne_top hz] at h

@[to_additive (attr := to_dual)]
lemma mul_left_cancel_of_ne_top [IsLeftCancelMul (Submonoid.notTop M)] (hz : z ≠ ⊤)
    (h : z * x = z * y) : x = y := by
  rwa [mul_left_inj_of_ne_top hz] at h

@[to_additive (attr := to_dual (attr := simp))]
lemma IsLeftRegular.of_ne_top [IsCancelMul (Submonoid.notTop M)] (hx : x ≠ ⊤) : IsLeftRegular x :=
  fun _ _ ↦ mul_left_cancel_of_ne_top hx

@[to_additive (attr := to_dual (attr := simp))]
lemma IsRightRegular.of_ne_top [IsCancelMul (Submonoid.notTop M)] (hx : x ≠ ⊤) : IsRightRegular x :=
  fun _ _ ↦ mul_right_cancel_of_ne_top hx

@[to_additive (attr := to_dual)]
lemma le_of_mul_le_mul_left_of_ne_top [MulLeftReflectLE (Submonoid.notTop M)] (hx : x ≠ ⊤)
    (hle : x * y ≤ x * z) : y ≤ z := by
  obtain rfl | hy := eq_top_or_lt_top' y
  · simpa [hx] using hle
  obtain rfl | hz := eq_top_or_lt_top' z
  · simp
  rw [← lt_top_iff_ne_top'] at hx
  simpa using @le_of_mul_le_mul_left' (Submonoid.notTop M) _ _ _ ⟨x, by simpa⟩
    ⟨y, by simpa⟩ ⟨z, by simpa⟩ (by simpa)

@[to_additive (attr := to_dual)]
lemma le_of_mul_le_mul_right_of_ne_top [MulRightReflectLE (Submonoid.notTop M)] (hx : x ≠ ⊤)
    (hle : y * x ≤ z * x) : y ≤ z := by
  obtain rfl | hy := eq_top_or_lt_top' y
  · simpa [hx] using hle
  obtain rfl | hz := eq_top_or_lt_top' z
  · simp
  rw [← lt_top_iff_ne_top'] at hx
  simpa using @le_of_mul_le_mul_right' (Submonoid.notTop M) _ _ _ ⟨x, by simpa⟩
    ⟨y, by simpa⟩ ⟨z, by simpa⟩ (by simpa)

@[to_additive (attr := to_dual)]
lemma mul_lt_mul_left_of_ne_top [MulLeftStrictMono (Submonoid.notTop M)] (hx : x ≠ ⊤)
    (hyz : y < z) : x * y < x * z := by
  obtain rfl | hz := eq_top_or_lt_top' z
  · simp [lt_top_iff_ne_top', hx, hyz.ne]
  simpa using @mul_lt_mul_right (Submonoid.notTop M) _ _ _ ⟨y, by simpa using hyz.trans_le le_top⟩
    ⟨z, by simpa⟩ (by simpa) ⟨x, by simpa [lt_top_iff_ne_top']⟩

@[to_additive (attr := to_dual)]
lemma mul_lt_mul_right_of_ne_top [MulRightStrictMono (Submonoid.notTop M)] (hx : x ≠ ⊤)
    (hyz : y < z) : y * x < z * x := by
  obtain rfl | hz := eq_top_or_lt_top' z
  · simp [lt_top_iff_ne_top', hx, hyz.ne]
  simpa using @mul_lt_mul_left (Submonoid.notTop M) _ _ _ ⟨y, by simpa using hyz.trans_le le_top⟩
    ⟨z, by simpa⟩ (by simpa) ⟨x, by simpa [lt_top_iff_ne_top']⟩

@[to_dual]
instance [MulLeftMono (Submonoid.notTop M)] : MulLeftMono M := by
  refine ⟨@fun x y z hyz ↦ ?_⟩
  obtain rfl | hx := eq_top_or_lt_top' x
  · simp
  obtain rfl | hz := eq_top_or_lt_top' z
  · simp
  sorry
  -- simpa using @mul_le_mul_right (Submonoid.notTop M) _ _ _ ⟨y, by simpa using hyz.trans_lt hz⟩
  --   ⟨z, by simpa⟩ (by simpa) ⟨x, by simpa⟩

instance [MulRightMono (Submonoid.notTop M)] : MulRightMono M := by
  refine ⟨@fun x y z hyz ↦ ?_⟩
  obtain rfl | hx := eq_top_or_lt_top' x
  · simp [Function.swap]
  obtain rfl | hz := eq_top_or_lt_top' z
  · simp [Function.swap]
  simpa using @mul_le_mul_left (Submonoid.notTop M) _ _ _ ⟨y, by simpa using hyz.trans_lt hz⟩
    ⟨z, by simpa⟩ (by simpa) ⟨x, by simpa⟩

@[gcongr]
theorem mul_lt_mul''' [MulLeftStrictMono (Submonoid.notTop M)]
    [MulRightStrictMono (Submonoid.notTop M)] {w : M}
    (xz : x < z) (yw : y < w) : x * y < z * w := by
  obtain rfl | hz := eq_top_or_lt_top' z
  · simp [lt_top_iff_ne_top', xz.ne, (yw.trans_le le_top).ne]
  refine lt_of_le_of_lt ?_ <| mul_lt_mul_left_of_ne_top hz.ne yw
  obtain rfl | hy := eq_top_or_lt_top' y
  · simp
  exact (mul_lt_mul_right_of_ne_top hy.ne xz).le


  -- have : MulLeftMono (Submonoid.notTop M) := by exact?

  -- apply (WithTop.add_lt_add_left xz.ne_top yw).trans_le
  -- cases w
  -- · simp
  -- · exact (WithTop.add_lt_add_right coe_ne_top xz).le

-- protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x ≠ ⊤) :
--     x + y ≤ x + z ↔ y ≤ z := ⟨WithTop.le_of_add_le_add_left hx, fun _ ↦ by gcongr⟩



@[to_additive (attr := to_dual)]
lemma mul_le_mul_iff_left_of_ne_top' (hx : x ≠ ⊤) : x * y ≤ x * z ↔ y ≤ z := by
  obtain rfl | hy := eq_or_ne y ⊤
  · simp [hx]
  obtain rfl | hz := eq_or_ne z ⊤
  · simp
  rw [← lt_top_iff_ne_top'] at hx hy hz
  have hwin := mul_le_mul_iff_left (α := Submonoid.notTop M) ⟨x, by simpa⟩ (b := ⟨y, by simpa⟩)
    (c := ⟨z, by simpa⟩)
  simp only [Subtype.mk_le_mk] at hwin
  simp_rw [← hwin, Submonoid.mk_mul_mk, Subtype.mk_le_mk]

@[to_additive (attr := to_dual)]
lemma mul_le_mul_iff_right_of_ne_top' (hx : x ≠ ⊤) : y * x ≤ z * x ↔ y ≤ z := by
  rw [← mul_comm, mul_comm z, mul_le_mul_iff_left_of_ne_top' hx]

@[to_additive (attr := to_dual)]
lemma mul_lt_mul_iff_right_of_ne_top' (hx : x ≠ ⊤) : y * x < z * x ↔ y < z := by
  simp_rw [lt_iff_le_not_ge, mul_le_mul_iff_right_of_ne_top' hx]

@[to_additive (attr := to_dual)]
lemma mul_lt_mul_iff_left_of_ne_top' (hx : x ≠ ⊤) : x * y < x * z ↔ y < z := by
  simp_rw [mul_comm x, mul_lt_mul_iff_right_of_ne_top' hx]

end Mono

section Archimedean

variable {M : Type*} [CommMonoid M] [PartialOrder M] [OrderTop M] [MulIsTopClass M] {x y z : M}

@[to_additive]
theorem exists_le_pow_of_ne_top [MulArchimedean (Submonoid.notTop M)] (hx : 1 < x)
    (hy : y ≠ ⊤) : ∃ n, y ≤ x ^ n := by
  obtain rfl | hne := eq_or_ne x ⊤
  · exact ⟨1, by simp⟩
  rw [← lt_top_iff_ne_top'] at hy hne
  exact Exists.imp (fun n ↦ by simp [← Subtype.coe_le_coe])
    <| MulArchimedean.arch (R := Submonoid.notTop M) (y := ⟨x, by simpa⟩) (x := ⟨y, by simpa⟩) hx

@[to_additive]
theorem exists_lt_pow_of_ne_top [MulArchimedean (Submonoid.notTop M)]
    [MulLeftStrictMono (Submonoid.notTop M)] (hx : 1 < x) (hy : y ≠ ⊤) :
    ∃ n, y < x ^ n := by
  obtain rfl | hne := eq_or_ne x ⊤
  · refine ⟨1, ?_⟩
    grw [pow_one, lt_top_iff_ne_top]
    exact hy
  rw [← lt_top_iff_ne_top'] at hy hne
  exact Exists.imp (fun n ↦ by simp [← Subtype.coe_lt_coe]) <| exists_lt_pow
    (R := Submonoid.notTop M) (a := ⟨x, by simpa⟩) hx ⟨y, by simpa⟩

end Archimedean



#exit

/- ### FROM WITHTOP-/



protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z ≠ ⊤) :
    x + z ≤ y + z ↔ x ≤ y := ⟨WithTop.le_of_add_le_add_right hz, fun _ ↦ by gcongr⟩

protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x ≠ ⊤) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left hx⟩

protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z ≠ ⊤) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right hz⟩

protected theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w ≠ ⊤) (hwy : w ≤ y) (hxz : x < z) :
    w + x < y + z :=
  (WithTop.add_lt_add_left hw hxz).trans_le <| by gcongr

protected theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x ≠ ⊤) (hwy : w < y) (hxz : x ≤ z) :
    w + x < y + z :=
  (WithTop.add_lt_add_right hx hwy).trans_le <| by gcongr

lemma addLECancellable_of_ne_top [LE α] [AddLeftReflectLE α]
    (hx : x ≠ ⊤) : AddLECancellable x := fun _b _c ↦ WithTop.le_of_add_le_add_left hx

lemma addLECancellable_of_lt_top [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊤) : AddLECancellable x := addLECancellable_of_ne_top hx.ne

lemma addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithTop α) := addLECancellable_of_ne_top coe_ne_top

lemma addLECancellable_iff_ne_top [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x ≠ ⊤ where
  mp := by rintro h rfl; exact (coe_lt_top <| Classical.arbitrary _).not_ge <| h <| by simp
  mpr := addLECancellable_of_ne_top

/- ### FROM ADDGROUPWITHTOP-/


@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

@[simp] lemma IsAddRegular.of_ne_top (ha : a ≠ ⊤) : IsAddRegular a := by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha

lemma add_left_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ x + b) :=
  (IsAddRegular.of_ne_top h).2

lemma add_right_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ b + x) :=
  (IsAddRegular.of_ne_top h).1

@[simp]
lemma add_left_inj_of_ne_top (h : a ≠ ⊤) : b + a = c + a ↔ b = c :=
  (add_left_injective_of_ne_top _ h).eq_iff

@[simp]
lemma add_right_inj_of_ne_top (h : a ≠ ⊤) : a + b = a + c ↔ b = c :=
  (add_right_injective_of_ne_top _ h).eq_iff

lemma add_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ x + b) :=
  add_left_mono.strictMono_of_injective <| add_left_injective_of_ne_top _ h

lemma add_right_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ b + x) :=
  add_right_mono.strictMono_of_injective <| add_right_injective_of_ne_top _ h

@[simp]
lemma add_le_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
  (add_left_strictMono_of_ne_top h).le_iff_le

@[simp]
lemma add_le_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
  (add_right_strictMono_of_ne_top h).le_iff_le

@[simp]
lemma add_lt_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a < c + a ↔ b < c :=
  (add_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
lemma add_lt_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b < a + c ↔ b < c :=
  (add_right_strictMono_of_ne_top h).lt_iff_lt


-- section WithTop

-- section Monoid

-- instance [DecidableEq M] [CommMonoidWithZero M] [Preorder M] : MulEqTopClass (WithTop M) where
--   one_ne_top := WithTop.one_ne_top
--   eq_or_eq_of_mul a b := by
--     match a, b with
--     | ⊤, _ => simp
--     | _, ⊤ => simp
--     | (a : M), (b : M) => exact fun h ↦ False.elim <| by norm_cast at h

-- instance [AddCommMonoid M] [Preorder M] : AddEqTopClass (WithTop M) where
--   zero_ne_top := WithTop.zero_ne_top
--   eq_or_eq_of_add := by simp

-- instance [Mul M] [Top M] [One M] [MulEqTopClass M] : Nontrivial M where
--   exists_pair_ne := ⟨1, ⊤, one_ne_top⟩

-- /-- The submonoid of non-top elements in `WithTop M` is isomorphic to `M`. -/
-- def orderAddMonoidIsoNeTop (M : Type*) [AddCommMonoid M] [Preorder M] :
--     (AddSubmonoid.neTop (WithTop M)) ≃+o M where
--   toFun x := WithTop.untop x.1 x.2
--   invFun x := ⟨x, by simp [AddSubmonoid.neTop]⟩
--   left_inv x := by simp
--   right_inv x := by simp
--   map_add' x y := by
--     match x, y with
--     | ⟨⊤, h⟩, _ => simp [AddSubmonoid.neTop] at h
--     | _, ⟨⊤, h⟩ => simp [AddSubmonoid.neTop] at h
--     | ⟨(x : M), hx⟩, ⟨(y : M), hy⟩ => norm_cast
--   map_le_map_iff' := by simp

-- instance [AddCommMonoid M] [IsCancelAdd M] [Preorder M] :
--     IsCancelAdd (AddSubmonoid.neTop (WithTop M)) := by
--   refine @AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _ _ ⟨fun a b c ↦ ?_⟩
--   rw [← EquivLike.apply_eq_iff_eq (f := orderAddMonoidIsoNeTop M)]
--   simp

-- instance [AddCommMonoid M] [Preorder M] [IsOrderedCancelAddMonoid M] :
--     IsOrderedCancelAddMonoid (AddSubmonoid.neTop (WithTop M)) where
--   add_le_add_left a b hab c := by
--     rw [← map_le_map_iff (f := (orderAddMonoidIsoNeTop M))]
--     simpa
--   le_of_add_le_add_left a b c hle := by
--     rw [← map_le_map_iff (f := (orderAddMonoidIsoNeTop M))] at hle ⊢
--     simpa using hle

-- end Monoid

-- section Ring

-- variable {R : Type*} [DecidableEq R] [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
--     [NoZeroDivisors R] [Nontrivial R]

-- instance : MulEqTopClass (WithTop R) where
--   one_ne_top := WithTop.one_ne_top
--   eq_or_eq_of_mul a b hab :=
--     match a, b with
--     | ⊤, _ => by simp
--     | _, ⊤ => by simp
--     | (a : R), (b : R) => by simp [← WithTop.coe_mul] at hab

-- /-- The subring of non-top elements in `WithTop R` is isomorphic to `R`. -/
-- def orderRingIsoNeTop (R : Type*) [DecidableEq R] [Semiring R] [PartialOrder R]
--     [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R] :
--     Subsemiring.neTop (WithTop R) ≃+*o R where
--   invFun x := ⟨x, by simp [Subsemiring.neTop]⟩
--   toFun x := WithTop.untop x.1 x.2
--   left_inv x := by simp
--   right_inv x := by simp
--   map_mul' x y := by
--     match x, y with
--     | ⟨⊤, h⟩, _ => simp [Subsemiring.neTop] at h
--     | _, ⟨⊤, h⟩ => simp [Subsemiring.neTop] at h
--     | ⟨(x : R), hx⟩, ⟨(y : R), hy⟩ => norm_cast
--   map_add' x y := by
--     match x, y with
--     | ⟨⊤, h⟩, _ => simp [Subsemiring.neTop] at h
--     | _, ⟨⊤, h⟩ => simp [Subsemiring.neTop] at h
--     | ⟨(x : R), hx⟩, ⟨(y : R), hy⟩ => norm_cast
--   map_le_map_iff' := by simp

-- end Ring

-- end WithTop
