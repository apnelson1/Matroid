import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Order.Atoms
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Order.AddGroupWithTop

variable {M α : Type*} {a b : α}

/-- A class for the property that `0 ≠ ⊤`. -/
class ZeroNeTopClass (M : Type*) [Zero M] [Top M] : Prop where
  protected zero_ne_top : (0 : M) ≠ ⊤

/-- A class for the property that `1 ≠ ⊤`. -/
@[to_additive]
class OneNeTopClass (M : Type*) [One M] [Top M] : Prop where
  protected one_ne_top : (1 : M) ≠ ⊤

@[to_additive, simp]
lemma one_ne_top [One M] [Top M] [OneNeTopClass M] : (1 : M) ≠ ⊤ :=
  OneNeTopClass.one_ne_top

/-- An `AddEqTopClass` is one where the top element is nonzero, and is not the sum of two
non-top elements. Equivalently, the non-top elements are an additive submonoid. -/
class AddEqTopClass (M : Type*) [Zero M] [Add M] [Top M] : Prop extends ZeroNeTopClass M where
  protected eq_or_eq_of_add (a b : M) : a + b = ⊤ → a = ⊤ ∨ b = ⊤

/-- A `MulEqTopClass` is one where the top element is not `1`, and is not the product of two
non-top elements. Equivalently, the non-top elements are a submonoid. -/
@[to_additive]
class MulEqTopClass (M : Type*) [One M] [Mul M] [Top M] : Prop extends OneNeTopClass M where
  protected eq_or_eq_of_mul (a b : M) : a * b = ⊤ → a = ⊤ ∨ b = ⊤

@[to_additive]
lemma mul_ne_top [One M] [Mul M] [Top M] [MulEqTopClass M] {a b : M} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a * b ≠ ⊤ :=
  fun h ↦ (MulEqTopClass.eq_or_eq_of_mul a b h).elim ha hb

@[to_additive]
lemma eq_or_eq_of_mul_eq_top [One M] [Mul M] [Top M] [MulEqTopClass M] {a b : M} (h : a * b = ⊤) :
    a = ⊤ ∨ b = ⊤ :=
  MulEqTopClass.eq_or_eq_of_mul _ _ h

@[to_additive]
lemma exists_of_prod_eq_top [CommMonoid M] [Top M] [MulEqTopClass M] {s : Finset α} {f : α → M}
    (h : ∏ x ∈ s, f x = ⊤) : ∃ x, f x = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert a s has ih =>
    rw [Finset.prod_insert has] at h
    obtain (ha | hs) := eq_or_eq_of_mul_eq_top h
    · exact ⟨a, ha⟩
    exact ih hs

/-- The set of non-top elements in a `MulEqTopClass` is a submonoid. -/
@[to_additive, simps]
def Submonoid.neTop (M : Type*) [Monoid M] [Top M] [MulEqTopClass M] :
    Submonoid M where
  carrier := {x | x ≠ ⊤}
  mul_mem' := mul_ne_top
  one_mem' := one_ne_top

/-- A mixin class for the property that `⊤` is additively absorbing. -/
class AddTopClass (M : Type*) [Add M] [Top M] : Prop where
  protected add_top (a : M) : a + ⊤ = ⊤
  protected top_add (a : M) : ⊤ + a = ⊤

/-- A mixin class for the property that `⊤` is multiplicatively absorbing. -/
@[to_additive]
class MulTopClass (M : Type*) [Mul M] [Top M] : Prop where
  protected mul_top (a : M) : a * ⊤ = ⊤
  protected top_mul (a : M) : ⊤ * a = ⊤

/-- A mixin class for the property that `⊤` multiplicatively absorbs positive elements. -/
class PosMulTopClass (M : Type*) [Zero M] [Top M] [Mul M] [LT M] : Prop where
  protected mul_top_of_pos {a : M} (ha : 0 < a) : a * ⊤ = ⊤
  protected top_mul_of_pos {a : M} (ha : 0 < a) : ⊤ * a = ⊤

lemma mul_top_of_pos {M : Type*} [Zero M] [Top M] [Mul M] [LT M] [PosMulTopClass M] {a : M}
    (ha : 0 < a) : a * ⊤ = ⊤ := PosMulTopClass.mul_top_of_pos ha

lemma top_mul_of_pos {M : Type*} [Zero M] [Top M] [Mul M] [LT M] [PosMulTopClass M] {a : M}
    (ha : 0 < a) : ⊤ * a = ⊤ := PosMulTopClass.top_mul_of_pos ha

@[to_additive, simp]
lemma mul_top' [Mul M] [Top M] [MulTopClass M] (a : M) : a * ⊤ = ⊤ :=
  MulTopClass.mul_top a

@[to_additive, simp]
lemma top_mul' [Mul M] [Top M] [MulTopClass M] (a : M) : ⊤ * a = ⊤ :=
  MulTopClass.top_mul a

instance [Zero M] [Top M] [Mul M] [LT M] [MulTopClass M] : PosMulTopClass M where
  mul_top_of_pos _ := mul_top' ..
  top_mul_of_pos _ := top_mul' ..

@[to_additive, simp]
lemma mul_eq_top_iff [One M] [Mul M] [Top M] [MulTopClass M] [MulEqTopClass M] {a b : M} :
    a * b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  ⟨eq_or_eq_of_mul_eq_top, by rintro (rfl | rfl) <;> simp⟩

/-- The set of non-top elements in a ring with `MulEqTopClass`, `AddEqTopClass` is a subring. -/
@[simps]
def Subsemiring.neTop (α : Type*) [DecidableEq α] [Semiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] [NoZeroDivisors α] [OrderTop α] [MulEqTopClass α] [AddEqTopClass α] :
    Subsemiring α where
  carrier := {x | x ≠ ⊤}
  mul_mem' := mul_ne_top
  one_mem' := one_ne_top
  add_mem' := add_ne_top
  zero_mem' := zero_ne_top

section instances

instance {M : Type*} [LinearOrderedAddCommMonoidWithTop M] : AddTopClass M where
  add_top := add_top
  top_add := top_add

instance {M : Type*} [LinearOrderedAddCommMonoidWithTop M] [Nontrivial M] : AddEqTopClass M where
  zero_ne_top := by
    obtain ⟨b, hb⟩ := exists_ne (⊤ : M)
    contrapose! hb
    rw [← zero_add b, hb, top_add]
  eq_or_eq_of_add a b hab := by
    contrapose! hab
    simpa using (add_right_strictMono_of_ne_top hab.1 (lt_top_iff_ne_top.2 hab.2)).ne

instance {M : Type*} [CommMonoidWithZero M] [Preorder M] [OrderTop M] [MulEqTopClass M]
    [ZeroNeTopClass M] : CommMonoidWithZero (Submonoid.neTop M) where
  zero := ⟨0, zero_ne_top⟩
  zero_mul a := Subtype.val_inj.1 <| zero_mul a.1
  mul_zero a := Subtype.val_inj.1 <| mul_zero a.1

end instances

section lemmas

variable {M : Type*} [CommMonoid M] [PartialOrder M] [OrderTop M] [MulEqTopClass M] [MulTopClass M]
    {x y z : M}

@[to_additive]
lemma isRegular_of_ne_top [IsCancelMul (Submonoid.neTop M)] (hx : x ≠ ⊤) : IsRegular x := by
  rw [← isLeftRegular_iff_isRegular]
  intro y z (hyz : x * y = x * z)
  obtain rfl | hy := eq_or_ne y ⊤
  · simpa [eq_comm, hx] using hyz
  obtain rfl | hz := eq_or_ne z ⊤
  · simp [hx, hy] at hyz
  have hwin := mul_right_inj (G := Submonoid.neTop M) (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) (c := ⟨z, hz⟩)
  simp_rw [Subtype.mk_eq_mk, (Submonoid.neTop M).mk_mul_mk _ _ hx hy,
    (Submonoid.neTop M).mk_mul_mk _ _ hx hz, Subtype.mk.injEq] at hwin
  exact hwin.1 hyz

@[to_additive]
lemma mul_le_mul_iff_left_of_ne_top' [IsOrderedCancelMonoid (Submonoid.neTop M)] (hx : x ≠ ⊤) :
    x * y ≤ x * z ↔ y ≤ z := by
  obtain rfl | hy := eq_or_ne y ⊤
  · simp [hx]
  obtain rfl | hz := eq_or_ne z ⊤
  · simp
  have hwin := mul_le_mul_iff_left (α := Submonoid.neTop M) ⟨x, hx⟩ (b := ⟨y, hy⟩) (c := ⟨z, hz⟩)
  simp only [Subtype.mk_le_mk] at hwin
  rw [← hwin]
  rfl

@[to_additive]
lemma mul_le_mul_iff_right_of_ne_top' [IsOrderedCancelMonoid (Submonoid.neTop M)] (hx : x ≠ ⊤) :
    y * x ≤ z * x ↔ y ≤ z := by
  rw [← mul_comm, mul_comm z, mul_le_mul_iff_left_of_ne_top' hx]

@[to_additive]
lemma mul_lt_mul_iff_right_of_ne_top' [IsOrderedCancelMonoid (Submonoid.neTop M)] (hx : x ≠ ⊤) :
    y * x < z * x ↔ y < z := by
  simp_rw [lt_iff_le_and_ne, mul_le_mul_iff_right_of_ne_top' hx, Ne,
    (isRegular_of_ne_top hx).right.eq_iff]

@[to_additive]
lemma mul_lt_mul_iff_left_of_ne_top' [IsOrderedCancelMonoid (Submonoid.neTop M)] (hx : x ≠ ⊤) :
    x * y < x * z ↔ y < z := by
  simp_rw [mul_comm x, mul_lt_mul_iff_right_of_ne_top' hx]

theorem mul_right_strictMono_of_pos_of_ne_top {M : Type*} [CommMonoidWithZero M] [PartialOrder M]
    [OrderTop M] [MulEqTopClass M] [ZeroNeTopClass M] [PosMulTopClass M]
    [PosMulStrictMono (Submonoid.neTop M)] {a : M} (h₀ : 0 < a) (hinf : a ≠ ⊤) :
    StrictMono (a * ·) := by
  intro x y hxy
  obtain rfl | hy := eq_or_ne y ⊤
  · simp [mul_top_of_pos h₀, lt_top_iff_ne_top, mul_ne_top hinf hxy.ne]
  exact mul_lt_mul_of_pos_left (α := Submonoid.neTop M) (a := ⟨a, hinf⟩)
    (b := ⟨x, (lt_top_of_lt hxy).ne⟩) (c := ⟨y, hy⟩) (by simpa) (by simpa)

theorem mul_left_strictMono_of_pos_of_ne_top {M : Type*} [CommMonoidWithZero M] [PartialOrder M]
    [OrderTop M] [MulEqTopClass M] [ZeroNeTopClass M] [PosMulTopClass M]
    [PosMulStrictMono (Submonoid.neTop M)] {a : M} (h₀ : 0 < a) (hinf : a ≠ ⊤) :
    StrictMono (· * a) := by
  simp_rw [mul_comm _ a]
  exact mul_right_strictMono_of_pos_of_ne_top h₀ hinf

@[simp]
theorem mul_lt_mul_iff_left₀_of_ne_top {M : Type*} [CommMonoidWithZero M] [LinearOrder M]
    [OrderTop M] [MulEqTopClass M] [ZeroNeTopClass M] [PosMulTopClass M]
    [PosMulStrictMono (Submonoid.neTop M)] {a b c : M} (a0 : 0 < a) (ha : a ≠ ⊤) :
    b * a < c * a ↔ b < c :=
  (mul_left_strictMono_of_pos_of_ne_top a0 ha).lt_iff_lt

@[simp]
theorem mul_lt_mul_iff_right₀_of_ne_top {M : Type*} [CommMonoidWithZero M] [LinearOrder M]
    [OrderTop M] [MulEqTopClass M] [ZeroNeTopClass M] [PosMulTopClass M]
    [PosMulStrictMono (Submonoid.neTop M)] {a b c : M} (a0 : 0 < a) (ha : a ≠ ⊤) :
    a * b < a * c ↔ b < c :=
  (mul_right_strictMono_of_pos_of_ne_top a0 ha).lt_iff_lt

end lemmas

section WithTop

section Monoid

instance [DecidableEq M] [CommMonoidWithZero M] [Preorder M] : MulEqTopClass (WithTop M) where
  one_ne_top := WithTop.one_ne_top
  eq_or_eq_of_mul a b := by
    match a, b with
    | ⊤, _ => simp
    | _, ⊤ => simp
    | (a : M), (b : M) => exact fun h ↦ False.elim <| by norm_cast at h

instance [AddCommMonoid M] [Preorder M] : AddEqTopClass (WithTop M) where
  zero_ne_top := WithTop.zero_ne_top
  eq_or_eq_of_add := by simp

instance [Mul M] [Top M] [One M] [MulEqTopClass M] : Nontrivial M where
  exists_pair_ne := ⟨1, ⊤, one_ne_top⟩

/-- The submonoid of non-top elements in `WithTop M` is isomorphic to `M`. -/
def orderAddMonoidIsoNeTop (M : Type*) [AddCommMonoid M] [Preorder M] :
    (AddSubmonoid.neTop (WithTop M)) ≃+o M where
  toFun x := WithTop.untop x.1 x.2
  invFun x := ⟨x, by simp [AddSubmonoid.neTop]⟩
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    match x, y with
    | ⟨⊤, h⟩, _ => simp [AddSubmonoid.neTop] at h
    | _, ⟨⊤, h⟩ => simp [AddSubmonoid.neTop] at h
    | ⟨(x : M), hx⟩, ⟨(y : M), hy⟩ => norm_cast
  map_le_map_iff' := by simp

instance [AddCommMonoid M] [IsCancelAdd M] [Preorder M] :
    IsCancelAdd (AddSubmonoid.neTop (WithTop M)) := by
  refine @AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _ _ ⟨fun a b c ↦ ?_⟩
  rw [← EquivLike.apply_eq_iff_eq (f := orderAddMonoidIsoNeTop M)]
  simp

instance [AddCommMonoid M] [Preorder M] [IsOrderedCancelAddMonoid M] :
    IsOrderedCancelAddMonoid (AddSubmonoid.neTop (WithTop M)) where
  add_le_add_left a b hab c := by
    rw [← map_le_map_iff (f := (orderAddMonoidIsoNeTop M))]
    simpa
  le_of_add_le_add_left a b c hle := by
    rw [← map_le_map_iff (f := (orderAddMonoidIsoNeTop M))] at hle ⊢
    simpa using hle

end Monoid

section Ring

variable {R : Type*} [DecidableEq R] [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
    [NoZeroDivisors R] [Nontrivial R]

instance : MulEqTopClass (WithTop R) where
  one_ne_top := WithTop.one_ne_top
  eq_or_eq_of_mul a b hab :=
    match a, b with
    | ⊤, _ => by simp
    | _, ⊤ => by simp
    | (a : R), (b : R) => by simp [← WithTop.coe_mul] at hab

/-- The subring of non-top elements in `WithTop R` is isomorphic to `R`. -/
def orderRingIsoNeTop (R : Type*) [DecidableEq R] [Semiring R] [PartialOrder R]
    [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R] :
    Subsemiring.neTop (WithTop R) ≃+*o R where
  invFun x := ⟨x, by simp [Subsemiring.neTop]⟩
  toFun x := WithTop.untop x.1 x.2
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    match x, y with
    | ⟨⊤, h⟩, _ => simp [Subsemiring.neTop] at h
    | _, ⟨⊤, h⟩ => simp [Subsemiring.neTop] at h
    | ⟨(x : R), hx⟩, ⟨(y : R), hy⟩ => norm_cast
  map_add' x y := by
    match x, y with
    | ⟨⊤, h⟩, _ => simp [Subsemiring.neTop] at h
    | _, ⟨⊤, h⟩ => simp [Subsemiring.neTop] at h
    | ⟨(x : R), hx⟩, ⟨(y : R), hy⟩ => norm_cast
  map_le_map_iff' := by simp

end Ring

end WithTop
