import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.FunLike.Basic
import Batteries.CodeAction.Misc
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel


set_option linter.style.longLine false

@[simp]
lemma ZMod.finEquiv_zero (n : ℕ) [NeZero n] : ZMod.finEquiv n 0 = 0 := by
  simp [ZMod.finEquiv]

@[simp]
lemma ZMod.finEquiv_one (n : ℕ) [NeZero n] : ZMod.finEquiv n 1 = 1 := by
  simp [ZMod.finEquiv]

@[simp]
lemma ZMod.finEquiv_ofNat (n a : ℕ) [NeZero n] [a.AtLeastTwo] : ZMod.finEquiv n ofNat(a) = a := by
  cases n with
  | zero => grind only
  | succ n => rfl

lemma ZMod.exists_equiv_three {i j k : ZMod 3} (hijk : [i, j, k].Nodup) :
    ∃ e : ZMod 3 ≃ ZMod 3, e 0 = i ∧ e 1 = j ∧ e 2 = k := by
  obtain ⟨⟨hij : i ≠ j, hik : i ≠ k⟩, hjk : j ≠ k⟩ := by simpa using hijk
  set e : ZMod 3 ↪ ZMod 3 := {
    toFun := ![i, j, k]
    inj' := by
      simp [Function.Injective, (ZMod.finEquiv 3).symm.forall_congr_left, Fin.forall_fin_succ, hij,
        hik, hij.symm, hjk, hik.symm, hjk.symm]}
  have hbij : Function.Bijective e := by
    rw [Fintype.bijective_iff_injective_and_card]
    simp [e.injective]
  exact ⟨Equiv.ofBijective _ hbij, rfl, rfl, rfl⟩


lemma prod_zmod_three {G : Type*} [CommMonoid G] (f : ZMod 3 → G) :
    ∏ (i : ZMod 3), f i = f 0 * f 1 * f 2 := by
  simp only [Finset.prod, ZMod, Nat.reduceAdd, Fin.univ_val_map, List.ofFn_succ, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, List.ofFn_zero, Multiset.prod_coe, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]
  rfl

lemma prod_zmod_three' {i j k : ZMod 3} {G : Type*} [CommMonoid G] (f : ZMod 3 → G)
    (hijk : [i, j, k].Nodup) : ∏ (i : ZMod 3), f i = f i * f j * f k := by
  obtain ⟨e, rfl, rfl, rfl⟩ := ZMod.exists_equiv_three hijk
  rw [← e.prod_comp, prod_zmod_three]

lemma forall_zmod_three (P : ZMod 3 → Prop) : (∀ (i : ZMod 3), P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  change (∀ i : Fin 3, P i) ↔ _
  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    IsEmpty.forall_iff, and_true]
  rfl

-- @[simp]
-- lemma prod_zmod_three' {a b c : G} : ∏ (i : ZMod 3), ![a, b, c] i = a * b * c := by
--   simp [ZMod, mul_assoc, Finset.prod]

open Set

variable {G H : Type*} [CommGroup G] [CommGroup H] {i j k : ZMod 3}

structure FunTrio (G H : Type*) [CommGroup G] [CommGroup H] where
  toFun : ZMod 3 → G → H
  support : ZMod 3 → Set G
  prod_eq_one (x : ZMod 3 → G) (hmul : ∏ i, x i = 1) (hsupp : ∀ i, x i ∈ support i) :
    ∏ i, (toFun i (x i)) = 1


namespace FunTrio

attribute [coe] FunTrio.toFun


instance : CoeFun (FunTrio G H) (fun _ ↦ (ZMod 3 → (G → H))) where
  coe φ := φ.toFun

-- lemma coe_apply (φ : FunTrio G H) (i : ZMod 3) (x : G) : φ i x = (φ.toFun i x).elim 1 id := rfl

variable {φ : FunTrio G H} {x y z : G} {a b c : H}

@[simps]
protected def comp (φ : FunTrio G H) (e : ZMod 3 ≃ ZMod 3) : FunTrio G H where
  toFun i := φ (e i)
  support i := φ.support (e i)
  prod_eq_one x hx h := by
    rw [← e.symm.prod_comp] at hx
    rw [← φ.prod_eq_one _ hx, eq_comm, ← e.prod_comp]
    · simp
    rw [e.symm.forall_congr_left]
    simpa

@[simps]
def comp' (φ : FunTrio G H) (e : ZMod 3 ↪ ZMod 3)  : FunTrio G H where
  toFun i := φ (e i)
  support i := φ.support (e i)
  prod_eq_one x hx h := by
    classical
    have hbij : Function.Bijective e := by
      rw [Fintype.bijective_iff_injective_and_card]
      simp [e.injective]
    exact (φ.comp (Equiv.ofBijective _ hbij)).prod_eq_one x hx h

@[simps]
def rotate (φ : FunTrio G H) (d : ZMod 3) : FunTrio G H where
  toFun i := φ (i + d)
  support i := φ.support (i + d)
  prod_eq_one x hx hsupp := by
    rw [← Equiv.prod_comp (Equiv.subRight d)] at hx
    rw [← φ.prod_eq_one _ hx (fun i ↦ by simpa using hsupp (i - d)),
      eq_comm, ← Equiv.prod_comp (Equiv.addRight d)]
    simp

@[simps]
def scaleRight (φ : FunTrio G H) (a : ZMod 3 → H) (ha : ∏ i, a i = 1) : FunTrio G H where
  toFun i x := a i * φ i x
  support := φ.support
  prod_eq_one x hx hsupp := by
    rw [Finset.prod_mul_distrib, ha, one_mul, φ.prod_eq_one _ hx hsupp]

@[simps!]
def scale (φ : FunTrio G H) (u : ZMod 3 → G) (hu : ∀ i, u i ∈ φ.support i) (hu1 : ∏ i, u i = 1) :
    FunTrio G H :=
  φ.scaleRight (fun i ↦ φ i (u i)) (by rw [φ.prod_eq_one _ hu1 hu])

@[simps]
def scaleLeft (φ : FunTrio G H) (u : ZMod 3 → G) (hu1 : ∏ i, u i = 1) : FunTrio G H where
  toFun i x := φ i (u i * x)
  support i := (u i * ·) ⁻¹' φ.support i
  prod_eq_one x hx h := φ.prod_eq_one _ (by rw [Finset.prod_mul_distrib, hu1, hx, mul_one])
    (by simpa using h)


lemma mul_eq_one (φ : FunTrio G H) {x y z : G} (hx : x ∈ φ.support 0) (hy : y ∈ φ.support 1)
    (hz : z ∈ φ.support 2) (h1 : x * y * z = 1) : φ 0 x * φ 1 y * φ 2 z = 1 := by
  rw [← φ.prod_eq_one ![x,y,z]]
  · rw [← (ZMod.finEquiv 3).toEquiv.prod_comp]
    simp [Finset.prod, mul_assoc]
  · rw [← (ZMod.finEquiv 3).toEquiv.prod_comp]
    simpa [Finset.prod, ← mul_assoc]
  intro i
  match i with | 0 => assumption | 1 => assumption | 2 => assumption

lemma mul_eq_one' (φ : FunTrio G H) (hijk : [i, j, k].Nodup) (hx : x ∈ φ.support i)
    (hy : y ∈ φ.support j) (hz : z ∈ φ.support k) (h1 : x * y * z = 1) :
    φ i x * φ j y * φ k z = 1 := by
  obtain ⟨e, rfl, rfl, rfl⟩ := ZMod.exists_equiv_three hijk
  exact (φ.comp e).mul_eq_one (x := x) (y := y) (z := z) (by simpa) (by simpa) (by simpa) h1

def IsHom (φ : FunTrio G H) : Prop := ∃ (f : G →* H), ∀ i, EqOn (φ i) f (φ.support i)

/-- a trio `IsNormal` if each of its functions maps the identity to the identity. -/
@[mk_iff]
structure IsNormal (φ : FunTrio G H) : Prop where
  mem {i : ZMod 3} : 1 ∈ φ.support i
  eq_one {i : ZMod 3} : φ i 1 = 1

def normalize (φ : FunTrio G H) (a : ZMod 3 → G) (ha : ∀ i, a i ∈ φ.support i)
    (ha1 : ∏ i, a i = 1) : FunTrio G H :=
  (φ.scaleLeft (fun i ↦ (a i)) (by simp [ha1])).scaleRight
    (fun i ↦ (φ i (a i))⁻¹) <| by simpa using φ.prod_eq_one a ha1 ha

lemma normalize_isNormal (φ : FunTrio G H) (a : ZMod 3 → G) (ha : ∀ i, a i ∈ φ.support i)
    (ha1 : ∏ i, a i = 1) : (φ.normalize a ha ha1).IsNormal :=
  ⟨by simpa [normalize], by simp [normalize]⟩

@[simp]
lemma IsNormal.comp (hφ : φ.IsNormal) (e : ZMod 3 ≃ ZMod 3) : (φ.comp e).IsNormal := by
  simp [isNormal_iff, hφ.mem, hφ.eq_one]


  -- have := φ.scaleLeft ![]

    -- (h2 : φ.support 2 = univ) : ∃ (φ' : FunTrio G H), φ'.IsNormal ∧ φ'.support 0 = {a}ᶜ
    -- ∧ ]





-- lemma IsNormal.foo (hφ : φ.IsNormal) (x : G) (h0 : x ∈ φ.support 0) (h1 : x ∈ φ.support 1)
--     (h2 : x⁻¹ ∈ φ.support 2) : φ 0 x = φ 1 x := by
--   have h := φ.mul_eq_one hφ.mem h1 h2 (by simp)
--   have h' := φ.mul_eq_one h0 hφ.mem h2 (by simp)
--   simp only [hφ.eq_one, one_mul, mul_one, mul_eq_one_iff_eq_inv] at h h'
--   rw [h, h']

-- If `φ 0` and `φ 1` agree on some `y`, and `x` is an element supported by both such that
-- `x⁻¹ * y⁻¹` is supported by `φ 2`, then `φ 0` and `φ 1` agree on `x`.
protected lemma eq_of_eq₀ (φ : FunTrio G H) (hx0 : x ∈ φ.support 0) (hx1 : x ∈ φ.support 1)
    (hy0 : y ∈ φ.support 0) (hy1 : y ∈ φ.support 1) (heq : φ 0 y = φ 1 y)
    (h2 : y⁻¹ * x⁻¹ ∈ φ.support 2) : φ 0 x = φ 1 x := by
  have h₁ := φ.mul_eq_one hx0 hy1 h2 (by simp [mul_assoc])
  have h₂ := φ.mul_eq_one hy0 hx1 h2 (by simp [mul_assoc])
  rw [mul_eq_one_iff_eq_inv] at h₁ h₂
  rw [← mul_left_inj (φ 1 y), h₁, ← heq, mul_comm (φ 1 x), h₂]

protected lemma eq_of_eq {i j k : ZMod 3} (φ : FunTrio G H) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hxi : x ∈ φ.support i) (hxj : x ∈ φ.support j)
    (hyi : y ∈ φ.support i) (hyj : y ∈ φ.support j) (heq : φ i y = φ j y)
    (h2 : y⁻¹ * x⁻¹ ∈ φ.support k) : φ i x = φ j x := by
  set e : ZMod 3 ↪ ZMod 3 := {
    toFun := ![i, j, k]
    inj' := by
      simp [Function.Injective, (ZMod.finEquiv 3).symm.forall_congr_left, Fin.forall_fin_succ, hij,
        hik, hij.symm, hjk, hik.symm, hjk.symm]}
  have hwin := (φ.comp' e).eq_of_eq₀ (x := x) (y := y) (by simpa [e]) (by simpa [e]) (by simpa [e])
    (by simpa [e])
  simpa [e, heq, h2] using hwin

protected lemma eq_of_eq' (φ : FunTrio G H) (hijk : [i, j, k].Nodup)
    (hxi : x ∈ φ.support i) (hxj : x ∈ φ.support j) (hyi : y ∈ φ.support i) (hyj : y ∈ φ.support j)
    (heq : φ i y = φ j y) (h2 : y⁻¹ * x⁻¹ ∈ φ.support k) : φ i x = φ j x := by
  obtain ⟨e, rfl, rfl, rfl⟩ := ZMod.exists_equiv_three hijk
  have hwin := (φ.comp e).eq_of_eq₀ (x := x) (y := y) (by simpa) (by simpa) (by simpa) (by simpa)
  simpa [heq, h2] using hwin

lemma IsNormal.eqOn (hφ : φ.IsNormal) : EqOn (φ 0) (φ 1)
    ((φ.support 0) ∩ (φ.support 1) ∩ (·⁻¹) ⁻¹' (φ.support 2)) := by
  intro x ⟨⟨hx0, hx1⟩, (hx2 : x⁻¹ ∈ φ.support 2)⟩
  exact φ.eq_of_eq₀ hx0 hx1 hφ.mem hφ.mem (by rw [hφ.eq_one, hφ.eq_one]) (by simpa)

lemma IsNormal.eqOn' (hφ : φ.IsNormal) (hijk : [i, j, k].Nodup) : EqOn (φ i) (φ j)
    ((φ.support i) ∩ (φ.support j) ∩ (·⁻¹) ⁻¹' (φ.support k)) := by
  obtain ⟨e, rfl, rfl, rfl⟩ := ZMod.exists_equiv_three hijk
  simpa using (hφ.comp e).eqOn

lemma IsNormal.map_inv (hφ : φ.IsNormal) (hijk : [i, j, k].Nodup) (hix : x ∈ φ.support i)
    (hix' : x⁻¹ ∈ φ.support i) (hjx : x ∈ φ.support j) (hkx : x⁻¹ ∈ φ.support k) :
    φ i x⁻¹ = (φ i x)⁻¹ := by
  have h := φ.mul_eq_one' hijk hix' hjx hφ.mem (by simp)
  rwa [hφ.eq_one, mul_one, ← hφ.eqOn' hijk, mul_eq_one_iff_eq_inv] at h
  simp [hix, hjx, hkx]

def Extensible (φ : FunTrio G H) (j : ZMod 3) (x : G) (a : H) : Prop :=
  ∀ (v : ZMod 3 → G), v j = x → ∏ i, v i = 1 → (∀ i ≠ j, v i ∈ φ.support i)
    → ∏ i with i ≠ j, φ i (v i) = a⁻¹

def extend [DecidableEq G] (φ : FunTrio G H) (hx : φ.Extensible j x a) : FunTrio G H where
  toFun i := if i = j then Function.update (φ i) x a else φ i
  support i := if i = j then insert x (φ.support j) else φ.support i
  prod_eq_one v h1 h := by
    obtain rfl | hne := eq_or_ne (v j) x
    · simp_rw [ite_apply, Finset.prod_ite, Finset.prod_filter,
        Finset.prod_ite_eq', Finset.mem_univ, if_true, Function.update_self, ite_not,
        Finset.prod_ite, Finset.prod_const_one, one_mul]
      rw [hx v rfl h1 (by grind), mul_inv_cancel]
    rw [Fintype.prod_congr (g := fun i ↦ φ i (v i)) _ (by grind), φ.prod_eq_one _ h1]
    exact fun i ↦ by by_cases i = j <;> grind

lemma IsNormal.exists_of_not_extensible (hφ : φ.IsNormal) (hijk : [i, j, k].Nodup)
    (hne : ∀ a, ¬ φ.Extensible k z a) (hzi : z⁻¹ ∈ φ.support i) :
    ∃ x y, x ∈ φ.support i ∧ y ∈ φ.support j ∧ φ i x * φ j y ≠ (φ i z⁻¹)⁻¹ := sorry

lemma IsNormal.foo (hφ : φ.IsNormal) (h0 : φ.support 0 = univ) {x y u : G}
    (hx : x ∈ φ.support 0) (hy : y ∈ φ.support 1) (hyu : y * u ∈ φ.support 1)
    (hu : u ∈ φ.support 0) (hxy : x * y ∈ φ.support 1)
    (hyu : y⁻¹ * u⁻¹ )

    (hyu : y * u ∈ φ.support 2)
    (hyu' : y⁻¹ * u⁻¹ ∈ φ.support 0)
    (hxyu : x⁻¹ * y⁻¹ * u⁻¹ ∈ φ.support 0) :
    ∃ z a, z ∉ φ.support 2 ∧ φ.Extensible 2 z a := by
  have h1 : φ 0 (x⁻¹ * y⁻¹ * u⁻¹) * φ 1 x = φ 0 (u⁻¹ * y⁻¹) := by
    rw [← eq_comm, ← mul_one (φ 0 _), ← hφ.eq_one (i := 1), ← mul_left_inj (φ 2 (y * u)),
      φ.mul_eq_one (by rwa [mul_comm]) hφ.mem hyu (by simp), φ.mul_eq_one hxyu hx hyu]
    simp [mul_assoc, mul_comm x⁻¹]
  have h2 : φ 1 (x * y) = φ 0 x * φ 1 y

-- lemma Extensible.of_add (φ : FunTrio G H) (j : ZMod 3) (x : G)
--     (h : ∀ y y' z z', y ∈ φ.support (j + 1) → y' ∈ φ.support (j + 1) → z ∈ φ.support (j + 2)
--       → z ∈ φ.support (j + 2) → y * z = x⁻¹ → y' * z' = x⁻¹ →
--         φ (j + 1) y * φ (j + 2) z = φ (j + 1) y' * φ (j + 2) z')









--     φ i (x⁻¹) = (φ i x)⁻¹ := by
--   wlog hi : i = 0 generalizing φ i with aux
--   · simpa using aux (hφ.comp (Equiv.addRight i)) (by simpa) (by simpa) rfl
--   subst hi

--   have := φ.mul_eq_one hix


-- lemma IsNormal.bar (hφ : φ.IsNormal) {d i j : ZMod 3} (h2 : φ.support d = Set.univ) (x : G)
--     (hid : i ≠ d) (hjd : j ≠ d) : Eq := by


-- lemma IsNormal (i : ZMod 3) (x : G) (hx0 : )


-- @[simps]
-- def reverse (φ : FunTrio G H) : FunTrio G H where
--   toFun i := φ.toFun (- i)
--   mul_eq_one' x y z a b c h1 hx hy hz := by
--     rw [mul_right_comm]
--     exact φ.mul_eq_one' x z y a c b (by rwa [mul_right_comm]) (by simpa) (by simpa) (by simpa)

-- @[simp]
-- lemma rotate_apply (φ : FunTrio G H) (d i : ZMod 3) : (φ.rotate d) i = φ (i + d) := rfl

-- def support (φ : FunTrio G H) (i : ZMod 3) : Set G := {x | φ.toFun i x ≠ none}

-- @[simp]
-- lemma rotate_support (φ : FunTrio G H) (d i : ZMod 3) :
--     (φ.rotate d).support i = φ.support (i + d) := rfl

-- lemma mul_eq_one (hx : x ∈ φ.support 0) (hy : y ∈ φ.support 1) (hz : z ∈ φ.support 2)
--     (h1 : x * y * z = 1) : φ 0 x * φ 1 y * φ 2 z = 1 := by
--   simp only [support, ne_eq, Option.ne_none_iff_exists, Set.mem_setOf_eq] at hx hy hz
--   obtain ⟨a, ha⟩ := hx
--   obtain ⟨b, hb⟩ := hy
--   obtain ⟨c, hc⟩ := hz
--   simpa [← ha, ← hb, ← hc, coe_apply] using φ.mul_eq_one' _ _ _ a b c h1 ha.symm hb.symm hc.symm

-- lemma mul_eq_one_shift (hx : x ∈ φ.support i) (hy : y ∈ φ.support (i + 1))
--     (hz : z ∈ φ.support (i + 2)) (h1 : x * y * z = 1) : φ i x * φ (i + 1) y * φ (i + 2) z = 1 := by
--   simpa [add_comm _ i] using (φ.rotate i).mul_eq_one (x := x) (y := y) (z := z) (by simpa)
--     (by simpa [add_comm]) (by simpa [add_comm]) h1

-- def scale (φ : FunTrio G H) (a : ZMod 3 → G) (ha : a 0 * a 1 * a 2 = 1) : FunTrio G H where
--   toFun i := φ.toFun i (a i) *
--   mul_eq_one' := _


  -- simpa using this
  -- sorry
