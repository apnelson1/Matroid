import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Order.T5
import Matroid.ForMathlib.Topology.SSup
import Mathlib.Topology.Algebra.InfiniteSum.Order
-- import Matroid.ForMathlib.ENat
-- import Matroid.ForMathlib.Card
set_option linter.style.longLine false

open Lean Lean.PrettyPrinter.Delaborator in
/-- Delaborator for tsums?. -/
@[app_delab tsum]
meta def tsum_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(∑' (_ : $dom), $body)
      else if prop || ppTypes then
        `(∑' ($x:ident : $dom), $body)
      else
        `(∑' $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∑' $x:ident, ∑' (_ : $y:ident ∈ $s), $body)
    | `(∑' ($x:ident : $_), ∑' (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(∑' $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

open Lean Lean.PrettyPrinter.Delaborator in
@[app_delab tprod]
meta def tprod_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(∏' (_ : $dom), $body)
      else if prop || ppTypes then
        `(∏' ($x:ident : $dom), $body)
      else
        `(∏' $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∏' $x:ident, ∑' (_ : $y:ident ∈ $s), $body)
    | `(∏' ($x:ident : $_), ∏' (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(∏' $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

open Set Set.Notation Function


variable {ι : Sort*} {α β M : Type*} {a b : α} {f g : α → M} {s t : Set α}

class AddEqTopClass (M : Type*) [Add M] [Top M] : Prop where
  eq_or_eq_of_add (a b : M) : a + b = ⊤ → a = ⊤ ∨ b = ⊤

@[to_additive]
class MulEqTopClass (M : Type*) [Mul M] [Top M] : Prop where
  eq_or_eq_of_mul (a b : M) : a * b = ⊤ → a = ⊤ ∨ b = ⊤

section prelim

variable [CommMonoid M] [TopologicalSpace M] [CompleteLattice M] [SupConvergenceClass M]
  [CanonicallyOrderedMul M]

@[to_additive]
theorem hasProd : HasProd f (⨆ s : Finset α, ∏ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.prod_le_prod_of_subset'

@[to_additive, simp]
theorem multipliable : Multipliable f :=
  ⟨_, hasProd⟩


@[to_additive]
theorem tprod_eq_iSup_prod [T2Space M] : ∏' x, f x = (⨆ s : Finset α, ∏ a ∈ s, f a) :=
  hasProd.tprod_eq

section ContinuousMul

variable  [ContinuousMul M]

section T2

variable [T2Space M]

@[to_additive]
theorem tprod_mul : ∏' a, (f a * g a) = (∏' a, f a) * ∏' a, g a :=
  multipliable.tprod_mul multipliable

@[to_additive]
theorem tprod_union_disjoint (hd : Disjoint s t) :
    ∏' (x : ↑(s ∪ t)), f x = (∏' (x : s), f x) * ∏' (x : t), f x :=
  multipliable.tprod_union_disjoint hd multipliable

@[to_additive]
theorem tprod_le_of_subset (h : s ⊆ t) : ∏' (x : s), f x ≤ ∏' (x : t), f x := by
  rw [← diff_union_of_subset h, tprod_union_disjoint disjoint_sdiff_left]
  exact le_mul_self

@[to_additive]
theorem tprod_union_le (s t : Set α) :
    ∏' (x : ↑(s ∪ t)), f (x : α) ≤ (∏' (x : s), f x) * ∏' (x : t), f x := by
  rw [← diff_union_self, tprod_union_disjoint disjoint_sdiff_left]
  exact mul_le_mul_left (tprod_le_of_subset diff_subset) _

@[to_additive]
theorem tprod_insert (h : a ∉ s) : ∏' (x : ↑(insert a s)), f x = f a * ∏' (x : s), f x := by
  rw [← singleton_union, tprod_union_disjoint, tprod_singleton]
  rwa [disjoint_singleton_left]

@[to_additive]
theorem tprod_singleton_add_tprod_ne : f a * (∏' (x : {x // x ≠ a}), f x) = ∏' x, f x := by
  rw [eq_comm, ← tprod_univ, show univ = insert a {a}ᶜ by ext; simp [em]]
  exact tprod_insert (by simp)

@[to_additive]
theorem tprod_ite (P : α → Prop) (f g : α → M) [DecidablePred P] :
    ∏' x, (if P x then f x else g x) = (∏' (x : {x | P x}), f x) * ∏' (x : {x | ¬ P x}), g x := by
  set φ := fun x ↦ (if P x then f x else g x) with hf
  convert tprod_union_disjoint (s := {x | P x}) disjoint_compl_right (f := φ) using 2
  · rw [tprod_congr_set_coe (f := φ) (union_compl_self {x | P x}), tprod_univ]
  all_goals exact tprod_congr <| by grind

end T2

section T3

variable [T3Space M]

@[to_additive]
theorem tprod_comm {f : α → β → M} : ∏' (a) (b), f a b = ∏' (b) (a), f a b :=
  multipliable.tprod_comm' (fun _ ↦ multipliable) fun _ ↦ multipliable

@[to_additive tsum_prod]
theorem tprod_prod {f : α → β → M} : ∏' p : α × β, f p.1 p.2 = ∏' (a) (b), f a b :=
  multipliable.tprod_prod' fun _ ↦ multipliable

@[to_additive]
theorem tprod_sigma {β : α → Type*} (f : ∀ a, β a → M) :
    ∏' p : Σa, β a, f p.1 p.2 = ∏' (a) (b), f a b :=
  multipliable.tprod_sigma' (fun _ ↦ multipliable)

@[to_additive]
theorem tprod_sigma' {β : α → Type*} (f : (Σ a, β a) → M) :
    ∏' p : Σ a, β a, f p = ∏' (a) (b), f ⟨a, b⟩ :=
  multipliable.tprod_sigma' (fun _ ↦ multipliable)

end T3

end ContinuousMul

section OrderClosedTopology

variable [IsOrderedMonoid M] [OrderClosedTopology M]

@[to_additive]
theorem tprod_le_tprod (h : f ≤ g) : ∏' a, f a ≤ ∏' a, g a :=
  multipliable.tprod_le_tprod h multipliable

@[to_additive]
theorem prod_le_tprod (s : Finset α) : ∏ x ∈ s, f x ≤ ∏' x, f x :=
  multipliable.prod_le_tprod s (fun _ _ ↦ one_le)

@[to_additive]
theorem le_tprod (a : α) : f a ≤ ∏' a, f a :=
  multipliable.le_tprod' a

@[to_additive]
theorem le_tprod_of_mem (ha : a ∈ s) : f a ≤ ∏' x : s, f x :=
  le_tprod ⟨a, ha⟩ (f := fun (x : s) ↦ f x)

@[to_additive, simp]
theorem tprod_eq_one : ∏' i, f i = 1 ↔ ∀ i, f i = 1 :=
  multipliable.tprod_eq_one_iff

@[to_additive]
theorem tprod_comp_le_tprod_of_injective  {f : α → β} (hf : Injective f) (g : β → M) :
    ∏' x, g (f x) ≤ ∏' y, g y :=
  multipliable.tprod_le_tprod_of_inj f hf (fun _ _ ↦ one_le) (fun _ ↦ le_refl ..) multipliable

@[to_additive]
theorem tprod_le_tprod_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → M) :
    ∏' y, g y ≤ ∏' x, g (f x) :=
  calc ∏' y, g y = ∏' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
    _ ≤ ∏' x, g (f x) := tprod_comp_le_tprod_of_injective (injective_surjInv hf) (g ∘ f)

@[to_additive]
theorem tprod_comp_eq_tprod_of_bijective {f : α → β} (hf : f.Bijective) (g : β → M) :
    ∏' x, g (f x) = ∏' y, g y :=
  (tprod_comp_le_tprod_of_injective hf.injective g).antisymm
    (tprod_le_tprod_comp_of_surjective hf.surjective g)

@[to_additive]
theorem tprod_range_le_tprod_comp (f : β → M) (g : α → β) : ∏' (x : range g), f x ≤ ∏' x, f (g x) :=
  tprod_le_tprod_comp_of_surjective rangeFactorization_surjective _

@[to_additive]
theorem tprod_comp_eq_tprod_of_equiv (e : α ≃ β) (g : β → M) : ∏' x, g (e x) = ∏' y, g y := by
  rw [tprod_comp_eq_tprod_of_bijective e.bijective]

@[to_additive]
theorem tprod_image_le_tprod_comp (f : β → M) (g : α → β) (s : Set α) :
    ∏' x : (g '' s), f x ≤ ∏' x : s, f (g x) :=
  tprod_le_tprod_comp_of_surjective imageFactorization_surjective _

@[to_additive]
theorem tprod_mono_subtype (f : α → M) {s t : Set α} (h : s ⊆ t) : ∏' x : s, f x ≤ ∏' x : t, f x :=
  tprod_comp_le_tprod_of_injective (inclusion_injective h) (f ∘ (↑))

@[to_additive]
theorem tprod_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∏' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ le_tprod a

@[to_additive]
theorem tprod_subtype_eq_top_of_eq_top (h : ∃ a ∈ s, f a = ⊤) : ∏' a : s, f a = ⊤ :=
  let ⟨a, ha, has⟩ := h
  tprod_eq_top_of_eq_top ⟨⟨a, ha⟩, has⟩

section ContinuousMul

variable [ContinuousMul M] [T3Space M] {ι : Type*}

@[to_additive]
theorem tprod_iUnion_le_tprod (f : α → M) (t : ι → Set α) :
    ∏' x : ⋃ i, t i, f x ≤ ∏' i, (∏' x : (t i), f x) :=
  calc ∏' x : ⋃ i, t i, f x ≤ ∏' x : Σ i, t i, f x.2 :=
    tprod_le_tprod_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∏' i, ∏' x : t i, f x := tprod_sigma' _

@[to_additive]
theorem tprod_biUnion_le_tprod (f : α → M) (s : Set ι) (t : ι → Set α) :
    ∏' x : ⋃ i ∈ s , t i, f x ≤ ∏' i : s, ∏' x : t i, f x :=
  calc ∏' x : ⋃ i ∈ s, t i, f x = ∏' x : ⋃ i : s, t i, f x := by rw [tprod_congr_subtype]; simp
  _ ≤ ∏' i : s, ∏' x : t i, f x := tprod_iUnion_le_tprod _ _

@[to_additive]
theorem tprod_biUnion_le (f : α → M) (s : Finset ι) (t : ι → Set α) :
    ∏' x : ⋃ i ∈ s, t i, f x ≤ ∏ i ∈ s, (∏' x : t i, f x) :=
  (tprod_biUnion_le_tprod f (↑s) t).trans_eq (Finset.tprod_subtype s fun i ↦ ∏' x : t i, f x)

@[to_additive]
theorem tprod_iUnion_le_prod [Fintype ι] (f : α → M) (t : ι → Set α) :
    ∏' x : ⋃ i, t i, f x ≤ ∏ i, ∏' x : t i, f x := by
  convert tprod_iUnion_le_tprod f t
  exact (tprod_fintype fun b ↦ ∏' (x : ↑(t b)), f ↑x).symm

@[to_additive]
theorem tprod_iUnion_eq_tprod (f : α → M) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∏' x : ⋃ i, t i, f x = ∏' i, ∏' x : t i, f x :=
  calc ∏' x : ⋃ i, t i, f x = ∏' x : Σ i, t i, f x.2 :=
    (tprod_comp_eq_tprod_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := tprod_sigma' _

@[to_additive]
theorem tprod_subtype_eq_tprod_mulSupport (s : Set α) (f : α → M) :
    ∏' (x : s), f x = ∏' (x : {x | x ∈ s ∧ f x ≠ 1}), f x := by
  have hu : s = {i | i ∈ s ∧ f i ≠ 1} ∪ {i | i ∈ s ∧ f i = 1} := by
    simp only [Set.ext_iff, ne_eq, mem_union, mem_setOf_eq]
    grind
  have hrw : ∏' i : {i | i ∈ s ∧ f i = 1}, f i = 1 := by simp
  rw [hu, tprod_union_disjoint (by grind), hrw, mul_one, ← hu]

end ContinuousMul

end OrderClosedTopology

section Union

section Top

@[to_additive]
theorem tprod_eq_top_iff_of_finite [T2Space M] [ContinuousMul M] [IsOrderedMonoid M]
    [OrderClosedTopology M] [MulEqTopClass M] (hs : s.Finite) (htop : (1 : M) ≠ ⊤) :
    ∏' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  refine ⟨fun h ↦ ?_, tprod_subtype_eq_top_of_eq_top⟩
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [htop] at h
  | @insert a s₀ has₀ hs₀ ih =>
    rw [tprod_insert has₀] at h
    obtain (h | h) := MulEqTopClass.eq_or_eq_of_mul _ _ h
    · simp [h]
    simp [ih h]

end Top

section distrib

variable {R : Type*} [Semiring R] [CompleteLinearOrder R] [CanonicallyOrderedAdd R]
    [TopologicalSpace R] [OrderTopology R]

theorem mul_tsum [ContinuousMul R] [ContinuousAdd R] [MulLeftMono R] (c : R) (f : α → R) :
    c * (∑' a, f a) = ∑' a, (c * f a) := by
  rw [tsum_eq_iSup_sum, mul_iSup, tsum_eq_iSup_sum, iSup_congr (fun _ ↦ Finset.mul_sum ..)]

theorem tsum_mul [ContinuousMul R] [ContinuousAdd R] [MulLeftMono R] (c : R) (f : α → R) :
    (∑' a, f a) * c = ∑' a, (f a * c) := by
  rw [tsum_eq_iSup_sum, iSup_mul, tsum_eq_iSup_sum, iSup_congr (fun _ ↦ Finset.sum_mul ..)]

end distrib

-- #exit

-- -- true for ennreal
-- protected theorem tsum_const_eq_top {ι : Type*} [Infinite ι] {c : M} (hc : c ≠ 0) :
--     ∑' (_ : ι), c = ⊤ :=
--   tsum_eq_top_of_support_infinite <| by rwa [Function.support_const hc, infinite_univ_iff]

-- -- true for ennreal
-- protected theorem tsum_subtype_const_eq_top_of_ne_zero {s : Set α} (hs : s.Infinite) {c : M}
--     (hc : c ≠ 0) : ∑' (_ : s), c = ⊤ :=
--   tsum_subtype_eq_top_of_inter_support_infinite <| by rwa [support_const hc, inter_univ]


-- -- false for ennreal
-- protected theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
--   rw [iff_def, or_imp, and_iff_right tsum_eq_top_of_support_infinite, or_iff_not_imp_left,
--     not_infinite]
--   refine ⟨fun htop hfin ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
--   · rw [← tsum_subtype_support, tsum_eq_top_iff_of_finite hfin] at htop
--     exact Exists.elim htop <| fun a h ↦ ⟨a, h.2⟩
--   rw [← top_le_iff, ← ha]
--   exact le_tsum a

-- -- false for ennreal
-- protected theorem tsum_subtype_eq_top_iff {s : Set α} :
--     ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
--   simp only [tsum_eq_top_iff, Subtype.exists, exists_prop]
--   convert Iff.rfl
--   convert Set.finite_image_iff Subtype.val_injective.injOn
--   aesop

-- -- false for ennreal
-- protected theorem tsum_subtype_eq_top_of_inter_support_infinite {s : Set α}
--     (hf : (s ∩ f.support).Infinite) : ∑' (a : s), f a = ⊤ :=
--   tsum_subtype_eq_top_iff.2 <| Or.inl hf


-- end prelim



-- #exit

-- protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
--   rw [tsum_eq_iSup_sum, iSup_eq_top]
--   intro b hb
--   lift b to ℕ using hb.ne
--   obtain ⟨t, htf, hbt, hfin⟩ := hf.exists_finite_subset_encard_gt b
--   refine ⟨hfin.toFinset, hbt.trans_le ?_⟩
--   rw [hfin.encard_eq_coe_toFinset_card, Finset.card_eq_sum_ones, Nat.cast_sum]
--   refine Finset.sum_le_sum fun i hi ↦ ?_
--   simp only [Nat.cast_one, one_le_iff_ne_zero]
--   exact htf <| by simpa using hi

-- protected theorem tsum_const_eq_top {ι : Type*} [Infinite ι] {c : M} (hc : c ≠ 0) :
--     ∑' (_ : ι), c = ⊤ :=
--   tsum_eq_top_of_support_infinite <| by rwa [Function.support_const hc, infinite_univ_iff]

-- protected theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
--   rw [iff_def, or_imp, and_iff_right tsum_eq_top_of_support_infinite, or_iff_not_imp_left,
--     not_infinite]
--   refine ⟨fun htop hfin ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
--   · rw [← tsum_subtype_support, tsum_eq_top_iff_of_finite hfin] at htop
--     exact Exists.elim htop <| fun a h ↦ ⟨a, h.2⟩
--   rw [← top_le_iff, ← ha]
--   exact le_tsum a

-- protected theorem tsum_subtype_eq_top_iff {s : Set α} :
--     ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
--   simp only [tsum_eq_top_iff, Subtype.exists, exists_prop]
--   convert Iff.rfl
--   convert Set.finite_image_iff Subtype.val_injective.injOn
--   aesop

-- protected theorem tsum_subtype_eq_top_of_inter_support_infinite {s : Set α}
--     (hf : (s ∩ f.support).Infinite) : ∑' (a : s), f a = ⊤ :=
--   tsum_subtype_eq_top_iff.2 <| Or.inl hf

-- protected theorem tsum_subtype_const_eq_top_of_ne_zero {s : Set α} (hs : s.Infinite) {c : M}
--     (hc : c ≠ 0) : ∑' (_ : s), c = ⊤ :=
--   tsum_subtype_eq_top_of_inter_support_infinite <| by rwa [support_const hc, inter_univ]

-- protected theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → M) :
--     ∑' x, g (f x) ≤ ∑' y, g y :=
--   summable.tsum_le_tsum_of_inj f hf (fun _ _ ↦ zero_le) (fun _ ↦ le_rfl) summable

-- protected theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → M) :
--     ∑' y, g y ≤ ∑' x, g (f x) :=
--   calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
--     _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) (g ∘ f)

-- protected theorem tsum_comp_eq_tsum_of_bijective {f : α → β} (hf : f.Bijective) (g : β → M) :
--     ∑' x, g (f x) = ∑' y, g y :=
--   (tsum_comp_le_tsum_of_injective hf.injective g).antisymm
--     (tsum_le_tsum_comp_of_surjective hf.surjective g)

-- protected theorem tsum_range_le_tsum_comp (f : β → M) (g : α → β) :
--     ∑' (x : range g), f x ≤ ∑' x, f (g x) :=
--   tsum_le_tsum_comp_of_surjective rangeFactorization_surjective _

-- protected theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → M) :
--     ∑' x, g (e x) = ∑' y, g y := by
--   rw [tsum_comp_eq_tsum_of_bijective e.bijective]

-- protected theorem tsum_image_le_tsum_comp (f : β → M) (g : α → β) (s : Set α) :
--     ∑' x : (g '' s), f x ≤ ∑' x : s, f (g x) :=
--   tsum_le_tsum_comp_of_surjective imageFactorization_surjective _

-- protected theorem tsum_mono_subtype (f : α → M) {s t : Set α} (h : s ⊆ t) :
--     ∑' x : s, f x ≤ ∑' x : t, f x :=
--   tsum_comp_le_tsum_of_injective (inclusion_injective h) (f ∘ (↑))

-- protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → M) :
--     ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
--   summable.tsum_sigma' (fun _ ↦ summable)

-- protected theorem tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → M) :
--     ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
--   summable.tsum_sigma' (fun _ ↦ summable)

-- variable {ι : Type*}

-- section Card

-- @[simp] protected theorem tsum_const (c : M) : ∑' _ : ι, c = c * card ι := by
--   obtain hι | hι := finite_or_infinite ι
--   · have := Fintype.ofFinite ι
--     simp [mul_comm]
--   obtain rfl | hne := eq_or_ne c 0
--   · simp
--   rw [tsum_eq_top_of_support_infinite, card_eq_top_of_infinite, mul_top hne]
--   rwa [support_const hne, infinite_univ_iff]

-- /-- A version of `tsum_one` where the `1` is explicitly a function from the type rather than
--   from the subtype. Useful for rewriting. -/
-- protected theorem tsum_one' (s : Set α) : ∑' (i : s), (1 : α → M) i = s.encard := by
--   simp only [Pi.one_apply, tsum_const, card_coe_set_eq, one_mul]

-- @[simp] protected theorem tsum_one (s : Set α) : ∑' (_ : s), 1 = s.encard :=
--   tsum_one' s

-- @[simp] protected theorem tsum_subtype_const (s : Set α) (c : M) :
--     ∑' (_ : s), c = c * s.encard := by
--   rw [← tsum_one s, mul_tsum, mul_one]

-- protected theorem tsum_subtype_const' (s : Set α) (c : M) :
--     ∑' (x : s), (fun (_ : α) ↦ c) x = c * s.encard := by
--   rw [← tsum_one s, mul_tsum, mul_one]

-- protected theorem encard_support_le_tsum : f.support.encard ≤ ∑' x, f x := by
--   classical
--   rw [← tsum_one', tsum_subtype]
--   refine tsum_le_tsum fun x ↦ ?_
--   rw [indicator_apply]
--   split_ifs with h
--   · simpa [one_le_iff_ne_zero]
--   simp

-- protected theorem tsum_ite {P : α → Prop} {s t : M} [DecidablePred P] :
--     ∑' x, (if P x then s else t) = s * {x | P x}.encard + t * {x | ¬ P x}.encard := by
--   set f := fun x ↦ (if P x then s else t) with hf
--   convert tsum_union_disjoint (s := {x | P x}) disjoint_compl_right
--   · rw [tsum_congr_set_coe (f := f) (union_compl_self {x | P x})]
--     exact (tsum_univ ..).symm
--   · rw [tsum_congr (g := fun _ ↦ s) (by grind), tsum_subtype_const]
--   rw [tsum_congr (g := fun _ ↦ t) (by grind), tsum_subtype_const, compl_setOf]

-- protected theorem tsum_encard_eq_encard_iUnion {ι} {s : ι → Set α} (hI : Pairwise (Disjoint on s)) :
--     ∑' i, (s i).encard = (⋃ i, s i).encard := by
--   simp_rw [← tsum_one', tsum_iUnion_eq_tsum _ _ hI]

-- protected theorem tsum_subtype_eq_tsum_support (s : Set α) (f : α → M) :
--     ∑' (x : s), f x = ∑' (x : {i ∈ s | f i ≠ 0}), f x := by
--   have hu : s = {i | i ∈ s ∧ f i ≠ 0} ∪ {i | i ∈ s ∧ f i = 0} := by
--     simp only [Set.ext_iff, ne_eq, mem_union, mem_setOf_eq]
--     grind
--   have hrw : ∑' i : {i | i ∈ s ∧ f i = 0}, f i = 0 := by simp
--   rw [hu, tsum_union_disjoint (by grind), hrw, add_zero, ← hu]

-- theorem encard_iUnion_le_tsum_encard {ι} {s : ι → Set α} :
--     (⋃ i, s i).encard ≤ ∑' i, (s i).encard := by
--   rw [← tsum_one]
--   exact (tsum_iUnion_le_tsum 1 s).trans_eq <| by simp

-- theorem tsum_encard_eq_encard_biUnion {ι} {s : ι → Set α} {t : Set ι}
--     (hI : t.PairwiseDisjoint s) : ∑' i : t, (s i).encard = (⋃ i ∈ t, s i).encard := by
--   rw [biUnion_eq_iUnion, ← tsum_encard_eq_encard_iUnion]
--   simp_rw [Pairwise, Disjoint]
--   aesop

-- theorem encard_biUnion_le_tsum_encard {ι} {s : ι → Set α} {I : Set ι} :
--     (⋃ i ∈ I, s i).encard ≤ ∑' i : I, (s i).encard := by
--   rw [biUnion_eq_iUnion]
--   apply encard_iUnion_le_tsum_encard

-- protected theorem encard_eq_tsum_ite (s : Set α) [DecidablePred (· ∈ s)] :
--     s.encard = ∑' (x : α), if x ∈ s then 1 else 0 := by
--   nth_rw 1 [← inter_univ s, ← iUnion_of_singleton α, inter_iUnion,
--     ← tsum_encard_eq_encard_iUnion (by simp +contextual [Pairwise, disjoint_left]), tsum_congr]
--   intro b
--   split_ifs with hb
--   · rw [inter_eq_self_of_subset_right (by simpa), encard_singleton]
--   rw [inter_singleton_eq_empty.2 hb, encard_empty]

-- theorem tsum_encard_eq_encard_biUnion_iff {ι} {s : ι → Set α} {t : Set ι}
--     (hfin : (⋃ i ∈ t, s i).Finite) :
--     ∑' i : t, (s i).encard = (⋃ i ∈ t, s i).encard ↔ t.PairwiseDisjoint s := by
--   refine ⟨fun h ↦ ?_, tsum_encard_eq_encard_biUnion⟩
--   by_contra hndj
--   simp only [PairwiseDisjoint, Set.Pairwise, ne_eq, onFun, disjoint_left, not_forall, not_not,
--     exists_prop] at hndj
--   obtain ⟨a, ha, b, hb, hab, x, hxa, hxb⟩ := hndj
--   have h1 := tsum_insert (a := a) (s := t \ {a}) (f := fun i ↦ (s i).encard) (by simp)
--   rw [tsum_congr_set_coe (insert_diff_self_of_mem ha) (f := fun i ↦ (s i).encard), h] at h1
--   have h2 := biUnion_insert a (t \ {a}) s
--   rw [insert_diff_self_of_mem ha] at h2
--   simp only at h1
--   have hle := add_le_add_right (encard_biUnion_le_tsum_encard (s := s) (I := t \ {a})) (s a).encard
--   rw [← h1, ← encard_union_add_encard_inter, h2, add_le_left_iff, encard_eq_top_iff,
--     encard_eq_zero, ← disjoint_iff_inter_eq_empty, disjoint_left, ← h2,
--     or_iff_right hfin.not_infinite] at hle
--   simp only [mem_diff, mem_singleton_iff, mem_iUnion, exists_prop, not_exists, not_and,
--     and_imp, not_imp_not] at hle
--   exact hab (hle hxa b hb hxb).symm

-- theorem tsum_encard_eq_encard_iUnion_iff {ι} {s : ι → Set α} (hfin : (⋃ i, s i).Finite) :
--     ∑' i, (s i).encard = (⋃ i, s i).encard ↔ Pairwise (Disjoint on s) := by
--   rw [← tsum_univ, ← biUnion_univ, tsum_encard_eq_encard_biUnion_iff (by simpa)]
--   rw [PairwiseDisjoint, pairwise_univ]

-- protected theorem tsum_encard_eq_encard_sUnion {c : Set (Set α)} (hc : c.PairwiseDisjoint id) :
--     ∑' (t : c), (t : Set α).encard = (⋃₀ c).encard := by
--   rw [sUnion_eq_iUnion, ← tsum_encard_eq_encard_iUnion]
--   rintro ⟨i,hi⟩ ⟨j,hj⟩ hij
--   exact hc hi hj (by simpa using hij)

-- theorem encard_sUnion_le_tsum_encard {c : Set (Set α)} :
--     (⋃₀ c).encard ≤ ∑' s : c, s.1.encard := by
--   rw [sUnion_eq_iUnion]
--   apply encard_iUnion_le_tsum_encard

-- protected theorem tsum_inter_fiber_eq {ι} {s : Set ι} (f : ι → α) :
--     ∑' (a : α), (s ∩ f ⁻¹' {a}).encard = s.encard := by
--   rw [tsum_encard_eq_encard_iUnion]
--   · congr
--     aesop
--   refine fun i j hij ↦ disjoint_iff_forall_ne.2 ?_
--   rintro a ⟨-,rfl⟩ _ ⟨-,rfl⟩ rfl
--   exact hij rfl

-- protected theorem tsum_fiber_eq {ι} (f : ι → α) :
--     ∑' (a : α), (f ⁻¹' {a}).encard = (univ : Set ι).encard := by
--   rw [← tsum_inter_fiber_eq (s := univ) f, tsum_congr]
--   simp

-- end Card

-- end ENat
