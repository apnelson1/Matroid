import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Order.T5
-- import Matroid.ForMathlib.Topology.SSup
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Matroid.ForMathlib.Order.Misc
import Mathlib.Algebra.Order.Quantale
-- import Mathlib.Algebra.Order.IsBotOne
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


section prelim

@[to_additive]
theorem tprod_subtype_eq_toFinset_prod [CommMonoid M] [TopologicalSpace M] (hs : s.Finite) :
    ∏' (x : s), f x = ∏ x ∈ hs.toFinset, f x := by
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe
  simp [Finset.prod_attach]

@[to_additive]
theorem tprod_subtype_const_of_finite [CommMonoid M] [TopologicalSpace M] (hs : s.Finite) (c : M) :
    ∏' (_ : s), c = c ^ hs.toFinset.card := by
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe
  simp

variable [CommMonoid M] [TopologicalSpace M]

section CompleteLattice

variable [CompleteLattice M] [SupConvergenceClass M] [CanonicallyOrderedMul M]

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

@[to_additive]
theorem tprod_eq_top_iff_of_finite [ContinuousMul M] [MulEqTopClass M] (hs : s.Finite) :
    ∏' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  refine ⟨fun h ↦ ?_, tprod_subtype_eq_top_of_eq_top⟩
  induction s, hs using Set.Finite.induction_on with
  | empty => simp at h
  | @insert a s₀ has₀ hs₀ ih =>
    rw [tprod_insert has₀] at h
    obtain (h | h) := MulEqTopClass.eq_or_eq_of_mul _ _ h
    · simp [h]
    simp [ih h]

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

end CompleteLattice

section CompleteLinearOrder

variable [CompleteLinearOrder M] [SupConvergenceClass M] [CanonicallyOrderedMul M]
    [MulEqTopClass M] [IsOrderedMonoid M] [OrderClosedTopology M]
    [MulArchimedean (Submonoid.neTop M)]
    [MulLeftStrictMono (Submonoid.neTop M)]

@[to_additive]
theorem tprod_const_eq_top [Infinite α] {c : M} (hc : c ≠ 1) : ∏' (_ : α), c = ⊤ := by
  obtain rfl | hne := eq_or_ne c ⊤
  · grw [← top_le_iff, ← le_tprod (Classical.arbitrary α)]
  simp only [tprod_eq_iSup_prod, Finset.prod_const, iSup_eq_top]
  refine fun b hb ↦ ?_
  obtain ⟨n, hlt⟩ := exists_lt_pow (R := (Submonoid.neTop M)) (a := ⟨c, hne⟩)
    (Subtype.coe_lt_coe.1 <| one_le.lt_of_ne (by simpa using hc.symm)) ⟨b, hb.ne⟩
  obtain ⟨s, rfl⟩ := Infinite.exists_subset_card_eq α n
  exact ⟨s, by simpa using hlt⟩

@[to_additive]
theorem tprod_subtype_const_eq_top (hs : s.Infinite) {c : M} (hc : c ≠ 1) : ∏' (_ : s), c = ⊤ := by
  have := hs.to_subtype
  exact tprod_const_eq_top hc

variable [IsAtomic M]

@[to_additive]
theorem tprod_eq_top_of_support_infinite (hf : f.mulSupport.Infinite) : ∏' a, f a = ⊤ := by
  obtain ⟨x, hx : f x ≠ 1⟩ := hf.nonempty
  have hx' := eq_bot_or_exists_atom_le (f x)
  rw [bot_eq_one, or_iff_right hx] at hx'
  obtain ⟨a, ha, hax⟩ := hx'
  grw [← tprod_subtype_mulSupport, ← top_le_iff, ← tprod_le_tprod (f := fun _ ↦ a),
    tprod_subtype_const_eq_top hf]
  · rw [← bot_eq_one]
    exact ha.ne_bot
  rintro ⟨y, hy⟩
  by_contra! hcon
  rw [ha.lt_iff, bot_eq_one] at hcon
  contradiction

@[to_additive]
theorem tprod_eq_top_iff : ∏' a, f a = ⊤ ↔ f.mulSupport.Infinite ∨ ∃ a, f a = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (fun hs ↦ ?_) (fun hex ↦ ?_)⟩
  · contrapose! h
    rw [← tprod_subtype_mulSupport, tprod_subtype_eq_toFinset_prod h.1]
    intro hcon
    obtain ⟨x, hx⟩ := exists_of_prod_eq_top hcon
    exact h.2 x hx
  · exact tprod_eq_top_of_support_infinite hs
  exact tprod_eq_top_of_eq_top hex

@[to_additive]
theorem tprod_subtype_eq_top_iff :
    ∏' (a : s), f a = ⊤ ↔ (s ∩ f.mulSupport).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
  convert tprod_eq_top_iff (M := M)
  · convert Set.finite_image_iff Subtype.val_injective.injOn
    aesop
  simp

@[to_additive]
theorem tprod_subtype_eq_top_of_inter_support_infinite {s : Set α}
    (hf : (s ∩ f.mulSupport).Infinite) : ∏' (a : s), f a = ⊤ := by
  simp [tprod_subtype_eq_top_iff, hf]

end CompleteLinearOrder

section Ring

variable {R : Type*} [Semiring R] [CompleteLattice R] [IsQuantale R] [TopologicalSpace R]
    [CanonicallyOrderedAdd R] [SupConvergenceClass R] [T2Space R]

theorem mul_tsum (c : R) (f : α → R) : c * (∑' a, f a) = ∑' a, (c * f a) := by
  rw [tsum_eq_iSup_sum, tsum_eq_iSup_sum, Quantale.mul_iSup_distrib,
    iSup_congr (fun _ ↦ Finset.mul_sum ..)]

theorem tsum_mul (c : R) (f : α → R) : (∑' a, f a) * c = ∑' a, (f a * c) := by
  rw [tsum_eq_iSup_sum, tsum_eq_iSup_sum, Quantale.iSup_mul_distrib,
    iSup_congr (fun _ ↦ Finset.sum_mul ..)]

end Ring
