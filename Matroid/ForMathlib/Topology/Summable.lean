module

public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Matroid.ForMathlib.Order.Misc

/-!
# Additional infinite-sum lemmas

The complete-lattice summation API is in `Mathlib.Topology.Algebra.InfiniteSum.Order`.
This file supplements it with finite-subtype formulas, sums of piecewise functions, and criteria
for a sum to equal `⊤`, including the infinite-support criterion in atomic orders.
It also retains the custom printers for infinite sums and products.
-/

@[expose] public section

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

open Set Function

variable {α M : Type*} {f : α → M} {s : Set α}

section Finite

variable [AddCommMonoid M] [TopologicalSpace M]

theorem tsum_subtype_eq_toFinset_sum (hs : s.Finite) :
    ∑' (x : s), f x = ∑ x ∈ hs.toFinset, f x := by
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe
  simp [Finset.sum_attach]

theorem tsum_subtype_const_of_finite (hs : s.Finite) (c : M) :
    ∑' (_ : s), c = hs.toFinset.card • c := by
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe
  simp

end Finite

section CompleteLattice

variable [AddCommMonoid M] [CompleteLattice M] [CanonicallyOrderedAdd M]
  [TopologicalSpace M] [SupConvergenceClass M]

theorem tsum_ite [T2Space M] [ContinuousAdd M] (P : α → Prop) (f g : α → M)
    [DecidablePred P] :
    ∑' x, (if P x then f x else g x) = (∑' (x : {x | P x}), f x) +
      ∑' (x : {x | ¬ P x}), g x := by
  set φ := fun x ↦ (if P x then f x else g x) with hf
  convert tsum_union_of_disjoint (s := {x | P x}) disjoint_compl_right (f := φ) using 2
  · rw [tsum_congr_set_coe (f := φ) (union_compl_self {x | P x}), tsum_univ]
  all_goals exact tsum_congr <| by grind

variable [IsOrderedAddMonoid M] [OrderClosedTopology M]

theorem tsum_eq_top_iff_of_finite [ContinuousAdd M] [AddEqTopClass M] (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  refine ⟨fun h ↦ ?_, tsum_subtype_eq_top_of_eq_top⟩
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    simp only [tsum_empty] at h
    exact (zero_ne_top h).elim
  | @insert a s₀ has₀ hs₀ ih =>
    rw [tsum_insert has₀] at h
    obtain (h | h) := AddEqTopClass.eq_or_eq_of_add _ _ h
    · simp [h]
    simp [ih h]

end CompleteLattice

section CompleteLinearOrder

variable [AddCommMonoid M] [TopologicalSpace M] [CompleteLinearOrder M]
    [SupConvergenceClass M] [CanonicallyOrderedAdd M]
    [AddEqTopClass M] [IsOrderedAddMonoid M] [OrderClosedTopology M]
    [Archimedean (AddSubmonoid.neTop M)]
    [AddLeftStrictMono (AddSubmonoid.neTop M)]

theorem tsum_const_eq_top [Infinite α] {c : M} (hc : c ≠ 0) : ∑' (_ : α), c = ⊤ := by
  obtain rfl | hne := eq_or_ne c ⊤
  · grw [← top_le_iff, ← le_tsum (fun _ : α ↦ ⊤) (Classical.arbitrary α)]
  simp only [tsum_eq_iSup_sum, Finset.sum_const, iSup_eq_top]
  refine fun b hb ↦ ?_
  obtain ⟨n, hlt⟩ := exists_lt_nsmul (R := (AddSubmonoid.neTop M)) (a := ⟨c, hne⟩)
    (Subtype.coe_lt_coe.1 <| zero_le.lt_of_ne (by simpa using hc.symm)) ⟨b, hb.ne⟩
  obtain ⟨s, rfl⟩ := Infinite.exists_subset_card_eq α n
  use s
  rwa [← AddSubmonoidClass.coe_nsmul (⟨c, hne⟩ : AddSubmonoid.neTop M) s.card]

theorem tsum_subtype_const_eq_top (hs : s.Infinite) {c : M} (hc : c ≠ 0) :
    ∑' (_ : s), c = ⊤ := by
  have := hs.to_subtype
  exact tsum_const_eq_top hc

variable [IsAtomic M]

theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  obtain ⟨x, hx : f x ≠ 0⟩ := hf.nonempty
  have hx' := eq_bot_or_exists_atom_le (f x)
  rw [bot_eq_zero, or_iff_right hx] at hx'
  obtain ⟨a, ha, hax⟩ := hx'
  grw [← tsum_subtype_support, ← top_le_iff, ← tsum_le_tsum (f := fun _ ↦ a),
    tsum_subtype_const_eq_top hf]
  · rw [← bot_eq_zero]
    exact ha.ne_bot
  rintro ⟨y, hy⟩
  by_contra! hcon
  rw [ha.lt_iff, bot_eq_zero] at hcon
  contradiction

theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (fun hs ↦ ?_) (fun hex ↦ ?_)⟩
  · contrapose! h
    rw [← tsum_subtype_support, tsum_subtype_eq_toFinset_sum h.1]
    intro hcon
    obtain ⟨x, hx⟩ := exists_of_sum_eq_top hcon
    exact h.2 x hx
  · exact tsum_eq_top_of_support_infinite hs
  exact tsum_eq_top_of_eq_top hex

theorem tsum_subtype_eq_top_iff :
    ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
  rw [tsum_eq_top_iff (f := fun a : s ↦ f a)]
  refine or_congr ?_ (by simp)
  change (support (f ∘ Subtype.val)).Infinite ↔ _
  rw [support_comp_eq_preimage, ← infinite_image_iff Subtype.val_injective.injOn,
    image_preimage_eq_inter_range, Subtype.range_coe, inter_comm]

theorem tsum_subtype_eq_top_of_inter_support_infinite (hf : (s ∩ f.support).Infinite) :
    ∑' (a : s), f a = ⊤ := by
  simp [tsum_subtype_eq_top_iff, hf]

end CompleteLinearOrder
