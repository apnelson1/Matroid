import Mathlib.Order.Minimal

open Set


variable {r : α → α → Prop} {s : β → β → Prop}

theorem RelIso.minimals_preimage_eq (f : r ≃r s) (y : Set β) :
    minimals r (f ⁻¹' y) = f ⁻¹' (minimals s y) := by
  have hr : range f = univ
  · convert f.toEquiv.range_eq_univ
  convert f.toRelEmbedding.minimals_preimage_eq y
  simp only [coe_toRelEmbedding, hr, inter_univ]

theorem RelIso.maximals_preimage_eq (f : r ≃r s) (y : Set β) :
    maximals r (f ⁻¹' y) = f ⁻¹' (maximals s y) :=
  f.swap.minimals_preimage_eq y
