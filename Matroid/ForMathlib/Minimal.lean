import Mathlib.Order.Minimal
import Mathlib.Order.RelIso.Set

open Set


variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}


theorem RelIso.minimals_preimage_eq (f : r ≃r s) (y : Set β) :
    minimals r (f ⁻¹' y) = f ⁻¹' (minimals s y) := by
  convert f.toRelEmbedding.minimals_preimage_eq y; simp

theorem RelIso.maximals_preimage_eq (f : r ≃r s) (y : Set β) :
    maximals r (f ⁻¹' y) = f ⁻¹' (maximals s y) :=
  f.swap.minimals_preimage_eq y
