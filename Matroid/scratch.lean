import Mathlib.Data.Set.Basic

variable {α : Type*}

example {s t : Set α} (hst : Disjoint s t) [DecidablePred (· ∈ s)] : ↑(s ∪ t) ≃ ↑s ⊕ ↑t where
  toFun x := if h : x.1 ∈ s then .inl ⟨x,h⟩ else .inr ⟨x, sorry⟩
  invFun := Sum.elim (fun x ↦ ⟨x, sorry⟩) (fun x ↦ ⟨x,sorry⟩)
  left_inv := _
  right_inv := _
