import Mathlib.Tactic

open Set

variable {α ι : Type*} {P : α → Prop} {i : ι} {x : α}

lemma minimal_is_lower_bound [LinearOrder α] (h : Minimal P x) : x ∈ lowerBounds P :=
  fun y hy ↦ (le_total x y).elim id (h.2 hy)

lemma minimalFor_is_lower_bound [LinearOrder α] {P : ι → Prop} (f : ι → α) (h : MinimalFor P f i) :
    ∀ j, P j → f i ≤ f j :=
  fun j hj ↦ (le_total (f i) (f j)).elim id (h.2 hj)

lemma maximal_is_upper_bound [LinearOrder α] (h : Maximal P x) : x ∈ upperBounds P :=
  fun y hy ↦ (le_total y x).elim id (h.2 hy)

lemma maximalFor_is_upper_bound [LinearOrder α] {P : ι → Prop} (f : ι → α) (h : MaximalFor P f i) :
    ∀ j, P j → f j ≤ f i :=
  fun j hj ↦ (le_total (f j) (f i)).elim id (h.2 hj)
