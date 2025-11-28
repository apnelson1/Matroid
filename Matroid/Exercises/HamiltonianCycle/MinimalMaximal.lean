import Mathlib.Tactic

open Set

variable {α ι : Type*}

lemma minimal_is_lower_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Minimal P x) :
    ∀ y, P y → x ≤ y := by
  intro y hy
  simp only [Minimal] at h
  obtain (_|_) := le_total x y
  · assumption
  · tauto

lemma minimalFor_is_lower_bound [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι}
    (h : MinimalFor P f i) : ∀ j, P j → f i ≤ f j := by
  intro j hj
  simp only [MinimalFor] at h
  obtain (_|_) := le_total (f i) (f j)
  · assumption
  · tauto

lemma maximal_is_upper_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Maximal P x) :
    ∀ y, P y → y ≤ x := by
  intro y hy
  simp [Maximal] at h
  obtain (_|_) := le_total y x
  · assumption
  · tauto

lemma maximalFor_is_upper_bound
    {ι} [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι} (h : MaximalFor P f i) :
    ∀ j, P j → f j ≤ f i := by
  intro j hj
  simp [MaximalFor] at h
  obtain (_|_) := le_total (f j) (f i)
  · assumption
  · tauto
