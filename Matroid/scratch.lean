import Mathlib

variable {R M ι : Type*} [CommSemiring R] [AddCommGroup M] [Module R M] {x : ι}

open Submodule

notation:65 f:65 " ⇂ " s:66 => fun x : ↥s ↦ f x

theorem linearIndependent_restrict_union {R M ι : Type*} [CommSemiring R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M}
    (hs : LinearIndependent R (f ⇂ s)) (ht : LinearIndependent R (f ⇂ t))
    (hdj : Disjoint (span R (f '' s)) (span R (f '' t))) :
    LinearIndependent R (f ⇂ (s ∪ t)) := by
  eta_expand at f

  sorry
