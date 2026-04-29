import Mathlib.Data.ENat.Pow
import Mathlib.RingTheory.Binomial
import Mathlib.Data.Set.PowersetCard

variable {n k a b : ℕ∞} {α : Type*}

namespace Set

def powersetCard' (s : Set α) (k : ℕ) : Set (Finset α) := {x | (x : Set α) ⊆ s ∧ x.card = k}

lemma encard_powersetCard_eq (α : Type*) (k : ℕ) :
    (powersetCard α k).encard = Ring.choose (ENat.card α) k := sorry

lemma Set.encard_powersetCard_eq (s : Set α) (k : ℕ) : (s.powersetCard' k).encard
