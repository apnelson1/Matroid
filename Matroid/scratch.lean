import Mathlib.Data.Finset.Basic

def hf_type : ℕ → Type
  | 0 => Unit
  | n+1 => Finset (hf_type n)

def hf : (n : ℕ) → Finset (hf_type n) → Prop
  | 0 s →
