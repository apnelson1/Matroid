import Mathlib.LinearAlgebra.LinearIndependent

variable {W 𝔽 : Type} [Field 𝔽] [AddCommGroup W] [Module 𝔽 W] {ι : Type*} {s t : Set ι} {v : ι → W}

lemma LinearIndependent.diff (h : LinearIndependent 𝔽 (fun x : s ↦ v x)) :
    LinearIndependent 𝔽 (fun x : (s \ t : Set ι) ↦ v x) := sorry

abbrev Set.incl {α : Type*} (s : Set α) : s → α := (↑)

lemma LinearIndependent.diff_incl (h : LinearIndependent 𝔽 (v ∘ s.incl)) :
    LinearIndependent 𝔽 (v ∘ (s \ t).incl) := sorry


variable {LongNameType 𝔽 : Type} [Field 𝔽] [AddCommGroup LongNameType] [Module 𝔽 LongNameType]
  {s t : Set LongNameType}

lemma LinearIndependent.diff_index (hli : LinearIndependent 𝔽 ((↑) : s → LongNameType)) :
    LinearIndependent 𝔽 ((↑) : (s \ t : Set LongNameType) → LongNameType) := sorry



lemma LinearIndependent.diff_index_better (hli : LinearIndependent 𝔽 s.incl) :
    LinearIndependent 𝔽 (s \ t).incl := sorry
