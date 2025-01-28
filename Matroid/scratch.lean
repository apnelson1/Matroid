import Mathlib.LinearAlgebra.LinearIndependent

variable {LongNameType 𝔽 : Type} [Field 𝔽] [AddCommGroup LongNameType] [Module 𝔽 LongNameType]
  {s t : Set LongNameType}

lemma LinearIndependent.diff_index (hli : LinearIndependent 𝔽 ((↑) : s → LongNameType)) :
    LinearIndependent 𝔽 ((↑) : (s \ t : Set LongNameType) → LongNameType) := sorry

abbrev Set.incl {α : Type*} (s : Set α) : s → α := (↑)

lemma LinearIndependent.diff_index_better (hli : LinearIndependent 𝔽 s.incl) :
    LinearIndependent 𝔽 (s \ t).incl := sorry
