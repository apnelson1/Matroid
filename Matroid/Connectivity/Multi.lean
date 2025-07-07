import Matroid.Connectivity.Local

open Set Function

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X Y : Set α} {ι : Type*}

noncomputable def multiConn (M : Matroid α) (X : ι → Set α) : ℕ∞ :=
  ⨅ (I : {I : ι → Set α // ∀ i, M.IsBasis (I i) (X i)}), M.nullity (⋃ i, I.1 i)

/-- If `I` and `J` are families of pairwise disjoint independent sets such that `I i` and `J i`
have the same closure for each `i`, then the unions of `I i` and `J i` have the same nullity. -/
lemma nullity_switch {X Y : ι → Set α} (hXdj : Pairwise (Disjoint on X))
    (hYdj : Pairwise (Disjoint on Y)) (hcl : ∀ i, M.closure (X i) = M.closure (Y i))
    (hnull : ∀ i, M.nullity (X i) = M.nullity (Y i)):
    M.nullity (⋃ i, X i) = M.nullity (⋃ i, Y i) := by
  wlog hle : M.nullity (⋃ i, X i) < M.nullity (⋃ i, Y i) generalizing X Y with aux
  · rw [not_lt] at hle
    obtain he | hlt := hle.eq_or_lt
    · rw [he]
    exact Eq.symm <| aux hYdj hXdj (fun i ↦ (hcl i).symm) (fun i ↦ (hnull i).symm) hlt
  obtain he | ⟨⟨s⟩⟩ := isEmpty_or_nonempty ι
  · simp

  -- obtain ⟨I, hI⟩

lemma multiConn_eq_of_forall_isBasis {X I : ι → Set α} (hdj : Pairwise (Disjoint on X))
    (hbas : ∀ i, M.IsBasis (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) := by
  sorry
