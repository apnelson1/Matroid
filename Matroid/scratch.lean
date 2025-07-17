import Mathlib.Data.ENat.Lattice

variable {α : Type*}

/--  Given a function from `f : α → α` and a proposition `P : α → Prop`,
the minimum number of iterations of `f` required to make `a : α` satisfy `P`,
or `⊤` if no number suffices. -/
noncomputable def depth (f : α → α) (P : α → Prop) (a : α) : ℕ∞ :=
  sInf ((↑) '' {i | P (f^[i] a)})

/-- If `d : α → ℕ∞` is a 'weight' function that drops by one whenever `f` is applied to an element
of nonzero weight, then `d` is equal to the `depth` for the property that `d = 0`. -/
lemma foo {f : α → α} (d : α → ℕ∞) (hdf : ∀ a, d a ≠ 0 → d a = d (f a) + 1) {a : α} :
    depth f (fun a ↦ d a = 0) a = d a := by
  refine le_antisymm ?_ (le_sInf ?_)
  · generalize hk : d a = k
    cases k with
    | top => simp
    | coe k =>
    · suffices d (f^[k] a) = 0 from sInf_le <| by simpa
      induction k generalizing a with
      | zero => simpa using hk
      | succ n IH =>
      · apply IH
        rwa [hdf _ (by simp [hk]), Nat.cast_add, Nat.cast_one,
          WithTop.add_right_inj (by simp)] at hk
  suffices ∀ k, d (f^[k] a) = 0 → d a ≤ k by simpa
  intro k hk
  induction k generalizing a with
  | zero => simpa using hk
  | succ n IH =>
  · simp at hk
    obtain h0 | hne := eq_or_ne (d a) 0
    · simp [h0]
    grw [hdf _ hne, IH hk, Nat.cast_add, Nat.cast_one]
