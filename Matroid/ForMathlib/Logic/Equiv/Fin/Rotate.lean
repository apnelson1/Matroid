module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Extra API for `finRotate`

`Mathlib.Logic.Equiv.Fin.Rotate` defines `finRotate n : Equiv.Perm (Fin n)`, the cycle
`(1, ..., n)`. This file collects the lemmas about it that are needed to treat `Fin n` as the
index type of a cyclic structure (a closed polygon, a cyclic word, ...), and that belong in
`Mathlib.Logic.Equiv.Fin.Rotate`.

## Main statements

* `add_finRotate` : `finRotate n` commutes with translation.
* `finRotate_rev_finRotate` : how `finRotate n` interacts with `Fin.rev`, i.e. with reversing the
  cyclic order.
* `finRotate_ne_self_of_two_le`, `finRotate_finRotate_ne_self_of_three_le` : `finRotate n` has no
  fixed point once `2 ≤ n`, and neither does its square once `3 ≤ n`.
* `finRotate_insert`, `finRotate_succAbove_insert` : the effect on `finRotate` of inserting one new
  index, i.e. of passing from `Fin n` to `Fin (n + 1)` along `(i.succ).succAbove`. These are the
  form in which `finRotate` meets `Fin.insertNth`.
-/

@[expose] public section

variable {n : ℕ}

lemma add_finRotate (i k : Fin n) : i + finRotate n k = finRotate n (i + k) := by
  have := i.neZero
  simp only [finRotate_apply]
  rw [add_assoc]

lemma finRotate_rev_finRotate (k : Fin n) :
    finRotate n (finRotate n k).rev = k.rev := by
  have := k.neZero
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  obtain rfl | hk := eq_or_ne k (Fin.last m)
  · simp
  ext
  have hkm : k < Fin.last m := Fin.lt_last_iff_ne_last.mpr hk
  rw [coe_finRotate_of_ne_last]
  · rw [Fin.val_rev, coe_finRotate_of_ne_last hk, Fin.val_rev]
    omega
  · rw [Fin.rev_ne_iff, Fin.rev_last]
    intro hzero
    have hz := congr_arg Fin.val hzero
    rw [coe_finRotate_of_ne_last hk] at hz
    simp at hz

lemma finRotate_ne_self_of_two_le (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  obtain rfl | hi := eq_or_ne i (Fin.last m)
  · simp only [finRotate_last]
    intro h
    have := congr_arg Fin.val h
    simp at this
    omega
  · intro h
    have hv := congr_arg Fin.val h
    rw [coe_finRotate_of_ne_last hi] at hv
    omega

lemma finRotate_finRotate_ne_self_of_three_le (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  have : NeZero n := ⟨by omega⟩
  simp only [finRotate_apply]
  intro hi
  have htwo : (1 + 1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa [add_assoc] using hi
  have hv := congr_arg Fin.val htwo
  simp [Fin.add_def, Nat.mod_eq_of_lt hn] at hv

/-- Inserting a new index just after `i` sends the successor of `i` to the new index itself. -/
lemma finRotate_insert (i : Fin n) :
    finRotate (n + 1) i.succ = i.succ.succAbove (finRotate n i) := by
  have := i.neZero
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  by_cases hi : i = Fin.last m
  · subst i
    rw [finRotate_last]
    have hs : (Fin.last m).succ = Fin.last (m + 1) := by
      apply Fin.ext
      simp
    rw [hs, finRotate_last, Fin.succAbove_of_castSucc_lt]
    · rfl
    · change (0 : Nat) < m + 1
      omega
  · have him : (i : Nat) < m := Fin.lt_last_iff_ne_last.mpr hi
    rw [finRotate_of_lt him, Fin.succAbove_of_le_castSucc]
    · apply Fin.ext
      rw [coe_finRotate_of_ne_last]
      · rfl
      · intro hilast
        have hv := congr_arg Fin.val hilast
        simp at hv
        omega
    · simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      exact le_rfl

/-- Inserting a new index just after `i` commutes with `finRotate` on the old indices, except at
`i` itself, whose successor is now the new index. -/
lemma finRotate_succAbove_insert (i j : Fin n) : finRotate (n + 1) (i.succ.succAbove j) =
    if j = i then i.succ else i.succ.succAbove (finRotate n j) := by
  have := i.neZero
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  obtain rfl | hji := eq_or_ne j i
  · ext
    simp [Fin.succAbove]
  rw [if_neg hji]
  by_cases hlt : j < i
  · have hjm : (j : Nat) < m := by
      have hji' : (j : Nat) < i := hlt
      have hi := i.isLt
      omega
    rw [Fin.succAbove_of_castSucc_lt]
    · rw [finRotate_of_lt hjm, Fin.succAbove_of_castSucc_lt]
      · apply Fin.ext
        rw [coe_finRotate_of_ne_last]
        · rfl
        · intro hjlast
          have hv := congr_arg Fin.val hjlast
          simp at hv
          omega
      · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega
    · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      omega
  · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hji)
    by_cases hjlast : j = Fin.last m
    · subst j
      rw [Fin.succAbove_of_le_castSucc, finRotate_last]
      · apply Fin.ext
        simp [Fin.succAbove]
      · simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
        change (i : Nat) < m at hij
        omega
    · have hjm : (j : Nat) < m := by
        have hjlt := Fin.lt_last_iff_ne_last.mpr hjlast
        exact hjlt
      rw [Fin.succAbove_of_le_castSucc, finRotate_of_lt, finRotate_of_lt hjm,
        Fin.succAbove_of_le_castSucc]
      · rfl
      · simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
        omega
      · exact Nat.succ_lt_succ hjm
      · have hij' : (i : Nat) < (j : Nat) := hij
        simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
        omega
