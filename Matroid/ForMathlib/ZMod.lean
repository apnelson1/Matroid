
lemma ZMod.val_ofNat_of_lt {i n : ℕ} [i.AtLeastTwo] (hin : i < n) :
    (ofNat(i) : ZMod n).val = i := by
  rw [ZMod.val_ofNat, Nat.mod_eq_of_lt (by simpa)]
  exact Nat.add_zero i

lemma ZMod.ofNat_eq_zero {i n : ℕ} [i.AtLeastTwo] : (ofNat(i) : ZMod n) = 0 ↔ (n ∣ i) := by
  rw [← ZMod.val_eq_zero, ZMod.val_ofNat, ← Nat.dvd_iff_mod_eq_zero]
  simp [OfNat.ofNat]

lemma ZMod.ofNat_ne_zero_of_lt {i n : ℕ} [i.AtLeastTwo] (hin : i < n) :
    (ofNat(i) : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.ofNat_eq_zero]
  contrapose! hin
  exact Nat.le_of_dvd (Nat.pos_of_neZero i) hin

lemma ZMod.val_succ [NeZero n] (i : ZMod n) (hi : i ≠ -1) : (i + 1).val = i.val + 1 := by
  obtain rfl | rfl | n := n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact False.elim <| hi <| Subsingleton.elim (α := Fin 1) ..
  rw [ZMod.val_add, ZMod.val_one'' (by simp), Nat.mod_eq_of_lt]
  obtain heq | hne := (Nat.add_one_le_of_lt i.val_lt).eq_or_lt
  · contrapose! hi
    refine ZMod.val_injective _ ?_
    rw [ZMod.val_neg_one]
    lia
  assumption

@[simp]
lemma ZMod.one_eq_zero {n : ℕ} : (1 : ZMod n) = 0 ↔ n = 1 := by
  simp [← ZMod.val_eq_zero, ZMod.val_one_eq_one_mod]

lemma ZMod.val_neg_eq_sub {n : ℕ} [NeZero n] (a : ZMod n) (ha : a ≠ 0) : (-a).val = n - a.val :=
  @ZMod.val_neg_of_ne_zero n _ a ⟨ha⟩
