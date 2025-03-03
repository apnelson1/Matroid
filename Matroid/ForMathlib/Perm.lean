import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Fin.Finset
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.BigOperators.Fin

variable {n  : ℕ} {R : Type*} [CommRing R]

theorem Equiv.Perm.transpose_induction_on_right {P : Equiv.Perm (Fin (n+1)) → Prop}
    (f : Equiv.Perm (Fin (n+1))) (h1 : P 1) (ih : ∀ (i : Fin n) (g : Equiv.Perm (Fin (n+1))),
      P g → P (g * Equiv.swap i.castSucc i.succ)) : P f :=
  Submonoid.induction_of_closure_eq_top_right (Equiv.Perm.mclosure_swap_castSucc_succ n) f h1 <| by
    rintro σ _ ⟨i, hi, rfl⟩ hσ
    exact ih _ _ hσ

theorem Equiv.Perm.transpose_induction_on_left {P : Equiv.Perm (Fin (n+1)) → Prop}
    (f : Equiv.Perm (Fin (n+1))) (h1 : P 1) (ih : ∀ (i : Fin n) (g : Equiv.Perm (Fin (n+1))),
      P g → P (Equiv.swap i.castSucc i.succ * g)) : P f :=
  Submonoid.induction_of_closure_eq_top_left (Equiv.Perm.mclosure_swap_castSucc_succ n) f h1 <| by
    rintro _ ⟨i, hi, rfl⟩ σ hσ
    exact ih _ _ hσ

theorem Equiv.Perm.sign_eq_prod_prod_Iio (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ j, ∏ i ∈ Finset.Iio j, (if σ i < σ j then 1 else -1) := by
  suffices h : σ.sign = σ.signAux by
    rw [h, Finset.prod_sigma', Equiv.Perm.signAux]
    convert rfl using 2 with x hx
    · simp [Finset.ext_iff, Equiv.Perm.mem_finPairsLT]
    simp [not_lt, ← ite_not (p := _ ≤ _)]
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq ↦ ?_
  rw [Equiv.Perm.signAux_mul, Equiv.Perm.sign_mul, h_eq, Equiv.Perm.sign_swap hne,
    Equiv.Perm.signAux_swap hne]

theorem Equiv.Perm.sign_eq_prod_prod_Ioi (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ i, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then 1 else -1) := by
  rw [σ.sign_eq_prod_prod_Iio]
  apply Finset.prod_comm' (by simp)

theorem prod_Iio_comp_eq_sign_mul_prod {f : Fin n → Fin n → R} (hf : ∀ i j, f i j = - f j i)
    (σ : Equiv.Perm (Fin n)) :
    ∏ j, ∏ i ∈ Finset.Iio j, f (σ i) (σ j) = σ.sign * ∏ j, ∏ i ∈ Finset.Iio j, f i j := by
  rw [← σ.sign_inv, Equiv.Perm.sign_eq_prod_prod_Iio, Finset.prod_sigma', Finset.prod_sigma',
    Finset.prod_sigma']
  simp only [Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
  set D := (Finset.univ : Finset (Fin n)).sigma Finset.Iio with hD
  have hφD : D.image (fun x ↦ ⟨σ x.1 ⊔ σ x.2, σ x.1 ⊓ σ x.2⟩) = D := by
    ext ⟨x1, x2⟩
    suffices (∃ a, ∃ b < a, σ a ⊔ σ b = x1 ∧ σ a ⊓ σ b = x2) ↔ x2 < x1 by simpa [hD]
    refine ⟨?_, fun hlt ↦ ?_⟩
    · rintro ⟨i, j, hij, rfl, rfl⟩
      exact inf_le_sup.lt_of_ne <| by simp [hij.ne.symm]
    obtain hlt' | hle := lt_or_le (σ.symm x1) (σ.symm x2)
    · exact ⟨_, _, hlt', by simp [hlt.le]⟩
    exact ⟨_, _, hle.lt_of_ne (by simp [hlt.ne]), by simp [hlt.le]⟩
  have hinj := Finset.injOn_of_card_image_eq (s := D) (by rw [hφD])
  nth_rw 2 [← hφD]
  rw [Finset.prod_image (fun x hx y hy hxy ↦ hinj hx hy hxy)]
  refine Finset.prod_congr rfl fun ⟨x₁, x₂⟩ hx ↦ ?_
  replace hx : x₂ < x₁ := by simpa [hD] using hx
  obtain hlt | hle := lt_or_le (σ x₁) (σ x₂)
  · simp [inf_eq_left.2 hlt.le, sup_eq_right.2 hlt.le, hx.not_lt, ← hf]
  simp [inf_eq_right.2 hle, sup_eq_left.2 hle, hx]

theorem prod_Ioi_comp_eq_sign_mul_prod {f : Fin n → Fin n → R}
    (hf : ∀ i j, f i j = - f j i) (σ : Equiv.Perm (Fin n)) :
    ∏ i, ∏ j ∈ Finset.Ioi i, f (σ i) (σ j) = σ.sign * ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  convert prod_Iio_comp_eq_sign_mul_prod hf σ using 1
  · apply Finset.prod_comm' (by simp)
  convert rfl using 2
  apply Finset.prod_comm' (by simp)
