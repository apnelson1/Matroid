import Mathlib

variable {α : Type*} {n : ℕ}

section DecEq

variable [DecidableEq α]

/-- A string `a` `IsCompatible` with `s : Finset α` and `f : α → ℕ` if `a i ∈ s` for all `i`,
and each `x ∈ s` occurs exactly `f x` times in `a`.
`IsCompatible` could have just been defined with an `∧`, but
defining it as a prop-valued structure with named fields means that for `h : IsCompatible s f a`,
you can write `h.forall_mem i` to prove that `a i ∈ s`,
and `h.forall_preimage_card x` to show that `x ∈ s → ({i : Fin n | a i = x} : Finset _).card = f x`.
Also, `mk_iff` means that a lemma `isCompatible_iff` is automatically generated. -/
@[mk_iff]
structure IsCompatible (s : Finset α) (f : α → ℕ) (a : Fin n → α) : Prop where
  forall_mem : ∀ i, a i ∈ s
  forall_preimage_card : ∀ x ∈ s, ({i : Fin n | a i = x} : Finset _).card = f x

structure IsCompat (s : Finset α) (f : α → ℕ) (l : List α) : Prop where
  forall_mem : ∀ i, l.get i ∈ s
  forall_length : ∀ x ∈ s, (l.filter (· = x)).length = f x

/-- The type of strings that are compatible with `s` is finite,
since it maps injectively into the finite type `Fin n → s`.  -/
noncomputable instance fintype_compatible (s : Finset α) (f : α → ℕ) :
    Fintype {a : Fin n → α // IsCompatible s f a} := by
  have : Finite {a : Fin n → α // IsCompatible s f a} := by
    refine Finite.of_injective (β := Fin n → s) (fun a i ↦ ⟨a.1 i, a.2.forall_mem i⟩) ?_
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simpa [funext_iff] using hab
  induction'
  apply Fintype.ofFinite

-- def foo' {m n : ℕ} (f : α → ℕ) (s : Finset α) {x : α} (hxs : x ∉ s) (hn : ∑ x ∈ s, f x = n) :
--     {a // IsCompat (Finset.cons x s hxs) f a} ≃
--     {q : Finset (Fin n) // q.card = f x} × {a // IsCompat s f a} where
--   toFun p := by
--     refine ⟨⟨({j | p.1.get j = x} : Finset _), ?_⟩, ?_⟩
--   invFun := _
--   left_inv := _
--   right_inv := _

def foo {m n : ℕ} (f : α → ℕ) (s : Finset α) {x : α} (hxs : x ∉ s) (hnm : n = f x + m) :
    {a : Fin n → α // IsCompatible (Finset.cons x s hxs) f a} ≃
    {q : Finset (Fin n) // q.card = f x} × {a : Fin m → α // IsCompatible s f a} where
  toFun p := ⟨⟨({j | p.1 j = x} : Finset _), sorry⟩,
    ⟨fun i ↦ p.1 (by

    have := (Finset.sort (· ≤ ·) {j | p.1 j ≠ x}).get i

    ), sorry⟩⟩
  invFun := _
  left_inv := _
  right_inv := _

lemma card_compatible_eq (s : Finset α) (f : α → ℕ) (hsum : ∑ x ∈ s, f x = n) :
    Fintype.card {a : Fin n → α // IsCompatible s f a} = Nat.multinomial s f := by
  -- Use induction on `s`
  induction s using Finset.cons_induction generalizing n with
  | empty =>
  -- we get some trivial goal if `s` is empty.
    obtain rfl : 0 = n := by simpa using hsum
    simp [show ∀ (a : Fin 0 → α), IsCompatible ∅ f a from fun a ↦ ⟨by simp, by simp⟩]
  | @cons i s his IH =>
  rw [Finset.sum_cons] at hsum
  rw [Nat.multinomial_cons, ← IH rfl, hsum, Fintype.card_congr (foo f s his hsum.symm)]
  simp [Fintype.card_finset_len, Fintype.card_fin]

end DecEq

lemma Finsupp.multinomial_spec (f : α →₀ ℕ) :
    (f.prod fun _ n ↦ n.factorial) * f.multinomial = (f.sum fun _ ↦ id).factorial :=
  Nat.multinomial_spec f.support f

theorem Finsupp.natInduction {α : Type u_1} {p : (α →₀ ℕ) → Prop} (f : α →₀ ℕ) (h0 : p 0)
    (IH : ∀ (a : α) (f : α →₀ ℕ), p f → p (single a 1 + f)) : p f := by
  classical
  obtain rfl | hne := eq_or_ne f 0
  · exact h0
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by simpa [DFunLike.ext_iff] using hne
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero ha
  have h_eq : f = single a 1 + (f.update a k) := by
    ext i
    obtain rfl | hne := eq_or_ne i a
    · simp [Finsupp.update, hk, add_comm]
    simp only [update, coe_add, coe_mk, Pi.add_apply, Finsupp.single]
    aesop
  have hlt : (f.update a k).sum (fun _ ↦ id) < f.sum (fun _ ↦ id) := by
    nth_rewrite 2 [h_eq]
    rw [Finsupp.sum_add_index' (by simp) (by simp)]
    simp
  rw [h_eq]
  exact IH a _ (Finsupp.natInduction (f.update a k) h0 IH)
termination_by Finsupp.sum f (fun _ ↦ id)



-- lemma Finsupp.multinomial_add_single_one (f : α →₀ ℕ) (i : α) :
--   (f.update i (f i + 1)).multinomial = 2 := by

-- lemma Finsupp.multinomial_add_one (f : α →₀ ℕ) (i : α) :
--     (f.update i (f i + 1)).multinomial = 2 := by
--   classical
--   -- have hsupp : (f.update i (f i + 1)).support = insert i f.support := sorry
--   have hrw : (f.update i (f i + 1)).sum (fun _ ↦ id) = f.sum (fun _ ↦ id) + 1 := by
--     simpa [← add_assoc, add_right_comm] using f.sum_update_add (g := fun _ ↦ id) i (f i + 1)

--   sorry


--   rw [(f.update i (f i + 1)).multinomial_update i]
--   simp [hrw]
--   have := f.multinomial_update i
--   have := (f.update i (f i + 1)).multinomial_spec

--   simp [Finsupp.sum, hsupp] at this
