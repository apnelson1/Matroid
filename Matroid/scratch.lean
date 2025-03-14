import Mathlib

set_option linter.style.longLine false

open Set
variable {X Y F : Type*} [Field F] [Fintype X] [Fintype Y] [Zero Y]

-- open Classical in
-- def aux {k : ℕ} (X Y : Type*) [Fintype X] [Fintype Y] [Zero Y] :
--     {f : X → Y // f.support.toFinset.card = k} ≃ (s : {s : Finset X // s.card = k}) × (s.1 → {y : Y // y ≠ 0}) where
--   toFun f := ⟨⟨f.1.support.toFinset, f.2⟩, fun x ↦ ⟨f.1 x.1, by
--     _

--     ⟩⟩
--   invFun s := by
--     refine ⟨fun x ↦ if h : x ∈ s.1.1 then s.2 ⟨x, h⟩ else 0, ?_⟩
--     convert s.1.2

--   left_inv := _
--   right_inv := _

open Classical in
example {k l : ℕ} (hkl : k + l = Fintype.card X) {A : Finset Y} :
    Fintype.card {f : X → Y // (f ⁻¹' A).toFinset.card = k}
    = ((Fintype.card X).choose k) * (A.card) ^ k * Aᶜ.card ^ l := by
  set ψ : {f : X → Y // (f ⁻¹' (A)).toFinset.card = k} → Finset X := fun f ↦ (f.1 ⁻¹' A).toFinset
  have hψ : Set.MapsTo ψ Finset.univ.toSet ({u : Finset X | u.card = k} : Finset _) := by simp [ψ]
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hψ]
  simp only [Finset.univ_filter_card_eq, ψ]
  rw [mul_assoc, ← Finset.card_univ, ← Finset.card_powersetCard, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.univ_filter_card_eq]

  -- rw [← Fintype.card_finset_len]
  -- let σ := fun (s : Finset X) ↦ (s → A) × (↥sᶜ → ↥Aᶜ)
  -- let t := fun (s : Finset X) ↦ (Finset.univ : Finset (σ s))
  -- convert Finset.card_sigma {s : Finset X | s.card = k} t
  -- · set ψ : { f : X → Y // (f ⁻¹' A).toFinset.card = k } → (i : Finset X) × σ i := fun f ↦
  --     ⟨(f.1 ⁻¹' A).toFinset,
  --       fun x ↦ ⟨f.1 x.1, (by obtain ⟨x, hx⟩ := x; simpa using hx)⟩,
  --       fun x ↦ ⟨f.1 x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩⟩
  --   have hinj : Function.Injective ψ := sorry
  --   rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
  --   convert rfl
  --   ext ⟨x, x1, x2⟩
  --   simp only [Finset.univ_filter_card_eq, Finset.mem_sigma, Finset.mem_powersetCard,
  --     Finset.subset_univ, true_and, Finset.mem_univ, and_true, Finset.mem_image, Sigma.mk.injEq,
  --     Subtype.exists, toFinset_card, Fintype.card_ofFinset, exists_and_left, t, ψ, σ]
  --   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩µ

    -- rw [← Fintype.card_range (f := (⟨ψ, hinj⟩ : _ ↪ _))]



  simp only [Fintype.card_finset_len, Finset.univ_filter_card_eq]
  rw [← Finset.card_univ, ← Finset.card_powersetCard, mul_assoc, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  simp [t, σ, ← hkl, show s.card = k by simpa using hs, Finset.card_compl]

  -- have hrw : ∀ x ∈ Finset.powersetCard k (Finset.univ : Finset X), (t x).card = (A.card ^ k)




  -- have : Fintype.card {X : Finset (Fin n) // X.card = k} = n.choose k := by
  --   rw [Fintype.card_finset_len]
  --   simp
