import Mathlib.Logic.Embedding.Set
import Mathlib.Tactic

open Set Function

section embeddingInsert

variable {α β γ : Type*} {a : α} {b : β} {s : Set α} {f : s ↪ β}


@[simp] theorem range_embeddingOfSubset {s t : Set α} (hst : s ⊆ t) :
    range (embeddingOfSubset s t hst) = {x | x.1 ∈ s} := by
  ext ⟨x,hx⟩; simp [embeddingOfSubset]

theorem embeddingOfSubset_apply {s t : Set α} (hst : s ⊆ t) (x : s) :
    embeddingOfSubset s t hst x = ⟨x.1, hst x.2⟩ := rfl

-- this should be elsewhere.
theorem Embedding.range_trans {f : α ↪ β} {g : β ↪ γ} : range (f.trans g) = g '' (range f) :=
  range_comp g f

-- this is an `apply_coe` lemma in mathlib that should be renamed.
-- @[simp] theorem embeddingOfSubset_apply_val {s t : Set α} (hst : s ⊆ t) (x : s) :
--     (embeddingOfSubset s t hst x).1 = x.1 := rfl

/-- An embedding defined on a coerced set can be extended to an embedding on an insertion. -/
noncomputable def Subtype.embeddingInsert (f : s ↪ β) (ha : a ∉ s) (hb : b ∉ range f) :
    ↑(insert a s) ↪ β where
  toFun := Function.extend (embeddingOfSubset _ _ (subset_insert a s)) f (fun _ ↦ b)
  inj' := by
    have hinj := (embeddingOfSubset _ _ (subset_insert a s)).injective
    have aux : ∀ (x : ↑(insert a s)),
        x = ⟨a, mem_insert _ _⟩ ∨ ∃ (x₀ : s), x = embeddingOfSubset _ _ (subset_insert a s) x₀ := by
      rintro ⟨x, (rfl | hx)⟩; exact .inl rfl; exact .inr ⟨⟨x,hx⟩, rfl⟩
    rintro x y hxy
    obtain (rfl | ⟨x₀,rfl⟩) := aux x
    · rw [extend_apply' _ _ _ (by simpa [embeddingOfSubset])] at hxy
      obtain (rfl | ⟨y₀,rfl⟩) := aux y
      · rfl
      rw [hinj.extend_apply] at hxy
      simp [hxy] at hb
    rw [hinj.extend_apply] at hxy
    obtain (rfl | ⟨y₀,rfl⟩) := aux y
    · rw [extend_apply' _ _ _ (by simpa [embeddingOfSubset])] at hxy
      simp [hxy.symm] at hb
    rw [hinj.extend_apply, f.apply_eq_iff_eq] at hxy
    rw [hxy]

theorem Subtype.embeddingInsert_apply_mem (f : s ↪ β) (ha : a ∉ s) (hb : b ∉ range f)
    {x : ↑(insert a s)} (hx : x.1 ∈ s) : (Subtype.embeddingInsert f ha hb) x = f ⟨x,hx⟩ := by
  nth_rw 1 [show x = embeddingOfSubset _ _ (subset_insert a s) ⟨x,hx⟩ from rfl]
  simp [embeddingInsert, (embeddingOfSubset _ _ (subset_insert a s)).injective.extend_apply]

theorem Subtype.embeddingInsert_apply (f : s ↪ β) (ha : a ∉ s) (hb : b ∉ range f) :
    (Subtype.embeddingInsert f ha hb) ⟨a, mem_insert _ _⟩ = b := by
  simp only [embeddingInsert, Embedding.coeFn_mk]
  rw [extend_apply' _ _ _ (by simpa [embeddingOfSubset])]

theorem Subtype.embeddingInsert_apply' (f : s ↪ β) (ha : a ∉ s) (hb : b ∉ range f)
    {x : ↑(insert a s)} (hx : x.1 ∉ s) : (Subtype.embeddingInsert f ha hb) x = b := by
  obtain ⟨x, (rfl | h)⟩ := x
  · rw [Subtype.embeddingInsert_apply]
  exact (hx h).elim

theorem Subtype.embeddingInsert_apply_eq_ite (f : s ↪ β) (ha : a ∉ s) (hb : b ∉ range f)
    {x : ↑(insert a s)} [DecidablePred (· ∈ s)] :
    (Subtype.embeddingInsert f ha hb) x = if hx : x.1 ∈ s then f ⟨x,hx⟩ else b := by
  split_ifs with h
  · rw [embeddingInsert_apply_mem]
  rwa [embeddingInsert_apply']

@[simp] theorem Subtype.range_embeddingInsert (f : s ↪ β) (ha : a ∉ s) (hb : b ∉ range f) :
    range (Subtype.embeddingInsert f ha hb) = insert b (range f) := by
  simp only [embeddingInsert, Embedding.coeFn_mk]
  rw [range_extend (embeddingOfSubset _ _ (subset_insert a s)).injective, range_embeddingOfSubset]
  simp_rw [← union_singleton]
  convert rfl
  ext x
  simp [ha, eq_comm (a := x)]

end embeddingInsert
