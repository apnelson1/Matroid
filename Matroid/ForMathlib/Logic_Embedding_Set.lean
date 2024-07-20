import Mathlib.Logic.Embedding.Set
import Mathlib.Tactic
import Mathlib.Data.Set.Subset

open Set Function Set.Notation

section embeddingInsert

variable {α β γ : Type*} {a : α} {b : β} {s : Set α} {f : s ↪ β}





@[simp] theorem Equiv.ofInjective_image (f : α → β) (hf : f.Injective) (s : Set α) :
    ((Equiv.ofInjective f hf) '' s) = f '' s := by
  ext; simp



-- this should be elsewhere.
theorem Function.Embedding.range_trans (f : α ↪ β) (g : β ↪ γ) :
    range (f.trans g) = g '' (range f) :=
  range_comp g f

@[simp] theorem Function.Embedding.preimage_trans (f : α ↪ β) (g : β ↪ γ) (s : Set γ) :
    (f.trans g) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := rfl

theorem Function.Embedding.image_trans (f : α ↪ β) (g : β ↪ γ) :
    (f.trans g) '' s = g '' (f '' s) :=
  Eq.symm <| image_image _ _ _


theorem Set.embeddingOfSubset_apply {s t : Set α} (hst : s ⊆ t) (x : s) :
    embeddingOfSubset s t hst x = ⟨x.1, hst x.2⟩ := rfl

theorem Set.embeddingOfSubset_image {s t : Set α} (hst : s ⊆ t) (r : Set s) :
    (embeddingOfSubset s t hst) '' r = {x : t | x.1 ∈ (r : Set α)} := by
  ext ⟨x,h⟩; simp [embeddingOfSubset_apply]

theorem Set.embeddingOfSubset_preimage {s t : Set α} (hst : s ⊆ t) (r : Set t) :
    (embeddingOfSubset s t hst) ⁻¹' r = {x : s | x.1 ∈ (r : Set α)} := by
  ext ⟨x,h⟩; simp [hst h, embeddingOfSubset_apply]

@[simp] theorem Set.embeddingOfSubset_coeFun {s t : Set α} (hst : s ⊆ t) :
    (embeddingOfSubset s t hst : s → t) = inclusion hst := rfl

@[simp] theorem image_val_image_comp_inclusion (s : Set α) (r : Set s) {t t' : Set β} (ht : t ⊆ t')
    (f : s → t) : Subtype.val '' ((fun x ↦ inclusion ht (f x)) '' r) = ↑(f '' r) := by
  simp_rw [image_image, coe_inclusion]

@[simp] theorem image_val_range_comp_inclusion (s : Set α) {t t' : Set β} (ht : t ⊆ t') (
    f : s → t) : Subtype.val '' (range (fun x ↦ inclusion ht (f x))) = ↑(range f) := by
  rw [← image_univ, image_val_image_comp_inclusion]
  simp

@[simp] theorem image_val_image_inclusion {s t : Set α} (hst : s ⊆ t) (r : Set s) :
    Subtype.val '' (inclusion hst '' r) = r :=
  image_image Subtype.val (inclusion hst) r

@[simp] lemma iUnion_preimage_image_sigmaMk_eq {ι : Type*} {α : ι → Type*}
    {f : (i : ι) → Set (α i)} {j : ι} : ⋃ i, Sigma.mk j ⁻¹' (Sigma.mk i '' (f i)) = f j := by
  aesop



-- this is an `apply_coe` lemma in mathlib that should be renamed.
-- @[simp] theorem embeddingOfSubset_apply_val {s t : Set α} (hst : s ⊆ t) (x : s) :
--     (embeddingOfSubset s t hst x).1 = x.1 := rfl

/-- The same as `Function.Embedding.subtype`, but for the special case of a set coercion.
Can be more convenient for rewriting.  -/
@[simps!] def Function.Embedding.setSubtype {α : Type*} (s : Set α) : s ↪ α :=
  Embedding.subtype s

@[simp] theorem Function.Embedding.preimage_setSubtype (s : Set α) (x : Set α) :
    ((Embedding.setSubtype s) ⁻¹' x : Set s) = s ↓∩ x := rfl

@[simp] theorem Function.Embedding.image_setSubtype (s : Set α) (x : Set s) :
    Embedding.setSubtype s '' x = ↑x := rfl

@[simp] theorem Function.Embedding.range_setSubtype_eq (s : Set α) :
    Set.range (Embedding.setSubtype s) = s :=
  Subtype.range_val


section embeddingInsert

/-- An embedding defined on a coerced set can be extended to an embedding on an insertion. -/
noncomputable def Subtype.embeddingInsert (f : s ↪ β) (ha : a ∉ s) (hb : b ∉ range f) :
    ↑(insert a s) ↪ β where
  toFun := Function.extend (inclusion (subset_insert a s)) f (fun _ ↦ b)
  inj' := by
    have hinj := (inclusion_injective (subset_insert a s))
    have aux : ∀ (x : ↑(insert a s)),
        x = ⟨a, mem_insert _ _⟩ ∨ ∃ (x₀ : s), x = inclusion (subset_insert a s) x₀ := by
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
  nth_rw 1 [show x = inclusion (subset_insert a s) ⟨x,hx⟩ from rfl]
  simp only [embeddingInsert,  Embedding.coeFn_mk]
  rw [(inclusion_injective (subset_insert a s)).extend_apply]

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
  rw [range_extend (inclusion_injective (subset_insert a s)), range_inclusion]
  simp_rw [← union_singleton]
  convert rfl
  ext x
  simp [ha, eq_comm (a := x)]

end embeddingInsert


section EquivSubset

/-- The restriction of an equivalence `e : s ≃ t` to a subset `a` of `s` and its image `b`. -/
@[simps] def Equiv.subsetEquivSubset {α β : Type*} {a s : Set α} {b t : Set β} (e : s ≃ t)
    (has : a ⊆ s) (hbt : b ⊆ t) (h_eq : ∀ x, (e x).1 ∈ b ↔ x.1 ∈ a) : a ≃ b where
  toFun x := ⟨(e ⟨x.1, has x.2⟩).1, by simp [h_eq]⟩
  invFun x := ⟨(e.symm ⟨x.1, hbt x.2⟩).1, by simp [← h_eq]⟩
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem Equiv.subsetEquivSubset_image_val {α β : Type*} {a s : Set α} {b t : Set β}
    (e : s ≃ t) (has) (hbt : b ⊆ t) (h_eq) (u : Set a) :
    Subtype.val '' (e.subsetEquivSubset has hbt h_eq '' u) = e '' ((inclusion has) '' u) := by
  ext x
  simp only [mem_image, mem_image_equiv, Subtype.exists, exists_and_right, exists_eq_right,
    inclusion_mk, Subtype.mk.injEq, exists_and_right, exists_eq_right, exists_and_left,
    subsetEquivSubset, coe_fn_mk, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨hxb, ⟨v, hva, hvu, rfl⟩⟩
    simp [has hva, hva, hvu]
  simp only [forall_exists_index, and_imp]
  rintro hxt v hva hvu hvs hvx
  refine ⟨?_, ⟨v, hva, hvu, by rw [hvx]⟩⟩
  specialize h_eq ⟨v, hvs⟩
  rw [hvx, Subtype.coe_mk, Subtype.coe_mk] at h_eq
  rwa [h_eq]

@[simps!] def Equiv.subsetEquivImage {α β : Type*} {a s : Set α} {t : Set β} (e : s ≃ t)
    (has : a ⊆ s) : a ≃ Subtype.val '' (e '' (s ↓∩ a)) :=
  e.subsetEquivSubset has (by simp) (by simp)




end EquivSubset
