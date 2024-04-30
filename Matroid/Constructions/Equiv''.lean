import Matroid.Map
import Matroid.ForMathlib.Function

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

open Set Function Set.Notation

namespace Matroid

structure Iso (M : Matroid α) (N : Matroid β) where
  toEquiv : M.E ≃ N.E
  indep_image_iff' : ∀ (I : Set M.E), M.Indep I ↔ N.Indep (↑(toEquiv '' I))

instance : EquivLike (Iso M N) M.E N.E where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.1.leftInverse_symm
  right_inv f := f.1.rightInverse_symm
  coe_injective' := by
    rintro ⟨f, -⟩ ⟨g, -⟩
    simp only [DFunLike.coe_fn_eq, Iso.mk.injEq]
    exact fun h _ ↦ h

@[simp] theorem image_val_image_val_eq (f : α → β) (s : Set α) (x : Set s) :
    (↑) '' ((fun x : s ↦ (⟨f x, mem_image_of_mem _ x.2⟩ : f '' s)) '' x) = f '' x := by
  aesop

@[simp] theorem image_val_image_eq_image_image_val (s : Set α) (t : Set β) (f : s → t) (x : Set s) :
    ↑((f '' (s ↓∩ x))) = f '' ↑(s ↓∩ x) := by
  aesop

theorem eq_image_val_of_subset {s x : Set α} (hsx : x ⊆ s) : ∃ (y : Set s), x = ↑y :=
  ⟨s ↓∩ x, by simpa⟩

theorem image_val_preimage_val_of_subset {s x : Set α} (hsx : x ⊆ s) : ↑(s ↓∩ x) = x := by
  simpa

theorem Iso.indep_image_iff (e : Iso M N) (I : Set α) :
    M.Indep (M.E ↓∩ I) ↔ N.Indep ↑(e '' (M.E ↓∩ I)) :=
  e.indep_image_iff' (M.E ↓∩ I)

noncomputable def iso_map (M : Matroid α) (f : α → β) (hf : M.E.InjOn f) : M.Iso (M.map f hf) where
  toEquiv := Equiv.Set.imageOfInjOn _ _ hf
  indep_image_iff' := by
    intro I
    simp only [Equiv.Set.imageOfInjOn, map_ground, Equiv.coe_fn_mk, image_val_image_val_eq]
    rw [map_image_indep_iff <| Subtype.coe_image_subset M.E I]

def iso_of_base_iff_base (e : M.E ≃ N.E) (he : ∀ (B : Set M.E), M.Base B ↔ N.Base (↑(e '' B))) :
  Iso M N where
    toEquiv := e
    indep_image_iff' := by
      intro I
      rw [indep_iff_subset_base, indep_iff_subset_base]
      refine ⟨fun ⟨B, hB, hIB⟩ ↦ ?_, fun ⟨B, hB, hIB⟩ ↦ ?_⟩
      · obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
        refine ⟨↑(e '' B), (he B).1 hB, ?_⟩
        rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
        exact image_subset e hIB
      obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
      refine ⟨↑(e.symm '' B), by rwa [he, e.image_symm_image] , ?_⟩
      rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
      simpa using hIB

theorem Iso.base_image {B : Set α} (e : Iso M N) (hB : M.Base B) : N.Base (↑(e '' (M.E ↓∩ B))) := by
  rw [base_iff_maximal_indep, ← e.indep_image_iff B,
    image_val_preimage_val_of_subset hB.subset_ground, and_iff_right hB.indep]
  intro I hI
  obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
  obtain ⟨I, rfl⟩ := eq_image_val_of_subset hI.subset_ground
  rw [image_val_image_eq_image_image_val, image_subset_image_iff Subtype.val_injective,
    image_eq_image Subtype.val_injective]
  -- have := hB.eq_of_subset_indep (e.indephI
  -- have : ↑(e '' M.E ↓∩ B) = e '' ↑(M.E ↓∩ B) := by
  --   ext x
  --   aesop
