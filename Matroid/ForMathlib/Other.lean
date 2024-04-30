import Matroid.ForMathlib.PartialEquiv
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol

variable {α β : Type*} {s s₁ s₂ t t' : Set α} {f : α → β }

open Set Function


section Lattice



lemma biUnion_insert_eq {X : Set α} (hX : X.Nonempty) (Y : Set α) :
    ⋃ (x ∈ X), (insert x Y) = X ∪ Y := by
  have := hX.to_subtype
  simp_rw [← singleton_union, biUnion_eq_iUnion, ← iUnion_union, iUnion_singleton_eq_range,
    Subtype.range_coe_subtype, setOf_mem_eq]


theorem Equiv.exists_bijOn [Nonempty β] {s : Set α} {t : Set β} (e : s ≃ t) :
    ∃ f, BijOn f s t ∧ ∀ x, e x = f x := by
  classical
  use fun x ↦ if hx : x ∈ s then e ⟨x,hx⟩ else Classical.arbitrary β
  refine ⟨BijOn.mk (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_) (fun y hy ↦ ⟨e.symm ⟨y, hy⟩, by simp⟩),
    by simp⟩
  · rw [dif_pos hx]; exact Subtype.prop _
  simpa [dif_pos hx, dif_pos hy, Subtype.coe_inj] using hxy

theorem Set.Finite.encard_le_iff_nonempty_embedding {s : Set α} {t : Set β} (hs : s.Finite) :
    s.encard ≤ t.encard ↔ Nonempty (s ↪ t) := by
  cases isEmpty_or_nonempty β
  · simp only [t.eq_empty_of_isEmpty, encard_empty, nonpos_iff_eq_zero, encard_eq_zero]
    constructor; rintro rfl; exact ⟨Embedding.ofIsEmpty⟩
    rintro ⟨e⟩
    exact isEmpty_coe_sort.1 e.toFun.isEmpty
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.enccard_le⟩
  obtain ⟨f, hst, hf⟩ := hs.exists_injOn_of_encard_le h
  exact ⟨codRestrict (s.restrict f) t (fun x ↦ by aesop), hf.injective.codRestrict _⟩

theorem Set.Finite.encard_le_iff_nonempty_embedding' {s : Set α} {t : Set β} (ht : t.Finite) :
    s.encard ≤ t.encard ↔ Nonempty (s ↪ t) := by
  obtain (hs | hs) := s.finite_or_infinite
  · exact hs.encard_le_iff_nonempty_embedding
  rw [hs.encard_eq, top_le_iff, encard_eq_top_iff, Set.Infinite, iff_true_intro ht,
    not_true, false_iff]
  rintro ⟨e⟩
  have hle := e.enccard_le
  rw [hs.encard_eq, top_le_iff, encard_eq_top_iff] at hle
  exact hle ht

@[simp] theorem encard_univ_fin (a : ℕ) : (univ : Set (Fin a)).encard = a := by
  simp [encard_eq_coe_toFinset_card]




  -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩


theorem Set.Finite.encard_eq_iff_nonempty_equiv {s : Set α} {t : Set β} (ht : t.Finite) :
    s.encard = t.encard ↔ Nonempty (s ≃ t) := by
  cases isEmpty_or_nonempty α
  · simp only [s.eq_empty_of_isEmpty, eq_comm (a := (0 : ℕ∞)), encard_empty, encard_eq_zero]
    constructor; rintro rfl; exact ⟨Equiv.equivOfIsEmpty _ _⟩
    rintro ⟨e⟩
    exact isEmpty_coe_sort.1 e.symm.toFun.isEmpty
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ encard_congr e⟩
  obtain ⟨f, hf⟩ := ht.exists_bijOn_of_encard_eq h.symm
  exact Nonempty.intro <| (hf.equiv _).symm





-- @[simp] theorem PartialEquiv.ofSetEquiv_apply_symm [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
--     (e : s ≃ t) (y : t) : (PartialEquiv.ofSetEquiv e).symm y = e.symm y := by

--   simp only [ofSetEquiv, Subtype.forall, BijOn.toPartialEquiv_symm_apply]

--   have := ((Classical.choose_spec e.exists_bijOn).2 (e.symm y)).symm





  -- use Function.extend Subtype.val (fun x ↦ (e x).1) (fun _ ↦ Classical.arbitrary β)
  -- simp

end Lattice
section Swap

variable {e f : α}

theorem Equiv.swap_image_eq_self [DecidableEq α] {S : Set α} (hef : e ∈ S ↔ f ∈ S) :
    (Equiv.swap e f) '' S = S := by
  ext x
  rw [image_equiv_eq_preimage_symm, mem_preimage, Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with hxe hxf
  · rwa [hxe, Iff.comm]
  · rwa [hxf]
  rfl

theorem Equiv.swap_image_eq_exchange [DecidableEq α] {S : Set α} (he : e ∈ S) (hf : f ∉ S) :
    (Equiv.swap e f) '' S = insert f (S \ {e}) := by
  ext x
  rw [image_equiv_eq_preimage_symm, mem_preimage, Equiv.symm_swap, Equiv.swap_apply_def,
    mem_insert_iff, mem_diff]
  split_ifs with hxe hxf
  · subst hxe
    simp [he, hf, (show x ≠ f by rintro rfl; exact hf he)]
  · subst hxf
    simp [he]
  simp [hxe, iff_false_intro hxf]

end Swap



-- theorem filter_preimage_eq {e f : α} [DecidableEq α] {S : Set α} (he : e ∈ S) (hf : f ∈ S)
--     (h_ne : e ≠ f) : (fun x ↦ if (x = e) then f else x) ⁻¹' (S \ {e}) = S := by
--   ext x
--   simp only [preimage_diff, mem_diff, mem_preimage, mem_singleton_iff]
--   split_ifs with hxe
--   · subst hxe
--     exact iff_of_true ⟨hf, h_ne.symm⟩ he
--   rw [and_iff_left hxe]

section Matrix

variable {m n R : Type} [Semiring R]

/-- For a semiring `R`, the modules `(n → R)` and `Matrix Unit n R` are linearly equivalent. -/
def Matrix.row_linearEquiv (n R : Type) [Semiring R] : (n → R) ≃ₗ[R] Matrix Unit n R where
  toFun := Matrix.row
  invFun A i := A () i
  map_add' := Matrix.row_add
  map_smul' := Matrix.row_smul
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

@[simp] theorem Matrix.row_linearEquiv_apply (x : n → R) :
    Matrix.row_linearEquiv n R x = Matrix.row x := rfl

@[simp] theorem Matrix.row_linearEquiv_apply_symm (A : Matrix Unit n R) :
    (Matrix.row_linearEquiv n R).symm A = A () := rfl

/-- For a semiring `R`, the modules `(m → R)` and `Matrix m Unit r` are linearly equivalent. -/
def Matrix.col_linearEquiv (m R : Type) [Semiring R] : (m → R) ≃ₗ[R] Matrix m Unit R where
  toFun := Matrix.col
  invFun A i := A i ()
  map_add' := Matrix.col_add
  map_smul' := Matrix.col_smul
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

@[simp] theorem Matrix.col_linearEquiv_apply (x : m → R) :
    Matrix.col_linearEquiv m R x = Matrix.col x := rfl

@[simp] theorem Matrix.col_linearEquiv_apply_symm (A : Matrix m Unit R) (i : m) :
    (Matrix.col_linearEquiv m R).symm A i = A i () := rfl

theorem exists_eq_image_subset_of_subset_image {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (hst : t ⊆ f '' s) : ∃ t₀, t₀ ⊆ s ∧ t = f '' t₀ := by
  refine ⟨f ⁻¹' t ∩ s, inter_subset_right _ _, subset_antisymm (fun x hxt ↦ ?_) ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hst hxt
    exact ⟨a, mem_inter hxt ha, rfl⟩
  simp [image_subset_iff, inter_subset_left]

theorem Set.restrict_id_eq (s : Set α) : s.restrict id = Subtype.val := rfl

abbrev Set.incl (s : Set α) : s → α := Subtype.val

@[simp] theorem isEmpty_fin_iff {b : ℕ} : IsEmpty (Fin b) ↔ b = 0 := by
  cases b <;> simp [Fin.isEmpty]
