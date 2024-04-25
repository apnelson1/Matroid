import Matroid.Minor.Basic
import Matroid.Minor.RelRank
import Matroid.Constructions.Basic

namespace Matroid

open Set PartialEquiv

variable {α β β' : Type*} {M : Matroid α} {N : Matroid β} {C D : Set α}
section Iso

/-- Deletions of isomorphic matroids are isomorphic. TODO : Actually define as a term. -/
noncomputable def Iso.delete (e : Iso M N) (hD : D ⊆ M.E) :
    Iso (M ⧹ D) (N ⧹ e '' D) := by
  convert Iso.restrict e (M.E \ D) using 1
  rw [e.injOn_ground.image_diff hD, e.image_ground, ← restrict_compl]

noncomputable def Iso.contract (e : Iso M N) (hC : C ⊆ M.E) :
    Iso (M ⧸ C) (N ⧸ e '' C) :=
  (e.dual.delete hC).dual

/-- We have `N ≤i M` if `M` has an `N`-minor; i.e. `N` is isomorphic to a minor of `M`. This is
  defined to be type-heterogeneous.  -/
def IsoMinor (N : Matroid β) (M : Matroid α) : Prop :=
  ∃ M' : Matroid α, M' ≤m M ∧ N ≅ M'

infixl:50 " ≤i " => Matroid.IsoMinor

instance isoMinor_refl : IsRefl (Matroid α) (· ≤i ·) :=
  ⟨fun M ↦ ⟨M, Minor.refl, IsIso.refl M⟩⟩

theorem IsIso.isoMinor (h : M ≅ N) : M ≤i N :=
  ⟨N, Minor.refl, h⟩

theorem Iso.isoMinor (e : Iso N M) : N ≤i M :=
  e.isIso.isoMinor

@[simp] theorem emptyOn_isoMinor (α : Type*) (M : Matroid β) : emptyOn α ≤i M := by
  refine ⟨emptyOn β, ?_, isIso_emptyOn_emptyOn _ _⟩
  rw [← M.delete_ground_self]
  apply delete_minor

@[simp] theorem isoMinor_emptyOn_iff : M ≤i emptyOn β ↔ M = emptyOn α := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨N, hN, hMN⟩ := h
    obtain rfl := minor_emptyOn_iff.1 hN
    rwa [isIso_emptyOn_iff] at hMN
  rintro rfl
  apply emptyOn_isoMinor

theorem Minor.trans_isIso {M N : Matroid α} {M' : Matroid β} (h : N ≤m M) (hi : M ≅ M') :
    N ≤i M' := by
  obtain (⟨rfl,rfl⟩ | ⟨-, -, ⟨i⟩⟩) := hi.empty_or_nonempty_iso
  · simpa using h
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h
  exact ⟨_, contract_delete_minor _ _ _,
    ((i.contract hC).delete (subset_diff.2 ⟨hD, hCD.symm⟩)).isIso⟩

theorem Minor.isoMinor {M N : Matroid α} (h : N ≤m M) : N ≤i M :=
  ⟨N, h, (Iso.refl N).isIso⟩

theorem IsoMinor.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂}
    {M₃ : Matroid α₃} (h : M₁ ≤i M₂) (h' : M₂ ≤i M₃) : M₁ ≤i M₃ := by
  obtain ⟨M₂', hM₂'M₃, i'⟩ := h'
  obtain ⟨M₁', hM₁'M₂, i''⟩ := h
  obtain ⟨N, hN, iN⟩ := hM₁'M₂.trans_isIso i'
  exact ⟨N, hN.trans hM₂'M₃, i''.trans iN⟩

theorem Iso.trans_isoMinor {N' : Matroid β'} (e : Iso N N') (h : N' ≤i M) : N ≤i M :=
  e.isoMinor.trans h

theorem IsoMinor.dual (h : N ≤i M) : N✶ ≤i M✶ :=
  let ⟨N', hN', hN'M⟩ := h
  ⟨N'✶, hN'.dual, hN'M.dual⟩

theorem isoMinor_dual_iff : N✶ ≤i M✶ ↔ N ≤i M :=
  ⟨fun h ↦ by rw [← dual_dual M, ← dual_dual N]; exact h.dual, IsoMinor.dual⟩

theorem IsoMinor.erk_le_erk (h : N ≤i M) : N.erk ≤ M.erk := by
  obtain ⟨N', hN', hNM⟩ := h
  exact hNM.erk_eq_erk.le.trans hN'.erk_le

theorem IsoMinor.encard_ground_le_encard_ground (h : N ≤i M) : N.E.encard ≤ M.E.encard := by
  obtain ⟨N', hN', (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩)⟩ := h; simp
  have hss := encard_le_card <| e.image_ground.subset.trans hN'.subset
  rwa [e.injOn_ground.encard_image] at hss

end Iso

section IsoRestr

/-- Type-heterogeneous statement that `N` is isomorphic to a restriction of `M` -/
def IsoRestr (N : Matroid β) (M : Matroid α) : Prop :=
  ∃ M' : Matroid α, M' ≤r M ∧ N ≅ M'

infixl:50 " ≤ir " => Matroid.IsoRestr

theorem IsoRestr.isoMinor (h : N ≤ir M) : N ≤i M := by
  obtain ⟨M', hMM', hNM'⟩ := h
  exact ⟨M', hMM'.minor, hNM'⟩

theorem Restriction.IsoRestr {N M : Matroid α} (h : N ≤r M) : N ≤ir M :=
  ⟨N, h, IsIso.refl N⟩

theorem IsoRestr.refl (M : Matroid α) : M ≤ir M :=
  Restriction.refl.IsoRestr

theorem IsIso.isoRestr (h : N ≅ M) : M ≤ir N :=
  ⟨N, Restriction.refl, h.symm⟩

@[simp] theorem emptyOn_isoRestr (β : Type*) (M : Matroid α) : emptyOn β ≤ir M :=
  ⟨emptyOn α, by simp only [emptyOn_restriction], by simp only [isIso_emptyOn_iff]⟩

@[simp] theorem isoRestr_emptyOn_iff {M : Matroid α} : M ≤ir emptyOn β ↔ M = emptyOn α :=
  ⟨fun h ↦ isoMinor_emptyOn_iff.1 h.isoMinor, by rintro rfl; simp⟩

theorem Restriction.trans_isIso {N M : Matroid α} {M' : Matroid β} (h : N ≤r M) (h' : M ≅ M') :
    N ≤ir M' := by
  obtain (⟨rfl,rfl⟩ | ⟨⟨i⟩⟩) := h'
  · simpa using h
  obtain ⟨D, hD, rfl⟩ := h.exists_eq_delete
  exact ⟨_, delete_restriction _ _, (i.delete hD).isIso⟩

theorem IsoRestr.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (h₁₂ : M₁ ≤ir M₂) (h₂₃ : M₂ ≤ir M₃) : M₁ ≤ir M₃ := by
  obtain ⟨N₁, hN₁M₂, hN₁M₁⟩ := h₁₂
  obtain ⟨N₂, hN₂M₃, hN₂M₂⟩ := h₂₃
  obtain ⟨N₁', hN₁'N₂, hN₁N₁'⟩ := hN₁M₂.trans_isIso hN₂M₂
  exact ⟨N₁', hN₁'N₂.trans hN₂M₃, hN₁M₁.trans hN₁N₁'⟩

theorem isoMinor_iff_exists_contract_isoRestr {N : Matroid α} {M : Matroid β} :
    N ≤i M ↔ ∃ C, M.Indep C ∧ N ≤ir M ⧸ C := by
  refine ⟨fun h ↦ ?_, fun ⟨C, _, hN⟩ ↦ hN.isoMinor.trans (M.contract_minor C).isoMinor ⟩
  obtain ⟨N', hN'M, hi⟩ := h
  obtain ⟨C, hC, hN', -⟩ := hN'M.exists_contract_spanning_restrict
  exact ⟨C, hC, ⟨_, hN', hi⟩⟩

end IsoRestr

section free_loopy

theorem isoMinor_loopyOn_iff {E : Set β} :
    M ≤i loopyOn E ↔ M = loopyOn M.E ∧ Nonempty (M.E ↪ E) := by
  simp_rw [IsoMinor, minor_loopyOn_iff]
  refine ⟨fun ⟨M₀, hM₀, hM₀M⟩ ↦ ?_, fun ⟨hM, ⟨e⟩⟩ ↦ ?_⟩
  · rw [hM₀.1, isIso_loopyOn_iff] at hM₀M
    obtain ⟨e⟩ := hM₀M.2
    exact ⟨hM₀M.1, ⟨e.toEmbedding.trans ⟨inclusion hM₀.2, inclusion_injective hM₀.2⟩⟩⟩
  refine ⟨(loopyOn E) ↾ (((↑) : E → β) '' range e), by simp, ?_⟩
  simp only [loopyOn_restrict, isIso_loopyOn_iff, and_iff_right hM]
  convert Nonempty.intro <| Equiv.ofInjective (e.trans (Function.Embedding.subtype _))
    ((e.trans _).injective)
  rw [← image_univ, image_image, image_univ]
  rfl

theorem isoMinor_freeOn_iff {E : Set β} :
    M ≤i freeOn E ↔ M = freeOn M.E ∧ Nonempty (M.E ↪ E) := by
  rw [← isoMinor_dual_iff, freeOn_dual_eq, isoMinor_loopyOn_iff, dual_ground,
    ← eq_dual_iff_dual_eq, loopyOn_dual_eq]

theorem isoMinor_loopyOn_iff_of_finite {E : Set β} (hE : E.Finite) :
    M ≤i loopyOn E ↔ M = loopyOn M.E ∧ M.E.encard ≤ E.encard := by
  simp [Matroid.isoMinor_loopyOn_iff, ← hE.encard_le_iff_nonempty_embedding']

theorem isoMinor_freeOn_iff_of_finite {E : Set β} (hE : E.Finite) :
    M ≤i freeOn E ↔ M = freeOn M.E ∧ M.E.encard ≤ E.encard := by
  simp [Matroid.isoMinor_freeOn_iff, ← hE.encard_le_iff_nonempty_embedding']

theorem freeOn_isoMinor_iff {E : Set α} {M : Matroid β} :
    freeOn E ≤i M ↔ ∃ (f : E ↪ β), M.Indep (range f) := by
  simp_rw [IsoMinor, IsIso.comm (M := freeOn E), isIso_freeOn_iff]
  refine ⟨fun ⟨M₀, hM₀M, hM₀free, ⟨e⟩⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · use e.symm.toEmbedding.trans (Function.Embedding.subtype _)
    refine Indep.of_minor ?_ hM₀M
    nth_rw 1 [hM₀free ]
    simp only [freeOn_indep_iff]
    rintro _ ⟨x,hx,rfl⟩
    simp
  refine ⟨M ↾ (range f), M.restrict_minor hf.subset_ground, ?_⟩
  rw [restrict_ground_eq, ← indep_iff_restrict_eq_freeOn, and_iff_right hf]
  exact ⟨(Equiv.ofInjective f f.2).symm⟩

theorem freeOn_isoMinor_iff_of_finite {E : Set α} (hE : E.Finite) :
    freeOn E ≤i M ↔ E.encard ≤ M.erk := by
  rw [Matroid.freeOn_isoMinor_iff]
  refine ⟨fun ⟨f, hf⟩  ↦ ?_, fun h ↦ ?_⟩
  · rw [encard_congr <| Equiv.ofInjective f f.2, ← hf.er]
    apply er_le_erk
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, hE.encard_le_iff_nonempty_embedding] at h
  obtain ⟨e⟩ := h
  refine ⟨e.trans (Function.Embedding.subtype _), hB.indep.subset ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simp

theorem loopyOn_isoMinor_iff_of_finite {E : Set α} (hE : E.Finite) :
    loopyOn E ≤i M ↔ E.encard ≤ M✶.erk := by
  rw [← isoMinor_dual_iff, loopyOn_dual_eq, freeOn_isoMinor_iff_of_finite hE]

end free_loopy
