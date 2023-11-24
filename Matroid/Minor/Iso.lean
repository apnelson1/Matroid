import Matroid.Minor.Basic
import Matroid.Constructions.Basic

namespace Matroid

open Set LocalEquiv

section Iso

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

/-- Deletions of isomorphic matroids are isomorphic. TODO : Actually define as a term. -/
noncomputable def Iso.delete (e : Iso M N) (hD : D ⊆ M.E) :
    Iso (M ⟍ D) (N ⟍ e '' D) := by
  convert Iso.restrict e (M.E \ D) using 1
  rw [e.injOn_ground.image_diff hD, e.image_ground, ←restrict_compl]

noncomputable def Iso.contract (e : Iso M N) (hC : C ⊆ M.E) :
    Iso (M ⟋ C) (N ⟋ e '' C) :=
  (e.dual.delete hC).dual

/-- We have `N ≤i M` if `M` has an `N`-minor; i.e. `N` is isomorphic to a minor of `M`. This is
  defined to be type-heterogeneous.  -/
def IsoMinor (N : Matroid β) (M : Matroid α) : Prop :=
  ∃ M' : Matroid α, M' ≤m M ∧ N ≅ M'

infixl:50 " ≤i " => Matroid.IsoMinor

instance isoMinor_refl : IsRefl (Matroid α) (· ≤i ·) :=
  ⟨fun M ↦ ⟨M, refl M, IsIso.refl M⟩⟩

theorem IsIso.isoMinor (h : M ≅ N) : M ≤i N :=
  ⟨N, Minor.refl _, h⟩

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
  obtain (hα | hα) := isEmpty_or_nonempty α
  · simp
  obtain (hβ | hβ) := isEmpty_or_nonempty β
  · simp only [eq_emptyOn, isIso_emptyOn_iff, isoMinor_emptyOn_iff] at *
    rwa [hi, minor_emptyOn_iff] at h
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h
  exact ⟨_, contract_delete_minor _ _ _,
    ((hi.iso.contract hC).delete (subset_diff.2 ⟨hD, hCD.symm⟩)).isIso⟩

theorem Minor.isoMinor {M N : Matroid α} (h : N ≤m M) : N ≤i M :=
  ⟨N, h, (Iso.refl N).isIso⟩

theorem IsoMinor.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂}
    {M₃ : Matroid α₃} (h : M₁ ≤i M₂) (h' : M₂ ≤i M₃) : M₁ ≤i M₃ := by
  cases isEmpty_or_nonempty α₁
  · simp
  cases isEmpty_or_nonempty α₂
  · simp only [eq_emptyOn, isoMinor_emptyOn_iff] at h; simp [h]
  cases isEmpty_or_nonempty α₃
  · simp only [eq_emptyOn, isoMinor_emptyOn_iff] at h' ⊢
    rwa [h', isoMinor_emptyOn_iff] at h
  obtain ⟨M₂', hM₂'M₃, i'⟩ := h'
  obtain ⟨M₁', hM₁'M₂, i''⟩ := h
  obtain ⟨N, hN, iN⟩ := hM₁'M₂.trans_isIso i'
  exact ⟨N, hN.trans hM₂'M₃, i''.trans iN⟩

theorem Iso.trans_isoMinor {N' : Matroid β'} (e : Iso N N') (h : N' ≤i M) : N ≤i M :=
  e.isoMinor.trans h

theorem IsoMinor.dual (h : N ≤i M) : N﹡ ≤i M﹡ :=
  let ⟨N', hN', hN'M⟩ := h
  ⟨N'﹡, hN'.dual, hN'M.dual⟩

theorem isoMinor_dual_iff : N﹡ ≤i M﹡ ↔ N ≤i M :=
  ⟨fun h ↦ by rw [← dual_dual M, ← dual_dual N]; exact h.dual, IsoMinor.dual⟩

theorem IsoMinor.erk_le_erk (h : N ≤i M) : N.erk ≤ M.erk := by
  obtain ⟨N', hN', hNM⟩ := h
  exact hNM.erk_eq_erk.le.trans hN'.erk_le

theorem IsoMinor.encard_ground_le_encard_ground (h : N ≤i M) : N.E.encard ≤ M.E.encard := by
  obtain ⟨N', hN', (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩)⟩ := h; simp
  have hss := encard_le_of_subset <| e.image_ground.subset.trans hN'.subset
  rwa [e.injOn_ground.encard_image] at hss

end Iso

section free_loopy

variable {α β : Type*} {M : Matroid α}

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
    dual_eq_comm, eq_comm, loopyOn_dual_eq]

theorem isoMinor_loopyOn_iff_of_finite {E : Set β} (hE : E.Finite) :
    M ≤i loopyOn E ↔ M = loopyOn M.E ∧ M.E.encard ≤ E.encard := by
  simp [Matroid.isoMinor_loopyOn_iff, ←hE.encard_le_iff_nonempty_embedding']

theorem isoMinor_freeOn_iff_of_finite {E : Set β} (hE : E.Finite) :
    M ≤i freeOn E ↔ M = freeOn M.E ∧ M.E.encard ≤ E.encard := by
  simp [Matroid.isoMinor_freeOn_iff, ←hE.encard_le_iff_nonempty_embedding']

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
  · rw [encard_congr <| Equiv.ofInjective f f.2, ←hf.er]
    apply er_le_erk
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, hE.encard_le_iff_nonempty_embedding] at h
  obtain ⟨e⟩ := h
  refine ⟨e.trans (Function.Embedding.subtype _), hB.indep.subset ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simp

theorem loopyOn_isoMinor_iff_of_finite {E : Set α} (hE : E.Finite) :
    loopyOn E ≤i M ↔ E.encard ≤ M﹡.erk := by
  rw [← isoMinor_dual_iff, loopyOn_dual_eq, freeOn_isoMinor_iff_of_finite hE]

end free_loopy

section Property

universe u

variable {α β : Type u} {M : Matroid α} {N : Matroid β} (P : ∀ {η : Type u}, Matroid η → Prop)

def IsoMinorClosed (P : ∀ {α : Type*}, Matroid α → Prop) : Prop := MinorClosed P ∧ Invariant P

def ExMinor (N : Matroid β) {α : Type*} (M : Matroid α) : Prop := ¬ (N ≤i M)

theorem exMinor_isoMinorClosed {N₀ : Matroid η} : IsoMinorClosed (ExMinor N₀) := by
  refine ⟨fun {α} N M hNM h_ex h_minor ↦ h_ex <| h_minor.trans hNM.isoMinor,
    fun {α} {β} M M' hMM' ↦ ?_⟩
  simp only [ExMinor, eq_iff_iff, not_iff_not]
  exact ⟨fun h ↦ h.trans hMM'.isoMinor, fun h ↦ h.trans hMM'.symm.isoMinor⟩


end Property
