import Matroid.Minor.Basic
import Matroid.Constructions.Basic

namespace Matroid

open Set LocalEquiv

section Iso

variable {α β : Type*} {M : Matroid α} {N : Matroid β}

/-- Restrictions of isomorphic matroids are isomorphic -/
def Iso.restrict (e : Iso M N) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    Iso (M ↾ R) (N ↾ (e '' R)) :=
  iso_of_forall_indep (e.toLocalEquiv.restr R)
  (by simpa [restrict_ground_eq])
  (by rw [restr_target, restrict_ground_eq,
    image_eq_target_inter_inv_preimage _ (by rwa [e.source_eq])] )

  (by {
    simp only [restrict_indep_iff, restr_coe, image_subset_iff, and_imp]
    exact fun I hI hIR ↦ ⟨e.on_indep hI, hIR.trans (subset_preimage_image _ _)⟩ })
  (by {
    simp only [restrict_indep_iff, restr_coe_symm, image_subset_iff, and_imp]
    refine' fun I hI hIR ↦ ⟨e.symm.on_indep hI, hIR.trans _⟩
    rw [image_eq_target_inter_inv_preimage _ (by rwa [e.source_eq])]
    apply inter_subset_right })

@[simp] lemma Iso.restrict_apply (e : Iso M N) {R : Set α} (hR : R ⊆ M.E := by aesop_mat) :
    (e.restrict R hR).toLocalEquiv = e.toLocalEquiv.restr R := by
  simp [restrict]

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
  -- refine ⟨Equiv.Set.image (((↑) : E → β) ∘ e.toFun) _ ?_⟩
  -- have := Equiv.Set.image (((↑) : E → β ) ∘ e)






-- theorem loopyOn_isoMinor_iff {E : Set β} : loopyOn E ≤i M ↔ Nonempty (E ↪ M.cl ∅) := by
--   _

-- theorem loopyOn_isoMinor_iff {E : Set β} : loopyOn E ≤i M ↔ Nonempty (E ↪ M.cl ∅) := by
--   cases isEmpty_or_nonempty β
--   · simp only [eq_emptyOn, emptyOn_isoMinor, true_iff]
--     exact ⟨Function.Embedding.ofIsEmpty⟩
--   cases isEmpty_or_nonempty α
--   · rw [eq_emptyOn M, isoMinor_emptyOn_iff, ← ground_eq_empty_iff, loopyOn_ground, emptyOn_cl_eq]
--     constructor
--     · rintro rfl; exact ⟨Function.Embedding.ofIsEmpty⟩
--     intro ⟨h⟩
--     rw [eq_empty_iff_forall_not_mem]
--     intro x hx
--     simpa using (h ⟨x,hx⟩).2
--   refine ⟨fun ⟨M', hM', hM'M⟩ ↦ ?_, fun h ↦ ?_⟩
--   · refine ⟨⟨fun x ↦ ⟨hM'M.iso x, ?_⟩, ?_⟩⟩
--     · rw [← loop_iff_mem_cl_empty, ← not_nonloop_iff _, ← indep_singleton, ← image_singleton]
--       have' := hM'M.iso.on_indep_iff _



end free_loopy
