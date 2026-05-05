import Matroid.Uniform.Finite

variable {α : Type*} {M : Matroid α} {E I B X Y C : Set α} {k : ℕ} {e f : α} {a b b' n : ℕ}

open Set

namespace Matroid



noncomputable def unif_isoRestr_unif (a : ℕ) (hbb' : b ≤ b') : unif a b ≤ir unif a b' :=
  let R : Set (Fin b') := range (Fin.castLE hbb')
  have hM : Nonempty (((unif a b') ↾ R) ≂ unif a b) := by
    refine nonempty_iso_unif_iff.2 ⟨R, ?_⟩
    suffices R.encard = b by simpa [ext_iff_indep]
    rw [show R = range (Fin.castLE hbb') from rfl, ← image_univ, Function.Injective.encard_image,
      encard_univ_fin]
    exact (Fin.castLEEmb hbb').injective
  hM.some.symm.isoRestr.trans ((unif a b').restrict_isRestriction R).isoRestr

noncomputable def unif_isoMinor_contr (a b d : ℕ) : unif a b ≤i unif (a+d) (b+d) := by
  have e := (unif_isoRestr_unif (b-a) (Nat.le_add_right b d)).isoMinor.dual
  rwa [unif_sub_dual, ← Nat.add_sub_add_right b d a, unif_sub_dual] at e

theorem unif_isoMinor_unif_iff {a₁ a₂ d₁ d₂ : ℕ} :
    Nonempty (unif a₁ (a₁ + d₁) ≤i unif a₂ (a₂ + d₂)) ↔ a₁ ≤ a₂ ∧ d₁ ≤ d₂ := by
  refine ⟨fun ⟨e⟩ ↦ ⟨by simpa using e.rank_le, by simpa using IsoMinor.rank_le e.dual⟩, fun h ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h.1
  exact ⟨(unif_isoMinor_contr a₁ (a₁ + d₁) j).trans (unif_isoRestr_unif _ (by linarith)).isoMinor⟩

theorem unif_isoMinor_unif_iff' {a₁ a₂ b₁ b₂ : ℕ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    Nonempty (unif a₁ b₁ ≤i unif a₂ b₂) ↔ a₁ ≤ a₂ ∧ b₁ - a₁ ≤ b₂ - a₂ := by
  obtain ⟨d₁, rfl⟩ := Nat.exists_eq_add_of_le h₁
  obtain ⟨d₂, rfl⟩ := Nat.exists_eq_add_of_le h₂
  rw [add_tsub_cancel_left, add_tsub_cancel_left, unif_isoMinor_unif_iff]

lemma unif_isoRestr_unifOn {a : ℕ} (hbb : b ≤ E.encard) :
    Nonempty (unif a b ≤ir (unifOn E a)) := by
  have hle : (unif a b).E.encard ≤ E.encard := by simpa
  obtain ⟨φ⟩ := (Finite.encard_le_iff_nonempty_embedding (by simp)).1 hle
  refine ⟨⟨φ, φ.injective, fun I ↦ ?_⟩⟩
  simp only [unif_ground_eq, unif_indep_iff, unifOn_ground_eq, unifOn_indep_iff, image_subset_iff,
    Subtype.coe_preimage_self, subset_univ, and_true, Subtype.val_injective.encard_image]
  rw [Function.Injective.encard_image (by exact φ.injective)]

def NoUniformMinor (M : Matroid α) (a b : ℕ) : Prop := IsEmpty (unif a b ≤i M)

@[simp] lemma not_noUniformMinor_iff {a b : ℕ} :
    ¬ M.NoUniformMinor a b ↔ Nonempty (unif a b ≤i M) := by
  simp [NoUniformMinor]

lemma NoUniformMinor.minor {N a b} (hM : M.NoUniformMinor a b) (hNM : N ≤m M) :
    N.NoUniformMinor a b := by
  contrapose! hM
  simp only [not_noUniformMinor_iff] at hM ⊢
  exact ⟨hM.some.trans_isMinor hNM⟩

set_option backward.isDefEq.respectTransparency false in
lemma nonempty_unif_isoRestr_unifOn (a : ℕ) {b : ℕ} {E : Set α} (h : b ≤ E.encard) :
    Nonempty (unif a b ≤ir unifOn E a) := by
  obtain ⟨f, hf⟩ : ∃ f : ↑(unif a b).E → ↑(unifOn E ↑a).E, f.Injective
  · obtain rfl | b := b
    · exact ⟨finZeroElim ∘ Subtype.val, Function.injective_of_subsingleton _⟩
    have : Nonempty E
    · rw [nonempty_coe_sort, nonempty_iff_ne_empty]
      rintro rfl
      simp at h
    obtain ⟨f, hf, hfi⟩ :=
      finite_univ.exists_injOn_of_encard_le (α := Fin (b+1)) (β := E) (t := univ) (by simpa using h)
    rw [injOn_univ] at hfi
    exact ⟨f ∘ Subtype.val, hfi.comp Subtype.val_injective⟩
  exact ⟨⟨f, hf, fun I ↦ by simp [Subtype.val_injective.encard_image, hf.encard_image]⟩⟩

@[simp] lemma unifOn_noUniformMinor_iff {a b : ℕ} :
    ((unifOn E a).NoUniformMinor a b) ↔ E.encard < b := by
  rw [← not_iff_not, not_noUniformMinor_iff, not_lt]
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ⟨(nonempty_unif_isoRestr_unifOn a h).some.isoMinor⟩⟩
  obtain ⟨f, hf, M₀, hm, hE, -⟩ := e
  refine le_trans ?_ <| encard_mono hm.subset
  rw [hE, Subtype.val_injective.encard_image, ← image_univ, hf.encard_image]
  simp

lemma no_line_minor_iff_of_eRank_le_two (hM : M.eRank ≤ 2) :
    M.NoUniformMinor 2 b ↔ M.simplification.E.encard < b := by
  obtain ⟨E, he⟩ := eq_unifOn_of_eRank_le_two (M := M.simplification) (by simpa)
  rw [← not_iff_not, not_noUniformMinor_iff, (unif_simple 0 b).isMinor_iff_isMinor_simplification,
      he, ← not_iff_not, ← not_noUniformMinor_iff, not_not, not_not,
    unifOn_noUniformMinor_iff, unifOn_ground_eq]

lemma NoUniformMinor.le_minor {a b b' : ℕ} (hM : M.NoUniformMinor a b) (ha : a ≤ b) (hb' : b ≤ b') :
    M.NoUniformMinor a b' := by
  contrapose! hM
  simp only [not_noUniformMinor_iff] at hM ⊢
  exact ⟨((unif_isoMinor_unif_iff' ha (Nat.le_trans ha hb')).2 ⟨ Nat.le_refl a,
      Nat.sub_le_sub_right hb' a ⟩).some.trans hM.some⟩

lemma NoUniformMinor.lt_of_isoMinor {β : Type*} {N : Matroid β} {a b : ℕ} (h : M.NoUniformMinor a b)
    (hNM : N ≤i M) (hN : N.IsFiniteRankUniform a) : N.E.encard < b := by
  by_contra! hle
  obtain ⟨E, rfl, _⟩ := hN.exists_eq_unifOn
  obtain ⟨φ⟩ := unif_isoRestr_unifOn (a := a) hle
  exact h.elim (IsoMinor.trans φ.isoMinor hNM)

@[simp]
lemma noUniformMinor_self_iff : M.NoUniformMinor a a ↔ M.eRank < a := by
  rw [← not_iff_not, NoUniformMinor, not_isEmpty_iff, not_lt]
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ?_⟩
  · grw [← e.eRank_le, unif_eRank_eq, min_self]
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨I, hIB, hI⟩ := B.exists_subset_encard_eq (h.trans_eq hB.encard_eq_eRank.symm)
  have him := (M.restrict_isRestriction _ (hIB.trans hB.subset_ground)).isMinor
  refine ⟨Iso.transIsoMinor (Iso.symm (Nonempty.some ?_)) him⟩
  rw [nonempty_iso_unif_iff]
  exact ⟨I, by rw [unifOn_eq_of_le hI.le, (hB.indep.subset hIB).restrict_eq_freeOn], hI⟩
