import Matroid.Uniform.Finite

variable {α : Type*} {M : Matroid α} {E I B X Y C : Set α} {k : ℕ} {e f : α} {a b b' n : ℕ}

open Set

namespace Matroid

noncomputable def unif_isoRestr_unif (a : ℕ) (hbb' : b ≤ b') : unif a b ≤ir unif a b' :=
  let R : Set (Fin b') := range (Fin.castLE hbb')
  have hM : Nonempty (((unif a b') ↾ R) ≂ unif a b) := by
    refine nonempty_iso_unif_iff'''.2 ⟨R, ?_⟩
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
  refine ⟨Iso.transIsMinor (Iso.symm (Nonempty.some ?_)) him⟩
  rw [nonempty_iso_unif_iff''']
  exact ⟨I, by rw [unifOn_eq_of_le hI.le, (hB.indep.subset hIB).restrict_eq_freeOn], hI⟩

theorem IsFiniteRankUniform.nonempty_isoMinor_iff {β : Type*} {M : Matroid β} {N : Matroid α}
    (hN : N.IsFiniteRankUniform a) : Nonempty (N ≤i M) ↔
      ∃ C X, M.Indep C ∧ (M ／ C).IsFiniteRankUniformOn a X ∧ Nonempty (N.E ≃ X) := by
  obtain rfl | hne := N.eq_emptyOn_or_nonempty
  · obtain rfl : a = 0 := by simpa [eq_comm] using hN.eRank_eq
    exact iff_of_true ⟨emptyOn_isoMinor α M⟩ ⟨∅, ∅, by simp [← Finite.encard_eq_iff_nonempty_equiv]⟩
  have haN := hN.le
  rw [hN.eq_unifOn, Matroid.nonempty_isoMinor_iff]
  simp_rw [nonempty_iso_comm (M := unifOn N.E a), nonempty_iso_unifOn_iff haN]
  refine ⟨fun ⟨M₀, hM₀, hM₀a, ⟨e⟩⟩ ↦ ?_, fun ⟨C, X, hC, hCX, ⟨e⟩⟩ ↦ ?_⟩
  · obtain ⟨C, X, hC, hX, -, rfl⟩ := hM₀.exists_eq_contract_spanning_restrict
    exact ⟨C, X, hC, isFiniteRankUniformOn_of_restrict hM₀a (by grind), ⟨e⟩⟩
  refine ⟨M ／ C ↾ X, (restrict_isMinor _ hCX.subset_ground).trans (contract_isMinor ..), ?_, ⟨e⟩⟩
  exact hCX.isFiniteRankUniform

theorem nonempty_loopyOn_isoMinor_iff {β : Type*} {E : Set α} {M : Matroid β} :
    Nonempty (loopyOn E ≤i M) ↔ ∃ (f : E ↪ β), M.Coindep (range f) := by
  rw [← unifOn_zero,
    IsFiniteRankUniform.nonempty_isoMinor_iff (unifOn_isFiniteRankUniform (by simp))]
  simp_rw [isFiniteRankUniformOn_zero_iff, contract_loops_eq, unifOn_ground_eq, subset_diff]
  refine ⟨fun ⟨C, X, hC, ⟨hCX, hXC⟩, ⟨e⟩⟩  ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · have hXc : M.Coindep X := by
      nth_grw 1 [coindep_iff_subset_closure_compl, hCX, show C ⊆ M.E \ X by grind]
    refine ⟨e.toEmbedding.trans (Function.Embedding.setSubtype _), hXc.subset ?_⟩
    grind [Function.Embedding.trans_apply, Function.Embedding.setSubtype_apply]
  obtain ⟨C, hC, hCf⟩ := hf.exists_isBase_subset_compl
  refine ⟨C, range f, hC.indep, ⟨?_, by grind⟩, ⟨Equiv.ofInjective f f.injective⟩⟩
  grw [hC.closure_eq, hf.subset_ground]

theorem nonempty_freeOn_isoMinor_iff {β : Type*} {E : Set α} {M : Matroid β} :
    Nonempty (freeOn E ≤i M) ↔ ∃ (f : E ↪ β), M.Indep (range f) := by
  rw [← nonempty_isoMinor_dual_iff, freeOn_dual_eq, nonempty_loopyOn_isoMinor_iff]
  simp_rw [dual_coindep_iff]

theorem nonempty_freeOn_isoMinor_iff_of_finite {β : Type*} {E : Set α} {M : Matroid β}
    (hEfin : E.Finite) : Nonempty (freeOn E ≤i M) ↔ E.encard ≤ M.eRank := by
  rw [nonempty_freeOn_isoMinor_iff]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun h ↦ ?_⟩
  · grw [← hf.encard_le_eRank, ← f.injective.encard_range]
    simp
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, hEfin.encard_le_iff_nonempty_embedding] at h
  obtain ⟨i⟩ := h
  refine ⟨i.trans (Function.Embedding.setSubtype B), hB.indep.subset ?_⟩
  intro x
  simp +contextual only [mem_range, Function.Embedding.trans_apply,
    Function.Embedding.setSubtype_apply, Subtype.exists, forall_exists_index]
  grind

theorem nonempty_loopyOn_isoMinor_iff_of_finite {β : Type*} {E : Set α} {M : Matroid β}
    (hEfin : E.Finite) : Nonempty (loopyOn E ≤i M) ↔ E.encard ≤ M✶.eRank := by
  rw [← nonempty_isoMinor_dual_iff, loopyOn_dual_eq, nonempty_freeOn_isoMinor_iff_of_finite hEfin]

theorem nonempty_circuitOn_isoMinor_iff {β : Type*} {E : Set α} {M : Matroid β}
    (he : E.Nonempty) : Nonempty (circuitOn E ≤i M) ↔ ∃ C, M.IsCircuit C ∧ Nonempty (E ↪ C) := by
  simp_rw [← nonempty_isoMinor_dual_iff (M := M), circuitOn_dual, nonempty_isoMinor_iff,
    nonempty_iso_comm (M := unifOn E 1), nonempty_iso_unifOn_iff (show 1 ≤ E.encard by simpa)]
  refine ⟨fun ⟨M₀, hM₀, hM₀u, ⟨e⟩⟩ ↦ ?_, fun ⟨C, hC, ⟨e⟩⟩ ↦ ?_⟩
  · obtain ⟨X, rfl, hne⟩ := hM₀u.exists_eq_unifOn
    rw [← circuitOn_dual, dual_isMinor_iff] at hM₀
    obtain ⟨A, D, hA, hD, hAD, hAM⟩ := hM₀.exists_eq_contract_spanning_restrict
    obtain rfl : X = D := congr_arg Matroid.E hAM
    rw [eq_comm, ← isCircuit_iff_restr_eq_circuitOn (by simpa using hne) hAD.subset_ground] at hAM
    obtain ⟨C, hC, hXC, hCX⟩ := hAM.exists_subset_isCircuit_of_contract
    exact ⟨C, hC, ⟨e.toEmbedding.trans ⟨_,inclusion_injective hXC⟩⟩⟩
  set N := ((M ↾ C) ／ (C \ (Subtype.val '' range e))) with hN
  have hNE : N.E = range e := by simp [hN]
  have hNC : N = circuitOn N.E := by
    rw [hC.restrict_eq_circuitOn, circuitOn_contract] at hN
    simp [hN]
  refine ⟨N✶, ?_, ?_, ?_⟩
  · exact IsMinor.dual <| (contract_isMinor ..).trans <| restrict_isMinor _
  · rw [hNC, circuitOn_dual]
    refine unifOn_isFiniteRankUniform ?_
    simp [hN, range_nonempty_iff_nonempty, he.to_subtype]
  refine ⟨(Equiv.ofInjective _ e.injective).trans ?_⟩
  rw [dual_ground, hNE]
  exact Equiv.Set.imageOfInjOn _ _ Subtype.val_injective.injOn

theorem nonempty_circuitOn_isoMinor_iff_of_finite {β : Type*} {E : Set α} {M : Matroid β}
    (he : E.Nonempty) (hEfin : E.Finite) :
    Nonempty (circuitOn E ≤i M) ↔ ∃ C, M.IsCircuit C ∧ E.encard ≤ C.encard := by
  simp_rw [nonempty_circuitOn_isoMinor_iff he, hEfin.encard_le_iff_nonempty_embedding]

lemma IsFiniteUniform.nonempty_isoMinor_iff {β : Type*} {N : Matroid β} {a' b' n' : ℕ}
    (hM : M.IsFiniteUniform a b n) (hN : N.IsFiniteUniform a' b' n') :
    Nonempty (N ≤i M) ↔ (a' ≤ a ∧ b' ≤ b) := by
  refine ⟨fun ⟨i⟩ ↦ ?_, fun h ↦ ?_⟩
  · grw [← ENat.coe_le_coe, ← ENat.coe_le_coe, ← hN.eRank_eq, ← hM.eRank_eq, ← hN.eRank_dual_eq,
      ← hM.eRank_dual_eq, i.eRank_le, i.dual.eRank_le]
    simp
  obtain ⟨e⟩ := hM.nonempty_iso_unif
  obtain ⟨f⟩ := hN.nonempty_iso_unif
  refine ⟨f.isoMinor.trans (IsoMinor.trans (Nonempty.some ?_) e.symm.isoMinor)⟩
  rw [unif_isoMinor_unif_iff' hN.le_left hM.le_left, ← hM.add_eq, ← hN.add_eq]
  lia
