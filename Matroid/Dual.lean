import Matroid.Constructions.IndepBaseAxioms

namespace Matroid

open Set

variable {α : Type*} {M : Matroid α}

section dual

/-- The dual of a matroid. TODO : refactor so that a dual base is definitionally the complement
  of a base. -/
def dual (M : Matroid α) : Matroid α :=
  matroid_of_indep M.E (fun I ↦ I ⊆ M.E ∧ ∃ B, M.Base B ∧ Disjoint I B)
⟨empty_subset M.E, M.exists_base.imp (fun B hB ↦ ⟨hB, empty_disjoint _⟩)⟩
( by {
    rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
    exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩ } )
( by {
    rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
    have hXE := hX_max.1.1
    have hB' := (base_compl_iff_mem_maximals_disjoint_base hXE).mpr hX_max

    set B' := M.E \ X with hX
    have hI := (not_iff_not.mpr (base_compl_iff_mem_maximals_disjoint_base)).mpr hI_not_max
    obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB
    rw [←compl_subset_compl, ←hIB.sdiff_eq_right, ←union_diff_distrib, diff_eq, compl_inter,
      compl_compl, union_subset_iff, compl_subset_compl] at hB''₂

    have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne
      (by { rintro rfl; apply hI; convert hB''; simp [hB''.subset_ground] })

    obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu
    use e
    simp_rw [mem_diff, insert_subset_iff, and_iff_left heI, and_iff_right heE, and_iff_right hIE]
    refine' ⟨by_contra (fun heX ↦ heB'' (hB''₁ ⟨_, heI⟩)), ⟨B'', hB'', _⟩⟩
    · rw [hX]; exact ⟨heE, heX⟩
    rw [←union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB'']
    exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left } )
( by {
    rintro X - I'⟨hI'E, B, hB, hI'B⟩ hI'X
    obtain ⟨I, hI⟩ :=  M.exists_basis (M.E \ X)
    obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB
    refine' ⟨(X \ B') ∩ M.E,
      ⟨_,subset_inter (subset_diff.mpr _) hI'E, (inter_subset_left _ _).trans (diff_subset _ _)⟩, _⟩
    · simp only [inter_subset_right, true_and]
      exact ⟨B', hB', disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩
    · rw [and_iff_right hI'X]
      refine' disjoint_of_subset_right hB'IB _
      rw [disjoint_union_right, and_iff_left hI'B]
      exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right
    simp only [mem_setOf_eq, subset_inter_iff, and_imp, forall_exists_index]
    intros J hJE B'' hB'' hdj _ hJX hssJ
    rw [and_iff_left hJE]
    rw [diff_eq, inter_right_comm, ←diff_eq, diff_subset_iff] at hssJ

    have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B'
    · rw [union_subset_iff, and_iff_left (diff_subset _ _),
      ←inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc]

      calc _ ⊆ _ := inter_subset_inter_right _ hssJ
           _ ⊆ _ := by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty]
           _ ⊆ _ := inter_subset_right _ _

    obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB''
    rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I

    have : B₁ = B'
    · refine' hB₁.eq_of_subset_indep hB'.indep (fun e he ↦ _)
      refine' (hB₁I he).elim (fun heB'' ↦ _) (fun h ↦ h.1)
      refine' (em (e ∈ X)).elim (fun heX ↦ hI' (Or.inl ⟨heB'', heX⟩)) (fun heX ↦ hIB' _)
      refine' hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩
        (hB₁.indep.subset (insert_subset he _))
      refine' (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁
      refine' disjoint_of_subset_left hI.subset disjoint_sdiff_left

    subst this

    refine' subset_diff.mpr ⟨hJX, by_contra (fun hne ↦ _)⟩
    obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne
    obtain (heB'' | ⟨-,heX⟩ ) := hB₁I heB'
    · exact hdj.ne_of_mem heJ heB'' rfl
    exact heX (hJX heJ) } )
( by tauto )

/-- A notation typeclass for matroid duality, denoted by the `﹡` symbol. (This is distinct from the
  usual `*` symbol for multiplication, due to precedence issues. )-/
class Mdual (β : Type*) := (dual : β → β)

postfix:max "﹡" => Mdual.dual

instance Matroid_Mdual {α : Type*} : Mdual (Matroid α) := ⟨Matroid.dual⟩

theorem dual_indep_iff_exists' : (M﹡.Indep I) ↔ I ⊆ M.E ∧ (∃ B, M.Base B ∧ Disjoint I B) :=
  by simp [Mdual.dual, dual]

@[simp] theorem dual_ground : M﹡.E = M.E := rfl

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem subset_dual_ground_of_subset_ground (hX : X ⊆ M.E) : X ⊆ M﹡.E :=
  hX

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem subset_ground_of_subset_dual_ground (hX : X ⊆ M﹡.E) : X ⊆ M.E :=
  hX

@[simp] theorem dual_indep_iff_exists (hI : I ⊆ M.E := by aesop_mat) :
  (M﹡.Indep I) ↔ (∃ B, M.Base B ∧ Disjoint I B) :=
by rw [dual_indep_iff_exists', and_iff_right hI]

theorem dual_dep_iff_forall : (M﹡.Dep I) ↔ (∀ B, M.Base B → (I ∩ B).Nonempty) ∧ I ⊆ M.E :=
  by simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter, imp_iff_right_iff, iff_true_intro Or.inl]

instance dual_finite [M.Finite] : M﹡.Finite :=
  ⟨M.ground_finite⟩

theorem subset_ground_dual (hX : X ⊆ M.E := by aesop_mat) : X ⊆ M﹡.E :=
  hX

@[simp] theorem dual_base_iff (hB : B ⊆ M.E := by aesop_mat) : M﹡.Base B ↔ M.Base (M.E \ B) := by
  rw [base_compl_iff_mem_maximals_disjoint_base, base_iff_maximal_indep, dual_indep_iff_exists',
    mem_maximals_setOf_iff]
  simp [dual_indep_iff_exists']

theorem dual_base_iff' : M﹡.Base B ↔ M.Base (M.E \ B) ∧ B ⊆ M.E :=
  (em (B ⊆ M.E)).elim (fun h ↦ by rw [dual_base_iff, and_iff_left h])
    (fun h ↦ iff_of_false (h ∘ (fun h' ↦ h'.subset_ground)) (h ∘ And.right))

theorem setOf_dual_base_eq : setOf M﹡.Base = (fun X ↦ M.E \ X) '' setOf M.Base := by
  ext B
  simp only [mem_setOf_eq, mem_image, dual_base_iff']
  refine' ⟨fun h ↦ ⟨_, h.1, diff_diff_cancel_left h.2⟩,
    fun ⟨B', hB', h⟩ ↦ ⟨_,h.symm.trans_subset (diff_subset _ _)⟩⟩
  rwa [←h, diff_diff_cancel_left hB'.subset_ground]

@[simp] theorem dual_dual (M : Matroid α) : M﹡﹡ = M :=
  eq_of_base_iff_base_forall rfl (fun B (h : B ⊆ M.E) ↦
    by rw [dual_base_iff, dual_base_iff, dual_ground, diff_diff_cancel_left h])

theorem Base.compl_base_of_dual (h : M﹡.Base B) : M.Base (M.E \ B) :=
  (dual_base_iff'.1 h).1

theorem Base.compl_base_dual (h : M.Base B) : M﹡.Base (M.E \ B) := by
  rwa [dual_base_iff, diff_diff_cancel_left h.subset_ground]

theorem Base.compl_inter_basis_of_inter_basis (hB : M.Base B) (hBX : M.Basis (B ∩ X) X) :
    M﹡.Basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine' Indep.basis_of_forall_insert _ (inter_subset_right _ _) (fun e he ↦ _)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩
  simp only [diff_inter_self_eq_diff, mem_diff, not_and, not_not, imp_iff_right he.1.1] at he
  simp_rw [dual_dep_iff_forall, insert_subset_iff, and_iff_right he.1.1,
    and_iff_left ((inter_subset_left _ _).trans (diff_subset _ _))]
  refine' fun B' hB' ↦ by_contra (fun hem ↦ _)
  rw [nonempty_iff_ne_empty, not_ne_iff, ←union_singleton, diff_inter_diff,
   inter_distrib_right, union_empty_iff, singleton_inter_eq_empty, diff_eq,
   inter_right_comm, inter_eq_self_of_subset_right hB'.subset_ground, ←diff_eq,
   diff_eq_empty] at hem
  obtain ⟨f, hfb, hBf⟩ := hB.exchange hB' ⟨he.2, hem.2⟩

  have hi : M.Indep (insert f (B ∩ X))
  · refine' hBf.indep.subset (insert_subset_insert _)
    simp_rw [subset_diff, and_iff_right (inter_subset_left _ _), disjoint_singleton_right,
      mem_inter_iff, iff_false_intro he.1.2, and_false]
  exact hfb.2 (hBX.mem_of_insert_indep (Or.elim (hem.1 hfb.1) (False.elim ∘ hfb.2) id) hi).1


theorem Base.inter_basis_iff_compl_inter_basis_dual (hB : M.Base B) (hX : X ⊆ M.E := by aesop_mat):
    M.Basis (B ∩ X) X ↔ M﹡.Basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine' ⟨hB.compl_inter_basis_of_inter_basis, fun h ↦ _⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_base_dual.compl_inter_basis_of_inter_basis h

theorem dual_inj {M₁ M₂ : Matroid α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
by rw [←dual_dual M₁, h, dual_dual]

@[simp] theorem dual_inj_iff {M₁ M₂ : Matroid α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂﹡ ↔ M₂ = M₁﹡ :=
by rw [←dual_inj_iff, dual_dual, eq_comm]

theorem dual_eq_comm {M₁ M₂ : Matroid α} : M₁﹡ = M₂ ↔ M₂﹡ = M₁ :=
by rw [←dual_inj_iff, dual_dual, eq_comm]

theorem base_iff_dual_base_compl (hB : B ⊆ M.E := by aesop_mat) :
    M.Base B ↔ M﹡.Base (M.E \ B) := by
  rw [dual_base_iff, diff_diff_cancel_left hB]

theorem ground_not_base (M : Matroid α) [h : RkPos M﹡] : ¬M.Base M.E := by
  rwa [rkPos_iff_empty_not_base, dual_base_iff, diff_empty] at h

theorem Base.ssubset_ground [h : RkPos M﹡] (hB : M.Base B) : B ⊂ M.E :=
  hB.subset_ground.ssubset_of_ne (by rintro rfl; exact M.ground_not_base hB)

theorem Indep.ssubset_ground [h : RkPos M﹡] (hI : M.Indep I) : I ⊂ M.E := by
  obtain ⟨B, hB⟩ := hI.exists_base_superset; exact hB.2.trans_ssubset hB.1.ssubset_ground

/-- A coindependent set of `M` is an independent set of the dual of `M﹡`. we give it a separate
  definition to enable dot notation. -/
@[reducible] def Coindep (M : Matroid α) (I : Set α) : Prop := M﹡.Indep I

theorem coindep_def : M.Coindep X ↔ M﹡.Indep X := Iff.rfl

theorem Coindep.indep (hX : M.Coindep X) : M﹡.Indep X :=
  hX

theorem coindep_iff_exists' : M.Coindep X ↔ (∃ B, M.Base B ∧ B ⊆ M.E \ X) ∧ X ⊆ M.E :=
  ⟨fun ⟨B, hB, hXB⟩ ↦ ⟨⟨M.E \ B, hB.compl_base_of_dual, diff_subset_diff_right hXB⟩,
      hXB.trans hB.subset_ground⟩,
    fun ⟨⟨B, hB, hBX⟩, hXE⟩ ↦ ⟨M.E \ B, hB.compl_base_dual,
      subset_diff.mpr ⟨hXE, (subset_diff.1 hBX).2.symm⟩⟩⟩

theorem coindep_iff_exists (hX : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ ∃ B, M.Base B ∧ B ⊆ M.E \ X := by
  rw [coindep_iff_exists', and_iff_left hX]

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.E :=
  hX.indep.subset_ground

theorem Coindep.exists_base_subset_compl (h : M.Coindep X) : ∃ B, M.Base B ∧ B ⊆ M.E \ X :=
  (coindep_iff_exists h.subset_ground).mp h

end dual
