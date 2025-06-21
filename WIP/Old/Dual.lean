import Matroid.Basic

namespace Matroid

open Set

variable {α : Type*} {M : Matroid α}

section dual

/- definition of dual where the bases of the dual
   are definitionally the complements of the
   bases of the primal -/
def dual (M : Matroid α) : Matroid α :=
  matroid_of_isBase
    M.E
    (fun B ↦ B ⊆ M.E ∧ M.IsBase (M.E \ B))
    (by {
      obtain ⟨B, hB⟩ := M.exists_isBase'
      refine' ⟨M.E \ B, _⟩
      simp_rw [sdiff_sdiff_right_self, ge_iff_le, le_eq_subset, inf_eq_inter,
        inter_eq_self_of_subset_right hB.subset_ground]
      exact ⟨diff_subset _ _, hB⟩
    })
    (by {
      rintro B₁ B₂ hB₁ hB₂ x hx

      obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB₂.2.indep.diff (B₁ \ { x })).exists_isBase_subset_union_isBase hB₁.2
      rw [← compl_subset_compl,
        ← (disjoint_of_subset_left (diff_subset B₁ {x}) disjoint_sdiff_self_right).sdiff_eq_right,
        ← union_diff_distrib, diff_eq, compl_inter, compl_compl, union_subset_iff,
        compl_subset_compl] at hB''₂

      have hI : ¬ M.IsBase (M.E \ (B₁ \ {x}))
      · intro g
        have : M.E \ B₁ ⊂ M.E \ (B₁ \ {x})
        · rw [diff_diff_right,
              inter_eq_self_of_subset_right (singleton_subset_iff.mpr (hB₁.1 hx.1)), union_comm,
              ← insert_eq]
          exact ssubset_insert (notMem_diff_of_mem hx.1)
        exact g.not_isBase_of_ssubset this hB₁.2

      have hssu : B₁ \ {x} ⊂ B''ᶜ ∩ M.E :=
        (subset_inter (hB''₂.2) ((diff_subset B₁ {x}).trans hB₁.1)).ssubset_of_ne
          (by { rintro g; apply hI; rw [g]; convert hB''; simp [hB''.subset_ground] })
      obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ :=
        exists_of_ssubset hssu
      refine' (em (x = e)).elim
        (by {rintro rfl; exfalso; exact heB'' (hB''₁ ⟨⟨hB₁.1 hx.1, hx.2⟩, heI⟩)}) (fun hxe ↦ ⟨e, _⟩)
      simp_rw [mem_diff, insert_subset_iff, and_iff_left heI, and_iff_right heE,
        and_iff_right ((diff_subset B₁ {x}).trans hB₁.1)]
      refine' ⟨by_contra (fun heX ↦ heB'' (hB''₁ ⟨_, heI⟩)), _⟩
      · rw [not_and_or, not_not] at heX
        refine' heX.elim (fun g ↦ ⟨heE, g⟩) (fun g ↦ _)
        · rw [mem_diff, not_and, not_not] at heI
          rw [← mem_singleton_iff.mp (heI g)] at hx
          exact ⟨heE, hx.2⟩
      · rw [insert_eq, diff_eq, compl_union, diff_eq, compl_inter, compl_compl,
            inter_distrib_left, inter_eq_self_of_subset_right (singleton_subset_iff.mpr
            (mem_compl_singleton_iff.mpr hxe)), inter_distrib_left,
            inter_eq_self_of_subset_right (singleton_subset_iff.mpr (hB₁.1 hx.1)),
            inter_comm {e}ᶜ _, ← inter_assoc, ← diff_eq M.E _, ← diff_eq, union_comm, ← insert_eq]
        have : B'' ⊆ insert x ((M.E \ B₁) \ {e})
        · have : e ∈ B''ᶜ ∩ M.E := ⟨heB'', heE⟩
          have : {e} ∪ B₁ \ {x} ⊆ B''ᶜ ∩ M.E :=
            union_subset (singleton_subset_iff.mpr this) hssu.subset
          rw [inter_comm, ← diff_eq] at this
          have : M.E \ (M.E \ B'') ⊆ M.E \ ({e} ∪ B₁ \ {x}) :=
            diff_subset_diff_right this
          rw [diff_diff_cancel_left hB''.subset_ground, diff_eq, diff_eq, compl_union,
              compl_inter, compl_compl, inter_union_distrib_left, inter_comm _ B₁ᶜ,
              inter_eq_self_of_subset_right (singleton_subset_iff.mpr
              (mem_compl_singleton_iff.mpr hxe)), inter_union_distrib_left, ← inter_assoc,
              ← diff_eq, ← diff_eq,
              inter_eq_self_of_subset_right (singleton_subset_iff.mpr (hB₁.1 hx.1)), union_comm,
              ← insert_eq] at this
          exact this
        rw [diff_eq, mem_inter_iff, not_and', mem_compl_singleton_iff] at heI
        rwa [← hB₁.2.eq_exchange_of_subset hB'' ⟨heE, heI (Ne.symm hxe)⟩ this]
    })
    (by {
      rintro X hX I' ⟨Bt, ⟨hBt, hI'B⟩⟩ hI'X

      set B := M.E \ Bt
      rw [(diff_diff_cancel_left hBt.1).symm] at hI'B

      obtain ⟨-, hB⟩ := hBt
      have hI'E := hI'B.trans (diff_subset M.E B)
      have hI'B := (subset_diff.mp hI'B).2

      obtain ⟨I, hI⟩ :=  M.exists_isBasis (M.E \ X)
      obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_isBase_subset_union_isBase hB

      refine' ⟨(X \ B') ∩ M.E,
        ⟨⟨M.E \ B', ⟨⟨diff_subset _ _, by { rwa [diff_diff_cancel_left hB'.subset_ground] }⟩,
         (inter_subset_left (X \ B') M.E).trans (diff_subset_diff_left hX)⟩⟩,
         ⟨subset_inter_iff.mpr ⟨_, hI'X.trans hX⟩,
          (inter_subset_left (X \ B') M.E).trans (diff_subset X B')⟩⟩, _⟩
      · rw [subset_diff, and_iff_right hI'X]
        refine' disjoint_of_subset_right hB'IB _
        rw [disjoint_union_right, and_iff_left hI'B]
        exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right
      simp only [mem_setOf_eq, subset_inter_iff, and_imp, forall_exists_index]
      rintro J Bt h₁Bt hB'' hJBt _ hJX hssJ

      set B'' := M.E \ Bt
      have hJE := hJBt.trans h₁Bt
      have hdj : Disjoint J B''
      · have : J ⊆ M.E \ B''
        · rwa [diff_diff_cancel_left h₁Bt]
        exact (subset_diff.mp this).2
      clear h₁Bt; clear hJBt

      rw [and_iff_left hJE]
      rw [diff_eq, inter_right_comm, ← diff_eq, diff_subset_iff] at hssJ

      have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B'
      · rw [union_subset_iff, and_iff_left diff_subset,
        ← inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc]

        calc _ ⊆ _ := inter_subset_inter_right _ hssJ
            _ ⊆ _ := by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty]
            _ ⊆ _ := inter_subset_right

      obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_isBase_subset_union_isBase hB''
      rw [union_comm, ← union_assoc, union_eq_self_of_subset_right inter_subset_left] at hB₁I

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
      exact heX (hJX heJ)
    })
    (fun B hB ↦ hB.1)

/- from ../Dual.lean -/

/-- A notation typeclass for matroid duality, denoted by the `✶` symbol. (This is distinct from the
  usual `*` symbol for multiplication, due to precedence issues. )-/
class Mdual (β : Type*) := (dual : β → β)

postfix:max "✶" => Mdual.dual

instance Matroid_Mdual {α : Type*} : Mdual (Matroid α) := ⟨Matroid.dual⟩

-- refactored
theorem dual_indep_iff_exists' : (M✶.Indep I) ↔ I ⊆ M.E ∧ (∃ B, M.IsBase B ∧ Disjoint I B) := by
  simp [Mdual.dual, dual, Indep]
  refine' ⟨fun ⟨B, hB⟩ ↦ ⟨hB.2.trans hB.1.1, M.E \ B, hB.1.2,
            disjoint_of_subset_left hB.2 disjoint_sdiff_right⟩, fun ⟨hIE, B, hB⟩ ↦ ⟨M.E \ B, _⟩⟩
  rw [diff_diff_cancel_left hB.1.subset_ground]
  exact ⟨⟨diff_subset _ _, hB.1⟩, subset_diff.mpr ⟨hIE, hB.2⟩⟩

@[simp] theorem dual_ground : M✶.E = M.E := rfl

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem subset_dual_ground_of_subset_ground (hX : X ⊆ M.E) : X ⊆ M✶.E :=
  hX

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem subset_ground_of_subset_dual_ground (hX : X ⊆ M✶.E) : X ⊆ M.E :=
  hX

@[simp] theorem dual_indep_iff_exists (hI : I ⊆ M.E := by aesop_mat) :
  (M✶.Indep I) ↔ (∃ B, M.IsBase B ∧ Disjoint I B) :=
by rw [dual_indep_iff_exists', and_iff_right hI]

theorem dual_dep_iff_forall : (M✶.Dep I) ↔ (∀ B, M.IsBase B → (I ∩ B).Nonempty) ∧ I ⊆ M.E :=
  by simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter, imp_iff_right_iff, iff_true_intro Or.inl]

instance dual_finite [M.Finite] : M✶.Finite :=
  ⟨M.ground_finite⟩

theorem subset_ground_dual (hX : X ⊆ M.E := by aesop_mat) : X ⊆ M✶.E :=
  hX

@[simp] theorem dual_isBase_iff (hB : B ⊆ M.E := by aesop_mat) : M✶.IsBase B ↔ M.IsBase (M.E \ B) := by
  rw [isBase_compl_iff_mem_maximals_disjoint_isBase, base_iff_maximal_indep, dual_indep_iff_exists',
    mem_maximals_setOf_iff]
  simp [dual_indep_iff_exists']

theorem dual_isBase_iff' : M✶.IsBase B ↔ M.IsBase (M.E \ B) ∧ B ⊆ M.E :=
  (em (B ⊆ M.E)).elim (fun h ↦ by rw [dual_isBase_iff, and_iff_left h])
    (fun h ↦ iff_of_false (h ∘ (fun h' ↦ h'.subset_ground)) (h ∘ And.right))

theorem setOf_dual_isBase_eq : setOf M✶.IsBase = (fun X ↦ M.E \ X) '' setOf M.IsBase := by
  ext B
  simp only [mem_setOf_eq, mem_image, dual_isBase_iff']
  refine' ⟨fun h ↦ ⟨_, h.1, diff_diff_cancel_left h.2⟩,
    fun ⟨B', hB', h⟩ ↦ ⟨_,h.symm.trans_subset diff_subset⟩⟩
  rwa [← h, diff_diff_cancel_left hB'.subset_ground]

@[simp] theorem dual_dual (M : Matroid α) : M✶✶ = M :=
  ext_isBase rfl (fun B (h : B ⊆ M.E) ↦
    by rw [dual_isBase_iff, dual_isBase_iff, dual_ground, diff_diff_cancel_left h])

theorem IsBase.compl_isBase_of_dual (h : M✶.IsBase B) : M.IsBase (M.E \ B) :=
  (dual_isBase_iff'.1 h).1

theorem IsBase.compl_isBase_dual (h : M.IsBase B) : M✶.IsBase (M.E \ B) := by
  rwa [dual_isBase_iff, diff_diff_cancel_left h.subset_ground]

theorem IsBase.compl_inter_isBasis_of_inter_isBasis (hB : M.IsBase B) (hBX : M.IsBasis (B ∩ X) X) :
    M✶.IsBasis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine' Indep.isBasis_of_forall_insert _ inter_subset_right (fun e he ↦ _)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left inter_subset_left disjoint_sdiff_left⟩
  simp only [diff_inter_self_eq_diff, mem_diff, not_and, not_not, imp_iff_right he.1.1] at he
  simp_rw [dual_dep_iff_forall, insert_subset_iff, and_iff_right he.1.1,
    and_iff_left (inter_subset_left.trans diff_subset)]
  refine' fun B' hB' ↦ by_contra (fun hem ↦ _)
  simp_rw [nonempty_iff_ne_empty, not_ne_iff, ← union_singleton, inter_distrib_right,
    union_empty_iff, singleton_inter_eq_empty, diff_eq, inter_comm _ M.E,
    ← inter_inter_distrib_left, ← inter_assoc, inter_right_comm,
    inter_eq_self_of_subset_right hB'.subset_ground, ← diff_eq, diff_eq_empty] at hem
  obtain ⟨f, hfb, hBf⟩ := hB.exchange hB' ⟨he.2, hem.2⟩

  have hi : M.Indep (insert f (B ∩ X))
  · refine' hBf.indep.subset (insert_subset_insert _)
    simp_rw [subset_diff, and_iff_right inter_subset_left, disjoint_singleton_right,
      mem_inter_iff, iff_false_intro he.1.2, and_false]
  exact hfb.2 (hBX.mem_of_insert_indep (hem.1 hfb) hi).1

theorem IsBase.inter_isBasis_iff_compl_inter_isBasis_dual (hB : M.IsBase B) (hX : X ⊆ M.E := by aesop_mat):
    M.IsBasis (B ∩ X) X ↔ M✶.IsBasis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine' ⟨hB.compl_inter_isBasis_of_inter_isBasis, fun h ↦ _⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_isBase_dual.compl_inter_isBasis_of_inter_isBasis h

theorem dual_inj {M₁ M₂ : Matroid α} (h : M₁✶ = M₂✶) : M₁ = M₂ :=
by rw [← dual_dual M₁, h, dual_dual]

@[simp] theorem dual_inj {M₁ M₂ : Matroid α} : M₁✶ = M₂✶ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₂ = M₁✶ :=
by rw [← dual_inj, dual_dual, eq_comm]

theorem dual_eq_comm {M₁ M₂ : Matroid α} : M₁✶ = M₂ ↔ M₂✶ = M₁ :=
by rw [← dual_inj, dual_dual, eq_comm]

theorem base_iff_dual_isBase_compl (hB : B ⊆ M.E := by aesop_mat) :
    M.IsBase B ↔ M✶.IsBase (M.E \ B) := by
  rw [dual_isBase_iff, diff_diff_cancel_left hB]

theorem ground_not_isBase (M : Matroid α) [h : RankPos M✶] : ¬M.IsBase M.E := by
  rwa [rankPos_iff_empty_not_isBase, dual_isBase_iff, diff_empty] at h

theorem IsBase.ssubset_ground [h : RankPos M✶] (hB : M.IsBase B) : B ⊂ M.E :=
  hB.subset_ground.ssubset_of_ne (by rintro rfl; exact M.ground_not_isBase hB)

theorem Indep.ssubset_ground [h : RankPos M✶] (hI : M.Indep I) : I ⊂ M.E := by
  obtain ⟨B, hB⟩ := hI.exists_isBase_superset; exact hB.2.trans_ssubset hB.1.ssubset_ground

/-- A coindependent set of `M` is an independent set of the dual of `M✶`. we give it a separate
  definition to enable dot notation. -/
@[reducible] def Coindep (M : Matroid α) (I : Set α) : Prop := M✶.Indep I

theorem coindep_def : M.Coindep X ↔ M✶.Indep X := Iff.rfl

theorem Coindep.indep (hX : M.Coindep X) : M✶.Indep X :=
  hX

theorem coindep_iff_exists' : M.Coindep X ↔ (∃ B, M.IsBase B ∧ B ⊆ M.E \ X) ∧ X ⊆ M.E :=
  ⟨fun ⟨B, hB, hXB⟩ ↦ ⟨⟨M.E \ B, hB.compl_isBase_of_dual, diff_subset_diff_right hXB⟩,
      hXB.trans hB.subset_ground⟩,
    fun ⟨⟨B, hB, hBX⟩, hXE⟩ ↦ ⟨M.E \ B, hB.compl_isBase_dual,
      subset_diff.mpr ⟨hXE, (subset_diff.1 hBX).2.symm⟩⟩⟩

theorem coindep_iff_exists (hX : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ ∃ B, M.IsBase B ∧ B ⊆ M.E \ X := by
  rw [coindep_iff_exists', and_iff_left hX]

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.E :=
  hX.indep.subset_ground

theorem Coindep.exists_isBase_subset_compl (h : M.Coindep X) : ∃ B, M.IsBase B ∧ B ⊆ M.E \ X :=
  (coindep_iff_exists h.subset_ground).mp h

end dual
end Matroid
