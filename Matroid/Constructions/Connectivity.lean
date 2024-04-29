import Matroid.Minor.Rank

open Set

variable {α : Type*} {M : Matroid α} {B I I' J K X Y : Set α}

namespace Matroid

theorem Base.encard_compl_eq (hB : M.Base B) : (M.E \ B).encard = M✶.erk :=
  (hB.compl_base_dual).encard

theorem Indep.contract_er_dual_eq (hI : M.Indep I) : (M ⧸ I)✶.erk = M✶.erk := by
  rw [contract_dual_eq_dual_delete]

theorem encard_dual_eq_foo (hI : M.Basis I X) (hI' : M.Basis I' X) (hJ : M.Indep J)
    (hXJ : Disjoint X J) : (M ↾ (I ∪ J))✶.erk = (M ↾ (I' ∪ J))✶.erk := by
  obtain ⟨BJ, hBJ, hJBJ⟩ := hJ.subset_basis_of_subset
    (show J ⊆ (I ∩ I') ∪ J from subset_union_right _ _)
    (union_subset ((inter_subset_left _ _).trans hI.indep.subset_ground) hJ.subset_ground)

  have hJ' : ∀ X, (M ↾ (X ∪ J)).Indep J := fun X ↦ by
    rw [restrict_indep_iff, and_iff_right hJ]; apply subset_union_right

  obtain ⟨B₀,hB₀⟩ := (M ⧸ J).exists_basis' (I ∩ I')
  obtain ⟨BI, hBI, hssBI⟩ :=
    hB₀.indep.subset_basis'_of_subset (hB₀.subset.trans (inter_subset_left _ _))
  obtain ⟨BI', hBI', hssBI'⟩ :=
    hB₀.indep.subset_basis'_of_subset (hB₀.subset.trans (inter_subset_right _ _))

  have hbas : ∀ Y K B, K ⊆ Y → Y ⊆ X → M.Basis K X → (M ⧸ J).Basis' B K →
      ((M ↾ (Y ∪ J)) ⧸ J).Base B := by
    intro Y K B hKY hYX hKX hBK
    rw [← contract_restrict_eq_restrict_contract _ _ _ (hXJ.symm.mono_right hYX),
      base_restrict_iff']
    refine (hBK.basis_cl_right.basis_subset (hBK.subset.trans hKY) ?_).basis'
    rw [contract_cl_eq, subset_diff, and_iff_left (hXJ.mono_left hYX)]
    exact (hYX.trans hKX.subset_cl).trans (M.cl_subset_cl (subset_union_left _ _))

  have hBIbas := hbas I I BI Subset.rfl hI.subset hI hBI
  have hBI'bas := hbas I' I' BI' Subset.rfl hI'.subset hI' hBI'

  have hb := hbas (I ∪ I') I BI (subset_union_left _ _) (union_subset hI.subset hI'.subset) hI hBI
  have hb' := hbas _ _ _ (subset_union_right _ _) (union_subset hI.subset hI'.subset) hI' hBI'


  simp_rw [← (hJ' I).delete_erk_dual_eq, ← hBIbas.encard_compl_eq,  ← (hJ' I').delete_erk_dual_eq,
    ← hBI'bas.encard_compl_eq, contract_ground, restrict_ground_eq, union_diff_right,
    (hXJ.mono_left hI.subset).sdiff_eq_left, (hXJ.mono_left hI'.subset).sdiff_eq_left]

  have hd : (I ∪ I') \ J = I ∪ I' := sorry
  have := hb'.compl_base_dual.encard_diff_comm hb.compl_base_dual
  simp [hd, diff_diff_right] at this

  -- have := hb'.encard_diff_comm hb
