import Matroid.Connectivity.Basic

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J K X Y : Set α}

section localConn

lemma Indep.encard_inter_add_erk_dual_eq_of_closure_eq_closure (hI : M.Indep I) (hI' : M.Indep I')
    (hII' : M.closure I = M.closure I') (hJ : M.Indep J) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J).encard + (M ↾ (I' ∪ J))✶.erk := by
  obtain ⟨K, hK, hIK⟩ := hI.subset_basis_of_subset (subset_union_left (s := I) (t := J))
  have hsk := (hK.indep.subset_skew_diff hIK)
  rw [skew_iff_closure_skew_left] at hsk
  have' hdj := hsk.disjoint_of_indep_subset_right (hK.indep.diff _) Subset.rfl

  have hb : ∀ ⦃B⦄, M.Basis B (M.closure I) →
      (M ／ (K \ I)).Basis B (B ∪ J \ (K \ I)) ∧ (K \ I ⊆ B ∪ J) := by
    refine fun B hB ↦ ⟨Indep.basis_of_subset_of_subset_closure ?_ ?_ ?_, ?_⟩
    · rw [(hK.indep.diff _).contract_indep_iff]
      exact ⟨hdj.mono_left hB.subset,
        hsk.union_indep_of_indep_subsets hB.indep hB.subset (hK.indep.diff _) Subset.rfl⟩

    · exact subset_union_left
    · rw [contract_closure_eq, subset_diff, disjoint_union_left, and_iff_left disjoint_sdiff_left,
        and_iff_left (hdj.mono_left hB.subset), ← closure_union_closure_left_eq,
        hB.closure_eq_closure, closure_closure, closure_union_closure_left_eq, union_diff_self,
        union_eq_self_of_subset_left hIK, hK.closure_eq_closure]
      exact union_subset (hB.subset.trans (M.closure_subset_closure subset_union_left))
        (M.subset_closure_of_subset (diff_subset.trans subset_union_right))

    rw [diff_subset_iff, union_comm B, ← union_assoc]
    exact hK.subset.trans <| subset_union_left

  have hb' : ∀ ⦃B⦄, M.Basis B (M.closure I) →
      (B ∩ J).encard + (M ／ (K \ I) ↾ (B ∪ J \ (K \ I)))✶.erk = (J \ (K \ I)).encard := by
    intro B hB
    rw [(hb hB).1.erk_dual_restrict, union_diff_left,
      ← encard_diff_add_encard_inter (J \ (K \ I)) B, add_comm, inter_comm _ B,
      inter_diff_distrib_left, (hdj.mono_left hB.subset).inter_eq, diff_empty]

  have hind : ∀ Y, (M ↾ (Y ∪ J)).Indep (K \ I) := by
    intro Y
    rw [restrict_indep_iff, and_iff_right (hK.indep.diff I), diff_subset_iff, union_comm Y,
      ← union_assoc]
    exact hK.subset.trans subset_union_left
  have hI'b := hII'.symm ▸ hI'.basis_closure
  rw [← (hind I).contract_er_dual_eq,  ← (hind I').contract_er_dual_eq,
    restrict_contract_eq_contract_restrict _ (hb hI.basis_closure).2,
    restrict_contract_eq_contract_restrict _ (hb hI'b).2,
    union_diff_distrib, sdiff_eq_left.2 disjoint_sdiff_right,
    union_diff_distrib, sdiff_eq_left.2 (hdj.mono_left hI'b.subset), hb' hI.basis_closure, hb' hI'b]

lemma Basis'.encard_dual_switch_switch_eq {I I' J J' X Y : Set α}
    (hI : M.Basis' I X) (hI' : M.Basis' I' X) (hJ : M.Basis' J Y) (hJ' : M.Basis' J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk := by
  rw [hI.indep.encard_inter_add_erk_dual_eq_of_closure_eq_closure hI'.indep
      (by rw [hI.closure_eq_closure, hI'.closure_eq_closure]) hJ.indep,
    inter_comm, union_comm, hJ.indep.encard_inter_add_erk_dual_eq_of_closure_eq_closure hJ'.indep
      (by rw [hJ.closure_eq_closure, hJ'.closure_eq_closure]) hI'.indep, inter_comm, union_comm]

/-- If `X` and `Y` are sets, then `|I ∩ J| + (M ↾ (I ∪ J))✶.erk` has the same value for
every basis `I` of `X` and `J` of `Y`. -/
lemma Basis.encard_dual_switch_switch_eq {I I' J J' X Y : Set α}
    (hI : M.Basis I X) (hI' : M.Basis I' X) (hJ : M.Basis J Y) (hJ' : M.Basis J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk :=
  hI.basis'.encard_dual_switch_switch_eq hI'.basis' hJ.basis' hJ'.basis'

noncomputable def localConn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let I := (M.exists_basis' X).choose
  let J := (M.exists_basis' Y).choose
  (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk

lemma localConn_comm (M : Matroid α) (X Y : Set α) : M.localConn X Y = M.localConn Y X := by
  simp_rw [localConn, union_comm, inter_comm]

lemma Basis'.localConn_eq (hI : M.Basis' I X) (hJ : M.Basis' J Y) :
    M.localConn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk := by
  simp_rw [localConn, hI.encard_dual_switch_switch_eq (M.exists_basis' X).choose_spec hJ
    (M.exists_basis' Y).choose_spec]

lemma Basis.localConn_eq (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.localConn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis'.localConn_eq hJ.basis'

lemma Indep.localConn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.localConn I J = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis_self.localConn_eq hJ.basis_self

lemma Basis'.localConn_eq_of_disjoint (hI : M.Basis' I X) (hJ : M.Basis' J Y) (hXY : Disjoint X Y) :
    M.localConn X Y = (M ↾ (I ∪ J))✶.erk := by
  rw [hI.localConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma localConn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.Basis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.localConn X Y = F.encard := by
  have hF' : M.Basis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.basis_inter_ground.basis_subset diff_subset
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.localConn_eq hJ, hF'.erk_dual_restrict, diff_diff_cancel_left hFIJ,
    (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma localConn_eq_encard_of_diff' {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFI : F ⊆ I)  (hF : M.Basis' ((I \ F) ∪ J) (X ∪ Y)) :
    M.localConn X Y = F.encard := by
  apply localConn_eq_encard_of_diff hXY hI hJ (hFI.trans subset_union_left)
  rwa [union_diff_distrib, (sdiff_eq_left (x := J)).2 ]
  exact (hXY.symm.mono hJ.subset (hFI.trans hI.subset))

lemma er_add_er_eq_er_union_add_localConn (M : Matroid α) (X Y : Set α) :
    M.er X + M.er Y = M.er (X ∪ Y) + M.localConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  obtain ⟨B, hB⟩ := M.exists_basis' (I ∪ J)
  have hB' : M.Basis' B (X ∪ Y) := by
    rw [basis'_iff_basis_closure, ← closure_closure_union_closure_eq_closure_union,
      ← hI.closure_eq_closure, ← hJ.closure_eq_closure,
      closure_closure_union_closure_eq_closure_union, ← hB.closure_eq_closure]
    exact ⟨hB.indep.basis_closure, hB.subset.trans (union_subset_union hI.subset hJ.subset)⟩
  rw [hI.localConn_eq hJ, ← hI.encard, ← hJ.encard, ← encard_union_add_encard_inter, ← hB'.encard,
    ← (base_restrict_iff'.2 hB).encard_compl_eq, restrict_ground_eq, ← add_assoc, add_comm B.encard,
    add_assoc, add_comm B.encard, encard_diff_add_encard_of_subset hB.subset, add_comm]

lemma er_inter_le_localConn (M : Matroid α) (X Y : Set α) : M.er (X ∩ Y) ≤ M.localConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' (X ∩ Y)
  obtain ⟨IX, hIX⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_left)
  obtain ⟨IY, hIY⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_right)
  rw [← hI.encard, hIX.1.localConn_eq hIY.1]
  exact (encard_le_card (subset_inter hIX.2 hIY.2)).trans le_self_add

lemma localConn_closure_left (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn (M.closure X) Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI.localConn_eq hJ, hI.basis_closure_right.basis'.localConn_eq hJ]

lemma localConn_closure_right (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn X (M.closure Y) := by
  rw [localConn_comm, localConn_closure_left, localConn_comm]

lemma localConn_closure_closure (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn (M.closure X) (M.closure Y) := by
  rw [localConn_closure_left, localConn_closure_right]

lemma localConn_mono_left {X' : Set α} (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.localConn X' Y ≤ M.localConn X Y := by
  obtain ⟨I', hI'⟩ := M.exists_basis' X'
  obtain ⟨I, hI, hII'⟩ := hI'.indep.subset_basis'_of_subset (hI'.subset.trans hX)
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI'.localConn_eq hJ, hI.localConn_eq hJ]
  refine add_le_add (encard_le_card (inter_subset_inter_left _ hII')) (Minor.erk_le ?_)
  rw [dual_minor_iff]
  exact (Restriction.of_subset M (union_subset_union_left _ hII')).minor

lemma localConn_mono_right {Y' : Set α} (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.localConn X Y' ≤ M.localConn X Y := by
  rw [localConn_comm, localConn_comm _ X]
  exact M.localConn_mono_left hY _

lemma localConn_mono {X' Y' : Set α} (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.localConn X' Y' ≤ M.localConn X Y :=
  ((M.localConn_mono_left hX Y').trans (M.localConn_mono_right _ hY))

@[simp] lemma empty_localConn (M : Matroid α) (X : Set α) : M.localConn ∅ X = 0 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [(M.empty_indep.basis_self.basis').localConn_eq hI, empty_inter, encard_empty,
    erk_dual_restrict_eq_zero_iff.2 (by simpa using hI.indep), zero_add]

@[simp] lemma localConn_empty (M : Matroid α) (X : Set α) : M.localConn X ∅ = 0 := by
  rw [localConn_comm, empty_localConn]

lemma localConn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.localConn X Y = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.localConn_eq hJ, inter_eq_self_of_subset_left hIJ, union_eq_self_of_subset_left hIJ,
    hJ.indep.erk_dual_restrict_eq, ← hI.encard, add_zero]

lemma localConn_eq_zero (M : Matroid α) (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : M.localConn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [skew_iff_closure_skew, localConn_closure_closure, ← hI.closure_eq_closure,
    ← hJ.closure_eq_closure, ← skew_iff_closure_skew, ← localConn_closure_closure,
    hI.indep.localConn_eq hJ.indep, add_eq_zero_iff, encard_eq_zero, ← disjoint_iff_inter_eq_empty,
    erk_dual_restrict_eq_zero_iff, hI.indep.skew_iff_disjoint_union_indep hJ.indep]

lemma localConn_eq_localConn_inter_ground (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn (X ∩ M.E) (Y ∩ M.E) := by
  rw [localConn_closure_closure, ← closure_inter_ground, ← closure_inter_ground _ Y,
    ← localConn_closure_closure]

lemma localConn_eq_localConn_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn (X ∩ M.E) Y := by
  rw [localConn_closure_left, ← closure_inter_ground, ← localConn_closure_left]

lemma localConn_eq_localConn_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.localConn X Y = M.localConn X (Y ∩ M.E) := by
  rw [localConn_closure_right, ← closure_inter_ground, ← localConn_closure_right]

lemma localConn_restrict_univ_eq (M : Matroid α) (X Y : Set α) :
    (M ↾ univ).localConn X Y = M.localConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI.localConn_eq hJ,
    (basis_restrict_univ_iff.2 hI).localConn_eq (basis_restrict_univ_iff.2 hJ),
    restrict_restrict_eq _ (subset_univ _)]

end localConn

section conn


noncomputable abbrev conn (M : Matroid α) (X : Set α) : ℕ∞ := M.localConn X (M.E \ X)

lemma conn_eq_localConn (M : Matroid α) (X : Set α) : M.conn X = M.localConn X (M.E \ X) := rfl

lemma conn_eq_conn_inter_ground (M : Matroid α) (X : Set α) : M.conn X = M.conn (X ∩ M.E) := by
  rw [conn, localConn_eq_localConn_inter_ground_left, conn, diff_inter_self_eq_diff]

lemma conn_restrict_univ_eq (M : Matroid α) (X : Set α) : (M ↾ univ).conn X = M.conn X := by
   rw [conn, localConn_restrict_univ_eq, restrict_ground_eq,
    localConn_eq_localConn_inter_ground_right, diff_eq, inter_right_comm, univ_inter, ← diff_eq]

@[simp] lemma conn_compl (M : Matroid α) (X : Set α) : M.conn (M.E \ X) = M.conn X := by
  rw [eq_comm, conn_eq_conn_inter_ground, conn, diff_inter_self_eq_diff, conn, localConn_comm,
    inter_comm]
  simp

/-- Connectivity is self-dual. -/
lemma localConn_compl_dual (M : Matroid α) (X : Set α) : M.conn X = M✶.conn X := by
  suffices ∀ X ⊆ M.E, M.localConn X (M.E \ X) = M✶.localConn X (M.E \ X) by
    rw [conn, conn, localConn_eq_localConn_inter_ground_left,
      M✶.localConn_eq_localConn_inter_ground_left, ← diff_inter_self_eq_diff (s := M.E) (t := X),
      this _ inter_subset_right, dual_ground, diff_inter_self_eq_diff]
  intro X hX

  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis (M.E \ X)
  obtain ⟨BX, hBX, hIBX⟩ := hI.indep.subset_basis_of_subset
    (subset_union_left (s := I) (t := J))
  have hIJE : M.Spanning (I ∪ J) := by
    rw [spanning_iff_closure, ← closure_closure_union_closure_eq_closure_union,
      hI.closure_eq_closure, hJ.closure_eq_closure, closure_closure_union_closure_eq_closure_union,
      union_diff_cancel hX, closure_ground]

  have hBXb : M.Base BX := by
    rw [← basis_ground_iff, ← hIJE.closure_eq]
    exact hBX.basis_closure_right

  obtain rfl : I = BX ∩ X := hI.eq_of_subset_indep (hBXb.indep.inter_right _)
    (subset_inter hIBX hI.subset) inter_subset_right

  have hBXdual := hBXb.compl_inter_basis_of_inter_basis hI
  rw [diff_inter_diff, union_comm, ← diff_diff] at hBXdual

  obtain ⟨BY, hBY, hJBY⟩ := hJ.indep.subset_basis_of_subset (subset_union_right (s := BX ∩ X))
  have hBYb : M.Base BY := by
    rw [← basis_ground_iff, ← hIJE.closure_eq]
    exact hBY.basis_closure_right

  obtain rfl : J = BY ∩ (M.E \ X) := hJ.eq_of_subset_indep (hBYb.indep.inter_right _)
    (subset_inter hJBY hJ.subset) inter_subset_right

  have hBYdual := hBYb.compl_inter_basis_of_inter_basis hJ
  rw [diff_inter_diff, union_comm, ← diff_diff, diff_diff_cancel_left hX] at hBYdual

  rw [hBYdual.basis'.localConn_eq_of_disjoint hBXdual.basis' disjoint_sdiff_right,
    hI.basis'.localConn_eq_of_disjoint hJ.basis' disjoint_sdiff_right, hBX.erk_dual_restrict,
    union_diff_distrib, diff_eq_empty.2 inter_subset_left, empty_union,
    Basis.erk_dual_restrict (hBYb.compl_base_dual.basis_ground.basis_subset _ _)]

  · rw [union_diff_distrib, diff_eq_empty.2 (diff_subset_diff_left hX), empty_union, diff_diff,
      diff_diff, ← union_assoc, union_comm, ← diff_diff, diff_diff_cancel_left hBYb.subset_ground,
      ← diff_diff, inter_diff_distrib_left, inter_eq_self_of_subset_left hBYb.subset_ground,
      diff_self_inter]
  · rw [← union_diff_cancel hX, union_diff_distrib, union_diff_cancel hX, diff_diff, diff_diff]
    refine union_subset_union_right _ (diff_subset_diff_right ?_)
    simp only [union_subset_iff, subset_union_left, true_and]
    exact hBX.subset.trans (union_subset_union inter_subset_right inter_subset_left)

  exact union_subset (diff_subset.trans hX) (diff_subset.trans diff_subset)

-- lemma conn_submod (M : Matroid α) (X Y : Set α) :
--     M.conn (X ∪ Y) + M.conn (X ∩ Y) ≤ M.conn X + M.conn Y := by
--   simp_rw [← conn_restrict_univ_eq M]
--   set M' := M ↾ univ
--   obtain ⟨I, hI⟩ := M'.exists_basis X
--   obtain ⟨J, hJ⟩ := M'.exists_basis Y



end conn
