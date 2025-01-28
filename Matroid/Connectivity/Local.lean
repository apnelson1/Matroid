import Matroid.Connectivity.Skew
import Matroid.ForMathlib.Matroid.Map
import Matroid.ForMathlib.ENat
import Matroid.Uniform

open Set Set.Notation

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J K X Y : Set α}

section localEConn

lemma Indep.encard_inter_add_eRank_dual_congr (hI : M.Indep I) (hI' : M.Indep I')
    (hII' : M.closure I = M.closure I') (hJ : M.Indep J) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.eRank = (I' ∩ J).encard + (M ↾ (I' ∪ J))✶.eRank := by
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
        and_iff_left (hdj.mono_left hB.subset), closure_union_congr_left hB.closure_eq_closure,
        closure_union_closure_left_eq, union_diff_cancel hIK, hK.closure_eq_closure]
      exact union_subset (hB.subset.trans (M.closure_subset_closure subset_union_left))
        (M.subset_closure_of_subset (diff_subset.trans subset_union_right))

    rw [diff_subset_iff, union_comm B, ← union_assoc]
    exact hK.subset.trans <| subset_union_left

  have hb' : ∀ ⦃B⦄, M.Basis B (M.closure I) →
      (B ∩ J).encard + (M ／ (K \ I) ↾ (B ∪ J \ (K \ I)))✶.eRank = (J \ (K \ I)).encard := by
    intro B hB
    rw [(hb hB).1.eRank_dual_restrict, union_diff_left,
      ← encard_diff_add_encard_inter (J \ (K \ I)) B, add_comm, inter_comm _ B,
      inter_diff_distrib_left, (hdj.mono_left hB.subset).inter_eq, diff_empty]

  have hind : ∀ Y, (M ↾ (Y ∪ J)).Indep (K \ I) := fun Y ↦ by
    rw [restrict_indep_iff, and_iff_right (hK.indep.diff I), diff_subset_iff, union_comm Y,
      ← union_assoc]
    exact hK.subset.trans subset_union_left
  have hI'b := hII'.symm ▸ hI'.basis_closure
  rw [← (hind I).contract_eRk_dual_eq,  ← (hind I').contract_eRk_dual_eq,
    restrict_contract_eq_contract_restrict _ (hb hI.basis_closure).2,
    restrict_contract_eq_contract_restrict _ (hb hI'b).2,
    union_diff_distrib, sdiff_eq_left.2 disjoint_sdiff_right,
    union_diff_distrib, sdiff_eq_left.2 (hdj.mono_left hI'b.subset), hb' hI.basis_closure, hb' hI'b]

lemma Basis'.encard_dual_congr₂ {I I' J J' X Y : Set α} (hI : M.Basis' I X) (hI' : M.Basis' I' X)
    (hJ : M.Basis' J Y) (hJ' : M.Basis' J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.eRank = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.eRank := by
  rw [hI.indep.encard_inter_add_eRank_dual_congr hI'.indep
      (by rw [hI.closure_eq_closure, hI'.closure_eq_closure]) hJ.indep,
    inter_comm, union_comm, hJ.indep.encard_inter_add_eRank_dual_congr hJ'.indep
      (by rw [hJ.closure_eq_closure, hJ'.closure_eq_closure]) hI'.indep, inter_comm, union_comm]

/-- If `X` and `Y` are sets, then `|I ∩ J| + (M ↾ (I ∪ J))✶.eRank` has the same value for
every basis `I` of `X` and `J` of `Y`. -/
lemma Basis.encard_dual_congr₂ {I I' J J' X Y : Set α} (hI : M.Basis I X) (hI' : M.Basis I' X)
    (hJ : M.Basis J Y) (hJ' : M.Basis J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.eRank = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.eRank :=
  hI.basis'.encard_dual_congr₂ hI'.basis' hJ.basis' hJ'.basis'

/-- The `ℕ∞`-valued local connectivity between two sets `X` and `Y`, often written `⊓ (X,Y)`.
Defined to correctly describe the connectivity even when one or both sets has infinite rank.
For a `ℕ`-valued version, see `Matroid.localConn`. -/
noncomputable def localEConn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let I := (M.exists_basis' X).choose
  let J := (M.exists_basis' Y).choose
  (I ∩ J).encard + (M ↾ (I ∪ J))✶.eRank

lemma localEConn_comm (M : Matroid α) (X Y : Set α) : M.localEConn X Y = M.localEConn Y X := by
  simp_rw [localEConn, union_comm, inter_comm]

lemma Basis'.localEConn_eq (hI : M.Basis' I X) (hJ : M.Basis' J Y) :
    M.localEConn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.eRank := by
  simp_rw [localEConn, hI.encard_dual_congr₂ (M.exists_basis' X).choose_spec hJ
    (M.exists_basis' Y).choose_spec]

lemma Basis'.localEConn_eq_encard_inter_add_eRelRk (hI : M.Basis' I X) (hJ : M.Basis' J Y) :
    M.localEConn X Y = (I ∩ J).encard + M✶.eRelRk (M✶.E \ (I ∪ J)) M✶.E := by
  rw [hI.localEConn_eq hJ,
    ← delete_compl (union_subset hI.indep.subset_ground hJ.indep.subset_ground),
    delete_dual_eq_dual_contract, eRank_contract_eq_eRelRk_ground]
  rfl

lemma Basis.localEConn_eq (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.localEConn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.eRank :=
  hI.basis'.localEConn_eq hJ.basis'

lemma Indep.localEConn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.localEConn I J = (I ∩ J).encard + (M ↾ (I ∪ J))✶.eRank :=
  hI.basis_self.localEConn_eq hJ.basis_self

lemma Basis'.localEConn_eq_of_disjoint (hI : M.Basis' I X) (hJ : M.Basis' J Y)
    (hXY : Disjoint X Y) : M.localEConn X Y = (M ↾ (I ∪ J))✶.eRank := by
  rw [hI.localEConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma localEConn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.Basis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.localEConn X Y = F.encard := by
  have hF' : M.Basis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.basis_inter_ground.basis_subset diff_subset
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.localEConn_eq hJ, hF'.eRank_dual_restrict, diff_diff_cancel_left hFIJ,
    (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma localEConn_eq_encard_of_diff' {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFI : F ⊆ I)  (hF : M.Basis' ((I \ F) ∪ J) (X ∪ Y)) :
    M.localEConn X Y = F.encard := by
  apply localEConn_eq_encard_of_diff hXY hI hJ (hFI.trans subset_union_left)
  rwa [union_diff_distrib, (sdiff_eq_left (x := J)).2 ]
  exact (hXY.symm.mono hJ.subset (hFI.trans hI.subset))

lemma eRk_add_eRk_eq_eRk_union_add_localEConn (M : Matroid α) (X Y : Set α) :
    M.eRk X + M.eRk Y = M.eRk (X ∪ Y) + M.localEConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  obtain ⟨B, hB⟩ := M.exists_basis' (I ∪ J)
  have hB' : M.Basis' B (X ∪ Y) := by
    rw [basis'_iff_basis_closure, ← closure_closure_union_closure_eq_closure_union,
      ← hI.closure_eq_closure, ← hJ.closure_eq_closure,
      closure_closure_union_closure_eq_closure_union, ← hB.closure_eq_closure]
    exact ⟨hB.indep.basis_closure, hB.subset.trans (union_subset_union hI.subset hJ.subset)⟩
  rw [hI.localEConn_eq hJ, ← hI.encard_eq_eRk, ← hJ.encard_eq_eRk, ← encard_union_add_encard_inter,
    ← hB'.encard_eq_eRk, ← (base_restrict_iff'.2 hB).encard_compl_eq, restrict_ground_eq,
    ← add_assoc, add_comm B.encard, add_assoc, add_comm B.encard,
    encard_diff_add_encard_of_subset hB.subset, add_comm]

lemma eRk_inter_le_localEConn (M : Matroid α) (X Y : Set α) : M.eRk (X ∩ Y) ≤ M.localEConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' (X ∩ Y)
  obtain ⟨IX, hIX⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_left)
  obtain ⟨IY, hIY⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_right)
  rw [← hI.encard_eq_eRk, hIX.1.localEConn_eq hIY.1]
  exact (encard_le_card (subset_inter hIX.2 hIY.2)).trans le_self_add

@[simp] lemma localEConn_closure_left (M : Matroid α) (X Y : Set α) :
    M.localEConn (M.closure X) Y = M.localEConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI.localEConn_eq hJ, hI.basis_closure_right.basis'.localEConn_eq hJ]

@[simp] lemma localEConn_closure_right (M : Matroid α) (X Y : Set α) :
    M.localEConn X (M.closure Y) = M.localEConn X Y := by
  rw [localEConn_comm, localEConn_closure_left, localEConn_comm]

@[simp] lemma localEConn_closure_closure (M : Matroid α) (X Y : Set α) :
    M.localEConn (M.closure X) (M.closure Y) = M.localEConn X Y := by
  rw [localEConn_closure_left, localEConn_closure_right]

lemma localEConn_mono_left {X' : Set α} (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.localEConn X' Y ≤ M.localEConn X Y := by
  obtain ⟨I', hI'⟩ := M.exists_basis' X'
  obtain ⟨I, hI, hII'⟩ := hI'.indep.subset_basis'_of_subset (hI'.subset.trans hX)
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI'.localEConn_eq hJ, hI.localEConn_eq hJ]
  refine add_le_add (encard_le_card (inter_subset_inter_left _ hII')) (Minor.eRank_le ?_)
  rw [dual_minor_iff]
  exact (Restriction.of_subset M (union_subset_union_left _ hII')).minor

lemma localEConn_mono_right {Y' : Set α} (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.localEConn X Y' ≤ M.localEConn X Y := by
  rw [localEConn_comm, localEConn_comm _ X]
  exact M.localEConn_mono_left hY _

lemma localEConn_mono {X' Y' : Set α} (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.localEConn X' Y' ≤ M.localEConn X Y :=
  ((M.localEConn_mono_left hX Y').trans (M.localEConn_mono_right _ hY))

@[simp] lemma empty_localEConn (M : Matroid α) (X : Set α) : M.localEConn ∅ X = 0 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [(M.empty_indep.basis_self.basis').localEConn_eq hI, empty_inter, encard_empty,
    eRank_dual_restrict_eq_zero_iff.2 (by simpa using hI.indep), zero_add]

@[simp] lemma localEConn_empty (M : Matroid α) (X : Set α) : M.localEConn X ∅ = 0 := by
  rw [localEConn_comm, empty_localEConn]

lemma localEConn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.localEConn X Y = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.localEConn_eq hJ, inter_eq_self_of_subset_left hIJ, union_eq_self_of_subset_left hIJ,
    hJ.indep.eRank_dual_restrict_eq, ← hI.encard_eq_eRk, add_zero]

lemma localEConn_eq_zero (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.localEConn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [skew_iff_closure_skew, ← localEConn_closure_closure, ← hI.closure_eq_closure,
    ← hJ.closure_eq_closure, ← skew_iff_closure_skew, localEConn_closure_closure,
    hI.indep.localEConn_eq hJ.indep, add_eq_zero, encard_eq_zero, ← disjoint_iff_inter_eq_empty,
    eRank_dual_restrict_eq_zero_iff, hI.indep.skew_iff_disjoint_union_indep hJ.indep]

lemma Skew.localEConn (hXY : M.Skew X Y) : M.localEConn X Y = 0 := by
  rwa [localEConn_eq_zero]

lemma localEConn_inter_ground (M : Matroid α) (X Y : Set α) :
    M.localEConn (X ∩ M.E) (Y ∩ M.E) = M.localEConn X Y := by
  rw [← localEConn_closure_closure, closure_inter_ground, closure_inter_ground _ Y,
    localEConn_closure_closure]

@[simp] lemma localEConn_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.localEConn (X ∩ M.E) Y = M.localEConn X Y := by
  rw [← localEConn_closure_left, closure_inter_ground, localEConn_closure_left]

@[simp] lemma localEConn_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.localEConn X (Y ∩ M.E) = M.localEConn X Y := by
  rw [← localEConn_closure_right, closure_inter_ground, localEConn_closure_right]

@[simp] lemma localEConn_restrict_eq (M : Matroid α) (X Y R : Set α) :
    (M ↾ R).localEConn X Y = M.localEConn (X ∩ R) (Y ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis' X
  obtain ⟨J, hJ⟩ := (M ↾ R).exists_basis' Y
  have ⟨hI', hI'R⟩ := basis'_restrict_iff.1 hI
  have ⟨hJ', hJ'R⟩ := basis'_restrict_iff.1 hJ
  rw [hI.localEConn_eq hJ, hI'.localEConn_eq hJ', restrict_restrict_eq _ (union_subset hI'R hJ'R)]

lemma localEConn_restrict_univ_eq (M : Matroid α) (X Y : Set α) :
    (M ↾ univ).localEConn X Y = M.localEConn X Y := by
  simp

lemma localEConn_restrict_of_subset (M : Matroid α) {R : Set α} (hXR : X ⊆ R) (hYR : Y ⊆ R) :
    (M ↾ R).localEConn X Y = M.localEConn X Y := by
  rw [localEConn_restrict_eq, inter_eq_self_of_subset_left hXR, inter_eq_self_of_subset_left hYR]

lemma localEConn_delete_eq (M : Matroid α) (X Y D : Set α) :
    (M ＼ D).localEConn X Y = M.localEConn (X \ D) (Y \ D) := by
  rw [delete_eq_restrict, localEConn_restrict_eq, ← inter_diff_assoc, inter_diff_right_comm,
    ← inter_diff_assoc, inter_diff_right_comm, localEConn_inter_ground]

lemma localEConn_delete_eq_of_disjoint (M : Matroid α) {D : Set α} (hXD : Disjoint X D)
    (hYD : Disjoint Y D) : (M ＼ D).localEConn X Y = M.localEConn X Y := by
  rw [localEConn_delete_eq, hXD.sdiff_eq_left, hYD.sdiff_eq_left]

@[simp] lemma localEConn_map {β : Type*} (M : Matroid α) (f : α → β) (hf) (X Y : Set β) :
    (M.map f hf).localEConn X Y = M.localEConn (f ⁻¹' X) (f ⁻¹' Y) := by
  obtain ⟨I, hI⟩ := M.exists_basis (f ⁻¹' X ∩ M.E)
  obtain ⟨J, hJ⟩ := M.exists_basis (f ⁻¹' Y ∩ M.E)
  have hI' := hI.map hf
  have hJ' := hJ.map hf
  rw [image_preimage_inter] at hI' hJ'
  rw [← M.localEConn_inter_ground, hI.localEConn_eq hJ, ← localEConn_inter_ground, map_ground,
    hI'.localEConn_eq hJ', ← hf.image_inter hI.indep.subset_ground hJ.indep.subset_ground,
    (hf.mono (inter_subset_left.trans hI.indep.subset_ground)).encard_image,
    ← image_union, ← M.map_restrict f hf (I ∪ J), map_dual, eRank_map]

@[simp] lemma localEConn_comap {β : Type*} (M : Matroid β) (f : α → β) (X Y : Set α) :
    (M.comap f).localEConn X Y = M.localEConn (f '' X) (f '' Y) := by
  suffices aux : ∀ (N : Matroid β) X Y,
      (N.comap f).localEConn (f ⁻¹' (f '' X)) (f ⁻¹' (f '' Y)) = N.localEConn (f '' X) (f '' Y) by
    specialize aux (M ↾ univ) X Y
    rw [← localEConn_restrict_univ_eq, ← M.localEConn_restrict_univ_eq, ← aux,
      comap_restrict, preimage_univ, le_antisymm_iff]
    refine ⟨(localEConn_mono _ (subset_preimage_image _ _) (subset_preimage_image _ _)), ?_⟩
    rw [← localEConn_closure_closure _ X, ← comap_restrict_univ]
    refine localEConn_mono _ ?_ ?_
    all_goals
    · rw [comap_closure_eq]
      exact preimage_mono (subset_closure _ _)
  intro N P Q

  obtain ⟨I₀, hI₀⟩ := (N.comap f).exists_basis' (f ⁻¹' (f '' P) ∩ f ⁻¹' (f '' Q))
  obtain ⟨IP, hIP, hI₀IP⟩ := hI₀.indep.subset_basis'_of_subset (hI₀.subset.trans inter_subset_left)
  obtain ⟨IQ, hIQ, hI₀IQ⟩ := hI₀.indep.subset_basis'_of_subset (hI₀.subset.trans inter_subset_right)
  obtain ⟨hIP', hPinj, hIPP⟩ := comap_basis'_iff.1 hIP
  obtain ⟨hIQ', hQinj, hIQQ⟩ := comap_basis'_iff.1 hIQ

  rw [image_preimage_image] at hIP' hIQ'

  have hinj : InjOn f (IP ∪ IQ) := by
    rw [show IP ∪ IQ = IP ∪ (IQ \ IP) by simp, injOn_union disjoint_sdiff_right,
      and_iff_right hPinj, and_iff_right (hQinj.mono diff_subset)]
    refine fun x hx y ⟨hyQ, hyP⟩ hxy ↦ hyP <| hI₀IP ?_
    apply hI₀.mem_of_insert_indep
    · simp only [mem_inter_iff, mem_preimage]
      exact ⟨hxy ▸ (by simpa using hIP.subset hx), by simpa using hIQ.subset hyQ⟩
    exact hIQ.indep.subset <| insert_subset hyQ hI₀IQ

  rw [hIP.localEConn_eq hIQ, hIP'.localEConn_eq hIQ',
    ← hinj.image_inter subset_union_left subset_union_right,
    (hPinj.mono inter_subset_left).encard_image, ← image_union,
    ← comapOn_map N hinj, map_dual, eRank_map, comapOn]

@[simp] lemma localEConn_ground_eq (M : Matroid α) (X : Set α) : M.localEConn X M.E = M.eRk X := by
  suffices hss : ∀ Y ⊆ M.E, M.localEConn Y M.E = M.eRk Y by
    rw [← localEConn_inter_ground_left, ← eRk_inter_ground, ← hss _ inter_subset_right]
  refine fun Y hYE ↦ ?_
  obtain ⟨I, hI⟩ := M.exists_basis Y
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_superset
  rw [hI.localEConn_eq hB.basis_ground, hI.eRk_eq_encard, inter_eq_self_of_subset_left hIB,
    union_eq_self_of_subset_left hIB, hB.indep.restrict_eq_freeOn, eRank_eq_zero_iff.2, add_zero]
  simp

@[simp] lemma ground_localEConn_eq (M : Matroid α) (X : Set α) : M.localEConn M.E X = M.eRk X := by
  rw [localEConn_comm, localEConn_ground_eq]

lemma localEConn_le_eRk_left (M : Matroid α) (X Y : Set α) : M.localEConn X Y ≤ M.eRk X := by
  rw [← localEConn_inter_ground_right]
  exact (M.localEConn_mono_right X inter_subset_right).trans <| by simp

lemma localEConn_le_eRk_right (M : Matroid α) (X Y : Set α) : M.localEConn X Y ≤ M.eRk Y := by
  rw [localEConn_comm]
  apply localEConn_le_eRk_left

lemma ModularPair.localEConn_eq_eRk_inter (h : M.ModularPair X Y) :
    M.localEConn X Y = M.eRk (X ∩ Y) := by
  obtain ⟨I, hIu, hIX, hIY, hIi⟩ := h.exists_common_basis
  rw [hIX.localEConn_eq hIY, ← hIi.encard_eq_eRk, ← inter_inter_distrib_left,
    ← inter_union_distrib_left, inter_eq_self_of_subset_left hIu.subset,
    hIu.indep.restrict_eq_freeOn, freeOn_dual_eq, loopyOn_eRank_eq, add_zero, ← inter_assoc]

/-- Contracting a subset of `Y` that is skew to `X` doesn't change the local connectivity
between `X` and `Y`. -/
lemma localEConn_contract_right_skew_left {C Y : Set α} (hXC : M.Skew X C) (hCY : C ⊆ Y) :
    (M ／ C).localEConn X (Y \ C) = M.localEConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' C
  obtain ⟨J, hJ, h_inter⟩ := hI.exists_basis'_inter_eq_of_superset hCY
  have hIJ : I ⊆ J := by simp [← h_inter]

  obtain ⟨K, hK⟩ := M.exists_basis' X

  have hKC : Disjoint K C :=
    hXC.diff_loops_disjoint_left.mono_left (subset_diff.2 ⟨hK.subset, hK.indep.disjoint_loops⟩)

  have hbY : (M ／ C).Basis' (J \ I) (Y \ C)
  · rw [← h_inter, diff_self_inter, basis'_iff_basis_closure, basis_iff_indep_subset_closure,
      contract_closure_eq, contract_closure_eq, diff_union_of_subset hCY,
      diff_union_self, and_iff_left (diff_subset_diff_left hJ.subset), hI.contract_indep_diff_iff,
      ← h_inter, diff_union_inter, and_iff_right hJ.indep, ← hJ.closure_eq_closure]
    exact ⟨diff_subset_diff_left (M.subset_closure J hJ.indep.subset_ground),
      diff_subset_diff_left <| M.closure_mono subset_union_left⟩

  have hbX : (M ／ C).Basis' K X
  · suffices h' : ((M ／ C) ↾ X).Basis' K X
    · rw [basis'_restrict_iff, inter_self] at h'
      exact h'.1
    rwa [hXC.symm.contract_restrict_eq, basis'_restrict_iff, inter_self, and_iff_left hK.subset]

  rw [hbX.localEConn_eq hbY, hK.localEConn_eq hJ, inter_diff_distrib_left,
    (hKC.mono_right hI.subset).inter_eq, diff_empty]
  convert rfl using 2
  obtain ⟨B, hB, hJB⟩ := hJ.indep.subset_basis_of_subset subset_union_right
    (union_subset hK.indep.subset_ground hJ.indep.subset_ground)

  have hB' : (M ／ C ↾ (K ∪ (J \ I)))✶.Base (K \ B)
  · suffices (M ／ C ↾ (K ∪ J \ I)).Base ((K ∪ J \ I) \ (K \ B)) by
      simpa [dual_base_iff', diff_subset.trans subset_union_left]
    rw [diff_diff_right, union_diff_left, union_inter_distrib_right,
      inter_eq_self_of_subset_left (diff_subset.trans hJB), union_comm (K ∩ B),
      ← union_assoc, union_eq_self_of_subset_left diff_subset]
    refine Basis.base_restrict (Indep.basis_of_subset_of_subset_closure ?_ ?_ ?_)
    · rw [hI.contract_indep_iff, disjoint_union_right, ← h_inter, diff_self_inter,
        and_iff_right disjoint_sdiff_right,
        and_iff_left (hKC.symm.mono_right inter_subset_left)]

      exact hB.indep.subset <| union_subset
        (union_subset (diff_subset.trans hJB) inter_subset_right) (inter_subset_left.trans hJB)
    · exact union_subset subset_union_right (inter_subset_left.trans subset_union_left)

    rw [contract_closure_eq, ← closure_union_congr_right hI.closure_eq_closure,
      union_right_comm, diff_union_of_subset hIJ, ← inter_eq_self_of_subset_left hJB,
      ← union_inter_distrib_right, union_comm J, inter_eq_self_of_subset_right hB.subset,
      hB.closure_eq_closure, inter_eq_self_of_subset_left hJB, subset_diff,
      disjoint_union_left, and_iff_right hKC, ← h_inter, diff_self_inter,
      and_iff_left disjoint_sdiff_left]

    exact M.subset_closure_of_subset (union_subset_union_right _ diff_subset)
      (union_subset hK.indep.subset_ground hJ.indep.subset_ground)

  rw [← hB.base_restrict.compl_base_dual.encard_eq_eRank, restrict_ground_eq, union_diff_distrib,
    diff_eq_empty.2 hJB, union_empty, hB'.encard_eq_eRank]

/-- TODO : prove this by showing that `⊓ (X ∪ D, Y) = ⊓ (X,Y) + r (D)` for all `D ⊆ cl(X ∪ Y)`
that is skew to `X`. -/
lemma localEConn_insert_left_eq_add_one {e : α} (heX : e ∉ M.closure X)
    (heXY : e ∈ M.closure (X ∪ Y)) : M.localEConn (insert e X) Y = M.localEConn X Y + 1 := by
  have heE : e ∈ M.E := mem_ground_of_mem_closure heXY
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← localEConn_inter_ground_left, insert_inter_of_mem heE,
      aux (by simpa) _ inter_subset_right, localEConn_inter_ground_left]
    rwa [← closure_inter_ground, union_inter_distrib_right, inter_assoc, inter_self,
      ← union_inter_distrib_right, closure_inter_ground]

  obtain ⟨I, hI⟩ := M.exists_basis X
  have heI : e ∉ I := not_mem_subset hI.basis_closure_right.subset heX
  have hIe := hI.insert_basis_insert_of_not_mem_closure (e := e) (by rwa [hI.closure_eq_closure])
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI.basis'.localEConn_eq hJ, hIe.basis'.localEConn_eq hJ]

  by_cases heJ : e ∈ J
  · rw [insert_inter_of_mem heJ, encard_insert_of_not_mem (not_mem_subset inter_subset_left heI),
      insert_union, insert_eq_of_mem (.inr heJ), add_right_comm]

  have hIJ : I ∪ J ⊆ M.E := union_subset hI.indep.subset_ground hJ.indep.subset_ground

  obtain ⟨B, hB⟩ := (M ↾ (I ∪ J)).exists_base

  have heB : e ∉ B := not_mem_subset hB.subset_ground (by simp [heI, heJ])

  have hB' : (M ↾ (insert e (I ∪ J))).Base B
  ·
    rw [base_restrict_iff hIJ] at hB
    refine Basis.base_restrict (hB.indep.basis_of_subset_of_subset_closure ?_ ?_)
    · exact hB.subset.trans (subset_insert _ _)
    rw [hB.closure_eq_closure]
    refine insert_subset ?_ (M.subset_closure _)
    rwa [closure_union_congr_left hI.closure_eq_closure,
      closure_union_congr_right hJ.closure_eq_closure]

  rw [insert_union, insert_inter_of_not_mem heJ, ← hB.compl_base_dual.encard_eq_eRank,
    ← hB'.compl_base_dual.encard_eq_eRank, restrict_ground_eq, insert_diff_of_not_mem _ heB,
      encard_insert_of_not_mem (by simp [heI, heJ]), ← add_assoc, restrict_ground_eq]


lemma FinRk.modularPair_iff_localEConn_eq_eRk_inter (hX : M.FinRk X) (Y : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.localEConn X Y = M.eRk (X ∩ Y) := by
  refine ⟨fun h ↦ h.localEConn_eq_eRk_inter, fun h ↦ ?_⟩
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ := hIi.exists_basis_inter_eq_of_superset inter_subset_left
  obtain ⟨IY, hIY, hIY'⟩ := hIi.exists_basis_inter_eq_of_superset inter_subset_right

  have h_inter : Ii = IX ∩ IY
  · exact hIi.eq_of_subset_indep (hIX.indep.inter_right _)
      (subset_inter (by simp [← hIX']) (by simp [← hIY']))
      (inter_subset_inter hIX.subset hIY.subset)

  rw [hIX.localEConn_eq hIY, ← h_inter, hIi.encard_eq_eRk, ← add_zero (a := M.eRk _), add_assoc,
    zero_add, WithTop.add_left_cancel_iff hX.inter_right.eRk_ne_top, eRank_eq_zero_iff,
    ← eq_dual_iff_dual_eq, loopyOn_dual_eq, dual_ground, restrict_ground_eq, restrict_eq_freeOn_iff]
    at h

  exact h.modularPair_of_union.of_basis_of_basis hIX hIY

lemma localEConn_insert_right_eq_add_one {e : α} (heY : e ∉ M.closure Y)
    (heXY : e ∈ M.closure (X ∪ Y)) : M.localEConn X (insert e Y) = M.localEConn X Y + 1 := by
  rw [localEConn_comm, localEConn_insert_left_eq_add_one heY (by rwa [union_comm]),
    localEConn_comm]

/-- For finite matroids, this is another rearrangement of the formula in
`Matroid.eRk_add_eRk_eq_eRk_union_add_localEConn`.
For infinite matroids it needs a separate proof. -/
lemma localEConn_add_eRelRk_union_eq_eRk (M : Matroid α) (X Y : Set α) :
    M.localEConn X Y + M.eRelRk Y (X ∪ Y) = M.eRk X := by
  wlog hE : X ⊆ M.E ∧ Y ⊆ M.E generalizing X Y with aux
  · rw [← localEConn_inter_ground, ← eRelRk_inter_ground_right, ← eRelRk_inter_ground_left,
      union_inter_distrib_right, aux _ _ ⟨inter_subset_right, inter_subset_right⟩, eRk_inter_ground]
  obtain ⟨hXE, hYE⟩ := hE
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ Y)
  obtain ⟨IX, hIX, hIXi⟩ := hI.exists_basis_inter_eq_of_superset inter_subset_left
  obtain ⟨IY, hIY, hIYi⟩ := hI.exists_basis_inter_eq_of_superset inter_subset_right
  obtain ⟨K, hK, hIYK⟩ := hIY.indep.subset_basis_of_subset (X := IX ∪ IY) subset_union_right

  have hK' : M.Basis K (X ∪ Y)
  · refine hK.basis_closure_right.basis_subset
      (hK.subset.trans (union_subset_union hIX.subset hIY.subset)) ?_
    rw [closure_union_congr_left hIX.closure_eq_closure,
      closure_union_congr_right hIY.closure_eq_closure]
    exact M.subset_closure _ (union_subset hXE hYE)

  have hbas : (M ↾ (IX ∪ IY))✶.Base ((IX ∪ IY) \ K) := by
    simpa using hK.base_restrict.compl_base_dual

  rw [hIX.eRk_eq_encard, hIX.localEConn_eq hIY, hIY.eRelRk_eq_encard_diff_of_subset_basis hK' hIYK,
    ← hbas.encard_eq_eRank, union_diff_distrib, diff_eq_empty.2 hIYK, union_empty, add_assoc,
    ← encard_union_eq (disjoint_sdiff_left.mono_right diff_subset),
    ← encard_diff_add_encard_inter IX IY, add_comm, eq_comm,
    diff_union_diff_cancel_of_inter_subset_of_subset_union
      (inter_subset_right.trans hIYK) hK.subset]

lemma Hyperplane.localEConn_add_one_eq {H X : Set α} (hH : M.Hyperplane H) (hXH : ¬ (X ⊆ H))
    (hXE : X ⊆ M.E := by aesop_mat) : M.localEConn X H + 1 = M.eRk X := by
  rw [← M.localEConn_add_eRelRk_union_eq_eRk X H, ← eRelRk_closure_right,
    (hH.spanning_of_ssuperset (show H ⊂ X ∪ H by simpa)).closure_eq, hH.eRelRk_eq_one]

end localEConn

section localConn

/-- The `ℕ`-valued local connectivity between sets `X` and `Y`, often denoted `⊓ (X, Y)`.
Equal to `M.r X + M.r Y - M.r (X ∪ Y)` if both sets have finite rank.
This is only mathematically meaningful if at least one of `X` and `Y` is known to have finite rank;
otherwise `Matroid.localEConn` is preferable. -/
noncomputable def localConn (M : Matroid α) (X Y : Set α) : ℕ := (M.localEConn X Y).toNat

lemma localConn_comm (M : Matroid α) (X Y : Set α) : M.localConn X Y = M.localConn Y X := by
  rw [localConn, localEConn_comm, localConn]

lemma FinRk.cast_localConn_right_eq (hX : M.FinRk X) (Y : Set α) :
    (M.localConn X Y : ℕ∞) = M.localEConn X Y :=
  ENat.coe_toNat fun htop ↦ hX.eRk_lt_top.not_le
    <| htop.symm.le.trans <| M.localEConn_le_eRk_left X Y

lemma FinRk.cast_localConn_left_eq (hY : M.FinRk Y) : (M.localConn X Y : ℕ∞) = M.localEConn X Y := by
  rw [localConn_comm, hY.cast_localConn_right_eq, localEConn_comm]

lemma FinRk.rk_add_rk_eq_rk_union_add_localConn (hX : M.FinRk X) (hY : M.FinRk Y) :
    M.rk X + M.rk Y = M.rk (X ∪ Y) + M.localConn X Y := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, Nat.cast_add, hX.cast_localConn_right_eq,
    hX.cast_rk_eq, hY.cast_rk_eq, (hX.union hY).cast_rk_eq, eRk_add_eRk_eq_eRk_union_add_localEConn]

lemma rk_add_rk_eq_rk_union_add_localConn (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.rk X + M.rk Y = M.rk (X ∪ Y) + M.localConn X Y :=
  (M.to_finRk X).rk_add_rk_eq_rk_union_add_localConn (M.to_finRk Y)

lemma localConn_inter_ground (M : Matroid α) (X Y : Set α) :
    M.localConn (X ∩ M.E) (Y ∩ M.E) = M.localConn X Y := by
  simp [localConn]

lemma localConn_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.localConn (X ∩ M.E) Y = M.localConn X Y := by
  simp [localConn]

lemma localConn_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.localConn X (Y ∩ M.E) = M.localConn X Y := by
  simp [localConn]

/-- The formula for local connectivity of two finite-rank sets in terms of the rank function.
This uses `ℕ` subtraction which never overflows. -/
lemma FinRk.localConn_eq_rk_add_rk_sub (hX : M.FinRk X) (hY : M.FinRk Y) :
    M.localConn X Y = M.rk X + M.rk Y - M.rk (X ∪ Y) := by
  rw [hX.rk_add_rk_eq_rk_union_add_localConn hY, add_comm]
  exact Nat.eq_sub_of_add_eq rfl

/-- The formula for local connectivity of two finite-rank sets written with `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma FinRk.localConn_cast_int_eq (hX : M.FinRk X) (hY : M.FinRk Y) :
    (M.localConn X Y : ℤ) = M.rk X + M.rk Y - M.rk (X ∪ Y) := by
  rw [hX.localConn_eq_rk_add_rk_sub hY, ← Nat.cast_add]
  exact Int.natCast_sub (rk_union_le_rk_add_rk _ _ _)

/-- The formula for local connectivity in terms of the rank function.
This uses `ℕ` subtraction which never overflows. -/
lemma localConn_eq_rk_add_rk_sub (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.localConn X Y = M.rk X + M.rk Y - M.rk (X ∪ Y) :=
  (M.to_finRk X).localConn_eq_rk_add_rk_sub (M.to_finRk Y)

/-- The formula for local connectivity written in terms of `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma localConn_cast_int_eq (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    (M.localConn X Y : ℤ) = M.rk X + M.rk Y - M.rk (X ∪ Y) :=
  (M.to_finRk X).localConn_cast_int_eq (M.to_finRk Y)

lemma ModularPair.localConn_eq_rk_inter (h : M.ModularPair X Y) :
    M.localConn X Y = M.rk (X ∩ Y) := by
  rw [localConn, h.localEConn_eq_eRk_inter, rk]

lemma FinRk.modularPair_iff_localConn_eq_rk_inter (hX : M.FinRk X) (Y : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.localConn X Y = M.rk (X ∩ Y) := by
  rw [hX.modularPair_iff_localEConn_eq_eRk_inter Y hXE hYE, localConn, rk,
    ← Nat.cast_inj (R := ℕ∞), ENat.coe_toNat, ENat.coe_toNat]
  · rw [eRk_ne_top_iff]
    exact hX.inter_right
  rw [← WithTop.lt_top_iff_ne_top]
  exact (M.localEConn_le_eRk_left _ _).trans_lt hX.eRk_lt_top

lemma modularPair_iff_localConn_eq_rk_inter [FiniteRk M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) : M.ModularPair X Y ↔ M.localConn X Y = M.rk (X ∩ Y) :=
  (M.to_finRk X).modularPair_iff_localConn_eq_rk_inter _ hXE hYE

lemma Circuit.localEConn_subset_compl {C : Set α} (hC : M.Circuit C) (hI : I.Nonempty)
    (hIC : I ⊂ C) : M.localEConn I (C \ I) = 1 := by
  obtain ⟨e, heC, heI⟩ := exists_of_ssubset hIC
  have hi' : C \ I ⊂ C := by simpa [inter_eq_self_of_subset_right hIC.subset]
  rw [(hC.ssubset_indep hIC).basis_self.localEConn_eq (hC.ssubset_indep hi').basis_self,
    disjoint_sdiff_right.inter_eq, encard_empty, zero_add, union_diff_cancel hIC.subset, hC.restrict_eq_circuitOn, circuitOn_dual, unifOn_eRank_eq, min_eq_right
    (by simpa using hC.nonempty)]
  rfl

end localConn

section econn

/-- The `ℕ∞`-valued connectivity of a set `X` to its complement, traditionally written as `λ (X)`.
For a `ℕ`-valued version, see `Matroid.conn`. -/
noncomputable abbrev econn (M : Matroid α) (X : Set α) : ℕ∞ := M.localEConn X (M.E \ X)

lemma econn_eq_localEConn (M : Matroid α) (X : Set α) : M.econn X = M.localEConn X (M.E \ X) := rfl

@[simp] lemma econn_inter_ground (M : Matroid α) (X : Set α) :  M.econn (X ∩ M.E) = M.econn X := by
  rw [econn, localEConn_inter_ground_left, econn, diff_inter_self_eq_diff]

lemma econn_eq_localEConn' (M : Matroid α) (X : Set α) :
    M.econn X = M.localEConn (M.E ∩ X) (M.E \ X) := by
  rw [← econn_inter_ground, econn_eq_localEConn, diff_inter_self_eq_diff, inter_comm]

lemma econn_restrict_univ_eq (M : Matroid α) (X : Set α) : (M ↾ univ).econn X = M.econn X := by
   rw [econn, localEConn_restrict_univ_eq, restrict_ground_eq,
    ← localEConn_inter_ground_right, diff_eq, inter_right_comm, univ_inter, ← diff_eq]

@[simp] lemma econn_compl (M : Matroid α) (X : Set α) : M.econn (M.E \ X) = M.econn X := by
  rw [eq_comm, ← econn_inter_ground, econn, diff_inter_self_eq_diff, econn, localEConn_comm,
    inter_comm]
  simp

/-- Connectivity is self-dual. -/
@[simp] lemma econn_dual (M : Matroid α) (X : Set α) : M✶.econn X = M.econn X := by
  suffices ∀ X ⊆ M.E, M.localEConn X (M.E \ X) = M✶.localEConn X (M.E \ X) by
    rw [eq_comm, econn, econn, ← localEConn_inter_ground_left,
      ← M✶.localEConn_inter_ground_left, ← diff_inter_self_eq_diff (s := M.E) (t := X),
      this _ inter_subset_right, dual_ground, diff_inter_self_eq_diff]
  intro X hX

  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis (M.E \ X)
  obtain ⟨BX, hBX, hIBX⟩ := hI.indep.subset_basis_of_subset (show I ⊆ I ∪ J from subset_union_left)

  have hIJE : M.Spanning (I ∪ J) := by
    rw [spanning_iff_closure_eq, ← closure_closure_union_closure_eq_closure_union,
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

  rw [hBYdual.basis'.localEConn_eq_of_disjoint hBXdual.basis' disjoint_sdiff_right,
    hI.basis'.localEConn_eq_of_disjoint hJ.basis' disjoint_sdiff_right, hBX.eRank_dual_restrict,
    union_diff_distrib, diff_eq_empty.2 inter_subset_left, empty_union,
    Basis.eRank_dual_restrict (hBYb.compl_base_dual.basis_ground.basis_subset _ _)]

  · rw [union_diff_distrib, diff_eq_empty.2 (diff_subset_diff_left hX), empty_union, diff_diff,
      diff_diff, ← union_assoc, union_comm, ← diff_diff, diff_diff_cancel_left hBYb.subset_ground,
      ← diff_diff, inter_diff_distrib_left, inter_eq_self_of_subset_left hBYb.subset_ground,
      diff_self_inter]
  · rw [← union_diff_cancel hX, union_diff_distrib, union_diff_cancel hX, diff_diff, diff_diff]
    refine union_subset_union_right _ (diff_subset_diff_right ?_)
    simp only [union_subset_iff, subset_union_left, true_and]
    exact hBX.subset.trans (union_subset_union inter_subset_right inter_subset_left)

  exact union_subset (diff_subset.trans hX) (diff_subset.trans diff_subset)

lemma eRk_add_eRk_compl_eq (M : Matroid α) (X : Set α) :
    M.eRk X + M.eRk (M.E \ X) = M.eRank + M.econn X := by
  rw [econn_eq_localEConn, eRk_add_eRk_eq_eRk_union_add_localEConn, union_diff_self,
    ← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

lemma econn_le_eRk (M : Matroid α) (X : Set α) : M.econn X ≤ M.eRk X :=
  localEConn_le_eRk_left _ _ _

end econn

section conn

/-- The `ℕ`-valued connectivity of a set `X` to its complement, traditionally written `λ (X)`.
Being `ℕ`-valued, this is not well-behaved unless `M` or its dual has finite rank,
since a set with infinite connectivity to its complement has a `conn` of zero.
If neither `M` nor `M✶` is known to have finite rank, then `Matroid.econn` is better. -/
noncomputable def conn (M : Matroid α) (X : Set α) : ℕ := (M.econn X).toNat

@[simp] lemma conn_dual (M : Matroid α) (X : Set α) : M✶.conn X = M.conn X := by
  rw [conn, econn_dual, conn]

@[simp] lemma conn_inter_ground (M : Matroid α) (X : Set α) : M.conn (X ∩ M.E) = M.conn X := by
  rw [conn, econn_inter_ground, conn]

@[simp] lemma cast_conn_eq (M : Matroid α) [FiniteRk M] (X : Set α) :
    (M.conn X : ℕ∞) = M.econn X := by
  rw [conn, econn_eq_localEConn]
  exact ENat.coe_toNat ((localEConn_le_eRk_left _ _ _).trans_lt (M.to_finRk X).eRk_lt_top).ne

@[simp] lemma cast_conn_eq' (M : Matroid α) [FiniteRk M✶] : (M.conn X : ℕ∞) = M.econn X := by
  rw [← conn_dual, cast_conn_eq, econn_dual]

lemma conn_eq_localConn (M : Matroid α) (X : Set α) : M.conn X = M.localConn X (M.E \ X) := by
  rw [conn, econn_eq_localEConn, localConn]

lemma rk_add_rk_compl_eq (M : Matroid α) [FiniteRk M] (X : Set α) :
    M.rk X + M.rk (M.E \ X) = M.rank + M.conn X := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, cast_rk_eq, cast_rk_eq, Nat.cast_add,
    rank_def, cast_rk_eq, eRk_add_eRk_compl_eq, cast_conn_eq, eRank_def]

/-- A formula for the connectivity of a set in terms of the rank function.
The `ℕ` subtraction will never overflow.  -/
lemma conn_eq_rk_add_rk_sub_rank (M : Matroid α) [FiniteRk M] (X : Set α) :
    M.conn X = M.rk X + M.rk (M.E \ X) - M.rank := by
  rw [conn_eq_localConn, localConn_eq_rk_add_rk_sub, union_diff_self, rk_eq_rank subset_union_right]

/-- A version of `Matroid.conn_eq_rk_add_rk_sub_rank` with `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma int_cast_conn_eq (M : Matroid α) [FiniteRk M] (X : Set α) :
    (M.conn X : ℤ) = M.rk X + M.rk (M.E \ X) - M.rank := by
  rw [conn_eq_rk_add_rk_sub_rank, ← Nat.cast_add, rank_def]
  refine Int.ofNat_sub ?_
  convert M.rk_union_le_rk_add_rk X (M.E \ X) using 1
  rw [union_diff_self, rk_eq_rank subset_union_right, rank_def]

/-- The function `M.conn` is submodular.
This is also true for `econn` without `FiniteRk`, but the proof will be more difficult. TODO. -/
lemma conn_submod (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.conn (X ∩ Y) + M.conn (X ∪ Y) ≤ M.conn X + M.conn Y := by
  zify
  simp_rw [int_cast_conn_eq, diff_inter, ← diff_inter_diff]
  linarith [M.rk_submod X Y, M.rk_submod (M.E \ X) (M.E \ Y)]

end conn
