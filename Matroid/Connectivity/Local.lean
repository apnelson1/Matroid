import Matroid.Connectivity.Skew
import Matroid.ForMathlib.Matroid.Map

open Set Set.Notation

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J K X Y : Set α}

section localEConn

lemma Indep.encard_inter_add_erk_dual_congr (hI : M.Indep I) (hI' : M.Indep I')
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
        and_iff_left (hdj.mono_left hB.subset), closure_union_congr_left hB.closure_eq_closure,
        closure_union_closure_left_eq, union_diff_cancel hIK, hK.closure_eq_closure]
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

  have hind : ∀ Y, (M ↾ (Y ∪ J)).Indep (K \ I) := fun Y ↦ by
    rw [restrict_indep_iff, and_iff_right (hK.indep.diff I), diff_subset_iff, union_comm Y,
      ← union_assoc]
    exact hK.subset.trans subset_union_left
  have hI'b := hII'.symm ▸ hI'.basis_closure
  rw [← (hind I).contract_er_dual_eq,  ← (hind I').contract_er_dual_eq,
    restrict_contract_eq_contract_restrict _ (hb hI.basis_closure).2,
    restrict_contract_eq_contract_restrict _ (hb hI'b).2,
    union_diff_distrib, sdiff_eq_left.2 disjoint_sdiff_right,
    union_diff_distrib, sdiff_eq_left.2 (hdj.mono_left hI'b.subset), hb' hI.basis_closure, hb' hI'b]

lemma Basis'.encard_dual_congr₂ {I I' J J' X Y : Set α} (hI : M.Basis' I X) (hI' : M.Basis' I' X)
    (hJ : M.Basis' J Y) (hJ' : M.Basis' J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk := by
  rw [hI.indep.encard_inter_add_erk_dual_congr hI'.indep
      (by rw [hI.closure_eq_closure, hI'.closure_eq_closure]) hJ.indep,
    inter_comm, union_comm, hJ.indep.encard_inter_add_erk_dual_congr hJ'.indep
      (by rw [hJ.closure_eq_closure, hJ'.closure_eq_closure]) hI'.indep, inter_comm, union_comm]

/-- If `X` and `Y` are sets, then `|I ∩ J| + (M ↾ (I ∪ J))✶.erk` has the same value for
every basis `I` of `X` and `J` of `Y`. -/
lemma Basis.encard_dual_congr₂ {I I' J J' X Y : Set α} (hI : M.Basis I X) (hI' : M.Basis I' X)
    (hJ : M.Basis J Y) (hJ' : M.Basis J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk :=
  hI.basis'.encard_dual_congr₂ hI'.basis' hJ.basis' hJ'.basis'

/-- The `ℕ∞`-valued local connectivity between two sets `X` and `Y`, often written `⊓ (X,Y)`.
Defined to correctly describe the connectivity even when one or both sets has infinite rank.
For a `ℕ`-valued version, see `Matroid.localConn`. -/
noncomputable def localEConn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let I := (M.exists_basis' X).choose
  let J := (M.exists_basis' Y).choose
  (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk

lemma localEConn_comm (M : Matroid α) (X Y : Set α) : M.localEConn X Y = M.localEConn Y X := by
  simp_rw [localEConn, union_comm, inter_comm]

lemma Basis'.localEConn_eq (hI : M.Basis' I X) (hJ : M.Basis' J Y) :
    M.localEConn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk := by
  simp_rw [localEConn, hI.encard_dual_congr₂ (M.exists_basis' X).choose_spec hJ
    (M.exists_basis' Y).choose_spec]

lemma Basis.localEConn_eq (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.localEConn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis'.localEConn_eq hJ.basis'

lemma Indep.localEConn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.localEConn I J = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis_self.localEConn_eq hJ.basis_self

lemma Basis'.localEConn_eq_of_disjoint (hI : M.Basis' I X) (hJ : M.Basis' J Y)
    (hXY : Disjoint X Y) : M.localEConn X Y = (M ↾ (I ∪ J))✶.erk := by
  rw [hI.localEConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma localEConn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.Basis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.localEConn X Y = F.encard := by
  have hF' : M.Basis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.basis_inter_ground.basis_subset diff_subset
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.localEConn_eq hJ, hF'.erk_dual_restrict, diff_diff_cancel_left hFIJ,
    (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma localEConn_eq_encard_of_diff' {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFI : F ⊆ I)  (hF : M.Basis' ((I \ F) ∪ J) (X ∪ Y)) :
    M.localEConn X Y = F.encard := by
  apply localEConn_eq_encard_of_diff hXY hI hJ (hFI.trans subset_union_left)
  rwa [union_diff_distrib, (sdiff_eq_left (x := J)).2 ]
  exact (hXY.symm.mono hJ.subset (hFI.trans hI.subset))

lemma er_add_er_eq_er_union_add_localEConn (M : Matroid α) (X Y : Set α) :
    M.er X + M.er Y = M.er (X ∪ Y) + M.localEConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  obtain ⟨B, hB⟩ := M.exists_basis' (I ∪ J)
  have hB' : M.Basis' B (X ∪ Y) := by
    rw [basis'_iff_basis_closure, ← closure_closure_union_closure_eq_closure_union,
      ← hI.closure_eq_closure, ← hJ.closure_eq_closure,
      closure_closure_union_closure_eq_closure_union, ← hB.closure_eq_closure]
    exact ⟨hB.indep.basis_closure, hB.subset.trans (union_subset_union hI.subset hJ.subset)⟩
  rw [hI.localEConn_eq hJ, ← hI.encard, ← hJ.encard, ← encard_union_add_encard_inter, ← hB'.encard,
    ← (base_restrict_iff'.2 hB).encard_compl_eq, restrict_ground_eq, ← add_assoc, add_comm B.encard,
    add_assoc, add_comm B.encard, encard_diff_add_encard_of_subset hB.subset, add_comm]

lemma er_inter_le_localEConn (M : Matroid α) (X Y : Set α) : M.er (X ∩ Y) ≤ M.localEConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' (X ∩ Y)
  obtain ⟨IX, hIX⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_left)
  obtain ⟨IY, hIY⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_right)
  rw [← hI.encard, hIX.1.localEConn_eq hIY.1]
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
  refine add_le_add (encard_le_card (inter_subset_inter_left _ hII')) (Minor.erk_le ?_)
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
    erk_dual_restrict_eq_zero_iff.2 (by simpa using hI.indep), zero_add]

@[simp] lemma localEConn_empty (M : Matroid α) (X : Set α) : M.localEConn X ∅ = 0 := by
  rw [localEConn_comm, empty_localEConn]

lemma localEConn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.localEConn X Y = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.localEConn_eq hJ, inter_eq_self_of_subset_left hIJ, union_eq_self_of_subset_left hIJ,
    hJ.indep.erk_dual_restrict_eq, ← hI.encard, add_zero]

lemma localEConn_eq_zero (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.localEConn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [skew_iff_closure_skew, ← localEConn_closure_closure, ← hI.closure_eq_closure,
    ← hJ.closure_eq_closure, ← skew_iff_closure_skew, localEConn_closure_closure,
    hI.indep.localEConn_eq hJ.indep, add_eq_zero, encard_eq_zero, ← disjoint_iff_inter_eq_empty,
    erk_dual_restrict_eq_zero_iff, hI.indep.skew_iff_disjoint_union_indep hJ.indep]

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
    ← image_union, ← M.map_restrict f hf (I ∪ J), map_dual, erk_map]

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
    ← comapOn_map N hinj, map_dual, erk_map, comapOn]

@[simp] lemma localEConn_ground_eq (M : Matroid α) (X : Set α) : M.localEConn X M.E = M.er X := by
  suffices hss : ∀ Y ⊆ M.E, M.localEConn Y M.E = M.er Y by
    rw [← localEConn_inter_ground_left, ← er_inter_ground, ← hss _ inter_subset_right]
  refine fun Y hYE ↦ ?_
  obtain ⟨I, hI⟩ := M.exists_basis Y
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_superset
  rw [hI.localEConn_eq hB.basis_ground, hI.er_eq_encard, inter_eq_self_of_subset_left hIB,
    union_eq_self_of_subset_left hIB, hB.indep.restrict_eq_freeOn, erk_eq_zero_iff.2, add_zero]
  simp

@[simp] lemma ground_localEConn_eq (M : Matroid α) (X : Set α) : M.localEConn M.E X = M.er X := by
  rw [localEConn_comm, localEConn_ground_eq]

lemma localEConn_le_er_left (M : Matroid α) (X Y : Set α) : M.localEConn X Y ≤ M.er X := by
  rw [← localEConn_inter_ground_right]
  exact (M.localEConn_mono_right X inter_subset_right).trans <| by simp

lemma localEConn_le_er_right (M : Matroid α) (X Y : Set α) : M.localEConn X Y ≤ M.er Y := by
  rw [localEConn_comm]
  apply localEConn_le_er_left

lemma ModularPair.localEConn_eq_er_inter (h : M.ModularPair X Y) :
    M.localEConn X Y = M.er (X ∩ Y) := by
  obtain ⟨I, hIu, hIX, hIY, hIi⟩ := h.exists_common_basis
  rw [hIX.localEConn_eq hIY, ← hIi.encard, ← inter_inter_distrib_left, ← inter_union_distrib_left,
    inter_eq_self_of_subset_left hIu.subset, hIu.indep.restrict_eq_freeOn, freeOn_dual_eq,
    loopyOn_erk_eq, add_zero, ← inter_assoc]

lemma rFin.modularPair_iff_localEConn_eq_er_inter (hX : M.rFin X) (Y : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.localEConn X Y = M.er (X ∩ Y) := by
  refine ⟨fun h ↦ h.localEConn_eq_er_inter, fun h ↦ ?_⟩
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ := hIi.exists_basis_inter_eq_of_superset inter_subset_left
  obtain ⟨IY, hIY, hIY'⟩ := hIi.exists_basis_inter_eq_of_superset inter_subset_right

  have h_inter : Ii = IX ∩ IY
  · exact hIi.eq_of_subset_indep (hIX.indep.inter_right _)
      (subset_inter (by simp [← hIX']) (by simp [← hIY']))
      (inter_subset_inter hIX.subset hIY.subset)

  rw [hIX.localEConn_eq hIY, ← h_inter, hIi.encard, ← add_zero (a := M.er _), add_assoc, zero_add,
    WithTop.add_left_cancel_iff (hX.inter_right Y).ne, erk_eq_zero_iff, ← eq_dual_iff_dual_eq,
    loopyOn_dual_eq, dual_ground, restrict_ground_eq, restrict_eq_freeOn_iff] at h

  exact h.modularPair_of_union.of_basis_of_basis hIX hIY
/-
***** WIP

lemma localEConn_contract_skew {C Y : Set α} (hXC : M.Skew X C) :
    (M ／ C).localEConn X (Y \ C) = M.localEConn X Y := by
  wlog hYE : Y ⊆ M.E generalizing Y with h'
  · rw [← M.localEConn_inter_ground_right, ← h' inter_subset_right, ← diff_inter_diff_right,
      ← contract_ground, localEConn_inter_ground_right]
  wlog hXdj : Disjoint X C generalizing X with h'
  · rw [← localEConn_inter_ground_left, contract_ground, ← inter_diff_assoc,
      ← diff_inter_diff_right, ← contract_ground, localEConn_inter_ground_left,
      h' (hXC.mono_left diff_subset) disjoint_sdiff_left, ← localEConn_closure_left,
      ← localEConn_closure_left (X := X), ← diff_self_inter,
      closure_diff_eq_closure_of_subset_loops]
    exact Skew.inter_subset_loops hXC
  have hXEC : X ⊆ (M ／ C).E := subset_diff.2 ⟨hXC.subset_ground_left, hXdj⟩
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := (M ／ C).exists_basis (Y \ C) (diff_subset_diff_left hYE)
  obtain ⟨K, hK⟩ := M.exists_basis C
  have hI' : (M ／ C).Basis I X
  · replace hI := hI.basis_restrict_of_subset rfl.subset
    rw [← hXC.symm.contract_restrict_eq, basis_restrict_iff] at hI
    exact hI.1

  -- have hJss := subset_diff.1 hJ.subset
  have hJi := hK.contract_indep_iff.1 hJ.indep
  have hJY : J ⊆ Y := hJ.subset.trans diff_subset

  have hCIJdj : Disjoint C (I ∪ J) :=
    disjoint_union_right.2 ⟨hXdj.symm.mono_right hI.subset, hJi.2⟩

  obtain ⟨J', hJ'Y, hJJ'⟩ := (hJi.1.subset subset_union_left).subset_basis_of_subset hJY


  -- have hK : M.Basis (J ∪ K) Y
  -- · refine Indep.basis_of_subset_of_subset_closure ?_ (union_subset hJss.1 ?_) ?_

  have foo : I ∩ J = I ∩ J'
  ·

  rw [hI'.localEConn_eq hJ, contract_restrict_eq_restrict_contract _ _ _ hCIJdj,
    contract_dual_eq_dual_delete, hI.localEConn_eq hJ'Y, erk_def]
  simp only [delete_ground, dual_ground, restrict_ground_eq, union_diff_right, delete_er_eq',
    sdiff_idem, hCIJdj.symm.sdiff_eq_left]



  -- obtain ⟨J, hJ⟩ := ()
-/

lemma Hyperplane.localEConn_add_one_eq {H X : Set α} (hH : M.Hyperplane H) (hXH : ¬ (X ⊆ H))
    (hXE : X ⊆ M.E := by aesop_mat) : M.localEConn H X + 1 = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis H
  sorry


end localEConn

section localConn

/-- The `ℕ`-valued local connectivity between sets `X` and `Y`, often denoted `⊓ (X, Y)`.
Equal to `M.r X + M.r Y - M.r (X ∪ Y)` if both sets have finite rank.
This is only mathematically meaningful if at least one of `X` and `Y` is known to have finite rank;
otherwise `Matroid.localEConn` is preferable. -/
noncomputable def localConn (M : Matroid α) (X Y : Set α) : ℕ := (M.localEConn X Y).toNat

lemma localConn_comm (M : Matroid α) (X Y : Set α) : M.localConn X Y = M.localConn Y X := by
  rw [localConn, localEConn_comm, localConn]

lemma rFin.cast_localConn_right_eq (hX : M.rFin X) (Y : Set α) :
    (M.localConn X Y : ℕ∞) = M.localEConn X Y :=
  ENat.coe_toNat fun htop ↦ hX.not_le <| htop.symm.le.trans <| M.localEConn_le_er_left X Y

lemma rFin.cast_localConn_left_eq (hY : M.rFin Y) : (M.localConn X Y : ℕ∞) = M.localEConn X Y := by
  rw [localConn_comm, hY.cast_localConn_right_eq, localEConn_comm]

lemma rFin.r_add_r_eq_r_union_add_localConn (hX : M.rFin X) (hY : M.rFin Y) :
    M.r X + M.r Y = M.r (X ∪ Y) + M.localConn X Y := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, Nat.cast_add, hX.cast_localConn_right_eq,
    hX.cast_r_eq, hY.cast_r_eq, (hX.union hY).cast_r_eq, er_add_er_eq_er_union_add_localEConn]

lemma r_add_r_eq_r_union_add_localConn (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.r X + M.r Y = M.r (X ∪ Y) + M.localConn X Y :=
  (M.to_rFin X).r_add_r_eq_r_union_add_localConn (M.to_rFin Y)

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
lemma rFin.localConn_eq_r_add_r_sub (hX : M.rFin X) (hY : M.rFin Y) :
    M.localConn X Y = M.r X + M.r Y - M.r (X ∪ Y) := by
  rw [hX.r_add_r_eq_r_union_add_localConn hY, add_comm]
  exact Nat.eq_sub_of_add_eq rfl

/-- The formula for local connectivity of two finite-rank sets written with `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma rFin.localConn_cast_int_eq (hX : M.rFin X) (hY : M.rFin Y) :
    (M.localConn X Y : ℤ) = M.r X + M.r Y - M.r (X ∪ Y) := by
  rw [hX.localConn_eq_r_add_r_sub hY, ← Nat.cast_add]
  exact Int.natCast_sub (r_union_le_r_add_r _ _ _)

/-- The formula for local connectivity in terms of the rank function.
This uses `ℕ` subtraction which never overflows. -/
lemma localConn_eq_r_add_r_sub (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.localConn X Y = M.r X + M.r Y - M.r (X ∪ Y) :=
  (M.to_rFin X).localConn_eq_r_add_r_sub (M.to_rFin Y)

/-- The formula for local connectivity written in terms of `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma localConn_cast_int_eq (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    (M.localConn X Y : ℤ) = M.r X + M.r Y - M.r (X ∪ Y) :=
  (M.to_rFin X).localConn_cast_int_eq (M.to_rFin Y)

lemma ModularPair.localConn_eq_r_inter (h : M.ModularPair X Y) :
    M.localConn X Y = M.r (X ∩ Y) := by
  rw [localConn, h.localEConn_eq_er_inter, r]

lemma rFin.modularPair_iff_localConn_eq_r_inter (hX : M.rFin X) (Y : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.localConn X Y = M.r (X ∩ Y) := by
  rw [hX.modularPair_iff_localEConn_eq_er_inter Y hXE hYE, localConn, r,
    ← Nat.cast_inj (R := ℕ∞), ENat.coe_toNat, ENat.coe_toNat]
  · rw [er_ne_top_iff]
    exact hX.inter_right Y
  rw [← WithTop.lt_top_iff_ne_top]
  exact (M.localEConn_le_er_left _ _).trans_lt hX

lemma modularPair_iff_localConn_eq_r_inter [FiniteRk M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) : M.ModularPair X Y ↔ M.localConn X Y = M.r (X ∩ Y) :=
  (M.to_rFin X).modularPair_iff_localConn_eq_r_inter _ hXE hYE


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
    hI.basis'.localEConn_eq_of_disjoint hJ.basis' disjoint_sdiff_right, hBX.erk_dual_restrict,
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

lemma er_add_er_compl_eq (M : Matroid α) (X : Set α) :
    M.er X + M.er (M.E \ X) = M.erk + M.econn X := by
  rw [econn_eq_localEConn, er_add_er_eq_er_union_add_localEConn, union_diff_self,
    ← er_inter_ground, inter_eq_self_of_subset_right subset_union_right, erk_def]

lemma econn_le_er (M : Matroid α) (X : Set α) : M.econn X ≤ M.er X :=
  localEConn_le_er_left _ _ _

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
  exact ENat.coe_toNat ((localEConn_le_er_left _ _ _).trans_lt (M.to_rFin X)).ne

@[simp] lemma cast_conn_eq' (M : Matroid α) [FiniteRk M✶] : (M.conn X : ℕ∞) = M.econn X := by
  rw [← conn_dual, cast_conn_eq, econn_dual]

lemma conn_eq_localConn (M : Matroid α) (X : Set α) : M.conn X = M.localConn X (M.E \ X) := by
  rw [conn, econn_eq_localEConn, localConn]

lemma r_add_r_compl_eq (M : Matroid α) [FiniteRk M] (X : Set α) :
    M.r X + M.r (M.E \ X) = M.rk + M.conn X := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, cast_r_eq, cast_r_eq, Nat.cast_add,
    rk_def, cast_r_eq, er_add_er_compl_eq, cast_conn_eq, erk_def]

/-- A formula for the connectivity of a set in terms of the rank function.
The `ℕ` subtraction will never overflow.  -/
lemma conn_eq_r_add_r_sub_rk (M : Matroid α) [FiniteRk M] (X : Set α) :
    M.conn X = M.r X + M.r (M.E \ X) - M.rk := by
  rw [conn_eq_localConn, localConn_eq_r_add_r_sub, union_diff_self, r_eq_rk subset_union_right]

/-- A version of `Matroid.conn_eq_r_add_r_sub_rk` with `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma int_cast_conn_eq (M : Matroid α) [FiniteRk M] (X : Set α) :
    (M.conn X : ℤ) = M.r X + M.r (M.E \ X) - M.rk := by
  rw [conn_eq_r_add_r_sub_rk, ← Nat.cast_add, rk_def]
  refine Int.ofNat_sub ?_
  convert M.r_union_le_r_add_r X (M.E \ X) using 1
  rw [union_diff_self, r_eq_rk subset_union_right, rk_def]

/-- The function `M.conn` is submodular.
This is also true for `econn` without `FiniteRk`, but the proof will be more difficult. TODO. -/
lemma conn_submod (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.conn (X ∩ Y) + M.conn (X ∪ Y) ≤ M.conn X + M.conn Y := by
  zify
  simp_rw [int_cast_conn_eq, diff_inter, ← diff_inter_diff]
  linarith [M.r_submod X Y, M.r_submod (M.E \ X) (M.E \ Y)]

end conn
