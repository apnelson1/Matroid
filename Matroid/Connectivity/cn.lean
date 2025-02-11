import Matroid.Connectivity.Skew
import Matroid.ForMathlib.Matroid.Map
import Matroid.ForMathlib.ENat
import Matroid.Uniform
import Mathlib.Tactic.TautoSet

open Set Set.Notation

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X Y : Set α}

section localEConn

lemma Indep.encard_inter_add_nullity_eq (hI : M.Indep I) (hJ : M.Indep J) (hK : M.Basis K (I ∪ J))
    (hIK : I ⊆ K) (hI' : M.Indep I') (hcl : M.closure I = M.closure I') :
    (I' ∩ J).encard + M.nullity (I' ∪ J) = (J \ (K \ I)).encard := by
  have hsk := (hK.indep.subset_skew_diff hIK)
  rw [skew_iff_closure_skew_left, hcl, ← skew_iff_closure_skew_left] at hsk
  have' hdj := hsk.disjoint_of_indep_subset_right (hK.indep.diff _) Subset.rfl

  set J₀ := (K \ I) with hJ₀
  set J₁ := J \ (K \ I) with hJ₁
  have hJ₀i : M.Indep J₀ := hK.indep.diff I
  have hss : J₀ ⊆ I' ∪ J := (diff_subset_iff.2 hK.subset).trans subset_union_right

  have hc1 : (M ／ J₀).Basis I' (I' ∪ J₁) := by
    refine Indep.basis_of_subset_of_subset_closure ?_ ?_ ?_
    · rw [(hK.indep.diff _).contract_indep_iff]
      refine ⟨hdj, hsk.union_indep_of_indep_subsets hI' rfl.subset (hK.indep.diff _) Subset.rfl⟩
    · exact subset_union_left
    · rw [contract_closure_eq, subset_diff, disjoint_union_left, and_iff_left disjoint_sdiff_left,
        and_iff_left hdj, ← closure_union_congr_left hcl, union_diff_cancel hIK,
        hK.closure_eq_closure, closure_union_congr_left hcl]
      exact subset_closure_of_subset _ (union_subset_union_right _ diff_subset)

  rw [← hJ₀i.nullity_contract_of_superset hss, union_diff_distrib, sdiff_eq_left.2 hdj,
    hc1.nullity_eq, union_diff_left,
    ← encard_union_eq (disjoint_sdiff_right.mono_left inter_subset_left),
    ← inter_union_diff J (K \ I), ← hJ₁, inter_union_distrib_left, union_assoc,
    inter_comm _ J₁, inter_union_diff, ← hJ₀, inter_comm J, ← inter_assoc,
    hdj.inter_eq, empty_inter, empty_union]

lemma Basis'.encard_dual_congr (hI : M.Basis' I X) (hI' : M.Basis' I' X) (hJ : M.Basis' J Y)
    (hJ' : M.Basis' J' Y) :
    (I ∩ J).encard + M.nullity (I ∪ J) = (I' ∩ J').encard + M.nullity (I' ∪ J') := by
  wlog hJJ' : J = J' generalizing I I' J J' X Y with h
  · rw [h hI hI' hJ hJ rfl, inter_comm, union_comm, h hJ hJ' hI' hI' rfl, inter_comm, union_comm]
  subst hJJ'
  obtain ⟨K, hK, hIK⟩ := hI.indep.subset_basis_of_subset (show I ⊆ I ∪ J from subset_union_left)
    (union_subset hI.indep.subset_ground hJ.indep.subset_ground)
  have hcl : M.closure I = M.closure I' := by rw [hI.closure_eq_closure, hI'.closure_eq_closure]
  rw [hI.indep.encard_inter_add_nullity_eq hJ.indep hK hIK hI'.indep hcl,
    hI.indep.encard_inter_add_nullity_eq hJ.indep hK hIK hI.indep rfl]

/-- If `X` and `Y` are sets, then `|I ∩ J| + M.nullity (I ∪ J)` has the same value for
every basis `I` of `X` and `J` of `Y`. -/
lemma Basis.encard_dual_congr₂ (hI : M.Basis I X) (hI' : M.Basis I' X)
    (hJ : M.Basis J Y) (hJ' : M.Basis J' Y) :
    (I ∩ J).encard + M.nullity (I ∪ J) = (I' ∩ J').encard + M.nullity (I' ∪ J') :=
  hI.basis'.encard_dual_congr hI'.basis' hJ.basis' hJ'.basis'

/-- The `ℕ∞`-valued local connectivity between two sets `X` and `Y`, often written `⊓ (X,Y)`.
Defined to correctly describe the connectivity even when one or both sets has infinite rank.
For a `ℕ`-valued version, see `Matroid.localConn`. -/
noncomputable def localEConn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let I := (M.exists_basis' X).choose
  let J := (M.exists_basis' Y).choose
  (I ∩ J).encard + M.nullity (I ∪ J)

lemma localEConn_comm (M : Matroid α) (X Y : Set α) : M.localEConn X Y = M.localEConn Y X := by
  simp_rw [localEConn, union_comm, inter_comm]

lemma Basis'.localEConn_eq (hI : M.Basis' I X) (hJ : M.Basis' J Y) :
    M.localEConn X Y = (I ∩ J).encard + M.nullity (I ∪ J) := by
  simp_rw [localEConn, hI.encard_dual_congr (M.exists_basis' X).choose_spec hJ
    (M.exists_basis' Y).choose_spec]

lemma Basis.localEConn_eq (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.localEConn X Y = (I ∩ J).encard + M.nullity (I ∪ J) :=
  hI.basis'.localEConn_eq hJ.basis'

lemma Indep.localEConn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.localEConn I J = (I ∩ J).encard + M.nullity (I ∪ J) :=
  hI.basis_self.localEConn_eq hJ.basis_self

lemma Basis'.localEConn_eq_of_disjoint (hI : M.Basis' I X) (hJ : M.Basis' J Y)
    (hXY : Disjoint X Y) : M.localEConn X Y = M.nullity (I ∪ J) := by
  rw [hI.localEConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma Basis.localEConn_eq_of_disjoint (hI : M.Basis I X) (hJ : M.Basis J Y)
    (hXY : Disjoint X Y) : M.localEConn X Y = M.nullity (I ∪ J) := by
  rw [hI.localEConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma localEConn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.Basis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.localEConn X Y = F.encard := by
  have hF' : M.Basis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.basis_inter_ground.basis_subset diff_subset
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.localEConn_eq hJ, hF'.nullity_eq, diff_diff_cancel_left hFIJ,
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
    ← hB'.encard_eq_eRk, hB.nullity_eq, ← add_assoc, add_right_comm, add_comm B.encard,
    encard_diff_add_encard_of_subset hB.subset]

lemma eRk_inter_le_localEConn (M : Matroid α) (X Y : Set α) : M.eRk (X ∩ Y) ≤ M.localEConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' (X ∩ Y)
  obtain ⟨IX, hIX⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_left)
  obtain ⟨IY, hIY⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans inter_subset_right)
  rw [← hI.encard_eq_eRk, hIX.1.localEConn_eq hIY.1]
  exact (encard_le_encard (subset_inter hIX.2 hIY.2)).trans le_self_add

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
  refine add_le_add (encard_le_encard (inter_subset_inter_left _ hII')) (Minor.eRank_le ?_)
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
  rw [(M.empty_indep.basis_self.basis').localEConn_eq hI]
  simp [hI.indep]

@[simp] lemma localEConn_empty (M : Matroid α) (X : Set α) : M.localEConn X ∅ = 0 := by
  rw [localEConn_comm, empty_localEConn]

lemma localEConn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.localEConn X Y = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.localEConn_eq hJ, inter_eq_self_of_subset_left hIJ, union_eq_self_of_subset_left hIJ,
    hJ.indep.nullity_eq, ← hI.encard_eq_eRk, add_zero]

lemma localEConn_eq_zero (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.localEConn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [skew_iff_closure_skew, ← localEConn_closure_closure, ← hI.closure_eq_closure,
    ← hJ.closure_eq_closure, ← skew_iff_closure_skew, localEConn_closure_closure,
    hI.indep.localEConn_eq hJ.indep]
  simp [hI.indep.skew_iff_disjoint_union_indep hJ.indep, disjoint_iff_inter_eq_empty]

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
  rw [hI.localEConn_eq hJ, hI'.localEConn_eq hJ',
    nullity_restrict_of_subset _ (union_subset hI'R hJ'R)]

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
    (hf.mono (inter_subset_left.trans hI.indep.subset_ground)).encard_image, ← image_union,
    nullity_eq_eRank_restrict_dual, ← M.map_restrict f hf (I ∪ J), map_dual, eRank_map,
    nullity_eq_eRank_restrict_dual]

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
    nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual,
    ← comapOn_map N hinj, map_dual, eRank_map, comapOn]

@[simp] lemma localEConn_ground_eq (M : Matroid α) (X : Set α) : M.localEConn X M.E = M.eRk X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← localEConn_inter_ground_left, aux _ inter_subset_right, eRk_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_superset
  rw [hI.localEConn_eq hB.basis_ground, hI.eRk_eq_encard, inter_eq_self_of_subset_left hIB,
    union_eq_self_of_subset_left hIB, hB.indep.nullity_eq, add_zero]

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
    ← inter_union_distrib_left, inter_eq_self_of_subset_left hIu.subset, hIu.indep.nullity_eq,
    add_zero, inter_assoc]


/-- Contracting a subset of `Y` that is skew to `X` doesn't change the local connectivity
between `X` and `Y`. -/
lemma localEConn_contract_right_skew_left' {C Y : Set α} (hXC : M.Skew X C) (hCY : C ⊆ Y) :
    (M ／ C).localEConn X (Y \ C) = M.localEConn X Y := by
  wlog hYE : Y ⊆ M.E generalizing Y with aux
  · rw [← localEConn_inter_ground_right, contract_ground, diff_inter_diff_right,
      aux (subset_inter hCY hXC.subset_ground_right) inter_subset_right,
      localEConn_inter_ground_right]
  wlog hC : M.Indep C generalizing C with aux
  · obtain ⟨I, hI⟩ := M.exists_basis C
    have hcl : (M ／ I).closure (Y \ C) = (M ／ I).closure (Y \ I) := by
      simp [closure_union_congr_right hI.closure_eq_closure]
    have ss : C \ I ⊆ (M ／ I).closure ∅ := by
      simp only [contract_closure_eq, empty_union, hI.closure_eq_closure]
      exact diff_subset_diff_left (subset_closure _ _)
    rw [hI.contract_eq_contract_delete, localEConn_delete_eq,
      ← localEConn_closure_closure, closure_diff_eq_closure_of_subset_loops _ _ ss,
      sdiff_eq_left.2 (disjoint_sdiff_left.mono_right diff_subset), hcl,
      localEConn_closure_closure, ← aux (hXC.mono_right hI.subset) (hI.subset.trans hCY) hI.indep]

  obtain ⟨J, hJ, hCJ⟩ := hC.subset_basis_of_subset hCY
  have hdj := hXC.disjoint_of_indep_right hC
  have hbY := hC.contract_basis hJ <| hJ.indep.subset <| union_subset hCJ rfl.subset
  obtain ⟨K, hK⟩ := M.exists_basis X

  have hbX : (M ／ C).Basis K X :=
    hC.contract_basis_of_disjoint hK hdj.symm <|
    hXC.symm.union_indep_of_indep_subsets hC rfl.subset hK.indep hK.subset
  have hrw : K ∪ J \ C = (K ∪ J) \ C := by
    rw [union_diff_distrib, (hdj.mono_left hK.subset).sdiff_eq_left]
  rw [hK.localEConn_eq hJ, hbX.localEConn_eq hbY, hrw,
    hC.nullity_contract_of_superset (hCJ.trans subset_union_right),
    inter_diff_distrib_left, (hdj.mono_left hK.subset).inter_eq, diff_empty]

lemma localEConn_insert_left_eq_add_one {e : α} (heX : e ∉ M.closure X)
    (heXY : e ∈ M.closure (X ∪ Y)) : M.localEConn (insert e X) Y = M.localEConn X Y + 1 := by
  have heE : e ∈ M.E := mem_ground_of_mem_closure heXY
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← localEConn_inter_ground_left, insert_inter_of_mem heE,
      aux (by simpa) _ inter_subset_right, localEConn_inter_ground_left]
    rwa [← closure_inter_ground, union_inter_distrib_right, inter_assoc, inter_self,
      ← union_inter_distrib_right, closure_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  have hIe : M.Basis (insert e I) (insert e X) := by
    refine hI.insert_basis_insert ?_
    rw [hI.indep.insert_indep_iff, hI.closure_eq_closure]
    exact .inl ⟨heE, heX⟩

  rw [hI.basis'.localEConn_eq hJ, hIe.basis'.localEConn_eq hJ, insert_union]
  have heI : e ∉ I := not_mem_subset (hI.subset.trans (M.subset_closure X)) heX
  by_cases heJ : e ∈ J
  · rw [insert_inter_of_mem heJ, insert_eq_of_mem (mem_union_right _ heJ),
      encard_insert_of_not_mem (by simp [heI]), add_right_comm]

  rw [insert_inter_of_not_mem heJ, nullity_insert_eq_add_one
    (by rwa [closure_union_congr_left hI.closure_eq_closure,
      closure_union_congr_right hJ.closure_eq_closure]) (by simp [heI, heJ]), add_assoc]


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
    zero_add, WithTop.add_left_cancel_iff hX.inter_right.eRk_ne_top, nullity_eq_zero] at h

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

  rw [hIX.eRk_eq_encard, hIX.localEConn_eq hIY, hIY.eRelRk_eq_encard_diff_of_subset_basis hK' hIYK,
    hK.nullity_eq, union_diff_distrib, diff_eq_empty.2 hIYK, union_empty, add_assoc,
    ← encard_union_eq (disjoint_sdiff_left.mono_right diff_subset),
    diff_union_diff_cancel_of_inter_subset_of_subset_union _ hK.subset, add_comm,
    encard_diff_add_encard_inter]
  exact (inter_subset_right.trans hIYK)

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

lemma rk_add_rk_eq_rk_union_add_localConn (M : Matroid α) [RankFinite M] (X Y : Set α) :
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
lemma localConn_eq_rk_add_rk_sub (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.localConn X Y = M.rk X + M.rk Y - M.rk (X ∪ Y) :=
  (M.to_finRk X).localConn_eq_rk_add_rk_sub (M.to_finRk Y)

/-- The formula for local connectivity written in terms of `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma localConn_cast_int_eq (M : Matroid α) [RankFinite M] (X Y : Set α) :
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

lemma modularPair_iff_localConn_eq_rk_inter [RankFinite M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) : M.ModularPair X Y ↔ M.localConn X Y = M.rk (X ∩ Y) :=
  (M.to_finRk X).modularPair_iff_localConn_eq_rk_inter _ hXE hYE

lemma Circuit.localEConn_subset_compl {C : Set α} (hC : M.Circuit C) (hI : I.Nonempty)
    (hIC : I ⊂ C) : M.localEConn I (C \ I) = 1 := by
  obtain ⟨e, heC, heI⟩ := exists_of_ssubset hIC
  have hi' : C \ I ⊂ C := by simpa [inter_eq_self_of_subset_right hIC.subset]
  rw [(hC.ssubset_indep hIC).basis_self.localEConn_eq (hC.ssubset_indep hi').basis_self,
    disjoint_sdiff_right.inter_eq, encard_empty, zero_add, union_diff_cancel hIC.subset,
    hC.nullity_eq]

end localConn

section econn

/-- The `ℕ∞`-valued connectivity of a set `X` to its complement, traditionally written as `λ (X)`.
For a `ℕ`-valued version, see `Matroid.conn`. -/
noncomputable abbrev econn (M : Matroid α) (X : Set α) : ℕ∞ := M.localEConn X (M.E \ X)

lemma econn_eq_localEConn (M : Matroid α) (X : Set α) : M.econn X = M.localEConn X (M.E \ X) := rfl

@[simp] lemma econn_inter_ground (M : Matroid α) (X : Set α) :  M.econn (X ∩ M.E) = M.econn X := by
  rw [econn, localEConn_inter_ground_left, econn, diff_inter_self_eq_diff]

lemma Basis'.econn_eq (hIX : M.Basis' I X) (hJX : M.Basis' J (M.E \ X)) :
    M.econn X = M.nullity (I ∪ J) := by
  rw [econn_eq_localEConn, hIX.localEConn_eq_of_disjoint hJX disjoint_sdiff_right]

lemma Basis.econn_eq (hIX : M.Basis I X) (hJX : M.Basis J (M.E \ X)) :
    M.econn X = M.nullity (I ∪ J) :=
  hIX.basis'.econn_eq hJX.basis'

lemma econn_eq_localEConn' (M : Matroid α) (X : Set α) :
    M.econn X = M.localEConn (M.E ∩ X) (M.E \ X) := by
  rw [← econn_inter_ground, econn_eq_localEConn, diff_inter_self_eq_diff, inter_comm]

lemma econn_restrict_univ_eq (M : Matroid α) (X : Set α) : (M ↾ univ).econn X = M.econn X := by
   rw [econn, localEConn_restrict_univ_eq, restrict_ground_eq,
    ← localEConn_inter_ground_right, diff_eq, inter_right_comm, univ_inter, ← diff_eq]

lemma econn_corestrict_univ_eq (M : Matroid α) (X : Set α) : (M✶ ↾ univ)✶.econn X = M.econn X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis (M.E \ X)

  have hJ' : (M✶ ↾ univ)✶.Basis (J ∪ (Xᶜ \ M.E)) ((M✶ ↾ univ)✶.E \ X) := by
    rwa [dual_ground, restrict_ground_eq, ← compl_eq_univ_diff, corestrict_univ_basis_iff,
      union_subset_iff, and_iff_left subset_union_right, and_iff_left diff_subset,
      and_iff_left <| hJ.subset.trans <| diff_subset_compl .., ← diff_eq_compl_inter,
      union_inter_distrib_right, disjoint_sdiff_left.inter_eq, union_empty,
      inter_eq_self_of_subset_left hJ.indep.subset_ground]

  rw [hI.corestrict_univ_basis.basis'.econn_eq hJ'.basis', hI.econn_eq hJ.basis',
    nullity_corestrict_univ_eq_nullity_inter, union_right_comm, union_assoc, union_assoc,
    ← union_diff_distrib, ← union_assoc, union_inter_distrib_right, disjoint_sdiff_left.inter_eq,
    union_empty,
    inter_eq_self_of_subset_left (union_subset hI.indep.subset_ground hJ.indep.subset_ground)]

@[simp] lemma econn_compl (M : Matroid α) (X : Set α) : M.econn (M.E \ X) = M.econn X := by
  rw [eq_comm, ← econn_inter_ground, econn, diff_inter_self_eq_diff, econn, localEConn_comm,
    inter_comm]
  simp

/-- Connectivity is self-dual. -/
@[simp] lemma econn_dual (M : Matroid α) (X : Set α) : M✶.econn X = M.econn X := by
  wlog h : OnUniv M with aux
  · rw [← econn_corestrict_univ_eq, dual_dual, eq_comm, ← econn_restrict_univ_eq, aux _ _ ⟨rfl⟩]
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis (M.E \ X)
  obtain ⟨B, hB, rfl⟩ := hI.exists_basis_inter_eq_of_superset (show X ⊆ X ∪ J from subset_union_left)
  have hsp : M.Spanning (X ∪ J) := by
    simp [spanning_iff_closure_eq, closure_union_congr_right hJ.closure_eq_closure]
  have hBdual := (hB.base_of_spanning hsp).compl_inter_basis_of_inter_basis hI
  rw [diff_inter_diff, union_comm, ← diff_diff] at hBdual
  obtain ⟨B', hB', rfl⟩ := hJ.exists_base
  have hB'dual : M✶.Basis (B'ᶜ ∩ X) X := by
    simpa [← compl_eq_univ_diff] using hB'.compl_inter_basis_of_inter_basis hJ
  have hBss := hB.subset
  have hgd := OnUniv.ground_diff_eq M X
  rw [ hB'dual.econn_eq hBdual, hI.econn_eq hJ, OnUniv.ground_diff_eq,
    (hB.basis_subset (by tauto_set) (by tauto_set)).nullity_eq,
    (hB'.compl_base_dual.basis_ground.basis_subset (by tauto_set) (by simp)).nullity_eq,
    OnUniv.ground_diff_eq,  union_diff_distrib]
  exact congr_arg _ (by tauto_set)

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

@[simp] lemma cast_conn_eq (M : Matroid α) [RankFinite M] (X : Set α) :
    (M.conn X : ℕ∞) = M.econn X := by
  rw [conn, econn_eq_localEConn]
  exact ENat.coe_toNat ((localEConn_le_eRk_left _ _ _).trans_lt (M.to_finRk X).eRk_lt_top).ne

@[simp] lemma cast_conn_eq' (M : Matroid α) [RankFinite M✶] : (M.conn X : ℕ∞) = M.econn X := by
  rw [← conn_dual, cast_conn_eq, econn_dual]

lemma conn_eq_localConn (M : Matroid α) (X : Set α) : M.conn X = M.localConn X (M.E \ X) := by
  rw [conn, econn_eq_localEConn, localConn]

lemma rk_add_rk_compl_eq (M : Matroid α) [RankFinite M] (X : Set α) :
    M.rk X + M.rk (M.E \ X) = M.rank + M.conn X := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, cast_rk_eq, cast_rk_eq, Nat.cast_add,
    rank_def, cast_rk_eq, eRk_add_eRk_compl_eq, cast_conn_eq, eRank_def]

/-- A formula for the connectivity of a set in terms of the rank function.
The `ℕ` subtraction will never overflow.  -/
lemma conn_eq_rk_add_rk_sub_rank (M : Matroid α) [RankFinite M] (X : Set α) :
    M.conn X = M.rk X + M.rk (M.E \ X) - M.rank := by
  rw [conn_eq_localConn, localConn_eq_rk_add_rk_sub, union_diff_self, rk_eq_rank subset_union_right]

/-- A version of `Matroid.conn_eq_rk_add_rk_sub_rank` with `Int` subtraction,
for use with `ring, linarith`, etc. -/
lemma intCast_conn_eq (M : Matroid α) [RankFinite M] (X : Set α) :
    (M.conn X : ℤ) = M.rk X + M.rk (M.E \ X) - M.rank := by
  rw [conn_eq_rk_add_rk_sub_rank, ← Nat.cast_add, rank_def]
  refine Int.ofNat_sub ?_
  convert M.rk_union_le_rk_add_rk X (M.E \ X) using 1
  rw [union_diff_self, rk_eq_rank subset_union_right, rank_def]

lemma conn_inter_add_conn_union_union_le (M : Matroid α) [RankFinite M] {A : Set α}
    (hAX : Disjoint A X) (hAY : Disjoint A Y) :
    M.conn (X ∩ Y) + M.conn (X ∪ Y ∪ A) ≤ M.rk A + (M ＼ A).conn X + (M ／ A).conn Y := by
  zify
  simp only [intCast_conn_eq, delete_ground, contract_rk_cast_int_eq, contract_ground,
    contract_rank_cast_int_eq]
  rw [delete_rk_eq_of_disjoint _ hAX.symm, delete_rk_eq_of_disjoint _
    (disjoint_sdiff_left.mono_left diff_subset), diff_diff, diff_diff_comm, diff_union_self,
    rk_compl_union_of_disjoint _ hAY.symm, union_comm A]
  have hle := delete_rank_le M A
  have hsm := M.rk_submod X (Y ∪ A)
  rw [inter_union_distrib_left, hAX.symm.inter_eq, union_empty, ← union_assoc] at hsm
  have hsm' := M.rk_submod_compl (X ∪ A) Y
  rw [union_right_comm, union_inter_distrib_right, hAY.inter_eq, union_empty] at hsm'
  linarith

/-- The function `M.conn` is submodular.
This is also true for `econn` without `RankFinite`, but the proof will be more difficult. TODO. -/
lemma conn_submod (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.conn (X ∩ Y) + M.conn (X ∪ Y) ≤ M.conn X + M.conn Y := by
  simpa using M.conn_inter_add_conn_union_union_le (disjoint_empty X).symm (disjoint_empty Y).symm

end conn
