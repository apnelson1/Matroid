import Matroid.Rank.Skew
import Matroid.ForMathlib.Matroid.Map
import Matroid.ForMathlib.ENat
import Matroid.Uniform
import Mathlib.Tactic.TautoSet
import Matroid.BasisDuo

open Set Set.Notation Function

set_option linter.style.longLine false

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X Y : Set α}

section eLocalConn

/- If `X` and `Y` are sets, then `|I ∩ J| + M.nullity (I ∪ J)` has the same value for
every isBasis `I` of `X` and `J` of `Y`. --/
lemma IsBasis'.encard_add_nullity_congr (hI : M.IsBasis' I X) (hI' : M.IsBasis' I' X)
    (hJ : M.IsBasis' J Y) (hJ' : M.IsBasis' J' Y) :
    (I ∩ J).encard + M.nullity (I ∪ J) = (I' ∩ J').encard + M.nullity (I' ∪ J') := by
  rw [add_comm, ← nullity_project_add_nullity_eq, add_comm (encard _),
    ← nullity_project_add_nullity_eq, hJ.indep.nullity_eq, hJ'.indep.nullity_eq,
    ← hJ.project_eq_project, ← hJ'.project_eq_project, hI.nullity_project hI']

/-- The `ℕ∞`-valued local connectivity between two sets `X` and `Y`, often written `⊓ (X,Y)`.
Defined to correctly describe the connectivity even when one or both sets has infinite rank.
For a `ℕ`-valued version, see `Matroid.localConn`. -/
noncomputable def eLocalConn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let I := (M.exists_isBasis' X).choose
  let J := (M.exists_isBasis' Y).choose
  (I ∩ J).encard + M.nullity (I ∪ J)

lemma eLocalConn_comm (M : Matroid α) (X Y : Set α) : M.eLocalConn X Y = M.eLocalConn Y X := by
  simp_rw [eLocalConn, union_comm, inter_comm]

lemma IsBasis'.eLocalConn_eq (hI : M.IsBasis' I X) (hJ : M.IsBasis' J Y) :
    M.eLocalConn X Y = (I ∩ J).encard + M.nullity (I ∪ J) := by
  rw [eLocalConn]
  generalize_proofs h1 h2
  exact IsBasis'.encard_add_nullity_congr h1.choose_spec hI h2.choose_spec hJ

lemma IsBasis.eLocalConn_eq (hI : M.IsBasis I X) (hJ : M.IsBasis J Y) :
    M.eLocalConn X Y = (I ∩ J).encard + M.nullity (I ∪ J) :=
  hI.isBasis'.eLocalConn_eq hJ.isBasis'

lemma IsBasis'.eLocalConn_eq_nullity_project_right (hI : M.IsBasis' I X) (Y : Set α) :
    M.eLocalConn X Y = (M.project Y).nullity I := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [hI.eLocalConn_eq hJ, add_comm, ← nullity_project_add_nullity_eq,
    ← hJ.project_eq_project, hJ.indep.nullity_eq, add_zero]

lemma IsBasis.eLocalConn_eq_nullity_project_right (hI : M.IsBasis I X) (Y : Set α) :
    M.eLocalConn X Y = (M.project Y).nullity I :=
  hI.isBasis'.eLocalConn_eq_nullity_project_right Y

lemma IsBasis'.eLocalConn_eq_nullity_project_left (hI : M.IsBasis' I Y) (X : Set α) :
    M.eLocalConn X Y = (M.project X).nullity I := by
  rw [eLocalConn_comm, hI.eLocalConn_eq_nullity_project_right]

lemma IsBasis.eLocalConn_eq_nullity_project_left (hI : M.IsBasis I Y) (X : Set α) :
    M.eLocalConn X Y = (M.project X).nullity I := by
  rw [eLocalConn_comm, hI.eLocalConn_eq_nullity_project_right]

lemma Indep.eLocalConn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.eLocalConn I J = (I ∩ J).encard + M.nullity (I ∪ J) :=
  hI.isBasis_self.eLocalConn_eq hJ.isBasis_self

lemma IsBasis'.eLocalConn_eq_of_disjoint (hI : M.IsBasis' I X) (hJ : M.IsBasis' J Y)
    (hXY : Disjoint X Y) : M.eLocalConn X Y = M.nullity (I ∪ J) := by
  rw [hI.eLocalConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma IsBasis.eLocalConn_eq_of_disjoint (hI : M.IsBasis I X) (hJ : M.IsBasis J Y)
    (hXY : Disjoint X Y) : M.eLocalConn X Y = M.nullity (I ∪ J) := by
  rw [hI.eLocalConn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma eLocalConn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.IsBasis' I X)
    (hJ : M.IsBasis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.IsBasis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.eLocalConn X Y = F.encard := by
  have hF' : M.IsBasis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.isBasis_inter_ground.isBasis_subset diff_subset
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.eLocalConn_eq hJ, hF'.nullity_eq, diff_diff_cancel_left hFIJ,
    (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma eLocalConn_eq_encard_of_diff' {F : Set α} (hXY : Disjoint X Y) (hI : M.IsBasis' I X)
    (hJ : M.IsBasis' J Y) (hFI : F ⊆ I)  (hF : M.IsBasis' ((I \ F) ∪ J) (X ∪ Y)) :
    M.eLocalConn X Y = F.encard := by
  apply eLocalConn_eq_encard_of_diff hXY hI hJ (hFI.trans subset_union_left)
  rwa [union_diff_distrib, (sdiff_eq_left (x := J)).2 ]
  exact (hXY.symm.mono hJ.subset (hFI.trans hI.subset))

@[simp] lemma eLocalConn_closure_right (M : Matroid α) (X Y : Set α) :
    M.eLocalConn X (M.closure Y) = M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eLocalConn_eq_nullity_project_right, project_closure_eq,
    ← hI.eLocalConn_eq_nullity_project_right]

@[simp] lemma eLocalConn_closure_left (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (M.closure X) Y = M.eLocalConn X Y := by
  rw [eLocalConn_comm, eLocalConn_closure_right, eLocalConn_comm]

@[simp] lemma eLocalConn_closure_closure (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (M.closure X) (M.closure Y) = M.eLocalConn X Y := by
  rw [eLocalConn_closure_left, eLocalConn_closure_right]

lemma eLocalConn_inter_ground (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (X ∩ M.E) (Y ∩ M.E) = M.eLocalConn X Y := by
  rw [← eLocalConn_closure_closure, closure_inter_ground, closure_inter_ground _ Y,
    eLocalConn_closure_closure]

@[simp] lemma eLocalConn_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.eLocalConn (X ∩ M.E) Y = M.eLocalConn X Y := by
  rw [← eLocalConn_closure_left, closure_inter_ground, eLocalConn_closure_left]

@[simp] lemma eLocalConn_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.eLocalConn X (Y ∩ M.E) = M.eLocalConn X Y := by
  rw [← eLocalConn_closure_right, closure_inter_ground, eLocalConn_closure_right]

@[simp] lemma eLocalConn_restrict_eq (M : Matroid α) (X Y R : Set α) :
    (M ↾ R).eLocalConn X Y = M.eLocalConn (X ∩ R) (Y ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  obtain ⟨J, hJ⟩ := (M ↾ R).exists_isBasis' Y
  have ⟨hI', hI'R⟩ := isBasis'_restrict_iff.1 hI
  have ⟨hJ', hJ'R⟩ := isBasis'_restrict_iff.1 hJ
  rw [hI.eLocalConn_eq hJ, hI'.eLocalConn_eq hJ',
    nullity_restrict_of_subset _ (union_subset hI'R hJ'R)]

lemma eLocalConn_restrict_univ (M : Matroid α) (X Y : Set α) :
    (M ↾ univ).eLocalConn X Y = M.eLocalConn X Y := by
  simp

lemma eRk_add_eRk_eq_eRk_union_add_eLocalConn (M : Matroid α) (X Y : Set α) :
    M.eRk X + M.eRk Y = M.eRk (X ∪ Y) + M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [hI.eLocalConn_eq hJ, ← hI.encard_eq_eRk, ← hJ.encard_eq_eRk, ← eRk_closure_eq,
    ← closure_union_congr_left hI.closure_eq_closure,
    ← closure_union_congr_right hJ.closure_eq_closure, eRk_closure_eq, add_comm (I ∩ J).encard,
    ← add_assoc, eRk_add_nullity_eq_encard, encard_union_add_encard_inter]

lemma eRk_inter_le_eLocalConn (M : Matroid α) (X Y : Set α) : M.eRk (X ∩ Y) ≤ M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨IX, hIX⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans inter_subset_left)
  obtain ⟨IY, hIY⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans inter_subset_right)
  rw [← hI.encard_eq_eRk, hIX.1.eLocalConn_eq hIY.1]
  exact (encard_le_encard (subset_inter hIX.2 hIY.2)).trans le_self_add

lemma eLocalConn_mono_left {X' : Set α} (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.eLocalConn X' Y ≤ M.eLocalConn X Y := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  rw [hJ.eLocalConn_eq_nullity_project_left, hJ.eLocalConn_eq_nullity_project_left]
  apply nullity_project_mono _ hX

lemma eLocalConn_mono_right {Y' : Set α} (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.eLocalConn X Y' ≤ M.eLocalConn X Y := by
  grw [eLocalConn_comm, eLocalConn_mono_left M hY, eLocalConn_comm]

lemma eLocalConn_mono {X' Y' : Set α} (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.eLocalConn X' Y' ≤ M.eLocalConn X Y :=
  ((M.eLocalConn_mono_left hX Y').trans (M.eLocalConn_mono_right _ hY))

@[simp] lemma empty_eLocalConn (M : Matroid α) (X : Set α) : M.eLocalConn ∅ X = 0 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [(M.empty_indep.isBasis_self.isBasis').eLocalConn_eq hI]
  simp [hI.indep]

@[simp] lemma eLocalConn_empty (M : Matroid α) (X : Set α) : M.eLocalConn X ∅ = 0 := by
  rw [eLocalConn_comm, empty_eLocalConn]

lemma eLocalConn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.eLocalConn X Y = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eLocalConn_eq_nullity_project_right, hI.eRk_eq_encard, nullity_eq_encard]
  grw [hI.isBasis_closure_right.subset, project_loops]
  exact M.closure_mono hXY

lemma eLocalConn_eq_zero (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.eLocalConn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis Y
  rw [skew_iff_closure_skew, ← eLocalConn_closure_closure, ← hI.closure_eq_closure,
    ← hJ.closure_eq_closure, ← skew_iff_closure_skew, eLocalConn_closure_closure,
    hI.indep.eLocalConn_eq hJ.indep]
  simp [hI.indep.skew_iff_disjoint_union_indep hJ.indep, disjoint_iff_inter_eq_empty]

lemma Skew.eLocalConn (hXY : M.Skew X Y) : M.eLocalConn X Y = 0 := by
  rwa [eLocalConn_eq_zero]

lemma eLocalConn_restrict_of_subset (M : Matroid α) {R : Set α} (hXR : X ⊆ R) (hYR : Y ⊆ R) :
    (M ↾ R).eLocalConn X Y = M.eLocalConn X Y := by
  rw [eLocalConn_restrict_eq, inter_eq_self_of_subset_left hXR, inter_eq_self_of_subset_left hYR]

lemma eLocalConn_delete_eq (M : Matroid α) (X Y D : Set α) :
    (M ＼ D).eLocalConn X Y = M.eLocalConn (X \ D) (Y \ D) := by
  rw [delete_eq_restrict, eLocalConn_restrict_eq, ← inter_diff_assoc, inter_diff_right_comm,
    ← inter_diff_assoc, inter_diff_right_comm, eLocalConn_inter_ground]

lemma eLocalConn_delete_eq_of_disjoint (M : Matroid α) {D : Set α} (hXD : Disjoint X D)
    (hYD : Disjoint Y D) : (M ＼ D).eLocalConn X Y = M.eLocalConn X Y := by
  rw [eLocalConn_delete_eq, hXD.sdiff_eq_left, hYD.sdiff_eq_left]

@[simp] lemma eLocalConn_map {β : Type*} (M : Matroid α) (f : α → β) (hf) (X Y : Set β) :
    (M.map f hf).eLocalConn X Y = M.eLocalConn (f ⁻¹' X) (f ⁻¹' Y) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (f ⁻¹' X ∩ M.E)
  obtain ⟨J, hJ⟩ := M.exists_isBasis (f ⁻¹' Y ∩ M.E)
  have hI' := hI.map hf
  have hJ' := hJ.map hf
  rw [image_preimage_inter] at hI' hJ'
  rw [← M.eLocalConn_inter_ground, hI.eLocalConn_eq hJ, ← eLocalConn_inter_ground, map_ground,
    hI'.eLocalConn_eq hJ', ← hf.image_inter hI.indep.subset_ground hJ.indep.subset_ground,
    (hf.mono (inter_subset_left.trans hI.indep.subset_ground)).encard_image, ← image_union,
    nullity_eq_eRank_restrict_dual, ← M.map_restrict f hf (I ∪ J), map_dual, eRank_map,
    nullity_eq_eRank_restrict_dual]

@[simp] lemma eLocalConn_comap {β : Type*} (M : Matroid β) (f : α → β) (X Y : Set α) :
    (M.comap f).eLocalConn X Y = M.eLocalConn (f '' X) (f '' Y) := by
  -- TODO : Golf
  suffices aux : ∀ (N : Matroid β) X Y,
      (N.comap f).eLocalConn (f ⁻¹' (f '' X)) (f ⁻¹' (f '' Y)) = N.eLocalConn (f '' X) (f '' Y) by
    specialize aux (M ↾ univ) X Y
    rw [← eLocalConn_restrict_univ, ← M.eLocalConn_restrict_univ, ← aux,
      comap_restrict, preimage_univ, le_antisymm_iff]
    refine ⟨(eLocalConn_mono _ (subset_preimage_image _ _) (subset_preimage_image _ _)), ?_⟩
    rw [← eLocalConn_closure_closure _ X, ← comap_restrict_univ]
    refine eLocalConn_mono _ ?_ ?_
    all_goals
    · rw [comap_closure_eq]
      exact preimage_mono (subset_closure _ _)
  intro N P Q

  obtain ⟨I₀, hI₀⟩ := (N.comap f).exists_isBasis' (f ⁻¹' (f '' P) ∩ f ⁻¹' (f '' Q))
  obtain ⟨IP, hIP, hI₀IP⟩ := hI₀.indep.subset_isBasis'_of_subset
    (hI₀.subset.trans inter_subset_left)
  obtain ⟨IQ, hIQ, hI₀IQ⟩ := hI₀.indep.subset_isBasis'_of_subset
    (hI₀.subset.trans inter_subset_right)
  obtain ⟨hIP', hPinj, hIPP⟩ := comap_isBasis'_iff.1 hIP
  obtain ⟨hIQ', hQinj, hIQQ⟩ := comap_isBasis'_iff.1 hIQ

  rw [image_preimage_image] at hIP' hIQ'

  have hinj : InjOn f (IP ∪ IQ) := by
    rw [show IP ∪ IQ = IP ∪ (IQ \ IP) by simp, injOn_union disjoint_sdiff_right,
      and_iff_right hPinj, and_iff_right (hQinj.mono diff_subset)]
    refine fun x hx y ⟨hyQ, hyP⟩ hxy ↦ hyP <| hI₀IP ?_
    apply hI₀.mem_of_insert_indep
    · simp only [mem_inter_iff, mem_preimage]
      exact ⟨hxy ▸ (by simpa using hIP.subset hx), by simpa using hIQ.subset hyQ⟩
    exact hIQ.indep.subset <| insert_subset hyQ hI₀IQ

  rw [hIP.eLocalConn_eq hIQ, hIP'.eLocalConn_eq hIQ',
    ← hinj.image_inter subset_union_left subset_union_right,
    (hPinj.mono inter_subset_left).encard_image, ← image_union,
    nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual,
    ← comapOn_map N hinj, map_dual, eRank_map, comapOn]

@[simp] lemma eLocalConn_ground_eq (M : Matroid α) (X : Set α) : M.eLocalConn X M.E = M.eRk X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← eLocalConn_inter_ground_left, aux _ inter_subset_right, eRk_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
  rw [hI.eLocalConn_eq hB.isBasis_ground, hI.eRk_eq_encard, inter_eq_self_of_subset_left hIB,
    union_eq_self_of_subset_left hIB, hB.indep.nullity_eq, add_zero]

@[simp] lemma ground_eLocalConn_eq (M : Matroid α) (X : Set α) : M.eLocalConn M.E X = M.eRk X := by
  rw [eLocalConn_comm, eLocalConn_ground_eq]

lemma eLocalConn_le_eRk_left (M : Matroid α) (X Y : Set α) : M.eLocalConn X Y ≤ M.eRk X := by
  rw [← eLocalConn_inter_ground_right]
  exact (M.eLocalConn_mono_right X inter_subset_right).trans <| by simp

lemma eLocalConn_le_eRk_right (M : Matroid α) (X Y : Set α) : M.eLocalConn X Y ≤ M.eRk Y := by
  rw [eLocalConn_comm]
  apply eLocalConn_le_eRk_left

lemma Indep.encard_inter_add_nullity_le_eLocalConn (hI : M.Indep I) (hIX : I ⊆ X) (hJ : M.Indep J)
    (hJY : J ⊆ Y) : (I ∩ J).encard + M.nullity (I ∪ J) ≤ M.eLocalConn X Y := by
  obtain ⟨I', hI', hII'⟩ := hI.subset_isBasis'_of_subset hIX
  obtain ⟨J', hJ', hJJ'⟩ := hJ.subset_isBasis'_of_subset hJY
  rw [hI'.eLocalConn_eq hJ']
  exact add_le_add (encard_le_encard (inter_subset_inter hII' hJJ')) <|
    M.nullity_le_of_subset <| union_subset_union hII' hJJ'

lemma IsModularPair.eLocalConn_eq_eRk_inter (h : M.IsModularPair X Y) :
    M.eLocalConn X Y = M.eRk (X ∩ Y) := by
  obtain ⟨I, hIu, hIX, hIY, hIi⟩ := h.exists_common_isBasis
  rw [hIX.eLocalConn_eq hIY, ← hIi.encard_eq_eRk, ← inter_inter_distrib_left,
    ← inter_union_distrib_left, inter_eq_self_of_subset_left hIu.subset, hIu.indep.nullity_eq,
    add_zero, inter_assoc]


/-- Contracting a subset of `Y` that is skew to `X` doesn't change the local connectivity
between `X` and `Y`. -/
lemma eLocalConn_contract_right_skew_left' {C Y : Set α} (hXC : M.Skew X C) (hCY : C ⊆ Y) :
    (M ／ C).eLocalConn X (Y \ C) = M.eLocalConn X Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hI' : (M ／ C).IsBasis' I X := by
    have hI' := hI.isBase_restrict.isBasis_ground.isBasis'
    rwa [← hXC.symm.contract_restrict_eq, restrict_ground_eq, isBasis'_restrict_iff, inter_self,
      and_iff_left hI.subset] at hI'
  rw [hI.eLocalConn_eq_nullity_project_right, hI'.eLocalConn_eq_nullity_project_right,
    nullity_project_eq_nullity_contract, contract_contract, union_diff_cancel hCY,
    nullity_project_eq_nullity_contract]

lemma eLocalConn_insert_left_eq_add_one {e : α} (heX : e ∉ M.closure X)
    (heXY : e ∈ M.closure (X ∪ Y)) : M.eLocalConn (insert e X) Y = M.eLocalConn X Y + 1 := by
  have heE : e ∈ M.E := mem_ground_of_mem_closure heXY
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← eLocalConn_inter_ground_left, insert_inter_of_mem heE,
      aux (by simpa) _ inter_subset_right, eLocalConn_inter_ground_left]
    rwa [← closure_inter_ground, union_inter_distrib_right, inter_assoc, inter_self,
      ← union_inter_distrib_right, closure_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis' Y
  have hIe : M.IsBasis (insert e I) (insert e X) := by
    refine hI.insert_isBasis_insert ?_
    rw [hI.indep.insert_indep_iff, hI.closure_eq_closure]
    exact .inl ⟨heE, heX⟩

  rw [hI.isBasis'.eLocalConn_eq hJ, hIe.isBasis'.eLocalConn_eq hJ, insert_union]
  have heI : e ∉ I := notMem_subset (hI.subset.trans (M.subset_closure X)) heX
  by_cases heJ : e ∈ J
  · rw [insert_inter_of_mem heJ, insert_eq_of_mem (mem_union_right _ heJ),
      encard_insert_of_notMem (by simp [heI]), add_right_comm]

  rw [insert_inter_of_notMem heJ, nullity_insert_eq_add_one
    (by rwa [closure_union_congr_left hI.closure_eq_closure,
      closure_union_congr_right hJ.closure_eq_closure]) (by simp [heI, heJ]), add_assoc]

lemma IsRkFinite.isModularPair_iff_eLocalConn_eq_eRk_inter (hX : M.IsRkFinite X) (Y : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.IsModularPair X Y ↔ M.eLocalConn X Y = M.eRk (X ∩ Y) := by
  refine ⟨fun h ↦ h.eLocalConn_eq_eRk_inter, fun h ↦ ?_⟩
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ := hIi.exists_isBasis_inter_eq_of_superset inter_subset_left
  obtain ⟨IY, hIY, hIY'⟩ := hIi.exists_isBasis_inter_eq_of_superset inter_subset_right

  have h_inter : Ii = IX ∩ IY
  · exact hIi.eq_of_subset_indep (hIX.indep.inter_right _)
      (subset_inter (by simp [← hIX']) (by simp [← hIY']))
      (inter_subset_inter hIX.subset hIY.subset)

  rw [hIX.eLocalConn_eq hIY, ← h_inter, hIi.encard_eq_eRk, ← add_zero (a := M.eRk _), add_assoc,
    zero_add, WithTop.add_left_inj hX.inter_right.eRk_lt_top.ne, nullity_eq_zero] at h

  exact h.isModularPair_of_union.of_isBasis_of_isBasis hIX hIY

lemma eLocalConn_insert_right_eq_add_one {e : α} (heY : e ∉ M.closure Y)
    (heXY : e ∈ M.closure (X ∪ Y)) : M.eLocalConn X (insert e Y) = M.eLocalConn X Y + 1 := by
  rw [eLocalConn_comm, eLocalConn_insert_left_eq_add_one heY (by rwa [union_comm]),
    eLocalConn_comm]

/-- For finite matroids, this is another rearrangement of the formula in
`Matroid.eRk_add_eRk_eq_eRk_union_add_eLocalConn`.
For infinite matroids it needs a separate proof. -/
lemma eLocalConn_add_eRelRk_union_eq_eRk (M : Matroid α) (X Y : Set α) :
    M.eLocalConn X Y + M.eRelRk Y (X ∪ Y) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hcl : (M.project Y).closure X = (M.project Y).closure I := by
    simp [closure_union_congr_left hI.closure_eq_closure]
  rw [hI.eLocalConn_eq_nullity_project_right, hI.eRk_eq_encard, ← eRelRk_eq_union_right,
    eRelRk_eq_eRk_project, ← eRk_closure_eq, hcl, eRk_closure_eq, add_comm,
    eRk_add_nullity_eq_encard]

lemma IsHyperplane.eLocalConn_add_one_eq {H X : Set α} (hH : M.IsHyperplane H) (hXH : ¬ (X ⊆ H))
    (hXE : X ⊆ M.E := by aesop_mat) : M.eLocalConn X H + 1 = M.eRk X := by
  rw [← M.eLocalConn_add_eRelRk_union_eq_eRk X H, ← eRelRk_closure_right,
    (hH.spanning_of_ssuperset (show H ⊂ X ∪ H by simpa)).closure_eq, hH.eRelRk_eq_one]

@[simp]
lemma removeLoops_eLocalConn (M : Matroid α) : M.removeLoops.eLocalConn = M.eLocalConn := by
  ext _ _
  rw [removeLoops_eq_restrict, eLocalConn_restrict_eq, ← eLocalConn_closure_closure]
  simp

end eLocalConn

section localConn

/-- The `ℕ`-valued local connectivity between sets `X` and `Y`, often denoted `⊓ (X, Y)`.
Equal to `M.r X + M.r Y - M.r (X ∪ Y)` if both sets have finite rank.
This is only mathematically meaningful if at least one of `X` and `Y` is known to have finite rank;
otherwise `Matroid.eLocalConn` is preferable. -/
noncomputable def localConn (M : Matroid α) (X Y : Set α) : ℕ := (M.eLocalConn X Y).toNat

lemma localConn_comm (M : Matroid α) (X Y : Set α) : M.localConn X Y = M.localConn Y X := by
  rw [localConn, eLocalConn_comm, localConn]

lemma IsRkFinite.cast_localConn_right_eq (hX : M.IsRkFinite X) (Y : Set α) :
    (M.localConn X Y : ℕ∞) = M.eLocalConn X Y :=
  ENat.coe_toNat fun htop ↦ hX.eRk_lt_top.not_ge
    <| htop.symm.le.trans <| M.eLocalConn_le_eRk_left X Y

lemma IsRkFinite.cast_localConn_left_eq (hY : M.IsRkFinite Y) :
    (M.localConn X Y : ℕ∞) = M.eLocalConn X Y := by
  rw [localConn_comm, hY.cast_localConn_right_eq, eLocalConn_comm]

lemma IsRkFinite.rk_add_rk_eq_rk_union_add_localConn (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y) :
    M.rk X + M.rk Y = M.rk (X ∪ Y) + M.localConn X Y := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, Nat.cast_add, hX.cast_localConn_right_eq,
    hX.cast_rk_eq, hY.cast_rk_eq, (hX.union hY).cast_rk_eq, eRk_add_eRk_eq_eRk_union_add_eLocalConn]

lemma rk_add_rk_eq_rk_union_add_localConn (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.rk X + M.rk Y = M.rk (X ∪ Y) + M.localConn X Y :=
  (M.isRkFinite_set X).rk_add_rk_eq_rk_union_add_localConn (M.isRkFinite_set Y)

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
lemma IsRkFinite.localConn_eq_rk_add_rk_sub (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y) :
    M.localConn X Y = M.rk X + M.rk Y - M.rk (X ∪ Y) := by
  rw [hX.rk_add_rk_eq_rk_union_add_localConn hY, add_comm]
  exact Nat.eq_sub_of_add_eq rfl

/-- The formula for local connectivity of two finite-rank sets written with `Int` subtraction,
for use with `ring` and `linarith`. -/
lemma IsRkFinite.localConn_intCast_eq (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y) :
    (M.localConn X Y : ℤ) = M.rk X + M.rk Y - M.rk (X ∪ Y) := by
  rw [hX.localConn_eq_rk_add_rk_sub hY, ← Nat.cast_add]
  exact Int.natCast_sub (rk_union_le_rk_add_rk _ _ _)

/-- The formula for local connectivity in terms of the rank function.
This uses `ℕ` subtraction which never overflows. -/
lemma localConn_eq_rk_add_rk_sub (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.localConn X Y = M.rk X + M.rk Y - M.rk (X ∪ Y) :=
  (M.isRkFinite_set X).localConn_eq_rk_add_rk_sub (M.isRkFinite_set Y)

/-- The formula for local connectivity written in terms of `Int` subtraction,
for use with `ring` and `linarith`. -/
@[simp]
lemma localConn_intCast_eq (M : Matroid α) [RankFinite M] (X Y : Set α) :
    (M.localConn X Y : ℤ) = M.rk X + M.rk Y - M.rk (X ∪ Y) :=
  (M.isRkFinite_set X).localConn_intCast_eq (M.isRkFinite_set Y)

lemma IsModularPair.localConn_eq_rk_inter (h : M.IsModularPair X Y) :
    M.localConn X Y = M.rk (X ∩ Y) := by
  rw [localConn, h.eLocalConn_eq_eRk_inter, rk]

lemma IsRkFinite.isModularPair_iff_localConn_eq_rk_inter (hX : M.IsRkFinite X) (Y : Set α)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.IsModularPair X Y ↔ M.localConn X Y = M.rk (X ∩ Y) := by
  rw [hX.isModularPair_iff_eLocalConn_eq_eRk_inter Y hXE hYE, localConn, rk,
    ← Nat.cast_inj (R := ℕ∞), ENat.coe_toNat, ENat.coe_toNat]
  · rw [eRk_ne_top_iff]
    exact hX.inter_right
  rw [← WithTop.lt_top_iff_ne_top]
  exact (M.eLocalConn_le_eRk_left _ _).trans_lt hX.eRk_lt_top

lemma isModularPair_iff_localConn_eq_rk_inter [RankFinite M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) : M.IsModularPair X Y ↔ M.localConn X Y = M.rk (X ∩ Y) :=
  (M.isRkFinite_set X).isModularPair_iff_localConn_eq_rk_inter _ hXE hYE

lemma IsCircuit.eLocalConn_subset_compl {C : Set α} (hC : M.IsCircuit C) (hI : I.Nonempty)
    (hIC : I ⊂ C) : M.eLocalConn I (C \ I) = 1 := by
  obtain ⟨e, heC, heI⟩ := exists_of_ssubset hIC
  have hi' : C \ I ⊂ C := by simpa [inter_eq_self_of_subset_right hIC.subset]
  rw [(hC.ssubset_indep hIC).isBasis_self.eLocalConn_eq (hC.ssubset_indep hi').isBasis_self,
    disjoint_sdiff_right.inter_eq, encard_empty, zero_add, union_diff_cancel hIC.subset,
    hC.nullity_eq]

end localConn

section eConn

/-- The `ℕ∞`-valued connectivity of a set `X` to its complement, traditionally written as `λ (X)`.
For a `ℕ`-valued version, see `Matroid.conn`. -/
noncomputable def eConn (M : Matroid α) (X : Set α) : ℕ∞ := M.eLocalConn X (M.E \ X)

lemma eConn_eq_eLocalConn (M : Matroid α) (X : Set α) : M.eConn X = M.eLocalConn X (M.E \ X) := rfl

@[simp] lemma eConn_inter_ground (M : Matroid α) (X : Set α) :  M.eConn (X ∩ M.E) = M.eConn X := by
  rw [eConn, eLocalConn_inter_ground_left, eConn, diff_inter_self_eq_diff]

lemma IsBasis'.eConn_eq (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J (M.E \ X)) :
    M.eConn X = M.nullity (I ∪ J) := by
  rw [eConn_eq_eLocalConn, hIX.eLocalConn_eq_of_disjoint hJX disjoint_sdiff_right]

lemma IsBasis.eConn_eq (hIX : M.IsBasis I X) (hJX : M.IsBasis J (M.E \ X)) :
    M.eConn X = M.nullity (I ∪ J) :=
  hIX.isBasis'.eConn_eq hJX.isBasis'

lemma IsBasis.eConn_eq' (hIX : M.IsBasis I X) (hJX : M.IsBasis J Xᶜ) :
    M.eConn X = M.nullity (I ∪ J) := by
  rw [hIX.eConn_eq (hJX.isBasis_subset ?_ (diff_subset_compl ..))]
  rw [subset_diff, ← subset_compl_iff_disjoint_right]
  exact ⟨hJX.indep.subset_ground, hJX.subset⟩

lemma eConn_eq_eLocalConn' (M : Matroid α) (X : Set α) :
    M.eConn X = M.eLocalConn (M.E ∩ X) (M.E \ X) := by
  rw [← eConn_inter_ground, eConn_eq_eLocalConn, diff_inter_self_eq_diff, inter_comm]

@[simp]
lemma removeLoops_eConn (M : Matroid α) : M.removeLoops.eConn = M.eConn := by
  ext X
  rw [eConn, removeLoops_eLocalConn, eConn, ← eLocalConn_closure_right, removeLoops_ground_eq,
    diff_eq_compl_inter, closure_inter_setOf_isNonloop_eq, ← closure_inter_ground,
    ← diff_eq_compl_inter, eLocalConn_closure_right]

lemma eConn_union_of_subset_loops (X : Set α) {L : Set α} (hL : L ⊆ M.loops) :
    M.eConn (X ∪ L) = M.eConn X := by
  rw [← removeLoops_eConn, ← eConn_inter_ground, removeLoops_ground_eq, setOf_isNonloop_eq,
    show (X ∪ L) ∩ (M.E \ M.loops) = X ∩ (M.E \ M.loops) by tauto_set,
    ← setOf_isNonloop_eq, ← removeLoops_ground_eq, eConn_inter_ground]

lemma eConn_diff_of_subset_loops (X : Set α) {L : Set α} (hL : L ⊆ M.loops) :
    M.eConn (X \ L) = M.eConn X := by
  rw [← eConn_union_of_subset_loops _ hL, diff_union_self, eConn_union_of_subset_loops _ hL]

lemma Indep.nullity_union_le_eConn (hI : M.Indep I) (hJ : M.Indep J) (hIX : I ⊆ X)
    (hJX : Disjoint J X) : M.nullity (I ∪ J) ≤ M.eConn X := by
  rw [eConn_eq_eLocalConn]
  refine le_trans ?_ <| hI.encard_inter_add_nullity_le_eLocalConn hIX hJ (Y := M.E \ X) ?_
  · simp [(hJX.symm.mono_left hIX).inter_eq]
  rwa [subset_diff, and_iff_right hJ.subset_ground]

@[simp]
lemma eConn_restrict_univ_eq (M : Matroid α) (X : Set α) : (M ↾ univ).eConn X = M.eConn X := by
  rw [← removeLoops_eConn, ← M.removeLoops_eConn, restrict_univ_removeLoops_eq]

@[simp]
lemma eConn_corestrict_univ_eq (M : Matroid α) (X : Set α) : (M✶ ↾ univ)✶.eConn X = M.eConn X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ⟩ := M.exists_isBasis (M.E \ X)
  have hJ' : (M✶ ↾ univ)✶.IsBasis (J ∪ (Xᶜ \ M.E)) ((M✶ ↾ univ)✶.E \ X) := by
    rwa [dual_ground, restrict_ground_eq, ← compl_eq_univ_diff, corestrict_univ_isBasis_iff,
      union_subset_iff, and_iff_left subset_union_right, and_iff_left diff_subset,
      and_iff_left <| hJ.subset.trans <| diff_subset_compl .., ← diff_eq_compl_inter,
      union_inter_distrib_right, disjoint_sdiff_left.inter_eq, union_empty,
      inter_eq_self_of_subset_left hJ.indep.subset_ground]
  rw [hI.corestrict_univ_isBasis.isBasis'.eConn_eq hJ'.isBasis', hI.eConn_eq hJ.isBasis',
    nullity_corestrict_univ_eq_nullity_inter, union_right_comm, union_assoc, union_assoc,
    ← union_diff_distrib, ← union_assoc, union_inter_distrib_right, disjoint_sdiff_left.inter_eq,
    union_empty,
    inter_eq_self_of_subset_left (union_subset hI.indep.subset_ground hJ.indep.subset_ground)]

@[simp]
lemma eConn_compl (M : Matroid α) (X : Set α) : M.eConn (M.E \ X) = M.eConn X := by
  rw [eq_comm, ← eConn_inter_ground, eConn, diff_inter_self_eq_diff, eConn, eLocalConn_comm,
    inter_comm]
  simp

/-- A version of `eConn_compl` where `compl` really means complementation in the universe. -/
@[simp]
lemma eConn_compl' (M : Matroid α) (X : Set α) : M.eConn Xᶜ = M.eConn X := by
  rw [← eConn_restrict_univ_eq, compl_eq_univ_diff, ← M.eConn_restrict_univ_eq,
    eq_comm, ← eConn_compl, restrict_ground_eq]

/-- Connectivity is self-dual. -/
@[simp]
lemma eConn_dual (M : Matroid α) (X : Set α) : M✶.eConn X = M.eConn X := by
  wlog h : OnUniv M with aux
  · rw [← eConn_corestrict_univ_eq, dual_dual, eq_comm, ← eConn_restrict_univ_eq, aux _ _ ⟨rfl⟩]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis (M.E \ X)
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset <| subset_union_left (t := J)
  have hsp : M.Spanning (X ∪ J) := by
    simp [spanning_iff_closure_eq, closure_union_congr_right hJ.closure_eq_closure]
  have hBdual := (hB.isBase_of_spanning hsp).compl_inter_isBasis_of_inter_isBasis hI
  rw [diff_inter_diff, union_comm, ← diff_diff] at hBdual
  obtain ⟨B', hB', rfl⟩ := hJ.exists_isBase
  have hB'dual : M✶.IsBasis (B'ᶜ ∩ X) X := by
    simpa [← compl_eq_univ_diff] using hB'.compl_inter_isBasis_of_inter_isBasis hJ
  have hBss := hB.subset
  have hgd := OnUniv.ground_diff_eq M X
  rw [ hB'dual.eConn_eq hBdual, hI.eConn_eq hJ, OnUniv.ground_diff_eq,
    (hB.isBasis_subset (by tauto_set) (by tauto_set)).nullity_eq,
    (hB'.compl_isBase_dual.isBasis_ground.isBasis_subset (by tauto_set) (by simp)).nullity_eq,
    OnUniv.ground_diff_eq]
  exact congr_arg _ <| by tauto_set

lemma eConn_union_of_subset_coloops (X : Set α) {L : Set α} (hL : L ⊆ M.coloops) :
    M.eConn (X ∪ L) = M.eConn X := by
  rw [← eConn_dual, eConn_union_of_subset_loops _ hL, eConn_dual]

lemma eConn_diff_of_subset_coloops (X : Set α) {L : Set α} (hL : L ⊆ M.coloops) :
    M.eConn (X \ L) = M.eConn X := by
  rw [← eConn_dual, eConn_diff_of_subset_loops _ hL, eConn_dual]

lemma eLocalConn_project_eq_eLocalConn_contract_diff (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y = (M ／ C).eLocalConn (X \ C) (Y \ C) := by
  rw [project, eLocalConn_restrict_eq, ← eLocalConn_inter_ground, eq_comm,
    ← eLocalConn_inter_ground, contract_ground]
  convert rfl using 2 <;> tauto_set

lemma eLocalConn_project_eq_eLocalConn_contract (M : Matroid α) (X Y C : Set α) :
    (M.project C).eLocalConn X Y = (M ／ C).eLocalConn X Y := by
  rw [project, eLocalConn_restrict_eq, ← eLocalConn_inter_ground, eq_comm,
    ← eLocalConn_inter_ground, contract_ground]
  convert rfl using 2 <;> tauto_set

lemma eConn_delete_eq {X D : Set α} (hDX : D ⊆ X) (hX : X ⊆ M.closure (X \ D)) :
    (M ＼ D).eConn (X \ D) = M.eConn X := by
  have hXE : X ⊆ M.E := hX.trans <| closure_subset_ground ..
  obtain ⟨I, hI⟩ := (M ＼ D).exists_isBasis (X \ D) (diff_subset_diff_left hXE)
  obtain ⟨J, hJ⟩ := (M ＼ D).exists_isBasis ((M ＼ D).E \ (X \ D)) diff_subset
  rw [hI.eConn_eq hJ, nullity_delete]
  · rw [delete_isBasis_iff, delete_ground, diff_diff, union_diff_cancel hDX] at hJ
    rw [delete_isBasis_iff] at hI
    rw [(hI.1.isBasis_closure_right.isBasis_subset (hI.1.subset.trans diff_subset) hX).eConn_eq
      hJ.1]
  rw [disjoint_union_left]
  exact ⟨(subset_diff.1 hI.subset).2, (subset_diff.1 (hJ.subset.trans diff_subset)).2⟩

lemma IsBasis'.eConn_delete_diff_eq (hIX : M.IsBasis' I X) : (M ＼ (X \ I)).eConn I = M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · rw [← M.eConn_inter_ground, ← aux hIX.isBasis_inter_ground.isBasis' inter_subset_right,
      ← delete_inter_ground_eq, ← inter_diff_right_comm]
  rw [← M.eConn_delete_eq (show X \ I ⊆ X from diff_subset), diff_diff_cancel_left hIX.subset]
  rw [diff_diff_cancel_left hIX.subset]
  exact hIX.isBasis.subset_closure

lemma IsBasis.eConn_delete_diff_eq (hIX : M.IsBasis I X) : (M ＼ (X \ I)).eConn I = M.eConn X :=
  hIX.isBasis'.eConn_delete_diff_eq

lemma eRk_add_eRk_compl_eq (M : Matroid α) (X : Set α) :
    M.eRk X + M.eRk (M.E \ X) = M.eRank + M.eConn X := by
  rw [eConn_eq_eLocalConn, eRk_add_eRk_eq_eRk_union_add_eLocalConn, union_diff_self,
    ← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

lemma eConn_le_eRk (M : Matroid α) (X : Set α) : M.eConn X ≤ M.eRk X :=
  eLocalConn_le_eRk_left _ _ _

lemma eConn_restrict_le (M : Matroid α) (X R : Set α) : (M ↾ R).eConn X ≤ M.eConn X := by
  rw [eConn_eq_eLocalConn, eLocalConn_restrict_eq, eConn_eq_eLocalConn, restrict_ground_eq,
    ← eLocalConn_inter_ground_right]
  exact M.eLocalConn_mono inter_subset_left (by tauto_set)

lemma eConn_delete_le (M : Matroid α) (X D : Set α) : (M ＼ D).eConn X ≤ M.eConn X := by
  rw [delete_eq_restrict]
  apply eConn_restrict_le

lemma eConn_contract_le (M : Matroid α) (X C : Set α) : (M ／ C).eConn X ≤ M.eConn X := by
  rw [← eConn_dual, dual_contract, ← M.eConn_dual]
  apply eConn_delete_le

lemma IsMinor.eConn_le {N : Matroid α} (hNM : N ≤m M) (X : Set α) : N.eConn X ≤ M.eConn X := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact ((M ／ C).eConn_delete_le X D).trans <| M.eConn_contract_le X C

end eConn

section conn

/-- The `ℕ`-valued connectivity of a set `X` to its complement, traditionally written `λ (X)`.
Being `ℕ`-valued, this is not well-behaved unless `M` or its dual has finite rank,
since a set with infinite connectivity to its complement has a `conn` of zero.
If neither `M` nor `M✶` is known to have finite rank, then `Matroid.eConn` is better. -/
noncomputable def conn (M : Matroid α) (X : Set α) : ℕ := (M.eConn X).toNat

@[simp] lemma conn_dual (M : Matroid α) (X : Set α) : M✶.conn X = M.conn X := by
  rw [conn, eConn_dual, conn]

@[simp] lemma conn_inter_ground (M : Matroid α) (X : Set α) : M.conn (X ∩ M.E) = M.conn X := by
  rw [conn, eConn_inter_ground, conn]

@[simp] lemma cast_conn_eq (M : Matroid α) [RankFinite M] (X : Set α) :
    (M.conn X : ℕ∞) = M.eConn X := by
  rw [conn, eConn_eq_eLocalConn]
  exact ENat.coe_toNat ((eLocalConn_le_eRk_left _ _ _).trans_lt (M.isRkFinite_set X).eRk_lt_top).ne

@[simp] lemma cast_conn_eq' (M : Matroid α) [RankFinite M✶] : (M.conn X : ℕ∞) = M.eConn X := by
  rw [← conn_dual, cast_conn_eq, eConn_dual]

lemma conn_eq_localConn (M : Matroid α) (X : Set α) : M.conn X = M.localConn X (M.E \ X) := by
  rw [conn, eConn_eq_eLocalConn, localConn]

lemma rk_add_rk_compl_eq (M : Matroid α) [RankFinite M] (X : Set α) :
    M.rk X + M.rk (M.E \ X) = M.rank + M.conn X := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, cast_rk_eq, cast_rk_eq, Nat.cast_add,
    rank_def, cast_rk_eq, eRk_add_eRk_compl_eq, cast_conn_eq, eRank_def]

/-- A formula for the connectivity of a set in terms of the rank function.
`Matroid.rk_add_rk_compl_eq` implies that the `ℕ` subtraction will never overflow.  -/
lemma conn_eq_rk_add_rk_sub_rank (M : Matroid α) [RankFinite M] (X : Set α) :
    M.conn X = M.rk X + M.rk (M.E \ X) - M.rank := by
  rw [conn_eq_localConn, localConn_eq_rk_add_rk_sub, union_diff_self, rk_eq_rank subset_union_right]

/-- A version of `Matroid.conn_eq_rk_add_rk_sub_rank` with `Int` subtraction,
for use with `ring, linarith`, etc. -/
@[simp]
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
This is also true for `eConn` without `RankFinite`, but the proof will be more difficult. TODO. -/
lemma conn_submod (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.conn (X ∩ Y) + M.conn (X ∪ Y) ≤ M.conn X + M.conn Y := by
  simpa using M.conn_inter_add_conn_union_union_le (disjoint_empty X).symm (disjoint_empty Y).symm

end conn

section core

/-- The core of a set is its intersection with the set of nonloop, noncoloop elements.
This does not change the connectivity of a set, and is stable under duality.
This is mostly an implementation detail, used for relating connectivity to junk elements . -/
protected def core (M : Matroid α) (X : Set α) := ((X \ M.loops) \ M.coloops) ∩ M.E

lemma core_def (M : Matroid α) (X : Set α) : M.core X = ((X \ M.loops) \ M.coloops) ∩ M.E :=
  rfl

@[simp]
lemma core_subset (M : Matroid α) (X : Set α) : M.core X ⊆ X :=
  inter_subset_left.trans <| diff_subset.trans diff_subset

@[simp, aesop safe (rule_sets := [Matroid])]
lemma core_subset_ground (M : Matroid α) (X : Set α) : M.core X ⊆ M.E :=
  inter_subset_right

@[simp]
lemma core_inter_ground (M : Matroid α) (X : Set α) : M.core (X ∩ M.E) = M.core X := by
  simp_rw [core_def]
  tauto_set

@[simp]
lemma core_empty (M : Matroid α) : M.core ∅ = ∅ := by
  simpa using M.core_subset ∅

@[simp]
lemma core_dual (M : Matroid α) (X : Set α) : M✶.core X = M.core X := by
  rw [core_def, coloops, dual_dual, diff_diff_comm, dual_ground]
  rfl

@[simp]
lemma removeLoops_core (M : Matroid α) (X : Set α) : M.removeLoops.core X = M.core X := by
  rw [core_def, removeLoops_ground_eq, setOf_isNonloop_eq, core_def, loops_eq_empty,
    removeLoops_coloops_eq]
  tauto_set

@[simp]
lemma eConn_core (M : Matroid α) : M.eConn (M.core X) = M.eConn X := by
  rw [Matroid.core, eConn_inter_ground, eConn_diff_of_subset_coloops _ rfl.subset,
    eConn_diff_of_subset_loops _ rfl.subset]

@[simp]
lemma core_core (M : Matroid α) (X : Set α) : M.core (M.core X) = M.core X := by
  rw [core_def, core_def]
  tauto_set

@[simp]
lemma core_union (M : Matroid α) (X Y : Set α) : M.core (X ∪ Y) = M.core X ∪ M.core Y := by
  simp_rw [core_def]
  tauto_set

@[simp]
lemma core_inter (M : Matroid α) (X Y : Set α) : M.core (X ∩ Y) = M.core X ∩ M.core Y := by
  simp_rw [core_def]
  tauto_set

@[simp]
lemma core_diff (M : Matroid α) (X Y : Set α) : M.core (X \ Y) = M.core X \ M.core Y := by
  simp_rw [core_def]
  tauto_set

lemma core_subset_core (M : Matroid α) (hXY : X ⊆ Y) : M.core X ⊆ M.core Y := by
  rw [← diff_eq_empty, ← core_diff, diff_eq_empty.2 hXY, core_empty]

@[simp]
lemma core_subset_inter_ground (M : Matroid α) (X : Set α) : M.core X ⊆ X ∩ M.E :=
  inter_subset_inter_left _ <| diff_subset.trans diff_subset

@[simp]
lemma core_delete_subset (M : Matroid α) (X D : Set α) : (M ＼ D).core X ⊆ M.core X := by
  simp_rw [core_def, delete_loops_eq, coloops, dual_delete, contract_loops_eq,
    delete_ground]
  have := M✶.closure_subset_closure (empty_subset D)
  tauto_set

@[simp]
lemma core_restrict_subset (M : Matroid α) (X R : Set α) : (M ↾ R).core X ⊆ M.core X := by
  rw [← removeLoops_core, restrict_removeLoops, removeLoops_core, ← delete_compl]
  apply core_delete_subset

@[simp]
lemma core_contract_subset (M : Matroid α) (X C : Set α) : (M ／ C).core X ⊆ M.core X := by
   rw [← core_dual, dual_contract, ← M.core_dual]
   apply core_delete_subset

end core

-- section BasisDuo

-- --

-- /-- Bases for `X` and `Y` that intersect in a basis for `X ∩ Y`. -/
-- structure BasisDuo (M : Matroid α) (X Y : Set α) where
--   I : Set α
--   J : Set α
--   isBasis'_left : M.IsBasis' I X
--   isBasis'_right : M.IsBasis' J Y
--   isBasis'_inter : M.IsBasis' (I ∩ J) (X ∩ Y)

-- lemma BasisDuo.subset_left (B : M.BasisDuo X Y) : B.I ⊆ X := B.isBasis'_left.subset
-- lemma BasisDuo.subset_right (B : M.BasisDuo X Y) : B.J ⊆ Y := B.isBasis'_right.subset
-- lemma BasisDuo.indep_left (B : M.BasisDuo X Y) : M.Indep B.I := B.isBasis'_left.indep
-- lemma BasisDuo.indep_right (B : M.BasisDuo X Y) : M.Indep B.J := B.isBasis'_right.indep


-- lemma nonempty_basisDuo (M : Matroid α) (X Y : Set α) : Nonempty (M.BasisDuo X Y) := by
--   obtain ⟨K, hK⟩ := M.exists_isBasis' (X ∩ Y)
--   obtain ⟨I, hI, hIss⟩ := hK.indep.subset_isBasis'_of_subset (hK.subset.trans inter_subset_left)
--   obtain ⟨J, hJ, hJss⟩ := hK.indep.subset_isBasis'_of_subset (hK.subset.trans inter_subset_right)
--   refine ⟨I, J, hI, hJ, ?_⟩
--   rwa [← hK.eq_of_subset_indep (hI.indep.inter_right J) (subset_inter hIss hJss)
--     (by grw [hI.subset, hJ.subset])]

-- lemma BasisDuo.inter_eq (B : M.BasisDuo X Y) : B.I ∩ Y = B.J ∩ X := by
--   rw [← B.isBasis'_inter.eq_of_subset_indep (B.indep_left.inter_right Y) (by grw [B.subset_right]
--     (by grw [B.subset_left]), B.isBasis'_inter.eq_of_subset_indep (B.indep_right.inter_left X)
--     (by grw [B.subset_left]) (by grw [B.subset_right]), inter_comm]

-- @[simps]
-- def BasisDuo.symm (B : M.BasisDuo X Y) : M.BasisDuo Y X where
--   I := B.J
--   J := B.I
--   isBasis'_left := B.isBasis'_right
--   isBasis'_right := B.isBasis'_left
--   isBasis'_inter := by
--     rw [inter_comm, inter_comm (a := Y)]
--     exact B.isBasis'_inter

-- -- def BasisDuo.diff_left (B : M.BasisDuo X Y) : Set α := B.I \ B.J

-- -- def BasisDuo.diff_right (B : M.BasisDuo X Y) : Set α := B.J \ B.I

-- -- def BasisDuo.inter (B : M.BasisDuo X Y) : Set α := B.I \ B.J


-- lemma BasisDuo.exists_isBasis'_union (B : M.BasisDuo X Y) :
--     ∃ K, M.IsBasis' K (X ∪ Y) ∧ B.I ⊆ K ∧ K ⊆ B.I ∪ B.J := by
--   obtain ⟨K, hK : M.IsBasis' K (B.I ∪ B.J), hKss⟩ :=
--     B.isBasis'_left.indep.subset_isBasis'_of_subset subset_union_left
--   refine ⟨K, isBasis'_iff_isBasis_closure.2 ⟨?_, ?_⟩, hKss, hK.subset⟩
--   · rw [← closure_union_congr_left B.isBasis'_left.closure_eq_closure,
--       ← closure_union_congr_right B.isBasis'_right.closure_eq_closure]
--     exact hK.isBasis_closure_right
--   grw [hK.subset, B.subset_left, B.subset_right]

-- lemma BasisDuo.diff_isBasis'_project_right (B : M.BasisDuo X Y) :
--     (M.project (X ∩ Y)).IsBasis' (B.J \ B.I) Y := by
--   rw [B.isBasis'_inter.project_eq_project, (B.indep_left.inter_right _).project_isBasis'_iff,
--     union_comm, inter_comm, diff_union_inter, union_eq_self_of_subset_left,
--     and_iff_left (disjoint_sdiff_right.mono_left inter_subset_right)]
--   · exact B.isBasis'_right
--   grw [inter_subset_left, B.subset_right]

-- lemma BasisDuo.diff_isBasis'_project_left (B : M.BasisDuo X Y) :
--     (M.project (X ∩ Y)).IsBasis' (B.I \ B.J) X := by
--   simpa [inter_comm X] using B.symm.diff_isBasis'_project_right

-- end BasisDuo





-- structure BasisQuad (M : Matroid α) (X Y : Set α) where
--   I₀ : Set α
--   IX : Set α
--   IY : Set α
--   I₁ : Set α
--   I₀_basis : M.IsBasis' I₀ (X ∩ Y)
--   IX_basis : M.IsBasis' (I₀ ∪ IX) X
--   IY_basis : M.IsBasis' (I₀ ∪ IY) Y
--   I₁_basis : M.IsBasis' (I₀ ∪ I₁) (X ∪ Y)
--   disjoint_left_IY : Disjoint X IY
--   disjoint_IX_right : Disjoint IX Y
--   I₁_subset : I₁ ⊆ IX ∪ IY
--   subset_I₁ : IX ⊆ I₁

-- -- lemma exists_basisQuad (M : Matroid α) (X Y : Set α) where


-- lemma bar1 (M : Matroid α) (X Y : Set α) : ∃ I IX IY I₁, M.IsBasis' I (X ∩ Y)
--     ∧ M.IsBasis' (I ∪ IX) X ∧ M.IsBasis' (I ∪ IY) Y ∧ M.IsBasis' (I ∪ I₁) (X ∪ Y)
--     ∧ IX ⊆ X ∧ Disjoint IX Y ∧ IY ⊆ Y ∧ Disjoint IY X ∧ IX ⊆ I₁ ∧ I₁ ⊆ IX ∪ IY := by
--   obtain ⟨I, hI⟩ := M.exists_isBasis' (X ∩ Y)
--   obtain ⟨IX', hX, hIX'⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans inter_subset_le
-- ft)
--   obtain ⟨IY', hY, hIY'⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans inter_subset_rig
-- ht)
--   obtain ⟨I₁', hI₁' : M.IsBasis' I₁' (IX' ∪ IY'), hss⟩ :=
--     hX.indep.subset_isBasis'_of_subset subset_union_left
--   have h_inter_right : IX' ∩ Y = I := Eq.symm <| hI.eq_of_subset_indep (hX.indep.inter_right Y)
--     (subset_inter hIX' (hIY'.trans hY.subset)) (inter_subset_inter_left _ hX.subset)
--   have h_inter_left : IY' ∩ X = I := Eq.symm <| hI.eq_of_subset_indep (hY.indep.inter_right X)
--     (subset_inter hIY' (hIX'.trans hX.subset)) (by grw [inter_comm, hY.subset])
--   refine ⟨I, IX' \ I, IY' \ I, I₁' \ I, hI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
--   · simpa [union_eq_self_of_subset_left hIX']
--   · simpa [union_eq_self_of_subset_left hIY']
--   · rw [isBasis'_iff_isBasis_closure, ← closure_union_congr_left hX.closure_eq_closure,
--       ← closure_union_congr_right hY.closure_eq_closure, union_comm, diff_union_of_subset,
--       and_iff_right hI₁'.isBasis_closure_right]
--     · grw [hI₁'.subset, hX.subset, hY.subset]
--     grw [hIX', hss]
--   · exact diff_subset.trans hX.subset
--   · rw [← h_inter_right, diff_self_inter]
--     exact disjoint_sdiff_left
--   · exact diff_subset.trans hY.subset
--   · rw [← h_inter_left, diff_self_inter]
--     exact disjoint_sdiff_left
--   · grw [hss]
--   grw [hI₁'.subset, union_diff_distrib]

lemma IsBasisDuo.eLocalConn_project_eq (h : M.IsBasisDuo I J X Y) :
    (M.project (X ∩ Y)).eLocalConn X Y = M.nullity (I ∪ J) := by
  rw [h.isBasis'_diff_project_left.eLocalConn_eq h.isBasis'_diff_project_right,
    disjoint_sdiff_sdiff.inter_eq, encard_empty, zero_add, h.isBasis'_inter.project_eq_project,
    h.indep_inter.nullity_project_of_disjoint (by tauto_set)]
  convert rfl using 2
  tauto_set

-- lemma bar (M : Matroid α) (X₁ X₂ Y₁ Y₂ : Set α) (hdjX : Disjoint X₁ X₂) (hdjY : Disjoint Y₁ Y₂)
--     -- (hcl1 : M.closure (A ∪ B) = M.closure (C ∪ D))
--     (hcl1 : M.closure (X₁ ∪ Y₁ ∪ (X₂ ∩ Y₂)) = M.closure (X₁ ∪ X₂))
--     (hcl2 : M.closure ((X₁ ∩ Y₁) ∪ X₂ ∪ Y₂) = M.closure (Y₁ ∪ Y₂)) :
--     M.nullity (X₁ ∪ X₂) + M.nullity (Y₁ ∪ Y₂) = M.nullity (X₁ ∪ Y₁ ∪ (X₂ ∩ Y₂)) +
--       M.nullity ((X₁ ∩ Y₁) ∪ X₂ ∪ Y₂) := by
--   wlog hdj₁ : Disjoint X₁ Y₁ with aux
--   · specialize aux (M.project (X₁ ∩ Y₁)) (X₁ \ Y₁) X₂ (Y₁ \ X₁) Y₂ (hdjX.mono_left diff_subset)
--       (hdjY.mono_left diff_subset)
--     rw [disjoint_sdiff_sdiff.inter_eq, empty_union, imp_iff_right disjoint_sdiff_sdiff,
--       project_closure, union_right_comm, union_right_comm (s₃ := X₁ ∩ _), diff_union_inter,
--       union_diff_self, union_comm _ X₂, project_closure, union_assoc X₂, diff_union_inter,
--       union_comm X₂, imp_iff_right hcl1, project_closure, union_comm, ← union_assoc,
--       hcl2, union_comm (_ \ _), project_closure, union_assoc, inter_comm, diff_union_inter,
--       --  ?_ ?_ disjoint_sdiff_sdiff
--       union_comm, imp_iff_right rfl, inter_comm, union_comm, union_comm Y₂] at aux
--     apply_fun (· + M.nullity (X₁ ∩ Y₁) + M.nullity (X₁ ∩ Y₁)) at aux
--     have comp {a b c : ℕ∞} : a + b + c + c = (a + c) + (b + c) := sorry
--     rw [comp, comp, nullity_project_of_disjoint _ (by tauto_set),
--       nullity_project_of_disjoint _ (by tauto_set), nullity_project_of_disjoint _ (by tauto_set),
--       nullity_project_of_disjoint _ (by tauto_set)] at aux
--     convert aux using 3
--     · rw [union_right_comm, diff_union_inter]
--     · rw [union_right_comm, inter_comm, diff_union_inter]
--     · rw [union_comm _ (X₁ ∩ _), ← union_assoc, ← union_assoc, inter_union_diff, union_diff_self]
--     rw [union_comm _ (_ ∩ _), union_assoc]
--   rw [hdj₁.inter_eq, empty_union] at hcl2 ⊢
--   have hdj₂ : Disjoint X₂ Y₂ := sorry
--   rw [hdj₂.inter_eq, union_empty] at hcl1 ⊢


      -- add_right_comm, add_assoc, add_assoc, ← add_assoc (b := M.nullity _),
      -- nullity_project_of_disjoint _ (by tauto_set), add_comm _ (M.nullity _), ← add_assoc,
      -- nullity_project_of_disjoint _ (by tauto_set), add_right_comm, add_assoc, add_assoc] at aux
    -- · simp_rw [project_closure]
    --   -- `tauto_set` failure below. Minimize?
    --   rw [eq_comm, union_right_comm, diff_union_inter, ← hcl1, eq_comm,
    --     union_assoc, union_assoc, union_comm, union_assoc, union_assoc, inter_union_diff,
    --     ← union_assoc, union_right_comm, diff_union_self, union_comm Y₁]
    -- · simp only [project_closure]
    --   rw [disjoint_sdiff_sdiff.inter_eq, empty_union, eq_comm, union_right_comm,
    --     inter_comm X₁, diff_union_inter, ← hcl2, union_assoc, union_comm, inter_comm]
    -- -- rw [project_nul]
    -- have hrw1 := M.nullity_project_of_disjoint (C := X₁ ∩ Y₁) (X := (X₁ \ Y₁) ∪ X₂) (by tauto_set)
    -- have hrw2 := M.nullity_project_of_disjoint (C := X₁ ∩ Y₁) (X := (Y₁ \ X₁) ∪ Y₂) (by tauto_set)
    -- rw [union_right_comm, diff_union_inter] at hrw1
    -- rw [union_right_comm, inter_comm X₁, diff_union_inter, inter_comm Y₁] at hrw2

    -- rw [← hrw1, ← hrw2, add_right_comm, ← add_assoc, aux, union_assoc (X₁ ∩ Y₁),
    --   union_comm (X₁ ∩ Y₁), ← M.nullity_project_of_disjoint (C := X₁ ∩ Y₁) (by tauto_set)]
    -- obtain ⟨I, hI⟩ := M.exists_isBasis' (X₁ ∩ Y₁)
    -- rw [hI.project_eq_project, hI.indep.nullity_project_of_disjoint] at aux




    -- convert rfl using 2

      -- convert rfl using 2


      --  union_assoc, union_assoc, union_comm (X₁ \ Y₁),
      --   union_assoc, union_assoc, inter_union_diff, ← union_assoc, union_right_comm,
      --   diff_union_self]






-- lemma foo (M : Matroid α) (X Y : Set α) : M.eConn X + M.eConn Y
-- = M.eConn (X ∪ Y) + M.eConn (X ∩ Y)
--       + (M.project (X ∩ Y)).eLocalConn X Y
--       + (M.project ((M.E \ X) ∩ (M.E \ Y))).eLocalConn (M.E \ X) (M.E \ Y) := by

--   obtain ⟨IX, IY, I₁, hI, hI₁, hssI₁, hI₁b⟩ := M.exists_isBasisDuo_union X Y
--   obtain ⟨JX, JY, J₁, hJ, hJ₁, hssJ₁, hJ₁b⟩ := M.exists_isBasisDuo_union (M.E \ X) (M.E \ Y)

--   have hdjX : Disjoint IX JX := disjoint_sdiff_right.mono hI.subset_left hJ.subset_left
--   have hdjY : Disjoint IY JY := disjoint_sdiff_right.mono hI.subset_right hJ.subset_right
--   -- have aux {A B I J : Set α} (h : M.IsBasisDuo I J A B) :
--       -- M.project (X ∩ Y).eC
--   -- have hrwX : IX ∪ JX = (IX ∩ IY)
--   rw [hI.isBasis'_left.eConn_eq hJ.isBasis'_left, hI.isBasis'_right.eConn_eq hJ.isBasis'_right,
--     hI₁.isBasis'_right.eConn_eq (diff_inter_diff ▸ hJ.isBasis'_inter),
--     hI.isBasis'_inter.eConn_eq (diff_inter ▸ hJ₁.isBasis'_right),
--     hI.eLocalConn_project_eq, hJ.eLocalConn_project_eq,
--     hI₁b.nullity_eq, hJ₁b.nullity_eq]
--   have h_eqIJ := M.nullity_union_eq_nullity_add_encard_diff (X := I₁ ∪ (JX ∩ JY)) (Y := IX ∪ IY)
--      (hI₁b.subset_closure.trans (M.closure_mono subset_union_left))
--   have h_eqJI := M.nullity_union_eq_nullity_add_encard_diff (X := J₁ ∪ (IX ∩ IY)) (Y := JX ∪ JY)
--      (hJ₁b.subset_closure.trans (M.closure_mono subset_union_left))
--   rw [← diff_diff, Disjoint.sdiff_eq_left (by tauto_set), union_right_comm,
--     union_eq_self_of_subset_left hI₁b.subset] at h_eqIJ
--   rw [← diff_diff, Disjoint.sdiff_eq_left (by tauto_set), union_right_comm,
--     union_eq_self_of_subset_left hJ₁b.subset] at h_eqJI

--   rw [add_assoc, add_right_comm, ← add_assoc, ← h_eqIJ, add_right_comm, add_assoc, union_comm _ J₁,
--     ← h_eqJI]

--   -- have aux : M.nullity (IX ∪ JX) =
--   --     (M.project ((IX ∩ IY) ∪ (JX ∩ JY))).nullity (IX \ IY ∪ (JX \ JY)) := by
--   --   rw [project_nu]
--   --   -- nth_rw 1 [← inter_union_diff IX IY, ]

--   -- nth_rw 1 [← inter_union_diff IX IY, union_assoc,
--   --     ← (hI.indep_left.inter_right _).nullity_project_of_disjoint (by tauto_set),
--   --     ← inter_union_diff JX JY]
--     --   ← diff_union_inter JX JY,
--     -- ← hI.indep_left.nullity_project_of_disjoint hdjX,
--     -- ← hI.indep_right.nullity_project_of_disjoint hdjY,
--     -- nullity_project_congr (Y := IY)]

--   --   hI.isBasis'_diff_project_left.eLocalConn_eq hI.isBasis'_diff_project_right,
--   --   hJ.isBasis'_diff_project_left.eLocalConn_eq hJ.isBasis'_diff_project_right,
--   --   hI.isBasis'_inter.project_eq_project, hJ.isBasis'_inter.project_eq_project,
--   --   hI.indep_inter.nullity_project_of_disjoint (by tauto_set),
--   --   ← union_assoc, inter_union_diff, union_diff_self,
--   --   hJ.indep_inter.nullity_project_of_disjoint (by tauto_set),
--   --   ← union_assoc, inter_union_diff, union_diff_self]
--   -- simp only [disjoint_sdiff_sdiff.inter_eq, encard_empty, zero_add]
--   -- have := hI₁.isBasis'_right

--     -- hI.isBasis'_left.eLocalConn_eq_of_disjoint hJ.isBasis'_left disjoint_sdiff_right]
--   -- obtain ⟨JX, JY, hJ⟩ := M.exists_isBasisDuo (M.E \ X) (M.E \ Y)
--   -- have := hI.isBasis'_left.exists_isBasisDuo (Y := IX ∪ IY) subset_union_left
--   -- obtain ⟨I₁, hI₁, hII₁⟩ := hI.isBasis'_left.exists_isBasisDuo (Y := IX ∪ IY) subset_union_left
--   -- replace hI₁ : M.IsBasisDuo IX I₁ X (X ∪ Y) :=
--   --   hI₁.superset_right' hII₁ (by grw [hI₁.subset_right, hI.subset_left, hI.subset_right])
--   --   (by grw [inter_ground_subset_closure,
--   --     ← closure_union_congr_left hI.isBasis'_left.closure_eq_closure,
--   --     ← closure_union_congr_right hI.isBasis'_right.closure_eq_closure])

--     -- (by grw [← closure_union_congr_left hI.isBasis'_left.closure_eq_closure])
--   -- have := (hI₁.mono_left rfl.subset hI₁.subset_left).superset_right' (Z := X ∪ Y) subset_union_left
--   --   (by grw [hI₁.subset_right, hI.subset_left, hI.subset_right])

--   -- have := hI₁.superset_right' (Z := IX ∪ IY)
--   -- have := hI₁.superset_right' (Z := X ∪ Y)
--   -- have := hI.isBasisDuo_inter_left.exists_extend_left (Z := X ∪ IY)
--   -- have := hI.isBasisDuo_inter_left.exists_extend_right (Z := X ∪ IY)
--   --   (by grw [inter_subset_left, inter_subset_left]) subset_union_left
--   -- obtain ⟨I₁, hI₁, hI₁ss⟩ := hI.isBasis'_left.exists_isBasisDuo (Y := X ∪ IY) subset_union_left
--   -- have := hI.indep_left.exists_isBasisDuo hI.subset_left (Y := X ∪ Y)
--   --   (by grw [hI.subset_left, ← subset_union_left])
-- --   obtain ⟨P⟩ := M.nonempty_basisDuo X Y
-- --   obtain ⟨Q⟩ := M.nonempty_basisDuo X Y
--   -- obtain ⟨I, IX, IY, I₁, hI, hIX, hIY, hI₁, -, hIXY, hIYY, hIYX, hIXI₁, hI₁ss⟩ := M.bar1 X Y
--   -- obtain ⟨J, JX, JY, J₁, hJ, hJX, hJY, hJ₁, -, hJXY, hJYY, hJYX, hJXJ₁, hJ₁ss⟩ :=
--   --   M.bar1 (M.E \ X) (M.E \ Y)
--   -- rw [hI.project_eq_project, hJ.project_eq_project]
--   -- rw [diff_inter_diff] at hJ
--   -- rw [← diff_inter] at hJ₁
--   -- rw [hIX.eConn_eq hJX, hIY.eConn_eq hJY, hI₁.eConn_eq hJ, hI.eConn_eq hJ₁]




--   -- wlog hM : OnUniv M with aux
--   -- · specialize aux (M ↾ univ) X Y (by infer_instance)
--   --   simp only [eConn_restrict_univ_eq, project_restrict_univ, eLocalConn_restrict_eq, inter_univ,
--   --     ground_eq_univ] at aux
--   --   rw [← project_inter_ground (C := _ ∪ _),
--   --     ← (M.project ((_ ∪ _) ∩ _)).eLocalConn_inter_ground] at aux
--   --   convert aux using 3
--   --   all_goals congr; tauto_set
--   -- rw [ground_eq_univ, ← compl_eq_univ_diff, ← compl_eq_univ_diff]
--   -- obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ Y)
--   -- obtain ⟨J, hJ⟩ := M.exists_isBasis (Xᶜ ∩ Yᶜ)
--   -- obtain ⟨IX, hIX⟩ := (M.project I).exists_isBasis X
--   -- obtain ⟨IY, hIY⟩ := (M.project I).exists_isBasis Y
--   -- obtain ⟨JX, hJX⟩ := (M.project J).exists_isBasis Xᶜ
--   -- obtain ⟨JY, hJY⟩ := (M.project J).exists_isBasis Yᶜ
--   -- obtain ⟨I₁, hI₁⟩ := (M.project I).exists_isBasis (IX ∪ IY)
--   -- have hI₁' : M.IsBasis (I ∪ I₁) (X ∪ Y) := by
--   --   have := hI.indep.project_isBasis_iff (J := I₁) (X := X ∪ Y)
--   --   rw [hI.indep.project_isBasis_iff, union_union_distrib_left] at hI₁

--   -- rw [hI.indep.project_isBasis_iff] at hIX hIY
--   -- rw [hJ.indep.project_isBasis_iff] at hJX hJY
--   -- rw [union_eq_self_of_subset_left (hI.subset.trans inter_subset_left)] at hIX
--   -- rw [union_eq_self_of_subset_left (hI.subset.trans inter_subset_right)] at hIY
--   -- rw [union_eq_self_of_subset_left (hJ.subset.trans inter_subset_left)] at hJX
--   -- rw [union_eq_self_of_subset_left (hJ.subset.trans inter_subset_right)] at hJY



--   -- have := hI₁.indep.isBasis_of_subset_of_subset_closure (union_subset_union )


--     --   ground_eq_univ]
--       -- ← (M.project (_ ∪ _)).eLocalConn_inter_ground] at aux
--     -- convert aux using 2
--     -- rw [eq_comm, ← eLocalConn_inter_ground, ← project_inter_ground]




--     -- convert aux (M ↾ univ) X Y (by simp) using 2
--     -- · simp
--     -- · simp

--     -- simp only [eConn_restrict_univ_eq, project_restrict_univ, eLocalConn_restrict_eq, inter_univ,
--     --   ground_eq_univ]
--     -- convert rfl







-- -- lemma foo (M : Matroid α) [OnUniv M] (X Y : Set α) :
-- --     M.eConn (X ∪ Y) + M.eConn (X ∩ Y) ≤ M.eConn X + M.eConn Y := by
-- --   obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ Y)


-- -- private lemma eConn_submod_aux' (M : Matroid α) [OnUniv M] (X : Bool × Bool → Set α)
-- --     (hX : Pairwise (Disjoint on X)) (hu : ⋃ b, X b = univ) :
-- --     M.eConn (X ⟨false, false⟩) + M.eConn (X ⟨true, true⟩) ≤
-- --     M.eConn (X ⟨false, false⟩ ∪ X ⟨false, true⟩) + M.eConn (X ⟨true, true⟩
-- -- ∪ X ⟨true, false⟩) := by
-- --   have hcompl : ∀ b, (X ⟨!b, !b⟩)ᶜ = X ⟨b, b⟩ ∪ X ⟨b, !b⟩ ∪ X ⟨!b, b⟩ := sorry
-- --   set Y := fun b ↦ X ⟨b,b⟩ ∪ X ⟨b, !b⟩
-- --   have hYdj (b) : Disjoint (Y b) (Y !b) := sorry
-- --   have
-- --   change _ ≤ M.eConn (Y false) + M.eConn (Y true)

-- --   choose I hI using fun b ↦ M.exists_isBasis (X ⟨b, b⟩)
-- --   obtain ⟨J, hJ⟩ := M.exists_isBasis (I true ∪ I false)
-- --   obtain ⟨B, hB, hJB⟩ := hJ.exists_isBase
-- --   -- set Bs := fun b : Bool × Bool ↦ (B ∩ X b) with hBs
-- --   set K := B ∩ (X ⟨true, false⟩ ∪ X ⟨false, true⟩) with hK
-- --   have h_ind (b) : M.Indep (I b ∪ K) := sorry
-- --   have hss (b) : I b ∪ K ⊆ (X ⟨!b, !b⟩)ᶜ := by
-- --     rw [hcompl, union_assoc]
-- --     exact union_subset_union (hI b).subset (inter_subset_right.trans (by cases b <;> simp))
-- --   choose L hL using fun b ↦ (h_ind b).subset_isBasis_of_subset (hss b)

-- --   rw [(hI true).eConn_eq' (by simpa using (hL false).1),
-- --     (hI false).eConn_eq' (by simpa using (hL true).1)]


-- --   have hbound (b) : M.nullity (L b ∩ Y b ∪ (L !b) ∩ Y !b) ≤ M.eConn (Y b) :=
-- --     ((hL b).1.indep.inter_right _).nullity_union_le_eConn ((hL !b).1.indep.inter_right _)
-- --       inter_subset_right ((hYdj b).symm.mono_left inter_subset_right)

-- --   have hss1 (b) : B ∩ Y b ⊆ I b ∪ K := sorry
-- --   have hss2 (b) : B ∩ Y b ⊆ L b ∩ Y b :=
-- -- subset_inter ((hss1 b).trans (hL b).2) inter_subset_right
-- --   have hss2 (b) : B ⊆ I (!b) ∪ L b := by
-- --     refine

-- --   refine le_trans ?_ (add_le_add (hbound false) (hbound true))
-- --   refine le_trans (add_le_add (M.nullity_le_of_subset (subset_union_right (s := B)))
-- --     (M.nullity_le_of_subset (subset_union_right (s := B)))) ?_

-- --   rw [nullity_union_eq_nullity_add_encard_diff (by simp [hB.closure_eq]),
-- --     nullity_union_eq_nullity_add_encard_diff (by simp [hB.closure_eq]), hB.indep.nullity_eq,
-- --     zero_add, zero_add]

--   -- have := ((hL b).1.indep.inter_right (Y b)).nullity_union_le_eConn
--   --  ((hL b).1.indep.inter_right (Y b)) inter_subset_left
--   -- have := Indep.eConn_eq_eLocalConn'

--   -- have hBss (b) : B ⊆ I b ∪ L !b := by
--   --   _
--   -- rw [← eConn_compl', add_comm, ← eConn_compl', add_comm]

--     -- rw [subset_compl_iff_disjoint_right, disjoint_union_left, hK, disjoint_union_left]
--     -- refine ⟨Disjoint.mono_left (hI b).subset (hX (by simp)), ?_, ?_⟩
--     -- · specialize hX (show ⟨true, false⟩ ≠ ⟨!b, !b⟩ by cases b <;> decide)
--     --   exact Disjoint.mono_left inter_subset_right hX
--     -- specialize hX (show ⟨false, true⟩ ≠ ⟨!b, !b⟩ by cases b <;> decide)
--     -- exact Disjoint.mono_left inter_subset_right hX


--     -- refine union_subset ((hI b).subset.trans ?_) <|
--     --   union_subset (inter_subset_right.trans ?_) (inter_subset_right.trans ?_)




-- -- private lemma eConn_submod_aux (M : Matroid α) [OnUniv M] (X : Bool → Bool → Set α)
-- --     (hb : ∀ b b', X b (!b') = (X b b')ᶜ) :
-- --     M.eConn (X true true ∪ X false true) + M.eConn (X true false ∪ X false false)
-- --     ≤ M.eConn (X true true) + M.eConn (X false false) := by
--   -- Let `I₀` and `I₁` be bases for `X ∩ Y` and `Xᶜ ∩ Yᶜ` respectively.
--   -- choose I hI using fun b ↦ M.exists_isBasis (X true b ∩ X false b)
--   -- have hI' : ∀ b : Bool, M.IsBasis (I !b) (M.E \ (X true b ∪ X false b)) := by
--   --   refine fun b ↦ ?_
--   --   rw [OnUniv.ground_diff_eq, compl_union, ← hb, ← hb]
--   --   exact hI !b
--   -- -- Let `J` be a isBasis for `I₀ ∪ I₁`, and `B` be a base containing `J`.
--   -- obtain ⟨J, hJ⟩ := M.exists_isBasis (I true ∪ I false) <| OnUniv.subset_ground ..
--   -- obtain ⟨B, hB, hJ_eq⟩ := hJ.exists_isBase
--   -- -- Let `K₀` and `K₁` be the intersections of `B` with `(X \ Y)` and `(Y \ X)` respectively.
--   -- set K := B ∩ ((X true false ∩ X false true) ∪ (X false true ∩ X true )
--   -- set K := fun b ↦ B ∩ X true b ∩ X false !b with hK
--   -- -- Claim that `I₀ ∪ K₀ ∪ K₁` and `I₁ ∪ K₀ ∪ K₁` are both independent.
--   -- have h_ind_IK (b) : M.Indep (I b ∪ K)
--   -- · sorry
--   -- have hss (b) : I b ∪ K true ∪ K false ⊆ X true b ∪ X false b := by
--   --   have := (hI b).subset
--   --   cases b <;>
--   --   · simp only [Bool.not_true, Bool.not_false, K]
--   --     tauto_set
--   -- choose L hL using fun b ↦ (h_ind_IK b).subset_isBasis_of_subset (hss b) <|
--   --OnUniv.subset_ground ..


--   -- rw [(hL true).1.eConn_eq (hI' true), (hL false).1.eConn_eq (hI' _)]

--   -- have hBss (b : Bool) : B ⊆ L b ∪ I (!b) := by
--   --   rw [← diff_union_inter B (X b true)]
--   --   refine union_subset_union (subset_trans ?_ (hL b).2) ?_
--   --   ·
--   --     rw [diff_eq_compl_inter, ← hb, hK]
--   --     simp
--   -- -- ← compl_compl (X true), flip_X, ← compl_compl (Y true),
--   --   flip_Y, ← compl_union, ← eConn_compl', compl_compl, (hL !true).1.eConn_eq (hI' _),
--   --   Bool.not_true]

-- --   sorry

-- -- lemma eConn_submod (M : Matroid α) (X Y : Set α) :
-- --     M.eConn (X ∪ Y) + M.eConn (X ∩ Y) ≤ M.eConn X + M.eConn Y := by
-- --   wlog h_univ : OnUniv M with aux
-- --   · simp_rw [← M.eConn_restrict_univ_eq]
-- --     exact aux _ _ _ (by infer_instance)
-- --   simpa using M.eConn_submod_aux (cond · X Xᶜ) (cond · Y Yᶜ)
