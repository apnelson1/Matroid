import Matroid.Minor.Rank
import Matroid.ForMathlib.SetPartition
import Matroid.ForMathlib.Minimal
import Matroid.ForMathlib.BooleanAlgebra

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid

section Spanning

lemma Flat.eq_ground_of_spanning (hF : M.Flat F) (h : M.Spanning F) : F = M.E := by
  rw [← hF.closure, h.closure_eq]

lemma Flat.spanning_iff (hF : M.Flat F) : M.Spanning F ↔ F = M.E :=
  ⟨hF.eq_ground_of_spanning, by rintro rfl; exact M.ground_spanning⟩

lemma Flat.inter (hF₁ : M.Flat F₁) (hF₂ : M.Flat F₂) : M.Flat (F₁ ∩ F₂) := by
  rw [inter_eq_iInter]; apply Flat.iInter; simp [hF₁, hF₂]

end Spanning

/-- The intersection of an arbitrary collection of flats with the ground set is a flat.
`Matroid.Flat.iInter` is often more convenient, but this works when the collection is empty. -/
lemma Flat.iInter_inter_ground {ι : Type*} {Fs : ι → Set α} (hFs : ∀ i, M.Flat (Fs i)) :
    M.Flat ((⋂ i, Fs i) ∩ M.E) := by
  obtain (hι | hι) := isEmpty_or_nonempty ι
  · simp
  exact (Flat.iInter hFs).inter M.ground_flat

lemma Flat.biInter {ι : Type*} {Fs : ι → Set α} {s : Set ι} (hs : s.Nonempty)
    (hFs : ∀ i ∈ s, M.Flat (Fs i)) : M.Flat (⋂ i ∈ s, Fs i) := by
  rw [biInter_eq_iInter]
  have := hs.to_subtype
  apply Flat.iInter (by simpa)

lemma Flat.biInter_inter_ground {ι : Type*} {Fs : ι → Set α} {s : Set ι}
    (hFs : ∀ i ∈ s, M.Flat (Fs i)) : M.Flat ((⋂ i ∈ s, Fs i) ∩ M.E) := by
  rw [biInter_eq_iInter]
  exact Flat.iInter_inter_ground (by simpa)

lemma Flat.sInter {Fs : Set (Set α)} (hF : Fs.Nonempty) (h : ∀ F ∈ Fs, M.Flat F) :
    M.Flat (⋂₀ Fs) := by
  rw [sInter_eq_iInter]
  have : Nonempty Fs := Iff.mpr nonempty_coe_sort hF
  exact Flat.iInter (fun ⟨F, hF⟩ ↦ h _ hF)

lemma Flat.sInter_inter_ground {Fs : Set (Set α)} (h : ∀ F ∈ Fs, M.Flat F) :
    M.Flat (⋂₀ Fs ∩ M.E) := by
  rw [sInter_eq_iInter]
  exact Flat.iInter_inter_ground (by simpa)

@[simp] lemma closure_flat (M : Matroid α) (X : Set α) : M.Flat (M.closure X) :=
  Flat.sInter ⟨M.E, M.ground_flat, inter_subset_right⟩ fun _ ↦ And.left

lemma flat_iff_closure_self : M.Flat F ↔ M.closure F = F :=
  ⟨fun h ↦ subset_antisymm (sInter_subset_of_mem ⟨h, inter_subset_left⟩)
    (M.subset_closure F (Flat.subset_ground h)), fun h ↦ by rw [← h]; exact closure_flat _ _⟩

lemma flat_iff_subset_closure_self (hF : F ⊆ M.E := by aesop_mat) : M.Flat F ↔ M.closure F ⊆ F := by
  rw [flat_iff_closure_self, subset_antisymm_iff, and_iff_left_iff_imp]
  exact fun _ ↦ M.subset_closure F

lemma exists_mem_closure_not_mem_of_not_flat (h : ¬ M.Flat F) (hF : F ⊆ M.E := by aesop_mat) :
    ∃ e, e ∈ M.closure F \ F := by
  rw [flat_iff_closure_self, subset_antisymm_iff, and_iff_left (M.subset_closure F)] at h
  exact not_subset.1 h

lemma flat_iff_ssubset_closure_insert_forall (hF : F ⊆ M.E := by aesop_mat) :
    M.Flat F ↔ ∀ e ∈ M.E \ F, M.closure F ⊂ M.closure (insert e F) := by
  refine ⟨fun h e he ↦ (M.closure_subset_closure (subset_insert _ _)).ssubset_of_ne ?_, fun h ↦ ?_⟩
  · rw [h.closure]
    exact fun h' ↦ mt ((Set.ext_iff.mp h') e).mpr (not_mem_of_mem_diff he)
      ((M.subset_closure _ (insert_subset he.1 hF)) (mem_insert _ _))
  rw [flat_iff_closure_self]
  by_contra h'
  obtain ⟨e, he', heF⟩ := exists_of_ssubset
    (ssubset_of_ne_of_subset (Ne.symm h') (M.subset_closure F))
  have h'' := h e ⟨(M.closure_subset_ground F) he', heF⟩
  rw [← M.closure_insert_closure_eq_closure_insert e F, insert_eq_of_mem he',
    M.closure_closure] at h''
  exact h''.ne rfl

lemma flat_iff_forall_circuit (hF : F ⊆ M.E := by aesop_mat) :
    M.Flat F ↔ ∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F := by
  rw [flat_iff_closure_self]
  refine ⟨fun h C e hC heC hCF ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    refine (M.closure_subset_closure ?_) (hC.subset_closure_diff_singleton e heC)
    rwa [diff_subset_iff, singleton_union]
  refine (M.subset_closure F hF).antisymm' (fun e heF ↦ by_contra fun he' ↦ ?_)
  obtain ⟨C, hCF, hC, heC⟩ := (mem_closure_iff_exists_circuit he').mp heF
  exact he' (h C e hC heC hCF)

lemma flat_iff_forall_circuit' :
    M.Flat F ↔ (∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F) ∧ F ⊆ M.E :=
  ⟨fun h ↦ ⟨(flat_iff_forall_circuit h.subset_ground).mp h, h.subset_ground⟩, fun h ↦
    (flat_iff_forall_circuit h.2).mpr h.1⟩

lemma Flat.closure_exchange (hF : M.Flat F) (he : e ∈ M.closure (insert f F) \ F) :
    f ∈ M.closure (insert e F) \ F := by
  nth_rw 2 [← hF.closure] at *; exact Matroid.closure_exchange he

lemma Flat.closure_insert_eq_closure_insert_of_mem (hF : M.Flat F)
    (he : e ∈ M.closure (insert f F) \ F) : M.closure (insert e F) = M.closure (insert f F) :=
  Matroid.closure_insert_congr (by rwa [hF.closure])

lemma Flat.insert_indep_of_basis (hF : M.Flat F) (hIF : M.Basis I F) (heI : e ∈ M.E \ F) :
    M.Indep (insert e I) := by
  rwa [hIF.indep.insert_indep_iff_of_not_mem, hIF.closure_eq_closure, hF.closure]
  exact not_mem_subset hIF.subset heI.2

lemma Flat.closure_subset_of_subset (hF : M.Flat F) (h : X ⊆ F) : M.closure X ⊆ F := by
  have h' := M.closure_mono h; rwa [hF.closure] at h'

@[simp] lemma Flat.closure_subset_iff_subset (hF : M.Flat F) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X ⊆ F ↔ X ⊆ F :=
  ⟨(M.subset_closure X).trans, hF.closure_subset_of_subset⟩

lemma Flat.closure_eq_iff_basis_of_indep (hF : M.Flat F) (hI : M.Indep I) :
    M.closure I = F ↔ M.Basis I F :=
  ⟨by rintro rfl; exact hI.basis_closure, fun h ↦ by rw [h.closure_eq_closure, hF.closure]⟩

lemma Flat.eq_closure_of_basis (hF : M.Flat F) (hI : M.Basis I F) : F = M.closure I :=
  hI.subset_closure.antisymm (hF.closure_subset_of_subset hI.subset)

lemma Flat.eRk_insert_eq_add_one (hF : M.Flat F) (he : e ∈ M.E \ F) :
    M.eRk (insert e F) = M.eRk F + 1 := by
  rw [Matroid.eRk_insert_eq_add_one]
  rwa [hF.closure]

lemma Flat.rk_insert_eq_add_one (hF : M.Flat F) (hfin : M.FinRk F) (he : e ∈ M.E \ F) :
    M.rk (insert e F) = M.rk F + 1 := by
  rw [← Nat.cast_inj (R := ℕ∞), (hfin.insert _).cast_rk_eq, hF.eRk_insert_eq_add_one he,
    Nat.cast_add, hfin.cast_rk_eq, Nat.cast_one]

lemma Flat.rk_lt_of_superset (hF : M.Flat F) (hFX : F ⊂ X) (hfin : M.FinRk X)
    (hX : X ⊆ M.E := by aesop_mat) : M.rk F < M.rk X := by
  obtain ⟨e, heX, heF⟩ := exists_of_ssubset hFX
  rw [Nat.lt_iff_add_one_le, ← hF.rk_insert_eq_add_one (hfin.subset hFX.subset) ⟨hX heX, heF⟩]
  exact hfin.rk_le_of_subset (insert_subset heX hFX.subset)

lemma Flat.subset_of_eRelRk_eq_zero (hF : M.Flat F) (hr : M.eRelRk F X = 0)
    (hX : X ⊆ M.E := by aesop_mat) : X ⊆ F := by
  rwa [eRelRk_eq_zero_iff, hF.closure] at hr

lemma Flat.one_le_eRelRk_of_ssubset (hF : M.Flat F) (hss : F ⊂ X)
    (hX : X ⊆ M.E := by aesop_mat) : 1 ≤ M.eRelRk F X :=
  ENat.one_le_iff_ne_zero.2 (fun h_eq ↦ hss.not_subset <| hF.subset_of_eRelRk_eq_zero h_eq)

lemma exists_insert_rk_eq_of_not_flat (hFE : F ⊆ M.E) (hnF : ¬ M.Flat F) :
    ∃ e ∈ M.E \ F, M.rk (insert e F) = M.rk F := by
  obtain ⟨e, hecl, heF⟩ := exists_mem_closure_not_mem_of_not_flat hnF
  refine ⟨e, ⟨mem_ground_of_mem_closure hecl, heF⟩, ?_⟩
  rw [← rk_closure_eq, ← closure_insert_closure_eq_closure_insert]
  simp [hecl]

lemma Flat.insert_rk_eq [M.FiniteRk] (hF : M.Flat F) (he : e ∈ M.E \ F) :
    M.rk (insert e F) = M.rk F + 1 := by
  rw [rk, hF.eRk_insert_eq_add_one he, ENat.toNat_add (by simp [M.to_finRk]) (by simp), rk,
    ENat.toNat_one]

lemma Flat.eq_of_subset_of_rk_ge [FiniteRk M] (hF : M.Flat F) (hFF' : F ⊆ F') (hle : M.rk F' ≤ M.rk F)
    (hF' : F' ⊆ M.E := by aesop_mat) : F = F' := by
  refine hFF'.antisymm fun e heF' ↦ by_contra fun heF ↦ ?_
  linarith [(hF.insert_rk_eq ⟨by aesop_mat, heF⟩).symm.trans_le (M.rk_mono (insert_subset heF' hFF'))]

lemma finite_setOf_flat (M : Matroid α) [M.Finite] : {F | M.Flat F}.Finite :=
  M.ground_finite.finite_subsets.subset (fun _ hF ↦ hF.subset_ground)

lemma uniqueBaseOn_flat_iff {I E : Set α} (hIE : I ⊆ E) : (uniqueBaseOn E I).Flat F ↔ F ⊆ I := by
  simp [flat_iff_closure_self, diff_eq_empty.2 hIE, inter_assoc, inter_eq_self_of_subset_right hIE]

@[simp] lemma loopyOn_flat_iff {E : Set α} : (loopyOn E).Flat F ↔ F = E := by
  simp [flat_iff_closure_self, eq_comm]

@[simp] lemma emptyOn_flat_iff : (emptyOn α).Flat F ↔ F = ∅ := by
  simp [← loopyOn_empty]

@[simp] lemma freeOn_flat_iff {E : Set α} : (freeOn E).Flat F ↔ F ⊆ E := by
  simp [← uniqueBaseOn_self, uniqueBaseOn_flat_iff Subset.rfl]


lemma flat_map_iff {β : Type*} {f : α → β} (hf : M.E.InjOn f) {F : Set β} :
    (M.map f hf).Flat F ↔ ∃ F₀, M.Flat F₀ ∧ F = f '' F₀ := by
  simp only [flat_iff_closure_self, map_closure_eq]
  refine ⟨fun h ↦ ⟨M.closure (f ⁻¹' F), by simp, h.symm⟩, ?_⟩
  rintro ⟨F, hF, rfl⟩
  rw [← closure_inter_ground, hf.preimage_image_inter, hF]
  exact hF.symm.subset.trans <| M.closure_subset_ground _

lemma Flat.map {β : Type*} {f : α → β} (hF : M.Flat F) (hf : M.E.InjOn f) :
    (M.map f hf).Flat (f '' F) := by
  rw [flat_iff_closure_self, map_closure_eq, ← closure_inter_ground,
    hf.preimage_image_inter hF.subset_ground, hF.closure]

lemma Flat.comap {β : Type*} {F : Set β} {M : Matroid β} (hF : M.Flat F) (f : α → β) :
    (M.comap f).Flat (f ⁻¹' F) := by
  rw [flat_iff_closure_self, comap_closure_eq, subset_antisymm_iff]
  refine ⟨preimage_mono (hF.closure_subset_of_subset (by simp)), fun y (hy : f y ∈ F) ↦ ?_⟩
  exact mem_closure_of_mem' _ ⟨y, hy, rfl⟩ (hF.subset_ground hy)

lemma flat_comap_iff_exists {β : Type*} {f : α → β} {F : Set α} {M : Matroid β} :
    (M.comap f).Flat F ↔ ∃ F₀, M.Flat F₀ ∧ F = f ⁻¹' F₀ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [flat_iff_closure_self, comap_closure_eq] at h
    exact ⟨M.closure (f '' F), M.closure_flat _, h.symm⟩
  rintro ⟨F₀, hF₀, rfl⟩
  exact hF₀.comap f





  -- TODO : Cyclic flats.


/-
this needs `ENatTopology`
lemma Flat.ground_encard_eq_tsum (hF₀ : M.Flat F₀) :
    M.E.encard = F₀.encard + ∑' F : {F // F₀ ⋖[M] F}, ((F : Set α) \ F₀).encard := by
  rw [← encard_diff_add_encard_of_subset hF₀.subset_ground, add_comm]
  apply congr_arg (_ + ·)
  have hcard := ENat.tsum_encard_eq_encard_sUnion hF₀.covByPartition.pairwiseDisjoint
  simp only [SetLike.coe_sort_coe, Partition.sUnion_eq] at hcard
  rw [← ENat.tsum_comp_eq_tsum_of_equiv hF₀.equivCovByPartition (fun F ↦ encard ((F : Set α) \ F₀)),
    ← hcard]
  apply tsum_congr
  rintro ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩
  rw [hF₀.equivCovByPartition_apply_coe, diff_union_self, union_diff_right]
-/

section Minor

lemma flat_contract (X C : Set α) : (M ／ C).Flat (M.closure (X ∪ C) \ C) := by
  rw [flat_iff_closure_self, contract_closure_eq, diff_union_self,
    ← M.closure_union_closure_right_eq, union_eq_self_of_subset_right
    (M.closure_subset_closure subset_union_right), closure_closure]

@[simp] lemma flat_contract_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Flat F ↔ M.Flat (F ∪ C) ∧ Disjoint F C := by
  rw [flat_iff_closure_self, contract_closure_eq, subset_antisymm_iff, subset_diff, diff_subset_iff,
    union_comm C, ← and_assoc, and_congr_left_iff, flat_iff_closure_self, subset_antisymm_iff,
    and_congr_right_iff]
  exact fun _ _ ↦
    ⟨fun h ↦ M.subset_closure _ (union_subset (h.trans (M.closure_subset_ground _)) hC),
    fun h ↦ subset_union_left.trans h⟩

lemma Flat.union_flat_of_contract (hF : (M ／ C).Flat F) (hC : C ⊆ M.E := by aesop_mat) :
    M.Flat (F ∪ C) :=
  ((flat_contract_iff hC).1 hF).1

lemma flat_contract_iff' :
    (M ／ C).Flat F ↔ (M.Flat (F ∪ (C ∩ M.E)) ∧ Disjoint F (C ∩ M.E)) := by
  rw [← contract_inter_ground_eq, flat_contract_iff]

lemma Flat.union_flat_of_contract' (hF : (M ／ C).Flat F) : M.Flat (F ∪ M.closure C) := by
  replace hF := (flat_contract_iff'.1 hF).1.closure
  rw [← closure_union_closure_right_eq, closure_inter_ground] at hF
  rw [flat_iff_subset_closure_self (union_subset _ (M.closure_subset_ground _)), hF]
  · exact union_subset_union_right _ <| (M.subset_closure _).trans (M.closure_inter_ground _).subset
  exact subset_union_left.trans (hF.symm.subset.trans (M.closure_subset_ground _))

lemma Nonloop.contract_flat_iff (he : M.Nonloop e) :
    (M ／ e).Flat F ↔ M.Flat (insert e F) ∧ e ∉ F := by
  rw [contractElem, flat_contract_iff, union_singleton, disjoint_singleton_right]

/-- Flats of `M ／ C` are equivalent to flats of `M` containing `C`-/
@[simps] def flatContractEquiv (M : Matroid α) (C : Set α) (hC : C ⊆ M.E := by aesop_mat) :
    {F // (M ／ C).Flat F} ≃ {F // M.Flat F ∧ C ⊆ F} where
  toFun F := ⟨F ∪ C, by simp [subset_union_right, F.prop.union_flat_of_contract]⟩
  invFun F := ⟨F \ C, by simp
    [flat_contract_iff hC, union_eq_self_of_subset_right F.prop.2, disjoint_sdiff_left, F.prop.1]⟩
  left_inv := by rintro ⟨-, hF⟩; simp [(subset_diff.1 hF.subset_ground).2]
  right_inv := by rintro ⟨F, hF⟩; simp [hF.2]

lemma flat_restrict_iff {R : Set α} (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Flat F ↔ ∃ F', M.Flat F' ∧ F = F' ∩ R := by
  refine ⟨fun h ↦ ⟨M.closure F, M.closure_flat F, ?_⟩, ?_⟩
  · nth_rw 1 [← h.closure]
    have hFR : F ⊆ R := h.subset_ground
    simp [inter_eq_self_of_subset_left hFR, diff_subset, diff_eq_empty.2 hR]
  rintro ⟨F, hF, rfl⟩
  rw [flat_iff_subset_closure_self]
  suffices M.closure (F ∩ R) ∩ R ⊆ F by simpa [inter_assoc, diff_eq_empty.2 hR]
  exact inter_subset_left.trans (hF.closure_subset_of_subset inter_subset_left)

lemma flat_delete_iff {D : Set α} :
    (M ＼ D).Flat F ↔ ∃ F', M.Flat F' ∧ F = F' \ D := by
  simp_rw [delete_eq_restrict, flat_restrict_iff diff_subset, ← inter_diff_assoc]
  constructor <;>
  · rintro ⟨F, hF, rfl⟩
    refine ⟨F, hF, ?_⟩
    rw [inter_eq_self_of_subset_left hF.subset_ground]

lemma flat_delete_iff' {D : Set α} :
    (M ＼ D).Flat F ↔ M.closure F ⊆ F ∪ D ∧ Disjoint F D ∧ F ⊆ M.E := by
  obtain hE | hE := em' (F ⊆ M.E \ D)
  · rw [iff_false_intro (show ¬ (M ＼ D).Flat F from fun h ↦ hE h.subset_ground), false_iff,
      and_comm (a := Disjoint _ _), ← subset_diff]
    simp [hE]
  have hE' := subset_diff.1 hE
  rw [flat_iff_subset_closure_self, delete_closure_eq, diff_subset_iff, union_comm,
    hE'.2.sdiff_eq_left , and_iff_left hE'.symm]

lemma flat_restrict_iff' {R : Set α} :
    (M ↾ R).Flat F ↔ F = M.closure F ∩ R ∪ (R \ M.E) := by
  by_cases hFR : F ⊆ R
  · rw [flat_iff_closure_self, M.restrict_closure_eq', inter_eq_self_of_subset_left hFR, eq_comm]
  refine iff_of_false (fun h ↦ hFR h.subset_ground) fun h ↦ hFR ?_
  rw [h, union_subset_iff, and_iff_left diff_subset]
  exact inter_subset_right

lemma Flat.flat_restrict' (hF : M.Flat F) (R : Set α) : (M ↾ R).Flat ((F ∩ R) ∪ (R \ M.E)) := by
  rw [flat_restrict_iff', ← closure_inter_ground, union_inter_distrib_right,
    diff_inter_self, union_empty, closure_inter_ground]
  convert rfl using 2
  simp only [subset_antisymm_iff, subset_inter_iff, inter_subset_right, and_true]
  nth_rw 2 [← hF.closure]
  exact ⟨inter_subset_left.trans (M.closure_subset_closure (inter_subset_left)),
    M.subset_closure _ (inter_subset_left.trans hF.subset_ground)⟩

lemma Flat.flat_restrict (hF : M.Flat F) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Flat (F ∩ R) := by
  simpa [diff_eq_empty.2 hR] using hF.flat_restrict' R

lemma Flat.closure_subset_of_flat_restrict {R : Set α} (hF : (M ↾ R).Flat F) :
    M.closure F ⊆ F ∪ (M.E \ R) := by
  rw [flat_restrict_iff'] at hF
  nth_rw 2 [hF]
  rw [union_assoc, ← diff_subset_iff, diff_self_inter, diff_subset_iff, ← union_assoc,
    union_eq_self_of_subset_right diff_subset, union_diff_self]
  exact (M.closure_subset_ground F).trans subset_union_right

lemma Flat.exists_of_delete {D : Set α} (hF : (M ＼ D).Flat F) : ∃ F₀, M.Flat F₀ ∧ F = F₀ \ D :=
  flat_delete_iff.1 hF

lemma Flat.closure_subset_of_delete {D : Set α} (hF : (M ＼ D).Flat F) : M.closure F ⊆ F ∪ D :=
  (flat_delete_iff'.1 hF).1

@[simp] lemma flat_deleteElem_iff : (M ＼ e).Flat F ↔ e ∉ F ∧ (M.Flat F ∨ M.Flat (insert e F)) := by
  rw [deleteElem, flat_delete_iff]
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain (heF | heF) := em (e ∈ F) <;> simp [heF, hF]
  rintro ⟨heF, (hF | hF)⟩ <;> exact ⟨_, hF, by simp [heF]⟩

lemma Flat.contract_subset_flat (hF : M.Flat F) (hC : C ⊆ F) : (M ／ C).Flat (F \ C) := by
  rw [flat_iff_closure_self, contract_closure_eq, diff_union_of_subset hC, hF.closure]

end Minor

lemma ext_flat {M₁ M₂ : Matroid α} (hF : ∀ F, M₁.Flat F ↔ M₂.Flat F) : M₁ = M₂ :=
  ext_closure fun X ↦ by simp [closure, hF,
    ((hF _).1 M₁.ground_flat).subset_ground.antisymm ((hF _).2 M₂.ground_flat).subset_ground]

lemma ext_iff_flat {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ ∀ F, M₁.Flat F ↔ M₂.Flat F :=
  ⟨fun h ↦ by simp [h], ext_flat⟩

section Directed

/-- Any downwards-directed collection of flats containing a flat of finite rank
must contain its intersection. -/
lemma Flat.iInter_mem_of_directed_of_finRk {ι : Type*} {F : ι → Set α} (hF : ∀ i, M.Flat (F i))
    (h_dir : Directed (fun A B ↦ B ⊆ A) F) (h_fin : ∃ i, M.FinRk (F i)) : ∃ i₀, F i₀ = ⋂ i, F i := by
  obtain ⟨j, hj⟩ := h_fin
  have _ : Nonempty ι := ⟨j⟩
  have hmin := Finite.exists_minimal_wrt' (fun i ↦ M.rk (F j ∩ F i)) univ
  simp only [image_univ, univ_nonempty, mem_univ, forall_const, true_and, finite_iff_bddAbove]
    at hmin
  have hub : M.rk (F j) ∈ upperBounds (range fun i ↦ M.rk (F j ∩ F i))
  · rintro _ ⟨X, rfl⟩
    exact hj.rk_le_of_subset inter_subset_left

  obtain ⟨k₁, hk₁⟩ := hmin ⟨(M.rk (F j)), hub⟩
  obtain ⟨k, hkk₁ : _ ⊆ _, hkj : _ ⊆ _⟩ := h_dir k₁ j
  refine ⟨k, (iInter_subset _ _).antisymm' (subset_iInter fun i ↦ ?_)⟩

  by_contra hnss
  obtain ⟨i', hki' : _ ⊆ _, hii' : _ ⊆ _⟩ := h_dir k i
  have hss : F j ∩ F i' ⊂ F j ∩ F k₁
  · obtain ⟨e, hek, hei⟩ := not_subset.1 hnss
    refine (inter_subset_inter_right _ (hki'.trans hkk₁)).ssubset_of_ne fun h_eq ↦ hei ?_
    exact hii' (h_eq.symm.subset ⟨hkj hek, hkk₁ hek⟩).2

  have hlt := (((hF j).inter (hF i')).rk_lt_of_superset hss hj.inter_right
    (inter_subset_left.trans (hF j).subset_ground))

  exact hlt.ne <| (hk₁ _ hlt.le).symm

end Directed


-- section from_axioms
-- lemma matroid_of_flat_aux [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂)) (X : set α) :
--   flat (⋂₀ {F | flat F ∧ X ⊆ F}) ∧ ∀ F₀, flat F₀ → ((⋂₀ {F | flat F ∧ X ⊆ F}) ⊆ F₀ ↔ X ⊆ F₀) :=
-- begin
--   set F₁ := ⋂₀ {F | flat F ∧ X ⊆ F} with hF₁,
--   refine ⟨_, λ F₀ hF₀, ⟨λ hF₁F₀, _, λ hXF, _⟩⟩ ,
--   { obtain ⟨F',⟨hF',hYF'⟩,hmin⟩ := finite.exists_minimal (λ F, flat F ∧ X ⊆ F)
--       ⟨univ, univ_flat, subset_univ _⟩,
--     convert hF',
--     refine subset_antisymm (sInter_subset_of_mem ⟨hF',hYF'⟩) (subset_sInter _),
--     rintro F ⟨hF,hYF⟩,
--     rw hmin _ ⟨flat_inter _ _ hF hF', subset_inter hYF hYF'⟩ _,
--     { apply inter_subset_left},
--     apply inter_subset_right},
--   { refine subset_trans (subset_sInter (λ F h, _)) hF₁F₀, exact h.2},
--   apply sInter_subset_of_mem,
--   exact ⟨hF₀, hXF⟩,
-- end
-- /-- A collection of sets satisfying the flat axioms determines a matroid -/
-- def matroid_of_flat [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
--   ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :=
-- matroid_of_closure_of_finite (λ X, ⋂₀ {F | flat F ∧ X ⊆ F})
-- (λ X, subset_sInter (λ F, and.right))
-- (λ X Y hXY, subset_sInter (λ F hF, by {apply sInter_subset_of_mem,
-- exact ⟨hF.1, hXY.trans hF.2⟩}))
-- (begin
--   refine λ X, (subset_sInter (λ F, and.right)).antisymm' _,
--   simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
--   rintro F hF hXF,
--   apply sInter_subset_of_mem,
--   split, assumption,
--   apply sInter_subset_of_mem,
--   exact ⟨hF, hXF⟩,
-- end )
-- (begin
--   simp only [mem_diff, mem_sInter, mem_set_of_eq, and_imp, not_forall, exists_prop,
--     forall_exists_index],
--   refine λ X e f h F₀ hF₀ hXF₀ hfF₀, ⟨λ Ff hFf hfXf, _,
--     ⟨F₀, hF₀, hXF₀, λ heF₀, hfF₀ (h _ hF₀ (insert_subset.mpr ⟨heF₀,hXF₀⟩))⟩⟩,
--   obtain ⟨hFX, hX'⟩    := matroid_of_flat_aux flat univ_flat flat_inter X,
--   obtain ⟨hFXe, hXe'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert e X),
--   obtain ⟨hFXf, hXf'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert f X),
--   set FX := sInter {F | flat F ∧ X ⊆ F} with hFX_def,
--   set FXe := sInter {F | flat F ∧ insert e X ⊆ F} with hFXe_def,
--   set FXf := sInter {F | flat F ∧ insert f X ⊆ F} with hFXe_def,
--   apply (hXf' Ff hFf).mpr hfXf,
--   have heFXe : e ∈ FXe := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
--   have hfFXf : f ∈ FXf := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
--   have hXFX : X ⊆ FX := subset_sInter (λ _, and.right),
--   have hfFX : f ∉ FX := λ hfFX, hfF₀ ((hX' F₀ hF₀).mpr hXF₀ hfFX),
--   have heFX : e ∉ FX := λ heFX, hfFX (h _ hFX (insert_subset.mpr ⟨heFX, hXFX⟩)),
--   have hFXFXe : FX ⊆ FXe,
--   { rw [hX' FXe hFXe], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
--   have hFXFXf : FX ⊆ FXf,
--   { rw [hX' FXf hFXf], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
--   have hfFXe := h FXe hFXe (insert_subset.mpr ⟨heFXe,hXFX.trans hFXFXe⟩),
--   have hss := (hXf' _ hFXe).mpr (insert_subset.mpr ⟨hfFXe, hXFX.trans hFXFXe⟩),
--   suffices h_eq : FXf = FXe, by rwa h_eq,
--   by_contra h_ne, apply hfFX,
--   have hssu := ssubset_of_subset_of_ne hss h_ne,
--   obtain ⟨FXe',⟨hFXe',heFX',hmin⟩, hunique⟩ := flat_partition FX e hFX heFX,
--   have hFXemin : ∀ (F : set α), flat F → FX ⊆ F → F ⊂ FXe → FX = F, from
--   λ F hF hFXF hFFXe, hmin _ hF hFXF
--     (hFFXe.trans_subset ((hXe' _ hFXe').mpr ((insert_subset_insert hXFX).trans heFX'))),
--   rw hunique FXe ⟨hFXe, insert_subset.mpr ⟨heFXe, hFXFXe⟩, hFXemin⟩ at hssu,
--   rwa ← (hmin _ hFXf hFXFXf hssu) at hfFXf,
-- end)
-- @[simp] lemma matroid_of_flat_apply [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
-- ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :
--   (matroid_of_flat flat univ_flat flat_inter flat_partition).flat = flat :=
-- begin
--   ext F,
--   simp_rw [matroid_of_flat, matroid.flat_iff_closure_self, matroid_of_closure_of_finite_apply],
--   refine ⟨λ hF, _, λ hF, _⟩,
--   { rw ← hF, exact (matroid_of_flat_aux flat univ_flat flat_inter _).1},
--   exact (subset_sInter (λ F', and.right)).antisymm' (sInter_subset_of_mem ⟨hF,rfl.subset⟩),
-- end
-- end from_axioms
end Matroid
