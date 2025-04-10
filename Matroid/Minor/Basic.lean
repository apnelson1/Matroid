import Matroid.Loop
import Mathlib.Data.Matroid.Minor.Basic

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

namespace Matroid

section Delete

variable {D D₁ D₂ R : Set α}

lemma eq_loopyOn_iff_closure {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h, loops]; simp, fun ⟨h,h'⟩ ↦
    by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']⟩

lemma IsRestriction.restriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ＼ {e} :=
  h.restrict_delete_of_disjoint (by simpa)

lemma Loopless.delete (h : M.Loopless) (D : Set α) : (M ＼ D).Loopless := by
  simp [loopless_iff_loops]

instance [h : M.Loopless] {D : Set α} : (M ＼ D).Loopless :=
  h.delete D

lemma removeLoops_eq_delete (M : Matroid α) : M.removeLoops = M ＼ M.loops := by
  rw [← restrict_compl, removeLoops]
  convert rfl using 2
  simp [Set.ext_iff, mem_setOf, isNonloop_iff, isLoop_iff, mem_diff, and_comm]

lemma removeLoops_del_eq_removeLoops (h : X ⊆ M.loops) :
    (M ＼ X).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_delete, delete_delete, removeLoops_eq_delete, loops, delete_closure_eq,
    empty_diff, union_diff_self, closure_empty, union_eq_self_of_subset_left h]

end Delete

section IsMinor

variable {M₀ M₁ M₂ : Matroid α}

lemma contract_delete_diff (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ／ C ＼ (D \ C) := by
  rw [delete_eq_delete_iff, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    inter_assoc]

lemma contract_restrict_eq_restrict_contract (M : Matroid α) (C R : Set α) (h : Disjoint C R) :
    (M ／ C) ↾ R = (M ↾ (R ∪ C)) ／ C := by
  refine ext_indep (by simp [h.sdiff_eq_right]) (fun I _ ↦ ?_)
  obtain ⟨J, hJ⟩ := (M ↾ (R ∪ C)).exists_isBasis' C
  have hJ' : M.IsBasis' J C := by
    have := (isBasis'_restrict_iff.1 hJ).1
    rwa [inter_eq_self_of_subset_left subset_union_right] at this
  rw [restrict_indep_iff, hJ.contract_indep_iff, hJ'.contract_indep_iff, restrict_indep_iff,
    union_subset_iff, and_iff_left (hJ.subset.trans subset_union_right), union_comm R C,
    ← diff_subset_iff, and_assoc, and_assoc, and_congr_right_iff, and_comm, and_congr_left_iff]
  intro _ hd
  rw [hd.sdiff_eq_right]

lemma restrict_contract_eq_contract_restrict (M : Matroid α) {C R : Set α} (hCR : C ⊆ R) :
    (M ↾ R) ／ C = (M ／ C) ↾ (R \ C) := by
  rw [contract_restrict_eq_restrict_contract _ _ _ disjoint_sdiff_right]
  simp [union_eq_self_of_subset_right hCR]

lemma contract_delete_comm (M : Matroid α) {C D : Set α} (hCD : Disjoint C D) :
    M ／ C ＼ D = M ＼ D ／ C := by
  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← contract_inter_ground_eq, aux (hCD.mono_left inter_subset_left) inter_subset_right,
      contract_eq_contract_iff, inter_assoc, delete_ground,
      inter_eq_self_of_subset_right diff_subset]
  rw [delete_eq_restrict, delete_eq_restrict, contract_ground, diff_diff_comm,
    restrict_contract_eq_contract_restrict _ (by simpa [hCE, subset_diff])]

/-- A version of `contract_delete_comm` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma contract_delete_comm' (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ＼ (D \ C) ／ C := by
  rw [contract_delete_diff, contract_delete_comm _ disjoint_sdiff_right]

lemma delete_contract_eq_diff (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D) := by
  rw [contract_eq_contract_iff, delete_ground, diff_inter_diff_right, diff_eq, diff_eq, inter_assoc]

/-- A version of `delete_contract_comm'` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma delete_contract_comm' (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ／ (C \ D) ＼ D := by
  rw [delete_contract_eq_diff, ← contract_delete_comm _ disjoint_sdiff_left]

/-- A version of `contract_delete_contract` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma contract_delete_contract' (M : Matroid α) (C D C' : Set α) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C' \ D) ＼ D := by
  rw [delete_contract_eq_diff, ← contract_delete_comm _ disjoint_sdiff_left, contract_contract]

lemma contract_delete_contract (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C') ＼ D := by rw [contract_delete_contract', sdiff_eq_left.mpr h]

/-- A version of `contract_delete_contract_delete` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma contract_delete_contract_delete' (M : Matroid α) (C D C' D' : Set α) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C' \ D) ＼ (D ∪ D') := by
  rw [contract_delete_contract', delete_delete]

lemma contract_delete_contract_delete (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C') ＼ (D ∪ D') := by
  rw [contract_delete_contract_delete', sdiff_eq_left.mpr h]

/-- A version of `delete_contract_delete` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma delete_contract_delete' (M : Matroid α) (D C D' : Set α) :
    M ＼ D ／ C ＼ D' = M ／ (C \ D) ＼ (D ∪ D') := by
  rw [delete_contract_comm', delete_delete]

lemma delete_contract_delete (M : Matroid α) (D C D' : Set α) (h : Disjoint C D) :
    M ＼ D ／ C ＼ D' = M ／ C ＼ (D ∪ D') := by
  rw [delete_contract_delete', sdiff_eq_left.mpr h]

/- `N` is a minor of `M` if `N = M ／ C ＼ D` for some `C` and `D`.
The definition itself does not require `C` and `D` to be disjoint,
or even to be subsets of the ground set. See `Matroid.IsMinor.exists_eq_contract_delete_disjoint`
for the fact that we can choose `C` and `D` with these properties.
See `Matroid.IsMinor.exists_contract_indep_delete_coindep`
for the fact that we can further choose `C` independent and `D` coindependent. -/
def IsMinor (N M : Matroid α) : Prop := ∃ C D, N = M ／ C ＼ D


infixl:50 " ≤m " => Matroid.IsMinor

/-- `N` is a strict minor of `M` if `N` is a minor of `M` that is not `M` itself.
Equivalently, `N` is obtained from `M` by deleting/contracting subsets of the ground set
that are not both empty. -/

def IsStrictMinor (N M : Matroid α) : Prop := N ≤m M ∧ ¬ M ≤m N

infixl:50 " <m " => Matroid.IsStrictMinor

lemma IsMinor.subset (h : N ≤m M) : N.E ⊆ M.E := by
  obtain ⟨C, D, rfl⟩ := h
  exact diff_subset.trans diff_subset

lemma IsMinor.refl {M : Matroid α} : M ≤m M := ⟨∅, ∅, by simp⟩

lemma IsMinor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
  obtain ⟨C₁, D₁, rfl⟩ := h
  obtain ⟨C₂, D₂, rfl⟩ := h'
  simp only [contract_delete_contract_delete']
  exact ⟨_, _, rfl⟩

lemma IsMinor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := by
  obtain ⟨C, D, rfl⟩ := h
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hE
  rw [← contract_inter_ground_eq, hE.1.2.symm.inter_eq, contract_empty, ← delete_inter_ground_eq,
    hE.2.symm.inter_eq, delete_empty]

lemma IsMinor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M :=
  h'.eq_of_ground_subset h.subset

/-- The minor order is a `PartialOrder` on `Matroid α`.
We prefer the spelling `M ≤m M'` to `M ≤ M'` for the dot notation. -/
instance (α : Type*) : PartialOrder (Matroid α) where
  le M M' := M ≤m M'
  lt M M' := M <m M'
  le_refl _ := IsMinor.refl
  le_trans _ _ _ h h' := IsMinor.trans h h'
  le_antisymm _ _ h h' := IsMinor.antisymm h h'

lemma IsMinor.le (h : N ≤m M) : N ≤ M := h

lemma IsStrictMinor.lt (h : N <m M) : N < M := h

@[simp]
lemma le_eq_isMinor : (fun M M' : Matroid α ↦ M ≤ M') = Matroid.IsMinor := rfl

@[simp]
lemma lt_eq_isStrictMinor : (fun M M' : Matroid α ↦ M < M') = Matroid.IsStrictMinor := rfl

lemma isStrictMinor_iff_isMinor_ne : N <m M ↔ N ≤m M ∧ N ≠ M :=
  lt_iff_le_and_ne (α := Matroid α)

lemma IsStrictMinor.ne (h : N <m M) : N ≠ M :=
  LT.lt.ne h

lemma isStrictMinor_irrefl (M : Matroid α) : ¬ (M <m M) :=
  lt_irrefl M

lemma IsStrictMinor.isMinor (h : N <m M) : N ≤m M :=
  h.lt.le

lemma IsStrictMinor.not_isMinor (h : N <m M) : ¬ (M ≤m N) :=
  h.lt.not_le

lemma IsStrictMinor.ssubset (h : N <m M) : N.E ⊂ M.E :=
  h.isMinor.subset.ssubset_of_ne (fun hE ↦ h.ne (h.isMinor.eq_of_ground_subset hE.symm.subset).symm)

lemma isStrictMinor_iff_isMinor_ssubset : N <m M ↔ N ≤m M ∧ N.E ⊂ M.E :=
  ⟨fun h ↦ ⟨h.isMinor, h.ssubset⟩, fun ⟨h, hss⟩ ↦ ⟨h, fun h' ↦ hss.ne <| by rw [h'.antisymm h]⟩⟩

lemma IsStrictMinor.trans_isMinor (h : N <m M) (h' : M ≤m M') : N <m M' :=
  h.lt.trans_le h'

lemma IsMinor.trans_isStrictMinor (h : N ≤m M) (h' : M <m M') : N <m M' :=
  h.le.trans_lt h'

lemma IsStrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
  h.lt.trans h'

@[simp]
lemma contract_delete_isMinor (M : Matroid α) (C D : Set α) : M ／ C ＼ D ≤m M :=
  ⟨C, D, rfl⟩

lemma IsMinor.exists_eq_contract_delete_disjoint (h : N ≤m M) :
    ∃ (C D : Set α), C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C, D, rfl⟩ := h
  exact ⟨C ∩ M.E, (D ∩ M.E) \ C, inter_subset_right, diff_subset.trans inter_subset_right,
    disjoint_sdiff_right.mono_left inter_subset_left,
    by simp [delete_eq_delete_iff, inter_assoc, inter_diff_assoc]⟩

lemma Indep.of_isMinor (hI : N.Indep I) (hNM : N ≤m M) : M.Indep I := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact hI.of_delete.of_contract

lemma IsNonloop.of_isMinor (h : N.IsNonloop e) (hNM : N ≤m M) : M.IsNonloop e := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact h.of_delete.of_contract

lemma Dep.of_isMinor {D : Set α} (hD : M.Dep D) (hDN : D ⊆ N.E) (hNM : N ≤m M) : N.Dep D :=
  ⟨fun h ↦ hD.not_indep <| h.of_isMinor hNM, hDN⟩

lemma IsLoop.of_isMinor (he : M.IsLoop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.IsLoop e := by
  rw [← singleton_dep] at he ⊢
  exact he.of_isMinor (by simpa) hNM

/-- The scum theorem : we can always realize a minor by contracting an independent set and deleting
a coindependent set/ -/
lemma IsMinor.exists_contract_indep_delete_coindep (h : N ≤m M) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  -- Using duality, it is enough to prove this just for contraction-minors.
  suffices aux : ∀ (M' : Matroid α) (C : Set α) (hC : C ⊆ M'.E),
      ∃ I D, Disjoint I D ∧ M'.Indep I ∧ M'.Coindep D ∧ M' ／ I ＼ D = M' ／ C by
    obtain ⟨C', D', hC', hD', hCD', rfl⟩ := h.exists_eq_contract_delete_disjoint
    obtain ⟨I, D, hID, hI, hD, h_eq⟩ := aux (M ／ C')✶ D' (subset_diff.2 ⟨hD', hCD'.symm⟩)
    obtain ⟨J, D₁, hJD₁, hJ, hD₁, h_eq'⟩ := aux M C' hC'
    rw [← h_eq', dual_coindep_iff, delete_indep_iff, hJ.contract_indep_iff, union_comm] at hD
    rw [← h_eq', dual_contract_delete, ← contract_delete_comm _ hJD₁.symm, delete_indep_iff,
      hD₁.indep.contract_indep_iff] at hI
    refine ⟨J ∪ D, I ∪ D₁, hD.1.2, hI.1.2, by tauto_set, ?_⟩
    rw [← dual_inj, dual_contract_delete, eq_comm, dual_contract, dual_dual] at h_eq
    rw [h_eq, ← h_eq', delete_delete, contract_delete_contract _ _ _ _ (by tauto_set), union_comm I]
  intro M' C hC
  obtain ⟨I, hI⟩ := M'.exists_isBasis C
  refine ⟨_, _, disjoint_sdiff_right, hI.indep, ?_, hI.contract_eq_contract_delete.symm⟩
  refine Indep.of_delete (D := I) <| (coloops_indep _).subset ?_
  rw [← dual_contract, dual_coloops, contract_loops_eq, hI.closure_eq_closure]
  exact diff_subset_diff_left <| M'.subset_closure C

/-- A version of the scum theorem where the minor is obtained as a spanning restriction
of a contraction rather than a contraction-deletion.  -/
lemma IsMinor.exists_spanning_isRestriction_contract (h : N ≤m M) :
    ∃ C, M.Indep C ∧ (N ≤r M ／ C) ∧ (M ／ C).closure N.E = (M ／ C).E := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  exact ⟨C, hC, delete_isRestriction .., by
    rw [← (hD.coindep_contract_of_disjoint hCD.symm).closure_compl, delete_ground]⟩

/-- A version of the scum theorem where the minor is obtained as a spanning restriction
of a contraction rather than a contraction-deletion.  -/
lemma IsMinor.exists_eq_contract_spanning_restrict (h : N ≤m M) :
    ∃ I R, M.Indep I ∧ Disjoint I R ∧ (M ／ I).Spanning R ∧ N = (M ／ I) ↾ R := by
  obtain ⟨C, hC, hNC, hcl⟩ := h.exists_spanning_isRestriction_contract
  obtain ⟨R, hR, rfl⟩ := hNC.exists_eq_restrict
  exact ⟨C, R, hC, (subset_diff.1 hR).2.symm, ⟨hcl, hR⟩, rfl⟩


lemma IsMinor.finite (h : N ≤m M) [M.Finite] : N.Finite :=
  ⟨M.ground_finite.subset h.subset⟩

lemma IsMinor.rankFinite (h : N ≤m M) [RankFinite M] : RankFinite N := by
  obtain ⟨C, D, rfl⟩ := h
  infer_instance

lemma IsMinor.finitary (h : N ≤m M) [Finitary M] : Finitary N := by
  obtain ⟨C, D, rfl⟩ := h
  infer_instance

lemma contract_isMinor (M : Matroid α) (C : Set α) : M ／ C ≤m M := by
  rw [← (M ／ C).delete_empty]
  apply contract_delete_isMinor

lemma contract_isMinor_of_subset (M : Matroid α) {C C' : Set α} (hCC' : C ⊆ C') :
    M ／ C' ≤m M ／ C := by
  rw [← diff_union_of_subset hCC', union_comm, ← contract_contract]
  apply contract_isMinor

lemma contract_isMinor_of_mem (M : Matroid α) {C : Set α} (he : e ∈ C) :
    M ／ C ≤m M ／ {e} :=
  M.contract_isMinor_of_subset (singleton_subset_iff.2 he)

lemma delete_isMinor (M : Matroid α) (D : Set α) : M ＼ D ≤m M := by
  nth_rw 1 [← M.contract_empty]; apply contract_delete_isMinor

lemma restrict_isMinor (M : Matroid α) (hR : R ⊆ M.E := by aesop_mat) : (M ↾ R) ≤m M := by
  rw [← delete_compl]
  apply delete_isMinor

lemma delete_restrict_eq_restrict (M : Matroid α) {D R : Set α} (hDR : Disjoint D R) :
    M ＼ D ↾ R = M ↾ R := by
  suffices ∀ ⦃I : Set α⦄, I ⊆ R → M.Indep I → Disjoint I D from ext_indep rfl <| by simpa
  exact fun I hIR _ ↦ hDR.symm.mono_left hIR

lemma IsRestriction.isMinor (h : N ≤r M) : N ≤m M := by
  rw [← h.eq_restrict, ← delete_compl h.subset]; apply delete_isMinor

lemma IsStrictRestriction.isStrictMinor (h : N <r M) : N <m M :=
  ⟨h.isRestriction.isMinor, fun h' ↦ h.ssubset.not_subset h'.subset⟩

lemma restrict_isStrictMinor (hR : R ⊂ M.E) : M ↾ R <m M :=
  (restrict_isStrictRestriction hR).isStrictMinor

@[simp]
lemma delete_contract_isMinor (M : Matroid α) (D C : Set α) : M ＼ D ／ C ≤m M :=
  ((M ＼ D).contract_isMinor C).trans <| M.delete_isMinor D

lemma contract_restrict_isMinor (M : Matroid α) (C : Set α) (hR : R ⊆ M.E \ C) :
    (M ／ C) ↾ R ≤m M := by
  rw [← delete_compl]
  apply contract_delete_isMinor

lemma contractElem_isStrictMinor (he : e ∈ M.E) : M ／ {e} <m M :=
  ⟨contract_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma deleteElem_isStrictMinor (he : e ∈ M.E) : M ＼ {e} <m M :=
  ⟨delete_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma IsStrictMinor.exists_eq_contract_delete_disjoint (hNM : N <m M) :
    ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ (C ∪ D).Nonempty ∧ N = M ／ C ＼ D := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.isMinor.exists_eq_contract_delete_disjoint
  refine ⟨C, D, hC, hD, hCD, ?_, rfl⟩
  exact (show (M.E ∩ _).Nonempty by simpa [diff_diff] using hNM.ssubset).mono inter_subset_right

lemma isStrictMinor_iff_exists_eq_contract_delete :
    N <m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ (C ∪ D).Nonempty ∧ N = M ／ C ＼ D := by
  refine ⟨IsStrictMinor.exists_eq_contract_delete_disjoint, ?_⟩
  rintro ⟨C, D, hC, hD, hdj, h, rfl⟩
  suffices (M.E ∩ (C ∪ D)).Nonempty by simpa [isStrictMinor_iff_isMinor_ssubset, diff_diff]
  rwa [inter_eq_self_of_subset_right (by simp [hC, hD])]

lemma IsStrictMinor.exists_isMinor_contractElem_or_deleteElem (hNM : N <m M) :
    ∃ e ∈ M.E, N ≤m M ／ {e} ∨ N ≤m M ＼ {e} := by
  obtain ⟨C, D, hC, hD, hCD, hne, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  obtain ⟨e, he : e ∈ C⟩ | ⟨e, he : e ∈ D⟩ := by simpa using hne
  · refine ⟨e, hC he, .inl ?_⟩
    rw [← insert_eq_of_mem he, ← singleton_union, ← contract_contract]
    apply contract_delete_isMinor
  refine ⟨e, hD he, .inr ?_⟩
  rw [contract_delete_comm _ hCD, ← insert_eq_of_mem he, ← singleton_union, ← delete_delete]
  apply delete_contract_isMinor

lemma IsMinor.isStrictMinor_or_eq (h : N ≤m M) : N <m M ∨ N = M := by
  rw [isStrictMinor_iff_isMinor_ne, and_iff_right h]
  exact ne_or_eq N M

lemma IsMinor.dual (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, rfl⟩ := h
  rw [dual_delete, dual_contract]
  apply delete_contract_isMinor

lemma IsMinor.of_dual (h : N✶ ≤m M✶) : N ≤m M := by
  simpa using h.dual

@[simp]
lemma dual_isMinor_iff : N✶ ≤m M✶ ↔ N ≤m M :=
  ⟨IsMinor.of_dual, IsMinor.dual⟩

lemma isMinor_dual_iff_dual_isMinor : N ≤m M✶ ↔ N✶ ≤m M := by
  rw [← dual_isMinor_iff, dual_dual]

lemma IsStrictMinor.dual (h : N <m M) : N✶ <m M✶ := by
  rwa [IsStrictMinor, dual_isMinor_iff, dual_isMinor_iff]

lemma IsStrictMinor.of_dual (h : N✶ <m M✶) : N <m M := by
  simpa using h.dual

lemma dual_isStrictMinor_iff: N✶ <m M✶ ↔ N <m M :=
  ⟨IsStrictMinor.of_dual, IsStrictMinor.dual⟩

lemma isStrictMinor_dual_iff_dual_isStrictMinor : N <m M✶ ↔ N✶ <m M := by
  rw [← dual_isStrictMinor_iff, dual_dual]

lemma IsColoop.of_isMinor (he : M.IsColoop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.IsColoop e := by
  rw [← dual_isLoop_iff_isColoop] at he ⊢
  exact he.of_isMinor heN hNM.dual

lemma IsStrictMinor.encard_ground_lt [N.Finite] (hNM : N <m M) : N.E.encard < M.E.encard :=
  N.ground_finite.encard_lt_encard hNM.ssubset


/-- Classically choose an independent contract-set from a proof that `N` is a minor of `M`. -/
def IsMinor.C (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose

/-- Classically choose a coindependent delete-set from a proof that `N` is a minor of `M`. -/
def IsMinor.D (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose

lemma IsMinor.C_indep (h : N ≤m M) : M.Indep h.C :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.1

lemma IsMinor.D_coindep (h : N ≤m M) : M.Coindep h.D :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.2.1

lemma IsMinor.disjoint (h : N ≤m M) : Disjoint h.C h.D :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.2.2.1

lemma IsMinor.eq_con_del (h : N ≤m M) : N = M ／ h.C ＼ h.D :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose_spec.2.2.2

lemma IsMinor.C_union_D_eq (h : N ≤m M) : h.C ∪ h.D = M.E \ N.E := by
  simp only [h.eq_con_del, delete_ground, contract_ground, diff_diff]
  rw [Set.diff_diff_cancel_left]
  exact union_subset h.C_indep.subset_ground h.D_coindep.subset_ground

lemma IsMinor.C_disjoint (h : N ≤m M) : Disjoint h.C N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_left

lemma IsMinor.D_disjoint (h : N ≤m M) : Disjoint h.D N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_right

lemma IsMinor.eq_con_restr (h : N ≤m M) : N = (M ／ h.C) ↾ N.E := by
  simp [h.eq_con_del, ← restrict_compl]

lemma IsStrictMinor.C_union_D_nonempty (h : N <m M) : (h.isMinor.C ∪ h.isMinor.D).Nonempty := by
  rw [h.isMinor.C_union_D_eq]
  exact nonempty_of_ssubset h.ssubset

lemma finite_setOf_isMinor (M : Matroid α) [M.Finite] : {N | N ≤m M}.Finite :=
  (finite_setOf_matroid M.ground_finite).subset (fun _ hNM ↦ hNM.subset)

end IsMinor

section Constructions

variable {E : Set α}

@[simp] lemma delete_ground_self (M : Matroid α) : M ＼ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] lemma contract_ground_self (M : Matroid α) : M ／ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] lemma emptyOn_isRestriction (M : Matroid α) : emptyOn α ≤r M :=
  ⟨∅, empty_subset _, by simp⟩

@[simp] lemma emptyOn_isMinor (M : Matroid α) : emptyOn α ≤m M :=
  M.emptyOn_isRestriction.isMinor

@[simp] lemma isMinor_emptyOn_iff : M ≤m emptyOn α ↔ M = emptyOn α :=
  ⟨fun h ↦ ground_eq_empty_iff.1 (eq_empty_of_subset_empty h.subset),
    by rintro rfl; apply emptyOn_isMinor⟩

@[simp]
lemma isRestriction_emptyOn_iff : M ≤r emptyOn α ↔ M = emptyOn α := by
  refine ⟨fun h ↦ isMinor_emptyOn_iff.1 h.isMinor, ?_⟩
  rintro rfl
  exact IsRestriction.refl

@[simp]
lemma loopyOn_delete (E X : Set α) : (loopyOn E) ＼ X = loopyOn (E \ X) := by
  rw [← restrict_compl, loopyOn_restrict, loopyOn_ground]

@[simp]
lemma loopyOn_contract (E X : Set α) : (loopyOn E) ／ X = loopyOn (E \ X) := by
  simp_rw [eq_loopyOn_iff_closure, loops, contract_closure_eq, empty_union, loopyOn_closure_eq,
    contract_ground, loopyOn_ground, true_and]

lemma isMinor_loopyOn_iff_exists : M ≤m loopyOn E ↔ ∃ F ⊆ E, M = loopyOn F := by
  refine ⟨fun h ↦ ⟨M.E, h.subset, ?_⟩, fun h ↦ ?_⟩
  · obtain ⟨C, D, rfl⟩ := h
    simp
  obtain ⟨F, hF, rfl⟩ := h
  simpa using (loopyOn E).restrict_isMinor hF

lemma isMinor_loopyOn_iff : M ≤m loopyOn E ↔ M = loopyOn M.E ∧ M.E ⊆ E := by
  rw [isMinor_loopyOn_iff_exists]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨_, h.2, h.1⟩⟩
  obtain ⟨F, h, rfl⟩ := h
  simpa

lemma contract_eq_loopyOn_of_spanning {C : Set α} (h : M.Spanning C) :
    M ／ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_closure, contract_ground, and_iff_left rfl, contract_loops_eq, h.closure_eq]

@[simp] lemma freeOn_delete (E X : Set α) : (freeOn E) ＼ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_contract, loopyOn_contract, loopyOn_dual_eq]

@[simp] lemma freeOn_contract (E X : Set α) : (freeOn E) ／ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_delete, loopyOn_delete, loopyOn_dual_eq]

-- Move next two to `Restriction`
lemma restrict_indep_eq_freeOn (hI : M.Indep I) : M ↾ I = freeOn I := by
  refine ext_indep rfl (fun J _ ↦ ?_)
  simp only [restrict_ground_eq, restrict_indep_iff, freeOn_indep_iff, and_iff_right_iff_imp]
  exact hI.subset

lemma indep_iff_restrict_eq_freeOn : M.Indep I ↔ (M ↾ I = freeOn I) := by
  refine ⟨restrict_indep_eq_freeOn, fun h ↦ ?_⟩
  have h' := restrict_indep_iff (M := M) (I := I) (R := I)
  rwa [h, freeOn_indep_iff, iff_true_intro Subset.rfl, and_true, true_iff] at h'

-- Move to `Loops`
lemma restrict_subset_loops_eq (hX : X ⊆ M.loops) : M ↾ X = loopyOn X := by
  rw [eq_loopyOn_iff_closure, restrict_loops_eq', inter_eq_self_of_subset_right hX,
    union_eq_self_of_subset_right diff_subset, and_iff_left M.restrict_ground_eq]

end Constructions

end Matroid
