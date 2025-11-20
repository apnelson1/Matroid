import Matroid.Connectivity.Separation

namespace Matroid

open Set

variable {α : Type*} {M : Matroid α} {P : M.Partition} {X Y X' Y' : Set α}

@[mk_iff]
structure Partition.SepOf (P : M.Partition) (X Y : Set α) : Prop where
  subset_left : X ⊆ P.left
  subset_right : Y ⊆ P.right

lemma Partition.sepOf_iff_left (P : M.Partition) (hY : Y ⊆ M.E) :
    P.SepOf X Y ↔ X ⊆ P.left ∧ Disjoint P.left Y := by
  rw [sepOf_iff, ← P.compl_left, subset_diff, and_iff_right hY, disjoint_comm]

lemma Partition.sepOf_iff_right (P : M.Partition) (hX : X ⊆ M.E) :
    P.SepOf X Y ↔ Disjoint X P.right ∧ Y ⊆ P.right := by
  rw [sepOf_iff, ← P.compl_right, subset_diff, and_iff_right hX]

lemma Partition.SepOf.symm (hP : P.SepOf X Y) : P.symm.SepOf Y X :=
  ⟨hP.2, hP.1⟩

lemma Partition.SepOf.disjoint (hP : P.SepOf X Y) : Disjoint X Y :=
  P.disjoint.mono hP.1 hP.2

lemma Partition.SepOf.mono_left (hP : P.SepOf X Y) (hX'X : X' ⊆ X) : P.SepOf X' Y :=
  ⟨hX'X.trans hP.1, hP.2⟩

lemma Partition.SepOf.mono_right (hP : P.SepOf X Y) (hY'Y : Y' ⊆ Y) : P.SepOf X Y' :=
  ⟨hP.1, hY'Y.trans hP.2⟩

lemma Partition.SepOf.disjoint_left (hP : P.SepOf X Y) : Disjoint P.left Y :=
  (subset_diff.1 <| hP.subset_right.trans_eq P.compl_left.symm).2.symm

lemma Partition.SepOf.disjoint_right (hP : P.SepOf X Y) : Disjoint X P.right :=
  (subset_diff.1 <| hP.subset_left.trans_eq P.compl_right.symm).2

lemma Partition.SepOf.mono (hP : P.SepOf X Y) (hX'X : X' ⊆ X) (hY'Y : Y' ⊆ Y) : P.SepOf X' Y' :=
  ⟨hX'X.trans hP.1, hY'Y.trans hP.2⟩

@[simp]
lemma Partition.symm_sepOf_iff : P.symm.SepOf X Y ↔ P.SepOf Y X :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

lemma partition_sepOf (hXY : Disjoint X Y) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    (M.partition X).SepOf X Y := by
  rw [Partition.sepOf_iff_left _ hYE, partition_left _ _ hXE, and_iff_left hXY]


-- lemma Partition.restrict_sepOf_iff (R : Set α) :
--     (P.restrict R).SepOf X Y ↔ P.SepOf X Y ∧ X ⊆ R ∧ Y ⊆ R := by
--   simp only [SepOf, restrict_left, subset_inter_iff, restrict_right]
--   refine ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ?_, fun h ↦ ?_⟩
--   · refine ⟨⟨h1, ?_⟩, ?_⟩

lemma Partition.SepOf.left_subset_ground (h : P.SepOf X Y) : X ⊆ M.E :=
  h.1.trans P.left_subset_ground

lemma Partition.SepOf.right_subset_ground (h : P.SepOf X Y) : Y ⊆ M.E :=
  h.2.trans P.right_subset_ground

lemma Partition.sepOf_self_compl_iff (hX : X ⊆ M.E) :
    P.SepOf X (M.E \ X) ↔ P = M.partition X hX := by
  rw [sepOf_iff, diff_subset_comm, P.compl_right, ← subset_antisymm_iff]
  refine ⟨?_, by simp +contextual⟩
  rintro rfl
  exact Partition.ext rfl <| by simp [P.compl_left]

lemma Partition.sepOf_compl_self_iff (hX : X ⊆ M.E) :
    P.SepOf (M.E \ X) X ↔ P = M.partition (M.E \ X) diff_subset := by
  rw [← sepOf_self_compl_iff]
  simp [inter_eq_self_of_subset_right hX]

/-- The minimum order of a separation of `M` with `X` and `Y` contained in different sides.
The 'well-defined' inputs are where `X` and `Y` are disjoint subsets of `M.E`,
but we give a more complicated definition (in terms of `Matroid.core`)
that ignores junk elements, loops and coloops in `X` and `Y`.
This definition is the simplest definition that is unconditionally monotone under restrictions,
and preserved by intersections with the ground set, duality and adding/removing loops.
`Matroid.eConnBetween_eq_iInf` shows that the definition behaves correctly for sensible inputs. -/
noncomputable def eConnBetween (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  ⨅ P : {P : M.Partition // P.SepOf (M.core X) (M.core Y)}, P.1.eConn

lemma Partition.SepOf.eConnBetween_le_of_core (hP : P.SepOf (M.core X) (M.core Y)) :
    M.eConnBetween X Y ≤ P.eConn :=
  iInf_le_of_le ⟨P, hP⟩ rfl.le

lemma Partition.SepOf.eConnBetween_le (hP : P.SepOf X Y) :
    M.eConnBetween X Y ≤ P.eConn :=
  (hP.mono (M.core_subset X) (M.core_subset Y)).eConnBetween_le_of_core

lemma eConnBetween_symm (M : Matroid α) : M.eConnBetween X Y = M.eConnBetween Y X := by
  apply le_antisymm <;>
  exact le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P.symm, by simpa⟩ (by simp)

lemma eConnBetween_le_eConn_left (M : Matroid α) (hdj : Disjoint X Y) :
    M.eConnBetween X Y ≤ M.eConn X := by
  have h : (M.partition (M.core X)).SepOf (M.core X) (M.core Y) := by
    simpa [Partition.sepOf_iff, subset_diff] using hdj.symm.mono (core_subset ..) (core_subset ..)
  exact h.eConnBetween_le_of_core.trans <| by simp

lemma eConnBetween_le_eConn_right (M : Matroid α) (hdj : Disjoint X Y) :
    M.eConnBetween X Y ≤ M.eConn Y := by
  rw [eConnBetween_symm]
  exact M.eConnBetween_le_eConn_left hdj.symm

lemma le_eConnBetween_iff_forall_sepOf_core {k : ℕ∞} : k ≤ M.eConnBetween X Y ↔
    ∀ (P : M.Partition), P.SepOf (M.core X) (M.core Y) → k ≤ P.eConn := by
  simp [eConnBetween, le_iInf_iff, Subtype.forall]

lemma eConnBetween_eq_iInf (hXY : Disjoint X Y) (hX : X ⊆ M.E) (hY : Y ⊆ M.E) :
    M.eConnBetween X Y = ⨅ P : {P : M.Partition // P.SepOf X Y}, P.1.eConn := by
  simp only [eConnBetween, le_antisymm_iff, le_iInf_iff, Subtype.forall]
  refine ⟨fun P hP ↦ ?_, fun P hP ↦ ?_⟩
  · exact iInf_le_of_le ⟨P, hP.mono (M.core_subset X) (M.core_subset Y)⟩ rfl.le
  refine iInf_le_of_le ⟨M.partition ((P.left ∪ X) \ Y), ?_⟩ ?_
  · simpa [Partition.sepOf_iff_left _ hY, disjoint_sdiff_left, subset_diff]
  rw [eConn_partition, ← eConn_core, core_diff, core_union, ← M.core_core X,
    union_eq_self_of_subset_right (M.core_subset_core hP.1), sdiff_eq_left.2, eConn_core,
    P.eConn_left]
  exact hP.disjoint_left.mono_left (M.core_subset ..)

lemma le_eConnBetween_iff_forall_sepOf {k : ℕ∞} (hdj : Disjoint X Y) (hX : X ⊆ M.E) (hY : Y ⊆ M.E) :
    k ≤ M.eConnBetween X Y ↔ ∀ (P : M.Partition), P.SepOf X Y → k ≤ P.eConn := by
  simp [eConnBetween_eq_iInf hdj hX hY]

lemma exists_partition_eConn_eq_eConnBetween_core (hXY : Disjoint (M.core X) (M.core Y)) :
    ∃ P : M.Partition, P.SepOf (M.core X) (M.core Y) ∧ P.eConn = M.eConnBetween X Y := by
  set α := {P : M.Partition // P.SepOf (M.core X) (M.core Y)}
  have hne : Nonempty α := ⟨_, partition_sepOf hXY (core_subset_ground ..) (core_subset_ground ..)⟩
  obtain ⟨⟨P,h⟩, hP⟩ := ENat.exists_eq_iInf (f := fun i : α ↦ i.1.eConn)
  exact ⟨P, h, hP⟩

lemma exists_partition_eConn_eq_eConnBetween (hXY : Disjoint X Y) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    ∃ P : M.Partition, P.SepOf X Y ∧ P.eConn = M.eConnBetween X Y := by
  simp_rw [eConnBetween_eq_iInf hXY hXE hYE]
  set α := {P : M.Partition // P.SepOf X Y}
  have hne : Nonempty α := ⟨_, partition_sepOf hXY hXE hYE⟩
  obtain ⟨⟨P,h⟩, hP⟩ := ENat.exists_eq_iInf (f := fun i : α ↦ i.1.eConn)
  exact ⟨P, h, hP⟩

lemma eConnBetween_of_not_disjoint (M : Matroid α) (hXY : ¬ Disjoint (M.core X) (M.core Y)) :
    M.eConnBetween X Y = ⊤ := by
  simp [eConnBetween, iInf_subtype, show ∀ P : M.Partition, ¬ P.SepOf (M.core X) (M.core Y) from
    fun P hP ↦ hXY <| P.disjoint.mono hP.1 hP.2]

lemma eConnBetween_mono_left (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.eConnBetween X' Y ≤ M.eConnBetween X Y :=
  le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P, hP.mono_left (M.core_subset_core hX)⟩ rfl.le

lemma eConnBetween_mono_right (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.eConnBetween X Y' ≤ M.eConnBetween X Y :=
  le_iInf fun ⟨P, hP⟩ ↦ iInf_le_of_le ⟨P, hP.mono_right (M.core_subset_core hY)⟩ rfl.le

lemma eConnBetween_mono (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.eConnBetween X' Y' ≤ M.eConnBetween X Y :=
  (M.eConnBetween_mono_left hX _).trans <| M.eConnBetween_mono_right _ hY

@[simp]
lemma eConnBetween_core_left (M : Matroid α) (X Y : Set α) :
    M.eConnBetween (M.core X) Y = M.eConnBetween X Y := by
  simp [eConnBetween, iInf_subtype]

@[simp]
lemma eConnBetween_core_right (M : Matroid α) (X Y : Set α) :
    M.eConnBetween X (M.core Y) = M.eConnBetween X Y := by
  simp [eConnBetween, iInf_subtype]

@[simp]
lemma eConnBetween_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.eConnBetween (X ∩ M.E) Y = M.eConnBetween X Y := by
  refine (M.eConnBetween_mono_left inter_subset_left _).antisymm ?_
  rw [← eConnBetween_core_left]
  exact M.eConnBetween_mono_left (by simp) _

@[simp]
lemma eConnBetween_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.eConnBetween X (Y ∩ M.E) = M.eConnBetween X Y := by
  rw [eConnBetween_symm, eConnBetween_inter_ground_left, eConnBetween_symm]

@[simp]
lemma eConnBetween_self_compl (M : Matroid α) (X : Set α) :
    M.eConnBetween X (M.E \ X) = M.eConn X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← eConnBetween_inter_ground_left, ← diff_inter_self_eq_diff, aux _ inter_subset_right,
      eConn_inter_ground]
  obtain ⟨P, hP, hP'⟩ := exists_partition_eConn_eq_eConnBetween disjoint_sdiff_right hXE diff_subset
  rw [Partition.sepOf_self_compl_iff hXE] at hP
  rw [← hP', hP, eConn_partition]

@[simp]
lemma eConnBetween_compl_self (M : Matroid α) (X : Set α) :
    M.eConnBetween (M.E \ X) X = M.eConn X := by
  rw [eConnBetween_symm, M.eConnBetween_self_compl]

@[simp]
lemma eConnBetween_dual_eq (M : Matroid α) (X Y : Set α) :
    M✶.eConnBetween X Y = M.eConnBetween X Y := by
  simp only [eConnBetween, iInf_subtype, core_dual]
  apply (Partition.dualEquiv M).symm.iInf_congr
  intro P
  convert rfl using 2 <;>
  simp [Partition.sepOf_iff]

@[simp]
lemma eConnBetween_removeLoops_eq (M : Matroid α) :
    M.removeLoops.eConnBetween = M.eConnBetween := by
  ext X Y
  obtain hndj | hdj := em' <| Disjoint (M.core X) (M.core Y)
  · rw [eConnBetween_of_not_disjoint _ (by simpa), eConnBetween_of_not_disjoint _ hndj]
  refine le_antisymm ?_ ?_
  · obtain ⟨P, hP, hP_eq⟩ := M.exists_partition_eConn_eq_eConnBetween_core hdj
    refine iInf_le_of_le ⟨M.removeLoops.partition (P.left ∩ _) inter_subset_right, ?_⟩ ?_
    · rw [Partition.sepOf_iff_left _ (core_subset_ground ..)]
      simp only [removeLoops_core, partition_left, subset_inter_iff, hP.1, true_and]
      rw [← removeLoops_core, and_iff_right (core_subset_ground ..)]
      exact P.disjoint.mono inter_subset_left hP.2
    simp only [eConn_partition, removeLoops_eConn, ← hP_eq, ← P.eConn_left]
    rw [← removeLoops_eConn, eConn_inter_ground]
  obtain ⟨P, hP, hP_eq⟩ := M.removeLoops.exists_partition_eConn_eq_eConnBetween_core (by simpa)
  refine iInf_le_of_le ⟨M.partition P.left ?_, ?_⟩ ?_
  · exact P.left_subset_ground.trans M.removeLoops_isRestriction.subset
  · rw [Partition.sepOf_iff_left _ (by simp)]
    simp only [partition_left]
    simp only [removeLoops_core] at hP
    exact ⟨hP.1, hP.disjoint_left⟩
  simp only [eConn_partition, hP_eq.symm, ← P.eConn_left, removeLoops_eConn]
  exact rfl.le

lemma eConnBetween_restrict_le (M : Matroid α) (X Y R : Set α) :
    (M ↾ R).eConnBetween X Y ≤ M.eConnBetween X Y := by
  wlog hRE : R ⊆ M.E with aux
  · rw [← eConnBetween_removeLoops_eq, restrict_removeLoops, eConnBetween_removeLoops_eq]
    exact aux M X Y (R ∩ M.E) inter_subset_right
  rw [le_eConnBetween_iff_forall_sepOf_core]
  intro P hP
  refine iInf_le_of_le ⟨P.restrict R, ?_⟩ ?_
  · rw [Partition.sepOf_iff_left _ (core_subset_ground ..)]
    simp only [Partition.restrict_left, subset_inter_iff]
    exact ⟨⟨(core_restrict_subset ..).trans hP.1, core_subset_ground ..⟩,
      P.disjoint.mono inter_subset_left ((core_restrict_subset ..).trans hP.2)⟩
  simp only [eLocalConn_restrict_eq, Partition.restrict_left, inter_assoc, inter_self,
    Partition.restrict_right, diff_eq_empty.2 hRE, union_empty, Partition.eConn]
  exact M.eLocalConn_mono inter_subset_left inter_subset_left

lemma eConnBetween_delete_le (M : Matroid α) (X Y D : Set α) :
    (M ＼ D).eConnBetween X Y ≤ M.eConnBetween X Y := by
  apply eConnBetween_restrict_le

lemma eConnBetween_contract_le (M : Matroid α) (X Y C : Set α) :
    (M ／ C).eConnBetween X Y ≤ M.eConnBetween X Y := by
  rw [← eConnBetween_dual_eq, dual_contract, ← M.eConnBetween_dual_eq]
  apply eConnBetween_delete_le

lemma IsMinor.eConnBetween_le {N : Matroid α} (hNM : N ≤m M) :
    N.eConnBetween X Y ≤ M.eConnBetween X Y := by
  obtain ⟨C, D, h, -, -, rfl⟩ := hNM
  exact le_trans ((M ／ C).eConnBetween_delete_le X Y D) <| (M.eConnBetween_contract_le X Y C)
