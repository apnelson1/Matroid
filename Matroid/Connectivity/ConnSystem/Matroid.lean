import Matroid.Connectivity.Basic
import Matroid.Connectivity.ConnSystem.Basic
import Matroid.Finitize

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X : Set α} {ι : Type*}

/- Our goal here is to define `Matroid.eConn` as a term of type `ConnSystem α`: that is, a
bundled symmetric, submodular function on `Set α`.
Proving submodularity requires a nontrivial amount of work,
which we do as quickly as possible in terms of an auxiliary raw function `eConnAux`;
we prove that this function is self-dual and submodular, and then use it to define `eConn`
as a package. -/


/-- the connectivity function of a matroid as a pure function, rather than a `ConnSystem`.
Just an implementation detail on the way to a `ConnSystem`; not intended for external use. -/
private noncomputable abbrev eConnAux (M : Matroid α) (X : Set α) : ℕ∞ :=
  M.eLocalConn X (M.E \ X)

private lemma eConnAux_inter_ground (M : Matroid α) (X : Set α) :
    M.eConnAux (X ∩ M.E) = M.eConnAux X := by
  rw [eConnAux, diff_inter_self_eq_diff, eLocalConn_inter_ground_left]

private lemma eConnAux_dual (M : Matroid α) (X : Set α) : M✶.eConnAux X = M.eConnAux X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [eq_comm, ← eConnAux_inter_ground, ← aux _ inter_subset_right, ← dual_ground,
      eConnAux_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis (M.E \ X)
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset <| subset_union_left (t := J)
  have hsp : M.Spanning (X ∪ J) := by
    rw [spanning_iff_closure_eq, closure_union_congr_right hJ.closure_eq_closure,
      union_diff_cancel hXE, closure_ground]
  have hBdual := (hB.isBase_of_spanning hsp).compl_inter_isBasis_of_inter_isBasis hI
  rw [diff_inter_diff, union_comm, ← diff_diff] at hBdual
  obtain ⟨B', hB', rfl⟩ := hJ.exists_isBase
  have hB'dual := hB'.compl_inter_isBasis_of_inter_isBasis hJ
  rw [diff_diff_cancel_left hXE] at hB'dual
  have hB'E := hB'.subset_ground
  have hBXB' : B ⊆ X ∪ B' := by grind [hB.subset]
  rw [eConnAux, eConnAux, dual_ground,
    hI.eLocalConn_eq_of_disjoint hJ disjoint_sdiff_right,
    hB'dual.eLocalConn_eq_of_disjoint hBdual disjoint_sdiff_right,
    (hB.isBasis_subset (by grind) (by grind)).nullity_eq,
    (hB'.compl_isBase_dual.isBasis_ground.isBasis_subset (by grind) (by grind)).nullity_eq]
  exact congr_arg _ <| by grind

private lemma eConnAux_delete_le (M : Matroid α) (X D : Set α) :
    (M ＼ D).eConnAux X ≤ M.eConnAux X := by
  grw [eConnAux, eLocalConn_delete_eq, eConnAux, delete_ground]
  exact M.eLocalConn_mono diff_subset <| by grind

lemma stronglyPreservable_eConnAux : StronglyPreservable (α := α) Matroid.eConnAux := by
  refine ⟨eConnAux_dual, eConnAux_inter_ground, eConnAux_delete_le, fun M B X k hB hkX ↦ ?_⟩
  have h1 := hB.exists_restrict_multiConn_eq'
      (X := fun b ↦ bif b then X ∩ M.E else M.E \ X) (k := k)
  simp only [inter_comm X, pairwise_disjoint_on_bool, disjoint_sdiff_inter.symm, iUnion_bool,
    cond_true, cond_false, inter_union_diff, ← eLocalConn_eq_multiConn, forall_const] at h1
  rw [inter_comm, eLocalConn_inter_ground_left, imp_iff_right hkX] at h1
  obtain ⟨R, hRE, hBR, hRK, hconnk⟩ := h1
  refine ⟨R \ B, diff_subset.trans hRE, disjoint_sdiff_left, hRK.le, ?_⟩
  have hrw1 : X ∩ M.E ∩ R = X ∩ (M ↾ R).E := by
    simp [inter_assoc, inter_eq_self_of_subset_right hRE]
  have hrw2 : M.E \ X ∩ R = (M ↾ R).E \ X := by
    rw [restrict_ground_eq, ← inter_diff_right_comm, inter_eq_self_of_subset_right hRE]
  simp_rw [Bool.apply_cond (f := fun X ↦ X ∩ R), hrw1, hrw2, ← eLocalConn_eq_multiConn,
    eLocalConn_inter_ground_left, restrict_ground_eq] at hconnk
  rwa [union_diff_cancel hBR]

private lemma eConnAux_submod (M : Matroid α) (X Y : Set α) :
    M.eConnAux (X ∩ Y) + M.eConnAux (X ∪ Y) ≤ M.eConnAux X + M.eConnAux Y := by
  by_contra! hlt
  obtain ⟨N, -, hN, hlt'⟩ :=
    stronglyPreservable_eConnAux.exists_finite_counterexample_of_sum_lt_sum M
    (fun i ↦ bif i then X else Y) (fun i ↦ bif i then (X ∩ Y) else (X ∪ Y)) (by simpa)
  replace hlt' : N.eConnAux X + N.eConnAux Y < N.eConnAux (X ∩ Y) + N.eConnAux (X ∪ Y) :=
    by simpa using hlt'
  have hsm1 := N.eRk_submod X Y
  have hsm2 := N.eRk_submod (N.E \ X) (N.E \ Y)
  rw [← diff_inter, diff_inter_diff] at hsm2
  have h1 := N.eRk_add_eRk_eq_eRk_union_add_eLocalConn X (N.E \ X)
  have h2 := N.eRk_add_eRk_eq_eRk_union_add_eLocalConn Y (N.E \ Y)
  have hi := N.eRk_add_eRk_eq_eRk_union_add_eLocalConn (X ∩ Y) (N.E \ (X ∩ Y))
  have hu := N.eRk_add_eRk_eq_eRk_union_add_eLocalConn (X ∪ Y) (N.E \ (X ∪ Y))
  rw [union_diff_self, eRk_eq_eRank subset_union_right, ← eConnAux] at h1 h2 hu hi
  simp_rw [← cast_rk_eq] at *
  clear hlt
  enat_to_nat!
  lia

/-- The connectivity function of a matroid, given as a `ConnSystem`. -/
noncomputable def eConn (M : Matroid α) : ConnSystem α ℕ∞ where
  E := M.E
  toFun := M.eConnAux
  toFun_inter_ground := by simp
  toFun_compl X hX := by rw [eConnAux, diff_diff_cancel_left hX, eLocalConn_comm]
  toFun_submod X Y _ _ := M.eConnAux_submod X Y

lemma eConn_eq_eLocalConn (M : Matroid α) (X : Set α) : M.eConn X = M.eLocalConn X (M.E \ X) := rfl

@[simp]
lemma eConn_ground_eq (M : Matroid α) : M.eConn.E = M.E := rfl

@[simp] lemma eConn_inter_ground (M : Matroid α) (X : Set α) :  M.eConn (X ∩ M.E) = M.eConn X :=
  M.eConnAux_inter_ground X

lemma eConn_unitary (M : Matroid α) : M.eConn.Unitary :=
  ⟨by simp [eConn_eq_eLocalConn],
    fun e ↦ by grw [eConn_eq_eLocalConn, eLocalConn_le_eRk_left, eRk_singleton_le]⟩

@[simp]
lemma eConn_empty (M : Matroid α) : M.eConn ∅ = 0 :=
  M.eConn_unitary.conn_empty

@[simp]
lemma loopyOn_eConn (E X : Set α) : (loopyOn E).eConn X = 0 := by
  simp [eConn]

@[simp]
lemma eConn_ground (M : Matroid α) : M.eConn M.E = 0 := by
  simp [eConn]

/-- Connectivity is self-dual. -/
@[simp]
lemma eConn_dual (M : Matroid α) (X : Set α) : M✶.eConn X = M.eConn X :=
  M.eConnAux_dual X

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
    M.eConn X = M.eLocalConn (X ∩ M.E) (M.E \ X) := by
  rw [← eConn_inter_ground, eConn_eq_eLocalConn, diff_inter_self_eq_diff, inter_comm]

@[simp]
lemma removeLoops_eConn (M : Matroid α) (X : Set α) : M.removeLoops.eConn X = M.eConn X := by
  rw [eConn_eq_eLocalConn, removeLoops_eLocalConn, eConn, ← eLocalConn_closure_right,
    removeLoops_ground_eq, diff_eq_compl_inter, closure_inter_setOf_isNonloop_eq,
    ← closure_inter_ground, ← diff_eq_compl_inter, eLocalConn_closure_right]

lemma eConn_union_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eConn (X ∪ L) = M.eConn X := by
  rw [← removeLoops_eConn, ← eConn_inter_ground, removeLoops_ground_eq, setOf_isNonloop_eq,
    show (X ∪ L) ∩ (M.E \ M.loops) = X ∩ (M.E \ M.loops) by tauto_set,
    ← setOf_isNonloop_eq, ← removeLoops_ground_eq, eConn_inter_ground, removeLoops_eConn]

lemma eConn_diff_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    M.eConn (X \ L) = M.eConn X := by
  rw [← eConn_union_of_subset_loops hL, diff_union_self, eConn_union_of_subset_loops hL]

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
  rw [eConn_dual, eConn_restrict_univ_eq, eConn_dual]

@[simp]
lemma eConn_compl (M : Matroid α) (X : Set α) : M.eConn (M.E \ X) = M.eConn X :=
  M.eConn.conn_compl X

/-- A version of `eConn_compl` where `compl` really means complementation in the universe. -/
@[simp]
lemma eConn_compl' (M : Matroid α) (X : Set α) : M.eConn Xᶜ = M.eConn X := by
  rw [← eConn_restrict_univ_eq, compl_eq_univ_diff, ← M.eConn_restrict_univ_eq,
    eq_comm, ← eConn_compl, restrict_ground_eq]

lemma IsBasis'.eConn_eq_nullity_contract (hI : M.IsBasis' I X) : M.eConn X =
    (M ／ (M.E \ X)).nullity I := by
  rw [eConn_eq_eLocalConn, hI.eLocalConn_eq_nullity_project_right,
    nullity_project_eq_nullity_contract]

lemma IsBasis.eConn_eq_nullity_contract (hI : M.IsBasis I X) : M.eConn X =
    (M ／ (M.E \ X)).nullity I :=
  hI.isBasis'.eConn_eq_nullity_contract

lemma eConn_union_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    M.eConn (X ∪ L) = M.eConn X := by
  rw [← eConn_dual, eConn_union_of_subset_loops hL, eConn_dual]

lemma eConn_diff_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    M.eConn (X \ L) = M.eConn X := by
  rw [← eConn_dual, eConn_diff_of_subset_loops hL, eConn_dual]

lemma eConn_delete_eq_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    (M ＼ L).eConn X = M.eConn X := by
  rw [eConn_eq_eLocalConn, eLocalConn_delete_eq_of_subset_loops hL, delete_ground, diff_diff_comm,
    eLocalConn_diff_right_of_subset_loops hL, eConn_eq_eLocalConn]

lemma eConn_delete_eq_diff_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) :
    (M ＼ L).eConn X = M.eConn (X \ L) := by
  rw [eConn_delete_eq_of_subset_loops hL, eConn_diff_of_subset_loops hL]

lemma eConn_contract_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    (M ／ L).eConn X = M.eConn X := by
  rw [← eConn_dual, dual_contract, eConn_delete_eq_of_subset_loops hL, eConn_dual]

lemma eConn_contract_eq_diff_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) :
    (M ／ L).eConn X = M.eConn (X \ L) := by
  rw [← eConn_dual, dual_contract, eConn_delete_eq_diff_of_subset_loops hL, eConn_dual]

@[simp]
lemma eConn_loops (M : Matroid α) : M.eConn M.loops = 0 := by
  rw [← eConn_diff_of_subset_loops rfl.subset]
  simp

@[simp]
lemma eConn_coloops (M : Matroid α) : M.eConn M.coloops = 0 := by
  rw [← eConn_dual, ← dual_loops, eConn_loops]

@[simp]
lemma eConn_union_loops (M : Matroid α) (X : Set α) : M.eConn (X ∪ M.loops) = M.eConn X :=
  eConn_union_of_subset_loops rfl.subset

@[simp]
lemma eConn_union_coloops (M : Matroid α) (X : Set α) : M.eConn (X ∪ M.coloops) = M.eConn X :=
  eConn_union_of_subset_coloops rfl.subset

lemma eConn_subset_loops (h : X ⊆ M.loops) : M.eConn X = 0 := by
  rw [← empty_union X, eConn_union_of_subset_loops h, eConn_empty]

lemma eConn_subset_coloops (h : X ⊆ M.coloops) : M.eConn X = 0 := by
  rw [← empty_union X, eConn_union_of_subset_coloops h, eConn_empty]

lemma eConn_of_subset_loops_union_coloops (h : X ⊆ M.loops ∪ M.coloops) :
    M.eConn X = 0 := by
  rw [← diff_union_inter X M.coloops, eConn_union_of_subset_coloops inter_subset_right,
    eConn_subset_loops]
  rwa [diff_subset_iff, union_comm]

@[simp]
lemma uniqueBaseon_eConn (E B X : Set α) : (uniqueBaseOn B E).eConn X = 0 := by
  have hrw : X ∩ (uniqueBaseOn B E).E =
    ((X ∩ (uniqueBaseOn B E).loops) ∪ (X ∩ (uniqueBaseOn B E).coloops)) := by
    simp only [uniqueBaseOn_ground, uniqueBaseOn_loops_eq, uniqueBaseOn_coloops_eq']
    tauto_set
  rw [← eConn_inter_ground, hrw, eConn_union_of_subset_coloops inter_subset_right,
    eConn_subset_loops inter_subset_right]

lemma eRk_add_eRk_compl_eq (M : Matroid α) (X : Set α) :
    M.eRk X + M.eRk (M.E \ X) = M.eRank + M.eConn X := by
  rw [eConn_eq_eLocalConn, eRk_add_eRk_eq_eRk_union_add_eLocalConn, union_diff_self,
    ← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

lemma eConn_le_eRk (M : Matroid α) (X : Set α) : M.eConn X ≤ M.eRk X :=
  eLocalConn_le_eRk_left ..

lemma eConn_le_eRk_dual (M : Matroid α) (X : Set α) : M.eConn X ≤ M✶.eRk X :=
  by grw [← eConn_dual, eConn_le_eRk]

lemma eConn_le_encard (M : Matroid α) (X : Set α) : M.eConn X ≤ X.encard :=
  (eConn_le_eRk ..).trans (eRk_le_encard ..)

@[simp]
lemma freeOn_eConn (E X : Set α) : (freeOn E).eConn X = 0 := by
  rw [← eConn_dual, freeOn_dual_eq, loopyOn_eConn]

/-- The slack term in the inequality `λ(X) ≤ r(X)` is co-nullity -/
lemma eConn_add_nullity_dual_eq_eRk (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.eConn X + M✶.nullity X = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [eConn_eq_eLocalConn, hI.eLocalConn_eq_nullity_project_right, ← hI.encard_eq_eRk,
    M✶.nullity_eq_eRank_restrict_dual, ← delete_compl, dual_delete_dual, dual_ground,
    ← eRk_ground, contract_ground, diff_diff_cancel_left hX, ← eRk_closure_eq,
    ← contract_closure_congr hI.closure_eq_closure, eRk_closure_eq,
    nullity_project_eq_nullity_contract, add_comm, eRk_add_nullity_eq_encard]

lemma eConn_add_nullity_dual_eq_eRk' (M : Matroid α) (X : Set α) :
    M.eConn X + M✶.nullity X = M.eRk X + (X \ M.E).encard := by
  rw [← eRk_inter_ground, ← M.eConn_add_nullity_dual_eq_eRk (X ∩ M.E), eConn_inter_ground,
    nullity_eq_nullity_inter_ground_add_encard_diff, dual_ground, add_assoc]

/-- The slack term in the inequality `λ(X) ≤ r✶(X)` is nullity -/
lemma eConn_add_nullity_eq_eRk_dual (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.eConn X + M.nullity X = M✶.eRk X := by
  simp [← M✶.eConn_add_nullity_dual_eq_eRk X hX]

lemma Indep.eConn_eq_eRk_dual (hI : M.Indep I) : M.eConn I = M✶.eRk I := by
  rw [← eConn_add_nullity_eq_eRk_dual _ I hI.subset_ground, hI.nullity_eq, add_zero]

lemma eConn_add_eRank_eq (M : Matroid α) : M.eConn X + M.eRank = M.eRk X + M.eRk (M.E \ X) := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← eConn_inter_ground, aux inter_subset_right, eRk_inter_ground, diff_inter_self_eq_diff]
  rw [M.eRk_add_eRk_eq_eRk_union_add_eLocalConn, ← eConn_eq_eLocalConn, union_diff_cancel hXE,
    eRk_ground, add_comm]

lemma Indep.eConn_eq_of_compl_indep (hI : M.Indep I) (hI' : M.Indep (M.E \ I)) :
    M.eConn I = M✶.eRank := by
  rw [hI.eConn_eq_eRk_dual, ← hI'.coindep.compl_spanning.eRk_eq, dual_ground,
    diff_diff_cancel_left hI.subset_ground]

lemma eConn_union_eq_of_subset_loops {Y : Set α} (X : Set α) (hY : Y ⊆ M.loops) :
    M.eConn (X ∪ Y) = M.eConn X := by
  rw [eConn_eq_eLocalConn, ← diff_diff, ← eLocalConn_closure_closure, ← union_empty (a := _ \ _),
    ← closure_union_congr_right (closure_eq_loops_of_subset hY), diff_union_self,
    closure_union_congr_right (closure_eq_loops_of_subset hY),
    closure_union_congr_right (closure_eq_loops_of_subset hY), union_empty, union_empty,
    eLocalConn_closure_closure, ← eConn_eq_eLocalConn]

lemma eConn_union_eq_of_subset_coloops {Y : Set α} (X : Set α) (hY : Y ⊆ M.coloops) :
    M.eConn (X ∪ Y) = M.eConn X := by
  rw [← eConn_dual, eConn_union_eq_of_subset_loops _ (by simpa), eConn_dual]

/-- The slack term in the inequality `λ(X) ≤ |X|` is the sum of the nullity and conullity of `X`.
This needs `X ⊆ M.E`, for instance in the case where `X` is a single non-element. -/
lemma eConn_add_nullity_add_nullity_dual (M : Matroid α) (X : Set α)
  (hX : X ⊆ M.E := by aesop_mat) :
    M.eConn X + M.nullity X + M✶.nullity X = X.encard := by
  rw [eConn_add_nullity_eq_eRk_dual _ _ hX, eRk_add_nullity_eq_encard]

lemma eConn_add_nullity_add_nullity_dual' (M : Matroid α) (X : Set α) :
    M.eConn X + M.nullity X + M✶.nullity X = X.encard + (X \ M.E).encard := by
  rw [add_right_comm, eConn_add_nullity_dual_eq_eRk', add_right_comm, eRk_add_nullity_eq_encard]

lemma eConn_eq_eRk_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X = M.eRk X ↔ M✶.Indep X := by
  rw [← eConn_add_nullity_dual_eq_eRk _ _ hXE, eq_comm, ENat.add_eq_left_iff, or_iff_right hX,
    nullity_eq_zero]

lemma IsRkFinite.eConn_eq_eRk_iff (h : M.IsRkFinite X) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X = M.eRk X ↔ M✶.Indep X :=
  Matroid.eConn_eq_eRk_iff (fun h' ↦ (h.eRk_lt_top.trans_eq h'.symm).not_ge (M.eConn_le_eRk X)) hXE

lemma eConn_eq_encard_iff' (hX : M.eConn X ≠ ⊤) :
    M.eConn X = X.encard ↔ M.Indep X ∧ M.Coindep X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · refine iff_of_false (fun h_eq ↦ hXE ?_) fun h ↦ hXE h.1.subset_ground
    have hle := h_eq.symm.le
    grw [← eConn_inter_ground, ← encard_diff_add_encard_inter X M.E, eConn_le_encard,
      ENat.add_le_right_iff, encard_eq_zero, diff_eq_empty, or_iff_right hXE,
      ← top_le_iff, encard_le_encard inter_subset_left, ← h_eq, top_le_iff] at hle
    contradiction
  simp [← M.eConn_add_nullity_add_nullity_dual X, add_assoc, hX]

lemma eConn_eq_encard_iff (hX : X.Finite) : M.eConn X = X.encard ↔ M.Indep X ∧ M.Coindep X := by
  apply eConn_eq_encard_iff'
  grw [← lt_top_iff_ne_top, eConn_le_encard]
  exact hX.encard_lt_top

lemma eRk_add_eRk_dual_eq (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X + M✶.eRk X = M.eConn X + X.encard := by
  rw [← M.eRk_add_nullity_eq_encard X, add_comm _ (nullity ..), ← add_assoc,
    M.eConn_add_nullity_eq_eRk_dual X, add_comm]

lemma Indep.eConn_eq (hI : M.Indep I) : M.eConn I = M✶.eRk I := by
  rw [← M✶.eConn_add_nullity_dual_eq_eRk _ hI.subset_ground, dual_dual, hI.nullity_eq, add_zero,
    eConn_dual]

lemma Indep.eConn_eq_zero_iff (hI : M.Indep I) : M.eConn I = 0 ↔ I ⊆ M.coloops := by
  rw [coloops, ← eRk_eq_zero_iff, hI.eConn_eq]

lemma Coindep.eConn_eq_zero_iff (hI : M.Coindep I) : M.eConn I = 0 ↔ I ⊆ M.loops := by
  rw [← eConn_dual, Indep.eConn_eq_zero_iff hI, dual_coloops]

lemma Coindep.eConn_eq (hI : M.Coindep I) : M.eConn I = M.eRk I := by
  simpa using Indep.eConn_eq hI

lemma Spanning.eConn_eq (h : M.Spanning X) : M.eConn X = M.eRk (M.E \ X) := by
  rw [← h.compl_coindep.eConn_eq, eConn_compl]

lemma IsHyperplane.eConn_add_one_eq {H : Set α} (hH : M.IsHyperplane H) :
    M.eConn H + 1 = M.eRk (M.E \ H) := by
  rw [← eConn_compl, ← M.eConn_add_nullity_dual_eq_eRk (M.E \ H), nullity_compl_dual_eq,
    hH.eRelRk_eq_one]

lemma IsCocircuit.eConn_add_one_eq {C : Set α} (hC : M.IsCocircuit C) :
    M.eConn C + 1 = M.eRk C := by
  rw [← eConn_compl, hC.compl_isHyperplane.eConn_add_one_eq, diff_diff_cancel_left hC.subset_ground]

lemma IsCircuit.eConn_add_one_eq {C : Set α} (hC : M.IsCircuit C) :
    M.eConn C + 1 = M✶.eRk C := by
  rw [← hC.isCocircuit.eConn_add_one_eq, eConn_dual]

lemma eConn_eq_eRk_compl_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X = M.eRk (M.E \ X) ↔ M.Spanning X := by
  rw [← eConn_compl, eConn_eq_eRk_iff (by simpa), ← coindep_def, ← spanning_iff_compl_coindep]

lemma Indep.eConn_eq_encard_of_coindep (hI : M.Indep I) (hI' : M.Coindep I) :
    M.eConn I = I.encard := by
  rw [hI.eConn_eq, hI'.indep.eRk_eq_encard]

lemma eConn_lt_encard_iff' (hX : M.eConn X ≠ ⊤) :
    M.eConn X < X.encard ↔ ¬ M.Indep X ∨ ¬ M.Coindep X := by
  rw [lt_iff_le_and_ne, and_iff_right (eConn_le_encard ..), Ne, eConn_eq_encard_iff' hX,
    Classical.not_and_iff_not_or_not]

lemma eConn_lt_encard_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < X.encard ↔ M.Dep X ∨ M✶.Dep X := by
  rw [eConn_lt_encard_iff' hX, coindep_def, not_indep_iff, not_indep_iff]

lemma eConn_lt_encard_compl_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < (M.E \ X).encard ↔ ¬ M✶.Spanning X ∨ ¬ M.Spanning X := by
  rw [← eConn_compl, eConn_lt_encard_iff' (by simpa), coindep_iff_compl_spanning,
    diff_diff_cancel_left hXE, ← dual_coindep_iff, ← dual_ground, ← spanning_iff_compl_coindep]

lemma eConn_lt_eRk_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < M.eRk X ↔ ¬ M.Spanning (M.E \ X) := by
  rw [lt_iff_le_and_ne, and_iff_right (eConn_le_eRk ..), Ne, eConn_eq_eRk_iff hX, ← coindep_def,
    coindep_iff_compl_spanning]

lemma eConn_lt_eRk_compl_iff (hX : M.eConn X ≠ ⊤) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eConn X < M.eRk (M.E \ X) ↔ ¬ M.Spanning X := by
  rw [← eConn_compl, eConn_lt_eRk_iff (by simpa), diff_diff_cancel_left hXE]

@[simp]
lemma eConn_lt_top (M : Matroid α) [RankFinite M] (X : Set α) : M.eConn X < ⊤ :=
  eLocalConn_lt_top ..

@[simp]
lemma eConn_ne_top (M : Matroid α) [RankFinite M] (X : Set α) : M.eConn X ≠ ⊤ :=
  (eLocalConn_lt_top ..).ne

@[simp]
lemma eConn_lt_top' (M : Matroid α) [RankFinite M✶] (X : Set α) : M.eConn X < ⊤ := by
  rw [← eConn_dual]
  apply eConn_lt_top

@[simp]
lemma eConn_ne_top' (M : Matroid α) [RankFinite M✶] (X : Set α) : M.eConn X ≠ ⊤ :=
  (eConn_lt_top' ..).ne

lemma eConn_le_of_subset_of_subset_closure {Y : Set α} (M : Matroid α)
    (hXY : X ⊆ Y) (hYX : Y ⊆ M.closure X) : M.eConn Y ≤ M.eConn X := by
  grw [eConn_eq_eLocalConn, eLocalConn_mono_left _ hYX, eLocalConn_closure_left,
    eLocalConn_mono_right _ _ (diff_subset_diff_right hXY), eConn_eq_eLocalConn]

lemma eConn_closure_le (M : Matroid α) (X : Set α) : M.eConn (M.closure X) ≤ M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · grw [← M.closure_inter_ground X, aux _ inter_subset_right, eConn_inter_ground]
  grw [eConn_eq_eLocalConn, eLocalConn_closure_left, eConn_eq_eLocalConn,
    M.eLocalConn_mono_right X (diff_subset_diff_right (M.subset_closure X))]

@[simp]
lemma eConn_disjointSum_left_eq {M₁ M₂ : Matroid α} (hdj : Disjoint M₁.E M₂.E) :
    (M₁.disjointSum M₂ hdj).eConn M₁.E = 0 := by
  rw [eConn, eLocalConn_eq_zero (by simp) (by tauto_set)]
  simp [hdj.sdiff_eq_right, skew_disjointSum]

@[simp]
lemma eConn_disjointSum_right_eq {M₁ M₂ : Matroid α} (hdj : Disjoint M₁.E M₂.E) :
    (M₁.disjointSum M₂ hdj).eConn M₂.E = 0 := by
  rw [disjointSum_comm]
  simp

lemma eConn_eq_zero_of_subset_loops {L : Set α} (hL : L ⊆ M.loops) : M.eConn L = 0 := by
  rw [eConn_eq_eLocalConn, ← eLocalConn_diff_left_of_subset_loops hL]
  simp

lemma eConn_eq_zero_of_subset_coloops {L : Set α} (hL : L ⊆ M.coloops) : M.eConn L = 0 := by
  rw [← eConn_dual]
  exact eConn_eq_zero_of_subset_loops <| by simpa

lemma IsLoop.eConn_eq_zero {e : α} (he : M.IsLoop e) : M.eConn {e} = 0 :=
  eConn_eq_zero_of_subset_loops <| by simpa

lemma IsColoop.eConn_eq_zero {e : α} (he : M.IsColoop e) : M.eConn {e} = 0 :=
  eConn_eq_zero_of_subset_coloops <| by simpa

lemma eConn_singleton_eq_zero_iff {e : α} (heM : e ∈ M.E) :
    M.eConn {e} = 0 ↔ M.IsLoop e ∨ M.IsColoop e := by
  rw [iff_def, or_imp, and_iff_right IsLoop.eConn_eq_zero, and_iff_left IsColoop.eConn_eq_zero]
  intro h
  obtain he | he := M.isLoop_or_isNonloop e
  · exact .inl he
  rw [he.indep.eConn_eq_zero_iff, singleton_subset_iff] at h
  exact .inr h

/-- Connectivity is submodular -/
lemma eConn_inter_add_eConn_union_le (M : Matroid α) (X Y : Set α) :
    M.eConn (X ∩ Y) + M.eConn (X ∪ Y) ≤ M.eConn X + M.eConn Y :=
  M.eConnAux_submod X Y

alias eConn_submod := eConn_inter_add_eConn_union_le

lemma stronglyPreservable_eConn : StronglyPreservable (α := α) (fun M X ↦ M.eConn X) :=
  stronglyPreservable_eConnAux
