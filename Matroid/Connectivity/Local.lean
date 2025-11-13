import Matroid.Connectivity.Multi

open Set Set.Notation Function

set_option linter.style.longLine false

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X Y : Set α}

section eLocalConn

-- /- If `X` and `Y` are sets, then `|I ∩ J| + M.nullity (I ∪ J)` has the same value for
-- every isBasis `I` of `X` and `J` of `Y`. --/
-- lemma IsBasis'.encard_add_nullity_congr (hI : M.IsBasis' I X) (hI' : M.IsBasis' I' X)
--     (hJ : M.IsBasis' J Y) (hJ' : M.IsBasis' J' Y) :
--     (I ∩ J).encard + M.nullity (I ∪ J) = (I' ∩ J').encard + M.nullity (I' ∪ J') := by
--   rw [add_comm, ← nullity_project_add_nullity_eq, add_comm (encard _),
--     ← nullity_project_add_nullity_eq, hJ.indep.nullity_eq, hJ'.indep.nullity_eq,
--     ← hJ.project_eq_project, ← hJ'.project_eq_project, hI.nullity_project hI']



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

@[simp]
lemma cast_localConn_eq (M : Matroid α) [M.RankFinite] (X Y : Set α) :
    (M.localConn X Y : ℕ∞) = M.eLocalConn X Y :=
  (M.isRkFinite_set Y).cast_localConn_left_eq

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

lemma IsRkFinite.localConn_le_rk_left (hX : M.IsRkFinite X) (Y : Set α) :
    M.localConn X Y ≤ M.rk X := by
  rw [← Nat.cast_le (α := ℕ∞), hX.cast_localConn_right_eq, hX.cast_rk_eq]
  exact M.eLocalConn_le_eRk_left X Y

lemma IsRkFinite.localConn_le_rk_right (hX : M.IsRkFinite Y) (X : Set α) :
    M.localConn X Y ≤ M.rk Y := by
  grw [localConn_comm, hX.localConn_le_rk_left]

lemma localConn_le_ncard_left (M : Matroid α) (hX : X.Finite) (Y : Set α) :
    M.localConn X Y ≤ X.ncard := by
  grw [IsRkFinite.localConn_le_rk_left (M.isRkFinite_of_finite hX), ← Nat.cast_le (α := ℕ∞),
    (M.isRkFinite_of_finite hX).cast_rk_eq, hX.cast_ncard_eq]
  exact M.eRk_le_encard X

lemma localConn_le_ncard_right (M : Matroid α) (hY : Y.Finite) (X : Set α) :
    M.localConn X Y ≤ Y.ncard := by
  grw [localConn_comm, localConn_le_ncard_left _ hY]

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
    M.eConn X = M.eLocalConn (X ∩ M.E) (M.E \ X) := by
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

lemma eRk_add_eRk_compl_eq (M : Matroid α) (X : Set α) :
    M.eRk X + M.eRk (M.E \ X) = M.eRank + M.eConn X := by
  rw [eConn_eq_eLocalConn, eRk_add_eRk_eq_eRk_union_add_eLocalConn, union_diff_self,
    ← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

lemma eConn_le_eRk (M : Matroid α) (X : Set α) : M.eConn X ≤ M.eRk X :=
  eLocalConn_le_eRk_left _ _ _

lemma eConn_le_encard (M : Matroid α) (X : Set α) : M.eConn X ≤ X.encard :=
  (eConn_le_eRk ..).trans (eRk_le_encard ..)

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
    M.eConn X = X.encard ↔ M.Indep X ∧ M✶.Indep X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · refine iff_of_false (fun h_eq ↦ hXE ?_) fun h ↦ hXE h.1.subset_ground
    have hle := h_eq.symm.le
    grw [← eConn_inter_ground, ← encard_diff_add_encard_inter X M.E, eConn_le_encard,
      ENat.add_le_right_iff, encard_eq_zero, diff_eq_empty, or_iff_right hXE,
      ← top_le_iff, encard_le_encard inter_subset_left, ← h_eq, top_le_iff] at hle
    contradiction
  simp [← M.eConn_add_nullity_add_nullity_dual X, add_assoc, hX]

lemma encard_le_eConn_iff (hX : X.Finite) : M.eConn X = X.encard ↔ M.Indep X ∧ M✶.Indep X := by
  apply eConn_eq_encard_iff'
  grw [← lt_top_iff_ne_top, eConn_le_encard]
  exact hX.encard_lt_top



-- lemma eConn_eq_encard_iff (hX : X.Finite) : M.eConn X = X.encard ↔ M.Indep X ∧ M✶.Indep X := by
--   rw [le_antisymm_iff, and_iff_right (M.eConn_le_encard ..), encard_le_eConn_iff hX]



--   ·
--
--     grw [← eConn_inter_ground, ← encard_diff_add_encard_inter X M.E, eConn_le_encard,
--       ENat.add_le_right_iff, encard_eq_zero, diff_eq_empty, or_iff_right hXE] at hle



    -- specialize aux (X := X ∩ M.E) (by simpa) inter_subset_right

    -- (le_antisymm (M.eConn_le_encard ..) ?_)

  -- obtain hX' | hX' := X.finite_or_infinite
  -- · sorry
  -- refine iff_of_false (fun h ↦ hX (by simpa [hX'.encard_eq] using h)) fun ⟨hi, hi'⟩ ↦ hX ?_
  -- rw [← encard_eq_top_iff, eConn_add] at hX'



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

lemma IsRankFinite.conn_le_rk (h : M.IsRkFinite X) : M.conn X ≤ M.rk X := by
  have hwin := M.eConn_le_eRk X
  rwa [eConn, ← h.cast_localConn_right_eq, ← conn_eq_localConn, ← h.cast_rk_eq, Nat.cast_le] at hwin

lemma conn_le_ncard (M : Matroid α) (h : X.Finite) : M.conn X ≤ X.ncard := by
  grw [conn_eq_localConn, localConn_le_ncard_left _ h]

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
