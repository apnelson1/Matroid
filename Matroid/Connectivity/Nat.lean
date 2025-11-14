import Matroid.Connectivity.Basic

variable {α : Type*} {M : Matroid α} {X Y I C D : Set α} {e : α}

open Set

namespace Matroid

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


section conn

/-- The `ℕ`-valued connectivity of a set `X` to its complement, traditionally written `λ (X)`.
Being `ℕ`-valued, this is not well-behaved unless `M` or its dual has finite rank,
since a set with infinite connectivity to its complement has a `conn` of zero.
If neither `M` nor `M✶` is known to have finite rank, then `Matroid.eConn` is better. -/
noncomputable def conn (M : Matroid α) (X : Set α) : ℕ := (M.eConn X).toNat

@[simp] lemma conn_dual (M : Matroid α) (X : Set α) : M✶.conn X = M.conn X := by
  rw [conn, eConn_dual, conn]

@[simp] lemma conn_empty (M : Matroid α) : M.conn ∅ = 0 := by
  simp [conn]

@[simp] lemma conn_ground (M : Matroid α) : M.conn M.E = 0 := by
  simp [conn]

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

/-- Generalizes submodularity of `conn`.  -/
theorem conn_inter_add_conn_union_union_le (M : Matroid α) [M.RankFinite] {C D X : Set α}
    (hC : Disjoint C X) (hXD : Disjoint D X) :
    M.conn (C ∩ D) + M.conn (X ∪ C ∪ D) ≤ (M ／ X).conn C + (M ＼ X).conn D + M.conn X := by
  have hsm1 := M.rk_submod (M.E \ C) (M.E \ (X ∪ D))
  have hsm2 := M.rk_submod (C ∪ X) D
  zify at *
  simp only [intCast_conn_eq, contract_rk_cast_int_eq, contract_ground, contract_rank_cast_int_eq,
    delete_ground]
  rw [diff_diff_comm, diff_union_self, ← M.rk_inter_ground (M.E \ C ∪ X), union_inter_distrib_right,
    inter_eq_self_of_subset_left diff_subset,
    union_eq_self_of_subset_right (t := X ∩ M.E) (by tauto_set),
    diff_diff, delete_rk_eq_of_disjoint M hXD, delete_rk_eq_of_disjoint _ (by tauto_set),
    ← (M ＼ X).rk_ground, delete_ground, delete_rk_eq_of_disjoint _ disjoint_sdiff_left]
  rw [diff_inter_diff, union_comm, union_right_comm, ← diff_inter, inter_union_distrib_left,
    hC.inter_eq, empty_union] at hsm1
  rw [union_inter_distrib_right, hXD.symm.inter_eq, union_empty, union_right_comm, union_comm,
    ← union_assoc] at hsm2
  linarith

/-- The function `M.conn` is submodular.
This is also true for `eConn` without `RankFinite`, but the proof will be more difficult. TODO. -/
lemma conn_submod (M : Matroid α) [RankFinite M] (X Y : Set α) :
    M.conn (X ∩ Y) + M.conn (X ∪ Y) ≤ M.conn X + M.conn Y := by
  simpa using M.conn_inter_add_conn_union_union_le (disjoint_empty X) (disjoint_empty Y)

/-- The Bixby-Coullard inequality -/
theorem conn_inter_add_conn_insert_union_le (M : Matroid α) [M.RankFinite]
    (heC : e ∉ C) (heD : e ∉ D) :
    M.conn (C ∩ D) + M.conn (insert e (C ∪ D)) ≤ (M ／ {e}).conn C + (M ＼ {e}).conn D + 1 := by
  grw [← singleton_union, ← union_assoc, M.conn_inter_add_conn_union_union_le (by simpa) (by simpa),
    M.conn_le_ncard (finite_singleton e), ncard_singleton]

end conn
