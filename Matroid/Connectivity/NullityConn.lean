import Matroid.Connectivity.Separation
import Matroid.Connectivity.Minor
import Mathlib.Tactic.Peel

open Set

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b d k : ℕ∞} {A : Set α} {P : M.Partition}

namespace Matroid

namespace Partition

/-- A generalized notion of separation, which specializes to vertical and Tutte separations.
The parameters `a` and `b` specify how much rank and corank contribute to the nontriviality
notion, while the parameter `d` measures the threshold for nontriviality.
For vertical, cyclical and Tutte connectivity, we have `d = 0` and `a,b ∈ {0,1}`.
For internal connectivity, we also use `d = 1`. Larger `d` would be relevant for
`(f,k)`-connectivity

For Tutte connectivity, the relevant nontriviality notion (with `a,b,d = 1,1,0`)
is `0 < M.nullity X + M✶.nullity X`, as opposed to the traditional `M.eConn X < X.encard`.
These two are equivalent for sets of finite connectivity, but not infinite.

-/
@[mk_iff]
structure IsDSeparation (P : M.Partition) (a b d : ℕ∞) : Prop where
  le_left : d < a * M.nullity P.left + b * M✶.nullity P.left
  le_right : d < a * M.nullity P.right + b * M✶.nullity P.right

lemma IsDSeparation.mono_left (h : P.IsDSeparation a b d) {a' : ℕ∞} (ha : a ≤ a') :
    P.IsDSeparation a' b d := by
  grw [isDSeparation_iff, ← ha, ← isDSeparation_iff]
  assumption

lemma IsDSeparation.mono_right (h : P.IsDSeparation a b d) {b' : ℕ∞} (hb : b ≤ b') :
    P.IsDSeparation a b' d := by
  grw [isDSeparation_iff, ← hb, ← isDSeparation_iff]
  assumption

lemma IsDSeparation.mono_threshold (h : P.IsDSeparation a b d) {d' : ℕ∞} (hd : d' ≤ d) :
    P.IsDSeparation a b d' := by
  grw [isDSeparation_iff, hd, ← isDSeparation_iff]
  assumption

@[simp]
lemma isDSeparation_dual_iff : P.dual.IsDSeparation a b d ↔ P.IsDSeparation b a d := by
  rw [isDSeparation_iff, and_comm, isDSeparation_iff, add_comm, add_comm (a * _), and_comm,
    dual_dual, dual_left, dual_right]

@[simp]
lemma isDSeparation_symm_iff : P.symm.IsDSeparation a b d ↔ P.IsDSeparation a b d := by
  rw [isDSeparation_iff, and_comm, isDSeparation_iff, symm_left, symm_right]


lemma IsDSeparation.symm (hP : P.IsDSeparation a b d) : P.symm.IsDSeparation a b d := by
  simpa

/-- A Tutte separation is one where each side has positive nullity or conullity.  -/
abbrev IsTutteSeparation (P : M.Partition) := P.IsDSeparation 1 1 0

@[simp]
lemma isDSeparation_one_one_zero_iff : P.IsDSeparation 1 1 0 ↔ P.IsTutteSeparation := Iff.rfl

/-- A vertical separation is one where each side has positive conullity.  -/
abbrev IsVerticalSeparation (P : M.Partition) := P.IsDSeparation 0 1 0

lemma IsDSeparation.nonempty_left (h : P.IsDSeparation a b d) : P.left.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro h0
  simp [isDSeparation_iff, h0] at h

lemma IsDSeparation.nonempty_right (h : P.IsDSeparation a b d) : P.right.Nonempty := by
  simpa using h.symm.nonempty_left

@[simp]
lemma isDSeparation_zero_one_one_iff : P.IsDSeparation 0 1 0 ↔ P.IsVerticalSeparation := Iff.rfl

lemma isTutteSeparation_iff_dep_or_dep :
    P.IsTutteSeparation ↔ (M.Dep P.left ∨ M✶.Dep P.left) ∧ (M.Dep P.right ∨ M✶.Dep P.right) := by
  simp only [IsTutteSeparation, isDSeparation_iff, one_mul, pos_iff_ne_zero, ne_eq, add_eq_zero,
    nullity_eq_zero, not_and, dual_ground, Partition.left_subset_ground,
    Partition.right_subset_ground, ← not_dep_iff, not_not]
  tauto

lemma isVerticalSeparation_iff :
    P.IsVerticalSeparation ↔ ¬ M.Spanning P.left ∧ ¬ M.Spanning P.right := by
  simp only [IsVerticalSeparation, isDSeparation_iff, zero_mul, one_mul, zero_add, pos_iff_ne_zero,
    ne_eq, nullity_eq_zero, dual_ground, Partition.left_subset_ground, not_indep_iff,
    Partition.right_subset_ground]
  rw [← not_indep_iff, ← not_indep_iff, ← coindep_def, ← compl_right, and_comm,
    ← spanning_iff_compl_coindep, ← coindep_def, ← compl_left, ← spanning_iff_compl_coindep,
    compl_left, compl_right]

lemma isTutteSeparation_iff_encard_lt (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ P.eConn < P.left.encard ∧ P.eConn < P.right.encard := by
  rw [isTutteSeparation_iff_dep_or_dep, ← eConn_lt_encard_iff (by simpa),
      ← eConn_lt_encard_iff (by simpa), P.eConn_left, P.eConn_right]

lemma IsTutteSeparation.nonempty_left (h : P.IsTutteSeparation) : P.left.Nonempty :=
  IsDSeparation.nonempty_left h

lemma isVerticalSeparation_iff_encard_lt (hP : P.eConn ≠ ⊤) :
    P.IsVerticalSeparation ↔ P.eConn < M.eRk P.left ∧ P.eConn < M.eRk P.right := by
  simp only [IsVerticalSeparation, isDSeparation_iff, zero_mul, one_mul, zero_add, pos_iff_ne_zero,
    ne_eq, nullity_eq_zero, dual_ground, Partition.left_subset_ground, not_indep_iff,
    Partition.right_subset_ground]
  rw [← eConn_left, eConn_lt_eRk_iff (by simpa), compl_left, eConn_left, ← eConn_right,
    eConn_lt_eRk_iff (by simpa), spanning_iff_compl_coindep, compl_right, coindep_def,
    not_indep_iff, spanning_iff_compl_coindep, compl_left, coindep_def, not_indep_iff]

end Partition

def IsfDConnected (M : Matroid α) (a b : ℕ∞) (f : ℕ∞ → ℕ∞) : Prop :=
    ∀ (P : M.Partition), ¬ P.IsDSeparation a b (f P.eConn)

def IsDConnected (M : Matroid α) (a b d k : ℕ∞) : Prop :=
    ∀ (P : M.Partition), P.eConn + 1 < k → ¬ P.IsDSeparation a b d

lemma IsDConnected.mono_left (h : M.IsDConnected a b d k) {a' : ℕ∞} (ha' : a' ≤ a) :
    M.IsDConnected a' b d k :=
  fun P hP hsep ↦ h P hP (hsep.mono_left ha')

lemma IsDConnected.mono_right (h : M.IsDConnected a b d k) {b' : ℕ∞} (hb' : b' ≤ b) :
    M.IsDConnected a b' d k :=
  fun P hP hsep ↦ h P hP (hsep.mono_right hb')

lemma IsDConnected.mono (h : M.IsDConnected a b d k) (hj : j ≤ k) : M.IsDConnected a b d j :=
  fun P hP hsep ↦ h P (hP.trans_le hj) hsep

def IsTutteConnected (M : Matroid α) (k : ℕ∞) : Prop := M.IsDConnected 1 1 0 k

lemma foo : M.IsTutteConnected k ↔ M.IsfDConnected 1 1 (fun t ↦ if t + 1 < k then 0 else ⊤) := by
  simp [IsTutteConnected, IsDConnected, IsfDConnected]
  refine ⟨fun h P hP ↦ ?_, fun h P hP hsep ↦ h P (by simpa [hP])⟩
  split_ifs at hP with hlt
  · exact h P hlt hP
  simp [Partition.isDSeparation_iff] at hP

def IsInternallyConnected' (M : Matroid α) (k : ℕ∞) :=
    M.IsfDConnected 1 1 (fun t ↦ if t + 2 < k then 0 else if t + 1 < k then 1 else ⊤)

lemma ground_indep_iff_empty_isBase_dual : M.Indep M.E ↔ M✶.IsBase ∅ := by
  rw [ground_indep_iff_isBase, ← M.dual_dual, dual_isBase_iff, M✶.dual_ground, diff_self,
    dual_dual]

lemma isTutteConnected_two_iff [M.Nonempty] : M.IsTutteConnected 2 ↔ M.Connected := by
  simp only [IsTutteConnected, IsDConnected, ← one_add_one_eq_two,
    ENat.add_one_lt_add_one_iff, ENat.lt_one_iff,
    Partition.isDSeparation_one_one_zero_iff]
  refine ⟨fun h ↦ by_contra fun hM ↦ ?_, fun hP P hPconn hPsep ↦ ?_⟩
  · obtain ⟨M₁, M₂, hdj, h₁, h₂, rfl⟩ := eq_disjointSum_of_not_connected hM
    have h' : ¬M₁.Indep M₁.E ∨ ¬M₁✶.Indep M₁.E → M₂.Indep M₂.E ∧ M₂✶.Indep M₂.E := by
      simpa [Partition.isTutteSeparation_iff_dep_or_dep, ← not_indep_iff, hdj.inter_eq,
        hdj.sdiff_eq_right, hdj.symm.inter_eq] using h (Matroid.partition _ M₁.E)
    rw [ground_indep_iff_empty_isBase_dual, ground_indep_iff_empty_isBase_dual,
      ← M₁.dual_ground, ← M₂.dual_ground, ground_indep_iff_empty_isBase_dual, dual_dual,
      ground_indep_iff_empty_isBase_dual, dual_dual, ← Classical.not_and_iff_not_or_not,
      ← or_iff_not_imp_left] at h'
    obtain ⟨h1,h2⟩ | ⟨h1,h2⟩ := h'
    · rw [← ground_nonempty_iff, ← encard_ne_zero, ← eRank_add_eRank_dual,
        ← h1.encard_eq_eRank, ← h2.encard_eq_eRank] at h₁
      simp at h₁
    rw [← ground_nonempty_iff, ← encard_ne_zero, ← eRank_add_eRank_dual,
        ← h1.encard_eq_eRank, ← h2.encard_eq_eRank] at h₂
    simp at h₂
  rw [Partition.eConn_eq_zero_iff_eq_disjointSum] at hPconn
  rw [hPconn] at hP
  refine disjointSum_not_connected ?_ ?_ _ hP
  · rw [← ground_nonempty_iff]
    exact hPsep.nonempty_left
  rw [← ground_nonempty_iff]
  exact hPsep.nonempty_right

/-- An internally `k`-connected matroid is a `(k-1)`-connected matroid where every set
`A` with `λ(A) = k - 2` satisfies `|A| = k-1` or `|E - A| = k-1`. -/
def IsInternallyConnected (M : Matroid α) (k : ℕ∞) :=
    M.IsTutteConnected (k - 1) ∧ M.IsDConnected 1 1 1 k

end Matroid
