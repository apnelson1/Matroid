import Matroid.Connectivity.Separation
import Matroid.Connectivity.Minor
import Mathlib.Tactic.Peel

open Set

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {a b d k : ℕ∞} {A : Set α} {P : M.Partition}

namespace Matroid



section abstract

variable {nt nt' : Matroid α → Set α → Prop}

namespace Partition

@[mk_iff]
structure IsPredSeparation (nontrivial : Matroid α → Set α → Prop) (P : M.Partition) : Prop where
    nontrivial_left : nontrivial M P.left
    nontrivial_right : nontrivial M P.right

lemma IsPredSeparation.dual (hnt : ∀ ⦃M X⦄, X ⊆ M.E → nt M X → nt' M✶ X)
    (hP : P.IsPredSeparation nt) : P.dual.IsPredSeparation nt' :=
  ⟨hnt P.left_subset_ground hP.1, hnt P.right_subset_ground hP.2⟩

lemma IsPredSeparation.dual_compl (hnt : ∀ ⦃M X⦄, X ⊆ M.E → nt M X → nt' M✶ (M.E \ X))
    (hP : P.IsPredSeparation nt) : P.dual.IsPredSeparation nt' :=
  ⟨P.compl_right ▸ hnt P.right_subset_ground hP.2, P.compl_left ▸ hnt P.left_subset_ground hP.1⟩

lemma IsPredSeparation.of_dual (hnt : ∀ ⦃M X⦄, X ⊆ M.E → nt M X → nt M✶ X)
    (hP : P.dual.IsPredSeparation nt) : P.IsPredSeparation nt :=
  ⟨by simpa using (hP.dual hnt).1, by simpa using (hP.dual hnt).2⟩

lemma isPredSeparation_dual_iff (hnt : ∀ ⦃M X⦄, X ⊆ M.E → nt M X → nt M✶ X) :
    P.dual.IsPredSeparation nt ↔ P.IsPredSeparation nt :=
  ⟨IsPredSeparation.of_dual hnt, IsPredSeparation.dual hnt⟩

lemma IsPredSeparation.symm (hP : P.IsPredSeparation nt) : P.symm.IsPredSeparation nt :=
  ⟨hP.2, hP.1⟩

lemma IsPredSeparation.of_symm (hP : P.symm.IsPredSeparation nt) : P.IsPredSeparation nt :=
  ⟨hP.2, hP.1⟩

@[simp]
lemma isPredSeparation_symm_eq : P.symm.IsPredSeparation = P.IsPredSeparation := by
  ext nt
  exact ⟨IsPredSeparation.of_symm, IsPredSeparation.symm⟩

lemma IsPredSeparation.mono {nt nt' : Matroid α → Set α → Prop}
    (h_imp : ∀ ⦃M X⦄, X ⊆ M.E → nt M X → nt' M X) (hP : P.IsPredSeparation nt) :
    P.IsPredSeparation nt' :=
  ⟨h_imp P.left_subset_ground hP.1, h_imp P.right_subset_ground hP.2⟩

lemma IsPredSeparation.mono_symm {nt nt' : Matroid α → Set α → Prop}
    (h_imp : ∀ ⦃M X⦄, X ⊆ M.E → nt M X → nt' M (M.E \ X)) (hP : P.IsPredSeparation nt) :
    P.IsPredSeparation nt' :=
  ⟨P.compl_right ▸ h_imp P.right_subset_ground hP.2,
    P.compl_left ▸ h_imp P.left_subset_ground hP.1⟩

def IsTutteSeparation' (P : M.Partition) := IsPredSeparation (fun M X ↦ M.Dep X ∨ M✶.Dep X) P

def IsVerticalSeparation' (P : M.Partition) := IsPredSeparation (fun M X ↦ ¬ M.Spanning X) P

def IsCyclicSeparation' (P : M.Partition) := IsPredSeparation Matroid.Dep P

lemma IsTutteSeparation'.dual (h : P.IsTutteSeparation') : P.dual.IsTutteSeparation' :=
  IsPredSeparation.dual (by simp [or_comm]) h

lemma IsTutteSeparation'.of_dual (h : P.dual.IsTutteSeparation') : P.IsTutteSeparation' :=
  IsPredSeparation.of_dual (by simp [or_comm]) h

lemma IsVerticalSeparation'.IsTutteSeparation' (h : P.IsVerticalSeparation') :
    P.IsTutteSeparation' :=
  h.mono_symm fun M X hXE hsp ↦ .inr <| by rwa [dep_compl_dual_iff_not_spanning]

lemma IsVerticalSeparation'.dual (h : P.IsVerticalSeparation') : P.dual.IsCyclicSeparation' :=
  h.dual_compl fun M X hX hsp ↦ by rwa [dep_compl_dual_iff_not_spanning]

lemma IsCyclicSeparation'.dual (h : P.IsCyclicSeparation') : P.dual.IsVerticalSeparation' :=
  h.dual_compl fun M X hX hd ↦ by rwa [spanning_compl_dual_iff, not_indep_iff]

lemma IsCyclicSeparation'.IsTutteSeparation' (h : P.IsCyclicSeparation') :
    P.IsTutteSeparation' :=
  h.dual.IsTutteSeparation'.of_dual

end Partition

variable {degen degen' : ℕ∞ → (M : Matroid α) → Set α → Prop}

/-- An abstract notion of connectivity. `degen` is a predicate-valued function that for each `t`,
specifies what it means for a set `X` with connectivity `t` to be degenerate in a matroid `M`.
`PredConnected degen M` means that in `M`, every set of connectivity `t` either satisfies
`degen t`, or its complement satisfies `degen t`.

For instance, for `k`-Tutte-connectivity, sets of connectivity `k-1` or higher are not degenerate,
and sets of connectivity `k-2` or less are degenerate iff they are independent and coindependent. -/
def PredConnected (degen : ℕ∞ → (M : Matroid α) → Set α → Prop) (M : Matroid α) :=
    ∀ P : M.Partition, degen P.eConn M P.left ∨ degen P.eConn M P.right

lemma PredConnected.mono'
    (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → degen k M X → (degen' k M X ∨ degen' k M (M.E \ X)))
    (h : M.PredConnected degen) : M.PredConnected degen' := by
  refine fun P ↦ ?_
  obtain h1 | h2 := h P
  · exact P.compl_left ▸ hdegen P.left_subset_ground h1
  rw [or_comm]
  exact P.compl_right ▸ hdegen P.right_subset_ground h2

lemma PredConnected.mono (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → degen k M X → degen' k M X)
    (h : M.PredConnected degen) : M.PredConnected degen' :=
  h.mono' fun _ _ _ hX h' ↦ .inl (hdegen hX h')

lemma PredConnected.mono_compl (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → degen k M X → degen' k M (M.E \ X))
    (h : M.PredConnected degen) : M.PredConnected degen' :=
  h.mono' fun _ _ _ hX h' ↦ .inr (hdegen hX h')

lemma PredConnected.dual' (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → degen k M X →
    (degen' k M✶ X ∨ degen' k M✶ (M.E \ X))) (h : M.PredConnected degen) :
    M✶.PredConnected degen' :=
  fun P ↦ by simpa using h.mono' (degen' := fun k N Y ↦ degen' k N✶ Y) (by simpa) P.ofDual

lemma PredConnected.dual_compl (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → degen k M X → degen' k M✶ (M.E \ X))
    (h : M.PredConnected degen) : M✶.PredConnected degen' :=
  fun P ↦ by simpa using h.mono_compl (degen' := fun k N Y ↦ degen' k N✶ Y) (by simpa) P.ofDual

lemma PredConnected.dual (hdegen : ∀ ⦃k M X⦄, X ⊆ M.E → degen k M X → degen' k M✶ X)
    (h : M.PredConnected degen) : M✶.PredConnected degen' :=
  fun P ↦ by simpa using h.mono (degen' := fun k N Y ↦ degen' k N✶ Y) (by simpa) P.ofDual

section Tutte

def TutteConnected (M : Matroid α) (k : ℕ∞) :=
    M.PredConnected (fun j M X ↦ j + 2 ≤ k → M.Indep X ∧ M.Coindep X)

lemma TutteConnected.dual (h : M.TutteConnected k) : M✶.TutteConnected k := by
  refine PredConnected.dual (fun t N X hX h' hle ↦ ?_) h
  rw [dual_coindep_iff, and_comm]
  exact h' hle

lemma TutteConnected.of_dual (h : M✶.TutteConnected k) : M.TutteConnected k :=
  M.dual_dual ▸ h.dual

@[simp]
lemma tutteConnected_dual : M✶.TutteConnected = M.TutteConnected := by
  ext k
  exact ⟨TutteConnected.of_dual, TutteConnected.dual⟩

lemma not_TutteConnected_iff_exists : ¬ M.TutteConnected k ↔ ∃ X ⊆ M.E, M.eConn X + 2 ≤ k ∧
    (M.Spanning (M.E \ X) → M.Dep X) ∧ (M.Spanning X → M.Dep (M.E \ X)) := by
  simp only [TutteConnected, PredConnected, not_forall, not_or, exists_prop, not_and,
    dual_ground, Partition.left_subset_ground, not_indep_iff, dep_dual_iff_compl_not_spanning,
    Partition.right_subset_ground, and_and_and_comm, and_self]
  refine ⟨fun ⟨P, hPconn, hP1, hP2⟩ ↦ ⟨_, P.left_subset_ground, by simpa,
    fun hi ↦ by simpa [hi] using hP1,
    fun hi ↦ by simpa [P.compl_left, P.compl_right, hi] using hP2⟩,
    fun ⟨X, hXE, hXconn, hX1, hX2⟩ ↦
      ⟨M.partition X, by simpa, fun hi hsp ↦ hi.not_dep (hX1 hsp),
        fun hi hsp ↦ (hX2 ?_).not_indep hi⟩⟩
  rwa [Partition.compl_right] at hsp


lemma Indep.exists_isTutteSeparation_of_not_coindep {I : Set α} (hI : M.Indep I)
    (hd : ¬ M.Coindep I) :
    ∃ P : M.Partition, P.left ⊆ I ∧ M.IsCocircuit P.left ∧ P.eConn ≤ M.eConn I := by
  rw [coindep_def, not_indep_iff] at hd
  obtain ⟨C, hCI, hC⟩ := hd.exists_isCircuit_subset
  refine ⟨M.partition C, hCI, hC, ?_⟩
  grw [← Partition.eConn_left, partition_left _ _, (hI.subset hCI).eConn_eq, hI.eConn_eq]
  exact M✶.eRk_mono hCI


lemma exists_dep_nonspanning_or_small_of_not_tutteConnected (h : ¬ M.TutteConnected k) :
    ∃ X ⊆ M.E, M.eConn X + 2 ≤ k ∧
      (((M.Dep X ∧ M.Dep (M.E \ X) ∧ ¬ M.Spanning X ∧ ¬ M.Spanning (M.E \ X)))
    ∨ (M.Indep X ∧ M.IsCocircuit X ∧ X.encard + 1 ≤ k)
    ∨ (M.Spanning (M.E \ X) ∧ M.IsCircuit X ∧ X.encard + 1 ≤ k)) := by
  simp only [TutteConnected, PredConnected, not_forall, not_or, not_and, exists_prop,
    dual_ground, Partition.left_subset_ground, not_indep_iff, Partition.right_subset_ground] at h
  obtain ⟨P, ⟨-, hP1⟩, ⟨hPconn, hP2⟩⟩ := h
  have dual_symm_claim {N : Matroid α} {Y : Set α}
      (h : N✶.Dep Y ∧ N✶.Dep (N✶.E \ Y) ∧ ¬ N✶.Spanning Y ∧ ¬ N✶.Spanning (N✶.E \ Y))  :
      (N.Dep Y ∧ N.Dep (N.E \ Y) ∧ ¬ N.Spanning Y ∧ ¬ N.Spanning (N.E \ Y)) := by
    have hYE : Y ⊆ N.E := h.1.subset_ground
    rw [dual_ground, dep_dual_iff_compl_not_spanning, dep_compl_dual_iff_not_spanning,
      spanning_dual_iff, spanning_compl_dual_iff, not_indep_iff, not_indep_iff] at h
    tauto
  wlog hi1 : M.Indep P.left generalizing M P with aux
  · obtain hi2 | hd2 := M.indep_or_dep (X := P.right)
    · exact aux P.symm hP2 (by simpa) hP1 hi2
    obtain hi3 | hd3 := M✶.indep_or_dep (X := P.left)
    · rw [← not_imp_not, not_indep_iff, not_dep_iff] at hP1 hP2
      obtain ⟨X, hXE : X ⊆ M.E, hXconn, h1 | h2 | h3⟩ := aux P.dual
        (by simpa) (by simpa) (by simpa) (by simpa)
      · exact ⟨X, hXE, by rwa [← eConn_dual], .inl (dual_symm_claim h1)⟩
      · exact ⟨X, hXE, by simpa using hXconn, .inr <| .inr
          ⟨Coindep.compl_spanning h2.1, by simpa using h2.2.1, h2.2.2⟩⟩
      · refine ⟨X, hXE, by simpa using hXconn, .inr <| .inl <| ⟨?_, h3.2.1, h3.2.2⟩⟩
        rw [← dual_coindep_iff, coindep_iff_compl_spanning]
        exact h3.1
    obtain hi4 | hd4 := M✶.indep_or_dep (X := P.right)
    · rw [← not_imp_not, not_indep_iff, not_dep_iff] at hP1 hP2
      obtain ⟨X, hXE : X ⊆ M.E, hXconn, h1 | h2 | h3⟩ :=
        aux P.dual.symm (by simpa) (by simpa) (by simpa) hi4
      · exact ⟨X, hXE, by simpa using hXconn, .inl <| dual_symm_claim h1⟩
      · exact ⟨X, hXE, by simpa using hXconn, .inr <| .inr
          ⟨Coindep.compl_spanning h2.1, by simpa using h2.2.1, h2.2.2⟩⟩
      refine ⟨X, hXE, by simpa using hXconn, .inr <| .inl <| ⟨?_, h3.2.1, h3.2.2⟩⟩
      rw [← dual_coindep_iff, coindep_iff_compl_spanning]
      exact h3.1
    refine ⟨P.left, P.left_subset_ground, by simpa, .inl ?_⟩
    rw [spanning_iff_compl_coindep P.left_subset_ground,
      ← coindep_iff_compl_spanning P.left_subset_ground, coindep_def, coindep_def,
      P.compl_left, ← not_indep_iff P.left_subset_ground]
    exact ⟨hi1, hd2, hd4.not_indep, hd3.not_indep⟩
  obtain ⟨Q, hQP, hQc, hQle⟩ := hi1.exists_isTutteSeparation_of_not_coindep (hP1 hi1).not_indep
  refine ⟨_, Q.left_subset_ground, ?_, .inr <| .inl ⟨hi1.subset hQP, hQc, ?_⟩⟩
  · grw [Q.eConn_left, hQle]
    simpa
  grw [← M.eConn_add_nullity_add_nullity_dual _ Q.left_subset_ground, Q.eConn_left, hQle,
    hQc.isCircuit.nullity_eq, (hi1.subset hQP).nullity_eq, add_zero, add_assoc, one_add_one_eq_two]
  simpa

lemma TutteConnected.deleteElem (h : M.TutteConnected (k+1)) (e : α) :
    (M ＼ {e}).TutteConnected k := by
  contrapose h
  rw [not_TutteConnected_iff_exists]
  obtain ⟨X, hXss, hXconn, hX⟩ := exists_dep_nonspanning_or_small_of_not_tutteConnected h
  obtain ⟨hXE : X ⊆ M.E, heX : e ∉ X⟩ := subset_diff_singleton_iff.1 hXss
  obtain (hX | hX | hX) := hX
  ·
    refine ⟨X, hXE, ?_, fun _ ↦ ?_, ?_⟩
-- lemma exists_dep_nonspanning_of_not_tutteConnected (hM : k ≤ M.eRank + 2)
-- (hMd : k ≤ M✶.eRank + 2)
--     (h : ¬ M.TutteConnected k) : ∃ X ⊆ M.E, M.eConn X + 2 ≤ k ∧
--       ((M.Dep X ∧ M.Dep (M.E \ X) ∧ ¬ M.Spanning X ∧ ¬ M.Spanning (M.E \ X))) := by
--   obtain ⟨X, hXE, hXconn, h1 | ⟨hXi, hXc, hle⟩ | h3⟩ :=
--     exists_dep_nonspanning_or_small_of_not_tutteConnected h
--   · exact ⟨X, hXE, hXconn, h1⟩
--   · rw []
    -- grw [← hXc.compl_isHyperplane.eRk_add_one_eq] at hM



end Tutte



def IsVerticallyConnected' (M : Matroid α) (k : ℕ∞) :=
    M.PredConnected (fun j M X ↦ j + 2 ≤ k → M.Spanning X)

def IsInternallyConnected' (M : Matroid α) (k : ℕ∞) :=
    M.PredConnected (fun j M X ↦ ((j+3 ≤ k) → M.Indep X ∧ M.Coindep X)
      ∧ (j + 2 = k → M.nullity X + M✶.nullity X ≤ 1))

lemma isVerticallyConnected'_top_iff :
    M.IsVerticallyConnected' ⊤ ↔ ∀ X ⊆ M.E, M.Spanning X ∨ M.Spanning (M.E \ X) := by
  simp only [IsVerticallyConnected', PredConnected, le_top, forall_const]
  exact ⟨fun h X hX ↦ by simpa using h (M.partition X),
    fun h P ↦ by simpa [P.compl_left] using h _ P.left_subset_ground⟩

-- lemma argg (h : ¬ M.TutteConnected k) : ∃ (P : M.Partition), P.eConn + 2 ≤ k ∧
--     ((M.Indep P.left ∨ M✶.Indep P.left) ∨
--     (M.Dep P.left ∧ M.Dep P.right ∧ ¬ M.Spanning P.left ∧ ¬ M.Spanning P.right)) := by
--   simp only [TutteConnected, PredConnected, not_forall, not_or, exists_prop, not_and,
--     dual_ground, Partition.left_subset_ground, not_indep_iff, Partition.right_subset_ground] at h
--   obtain ⟨Q, ⟨hQconn, hQ1⟩, -, hQ2⟩ := h
--   obtain hi | hd := M.indep_or_dep Q.left_subset_ground
--   · exact ⟨Q, hQconn, .inl <| .inl hi⟩
--   obtain hid | hdd := M✶.indep_or_dep Q.left_subset_ground
--   · exact ⟨Q, hQconn, .inl <| .inr hid⟩
--   obtain hir | hdr := M.indep_or_dep Q.right_subset_ground
--   · exact ⟨Q.symm, by simpa, .inl <| .inl hir⟩
--   obtain hird | hdrd := M✶.indep_or_dep Q.right_subset_ground
--   · exact ⟨Q.symm, by simpa, .inl <| .inr hird⟩
--   refine ⟨Q, hQconn, .inr ⟨hd, hdr, ?_⟩⟩
--   rwa [← Q.dual_dep_right_iff, ← Q.dual_dep_left_iff, and_iff_left hdd]






end abstract

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

lemma IsDSeparation.dual (hP : P.IsDSeparation a b d) : P.dual.IsDSeparation b a d := by
  simpa

lemma IsDSeparation.nonempty_left (h : P.IsDSeparation a b d) : P.left.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro h0
  simp [isDSeparation_iff, h0] at h

lemma IsDSeparation.nonempty_right (h : P.IsDSeparation a b d) : P.right.Nonempty := by
  simpa using h.symm.nonempty_left

/-- A Tutte separation is one where each side has positive nullity or conullity.  -/
abbrev IsTutteSeparation (P : M.Partition) := P.IsDSeparation 1 1 0

lemma IsTutteSeparation.dual (h : P.IsTutteSeparation) : P.dual.IsTutteSeparation :=
  IsDSeparation.dual h

lemma IsTutteSeparation.symm (h : P.IsTutteSeparation) : P.symm.IsTutteSeparation :=
  IsDSeparation.symm h

@[simp]
lemma isDSeparation_one_one_zero_iff : P.IsDSeparation 1 1 0 ↔ P.IsTutteSeparation := Iff.rfl

lemma isTutteSeparation_iff_dep_or_dep :
    P.IsTutteSeparation ↔ (M.Dep P.left ∨ M✶.Dep P.left) ∧ (M.Dep P.right ∨ M✶.Dep P.right) := by
  simp only [IsTutteSeparation, isDSeparation_iff, one_mul, pos_iff_ne_zero, ne_eq, add_eq_zero,
    nullity_eq_zero, not_and, dual_ground, Partition.left_subset_ground,
    Partition.right_subset_ground, ← not_dep_iff, not_not]
  tauto

lemma isTutteSeparation_iff_dep_or_spanning : P.IsTutteSeparation ↔
    (M.Dep P.left ∨ ¬ M.Spanning P.right) ∧ (M.Dep P.right ∨ ¬ M.Spanning P.left) := by
  rw [isTutteSeparation_iff_dep_or_dep, dep_dual_iff_compl_not_spanning,
    dep_dual_iff_compl_not_spanning, P.compl_right, P.compl_left]

lemma isTutteSeparation_iff_spanning_imp_dep : P.IsTutteSeparation ↔
    (M.Spanning P.right → M.Dep P.left) ∧ (M.Spanning P.left → M.Dep P.right) := by
  rw [isTutteSeparation_iff_dep_or_spanning, imp_iff_or_not, imp_iff_or_not]

lemma IsTutteSeparation.dep_of_indep (h : P.IsTutteSeparation) (hi : M.Indep P.left) :
    M✶.Dep P.left := by
  rw [isTutteSeparation_iff_dep_or_dep, or_iff_right hi.not_dep] at h
  exact h.1

lemma IsTutteSeparation.dep_of_coindep (h : P.IsTutteSeparation) (hi : M.Coindep P.left) :
    M.Dep P.left := by
  rw [isTutteSeparation_iff_dep_or_dep, or_iff_left hi.indep.not_dep] at h
  exact h.1

lemma isTutteSeparation_iff_encard_lt (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ P.eConn < P.left.encard ∧ P.eConn < P.right.encard := by
  rw [isTutteSeparation_iff_dep_or_dep, ← eConn_lt_encard_iff (by simpa),
      ← eConn_lt_encard_iff (by simpa), P.eConn_left, P.eConn_right]

lemma IsTutteSeparation.nonempty_left (h : P.IsTutteSeparation) : P.left.Nonempty :=
  IsDSeparation.nonempty_left h

lemma Dep.isTutteSeparation_partition_of_not_spanning {X : Set α}
    (hX : M.Dep X) (hsp : ¬ M.Spanning X) : (M.partition X).IsTutteSeparation := by
  rw [isTutteSeparation_iff_dep_or_dep]
  simp only [partition_left, hX, true_or, partition_right, true_and]
  rw [dep_compl_dual_iff_not_spanning]
  exact .inr hsp

lemma Dep.partition_isTutteSeparation_of_dep {X : Set α} (hX : M.Dep X) (hXc : M.Dep (M.E \ X)) :
    (M.partition X).IsTutteSeparation := by
  rw [isTutteSeparation_iff_dep_or_spanning]
  simp [partition_left, partition_right, hX, hXc]

lemma IsTutteSeparation.exists_of_indep (h : P.IsTutteSeparation) (h_ind : M.Indep P.left) :
    ∃ (Q : M.Partition), Q.left ⊆ P.left ∧ M.IsCocircuit Q.left ∧ Q.eConn ≤ P.eConn := by
  obtain ⟨C, hCP, hC⟩ := (h.dep_of_indep h_ind).exists_isCircuit_subset
  refine ⟨M.partition C hC.subset_ground, hCP, hC, ?_⟩
  rw [← Partition.eConn_left, partition_left _ _, ← M.eConn_compl, ← P.eConn_right, ← compl_left,
    ← eConn_dual, ← M.eConn_dual]
  refine eConn_le_of_subset_of_subset_closure _ (diff_subset_diff_right hCP) ?_
  grw [← dual_ground, h_ind.coindep.compl_spanning.closure_eq, diff_subset]

lemma IsCircuit.isTutteSeparation_partition {C : Set α} (hC : M.IsCircuit C)
    (hCs : M.Spanning C → M.Dep (M.E \ C)) :
    (M.partition C hC.subset_ground).IsTutteSeparation := by
  simpa [isTutteSeparation_iff_dep_or_spanning, hC.dep, or_iff_not_imp_right]

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

lemma isTutteConnected_iff_isfDConnected :
    M.IsTutteConnected k ↔ M.IsfDConnected 1 1 (fun t ↦ if t + 1 < k then 0 else ⊤) := by
  simp [IsTutteConnected, IsDConnected, IsfDConnected]
  refine ⟨fun h P hP ↦ ?_, fun h P hP hsep ↦ h P (by simpa [hP])⟩
  split_ifs at hP with hlt
  · exact h P hlt hP
  simp [Partition.isDSeparation_iff] at hP

-- Make this the definition
lemma isTutteConnected_iff_forall_not_isTutteSeparation :
    M.IsTutteConnected k ↔ ∀ P : M.Partition, P.eConn + 1 < k → ¬ P.IsTutteSeparation := Iff.rfl


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

lemma exists_dep_nonspanning_or_small_of_not_isTutteConnected (h : ¬ M.IsTutteConnected k) :
    ∃ X ⊆ M.E, M.eConn X + 1 < k ∧
      (((M.Dep X ∧ M.Dep (M.E \ X) ∧ ¬ M.Spanning X ∧ ¬ M.Spanning (M.E \ X)))
    ∨ (M.Indep X ∧ M.IsCocircuit X ∧ X.encard < k)
    ∨ (M.Spanning (M.E \ X) ∧ M.IsCircuit X ∧ X.encard < k)) := by
  simp only [isTutteConnected_iff_forall_not_isTutteSeparation, not_forall, not_not] at h
  obtain ⟨P, hPconn, hP⟩ := h
  have dual_symm_claim {N : Matroid α} {Y : Set α}
      (h : N✶.Dep Y ∧ N✶.Dep (N✶.E \ Y) ∧ ¬ N✶.Spanning Y ∧ ¬ N✶.Spanning (N✶.E \ Y))  :
      (N.Dep Y ∧ N.Dep (N.E \ Y) ∧ ¬ N.Spanning Y ∧ ¬ N.Spanning (N.E \ Y)) := by
    have hYE : Y ⊆ N.E := h.1.subset_ground
    rw [dual_ground, dep_dual_iff_compl_not_spanning, dep_compl_dual_iff_not_spanning,
      spanning_dual_iff, spanning_compl_dual_iff, not_indep_iff,] at h
    tauto
  wlog hi1 : M.Indep P.left generalizing M P with aux
  · obtain hi2 | hd2 := M.indep_or_dep (X := P.right)
    · exact aux P.symm (by simpa) hP.symm hi2
    obtain hi3 | hd3 := M✶.indep_or_dep (X := P.left)
    · obtain ⟨X, hXE : X ⊆ M.E, hXconn, h1 | h2 | h3⟩ := aux P.dual (by simpa) hP.dual (by simpa)
      · exact ⟨X, hXE, by rwa [← eConn_dual], .inl (dual_symm_claim h1)⟩
      · exact ⟨X, hXE, by simpa using hXconn, .inr <| .inr
          ⟨Coindep.compl_spanning h2.1, by simpa using h2.2.1, h2.2.2⟩⟩
      · refine ⟨X, hXE, by simpa using hXconn, .inr <| .inl <| ⟨?_, h3.2.1, h3.2.2⟩⟩
        rw [← dual_coindep_iff, coindep_iff_compl_spanning]
        exact h3.1
    obtain hi4 | hd4 := M✶.indep_or_dep (X := P.right)
    · obtain ⟨X, hXE : X ⊆ M.E, hXconn, h1 | h2 | h3⟩ :=
        aux P.dual.symm (by simpa) (by simpa) hi4
      · exact ⟨X, hXE, by simpa using hXconn, .inl <| dual_symm_claim h1⟩
      · exact ⟨X, hXE, by simpa using hXconn, .inr <| .inr
          ⟨Coindep.compl_spanning h2.1, by simpa using h2.2.1, h2.2.2⟩⟩
      refine ⟨X, hXE, by simpa using hXconn, .inr <| .inl <| ⟨?_, h3.2.1, h3.2.2⟩⟩
      rw [← dual_coindep_iff, coindep_iff_compl_spanning]
      exact h3.1
    refine ⟨P.left, P.left_subset_ground, by simpa, .inl ?_⟩
    rw [spanning_iff_compl_coindep, ← coindep_iff_compl_spanning, coindep_def, coindep_def,
      not_indep_iff, not_indep_iff, P.compl_left, ← not_indep_iff]
    exact ⟨hi1, hd2, hd4, hd3⟩
  obtain ⟨Q, hQP, hQc, hQle⟩ := hP.exists_of_indep hi1
  refine ⟨_, Q.left_subset_ground, ?_, .inr <| .inl ⟨hi1.subset hQP, hQc, ?_⟩⟩
  · grw [Q.eConn_left, hQle]
    assumption
  grw [← M.eConn_add_nullity_add_nullity_dual Q.left, Q.eConn_left, hQle,
    hQc.isCircuit.nullity_eq, (hi1.subset hQP).nullity_eq, add_zero]
  assumption

/-- If `M` is not `k`-connected, then there is a separation `(X,E-X)` with both sides dependent,
or in which `X` is a small independent cocircuit. -/
lemma exists_dep_dep_or_small_of_not_isTutteConnected (h : ¬ M.IsTutteConnected k) :
    ∃ X ⊆ M.E, M.eConn X + 1 < k ∧
    ((M.Dep X ∧ M.Dep (M.E \ X)) ∨ (M.Indep X ∧ M.IsCocircuit X ∧ X.encard < k)) := by
  by_contra! hcon
  simp only [IsTutteConnected, IsDConnected, Partition.isDSeparation_one_one_zero_iff,
    Partition.isTutteSeparation_iff_dep_or_dep, not_and, not_or, Partition.right_subset_ground,
    not_dep_iff, dual_ground, not_forall, not_indep_iff, exists_prop] at h
  obtain ⟨P, hPconn, h1, h2⟩ := h
  have hc1 := P.compl_left ▸ hcon _ P.left_subset_ground (by simpa)
  have hc2 := P.compl_right ▸ hcon _ P.right_subset_ground (by simpa)
  wlog hi : M.Indep P.right generalizing P with aux
  · rw [not_indep_iff] at hi
    specialize aux P.symm (by simpa)
    simp only [hi, not_true_eq_false, imp_false, Partition.left_subset_ground, not_dep_iff] at hc1
    rw [or_iff_right hc1.1.not_dep] at h1
    obtain ⟨hC : M.IsCocircuit P.left, hcard : P.left.encard < k⟩ := by
      simpa [hc1.1, hi, h1] using aux
    simp [hcard.not_ge, hC, hc1.1.not_dep] at hc1
  obtain ⟨C, hCr, hC⟩ := (h2 hi).exists_isCircuit_subset
  have hconn_le : M.eConn C + 1 ≤ P.eConn + 1 := by
    rw [ENat.add_one_le_add_one_iff, ← P.eConn_left, ← eConn_dual, ← M.eConn_dual, ← eConn_compl,
    ← P.compl_right]
    refine eConn_le_of_subset_of_subset_closure _ (diff_subset_diff_right hCr) ?_
    grw [← M.dual_ground, hi.coindep.compl_spanning.closure_eq, diff_subset]
  have hcard := (hcon _ hC.subset_ground (lt_of_le_of_lt hconn_le hPconn)).2 (hi.subset hCr) hC
  grw [← M.eConn_add_nullity_add_nullity_dual _ hC.subset_ground, hC.nullity_eq,
    (hi.subset hCr).nullity_eq, add_zero, hconn_le] at hcard
  exact hPconn.not_ge hcard

lemma not_isTutteConnected_iff_exists_dep_dep_or_small (h_nt : 2 * k ≤ M.E.encard + 2) :
    ¬ M.IsTutteConnected k ↔ ∃ X ⊆ M.E, M.eConn X + 1 < k ∧
    ((M.Dep X ∧ M.Dep (M.E \ X)) ∨ (M.Indep X ∧ M.IsCocircuit X ∧ X.encard < k)) := by
  refine ⟨exists_dep_dep_or_small_of_not_isTutteConnected, ?_⟩
  rintro ⟨X, hXE, hXconn, hsep⟩ hconn
  refine hconn (M.partition X hXE) (by simpa) ?_
  simp only [Partition.isDSeparation_one_one_zero_iff, Partition.isTutteSeparation_iff_dep_or_dep,
    partition_left, partition_right]
  obtain ⟨hd, hd'⟩ | ⟨hi, hc, hcard⟩ := hsep
  · simp [hd, hd']
  rw [and_iff_right (.inr hc.dep), ← not_indep_iff, ← not_indep_iff,
    ← Classical.not_and_iff_not_or_not, ← coindep_def, ← spanning_iff_compl_coindep]
  rintro ⟨hic, hic'⟩
  have h1 := hc.compl_isHyperplane.eRk_add_one_eq
  rw [hic.eRk_eq_encard, ← hic'.eRk_eq, hi.eRk_eq_encard] at h1
  grw [← encard_diff_add_encard_of_subset hi.subset_ground, add_right_comm] at h_nt
  generalize ha : (M.E \ X).encard = a at *
  generalize hb : X.encard = b at *
  enat_to_nat
  linarith

section Vertical


/-- A vertical separation is one where each side has positive conullity.  -/
abbrev Partition.IsVerticalSeparation (P : M.Partition) := P.IsDSeparation 0 1 0

@[simp]
lemma Partition.isDSeparation_zero_one_one_iff :
    P.IsDSeparation 0 1 0 ↔ P.IsVerticalSeparation := Iff.rfl


lemma Partition.isVerticalSeparation_iff :
    P.IsVerticalSeparation ↔ ¬ M.Spanning P.left ∧ ¬ M.Spanning P.right := by
  simp only [IsVerticalSeparation, isDSeparation_iff, zero_mul, one_mul, zero_add, pos_iff_ne_zero,
    ne_eq, nullity_eq_zero, dual_ground, Partition.left_subset_ground, not_indep_iff,
    Partition.right_subset_ground]
  rw [← not_indep_iff, ← not_indep_iff, ← coindep_def, ← compl_right, and_comm,
    ← spanning_iff_compl_coindep, ← coindep_def, ← compl_left, ← spanning_iff_compl_coindep,
    compl_left, compl_right]

lemma Partition.isVerticalSeparation_iff_encard_lt (hP : P.eConn ≠ ⊤) :
    P.IsVerticalSeparation ↔ P.eConn < M.eRk P.left ∧ P.eConn < M.eRk P.right := by
  simp only [IsVerticalSeparation, isDSeparation_iff, zero_mul, one_mul, zero_add, pos_iff_ne_zero,
    ne_eq, nullity_eq_zero, dual_ground, Partition.left_subset_ground, not_indep_iff,
    Partition.right_subset_ground]
  rw [← eConn_left, eConn_lt_eRk_iff (by simpa), compl_left, eConn_left, ← eConn_right,
    eConn_lt_eRk_iff (by simpa), spanning_iff_compl_coindep, compl_right, coindep_def,
    not_indep_iff, spanning_iff_compl_coindep, compl_left, coindep_def, not_indep_iff]

end Vertical

section Internal

def IsInternallyConnected'' (M : Matroid α) (k : ℕ∞) :=
    M.IsfDConnected 1 1 (fun t ↦ if t + 2 < k then 0 else if t + 1 < k then 1 else ⊤)

/-- An internally `k`-connected matroid is a `(k-1)`-connected matroid where every set
`A` with `λ(A) = k - 2` satisfies `|A| = k-1` or `|E - A| = k-1`. -/
def IsInternallyConnected (M : Matroid α) (k : ℕ∞) :=
    M.IsTutteConnected (k - 1) ∧ M.IsDConnected 1 1 1 k

end Internal

end Matroid
