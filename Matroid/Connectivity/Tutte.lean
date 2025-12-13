import Matroid.Connectivity.Separation
import Matroid.Connectivity.Minor
import Matroid.ForMathlib.Matroid.Constructions
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.ForMathlib.Tactic.TautoSet

lemma ENat.eq_zero_or_exists_eq_add_one (a : ℕ∞) : a = 0 ∨ ∃ b, a = b + 1 := by
  obtain (a | a | a) := a
  · exact .inr ⟨⊤, rfl⟩
  · exact .inl rfl
  exact .inr ⟨a, rfl⟩

open Set Matroid.Partition Function

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Partition}
  {b : Bool}

namespace Matroid

variable {dg dg' dg_l dg_r : Bool → Matroid α → Set α → Prop}

namespace Partition

/-! ### Abstract Separations -/

/-- An abstract notion of nondegenerate separation : given a predicate on sets in `M`,
`P.IsPredSeparation` means that neither side of `P` satisfies the degeneracy predicate. -/
def IsPredSeparation (dg : Bool → Matroid α → Set α → Prop) (P : M.Partition) := ∀ b, ¬ dg b M (P b)

lemma isPredSeparation_iff : P.IsPredSeparation dg ↔ ∀ b, ¬ dg b M (P b) := Iff.rfl

lemma not_isPredSeparation_iff {dg} : ¬ P.IsPredSeparation dg ↔ ∃ b, dg b M (P b) := by
  simp only [IsPredSeparation, Bool.forall_bool, not_and, not_not, Bool.exists_bool]
  grind

lemma IsPredSeparation.dual {dg dg' : Bool → Matroid α → Set α → Prop}
    (hdg : ∀ ⦃M X b⦄, X ⊆ M.E → dg' b M X → dg b M✶ X) (hP : P.IsPredSeparation dg) :
    P.dual.IsPredSeparation dg' :=
  fun b h ↦ hP b <| by simpa using hdg (by simp) h

lemma IsPredSeparation.dual_compl (hdg : ∀ ⦃M X b⦄, X ⊆ M.E → dg' b M X → dg (!b) M✶ (M.E \ X))
    (hP : P.IsPredSeparation dg) : P.dual.IsPredSeparation dg' :=
  fun b h ↦ hP (!b) <| by simpa using hdg (by simp) h

lemma IsPredSeparation.of_dual (hdg : ∀ ⦃M X b⦄, X ⊆ M.E → dg' b M X → dg b M✶ X)
    (hP : P.dual.IsPredSeparation dg) : P.IsPredSeparation dg' :=
  fun i h ↦ hP i <| hdg (by simp) h

lemma isPredSeparation_dual_iff (hdg : ∀ ⦃M X b⦄, X ⊆ M.E → dg b M X → dg b M✶ X) :
    P.dual.IsPredSeparation dg ↔ P.IsPredSeparation dg :=
  ⟨IsPredSeparation.of_dual hdg, IsPredSeparation.dual hdg⟩

lemma isPredSeparation_ofDual_iff {P : M✶.Partition}
    (hdg : ∀ ⦃M X b⦄, X ⊆ M.E → dg b M X → dg b M✶ X) :
    P.ofDual.IsPredSeparation dg ↔ P.IsPredSeparation dg := by
  rw [← isPredSeparation_dual_iff hdg, ofDual_dual]

lemma IsPredSeparation.symm (hP : P.IsPredSeparation dg) :
    P.symm.IsPredSeparation (fun b ↦ dg !b) :=
  fun b ↦ hP !b

lemma IsPredSeparation.of_symm (hP : P.symm.IsPredSeparation dg) :
    P.IsPredSeparation (fun b ↦ dg !b) :=
  fun b ↦ by simpa using hP !b

lemma isPredSeparation_symm_iff :
    P.symm.IsPredSeparation dg ↔ P.IsPredSeparation (fun b ↦ dg !b) :=
  ⟨IsPredSeparation.of_symm, fun h ↦ by simpa using h.symm⟩

lemma IsPredSeparation.mono (h_imp : ∀ ⦃M X b⦄, X ⊆ M.E → dg' b M X → dg b M X)
    (hP : P.IsPredSeparation dg) : P.IsPredSeparation dg' :=
  fun b h ↦ hP b <| h_imp (by simp) h

lemma IsPredSeparation.nonempty (h : P.IsPredSeparation dg) (hdg : ∀ b, dg b M ∅) (b : Bool) :
    (P b).Nonempty := by
  rw [nonempty_iff_ne_empty]
  refine fun he ↦ h b ?_
  rw [he]
  apply hdg

lemma IsPredSeparation.not_trivial (h : P.IsPredSeparation dg) (hdg : ∀ b, dg b M ∅) :
    ¬ P.Trivial := by
  simp_rw [Partition.Trivial, not_exists, ← nonempty_iff_ne_empty]
  exact h.nonempty hdg

/-! ### Tutte Separations -/

abbrev IsTutteSeparation (P : M.Partition) := IsPredSeparation
    (fun _ M X ↦ M.Indep X ∧ M.Coindep X) P

lemma isTutteSeparation_iff_forall : P.IsTutteSeparation ↔ ∀ b, M.Dep (P b) ∨ M.Codep (P b) := by
  simp_rw [IsTutteSeparation, IsPredSeparation, Classical.not_and_iff_not_or_not]
  simp

lemma isTutteSeparation_iff (b : Bool) :
    P.IsTutteSeparation ↔ (M.Dep (P b) ∨ M.Codep (P b)) ∧ (M.Dep (P !b) ∨ M.Codep (P !b)) := by
  simp_rw [isTutteSeparation_iff_forall, b.forall_bool']

lemma isTutteSeparation_iff' (b : Bool) : P.IsTutteSeparation ↔
    (M.Dep (P b) ∨ M.Nonspanning (P !b)) ∧ (M.Dep (P !b) ∨ M.Nonspanning (P b)) := by
  rw [isTutteSeparation_iff b, nonspanning_not_iff, ← codep_not_iff]

@[simp]
lemma isTutteSeparation_dual_iff : P.dual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_dual_iff <| by simp [and_comm]

alias ⟨IsTutteSeparation.of_dual, IsTutteSeparation.dual⟩ := isTutteSeparation_dual_iff

@[simp]
lemma isTutteSeparation_ofDual_iff {P : M✶.Partition} :
    P.ofDual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_ofDual_iff <| by simp [and_comm]

@[simp]
lemma isTutteSeparation_symm_iff : P.symm.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_symm_iff

lemma IsTutteSeparation.symm (h : P.IsTutteSeparation) : P.symm.IsTutteSeparation :=
  IsPredSeparation.symm h

lemma IsTutteSeparation.codep_of_indep (hP : P.IsTutteSeparation) (hi : M.Indep (P b)) :
    M.Codep (P b) := by
  contrapose hi
  rw [isTutteSeparation_iff b, or_iff_left hi] at hP
  exact hP.1.not_indep

lemma IsTutteSeparation.nonspanning_of_indep (hP : P.IsTutteSeparation) (hi : M.Indep (P b)) :
    M.Nonspanning (P !b) :=
  nonspanning_not_iff.2 (hP.codep_of_indep hi)

lemma IsTutteSeparation.dep_of_spanning (hP : P.IsTutteSeparation) (hs : M.Spanning (P b)) :
    M.Dep (P !b) := by
  simpa using hP.dual.codep_of_indep (b := !b) (by simpa using hs.compl_coindep)

lemma isTutteSeparation_iff_lt_encard (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ ∀ b, P.eConn < (P b).encard := by
  rw [isTutteSeparation_iff_forall]
  convert Iff.rfl with b
  simp_rw [← M.eConn_add_nullity_add_nullity_dual (P b), P.eConn_eq, add_assoc]
  simp [-not_and, Classical.not_and_iff_not_or_not, hP]

lemma isTutteSeparation_iff_add_one_le_encard (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ ∀ b, P.eConn + 1 ≤ (P b).encard := by
  convert isTutteSeparation_iff_lt_encard hP using 2 with b
  rw [ENat.add_one_le_iff hP]

lemma isTutteSeparation_iff_nullity :
    P.IsTutteSeparation ↔ ∀ b, 1 ≤ M.nullity (P b) + M✶.nullity (P b) := by
  simp only [ENat.one_le_iff_ne_zero, ne_eq, add_eq_zero, nullity_eq_zero,
    Classical.not_and_iff_not_or_not, dual_ground,
    Partition.subset_ground, not_indep_iff, dep_dual_iff, isTutteSeparation_iff_forall]

lemma not_isTutteSeparation_iff_exists :
    ¬ P.IsTutteSeparation ↔ ∃ b, M.Indep (P b) ∧ M.Coindep (P b) := by
  simp_rw [isTutteSeparation_iff_forall, not_forall, not_or, Partition.not_dep_iff,
    Partition.not_codep_iff]

-- lemma not_isTutteSeparation_iff' : ¬ P.IsTutteSeparation ↔
--     (M.Indep P.left ∧ M.Spanning P.right) ∨ (M.Spanning P.left ∧ M.Indep P.right) := by
--   rw [isTutteSeparation_iff', ← not_spanning_iff, ← not_indep_iff, ← not_spanning_iff,
--     ← not_indep_iff]
--   tauto
lemma isTutteSeparation_of_encard (h : P.eConn < (P b).encard) (h' : P.eConn < (P !b).encard) :
    P.IsTutteSeparation := by
  rwa [isTutteSeparation_iff_lt_encard (fun hP ↦ by simp [hP] at h), b.forall_bool',
    and_iff_right h]

lemma IsTutteSeparation.nonempty (h : P.IsTutteSeparation) (b : Bool) : (P b).Nonempty := by
  rw [isTutteSeparation_iff b] at h
  exact h.1.elim Dep.nonempty Dep.nonempty

lemma IsTutteSeparation.ssubset_ground (h : P.IsTutteSeparation) (b : Bool) : P b ⊂ M.E := by
  refine (P.subset_ground b).eq_or_ssubset.elim (fun h' ↦ ?_) id
  have hne := P.compl_eq _ ▸ h.nonempty !b
  simp [h'] at hne

lemma IsTutteSeparation.exists_of_indep (h : P.IsTutteSeparation) (hi : M.Indep (P b)) :
    ∃ Q : M.Partition, Q.IsTutteSeparation ∧
      Q b ⊆ P b ∧ M.IsCocircuit (Q b) ∧ Q.eConn ≤ P.eConn := by
  obtain ⟨C, hCP, hC⟩ := (h.codep_of_indep hi).exists_isCocircuit_subset
  refine ⟨M.partition C b, ?_, ?_⟩
  · rw [isTutteSeparation_iff b, partition_apply, partition_apply_not,
      and_iff_right (.inr hC.codep), codep_compl_iff, ← not_spanning_iff, ← imp_iff_or_not]
    intro hCs
    obtain rfl : C = P b := hi.eq_of_spanning_subset hCs hCP
    simpa using h.dep_of_spanning hCs
  grw [← Partition.eConn_eq _ b, partition_apply, (hi.subset hCP).eConn_eq, ← P.eConn_eq b,
    hi.eConn_eq]
  exact ⟨hCP, hC, M✶.eRk_mono hCP⟩



end Partition



variable {dg dg' : Bool → ℕ∞ → Matroid α → Set α → Prop}

/-! ### Abstract Connectivity -/

/-- An abstract notion of connectivity. `dg` is a predicate-valued function that for each `t`,
specifies what it means for a set `X` with connectivity `t` to be degenerate in a matroid `M`.
`PredConnected dg M` means that in `M`, every set of connectivity `t` either satisfies
`dg t`, or its complement satisfies `dg t`.
`
For instance, for `k`-Tutte-connectivity, sets of connectivity `k-1` or higher are not degenerate,
and sets of connectivity `k-2` or less are degenerate iff they are independent and coindependent. -/
def PredConnected (dg : Bool → ℕ∞ → Matroid α → Set α → Prop) (M : Matroid α) :=
    ∀ P : M.Partition, ∃ b, dg b P.eConn M (P b)

lemma not_predConnected_iff :
    ¬ M.PredConnected dg ↔ ∃ P : M.Partition, P.IsPredSeparation (dg · P.eConn) := by
  simp [PredConnected, Partition.IsPredSeparation]

lemma PredConnected.not_IsPredSeparation (h : M.PredConnected dg) (P : M.Partition) :
    ¬ P.IsPredSeparation (dg · P.eConn) := by
  contrapose! h
  rw [not_predConnected_iff]
  exact ⟨P, h⟩

lemma PredConnected.mono'
    (hdegen : ∀ ⦃k b M X⦄, X ⊆ M.E → dg b k M X → (dg' b k M X ∨ dg' (!b) k M (M.E \ X)))
    (h : M.PredConnected dg) : M.PredConnected dg' := by
  refine fun P ↦ ?_
  obtain ⟨b, h'⟩ := h P
  obtain h1 | h2 := hdegen (P.subset_ground _) h'
  · exact ⟨b, h1⟩
  exact ⟨!b, by simpa using h2⟩

lemma PredConnected.mono {dg : Bool → ℕ∞ → Matroid α → Set α → Prop}
    (hdegen : ∀ ⦃b k M X⦄, X ⊆ M.E → dg b k M X → dg' b k M X)
    (h : M.PredConnected dg) : M.PredConnected dg' :=
  h.mono' fun _ _ _ _ hX h' ↦ .inl <| hdegen hX h'

lemma PredConnected.mono_compl (hdegen : ∀ ⦃b k M X⦄, X ⊆ M.E → dg b k M X → dg' (!b) k M (M.E \ X))
    (h : M.PredConnected dg) : M.PredConnected dg' :=
  h.mono' fun _ _ _ _ hX h' ↦ .inr <| hdegen hX h'

lemma PredConnected.dual' (hdegen : ∀ ⦃b k M X⦄, X ⊆ M.E → dg b k M X →
    (dg' b k M✶ X ∨ dg' (!b) k M✶ (M.E \ X))) (h : M.PredConnected dg) :
    M✶.PredConnected dg' := by
  intro P
  obtain ⟨b, hb⟩ := h.mono' (dg' := fun b k N Y ↦ dg' b k N✶ Y) (P := P.ofDual)
    (fun _ _ _ _ hX h ↦ hdegen hX h)
  exact ⟨b, by simpa using hb⟩

lemma PredConnected.dual_compl (hdg : ∀ ⦃b k M X⦄, X ⊆ M.E → dg b k M X → dg' (!b) k M✶ (M.E \ X))
    (h : M.PredConnected dg) : M✶.PredConnected dg' :=
  h.dual' fun _ _ _ _ hX h' ↦ by simp [hdg hX h']

lemma PredConnected.dual (hdegen : ∀ ⦃b k M X⦄, X ⊆ M.E → dg b k M X → dg' b k M✶ X)
    (h : M.PredConnected dg) : M✶.PredConnected dg' :=
  h.dual' fun b k N X hX h' ↦ by simp [hdegen hX h']

/-- A slightly more concrete notion of connectivity that still abstracts Tutte, vertical and cyclic
connectivity. `M.numConnected dg (k+1)` means that every separation of connectivity less than `k`
has a degenerate side in the of a specified `dg`.
Unlike `PredConnected`, this is required to be symmetric in the two sides.
Internal connectivity is not an example of this, since it has a nondegeneracy condition that
depends on the connectivity. -/
def NumConnected (M : Matroid α) (dg : Matroid α → Set α → Prop) (k : ℕ∞) : Prop :=
  M.PredConnected (fun _ j M X ↦ j + 1 + 1 ≤ k → dg M X)

lemma NumConnected.mono {dg} (h : M.NumConnected dg k) (hjk : j ≤ k) : M.NumConnected dg j :=
  PredConnected.mono (fun _ _ _ _ _ h hle ↦ h (hle.trans hjk)) h

/-- A version with `k`-connectedness rather than `(k+1)`. Usually the latter is preferred-/
lemma numConnected_iff_forall' {dg} : M.NumConnected dg k ↔
    ∀ (P : M.Partition), P.eConn + 1 + 1 ≤ k → ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  simp only [NumConnected, PredConnected, Bool.exists_bool, IsPredSeparation, Bool.forall_bool]
  grind

lemma numConnected_iff_forall {dg} : M.NumConnected dg (k+1) ↔
    ∀ (P : M.Partition), P.eConn + 1 ≤ k → ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  simp [numConnected_iff_forall']

lemma numConnected_iff_forall_set {dg} : M.NumConnected dg (k + 1) ↔
    ∀ ⦃X⦄, X ⊆ M.E → M.eConn X + 1 ≤ k → dg M X ∨ dg M (M.E \ X) := by
  simp only [numConnected_iff_forall, IsPredSeparation, not_forall_not]
  refine ⟨fun hP X hX hconn ↦ ?_, fun h P hP ↦ ?_⟩
  · obtain ⟨rfl | rfl, hb⟩ := hP (M.partition X true) (by simpa)
    · exact .inr <| by simpa using hb
    exact .inl <| by simpa using hb
  obtain h | h := h (P.subset_ground true) (by simpa)
  · exact ⟨true, h⟩
  exact ⟨false, by simpa using h⟩

lemma numConnected_top_iff {dg} : M.NumConnected dg ⊤ ↔ ∀ (P : M.Partition),
    ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  simp [numConnected_iff_forall']

lemma numConnected_top_iff' {dg} :
    M.NumConnected dg ⊤ ↔ ∀ ⦃X⦄, X ⊆ M.E → dg M X ∨ dg M (M.E \ X) := by
  rw [← top_add (a := 1), numConnected_iff_forall_set]
  simp

lemma NumConnected.not_isPredSeparation {dg} (h : M.NumConnected dg (k+1)) (hP : P.eConn + 1 ≤ k) :
    ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  rw [numConnected_iff_forall] at h
  exact h P hP

-- lemma exists_of_not_numConnected {dg} (h : ¬ M.NumConnected dg (k+1)) :
--     ∃ (P : M.Partition), P.eConn + 1 ≤ k ∧ P.IsPredSeparation (fun _ ↦ dg) := by

  -- simpa [numConnected_iff_forall] using h

-- lemma exists_right_le_of_not_numConnected {β : Type*} [LinearOrder β] {dg}
--     (h : ¬ M.NumConnected dg (k+1)) (f : Set α → β) :
--     ∃ (P : M.Partition), P.eConn + 1 ≤ k ∧ P.IsPredSeparation dg ∧ f P.right ≤ f P.left := by
--   obtain ⟨P, hPle, hP, hPf⟩ := exists_left_le_of_not_numConnected h f
--   exact ⟨P.symm, by simpa, hP.symm, by simpa⟩

lemma not_numConnected_iff_exists {dg} : ¬ M.NumConnected dg (k+1) ↔
    ∃ (P : M.Partition), P.eConn + 1 ≤ k ∧ P.IsPredSeparation (fun _ ↦ dg) := by
  simp [numConnected_iff_forall]

lemma Partition.IsPredSeparation.not_numConnected {dg} (h : P.IsPredSeparation (fun _ ↦ dg)) :
    ¬ M.NumConnected dg (P.eConn + 1 + 1) :=
  fun hM ↦ hM.not_isPredSeparation rfl.le h

@[simp]
lemma numConnected_zero (M : Matroid α) (dg) : M.NumConnected dg 0 := by
  simp [NumConnected, PredConnected]

@[simp]
lemma numConnected_one (M : Matroid α) (dg) : M.NumConnected dg 1 := by
  simp [NumConnected, PredConnected]

lemma NumConnected.compl_degen {dg} (h : M.NumConnected dg k) :
    M.NumConnected (fun M X ↦ dg M (M.E \ X)) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simpa [numConnected_iff_forall, IsPredSeparation, not_imp_comm] using h

lemma NumConnected.mono_degen {dg dg'} (h : M.NumConnected dg k)
    (hdg : ∀ ⦃X⦄, X ⊆ M.E → dg M X → dg' M X) : M.NumConnected dg' k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp_rw [numConnected_iff_forall, not_isPredSeparation_iff] at h ⊢
  rintro P hPconn
  obtain ⟨b, hb⟩ := h P hPconn
  exact ⟨b, hdg (P.subset_ground _) hb⟩

lemma NumConnected.congr_degen {dg dg'} (hdg : ∀ ⦃X⦄, X ⊆ M.E → (dg M X ↔ dg' M X)) :
    M.NumConnected dg = M.NumConnected dg' := by
  ext k
  exact ⟨fun h ↦ h.mono_degen fun X hX ↦ (hdg hX).1, fun h ↦ h.mono_degen fun X hX ↦ (hdg hX).2⟩

lemma NumConnected.dual {dg} (h : M.NumConnected dg k) : M✶.NumConnected (fun M X ↦ dg M✶ X) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp_rw [numConnected_iff_forall, not_isPredSeparation_iff] at h ⊢
  exact fun P hP ↦ by simpa using h P.ofDual (by simpa)

lemma NumConnected.of_dual {dg} (h : M✶.NumConnected dg k) :
    M.NumConnected (fun M X ↦ dg M✶ X) k := by
  simpa using h.dual

lemma numConnected_of_subsingleton {dg} (h : M.E.Subsingleton) (k : ℕ∞) (hdg : dg M ∅) :
    M.NumConnected dg k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [numConnected_iff_forall]
  refine fun P hPconn hP ↦ ?_
  obtain ⟨b, hb⟩ := P.trivial_of_ground_subsingleton h
  exact hP b <| by rwa [hb]


/-! ### Tutte Connectivity -/

/-- `M` is `k`-connected if the connectivity of every Tutte separation strictly exceeds `k - 2`.
The term has always been defined this way, but the difference of two is very awkward to work with;
`(k+1)`-connectedness is much more natural than `k`-connectedness.

For this reason, we use `TutteConnected (k+1)` in the API in all places except where
no convenience is lost. Vertical and Cyclic connectivities have the same issues. -/
def TutteConnected (M : Matroid α) (k : ℕ∞) := M.NumConnected (fun M X ↦ M.Indep X ∧ M.Coindep X) k


lemma not_tutteConnected_iff_exists : ¬ M.TutteConnected (k + 1) ↔
    ∃ P : M.Partition, P.eConn + 1 ≤ k ∧ P.IsTutteSeparation :=
  not_numConnected_iff_exists

lemma tutteConnected_iff_forall : M.TutteConnected (k + 1) ↔
    ∀ (P : M.Partition), P.eConn + 1 ≤ k → ¬ P.IsTutteSeparation :=
  numConnected_iff_forall

lemma tutteConnected_top_iff_forall : M.TutteConnected ⊤ ↔
    ∀ (P : M.Partition), ¬ P.IsTutteSeparation :=
  numConnected_top_iff ..

lemma TutteConnected.dual (h : M.TutteConnected k) : M✶.TutteConnected k :=
  (NumConnected.dual h).mono_degen <| by simp +contextual [coindep_def]

lemma TutteConnected.of_dual (h : M✶.TutteConnected k) : M.TutteConnected k :=
  M.dual_dual ▸ h.dual

lemma TutteConnected.mono (h : M.TutteConnected k) (hjk : j ≤ k) : M.TutteConnected j :=
  NumConnected.mono h hjk

@[gcongr]
lemma TutteConnected.mono'
    (hjk : j ≤ k) (h : M.TutteConnected k) : M.TutteConnected j := h.mono hjk

@[simp]
lemma tutteConnected_one (M : Matroid α) : M.TutteConnected 1 :=
  numConnected_one M _

@[simp]
lemma tutteConnected_zero (M : Matroid α) : M.TutteConnected 0 :=
  numConnected_zero M _

lemma tutteConnected_of_le_one (M : Matroid α) (hk : k ≤ 1) : M.TutteConnected k := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by enat_to_nat; omega
  · simp
  simp

@[simp]
lemma tutteConnected_dual_iff : M✶.TutteConnected = M.TutteConnected := by
  ext k
  exact ⟨TutteConnected.of_dual, TutteConnected.dual⟩

lemma Partition.IsTutteSeparation.not_tutteConnected (hP : P.IsTutteSeparation) :
    ¬ M.TutteConnected (P.eConn + 1 + 1) := by
  rw [not_tutteConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma TutteConnected.not_isTutteSeparation (h : M.TutteConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ¬ P.IsTutteSeparation :=
  fun h' ↦ h'.not_tutteConnected <| h.mono <| add_left_mono hP

lemma tutteConnected_of_subsingleton (h : M.E.Subsingleton) (k : ℕ∞) : M.TutteConnected k :=
  numConnected_of_subsingleton h _ <| by simp


lemma tutteConnected_iff_numConnected_encard (hk : k ≠ ⊤) :
    M.TutteConnected k ↔ M.NumConnected (fun M X ↦ X.encard ≤ M.eConn X) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp only [tutteConnected_iff_forall, numConnected_iff_forall,
    isPredSeparation_iff, not_forall_not]
  convert Iff.rfl with P hP b
  rw [← M.eConn_add_nullity_add_nullity_dual (P b)]
  simp [add_assoc, show P.eConn ≠ ⊤ by enat_to_nat!]


@[simp]
lemma uniqueBaseOn_tutteConnected_iff {B E : Set α} :
    (uniqueBaseOn B E).TutteConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  obtain hE | hE := E.subsingleton_or_nontrivial
  · simp [(uniqueBaseOn B E).tutteConnected_of_subsingleton hE, hE]
  obtain (rfl | ⟨k,rfl⟩) := k.eq_zero_or_exists_eq_add_one; simp
  refine iff_of_false (fun ht ↦ ?_) (by simp [hE.not_subsingleton])
  obtain ⟨e, he⟩ := hE.nonempty
  refine ht.not_isTutteSeparation (P := Matroid.partition _ {e} true) (by simp) ?_
  rw [isTutteSeparation_iff_add_one_le_encard (by simp)]
  simp [hE.diff_singleton_nonempty e]

@[simp]
lemma loopyOn_tutteConnected_iff (E : Set α) :
    (loopyOn E).TutteConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  simp [← uniqueBaseOn_empty]

@[simp]
lemma freeOn_tutteConnected_iff (E : Set α) :
    (freeOn E).TutteConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  rw [← tutteConnected_dual_iff, freeOn_dual_eq, loopyOn_tutteConnected_iff]

lemma tutteConnected_two_iff [M.Nonempty] : M.TutteConnected 2 ↔ M.Connected := by
  rw [← not_iff_not, exists_partition_iff_not_connected, ← one_add_one_eq_two,
    not_tutteConnected_iff_exists]
  simp only [ENat.add_le_right_iff, ENat.one_ne_top, or_false]
  refine ⟨fun ⟨P, hP0, hP⟩ ↦ ⟨P, hP0, IsPredSeparation.not_trivial hP (by simp)⟩,
    fun ⟨P, hP0, hP⟩ ↦ ⟨P, hP0, ?_⟩⟩
  rw [isTutteSeparation_iff_add_one_le_encard (by simp [hP0]), hP0]
  simp only [zero_add, one_le_encard_iff_nonempty, Bool.forall_bool]
  simp_rw [nonempty_iff_ne_empty, ← not_or, or_comm (a := P false = ∅), ← P.trivial_def]
  exact hP

lemma TutteConnected.connected [M.Nonempty] (hM : M.TutteConnected k) (hk : 2 ≤ k) :
    M.Connected :=
  tutteConnected_two_iff.1 (hM.mono hk)

@[simp]
lemma emptyOn_tutteConnected (α : Type*) (k : ℕ∞) : (emptyOn α).TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp [← freeOn_empty, freeOn_tutteConnected_iff]

lemma Connected.tutteConnected_two (hM : M.Connected) : (M.TutteConnected 2) := by
  obtain rfl | hne := M.eq_emptyOn_or_nonempty; simp
  rwa [tutteConnected_two_iff]

lemma Connected.tutteConnected_one_add_one (hM : M.Connected) : (M.TutteConnected (1 + 1)) :=
  hM.tutteConnected_two

lemma TutteConnected.le_girth (h : M.TutteConnected (k + 1)) (hlt : 2 * k ≤ M.E.encard) :
    k + 1 ≤ M.girth := by
  rw [← not_lt, girth_lt_iff, not_exists]
  rintro C ⟨hC, hCcard⟩
  have hlt' : (M.partition C true).eConn + 1 < k + 1 := by
    grw [eConn_partition, eConn_le_eRk, hC.eRk_add_one_eq]
    assumption
  refine h.not_isTutteSeparation (P := M.partition C true)
    (by simpa using Order.le_of_lt_add_one hlt') ?_
  grw [isTutteSeparation_iff_add_one_le_encard (fun h ↦ by simp [h] at hlt'),
    Bool.forall_bool, eConn_partition, partition_true_false, partition_apply, eConn_le_eRk,
    hC.eRk_add_one_eq, and_iff_left rfl.le, Order.le_of_lt_add_one hCcard]
  rw [← encard_diff_add_encard_of_subset hC.subset_ground] at hlt
  enat_to_nat! <;> cutsat

/-- Every `(k + 1)`-connected matroid on at most `2k` elements is uniform. -/
lemma TutteConnected.isUniform_of_encard_le (h : M.TutteConnected (k + 1))
    (hle : M.E.encard ≤ 2 * k) : M.IsUniform := by
  intro X hXE
  by_contra! hnot
  rw [not_indep_iff, not_spanning_iff] at hnot
  wlog hXcard : X.encard ≤ k generalizing M X with aux
  · refine aux h.dual (by simpa) (X := M.E \ X) diff_subset ?_ ?_
    · rwa [dep_dual_iff, codep_compl_iff, nonspanning_compl_dual_iff, and_comm]
    have := encard_diff_add_encard_of_subset hXE
    enat_to_nat!
    omega
  have hXconn : M.eConn X + 1 ≤ k := by grw [eConn_le_eRk, hnot.1.eRk_add_one_le_encard, hXcard]
  refine h.not_isTutteSeparation (P := M.partition X true) (by simpa) ?_
  simp [isTutteSeparation_iff' true, hnot.1, hnot.2]

-- lemma TutteConnected.contract {C : Set α} (h : M.TutteConnected (k + M.eRk C + 1))
--     (hnt : 2 * (k + M.eRk C) < M.E.encard + 1) : (M ／ C).TutteConnected (k + 1) := by
--   obtain rfl | hne := eq_or_ne k 0; simp
--   wlog hCE : C ⊆ M.E generalizing C with aux
--   · specialize aux (C := C ∩ M.E)
--     grw [M.eRk_mono inter_subset_left, imp_iff_right inter_subset_right,
--       contract_inter_ground_eq] at aux
--     exact aux h hnt
--   have hnt' := Order.le_of_lt_add_one hnt
--   have hgirth := h.le_girth hnt'
--   have hC : M.Indep C := indep_of_eRk_add_one_lt_girth (by enat_to_nat! <;> omega) hCE
--   have hfin : C.Finite := not_infinite.1 fun hinf ↦ by
--     simp [hC.eRk_eq_encard, hinf.encard_eq] at hnt
--   rw [tutteConnected_iff_verticallyConnected_girth]
--   refine ⟨(h.verticallyConnected.mono ?_).contract, ?_⟩
--   · grw [add_right_comm]
--   · have hle := hgirth.trans (M.girth_le_girth_contract_add C)
--     · rwa [add_right_comm, WithTop.add_le_add_iff_right
--         (M.isRkFinite_of_finite hfin).eRk_lt_top.ne] at hle
--   grw [hC.eRk_eq_encard, ← encard_diff_add_encard_of_subset hCE, ← contract_ground] at hnt
--   enat_to_nat! <;> omega

-- lemma TutteConnected.delete {D : Set α} (h : M.TutteConnected (k + M✶.eRk D + 1))
--     (hnt : 2 * (k + M✶.eRk D) < M.E.encard + 1) : (M ＼ D).TutteConnected (k + 1) :=
--   dual_contract_dual .. ▸ (h.dual.contract (by simpa)).dual

-- lemma TutteConnected.contractElem (h : M.TutteConnected (k + 1)) (hnt : 2 * k < M.E.encard + 1)
--     (e : α) : (M ／ {e}).TutteConnected k := by
--   obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
--   refine TutteConnected.contract (h.mono (by grw [eRk_singleton_le])) ?_
--   grw [eRk_singleton_le]
--   assumption


end Matroid
