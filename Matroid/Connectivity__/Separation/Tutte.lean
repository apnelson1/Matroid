import Matroid.Connectivity.Separation.Abstract

open Set Matroid.Separation Function

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Separation}
  {i : Bool}

namespace Matroid

variable {dg dg' dg_l dg_r : Bool → Matroid α → Set α → Prop}

@[mk_iff]
structure TutteDegen (M : Matroid α) (X : Set α) : Prop where
  indep : M.Indep X
  coindep : M.Coindep X

lemma tutteDegen_eq : TutteDegen (α := α) = fun M X ↦ M.Indep X ∧ M.Coindep X := by
  ext M X
  rw [M.tutteDegen_iff]

@[simp]
lemma tutteDegen_dual : M✶.TutteDegen X ↔ M.TutteDegen X := by
  simp [tutteDegen_iff, and_comm]

@[simp]
lemma tutteDegen_empty (M : Matroid α) : M.TutteDegen ∅ := by
  simp [tutteDegen_iff]

lemma TutteDegen.antitone : Antitone M.TutteDegen :=
  fun _ _ hYX h ↦ ⟨h.indep.subset hYX, h.coindep.subset hYX⟩

lemma TutteDegen.subset (h : M.TutteDegen X) (hYX : Y ⊆ X) : M.TutteDegen Y :=
  h.antitone hYX

@[simp]
lemma tutteWeight_eq_zero : M.tutteWeight X = 0 ↔ M.TutteDegen X := by
  simp [tutteWeight_def, tutteDegen_iff]

lemma SeqConnected.exists_encard_le {f} (h : M.SeqConnected Matroid.tutteWeight f)
    (P : M.Separation) : ∃ i, (P i).encard ≤ P.eConn + f P.eConn := by
  obtain ⟨i, hi⟩ := h.exists P
  exact ⟨i, by grw [← M.eConn_add_tutteWeight_eq, hi, P.eConn_eq]⟩

lemma seqConnected_tutteWeight_iff {f} (hf : f ⊤ = ⊤) :
    M.SeqConnected Matroid.tutteWeight f ↔
    ∀ (P : M.Separation), ∃ i, (P i).encard ≤ P.eConn + f P.eConn := by
  refine ⟨SeqConnected.exists_encard_le, fun h P ↦ (?_ : ∃ i, _ ≤ _)⟩
  obtain ⟨i, hi⟩ := h P
  obtain htop | htop := eq_or_ne P.eConn ⊤
  · simp [htop, hf]
  exact ⟨i, by rwa [← ENat.add_le_add_iff_left htop, ← P.eConn_eq i,
    M.eConn_add_tutteWeight_eq, P.eConn_eq]⟩

alias ⟨_, TutteDegen.dual⟩ := tutteDegen_dual

namespace Separation

abbrev IsTutteSeparation (P : M.Separation) := IsPredSeparation (fun _ ↦ TutteDegen) P

lemma isTutteSeparation_iff_forall : P.IsTutteSeparation ↔ ∀ i, M.Dep (P i) ∨ M.Codep (P i) := by
  simp_rw [IsTutteSeparation, IsPredSeparation, tutteDegen_iff, Classical.not_and_iff_not_or_not]
  simp

lemma isTutteSeparation_iff (i : Bool) :
    P.IsTutteSeparation ↔ (M.Dep (P i) ∨ M.Codep (P i)) ∧ (M.Dep (P !i) ∨ M.Codep (P !i)) := by
  simp_rw [isTutteSeparation_iff_forall, i.forall_bool']

lemma isTutteSeparation_iff' (i : Bool) : P.IsTutteSeparation ↔
    (M.Dep (P i) ∨ M.Nonspanning (P !i)) ∧ (M.Dep (P !i) ∨ M.Nonspanning (P i)) := by
  rw [isTutteSeparation_iff i, nonspanning_not_iff, ← codep_not_iff]

@[simp]
lemma isTutteSeparation_dual_iff : P.dual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_dual_iff <| by simp

alias ⟨IsTutteSeparation.of_dual, IsTutteSeparation.dual⟩ := isTutteSeparation_dual_iff

@[simp]
lemma isTutteSeparation_ofDual_iff {P : M✶.Separation} :
    P.ofDual.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_ofDual_iff <| by simp

@[simp]
lemma isTutteSeparation_symm_iff : P.symm.IsTutteSeparation ↔ P.IsTutteSeparation :=
  isPredSeparation_symm_iff

lemma IsTutteSeparation.symm (h : P.IsTutteSeparation) : P.symm.IsTutteSeparation :=
  IsPredSeparation.symm h

lemma IsTutteSeparation.codep_of_indep (hP : P.IsTutteSeparation) (hi : M.Indep (P i)) :
    M.Codep (P i) := by
  contrapose hi
  rw [isTutteSeparation_iff i, or_iff_left hi] at hP
  exact hP.1.not_indep

lemma IsTutteSeparation.nonspanning_of_indep (hP : P.IsTutteSeparation) (hi : M.Indep (P i)) :
    M.Nonspanning (P !i) :=
  nonspanning_not_iff.2 (hP.codep_of_indep hi)

lemma IsTutteSeparation.dep_of_spanning (hP : P.IsTutteSeparation) (hs : M.Spanning (P i)) :
    M.Dep (P !i) := by
  simpa using hP.dual.codep_of_indep (i := !i) (by simpa using hs.compl_coindep)

lemma isTutteSeparation_iff_lt_encard (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ ∀ i, P.eConn < (P i).encard := by
  rw [isTutteSeparation_iff_forall]
  convert Iff.rfl with i
  simp_rw [← M.eConn_add_nullity_add_nullity_dual (P i), P.eConn_eq, add_assoc]
  simp [-not_and, Classical.not_and_iff_not_or_not, hP]

lemma isTutteSeparation_iff_add_one_le_encard (hP : P.eConn ≠ ⊤) :
    P.IsTutteSeparation ↔ ∀ i, P.eConn + 1 ≤ (P i).encard := by
  convert isTutteSeparation_iff_lt_encard hP using 2 with i
  rw [ENat.add_one_le_iff hP]

lemma isTutteSeparation_of_lt_encard (h : ∀ i, P.eConn < (P i).encard) : P.IsTutteSeparation := by
  have hP : P.eConn ≠ ⊤ := by
    specialize h true
    enat_to_nat!
  rw [isTutteSeparation_iff_add_one_le_encard hP]
  exact fun i ↦ Order.add_one_le_of_lt (h i)

lemma isTutteSeparation_iff_nullity :
    P.IsTutteSeparation ↔ ∀ i, 1 ≤ M.nullity (P i) + M✶.nullity (P i) := by
  simp only [ENat.one_le_iff_ne_zero, ne_eq, add_eq_zero, nullity_eq_zero,
    Classical.not_and_iff_not_or_not, dual_ground,
    Separation.subset_ground, not_indep_iff, dep_dual_iff, isTutteSeparation_iff_forall]

lemma not_isTutteSeparation_iff_exists :
    ¬ P.IsTutteSeparation ↔ ∃ i, M.Indep (P i) ∧ M.Coindep (P i) := by
  simp_rw [isTutteSeparation_iff_forall, not_forall, not_or, Separation.not_dep_iff,
    Separation.not_codep_iff]

-- lemma not_isTutteSeparation_iff' : ¬ P.IsTutteSeparation ↔
--     (M.Indep P.left ∧ M.Spanning P.right) ∨ (M.Spanning P.left ∧ M.Indep P.right) := by
--   rw [isTutteSeparation_iff', ← not_spanning_iff, ← not_indep_iff, ← not_spanning_iff,
--     ← not_indep_iff]
--   tauto
lemma isTutteSeparation_of_encard (h : P.eConn < (P i).encard) (h' : P.eConn < (P !i).encard) :
    P.IsTutteSeparation := by
  rwa [isTutteSeparation_iff_lt_encard (fun hP ↦ by simp [hP] at h), i.forall_bool',
    and_iff_right h]

lemma IsTutteSeparation.nonempty (h : P.IsTutteSeparation) (i : Bool) : (P i).Nonempty := by
  rw [isTutteSeparation_iff i] at h
  exact h.1.elim Dep.nonempty Dep.nonempty

lemma IsTutteSeparation.ssubset_ground (h : P.IsTutteSeparation) (i : Bool) : P i ⊂ M.E := by
  refine P.subset_ground.eq_or_ssubset.elim (fun h' ↦ ?_) id
  have hne := P.compl_eq _ ▸ h.nonempty !i
  simp [h'] at hne

lemma IsTutteSeparation.exists_of_indep (h : P.IsTutteSeparation) (hi : M.Indep (P i)) :
    ∃ Q : M.Separation, Q.IsTutteSeparation ∧
      Q i ⊆ P i ∧ M.IsCocircuit (Q i) ∧ Q.eConn ≤ P.eConn := by
  obtain ⟨C, hCP, hC⟩ := (h.codep_of_indep hi).exists_isCocircuit_subset
  refine ⟨M.ofSetSep C i, ?_, ?_⟩
  · rw [isTutteSeparation_iff i, ofSetSep_apply_not, ofSetSep_apply_self,
      and_iff_right (.inr hC.codep), codep_compl_iff, ← not_spanning_iff, ← imp_iff_or_not]
    intro hCs
    obtain rfl : C = P i := hi.eq_of_spanning_subset hCs hCP
    simpa using h.dep_of_spanning hCs
  grw [← Separation.eConn_eq _ i, ofSetSep_apply_self, (hi.subset hCP).eConn_eq, ← P.eConn_eq i,
    hi.eConn_eq]
  exact ⟨hCP, hC, M✶.eRk_mono hCP⟩

lemma IsTutteSeparation.eConn_add_one_le (h : P.IsTutteSeparation) (i : Bool) :
    P.eConn + 1 ≤ (P i).encard := by
  by_cases hP : P.eConn = ⊤
  · grw [← M.eConn_le_encard, P.eConn_eq, hP, top_add]
  exact (isTutteSeparation_iff_add_one_le_encard hP).1 h i

lemma IsTutteSeparation.nontrivial (h : P.IsTutteSeparation) (hP : 1 ≤ P.eConn) (i : Bool) :
    (P i).Nontrivial := by
  grw [← two_le_encard_iff_nontrivial, ← h.eConn_add_one_le i, ← hP, one_add_one_eq_two]

lemma isTutteSeparation_iff_tutteWeight : P.IsTutteSeparation ↔ ∀ i, 0 < M.tutteWeight (P i) := by
  simp [IsTutteSeparation, isPredSeparation_iff, ← tutteWeight_eq_zero, pos_iff_ne_zero]

lemma IsTutteSeparation.tutteWeight_pos (h : P.IsTutteSeparation) (i : Bool) :
    0 < M.tutteWeight (P i) :=
  (isTutteSeparation_iff_tutteWeight.1 h) i

@[simp]
lemma isOffsetSeparation_zero : P.IsOffsetSeparation 0 ↔ P.IsTutteSeparation := by
  simp [IsOffsetSeparation, IsTutteSeparation, tutteDegen_eq]

end Separation



variable {dg dg' : Bool → ℕ∞ → Matroid α → Set α → Prop}

/-! ### Tutte Connectivity -/



-- lemma TutteDegen.delete_monotone : DeleteMonotone (α := α) TutteDegen where
--   mono_subset M X Y hY hXY := ⟨hY.1.subset hXY, hY.2.subset hXY⟩

--   mono_del M D P hD hP k := by
--     intro ⟨hi, hi'⟩
--     have := hP k
--     simp [TutteDegen, disjoint_sdiff_left, hi.diff] at this
--     apply this
--     rw [hD.delete_coindep_iff]
--     simp
--     rw [← hD.coin]
--     have := hP !k
--     simp [TutteDegen, disjoint_sdiff_left] at this

-- lemma TutteDegen.mono (h : M.TutteDegen X) (hYX : Y ⊆ X) : M.TutteDegen Y :=
--   ⟨h.1.subset hYX, h.2.subset hYX⟩

-- lemma TutteDegen.mono_delete (h : M.TutteDegen X) (hYX : Y ⊆ X) : (M ＼ Y).TutteDegen (X \ Y) :=
-- by
--   rw [TutteDegen, delete_indep_iff, and_iff_left disjoint_sdiff_left, and_iff_right (h.1.diff _),
--     coindep_def, dual_delete, (h.2.subset hYX).contract_indep_iff,
--     and_iff_right disjoint_sdiff_left]
--   exact h.2.subset <| by grind

/-- `M` is `k`-connected if the connectivity of every Tutte separation strictly exceeds `k - 2`.
The term has always been defined this way, but the difference of two is very awkward to work with;
`(k+1)`-connectedness is much more natural than `k`-connectedness.

For this reason, we use `TutteConnected (k+1)` in the API in all places except where
no convenience is lost. Vertical and Cyclic connectivities have the same issues. -/
def TutteConnected (M : Matroid α) (k : ℕ∞) := M.NumConnected TutteDegen k

lemma tutteConnected_iff_numConnected_tutteWeight_eq_zero : M.TutteConnected k ↔
    M.NumConnected (fun M X ↦ M.tutteWeight X = 0) k := by
  simp [TutteConnected]

lemma not_tutteConnected_iff_exists : ¬ M.TutteConnected (k + 1) ↔
    ∃ P : M.Separation, P.eConn + 1 ≤ k ∧ P.IsTutteSeparation :=
  not_numConnected_iff_exists

lemma tutteConnected_iff_forall : M.TutteConnected (k + 1) ↔
    ∀ (P : M.Separation), P.eConn + 1 ≤ k → ¬ P.IsTutteSeparation :=
  numConnected_iff_forall

lemma tutteConnected_top_iff_forall : M.TutteConnected ⊤ ↔
    ∀ (P : M.Separation), ¬ P.IsTutteSeparation :=
  numConnected_top_iff ..

lemma TutteConnected.dual (h : M.TutteConnected k) : M✶.TutteConnected k :=
  (NumConnected.dual h).mono_degen <| by simp

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

lemma Separation.IsTutteSeparation.not_tutteConnected (hP : P.IsTutteSeparation) :
    ¬ M.TutteConnected (P.eConn + 1 + 1) := by
  rw [not_tutteConnected_iff_exists]
  exact ⟨P, rfl.le, hP⟩

lemma TutteConnected.not_isTutteSeparation (h : M.TutteConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ¬ P.IsTutteSeparation :=
  fun h' ↦ h'.not_tutteConnected <| h.mono <| add_left_mono hP

lemma TutteConnected.exists_indep_coindep (h : M.TutteConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ∃ i, M.Indep (P i) ∧ M.Coindep (P i) := by
  simpa only [isTutteSeparation_iff_forall, not_forall, not_or, Separation.not_dep_iff,
    Separation.not_codep_iff] using h.not_isTutteSeparation hP

lemma TutteConnected.exists_encard_eq (h : M.TutteConnected (k + 1)) (hP : P.eConn + 1 ≤ k) :
    ∃ i, (P i).encard = P.eConn :=
  (h.exists_indep_coindep hP).imp fun i hi ↦ by
    simp [← M.eConn_add_nullity_add_nullity_dual (P i), hi.1.nullity_eq, hi.2.nullity_eq]

lemma tutteConnected_iff_forall_exists_encard_le (hk : k ≠ ⊤) : M.TutteConnected (k + 1) ↔
    ∀ ⦃P : M.Separation⦄, P.eConn + 1 ≤ k → ∃ i, (P i).encard ≤ P.eConn := by
  refine ⟨fun h P hP ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨i, hi⟩ := h.exists_encard_eq hP
    exact ⟨i, hi.le⟩
  rw [tutteConnected_iff_forall]
  intro P hPk hP
  obtain ⟨i, hi⟩ := h hPk
  rw [isTutteSeparation_iff_lt_encard (by enat_to_nat!)] at hP
  exact (hP i).not_ge hi

lemma TutteConnected.encard_eq_or_encard_compl_eq (h : M.TutteConnected (k + 1))
    (hX : M.eConn X + 1 ≤ k) (hXE : X ⊆ M.E := by aesop_mat) :
    X.encard = M.eConn X ∨ (M.E \ X).encard = M.eConn X := by
  have h' := h.exists_encard_eq (P := M.ofSetSep X true) (by simpa)
  simpa [or_comm, eq_comm] using h'

lemma tutteConnected_of_subsingleton (h : M.E.Subsingleton) (k : ℕ∞) : M.TutteConnected k :=
  numConnected_of_subsingleton h _ <| by simp

lemma tutteConnected_iff_numConnected_encard (hk : k ≠ ⊤) :
    M.TutteConnected k ↔ M.NumConnected (fun M X ↦ X.encard ≤ M.eConn X) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp_rw [tutteConnected_iff_forall_exists_encard_le (by simpa using hk),
    numConnected_iff_forall, isPredSeparation_iff, not_forall_not]
  simp

/-- A matroid is `InfinitelyConnected` if it is both finite and infinitely Tutte-connected.
All such matroids are uniform and nearly self-dual. -/
@[mk_iff]
structure InfinitelyConnected (M : Matroid α) : Prop where
  tutteConnected : M.TutteConnected ⊤
  finite : M.Finite

@[simp]
lemma uniqueBaseOn_tutteConnected_iff {B E : Set α} :
    (uniqueBaseOn B E).TutteConnected (k + 1) ↔ E.Subsingleton ∨ k = 0 := by
  obtain hE | hE := E.subsingleton_or_nontrivial
  · simp [(uniqueBaseOn B E).tutteConnected_of_subsingleton hE, hE]
  obtain (rfl | ⟨k,rfl⟩) := k.eq_zero_or_exists_eq_add_one; simp
  refine iff_of_false (fun ht ↦ ?_) (by simp [hE.not_subsingleton])
  obtain ⟨e, he⟩ := hE.nonempty
  refine ht.not_isTutteSeparation (P := Matroid.ofSetSep _ {e} true) (by simp) ?_
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
  rw [← not_iff_not, exists_separation_iff_not_connected, ← one_add_one_eq_two,
    not_tutteConnected_iff_exists]
  simp only [ENat.add_le_right_iff, ENat.one_ne_top, or_false]
  refine ⟨fun ⟨P, hP0, hP⟩ ↦ ⟨P, hP0, IsPredSeparation.nontrivial hP (by simp)⟩,
    fun ⟨P, hP0, hP⟩ ↦ ⟨P, hP0, ?_⟩⟩
  rw [isTutteSeparation_iff_add_one_le_encard (by simp [hP0]), hP0]
  simpa [one_le_encard_iff_nonempty, ← P.nontrivial_def]

lemma TutteConnected.connected [M.Nonempty] (hM : M.TutteConnected k) (hk : 2 ≤ k) :
    M.Connected :=
  tutteConnected_two_iff.1 (hM.mono hk)

lemma exists_of_tutteConnected_of_not_tutteConnected_add_one (hM : M.TutteConnected k)
    (hM' : ¬ M.TutteConnected (k + 1)) :
    ∃ (P : M.Separation), P.eConn + 1 = k ∧ P.IsTutteSeparation := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp at hM'
  obtain ⟨P, hPconn, hP⟩ := not_tutteConnected_iff_exists.1 hM'
  refine ⟨P, hPconn.antisymm ?_, hP⟩
  by_contra! hcon
  exact (mt <| hM.not_isTutteSeparation (P := P)) (by simpa) <| Order.le_of_lt_add_one hcon

lemma TutteConnected.exists_subsingleton_of_isTutteSeparation (hM : M.TutteConnected (2 + 1))
    (hP : P.eConn ≤ 1) : ∃ i, (P i).Subsingleton := by
  have hP' : ¬ P.IsTutteSeparation := hM.not_isTutteSeparation (P := P) (by enat_to_nat!; lia)
  simp_rw [isTutteSeparation_iff_add_one_le_encard (by enat_to_nat!),
    not_forall, not_le] at hP'
  obtain ⟨i, hlt⟩ := hP'
  refine ⟨i, encard_le_one_iff_subsingleton.1 ?_⟩
  grw [← hP, Order.le_of_lt_add_one hlt]

@[simp]
lemma emptyOn_tutteConnected (α : Type*) (k : ℕ∞) : (emptyOn α).TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp [← freeOn_empty, freeOn_tutteConnected_iff]

lemma Connected.tutteConnected_two (hM : M.Connected) : (M.TutteConnected 2) := by
  obtain rfl | hne := M.eq_emptyOn_or_nonempty; simp
  rwa [tutteConnected_two_iff]

lemma Connected.tutteConnected_one_add_one (hM : M.Connected) : (M.TutteConnected (1 + 1)) :=
  hM.tutteConnected_two

lemma TutteConnected.girth_ge (h : M.TutteConnected (k + 1)) (hlt : 2 * k ≤ M.E.encard) :
    k + 1 ≤ M.girth := by
  simp_rw [le_girth_iff, ← not_lt]
  intro C hC hCcard
  have hle : M.eConn C + 1 ≤ k := by
    grw [hC.eConn_add_one_eq, ← Order.le_of_lt_add_one hCcard, eRk_le_encard]
  have hCfin : C.Finite := by rw [← encard_lt_top_iff]; enat_to_nat!
  have h' := Or.imp Eq.le Eq.le <| h.encard_eq_or_encard_compl_eq (X := C) hle
  nth_grw 1 [M.eConn_le_eRk, ← hC.eRk_add_one_eq, or_iff_right
    ((by simpa using M.isRkFinite_of_finite hCfin))] at h'
  have aux := encard_diff_add_encard_of_subset hC.subset_ground
  grw [← encard_diff_add_encard_of_subset hC.subset_ground] at hlt
  have := M.eConn_le_encard C
  enat_to_nat! <;> lia

lemma TutteConnected.girth_ge_of_exists_eConn_ge (h : M.TutteConnected (k + 1))
    (hP : ∃ (P : M.Separation), k ≤ P.eConn) : k + 1 ≤ M.girth := by
  obtain ⟨P, hP⟩ := hP
  refine h.girth_ge ?_
  grw [← encard_diff_add_encard_of_subset (P.subset_ground (i := true)), P.compl_true, hP,
    ← M.eConn_le_encard, ← M.eConn_le_encard, P.eConn_eq, P.eConn_eq, two_mul]


/-- `U₃,₈` (for example) is `(3 + 1)`-connected with rank `3`, but not infinitely connected;
hence the bound is tight. -/
lemma TutteConnected.tutteConnected_top_of_eRank_add_one_le
    (h : M.TutteConnected (k + 1)) (hle : M.eRank + 1 ≤ k) : M.TutteConnected ⊤ := by
  rw [tutteConnected_top_iff_forall]
  refine fun P hP ↦ h.not_isTutteSeparation ?_ hP
  grw [← P.eConn_eq true, eConn_le_eRk, eRk_le_eRank, hle]

/-- `U₅,₈` (for example) is `(3 + 1)`-connected with corank `3`, but not infinitely connected.
hence the bound is tight. -/
lemma TutteConnected.tutteConnected_top_of_eRank_dual_add_one_le
    (h : M.TutteConnected (k + 1)) (hle : M✶.eRank + 1 ≤ k) : M.TutteConnected ⊤ := by
  simpa using h.dual.tutteConnected_top_of_eRank_add_one_le hle

lemma TutteConnected.tutteConnected_top_of_encard_add_one_le
    (h : M.TutteConnected (k + 1)) (hlt : M.E.encard + 1 ≤ 2 * k) : M.TutteConnected ⊤ := by
  wlog hle : M.eRank ≤ M✶.eRank generalizing M with aux
  · simpa using aux h.dual (by simpa) (by simpa using (not_le.1 hle).le)
  obtain hle | hlt' := le_or_gt (M.eRank + 1) k
  · exact h.tutteConnected_top_of_eRank_add_one_le hle
  grw [← M.eRank_add_eRank_dual] at hlt
  eomega

lemma TutteConnected.girth_ge_of_not_tutteConnected_top (h : M.TutteConnected k)
    (h_top : ¬ M.TutteConnected ⊤) : k ≤ M.girth := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine h.girth_ge ?_
  contrapose! h_top
  exact h.tutteConnected_top_of_encard_add_one_le (Order.add_one_le_of_lt h_top)

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
  refine h.not_isTutteSeparation (P := M.ofSetSep X true) (by simpa) ?_
  simp [isTutteSeparation_iff' true, hnot.1, hnot.2]

/-- If a `(k + 1)`-connected matroid `M` has a finite circuit/cocircuit of size `k + 1`,
then `M` is a self-dual uniform matroid of rank `k`. -/
lemma IsCircuit.exists_eq_unifOn_of_isCocircuit_of_tutteConnected {C : Set α} (hC : M.IsCircuit C)
    (hC' : M.IsCocircuit C) (hCk : C.encard = k + 1) (hk : k ≠ ⊤) (hM : M.TutteConnected (k + 1)) :
    ∃ (E : Set α) (r : ℕ), r = k ∧ E.encard = 2 * k ∧ M = unifOn E r := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · obtain ⟨e, rfl⟩ := encard_eq_one.1 (show C.encard = 1 by simpa using hCk)
    simp only [singleton_isCircuit, dual_isLoop_iff_isColoop] at hC hC'
    exact False.elim <| hC.not_isColoop hC'
  obtain hCconn : M.eConn C = k := by
    rw [← ENat.add_one_eq_add_one_iff, hC.eConn_add_one_eq, ← ENat.add_one_eq_add_one_iff,
      hC'.eRk_add_one_eq, hCk]
  have hcard := hM.encard_eq_or_encard_compl_eq (X := C) (by simp [hCconn])
  have hfin : M✶.IsRkFinite C := by grw [← eRk_lt_top_iff, eRk_le_encard]; enat_to_nat!
  rw [← ENat.add_one_eq_add_one_iff, hC.eConn_add_one_eq, ← ENat.add_one_eq_add_one_iff,
    ← hC'.eRk_add_one_eq, or_iff_right (by simpa [add_assoc]), hCconn] at hcard
  have hEcard : M.E.encard = 2 * (k + 1) := by
    rw [← encard_diff_add_encard_of_subset hC.subset_ground, hCk, hcard]
    enat_to_nat; lia
  have hgirth : k + 1 < M.girth := by
    grw [← hM.girth_ge (by simp [hEcard])]
    enat_to_nat; lia
  have hgirth_dual : k + 1 < M✶.girth := by
    grw [← hM.dual.girth_ge (by simp [hEcard])]
    enat_to_nat; lia
  have hrank : M.eRank = k + 1 := by
    rw [← Coindep.delete_eRank_eq (X := M.E \ C), delete_compl, eRank_restrict,
      ← ENat.add_one_eq_add_one_iff, ← hCk, hC.eRk_add_one_eq]
    exact indep_of_card_lt_girth (by enat_to_nat! <;> lia) diff_subset
  have hfin : M.Finite := by
    rw [finite_iff, ← encard_lt_top_iff]
    enat_to_nat!
  obtain ⟨E, r, hrE, rfl, hr⟩ := (M.isUniform_of_eRank_lt_girth (hrank ▸ hgirth)).exists_eq_unifOn
  refine ⟨E, r, ?_, by simpa using hEcard, rfl⟩
  rwa [unifOn_eRank_eq' hrE] at hrank

lemma tutteConnected_iff_seqConnected : M.TutteConnected (k + 1) ↔
    M.SeqConnected Matroid.tutteWeight (indicator {i | k < i + 1} ⊤) := by
  simp [seqConnected_indicator_iff_numConnected, TutteConnected]

lemma tutteConnected_iff_seqConnected' : M.TutteConnected k ↔
    M.SeqConnected Matroid.tutteWeight (indicator {i | k < i + 1 + 1} ⊤) := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one <;>
  simp [tutteConnected_iff_seqConnected]

lemma TutteConnected.eConn_union_le_of_eConn_le_eConn_le_card_ge (hM : M.TutteConnected (k + 1))
    {P Q : M.Separation} (hP : P.eConn ≤ k) (hQ : Q.eConn ≤ k) {b c : Bool}
    (hcard : k ≤ (P b ∩ Q c).encard) : (P.union Q b c).eConn ≤ k := by
  by_contra! hcon
  have hk : k ≠ ⊤ := by enat_to_nat!
  have hsm := P.eConn_inter_add_eConn_union_le Q b c
  obtain hle | hlt := le_or_gt k (P.inter Q b c).eConn
  · grw [hP, hQ, ← hle, ENat.add_le_add_iff_left hk] at hsm
    exact hcon.not_ge hsm
  refine hM.not_isTutteSeparation (Order.add_one_le_of_lt hlt) ?_
  rw [isTutteSeparation_iff_add_one_le_encard (by enat_to_nat!)]
  rintro (rfl | rfl)
  · grw [Order.add_one_le_of_lt hlt, P.inter_apply_false,
      ← show P (!b) ∩ Q (!c) ⊆ P (!b) ∪ Q !c by grind, ← P.union_apply_false,
      ← M.eConn_le_encard, eConn_eq, hcon]
  grw [Order.add_one_le_of_lt hlt, P.inter_apply_true, hcard]


  -- cases k with
  -- | top => simp
  -- | coe k =>
  --   have hsm := P.eConn_inter_add_eConn_union_le Q b c

  --   grw [hP, hQ] at hsm
  --   have := hM.not_isTutteSeparation (P := P.inter Q b c)




-- lemma tutteConnected_iff_biConnected :
--     M.TutteConnected (k + 1) ↔ M.BiConnected (· + ·) (indicator {i | k < i + 1} ⊤) := by
--   refine ⟨fun h P ↦ ?_, fun h P ↦ ?_⟩
--   · obtain hlt | hle := lt_or_ge k (P.eConn + 1)
--     · simp [hlt]
--     simpa [-Bool.exists_bool, hle, ← not_isTutteSeparation_iff_exists] using
--       h.not_isTutteSeparation hle
--   obtain hlt | hle := lt_or_ge k (P.eConn + 1)
--   · simp [hlt.not_ge]
--   obtain ⟨i, hi⟩ := h.exists P
--   exact ⟨i, by simpa [hle, tutteDegen_iff] using hi⟩

-- lemma tutteConnected_iff_biConnected' :
--     M.TutteConnected k ↔ M.BiConnected (· + ·) (indicator {i | k < i + 1 + 1} ⊤) := by
--   obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one <;>
--   simp [tutteConnected_iff_biConnected]

-- lemma tutteConnected_iff_offsetConnected :
--     M.TutteConnected (k + 1) ↔ M.OffsetConnected (indicator {i | k < i + 1} ⊤) := by
--   refine ⟨fun h P ↦ ?_, fun h P ↦ ?_⟩
--   · obtain hlt | hle := lt_or_ge k (P.eConn + 1)
--     · simp [hlt]
--     simpa [-Bool.exists_bool, hle, ← not_isTutteSeparation_iff_exists] using
--       h.not_isTutteSeparation hle
--   obtain hlt | hle := lt_or_ge k (P.eConn + 1)
--   · simp [hlt.not_ge]
--   obtain ⟨i, hi⟩ := h.exists P
--   exact ⟨i, by simpa [hle, tutteDegen_iff] using hi⟩

-- lemma tutteConnected_iff_offsetConnected' :
--     M.TutteConnected k ↔ M.OffsetConnected (indicator {i | k < i + 1 + 1} ⊤) := by
--   obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one <;>
--   simp [tutteConnected_iff_offsetConnected]


  -- rw [tutteConnected_iff_verticallyConnected_girth]
  -- refine ⟨(h.verticallyConnected.mono ?_).contract, ?_⟩
  -- · grw [add_right_comm]
  -- · have hle := hgirth.trans (M.girth_le_girth_contract_add C)
  --   · rwa [add_right_comm, WithTop.add_le_add_iff_right
  --       (M.isRkFinite_of_finite hfin).eRk_lt_top.ne] at hle
  -- grw [hC.eRk_eq_encard, ← encard_diff_add_encard_of_subset hCE, ← contract_ground] at hnt
  -- enat_to_nat! <;> omega




end Matroid
