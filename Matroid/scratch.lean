import Mathlib.Data.Matroid.Loop

open Set

variable {α β : Type*} {M M' N : Matroid α} {e f : α} {I C J R B X Y Z K S : Set α}

namespace Matroid




lemma closure_loops (M : Matroid α) : M.closure M.loops = M.loops :=
  M.closure_closure ∅

lemma closure_union_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M.loops) = M.closure X := by
  rw [closure_union_closure_right_eq, union_empty]

@[simp] lemma closure_diff_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X \ M.loops) = M.closure X := by
  rw [← M.closure_union_loops_eq (X \ M.loops), diff_union_self,
    closure_union_closure_right_eq, union_empty]

section IsNonloop

/-- A `nonloop` is an element that is not a loop -/
def IsNonloop (M : Matroid α) (e : α) : Prop :=
  ¬M.IsLoop e ∧ e ∈ M.E

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsNonloop.mem_ground (h : M.IsNonloop e) : e ∈ M.E :=
  h.2

lemma IsNonloop.not_isLoop (he : M.IsNonloop e) : ¬M.IsLoop e :=
  he.1

lemma IsLoop.not_isNonloop (he : M.IsLoop e) : ¬M.IsNonloop e :=
  fun h ↦ h.not_isLoop he

lemma isNonloop_of_not_isLoop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsLoop e) : M.IsNonloop e :=
  ⟨h,he⟩

lemma isLoop_of_not_isNonloop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsNonloop e) : M.IsLoop e :=
  by rwa [IsNonloop, and_iff_left he, not_not] at h

@[simp] lemma not_isLoop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsLoop e ↔ M.IsNonloop e :=
  (and_iff_left he).symm

@[simp] lemma not_isNonloop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsNonloop e ↔ M.IsLoop e := by
  rw [← not_isLoop_iff, not_not]

lemma isNonloop_iff_mem_compl_loops : M.IsNonloop e ↔ e ∈ M.E \ M.loops := by
  rw [IsNonloop, IsLoop, and_comm, mem_diff]

lemma setOf_isNonloop_eq (M : Matroid α) : {e | M.IsNonloop e} = M.E \ M.loops :=
  Set.ext (fun _ ↦ isNonloop_iff_mem_compl_loops)

lemma not_isNonloop_iff_closure : ¬ M.IsNonloop e ↔ M.closure {e} = M.loops := by
  by_cases he : e ∈ M.E
  · simp [IsNonloop, isLoop_iff_closure_eq_loops_and_mem_ground, he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he,
    (show ¬ M.IsNonloop e from fun h ↦ he h.mem_ground)]

lemma isLoop_or_isNonloop (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ∨ M.IsNonloop e := by
  rw [IsNonloop, and_iff_left he]; apply em

@[simp] lemma indep_singleton : M.Indep {e} ↔ M.IsNonloop e := by
  rw [IsNonloop, ← singleton_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, singleton_subset_iff.mp h.subset_ground⟩, fun h ↦ h.1 h.2⟩

alias ⟨Indep.isNonloop, IsNonloop.indep⟩ := indep_singleton

lemma Indep.isNonloop_of_mem (hI : M.Indep I) (h : e ∈ I) : M.IsNonloop e := by
  rw [← not_isLoop_iff (hI.subset_ground h)]; exact fun he ↦ (he.not_mem_of_indep hI) h

lemma IsNonloop.exists_mem_isBase (he : M.IsNonloop e) : ∃ B, M.IsBase B ∧ e ∈ B := by
  simpa using (indep_singleton.2 he).exists_isBase_superset

lemma IsCocircuit.isNonloop_of_mem (hK : M.IsCocircuit K) (he : e ∈ K) : M.IsNonloop e := by
  rw [← not_isLoop_iff (hK.subset_ground he), ← singleton_isCircuit]
  intro he'
  obtain ⟨f, ⟨rfl, -⟩, hfe⟩ := (he'.isCocircuit_inter_nontrivial hK ⟨e, by simp [he]⟩).exists_ne e
  exact hfe rfl

lemma IsCircuit.isNonloop_of_mem (hC : M.IsCircuit C) (hC' : C.Nontrivial) (he : e ∈ C) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop (hC.subset_ground he)
    (fun hL ↦ by simp [hL.eq_of_isCircuit_mem hC he] at hC')

lemma IsCircuit.isNonloop_of_mem_of_one_lt_card (hC : M.IsCircuit C) (h : 1 < C.encard)
    (he : e ∈ C) : M.IsNonloop e := by
  refine isNonloop_of_not_isLoop (hC.subset_ground he) (fun hlp ↦ ?_)
  rw [hlp.eq_of_isCircuit_mem hC he, encard_singleton] at h
  exact h.ne rfl

lemma isNonloop_of_not_mem_closure (h : e ∉ M.closure X) (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop he (fun hel ↦ h (hel.mem_closure X))

lemma isNonloop_iff_not_mem_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e ↔ e ∉ M.loops := by rw [IsNonloop, isLoop_iff, and_iff_left he]

lemma IsNonloop.mem_closure_singleton (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    f ∈ M.closure {e} := by
  rw [← union_empty {_}, singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_not_mem_loops he.mem_ground).1 he⟩).1

lemma IsNonloop.mem_closure_comm (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    f ∈ M.closure {e} ↔ e ∈ M.closure {f} :=
  ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩

lemma IsNonloop.isNonloop_of_mem_closure (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    M.IsNonloop f := by
  rw [IsNonloop, and_comm]
  by_contra! h; apply he.not_isLoop
  rw [isLoop_iff] at *; convert hef using 1
  obtain (hf | hf) := em (f ∈ M.E)
  · rw [← closure_loops, ← insert_eq_of_mem (h hf), closure_insert_congr_right M.closure_loops,
      insert_emptyc_eq]
  rw [eq_comm, ← closure_inter_ground, inter_comm, inter_singleton_eq_empty.mpr hf]

lemma IsNonloop.closure_eq_of_mem_closure (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    M.closure {e} = M.closure {f} := by
  rw [← closure_closure _ {f}, ← insert_eq_of_mem hef, closure_insert_closure_eq_closure_insert,
    ← closure_closure _ {e}, ← insert_eq_of_mem (he.mem_closure_singleton hef),
    closure_insert_closure_eq_closure_insert, pair_comm]

lemma IsNonloop.closure_eq_closure_iff_isCircuit_of_ne (he : M.IsNonloop e) (hef : e ≠ f) :
    M.closure {e} = M.closure {f} ↔ M.IsCircuit {e, f} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hf := he.isNonloop_of_mem_closure (by rw [← h]; exact M.mem_closure_self e)
    rw [isCircuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff,
      and_iff_right he.mem_ground, singleton_subset_iff, and_iff_left hf.mem_ground]
    suffices ¬ M.Indep {e, f} by simpa [pair_diff_left hef, hf, pair_diff_right hef, he]
    rw [Indep.insert_indep_iff_of_not_mem (by simpa) (by simpa)]
    simp [← h, mem_closure_self _ _ he.mem_ground]
  have hclosure := (h.closure_diff_singleton_eq e).trans
    (h.closure_diff_singleton_eq f).symm
  rwa [pair_diff_left hef, pair_diff_right hef, eq_comm] at hclosure

lemma IsNonloop.closure_eq_closure_iff_eq_or_dep (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    M.closure {e} = M.closure {f} ↔ e = f ∨ ¬M.Indep {e, f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.closure_eq_closure_iff_isCircuit_of_ne hne, or_iff_right hne,
    isCircuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff, singleton_subset_iff,
    and_iff_left hf.mem_ground, and_iff_left he.mem_ground, and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_diff_left hne, indep_singleton]
  rwa [pair_diff_right hne, indep_singleton]

lemma exists_isNonloop (M : Matroid α) [RankPos M] : ∃ e, M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  ⟨_, hB.indep.isNonloop_of_mem hB.nonempty.some_mem⟩

lemma IsNonloop.rankPos (h : M.IsNonloop e) : M.RankPos :=
  h.indep.rankPos_of_nonempty (singleton_nonempty e)

@[simp] lemma restrict_isNonloop_iff {R : Set α} : (M ↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e ∈ R := by
  rw [← indep_singleton, restrict_indep_iff, singleton_subset_iff, indep_singleton]

lemma IsNonloop.of_restrict {R : Set α} (h : (M ↾ R).IsNonloop e) : M.IsNonloop e :=
  (restrict_isNonloop_iff.1 h).1

lemma IsNonloop.of_isRestriction (h : N.IsNonloop e) (hNM : N ≤r M) : M.IsNonloop e := by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict

lemma isNonloop_iff_restrict_of_mem {R : Set α} (he : e ∈ R) :
    M.IsNonloop e ↔ (M ↾ R).IsNonloop e :=
  ⟨fun h ↦ restrict_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_restrict⟩

@[simp] lemma comap_isNonloop_iff {M : Matroid β} {f : α → β} :
    (M.comap f).IsNonloop e ↔ M.IsNonloop (f e) := by
  rw [← indep_singleton, comap_indep_iff, image_singleton, indep_singleton,
    and_iff_left (injOn_singleton _ _)]

@[simp] lemma freeOn_isNonloop_iff {E : Set α} : (freeOn E).IsNonloop e ↔ e ∈ E := by
  rw [← indep_singleton, freeOn_indep_iff, singleton_subset_iff]

@[simp] lemma uniqueBaseOn_isNonloop_iff {I E : Set α} :
    (uniqueBaseOn I E).IsNonloop e ↔ e ∈ I ∩ E := by
  rw [← indep_singleton, uniqueBaseOn_indep_iff', singleton_subset_iff]

lemma IsNonloop.exists_mem_isCocircuit (he : M.IsNonloop e) : ∃ K, M.IsCocircuit K ∧ e ∈ K := by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_isBase
  exact ⟨_, fundCocircuit_isCocircuit heB hB, mem_fundCocircuit M e B⟩

@[simp]
lemma closure_inter_setOf_isNonloop_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∩ {e | M.IsNonloop e}) = M.closure X := by
  rw [setOf_isNonloop_eq, ← inter_diff_assoc, closure_diff_loops_eq, closure_inter_ground]

end IsNonloop
#lint
