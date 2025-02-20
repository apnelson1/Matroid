import Matroid.Circuit
import Matroid.ForMathlib.Finset
import Matroid.OnUniv

/-
  A `Loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.closure ∅`.
  Thus, the set of loops of `M` is equal to `M.closure ∅`, and we prefer this notation instead of
  `{e | M.IsLoop e}` or similar. A `Nonloop` is an element of the ground set that is not a loop.
-/


variable {α β : Type*} {M N : Matroid α} {e f : α} {B L L' I X Y Z F C K : Set α}

open Set
open scoped symmDiff

namespace Matroid

section IsLoop
/-- A loop is a member of the closure of the empty set -/
def IsLoop (M : Matroid α) (e : α) : Prop :=
  e ∈ M.closure ∅

lemma isLoop_iff_mem_closure_empty : M.IsLoop e ↔ e ∈ M.closure ∅ := Iff.rfl

lemma closure_empty_eq_loops (M : Matroid α) : M.closure ∅ = {e | M.IsLoop e} := rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsLoop.mem_ground (he : M.IsLoop e) : e ∈ M.E :=
  closure_subset_ground M ∅ he

@[simp] lemma singleton_dep : M.Dep {e} ↔ M.IsLoop e := by
  rw [isLoop_iff_mem_closure_empty, M.empty_indep.mem_closure_iff_of_not_mem (not_mem_empty e),
    insert_emptyc_eq]

@[simp] lemma singleton_not_indep (he : e ∈ M.E := by aesop_mat) : ¬M.Indep {e} ↔ M.IsLoop e :=
  by rw [← singleton_dep, ← not_indep_iff]

lemma IsLoop.dep (he : M.IsLoop e) : M.Dep {e} :=
  singleton_dep.mpr he

lemma singleton_isCircuit : M.IsCircuit {e} ↔ M.IsLoop e := by
  simp [← singleton_dep, isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]

lemma isLoop_iff_not_mem_isBase_forall (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ ∀ B, M.IsBase B → e ∉ B := by
  rw [← singleton_dep, ← not_indep_iff, not_iff_comm, not_forall]
  simp_rw [_root_.not_imp, not_not, ← singleton_subset_iff, indep_iff]

lemma IsLoop.isCircuit (he : M.IsLoop e) : M.IsCircuit {e} :=
  singleton_isCircuit.mpr he

lemma IsLoop.mem_closure (he : M.IsLoop e) (X : Set α) : e ∈ M.closure X :=
  M.closure_mono (empty_subset _) he

lemma IsLoop.mem_isFlat (he : M.IsLoop e) {F : Set α} (hF : M.IsFlat F) : e ∈ F := by
  have := he.mem_closure F; rwa [hF.closure] at this

lemma IsFlat.loops_subset (hF : M.IsFlat F) : M.closure ∅ ⊆ F := fun _ he ↦ IsLoop.mem_isFlat he hF

lemma IsLoop.dep_of_mem (he : M.IsLoop e) (h : e ∈ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  he.dep.superset (singleton_subset_iff.mpr h) hXE

lemma IsLoop.not_indep_of_mem (he : M.IsLoop e) (h : e ∈ X) : ¬M.Indep X := fun hX ↦
  he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

lemma IsLoop.not_mem_of_indep (he : M.IsLoop e) (hI : M.Indep I) : e ∉ I := fun h ↦
  he.not_indep_of_mem h hI

lemma IsLoop.eq_of_isCircuit_mem (he : M.IsLoop e) (hC : M.IsCircuit C) (h : e ∈ C) : C = {e} := by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]

lemma Indep.disjoint_loops (hI : M.Indep I) : Disjoint I (M.closure ∅) :=
  by_contra fun h ↦
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.not_mem_of_indep he hI heI

lemma Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I ⊆ M.closure ∅) : I = ∅ :=
  eq_empty_iff_forall_not_mem.mpr fun _ he ↦ IsLoop.not_mem_of_indep (h he) hI he

@[simp] lemma isBasis_loops_iff : M.IsBasis I (M.closure ∅) ↔ I = ∅ := by
  refine ⟨fun h ↦ h.indep.eq_empty_of_subset_loops h.subset, ?_⟩
  rintro rfl
  exact M.empty_indep.isBasis_closure

lemma closure_eq_loops_of_subset (h : X ⊆ M.closure ∅) : M.closure X = M.closure ∅ :=
  (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))

lemma isBasis_iff_empty_of_subset_loops (hX : X ⊆ M.closure ∅) : M.IsBasis I X ↔ I = ∅ := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simpa⟩
  replace h := (closure_eq_loops_of_subset hX) ▸ h.isBasis_closure_right
  simpa using h

lemma IsLoop.closure (he : M.IsLoop e) : M.closure {e} = M.closure ∅ :=
  closure_eq_loops_of_subset (singleton_subset_iff.mpr he)

lemma isLoop_iff_closure_eq_closure_empty' :
    M.IsLoop e ↔ M.closure {e} = M.closure ∅ ∧ e ∈ M.E := by
  rw [← singleton_dep, dep_iff, singleton_subset_iff, and_congr_left_iff]
  intro he
  rw [not_indep_iff, singleton_dep]
  exact ⟨fun h ↦ by rw [h.closure],
    fun h ↦ by rw [isLoop_iff_mem_closure_empty, ← h]; exact M.mem_closure_self e⟩

lemma isLoop_iff_closure_eq_closure_empty (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ M.closure {e} = M.closure ∅ := by
  rw [isLoop_iff_closure_eq_closure_empty', and_iff_left he]

lemma isLoop_iff_forall_mem_compl_isBase : M.IsLoop e ↔ ∀ B, M.IsBase B → e ∈ M.E \ B := by
  refine ⟨fun h B hB ↦ mem_of_mem_of_subset h ?_, fun h ↦ ?_⟩
  · rw [subset_diff, and_iff_right (closure_subset_ground _ _), disjoint_iff_inter_eq_empty,
      hB.indep.closure_inter_eq_self_of_subset (empty_subset B)]
  have he : e ∈ M.E := M.exists_isBase.elim (fun B hB ↦ (h B hB).1)
  rw [← singleton_dep, ← not_indep_iff]
  intro hei
  obtain ⟨B, hB, heB⟩ := hei.exists_isBase_superset
  exact (h B hB).2 (singleton_subset_iff.mp heB)

@[simp] lemma restrict_isLoop_iff {R : Set α} :
    (M ↾ R).IsLoop e ↔ e ∈ R ∧ (M.IsLoop e ∨ e ∉ M.E) := by
  rw [← singleton_dep, restrict_dep_iff, singleton_subset_iff, ← singleton_dep, and_comm,
    and_congr_right_iff, Dep, and_or_right, singleton_subset_iff, and_iff_left or_not,
    or_iff_left_of_imp (fun he hi ↦ he (singleton_subset_iff.1 hi.subset_ground))]
  simp only [singleton_subset_iff, implies_true]

lemma isRestriction_isLoop_iff (hNM : N ≤r M) :
    N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE ↦ (heE (hR heR)).elim

lemma IsLoop.of_isRestriction (he : N.IsLoop e) (hNM : N ≤r M) : M.IsLoop e :=
  ((isRestriction_isLoop_iff hNM).1 he).2

lemma IsLoop.isLoop_isRestriction (he : M.IsLoop e) (hNM : N ≤r M) (heN : e ∈ N.E) : N.IsLoop e :=
  (isRestriction_isLoop_iff hNM).2 ⟨heN, he⟩

@[simp] lemma comap_isLoop_iff {M : Matroid β} {f : α → β} :
    (M.comap f).IsLoop e ↔ M.IsLoop (f e) := by
  rw [← singleton_dep, comap_dep_iff]
  simp

@[simp] lemma loopyOn_isLoop_iff {E : Set α} : (loopyOn E).IsLoop e ↔ e ∈ E := by
  simp [IsLoop]

end IsLoop

section IsLoopEquiv

lemma closure_union_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M.closure ∅) = M.closure X := by
  rw [closure_union_closure_right_eq, union_empty]

@[simp] lemma closure_diff_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X \ M.closure ∅) = M.closure X := by
  rw [← M.closure_union_loops_eq (X \ M.closure ∅), diff_union_self,
    closure_union_closure_right_eq, union_empty]

/-- Two sets are `IsLoopEquiv` in `M` if their symmetric difference contains only loops. -/
def IsLoopEquiv (M : Matroid α) (X Y : Set α) := X ∪ M.closure ∅ = Y ∪ M.closure ∅

lemma isLoopEquiv_iff_union_eq_union :
    M.IsLoopEquiv X Y ↔ X ∪ M.closure ∅ = Y ∪ M.closure ∅ := Iff.rfl

lemma IsLoopEquiv.union_eq_union (h : M.IsLoopEquiv X Y) : X ∪ M.closure ∅ = Y ∪ M.closure ∅ := h

lemma IsLoopEquiv.diff_eq_diff (h : M.IsLoopEquiv X Y) : X \ M.closure ∅ = Y \ M.closure ∅ := by
  rw [subset_antisymm_iff, diff_subset_iff, union_diff_self, union_comm, ← h.union_eq_union,
    diff_subset_iff, union_diff_self, union_comm _ X, and_iff_right subset_union_left,
    h.union_eq_union]
  apply subset_union_left

lemma IsLoopEquiv.rfl (M : Matroid α) {X : Set α} : M.IsLoopEquiv X X := by
  rfl

lemma IsLoopEquiv.symm (h : M.IsLoopEquiv X Y) : M.IsLoopEquiv Y X :=
  Eq.symm h

lemma IsLoopEquiv.comm : M.IsLoopEquiv X Y ↔ M.IsLoopEquiv Y X :=
  ⟨IsLoopEquiv.symm, IsLoopEquiv.symm⟩

lemma IsLoopEquiv.trans (hXY : M.IsLoopEquiv X Y) (hYZ : M.IsLoopEquiv Y Z) : M.IsLoopEquiv X Z :=
  Eq.trans hXY hYZ

lemma IsLoopEquiv.diff_subset_loops (h : M.IsLoopEquiv X Y) : X \ Y ⊆ M.closure ∅ := by
  rw [diff_subset_iff, ← h.union_eq_union]
  exact subset_union_left

lemma IsLoopEquiv.symmDiff_subset_loops : M.IsLoopEquiv X Y ↔ X ∆ Y ⊆ M.closure ∅ := by
  rw [Set.symmDiff_def, union_subset_iff]
  refine ⟨fun h ↦ ⟨h.diff_subset_loops, h.symm.diff_subset_loops⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  rw [diff_subset_iff] at h1 h2
  rw [isLoopEquiv_iff_union_eq_union, subset_antisymm_iff, union_subset_iff, union_subset_iff]
  exact ⟨⟨h1, subset_union_right⟩, h2, subset_union_right⟩

lemma isLoopEquiv_union (X : Set α) (hL : L ⊆ M.closure ∅) : M.IsLoopEquiv X (X ∪ L) := by
   rw [isLoopEquiv_iff_union_eq_union, union_assoc, union_eq_self_of_subset_left hL]

lemma isLoopEquiv_diff (X : Set α) (hL : L ⊆ M.closure ∅) : M.IsLoopEquiv X (X \ L) := by
  rw [IsLoopEquiv.comm]
  refine (isLoopEquiv_union (X \ L) hL).trans ?_
  rw [diff_union_self, IsLoopEquiv.comm]
  exact isLoopEquiv_union X hL

lemma isLoopEquiv_union_diff (X : Set α) (hL : L ⊆ M.closure ∅) (hL' : L' ⊆ M.closure ∅) :
    M.IsLoopEquiv X ((X ∪ L) \ L') :=
  (isLoopEquiv_union X hL).trans (isLoopEquiv_diff _ hL')

lemma isLoopEquiv_union_loops (M : Matroid α) (X : Set α) : M.IsLoopEquiv X (X ∪ M.closure ∅) :=
  isLoopEquiv_union X Subset.rfl

lemma isLoopEquiv_diff_loops (M : Matroid α) (X : Set α) : M.IsLoopEquiv X (X \ M.closure ∅) :=
  isLoopEquiv_diff X Subset.rfl

lemma IsLoopEquiv.exists_diff_union_loops (h : M.IsLoopEquiv X Y) :
    ∃ L L', L ⊆ M.closure ∅ ∧ L' ⊆ M.closure ∅ ∧ Y = (X ∪ L) \ L' :=
  ⟨_, _, h.symm.diff_subset_loops, h.diff_subset_loops, by aesop⟩

lemma IsLoopEquiv.subset_union_loops (h : M.IsLoopEquiv X Y) : Y ⊆ X ∪ M.closure ∅ := by
  rw [h.union_eq_union]; exact subset_union_left

lemma IsLoopEquiv.closure_eq_closure (h : M.IsLoopEquiv X Y) : M.closure X = M.closure Y := by
  rw [← closure_union_loops_eq, h.union_eq_union, closure_union_loops_eq]

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma IsLoopEquiv.subset_ground (h : M.IsLoopEquiv X Y) (hX : X ⊆ M.E := by aesop_mat) : Y ⊆ M.E :=
  h.subset_union_loops.trans (union_subset hX (M.closure_subset_ground ∅))

lemma IsLoopEquiv.inter_eq_of_indep (h : M.IsLoopEquiv X Y) (hI : M.Indep I) : X ∩ I = Y ∩ I := by
  rw [show X ∩ I = (X ∪ M.closure ∅) ∩ I
    by rw [union_inter_distrib_right, hI.disjoint_loops.symm.inter_eq, union_empty],
    h.union_eq_union, union_inter_distrib_right, hI.disjoint_loops.symm.inter_eq, union_empty]

lemma IsLoopEquiv.subset_iff_of_indep (h : M.IsLoopEquiv X Y) (hI : M.Indep I) : I ⊆ X ↔ I ⊆ Y := by
  rw [← sdiff_eq_left.2 hI.disjoint_loops, diff_subset_iff, diff_subset_iff,
    union_comm, h.union_eq_union, union_comm]

lemma IsLoopEquiv.isBasis_iff (h : M.IsLoopEquiv X Y) : M.IsBasis I X ↔ M.IsBasis I Y := by
  rw [isBasis_iff_indep_subset_closure, isBasis_iff_indep_subset_closure, and_congr_right_iff]
  intro hI
  rw [h.subset_iff_of_indep hI, and_congr_right_iff,
    show M.closure I = M.closure I ∪ M.closure ∅ by simp,
    union_comm, ← diff_subset_iff,  h.diff_eq_diff, diff_subset_iff]
  exact fun _ ↦ Iff.rfl

lemma isBasis_union_iff_isBasis_of_subset_loops (hL : L ⊆ M.closure ∅) :
    M.IsBasis I (X ∪ L) ↔ M.IsBasis I X :=
  (isLoopEquiv_union X hL).symm.isBasis_iff

lemma isBasis_diff_iff_isBasis_of_subset_loops (hL : L ⊆ M.closure ∅) :
    M.IsBasis I (X \ L) ↔ M.IsBasis I X :=
  (isLoopEquiv_diff X hL).symm.isBasis_iff

lemma closure_union_eq_closure_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.closure ∅) :
    M.closure (X ∪ Y) = M.closure X :=
  (isLoopEquiv_union X hY).symm.closure_eq_closure

lemma closure_diff_eq_closure_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.closure ∅) :
    M.closure (X \ Y) = M.closure X :=
  (isLoopEquiv_diff X hY).symm.closure_eq_closure

end IsLoopEquiv

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

lemma isNonloop_iff_mem_compl_loops : M.IsNonloop e ↔ e ∈ M.E \ M.closure ∅ := by
  rw [IsNonloop, IsLoop, and_comm, mem_diff]

lemma setOf_isNonloop_eq (M : Matroid α) : {e | M.IsNonloop e} = M.E \ M.closure ∅ :=
  Set.ext (fun _ ↦ isNonloop_iff_mem_compl_loops)

lemma not_isNonloop_iff_closure : ¬ M.IsNonloop e ↔ M.closure {e} = M.closure ∅ := by
  by_cases he : e ∈ M.E
  · simp [IsNonloop, and_comm, not_and, not_not, isLoop_iff_closure_eq_closure_empty', he]
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

lemma Cocircuit.isNonloop_of_mem (hK : M.Cocircuit K) (he : e ∈ K) : M.IsNonloop e := by
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

lemma isNonloop_iff_not_mem_closure_empty (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e ↔ e ∉ M.closure ∅ := by rw [IsNonloop, isLoop_iff_mem_closure_empty,
      and_iff_left he]

lemma IsNonloop.mem_closure_singleton (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    f ∈ M.closure {e} := by
  rw [← union_empty {_}, singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_not_mem_closure_empty he.mem_ground).1 he⟩).1

lemma IsNonloop.mem_closure_comm (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    f ∈ M.closure {e} ↔ e ∈ M.closure {f} :=
  ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩

lemma IsNonloop.isNonloop_of_mem_closure (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    M.IsNonloop f := by
  rw [IsNonloop, and_comm]
  by_contra! h; apply he.not_isLoop
  rw [isLoop_iff_mem_closure_empty] at *; convert hef using 1
  obtain (hf | hf) := em (f ∈ M.E)
  · rw [← closure_closure _ ∅, ← insert_eq_of_mem (h hf),
      closure_insert_closure_eq_closure_insert, insert_emptyc_eq]
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

lemma IsNonloop.exists_mem_isCocircuit (he : M.IsNonloop e) : ∃ K, M.Cocircuit K ∧ e ∈ K := by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_isBase
  exact ⟨_, fundCocircuit_isCocircuit heB hB, mem_fundCocircuit M e B⟩

@[simp]
lemma closure_inter_setOf_isNonloop_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∩ {e | M.IsNonloop e}) = M.closure X := by
  rw [setOf_isNonloop_eq, ← inter_diff_assoc, closure_diff_loops_eq, closure_inter_ground]

end IsNonloop

section Loopless

/-- A Matroid is loopless if it has no loop -/
class Loopless (M : Matroid α) : Prop where
  closure_empty : M.closure ∅ = ∅

lemma loopless_iff_closure_empty : M.Loopless ↔ M.closure ∅ = ∅ :=
  ⟨fun h ↦ h.closure_empty, fun h ↦ ⟨h⟩⟩

@[simp]
lemma closure_empty_eq_empty (M : Matroid α) [Loopless M] : M.closure ∅ = ∅ :=
  ‹Loopless M›.closure_empty

lemma toIsNonloop [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff, isLoop_iff_mem_closure_empty, closure_empty_eq_empty]; exact not_mem_empty _

@[simp]
lemma OnUniv.toIsNonloop [Loopless M] [OnUniv M] (e : α) : M.IsNonloop e :=
  Matroid.toIsNonloop (e := e)

lemma subsingleton_indep [M.Loopless] (hI : I.Subsingleton) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  obtain rfl | ⟨x, rfl⟩ := hI.eq_empty_or_singleton
  · simp
  simpa using M.toIsNonloop

lemma not_isLoop (M : Matroid α) [Loopless M] (e : α) : ¬ M.IsLoop e :=
  fun h ↦ (toIsNonloop (e := e)).not_isLoop h

lemma loopless_iff_forall_isNonloop : M.Loopless ↔ ∀ e ∈ M.E, M.IsNonloop e :=
  ⟨fun _ _ he ↦ toIsNonloop he,
    fun h ↦ ⟨subset_empty_iff.1 (fun e (he : M.IsLoop e) ↦ (h e he.mem_ground).not_isLoop he)⟩⟩

lemma loopless_iff_forall_not_isLoop : M.Loopless ↔ ∀ e ∈ M.E, ¬M.IsLoop e :=
  ⟨fun _ e _ ↦ M.not_isLoop e,
    fun h ↦ loopless_iff_forall_isNonloop.2 fun e he ↦ (not_isLoop_iff he).1 (h e he)⟩

lemma loopless_iff_forall_isCircuit : M.Loopless ↔ ∀ C, M.IsCircuit C → C.Nontrivial := by
  suffices (∃ x ∈ M.E, M.IsLoop x) ↔ ∃ x, M.IsCircuit x ∧ x.Subsingleton by
    simpa [loopless_iff_forall_not_isLoop, ← not_iff_not (a := ∀ _, _)]
  refine ⟨fun ⟨e, _, he⟩ ↦ ⟨{e}, he.isCircuit, by simp⟩, fun ⟨C, hC, hCs⟩ ↦ ?_⟩
  obtain (rfl | ⟨e, rfl⟩) := hCs.eq_empty_or_singleton
  · simpa using hC.nonempty
  exact ⟨e, (singleton_isCircuit.1 hC).mem_ground, singleton_isCircuit.1 hC⟩

@[simp] lemma one_lt_girth_iff : 1 < M.girth ↔ M.Loopless := by
  simp_rw [loopless_iff_forall_isCircuit, ← Nat.cast_one (R := ℕ∞), lt_girth_iff',
    Finset.one_lt_card_iff_nontrivial]
  refine ⟨fun h C hC ↦ ?_, fun h C hC ↦ by simpa using h C hC⟩
  obtain hfin | hinf := C.finite_or_infinite
  · have := h hfin.toFinset (by simpa)

    simpa using h hfin.toFinset (by simpa)
  exact hinf.nontrivial

@[simp] lemma two_le_girth_iff : 2 ≤ M.girth ↔ M.Loopless := by
  rw [show (2 : ℕ∞) = 1 + 1 from rfl, ENat.add_one_le_iff (by simp), one_lt_girth_iff]

lemma Loopless.ground_eq (M : Matroid α) [Loopless M] : M.E = {e | M.IsNonloop e} :=
  Set.ext fun _ ↦  ⟨fun he ↦ toIsNonloop he, IsNonloop.mem_ground⟩

lemma IsRestriction.loopless [M.Loopless] (hR : N ≤r M) : N.Loopless := by
  obtain ⟨R, hR, rfl⟩ := hR
  rw [loopless_iff_closure_empty, restrict_closure_eq _ (empty_subset _), M.closure_empty_eq_empty,
    empty_inter]

instance {M : Matroid α} [Matroid.Nonempty M] [Loopless M] : RankPos M :=
  M.ground_nonempty.elim fun _ he ↦ (toIsNonloop he).rankPos

@[simp] lemma loopyOn_isLoopless_iff {E : Set α} : Loopless (loopyOn E) ↔ E = ∅ := by
  simp [loopless_iff_forall_not_isLoop, eq_empty_iff_forall_not_mem]

/-- The matroid obtained by removing the loops of `e` -/
def removeLoops (M : Matroid α) : Matroid α := M ↾ {e | M.IsNonloop e}

lemma removeLoops_eq_restr (M : Matroid α) : M.removeLoops = M ↾ {e | M.IsNonloop e} := rfl

lemma removeLoops_ground_eq (M : Matroid α) : M.removeLoops.E = {e | M.IsNonloop e} := rfl

instance removeLoops_isLoopless (M : Matroid α) : Loopless M.removeLoops := by
  simp [loopless_iff_forall_isNonloop, removeLoops]

@[simp] lemma removeLoops_eq_self (M : Matroid α) [Loopless M] : M.removeLoops = M := by
  rw [removeLoops, ← Loopless.ground_eq, restrict_ground_eq_self]

lemma removeLoops_eq_self_iff : M.removeLoops = M ↔ M.Loopless := by
  refine ⟨fun h ↦ ?_, fun h ↦ M.removeLoops_eq_self⟩
  rw [← h]
  infer_instance

lemma removeLoops_isRestriction (M : Matroid α) : M.removeLoops ≤r M :=
  restrict_isRestriction _ _ (fun _ h ↦ IsNonloop.mem_ground h)

lemma eq_restrict_removeLoops (M : Matroid α) : M = M.removeLoops ↾ M.E := by
  rw [removeLoops, ext_iff_indep]
  simp only [restrict_ground_eq, restrict_indep_iff, true_and]
  exact fun I hIE ↦ ⟨fun hI ↦ ⟨⟨hI,fun e heI ↦ hI.isNonloop_of_mem heI⟩, hIE⟩, fun hI ↦ hI.1.1⟩

@[simp]
lemma removeLoops_indep_eq : M.removeLoops.Indep = M.Indep := by
  ext I
  rw [removeLoops_eq_restr, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun h e ↦ h.isNonloop_of_mem

@[simp]
lemma removeLoops_isBasis'_eq : M.removeLoops.IsBasis' = M.IsBasis' := by
  ext
  simp [IsBasis']

@[simp] lemma removeLoops_isBase_eq : M.removeLoops.IsBase = M.IsBase := by
  ext B
  rw [isBase_iff_maximal_indep, removeLoops_indep_eq, isBase_iff_maximal_indep]

@[simp]
lemma removeLoops_isNonloop_iff : M.removeLoops.IsNonloop e ↔ M.IsNonloop e := by
  rw [removeLoops_eq_restr, restrict_isNonloop_iff, mem_setOf, and_self]

lemma IsNonloop.removeLoops_isNonloop (he : M.IsNonloop e) : M.removeLoops.IsNonloop e :=
  removeLoops_isNonloop_iff.2 he

@[simp] lemma removeLoops_idem (M : Matroid α) : M.removeLoops.removeLoops = M.removeLoops := by
  simp [removeLoops_eq_restr]

lemma removeLoops_restr_eq_restr (hX : X ⊆ {e | M.IsNonloop e}) : M.removeLoops ↾ X = M ↾ X := by
  rwa [removeLoops_eq_restr, restrict_restrict_eq]

@[simp]
lemma restrict_univ_removeLoops_eq : (M ↾ univ).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_restr, restrict_restrict_eq _ (subset_univ _), removeLoops_eq_restr]
  simp

end Loopless
section Coloop

/-- A coloop is a loop of the dual  -/
abbrev Coloop (M : Matroid α) (e : α) : Prop :=
  M✶.IsLoop e

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Coloop.mem_ground (he : M.Coloop e) : e ∈ M.E :=
  @IsLoop.mem_ground α (M✶) e he

lemma coisLoop_iff_mem_closure_empty : M.Coloop e ↔ e ∈ M✶.closure ∅ := Iff.rfl

lemma coloops_eq_dual_closure_empty : {e | M.Coloop e} = M✶.closure ∅ := rfl

lemma Coloop.dual_isLoop (he : M.Coloop e) : M✶.IsLoop e :=
  he

lemma Coloop.isCocircuit (he : M.Coloop e) : M.Cocircuit {e} :=
  IsLoop.isCircuit he

@[simp] lemma singleton_isCocircuit : M.Cocircuit {e} ↔ M.Coloop e :=
  singleton_isCircuit

lemma IsLoop.dual_coloop (he : M.IsLoop e) : M✶.Coloop e :=
  by rwa [Coloop, dual_dual]

@[simp] lemma dual_coisLoop_iff_isLoop : M✶.Coloop e ↔ M.IsLoop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_isLoop, IsLoop.dual_coloop⟩

@[simp] lemma dual_isLoop_iff_coloop : M✶.IsLoop e ↔ M.Coloop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_coloop, Coloop.dual_isLoop⟩

lemma coisLoop_iff_forall_mem_isBase : M.Coloop e ↔ ∀ ⦃B⦄, M.IsBase B → e ∈ B := by
  simp_rw [← dual_isLoop_iff_coloop, isLoop_iff_forall_mem_compl_isBase, dual_isBase_iff',
    dual_ground, mem_diff]
  refine ⟨fun h B hB ↦ ?_, fun h B ⟨hB, _⟩ ↦ ⟨hB.subset_ground (h hB), (h hB).2⟩⟩
  rw [← diff_diff_cancel_left hB.subset_ground]
  exact h (M.E \ B) ⟨(by rwa [diff_diff_cancel_left hB.subset_ground]), diff_subset⟩

lemma IsBase.mem_of_coloop (hB : M.IsBase B) (he : M.Coloop e) : e ∈ B :=
  coisLoop_iff_forall_mem_isBase.mp he hB

lemma Coloop.mem_of_isBase (he : M.Coloop e) (hB : M.IsBase B) : e ∈ B :=
  coisLoop_iff_forall_mem_isBase.mp he hB

lemma IsBase.coloops_subset (hB : M.IsBase B) : M✶.closure ∅ ⊆ B :=
  fun _ he ↦ Coloop.mem_of_isBase he hB

lemma Coloop.isNonloop (h : M.Coloop e) : M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  hB.indep.isNonloop_of_mem ((coisLoop_iff_forall_mem_isBase.mp h) hB)

lemma IsLoop.not_coloop (h : M.IsLoop e) : ¬M.Coloop e := by
  rw [← dual_isLoop_iff_coloop]; rw [← dual_dual M, dual_isLoop_iff_coloop] at h
  exact h.isNonloop.not_isLoop

lemma Coloop.not_mem_isCircuit (he : M.Coloop e) (hC : M.IsCircuit C) : e ∉ C :=
  fun h ↦ (hC.isCocircuit.isNonloop_of_mem h).not_isLoop he

lemma coisLoop_iff_forall_mem_compl_isCircuit [RankPos M✶] :
    M.Coloop e ↔ ∀ C, M.IsCircuit C → e ∈ M.E \ C := by
  refine ⟨fun h C hC ↦ ⟨h.mem_ground, h.not_mem_isCircuit hC⟩, fun h ↦ ?_⟩
  rw [coisLoop_iff_forall_mem_isBase]
  refine fun B hB ↦ by_contra fun heB ↦ ?_
  have heE : e ∈ M.E := Exists.elim M.exists_isCircuit (fun C hC ↦ (h C hC).1)
  rw [← hB.closure_eq] at heE
  exact (h _ (hB.indep.fundCircuit_isCircuit heE heB)).2 (mem_fundCircuit _ _ _)

lemma IsCircuit.not_coisLoop_of_mem (hC : M.IsCircuit C) (heC : e ∈ C) : ¬M.Coloop e :=
  fun h ↦ h.not_mem_isCircuit hC heC

lemma coisLoop_iff_forall_mem_closure_iff_mem :
    M.Coloop e ↔ (∀ X, e ∈ M.closure X ↔ e ∈ X) ∧ e ∈ M.E := by
  rw [coisLoop_iff_forall_mem_isBase]
  refine ⟨fun h ↦ ?_, fun h B hB ↦ ?_⟩
  · have heE := M.exists_isBase.elim (fun _ hB ↦ hB.subset_ground (h hB))
    refine ⟨fun X ↦ ⟨fun heX ↦ ?_, fun heX ↦ M.mem_closure_of_mem' heX⟩, heE⟩
    obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ M.E)
    obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
    rw [← closure_inter_ground, ← hI.closure_eq_closure] at heX
    exact (hI.subset ((hB.indep.closure_inter_eq_self_of_subset hIB).subset ⟨heX, h hB⟩)).1
  rw [← h.1, hB.closure_eq]
  exact h.2

lemma coisLoop_iff_forall_mem_closure_iff_mem' :
    M.Coloop e ↔ (∀ X, X ⊆ M.E → (e ∈ M.closure X ↔ e ∈ X)) ∧ e ∈ M.E := by
  rw [coisLoop_iff_forall_mem_closure_iff_mem, and_congr_left_iff]
  refine fun he ↦ ⟨fun h X _ ↦ h X, fun h X ↦ ?_⟩
  rw [← closure_inter_ground, h (X ∩ M.E) inter_subset_right, mem_inter_iff, and_iff_left he]

lemma Coloop.mem_closure_iff_mem (he : M.Coloop e) : e ∈ M.closure X ↔ e ∈ X :=
  (coisLoop_iff_forall_mem_closure_iff_mem.1 he).1 X

lemma Coloop.mem_of_mem_closure (he : M.Coloop e) (hX : e ∈ M.closure X) : e ∈ X := by
  rwa [← he.mem_closure_iff_mem]

lemma coisLoop_iff_diff_nonspanning : M.Coloop e ↔ ¬ M.Spanning (M.E \ {e}) := by
  rw [coisLoop_iff_forall_mem_closure_iff_mem']
  refine ⟨fun h hsp ↦ ?_, fun h ↦ ⟨fun X hX ↦ ⟨fun he ↦ ?_, fun he ↦ ?_⟩, by_contra fun h' ↦ h ?_⟩⟩
  · simpa [hsp.closure_eq.symm ▸ h.2] using h.1 (M.E \ {e})
  · rw [spanning_iff_ground_subset_closure] at h
    refine by_contra fun he' ↦ h ?_
    rw [← union_eq_self_of_subset_left (subset_diff_singleton hX he'),
      ← closure_union_closure_left_eq, ← insert_eq_of_mem he, ← union_singleton, union_assoc,
      union_diff_self, singleton_union, ← closure_ground]
    apply M.closure_subset_closure
    rw [closure_ground]
    exact (subset_insert _ _).trans subset_union_right
  · exact M.subset_closure X hX he
  rw [spanning_iff_closure_eq, diff_singleton_eq_self h', closure_ground]

lemma coisLoop_iff_diff_closure : M.Coloop e ↔ M.closure (M.E \ {e}) ≠ M.E := by
  rw [coisLoop_iff_diff_nonspanning, spanning_iff_closure_eq]

lemma coisLoop_iff_not_mem_closure_compl (he : e ∈ M.E := by aesop_mat) :
    M.Coloop e ↔ e ∉ M.closure (M.E \ {e}) := by
  rw [coisLoop_iff_diff_closure, not_iff_not]
  refine ⟨fun h ↦ by rwa [h], fun h ↦ (M.closure_subset_ground _).antisymm fun x hx ↦ ?_⟩
  obtain (rfl | hne) := eq_or_ne x e; assumption
  exact M.subset_closure (M.E \ {e}) diff_subset (show x ∈ M.E \ {e} from ⟨hx, hne⟩)

lemma IsBase.mem_coisLoop_iff_forall_not_mem_fundCircuit (hB : M.IsBase B) (he : e ∈ B) :
    M.Coloop e ↔ ∀ x ∈ M.E \ B, e ∉ M.fundCircuit x B := by
  refine ⟨fun h x hx heC ↦ (h.not_mem_isCircuit <| hB.fundCircuit_isCircuit hx.1 hx.2) heC,
    fun h ↦ ?_⟩
  have h' : M.E \ {e} ⊆ M.closure (B \ {e}) := by
    rintro x ⟨hxE, hne : x ≠ e⟩
    obtain (hx | hx) := em (x ∈ B)
    · exact M.subset_closure (B \ {e}) (diff_subset.trans hB.subset_ground) ⟨hx, hne⟩
    have h_cct := (hB.fundCircuit_isCircuit hxE hx).mem_closure_diff_singleton_of_mem
      (M.mem_fundCircuit x B)
    refine (M.closure_subset_closure (subset_diff_singleton ?_ ?_)) h_cct
    · simpa using fundCircuit_subset_insert ..
    simp [hne.symm, h x ⟨hxE, hx⟩]
  rw [coisLoop_iff_not_mem_closure_compl (hB.subset_ground he)]
  exact not_mem_subset (M.closure_subset_closure_of_subset_closure h') <|
    hB.indep.not_mem_closure_diff_of_mem he

lemma exists_mem_isCircuit_of_not_coloop (heE : e ∈ M.E) (he : ¬ M.Coloop e) :
    ∃ C, M.IsCircuit C ∧ e ∈ C := by
  simp only [coisLoop_iff_forall_mem_isBase, not_forall, Classical.not_imp, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCircuit e B, hB.fundCircuit_isCircuit heE heB, .inl rfl⟩

@[simp] lemma closure_inter_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure X ∩ M✶.closure ∅ = X ∩ M✶.closure ∅ := by
  simp_rw [Set.ext_iff, mem_inter_iff, ← coisLoop_iff_mem_closure_empty, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]

lemma closure_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M✶.closure ∅) :
     M.closure X ∩ K = X ∩ K := by
  have hKE : K ∩ M.E = K := by
    rw [inter_eq_left, ← dual_ground]; exact hK.trans (closure_subset_ground _ _)
  rw [← hKE, ← inter_assoc X, inter_right_comm, hKE, ← closure_inter_ground,
    subset_antisymm_iff, and_iff_left (inter_subset_inter_left K (M.subset_closure _)),
    ← inter_eq_self_of_subset_right hK, ← inter_assoc, closure_inter_coloops_eq,
    inter_assoc]

lemma closure_insert_coisLoop_eq (X : Set α) (he : M.Coloop e) :
    M.closure (insert e X) = insert e (M.closure X) := by
  rw [ subset_antisymm_iff, insert_subset_iff,
    and_iff_left (M.closure_subset_closure (subset_insert _ _)),
    and_iff_left (M.mem_closure_of_mem' (mem_insert _ _)), ← union_singleton (s := M.closure X),
    ← diff_subset_iff, subset_singleton_iff]
  refine fun f hf ↦ (he.mem_of_mem_closure (closure_exchange hf).1).elim
    Eq.symm (fun heX ↦ False.elim ?_)
  simp [insert_eq_of_mem heX] at hf

lemma closure_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M✶.closure ∅) :
    M.closure (X ∪ K) = M.closure X ∪ K := by
  rw [← closure_union_closure_left_eq]
  refine (M.subset_closure _).antisymm' fun e he ↦ ?_
  obtain he' | ⟨C, hCss, hC, heC⟩ := (mem_closure_iff_mem_or_exists_isCircuit
    (union_subset (M.closure_subset_ground _) (hK.trans (M✶.closure_subset_ground _)))).1 he
  · exact he'
  have hCX : C \ {e} ⊆ M.closure X := by
    rw [diff_subset_iff, singleton_union]
    refine (subset_inter hCss Subset.rfl).trans ?_
    rintro f ⟨rfl | h1 | h2, h⟩
    · apply mem_insert
    · exact Or.inr h1
    exact (hC.not_coisLoop_of_mem h (hK h2)).elim
  left
  exact M.closure_subset_closure_of_subset_closure hCX <| hC.mem_closure_diff_singleton_of_mem heC

lemma closure_eq_of_subset_coloops (hK : K ⊆ M✶.closure ∅) : M.closure K = K ∪ M.closure ∅ := by
  rw [← empty_union K, closure_union_eq_of_subset_coloops _ hK, empty_union, union_comm]

lemma closure_diff_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M✶.closure ∅) :
    M.closure (X \ K) = M.closure X \ K := by
  nth_rw 2 [← inter_union_diff X K]
  rw [union_comm, closure_union_eq_of_subset_coloops _ (inter_subset_right.trans hK),
    union_diff_distrib, diff_eq_empty.mpr inter_subset_right, union_empty, eq_comm,
    sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  have he : M.Coloop e := hK heK
  rw [he.mem_closure_iff_mem] at heX
  exact heX.2 heK

lemma closure_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M✶.closure ∅) :
    Disjoint (M.closure X) K := by
  rwa [disjoint_iff_inter_eq_empty, closure_inter_eq_of_subset_coloops X hK,
    ← disjoint_iff_inter_eq_empty]

lemma closure_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M✶.closure ∅)) :
    Disjoint (M.closure X) (M✶.closure ∅) :=
  closure_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

lemma closure_union_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M✶.closure ∅) = M.closure X ∪ M✶.closure ∅ :=
  closure_union_eq_of_subset_coloops _ Subset.rfl

lemma Coloop.not_mem_closure_of_not_mem (he : M.Coloop e) (hX : e ∉ X) : e ∉ M.closure X :=
  mt he.mem_closure_iff_mem.mp hX

lemma Coloop.insert_indep_of_indep (he : M.Coloop e) (hI : M.Indep I) : M.Indep (insert e I) := by
  refine (em (e ∈ I)).elim (fun h ↦ by rwa [insert_eq_of_mem h]) fun h ↦ ?_
  rw [← hI.not_mem_closure_iff_of_not_mem h]
  exact he.not_mem_closure_of_not_mem h

lemma union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M✶.closure ∅) :
    M.Indep (I ∪ K) ↔ M.Indep I := by
  refine ⟨fun h ↦ h.subset subset_union_left, fun h ↦ ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he ↦ Coloop.mem_of_isBase he hB))

lemma diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M✶.closure ∅) :
    M.Indep (I \ K) ↔ M.Indep I := by
  rw [← union_indep_iff_indep_of_subset_coloops hK, diff_union_self,
    union_indep_iff_indep_of_subset_coloops hK]

lemma indep_iff_union_coloops_indep : M.Indep I ↔ M.Indep (I ∪ M✶.closure ∅) :=
  (union_indep_iff_indep_of_subset_coloops Subset.rfl).symm

lemma indep_iff_diff_coloops_indep : M.Indep I ↔ M.Indep (I \ M✶.closure ∅) :=
  (diff_indep_iff_indep_of_subset_coloops Subset.rfl).symm

lemma coloops_indep (M : Matroid α) : M.Indep (M✶.closure ∅) := by
  rw [indep_iff_diff_coloops_indep, diff_self]; exact M.empty_indep

lemma indep_of_subset_coloops (h : I ⊆ M✶.closure ∅) : M.Indep I :=
  M.coloops_indep.subset h

/-- If two matroids agree on loops and coloops, and have the same independent sets after
  loops/coloops are removed, they are equal. -/
lemma ext_indep_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hl : M₁.closure ∅ = M₂.closure ∅) (hc : M₁✶.closure ∅ = M₂✶.closure ∅)
    (h : ∀ I, I ⊆ M₁.E → Disjoint I (M₁.closure ∅ ∪ M₁✶.closure ∅) → (M₁.Indep I ↔ M₂.Indep I)) :
    M₁ = M₂ := by
  refine ext_indep hE fun I hI ↦ ?_
  rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.closure ∅))
  · rw [h _ (diff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left diff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.IsLoop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩) ?_
  rw [isLoop_iff_mem_closure_empty, hl, ← isLoop_iff_mem_closure_empty] at hel ; rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩

@[simp]
lemma removeLoops_coisLoop_eq (M : Matroid α) : M.removeLoops.Coloop = M.Coloop := by
  ext e
  rw [coisLoop_iff_forall_mem_isBase, removeLoops_isBase_eq, ← coisLoop_iff_forall_mem_isBase]

@[simp]
lemma removeLoops_coloops_eq (M : Matroid α) : M.removeLoops✶.closure ∅ = M✶.closure ∅ := by
  ext e
  rw [← coisLoop_iff_mem_closure_empty, removeLoops_coisLoop_eq, coisLoop_iff_mem_closure_empty]

/-- This turns a restriction into a restriction to a subset. -/
lemma restrict_removeLoops (R : Set α) : (M ↾ R).removeLoops = (M ↾ (R ∩ M.E)).removeLoops := by
  rw [removeLoops_eq_restr, restrict_restrict_eq _ (by simp [subset_def]),
    removeLoops_eq_restr, restrict_restrict_eq _ (by simp [subset_def])]
  convert rfl using 2
  ext e
  simp +contextual [IsNonloop.mem_ground]

end Coloop

section Constructions

lemma eq_uniqueBaseOn_of_loops_union_coloops (hE : M.E = M.closure ∅ ∪ M✶.closure ∅) :
    M = uniqueBaseOn (M✶.closure ∅) M.E := by
  refine ext_isBase rfl (fun B hBE ↦ ?_)
  rw [uniqueBaseOn_isBase_iff (show M✶.closure ∅ ⊆ M.E from M✶.closure_subset_ground _)]
  rw [hE, ← diff_subset_iff] at hBE
  use fun h ↦ h.coloops_subset.antisymm' (by rwa [sdiff_eq_left.mpr h.indep.disjoint_loops] at hBE)
  rintro rfl
  obtain ⟨B, hB⟩ := M.exists_isBase
  rwa [hB.coloops_subset.antisymm ]
  refine subset_trans ?_ (diff_subset_iff.2 hE.subset)
  rw [subset_diff, and_iff_right hB.subset_ground]
  exact hB.indep.disjoint_loops

lemma uniqueBaseOn_loops_eq (I E : Set α) : (uniqueBaseOn I E).closure ∅ = E \ I := by
  simp

@[simp] lemma uniqueBaseOn_coloops_eq' (I E : Set α) : (uniqueBaseOn I E)✶.closure ∅ = I ∩ E := by
  simp [inter_comm I]

lemma uniqueBaseOn_coloops_eq {I E : Set α} (h : I ⊆ E) : (uniqueBaseOn I E)✶.closure ∅ = I := by
  simp [h]

end Constructions

end Matroid
