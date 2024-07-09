import Matroid.Circuit
import Mathlib.Data.Matroid.Map
import Mathlib.Order.SymmDiff
import Matroid.ForMathlib.Set

/-
  A `Loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.closure ∅`.
  Thus, the set of loops of `M` is equal to `M.closure ∅`, and we prefer this notation instead of
  `{e | M.Loop e}` or similar. A `Nonloop` is an element of the ground set that is not a loop.
-/


variable {α β : Type*} {M N : Matroid α} {e f : α} {B L L' I X Y Z F C K : Set α}

open Set
open scoped symmDiff

namespace Matroid

section Loop
/-- A loop is a member of the closure of the empty set -/
def Loop (M : Matroid α) (e : α) : Prop :=
  e ∈ M.closure ∅

lemma loop_iff_mem_closure_empty : M.Loop e ↔ e ∈ M.closure ∅ := Iff.rfl

lemma closure_empty_eq_loops (M : Matroid α) : M.closure ∅ = {e | M.Loop e} := rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Loop.mem_ground (he : M.Loop e) : e ∈ M.E :=
  closure_subset_ground M ∅ (by simp) he

@[simp] lemma singleton_dep : M.Dep {e} ↔ M.Loop e := by
  rw [loop_iff_mem_closure_empty, M.empty_indep.mem_closure_iff_of_not_mem (not_mem_empty e),
    insert_emptyc_eq]

@[simp] lemma singleton_not_indep (he : e ∈ M.E := by aesop_mat) : ¬M.Indep {e} ↔ M.Loop e :=
  by rw [← singleton_dep, ← not_indep_iff]

lemma Loop.dep (he : M.Loop e) : M.Dep {e} :=
  singleton_dep.mpr he

lemma singleton_circuit : M.Circuit {e} ↔ M.Loop e := by
  simp_rw [← singleton_dep, circuit_def, mem_minimals_setOf_iff, and_iff_left_iff_imp,
    subset_singleton_iff_eq]
  rintro _ _ hY (rfl | rfl)
  · simpa using hY.nonempty
  rfl

lemma loop_iff_not_mem_base_forall (he : e ∈ M.E := by aesop_mat) :
    M.Loop e ↔ ∀ B, M.Base B → e ∉ B := by
  rw [← singleton_dep, ← not_indep_iff, not_iff_comm, not_forall]
  simp_rw [_root_.not_imp, not_not, ← singleton_subset_iff, indep_iff]

lemma Loop.circuit (he : M.Loop e) : M.Circuit {e} :=
  singleton_circuit.mpr he

lemma Loop.mem_closure (he : M.Loop e) (X : Set α) : e ∈ M.closure X :=
  M.closure_mono (empty_subset _) he

lemma Loop.mem_flat (he : M.Loop e) {F : Set α} (hF : M.Flat F) : e ∈ F := by
  have := he.mem_closure F; rwa [hF.closure] at this

lemma Flat.loops_subset (hF : M.Flat F) : M.closure ∅ ⊆ F := fun _ he ↦ Loop.mem_flat he hF

lemma Loop.dep_of_mem (he : M.Loop e) (h : e ∈ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  he.dep.superset (singleton_subset_iff.mpr h) hXE

lemma Loop.not_indep_of_mem (he : M.Loop e) (h : e ∈ X) : ¬M.Indep X := fun hX ↦
  he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

lemma Loop.not_mem_of_indep (he : M.Loop e) (hI : M.Indep I) : e ∉ I := fun h ↦
  he.not_indep_of_mem h hI

lemma Loop.eq_of_circuit_mem (he : M.Loop e) (hC : M.Circuit C) (h : e ∈ C) : C = {e} := by
  rw [he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)]

@[simp] lemma coexpand_loop_iff (M : Matroid α) : M.coexpand.Loop e ↔ M.Loop e := by
  simp [← singleton_circuit]

lemma Indep.disjoint_loops (hI : M.Indep I) : Disjoint I (M.closure ∅) :=
  by_contra fun h ↦
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    Loop.not_mem_of_indep he hI heI

lemma Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I ⊆ M.closure ∅) : I = ∅ :=
  eq_empty_iff_forall_not_mem.mpr fun _ he ↦ Loop.not_mem_of_indep (h he) hI he

@[simp] lemma basis_loops_iff : M.Basis I (M.closure ∅) ↔ I = ∅ := by
  refine ⟨fun h ↦ h.indep.eq_empty_of_subset_loops h.subset, ?_⟩
  rintro rfl
  exact M.empty_indep.basis_closure

lemma closure_eq_loops_of_subset (h : X ⊆ M.closure ∅) : M.closure X = M.closure ∅ :=
  (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))

lemma basis_iff_empty_of_subset_loops (hX : X ⊆ M.closure ∅) : M.Basis I X ↔ I = ∅ := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simpa⟩
  replace h := (closure_eq_loops_of_subset hX) ▸ h.basis_closure_right
  simpa using h

lemma Loop.closure (he : M.Loop e) : M.closure {e} = M.closure ∅ :=
  closure_eq_loops_of_subset (singleton_subset_iff.mpr he)

lemma loop_iff_closure_eq_closure_empty' : M.Loop e ↔ M.closure {e} = M.closure ∅ ∧ e ∈ M.E := by
  rw [← singleton_dep, dep_iff, singleton_subset_iff, and_congr_left_iff]
  intro he
  rw [not_indep_iff, singleton_dep]
  exact ⟨fun h ↦ by rw [h.closure], fun h ↦ by rw [loop_iff_mem_closure_empty, ← h]; exact M.mem_closure_self e⟩

lemma loop_iff_closure_eq_closure_empty (he : e ∈ M.E := by aesop_mat) :
    M.Loop e ↔ M.closure {e} = M.closure ∅ := by rw [loop_iff_closure_eq_closure_empty', and_iff_left he]

lemma loop_iff_forall_mem_compl_base : M.Loop e ↔ ∀ B, M.Base B → e ∈ M.E \ B := by
  refine' ⟨fun h B hB ↦ mem_of_mem_of_subset h _, fun h ↦ _⟩
  · rw [subset_diff, and_iff_right (closure_subset_ground _ _), disjoint_iff_inter_eq_empty,
      hB.indep.closure_inter_eq_self_of_subset (empty_subset B)]
  have he : e ∈ M.E := M.exists_base.elim (fun B hB ↦ (h B hB).1)
  rw [← singleton_dep, ← not_indep_iff]
  intro hei
  obtain ⟨B, hB, heB⟩ := hei.exists_base_superset
  exact (h B hB).2 (singleton_subset_iff.mp heB)

@[simp] lemma restrict_loop_iff {R : Set α} :
    (M ↾ R).Loop e ↔ e ∈ R ∧ (M.Loop e ∨ e ∉ M.E) := by
  rw [← singleton_dep, restrict_dep_iff, singleton_subset_iff, ← singleton_dep, and_comm,
    and_congr_right_iff, Dep, and_or_right, singleton_subset_iff, and_iff_left or_not,
    or_iff_left_of_imp (fun he hi ↦ he (singleton_subset_iff.1 hi.subset_ground))]
  simp only [singleton_subset_iff, implies_true]

lemma restriction_loop_iff (hNM : N ≤r M) :
    N.Loop e ↔ e ∈ N.E ∧ M.Loop e := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_loop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE ↦ (heE (hR heR)).elim

lemma Loop.of_restriction (he : N.Loop e) (hNM : N ≤r M) : M.Loop e :=
  ((restriction_loop_iff hNM).1 he).2

lemma Loop.loop_restriction (he : M.Loop e) (hNM : N ≤r M) (heN : e ∈ N.E) : N.Loop e :=
  (restriction_loop_iff hNM).2 ⟨heN, he⟩

@[simp] lemma comap_loop_iff {M : Matroid β} {f : α → β} : (M.comap f).Loop e ↔ M.Loop (f e) := by
  rw [← singleton_dep, comap_dep_iff]
  simp

@[simp] lemma loopyOn_loop_iff {E : Set α} : (loopyOn E).Loop e ↔ e ∈ E := by
  simp [Loop]

end Loop

section LoopEquiv

lemma closure_union_loops_eq (M : Matroid α) (X : Set α) : M.closure (X ∪ M.closure ∅) = M.closure X := by
  rw [closure_union_closure_right_eq, union_empty]

@[simp] lemma closure_diff_loops_eq (M : Matroid α) (X : Set α) : M.closure (X \ M.closure ∅) = M.closure X := by
  rw [← M.closure_union_loops_eq (X \ M.closure ∅), diff_union_self, closure_union_closure_right_eq, union_empty]

/-- Two sets are `LoopEquiv` in `M` if their symmetric difference contains only loops. -/
def LoopEquiv (M : Matroid α) (X Y : Set α) := X ∪ M.closure ∅ = Y ∪ M.closure ∅

lemma loopEquiv_iff_union_eq_union : M.LoopEquiv X Y ↔ X ∪ M.closure ∅ = Y ∪ M.closure ∅ := Iff.rfl

lemma LoopEquiv.union_eq_union (h : M.LoopEquiv X Y) : X ∪ M.closure ∅ = Y ∪ M.closure ∅ := h

lemma LoopEquiv.diff_eq_diff (h : M.LoopEquiv X Y) : X \ M.closure ∅ = Y \ M.closure ∅ := by
  rw [subset_antisymm_iff, diff_subset_iff, union_diff_self, union_comm, ← h.union_eq_union,
    diff_subset_iff, union_diff_self, union_comm _ X, and_iff_right subset_union_left,
    h.union_eq_union]
  apply subset_union_left

lemma LoopEquiv.rfl (M : Matroid α) {X : Set α} : M.LoopEquiv X X := by
  rfl

lemma LoopEquiv.symm (h : M.LoopEquiv X Y) : M.LoopEquiv Y X :=
  Eq.symm h

lemma LoopEquiv.comm : M.LoopEquiv X Y ↔ M.LoopEquiv Y X :=
  ⟨LoopEquiv.symm, LoopEquiv.symm⟩

lemma LoopEquiv.trans (hXY : M.LoopEquiv X Y) (hYZ : M.LoopEquiv Y Z) : M.LoopEquiv X Z :=
  Eq.trans hXY hYZ

lemma LoopEquiv.diff_subset_loops (h : M.LoopEquiv X Y) : X \ Y ⊆ M.closure ∅ := by
  rw [diff_subset_iff, ← h.union_eq_union]
  exact subset_union_left

lemma LoopEquiv.symmDiff_subset_loops : M.LoopEquiv X Y ↔ X ∆ Y ⊆ M.closure ∅ := by
  rw [Set.symmDiff_def, union_subset_iff]
  refine ⟨fun h ↦ ⟨h.diff_subset_loops, h.symm.diff_subset_loops⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  rw [diff_subset_iff] at h1 h2
  rw [loopEquiv_iff_union_eq_union, subset_antisymm_iff, union_subset_iff, union_subset_iff]
  exact ⟨⟨h1, subset_union_right⟩, h2, subset_union_right⟩

lemma loopEquiv_union (X : Set α) (hL : L ⊆ M.closure ∅) : M.LoopEquiv X (X ∪ L) := by
   rw [loopEquiv_iff_union_eq_union, union_assoc, union_eq_self_of_subset_left hL]

lemma loopEquiv_diff (X : Set α) (hL : L ⊆ M.closure ∅) : M.LoopEquiv X (X \ L) := by
  rw [LoopEquiv.comm]
  refine (loopEquiv_union (X \ L) hL).trans ?_
  rw [diff_union_self, LoopEquiv.comm]
  exact loopEquiv_union X hL

lemma loopEquiv_union_diff (X : Set α) (hL : L ⊆ M.closure ∅) (hL' : L' ⊆ M.closure ∅) :
    M.LoopEquiv X ((X ∪ L) \ L') :=
  (loopEquiv_union X hL).trans (loopEquiv_diff _ hL')

lemma loopEquiv_union_loops (M : Matroid α) (X : Set α) : M.LoopEquiv X (X ∪ M.closure ∅) :=
  loopEquiv_union X Subset.rfl

lemma loopEquiv_diff_loops (M : Matroid α) (X : Set α) : M.LoopEquiv X (X \ M.closure ∅) :=
  loopEquiv_diff X Subset.rfl

lemma LoopEquiv.exists_diff_union_loops (h : M.LoopEquiv X Y) :
    ∃ L L', L ⊆ M.closure ∅ ∧ L' ⊆ M.closure ∅ ∧ Y = (X ∪ L) \ L' :=
  ⟨_, _, h.symm.diff_subset_loops, h.diff_subset_loops, by aesop⟩

lemma LoopEquiv.subset_union_loops (h : M.LoopEquiv X Y) : Y ⊆ X ∪ M.closure ∅ := by
  rw [h.union_eq_union]; exact subset_union_left

lemma LoopEquiv.closure_eq_closure (h : M.LoopEquiv X Y) : M.closure X = M.closure Y := by
  rw [← closure_union_loops_eq, h.union_eq_union, closure_union_loops_eq]

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma LoopEquiv.subset_ground (h : M.LoopEquiv X Y) (hX : X ⊆ M.E := by aesop_mat) : Y ⊆ M.E :=
  h.subset_union_loops.trans (union_subset hX (M.closure_subset_ground ∅))

lemma LoopEquiv.inter_eq_of_indep (h : M.LoopEquiv X Y) (hI : M.Indep I) : X ∩ I = Y ∩ I := by
  rw [show X ∩ I = (X ∪ M.closure ∅) ∩ I
    by rw [union_inter_distrib_right, hI.disjoint_loops.symm.inter_eq, union_empty],
    h.union_eq_union, union_inter_distrib_right, hI.disjoint_loops.symm.inter_eq, union_empty]

lemma LoopEquiv.subset_iff_of_indep (h : M.LoopEquiv X Y) (hI : M.Indep I) : I ⊆ X ↔ I ⊆ Y := by
  rw [← sdiff_eq_left.2 hI.disjoint_loops, diff_subset_iff, diff_subset_iff,
    union_comm, h.union_eq_union, union_comm]

lemma LoopEquiv.basis_iff (h : M.LoopEquiv X Y) : M.Basis I X ↔ M.Basis I Y := by
  rw [basis_iff_indep_subset_closure, basis_iff_indep_subset_closure, and_congr_right_iff]
  intro hI
  rw [h.subset_iff_of_indep hI, and_congr_right_iff, show M.closure I = M.closure I ∪ M.closure ∅ by simp,
    union_comm, ← diff_subset_iff,  h.diff_eq_diff, diff_subset_iff]
  exact fun _ ↦ Iff.rfl

lemma basis_union_iff_basis_of_subset_loops (hL : L ⊆ M.closure ∅) :
    M.Basis I (X ∪ L) ↔ M.Basis I X :=
  (loopEquiv_union X hL).symm.basis_iff

lemma basis_diff_iff_basis_of_subset_loops (hL : L ⊆ M.closure ∅) :
    M.Basis I (X \ L) ↔ M.Basis I X :=
  (loopEquiv_diff X hL).symm.basis_iff

lemma closure_union_eq_closure_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.closure ∅) :
    M.closure (X ∪ Y) = M.closure X :=
  (loopEquiv_union X hY).symm.closure_eq_closure

lemma closure_diff_eq_closure_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.closure ∅) :
    M.closure (X \ Y) = M.closure X :=
  (loopEquiv_diff X hY).symm.closure_eq_closure

end LoopEquiv

section Nonloop

/-- A `nonloop` is an element that is not a loop -/
def Nonloop (M : Matroid α) (e : α) : Prop :=
  ¬M.Loop e ∧ e ∈ M.E

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Nonloop.mem_ground (h : M.Nonloop e) : e ∈ M.E :=
  h.2

lemma Nonloop.not_loop (he : M.Nonloop e) : ¬M.Loop e :=
  he.1

lemma Loop.not_nonloop (he : M.Loop e) : ¬M.Nonloop e :=
  fun h ↦ h.not_loop he

lemma nonloop_of_not_loop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.Loop e) : M.Nonloop e :=
  ⟨h,he⟩

lemma loop_of_not_nonloop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.Nonloop e) : M.Loop e :=
  by rwa [Nonloop, and_iff_left he, not_not] at h

@[simp] lemma not_loop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.Loop e ↔ M.Nonloop e :=
  (and_iff_left he).symm

@[simp] lemma not_nonloop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.Nonloop e ↔ M.Loop e := by
  rw [← not_loop_iff, not_not]

lemma nonloop_iff_mem_compl_loops : M.Nonloop e ↔ e ∈ M.E \ M.closure ∅ := by
  rw [Nonloop, Loop, and_comm, mem_diff]

lemma setOf_nonloop_eq (M : Matroid α) : {e | M.Nonloop e} = M.E \ M.closure ∅ :=
  Set.ext (fun _ ↦ nonloop_iff_mem_compl_loops)

lemma not_nonloop_iff_closure : ¬ M.Nonloop e ↔ M.closure {e} = M.closure ∅ := by
  by_cases he : e ∈ M.E
  · simp [Nonloop, and_comm, not_and, not_not, loop_iff_closure_eq_closure_empty', he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he,
    (show ¬ M.Nonloop e from fun h ↦ he h.mem_ground)]

lemma loop_or_nonloop (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) :
    M.Loop e ∨ M.Nonloop e := by
  rw [Nonloop, and_iff_left he]; apply em

@[simp] lemma indep_singleton : M.Indep {e} ↔ M.Nonloop e := by
  rw [Nonloop, ← singleton_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, singleton_subset_iff.mp h.subset_ground⟩, fun h ↦ h.1 h.2⟩

alias ⟨Indep.nonloop, Nonloop.indep⟩ := indep_singleton

lemma Indep.nonloop_of_mem (hI : M.Indep I) (h : e ∈ I) : M.Nonloop e := by
  rw [← not_loop_iff (hI.subset_ground h)]; exact fun he ↦ (he.not_mem_of_indep hI) h

lemma Nonloop.exists_mem_base (he : M.Nonloop e) : ∃ B, M.Base B ∧ e ∈ B := by
  simpa using (indep_singleton.2 he).exists_base_superset

lemma Cocircuit.nonloop_of_mem (hK : M.Cocircuit K) (he : e ∈ K) : M.Nonloop e := by
  rw [← not_loop_iff (hK.subset_ground he), ← singleton_circuit]
  intro he'
  obtain ⟨f, ⟨rfl, -⟩, hfe⟩ := (he'.cocircuit_inter_nontrivial hK ⟨e, by simp [he]⟩).exists_ne e
  exact hfe rfl

lemma Circuit.nonloop_of_mem (hC : M.Circuit C) (hC' : C.Nontrivial) (he : e ∈ C) : M.Nonloop e :=
  nonloop_of_not_loop (hC.subset_ground he) (fun hL ↦ by simp [hL.eq_of_circuit_mem hC he] at hC')

lemma Circuit.nonloop_of_mem_of_one_lt_card (hC : M.Circuit C) (h : 1 < C.encard) (he : e ∈ C) :
    M.Nonloop e := by
  refine nonloop_of_not_loop (hC.subset_ground he) (fun hlp ↦ ?_)
  rw [hlp.eq_of_circuit_mem hC he, encard_singleton] at h
  exact h.ne rfl

lemma nonloop_of_not_mem_closure (h : e ∉ M.closure X) (he : e ∈ M.E := by aesop_mat) : M.Nonloop e :=
  nonloop_of_not_loop he (fun hel ↦ h (hel.mem_closure X))

lemma nonloop_iff_not_mem_closure_empty (he : e ∈ M.E := by aesop_mat) :
    M.Nonloop e ↔ e ∉ M.closure ∅ := by rw [Nonloop, loop_iff_mem_closure_empty, and_iff_left he]

lemma Nonloop.mem_closure_singleton (he : M.Nonloop e) (hef : e ∈ M.closure {f}) : f ∈ M.closure {e} := by
  rw [← union_empty {_}, singleton_union] at *
  exact (M.closure_exchange (X := ∅) ⟨hef, (nonloop_iff_not_mem_closure_empty he.mem_ground).1 he⟩).1

lemma Nonloop.mem_closure_comm (he : M.Nonloop e) (hf : M.Nonloop f) : f ∈ M.closure {e} ↔ e ∈ M.closure {f} :=
  ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩

lemma Nonloop.nonloop_of_mem_closure (he : M.Nonloop e) (hef : e ∈ M.closure {f}) :
    M.Nonloop f := by
  by_cases hf : f ∈ M.E
  · rw [← not_loop_iff, Loop, ← singleton_subset_iff]
    exact fun h ↦ he.not_loop (M.closure_subset_closure_of_subset_closure h hef)
  refine False.elim <| he.not_loop ?_
  rw [← insert_emptyc_eq, closure_insert_of_not_mem_ground hf, mem_insert_iff, ← Loop] at hef
  obtain (rfl | h) := hef
  · exact False.elim <| hf he.mem_ground
  exact h

lemma Nonloop.closure_eq_of_mem_closure (he : M.Nonloop e) (hef : e ∈ M.closure {f}) : M.closure {e} = M.closure {f} := by
  rw [← closure_closure _ {f}, ← insert_eq_of_mem hef, closure_insert_closure_eq_closure_insert,
    ← closure_closure _ {e}, ← insert_eq_of_mem (he.mem_closure_singleton hef), closure_insert_closure_eq_closure_insert,
    pair_comm]

lemma Nonloop.closure_eq_closure_iff_circuit_of_ne (he : M.Nonloop e) (hef : e ≠ f) :
    M.closure {e} = M.closure {f} ↔ M.Circuit {e, f} := by
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · have hf := he.nonloop_of_mem_closure (by rw [← h]; exact M.mem_closure_self e)
    rw [circuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff,
      and_iff_right he.mem_ground, singleton_subset_iff, and_iff_left hf.mem_ground]
    refine' ⟨fun hi ↦ _, _⟩
    · apply hi.not_mem_closure_diff_of_mem (mem_insert _ _)
      rw [insert_diff_of_mem _ (by exact rfl : e ∈ {e}), diff_singleton_eq_self (by simpa), ← h]
      exact mem_closure_self _ _
    rintro x (rfl | rfl)
    · rwa [pair_diff_left hef, indep_singleton]
    rwa [pair_diff_right hef, indep_singleton]
  have hcl := (h.closure_diff_singleton_eq_closure e).trans
    (h.closure_diff_singleton_eq_closure f).symm
  rwa [pair_diff_left hef, pair_diff_right hef, eq_comm] at hcl

lemma Nonloop.closure_eq_closure_iff_eq_or_dep (he : M.Nonloop e) (hf : M.Nonloop f) :
    M.closure {e} = M.closure {f} ↔ e = f ∨ ¬M.Indep {e, f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.closure_eq_closure_iff_circuit_of_ne hne, or_iff_right hne,
    circuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff, singleton_subset_iff,
    and_iff_left hf.mem_ground, and_iff_left he.mem_ground, and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_diff_left hne, indep_singleton]
  rwa [pair_diff_right hne, indep_singleton]

lemma exists_nonloop (M : Matroid α) [RkPos M] : ∃ e, M.Nonloop e :=
  let ⟨_, hB⟩ := M.exists_base
  ⟨_, hB.indep.nonloop_of_mem hB.nonempty.some_mem⟩

lemma Nonloop.rkPos (h : M.Nonloop e) : M.RkPos :=
  h.indep.rkPos_of_nonempty (singleton_nonempty e)

@[simp] lemma restrict_nonloop_iff {R : Set α} : (M ↾ R).Nonloop e ↔ M.Nonloop e ∧ e ∈ R := by
  rw [← indep_singleton, restrict_indep_iff, singleton_subset_iff, indep_singleton]

lemma Nonloop.of_restrict {R : Set α} (h : (M ↾ R).Nonloop e) : M.Nonloop e :=
  (restrict_nonloop_iff.1 h).1

lemma Nonloop.of_restriction (h : N.Nonloop e) (hNM : N ≤r M) : M.Nonloop e := by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict

lemma nonloop_iff_restrict_of_mem {R : Set α} (he : e ∈ R) : M.Nonloop e ↔ (M ↾ R).Nonloop e :=
  ⟨fun h ↦ restrict_nonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_restrict⟩

@[simp] lemma comap_nonloop_iff {M : Matroid β} {f : α → β} :
    (M.comap f).Nonloop e ↔ M.Nonloop (f e) := by
  rw [← indep_singleton, comap_indep_iff, image_singleton, indep_singleton,
    and_iff_left (injOn_singleton _ _)]

@[simp] lemma freeOn_nonloop_iff {E : Set α} : (freeOn E).Nonloop e ↔ e ∈ E := by
  rw [← indep_singleton, freeOn_indep_iff, singleton_subset_iff]

@[simp] lemma uniqueBaseOn_nonloop_iff {I E : Set α} :
    (uniqueBaseOn I E).Nonloop e ↔ e ∈ I ∩ E := by
  rw [← indep_singleton, uniqueBaseOn_indep_iff', singleton_subset_iff]

lemma Nonloop.exists_mem_cocircuit (he : M.Nonloop e) : ∃ K, M.Cocircuit K ∧ e ∈ K := by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_base
  exact ⟨_, fundCocct_cocircuit heB hB, mem_fundCocct M e B⟩

end Nonloop

section Loopless

/-- A Matroid is loopless if it has no loop -/
class Loopless (M : Matroid α) : Prop where
  closure_empty : M.closure ∅ = ∅

lemma loopless_iff_closure_empty : M.Loopless ↔ M.closure ∅ = ∅ :=
  ⟨fun h ↦ h.closure_empty, fun h ↦ ⟨h⟩⟩

@[simp] lemma closure_empty_eq_empty (M : Matroid α) [Loopless M] : M.closure ∅ = ∅ :=
  ‹Loopless M›.closure_empty

lemma toNonloop [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.Nonloop e := by
  rw [← not_loop_iff, loop_iff_mem_closure_empty, closure_empty_eq_empty]; exact not_mem_empty _

lemma not_loop (M : Matroid α) [Loopless M] (e : α) : ¬ M.Loop e :=
  fun h ↦ (toNonloop (e := e)).not_loop h

lemma loopless_iff_forall_nonloop : M.Loopless ↔ ∀ e ∈ M.E, M.Nonloop e :=
  ⟨fun _ _ he ↦ toNonloop he,
    fun h ↦ ⟨subset_empty_iff.1 (fun e (he : M.Loop e) ↦ (h e he.mem_ground).not_loop he)⟩⟩

lemma loopless_iff_forall_not_loop : M.Loopless ↔ ∀ e ∈ M.E, ¬M.Loop e :=
  ⟨fun _ e _ ↦ M.not_loop e,
    fun h ↦ loopless_iff_forall_nonloop.2 fun e he ↦ (not_loop_iff he).1 (h e he)⟩

lemma loopless_iff_forall_circuit : M.Loopless ↔ ∀ C, M.Circuit C → C.Nontrivial := by
  suffices (∃ x ∈ M.E, M.Loop x) ↔ ∃ x, M.Circuit x ∧ x.Subsingleton by
    simpa [loopless_iff_forall_not_loop, ← not_iff_not (a := ∀ _, _)]
  refine ⟨fun ⟨e, _, he⟩ ↦ ⟨{e}, he.circuit, by simp⟩, fun ⟨C, hC, hCs⟩ ↦ ?_⟩
  obtain (rfl | ⟨e, rfl⟩) := hCs.eq_empty_or_singleton
  · simpa using hC.nonempty
  exact ⟨e, (singleton_circuit.1 hC).mem_ground, singleton_circuit.1 hC⟩

lemma Loopless.ground_eq (M : Matroid α) [Loopless M] : M.E = {e | M.Nonloop e} :=
  Set.ext fun _ ↦  ⟨fun he ↦ toNonloop he, Nonloop.mem_ground⟩

instance {M : Matroid α} [Matroid.Nonempty M] [Loopless M] : RkPos M :=
  M.ground_nonempty.elim fun _ he ↦ (toNonloop he).rkPos

@[simp] lemma loopyOn_loopless_iff {E : Set α} : Loopless (loopyOn E) ↔ E = ∅ := by
  simp [loopless_iff_forall_not_loop, eq_empty_iff_forall_not_mem]

/-- The matroid obtained by removing the loops of `e` -/
def removeLoops (M : Matroid α) : Matroid α := M ↾ {e | M.Nonloop e}

lemma removeLoops_eq_restr (M : Matroid α) : M.removeLoops = M ↾ {e | M.Nonloop e} := rfl

@[simp] lemma removeLoops_ground_eq (M : Matroid α) : M.removeLoops.E = {e | M.Nonloop e} := rfl

instance removeLoops_loopless (M : Matroid α) : Loopless M.removeLoops := by
  simp [loopless_iff_forall_nonloop, removeLoops]

@[simp] lemma removeLoops_eq_self (M : Matroid α) [Loopless M] : M.removeLoops = M := by
  rw [removeLoops, ← Loopless.ground_eq, restrict_ground_eq_self]

lemma removeLoops_eq_self_iff : M.removeLoops = M ↔ M.Loopless := by
  refine ⟨fun h ↦ ?_, fun h ↦ M.removeLoops_eq_self⟩
  rw [← h]
  infer_instance

lemma removeLoops_restriction (M : Matroid α) : M.removeLoops ≤r M :=
  restrict_restriction _ _ (fun _ h ↦ Nonloop.mem_ground h)

lemma eq_restrict_removeLoops (M : Matroid α) : M = M.removeLoops ↾ M.E := by
  rw [removeLoops, eq_iff_indep_iff_indep_forall]
  simp only [restrict_ground_eq, restrict_indep_iff, true_and]
  exact fun I hIE ↦ ⟨fun hI ↦ ⟨⟨hI,fun e heI ↦ hI.nonloop_of_mem heI⟩, hIE⟩, fun hI ↦ hI.1.1⟩

@[simp] lemma removeLoops_nonloop_iff : M.removeLoops.Nonloop e ↔ M.Nonloop e := by
  rw [removeLoops_eq_restr, restrict_nonloop_iff, mem_setOf, and_self]

lemma Nonloop.removeLoops_nonloop (he : M.Nonloop e) : M.removeLoops.Nonloop e :=
  removeLoops_nonloop_iff.2 he

@[simp] lemma removeLoops_idem (M : Matroid α) : M.removeLoops.removeLoops = M.removeLoops := by
  simp [removeLoops_eq_restr]

lemma removeLoops_restr_eq_restr (hX : X ⊆ {e | M.Nonloop e}) : M.removeLoops ↾ X = M ↾ X := by
  rwa [removeLoops_eq_restr, restrict_restrict_eq]

end Loopless
section Coloop

/-- A coloop is a loop of the dual  -/
abbrev Coloop (M : Matroid α) (e : α) : Prop :=
  M✶.Loop e

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Coloop.mem_ground (he : M.Coloop e) : e ∈ M.E :=
  @Loop.mem_ground α (M✶) e he

lemma coloop_iff_mem_closure_empty : M.Coloop e ↔ e ∈ M✶.closure ∅ := Iff.rfl

lemma coloops_eq_dual_closure_empty : {e | M.Coloop e} = M✶.closure ∅ := rfl

lemma Coloop.dual_loop (he : M.Coloop e) : M✶.Loop e :=
  he

lemma Coloop.cocircuit (he : M.Coloop e) : M.Cocircuit {e} :=
  Loop.circuit he

lemma coexpand_coloop_iff : M.coexpand.Coloop e ↔ M.Coloop e ∨ e ∉ M.E := by
  rw [coexpand, Coloop, dual_dual, restrict_loop_iff, and_iff_right (mem_univ _)]
  rfl

@[simp] lemma singleton_cocircuit : M.Cocircuit {e} ↔ M.Coloop e :=
  singleton_circuit

lemma Loop.dual_coloop (he : M.Loop e) : M✶.Coloop e :=
  by rwa [Coloop, dual_dual]

@[simp] lemma dual_coloop_iff_loop : M✶.Coloop e ↔ M.Loop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_loop, Loop.dual_coloop⟩

@[simp] lemma dual_loop_iff_coloop : M✶.Loop e ↔ M.Coloop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_coloop, Coloop.dual_loop⟩

lemma coloop_iff_forall_mem_base : M.Coloop e ↔ ∀ ⦃B⦄, M.Base B → e ∈ B := by
  simp_rw [← dual_loop_iff_coloop, loop_iff_forall_mem_compl_base, dual_base_iff',
    dual_ground, mem_diff]
  refine' ⟨fun h B hB ↦ _, fun h B ⟨hB, _⟩ ↦ ⟨hB.subset_ground (h hB), (h hB).2⟩⟩
  · rw [← diff_diff_cancel_left hB.subset_ground]
    exact h (M.E \ B) ⟨(by rwa [diff_diff_cancel_left hB.subset_ground]), diff_subset⟩

lemma Base.mem_of_coloop (hB : M.Base B) (he : M.Coloop e) : e ∈ B :=
  coloop_iff_forall_mem_base.mp he hB

lemma Coloop.mem_of_base (he : M.Coloop e) (hB : M.Base B) : e ∈ B :=
  coloop_iff_forall_mem_base.mp he hB

lemma Base.coloops_subset (hB : M.Base B) : M✶.closure ∅ ⊆ B :=
  fun _ he ↦ Coloop.mem_of_base he hB

lemma Coloop.nonloop (h : M.Coloop e) : M.Nonloop e :=
  let ⟨_, hB⟩ := M.exists_base
  hB.indep.nonloop_of_mem ((coloop_iff_forall_mem_base.mp h) hB)

lemma Loop.not_coloop (h : M.Loop e) : ¬M.Coloop e := by
  rw [← dual_loop_iff_coloop]; rw [← dual_dual M, dual_loop_iff_coloop] at h
  exact h.nonloop.not_loop

lemma Coloop.not_mem_circuit (he : M.Coloop e) (hC : M.Circuit C) : e ∉ C :=
  fun h ↦ (hC.cocircuit.nonloop_of_mem h).not_loop he

lemma coloop_iff_forall_mem_compl_circuit [RkPos M✶] :
    M.Coloop e ↔ ∀ C, M.Circuit C → e ∈ M.E \ C := by
  refine ⟨fun h C hC ↦ ⟨h.mem_ground, h.not_mem_circuit hC⟩, fun h ↦ ?_⟩
  rw [coloop_iff_forall_mem_base]
  refine fun B hB ↦ by_contra fun heB ↦ ?_
  have heE : e ∈ M.E := Exists.elim M.exists_circuit (fun C hC ↦ (h C hC).1)
  rw [← hB.closure_eq] at heE
  exact (h _ (hB.indep.fundCct_circuit ⟨heE, heB⟩)).2 (mem_fundCct _ _ _)

lemma Circuit.not_coloop_of_mem (hC : M.Circuit C) (heC : e ∈ C) : ¬M.Coloop e :=
  fun h ↦ h.not_mem_circuit hC heC

lemma Coloop.mem_closure_iff_mem (he : M.Coloop e) : e ∈ M.closure X ↔ e ∈ X := by
  rw [closure_eq_union_closure_inter_ground_self, mem_union, or_iff_right_iff_imp]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.closure_eq_closure]
  obtain ⟨B, hB, rfl⟩ := hI.exists_basis_inter_eq_of_superset inter_subset_right
  have heB := (basis_ground_iff.1 hB).mem_of_coloop he
  have h' := (hB.indep.closure_inter_eq_self_of_subset (inter_subset_left (t := X ∩ M.E))).subset
  exact fun hi ↦ (h' ⟨hi, heB⟩).2.1

lemma Coloop.mem_of_mem_closure (he : M.Coloop e) (hX : e ∈ M.closure X) : e ∈ X := by
  rwa [← he.mem_closure_iff_mem]

lemma coloop_iff_forall_mem_closure_iff_mem :
    M.Coloop e ↔ (∀ X, e ∈ M.closure X ↔ e ∈ X) ∧ e ∈ M.E :=
  ⟨fun h ↦ ⟨fun _ ↦ h.mem_closure_iff_mem, h.mem_ground⟩,
    fun ⟨h, he⟩ ↦ coloop_iff_forall_mem_base.2 fun B hB ↦ by rwa [← h, hB.closure_eq]⟩

lemma coloop_iff_forall_mem_closure_iff_mem' :
    M.Coloop e ↔ (∀ X, X ⊆ M.E → (e ∈ M.closure X ↔ e ∈ X)) ∧ e ∈ M.E :=

  ⟨fun he ↦ ⟨fun X _ ↦ he.mem_closure_iff_mem, he.mem_ground⟩,
    fun ⟨h', he⟩ ↦ coloop_iff_forall_mem_base.2 fun B hB ↦
      by rwa [← h' _ hB.subset_ground, hB.closure_eq]⟩

lemma coloop_iff_diff_nonspanning : M.Coloop e ↔ ¬ M.Spanning (M.E \ {e}) := by
  by_cases he : e ∈ M.E
  · rw [← coindep_iff_compl_spanning, Coloop, Coindep, indep_singleton, not_nonloop_iff]
  rw [diff_singleton_eq_self he]
  exact iff_of_false (fun h ↦ he h.mem_ground) <| not_not.2 <| ground_spanning M

lemma coloop_iff_diff_closure : M.Coloop e ↔ M.closure (M.E \ {e}) ≠ M.E := by
  rw [coloop_iff_diff_nonspanning, spanning_def]

lemma coloop_iff_not_mem_closure_compl (he : e ∈ M.E := by aesop_mat) :
    M.Coloop e ↔ e ∉ M.closure (M.E \ {e}) := by
  rw [coloop_iff_diff_closure, not_iff_not]
  refine ⟨fun h ↦ by rwa [h], fun h ↦ (M.closure_subset_ground _).antisymm fun x hx ↦ ?_⟩
  rwa [← closure_closure, ← insert_eq_of_mem h, closure_insert_closure_eq_closure_insert,
    insert_diff_singleton, insert_eq_of_mem he, closure_ground]

lemma Base.mem_coloop_iff_forall_not_mem_fundCct (hB : M.Base B) (he : e ∈ B) :
    M.Coloop e ↔ ∀ x ∈ M.E \ B, e ∉ M.fundCct x B := by
  refine ⟨fun h x hx heC ↦ (h.not_mem_circuit <| hB.fundCct_circuit hx) heC, fun h ↦ ?_⟩
  have h' : M.E \ {e} ⊆ M.closure (B \ {e}) := by
    rintro x ⟨hxE, hne : x ≠ e⟩
    obtain (hx | hx) := em (x ∈ B)
    · exact M.subset_closure (B \ {e}) ⟨hx, hne⟩
    have h_cct := (hB.fundCct_circuit ⟨hxE, hx⟩).mem_closure_diff_singleton_of_mem
      (M.mem_fundCct x B)
    refine (M.closure_subset_closure (subset_diff_singleton ?_ ?_)) h_cct
    · simpa using fundCct_subset_insert _ _
    simp [hne.symm, h x ⟨hxE, hx⟩]
  rw [coloop_iff_not_mem_closure_compl (hB.subset_ground he)]
  exact not_mem_subset (M.closure_subset_closure_of_subset_closure h') <| hB.indep.not_mem_closure_diff_of_mem he

lemma exists_mem_circuit_of_not_coloop (heE : e ∈ M.E) (he : ¬ M.Coloop e) :
    ∃ C, M.Circuit C ∧ e ∈ C := by
  simp only [coloop_iff_forall_mem_base, not_forall, Classical.not_imp, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCct e B, hB.fundCct_circuit ⟨heE,heB⟩, .inl rfl⟩

@[simp] lemma closure_inter_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure X ∩ M✶.closure ∅ = X ∩ M✶.closure ∅ := by
  simp_rw [Set.ext_iff, mem_inter_iff, ← coloop_iff_mem_closure_empty, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]

lemma closure_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M✶.closure ∅) : M.closure X ∩ K = X ∩ K := by
  ext e
  simp only [mem_inter_iff, and_congr_left_iff]
  exact fun heK ↦ Coloop.mem_closure_iff_mem (hK heK)

lemma closure_insert_coloop_eq (X : Set α) (he : M.Coloop e) :
    M.closure (insert e X) = insert e (M.closure X) := by
  by_cases heX : e ∈ X
  · rw [insert_eq_of_mem heX, insert_eq_of_mem (mem_closure_of_mem _ heX)]
  ext f
  by_cases hx : f ∈ M.closure X
  · exact iff_of_true (mem_of_mem_of_subset hx (M.closure_subset_closure (subset_insert _ _)))
      (.inr hx)
  rw [mem_closure_insert_comm (by simp [he.mem_closure_iff_mem, heX, hx]), he.mem_closure_iff_mem,
    mem_insert_iff, or_iff_left heX, eq_comm, mem_insert_iff, or_iff_left hx]

lemma closure_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M✶.closure ∅) :
    M.closure (X ∪ K) = M.closure X ∪ K := by
  obtain (rfl | hne) := K.eq_empty_or_nonempty
  · simp
  rw [show M.closure X ∪ K = ⋃ e ∈ K , insert e (M.closure X) from sorry,
    ← biUnion_congr rfl (show ∀ e ∈ K, M.closure (insert e X) = insert e (M.closure X) from sorry),
    ← ]
  rw [show X ∪ K = ⋃ e ∈ K, insert e X by
    simp_rw [← union_singleton, ← union_distrib_biUnion _ hne, biUnion_of_singleton],
    ← closure_biUnion_closure_eq_closure_biUnion,
    biUnion_congr rfl (show ∀ e ∈ K, M.closure (insert e X) = insert e (M.closure X) from
      fun e heK ↦ closure_insert_coloop_eq _ (hK heK))]
  simp_rw [← union_singleton, ← union_distrib_biUnion _ hne]



  -- rw [union_comm, show K = ⋃ (e ∈ K), {e} from sorry, ← biUnion_union]
  -- ext e
  -- by_cases he : e ∈ M.closure X
  -- · exact iff_of_true (M.closure_subset_closure subset_union_left he) (.inl he)


  -- rw [← closure_union_closure_left_eq]
  -- refine' (M.subset_closure _).antisymm' fun e he ↦ _
  -- obtain he' | ⟨C, hC, heC, hCss⟩ := (mem_closure_iff_mem_or_exists_circuit
  --   (union_subset (M.closure_subset_ground _) (hK.trans (M✶.closure_subset_ground _)))).1 he
  -- · exact he'
  -- have hCX : C \ {e} ⊆ M.closure X := by
  --   rw [diff_subset_iff, singleton_union]
  --   refine (subset_inter hCss Subset.rfl).trans ?_
  --   rintro f ⟨rfl | h1 | h2, h⟩
  --   · apply mem_insert
  --   · exact Or.inr h1
  --   exact (hC.not_coloop_of_mem h (hK h2)).elim
  -- exact Or.inl (M.closure_subset_closure_of_subset_closure hCX (hC.mem_closure_diff_singleton_of_mem heC))

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

lemma closure_union_coloops_eq (M : Matroid α) (X : Set α) : M.closure (X ∪ M✶.closure ∅) = M.closure X ∪ M✶.closure ∅ :=
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
  obtain ⟨B, hB, hIB⟩ := h.exists_base_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he ↦ Coloop.mem_of_base he hB))

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
lemma eq_of_indep_iff_indep_forall_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hl : M₁.closure ∅ = M₂.closure ∅) (hc : M₁✶.closure ∅ = M₂✶.closure ∅)
    (h : ∀ I, I ⊆ M₁.E → Disjoint I (M₁.closure ∅ ∪ M₁✶.closure ∅) → (M₁.Indep I ↔ M₂.Indep I)) :
    M₁ = M₂ := by
  refine' eq_of_indep_iff_indep_forall hE fun I hI ↦ _
  rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.closure ∅))
  · rw [h _ (diff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left diff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.Loop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine' iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩) _
  rw [loop_iff_mem_closure_empty, hl, ← loop_iff_mem_closure_empty] at hel ; rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩


end Coloop

section Constructions

lemma eq_uniqueBaseOn_of_loops_union_coloops (hE : M.E = M.closure ∅ ∪ M✶.closure ∅) :
    M = uniqueBaseOn (M✶.closure ∅) M.E := by
  refine eq_of_base_iff_base_forall rfl (fun B hBE ↦ ?_)
  rw [uniqueBaseOn_base_iff (show M✶.closure ∅ ⊆ M.E from M✶.closure_subset_ground _)]
  rw [hE, ← diff_subset_iff] at hBE
  use fun h ↦ h.coloops_subset.antisymm' (by rwa [sdiff_eq_left.mpr h.indep.disjoint_loops] at hBE)
  rintro rfl
  obtain ⟨B, hB⟩ := M.exists_base
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
