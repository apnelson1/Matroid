import Matroid.Circuit
import Mathlib.Data.Matroid.Loop
import Matroid.ForMathlib.Finset
import Matroid.OnUniv

/-
  A `Loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.loops`.
  Thus, the set of loops of `M` is equal to `M.loops`, and we prefer this notation instead of
  `{e | M.IsLoop e}` or similar. A `Nonloop` is an element of the ground set that is not a loop.
-/


variable {α β : Type*} {M N : Matroid α} {e f : α} {B L L' I X Y Z F C K : Set α}

open Set
open scoped symmDiff

namespace Matroid

section IsLoopEquiv

/-- Two sets are `IsLoopEquiv` in `M` if their symmetric difference contains only loops. -/
def IsLoopEquiv (M : Matroid α) (X Y : Set α) := X ∪ M.loops = Y ∪ M.loops

lemma isLoopEquiv_iff_union_eq_union :
    M.IsLoopEquiv X Y ↔ X ∪ M.loops = Y ∪ M.loops := Iff.rfl

lemma IsLoopEquiv.union_eq_union (h : M.IsLoopEquiv X Y) : X ∪ M.loops = Y ∪ M.loops := h

lemma IsLoopEquiv.diff_eq_diff (h : M.IsLoopEquiv X Y) : X \ M.loops = Y \ M.loops := by
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

lemma IsLoopEquiv.diff_subset_loops (h : M.IsLoopEquiv X Y) : X \ Y ⊆ M.loops := by
  rw [diff_subset_iff, ← h.union_eq_union]
  exact subset_union_left

lemma IsLoopEquiv.symmDiff_subset_loops : M.IsLoopEquiv X Y ↔ X ∆ Y ⊆ M.loops := by
  rw [Set.symmDiff_def, union_subset_iff]
  refine ⟨fun h ↦ ⟨h.diff_subset_loops, h.symm.diff_subset_loops⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  rw [diff_subset_iff] at h1 h2
  rw [isLoopEquiv_iff_union_eq_union, subset_antisymm_iff, union_subset_iff, union_subset_iff]
  exact ⟨⟨h1, subset_union_right⟩, h2, subset_union_right⟩

lemma isLoopEquiv_union (X : Set α) (hL : L ⊆ M.loops) : M.IsLoopEquiv X (X ∪ L) := by
   rw [isLoopEquiv_iff_union_eq_union, union_assoc, union_eq_self_of_subset_left hL]

lemma isLoopEquiv_diff (X : Set α) (hL : L ⊆ M.loops) : M.IsLoopEquiv X (X \ L) := by
  rw [IsLoopEquiv.comm]
  refine (isLoopEquiv_union (X \ L) hL).trans ?_
  rw [diff_union_self, IsLoopEquiv.comm]
  exact isLoopEquiv_union X hL

lemma isLoopEquiv_union_diff (X : Set α) (hL : L ⊆ M.loops) (hL' : L' ⊆ M.loops) :
    M.IsLoopEquiv X ((X ∪ L) \ L') :=
  (isLoopEquiv_union X hL).trans (isLoopEquiv_diff _ hL')

lemma isLoopEquiv_union_loops (M : Matroid α) (X : Set α) : M.IsLoopEquiv X (X ∪ M.loops) :=
  isLoopEquiv_union X Subset.rfl

lemma isLoopEquiv_diff_loops (M : Matroid α) (X : Set α) : M.IsLoopEquiv X (X \ M.loops) :=
  isLoopEquiv_diff X Subset.rfl

lemma IsLoopEquiv.exists_diff_union_loops (h : M.IsLoopEquiv X Y) :
    ∃ L L', L ⊆ M.loops ∧ L' ⊆ M.loops ∧ Y = (X ∪ L) \ L' :=
  ⟨_, _, h.symm.diff_subset_loops, h.diff_subset_loops, by aesop⟩

lemma IsLoopEquiv.subset_union_loops (h : M.IsLoopEquiv X Y) : Y ⊆ X ∪ M.loops := by
  rw [h.union_eq_union]; exact subset_union_left

lemma IsLoopEquiv.closure_eq_closure (h : M.IsLoopEquiv X Y) : M.closure X = M.closure Y := by
  rw [← closure_union_loops_eq, h.union_eq_union, closure_union_loops_eq]

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma IsLoopEquiv.subset_ground (h : M.IsLoopEquiv X Y) (hX : X ⊆ M.E := by aesop_mat) : Y ⊆ M.E :=
  h.subset_union_loops.trans (union_subset hX (M.closure_subset_ground ∅))

lemma IsLoopEquiv.inter_eq_of_indep (h : M.IsLoopEquiv X Y) (hI : M.Indep I) : X ∩ I = Y ∩ I := by
  rw [show X ∩ I = (X ∪ M.loops) ∩ I
    by rw [union_inter_distrib_right, hI.disjoint_loops.symm.inter_eq, union_empty],
    h.union_eq_union, union_inter_distrib_right, hI.disjoint_loops.symm.inter_eq, union_empty]

lemma IsLoopEquiv.subset_iff_of_indep (h : M.IsLoopEquiv X Y) (hI : M.Indep I) : I ⊆ X ↔ I ⊆ Y := by
  rw [← sdiff_eq_left.2 hI.disjoint_loops, diff_subset_iff, diff_subset_iff,
    union_comm, h.union_eq_union, union_comm]

lemma IsLoopEquiv.isBasis_iff (h : M.IsLoopEquiv X Y) : M.IsBasis I X ↔ M.IsBasis I Y := by
  rw [isBasis_iff_indep_subset_closure, isBasis_iff_indep_subset_closure, and_congr_right_iff]
  intro hI
  rw [h.subset_iff_of_indep hI, and_congr_right_iff,
    show M.closure I = M.closure I ∪ M.loops by simp [loops],
    union_comm, ← diff_subset_iff,  h.diff_eq_diff, diff_subset_iff]
  exact fun _ ↦ Iff.rfl

lemma isBasis_union_iff_isBasis_of_subset_loops (hL : L ⊆ M.loops) :
    M.IsBasis I (X ∪ L) ↔ M.IsBasis I X :=
  (isLoopEquiv_union X hL).symm.isBasis_iff

lemma isBasis_diff_iff_isBasis_of_subset_loops (hL : L ⊆ M.loops) :
    M.IsBasis I (X \ L) ↔ M.IsBasis I X :=
  (isLoopEquiv_diff X hL).symm.isBasis_iff

lemma closure_union_eq_closure_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.loops) :
    M.closure (X ∪ Y) = M.closure X :=
  (isLoopEquiv_union X hY).symm.closure_eq_closure

lemma closure_diff_eq_closure_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.loops) :
    M.closure (X \ Y) = M.closure X :=
  (isLoopEquiv_diff X hY).symm.closure_eq_closure

end IsLoopEquiv


section Loopless

/-- A Matroid is loopless if it has no loop -/
class Loopless (M : Matroid α) : Prop where
  loops : M.loops = ∅

lemma loopless_iff_loops : M.Loopless ↔ M.loops = ∅ :=
  ⟨fun h ↦ h.loops, fun h ↦ ⟨h⟩⟩

@[simp]
lemma loops_eq_empty (M : Matroid α) [Loopless M] : M.loops = ∅ :=
  ‹Loopless M›.loops

lemma toIsNonloop [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff, isLoop_iff, loops_eq_empty]; exact not_mem_empty _

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
  rw [loopless_iff_loops, restrict_loops_eq hR, M.loops_eq_empty, empty_inter]

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

lemma removeLoops_loops_eq : M.removeLoops.loops = ∅ :=
  Loopless.loops

end Loopless

section IsColoop

/-- A coloop is a loop of the dual  -/
def IsColoop (M : Matroid α) (e : α) : Prop :=
  M✶.IsLoop e

def coloops (M : Matroid α) := M✶.loops

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsColoop.mem_ground (he : M.IsColoop e) : e ∈ M.E :=
  @IsLoop.mem_ground α (M✶) e he

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma coloops_subset_ground (M : Matroid α) : M.coloops ⊆ M.E :=
  fun _ ↦ IsColoop.mem_ground

lemma isColoop_iff_mem_loops : M.IsColoop e ↔ e ∈ M.coloops := Iff.rfl

@[simp]
lemma dual_loops : M✶.loops = M.coloops := rfl

@[simp]
lemma dual_coloops : M✶.coloops = M.loops := by
  rw [coloops, dual_dual]

lemma IsColoop.dual_isLoop (he : M.IsColoop e) : M✶.IsLoop e :=
  he

lemma IsColoop.isCocircuit (he : M.IsColoop e) : M.IsCocircuit {e} :=
  IsLoop.isCircuit he

@[simp] lemma singleton_isCocircuit : M.IsCocircuit {e} ↔ M.IsColoop e :=
  singleton_isCircuit

lemma IsLoop.dual_isColoop (he : M.IsLoop e) : M✶.IsColoop e :=
  by rwa [IsColoop, dual_dual]

@[simp] lemma dual_isColoop_iff_isLoop : M✶.IsColoop e ↔ M.IsLoop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_isLoop, IsLoop.dual_isColoop⟩

@[simp] lemma dual_isLoop_iff_isColoop : M✶.IsLoop e ↔ M.IsColoop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_isColoop, IsColoop.dual_isLoop⟩

lemma isColoop_iff_forall_mem_isBase : M.IsColoop e ↔ ∀ ⦃B⦄, M.IsBase B → e ∈ B := by
  simp_rw [← dual_isLoop_iff_isColoop, isLoop_iff_forall_mem_compl_isBase, dual_isBase_iff',
    dual_ground, mem_diff]
  refine ⟨fun h B hB ↦ ?_, fun h B ⟨hB, _⟩ ↦ ⟨hB.subset_ground (h hB), (h hB).2⟩⟩
  rw [← diff_diff_cancel_left hB.subset_ground]
  exact h (M.E \ B) ⟨(by rwa [diff_diff_cancel_left hB.subset_ground]), diff_subset⟩

lemma IsBase.mem_of_isColoop (hB : M.IsBase B) (he : M.IsColoop e) : e ∈ B :=
  isColoop_iff_forall_mem_isBase.mp he hB

lemma IsColoop.mem_of_isBase (he : M.IsColoop e) (hB : M.IsBase B) : e ∈ B :=
  isColoop_iff_forall_mem_isBase.mp he hB

lemma IsBase.coloops_subset (hB : M.IsBase B) : M.coloops ⊆ B :=
  fun _ he ↦ IsColoop.mem_of_isBase he hB

lemma IsColoop.isNonloop (h : M.IsColoop e) : M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  hB.indep.isNonloop_of_mem ((isColoop_iff_forall_mem_isBase.mp h) hB)

lemma IsLoop.not_isColoop (h : M.IsLoop e) : ¬M.IsColoop e := by
  rw [← dual_isLoop_iff_isColoop]; rw [← dual_dual M, dual_isLoop_iff_isColoop] at h
  exact h.isNonloop.not_isLoop

lemma IsColoop.not_mem_isCircuit (he : M.IsColoop e) (hC : M.IsCircuit C) : e ∉ C :=
  fun h ↦ (hC.isCocircuit.isNonloop_of_mem h).not_isLoop he

lemma isColoop_iff_forall_mem_compl_isCircuit [RankPos M✶] :
    M.IsColoop e ↔ ∀ C, M.IsCircuit C → e ∈ M.E \ C := by
  refine ⟨fun h C hC ↦ ⟨h.mem_ground, h.not_mem_isCircuit hC⟩, fun h ↦ ?_⟩
  rw [isColoop_iff_forall_mem_isBase]
  refine fun B hB ↦ by_contra fun heB ↦ ?_
  have heE : e ∈ M.E := Exists.elim M.exists_isCircuit (fun C hC ↦ (h C hC).1)
  rw [← hB.closure_eq] at heE
  exact (h _ (hB.indep.fundCircuit_isCircuit heE heB)).2 (mem_fundCircuit _ _ _)

lemma IsCircuit.not_isColoop_of_mem (hC : M.IsCircuit C) (heC : e ∈ C) : ¬ M.IsColoop e :=
  fun h ↦ h.not_mem_isCircuit hC heC

lemma IsColoop.mem_of_mem_closure (h : M.IsColoop e) (heX : e ∈ M.closure X) : e ∈ X := by
  by_contra heX'
  obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heX').1 heX
  exact hC.not_isColoop_of_mem heC h

lemma IsColoop.mem_closure_iff_mem (he : M.IsColoop e) : e ∈ M.closure X ↔ e ∈ X :=
  ⟨he.mem_of_mem_closure, M.mem_closure_of_mem'⟩

lemma isColoop_iff_forall_mem_closure_iff_mem :
    M.IsColoop e ↔ (∀ X, e ∈ M.closure X ↔ e ∈ X) ∧ e ∈ M.E :=
  ⟨fun h ↦ ⟨fun _ ↦ h.mem_closure_iff_mem, h.mem_ground⟩,
    fun ⟨h, he⟩ ↦ isColoop_iff_forall_mem_isBase.2 fun B hB ↦ (h B).1 <| by rwa [hB.closure_eq]⟩

lemma isColoop_iff_forall_mem_closure_iff_mem' :
    M.IsColoop e ↔ (∀ X, X ⊆ M.E → (e ∈ M.closure X ↔ e ∈ X)) ∧ e ∈ M.E := by
  rw [isColoop_iff_forall_mem_closure_iff_mem, and_congr_left_iff]
  refine fun he ↦ ⟨fun h X _ ↦ h X, fun h X ↦ ?_⟩
  rw [← closure_inter_ground, h (X ∩ M.E) inter_subset_right, mem_inter_iff, and_iff_left he]

lemma IsColoop.diff_not_spanning (he : M.IsColoop e) : ¬ M.Spanning (M.E \ {e}) := by
  obtain ⟨B, hB⟩ := M.exists_isBasis (M.E \ {e})
  exact fun h ↦ (hB.subset <| (hB.isBase_of_spanning h).mem_of_isColoop he).2 rfl

lemma isColoop_iff_diff_not_spanning : M.IsColoop e ↔ ¬ M.Spanning (M.E \ {e}) := by
  refine ⟨IsColoop.diff_not_spanning, fun h ↦ by_contra fun h' ↦ h ?_⟩
  obtain ⟨B, hB : M.IsBase B, heB : e ∉ B⟩ := by simpa [isColoop_iff_forall_mem_isBase] using h'
  exact hB.spanning.superset <| subset_diff_singleton hB.subset_ground heB

lemma isColoop_iff_diff_closure : M.IsColoop e ↔ M.closure (M.E \ {e}) ≠ M.E := by
  rw [isColoop_iff_diff_not_spanning, spanning_iff_closure_eq]

lemma isColoop_iff_not_mem_closure_compl (he : e ∈ M.E := by aesop_mat) :
    M.IsColoop e ↔ e ∉ M.closure (M.E \ {e}) := by
  rw [isColoop_iff_diff_closure, not_iff_not]
  refine ⟨fun h ↦ by rwa [h], fun h ↦ (M.closure_subset_ground _).antisymm fun x hx ↦ ?_⟩
  obtain (rfl | hne) := eq_or_ne x e; assumption
  exact M.subset_closure (M.E \ {e}) diff_subset (show x ∈ M.E \ {e} from ⟨hx, hne⟩)

lemma IsBase.mem_isColoop_iff_forall_not_mem_fundCircuit (hB : M.IsBase B) (he : e ∈ B) :
    M.IsColoop e ↔ ∀ x ∈ M.E \ B, e ∉ M.fundCircuit x B := by
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
  rw [isColoop_iff_not_mem_closure_compl (hB.subset_ground he)]
  exact not_mem_subset (M.closure_subset_closure_of_subset_closure h') <|
    hB.indep.not_mem_closure_diff_of_mem he

lemma IsBasis'.inter_coloops_subset (hIX : M.IsBasis' I X) : X ∩ M.coloops ⊆ I := by
  intro e ⟨heX, (heI : M.IsColoop e)⟩
  rwa [← heI.mem_closure_iff_mem, hIX.isBasis_closure_right.closure_eq_right,
    heI.mem_closure_iff_mem]

lemma IsBasis.inter_coloops_subset (hIX : M.IsBasis I X) : X ∩ M.coloops ⊆ I :=
  hIX.isBasis'.inter_coloops_subset

-- lemma isColoop_tfae {e : α} : List.TFAE [
--     M.IsColoop e,
--     e ∈ M.coloops,
--     M.IsCocircuit {e},
--     ∀ ⦃B⦄, M.IsBase B → e ∈ B,
--     (∀ ⦃C⦄, M.IsCircuit C → e ∉ C) ∧ e ∈ M.E,
--     ∀ X, M.closure (insert e X) = insert e (M.closure X)] := by
--   tfae_have 1 <-> 2 := Iff.rfl
--   tfae_have 1 <-> 3 := by
--     rw [← dual_isLoop_iff_isColoop, ← singleton_isCircuit]
--   tfae_have 1 <-> 4 := by
--     simp_rw [← dual_isLoop_iff_isColoop, isLoop_iff_forall_mem_compl_isBase]
--     refine ⟨fun h B hB ↦ ?_, fun h B hB ↦ h hB.compl_isBase_of_dual⟩
--     obtain ⟨-, heB : e ∈ B⟩ := by simpa using h (M.E \ B) hB.compl_isBase_dual
--     assumption
--   tfae_have 3 -> 5 := fun h ↦
--     ⟨fun C hC heC ↦ hC.inter_isCocircuit_ne_singleton h (e := e) (by simpa), h.subset_ground rfl⟩
--   tfae_have 5 -> 4 := by
--     refine fun ⟨h, heE⟩ B hB ↦ by_contra fun heB ↦ ?_
--     rw [← hB.closure_eq] at heE
--     obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heB).1 heE
--     exact h hC heC
--   tfae_have 5 -> 6 := fun h X ↦ by
--     rw [← closure_insert_closure_eq_closure_insert]
--     refine (M.subset_closure _ (insert_subset h.2 (M.closure_subset_ground _))).antisymm' ?_
--     rw [← diff_eq_empty, eq_empty_iff_forall_not_mem]
--     refine fun f ⟨hf, hf'⟩ ↦ hf' <| .inr ?_
--     obtain ⟨C, hCss, hC, hfC⟩ := (mem_closure_iff_exists_isCircuit hf').1 hf
--     rw [insert_comm, subset_insert_iff_of_not_mem (h.1 hC)] at hCss
--     exact (M.closure_subset_closure_of_subset_closure (by simpa)) <|
--       hC.mem_closure_diff_singleton_of_mem hfC
--   tfae_have 6 -> 4 := fun h B hB ↦ by_contra fun heB ↦ by
--     sorry
--   tfae_finish

-- lemma closure_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
--     M.closure (X ∪ K) = M.closure X ∪ K := by
--   obtain rfl | hne := K.eq_empty_or_nonempty; simp
--   rw [← biUnion_of_singleton K, eq_comm, union_distrib_biUnion _ hne]
--   have : ∀ i ∈ K, M.closure (X ∪ {i}) = (M.closure X) ∪ {i} := sorry
--   rw [← iUnion₂_congr this, ← union_distrib_biUnion _ hne, biUni]
  -- have : ⋃ x ∈ K, {x} = K := by exact biUnion_of_singleton K


lemma exists_mem_isCircuit_of_not_isColoop (heE : e ∈ M.E) (he : ¬ M.IsColoop e) :
    ∃ C, M.IsCircuit C ∧ e ∈ C := by
  simp only [isColoop_iff_forall_mem_isBase, not_forall, Classical.not_imp, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCircuit e B, hB.fundCircuit_isCircuit heE heB, .inl rfl⟩

@[simp] lemma closure_inter_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure X ∩ M.coloops = X ∩ M.coloops := by
  simp_rw [Set.ext_iff, mem_inter_iff, ← isColoop_iff_mem_loops, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]

lemma closure_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
     M.closure X ∩ K = X ∩ K := by
  nth_rw 1 [← inter_eq_self_of_subset_right hK]
  rw [← inter_assoc, closure_inter_coloops_eq, inter_assoc, inter_eq_self_of_subset_right hK]

lemma closure_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
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
    exact (hC.not_isColoop_of_mem h (hK h2)).elim
  left
  exact M.closure_subset_closure_of_subset_closure hCX <| hC.mem_closure_diff_singleton_of_mem heC

lemma closure_insert_isColoop_eq (X : Set α) (he : M.IsColoop e) :
    M.closure (insert e X) = insert e (M.closure X) := by
  rw [← union_singleton, closure_union_eq_of_subset_coloops _ (by simpa), union_singleton]

lemma closure_eq_of_subset_coloops (hK : K ⊆ M.coloops) : M.closure K = K ∪ M.loops := by
  rw [← empty_union K, closure_union_eq_of_subset_coloops _ hK, empty_union, union_comm,
    closure_empty]

lemma closure_diff_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
    M.closure (X \ K) = M.closure X \ K := by
  nth_rw 2 [← inter_union_diff X K]
  rw [union_comm, closure_union_eq_of_subset_coloops _ (inter_subset_right.trans hK),
    union_diff_distrib, diff_eq_empty.mpr inter_subset_right, union_empty, eq_comm,
    sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  rw [IsColoop.mem_closure_iff_mem (hK heK)] at heX
  exact heX.2 heK

lemma closure_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M.coloops) :
    Disjoint (M.closure X) K := by
  rwa [disjoint_iff_inter_eq_empty, closure_inter_eq_of_subset_coloops X hK,
    ← disjoint_iff_inter_eq_empty]

lemma closure_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M.coloops)) :
    Disjoint (M.closure X) M.coloops :=
  closure_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

lemma closure_union_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M.coloops) = M.closure X ∪ M.coloops :=
  closure_union_eq_of_subset_coloops _ Subset.rfl

lemma IsColoop.not_mem_closure_of_not_mem (he : M.IsColoop e) (hX : e ∉ X) : e ∉ M.closure X :=
  mt he.mem_closure_iff_mem.mp hX

lemma IsColoop.insert_indep_of_indep (he : M.IsColoop e) (hI : M.Indep I) :
    M.Indep (insert e I) := by
  refine (em (e ∈ I)).elim (fun h ↦ by rwa [insert_eq_of_mem h]) fun h ↦ ?_
  rw [← hI.not_mem_closure_iff_of_not_mem h]
  exact he.not_mem_closure_of_not_mem h

lemma union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M.coloops) :
    M.Indep (I ∪ K) ↔ M.Indep I := by
  refine ⟨fun h ↦ h.subset subset_union_left, fun h ↦ ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he ↦ IsColoop.mem_of_isBase he hB))

lemma diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M.coloops) :
    M.Indep (I \ K) ↔ M.Indep I := by
  rw [← union_indep_iff_indep_of_subset_coloops hK, diff_union_self,
    union_indep_iff_indep_of_subset_coloops hK]

lemma indep_iff_union_coloops_indep : M.Indep I ↔ M.Indep (I ∪ M.coloops) :=
  (union_indep_iff_indep_of_subset_coloops Subset.rfl).symm

lemma indep_iff_diff_coloops_indep : M.Indep I ↔ M.Indep (I \ M.coloops) :=
  (diff_indep_iff_indep_of_subset_coloops Subset.rfl).symm

lemma coloops_indep (M : Matroid α) : M.Indep (M.coloops) := by
  rw [indep_iff_diff_coloops_indep, diff_self]; exact M.empty_indep

lemma indep_of_subset_coloops (h : I ⊆ M.coloops) : M.Indep I :=
  M.coloops_indep.subset h

/-- If two matroids agree on loops and coloops, and have the same independent sets after
  loops/coloops are removed, they are equal. -/
lemma ext_indep_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hl : M₁.loops = M₂.loops) (hc : M₁.coloops = M₂.coloops)
    (h : ∀ I, I ⊆ M₁.E → Disjoint I (M₁.loops ∪ M₁.coloops) → (M₁.Indep I ↔ M₂.Indep I)) :
    M₁ = M₂ := by
  refine ext_indep hE fun I hI ↦ ?_
  rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.loops))
  · rw [h _ (diff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left diff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.IsLoop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩) ?_
  rw [isLoop_iff, hl, ← isLoop_iff] at hel
  rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩

@[simp]
lemma removeLoops_isColoop_eq (M : Matroid α) : M.removeLoops.IsColoop = M.IsColoop := by
  ext e
  rw [isColoop_iff_forall_mem_isBase, removeLoops_isBase_eq, ← isColoop_iff_forall_mem_isBase]

@[simp]
lemma removeLoops_coloops_eq (M : Matroid α) : M.removeLoops.coloops = M.coloops := by
  ext e
  rw [← isColoop_iff_mem_loops, removeLoops_isColoop_eq, isColoop_iff_mem_loops]

lemma restrict_removeLoops (R : Set α) : (M ↾ R).removeLoops = (M ↾ (R ∩ M.E)).removeLoops := by
  rw [removeLoops_eq_restr, restrict_restrict_eq _ (by simp [subset_def]),
    removeLoops_eq_restr, restrict_restrict_eq _ (by simp [subset_def])]
  convert rfl using 2
  ext e
  simp +contextual [IsNonloop.mem_ground]

end IsColoop

section Constructions

lemma eq_uniqueBaseOn_of_loops_union_coloops (hE : M.E = M.loops ∪ M.coloops) :
    M = uniqueBaseOn (M.coloops) M.E := by
  refine ext_isBase rfl (fun B hBE ↦ ?_)
  rw [uniqueBaseOn_isBase_iff (show M.coloops ⊆ M.E from M✶.closure_subset_ground _)]
  rw [hE, ← diff_subset_iff] at hBE
  use fun h ↦ h.coloops_subset.antisymm' (by rwa [sdiff_eq_left.mpr h.indep.disjoint_loops] at hBE)
  rintro rfl
  obtain ⟨B, hB⟩ := M.exists_isBase
  rwa [hB.coloops_subset.antisymm ]
  refine subset_trans ?_ (diff_subset_iff.2 hE.subset)
  rw [subset_diff, and_iff_right hB.subset_ground]
  exact hB.indep.disjoint_loops

lemma uniqueBaseOn_loops_eq (I E : Set α) : (uniqueBaseOn I E).loops = E \ I := by
  simp [loops]

@[simp] lemma uniqueBaseOn_coloops_eq' (I E : Set α) : (uniqueBaseOn I E).coloops = I ∩ E := by
  simp [coloops, loops, inter_comm I]

lemma uniqueBaseOn_coloops_eq {I E : Set α} (h : I ⊆ E) : (uniqueBaseOn I E).coloops = I := by
  simp [h]

end Constructions

end Matroid
