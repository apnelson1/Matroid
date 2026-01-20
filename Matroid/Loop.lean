import Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Loop -- inefficient import
import Matroid.ForMathlib.Finset
import Matroid.ForMathlib.Matroid.Closure
import Matroid.OnUniv

/-
  A `Loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.loops`.
  Thus, the set of loops of `M` is equal to `M.loops`, and we prefer this notation instead of
  `{e | M.IsLoop e}` or similar. A `Nonloop` is an element of the ground set that is not a loop.
-/


variable {α β : Type*} {M N : Matroid α} {e f : α} {B D L L' I X Y Z F C K : Set α}

open Set
open scoped symmDiff

namespace Matroid

lemma removeLoops_ground_eq_diff : M.removeLoops.E = M.E \ M.loops := by
  ext x
  simp only [removeLoops_ground_eq, isNonloop_iff, mem_setOf_eq, mem_diff]
  rw [and_comm]
  rfl

/-- remove the coloops of a matroid `M`. -/
def removeColoops (M : Matroid α) := M✶.removeLoops✶

lemma removeLoops_dual : M.removeLoops✶ = M✶.removeColoops := by
  rw [removeColoops, dual_dual]

lemma removeColoops_dual : M.removeColoops✶ = M✶.removeLoops := by
  rw [removeColoops, dual_dual]

@[simp]
lemma removeColoops_coloops : M.removeColoops.coloops = ∅ := by
  simp [removeColoops, dual_coloops]

lemma union_dep_iff_dep_of_subset_coloops (hX : X ⊆ M.coloops) : M.Dep (D ∪ X) ↔ M.Dep D := by
  rw [Dep, union_indep_iff_indep_of_subset_coloops hX, Dep, union_subset_iff,
    and_iff_left (hX.trans M.coloops_subset_ground)]

lemma diff_dep_iff_dep_of_subset_coloops (hX : X ⊆ M.coloops) : M.Dep (D \ X) ↔ M.Dep D := by
  rwa [← union_dep_iff_dep_of_subset_coloops hX, diff_union_self,
    union_dep_iff_dep_of_subset_coloops]

attribute [simp] union_coloops_indep_iff

@[simp]
lemma union_coloops_dep_iff : M.Dep (X ∪ M.coloops) ↔ M.Dep X :=
  union_dep_iff_dep_of_subset_coloops rfl.subset

lemma union_coindep_iff_coindep_of_subset_loops (hX : X ⊆ M.loops) :
    M.Coindep (I ∪ X) ↔ M.Coindep I :=
  M✶.union_indep_iff_indep_of_subset_coloops (K := X) (by rwa [dual_coloops])

@[simp]
lemma union_loops_coindep_iff : M.Coindep (X ∪ M.loops) ↔ M.Coindep X :=
  union_coindep_iff_coindep_of_subset_loops rfl.subset

lemma union_codep_iff_codep_of_subset_loops (hX : X ⊆ M.loops) :
    M.Codep (I ∪ X) ↔ M.Codep I :=
  M✶.union_dep_iff_dep_of_subset_coloops (X := X) (by rwa [dual_coloops])

@[simp]
lemma union_loops_codep_iff : M.Codep (X ∪ M.loops) ↔ M.Codep X :=
  union_codep_iff_codep_of_subset_loops rfl.subset

lemma eRk_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
    M.eRk (X ∪ K) = M.eRk X + (K \ X).encard := by
  obtain ⟨I, hI, hssu⟩ :=
    ((M.coloops_indep.subset hK).inter_left X).subset_isBasis'_of_subset inter_subset_left
  have := hI.subset
  rw [← eRk_union_closure_left_eq, ← hI.closure_eq_closure, eRk_union_closure_left_eq,
    Indep.eRk_eq_encard, hI.eRk_eq_encard, ← union_diff_self, encard_union_eq disjoint_sdiff_right,
      show K \ I = K \ X by tauto_set]
  rw [union_indep_iff_indep_of_subset_coloops hK]
  exact hI.indep

@[simp]
lemma loops_indep_iff : M.Indep M.loops ↔ M.Loopless := by
  rw [loopless_iff_forall_not_isLoop]
  exact ⟨fun h e heE he ↦ (h.isNonloop_of_mem he).not_isLoop he,
    fun h ↦ M.empty_indep.subset fun e (he : M.IsLoop e) ↦ (h e he.mem_ground he).elim⟩

@[simp]
lemma loops_dep_iff : M.Dep M.loops ↔ M.loops.Nonempty := by
  rw [← not_indep_iff, loops_indep_iff, loopless_iff, nonempty_iff_ne_empty]

@[simp]
lemma coloops_coindep_iff : M.Coindep M.coloops ↔ M✶.Loopless :=
  loops_indep_iff

@[simp]
lemma coloops_codep_iff : M.Codep M.coloops ↔ M.coloops.Nonempty :=
  loops_dep_iff

@[simp]
lemma closure_coloops (M : Matroid α) : M.closure M.coloops = M.coloops ∪ M.loops :=
  closure_eq_of_subset_coloops rfl.subset

@[simp]
lemma loops_subset_closure (M : Matroid α) (X : Set α) : M.loops ⊆ M.closure X :=
  M.closure_subset_closure <| empty_subset ..

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

instance freeOn_loopless (E : Set α) : Loopless (freeOn E) := by
  simp [loopless_iff_forall_not_isLoop]

@[simp]
lemma OnUniv.toIsNonloop [Loopless M] [OnUniv M] (e : α) : M.IsNonloop e :=
  Matroid.isNonloop_of_loopless (e := e)


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

@[simp]
lemma removeLoops_isNonloop_iff : M.removeLoops.IsNonloop e ↔ M.IsNonloop e := by
  rw [removeLoops_eq_restrict, restrict_isNonloop_iff, mem_setOf, and_self]

end Loopless

@[simp]
lemma loopyOn_loops (E : Set α) : (loopyOn E).loops = E := by
  simp [loops]

@[simp]
lemma loopyOn_coloops (E : Set α) : (loopyOn E).coloops = ∅ := by
  simp [coloops]

@[simp]
lemma removeLoops_isColoop_eq (M : Matroid α) : M.removeLoops.IsColoop = M.IsColoop := by
  ext e
  rw [isColoop_iff_forall_mem_isBase, removeLoops_isBase_eq, ← isColoop_iff_forall_mem_isBase]

@[simp]
lemma removeLoops_coloops_eq (M : Matroid α) : M.removeLoops.coloops = M.coloops := by
  ext e
  rw [← isColoop_iff_mem_coloops, removeLoops_isColoop_eq, isColoop_iff_mem_coloops]

@[simp]
lemma removeColoops_loops_eq (M : Matroid α) : M.removeColoops.loops = M.loops := by
  rw [← dual_coloops, removeColoops_dual, removeLoops_coloops_eq, dual_coloops]

lemma restrict_removeLoops (R : Set α) : (M ↾ R).removeLoops = (M ↾ (R ∩ M.E)).removeLoops := by
  rw [removeLoops_eq_restrict, restrict_restrict_eq _ (by simp [subset_def]),
    removeLoops_eq_restrict, restrict_restrict_eq _ (by simp [subset_def])]
  convert rfl using 2
  ext e
  simp +contextual [IsNonloop.mem_ground]


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

lemma exists_eq_uniqueBaseOn_of_loops_union_coloops (hE : M.E = M.loops ∪ M.coloops) :
    ∃ B E, B ⊆ E ∧ M = uniqueBaseOn B E :=
  ⟨M.coloops, M.E, M.coloops_subset_ground, eq_uniqueBaseOn_of_loops_union_coloops hE⟩

lemma exists_eq_uniqueBaseOn_or_removeColoops_rankPos (M : Matroid α) :
    (∃ B E, B ⊆ E ∧ M = uniqueBaseOn B E) ∨ M.removeColoops.RankPos := by
  obtain h1 | ⟨L, hL⟩ := M.removeColoops.eq_loopyOn_or_rankPos'.symm; exact .inr h1
  refine .inl <| exists_eq_uniqueBaseOn_of_loops_union_coloops <| subset_antisymm ?_ (by aesop_mat)
  rw [union_comm, ← diff_subset_iff, ← dual_ground, ← dual_loops, ← removeLoops_ground_eq_diff,
    ← dual_ground, ← removeColoops, hL, loopyOn_ground, ← removeColoops_loops_eq, hL, loopyOn_loops]

lemma uniqueBaseOn_loops_eq (I E : Set α) : (uniqueBaseOn I E).loops = E \ I := by
  simp [loops]

@[simp]
lemma uniqueBaseOn_coloops_eq' (I E : Set α) : (uniqueBaseOn I E).coloops = I ∩ E := by
  simp [coloops, loops, inter_comm I]

lemma uniqueBaseOn_coloops_eq {I E : Set α} (h : I ⊆ E) : (uniqueBaseOn I E).coloops = I := by
  simp [h]

end Constructions

lemma IsNonloop.isNonloop_of_isRestriction_of_mem (he : M.IsNonloop e) (hNM : N ≤r M)
    (heN : e ∈ N.E) : N.IsNonloop e := by
  simpa using he.indep.indep_isRestriction hNM (by simpa)

lemma IsRestriction.isNonloop_iff (hNM : N ≤r M) : N.IsNonloop e ↔ M.IsNonloop e ∧ e ∈ N.E := by
  refine ⟨fun h ↦ ⟨h.of_isRestriction hNM, h.mem_ground⟩,
    fun h ↦ h.1.isNonloop_of_isRestriction_of_mem hNM h.2⟩

lemma IsLoop.isLoop_of_isRestriction_of_mem (he : M.IsLoop e) (hNM : N ≤r M)
    (heN : e ∈ N.E) : N.IsLoop e := by
  simpa using he.dep.dep_isRestriction hNM (by simpa)

end Matroid
