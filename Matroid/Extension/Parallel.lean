import Matroid.Simple
import Matroid.Extension.ModularCut
import Matroid.ForMathlib.Function

open Set Function Set.Notation
namespace Matroid



section Set

/-- Replace the elements of `S` with parallel copies of `e`. -/
def parallelExtendSet {α : Type*} (M : Matroid α) (e : α) (S : Set α) [DecidablePred (· ∈ S)] :
    Matroid α :=
  M.comap (fun x ↦ if x ∈ S then e else x)

end Set

section IsLoop

variable {α : Type*} {M M' : Matroid α} {e f : α} {I : Set α}

/-- Add a loop `e` to a matroid `M`. Has the junk value `M` if `e ∈ M.E` -/
def addLoop (M : Matroid α) (e : α) : Matroid α := M ↾ (insert e M.E)

lemma addLoop_eq_self (he : e ∈ M.E) : M.addLoop e = M := by
  rw [addLoop, insert_eq_of_mem he, restrict_ground_eq_self]

@[simp] lemma addLoop_ground (M : Matroid α) (e : α) : (M.addLoop e).E = insert e M.E := rfl

@[simp] lemma addLoop_indep_iff : (M.addLoop f).Indep I ↔ M.Indep I := by
  simp only [addLoop, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun hI ↦ hI.subset_ground.trans (subset_insert _ _)

lemma eq_addLoop_iff (he : e ∉ M.E) : M' = M.addLoop e ↔ M'.IsLoop e ∧ M' ＼ {e} = M := by
  obtain (he' | he') := em' (e ∈ M'.E)
  · refine iff_of_false ?_ ?_
    · rintro rfl; simp at he'
    rintro ⟨h, rfl⟩; exact he' h.mem_ground

  simp_rw [ext_iff_indep, addLoop_ground, addLoop_indep_iff,
    delete_ground, delete_indep_iff, disjoint_singleton_right, ← singleton_dep, dep_iff,
    singleton_subset_iff, and_iff_left he', subset_diff, disjoint_singleton_right, and_imp]

  refine ⟨fun ⟨hE, hi⟩ ↦ ⟨?_, ?_, ?_⟩, fun ⟨hi, hE, h⟩ ↦ ⟨?_, fun I hIss ↦ ?_⟩⟩
  · rw [hi (singleton_subset_iff.2 he')]
    exact fun hei ↦ he (singleton_subset_iff.1 hei.subset_ground)
  · simp [hE, he]
  · rintro I hIss heI
    rw [and_iff_left heI, hi hIss]
  · rw [← hE, insert_diff_singleton, insert_eq_of_mem he']
  obtain (heI | heI) := em (e ∈ I)
  · exact iff_of_false (fun hI ↦ hi <| hI.subset (singleton_subset_iff.2 heI))
      (fun hI ↦ he <| hI.subset_ground heI)
  specialize h hIss
  simpa [heI] using h

lemma addLoop_isLoop (he : e ∉ M.E) : (M.addLoop e).IsLoop e := by
  rw [addLoop, ← singleton_dep, Dep, singleton_subset_iff, restrict_indep_iff,
    singleton_subset_iff, restrict_ground_eq, and_iff_left (mem_insert _ _),
    and_iff_left (mem_insert _ _)]
  exact fun hi ↦ he (singleton_subset_iff.1 hi.subset_ground)

instance addLoop_finite (M : Matroid α) [M.Finite] (e : α) : (M.addLoop e).Finite :=
  ⟨M.ground_finite.insert e⟩

instance addLoop_rankFinite (M : Matroid α) [M.RankFinite] (e : α) : (M.addLoop e).RankFinite := by
  obtain ⟨B, hB⟩ := (addLoop M e).exists_isBase
  exact ⟨⟨B, hB, (addLoop_indep_iff.1 hB.indep).finite⟩⟩

instance addLoop_finitary (M : Matroid α) [M.Finitary] (e : α) : (M.addLoop e).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [addLoop_indep_iff] at *
  exact Finitary.indep_of_forall_finite I hI

def addColoop (M : Matroid α) (e : α) : Matroid α := (M✶.addLoop e)✶

lemma addColoop_eq_self (he : e ∈ M.E) : M.addColoop e = M := by
  rwa [addColoop, addLoop_eq_self, dual_dual]

@[simp] lemma addColoop_ground (M : Matroid α) (e : α) : (M.addColoop e).E = insert e M.E := rfl

lemma eq_addColoop_iff (he : e ∉ M.E) :
    M' = M.addColoop e ↔ M'.IsColoop e ∧ (M' ／ {e}) = M := by
  rw [addColoop, eq_dual_comm, eq_comm, eq_addLoop_iff (show e ∉ M✶.E from he),
    dual_isLoop_iff_isColoop, eq_dual_comm, dual_delete_dual, eq_comm]

end IsLoop

section Parallel

variable {α : Type*} [DecidableEq α] {M M' : Matroid α} {e f x : α} {I C : Set α}

/-- Replace `f` with a parallel copy of `e` in `M`. Intended for use where `e` is a nonloop
  and `f ∉ M.E`. When this is not the case, the junk value is described by
  either `parallelExtend_not_nonloop` or `parallelExtend_delete_eq` -/
def parallelExtend (M : Matroid α) (e f : α) : Matroid α :=
  (M.comap (update id f e)) ↾ (insert f M.E)

@[simp] lemma parallelExtend_ground (M : Matroid α) (e f : α) :
    (M.parallelExtend e f).E = insert f M.E := rfl

@[simp] lemma parallelExtend_self (M : Matroid α) (e : α) :
    M.parallelExtend e e = M.addLoop e := by
  change comap _ (update id e (id e)) ↾ _ = _
  rw [update_eq_self, comap_id, addLoop]

lemma parallelExtend_not_isNonloop (he : ¬M.IsNonloop e) (f : α) :
    M.parallelExtend e f = (M ＼ {f}).addLoop f := by
  classical
  simp only [parallelExtend, ext_iff_indep, restrict_ground_eq, addLoop_ground, delete_ground,
    insert_diff_singleton, restrict_indep_iff, comap_indep_iff, image_update, id_eq, image_id',
    update_id_injOn_iff, addLoop_indep_iff, delete_indep_iff, disjoint_singleton_right, true_and]

  rintro I hI
  split_ifs with hf
  · simp [(show ¬ M.Indep (insert e _) from
      fun hi ↦ he <| hi.isNonloop_of_mem (mem_insert _ _)), hf]
  simp [hf, hI]

lemma parallelExtend_eq_parallelExtend_delete (M : Matroid α) {e f : α} (hef : e ≠ f):
    M.parallelExtend e f = (M ＼ {f}).parallelExtend e f := by
  classical
  rw [parallelExtend, parallelExtend, delete_ground, insert_diff_singleton, ext_iff_indep]
  simp only [restrict_ground_eq, restrict_indep_iff, comap_indep_iff, image_update, id_eq,
    image_id', update_id_injOn_iff, delete_indep_iff, disjoint_singleton_right, and_congr_left_iff,
    iff_self_and, true_and]
  aesop

/-- Deleting `f` in a parallel extension of `M` by `f` is the same as deleting `f` from `M`.
  This could be a simp lemma, but it is less convenient than the 'non-junk' unprimed version,
  which is simpler for reasonable inputs, even though it requires `f ∉ M.E` explicitly.  -/
lemma parallelExtend_delete_eq' (M : Matroid α) (e f : α) :
    (M.parallelExtend e f) ＼ {f} = M ＼ {f} := by
  classical
  suffices ∀ I ⊆ M.E, _ → _ → I ⊆ insert f M.E by simpa +contextual [parallelExtend,
    ext_iff_indep, subset_diff]
  exact fun I hI _ _ ↦ hI.trans (subset_insert _ _)

lemma parallelExtend_delete_eq (e : α) (hf : f ∉ M.E) : (M.parallelExtend e f) ＼ {f} = M := by
  rwa [parallelExtend_delete_eq', delete_eq_self_iff, disjoint_singleton_left]

lemma parallelExtend_isNonloop_iff (he : M.IsNonloop e) :
    (M.parallelExtend e f).IsNonloop x ↔ M.IsNonloop x ∨ x = f := by
  classical
  rw [← indep_singleton, parallelExtend, restrict_indep_iff, singleton_subset_iff,
    comap_indep_iff, and_iff_left (injOn_singleton _ _), mem_insert_iff,
    image_update, image_id, image_id]
  obtain (rfl | hne) := eq_or_ne x f
  · simpa
  simp only [mem_singleton_iff, hne.symm, not_false_eq_true, diff_singleton_eq_self, ite_false,
    indep_singleton, hne, false_or, or_false, and_iff_left_iff_imp]
  exact IsNonloop.mem_ground

lemma parallelExtend_parallel (he : M.IsNonloop e) (f : α) :
    (M.parallelExtend e f).Parallel e f := by
  classical
  have he' : (M.parallelExtend e f).IsNonloop e := by
    rw [parallelExtend_isNonloop_iff he]; left; assumption
  have hf : (M.parallelExtend e f).IsNonloop f := by
    rw [parallelExtend_isNonloop_iff he]; right; rfl
  obtain (rfl | hef) := eq_or_ne e f
  · rwa [parallel_self_iff]
  rw [he'.parallel_iff_dep hf hef, Dep, pair_subset_iff, and_iff_right he'.mem_ground,
    and_iff_left hf.mem_ground, parallelExtend, restrict_indep_iff, comap_indep_iff,
    image_update, image_id, image_id,
    if_pos (mem_insert_of_mem _ (show f ∈ ({f} : Set α) from rfl))]
  exact fun hcon ↦ hef <| hcon.1.2 (by simp) (by simp) (by simp [update_of_ne hef e id])

lemma eq_parallelExtend_iff (he : M.IsNonloop e) (hf : f ∉ M.E) :
    M' = M.parallelExtend e f ↔ M'.Parallel e f ∧ M' ＼ {f} = M := by
  classical
  constructor
  · rintro rfl; exact ⟨parallelExtend_parallel he f, parallelExtend_delete_eq e hf⟩
  rintro ⟨h, rfl⟩
  simp only [delete_isNonloop_iff, mem_singleton_iff] at he
  refine ext_indep (by simp [insert_eq_of_mem h.mem_ground_right])
    (fun I hI ↦ ?_)
  obtain (hfI | hfI) := em' (f ∈ I)
  · simp [hfI, parallelExtend, hI.trans (subset_insert _ _)]
  suffices M'.Indep I ↔ M'.Indep (insert e (I \ {f})) ∧ e ∉ I by
    simpa [hfI, parallelExtend, Ne.symm he.2, hI.trans (subset_insert _ _)]
  obtain (heI | heI) := em (e ∈ I)
  · simp [heI, show ¬ M'.Indep I from
      fun hI ↦ he.2 (h.eq_of_indep (hI.subset (pair_subset heI hfI)))]
  simp [heI, h.parallel'.symm.indep_substitute_iff hfI heI]

lemma parallelExtend_closure_eq_of_mem (he : M.IsNonloop e) (hf : f ∉ M.E) (X : Set α)
    (heX : e ∈ M.closure X) : (M.parallelExtend e f).closure X = insert f (M.closure X) := by
  nth_rw 2 [← M.parallelExtend_delete_eq e hf]
  simp only [delete_closure_eq, insert_diff_singleton]
  rw [← M.parallelExtend_delete_eq e hf, delete_closure_eq, mem_diff,
    (parallelExtend_parallel he f).mem_closure_iff_mem_closure] at heX
  rw [closure_diff_singleton_eq_closure heX.1, eq_comm, insert_eq_self]
  exact mem_of_mem_of_subset heX.1 (closure_subset_closure _ diff_subset)

lemma parallelExtend_closure_eq_of_notMem_notMem (he : M.IsNonloop e) (hf : f ∉ M.E) {X : Set α}
    (heX : e ∉ M.closure X) (hfX : f ∉ X) : (M.parallelExtend e f).closure X = M.closure X := by
  nth_rw 2 [← M.parallelExtend_delete_eq e hf]
  have hfX' : f ∉ (M.parallelExtend e f).closure (X \ {f}) := by
    rw [← M.parallelExtend_delete_eq e hf, delete_closure_eq, mem_diff,
      (parallelExtend_parallel he f).mem_closure_iff_mem_closure] at heX
    simpa [(show e ≠ f by rintro rfl; exact hf he.mem_ground)] using heX
  simp only [delete_closure_eq, diff_singleton_eq_self hfX']
  rw [diff_singleton_eq_self hfX]

lemma parallelExtend_indep_iff (he : M.IsNonloop e) (hf : f ∉ M.E) :
    (M.parallelExtend e f).Indep I ↔
      (f ∉ I ∧ M.Indep I) ∨ (f ∈ I ∧ e ∉ I ∧ M.Indep (insert e (I \ {f}))) := by
  have hdel : ∀ J, f ∉ J → ((M.parallelExtend e f).Indep J ↔ M.Indep J) := by
    rintro J hfJ
    convert (delete_indep_iff (M := M.parallelExtend e f) (D := {f}) (I := J)).symm using 1
    · rw [disjoint_singleton_right, and_iff_left hfJ]
    rw [parallelExtend_delete_eq', delete_indep_iff, disjoint_singleton_right, and_iff_left hfJ]
  have hef : e ≠ f := by rintro rfl; exact hf he.mem_ground

  obtain (hfI | hfI) := em (f ∈ I)
  · rw [iff_true_intro hfI, not_true, false_and, false_or, true_and]
    obtain (heI | heI) := em (e ∈ I)
    · simp only [heI, not_true_eq_false, false_and, iff_false]
      exact fun hi ↦ ((parallelExtend_parallel he f).dep_of_ne hef).not_indep
        (hi.subset (pair_subset heI hfI))
    rw [and_iff_right heI,
      (parallelExtend_parallel he f).parallel'.symm.indep_substitute_iff hfI heI, hdel]
    rintro (rfl | h); exact hef rfl
    exact h.2 rfl
  simp [hdel _ hfI, hfI]

lemma parallelExtend_isCircuit_iff (he : M.IsNonloop e) (hf : f ∉ M.E) :
    (M.parallelExtend e f).IsCircuit C ↔ M.IsCircuit C ∨ C = {e,f} ∨
        f ∈ C ∧ e ∉ C ∧ M.IsCircuit (insert e (C \ {f})) := by
  have hef : e ≠ f := by rintro rfl; exact hf he.mem_ground
  have aux : ∀ ⦃C' : Set α⦄, f ∉ C' → ((M.parallelExtend e f).IsCircuit C' ↔ M.IsCircuit C') := by
    intro C' hfC'
    suffices h' : ((M.parallelExtend e f) ＼ {f}).IsCircuit C' ↔ M.IsCircuit C' by
      simpa [delete_isCircuit_iff, hfC'] using h'
    rw [parallelExtend_delete_eq _ hf]
  by_cases hfC : f ∈ C; swap
  · simp [aux hfC, hfC, show C ≠ {e,f} by rintro rfl; simp at hfC]
  simp only [show ¬M.IsCircuit C from fun h ↦ hf <| h.subset_ground hfC, hfC, true_and, false_or]
  by_cases heC : e ∈ C
  · suffices (M.parallelExtend e f).IsCircuit C ↔ C = {e, f} by simpa [heC]
    have hC := (M.parallelExtend_parallel he f).isCircuit_of_ne hef
    exact ⟨fun h ↦ Eq.symm <| hC.eq_of_subset_isCircuit h (by simp [pair_subset_iff, heC, hfC]),
      by rintro rfl; assumption⟩
  rw [← (M.parallelExtend_parallel he f).parallel'.eq_mapEquiv_swap, mapEquiv_isCircuit_iff,
    Equiv.symm_swap, Equiv.swap_comm, Equiv.swap_image_eq_exchange hfC heC,
    aux (by simp [hef.symm])]
  simp [heC, show C ≠ {e,f} by rintro rfl; simp at heC]

instance parallelExtend_finite (M : Matroid α) [M.Finite] (e f : α) :
    (M.parallelExtend e f).Finite :=
  ⟨M.ground_finite.insert f⟩

instance parallelExtend_rankFinite (M : Matroid α) [RankFinite M] (e f : α) :
    (M.parallelExtend e f).RankFinite := by
  obtain ⟨B, hB⟩ := (M.parallelExtend e f).exists_isBase
  have hB' : M.Indep (B \ {f}) := by
    rw [indep_iff_delete_of_disjoint (disjoint_sdiff_left (t := B) (s := {f})),
      ← parallelExtend_delete_eq' M e f, delete_indep_iff, and_iff_left disjoint_sdiff_left]
    exact hB.indep.subset diff_subset
  exact ⟨⟨_, hB, (hB'.finite.insert f).subset <| by simp⟩⟩

instance parallelExtend_finitary (M : Matroid α) [Finitary M] (e f : α) :
    (M.parallelExtend e f).Finitary := by
  obtain (rfl | hef) := eq_or_ne e f
  · rw [parallelExtend_self]; infer_instance
  obtain (he | he) := em' (M.IsNonloop e)
  · rw [parallelExtend_not_isNonloop he]
    infer_instance
  rw [parallelExtend_eq_parallelExtend_delete _ hef, finitary_iff_forall_isCircuit_finite]
  intro C
  rw [parallelExtend_isCircuit_iff, delete_isCircuit_iff, disjoint_singleton_right,
    delete_isCircuit_iff]
  · rintro (h | rfl | h)
    · exact h.1.finite
    · exact toFinite {e, f}
    refine (h.2.2.1.finite.insert f).subset ?_
    rw [insert_comm, insert_diff_singleton]
    exact (subset_insert _ _).trans (subset_insert _ _)
  · rwa [delete_isNonloop_iff, and_iff_right he]
  exact fun h ↦ h.2 rfl

end Parallel

section Series

variable {α : Type*} [DecidableEq α] {M M' : Matroid α} {e f : α}

/-- Coextend `e` by `f` in series. Intended for use where `e` is a non-isColoop and `f ∉ M.E`. -/
def seriesExtend (M : Matroid α) (e f : α) : Matroid α := (M✶.parallelExtend e f)✶

@[simp] lemma seriesExtend_dual (M : Matroid α) (e f : α) :
    (M.seriesExtend e f)✶ = M✶.parallelExtend e f := by
  rw [seriesExtend, dual_dual]

@[simp] lemma parallelExtend_dual (M : Matroid α) (e f : α) :
    (M.parallelExtend e f)✶ = M✶.seriesExtend e f := by
  rw [seriesExtend, dual_dual]

@[simp] lemma seriesExtend_ground (M : Matroid α) (e f : α) :
    (M.seriesExtend e f).E = insert f M.E := rfl

@[simp] lemma seriesExtend_self (M : Matroid α) (e : α) :
    M.seriesExtend e e = M.addColoop e := by
  rw [seriesExtend, parallelExtend_self, addColoop]

lemma seriesExtend_isColoop (he : M.IsColoop e) (f : α) :
    M.seriesExtend e f = (M ／ {f}).addColoop f := by
  rw [seriesExtend, parallelExtend_not_isNonloop, addColoop, dual_contract]
  simp [isNonloop_iff, dual_isLoop_iff_isColoop, he]

lemma seriesExtend_notMem_ground (he : e ∉ M.E) (f : α) :
    M.seriesExtend e f = (M ／ {f}).addColoop f := by
  rw [seriesExtend, parallelExtend_not_isNonloop, addColoop, dual_contract]
  simp [isNonloop_iff, he]

lemma seriesExtend_eq_seriesExtend_contract (M : Matroid α) {e f : α} (hef : e ≠ f):
    M.seriesExtend e f = (M ／ {f}).seriesExtend e f := by
  rw [seriesExtend, parallelExtend_eq_parallelExtend_delete _ hef, seriesExtend]
  simp only [dual_contract]

lemma seriesExtend_contract_eq' (M : Matroid α) (e f : α) :
    ((M.seriesExtend e f) ／ {f}) = M ／ {f} := by
  rw [seriesExtend, ← dual_delete, parallelExtend_delete_eq']
  simp

lemma seriesExtend_contract_eq (e : α) (hf : f ∉ M.E) : (M.seriesExtend e f ／ {f}) = M := by
  rw [seriesExtend, ← dual_delete, parallelExtend_delete_eq _ (show f ∉ M✶.E from hf), dual_dual]

lemma seriesExtend_series (heE : e ∈ M.E) (he : ¬M.IsColoop e) (f : α) :
    (M.seriesExtend e f).Series e f := by
  rw [Series, seriesExtend, dual_dual]
  apply parallelExtend_parallel
  rwa [isNonloop_iff, dual_ground, and_iff_left heE, dual_isLoop_iff_isColoop]

lemma eq_seriesExtend_iff (heE : e ∈ M.E) (he : ¬M.IsColoop e) (hf : f ∉ M.E) :
    M' = M.seriesExtend e f ↔ M'.Series e f ∧ ((M' ／ {f}) = M) := by
  rw [seriesExtend, eq_dual_comm, eq_comm, eq_parallelExtend_iff _ (show f ∉ M✶.E from hf),
    ← dual_contract, dual_inj, Series]
  rwa [isNonloop_iff, and_iff_left (show e ∈ M✶.E from heE), dual_isLoop_iff_isColoop]

instance seriesExtend_finite (M : Matroid α) [M.Finite] : (M.seriesExtend e f).Finite :=
  ⟨M.ground_finite.insert f⟩

end Series

variable {α β : Type*} {M : Matroid α} {N : Matroid β} {P : β → Set α}

lemma multiExtendLoopless_aux (φ : α → β) (hφN : ∀ x ∈ N.E, ∀ e ∈ P x, φ e = x) {I : Set α} :
    (N.comapOn (⋃ f ∈ N.E, P f) φ).Indep I ↔ (N.Indep {f ∈ N.E | ((P f) ∩ I).Nonempty} ∧
    (∀ f ∈ N.E, (P f ∩ I).Subsingleton) ∧ I ⊆ ⋃ f ∈ N.E, P f) := by
  have aux1 (I) (hI : I ⊆ ⋃ f ∈ N.E, P f) : φ '' I = {f ∈ N.E | (P f ∩ I).Nonempty} := by
    ext b
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨b, hbI, rfl⟩
      obtain ⟨x, hxN, hbx⟩ : ∃ x ∈ N.E, b ∈ P x := by simpa using hI hbI
      exact ⟨by grind, b, by grind⟩
    rintro ⟨hb, ⟨e, ⟨heb, heI⟩⟩⟩
    grind
  have aux2 (I) (hI : I ⊆ ⋃ f ∈ N.E, P f) : InjOn φ I ↔ ∀ f ∈ N.E, (P f ∩ I).Subsingleton := by
    refine ⟨fun h b hbN e he f hf ↦ h he.2 hf.2 <| by grind, fun h e heI f hfI hef ↦ ?_⟩
    obtain ⟨x, hxN, hbx⟩ : ∃ x ∈ N.E, e ∈ P x := by simpa using hI heI
    obtain ⟨y, hyN, hby⟩ : ∃ y ∈ N.E, f ∈ P y := by simpa using hI hfI
    exact h x hxN ⟨hbx, heI⟩ ⟨by grind, hfI⟩
  simp +contextual [comapOn_indep_iff, ← and_assoc, and_congr_left_iff, aux1, aux2]

/-- Given a matroid `N` on `β` and a function `P` that maps the elements of `N` to
pairwise disjoint sets in `α`, constructs the matroid on `α` obtained from `N` by replacing
each element `f` of `N` with the parallel class `P f` of elements of `α`.

This is essentially a comap in the opposite direction. -/
def multiExtendLoopless (N : Matroid β) (P : β → Set α) (dj : N.E.Pairwise (Disjoint on P)) :
    Matroid α := Matroid.ofExistsMatroid
  (E := ⋃ f ∈ N.E, P f)
  (fun I ↦ N.Indep {f ∈ N.E | ((P f) ∩ I).Nonempty} ∧
    (∀ f ∈ N.E, (P f ∩ I).Subsingleton) ∧ I ⊆ ⋃ f ∈ N.E, P f)
  (by
    obtain hβ | hβ := isEmpty_or_nonempty β
    · exact ⟨emptyOn α, by simp [eq_empty_of_isEmpty]⟩
    have hinv : ∀ x ∈ ⋃ f ∈ N.E, P f, ∃! e ∈ N.E, x ∈ P e := by
      simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp]
      refine fun x  b hb hxb ↦ ⟨b, ⟨hb, hxb⟩, fun c ⟨hcN, hcx⟩ ↦ by_contra fun hcb ↦ ?_⟩
      exact (dj hcN hb hcb).notMem_of_mem_left hcx hxb
    choose! φ hφ hu using hinv
    refine ⟨N.comapOn (⋃ f ∈ N.E, P f) φ, rfl, fun I ↦ ?_⟩
    simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp] at hφ
    simp only [mem_iUnion, exists_prop, and_imp, forall_exists_index] at hu
    rw [multiExtendLoopless_aux (φ := φ) (by grind)] )


@[simp]
def multiExtendLoopless_ground (N : Matroid β) (P : β → Set α) (dj : N.E.Pairwise (Disjoint on P)) :
    (N.multiExtendLoopless P dj).E = ⋃ e ∈ N.E, P e := rfl

@[simp]
def multiExtendLoopless_indep (N : Matroid β) (P : β → Set α) (dj : N.E.Pairwise (Disjoint on P))
    {I : Set α} : (N.multiExtendLoopless P dj).Indep I ↔ N.Indep {f ∈ N.E | ((P f) ∩ I).Nonempty} ∧
    (∀ f ∈ N.E, (P f ∩ I).Subsingleton) ∧ I ⊆ ⋃ f ∈ N.E, P f := Iff.rfl

lemma multiExtendLoopless_eq_comapOn [Nonempty β] (N : Matroid β) (P : β → Set α)
    (dj : N.E.Pairwise (Disjoint on P)) (hne : ∀ x ∈ N.E, (P x).Nonempty) :
    ∃ (φ : α → β), (∀ x ∈ N.E, ∀ e ∈ P x, φ e = x) ∧ (SurjOn φ (⋃ x ∈ N.E, P x) N.E) ∧
    N.multiExtendLoopless P dj = N.comapOn (⋃ f ∈ N.E, P f) φ := by
  have hinv : ∀ x ∈ ⋃ f ∈ N.E, P f, ∃! e ∈ N.E, x ∈ P e := by
    simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp]
    refine fun x  b hb hxb ↦ ⟨b, ⟨hb, hxb⟩, fun c ⟨hcN, hcx⟩ ↦ by_contra fun hcb ↦ ?_⟩
    exact (dj hcN hb hcb).notMem_of_mem_left hcx hxb
  choose! φ hφ hu using hinv
  simp only [mem_iUnion, exists_prop, forall_exists_index, forall_and_index] at hφ hu
  refine ⟨φ, by grind, fun x hx ↦ ?_, ext_indep (by simp) fun I hIE ↦ ?_⟩
  · obtain ⟨e, he⟩ := hne x hx
    exact ⟨e, mem_iUnion₂.2 (by grind), by grind⟩
  simp only [multiExtendLoopless_indep]
  rw [multiExtendLoopless_aux _ (by grind)]

/-- the same as `multiExtendLoopless`, but with a specified set `L` of loops added. -/
def multiExtend (N : Matroid β) (P : β → Set α) (L : Set α) (dj : N.E.Pairwise (Disjoint on P)) :
    Matroid α := (N.multiExtendLoopless P dj ↾ (L ∪ ⋃ f ∈ N.E, P f))

@[simp]
lemma multiExtend_ground (N : Matroid β) (L : Set α) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)} : (multiExtend N P L dj).E = (⋃ i ∈ N.E, P i) ∪ L := by
  simp [multiExtend, union_comm]

lemma multiExtend_ground_of_onUniv (N : Matroid β) [OnUniv N] (L : Set α) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)} : (multiExtend N P L dj).E = (⋃ i, P i) ∪ L := by
  simp [multiExtend, union_comm]

@[simp]
lemma multiExtend_indep_iff (N : Matroid β) (L : Set α) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)} {I : Set α} :
    (multiExtend N P L dj).Indep I ↔ N.Indep {f ∈ N.E | ((P f) ∩ I).Nonempty}
      ∧ (∀ f ∈ N.E, (P f ∩ I).Subsingleton) ∧ I ⊆ ⋃ f ∈ N.E, P f := by
  simp only [multiExtend, multiExtendLoopless, Matroid.ofExistsMatroid, restrict_indep_iff,
    IndepMatroid.matroid_Indep, and_iff_left_iff_imp, and_imp]
  grind

lemma multiExtend_delete_loops (N : Matroid β) (L : Set α) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)}  (hLP : ∀ i ∈ N.E, Disjoint (P i) L):
    (multiExtend N P L dj) ＼ L = multiExtendLoopless N P dj := by
  refine ext_indep (by simpa) <| ?_
  simp only [delete_indep_iff, multiExtend_indep_iff, multiExtendLoopless_indep]
  grind

lemma multiExtend_eq_diff (N : Matroid β) (L : Set α) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)} :
    multiExtend N P L dj = multiExtend N P (L \ ⋃ f ∈ N.E, P f) dj :=
  ext_indep (by simp) (by simp)

lemma multiExtend_indep_iff_of_onUniv (N : Matroid β) [OnUniv N] (L : Set α) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)} {I : Set α} :
    (multiExtend N P L dj).Indep I ↔ N.Indep {f ∈ N.E | ((P f) ∩ I).Nonempty}
      ∧ (∀ f ∈ N.E, (P f ∩ I).Subsingleton) ∧ I ⊆ ⋃ f ∈ N.E, P f := by
  simp [multiExtend_indep_iff]

@[simp]
lemma multiExtend_map {α β γ : Type*} (N : Matroid β) (f : β → γ) (hf : InjOn f N.E)
    (P : γ → Set α) (L : Set α) (hP) : (N.map f hf).multiExtend P L hP = N.multiExtend (P ∘ f) L
      ((hf.pairwiseDisjoint_image (f := P)).1 hP) := by
  refine ext_indep (by simp) fun I hi ↦ ?_
  simp only [multiExtend_indep_iff, map_ground, mem_image, map_indep_iff, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right,
    comp_apply, and_congr_left_iff]
  refine fun hss hIss ↦ ⟨fun ⟨I₀, hI₀, hI₀'⟩ ↦ hI₀.subset ?_, fun hI ↦ ⟨_, hI, by grind⟩⟩
  rw [← hf.image_subset_image_iff (by grind) hI₀.subset_ground, ← hI₀']
  grind

lemma multiExtendLoopless_eRank_eq (N : Matroid β) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)} (hP : ∀ x ∈ N.E, (P x).Nonempty) :
    (N.multiExtendLoopless P dj).eRank = N.eRank := by
  obtain hβ | hβ := isEmpty_or_nonempty β
  · simp only [eq_emptyOn N, eRank_emptyOn]
    rw [((emptyOn β).multiExtendLoopless P _).ground_eq_empty_iff.1 ?_, eRank_emptyOn]
    simp
  obtain ⟨φ, hφ1, hφ2, h⟩ := multiExtendLoopless_eq_comapOn N P dj hP
  rw [h, eRank_comapOn _ hφ2]

lemma multiExtend_eRank_eq (N : Matroid β) (L : Set α) (P : β → Set α)
    {dj : N.E.Pairwise (Disjoint on P)} (hP : ∀ f ∈ N.E, (P f).Nonempty) :
    (N.multiExtend P L dj).eRank = N.eRank := by
  rw [multiExtend, eRank_restrict, ← eRk_inter_ground, multiExtendLoopless_ground,
    inter_eq_self_of_subset_right subset_union_right, ← multiExtendLoopless_ground _ _ dj,
    eRk_ground, multiExtendLoopless_eRank_eq _ _ hP]

lemma IsSimplification.multiExtendLoopless_eq {N M : Matroid α} [hM : M.Loopless]
    (hN : N.IsSimplification M) : N.multiExtendLoopless (fun e ↦ {x | M.Parallel e x})
    hN.setOf_parallel_pairwiseDisjoint = M := by
  simp only [ext_iff_indep, multiExtendLoopless_ground, ← hN.ground_eq_biUnion_setOf_parallel,
    multiExtendLoopless_indep, true_and]
  intro I hI
  obtain ⟨φ, hφ, hφNE, him, hpim, hidem⟩ := hN.simplifies.exists_eq_comap
  nth_rw 1 [and_iff_left hI, iff_comm, hφ, comap_indep_iff]
  simp_rw [hφ, comap_parallel_iff]
  have auxN {e} (he : e ∈ M.E) : φ e ∈ N.E := by grind
  have aux {e f} (he : e ∈ M.E) : M.Parallel e f ↔ φ e = φ f := by
    rw [hφ, comap_parallel_iff, hN.simple.parallel_iff_eq (auxN he)]
  convert Iff.rfl using 3
  · ext e
    simp only [mem_setOf_eq, mem_image]
    constructor
    · rintro ⟨heN, ⟨x, hex : N.Parallel _ _, hxI⟩⟩
      refine ⟨x, hxI, ?_⟩
      rw [show e = φ e from hφNE heN, ← hidem e, ← hidem x, eq_comm, ← aux]
      · refine hex.of_isRestriction hN.isRestriction
      exact hN.isRestriction.subset hex.mem_ground_left
    rintro ⟨x, hxI, rfl⟩
    refine ⟨auxN (hI hxI), ⟨x, ?_, hxI⟩⟩
    rw [mem_setOf_eq, hidem, parallel_self_iff]
    exact hN.simple.isNonloop_of_mem <| auxN <| hI hxI
  refine ⟨fun h e heI f hfI hef ↦ ?_, fun h f hfN x ⟨hxf, hxI⟩ y ⟨hyf, hyI⟩ ↦ ?_⟩
  · refine h (φ e) (auxN (hI heI)) ⟨?_, heI⟩ ⟨?_, hfI⟩
    · simpa [hidem] using hN.simple.isNonloop_of_mem <| auxN (hI heI)
    simpa [hef, hidem] using hN.simple.isNonloop_of_mem <| auxN (hI heI)
  refine h hxI hyI ?_
  rw [← hN.simple.parallel_iff_eq (auxN (hI hxI))]
  exact hxf.symm.trans hyf

lemma IsSimplification.multiExtend_eq {N M : Matroid α} (hN : N.IsSimplification M) :
    N.multiExtend (fun e ↦ {x | M.Parallel e x})
    M.loops hN.setOf_parallel_pairwiseDisjoint = M := by
  have aux := hN.isSimplification_removeLoops.multiExtendLoopless_eq
  simp_rw [removeLoops_parallel_iff] at aux
  rw [multiExtend, aux, union_comm, ← hN.ground_eq_biUnion_setOf_parallel_union_loops,
    eq_restrict_removeLoops]

-- (unifOn E 2).multiExtend (fun e ↦ {x | M.Parallel e x}) M.loops ⋯ =
--   (unifOn ((fun e ↦ {x | M.Parallel e x}) '' E) 2).multiExtend id M.loops ⋯
