import Matroid.Simple
import Matroid.Closure
import Matroid.Minor.Basic
import Matroid.Map
import Matroid.ForMathlib.Other

open Set Function
namespace Matroid



section Set

/-- Replace the elements of `S` with parallel copies of `e`. -/
def parallelExtendSet {α : Type*} (M : Matroid α) (e : α) (S : Set α) [DecidablePred (· ∈ S)] :
    Matroid α :=
  M.comap (fun x ↦ if (x ∈ S) then e else x)

end Set


section Loop

variable {α : Type*} {M M' : Matroid α} {e f : α} {I : Set α}

/-- Add a loop `e` to a matroid `M`. Has the junk value `M` if `e ∈ M.E` -/
def addLoop (M : Matroid α) (e : α) : Matroid α := M ↾ (insert e M.E)

theorem addLoop_eq_self (he : e ∈ M.E) : M.addLoop e = M := by
  rw [addLoop, insert_eq_of_mem he, restrict_ground_eq_self]

@[simp] theorem addLoop_ground (M : Matroid α) (e : α) : (M.addLoop e).E = insert e M.E := rfl

@[simp] theorem addLoop_indep_iff : (M.addLoop f).Indep I ↔ M.Indep I := by
  simp only [addLoop, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun hI ↦ hI.subset_ground.trans (subset_insert _ _)

theorem eq_addLoop_iff (he : e ∉ M.E) : M' = M.addLoop e ↔ M'.Loop e ∧ M' ⧹ e = M := by
  obtain (he' | he') := em' (e ∈ M'.E)
  · refine iff_of_false ?_ ?_
    · rintro rfl; simp at he'
    rintro ⟨h, rfl⟩; exact he' h.mem_ground

  simp_rw [deleteElem, eq_iff_indep_iff_indep_forall, addLoop_ground, addLoop_indep_iff,
    delete_ground, delete_indep_iff, disjoint_singleton_right, ← singleton_dep, dep_iff,
    singleton_subset_iff, and_iff_left he', subset_diff, disjoint_singleton_right, and_imp]

  refine ⟨fun ⟨hE, hi⟩ ↦ ⟨?_, ?_, ?_⟩, fun ⟨hi, hE, h⟩ ↦ ⟨?_, fun I hIss ↦ ?_⟩⟩
  · rw [hi _ (singleton_subset_iff.2 he')]
    exact fun hei ↦ he (singleton_subset_iff.1 hei.subset_ground)
  · simp [hE, he]
  · rintro I hIss heI
    rw [and_iff_left heI, hi _ hIss]
  · rw [← hE, insert_diff_singleton, insert_eq_of_mem he']
  obtain (heI | heI) := em (e ∈ I)
  · exact iff_of_false (fun hI ↦ hi <| hI.subset (singleton_subset_iff.2 heI))
      (fun hI ↦ he <| hI.subset_ground heI)
  specialize h I hIss
  simpa [heI] using h

theorem addLoop_loop (he : e ∉ M.E) : (M.addLoop e).Loop e := by
  rw [addLoop, ← singleton_dep, Dep, singleton_subset_iff, restrict_indep_iff,
    singleton_subset_iff, restrict_ground_eq, and_iff_left (mem_insert _ _),
    and_iff_left (mem_insert _ _)]
  exact fun hi ↦ he (singleton_subset_iff.1 hi.subset_ground)

instance addLoop_finite (M : Matroid α) [M.Finite] (e : α) : (M.addLoop e).Finite :=
  ⟨M.ground_finite.insert e⟩

instance addLoop_finiteRk (M : Matroid α) [M.FiniteRk] (e : α) : (M.addLoop e).FiniteRk := by
  obtain ⟨B, hB⟩ := (addLoop M e).exists_base
  exact ⟨⟨B, hB, (addLoop_indep_iff.1 hB.indep).finite⟩⟩

instance addLoop_finitary (M : Matroid α) [M.Finitary] (e : α) : (M.addLoop e).Finitary := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [addLoop_indep_iff] at *
  exact Finitary.indep_of_forall_finite I hI

def addColoop (M : Matroid α) (e : α) : Matroid α := (M✶.addLoop e)✶

theorem addColoop_eq_self (he : e ∈ M.E) : M.addColoop e = M := by
  rwa [addColoop, addLoop_eq_self, dual_dual]

@[simp] theorem addColoop_ground (M : Matroid α) (e : α) : (M.addColoop e).E = insert e M.E := rfl

theorem eq_addColoop_iff (he : e ∉ M.E) : M' = M.addColoop e ↔ M'.Coloop e ∧ (M' ⧸ e) = M := by
  rw [addColoop, eq_dual_comm, eq_comm, eq_addLoop_iff (show e ∉ M✶.E from he),
    dual_loop_iff_coloop, eq_dual_comm, deleteElem, dual_delete_dual_eq_contract, contract_elem,
    eq_comm]

end Loop

section Parallel

variable {α : Type*} [DecidableEq α] {M M' : Matroid α} {e f x : α} {I C : Set α}

/-- Replace `f` with a parallel copy of `e` in `M`. Intended for use where `e` is a nonloop
  and `f ∉ M.E`. When this is not the case, the junk value is described by
  either `parallelExtend_not_nonloop` or `parallelExtend_delete_mem_eq` -/
def parallelExtend (M : Matroid α) (e f : α) : Matroid α :=
  (M.comap (update id f e)) ↾ (insert f M.E)

@[simp] theorem parallelExtend_ground (M : Matroid α) (e f : α) :
    (M.parallelExtend e f).E = insert f M.E := rfl

@[simp] theorem parallelExtend_self (M : Matroid α) (e : α) :
    M.parallelExtend e e = M.addLoop e := by
  change comap _ (update id e (id e)) ↾ _ = _
  rw [update_eq_self, comap_id, addLoop]

theorem parallelExtend_not_nonloop (he : ¬M.Nonloop e) (f : α) :
    M.parallelExtend e f = (M ⧹ f).addLoop f := by
  classical
  simp only [parallelExtend, deleteElem, eq_iff_indep_iff_indep_forall, restrict_ground_eq,
    addLoop_ground, delete_ground, mem_diff, mem_singleton_iff, not_true_eq_false, and_false,
    insert_diff_singleton, restrict_indep_iff, comap_indep_iff, ne_eq, image_update, id_eq,
    image_id', update_id_injOn_iff, addLoop_indep_iff, delete_indep_iff, disjoint_singleton_right,
    true_and]

  rintro I hI
  split_ifs with hf
  · simp [(show ¬ M.Indep (insert e _) from fun hi ↦ he <| hi.nonloop_of_mem (mem_insert _ _)), hf]
  simp [hf, hI]

theorem parallelExtend_eq_parallelExtend_delete (M : Matroid α) {e f : α} (hef : e ≠ f):
    M.parallelExtend e f = (M ⧹ f).parallelExtend e f := by
  classical
  rw [parallelExtend, parallelExtend, deleteElem, delete_ground, insert_diff_singleton,
    eq_iff_indep_iff_indep_forall]
  simp only [restrict_ground_eq, restrict_indep_iff, comap_indep_iff, ne_eq, image_update, id_eq,
    image_id', mem_diff, mem_singleton_iff, update_id_injOn_iff, delete_indep_iff,
    disjoint_singleton_right, and_congr_left_iff, iff_self_and, true_and]
  aesop

/-- Deleting `f` in a parallel extension of `M` by `f` is the same as deleting `f` from `M`.
  This could be a simp lemma, but it is less convenient than the 'non-junk' unprimed version,
  which is simpler for reasonable inputs, even though it requires `f ∉ M.E` explicitly.  -/
theorem parallelExtend_delete_eq' (M : Matroid α) (e f : α) :
    (M.parallelExtend e f) ⧹ f = M ⧹ f := by
  classical
  simp only [parallelExtend, deleteElem, eq_iff_indep_iff_indep_forall, delete_ground,
    restrict_ground_eq, mem_insert_iff, true_or, not_true_eq_false, mem_singleton_iff,
    insert_diff_of_mem, subset_diff, disjoint_singleton_right, delete_indep_iff, restrict_indep_iff,
    comap_indep_iff, ne_eq, image_update, id_eq, image_id', mem_diff, update_id_injOn_iff,
    and_congr_left_iff, and_imp, true_and]
  rintro I - hf -
  simp only [hf, not_false_eq_true, diff_singleton_eq_self, ite_false, IsEmpty.forall_iff, and_true,
    and_iff_left_iff_imp]
  exact fun hI ↦ hI.subset_ground.trans <| subset_insert _ _

theorem parallelExtend_delete_eq (e : α) (hf : f ∉ M.E) : (M.parallelExtend e f) ⧹ f = M := by
  rwa [parallelExtend_delete_eq', deleteElem, delete_eq_self_iff, disjoint_singleton_left]

theorem parallelExtend_nonloop_iff (he : M.Nonloop e) :
    (M.parallelExtend e f).Nonloop x ↔ M.Nonloop x ∨ x = f := by
  classical
  rw [← indep_singleton, parallelExtend, restrict_indep_iff, singleton_subset_iff,
    comap_indep_iff, and_iff_left (injOn_singleton _ _), mem_insert_iff,
    image_update, image_id, image_id]

  obtain (rfl | hne) := eq_or_ne x f
  · simpa
  simp only [mem_singleton_iff, hne.symm, not_false_eq_true, diff_singleton_eq_self, ite_false,
    indep_singleton, hne, false_or, or_false, and_iff_left_iff_imp]
  exact Nonloop.mem_ground

theorem parallelExtend_parallel (he : M.Nonloop e) (f : α) :
    (M.parallelExtend e f).Parallel e f := by
  classical
  have he' : (M.parallelExtend e f).Nonloop e := by
    rw [parallelExtend_nonloop_iff he]; left; assumption
  have hf : (M.parallelExtend e f).Nonloop f := by
    rw [parallelExtend_nonloop_iff he]; right; rfl
  obtain (rfl | hef) := eq_or_ne e f
  · rwa [parallel_self_iff]
  rw [he'.parallel_iff_dep hf hef, Dep, pair_subset_iff, and_iff_right he'.mem_ground,
    and_iff_left hf.mem_ground, parallelExtend, restrict_indep_iff, comap_indep_iff,
    image_update, image_id, image_id,
    if_pos (mem_insert_of_mem _ (show f ∈ ({f} : Set α) from rfl))]
  exact fun hcon ↦ hef <| hcon.1.2 (by simp) (by simp) (by simp [update_noteq hef e id])

theorem parallelExtend_indep_iff (he : M.Nonloop e) (hf : f ∉ M.E) :
    (M.parallelExtend e f).Indep I ↔
      (f ∉ I ∧ M.Indep I) ∨ (f ∈ I ∧ e ∉ I ∧ M.Indep (insert e (I \ {f}))) := by
  have hdel : ∀ J, f ∉ J → ((M.parallelExtend e f).Indep J ↔ M.Indep J) := by
    rintro J hfJ
    convert (delete_indep_iff (M := M.parallelExtend e f) (D := {f}) (I := J)).symm using 1
    · rw [disjoint_singleton_right, and_iff_left hfJ]
    rw [← deleteElem, parallelExtend_delete_eq', deleteElem, delete_indep_iff,
      disjoint_singleton_right, and_iff_left hfJ]
  have hef : e ≠ f := by rintro rfl; exact hf he.mem_ground

  obtain (hfI | hfI) := em (f ∈ I)
  · rw [iff_true_intro hfI, not_true, false_and, false_or, true_and]
    obtain (heI | heI) := em (e ∈ I)
    · simp only [heI, not_true_eq_false, mem_diff, mem_singleton_iff, true_and, false_and,
        iff_false, parallelExtend_ground]
      exact fun hi ↦ ((parallelExtend_parallel he f).dep_of_ne hef).not_indep
        (hi.subset (pair_subset heI hfI))
    rw [and_iff_right heI, (parallelExtend_parallel he f).symm.indep_substitute_iff hfI heI, hdel]
    rintro (rfl | h); exact hef rfl
    exact h.2 rfl

  simp [hdel _ hfI, hfI]


theorem eq_parallelExtend_iff (he : M.Nonloop e) (hf : f ∉ M.E) :
    M' = M.parallelExtend e f ↔ M'.Parallel e f ∧ M' ⧹ f = M := by
  have hef : e ≠ f := by rintro rfl; exact hf he.mem_ground
  constructor
  · rintro rfl
    exact ⟨parallelExtend_parallel he f, parallelExtend_delete_eq _ hf⟩
  rintro ⟨hpar, rfl⟩
  apply eq_of_indep_iff_indep_forall
  · simp [insert_eq_of_mem hpar.mem_ground_right]
  rintro I -
  simp_rw [parallelExtend_indep_iff he hf, deleteElem, delete_indep_iff]
  simp only [disjoint_singleton_right, mem_diff, mem_singleton_iff, mem_insert_iff,
    not_true_eq_false, and_false, or_false, and_iff_left hef.symm]
  obtain (hfI | hfI) := em (f ∈ I)
  · simp only [hfI, not_true_eq_false, and_false, and_self, mem_diff, mem_singleton_iff, true_and,
      false_or]
    obtain (heI | heI) := em (e ∈ I)
    · simp only [heI, not_true_eq_false, mem_diff, mem_singleton_iff, true_and, false_and,
        iff_false]
      exact fun hI ↦ (hpar.dep_of_ne hef).not_indep (hI.subset <| pair_subset heI hfI)
    rw [hpar.symm.indep_substitute_iff hfI heI, and_iff_right heI]
  simp [hfI]

theorem parallelExtend_circuit_iff (he : M.Nonloop e) (hf : f ∉ M.E) :
    (M.parallelExtend e f).Circuit C ↔ M.Circuit C ∨ C = {e,f} ∨
        f ∈ C ∧ e ∉ C ∧ M.Circuit (insert e (C \ {f})) := by
  have hef : e ≠ f := by rintro rfl; exact hf he.mem_ground
  obtain (hfC | hfC) := em' (f ∈ C)
  · rw [circuit_iff_delete_of_disjoint (disjoint_singleton_right.2 hfC), ← deleteElem,
      parallelExtend_delete_eq _ hf, iff_false_intro hfC, false_and, or_false, or_iff_left]
    rintro rfl
    simp at hfC
  set i := (parallelExtend_parallel he f).swap with hi_def
  obtain (hss | hnss) := em (C ⊆ (parallelExtend M e f).E)
  · have hnC : ¬ M.Circuit C := fun hC ↦ hf (hC.subset_ground hfC)
    rw [or_iff_right hnC, and_iff_right hfC]
    by_cases heC : e ∈ C
    · rw [iff_true_intro heC, not_true, false_and, or_false]
      have hC := (parallelExtend_parallel he f).circuit_of_ne hef
      exact ⟨fun h ↦ (hC.eq_of_subset_circuit h (pair_subset heC hfC)).symm, fun h ↦ by rwa [h]⟩
    have hfC' : f ∉ i '' C := by simpa [hi_def]
    rw [or_iff_right (show C ≠ {e,f} by rintro rfl; exact heC (Or.inl rfl)), and_iff_right heC,
      i.on_circuit_iff, circuit_iff_delete_of_disjoint (disjoint_singleton_right.2 hfC'),
      ← deleteElem, parallelExtend_delete_eq _ hf, parallel_swap_apply, parallelExtend_ground,
      PartialEquiv.restr_coe, Equiv.toPartialEquiv_apply, Equiv.swap_comm,
      Equiv.swap_image_eq_exchange hfC heC]

  refine iff_of_false (fun hC ↦ hnss hC.subset_ground) ?_
  rw [parallelExtend_ground] at hnss
  rintro (hC | rfl | hC)
  · exact hnss (hC.subset_ground.trans (subset_insert _ _))
  · exact hnss (pair_subset (mem_insert_of_mem _ he.mem_ground) (mem_insert _ _))
  have hss := hC.2.2.subset_ground
  rw [insert_subset_iff, diff_subset_iff, singleton_union] at hss
  exact hnss hss.2

instance parallelExtend_finite (M : Matroid α) [M.Finite] (e f : α) :
    (M.parallelExtend e f).Finite :=
  ⟨M.ground_finite.insert f⟩

instance parallelExtend_finiteRk (M : Matroid α) [FiniteRk M] (e f : α) :
    (M.parallelExtend e f).FiniteRk := by
  obtain ⟨B, hB⟩ := (M.parallelExtend e f).exists_base
  have hB' : M.Indep (B \ {f}) := by
    rw [indep_iff_delete_of_disjoint (disjoint_sdiff_left (t := B) (s := {f})),
      ← deleteElem, ← parallelExtend_delete_eq' M e f, deleteElem, delete_indep_iff,
      and_iff_left disjoint_sdiff_left]
    exact hB.indep.subset <| diff_subset _ _
  exact ⟨⟨_, hB, (hB'.finite.insert f).subset <| by simp⟩⟩

instance parallelExtend_finitary (M : Matroid α) [Finitary M] (e f : α) :
    (M.parallelExtend e f).Finitary := by
  obtain (rfl | hef) := eq_or_ne e f
  · rw [parallelExtend_self]; infer_instance
  obtain (he | he) := em' (M.Nonloop e)
  · rw [parallelExtend_not_nonloop he]
    infer_instance
  rw [parallelExtend_eq_parallelExtend_delete _ hef, finitary_iff_forall_circuit_finite]
  intro C
  rw [parallelExtend_circuit_iff, deleteElem, delete_circuit_iff, disjoint_singleton_right,
    delete_circuit_iff]
  · rintro (h | rfl | h)
    · exact h.1.finite
    · exact toFinite {e, f}
    refine (h.2.2.1.finite.insert f).subset ?_
    rw [insert_comm, insert_diff_singleton]
    exact (subset_insert _ _).trans (subset_insert _ _)
  · rwa [deleteElem, delete_nonloop_iff, and_iff_right he]
  exact fun h ↦ h.2 rfl

end Parallel

section Series

variable {α : Type*} [DecidableEq α] {M M' : Matroid α} {e f : α}

/-- Coextend `e` by `f` in series. Intended for use where `e` is a non-coloop and `f ∉ M.E`. -/
def seriesExtend (M : Matroid α) (e f : α) : Matroid α := (M✶.parallelExtend e f)✶

@[simp] theorem seriesExtend_dual (M : Matroid α) (e f : α) :
    (M.seriesExtend e f)✶ = M✶.parallelExtend e f := by
  rw [seriesExtend, dual_dual]

@[simp] theorem parallelExtend_dual (M : Matroid α) (e f : α) :
    (M.parallelExtend e f)✶ = M✶.seriesExtend e f := by
  rw [seriesExtend, dual_dual]

@[simp] theorem seriesExtend_ground (M : Matroid α) (e f : α) :
    (M.seriesExtend e f).E = insert f M.E := rfl

@[simp] theorem seriesExtend_self (M : Matroid α) (e : α) :
    M.seriesExtend e e = M.addColoop e := by
  rw [seriesExtend, parallelExtend_self, addColoop]

theorem seriesExtend_coloop (he : M.Coloop e) (f : α) :
    M.seriesExtend e f = (M ⧸ f).addColoop f := by
  rw [seriesExtend, parallelExtend_not_nonloop, addColoop, deleteElem, contract_elem,
    contract_dual_eq_dual_delete]
  simp [Nonloop, dual_loop_iff_coloop, he]

theorem seriesExtend_not_mem_ground (he : e ∉ M.E) (f : α) :
    M.seriesExtend e f = (M ⧸ f).addColoop f := by
  rw [seriesExtend, parallelExtend_not_nonloop, addColoop, contract_elem, deleteElem,
    contract_dual_eq_dual_delete]
  simp [Nonloop, he]

theorem seriesExtend_eq_seriesExtend_contract (M : Matroid α) {e f : α} (hef : e ≠ f):
    M.seriesExtend e f = (M ⧸ f).seriesExtend e f := by
  rw [seriesExtend, parallelExtend_eq_parallelExtend_delete _ hef, seriesExtend]
  simp only [deleteElem, contract_elem, contract_dual_eq_dual_delete]

theorem seriesExtend_contract_eq' (M : Matroid α) (e f : α) :
    ((M.seriesExtend e f) ⧸ f) = M ⧸ f := by
  rw [seriesExtend, contract_elem, ← delete_dual_eq_dual_contract, ← deleteElem,
    parallelExtend_delete_eq']
  simp

theorem seriesExtend_contract_eq (e : α) (hf : f ∉ M.E) : (M.seriesExtend e f ⧸ f) = M := by
  rw [seriesExtend, contract_elem, ← delete_dual_eq_dual_contract, ← deleteElem,
    parallelExtend_delete_eq _ (show f ∉ M✶.E from hf), dual_dual]

theorem seriesExtend_series (heE : e ∈ M.E) (he : ¬M.Coloop e) (f : α) :
    (M.seriesExtend e f).Series e f := by
  rw [Series, seriesExtend, dual_dual]
  apply parallelExtend_parallel
  rwa [Nonloop, dual_ground, and_iff_left heE, dual_loop_iff_coloop]

theorem eq_seriesExtend_iff (heE : e ∈ M.E) (he : ¬M.Coloop e) (hf : f ∉ M.E) :
    M' = M.seriesExtend e f ↔ M'.Series e f ∧ ((M' ⧸ f) = M) := by
  rw [seriesExtend, eq_dual_comm, eq_comm, eq_parallelExtend_iff _ (show f ∉ M✶.E from hf),
    deleteElem, ← contract_dual_eq_dual_delete, ← contract_elem, dual_inj, Series]
  rwa [Nonloop, and_iff_left (show e ∈ M✶.E from heE), dual_loop_iff_coloop]

instance seriesExtend_finite (M : Matroid α) [M.Finite] : (M.seriesExtend e f).Finite :=
  ⟨M.ground_finite.insert f⟩

end Series
