import Mathlib.Combinatorics.Matroid.Sum
import Matroid.Extension.Minor

set_option linter.style.longLine false

variable {α β : Type*} {e : α} {f : β} {M : Matroid α} {N : Matroid β} {I : Set (α ⊕ β)}

@[simp]
lemma Sum.preimage_inl_image_swap (X : Set (α ⊕ β)) :
    Sum.inl ⁻¹' (Sum.swap '' X) = Sum.inr ⁻¹' X := by
  grind

@[simp]
lemma Sum.preimage_inr_image_swap (X : Set (α ⊕ β)) :
    Sum.inr ⁻¹' (Sum.swap '' X) = Sum.inl ⁻¹' X := by
  grind

@[simp]
lemma Sum.image_inr_diff (X Y : Set β) (α : Type*) :
    Sum.inr (α := α) '' (X \ Y) = Sum.inr '' X \ Sum.inr '' Y :=
  Set.image_diff Sum.inr_injective ..

@[simp]
lemma Sum.image_inl_diff (X Y : Set α) (β : Type*) :
    Sum.inl (β := β) '' (X \ Y) = Sum.inl '' X \ Sum.inl '' Y :=
  Set.image_diff Sum.inl_injective ..


namespace Matroid

@[simp]
lemma sum_loops (M : Matroid α) (N : Matroid β) :
    (M.sum N).loops = .inl '' M.loops ∪ .inr '' N.loops := by
  rw [← closure_empty, sum_closure_eq]
  simp [closure_empty]

open ModularCut Set Sum


lemma IsLoop.contractElem_eq_deleteElem (h : M.IsLoop e) : M ／ {e} = M ＼ {e} :=
  contract_eq_delete_of_subset_loops <| by rwa [singleton_subset_iff]

lemma contractElem_indep_iff {M : Matroid α} {e : α} {I : Set α} :
    (M ／ {e}).Indep I ↔ M.Indep I ∧ e ∉ I ∧ (M.IsNonloop e → M.Indep (insert e I)) := by
  by_cases hnl : M.IsNonloop e
  · rw [hnl.contractElem_indep_iff, imp_iff_right hnl, iff_and_self]
    exact fun h ↦ h.2.subset <| subset_insert ..
  rw [← contract_inter_ground_eq, contract_eq_delete_of_subset_loops, delete_indep_iff,
    disjoint_right]
  · have : M.Indep (insert e I) → M.Indep I := fun h ↦ h.subset <| subset_insert ..
    have h' : M.Indep I → e ∈ I → e ∈ M.E := fun h heI ↦ h.subset_ground heI
    grind
  rintro e ⟨rfl, heE⟩
  rwa [← isLoop_iff, ← not_isNonloop_iff]

def twoSum (M : Matroid α) (N : Matroid β) (e : α) (f : β) : Matroid (α ⊕ β) :=
  let MN := M.sum N
  let L : Set (α ⊕ β) := {.inl e, .inr f}
  ((MN.projectBy <| ModularCut.principal MN L) ＼ L)

@[simp]
lemma twoSum_ground_eq (M : Matroid α) (N : Matroid β) (e : α) (f : β) :
    (M.twoSum N e f).E = (.inl '' (M.E \ {e})) ∪ (.inr '' (N.E \ {f})) := by
  simp only [twoSum, delete_ground, projectBy_ground, sum_ground, image_diff Sum.inl_injective,
    image_singleton, image_diff Sum.inr_injective]
  grind

lemma twoSum_indep_iff (M : Matroid α) (N : Matroid β) (he : M.IsNonloop e)
    (hf : N.IsNonloop f) (I : Set (α ⊕ β)) :
    (M.twoSum N e f).Indep I ↔ (M ＼ {e}).Indep (.inl ⁻¹' I) ∧ (N ＼ {f}).Indep (.inr ⁻¹' I) ∧
      (M.Indep (insert e (.inl ⁻¹' I)) ∨ N.Indep (insert f (.inr ⁻¹' I))) := by
  rw [twoSum, delete_indep_iff, projectBy_indep_iff_of_ne_top, sum_indep_iff,
    mem_principal_iff, and_iff_right (closure_isFlat ..), pair_subset_iff,
    Classical.not_and_iff_not_or_not]
  swap
  · simp [← closure_empty, sum_closure_eq, pair_subset_iff, show e ∉ M.closure ∅ from he.not_isLoop]
  by_cases heI : .inl e ∈ I
  · simp [heI]
  by_cases hfI : .inr f ∈ I
  · simp [hfI]
  simp [heI, hfI, and_assoc]
  intro hIl hIr
  have hsi : (M.sum N).Indep I := by simp [hIl, hIr]
  rw [hIr.notMem_closure_iff_of_notMem (by simpa), hIl.notMem_closure_iff_of_notMem (by simpa)]

lemma twoSum_eq_of_notMem (he : e ∉ M.E) (N : Matroid β) (f : β) :
    (M.twoSum N e f) = M.sum (N ＼ {f}) := by
  refine ext_indep ?_ fun I hI ↦ ?_
  · simp only [twoSum_ground_eq, Sum.image_inl_diff, image_singleton, Sum.image_inr_diff,
    sum_ground, delete_ground]
    grind
  have heI : .inl e ∉ I := notMem_subset hI <| by simp
  have hfI : .inr f ∉ I := notMem_subset hI <| by simp
  rw [twoSum, principal_eq_bot_iff.2 (by simp [pair_subset_iff, he]), projectBy_bot,
    delete_indep_iff, and_iff_left (by grind), sum_indep_iff, sum_indep_iff, delete_indep_iff,
    disjoint_singleton_right, mem_preimage, and_iff_left hfI]

lemma IsLoop.twoSum_eq_sum (he : M.IsLoop e) (N : Matroid β) (f : β) :
    (M.twoSum N e f) = (M ＼ {e}).sum (N ／ {f}) := by
  refine ext_indep ?_ fun I hI ↦ ?_
  · simp
  have heI : .inl e ∉ I := notMem_subset hI <| by simp
  have hfI : .inr f ∉ I := notMem_subset hI <| by simp
  rw [twoSum, delete_indep_iff, disjoint_insert_right, disjoint_singleton_right,
    and_iff_right heI, and_iff_left hfI, sum_indep_iff, deleteElem_indep_iff, mem_preimage,
    and_iff_left heI, contractElem_indep_iff, mem_preimage, and_iff_right hfI]
  obtain hfE | hfE := em' <| f ∈ N.E
  · rw [principal_eq_bot_iff.2 (by simp [pair_subset_iff, hfE]), projectBy_bot]
    simp [show ¬ N.IsNonloop f from fun hf ↦ hfE hf.mem_ground]
  obtain hfl | hfnl := N.isLoop_or_isNonloop f
  · rw [principal_eq_top_iff.2, projectBy_top]
    · simp [hfl.not_isNonloop]
    simp [pair_subset_iff, ← closure_empty, he.mem_closure, hfl.mem_closure]
  rw [projectBy_indep_iff_of_ne_top, mem_principal_iff, and_iff_right (closure_isFlat ..),
    pair_subset_iff]
  · simp [sum_indep_iff, he.mem_closure, hfnl, insert_indep_iff, hfI,  hfE, and_assoc]
  simp [Ne, principal_eq_top_iff, pair_subset_iff, ← closure_empty,
    show f ∉ N.closure ∅ from hfnl.not_isLoop]

lemma sum_comm (M : Matroid α) (N : Matroid β) :
    M.sum N = (N.sum M).mapEquiv (Equiv.sumComm ..) := by
  refine ext_indep ?_ fun I hI ↦ by simp [and_comm]
  simp [union_comm, image_union, image_image]

lemma twoSum_comm (M : Matroid α) (N : Matroid β) (e : α) (f : β) :
    M.twoSum N e f = (N.twoSum M f e).mapEquiv (Equiv.sumComm ..) := by
  refine ext_indep ?_ fun I hI ↦ ?_
  · simp only [twoSum_ground_eq, Sum.image_inl_diff, image_singleton, Sum.image_inr_diff,
      mapEquiv_ground_eq, image_union, image_diff (Equiv.injective _)]
    simp only [Equiv.sumComm_apply, image_image, Sum.swap_inl, Sum.swap_inr]
    grind
  have heI : .inl e ∉ I := notMem_subset hI <| by simp
  have hfI : .inr f ∉ I := notMem_subset hI <| by simp
  simp only [twoSum, delete_indep_iff, projectBy_indep_iff, sum_indep_iff, ne_eq,
    principal_eq_top_iff, sum_loops, pair_subset_iff, mem_union, mem_image, Sum.inl.injEq,
    exists_eq_right, reduceCtorEq, and_false, exists_false, or_false, Sum.inr.injEq, false_or,
     mem_principal_iff, isFlat_closure, inl_mem_sum_closure_iff, inr_mem_sum_closure_iff,
    mapEquiv_indep_iff, Equiv.sumComm_symm, Equiv.sumComm_apply, Sum.preimage_inl_image_swap,
    Sum.preimage_inr_image_swap]
  grind

lemma twoSum_isBase_iff (M : Matroid α) (N : Matroid β) (he : M.IsNonloop e) (hf : N.IsNonloop f)
    {B} : (M.twoSum N e f).IsBase B ↔
      ((M ＼ {e}).IsBase (.inl ⁻¹' B) ∧ (N ／ {f}).IsBase (.inr ⁻¹' B))
      ∨ ((M ／ {e}).IsBase (.inl ⁻¹' B) ∧ (N ＼ {f}).IsBase (.inr ⁻¹' B)) := by
  sorry

-- lemma twoSum_dual (M : Matroid α) (N : Matroid β) (he : e ∈ M.E) (hf : f ∈ N.E) :
--     (M.twoSum N e f)✶ = M✶.twoSum N✶ e f := by
--   _












  -- rw [twoSum, delete_indep_iff, projectBy_indep_iff_of_ne_top]
  -- sorry
  -- simp [pair_subset_iff, ← closure_empty]




private lemma inj_of_inter_eq_singleton {M N : Matroid α} (hMNe : M.E ∩ N.E = {e}) :
    InjOn (Sum.elim id id) (M.twoSum N e e).E := by
  rintro (x | x) hx (y | y) hy
  · simp
  · rintro rfl
    replace hy : x ∈ N.E ∧ x ≠ e := by simpa using hy
    replace hx : x ∈ M.E ∧ x ≠ e := by simpa using hx
    exact False.elim <| hx.2 <| hMNe.subset ⟨hx.1, hy.1⟩
  · rintro rfl
    replace hx : x ∈ N.E ∧ x ≠ e := by simpa using hx
    replace hy : x ∈ M.E ∧ x ≠ e := by simpa using hy
    exact False.elim <| hx.2 <| hMNe.subset ⟨hy.1, hx.1⟩
  simp

def twoSumAt (M N : Matroid α) (hMNe : M.E ∩ N.E = {e}) : Matroid α :=
  (M.twoSum N e e).map (Sum.elim id id) (inj_of_inter_eq_singleton hMNe)

@[simp]
lemma twoSumAt_ground (M N : Matroid α) (hMNe : M.E ∩ N.E = {e}) :
    (M.twoSumAt N hMNe).E = (M.E ∪ N.E) \ {e} := by
  rw [twoSumAt, map_ground, twoSum_ground_eq, image_diff Sum.inl_injective,
    image_diff Sum.inr_injective, image_union, image_diff_of_injOn (by simp [InjOn]),
    image_diff_of_injOn (by simp [InjOn])]
  · simp [image_image, union_diff_distrib]
  · grw [← hMNe, inter_subset_right]
  grw [← hMNe, inter_subset_left]

-- def twoSumAt_indep_iff (M N : Matroid α) (hMNe : M.E ∩ N.E = {e}) (he : M.IsNonloop e) :
--     Matroid α :=



    -- sum_indep_iff, ← union_singleton, preimage_union, ← image_singleton, preimage_union,
    -- preimage_image_eq _ Sum.inl_injective, union_singleton, ← union_singleton (s := I),
    -- preimage_eq_empty]


  --   and_assoc, delete_indep_iff, delete_indep_iff,
  --   disjoint_insert_right, disjoint_singleton_right, disjoint_singleton_right,
  --   disjoint_singleton_right, mem_preimage, mem_preimage,
  --   and_congr_right_iff, and_imp, and_iff_l]
  -- intro hIl hIr




  -- simp only [TwoSum, delete_indep_iff, projectBy_indep_iff_of_ne_top sorry, sum_indep_iff, ne_eq,
  --   ModularCut.mem_principal_iff, closure_isFlat, true_and]

-- def InternalTwoSumIndepMatroid (M N : Matroid α) (e : α) (hMN : M.E ∩ N.E = {e}) :
--     IndepMatroid α where
--   E := M.E ∪ N.E
--   Indep I := I ⊆ M.E ∪ N.E ∧ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E)
--   indep_empty := sorry
--   indep_subset := sorry
--   indep_aug := sorry
--   indep_maximal := sorry
--   subset_ground := sorry

-- def InternalTwoSum (M N : Matroid α) (e : α) (hMN : M.E ∩ N.E = {e}) : Matroid α :=
--   (InternalTwoSumIndepMatroid M N e hMN).matroid

-- @[simp] lemma internalTwoSum_indep_iff (M N : Matroid α) e hMN (I : Set α) :
--     (InternalTwoSum M N e hMN).Indep I ↔ I ⊆ M.E ∪ N.E ∧ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) := by
--   rfl

-- def ModularSum (M N : Matroid α) (A : Set α) (h : M.E ∩ N.E = A) (hAMN : M ↾ A = N ↾ A) :
--   Matroid α



-- ( ........  e)    g     (f ........ )

--         α       e  |      β        f  |   g
-- [  * * * * * *  1  |   0 0 0 0 0 0 0  |   1   ]
-- [  * * * * * *  3  |   0 0 0 0 0 0 0  |   3   ]
-- [  0 0 0 0 0 0  0  |   * * * * * * 3  |   3t  ]
-- [  0 0 0 0 0 0  0  |   * * * * * * 6  |   6t  ]
-- [  0 0 0 0 0 0  0  |   * * * * * * 8  |   8t  ]
