import Matroid.ForMathlib.SetPartition
import Matroid.ForMathlib.Other
import Matroid.Flat
import Matroid.Equiv

open Set Set.Notation

namespace Matroid

variable {α : Type*} {M N : Matroid α} {e f g : α} {I X P D : Set α}

section Parallel

/-- The partition of the nonloops of `M` into parallel classes. -/
def parallelClasses (M : Matroid α) : Partition {e | M.Nonloop e} :=
  (M.closure_flat ∅).covByPartition.congr M.setOf_nonloop_eq.symm

def Parallel (M : Matroid α) : α → α → Prop := M.parallelClasses.Rel

@[simp] lemma parallelClasses_rel_eq : M.parallelClasses.Rel = M.Parallel := rfl

lemma parallel_iff :
    M.Parallel e f ↔ M.Nonloop e ∧ M.Nonloop f ∧ M.closure {e} = M.closure {f} := by
  simp [Parallel, parallelClasses, and_comm (a := _ ∈ M.E), nonloop_iff_mem_compl_loops]

instance {M : Matroid α} : IsSymm α M.Parallel :=
  inferInstanceAs <| IsSymm α M.parallelClasses.Rel

instance {M : Matroid α} : IsTrans α M.Parallel :=
  inferInstanceAs <| IsTrans α M.parallelClasses.Rel

lemma Parallel.symm (h : M.Parallel e f) : M.Parallel f e :=
  Partition.Rel.symm h

lemma parallel_comm : M.Parallel e f ↔ M.Parallel f e :=
  Partition.rel_comm

lemma Parallel.trans (h : M.Parallel e f) (h' : M.Parallel f g) : M.Parallel e g :=
  Partition.Rel.trans h h'

lemma Parallel.closure_eq_closure (h : M.Parallel e f) : M.closure {e} = M.closure {f} :=
  (parallel_iff.1 h).2.2

lemma Parallel.nonloop_left (h : M.Parallel e f) : M.Nonloop e :=
  (parallel_iff.1 h).1

lemma Parallel.nonloop_right (h : M.Parallel e f) : M.Nonloop f :=
  h.symm.nonloop_left

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Parallel.mem_ground_left (h : M.Parallel e f) : e ∈ M.E :=
  h.nonloop_left.mem_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Parallel.mem_ground_right (h : M.Parallel e f) : f ∈ M.E :=
  h.nonloop_right.mem_ground

lemma Nonloop.parallel_iff_closure_eq_closure (he : M.Nonloop e) :
    M.Parallel e f ↔ M.closure {e} = M.closure {f} := by
  rw [Parallel, parallelClasses, Partition.rel_congr,
    (M.closure_flat ∅).rel_covByPartition_iff' ⟨he.mem_ground, he.not_loop⟩]; simp

lemma Parallel.mem_closure (h : M.Parallel e f) : e ∈ M.closure {f} := by
  rw [← h.closure_eq_closure]; exact mem_closure_of_mem' _ rfl

lemma Parallel.parallel_iff_left (h : M.Parallel e f) {x : α} :
    M.Parallel x e ↔ M.Parallel x f :=
  ⟨fun h' ↦ h'.trans h , fun h' ↦ h'.trans h.symm⟩

lemma Parallel.parallel_iff_right (h : M.Parallel e f) {x : α} :
    M.Parallel e x ↔ M.Parallel f x :=
  ⟨h.symm.trans, h.trans⟩

lemma setOf_parallel_eq_closure_diff_loops (M : Matroid α) (e : α) :
    {f | M.Parallel e f} = M.closure {e} \ M.closure ∅ := by
  by_cases he : M.Nonloop e
  · rw [Parallel, parallelClasses, Partition.rel_congr,
      Partition.setOf_rel_eq_partOf, (M.closure_flat ∅).partOf_covByPartition_eq,
      closure_insert_closure_eq_closure_insert, insert_emptyc_eq]
  rw [not_nonloop_iff_closure.1 he, diff_self, eq_empty_iff_forall_not_mem]
  exact fun f hf ↦ he (Parallel.nonloop_left hf)

lemma closure_eq_parallel_class_union_loops (M : Matroid α) (e : α) :
    M.closure {e} = {f | M.Parallel e f} ∪ M.closure ∅ := by
  rw [setOf_parallel_eq_closure_diff_loops, diff_union_self,
    union_eq_self_of_subset_right (M.closure_mono (empty_subset _))]

lemma Nonloop.parallel_self (h : M.Nonloop e) : M.Parallel e e :=
  (h.parallel_iff_closure_eq_closure).2 rfl

@[simp] lemma parallel_self_iff : M.Parallel e e ↔ M.Nonloop e :=
  ⟨Parallel.nonloop_left, Nonloop.parallel_self⟩

lemma Loop.not_parallel (h : M.Loop e) (f : α) : ¬ M.Parallel e f :=
  fun h' ↦ h'.nonloop_left.not_loop h

lemma Nonloop.parallel_iff_mem_closure (he : M.Nonloop e) : M.Parallel e f ↔ e ∈ M.closure {f} := by
  refine ⟨Parallel.mem_closure, fun h ↦ ?_⟩
  rw [closure_eq_parallel_class_union_loops, mem_union,  mem_setOf_eq, parallel_comm] at h
  exact h.elim id (fun h' ↦ (he.not_loop h').elim)

lemma Loopless.parallel_class_eq_closure (h : M.Loopless) (e : α) :
    {f | M.Parallel e f} = M.closure {e} := by
  rw [setOf_parallel_eq_closure_diff_loops, h.closure_empty, diff_empty]

lemma Parallel.dep_of_ne (h : M.Parallel e f) (hne : e ≠ f) : M.Dep {e,f} := by
  rw [pair_comm, ← h.nonloop_left.indep.mem_closure_iff_of_not_mem hne.symm]
  exact h.symm.mem_closure

lemma parallel_iff_circuit (hef : e ≠ f) : M.Parallel e f ↔ M.Circuit {e,f} := by
  refine ⟨fun h ↦ circuit_iff_dep_forall_diff_singleton_indep.2 ⟨h.dep_of_ne hef, ?_⟩, fun h ↦ ?_⟩
  · rintro x (rfl | rfl)
    · rw [pair_diff_left hef]; exact h.nonloop_right.indep
    · rw [pair_diff_right hef]; exact h.nonloop_left.indep
  rw [Nonloop.parallel_iff_mem_closure]
  · convert h.mem_closure_diff_singleton_of_mem (mem_insert _ _); rw [pair_diff_left hef]
  apply h.nonloop_of_mem_of_one_lt_card _ (mem_insert _ _)
  rw [encard_pair hef]
  norm_num

lemma Parallel.circuit_of_ne (hef : M.Parallel e f) (hne : e ≠ f) : M.Circuit {e,f} := by
  rwa [parallel_iff_circuit hne] at hef

lemma Nonloop.parallel_iff_dep (he : M.Nonloop e) (hf : M.Nonloop f) (hef : e ≠ f) :
    M.Parallel e f ↔ M.Dep {e,f} := by
  rw [← hf.indep.mem_closure_iff_of_not_mem hef, he.parallel_iff_mem_closure]

lemma Parallel.eq_of_indep (h : M.Parallel e f) (hi : M.Indep {e,f}) : e = f := by
  by_contra hef
  exact ((h.nonloop_left.parallel_iff_dep h.nonloop_right hef).1 h).not_indep hi

lemma parallel_iff_nonloop_nonloop_indep_imp_eq :
    M.Parallel e f ↔ M.Nonloop e ∧ M.Nonloop f ∧ (M.Indep {e,f} → e = f) := by
  refine ⟨fun h ↦ ⟨h.nonloop_left, h.nonloop_right, fun hi ↦ h.eq_of_indep hi⟩, fun h ↦ ?_⟩
  obtain (rfl | hne) := eq_or_ne e f
  · exact h.1.parallel_self
  rw [h.1.parallel_iff_dep h.2.1 hne, Dep, pair_subset_iff, and_iff_left h.2.1.mem_ground,
    and_iff_left h.1.mem_ground]
  exact fun hi ↦ hne (h.2.2 hi)

lemma Parallel.mem_closure_iff_mem_closure (h : M.Parallel e f) {X : Set α} :
    e ∈ M.closure X ↔ f ∈ M.closure X := by
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · exact mem_of_mem_of_subset h.symm.mem_closure
      (M.closure_subset_closure_of_subset_closure (by simpa))
  exact mem_of_mem_of_subset h.mem_closure (M.closure_subset_closure_of_subset_closure (by simpa))

lemma Parallel.loop_of_contract (hef : M.Parallel e f) (hne : e ≠ f) : (M ／ e).Loop f := by
  rw [loop_iff_mem_closure_empty, contract_elem, contract_loops_eq, mem_diff]
  exact ⟨hef.symm.mem_closure, hne.symm⟩

lemma restrict_parallel_iff {R : Set α} :
    (M ↾ R).Parallel e f ↔ M.Parallel e f ∧ e ∈ R ∧ f ∈ R := by
  simp only [parallel_iff_nonloop_nonloop_indep_imp_eq, restrict_nonloop_iff, restrict_indep_iff,
    pair_subset_iff, and_imp]
  aesop

lemma delete_parallel_iff {D : Set α} :
    (M ＼ D).Parallel e f ↔ M.Parallel e f ∧ e ∉ D ∧ f ∉ D := by
  rw [delete_eq_restrict, restrict_parallel_iff, and_congr_right_iff]
  intro h
  rw [mem_diff, and_iff_right h.mem_ground_left, mem_diff, and_iff_right h.mem_ground_right]

@[simp] lemma removeLoops_parallel_iff : M.removeLoops.Parallel e f ↔ M.Parallel e f := by
  rw [removeLoops_eq_restr, restrict_parallel_iff,
    and_iff_left_of_imp (fun h ↦ ⟨h.nonloop_left, h.nonloop_right⟩)]

lemma Parallel.mem_cocircuit_of_mem {K : Set α}  (hef : M.Parallel e f) (hK : M.Cocircuit K)
    (he : e ∈ K) : f ∈ K := by
  by_contra hf
  have hK' := (hK.compl_hyperplane).flat.closure
  have hfK := hK'.symm.subset ⟨hef.mem_ground_right, hf⟩
  rw [← hef.mem_closure_iff_mem_closure, hK'] at hfK
  exact hfK.2 he

-- @[simp] lemma comap_parallel_iff {β : Type*} {M : Matroid β} {f : α → β} {x y : α} :
--     (M.comap f).Parallel x y ↔ M.Parallel (f x) (f y) := by
--   simp [parallel_iff]

end Parallel

section Parallel'

/-- Two elements are `Parallel'` if they are either both loops or are `Parallel` nonloops.
(Sometimes allowing loops is more convenient.) -/
def Parallel' (M : Matroid α) (e f : α) : Prop := e ∈ M.E ∧ f ∈ M.E ∧ M.closure {e} = M.closure {f}

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Parallel'.mem_ground_left (h : M.Parallel' e f) : e ∈ M.E := h.1

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Parallel'.mem_ground_right (h : M.Parallel' e f) : f ∈ M.E := h.2.1

lemma Parallel'.closure_eq_closure (h : M.Parallel' e f) : M.closure {e} = M.closure {f} := h.2.2

lemma Parallel'.symm (h : M.Parallel' e f) : M.Parallel' f e :=
  ⟨h.mem_ground_right, h.mem_ground_left, h.closure_eq_closure.symm⟩

lemma parallel'_self (h : e ∈ M.E) : M.Parallel' e e :=
    ⟨h,h,rfl⟩

lemma Parallel'.trans (h : M.Parallel' e f) (h' : M.Parallel' f g) : M.Parallel' e g :=
  ⟨h.mem_ground_left, h'.mem_ground_right, h.closure_eq_closure.trans h'.closure_eq_closure⟩

lemma Parallel'.parallel_of_nonloop (h : M.Parallel' e f) (he : M.Nonloop e) :
    M.Parallel e f := by
  rwa [Nonloop.parallel_iff_closure_eq_closure, h.closure_eq_closure]

lemma Parallel.parallel' (h : M.Parallel e f) : M.Parallel' e f :=
  ⟨h.mem_ground_left, h.mem_ground_right, h.closure_eq_closure⟩

lemma Parallel'.parallel_iff (h : M.Parallel' e f) : M.Parallel e f ↔ M.Nonloop e :=
  ⟨fun h' ↦ h'.nonloop_left, h.parallel_of_nonloop⟩

lemma Parallel'.loop_of_loop (h : M.Parallel' e f) (he : M.Loop e) : M.Loop f := by
  have h' := h.closure_eq_closure
  rw [he.closure, eq_comm] at h'
  rwa [loop_iff_closure_eq_closure_empty h.mem_ground_right]

lemma Parallel'.loop_or_parallel (h : M.Parallel' e f) :
    (M.Loop e ∧ M.Loop f) ∨ M.Parallel e f := by
  obtain (he | he) := M.loop_or_nonloop e
  · exact .inl ⟨he, h.loop_of_loop he⟩
  exact .inr <| h.parallel_of_nonloop he

lemma parallel'_iff_loops_or_parallel :
    M.Parallel' e f ↔ (M.Loop e ∧ M.Loop f) ∨ M.Parallel e f := by
  refine ⟨Parallel'.loop_or_parallel, ?_⟩
  rintro (⟨he, hf⟩ | hef)
  · rw [Matroid.Parallel', he.closure, hf.closure]
    simp [he.mem_ground, hf.mem_ground]
  exact hef.parallel'

lemma parallel'_iff_closure_eq_closure (e f : α) (he : e ∈ M.E := by aesop_mat)
    (hf : f ∈ M.E := by aesop_mat) : M.Parallel' e f ↔ M.closure {e} = M.closure {f} := by
  rw [Matroid.Parallel', and_iff_right he, and_iff_right hf]

lemma Parallel'.mem_closure (h : M.Parallel' e f) : e ∈ M.closure {f} := by
  rw [← h.closure_eq_closure]
  apply mem_closure_self _ _ h.mem_ground_left

lemma Parallel'.eq_of_indep (h : M.Parallel' e f) (hef : M.Indep {e,f}) : e = f :=
  (h.parallel_of_nonloop <| hef.nonloop_of_mem (.inl rfl)).eq_of_indep hef

@[simp] lemma parallel'_iff_parallel [Loopless M] : M.Parallel' e f ↔ M.Parallel e f := by
  rw [parallel'_iff_loops_or_parallel, or_iff_right (fun h ↦ M.not_loop e h.1)]

lemma Parallel'.mem_closure_iff_mem_closure (h : M.Parallel' e f) {X : Set α} :
    e ∈ M.closure X ↔ f ∈ M.closure X := by
  obtain (⟨he, hf⟩ | h) := h.loop_or_parallel
  · simp [he.mem_closure, hf.mem_closure]
  exact h.mem_closure_iff_mem_closure

end Parallel'

section Iso

/-
We show if `φ` is a function with `Parallel' e (φ e)` for all `e`,
then `φ` determines various matroid isomorphisms.
There are a few different contexts, depending on whether `φ` is defined on all of `α` or
only on a subtype, and whether or not `φ` is an equivalence.
-/

lemma closure_range_of_forall_parallel'_subtype {X : Set α} (φ : X → α)
    (h_para : ∀ e : X, M.Parallel' e (φ e)) : M.closure (range φ) = M.closure X := by
  simpa using M.closure_iUnion_congr (fun e ↦ {φ e}) (fun e ↦ {e.1})
    (fun e ↦ (h_para e).closure_eq_closure.symm)

lemma closure_image_of_forall_parallel'_subtype {X : Set α} (φ : X → α)
    (h_para : ∀ e : X, M.Parallel' e (φ e)) (Y : Set X) : M.closure (φ '' Y) = M.closure Y := by
  convert M.closure_biUnion_congr (fun e : X ↦ {φ e}) (fun e ↦ {e.1}) Y
    (fun e _ ↦ (h_para e).closure_eq_closure.symm) <;> aesop

lemma closure_image_of_forall_parallel' (φ : α → α) (h_para : ∀ e, M.Parallel' e (φ e))
    (X : Set α) : M.closure (φ '' X) = M.closure X := by
  rw [← closure_range_of_forall_parallel'_subtype (fun x : X ↦ φ x) (fun x ↦ h_para x),
    image_eq_range]

/-- If `φ : X ≃ Y` is such that `e` and `φ e` are always `Parallel'`, then `φ` determines a
matroid isomorphism between `M ↾ X` and `M ↾ Y`. -/
def isoOfMapParallelRestr {X Y : Set α} (φ : X ≃ Y) (h_para : ∀ e : X,  M.Parallel' e (φ e)) :
    (M ↾ X) ≂ (M ↾ Y) :=
  isoOfForallImageclosure φ
  ( by
      have hXE : X ⊆ M.E := fun x hx ↦ (h_para ⟨x,hx⟩).mem_ground_left
      simp only [restrict_ground_eq, restrict_closure_eq', image_val_inter_self_left_eq_coe,
        preimage_union, preimage_inter, Subtype.coe_preimage_self, inter_univ, preimage_diff]
      intro Z
      rw [image_image, closure_image_of_forall_parallel'_subtype _ h_para, image_image]
      have hYE : Y ⊆ M.E := fun y hy ↦ by simpa using (h_para (φ.symm ⟨y,hy⟩)).mem_ground_right

      simp [preimage_val_eq_univ_of_subset hXE, diff_eq_empty.2 hYE]
      ext x
      simp only [mem_inter_iff, mem_image, mem_preimage, Subtype.exists, exists_and_left]
      refine ⟨fun ⟨hx,hxY⟩  ↦ ⟨φ.symm ⟨_,hxY⟩, ?_⟩, ?_⟩
      · suffices (φ.symm ⟨x, hxY⟩).1 ∈ M.closure Z by simpa
        exact mem_of_mem_of_subset (by simpa using (h_para (φ.symm ⟨x,hxY⟩)).mem_closure) <|
          M.closure_subset_closure_of_subset_closure (by simpa)
      rintro ⟨x, hx', hx, rfl⟩
      simp only [Subtype.coe_prop, and_true]
      exact mem_of_mem_of_subset (h_para ⟨x,hx⟩).symm.mem_closure <|
          M.closure_subset_closure_of_subset_closure (by simpa) )

/-- If `φ` is a permutation of `M.E` that maps each element to something `Parallel'`, then
`φ` determines an automorphism of `M`. -/
def isoOfMapParallel (φ : M.E ≃ M.E) (h_para : ∀ (e : M.E), M.Parallel' e (φ e)) : M ≂ M :=
  let ψ := (Iso.ofEq <| M.restrict_ground_eq_self)
  ψ.symm.trans (Iso.trans (isoOfMapParallelRestr φ h_para) ψ)

/-- If `φ : α → α` restricts to a permutation of `M.E` and maps each element to something
`Parallel'`, it induces an automorphism of `M`. -/
@[simps] noncomputable def isoOfMapParallelBijOn {φ : α → α} (hφ : BijOn φ M.E M.E)
    (h_para : ∀ e ∈ M.E, M.Parallel' e (φ e)) : M ≂ M where
  toEquiv := hφ.equiv
  indep_image_iff' I := (isoOfMapParallel hφ.equiv (by simpa [BijOn.equiv])).indep_image_iff

@[simp] lemma isoOfMapParallelBijOn_apply {φ} (hφ : BijOn φ M.E M.E)
    (h_para : ∀ e ∈ M.E, M.Parallel' e (φ e)) (x : M.E) :
    isoOfMapParallelBijOn hφ h_para x = ⟨φ x, (h_para x.1 x.2).mem_ground_right⟩ := rfl

@[simp] lemma isoOfMapParallelBijOn_apply_image {φ} (hφ : BijOn φ M.E M.E)
    (h_para : ∀ e ∈ M.E, M.Parallel' e (φ e)) (X : Set M.E) :
    isoOfMapParallelBijOn hφ h_para '' X = φ '' X := by
  suffices ∀ (x y : α) (h : y ∈ M.E), ⟨y, h⟩ ∈ X → φ y = x → x ∈ M.E by simpa [Set.ext_iff]
  rintro x y h - rfl
  exact (h_para y h).mem_ground_right



end Iso

section Swap




    -- ext x
    -- obtain (rfl | he) := eq_or_ne x e
    -- · simp [h.mem_ground_right, h.mem_ground_left]
    -- obtain (rfl | he) := eq_or_ne x f
    -- ·


/-- Swapping two `Parallel'` matroid elements gives an automorphism -/
@[simps!] noncomputable def isoOfSwapParallel [DecidableEq α] (h_para : M.Parallel' e f) : M ≂ M :=
  isoOfMapParallelBijOn (φ := Equiv.swap e f)
    (Equiv.swap_bijOn_self (iff_of_true h_para.mem_ground_left h_para.mem_ground_right))
    (by
      intro x hx
      obtain (rfl | he) := eq_or_ne x e; simpa
      obtain (rfl | hf) := eq_or_ne x f; simpa using h_para.symm
      rw [Equiv.swap_apply_of_ne_of_ne he hf]
      exact M.parallel'_self hx )

@[simp] lemma isoOfSwapParallel_apply [DecidableEq α] (h_para : M.Parallel' e f) (x : M.E) :
    isoOfSwapParallel h_para x = ⟨Equiv.swap e f x, (isoOfSwapParallel h_para x).2⟩ := rfl

@[simp] lemma isoOfSwapParallel_apply_image [DecidableEq α] (h_para : M.Parallel' e f)
    (X : Set M.E) : isoOfSwapParallel h_para '' X = Equiv.swap e f '' X := by
  rw [isoOfSwapParallel, isoOfMapParallelBijOn_apply_image]

lemma Indep.parallel'_substitute (hI : M.Indep I) (h_para : M.Parallel' e f)
    (heI : e ∈ I) : M.Indep (insert f (I \ {e})) := by
  classical
  convert (isoOfSwapParallel h_para).image_indep (I := M.E ↓∩ I)
    (by rwa [Subset.image_val_preimage_val_eq hI.subset_ground])
  simp only [isoOfSwapParallel_apply_image, Subtype.image_preimage_coe,
    inter_eq_self_of_subset_right hI.subset_ground]
  by_cases hfI : f ∈ I
  · obtain (rfl : e = f) := h_para.eq_of_indep (hI.subset (pair_subset heI hfI))
    simpa
  rw [(Equiv.swap_bijOn_exchange heI hfI).image_eq]

lemma Parallel'.indep_substitute_iff (h_para : M.Parallel' e f) (he : e ∈ I) (hf : f ∉ I) :
    M.Indep I ↔ M.Indep (insert f (I \ {e})) := by
  refine ⟨fun hI ↦ hI.parallel'_substitute h_para he, fun hI ↦ ?_⟩
  convert hI.parallel'_substitute h_para.symm (mem_insert _ _)
  have hef : e ≠ f := by rintro rfl; exact hf he
  simp [insert_diff_singleton_comm hef, insert_eq_of_mem he, diff_singleton_eq_self hf]

lemma Parallel'.eq_mapEquiv_swap (h : M.Parallel' e f) [DecidableEq α] :
    M.mapEquiv (Equiv.swap e f) = M := by
  have hrw := Equiv.swap_image_eq_self
      (show e ∈ M.E ↔ f ∈ M.E by simp [h.mem_ground_left, h.mem_ground_right])
  simp only [ext_iff_indep, mapEquiv_ground_eq, hrw, mapEquiv_indep_iff,
    Equiv.symm_swap, true_and]
  rintro I -
  by_cases heI : e ∈ I
  · by_cases hfI : f ∈ I
    · rw [Equiv.swap_image_eq_self (by simp [heI, hfI])]
    rw [Equiv.swap_image_eq_exchange heI hfI, ← h.indep_substitute_iff heI hfI]
  by_cases hfI : f ∈ I
  · rw [Equiv.swap_comm, Equiv.swap_image_eq_exchange hfI heI,
      ← h.symm.indep_substitute_iff hfI heI]
  rw [Equiv.swap_image_eq_self (by simp [hfI, heI])]

end Swap

section Subtype

variable {φ : I → α}

lemma indep_iff_range_indep_of_paraMap {φ : I → α} (hφ : φ.Injective)
    (h_para : ∀ e : I, M.Parallel' e (φ e)) : M.Indep I ↔ M.Indep (range φ) := by
  set ψ := Equiv.ofInjective _ hφ
  convert Iso.indep_image_iff (I := univ) <|
    (isoOfMapParallelRestr ψ (by simpa only [Equiv.ofInjective_apply, ψ] using h_para)) using 1
  · simp [Subset.rfl]
  simp only [restrict_ground_eq, image_univ, restrict_indep_iff, image_subset_iff,
    Subtype.coe_preimage_self, subset_univ, and_true]
  simp_rw [← image_univ, image_image, image_univ]
  rfl

end Subtype

section Function

lemma Indep.paraMap_injective (hI : M.Indep I) (φ : I → α)
    (h_para : ∀ e : I, M.Parallel' e (φ e)) : φ.Injective := by
  intro x y hxy
  have hx := h_para x
  rw [hxy] at hx
  exact Subtype.val_inj.1
    ((hx.trans (h_para y).symm).eq_of_indep (hI.subset (pair_subset x.2 y.2)))

lemma Indep.indep_range_paraMap (hI : M.Indep I) (φ : I → α)
    (h_para : ∀ e : I, M.Parallel' e (φ e)) : M.Indep (range φ) := by
  rwa [← indep_iff_range_indep_of_paraMap (hI.paraMap_injective φ h_para) h_para]

lemma Indep.image_paraMap {φ : α → α} (hI : M.Indep I) (h_para : ∀ e ∈ I, M.Parallel' e (φ e)) :
    M.Indep (φ '' I) := by
  convert hI.indep_range_paraMap (fun e ↦ φ e) (by simpa); simp [Set.ext_iff]

lemma Indep.of_image_paraMap {φ : α → α} (hI : M.Indep (φ '' I)) (hφ : InjOn φ I)
    (h_para : ∀ e ∈ I, M.Parallel' e (φ e)) : M.Indep I := by
  rwa [indep_iff_range_indep_of_paraMap hφ.injective (by simpa), range_restrict]

lemma indep_image_iff_of_injOn_paraMap {φ : α → α} (hφ : InjOn φ I)
    (h : ∀ e ∈ I, M.Parallel' e (φ e)) : M.Indep (φ '' I) ↔ M.Indep I :=
  ⟨fun hI ↦ hI.of_image_paraMap hφ h, fun hi ↦ hi.image_paraMap h⟩

end Function

section ParallelClass

lemma mem_parallelClasses_iff_eq_closure_diff_loops {P : Set α} :
    P ∈ M.parallelClasses ↔ ∃ e, M.Nonloop e ∧ P = M.closure {e} \ M.closure ∅ := by
  simp only [parallelClasses, Partition.mem_congr_iff, Flat.mem_covByPartition_iff,
    loops_covBy_iff, point_iff_exists_eq_closure_nonloop]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  rintro ⟨e, he, rfl⟩
  exact ⟨_, ⟨e, he, rfl⟩,rfl⟩

lemma mem_parallelClasses_iff {P : Set α} :
    P ∈ M.parallelClasses ↔ ∃ e, M.Nonloop e ∧ P = {f | M.Parallel e f} := by
  simp_rw [mem_parallelClasses_iff_eq_closure_diff_loops, setOf_parallel_eq_closure_diff_loops]

@[simp] lemma parallelClasses_partOf_eq (M : Matroid α) (e : α) :
    M.parallelClasses.partOf e = {f | M.Parallel e f} :=
  (M.parallelClasses.setOf_rel_eq_partOf e).symm

/-- Parallel classes are equivalent to points. -/
@[simps] def parallelPointEquiv (M : Matroid α) : ↑(M.parallelClasses) ≃ {P // M.Point P} where
  toFun P := ⟨P ∪ M.closure ∅, by
    obtain ⟨e, he, h⟩ := mem_parallelClasses_iff_eq_closure_diff_loops.1 P.prop
    rw [h, diff_union_self, union_eq_self_of_subset_right
      (M.closure_subset_closure (empty_subset _))]
    exact he.closure_point ⟩
  invFun P := ⟨P \ M.closure ∅, by
    obtain ⟨e, he, heP⟩ := P.prop.exists_eq_closure_nonloop
    rw [mem_parallelClasses_iff_eq_closure_diff_loops]
    exact ⟨e, he, by rw [heP]⟩⟩
  left_inv := by
    rintro ⟨P, hP⟩
    obtain ⟨e, -, rfl⟩ := mem_parallelClasses_iff_eq_closure_diff_loops.1 hP
    simp
  right_inv := by
    rintro ⟨P, hP⟩
    obtain ⟨e, -, rfl⟩ := hP.exists_eq_closure_nonloop
    simp

end ParallelClass

section Series

section Series

def Series (M : Matroid α) (e f : α) : Prop := M✶.Parallel e f

-- API TODO, but all will follow easily from duality.


end Series
