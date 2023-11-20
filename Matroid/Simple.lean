import Matroid.Constructions.Basic
import Matroid.ForMathlib.PartitionOf
import Matroid.ForMathlib.Other
import Matroid.Flat
open Set

namespace Matroid

variable {α : Type*} {M : Matroid α}

section Parallel

@[pp_dot] def Parallel (M : Matroid α) (e f : α) : Prop :=
  M.Nonloop e ∧ M.cl {e} = M.cl {f}

theorem Parallel.nonloop_left (h : M.Parallel e f) : M.Nonloop e :=
  h.1

theorem Parallel.cl_eq_cl (h : M.Parallel e f) : M.cl {e} = M.cl {f} :=
  h.2

@[aesop unsafe 20% (rule_sets [Matroid])]
theorem Parallel.mem_ground_left (h : M.Parallel e f) : e ∈ M.E :=
  h.1.mem_ground

@[aesop unsafe 20% (rule_sets [Matroid])]
theorem Parallel.mem_ground_right (h : M.Parallel e f) : f ∈ M.E := by
  by_contra hf
  have hcl := h.2.symm
  rw [cl_eq_cl_inter_ground, singleton_inter_eq_empty.2 hf] at hcl
  exact h.nonloop_left.not_loop (hcl.symm.subset (mem_cl_self _ _))

theorem Parallel.nonloop_right (h : M.Parallel e f) : M.Nonloop f := by
  rw [←not_loop_iff]
  refine fun hf ↦ h.nonloop_left.not_loop ?_
  rw [loop_iff_cl_eq_cl_empty, h.cl_eq_cl, hf.cl]

theorem Nonloop.parallel_iff_cl_eq_cl (he : M.Nonloop e) :
    M.Parallel e f ↔ M.cl {e} = M.cl {f} := by
  refine' ⟨fun h ↦ h.2, fun h ↦ ⟨he, h⟩⟩

theorem Parallel.mem_cl (h : M.Parallel e f) : e ∈ M.cl {f} := by
  rw [←h.cl_eq_cl]; exact mem_cl_of_mem' _ rfl

theorem Parallel.symm (h : M.Parallel e f) : M.Parallel f e :=
  ⟨h.nonloop_right, h.cl_eq_cl.symm⟩

theorem parallel_comm : M.Parallel e f ↔ M.Parallel f e :=
  ⟨Parallel.symm, Parallel.symm⟩

theorem Parallel.trans (h : M.Parallel e f) (h' : M.Parallel f g) : M.Parallel e g :=
  ⟨h.nonloop_left, h.cl_eq_cl.trans h'.cl_eq_cl⟩

instance {M : Matroid α} : IsSymm α M.Parallel :=
  ⟨ fun _ _ ↦ Parallel.symm ⟩

instance {M : Matroid α} : IsTrans α M.Parallel :=
  ⟨ fun _ _ _ ↦ Parallel.trans ⟩

theorem Nonloop.parallel_self (h : M.Nonloop e) : M.Parallel e e :=
  ⟨h, rfl⟩

@[simp] theorem parallel_self_iff : M.Parallel e e ↔ M.Nonloop e := by
  simp [Parallel]

theorem Loop.not_parallel (h : M.Loop e) (f : α) : ¬ M.Parallel e f :=
  fun h' ↦ h'.nonloop_left.not_loop h

@[simp] theorem parallel_class_eq_cl_diff_loops (M : Matroid α) (e : α) :
    {f | M.Parallel e f} = M.cl {e} \ M.cl ∅ := by
  ext f
  rw [mem_setOf_eq, parallel_comm (e := e), Parallel]
  refine' ⟨fun ⟨hf, hcl⟩ ↦ ⟨_,hf.not_loop⟩, fun h ↦ ⟨⟨h.2, (M.cl_subset_ground _) h.1⟩,?_⟩⟩
  · rw [←hcl]; exact mem_cl_self _ _ hf.mem_ground
  rw [←insert_emptyc_eq, eq_comm, ←insert_emptyc_eq, eq_comm]
  apply cl_insert_eq_cl_insert_of_mem
  simpa using h

theorem cl_eq_parallel_class_union_loops (M : Matroid α) (e : α) :
    M.cl {e} = {f | M.Parallel e f} ∪ M.cl ∅ := by
  rw [parallel_class_eq_cl_diff_loops, diff_union_self,
    union_eq_self_of_subset_right (M.cl_mono (empty_subset _))]

theorem Nonloop.parallel_iff_mem_cl (he : M.Nonloop e) : M.Parallel e f ↔ e ∈ M.cl {f} := by
  refine ⟨Parallel.mem_cl, fun h ↦ ?_⟩
  rw [cl_eq_parallel_class_union_loops, mem_union,  mem_setOf_eq, parallel_comm] at h
  exact h.elim id (fun h' ↦ (he.not_loop h').elim)

theorem Loopless.parallel_class_eq_cl (h : M.Loopless) (e : α) :
    {f | M.Parallel e f} = M.cl {e} := by
  rw [parallel_class_eq_cl_diff_loops, h.cl_empty, diff_empty]

theorem Parallel.dep_of_ne (h : M.Parallel e f) (hne : e ≠ f) : M.Dep {e,f} := by
  rw [pair_comm, ←h.nonloop_left.indep.mem_cl_iff_of_not_mem hne.symm]; exact h.symm.mem_cl

theorem parallel_iff_circuit (hef : e ≠ f) : M.Parallel e f ↔ M.Circuit {e,f} := by
  refine' ⟨fun h ↦ circuit_iff_dep_forall_diff_singleton_indep.2 ⟨h.dep_of_ne hef,_⟩, fun h ↦ _⟩
  · rintro x (rfl | rfl)
    · rw [pair_diff_left hef]; exact h.nonloop_right.indep
    · rw [pair_diff_right hef]; exact h.nonloop_left.indep
  rw [Nonloop.parallel_iff_mem_cl]
  · convert h.mem_cl_diff_singleton_of_mem (mem_insert _ _); rw [pair_diff_left hef]
  apply h.nonloop_of_mem_of_one_lt_card _ (mem_insert _ _)
  rw [encard_pair hef]
  norm_num

theorem Nonloop.parallel_iff_dep (he : M.Nonloop e) (hf : M.Nonloop f) (hef : e ≠ f) :
    M.Parallel e f ↔ M.Dep {e,f} := by
  rw [←hf.indep.mem_cl_iff_of_not_mem hef, he.parallel_iff_mem_cl]

theorem Indep.parallel_substitute (hI : M.Indep I) (h_para : M.Parallel e f) (hI_e : e ∈ I) :
    M.Indep (insert f (I \ {e})) := by
  obtain (rfl | hef) := eq_or_ne e f
  · rwa [insert_diff_singleton, insert_eq_of_mem hI_e]
  rw [indep_iff_forall_subset_not_circuit']
  refine ⟨fun C C_sub C_circ ↦ ?_, ?_⟩
  · have e_notin_C : e ∉ C := fun e_in_C ↦ (mem_of_mem_insert_of_ne (C_sub e_in_C) hef).2 rfl
    have C_ne_ef : C ≠ {e, f}
    · intro h_f
      rw [h_f] at e_notin_C
      exact e_notin_C (mem_insert e _)
    obtain ⟨C', C'_circ, C'_sub⟩ :=
      C_circ.elimination ((parallel_iff_circuit hef).1 h_para) C_ne_ef f
    refine C'_circ.dep.not_indep (hI.subset <| C'_sub.trans ?_)
    simp only [mem_singleton_iff, union_insert, union_singleton, mem_insert_iff, true_or, or_true,
      not_true, diff_subset_iff, singleton_union, insert_subset_iff, hI_e, true_and]
    refine C_sub.trans (insert_subset_insert (diff_subset _ _))
  exact insert_subset h_para.mem_ground_right <| (diff_subset _ _).trans hI.subset_ground

theorem Parallel.indep_substitute_iff (h_para : M.Parallel e f) (he : e ∈ I) (hf : f ∉ I) :
    M.Indep I ↔ M.Indep (insert f (I \ {e})) := by
  refine ⟨fun hI ↦ hI.parallel_substitute h_para he, fun hI ↦ ?_⟩
  convert hI.parallel_substitute h_para.symm (mem_insert _ _)
  have hef : e ≠ f := by rintro rfl; exact hf he
  simp [insert_diff_singleton_comm hef, insert_eq_of_mem he, diff_singleton_eq_self hf]

/-- Swapping two parallel elements gives an automorphism -/
def parallelSwap [DecidableEq α] {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : Iso M M :=
  iso_of_forall_indep' ((Equiv.swap e f).toLocalEquiv.restr M.E) (by simp)
  ( by
    simp only [LocalEquiv.restr_target, Equiv.toLocalEquiv_target, Equiv.toLocalEquiv_symm_apply,
      Equiv.symm_swap, univ_inter, preimage_equiv_eq_image_symm]
    exact Equiv.swap_image_eq_self (iff_of_true h_para.mem_ground_left h_para.mem_ground_right))
  ( by
    simp only [LocalEquiv.restr_coe, Equiv.toLocalEquiv_apply]
    intro I _
    by_cases hef : e ∈ I ↔ f ∈ I
    · rw [Equiv.swap_image_eq_self hef]
    rw [not_iff, iff_iff_and_or_not_and_not, not_not] at hef
    obtain (hef | hef) := hef
    · rw [Equiv.swap_comm, Equiv.swap_image_eq_exchange hef.2 hef.1,
        h_para.symm.indep_substitute_iff hef.2 hef.1]
    rw [Equiv.swap_image_eq_exchange hef.1 hef.2, h_para.indep_substitute_iff hef.1 hef.2] )

@[simp] theorem parallel_swap_apply [DecidableEq α] (h_para : M.Parallel e f) :
    (parallelSwap h_para).toLocalEquiv = (Equiv.swap e f).toLocalEquiv.restr M.E := rfl


end Parallel

section Series

@[pp_dot] def Series (M : Matroid α) (e f : α) : Prop := M﹡.Parallel e f

-- API TODO


end Series

section ParallelClass

open PSetoid

theorem mem_parallel_classes_iff_eq_cl :
    P ∈ classes M.Parallel ↔ ∃ e, M.Nonloop e ∧ P = M.cl {e} \ M.cl ∅ := by
  simp [mem_classes_iff]

@[simp] theorem mem_parallel_classes_iff :
    P ∈ classes M.Parallel ↔ ∃ e, M.Nonloop e ∧ P = {f | M.Parallel e f} := by
  simp only [mem_classes_iff, parallel_self_iff, parallel_class_eq_cl_diff_loops]

/-- Parallel classes correspond to points -/
def parallel_point_equiv (M : Matroid α) : classes M.Parallel ≃ {P // M.Point P} where
  toFun := fun X ↦ ⟨X ∪ M.cl ∅, by
    obtain ⟨e, he, h⟩ := mem_parallel_classes_iff_eq_cl.1 X.prop
    rw [h, diff_union_self, cl_union_cl_empty_eq, Point, er_cl_eq, and_iff_right (M.cl_flat _),
      he.er_eq] ⟩
  invFun := fun P ↦ ⟨P \ M.cl ∅, by
    obtain ⟨P, hP, hr⟩ := P
    rw [mem_parallel_classes_iff_eq_cl]
    obtain ⟨e, heP, he, hecl⟩ := (er_eq_one_iff hP.subset_ground).1 hr
    obtain rfl := hecl.antisymm (hP.cl_subset_of_subset (singleton_subset_iff.2 heP))
    exact ⟨e, he, rfl⟩ ⟩
  left_inv := by
    rintro ⟨P, hP⟩; obtain ⟨e, -, rfl⟩ := mem_parallel_classes_iff.1 hP; simp
  right_inv := by
    rintro ⟨P, hP, hPr⟩; simp [hP.cl_subset_of_subset (empty_subset P)]

@[simp] theorem parallel_point_equiv_apply (P : classes M.Parallel) :
    (M.parallel_point_equiv P : Set α) = (P : Set α) ∪ M.cl ∅ := rfl

@[simp] theorem parallel_point_equiv_apply_symm (P : {P // M.Point P}) :
  (M.parallel_point_equiv.symm P : Set α) = (P : Set α) \ M.cl ∅ := rfl

theorem parallel_classes_partition (M : Matroid α) :
    IsPartition (classes M.Parallel) (M.E \ M.cl ∅) := by
  convert classes_partition M.Parallel using 1; ext x; simp [Nonloop, Loop, and_comm]

theorem parallel_classes_finite (M : Matroid α) [Matroid.Finite M] : (classes M.Parallel).Finite :=
  M.parallel_classes_partition.finite_of_finite (M.set_finite _ (diff_subset _ _))

end ParallelClass


section Simple

class Simple (M : Matroid α) : Prop where
  (parallel_iff_eq : ∀ {e f}, e ∈ M.E → (M.Parallel e f ↔ e = f))

theorem Parallel.eq [Simple M] (h : M.Parallel e f) : e = f := by
  rwa [Simple.parallel_iff_eq h.mem_ground_left] at h

theorem parallel_iff_eq [Simple M] (he : e ∈ M.E := by aesop_mat) :
    M.Parallel e f ↔ e = f :=
  Simple.parallel_iff_eq he

theorem not_parallel_of_ne (M : Matroid α) [Simple M] (hef : e ≠ f) : ¬ M.Parallel e f :=
  fun h ↦ hef h.eq

instance [Simple M] : Loopless M := by
  rw [loopless_iff_forall_nonloop]
  exact fun e he ↦ ((parallel_iff_eq he).2 rfl).nonloop_left

instance {α : Type*} : Simple (emptyOn α) :=
  ⟨fun he ↦ by simp at he⟩

theorem simple_iff_loopless_eq_of_parallel_forall:
    Simple M ↔ (M.Loopless ∧ ∀ e f, M.Parallel e f → e = f) :=
  ⟨fun h ↦ ⟨by infer_instance, fun _ _ ↦ Parallel.eq⟩,
    fun ⟨_,h⟩ ↦ ⟨fun heE ↦ ⟨h _ _,by rintro rfl; exact (toNonloop heE).parallel_self⟩⟩⟩

theorem parallel_class_eq [Simple M] (he : e ∈ M.E := by aesop_mat) :
    {f | M.Parallel e f} = {e} := by
  simp_rw [parallel_iff_eq he, setOf_eq_eq_singleton']

theorem cl_singleton_eq [Simple M] (he : e ∈ M.E := by aesop_mat) : M.cl {e} = {e} := by
  rw [cl_eq_parallel_class_union_loops, parallel_class_eq he, cl_empty_eq_empty, union_empty]

/-- We need `RkPos` or something similar here, since otherwise the matroid whose only element is
  a loop is a counterexample. -/
theorem simple_iff_cl_subset_self_forall [RkPos M] :
    M.Simple ↔ ∀ e, M.Nonloop e → M.cl {e} ⊆ {e} := by
  refine ⟨fun h e he ↦ by rw [cl_singleton_eq], fun h ↦ ?_⟩
  have hl : M.Loopless
  · rw [loopless_iff_forall_not_loop]
    intro e _ hel
    obtain ⟨f, hf⟩ := M.exists_nonloop
    obtain (rfl : e = f) := (h f hf).subset (hel.mem_cl _)
    exact hf.not_loop hel
  rw [simple_iff_loopless_eq_of_parallel_forall, and_iff_right hl]
  exact fun e f hp ↦ (h _ hp.nonloop_right) hp.mem_cl

theorem singleton_flat [Simple M] (he : e ∈ M.E := by aesop_mat) : M.Flat {e} := by
  rw [←cl_singleton_eq]; apply cl_flat

theorem pair_indep [Simple M] (he : e ∈ M.E := by aesop_mat) (hf : f ∈ M.E := by aesop_mat) :
    M.Indep {e,f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · rw [pair_eq_singleton, indep_singleton]; exact toNonloop he
  rwa [←not_dep_iff, ←(toNonloop he).parallel_iff_dep (toNonloop hf) hne, parallel_iff_eq he]

theorem indep_of_encard_le_two [Simple M] (h : I.encard ≤ 2) (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  have hne : I.encard ≠ ⊤ := (h.trans_lt (by exact (cmp_eq_lt_iff 2 ⊤).mp rfl : (2 : ℕ∞) < ⊤ )).ne
  rw [le_iff_lt_or_eq, encard_eq_two, ←ENat.add_one_le_iff hne, (by norm_num : (2 : ℕ∞) = 1 + 1),
    WithTop.add_le_add_iff_right, encard_le_one_iff_eq] at h
  · obtain (rfl | ⟨x, rfl⟩) | ⟨x, y, hxy, rfl⟩ := h
    · exact M.empty_indep
    · refine indep_singleton.2 (toNonloop (by aesop_mat))
    exact pair_indep
  norm_num

theorem er_pair_eq [Simple M] (hef : e ≠ f) (he : e ∈ M.E := by aesop_mat)
    (hf : f ∈ M.E := by aesop_mat) : M.er {e,f} = 2 := by
  rw [(pair_indep he).er, encard_pair hef]

theorem Dep.two_lt_encard [Simple M] (hD : M.Dep D) : 2 < D.encard :=
  lt_of_not_le fun hle ↦ hD.not_indep (indep_of_encard_le_two hle)

theorem simple_iff_forall_circuit : M.Simple ↔ ∀ C, M.Circuit C → 2 < C.encard := by
  refine ⟨fun h C hC ↦ hC.dep.two_lt_encard, fun h ↦  ?_⟩
  rw [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_circuit]
  refine ⟨fun C hC ↦ lt_of_le_of_lt (by norm_num) (h C hC), fun e f hef ↦ by_contra fun hne ↦ ?_⟩
  exact (h _ ((parallel_iff_circuit hne).1 hef)).ne (by rw [encard_pair hne])

theorem simple_iff_forall_pair_indep :
    M.Simple ↔ ∀ {e f} (_ : e ∈ M.E) (_ : f ∈ M.E), M.Indep {e,f} := by
  refine ⟨fun h e f he hf ↦ pair_indep he hf,
    fun h ↦ ⟨fun {e f} he ↦
      ⟨fun hp ↦ by_contra fun hef ↦ (hp.dep_of_ne hef).not_indep <| h he hp.mem_ground_right, ?_ ⟩⟩⟩
  rintro rfl
  have hee := h he he
  simp only [mem_singleton_iff, insert_eq_of_mem, indep_singleton] at hee
  exact hee.parallel_self

theorem simple_iff_forall_parallel_class [Loopless M] :
    M.Simple ↔ ∀ P ∈ PSetoid.classes M.Parallel, encard P ≤ 1 := by
  simp_rw [mem_parallel_classes_iff_eq_cl]
  refine ⟨fun h P ⟨e, he, hP⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [cl_singleton_eq, cl_empty_eq_empty, diff_empty] at hP
    rw [hP, encard_singleton]

  obtain (rfl | _) := M.eq_emptyOn_or_nonempty
  · infer_instance

  rw [simple_iff_cl_subset_self_forall]
  refine fun e he x hx ↦ (?_ : x = e)
  have hpara := h _ ⟨e, he, rfl⟩
  rw [←parallel_class_eq_cl_diff_loops, encard_le_one_iff] at hpara
  apply hpara _ _ _ he.parallel_self
  rwa [mem_setOf, parallel_comm, (toNonloop (M.cl_subset_ground _ hx)).parallel_iff_mem_cl]

@[simp] theorem simple_trivialOn_iff {I E : Set α} : (trivialOn I E).Simple ↔ E ⊆ I := by
  simp only [simple_iff_forall_pair_indep, trivialOn_ground, mem_singleton_iff,
    trivialOn_indep_iff', subset_inter_iff]
  refine ⟨fun h x hxE ↦ by simpa using (h hxE hxE).1, fun h {e f} he hf ↦ ⟨subset_trans ?_ h, ?_⟩⟩
  <;> rintro x (rfl | rfl) <;> assumption

instance simple_freeOn {E : Set α} : (freeOn E).Simple := by
  rw [←trivialOn_eq_freeOn, simple_trivialOn_iff]

@[simp] theorem simple_loopyOn_iff {E : Set α} : (loopyOn E).Simple ↔ E = ∅ := by
  rw [←trivialOn_eq_loopyOn, simple_trivialOn_iff, subset_empty_iff]

end Simple
