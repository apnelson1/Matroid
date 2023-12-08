import Matroid.Constructions.Basic
import Matroid.ForMathlib.PartitionOf
import Matroid.ForMathlib.Other
import Matroid.Flat
import Matroid.Constructions.ImagePreimage

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

theorem Parallel.parallel_iff_left (h : M.Parallel e f) {x : α} :
    M.Parallel x e ↔ M.Parallel x f :=
  ⟨fun h' ↦ h'.trans h , fun h' ↦ h'.trans h.symm⟩

theorem Parallel.parallel_iff_right (h : M.Parallel e f) {x : α} :
    M.Parallel e x ↔ M.Parallel f x :=
  ⟨h.symm.trans, h.trans⟩

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

theorem parallel_class_eq_cl_diff_loops (M : Matroid α) (e : α) :
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

theorem Parallel.circuit_of_ne (hef : M.Parallel e f) (hne : e ≠ f) : M.Circuit {e,f} := by
  rwa [parallel_iff_circuit hne] at hef

theorem Nonloop.parallel_iff_dep (he : M.Nonloop e) (hf : M.Nonloop f) (hef : e ≠ f) :
    M.Parallel e f ↔ M.Dep {e,f} := by
  rw [←hf.indep.mem_cl_iff_of_not_mem hef, he.parallel_iff_mem_cl]

theorem Parallel.eq_of_indep (h : M.Parallel e f) (hi : M.Indep {e,f}) : e = f := by
  by_contra hef
  exact ((h.nonloop_left.parallel_iff_dep h.nonloop_right hef).1 h).not_indep hi

theorem parallel_iff_nonloop_nonloop_indep_imp_eq :
    M.Parallel e f ↔ M.Nonloop e ∧ M.Nonloop f ∧ (M.Indep {e,f} → e = f) := by
  refine ⟨fun h ↦ ⟨h.nonloop_left, h.nonloop_right, fun hi ↦ h.eq_of_indep hi⟩, fun h ↦ ?_⟩
  obtain (rfl | hne) := eq_or_ne e f
  · exact h.1.parallel_self
  rw [h.1.parallel_iff_dep h.2.1 hne, Dep, pair_subset_iff, and_iff_left h.2.1.mem_ground,
    and_iff_left h.1.mem_ground]
  exact fun hi ↦ hne (h.2.2 hi)

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

theorem Indep.parallelMap {φ : α → α} (hI : M.Indep I) (h_para : ∀ e ∈ I, M.Parallel e (φ e)) :
    M.Indep (φ '' I) := by
  rw [indep_iff_forall_subset_not_circuit', and_iff_right]
  · rintro _ ⟨e,he,rfl⟩; exact (h_para e he).mem_ground_right
  rintro C hCI hC
  obtain ⟨e, heC⟩ := hC.nonempty
  obtain ⟨e, he, rfl⟩ := hCI heC
  have h1 : e ∈ M.cl (φ '' (I \ {e}))
  · have h1' := singleton_subset_iff.2 <| (hC.subset_cl_diff_singleton (φ e)) heC
    apply mem_of_mem_of_subset <| (cl_subset_cl_of_subset_cl h1') (h_para _ he).mem_cl
    apply M.cl_subset_cl
    rw [diff_subset_iff, singleton_union, ← image_insert_eq, insert_diff_singleton]
    exact hCI.trans (image_subset _ (subset_insert _ _))
  have h2 : φ '' (I \ {e}) ⊆ M.cl (I \ {e})
  · rintro _ ⟨f, hf, rfl⟩
    exact mem_of_mem_of_subset (h_para _ hf.1).symm.mem_cl
      (M.cl_subset_cl <| singleton_subset_iff.2 hf)
  exact hI.not_mem_cl_diff_of_mem he <| (cl_subset_cl_of_subset_cl h2) h1

theorem Indep.of_parallelMap {φ : α → α} (hI : M.Indep (φ '' I)) (hφ : InjOn φ I)
    (h_para : ∀ e ∈ I, M.Parallel e (φ e)) : M.Indep I := by
  rw [indep_iff_forall_subset_not_circuit', and_iff_right]
  · exact fun e heI ↦ (h_para e heI).mem_ground_left
  intro C hCI hC
  obtain ⟨e, heC⟩ := hC.nonempty
  have he' : φ e ∈ M.cl (C \ {e})
  · exact cl_subset_cl_of_subset_cl (singleton_subset_iff.2 <| hC.subset_cl_diff_singleton e heC)
      (h_para _ (hCI heC)).symm.mem_cl
  have h : C \ {e} ⊆ M.cl (φ '' (C \ {e}))
  · rintro x hx
    refine mem_of_mem_of_subset (h_para x (hCI hx.1)).mem_cl (M.cl_subset_cl ?_)
    rw [singleton_subset_iff]
    exact mem_image_of_mem φ hx
  apply hI.not_mem_cl_diff_of_mem (mem_image_of_mem φ (hCI heC))
  refine mem_of_mem_of_subset (cl_subset_cl_of_subset_cl h he') (M.cl_subset_cl ?_)
  rw [← image_singleton, ← hφ.image_diff (singleton_subset_iff.2 (hCI heC))]
  exact image_subset _ <| diff_subset_diff_left hCI

theorem indep_image_iff_of_injOn_parallelMap {φ : α → α} (hφ : InjOn φ I)
    (h : ∀ e ∈ I, M.Parallel e (φ e)) : M.Indep (φ '' I) ↔ M.Indep I :=
  ⟨fun hI ↦ hI.of_parallelMap hφ h, fun hi ↦ hi.parallelMap h⟩

/-- A LocalEquiv from `X ⊆ M.E` to `Y` that maps loops to loops and nonloops to
  parallel copies on a set `X` gives an isomorphism from `M ↾ X` to `M ↾ Y` -/
def isoOfMapParallelRestr {M : Matroid α} (X Y : Set α) (hXE : X ⊆ M.E) (π : LocalEquiv α α)
  (hX : π.source = X) (hY : π.target = Y) (hLoop : ∀ e ∈ X, M.Loop e → M.Loop (π e))
  (hPara : ∀ e ∈ X, M.Nonloop e → M.Parallel e (π e)) : (M ↾ X).Iso (M ↾ Y) :=
  iso_of_forall_indep' π (by simpa) (by simpa)
  ( by
    subst hX hY
    simp only [restrict_ground_eq, restrict_indep_iff, image_subset_iff]
    refine fun I hI ↦ ⟨fun ⟨h,_⟩ ↦ ⟨?_,?_⟩, fun ⟨hi, _⟩ ↦ ⟨?_,hI⟩⟩
    · exact h.parallelMap (fun e heI ↦ hPara _ (hI heI) (h.nonloop_of_mem heI))
    · exact hI.trans π.source_subset_preimage_target
    refine hi.of_parallelMap (π.injOn.mono hI) (fun e heI ↦ hPara e (hI heI) ?_ )
    rw [Nonloop, and_iff_left ((hI.trans hXE) heI)]
    exact fun hl ↦ (hi.nonloop_of_mem (mem_image_of_mem π heI)).not_loop (hLoop _ (hI heI) hl) )

@[simp] theorem isoOfMapParallelRestr_toLocalEquiv {M : Matroid α} (X Y : Set α) (hXE : X ⊆ M.E)
    (π : LocalEquiv α α) (hX : π.source = X) (hY : π.target = Y)
    (hLoop : ∀ e ∈ X, M.Loop e → M.Loop (π e)) (hPara : ∀ e ∈ X, M.Nonloop e → M.Parallel e (π e)) :
    (isoOfMapParallelRestr X Y hXE π hX hY hLoop hPara).toLocalEquiv = π := rfl

def isoOfMapParallel (M : Matroid α) (π : LocalEquiv α α) (h_source : π.source = M.E)
    (h_target : π.target = M.E) (hLoop : ∀ {e}, M.Loop e → M.Loop (π e))
    (hPara : ∀ {e}, M.Nonloop e → M.Parallel e (π e)) : M.Iso M :=
  let π := isoOfMapParallelRestr M.E M.E Subset.rfl π h_source h_target
    (fun _ _ he ↦ hLoop he) (fun _ _ he ↦ hPara he)
  let ψ := Iso.ofEq M.restrict_ground_eq_self
  (ψ.symm.trans π).trans ψ

@[simp] theorem isoOfMapParallel_toLocalEquiv (M : Matroid α) (π : LocalEquiv α α)
    (h_source : π.source = M.E) (h_target : π.target = M.E) (hLoop : ∀ {e}, M.Loop e → M.Loop (π e))
    (hPara : ∀ {e}, M.Nonloop e → M.Parallel e (π e)) :
    (isoOfMapParallel M π h_source h_target hLoop hPara).toLocalEquiv = π := by
  simp only [isoOfMapParallel, Iso.trans_toLocalEquiv, Iso.symm_toLocalEquiv, Iso.ofEq_toLocalEquiv,
    restrict_ground_eq_self, LocalEquiv.ofSet_symm, isoOfMapParallelRestr_toLocalEquiv]
  ext x
  · simp
  · simp
  simp only [← h_source, LocalEquiv.trans_source, LocalEquiv.ofSet_source, LocalEquiv.ofSet_coe,
    preimage_id_eq, id_eq, inter_self, LocalEquiv.coe_trans, Function.comp.right_id, mem_inter_iff,
    mem_preimage, and_iff_left_iff_imp]
  intro hx
  rw [h_source, ← h_target]
  exact LocalEquiv.map_source π hx

/-- Swapping two parallel elements gives an automorphism -/
def Parallel.swap [DecidableEq α] {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : Iso M M :=
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
    (Parallel.swap h_para).toLocalEquiv = (Equiv.swap e f).toLocalEquiv.restr M.E := rfl

@[simp] theorem restrict_parallel_iff {R : Set α} :
    (M ↾ R).Parallel e f ↔ M.Parallel e f ∧ e ∈ R ∧ f ∈ R := by
  obtain (rfl | hef) := eq_or_ne e f
  · simp
  rw [parallel_iff_nonloop_nonloop_indep_imp_eq, restrict_nonloop_iff, restrict_nonloop_iff,
    restrict_indep_iff, pair_subset_iff, iff_false_intro hef, imp_false,
    parallel_iff_nonloop_nonloop_indep_imp_eq]
  aesop

@[simp] theorem removeLoops_parallel_iff : M.removeLoops.Parallel e f ↔ M.Parallel e f := by
  rw [removeLoops_eq_restr, restrict_parallel_iff, mem_setOf, mem_setOf, and_iff_left_iff_imp]
  exact fun h ↦ ⟨h.nonloop_left, h.nonloop_right⟩

theorem Parallel.of_restriction (h : N.Parallel e f) (hNM : N ≤r M) : M.Parallel e f := by
  obtain ⟨R, hR, rfl⟩ := hNM; exact (restrict_parallel_iff.1 h).1

theorem Parallel.parallel_restriction (h : M.Parallel e f) (hNM : N ≤r M)
    (he : e ∈ N.E) (hf : f ∈ N.E) : N.Parallel e f := by
  obtain ⟨R, -, rfl⟩ := hNM; rwa [restrict_parallel_iff, and_iff_left ⟨he, hf⟩]

theorem Restriction.parallel_iff (hNM : N ≤r M) :
    N.Parallel e f ↔ M.Parallel e f ∧ e ∈ N.E ∧ f ∈ N.E := by
  obtain ⟨R, -, rfl⟩ := hNM; simp

end Parallel

section Series

@[pp_dot] def Series (M : Matroid α) (e f : α) : Prop := M﹡.Parallel e f

-- API TODO, but all will follow easily from duality.


end Series

section ParallelClass

open PSetoid

theorem mem_parallel_classes_iff_eq_cl :
    P ∈ classes M.Parallel ↔ ∃ e, M.Nonloop e ∧ P = M.cl {e} \ M.cl ∅ := by
  simp [mem_classes_iff, parallel_class_eq_cl_diff_loops]

@[simp] theorem mem_parallel_classes_iff :
    P ∈ classes M.Parallel ↔ ∃ e, M.Nonloop e ∧ P = {f | M.Parallel e f} := by
  simp only [mem_classes_iff, parallel_self_iff, parallel_class_eq_cl_diff_loops]

/-- Parallel classes correspond to points -/
def parallelPointEquiv (M : Matroid α) : classes M.Parallel ≃ {P // M.Point P} where
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
    rintro ⟨P, hP⟩; obtain ⟨e, -, rfl⟩ := mem_parallel_classes_iff.1 hP
    simp [parallel_class_eq_cl_diff_loops]
  right_inv := by
    rintro ⟨P, hP, hPr⟩; simp [hP.cl_subset_of_subset (empty_subset P)]

@[simp] theorem parallelPointEquiv_apply (P : classes M.Parallel) :
    (M.parallelPointEquiv P : Set α) = (P : Set α) ∪ M.cl ∅ := rfl

@[simp] theorem parallelPointEquiv_apply_symm (P : {P // M.Point P}) :
  (M.parallelPointEquiv.symm P : Set α) = (P : Set α) \ M.cl ∅ := rfl

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

@[simp] theorem cl_singleton_eq [Simple M] (he : e ∈ M.E := by aesop_mat) : M.cl {e} = {e} := by
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

theorem cl_eq_self_of_subset_singleton [Simple M] (he : e ∈ M.E) (hX : X ⊆ {e}) : M.cl X = X := by
  obtain (rfl | rfl) := subset_singleton_iff_eq.1 hX
  · exact M.cl_empty_eq_empty
  exact cl_singleton_eq he

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

theorem Indep.restr_simple (hI : M.Indep I) : (M ↾ I).Simple := by
  simp only [simple_iff_forall_pair_indep, restrict_ground_eq, mem_singleton_iff,
    restrict_indep_iff, pair_subset_iff]
  rintro e f he hf
  exact ⟨hI.subset (pair_subset he hf), he, hf⟩

theorem Simple.subset_ground {X : Set α} (_ : (M ↾ X).Simple) : X ⊆ M.E :=
  fun _ hx ↦ (toNonloop (M := M ↾ X) hx).of_restrict.mem_ground

theorem Simple.subset {X Y : Set α} (hY : (M ↾ Y).Simple) (hXY : X ⊆ Y) : (M ↾ X).Simple := by
  simp only [simple_iff_forall_pair_indep, restrict_ground_eq, mem_singleton_iff,
    restrict_indep_iff, pair_subset_iff] at *
  aesop

theorem exists_loop_or_para_of_not_simple (hM : ¬ M.Simple) :
    (∃ e, M.Loop e) ∨ ∃ e f, M.Parallel e f ∧ e ≠ f := by
  by_contra! h
  rw [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_not_loop] at hM
  push_neg at hM
  obtain ⟨e, f, hef, hne⟩ := hM (fun e _ ↦ h.1 e)
  exact hne <| h.2 e f hef



end Simple

section Simplification

variable {M : Matroid α} {c : α → α}

/-- A function that chooses a representative from the parallel class for each nonloop,
  and is the identity elsewhere. Such a function corresponds to a restriction of `M`
  that is simple  -/
def ParallelChoiceFunction (M : Matroid α) (c : α → α) : Prop :=
  (∀ {e}, ¬ M.Nonloop e → c e = e) ∧ (∀ {e}, M.Nonloop e → M.Parallel e (c e)) ∧
    (∀ {e f}, M.Nonloop e → M.Nonloop f → (M.Parallel e f ↔ c e = c f))

theorem ParallelChoiceFunction.parallel_iff_of_nonloop (hc : M.ParallelChoiceFunction c)
  (he : M.Nonloop e) (hf : M.Nonloop f) : M.Parallel e f ↔ c e = c f := hc.2.2 he hf

theorem ParallelChoiceFunction.eq_of_parallel (hc : M.ParallelChoiceFunction c)
    (hef : M.Parallel e f) : c e = c f :=
  (hc.parallel_iff_of_nonloop hef.nonloop_left hef.nonloop_right).1 hef

theorem ParallelChoiceFunction.parallel_apply (hc : M.ParallelChoiceFunction c)
    (he : M.Nonloop e) : M.Parallel e (c e) :=
  hc.2.1 he

theorem ParallelChoiceFunction.nonloop (hc : M.ParallelChoiceFunction c)
    (he : M.Nonloop e) : M.Nonloop (c e) :=
  (hc.parallel_apply he).nonloop_right

theorem ParallelChoiceFunction.eq_self (hc : M.ParallelChoiceFunction c) (he : ¬M.Nonloop e) :
    c e = e := hc.1 he

theorem ParallelChoiceFunction.idem (hc : M.ParallelChoiceFunction c) (e : α) : c (c e) = c e := by
  obtain (he | he) := em (M.Nonloop e)
  · rw [hc.eq_of_parallel]
    rw [parallel_comm]
    exact hc.parallel_apply he
  rw [hc.eq_self he, hc.eq_self he]

theorem ParallelChoiceFunction.nonloop_apply_iff (hc : M.ParallelChoiceFunction c) :
    M.Nonloop (c e) ↔ M.Nonloop e := by
  refine ⟨fun h ↦ by_contra fun he ↦ ?_, hc.nonloop⟩
  rw [hc.eq_self he] at h
  exact he h

theorem ParallelChoiceFunction.parallel_of_apply_eq (hc : M.ParallelChoiceFunction c)
    (he : M.Nonloop e) (hef : c e = c f) : M.Parallel e f := by
  apply (hc.parallel_iff_of_nonloop he _).2 hef
  rwa [← hc.nonloop_apply_iff, ← hef, hc.nonloop_apply_iff]

theorem ParallelChoiceFunction.preimage_image_setOf_nonloop (hc : M.ParallelChoiceFunction c) :
    c ⁻¹' (c '' {e | M.Nonloop e}) = {e | M.Nonloop e} := by
  simp only [ext_iff, mem_preimage, mem_image, mem_setOf_eq]
  exact fun x ↦ ⟨fun ⟨y, hy, hyx⟩ ↦ (hc.parallel_of_apply_eq hy hyx).nonloop_right,
    fun hx ↦ ⟨_, hx, rfl⟩⟩

theorem ParallelChoiceFunction.image_setOf_nonloop_subset (hc : M.ParallelChoiceFunction c) :
    c '' {e | M.Nonloop e} ⊆ {e | M.Nonloop e} := by
  rintro _ ⟨e, he, rfl⟩; exact hc.nonloop he

theorem ParallelChoiceFunction.injOn (hc : M.ParallelChoiceFunction c) (hX : (M ↾ X).Simple) :
    InjOn c X := by
  simp only [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_nonloop,
    restrict_ground_eq, restrict_nonloop_iff, restrict_parallel_iff, and_imp] at hX
  exact fun e he f hf hef ↦ hX.2 _ _ (hc.parallel_of_apply_eq (hX.1 _ he).1 hef) he hf

/-- Any simple restriction of `M` can be extended to a parallel choice function. -/
theorem extends_to_parallelChoiceFunction {M : Matroid α} {X : Set α} (hX : (M ↾ X).Simple) :
    ∃ c, M.ParallelChoiceFunction c ∧ EqOn c id X := by
  classical
  have hc : ∀ {x}, M.Nonloop x → {y | M.Parallel x y}.Nonempty :=
    fun {x} hx ↦ ⟨x, hx.parallel_self⟩

  set φ := fun e ↦ if he : M.Nonloop e then
    (if heX : ∃ x ∈ X, M.Parallel e x then heX.choose else (hc he).some) else e

  have hnl : ∀ {e}, M.Nonloop e → M.Parallel e (φ e)
  · intro e
    simp only
    split_ifs with h he
    · exact fun _ ↦ he.choose_spec.2
    · exact fun _ ↦ (hc h).some_mem
    exact Nonloop.parallel_self

  have h_eq : ∀ {e} {f}, M.Parallel (φ e) (φ f) → φ e = φ f
  · intro e f
    simp only
    obtain (he | he) := em' (M.Nonloop e)
    · rw [dif_neg he]
      exact fun h ↦ (he h.nonloop_left).elim
    obtain (hf | hf) := em' (M.Nonloop f)
    · rw [dif_neg hf]
      exact fun h ↦ (hf h.nonloop_right).elim
    rw [dif_pos he, dif_pos hf]
    split_ifs with heX hfX hfX <;> intro hp
    · refine Parallel.eq (M := M ↾ X) ?_
      rw [restrict_parallel_iff]
      exact ⟨hp, heX.choose_spec.1, hfX.choose_spec.1⟩
    · exact (hfX ⟨heX.choose, heX.choose_spec.1, (hp.trans (hc hf).some_mem.symm).symm⟩).elim
    · exact (heX ⟨hfX.choose, hfX.choose_spec.1, Parallel.trans (hc he).some_mem hp⟩).elim
    convert rfl using 2
    simp only [Set.ext_iff, mem_setOf_eq]
    have hef := (Parallel.trans (hc he).some_mem hp).trans (hc hf).some_mem.symm
    exact fun _ ↦ ⟨hef.trans, hef.symm.trans⟩

  refine ⟨φ, ⟨fun {e} he ↦ by simp [he], fun he ↦ hnl he, fun {e} {f} he hf ↦ ?_⟩, fun e heX ↦ ?_⟩
  · exact ⟨fun h ↦ h_eq <| (hnl he).symm.trans (h.trans (hnl hf)),
      fun h ↦ (hnl he).trans (h ▸ (hnl hf).symm)⟩

  obtain ⟨hnl',-⟩ := restrict_nonloop_iff.1 <| toNonloop (M := M ↾ X) heX

  refine Parallel.eq (M := M ↾ X) ?_
  rw [restrict_parallel_iff, id, and_iff_right ((hnl hnl').symm), and_iff_left heX]
  simp only
  have he' : ∃ x ∈ X, M.Parallel e x
  · exact ⟨e, heX, hnl'.parallel_self⟩
  rw [dif_pos hnl', dif_pos he']
  exact he'.choose_spec.1

theorem exists_parallelChoiceFunction (M : Matroid α) : ∃ c, M.ParallelChoiceFunction c := by
  obtain ⟨c, hc, -⟩ := extends_to_parallelChoiceFunction (M := M) (X := ∅) (by simp; infer_instance)
  exact ⟨c,hc⟩

@[simp] theorem parallelChoiceFunction_removeLoops_iff :
    M.removeLoops.ParallelChoiceFunction c ↔ M.ParallelChoiceFunction c := by
  simp [ParallelChoiceFunction]

/-- The simplification of `M` (with respect to a choice function `c`) as a restriction of `M`. -/
@[pp_dot] def simplificationWrt (M : Matroid α) (c : α → α) : Matroid α :=
  M ↾ (c '' {e | M.Nonloop e})

@[simp] theorem removeLoops_simplificationWrt_eq (M : Matroid α) (c : α → α)
    (hc : M.ParallelChoiceFunction c) :
    M.removeLoops.simplificationWrt c = M.simplificationWrt c := by
  simp_rw [simplificationWrt, removeLoops_eq_restr, restrict_nonloop_iff, mem_setOf_eq, and_self]
  rw [restrict_restrict_eq]
  exact ParallelChoiceFunction.image_setOf_nonloop_subset hc

/-- The simplification of `M` relative to a classically chosen parallel choice function.
  Defined to depend only on `M.removeLoops`, so the same choice is made even if loops
  are removed/added to `M`. -/
@[pp_dot] def simplification (M : Matroid α) : Matroid α :=
  M.removeLoops.simplificationWrt M.removeLoops.exists_parallelChoiceFunction.choose

theorem simplification_eq_wrt (M : Matroid α) :
    M.simplification = M.simplificationWrt M.removeLoops.exists_parallelChoiceFunction.choose := by
  rw [simplification, removeLoops_simplificationWrt_eq]
  simpa using M.removeLoops.exists_parallelChoiceFunction.choose_spec

theorem exists_simplification_eq_wrt (M : Matroid α) :
    ∃ c, M.ParallelChoiceFunction c ∧ M.simplification = M.simplificationWrt c := by
  use M.removeLoops.exists_parallelChoiceFunction.choose
  rw [simplification_eq_wrt]
  simpa using M.removeLoops.exists_parallelChoiceFunction.choose_spec

@[simp] theorem removeLoops_simplification_eq (M : Matroid α) :
    M.removeLoops.simplification = M.simplification := by
  simp [simplification]

@[simp] theorem simplificationWrt_ground_eq (M : Matroid α) (c : α → α) :
  (M.simplificationWrt c).E = c '' {e | M.Nonloop e} := rfl

theorem Nonloop.mem_simplificationWrt_ground (he : M.Nonloop e) (c : α → α) :
    c e ∈ (M.simplificationWrt c).E := ⟨_, he, rfl⟩

theorem simplificationWrt_simple (M : Matroid α) {c : α → α}
    (hc : M.ParallelChoiceFunction c) : (M.simplificationWrt c).Simple := by
  simp_rw [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_nonloop,
    simplificationWrt, restrict_ground_eq, restrict_nonloop_iff, mem_image]
  simp only [mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    restrict_parallel_iff, mem_image]
  use fun e he ↦ ⟨(hc.2.1 he).nonloop_right, ⟨_, he, rfl⟩⟩
  rintro e f hef x hx rfl y hy rfl
  rw [← hc.2.2 hx hy]
  exact ((hef.trans (hc.2.1 hy).symm).symm.trans (hc.2.1 hx).symm).symm

instance simplification_simple (M : Matroid α) : M.simplification.Simple := by
  obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
  rw [hM]
  exact simplificationWrt_simple M hc

theorem preimage_simplificationWrt (M : Matroid α) (hc : M.ParallelChoiceFunction c) :
    (M.simplificationWrt c).preimage c = M.removeLoops := by
  simp only [simplificationWrt, removeLoops_eq_restr, eq_iff_indep_iff_indep_forall,
    preimage_ground_eq, restrict_ground_eq, hc.preimage_image_setOf_nonloop, preimage_indep_iff,
    restrict_indep_iff, image_subset_iff, true_and]
  intro I hI
  simp only [hI, and_true]
  refine ⟨fun ⟨hi, hinj⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · exact hi.of_parallelMap hinj (fun e heI ↦ hc.parallel_apply (hI heI))
  · exact h.parallelMap (fun e heI ↦ hc.parallel_apply (hI heI))
  exact hc.injOn h.restr_simple

/-- Any two simplifications are isomorphic -/
noncomputable def simplificationWrt_iso {c c' : α → α} (hc : M.ParallelChoiceFunction c)
  (hc' : M.ParallelChoiceFunction c') : (M.simplificationWrt c).Iso (M.simplificationWrt c') :=
  let L := {e | M.Nonloop e}
  have lem :  ∀ {c₁ c₂ : α → α} (_ : M.ParallelChoiceFunction c₁)
    (_ : M.ParallelChoiceFunction c₂) ⦃x : α⦄, x ∈ c₁ '' L → c₁ (c₂ x) = x := by
    rintro c₁ c₂ hc₁ hc₂ _ ⟨e, he, rfl⟩
    apply hc₁.eq_of_parallel
    apply ((hc₁.parallel_apply he).trans _).symm
    apply hc₂.parallel_of_apply_eq
    · rwa [hc₁.nonloop_apply_iff]
    rw [hc₂.idem]
  let π : LocalEquiv α α := {
    toFun := c'
    invFun := c
    source := c '' L
    target := c' '' L
    map_source' := ( by
      rintro _ ⟨e, (he : M.Nonloop e), rfl⟩
      exact mem_image_of_mem c' (hc.nonloop he) )
    map_target' := ( by
      rintro _ ⟨e, he, rfl⟩
      exact mem_image_of_mem c (hc'.nonloop he) )
    left_inv' := lem hc hc'
    right_inv' := lem hc' hc }
  isoOfMapParallelRestr (c '' L) (c' '' L)
    ( by
      simp only [image_subset_iff]
      exact fun e he ↦ (hc.nonloop he).mem_ground)
    π rfl rfl
    ( by
      rintro _ ⟨e,-,rfl⟩ he'
      change M.Loop (c' _)
      rwa [hc'.eq_self he'.not_nonloop] )
    ( by
      rintro _ ⟨e,-,rfl⟩ he'
      exact hc'.parallel_apply he' )

/-- Any simplification is isomorphic to the canonical one. This is defined in tactic mode for now -/
noncomputable def simplificationWrt_iso_simplification (hc : M.ParallelChoiceFunction c) :
    (M.simplificationWrt c).Iso M.simplification := by
  rw [simplification_eq_wrt]
  apply simplificationWrt_iso hc
  simpa using M.removeLoops.exists_parallelChoiceFunction.choose_spec

theorem simplificationWrt_isIso_simplification (hc : M.ParallelChoiceFunction c) :
    M.simplificationWrt c ≅ M.simplification :=
  (simplificationWrt_iso_simplification hc).isIso

theorem simplificationWrt_restriction (hc : M.ParallelChoiceFunction c) :
    M.simplificationWrt c ≤r M :=
  restrict_restriction _ _ <| hc.image_setOf_nonloop_subset.trans (fun _ ↦ Nonloop.mem_ground)

theorem simplification_restriction (M : Matroid α) : M.simplification ≤r M :=
  (simplificationWrt_restriction M.removeLoops.exists_parallelChoiceFunction.choose_spec).trans
    M.removeLoops_restriction

theorem simplificationWrt_eq_self_iff (hc : M.ParallelChoiceFunction c) :
    M.simplificationWrt c = M ↔ M.Simple := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]; exact M.simplificationWrt_simple hc
  rw [eq_comm]
  apply (simplificationWrt_restriction hc).minor.eq_of_ground_subset
  exact fun e he ↦ ⟨e, toNonloop he, Parallel.eq (hc.parallel_apply (toNonloop he)).symm⟩

@[simp] theorem simplification_eq_self_iff (M : Matroid α) : M.simplification = M ↔ M.Simple := by
  rw [simplification_eq_wrt, simplificationWrt_eq_self_iff]
  simpa using M.exists_parallelChoiceFunction.choose_spec

theorem exists_loop_or_parallel_of_simplificationWrt_strictRestriction
    (hc : M.ParallelChoiceFunction c) (hsN : M.simplificationWrt c <r N) (hNM : N ≤r M) :
    (∃ e, N.Loop e) ∨ (∃ e, N.Parallel e (c e) ∧ e ≠ c e) := by
  obtain ⟨R, hR, hsi⟩ := hsN.exists_eq_restrict
  obtain ⟨e, heN, heR⟩ := exists_of_ssubset hR
  refine (N.loop_or_nonloop e).elim (fun h ↦ Or.inl ⟨e,h⟩)
    (fun he ↦ Or.inr ⟨e, ?_, fun hce ↦ heR ?_⟩)
  · refine (hc.parallel_apply (he.of_restriction hNM)).parallel_restriction hNM heN (hR.subset ?_)
    rw [← restrict_ground_eq (M := N) (R := R), ← hsi]
    exact (he.of_restriction hNM).mem_simplificationWrt_ground c
  rw [← restrict_ground_eq (M := N) (R := R), ← hsi, hce]
  exact (he.of_restriction hNM).mem_simplificationWrt_ground c

theorem eq_simplificationWrt_of_restriction [Simple N] (hc : M.ParallelChoiceFunction c)
    (hsN : M.simplificationWrt c ≤r N) (hNM : N ≤r M)  :
    N = M.simplificationWrt c := by
  obtain (rfl | hM) := hsN.eq_or_strictRestriction
  · rfl
  obtain (⟨e,he⟩ | ⟨e,hef⟩) := exists_loop_or_parallel_of_simplificationWrt_strictRestriction
    hc hM hNM
  · exact (N.not_loop e he).elim
  exact (hef.2 hef.1.eq).elim

/-- If `N` is below `M` but strictly above `M.simplification` in the restriction order, then
  `N` has a loop or an element parallel to something in the simplification. -/
theorem exists_loop_or_parallel_of_simplification_strictRestriction
    (hsN : M.simplification <r N) (hNM : N ≤r M) :
    (∃ e, N.Loop e) ∨
    (∃ e f, N.Parallel e f ∧ e ∉ M.simplification.E ∧ f ∈ M.simplification.E) := by
  obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
  obtain (he | ⟨e,he,hce⟩) :=
    exists_loop_or_parallel_of_simplificationWrt_strictRestriction hc (hM ▸ hsN) hNM
  · exact Or.inl he
  refine Or.inr ⟨e,_, he, ?_⟩
  rw [hM] at hsN ⊢
  have hr := (he.nonloop_left.of_restriction hNM).mem_simplificationWrt_ground c
  refine ⟨fun h' ↦ ?_, hr⟩
  have _ := M.simplificationWrt_simple hc
  exact hce (he.parallel_restriction hsN.restriction h' hr).eq

theorem exists_parallel_of_simplification_strictRestriction [Loopless N]
    (hsN : M.simplification <r N) (hNM : N ≤r M) :
    (∃ e f, N.Parallel e f ∧ e ∉ M.simplification.E ∧ f ∈ M.simplification.E) := by
   obtain (⟨e,he⟩ | h) := exists_loop_or_parallel_of_simplification_strictRestriction hsN hNM
   · exact (N.not_loop e he).elim
   assumption

theorem eq_simplification_of_restriction [Simple N] (hsN : M.simplification ≤r N) (hNM : N ≤r M) :
    N = M.simplification := by
  obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
  rw [hM]
  exact eq_simplificationWrt_of_restriction hc (by rwa [← hM]) hNM


-- noncomputable def ParallelChoiceFunction.equiv (hc : M.ParallelChoiceFunction c) :
--     PSetoid.classes M.Parallel ≃ (M.simplificationWrt c).E where
--   toFun P := ⟨P.prop.nonempty.some, ⟨P.prop.nonempty.some, by
--     simp


--     ⟩⟩
--   invFun := _
--   left_inv := _
--   right_inv := _


end Simplification
