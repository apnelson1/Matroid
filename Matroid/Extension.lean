import Matroid.Simple
import Matroid.Closure
import Matroid.Minor.Basic
import Matroid.Constructions.ImagePreimage
import Matroid.ForMathlib.Other
open Set
namespace Matroid

variable {M : Matroid α}

/-- Replace the elements of `S` with parallel copies of `e`. -/
def ParallelExt (M : Matroid α) (e : α) (S : Set α) [DecidablePred (· ∈ S)] : Matroid α :=
    M.preimage (fun x ↦ if (x ∈ S) then e else x)

theorem insert_diff_insert_diff {B : Set α} (e_in_B : e ∈ B) (f_notin_B : f ∉ B):
    insert e (insert f (B \ {e}) \ {f}) = B := by simp [e_in_B, f_notin_B]

theorem Equiv.image_invol [DecidableEq α] {e f : α} :
    Function.Involutive (Set.image (Equiv.swap e f)) := by
  have inv : Function.Involutive (Equiv.swap e f) := fun x ↦ Equiv.swap_apply_self _ _ _
  intro X
  rw [←Set.image_comp _ _, Function.Involutive.comp_self inv, image_id]

theorem Equiv.swap_image_eq_self [DecidableEq α] {S : Set α} (hef : e ∈ S ↔ f ∈ S) :
    (Equiv.swap e f) '' S = S := by
  ext x
  rw [image_equiv_eq_preimage_symm, mem_preimage, Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with hxe hxf
  · rwa [hxe, Iff.comm]
  · rwa [hxf]
  rfl

theorem Equiv.swap_image_eq_exchange [DecidableEq α] {S : Set α} (he : e ∈ S) (hf : f ∉ S) :
    (Equiv.swap e f) '' S = insert f (S \ {e}) := by
  ext x
  rw [image_equiv_eq_preimage_symm, mem_preimage, Equiv.symm_swap, Equiv.swap_apply_def,
    mem_insert_iff, mem_diff]
  split_ifs with hxe hxf
  · subst hxe
    simp [he, hf, (show x ≠ f by rintro rfl; exact hf he)]
  · subst hxf
    simp [he]
  simp [hxe, iff_false_intro hxf]

/-- Swapping two parallel elements gives an automorphism -/
def parallel_swap [DecidableEq α] {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : Iso M M :=
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
    (parallel_swap h_para).toLocalEquiv = (Equiv.swap e f).toLocalEquiv.restr M.E := rfl

theorem filter_preimage_eq {e f : α} [DecidableEq α] {S : Set α} (he : e ∈ S) (hf : f ∈ S)
    (h_ne : e ≠ f) : (fun x ↦ if (x = e) then f else x) ⁻¹' (S \ {e}) = S := by
  ext x
  simp only [preimage_diff, mem_diff, mem_preimage, mem_singleton_iff]
  split_ifs with hxe
  · subst hxe
    exact iff_of_true ⟨hf, h_ne.symm⟩ he
  rw [and_iff_left hxe]

open Classical
theorem eq_parallelExt_del {M : Matroid α} {e f : α} (h_para : M.Parallel e f) (h_ne : e ≠ f):
    M = ParallelExt (M ⟍ f) e {f} := by
  rw [ParallelExt, eq_iff_indep_iff_indep_forall, preimage_ground_eq]


  refine' ⟨_, fun I I_ground ↦ ⟨fun I_Ind ↦ _, _⟩⟩
  · simp only [mem_singleton_iff, delete_elem, delete_ground]
    rw [filter_preimage_eq (h_para.mem_ground_right) (h_para.mem_ground_left) h_ne.symm]
  · rw [preimage_indep_iff]
    simp only [delete_elem, mem_singleton_iff, delete_indep_iff, disjoint_singleton_right,
      mem_image, not_exists, not_and, delete_ground, union_singleton, mem_diff, not_true, and_false,
      insert_diff_singleton]
    constructor
    · constructor
      · by_cases f_in_I : f ∈ I
        · have image_eq : (fun a ↦ if a = f then e else a) '' I = insert e (I \ {f})
          · apply subset_antisymm
            · rintro i ⟨a, a_I, h_a₁⟩
              dsimp at h_a₁
              by_cases a_eq_f : a = f
              · rw [if_pos a_eq_f] at h_a₁
                rw [←h_a₁]
                exact mem_insert _ _
              · rw [if_neg a_eq_f] at h_a₁
                rw [←h_a₁]
                exact mem_insert_of_mem _ (mem_diff_singleton.2 ⟨a_I, a_eq_f⟩)
            · rintro i (i_eq_e | ⟨i_in_I, (i_ne_f : i ≠ f)⟩)
              · refine' ⟨f, f_in_I, _⟩
                rw [i_eq_e]
                exact if_pos rfl
              · refine ⟨i, i_in_I, if_neg i_ne_f⟩
          rw [image_eq]
          apply I_Ind.parallel_substitute h_para.symm f_in_I
        · have image_eq : (fun a ↦ if a = f then e else a) '' I = I
          · apply subset_antisymm
            · rintro i ⟨a, a_I, h_a₁⟩
              dsimp at h_a₁
              rw [if_neg (ne_of_mem_of_not_mem a_I f_in_I)] at h_a₁
              rwa [←h_a₁]
            · rintro i i_in_I
              refine' ⟨i, i_in_I, if_neg (ne_of_mem_of_not_mem i_in_I f_in_I)⟩
          rwa [image_eq]
      · intro x _
        by_cases x_eq_f : x = f
        · rwa [if_pos x_eq_f]
        · rwa [if_neg x_eq_f]

    --refine' ⟨_, subset_trans I_ground (subset_insert f M.E)⟩
    rintro a a_I b b_I f_ab
    dsimp at f_ab
    by_cases b_eq_f : b = f
    · rw [if_pos b_eq_f, ite_eq_left_iff] at f_ab
      by_cases a_eq_f : a = f
      · rwa [b_eq_f]
      · have ef_sub_I : {e, f} ⊆ I
        · rintro i (i_eq_e | (i_eq_f : i = f))
          · rwa [i_eq_e, ←(f_ab a_eq_f)]
          · rwa [i_eq_f, ←b_eq_f]
        exfalso
        apply I_Ind.not_dep _
        rw [dep_iff_superset_circuit]
        exact ⟨{e, f}, ef_sub_I, (parallel_iff_circuit h_ne).1 h_para⟩
    · rw [if_neg b_eq_f] at f_ab
      by_cases a_eq_f : a = f
      · rw [if_pos a_eq_f] at f_ab
        have ef_sub_I : {e, f} ⊆ I
        · rintro i (i_eq_e | (i_eq_f : i = f))
          · rwa [i_eq_e, f_ab]
          · rwa [i_eq_f, ←a_eq_f]
        exfalso
        apply I_Ind.not_dep _
        rw [dep_iff_superset_circuit]
        exact ⟨{e, f}, ef_sub_I, (parallel_iff_circuit h_ne).1 h_para⟩
      · rwa [if_neg a_eq_f] at f_ab
  -- part 2
  rw [preimage_indep_iff]

  rintro ⟨(I_image_Indep : (M ⟍ f).Indep ((fun x ↦ if x = f then e else x) '' I)), h_inj⟩
  by_cases f_in_I : f ∈ I
  · have image_eq : (fun a ↦ if a = f then e else a) '' I = insert e (I \ {f})
    · apply subset_antisymm
      · rintro i ⟨a, a_I, h_a₁⟩
        dsimp at h_a₁
        by_cases a_eq_f : a = f
        · rw [if_pos a_eq_f] at h_a₁
          rw [←h_a₁]
          exact mem_insert _ _
        · rw [if_neg a_eq_f] at h_a₁
          rw [←h_a₁]
          exact mem_insert_of_mem _ (mem_diff_singleton.2 ⟨a_I, a_eq_f⟩)
      · rintro i (i_eq_e | ⟨i_in_I, (i_ne_f : i ≠ f)⟩)
        · refine' ⟨f, f_in_I, _⟩
          rw [i_eq_e]
          exact if_pos rfl
        · refine ⟨i, i_in_I, if_neg i_ne_f⟩
    rw [image_eq] at I_image_Indep
    have:= I_image_Indep.of_delete.parallel_substitute h_para (mem_insert e _)
    have e_notin_I : e ∉ I
    · intro e_in_I
      apply h_ne (h_inj e_in_I f_in_I _)
      dsimp
      simp
    rwa [←insert_diff_insert_diff f_in_I e_notin_I]
  · have image_eq : (fun a ↦ if a = f then e else a) '' I = I
    · apply subset_antisymm
      · rintro i ⟨a, a_I, h_a₁⟩
        dsimp at h_a₁
        rw [if_neg (ne_of_mem_of_not_mem a_I f_in_I)] at h_a₁
        rwa [←h_a₁]
      · intro i i_in_I
        refine' ⟨i, i_in_I, _⟩
        exact if_neg (ne_of_mem_of_not_mem i_in_I f_in_I)
    rw [image_eq] at I_image_Indep
    exact I_image_Indep.of_delete
--another definition of "modularity" exists in the repo- is such that a base is modular over a set
--subsets if for any subset of that set, the intersection of the base with the intersection of
--that subset is a base for the intersection of the subset - cant find what exactly this means wrt
--modular pairs
