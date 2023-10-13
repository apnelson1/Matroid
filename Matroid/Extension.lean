import Matroid.Simple
import Matroid.Minor
import Matroid.Constructions.ParallelExt
open Set
namespace Matroid

variable {M : Matroid α}

def ParallelExt (M : Matroid α) (e : α) (S : Set α) [DecidablePred (· ∈ S)] : Matroid α := 
    M.parallel_preimage (M.E ∪ S) (fun x ↦ if (x ∈ S) then e else x)

theorem Indep.parallel_substitute (hI : M.Indep I) (h_para : M.Parallel e f) (hI_e : e ∈ I):
    M.Indep (insert f (I \ {e})) := by
  by_cases e_ne_f : e = f
  · rwa [←e_ne_f, insert_diff_singleton, insert_eq_of_mem hI_e]
  · rw [indep_iff_forall_subset_not_circuit']
    refine' ⟨fun C C_sub C_circ ↦ _, _⟩
    · have e_notin_C : e ∉ C := fun e_in_C ↦ (mem_of_mem_insert_of_ne (C_sub e_in_C) e_ne_f).2 rfl
      have C_ne_ef : C ≠ {e, f}
      · intro h_f
        rw [h_f] at e_notin_C
        exact e_notin_C (mem_insert e _)
      obtain ⟨C', C'_circ, C'_sub⟩ := C_circ.elimination ((parallel_iff_circuit e_ne_f).1 h_para) C_ne_ef f
      have C'_sub_I : C' ⊆ I
      intro c c_sub_C'
      obtain ⟨(c_sub_C | c_sub_ef), (c_ne_f : c ≠ f)⟩ := C'_sub c_sub_C'
      · exact (mem_of_mem_insert_of_ne (C_sub c_sub_C) c_ne_f).1
      · have c_eq_e : c = e
        · apply eq_of_not_mem_of_mem_insert c_sub_ef _
          rwa [mem_singleton_iff]
        rwa [c_eq_e]
      exact (hI.subset C'_sub_I).not_dep C'_circ.1
    · rintro i (i_eq_f | i_sub_I)
      · rw [i_eq_f]
        exact h_para.mem_ground_right
      · exact hI.subset_ground i_sub_I.1    

lemma insert_diff_insert_diff {B : Set α} (e_in_B : e ∈ B) (f_notin_B : f ∉ B):
    insert e (insert f (B \ {e}) \ {f}) = B := by simp [e_in_B, f_notin_B]
  

lemma Equiv.image_invol [DecidableEq α] {e f : α} : Function.Involutive (Set.image (Equiv.swap e f)) := by
  have inv : Function.Involutive (Equiv.swap e f) := fun x ↦ Equiv.swap_apply_self _ _ _
  intro X
  rw [←Set.image_comp _ _, Function.Involutive.comp_self inv, image_id]

#check Function.Involutive.eq_iff Equiv.image_invol

lemma Equiv.swap_mem_image_iff [DecidableEq α] {e f : α} : x ∈ (Equiv.swap e f) '' S ↔ (Equiv.swap e f) x ∈ S := by
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · obtain ⟨x', x'_mem, hx'⟩ := h
    rwa [←hx', Equiv.swap_apply_self]
  · refine' ⟨(Equiv.swap e f) x, h, _⟩
    rw [Equiv.swap_apply_self] 

lemma Equiv.swap_image_eq_self_both_mem [DecidableEq α] (S : Set α) (e_in_S : e ∈ S) (f_in_S : f ∈ S) :
    (Equiv.swap e f)'' S = S := by
  ext x
  rw [Equiv.swap_mem_image_iff]
  by_cases x_eq_e : x = e
  · rw [x_eq_e, Equiv.swap_apply_left]
    exact ⟨fun _ ↦ e_in_S, fun _ ↦ f_in_S⟩
  · by_cases x_eq_f : x = f
    · rw [x_eq_f, Equiv.swap_apply_right]
      exact ⟨fun _ ↦ f_in_S, fun _ ↦ e_in_S⟩
    · rw [Equiv.swap_apply_of_ne_of_ne x_eq_e x_eq_f]

lemma Equiv.swap_image_eq_self_not_mem [DecidableEq α] {S : Set α} (e_notin_S : e ∉ S) (f_notin_S : f ∉ S) :
    (Equiv.swap e f)'' S = S := by
  ext x
  rw [Equiv.swap_mem_image_iff]
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · rwa [←(@Equiv.swap_apply_self _ _ e f x), Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem h e_notin_S)
  (ne_of_mem_of_not_mem h f_notin_S)]
  · rwa [Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem h e_notin_S)
  (ne_of_mem_of_not_mem h f_notin_S)]


  
lemma Equiv.swap_image_eq_self_left [DecidableEq α] {S : Set α} (e_in_S : e ∈ S) (f_notin_S : f ∉ S) :
    (Equiv.swap e f)'' S = insert f (S \ {e}) := by
  ext x
  rw [Equiv.swap_mem_image_iff]
  by_cases x_eq_f : x = f
  · refine' ⟨fun h ↦ _, fun h ↦ _⟩
    · rw [x_eq_f]
      exact mem_insert f _
    · rwa [x_eq_f, Equiv.swap_apply_right]
  · refine' ⟨fun h ↦ _, fun h ↦ _⟩
    · have x_ne_e : x ≠ e
      · intro x'_eq_e
        rw [x'_eq_e, Equiv.swap_apply_left] at h
        apply f_notin_S h
      rw [Equiv.swap_apply_of_ne_of_ne x_ne_e x_eq_f] at h
      exact mem_insert_of_mem f (mem_diff_of_mem h x_ne_e)
    · obtain ⟨x_in_S, (x_ne_e : x ≠ e)⟩ := mem_of_mem_insert_of_ne h x_eq_f
      rwa [Equiv.swap_apply_of_ne_of_ne x_ne_e x_eq_f]


lemma Equiv.swap_image_eq_self [DecidableEq α] {S : Set (Set α)} (h_B : ∀ B, B ∈ S ↔ (Equiv.swap e f) '' B ∈ S) :
    S = image (Equiv.swap e f)'' S := by
  ext B
  refine' ⟨fun B_S ↦ _, fun ⟨B', B'_mem, hB'⟩ ↦ _⟩
  · refine' ⟨(Equiv.swap e f) '' B, (h_B B).1 B_S, _⟩
    rw [Equiv.image_invol.eq_iff]
  rw [←hB']
  exact (h_B B').1 B'_mem

def parallel_swap [DecidableEq α] {M : Matroid α} {e f : α} (h_para : M.Parallel e f) : Iso M M where
  toLocalEquiv := (Equiv.swap e f).toLocalEquiv.restr M.E
  source_eq' := by
    simp
  target_eq' := by
    simp only [LocalEquiv.restr_target, Equiv.toLocalEquiv_target, Equiv.toLocalEquiv_symm_apply, Equiv.symm_swap,
      univ_inter]
    rw [preimage_eq_iff_eq_image, Equiv.swap_image_eq_self_both_mem M.E h_para.mem_ground_left h_para.mem_ground_right]
    exact Equiv.bijective _
  setOf_base_eq' := by
    apply Equiv.swap_image_eq_self _
    intro B
    by_cases e_in_B : e ∈ B
    by_cases f_in_B : f ∈ B
    · rw [Equiv.swap_image_eq_self_both_mem B e_in_B f_in_B]
    · rw [Equiv.swap_image_eq_self_left e_in_B f_in_B]
      refine' ⟨fun (B_Base : M.Base B) ↦ _, fun (B'_Base : M.Base _) ↦ _⟩
      · exact Base.exchange_base_of_indep B_Base f_in_B ((B_Base.indep).parallel_substitute h_para e_in_B) 
      · rw [←insert_diff_insert_diff e_in_B f_in_B] 
        apply Base.exchange_base_of_indep B'_Base ?_ ((B'_Base.indep).parallel_substitute h_para.symm (mem_insert f _))
        exact fun e_in_B' ↦ (mem_of_mem_insert_of_ne e_in_B' (ne_of_mem_of_not_mem e_in_B f_in_B)).2 rfl
    by_cases f_in_B : f ∈ B
    · rw [Equiv.swap_comm, Equiv.swap_image_eq_self_left f_in_B e_in_B]
      refine' ⟨fun (B_Base : M.Base B) ↦ _, fun (B'_Base : M.Base _) ↦ _⟩
      · exact Base.exchange_base_of_indep B_Base e_in_B ((B_Base.indep).parallel_substitute h_para.symm f_in_B) 
      · rw [←insert_diff_insert_diff f_in_B e_in_B] 
        apply Base.exchange_base_of_indep B'_Base ?_ ((B'_Base.indep).parallel_substitute h_para (mem_insert e _))
        exact fun f_in_B' ↦ (mem_of_mem_insert_of_ne f_in_B' (ne_of_mem_of_not_mem f_in_B e_in_B)).2 rfl
    · rw [Equiv.swap_image_eq_self_not_mem e_in_B f_in_B]


@[simp] theorem parallel_swap_apply [DecidableEq α] (h_para : M.Parallel e f) :
    (parallel_swap h_para).toLocalEquiv = (Equiv.swap e f).toLocalEquiv.restr M.E := rfl 
    -- (parallel_swap h_para).toLocalEquiv = (fun x ↦ if (x = e) then f else (if (x = f) then e else x)) := sorry
open Classical
theorem eq_parallelExt_del {M : Matroid α} {e f : α} (h_para : M.Parallel e f) (h_ne : e ≠ f): 
    M = ParallelExt (M ⟍ f) e {f} := by
  rw [ParallelExt, eq_iff_indep_iff_indep_forall, parallel_preimage_ground_eq]
  refine' ⟨_, fun I I_ground ↦ ⟨fun I_Ind ↦ _, _⟩⟩
  · simp
    exact (insert_eq_of_mem (Parallel.mem_ground_right h_para)).symm
  · rw [parallel_preimage_indep_iff]
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
    refine' ⟨_, subset_trans I_ground (subset_insert f M.E)⟩
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
        rw [dep_iff_supset_circuit]
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
        rw [dep_iff_supset_circuit]
        exact ⟨{e, f}, ef_sub_I, (parallel_iff_circuit h_ne).1 h_para⟩
      · rwa [if_neg a_eq_f] at f_ab
  -- part 2
  rw [parallel_preimage_indep_iff]
  simp only [delete_elem, mem_singleton_iff, delete_indep_iff, disjoint_singleton_right, mem_image, not_exists, not_and,
    delete_ground, union_singleton, mem_diff, not_true, and_false, insert_diff_singleton, and_imp]
  rintro I_image_Indep h_not_f h_inj I_sub
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
    have:= I_image_Indep.parallel_substitute h_para (mem_insert e _)
    have e_notin_I : e ∉ I
    · intro e_in_I
      apply h_ne (h_inj e_in_I f_in_I _)
      dsimp
      rw [if_pos rfl, if_neg h_ne]
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
    rwa [image_eq] at I_image_Indep
