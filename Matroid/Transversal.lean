import Matroid.Simple
open Set
namespace Matroid

structure family_over (ι : Type _) (S : Set α) where
  (index : ι → Set α)
  (mem_subset : ∀ ι, index ι ⊆ S)

def Function.transversal {S : Set α} {ι : Type _} (T : Set α) (T_map : α → ι)
    (f : family_over ι S): Prop :=
  (∀ t ∈ T, t ∈ f.index (T_map t)) ∧ T.InjOn T_map

def Set.transverses (T : Set α) {S : Set α} {ι : Type _} (f : family_over ι S) : Prop :=
  ∃ (T_map : α → ι), Function.transversal T T_map f

/-
def Function.total_transversal {S : Set α} {ι : Type _} (T : Set α) (T_map : α → ι) 
    (f : family_over ι S) : Prop :=
  Function.transversal T T_map f ∧ T.BijOn T_map univ

def Set.total_transverses (T : Set α) {S : Set α} {ι : Type _} (f : family_over ι S) : Prop :=
  ∃ (T_map : α → ι), Function.total_transversal T T_map f
-/



lemma transversal_not_maximal_of_open_pair [DecidableEq α]{T : Set α} {f : family_over ι S} {T_map : α → ι}
    (T_map_trans : Function.transversal T T_map f) {s : α} {i : ι} (s_i : s ∈ f.index i)
    (s_nT : s ∉ T) (i_nT : i ∉ T_map '' T) : 
    T ∉ maximals (fun x x_1 ↦ x ⊆ x_1) {I | Set.transverses I f} := by
  intro T_max
  set T_map' := Function.update T_map s i
  apply (ne_insert_of_not_mem T s_nT) (subset_antisymm (subset_insert s T) _)
  apply T_max.2 _ (subset_insert s T)
  use (Function.update T_map s i)
  refine' ⟨_, fun a a_mem b b_mem abeq ↦ _⟩
  rintro t ((t_eq_s : t = s)| t_mem_T)
  rwa [t_eq_s, Function.update_same]
  rw [Function.update_noteq (ne_of_mem_of_not_mem t_mem_T s_nT)]
  exact T_map_trans.1 t t_mem_T
  obtain ((a_eq_s : a = s) | a_mem_T) := a_mem
  · obtain ((b_eq_s : b = s) | b_mem_T) := b_mem
    · rw [a_eq_s, b_eq_s]
    · rw [a_eq_s, Function.update_same, Function.update_apply] at abeq
      symm at abeq
      rw [ite_eq_left_iff] at abeq
      exfalso
      exact i_nT ⟨b, b_mem_T, abeq (ne_of_mem_of_not_mem b_mem_T s_nT)⟩
  · obtain ((b_eq_s : b = s) | b_mem_T) := b_mem
    · rw [b_eq_s, Function.update_same, Function.update_apply, ite_eq_left_iff] at abeq 
      exfalso
      exact i_nT ⟨a, a_mem_T, abeq (ne_of_mem_of_not_mem a_mem_T s_nT)⟩
    · rw [Function.update_noteq (ne_of_mem_of_not_mem a_mem_T s_nT), 
    Function.update_noteq (ne_of_mem_of_not_mem b_mem_T s_nT), ] at abeq
      exact T_map_trans.2 a_mem_T b_mem_T abeq



def matroid_of_transversals {S : Set α} {ι : Type _} [Inhabited ι] (f : family_over ι S) : Matroid α :=
  matroid_of_indep S (fun I ↦ Set.transverses I f)
  (⟨(fun a ↦ default), ⟨fun t t_mem ↦ absurd t_mem (not_mem_empty t), fun a a_mem ↦ absurd a_mem (not_mem_empty a)⟩⟩) 
  (fun I J ⟨J_map, h_J_map⟩ I_sub ↦ ⟨J_map, ⟨fun t t_mem ↦ h_J_map.1 t (I_sub t_mem), Set.InjOn.mono I_sub h_J_map.2⟩⟩)
  (by
    rintro I J ⟨I_map, h_I_map⟩ I_not_max J_max
    have not_J_sub_I : ¬ J ⊆ I
    · intro J_sub_I
      apply I_not_max ⟨⟨I_map, h_I_map⟩, _⟩
      intro B B_ind I_sub_B
      exact subset_trans (J_max.2 B_ind (subset_trans J_sub_I I_sub_B)) J_sub_I
    obtain ⟨j, j_J, j_nI⟩ := not_subset_iff_exists_mem_not_mem.1 not_J_sub_I
    refine' ⟨j, ⟨j_J, j_nI⟩, _⟩
    dsimp
    



  ) 
  sorry sorry

