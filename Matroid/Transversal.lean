import Matroid.Simple
import Mathlib.combinatorics.hall.basic
namespace Matroid
open Finset



def transverses (T : Finset α) {ι : Type _} (fam : ι → Finset α): Prop :=
  ∃ (m : α → ι), Set.InjOn m T.toSet ∧ (∀ a, a ∈ T → a ∈ fam (m a))



def neighbors [Fintype ι] [DecidableEq α] (fam : ι → Finset α) (a : α) : Finset ι :=
    {i | a ∈ fam i}.toFinset

theorem transverses_iff_hall {ι : Type _} [Fintype ι] [DecidableEq α] [DecidableEq ι]  (T : Finset α)
    (fam : ι → Finset α): transverses T fam ↔ ∀ S, S ⊆ T → S.card ≥ (S.biUnion (neighbors fam)).card
    := by
  constructor
  · rintro ⟨T_map, T_map_inj, h_T_map⟩
    have hall:= (Finset.all_card_le_biUnion_card_iff_exists_injective (neighbors fam)).2 ⟨T_map, ?_⟩









def matroid_of_transversals_finite {ι a : Type _} [DecidableEq α] [Inhabited ι] [Fintype ι]
    (f : ι → Finset α) : Matroid α :=
  matroid_of_indep_finset (Finset.univ.biUnion f)
  (fun S ↦ transverses S f)
  (⟨(fun a ↦ default), ⟨fun a a_mem ↦ absurd a_mem (not_mem_empty a),
    fun a a_mem ↦ absurd a_mem (not_mem_empty a)⟩⟩)
  (by
    rintro I J ⟨J_map, J_map_inj, h_J_map⟩ I_sub
    refine' ⟨J_map, J_map_inj.mono I_sub, fun a a_T ↦ h_J_map a (I_sub a_T)⟩
  )
  (by
    rintro I J ⟨I_map, I_map_inj, h_I_map⟩ ⟨J_map, J_map_inj, h_J_map⟩ I_lt_J
    sorry
  )

   sorry


/-
def Function.total_transversal {S : Set α} {ι : Type _} (T : Set α) (T_map : α → ι)
    (f : family_over ι S) : Prop :=
  Function.transversal T T_map f ∧ T.BijOn T_map univ

def Set.total_transverses (T : Set α) {S : Set α} {ι : Type _} (f : family_over ι S) : Prop :=
  ∃ (T_map : α → ι), Function.total_transversal T T_map f
-/

def Function.pairs (f : α → β) := {x : Prod α β | f x.1 = x.2}




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
