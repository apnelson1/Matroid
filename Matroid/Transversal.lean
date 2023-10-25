import Matroid.Simple
import Mathlib.combinatorics.hall.basic
namespace Matroid
open Finset



def transverses (T : Finset α) {ι : Type _} (fam : ι → Finset α): Prop :=
  ∃ (m : α → ι), Set.InjOn m T.toSet ∧ (∀ a, a ∈ T → a ∈ fam (m a))



def neighbors [Fintype ι] [DecidableEq α] (fam : ι → Finset α) (a : α) : Finset ι :=
    {i | a ∈ fam i}.toFinset

theorem hall_subset {ι : Type u}  {α : Type v}
[DecidableEq α] [DecidableEq ι] (T : Finset ι) (fam : ι → Finset α) : (∀ (s : Finset ι), s ⊆ T →
Finset.card s ≤ Finset.card (Finset.biUnion s fam)) ↔
∃ f, Set.InjOn f T ∧ ∀ x ∈ T, f x ∈ fam x := by
  haveI : (Inhabited α) := by
    inhabit α

  have hall:= Finset.all_card_le_biUnion_card_iff_exists_injective (fun (x : T) ↦ fam x)
  have biUnion_eq : ∀ S, Finset.biUnion (Finset.map (Function.Embedding.subtype (fun x ↦ x ∈ T)) S) fam =
      Finset.biUnion S (fun (x : T) ↦ fam x)
  · intro S
    apply subset_antisymm
    · rintro x y
      obtain ⟨a, a_mem, h_a⟩ :=Finset.mem_biUnion.1 y
      rw [Finset.mem_biUnion]
      rw [Finset.mem_map] at a_mem
      obtain ⟨a', a'_mem, h_a'⟩ := a_mem
      refine' ⟨a', a'_mem, _⟩
      simp at h_a'
      rwa [h_a']
    · rintro x y
      obtain ⟨a, a_mem, h_a⟩ := Finset.mem_biUnion.1 y
      rw [Finset.mem_biUnion]
      refine' ⟨a, _, h_a⟩
      simpa
  constructor
  · intro hall_condition
    have hall_condition2 : (∀ (s : Finset { x // x ∈ T }),
    card s ≤ card (Finset.biUnion s fun x ↦ fam ↑x))
    · intro S
      set S' : Finset ι := Finset.map (Function.Embedding.subtype _) S with S'_def
      have S'_sub_T : S' ⊆ T
      · intro s s_sub_S'
        rw [S'_def] at s_sub_S'
        apply Finset.property_of_mem_map_subtype S s_sub_S'
      have card:= hall_condition S' S'_sub_T
      rw [Finset.card_map] at card
      rwa [←(biUnion_eq S), ←S'_def]
    obtain ⟨f, f_Inj, h_f⟩ := hall.1 hall_condition2
    set f' : ι → α := fun x ↦ if h: (x ∈ T) then f ⟨x, h⟩ else default with f'_def
    refine' ⟨f', _, _⟩
    · intro a (a_mem : a ∈ T) b (b_mem : b ∈ T) abeq
      simp only [a_mem, dite_true, b_mem] at abeq
      exact Subtype.mk_eq_mk.1 (f_Inj abeq)
    · intro x x_T
      simp only [x_T, dite_true]
      exact h_f _
  rintro ⟨f, f_Inj, h_f⟩
  have exists_transversal_on_set : ∃ f, Function.Injective f ∧ ∀ (x : { x // x ∈ T }), f x ∈ fam ↑x
  · refine' ⟨fun x ↦ Subtype.restrict _ f x, _, _⟩
    · intro a b abeq
      dsimp at abeq
      apply Subtype.ext (f_Inj a.prop b.prop abeq)
    · intro x
      exact h_f x.val x.prop
  have hall_condition := hall.2 exists_transversal_on_set
  intro S S_sub_T
  set S' := S.subtype (fun x ↦ x ∈ T)
  have card:= hall_condition (S.subtype (fun x ↦ x ∈ T))
  rw [←biUnion_eq] at card
  simp only [card_subtype, subtype_map] at card
  rw [Finset.filter_true_of_mem (fun x x_mem ↦ S_sub_T x_mem)] at card
  assumption



















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
