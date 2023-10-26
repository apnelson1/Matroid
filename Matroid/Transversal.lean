import Matroid.Simple
import Mathlib.combinatorics.hall.basic
namespace Matroid
open Finset



def transverses (T : Finset α) {ι : Type _} (fam : ι → Finset α): Prop :=
  ∃ (m : α → ι), Set.InjOn m T.toSet ∧ (∀ a, a ∈ T → a ∈ fam (m a))



def neighbors [Fintype ι] [DecidableEq α] (fam : ι → Finset α) (a : α) : Finset ι :=
    {i | a ∈ fam i}.toFinset

theorem hall_subset {ι : Type u}  {α : Type v}
[DecidableEq α] [Inhabited α] [DecidableEq ι] (T : Finset ι) (fam : ι → Finset α) : (∀ (s : Finset ι), s ⊆ T →
Finset.card s ≤ Finset.card (Finset.biUnion s fam)) ↔
∃ f, Set.InjOn f T ∧ ∀ x ∈ T, f x ∈ fam x := by
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
    set f' : ι → α := fun x ↦ if h: (x ∈ T) then f ⟨x, h⟩ else default
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


lemma transversal_exists_iff {ι : Type u}  {α : Type v}
[DecidableEq α] [Inhabited ι] [DecidableEq ι] [Fintype ι] (T : Finset α) (fam : ι → Finset α):
transverses T fam ↔ ∀ S, S ⊆ T → S.card ≤ (S.biUnion (neighbors fam)).card := by
  constructor
  · rintro ⟨T_map, T_map_inj, h_T_map⟩
    apply (hall_subset T (neighbors fam)).2 ⟨T_map, T_map_inj, _⟩
    intro x x_T
    unfold neighbors
    rw [Set.mem_toFinset]
    exact h_T_map x x_T
  · intro h
    obtain ⟨f, f_inj, h_f⟩:= (hall_subset T (neighbors fam)).1 h
    refine' ⟨f, f_inj, _⟩
    intro x x_T
    have mem:= h_f x x_T
    unfold neighbors at mem
    rw [Set.mem_toFinset] at mem
    exact mem















lemma eq_union_inter_diff [DecidableEq α] (S T : Finset α): S = (S \ T) ∪ (S ∩ T):= by
  refine' (ext (fun a ↦ _)).symm
  · constructor
    · rintro a_mem
      rw [mem_union] at a_mem
      obtain (diff | inter) := a_mem
      · exact (Finset.mem_sdiff.1 diff).1
      · exact (Finset.mem_inter.1 inter).1
    · intro a_S
      by_cases a ∈ T
      refine Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨a_S, h⟩))
      refine Finset.mem_union.2 (Or.inl (Finset.mem_sdiff.2 ⟨a_S, h⟩))


def matroid_of_transversals_finite {ι a : Type _} [DecidableEq α] [DecidableEq ι] [Inhabited ι] [Fintype ι]
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
    rintro I J I_trans J_trans I_lt_J
    by_contra h_false
    push_neg at h_false
    have diff_card_lt : (I \ J).card < (J \ I).card
    · rw [eq_union_inter_diff I J] at I_lt_J
      nth_rw 3 [eq_union_inter_diff J I] at I_lt_J
      rw [Finset.card_disjoint_union (Finset.disjoint_sdiff_inter _ _), Finset.card_disjoint_union
      (Finset.disjoint_sdiff_inter _ _), Finset.inter_comm] at I_lt_J
      exact lt_of_add_lt_add_right I_lt_J
    have h_hall : ∀ e ∈ J \ I, ∃ I_e, I_e ⊆ insert e I ∧
    (I_e.biUnion (neighbors f)).card < I_e.card ∧ e ∈ I_e ∧
    (I_e \ {e}).card = ((I_e \ {e}).biUnion (neighbors f)).card
    · intro e e_mem_diff
      have no_trans := h_false e (Finset.mem_sdiff.1 e_mem_diff).1 (Finset.mem_sdiff.1 e_mem_diff).2
      rw [transversal_exists_iff (insert e I) f] at no_trans
      push_neg at no_trans
      obtain ⟨S, S_sub, h_S⟩ := no_trans
      refine' ⟨S, S_sub, h_S, _⟩
      have e_in_I_e : e ∈ S
      · by_contra e_nS
        rw [Finset.subset_insert_iff_of_not_mem e_nS] at S_sub
        --w [transversal_exists_iff _ _] at I_trans
        apply (not_le_of_lt h_S) (((transversal_exists_iff _ _).1 I_trans) S S_sub)
      refine' ⟨e_in_I_e, _⟩
      have card_le : card (S \ {e}) ≤ card (Finset.biUnion (S \ {e}) (neighbors f))
      · have Sde_sub : (S \ {e}) ⊆ I
        . intro s s_mem
          apply mem_of_mem_insert_of_ne (S_sub (Finset.mem_sdiff.1 s_mem).1) (Finset.not_mem_singleton.1
          (Finset.mem_sdiff.1 s_mem).2)
        exact ((transversal_exists_iff _ _).1 I_trans) (S \ {e}) Sde_sub
      apply le_antisymm card_le
      have card_eq_plus_one : card S = card (S \ {e}) + 1
      · rw [Finset.card_sdiff, card_singleton]







  )

   sorry


/-
def Function.total_transversal {S : Set α} {ι : Type _} (T : Set α) (T_map : α → ι)
    (f : family_over ι S) : Prop :=
  Function.transversal T T_map f ∧ T.BijOn T_map univ

def Set.total_transverses (T : Set α) {S : Set α} {ι : Type _} (f : family_over ι S) : Prop :=
  ∃ (T_map : α → ι), Function.total_transversal T T_map f
-/
