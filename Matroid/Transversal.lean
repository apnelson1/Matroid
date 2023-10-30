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

lemma biUnion_union_eq [DecidableEq γ] [DecidableEq β]
    {f : γ → Finset β} {A B : Finset γ} : (A ∪ B).biUnion f = (A.biUnion f) ∪ (B.biUnion f)
    := by
  apply subset_antisymm
  · intro a a_mem
    obtain ⟨a', a'_mem, h_a'⟩ := Finset.mem_biUnion.1 a_mem
    obtain (a'_A | a'_B) := Finset.mem_union.1 a'_mem
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine' ⟨a', a'_A, h_a'⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine' ⟨a', a'_B, h_a'⟩
  · intro a a_mem
    rw [Finset.mem_biUnion]
    obtain (a_A | a_B) := Finset.mem_union.1 a_mem
    · obtain ⟨a', a'_A, h_a'⟩ := Finset.mem_biUnion.1 a_A
      refine ⟨a', Finset.mem_union_left _ a'_A, h_a'⟩
    · obtain ⟨a', a'_B, h_a'⟩ := Finset.mem_biUnion.1 a_B
      refine ⟨a', Finset.mem_union_right _ a'_B, h_a'⟩

lemma biUnion_inter_sub [DecidableEq γ] [DecidableEq β]
    {f : γ → Finset β} {A B : Finset γ} : (A ∩ B).biUnion f ⊆ (A.biUnion f) ∩ (B.biUnion f)
    := by
  intro a a_mem
  obtain ⟨a', a'_mem, h_a'⟩ := Finset.mem_biUnion.1 a_mem
  rw [mem_inter]
  refine' ⟨Finset.mem_biUnion.2 ⟨a', _, h_a'⟩, Finset.mem_biUnion.2 ⟨a', _, h_a'⟩⟩
  exact Finset.mem_of_mem_inter_left a'_mem
  exact Finset.mem_of_mem_inter_right a'_mem

lemma card_le_union_of_card_add_inter_le_add [DecidableEq γ] {a b : ℕ} {S T : Finset γ}
    (h : a + b ≤ S.card + T.card) (b_le : (S ∩ T).card ≤ b) : a ≤ (S ∪ T).card := by
  rw [←(card_union_add_card_inter _ _)] at h
  apply @Nat.le_of_add_le_add_right _ b _
  apply le_trans h (add_le_add_left b_le _)

lemma hall_union_card_eq [DecidableEq α] [DecidableEq ι] [Inhabited ι] [Fintype ι]
    {f : ι → Finset α} {I : Finset α} (trans : transverses I f) (witness_set : Finset α)
    (witness : α → Finset α)
    (h_witness : ∀ a, a ∈ witness_set → ((((witness a) \ {a}).biUnion (neighbors f)).card =
    ((witness a) \ {a}).card ∧ witness a \ {a} ⊆ I)) :
    ((witness_set.biUnion (fun a ↦ witness a \ {a})).biUnion (neighbors f)).card =
    (witness_set.biUnion (fun a ↦ witness a \ {a})).card := by
  revert witness
  suffices (∀ i (witness_set : Finset α)
    (witness : α → Finset α)
    (h_witness : ∀ a, a ∈ witness_set → ((((witness a) \ {a}).biUnion (neighbors f)).card =
    ((witness a) \ {a}).card ∧ witness a \ {a} ⊆ I)), witness_set.card = i →  ((witness_set.biUnion (fun a ↦ witness a \ {a})).biUnion (neighbors f)).card =
    (witness_set.biUnion (fun a ↦ witness a \ {a})).card) by
    · intro witness h_witness
      exact this witness_set.card witness_set witness h_witness rfl
  intro i

  induction i with
  | zero => intro w_set witness _ w_set_card_eq
            rw [card_eq_zero] at w_set_card_eq
            rw [w_set_card_eq]
            rfl
  | succ n ih => intro w_set witness h_witness card_eq
                 obtain ⟨a, T, _, w_eq, T_card⟩ := Finset.card_eq_succ.1 card_eq
                 apply le_antisymm
                 · rw [←w_eq, biUnion_insert]
                   have card_le : card (Finset.biUnion (witness a \ {a} ∪ T.biUnion
                    fun a ↦ witness a \ {a}) (neighbors f)) + ((T.biUnion (fun a ↦ witness a \ {a})
                     ∩ (witness a \ {a})).biUnion
                    (neighbors f)).card ≤ (T.biUnion (fun a ↦ witness a \ {a})).card +
                     (witness a \ {a}).card
                   rw [biUnion_union_eq]
                   apply le_trans
                   · apply add_le_add_left (Finset.card_le_of_subset biUnion_inter_sub)
                   · rw [Finset.union_comm, Finset.card_union_add_card_inter _ _]
                     have h_T : card (Finset.biUnion (Finset.biUnion T fun a ↦ witness a \ {a})
                     (neighbors f)) = (T.biUnion (fun a ↦ witness a \ {a})).card
                     · apply ih T witness _ T_card
                       intro a a_T
                       apply h_witness a _
                       rw [←w_eq]
                       exact mem_insert_of_mem a_T
                     rw [h_T, Nat.add_le_add_iff_left]
                     apply le_of_eq (h_witness a _).1
                     rw [←w_eq]
                     exact Finset.mem_insert_self _ _
                   nth_rw 2 [union_comm]
                   apply card_le_union_of_card_add_inter_le_add card_le _
                   apply (transversal_exists_iff _ _).1 trans
                   intro x x_mem
                   obtain ⟨_, x_a⟩ := Finset.mem_inter.1 x_mem
                   apply (h_witness a _).2 x_a
                   rw [←w_eq]
                   exact Finset.mem_insert_self _ _
                 apply (transversal_exists_iff _ _).1 trans
                 rw [←w_eq, biUnion_subset]
                 intro x x_mem
                 apply (h_witness x _).2
                 rw [←w_eq]
                 exact x_mem



















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
    (I_e \ {e}).card = ((I_e).biUnion (neighbors f)).card
    · intro e e_mem_diff
      have no_trans := h_false e (Finset.mem_sdiff.1 e_mem_diff).1 (Finset.mem_sdiff.1 e_mem_diff).2
      rw [transversal_exists_iff (insert e I) f] at no_trans
      push_neg at no_trans
      obtain ⟨S, S_sub, h_S⟩ := no_trans
      refine' ⟨S, S_sub, h_S, _⟩
      have e_in_S : e ∈ S
      · by_contra e_nS
        rw [Finset.subset_insert_iff_of_not_mem e_nS] at S_sub
        --w [transversal_exists_iff _ _] at I_trans
        apply (not_le_of_lt h_S) (((transversal_exists_iff _ _).1 I_trans) S S_sub)
      have card_eq_plus_one : card S = card (S \ {e}) + 1
      · rw [Finset.card_sdiff, card_singleton, Nat.sub_add_cancel _]
        apply le_trans _ (Finset.card_le_of_subset (Finset.singleton_subset_iff.2 e_in_S))
        rw [card_singleton]
        rwa [singleton_subset_iff]
      rw [card_eq_plus_one, Nat.lt_add_one_iff] at h_S
      have card_eq' : (S \ {e}).card = ((S \ {e}).biUnion (neighbors f)).card
      · have card_le : card (S \ {e}) ≤ card (Finset.biUnion (S \ {e}) (neighbors f)) :=
        ((transversal_exists_iff _ _).1 I_trans) (S \ {e}) (fun s s_mem ↦ mem_of_mem_insert_of_ne
        (S_sub (Finset.mem_sdiff.1 s_mem).1) (Finset.not_mem_singleton.1
        (Finset.mem_sdiff.1 s_mem).2))
        apply le_antisymm card_le _
        apply le_trans (Finset.card_le_of_subset (Finset.biUnion_subset_biUnion_of_subset_left
        (neighbors f) (Finset.sdiff_subset S {e})))
        assumption
      refine' ⟨e_in_S, _⟩
      apply le_antisymm _ h_S
      rw [card_eq']
      apply card_le_of_subset (biUnion_subset_biUnion_of_subset_left (neighbors f)
      (sdiff_subset _ _))
    choose! witness h_witness using h_hall
    set W := (J \ I).biUnion witness with W_def
    have JI_sub_W : (J \ I) ⊆ W
    · intro j j_sub_J
      rw [W_def, mem_biUnion]
      refine' ⟨j, j_sub_J, _⟩
      exact (h_witness j j_sub_J).2.2.1
    have W_diff_sub_I : W \ (J \ I) ⊆ I
    · intro w w_sub_W
      rw [mem_sdiff, W_def, mem_biUnion] at w_sub_W
      obtain ⟨⟨a, a_JI, h_a⟩, w_mem⟩ := w_sub_W
      obtain (w_eq_a | w_mem_I) := Finset.mem_insert.1 ((h_witness a a_JI).1 h_a)
      rw [w_eq_a] at w_mem
      exact absurd a_JI w_mem
      assumption
    have W_eq : W \ (J \ I) = (J \ I).biUnion (fun j ↦ (witness j) \ {j})
    · apply subset_antisymm
      · intro w w_mem
        rw [mem_biUnion]
        rw [W_def, mem_sdiff, mem_biUnion] at w_mem
        obtain ⟨⟨a, a_JI, h_a⟩, w_mem⟩ := w_mem
        refine' ⟨a, a_JI, _⟩
        rw [mem_sdiff, mem_singleton]
        exact ⟨h_a, (ne_of_mem_of_not_mem a_JI w_mem).symm⟩
      · intro w w_mem
        rw [mem_biUnion] at w_mem
        rw [mem_sdiff, W_def, mem_biUnion]
        obtain ⟨a, a_JI, h_a⟩ := w_mem
        refine' ⟨⟨a, a_JI, (mem_sdiff.1 h_a).1⟩, _⟩
        intro w_JI
        apply (mem_sdiff.1 w_JI).2
        exact mem_of_mem_insert_of_ne ((h_witness a a_JI).1 (mem_sdiff.1 h_a).1) (
          not_mem_singleton.1 (mem_sdiff.1 h_a).2)
    have W_diff_card : (W \ (J \ I)).card = ((W \ (J \ I)).biUnion (neighbors f)).card
    · rw [W_eq]
      symm
      apply hall_union_card_eq I_trans (J \ I)
      intro a a_sub
      constructor
      · symm
        have:= (h_witness a a_sub).2.2.2
        apply le_antisymm






    /-
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
    (I_e \ {e}).card = ((I_e).biUnion (neighbors f)).card
    · intro e e_mem_diff
      have no_trans := h_false e (Finset.mem_sdiff.1 e_mem_diff).1 (Finset.mem_sdiff.1 e_mem_diff).2
      rw [transversal_exists_iff (insert e I) f] at no_trans
      push_neg at no_trans
      obtain ⟨S, S_sub, h_S⟩ := no_trans
      refine' ⟨S, S_sub, h_S, _⟩
      have e_in_S : e ∈ S
      · by_contra e_nS
        rw [Finset.subset_insert_iff_of_not_mem e_nS] at S_sub
        --w [transversal_exists_iff _ _] at I_trans
        apply (not_le_of_lt h_S) (((transversal_exists_iff _ _).1 I_trans) S S_sub)
      refine' ⟨e_in_S, _⟩
      have card_eq_plus_one : card S = card (S \ {e}) + 1
        · rw [Finset.card_sdiff, card_singleton, Nat.sub_add_cancel _]
          apply le_trans _ (Finset.card_le_of_subset (Finset.singleton_subset_iff.2 e_in_S))
          rw [card_singleton]
          rwa [singleton_subset_iff]
      rw [card_eq_plus_one, Nat.lt_add_one_iff] at h_S
      have card_eq' : (S \ {e}).card = ((S \ {e}).biUnion (neighbors f)).card
      · have card_le : card (S \ {e}) ≤ card (Finset.biUnion (S \ {e}) (neighbors f)) :=
        ((transversal_exists_iff _ _).1 I_trans) (S \ {e}) (fun s s_mem ↦ mem_of_mem_insert_of_ne
        (S_sub (Finset.mem_sdiff.1 s_mem).1) (Finset.not_mem_singleton.1
        (Finset.mem_sdiff.1 s_mem).2))
        apply le_antisymm card_le _
        apply le_trans (Finset.card_le_of_subset (Finset.biUnion_subset_biUnion_of_subset_left
        (neighbors f) (Finset.sdiff_subset S {e})))
        assumption
    choose! witness h_witness using h_hall
    set W := (J \ I).biUnion witness
    have W_card : W.card = (W.biUnion (neighbors f)).card
    -/

    /-set W:= (((J \ I).biUnion witness) \ (I \ J)) with W_def
    have W_sub_J : W ⊆ J
    · intro w w_mem_W
      rw [W_def, mem_sdiff, mem_biUnion] at w_mem_W
      obtain ⟨⟨j, j_mem_JI, w_witness_j⟩, w_not_mem_IJ⟩ := w_mem_W
      obtain (w_eq_j | w_mem_I) := Finset.mem_insert.1 ((h_witness j j_mem_JI).1 w_witness_j)
      · rw [w_eq_j]
        exact (Finset.mem_sdiff.1 j_mem_JI).1
      · rw [mem_sdiff] at w_not_mem_IJ
        push_neg at w_not_mem_IJ
        exact w_not_mem_IJ w_mem_I
    apply not_lt_of_le (((transversal_exists_iff _ _).1 J_trans W W_sub_J))
    nth_rewrite 2 [W_def]
    apply lt_of_le_of_lt Finset.card_biUnion_le
    -/




  )

   sorry

#check ENat.le_of_lt_add_one

/-
def Function.total_transversal {S : Set α} {ι : Type _} (T : Set α) (T_map : α → ι)
    (f : family_over ι S) : Prop :=
  Function.transversal T T_map f ∧ T.BijOn T_map univ

def Set.total_transverses (T : Set α) {S : Set α} {ι : Type _} (f : family_over ι S) : Prop :=
  ∃ (T_map : α → ι), Function.total_transversal T T_map f
-/
