import Matroid.Simple
import Mathlib.combinatorics.hall.basic
import Matroid.Constructions.Uniform
import Mathlib.Order.RelClasses
import Mathlib.SetTheory.Ordinal.Basic


namespace Matroid
open Finset

def Transverses' (T : Finset α) {ι : Type _} (fam : ι → Finset α): Prop :=
  ∃ (m : α → ι), Set.InjOn m T.toSet ∧ (∀ a, a ∈ T → a ∈ fam (m a))

def Transverses (T : Finset α) {ι : Type _} (fam : ι → Finset α) : Prop :=
  ∃ (m : T → ι), m.Injective ∧ (∀ a, a.1 ∈ fam (m a))

lemma transverses_mono {T S : Finset α} {fam : ι → Finset α} (h : S ⊆ T) (ht : Transverses T fam) :
    Transverses S fam := by
  obtain ⟨T_map, T_map_inj, h_T_map⟩ := ht
  refine' ⟨fun s ↦ T_map ⟨s, h s.2⟩, fun a b abeq ↦ Subtype.ext_val (Subtype.mk_eq_mk.1
  (T_map_inj abeq)), fun a ↦ h_T_map ⟨a, h a.2⟩⟩

theorem transverses_subtype_iff_transverses_of_inhabited [DecidableEq α] [Inhabited ι]
    {T : Finset α} {fam : ι → Finset α} : Transverses T fam ↔ Transverses' T fam := by
  refine' ⟨_, _⟩
  · rintro ⟨m, m_inj, h_m⟩
    set m' : α → ι := fun a ↦ if h : (a ∈ T) then (m ⟨a, h⟩) else default
    refine' ⟨m', fun a a_mem b b_mem abeq ↦ _, fun a a_mem ↦ _⟩
    · dsimp at abeq
      simp only [mem_coe.1 b_mem, mem_coe.1 a_mem, dite_true] at abeq
      apply Subtype.mk_eq_mk.1 (m_inj abeq)
    · nth_rw 1 [← (@Subtype.coe_mk _ (fun a ↦ a ∈ T) a a_mem)]
      simp only [mem_coe.1 a_mem, dite_true]
      exact h_m ⟨a, a_mem⟩
  · rintro ⟨m, m_inj, h_m⟩
    set m' : T → ι := fun a ↦ m a.val
    refine' ⟨m', fun a b abeq ↦ _, fun a ↦ _⟩
    · rw [Subtype.mk_eq_mk]
      exact m_inj a.2 b.2 abeq
    · exact h_m a a.2



def neighbors [Fintype ι] [DecidableEq α] (fam : ι → Finset α) (a : α) : Finset ι :=
    {i | a ∈ fam i}.toFinset

theorem hall_subset {ι : Type u}  {α : Type v}
[DecidableEq α] [Inhabited α] [DecidableEq ι] (T : Finset ι) (fam : ι → Finset α) :
    (∀ (s : Finset ι), s ⊆ T → Finset.card s ≤ Finset.card (Finset.biUnion s fam)) ↔
∃ f, Set.InjOn f T ∧ ∀ x ∈ T, f x ∈ fam x := by
  have hall:= Finset.all_card_le_biUnion_card_iff_exists_injective (fun (x : T) ↦ fam x)
  have biUnion_eq : ∀ S, Finset.biUnion (Finset.map (Function.Embedding.subtype (fun x ↦ x ∈ T))
   S) fam =
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
      rwa [← (biUnion_eq S), ← S'_def]
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
  rw [← biUnion_eq] at card
  simp only [card_subtype, subtype_map] at card
  rw [Finset.filter_true_of_mem (fun x x_mem ↦ S_sub_T x_mem)] at card
  assumption


lemma transversal_exists_iff {ι : Type u}  {α : Type v}
[DecidableEq α] [Inhabited ι] [DecidableEq ι] [Fintype ι] (T : Finset α) (fam : ι → Finset α):
Transverses' T fam ↔ ∀ S, S ⊆ T → S.card ≤ (S.biUnion (neighbors fam)).card := by
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
  rw [← (card_union_add_card_inter _ _)] at h
  apply @Nat.le_of_add_le_add_right _ b _
  apply le_trans h (add_le_add_left b_le _)

lemma card_lt_of_diff_subset_lt [DecidableEq γ] {A B C : Finset γ} (B_sub : B ⊆ A)
    (card_lt : C.card < B.card) : (A \ B).card < (A \ C).card := by
  rw [card_sdiff B_sub]
  apply lt_of_lt_of_le _ (le_card_sdiff _ _)
  refine (tsub_lt_tsub_iff_left_of_le (card_le_of_subset B_sub)).mpr card_lt


lemma hall_union_card_eq [DecidableEq α] [DecidableEq ι] [Inhabited ι] [Fintype ι]
    {f : ι → Finset α} {I : Finset α} (trans : Transverses' I f) (witness_set : Finset α)
    (witness : α → Finset α)
    (h_witness : ∀ a, a ∈ witness_set → ((((witness a) \ {a}).biUnion (neighbors f)).card =
    ((witness a) \ {a}).card ∧ witness a \ {a} ⊆ I)) :
    ((witness_set.biUnion (fun a ↦ witness a \ {a})).biUnion (neighbors f)).card =
    (witness_set.biUnion (fun a ↦ witness a \ {a})).card := by
  obtain (rfl | h) := witness_set.eq_empty_or_nonempty
  ·  rfl
  · obtain ⟨a, a_mem⟩ := Finset.Nonempty.bex h
    set T:= witness_set.erase a with T_def
    have w_eq := Finset.insert_erase a_mem
    have T_card := Finset.card_insert_of_not_mem (not_mem_erase a witness_set)
    rw [← T_def] at w_eq T_card
    apply le_antisymm
    · rw [← w_eq, biUnion_insert]
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
        · have term: card T < card witness_set
          · rw [← w_eq, T_card]
            norm_num
          have _ := term --oddly, termination is only found if the context giving termination
          apply hall_union_card_eq trans T witness _ --is provided in a term proof not tactic
          intro a a_T
          apply h_witness a _
          rw [← w_eq]
          exact mem_insert_of_mem a_T
        rw [h_T, Nat.add_le_add_iff_left]
        apply le_of_eq (h_witness a _).1
        rw [← w_eq]
        exact Finset.mem_insert_self _ _
      nth_rw 2 [union_comm]
      apply card_le_union_of_card_add_inter_le_add card_le _
      apply (transversal_exists_iff _ _).1 trans
      intro x x_mem
      obtain ⟨_, x_a⟩ := Finset.mem_inter.1 x_mem
      apply (h_witness a _).2 x_a
      rw [← w_eq]
      exact Finset.mem_insert_self _ _
    apply (transversal_exists_iff _ _).1 trans
    rw [← w_eq, biUnion_subset]
    intro x x_mem
    apply (h_witness x _).2
    rw [← w_eq]
    exact x_mem
termination_by _ => (witness_set.card)
-- decreasing_by  --not well done, is extra hypothesis in lemma for this reason
--   simp_wf
--   rw [← witness_set_card, card_eq]
--   simp


def matroid_of_transversals_finite [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (f : ι → Finset α) (E : Set α) : Matroid α :=
  matroid_of_indep_finset E
  (fun S ↦ S.toSet ⊆ E ∧ Transverses S f)
  (by
    refine' ⟨_, ⟨fun a ↦ absurd a.2 (not_mem_empty a.1), fun a ↦ absurd a.2 (not_mem_empty a.1),
    fun a ↦ absurd a.2 (not_mem_empty a.1)⟩⟩
    rw [coe_empty]
    exact Set.empty_subset _
    )
  (fun I J J_trans I_sub ↦ ⟨subset_trans I_sub J_trans.1, transverses_mono I_sub J_trans.2⟩)
  (by
    obtain (empty | nonempty) := isEmpty_or_nonempty ι
    · rintro I J _ ⟨_, ⟨J_map, _⟩⟩ I_lt_J
      have J_empty : J = ∅
      · have:= J_map.isEmpty
        rw [eq_empty_iff_forall_not_mem]
        intro x x_J
        apply this.elim' ⟨x, x_J⟩
      rw [J_empty, card_empty] at I_lt_J
      exact absurd I_lt_J (Nat.not_lt_zero _)
    · inhabit ι
      simp_rw [transverses_subtype_iff_transverses_of_inhabited]
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
        have no_trans := h_false e (Finset.mem_sdiff.1 e_mem_diff).1 (Finset.mem_sdiff.1
         e_mem_diff).2
        rw [transversal_exists_iff (insert e I) f] at no_trans
        push_neg at no_trans
        have insert_sub: (insert e I).toSet ⊆ E
        · rw [coe_insert]
          apply Set.insert_subset (J_trans.1 (Finset.mem_sdiff.1 e_mem_diff).1) I_trans.1
        obtain ⟨S, S_sub, h_S⟩ := no_trans insert_sub
        refine' ⟨S, S_sub, h_S, _⟩
        have e_in_S : e ∈ S
        · by_contra e_nS
          rw [Finset.subset_insert_iff_of_not_mem e_nS] at S_sub
          --w [transversal_exists_iff _ _] at I_trans
          apply (not_le_of_lt h_S) (((transversal_exists_iff _ _).1 I_trans.2) S S_sub)
        have card_eq_plus_one : card S = card (S \ {e}) + 1
        · rw [Finset.card_sdiff, card_singleton, Nat.sub_add_cancel _]
          apply le_trans _ (Finset.card_le_of_subset (Finset.singleton_subset_iff.2 e_in_S))
          rw [card_singleton]
          rwa [singleton_subset_iff]
        rw [card_eq_plus_one, Nat.lt_add_one_iff] at h_S
        have card_eq' : (S \ {e}).card = ((S \ {e}).biUnion (neighbors f)).card
        · have card_le : card (S \ {e}) ≤ card (Finset.biUnion (S \ {e}) (neighbors f)) :=
          ((transversal_exists_iff _ _).1 I_trans.2) (S \ {e}) (fun s s_mem ↦ mem_of_mem_insert_of_ne
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
        apply hall_union_card_eq I_trans.2 (J \ I) _
        intro a a_sub
        constructor
        · symm
          have card_eq:= (h_witness a a_sub).2.2.2
          apply le_antisymm
          · apply (transversal_exists_iff _ _).1 I_trans.2
            rw [sdiff_singleton_eq_erase, ← subset_insert_iff]
            exact (h_witness a a_sub).1
          · apply le_trans (card_le_of_subset (biUnion_subset_biUnion_of_subset_left _
            (sdiff_subset (witness a) {a}))) (le_of_eq card_eq.symm)
        rw [sdiff_singleton_eq_erase, ← subset_insert_iff]
        exact (h_witness a a_sub).1
      apply not_lt_of_le (((transversal_exists_iff J _).1 J_trans.2) (W \ (I \ J)) _)
      · apply lt_of_le_of_lt _ (card_lt_of_diff_subset_lt JI_sub_W diff_card_lt)
        rw [W_diff_card]
        have W_sdiff_neighbors_eq : (W \ (J \ I)).biUnion (neighbors f) = W.biUnion (neighbors f)
        · apply subset_antisymm (biUnion_subset_biUnion_of_subset_left _ (sdiff_subset _ _)) _
          rw [W_eq, W_def]
          intro n n_mem
          rw [biUnion_biUnion, mem_biUnion] at n_mem ⊢
          obtain ⟨j, j_mem, h_j⟩ := n_mem
          refine' ⟨j, j_mem, _⟩
          have neighbor_eq : (witness j \ {j}).biUnion (neighbors f) = (witness j).biUnion
           (neighbors f)
          · apply eq_of_subset_of_card_le (biUnion_subset_biUnion_of_subset_left _
             (sdiff_subset _ _))
            rw [← (h_witness j j_mem).2.2.2]
            apply (transversal_exists_iff _ _).1 I_trans.2
            rw [sdiff_singleton_eq_erase, ← subset_insert_iff]
            exact (h_witness j j_mem).1
          rwa [neighbor_eq]
        rw [W_sdiff_neighbors_eq]
        exact card_le_of_subset (biUnion_subset_biUnion_of_subset_left _ (sdiff_subset _ _))
      · intro w w_mem
        by_cases w_in_J : w ∈ J
        · assumption
        · obtain ⟨w_W, w_IJ⟩ := mem_sdiff.1 w_mem
          exfalso
          apply w_IJ
          rw [mem_sdiff]
          refine' ⟨W_diff_sub_I _, w_in_J⟩
          rw [mem_sdiff]
          exact ⟨w_W, not_mem_sdiff_of_not_mem_left w_in_J⟩
  )

  (
    by
    rintro I ⟨I_sub, _, _, _⟩ i i_mem_I
    exact (I_sub (mem_coe.1 i_mem_I))
  )

@[simp] theorem transversal_indep_iff [DecidableEq α] [DecidableEq ι] [Fintype ι]
    {f : ι → Finset α} {E : Set α} {I : Finset α} :
    (matroid_of_transversals_finite f E).Indep I ↔ I.toSet ⊆ E ∧ Transverses I f := by
  simp only [matroid_of_transversals_finite, coe_biUnion, coe_univ, Set.mem_univ, Set.iUnion_true,
    matroid_of_indep_finset_apply', coe_subset]
  exact ⟨fun s_trans ↦ s_trans I subset_rfl, fun I_trans J J_sub ↦
   ⟨subset_trans J_sub I_trans.1, transverses_mono J_sub I_trans.2⟩⟩

@[simp] theorem transversal_ground_eq [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (f : ι → Finset α) (E : Set α) : (matroid_of_transversals_finite f E).E = E := by rfl


def Matroid.is_Transversal [DecidableEq α] (M : Matroid α) : Prop :=
    ∃ (k : ℕ) (f : (Fin k) → Finset α),
    M = matroid_of_transversals_finite f M.E

theorem unif_is_transversal [DecidableEq α] (E : Finset α) (k : ℕ) :
    Matroid.is_Transversal (unif_on E.toSet k) := by
  refine' ⟨k, (fun (_ : Fin k) ↦ E), _⟩
  rw [eq_iff_indep_iff_indep_forall, transversal_ground_eq, unif_on_ground_eq]
  refine' ⟨by rfl, fun I hIE ↦ _⟩
  obtain ⟨I', hI'⟩ := Set.Finite.exists_finset_coe (Set.Finite.subset (Finset.finite_toSet E) hIE)
  refine' ⟨fun hU ↦ _, fun hT ↦ _⟩
  · rw [unif_on_indep_iff, Set.encard_le_coe_iff_finite_ncard_le, ← hI', Set.ncard_coe_Finset] at hU
    rw [← hI', transversal_indep_iff, coe_subset]
    refine' ⟨hU.2, _⟩
    haveI linOrder: LinearOrder α:= IsWellOrder.linearOrder (WellOrderingRel)
    set map := (I'.orderIsoOfFin (rfl)).symm.toOrderEmbedding
    set finmap := Fin.castLEEmb hU.1.2
    set map': I' ↪o Fin k := RelEmbedding.trans map finmap
    refine' ⟨map', map'.inj', fun a ↦ _⟩
    dsimp
    exact coe_subset.1 hU.2 a.2
  · rw [unif_on_indep_iff, ← hI', Set.encard_le_coe_iff_finite_ncard_le, Set.ncard_coe_Finset]
    nth_rw 2 [hI']
    refine' ⟨⟨Finset.finite_toSet I', _⟩, hIE⟩
    rw [← hI', transversal_indep_iff] at hT
    obtain ⟨_, ⟨I'_map, I'_map_inj, _⟩⟩ := hT
    have card_le:= Finite.card_le_of_injective I'_map I'_map_inj
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_fin] at card_le
    exact card_le
