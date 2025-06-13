import Matroid.Axioms.Circuit
import Matroid.Uniform

variable {α : Type*} {X I J C Y : Set α}

universe u


namespace Matroid

open Set Function

/-- A free spike with legs indexed by a type `ι` - the ground set is `univ : Set (ι × Bool)`
and the legs are the pairs `{⟨i,true⟩, ⟨i, false⟩}` for `i : ι`.
The bases are precisely the sets that differ from a transversal of the legs by a single exchange. -/
def freeSpike (ι : Type*) : Matroid (ι × Bool) :=
  ((circuitOn (univ : Set ι)).comap Prod.fst)✶.truncate

def double_circuitOn (ι : Type*) : Matroid (ι × Bool) :=
  (circuitOn (univ : Set ι)).comap Prod.fst

lemma freeSpike_ground_set (ι : Type*) : (freeSpike ι).E = univ := rfl

lemma double_circuitOn_ground_set (ι : Type*) : (double_circuitOn ι).E = univ := rfl

lemma freeSpike_to_double (ι : Type*) : (double_circuitOn ι)✶.truncate = freeSpike ι := by
  exact rfl
lemma freeSpike_def (ι : Type*) : double_circuitOn ι = (circuitOn (univ : Set ι)).comap Prod.fst
    := by
  exact rfl

lemma double_circuitOn_isBase_iff (ι : Type*) (B : Set (ι × Bool)) :
    (double_circuitOn ι).IsBase B ↔
    (∃ i : ι, ((i, true) ∉ B ∧ (i, false) ∉ B) ∧
    (∀ j : ι, j ≠ i → (Xor' ((j,false) ∈ B) ((j, true) ∈ B)) ) )
    := by
    constructor
    · intro hB
      have hC : (univ : Set ι).Nonempty := by sorry
      have h1 := ((circuitOn (univ : Set ι)).comap_isBase_iff.1 hB).2.1
      have h2: (circuitOn (univ : Set ι)).E = univ := by exact rfl
      obtain h3 := ((circuitOn (univ : Set ι)).comap_isBase_iff.1 hB  ).1
      simp at h3
      nth_rewrite 2 [ ←h2 ] at h3
      rw [isBasis_ground_iff ] at h3
      obtain ⟨ i, hi1, hi2 ⟩ := (circuitOn_isBase_iff hC).1 h3
      refine ⟨ i, ⟨ ?_, ?_ ⟩, ?_ ⟩
      · by_contra hitB
        have hhe: i ∈ Prod.fst '' B := by
          refine (mem_image Prod.fst B i).mpr ?_
          use (i, true)
        exact hi1 hhe
      · by_contra hitB
        have hhe: i ∈ Prod.fst '' B := by
          refine (mem_image Prod.fst B i).mpr ?_
          use (i, false)
        exact hi1 hhe
      intro j hij
      unfold Xor'
      have hjin : j ∈ insert i (Prod.fst '' B) := by
        rw [hi2]
        exact trivial
      obtain ⟨x, hxB, hxB1 ⟩ := (mem_image Prod.fst B j).1 (mem_of_mem_insert_of_ne hjin hij )
      have hcases : x.2 = true ∨ x.2 = false := by exact Bool.eq_false_or_eq_true x.2
      cases hcases with
      | inl h =>
        right
        rw[ ←hxB1]
        rw [←h]
        refine ⟨hxB, ?_ ⟩
        by_contra hfB
        exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false
          h (Prod.snd_eq_iff.mpr (h1 hxB hfB rfl) )
      | inr h =>
        left
        rw[ ←hxB1]
        rw [←h]
        refine ⟨hxB, ?_ ⟩
        by_contra hfB
        exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false
          (Prod.snd_eq_iff.mpr (h1 hxB hfB rfl) ) h
    intro h
    obtain ⟨ i, ⟨hit, hif⟩, hj ⟩ := h
    apply (circuitOn (univ : Set ι)).comap_isBase_iff.2
    simp
    constructor
    · have h1: (circuitOn (univ : Set ι)).E = univ := by exact rfl
      nth_rewrite 2 [ ←h1 ]
      apply isBasis_ground_iff.2
      have hC : (univ : Set ι).Nonempty := by sorry
      apply (circuitOn_isBase_iff hC).2
      simp
      refine ⟨i,⟨ hif, hit ⟩ , ?_  ⟩
      refine eq_univ_iff_forall.mpr ?_
      intro j
      by_cases hij : j = i
      · rw [hij]
        exact mem_insert i (Prod.fst '' B)
      have ht:= (hj j hij).or
      apply mem_insert_iff.2
      simp_all only [ne_eq, circuitOn_ground, mem_insert_iff, mem_image,
      Prod.exists, exists_and_right, Bool.exists_bool, exists_eq_right, or_true]
    intro e heB f hf hef
    have h1: e.2 = f.2 := by
      have hei : e.1 ≠ i := by
        by_contra h2
        have hcases : e.2 = true ∨ e.2 = false := by exact Bool.eq_false_or_eq_true e.2
        cases hcases with
        | inl h =>
          have h3: (i, true) ∈ B := by
            rw[ ←h2, ←h]
            exact heB
          exact hit h3
        | inr h =>
          have h3: (i, false) ∈ B := by
            rw[ ←h2, ←h]
            exact heB
          exact hif h3
      by_contra h
      have h1 : (e.1, false) ∈ B ∧ (e.1, true) ∈ B := by
        refine ⟨ ?_, ?_ ⟩
        · have hcases : e.2 = true ∨ e.2 = false := by exact Bool.eq_false_or_eq_true e.2
          cases hcases with
        | inl h2 =>
          rw [h2] at h
          simp only [Bool.true_eq, ne_eq, Bool.not_eq_true] at h
          rwa [hef, ←h]
        | inr h2 =>
          rwa [←h2 ]
        have hcases : e.2 = true ∨ e.2 = false := by exact Bool.eq_false_or_eq_true e.2
        cases hcases with
        | inl h2 =>
          rwa [←h2 ]
        | inr h2 =>
          rw [h2] at h
          simp at h
          rwa [hef, ←h]
      exact ((xor_iff_or_and_not_and ((e.1, false) ∈ B) ((e.1, true) ∈ B)).1 (hj e.1 hei )).2 h1
    exact Prod.ext hef h1

--May be useless

lemma freeSpike_leg_im_eq (ι : Type*) (I : Set (ι × Bool) ) (hI : (freeSpike ι).Indep I) :
    ∀ i j : ι, (i,true) ∈ I → (i,false) ∈ I → (j, true) ∈ I → (j, false) ∈ I → i = j := by
  intro i j hit hif hjt hjf
  by_contra! hij
  obtain ⟨ B, hBB, hIB ⟩ :=
    ((((circuitOn (univ : Set ι)).comap Prod.fst).dual_indep_iff_exists').1
    ((truncate_indep_iff'.1) hI).1 ).2
  have hM1 := (((circuitOn (univ : Set ι)).comap_isBase_iff).1 hBB).1
  simp only [circuitOn_ground, preimage_univ, image_univ, Prod.range_fst] at hM1
  have hC : (univ : Set ι).Nonempty := ⟨i, trivial ⟩
  have h2 := (circuitOn_isBase_iff hC).1 (isBasis_ground_iff.mp hM1)
  simp only [mem_image, Prod.exists, exists_and_right, Bool.exists_bool, exists_eq_right,
    not_or] at h2
  obtain ⟨e, ⟨hef, het⟩, hu ⟩ := h2
  obtain he | hei := eq_or_ne e i
  --by_cases he : e = i
  · rw [←he] at hij
    have hun: j ∉ insert e (Prod.fst '' B) := by
      simp only [mem_insert_iff, mem_image, Prod.exists, exists_and_right, Bool.exists_bool,
      exists_eq_right, not_or]
      refine ⟨ fun a ↦ hij (id (Eq.symm a)), Disjoint.not_mem_of_mem_left hIB hjf,
      Disjoint.not_mem_of_mem_left hIB hjt ⟩
    exact (Ne.symm (ne_of_mem_of_not_mem' trivial hun)) hu
  have hun: i ∉ insert e (Prod.fst '' B) := by
    simp only [mem_insert_iff, mem_image, Prod.exists, exists_and_right, Bool.exists_bool,
      exists_eq_right, not_or]
    refine ⟨ fun a ↦ hei (id (Eq.symm a)), Disjoint.not_mem_of_mem_left hIB hif,
      Disjoint.not_mem_of_mem_left hIB hit ⟩
  exact (Ne.symm (ne_of_mem_of_not_mem' trivial hun)) hu

--lemma foo (a : α) (X : Set α ) : a ∈ X ∨ a ∉ X := by exact Classical.em (a ∈ X)

lemma freeSpike_leg_dep (ι : Type*) (i j : ι) (hij : i ≠ j) (C : Set (ι × Bool) )
    (hC : {(i, true), (i,false), (j,true), (j,false) } ⊆ C ): (freeSpike ι).Dep C := by
  by_contra hc
  have hC1 : C ⊆ (freeSpike ι).E := fun ⦃a⦄ a ↦ trivial
  have hit: (i ,true) ∈ C := by
    apply hC
    exact mem_insert (i, true) {(i, false), (j, true), (j, false)}
  have hif : (i ,false) ∈ C := by
    apply hC
    simp only [mem_insert_iff, mem_singleton_iff, and_true, false_or, true_or, or_true]
  have hjt: (j ,true) ∈ C := by
    apply hC
    simp only [mem_insert_iff, mem_singleton_iff, and_true, false_or, true_or, or_true]
  have hjf : (j ,false) ∈ C := by
    apply hC
    simp only [mem_insert_iff, mem_singleton_iff, and_true, false_or, true_or, or_true]
  exact hij (freeSpike_leg_im_eq ι C (((freeSpike ι).not_dep_iff).1 hc) i j hit hif hjt hjf)

lemma freeSpike_basis (ι : Type*) (B : Set (ι × Bool) ) :
    (freeSpike ι).IsBase B ↔ (freeSpike ι)✶.IsBase B := by
  have ha : (double_circuitOn ι)✶.RankPos := by sorry
  unfold double_circuitOn at ha
  refine ⟨ ?_, ?_ ⟩
  · intro hB
    obtain ⟨e, heB, heb⟩ := truncate_isBase_iff.1 hB
    rw [←freeSpike_to_double ]
    have hhelp : (circuitOn univ).comap Prod.fst = double_circuitOn ι := by exact rfl
    rw [hhelp] at heb
    have hhB : ( insert e B) ⊆ (double_circuitOn ι).E := by
      rw [double_circuitOn_ground_set]
      exact fun ⦃a⦄ a ↦ trivial
    obtain ⟨i, ⟨ hi, hii ⟩, hij ⟩ :=
      (double_circuitOn_isBase_iff ι ((double_circuitOn ι).E \ insert e B)).1
      (((double_circuitOn ι ).dual_isBase_iff hhB).1 heb )

    apply (freeSpike ι).dual_isBase_iff.2
    apply truncate_isBase_iff.2
    have hg  := double_circuitOn_ground_set ι

    by_cases he : (e ∈ ({(i, true), (i, false)} : Set (ι × Bool)))
    · have hnx : ∃ x ∈ B, x.1 ≠ i := by sorry
      --have hnx : ∃ x ∈ B, x ∉ ({(i, true), (i, false)} : Set (ι × Bool)) := by sorry
      obtain ⟨x, hxB, hx1 ⟩ := hnx
      use x
      refine ⟨?_, ?_ ⟩
      · refine not_mem_diff_of_mem hxB
      apply ((circuitOn univ).comap Prod.fst).dual_isBase_iff.2
      rw [←freeSpike_def ι]
      rw [double_circuitOn_ground_set ι, freeSpike_ground_set ι]
      have hannoying : (univ \ insert x (univ \ B)) = B \ {x} := by sorry
      rw [hannoying]
      apply (double_circuitOn_isBase_iff ι (B \ {x}) ).2
      refine ⟨ x.1, ⟨ ?_ , ?_ ⟩ ⟩
      · have hcases : x.2 = true ∨ x.2 = false := Bool.eq_false_or_eq_true x.2
        cases hcases with
        | inl h2 =>
          rw [←h2]
          refine ⟨ not_mem_diff_of_mem rfl, ?_ ⟩
          have h3 : (x.1, false) ∉ B := by
            have huse := hij x.1 hx1
            rw [ double_circuitOn_ground_set ι] at huse
            simp at huse
            rw [ ←h2 ] at huse
            have hhelp := ((xor_iff_or_and_not_and (¬(x.1, false) = e ∧ (x.1, false) ∉ B)
                (¬(x.1, x.2) = e ∧ (x.1, x.2) ∉ B)).1 huse).1
            cases hhelp with
            | inl h4 => exact h4.2
            | inr h4 =>
            by_contra h

            have hc1 := hij x.1 hx1
            rw [double_circuitOn_ground_set ι] at hc1
            have hg1 : (x.1, false) ∉ univ \ insert e B := by
              refine not_mem_diff_of_mem (mem_insert_of_mem e h)
            have hg2 : ((x.1, true) ∉ univ \ insert e B) := by
              refine not_mem_diff_of_mem ?_
              rw [←h2 ]
              exact mem_insert_of_mem e hxB
            have hcon1:= (xor_iff_or_and_not_and
                ((x.1, false) ∈ univ \ insert e B) ((x.1, true) ∈ univ \ insert e B)).1 hc1
            have hcon2 : ¬ (((x.1, false) ∈ univ \ insert e B ∨ (x.1, true) ∈ univ \ insert e B) ∧
                ¬((x.1, false) ∈ univ \ insert e B ∧ (x.1, true) ∈ univ \ insert e B)) := by
              apply not_and_or.2
              --right
              simp only [ not_or, true_and, not_and, not_not,
                and_imp, Classical.not_imp]
              left
              exact Classical.not_imp.mp fun a ↦ hg2 (a hg1)
              --apply not_and_or.1
            exact hcon2 hcon1
          simp_all only [subset_univ, dual_isBase_iff, ne_eq, mem_diff, mem_univ,
            mem_insert_iff, not_or, true_and,
            not_and, not_not, mem_singleton_iff, false_and, not_false_eq_true]
        | inr h2 =>
          rw [←h2]
          refine ⟨ ?_, not_mem_diff_of_mem rfl⟩

          sorry
      intro j hj1
      have huse := hij j
      apply (xor_iff_or_and_not_and ((j, false) ∈ B \ {x}) ((j, true) ∈ B \ {x})).2
      by_cases hji : j = i
      · rw [double_circuitOn_ground_set ι] at hi
        rw [double_circuitOn_ground_set ι] at hii
        have he1 : e.1 = i := by sorry
        have hiu : (i, true ) ∈ insert e B := by
          by_contra hcon
          exact hi (mem_diff_of_mem trivial hcon)
        have hiuf : (i, false ) ∈ insert e B := by
          by_contra hcon
          exact hii (mem_diff_of_mem trivial hcon)
        have hcases : e.2 = true ∨ e.2 = false := Bool.eq_false_or_eq_true e.2
        cases hcases with
        | inl h2 =>

          constructor
          · rw [hji]
            left
            have hc : (i, false) ≠ e := by sorry



            sorry
          sorry
        | inr h2 =>

        sorry

      --have hcas : hij j

      sorry

    ·
      sorry

  --Goodcase
  intro hB

  sorry


-- lemma foo (a : α) (X : Set α) (Y : Set α ) (haX : a ∈ X ) (hXY : a ∉ X \ Y) : a ∈ Y
--   := by apply?



-- lemma freeSpike_leg_circ (ι : Type*) (i j : ι) (hij : i ≠ j) (C : Set (ι × Bool) )
--     (hC : C = {(i, true), (i,false), (j,true), (j,false) }): (freeSpike ι).IsCircuit C := by
--   apply ((freeSpike ι).isCircuit_iff).2
--   refine ⟨?_, fun D hDd hDC ↦ ?_ ⟩
--   · by_contra hc
--     have hC1 : C ⊆ (freeSpike ι).E := fun ⦃a⦄ a ↦ trivial
--     --have ht: (freeSpike ι).Indep C := by exact ((freeSpike ι).not_dep_iff).1 hc
--     have hit: (i, true) ∈ C := by
--       simp_all only [ne_eq, not_dep_iff, mem_insert_iff, Prod.mk.injEq, Bool.true_eq_false,
--       and_false, and_true, mem_singleton_iff, and_self, or_self, or_false]
--     have hif: (i, false) ∈ C := by
--       simp_all only [ne_eq, not_dep_iff, mem_insert_iff, Prod.mk.injEq, Bool.true_eq_false,
--       and_false, and_true,
--       mem_singleton_iff, and_self, or_self, or_false, Bool.false_eq_true, or_true]
--     have hjt: (j ,true) ∈ C := by sorry
--     have hjf : (j ,false) ∈ C := by sorry
--     exact hij (freeSpike_leg_im_eq ι C (((freeSpike ι).not_dep_iff).1 hc) i j hit hif hjt hjf)
--   by_contra hc
--   sorry

--lemma freeSpike_self_dual (ι : Type*) :










-- def TLSpike {ι : Type*} [Finite ι] (F : Set (ι → Bool) )
--     (hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
--     : Matroid (ι × Bool) :=
--   FiniteCircuitMatroid.matroid <| (FiniteCircuitMatroid.ofNonSpanningCircuit
--   (univ)
  --(IsNonspanningCircuit := fun {(i, true), (i, false), (j, true), (j,false)}
  --(i ∈ ι) (j ∈ ι) (i ≠ j) ↦ true)
  --(IsNonspanningCircuit :=
  --{ {(i, true), (i, false), (j, true), (j,false)} | (i ∈ ι) ∧ (j ∈ ι) ∧ (i ≠ j)} )
  -- sorry
  -- sorry
  -- sorry
  -- sorry
  -- sorry
  -- sorry
  -- sorry)

  --Nat.card Set.Subsingleton
-- @[mk_iff] structure SpikeIndep {ι : Type*} (I : Set (ι × Bool)) (F : Set (ι → Bool) )
--     --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
--     where
--   (for_all_leg_im_eq :
--     ∀ i j : ι, (i,true) ∈ I → (i,false) ∈ I → (j, true) ∈ I → (j, false) ∈ I → i = j)
--   (not_indep_trans :
--     ∀ f ∈ F, range (fun i ↦ ⟨i, f i⟩ ) ≠ I )
--   --I think it should be subset

-- lemma SpikeIndep.empty {ι : Type*} (hcard : 2 ≤ Nat.card ι )
--     (F : Set (ι → Bool))
--     --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
--     : SpikeIndep ∅ F := by
--     constructor
--     exact fun i j a a_1 a_2 a_3 ↦ False.elim a
--     intro f hf
--     by_contra hce
--     simp_all only [range_eq_empty_iff, Nat.card_of_isEmpty,
--nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]

-- lemma SpikeIndep.subset {ι : Type*} (I : Set (ι × Bool) ) (J : Set (ι × Bool) ) (hJI : J ⊆ I)
--     (F : Set (ι → Bool))
--     --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
--     (hI : SpikeIndep I F )
--     : SpikeIndep J F := by
--   constructor
--   exact fun i j hit hif hjt hjf ↦
--   (hI.for_all_leg_im_eq i j (hJI hit ) (hJI hif ) (hJI hjt ) (hJI hjf ))
--   intro f hf
--   by_contra hrJ
--   rw [←hrJ] at hJI
--   --have hIR : Nat.card I ≤ Nat.card (range fun i ↦ (i, f i) ) := by sorry
--   have : I ⊆ (range fun i ↦ (i, f i)) := by
--     intro (i,bo) hiI
--     have heq : (i, bo) = (i, f i) := by
--       --simp only [Prod.mk.injEq, true_and]
--       sorry
--     --simp only [mem_range]

--     sorry
--   sorry

-- lemma SpikeIndep.aug {ι : Type*} (I : Set (ι × Bool) ) (B : Set (ι × Bool) )
--     (F : Set (ι → Bool))
--     --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
--     (hI : SpikeIndep I F ) (hmaxI : ¬Maximal (fun (K : Set (ι × Bool)) ↦ (SpikeIndep K F) ) I)
--     (hmaxB : Maximal (fun (K : Set (ι × Bool)) ↦ (SpikeIndep K F) ) B)
--     : ∃ b ∈ B \ I, SpikeIndep (insert b I) F := by
--   sorry

-- lemma SpikeIndep.max {ι : Type*} (I : Set (ι × Bool) ) (X : Set (ι × Bool) ) (hIX : I ⊆ X)
--     (F : Set (ι → Bool))
--     --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
--     (hI : SpikeIndep I F )
--     : ∃ J : Set (ι × Bool), I ⊆ J ∧ J ⊆ X ∧
--     Maximal (fun (K : Set (ι × Bool)) ↦ SpikeIndep K F ∧ K ⊆ X) J
--     := by
--   sorry

-- def TiplessSpikeIndepMatroid {ι : Type*} (F : Set (ι → Bool) )
--     (hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
--   : IndepMatroid (ι × Bool) where
--   E := univ
--   Indep := sorry --{I : SpikeIndep I F}
--   indep_empty := sorry
--   indep_subset := sorry
--   indep_aug := sorry
--   indep_maximal := sorry
--   subset_ground := sorry
