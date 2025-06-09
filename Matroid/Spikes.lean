import Matroid.Axioms.Circuit

variable {α : Type*} {X I J C Y : Set α}

universe u



open Set Function

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
@[mk_iff] structure SpikeIndep {ι : Type*} (I : Set (ι × Bool)) (F : Set (ι → Bool) )
    --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
    where
  (for_all_leg_im_eq :
    ∀ i j : ι, (i,true) ∈ I → (i,false) ∈ I → (j, true) ∈ I → (j, false) ∈ I → i = j)
  (not_indep_trans :
    ∀ f ∈ F, range (fun i ↦ ⟨i, f i⟩ ) ≠ I )
  --I think it should be subset

lemma SpikeIndep.empty {ι : Type*} (hcard : 2 ≤ Nat.card ι )
    (F : Set (ι → Bool))
    --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
    : SpikeIndep ∅ F := by
    constructor
    exact fun i j a a_1 a_2 a_3 ↦ False.elim a
    intro f hf
    by_contra hce
    simp_all only [range_eq_empty_iff, Nat.card_of_isEmpty, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]

lemma SpikeIndep.subset {ι : Type*} (I : Set (ι × Bool) ) (J : Set (ι × Bool) ) (hJI : J ⊆ I)
    (F : Set (ι → Bool))
    --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
    (hI : SpikeIndep I F )
    : SpikeIndep J F := by
  constructor
  exact fun i j hit hif hjt hjf ↦
  (hI.for_all_leg_im_eq i j (hJI hit ) (hJI hif ) (hJI hjt ) (hJI hjf ))
  intro f hf
  by_contra hrJ
  rw [←hrJ] at hJI
  --have hIR : Nat.card I ≤ Nat.card (range fun i ↦ (i, f i) ) := by sorry
  have : I ⊆ (range fun i ↦ (i, f i)) := by
    intro (i,bo) hiI
    have heq : (i, bo) = (i, f i) := by
      --simp only [Prod.mk.injEq, true_and]
      sorry
    --simp only [mem_range]

    sorry
  sorry

lemma SpikeIndep.aug {ι : Type*} (I : Set (ι × Bool) ) (B : Set (ι × Bool) )
    (F : Set (ι → Bool))
    --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
    (hI : SpikeIndep I F ) (hmaxI : ¬Maximal (fun (K : Set (ι × Bool)) ↦ (SpikeIndep K F) ) I)
    (hmaxB : Maximal (fun (K : Set (ι × Bool)) ↦ (SpikeIndep K F) ) B)
    : ∃ b ∈ B \ I, SpikeIndep (insert b I) F := by
  sorry

lemma SpikeIndep.max {ι : Type*} (I : Set (ι × Bool) ) (X : Set (ι × Bool) ) (hIX : I ⊆ X)
    (F : Set (ι → Bool))
    --(hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
    (hI : SpikeIndep I F )
    : ∃ J : Set (ι × Bool), I ⊆ J ∧ J ⊆ X ∧
    Maximal (fun (K : Set (ι × Bool)) ↦ SpikeIndep K F ∧ K ⊆ X) J
    := by
  sorry

def TiplessSpikeIndepMatroid {ι : Type*} (F : Set (ι → Bool) )
    (hF : ∀ ⦃C C' ⦄, C ∈ F → C' ∈ F → ∀ i : ι, (∀ j : ι, i ≠ j ∧ (C j = C' j)) → C i = C' i )
  : IndepMatroid (ι × Bool) where
  E := univ
  Indep := sorry --{I : SpikeIndep I F}
  indep_empty := sorry
  indep_subset := sorry
  indep_aug := sorry
  indep_maximal := sorry
  subset_ground := sorry
