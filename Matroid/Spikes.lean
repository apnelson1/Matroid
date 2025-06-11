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

--May be useless
lemma freeSpike_ground_set (ι : Type*) : (freeSpike ι).E = univ := rfl

lemma freeSpike_leg_im_eq (ι : Type*) (I : Set (ι × Bool) ) (hI : (freeSpike ι).Indep I) :
    ∀ i j : ι, (i,true) ∈ I → (i,false) ∈ I → (j, true) ∈ I → (j, false) ∈ I → i = j := by
  intro i j hit hif hjt hjf
  by_contra! hij
  obtain ⟨ B, hBB, hIB ⟩ :=
    ((((circuitOn (univ : Set ι)).comap Prod.fst).dual_indep_iff_exists').1
    ((truncate_indep_iff'.1) hI).1 ).2
  have hM1 := (((circuitOn (univ : Set ι)).comap_isBase_iff).1 hBB).1
  simp only [circuitOn_ground, preimage_univ, image_univ, Prod.range_fst] at hM1
  have hC : (univ : Set ι).Nonempty := by sorry
  have h2 := (circuitOn_isBase_iff hC).1 (isBasis_ground_iff.mp hM1)
  simp only [mem_image, Prod.exists, exists_and_right, Bool.exists_bool, exists_eq_right,
    not_or] at h2
  obtain ⟨e, ⟨hef, het⟩, hu ⟩ := h2
  by_cases he : e = i
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
    refine ⟨ fun a ↦ he (id (Eq.symm a)), Disjoint.not_mem_of_mem_left hIB hif,
      Disjoint.not_mem_of_mem_left hIB hit ⟩
  exact (Ne.symm (ne_of_mem_of_not_mem' trivial hun)) hu

lemma freeSpike_leg_circ (ι : Type*) (i j : ι) (hij : i ≠ j) (C : Set (ι × Bool) )
    (hC : C = {(i, true), (i,false), (j,true), (j,false) }): (freeSpike ι).IsCircuit C := by
  apply ((freeSpike ι).isCircuit_iff).2
  refine ⟨?_, fun D hDd hDC ↦ ?_ ⟩
  · by_contra hc
    have hC1 : C ⊆ (freeSpike ι).E := fun ⦃a⦄ a ↦ trivial
    --have ht: (freeSpike ι).Indep C := by exact ((freeSpike ι).not_dep_iff).1 hc
    have hit: (i, true) ∈ C := by
      simp_all only [ne_eq, not_dep_iff, mem_insert_iff, Prod.mk.injEq, Bool.true_eq_false,
      and_false, and_true, mem_singleton_iff, and_self, or_self, or_false]
    have hif: (i, false) ∈ C := by
      simp_all only [ne_eq, not_dep_iff, mem_insert_iff, Prod.mk.injEq, Bool.true_eq_false,
      and_false, and_true,
      mem_singleton_iff, and_self, or_self, or_false, Bool.false_eq_true, or_true]
    have hjt: (j ,true) ∈ C := by sorry
    have hjf : (j ,false) ∈ C := by sorry
    exact hij (freeSpike_leg_im_eq ι C (((freeSpike ι).not_dep_iff).1 hc) i j hit hif hjt hjf)
  by_contra hc

  sorry










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
