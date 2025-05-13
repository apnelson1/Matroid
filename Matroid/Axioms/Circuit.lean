import Mathlib.Data.Matroid.IndepAxioms
import Matroid.ForMathlib.Finset
import Matroid.Circuit

variable {α : Type*} {X I J C Y : Set α}

universe u

section Set

open Set Function

/-- A general infinite matroid as described by its circuits.
Showing this definition actually corresponds to a matroid is TODO. -/
structure CircuitMatroid (α : Type u) where
  (E : Set α)
  (IsCircuit : Set α → Prop)
  (empty_not_isCircuit : ¬IsCircuit ∅)
  (circuit_antichain : IsAntichain (· ⊆ ·) {C | IsCircuit C})
  (elimination : ∀ (ι : Type u) (x : ι → α) (I : ι → Set α) (J : Set α) (z : α),
    (∀ i, IsCircuit (insert (x i) (I i))) → Injective x → (∀ i, x i ∉ I i) →
    (IsCircuit (J ∪ range x)) → (∀ i, z ∉ I i) →
    ∃ C ⊆ (J ∪ ⋃ i, I i), IsCircuit C ∧ z ∈ C )
  (circuit_subset_ground : ∀ ⦃C⦄, IsCircuit C → C ⊆ E)

/-- A finitary matroid as described by its circuits. -/
structure FiniteCircuitMatroid (α : Type*) where
  (E : Set α)
  (IsCircuit : Set α → Prop)
  (empty_not_isCircuit : ¬IsCircuit ∅)
  (circuit_antichain : IsAntichain (· ⊆ ·) {C | IsCircuit C})
  (circuit_elimination : ∀ ⦃C₁ C₂ e⦄, IsCircuit C₁ → IsCircuit C₂ → C₁ ≠ C₂ → e ∈ C₁ → e ∈ C₂ →
    ∃ C, IsCircuit C ∧ e ∉ C ∧ C ⊆ (C₁ ∪ C₂))
  (circuit_finite : ∀ ⦃C⦄, IsCircuit C → C.Finite)
  (circuit_subset_ground : ∀ ⦃C⦄, IsCircuit C → C ⊆ E)

namespace FiniteCircuitMatroid

variable {M : FiniteCircuitMatroid α}

@[mk_iff]
protected structure Indep (M : FiniteCircuitMatroid α) (I : Set α) : Prop where
  subset_ground : I ⊆ M.E
  not_isCircuit_of_subset : ∀ ⦃C⦄, C ⊆ I → ¬ M.IsCircuit C

protected lemma Indep.subset (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I :=
  ⟨hIJ.trans hJ.subset_ground, fun _ hCI hC ↦ hJ.not_isCircuit_of_subset (hCI.trans hIJ) hC⟩

protected lemma Indep.augment {J : Set α} (hI : M.Indep I) (hIfin : I.Finite) (hJ : M.Indep J)
    (hJfin : J.Finite) (hIJ : I.ncard < J.ncard) : ∃ e ∈ J, e ∉ I ∧ M.Indep (insert e I) := by
  by_cases hss : I ⊆ J
  · obtain ⟨e, he⟩ := exists_of_ssubset <| hss.ssubset_of_ne <| by rintro rfl; simp at hIJ
    exact ⟨e, he.1, he.2, hJ.subset <| insert_subset he.1 hss⟩
  obtain ⟨x, hxI, hxJ⟩ := not_subset.1 hss
  by_contra! hcon
  -- For each `y ∈ J \ I`, we can find a circuit in `J ∪ {e}` that avoids `y`,
  -- as otherwise we can replace `J` wth the set `insert x (J \ {y})`,
  -- which is closer to `I` than `J` is, and therefore satisfies the inductive hypothesis.
  have h_ex : ∀ y ∈ J \ I, ∃ C, M.IsCircuit C ∧ x ∈ C ∧ y ∉ C ∧ C \ {x} ⊆ J := by
    intro y hy
    by_cases hJ' : M.Indep (insert x (J \ {y}))
    · have hlt : ((insert x (J \ {y})) \ I).ncard < (J \ I).ncard := by
        rw [insert_diff_of_mem _ hxI, diff_diff_comm]
        exact ncard_diff_singleton_lt_of_mem hy hJfin.diff
      have hcard : I.ncard < (insert x (J \ {y})).ncard :=
        hIJ.trans_eq <| (ncard_exchange hxJ hy.1).symm
      obtain ⟨e, rfl | heJ, heI, hi⟩ := Indep.augment hI hIfin hJ' (hJfin.diff.insert _) hcard
      · exact (heI hxI).elim
      exact False.elim <| hcon e heJ.1 heI hi
    obtain ⟨C, hCss, hC⟩ : ∃ C ⊆ insert x (J \ {y}), M.IsCircuit C := by
      simpa [indep_iff, insert_subset (hI.subset_ground hxI) (diff_subset.trans hJ.subset_ground)]
      using hJ'
    rw [subset_insert_iff,
      or_iff_right (fun h ↦ (hJ.subset diff_subset).not_isCircuit_of_subset h hC)] at hCss
    refine ⟨C, hC, hCss.1, fun hyC ↦ (hCss.2 ⟨hyC, ?_⟩).2 rfl, hCss.2.trans diff_subset⟩
    rintro rfl
    exact hy.2 hxI
  -- Take such a circuit `Ca` for some arbitrary `a ∈ J \ I`, and then choose `b ∈ Ca \ {x}`
  -- and take a circuit `Cb` for `b`. Now by circuit elimination, the set `Ca ∪ Cb \ {x}`
  -- contains a circuit but is contained in `J`, a contradiction.
  obtain ⟨a, haJ, haI⟩ : ∃ a ∈ J, a ∉ I :=
    not_subset.1 <| fun h ↦ hIJ.not_le (ncard_le_ncard h hIfin)
  obtain ⟨Ca, hCa, hxCa, haCa, hCaJ⟩ := h_ex a ⟨haJ, haI⟩
  obtain ⟨b, hbCa, hbI⟩ : ∃ b ∈ Ca, b ∉ I := not_subset.1 fun h ↦ hI.not_isCircuit_of_subset h hCa
  obtain ⟨Cb, hCb, hxCb, hbCb, hCbJ⟩ :=
    h_ex b ⟨hCaJ (mem_diff_singleton.2 ⟨hbCa, fun hbx ↦ hbI <| hbx ▸ hxI⟩), hbI⟩
  obtain ⟨C, hC, hxC, hC'⟩ := M.circuit_elimination hCa hCb (by rintro rfl; contradiction) hxCa hxCb
  refine hJ.not_isCircuit_of_subset ?_ hC
  rw [← diff_singleton_eq_self hxC]
  refine (diff_subset_diff_left hC').trans ?_
  rw [union_diff_distrib]
  exact union_subset hCaJ hCbJ
termination_by (J \ I).ncard

/-- The matroid of a `FiniteCircuitMatroid`. -/
@[simps! E]
protected def matroid (M : FiniteCircuitMatroid α) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofFinitaryCardAugment
  (E := M.E)
  (Indep := M.Indep)
  (⟨by simp, fun C hC hss ↦ M.empty_not_isCircuit (by rwa [← subset_empty_iff.1 hC])⟩)
  (fun _ _ ↦ Indep.subset)
  (fun _ _ ↦ Indep.augment)
  (fun I h ↦
      ⟨fun e heI ↦ by simpa using (h {e} (by simpa) (by simp)).subset_ground,
      fun C hCI hC ↦ (h C hCI (M.circuit_finite hC)).not_isCircuit_of_subset rfl.subset hC⟩)
  (fun _ ↦ Indep.subset_ground)

@[simp]
protected lemma matroid_indep_iff :
    M.matroid.Indep I ↔ I ⊆ M.E ∧ ∀ ⦃C⦄, C ⊆ I → ¬ M.IsCircuit C := by
  simp [FiniteCircuitMatroid.matroid, M.indep_iff]

@[simp]
protected lemma matroid_isCircuit : M.matroid.IsCircuit = M.IsCircuit := by
  ext C
  obtain hCE | hCE := em' <| C ⊆ M.E
  · refine iff_of_false (mt Matroid.IsCircuit.subset_ground hCE)
      (mt (fun h ↦ M.circuit_subset_ground h) hCE)
  simp only [Matroid.isCircuit_iff_forall_ssubset, M.matroid_indep_iff,  hCE, true_and,
    ← Matroid.not_indep_iff (show C ⊆ M.matroid.E from hCE), not_forall, Classical.not_imp,
    not_not, exists_prop]
  refine ⟨fun ⟨⟨C', hC', hC'ss⟩, hmin⟩ ↦ ?_, fun h ↦ ⟨⟨C, rfl.subset, h⟩, fun I hIC ↦ ?_⟩⟩
  · obtain rfl | hssu := hC'.eq_or_ssubset
    · exact hC'ss
    exact False.elim <| (hmin hssu).2 rfl.subset hC'ss
  refine ⟨hIC.subset.trans hCE, fun C' hC'I hC' ↦ ?_⟩
  exact M.circuit_antichain hC' h (hC'I.trans_ssubset hIC).ne (hC'I.trans hIC.subset)

--lemma foo {A B : Set α} : A ⊂ B ∨ B ⊂ A ∨ A = B

protected def ofNonSpanningCircuit
  (E : Set α)
  (IsNonspanningCircuit : Set α → Prop)
  (r : ℕ)
  -- (... ) axioms here
  (ground_set : ∀ C, IsNonspanningCircuit C → C ⊆ E)
  (rank_not_spanning : ∀ C, IsNonspanningCircuit C → C.Finite ∧ C.ncard ≤ r )
  (empty_not_isCircuit : ¬IsNonspanningCircuit ∅)
  (circuit_antichain : IsAntichain (· ⊆ ·) {C | IsNonspanningCircuit C})
  (circuit_elimination :
    ∀ ⦃C₁ C₂ e⦄, IsNonspanningCircuit C₁ → IsNonspanningCircuit C₂ → C₁ ≠ C₂ → e ∈ C₁ → e ∈ C₂ →
    ∃ C, IsNonspanningCircuit C ∧ e ∉ C ∧ C ⊆ C₁ ∪ C₂)
  : FiniteCircuitMatroid α where
    E := E
    IsCircuit C := IsNonspanningCircuit C ∨
      (C.Finite ∧ C.ncard = r + 1 ∧ C ⊆ E ∧ (∀ C₀ ⊆ C, ¬ IsNonspanningCircuit C₀))
    empty_not_isCircuit := by
      simp only [finite_empty, ncard_empty, Nat.right_eq_add, Nat.add_eq_zero, one_ne_zero,
        and_false, subset_empty_iff, forall_eq, false_and, or_false]
      exact empty_not_isCircuit
    circuit_antichain := by
      intro C hC C₁ hC₁ hCC₁
      simp only [Pi.compl_apply, compl_iff_not]
      obtain ( hSC | hS ) := hC
      · obtain ( hSC1 | hS1 ) := hC₁
        · exact circuit_antichain hSC hSC1 hCC₁
        · by_contra hc
          exact (hS1.2.2.2 C hc ) hSC
      · obtain ( hSC1 | hS1 ) := hC₁
        · have h1 := rank_not_spanning C₁ hSC1
          by_contra hcon
          have hcard : r + 1 ≤ C₁.ncard := by
            rw [←hS.2.1]
            exact ncard_le_ncard hcon (h1.1)
          linarith
          --sorry
        · by_contra! hcon
          -- have ht : C₁.Finite := by sorry
          have hcard : C₁.ncard ≤ C.ncard := by linarith
          refine hCC₁ (eq_of_subset_of_ncard_le hcon hcard hS1.1)
      --by_contra! hc

    circuit_elimination := by
      intro C C₁ e hC hC1 hCC1 heC heC1
      obtain ( hNSC | hS ) := hC
      · obtain ( hSC1 | ⟨hC₁fin, hC₁card, hC₁⟩ ) := hC1
        · obtain⟨ C₃, hC₃ ⟩ := circuit_elimination hNSC hSC1 hCC1 heC heC1
          use C₃
          constructor
          · left
            exact hC₃.1
          · refine⟨hC₃.2.1, hC₃.2.2⟩
        · obtain ⟨f, hfC, hfC₁⟩ : (C \ C₁).Nonempty := by
            rw [diff_nonempty]
            exact fun hss ↦ hC₁.2 _ hss hNSC

          have hef : f ≠ e := by rintro rfl; contradiction
          by_cases hsub : (∃ C₃, IsNonspanningCircuit C₃ ∧ C₃ ⊆ (C₁\{e}) ∪ {f} )
          · obtain ⟨C₃, hC3ns, hC2 ⟩ := hsub
            use C₃
            constructor
            · left
              exact hC3ns
            · constructor
              · by_contra hcon
                have hc1 : e ∉ C₁ \ {e} ∪ {f} := by simp [hef.symm]
                exact hc1 (mem_of_mem_of_subset hcon hC2)
              · have he1 : C₁ \ {e} ⊆ C₁ := diff_subset
                have he2 : {f} ⊆ C := by simpa
                rw [union_comm C C₁]
                exact fun ⦃a⦄ a_1 ↦ (union_subset_union he1 he2) (hC2 a_1)
          · use (C₁\{e}) ∪ {f}
            constructor
            · right
              refine ⟨ ?_, ?_, ?_, ?_ ⟩
              · simpa using hC₁fin.diff.insert _
              · simp only [union_singleton]
                rwa [ncard_exchange hfC₁ heC1]
              · apply union_subset
                · --have h1 : C₁ ⊆ E := by exact hS1.2.2.1
                  have h2 : C₁ \ {e} ⊆ C₁ := by
                    simp only [diff_singleton_subset_iff, subset_insert]
                  exact diff_subset.trans hC₁.1
                  -- exact?
                  -- exact fun ⦃a⦄ a_1 ↦ (hC₁) (h2 a_1)
                simp only [singleton_subset_iff]
                exact mem_of_subset_of_mem (ground_set C hNSC) hfC


              · intro C₃ hC3
                · by_contra hcon
                  have hC3c : ∃ C, IsNonspanningCircuit C ∧ C ⊆ C₁ \ {e} ∪ {f} := by
                    use C₃
                  exact hsub hC3c
            · refine ⟨ ?_, ?_ ⟩
              · simp [hef.symm]
              · rw [union_comm C C₁]
                apply union_subset_union diff_subset
                simpa only [singleton_subset_iff]
      · have hex : ∃ f, f ∈ C₁ \ C := by
          by_contra! hc
          simp only [mem_diff, not_and, not_not] at hc
          obtain ( hSC1 | hS1 ) := hC1
          · exact (hS.2.2.2 C₁ hc) hSC1
          -- have ht : Finite ↑C := by sorry
          have hcontra : C₁ = C := by
            apply eq_of_subset_of_ncard_le hc _ hS.1
            rw [hS.2.1, hS1.2.1]
          exact hCC1 (id (Eq.symm hcontra))
        obtain ⟨f, hf⟩ := hex
        have hef : f ≠ e := by sorry
        by_cases hsub : (∃ C₃, IsNonspanningCircuit C₃ ∧ C₃ ⊆ (C\{e}) ∪ {f} )
        · obtain ⟨C₃, hC3ns, hC2 ⟩ := hsub
          use C₃
          constructor
          · left
            exact hC3ns
          · constructor
            · by_contra hcon
              have hc1 : e ∉ C \ {e} ∪ {f} := by
                simp [hef.symm]
              exact hc1 (mem_of_mem_of_subset hcon hC2)
            · have he1 : C \ {e} ⊆ C := diff_subset
              have he2 : {f} ⊆ C₁ := by simpa using hf.1
              have := union_subset_union he1 he2
              exact fun ⦃a⦄ a_1 ↦ (union_subset_union he1 he2) (hC2 a_1)
        · use (C\{e}) ∪ {f}
          constructor
          · right
            refine ⟨ ?_, ?_, ?_, ?_ ⟩
            · simpa using hS.1.diff.insert f

            ·
              rw [union_singleton, ncard_exchange hf.2 heC]
              exact hS.2.1
            · apply union_subset
              · have : C \ {e} ⊆ C := by
                  simp only [diff_singleton_subset_iff, subset_insert]
                exact fun ⦃a⦄ a_1 ↦ (hS.2.2.1 ) (this a_1)
              · have h1 : C₁ ⊆ E := by
                  obtain ( hSC1 | hS1 ) := hC1
                  · exact ground_set C₁ hSC1
                  · exact hS1.2.2.1
                simp only [singleton_subset_iff]
                exact mem_of_mem_of_subset (mem_of_mem_diff hf) h1
            · intro C₂ hC2
              by_contra! hcon
              have hC2c : ∃ C₃, IsNonspanningCircuit C₃ ∧ C₃ ⊆ C \ {e} ∪ {f} := by
                use C₂
              exact hsub hC2c
          refine ⟨ ?_,
          union_subset_union diff_subset (singleton_subset_iff.mpr (mem_of_mem_diff hf))⟩
          · simp [hef.symm]

    circuit_subset_ground := by
      intro C hNS
      obtain ( hSC1 | hS1 ) := hNS
      · exact ground_set C hSC1
      · exact hS1.2.2.1

    circuit_finite := by
      intro C hNS
      obtain ( hSC1 | hS1 ) := hNS
      · exact (rank_not_spanning C hSC1).1
      · exact hS1.1

-- example : Matroid α :=
--   FiniteCircuitMatroid.matroid <| (ofNonSpanningCircuit E sorry sorry sorry sorry)

end FiniteCircuitMatroid



-- ∃ e ∈ J, e ∉ I ∧ M.Indep (insert e I) := by
-- namespace FiniteCircuitMatroid



-- end FiniteCircuitMatroid


end Set

section Finset

open Finset

/-
TODO : Give better API for `Set`-valued predicates.
-/


-- /-- A matroid described using a `IsCircuit` predicate on `Finset`s. Can be converted to a matroid
-- using `FinsetCircuitMatroid.matroid`. -/
-- structure FinsetCircuitMatroid (α : Type*) where
--   (E : Set α)
--   (IsCircuit : Finset α → Prop)
--   (empty_not_isCircuit : ¬IsCircuit ∅)
--   (circuit_antichain : IsAntichain (· ⊆ ·) {C | IsCircuit C})
--   (circuit_elimination : ∀ ⦃C₁ C₂ e⦄, IsCircuit C₁ → IsCircuit C₂ → C₁ ≠ C₂ → e ∈ C₁ → e ∈ C₂ →
--     ∃ C, IsCircuit C ∧ e ∉ C ∧ ∀ x ∈ C, x ∈ C₁ ∨ x ∈ C₂)
--   (circuit_subset_ground : ∀ ⦃C⦄, IsCircuit C → ↑C ⊆ E)
--   (Indep : Finset α → Prop)
--   (indep_iff : ∀ ⦃I⦄, Indep I ↔ ↑I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C)

-- namespace FinsetCircuitMatroid

-- variable {α : Type*} {I J C C₁ C₂ : Finset α} {M : FinsetCircuitMatroid α}

-- lemma IsCircuit.exists_subset_erase_of_ne [DecidableEq α] (hC₁ : M.IsCircuit C₁)
--     (hC₂ : M.IsCircuit C₂) (hne : C₁ ≠ C₂) (e : α) :
--     ∃ C, M.IsCircuit C ∧ C ⊆ (C₁ ∪ C₂).erase e := by
--   simp only [subset_iff, mem_erase, ne_eq, mem_union]
--   wlog he : e ∈ C₁ ∩ C₂
--   · rw [mem_inter, Classical.not_and_iff_not_or_not] at he
--     obtain he | he := he
--     · exact ⟨C₁, hC₁, by aesop⟩
--     exact ⟨C₂, hC₂, by aesop⟩
--   rw [mem_inter] at he
--   obtain ⟨C, hC, heC, h⟩ := M.circuit_elimination hC₁ hC₂ hne he.1 he.2
--   exact ⟨C, hC, by aesop⟩

-- lemma IsCircuit.subset_ground (hC : M.IsCircuit C) : (C : Set α) ⊆ M.E :=
--   M.circuit_subset_ground hC

-- lemma indep_empty : M.Indep ∅ :=
--   M.indep_iff.2 <| by simp [subset_empty, empty_not_isCircuit]

-- lemma Indep.subset_ground (hI : M.Indep I) : (I : Set α) ⊆ M.E :=
--   (M.indep_iff.1 hI).1

-- lemma Indep.not_isCircuit_of_subset (hI : M.Indep I) (hCI : C ⊆ I) : ¬ M.IsCircuit C :=
--   (M.indep_iff.1 hI).2 hCI

-- lemma IsCircuit.not_indep (hC : M.IsCircuit C) : ¬ M.Indep C :=
--   fun hI ↦ hI.not_isCircuit_of_subset Subset.rfl hC

-- lemma exists_isCircuit_subset (h : ¬ M.Indep I) (hIE : (I : Set α) ⊆ M.E) :
--     ∃ C ⊆ I, M.IsCircuit C := by
--   simpa [M.indep_iff, hIE] using h

-- lemma Indep.subset {M : FinsetCircuitMatroid α} (hJ : M.Indep J) (hI : I ⊆ J) : M.Indep I :=
--   M.indep_iff.2 ⟨(coe_subset.2 hI).trans hJ.subset_ground,
--     fun _ hCI hC ↦ hJ.not_isCircuit_of_subset (hCI.trans hI) hC⟩

-- lemma Indep.aug [DecidableEq α] (hI : M.Indep I) (hJ : M.Indep J) (hIJ : I.card < J.card) :
--     ∃ e ∈ J, e ∉ I ∧ M.Indep (insert e I) := by
--   let T := {S | S ⊆ I ∪ J ∧ M.Indep S ∧ I.card < S.card}
--   have hfin : T.Finite :=
--     (finite_toSet <| (I ∪ J).powerset).subset fun S hS ↦ by simp only
--[hS.1, mem_coe, mem_powerset]
--   have hne : T.Nonempty := ⟨J, subset_union_right, hJ, hIJ⟩
--   obtain ⟨K, ⟨hK_subset, hK_indep, hK_card⟩, hK_min⟩ :=
--     Set.Finite.exists_minimal_wrt (card <| I \ ·) _ hfin hne

--   obtain (h_empty | ⟨e, he⟩) := (I \ K).eq_empty_or_nonempty
--   · have hssu : I ⊂ K := (sdiff_eq_empty_iff_subset.1 h_empty).ssubset_of_ne
--       (by rintro rfl; simp at hK_card)
--     obtain ⟨e, heK, heI⟩ := exists_of_ssubset hssu
--     have heJ := (mem_union.1 (hK_subset heK)).elim (False.elim ∘ heI) id
--     refine ⟨e, heJ, heI, hK_indep.subset <| insert_subset heK hssu.subset⟩

--   obtain ⟨heI, heK⟩ := Finset.mem_sdiff.mp he
--   have hKfe : ∀ f ∈ K \ I, ∃ C ⊆ ((insert e K).erase f), M.IsCircuit C := by
--     intro f hf
--     obtain ⟨hfK, hfI⟩ := mem_sdiff.mp hf
--     contrapose! hK_min with hK_indep'
--     have hKfe_subset : ((insert e K).erase f) ⊆ I ∪ J := (erase_subset f (insert e K)).trans <|
--       insert_subset (mem_union_left J heI) hK_subset
--     have hKfe_card : ((insert e K).erase f).card = K.card := by
--       calc ((insert e K).erase f).card
--         _ = (insert e K).card - 1 := card_erase_of_mem <| mem_insert_of_mem hfK
--         _ = K.card := by rw [card_insert_of_not_mem heK, add_tsub_cancel_right]
--     use ((insert e K).erase f)
--     refine ⟨⟨hKfe_subset, M.indep_iff.mpr ⟨?_, hK_indep'⟩, (by rwa [hKfe_card])⟩, ?_⟩
--     · simp only [coe_erase, coe_insert]
--       exact Set.diff_subset.trans <| Set.insert_subset (hI.subset_ground heI)
-- hK_indep.subset_ground
--     have hssu : (I \ (insert e K).erase f) ⊂ I \ K := by
--       rw [sdiff_erase_not_mem hfI, Finset.ssubset_iff_subset_ne, Ne, Finset.ext_iff, not_forall]
--       exact ⟨(sdiff_subset_sdiff Subset.rfl (subset_insert _ _)), ⟨e, by simp [heI, heK]⟩⟩
--     exact ⟨card_le_card hssu.subset, (card_lt_card hssu).ne.symm⟩
--   obtain ⟨f, hfK, hfI⟩ : ∃ f ∈ K, f ∉ I :=
--     not_subset.1 (show ¬ K ⊆ I from fun hss ↦ hK_card.not_le (card_le_card hss))

--   obtain ⟨Cf, hCf_subset, hCf⟩ := hKfe f (by simp [hfI, hfK])
--   exfalso
--   obtain (hCfKI | ⟨g,hg⟩) := (Cf ∩ (K \ I)).eq_empty_or_nonempty
--   · suffices h_bad : Cf ⊆ I by rw [M.indep_iff] at hI; exact hI.2 h_bad hCf
--     rw [← inter_sdiff_assoc, sdiff_eq_empty_iff_subset] at hCfKI
--     replace hCfKI := insert_subset heI hCfKI
--     rw [Finset.insert_inter_distrib, inter_eq_left.mpr <| insert_subset_iff.mpr
--       ⟨mem_insert_self e K, (hCf_subset.trans <| erase_subset f <| insert e K)⟩] at hCfKI
--     exact (insert_subset_iff.mp hCfKI).right

--   obtain ⟨Cg, hCg_subset, hCg⟩ := hKfe g <| mem_of_mem_inter_right hg
--   have he_mem : ∀ ⦃C x⦄, C ⊆ (insert e K).erase x → M.IsCircuit C → e ∈ C := by
--     intro C x hC_subset hC; by_contra! heC
--     replace hC_subset := hC_subset.trans <| erase_subset _ _
--     rw [subset_insert_iff_of_not_mem heC] at hC_subset
--     rw [M.indep_iff] at hK_indep
--     exact hK_indep.2 hC_subset hC
--   have h_subset : ∀ ⦃C x⦄, C ⊆ (insert e K).erase x → C \ {e} ⊆ K := by
--     simp_rw [sdiff_subset_iff, insert_eq]
--     exact fun C x hC ↦ hC.trans (erase_subset _ _)
--   have h_ne : Cf ≠ Cg := by rintro rfl; simpa using hCg_subset (mem_inter.1 hg).1
--   obtain ⟨C, hC, hC_subset⟩ := hCf.exists_subset_erase_of_ne hCg h_ne e
--   rw [← sdiff_singleton_eq_erase, union_sdiff_distrib] at hC_subset
--   exact hK_indep.not_isCircuit_of_subset
--     (hC_subset.trans <| union_subset (h_subset hCf_subset) (h_subset hCg_subset)) hC

-- @[simps!]
-- protected def ofFinite (E : Set α) (IsCircuit : Set α → Prop)
--     (empty_not_isCircuit : ¬IsCircuit ∅)
--     (circuit_antichain : IsAntichain (· ⊆ ·) {C | IsCircuit C})
--     (circuit_elimination : ∀ ⦃C₁ C₂ e⦄, IsCircuit C₁ → IsCircuit C₂ → C₁ ≠ C₂ → e ∈ C₁ → e ∈ C₂ →
--       ∃ C, IsCircuit C ∧ e ∉ C ∧ ∀ x ∈ C, x ∈ C₁ ∨ x ∈ C₂)
--     (circuit_subset_ground : ∀ ⦃C⦄, IsCircuit C → C ⊆ E)
--     (hfin : ∀ ⦃C⦄, IsCircuit C → C.Finite)
--     (Indep : Set α → Prop)
--     (indep_iff : ∀ ⦃I⦄, Indep I ↔ I ⊆ E ∧ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C) :
--     FinsetCircuitMatroid α where
--   E := E
--   IsCircuit C := IsCircuit C
--   empty_not_isCircuit := by simpa
--   circuit_antichain C hC C' hC' hne hle := circuit_antichain hC hC' (by simpa) (by simpa)
--   circuit_elimination C₁ C₂ e hC₁ hC₂ hne heC₁ heC₂ := by
--     obtain ⟨C, hC, heC, h⟩ := circuit_elimination hC₁ hC₂ (by simpa) heC₁ heC₂
--     exact ⟨(hfin hC).toFinset, by simpa, by simpa, by simpa⟩
--   circuit_subset_ground C hC := circuit_subset_ground hC
--   Indep I := Indep I
--   indep_iff I := by
--     simp only [indep_iff, and_congr_right_iff]
--     exact fun hIE ↦ ⟨fun h C hCI hC ↦ h (by simpa) hC,
--       fun h C hCE hC ↦ h (C := (hfin hC).toFinset) (by simpa) (by simpa)⟩

-- /-- A `FinsetCircuitMatroid` gives rise to a finitary `Matroid` with the same circuits. -/
-- @[simps!] protected def matroid [DecidableEq α] (M : FinsetCircuitMatroid α) : Matroid α :=
--   IndepMatroid.matroid <| IndepMatroid.ofFinset
--   (E := M.E)
--   (Indep := M.Indep)
--   (indep_empty := M.indep_empty)
--   (indep_subset := fun _ _ hJ ↦ hJ.subset)
--   (indep_aug := fun _ _ hI hJ ↦ hI.aug hJ)
--   (subset_ground := fun _ hI ↦ hI.subset_ground)

-- instance [DecidableEq α] : Matroid.Finitary (M.matroid) := by
--   rw [FinsetCircuitMatroid.matroid, IndepMatroid.ofFinset]
--   infer_instance

-- @[simp] lemma matroid_isCircuit_iff [DecidableEq α] : M.matroid.IsCircuit C ↔ M.IsCircuit C := by
--   simp only [Matroid.isCircuit_def, Matroid.Dep, matroid_Indep, IndepMatroid.ofFinset_indep',
--     not_forall, Classical.not_imp, minimal_subset_iff, Set.mem_setOf_eq, coe_subset, and_imp,
--     forall_exists_index, exists_prop, matroid_E]
--   refine ⟨fun ⟨⟨⟨D, hDC, hD⟩, hCE⟩, hmin⟩ ↦ ?_,
--     fun h ↦ ⟨⟨⟨C, Subset.rfl,h.not_indep⟩, h.subset_ground⟩, fun X D hDX hD hX hXC ↦ ?_⟩⟩
--   · obtain ⟨C', hCD', hC'⟩ := exists_isCircuit_subset hD <| subset_trans (by simpa) hCE
--     rwa [coe_inj.1 <| hmin (t := C') C' Subset.rfl hC'.not_indep hC'.subset_ground
--       (by simpa using hCD'.trans hDC)]

--   obtain ⟨C', hCD', hC'⟩ := exists_isCircuit_subset hD <| subset_trans (by simpa) hX
--   have hC'X := (coe_subset.2 hCD').trans hDX
--   obtain rfl := M.circuit_antichain.eq hC' h (by simpa using hC'X.trans hXC)
--   exact hC'X.antisymm hXC

-- lemma matroid_isCircuit_iff' [DecidableEq α] {C : Set α} :
--     M.matroid.IsCircuit C ↔ ∃ (h : C.Finite), M.IsCircuit h.toFinset := by
--   simp only [← matroid_isCircuit_iff, Set.Finite.coe_toFinset, exists_prop, iff_and_self]
--   exact fun h ↦ h.finite

-- @[simp] lemma matroid_indep_iff [DecidableEq α] : M.matroid.Indep I ↔ M.Indep I := by
--   rw [M.indep_iff, Matroid.indep_iff_forall_subset_not_isCircuit', and_comm]
--   simp only [matroid_E, matroid_isCircuit_iff', not_exists, and_congr_right_iff]
--   exact fun _ ↦ ⟨fun h C hCI hC ↦ h C (by simpa) (by simp) (by simpa),
--     fun h C hCI hfin hC ↦ h (by simpa) hC⟩

-- lemma matroid_indep_iff' (I : Set α) [DecidableEq α] :
--     M.matroid.Indep I ↔ I ⊆ M.E ∧ ∀ C, M.IsCircuit C → ¬ ((C : Set α) ⊆ I) := by
--   simp only [FinsetCircuitMatroid.matroid, IndepMatroid.matroid_Indep,
--  IndepMatroid.ofFinset_indep']
--   refine ⟨fun h ↦ ⟨fun e heI ↦ ?_, fun C hC hCI ↦ ?_⟩ , fun h J hJI ↦ ?_⟩
--   · simpa using (h {e} (by simpa)).subset_ground
--   · exact (M.indep_iff.1 <| h C hCI).2 rfl.subset hC
--   rw [M.indep_iff, and_iff_right (hJI.trans h.1)]
--   exact fun C hCJ hC ↦ h.2 C hC <| subset_trans (by simpa) hJI



-- end FinsetCircuitMatroid

end Finset
