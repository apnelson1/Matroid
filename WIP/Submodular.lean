
import Mathlib.Order.Lattice
import Matroid.Rank.Nat
import Matroid.Constructions.IsCircuitAxioms
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

namespace Matroid

variable {α β : Type*}

-- Should this be predicate or class?
def Submodular [Lattice α] [LinearOrderedAddCommMonoid β] (f : α → β) :=
  ∀ X Y, f (X ⊓ Y) + f (X ⊔ Y) ≤ f X + f Y

open Matroid

-- prop 11.1.1
@[simps!] def ofSubmodular [DecidableEq α] {f : Finset α → ℤ} (h_sub : Submodular f)
    (h_mono : Monotone f) : Matroid α := by
  set IsCircuit := Minimal (fun X ↦ X.Nonempty ∧ f X < X.card)
  have circuit_antichain := setOf_minimal_antichain (fun X ↦ X.Nonempty ∧ f X < X.card)

  have circuit_f_lt_card : ∀ ⦃C⦄, IsCircuit C → f C < C.card := fun C hC ↦ hC.1.2
  have indep_f_ge_card : ∀ ⦃I C⦄, IsCircuit C → I ⊂ C → I.Nonempty → I.card ≤ f I := by
    intro I C hC hI hI_nonempty
    by_contra! h_lt
    exact not_ssubset_of_subset (hC.2 ⟨hI_nonempty, h_lt⟩ hI.subset) hI
  exact FinsetCircuitMatroid.matroid <| FinsetCircuitMatroid.mk
    (E := Set.univ)
    (IsCircuit := IsCircuit)
    (empty_not_isCircuit := fun h ↦ by simpa using h.1.1)
    (circuit_antichain := circuit_antichain)
    (circuit_elimination := by
      intro C₁ C₂ e hC₁ hC₂ h_ne he
      obtain ⟨heC₁, heC₂⟩ := mem_inter.mp he
      set D := (C₁ ∪ C₂).erase e
      suffices h : D ∈ {C | C.Nonempty ∧ f C < C.card} by
        obtain ⟨C, hC, hC_mem, hC_min⟩ := exists_minimal_satisfying_subset
          (fun C ↦ C.Nonempty ∧ f C < C.card) subset_rfl h
        use C;
        refine ⟨⟨hC_mem, hC_min⟩, hC⟩
      refine ⟨?_, ?_⟩
      · contrapose! h_ne; simp only [not_nonempty_iff_eq_empty] at h_ne
        rw [erase_eq_empty_of_mem (inter_subset_union he)] at h_ne
        obtain ⟨rfl, rfl⟩ := singleton_subset_inter_and_union_subset_singleton
          (singleton_subset_iff.mpr he) (by rw [h_ne];)
        rfl
      obtain ⟨hC₁_ne, hC₂_ne⟩ := FinsetCircuitMatroid.intro_elimination_nontrivial
        circuit_antichain hC₁ hC₂ h_ne he
      have hfCi : ∀ ⦃C⦄, IsCircuit C → e ∈ C → C.Nontrivial → f C = C.card - 1 := by
        intro C hC he hC_non
        refine le_antisymm ?_ ?_
        · rw [Int.le_sub_one_iff]; exact circuit_f_lt_card hC
        calc (C.card : ℤ) - 1
          _ = ↑(C.erase e).card := by
            rw [← Nat.cast_one, ← Nat.cast_sub, Nat.cast_inj, card_erase_of_mem he]
            exact (one_lt_card_iff_nontrivial.mpr hC_non).le
          _ ≤ f (C.erase e) :=
            indep_f_ge_card hC (erase_ssubset he) <| (erase_nonempty he).mpr hC_non
          _ ≤ f C := by
            apply h_mono; simp only [le_eq_subset]; exact erase_subset e C
      calc f D
        _ ≤ f (C₁ ∪ C₂) := h_mono (erase_subset e <| C₁ ∪ C₂)
        _ ≤ f C₁ + f C₂ - f (C₁ ∩ C₂) := by
          linarith [@inf_eq_inter α _ ▸ @sup_eq_union α _ ▸ h_sub C₁ C₂]
        _ = C₁.card - 1 + C₂.card - 1 - f (C₁ ∩ C₂) := by
          rw [hfCi hC₁ heC₁ hC₁_ne, hfCi hC₂ heC₂ hC₂_ne]; ring
        _ ≤ C₁.card - 1 + C₂.card - 1 - (C₁ ∩ C₂).card := by
          suffices (C₁ ∩ C₂).card ≤ f (C₁ ∩ C₂) by linarith
          have h_nonempty : (C₁ ∩ C₂).Nonempty := by use e
          have h_ssubset : (C₁ ∩ C₂) ⊂ C₁ :=
            inter_ssubset_of_not_subset_left (circuit_antichain hC₁ hC₂ h_ne)
          exact indep_f_ge_card hC₁ h_ssubset h_nonempty
        _ = C₁.card + C₂.card - (C₁ ∩ C₂).card - 2 := by ring
        _ = (C₁ ∪ C₂).card - 2 := by rw [coe_card_inter]; ring
        _ = D.card - 1 := by
          have : e ∈ C₁ ∪ C₂ := mem_union_left C₂ heC₁
          rw [card_erase_of_mem <| this, Nat.cast_sub <| (by simp only [one_le_card]; use e)]
          ring
        _ < D.card := sub_one_lt _
    )
    (circuit_subset_ground := by simp)
    (Indep := fun I ↦ ∀ ⦃C⦄, C ⊆ I → ¬IsCircuit C)
    (indep_iff := by simp)

@[simp] theorem circuit_ofSubmodular_iff [DecidableEq α] {f : Finset α → ℤ}
    (h_sub : Submodular f) (h_mono : Monotone f) (C : Finset α) :
    (ofSubmodular h_sub h_mono).IsCircuit C ↔ Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) C := by
  unfold ofSubmodular
  simp only [FinsetCircuitMatroid.matroid_isCircuit_iff]

-- corollary 11.1.2
@[simp] theorem indep_ofSubmodular_iff [DecidableEq α] {f : Finset α → ℤ}
    (h_sub : Submodular f) (h_mono : Monotone f) (I : Finset α) :
    (ofSubmodular h_sub h_mono).Indep I ↔ ∀ I' ⊆ I, I'.Nonempty → I'.card ≤ f I' := by
  simp only [ofSubmodular_Indep, IndepMatroid.ofFinset_indep]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro I' hI' hI'_non
    contrapose! h
    obtain ⟨C, hC_subset, hC_min⟩ := exists_minimal_satisfying_subset
      (· ∈ {C | C.Nonempty ∧ f C < ↑C.card}) subset_rfl ⟨hI'_non, h⟩
    use C;
    refine ⟨hC_subset.trans hI', hC_min⟩
  intro I' h' hI'
  obtain ⟨h_nonempty, h_con⟩ := hI'.1
  linarith [h I' h' h_nonempty]

-- definition at bottom of page 406
structure PolymatroidFn [Lattice α] [Bot α] [LinearOrderedAddCommMonoid β] (f : α → β) where
  (submodular : Submodular f)
  (mono : Monotone f)
  (zero_at_bot : f ⊥ = 0)

variable {f : Finset α → ℤ}

@[simps!] def ofPolymatroidFn [DecidableEq α] (h : PolymatroidFn f) : Matroid α :=
  ofSubmodular h.submodular h.mono

@[simp] theorem indep_ofPolymatroidFn_iff [DecidableEq α] (hf : PolymatroidFn f) (I : Finset α) :
    (ofPolymatroidFn hf).Indep I ↔ ∀ I' ⊆ I, I'.Nonempty → I'.card ≤ f I' := by
  simp only [ofPolymatroidFn, indep_ofSubmodular_iff]

theorem ofPolymatroidFn_nonempty_indep_le [DecidableEq α] {hf : PolymatroidFn f} {I : Finset α}
    (h' : I.Nonempty) (h : (ofPolymatroidFn hf).Indep I) : I.card ≤ f I := by
  exact (indep_ofPolymatroidFn_iff hf I).mp h I subset_rfl h'

private theorem polymatroid_rank_eq_on_indep [DecidableEq α] {hf : PolymatroidFn f} {X : Finset α}
    (hX_indep : (ofPolymatroidFn hf).Indep X) :
    (∃ Y ⊆ X, (ofPolymatroidFn hf).r X = f Y + (X \ Y).card ∧
    ∀ Y' ⊆ X, f Y + (X \ Y).card ≤ f Y' + (X \ Y').card) := by
  set M := ofPolymatroidFn hf
  unfold r
  rw [hX_indep.eRk, Set.encard_coe_eq_coe_finsetCard, ENat.toNat_coe]
  use ∅
  simp only [empty_subset, sdiff_empty, self_eq_add_left, true_and]
  rw [← bot_eq_empty, hf.zero_at_bot]
  simp only [zero_add, true_and]
  intro Y hY
  rw [Finset.cast_card_sdiff hY]
  change (Y : Set α) ⊆ X at hY
  have hY_indep := hX_indep.subset hY
  simp only [M, indep_ofPolymatroidFn_iff] at hY_indep
  by_cases hY_nonempty : Y.Nonempty
  · specialize hY_indep Y subset_rfl hY_nonempty
    linarith
  simp only [not_nonempty_iff_eq_empty] at hY_nonempty
  rw [hY_nonempty, card_empty, ← bot_eq_empty, hf.zero_at_bot]
  simp only [Nat.cast_zero, sub_zero, zero_add, le_refl]


-- proposition 11.1.7
theorem polymatroid_rank_eq [DecidableEq α] (hf : PolymatroidFn f) (X : Finset α) :
    (∃ Y ⊆ X, f Y + (X \ Y).card ≤ (ofPolymatroidFn hf).r X) ∧
    (∀ Y ⊆ X, (ofPolymatroidFn hf).r X ≤ f Y + (X \ Y).card) := by
  set M := ofPolymatroidFn hf
  obtain ⟨B, hB⟩ := M.exists_isBasis X (by simp only [ofPolymatroidFn_E, Set.subset_univ, M])
  have hB_finite : B.Finite := Set.Finite.subset X.finite_toSet hB.subset
  have hB_fintype : Fintype ↑B := by exact hB_finite.fintype
  rw [← Set.coe_toFinset B] at hB
  refine ⟨?_, ?_⟩; swap
  · intro Y _
    rw [← hB.rk_eq_rk]
    simp only [M] at hB
    obtain ⟨W, _, hW, h⟩ := polymatroid_rank_eq_on_indep hB.indep
    rw [hW]
    calc f W + ↑(B.toFinset \ W).card
      _ ≤ f (Y ∩ B.toFinset) + ↑(B.toFinset \ (Y ∩ B.toFinset)).card :=
        h (Y ∩ B.toFinset) inter_subset_right
      _ ≤ f Y + ↑(B.toFinset \ (Y ∩ B.toFinset)).card := by
        linarith [hf.mono <| @inter_subset_left α _ Y B.toFinset]
      _ ≤ f Y + ↑(X \ Y).card := by
        simp only [sdiff_inter_self_right, add_le_add_iff_left, Nat.cast_le]
        refine card_le_card ?_
        refine sdiff_subset_sdiff hB.subset subset_rfl
  have h_choice : ∀ e : ↑(X \ B.toFinset),
      ∃ I ⊆ B.toFinset, M.Indep I ∧ f (insert ↑e I) < (insert ↑e I).card := by
    intro e
    have h_ins : M.Dep (insert e.val B) := by
      have : ↑e ∈ X.toSet \ ↑B.toFinset := by
        rw [← coe_sdiff]
        exact e.2
      replace this := hB.insert_dep this
      simpa only [Set.coe_toFinset] using this
    obtain ⟨C, hC_subset, hC⟩ := h_ins.exists_isCircuit_subset
    have : Fintype ↑C := by
      have : C ⊆ ↑(insert ↑e B.toFinset) := by
        rwa [coe_insert, Set.coe_toFinset]
      exact ((insert ↑e B.toFinset).finite_toSet.subset this).fintype
    set I := C.toFinset.erase e
    have hI : I ⊆ B.toFinset := by
      intro x hx
      obtain ⟨hxe, hx⟩ := mem_erase.mp hx
      simp only [Set.mem_toFinset] at hx ⊢
      obtain ⟨h, h⟩ := Set.mem_insert_iff.mp <| hC_subset hx
      · contradiction
      assumption
    use I
    refine ⟨hI, hB.indep.subset hI, ?_⟩
    by_cases he : ↑e ∈ C.toFinset; swap
    · exfalso
      simp only [Set.mem_toFinset] at he
      have := ((Set.subset_insert_iff_of_not_mem he).mp hC_subset)
      rw [← Set.coe_toFinset B] at this
      exact hC.dep.1 <| hB.indep.subset this
    rw [insert_erase he]
    simp only [M, ofPolymatroidFn] at hC
    rw [← Set.coe_toFinset C, circuit_ofSubmodular_iff hf.submodular hf.mono] at hC
    exact hC.1.2
  choose I h_subset h_indep h_lt using h_choice
  set Ie := fun e : ↑(X \ B.toFinset) ↦ insert ↑e (I e)
  have h_induc : ∀ Y : Finset ↑(X \ B.toFinset), Y.Nonempty →
    f (Finset.biUnion Y Ie) ≤ (Finset.biUnion Y I).card := by
    intro Y hY_nonempty
    induction' hY_nonempty using Finset.Nonempty.strong_induction
    case h₀ a =>
      have ha : ↑a ∈ X \ B.toFinset := coe_mem a
      replace ha : ↑a ∉ I a := by
        specialize h_subset a
        contrapose! ha
        exact not_mem_sdiff_of_mem_right <| h_subset ha
      simp only [singleton_biUnion, Ie]
      rw [← Int.lt_add_one_iff, ← Nat.cast_one, ← Nat.cast_add, ← card_insert_of_not_mem ha]
      exact h_lt a
    case h₁ Y hY IH =>
      obtain ⟨T, a, ha, b, hb, hab, h⟩ := Nontrivial.exists_cons_eq hY
      set Y' := (cons b T hb) with hY'
      have hIH := IH Y' (cons_nonempty hb) (by rw [← h]; exact ssubset_cons _)
      rw [← h, cons_eq_insert, ← hY', biUnion_insert, biUnion_insert]
      calc f (Ie a ∪ Y'.biUnion Ie)
        _ ≤ f (Ie a) + f (Y'.biUnion Ie) - f (Ie a ∩ Y'.biUnion Ie) := by
          have := hf.submodular (Ie a) (Y'.biUnion Ie)
          simp only [inf_eq_inter, sup_eq_union] at this
          linarith [this]
        _ ≤ f (Ie a) + f (Y'.biUnion Ie) - (Ie a ∩ Y'.biUnion Ie).card := by
          have : Ie a ∩ Y'.biUnion Ie ⊆ I a := by
            intro x hx
            obtain (rfl | h) := mem_insert.mp <| mem_of_mem_inter_left hx; swap
            · assumption
            exfalso
            replace hx := mem_of_mem_inter_right hx
            simp only [mem_biUnion, Subtype.exists] at hx
            obtain ⟨e, he, heY', h_con⟩ := hx
            have : a ∉ Y' := (Iff.not mem_cons).mpr (not_or_intro hab ha)
            obtain (rfl | h) := mem_insert.mp h_con
            · simp only [Subtype.coe_eta] at heY'
              exact this heY'
            replace this := h_subset ⟨e, he⟩ <| h
            exact (mem_sdiff.mp a.2).right this
          obtain (h_empty | h_nonempty) := eq_empty_or_nonempty (Ie a ∩ Y'.biUnion Ie)
          · rw [h_empty, card_empty, ← bot_eq_empty, hf.zero_at_bot, Nat.cast_zero]
          linarith [ofPolymatroidFn_nonempty_indep_le h_nonempty <|
            (h_indep a).subset <| coe_subset.mpr this]
        _ ≤ f (Ie a) + f (Y'.biUnion Ie) - (I a ∩ Y'.biUnion I).card := by
          have : I a ∩ Y'.biUnion I ⊆ (Ie a ∩ Y'.biUnion Ie) := by
            refine inter_subset_inter ?_ ?_
            · exact subset_insert (↑a) (I a)
            refine biUnion_mono fun a _ ↦ subset_insert (↑a) (I a)
          linarith [card_mono this]
        _ ≤ f (Ie a) + (Y'.biUnion I).card - (I a ∩ Y'.biUnion I).card := by
          linarith [hIH]
        _ ≤ (I a).card + (Y'.biUnion I).card - (I a ∩ Y'.biUnion I).card := by
          have : {a} ⊂ Y := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · simp only [singleton_subset_iff, ← h]
              exact mem_cons_self a (cons b T hb)
            exact Ne.symm (Nontrivial.ne_singleton hY)
          specialize IH {a} (singleton_nonempty a) this
          simp only [singleton_biUnion] at IH
          linarith [IH]
        _ = (I a ∪ Y'.biUnion I).card := by exact Eq.symm cast_card_union
  use univ.biUnion Ie
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [mem_biUnion, mem_univ, true_and] at hx
    obtain ⟨e, he⟩ := hx
    exact insert_subset (sdiff_subset <| coe_mem e) ((h_subset e).trans hB.subset) <| he
  rw [← hB.r]
  unfold r
  rw [hB.indep.eRk, Set.encard_coe_eq_coe_finsetCard, ENat.toNat_coe]
  have h_eq : X \ univ.biUnion Ie = B.toFinset \ univ.biUnion I := by
    ext x; refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    <;> refine mem_sdiff.mpr ⟨?_, ?_⟩
    · have :  X \ B.toFinset ⊆ univ.biUnion Ie := by
        intro a ha
        simp only [univ_eq_attach, mem_biUnion, mem_attach, true_and, Subtype.exists]
        use a, ha
        exact mem_insert_self a (I ⟨a, ha⟩)
      replace h := sdiff_subset_sdiff (subset_refl X) this <| h
      simp only [sdiff_sdiff_right_self, inf_eq_inter] at h
      exact mem_of_mem_inter_right h
    -- thanks aesop
    · simp_all only [Set.coe_toFinset, Set.subset_toFinset, Subtype.forall, mem_sdiff,
      Set.mem_toFinset, ofPolymatroidFn_Indep, IndepMatroid.ofFinset_indep, univ_eq_attach,
        mem_biUnion, mem_attach, mem_insert, true_and, Subtype.exists, not_exists, not_or,
        not_false_eq_true, and_self, exists_false, M, Ie]
    · exact hB.subset (mem_sdiff.mp h).left
    -- thanks aesop
    simp_all only [Set.coe_toFinset, Set.subset_toFinset, Subtype.forall, mem_sdiff,
      Set.mem_toFinset, ofPolymatroidFn_Indep, IndepMatroid.ofFinset_indep, univ_eq_attach,
      mem_biUnion, mem_attach, true_and, Subtype.exists, not_exists, mem_insert, not_false_eq_true,
      and_self, or_false, exists_prop, exists_eq_right', not_true_eq_false, and_false, M, Ie]
  rw [h_eq, cast_card_sdiff, add_sub]
  · obtain (rfl | hXB) := eq_or_ne X B.toFinset
    · simp only [sdiff_self, bot_eq_empty, not_mem_empty, isEmpty_subtype, not_false_eq_true,
      implies_true, univ_eq_empty, biUnion_empty, Set.toFinset_card, card_empty, Nat.cast_zero,
      sub_zero, add_le_iff_nonpos_left, ge_iff_le]
      rw [← bot_eq_empty, hf.zero_at_bot]
    have h_nonempty : (@univ ↑(X \ B.toFinset) _).Nonempty := by
      have := hXB.symm.ssubset_of_subset <| Finset.coe_subset.mp hB.subset
      obtain ⟨x, hx⟩ := Finset.exists_of_ssubset this
      simp only [univ_eq_attach, attach_nonempty_iff]
      use x
      exact mem_sdiff.mpr hx
    linarith [h_induc univ h_nonempty]
  intro x hx
  simp only [mem_biUnion, mem_univ, true_and] at hx
  obtain ⟨e, he⟩ := hx
  exact h_subset e he

-- theorem 11.2.3
theorem generalized_halls_marriage {ι : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq α]
    {A : ι → Finset α}
    (hA_nonempty : ∀ i, (A i).Nonempty)
    {f : Finset α → ℕ} (hf_submodular : Submodular f) (hf_mono : Monotone f) :
    (∃ e : ι → α, (∀ i : ι, e i ∈ A i) ∧ (∀ K : Finset ι, K.card ≤ f (Finset.image e K))) ↔
    (∀ K : Finset ι, K.card ≤ f (K.biUnion A)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨e, he_mem, he⟩ := h
    intro K
    refine le_trans (he K) ?_
    refine hf_mono ?_
    intro a ha
    obtain ⟨i, hi, hei⟩ := mem_image.mp ha
    specialize he_mem i
    rw [hei] at he_mem
    simp only [mem_biUnion]
    use i
  by_cases h_isBase : ∀ i, ¬(A i).Nontrivial
  · replace h_isBase : ∀ (i : ι), ∃ e, A i = {e} := by
      intro i
      obtain hgood | hbad := (hA_nonempty i).exists_eq_singleton_or_nontrivial
      · assumption
      exfalso; exact h_isBase i hbad
    choose e he using h_isBase
    use e
    refine ⟨fun i ↦ by rw [he i]; exact mem_singleton.mpr rfl, fun K ↦ ?_⟩
    specialize h K
    suffices K.biUnion A = image e K by exact le_of_le_of_eq h (congrArg f this)
    ext x
    simp only [mem_biUnion, mem_image, he, mem_singleton]
    tauto
  push_neg at h_isBase
  obtain ⟨i, hAi⟩ := h_isBase
  have h_induc : ∃ x ∈ A i, ∀ K : Finset ι,
      K.card ≤ f (K.biUnion <| Function.update A i ((A i).erase x)) := by
    by_contra! h_con
    obtain ⟨x₁, hx₁, x₂, hx₂, hx₁x₂⟩ := hAi
    simp only [mem_coe] at hx₁ hx₂
    obtain ⟨K₁, hK₁⟩ := h_con x₁ hx₁
    obtain ⟨K₂, hK₂⟩ := h_con x₂ hx₂
    by_cases hiK₁ : i ∈ K₁; swap
    · absurd hK₁; push_neg
      specialize h K₁
      suffices K₁.biUnion A = K₁.biUnion (Function.update A i ((A i).erase x₁)) by rwa [← this]
      refine biUnion_congr rfl (fun j hj ↦ ?_)
      have : i ≠ j := by exact Ne.symm (ne_of_mem_of_not_mem hj hiK₁)
      exact Eq.symm (Function.update_of_ne (id (Ne.symm this)) ((A i).erase x₁) A)
    by_cases hiK₂ : i ∈ K₂; swap
    · absurd hK₂; push_neg
      specialize h K₂
      suffices K₂.biUnion A = K₂.biUnion (Function.update A i ((A i).erase x₂)) by rwa [← this]
      refine biUnion_congr rfl (fun j hj ↦ ?_)
      have : i ≠ j := by exact Ne.symm (ne_of_mem_of_not_mem hj hiK₂)
      exact Eq.symm (Function.update_of_ne (id (Ne.symm this)) ((A i).erase x₂) A)
    suffices h_bad : (K₁.card : ℤ) + K₂.card - 1 ≤ K₁.card + K₂.card - 2 by linarith
    set A'₁ := (Function.update A i ((A i).erase x₁))
    set A'₂ := (Function.update A i ((A i).erase x₂))
    calc (K₁.card : ℤ) + K₂.card - 1
      _ = (K₁ ∪ K₂).card + ((K₁ ∩ K₂).erase i).card := by
        rw [cast_card_union, cast_card_erase_of_mem <| mem_inter.mpr ⟨hiK₁, hiK₂⟩]
        ring
      _ ≤ f ((K₁ ∪ K₂).biUnion A) + ((K₁ ∩ K₂).erase i).card := by
        linarith [h <| K₁ ∪ K₂]
      _ ≤ f ((K₁ ∪ K₂).biUnion A) + f (((K₁ ∩ K₂).erase i).biUnion A) := by
        linarith [h <| (K₁ ∩ K₂).erase i]
      _ ≤ f (K₁.biUnion A ∪ K₂.biUnion A) + f (((K₁ ∩ K₂).erase i).biUnion A) := by
        rw [finset_biUnion_union K₁ K₂ A]
      _ ≤ f (K₁.biUnion A'₁ ∪ K₂.biUnion A'₂) + f (((K₁ ∩ K₂).erase i).biUnion A) := by
        simp only [tsub_le_iff_right, sub_add_cancel, add_le_add_iff_right, Nat.cast_le]
        apply hf_mono
        simp only [le_eq_subset]
        intro x hx
        simp only [mem_union, mem_biUnion] at hx
        obtain ⟨j, hj, hx⟩ | ⟨j, hj, hx⟩ := hx
        <;> obtain rfl | h_neij := eq_or_ne i j
        · obtain rfl | h_ne := eq_or_ne x x₂
          · refine mem_union_left _ ?_
            simp only [mem_biUnion, A'₁]
            use i
            simp only [Function.update_self, mem_erase]
            exact ⟨(by assumption), hx₁x₂.symm, hx₂⟩
          refine mem_union_right _ ?_
          simp only [mem_biUnion, A'₂]
          use i
          simp only [Function.update_self, mem_erase]
          exact ⟨hiK₂, h_ne, (by assumption)⟩
        · refine mem_union_left _ ?_
          simp only [mem_biUnion, A'₁]
          use j
          simp only [Function.update_of_ne h_neij.symm ((A i).erase x₁) A]
          exact ⟨hj, hx⟩
        · obtain rfl | h_ne := eq_or_ne x x₂
          · refine mem_union_left _ ?_
            simp only [mem_biUnion, A'₁]
            use i
            simp only [Function.update_self, mem_erase]
            exact ⟨(by assumption), hx₁x₂.symm, hx₂⟩
          refine mem_union_right _ ?_
          simp only [mem_biUnion, A'₂]
          use i
          simp only [Function.update_self, mem_erase]
          exact ⟨hiK₂, h_ne, (by assumption)⟩
        refine mem_union_right _ ?_
        simp only [mem_biUnion, A'₂]
        use j
        simp only [Function.update_of_ne h_neij.symm ((A i).erase x₂) A]
        exact ⟨hj, hx⟩
      _ ≤ f (K₁.biUnion A'₁ ∪ K₂.biUnion A'₂) +
          f ((K₁.erase i).biUnion A ∩ (K₂.erase i).biUnion A) := by
        simp only [tsub_le_iff_right, sub_add_cancel, add_le_add_iff_left, Nat.cast_le]
        apply hf_mono
        simp only [le_eq_subset, erase_inter_distrib]
        exact finset_biUnion_inter (K₁.erase i) (K₂.erase i) A
      _ ≤ f (K₁.biUnion A'₁ ∪ K₂.biUnion A'₂) +
          f ((K₁.erase i).biUnion A'₁ ∩ (K₂.erase i).biUnion A'₂) := by
        simp only [tsub_le_iff_right, sub_add_cancel, add_le_add_iff_left, Nat.cast_le]
        apply hf_mono
        simp [le_eq_subset]
        refine inter_subset_inter ?_ ?_
        <;> rw [biUnion_subset_iff_forall_subset]
        <;> intro j hj
        <;> intro x hx
        <;> simp only [mem_biUnion, A'₁, A'₂]
        <;> use j
        <;> refine ⟨hj, ?_⟩
        · simp only [Function.update_of_ne (ne_of_mem_erase hj) ((A i).erase x₁) A]; exact hx
        simp only [Function.update_of_ne (ne_of_mem_erase hj) ((A i).erase x₂) A]; exact hx
      _ ≤ f (K₁.biUnion A'₁ ∪ K₂.biUnion A'₂) + f (K₁.biUnion A'₁ ∩ K₂.biUnion A'₂) := by
        simp only [add_le_add_iff_left, Nat.cast_le]
        apply hf_mono
        refine inter_subset_inter ?_ ?_
        <;> exact biUnion_subset_biUnion_of_subset_left _ <| erase_subset i _
      _ ≤ f (K₁.biUnion A'₁) + f (K₂.biUnion A'₂) := by
        simp only [tsub_le_iff_right, sub_add_cancel, ← Nat.cast_add, Nat.cast_le, ← inf_eq_inter,
          ← sup_eq_union]
        linarith [hf_submodular (K₁.biUnion A'₁) (K₂.biUnion A'₂)]
      _ ≤ K₁.card + K₂.card - 2 := by
        linarith
  obtain ⟨x, hx_mem, hA'⟩ := h_induc
  set A' := Function.update A i ((A i).erase x)
  have hA'_nonempty : ∀ i, (A' i).Nonempty := by
    intro j
    obtain rfl | h_ne := eq_or_ne i j
    · simp only [A', Function.update_self]
      exact (erase_nonempty hx_mem).mpr hAi
    simp only [A', Function.update_of_ne h_ne.symm, hA_nonempty j]
  obtain ⟨e, he_mem, he⟩ := (generalized_halls_marriage hA'_nonempty hf_submodular hf_mono).mpr hA'
  use e
  refine ⟨?_, he⟩
  intro j
  specialize he_mem j
  obtain rfl | h_ne := eq_or_ne i j
  · simp only [A', Function.update_self] at he_mem
    exact mem_of_mem_erase he_mem
  simpa [A', Function.update_of_ne h_ne.symm] using he_mem
termination_by ∑ i, (A i).card
decreasing_by
  simp_wf
  refine Finset.sum_lt_sum ?_ ?_
  · intro j hj
    refine card_le_card ?_
    obtain rfl | h_ne := eq_or_ne i j
    · simp only [Function.update_self]
      exact erase_subset x (A i)
    simp only [Function.update_of_ne h_ne.symm, subset_rfl]
  use i
  refine ⟨(by simp only [mem_univ]), ?_⟩
  refine card_lt_card ?_
  simp only [Function.update_self]
  exact erase_ssubset hx_mem

theorem generalized_halls_marriage' {ι : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq α]
    (I : Finset ι) {A : ↑I → Finset α}
    (hA_nonempty : ∀ i : ↑I, (A i).Nonempty)
    {f : Finset α → ℕ} (hf_submodular : Submodular f) (hf_mono : Monotone f) :
    (∃ e : I → α, (∀ i : ↑I, e i ∈ A i) ∧ (∀ K : Finset ↑I, K.card ≤ f (Finset.image e K))) ↔
    (∀ K : Finset ↑I, K.card ≤ f (K.biUnion A)) := by
  exact generalized_halls_marriage hA_nonempty hf_submodular hf_mono

variable {ι : Type*}

structure PartialTransversal (A : ι → Finset α) where
  (edges : Finset (ι × α))
  (mem : ∀ ⦃e⦄, e ∈ edges → e.2 ∈ A e.1)
  (uniq : ∀ ⦃e⦄, e ∈ edges → ∀ ⦃f⦄, f ∈ edges → e.1 = f.1 → e.2 = f.2)
  (inj : ∀ ⦃e⦄, e ∈ edges → ∀ ⦃f⦄, f ∈ edges → e.2 = f.2 → e.1 = f.1)

variable {A : ι → Finset α}

def PartialTransversal.left [DecidableEq ι] (T : PartialTransversal A) :
    Finset ι :=
  T.edges.image Prod.fst

def PartialTransversal.right [DecidableEq α] (T : PartialTransversal A) :
    Finset α :=
  T.edges.image Prod.snd

lemma PartialTransversal.left_mem_left [DecidableEq ι] {T : PartialTransversal A} {e : ι × α}
    (h : e ∈ T.edges) : e.1 ∈ T.left := by
  simp only [left, mem_image]
  use e

lemma PartialTransversal.right_mem_right [DecidableEq α] {T : PartialTransversal A} {e : ι × α}
    (h : e ∈ T.edges) : e.2 ∈ T.right := by
  simp only [right, mem_image]
  use e

lemma PartialTransversal.uniq' {T : PartialTransversal A} {i : ι} {x y : α} :
    (i, x) ∈ T.edges → (i, y) ∈ T.edges → x = y := by
  intro hx hy
  exact T.uniq hx hy rfl

lemma PartialTransversal.inj' {T : PartialTransversal A} {i j : ι} {x : α} :
    (i, x) ∈ T.edges → (j, x) ∈ T.edges → i = j := by
  intro hi hj
  exact T.inj hi hj rfl

lemma PartialTransversal.mem_left [DecidableEq ι] {T : PartialTransversal A}
    {i : ι} (h : i ∈ T.left) : ∃! x, ⟨i, x⟩ ∈ T.edges := by
  simp only [PartialTransversal.left, mem_image, Prod.exists,
    exists_and_right, exists_eq_right] at h
  refine existsUnique_of_exists_of_unique h (fun x y ↦ T.uniq')

lemma PartialTransversal.mem_right [DecidableEq α] {T : PartialTransversal A}
    {x : α} (h : x ∈ T.right) : ∃! i, ⟨i, x⟩ ∈ T.edges := by
  simp only [PartialTransversal.right, mem_image, Prod.exists,
    exists_and_right, exists_eq_right] at h
  refine existsUnique_of_exists_of_unique h (fun x y ↦ T.inj')

lemma PartialTransversal.mem_left_iff [DecidableEq ι] {T : PartialTransversal A}
    {i : ι} : i ∈ T.left ↔ ∃ x, ⟨i, x⟩ ∈ T.edges := by
  refine ⟨fun h ↦ (T.mem_left h).exists, fun h ↦ ?_⟩
  simp only [left, mem_image]
  obtain ⟨x, hx⟩ := h
  use (i, x)

lemma PartialTransversal.mem_right_iff [DecidableEq α] {T : PartialTransversal A}
    {x : α} : x ∈ T.right ↔ ∃ i, ⟨i, x⟩ ∈ T.edges := by
  refine ⟨fun h ↦ (T.mem_right h).exists, fun h ↦ ?_⟩
  simp only [right, mem_image]
  obtain ⟨i, hi⟩ := h
  use (i, x)

def PartialTransversal.fun [Fintype α] [DecidableEq ι]
  (T : PartialTransversal A) [DecidablePred (· ∈ T.edges)] : T.left → α :=
  fun i ↦ Fintype.choose _ (PartialTransversal.mem_left i.property)

lemma PartialTransversal.fun_mem_edges [Fintype α] [DecidableEq ι] {T : PartialTransversal A}
    [DecidablePred (· ∈ T.edges)] (i : T.left) : ⟨i, T.fun i⟩ ∈ T.edges := by
  exact Fintype.choose_spec _ (PartialTransversal.mem_left i.property)

lemma PartialTransversal.fun_mem_right [Fintype α] [DecidableEq ι] [DecidableEq α]
    {T : PartialTransversal A} [DecidablePred (· ∈ T.edges)] (i : T.left) : T.fun i ∈ T.right := by
  exact T.right_mem_right <| T.fun_mem_edges i

lemma PartialTransversal.fun_mem [Fintype α] [DecidableEq ι] [DecidableEq α]
    {T : PartialTransversal A} [DecidablePred (· ∈ T.edges)] (i : T.left) : T.fun i ∈ A i := by
  exact T.mem <| T.fun_mem_edges i

lemma PartialTransversal.fun_inj [Fintype α] [DecidableEq ι] [DecidableEq α]
    {T : PartialTransversal A} [DecidablePred (· ∈ T.edges)] {i j : T.left}
    (h : T.fun i = T.fun j) : i = j := by
  exact SetCoe.ext <| T.inj (T.fun_mem_edges i) (T.fun_mem_edges j) h

lemma PartialTransversal.fun_injective [Fintype α] [DecidableEq ι] [DecidableEq α]
    (T : PartialTransversal A) [DecidablePred (· ∈ T.edges)]: T.fun.Injective :=
  fun _ _ h ↦ fun_inj h

def PartialTransversal.Total (T : PartialTransversal A) := ∀ i, ∃ x, ⟨i, x⟩ ∈ T.edges

lemma PartialTransversal.Total.mem_left [DecidableEq ι] {T : PartialTransversal A} (hT : T.Total)
    {i : ι} : i ∈ T.left := by
  simp only [PartialTransversal.left, mem_image, Prod.exists, exists_and_right, exists_eq_right]
  exact hT i

lemma PartialTransversal.Total.left_eq_univ [DecidableEq ι] [Fintype ι]
    {T : PartialTransversal A} (hT : T.Total) : T.left = univ := by
  refine univ_subset_iff.mp (fun i _ ↦ hT.mem_left)

def PartialTransversal.card (T : PartialTransversal A) : ℕ :=
  T.edges.card

@[simp] lemma PartialTransversal.card_left [DecidableEq ι] {T : PartialTransversal A} :
    T.left.card = T.card := by
  refine card_image_iff.mpr <| fun e he e' he' h ↦ Prod.ext_iff.mpr ⟨h, T.uniq he he' h⟩

@[simp] lemma PartialTransversal.card_right [DecidableEq α] {T : PartialTransversal A} :
    T.right.card = T.card := by
  refine card_image_iff.mpr <| fun e he e' he' h ↦ Prod.ext_iff.mpr ⟨T.inj he he' h, h⟩

noncomputable def PartialTransversal.encard (T : PartialTransversal A) : ℕ∞ :=
  T.edges.toSet.encard

@[simp] lemma PartialTransversal.card_eq_iff_total [DecidableEq ι] [Fintype ι]
    {T : PartialTransversal A} : T.card = Fintype.card ι ↔ T.Total := by
  simp only [← card_left, card_eq_iff_eq_univ, eq_univ_iff_forall, mem_left_iff, Total]

@[simp] lemma PartialTransversal.coe_card_eq_encard (T : PartialTransversal A) :
    ↑T.card = T.encard := by
  simp only [card, encard, Set.encard_coe_eq_coe_finsetCard]

@[simps] def PartialTransversal.of_fun [DecidableEq (ι × α)] {I : Finset ι} {f : ↑I → α}
    (h : ∀ i : I, f i ∈ A i) (hf : f.Injective) : PartialTransversal A where
  edges := Finset.image (fun i ↦ ⟨i.val, f i⟩) Finset.univ
  mem := by
    simp only [mem_image, mem_univ, true_and]
    rintro e ⟨i, rfl⟩
    exact h i
  uniq := by
    simp only [mem_image, mem_univ, true_and]
    rintro e ⟨i, rfl⟩ f ⟨j, rfl⟩ h
    rw [← SetCoe.ext h]
  inj := by
    simp only [mem_image, mem_univ, true_and]
    rintro e ⟨i, rfl⟩ f ⟨j, rfl⟩ h
    rw [hf h]

@[simp] lemma PartialTransversal.of_fun_mem_edges_iff {I : Finset ι} {f : ↑I → α}
    {h : ∀ i : I, f i ∈ A i} {hf : f.Injective} {i : ι} {x : α} :
    (i, x) ∈ (PartialTransversal.of_fun h hf).edges ↔ ∃ hi, f ⟨i, hi⟩ = x := by
  simp only [of_fun_edges, mem_image, mem_univ, true_and, Prod.mk.injEq, Subtype.exists,
    exists_and_left, exists_eq_left]

lemma PartialTransversal.of_fun_mem_dom {I : Finset ι} {f : ↑I → α} {h : ∀ i, f i ∈ A i}
    {hf : f.Injective} {i : ι} {x : α} (hix : (i, x) ∈ (PartialTransversal.of_fun h hf).edges) :
    i ∈ I := by
  simp only [of_fun_mem_edges_iff] at hix
  obtain ⟨hi, _⟩ := hix; use hi

@[simp] lemma PartialTransversal.of_fun_total_iff {I : Finset ι} {f : ↑I → α} {h : ∀ i, f i ∈ A i}
    {hf : f.Injective} : (PartialTransversal.of_fun h hf).Total ↔ I = univ := by
  simp only [Total, of_fun_mem_edges_iff]
  refine ⟨fun h' ↦ ?_, fun h' i ↦ ?_⟩
  · refine univ_subset_iff.mp (fun i _ ↦ ?_)
    obtain ⟨x, hi, _⟩ := h' i; use hi
  have h_mem : i ∈ I := by simp only [h', mem_univ i]
  use f ⟨i, h_mem⟩, h_mem

@[simp] def PartialTransversal.of_fun_left_eq {I : Finset ι} {f : ↑I → α} {h : ∀ i, f i ∈ A i}
    {hf : f.Injective} : (PartialTransversal.of_fun h hf).left = I := by
  ext i
  simp only [mem_left_iff, of_fun_mem_edges_iff]
  refine ⟨fun ⟨_, hi, _⟩ ↦ hi, fun a ↦ BEx.intro (f ⟨i, a⟩) a rfl⟩

@[simp] def PartialTransversal.of_fun_right_eq {I : Finset ι} {f : ↑I → α} {h : ∀ i, f i ∈ A i}
    {hf : f.Injective} : (PartialTransversal.of_fun h hf).right = image f univ := by
  ext x
  simp only [mem_right_iff, of_fun_mem_edges_iff, mem_image, mem_univ, true_and]
  refine ⟨fun ⟨i, hi, h⟩ ↦ ⟨⟨i, hi⟩, h⟩, fun ⟨a, h⟩ ↦ ⟨a.1, a.2, h⟩⟩

instance {B : ι → Finset α} : DecidablePred ((fun ⟨i, x⟩ ↦ x ∈ B i) : ι × α → Prop) :=
  fun ⟨i, x⟩ ↦ match decidableMem x (B i) with
  | isTrue hp => isTrue hp
  | isFalse hp => isFalse hp

def PartialTransversal.move {A : ι → Finset α} (B : ι → Finset α) (T : PartialTransversal A) :
    PartialTransversal B where
  edges := T.edges.filter (fun ⟨i, x⟩ ↦ x ∈ B i)
  mem := by
    simp only [mem_filter, and_imp, imp_self, implies_true]
  uniq := by
    simp only [mem_filter]
    intro e he f hf
    exact T.uniq he.1 hf.1
  inj := by
    simp only [mem_filter]
    intro e he f hf
    exact T.inj he.1 hf.1

lemma PartialTransversal.move_edges {A B : ι → Finset α} (T : PartialTransversal A) :
    (PartialTransversal.move B T).edges = T.edges.filter (fun e ↦ e.2 ∈ B e.1) := rfl

lemma PartialTransversal.move_edges_subset {A B : ι → Finset α} (T : PartialTransversal A) :
    (PartialTransversal.move B T).edges ⊆ T.edges := by
  rw [move_edges]
  exact filter_subset (fun e ↦ e.2 ∈ B e.1) T.edges

lemma PartialTransversal.mem_move_edges_iff {A B : ι → Finset α} (T : PartialTransversal A)
    {e : ι × α} : (e ∈ (PartialTransversal.move B T).edges) ↔ e ∈ T.edges ∧ e.2 ∈ B e.1 := by
  simp only [move_edges, mem_filter]

lemma PartialTransversal.move_edges_eq_iff {A B : ι → Finset α} (T : PartialTransversal A) :
    (PartialTransversal.move B T).edges = T.edges ↔ (∀ e ∈ T.edges, e.2 ∈ B e.1) := by
  simp only [T.move_edges, Finset.filter_eq_self]

lemma PartialTransversal.move_left_eq_iff {A B : ι → Finset α} (T : PartialTransversal A) :
    (PartialTransversal.move B T).left = T.left ↔ (∀ e ∈ T.edges, e.2 ∈ B e.1) := by
  refine ⟨fun h e he ↦ ?_, fun h ↦ by simp only [left, T.move_edges_eq_iff.mpr h]⟩
  have := h ▸ T.left_mem_left he
  obtain ⟨e', he', h⟩ := by simpa only [left, mem_image] using this
  simp only [T.uniq he (T.move_edges_subset he') h.symm, ← h, (move B T).mem he']

lemma PartialTransversal.move_right_eq_iff {A B : ι → Finset α} (T : PartialTransversal A) :
    (PartialTransversal.move B T).right = T.right ↔ (∀ e ∈ T.edges, e.2 ∈ B e.1) := by
  refine ⟨fun h e he ↦ ?_, fun h ↦ by simp only [right, T.move_edges_eq_iff.mpr h]⟩
  have := h ▸ T.right_mem_right he
  obtain ⟨e', he', h⟩ := by simpa only [right, mem_image] using this
  simp only [T.inj he (T.move_edges_subset he') h.symm, ← h, (move B T).mem he']

instance : HasSubset (PartialTransversal A) := ⟨fun T T' ↦ T.edges ⊆ T'.edges⟩

lemma PartialTransversal.left_subset {T T' : PartialTransversal A} (h : T ⊆ T') :
    T.left ⊆ T'.left := by
  simp only [left, image_subset_image h]

lemma PartialTransversal.right_subset {T T' : PartialTransversal A} (h : T ⊆ T') :
    T.right ⊆ T'.right := by
  simp only [right, image_subset_image h]

lemma PartialTransversal.exists_subset_card_eq {T : PartialTransversal A} {n : ℕ} (h : n ≤ T.card) :
    ∃ T', T' ⊆ T ∧ T'.card = n := by
  obtain ⟨edges', h', rfl⟩ := Finset.exists_subset_card_eq h
  use PartialTransversal.mk
    (edges := edges')
    (mem := fun e he ↦ T.mem <| h' he)
    (inj := fun e he e' he' ↦ T.inj (h' he) (h' he'))
    (uniq := fun e he e' he' ↦ T.uniq (h' he) (h' he'))
  exact ⟨h', rfl⟩

theorem rado_v2 (M : Matroid α) (A : ι → Finset α) :
    (∃ T : PartialTransversal A, T.Total ∧ M.Indep T.right) ↔
    (∀ K : Finset ι, K.card ≤ M.r (K.biUnion A)) := by
  by_cases hA_nonempty : ∀ i, (A i).Nonempty; swap
  · simp only [not_forall, not_nonempty_iff_eq_empty] at hA_nonempty
    obtain ⟨i, hAi⟩ := hA_nonempty
    apply iff_of_false
    <;> push_neg
    · intro e he; exfalso
      obtain ⟨x, hx⟩ := he i
      exact not_mem_empty x <| hAi ▸ e.mem hx
    use {i}
    simp only [hAi, singleton_biUnion, card_singleton, Nat.lt_one_iff, coe_empty, rk_empty]
  set f : Finset α → ℕ := fun S ↦ M.r (S : Set α)
  have hf_submodular : Submodular f := by
    intro a b
    simp only [inf_eq_inter, sup_eq_union, f, coe_inter, coe_union]
    exact IsRkFinite.submod (M.IsRkFinite.of_finite <| finite_toSet a) (M.IsRkFinite.of_finite <| finite_toSet b)
  have hf_mono : Monotone f := by
    intro a b hab
    simp only [le_eq_subset, ← coe_subset] at hab
    rw [← IsRkFinite.eRk_le_eRk_iff
      (M.IsRkFinite.of_finite <| finite_toSet a) (M.IsRkFinite.of_finite <| finite_toSet b)]
    exact M.eRk_mono hab
  have h := generalized_halls_marriage hA_nonempty hf_submodular hf_mono
  simp only [f] at h
  rw [← h]
  refine ⟨fun ⟨T, hT_total, hT_indep⟩ ↦ ?_, fun ⟨e, he_mem, he_card⟩ ↦ ?_⟩
  · set e := fun i ↦ T.fun ⟨i, PartialTransversal.Total.mem_left hT_total⟩
    have h_inj : e.Injective := fun i j h ↦ Subtype.val_inj.mpr (T.fun_inj h)
    use e
    refine ⟨fun i ↦ T.fun_mem _, fun K ↦ ?_⟩
    have h_subset : ↑(image e K) ⊆ (T.right : Set α) := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact PartialTransversal.fun_mem_right _
    rw [(hT_indep.subset h_subset).r, Set.ncard_coe_Finset (image e K),
      card_image_of_injective K h_inj]

  set e' : (@univ ι _) → α := fun i ↦ e i
  have he_inj : e.Injective := by
    intro i j hij
    contrapose! he_card
    use {i, j}
    simp only [image_insert, image_singleton, coe_insert, coe_singleton, hij, Set.mem_singleton_iff,
      Set.insert_eq_of_mem, card_insert_of_not_mem <| not_mem_singleton.mpr he_card,
      Nat.lt_add_one_iff, ← @Nat.cast_le ℕ∞, cast_rk_eq, card_singleton, Nat.cast_one]
    refine (M.eRk_le_encard {e j}).trans (by simp only [Set.encard_singleton, le_refl])
  have he'_inj : e'.Injective := fun i j hij ↦ SetCoe.ext (he_inj (by simpa only [e'] using hij))
  use PartialTransversal.of_fun (fun i ↦ he_mem i) he'_inj
  refine ⟨by simp only [PartialTransversal.of_fun_total_iff], ?_⟩
  simp only [PartialTransversal.of_fun_right_eq, indep_iff_eRk_eq_encard_of_finite <| finite_toSet _]
  refine le_antisymm (M.eRk_le_encard _) ?_
  have : (image e' univ) = (image e univ) := by
    ext x
    simp only [univ_eq_attach, mem_image, mem_attach, true_and, Subtype.exists, mem_univ,
      exists_true_left]
  rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective univ he'_inj,
    ← M.cast_rk_eq_eRk_of_finite <| finite_toSet _, Nat.cast_le, this]
  refine le_trans ?_ (he_card univ)
  simp only [univ_eq_attach, card_attach, card_univ, le_refl]

def Transversal [DecidableEq ι] (f : ι → α) (A : ι → Finset α) :=
  f.Injective ∧ ∀ i, f i ∈ A i

def Transverses (T : Finset α) (A : ι → Finset α) :=
  ∃ (f : T → ι), f.Injective ∧ ∀ t, t.1 ∈ A (f t)

def Transverses' (T : Finset α) (A : ι → Finset α) :=
  ∃ (f : α → ι), Set.InjOn f T.toSet ∧ ∀ t ∈ T, t ∈ A (f t)

lemma transverses_of_empty (A : ι → Finset α) : Transverses ∅ A := by
  unfold Transverses
  simp only [IsEmpty.forall_iff, and_true]
  have : IsEmpty { x : α // x ∈ (∅ : Finset α) } := by exact instIsEmpty
  have : Nonempty ({ x : α // x ∈ (∅ : Finset α) } → ι) := by exact instNonemptyOfInhabited
  use Classical.choice this
  exact Function.injective_of_subsingleton (Classical.choice this)

lemma transverses'_of_empty [Nonempty ι] (A : ι → Finset α) : Transverses' ∅ A := by
  unfold Transverses'
  simp only [coe_empty, Set.injOn_empty, not_mem_empty, false_implies, implies_true, and_self]
  exact (exists_const (α → ι)).mpr trivial

lemma transverses_mono {T : Finset α} {T' : Finset α} {A : ι → Finset α}
    (hT : Transverses T A) (hT' : T' ⊆ T) : Transverses T' A := by
  obtain ⟨f, hf_inj, hf⟩ := hT
  set f' := fun x : ↑T' ↦ f ⟨x.val, hT' x.property⟩
  use f'
  refine ⟨?_, ?_⟩
  · intro x y hxy
    replace hxy := hf_inj hxy
    simp only [Subtype.mk.injEq] at hxy
    exact SetCoe.ext hxy
  intro x
  exact hf ⟨↑x, hT' x.property⟩

lemma transverses_of_transverses' {T : Finset α} {A : ι → Finset α}
    (h : Transverses' T A) : Transverses T A := by
  obtain ⟨f, hf_inj, hf⟩ := h
  set f' := fun x : ↑T ↦ f x.val
  use f'
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simp only [f'] at hxy
    replace hxy := hf_inj x.property y.property hxy
    exact SetCoe.ext hxy
  simp only [coe_mem, f']
  intro t
  exact hf t.val t.property

lemma transverses_iff_transverses' (T : Finset α) [Nonempty ι] (A : ι → Finset α) :
    Transverses' T A ↔ Transverses T A := by
  refine ⟨transverses_of_transverses', fun h ↦ ?_⟩
  obtain ⟨f, hf_inj, hf⟩ := h
  set j := (fun _ ↦ Classical.arbitrary ι)
  use Function.extend Subtype.val f j
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    rw [Function.Injective.extend_apply Subtype.val_injective f j ⟨x, hx⟩] at hxy
    rw [Function.Injective.extend_apply Subtype.val_injective f j ⟨y, hy⟩] at hxy
    apply hf_inj at hxy
    simpa [Subtype.mk.inj] using hxy
  intro t ht
  rw [Function.Injective.extend_apply Subtype.val_injective f j ⟨t, ht⟩]
  exact hf ⟨t, ht⟩

lemma transverses_of_image_univ [DecidableEq α]
    {A : ι → Finset α} {f : ι → α} (hi : ∀ i, f i ∈ A i) : Transverses (image f univ) A := by
  have h_choose : ∀ x : ↑(image f univ), ∃ i, f i = x.val := by
    intro x
    simpa [mem_image, mem_univ, true_and] using x.property
  choose f' hf' using h_choose
  use f'
  refine ⟨?_, ?_⟩
  · intro x y hxy
    replace hxy := congrArg f hxy
    rw [hf' x, hf' y] at hxy
    exact SetCoe.ext hxy
  intro x
  rw [← hf' x]
  exact hi (f' x)

lemma transverses_of_subset_image_univ {T : Finset α} [DecidableEq α]
    {A : ι → Finset α} {f : ι → α} (hi : ∀ i, f i ∈ A i) (hf : T ⊆ image f univ) :
    Transverses T A := by
  exact transverses_mono (transverses_of_image_univ hi) hf

-- theorem 11.2.2
theorem rado [DecidableEq ι] [DecidableEq α] (M : Matroid α) (A : ι → Finset α) :
    (∃ e, Transversal e A ∧ M.Indep (Set.range e)) ↔
    (∀ K : Finset ι, K.card ≤ M.r (K.biUnion A)) := by
  by_cases hA_nonempty : ∀ i, (A i).Nonempty; swap
  · simp only [not_forall, not_nonempty_iff_eq_empty] at hA_nonempty
    obtain ⟨i, hAi⟩ := hA_nonempty
    apply iff_of_false
    <;> push_neg
    · intro e he; exfalso
      replace he := hAi ▸ he.2 i
      simp only [not_mem_empty] at he
    use {i}
    simp only [hAi, singleton_biUnion, card_singleton, Nat.lt_one_iff, coe_empty, rk_empty]
  set f : Finset α → ℕ := fun S ↦ M.r (S : Set α)
  have hf_submodular : Submodular f := by
    intro a b
    simp only [inf_eq_inter, sup_eq_union, f, coe_inter, coe_union]
    exact IsRkFinite.submod (M.IsRkFinite.of_finite <| finite_toSet a) (M.IsRkFinite.of_finite <| finite_toSet b)
  have hf_mono : Monotone f := by
    intro a b hab
    simp only [le_eq_subset, ← coe_subset] at hab
    rw [← IsRkFinite.eRk_le_eRk_iff
      (M.IsRkFinite.of_finite <| finite_toSet a) (M.IsRkFinite.of_finite <| finite_toSet b)]
    exact M.eRk_mono hab
  have h := generalized_halls_marriage hA_nonempty hf_submodular hf_mono
  simp only [f] at h
  rw [← h]
  refine exists_congr (fun e ↦ ?_)
  unfold Transversal
  refine ⟨fun ⟨⟨he_inj, he_mem⟩, he_indep⟩ ↦ ⟨he_mem, ?_⟩, fun ⟨he_mem, he⟩ ↦ ?_⟩
  · intro K
    simp only [← card_image_of_injective K he_inj]
    have h_indep : M.Indep (image e K : Set α) := he_indep.subset coe_image_subset_range
    rw [← @Nat.cast_le ℕ∞, ← Set.encard_coe_eq_coe_finsetCard (image e K),
      M.cast_rk_eq_eRk_of_finite <| finite_toSet (image e K), h_indep.eRk]
  refine ⟨⟨?_, he_mem⟩, ?_⟩
  · intro a b hab
    contrapose! he
    use {a, b}
    simp only [image_insert, image_singleton, coe_insert, coe_singleton, hab]
    simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem, card_pair he]
    rw [← @Nat.cast_lt ℕ∞, M.cast_rk_eq_eRk_of_finite <| Set.finite_singleton (e b),
      Nat.cast_two]
    have := Set.encard_singleton (e b) ▸ M.eRk_le_encard {e b}
    refine this.trans_lt Nat.one_lt_ofNat
  specialize he univ
  simp only [coe_image, coe_univ, Set.image_univ] at he
  rw [← @Nat.cast_le ℕ∞, M.cast_rk_eq_eRk_of_finite <| Set.finite_range e] at he
  rw [indep_iff_eRk_eq_encard_of_finite <| Set.finite_range e]
  refine le_antisymm (eRk_le_encard M (Set.range e)) ?_
  refine le_trans ?_ he
  simp only [Set.encard_eq_coe_toFinset_card, Set.toFinset_range, Nat.cast_le, card_image_le]

theorem rado' {ι : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq α]
    (M : Matroid α) (A : ι → Finset α) {d : ℕ} (hd : d ≤ Fintype.card ι):
    (∃ T, Transverses T A ∧ M.Indep ↑T ∧ T.card + d = Fintype.card ι) ↔
    (∀ K : Finset ι, K.card ≤ M.r (K.biUnion A) + d) := by
  by_cases hd_pos : d = 0
  · rw [hd_pos]
    simp only [add_zero]
    rw [← rado M A]
    refine ⟨fun ⟨T, hT⟩ ↦ ?_, fun ⟨e, he_trans, he_indep⟩ ↦ ?_⟩
    · obtain ⟨hT_trans, hT_indep, hT_card⟩ := hT
      obtain ⟨f, hf_inj, hf_mem⟩ := hT_trans
      have h_bij : Function.Bijective f := by
        have h_fin : Finite ι := Fintype.finite (by assumption)
        refine Function.Injective.bijective_of_nat_card_le hf_inj ?_
        simp only [Nat.card_eq_fintype_card, Fintype.card_coe, hT_card, le_rfl]
      obtain ⟨g, hg₁, hg₂⟩ := Function.bijective_iff_has_inverse.mp h_bij
      set e : ι → α := fun i ↦ ↑(g i)
      use Subtype.val ∘ g
      refine ⟨?_, ?_⟩
      · simp only [Transversal]
        refine ⟨?_, ?_⟩
        · exact Function.Injective.comp Subtype.val_injective <| Function.LeftInverse.injective hg₂
        intro i
        simp only [Function.comp_apply]
        obtain ⟨x, hx, _⟩ := Function.Bijective.existsUnique h_bij i
        rw [← hx, hg₁]
        exact hf_mem x
      suffices h : (Set.range (Subtype.val ∘ g)) = ↑T by rwa [h]
      ext x
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · simp only [Set.mem_range, Function.comp_apply] at h
        obtain ⟨i, hi⟩ := h
        rw [← hi]
        exact Subtype.coe_prop (g i)
      simp only [Set.mem_range, Function.comp_apply]
      simp only [mem_coe] at h
      use f ⟨x, h⟩
      rw [hg₁]
    use (Set.range e).toFinset
    simp only [Set.toFinset_range, coe_image, coe_univ, Set.image_univ]
    refine ⟨?_, he_indep, ?_⟩
    · apply transverses_of_image_univ
      exact he_trans.2
    have h_inj := Set.injective_iff_injOn_univ.mp he_trans.1
    rw [← coe_univ] at h_inj
    rw [Finset.card_image_of_injOn h_inj]
    rfl
  rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at hd_pos
  by_cases hA_nonempty : ∀ i, (A i).Nonempty; swap
  · push_neg at hA_nonempty
    obtain ⟨i, hi⟩ := hA_nonempty
    have hι : 1 ≤ Fintype.card ι := hd_pos.trans hd
    simp only [not_nonempty_iff_eq_empty] at hi
    set ι' := {j : ι // j ≠ i}
    set A' : ι' → Finset α := fun j ↦ A ↑j
    have hι' : Fintype.card ι' = Fintype.card ι - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have hd' : d - 1 ≤ Fintype.card ι' := by
      rw [hι']
      exact Nat.sub_le_sub_right hd 1
    have h_rem : (∀ K : Finset ι, K.card ≤ M.r (K.biUnion A) + d) ↔
          ∀ (K : Finset ι'), K.card ≤ M.r ↑(K.biUnion A') + (d - 1) := by
      refine ⟨?_, ?_⟩
      · intro h
        intro K'
        set K := Finset.cons i (Finset.image Subtype.val K') (by
          by_contra! h_bad
          simp only [ne_eq, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            not_true_eq_false, IsEmpty.exists_iff] at h_bad
        )
        specialize h <| K
        rw [card_cons, Finset.card_image_of_injective K' Subtype.val_injective] at h
        suffices h_good : M.r ↑(K.biUnion A) = M.r ↑(K'.biUnion A') by
          zify [hd_pos] at h_good h ⊢
          linarith
        apply congrArg
        apply congrArg
        simp only [K, A', ne_eq, cons_eq_insert, biUnion_insert, hi, empty_union]
        exact image_biUnion
      intro h
      intro K
      by_cases hi : i ∈ K
      · have : ∀ j : ↑(K.erase i), j.val ≠ i := by
          intro j
          exact ne_of_mem_erase j.2
        set f : ↑(K.erase i) → ι' := fun j ↦ ⟨j.val, this j⟩
        specialize h <| image f (K.erase i).attach
        have h_eq : (image f (K.erase i).attach).card = K.card - 1 := by
          rw [← card_erase_of_mem hi]
          nth_rw 2 [← card_attach]
          apply Finset.card_image_of_injective
          intro a b hab
          simp only [f] at hab
          have := congrArg Subtype.val hab
          dsimp only at this
          exact SetCoe.ext this
        rw [h_eq,  tsub_le_iff_right] at h
        refine le_trans h ?_
        suffices M.r ↑((image f (K.erase i).attach).biUnion A') ≤ M.r ↑(K.biUnion A) by
          rw [add_assoc]
          refine Nat.add_le_add this <| Nat.add_le_of_le_sub hd_pos le_rfl
        refine IsRkFinite.rk_le_rk_of_eRk_le_eRk ?_ ?_
        · apply IsRkFinite.of_finite
          exact finite_toSet (K.biUnion A)
        apply M.eRk_mono
        simp only [image_biUnion, Set.le_eq_subset, coe_subset]
        simp only [biUnion_subset_iff_forall_subset, mem_attach, true_implies, Subtype.forall,
          mem_erase, ne_eq, A']
        rintro j ⟨_, hj⟩
        exact subset_biUnion_of_mem A hj
      have : ∀ j : ↑K, j.val ≠ i := by
        intro j
        contrapose! hi
        rw [← hi]
        exact j.2
      set f : ↑K → ι' := fun j ↦ ⟨j.val, this j⟩
      specialize h <| image f K.attach
      have h_eq : (image f K.attach).card = K.attach.card := by
        refine Finset.card_image_of_injective K.attach ?_
        intro a b hab
        simp only [f] at hab
        have := congrArg Subtype.val hab
        dsimp only at this
        exact SetCoe.ext this
      rw [h_eq, card_attach, image_biUnion] at h
      refine le_trans h ?_
      suffices M.r ↑(K.attach.biUnion fun a ↦ A' (f a)) = M.r ↑(K.biUnion A) by
        rw [this]
        simp only [coe_biUnion, mem_coe, add_le_add_iff_left, tsub_le_iff_right,
          le_add_iff_nonneg_right, zero_le]
      apply congrArg
      apply congrArg
      ext x
      simp only [A', f, mem_biUnion, mem_attach, true_and, Subtype.exists]
      exact bex_def
    obtain h := rado' M A' hd'
    rw [h_rem, ← h]
    refine ⟨?_, ?_⟩
    · refine fun ⟨T, hT_trans, hT_indep, hT_card⟩ ↦ ?_
      have hT_trans' : Transverses T A' := by
        obtain ⟨f, hf_inj, hf_mem⟩ := hT_trans
        have hf : ∀ x : T, f x ≠ i := by
          intro x
          specialize hf_mem x
          contrapose! hf_mem
          rw [hf_mem, hi]
          exact not_mem_empty _
        use fun x ↦ ⟨f x, hf x⟩
        refine ⟨?_, ?_⟩
        · intro x x' hx
          dsimp at hx
          exact hf_inj <| congrArg Subtype.val hx
        intro x
        exact hf_mem x
      have hT_card' : T.card + (d - 1) = Fintype.card ι' := by
        zify [hd_pos, hι, hι']
        linarith
      exact ⟨T, hT_trans', hT_indep, hT_card'⟩
    refine fun ⟨T, hT_trans, hT_indep, hT_card⟩ ↦ ?_
    have hT_trans' : Transverses T A := by
      obtain ⟨f, hf_inj, hf_mem⟩ := hT_trans
      use fun x ↦ ↑(f x)
      refine ⟨?_, ?_⟩
      · exact Function.Injective.comp Subtype.val_injective hf_inj
      intro x
      exact hf_mem x
    have hT_card' : T.card + d = Fintype.card ι := by
      zify [hι, hd_pos] at hι' hT_card ⊢
      linarith
    exact ⟨T, hT_trans', hT_indep, hT_card'⟩

  set f : Finset α → ℕ := fun S ↦ M.r (S : Set α) + d
  have hf_submodular : Submodular f := by
    intro a b
    simp only [inf_eq_inter, sup_eq_union, f, coe_inter, coe_union]
    linarith [IsRkFinite.submod (M.IsRkFinite.of_finite <| finite_toSet a) (M.IsRkFinite.of_finite <| finite_toSet b)]
  have hf_mono : Monotone f := by
    intro a b hab
    simp only [le_eq_subset, ← coe_subset] at hab
    simp only [f, add_le_add_iff_right]
    rw [← IsRkFinite.eRk_le_eRk_iff
      (M.IsRkFinite.of_finite <| finite_toSet a) (M.IsRkFinite.of_finite <| finite_toSet b)]
    exact M.eRk_mono hab

  have h := generalized_halls_marriage hA_nonempty hf_submodular hf_mono
  rw [← h]
  refine ⟨?_, ?_⟩
  · refine fun ⟨T, hT_trans, hT_indep, hT_card⟩ ↦ ?_
    simp only [f]
    obtain ⟨f, hf_inj, hf_mem⟩ := hT_trans
    choose j hj using hA_nonempty
    set e : ι → α := Function.extend Subtype.val (Subtype.val ∘ hf_inj.invOfMemRange) j
    use e
    refine ⟨?_, ?_⟩
    · intro i
      simp only [e, Function.extend]
      split
      next h =>
        simp only [Function.comp_apply]
        specialize hf_mem (hf_inj.invOfMemRange (Classical.choose h))
        rwa [hf_inj.left_inv_of_invOfMemRange, Classical.choose_spec h] at hf_mem
      next h =>
        exact hj i
    intro K
    rw [← card_inter_add_card_sdiff K (image f univ)]
    refine add_le_add ?_ ?_
    · suffices h : (K ∩ image f univ).card ≤ M.r ↑(image e (K ∩ image f univ)) by
        refine le_trans h ?_
        rw [← @Nat.cast_le ℕ∞]
        rw [M.cast_rk_eq_eRk_of_finite <| finite_toSet (image e (K ∩ image f univ)),
            M.cast_rk_eq_eRk_of_finite <| finite_toSet (image e K)]
        apply M.eRk_mono
        simp only [Set.le_eq_subset, coe_subset]
        apply image_subset_image
        exact inter_subset_left
      suffices (K ∩ image f univ).card = (image e (K ∩ image f univ)).card by
        rw [this]
        suffices h : ((image e (K ∩ image f univ)) : Set α) ⊆ (T : Set α) by
          replace h := hT_indep.subset h
          rw [← @Nat.cast_le ℕ∞, M.cast_rk_eq_eRk_of_finite <| finite_toSet _,
              ← Set.encard_coe_eq_coe_finsetCard _, h.eRk]
        simp only [coe_subset]
        intro x hx
        rw [mem_image] at hx
        simp only [mem_inter] at hx
        obtain ⟨i, ⟨_, hif⟩, hi⟩ := hx
        simp only [e, Function.extend] at hi
        rename_i _ _ _ _ _ _ f_2 _
        subst hi
        simp_all only [coe_image, coe_biUnion, mem_coe, Subtype.forall, univ_eq_attach, mem_image,
          mem_attach, true_and, Subtype.exists, Set.mem_range, exists_prop, exists_eq_right,
          ↓reduceDIte, Function.comp_apply, coe_mem, f_2, e]
      symm
      rw [card_image_iff]
      intro x hx y hy hxy
      simp only [coe_inter, Set.mem_inter_iff] at hx hy
      simp only [e, Function.extend] at hxy
      replace hx := hx.2
      replace hy := hy.2
      simp only [mem_coe, mem_image_univ_iff_mem_range] at hx hy

      split at hxy
      <;> split at hxy
      next h₁ h₂ =>
        simp only [Function.comp_apply] at hxy
        replace hxy := Subtype.val_injective hxy
        replace hxy := congrArg f hxy
        rw [hf_inj.left_inv_of_invOfMemRange, hf_inj.left_inv_of_invOfMemRange] at hxy
        rwa [Classical.choose_spec h₁, Classical.choose_spec h₂] at hxy
      next h₁ h₂ =>
        exact False.elim <| h₂ <| Set.exists_subtype_range_iff.mpr hy
      next h₁ h₂ =>
        have : ∃ (a : ↑(Set.range f)), ↑a = x := Set.exists_subtype_range_iff.mpr hx
        exfalso
        exact h₁ this
      next h₁ h₂ =>
        have : ∃ (a : ↑(Set.range f)), ↑a = y := Set.exists_subtype_range_iff.mpr hy
        exfalso
        exact h₂ this
    rw [← add_le_add_iff_left T.card]
    rw [hT_card, ← Nat.card_eq_finsetCard T, Nat.card_eq_fintype_card, ← card_univ]
    have : (@univ { x // x ∈ T }).card = (image f univ).card := by
      symm
      rw [card_image_iff]
      exact fun ⦃x₁⦄ _ ⦃x₂⦄ _ h ↦ hf_inj h
    rw [this, add_comm, card_sdiff_add_card]
    exact card_le_univ (K ∪ image f univ)
  refine fun ⟨e, he_mem, he_card⟩ ↦ ?_
  suffices ∃ T, Transverses T A ∧ M.Indep ↑T ∧ Fintype.card ι ≤ T.card + d by
    obtain ⟨T, hT_trans, hT_indep, hT_card⟩ := this
    rw [← Nat.sub_le_iff_le_add] at hT_card
    obtain ⟨T', hT', hT'_card⟩ := exists_subset_card_eq hT_card
    use T'
    refine ⟨transverses_mono hT_trans hT', hT_indep.subset hT', ?_⟩
    symm
    exact (Nat.sub_eq_iff_eq_add hd).mp hT'_card.symm
  obtain ⟨T, hT⟩ := M.exists_isBasis' (image e univ)
  have : Fintype T := finite_toSet (image e univ) |>.subset hT.subset |>.fintype
  use T.toFinset
  simp only [Set.coe_toFinset]
  refine ⟨?_, hT.indep, ?_⟩
  · have hT_subset : T.toFinset ⊆ image e univ := by
      exact Set.toFinset_subset.mpr hT.subset
    exact transverses_of_subset_image_univ he_mem hT_subset
  specialize he_card univ
  simp only [f, ← hT.r, hT.indep.r, card_univ] at he_card
  rwa [← Set.ncard_eq_toFinset_card']

-- theorem 11.2.1
theorem halls_marriage {ι : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq α] (A : ι → Finset α) :
    (∃ e, Transversal e A) ↔ (∀ K : Finset ι, K.card ≤ (K.biUnion A).card) := by
  simpa only [freeOn_indep_iff, Set.subset_univ, and_true, freeOn_rk_eq, Set.ncard_coe_Finset]
    using rado (freeOn Set.univ) A
