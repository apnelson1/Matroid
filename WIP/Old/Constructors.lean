


-- /-- If there is an absolute upper bound on the size of a set satisfying `P`, then the
--   maximal subset property always holds. -/
-- theorem Matroid.existsMaximalSubsetProperty_of_bdd {P : Set α → Prop}
--     (hP : ∃ (n : ℕ), ∀ Y, P Y → Y.encard ≤ n) (X : Set α) : ExistsMaximalSubsetProperty P X := by
--   obtain ⟨n, hP⟩ := hP

--   rintro I hI hIX
--   have hfin : Set.Finite (ncard '' {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X})
--   · rw [finite_iff_bddAbove, bddAbove_def]
--     simp_rw [ENat.le_coe_iff] at hP
--     use n
--     rintro x ⟨Y, ⟨hY,-,-⟩, rfl⟩
--     obtain ⟨n₀, heq, hle⟩ := hP Y hY
--     rwa [ncard_def, heq, ENat.toNat_coe]
--     -- have := (hP Y hY).2
--   obtain ⟨Y, hY, hY'⟩ := Finite.exists_maximal_wrt' ncard _ hfin ⟨I, hI, rfl.subset, hIX⟩
--   refine' ⟨Y, hY, fun J ⟨hJ, hIJ, hJX⟩ (hYJ : Y ⊆ J) ↦ (_ : J ⊆ Y)⟩
--   have hJfin := finite_of_encard_le_coe (hP J hJ)
--   refine' (eq_of_subset_of_ncard_le hYJ _ hJfin).symm.subset
--   rw [hY' J ⟨hJ, hIJ, hJX⟩ (ncard_le_of_subset hYJ hJfin)]

-- /-- If there is an absolute upper bound on the size of an independent set, then the maximality axiom
--   isn't needed to define a matroid by independent sets. -/
-- def matroid_of_indep_of_bdd (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
--     (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
--       B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
--     (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n )
--     (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
--   matroid_of_indep E Indep h_empty h_subset h_aug
--     (fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd h_bdd X) h_support

-- @[simp] theorem matroid_of_indep_of_bdd_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
--     (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
--       B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
--     (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n) (h_support : ∀ I, Indep I → I ⊆ E) :
--     (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).Indep = Indep := by
--   simp [matroid_of_indep_of_bdd]

-- /-- `matroid_of_indep_of_bdd` constructs a `RankFinite` matroid. -/
-- instance (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
--     (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
--       B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
--     (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n )
--     (h_support : ∀ I, Indep I → I ⊆ E) :
--     Matroid.RankFinite (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support) := by

--   refine' (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).exists_base.elim
--     (fun B hB ↦ hB.rankFinite_of_finite _)
--   obtain ⟨n, h_bdd⟩ := h_bdd
--   refine' finite_of_encard_le_coe (h_bdd _ _)
--   rw [← matroid_of_indep_of_bdd_apply E Indep, indep_iff_subset_base]
--   exact ⟨_, hB, rfl.subset⟩

-- /-- If there is an absolute upper bound on the size of an independent set, then matroids
--   can be defined using an 'augmentation' axiom similar to the standard definition of finite matroids
--   for independent sets. -/
-- def matroid_of_indep_of_bdd_augment (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
--     (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
--       ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
--     (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) :
--     Matroid α :=
--   matroid_of_indep_of_bdd E Indep h_empty h_subset
--     (by
--       simp_rw [mem_maximals_setOf_iff, not_and, not_forall, exists_prop, exists_and_left, mem_diff,
--         and_imp, and_assoc]
--       rintro I B hI hImax hB hBmax
--       obtain ⟨J, hJ, hIJ, hne⟩ := hImax hI
--       obtain ⟨n, h_bdd⟩ := h_bdd

--       have hlt : I.encard < J.encard :=
--         (finite_of_encard_le_coe (h_bdd J hJ)).encard_lt_encard (hIJ.ssubset_of_ne hne)
--       have hle : J.encard ≤ B.encard
--       · refine le_of_not_lt (fun hlt' ↦ ?_)
--         obtain ⟨e, he⟩ := ind_aug hB hJ hlt'
--         rw [hBmax he.2.2 (subset_insert _ _)] at he
--         exact he.2.1 (mem_insert _ _)
--       exact ind_aug hI hB (hlt.trans_le hle) )
--     h_bdd h_support

-- @[simp] theorem matroid_of_indep_of_bdd_augment_apply (E : Set α) (Indep : Set α → Prop)
--     (h_empty : Indep ∅) (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
--       ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
--     (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) :
--     (matroid_of_indep_of_bdd_augment E Indep h_empty h_subset ind_aug h_bdd h_support).Indep
--       = Indep := by
--   simp [matroid_of_indep_of_bdd_augment]

-- /-- A collection of Bases with the exchange property and at least one finite member is a matroid -/
-- def matroid_of_exists_finite_base {α : Type*} (E : Set α) (Base : Set α → Prop)
--     (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : ExchangeProperty Base)
--     (support : ∀ B, Base B → B ⊆ E) : Matroid α :=
--   matroid_of_base E Base
--     (by { obtain ⟨B,h⟩ := exists_finite_base; exact ⟨B,h.1⟩ }) base_exchange
--     (by {
--       obtain ⟨B, hB, hfin⟩ := exists_finite_base
--       refine' fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd
--         ⟨B.ncard, fun Y ⟨B', hB', hYB'⟩ ↦ _⟩ X
--       rw [hfin.cast_ncard_eq, encard_base_eq_of_exch base_exchange hB hB']
--       exact encard_mono hYB' })
--     support

-- @[simp] theorem matroid_of_exists_finite_base_apply {α : Type*} (E : Set α) (Base : Set α → Prop)
--     (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : ExchangeProperty Base)
--     (support : ∀ B, Base B → B ⊆ E) :
--     (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support).Base = Base :=
--   rfl

-- /-- A matroid constructed with a finite Base is `RankFinite` -/
-- instance {E : Set α} {Base : Set α → Prop} {exists_finite_base : ∃ B, Base B ∧ B.Finite}
--     {base_exchange : ExchangeProperty Base} {support : ∀ B, Base B → B ⊆ E} :
--     Matroid.RankFinite
--       (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support) :=
--   ⟨exists_finite_base⟩

-- def matroid_of_base_of_finite {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
--     (exists_base : ∃ B, Base B) (base_exchange : ExchangeProperty Base)
--     (support : ∀ B, Base B → B ⊆ E) : Matroid α :=
--   matroid_of_exists_finite_base E Base
--     (by { obtain ⟨B,hB⟩ := exists_base; exact ⟨B,hB, hE.subset (support _ hB)⟩ })
--     base_exchange support

-- @[simp] theorem matroid_of_base_of_finite_apply {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
--     (exists_base : ∃ B, Base B) (base_exchange : ExchangeProperty Base)
--     (support : ∀ B, Base B → B ⊆ E) :
--     (matroid_of_base_of_finite hE Base exists_base base_exchange support).Base = Base := rfl

-- /-- A collection of subsets of a finite ground set satisfying the usual independence axioms
--   determines a matroid -/
-- def matroid_of_indep_of_finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
--     (h_empty : Indep ∅)
--     (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
--     (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α :=
--   matroid_of_indep_of_bdd_augment E Indep h_empty ind_mono
--   ( fun I J hI hJ hlt ↦ ind_aug hI hJ ( by
--       rwa [← Nat.cast_lt (α := ℕ∞), (hE.subset (h_support hJ)).cast_ncard_eq,
--       (hE.subset (h_support hI)).cast_ncard_eq]) )
--   (⟨E.ncard, fun I hI ↦ by { rw [hE.cast_ncard_eq]; exact encard_mono (h_support hI) }⟩ )
--   h_support

-- instance matroid_of_indep_of_finite.Finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
--     (h_empty : Indep ∅)
--     (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
--     (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
--     ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Finite :=
--   ⟨hE⟩

-- instance matroid_of_indep_of_finite_apply {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
--     (h_empty : Indep ∅)
--     (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
--     (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
--     (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
--     ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Indep = Indep := by
--   simp [matroid_of_indep_of_finite]
