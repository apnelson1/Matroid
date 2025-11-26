import Matroid.Tame

open Set.Notation
open Set

namespace Matroid

variable {α β : Type*} {M : Matroid α} {C K X Y B I J : Set α} {e f : α}

section CrossingBinary

/-- A matroid is Crossing-Binary if all its finite crossings are even.
This is the same as having no U₂,₄-minor; see `crossingBinary_iff_no_U24_isMinor`.  -/
def CrossingBinary (M : Matroid α) : Prop := ∀ ⦃X : Finset α⦄, M.IsCrossing X → Even X.card

lemma CrossingBinary.even_of_finite (h : M.CrossingBinary) (hX : M.IsCrossing X) (hfin : X.Finite) :
    Even hfin.toFinset.card :=
  h (X := hfin.toFinset) (by simpa)

lemma CrossingBinary.even_of_isCrossing (h : M.CrossingBinary) (hX : M.IsCrossing X) :
    Even X.encard := by
  obtain hfin | hinf := X.finite_or_infinite
  · rw [hfin.encard_eq_coe_toFinset_card, ENat.even_natCast]
    exact h.even_of_finite hX hfin
  simp [hinf.encard_eq]

lemma CrossingBinary.dual (hM : M.CrossingBinary) : M✶.CrossingBinary :=
  fun _ hX ↦ hM hX.of_dual

lemma CrossingBinary.of_dual (hM : M✶.CrossingBinary) : M.CrossingBinary :=
  fun _ hX ↦ hM hX.dual

@[simp] lemma CrossingBinary_dual_iff : M✶.CrossingBinary ↔ M.CrossingBinary :=
  ⟨CrossingBinary.of_dual, CrossingBinary.dual⟩

lemma CrossingBinary.of_isMinor {N M : Matroid α} (hM : M.CrossingBinary) (hNM : N ≤m M) :
    N.CrossingBinary := by
  refine fun X hX ↦ hM <| hX.of_isMinor hNM

lemma CrossingBinary.iso {N : Matroid β} (hM : M.CrossingBinary) (i : M ≂ N) :
    N.CrossingBinary := by
  intro X hX
  have hX' : N.IsCrossing (N.E ↓∩ X) := by
    simpa [inter_eq_self_of_subset_right hX.subset_ground]
  have hcard_eq : (Subtype.val '' (⇑i ⁻¹' N.E ↓∩ ↑X)).encard = (X : Set β).encard
  · rw [Subtype.val_injective.injOn.encard_image,
      encard_preimage_of_injective_subset_range (EmbeddingLike.injective' i) (by simp),
      encard_preimage_of_injective_subset_range Subtype.val_injective
        (by simpa using hX.subset_ground)]
  have hfin : (Subtype.val '' (⇑i.symm '' N.E ↓∩ ↑X)).Finite
  · simp [← encard_ne_top_iff, hcard_eq]
  convert hM.even_of_finite (i.symm.isCrossing_image hX') hfin
  rw [← Nat.cast_inj (R := ℕ∞), ← encard_coe_eq_coe_finsetCard, ← hcard_eq,
    ← encard_coe_eq_coe_finsetCard]
  simp

lemma CrossingBinary.isoMinor {N : Matroid β} (hM : M.CrossingBinary) (e : N ≤i M) :
    N.CrossingBinary := by
  obtain ⟨M₀, hM₀M, i, -⟩ := e.exists_iso
  exact (hM.of_isMinor hM₀M).iso i.symm

lemma crossingBinary_of_eRank_le_one (hM : M.eRank ≤ 1) : M.CrossingBinary := by
  intro X hX
  obtain ⟨C, K, hC, hK, hX'⟩ := id hX
  have hC' : C.encard ≤ 2 :=
    (hC.eRk_add_one_eq.symm.trans_le (add_le_add_left (M.eRk_le_eRank C) 1)).trans
    (add_le_add_left hM 1)
  replace hX' := (encard_le_encard (hX'.subset.trans inter_subset_left)).trans hC'
  rw [encard_coe_eq_coe_finsetCard, Nat.cast_le_ofNat] at hX'
  obtain (h | h | h) : X.card = 1 ∨ X.card = 0 ∨ X.card = 2 := by omega
  · simpa [h] using hX.encard_ne_one
  · simp [h]
  simp [h]

/-- CrossingBinary uniform matroids have rank or corank at most one. -/
lemma crossingBinary_unif_iff {a b : ℕ} : (unif a b).CrossingBinary ↔ a ≤ 1 ∨ b ≤ a + 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [or_iff_not_imp_left, not_le, ← not_lt, Nat.lt_iff_add_one_le, one_add_one_eq_two]
    intro h2a hab
    have hm : Nonempty (unif 2 4 ≤i unif a b)
    · rw [unif_isoMinor_unif_iff' (by simp) (by linarith), Nat.le_sub_iff_add_le (by linarith)]
      exact ⟨h2a, by linarith⟩
    have h_even := h.isoMinor hm.some (X := {0,1,2}) ⟨{0,1,2}, {0,1,2}, ?_⟩
    · simp [Nat.even_iff] at h_even
    simp [unif_isCircuit_iff, isCocircuit_def, unif_dual]
    rw [encard_insert_of_notMem (by simp), encard_pair (by simp)]
  obtain h | h := h
  · refine crossingBinary_of_eRank_le_one (by simp [h])
  refine (crossingBinary_of_eRank_le_one ?_).of_dual
  suffices (b : ℕ∞) ≤ a + 1 by simpa [unif_dual, add_comm]
  norm_cast

end CrossingBinary

/-- If `e` is a non-coloop point in a rank-two matroid with no `U₂,₄`-minor,
then `M ＼ e` is the disjoint union of two cocircuits. -/
lemma exist_isCocircuits_of_rank_two (hr : M.eRank = 2) (hel : ¬ M.IsColoop e) (he : M.IsPoint {e})
    (hU : M.NoUniformMinor 2 4) : ∃ C₁ C₂, (M ＼ {e}).IsCocircuit C₁ ∧ (M ＼ {e}).IsCocircuit C₂ ∧
    Disjoint C₁ C₂ ∧ C₁ ∪ C₂ = M.E \ {e} := by
  have hl := he.loopless_of_singleton.delete {e}
  have heE : e ∈ M.E := by simpa using he.subset_ground
  -- Take a simplification `N` of `M`. Since `e` isn't parallel to anything else,
  -- we also have that `N ＼ e` is a simplification of `M ＼ e`.
  obtain ⟨N, hN⟩ := M.exists_isSimplification
  have heN : e ∈ N.E := he.mem_simplification hN
  have hNe : (N ＼ {e}).IsSimplification (M ＼ {e})
  · convert hN.delete (D := {e}) (by simpa)
    simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
    rw [setOf_parallel_eq_closure_diff_loops, he.loopless_of_singleton.loops_eq_empty,
      he.isFlat.closure, diff_empty]
  -- Since `M` has no `U_{2,4}`-minor, we have `|N| ≤ 3` and so `|N \ e| ≤ 2`.
  replace hU := hU.minor hN.isRestriction.isMinor
  rw [no_line_minor_iff_of_eRank_le_two (hN.isRestriction.isMinor.eRank_le.trans_eq hr),
    hN.simple.simplification_eq_self, show ((4 : ℕ) : ℕ∞) = (2 : ℕ∞) + 1 + 1 by norm_num,
    ENat.lt_add_one_iff (by norm_num),
    ← encard_diff_singleton_add_one (he.mem_simplification hN),
    WithTop.add_le_add_iff_right (by simp), ← delete_ground] at hU
  -- Since `N ＼ e` has rank two and at most two elements,
  -- it must have a two-element ground set `{a,b}`.
  obtain ⟨I, hI⟩ := (N ＼ {e}).exists_isBase
  have hIM : (M ＼ {e}).IsBase I := hNe.isBase_of_isBase hI
  have hIcard : I.encard = 2
  · rwa [hI.encard_eq_eRank, hNe.eRank_eq, deleteElem_eRank_eq hel]
  obtain ⟨a,b, hab, rfl⟩ := encard_eq_two.1 hIcard
  have hIe : {a,b} = (N ＼ {e}).E
  · apply Finite.eq_of_subset_of_encard_le ?_ hI.subset_ground (hU.trans_eq hIcard.symm)
    rw [← encard_lt_top_iff, hIcard]
    decide
  -- `N \ e` is a simplification of `M ＼ e`, so the closures of `{a}` and `{b}`
  -- form a partition of `M ＼ e`.
  have hdj : Disjoint ((M ＼ {e}).closure {a}) ((M ＼ {e}).closure {b})
  · have h := hNe.closure_pairwiseDisjoint
    rw [← hIe, pair_comm, ← union_singleton, pairwiseDisjoint_union] at h
    simpa only [pairwiseDisjoint_singleton, mem_singleton_iff, ne_eq, hab,
      forall_eq, hab.symm, not_false_eq_true, forall_const, true_and] using h
  have hpos : (M ＼ {e}).RankPos := hIM.rankPos_of_nonempty (by simp)
  have hucl : (M ＼ {e}).closure {a} ∪ (M ＼ {e}).closure {b} = (M ＼ {e}).E
  · rw [hNe.ground_eq_biUnion_closure, ← hIe]
    simp
  -- Each such closure is the complement of a hyperplane, so is a cocircuit. We're done.
  refine ⟨_, _, ?_, ?_, hdj, hucl⟩
  · rw [← isHyperplane_compl_iff_isCocircuit, ← hucl, union_diff_left, hdj.sdiff_eq_right,
      ← pair_diff_left hab]
    exact hIM.isHyperplane_of_closure_diff_singleton (by simp)
  rw [← isHyperplane_compl_iff_isCocircuit, ← hucl, union_diff_right, hdj.sdiff_eq_left,
    ← pair_diff_right hab]
  exact hIM.isHyperplane_of_closure_diff_singleton (by simp)

/-- If `C` is a spanning/cospanning circuit/cocircuit of finite odd cardinality in a matroid `M`
with no `U₂,₄`-minor, then there is an odd proper subset of `C` that is a cocircuit/cocircuit
in a minor of `M`.   -/
lemma exists_smaller_of_odd_isCircuit_isCocircuit (hfin : C.Finite) (hCc : M.IsCircuit C)
    (hCk : M.IsCocircuit C) (hCs : M.Spanning C) (hCcs : M✶.Spanning C)
    (h_odd : Odd hfin.toFinset.card) (h_bin : M.NoUniformMinor 2 4) :
    ∃ (N : Matroid α), N ≤m M ∧ N.IsCircuit C ∧ ∃ (K : Finset α),
      N.IsCocircuit K ∧ (K : Set α) ⊂ C ∧ Odd K.card := by
  classical
  have hCh := hCk.compl_isHyperplane
  have hCi : M.Indep (M.E \ C) := by simpa using hCcs.compl_coindep
  -- Since `M` has an odd crossing, it has rank at least `2`.
  have hr : 2 ≤ M.eRank := by
    obtain ⟨C, rfl⟩ := hfin.exists_finset_coe
    contrapose! h_odd with hlt
    simpa using (M.crossingBinary_of_eRank_le_one <| Order.le_of_lt_add_one hlt)
      (hCc.isCrossing_of_isCocircuit hCk)
  -- `M.E \ C` cannot be empty, since this would make `M` a rank-one matroid. Let `f ∈ M.E \ C`.
  obtain ⟨f, hf⟩ : (M.E \ C).Nonempty := nonempty_iff_ne_empty.2 fun hss ↦ by
    simpa [hss] using hr.trans_eq hCh.eRk_add_one_eq.symm
  -- Now contract all but one element of `M.E \ C`.
  set N := M ／ ((M.E \ C) \ {f}) with hN
  have hNE : C = N.E \ {f} := by
    rw [hN, contract_ground, diff_diff, diff_union_self, union_singleton,
      insert_eq_self.2 hf, diff_diff_cancel_left hCc.subset_ground]
  have hNM : N ≤m M := contract_isMinor _ _
  -- Since `f` is in the coindependent set `M.E \ C`, it is not a coloop of `M` or `N`.
  have hfl : ¬ N.IsColoop f
  · simpa [hN, ← dual_isLoop_iff_isColoop] using
      (hCs.compl_coindep.indep.isNonloop_of_mem hf).not_isLoop
  -- `N` has rank two, since we contracted all but one element of an independent hyperplane.
  have hNr : N.eRank = 2
  · rw [hN, eRank_contract_eq_eRelRk_ground, ← eRelRk_add_cancel _ diff_subset diff_subset,
      hCh.eRelRk_eq_one, hCi.eRelRk_of_subset diff_subset, diff_diff_cancel_left (by simpa),
      encard_singleton, one_add_one_eq_two]
  -- Since the hyperplane was independent, the remaining element is a flat.
  have hfP : N.IsPoint {f}
  · rw [IsPoint, isFlat_iff_closure_self, hN, contract_closure_eq, union_diff_cancel (by simpa)]
    simp [hCh.isFlat.closure, hf.1, hf.2, hCi.notMem_closure_diff_of_mem hf]
  -- Therefore `C = (N ＼ f).E` is the union of two disjoint cocircuits.
  obtain ⟨C₁, C₂, hC₁, hC₂, hdj, hu⟩ := exist_isCocircuits_of_rank_two hNr hfl hfP (h_bin.minor hNM)
  -- We may assume that both are even, which contradicts oddness of `C`.
  contrapose! h_odd
  specialize h_odd (M ＼ {f}) (delete_isMinor ..) (by simpa [hf.2])
  simp_rw [Nat.not_odd_iff_even, ssubset_iff_subset_ne, and_imp, ne_comm (b := C)] at h_odd
  rw [hN, contract_delete_comm _ disjoint_sdiff_left] at hC₁ hC₂
  obtain rfl : C₁ ∪ C₂ = C := by rw [hu, hNE]
  obtain ⟨C₁, rfl⟩ := (hfin.subset subset_union_left).exists_finset_coe
  obtain ⟨C₂, rfl⟩ := (hfin.subset subset_union_right).exists_finset_coe
  rw [Finset.disjoint_coe] at hdj
  have h₁ := h_odd C₁ hC₁.of_contract subset_union_left ?_
  · have h₂ := h_odd C₂ hC₂.of_contract subset_union_right ?_
    · simpa [Nat.not_odd_iff_even, ← Finset.card_union_of_disjoint hdj] using h₁.add h₂
    rw [ne_eq, union_eq_right, Finset.coe_subset, ← Finset.sdiff_eq_empty_iff_subset,
      hdj.sdiff_eq_left]
    simpa using hC₁.nonempty.ne_empty
  rw [ne_eq, union_eq_left, Finset.coe_subset, ← Finset.sdiff_eq_empty_iff_subset,
    hdj.sdiff_eq_right]
  simpa using hC₂.nonempty.ne_empty

/-- For any nonempty crossing `X` of `M`,
we can find a minor of `M` in which `X` is a spanning/cospanning circuit/cocircuit.-/
lemma IsCrossing.exists_isMinor_isCircuit_isCocircuit (hX : M.IsCrossing X) (hXne : X.Nonempty) :
    ∃ N, N ≤m M ∧ N.IsCircuit X ∧ N.IsCocircuit X ∧ N.Spanning X ∧ N✶.Spanning X := by
  obtain ⟨C, K, hC, hK, rfl⟩ := hX
  have hdj1 : Disjoint (C ∩ K) (K \ C) := disjoint_sdiff_right.mono_left inter_subset_left
  have hdj2 : Disjoint (C ∩ K) (C \ K) := disjoint_sdiff_right.mono_left inter_subset_right
  set N₁ := M ／ (C \ K) ＼ (K \ C) with hN₁
  have hXE : C ∩ K ⊆ N₁.E := by
    rw [hN₁, delete_ground, contract_ground, diff_diff, subset_diff,
      and_iff_right (inter_subset_left.trans hC.subset_ground)]
    simp [hdj1, hdj2]
  obtain ⟨N₂, hN₂N₁, hN₂r, hN₂r', hsp, hcsp⟩ :=
    N₁.exists_isMinor_restrict_corestrict_eq_spanning_cospanning hXE
  refine ⟨N₂, hN₂N₁.trans (contract_delete_isMinor ..), ?_, ?_, hsp, hcsp⟩
  · rw [isCircuit_iff_restr_eq_circuitOn hXne, hN₂r, ← isCircuit_iff_restr_eq_circuitOn hXne,
      hN₁, delete_isCircuit_iff, and_iff_left hdj1, ← diff_self_inter]
    apply hC.contract_diff_isCircuit hXne inter_subset_left
  rw [IsCocircuit, isCircuit_iff_restr_eq_circuitOn hXne, hN₂r',
    ← isCircuit_iff_restr_eq_circuitOn hXne, ← isCocircuit_def, hN₁,
    contract_delete_comm _ disjoint_sdiff_sdiff, contract_isCocircuit_iff, and_iff_left hdj2,
    ← diff_inter_self_eq_diff, isCocircuit_def, dual_delete]
  exact hK.isCircuit.contract_diff_isCircuit hXne inter_subset_right

lemma exists_uniformMinor_of_odd_isCrossing {M : Matroid α} {X : Finset α} (hX : M.IsCrossing X)
    (h_odd : Odd X.card) : ¬ M.NoUniformMinor 2 4  := by
  have hne : X.Nonempty := by
    rw [← Finset.card_ne_zero]
    exact Nat.ne_of_odd_add h_odd
  -- Take a minor of `M` in which `X` is a spanning/cospanning circuit/cocircuit.
  obtain ⟨N, hNM, hXc, hXk, hXsp, hXcsp⟩ := hX.exists_isMinor_isCircuit_isCocircuit hne
  intro hcon
  obtain ⟨N₃, hN₃N, hN₃C, C₀, hN₃, hssu, h_odd'⟩ :=
    exists_smaller_of_odd_isCircuit_isCocircuit (by simp) hXc hXk (by simpa) hXcsp (by simpa)
      (hcon.minor hNM)
  -- Take a minor with a smaller odd crossing, and apply induction.
  have hcr : N₃.IsCrossing C₀ := ⟨_, _, hN₃C, hN₃,
    by rw [inter_eq_self_of_subset_right hssu.subset]⟩
  have hlt := Finset.card_strictMono hssu
  exact exists_uniformMinor_of_odd_isCrossing hcr h_odd' <| (hcon.minor (hN₃N.trans hNM))
termination_by X.card

theorem crossingBinary_iff_no_U24_isMinor (M : Matroid α) :
    M.CrossingBinary ↔ M.NoUniformMinor 2 4 := by
  rw [← not_iff_not]
  refine ⟨fun h ↦ ?_, fun h hbin ↦ ?_⟩
  · simp only [CrossingBinary, not_forall, Nat.not_even_iff_odd] at h
    obtain ⟨X, hX, hodd⟩ := h
    exact exists_uniformMinor_of_odd_isCrossing hX hodd

  simp only [not_noUniformMinor_iff] at h
  simpa [crossingBinary_unif_iff] using hbin.isoMinor h.some

section Cyclic

variable {A : Set α}

lemma Even.add_even [Semiring α] {a b : α} (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  rw [add_right_comm, ← add_assoc, add_comm a b, add_assoc]
  exact ⟨b + a, rfl⟩

-- lemma foo (hM : M.CrossingBinary) (hA : M.Cyclic A) (hAfin : A.Finite) (hK : M.IsCocircuit K) :
--     Even (A ∩ K).encard := by
--   classical
--   obtain ⟨A, rfl⟩ := hAfin.exists_finset_coe
--   induction' A using Finset.strongInduction with A IH
--   obtain rfl | hne := A.eq_empty_or_nonempty
--   · simp
--   obtain ⟨C, hCA, hC⟩ := (hA.dep_of_nonempty hne).exists_isCircuit_subset
--   obtain ⟨C, rfl⟩ := (hAfin.subset hCA).exists_finset_coe
--   have hcard {K'} (hK' : M.IsCocircuit K') :
--       Even (((A \ C : Finset α) : Set α) ∩ K').encard ↔ Even (A ∩ K' : Set α).encard := by
--     rw [← diff_union_of_subset hCA, union_inter_distrib_right, encard_union_eq (by tauto_set),
--       ENat.even_add, iff_true_intro (hM.even_of_isCrossing (hC.isCrossing_inter hK')), iff_true,
--       Finset.coe_sdiff]
--     · simp only [ne_eq, encard_eq_top_iff, not_infinite]
--       exact hAfin.subset (by tauto_set)
--     simp only [ne_eq, encard_eq_top_iff, not_infinite]
--     exact hAfin.subset (by tauto_set)

--   have hssu : A \ C ⊂ A := by
--     have := diff_ssubset hCA hC.nonempty
--     norm_cast at this
--   have h_even := IH _ hssu ?_ (Finset.finite_toSet ..)
--   · rwa [← hcard hK]
--   rw [cyclic_iff_forall_inter_isCocircuit_encard_ne
--(by simp [diff_subset.trans hA.subset_ground])]
--   intro K' hK' h1
--   have hne : ¬ Even (((A \ C : Finset α) : Set α) ∩ K').encard := by
--     rw [h1, ← Nat.cast_one, ENat.even_natCast]
--     exact Nat.not_even_one

  -- rw [hcard hK] at hne






    -- refine Finset.sdiff_subset.ssubset_of_ne fun h_eq ↦ ?_
    -- have : C.Nonempty := by simpa using hC.nonempty





  -- have := IH (A \ C) (Finset.diff_subset.ss)



  -- obtain ⟨C, A₀, hCA₀, hA₀A, hC, hA₀, hu⟩ := hA.exists_eq_union_isCircuit_cyclic_ssubset hne



  -- refine Set.Finite.induction_on A hA (by simp) ?_


-- lemma CrossingBinary.cyclic_iff_forall_inter_isCocircuit_even
--     (hM : M.CrossingBinary) (hA : A.Finite) (hAE : A ⊆ M.E := by aesop_mat) :
--     M.Cyclic A ↔ ∀ K, M.IsCocircuit K → Even (A ∩ K).encard := by
--   refine ⟨fun h K hK ↦ ?_,
--     fun h ↦ (cyclic_iff_forall_inter_isCocircuit_encard_ne hAE).2 fun K hK h_even ↦ ?_⟩
--   · obtain rfl | hne := A.eq_empty_or_nonempty
--     · simp
--     obtain ⟨C, A₀, hCA, hA₀A, hC, hA₀, hssu⟩ := h.exists_eq_union_isCircuit_cyclic_ssubset hne
--     have hlt : A₀.encard < A.encard := by
--       sorry
--     have := CrossingBinary.cyclic_iff_forall_inter_isCocircuit_even

--     -- rw [← hssu, ← union_diff_self, union_inter_distrib_right, encard_union_eq]
--     -- ·

--   obtain ⟨r, hr⟩ := h K hK
--   rw [h_even] at hr
--   enat_to_nat
--   omega
-- decreasing_by hlt
