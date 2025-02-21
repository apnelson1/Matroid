import Matroid.Uniform
import Matroid.Connectivity.Skew

open Set.Notation


open Set



namespace Matroid


variable {α β : Type*} {M : Matroid α} {C K X Y B I J : Set α} {e f : α}

section IsCrossing

/-- A `Crossing` is the intersection of a circuit and a cocircuit. -/
def IsCrossing (M : Matroid α) (X : Set α) : Prop :=
  ∃ C K, M.IsCircuit C ∧ M.IsCocircuit K ∧ X = C ∩ K

lemma IsCrossing.dual (h : M.IsCrossing X) : M✶.IsCrossing X := by
  obtain ⟨C, K, hC, hK, rfl⟩ := h
  exact ⟨K, C, hK, by simpa, inter_comm C K⟩

lemma IsCrossing.of_dual (h : M✶.IsCrossing X) : M.IsCrossing X :=
  M.dual_dual.symm ▸ h.dual

@[simp] lemma isCrossing_dual_iff : M✶.IsCrossing X ↔ M.IsCrossing X :=
  ⟨IsCrossing.of_dual, IsCrossing.dual⟩

lemma IsCrossing.subset_ground (h : M.IsCrossing X) : X ⊆ M.E := by
  obtain ⟨C, K, hC, -, rfl⟩ := h
  exact inter_subset_left.trans hC.subset_ground

lemma IsCrossing.encard_ne_one (h : M.IsCrossing X) : X.encard ≠ 1 := by
  rw [Ne, encard_eq_one]
  rintro ⟨e, rfl⟩
  obtain ⟨C, K, hC, hK, h'⟩ := h
  exact hC.inter_isCocircuit_ne_singleton hK h'.symm

lemma IsCrossing.of_contract (hC : (M ／ C).IsCrossing X) : M.IsCrossing X := by
  obtain ⟨X, Y, hX, hY, rfl⟩ := hC
  obtain ⟨X', hX', hXX', hX'X⟩ := hX.subset_isCircuit_of_contract
  rw [contract_isCocircuit_iff] at hY
  refine ⟨X', Y, hX', hY.1, (inter_subset_inter_left _ hXX').antisymm
    (subset_inter ?_ inter_subset_right)⟩
  refine (inter_subset_inter_left Y hX'X).trans ?_
  rw [union_inter_distrib_right, hY.2.symm.inter_eq, union_empty]
  exact inter_subset_left

lemma IsCrossing.of_delete {D : Set α} (hD : (M ＼ D).IsCrossing X) : M.IsCrossing X := by
  have hd := hD.dual
  rw [delete_dual_eq_dual_contract] at hd
  exact hd.of_contract.of_dual

lemma IsCrossing.of_isMinor {N : Matroid α} (hX : N.IsCrossing X) (hNM : N ≤m M) :
    M.IsCrossing X := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact hX.of_delete.of_contract

lemma Iso.isCrossing_image {α β : Type*} {M : Matroid α} {N : Matroid β} {X : Set M.E} (i : M ≂ N)
    (hX : M.IsCrossing X) : N.IsCrossing ↑(i '' X) := by
  obtain ⟨C, K, hC, hK, hX⟩ := hX
  have hC' : M.IsCircuit (M.E ↓∩ C) := by simpa [inter_eq_self_of_subset_right hC.subset_ground]
  have hK' : M✶.IsCircuit (M✶.E ↓∩ K) := by simpa [inter_eq_self_of_subset_right hK.subset_ground]
  refine ⟨_, _, i.isCircuit_image hC', i.dual.isCircuit_image hK', ?_⟩
  simp only [dual_ground, dual_image]
  rw [← image_inter_on (by simp), ← image_inter_on (by simp), image_val_inj, ← preimage_inter, ← hX]
  simp

lemma IsCircuit.isCrossing_inter (hC : M.IsCircuit C) (hK : M.IsCocircuit K) :
    M.IsCrossing (C ∩ K) :=
  ⟨C, K, hC, hK, rfl⟩

lemma IsCocircuit.isCrossing_inter (hK : M.IsCocircuit K) (hC : M.IsCircuit C) :
    M.IsCrossing (K ∩ C) :=
  ⟨C, K, hC, hK, by rw [inter_comm]⟩

lemma IsCircuit.isCrossing_of_isCocircuit (hC : M.IsCircuit C) (hC' : M.IsCocircuit C) :
    M.IsCrossing C := by
  simpa using hC.isCrossing_inter hC'

end IsCrossing

section CrossingBinary

/-- A matroid is Crossing-Binary if all its finite crossings are even.
This is the same as having no U₂,₄-minor; see `crossingBinary_iff_no_U24_isMinor`.  -/
def CrossingBinary (M : Matroid α) : Prop := ∀ ⦃X : Finset α⦄, M.IsCrossing X → Even X.card

lemma CrossingBinary.even_of_finite (h : M.CrossingBinary) (hX : M.IsCrossing X) (hfin : X.Finite) :
    Even hfin.toFinset.card :=
  h (X := hfin.toFinset) (by simpa)

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
    (hC.eRk_add_one_eq.symm.trans_le (add_le_add_right (M.eRk_le_eRank C) 1)).trans
    (add_le_add_right hM 1)
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
    rw [encard_insert_of_not_mem (by simp), encard_pair (by simp)]
  obtain h | h := h
  · refine crossingBinary_of_eRank_le_one (by simp [h])
  refine (crossingBinary_of_eRank_le_one ?_).of_dual
  suffices (b : ℕ∞) ≤ a + 1 by simpa [unif_dual, add_comm]
  norm_cast

end CrossingBinary

/-- If `e` is a non-coloop point in a rank-two matroid with no `U₂,₄`-minor,
then `M ＼ e` is the disjoint union of two cocircuits. -/
lemma exist_isCocircuits_of_rank_two (hr : M.eRank = 2) (hel : ¬ M.Coloop e) (he : M.IsPoint {e})
    (hU : M.NoUniformMinor 2 4) : ∃ C₁ C₂, (M ＼ e).IsCocircuit C₁ ∧ (M ＼ e).IsCocircuit C₂ ∧
    Disjoint C₁ C₂ ∧ C₁ ∪ C₂ = M.E \ {e} := by
  have hl := he.loopless_of_singleton.delete {e}
  have heE : e ∈ M.E := by simpa using he.subset_ground
  -- Take a simplification `N` of `M`. Since `e` isn't parallel to anything else,
  -- we also have that `N ＼ e` is a simplification of `M ＼ e`.
  obtain ⟨N, hN⟩ := M.exists_isSimplification
  have heN : e ∈ N.E := he.mem_simplification hN
  have hNe : (N ＼ e).IsSimplification (M ＼ e)
  · convert hN.delete (D := {e}) (by simpa)
    simp only [deleteElem, mem_singleton_iff, iUnion_iUnion_eq_left]
    rw [setOf_parallel_eq_closure_diff_loops, he.loopless_of_singleton.closure_empty,
      he.isFlat.closure, diff_empty]
  -- Since `M` has no `U_{2,4}`-minor, we have `|N| ≤ 3` and so `|N \ e| ≤ 2`.
  replace hU := hU.minor hN.restriction.isMinor
  rw [no_line_minor_iff_of_eRank_le_two (hN.restriction.isMinor.eRank_le.trans_eq hr),
    hN.simple.simplification_eq_self, show ((4 : ℕ) : ℕ∞) = (2 : ℕ∞) + 1 + 1 by norm_num,
    ENat.lt_add_one_iff (by norm_num),
    ← encard_diff_singleton_add_one (he.mem_simplification hN),
    WithTop.add_le_add_iff_right (by simp), ← delete_ground, ← deleteElem] at hU
  -- Since `N ＼ e` has rank two and at most two elements,
  -- it must have a two-element ground set `{a,b}`.
  obtain ⟨I, hI⟩ := (N ＼ e).exists_isBase
  have hIM : (M ＼ e).IsBase I := hNe.isBase_of_isBase hI
  have hIcard : I.encard = 2
  · rwa [hI.encard_eq_eRank, hNe.eRank_eq, delete_elem_eRank_eq hel]
  obtain ⟨a,b, hab, rfl⟩ := encard_eq_two.1 hIcard
  have hIe : {a,b} = (N ＼ e).E
  · apply Finite.eq_of_subset_of_encard_le ?_ hI.subset_ground (hU.trans_eq hIcard.symm)
    rw [← encard_lt_top_iff]
    exact hU.trans_lt (by exact Batteries.compareOfLessAndEq_eq_lt.mp rfl)
  -- `N \ e` is a simplification of `M ＼ e`, so the closures of `{a}` and `{b}`
  -- form a partition of `M ＼ e`.
  have hdj : Disjoint ((M ＼ e).closure {a}) ((M ＼ e).closure {b})
  · have h := hNe.closure_pairwiseDisjoint
    rw [← hIe, pair_comm, ← union_singleton, pairwiseDisjoint_union] at h
    simpa only [pairwiseDisjoint_singleton, mem_singleton_iff, ne_eq, hab,
      forall_eq, hab.symm, not_false_eq_true, forall_const, true_and] using h
  have hpos : (M ＼ e).RankPos := hIM.rankPos_of_nonempty (by simp)
  have hucl : (M ＼ e).closure {a} ∪ (M ＼ e).closure {b} = (M ＼ e).E
  · rw [hNe.ground_eq_biUnion_closure, ← hIe]
    simp
  -- Each such closure is the complement of a hyperplane, so is a cocircuit. We're done.
  refine ⟨_, _, ?_, ?_, hdj, hucl⟩
  · rw [← compl_isHyperplane_iff_isCocircuit, ← hucl, union_diff_left, hdj.sdiff_eq_right,
      ← pair_diff_left hab]
    exact hIM.isHyperplane_of_closure_diff_singleton (by simp)
  rw [← compl_isHyperplane_iff_isCocircuit, ← hucl, union_diff_right, hdj.sdiff_eq_left,
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
  have hfl : ¬ N.Coloop f
  · simpa [hN, ← dual_isLoop_iff_coloop] using
      (hCs.compl_coindep.indep.isNonloop_of_mem hf).not_isLoop
  -- `N` has rank two, since we contracted all but one element of an independent hyperplane.
  have hNr : N.eRank = 2
  · rw [hN, eRank_contract_eq_eRelRk_ground, ← eRelRk_add_cancel _ diff_subset diff_subset,
      hCh.eRelRk_eq_one, hCi.eRelRk_of_subset diff_subset, diff_diff_cancel_left (by simpa),
      encard_singleton, one_add_one_eq_two]
  -- Since the hyperplane was independent, the remaining element is a flat.
  have hfP : N.IsPoint {f}
  · rw [IsPoint, isFlat_iff_closure_self, hN, contract_closure_eq, union_diff_cancel (by simpa)]
    simp [hCh.isFlat.closure, hf.1, hf.2, hCi.not_mem_closure_diff_of_mem hf]
  -- Therefore `C = (N ＼ f).E` is the union of two disjoint cocircuits.
  obtain ⟨C₁, C₂, hC₁, hC₂, hdj, hu⟩ := exist_isCocircuits_of_rank_two hNr hfl hfP (h_bin.minor hNM)
  -- We may assume that both are even, which contradicts oddness of `C`.
  contrapose! h_odd
  specialize h_odd (M ＼ f) (delete_isMinor ..) (by simpa [hf.2])
  simp_rw [Nat.not_odd_iff_even, ssubset_iff_subset_ne, and_imp, ne_comm (b := C)] at h_odd
  rw [hN, deleteElem, contract_delete_comm _ disjoint_sdiff_left, ← deleteElem] at hC₁ hC₂
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
    ← diff_inter_self_eq_diff, isCocircuit_def, delete_dual_eq_dual_contract]
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
  · simp only [CrossingBinary, not_forall, Classical.not_imp, Nat.not_even_iff_odd,
      exists_and_left] at h
    obtain ⟨X, hX, hodd⟩ := h
    exact exists_uniformMinor_of_odd_isCrossing hX hodd

  simp only [not_noUniformMinor_iff] at h
  simpa [crossingBinary_unif_iff] using hbin.isoMinor h.some

section Cyclic

variable {A : Set α}
