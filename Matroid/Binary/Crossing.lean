import Matroid.Uniform
import Matroid.Connectivity.Skew

open Set.Notation


open Set



namespace Matroid


variable {α β : Type*} {M : Matroid α} {C K X Y B I J : Set α} {e f : α}

section Crossing

/-- A `Crossing` is the intersection of a circuit and a cocircuit. -/
def Crossing (M : Matroid α) (X : Set α) := ∃ C K, M.IsCircuit C ∧ M.Cocircuit K ∧ X = C ∩ K

lemma Crossing.dual (h : M.Crossing X) : M✶.Crossing X := by
  obtain ⟨C, K, hC, hK, rfl⟩ := h
  exact ⟨K, C, hK, by simpa, inter_comm C K⟩

lemma Crossing.of_dual (h : M✶.Crossing X) : M.Crossing X :=
  M.dual_dual.symm ▸ h.dual

@[simp] lemma crossing_dual_iff : M✶.Crossing X ↔ M.Crossing X :=
  ⟨Crossing.of_dual, Crossing.dual⟩

lemma Crossing.subset_ground (h : M.Crossing X) : X ⊆ M.E := by
  obtain ⟨C, K, hC, -, rfl⟩ := h
  exact inter_subset_left.trans hC.subset_ground

lemma Crossing.encard_ne_one (h : M.Crossing X) : X.encard ≠ 1 := by
  rw [Ne, encard_eq_one]
  rintro ⟨e, rfl⟩
  obtain ⟨C, K, hC, hK, h'⟩ := h
  exact hC.inter_cocircuit_ne_singleton hK h'.symm

lemma Crossing.of_contract (hC : (M ／ C).Crossing X) : M.Crossing X := by
  obtain ⟨X, Y, hX, hY, rfl⟩ := hC
  obtain ⟨X', hX', hXX', hX'X⟩ := hX.subset_isCircuit_of_contract
  rw [contract_cocircuit_iff] at hY
  refine ⟨X', Y, hX', hY.1, (inter_subset_inter_left _ hXX').antisymm
    (subset_inter ?_ inter_subset_right)⟩
  refine (inter_subset_inter_left Y hX'X).trans ?_
  rw [union_inter_distrib_right, hY.2.symm.inter_eq, union_empty]
  exact inter_subset_left

lemma Crossing.of_delete {D : Set α} (hD : (M ＼ D).Crossing X) : M.Crossing X := by
  have hd := hD.dual
  rw [delete_dual_eq_dual_contract] at hd
  exact hd.of_contract.of_dual

lemma Crossing.of_minor {N : Matroid α} (hX : N.Crossing X) (hNM : N ≤m M) : M.Crossing X := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact hX.of_delete.of_contract

lemma Iso.crossing_image {α β : Type*} {M : Matroid α} {N : Matroid β} {X : Set M.E}
    (i : M ≂ N) (hX : M.Crossing X) : N.Crossing ↑(i '' X) := by
  obtain ⟨C, K, hC, hK, hX⟩ := hX
  have hC' : M.IsCircuit (M.E ↓∩ C) := by simpa [inter_eq_self_of_subset_right hC.subset_ground]
  have hK' : M✶.IsCircuit (M✶.E ↓∩ K) := by simpa [inter_eq_self_of_subset_right hK.subset_ground]
  refine ⟨_, _, i.isCircuit_image hC', i.dual.isCircuit_image hK', ?_⟩
  simp only [dual_ground, dual_image]
  rw [← image_inter_on (by simp), ← image_inter_on (by simp), image_val_inj, ← preimage_inter, ← hX]
  simp

lemma IsCircuit.crossing_inter (hC : M.IsCircuit C) (hK : M.Cocircuit K) : M.Crossing (C ∩ K) :=
  ⟨C, K, hC, hK, rfl⟩

lemma Cocircuit.crossing_inter (hK : M.Cocircuit K) (hC : M.IsCircuit C) : M.Crossing (K ∩ C) :=
  ⟨C, K, hC, hK, by rw [inter_comm]⟩

end Crossing

section Binary

/-- A matroid is Crossing-Binary if all its finite crossings are even.
This is the same as having no U₂,₄-minor; see `binary_iff_no_U24_minor`.
Relating this to binary representations is still TODO.  -/
def Binary (M : Matroid α) : Prop := ∀ ⦃X : Finset α⦄, M.Crossing X → Even X.card

lemma Binary.even_of_finite (h : M.Binary) (hX : M.Crossing X) (hfin : X.Finite) :
    Even hfin.toFinset.card :=
  h (X := hfin.toFinset) (by simpa)

lemma Binary.dual (hM : M.Binary) : M✶.Binary :=
  fun _ hX ↦ hM hX.of_dual

lemma Binary.of_dual (hM : M✶.Binary) : M.Binary :=
  fun _ hX ↦ hM hX.dual

@[simp] lemma Binary_dual_iff : M✶.Binary ↔ M.Binary :=
  ⟨Binary.of_dual, Binary.dual⟩

lemma Binary.minor {N M : Matroid α} (hM : M.Binary) (hNM : N ≤m M) :
    N.Binary := by
  refine fun X hX ↦ hM <| hX.of_minor hNM

lemma Binary.iso {N : Matroid β} (hM : M.Binary) (i : M ≂ N) :
    N.Binary := by
  intro X hX
  have hX' : N.Crossing (N.E ↓∩ X) := by
    simpa [inter_eq_self_of_subset_right hX.subset_ground]
  have hcard_eq : (Subtype.val '' (⇑i ⁻¹' N.E ↓∩ ↑X)).encard = (X : Set β).encard
  · rw [Subtype.val_injective.injOn.encard_image,
      encard_preimage_of_injective_subset_range (EmbeddingLike.injective' i) (by simp),
      encard_preimage_of_injective_subset_range Subtype.val_injective
        (by simpa using hX.subset_ground)]

  have hfin : (Subtype.val '' (⇑i.symm '' N.E ↓∩ ↑X)).Finite
  · simp [← encard_ne_top_iff, hcard_eq]

  convert hM.even_of_finite (i.symm.crossing_image hX') hfin
  rw [← Nat.cast_inj (R := ℕ∞), ← encard_coe_eq_coe_finsetCard, ← hcard_eq,
    ← encard_coe_eq_coe_finsetCard]
  simp

lemma Binary.isoMinor {N : Matroid β} (hM : M.Binary) (e : N ≤i M) :
    N.Binary := by
  obtain ⟨M₀, hM₀M, i, -⟩ := e.exists_iso
  exact (hM.minor hM₀M).iso i.symm

lemma binary_of_eRank_le_one (hM : M.eRank ≤ 1) : M.Binary := by
  intro X hX
  obtain ⟨C, K, hC, hK, hX'⟩ := id hX
  have hC' : C.encard ≤ 2 :=
    (hC.eRk_add_one_eq.symm.trans_le (add_le_add_right (M.eRk_le_eRank C) 1)).trans
    (add_le_add_right hM 1)
  replace hX' := (encard_le_encard (hX'.subset.trans inter_subset_left)).trans hC'
  rw [encard_coe_eq_coe_finsetCard, Nat.cast_le_ofNat] at hX'
  obtain (h | h | h) : X.card = 1 ∨ X.card = 0 ∨ X.card = 2 := by omega
  · simpa [h] using hX.encard_ne_one
  simp [h]
  simp [h]

lemma binary_unif_iff {a b : ℕ} : (unif a b).Binary ↔ a ≤ 1 ∨ b ≤ a + 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [or_iff_not_imp_left, not_le, ← not_lt, Nat.lt_iff_add_one_le, one_add_one_eq_two]
    intro h2a hab
    have hm : Nonempty (unif 2 4 ≤i unif a b)
    · rw [unif_isoMinor_unif_iff' (by simp) (by linarith), Nat.le_sub_iff_add_le (by linarith)]
      exact ⟨h2a, by linarith⟩
    have h_even := h.isoMinor hm.some (X := {0,1,2}) ⟨{0,1,2}, {0,1,2}, ?_⟩
    · simp [Nat.even_iff] at h_even
    simp [unif_isCircuit_iff, cocircuit_def, unif_dual]
    rw [encard_insert_of_not_mem (by simp), encard_pair (by simp)]
  obtain h | h := h
  · refine binary_of_eRank_le_one (by simp [h])
  refine (binary_of_eRank_le_one ?_).of_dual
  suffices (b : ℕ∞) ≤ a + 1 by simpa [unif_dual, add_comm]
  norm_cast

end Binary

lemma exist_cocircuits_of_rank_two (hr : M.eRank = 2) (hel : ¬ M.Coloop e) (he : M.IsPoint {e})
    (hU : M.NoUniformMinor 2 4) : ∃ C₁ C₂, (M ＼ e).Cocircuit C₁ ∧ (M ＼ e).Cocircuit C₂ ∧
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
  replace hU := hU.minor hN.restriction.minor
  rw [no_line_minor_iff_of_eRank_le_two (hN.restriction.minor.eRank_le.trans_eq hr),
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
  · rw [← compl_isHyperplane_iff_cocircuit, ← hucl, union_diff_left, hdj.sdiff_eq_right,
      ← pair_diff_left hab]
    exact hIM.isHyperplane_of_closure_diff_singleton (by simp)
  rw [← compl_isHyperplane_iff_cocircuit, ← hucl, union_diff_right, hdj.sdiff_eq_left,
    ← pair_diff_right hab]
  exact hIM.isHyperplane_of_closure_diff_singleton (by simp)

lemma exists_smaller_of_odd_isCircuit_cocircuit (hfin : C.Finite) (hCc : M.IsCircuit C)
    (h_odd : Odd hfin.toFinset.card) (hCs : M.Spanning C) (hCh : M.IsHyperplane (M.E \ C))
    (hCi : M.Indep (M.E \ C)) (hcard : 3 ≤ C.encard) (h_bin : M.NoUniformMinor 2 4) :
  ∃ (N : Matroid α) (K : Finset α),
    N ≤m M ∧ N.IsCircuit C ∧ N.Cocircuit K ∧ (K : Set α) ⊂ C ∧ Odd K.card := by

  classical
  obtain ⟨f, hf⟩ : (M.E \ C).Nonempty
  · rw [nonempty_iff_ne_empty]
    intro hss
    have hle := (M.eRk_le_eRank C).trans_eq hCh.eRk_add_one_eq.symm
    rw [hss, eRk_empty, zero_add, ← WithTop.add_le_add_iff_right (show 1 ≠ ⊤ by simp),
      hCc.eRk_add_one_eq] at hle
    have hcon := hcard.trans hle
    norm_num at hcon

  set N := M ／ ((M.E \ ↑C) \ {f}) with hN
  have hNM : N ≤m M := contract_minor _ _

  have hfl : ¬ N.Coloop f
  · simpa [hN, ← dual_loop_iff_coloop] using (hCs.compl_coindep.indep.nonloop_of_mem hf).not_loop

  have hNr : N.eRank = 2
  · obtain ⟨e, he, hbas⟩ := hCh.exists_insert_isBase_of_isBasis (hCi.isBasis_self)
    simp only [sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff, Finset.mem_coe] at he
    have hb' : N.IsBase {e, f}
    · rw [hN, (hCi.diff _).contract_isBase_iff, ← singleton_union, union_assoc, disjoint_union_left]
      simpa [hf, he.1, he.2]
    rw [← hb'.encard_eq_eRank, encard_pair (by rintro rfl; exact hf.2 he.2)]

  have hfP : N.IsPoint {f}
  · rw [IsPoint, isFlat_iff_closure_self, hN, contract_closure_eq, union_diff_cancel (by simpa)]
    simp [hCh.isFlat.closure, hf.1, hf.2, hCi.not_mem_closure_diff_of_mem hf]


  obtain ⟨C₁, C₂, hC₁, hC₂, hdj, hu⟩ := exist_cocircuits_of_rank_two hNr hfl hfP (h_bin.minor hNM)

  obtain rfl : C₁ ∪ C₂ = C
  · simpa [hu, hN, diff_diff_right, inter_eq_self_of_subset_right hCc.subset_ground,
      show M.E ∩ {f} = {f} by simpa using hf.1] using hf.2

  have hnss1 : ¬ C₁ ⊆ C₂
  · simpa [← diff_eq_empty, hdj.sdiff_eq_left, ← nonempty_iff_ne_empty] using hC₁.nonempty

  have hnss2 : ¬ C₂ ⊆ C₁
  · simpa [← diff_eq_empty, hdj.sdiff_eq_right, ← nonempty_iff_ne_empty] using hC₂.nonempty

  contrapose! h_odd

  rw [hN, deleteElem, contract_delete_comm _ (by simp)] at hC₁ hC₂

  have hfin' := hfin
  rw [finite_union] at hfin'

  obtain ⟨C₁, rfl⟩ := hfin'.1.exists_finset_coe
  obtain ⟨C₂, rfl⟩ := hfin'.2.exists_finset_coe

  have hC₁_even : ¬ Odd C₁.card :=
    h_odd (M ＼ f) C₁ (delete_minor _ _) (by simpa [hf.2]) hC₁.of_contract (by simpa)

  have hC₂_even : ¬ Odd C₂.card :=
    h_odd (M ＼ f) C₂ (delete_minor _ _) (by simpa [hf.2]) hC₂.of_contract (by simpa)

  rw [Nat.not_odd_iff_even] at hC₁_even hC₂_even ⊢
  rw [toFinite_toFinset, toFinset_union, Finset.toFinset_coe, Finset.toFinset_coe,
    Finset.card_union_eq_card_add_card.2 (by simpa using hdj)]
  exact hC₁_even.add hC₂_even

lemma IsCircuit.exists_minor_inter_isCircuit_cocircuit_of_cocircuit (hC : M.IsCircuit C)
    (hK : M.Cocircuit K) (h_inter : (C ∩ K).Nonempty) :
    ∃ N, N ≤m M ∧ N.IsCircuit (C ∩ K) ∧ N.Cocircuit (C ∩ K) := by
  refine ⟨M ／ (C \ K) ＼ (K \ C), contract_delete_minor _ _ _, ?_, ?_⟩
  · simpa [delete_isCircuit_iff, disjoint_sdiff_right.mono_left inter_subset_left]
      using hC.contract_isCircuit (C := C \ K) (by simpa)
  simp only [contract_delete_comm _ disjoint_sdiff_sdiff, contract_cocircuit_iff,
    disjoint_sdiff_right.mono_left inter_subset_right, and_true]
  rw [cocircuit_def, delete_dual_eq_dual_contract]
  simpa [inter_comm C K] using hK.isCircuit.contract_isCircuit (C := K \ C) (by simpa [inter_comm])

lemma IsCircuit.exists_minor_spanning_cospanning_of_cocircuit (hC : M.IsCircuit C)
    (hK : M.Cocircuit C) :
    ∃ N, N ≤m M ∧ N.IsCircuit C ∧ N.Cocircuit C ∧ N.Spanning C ∧ N✶.Spanning C := by
  obtain ⟨N, hNM, hr, hcr, hsp, hcsp⟩ :=
    exists_minor_restrict_corestrict_eq_spanning_cospanning hC.subset_ground
  refine ⟨N, hNM, ?_, ?_, hsp, hcsp⟩
  · rwa [isCircuit_iff_restr_eq_circuitOn hC.nonempty, hr,
      ← isCircuit_iff_restr_eq_circuitOn hC.nonempty]
  rwa [cocircuit_def, isCircuit_iff_restr_eq_circuitOn hC.nonempty, hcr,
    ← isCircuit_iff_restr_eq_circuitOn hC.nonempty]

lemma exists_uniformMinor_of_odd_crossing {M : Matroid α} {X : Finset α} (hX : M.Crossing X)
    (h_odd : Odd X.card) : ¬ M.NoUniformMinor 2 4  := by

  obtain ⟨C, K, hC, hK, hCK⟩ := hX

  have hcard : 3 ≤ (C ∩ K).encard
  · obtain ⟨rfl | k, hk⟩ := h_odd
    · exfalso
      simp only [mul_zero, zero_add, Finset.card_eq_one] at hk
      obtain ⟨e, he⟩ := hk
      rw [he, Finset.coe_singleton] at hCK
      exact hC.inter_cocircuit_ne_singleton hK hCK.symm
    rw [← hCK, encard_coe_eq_coe_finsetCard, Nat.ofNat_le_cast]
    linarith

  have hne : (C ∩ K).Nonempty
  · rw [← encard_ne_zero, ← ENat.one_le_iff_ne_zero]
    exact le_trans (by norm_num) hcard

  by_contra hcon
  obtain ⟨N₁, hN₁M, hCN₁, hKN₁⟩ := hC.exists_minor_inter_isCircuit_cocircuit_of_cocircuit hK hne

  obtain ⟨N₂, hN₂N₁, hCN₂, hKN₂, hSN₂, hSdN₂⟩ :=
    hCN₁.exists_minor_spanning_cospanning_of_cocircuit hKN₁

  rw [← hCK] at *

  have hN₂m := hcon.minor (hN₂N₁.trans hN₁M)

  obtain ⟨N₃, C₀, hN₃, hN₃C, hN₃K, hssu, h_odd'⟩ :=
    exists_smaller_of_odd_isCircuit_cocircuit (by simp) hCN₂ (by simpa) hSN₂ hKN₂.compl_isHyperplane
    (by simpa using hSdN₂.compl_coindep) hcard (hcon.minor (hN₂N₁.trans hN₁M))

  have hcr : N₃.Crossing C₀ := ⟨_, _, hN₃C, hN₃K, by rw [inter_eq_self_of_subset_right hssu.subset]⟩
  have hlt := Finset.card_strictMono hssu
  exact exists_uniformMinor_of_odd_crossing hcr h_odd' <| hN₂m.minor hN₃

termination_by X.card

theorem binary_iff_no_U24_minor (M : Matroid α) :
    M.Binary ↔ M.NoUniformMinor 2 4 := by
  rw [← not_iff_not]
  refine ⟨fun h ↦ ?_, fun h hbin ↦ ?_⟩
  · simp only [Binary, not_forall, Classical.not_imp, Nat.not_even_iff_odd, exists_and_left] at h
    obtain ⟨X, hX, hodd⟩ := h
    exact exists_uniformMinor_of_odd_crossing hX hodd

  simp only [not_noUniformMinor_iff] at h
  simpa [binary_unif_iff] using hbin.isoMinor h.some
