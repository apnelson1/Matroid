import Matroid.Extension.Parallel
import Matroid.ForMathlib.Topology.ENat
import Matroid.Uniform

open Set

namespace Matroid

variable {α : Type*} {M M' : Matroid α} {e f : α} {I : Set α} {a : ℕ}

-- lemma eq_of_encard_eq_one (hM : M.E.encard = 1) : ∃ e, M = loopyOn {e} ∨ M = freeOn {e} := by
--   _

/-- A rank-`a` uniform matroid with the elements replaced by parallel classes from a set `P`,
and with a set `L` of loops added. -/
def extendedUnifOn (P : Set (Set α)) (L : Set α) (a : ℕ) (hP : P.PairwiseDisjoint id) : Matroid α :=
    (unifOn P a).multiExtend id L (hP.mono' fun _ _ ↦ id)

@[simp]
lemma extendedUnifOn_ground (P : Set (Set α)) (L : Set α) (hP : P.PairwiseDisjoint id) :
    (extendedUnifOn P L a hP).E = ⋃₀ P ∪ L := by
  simp_rw [extendedUnifOn, multiExtend_ground, unifOn_ground_eq, id_eq, sUnion_eq_biUnion]

@[simp]
lemma extendedUnifOn_indep_iff (P : Set (Set α)) (L : Set α) (hP : P.PairwiseDisjoint id)
    (I : Set α) : (extendedUnifOn P L a hP).Indep I ↔
      I ⊆ ⋃₀ P ∧ I.encard ≤ a ∧ ∀ S ∈ P, (I ∩ S).Subsingleton := by
  rw [extendedUnifOn, multiExtend_indep_iff]
  simp only [unifOn_ground_eq, id_eq, unifOn_indep_iff, sep_subset, and_comm, true_and,
    sUnion_eq_biUnion, ← inter_comm I]
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h2, ?_, by simpa⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨?_, h1, h3⟩⟩
  · grw [← inter_eq_self_of_subset_left h2, inter_iUnion₂, ENat.encard_biUnion_le_tsum_encard,
      ENat.tsum_subtype_eq_tsum_support (s := P) (f := fun x ↦ (I ∩ x).encard),
      ENat.tsum_le_tsum (g := fun _ ↦ 1), ENat.tsum_one]
    · simpa [← nonempty_iff_ne_empty]
    rintro ⟨S, hS, hSp⟩
    simpa [encard_le_one_iff_subsingleton, inter_comm I] using h3 _ hS
  choose φ hφ using fun f : {f | f ∈ P ∧ (I ∩ f).Nonempty} ↦ f.2.2
  have hinj : φ.Injective := by
    refine fun i j hij ↦ by_contra fun hne ↦ ?_
    exact (hP i.2.1 j.2.1 (Subtype.coe_ne_coe.2 hne)).notMem_of_mem_left (hφ i).2 (hij ▸ hφ j).2
  have hi := hinj.encard_image univ
  simp only [image_univ, encard_univ, ENat.card_coe_set_eq] at hi
  grw [← h2, ← hi]
  refine encard_le_encard ?_
  rintro _ ⟨e, he, rfl⟩
  exact (hφ e).1

lemma extendedUnifOn_eRank_eq (P : Set (Set α)) (L : Set α) (hP : P.PairwiseDisjoint id)
    (hPne : ∀ S ∈ P, S.Nonempty) (haP : a ≤ P.encard) : (extendedUnifOn P L a hP).eRank = a := by
  rw [extendedUnifOn, multiExtend_eRank_eq _ _ _ (by simpa), unifOn_eRank_eq' haP]

/-- Every matroid of rank at most two is obtained from a uniform matroid by parallel extensions
and adding loops. -/
lemma eq_extendedUnifOn_of_eRank_le_two (hM : M.eRank ≤ 2) : ∃ (P : Set (Set α)) (L : Set α)
    (hP : P.PairwiseDisjoint id), (∀ S ∈ P, S.Nonempty) ∧ (∀ S ∈ P, Disjoint S L) ∧
    M = extendedUnifOn P L 2 hP := by
  obtain ⟨N, hN⟩ := M.exists_isSimplification
  refine ⟨(fun e ↦ {f | M.Parallel e f}) '' N.E, M.loops, ?_, ?_, ?_, ?_⟩
  · exact hN.image_setOf_parallel_pairwiseDisjoint
  · rintro _ ⟨e, he, rfl⟩
    exact ⟨e, by simp [hN.isNonloop_of_mem he]⟩
  · rintro _ ⟨e, he, rfl⟩
    simp only [disjoint_left, mem_setOf_eq, ← isLoop_iff]
    exact fun _ h ↦ h.isNonloop_right.not_isLoop
  nth_rw 1 [← hN.multiExtend_eq, extendedUnifOn]
  have hNs := hN.simple
  obtain ⟨E, rfl⟩ := N.eq_unifOn_of_eRank_le_two <| hN.eRank_eq.trans_le hM
  convert Eq.symm <| multiExtend_map (unifOn E 2) (fun e ↦ {f | M.Parallel e f})
    hN.setOf_parallel_injOn id M.loops hN.image_setOf_parallel_pairwiseDisjoint
  simp

lemma extendedUnifOn_delete_loops {L₀ : Set α} (hL₀ : L₀ ⊆ M.loops) (P : Set (Set α)) (L : Set α)
    (hP : P.PairwiseDisjoint id) (hdel : M ＼ L₀ = extendedUnifOn P L a hP) :
    M = extendedUnifOn P (L ∪ L₀) a hP := by
  refine ext_indep ?_ fun I hI ↦ ?_
  · rw [← union_diff_cancel (hL₀.trans M.loops_subset_ground), ← delete_ground, hdel]
    simp [union_comm L₀, union_assoc]
  rw [← delete_restrict_ground_of_subset_loops hL₀, hdel]
  simp [hI]

@[simp]
lemma extendedUnifOn_empty (L : Set α) : extendedUnifOn ∅ L a (by simp) = loopyOn L :=
  ext_indep (by simp) <| by simp +contextual

@[simp]
lemma extendedUnifOn_singleton_empty (P : Set α) :
    extendedUnifOn {P} ∅ (a + 1) (by simp) = unifOn P 1 := by
  refine ext_indep (by simp) fun I hIP ↦ ?_
  simp only [extendedUnifOn_ground, sUnion_singleton, union_empty] at hIP
  simp only [extendedUnifOn_indep_iff, sUnion_singleton, hIP, Nat.cast_add, Nat.cast_one,
    mem_singleton_iff, ← encard_le_one_iff_subsingleton, forall_eq,
    inter_eq_self_of_subset_left hIP, true_and, unifOn_indep_iff, and_true, and_iff_right_iff_imp]
  exact fun h ↦ h.trans le_add_self

@[simp]
lemma extendedUnifOn_eq_unifOn (P : Set α) : extendedUnifOn ((fun x ↦ {x}) '' P) ∅ a
      (by simp +contextual [PairwiseDisjoint, Set.Pairwise, Function.onFun, eq_comm])
      = unifOn P a :=
  ext_indep (by simp) <| by simp [(subsingleton_singleton.anti inter_subset_right), and_comm]

/-- A one-element matroid is a loop or a coloop. -/
lemma encard_ground_eq_one_iff_eq (hM : M.E.encard = 1) :
    ∃ a, M = loopyOn {a} ∨ M = freeOn {a} := by
  obtain ⟨a, ha⟩ := encard_eq_one.1 hM
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | rfl := subset_singleton_iff_eq.1 <| hB.subset_ground.trans ha.subset
  · exact ⟨a, .inl <| by rwa [empty_isBase_iff, ha] at hB⟩
  refine ⟨a, .inr ?_⟩
  rwa [← ha, ← ground_indep_iff_isBase, ground_indep_iff_eq_freeOn, ha] at hB

lemma eq_extendedUnifOn_of_eRank_le_one (hM : M.eRank ≤ 1) :
    M = extendedUnifOn {{e | M.IsNonloop e}} M.loops 1 (by simp) := by
  obtain ⟨E, hE⟩ := M.removeLoops.eq_unifOn_of_eRank_le_one (by simpa)
  obtain rfl : E = {e | M.IsNonloop e} := by
    rw [← unifOn_ground_eq (E := E) (k := 1), ← hE, removeLoops_ground_eq]
  rw [← extendedUnifOn_singleton_empty (a := 0), zero_add, removeLoops_eq_delete] at hE
  exact empty_union M.loops ▸ extendedUnifOn_delete_loops rfl.subset _ _ _ hE

lemma extendedUnifOn_eq_restrict (P : Set (Set α)) (L : Set α) (hdj : P.PairwiseDisjoint id) :
    extendedUnifOn P L a hdj = extendedUnifOn P ∅ a hdj ↾ (⋃₀ P ∪ L) :=
  ext_indep (by simp) <| by simp +contextual

lemma eq_disjointSum_of_rank_le_one (hM : M.eRank ≤ 1) :
    M = (unifOn {e | M.IsNonloop e} 1).disjointSum (loopyOn M.loops)
      M.loops_disjoint_setOf_isNonloop.symm := by
  nth_rw 1 [eq_extendedUnifOn_of_eRank_le_one hM, extendedUnifOn_eq_restrict,
    restrict_superset_ground_eq_disjointSum (by simp)]
  rw! [extendedUnifOn_singleton_empty, sUnion_singleton, unifOn_ground_eq, union_diff_left,
    M.loops_disjoint_setOf_isNonloop.sdiff_eq_left]
  rfl

/-- Every two-element matroid is either uniform, or the sum of a loop and a coloop. -/
lemma bar (hM : M.E.encard = 2) : ∃ (e f : α) (_hef : e ≠ f),
    M = loopyOn {e, f} ∨ M = freeOn {e, f} ∨ M = unifOn {e, f} 1
    ∨ M = extendedUnifOn {{e}} {f} 1 (by simp) := by
  obtain ⟨x, y, hxy, hExy⟩ := encard_eq_two.1 hM
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | hne := B.eq_empty_or_nonempty
  · rw [empty_isBase_iff, hExy] at hB
    grind
  obtain rfl | hssu := hB.subset_ground.eq_or_ssubset
  · rw [← ground_indep_iff_isBase, ground_indep_iff_eq_freeOn, hExy] at hB
    grind
  have hcard : B.encard = 1 := by
    have h1 := hne.encard_pos
    have h2 := encard_add_one_le_of_ssubset hssu
    enat_to_nat!; lia
  obtain ⟨a, ha⟩ := encard_eq_one.1 hcard
  have ha : M.IsNonloop a := hB.indep.isNonloop_of_mem (ha.symm.subset rfl)
  obtain ⟨b, hba, hMab⟩ := exists_eq_of_encard_eq_two_of_mem hM (x := a) (by grind)
  obtain hbl | hbnl := M.isLoop_or_isNonloop b (by grind)
  · refine ⟨a, b, hba.symm, .inr <| .inr <| .inr ?_⟩
    rw [← empty_union {b}, ← extendedUnifOn_delete_loops (by simpa) {{a}} (L := ∅) (by simp)]
    simp only [extendedUnifOn_singleton_empty]
    refine ext_indep (by grind) ?_
    simp [show M.E \ {b} = {a} by grind, -subset_singleton_iff, subset_singleton_iff_eq, hba, ha]
  refine ⟨a, b, hba.symm, .inr <| .inr <| .inl ?_⟩
  refine ext_indep (by simpa) ?_
  simp +contextual only [hMab, unifOn_indep_iff, Nat.cast_one, and_true]
  intro I
  have hni : ¬ M.Indep {a, b} := (hB.dep_of_ssubset (by grind)).not_indep
  simp +contextual [subset_pair_iff_eq, or_imp, ha, hbnl, encard_pair hba.symm, hni]

lemma exists_disjointSum_loopyOn_freeOn (M : Matroid α) : ∃ (M₀ : Matroid α) (L K : Set α)
    (hML : Disjoint M₀.E L) (hMK : Disjoint M₀.E K) (hLK : Disjoint L K),
    M₀.Loopless ∧ M₀✶.Loopless ∧
    M = M₀.disjointSum ((loopyOn L).disjointSum (freeOn K) hLK) (by simp [hML, hMK]) := by
  refine ⟨M.removeLoops.removeColoops, M.loops, M.coloops, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [removeLoops_removeColoops_comm, removeLoops_eq_delete, removeColoops_loops_eq]
    exact disjoint_sdiff_left
  · rw [removeColoops_eq_delete, removeLoops_coloops_eq]
    exact disjoint_sdiff_left
  · exact M.loops_disjoint_coloops
  · rw [removeColoops_eq_delete]
    infer_instance
  · rw [removeColoops_dual, removeLoops_dual]
    infer_instance
  nth_rw 1 [M.removeLoops_disjointSum]
  rw! [M.removeLoops.removeColoops_disjointSum, disjointSum_assoc]
  simp




/-- There are nine isomorphism classes of three-element matroids. -/
lemma encard_eq_three_iff_eq (hM : M.E.encard = 3) : ∃ (a b c : α) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c),
    M = loopyOn {a, b, c}
    ∨ (M = unifOn {a, b, c} 1)
    ∨ (M = circuitOn {a, b, c})
    ∨ (M = freeOn {a, b, c})
    ∨ (M = (freeOn {a}).disjointSum (loopyOn {b, c}) (by grind [loopyOn_ground, freeOn_ground]))
    ∨ (M = (circuitOn {a, b}).disjointSum (loopyOn {c})
        (by grind [loopyOn_ground, circuitOn_ground]))
    ∨ (M = (freeOn {a, b}).disjointSum (loopyOn {c}) (by grind [freeOn_ground, loopyOn_ground]))
    ∨ (M = (circuitOn {a, b}).disjointSum (loopyOn {c})
        (by grind [loopyOn_ground, circuitOn_ground]))
    ∨ (M = (circuitOn {a, b}).disjointSum (freeOn {c})
        (by grind [freeOn_ground, circuitOn_ground])) := by
  wlog hr : M.eRank ≤ 1 generalizing M with aux
  · have hd : M✶.eRank ≤ 1 := by
      rw [← eRank_add_eRank_dual] at hM
      enat_to_nat! <;> lia
    obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := aux (M := M✶) (by simpa) hd
    simp only [eq_comm (a := M✶), eq_dual_iff_dual_eq, loopyOn_dual_eq, eq_comm (b := M),
      unifOn_one_dual, circuitOn_dual, freeOn_dual_eq, disjointSum_dual] at h_eq
    obtain h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 := h_eq
    all_goals grind [disjointSum_comm, unifOn_pair_one]
  have hM_eq := eq_disjointSum_of_rank_le_one hr
  have hl3 := (encard_le_encard M.loops_subset_ground).trans hM.le
  obtain h0 | h1 | h2 | h3 : M.loops.encard = 0 ∨ M.loops.encard = 1 ∨ M.loops.encard = 2 ∨
    M.loops.encard = 3 := by enat_to_nat! <;> lia
  · rw [encard_eq_zero] at h0
    obtain ⟨a, b, c, hab, hac, hbc, h_eq⟩ := encard_eq_three.1 hM
    have hnl : {e | M.IsNonloop e} = {a, b, c} := by rw [setOf_isNonloop_eq, h_eq, h0, diff_empty]
    rw! [h0, hnl, loopyOn_empty, disjointSum_comm, disjointSum_emptyOn] at hM_eq
    grind
  · obtain ⟨c, hc⟩ := encard_eq_one.1 h1
    obtain ⟨a, b, hac, hbc, hab, hE⟩ := exists_eq_of_encard_eq_three_of_mem (x := c) (s := M.E)
      (by grind) (by grind [M.loops_subset_ground])
    rw! [setOf_isNonloop_eq, hE, hc, insert_diff_self_of_notMem (by grind),
      unifOn_pair_one hab] at hM_eq
    grind
  · obtain ⟨b, c, hbc, hbcE⟩ := encard_eq_two.1 h2
    obtain ⟨a, ab, hac, hE⟩ := exists_eq_of_encard_eq_three_of_mem_of_mem (x := b) (y := c)
      (s := M.E) (by grind) (by grind [M.loops_subset_ground]) (by grind [M.loops_subset_ground])
      hbc
    rw! [setOf_isNonloop_eq] at hM_eq
    -- have hab : ∃ a b, a ≠ b ∧ a ≠ c ∧ b ≠ c








      -- have := unifOn_eq_of_le (E := {b, c}) (k := 2) (show ({b, c} : Set α).encard ≤ 2 from sorry)


    -- simp only [eq_comm (a := M✶), eq_dual_iff_dual_eq, loopyOn_dual_eq, unifOn_one_dual,
    --   circuitOn_dual, freeOn_dual_eq] at h_eq

  sorry
