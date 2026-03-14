import Matroid.Extension.Parallel
import Matroid.ForMathlib.Topology.ENat
import Matroid.Uniform

open Set

namespace Matroid

variable {α : Type*} {M M' : Matroid α} {e f : α} {I : Set α} {a : ℕ}


/-- Every matroid is the disjoint sum of a loopless, coloopless matroid, a rank-zero matroid,
and a free matroid. -/
lemma exists_disjointSum_loopyOn_freeOn (M : Matroid α) : ∃ (M₀ : Matroid α) (L K : Set α)
    (hML : Disjoint M₀.E L) (hMK : Disjoint M₀.E K) (hLK : Disjoint L K),
    M₀.Loopless ∧ M₀.Coloopless ∧
    M = M₀.disjointSum ((loopyOn L).disjointSum (freeOn K) hLK) (by simp [hML, hMK]) := by
  refine ⟨M.removeLoops.removeColoops, M.loops, M.coloops, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [removeLoops_removeColoops_comm, removeLoops_eq_delete, removeColoops_loops_eq]
    exact disjoint_sdiff_left
  · rw [removeColoops_eq_delete, removeLoops_coloops_eq]
    exact disjoint_sdiff_left
  · exact M.loops_disjoint_coloops
  · rw [removeColoops_eq_delete]
    infer_instance
  · infer_instance
  nth_rw 1 [M.removeLoops_disjointSum]
  rw! [M.removeLoops.removeColoops_disjointSum, disjointSum_assoc]
  simp only [removeLoops_coloops_eq, disjointSum_removeColoops, removeColoops_removeColoops]
  rw! [disjointSum_assoc, disjointSum_comm (M := loopyOn _)]
  simp

/-- A one-element matroid is a loop or a coloop. -/
lemma encard_ground_eq_one_iff_eq (hM : M.E.encard = 1) :
    ∃ a, M = loopyOn {a} ∨ M = freeOn {a} := by
  obtain ⟨a, ha⟩ := encard_eq_one.1 hM
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | rfl := subset_singleton_iff_eq.1 <| hB.subset_ground.trans ha.subset
  · exact ⟨a, .inl <| by rwa [empty_isBase_iff, ha] at hB⟩
  refine ⟨a, .inr ?_⟩
  rwa [← ha, ← ground_indep_iff_isBase, ground_indep_iff_eq_freeOn, ha] at hB

/-- A nonempty, loopless, coloopless matroid on at most two elements is a two-element circuit. -/
lemma eq_circuitOn_of_encard_ground_le_two [M.Loopless] [M.Coloopless] [M.Nonempty]
    (hM : M.E.encard ≤ 2) : ∃ a b, a ≠ b ∧ M = circuitOn {a, b} := by
  wlog hr : 2 * M.eRank ≤ M.E.encard generalizing M with aux
  · have hrr := M.eRank_add_eRank_dual
    obtain ⟨a, b, hab, hM⟩ := aux (M := M✶) (by simpa) (by enat_to_nat!; lia)
    refine ⟨a, b, hab, ?_⟩
    rwa [← dual_inj, ← unifOn_pair_one hab, unifOn_one_dual]
  obtain heq | hlt := hM.eq_or_lt
  · obtain ⟨E, rfl⟩ := M.eq_unifOn_of_eRank_le_one (by enat_to_nat! <;> lia)
    obtain ⟨a, b, hab, rfl : E = {a, b}⟩ := encard_eq_two.1 heq
    exact ⟨a, b, hab, unifOn_pair_one hab⟩
  have hpos := M.eRank_pos
  enat_to_nat! <;> lia

/-- A loopless, coloopless three-element matroid is uniform.  -/
lemma eq_unifOn_of_encard_ground_eq_three [M.Loopless] [M.Coloopless] (hM : M.E.encard = 3) :
    ∃ a b c , a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ (M = unifOn {a, b, c} 1 ∨ M = circuitOn {a, b, c}) := by
  wlog hr : M.eRank ≤ 1 generalizing M with aux
  · have hrr := M.eRank_add_eRank_dual
    obtain ⟨a, b, c, hab, hac, hbc, hM⟩ := aux (M := M✶) (by simpa) (by enat_to_nat!; lia)
    refine ⟨a, b, c, hab, hac, hbc, ?_⟩
    rwa [← dual_inj, unifOn_one_dual, or_comm, ← dual_inj, ← unifOn_one_dual, dual_dual,
      unifOn_one_dual]
  obtain ⟨E, rfl⟩ := M.eq_unifOn_of_eRank_le_one hr
  obtain ⟨a, b, c, hab, hac, hbc, rfl : E = {a, b, c}⟩ := encard_eq_three.1 hM
  exact ⟨a, b, c, hab, hac, hbc, by simp⟩

/-- Every two-element matroid is either uniform, or the sum of a loop and a coloop. -/
lemma eq_of_encard_ground_eq_two (hM2 : M.E.encard = 2) : ∃ (e f : α) (_hef : e ≠ f),
    M = loopyOn {e, f} ∨ M = freeOn {e, f} ∨ M = circuitOn {e, f}
    ∨ M = (loopyOn {e}).disjointSum (freeOn {f}) (by simpa) := by
  have : M.Nonempty := ⟨nonempty_of_ofNat_le_encard hM2.symm.le⟩
  obtain ⟨M₀, L, K, hML, hMK, hLK, hM₀, hM₀', hM⟩ := M.exists_disjointSum_loopyOn_freeOn
  obtain rfl | hne := M₀.eq_emptyOn_or_nonempty
  · rw [hM, emptyOn_disjointSum, disjointSum_encard_ground, loopyOn_ground, freeOn_ground] at hM2
    obtain ⟨e, f, hef, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
      exists_of_encard_add_encard_eq_two hM2 hLK
    all_goals grind [loopyOn_empty, disjointSum_emptyOn, freeOn_empty, emptyOn_disjointSum]
  rw [hM, disjointSum_encard_ground, disjointSum_encard_ground, loopyOn_ground,
    freeOn_ground] at hM2
  obtain ⟨e, f, hef, rfl⟩ := eq_circuitOn_of_encard_ground_le_two (M := M₀)
    (by enat_to_nat! <;> lia)
  obtain ⟨rfl, rfl⟩ : L = ∅ ∧ K = ∅ := by simpa [encard_pair hef] using hM2
  grind [loopyOn_empty, freeOn_empty, disjointSum_emptyOn]

lemma isFinRankUniform_of_eRank_le_one [M.Nonempty] [M.Loopless] (hM : M.eRank ≤ 1) :
    M.IsFinRankUniform 1 := by
  rw [isFinRankUniform_iff_eq_unifOn, ENat.coe_one, one_le_encard_iff_nonempty,
    and_iff_left M.ground_nonempty, ext_iff_indep, unifOn_ground_eq, and_iff_right rfl]
  simp +contextual only [unifOn_indep_iff, Nat.cast_one, and_true]
  exact fun I hIE ↦ ⟨fun hI ↦ hI.encard_le_eRank.trans hM,
    fun hI ↦ subsingleton_indep (encard_le_one_iff_subsingleton.1 hI) hIE⟩

lemma eq_freeOn_of_eRank_le_one_of_simple [M.Nonempty] [M.Simple] (hM : M.eRank ≤ 1) :
    ∃ e, M = freeOn {e} := by
  have h1 := M.isFinRankUniform_of_eRank_le_one hM
  obtain ⟨e, he⟩ | hnt := M.ground_nonempty.exists_eq_singleton_or_nontrivial
  · obtain rfl := he ▸ h1.eq_unifOn
    exact ⟨e, by simp [unifOn_eq_of_le]⟩
  obtain ⟨x, hx⟩ := hnt.nonempty
  obtain ⟨y, hy, hxy⟩ := hnt.exists_ne x
  exact False.elim <| (encard_pair hxy.symm ▸ (M.pair_indep hx hy).encard_le_eRank.trans_lt
    (by enat_to_nat!; lia)).ne rfl

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
  obtain ⟨M₀, L, K, hML, hMK, hLK, hM₀, hM₀', hMs⟩ := M.exists_disjointSum_loopyOn_freeOn
  rw! [hMs, disjointSum_encard_ground, disjointSum_encard_ground, loopyOn_ground,
    freeOn_ground] at hM
  obtain rfl | hM₀ne := M₀.eq_emptyOn_or_nonempty
  · rw [emptyOn_ground, encard_empty, zero_add] at hM
    obtain ⟨a, b, c, hab, hac, hbc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
      exists_of_encard_add_encard_eq_three hM hLK
    all_goals grind
      [loopyOn_empty, freeOn_empty, emptyOn_disjointSum, disjointSum_emptyOn, disjointSum_comm]
  obtain h3 | hlt := (le_self_add.trans hM.le).eq_or_lt
  · obtain ⟨rfl, rfl⟩ : L = ∅ ∧ K = ∅ := by simpa [h3] using hM
    obtain rfl : M = M₀ := by simpa using hMs
    obtain ⟨a, b, c, hab, hac, hbc, rfl | rfl⟩ := eq_unifOn_of_encard_ground_eq_three h3 <;> grind
  obtain ⟨e, f, hef, rfl⟩ := eq_circuitOn_of_encard_ground_le_two (M := M₀)
    (by enat_to_nat! <;> lia)
  have hLK1 : L.encard + K.encard = 1 := by
    simpa [encard_pair hef, show (3 : ℕ∞) = 2 + 1 from rfl] using hM
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_of_encard_add_encard_eq_one hLK1
  · simp only [loopyOn_empty, emptyOn_disjointSum] at hMs
    use e, f, g
    grind
  simp only [freeOn_empty, disjointSum_emptyOn] at hMs
  use e, f, g
  grind

lemma isFinRankUniform_of_eRank_eq_two [M.Nonempty] [M.Simple] (hM : M.eRank = 2) :
    M.IsFinRankUniform 2 := by
  grw [isFinRankUniform_iff_eq_unifOn, Nat.cast_two, ← hM, and_iff_left M.eRank_le_encard_ground,
    ext_iff_indep, unifOn_ground_eq, and_iff_right rfl]
  simp +contextual only [unifOn_indep_iff, Nat.cast_ofNat, and_true]
  refine fun I hIE ↦ ⟨fun hI ↦ (hI.encard_le_eRank.trans hM.le), fun hI ↦ ?_⟩
  exact indep_of_encard_le_two hI hIE

lemma isFinRankUniform_or_freeOn_of_eRank_le_two [M.Nonempty] [M.Simple] (hM : M.eRank ≤ 2) :
    M.IsFinRankUniform 2 ∨ ∃ e, M = freeOn {e} := by
  obtain h2 | h2 := hM.eq_or_lt
  · exact .inl <| isFinRankUniform_of_eRank_eq_two h2
  exact .inr <| M.eq_freeOn_of_eRank_le_one_of_simple (Order.le_of_lt_add_one h2)

/-- The only nonempty, simple, cosimple matroid on at most four elements is `U₂,₄`. -/
lemma isFiniteUniform_two_four_of_encard_ground_le_four_simple_simple_dual (hME : M.E.encard ≤ 4)
    [M.Nonempty] [M.Simple] [M✶.Simple] : M.IsFiniteUniform 2 2 4 := by
  wlog hMr : 2 * M.eRank ≤ M.E.encard generalizing M with aux
  · have hrr := M.eRank_add_eRank_dual
    rw [← dual_ground] at hrr hMr
    exact (aux (M := M✶) (by simpa) (by enat_to_nat!; lia)).of_dual
  have hrr := M.eRank_add_eRank_dual
  have hM : M.Finite := ⟨finite_of_encard_le_ofNat hME⟩
  obtain h2 | ⟨e, rfl⟩ := M.isFinRankUniform_or_freeOn_of_eRank_le_two <| by enat_to_nat! <;> lia
  · have := h2.eRank_eq
    obtain ⟨b, n, hMbn, hb, hn⟩ := h2.exists_isFiniteUniform_of_finite
    obtain rfl : b = 2 := by enat_to_nat! <;> lia
    rwa [← hMbn.add_eq] at hMbn
  simp at hMr



  -- have := isFinRankUniform_of_eRank_le_two hMr



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

-- lemma extendedUnifOn_simple_iff {P : Set (Set α)} {L : Set α} (hP : P.PairwiseDisjoint id) :
--     (extendedUnifOn P L a hP).Simple ↔ 2 ≤ a ∧ L = ∅ ∧ ∀ S ∈ P, S.Subsingleton := by
--   _

@[simp]
lemma extendedUnifOn_eq_unifOn (P : Set α) : extendedUnifOn ((fun x ↦ {x}) '' P) ∅ a
      (by simp +contextual [PairwiseDisjoint, Set.Pairwise, Function.onFun, eq_comm])
      = unifOn P a :=
  ext_indep (by simp) <| by simp [(subsingleton_singleton.anti inter_subset_right), and_comm]

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

lemma extendedUnifOn_eq_disjointSum (P : Set (Set α)) (L : Set α) (hdj : P.PairwiseDisjoint id)
    (hL : ∀ S ∈ P, Disjoint S L) :
    extendedUnifOn P L a hdj = (extendedUnifOn P ∅ a hdj).disjointSum (loopyOn L) (by simpa) := by
  rw [extendedUnifOn_eq_restrict, disjointSum_loopyOn, extendedUnifOn_ground, union_empty]

lemma eq_disjointSum_of_rank_le_one (hM : M.eRank ≤ 1) :
    M = (unifOn {e | M.IsNonloop e} 1).disjointSum (loopyOn M.loops)
      M.loops_disjoint_setOf_isNonloop.symm := by
  nth_rw 1 [eq_extendedUnifOn_of_eRank_le_one hM, extendedUnifOn_eq_restrict,
    restrict_superset_ground_eq_disjointSum (by simp)]
  rw! [extendedUnifOn_singleton_empty, sUnion_singleton, unifOn_ground_eq, union_diff_left,
    M.loops_disjoint_setOf_isNonloop.sdiff_eq_left]
  rfl

lemma eq_or_eq_of_encard_ground_eq_four (hME : M.E.encard = 4)
    [M.Loopless] [M.Coloopless] : M.IsFiniteUniform 2 2 4 ∨
    ∃ (a a' b b' : α) (hnd : [a, a', b, b'].Nodup),
      M = extendedUnifOn {{a, a'}, {b}, {b'}} ∅ 2 (by
        simp only [pairwiseDisjoint_insert, Partition.isPartition_singleton_iff, bot_eq_empty,
          ne_eq, singleton_ne_empty, not_false_eq_true, Partition.IsPartition.pairwiseDisjoint,
          mem_singleton_iff, forall_eq, singleton_eq_singleton_iff,
          mem_insert_iff, forall_eq_or_imp, true_and]
        grind ) := by


/-- Every two-element matroid is either uniform, or the sum of a loop and a coloop. -/
lemma bar (hM : M.E.encard = 2) : ∃ (e f : α) (_hef : e ≠ f),
    M = loopyOn {e, f} ∨ M = freeOn {e, f} ∨ M = circuitOn {e, f}
    ∨ M = extendedUnifOn {{e}} {f} 1 (by simp) := by
  obtain ⟨e, f, hef, rfl | rfl | rfl | rfl⟩ := eq_of_encard_ground_eq_two hM
  · grind
  · grind
  · grind
  use f, e, hef.symm
  right; right; right
  rw! [extendedUnifOn_eq_disjointSum _ _ _ (by grind), extendedUnifOn_singleton_empty,
    unifOn_eq_of_le (by simp), disjointSum_comm]
  rfl
