import Matroid.Connectivity.Minor
import Matroid.Connectivity.Connected
import Matroid.Connectivity.Separation.Basic
import Matroid.ForMathlib.Matroid.Constructions
import Matroid.Triangle


/-
This file contains miscellaneous lemmas about triangles/triads and connectivity that are not
explicitly about fans.
-/

variable {α : Type*} {M : Matroid α} {e f g a b c d : α} {T T' C K X : Set α}

open Set Function

namespace Matroid


/- If `e, f` is a series pair contained in a triangle of a connected matroid, then we can
remove both and stay connected. -/
lemma Connected.contract_delete_connected_of_mem_triangle_of_series {T} (hM : M.Connected)
    (hT : M.IsTriangle T) (heT : e ∈ T) (hfT : f ∈ T) (hef : e ≠ f) (h_series : M✶.Parallel e f) :
    (M ／ {e} ＼ {f}).Connected := by
  have hMnt := hT.nontrivial.mono hT.subset_ground
  have hnt' := ((hT.nontrivial_diff_singleton e).mono
    (diff_subset_diff_left hT.subset_ground))
  obtain ⟨g, hge, hgf, rfl⟩ :=
    exists_eq_of_encard_eq_three_of_mem_of_mem hT.three_elements heT hfT hef
  obtain hd | hc := hM.delete_or_contract hMnt e
  · rw [← connected_dual_iff] at hd
    refine False.elim <| ((hd.loopless hnt').isNonloop_of_mem (e := f) ?_).not_isLoop ?_
    · simp only [dual_delete, contract_ground, dual_ground, mem_diff, mem_singleton_iff]
      grind
    exact dual_delete .. ▸ h_series.isLoop_contractElem hef
  refine (hc.delete_or_contract hnt' f).elim id fun hd ↦ ?_
  obtain hss | hnt := (M ／ {e} ／ {f}).E.subsingleton_or_nontrivial
  · convert singleton_connected (M := M ／ {e} ＼ {f}) (e := g) ?_
    exact hss.eq_singleton_of_mem <| by grind
  simpa [hT.swap_left.mem_closure₃] using (hd.loopless hnt).isNonloop_of_mem (e := g) (by grind)

/- If `e, f` is a parallel pair contained in a triad of a connected matroid, then we can
remove both and stay connected. -/
lemma Connected.contract_delete_connected_of_mem_triad_of_parallel {T} (hM : M.Connected)
    (hT : M.IsTriad T) (heT : e ∈ T) (hfT : f ∈ T) (hef : e ≠ f) (h_para : M.Parallel e f) :
    (M ／ {e} ＼ {f}).Connected := by
  have h := hM.to_dual.contract_delete_connected_of_mem_triangle_of_series hT heT hfT hef (by simpa)
  rwa [h_para.parallel'.contract_delete_comm, ← connected_dual_iff, dual_contract_delete,
    ← contract_delete_comm _ (by grind)]

-- def parallelUnifOn {ι : Type*} (L : ι → Set α) (hL : Pairwise (Disjoint on L) := by grind)
-- (k : ℕ) :
--     Matroid α := (Matroid.disjointSigma (fun i ↦ unifOn (L i) 1) (by simpa)).truncateTo k

-- lemma rankTwoOn_indep_iff {ι : Type*} (L : ι → Set α) (hL) {I : Set α} {k : ℕ} :
--     (parallelUnifOn L hL k).Indep I ↔
--         I ⊆ ⋃ i, L i ∧ (∀ i, (I ∩ L i).encard ≤ 1) ∧ I.encard ≤ k := by
--   simp only [parallelUnifOn, truncateTo_indep_iff, disjointSigma_indep_iff, unifOn_ground_eq,
--     unifOn_indep_iff, Nat.cast_one, inter_subset_right, and_true]
--   tauto

-- lemma IsTriangle.small_of_isTriangle_isTriad {a b c d : α} (habc : M.IsTriangle {a, b, c})
--     (habd : M.IsTriangle {a, b, d}) (hbcd : M.IsTriad {b, c, d}) (ha : (M ／ {a}).Connected) :
--     M = parallelUnifOn #[{a}, {b, c}, {d}] := by

/-- If a four-element set `{a, b, c, d}` contains two triangles through `a` and `b`,
and a triad not containing both `a` and `b`, and `M ／ {a}` is connected,
then the matroid is `U₂,₄`, or a parallel extension of `U₂,₃`. -/
lemma IsTriangle.small_of_isTriangle_isTriad {a b c d : α} (habc : M.IsTriangle {a, b, c})
    (habd : M.IsTriangle {a, b, d}) (hbcd : M.IsTriad {b, c, d}) (ha : (M ／ {a}).Connected) :
    M ＼ {d} = unifOn {a, b, c} 2 := by
  obtain rfl | hne := eq_or_ne c d
  · simp at hbcd
  have hss : {a, b, c, d} ⊆ M.closure {a, b} := by simp [insert_subset_iff, habc.mem_closure₃,
    habd.mem_closure₃, mem_closure_of_mem', habc.mem_ground₁, habc.mem_ground₂]
  have hacl : a ∈ M.closure {b, c, d} :=
    mem_of_mem_of_subset habc.mem_closure₁ <| M.closure_subset_closure <| by grind
  have hE : M.E = {a, b, c, d}
  · have hconn := hbcd.isCircuit.eConn_add_one_eq.le
    grw [dual_dual, ← eRk_closure_eq, ← closure_insert_eq_of_mem_closure hacl,
      hss, closure_closure, eRk_closure_eq, eRk_le_encard, encard_pair_le,
      M✶.eConn_eq_eConn_delete_disjoint_add (D := {a}) (by grind), dual_dual,
      ← eConn_dual, dual_delete_dual, eLocalConn_comm,
      habc.isNonloop₁.eLocalConn_eq_one_iff.2 hacl, ← one_add_one_eq_two,
      ENat.add_one_le_add_one_iff, ENat.add_le_right_iff, or_iff_left (by simp)] at hconn
    rw [ha.eq_ground_of_eConn_eq_zero hconn (by simp) (by grind [hbcd.subset_ground]),
      contract_ground, insert_diff_self_of_mem habc.mem_ground₁]
  rw [← circuitOn_eq_unifOn, ← habc.isCircuit.restrict_eq_circuitOn, delete_eq_restrict, hE,
    show ({a, b, c, d} : Set α) \ {d} = {a, b, c} by grind]
  simp [habc.three_elements, two_add_one_eq_three]


-- /-- A matroid consisting of a series class on `S` and a parallel class on `P`. -/
-- def seriesParallelDuo (S P : Set α) (hdj : Disjoint S P) :=
--   Matroid.ofExistsMatroidBase (S ∪ P)
--   (fun B ↦ (P = ∅ ∧ (circuitOn S).IsBase B) ∨ (S = ∅ ∧ (unifOn P 1).IsBase B) ∨
--       (∃ e ∈ P, ∃ f ∈ S, B = insert e (S \ {f})))
--   (by
--     obtain rfl | hPne := P.eq_empty_or_nonempty
--     · exact ⟨circuitOn S, by simp, fun I ↦ by simp +contextual⟩
--     obtain rfl | hSne := S.eq_empty_or_nonempty
--     · exact ⟨unifOn P 1, by simp, fun I ↦ by simp +contextual⟩
--     refine ⟨(Matroid.disjointSum (loopyOn S) (freeOn P) hdj).truncate✶.truncate, ?_⟩
--     simp only [truncate_ground_eq, dual_ground, disjointSum_ground_eq, loopyOn_ground,
--       freeOn_ground, hPne.ne_empty, false_and, hSne.ne_empty, false_or, true_and]
--     have h0 : RankPos ((loopyOn S).disjointSum (freeOn P) hdj) := by
--       simp [rankPos_iff, hPne.ne_empty.symm]
--     have h1 : RankPos ((loopyOn S).disjointSum (freeOn P) hdj).truncate✶ := by
--       simp only [rankPos_iff, truncate_ground_eq, disjointSum_ground_eq, loopyOn_ground,
--         freeOn_ground, empty_subset, dual_isBase_iff, truncate_isBase_iff,
--         disjointSum_isBase_iff, loopyOn_isBase_iff, freeOn_isBase_iff]
--       grind
--     simp only [truncate_isBase_iff, dual_isBase_iff', truncate_ground_eq, disjointSum_ground_eq,
--       loopyOn_ground, freeOn_ground, mem_diff, mem_union, mem_insert_iff, not_or, not_and, not_not,
--       disjointSum_isBase_iff, loopyOn_isBase_iff, freeOn_isBase_iff, inter_eq_right]
--     refine fun I ↦ ⟨fun ⟨e, h1, ⟨f, hf1, hf2, hf3, hf4⟩, h3⟩ ↦ ?_, ?_⟩
--     · rw [← union_singleton (a := e), ← diff_diff] at hf4 hf3 hf2
--       have hfP : f ∈ P := by
--         grind [show f ∉ S from fun hfS ↦ by simpa using hf2.subset ⟨.inl rfl, hfS⟩]
--       have hef : e ≠ f := by
--         rintro rfl

--         -- nth_rw 2 [← union_singleton] at hf3
--         rw [insert_diff_self_of_mem (by grind)] at hf3

--       have heS : e ∈ S := by
--         by_cases heP : e ∈ P
--         · have := hf3 heP
--           simp at this
--         grind [show e ∉ P from fun heP ↦ by
--           (grind [hf3 heP])
--         ]
--       refine ⟨f, hfP, e, ?_, ?_⟩
--       · grind [show f ∉ S from fun hfS ↦ by simpa using hf2.subset ⟨.inl rfl, hfS⟩]










    -- · obtain rfl | hSne := S.eq_empty_or_nonempty
    --   · refine ⟨emptyOn α, by simp⟩
    --   refine ⟨circuitOn S, ?_⟩
    --   simp only [union_empty, circuitOn_ground, circuitOn_isBase_iff hSne, hSne.ne_empty, false_and,
    --     and_false, true_and, mem_empty_iff_false, exists_false, and_self, or_self, or_false,
    --     false_or]
    --   exact fun I ↦ ⟨Exists.imp <| by grind, fun ⟨e, heS, hI⟩ ↦ ⟨e, by grind⟩⟩
    -- obtain rfl | hSne := S.eq_empty_or_nonempty
    -- · suffices aux (I) : (unifOn P 1).IsBase I ↔ ∃ f ∈ P, I = {f}
    --   refine ⟨unifOn P 1, by simp, fun I ↦ by simp [hPne.ne_empty] using aux⟩
    --   simp [hPne.ne_empty]
    --   rw [unifOn_isBase_iff]
    --   simp [empty_union, unifOn_ground_eq, true_and, mem_empty_iff_false, not_false_eq_true,
    --     diff_singleton_eq_self, false_and, exists_false, and_false, insert_empty_eq, or_false,
    --     false_or, hPne.ne_empty]






  )

    -- (Matroid.disjointSum (freeOn P) (loopyOn S) hdj.symm).truncate✶.truncate

lemma seriesParallelDuo_empty_left {P : Set α} :
    seriesParallelDuo ∅ P (by simp) = unifOn P 1 := by
  simp [seriesParallelDuo]

lemma seriesParallelDuo_empty_right {S : Set α} :
    seriesParallelDuo S ∅ (by simp) = freeOn S := by
  simp [seriesParallelDuo]

lemma seriesParallelDuo_isBase_iff {S P B : Set α} {hSP : Disjoint S P} :
    (seriesParallelDuo S P hSP).IsBase B ↔ (P = ∅ ∧ S = ∅ ∧ B = ∅) ∨
      (P = ∅ ∧ ∃ e ∈ S, B = S \ {e}) ∨ (S = ∅ ∧ ∃ f ∈ P, B = {f}) ∨
      (∃ e ∈ P, ∃ f ∈ S, B = insert e (S \ {f})) := by
  obtain rfl | hne := eq_or_ne P ∅
  · simp [seriesParallelDuo]



lemma seriesParallelDuo_indep_iff {S P I : Set α} {hSP : Disjoint S P} :
    (seriesParallelDuo S P hSP).Indep I ↔ (P.Nonempty ∧ I = S) ∨
      (S.Nonempty ∧ (I ∩ P).Subsingleton ∧ I ⊆ S ∪ P ∧ ¬ (S ⊆ I)) := by
  simp only [seriesParallelDuo]
  simp [truncate_indep_iff']
  simp [dual_isBase_iff', ]
  simp [seriesParallelDuo]
  simp [truncate_indep_iff']
  obtain rfl | hne := P.eq_empty_or_nonempty
  · simp only [inter_empty, encard_empty, zero_le, union_empty, true_and, unifOn_empty,
      emptyOn_isBase_iff, forall_const, subsingleton_empty]
    simp only [Set.not_nonempty_empty, false_and, false_or, and_congr_right_iff]


    refine fun hIS ↦ ?_
    ·
    rw [or_comm, ← subset_iff_ssubset_or_eq]
    simp
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← ssubset_iff_subset_not_subset]
      obtain rfl | hssu := h.1.eq_or_ssubset
      · simp

    grind
  -- · simp only [unifOn_empty, truncate_emptyOn_eq, inter_empty, emptyOn_indep_iff, union_empty,
  --     true_and, subsingleton_empty]
  --   grind
  -- have hp : (unifOn P 1).RankPos := by
  --   rw [rankPos_iff, unifOn_isBase_iff (one_le_encard_iff_nonempty.2 hne) (by simp)]
  --   simp
  -- rw [truncate_indep_iff, unifOn_isBase_iff (one_le_encard_iff_nonempty.2 hne) (by simp),
  --   unifOn_indep_iff, and_iff_left inter_subset_right, ← lt_iff_le_and_ne, Nat.cast_one,
  --   ENat.lt_one_iff_eq_zero, encard_eq_zero, ← disjoint_iff_inter_eq_empty]
  -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  -- · simp only [h.1.inter_eq, subsingleton_empty, h.2, true_and]
  --   nth_rw 1 [subset_antisymm_iff, ← h.1.sdiff_eq_left, diff_subset_iff, union_comm,
  --     and_iff_right h.2]
  --   apply em
  -- obtain rfl | ⟨hss, hdj, hSI⟩ := h
  -- · simp [hSP]




  -- rw [truncate_indep_iff]
-- lemma bar (he : M.IsNonloop e) (hconn : (M ／ {e}).Connected) (he' : M.Dep (M.E \ {e}))

-- lemma IsTriangle.foo {a b c d : α} (hanl : M.IsNonloop a) (habc : M.Dep {a, b, c})
--     (habd : M.Dep {a, b, d}) (hbcd : M✶.Dep {b, c, d}) (ha : (M ／ {a}).Connected)
--     (hnt : (M.E \ {a}).Nontrivial) : M.E = {a, b, c, d} ∧ M.IsTriad {a, c, d} := by
--   have hMl : M.Loopless := by
--     rw [loopless_iff_forall_isNonloop]
--     intro e heE
--     obtain rfl | hne := eq_or_ne e a
--     · assumption
--     exact ((ha.loopless hnt).isNonloop_of_mem (by grind)).of_contract
--   obtain ⟨x, hx⟩ | hnp := exists_or_forall_not (fun x ↦ a ≠ x ∧ M.Parallel x a)
--   · have hnl := (ha.loopless hnt).isNonloop_of_mem (e := x) (by grind [hx.2.mem_ground_left])
--     exact False.elim <| (hx.2.symm.isLoop_contractElem hx.1).not_isNonloop hnl
--   simp_rw [not_and] at hnp
--   have h' (x) (hxE : x ∈ M.E) : M.Indep {a, x} := by
--     obtain rfl | hne := eq_or_ne a x
--     · simp [hanl.indep]
--     rw [← hanl.not_parallel_iff (hMl.isNonloop_of_mem hxE) hne, parallel_comm]
--     exact hnp _ hne
--   obtain ⟨K, hKbcd, hK⟩ := hbcd.exists_isCircuit_subset
--   have hd {x y} (hxy : M.Dep {a, x, y}) :
--       a ≠ x ∧ x ≠ y ∧ ∃ C, M.IsCircuit C ∧ ({x, y} : Set α) ⊆ C ∧ C ⊆ {a, x, y} := by
--     obtain rfl | hxa := eq_or_ne x a
--     · exact False.elim <| (h' y (by grind)).not_dep <| by simpa using hxy
--     obtain rfl | hne := eq_or_ne x y
--     · exact False.elim <| (h' x (by grind)).not_dep (by simpa using hxy)
--     obtain ⟨C, hC⟩ := hxy.exists_isCircuit_subset


    -- obtain hxC | hxC := em' <| x ∈ C
    -- · exact False.elim <| hC.2.dep.not_indep <| (h' y (by grind)).subset <| by grind
    -- obtain hyC | hyC := em' <| y ∈ C
    -- · exact False.elim <| hC.2.dep.not_indep <| (h' x (by grind)).subset <| by grind
    -- by_cases haC : a ∈ C
    -- · grind [show C = {a, x, y} by grind]
    -- grind [show C = {x, y} by grind]

        -- obtain rfl : C = {a, b, c} := hC.1.antisymm (by grind [insert_subset_iff])





  -- obtain rfl | had := eq_or_ne a d
  -- ·
  -- by_cases hbc : ¬ M.Parallel b c
  -- · obtain ⟨C, hCss, hC⟩ := habc.exists_isCircuit_subset
  --   by_cases hC3 : C.encard = 3
  --   · rw [← Finite.eq_of_subset_of_encard_le' (by simp) hCss (by grind)]
  --     rw [← circuitOn_eq_unifOn (by grind), ← hC.restrict_eq_circuitOn, delete_eq_restrict, ]


  --   obtain rfl | hssu := hCss.eq_or_ssubset
  --   · rw [← circuitOn_eq_unifOn]
  --   -- by_cases haC : a ∈ C
  --   -- ·

  -- obtain rfl | hne := eq_or_ne a b
  -- · rw [insert_eq_of_mem (by simp), ← hanl.parallel_iff_dep] at habc
  -- obtain hacl | hncl := M✶.isLoop_or_isNonloop a
  -- · rw [← diff_dep_iff_dep_of_subset_coloops (X := {a}) (by simpa)] at habc habd
  --   sorry
  -- obtain ⟨K, hK, hKbcd⟩ := hbcd.exists_isCircuit_subset

  -- by_cases hK1 : K.encard = 1
  -- · obtain ⟨x, rfl⟩ := encard_eq_one.1 hK1
  --   refine False.elim <| (ha.to_dual.loopless hnt).not_isLoop (e := x) ?_
  --   simp only [dual_contract, delete_isLoop_iff, dual_isLoop_iff_isColoop, mem_singleton_iff]
  --   simp only [singleton_isCircuit, dual_isLoop_iff_isColoop] at hKbcd
  --   exact ⟨hKbcd, fun hxa ↦ (hxa ▸ hncl).not_isLoop hKbcd⟩
  -- by_cases hK2 : K.encard = 2
  -- · rw [encard_eq_two] at hK2
  --   obtain ⟨x, y, hxy, rfl⟩ := hK2


    -- have : K = {b, c} ∨ K = {b, d} ∨ K = {c, d} := by grind


  -- obtain rfl | hne := eq_or_ne a c
  -- · obtain hal | hanl := M.isLoop_or_isNonloop a
  --   · rw [← diff_dep_iff_dep_of_subset_coloops (X := {a})] at hbcd


lemma IsTriangle.triad_of_isTriangle_isTriad {a b c d : α} (habc : M.IsTriangle {a, b, c})
    (habd : M.IsTriangle {a, b, d}) (hbcd : M.IsTriad {b, c, d}) (ha : (M ／ {a}).Connected) :
    M.IsTriad {a, c, d} := by
  have h_eq := habc.small_of_isTriangle_isTriad habd hbcd ha
  rw [← dual_inj, dual_delete, unifOn_dual_eq' (j := 1) (by grind [habc.three_elements])] at h_eq
  have hC : (M✶ ／ {d}).IsCircuit {a, c} := by grind [unifOn_isCircuit_iff, encard_pair habc.ne₁₃]
  obtain ⟨T, hT, hacT, hTss⟩ := hC.exists_subset_isCircuit_of_contract
  simp only [union_singleton] at hTss
  by_cases hd : d ∈ T
  · rwa [isTriad_iff, encard_insert_of_notMem (by grind), encard_pair hbcd.ne₂₃,
      ← show T = {a, c, d} by grind, and_iff_left (by grind)]
  rw [show T = {a, c} by grind] at hT
  have hwin := habd.reverse.mem_iff_mem_of_isCocircuit hT
  grind
  -- have := IsCircuit.exists_subset_isCircuit_of_contract
