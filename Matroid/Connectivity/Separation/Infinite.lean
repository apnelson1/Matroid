import Matroid.Connectivity.Separation.Vertical
import Matroid.Tame

variable {α : Type*} {M : Matroid α} {X Y : Set α} {e f : α} {P : M.Separation} {k : ℕ∞}

open Set Matroid.Separation

namespace Matroid



@[simp]
lemma freeOn_tutteConnected_top_iff {E : Set α} : (freeOn E).TutteConnected ⊤ ↔ E.Subsingleton := by
  rw [← top_add (a := 1), freeOn_tutteConnected_iff]
  simp

@[simp]
lemma loopyOn_tutteConnected_top_iff {E : Set α} :
    (loopyOn E).TutteConnected ⊤ ↔ E.Subsingleton := by
  rw [← top_add (a := 1), loopyOn_tutteConnected_iff]
  simp

lemma cyclicallyConnected_top_iff :
    M.CyclicallyConnected ⊤ ↔ ∀ X ⊆ M.E, M.Indep X ∨ M.Indep (M.E \ X) := by
  rw [CyclicallyConnected, numConnected_top_iff']

lemma CyclicallyConnected.inter_nonempty_of_dep_dep (h : M.CyclicallyConnected ⊤)
    (hX : M.Dep X) (hY : M.Dep Y) : (X ∩ Y).Nonempty := by
  by_contra! hcon
  have hX' := cyclicallyConnected_top_iff.1 h X hX.subset_ground
  rw [or_iff_right hX.not_indep] at hX'
  exact (hX'.subset (subset_diff.2 ⟨hY.subset_ground,
    by rwa [disjoint_comm, disjoint_iff_inter_eq_empty]⟩)).not_dep hY

lemma cyclicallyConnected_top_iff_forall_inter_nonempty :
    M.CyclicallyConnected ⊤ ↔ ∀ ⦃C₁ C₂⦄, M.IsCircuit C₁ → M.IsCircuit C₂ → (C₁ ∩ C₂).Nonempty := by
  refine ⟨fun h C₁ C₂ hC₁ hC₂ ↦ h.inter_nonempty_of_dep_dep hC₁.dep hC₂.dep,
    fun h ↦ cyclicallyConnected_top_iff.2 fun X hX ↦ ?_⟩
  rw [← not_dep_iff, ← not_dep_iff, ← Classical.not_and_iff_not_or_not]
  rintro ⟨hX, hX'⟩
  obtain ⟨C₁, hC₁X, hC₁⟩ := hX.exists_isCircuit_subset
  obtain ⟨C₂, hC₂X, hC₂⟩ := hX'.exists_isCircuit_subset
  refine (h hC₁ hC₂).ne_empty ?_
  grw [← subset_empty_iff, hC₁X, hC₂X]
  simp

lemma verticallyConnected_top_iff_forall_inter_nonempty : M.VerticallyConnected ⊤ ↔
    ∀ ⦃C₁ C₂⦄, M.IsCocircuit C₁ → M.IsCocircuit C₂ → (C₁ ∩ C₂).Nonempty := by
  rw [← cyclicallyConnected_dual_iff, cyclicallyConnected_top_iff_forall_inter_nonempty]

lemma VerticallyConnected.inter_nonempty_of_codep_codep (h : M.VerticallyConnected ⊤)
    (hX : M.Codep X) (hY : M.Codep Y) : (X ∩ Y).Nonempty :=
  h.dual_cyclicallyConnected.inter_nonempty_of_dep_dep hX hY

lemma TutteConnected.inter_nonempty_of_dep_codep (h : M.TutteConnected ⊤) (hX : M.Dep X)
    (hY : M.Codep Y) : (X ∩ Y).Nonempty := by
  rw [← not_disjoint_iff_nonempty_inter]
  intro hdj
  rw [TutteConnected, numConnected_top_iff'] at h
  obtain ⟨hi, hd⟩ | ⟨hi, hd⟩ := h hX.subset_ground
  · exact hX.not_indep hi
  refine hY.not_coindep (hd.subset ?_)
  rwa [subset_diff, disjoint_comm, and_iff_right hY.subset_ground]

lemma TutteConnected.isUniform (h : M.TutteConnected ⊤) : M.IsUniform :=
  TutteConnected.isUniform_of_encard_le (k := ⊤) (by simpa) (by simp)

lemma tutteConnected_top_iff_verticallyConnected_cyclicallyConnected_isUniform :
    M.TutteConnected ⊤ ↔ M.VerticallyConnected ⊤ ∧ M.CyclicallyConnected ⊤ ∧ M.IsUniform := by
  refine ⟨fun h ↦ ⟨h.verticallyConnected, h.cyclicallyConnected, h.isUniform⟩, fun ⟨h, h', hu⟩ ↦ ?_⟩
  rw [TutteConnected, numConnected_top_iff']
  intro X hXE
  wlog hXi : M.Indep X generalizing M X with aux
  · rw [not_indep_iff] at hXi
    obtain ⟨h,h'⟩ | ⟨h, h'⟩ := aux
      ⟨h'.dual_verticallyConnected, h.dual_cyclicallyConnected, hu.dual⟩
      h'.dual_verticallyConnected h.dual_cyclicallyConnected hu.dual
      (show M.E \ X ⊆ M.E from diff_subset) (hu.spanning_of_dep hXi).compl_coindep
    · rw [dual_coindep_iff] at h'
      exact .inr ⟨h', h⟩
    rw [dual_coindep_iff, dual_ground, diff_diff_cancel_left hXE] at h'
    rw [dual_ground, diff_diff_cancel_left hXE] at h
    exact .inl ⟨h', h⟩
  obtain (hXci | hXcd) := M.coindep_or_codep X
  · simp [hXi, hXci, tutteDegen_iff]
  have hXi' := hu.dual.spanning_of_dep hXcd
  rw [spanning_dual_iff] at hXi'
  obtain (hXci' | hXcd') := M.coindep_or_codep (X := M.E \ X)
  · simp [hXci', hXi', tutteDegen_iff]
  simpa using h.inter_nonempty_of_codep_codep hXcd hXcd'

lemma VerticallyConnected.two_mul_eRank_le (h : M.VerticallyConnected ⊤) :
    2 * M.eRank ≤ M.E.encard + 1 := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | ⟨e, he⟩ := B.eq_empty_or_nonempty
  · simp [← hB.encard_eq_eRank]
  obtain hs | hs := verticallyConnected_top_iff.1 h (B \ {e}) (diff_subset.trans hB.subset_ground)
  · rw [hB.eq_of_superset_spanning hs diff_subset] at he
    simp at he
  obtain ⟨B', hB', hB'ss⟩ := hs.exists_isBase_subset
  nth_grw 1 [two_mul, ← hB.encard_eq_eRank, ← hB'.encard_eq_eRank,
    ← encard_diff_singleton_add_one he, add_right_comm, ← encard_union_eq,
    encard_le_encard (union_subset (diff_subset.trans hB.subset_ground) hB'.subset_ground)]
  exact disjoint_sdiff_right.mono_right hB'ss

lemma CyclicallyConnected.two_mul_dual_eRank_le (h : M.CyclicallyConnected ⊤) :
    2 * M✶.eRank ≤ M.E.encard + 1 := by
  simpa using h.dual_verticallyConnected.two_mul_eRank_le

lemma CyclicallyConnected.encard_le (h : M.CyclicallyConnected ⊤) :
    M.E.encard ≤ 2 * M.eRank + 1 := by
  by_contra! hlt
  obtain ⟨D, hDE, hD⟩ :=
    exists_subset_encard_eq (k := M.eRank + 1) (s := M.E) (by enat_to_nat!; omega)
  have hle' : M.eRank + 1 ≤ (M.E \ D).encard := by
    rw [← encard_diff_add_encard_of_subset hDE] at hlt
    eomega
  obtain ⟨D', hD'E, hD'⟩ := exists_subset_encard_eq hle'
  have hrt : ¬ M.RankInfinite := by rw [← eRank_eq_top_iff]; enat_to_nat!
  refine (h.inter_nonempty_of_dep_dep ?_ ?_).not_disjoint (disjoint_sdiff_right.mono_right hD'E)
  · rw [← not_indep_iff]
    exact fun hi ↦ hrt <| by simpa [hD] using hi.encard_le_eRank
  rw [← not_indep_iff]
  exact fun hi ↦ hrt <| by simpa [hD'] using hi.encard_le_eRank

lemma VerticallyConnected.compl_spanning_of_nonspanning (h : M.VerticallyConnected ⊤)
    (hX : M.Nonspanning X) : M.Spanning (M.E \ X) := by
  rw [verticallyConnected_top_iff] at h
  simpa [hX.not_spanning] using h X hX.subset_ground

lemma CyclicallyConnected.compl_indep_of_dep (h : M.CyclicallyConnected ⊤) (hX : M.Dep X) :
    M.Indep (M.E \ X) := by
  rw [cyclicallyConnected_top_iff] at h
  simpa [hX.not_indep] using h X hX.subset_ground

/-- A rank-`k` uniform matroid is infinitely Tutte-connected if and only if its
cardinality is `2k-1`, `2k` or `2k+1`.  -/
lemma unifOn_tutteConnected_top_iff {E : Set α} {k : ℕ} (hkE : k ≤ E.encard) :
    (unifOn E k).TutteConnected ⊤ ↔
    (E.encard = 2 * k ∨ E.encard + 1 = 2 * k ∨ E.encard = 2 * k + 1) := by
  have aux (s t : ℕ∞) : ((s = 2 * t) ∨ (s + 1 = 2 * t) ∨ (s = 2 * t + 1)) ↔
      (2 * t ≤ s + 1 ∧ s ≤ 2 * t + 1) := by eomega
  rw [aux]
  clear aux
  refine ⟨fun h ↦ ?_, fun ⟨hle, hle'⟩ ↦ ?_⟩
  · exact ⟨by simpa [min_eq_right hkE] using h.verticallyConnected.two_mul_eRank_le,
      by simpa [min_eq_right hkE] using h.cyclicallyConnected.encard_le⟩
  suffices hsuff : ∀ ⦃X⦄, X ⊆ E →
    X.encard ≤ k ∧ k ≤ (E \ X).encard ∨ (E \ X).encard ≤ k ∧ k ≤ X.encard by
    simpa +contextual [TutteConnected, numConnected_top_iff', unifOn_coindep_iff'' hkE,
      diff_subset, tutteDegen_iff]
  intro X hX
  have hcard := encard_diff_add_encard_of_subset hX
  enat_to_nat!; lia

/-- For finite `r`, a rank-`r` uniform matroid is `k`-Tutte-connected if and only if either
it has size `2r-1, 2r` or `2r+1`, or `k` is at most the rank and at most the corank. -/
lemma unifOn_tutteConnected_iff {E : Set α} {r : ℕ} (hrE : r ≤ E.encard) :
    (unifOn E r).TutteConnected (k + 1) ↔ (k ≤ r ∧ k + r ≤ E.encard) ∨
      (E.encard = 2 * r ∨ E.encard + 1 = 2 * r ∨ E.encard = 2 * r + 1) := by
  rw [← unifOn_tutteConnected_top_iff hrE]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain hle | hlt := le_or_gt k r
    · obtain hle' | hlt' := le_or_gt (k + r) E.encard
      · simp [hle, hle']
      refine .inr <| h.tutteConnected_top_of_eRank_dual_add_one_le <| Order.add_one_le_of_lt ?_
      rwa [← unifOn_ground_eq E, ← (unifOn E r).eRank_add_eRank_dual, add_comm,
        unifOn_eRank_eq, min_eq_right hrE, WithTop.add_lt_add_iff_right (ENat.coe_ne_top _)] at hlt'
    · refine .inr <| h.tutteConnected_top_of_eRank_add_one_le <| Order.add_one_le_of_lt ?_
      rwa [unifOn_eRank_eq, min_eq_right hrE]
  by_cases hconn : (unifOn E r).TutteConnected ⊤
  · exact hconn.mono le_top
  obtain ⟨hkr, hkrE⟩ := (or_iff_left hconn).1 h
  rw [unifOn_tutteConnected_top_iff hrE] at hconn
  have : 2 * k + 2 ≤ E.encard := by eomega
  rw [tutteConnected_iff_verticallyConnected_girth (by rw [unifOn_ground_eq]; eomega),
    le_girth_iff, verticallyConnected_iff_forall]
  refine ⟨fun P hPconn hPsep ↦ ?_, fun C hC ↦ ?_⟩
  · simp_rw [isVerticalSeparation_iff_forall_nonspanning, ← Separation.not_spanning_iff,
      unifOn_spanning_iff hrE P.subset_ground, not_le] at hPsep
    rw [← (unifOn_ground_eq E (k := r)), ← eRank_add_eRank_dual,
      ← Indep.eConn_eq_of_compl_indep (I := P true), P.eConn_eq, unifOn_eRank_eq,
      min_eq_right hrE, add_comm, WithTop.add_le_add_iff_left (ENat.coe_ne_top r)] at hkrE
    · eomega
    · simpa [(hPsep true).le] using P.subset_ground
    rw [P.compl_true]
    simpa [(hPsep false).le] using P.subset_ground
  rw [unifOn_isCircuit_iff] at hC
  simpa [hC.1]

/-- This might be true without `Tame`. -/
lemma IsUniform.tutteConnected_iff [M.Tame] (h : M.IsUniform) :
    M.TutteConnected (k + 1) ↔ (k ≤ M.eRank ∧ k ≤ M✶.eRank) ∨ M.TutteConnected ⊤ := by
  refine ⟨fun h ↦ ?_, fun h' ↦ h'.elim (fun ⟨hle, hle'⟩ ↦ ?_) (fun h' ↦ h'.mono le_top)⟩
  · rw [or_iff_not_imp_left, Classical.not_and_iff_not_or_not, not_le, not_le]
    rintro (hlt | hlt)
    · exact h.tutteConnected_top_of_eRank_add_one_le (Order.add_one_le_of_lt hlt)
    exact h.tutteConnected_top_of_eRank_dual_add_one_le (Order.add_one_le_of_lt hlt)
  clear h'
  wlog hfin : M.RankFinite generalizing M with aux
  · have := M.tame_dual
    rw [← tutteConnected_dual_iff]
    apply aux h.dual (by simp [hle, hle']) hle' (by simpa)
    exact h.sparsePaving.rankFinite_or_rankFinite_dual.elim (False.elim ∘ hfin) id
  have hrle := M.eRank_lt_top
  have hr := M.eRank_add_eRank_dual
  rw [tutteConnected_iff_verticallyConnected_girth (by eomega), le_girth_iff,
    verticallyConnected_iff_forall]
  refine ⟨fun P hP hsep ↦ ?_, fun C hC ↦ ?_⟩
  · rw [isVerticalSeparation_iff_forall_nonspanning] at hsep
    have h1 := h.indep_of_nonspanning <| hsep true
    have h2 := h.indep_of_nonspanning <| hsep false
    have hr1 := (hsep true).eRk_add_one_le
    have hr2 := (hsep false).eRk_add_one_le
    replace hr := hr.le
    grw [← hle', ← P.union_eq, encard_union_le, ← h1.eRk_eq_encard, ← h2.eRk_eq_encard] at hr
    have hconn := M.eConn_add_eRank_eq (X := P true)
    rw [P.eConn_eq, P.compl_eq, Bool.not_true] at hconn
    enat_to_nat! <;> omega
  rwa [← hC.eRk_add_one_eq, (h.spanning_of_dep hC.dep).eRk_eq, ENat.add_one_le_add_one_iff]

/-- Every tame, infinitely Tutte-connected matroid is finite. -/
lemma TutteConnected.finite_of_tame [M.Tame] (hM : M.TutteConnected ⊤) : M.Finite := by
  wlog hfin : M.RankFinite generalizing M with aux
  · obtain hfin | hfin := hM.isUniform.sparsePaving.rankFinite_or_rankFinite_dual
    · exact aux hM (by infer_instance)
    have := M.tame_dual
    exact ⟨(aux hM.dual (by infer_instance)).ground_finite⟩
  grw [finite_iff, ← encard_lt_top_iff, hM.cyclicallyConnected.encard_le]
  have := M.eRank_lt_top
  enat_to_nat!

lemma tutteConnected_top_iff_of_tame [M.Tame] : M.TutteConnected ⊤ ↔
    M.IsUniform ∧ M.Finite ∧ M.E.encard ≤ 2 * M.eRank + 1 ∧ 2 * M.eRank ≤ M.E.encard + 1 := by
  refine ⟨fun h ↦ ⟨h.isUniform, h.finite_of_tame, ?_⟩, fun ⟨hU, hfin, hle, hle'⟩ ↦ ?_⟩
  · exact ⟨h.cyclicallyConnected.encard_le, h.verticallyConnected.two_mul_eRank_le⟩
  obtain ⟨E, k, hkE, rfl, h'⟩ := hU.exists_eq_unifOn
  rw [unifOn_tutteConnected_top_iff hkE]
  rw [unifOn_ground_eq, unifOn_eRank_eq' hkE] at hle hle'
  eomega

lemma Paving.cyclicallyConnected (h : M.Paving) (hk : k < M.eRank) : M.CyclicallyConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine cyclicallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  rw [Separation.isCyclicSeparation_iff_forall] at hP
  nth_grw 1 [h.eRank_le_eRk_add_one_of_dep (hP false), ← hPconn,
    ← h.eRelRk_ground_le_of_dep (hP true), ← P.compl_false, ← nullity_dual_eq ..,
    ← P.eConn_eq false, M.eConn_add_nullity_dual_eq_eRk (P false)] at hk
  exact hk.ne rfl

lemma Paving.cyclicallyConnected_of_verticallyConnected (h : M.Paving)
    (hconn : M.VerticallyConnected (k + 1)) (hk : k < M.eRank) : M.CyclicallyConnected (k + 1) := by
  refine cyclicallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  rw [Separation.isCyclicSeparation_iff_forall] at hP
  wlog hs : M.Spanning (P true) generalizing P with aux
  · refine hconn.not_isVerticalSeparation (P := P) (by simpa) ?_
    simp_rw [Separation.isVerticalSeparation_iff_forall_nonspanning, ← Separation.not_spanning_iff,
      Bool.forall_bool, and_iff_left hs]
    exact aux P.symm (by simpa) <| by simpa [and_comm] using Bool.forall_bool.1 hP
  grw [← hPconn, ← P.eConn_eq true, hs.eConn_eq, P.compl_true,
    h.eRank_le_eRk_add_one_of_dep (hP false)] at hk
  exact hk.ne rfl

lemma SparsePaving.tutteConnected_of_eRank_gt_eRank_dual_ge (h : M.SparsePaving)
    (h1 : k < M.eRank) (h2 : k ≤ M✶.eRank) : M.TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [ENat.add_one_le_iff (by enat_to_nat)] at h2
  rw [tutteConnected_iff_verticallyConnected_cyclicallyConnected]
  · have h' := h.1.cyclicallyConnected h1
    have h'' := h.dual.1.cyclicallyConnected_of_verticallyConnected (by simpa) h2
    simp only [cyclicallyConnected_dual_iff] at h''
    exact ⟨h'', h'⟩
  rw [← eRank_add_eRank_dual]
  enat_to_nat!
  omega

lemma SparsePaving.tutteConnected_of_eRank_ge_eRank_dual_gt (h : M.SparsePaving)
    (h1 : k ≤ M.eRank) (h2 : k < M✶.eRank) : M.TutteConnected k :=
  by simpa using (h.dual.tutteConnected_of_eRank_gt_eRank_dual_ge h2 (by simpa)).dual

lemma VerticallyConnected.sparsePaving_of_cyclicallyConnected (hv : M.VerticallyConnected ⊤)
    (hc : M.CyclicallyConnected ⊤) : M.SparsePaving := by
  rw [sparsePaving_iff_forall_indep_or_spanning_or_isCircuit_isHyperplane]
  by_contra! hcon
  obtain ⟨X, hXE, hd, hns, hch⟩ := hcon
  rw [not_indep_iff] at hd
  rw [not_spanning_iff] at hns
  wlog hnot : ¬ M.IsCircuit X generalizing M X with aux
  · rw [not_not] at hnot
    refine aux hc.dual_verticallyConnected hv.dual_cyclicallyConnected (X := M.E \ X)
      diff_subset hns.codep_compl ?_ ?_ ?_
    · rwa [nonspanning_compl_dual_iff]
    · rwa [← isCocircuit_def, isCocircuit_compl_iff_isHyperplane, isHyperplane_compl_dual_iff,
        imp_not_comm]
    rw [← isCocircuit_def, isCocircuit_compl_iff_isHyperplane]
    exact hch hnot
  obtain ⟨C, hCX, hC⟩ := hd.exists_isCircuit_subset
  have h_eq := (hc.compl_indep_of_dep hC.dep).eq_of_spanning_subset
    (hv.compl_spanning_of_nonspanning hns) (diff_subset_diff_right hCX)
  rw [← diff_diff_cancel_left hXE, h_eq, diff_diff_cancel_left hC.subset_ground] at hnot
  contradiction

-- lemma something [M.Tame] (hv : M.VerticallyConnected ⊤) (hc : M.CyclicallyConnected ⊤) :
--     M.TutteConnected ⊤ ↔ M = M✶ := by
--   rw [tutteConnected_top_iff_verticallyConnected_cyclicallyConnected_isUniform,
--     and_iff_right hv, and_iff_right hc]

--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   ·

--     rw [ext_iff_isBase, dual_ground, and_iff_right rfl]
--     intro B hBE
--     wlog hB : M.IsBase B generalizing M B with aux
--     · rw [iff_false_intro hB, false_iff]
--       refine fun hB' ↦ hB ?_
--       have := M.tame_dual
--       rwa [← M.dual_dual, ← aux hc.dual_verticallyConnected hv.dual_cyclicallyConnected h.dual
--         hB'.subset_ground hB']
--     rw [iff_true_intro hB, true_iff]


    -- obtain hi | hd := M✶.indep_or_dep (X := B)
    -- · obtain hs | hns := M✶.spanning_or_nonspanning (X := B)
    --   · exact hi.isBase_of_spanning hs

      -- have := hc.dual_verticallyConnected.compl_spanning_of_nonspanning hns



    -- have := h.sparsePaving.rankFinite_or_rankFinite_dual

  -- rw [tutteConnected_top_iff_verticallyConnected_cyclicallyConnected_isUniform,
  --   and_iff_right hv, and_iff_right hc, not_iff_comm, not_and, Ne, not_not]

  -- refine ⟨fun h X hXE ↦ ?_, fun h ↦ ?_⟩
  -- · rw [← not_dep_iff, ← not_nonspanning_iff, ← Classical.not_and_iff_not_or_not]
  --   intro ⟨hXd, hXn⟩
  --   by_cases hs : M.SparsePaving
  --   · have hci := (hv.compl_spanning_of_nonspanning hXn).compl_coindep
  --     rw [diff_diff_cancel_left hXE, coindep_def, ← h hs] at hci
  --     exact hXd.not_indep hci
  --   clear! X
  --   rw [sparsePaving_iff_forall_indep_or_spanning_or_isCircuit_isHyperplane] at hs
  --   push_neg at hs
  --   obtain ⟨Y, hYE, hni, hns, hch⟩ := hs
  --   rw [not_spanning_iff] at hns
  --   rw [not_indep_iff] at hni
  --   wlog hnot : ¬ M.IsCircuit Y generalizing M Y with aux
  --   · rw [not_not] at hnot
  --     have := M.tame_dual
  --     specialize aux hc.dual_verticallyConnected hv.dual_cyclicallyConnected (by simpa [eq_comm])
  --       (Y := M.E \ Y) diff_subset
  --     simp only [dep_dual_iff, hns.codep_compl, imp_false, not_not, forall_const] at aux
  --     rw [isHyperplane_compl_dual_iff, ← isCocircuit_def, nonspanning_compl_dual_iff,
  --       imp_iff_right hni, imp_not_comm, imp_iff_right hnot, isCocircuit_compl_iff_isHyperplane,
  --       not_imp_self] at aux
  --     exact hch hnot aux
  --   obtain ⟨C, hCY, hC⟩ := hni.exists_isCircuit_subset
  --   have := hv.compl_spanning_of_nonspanning hns





    -- intro ⟨hC', hns⟩
    -- wlog hC : M.IsCircuit C generalizing C with aux
    -- · obtain ⟨C₀, hC₀C, hC₀⟩ := hC'.exists_isCircuit_subset
    --   exact aux C₀ hC₀.subset_ground hC₀.dep (hns.subset hC₀C) hC₀

    -- -- wlog hC : M.IsCircuit C gener
    -- have hX1 := cyclicallyConnected_top_iff.1 hc C hCE
    -- have hX2 := verticallyConnected_top_iff.1 hv C hCE

    -- rw [or_iff_right hC.not_indep] at hX1
    -- rw [or_iff_right hns.not_spanning] at hX2


    -- rw [cyclicallyConnected_top_iff] at hc
