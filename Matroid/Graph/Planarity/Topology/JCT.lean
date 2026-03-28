import Matroid.ForMathlib.Card
import Matroid.Graph.Planarity.Plane
import Matroid.Graph.Planarity.Cut
import Matroid.Graph.Planarity.PolygonalPath

open Set EuclideanSpace RealInnerProductSpace Metric Plane
variable {x y z a b c u v : ℝ²} {S : Set ℝ²} {P : PolygonalPath x x}

lemma PolygonalPath.simple.epsilon_inter_subset_segment {P : PolygonalPath x y} (hbP : b ∈ P.toSet)
    (hbv : b ∉ P.vertices) (hP : P.simple) : ∃ ε > 0, ∃ s ∈ P.vPairs,
    b ∈ segment ℝ s.1 s.2 ∧ ball b ε ∩ P.toSet = ball b ε ∩ segment ℝ s.1 s.2 := by
  obtain ⟨⟨a, c⟩, ⟨hacP, hac⟩, hacUnique⟩ := hP.unique_segment hbP hbv
  let g := ⋃ s ∈ {s | s ∈ P.vPairs} \ {(a, c)}, segment ℝ s.1 s.2
  have hgcl : IsClosed g := by apply Finite.isClosed_biUnion <;> simp
  have hb : b ∈ gᶜ := by
    simp only [mem_diff, mem_setOf_eq, mem_singleton_iff, ← ne_eq, compl_iUnion, mem_iInter,
      mem_compl_iff, and_imp, g]
    exact fun s hsP hne hbs ↦ hne <| hacUnique s ⟨hsP, hbs⟩
  have hPg : P.toSet = g ∪ segment ℝ a c := by
    rw [P.toSet_eq_biUnion, ← biUnion_singleton (a, c) (fun s ↦ segment ℝ s.1 s.2),
      ← biUnion_union, diff_union_self, union_eq_left.mpr (by simpa)]
    rfl
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hgcl.isOpen_compl b hb
  rw [subset_compl_iff_disjoint_left] at hε
  use ε, hεpos, (a, c), hacP, hac
  rw [hPg, inter_union_distrib_left, hε.symm.inter_eq, empty_union]

lemma PolygonalPath.closedSimple.epsilon_inter_subset_segment (hbP : b ∈ P.toSet)
    (hbv : b ∉ P.vertices) (hP : P.closedSimple) : ∃ ε > 0, ∃ s ∈ P.vPairs,
    b ∈ openSegment ℝ s.1 s.2 ∧ s.1 ∉ ball b ε ∧ s.2 ∉ ball b ε ∧
    ball b ε ∩ P.toSet = ball b ε ∩ segment ℝ s.1 s.2 := by
  obtain ⟨⟨a, c⟩, ⟨hacP, hac⟩, hacUnique⟩ := hP.unique_segment hbP hbv
  let g := ⋃ s ∈ {s | s ∈ P.vPairs} \ {(a, c)}, segment ℝ s.1 s.2
  have hgcl : IsClosed g := by apply Finite.isClosed_biUnion <;> simp
  have hb : b ∈ gᶜ := by
    simp only [mem_diff, mem_setOf_eq, mem_singleton_iff, ← ne_eq, compl_iUnion, mem_iInter,
      mem_compl_iff, and_imp, g]
    exact fun s hsP hne hbs ↦ hne <| hacUnique s ⟨hsP, hbs⟩
  have hPg : P.toSet = g ∪ segment ℝ a c := by
    rw [P.toSet_eq_biUnion, ← biUnion_singleton (a, c) (fun s ↦ segment ℝ s.1 s.2),
      ← biUnion_union, diff_union_self, union_eq_left.mpr (by simpa)]
    rfl
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hgcl.isOpen_compl b hb
  rw [subset_compl_iff_disjoint_left] at hε
  have hag : a ∈ g := by sorry
  have hcg : c ∈ g := by sorry
  use ε, hεpos, (a, c), hacP, ?_, hε.notMem_of_mem_left hag, hε.notMem_of_mem_left hcg, ?_
  · simp only [← insert_endpoints_openSegment, mem_insert_iff] at hac
    obtain rfl | rfl | hbac := hac
    · simpa [hεpos] using hε.notMem_of_mem_left hag
    · simpa [hεpos] using hε.notMem_of_mem_left hcg
    exact hbac
  rw [hPg, inter_union_distrib_left, hε.symm.inter_eq, empty_union, ← insert_endpoints_openSegment,
    inter_insert_of_notMem, inter_insert_of_notMem] <;> refine hε.notMem_of_mem_left (by assumption)

lemma PolygonalPath.closedSimple.epsilon_inter_subset_segment_two (hbP : b ∈ P.vertices)
    (hP : P.closedSimple) : ∃ ε > 0, ∃ a c, a ∉ ball b ε ∧ c ∉ ball b ε ∧
    ball b ε ∩ P.toSet = ball b ε ∩ (segment ℝ a b ∪ segment ℝ b c) := by
  sorry

lemma PolygonalPath.closedSimple.epsilon_clock {P : PolygonalPath x x} (hbP : b ∈ P.toSet)
    (hP : P.closedSimple) : ∃ ε > 0, ∃ a c, ball b ε ∩ P.toSet =
    ball b ε ∩ (halfRay (segmentTangent b a) b ∪ halfRay (segmentTangent b c) b) := by
  by_cases hbv : b ∈ P.vertices
  · sorry
    -- obtain ⟨ε, hεpos, a, c, hac⟩ := hP.epsilon_inter_subset_segment_two hbv
    -- use ε, hεpos, a, c
    -- rw [hac, inter_union_distrib_left, inter_union_distrib_left, ball_inter_segment_eq_inter_halfRay,
    --   segment_symm, ball_inter_segment_eq_inter_halfRay]
    -- · suffices a ∉ ball b ε by simpa [mem_ball, not_lt] using this
    --   sorry
    -- suffices c ∉ ball b ε by simpa [mem_ball, not_lt] using this
    -- sorry
  obtain ⟨ε, hεpos, s, hsP, hbs, hs1b, hs2b, h⟩ := hP.epsilon_inter_subset_segment hbP hbv
  use ε, hεpos, s.1, s.2
  rw [h, ← segment_union_eq_segment (z := b) (by simp [← insert_endpoints_openSegment, hbs]),
    inter_union_distrib_left, inter_union_distrib_left,
    ball_inter_segment_eq_inter_halfRay, segment_symm, ball_inter_segment_eq_inter_halfRay]
  · simpa [dist_eq_norm] using hs1b
  simpa [dist_eq_norm] using hs2b

lemma JCT_induction (hP : P.closedSimple) (hzP : z ∈ P.toSet) (hzv : z ∈ frontier (P.region v)) :
    P.toSet ⊆ frontier (P.region v) := by
  intro y hyP
  let r : ℝ² → ℝ² → Prop := fun u u' ↦ (u ∈ frontier (P.region v) ↔ u' ∈ frontier (P.region v))
  refine (P.toSet_isConnected.isPreconnected.induction₂ r ?_ (by grind) (by grind) hzP hyP).mp hzv
  simp_rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball, r]
  intro x hxP
  obtain ⟨ε, hεpos, a, c, h⟩ := hP.epsilon_clock hxP
  refine ⟨ε, hεpos, fun y hyx hyP ↦ ?_⟩
  suffices (∃ z ∈ P.toSet, z ∈ ball x ε) → ball x ε ∩ P.toSet ⊆ frontier (P.region v) by
    have hex : ∃ z ∈ P.toSet, z ∈ ball x ε := by use x, hxP, by simpa
    simp [this hex ⟨by simpa, hxP⟩, this hex ⟨hyx, hyP⟩]
  rintro ⟨z, hzP, hzx⟩
  rw [h]
  -- have := clock_frontier (x := x) (r := ε) (u := segmentTangent x a) (v := segmentTangent x c)
  sorry


lemma JCT_le_two (hP : P.closedSimple) (ha : a ∉ P.toSet) (hb : b ∉ P.toSet) (hc : c ∉ P.toSet)
    (hab : ¬ JoinedIn P.toSetᶜ a b) : JoinedIn P.toSetᶜ a c ∨ JoinedIn P.toSetᶜ b c := by
  by_contra! hS
  obtain ⟨hac, hbc⟩ := hS
  obtain ⟨Pa, hPaP, hPaf⟩ := P.exists_mem_frontier_connectedComponentIn ha
  have := JCT_induction hP hPaP hPaf
  obtain ⟨y, Py, rfl, hPy, hdj⟩ := hP.cons_simple
  let half : unitInterval := ⟨1/2, by constructor <;> linarith⟩
  let Pd := Path.segment x y half

  sorry
