module

public import Matroid.ForMathlib.Geometry.Polygon.JordanCurve
public import Matroid.ForMathlib.Geometry.PolygonalPath.LocalStar
public import Matroid.ForMathlib.Geometry.PolygonalPath.SimpleArcOrLoop
public import Matroid.ForMathlib.Geometry.StarComponents
public import Matroid.ForMathlib.Topology.ConnectedComponent

/-!
# The polygonal theta-curve theorem

Three simple polygonal arcs with the same two endpoints and no other common points cut the
one-point compactification of the plane into exactly three regions.

This file is graph-free.  The theorem used to live under `Graph.Planarity`; keeping its actual proof
here records its real mathematical ownership and prevents graph/drawing hypotheses from leaking
into local topology.

## Proof architecture

The proof is split along mathematical boundaries rather than accumulated into one large theorem.

1. **Local classification.**  At either common endpoint the theta set has exactly three radial
   germs.  At an interior point of one arm it has exactly two.
2. **Candidate components.**  For each omitted arm, the other two arms form a Jordan loop.  The
   side opposite the omitted arm is a genuine component of the theta complement.
3. **Distinctness.**  The three candidate components have different frontiers.
4. **Exhaustion.**  For an arbitrary complement component choose a frontier point.  The generic
   component-frontier lemmas put it on the theta set.  The point is either a common endpoint or an
   interior point of a unique arm.  The corresponding three-sector/two-sector local classification
   forces the component to be one of the candidates.

The endpoint proof must localize each arm before applying `le_card_radii_of_pairwise`: globally two
different arms meet at both `a` and `b`, whereas the counting lemma asks that the chosen pieces meet
only at the center of the star.
-/

open Function Set Topology Metric
open scoped unitInterval

namespace PolygonalPath

public noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a b : V}

/-! ### Local theta structure -/

section

/-- At either common endpoint, a theta curve has exactly three local radial germs.  The requested
upper bound makes the lemma stable under later shrinking requirements.

This is private because the theta statement is currently a bootstrap theorem.  The reusable
dimension-free local theorem is `IsSimple.exists_local_star_two`; a future abstract
two-dimensional version of the sector theory should subsume this endpoint packaging. -/
private theorem exists_endpoint_star_three
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b})
    (p : V) (hp : p = a ∨ p = b) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ε ∧
      ∃ Y : Finset V, Y.card = 3 ∧
        (Y : Set V) ⊆ sphere p ρ ∧
        closedBall p ρ ∩ (⋃ i, (A i).toSet) =
          {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  have star {x y : V} (hxy : x ≠ y) (B : Fin 3 → PolygonalPath x y)
      (hsB : ∀ i, (B i).IsSimple)
      (hmeetB : ∀ i j, i ≠ j → (B i).toSet ∩ (B j).toSet = {x, y}) {ε : ℝ} (hε : 0 < ε) :
      ∃ ρ, 0 < ρ ∧ ρ ≤ ε ∧
        ∃ Y : Finset V, Y.card = 3 ∧
          (Y : Set V) ⊆ sphere x ρ ∧
          closedBall x ρ ∩ (⋃ i, (B i).toSet) =
            {x} ∪ ⋃ z ∈ Y, segment ℝ x z := by
    let T : Set V := ⋃ i, (B i).toSet
    have hT : IsSegmentFigure T := IsSegmentFigure.iUnion fun i ↦ (B i).isSegmentFigure_toSet
    have hxT : x ∈ T :=
      mem_iUnion.mpr ⟨0, (B 0).mem_toSet_of_mem_vertices (B 0).first_mem_vertices⟩
    obtain ⟨ρ0, hρ0, Y0, hY0, hstar0⟩ := hT.exists_radius hxT
    choose ρA hρApos hAball using fun i ↦ exists_ball_inter_subset_firstSegment (hsB i) hxy
    let ρAmin : ℝ := min (ρA 0) (min (ρA 1) (ρA 2))
    let ρ : ℝ := min ε (min ρ0 (min (dist x y / 2) ρAmin))
    have hρAmin_pos : 0 < ρAmin := lt_min (hρApos 0) (lt_min (hρApos 1) (hρApos 2))
    have hρ : 0 < ρ :=
      lt_min hε (lt_min hρ0 (lt_min (half_pos (dist_pos.mpr hxy)) hρAmin_pos))
    have hρ_le_ε : ρ ≤ ε := min_le_left _ _
    have hρ_le_ρ0 : ρ ≤ ρ0 := (min_le_right ε _).trans (min_le_left _ _)
    have hρ_le_half : ρ ≤ dist x y / 2 :=
      (min_le_right ε _).trans ((min_le_right ρ0 _).trans (min_le_left _ _))
    have hρ_le_ρA (i : Fin 3) : ρ ≤ ρA i := by
      have h1 : ρ ≤ ρAmin :=
        (min_le_right ε _).trans ((min_le_right ρ0 _).trans (min_le_right _ _))
      have h2 : ρAmin ≤ ρA i := by
        fin_cases i
        · exact min_le_left _ _
        · exact (min_le_right (ρA 0) _).trans (min_le_left _ _)
        · exact (min_le_right (ρA 0) _).trans (min_le_right _ _)
      exact h1.trans h2
    obtain ⟨Y, hY, -, hstar⟩ := exists_radius_of_le hρ0 hY0 hstar0 hρ hρ_le_ρ0
    let U : Fin 3 → Set V := fun i ↦ (B i).toSet ∩ closedBall x ρ
    let z : Fin 3 → V := fun i ↦ (B i).firstTip
    have hlen (i : Fin 3) : 0 < (B i).length := (B i).length_pos_of_ne hxy
    have hzne (i : Fin 3) : z i ≠ x := (hsB i).firstTip_ne (hlen i)
    have hUT : ∀ i, U i ⊆ T :=
      fun i ↦ inter_subset_left.trans (subset_iUnion (fun j ↦ (B j).toSet) i)
    have hUp : ∀ i, ∃ w ≠ x, segment ℝ x w ⊆ U i := by
      intro i
      let r : ℝ := min ρ (dist x (z i))
      have hrpos : 0 < r := lt_min hρ (dist_pos.mpr (hzne i).symm)
      refine ⟨radialPoint x (z i) r, ?_, ?_⟩
      · exact ne_of_mem_sphere (mem_sphere_radialPoint x (z i) hrpos.le (hzne i)) hrpos.ne'
      · intro u hu
        refine ⟨segment_firstTip_subset_toSet (B i) (hlen i)
            (segment_subset_segment_right
              (radialPoint_mem_segment x (z i) hrpos.le (min_le_right _ _)) hu), ?_⟩
        exact (convex_closedBall x ρ).segment_subset (mem_closedBall_self hρ.le)
          (by
            have hdist : dist (radialPoint x (z i) r) x = r :=
              dist_radialPoint x (z i) hrpos.le (hzne i)
            exact mem_closedBall.mpr (hdist.trans_le (min_le_left _ _))) hu
    have hUmeet : ∀ i j, i ≠ j → U i ∩ U j ⊆ {x} := by
      intro i j hij u ⟨hui, huj⟩
      have huij : u ∈ ({x, y} : Set V) := (hmeetB i j hij) ▸ ⟨hui.1, huj.1⟩
      rw [mem_insert_iff, mem_singleton_iff] at huij
      rcases huij with rfl | rfl
      · rfl
      · have : dist u x ≤ ρ := mem_closedBall.mp hui.2
        rw [dist_comm] at this
        linarith [half_lt_self (dist_pos.mpr hxy), hρ_le_half]
    have hge : Fintype.card (Fin 3) ≤ Y.card :=
      le_card_radii_of_pairwise (T := T) hρ hY hstar hUT hUp hUmeet
    have hcover : T ∩ closedBall x ρ ⊆ {x} ∪ ⋃ i, U i := by
      intro u ⟨huT, huball⟩
      refine Or.inr ?_
      obtain ⟨i, hui⟩ := mem_iUnion.mp huT
      exact mem_iUnion.mpr ⟨i, hui, huball⟩
    have hUz : ∀ i, U i ∩ closedBall x ρ ⊆ segment ℝ x (z i) := by
      intro i u ⟨huU, huball⟩
      exact hAball i ⟨huU.1, closedBall_subset_closedBall (hρ_le_ρA i) huball⟩
    have hle : Y.card ≤ Fintype.card (Fin 3) :=
      card_radii_le_of_cover (T := T) hρ hY hstar hcover hzne hUz
    refine ⟨ρ, hρ, hρ_le_ε, Y, ?_, hY, hstar⟩
    rw [← Fintype.card_fin (n := 3)]
    exact Nat.le_antisymm hle hge
  rcases hp with rfl | rfl
  · exact star hab A hsimple hmeet hε
  · simpa [← toSet_eq_range_toPath, toSet_reverse] using
      star hab.symm (fun i ↦ (A i).reverse)
        (fun i ↦ isSimple_reverse.mpr (hsimple i))
        (fun i j hij ↦ by
          rw [toSet_reverse, toSet_reverse, hmeet i j hij, pair_comm]) hε

/-- At an interior point of one arm, sufficiently small neighborhoods of the whole theta set have
exactly two radial germs. -/
private theorem exists_arm_interior_star_two
    (_hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b})
    (i : Fin 3) {q : V} (hq : q ∈ (A i).toSet \ {a, b})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ε ∧
      ∃ Y : Finset V, Y.card = 2 ∧
        (Y : Set V) ⊆ sphere q ρ ∧
        closedBall q ρ ∩ (⋃ j, (A j).toSet) =
          {q} ∪ ⋃ y ∈ Y, segment ℝ q y := by
  have hqa : q ≠ a := fun h ↦ hq.2 (mem_insert_iff.mpr (Or.inl h))
  have hqb : q ≠ b := fun h ↦ hq.2 (by simp [h])
  let K : Set V := ⋃ j : {j : Fin 3 // j ≠ i}, (A j.1).toSet
  have hKcompact : IsCompact K := isCompact_iUnion fun j ↦ (A j.1).isCompact_toSet
  have hqK : q ∉ K := by
    intro hqK
    obtain ⟨j, hj⟩ := mem_iUnion.mp hqK
    exact hq.2 ((hmeet i j.1 j.2.symm) ▸ ⟨hq.1, hj⟩)
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_dist_of_notMem hKcompact.isClosed hqK
  let ε' : ℝ := min ε (δ / 2)
  have hε' : 0 < ε' := lt_min hε (half_pos hδpos)
  obtain ⟨ρ, hρ, hρ_le, Y, hYcard, hYsph, hstar⟩ :=
    IsSimple.exists_local_star_two (hsimple i) hq.1 hqa hqb hε'
  have hρ_le_ε : ρ ≤ ε := hρ_le.trans (min_le_left _ _)
  have hρ_le_half : ρ ≤ δ / 2 := hρ_le.trans (min_le_right _ _)
  have hTK : (⋃ j, (A j).toSet) = (A i).toSet ∪ K := by
    ext u
    constructor
    · intro hu
      obtain ⟨j, hj⟩ := mem_iUnion.mp hu
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
    · rintro (h | h)
      · exact mem_iUnion.mpr ⟨i, h⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (show u ∈ ⋃ j : {j : Fin 3 // j ≠ i}, (A j.1).toSet from h)
        exact mem_iUnion.mpr ⟨j.1, hj⟩
  have hKball : closedBall q ρ ∩ K = ∅ := by
    ext u
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro huball huK
    have : dist u q ≤ ρ := mem_closedBall.mp huball
    linarith [hδle u huK, dist_comm u q ▸ this, half_lt_self hδpos, hρ_le_half]
  refine ⟨ρ, hρ, hρ_le_ε, Y, hYcard, hYsph, ?_⟩
  rw [hTK, inter_union_distrib_left, hKball, union_empty, hstar]

end

variable [Fact (Module.finrank ℝ V = 2)]

/-! ### The three JCT candidate components -/

/-- For one omitted arm, the other two arms bound a genuine component of the theta complement,
whose frontier is exactly those two arms. -/
private theorem exists_candidate_region
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b})
    (i : Fin 3) :
    ∃ (W : Set (OnePoint V)) (w : OnePoint V),
      w ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ ∧
      W = connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) w ∧
      IsOpen W ∧ IsConnected W ∧
      frontier W =
        (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet := by
  let j : Fin 3 := i + 1
  let k : Fin 3 := i + 2
  have hji : j ≠ i := fun h ↦
    Fin.zero_ne_one.symm (add_left_cancel (h.trans (add_zero i).symm))
  have hki : k ≠ i := fun h ↦
    absurd (add_left_cancel (h.trans (add_zero i).symm)) (by decide : (2 : Fin 3) ≠ 0)
  have hjk : j ≠ k := fun h ↦
    absurd (add_left_cancel h) (by decide : (1 : Fin 3) ≠ 2)
  have hcompl : ({i}ᶜ : Set (Fin 3)) = {j, k} := by
    ext t
    simp only [mem_compl_iff, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro hti
      fin_cases i <;> fin_cases t <;> simp [j, k] at hti ⊢
    · rintro (rfl | rfl)
      · exact hji
      · exact hki
  let Ploop : PolygonalPath a a := (A j).append (A k).reverse
  have hPloop : Ploop.IsSimpleLoop :=
    (isSimpleLoop_append_iff hab).mpr
      ⟨hsimple j, isSimple_reverse.mpr (hsimple k), by rw [toSet_reverse, hmeet j k hjk]⟩
  have hJ : IsJordanCurve Ploop.toSet := IsSimpleLoop.isJordanCurve hPloop
  have hPset : Ploop.toSet = (A j).toSet ∪ (A k).toSet := by
    rw [toSet_append, toSet_reverse]
  have hsa : (A i).IsSimpleArcOrLoop :=
    Or.inl ⟨hsimple i, (A i).length_pos_of_ne hab⟩
  have hinter : ((A i).toSet \ {a, b}).Nonempty := by
    rw [hsa.toSet_diff_endpoints]
    exact (nonempty_Ioo.2 (zero_lt_one : (0 : I) < 1)).image _
  have hinter_conn : IsConnected ((A i).toSet \ {a, b}) := by
    rw [hsa.toSet_diff_endpoints]
    exact (isConnected_Ioo (zero_lt_one : (0 : I) < 1)).image _
      (A i).toPath.continuous.continuousOn
  have hinterJ : Disjoint ((A i).toSet \ {a, b}) Ploop.toSet := by
    rw [disjoint_iff_inter_eq_empty, hPset]
    ext q
    constructor
    · intro h
      have hqab : q ∉ ({a, b} : Set V) := h.1.2
      rcases h.2 with hqj | hqk
      · exact hqab ((hmeet i j hji.symm) ▸ ⟨h.1.1, hqj⟩)
      · exact hqab ((hmeet i k hki.symm) ▸ ⟨h.1.1, hqk⟩)
    · intro h
      exact h.elim
  let S : Set (OnePoint V) := (↑) '' ((A i).toSet \ {a, b})
  have hSconn : IsConnected S :=
    hinter_conn.image _ OnePoint.continuous_coe.continuousOn
  have hSsub : S ⊆ ((↑) '' Ploop.toSet : Set (OnePoint V))ᶜ := by
    intro p hp hpJ
    obtain ⟨q, hq, rfl⟩ := (mem_image _ _ _).mp hp
    obtain ⟨q', hqJ, hqe⟩ := (mem_image _ _ _).mp hpJ
    exact hinterJ.notMem_of_mem_left hq (OnePoint.coe_injective hqe ▸ hqJ)
  have hScover : S ⊆ hJ.insideOnePoint ∪ hJ.outsideOnePoint := by
    intro p hp
    rw [hJ.insideOnePoint_union_outsideOnePoint]
    exact hSsub hp
  have hSside : S ⊆ hJ.insideOnePoint ∨ S ⊆ hJ.outsideOnePoint :=
    hSconn.isPreconnected.subset_or_subset hJ.insideOnePoint_isOpen hJ.outsideOnePoint_isOpen
      hJ.insideOnePoint_disjoint_outsideOnePoint hScover
  have hends_i : ({a, b} : Set V) ⊆ (A i).toSet := by
    intro x hx
    rw [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (A i).mem_toSet_of_mem_vertices (A i).first_mem_vertices
    · exact (A i).mem_toSet_of_mem_vertices (A i).last_mem_vertices
  have hends_J : ({a, b} : Set V) ⊆ Ploop.toSet := by
    rw [hPset]
    intro x hx
    rw [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ((A j).mem_toSet_of_mem_vertices (A j).first_mem_vertices)
    · exact Or.inl ((A j).mem_toSet_of_mem_vertices (A j).last_mem_vertices)
  have hΘ : (⋃ t, (A t).toSet) = Ploop.toSet ∪ (A i).toSet := by
    refine subset_antisymm ?_ ?_
    · intro u hu
      obtain ⟨t, ht⟩ := mem_iUnion.mp hu
      obtain rfl | hti := eq_or_ne t i
      · exact Or.inr ht
      · refine Or.inl ?_
        rw [hPset]
        have : t = j ∨ t = k := by
          have htcompl : t ∈ ({i}ᶜ : Set (Fin 3)) := hti
          rwa [hcompl, mem_insert_iff, mem_singleton_iff] at htcompl
        rcases this with rfl | rfl
        · exact Or.inl ht
        · exact Or.inr ht
    · intro u hu
      rcases hu with hPj | hAi
      · rw [hPset] at hPj
        rcases hPj with hj | hk
        · exact mem_iUnion.mpr ⟨j, hj⟩
        · exact mem_iUnion.mpr ⟨k, hk⟩
      · exact mem_iUnion.mpr ⟨i, hAi⟩
  have hsets : ⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (A t).toSet = Ploop.toSet := by
    rw [hcompl, hPset]
    ext u
    constructor
    · intro hu
      obtain ⟨t, ht, hut⟩ := mem_iUnion₂.mp hu
      rw [mem_insert_iff, mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact Or.inl hut
      · exact Or.inr hut
    · intro hu
      rcases hu with hut | hut
      · exact mem_iUnion₂.mpr ⟨j, Or.inl rfl, hut⟩
      · exact mem_iUnion₂.mpr ⟨k, Or.inr rfl, hut⟩
  have hfront : OnePoint.some '' (⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (A t).toSet) =
      OnePoint.some '' Ploop.toSet := by
    rw [hsets]
  have hdisj_of (W : Set (OnePoint V))
      (hWJ : Disjoint W ((↑) '' Ploop.toSet)) (hWS : Disjoint W S) :
      Disjoint W ((↑) '' (⋃ t, (A t).toSet)) := by
    rw [hΘ, image_union, show (A i).toSet = ((A i).toSet \ {a, b}) ∪ {a, b} from
      (sdiff_union_of_subset hends_i).symm]
    rw [image_union]
    refine hWJ.union_right (hWS.union_right (hWJ.mono_right (image_mono hends_J)))
  have hcomp_of {W : Set (OnePoint V)} {w : OnePoint V}
      (hWopen : IsOpen W) (hWconn : IsConnected W)
      (hWfront : frontier W = (↑) '' Ploop.toSet)
      (hWJ : Disjoint W ((↑) '' Ploop.toSet)) (hWS : Disjoint W S)
      (hwW : w ∈ W) :
      w ∈ ((↑) '' (⋃ t, (A t).toSet))ᶜ ∧
        W = connectedComponentIn (((↑) '' (⋃ t, (A t).toSet))ᶜ) w := by
    have hWΘ : Disjoint W ((↑) '' (⋃ t, (A t).toSet)) := hdisj_of W hWJ hWS
    have hwΘ : w ∈ ((↑) '' (⋃ t, (A t).toSet))ᶜ :=
      (subset_compl_iff_disjoint_right.mpr hWΘ) hwW
    refine ⟨hwΘ, ?_⟩
    exact eq_connectedComponentIn_of_frontier_subset hWopen hWconn.isPreconnected hWΘ
      (hWfront.trans_subset (image_mono (hΘ ▸ subset_union_left))) hwW
  have hOutJ : Disjoint hJ.outsideOnePoint ((↑) '' Ploop.toSet) :=
    subset_compl_iff_disjoint_right.mp sdiff_subset
  have hInJ : Disjoint hJ.insideOnePoint ((↑) '' Ploop.toSet) := by
    rw [IsJordanCurve.insideOnePoint]
    exact disjoint_image_of_injective OnePoint.coe_injective
      (subset_compl_iff_disjoint_right.mp hJ.inside_subset_compl)
  rcases hSside with hSin | hSout
  · obtain ⟨hwΘ, hWeq⟩ :=
      hcomp_of hJ.outsideOnePoint_isOpen hJ.outsideOnePoint_isConnected
        hJ.frontier_outsideOnePoint hOutJ
        (hJ.insideOnePoint_disjoint_outsideOnePoint.symm.mono_right hSin)
        hJ.infty_mem_outsideOnePoint
    exact ⟨hJ.outsideOnePoint, OnePoint.infty, hwΘ, hWeq, hJ.outsideOnePoint_isOpen,
      hJ.outsideOnePoint_isConnected, hJ.frontier_outsideOnePoint.trans hfront.symm⟩
  · obtain ⟨w, hw⟩ := hJ.insideOnePoint_isConnected.nonempty
    obtain ⟨hwΘ, hWeq⟩ :=
      hcomp_of hJ.insideOnePoint_isOpen hJ.insideOnePoint_isConnected
        hJ.frontier_insideOnePoint hInJ
        (hJ.insideOnePoint_disjoint_outsideOnePoint.mono_right hSout) hw
    exact ⟨hJ.insideOnePoint, w, hwΘ, hWeq, hJ.insideOnePoint_isOpen,
      hJ.insideOnePoint_isConnected, hJ.frontier_insideOnePoint.trans hfront.symm⟩

/-- Assemble the three candidate regions and prove they are distinct. -/
private theorem exists_candidate_regions
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b}) :
    ∃ W : Fin 3 → Set (OnePoint V),
      (∀ i, IsOpen (W i)) ∧
      (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (∀ i, ∃ w ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ,
        W i = connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) w) ∧
      ∀ i, frontier (W i) =
        (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet := by
  choose W w hw hEq hOpen hConn hFront using fun i ↦
    exists_candidate_region hab A hsimple hmeet i
  refine ⟨W, hOpen, hConn, ?_, fun i ↦ ⟨w i, hw i, hEq i⟩, hFront⟩
  intro i j hij
  have hne : W i ≠ W j := by
    intro hWW
    have hsa : (A i).IsSimpleArcOrLoop :=
      Or.inl ⟨hsimple i, (A i).length_pos_of_ne hab⟩
    have hinter : ((A i).toSet \ {a, b}).Nonempty := by
      rw [hsa.toSet_diff_endpoints]
      exact (nonempty_Ioo.2 (zero_lt_one : (0 : I) < 1)).image _
    obtain ⟨q, hq⟩ := hinter
    have hqj : OnePoint.some q ∈ frontier (W j) := by
      rw [hFront j]
      exact ⟨q, mem_iUnion₂.mpr ⟨i, hij, hq.1⟩, rfl⟩
    have hqi : OnePoint.some q ∉ frontier (W i) := by
      rw [hFront i]
      intro hmem
      obtain ⟨q', hunion, hqe⟩ := hmem
      have heq : q = q' := OnePoint.coe_injective hqe.symm
      subst q'
      obtain ⟨t, hti, htA⟩ := mem_iUnion₂.mp hunion
      exact hq.2 ((hmeet i t (Ne.symm hti)) ▸ ⟨hq.1, htA⟩)
    rw [hWW] at hqi
    exact hqi hqj
  rw [hEq i, hEq j, disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzi hzj
  apply hne
  rw [hEq i, hEq j]
  have hi := connectedComponentIn_eq (x := w i) (y := z) hzi
  have hj := connectedComponentIn_eq (x := w j) (y := z) hzj
  exact hi.trans hj.symm

/-! ### Local exhaustion of an arbitrary global component -/

/-- A complement component whose frontier reaches a common endpoint is one of the three candidate
components. -/
private theorem component_eq_candidate_of_endpoint_frontier
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b})
    (W : Fin 3 → Set (OnePoint V))
    (hWcomp : ∀ i, ∃ w ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ,
      W i = connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) w)
    (hWdisj : Pairwise fun i j ↦ Disjoint (W i) (W j))
    (hWfront : ∀ i, frontier (W i) =
      (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet)
    {z : OnePoint V} (_hz : z ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ)
    {q : V} (hqend : q = a ∨ q = b)
    (hqfr : (q : OnePoint V) ∈
      frontier (connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z)) :
    ∃ i, connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z = W i := by
  obtain ⟨ρ, hρ, _, Y, hYcard, hYsph, hstar⟩ :=
    exists_endpoint_star_three hab A hsimple hmeet q hqend one_pos
  have hYne : Y.Nonempty := Finset.card_pos.mp (by rw [hYcard]; norm_num)
  have hqball : q ∈ ball q ρ := mem_ball_self hρ
  have hqfront (i : Fin 3) : (q : OnePoint V) ∈ frontier (W i) := by
    rw [hWfront i]
    refine ⟨q, ?_, rfl⟩
    have hne : i + 1 ≠ i := fun h ↦
      Fin.zero_ne_one.symm (add_left_cancel (h.trans (add_zero i).symm))
    refine mem_iUnion₂.mpr ⟨i + 1, hne, ?_⟩
    rcases hqend with rfl | rfl
    · exact (A (i + 1)).mem_toSet_of_mem_vertices (A (i + 1)).first_mem_vertices
    · exact (A (i + 1)).mem_toSet_of_mem_vertices (A (i + 1)).last_mem_vertices
  have hsec : ∀ i, ∃ C ∈ sectors q ρ Y, OnePoint.some '' C ⊆ W i := by
    intro i
    obtain ⟨wi, _, hWi⟩ := hWcomp i
    have hfr : (q : OnePoint V) ∈
        frontier (connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) wi) := by
      rw [← hWi]
      exact hqfront i
    obtain ⟨C, hC, hsub⟩ :=
      exists_sector_subset_connectedComponentIn hYne hstar hqball hfr
    refine ⟨C, hC, ?_⟩
    rw [hWi]
    exact hsub
  choose C hCmem hCsub using hsec
  have hCpair : Pairwise fun i j ↦ C i ≠ C j := by
    intro i j hij hCeq
    have hne : (OnePoint.some '' C i : Set (OnePoint V)).Nonempty :=
      (isConnected_of_mem_sectors (hCmem i)).nonempty.image _
    obtain ⟨p, hp⟩ := hne
    exact (hWdisj hij).notMem_of_mem_left (hCsub i hp) (hCsub j (hCeq ▸ hp))
  have hCinj : Function.Injective C := fun i j h ↦ by_contra fun hij ↦ hCpair hij h
  obtain ⟨C0, hC0, hC0sub⟩ :=
    exists_sector_subset_connectedComponentIn hYne hstar hqball hqfr
  have hrange : Set.range C ⊆ sectors q ρ Y := by
    rintro s ⟨i, hi⟩
    rw [← hi]
    exact hCmem i
  have hnC : (Set.range C).ncard = 3 := by
    rw [ncard_range_of_injective hCinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hnS : (sectors q ρ Y).ncard = 3 := by
    rw [ncard_sectors hρ hYne hYsph, hYcard]
  have hfin : (sectors q ρ Y).Finite := by
    refine finite_of_ncard_pos ?_
    rw [hnS]; norm_num
  have heq : Set.range C = sectors q ρ Y :=
    eq_of_subset_of_ncard_le hrange (le_of_eq (hnS.trans hnC.symm)) hfin
  have hC0range : C0 ∈ Set.range C := heq.symm ▸ hC0
  obtain ⟨i, hi⟩ := hC0range
  refine ⟨i, ?_⟩
  have hinter : (OnePoint.some '' C0 ∩ W i).Nonempty := by
    have hne : (OnePoint.some '' C0).Nonempty :=
      (isConnected_of_mem_sectors hC0).nonempty.image _
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, hCsub i (hi ▸ hp)⟩
  obtain ⟨p, hp0, hpW⟩ := hinter
  obtain ⟨wi, _, hWi⟩ := hWcomp i
  rw [hWi]
  have hpK := hC0sub hp0
  have hpWi : p ∈ connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) wi := by
    rw [← hWi]
    exact hpW
  exact (connectedComponentIn_eq (x := z) (y := p) hpK).trans
    (connectedComponentIn_eq (x := wi) (y := p) hpWi).symm

/-- A complement component whose frontier reaches the interior of one arm is one of the two
candidate components incident with that arm. -/
private theorem component_eq_candidate_of_arm_frontier
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b})
    (W : Fin 3 → Set (OnePoint V))
    (hWcomp : ∀ i, ∃ w ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ,
      W i = connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) w)
    (hWdisj : Pairwise fun i j ↦ Disjoint (W i) (W j))
    (hWfront : ∀ i, frontier (W i) =
      (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet)
    {z : OnePoint V} (_hz : z ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ)
    (i : Fin 3) {q : V} (hqarm : q ∈ (A i).toSet \ {a, b})
    (hqfr : (q : OnePoint V) ∈
      frontier (connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z)) :
    ∃ j, connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z = W j := by
  obtain ⟨ρ, hρ, _, Y, hYcard, hYsph, hstar⟩ :=
    exists_arm_interior_star_two hab A hsimple hmeet i hqarm one_pos
  have hYne : Y.Nonempty := Finset.card_pos.mp (by rw [hYcard]; norm_num)
  have hqball : q ∈ ball q ρ := mem_ball_self hρ
  have hqfront (j : {j : Fin 3 // j ≠ i}) : (q : OnePoint V) ∈ frontier (W j.1) := by
    rw [hWfront j.1]
    refine ⟨q, ?_, rfl⟩
    exact mem_iUnion₂.mpr ⟨i, j.2.symm, hqarm.1⟩
  have hsec : ∀ j : {j : Fin 3 // j ≠ i},
      ∃ C ∈ sectors q ρ Y, OnePoint.some '' C ⊆ W j.1 := by
    intro j
    obtain ⟨wj, _, hWj⟩ := hWcomp j.1
    have hfr : (q : OnePoint V) ∈
        frontier (connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) wj) := by
      rw [← hWj]
      exact hqfront j
    obtain ⟨C, hC, hsub⟩ :=
      exists_sector_subset_connectedComponentIn hYne hstar hqball hfr
    refine ⟨C, hC, ?_⟩
    rw [hWj]
    exact hsub
  choose C hCmem hCsub using hsec
  have hCpair : Pairwise fun (j k : {j : Fin 3 // j ≠ i}) ↦ C j ≠ C k := by
    intro j k hjk hCeq
    have hne : (OnePoint.some '' C j : Set (OnePoint V)).Nonempty :=
      (isConnected_of_mem_sectors (hCmem j)).nonempty.image _
    obtain ⟨p, hp⟩ := hne
    exact (hWdisj (Subtype.coe_ne_coe.mpr hjk)).notMem_of_mem_left
      (hCsub j hp) (hCsub k (hCeq ▸ hp))
  have hCinj : Function.Injective C := fun j k h ↦ by_contra fun hjk ↦ hCpair hjk h
  obtain ⟨C0, hC0, hC0sub⟩ :=
    exists_sector_subset_connectedComponentIn hYne hstar hqball hqfr
  have hrange : Set.range C ⊆ sectors q ρ Y := by
    rintro s ⟨j, hj⟩
    rw [← hj]
    exact hCmem j
  have hι : Fintype.card {j : Fin 3 // j ≠ i} = 2 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hnC : (Set.range C).ncard = 2 := by
    rw [ncard_range_of_injective hCinj, Nat.card_eq_fintype_card, hι]
  have hnS : (sectors q ρ Y).ncard = 2 := by
    rw [ncard_sectors hρ hYne hYsph, hYcard]
  have hfin : (sectors q ρ Y).Finite := by
    refine finite_of_ncard_pos ?_
    rw [hnS]; norm_num
  have heq : Set.range C = sectors q ρ Y :=
    eq_of_subset_of_ncard_le hrange (le_of_eq (hnS.trans hnC.symm)) hfin
  have hC0range : C0 ∈ Set.range C := heq.symm ▸ hC0
  obtain ⟨j, hj⟩ := hC0range
  refine ⟨j.1, ?_⟩
  have hinter : (OnePoint.some '' C0 ∩ W j.1).Nonempty := by
    have hne : (OnePoint.some '' C0).Nonempty :=
      (isConnected_of_mem_sectors hC0).nonempty.image _
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, hCsub j (hj ▸ hp)⟩
  obtain ⟨p, hp0, hpW⟩ := hinter
  obtain ⟨wj, _, hWj⟩ := hWcomp j.1
  rw [hWj]
  have hpK := hC0sub hp0
  have hpWj : p ∈ connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) wj := by
    rw [← hWj]
    exact hpW
  exact (connectedComponentIn_eq (x := z) (y := p) hpK).trans
    (connectedComponentIn_eq (x := wj) (y := p) hpWj).symm

/-- Every component of the theta complement is one of the three JCT candidates. -/
private theorem component_eq_candidate
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b})
    (W : Fin 3 → Set (OnePoint V))
    (hWcomp : ∀ i, ∃ w ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ,
      W i = connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) w)
    (hWdisj : Pairwise fun i j ↦ Disjoint (W i) (W j))
    (hWfront : ∀ i, frontier (W i) =
      (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet)
    {z : OnePoint V} (hz : z ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ) :
    ∃ i, connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z = W i := by
  let S : Set (OnePoint V) := (↑) '' ⋃ k, (A k).toSet
  have hSne : S.Nonempty :=
    ⟨a, ⟨a, mem_iUnion.mpr ⟨0, (A 0).mem_toSet_of_mem_vertices (A 0).first_mem_vertices⟩, rfl⟩⟩
  have hTcompact : IsCompact (⋃ k, (A k).toSet) := isCompact_iUnion fun k ↦ (A k).isCompact_toSet
  have hSclosed : IsClosed S :=
    OnePoint.isClosed_image_coe.mpr ⟨hTcompact.isClosed, hTcompact⟩
  let : Nontrivial V := ⟨⟨a, b, hab⟩⟩
  let : PreconnectedSpace V :=
    ⟨((convex_univ (𝕜 := ℝ)).isPathConnected ⟨a, mem_univ a⟩).isConnected.isPreconnected⟩
  let : PreconnectedSpace (OnePoint V) :=
    (inferInstance : ConnectedSpace (OnePoint V)).toPreconnectedSpace
  obtain ⟨q1, hq1fr⟩ := frontier_connectedComponentIn_compl_nonempty (S := S) hSne hz
  have hq1S : q1 ∈ S := hSclosed.frontier_connectedComponentIn_compl_subset hq1fr
  obtain ⟨q, hqT, rfl⟩ := hq1S
  obtain ⟨i, hi⟩ := mem_iUnion.mp hqT
  by_cases ha : q = a
  · exact component_eq_candidate_of_endpoint_frontier hab A hsimple hmeet W hWcomp hWdisj
      hWfront hz (Or.inl ha) hq1fr
  by_cases hb : q = b
  · exact component_eq_candidate_of_endpoint_frontier hab A hsimple hmeet W hWcomp hWdisj
      hWfront hz (Or.inr hb) hq1fr
  have hqarm : q ∈ (A i).toSet \ {a, b} := ⟨hi, by simp [ha, hb]⟩
  exact component_eq_candidate_of_arm_frontier hab A hsimple hmeet W hWcomp hWdisj hWfront hz
    i hqarm hq1fr

/-- **Theta-curve theorem.** Three embedded polygonal arcs with the same two endpoints, meeting
nowhere else, cut the sphere into exactly three regions.  The region omitted by index `i` is bounded
by the other two arcs. -/
theorem exists_three_regions_theta (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b}) :
    ∃ W : Fin 3 → Set (OnePoint V),
      (∀ i, IsOpen (W i)) ∧
      (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (⋃ i, W i) = ((↑) '' (⋃ i, (A i).toSet))ᶜ ∧
      ∀ i, frontier (W i) =
        (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet := by
  obtain ⟨W, hWopen, hWconn, hWdisj, hWcomp, hWfront⟩ :=
    exists_candidate_regions hab A hsimple hmeet
  refine ⟨W, hWopen, hWconn, hWdisj, ?_, hWfront⟩
  apply subset_antisymm
  · intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    obtain ⟨w, hw, hWi⟩ := hWcomp i
    rw [hWi] at hzi
    exact connectedComponentIn_subset _ _ hzi
  · intro z hz
    obtain ⟨i, hi⟩ :=
      component_eq_candidate hab A hsimple hmeet W hWcomp hWdisj hWfront hz
    have hzi : z ∈ W i := by
      rw [← hi]
      exact mem_connectedComponentIn hz
    exact mem_iUnion.mpr ⟨i, hzi⟩

end

end PolygonalPath
