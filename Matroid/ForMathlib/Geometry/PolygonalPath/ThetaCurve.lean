module

public import Matroid.ForMathlib.Geometry.Polygon.JordanCurve
public import Matroid.ForMathlib.Geometry.PolygonalPath.LocalStar
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

namespace PolygonalPath

public noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] {a b : V}

/-! ### Local theta structure -/

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
  /-
  At `a`, shrink below:
  * the radius from `IsSegmentFigure.exists_radius`,
  * all three `exists_ball_inter_subset_firstSegment` radii,
  * `dist a b`, and
  * `ε`.

  For the lower cardinality bound use
      U i := (A i).toSet ∩ closedBall a ρ
  rather than `U i := (A i).toSet`.
  This is essential: the unlocalized paths still intersect at `b`.

  The `b` case is the same argument after reversing all three paths.
  -/
  sorry

/-- At an interior point of one arm, sufficiently small neighborhoods of the whole theta set have
exactly two radial germs. -/
private theorem exists_arm_interior_star_two
    (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b})
    (i : Fin 3) {q : V} (hq : q ∈ (A i).toSet \ {a, b})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ε ∧
      ∃ Y : Finset V, Y.card = 2 ∧
        (Y : Set V) ⊆ sphere q ρ ∧
        closedBall q ρ ∩ (⋃ j, (A j).toSet) =
          {q} ∪ ⋃ y ∈ Y, segment ℝ q y := by
  /-
  Apply `hsimple i |>.exists_local_star_two` to arm `i`.
  The other two polygonal arcs are closed and do not contain `q`; use a positive-distance
  neighborhood avoiding them, then shrink with the arbitrary `ε` parameter of the local-star
  theorem.  At that scale the whole theta set agrees with arm `i`.
  -/
  sorry

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
  /-
  * The two arms with index different from `i` concatenate (one reversed) to a simple loop.
  * Apply polygonal JCT on `OnePoint V`.
  * The omitted arm has nonempty connected interior and is disjoint from that loop, hence lies in
    one JCT side.  Choose the other side.
  * That side is contained in the theta complement.
  * Conversely the theta-complement component of any point in the chosen side lies in the same JCT
    side, because the theta complement is contained in the loop complement.
    Connected-component maximality gives equality.
  -/
  sorry

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
  /-
  Choose the component from `exists_candidate_region` for each `i`.

  For `i ≠ j`, distinguish the two components by their frontiers: an interior point of arm `i`
  belongs to the frontier of the candidate omitting `j`, but not to the frontier of the candidate
  omitting `i`.  Distinct connected components are disjoint.
  -/
  sorry

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
    {z : OnePoint V} (hz : z ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ)
    {q : V} (hqend : q = a ∨ q = b)
    (hqfr : (q : OnePoint V) ∈
      frontier (connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z)) :
    ∃ i, connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z = W i := by
  /-
  Use `exists_endpoint_star_three` and `ncard_sectors`: there are exactly three local sectors.
  `exists_sector_subset_connectedComponentIn` assigns one sector to the unknown component and one
  to each candidate whose frontier contains the endpoint.  Pairwise disjoint candidate components
  occupy distinct sectors, so the three candidates exhaust all sectors.  The unknown component
  shares a sector with one candidate and hence is the same global connected component.
  -/
  sorry

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
    {z : OnePoint V} (hz : z ∈ ((↑) '' (⋃ k, (A k).toSet))ᶜ)
    (i : Fin 3) {q : V} (hqarm : q ∈ (A i).toSet \ {a, b})
    (hqfr : (q : OnePoint V) ∈
      frontier (connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z)) :
    ∃ j, connectedComponentIn (((↑) '' (⋃ k, (A k).toSet))ᶜ) z = W j := by
  /-
  `exists_arm_interior_star_two` gives exactly two local sectors.  From `hWfront`, exactly the two
  candidates whose boundary contains arm `i` reach `q`; sector extraction puts a distinct sector
  in each.  Hence they exhaust the two sectors.  The unknown component also contains a sector and
  must coincide with one of those candidates.
  -/
  sorry

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
  /-
  The theta image is nonempty and closed.  Apply
  `frontier_connectedComponentIn_compl_nonempty` and
  `IsClosed.frontier_connectedComponentIn_compl_subset` to choose a frontier point `q` on theta.

  Pairwise intersection of the arms implies that `q` is either `a`, `b`, or an interior point of a
  unique arm.  Dispatch to the two preceding local-classification lemmas.  This is intentionally a
  local case split at one frontier point; there is no global "propagate the face to an endpoint"
  lemma.
  -/
  sorry

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
