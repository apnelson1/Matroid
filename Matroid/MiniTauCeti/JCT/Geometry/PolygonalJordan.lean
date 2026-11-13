module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.SetTheory.Cardinal.NatCard
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalCrossing
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.RayCrossing
public import Matroid.MiniTauCeti.JCT.Geometry.SegmentFigure.Topology
public import Matroid.MiniTauCeti.JCT.Geometry.PrimitiveLink
public import Matroid.MiniTauCeti.JCT.Geometry.StarComponents
public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink.Crossing
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.CompactParametrization

/-!
# The polygonal Jordan curve theorem

A polygonal circuit has exactly two complementary components, and every complementary component
has the whole circuit as its frontier. The public statements use `IsCircuit` and
`IsSegmentFigure`. The proofs choose a simple loop internally.

The upper bound propagates frontier membership through two-radius stars, then counts sectors
at one fixed point. For the lower bound, ray-crossing parity is locally constant on the
complement, but both a one-crossing ray and a ray missing the figure exist. Thus their starting
points lie in distinct components. The parity argument uses evenness of boundary crossings,
not an existing Jordan separation theorem.

Finiteness is also stated separately: an upper bound on `Nat.card` alone would not exclude
infinitely many components. The present result does not classify boundedness of the components.
-/

@[expose] public section

attribute [local instance] Complex.finrank_real_complex_fact

open Set Metric Topology Function

namespace Path.IsSimpleLoop

variable {x z : ℂ} {P : Path x x}

/-- Every complementary component of a polygonal primitive loop has the whole loop as frontier. -/
private theorem frontier_connectedComponentIn_compl_eq (hP : P.IsSimpleLoop)
    (hpoly : IsSegmentFigure (range P)) (hz : z ∉ (range P)) :
    frontier (connectedComponentIn (range P)ᶜ z) = (range P) := by
  have hL := hP.isPrimitive.isPrimitiveLink
  have hclosed : IsClosed (range P) := hL.isClosed
  have hsub := hclosed.frontier_connectedComponentIn_compl_subset (x := z)
  let A : Set (range P) := Subtype.val ⁻¹' frontier (connectedComponentIn (range P)ᶜ z)
  have hAcl : IsClosed A := isClosed_frontier.preimage continuous_subtype_val
  have hAne : A.Nonempty := by
    obtain ⟨p, hp⟩ := frontier_connectedComponentIn_compl_nonempty hL.isConnected.nonempty hz
    exact ⟨⟨p, hsub hp⟩, hp⟩
  have hAo : IsOpen A := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨r, hr, hstar⟩ := hL.exists_local_star_two hpoly p.2 (Or.inl rfl)
    obtain ⟨Y, hcard, hY, hstar⟩ := hstar r hr le_rfl
    have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨C, hC, hCK⟩ := exists_sector_subset_connectedComponentIn_compl
      hYne hstar (mem_ball_self hr) hp
    refine ⟨Subtype.val ⁻¹' ball p.1 r, ?_,
      isOpen_ball.preimage continuous_subtype_val, mem_ball_self hr⟩
    intro q hq
    refine ⟨closure_mono hCK
      (ball_inter_subset_closure_sector_of_card_eq_two hr hY hcard hstar hC ⟨hq, q.2⟩), ?_⟩
    exact fun h ↦ connectedComponentIn_subset (range P)ᶜ z (interior_subset h) q.2
  let : ConnectedSpace (range P) := isConnected_iff_connectedSpace.mp hL.isConnected
  have hA : A = univ := IsClopen.eq_univ ⟨hAcl, hAo⟩ hAne
  refine hsub.antisymm fun p hp ↦ ?_
  have : (⟨p, hp⟩ : (range P)) ∈ A := hA ▸ mem_univ _
  exact this

private theorem finite_card_connectedComponents_compl (hP : P.IsSimpleLoop)
    (hpoly : IsSegmentFigure (range P)) :
    Finite (ConnectedComponents ↥(range P)ᶜ) ∧ Nat.card (ConnectedComponents ↥(range P)ᶜ) ≤ 2 := by
  have hL := hP.isPrimitive.isPrimitiveLink
  classical
  obtain ⟨r, hr, hstar⟩ := hL.exists_local_star_two hpoly hL.left_mem (Or.inl rfl)
  obtain ⟨Y, hcard, hY, hstar⟩ := hstar r hr le_rfl
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hn : (sectors x r Y).ncard = 2 := by rw [ncard_sectors hr hYne hY, hcard]
  have hfin : (sectors x r Y).Finite := finite_of_ncard_ne_zero (by omega)
  let : Finite ↥(sectors x r Y) := hfin.to_subtype
  have hCS (C : ↥(sectors x r Y)) : C.1 ⊆ (range P)ᶜ := by
    intro p hp hpS
    have hpD := subset_diskMinusRadii_of_mem_sectors C.2 hp
    have hpstar : p ∈ ({x} ∪ ⋃ y ∈ Y, segment ℝ x y : Set ℂ) :=
      hstar ▸ ⟨ball_subset_closedBall hpD.1, hpS⟩
    apply hpD.2
    rcases hpstar with rfl | hrad
    · obtain ⟨y, hy⟩ := hYne
      exact mem_iUnion₂.mpr ⟨y, hy, left_mem_segment ℝ _ y⟩
    · exact hrad
  have hne (C : ↥(sectors x r Y)) : C.1.Nonempty :=
    (isConnected_of_mem_sectors C.2).nonempty
  let point (C : ↥(sectors x r Y)) : ↥(range P)ᶜ := ⟨(hne C).choose, hCS C (hne C).choose_spec⟩
  let f : ↥(sectors x r Y) → ConnectedComponents ↥(range P)ᶜ :=
    fun C ↦ ConnectedComponents.mk (point C)
  have hf : Surjective f := by
    intro k
    obtain ⟨w, rfl⟩ := ConnectedComponents.surjective_coe k
    have hxfr : x ∈ frontier (connectedComponentIn (range P)ᶜ w.1) := by
      rw [hP.frontier_connectedComponentIn_compl_eq hpoly w.2]
      exact hL.left_mem
    obtain ⟨C, hC, hCK⟩ := exists_sector_subset_connectedComponentIn_compl
      hYne hstar (mem_ball_self hr) hxfr
    refine ⟨⟨C, hC⟩, ?_⟩
    apply ConnectedComponents.coe_eq_coe'.2
    have hpK := hCK (hne ⟨C, hC⟩).choose_spec
    rw [connectedComponentIn_eq_image w.2] at hpK
    obtain ⟨t, ht, heq⟩ := hpK
    exact (show t = point ⟨C, hC⟩ from Subtype.ext heq) ▸ ht
  exact ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans (by
    simpa only [Nat.card_coe_set_eq] using hn.le)⟩

/-- A polygonal primitive loop has finitely many complementary components. -/
private theorem finite_connectedComponents_compl (hP : P.IsSimpleLoop)
    (hpoly : IsSegmentFigure (range P)) : Finite (ConnectedComponents ↥(range P)ᶜ) :=
  (hP.finite_card_connectedComponents_compl hpoly).1

/-- A polygonal primitive loop has at most two complementary components.
Use `finite_connectedComponents_compl` as well: `Nat.card` is zero on infinite types. -/
private theorem card_connectedComponents_compl_le_two (hP : P.IsSimpleLoop)
    (hpoly : IsSegmentFigure (range P)) : Nat.card (ConnectedComponents ↥(range P)ᶜ) ≤ 2 :=
  (hP.finite_card_connectedComponents_compl hpoly).2

/-- **Polygonal Jordan curve theorem.** The complement of a polygonal primitive loop in the
complex plane has exactly two connected components. Together with
`frontier_connectedComponentIn_compl_eq`, each of these components has frontier `(range P)`. -/
private theorem card_connectedComponents_compl_eq_two (hP : P.IsSimpleLoop)
    (hS : IsSegmentFigure (range P)) : Nat.card (ConnectedComponents ↥(range P)ᶜ) = 2 := by
  have hL := hP.isPrimitive.isPrimitiveLink
  let : Finite (ConnectedComponents ↥(range P)ᶜ) := hP.finite_connectedComponents_compl hS
  obtain ⟨v, _, htrans, p, _, ε, hε, hinterval⟩ :=
    Complex.orientation.exists_direction_singleton_interval hS hL.infinite
  obtain ⟨d, hd⟩ := exists_between hε
  let a := p - d • v
  have ha : a ∉ (range P) := (hinterval d hd).1
  have haCross : Complex.rayCrossings (range P) a v = {p} := (hinterval d hd).2
  obtain ⟨b, hb, hbCross⟩ :=
    Complex.orientation.exists_rayCrossings_eq_empty hL.isCompact.isBounded v
  change Complex.rayCrossings (range P) b v = ∅ at hbCross
  have hne : ConnectedComponents.mk (⟨a, ha⟩ : ↥(range P)ᶜ) ≠
      ConnectedComponents.mk (⟨b, hb⟩ : ↥(range P)ᶜ) := by
    intro heq
    have hmem : (⟨a, ha⟩ : ↥(range P)ᶜ) ∈ connectedComponent (⟨b, hb⟩ : ↥(range P)ᶜ) :=
      ConnectedComponents.coe_eq_coe'.mp heq
    have he := (hP.isLocallyConstant_rayCrossings_parity hS htrans).apply_eq_of_isPreconnected
      isPreconnected_connectedComponent hmem mem_connectedComponent
    change (Complex.rayCrossings (range P) a v).ncard % 2 =
      (Complex.rayCrossings (range P) b v).ncard % 2 at he
    rw [haCross, hbCross, ncard_singleton, ncard_empty] at he
    norm_num at he
  let : Nontrivial (ConnectedComponents ↥(range P)ᶜ) :=
    ⟨⟨ConnectedComponents.mk ⟨a, ha⟩, ConnectedComponents.mk ⟨b, hb⟩, hne⟩⟩
  exact (hP.card_connectedComponents_compl_le_two hS).antisymm Finite.one_lt_card

private theorem exists_complement_regions_complex (hP : P.IsSimpleLoop)
    (hpoly : IsSegmentFigure (range P)) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range P)ᶜ ∧ frontier U = range P ∧ frontier V = range P :=
  hP.isPrimitive.isPrimitiveLink.isClosed.isOpen_compl
    |>.exists_two_regions_of_card_connectedComponents_eq_two
      (hP.card_connectedComponents_compl_eq_two hpoly)
      (fun _ hp ↦ hP.frontier_connectedComponentIn_compl_eq hpoly hp)

/-- A polygonal simple loop separates a real normed plane into two open connected regions
with the loop as their common frontier. -/
private theorem exists_complement_regions {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] {x : E} {P : Path x x}
    (hP : P.IsSimpleLoop) (hpoly : IsSegmentFigure (range P)) :
    ∃ U V : Set E, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range P)ᶜ ∧ frontier U = range P ∧ frontier V = range P := by
  let : FiniteDimensional ℝ E := .of_fact_finrank_eq_two
  let e : E ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofFinrankEq
    ((Fact.out : Module.finrank ℝ E = 2).trans Complex.finrank_real_complex.symm)
  let Q := P.map' e.continuous.continuousOn
  have hQ : Q.IsSimpleLoop :=
    (hP.isPrimitive.map e.continuous.continuousOn e.injective.injOn).isSimpleLoop
  have hrange : range Q = e '' range P := range_comp e P
  have hpolyQ : IsSegmentFigure (range Q) := by
    rw [hrange]
    exact hpoly.image e.toLinearMap.toAffineMap
  obtain ⟨U, V, hU, hV, hcU, hcV, hd, hcover, hfU, hfV⟩ :=
    hQ.exists_complement_regions_complex hpolyQ
  refine ⟨e ⁻¹' U, e ⁻¹' V, hU.preimage e.continuous, hV.preimage e.continuous,
    e.toHomeomorph.isConnected_preimage.mpr hcU, e.toHomeomorph.isConnected_preimage.mpr hcV,
    hd.preimage e, ?_, ?_, ?_⟩
  · rw [← preimage_union, hcover, preimage_compl, hrange, e.injective.preimage_image]
  · change frontier (e.toHomeomorph ⁻¹' U) = range P
    rw [← e.toHomeomorph.preimage_frontier, hfU]
    simpa only [hrange, ContinuousLinearEquiv.coe_toHomeomorph] using
      e.injective.preimage_image (range P)
  · change frontier (e.toHomeomorph ⁻¹' V) = range P
    rw [← e.toHomeomorph.preimage_frontier, hfV]
    simpa only [hrange, ContinuousLinearEquiv.coe_toHomeomorph] using
      e.injective.preimage_image (range P)

variable {p : ℂ}

/-- Every neighborhood of a point of a polygonal primitive loop contains a ball whose
intersection with each open side of a complementary component is connected. -/
private theorem exists_ball_connected_sides (hP : P.IsSimpleLoop)
    (hpoly : IsSegmentFigure (range P))
    (hz : z ∉ (range P)) (hp : p ∈ (range P)) {N : Set ℂ} (hN : N ∈ 𝓝 p) :
    ∃ r > 0, ball p r ⊆ N ∧
      IsConnected (ball p r ∩ interior (connectedComponentIn (range P)ᶜ z)) ∧
      IsConnected (ball p r ∩ interior (connectedComponentIn (range P)ᶜ z)ᶜ) := by
  have hL := hP.isPrimitive.isPrimitiveLink
  classical
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨r, hr, hrε, Y, hcard, hY, hstar⟩ :=
    hL.exists_local_star_two_le hpoly hp (Or.inl rfl) hε
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hn : (sectors p r Y).ncard = 2 := by rw [ncard_sectors hr hYne hY, hcard]
  have hfin : (sectors p r Y).Finite := finite_of_ncard_ne_zero (by omega)
  obtain ⟨k, hk, _⟩ := (Nat.card_eq_two_iff'
    (ConnectedComponents.mk (⟨z, hz⟩ : ↥(range P)ᶜ))).mp
    (hP.card_connectedComponents_compl_eq_two hpoly)
  obtain ⟨w, rfl⟩ := ConnectedComponents.surjective_coe k
  let U := connectedComponentIn (range P)ᶜ z
  let V := connectedComponentIn (range P)ᶜ w.1
  have hUV : Disjoint U V := by
    apply disjoint_left.mpr
    intro q hqU hqV
    have heq : U = V := (connectedComponentIn_eq hqU).trans (connectedComponentIn_eq hqV).symm
    have hwU : w.1 ∈ U := heq ▸ mem_connectedComponentIn w.2
    change w.1 ∈ connectedComponentIn (range P)ᶜ z at hwU
    rw [connectedComponentIn_eq_image (show z ∈ (range P)ᶜ from hz)] at hwU
    obtain ⟨v, hv, he⟩ := hwU
    exact hk (ConnectedComponents.coe_eq_coe'.mpr ((Subtype.ext he : v = w) ▸ hv))
  have hpU : p ∈ frontier U := by
    rw [hP.frontier_connectedComponentIn_compl_eq hpoly hz]
    exact hp
  have hpV : p ∈ frontier V := by
    rw [hP.frontier_connectedComponentIn_compl_eq hpoly w.2]
    exact hp
  obtain ⟨A, hA, hAU⟩ := exists_sector_subset_connectedComponentIn_compl
    hYne hstar (mem_ball_self hr) hpU
  obtain ⟨B, hB, hBV⟩ := exists_sector_subset_connectedComponentIn_compl
    hYne hstar (mem_ball_self hr) hpV
  have hAB : A ≠ B := by
    intro he
    obtain ⟨q, hq⟩ := (isConnected_of_mem_sectors hA).nonempty
    exact hUV.notMem_of_mem_left (hAU hq) (hBV (he ▸ hq))
  have hsectors : sectors p r Y = {A, B} :=
    (eq_of_subset_of_ncard_le (pair_subset hA hB) (by rw [hn, ncard_pair hAB]) hfin).symm
  have hdisk : diskMinusRadii p r Y = ball p r ∩ (range P)ᶜ := by
    ext q
    constructor
    · rintro ⟨hqb, hqr⟩
      refine ⟨hqb, fun hqS ↦ ?_⟩
      have hqstar : q ∈ ({p} ∪ ⋃ y ∈ Y, segment ℝ p y : Set ℂ) :=
        hstar ▸ ⟨ball_subset_closedBall hqb, hqS⟩
      apply hqr
      rcases hqstar with rfl | hrad
      · obtain ⟨y, hy⟩ := hYne
        exact mem_iUnion₂.mpr ⟨y, hy, left_mem_segment ℝ _ y⟩
      · exact hrad
    · rintro ⟨hqb, hqS⟩
      refine ⟨hqb, fun hqr ↦ hqS ?_⟩
      exact (show q ∈ closedBall p r ∩ (range P) from hstar.symm ▸ Or.inr hqr).2
  have hcover : ball p r ∩ (range P)ᶜ = A ∪ B := by
    rw [← hdisk, ← sUnion_sectors, hsectors, sUnion_pair]
  have hBo : B ⊆ interior Uᶜ :=
    interior_maximal (fun q hq ↦ hUV.notMem_of_mem_right (hBV hq))
      (isOpen_of_mem_sectors hB)
  have hUo : IsOpen U := hL.isClosed.isOpen_compl.connectedComponentIn
  have hfirst : ball p r ∩ interior U = A := by
    rw [hUo.interior_eq]
    apply Subset.antisymm
    · intro q hq
      have hqab : q ∈ A ∪ B := hcover ▸ ⟨hq.1, connectedComponentIn_subset _ _ hq.2⟩
      exact hqab.resolve_right (fun hqB ↦ hUV.notMem_of_mem_left hq.2 (hBV hqB))
    · intro q hq
      exact ⟨(subset_diskMinusRadii_of_mem_sectors hA hq).1, hAU hq⟩
  have hsecond : ball p r ∩ interior Uᶜ = B := by
    apply Subset.antisymm
    · intro q hq
      have hqS : q ∉ (range P) := by
        rw [← hP.frontier_connectedComponentIn_compl_eq hpoly hz]
        exact fun h ↦ disjoint_interior_frontier.notMem_of_mem_left hq.2
          (frontier_compl (s := U) ▸ h)
      have hqab : q ∈ A ∪ B := hcover ▸ ⟨hq.1, hqS⟩
      exact hqab.resolve_left (fun hqA ↦ interior_subset hq.2 (hAU hqA))
    · intro q hq
      exact ⟨(subset_diskMinusRadii_of_mem_sectors hB hq).1, hBo hq⟩
  refine ⟨r, hr, (ball_subset_ball hrε).trans hεN, ?_, ?_⟩
  · change IsConnected (ball p r ∩ interior U)
    rw [hfirst]
    exact isConnected_of_mem_sectors hA
  · change IsConnected (ball p r ∩ interior Uᶜ)
    rw [hsecond]
    exact isConnected_of_mem_sectors hB

end Path.IsSimpleLoop

namespace IsCircuit

variable {C : Set ℂ} {z p : ℂ}

/-- A polygonal circuit is the frontier of every complementary component. -/
theorem frontier_connectedComponentIn_compl_of_isSegmentFigure (hC : IsCircuit C)
    (hpoly : IsSegmentFigure C) (hz : z ∉ C) :
    frontier (connectedComponentIn Cᶜ z) = C := by
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨P, hP, rfl⟩ := hC.exists_isSimpleLoop hpoly.isCompact hx
  exact hP.frontier_connectedComponentIn_compl_eq hpoly hz

/-- The complement of a polygonal circuit has finitely many components. -/
theorem finite_connectedComponents_compl_of_isSegmentFigure (hC : IsCircuit C)
    (hpoly : IsSegmentFigure C) : Finite (ConnectedComponents ↥Cᶜ) := by
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨P, hP, rfl⟩ := hC.exists_isSimpleLoop hpoly.isCompact hx
  exact hP.finite_connectedComponents_compl hpoly

/-- A polygonal circuit has exactly two complementary components. -/
theorem card_connectedComponents_compl_of_isSegmentFigure (hC : IsCircuit C)
    (hpoly : IsSegmentFigure C) : Nat.card (ConnectedComponents ↥Cᶜ) = 2 := by
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨P, hP, rfl⟩ := hC.exists_isSimpleLoop hpoly.isCompact hx
  exact hP.card_connectedComponents_compl_eq_two hpoly

/-- Near a point of a polygonal circuit, both local sides of a complementary component
are connected. The circuit has no supplied parametrization. -/
theorem exists_ball_connected_sides_of_isSegmentFigure (hC : IsCircuit C)
    (hpoly : IsSegmentFigure C) (hz : z ∉ C) (hp : p ∈ C)
    {N : Set ℂ} (hN : N ∈ 𝓝 p) :
    ∃ r > 0, ball p r ⊆ N ∧
      IsConnected (ball p r ∩ interior (connectedComponentIn Cᶜ z)) ∧
      IsConnected (ball p r ∩ interior (connectedComponentIn Cᶜ z)ᶜ) := by
  obtain ⟨P, hP, rfl⟩ := hC.exists_isSimpleLoop hpoly.isCompact hp
  exact hP.exists_ball_connected_sides hpoly hz hp hN

/-- Polygonal Jordan separation stated for the circuit set, without a chosen traversal. -/
theorem exists_complement_regions_of_isSegmentFigure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
    {C : Set E} (hC : IsCircuit C) (hpoly : IsSegmentFigure C) :
    ∃ U V : Set E, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Cᶜ ∧ frontier U = C ∧ frontier V = C := by
  let : FiniteDimensional ℝ E := .of_fact_finrank_eq_two
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨P, hP, rfl⟩ := hC.exists_isSimpleLoop hpoly.isCompact hx
  exact hP.exists_complement_regions hpoly

end IsCircuit

namespace Set.CrossesOnce

variable {C L : Set ℂ} {x y : ℂ}

/-- A primitive link crossing a polygonal circuit once has endpoints in different complementary
components. The link itself need not be polygonal. -/
theorem not_mem_connectedComponentIn_compl_of_isSegmentFigure
    (h : CrossesOnce L C) (hC : IsCircuit C) (hpoly : IsSegmentFigure C)
    (hL : IsPrimitiveLink L x y) (hx : x ∉ C) (hy : y ∉ C) :
    x ∉ connectedComponentIn Cᶜ y := by
  apply h.not_mem_connectedComponentIn_compl hL
    (hC.frontier_connectedComponentIn_compl_of_isSegmentFigure hpoly hy) hx hy
  intro p hp N hN
  obtain ⟨r, hr, hrN, hleft, hright⟩ :=
    hC.exists_ball_connected_sides_of_isSegmentFigure hpoly hy hp.2 hN
  exact ⟨ball p r, ball_mem_nhds p hr, hrN, hleft.isPreconnected, hright.isPreconnected⟩

end Set.CrossesOnce

namespace IsCircuit

/-- With unique contact, crossing a polygonal circuit is equivalent to having endpoints
in different complementary components. -/
theorem crossesOnce_iff_not_mem_connectedComponentIn_compl_of_isSegmentFigure
    {C L : Set ℂ} {x y p : ℂ} (hC : IsCircuit C) (hpoly : IsSegmentFigure C)
    (hL : IsPrimitiveLink L x y) (hinter : C ∩ L = {p}) (hx : x ∉ C) (hy : y ∉ C) :
    CrossesOnce L C ↔ x ∉ connectedComponentIn Cᶜ y := by
  refine ⟨fun h ↦ h.not_mem_connectedComponentIn_compl_of_isSegmentFigure hC hpoly hL hx hy,
    fun hxy ↦ ?_⟩
  have hfront := hC.frontier_connectedComponentIn_compl_of_isSegmentFigure hpoly hy
  have hcross := hL.crossesOnce_frontier_of_not_iff_mem (U := connectedComponentIn Cᶜ y)
    (by rw [hfront, inter_comm]; exact hinter) (by rwa [hfront]) (by rwa [hfront])
    (fun h ↦ hxy (h.mpr (mem_connectedComponentIn hy)))
  simpa only [hfront] using hcross

end IsCircuit
