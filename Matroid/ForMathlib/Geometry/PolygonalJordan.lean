module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.SetTheory.Cardinal.NatCard
public import Matroid.ForMathlib.Geometry.PolygonalCrossing
public import Matroid.ForMathlib.Geometry.SegmentFigure.RayCrossing
public import Matroid.ForMathlib.Geometry.PrimitiveLink
public import Matroid.ForMathlib.Geometry.StarComponents
public import Matroid.ForMathlib.Topology.ConnectedComponent

/-!
# The polygonal Jordan curve theorem

A polygonal primitive loop in `ℂ` has exactly two complementary components, and every
complementary component has the whole loop as its frontier.

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

namespace IsPrimitiveLink

variable {S : Set ℂ} {x z : ℂ}

/-- Every complementary component of a polygonal primitive loop has the whole loop as frontier. -/
theorem frontier_connectedComponentIn_compl_eq (hL : IsPrimitiveLink S x x)
    (hpoly : IsSegmentFigure S) (hz : z ∉ S) :
    frontier (connectedComponentIn Sᶜ z) = S := by
  have hclosed : IsClosed S := hL.isClosed
  have hsub := hclosed.frontier_connectedComponentIn_compl_subset (x := z)
  let A : Set S := Subtype.val ⁻¹' frontier (connectedComponentIn Sᶜ z)
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
    exact fun h ↦ connectedComponentIn_subset Sᶜ z (interior_subset h) q.2
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hL.isConnected
  have hA : A = univ := IsClopen.eq_univ ⟨hAcl, hAo⟩ hAne
  refine hsub.antisymm fun p hp ↦ ?_
  have : (⟨p, hp⟩ : S) ∈ A := hA ▸ mem_univ _
  exact this

private theorem finite_card_connectedComponents_compl (hL : IsPrimitiveLink S x x)
    (hpoly : IsSegmentFigure S) :
    Finite (ConnectedComponents ↥Sᶜ) ∧ Nat.card (ConnectedComponents ↥Sᶜ) ≤ 2 := by
  classical
  obtain ⟨r, hr, hstar⟩ := hL.exists_local_star_two hpoly hL.left_mem (Or.inl rfl)
  obtain ⟨Y, hcard, hY, hstar⟩ := hstar r hr le_rfl
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hn : (sectors x r Y).ncard = 2 := by rw [ncard_sectors hr hYne hY, hcard]
  have hfin : (sectors x r Y).Finite := finite_of_ncard_ne_zero (by omega)
  let : Finite ↥(sectors x r Y) := hfin.to_subtype
  have hCS (C : ↥(sectors x r Y)) : C.1 ⊆ Sᶜ := by
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
  let point (C : ↥(sectors x r Y)) : ↥Sᶜ := ⟨(hne C).choose, hCS C (hne C).choose_spec⟩
  let f : ↥(sectors x r Y) → ConnectedComponents ↥Sᶜ :=
    fun C ↦ ConnectedComponents.mk (point C)
  have hf : Surjective f := by
    intro k
    obtain ⟨w, rfl⟩ := ConnectedComponents.surjective_coe k
    have hxfr : x ∈ frontier (connectedComponentIn Sᶜ w.1) := by
      rw [hL.frontier_connectedComponentIn_compl_eq hpoly w.2]
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
theorem finite_connectedComponents_compl (hL : IsPrimitiveLink S x x)
    (hpoly : IsSegmentFigure S) : Finite (ConnectedComponents ↥Sᶜ) :=
  (hL.finite_card_connectedComponents_compl hpoly).1

/-- A polygonal primitive loop has at most two complementary components.
Use `finite_connectedComponents_compl` as well: `Nat.card` is zero on infinite types. -/
theorem card_connectedComponents_compl_le_two (hL : IsPrimitiveLink S x x)
    (hpoly : IsSegmentFigure S) : Nat.card (ConnectedComponents ↥Sᶜ) ≤ 2 :=
  (hL.finite_card_connectedComponents_compl hpoly).2

/-- **Polygonal Jordan curve theorem.** The complement of a polygonal primitive loop in the
complex plane has exactly two connected components. Together with
`frontier_connectedComponentIn_compl_eq`, each of these components has frontier `S`. -/
theorem card_connectedComponents_compl_eq_two (hL : IsPrimitiveLink S x x)
    (hS : IsSegmentFigure S) : Nat.card (ConnectedComponents ↥Sᶜ) = 2 := by
  let : Finite (ConnectedComponents ↥Sᶜ) := hL.finite_connectedComponents_compl hS
  obtain ⟨v, _, htrans, p, _, ε, hε, hinterval⟩ :=
    Complex.orientation.exists_direction_singleton_interval hS hL.infinite
  obtain ⟨d, hd⟩ := exists_between hε
  let a := p - d • v
  have ha : a ∉ S := (hinterval d hd).1
  have haCross : Complex.rayCrossings S a v = {p} := (hinterval d hd).2
  obtain ⟨b, hb, hbCross⟩ :=
    Complex.orientation.exists_rayCrossings_eq_empty hL.isCompact.isBounded v
  change Complex.rayCrossings S b v = ∅ at hbCross
  have hne : ConnectedComponents.mk (⟨a, ha⟩ : ↥Sᶜ) ≠
      ConnectedComponents.mk (⟨b, hb⟩ : ↥Sᶜ) := by
    intro heq
    have hmem : (⟨a, ha⟩ : ↥Sᶜ) ∈ connectedComponent (⟨b, hb⟩ : ↥Sᶜ) :=
      ConnectedComponents.coe_eq_coe'.mp heq
    have he := (hL.isLocallyConstant_rayCrossings_parity hS htrans).apply_eq_of_isPreconnected
      isPreconnected_connectedComponent hmem mem_connectedComponent
    change (Complex.rayCrossings S a v).ncard % 2 =
      (Complex.rayCrossings S b v).ncard % 2 at he
    rw [haCross, hbCross, ncard_singleton, ncard_empty] at he
    norm_num at he
  let : Nontrivial (ConnectedComponents ↥Sᶜ) :=
    ⟨⟨ConnectedComponents.mk ⟨a, ha⟩, ConnectedComponents.mk ⟨b, hb⟩, hne⟩⟩
  exact (hL.card_connectedComponents_compl_le_two hS).antisymm Finite.one_lt_card

end IsPrimitiveLink
