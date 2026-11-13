module

public import Matroid.MiniTauCeti.JCT.Topology.Path
public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent
public import Matroid.MiniTauCeti.JCT.Topology.OnePoint
public import Matroid.MiniTauCeti.JCT.Geometry.Jordan
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Complementary regions of compact circuits

For `hJ : IsCircuit J` and `hc : IsCompact J`, `hJ.inside hc` and `hJ.outside hc` are the
bounded and unbounded complementary components supplied by `IsCircuit.jordanCurveTheorem`.
Their one-point compactification counterparts are `hJ.insideOnePoint hc` and
`hJ.outsideOnePoint hc`, with the latter containing infinity.
-/

@[expose] public section

open Set Function Topology Bornology

namespace IsCircuit

section Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
  {J : Set E} (hJ : IsCircuit J) (hc : IsCompact J)

include hJ hc

/-- `E` is finite-dimensional throughout this section, hence proper, so bounded sets have compact
closure. Local rather than global because `Fact (Module.finrank ℝ E = 2)` is a section hypothesis
here, not something to search for library-wide. -/
local instance : FiniteDimensional ℝ E := .of_fact_finrank_eq_two

/-- The **inside** of a Jordan curve: its bounded complementary component.

This is noncomputable because it chooses the bounded side supplied by `jordanCurveTheorem`.
Although implemented using choice, the later uniqueness API shows that this set is mathematically
canonical: it is the unique bounded connected component of `Jᶜ`.
-/
noncomputable def inside : Set E := (hJ.jordanCurveTheorem hc).choose

/-- The **outside** of a Jordan curve: the part of the complement not belonging to `inside`.

This definition makes disjointness and coverage essentially set-theoretic consequences. Later
lemmas show that it is exactly the unique unbounded connected component of `Jᶜ`.
-/
noncomputable def outside : Set E := Jᶜ \ hJ.inside hc

/-! #### Basic set-theoretic and topological properties -/

/-- The inside lies in the complement of the curve. -/
theorem inside_subset_compl : hJ.inside hc ⊆ Jᶜ :=
  (hJ.jordanCurveTheorem hc).choose_spec.1

/-- The outside lies in the complement of the curve. -/
theorem outside_subset_compl : hJ.outside hc ⊆ Jᶜ := sdiff_subset

/-- The inside of a Jordan curve is connected. -/
theorem inside_isConnected : IsConnected (hJ.inside hc) :=
  (hJ.jordanCurveTheorem hc).choose_spec.2.2.1

/-- The outside of a Jordan curve is connected. -/
theorem outside_isConnected : IsConnected (hJ.outside hc) :=
  (hJ.jordanCurveTheorem hc).choose_spec.2.2.2.1

/-- The inside of a Jordan curve is nonempty. -/
theorem inside_nonempty : (hJ.inside hc).Nonempty :=
  (hJ.inside_isConnected hc).nonempty

/-- The outside of a Jordan curve is nonempty. -/
theorem outside_nonempty : (hJ.outside hc).Nonempty :=
  (hJ.outside_isConnected hc).nonempty

/-- The inside and outside are disjoint. -/
theorem inside_disjoint_outside : Disjoint (hJ.inside hc) (hJ.outside hc) :=
  disjoint_sdiff_right

/-- The inside and outside exhaust the complement of the curve. -/
@[simp, grind =]
theorem inside_union_outside : hJ.inside hc ∪ hJ.outside hc = Jᶜ :=
  union_sdiff_cancel (hJ.inside_subset_compl hc)

/-- The complement of the curve is the union of its inside and outside. -/
theorem compl_eq_inside_union_outside : Jᶜ = hJ.inside hc ∪ hJ.outside hc :=
  (hJ.inside_union_outside hc).symm

/-- The inside is bounded. This is the property that orients the two complementary components. -/
theorem inside_isBounded : IsBounded (hJ.inside hc) :=
  (hJ.jordanCurveTheorem hc).choose_spec.2.1

/-- The frontier of the inside is exactly the Jordan curve. -/
@[simp, grind =]
theorem frontier_inside : frontier (hJ.inside hc) = J :=
  (hJ.jordanCurveTheorem hc).choose_spec.2.2.2.2.1

/-- The frontier of the outside is exactly the Jordan curve. -/
@[simp, grind =]
theorem frontier_outside : frontier (hJ.outside hc) = J :=
  (hJ.jordanCurveTheorem hc).choose_spec.2.2.2.2.2

/-- The inside is open. -/
theorem inside_isOpen : IsOpen (hJ.inside hc) := by
  rw [← disjoint_frontier_iff_isOpen, hJ.frontier_inside hc, disjoint_comm]
  exact subset_compl_iff_disjoint_right.mp (hJ.inside_subset_compl hc)

/-- The outside is open. -/
theorem outside_isOpen : IsOpen (hJ.outside hc) := by
  rw [← disjoint_frontier_iff_isOpen, hJ.frontier_outside hc, disjoint_comm]
  exact subset_compl_iff_disjoint_right.mp (hJ.outside_subset_compl hc)

/-- The outside is unbounded. -/
theorem outside_not_isBounded : ¬ IsBounded (hJ.outside hc) := by
  intro hB
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (R := ℝ) (M := E) (n := 1) Fact.out
  refine NormedSpace.unbounded_univ (𝕜 := ℝ) (E := E) ?_
  rw [← union_compl_self J, ← hJ.inside_union_outside hc]
  exact hc.isBounded.union ((hJ.inside_isBounded hc).union hB)

/-! #### Closure and boundary formulas -/

/-- The closure of the inside is the inside together with the curve. -/
@[simp, grind =]
theorem closure_inside : closure (hJ.inside hc) = hJ.inside hc ∪ J :=
  (closure_eq_self_union_frontier _).trans (congrArg _ (hJ.frontier_inside hc))

/-- The closure of the outside is the outside together with the curve. -/
@[simp, grind =]
theorem closure_outside : closure (hJ.outside hc) = hJ.outside hc ∪ J :=
  (closure_eq_self_union_frontier _).trans (congrArg _ (hJ.frontier_outside hc))

/-- The closures of the two complementary regions meet exactly in the Jordan curve. -/
theorem closure_inside_inter_closure_outside :
    closure (hJ.inside hc) ∩ closure (hJ.outside hc) = J := by
  rw [hJ.closure_inside hc, hJ.closure_outside hc]
  ext x
  grind [(hJ.inside_disjoint_outside hc).notMem_of_mem_left]

/-! #### Connected-component characterizations -/

/-- Any point of the inside generates the inside as its connected component in `Jᶜ`. -/
theorem inside_eq_connectedComponentIn {a : E} (ha : a ∈ hJ.inside hc) :
    hJ.inside hc = connectedComponentIn Jᶜ a :=
  eq_connectedComponentIn_of_frontier_subset (hJ.inside_isOpen hc)
    (hJ.inside_isConnected hc).isPreconnected
    (subset_compl_iff_disjoint_right.mp (hJ.inside_subset_compl hc))
    (hJ.frontier_inside hc).subset ha

/-- Any point of the outside generates the outside as its connected component in `Jᶜ`. -/
theorem outside_eq_connectedComponentIn {a : E} (ha : a ∈ hJ.outside hc) :
    hJ.outside hc = connectedComponentIn Jᶜ a :=
  eq_connectedComponentIn_of_frontier_subset (hJ.outside_isOpen hc)
    (hJ.outside_isConnected hc).isPreconnected
    (subset_compl_iff_disjoint_right.mp (hJ.outside_subset_compl hc))
    (hJ.frontier_outside hc).subset ha

/-- The two sides are distinct: they are disjoint and both nonempty. -/
theorem inside_ne_outside : hJ.inside hc ≠ hJ.outside hc := fun h ↦
  (hJ.inside_nonempty hc).ne_empty (disjoint_self.1 (h ▸ (hJ.inside_disjoint_outside hc)))

/-- Every point off the curve belongs to exactly one of the two canonical complementary
components. -/
theorem mem_inside_or_mem_outside {a : E} (ha : a ∉ J) :
    a ∈ hJ.inside hc ∨ a ∈ hJ.outside hc := by
  rw [← mem_union, hJ.inside_union_outside hc, mem_compl_iff]
  exact ha

/-- Off the curve, lying outside is exactly not lying inside. -/
@[grind =]
theorem mem_outside_iff_notMem_inside {a : E} (ha : a ∉ J) :
    a ∈ hJ.outside hc ↔ a ∉ hJ.inside hc := by
  simp [outside, ha]

/-- A connected component of the complement is either the inside or the outside. -/
theorem connectedComponentIn_eq_inside_or_outside
    {a : E} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = hJ.inside hc ∨ connectedComponentIn Jᶜ a = hJ.outside hc := by
  obtain h | h := hJ.mem_inside_or_mem_outside hc ha
  · exact Or.inl (hJ.inside_eq_connectedComponentIn hc h).symm
  exact Or.inr (hJ.outside_eq_connectedComponentIn hc h).symm

/-- The inside is the unique bounded connected component of the complement. -/
@[grind =]
theorem connectedComponentIn_eq_inside_iff_isBounded
    {a : E} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = hJ.inside hc ↔ IsBounded (connectedComponentIn Jᶜ a) :=
  ⟨fun h ↦ h ▸ hJ.inside_isBounded hc, fun hB ↦
    (hJ.connectedComponentIn_eq_inside_or_outside hc ha).elim id
      (fun h ↦ absurd (h ▸ hB) (hJ.outside_not_isBounded hc))⟩

/-- The outside is the unique unbounded connected component of the complement. -/
theorem connectedComponentIn_eq_outside_iff_not_isBounded
    {a : E} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = hJ.outside hc ↔ ¬ IsBounded (connectedComponentIn Jᶜ a) := by
  rw [← hJ.connectedComponentIn_eq_inside_iff_isBounded hc ha]
  obtain h | h := hJ.connectedComponentIn_eq_inside_or_outside hc ha <;>
    simp [h, hJ.inside_ne_outside hc, (hJ.inside_ne_outside hc).symm]

/-- A point off the curve lies inside exactly when its complementary component is bounded. -/
@[grind =]
theorem mem_inside_iff_isBounded_connectedComponentIn {a : E} (ha : a ∉ J) :
    a ∈ hJ.inside hc ↔ IsBounded (connectedComponentIn Jᶜ a) := by
  rw [← hJ.connectedComponentIn_eq_inside_iff_isBounded hc ha]
  exact ⟨fun hin ↦ (hJ.inside_eq_connectedComponentIn hc hin).symm,
    (· ▸ mem_connectedComponentIn (mem_compl ha))⟩

/-- A point off the curve lies outside exactly when its complementary component is unbounded. -/
theorem mem_outside_iff_not_isBounded_connectedComponentIn
    {a : E} (ha : a ∉ J) :
    a ∈ hJ.outside hc ↔ ¬ IsBounded (connectedComponentIn Jᶜ a) := by
  rw [hJ.mem_outside_iff_notMem_inside hc ha,
    hJ.mem_inside_iff_isBounded_connectedComponentIn hc ha]

/-- The complement of a Jordan curve has exactly two connected components. -/
theorem card_connectedComponents_compl :
    Nat.card (ConnectedComponents ↥Jᶜ) = 2 :=
  ConnectedComponents.card_eq_two (hJ.inside_isOpen hc) (hJ.outside_isOpen hc)
    (hJ.inside_isConnected hc)
    (hJ.outside_isConnected hc) (hJ.inside_disjoint_outside hc) (hJ.inside_union_outside hc)

/-! ### The one-point compactification -/

/-- The inside region viewed in the one-point compactification. -/
noncomputable def insideOnePoint : Set (OnePoint E) := (↑) '' hJ.inside hc

/-- The outside region in the one-point compactification.

It is defined as the remainder of the complement after removing `insideOnePoint`. This makes the
sphere-side disjointness and covering formulas set-theoretic. The geometric formula
`outsideOnePoint = insert ∞ ((↑) '' outside)` is stated below.
-/
noncomputable def outsideOnePoint : Set (OnePoint E) :=
  ((↑) '' J : Set (OnePoint E))ᶜ \ hJ.insideOnePoint hc

/-- The image of the plane inside misses infinity. -/
@[simp]
theorem infty_notMem_insideOnePoint : OnePoint.infty ∉ hJ.insideOnePoint hc :=
  OnePoint.infty_notMem_image_coe

/-- The sphere outside contains infinity. -/
@[simp]
theorem infty_mem_outsideOnePoint : OnePoint.infty ∈ hJ.outsideOnePoint hc :=
  ⟨mem_compl OnePoint.infty_notMem_image_coe, hJ.infty_notMem_insideOnePoint hc⟩

/-- The sphere outside is infinity together with the image of the plane outside. -/
theorem outsideOnePoint_eq_insert_image_outside :
    hJ.outsideOnePoint hc = insert OnePoint.infty ((↑) '' hJ.outside hc) := by
  rw [outsideOnePoint, insideOnePoint, OnePoint.compl_image_coe, ← hJ.inside_union_outside hc,
    image_union, insert_eq, union_comm {OnePoint.infty}, union_assoc]
  refine union_sdiff_cancel_left ?_
  rw [subset_empty_iff, ← disjoint_iff_inter_eq_empty]
  exact (disjoint_image_of_injective OnePoint.coe_injective
    (hJ.inside_disjoint_outside hc)).union_right
    (disjoint_singleton_right.2 OnePoint.infty_notMem_image_coe)

/-- The inside and outside are disjoint on the sphere. -/
theorem insideOnePoint_disjoint_outsideOnePoint :
    Disjoint (hJ.insideOnePoint hc) (hJ.outsideOnePoint hc) := disjoint_sdiff_right

/-- The two sphere regions exhaust the complement of the embedded curve. -/
@[simp, grind =]
theorem insideOnePoint_union_outsideOnePoint :
    hJ.insideOnePoint hc ∪ hJ.outsideOnePoint hc = ((↑) '' J : Set (OnePoint E))ᶜ := by
  refine union_sdiff_cancel ?_
  rw [insideOnePoint, subset_compl_iff_disjoint_right]
  exact disjoint_image_of_injective OnePoint.coe_injective
    (subset_compl_iff_disjoint_right.mp (hJ.inside_subset_compl hc))

/-- The sphere inside is connected. -/
theorem insideOnePoint_isConnected : IsConnected (hJ.insideOnePoint hc) :=
  (hJ.inside_isConnected hc).image _ OnePoint.continuous_coe.continuousOn

/-- The sphere outside is connected. -/
theorem outsideOnePoint_isConnected : IsConnected (hJ.outsideOnePoint hc) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (R := ℝ) (M := E) (n := 1) Fact.out
  have hcompact : IsCompact (hJ.outside hc)ᶜ := by
    simpa only [outside, compl_sdiff, compl_compl, hJ.closure_inside hc, union_comm] using
      (hJ.inside_isBounded hc).isCompact_closure
  rw [hJ.outsideOnePoint_eq_insert_image_outside hc, insert_eq, union_comm]
  simpa only [OnePoint.compl_image_coe, compl_compl] using
    OnePoint.isConnected_compl_image_coe_of_isCompact (hJ.outside_isConnected hc).isPreconnected
      hcompact

/-- The sphere inside is open. -/
theorem insideOnePoint_isOpen : IsOpen (hJ.insideOnePoint hc) :=
  OnePoint.isOpen_image_coe.2 (hJ.inside_isOpen hc)

/-- The sphere outside is open. -/
theorem outsideOnePoint_isOpen : IsOpen (hJ.outsideOnePoint hc) := by
  rw [(show hJ.outsideOnePoint hc = ((↑) '' (J ∪ hJ.inside hc))ᶜ from by
    rw [outsideOnePoint, insideOnePoint, sdiff_eq, ← compl_union, image_union, union_comm]),
      (show J ∪ hJ.inside hc = closure (hJ.inside hc) from by
    rw [hJ.closure_inside hc, union_comm]), OnePoint.isOpen_compl_image_coe]
  exact ⟨isClosed_closure, (hJ.inside_isBounded hc).isCompact_closure⟩

/-- The frontier of the sphere inside is the embedded Jordan curve. -/
@[simp, grind =]
theorem frontier_insideOnePoint : frontier (hJ.insideOnePoint hc) = (↑) '' J := by
  rw [insideOnePoint,
    OnePoint.frontier_image_coe_eq_iff.mpr (hJ.inside_isBounded hc).isCompact_closure,
    hJ.frontier_inside hc]

/-- The frontier of the sphere outside is the embedded Jordan curve. -/
@[simp, grind =]
theorem frontier_outsideOnePoint :
    frontier (hJ.outsideOnePoint hc) = (↑) '' J := by
  have hcompact : IsCompact (closure (hJ.outside hc)ᶜ) := by
    rw [(hJ.outside_isOpen hc).isClosed_compl.closure_eq]
    simpa only [outside, compl_sdiff, compl_compl, hJ.closure_inside hc, union_comm] using
      (hJ.inside_isBounded hc).isCompact_closure
  rw [show hJ.outsideOnePoint hc = ((↑) '' (hJ.outside hc)ᶜ : Set (OnePoint E))ᶜ by
    rw [outsideOnePoint, insideOnePoint, outside, compl_sdiff, compl_compl,
      image_union, compl_union, sdiff_eq, inter_comm], frontier_compl,
    OnePoint.frontier_image_coe_eq_iff.mpr hcompact, frontier_compl,
    hJ.frontier_outside hc]

/-- Any point of the sphere inside generates that side as its complementary connected component. -/
theorem insideOnePoint_eq_connectedComponentIn {a : OnePoint E}
    (ha : a ∈ hJ.insideOnePoint hc) :
    hJ.insideOnePoint hc = connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a :=
  eq_connectedComponentIn_of_frontier_subset (hJ.insideOnePoint_isOpen hc)
    (hJ.insideOnePoint_isConnected hc).isPreconnected (by
      rw [insideOnePoint]
      exact disjoint_image_of_injective OnePoint.coe_injective
        (subset_compl_iff_disjoint_right.mp (hJ.inside_subset_compl hc)))
    (hJ.frontier_insideOnePoint hc).subset ha

/-- Any point of the sphere outside generates that side as its complementary connected component. -/
theorem outsideOnePoint_eq_connectedComponentIn {a : OnePoint E}
    (ha : a ∈ hJ.outsideOnePoint hc) :
    hJ.outsideOnePoint hc = connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a :=
  eq_connectedComponentIn_of_frontier_subset (hJ.outsideOnePoint_isOpen hc)
    (hJ.outsideOnePoint_isConnected hc).isPreconnected
    (subset_compl_iff_disjoint_right.mp sdiff_subset)
    (hJ.frontier_outsideOnePoint hc).subset ha

/-- Every point off the embedded curve belongs to one of the two canonical sphere regions. -/
theorem mem_insideOnePoint_or_mem_outsideOnePoint {a : OnePoint E}
    (ha : a ∉ ((↑) '' J : Set (OnePoint E))) :
    a ∈ hJ.insideOnePoint hc ∨ a ∈ hJ.outsideOnePoint hc := by
  rwa [← mem_union, hJ.insideOnePoint_union_outsideOnePoint hc, mem_compl_iff]

/-- Every complementary component on the sphere is one of the two canonical sides. -/
theorem connectedComponentIn_onePoint_eq_inside_or_outside {a : OnePoint E}
    (ha : a ∉ (↑) '' J) :
    connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a = hJ.insideOnePoint hc ∨
      connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a = hJ.outsideOnePoint hc := by
  obtain h | h := hJ.mem_insideOnePoint_or_mem_outsideOnePoint hc ha
  · exact Or.inl (hJ.insideOnePoint_eq_connectedComponentIn hc h).symm
  exact Or.inr (hJ.outsideOnePoint_eq_connectedComponentIn hc h).symm

/-- The complement of a Jordan curve on the sphere has exactly two connected components. -/
theorem card_connectedComponents_compl_onePoint :
    Nat.card (ConnectedComponents ↥(((↑) '' J : Set (OnePoint E)))ᶜ) = 2 :=
  ConnectedComponents.card_eq_two (hJ.insideOnePoint_isOpen hc) (hJ.outsideOnePoint_isOpen hc)
    (hJ.insideOnePoint_isConnected hc) (hJ.outsideOnePoint_isConnected hc)
    (hJ.insideOnePoint_disjoint_outsideOnePoint hc) (hJ.insideOnePoint_union_outsideOnePoint hc)

/-- Packed plane form of the Jordan curve theorem. -/
theorem exists_sides : ∃ U V : Set E,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = Jᶜ ∧
      IsBounded U ∧ ¬ IsBounded V ∧ frontier U = J ∧ frontier V = J :=
  ⟨hJ.inside hc, hJ.outside hc, hJ.inside_isOpen hc, hJ.outside_isOpen hc,
    hJ.inside_isConnected hc, hJ.outside_isConnected hc, hJ.inside_disjoint_outside hc,
    hJ.inside_union_outside hc, hJ.inside_isBounded hc, hJ.outside_not_isBounded hc,
    hJ.frontier_inside hc, hJ.frontier_outside hc⟩

/-- Packed sphere form of the Jordan curve theorem. -/
theorem exists_sides_onePoint : ∃ U V : Set (OnePoint E),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = ((↑) '' J)ᶜ ∧ OnePoint.infty ∈ V ∧ frontier U = (↑) '' J ∧ frontier V = (↑) '' J :=
  ⟨hJ.insideOnePoint hc, hJ.outsideOnePoint hc, hJ.insideOnePoint_isOpen hc,
    hJ.outsideOnePoint_isOpen hc, hJ.insideOnePoint_isConnected hc,
    hJ.outsideOnePoint_isConnected hc, hJ.insideOnePoint_disjoint_outsideOnePoint hc,
    hJ.insideOnePoint_union_outsideOnePoint hc,
    hJ.infty_mem_outsideOnePoint hc, hJ.frontier_insideOnePoint hc, hJ.frontier_outsideOnePoint hc⟩

end Plane

end IsCircuit
