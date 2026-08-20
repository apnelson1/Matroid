module

public import Matroid.ForMathlib.Topology.Path
public import Matroid.ForMathlib.Topology.ConnectedComponent
public import Matroid.ForMathlib.Topology.OnePoint
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The Jordan curve theorem

A **Jordan curve** is the image of an embedded circle. `IsJordanCurve J` expresses this as the
range of a simple loop.

This file deliberately treats the Jordan curve theorem as an **axiom**. The axiom chooses the
bounded complementary component. From it we define canonical sets `IsJordanCurve.inside` and
`IsJordanCurve.outside` and derive the rest of the usual plane and sphere APIs.

The canonical sets serve two purposes:

* callers do not have to repeatedly unpack increasingly large existential statements; and
* references to JCT-dependent objects remain visible.

## Main definitions

* `IsJordanCurve`
* `IsJordanCurve.inside` : the bounded component of the complement.
* `IsJordanCurve.outside` : the unbounded component of the complement.
* `IsJordanCurve.insideOnePoint`, `IsJordanCurve.outsideOnePoint` : the corresponding regions in
  the one-point compactification, with `outsideOnePoint` containing `∞`.

## Foundational assumption

* `IsJordanCurve.jordanCurveTheorem` : the sole JCT axiom in this file.
-/

@[expose] public section

open Set Function Topology Bornology

variable {X : Type*} [TopologicalSpace X] {J K W : Set X} {a : X}

/-- `J` is a Jordan curve: the image of a loop traversing it exactly once. Equivalently, for
compact `J` in a Hausdorff space, `J` is homeomorphic to a circle. -/
def IsJordanCurve (J : Set X) : Prop := ∃ (x : X) (P : Path x x), P.IsSimpleLoop ∧ range P = J

namespace IsJordanCurve

lemma isCompact (hJ : IsJordanCurve J) : IsCompact J := by
  obtain ⟨x, P, -, rfl⟩ := hJ
  exact isCompact_range P.continuous

lemma isClosed [T2Space X] (hJ : IsJordanCurve J) : IsClosed J := hJ.isCompact.isClosed

lemma nonempty (hJ : IsJordanCurve J) : J.Nonempty := by
  obtain ⟨x, P, -, rfl⟩ := hJ
  exact range_nonempty P

end IsJordanCurve

/-! ### The plane -/

namespace IsJordanCurve

section Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
  {J : Set E}

/-- `E` is finite-dimensional throughout this section, hence proper, so bounded sets have compact
closure. Local rather than global because `Fact (Module.finrank ℝ E = 2)` is a section hypothesis
here, not something to search for library-wide. -/
local instance : FiniteDimensional ℝ E := .of_fact_finrank_eq_two

/-- **AXIOM: the Jordan curve theorem.**

A Jordan curve in the plane has a bounded connected side; the remainder of its complement is
connected; and the curve is the frontier of both sides.

The boundedness hypothesis orients the otherwise symmetric theorem and makes the bounded side
canonical. `inside` is defined to be the chosen witness and `outside` is defined as the rest of the
complement.

This theorem is intentionally an axiom for now. It should eventually be replaced by a proof.
-/
axiom jordanCurveTheorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] {J : Set E} (hJ : IsJordanCurve J) : ∃ U : Set E, U ⊆ Jᶜ ∧
    IsBounded U ∧ IsConnected U ∧ IsConnected (Jᶜ \ U) ∧ frontier U = J ∧ frontier (Jᶜ \ U) = J

run_cmd Lean.logWarning "The Jordan curve theorem is currently assumed as an axiom and has not \
  been proved in this library."

/-- The **inside** of a Jordan curve: its bounded complementary component.

This is noncomputable because it chooses the bounded side supplied by `jordanCurveTheorem`.
Although implemented using choice, the later uniqueness API shows that this set is mathematically
canonical: it is the unique bounded connected component of `Jᶜ`.
-/
noncomputable def inside (hJ : IsJordanCurve J) : Set E := hJ.jordanCurveTheorem.choose

/-- The **outside** of a Jordan curve: the part of the complement not belonging to `inside`.

This definition makes disjointness and coverage essentially set-theoretic consequences. Later
lemmas show that it is exactly the unique unbounded connected component of `Jᶜ`.
-/
noncomputable def outside (hJ : IsJordanCurve J) : Set E := Jᶜ \ hJ.inside

/-! #### Basic set-theoretic and topological properties -/

/-- The inside lies in the complement of the curve. -/
theorem inside_subset_compl (hJ : IsJordanCurve J) : hJ.inside ⊆ Jᶜ :=
  hJ.jordanCurveTheorem.choose_spec.1

/-- The outside lies in the complement of the curve. -/
theorem outside_subset_compl (hJ : IsJordanCurve J) : hJ.outside ⊆ Jᶜ := sdiff_subset

/-- The inside of a Jordan curve is connected. -/
theorem inside_isConnected (hJ : IsJordanCurve J) : IsConnected hJ.inside :=
  hJ.jordanCurveTheorem.choose_spec.2.2.1

/-- The outside of a Jordan curve is connected. -/
theorem outside_isConnected (hJ : IsJordanCurve J) : IsConnected hJ.outside :=
  hJ.jordanCurveTheorem.choose_spec.2.2.2.1

/-- The inside of a Jordan curve is nonempty. -/
theorem inside_nonempty (hJ : IsJordanCurve J) : hJ.inside.Nonempty :=
  hJ.inside_isConnected.nonempty

/-- The outside of a Jordan curve is nonempty. -/
theorem outside_nonempty (hJ : IsJordanCurve J) : hJ.outside.Nonempty :=
  hJ.outside_isConnected.nonempty

/-- The inside and outside are disjoint. -/
theorem inside_disjoint_outside (hJ : IsJordanCurve J) : Disjoint hJ.inside hJ.outside :=
  disjoint_sdiff_right

/-- The inside and outside exhaust the complement of the curve. -/
@[simp, grind =]
theorem inside_union_outside (hJ : IsJordanCurve J) : hJ.inside ∪ hJ.outside = Jᶜ :=
  union_sdiff_cancel hJ.inside_subset_compl

/-- The complement of the curve is the union of its inside and outside. -/
theorem compl_eq_inside_union_outside (hJ : IsJordanCurve J) : Jᶜ = hJ.inside ∪ hJ.outside :=
  hJ.inside_union_outside.symm

/-- The inside is bounded. This is the property that orients the two complementary components. -/
theorem inside_isBounded (hJ : IsJordanCurve J) : IsBounded hJ.inside :=
  hJ.jordanCurveTheorem.choose_spec.2.1

/-- The frontier of the inside is exactly the Jordan curve. -/
@[simp, grind =]
theorem frontier_inside (hJ : IsJordanCurve J) : frontier hJ.inside = J :=
  hJ.jordanCurveTheorem.choose_spec.2.2.2.2.1

/-- The frontier of the outside is exactly the Jordan curve. -/
@[simp, grind =]
theorem frontier_outside (hJ : IsJordanCurve J) : frontier hJ.outside = J :=
  hJ.jordanCurveTheorem.choose_spec.2.2.2.2.2

/-- The inside is open. -/
theorem inside_isOpen (hJ : IsJordanCurve J) : IsOpen hJ.inside := by
  rw [← disjoint_frontier_iff_isOpen, hJ.frontier_inside, disjoint_comm]
  exact subset_compl_iff_disjoint_right.mp hJ.inside_subset_compl

/-- The outside is open. -/
theorem outside_isOpen (hJ : IsJordanCurve J) : IsOpen hJ.outside := by
  rw [← disjoint_frontier_iff_isOpen, hJ.frontier_outside, disjoint_comm]
  exact subset_compl_iff_disjoint_right.mp hJ.outside_subset_compl

/-- The outside is unbounded. -/
theorem outside_not_isBounded (hJ : IsJordanCurve J) : ¬ IsBounded hJ.outside := by
  intro hB
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (R := ℝ) (M := E) (n := 1) Fact.out
  refine NormedSpace.unbounded_univ (𝕜 := ℝ) (E := E) ?_
  rw [← union_compl_self J, ← hJ.inside_union_outside]
  exact hJ.isCompact.isBounded.union (hJ.inside_isBounded.union hB)

/-! #### Closure and boundary formulas -/

/-- The closure of the inside is the inside together with the curve. -/
@[simp, grind =]
theorem closure_inside (hJ : IsJordanCurve J) : closure hJ.inside = hJ.inside ∪ J :=
  (closure_eq_self_union_frontier _).trans (congrArg _ hJ.frontier_inside)

/-- The closure of the outside is the outside together with the curve. -/
@[simp, grind =]
theorem closure_outside (hJ : IsJordanCurve J) : closure hJ.outside = hJ.outside ∪ J :=
  (closure_eq_self_union_frontier _).trans (congrArg _ hJ.frontier_outside)

/-- The closures of the two complementary regions meet exactly in the Jordan curve. -/
theorem closure_inside_inter_closure_outside (hJ : IsJordanCurve J) :
    closure hJ.inside ∩ closure hJ.outside = J := by
  rw [hJ.closure_inside, hJ.closure_outside]
  ext x
  grind [hJ.inside_disjoint_outside.notMem_of_mem_left]

/-! #### Connected-component characterizations -/

/-- Any point of the inside generates the inside as its connected component in `Jᶜ`. -/
theorem inside_eq_connectedComponentIn (hJ : IsJordanCurve J) {a : E} (ha : a ∈ hJ.inside) :
    hJ.inside = connectedComponentIn Jᶜ a :=
  eq_connectedComponentIn_of_frontier_subset hJ.inside_isOpen hJ.inside_isConnected.isPreconnected
    (subset_compl_iff_disjoint_right.mp hJ.inside_subset_compl) hJ.frontier_inside.subset ha

/-- Any point of the outside generates the outside as its connected component in `Jᶜ`. -/
theorem outside_eq_connectedComponentIn (hJ : IsJordanCurve J) {a : E} (ha : a ∈ hJ.outside) :
    hJ.outside = connectedComponentIn Jᶜ a :=
  eq_connectedComponentIn_of_frontier_subset hJ.outside_isOpen hJ.outside_isConnected.isPreconnected
    (subset_compl_iff_disjoint_right.mp hJ.outside_subset_compl) hJ.frontier_outside.subset ha

/-- The two sides are distinct: they are disjoint and both nonempty. -/
theorem inside_ne_outside (hJ : IsJordanCurve J) : hJ.inside ≠ hJ.outside := fun h ↦
  hJ.inside_nonempty.ne_empty (disjoint_self.1 (h ▸ hJ.inside_disjoint_outside))

/-- Every point off the curve belongs to exactly one of the two canonical complementary
components. -/
theorem mem_inside_or_mem_outside (hJ : IsJordanCurve J) {a : E} (ha : a ∉ J) :
    a ∈ hJ.inside ∨ a ∈ hJ.outside := by
  rw [← mem_union, hJ.inside_union_outside, mem_compl_iff]
  exact ha

/-- Off the curve, lying outside is exactly not lying inside. -/
@[grind =]
theorem mem_outside_iff_notMem_inside (hJ : IsJordanCurve J) {a : E} (ha : a ∉ J) :
    a ∈ hJ.outside ↔ a ∉ hJ.inside := by
  simp [outside, ha]

/-- A connected component of the complement is either the inside or the outside. -/
theorem connectedComponentIn_eq_inside_or_outside
    (hJ : IsJordanCurve J) {a : E} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = hJ.inside ∨ connectedComponentIn Jᶜ a = hJ.outside := by
  obtain h | h := hJ.mem_inside_or_mem_outside ha
  · exact Or.inl (hJ.inside_eq_connectedComponentIn h).symm
  exact Or.inr (hJ.outside_eq_connectedComponentIn h).symm

/-- The inside is the unique bounded connected component of the complement. -/
@[grind =]
theorem connectedComponentIn_eq_inside_iff_isBounded
    (hJ : IsJordanCurve J) {a : E} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = hJ.inside ↔ IsBounded (connectedComponentIn Jᶜ a) :=
  ⟨fun h ↦ h ▸ hJ.inside_isBounded, fun hB ↦ (hJ.connectedComponentIn_eq_inside_or_outside ha).elim
    id (fun h ↦ absurd (h ▸ hB) hJ.outside_not_isBounded)⟩

/-- The outside is the unique unbounded connected component of the complement. -/
theorem connectedComponentIn_eq_outside_iff_not_isBounded
    (hJ : IsJordanCurve J) {a : E} (ha : a ∉ J) :
    connectedComponentIn Jᶜ a = hJ.outside ↔ ¬ IsBounded (connectedComponentIn Jᶜ a) := by
  rw [← hJ.connectedComponentIn_eq_inside_iff_isBounded ha]
  obtain h | h := hJ.connectedComponentIn_eq_inside_or_outside ha <;>
    simp [h, hJ.inside_ne_outside, hJ.inside_ne_outside.symm]

/-- A point off the curve lies inside exactly when its complementary component is bounded. -/
@[grind =]
theorem mem_inside_iff_isBounded_connectedComponentIn (hJ : IsJordanCurve J) {a : E} (ha : a ∉ J) :
    a ∈ hJ.inside ↔ IsBounded (connectedComponentIn Jᶜ a) := by
  rw [← hJ.connectedComponentIn_eq_inside_iff_isBounded ha]
  exact ⟨fun hin ↦ (hJ.inside_eq_connectedComponentIn hin).symm,
    (· ▸ mem_connectedComponentIn (mem_compl ha))⟩

/-- A point off the curve lies outside exactly when its complementary component is unbounded. -/
theorem mem_outside_iff_not_isBounded_connectedComponentIn
    (hJ : IsJordanCurve J) {a : E} (ha : a ∉ J) :
    a ∈ hJ.outside ↔ ¬ IsBounded (connectedComponentIn Jᶜ a) := by
  rw [hJ.mem_outside_iff_notMem_inside ha, hJ.mem_inside_iff_isBounded_connectedComponentIn ha]

/-- The complement of a Jordan curve has exactly two connected components. -/
theorem card_connectedComponents_compl (hJ : IsJordanCurve J) :
    Nat.card (ConnectedComponents ↥Jᶜ) = 2 :=
  ConnectedComponents.card_eq_two hJ.inside_isOpen hJ.outside_isOpen hJ.inside_isConnected
    hJ.outside_isConnected hJ.inside_disjoint_outside hJ.inside_union_outside

/-! ### The one-point compactification -/

/-- The inside region viewed in the one-point compactification. -/
noncomputable def insideOnePoint (hJ : IsJordanCurve J) : Set (OnePoint E) := (↑) '' hJ.inside

/-- The outside region in the one-point compactification.

It is defined as the remainder of the complement after removing `insideOnePoint`. This makes the
sphere-side disjointness and covering formulas set-theoretic. The geometric formula
`outsideOnePoint = insert ∞ ((↑) '' outside)` is stated below.
-/
noncomputable def outsideOnePoint (hJ : IsJordanCurve J) : Set (OnePoint E) :=
  ((↑) '' J : Set (OnePoint E))ᶜ \ hJ.insideOnePoint

/-- The image of the plane inside misses infinity. -/
@[simp]
theorem infty_notMem_insideOnePoint (hJ : IsJordanCurve J) : OnePoint.infty ∉ hJ.insideOnePoint :=
  OnePoint.infty_notMem_image_coe

/-- The sphere outside contains infinity. -/
@[simp]
theorem infty_mem_outsideOnePoint (hJ : IsJordanCurve J) : OnePoint.infty ∈ hJ.outsideOnePoint :=
  ⟨mem_compl OnePoint.infty_notMem_image_coe, hJ.infty_notMem_insideOnePoint⟩

/-- The sphere outside is infinity together with the image of the plane outside. -/
theorem outsideOnePoint_eq_insert_image_outside (hJ : IsJordanCurve J) :
    hJ.outsideOnePoint = insert OnePoint.infty ((↑) '' hJ.outside) := by
  rw [outsideOnePoint, insideOnePoint, OnePoint.compl_image_coe, ← hJ.inside_union_outside,
    image_union, insert_eq, union_comm {OnePoint.infty}, union_assoc]
  refine union_sdiff_cancel_left ?_
  rw [subset_empty_iff, ← disjoint_iff_inter_eq_empty]
  exact (disjoint_image_of_injective OnePoint.coe_injective hJ.inside_disjoint_outside).union_right
    (disjoint_singleton_right.2 OnePoint.infty_notMem_image_coe)

/-- The inside and outside are disjoint on the sphere. -/
theorem insideOnePoint_disjoint_outsideOnePoint (hJ : IsJordanCurve J) :
    Disjoint hJ.insideOnePoint hJ.outsideOnePoint := disjoint_sdiff_right

/-- The two sphere regions exhaust the complement of the embedded curve. -/
@[simp, grind =]
theorem insideOnePoint_union_outsideOnePoint (hJ : IsJordanCurve J) :
    hJ.insideOnePoint ∪ hJ.outsideOnePoint = ((↑) '' J : Set (OnePoint E))ᶜ := by
  refine union_sdiff_cancel ?_
  rw [insideOnePoint, subset_compl_iff_disjoint_right]
  exact disjoint_image_of_injective OnePoint.coe_injective
    (subset_compl_iff_disjoint_right.mp hJ.inside_subset_compl)

/-- The sphere inside is connected. -/
theorem insideOnePoint_isConnected (hJ : IsJordanCurve J) : IsConnected hJ.insideOnePoint :=
  hJ.inside_isConnected.image _ OnePoint.continuous_coe.continuousOn

/-- The sphere outside is connected. -/
theorem outsideOnePoint_isConnected (hJ : IsJordanCurve J) : IsConnected hJ.outsideOnePoint := by
  rw [hJ.outsideOnePoint_eq_insert_image_outside]
  have himg : IsConnected ((OnePoint.some : E → OnePoint E) '' hJ.outside) :=
    hJ.outside_isConnected.image OnePoint.some OnePoint.continuous_coe.continuousOn
  exact himg.subset_closure (subset_insert _ _)
    (insert_subset (OnePoint.infty_mem_closure_image_coe.2 fun _ _ hK hsub ↦
    hJ.outside_not_isBounded (hK.isBounded.subset hsub)) subset_closure)

/-- The sphere inside is open. -/
theorem insideOnePoint_isOpen (hJ : IsJordanCurve J) : IsOpen hJ.insideOnePoint :=
  OnePoint.isOpen_image_coe.2 hJ.inside_isOpen

/-- The sphere outside is open. -/
theorem outsideOnePoint_isOpen (hJ : IsJordanCurve J) : IsOpen hJ.outsideOnePoint := by
  rw [(show hJ.outsideOnePoint = ((↑) '' (J ∪ hJ.inside))ᶜ from by
    rw [outsideOnePoint, insideOnePoint, sdiff_eq, ← compl_union, image_union, union_comm]),
      (show J ∪ hJ.inside = closure hJ.inside from by
    rw [hJ.closure_inside, union_comm]), OnePoint.isOpen_compl_image_coe]
  exact ⟨isClosed_closure, hJ.inside_isBounded.isCompact_closure⟩

/-- The frontier of the sphere inside is the embedded Jordan curve. -/
@[simp, grind =]
theorem frontier_insideOnePoint (hJ : IsJordanCurve J) : frontier hJ.insideOnePoint = (↑) '' J := by
  have hclImg : closure hJ.insideOnePoint =
      (OnePoint.some : E → OnePoint E) '' closure hJ.inside := by
    rw [insideOnePoint]
    exact subset_antisymm (closure_minimal (image_mono subset_closure)
      (OnePoint.isClosed_image_coe.2 ⟨isClosed_closure, hJ.inside_isBounded.isCompact_closure⟩))
      (image_closure_subset_closure_image (f := OnePoint.some) OnePoint.continuous_coe)
  rw [hJ.insideOnePoint_isOpen.frontier_eq, hclImg, insideOnePoint,
    ← image_sdiff OnePoint.coe_injective, ← hJ.inside_isOpen.frontier_eq, hJ.frontier_inside]

/-- The frontier of the sphere outside is the embedded Jordan curve. -/
@[simp, grind =]
theorem frontier_outsideOnePoint (hJ : IsJordanCurve J) :
    frontier hJ.outsideOnePoint = (↑) '' J := by
  have hcl : closure hJ.insideOnePoint =
    hJ.insideOnePoint ∪ ((OnePoint.some : E → OnePoint E) '' J) :=
    (closure_eq_self_union_frontier _).trans (congrArg _ hJ.frontier_insideOnePoint)
  have hcompl : hJ.outsideOnePoint = (closure hJ.insideOnePoint)ᶜ := by
    rw [hcl, outsideOnePoint, sdiff_eq, compl_union, inter_comm]
  rw [hcompl, frontier_compl, isClosed_closure.frontier_eq, hcl]
  set Jimg : Set (OnePoint E) := OnePoint.some '' J
  have hinter : interior (hJ.insideOnePoint ∪ Jimg) = hJ.insideOnePoint := by
    refine subset_antisymm (fun p hp ↦ (interior_subset hp).elim id fun hpJ ↦ ?_)
      <| hJ.insideOnePoint_isOpen.interior_eq.symm.subset.trans (interior_mono subset_union_left)
    obtain ⟨t, htss, htopen, hpt⟩ := mem_interior.1 hp
    obtain ⟨q, hqt, hqout⟩ := by
      refine mem_closure_iff.1 (show p ∈ closure hJ.outsideOnePoint from ?_) t htopen hpt
      rw [hJ.outsideOnePoint_eq_insert_image_outside]
      obtain ⟨x, hxJ, rfl⟩ := hpJ
      exact closure_mono (subset_insert OnePoint.infty _) (image_closure_subset_closure_image
        (f := OnePoint.some) OnePoint.continuous_coe
          ⟨x, hJ.closure_outside.symm ▸ mem_union_right _ hxJ, rfl⟩)
    exact ((hcompl ▸ hqout) (hcl ▸ htss hqt)).elim
  rw [hinter]
  refine union_sdiff_cancel_left ?_
  rw [subset_empty_iff, ← disjoint_iff_inter_eq_empty]
  exact disjoint_image_of_injective OnePoint.coe_injective
    (subset_compl_iff_disjoint_right.mp hJ.inside_subset_compl)

/-- Any point of the sphere inside generates that side as its complementary connected component. -/
theorem insideOnePoint_eq_connectedComponentIn (hJ : IsJordanCurve J) {a : OnePoint E}
    (ha : a ∈ hJ.insideOnePoint) :
    hJ.insideOnePoint = connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a :=
  eq_connectedComponentIn_of_frontier_subset hJ.insideOnePoint_isOpen
    hJ.insideOnePoint_isConnected.isPreconnected (by
      rw [insideOnePoint]
      exact disjoint_image_of_injective OnePoint.coe_injective
        (subset_compl_iff_disjoint_right.mp hJ.inside_subset_compl))
    hJ.frontier_insideOnePoint.subset ha

/-- Any point of the sphere outside generates that side as its complementary connected component. -/
theorem outsideOnePoint_eq_connectedComponentIn (hJ : IsJordanCurve J) {a : OnePoint E}
    (ha : a ∈ hJ.outsideOnePoint) :
    hJ.outsideOnePoint = connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a :=
  eq_connectedComponentIn_of_frontier_subset hJ.outsideOnePoint_isOpen
    hJ.outsideOnePoint_isConnected.isPreconnected (subset_compl_iff_disjoint_right.mp sdiff_subset)
    hJ.frontier_outsideOnePoint.subset ha

/-- Every point off the embedded curve belongs to one of the two canonical sphere regions. -/
theorem mem_insideOnePoint_or_mem_outsideOnePoint (hJ : IsJordanCurve J) {a : OnePoint E}
    (ha : a ∉ ((↑) '' J : Set (OnePoint E))) : a ∈ hJ.insideOnePoint ∨ a ∈ hJ.outsideOnePoint := by
  rwa [← mem_union, hJ.insideOnePoint_union_outsideOnePoint, mem_compl_iff]

/-- Every complementary component on the sphere is one of the two canonical sides. -/
theorem connectedComponentIn_onePoint_eq_inside_or_outside (hJ : IsJordanCurve J) {a : OnePoint E}
    (ha : a ∉ (↑) '' J) :
    connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a = hJ.insideOnePoint ∨
      connectedComponentIn ((↑) '' J : Set (OnePoint E))ᶜ a = hJ.outsideOnePoint := by
  obtain h | h := hJ.mem_insideOnePoint_or_mem_outsideOnePoint ha
  · exact Or.inl (hJ.insideOnePoint_eq_connectedComponentIn h).symm
  exact Or.inr (hJ.outsideOnePoint_eq_connectedComponentIn h).symm

/-- The complement of a Jordan curve on the sphere has exactly two connected components. -/
theorem card_connectedComponents_compl_onePoint (hJ : IsJordanCurve J) :
    Nat.card (ConnectedComponents ↥(((↑) '' J : Set (OnePoint E)))ᶜ) = 2 :=
  ConnectedComponents.card_eq_two hJ.insideOnePoint_isOpen hJ.outsideOnePoint_isOpen
    hJ.insideOnePoint_isConnected hJ.outsideOnePoint_isConnected
    hJ.insideOnePoint_disjoint_outsideOnePoint hJ.insideOnePoint_union_outsideOnePoint

/-- Packed plane form of the Jordan curve theorem. -/
theorem exists_sides (hJ : IsJordanCurve J) : ∃ U V : Set E,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = Jᶜ ∧
      IsBounded U ∧ ¬ IsBounded V ∧ frontier U = J ∧ frontier V = J :=
  ⟨hJ.inside, hJ.outside, hJ.inside_isOpen, hJ.outside_isOpen, hJ.inside_isConnected,
    hJ.outside_isConnected, hJ.inside_disjoint_outside, hJ.inside_union_outside,
    hJ.inside_isBounded, hJ.outside_not_isBounded, hJ.frontier_inside, hJ.frontier_outside⟩

/-- Packed sphere form of the Jordan curve theorem. -/
theorem exists_sides_onePoint (hJ : IsJordanCurve J) : ∃ U V : Set (OnePoint E),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = ((↑) '' J)ᶜ ∧ OnePoint.infty ∈ V ∧ frontier U = (↑) '' J ∧ frontier V = (↑) '' J :=
  ⟨hJ.insideOnePoint, hJ.outsideOnePoint, hJ.insideOnePoint_isOpen, hJ.outsideOnePoint_isOpen,
    hJ.insideOnePoint_isConnected, hJ.outsideOnePoint_isConnected,
    hJ.insideOnePoint_disjoint_outsideOnePoint, hJ.insideOnePoint_union_outsideOnePoint,
    hJ.infty_mem_outsideOnePoint, hJ.frontier_insideOnePoint, hJ.frontier_outsideOnePoint⟩

end Plane

end IsJordanCurve
