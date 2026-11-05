module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Shape
public import Matroid.ForMathlib.Geometry.SegmentFigure.Clipping
public import Matroid.ForMathlib.Geometry.SegmentFigure.Subset

/-! # Segment-figure consumers

These examples exercise algebraic ambient spaces, degenerate figures, common straight-line
presentations, intrinsic subsets, and clipping followed by deletion.
-/

open Set
open scoped GraphLike

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {S : Set V} {a b c d p z : V}

-- Degenerate segments account for finite point sets without a second generator type.
example : IsSegmentFigure ({a, b, c} : Set V) := by
  exact IsSegmentFigure.of_finite (by simp)

-- Reversed and duplicate segments do not change the intrinsic maximal-segment family.
example : maximalSegments (segment ℝ a b ∪ segment ℝ b a) = {segment ℝ a b} := by
  simp [segment_symm ℝ b a]

example : maximalSegments ({a} ∪ segment ℝ a a) = {{a}} := by simp

-- Membership is the standard order-theoretic maximality predicate, definitionally.
example (T : Set V) : T ∈ maximalSegments S ↔
    Maximal (fun U ↦ U ⊆ S ∧ ∃ a b, U = segment ℝ a b) T := Iff.rfl

example {T U : Set V} (hT : T ∈ maximalSegments S) (hU : U ⊆ S)
    (hseg : ∃ a b, U = segment ℝ a b) (hTU : T ⊆ U) : U = T := by
  have hmax : Maximal (fun U ↦ U ⊆ S ∧ ∃ a b, U = segment ℝ a b) T := hT
  exact hmax.eq_of_superset ⟨hU, hseg⟩ hTU

-- Endpoint-based construction remains available without unfolding Maximal.
example {T : Set V} (hseg : ∃ a b, T = segment ℝ a b) (hTS : T ⊆ S)
    (hmax : ∀ a b, T ⊆ segment ℝ a b → segment ℝ a b ⊆ S → segment ℝ a b = T) :
    T ∈ maximalSegments S := mem_maximalSegments_iff.mpr ⟨hseg, hTS, hmax⟩

-- Sections by an injectively parametrized line are finite unions of intervals even when
-- the ambient space has no topology instance.
example (hS : IsSegmentFigure S) (f : ℝ →ᵃ[ℝ] V) (hf : Function.Injective f) :
    ∃ E : Set (ℝ × ℝ), E.Finite ∧ f ⁻¹' S = ⋃ e ∈ E, Icc e.1 e.2 :=
  isSegmentFigure_iff_finite_iUnion_Icc.mp (hS.preimage f hf)

-- Endpoint separation controls a segment without any topology or global injectivity.
example {W : Type*} [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W)
    (hab : f a ≠ f b) : Set.InjOn f (segment ℝ a b) := f.injOn_segment (Or.inr hab)

example {W : Type*} [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W)
    (hab : f a ≠ f b) (w : W) : (segment ℝ a b ∩ f ⁻¹' {w}).Subsingleton :=
  f.subsingleton_segment_fiber hab w

-- The figure-level theorem permits affine maps to arbitrary real modules.
example {W : Type*} [AddCommGroup W] [Module ℝ W] (hS : IsSegmentFigure S)
    (f : V →ᵃ[ℝ] W) (hf : ∀ a b, a ≠ b → segment ℝ a b ⊆ S → f a ≠ f b) (w : W) :
    (S ∩ f ⁻¹' {w}).Finite := (hS.finite_fibers_iff f).mpr hf w

-- Degenerate generators impose no condition, even on a constant affine map.
example {W : Type*} [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (a : V) (w : W) :
    ({a} ∩ f ⁻¹' {w}).Finite := by
  refine AffineMap.finite_fiber_of_cover (E := {(a, a)})
    (finite_singleton _) ?_ f w ?_
  · simp
  · rintro e rfl h
    exact (h rfl).elim

end Algebra

-- A translated projection is not linear or globally injective, but separates these endpoints.
example : ∃ f : (ℝ × ℝ) →ᵃ[ℝ] ℝ,
    f (0, 0) ≠ 0 ∧ ¬ Function.Injective f ∧
      Set.InjOn f (segment ℝ (0, 0) (1, 1)) ∧
      (segment ℝ (0, 0) (1, 1) ∩ f ⁻¹' {(3 / 2 : ℝ)}).Subsingleton := by
  let f : (ℝ × ℝ) →ᵃ[ℝ] ℝ := AffineMap.fst + AffineMap.const ℝ (ℝ × ℝ) 1
  have hsep : f (0, 0) ≠ f (1, 1) := by norm_num [f]
  refine ⟨f, by norm_num [f], ?_, f.injOn_segment (Or.inr hsep),
    f.subsingleton_segment_fiber hsep _⟩
  intro h
  have heq : ((0, 0) : ℝ × ℝ) = (0, 1) := h (by simp [f])
  have := congrArg Prod.snd heq
  norm_num at this

section Presentation

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V] [T2Space V] {a b c d p z : V}

-- A marked common point survives common presentation, as does an extra point component.
example (hp : p ∈ segment ℝ a b ∩ segment ℝ c d) :
    ∃ G : GraphLike V, G.Finite ∧ G.IsStraightLine ∧ p ∈ G.vertexSet ∧ z ∈ G.vertexSet ∧
      segment ℝ a b ∪ {z} = ((segment ℝ a b ∪ {z}) ∩ G.vertexSet) ∪
        ⋃ e ∈ {e ∈ E(G) | e ⊆ segment ℝ a b ∪ {z}}, e := by
  let U : Bool → Set V := fun i ↦ if i then segment ℝ a b ∪ {z} else segment ℝ c d
  have hU (i) : IsSegmentFigure (U i) := by
    cases i <;> simp only [U, Bool.false_eq_true, ↓reduceIte]
    · exact isSegmentFigure_segment _ _
    exact (isSegmentFigure_segment _ _).union (isSegmentFigure_singleton _)
  have hmark : ({p, z} : Set V) ⊆ ⋃ i, U i := by
    rintro x (rfl | rfl)
    · exact mem_iUnion.mpr ⟨true, Or.inl hp.1⟩
    · exact mem_iUnion.mpr ⟨true, Or.inr rfl⟩
  obtain ⟨G, hfin, hstraight, _, hvertices, hcover⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike hU (by simp) hmark
  exact ⟨G, hfin, hstraight, hvertices (by simp), hvertices (by simp),
    by simpa [U] using hcover true⟩

end Presentation

section Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  {C : Set V} {a b c : V}

-- A connected closed subset of a branching figure inherits finite convex-hull data.
example (hc : IsClosed C) (hconn : IsConnected C)
    (hsub : C ⊆ segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a) :
    ∃ F : Set V, F.Finite ∧ F ⊆ C ∧ convexHull ℝ F = convexHull ℝ C := by
  have hS := ((isSegmentFigure_segment a b).union (isSegmentFigure_segment b c)).union
    (isSegmentFigure_segment c a)
  exact (hS.of_isClosed_isPreconnected hsub hc hconn.isPreconnected).exists_finite_convexHull_eq

-- Closedness alone is insufficient: infinitely many components rule out polygonality.
example (hsub : C ⊆ segment ℝ a b) [Infinite (ConnectedComponents C)] :
    ¬ IsSegmentFigure C := by
  intro h
  have := ((isSegmentFigure_segment a b).iff_isClosed_finite_connectedComponents hsub).mp h
  let := this.2
  exact _root_.not_finite (ConnectedComponents C)

-- Clipping and deleting finitely many points still leaves finite-dimensional geometry.
example {K F : Set V} (hK : Convex ℝ K) (hF : F.Finite) :
    FiniteDimensional ℝ (Submodule.span ℝ
      (closure (closure ((segment ℝ a b ∪ segment ℝ b c) ∩ K) \ F))) := by
  have hS := ((isSegmentFigure_segment a b).union
    (isSegmentFigure_segment b c)).closure_inter_convex hK
  exact (hS.closure_sdiff (IsSegmentFigure.of_finite hF)).finiteDimensional_span

-- Deleting vertices must retain surviving isolated points as well as edge ranges.
example {z : V} : IsSegmentFigure (closure ((segment ℝ a b ∪ {z}) \ {a, b})) :=
  ((isSegmentFigure_segment a b).union (isSegmentFigure_singleton z)).closure_sdiff
    (IsSegmentFigure.of_finite (by simp))

-- A figure consisting only of vertices has no edge pieces to supply the conclusion.
example {F T : Set V} (hF : F.Finite) (hT : IsSegmentFigure T) :
    IsSegmentFigure (closure (F \ T)) := (IsSegmentFigure.of_finite hF).closure_sdiff hT

-- Equal inputs leave nothing; partial overlap and disjoint components use the same API.
example (hS : IsSegmentFigure C) : IsSegmentFigure (closure (C \ C)) := hS.closure_sdiff hS

end Topology

example : IsSegmentFigure (closure ((Icc (0 : ℝ) 2 ∪ {4}) \ Icc 1 3)) :=
  ((isSegmentFigure_Icc 0 2).union (isSegmentFigure_singleton 4)).closure_sdiff
    (isSegmentFigure_Icc 1 3)

/-- info: 'IsSegmentFigure.closure_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsSegmentFigure.closure_sdiff

/-- info: 'IsSegmentFigure.exists_common_straightLineGraphLike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsSegmentFigure.exists_common_straightLineGraphLike

/-- info: 'IsSegmentFigure.iff_isClosed_finite_connectedComponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsSegmentFigure.iff_isClosed_finite_connectedComponents

/-- info: 'IsSegmentFigure.finite_maximalSegments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsSegmentFigure.finite_maximalSegments

/-- info: 'AffineMap.injOn_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AffineMap.injOn_segment

/-- info: 'IsSegmentFigure.finite_fibers_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSegmentFigure.finite_fibers_iff
