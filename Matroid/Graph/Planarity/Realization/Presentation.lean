module

public import Matroid.Graph.Presentation.Quotient
public import Matroid.Graph.Connected.Defs
public import Matroid.Graph.Planarity.Realization.VertexSpace
public import Matroid.Graph.Presentation.Orientation
public import Matroid.ForMathlib.Topology.Path
public import Mathlib.Topology.Constructions

/-!
# The incidence (half-edge) realization

The realization of an incidence presentation: one half-interval for each incidence, with its `0`
endpoint glued to the incident vertex and its `1` endpoint glued to the `1` endpoint of the mate
incidence.  So each edge is two half-edges meeting at a midpoint, and an *orientation* of an edge
is a choice of one of its two incidences rather than a choice made by `Graph.source`.

This is a development running in parallel with the whole-edge model in
`Planarity/Realization/Basic.lean`, and it is intended to replace it: the plan is to reach parity
with that file, then deprecate it.  Everything here is therefore proved **natively**, not
transported across a homeomorphism with the whole-edge model — an API proved through a bridge to
the development being retired could not outlive it.  The two models are decoupled: nothing in the
import closure of this file mentions `Realization.Basic`, and the shared discrete `0`-skeleton
lives in `Realization.VertexSpace`.

## Why the incidence model

The gluing relation is strictly simpler.  A vertex meets a half-edge in exactly one way
(`glueRel_inl_inr_iff`) where the whole-edge model needs a case for each of `source` and `target`;
and a half-edge is never glued to itself, so **every** half-edge is an injective closed embedding
(`halfPath_injective`, `isClosedEmbedding_halfPath`).  The whole-edge model can only state those
two for a non-loop, guarded by `IsNonloopAt`.

## Parity ledger

Tracks `Planarity/Realization/Basic.lean`, whose 75 declarations are the target.  **stronger**
marks a statement that holds here without a hypothesis the whole-edge version needs — a caller
migrating across will have a dangling `IsNonloopAt` argument to drop.

* `Sum.preimage_image_*`, `Sigma.continuous_snd`, `*_of_subsingleton` — n/a; these are
  `ForMathlib` strays that happen to sit in the whole-edge file.
* `UniformSpace V(G)`, `DiscreteTopology`, `instFinite*` — shared, in `Realization.VertexSpace`.
* `edgeSource`, `edgeTarget`, `isLink_edgeSource_edgeTarget`,
  `IsNonloopAt.edgeSource_ne_edgeTarget` → `IncidenceAt.source`, `.target`,
  `.isLink_source_target`, `.other_ne`.  Done, in `Presentation/Orientation.lean`.
* `PreRealization`, `glueRelAux`, `glueRel` and the 18 lemmas analysing them → the same three
  names, plus `glueRel_inl_inl_iff`, `glueRel_inl_inr_iff`, `glueRel_inr_inl_iff`,
  `glueRel_inr_inr_iff`, `glueRel_inr_interior_iff(_eq)`.  Done, and shorter: no
  `_of_isNonloopAt` variant is needed here.
* `Realization`, `mk`, `mk_surjective`, `ind`, `mk_eq_mk`, `isOpen_iff_isOpen_preimage_mk`,
  `mk_inl`, `mk_inr`, `vertexMk`, `vertexMk_injective`, `vertexMk_inj` → same names.  Done.
* `edgePath` → `halfPath` (a half-edge) and `edgePathAt` (a whole edge, given an incidence).
  Done.
* `isOpen_iff` → `isOpen_iff`, together with `isClosed_iff`.  Done.
* `vertexMk_not_mem_edgePath_Ioo` → `vertexMk_eq_halfPath_iff`.  Done, stronger: an `iff`
  describing every coincidence, rather than a single non-membership.
* `edgePath_inj_of_mem_Ioo` → `halfPath_eq_halfPath_iff`, `edgePathAt_injOn_Ioo`.  Done.
* `edgePath_injective` (private, needs `IsNonloopAt`) → `halfPath_injective`.  Done, **stronger**.
* `disjoint_edgePath_Ioo_iff` → `disjoint_halfPath_Ioo_iff`, `disjoint_halfPath_Ioc_iff`.  Done.
* `preimage_edgePath_image`, `isOpen_edgePath_image` → `preimage_halfPath_image_self`,
  `preimage_halfPath_image_eq_empty`, `isOpen_halfPath_image`.  Done.
* `isClosedMap_edgePath` → `isClosedMap_halfPath`.  Done.
* `isClosedEmbedding_edgePath` (needs `IsNonloopAt`) → `isClosedEmbedding_halfPath`.  Done,
  **stronger**.
* `joined_vertexMk_of_isLink`, `_of_isWalk`, `_of_connBetween`,
  `Preconnected.joined_vertexMk_quotientMk`, `Connected.pathConnectedSpace` → `component`,
  `isClopen_preimage_component`, `exists_joined_vertexMk`, `joined_iff_component_eq`,
  `connectedComponent_eq`, `joined_vertexMk_iff`, `pathConnectedSpace_iff`.  Done, **stronger**:
  the two headline statements are `iff`s where all five whole-edge lemmas are one-directional, and
  `joined_iff_component_eq` is about arbitrary points rather than vertices.  The `Quotient.ind`
  plumbing of `Preconnected.joined_vertexMk_quotientMk` has no counterpart; it is replaced by
  `exists_joined_vertexMk`.
* `exists_vertexMk_or_exists_edgePath` → `indexMk`, `bijective_indexMk`.  Done, **stronger**: a
  bijection rather than a disjunction.  A caller wanting this as an `Equiv` writes
  `Equiv.ofBijective _ (bijective_indexMk O)`; it is not worth a name of its own.
* `edgeInteriorSet`, `iUnion_edgePath_Ioo` → `edgeInteriorSet`, `iUnion_edgeInteriorAt`.  Done.
* `isClopen_edgePath_Ioo` → `isOpen_edgeInteriorAt`.  Done, **stronger**: open in the whole
  realization rather than clopen in the subspace.  Closedness in the subspace follows from it with
  `disjoint_edgeInteriorAt_iff` and `iUnion_edgeInteriorAt`.
* `eq_edgePath_Ioo_of_mem_pathComponentPartition` → `isPathConnected_edgeInteriorAt` together with
  the previous two rows: the open edges are open, pairwise disjoint, cover `edgeInteriorSet` and
  are path-connected, so they are its path components.  Done.
* `nonempty_homeomorph_Ioo_of_mem_pathComponentPartition` — TODO.  What is missing is that
  `edgePathAt P a` restricted to `Ioo 0 1` is an *open* embedding; injectivity
  (`edgePathAt_injOn_Ioo`) and the image (`interior_edgePathAt`) are already here, and
  `isOpen_halfPath_image` does not apply directly because its hypothesis `1 ∉ X` fails for the
  half-open pieces `Ioc 0 1`.

Still outstanding beyond this file: the bridge `P.Realization ≃ₜ Graph.Realization P.toGraph`
(not needed for correctness, but it is what lets downstream files migrate one at a time instead of
in a single flag day), then parity for `Realization/Subgraph.lean`, `Iso.lean`, `CWComplex.lean`
and `Metric.lean`.  `Metric.lean` needs a design decision rather than only labour: half-edges want
length `1/2`, so the metric is not merely transported.
-/
@[expose] public noncomputable section

open Set Function TopologicalSpace Topology Sum Path Relation
open scoped unitInterval

namespace Graph.Presentation

/- Internal realization model attached to an incidence presentation.

This namespace is intentionally verbose so that it can be prototyped in a separate file.  In the
final realization module it should become private implementation detail. -/

variable {V E : Type*} {P Q R : Presentation V E} {e : E} {i j : P.I} {t : I}

/-- Disjoint union of the discrete vertices and one half-interval for each incidence. -/
abbrev PreRealization (P : Presentation V E) :=
  V(P.toGraph) ⊕ Σ (_ : P.I), unitInterval

/-- Generating gluings for the incidence realization.

* vertices are reflexively related to themselves;
* the `0` endpoint of incidence `i` is attached to `P.attach i`;
* the `1` endpoints of `i` and `P.other i` are identified.
-/
inductive GlueRelAux (P : Presentation V E) : P.PreRealization → P.PreRealization → Prop
  | vertex (v : V(P.toGraph)) : GlueRelAux P (.inl v) (.inl v)
  | attach (i : P.I) : GlueRelAux P (.inl ⟨P.attach i, P.attach_mem i⟩) (.inr ⟨i, 0⟩)
  | other (i : P.I) : GlueRelAux P (.inr ⟨i, 1⟩) (.inr ⟨P.other i, 1⟩)

/-- Equivalence closure of the generating incidence gluings. -/
instance glueRel (P : Presentation V E) : Setoid P.PreRealization :=
  EqvGen.setoid (GlueRelAux P)

instance : Std.Symm (glueRel P) where
  symm _ _ h := EqvGen.symm _ _ h

instance : IsTrans _ (glueRel P) where
  trans _ _ _ := EqvGen.trans _ _ _

/-! ### Analysis of the gluing relation

Three invariants determine the relation completely: an interior point of a half-edge is alone in
its class, the class of a vertex is that vertex together with the `0` ends attached to it, and the
class of a midpoint is the two `1` ends of one edge.  Unlike the whole-edge model there is no
source/target case split anywhere, and no case is special to loops. -/

private lemma one_ne_zero' : (1 : I) ≠ 0 := fun h ↦ one_ne_zero (congrArg Subtype.val h)

private lemma zero_ne_one' : (0 : I) ≠ 1 := fun h ↦ zero_ne_one (congrArg Subtype.val h)

/-- Membership of the class of the vertex `u`. -/
private def AtVertex (P : Presentation V E) (u : V(P.toGraph)) : P.PreRealization → Prop
  | .inl v => v = u
  | .inr ⟨j, t⟩ => t = 0 ∧ P.attach j = (u : V)

/-- Membership of the class of the midpoint of the edge through `i`. -/
private def AtMidpoint (P : Presentation V E) (i : P.I) : P.PreRealization → Prop
  | .inl _ => False
  | .inr ⟨j, t⟩ => t = 1 ∧ (j = i ∨ j = P.other i)

private lemma atVertex_eqvGen (u : V(P.toGraph)) {z w : P.PreRealization} (h : glueRel P z w) :
    AtVertex P u z ↔ AtVertex P u w := by
  induction h generalizing u with
  | refl => rfl
  | rel x y hxy =>
    cases hxy with
    | vertex v => rfl
    | attach j =>
      exact ⟨fun h ↦ ⟨rfl, congrArg Subtype.val h⟩, fun h ↦ Subtype.ext h.2⟩
    | other j => exact iff_of_false (fun h ↦ one_ne_zero' h.1) fun h ↦ one_ne_zero' h.1
  | symm x y _ ih => simpa [iff_comm] using ih u
  | trans x y z _ _ ixy iyz => exact (ixy u).trans (iyz u)

private lemma atMidpoint_eqvGen (i : P.I) {z w : P.PreRealization} (h : glueRel P z w) :
    AtMidpoint P i z ↔ AtMidpoint P i w := by
  induction h generalizing i with
  | refl => rfl
  | rel x y hxy =>
    cases hxy with
    | vertex v => rfl
    | attach j => exact iff_of_false id fun h ↦ zero_ne_one' h.1
    | other j =>
      refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
      · rintro (rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl (P.other_other i)
      · rintro (h | h)
        · exact Or.inr (P.other_involutive.injective (by rw [h, P.other_other]))
        · exact Or.inl (P.other_involutive.injective h)
  | symm x y _ ih => simpa [iff_comm] using ih i
  | trans x y z _ _ ixy iyz => exact (ixy i).trans (iyz i)

/-- The class of a vertex is the vertex together with the `0` ends attached to it. -/
private theorem glueRel_inl_iff_atVertex (u : V(P.toGraph)) (x : P.PreRealization) :
    glueRel P (.inl u) x ↔ AtVertex P u x := by
  refine ⟨fun h ↦ (atVertex_eqvGen u h).mp rfl, ?_⟩
  match x with
  | .inl v => exact fun h ↦ h ▸ EqvGen.refl _
  | .inr ⟨j, t⟩ =>
    rintro ⟨rfl, hj⟩
    obtain ⟨u, hu⟩ := u
    cases hj
    exact EqvGen.rel _ _ (.attach j)

/-- The class of a midpoint is exactly the two `1` ends of its edge. -/
private theorem glueRel_inr_one_iff_atMidpoint (i : P.I) (x : P.PreRealization) :
    glueRel P (.inr ⟨i, (1 : I)⟩) x ↔ AtMidpoint P i x := by
  refine ⟨fun h ↦ (atMidpoint_eqvGen i h).mp ⟨rfl, Or.inl rfl⟩, ?_⟩
  match x with
  | .inl v => exact False.elim
  | .inr ⟨j, t⟩ =>
    rintro ⟨rfl, rfl | rfl⟩
    · exact EqvGen.refl _
    · exact EqvGen.rel _ _ (.other i)

private lemma not_glueRelAux_inr_interior (ht : t ≠ 0 ∧ t ≠ 1) (y : P.PreRealization) :
    ¬ GlueRelAux P (.inr ⟨i, t⟩) y ∧ ¬ GlueRelAux P y (.inr ⟨i, t⟩) := by
  constructor <;> intro h <;> cases h
  · exact ht.2 rfl
  · exact ht.1 rfl
  · exact ht.2 rfl

/-- An interior point of a half-edge is glued to nothing else. -/
theorem glueRel_inr_interior_iff {a b : P.PreRealization} (ht : t ≠ 0 ∧ t ≠ 1)
    (h : glueRel P a b) : a = .inr ⟨i, t⟩ ↔ b = .inr ⟨i, t⟩ := by
  induction h with
  | refl => exact ⟨id, id⟩
  | rel x y hxy =>
    constructor <;> rintro rfl
    · exact ((not_glueRelAux_inr_interior ht y).1 hxy).elim
    · exact ((not_glueRelAux_inr_interior ht x).2 hxy).elim
  | symm _ _ _ ih => simpa [iff_comm] using ih
  | trans _ _ _ _ _ ixy iyz => exact ⟨fun hx ↦ iyz.1 (ixy.1 hx), fun hz ↦ ixy.2 (iyz.2 hz)⟩

lemma glueRel_inr_interior_iff_eq (ht : t ≠ 0 ∧ t ≠ 1) (x : P.PreRealization) :
    glueRel P (.inr ⟨i, t⟩) x ↔ x = .inr ⟨i, t⟩ :=
  ⟨fun h ↦ (glueRel_inr_interior_iff ht h).mp rfl, fun h ↦ h ▸ EqvGen.refl _⟩

/-! ### The membership criteria -/

@[simp]
lemma glueRel_inl_inl_iff (u v : V(P.toGraph)) : glueRel P (.inl u) (.inl v) ↔ u = v :=
  (glueRel_inl_iff_atVertex u _).trans eq_comm

/-- A vertex meets a half-edge only at its `0` end, and only the half-edge attached to it.  The
whole-edge model needs two cases here, one for each end of the edge. -/
@[simp]
theorem glueRel_inl_inr_iff (u : V(P.toGraph)) (j : P.I) (t : I) :
    glueRel P (.inl u) (.inr ⟨j, t⟩) ↔ t = 0 ∧ P.attach j = (u : V) :=
  glueRel_inl_iff_atVertex u _

@[simp]
theorem glueRel_inr_inl_iff (j : P.I) (t : I) (u : V(P.toGraph)) :
    glueRel P (.inr ⟨j, t⟩) (.inl u) ↔ t = 0 ∧ P.attach j = (u : V) :=
  Iff.trans ⟨EqvGen.symm _ _, EqvGen.symm _ _⟩ (glueRel_inl_inr_iff u j t)

/-- Two half-edge points are glued only when they coincide, when both are `0` ends attached to the
same vertex, or when both are the `1` ends of one edge. -/
theorem glueRel_inr_inr_iff (i j : P.I) (t s : I) :
    glueRel P (.inr ⟨i, t⟩) (.inr ⟨j, s⟩) ↔ (i = j ∧ t = s) ∨
      (t = 0 ∧ s = 0 ∧ P.attach i = P.attach j) ∨ (t = 1 ∧ s = 1 ∧ j = P.other i) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl | ht0 := eq_or_ne t 0
    · have hv : glueRel P (.inl (⟨P.attach i, P.attach_mem i⟩ : V(P.toGraph)))
          (.inr ⟨j, s⟩) := trans_of (glueRel P) (EqvGen.rel _ _ (.attach i)) h
      obtain ⟨rfl, hu⟩ := (glueRel_inl_inr_iff _ j s).mp hv
      exact Or.inr (Or.inl ⟨rfl, rfl, hu.symm⟩)
    obtain rfl | ht1 := eq_or_ne t 1
    · obtain ⟨rfl, rfl | rfl⟩ := (glueRel_inr_one_iff_atMidpoint i _).mp h
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    · have hx := (glueRel_inr_interior_iff_eq ⟨ht0, ht1⟩ _).mp h
      simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq] at hx
      exact Or.inl ⟨hx.1.symm, hx.2.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, hu⟩ | ⟨rfl, rfl, rfl⟩)
    · exact EqvGen.refl _
    · refine trans_of (glueRel P) (EqvGen.symm _ _ (EqvGen.rel _ _ (.attach i))) ?_
      exact (glueRel_inl_inr_iff _ j 0).mpr ⟨rfl, hu.symm⟩
    · exact EqvGen.rel _ _ (.other i)

/-- Presentation-level realization.  This should be private in the final public module. -/
abbrev Realization (P : Presentation V E) := Quotient (glueRel P)

namespace Realization

/-- Quotient projection. -/
def mk (P : Presentation V E) : C(P.PreRealization, P.Realization) where
  toFun := Quotient.mk'
  continuous_toFun := continuous_quotient_mk'

/-- Inclusion of a vertex in the presentation realization. -/
def vertexMk (P : Presentation V E) (v : V(P.toGraph)) : P.Realization :=
  Quotient.mk' (Sum.inl v)

/-- The midpoint representative supplied by one incidence.  The mate incidence gives the same
point in the quotient. -/
def midpointMk (P : Presentation V E) (i : P.I) : P.Realization :=
  Quotient.mk' (Sum.inr ⟨i, (1 : unitInterval)⟩)

@[simp]
lemma midpointMk_other (P : Presentation V E) (i : P.I) :
    midpointMk P (P.other i) = midpointMk P i := by
  apply Quotient.sound
  exact EqvGen.symm _ _ <| EqvGen.rel _ _ <| GlueRelAux.other i

/-- The half-edge path from the incident vertex to the midpoint of the edge. -/
def halfPath (P : Presentation V E) (i : P.I) :
    Path (vertexMk P ⟨P.attach i, P.attach_mem i⟩) (midpointMk P i) where
  toFun t := Quotient.mk' (Sum.inr ⟨i, t⟩)
  source' := Quotient.sound <| EqvGen.symm _ _ <| EqvGen.rel _ _ <| GlueRelAux.attach i
  target' := rfl
  continuous_toFun := continuous_quotient_mk'.comp' <| continuous_inr.comp' continuous_sigmaMk

/-! ### The quotient API -/

lemma mk_surjective : Surjective (mk P) := Quotient.mk_surjective

@[elab_as_elim]
lemma ind {p : P.Realization → Prop} (h : ∀ x, p (mk P x)) (x : P.Realization) : p x :=
  Quotient.inductionOn x h

@[simp]
lemma mk_eq_mk {x y : P.PreRealization} : mk P x = mk P y ↔ glueRel P x y := Quotient.eq

/-- The realization carries the quotient topology. -/
lemma isOpen_iff_isOpen_preimage_mk (U : Set P.Realization) : IsOpen U ↔ IsOpen (mk P ⁻¹' U) :=
  isOpen_coinduced

@[simp]
lemma mk_inl (v : V(P.toGraph)) : mk P (.inl v) = vertexMk P v := rfl

@[simp]
lemma mk_inr (i : P.I) (t : I) : mk P (.inr ⟨i, t⟩) = halfPath P i t := rfl

lemma vertexMk_injective (P : Presentation V E) : Injective (vertexMk P) := fun u v h ↦
  (glueRel_inl_inl_iff u v).mp (Quotient.exact h)

@[simp]
lemma vertexMk_inj {u v : V(P.toGraph)} : vertexMk P u = vertexMk P v ↔ u = v :=
  (vertexMk_injective P).eq_iff

/-- Openness in the realization is a condition on the half-edges only: the `0`-skeleton is
discrete, so the vertex half of the quotient criterion is automatic. -/
lemma isOpen_iff (U : Set P.Realization) :
    IsOpen U ↔ ∀ i : P.I, IsOpen (halfPath P i ⁻¹' U) := by
  rw [isOpen_iff_isOpen_preimage_mk, isOpen_sum_iff, isOpen_sigma_iff]
  simp only [isOpen_discrete, true_and]
  rfl

/-! ### Points of the realization

The two `iff`s below describe the points of the realization completely: when a vertex equals a
half-edge point, and when two half-edge points agree.  Everything else in this section is a
corollary. -/

@[simp]
theorem vertexMk_eq_halfPath_iff {v : V(P.toGraph)} {i : P.I} {t : I} :
    vertexMk P v = halfPath P i t ↔ t = 0 ∧ P.attach i = (v : V) :=
  Iff.trans mk_eq_mk (glueRel_inl_inr_iff v i t)

@[simp]
theorem halfPath_eq_vertexMk_iff {v : V(P.toGraph)} {i : P.I} {t : I} :
    halfPath P i t = vertexMk P v ↔ t = 0 ∧ P.attach i = (v : V) :=
  eq_comm.trans vertexMk_eq_halfPath_iff

theorem halfPath_eq_halfPath_iff {i j : P.I} {t s : I} :
    halfPath P i t = halfPath P j s ↔ (i = j ∧ t = s) ∨
      (t = 0 ∧ s = 0 ∧ P.attach i = P.attach j) ∨ (t = 1 ∧ s = 1 ∧ j = P.other i) :=
  Iff.trans mk_eq_mk (glueRel_inr_inr_iff i j t s)

/-- **Every** half-edge is injectively parametrised, with no nonloop hypothesis.  This is the
first place the incidence model is stronger than the whole-edge model, where the corresponding
statement fails for a loop and has to be guarded by `IsNonloopAt`. -/
theorem halfPath_injective (P : Presentation V E) (i : P.I) : Injective (halfPath P i) := by
  intro t s h
  obtain ⟨-, hts⟩ | ⟨rfl, rfl, -⟩ | ⟨-, -, hi⟩ := halfPath_eq_halfPath_iff.mp h
  · exact hts
  · rfl
  · exact absurd hi.symm (P.other_ne i)

@[simp]
theorem halfPath_inj {i : P.I} {t s : I} : halfPath P i t = halfPath P i s ↔ t = s :=
  (halfPath_injective P i).eq_iff

private lemma zero_lt_one_I : (0 : I) < 1 := unitInterval.pos_iff_ne_zero.2 one_ne_zero'

@[simp]
lemma halfPath_one (P : Presentation V E) (i : P.I) : halfPath P i 1 = midpointMk P i := rfl

@[simp]
lemma halfPath_zero (P : Presentation V E) (i : P.I) :
    halfPath P i 0 = vertexMk P ⟨P.attach i, P.attach_mem i⟩ := (halfPath P i).source

private lemma midpointMk_mem_image (i : P.I) : midpointMk P i ∈ halfPath P i '' Ioc 0 1 :=
  ⟨1, right_mem_Ioc.2 zero_lt_one_I, rfl⟩

/-- Two half-edges meet away from their attached vertices exactly when they are the two halves of
one edge, and then only at the midpoint.  Both conjuncts on the right are needed: `j = i` makes the
two images equal, and `j = P.other i` makes them share the midpoint.  Compare
`disjoint_halfPath_Ioo_iff`, whose right-hand side is the single condition `j ≠ i` because `Ioo`
omits the midpoint. -/
theorem disjoint_halfPath_Ioc_iff {i j : P.I} :
    Disjoint (halfPath P i '' Ioc 0 1) (halfPath P j '' Ioc 0 1) ↔
      j ≠ i ∧ j ≠ P.other i := by
  constructor
  · refine fun h ↦ ⟨?_, ?_⟩ <;> rintro rfl
    · exact h.notMem_of_mem_left (midpointMk_mem_image j) (midpointMk_mem_image j)
    · refine h.notMem_of_mem_left (midpointMk_mem_image i) ?_
      exact (midpointMk_other P i) ▸ midpointMk_mem_image (P.other i)
  · rintro ⟨hne, hno⟩
    refine disjoint_left.2 ?_
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, hst⟩
    obtain ⟨hij, -⟩ | ⟨-, ht0, -⟩ | ⟨-, -, hj⟩ := halfPath_eq_halfPath_iff.mp hst
    · exact hne hij
    · rw [ht0] at ht
      exact absurd ht.1 (lt_irrefl 0)
    · exact hno (by rw [hj, P.other_other])

/-! ### Half-edges are closed embeddings -/

lemma isClosed_iff (S : Set P.Realization) :
    IsClosed S ↔ ∀ i : P.I, IsClosed (halfPath P i ⁻¹' S) := by
  rw [← isOpen_compl_iff, isOpen_iff]
  simp only [preimage_compl, isOpen_compl_iff]

@[simp]
lemma preimage_halfPath_image_self (i : P.I) (X : Set I) :
    halfPath P i ⁻¹' (halfPath P i '' X) = X :=
  (halfPath_injective P i).preimage_image X

private lemma preimage_halfPath_image_subset_endpoints {i j : P.I} (hne : j ≠ i) (X : Set I) :
    halfPath P j ⁻¹' (halfPath P i '' X) ⊆ {0, 1} := by
  rintro t ⟨c, hc, hct⟩
  obtain ⟨hij, -⟩ | ⟨-, ht0, -⟩ | ⟨-, ht1, -⟩ := halfPath_eq_halfPath_iff.mp hct
  · exact absurd hij.symm hne
  · exact Or.inl ht0
  · exact Or.inr ht1

lemma preimage_halfPath_image_eq_empty {i j : P.I} (hne : j ≠ i) {X : Set I} (h0X : 0 ∉ X)
    (h1X : 1 ∉ X) : halfPath P j ⁻¹' (halfPath P i '' X) = ∅ := by
  refine eq_empty_of_forall_notMem fun t ht ↦ ?_
  obtain ⟨c, hc, hct⟩ := ht
  obtain ⟨hij, -⟩ | ⟨hc0, -, -⟩ | ⟨hc1, -, -⟩ := halfPath_eq_halfPath_iff.mp hct
  · exact hne hij.symm
  · exact h0X (hc0 ▸ hc)
  · exact h1X (hc1 ▸ hc)

theorem isOpen_halfPath_image (i : P.I) {X : Set I} (h0X : 0 ∉ X) (h1X : 1 ∉ X) :
    IsOpen (halfPath P i '' X) ↔ IsOpen X := by
  rw [isOpen_iff]
  refine ⟨fun h ↦ ?_, fun h j ↦ ?_⟩
  · have h' : IsOpen ((halfPath P i) ⁻¹' (halfPath P i '' X)) := h i
    rwa [(halfPath_injective P i).preimage_image] at h'
  · by_cases hne : j = i
    · rw [hne]
      show IsOpen ((halfPath P i) ⁻¹' (halfPath P i '' X))
      rwa [(halfPath_injective P i).preimage_image]
    · rw [preimage_halfPath_image_eq_empty hne h0X h1X]
      exact isOpen_empty

theorem isClosedMap_halfPath (P : Presentation V E) (i : P.I) : IsClosedMap (halfPath P i) := by
  intro C hC
  rw [isClosed_iff]
  intro j
  by_cases hne : j = i
  · rw [hne]
    show IsClosed ((halfPath P i) ⁻¹' (halfPath P i '' C))
    rwa [(halfPath_injective P i).preimage_image]
  · exact (Set.Finite.subset (toFinite {0, 1})
      (preimage_halfPath_image_subset_endpoints hne C)).isClosed

/-- **Every** half-edge is a closed embedding.  The whole-edge model can only say this for an edge
that is not a loop; here the statement is unconditional, because a half-edge is never glued to
itself. -/
theorem isClosedEmbedding_halfPath (P : Presentation V E) (i : P.I) :
    IsClosedEmbedding (halfPath P i) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap (halfPath P i).continuous
    (halfPath_injective P i) (isClosedMap_halfPath P i)

/-- The path through an edge selected by one incidence of that edge.

This path first traverses the selected half-edge to the midpoint, then traverses the mate
half-edge backwards from the midpoint to its incident vertex. -/
def edgePathAt (P : Presentation V E) (a : P.IncidenceAt e) :
    Path (vertexMk P ⟨P.attach a.1, P.attach_mem a.1⟩)
      (vertexMk P ⟨P.attach (P.other a.1), P.attach_mem (P.other a.1)⟩) :=
  (halfPath P a.1).trans <| ((halfPath P (P.other a.1)).symm).cast (midpointMk_other P a.1).symm rfl

/-- Distinct half-edges have disjoint open parts.  Note this is a cleaner statement than the
whole-edge analogue: there is no exception for the two halves of one edge, because the shared
midpoint sits at parameter `1`, outside `Ioo`. -/
theorem disjoint_halfPath_Ioo_iff {i j : P.I} :
    Disjoint (halfPath P i '' Ioo 0 1) (halfPath P j '' Ioo 0 1) ↔ j ≠ i := by
  constructor
  · refine fun h hji ↦ ?_
    rw [hji] at h
    have hmem : halfPath P i unitInterval.half ∈ halfPath P i '' Ioo 0 1 :=
      ⟨unitInterval.half, ⟨unitInterval.zero_lt_half, unitInterval.half_lt_one⟩, rfl⟩
    exact h.notMem_of_mem_left hmem hmem
  · refine fun hne ↦ disjoint_left.2 ?_
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, hst⟩
    obtain ⟨hij, -⟩ | ⟨-, ht0, -⟩ | ⟨-, ht1, -⟩ := halfPath_eq_halfPath_iff.mp hst
    · exact hne hij
    · rw [ht0] at ht
      exact absurd ht.1 (lt_irrefl 0)
    · rw [ht1] at ht
      exact absurd ht.2 (lt_irrefl 1)

lemma midpointMk_notMem_halfPath_Ioo (i j : P.I) : midpointMk P i ∉ halfPath P j '' Ioo 0 1 := by
  rintro ⟨s, hs, hst⟩
  obtain ⟨-, hs1⟩ | ⟨-, h10, -⟩ | ⟨hs1, -, -⟩ := halfPath_eq_halfPath_iff.mp hst
  · rw [hs1] at hs
    exact absurd hs.2 (lt_irrefl 1)
  · exact one_ne_zero' h10
  · rw [hs1] at hs
    exact absurd hs.2 (lt_irrefl 1)

/-- The open part of a whole edge is injectively parametrised, for every edge including a loop.
The two halves meet only at the midpoint, which is the junction of the concatenation. -/
theorem edgePathAt_injOn_Ioo (P : Presentation V E) {e : E} (a : P.IncidenceAt e) :
    InjOn (edgePathAt P a) (Ioo 0 1) := by
  have hQint : (((halfPath P (P.other a.1)).symm).cast (midpointMk_other P a.1).symm rfl).Interior
      = halfPath P (P.other a.1) '' Ioo 0 1 := by
    rw [Path.cast_interior, Path.symm_interior]
    rfl
  rw [edgePathAt, Path.trans_injOn_ioo_iff]
  refine ⟨(halfPath_injective P a.1).injOn, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv h
    simp only [Path.cast_coe, Path.symm_apply] at h
    simpa [unitInterval.symm_symm] using congrArg σ (halfPath_injective P _ h)
  · exact midpointMk_notMem_halfPath_Ioo a.1 a.1
  · rw [hQint]
    exact midpointMk_notMem_halfPath_Ioo a.1 (P.other a.1)
  · rw [hQint]
    exact disjoint_halfPath_Ioo_iff.2 (P.other_ne a.1)

@[simp]
lemma edgePathAt_other_range (P : Presentation V E) (a : P.IncidenceAt e) :
    Set.range (edgePathAt P a.other) = Set.range (edgePathAt P a) := by
  have hrange (b : P.IncidenceAt e) :
      Set.range (edgePathAt P b) =
        Set.range (halfPath P b.1) ∪ Set.range (halfPath P (P.other b.1)) := by
    simp only [edgePathAt]
    rw [Path.trans_range]
    congr 1
    exact Path.symm_range (halfPath P (P.other b.1))
  rw [hrange, hrange, IncidenceAt.other_val]
  refine (union_comm _ _).trans ?_
  exact congrArg (· ∪ Set.range (halfPath P (P.other a.1)))
    (congrArg (fun j => Set.range (halfPath P j)) (P.other_other a.1))

/-- The intrinsic range of the edge represented by an incidence.  This is independent of which of
its two incidences is chosen. -/
def edgeRangeAt (P : Presentation V E) (a : P.IncidenceAt e) : Set P.Realization :=
  Set.range (halfPath P a.1) ∪ Set.range (halfPath P (P.other a.1))

@[simp]
lemma edgeRangeAt_other (P : Presentation V E) (a : P.IncidenceAt e) :
    edgeRangeAt P a.other = edgeRangeAt P a := by
  unfold edgeRangeAt
  simp only [IncidenceAt.other_val]
  exact (union_comm _ _).trans <| congrArg (· ∪ Set.range (halfPath P (P.other a.1)))
    (congrArg (fun j => Set.range (halfPath P j)) (P.other_other a.1))

/-- The intrinsic open edge in the half-edge model.  Each incident vertex (`t = 0`) is omitted,
while the common midpoint (`t = 1`) is retained. -/
def edgeInteriorAt (P : Presentation V E) (a : P.IncidenceAt e) : Set P.Realization :=
  halfPath P a.1 '' Ioc 0 1 ∪ halfPath P (P.other a.1) '' Ioc 0 1

@[simp]
lemma edgeInteriorAt_other (P : Presentation V E) (a : P.IncidenceAt e) :
    edgeInteriorAt P a.other = edgeInteriorAt P a := by
  unfold edgeInteriorAt
  simp only [IncidenceAt.other_val]
  exact (union_comm _ _).trans <| congrArg (· ∪ (halfPath P (P.other a.1) '' Ioc 0 1))
    (congrArg (fun j => halfPath P j '' Ioc 0 1) (P.other_other a.1))

/-! ### Classification of the points

Every point is a vertex or an interior point of exactly one edge.  `mem_edgeInteriorAt_halfPath_iff`
is the computation the rest of the section rests on. -/

/-- The points of the realization that are not vertices. -/
def edgeInteriorSet (P : Presentation V E) : Set P.Realization := (Set.range (vertexMk P))ᶜ

/-- A half-edge point lies on the open edge of `a` exactly when it belongs to that edge and is not
one of its endpoints.  Note the parameter condition is `Ioc`, not `Ioo`: the midpoint belongs to
the open edge, and is the point at which the two halves meet. -/
theorem mem_edgeInteriorAt_halfPath_iff (a : P.IncidenceAt e) (j : P.I) (t : I) :
    halfPath P j t ∈ edgeInteriorAt P a ↔ P.edgeMap j = e ∧ t ∈ Ioc 0 1 := by
  have key : ∀ (k : P.I) (s : I), P.edgeMap k = e → s ∈ Ioc 0 1 →
      halfPath P k s = halfPath P j t → P.edgeMap j = e ∧ t ∈ Ioc 0 1 := by
    intro k s hk hs hks
    obtain ⟨rfl, rfl⟩ | ⟨hs0, -, -⟩ | ⟨-, rfl, hj⟩ := halfPath_eq_halfPath_iff.mp hks
    · exact ⟨hk, hs⟩
    · exact absurd hs0 hs.1.ne'
    · exact ⟨by rw [hj, P.edgeMap_other]; exact hk, ⟨zero_lt_one_I, le_refl 1⟩⟩
  constructor
  · rintro (⟨s, hs, hst⟩ | ⟨s, hs, hst⟩)
    · exact key a.1 s a.2 hs hst
    · exact key (P.other a.1) s ((P.edgeMap_other a.1).trans a.2) hs hst
  rintro ⟨hj, ht⟩
  obtain rfl | rfl := P.eq_or_eq_other_of_edgeMap_eq (hj.trans a.2.symm)
  · exact Or.inl ⟨t, ht, rfl⟩
  exact Or.inr ⟨t, ht, rfl⟩

lemma vertexMk_notMem_edgeInteriorAt (v : V(P.toGraph)) (a : P.IncidenceAt e) :
    vertexMk P v ∉ edgeInteriorAt P a := by
  rintro (⟨s, hs, hst⟩ | ⟨s, hs, hst⟩) <;>
    exact absurd (vertexMk_eq_halfPath_iff.mp hst.symm).1 (ne_of_gt hs.1)

/-- An open edge depends only on the edge, not on which of its incidences names it. -/
lemma edgeInteriorAt_congr (a b : P.IncidenceAt e) :
    edgeInteriorAt P a = edgeInteriorAt P b := by
  obtain rfl | rfl := IncidenceAt.eq_or_eq_other a b
  · rfl
  exact (edgeInteriorAt_other P a).symm

private lemma isOpen_Ioc_zero_one : IsOpen (Ioc (0 : I) 1) := by
  have h : Ioc (0 : I) 1 = Subtype.val ⁻¹' Ioi (0 : ℝ) := by
    ext t
    simp only [mem_Ioc, mem_preimage, mem_Ioi, ← unitInterval.coe_pos]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, unitInterval.le_one t⟩⟩
  rw [h]
  exact isOpen_Ioi.preimage continuous_subtype_val

/-- An open edge is open in the whole realization, not merely in `edgeInteriorSet`.  The
whole-edge model can only state clopen-ness relative to the subspace. -/
theorem isOpen_edgeInteriorAt (a : P.IncidenceAt e) : IsOpen (edgeInteriorAt P a) := by
  rw [isOpen_iff]
  intro j
  by_cases hj : P.edgeMap j = e
  · have hpre : halfPath P j ⁻¹' edgeInteriorAt P a = Ioc 0 1 := by
      ext t
      rw [mem_preimage, mem_edgeInteriorAt_halfPath_iff]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hj, h⟩⟩
    rw [hpre]
    exact isOpen_Ioc_zero_one
  · have hpre : halfPath P j ⁻¹' edgeInteriorAt P a = ∅ := by
      ext t
      rw [mem_preimage, mem_edgeInteriorAt_halfPath_iff]
      simp only [mem_empty_iff_false, iff_false, not_and]
      exact fun h ↦ absurd h hj
    rw [hpre]
    exact isOpen_empty

/-- Two open edges are disjoint exactly when they are different edges. -/
theorem disjoint_edgeInteriorAt_iff {f : E} (a : P.IncidenceAt e) (b : P.IncidenceAt f) :
    Disjoint (edgeInteriorAt P a) (edgeInteriorAt P b) ↔ e ≠ f := by
  constructor
  · rintro h rfl
    have hmem : halfPath P a.1 1 ∈ edgeInteriorAt P a :=
      (mem_edgeInteriorAt_halfPath_iff a a.1 1).2 ⟨a.2, ⟨zero_lt_one_I, le_refl 1⟩⟩
    exact h.notMem_of_mem_left hmem (edgeInteriorAt_congr a b ▸ hmem)
  refine fun hne ↦ Set.disjoint_left.2 fun x hxa hxb ↦ ?_
  induction x using Quotient.inductionOn with | _ z =>
  obtain v | ⟨j, t⟩ := z
  · exact vertexMk_notMem_edgeInteriorAt v a hxa
  exact hne (((mem_edgeInteriorAt_halfPath_iff a j t).1 hxa).1.symm.trans
    ((mem_edgeInteriorAt_halfPath_iff b j t).1 hxb).1)

/-- The open edge is the interior of the whole-edge path through either of its incidences. -/
theorem interior_edgePathAt (a : P.IncidenceAt e) :
    (edgePathAt P a).Interior = edgeInteriorAt P a := by
  have himg : ∀ j : P.I,
      halfPath P j '' Ioc 0 1 = (halfPath P j).Interior ∪ {midpointMk P j} := by
    intro j
    rw [← Set.Ioo_union_right zero_lt_one_I, Set.image_union, Set.image_singleton, halfPath_one]
    rfl
  rw [edgePathAt, Path.trans_interior, Path.cast_interior, Path.symm_interior, edgeInteriorAt,
    himg a.1, himg (P.other a.1)]
  ext z
  simp only [mem_union, mem_singleton_iff, midpointMk_other]
  tauto

/-- Assemble a point of the realization from its index: either a vertex, or an edge together with
an interior parameter along it, read in the direction chosen by `O`. -/
def indexMk (O : P.Orientation) :
    V(P.toGraph) ⊕ E(P.toGraph) × Ioo (0 : I) 1 → P.Realization
  | .inl v => vertexMk P v
  | .inr (e, t) => edgePathAt P (O e) t.1

private lemma mem_edgeInteriorAt_indexMk (O : P.Orientation) (e : E(P.toGraph))
    (t : Ioo (0 : I) 1) : indexMk O (.inr (e, t)) ∈ edgeInteriorAt P (O e) := by
  rw [← interior_edgePathAt]
  exact ⟨t.1, t.2, rfl⟩

/-- Every point of the realization is a vertex or an interior point of exactly one edge, at a
parameter pinned down by the orientation.  The whole-edge model states only the disjunction
`exists_vertexMk_or_exists_edgePath`. -/
theorem bijective_indexMk (O : P.Orientation) : Bijective (indexMk O) := by
  constructor
  · rintro (v | ⟨e, t⟩) (w | ⟨f, s⟩) h
    · exact congrArg Sum.inl (vertexMk_inj.1 h)
    · refine absurd ?_ (vertexMk_notMem_edgeInteriorAt v (O f))
      rw [show vertexMk P v = indexMk O (.inl v) from rfl, h]
      exact mem_edgeInteriorAt_indexMk O f s
    · refine absurd ?_ (vertexMk_notMem_edgeInteriorAt w (O e))
      rw [show vertexMk P w = indexMk O (.inl w) from rfl, ← h]
      exact mem_edgeInteriorAt_indexMk O e t
    · have hef : e = f := by
        by_contra hne
        have hdisj := (disjoint_edgeInteriorAt_iff (O e) (O f)).2 fun hh ↦ hne (Subtype.ext hh)
        refine hdisj.notMem_of_mem_left (mem_edgeInteriorAt_indexMk O e t) ?_
        rw [h]
        exact mem_edgeInteriorAt_indexMk O f s
      subst hef
      have hts : t = s := Subtype.ext (edgePathAt_injOn_Ioo P (O e) t.2 s.2 h)
      rw [hts]
  intro x
  induction x using Quotient.inductionOn with | _ z =>
  obtain v | ⟨i, t⟩ := z
  · exact ⟨.inl v, rfl⟩
  by_cases ht0 : t = 0
  · refine ⟨.inl ⟨P.attach i, P.attach_mem i⟩, ?_⟩
    rw [show (⟦Sum.inr ⟨i, t⟩⟧ : P.Realization) = halfPath P i t from rfl, ht0]
    exact ((halfPath P i).source).symm
  have ht : t ∈ Ioc (0 : I) 1 := ⟨unitInterval.pos_iff_ne_zero.2 ht0, unitInterval.le_one t⟩
  have hmem :
      halfPath P i t ∈ edgeInteriorAt P (O ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩) := by
    rw [edgeInteriorAt_congr _ (⟨i, rfl⟩ : P.IncidenceAt (P.edgeMap i)),
      mem_edgeInteriorAt_halfPath_iff]
    exact ⟨rfl, ht⟩
  rw [← interior_edgePathAt] at hmem
  obtain ⟨s, hs, hse⟩ := hmem
  exact ⟨.inr (⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩, ⟨s, hs⟩), hse⟩

/-- The open edges cover exactly the non-vertex points. -/
theorem iUnion_edgeInteriorAt (O : P.Orientation) :
    ⋃ e : E(P.toGraph), edgeInteriorAt P (O e) = edgeInteriorSet P := by
  ext x
  simp only [mem_iUnion, edgeInteriorSet, mem_compl_iff, mem_range, not_exists]
  constructor
  · rintro ⟨e, hxe⟩ v rfl
    exact vertexMk_notMem_edgeInteriorAt v (O e) hxe
  intro hx
  obtain ⟨y, rfl⟩ := (bijective_indexMk O).2 x
  obtain v | ⟨e, t⟩ := y
  · exact absurd rfl (hx v)
  exact ⟨e, mem_edgeInteriorAt_indexMk O e t⟩

/-- An open edge is path-connected.  With `isOpen_edgeInteriorAt`, `disjoint_edgeInteriorAt_iff`
and `iUnion_edgeInteriorAt` this says the open edges are exactly the path components of
`edgeInteriorSet`. -/
theorem isPathConnected_edgeInteriorAt (a : P.IncidenceAt e) :
    IsPathConnected (edgeInteriorAt P a) := by
  rw [← interior_edgePathAt, Path.Interior]
  exact (unitInterval.isPathConnected_Ioo zero_lt_one_I).image (edgePathAt P a).continuous

/-! ### Connectivity

The realization decomposes over the components of the coarse graph.  `component` records which
one a point lies over; the two facts that drive everything else are that it is constant along
paths (`isClopen_preimage_component`) and that every point is joined to a vertex
(`exists_joined_vertexMk`). -/

/-- The component of the coarse graph that a point of the realization lies over.

A point is a vertex or a point of a half-edge; in the second case it lies over the vertex that
half-edge is attached to, and `Graph.walkable` names the component.  The content of the
definition is that this descends to the quotient: the two half-edges of an edge are attached to
the two ends of that edge, which are connected. -/
def component (P : Presentation V E) : P.Realization → Graph V E :=
  Quotient.lift
    (fun z ↦ match z with
      | .inl v => P.toGraph.walkable v.1
      | .inr p => P.toGraph.walkable (P.attach p.1)) <| by
    intro a b h
    induction h with
    | refl => rfl
    | rel x y hxy =>
      cases hxy with
      | vertex v => rfl
      | attach i => rfl
      | other i => exact (P.isLink_edgeMap_attach i).connBetween.walkable_eq_walkable
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ hxy hyz => exact hxy.trans hyz

@[simp]
lemma component_vertexMk (v : V(P.toGraph)) :
    component P (vertexMk P v) = P.toGraph.walkable v.1 := rfl

/-- Name this one: like every lemma in this file whose left-hand side is a coerced `Path`
application, it is not retrieved by a bare `simp`, only by `simp only [component_halfPath]`
or `rw`. -/
@[simp]
lemma component_halfPath (i : P.I) (t : I) :
    component P (halfPath P i t) = P.toGraph.walkable (P.attach i) := rfl

lemma component_mem_components (x : P.Realization) : component P x ∈ P.toGraph.Components := by
  rw [components_eq_walkable_image]
  induction x using Quotient.inductionOn with | _ z =>
  obtain v | ⟨i, t⟩ := z
  · exact ⟨v.1, v.2, rfl⟩
  exact ⟨P.attach i, P.attach_mem i, rfl⟩

/-- `component` is locally constant, in the strongest form: **every** preimage is clopen, not only
the fibres.  A half-edge lies over a single vertex, so each `halfPath` preimage is `univ` or `∅`,
and the `0`-skeleton is discrete. -/
theorem isClopen_preimage_component (S : Set (Graph V E)) : IsClopen (component P ⁻¹' S) := by
  have key : ∀ i : P.I, IsClopen (halfPath P i ⁻¹' (component P ⁻¹' S)) := by
    intro i
    by_cases h : P.toGraph.walkable (P.attach i) ∈ S
    · convert isClopen_univ
      ext t
      exact iff_of_true h (mem_univ t)
    · convert isClopen_empty
      ext t
      exact iff_of_false h (notMem_empty t)
  exact ⟨(isClosed_iff _).2 fun i ↦ (key i).1, (isOpen_iff _).2 fun i ↦ (key i).2⟩

private lemma component_apply_eq {x y : P.Realization} (γ : Path x y) (t : I) :
    component P (γ t) = component P x := by
  have hcl : IsClopen (γ ⁻¹' (component P ⁻¹' {component P x})) :=
    (isClopen_preimage_component _).preimage γ.continuous
  have h0 : (0 : I) ∈ γ ⁻¹' (component P ⁻¹' {component P x}) := by simp [γ.source]
  have ht : t ∈ γ ⁻¹' (component P ⁻¹' {component P x}) := by
    rw [hcl.eq_univ ⟨0, h0⟩]
    exact mem_univ t
  simpa using ht

private lemma joined_vertexMk_of_isWalk {w : WList V E} (hw : P.toGraph.IsWalk w) :
    Joined (vertexMk P ⟨w.first, hw.first_mem⟩) (vertexMk P ⟨w.last, hw.last_mem⟩) := by
  induction hw with
  | @nil x hx => exact Joined.refl _
  | @cons x e w hw' hlink ih =>
    refine Joined.trans ?_ (by simpa [WList.last_cons] using ih)
    obtain ⟨i, -, hx, hy⟩ := hlink
    exact ⟨(edgePathAt P (⟨i, rfl⟩ : P.IncidenceAt (P.edgeMap i))).cast
      (congrArg (vertexMk P) (Subtype.ext hx.symm))
      (congrArg (vertexMk P) (Subtype.ext hy.symm))⟩

/-- Every point of the realization is joined to a vertex: the vertices meet every path component.
This is what lets statements about arbitrary points reduce to statements about vertices, and it is
why the whole-edge model's `Quotient.ind` plumbing is not needed here. -/
theorem exists_joined_vertexMk (x : P.Realization) :
    ∃ v : V(P.toGraph), Joined (vertexMk P v) x := by
  induction x using Quotient.inductionOn with | _ z =>
  obtain v | ⟨i, t⟩ := z
  · exact ⟨v, Joined.refl _⟩
  refine ⟨⟨P.attach i, P.attach_mem i⟩, ⟨((halfPath P i).truncate 0 t).cast ?_ ?_⟩⟩
  · rw [min_eq_left t.2.1]
    exact ((halfPath P i).extend_zero).symm
  · exact ((halfPath P i).extend_extends' t).symm

/-- Two points of the realization are joined exactly when they lie over the same component of the
coarse graph.  This is stated for arbitrary points; the whole-edge model has only the four
one-directional lemmas about vertices, which are corollaries below. -/
theorem joined_iff_component_eq {x y : P.Realization} :
    Joined x y ↔ component P x = component P y := by
  refine ⟨fun ⟨γ⟩ ↦ ?_, fun h ↦ ?_⟩
  · simpa using (component_apply_eq γ 1).symm
  obtain ⟨u, hu⟩ := exists_joined_vertexMk x
  obtain ⟨v, hv⟩ := exists_joined_vertexMk y
  have key : ∀ {z : P.Realization} {w : V(P.toGraph)}, Joined (vertexMk P w) z →
      component P z = P.toGraph.walkable w.1 := by
    rintro z w ⟨γ⟩
    have hz := component_apply_eq γ 1
    rw [γ.target] at hz
    simpa using hz
  have hwalk : P.toGraph.walkable u.1 = P.toGraph.walkable v.1 := by
    rw [← key hu, ← key hv, h]
  have huv : P.toGraph.ConnBetween u.1 v.1 :=
    (mem_walkable_iff.1 ((walkable_eq_walkable_iff_mem u.2).1 hwalk)).symm
  obtain ⟨w, hw, hf, hl⟩ := huv
  have h1 : (⟨w.first, hw.first_mem⟩ : V(P.toGraph)) = u := Subtype.ext hf
  have h2 : (⟨w.last, hw.last_mem⟩ : V(P.toGraph)) = v := Subtype.ext hl
  refine hu.symm.trans (Joined.trans ?_ hv)
  rw [← h1, ← h2]
  exact joined_vertexMk_of_isWalk hw

/-- Connected components and path components of the realization coincide, and both are the fibres
of `component`.  A fibre is clopen, so it contains the connected component of each of its points;
it is path-connected by `joined_iff_component_eq`, so it is contained in it. -/
theorem connectedComponent_eq (x : P.Realization) :
    connectedComponent x = component P ⁻¹' {component P x} := by
  refine subset_antisymm ((isClopen_preimage_component _).connectedComponent_subset rfl) ?_
  have hpc : IsPathConnected (component P ⁻¹' {component P x}) := by
    refine ⟨x, rfl, fun y hy ↦ ?_⟩
    obtain ⟨γ⟩ := joined_iff_component_eq.2 (mem_singleton_iff.1 hy).symm
    exact ⟨γ, fun t ↦ component_apply_eq γ t⟩
  exact hpc.isConnected.isPreconnected.subset_connectedComponent rfl

/-- Two vertices are joined in the realization exactly when they are connected in the graph.  The
whole-edge model has only the forward implication, split across three lemmas. -/
theorem joined_vertexMk_iff {u v : V(P.toGraph)} :
    Joined (vertexMk P u) (vertexMk P v) ↔ P.toGraph.ConnBetween u.1 v.1 := by
  rw [joined_iff_component_eq, component_vertexMk, component_vertexMk,
    walkable_eq_walkable_iff_mem u.2, mem_walkable_iff]
  exact connBetween_comm

/-- The realization is path-connected exactly when the graph is connected.  The whole-edge model
has only the forward implication. -/
theorem pathConnectedSpace_iff : PathConnectedSpace P.Realization ↔ P.toGraph.Connected := by
  rw [connected_iff]
  refine ⟨fun h ↦ ⟨?_, fun a b ha hb ↦ ?_⟩, fun ⟨⟨v0, hv0⟩, hpre⟩ ↦ ?_⟩
  · obtain ⟨x⟩ := h.nonempty
    obtain ⟨v, -⟩ := exists_joined_vertexMk x
    exact ⟨v.1, v.2⟩
  · exact (joined_vertexMk_iff (u := ⟨a, ha⟩) (v := ⟨b, hb⟩)).1
      (PathConnectedSpace.joined _ _)
  refine ⟨⟨vertexMk P ⟨v0, hv0⟩⟩, fun x y ↦ ?_⟩
  obtain ⟨u, hu⟩ := exists_joined_vertexMk x
  obtain ⟨w, hw⟩ := exists_joined_vertexMk y
  exact hu.symm.trans ((joined_vertexMk_iff.2 (hpre u.1 w.1 u.2 w.2)).trans hw)

end Realization

/-! ## Change of incidence presentation -/

namespace Equiv

/-- Identity-on-labels equivalence of the vertex subtypes. -/
def vertexEquiv (F : P.Equiv Q) : V(P.toGraph) ≃ V(Q.toGraph) where
  toFun v := ⟨v.1, by
    change v.1 ∈ Q.vertexSet
    rw [← F.vertexSet_eq]
    exact v.2⟩
  invFun v := ⟨v.1, by
    change v.1 ∈ P.vertexSet
    rw [F.vertexSet_eq]
    exact v.2⟩
  left_inv v := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

/-- Relabel incidences in the pre-realization and leave interval coordinates unchanged. -/
def preMap (F : P.Equiv Q) : P.PreRealization → Q.PreRealization
  | .inl v => .inl (vertexEquiv F v)
  | .inr p => .inr ⟨F.incEquiv p.1, p.2⟩

@[simp]
lemma preMap_inl (F : P.Equiv Q) (v : V(P.toGraph)) :
    F.preMap (.inl v) = .inl (F.vertexEquiv v) := rfl

@[simp]
lemma preMap_inr (F : P.Equiv Q) (i : P.I) (t : unitInterval) :
    F.preMap (.inr ⟨i, t⟩) = .inr ⟨F.incEquiv i, t⟩ := rfl

lemma continuous_preMap (F : P.Equiv Q) : Continuous F.preMap := by
  rw [continuous_sum_dom]
  constructor
  · exact continuous_inl.comp continuous_of_discreteTopology
  exact continuous_sigma_iff.mpr fun i ↦ continuous_inr.comp
    <| @continuous_sigmaMk Q.I (fun _ : Q.I ↦ unitInterval) _ (F.incEquiv i)

lemma map_glueRelAux (F : P.Equiv Q) {x y : P.PreRealization}
    (h : GlueRelAux P x y) : GlueRelAux Q (F.preMap x) (F.preMap y) := by
  cases h with
  | vertex v => exact GlueRelAux.vertex (F.vertexEquiv v)
  | attach i =>
    have hv : F.vertexEquiv ⟨P.attach i, P.attach_mem i⟩ =
        ⟨Q.attach (F.incEquiv i), Q.attach_mem (F.incEquiv i)⟩ :=
      Subtype.ext <| (F.vertex_eq i).symm
    simpa only [preMap_inl, preMap_inr, hv] using GlueRelAux.attach (F.incEquiv i)
  | other i =>
    simpa only [preMap_inr, F.map_other] using GlueRelAux.other (F.incEquiv i)

lemma map_glueRel (F : P.Equiv Q) {x y : P.PreRealization}
    (h : (glueRel P) x y) : (glueRel Q) (F.preMap x) (F.preMap y) := by
  induction h with
  | refl => exact EqvGen.refl _
  | rel x y hxy => exact EqvGen.rel _ _ (F.map_glueRelAux hxy)
  | symm x y _ ih => exact EqvGen.symm _ _ ih
  | trans x y z _ _ hxy hyz => exact EqvGen.trans _ _ _ hxy hyz

/-- Relabel incidences in the realization. -/
def realizationMap (F : P.Equiv Q) : P.Realization → Q.Realization :=
  Quotient.map' F.preMap fun _ _ h ↦ F.map_glueRel h

lemma continuous_realizationMap (F : P.Equiv Q) : Continuous F.realizationMap :=
  F.continuous_preMap.quotient_map' fun _ _ h ↦ F.map_glueRel h

@[simp]
lemma realizationMap_vertexMk (F : P.Equiv Q) (v : V(P.toGraph)) :
    F.realizationMap (Realization.vertexMk P v) = Realization.vertexMk Q (F.vertexEquiv v) :=
  rfl

@[simp]
lemma realizationMap_midpointMk (F : P.Equiv Q) (i : P.I) :
    F.realizationMap (Realization.midpointMk P i) = Realization.midpointMk Q (F.incEquiv i) :=
  rfl

@[simp]
lemma realizationMap_halfPath (F : P.Equiv Q) (i : P.I) (t : unitInterval) :
    F.realizationMap (Realization.halfPath P i t) = Realization.halfPath Q (F.incEquiv i) t :=
  rfl

private lemma preMap_symm_apply (F : P.Equiv Q) (x : P.PreRealization) :
    F.symm.preMap (F.preMap x) = x := by
  cases x with
  | inl v => exact congrArg Sum.inl <| Subtype.ext rfl
  | inr p =>
    cases p with
    | mk i t =>
      simp only [preMap]
      exact congrArg (fun j : P.I => Sum.inr (⟨j, t⟩ : (_ : P.I) × unitInterval))
        <| F.incEquiv.symm_apply_apply i

private lemma preMap_apply_symm (F : P.Equiv Q) (x : Q.PreRealization) :
    F.preMap (F.symm.preMap x) = x := by
  cases x with
  | inl v => exact congrArg Sum.inl <| Subtype.ext rfl
  | inr p =>
    cases p with
    | mk i t =>
      simp only [preMap]
      exact congrArg (fun j : Q.I =>
        Sum.inr (⟨j, t⟩ : (_ : Q.I) × unitInterval)) <| F.incEquiv.apply_symm_apply i

/-- Presentation equivalence gives a homeomorphism of the half-edge realizations. -/
def realizationHomeomorph (F : P.Equiv Q) : P.Realization ≃ₜ Q.Realization where
  toFun := F.realizationMap
  invFun := F.symm.realizationMap
  left_inv z := by
    induction z using Quotient.inductionOn with | _ x =>
    change Quotient.mk' (F.symm.preMap (F.preMap x)) = Quotient.mk' x
    rw [F.preMap_symm_apply]
  right_inv z := by
    induction z using Quotient.inductionOn with | _ x =>
    change Quotient.mk' (F.preMap (F.symm.preMap x)) = Quotient.mk' x
    rw [F.preMap_apply_symm]
  continuous_toFun := F.continuous_realizationMap
  continuous_invFun := F.symm.continuous_realizationMap

/-! ### Functoriality

`Realization` is a functor from the groupoid of presentations and incidence relabellings to
topological spaces.  This is the whole of the canonical content of change of presentation: see
`realizationHomeomorph_loopSwap_ne_refl` for why nothing stronger, indexed by an equality of
coarse graphs rather than by a relabelling, can hold. -/

@[simp]
lemma realizationHomeomorph_apply (F : P.Equiv Q) (x : P.Realization) :
    F.realizationHomeomorph x = F.realizationMap x := rfl

@[simp]
lemma realizationHomeomorph_symm_apply (F : P.Equiv Q) (x : Q.Realization) :
    F.realizationHomeomorph.symm x = F.symm.realizationMap x := rfl

@[simp]
lemma realizationMap_refl (P : Presentation V E) :
    (Presentation.Equiv.refl P).realizationMap = id := by
  funext z
  induction z using Quotient.inductionOn with | _ x =>
  obtain v | ⟨i, t⟩ := x <;> rfl

lemma realizationMap_trans (F : P.Equiv Q) (F' : Q.Equiv R) :
    (F.trans F').realizationMap = F'.realizationMap ∘ F.realizationMap := by
  funext z
  induction z using Quotient.inductionOn with | _ x =>
  obtain v | ⟨i, t⟩ := x <;> rfl

@[simp]
lemma realizationHomeomorph_refl (P : Presentation V E) :
    (Presentation.Equiv.refl P).realizationHomeomorph = Homeomorph.refl P.Realization :=
  Homeomorph.ext fun z ↦ congrFun (realizationMap_refl P) z

@[simp]
lemma realizationHomeomorph_trans (F : P.Equiv Q) (F' : Q.Equiv R) :
    (F.trans F').realizationHomeomorph = F.realizationHomeomorph.trans F'.realizationHomeomorph :=
  Homeomorph.ext fun z ↦ congrFun (realizationMap_trans F F') z

@[simp]
lemma realizationHomeomorph_symm (F : P.Equiv Q) :
    F.symm.realizationHomeomorph = F.realizationHomeomorph.symm :=
  Homeomorph.ext fun _ ↦ rfl

end Equiv

open Realization in
/-- Reflecting a loop is a **nontrivial** self-homeomorphism of the realization.

So the fibres of `toGraph` are not rigid, and a homeomorphism between the realizations of two
presentations of the same coarse graph is genuine extra data: it is not determined by
`P.toGraph = Q.toGraph`.  This is the reason the functoriality above is indexed by
`Presentation.Equiv` rather than by an equality of coarse graphs, and the reason
`Presentation.homeomorphOfToGraphEq` can only be a choice. -/
theorem realizationHomeomorph_loopSwap_ne_refl (P : Presentation V E) (i : P.I)
    (h : P.attach (P.other i) = P.attach i) :
    (P.loopSwap i h).realizationHomeomorph ≠ Homeomorph.refl P.Realization := by
  intro hEq
  have happ := congrArg
    (fun f : P.Realization ≃ₜ P.Realization ↦ f (halfPath P i unitInterval.half)) hEq
  simp only [Equiv.realizationHomeomorph_apply, Equiv.realizationMap_halfPath,
    Homeomorph.refl_apply, id_eq] at happ
  rw [loopSwap_incEquiv_self] at happ
  have hhalf : unitInterval.half ∈ Ioo (0 : I) 1 :=
    ⟨unitInterval.zero_lt_half, unitInterval.half_lt_one⟩
  exact ((disjoint_halfPath_Ioo_iff (i := i) (j := P.other i)).2 (P.other_ne i)).notMem_of_mem_left
    ⟨unitInterval.half, hhalf, rfl⟩ ⟨unitInterval.half, hhalf, happ⟩

end Presentation
end Graph
