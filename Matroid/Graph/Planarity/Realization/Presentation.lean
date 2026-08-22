module

public import Matroid.Graph.Presentation.Quotient
public import Matroid.Graph.Presentation.Orientation
public import Matroid.ForMathlib.Topology.Path
public import Mathlib.Topology.Constructions

/-!
# Incidence-presentation backend for graph realization

This is an implementation prototype, not intended as public API.

The public mathematical object should remain `Graph.Realization`.  The point of this file is to
provide the natural presentation-level backend from which that public object can be implemented:
one half-interval for each incidence, with its `0` endpoint glued to the incident vertex and its
`1` endpoint glued to the `1` endpoint of the mate incidence.

When this is folded into `Planarity/Realization/Basic.lean`, the declarations in
`Presentation.RealizationModel` should be made private/internal and only the graph-level facade
should remain public.
-/

@[expose] public noncomputable section

open Set Function TopologicalSpace Topology Sum Path Relation
open scoped unitInterval

namespace Graph.Presentation

/- Internal realization model attached to an incidence presentation.

This namespace is intentionally verbose so that it can be prototyped in a separate file.  In the
final realization module it should become private implementation detail. -/

variable {V E : Type*} {P Q : Presentation V E} {e : E} {i j : P.I} {t : I}

/-- The vertex part of the realization is discrete, exactly as in the current graph realization. -/
local instance (P : Presentation V E) : TopologicalSpace V(P.toGraph) := ⊥
local instance (P : Presentation V E) : DiscreteTopology V(P.toGraph) where
  eq_bot := rfl

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

/-- The path through an edge selected by one incidence of that edge.

This path first traverses the selected half-edge to the midpoint, then traverses the mate
half-edge backwards from the midpoint to its incident vertex. -/
def edgePathAt (P : Presentation V E) (a : P.IncidenceAt e) :
    Path (vertexMk P ⟨P.attach a.1, P.attach_mem a.1⟩)
      (vertexMk P ⟨P.attach (P.other a.1), P.attach_mem (P.other a.1)⟩) :=
  (halfPath P a.1).trans <| ((halfPath P (P.other a.1)).symm).cast (midpointMk_other P a.1).symm rfl

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

end Equiv

end Presentation
end Graph
