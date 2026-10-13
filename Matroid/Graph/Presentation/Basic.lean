module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Incidence presentations of multigraphs

A `Graph.Presentation V I E` is the incidence-rich object lying above the coarse multigraph
`Graph V E`.

Every element of `I` is an actual incidence.  The fixed-point-free involution `P.other`
pairs the two incidences belonging to an edge. The fields `edgeMap_other` and `edgeMap_eq`
say precisely that an edge fibre consists of `i` and `P.other i`.

The forgetful map `Presentation.toGraph` discards the names of incidences.  In
`Presentation.Quotient` we prove that its fibres are exactly incidence relabellings, so the
current `Graph V E` is the coarse quotient of presentations.
-/

@[expose] public section

open Set Function Classical

universe uV uI uE

namespace Graph

/-- An incidence presentation of a multigraph on ambient vertex and edge types `V` and `E`.

`I` is the type of incidences, with no unused incidence labels. The involution `other` exchanges
the two incidences of an edge.
-/
structure Presentation (V : Type uV) (I : Type uI) (E : Type uE) where
  /-- The vertices present in the presentation. -/
  vertexSet : Set V
  /-- The vertex incident with an incidence. -/
  attach : I → V
  /-- The edge incident with an incidence. -/
  edgeMap : I → E
  /-- Every incidence is attached to a vertex of the presentation. -/
  attach_mem : ∀ i, attach i ∈ vertexSet
  /-- The other incidence of the same edge. -/
  other : I → I
  /-- The two incidences of an edge are distinct, including for a loop. -/
  other_ne : ∀ i, other i ≠ i
  /-- The other incidence is associated with the same edge. -/
  edgeMap_other : ∀ i, edgeMap (other i) = edgeMap i
  /-- Every incidence of an edge is one of its two paired incidences. -/
  edgeMap_eq : ∀ i j, edgeMap i = edgeMap j → j = i ∨ j = other i

namespace Presentation

variable {V : Type uV} {I : Type uI} {E : Type uE} {P Q R : Presentation V I E}
  {i j : I} {e : E} {x y : V}

attribute [simp] other_ne edgeMap_other

lemma other_involutive (P : Presentation V I E) : Function.Involutive P.other := fun i ↦
  ((P.edgeMap_eq (P.other i) i (P.edgeMap_other i)).resolve_left (P.other_ne i).symm).symm

@[simp]
lemma other_other (P : Presentation V I E) (i : I) : P.other (P.other i) = i :=
  P.other_involutive i

lemma edgeMap_eq_iff (P : Presentation V I E) (i j : I) :
    P.edgeMap i = P.edgeMap j ↔ j = i ∨ j = P.other i := by
  refine ⟨P.edgeMap_eq i j, ?_⟩
  rintro (rfl | rfl)
  · rfl
  exact (P.edgeMap_other i).symm

lemma eq_or_eq_other_of_edgeMap_eq (P : Presentation V I E) {i j : I}
    (h : P.edgeMap j = P.edgeMap i) : j = i ∨ j = P.other i :=
  (P.edgeMap_eq_iff i j).1 h.symm

lemma eq_or_other_eq_of_edgeMap_eq (P : Presentation V I E) {i j : I}
    (h : P.edgeMap i = P.edgeMap j) : i = j ∨ P.other i = j := by
  obtain rfl | hji := (P.edgeMap_eq_iff i j).1 h
  · exact Or.inl rfl
  exact Or.inr hji.symm

/-- The edge set of a presentation is the range of its incidence-to-edge map. -/
def edgeSet (P : Presentation V I E) : Set E := Set.range P.edgeMap

@[simp]
lemma mem_edgeSet_iff {P : Presentation V I E} {e : E} : e ∈ P.edgeSet ↔ ∃ i : I, P.edgeMap i = e :=
  Iff.rfl

lemma edgeMap_mem_edgeSet (P : Presentation V I E) (i : I) : P.edgeMap i ∈ P.edgeSet :=
  ⟨i, rfl⟩

/-- `V(P)` denotes the `vertexSet` of a presentation `P`. -/
scoped notation "V(" P ")" => Graph.Presentation.vertexSet P

/-- `E(P)` denotes the `edgeSet` of a presentation `P`. -/
scoped notation "E(" P ")" => Graph.Presentation.edgeSet P

/-- The two-element incidence fibre over an ambient edge label `e`.

This definition makes sense even when `e` is not an edge of the presentation; in that case the
fibre is empty. -/
abbrev IncidenceAt (P : Presentation V I E) (e : E) := {i : I // P.edgeMap i = e}

/-- Binary endpoint relation induced by a presentation. -/
def IsLink (P : Presentation V I E) (e : E) (x y : V) : Prop :=
  ∃ i : I, P.edgeMap i = e ∧ P.attach i = x ∧ P.attach (P.other i) = y

lemma IsLink.symm {P : Presentation V I E} {e : E} {x y : V} (h : P.IsLink e x y) :
    P.IsLink e y x := by
  obtain ⟨i, rfl, rfl, rfl⟩ := h
  exact ⟨P.other i, by simp, rfl, by simp⟩

lemma IsLink.left_eq_or_eq {P : Presentation V I E} {e : E} {x y v w : V}
    (h : P.IsLink e x y) (h' : P.IsLink e v w) : x = v ∨ x = w := by
  obtain ⟨i, hiE, rfl, rfl⟩ := h
  obtain ⟨j, hjE, rfl, rfl⟩ := h'
  obtain rfl | rfl := (P.edgeMap_eq_iff i j).1 (hiE.trans hjE.symm)
  · exact Or.inl rfl
  exact Or.inr (by simp)

/-- Forget the names of incidences and retain only the ordinary undirected graph. -/
@[simps]
def toGraph (P : Presentation V I E) : Graph V E where
  vertexSet := P.vertexSet
  IsLink := P.IsLink
  edgeSet := P.edgeSet
  isLink_symm := fun _ _ ↦ ⟨fun _ _ h ↦ h.symm⟩
  eq_or_eq_of_isLink_of_isLink := fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h'
  edge_mem_iff_exists_isLink e := by
    refine ⟨?_, fun ⟨x, y, i, hi, _, _⟩ ↦ ⟨i, hi⟩⟩
    rintro ⟨i, rfl⟩
    exact ⟨P.attach i, P.attach (P.other i), i, rfl, rfl, rfl⟩
  left_mem_of_isLink e x y := by
    rintro ⟨i, -, rfl, -⟩
    exact P.attach_mem i

lemma isLink_edgeMap_attach (P : Presentation V I E) (i : I) :
    P.toGraph.IsLink (P.edgeMap i) (P.attach i) (P.attach (P.other i)) :=
  ⟨i, rfl, rfl, rfl⟩

end Presentation

end Graph
