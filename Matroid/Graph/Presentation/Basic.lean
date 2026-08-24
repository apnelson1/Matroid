module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Incidence presentations of multigraphs

A `Graph.Presentation V E` is the incidence-rich object lying above the coarse multigraph
`Graph V E`.

Every element of `P.I` is an actual incidence.  The fixed-point-free involution `P.other`
pairs the two incidences belonging to an edge.  The field `edgeMap_eq_iff` says precisely that
an edge fibre consists of `i` and `P.other i`.

The forgetful map `Presentation.toGraph` discards the names of incidences.  In
`Presentation.Quotient` we prove that its fibres are exactly incidence relabellings, so the
current `Graph V E` is the coarse quotient of presentations.
-/

@[expose] public section

open Set Function Classical

universe uV uE

namespace Graph

/-- An incidence presentation of a multigraph on ambient vertex and edge types `V` and `E`.

`I` is the type of incidences. Every incidence is active: there is deliberately no ambient set
of unused incidence labels. The involution `other` exchanges the two incidences of an edge.
-/
structure Presentation (V : Type uV) (E : Type uE) where
  /-- The incidence type. -/
  I : Type (max uV uE)
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
  /-- Taking the other incidence twice gives the original incidence. -/
  other_involutive : Function.Involutive other
  /-- The two incidences of an edge are distinct, including for a loop. -/
  other_ne : ∀ i, other i ≠ i
  /-- The fibre of `edgeMap` through `i` consists exactly of `i` and `other i`. -/
  edgeMap_eq_iff : ∀ i j, edgeMap i = edgeMap j ↔ j = i ∨ j = other i

namespace Presentation

variable {V : Type uV} {E : Type uE} {P Q R : Presentation V E} {i j : P.I} {e : E} {x y : V}

attribute [simp] other_ne other_ne

@[simp]
lemma other_other (P : Presentation V E) (i : P.I) : P.other (P.other i) = i :=
  P.other_involutive i

@[simp]
lemma edgeMap_other (P : Presentation V E) (i : P.I) : P.edgeMap (P.other i) = P.edgeMap i :=
  (P.edgeMap_eq_iff i (P.other i)).2 (Or.inr rfl) |>.symm

lemma eq_or_eq_other_of_edgeMap_eq (P : Presentation V E) {i j : P.I}
    (h : P.edgeMap j = P.edgeMap i) : j = i ∨ j = P.other i :=
  (P.edgeMap_eq_iff i j).1 h.symm

lemma eq_or_other_eq_of_edgeMap_eq (P : Presentation V E) {i j : P.I}
    (h : P.edgeMap i = P.edgeMap j) : i = j ∨ P.other i = j := by
  obtain rfl | hji := (P.edgeMap_eq_iff i j).1 h
  · exact Or.inl rfl
  exact Or.inr hji.symm

/-- The edge set of a presentation is the range of its incidence-to-edge map. -/
def edgeSet (P : Presentation V E) : Set E := Set.range P.edgeMap

@[simp]
lemma mem_edgeSet_iff {P : Presentation V E} {e : E} : e ∈ P.edgeSet ↔ ∃ i : P.I, P.edgeMap i = e :=
  Iff.rfl

lemma edgeMap_mem_edgeSet (P : Presentation V E) (i : P.I) : P.edgeMap i ∈ P.edgeSet :=
  ⟨i, rfl⟩

/-- The two-element incidence fibre over an ambient edge label `e`.

This definition makes sense even when `e` is not an edge of the presentation; in that case the
fibre is empty. -/
abbrev IncidenceAt (P : Presentation V E) (e : E) := {i : P.I // P.edgeMap i = e}

/-- Binary endpoint relation induced by a presentation. -/
def IsLink (P : Presentation V E) (e : E) (x y : V) : Prop :=
  ∃ i : P.I, P.edgeMap i = e ∧ P.attach i = x ∧ P.attach (P.other i) = y

lemma IsLink.symm {P : Presentation V E} {e : E} {x y : V} (h : P.IsLink e x y) :
    P.IsLink e y x := by
  obtain ⟨i, rfl, rfl, rfl⟩ := h
  exact ⟨P.other i, by simp, rfl, by simp⟩

lemma IsLink.left_eq_or_eq {P : Presentation V E} {e : E} {x y v w : V}
    (h : P.IsLink e x y) (h' : P.IsLink e v w) : x = v ∨ x = w := by
  obtain ⟨i, hiE, rfl, rfl⟩ := h
  obtain ⟨j, hjE, rfl, rfl⟩ := h'
  obtain rfl | rfl := (P.edgeMap_eq_iff i j).1 (hiE.trans hjE.symm)
  · exact Or.inl rfl
  exact Or.inr (by simp)

/-- Forget the names of incidences and retain only the ordinary undirected graph. -/
def toGraph (P : Presentation V E) : Graph V E where
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

@[simp]
lemma toGraph_vertexSet (P : Presentation V E) : P.toGraph.vertexSet = P.vertexSet := rfl

@[simp]
lemma toGraph_edgeSet (P : Presentation V E) : P.toGraph.edgeSet = P.edgeSet := rfl

@[simp]
lemma toGraph_isLink {P : Presentation V E} {e : E} {x y : V} :
    P.toGraph.IsLink e x y ↔ P.IsLink e x y := Iff.rfl

lemma isLink_edgeMap_attach (P : Presentation V E) (i : P.I) :
    P.toGraph.IsLink (P.edgeMap i) (P.attach i) (P.attach (P.other i)) :=
  ⟨i, rfl, rfl, rfl⟩

/-- An incidence relabelling between presentations on the same ambient vertex and edge types.

The vertex and edge labels are fixed; only incidence labels are allowed to move. -/
protected structure Equiv (P Q : Presentation V E) where
  vertexSet_eq : P.vertexSet = Q.vertexSet
  incEquiv : P.I ≃ Q.I
  edge_eq : ∀ i, Q.edgeMap (incEquiv i) = P.edgeMap i
  vertex_eq : ∀ i, Q.attach (incEquiv i) = P.attach i

attribute [simp, grind =] Equiv.edge_eq Equiv.vertex_eq

namespace Equiv

@[simp, grind =]
lemma map_other (F : P.Equiv Q) (i : P.I) : F.incEquiv (P.other i) = Q.other (F.incEquiv i) := by
  have he : Q.edgeMap (F.incEquiv i) = Q.edgeMap (F.incEquiv (P.other i)) := by
    rw [F.edge_eq, F.edge_eq, P.edgeMap_other]
  obtain hEq | hOther := (Q.edgeMap_eq_iff (F.incEquiv i) (F.incEquiv (P.other i))).1 he
  · exact (P.other_ne i (F.incEquiv.injective hEq)).elim
  exact hOther

protected def refl (P : Presentation V E) : P.Equiv P where
  vertexSet_eq := rfl
  incEquiv := _root_.Equiv.refl _
  edge_eq := fun _ ↦ rfl
  vertex_eq := fun _ ↦ rfl

protected def symm (F : P.Equiv Q) : Q.Equiv P where
  vertexSet_eq := F.vertexSet_eq.symm
  incEquiv := F.incEquiv.symm
  edge_eq := by
    intro j
    simpa using (F.edge_eq (F.incEquiv.symm j)).symm
  vertex_eq := by
    intro j
    simpa using (F.vertex_eq (F.incEquiv.symm j)).symm

protected def trans (F : P.Equiv Q) (F' : Q.Equiv R) : P.Equiv R where
  vertexSet_eq := F.vertexSet_eq.trans F'.vertexSet_eq
  incEquiv := F.incEquiv.trans F'.incEquiv
  edge_eq i := by
    simp only [Equiv.trans_apply]
    rw [F'.edge_eq, F.edge_eq]
  vertex_eq i := by
    simp only [Equiv.trans_apply]
    rw [F'.vertex_eq, F.vertex_eq]

lemma edgeSet_eq (F : P.Equiv Q) : P.edgeSet = Q.edgeSet := by
  ext e
  constructor <;> rintro ⟨i, rfl⟩
  · exact ⟨F.incEquiv i, F.edge_eq i⟩
  refine ⟨F.incEquiv.symm i, ?_⟩
  simpa using (F.edge_eq (F.incEquiv.symm i)).symm

/-- Incidence equivalence preserves the coarse graph exactly. -/
theorem toGraph_eq (F : P.Equiv Q) : P.toGraph = Q.toGraph := by
  refine Graph.ext F.vertexSet_eq fun e x y ↦ ⟨fun ⟨i, hiE, hiV, hiO⟩ ↦ ⟨F.incEquiv i, ?_, ?_, ?_⟩,
    fun ⟨i, hiE, hiV, hiO⟩ ↦ ⟨F.symm.incEquiv i, ?_, ?_, ?_⟩⟩
  · rw [F.edge_eq, hiE]
  · rw [F.vertex_eq, hiV]
  · rw [← F.map_other, F.vertex_eq, hiO]
  · rw [F.symm.edge_eq, hiE]
  · rw [F.symm.vertex_eq, hiV]
  · rw [← F.symm.map_other, F.symm.vertex_eq, hiO]

end Equiv

/-! ## Loop reflections

The fibres of `toGraph` carry a nontrivial automorphism group as soon as the graph has a loop,
which is why no construction can single out a presentation of a coarse graph, and why an
identification of two presentations must be carried as an `Equiv` rather than recovered from an
equality of their coarse graphs. -/

/-- Exchanging the two incidences of a loop is an automorphism of the presentation.

The hypothesis is exactly that `i` is an incidence of a loop; no assumption is made about the
other edges, and they are all left fixed. -/
noncomputable def loopSwap (P : Presentation V E) (i : P.I)
    (h : P.attach (P.other i) = P.attach i) : P.Equiv P :=
  letI := Classical.decEq P.I
  { vertexSet_eq := rfl
    incEquiv := _root_.Equiv.swap i (P.other i)
    edge_eq := fun j ↦ by
      obtain rfl | hji := eq_or_ne j i
      · rw [_root_.Equiv.swap_apply_left, P.edgeMap_other]
      obtain rfl | hjo := eq_or_ne j (P.other i)
      · rw [_root_.Equiv.swap_apply_right]
        exact (P.edgeMap_other i).symm
      rw [_root_.Equiv.swap_apply_of_ne_of_ne hji hjo]
    vertex_eq := fun j ↦ by
      obtain rfl | hji := eq_or_ne j i
      · rw [_root_.Equiv.swap_apply_left]
        exact h
      obtain rfl | hjo := eq_or_ne j (P.other i)
      · rw [_root_.Equiv.swap_apply_right]
        exact h.symm
      rw [_root_.Equiv.swap_apply_of_ne_of_ne hji hjo] }

/-- Note both this and `loopSwap_incEquiv_other` are `rw`-only where it matters: the index of a
half-edge occurs in the *type* of `Realization.halfPath P i`, so `simp` will not rewrite it there,
while `rw` abstracts the occurrences in the type along with the rest. -/
@[simp]
lemma loopSwap_incEquiv_self (P : Presentation V E) (i : P.I)
    (h : P.attach (P.other i) = P.attach i) : (P.loopSwap i h).incEquiv i = P.other i :=
  @_root_.Equiv.swap_apply_left P.I (Classical.decEq P.I) i (P.other i)

@[simp]
lemma loopSwap_incEquiv_other (P : Presentation V E) (i : P.I)
    (h : P.attach (P.other i) = P.attach i) : (P.loopSwap i h).incEquiv (P.other i) = i :=
  @_root_.Equiv.swap_apply_right P.I (Classical.decEq P.I) i (P.other i)

end Presentation

end Graph
