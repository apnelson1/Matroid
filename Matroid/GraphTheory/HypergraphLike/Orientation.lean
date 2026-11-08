module

public import Matroid.GraphTheory.HypergraphLike.Hierarchy.GraphLike
public import Matroid.GraphTheory.HypergraphLike.Hierarchy.Directed

/-!
# Choosing incidences of graph-like objects

An orientation chooses one incidence of each edge. It parametrizes undirected edge traversal,
independently of the source and target predicates supplied by the representation.
For a loop, the two incidence choices remain distinct even when their vertices agree.
-/

@[expose] public section

open Set Function Classical

namespace HypergraphLike

variable {V I E Gr : Type*} {G : Gr} [HypergraphLike V I E G] [GraphLike G] {e : E}

namespace GraphLike

lemma other'_involutive (G : Gr) [HypergraphLike V I E G] [GraphLike G] :
    Involutive (other' (G := G) : I(G) → I(G)) := fun i ↦
  ((edgeMap'_eq (other' i) i (edgeMap'_other' i)).resolve_left (other'_ne i).symm).symm

@[simp]
lemma other'_other' (i : I(G)) : other' (other' i) = i := other'_involutive G i

lemma edgeMap'_val_other' (i : I(G)) :
    (edgeMap' (other' i) : E) = (edgeMap' i : E) :=
  congrArg Subtype.val (edgeMap'_other' i)

lemma edgeMap'_val_eq_iff (i j : I(G)) :
    (edgeMap' i : E) = (edgeMap' j : E) ↔ j = i ∨ j = other' i := by
  refine ⟨fun h ↦ edgeMap'_eq i j (Subtype.ext h), ?_⟩
  rintro (rfl | rfl)
  · rfl
  exact (edgeMap'_val_other' i).symm

lemma eq_or_eq_other'_of_edgeMap'_val_eq {i j : I(G)}
    (h : (edgeMap' j : E) = (edgeMap' i : E)) : j = i ∨ j = other' i :=
  edgeMap'_eq i j (Subtype.ext h.symm)

end GraphLike

open GraphLike

/-- The incidence fibre over an edge label; empty for an unused label. -/
abbrev IncidenceAt (G : Gr) [HypergraphLike V I E G] (e : E) :=
  {i : I(G) // (edgeMap' i : E) = e}

namespace IncidenceAt

/-- The paired incidence in the same edge fibre. -/
def other (i : IncidenceAt G e) : IncidenceAt G e :=
  ⟨other' i.1, (edgeMap'_val_other' i.1).trans i.2⟩

@[simp] lemma other_val (i : IncidenceAt G e) : i.other.1 = other' i.1 := rfl

@[simp] lemma other_other (i : IncidenceAt G e) : i.other.other = i :=
  Subtype.ext (other'_other' i.1)

@[simp] lemma other_ne (i : IncidenceAt G e) : i.other ≠ i :=
  fun h ↦ other'_ne i.1 (congrArg Subtype.val h)

@[simp] lemma ne_other (i : IncidenceAt G e) : i ≠ i.other := i.other_ne.symm

/-- The vertex at the chosen incidence, regardless of its source or target predicate. -/
abbrev source (i : IncidenceAt G e) : V(G) := attach' i.1

/-- The vertex at the paired incidence. -/
abbrev target (i : IncidenceAt G e) : V(G) := attach' (other' i.1)

@[simp] lemma source_other (i : IncidenceAt G e) : i.other.source = i.target := rfl

@[simp] lemma target_other (i : IncidenceAt G e) : i.other.target = i.source := by
  simp [target, source, other]

lemma eq_or_eq_other (i j : IncidenceAt G e) : j = i ∨ j = i.other := by
  obtain h | h := edgeMap'_eq i.1 j.1 (Subtype.ext (i.2.trans j.2.symm))
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end IncidenceAt

/-- A choice of one incidence of every edge, used only to parametrize its interval. -/
def Orientation (G : Gr) [HypergraphLike V I E G] [Undirected G] := ∀ e : E(G), IncidenceAt G e.1

variable [Undirected G]

namespace Orientation

/-- The vertex selected by an orientation. -/
def source (O : Orientation G) (e : E(G)) : V(G) := (O e).source

/-- The vertex at the paired incidence. -/
def target (O : Orientation G) (e : E(G)) : V(G) := (O e).target

/-- Reverse all chosen incidence pairs. -/
def reverse (O : Orientation G) : Orientation G := fun e ↦ (O e).other

@[simp] lemma reverse_reverse (O : Orientation G) : O.reverse.reverse = O := by
  funext e
  exact (O e).other_other

@[simp] lemma source_reverse (O : Orientation G) (e : E(G)) :
    O.reverse.source e = O.target e := rfl

@[simp] lemma target_reverse (O : Orientation G) (e : E(G)) :
    O.reverse.target e = O.source e := (O e).target_other

end Orientation

/-- Choose interval parametrizations classically, without imposing graph edge directions. -/
noncomputable def chooseOrientation (G : Gr) [HypergraphLike V I E G] [GraphLike G] [Undirected G] :
    Orientation G := fun e ↦
  let h := GraphLike.exists_isSource_of_mem_edgeSet' e.property
  ⟨h.choose, h.choose_spec.1⟩

end HypergraphLike
