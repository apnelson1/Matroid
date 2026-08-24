module

public import Matroid.Graph.Presentation.Basic

/-!
# Orientations of an incidence presentation

An orientation of an edge is not encoded in the coarse graph.  For a presentation, however, an
edge orientation is simply the choice of one of the two incidences in its fibre.  We therefore use
`Presentation.IncidenceAt e` for the local object rather than introducing a misleading
`EdgeOrientation` synonym.

A global `Presentation.Orientation` chooses one incidence over every edge.  For loops the two
choices are genuinely distinct even though their attached vertices agree.
-/

@[expose] public section

open Set Function Classical

universe uV uE

namespace Graph.Presentation

variable {V : Type uV} {E : Type uE} {P Q : Presentation V E} {e : E}

namespace IncidenceAt

/-- The mate of an incidence in the same edge fibre. -/
def other (i : P.IncidenceAt e) : P.IncidenceAt e :=
  ⟨P.other i.1, by simpa using (P.edgeMap_other i.1).trans i.2⟩

@[simp]
lemma other_val (i : P.IncidenceAt e) : i.other.1 = P.other i.1 := rfl

@[simp]
lemma other_other (i : P.IncidenceAt e) : i.other.other = i := by
  apply Subtype.ext
  simp [other]

@[simp]
lemma other_ne (i : P.IncidenceAt e) : i.other ≠ i := by
  intro h
  exact P.other_ne i.1 (congrArg Subtype.val h)

@[simp]
lemma ne_other (i : P.IncidenceAt e) : i ≠ i.other :=
  i.other_ne.symm

/-- The vertex at the chosen incidence, as an actual vertex of the coarse graph. -/
def source (i : P.IncidenceAt e) : V(P.toGraph) :=
  ⟨P.attach i.1, P.attach_mem i.1⟩

/-- The vertex at the mate incidence, as an actual vertex of the coarse graph. -/
def target (i : P.IncidenceAt e) : V(P.toGraph) :=
  ⟨P.attach (P.other i.1), P.attach_mem (P.other i.1)⟩

@[simp]
lemma source_other (i : P.IncidenceAt e) : i.other.source = i.target := rfl

@[simp]
lemma target_other (i : P.IncidenceAt e) : i.other.target = i.source := by
  apply Subtype.ext
  simp [target, source, other]

lemma isLink_source_target (i : P.IncidenceAt e) :
    P.toGraph.IsLink e i.source i.target := by
  exact ⟨i.1, i.2, rfl, rfl⟩

/-- The incidence fibre over an actual edge consists exactly of a chosen incidence and its mate. -/
lemma eq_or_eq_other (i j : P.IncidenceAt e) : j = i ∨ j = i.other := by
  obtain h | h := (P.edgeMap_eq_iff i.1 j.1).1 (i.2.trans j.2.symm)
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end IncidenceAt

/-- A global orientation chooses one of the two incidences over every actual edge. -/
def Orientation (P : Presentation V E) :=
  ∀ e : E(P.toGraph), P.IncidenceAt e.1

namespace Orientation

/-- The source selected by a presentation orientation. -/
def source (O : P.Orientation) (e : E(P.toGraph)) : V(P.toGraph) :=
  (O e).source

/-- The target selected by a presentation orientation. -/
def target (O : P.Orientation) (e : E(P.toGraph)) : V(P.toGraph) :=
  (O e).target

lemma isLink_source_target (O : P.Orientation) (e : E(P.toGraph)) :
    P.toGraph.IsLink e (O.source e) (O.target e) :=
  (O e).isLink_source_target

/-- Reverse every edge of an orientation. -/
def reverse (O : P.Orientation) : P.Orientation :=
  fun e ↦ (O e).other

@[simp]
lemma reverse_reverse (O : P.Orientation) : O.reverse.reverse = O := by
  funext e
  exact (O e).other_other

@[simp]
lemma source_reverse (O : P.Orientation) (e : E(P.toGraph)) :
    O.reverse.source e = O.target e :=
  rfl

@[simp]
lemma target_reverse (O : P.Orientation) (e : E(P.toGraph)) :
    O.reverse.target e = O.source e :=
  (O e).target_other

end Orientation

/-- Every presentation admits a global orientation.  This is intentionally noncomputable and
carries no mathematical canonicity. -/
noncomputable def chooseOrientation (P : Presentation V E) : P.Orientation :=
  fun e ↦ ⟨Exists.choose e.2, Exists.choose_spec e.2⟩

namespace Equiv

/-- Incidence relabelling restricts to an equivalence of the fibres over every ambient edge. -/
def incidenceAtEquiv (F : P.Equiv Q) (e : E) : P.IncidenceAt e ≃ Q.IncidenceAt e where
  toFun i := ⟨F.incEquiv i.1, by
    calc
      Q.edgeMap (F.incEquiv i.1) = P.edgeMap i.1 := F.edge_eq i.1
      _ = e := i.2⟩
  invFun j := ⟨F.incEquiv.symm j.1, by
    have h := F.edge_eq (F.incEquiv.symm j.1)
    calc
      P.edgeMap (F.incEquiv.symm j.1) = Q.edgeMap j.1 := by simpa using h.symm
      _ = e := j.2⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv j := by
    apply Subtype.ext
    simp

@[simp]
lemma incidenceAtEquiv_other (F : P.Equiv Q) (e : E) (i : P.IncidenceAt e) :
    F.incidenceAtEquiv e i.other = (F.incidenceAtEquiv e i).other := by
  apply Subtype.ext
  exact F.map_other i.1

/-- Incidence equivalence induces the identity-on-labels equivalence of actual edge subtypes. -/
def edgeEquiv (F : P.Equiv Q) : E(P.toGraph) ≃ E(Q.toGraph) where
  toFun e := ⟨e.1, by
    change e.1 ∈ Q.edgeSet
    rw [← F.edgeSet_eq]
    exact e.2⟩
  invFun e := ⟨e.1, by
    change e.1 ∈ P.edgeSet
    rw [F.edgeSet_eq]
    exact e.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

@[simp]
lemma edgeEquiv_val (F : P.Equiv Q) (e : E(P.toGraph)) : (F.edgeEquiv e).1 = e.1 := rfl

/-- Transport a global orientation through an incidence relabelling. -/
def mapOrientation (F : P.Equiv Q) (O : P.Orientation) : Q.Orientation :=
  fun e ↦ F.incidenceAtEquiv e.1 (O (F.edgeEquiv.symm e))

@[simp]
lemma mapOrientation_apply_val (F : P.Equiv Q) (O : P.Orientation) (e : E(Q.toGraph)) :
    (F.mapOrientation O e).1 = F.incEquiv (O (F.edgeEquiv.symm e)).1 :=
  rfl

@[simp]
lemma mapOrientation_reverse (F : P.Equiv Q) (O : P.Orientation) :
    F.mapOrientation O.reverse = (F.mapOrientation O).reverse := by
  funext e
  apply Subtype.ext
  exact F.map_other _

end Equiv

end Graph.Presentation
