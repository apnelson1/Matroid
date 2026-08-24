module

public import Matroid.Graph.Presentation.Basic

/-!
# The coarse quotient of incidence presentations

Two presentations are equivalent when they differ only by an incidence relabelling.  This file
proves that the current `Graph V E` is exactly the quotient by that relation.

The main classification theorem is

```
Nonempty (P.Equiv Q) ↔ P.toGraph = Q.toGraph.
```

Thus `Presentation.toGraph` is not merely a forgetful construction: its fibres are precisely the
incidence-equivalence classes.
-/

@[expose] public section

open Set Function Classical

namespace Graph.Presentation

variable {V E : Type*} {P Q R : Presentation V E}

/-- Incidence relabelling, regarded merely as a relation on presentations. -/
def IncidenceRel (P Q : Presentation V E) : Prop := Nonempty (P.Equiv Q)

instance incidenceSetoid : Setoid (Presentation V E) where
  r := IncidenceRel
  iseqv := {
    refl := fun P ↦ ⟨Equiv.refl P⟩
    symm := fun ⟨F⟩ ↦ ⟨F.symm⟩
    trans := fun ⟨F⟩ ⟨F'⟩ ↦ ⟨F.trans F'⟩ }

/-- The literal quotient of presentations by incidence relabelling.

This type is primarily useful as a classification/specification object.  The existing `Graph V E`
is the preferred concrete implementation of the quotient. -/
abbrev QuotientGraph (V E : Type*) :=
  Quotient (incidenceSetoid (V := V) (E := E))

/-- Forget incidences on the quotient. -/
def quotientToGraph : QuotientGraph V E → Graph V E :=
  Quotient.lift Presentation.toGraph (fun _ _ ⟨F⟩ ↦ F.toGraph_eq)

/-! ## Every coarse graph has a presentation -/

/-- A noncomputably chosen ordered representative of the unordered ends of an edge. -/
noncomputable def chosenLink (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) :
    {p : ({v : V // v ∈ G.vertexSet} × {v : V // v ∈ G.vertexSet}) //
      G.IsLink e.1 p.1.1 p.2.1} :=
  have hex := G.exists_isLink_of_mem_edgeSet e.2
  have hxy := hex.choose_spec.choose_spec
  ⟨(⟨hex.choose, hxy.left_mem⟩, ⟨hex.choose_spec.choose, hxy.right_mem⟩), hxy⟩

/-- A chosen incidence presentation of a coarse graph.

The `Bool` coordinate is only presentation data.  Reversing it independently on any edge gives an
incidence-equivalent presentation, and the quotient theorem below proves that no such choice is
visible in `Graph`. -/
noncomputable def ofGraph (G : Graph V E) : Presentation V E where
  I := ULift ({e : E // e ∈ G.edgeSet} × Bool)
  vertexSet := G.vertexSet
  attach i := if i.down.2 then (chosenLink G i.down.1).1.2.1 else (chosenLink G i.down.1).1.1.1
  edgeMap := fun i ↦ i.down.1.1
  attach_mem i := by
    split_ifs
    · exact (chosenLink G i.down.1).1.2.2
    exact (chosenLink G i.down.1).1.1.2
  other i := ULift.up (i.down.1, !i.down.2)
  other_involutive i := by
    apply ULift.ext
    simp
  other_ne i h:= by
    have hb := congrArg (fun t : _ => t.down.2) h
    simp at hb
  edgeMap_eq_iff i j := by
    refine ⟨fun h ↦ ?_, by grind⟩
    have he : i.down.1 = j.down.1 := Subtype.ext h
    refine (eq_or_ne j.down.2 i.down.2).imp (ULift.ext _ _ <| Prod.ext he.symm ·) (fun hb ↦ ?_)
    apply ULift.ext
    ext
    · simpa using h.symm
    grind

private def ofGraphInc (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).I := ULift.up (e, b)

private lemma ofGraphInc_self (G : Graph V E) (i : (ofGraph G).I) :
    ofGraphInc G i.down.1 i.down.2 = i := ULift.up_down i

private lemma ofGraphInc_other (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).other (ofGraphInc G e b) = ofGraphInc G e (!b) := rfl

private lemma ofGraphInc_vertex (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).attach (ofGraphInc G e b) =
    if b then (chosenLink G e).1.2.1 else (chosenLink G e).1.1.1 := rfl

private lemma ofGraphInc_edge (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).edgeMap (ofGraphInc G e b) = e.1 := rfl

private lemma ofGraph_isLink (G : Graph V E) (i : (ofGraph G).I) :
    G.IsLink ((ofGraph G).edgeMap i) ((ofGraph G).attach i)
      ((ofGraph G).attach ((ofGraph G).other i)) := by
  cases h : i.down.2
  · rw [← ofGraphInc_self G i, ofGraphInc_edge, ofGraphInc_vertex, ofGraphInc_other,
      ofGraphInc_vertex]
    simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    exact (chosenLink G i.down.1).2
  rw [← ofGraphInc_self G i, ofGraphInc_edge, ofGraphInc_vertex, ofGraphInc_other,
    ofGraphInc_vertex]
  simp only [h, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
  exact (chosenLink G i.down.1).2.symm

@[simp]
theorem toGraph_ofGraph (G : Graph V E) : (ofGraph G).toGraph = G := by
  refine Graph.ext (by rfl) fun e x y => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨i, rfl, rfl, rfl⟩ := h
    exact ofGraph_isLink G i
  let e' : {e : E // e ∈ G.edgeSet} := ⟨e, h.edge_mem⟩
  have hc := (chosenLink G e').2
  obtain hsame | hswap := hc.eq_and_eq_or_eq_and_eq h
  · refine ⟨ofGraphInc G e' false, rfl, ?_, ?_⟩
    · simpa [ofGraphInc_vertex] using hsame.1
    · rw [ofGraphInc_other, ofGraphInc_vertex]
      simpa using hsame.2
  refine ⟨ofGraphInc G e' true, rfl, ?_, ?_⟩
  · simpa [ofGraphInc_vertex] using hswap.2
  rw [ofGraphInc_other, ofGraphInc_vertex]
  simpa using hswap.1

/-! ## Classification of the fibres of `toGraph` -/

lemma vertexSet_eq_of_toGraph_eq (h : P.toGraph = Q.toGraph) : P.vertexSet = Q.vertexSet := by
  simpa using congrArg Graph.vertexSet h

lemma edgeSet_eq_of_toGraph_eq (h : P.toGraph = Q.toGraph) : P.edgeSet = Q.edgeSet := by
  simpa using congrArg Graph.edgeSet h

noncomputable def chosenInc (P : Presentation V E) {e : E} (he : e ∈ P.edgeSet) : P.I :=
  he.choose

lemma chosenInc_edge (P : Presentation V E) {e : E} (he : e ∈ P.edgeSet) :
    P.edgeMap (chosenInc P he) = e :=
  he.choose_spec

lemma chosenInc_congr (P : Presentation V E) {e e' : E} (he : e ∈ P.edgeSet) (he' : e' ∈ P.edgeSet)
    (h : e = e') : chosenInc P he = chosenInc P he' := by
  subst h
  exact congrArg (chosenInc P (e := e)) (Subsingleton.elim _ _)

lemma chosenInc_repr (P : Presentation V E) {e : E} (he : e ∈ P.edgeSet) :
    chosenInc P (P.edgeMap_mem_edgeSet (chosenInc P he)) = chosenInc P he :=
  chosenInc_congr P _ _ (chosenInc_edge P he)

lemma chosenInc_repr_other (P : Presentation V E) {e : E} (he : e ∈ P.edgeSet) :
    chosenInc P (P.edgeMap_mem_edgeSet (P.other (chosenInc P he))) = chosenInc P he :=
  chosenInc_congr P _ _ (by rw [P.edgeMap_other, chosenInc_edge])

lemma eq_chosenInc_or_other (P : Presentation V E) (i : P.I) :
    i = chosenInc P (P.edgeMap_mem_edgeSet i) ∨
      i = P.other (chosenInc P (P.edgeMap_mem_edgeSet i)) := by
  apply (P.edgeMap_eq_iff (chosenInc P (P.edgeMap_mem_edgeSet i)) i).1
  exact (chosenInc_edge P (P.edgeMap_mem_edgeSet i)).trans rfl

lemma isLink_transfer (h : P.toGraph = Q.toGraph) (i : P.I) :
    Q.IsLink (P.edgeMap i) (P.attach i) (P.attach (P.other i)) := by
  have hi : P.IsLink (P.edgeMap i) (P.attach i) (P.attach (P.other i)) :=
    ⟨i, rfl, rfl, rfl⟩
  rwa [← toGraph_isLink, h, toGraph_isLink] at hi

noncomputable def chosenQInc (h : P.toGraph = Q.toGraph) (i : P.I) : Q.I :=
  (isLink_transfer h i).choose

lemma chosenQInc_spec (h : P.toGraph = Q.toGraph) (i : P.I) :
    Q.edgeMap (chosenQInc h i) = P.edgeMap i ∧ Q.attach (chosenQInc h i) = P.attach i ∧
    Q.attach (Q.other (chosenQInc h i)) = P.attach (P.other i) :=
  (isLink_transfer h i).choose_spec

noncomputable def incMap (h : P.toGraph = Q.toGraph) (i : P.I) : Q.I :=
  if i = chosenInc P (P.edgeMap_mem_edgeSet i) then
    chosenQInc h (chosenInc P (P.edgeMap_mem_edgeSet i))
  else Q.other (chosenQInc h (chosenInc P (P.edgeMap_mem_edgeSet i)))

lemma incMap_chosenInc (h : P.toGraph = Q.toGraph) {e : E} (he : e ∈ P.edgeSet) :
    incMap h (chosenInc P he) = chosenQInc h (chosenInc P he) := by
  unfold incMap
  split_ifs with hi
  · congr 1
    exact chosenInc_repr P he
  exact (hi (chosenInc_repr P he).symm).elim

lemma incMap_chosenInc_other (h : P.toGraph = Q.toGraph) {e : E} (he : e ∈ P.edgeSet) :
    incMap h (P.other (chosenInc P he)) = Q.other (chosenQInc h (chosenInc P he)) := by
  unfold incMap
  have hp := chosenInc_repr_other P he
  have hne : P.other (chosenInc P he) ≠
      chosenInc P (P.edgeMap_mem_edgeSet (P.other (chosenInc P he))) := by
    rw [hp]
    exact P.other_ne _
  split_ifs with hi
  · exact (hne hi).elim
  rw [hp]

lemma incMap_edge (h : P.toGraph = Q.toGraph) (i : P.I) :
    Q.edgeMap (incMap h i) = P.edgeMap i := by
  unfold incMap
  split_ifs
  · rw [(chosenQInc_spec h _).1, chosenInc_edge]
  rw [Q.edgeMap_other, (chosenQInc_spec h _).1, chosenInc_edge]

lemma incMap_vertex (h : P.toGraph = Q.toGraph) (i : P.I) :
    Q.attach (incMap h i) = P.attach i := by
  obtain hi | hi := eq_chosenInc_or_other P i
  · rw [hi, incMap_chosenInc, (chosenQInc_spec h _).2.1]
  rw [hi, incMap_chosenInc_other, (chosenQInc_spec h _).2.2]

lemma incMap_injective (h : P.toGraph = Q.toGraph) : Injective (incMap h) := by
  intro i j hij
  have heij : P.edgeMap i = P.edgeMap j := by
    rw [← incMap_edge h i, hij, incMap_edge h j]
  have hp0 : chosenInc P (P.edgeMap_mem_edgeSet i) = chosenInc P (P.edgeMap_mem_edgeSet j) :=
    chosenInc_congr P _ _ heij
  obtain hi | hi := eq_chosenInc_or_other P i <;> obtain hj | hj := eq_chosenInc_or_other P j
  · rw [hi, hj, hp0]
  · rw [hi, incMap_chosenInc, hj, incMap_chosenInc_other, hp0] at hij
    exact False.elim <| (Q.other_ne (chosenQInc h (chosenInc P (P.edgeMap_mem_edgeSet i))))
      (by convert hij.symm)
  · rw [hi, incMap_chosenInc_other, hj, incMap_chosenInc, hp0] at hij
    exact False.elim <| (Q.other_ne (chosenQInc h (chosenInc P (P.edgeMap_mem_edgeSet i))))
      (by convert hij)
  rw [hi, hj, hp0]

lemma incMap_surjective (h : P.toGraph = Q.toGraph) : Surjective (incMap h) := by
  intro k
  have heP : Q.edgeMap k ∈ P.edgeSet :=
    (edgeSet_eq_of_toGraph_eq h).symm ▸ Q.edgeMap_mem_edgeSet k
  let p0 := chosenInc P heP
  let q0 := chosenQInc h p0
  have hq0e : Q.edgeMap q0 = Q.edgeMap k := by
    rw [(chosenQInc_spec h p0).1, chosenInc_edge]
  obtain hk | hk := (Q.edgeMap_eq_iff q0 k).1 hq0e
  · refine ⟨p0, ?_⟩
    rw [incMap_chosenInc]
    exact hk.symm
  refine ⟨P.other p0, ?_⟩
  rw [incMap_chosenInc_other]
  exact hk.symm

noncomputable def equivOfToGraphEq (h : P.toGraph = Q.toGraph) : P.Equiv Q where
  vertexSet_eq := vertexSet_eq_of_toGraph_eq h
  incEquiv := _root_.Equiv.ofBijective (incMap h) ⟨incMap_injective h, incMap_surjective h⟩
  edge_eq := fun i ↦ incMap_edge h i
  vertex_eq := fun i ↦ incMap_vertex h i

/-- Two presentations forget to the same coarse graph exactly when they differ by an incidence
relabelling. -/
theorem nonempty_equiv_iff_toGraph_eq (P Q : Presentation V E) :
    Nonempty (P.Equiv Q) ↔ P.toGraph = Q.toGraph :=
  ⟨fun ⟨F⟩ ↦ F.toGraph_eq, fun h ↦ ⟨equivOfToGraphEq h⟩⟩

@[deprecated nonempty_equiv_iff_toGraph_eq (since := "2026-08-20")]
theorem incidenceRel_iff_toGraph_eq (P Q : Presentation V E) :
    IncidenceRel P Q ↔ P.toGraph = Q.toGraph :=
  nonempty_equiv_iff_toGraph_eq P Q

/-- The literal incidence quotient is equivalent to the current `Graph`. -/
theorem quotientToGraph_injective : Injective (quotientToGraph (V := V) (E := E)) := by
  intro a b hab
  induction a using Quotient.inductionOn with | _ P =>
  induction b using Quotient.inductionOn with | _ Q =>
  exact Quotient.sound <| (nonempty_equiv_iff_toGraph_eq P Q).2 hab

theorem quotientToGraph_surjective : Surjective (quotientToGraph (V := V) (E := E)) :=
  fun G ↦ ⟨Quotient.mk _ (ofGraph G), toGraph_ofGraph G⟩

noncomputable def quotientGraphEquivCurrentGraph : QuotientGraph V E ≃ Graph V E :=
  Equiv.ofBijective quotientToGraph ⟨quotientToGraph_injective, quotientToGraph_surjective⟩

end Presentation
end Graph
