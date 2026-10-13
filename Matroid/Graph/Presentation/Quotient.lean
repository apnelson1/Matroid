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

universe uV uI uJ uK uE

namespace Graph.Presentation

variable {V : Type uV} {E : Type uE} {I : Type uI} {J : Type uJ} {K : Type uK}
  {P : Presentation V I E} {Q : Presentation V J E} {R : Presentation V K E}

/-- An incidence relabelling between presentations on the same ambient vertex and edge types.

The vertex and edge labels are fixed; only incidence labels are allowed to move. -/
protected structure Equiv (P : Presentation V I E) (Q : Presentation V J E) where
  vertexSet_eq : P.vertexSet = Q.vertexSet
  incEquiv : I ≃ J
  edge_eq : ∀ i, Q.edgeMap (incEquiv i) = P.edgeMap i
  vertex_eq : ∀ i, Q.attach (incEquiv i) = P.attach i

attribute [simp, grind =] Equiv.edge_eq Equiv.vertex_eq

namespace Equiv

@[simp, grind =]
lemma map_other (F : P.Equiv Q) (i : I) : F.incEquiv (P.other i) = Q.other (F.incEquiv i) := by
  have he : Q.edgeMap (F.incEquiv i) = Q.edgeMap (F.incEquiv (P.other i)) := by
    rw [F.edge_eq, F.edge_eq, P.edgeMap_other]
  obtain hEq | hOther := (Q.edgeMap_eq_iff (F.incEquiv i) (F.incEquiv (P.other i))).1 he
  · exact (P.other_ne i (F.incEquiv.injective hEq)).elim
  exact hOther

protected def refl (P : Presentation V I E) : P.Equiv P where
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

/-- Identity-on-labels equivalence of the vertex subtypes. -/
@[simps (attr := grind =)]
def vertexEquiv (F : P.Equiv Q) : V(P) ≃ V(Q) where
  toFun v := ⟨v.1, F.vertexSet_eq ▸ v.2⟩
  invFun v := ⟨v.1, F.vertexSet_eq.symm ▸ v.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Identity-on-labels equivalence of the edge subtypes. -/
@[simps (attr := grind =)]
def edgeEquiv (F : P.Equiv Q) : E(P) ≃ E(Q) where
  toFun e := ⟨e.1, F.edgeSet_eq ▸ e.2⟩
  invFun e := ⟨e.1, F.edgeSet_eq.symm ▸ e.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Incidence equivalence preserves the coarse graph exactly. -/
theorem toGraph_eq (F : P.Equiv Q) : P.toGraph = Q.toGraph := by
  refine Graph.ext F.vertexSet_eq fun e x y ↦ ⟨fun ⟨i, hiE, hiV, hiO⟩ ↦ ⟨F.incEquiv i, ?_, ?_, ?_⟩,
    fun ⟨i, hiE, hiV, hiO⟩ ↦ ⟨F.symm.incEquiv i, ?_, ?_, ?_⟩⟩
  on_goal 3 => rw [← F.map_other, F.vertex_eq, hiO]
  on_goal 5 => rw [← F.symm.map_other, F.symm.vertex_eq, hiO]
  all_goals grind

end Equiv

open Classical in
/-! ## Loop reflections

The fibres of `toGraph` carry a nontrivial automorphism group as soon as the graph has a loop,
which is why no construction can single out a presentation of a coarse graph, and why an
identification of two presentations must be carried as an `Equiv` rather than recovered from an
equality of their coarse graphs. -/

/-- Exchanging the two incidences of a loop is an automorphism of the presentation.

The hypothesis is exactly that `i` is an incidence of a loop; no assumption is made about the
other edges, and they are all left fixed. -/
noncomputable def loopSwap (P : Presentation V I E) (i : I)
    (h : P.attach (P.other i) = P.attach i) : P.Equiv P where
  vertexSet_eq := rfl
  incEquiv := Equiv.swap i (P.other i)
  edge_eq j := by
    obtain rfl | hji := eq_or_ne j i
    · rw [Equiv.swap_apply_left, P.edgeMap_other]
    obtain rfl | hjo := eq_or_ne j (P.other i)
    · rw [Equiv.swap_apply_right]
      exact (P.edgeMap_other i).symm
    rw [Equiv.swap_apply_of_ne_of_ne hji hjo]
  vertex_eq j := by
    obtain rfl | hji := eq_or_ne j i
    · rwa [Equiv.swap_apply_left]
    obtain rfl | hjo := eq_or_ne j (P.other i)
    · rw [Equiv.swap_apply_right]
      exact h.symm
    rw [Equiv.swap_apply_of_ne_of_ne hji hjo]

/-- Note both this and `loopSwap_incEquiv_other` are `rw`-only where it matters: the index of a
half-edge occurs in the *type* of `Realization.halfPath P i`, so `simp` will not rewrite it there,
while `rw` abstracts the occurrences in the type along with the rest. -/
@[simp]
lemma loopSwap_incEquiv_self (P : Presentation V I E) (i : I)
    (h : P.attach (P.other i) = P.attach i) : (P.loopSwap i h).incEquiv i = P.other i :=
  Equiv.swap_apply_left i (P.other i)

@[simp]
lemma loopSwap_incEquiv_other (P : Presentation V I E) (i : I)
    (h : P.attach (P.other i) = P.attach i) : (P.loopSwap i h).incEquiv (P.other i) = i :=
  Equiv.swap_apply_right i (P.other i)

/-- Incidence relabelling, regarded merely as a relation on presentations. -/
def IncidenceRel (P : Presentation V I E) (Q : Presentation V J E) : Prop := Nonempty (P.Equiv Q)

instance incidenceSetoid : Setoid (Σ I : Type (max uV uE), Presentation V I E) where
  r P Q := IncidenceRel P.2 Q.2
  iseqv := {
    refl := fun P ↦ ⟨Equiv.refl P.2⟩
    symm := fun ⟨F⟩ ↦ ⟨F.symm⟩
    trans := fun ⟨F⟩ ⟨F'⟩ ↦ ⟨F.trans F'⟩ }

/-- The literal quotient of presentations by incidence relabelling.

This type is primarily useful as a classification/specification object.  The existing `Graph V E`
is the preferred concrete implementation of the quotient. -/
abbrev QuotientGraph (V E : Type*) :=
  Quotient (incidenceSetoid (V := V) (E := E))

/-- Forget incidences on the quotient. -/
def quotientToGraph : QuotientGraph V E → Graph V E :=
  Quotient.lift (fun P ↦ P.2.toGraph) (fun _ _ ⟨F⟩ ↦ F.toGraph_eq)

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
noncomputable def ofGraph (G : Graph V E) :
    Presentation V (ULift.{uV} (E(G) × Bool)) E where
  vertexSet := G.vertexSet
  attach i := if i.down.2 then (chosenLink G i.down.1).1.2.1 else (chosenLink G i.down.1).1.1.1
  edgeMap := fun i ↦ i.down.1.1
  attach_mem i := by
    split_ifs
    · exact (chosenLink G i.down.1).1.2.2
    exact (chosenLink G i.down.1).1.1.2
  other i := ULift.up (i.down.1, !i.down.2)
  other_ne i h:= by
    have hb := congrArg (fun t : _ => t.down.2) h
    simp at hb
  edgeMap_other _ := rfl
  edgeMap_eq i j h := by
    have he : i.down.1 = j.down.1 := Subtype.ext h
    refine (eq_or_ne j.down.2 i.down.2).imp (ULift.ext <| Prod.ext he.symm ·) (fun hb ↦ ?_)
    apply ULift.ext
    ext
    · simpa using h.symm
    grind

private def ofGraphInc (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    ULift.{uV} (E(G) × Bool) := ULift.up (e, b)

private lemma ofGraphInc_self (G : Graph V E) (i : ULift.{uV} (E(G) × Bool)) :
    ofGraphInc G i.down.1 i.down.2 = i := ULift.up_down i

private lemma ofGraphInc_other (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).other (ofGraphInc G e b) = ofGraphInc G e (!b) := rfl

private lemma ofGraphInc_vertex (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).attach (ofGraphInc G e b) =
    if b then (chosenLink G e).1.2.1 else (chosenLink G e).1.1.1 := rfl

private lemma ofGraphInc_edge (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).edgeMap (ofGraphInc G e b) = e.1 := rfl

/-- Each incidence of the chosen presentation of `G` is a link of `G`. -/
lemma ofGraph_isLink (G : Graph V E) (i : ULift.{uV} (E(G) × Bool)) :
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

@[simp]
lemma ofGraph_vertexSet (G : Graph V E) : V(ofGraph G) = V(G) :=
  rfl

@[simp]
lemma ofGraph_edgeSet (G : Graph V E) : E(ofGraph G) = E(G) := by
  rw [← edgeSet_toGraph, toGraph_ofGraph]

/-! ## Classification of the fibres of `toGraph` -/

lemma vertexSet_eq_of_toGraph_eq (h : P.toGraph = Q.toGraph) : P.vertexSet = Q.vertexSet := by
  simpa using congrArg Graph.vertexSet h

lemma edgeSet_eq_of_toGraph_eq (h : P.toGraph = Q.toGraph) : P.edgeSet = Q.edgeSet := by
  simpa using congrArg Graph.edgeSet h

noncomputable def chosenInc (P : Presentation V I E) {e : E} (he : e ∈ P.edgeSet) : I :=
  he.choose

lemma chosenInc_edge (P : Presentation V I E) {e : E} (he : e ∈ P.edgeSet) :
    P.edgeMap (chosenInc P he) = e :=
  he.choose_spec

lemma chosenInc_congr (P : Presentation V I E) {e e' : E} (he : e ∈ P.edgeSet)
    (he' : e' ∈ P.edgeSet) (h : e = e') : chosenInc P he = chosenInc P he' := by
  subst h
  exact congrArg (chosenInc P (e := e)) (Subsingleton.elim _ _)

lemma chosenInc_repr (P : Presentation V I E) {e : E} (he : e ∈ P.edgeSet) :
    chosenInc P (P.edgeMap_mem_edgeSet (chosenInc P he)) = chosenInc P he :=
  chosenInc_congr P _ _ (chosenInc_edge P he)

lemma chosenInc_repr_other (P : Presentation V I E) {e : E} (he : e ∈ P.edgeSet) :
    chosenInc P (P.edgeMap_mem_edgeSet (P.other (chosenInc P he))) = chosenInc P he :=
  chosenInc_congr P _ _ (by rw [P.edgeMap_other, chosenInc_edge])

lemma eq_chosenInc_or_other (P : Presentation V I E) (i : I) :
    i = chosenInc P (P.edgeMap_mem_edgeSet i) ∨
      i = P.other (chosenInc P (P.edgeMap_mem_edgeSet i)) := by
  apply (P.edgeMap_eq_iff (chosenInc P (P.edgeMap_mem_edgeSet i)) i).1
  exact (chosenInc_edge P (P.edgeMap_mem_edgeSet i)).trans rfl

lemma isLink_transfer (h : P.toGraph = Q.toGraph) (i : I) :
    Q.IsLink (P.edgeMap i) (P.attach i) (P.attach (P.other i)) := by
  have hi : P.IsLink (P.edgeMap i) (P.attach i) (P.attach (P.other i)) :=
    ⟨i, rfl, rfl, rfl⟩
  rwa [← toGraph_isLink, h, toGraph_isLink] at hi

noncomputable def chosenQInc (h : P.toGraph = Q.toGraph) (i : I) : J :=
  (isLink_transfer h i).choose

lemma chosenQInc_spec (h : P.toGraph = Q.toGraph) (i : I) :
    Q.edgeMap (chosenQInc h i) = P.edgeMap i ∧ Q.attach (chosenQInc h i) = P.attach i ∧
    Q.attach (Q.other (chosenQInc h i)) = P.attach (P.other i) :=
  (isLink_transfer h i).choose_spec

noncomputable def incMap (h : P.toGraph = Q.toGraph) (i : I) : J :=
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

lemma incMap_edge (h : P.toGraph = Q.toGraph) (i : I) :
    Q.edgeMap (incMap h i) = P.edgeMap i := by
  unfold incMap
  split_ifs
  · rw [(chosenQInc_spec h _).1, chosenInc_edge]
  rw [Q.edgeMap_other, (chosenQInc_spec h _).1, chosenInc_edge]

lemma incMap_vertex (h : P.toGraph = Q.toGraph) (i : I) :
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
theorem nonempty_equiv_iff_toGraph_eq (P : Presentation V I E) (Q : Presentation V J E) :
    Nonempty (P.Equiv Q) ↔ P.toGraph = Q.toGraph :=
  ⟨fun ⟨F⟩ ↦ F.toGraph_eq, fun h ↦ ⟨equivOfToGraphEq h⟩⟩

@[deprecated nonempty_equiv_iff_toGraph_eq +typeChanged (since := "2026-08-20")]
theorem incidenceRel_iff_toGraph_eq (P : Presentation V I E) (Q : Presentation V J E) :
    IncidenceRel P Q ↔ P.toGraph = Q.toGraph :=
  nonempty_equiv_iff_toGraph_eq P Q

/-- The literal incidence quotient is equivalent to the current `Graph`. -/
theorem quotientToGraph_injective : Injective (quotientToGraph (V := V) (E := E)) := by
  intro a b hab
  induction a using Quotient.inductionOn with | _ P =>
  induction b using Quotient.inductionOn with | _ Q =>
  exact Quotient.sound <| (nonempty_equiv_iff_toGraph_eq P.2 Q.2).2 hab

theorem quotientToGraph_surjective : Surjective (quotientToGraph (V := V) (E := E)) :=
  fun G ↦ ⟨Quotient.mk _ ⟨_, ofGraph G⟩, toGraph_ofGraph G⟩

noncomputable def quotientGraphEquivCurrentGraph : QuotientGraph V E ≃ Graph V E :=
  Equiv.ofBijective quotientToGraph ⟨quotientToGraph_injective, quotientToGraph_surjective⟩

end Presentation
end Graph
