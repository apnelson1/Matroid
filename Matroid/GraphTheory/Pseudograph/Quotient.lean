module

public import Matroid.GraphTheory.Pseudograph.Incidence
public import Matroid.GraphTheory.HypergraphLike.Hom

/-!
# The coarse quotient of pseudographs

Two pseudographs are equivalent when they differ only by an incidence relabelling.  This file
proves that the current `Graph V E` is exactly the quotient by that relation.

The main classification theorem is

```
Nonempty (P.Equiv Q) ↔ P.toGraph = Q.toGraph.
```

Thus `Pseudograph.toGraph` is not merely a forgetful construction: its fibres are precisely the
incidence-equivalence classes.
-/

open HypergraphLike

@[expose] public section

open Set Function Classical

universe uV uI uJ uK uE

namespace Pseudograph

open Graph

variable {V : Type uV} {E : Type uE} {I : Type uI} {J : Type uJ} {K : Type uK}
  {P : Pseudograph V I E} {Q : Pseudograph V J E} {R : Pseudograph V K E}

/-- An incidence relabelling between pseudographs on the same ambient vertex and edge types.

The vertex and edge labels are fixed; only incidence labels are allowed to move. -/
protected structure Equiv (P : Pseudograph V I E) (Q : Pseudograph V J E) where
  vertexSet_eq : V(P) = V(Q)
  incEquiv : I(P) ≃ I(Q)
  edge_eq : ∀ i, Q.edgeMap' (incEquiv i) = P.edgeMap' i
  vertex_eq : ∀ i, Q.attach' (incEquiv i) = P.attach' i

attribute [simp, grind =] Equiv.edge_eq Equiv.vertex_eq

namespace Equiv

@[simp, grind =]
lemma map_other (F : P.Equiv Q) (i : I(P)) : F.incEquiv (P.other' i) = Q.other' (F.incEquiv i) := by
  have he : Q.edgeMap' (F.incEquiv i) = Q.edgeMap' (F.incEquiv (P.other' i)) := by
    rw [F.edge_eq, F.edge_eq, P.edgeMap'_other']
  obtain hEq | hOther :=
    (GraphLike.edgeMap'_val_eq_iff (F.incEquiv i) (F.incEquiv (P.other' i))).1 he
  · exact (P.other'_ne i (F.incEquiv.injective hEq)).elim
  exact hOther

protected def refl (P : Pseudograph V I E) : P.Equiv P where
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

lemma edgeSet_eq (F : P.Equiv Q) : E(P) = E(Q) := by
  ext e
  simp only [mem_edgeSet_iff]
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

/-- Regard incidence relabelling as a shared isomorphism fixing vertex and edge labels. -/
def toIso (F : P.Equiv Q) : HypergraphLike.Iso P Q :=
  HypergraphLike.Iso.ofEquivs F.vertexEquiv F.incEquiv F.edgeEquiv
    (fun i ↦ Subtype.ext (F.vertex_eq i)) (fun i ↦ Subtype.ext (F.edge_eq i))
    (fun i ↦ iff_of_true (F.incEquiv i).property i.property)
    (fun i ↦ iff_of_true (F.incEquiv i).property i.property)

-- Propositional rewrites let congruence rules update dependent path endpoints as well.
@[simp]
lemma toIso_vertMap' (F : P.Equiv Q) : F.toIso.vertMap' = F.vertexEquiv := funext fun _ ↦ rfl

@[simp]
lemma toIso_incMap' (F : P.Equiv Q) : F.toIso.incMap' = F.incEquiv := funext fun _ ↦ rfl

@[simp]
lemma toIso_edgeMap' (F : P.Equiv Q) : F.toIso.edgeMap' = F.edgeEquiv := funext fun _ ↦ rfl

@[simp]
lemma toIso_symm_vertMap' (F : P.Equiv Q) :
    F.toIso.symm.vertMap' = F.vertexEquiv.symm := funext fun _ ↦ rfl

@[simp]
lemma toIso_symm_incMap' (F : P.Equiv Q) :
    F.toIso.symm.incMap' = F.incEquiv.symm := funext fun _ ↦ rfl

@[simp]
lemma toIso_symm_edgeMap' (F : P.Equiv Q) :
    F.toIso.symm.edgeMap' = F.edgeEquiv.symm := funext fun _ ↦ rfl

@[simp]
lemma toIso_refl (P : Pseudograph V I E) : (Equiv.refl P).toIso = HypergraphLike.Iso.id P := rfl

@[simp]
lemma toIso_symm (F : P.Equiv Q) : F.symm.toIso = F.toIso.symm := rfl

lemma toIso_trans (F : P.Equiv Q) (F' : Q.Equiv R) :
    (F.trans F').toIso = F.toIso.comp F'.toIso := rfl

/-- Incidence equivalence preserves the coarse graph exactly. -/
theorem toGraph_eq (F : P.Equiv Q) : P.toGraph = Q.toGraph := by
  apply Graph.ext F.vertexSet_eq
  intro e x y
  simp only [toGraph_isLink_iff]
  refine ⟨fun ⟨i, hiE, hiV, hiO⟩ ↦ ⟨F.incEquiv i, ?_, ?_, ?_⟩,
    fun ⟨i, hiE, hiV, hiO⟩ ↦ ⟨F.symm.incEquiv i, ?_, ?_, ?_⟩⟩
  on_goal 3 => rw [← F.map_other, F.vertex_eq, hiO]
  on_goal 5 => rw [← F.symm.map_other, F.symm.vertex_eq, hiO]
  all_goals grind

end Equiv

open Classical in
/-! ## Loop reflections

The fibres of `toGraph` carry a nontrivial automorphism group as soon as the graph has a loop,
which is why no construction can single out a pseudograph of a coarse graph, and why an
identification of two pseudographs must be carried as an `Equiv` rather than recovered from an
equality of their coarse graphs. -/

/-- Exchanging the two incidences of a loop is an automorphism of the pseudograph.

The hypothesis is exactly that `i` is an incidence of a loop; no assumption is made about the
other edges, and they are all left fixed. -/
noncomputable def loopSwap (P : Pseudograph V I E) (i : I(P))
    (h : P.attach' (P.other' i) = P.attach' i) : P.Equiv P where
  vertexSet_eq := rfl
  incEquiv := Equiv.swap i (P.other' i)
  edge_eq j := by
    obtain rfl | hji := eq_or_ne j i
    · rw [Equiv.swap_apply_left, P.edgeMap'_other']
    obtain rfl | hjo := eq_or_ne j (P.other' i)
    · rw [Equiv.swap_apply_right]
      exact (P.edgeMap'_other' i).symm
    rw [Equiv.swap_apply_of_ne_of_ne hji hjo]
  vertex_eq j := by
    obtain rfl | hji := eq_or_ne j i
    · rwa [Equiv.swap_apply_left]
    obtain rfl | hjo := eq_or_ne j (P.other' i)
    · rw [Equiv.swap_apply_right]
      exact h.symm
    rw [Equiv.swap_apply_of_ne_of_ne hji hjo]

/-- Note both this and `loopSwap_incEquiv_other` are `rw`-only where it matters: the index of a
half-edge occurs in the *type* of `Realization.halfPath P i`, so `simp` will not rewrite it there,
while `rw` abstracts the occurrences in the type along with the rest. -/
@[simp]
lemma loopSwap_incEquiv_self (P : Pseudograph V I E) (i : I(P))
    (h : P.attach' (P.other' i) = P.attach' i) : (P.loopSwap i h).incEquiv i = P.other' i :=
  Equiv.swap_apply_left i (P.other' i)

@[simp]
lemma loopSwap_incEquiv_other (P : Pseudograph V I E) (i : I(P))
    (h : P.attach' (P.other' i) = P.attach' i) : (P.loopSwap i h).incEquiv (P.other' i) = i :=
  Equiv.swap_apply_right i (P.other' i)

/-- Incidence relabelling, regarded merely as a relation on pseudographs. -/
def IncidenceRel (P : Pseudograph V I E) (Q : Pseudograph V J E) : Prop := Nonempty (P.Equiv Q)

instance incidenceSetoid : Setoid (Σ I : Type (max uV uE), Pseudograph V I E) where
  r P Q := IncidenceRel P.2 Q.2
  iseqv := {
    refl := fun P ↦ ⟨Equiv.refl P.2⟩
    symm := fun ⟨F⟩ ↦ ⟨F.symm⟩
    trans := fun ⟨F⟩ ⟨F'⟩ ↦ ⟨F.trans F'⟩ }

/-- The literal quotient of pseudographs by incidence relabelling.

This type is primarily useful as a classification/specification object.  The existing `Graph V E`
is the preferred concrete implementation of the quotient. -/
abbrev QuotientGraph (V E : Type*) :=
  Quotient (incidenceSetoid (V := V) (E := E))

/-- Forget incidences on the quotient. -/
def quotientToGraph : QuotientGraph V E → Graph V E :=
  Quotient.lift (fun P ↦ P.2.toGraph) (fun _ _ ⟨F⟩ ↦ F.toGraph_eq)

/-! ## Every coarse graph has a pseudograph -/

/-- A noncomputably chosen ordered representative of the unordered ends of an edge. -/
noncomputable def chosenLink (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) :
    {p : ({v : V // v ∈ G.vertexSet} × {v : V // v ∈ G.vertexSet}) //
      G.IsLink e.1 p.1.1 p.2.1} :=
  have hex := G.exists_isLink_of_mem_edgeSet e.2
  have hxy := hex.choose_spec.choose_spec
  ⟨(⟨hex.choose, hxy.left_mem⟩, ⟨hex.choose_spec.choose, hxy.right_mem⟩), hxy⟩

/-- A chosen pseudograph of a coarse graph.

The `Bool` coordinate is only pseudograph data.  Reversing it independently on any edge gives an
incidence-equivalent pseudograph, and the quotient theorem below proves that no such choice is
visible in `Graph`. -/
noncomputable def ofGraph (G : Graph V E) :
    Pseudograph V (ULift.{uV} (E(G) × Bool)) E where
  vertexSet := G.vertexSet
  incidenceSet := univ
  edgeSet := G.edgeSet
  attach' i := if i.val.down.2 then (chosenLink G i.val.down.1).1.2.1
    else (chosenLink G i.val.down.1).1.1.1
  edgeMap' i := i.val.down.1.val
  edgeMap'_mem i := i.val.down.1.property
  attach'_mem i := by
    split_ifs
    · exact (chosenLink G i.val.down.1).1.2.2
    exact (chosenLink G i.val.down.1).1.1.2
  edgeMap_range := by
    ext e
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.val.down.1.property,
      fun he ↦ ⟨⟨ULift.up (⟨e, he⟩, false), mem_univ _⟩, rfl⟩⟩
  other' i := ⟨ULift.up (i.val.down.1, !i.val.down.2), mem_univ _⟩
  other'_ne i h := by
    have hb := congrArg (fun t : _ => t.val.down.2) h
    simp at hb
  edgeMap'_other' _ := rfl
  edgeMap'_eq i j h := by
    have he : i.val.down.1 = j.val.down.1 := Subtype.ext h
    rcases eq_or_ne j.val.down.2 i.val.down.2 with hb | hb
    · exact Or.inl (Subtype.ext (ULift.ext (Prod.ext he.symm hb)))
    · exact Or.inr (Subtype.ext (ULift.ext (Prod.ext he.symm (Bool.eq_not_iff.mpr hb))))

private def ofGraphInc (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    I(ofGraph G) := ⟨ULift.up (e, b), mem_univ _⟩

private lemma ofGraphInc_self (G : Graph V E) (i : I(ofGraph G)) :
    ofGraphInc G i.val.down.1 i.val.down.2 = i := Subtype.ext (ULift.up_down i.val)

private lemma ofGraphInc_other (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).other' (ofGraphInc G e b) = ofGraphInc G e (!b) := rfl

private lemma ofGraphInc_vertex (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).attach' (ofGraphInc G e b) =
    if b then (chosenLink G e).1.2.1 else (chosenLink G e).1.1.1 := rfl

private lemma ofGraphInc_edge (G : Graph V E) (e : {e : E // e ∈ G.edgeSet}) (b : Bool) :
    (ofGraph G).edgeMap' (ofGraphInc G e b) = e.1 := rfl

/-- Each incidence of the chosen pseudograph of `G` is a link of `G`. -/
lemma ofGraph_isLink (G : Graph V E) (i : I(ofGraph G)) :
    G.IsLink ((ofGraph G).edgeMap' i) ((ofGraph G).attach' i)
      ((ofGraph G).attach' ((ofGraph G).other' i)) := by
  cases h : i.val.down.2
  · rw [← ofGraphInc_self G i, ofGraphInc_edge, ofGraphInc_vertex, ofGraphInc_other,
      ofGraphInc_vertex]
    simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    exact (chosenLink G i.val.down.1).2
  rw [← ofGraphInc_self G i, ofGraphInc_edge, ofGraphInc_vertex, ofGraphInc_other,
    ofGraphInc_vertex]
  simp only [h, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
  exact (chosenLink G i.val.down.1).2.symm

@[simp]
theorem toGraph_ofGraph (G : Graph V E) : (ofGraph G).toGraph = G := by
  refine Graph.ext (by rfl) fun e x y => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨i, rfl, rfl, rfl⟩ := toGraph_isLink_iff.mp h
    exact ofGraph_isLink G i
  apply toGraph_isLink_iff.mpr
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
  rfl

/-- The chosen incidence presentation of a finite graph is finite in the shared interface. -/
instance ofGraph_finite (G : Graph V E) [G.Finite] : HypergraphLike.Finite (ofGraph G) :=
  GraphLike.finite_of_finite_verts_edges
    (by simpa only [ofGraph_vertexSet] using G.vertexSet_finite)
    (by simpa only [ofGraph_edgeSet] using G.edgeSet_finite)

/-! ## Classification of the fibres of `toGraph` -/

lemma vertexSet_eq_of_toGraph_eq (h : P.toGraph = Q.toGraph) : P.vertexSet = Q.vertexSet := by
  exact congrArg Graph.vertexSet h

lemma edgeSet_eq_of_toGraph_eq (h : P.toGraph = Q.toGraph) : P.edgeSet = Q.edgeSet := by
  exact congrArg Graph.edgeSet h

noncomputable def chosenInc (P : Pseudograph V I E) {e : E} (he : e ∈ P.edgeSet) : I(P) :=
  (mem_edgeSet_iff.mp he).choose

lemma chosenInc_edge (P : Pseudograph V I E) {e : E} (he : e ∈ P.edgeSet) :
    P.edgeMap' (chosenInc P he) = e :=
  (mem_edgeSet_iff.mp he).choose_spec

lemma chosenInc_congr (P : Pseudograph V I E) {e e' : E} (he : e ∈ P.edgeSet)
    (he' : e' ∈ P.edgeSet) (h : e = e') : chosenInc P he = chosenInc P he' := by
  subst h
  exact congrArg (chosenInc P (e := e)) (Subsingleton.elim _ _)

lemma chosenInc_repr (P : Pseudograph V I E) {e : E} (he : e ∈ P.edgeSet) :
    chosenInc P (P.edgeMap'_mem (chosenInc P he)) = chosenInc P he :=
  chosenInc_congr P _ _ (chosenInc_edge P he)

lemma chosenInc_repr_other (P : Pseudograph V I E) {e : E} (he : e ∈ P.edgeSet) :
    chosenInc P (P.edgeMap'_mem (P.other' (chosenInc P he))) = chosenInc P he :=
  chosenInc_congr P _ _ (by rw [P.edgeMap'_other', chosenInc_edge])

lemma eq_chosenInc_or_other (P : Pseudograph V I E) (i : I(P)) :
    i = chosenInc P (P.edgeMap'_mem i) ∨
      i = P.other' (chosenInc P (P.edgeMap'_mem i)) := by
  apply (GraphLike.edgeMap'_val_eq_iff (chosenInc P (P.edgeMap'_mem i)) i).1
  exact (chosenInc_edge P (P.edgeMap'_mem i)).trans rfl

lemma isLink_transfer (h : P.toGraph = Q.toGraph) (i : I(P)) :
    ∃ j : I(Q), Q.edgeMap' j = P.edgeMap' i ∧ Q.attach' j = P.attach' i ∧
      Q.attach' (Q.other' j) = P.attach' (P.other' i) := by
  apply toGraph_isLink_iff.mp
  rw [← h]
  exact P.isLink_edgeMap_attach i

noncomputable def chosenQInc (h : P.toGraph = Q.toGraph) (i : I(P)) : I(Q) :=
  (isLink_transfer h i).choose

lemma chosenQInc_spec (h : P.toGraph = Q.toGraph) (i : I(P)) :
    Q.edgeMap' (chosenQInc h i) = P.edgeMap' i ∧ Q.attach' (chosenQInc h i) = P.attach' i ∧
    Q.attach' (Q.other' (chosenQInc h i)) = P.attach' (P.other' i) :=
  (isLink_transfer h i).choose_spec

noncomputable def incMap (h : P.toGraph = Q.toGraph) (i : I(P)) : I(Q) :=
  if i = chosenInc P (P.edgeMap'_mem i) then
    chosenQInc h (chosenInc P (P.edgeMap'_mem i))
  else Q.other' (chosenQInc h (chosenInc P (P.edgeMap'_mem i)))

lemma incMap_chosenInc (h : P.toGraph = Q.toGraph) {e : E} (he : e ∈ P.edgeSet) :
    incMap h (chosenInc P he) = chosenQInc h (chosenInc P he) := by
  unfold incMap
  split_ifs with hi
  · congr 1
    exact chosenInc_repr P he
  exact (hi (chosenInc_repr P he).symm).elim

lemma incMap_chosenInc_other (h : P.toGraph = Q.toGraph) {e : E} (he : e ∈ P.edgeSet) :
    incMap h (P.other' (chosenInc P he)) = Q.other' (chosenQInc h (chosenInc P he)) := by
  unfold incMap
  have hp := chosenInc_repr_other P he
  have hne : P.other' (chosenInc P he) ≠
      chosenInc P (P.edgeMap'_mem (P.other' (chosenInc P he))) := by
    rw [hp]
    exact P.other'_ne _
  split_ifs with hi
  · exact (hne hi).elim
  rw [hp]

lemma incMap_edge (h : P.toGraph = Q.toGraph) (i : I(P)) :
    Q.edgeMap' (incMap h i) = P.edgeMap' i := by
  unfold incMap
  split_ifs
  · rw [(chosenQInc_spec h _).1, chosenInc_edge]
  rw [Q.edgeMap'_other', (chosenQInc_spec h _).1, chosenInc_edge]

lemma incMap_vertex (h : P.toGraph = Q.toGraph) (i : I(P)) :
    Q.attach' (incMap h i) = P.attach' i := by
  obtain hi | hi := eq_chosenInc_or_other P i
  · rw [hi, incMap_chosenInc, (chosenQInc_spec h _).2.1]
  rw [hi, incMap_chosenInc_other, (chosenQInc_spec h _).2.2]

lemma incMap_injective (h : P.toGraph = Q.toGraph) : Injective (incMap h) := by
  intro i j hij
  have heij : P.edgeMap' i = P.edgeMap' j := by
    rw [← incMap_edge h i, hij, incMap_edge h j]
  have hp0 : chosenInc P (P.edgeMap'_mem i) = chosenInc P (P.edgeMap'_mem j) :=
    chosenInc_congr P _ _ heij
  obtain hi | hi := eq_chosenInc_or_other P i <;> obtain hj | hj := eq_chosenInc_or_other P j
  · rw [hi, hj, hp0]
  · rw [hi, incMap_chosenInc, hj, incMap_chosenInc_other, hp0] at hij
    exact False.elim <| (Q.other'_ne (chosenQInc h (chosenInc P (P.edgeMap'_mem i))))
      (by convert hij.symm)
  · rw [hi, incMap_chosenInc_other, hj, incMap_chosenInc, hp0] at hij
    exact False.elim <| (Q.other'_ne (chosenQInc h (chosenInc P (P.edgeMap'_mem i))))
      (by convert hij)
  rw [hi, hj, hp0]

lemma incMap_surjective (h : P.toGraph = Q.toGraph) : Surjective (incMap h) := by
  intro k
  have heP : Q.edgeMap' k ∈ P.edgeSet :=
    (edgeSet_eq_of_toGraph_eq h).symm ▸ Q.edgeMap'_mem k
  let p0 := chosenInc P heP
  let q0 := chosenQInc h p0
  have hq0e : Q.edgeMap' q0 = Q.edgeMap' k := by
    rw [(chosenQInc_spec h p0).1, chosenInc_edge]
  obtain hk | hk := (GraphLike.edgeMap'_val_eq_iff q0 k).1 hq0e
  · refine ⟨p0, ?_⟩
    rw [incMap_chosenInc]
    exact hk.symm
  refine ⟨P.other' p0, ?_⟩
  rw [incMap_chosenInc_other]
  exact hk.symm

noncomputable def equivOfToGraphEq (h : P.toGraph = Q.toGraph) : P.Equiv Q where
  vertexSet_eq := vertexSet_eq_of_toGraph_eq h
  incEquiv := _root_.Equiv.ofBijective (incMap h) ⟨incMap_injective h, incMap_surjective h⟩
  edge_eq := fun i ↦ incMap_edge h i
  vertex_eq := fun i ↦ incMap_vertex h i

/-- Two pseudographs forget to the same coarse graph exactly when they differ by an incidence
relabelling. -/
theorem nonempty_equiv_iff_toGraph_eq (P : Pseudograph V I E) (Q : Pseudograph V J E) :
    Nonempty (P.Equiv Q) ↔ P.toGraph = Q.toGraph :=
  ⟨fun ⟨F⟩ ↦ F.toGraph_eq, fun h ↦ ⟨equivOfToGraphEq h⟩⟩

@[deprecated nonempty_equiv_iff_toGraph_eq +typeChanged (since := "2026-08-20")]
theorem incidenceRel_iff_toGraph_eq (P : Pseudograph V I E) (Q : Pseudograph V J E) :
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

end Pseudograph
