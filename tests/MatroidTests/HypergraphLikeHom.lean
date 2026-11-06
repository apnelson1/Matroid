/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
import Matroid.GraphTheory.HypergraphLike.Hom
import Mathlib.Combinatorics.Hypergraph.Basic
import Matroid.GraphTheory.IncidenceHypergraph.Basic

open Set Function HypergraphLike

namespace HypergraphLikeTest

local instance (G : Bool) : HypergraphLike Unit Bool Unit G where
  verts := univ
  edges := univ
  incs := univ
  edgeMap' _ := ⟨(), trivial⟩
  attach' _ := ⟨(), trivial⟩
  IsSource _ := True
  IsTarget _ := G = true
  mem_incs_iff := by simp

private def addTargets : Hom false true where
  vertMap' := id
  incMap' := id
  edgeMap' := id
  map_attach' _ := rfl
  map_edgeMap' _ := rfl
  map_isSource' := id
  map_isTarget' _ := rfl
  isLocallySurjective _ j hj := ⟨j, hj, rfl⟩

example : Bijective addTargets.vertMap' ∧ Bijective addTargets.incMap' ∧
    Bijective addTargets.edgeMap' := ⟨bijective_id, bijective_id, bijective_id⟩

example : Emb false true :=
  Emb.ofInjOn addTargets
    (by intro x hx y hy h; exact Subsingleton.elim _ _)
    (by intro x hx y hy h; simpa [IncHom.incMap, addTargets, incs] using h)
    (by intro x hx y hy h; exact Subsingleton.elim _ _)

example : IsLink true () () () :=
  ⟨⟨false, true, by decide, trivial, rfl, rfl, rfl, rfl, rfl⟩⟩

example : ¬ IsLink false () () () := by
  intro h
  obtain ⟨l⟩ := h
  cases l.isTarget_target

example : IsEmpty (Iso false true) where
  false F := by
    have h : false = true := F.isTarget_of_map' (i := ⟨false, trivial⟩) rfl
    cases h

private def collapse : IncHom true true where
  vertMap' := id
  incMap' _ := ⟨false, trivial⟩
  edgeMap' := id
  map_attach' _ := rfl
  map_edgeMap' _ := rfl
  map_isSource' := id
  map_isTarget' := id

example : ¬ Injective collapse.incMap' := by
  intro h
  have he := h (a₁ := ⟨false, trivial⟩) (a₂ := ⟨true, trivial⟩) rfl
  cases congrArg Subtype.val he

example : ¬ collapse.IsLocallySurjective := by
  intro h
  obtain ⟨i, _, hi⟩ := h ⟨(), trivial⟩ (a := ⟨true, trivial⟩) rfl
  cases congrArg Subtype.val hi

private def emptyGraph : IncidenceHypergraph Empty Empty Empty where
  vertexSet := ∅
  incidenceSet := ∅
  edgeSet := ∅
  attach' i := i.val.elim
  edgeMap' i := i.val.elim
  attach'_mem i := i.val.elim
  edgeMap'_mem i := i.val.elim

example : (Iso.id emptyGraph).symm = Iso.id emptyGraph := by simp

example : IncHom emptyGraph emptyGraph := IncHom.id _

example : Hom emptyGraph emptyGraph := Hom.id _

private def splitEdges : IncidenceHypergraph Unit Bool Bool where
  vertexSet := univ
  incidenceSet := univ
  edgeSet := univ
  attach' _ := ()
  attach'_mem _ := trivial
  edgeMap' i := i.val
  edgeMap'_mem _ := trivial

private def joinedEdges : IncidenceHypergraph Unit Bool Unit where
  vertexSet := univ
  incidenceSet := univ
  edgeSet := univ
  attach' _ := ()
  attach'_mem _ := trivial
  edgeMap' _ := ()
  edgeMap'_mem _ := trivial

private def joinEdges : IncHom splitEdges joinedEdges where
  vertMap' := id
  incMap' := id
  edgeMap' _ := ⟨(), trivial⟩
  map_attach' _ := rfl
  map_edgeMap' _ := rfl
  map_isSource' _ := trivial
  map_isTarget' _ := trivial

example : Bijective joinEdges.incMap' := bijective_id

example : ¬ joinEdges.IsLocallySurjective := by
  intro h
  obtain ⟨i, hi, hI⟩ := h ⟨false, trivial⟩ (a := ⟨true, trivial⟩) rfl
  have hf : i.val = false := congrArg Subtype.val hi
  have ht : i.val = true := congrArg Subtype.val hI
  cases hf.symm.trans ht

example : Hom emptyGraph joinedEdges where
  vertMap' x := x.val.elim
  incMap' i := i.val.elim
  edgeMap' e := e.val.elim
  map_attach' i := i.val.elim
  map_edgeMap' i := i.val.elim
  map_isSource' := fun {i} _ ↦ i.val.elim
  map_isTarget' := fun {i} _ ↦ i.val.elim
  isLocallySurjective e := e.val.elim

variable {α : Type*}

private abbrev setSystem (G : Hypergraph α) : IncidenceHypergraph α (α × Set α) (Set α) where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  incidenceSet := {p | p.2 ∈ G.edgeSet ∧ p.1 ∈ p.2}
  edgeMap' i := i.val.2
  edgeMap'_mem i := i.property.1
  attach' i := i.val.1
  attach'_mem i := G.mem_vertexSet_of_mem_edgeSet i.property.1 i.property.2

private lemma setSystem_incVerts (G : Hypergraph α) (e : G.edgeSet) :
    HypergraphLike.incVerts (setSystem G) e.val = e.val := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    change i.val.1 ∈ e.val
    change i.val.2 = e.val at hi
    exact hi ▸ i.property.2
  · intro hx
    exact ⟨⟨(x, e.val), e.property, hx⟩, rfl, rfl⟩

private lemma setSystem_adj_iff (G : Hypergraph α) (x y : α) :
    HypergraphLike.Adj (setSystem G) x y ↔
      x ≠ y ∧ ∃ e ∈ G.edgeSet, x ∈ e ∧ y ∈ e := by
  constructor
  · rintro ⟨e, ⟨l⟩⟩
    have hi := l.edgeMap'_source
    have hj := l.edgeMap'_target
    have hx := l.attach'_source
    have hy := l.attach'_target
    change l.source.2 = e at hi
    change l.target.2 = e at hj
    change l.source.1 = x at hx
    change l.target.1 = y at hy
    refine ⟨fun hxy ↦ l.source_ne_target (Prod.ext (hx.trans (hxy.trans hy.symm))
      (hi.trans hj.symm)), e, l.edge_mem_edgeSet, ?_, ?_⟩
    · exact (congrArg₂ Membership.mem hi hx).mp l.isSource_source.2
    · exact (congrArg₂ Membership.mem hj hy).mp l.isTarget_target.2
  · rintro ⟨hne, e, he, hx, hy⟩
    exact ⟨e, ⟨⟨(x, e), (y, e), fun h ↦ hne (congrArg Prod.fst h),
      ⟨he, hx⟩, ⟨he, hy⟩, rfl, rfl, rfl, rfl⟩⟩⟩

private def oneEdge {α : Type*} (s : Set α) : Hypergraph α where
  vertexSet := univ
  edgeSet := {s}
  subset_vertexSet_of_mem_edgeSet' := fun {_} _ ↦ subset_univ _

private def containEdge {α : Type*} {s t : Set α} (hst : s ⊆ t) :
    IncEmb (setSystem (oneEdge s)) (setSystem (oneEdge t)) where
  vertMap' := id
  edgeMap' _ := ⟨t, rfl⟩
  incMap' i := ⟨(i.val.1, t), rfl,
    hst ((congrArg (fun e ↦ i.val.1 ∈ e) (mem_singleton_iff.mp i.property.1)).mp i.property.2)⟩
  map_attach' _ := rfl
  map_edgeMap' _ := rfl
  map_isSource' := fun {i} _ ↦
    ⟨rfl, hst ((congrArg (fun e ↦ i.val.1 ∈ e)
      (mem_singleton_iff.mp i.property.1)).mp i.property.2)⟩
  map_isTarget' := fun {i} _ ↦
    ⟨rfl, hst ((congrArg (fun e ↦ i.val.1 ∈ e)
      (mem_singleton_iff.mp i.property.1)).mp i.property.2)⟩
  vertMap'_injective := injective_id
  edgeMap'_injective := fun e e' _ ↦
    Subtype.ext ((mem_singleton_iff.mp e.property).trans (mem_singleton_iff.mp e'.property).symm)
  incMap'_injective := by
    intro i j hij
    exact Subtype.ext (Prod.ext (congrArg (fun k ↦ k.val.1) hij)
      ((mem_singleton_iff.mp i.property.1).trans (mem_singleton_iff.mp j.property.1).symm))

example : ¬ (containEdge (subset_univ ({false} : Set Bool))).toIncHom.IsLocallySurjective := by
  intro h
  obtain ⟨i, _, hi⟩ := h ⟨{false}, rfl⟩ (a := ⟨(true, univ), rfl, trivial⟩) rfl
  have hfalse : i.val.1 = false :=
    mem_singleton_iff.mp
      ((congrArg (fun e ↦ i.val.1 ∈ e) (mem_singleton_iff.mp i.property.1)).mp i.property.2)
  have htrue : i.val.1 = true := congrArg (fun k ↦ k.val.1) hi
  cases hfalse.symm.trans htrue

private def identifyVertices : Hom (setSystem (oneEdge (univ : Set Bool)))
    (setSystem (oneEdge ({false} : Set Bool))) where
  vertMap' _ := ⟨false, trivial⟩
  incMap' _ := ⟨(false, {false}), rfl, rfl⟩
  edgeMap' _ := ⟨{false}, rfl⟩
  map_attach' _ := rfl
  map_edgeMap' _ := rfl
  map_isSource' _ := ⟨rfl, rfl⟩
  map_isTarget' _ := ⟨rfl, rfl⟩
  isLocallySurjective := by
    rintro ⟨e, rfl⟩ ⟨⟨v, f⟩, hf, hv⟩ _
    change f = {false} at hf
    subst f
    change v = false at hv
    subst v
    exact ⟨⟨(false, univ), rfl, trivial⟩, rfl, rfl⟩

example : ¬ Injective identifyVertices.vertMap := by
  intro h
  have he := h (a₁ := false) (a₂ := true)
    (by simp [IncHom.vertMap, identifyVertices, verts, oneEdge])
  cases he

example : Adj (setSystem (oneEdge (univ : Set Bool))) false true := by
  rw [setSystem_adj_iff]
  simp [oneEdge]

example : ¬ Adj (setSystem (oneEdge ({false} : Set Bool)))
     (identifyVertices.vertMap false) (identifyVertices.vertMap true) := by
  rw [setSystem_adj_iff]
  simp [identifyVertices, IncHom.vertMap, verts, oneEdge]

example {α β : Type*} [Nonempty β] {G : Hypergraph α} {H : Hypergraph β}
    (F : Hom (setSystem G) (setSystem H)) {e : Set α} (he : e ∈ G.edgeSet) :
    F.vertMap '' e = F.edgeMap e := by
  have h := F.image_incVerts he
  rw [setSystem_incVerts G ⟨e, he⟩,
    setSystem_incVerts H ⟨F.edgeMap e, F.edgeMap_mem he⟩] at h
  exact h

example : (∅ : Set Empty) ∈ (setSystem (oneEdge (∅ : Set Empty))).edgeSet := rfl

example : Hom (setSystem (oneEdge (∅ : Set Empty))) (setSystem (oneEdge (∅ : Set Empty))) :=
  Hom.id _

example {V I E T V' I' E' T' : Type*} {G : T} {H : T'}
    [HypergraphLike V I E G] [HypergraphLike V' I' E' H] [Nonempty V'] (F : Emb G H)
    {x y : V} (h : Adj G x y) : Adj H (F.vertMap x) (F.vertMap y) := F.map_adj h

section TotalMaps

variable {V I E T V' I' E' T' V'' I'' E'' T'' : Type*}
  {G : T} {H : T'} {K : T''}
  [HypergraphLike V I E G] [HypergraphLike V' I' E' H]
  [HypergraphLike V'' I'' E'' K]

example [Nonempty V'] [Nonempty E'] (F : Iso G H) {e : E} (he : e ∈ E(G)) :
    F.vertMap '' incVerts G e = incVerts H (F.edgeMap e) := F.image_incVerts he

example [Nonempty I'] [Nonempty E'] (F : Iso G H) {e : E} (he : e ∈ E(G)) :
    BijOn F.incMap (edgeFiber G e) (edgeFiber H (F.edgeMap e)) := F.bijOn_incMap he

example [Nonempty V'] [Nonempty E'] (F : Iso G H) {e : E} {x : V}
    (he : e ∈ E(G)) (hx : x ∈ V(G)) :
    F.vertMap x ∈ incVerts H (F.edgeMap e) ↔ x ∈ incVerts G e :=
  F.mem_incVerts_map_iff he hx

example [Nonempty V'] (F : Iso G H) {x y : V} (h : Adj G x y) :
    Adj H (F.vertMap x) (F.vertMap y) := F.map_adj h

example [Nonempty V'] [Nonempty I'] [Nonempty E'] {F F' : Iso G H}
    (hv : EqOn F.vertMap F'.vertMap V(G)) (hi : EqOn F.incMap F'.incMap I(G))
    (he : EqOn F.edgeMap F'.edgeMap E(G)) : F = F' := by
  ext
  · exact hv ‹_›
  · exact hi ‹_›
  · exact he ‹_›

example [Nonempty V'] [Nonempty I'] [Nonempty E']
    [Nonempty V''] [Nonempty I''] [Nonempty E''] (F : Iso G H) (F' : Iso H K)
    {x : V} {i : I} {e : E} (hx : x ∈ V(G)) (hi : i ∈ I(G)) (he : e ∈ E(G)) :
    (F.comp F').vertMap x = F'.vertMap (F.vertMap x) ∧
      (F.comp F').incMap i = F'.incMap (F.incMap i) ∧
      (F.comp F').edgeMap e = F'.edgeMap (F.edgeMap e) := by
  simp [hx, hi, he]

example [Nonempty V] [Nonempty I] [Nonempty E]
    {x : V} {i : I} {e : E} (hx : x ∈ V(G)) (hi : i ∈ I(G)) (he : e ∈ E(G)) :
    (Iso.id G).vertMap x = x ∧ (Iso.id G).incMap i = i ∧ (Iso.id G).edgeMap e = e := by
  simp [hx, hi, he]

example [Nonempty V] [Nonempty I] [Nonempty E] [Nonempty V'] [Nonempty I'] [Nonempty E']
    (F : Iso G H) {x : V} {i : I} {e : E}
    (hx : x ∈ V(G)) (hi : i ∈ I(G)) (he : e ∈ E(G)) :
    F.symm.vertMap (F.vertMap x) = x ∧ F.symm.incMap (F.incMap i) = i ∧
      F.symm.edgeMap (F.edgeMap e) = e := by
  simp [hx, hi, he]

example [Nonempty V'] [Nonempty I'] [Nonempty E'] (F : IncHom G H)
    (hv : BijOn F.vertMap V(G) V(H)) (hi : BijOn F.incMap I(G) I(H))
    (he : BijOn F.edgeMap E(G) E(H))
    (hs : ∀ i ∈ I(G), IsSource H (F.incMap i) → IsSource G i)
    (ht : ∀ i ∈ I(G), IsTarget H (F.incMap i) → IsTarget G i) :
    (Iso.ofBijOn F hv hi he hs ht).toIncHom = F := rfl

end TotalMaps

private def emptySupport : IncidenceHypergraph Bool Bool Bool where
  vertexSet := ∅
  incidenceSet := ∅
  edgeSet := ∅
  attach' i := i.property.elim
  edgeMap' i := i.property.elim
  attach'_mem i := i.property.elim
  edgeMap'_mem i := i.property.elim

example : BijOn (Iso.id emptySupport).vertMap V(emptySupport) V(emptySupport) :=
  (Iso.id emptySupport).vertMap_bijOn

example : ¬ Injective (Iso.id emptySupport).vertMap := by
  intro h
  have he := h (a₁ := false) (a₂ := true) (by simp [IncHom.vertMap, verts, emptySupport])
  cases he

end HypergraphLikeTest
