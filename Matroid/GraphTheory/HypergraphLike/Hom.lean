/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.HypergraphLike.Basic

/-!
# Incidence maps and homomorphisms of graph-like structures

The stored maps `vertMap'`, `incMap'` and `edgeMap'` act on vertices, incidences and edges,
respectively, as members of their ground sets, without nonemptiness assumptions. The public maps
`vertMap`, `incMap` and `edgeMap` extend these maps to all labels when the corresponding target
label type is nonempty. They take arbitrary values on unused source labels, so their laws require
membership in the source ground sets. The two graphs may have different representations and label
types.

## Choosing a morphism

* `HypergraphLike.IncHom` respects incidence and its allowed directions of traversal. It may
  forget directedness by mapping a directed incidence to an undirected one, identify incidences,
  or omit incidences of a mapped edge. This is the usual morphism of incidence hypergraphs.
* `HypergraphLike.IncEmb` is an `IncHom` injective on vertices, incidences and edges. It is the
  usual incidence embedding, allowing partial edge fibers.
* `HypergraphLike.Hom` additionally maps each edge's incidence fiber onto the target edge's
  fiber. It specializes to exact-edge-image homomorphisms for set systems and to graph
  homomorphisms for undirected incidence graphs.
* `HypergraphLike.Emb` is a `Hom` injective on vertices, incidences and edges. It preserves
  entire edge fibers but need not be induced.
* `HypergraphLike.Iso` has specified two-sided inverses and preserves the directedness of every
  incidence in both directions. Every isomorphism automatically maps edge fibers bijectively,
  so both notions share `Iso`.

`IncHom.IsLocallySurjective` names the additional condition independently of its bundling in
`Hom`. Here local surjectivity is at edges, not at vertices, and does not require the edge map
itself to be surjective. For incidence hypergraphs it specifies a restricted class of morphisms;
it is not part of their conventional homomorphism definition.

## Implementation notes

Forward maps are stored once. `Hom` and `IncEmb` extend `IncHom`, while `Emb` extends both.
`Iso` extends `Emb`, giving direct access to the homomorphism and embedding APIs. Bundled
carrier embeddings and equivalences are derived views. `F.comp F'` means first `F`, then `F'`.

A general hypergraph `Hom` can still identify incidences within an edge, so link preservation
requires incidence injectivity. Even an injective, locally surjective morphism can forget
directedness; `Iso` requires the inverse to respect directions as well. The structures and their
identity, composition and symmetry operations do not require nonempty label types.
-/

@[expose] public section

open Set Function

namespace HypergraphLike

variable {V₀ I₀ E₀ Gr₀ V₁ I₁ E₁ Gr₁ V₂ I₂ E₂ Gr₂ V₃ I₃ E₃ Gr₃ : Type*} {x y : V₀} {i j : I₀}
  {G : Gr₀} [HypergraphLike V₀ I₀ E₀ G] {H : Gr₁} [HypergraphLike V₁ I₁ E₁ H] {e : E₀}
  {K : Gr₂} [HypergraphLike V₂ I₂ E₂ K] {L : Gr₃} [HypergraphLike V₃ I₃ E₃ L]

/-- A map of vertices, incidences and edges respecting incidence and its allowed directions of
traversal. Directed incidences may map to undirected incidences. -/
structure IncHom (G : Gr₀) (H : Gr₁) [HypergraphLike V₀ I₀ E₀ G] [HypergraphLike V₁ I₁ E₁ H] where
  /-- The function on vertices. -/
  vertMap' : V(G) → V(H)
  /-- The function on incidences. -/
  incMap' : I(G) → I(H)
  /-- The function on edges. -/
  edgeMap' : E(G) → E(H)
  /-- Incidence maps commute with attachment to vertices. -/
  map_attach' (i : I(G)) : attach' (incMap' i) = vertMap' (attach' i)
  /-- Incidence maps commute with assignment to edges. -/
  map_edgeMap' (i : I(G)) :
    HypergraphLike.edgeMap' (incMap' i) = edgeMap' (HypergraphLike.edgeMap' i)
  /-- Traversal from a vertex to an edge remains allowed at the image incidence. -/
  map_isSource' {i : I(G)} : IsSource G i.val → IsSource H (incMap' i).val
  /-- Traversal from an edge to a vertex remains allowed at the image incidence. -/
  map_isTarget' {i : I(G)} : IsTarget G i.val → IsTarget H (incMap' i).val

/-- An incidence homomorphism injective on vertices, incidences and edges.
It may omit incidences of mapped edges and need not be induced. -/
structure IncEmb (G : Gr₀) (H : Gr₁) [HypergraphLike V₀ I₀ E₀ G] [HypergraphLike V₁ I₁ E₁ H]
    extends IncHom G H where
  /-- Distinct vertices have distinct images. -/
  vertMap'_injective : Injective vertMap'
  /-- Distinct incidences have distinct images. -/
  incMap'_injective : Injective incMap'
  /-- Distinct edges have distinct images. -/
  edgeMap'_injective : Injective edgeMap'

namespace IncHom

/-- Every incidence of a mapped edge comes from an incidence of that source edge.
This condition does not assert global surjectivity of the edge or incidence maps.
Its definition uses ground sets to avoid nonemptiness assumptions; the public characterization
`isLocallySurjective_iff` uses total maps and `edgeFiber`. -/
def IsLocallySurjective (F : IncHom G H) : Prop :=
  ∀ e : E(G), SurjOn F.incMap' {i | HypergraphLike.edgeMap' i = e}
    {j | HypergraphLike.edgeMap' j = F.edgeMap' e}

private lemma ext' {F F' : IncHom G H} (hV : ∀ x, F.vertMap' x = F'.vertMap' x)
    (hI : ∀ i, F.incMap' i = F'.incMap' i) (hE : ∀ e, F.edgeMap' e = F'.edgeMap' e) : F = F' :=
  (mk.injEq ..).mpr ⟨funext hV, funext hI, funext hE⟩

open Classical in
/-- The map on all vertex labels, taking an arbitrary value on unused labels. -/
noncomputable def vertMap [Nonempty V₁] (F : IncHom G H) (x : V₀) : V₁ :=
  if h : x ∈ V(G) then F.vertMap' ⟨x, h⟩ else Classical.arbitrary V₁

@[simp]
lemma vertMap'_eq_vertMap [Nonempty V₁] (F : IncHom G H) (x : V(G)) :
    (F.vertMap' x).val = F.vertMap x.val := by simp [vertMap]

lemma vertMap_mem [Nonempty V₁] (F : IncHom G H) {x : V₀} (h : x ∈ V(G)) : F.vertMap x ∈ V(H) := by
  simpa using (F.vertMap' ⟨x, h⟩).property

open Classical in
/-- The map on all incidence labels, taking an arbitrary value on unused labels. -/
noncomputable def incMap [Nonempty I₁] (F : IncHom G H) (i : I₀) : I₁ :=
  if h : i ∈ I(G) then F.incMap' ⟨i, h⟩ else Classical.arbitrary I₁

@[simp]
lemma incMap'_eq_incMap [Nonempty I₁] (F : IncHom G H) (i : I(G)) :
    (F.incMap' i).val = F.incMap i.val := by simp [incMap]

lemma incMap_mem [Nonempty I₁] (F : IncHom G H) {i : I₀} (h : i ∈ I(G)) : F.incMap i ∈ I(H) := by
  simpa using (F.incMap' ⟨i, h⟩).property

open Classical in
/-- The map on all edge labels, taking an arbitrary value on unused labels. -/
noncomputable def edgeMap [Nonempty E₁] (F : IncHom G H) (e : E₀) : E₁ :=
  if h : e ∈ E(G) then F.edgeMap' ⟨e, h⟩ else Classical.arbitrary E₁

@[simp]
lemma edgeMap'_eq_edgeMap [Nonempty E₁] (F : IncHom G H) (e : E(G)) :
    (F.edgeMap' e).val = F.edgeMap e.val := by simp [edgeMap]

lemma edgeMap_mem [Nonempty E₁] (F : IncHom G H) {e : E₀} (h : e ∈ E(G)) : F.edgeMap e ∈ E(H) := by
  simpa using (F.edgeMap' ⟨e, h⟩).property

@[ext]
lemma ext [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] {F F' : IncHom G H}
    (hV : ∀ x ∈ V(G), F.vertMap x = F'.vertMap x) (hI : ∀ i ∈ I(G), F.incMap i = F'.incMap i)
    (hE : ∀ e ∈ E(G), F.edgeMap e = F'.edgeMap e) : F = F' :=
  ext' (fun x ↦ Subtype.ext (by simpa using hV x.val x.property))
    (fun i ↦ Subtype.ext (by simpa using hI i.val i.property))
    (fun e ↦ Subtype.ext (by simpa using hE e.val e.property))

/-- The identity homomorphism. -/
def id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : IncHom G G where
  vertMap' := _root_.id
  incMap' := _root_.id
  edgeMap' := _root_.id
  map_attach' _ := rfl
  map_edgeMap' _ := rfl
  map_isSource' := _root_.id
  map_isTarget' := _root_.id

/-- Composition in diagrammatic order. -/
def comp (F : IncHom G H) (F' : IncHom H K) : IncHom G K where
  vertMap' := F'.vertMap' ∘ F.vertMap'
  incMap' := F'.incMap' ∘ F.incMap'
  edgeMap' := F'.edgeMap' ∘ F.edgeMap'
  map_attach' i := (F'.map_attach' _).trans (congrArg F'.vertMap' (F.map_attach' i))
  map_edgeMap' i := (F'.map_edgeMap' _).trans (congrArg F'.edgeMap' (F.map_edgeMap' i))
  map_isSource' h := F'.map_isSource' (F.map_isSource' h)
  map_isTarget' h := F'.map_isTarget' (F.map_isTarget' h)

@[simp]
lemma id_comp (F : IncHom G H) : (id G).comp F = F := rfl

@[simp]
lemma comp_id (F : IncHom G H) : F.comp (id H) = F := rfl

lemma comp_assoc (F : IncHom G H) (F' : IncHom H K) (F'' : IncHom K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := rfl

@[simp]
lemma vertMap_id [Nonempty V₀] (h : x ∈ V(G)) : (id G).vertMap x = x := by simp [vertMap, id, h]

@[simp]
lemma vertMap_comp [Nonempty V₁] [Nonempty V₂] (F : IncHom G H) (F' : IncHom H K)
    (h : x ∈ V(G)) : (F.comp F').vertMap x = F'.vertMap (F.vertMap x) := by
  simp [vertMap, comp, h, -vertMap'_eq_vertMap]

@[simp]
lemma incMap_id [Nonempty I₀] (h : i ∈ I(G)) : (id G).incMap i = i := by simp [incMap, id, h]

@[simp]
lemma incMap_comp [Nonempty I₁] [Nonempty I₂] (F : IncHom G H) (F' : IncHom H K)
    (h : i ∈ I(G)) : (F.comp F').incMap i = F'.incMap (F.incMap i) := by
  simp [incMap, comp, h, -incMap'_eq_incMap]

@[simp]
lemma edgeMap_id [Nonempty E₀] (h : e ∈ E(G)) : (id G).edgeMap e = e := by simp [edgeMap, id, h]

@[simp]
lemma edgeMap_comp [Nonempty E₁] [Nonempty E₂] (F : IncHom G H) (F' : IncHom H K)
    (h : e ∈ E(G)) : (F.comp F').edgeMap e = F'.edgeMap (F.edgeMap e) := by
  simp [edgeMap, comp, h, -edgeMap'_eq_edgeMap]

@[simp]
lemma isLocallySurjective_id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] :
    (id G).IsLocallySurjective := fun _ j hj ↦ ⟨j, hj, rfl⟩

lemma IsLocallySurjective.comp {F : IncHom G H} {F' : IncHom H K}
    (hF : F.IsLocallySurjective) (hF' : F'.IsLocallySurjective) :
    (F.comp F').IsLocallySurjective := fun e ↦ (hF' (F.edgeMap' e)).comp (hF e)

lemma map_attach [Nonempty V₀] [Nonempty V₁] [Nonempty I₁] (F : IncHom G H)
    (hi : i ∈ I(G)) : attach H (F.incMap i) = F.vertMap (attach G i) := by
  simpa using congrArg Subtype.val (F.map_attach' ⟨i, hi⟩)

lemma map_edgeMap [Nonempty E₀] [Nonempty E₁] [Nonempty I₁] (F : IncHom G H) (hi : i ∈ I(G)) :
    HypergraphLike.edgeMap H (F.incMap i) = F.edgeMap (HypergraphLike.edgeMap G i) := by
  simpa using congrArg Subtype.val (F.map_edgeMap' ⟨i, hi⟩)

lemma map_isSource [Nonempty I₁] (F : IncHom G H) (hi : IsSource G i) :
    IsSource H (F.incMap i) := by simpa using F.map_isSource' (i := ⟨i, hi.mem_incs⟩) hi

lemma map_isTarget [Nonempty I₁] (F : IncHom G H) (hi : IsTarget G i) :
    IsTarget H (F.incMap i) := by simpa using F.map_isTarget' (i := ⟨i, hi.mem_incs⟩) hi

lemma mapsTo_edgeFiber [Nonempty I₁] [Nonempty E₁] (F : IncHom G H) :
    MapsTo F.incMap (edgeFiber G e) (edgeFiber H (F.edgeMap e)) := by
  rintro _ ⟨i, hi, rfl⟩
  refine ⟨F.incMap' i, ?_, F.incMap'_eq_incMap i⟩
  simpa only [mem_ofPred_eq, F.map_edgeMap', F.edgeMap'_eq_edgeMap] using congrArg F.edgeMap hi

lemma isLocallySurjective_iff [Nonempty I₁] [Nonempty E₁] (F : IncHom G H) : F.IsLocallySurjective ↔
    ∀ e ∈ E(G), SurjOn F.incMap (edgeFiber G e) (edgeFiber H (F.edgeMap e)) := by
  simp only [IsLocallySurjective, SurjOn, Subtype.ext_iff, val_edgeMap', edgeMap'_eq_edgeMap,
    subset_def, mem_ofPred_eq, mem_image, incMap'_eq_incMap, Subtype.exists, exists_and_right,
    Subtype.forall, edgeFiber, exists_prop, exists_eq_right, and_imp]

lemma IsLocallySurjective.surjOn_incMap [Nonempty I₁] [Nonempty E₁] {F : IncHom G H}
    (hF : F.IsLocallySurjective) (he : e ∈ E(G)) :
    SurjOn F.incMap (edgeFiber G e) (edgeFiber H (F.edgeMap e)) :=
  (F.isLocallySurjective_iff.mp hF) e he

lemma isLocallySurjective_of_surjOn_of_injOn [Nonempty I₁] [Nonempty E₁] (F : IncHom G H)
    (hi : SurjOn F.incMap I(G) I(H)) (he : InjOn F.edgeMap E(G)) : F.IsLocallySurjective := by
  intro e j hj
  obtain ⟨i, hi, hij⟩ := hi j.property
  obtain rfl : F.incMap' ⟨i, hi⟩ = j := Subtype.ext ((F.incMap'_eq_incMap ⟨i, hi⟩).trans hij)
  refine ⟨⟨i, hi⟩, Subtype.ext (he (HypergraphLike.edgeMap' ⟨i, hi⟩).property e.property ?_), rfl⟩
  simpa using congrArg Subtype.val ((F.map_edgeMap' ⟨i, hi⟩).symm.trans hj)

lemma map_mem_incVerts [Nonempty V₁] [Nonempty E₁] (F : IncHom G H)
    (h : x ∈ incVerts G e) : F.vertMap x ∈ incVerts H (F.edgeMap e) := by
  obtain ⟨i, he, rfl⟩ := h
  refine ⟨F.incMap' i, ?_, ?_⟩
  · simpa only [mem_ofPred_eq, F.map_edgeMap', F.edgeMap'_eq_edgeMap] using congrArg F.edgeMap he
  simp only [F.map_attach', F.vertMap'_eq_vertMap]

lemma map_mem_incEdges [Nonempty V₁] [Nonempty E₁] (F : IncHom G H)
    (h : e ∈ incEdges G x) : F.edgeMap e ∈ incEdges H (F.vertMap x) :=
  mem_incEdges.mpr (F.map_mem_incVerts (mem_incEdges.mp h))

/-- Injectivity on this edge's fiber keeps the two witnesses of a link distinct. -/
lemma map_isLink_of_injOn [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] (F : IncHom G H)
    (hi : InjOn F.incMap (edgeFiber G e)) (h : IsLink G e x y) :
    IsLink H (F.edgeMap e) (F.vertMap x) (F.vertMap y) := by
  obtain ⟨l⟩ := h
  let i : I(G) := ⟨l.source, l.isSource_source.mem_incs⟩
  let j : I(G) := ⟨l.target, l.isTarget_target.mem_incs⟩
  refine ⟨⟨(F.incMap' i).val, (F.incMap' j).val, ?_,
    F.map_isSource' l.isSource_source, F.map_isTarget' l.isTarget_target, ?_, ?_, ?_, ?_⟩⟩
  · exact fun h ↦ l.source_ne_target
      (hi ⟨i, l.edgeMap'_source, rfl⟩ ⟨j, l.edgeMap'_target, rfl⟩ (by simpa using h))
  · rw [F.map_edgeMap', F.edgeMap'_eq_edgeMap, l.edgeMap'_source]
  · rw [F.map_edgeMap', F.edgeMap'_eq_edgeMap, l.edgeMap'_target]
  · rw [F.map_attach', F.vertMap'_eq_vertMap, l.attach'_source]
  rw [F.map_attach', F.vertMap'_eq_vertMap, l.attach'_target]

lemma map_adj_of_injOn [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] (F : IncHom G H)
    (hi : InjOn F.incMap I(G)) (h : Adj G x y) : Adj H (F.vertMap x) (F.vertMap y) := by
  obtain ⟨e, he⟩ := h
  exact ⟨F.edgeMap e, F.map_isLink_of_injOn (hi.mono edgeFiber_subset_incs) he⟩

end IncHom

namespace IncEmb

private lemma ext' {F F' : IncEmb G H} (hV : ∀ x, F.vertMap' x = F'.vertMap' x)
    (hI : ∀ i, F.incMap' i = F'.incMap' i) (hE : ∀ e, F.edgeMap' e = F'.edgeMap' e) : F = F' :=
  (mk.injEq ..).mpr (IncHom.ext' hV hI hE)

lemma toIncHom_injective : Injective (toIncHom : IncEmb G H → IncHom G H) :=
  fun _ _ h ↦ (mk.injEq ..).mpr h

@[ext]
lemma ext [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] {F F' : IncEmb G H}
    (hV : ∀ x ∈ V(G), F.vertMap x = F'.vertMap x) (hI : ∀ i ∈ I(G), F.incMap i = F'.incMap i)
    (hE : ∀ e ∈ E(G), F.edgeMap e = F'.edgeMap e) : F = F' :=
  toIncHom_injective (IncHom.ext hV hI hE)

/-- Bundle a homomorphism whose maps on labels are injective on the source ground sets. -/
@[simps toIncHom]
def ofInjOn [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] (F : IncHom G H)
    (hv : InjOn F.vertMap V(G)) (hi : InjOn F.incMap I(G)) (he : InjOn F.edgeMap E(G)) :
    IncEmb G H where
  toIncHom := F
  vertMap'_injective := by simpa [Injective, Subtype.ext_iff] using hv.injective
  incMap'_injective := by simpa [Injective, Subtype.ext_iff] using hi.injective
  edgeMap'_injective := by simpa [Injective, Subtype.ext_iff] using he.injective

/-- Construct an incidence embedding from embeddings of the three ground sets. -/
def ofEmbeddings (v : V(G) ↪ V(H)) (i : I(G) ↪ I(H)) (e : E(G) ↪ E(H))
    (hv : ∀ j, attach' (i j) = v (attach' j))
    (he : ∀ j, HypergraphLike.edgeMap' (i j) = e (HypergraphLike.edgeMap' j))
    (hs : ∀ j, IsSource G j.val → IsSource H (i j).val)
    (ht : ∀ j, IsTarget G j.val → IsTarget H (i j).val) : IncEmb G H where
  vertMap' := v
  incMap' := i
  edgeMap' := e
  map_attach' := hv
  map_edgeMap' := he
  map_isSource' := hs _
  map_isTarget' := ht _
  vertMap'_injective := v.injective
  incMap'_injective := i.injective
  edgeMap'_injective := e.injective

/-- The identity incidence embedding. -/
@[simps toIncHom]
def id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : IncEmb G G where
  toIncHom := IncHom.id G
  vertMap'_injective := injective_id
  incMap'_injective := injective_id
  edgeMap'_injective := injective_id

/-- Composition in diagrammatic order. -/
@[simps toIncHom]
def comp (F : IncEmb G H) (F' : IncEmb H K) : IncEmb G K where
  toIncHom := F.toIncHom.comp F'.toIncHom
  vertMap'_injective := F'.vertMap'_injective.comp F.vertMap'_injective
  incMap'_injective := F'.incMap'_injective.comp F.incMap'_injective
  edgeMap'_injective := F'.edgeMap'_injective.comp F.edgeMap'_injective

@[simp]
lemma id_comp (F : IncEmb G H) : (id G).comp F = F := rfl

@[simp]
lemma comp_id (F : IncEmb G H) : F.comp (id H) = F := rfl

lemma comp_assoc (F : IncEmb G H) (F' : IncEmb H K) (F'' : IncEmb K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := rfl

lemma vertMap_injOn [Nonempty V₁] (F : IncEmb G H) : InjOn F.vertMap V(G) := by
  simpa [injOn_iff_injective, Injective, Subtype.ext_iff] using F.vertMap'_injective

/-- The derived embedding of vertices. -/
def vertEmbedding (F : IncEmb G H) : V(G) ↪ V(H) where
  toFun := F.vertMap'
  inj' := F.vertMap'_injective

lemma incMap_injOn [Nonempty I₁] (F : IncEmb G H) : InjOn F.incMap I(G) := by
  simpa [injOn_iff_injective, Injective, Subtype.ext_iff] using F.incMap'_injective

/-- The derived embedding of incidences. -/
def incEmbedding (F : IncEmb G H) : I(G) ↪ I(H) where
  toFun := F.incMap'
  inj' := F.incMap'_injective

lemma edgeMap_injOn [Nonempty E₁] (F : IncEmb G H) : InjOn F.edgeMap E(G) := by
  simpa [injOn_iff_injective, Injective, Subtype.ext_iff] using F.edgeMap'_injective

/-- The derived embedding of edges. -/
def edgeEmbedding (F : IncEmb G H) : E(G) ↪ E(H) where
  toFun := F.edgeMap'
  inj' := F.edgeMap'_injective

lemma map_isLink [Nonempty V₁] [Nonempty E₁] (F : IncEmb G H)
    {e : E₀} {x y : V₀} (h : IsLink G e x y) :
    IsLink H (F.edgeMap e) (F.vertMap x) (F.vertMap y) := by
  obtain ⟨l⟩ := h
  let : Nonempty I₁ := ⟨(F.incMap' ⟨l.source, l.isSource_source.mem_incs⟩).val⟩
  exact F.toIncHom.map_isLink_of_injOn (F.incMap_injOn.mono edgeFiber_subset_incs) ⟨l⟩

lemma map_adj [Nonempty V₁] (F : IncEmb G H)
    {x y : V₀} (h : Adj G x y) : Adj H (F.vertMap x) (F.vertMap y) := by
  obtain ⟨e, he⟩ := h
  let : Nonempty E₁ := ⟨(F.edgeMap' ⟨e, he.edge_mem_edgeSet⟩).val⟩
  exact ⟨F.edgeMap e, F.map_isLink he⟩

end IncEmb

/-- An incidence homomorphism mapping each edge's incidence fiber onto its image edge's fiber.
For set systems, this means exact edge images. For incidence hypergraphs, it is a restriction
of their usual morphisms; use `IncHom` for those. -/
structure Hom (G : Gr₀) (H : Gr₁) [HypergraphLike V₀ I₀ E₀ G] [HypergraphLike V₁ I₁ E₁ H]
    extends IncHom G H where
  /-- Every incidence of the image edge is reached from this edge. -/
  isLocallySurjective : toIncHom.IsLocallySurjective

/-- An injective homomorphism preserving entire edge fibers. This need not be induced.
Use `IncEmb` for incidence embeddings that may omit incidences of their image edges. -/
structure Emb (G : Gr₀) (H : Gr₁) [HypergraphLike V₀ I₀ E₀ G] [HypergraphLike V₁ I₁ E₁ H]
    extends Hom G H, IncEmb G H

/-- An embedding with specified two-sided inverses preserving incidence directedness
in both directions. -/
structure Iso (G : Gr₀) (H : Gr₁) [HypergraphLike V₀ I₀ E₀ G] [HypergraphLike V₁ I₁ E₁ H]
    extends Emb G H where
  /-- The inverse preserves allowed traversal from a vertex to an edge. -/
  isSource_of_map' {i : I(G)} : IsSource H (incMap' i).val → IsSource G i.val
  /-- The inverse preserves allowed traversal from an edge to a vertex. -/
  isTarget_of_map' {i : I(G)} : IsTarget H (incMap' i).val → IsTarget G i.val
  /-- The inverse function on vertices. -/
  invVertMap' : V(H) → V(G)
  /-- The inverse function on incidences. -/
  invIncMap' : I(H) → I(G)
  /-- The inverse function on edges. -/
  invEdgeMap' : E(H) → E(G)
  vertMap'_leftInverse (x : V(G)) : invVertMap' (vertMap' x) = x
  vertMap'_rightInverse (x : V(H)) : vertMap' (invVertMap' x) = x
  incMap'_leftInverse (x : I(G)) : invIncMap' (incMap' x) = x
  incMap'_rightInverse (x : I(H)) : incMap' (invIncMap' x) = x
  edgeMap'_leftInverse (x : E(G)) : invEdgeMap' (edgeMap' x) = x
  edgeMap'_rightInverse (x : E(H)) : edgeMap' (invEdgeMap' x) = x

namespace Hom

private lemma ext' {F F' : Hom G H} (hV : ∀ x, F.vertMap' x = F'.vertMap' x)
    (hI : ∀ i, F.incMap' i = F'.incMap' i) (hE : ∀ e, F.edgeMap' e = F'.edgeMap' e) : F = F' :=
  (mk.injEq ..).mpr (IncHom.ext' hV hI hE)

lemma toIncHom_injective : Injective (toIncHom : Hom G H → IncHom G H) :=
  fun _ _ h ↦ (mk.injEq ..).mpr h

@[ext]
lemma ext [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] {F F' : Hom G H}
    (hV : ∀ x ∈ V(G), F.vertMap x = F'.vertMap x) (hI : ∀ i ∈ I(G), F.incMap i = F'.incMap i)
    (hE : ∀ e ∈ E(G), F.edgeMap e = F'.edgeMap e) : F = F' :=
  toIncHom_injective (IncHom.ext hV hI hE)

/-- Bundle a locally surjective incidence homomorphism without changing its maps. -/
@[simps toIncHom]
def ofIncHom (F : IncHom G H) (hF : F.IsLocallySurjective) : Hom G H where
  toIncHom := F
  isLocallySurjective := hF

/-- The identity homomorphism. -/
@[simps! toIncHom]
def id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : Hom G G :=
  ofIncHom (IncHom.id G) (IncHom.isLocallySurjective_id G)

/-- Composition in diagrammatic order. -/
@[simps! toIncHom]
def comp (F : Hom G H) (F' : Hom H K) : Hom G K :=
  ofIncHom (F.toIncHom.comp F'.toIncHom) (F.isLocallySurjective.comp F'.isLocallySurjective)

@[simp]
lemma id_comp (F : Hom G H) : (id G).comp F = F := rfl

@[simp]
lemma comp_id (F : Hom G H) : F.comp (id H) = F := rfl

lemma comp_assoc (F : Hom G H) (F' : Hom H K) (F'' : Hom K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := rfl

/-- Each edge's incidences map onto all incidences of its image edge. -/
lemma surjOn_incMap [Nonempty I₁] [Nonempty E₁] (F : Hom G H) {e : E₀} (he : e ∈ E(G)) :
    SurjOn F.incMap (edgeFiber G e) (edgeFiber H (F.edgeMap e)) :=
  F.isLocallySurjective.surjOn_incMap he

/-- The vertices incident to an edge map onto exactly the vertices incident to its image edge. -/
lemma image_incVerts [Nonempty V₁] [Nonempty E₁] (F : Hom G H) {e : E₀} (he : e ∈ E(G)) :
    F.vertMap '' incVerts G e = incVerts H (F.edgeMap e) := by
  refine Subset.antisymm (image_subset_iff.mpr fun _ hx ↦ F.map_mem_incVerts hx) ?_
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨i, hi, rfl⟩ := F.isLocallySurjective ⟨e, he⟩
    (show HypergraphLike.edgeMap' j = F.edgeMap' ⟨e, he⟩ from
    Subtype.ext (by simpa using hj))
  refine ⟨(attach' i).val, ⟨i, congrArg Subtype.val hi, rfl⟩, ?_⟩
  simp only [F.map_attach', IncHom.vertMap'_eq_vertMap]

end Hom

namespace Emb

private lemma ext' {F F' : Emb G H} (hV : ∀ x, F.vertMap' x = F'.vertMap' x)
    (hI : ∀ i, F.incMap' i = F'.incMap' i) (hE : ∀ e, F.edgeMap' e = F'.edgeMap' e) : F = F' :=
  (mk.injEq ..).mpr (Hom.ext' hV hI hE)

lemma toHom_injective : Injective (toHom : Emb G H → Hom G H) :=
  fun _ _ h ↦ (mk.injEq ..).mpr h

lemma toIncHom_injective : Injective (fun F : Emb G H ↦ F.toIncHom) :=
  Hom.toIncHom_injective.comp toHom_injective

lemma toIncEmb_injective : Injective (toIncEmb : Emb G H → IncEmb G H) := fun _ _ h ↦
  toIncHom_injective (congrArg IncEmb.toIncHom h)

@[ext]
lemma ext [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] {F F' : Emb G H}
    (hV : ∀ x ∈ V(G), F.vertMap x = F'.vertMap x) (hI : ∀ i ∈ I(G), F.incMap i = F'.incMap i)
    (hE : ∀ e ∈ E(G), F.edgeMap e = F'.edgeMap e) : F = F' :=
  toIncHom_injective (IncHom.ext hV hI hE)

/-- Bundle a homomorphism whose maps on labels are injective on the source ground sets. -/
@[simps toHom]
def ofInjOn [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] (F : Hom G H)
    (hv : InjOn F.vertMap V(G)) (hi : InjOn F.incMap I(G)) (he : InjOn F.edgeMap E(G)) :
    Emb G H where
  toHom := F
  vertMap'_injective := (IncEmb.ofInjOn F.toIncHom hv hi he).vertMap'_injective
  incMap'_injective := (IncEmb.ofInjOn F.toIncHom hv hi he).incMap'_injective
  edgeMap'_injective := (IncEmb.ofInjOn F.toIncHom hv hi he).edgeMap'_injective

/-- Bundle an incidence embedding that preserves entire edge fibers. -/
@[simps toHom]
def ofIncEmb (F : IncEmb G H) (hF : F.toIncHom.IsLocallySurjective) : Emb G H where
  toHom := Hom.ofIncHom F.toIncHom hF
  vertMap'_injective := F.vertMap'_injective
  incMap'_injective := F.incMap'_injective
  edgeMap'_injective := F.edgeMap'_injective

@[simp]
lemma ofIncEmb_toIncEmb (F : IncEmb G H) (hF : F.toIncHom.IsLocallySurjective) :
    (ofIncEmb F hF).toIncEmb = F := rfl

/-- The identity embedding. -/
@[simps toHom]
def id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : Emb G G where
  toHom := Hom.id G
  vertMap'_injective := injective_id
  incMap'_injective := injective_id
  edgeMap'_injective := injective_id

/-- Composition in diagrammatic order. -/
@[simps toHom]
def comp (F : Emb G H) (F' : Emb H K) : Emb G K where
  toHom := F.toHom.comp F'.toHom
  vertMap'_injective := F'.vertMap'_injective.comp F.vertMap'_injective
  incMap'_injective := F'.incMap'_injective.comp F.incMap'_injective
  edgeMap'_injective := F'.edgeMap'_injective.comp F.edgeMap'_injective

@[simp]
lemma id_toIncEmb (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : (id G).toIncEmb = IncEmb.id G := rfl

@[simp]
lemma comp_toIncEmb (F : Emb G H) (F' : Emb H K) :
    (F.comp F').toIncEmb = F.toIncEmb.comp F'.toIncEmb := rfl

@[simp]
lemma id_comp (F : Emb G H) : (id G).comp F = F := rfl

@[simp]
lemma comp_id (F : Emb G H) : F.comp (id H) = F := rfl

lemma comp_assoc (F : Emb G H) (F' : Emb H K) (F'' : Emb K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := rfl

/-- An embedding maps each edge's incidences bijectively onto those of its image edge. -/
lemma bijOn_incMap [Nonempty I₁] [Nonempty E₁] (F : Emb G H) {e : E₀} (he : e ∈ E(G)) :
    BijOn F.incMap (edgeFiber G e) (edgeFiber H (F.edgeMap e)) :=
  ⟨F.mapsTo_edgeFiber, F.incMap_injOn.mono edgeFiber_subset_incs, F.surjOn_incMap he⟩

@[simp]
lemma mem_incVerts_map_iff [Nonempty V₁] [Nonempty E₁] (F : Emb G H)
    {e : E₀} {x : V₀} (he : e ∈ E(G)) (hx : x ∈ V(G)) :
    F.vertMap x ∈ incVerts H (F.edgeMap e) ↔ x ∈ incVerts G e := by
  simpa only [← F.image_incVerts he] using F.vertMap_injOn.mem_image_iff incVerts_subset_verts hx

lemma mem_incEdges_map_iff [Nonempty V₁] [Nonempty E₁] (F : Emb G H)
    {e : E₀} {x : V₀} (he : e ∈ E(G)) (hx : x ∈ V(G)) :
    F.edgeMap e ∈ incEdges H (F.vertMap x) ↔ e ∈ incEdges G x := by
  simp only [mem_incEdges, F.mem_incVerts_map_iff he hx]

end Emb

namespace Iso

private lemma ext' {F F' : Iso G H} (hV : ∀ x, F.vertMap' x = F'.vertMap' x)
    (hI : ∀ i, F.incMap' i = F'.incMap' i) (hE : ∀ e, F.edgeMap' e = F'.edgeMap' e) : F = F' :=
  (mk.injEq ..).mpr ⟨Emb.ext' hV hI hE,
    LeftInverse.eq_rightInverse F.vertMap'_leftInverse
      (fun y ↦ (hV _).trans (F'.vertMap'_rightInverse y)),
    LeftInverse.eq_rightInverse F.incMap'_leftInverse
      (fun i ↦ (hI _).trans (F'.incMap'_rightInverse i)),
    LeftInverse.eq_rightInverse F.edgeMap'_leftInverse
      (fun e ↦ (hE _).trans (F'.edgeMap'_rightInverse e))⟩

lemma toIncHom_injective : Injective (fun F : Iso G H ↦ F.toIncHom) := fun _ _ h ↦
  ext' (congrFun (congrArg IncHom.vertMap' h)) (congrFun (congrArg IncHom.incMap' h))
    (congrFun (congrArg IncHom.edgeMap' h))

lemma toIncEmb_injective : Injective (fun F : Iso G H ↦ F.toIncEmb) := fun _ _ h ↦
  toIncHom_injective (congrArg IncEmb.toIncHom h)

lemma toEmb_injective : Injective (toEmb : Iso G H → Emb G H) := fun _ _ h ↦
  toIncHom_injective (congrArg (fun F : Emb G H ↦ F.toIncHom) h)

lemma toHom_injective : Injective (fun F : Iso G H ↦ F.toHom) := fun _ _ h ↦
  toIncHom_injective (congrArg Hom.toIncHom h)

@[ext]
lemma ext [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] {F F' : Iso G H}
    (hV : ∀ x ∈ V(G), F.vertMap x = F'.vertMap x) (hI : ∀ i ∈ I(G), F.incMap i = F'.incMap i)
    (hE : ∀ e ∈ E(G), F.edgeMap e = F'.edgeMap e) : F = F' :=
  toIncHom_injective (IncHom.ext hV hI hE)

/-- Construct an isomorphism from equivalences of the three ground sets preserving incidence
and directedness. -/
def ofEquivs (v : V(G) ≃ V(H)) (i : I(G) ≃ I(H)) (e : E(G) ≃ E(H))
    (hv : ∀ j, attach' (i j) = v (attach' j))
    (he : ∀ j, HypergraphLike.edgeMap' (i j) = e (HypergraphLike.edgeMap' j))
    (hs : ∀ j, IsSource H (i j).val ↔ IsSource G j.val)
    (ht : ∀ j, IsTarget H (i j).val ↔ IsTarget G j.val) : Iso G H where
  toEmb := Emb.ofIncEmb (IncEmb.ofEmbeddings v.toEmbedding i.toEmbedding e.toEmbedding hv he
    (fun j ↦ (hs j).mpr) (fun j ↦ (ht j).mpr))
    (fun _ j hj ↦ ⟨i.symm j, e.injective ((he (i.symm j)).symm.trans
      ((congrArg (HypergraphLike.edgeMap' (G := H)) (i.apply_symm_apply j)).trans hj)),
      i.apply_symm_apply j⟩)
  isSource_of_map' := (hs _).mp
  isTarget_of_map' := (ht _).mp
  invVertMap' := v.symm
  invIncMap' := i.symm
  invEdgeMap' := e.symm
  vertMap'_leftInverse := v.symm_apply_apply
  vertMap'_rightInverse := v.apply_symm_apply
  incMap'_leftInverse := i.symm_apply_apply
  incMap'_rightInverse := i.apply_symm_apply
  edgeMap'_leftInverse := e.symm_apply_apply
  edgeMap'_rightInverse := e.apply_symm_apply

/-- A homomorphism bijective on the ground sets whose inverse respects incidence directions
gives an isomorphism.
The forward maps are retained; choice supplies only their inverses. -/
noncomputable def ofBijOn [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] (F : IncHom G H)
    (hv : BijOn F.vertMap V(G) V(H)) (hi : BijOn F.incMap I(G) I(H))
    (he : BijOn F.edgeMap E(G) E(H)) (hs : ∀ i ∈ I(G), IsSource H (F.incMap i) → IsSource G i)
    (ht : ∀ i ∈ I(G), IsTarget H (F.incMap i) → IsTarget G i) : Iso G H := by
  have hv' : Bijective F.vertMap' := by
    simpa [Bijective, Injective, Surjective, Subtype.ext_iff] using hv.bijective
  have hi' : Bijective F.incMap' := by
    simpa [Bijective, Injective, Surjective, Subtype.ext_iff] using hi.bijective
  have he' : Bijective F.edgeMap' := by
    simpa [Bijective, Injective, Surjective, Subtype.ext_iff] using he.bijective
  exact ofEquivs (Equiv.ofBijective F.vertMap' hv') (Equiv.ofBijective F.incMap' hi')
    (Equiv.ofBijective F.edgeMap' he') F.map_attach' F.map_edgeMap'
    (fun i ↦ ⟨fun h ↦ hs i.val i.property (by simpa using h), F.map_isSource'⟩)
    (fun i ↦ ⟨fun h ↦ ht i.val i.property (by simpa using h), F.map_isTarget'⟩)

@[simp]
lemma ofBijOn_toIncHom [Nonempty V₁] [Nonempty I₁] [Nonempty E₁] (F : IncHom G H)
    (hv : BijOn F.vertMap V(G) V(H)) (hi : BijOn F.incMap I(G) I(H))
    (he : BijOn F.edgeMap E(G) E(H)) (hs : ∀ i ∈ I(G), IsSource H (F.incMap i) → IsSource G i)
    (ht : ∀ i ∈ I(G), IsTarget H (F.incMap i) → IsTarget G i) :
    (ofBijOn F hv hi he hs ht).toIncHom = F := rfl

@[simp]
lemma isSource_map_iff [Nonempty I₁] (F : Iso G H) {i : I₀} (hi : i ∈ I(G)) :
    IsSource H (F.incMap i) ↔ IsSource G i :=
  ⟨fun h ↦ F.isSource_of_map' (i := ⟨i, hi⟩) (by simpa using h), F.map_isSource⟩

@[simp]
lemma isTarget_map_iff [Nonempty I₁] (F : Iso G H) {i : I₀} (hi : i ∈ I(G)) :
    IsTarget H (F.incMap i) ↔ IsTarget G i :=
  ⟨fun h ↦ F.isTarget_of_map' (i := ⟨i, hi⟩) (by simpa using h), F.map_isTarget⟩

/-- The identity isomorphism. -/
@[simps toEmb]
def id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : Iso G G where
  toEmb := Emb.id G
  isSource_of_map' := _root_.id
  isTarget_of_map' := _root_.id
  invVertMap' := _root_.id
  invIncMap' := _root_.id
  invEdgeMap' := _root_.id
  vertMap'_leftInverse _ := rfl
  vertMap'_rightInverse _ := rfl
  incMap'_leftInverse _ := rfl
  incMap'_rightInverse _ := rfl
  edgeMap'_leftInverse _ := rfl
  edgeMap'_rightInverse _ := rfl

/-- Reverse an isomorphism using its specified inverse functions. -/
def symm (F : Iso G H) : Iso H G where
  vertMap' := F.invVertMap'
  incMap' := F.invIncMap'
  edgeMap' := F.invEdgeMap'
  map_attach' i := by
    apply F.vertMap'_injective
    rw [F.vertMap'_rightInverse, ← F.map_attach', F.incMap'_rightInverse]
  map_edgeMap' i := by
    apply F.edgeMap'_injective
    rw [F.edgeMap'_rightInverse, ← F.map_edgeMap', F.incMap'_rightInverse]
  map_isSource' := fun {i} h ↦ F.isSource_of_map'
    (by simpa only [F.incMap'_rightInverse] using h)
  map_isTarget' := fun {i} h ↦ F.isTarget_of_map'
    (by simpa only [F.incMap'_rightInverse] using h)
  isSource_of_map' := fun {i} h ↦ by
    simpa only [F.incMap'_rightInverse] using F.map_isSource' h
  isTarget_of_map' := fun {i} h ↦ by
    simpa only [F.incMap'_rightInverse] using F.map_isTarget' h
  vertMap'_injective := LeftInverse.injective F.vertMap'_rightInverse
  incMap'_injective := LeftInverse.injective F.incMap'_rightInverse
  edgeMap'_injective := LeftInverse.injective F.edgeMap'_rightInverse
  isLocallySurjective e j hj := ⟨F.incMap' j, (F.map_edgeMap' j).trans
    ((congrArg F.edgeMap' hj).trans (F.edgeMap'_rightInverse e)), F.incMap'_leftInverse j⟩
  invVertMap' := F.vertMap'
  invIncMap' := F.incMap'
  invEdgeMap' := F.edgeMap'
  vertMap'_leftInverse := F.vertMap'_rightInverse
  vertMap'_rightInverse := F.vertMap'_leftInverse
  incMap'_leftInverse := F.incMap'_rightInverse
  incMap'_rightInverse := F.incMap'_leftInverse
  edgeMap'_leftInverse := F.edgeMap'_rightInverse
  edgeMap'_rightInverse := F.edgeMap'_leftInverse

/-- Compose forward maps in diagrammatic order and inverse maps in reverse order. -/
@[simps toEmb]
def comp (F : Iso G H) (F' : Iso H K) : Iso G K where
  toEmb := F.toEmb.comp F'.toEmb
  isSource_of_map' h := F.isSource_of_map' (F'.isSource_of_map' h)
  isTarget_of_map' h := F.isTarget_of_map' (F'.isTarget_of_map' h)
  invVertMap' := F.invVertMap' ∘ F'.invVertMap'
  invIncMap' := F.invIncMap' ∘ F'.invIncMap'
  invEdgeMap' := F.invEdgeMap' ∘ F'.invEdgeMap'
  vertMap'_leftInverse := LeftInverse.comp F'.vertMap'_leftInverse F.vertMap'_leftInverse
  vertMap'_rightInverse := RightInverse.comp F'.vertMap'_rightInverse F.vertMap'_rightInverse
  incMap'_leftInverse := LeftInverse.comp F'.incMap'_leftInverse F.incMap'_leftInverse
  incMap'_rightInverse := RightInverse.comp F'.incMap'_rightInverse F.incMap'_rightInverse
  edgeMap'_leftInverse := LeftInverse.comp F'.edgeMap'_leftInverse F.edgeMap'_leftInverse
  edgeMap'_rightInverse := RightInverse.comp F'.edgeMap'_rightInverse F.edgeMap'_rightInverse

@[simp]
lemma id_comp (F : Iso G H) : (id G).comp F = F := rfl

@[simp]
lemma comp_id (F : Iso G H) : F.comp (id H) = F := rfl

lemma comp_assoc (F : Iso G H) (F' : Iso H K) (F'' : Iso K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := rfl

@[simp]
lemma symm_symm (F : Iso G H) : F.symm.symm = F := rfl

@[simp]
lemma symm_id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : (id G).symm = id G := rfl

@[simp]
lemma symm_comp (F : Iso G H) : F.symm.comp F = id H :=
  ext' F.vertMap'_rightInverse F.incMap'_rightInverse F.edgeMap'_rightInverse

@[simp]
lemma comp_symm (F : Iso G H) : F.comp F.symm = id G :=
  ext' F.vertMap'_leftInverse F.incMap'_leftInverse F.edgeMap'_leftInverse

@[simp]
lemma comp_symm_eq (F : Iso G H) (F' : Iso H K) : (F.comp F').symm = F'.symm.comp F.symm := rfl

@[simp]
lemma toHom_id (G : Gr₀) [HypergraphLike V₀ I₀ E₀ G] : (id G).toHom = Hom.id G := rfl

@[simp]
lemma toHom_comp (F : Iso G H) (F' : Iso H K) : (F.comp F').toHom = F.toHom.comp F'.toHom := rfl

@[simp]
lemma symm_vertMap_vertMap [Nonempty V₀] [Nonempty V₁] (F : Iso G H)
    {x : V₀} (hx : x ∈ V(G)) : F.symm.vertMap (F.vertMap x) = x := by
  simpa using (show (F.symm.vertMap' (F.vertMap' ⟨x, hx⟩)).val = x from
    congrArg Subtype.val (F.vertMap'_leftInverse ⟨x, hx⟩))

@[simp]
lemma vertMap_symm_vertMap [Nonempty V₀] [Nonempty V₁] (F : Iso G H)
    {x : V₁} (hx : x ∈ V(H)) : F.vertMap (F.symm.vertMap x) = x := by
  simpa using F.symm.symm_vertMap_vertMap hx

lemma vertMap_bijOn [Nonempty V₁] (F : Iso G H) : BijOn F.vertMap V(G) V(H) := by
  refine ⟨fun _ hx ↦ F.vertMap_mem hx, F.vertMap_injOn,
    fun y hy ↦ ⟨(F.invVertMap' ⟨y, hy⟩).val, (F.invVertMap' ⟨y, hy⟩).property, ?_⟩⟩
  simpa using congrArg Subtype.val (F.vertMap'_rightInverse ⟨y, hy⟩)

/-- The derived equivalence of vertices, using the specified inverse. -/
def vertEquiv (F : Iso G H) : V(G) ≃ V(H) where
  toFun := F.vertMap'
  invFun := F.invVertMap'
  left_inv := F.vertMap'_leftInverse
  right_inv := F.vertMap'_rightInverse

@[simp]
lemma symm_incMap_incMap [Nonempty I₀] [Nonempty I₁] (F : Iso G H)
    {i : I₀} (hi : i ∈ I(G)) : F.symm.incMap (F.incMap i) = i := by
  simpa using (show (F.symm.incMap' (F.incMap' ⟨i, hi⟩)).val = i from
    congrArg Subtype.val (F.incMap'_leftInverse ⟨i, hi⟩))

@[simp]
lemma incMap_symm_incMap [Nonempty I₀] [Nonempty I₁] (F : Iso G H)
    {i : I₁} (hi : i ∈ I(H)) : F.incMap (F.symm.incMap i) = i := by
  simpa using F.symm.symm_incMap_incMap hi

lemma incMap_bijOn [Nonempty I₁] (F : Iso G H) : BijOn F.incMap I(G) I(H) := by
  refine ⟨fun _ hx ↦ F.incMap_mem hx, F.incMap_injOn,
    fun y hy ↦ ⟨(F.invIncMap' ⟨y, hy⟩).val, (F.invIncMap' ⟨y, hy⟩).property, ?_⟩⟩
  simpa using congrArg Subtype.val (F.incMap'_rightInverse ⟨y, hy⟩)

/-- The derived equivalence of incidences, using the specified inverse. -/
def incEquiv (F : Iso G H) : I(G) ≃ I(H) where
  toFun := F.incMap'
  invFun := F.invIncMap'
  left_inv := F.incMap'_leftInverse
  right_inv := F.incMap'_rightInverse

@[simp]
lemma symm_edgeMap_edgeMap [Nonempty E₀] [Nonempty E₁] (F : Iso G H)
    {e : E₀} (he : e ∈ E(G)) : F.symm.edgeMap (F.edgeMap e) = e := by
  simpa using (show (F.symm.edgeMap' (F.edgeMap' ⟨e, he⟩)).val = e from
    congrArg Subtype.val (F.edgeMap'_leftInverse ⟨e, he⟩))

@[simp]
lemma edgeMap_symm_edgeMap [Nonempty E₀] [Nonempty E₁] (F : Iso G H)
    {e : E₁} (he : e ∈ E(H)) : F.edgeMap (F.symm.edgeMap e) = e := by
  simpa using F.symm.symm_edgeMap_edgeMap he

lemma edgeMap_bijOn [Nonempty E₁] (F : Iso G H) : BijOn F.edgeMap E(G) E(H) := by
  refine ⟨fun _ hx ↦ F.edgeMap_mem hx, F.edgeMap_injOn,
    fun y hy ↦ ⟨(F.invEdgeMap' ⟨y, hy⟩).val, (F.invEdgeMap' ⟨y, hy⟩).property, ?_⟩⟩
  simpa using congrArg Subtype.val (F.edgeMap'_rightInverse ⟨y, hy⟩)

/-- The derived equivalence of edges, using the specified inverse. -/
def edgeEquiv (F : Iso G H) : E(G) ≃ E(H) where
  toFun := F.edgeMap'
  invFun := F.invEdgeMap'
  left_inv := F.edgeMap'_leftInverse
  right_inv := F.edgeMap'_rightInverse

@[simp]
lemma isLink_map_iff [Nonempty V₁] [Nonempty E₁] (F : Iso G H) {e : E₀} {x y : V₀}
    (he : e ∈ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    IsLink H (F.edgeMap e) (F.vertMap x) (F.vertMap y) ↔ IsLink G e x y := by
  let : Nonempty V₀ := ⟨x⟩
  let : Nonempty E₀ := ⟨e⟩
  refine ⟨fun h ↦ ?_, F.map_isLink⟩
  simpa only [F.symm_edgeMap_edgeMap he, F.symm_vertMap_vertMap hx, F.symm_vertMap_vertMap hy]
    using F.symm.map_isLink h

@[simp]
lemma adj_map_iff [Nonempty V₁] (F : Iso G H) {x y : V₀} (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    Adj H (F.vertMap x) (F.vertMap y) ↔ Adj G x y := by
  let : Nonempty V₀ := ⟨x⟩
  refine ⟨fun h ↦ ?_, F.map_adj⟩
  simpa only [F.symm_vertMap_vertMap hx, F.symm_vertMap_vertMap hy] using F.symm.map_adj h

end Iso

end HypergraphLike
