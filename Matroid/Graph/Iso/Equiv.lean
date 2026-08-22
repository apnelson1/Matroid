/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.ForMathlib.Iso.Equiv
public import Matroid.Graph.Iso.Hom

/-!
# Graph adapter for the generic isomorphism-equivalence framework

The public graph-facing family syntax remains unbundled. Bundling is only the internal index used to
instantiate the generic core.
-/

@[expose] public section

open Set Function

namespace Graph

universe uV₁ uE₁ uF₁ uV₂ uE₂ uF₂ uV₃ uE₃ uF₃ uV₄ uE₄ uF₄

/-- Internal bundled graph object used only to feed the generic core. -/
structure IsoObj where
  V : Type uV₁
  E : Type uE₁
  graph : Graph V E

set_option linter.checkUnivs false in
abbrev Family := {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uF₁

set_option linter.checkUnivs false in
abbrev TypeFamily := {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uF₁

/-- Reindex an unbundled graph family by the bundled generic-core index.

Implementation detail of the generic-core adapter; ordinary users should reach the
domain-facing wrappers instead of naming this. -/
protected abbrev Family.bundle (F : Family.{uV₁, uE₁, uF₁}) : IsoObj.{uV₁, uE₁} → Sort uF₁ :=
  fun X ↦ @F X.V X.E X.graph

instance instIsoRelIsoObj : _root_.IsoRel IsoObj.{uV₁, uE₁} IsoObj.{uV₂, uE₂} where
  Iso X Y := Graph.Iso X.graph Y.graph

/-- Graph-facing alias of the generic weak equivalence class. -/
abbrev IsoEquiv (F : Family.{uV₁, uE₁, uF₁}) (F' : Family.{uV₂, uE₂, uF₂}) :=
  _root_.IsoEquiv F.bundle F'.bundle

/-- Graph-facing transport along an isomorphism.

This is the generic `_root_.IsoEquiv.map` with the bundling index supplied. Stating graph results
through it keeps them in unbundled vocabulary, and it is the only place `⟨V, E, G⟩` has to be
written: the generic `map` cannot infer that index, because unifying `IsoRel.Iso X Y` against
`Iso G H` would have to solve `?X.graph ≡ G`. -/
abbrev IsoEquiv.map {F : Family.{uV₁, uE₁, uF₁}} {F' : Family.{uV₂, uE₂, uF₂}} [IsoEquiv F F']
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : F G ≃ F' H :=
  _root_.IsoEquiv.map (F := F.bundle) (F' := F'.bundle) (X := ⟨V, E, G⟩) (Y := ⟨V', E', H⟩) i

/-- Graph-facing alias for isomorphism-preserving maps between bundled graph objects. -/
abbrev IsoMap (f : IsoObj.{uV₁, uE₁} → IsoObj.{uV₃, uE₃})
    (f' : IsoObj.{uV₂, uE₂} → IsoObj.{uV₄, uE₄}) := _root_.IsoMap f f'

namespace Family

/-- Reindex an unbundled graph family along an object construction while retaining an explicit
reindexing node at the graph adapter boundary. -/
def reindex (f : IsoObj.{uV₁, uE₁} → IsoObj.{uV₃, uE₃}) (F : Family.{uV₃, uE₃, uF₃}) :
    Family.{uV₁, uE₁, uF₃} := fun {V} {E} G ↦ @F (f ⟨V, E, G⟩).V (f ⟨V, E, G⟩).E (f ⟨V, E, G⟩).graph

end Family

/-- Graph-facing reindex closure. Core users generally reach this through named graph operations,
not by writing `Family.reindex` directly. -/
instance instIsoEquivReindex (f : IsoObj.{uV₁, uE₁} → IsoObj.{uV₃, uE₃})
    (f' : IsoObj.{uV₂, uE₂} → IsoObj.{uV₄, uE₄})
    (F : Family.{uV₃, uE₃, uF₃}) (F' : Family.{uV₄, uE₄, uF₄})
    [m : _root_.IsoMap f f'] [e : IsoEquiv F F'] :
    IsoEquiv (Family.reindex f F) (Family.reindex f' F') where
  map i := IsoEquiv.map (F := F) (F' := F') (m.map i)

/-! ## Primitive graph families -/

/-- Intrinsic active-vertex family. -/
abbrev VertexFamily : TypeFamily.{uV₁, uE₁, uV₁} := fun {V} {E} (G : Graph V E) ↦ V(G)

/-- Intrinsic active-edge family. -/
abbrev EdgeFamily : TypeFamily.{uV₁, uE₁, uE₁} := fun {V} {E} (G : Graph V E) ↦ E(G)

instance instIsoEquivVertices : IsoEquiv (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G))
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G)) where
  map := Graph.Iso.vertexEquiv

instance instIsoEquivEdges : IsoEquiv (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ E(G))
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ E(G)) where
  map := Graph.Iso.edgeEquiv

section Computation

variable {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
  {G : Graph V E} {H : Graph V' E'}

@[simp] theorem IsoEquiv.map_vertices (i : Iso G H) :
    IsoEquiv.map (F := fun {V E} (G : Graph V E) ↦ V(G))
      (F' := fun {V E} (G : Graph V E) ↦ V(G)) i = i.vertexEquiv := rfl

@[simp] theorem IsoEquiv.map_edges (i : Iso G H) :
    IsoEquiv.map (F := fun {V E} (G : Graph V E) ↦ E(G))
      (F' := fun {V E} (G : Graph V E) ↦ E(G)) i = i.edgeEquiv := rfl

end Computation

/-! ## Ambient supported subsets

These reproduce the useful part of the old graph-specific supported-subset API while all ordinary
`Set`, `→`, `×`, `⊕`, and `Option` families are now supplied by the generic core. -/

/-- Ambient subsets of `S` are equivalent to intrinsic subsets of the subtype `S`. -/
def setSubtypeEquiv {α : Type*} (S : Set α) : {X : Set α // X ⊆ S} ≃ Set S where
  toFun X := Subtype.val ⁻¹' X.1
  invFun t := ⟨Subtype.val '' t, Subtype.coe_image_subset S t⟩
  left_inv := by
    rintro ⟨X, hX⟩
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyX, rfl⟩
      exact hyX
    · exact fun hx ↦ ⟨⟨x, hX hx⟩, hx, rfl⟩
  right_inv := by
    intro t
    ext ⟨x, hx⟩
    simp

instance instIsoEquivVertexSubsets : IsoEquiv
    (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ {X : Set V // X ⊆ V(G)})
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ {X : Set V // X ⊆ V(G)}) :=
  _root_.IsoEquiv.ofFiberEquiv (F := fun X : IsoObj.{uV₁, uE₁} ↦ Set V(X.graph))
    (F' := fun X : IsoObj.{uV₂, uE₂} ↦ Set V(X.graph))
    (fun X ↦ setSubtypeEquiv V(X.graph)) (fun X ↦ setSubtypeEquiv V(X.graph))

instance instIsoEquivEdgeSubsets : IsoEquiv
    (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ {X : Set E // X ⊆ E(G)})
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ {X : Set E // X ⊆ E(G)}) :=
  _root_.IsoEquiv.ofFiberEquiv (F := fun X : IsoObj.{uV₁, uE₁} ↦ Set E(X.graph))
    (F' := fun X : IsoObj.{uV₂, uE₂} ↦ Set E(X.graph))
    (fun X ↦ setSubtypeEquiv E(X.graph)) (fun X ↦ setSubtypeEquiv E(X.graph))

end Graph
