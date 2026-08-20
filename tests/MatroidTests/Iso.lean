/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.Transfer

/-!
# Regression and ergonomics tests for graph isomorphism transport

This file tests the post-restructuring `Graph.Iso` API.

The intended architecture is:

* `Iso` remains the `PEquiv`-based graph isomorphism structure.
* `Iso.vertexEquiv` / `Iso.edgeEquiv` are the active-carrier interface and their coherence API
  lives with `Iso`.
* `IsoTransport` is the only structural transport typeclass.
* `IsoAction F` is only the diagonal compatibility view `IsoTransport F F`; there is no parallel
  structural instance hierarchy.
* `InvariantTransport P P'` is the only proposition-valued invariance class.  `Invariant P` is
  recovered in the same-universe case.
* Logical closure is inferred through `InvariantTransport`.
* Ambient bounded quantifiers are handled generically by transporting the subtype cut out by the
  guard.  In particular, the same mechanism should handle
    `x ∈ V(G)`, `e ∈ E(G)`, `X ⊆ V(G)`, and `F ⊆ E(G)`.
* The public API is expression-first: ordinary lambdas and universe-polymorphic declarations are
  passed directly; callers should not need bundled families or explicit universe plumbing.

Several tests below are deliberately ergonomic rather than merely extensional.  For example,
`IsoTransport.map i` and `InvariantTransport.iff_of_iso i` are used with no explicit family or
property arguments whenever the expected type already determines them.
-/

@[expose] public section

open Set

namespace Graph
namespace GFCheck

universe uV uE uV' uE' uV'' uE'' uA uA'

/-! ## Atomic properties: register exactly one heterogeneous invariant theorem -/

/-- Vertex-side test atom. -/
def IsBig {V : Type uV} {E : Type uE} (G : Graph V E) : Prop :=
  3 ≤ V(G).encard

theorem isBig_iff_of_iso
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    IsBig G ↔ IsBig H := by
  simp only [IsBig, IsIsoTo.vertexSet_encard_eq ⟨i⟩]

instance instIsBigInvariantTransport : InvariantTransport ⧉ IsBig :=
  InvariantTransport.of_iff isBig_iff_of_iso

/-- Edge-side test atom. -/
def IsDense {V : Type uV} {E : Type uE} (G : Graph V E) : Prop :=
  3 ≤ E(G).encard

theorem isDense_iff_of_iso
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    IsDense G ↔ IsDense H := by
  simp only [IsDense, IsIsoTo.edgeSet_encard_eq ⟨i⟩]

instance instIsDenseInvariantTransport : InvariantTransport ⧉ IsDense :=
  InvariantTransport.of_iff isDense_iff_of_iso

/-- Parameterized atom, modelling a fixed pattern such as `K.IsTopologicalMinor G`. -/
def HasOrder (n : ℕ∞) {V : Type uV} {E : Type uE} (G : Graph V E) : Prop :=
  V(G).encard = n

theorem hasOrder_iff_of_iso (n : ℕ∞)
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    HasOrder n G ↔ HasOrder n H := by
  simp only [HasOrder, IsIsoTo.vertexSet_encard_eq ⟨i⟩]

instance instHasOrderInvariantTransport (n : ℕ∞) :
    InvariantTransport ⧉ HasOrder n :=
  InvariantTransport.of_iff (hasOrder_iff_of_iso n)

/-! Atomic registration should immediately supply both heterogeneous and same-universe use. -/

#synth InvariantTransport ⧉ IsBig
#synth InvariantTransport ⧉ IsDense
#synth InvariantTransport ⧉ HasOrder 5

#synth Invariant IsBig
#synth Invariant IsDense
#synth Invariant (HasOrder 5)

/-! Use ergonomics: the expected proposition should determine `P` and `P'`. -/

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    IsBig G ↔ IsBig H :=
  InvariantTransport.iff_of_iso i

example
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    IsDense G ↔ IsDense H :=
  Invariant.iff_of_iso i

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (h : G.IsIsoTo H) :
    HasOrder 7 G ↔ HasOrder 7 H :=
  InvariantTransport.iff_of_isIsoTo h

/-! ## One structural hierarchy: `IsoAction` is only the diagonal view -/

/- The key regression: diagonal synthesis should resolve to the *transport* instance itself,
not to a second `instVertices` hierarchy. -/
/-- info: instTransportVertices -/
#guard_msgs (whitespace := lax) in
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G))

/-- info: instTransportEdges -/
#guard_msgs (whitespace := lax) in
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G))

#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set V(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) × E(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) ⊕ E(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Option V(G))
#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G) → V(G) → Prop)

/-- On a local diagonal transport, the compatibility `IsoAction.map` is definitionally the source
endpoint action. -/
example
    {F : {V : Type uV} → {E : Type uE} → Graph V E → Sort uA}
    [t : IsoTransport F F]
    {V V' : Type uV} {E E' : Type uE}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) (x : F G) :
    IsoAction.map i x =
      IsoTransport.sourceMap (F := F) (F' := F) i x :=
  rfl

/-! ## Heterogeneous structural synthesis -/

#synth IsoTransport
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G))
  (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ V(G))

#synth IsoTransport
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ E(G))
  (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ E(G))

#synth IsoTransport ⧉ fun G ↦ Set V(G)
#synth IsoTransport ⧉ fun G ↦ Set E(G)
#synth IsoTransport ⧉ fun G ↦ V(G) × E(G)
#synth IsoTransport ⧉ fun G ↦ V(G) ⊕ E(G)
#synth IsoTransport ⧉ fun G ↦ Option V(G)
#synth IsoTransport ⧉ fun G ↦ E(G) → Set V(G)

/-! Use ergonomics: expected types should determine both transported families. -/

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    V(G) ≃ V(H) :=
  IsoTransport.map (F := fun G ↦ V(G)) i

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    Set E(G) ≃ Set E(H) :=
  IsoTransport.map (F := fun G ↦ Set E(G)) i

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    (E(G) → Set V(G)) ≃ (E(H) → Set V(H)) :=
  IsoTransport.map (F := fun G ↦ E(G) → Set V(G)) i

/-! The incidence-graph universe shape must work without assuming `uV = uE`. -/
example
    {V : Type uV} {E : Type uE} {I : Type uE'}
    {G : Graph V E} {H : Graph (V ⊕ E) I} (i : Iso G H) :
    V(G) ≃ V(H) :=
  IsoTransport.map (F := fun G ↦ V(G)) i

/-! The two coherence directions are part of the actual structural contract. -/
example
    {V₀ V₁ : Type uV} {E₀ E₁ : Type uE}
    {V₂ : Type uV'} {E₂ : Type uE'}
    {G₀ : Graph V₀ E₀} {G₁ : Graph V₁ E₁} {H : Graph V₂ E₂}
    (i : Iso G₀ G₁) (j : Iso G₁ H) (x : V(G₀)) :
    IsoTransport.map (F := fun G ↦ V(G)) (i.comp j) x =
      IsoTransport.map (F := fun G ↦ V(G)) j (IsoTransport.sourceMap
        (F := fun G ↦ V(G)) i x) :=
  IsoTransport.map_pre (F := fun G ↦ V(G)) i j x

example
    {V₀ : Type uV} {E₀ : Type uE}
    {V₁ V₂ : Type uV'} {E₁ E₂ : Type uE'}
    {G : Graph V₀ E₀} {H₁ : Graph V₁ E₁} {H₂ : Graph V₂ E₂}
    (i : Iso G H₁) (j : Iso H₁ H₂) (x : V(G)) :
    IsoTransport.map (F := fun G ↦ V(G)) (i.comp j) x =
      IsoTransport.targetMap (F := fun G ↦ V(G)) j
        (IsoTransport.map (F := fun G ↦ V(G)) i x) :=
  IsoTransport.map_post (F := fun G ↦ V(G)) i j x

/-! ## `Iso` active-equivalence API belongs with `Iso` and should be pleasant to use -/

example
    {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'}
    {V'' : Type uV''} {E'' : Type uE''}
    {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}
    (i : Iso G H) (j : Iso H K) :
    (i.comp j).vertexEquiv = i.vertexEquiv.trans j.vertexEquiv :=
  i.vertexEquiv_comp_eq j

example
    {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE'}
    {V'' : Type uV''} {E'' : Type uE''}
    {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}
    (i : Iso G H) (j : Iso H K) :
    (i.comp j).edgeEquiv = i.edgeEquiv.trans j.edgeEquiv :=
  i.edgeEquiv_comp_eq j

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H)
    (e : E(G)) (x y : V(G)) :
    G.IsLink e.1 x.1 y.1 ↔
      H.IsLink (i.edgeEquiv e).1 (i.vertexEquiv x).1 (i.vertexEquiv y).1 :=
  i.isLink_edgeEquiv_vertexEquiv e x y

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H)
    (x y : V(G)) :
    G.Adj x.1 y.1 ↔ H.Adj (i.vertexEquiv x).1 (i.vertexEquiv y).1 :=
  i.adj_vertexEquiv x y

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    i.symm.vertexEquiv = i.vertexEquiv.symm := by
  simp

/-! ## Logical algebra lives only in `InvariantTransport` -/

#synth InvariantTransport ⧉ fun G ↦ ¬ IsBig G
#synth InvariantTransport ⧉ fun G ↦ IsBig G ∧ IsDense G
#synth InvariantTransport ⧉ fun G ↦ IsBig G ∨ IsDense G
#synth InvariantTransport ⧉ fun G ↦ IsBig G → IsDense G
#synth InvariantTransport ⧉ fun G ↦ IsBig G ↔ IsDense G
#synth InvariantTransport ⧉ fun G ↦
  IsBig G ↔ ¬ (IsDense G ∨ ¬ IsBig G)

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  IsBig G ∧ ¬ IsDense G)

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  IsBig G → (IsDense G ∨ HasOrder 5 G))

/-! Again test downstream use without explicit property parameters. -/
example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    (IsBig G ∧ ¬ IsDense G) ↔ (IsBig H ∧ ¬ IsDense H) :=
  InvariantTransport.iff_of_iso i (P := fun G ↦ IsBig G ∧ ¬ IsDense G)
    (P' := fun G ↦ IsBig G ∧ ¬ IsDense G)

/-! ## A tiny generic fixture for quantifier inference

This is deliberately test-only.  The body is `True`, so there is no mathematical content hidden
in the fixture: it isolates whether the quantifier machinery can infer the correct transported
binder.
-/

instance instTrueMarkedTransport
    (A : {V : Type uV} → {E : Type uE} → Graph V E → Type uA)
    (A' : {V : Type uV'} → {E : Type uE'} → Graph V E → Type uA')
    [IsoTransport A A'] :
    EquivariantTransport
      (fun G ↦ A G → Prop)
      (fun G ↦ A' G → Prop)
      (fun _ _ ↦ True)
      (fun _ _ ↦ True) where
  map_eq _ := by
    funext
    rfl

/-! ## Ordinary quantifiers over intrinsic transported types -/

#synth InvariantTransport ⧉ fun G ↦ ∀ _ : V(G), True
#synth InvariantTransport ⧉ fun G ↦ ∃ _ : V(G), True
#synth InvariantTransport ⧉ fun G ↦ ∀ _ : E(G), True
#synth InvariantTransport ⧉ fun G ↦ ∃ _ : Set E(G), True

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∀ _ : V(G), True)

/-! ## Generic bounded quantifiers: ambient vertices and edges

These must work even though there is no transport on the entire ambient `V` or `E`: only the
guarded subtype is transportable.
-/

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∀ x : V, x ∈ V(G) → True

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∃ x : V, x ∈ V(G) ∧ True

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∀ e : E, e ∈ E(G) → True

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∃ e : E, e ∈ E(G) ∧ True

/-! Repository syntax should be accepted directly. -/
#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∀ x ∈ V(G), True

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∃ e ∈ E(G), True

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∀ x ∈ V(G), True)

/-! ## Supported ambient subsets

The structural transport should synthesize directly for ambient subsets guarded by the active
vertex/edge set.  These are the Phase-4 cases: no bespoke `VertexSubset` or `EdgeSubset` class is
needed.
-/

#synth IsoTransport ⧉ fun {V E} (G : Graph V E) ↦
  {X : Set V // X ⊆ V(G)}

#synth IsoTransport ⧉ fun {V E} (G : Graph V E) ↦
  {F : Set E // F ⊆ E(G)}

#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  {X : Set V // X ⊆ V(G)})

#synth IsoAction (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  {F : Set E // F ⊆ E(G)})

/-! The same generic bounded-quantifier adapter must now work for subset guards. -/

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∀ X : Set V, X ⊆ V(G) → True

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∃ X : Set V, X ⊆ V(G) ∧ True

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∀ F : Set E, F ⊆ E(G) → True

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∃ F : Set E, F ⊆ E(G) ∧ True

#synth Invariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
  ∀ F : Set E, F ⊆ E(G) → True)

/-! ## Nontrivial bounded-body ergonomics

The preceding `True` tests isolate binder inference.  These fixtures check the realistic pattern:
an ambient predicate is registered for the corresponding guarded subtype, and the outer bounded
quantifier should then need no custom invariant theorem.
-/

/-- Ambient-label predicate whose mathematical content is the graph property `IsBig`. -/
def bigAtLabel {V : Type uV} {E : Type uE}
    (G : Graph V E) (_ : V) : Prop :=
  IsBig G

instance instBigAtLabelSupportedTransport :
    EquivariantTransport
      (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ V(G) → Prop)
      (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦ V(G) → Prop)
      (fun G x ↦ bigAtLabel G x.1)
      (fun G x ↦ bigAtLabel G x.1) where
  map_eq i := by
    funext y
    change IsBig _ = IsBig _
    exact propext (InvariantTransport.iff_of_iso i)

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∀ x ∈ V(G), bigAtLabel G x

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∃ x ∈ V(G), bigAtLabel G x

/-- Ambient edge-set predicate whose mathematical content is `IsDense`. -/
def denseAtEdgeSet {V : Type uV} {E : Type uE}
    (G : Graph V E) (_ : Set E) : Prop :=
  IsDense G

instance instDenseAtSupportedEdgeSetTransport :
    EquivariantTransport
      (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
        {F : Set E // F ⊆ E(G)} → Prop)
      (fun {V : Type uV'} {E : Type uE'} (G : Graph V E) ↦
        {F : Set E // F ⊆ E(G)} → Prop)
      (fun G F ↦ denseAtEdgeSet G F.1)
      (fun G F ↦ denseAtEdgeSet G F.1) where
  map_eq i := by
    funext F
    change IsDense _ = IsDense _
    exact propext (InvariantTransport.iff_of_iso i)

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∀ F : Set E, F ⊆ E(G) → denseAtEdgeSet G F

#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  ∃ F : Set E, F ⊆ E(G) ∧ denseAtEdgeSet G F

/-! A realistic compound expression should compose all of the above automatically. -/
#synth InvariantTransport ⧉ fun {V E} (G : Graph V E) ↦
  (∀ x ∈ V(G), bigAtLabel G x) ∧
    (∃ F : Set E, F ⊆ E(G) ∧ denseAtEdgeSet G F)

/-! ## Homogeneous `Equivariant` remains available for data-valued sections -/

def emptyVertexSet :
    {V : Type uV} → {E : Type uE} → (G : Graph V E) → Set V(G) :=
  fun _ ↦ ∅

instance instEmptyVertexSet :
    Equivariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set V(G)) emptyVertexSet where
  map_eq i := by simp only [emptyVertexSet, IsoAction.map_set, Equiv.Set.congr_apply, image_empty]

def emptyEdgeSet : {V : Type uV} → {E : Type uE} → (G : Graph V E) → Set E(G) := fun _ ↦ ∅

instance instEmptyEdgeSet :
    Equivariant (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set E(G)) emptyEdgeSet where
  map_eq i := by
    simp only [emptyEdgeSet, IsoAction.map_set, Equiv.Set.congr_apply, image_empty]

#synth Equivariant
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦ Set V(G) × Set E(G))
  (fun {V : Type uV} {E : Type uE} (G : Graph V E) ↦
    (emptyVertexSet G, emptyEdgeSet G))

/-! ## Relabel facade: proof-facing convenience without changing `Iso` -/

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    G.relabel i.vertexEmbeddingInto i.edgeEmbeddingInto = H :=
  i.relabel_eq

example
    {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    (G : Graph V E) (H : Graph V' E') :
    G.IsIsoTo H ↔
      ∃ fv : V(G) ↪ V', ∃ fe : E(G) ↪ E',
        G.relabel fv fe = H :=
  isIsoTo_iff_exists_relabel G H

/-- Separate fixture so the relabel-first constructor itself is tested without overlapping the
primary `IsBig` instance. -/
def IsBigViaRelabel {V : Type uV} {E : Type uE} (G : Graph V E) : Prop :=
  IsBig G

instance instIsBigViaRelabelTransport : InvariantTransport ⧉ IsBigViaRelabel :=
  InvariantTransport.of_relabel_iff fun fv fe ↦ isBig_iff_of_iso (relabelIso _ fv fe)

#synth InvariantTransport ⧉ IsBigViaRelabel
#synth Invariant IsBigViaRelabel

/-! ## End-to-end transfer ergonomics -/

example
    {V : Type uV} {E : Type uE} {G : Graph V E}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (h : ∀ H : Graph ℕ ℕ, V(H).Finite → E(H).Finite → IsBig H) :
    IsBig G :=
  InvariantTransport.of_forall_finite_nat h hV hE

end GFCheck
end Graph
