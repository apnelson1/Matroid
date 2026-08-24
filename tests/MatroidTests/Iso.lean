module

public import Matroid.Graph.Iso.Invariant
public import Matroid.Graph.Iso.Lawful
public import Matroid.Iso.Invariant
public import Matroid.Iso.Lawful

@[expose] public section

open Set Function

/-! ## Graph coverage -/

namespace GraphGenericTests

open Graph

universe uV₁ uE₁ uV₂ uE₂ uV₃ uE₃

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G))

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ E(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ E(G))

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ Set V(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ Set V(G))

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G) → Set V(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G) → Set V(G))

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G) × E(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G) × E(G))

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G) ⊕ E(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G) ⊕ E(G))

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ Option V(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ Option V(G))

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ {X : Set V // X ⊆ V(G)})
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ {X : Set V // X ⊆ V(G)})

#synth Graph.IsoEquiv
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ {X : Set E // X ⊆ E(G)})
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ {X : Set E // X ⊆ E(G)})

-- The Graph adapter also exposes the generic object-map/reindex layer.
#synth Graph.IsoEquiv
  (Graph.Family.reindex (id : Graph.IsoObj.{uV₁, uE₁} → Graph.IsoObj.{uV₁, uE₁})
    Graph.VertexFamily.{uV₁, uE₁})
  (Graph.Family.reindex (id : Graph.IsoObj.{uV₁, uE₁} → Graph.IsoObj.{uV₁, uE₁})
    Graph.VertexFamily.{uV₁, uE₁})

-- Variable output universe: both argument and output move with the graph.
#synth Graph.IsoInvariant
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) (x : V(G)) ↦ x)
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) (x : V(G)) ↦ x)

instance instAdj : Graph.IsoInvariant
    (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) (x y : V(G)) ↦ G.Adj x.1 y.1)
    (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) (x y : V(G)) ↦ G.Adj x.1 y.1) :=
  _root_.IsoInvariant.of_map_apply₂ _ _ fun i x y ↦ by
    change Graph.Iso _ _ at i
    exact propext (Graph.Iso.adj_vertexEquiv i x y)

#synth Graph.IsoInvariant
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦
    ∀ x, x ∈ V(G) → ∀ y, y ∈ V(G) → G.Adj x y)
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦
    ∀ x, x ∈ V(G) → ∀ y, y ∈ V(G) → G.Adj x y)

-- The duplicate-expression macro remains usable at the adapter boundary.
#synth Graph.IsoInvariant ⧉ fun {V E} (G : Graph V E) ↦
  ∀ x, x ∈ V(G) → ∀ y, y ∈ V(G) → G.Adj x y

#synth Graph.IsoInvariant
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦
    ∀ x, x ∈ V(G) → ∃ y, y ∈ V(G) ∧ G.Adj x y)
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦
    ∀ x, x ∈ V(G) → ∃ y, y ∈ V(G) ∧ G.Adj x y)

#synth Graph.IsoInvariant
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦
    ∃ x, x ∈ V(G) ∧ ∀ y, y ∈ V(G) → G.Adj x y)
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦
    ∃ x, x ∈ V(G) ∧ ∀ y, y ∈ V(G) → G.Adj x y)

-- All structural lawfulness should be generic after the two primitive graph seeds.
#synth Graph.IsoEquiv.Lawful
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G))
  (fun {V : Type uV₃} {E : Type uE₃} (G : Graph V E) ↦ V(G))

#synth Graph.IsoEquiv.Lawful
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ E(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ E(G))
  (fun {V : Type uV₃} {E : Type uE₃} (G : Graph V E) ↦ E(G))

#synth Graph.IsoEquiv.Lawful
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ V(G) → Set V(G))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ V(G) → Set V(G))
  (fun {V : Type uV₃} {E : Type uE₃} (G : Graph V E) ↦ V(G) → Set V(G))

#synth Graph.IsoEquiv.Lawful
  (fun {V : Type uV₁} {E : Type uE₁} (G : Graph V E) ↦ Option (V(G) ⊕ E(G)))
  (fun {V : Type uV₂} {E : Type uE₂} (G : Graph V E) ↦ Option (V(G) ⊕ E(G)))
  (fun {V : Type uV₃} {E : Type uE₃} (G : Graph V E) ↦ Option (V(G) ⊕ E(G)))

example {V : Type uV₁} {E : Type uE₁} (G : Graph V E) (x : V(G)) :
    Graph.IsoEquiv.map (F := fun {V E : Type _} (G : Graph V E) ↦ V(G))
    (F' := fun {V E : Type _} (G : Graph V E) ↦ V(G)) (Graph.Iso.id G) x = x := by
  exact Graph.IsoEquiv.Lawful.map_id (F := fun {V E : Type _} (G : Graph V E) ↦ V(G)) G x

example {V E V' E' : Type*} {G : Graph V E} {H : Graph V' E'} (i : Graph.Iso G H) :
    Graph.IsoEquiv.map (F := fun {V E : Type _} (G : Graph V E) ↦ V(G))
    (F' := fun {V E : Type _} (G : Graph V E) ↦ V(G)) i.symm =
    (Graph.IsoEquiv.map (F := fun {V E : Type _} (G : Graph V E) ↦ V(G))
    (F' := fun {V E : Type _} (G : Graph V E) ↦ V(G)) i).symm := by
  exact Graph.IsoEquiv.Lawful.map_symm i

end GraphGenericTests

/-! ## Matroid coverage -/

namespace MatroidGenericTests

open Matroid

universe uα₁ uα₂ uα₃ uι uR

#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ M.E)
  (fun {α : Type uα₂} (M : Matroid α) ↦ M.E)

#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E)
  (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E)

#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E → Prop)
  (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E → Prop)

#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E → Set M.E)
  (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E → Set M.E)

#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E × Option M.E)
  (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E × Option M.E)

-- Ambient support classes represented intrinsically.
#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ {e : α // e ∈ M.E})
  (fun {α : Type uα₂} (M : Matroid α) ↦ {e : α // e ∈ M.E})

#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ {X : Set α // X ⊆ M.E})
  (fun {α : Type uα₂} (M : Matroid α) ↦ {X : Set α // X ⊆ M.E})

#synth Matroid.IsoEquiv
  (fun {α : Type uα₁} (M : Matroid α) ↦ {X : Fin 3 → Set α // ∀ i, X i ⊆ M.E})
  (fun {α : Type uα₂} (M : Matroid α) ↦ {X : Fin 3 → Set α // ∀ i, X i ⊆ M.E})

-- Every active predicate registered by the current Matroid.Invariant system.
#synth Matroid.IsoInvariant Matroid.IndepObs.{uα₁} Matroid.IndepObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.DepObs.{uα₁} Matroid.DepObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.IsBaseObs.{uα₁} Matroid.IsBaseObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.CoindepObs.{uα₁} Matroid.CoindepObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.CodepObs.{uα₁} Matroid.CodepObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.SpanningObs.{uα₁} Matroid.SpanningObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.NonspanningObs.{uα₁} Matroid.NonspanningObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.IsBasisObs.{uα₁} Matroid.IsBasisObs.{uα₂}
#synth Matroid.IsoInvariant Matroid.EncardObs.{uα₁} Matroid.EncardObs.{uα₂}

-- The old `InvariantFun.of_empty` branch is recovered by an actual isomorphism of empty matroids.
example {α : Type uα₁} {β : Type uα₂} :
    Matroid.IndepObs (Matroid.emptyOn α) (∅ : Set (Matroid.emptyOn α).E) ↔
      Matroid.IndepObs (Matroid.emptyOn β) (∅ : Set (Matroid.emptyOn β).E) := by
  rw [(Set.image_empty (Matroid.empty_iso_empty α β).toEquiv).symm]
  exact Matroid.IsoInvariant.iff_map_iso (P := Matroid.IndepObs.{uα₁})
    (P' := Matroid.IndepObs.{uα₂}) (Matroid.empty_iso_empty α β) (∅ : Set (Matroid.emptyOn α).E)

#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ (7 : ℕ∞))
  (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ (7 : ℕ∞))

-- Pointwise proposition algebra works while the set argument is still free.
#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ ¬ Matroid.IndepObs M X)
  (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ ¬ Matroid.IndepObs M X)

#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦
    Matroid.IndepObs M X ∨ Matroid.DepObs M X)
  (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦
    Matroid.IndepObs M X ∨ Matroid.DepObs M X)

-- Binary input, replacing the role of InvariantFun₂.
#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) (I X : Set M.E) ↦
    M.IsBasis (↑I : Set α) (↑X : Set α))
  (fun {α : Type uα₂} (M : Matroid α) (I X : Set M.E) ↦
    M.IsBasis (↑I : Set α) (↑X : Set α))

-- Variable output: the complete collection of independent subsets.
#synth Matroid.IsoInvariant Matroid.IndepSetsObs.{uα₁} Matroid.IndepSetsObs.{uα₂}

-- Dual transport is reached through the named family wrapper, which retains the `Reindex` node.
#synth Matroid.IsoEquiv
  (Matroid.Family.dual Matroid.GroundFamily.{uα₁})
  (Matroid.Family.dual Matroid.GroundFamily.{uα₂})

#synth Matroid.IsoEquiv
  (Matroid.Family.dual (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E))
  (Matroid.Family.dual (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E))

#synth Matroid.IsoEquiv
  (Matroid.Family.dual (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E → Prop))
  (Matroid.Family.dual (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E → Prop))

-- Dual precomposition uses the named family wrapper, not a separate proof for each predicate.
example : Matroid.IsoInvariant
    (F := Matroid.Family.dual (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E → Prop))
    (F' := Matroid.Family.dual (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E → Prop))
    (fun {α : Type uα₁} (M : Matroid α) ↦ Matroid.IndepObs M✶)
    (fun {α : Type uα₂} (M : Matroid α) ↦ Matroid.IndepObs M✶) :=
  Matroid.IsoInvariant.dual Matroid.IndepObs.{uα₁} Matroid.IndepObs.{uα₂}

/-! ### Reindex architecture regression tests -/

-- The explicit node is inferable at the base family and fiber constructors recurse above it.
#synth _root_.IsoEquiv
  (_root_.Reindex Matroid.dualObj.{uα₁} (fun X : Matroid.IsoObj.{uα₁} ↦ X.matroid.E))
  (_root_.Reindex Matroid.dualObj.{uα₂} (fun X : Matroid.IsoObj.{uα₂} ↦ X.matroid.E))

#synth _root_.IsoEquiv
  (fun X : Matroid.IsoObj.{uα₁} ↦
    Set ((_root_.Reindex Matroid.dualObj.{uα₁} (fun Y : Matroid.IsoObj.{uα₁} ↦ Y.matroid.E)) X)
      → Prop)
  (fun X : Matroid.IsoObj.{uα₂} ↦
    Set ((_root_.Reindex Matroid.dualObj.{uα₂} (fun Y : Matroid.IsoObj.{uα₂} ↦ Y.matroid.E)) X)
      → Prop)

-- Explicit `IsoMap` composition is recursively available and can itself be reindexed.
#synth _root_.IsoMap
  (Matroid.dualObj.{uα₁} ∘ Matroid.dualObj.{uα₁})
  (Matroid.dualObj.{uα₂} ∘ Matroid.dualObj.{uα₂})

#synth Matroid.IsoEquiv
  (Matroid.Family.reindex (Matroid.dualObj.{uα₁} ∘ Matroid.dualObj.{uα₁})
    Matroid.GroundFamily.{uα₁})
  (Matroid.Family.reindex (Matroid.dualObj.{uα₂} ∘ Matroid.dualObj.{uα₂})
    Matroid.GroundFamily.{uα₂})

-- Optional coherence propagates through the same canonical dual reindexing.
#synth Matroid.IsoEquiv.Lawful
  (Matroid.Family.dual Matroid.GroundFamily.{uα₁})
  (Matroid.Family.dual Matroid.GroundFamily.{uα₂})
  (Matroid.Family.dual Matroid.GroundFamily.{uα₃})

/-- Small intrinsic element leaf used to test bounded quantification over the ambient carrier. -/
instance instSingletonIndep : Matroid.IsoInvariant
    (fun {α : Type uα₁} (M : Matroid α) (e : M.E) ↦ M.Indep ({e.1} : Set α))
    (fun {α : Type uα₂} (M : Matroid α) (e : M.E) ↦ M.Indep ({e.1} : Set α)) :=
  _root_.IsoInvariant.of_map_apply _ _ fun i e ↦ by
    change Matroid.Iso _ _ at i
    refine propext ?_
    simpa [Set.image_singleton, Matroid.IndepObs] using
      Matroid.IsoInvariant.iff_map_iso (P := Matroid.IndepObs.{uα₁})
        (P' := Matroid.IndepObs.{uα₂}) i ({e} : Set _)

#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) ↦
    ∀ e, e ∈ M.E → M.Indep ({e} : Set α))
  (fun {α : Type uα₂} (M : Matroid α) ↦
    ∀ e, e ∈ M.E → M.Indep ({e} : Set α))

-- Arbitrary-output analogue of the old `InvariantFun.map_eq`.
example {α : Type uα₁} {β : Type uα₂} {M : Matroid α} (f : α → β)
    (hf : InjOn f M.E) (X : Set M.E) :
    X.encard =
      (Matroid.IsoEquiv.map
        (F := (fun {α} (M : Matroid α) ↦ Set M.E))
        (F' := (fun {α} (M : Matroid α) ↦ Set M.E))
        (Matroid.isoMap M f hf) X).encard := by
  simpa [Matroid.EncardObs] using
    (Matroid.IsoInvariant.map_apply_map (F := Matroid.EncardObs.{uα₁})
      (F' := Matroid.EncardObs.{uα₂}) hf X)

-- Current map-oriented proposition statements are recovered intrinsically by applying invariance to
-- isoMap.
example {α : Type uα₁} {β : Type uα₂} {M : Matroid α} (f : α → β)
    (hf : InjOn f M.E) (X : Set M.E) :
    Matroid.IndepObs M X ↔
      Matroid.IndepObs (M.map f hf)
        (Matroid.IsoEquiv.map
          (F := (fun {α} (M : Matroid α) ↦ Set M.E))
          (F' := (fun {α} (M : Matroid α) ↦ Set M.E))
          (Matroid.isoMap M f hf) X) :=
  Matroid.IsoInvariant.iff_map (P := Matroid.IndepObs) (P' := Matroid.IndepObs) hf X

-- Fully heterogeneous three-universe lawfulness.
#synth Matroid.IsoEquiv.Lawful
  (fun {α : Type uα₁} (M : Matroid α) ↦ M.E)
  (fun {α : Type uα₂} (M : Matroid α) ↦ M.E)
  (fun {α : Type uα₃} (M : Matroid α) ↦ M.E)

#synth Matroid.IsoEquiv.Lawful
  (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E → Set M.E)
  (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E → Set M.E)
  (fun {α : Type uα₃} (M : Matroid α) ↦ Set M.E → Set M.E)

/-! ### Generic reconstruction of old `InvariantFun` combinators -/

-- Complement is generic, not matroid-specific.
#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ Xᶜ)
  (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ Xᶜ)

-- `Minimal` and `Maximal` now follow from generic logical/set closure.
#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦
    Minimal (Matroid.IndepObs M) X)
  (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦
    Minimal (Matroid.IndepObs M) X)

#synth Matroid.IsoInvariant
  (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦
    Maximal (Matroid.IndepObs M) X)
  (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦
    Maximal (Matroid.IndepObs M) X)

-- Old `InvariantFun.comp_right`: postcompose encard by a fixed function.
example : Matroid.IsoInvariant
    (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ (7 : ℕ∞))
    (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ (7 : ℕ∞)) :=
  Matroid.IsoInvariant.comp_right Matroid.EncardObs.{uα₁} Matroid.EncardObs.{uα₂}
    (fun n ↦ n ≤ (7 : ℕ∞))

-- Old `InvariantFun.comp`: precompose independence by the invariant complement endomorphism.
example : Matroid.IsoInvariant
    (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ Matroid.IndepObs M Xᶜ)
    (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ Matroid.IndepObs M Xᶜ) :=
  Matroid.IsoInvariant.comp Matroid.IndepObs.{uα₁} Matroid.IndepObs.{uα₂}
    (fun _ X ↦ Xᶜ) (fun _ X ↦ Xᶜ)

-- Old `InvariantFun.combine`: combine two functions with the same transported set argument.
example : Matroid.IsoInvariant
    (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ (X.encard, X.encard ≤ (7 : ℕ∞)))
    (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ (X.encard, X.encard ≤ (7 : ℕ∞))) :=
  Matroid.IsoInvariant.combine
    Matroid.EncardObs.{uα₁} Matroid.EncardObs.{uα₂}
    (fun {α : Type uα₁} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ (7 : ℕ∞))
    (fun {α : Type uα₂} (M : Matroid α) (X : Set M.E) ↦ X.encard ≤ (7 : ℕ∞))
    (fun n h ↦ (n, h))

-- Target-oriented map form: intrinsic replacement for the old `map_set_iff_exists`.
example {α : Type uα₁} {β : Type uα₂} {M : Matroid α} (f : α → β)
    (hf : InjOn f M.E) (Y : Set (M.map f hf).E) :
    Matroid.IndepObs M
        ((Matroid.IsoEquiv.map
          (F := (fun {α} (M : Matroid α) ↦ Set M.E))
          (F' := (fun {α} (M : Matroid α) ↦ Set M.E))
          (Matroid.isoMap M f hf)).symm Y) ↔
      Matroid.IndepObs (M.map f hf) Y :=
  Matroid.IsoInvariant.iff_map_target (P := Matroid.IndepObs)
    (P' := Matroid.IndepObs) hf Y

example {α : Type uα₁} (M : Matroid α) (x : M.E) :
    Matroid.IsoEquiv.map
      (F := (fun {α} (M : Matroid α) ↦ M.E))
      (F' := (fun {α} (M : Matroid α) ↦ M.E))
      (Matroid.Iso.refl : Matroid.Iso M M) x = x := by
  exact Matroid.IsoEquiv.Lawful.map_id (F := fun {α} (M : Matroid α) ↦ M.E) M x

example {α : Type uα₁} {β : Type uα₂} {M : Matroid α} {N : Matroid β}
    (i : Matroid.Iso M N) :
    Matroid.IsoEquiv.map
      (F := (fun {α} (M : Matroid α) ↦ M.E))
      (F' := (fun {α} (M : Matroid α) ↦ M.E)) i.symm =
      (Matroid.IsoEquiv.map
        (F := (fun {α} (M : Matroid α) ↦ M.E))
        (F' := (fun {α} (M : Matroid α) ↦ M.E)) i).symm := by
  exact Matroid.IsoEquiv.Lawful.map_symm i


/-! ### Feedback loop: `IsoInvariant → IsoMap → IsoEquiv → IsoInvariant` -/

/-- A test object construction parameterized by invariant data. -/
def restrictObj (R : (X : Matroid.IsoObj.{uR}) → Set X.matroid.E) (X : Matroid.IsoObj.{uR}) :
    Matroid.IsoObj.{uR} :=
  ⟨X.α, X.matroid ↾ (↑(R X) : Set X.α)⟩

-- This is the feedback step: an `IsoInvariant` parameter creates a new `IsoMap`.
instance instIsoMapRestrict {R : (X : Matroid.IsoObj.{uα₁}) → Set X.matroid.E}
    {R' : (X : Matroid.IsoObj.{uα₂}) → Set X.matroid.E} [hR : _root_.IsoInvariant R R'] :
    _root_.IsoMap (restrictObj R) (restrictObj R') where
  map {X Y} i := by
    refine Matroid.Iso.restrict (i : X.matroid ≂ Y.matroid) (by simp) (by simp) ?_
    intro x
    simp only [Subtype.val_injective.mem_set_image]
    rw [← hR.map_eq i]
    exact (Equiv.injective _).mem_set_image

-- The new object map immediately feeds back into family transport.
example {R : (X : Matroid.IsoObj.{uα₁}) → Set X.matroid.E}
    {R' : (X : Matroid.IsoObj.{uα₂}) → Set X.matroid.E} [_root_.IsoInvariant R R'] :
    Matroid.IsoEquiv
      (Matroid.Family.reindex (restrictObj R) Matroid.GroundFamily.{uα₁})
      (Matroid.Family.reindex (restrictObj R') Matroid.GroundFamily.{uα₂}) :=
  inferInstance

-- Full loop: `IsoInvariant → IsoMap → IsoEquiv → IsoInvariant`.
example {R : (X : Matroid.IsoObj.{uα₁}) → Set X.matroid.E}
    {R' : (X : Matroid.IsoObj.{uα₂}) → Set X.matroid.E} [_root_.IsoInvariant R R'] :
    Matroid.IsoInvariant
      (F := Matroid.Family.reindex (restrictObj R)
        (fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E → Prop))
      (F' := Matroid.Family.reindex (restrictObj R')
        (fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E → Prop))
      (fun {α} M ↦ Matroid.IndepObs (restrictObj R ⟨α, M⟩).matroid)
      (fun {α} M ↦ Matroid.IndepObs (restrictObj R' ⟨α, M⟩).matroid) :=
  Matroid.IsoInvariant.reindex (f := restrictObj R) (f' := restrictObj R')
    (F := fun {α : Type uα₁} (M : Matroid α) ↦ Set M.E → Prop)
    (F' := fun {α : Type uα₂} (M : Matroid α) ↦ Set M.E → Prop)
    Matroid.IndepObs.{uα₁} Matroid.IndepObs.{uα₂}

end MatroidGenericTests
