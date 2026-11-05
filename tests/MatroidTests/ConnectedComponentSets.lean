module

import Matroid.ForMathlib.Topology.ConnectedComponent
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-! # Connected-component point sets without graph data -/

open Set ConnectedComponents

variable {X : Type*} [TopologicalSpace X]

example (c : ConnectedComponents X) (x : X) : x ∈ c.toSet ↔ mk x = c := Iff.rfl

example (c : ConnectedComponents X) : IsConnected c.toSet ∧ IsClosed c.toSet :=
  ⟨c.isConnected_toSet, c.isClosed_toSet⟩

example (c d : ConnectedComponents X) (h : c.toSet = d.toSet) : c = d :=
  toSet_injective h

example (c d : ConnectedComponents X) (h : c ≠ d) : Disjoint c.toSet d.toSet :=
  disjoint_toSet h

example : (mk (0 : ℝ)).toSet = univ := by
  rw [toSet_mk, PreconnectedSpace.connectedComponent_eq_univ]

-- A disconnected space gives distinct nonempty component sets.
example : letI : TopologicalSpace Bool := ⊥
    (mk false).toSet = {false} ∧ (mk true).toSet = {true} := by
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  simp only [toSet_mk, connectedComponent_eq_singleton, and_self]

-- The construction also works before any graph exists, on a nonclosed subspace.
example : ∃ c : ConnectedComponents ↥(Ioo (-1 : ℝ) 1),
    Subtype.val '' c.toSet = Ioo (-1 : ℝ) 1 ∧
    Ioo (-1 : ℝ) 1 ∩ closure (Subtype.val '' c.toSet) = Subtype.val '' c.toSet := by
  let : PreconnectedSpace ↥(Ioo (-1 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  let p : Ioo (-1 : ℝ) 1 := ⟨0, neg_one_lt_zero, zero_lt_one⟩
  refine ⟨mk p, ?_, (mk p).inter_closure_image_toSet⟩
  rw [toSet_mk, PreconnectedSpace.connectedComponent_eq_univ, image_univ, Subtype.range_coe]

/-- info: 'ConnectedComponents.inter_closure_image_toSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConnectedComponents.inter_closure_image_toSet
