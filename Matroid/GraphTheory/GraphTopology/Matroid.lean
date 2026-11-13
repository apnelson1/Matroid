module

public import Matroid.GraphTheory.GraphTopology.ToGraph
public import Matroid.Axioms.Circuit
public import Matroid.Graphic

/-! # Matroids on the geometric edges of graphlike spaces

Finite cycles and finite topological bonds define finitary matroids. The dual of the latter
is the topological cycle matroid; its circuits need not be intrinsic circuit supports for a
noncompact carrier.
-/

@[expose] public section

open Set WList Set.Notation Graph

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] {G : GraphLike X} {B C I : Set (Set X)}

/-- The matroid of finite cycles of the underlying graph. -/
def finiteCycleMatroid (G : GraphLike X) : Matroid (Set X) := G.toGraph.cycleMatroid

/-- The finitary matroid whose circuits are the finite topological bonds. -/
def finiteBondMatroid (G : GraphLike X) : Matroid (Set X) := FiniteCircuitMatroid.matroid {
  E := E(G)
  IsCircuit B := G.IsBond B ∧ B.Finite
  empty_not_isCircuit := fun h ↦ h.1.nonempty.ne_empty rfl
  circuit_antichain := fun B hB D hD hne hBD ↦
    hne (hD.1.eq_of_subset hB.1.isEdgeCut hB.1.nonempty hBD)
  circuit_elimination := by
    intro B D e hB hD hne heB heD
    obtain ⟨C, hC, hbond, hfin⟩ := hB.1.elimination hD.1 hB.2 hD.2 hne heB heD
    exact ⟨C, ⟨hbond, hfin⟩, fun he ↦ (hC he).2 rfl, hC.trans sdiff_subset⟩
  circuit_finite := fun _ h ↦ h.2
  circuit_subset_ground := fun _ h ↦ h.1.isEdgeCut.subset }

/-- The dual of the finite topological bond matroid. Without further hypotheses on the
carrier, its matroid circuits are not asserted to be intrinsic circuit supports. -/
def topologicalCycleMatroid (G : GraphLike X) : Matroid (Set X) := G.finiteBondMatroid✶

instance (G : GraphLike X) : Matroid.Finitary G.finiteCycleMatroid :=
  inferInstanceAs (Matroid.Finitary G.toGraph.cycleMatroid)

instance (G : GraphLike X) : Matroid.Finitary G.finiteBondMatroid := by
  unfold finiteBondMatroid
  infer_instance

@[simp] lemma finiteCycleMatroid_ground (G : GraphLike X) : G.finiteCycleMatroid.E = E(G) := rfl
@[simp] lemma finiteBondMatroid_ground (G : GraphLike X) : G.finiteBondMatroid.E = E(G) := rfl
@[simp] lemma topologicalCycleMatroid_ground (G : GraphLike X) :
    G.topologicalCycleMatroid.E = E(G) := rfl

@[simp] lemma finiteCycleMatroid_isCircuit :
    G.finiteCycleMatroid.IsCircuit C ↔ G.toGraph.IsCycleSet C := by
  exact congrFun G.toGraph.cycleMatroid_isCircuit C ▸ Iff.rfl

@[simp] lemma finiteCycleMatroid_isCocircuit :
    G.finiteCycleMatroid.IsCocircuit B ↔ G.toGraph.IsBond B :=
  G.toGraph.cycleMatroid_cocircuit B

@[simp] lemma finiteBondMatroid_isCircuit :
    G.finiteBondMatroid.IsCircuit B ↔ G.IsBond B ∧ B.Finite := by
  rw [finiteBondMatroid, FiniteCircuitMatroid.matroid_isCircuit]

lemma finiteBondMatroid_indep :
    G.finiteBondMatroid.Indep I ↔ I ⊆ E(G) ∧ ∀ B ⊆ I, G.IsBond B → B.Infinite := by
  rw [finiteBondMatroid, FiniteCircuitMatroid.matroid_indep_iff]
  simp only [not_and]
  rfl

@[simp] lemma topologicalCycleMatroid_isCocircuit :
    G.topologicalCycleMatroid.IsCocircuit B ↔ G.IsBond B ∧ B.Finite := by
  rw [topologicalCycleMatroid, Matroid.dual_isCocircuit_iff, finiteBondMatroid_isCircuit]

lemma topologicalCycleMatroid_isCocircuit_of_isCompact (hG : IsCompact G.carrier) :
    G.topologicalCycleMatroid.IsCocircuit B ↔ G.IsBond B := by
  rw [topologicalCycleMatroid_isCocircuit]
  exact ⟨And.left, fun h ↦ ⟨h, h.finite hG⟩⟩

lemma IsEdgeCut.finiteCycleMatroid_dual_cyclic (hB : G.IsEdgeCut B) :
    (G.finiteCycleMatroid✶).Cyclic B := hB.toGraph.cycleMatroid_dual_cyclic

/-- With finitely many vertices, the only difference between the two bond matroids is
whether infinite bonds are retained. -/
theorem finiteBondMatroid_eq_dual_iff (hV : V(G).Finite) :
    G.finiteBondMatroid = G.finiteCycleMatroid✶ ↔ ∀ B, G.IsBond B → B.Finite := by
  constructor
  · intro h B hB
    have hc : G.finiteBondMatroid.IsCircuit B := by
      rw [h, ← Matroid.isCocircuit_def, finiteCycleMatroid_isCocircuit]
      exact (isBond_iff_toGraph hV).mp hB
    exact (finiteBondMatroid_isCircuit.mp hc).2
  intro h
  apply Matroid.ext_isCircuit (by simp)
  intro B hB
  rw [finiteBondMatroid_isCircuit, ← Matroid.isCocircuit_def,
    finiteCycleMatroid_isCocircuit, ← isBond_iff_toGraph hV]
  exact ⟨And.left, fun hB ↦ ⟨hB, h B hB⟩⟩

lemma finiteBondMatroid_eq_dual (G : GraphLike X) [G.Finite] :
    G.finiteBondMatroid = G.finiteCycleMatroid✶ :=
  (finiteBondMatroid_eq_dual_iff Finite.vertexSet_finite).mpr fun _ hB ↦ hB.finite G.isCompact

@[simp] lemma topologicalCycleMatroid_eq_finiteCycleMatroid (G : GraphLike X) [G.Finite] :
    G.topologicalCycleMatroid = G.finiteCycleMatroid := by
  rw [topologicalCycleMatroid, finiteBondMatroid_eq_dual, Matroid.dual_dual]

/-- Finite matroid circuits are exactly finite intrinsic circuit supports. -/
theorem finiteCycleMatroid_isCircuit_iff :
    G.finiteCycleMatroid.IsCircuit C ↔ G.IsCircuitSet C ∧ C.Finite := by
  rw [finiteCycleMatroid_isCircuit]
  refine ⟨fun h ↦ ⟨isCircuitSet_of_toGraph_isCycleSet h, ?_⟩,
    fun h ↦ h.1.toGraph_isCycleSet h.2⟩
  obtain ⟨W, _, rfl⟩ := h
  exact W.edgeSet_finite

end GraphLike
