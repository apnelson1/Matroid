module

public import Matroid.GraphTheory.GraphTopology.Map
public import Matroid.MiniTauCeti.JCT.Topology.OnePoint

/-! # Graphlike spaces in the one-point compactification -/

@[expose] public section

namespace GraphLike

variable {X : Type*} [TopologicalSpace X]

/-- Regard a graphlike space as a subspace of the one-point compactification. -/
noncomputable def onePoint (G : GraphLike X) : GraphLike (OnePoint X) :=
  G.map (↑) (OnePoint.isOpenEmbedding_coe.isEmbedding.comp
    Topology.IsEmbedding.subtypeVal)

@[simp] theorem onePoint_carrier (G : GraphLike X) :
    G.onePoint.carrier = (↑) '' G.carrier := rfl

end GraphLike
