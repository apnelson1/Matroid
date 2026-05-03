import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Matroid.Graph.Planarity.Topology.Path

instance (x : ℝ) : LocPathConnectedSpace (AddCircle x) := LocPathConnectedSpace.coinduced _

instance : LocPathConnectedSpace Circle := by
  convert LocPathConnectedSpace.coinduced AddCircle.homeomorphCircle'
  exact AddCircle.homeomorphCircle'.coinduced_eq.symm

namespace Circle

variable {x y z : Circle} {a b : ℝ} {s : Set ℝ}

open Set Function TopologicalSpace Topology Metric Nat Complex

lemma path_isClosedEmbedding_of_ne (hne : x ≠ y) : IsClosedEmbedding (path x y) :=
  (path x y).continuous.isClosedEmbedding (path_injective_of_ne hne)

end Circle
