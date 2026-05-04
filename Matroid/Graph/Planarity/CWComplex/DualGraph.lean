import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Combinatorics.Graph.Subgraph
import Matroid.Graph.Planarity.Topology.Circuit
import Matroid.Graph.Forest
import Matroid.ForMathlib.Analysis.Normed.Module.Connected


open Metric Set Graph Topology.RelCWComplex Topology.CWComplex

namespace Topology

variable {E : Type*} [TopologicalSpace E]

/- Cycle & Jordan curve correspondence

  Given a CW complex `K`, a subset of `K` is a jordan curve iff it is a cycle of its one skeleton.
-/
theorem cycle_iff_jordan_curve (K C : Set E) [CWComplex K] (hCK : C ⊆ skeleton K 1) :
    IsCircuit C ↔ ∃ H : Graph (cell K 0) (cell K 1),
      H ≤ OneSkeletonGraph K ∧ H.IsCycle := by


variable [CWComplex (univ : Set E)]
    (h_max_two : ∀ e : cell (univ : Set E) 1, ∀ x y z : cell (univ : Set E) 2,
      closedCell 1 e ⊆ cellFrontier 2 x ∩ cellFrontier 2 y ∩ cellFrontier 2 z → z = x ∨ z = y)
    (h_no_dangling : ∀ e : cell (univ : Set E) 1, ∃ x : cell (univ : Set E) 2,
      closedCell 1 e ⊆ cellFrontier 2 x)

def CWComplex.DualGraph : Graph (cell (univ : Set E) 2) (cell (univ : Set E) 1) where
  vertexSet := univ
  edgeSet := univ
  IsLink e x y := closedCell 1 e ⊆ cellFrontier 2 x ∩ cellFrontier 2 y
  isLink_symm e he x y h := by grind
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    simp only [subset_inter_iff, and_imp] at h1 h2 h_max_two
    exact h_max_two e z w x h2.1 h2.2 h1.1
  left_mem_of_isLink e x y h := mem_univ _
  edge_mem_iff_exists_isLink e := by simp [h_no_dangling]
