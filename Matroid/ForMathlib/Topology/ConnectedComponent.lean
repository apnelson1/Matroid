module

public import Mathlib.Topology.Connected.LocallyConnected

public section

/-!
# Frontiers of connected components

Small facts about `connectedComponentIn` and the frontiers of its components.

The results describe where the frontier of a component lies and when that frontier is nonempty.
-/

open Set Topology

variable {X : Type*} [TopologicalSpace X] {U S : Set X} {x : X}

/-- In a locally connected space, the frontier of a connected component of an open set is outside
that open set. -/
theorem IsOpen.frontier_connectedComponentIn_subset_compl [LocallyConnectedSpace X]
    (hU : IsOpen U) : frontier (connectedComponentIn U x) ⊆ Uᶜ := by
  intro y hyfr
  by_contra hyU
  simp only [mem_compl_iff, not_not] at hyU
  have hVopen : IsOpen (connectedComponentIn U y) := hU.connectedComponentIn
  have hyV : y ∈ connectedComponentIn U y := mem_connectedComponentIn hyU
  obtain ⟨z, hzV, hzK⟩ :=
    (mem_closure_iff.mp (frontier_subset_closure hyfr)) _ hVopen hyV
  have heq : connectedComponentIn U y = connectedComponentIn U x :=
    (connectedComponentIn_eq hzV).trans (connectedComponentIn_eq hzK).symm
  have hyK : y ∈ connectedComponentIn U x := by
    rw [← heq]
    exact hyV
  have hKopen : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
  exact ((hKopen.frontier_eq ▸ hyfr).2 hyK)

/-- If `S` is closed, the frontier of every component of `Sᶜ` lies in `S`. -/
theorem IsClosed.frontier_connectedComponentIn_compl_subset [LocallyConnectedSpace X]
    (hS : IsClosed S) : frontier (connectedComponentIn Sᶜ x) ⊆ S := by
  simpa using hS.isOpen_compl.frontier_connectedComponentIn_subset_compl

/-- A component of a proper set in a preconnected ambient space has nonempty frontier.

No openness or local-connectedness hypothesis is needed for this statement. -/
theorem frontier_connectedComponentIn_nonempty [PreconnectedSpace X]
    (hx : x ∈ U) (hU : U ≠ Set.univ) :
    (frontier (connectedComponentIn U x)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨⟨x, mem_connectedComponentIn hx⟩, ?_⟩
  intro hK
  apply hU
  ext y
  simp only [mem_univ, iff_true]
  have hyK : y ∈ connectedComponentIn U x := by
    rw [hK]
    exact mem_univ y
  exact connectedComponentIn_subset _ _ hyK

/-- A component of the complement of a nonempty set has nonempty frontier in a preconnected
ambient space. -/
theorem frontier_connectedComponentIn_compl_nonempty [PreconnectedSpace X]
    (hS : S.Nonempty) (hx : x ∉ S) :
    (frontier (connectedComponentIn Sᶜ x)).Nonempty := by
  apply frontier_connectedComponentIn_nonempty hx
  intro hSc
  obtain ⟨s, hs⟩ := hS
  have hsc : s ∈ Sᶜ := by
    rw [hSc]
    exact mem_univ s
  exact hsc hs
