module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Connected.LocallyConnected

public section

/-!
# Frontiers and counting of connected components

Small facts about `connectedComponentIn` and the frontiers of its components: where the frontier of
a component lies, when that frontier is nonempty, and when an open set is a component of a
complement.

`ConnectedComponents.card_eq_two` then counts the components of a set presented as two disjoint
nonempty open connected pieces.
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
  have hyV : y ∈ connectedComponentIn U y := mem_connectedComponentIn hyU
  obtain ⟨z, hzV, hzK⟩ :=
    (mem_closure_iff.mp (frontier_subset_closure hyfr)) _ hU.connectedComponentIn hyV
  have hKopen : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
  refine (hKopen.frontier_eq ▸ hyfr).2 ?_
  rw [← ((connectedComponentIn_eq hzV).trans (connectedComponentIn_eq hzK).symm)]
  exact hyV

/-- If `S` is closed, the frontier of every component of `Sᶜ` lies in `S`. -/
theorem IsClosed.frontier_connectedComponentIn_compl_subset [LocallyConnectedSpace X]
    (hS : IsClosed S) : frontier (connectedComponentIn Sᶜ x) ⊆ S := by
  simpa using hS.isOpen_compl.frontier_connectedComponentIn_subset_compl

/-- A component of a proper set in a preconnected ambient space has nonempty frontier.

No openness or local-connectedness hypothesis is needed for this statement. -/
theorem frontier_connectedComponentIn_nonempty [PreconnectedSpace X]
    (hx : x ∈ U) (hU : U ≠ Set.univ) : (frontier (connectedComponentIn U x)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨⟨x, mem_connectedComponentIn hx⟩, ?_⟩
  intro hK
  apply hU
  ext y
  simp only [mem_univ, iff_true]
  exact connectedComponentIn_subset _ _ (by
    rw [hK]
    exact mem_univ y)

/-- A component of the complement of a nonempty set has nonempty frontier in a preconnected
ambient space. -/
theorem frontier_connectedComponentIn_compl_nonempty [PreconnectedSpace X]
    (hS : S.Nonempty) (hx : x ∉ S) : (frontier (connectedComponentIn Sᶜ x)).Nonempty := by
  apply frontier_connectedComponentIn_nonempty hx
  intro hSc
  obtain ⟨s, hs⟩ := hS
  refine (show s ∈ Sᶜ from ?_) hs
  rw [hSc]
  exact mem_univ s

/-- An open connected set disjoint from `K` whose frontier lies in `K` is a connected component of
the complement of `K`. -/
theorem eq_connectedComponentIn_of_frontier_subset {W K : Set X} {a : X} (hW : IsOpen W)
    (hWc : IsPreconnected W) (hWK : Disjoint W K) (hfr : frontier W ⊆ K) (ha : a ∈ W) :
    W = connectedComponentIn Kᶜ a := by
  have hWKc : W ⊆ Kᶜ := hWK.subset_compl_right
  refine (hWc.subset_connectedComponentIn ha hWKc).antisymm
    <| isPreconnected_connectedComponentIn.subset_left_of_subset_union hW
    isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.mpr subset_closure)
    (fun z hz ↦ (em (z ∈ closure W)).imp (fun hzc ↦ ?_) id)
    ⟨a, mem_connectedComponentIn (hWKc ha), ha⟩
  have hzf : z ∉ frontier W := fun h ↦ connectedComponentIn_subset _ _ hz (hfr h)
  rw [hW.frontier_eq] at hzf
  simp only [mem_sdiff, hzc, true_and, not_not] at hzf
  exact hzf

/-! ### Counting the components of a two-piece open partition -/

namespace ConnectedComponents

/-- A set that splits into two disjoint nonempty open connected pieces has exactly two connected
components.

Three places in this repository compute this by hand from `equivOfIsClopenOfIsConnected`: the two
sides of a Jordan curve in the plane and on the sphere, and the two sides of a hyperplane
(`ContinuousLinearMap.connectedComponents_compl_hyperplane_card_eq_two`). What each of them repeats
is the `Bool`-indexed clopen cover of `↥s` built here.

That equivalence supplies `ConnectedComponents ↥s ≃ Bool` under these same hypotheses; only the
cardinality is stated, since that is what the callers hold and a promoted definition is a larger
commitment than a promoted lemma. `IsOpen` is taken in `X` rather than relative to `s` — more than
the proof needs, and what every call site has. -/
theorem card_eq_two {s u v : Set X} (hu : IsOpen u) (hv : IsOpen v) (hcu : IsConnected u)
    (hcv : IsConnected v) (hd : Disjoint u v) (huv : u ∪ v = s) :
    Nat.card (ConnectedComponents ↥s) = 2 := by
  have hpre {w : Set X} (hw : IsOpen w) (hcw : IsConnected w) (hws : w ⊆ s) :
      IsOpen ((↑) ⁻¹' w : Set ↥s) ∧ IsConnected ((↑) ⁻¹' w : Set ↥s) := by
    refine ⟨hw.preimage continuous_subtype_val, ⟨?_, ?_⟩⟩
    · obtain ⟨x, hx⟩ := hcw.nonempty
      exact ⟨⟨x, hws hx⟩, hx⟩
    · refine IsInducing.subtypeVal.isPreconnected_image.1 ?_
      rw [Subtype.image_preimage_coe, inter_eq_right.2 hws]
      exact hcw.isPreconnected
  obtain ⟨hou, hnu⟩ := hpre hu hcu (huv ▸ subset_union_left)
  obtain ⟨hov, hnv⟩ := hpre hv hcv (huv ▸ subset_union_right)
  have hcompl : ((↑) ⁻¹' v : Set ↥s) = ((↑) ⁻¹' u : Set ↥s)ᶜ := by
    ext x
    have hx : (x : X) ∈ u ∪ v := huv ▸ x.2
    exact ⟨fun h hu' ↦ hd.notMem_of_mem_left hu' h, fun h ↦ hx.resolve_left h⟩
  refine (Nat.card_congr (equivOfIsClopenOfIsConnected
      (U := fun b : Bool ↦ ((↑) ⁻¹' (cond b u v) : Set ↥s)) (fun b ↦ ?_) ?_ ?_
      (fun b ↦ ?_))).trans (by simp)
  · cases b
    · exact ⟨hcompl ▸ hou.isClosed_compl, hov⟩
    · exact ⟨compl_compl ((↑) ⁻¹' u : Set ↥s) ▸ hcompl ▸ hov.isClosed_compl, hou⟩
  · intro b b' hbb'
    cases b <;> cases b' <;> simp only [Function.onFun, Bool.cond_true, Bool.cond_false] <;>
      first
        | exact absurd rfl hbb'
        | exact (hd.preimage _).symm
        | exact hd.preimage _
  · refine eq_univ_of_forall fun x ↦ ?_
    obtain h | h := (huv ▸ x.2 : (x : X) ∈ u ∪ v)
    · exact mem_iUnion.2 ⟨true, h⟩
    · exact mem_iUnion.2 ⟨false, h⟩
  · cases b
    · exact hnv
    · exact hnu

end ConnectedComponents
