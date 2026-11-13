module

public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink
public import Matroid.MiniTauCeti.JCT.Topology.Path.Crossing
public import Matroid.MiniTauCeti.JCT.Topology.CrossesOnce

/-!
# Crossing parity and endpoint separation for primitive links

The path-level theorem supplies parity. Primitivity discharges the unique-visit condition,
including loops, and singleton frontier contact yields the endpoint separation criterion.
-/

@[expose] public section

open Set Function Topology Classical

namespace IsPrimitiveLink

variable {X : Type*} [TopologicalSpace X] {L U : Set X} {x y p : X}

/-- A primitive link avoiding a frontier has both endpoints on the same side. -/
theorem iff_mem_of_disjoint_frontier (hL : IsPrimitiveLink L x y)
    (hdis : Disjoint L (frontier U)) : x ∈ U ↔ y ∈ U := by
  rcases hL.isConnected.isPreconnected.disjoint_frontier_iff.mp hdis with hi | ho
  · exact iff_of_true (interior_subset (hi hL.left_mem)) (interior_subset (hi hL.right_mem))
  · exact iff_of_false (interior_subset (ho hL.left_mem)) (interior_subset (ho hL.right_mem))

/-- Primitive-link crossing parity depends only on the endpoint sides. -/
theorem ncard_boundaryCrossings_mod_two [T2Space ↥L]
    (hL : IsPrimitiveLink L x y) (hf : (L ∩ frontier U).Finite)
    (hx : x ∉ frontier U) (hy : y ∉ frontier U) :
    (boundaryCrossings L U).ncard % 2 = if (x ∈ U ↔ y ∈ U) then 0 else 1 := by
  obtain ⟨P, hP, hPL⟩ := hL
  apply P.ncard_boundaryCrossings_mod_two hPL hf _ hx hy
  intro s hs t ht heq
  obtain heq | hpair := hP heq
  · exact heq
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := pair_eq_pair_iff.mp hpair
  · exact (hx (by simpa using boundaryCrossings_subset_frontier L U hs)).elim
  · exact (hy (by simpa using boundaryCrossings_subset_frontier L U hs)).elim

/-- At a unique frontier contact, crossing is equivalent to opposite endpoint sides. -/
theorem mem_boundaryCrossings_iff_of_inter_eq_singleton [T2Space ↥L]
    (hL : IsPrimitiveLink L x y) (hinter : L ∩ frontier U = {p})
    (hx : x ∉ frontier U) (hy : y ∉ frontier U) :
    p ∈ boundaryCrossings L U ↔ ¬ (x ∈ U ↔ y ∈ U) := by
  classical
  have hsub : boundaryCrossings L U ⊆ {p} := by
    rw [← hinter]
    exact boundaryCrossings_subset L U
  have hpar := ncard_boundaryCrossings_mod_two hL
    (hinter ▸ finite_singleton p) hx hy
  constructor
  · intro hp hxy
    have heq : boundaryCrossings L U = {p} :=
      hsub.antisymm (singleton_subset_iff.mpr hp)
    rw [heq, ncard_singleton, ite_eq_left hxy] at hpar
    norm_num at hpar
  · intro hxy
    by_contra hp
    have heq : boundaryCrossings L U = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact hp ((mem_singleton_iff.mp (hsub hq)) ▸ hq)
    rw [heq, ncard_empty, ite_eq_right hxy] at hpar
    norm_num at hpar

/-- A single boundary crossing separates the endpoints into different complement components. -/
theorem not_mem_connectedComponentIn_compl_frontier [T2Space ↥L]
    (hL : IsPrimitiveLink L x y) (hinter : L ∩ frontier U = {p})
    (hx : x ∉ frontier U) (hy : y ∉ frontier U)
    (hp : p ∈ boundaryCrossings L U) :
    x ∉ connectedComponentIn (frontier U)ᶜ y := by
  intro hxc
  have hyc : y ∈ connectedComponentIn (frontier U)ᶜ y := mem_connectedComponentIn hy
  have hd : Disjoint (connectedComponentIn (frontier U)ᶜ y) (frontier U) :=
    disjoint_left.mpr fun z hz hzU ↦ connectedComponentIn_subset _ _ hz hzU
  have hside := isPreconnected_connectedComponentIn.disjoint_frontier_iff.mp hd
  apply (mem_boundaryCrossings_iff_of_inter_eq_singleton hL hinter hx hy).mp hp
  rcases hside with hi | ho
  · exact iff_of_true (interior_subset (hi hxc)) (interior_subset (hi hyc))
  · exact iff_of_false (interior_subset (ho hxc)) (interior_subset (ho hyc))

end IsPrimitiveLink

namespace Set.CrossesOnce

variable {X : Type*} [TopologicalSpace X] {S L U : Set X} {x y : X}

/-- A primitive link crossing a separating frontier once has endpoints on opposite sides.
Only the frontier's local sides at the crossing need be preconnected. -/
theorem not_iff_mem [T2Space ↥L] (h : CrossesOnce L S) (hL : IsPrimitiveLink L x y)
    (hfront : frontier U = S) (hx : x ∉ S) (hy : y ∉ S)
    (hlocal : ∀ p ∈ L ∩ S, PreconnectedSidesAt U p) :
    ¬ (x ∈ U ↔ y ∈ U) := by
  have hcross := h.boundaryCrossings_eq_inter hfront hlocal
  obtain ⟨p, hinter⟩ := (crossesOnce_iff_forall.mp h).1
  apply (hL.mem_boundaryCrossings_iff_of_inter_eq_singleton
    (by rw [hfront]; exact hinter) (hfront ▸ hx) (hfront ▸ hy)).mp
  rw [hcross, hinter]
  exact mem_singleton p

/-- The endpoints of a link crossing once cannot lie in the same component of the frontier
complement. No global component count is needed. -/
theorem not_mem_connectedComponentIn_compl [T2Space ↥L]
    (h : CrossesOnce L S) (hL : IsPrimitiveLink L x y)
    (hfront : frontier U = S) (hx : x ∉ S) (hy : y ∉ S)
    (hlocal : ∀ p ∈ L ∩ S, PreconnectedSidesAt U p) :
    x ∉ connectedComponentIn Sᶜ y := by
  have hcross := h.boundaryCrossings_eq_inter hfront hlocal
  obtain ⟨p, hinter⟩ := (crossesOnce_iff_forall.mp h).1
  rw [← hfront]
  apply hL.not_mem_connectedComponentIn_compl_frontier
    (by rw [hfront]; exact hinter) (hfront ▸ hx) (hfront ▸ hy)
  rw [hcross, hinter]
  exact mem_singleton p

end Set.CrossesOnce

namespace IsPrimitiveLink

variable {X : Type*} [TopologicalSpace X] {L U : Set X} {x y p : X}

/-- Opposite endpoint sides and unique frontier contact give a single crossing, without any
assumption on the local connectedness of the region. -/
theorem crossesOnce_frontier_of_not_iff_mem [T2Space ↥L]
    (hL : IsPrimitiveLink L x y) (hinter : L ∩ frontier U = {p})
    (hx : x ∉ frontier U) (hy : y ∉ frontier U) (hxy : ¬ (x ∈ U ↔ y ∈ U)) :
    CrossesOnce L (frontier U) :=
  crossesOnce_iff.mpr ⟨p, hinter, .of_mem_boundaryCrossings Filter.EventuallyEq.rfl
    ((hL.mem_boundaryCrossings_iff_of_inter_eq_singleton hinter hx hy).mpr hxy)⟩

end IsPrimitiveLink
