module

import Matroid.GraphLike.Restriction
import Matroid.GraphLike.Assembly

open Set Topology Set.Notation
open scoped GraphLike

namespace GraphLikeRestrictionTests

/-- An infinite graph-like space consisting entirely of isolated vertices. -/
def discreteVertices : GraphLike ℕ where
  carrier := univ
  vertexSet := univ
  t2Space := inferInstance
  subset := Subset.rfl
  isClosed := by simp
  isTotallySeparated := by
    simpa using TotallySeparatedSpace.isTotallySeparated_univ (α := ↥(univ : Set ℕ))
  interior_isOpen' := by
    intro e
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
    exact False.elim (x.2.2 (mem_univ _))
  boundary_isPair' := by
    intro e
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
    exact False.elim (x.2.2 (mem_univ _))

example : (discreteVertices.restrict univ ∅).carrier = univ := by
  simp [GraphLike.support, discreteVertices]

example : ¬ (discreteVertices.restrict univ ∅).Finite := by
  rw [GraphLike.restrict_finite_iff]
  intro h
  have hf : (univ : Set ℕ).Finite := by
    simpa [discreteVertices] using h.1
  exact Set.infinite_univ hf

example (v : ℕ) :
    (discreteVertices.restrict {v} ∅).carrier = {v} := by
  simp [GraphLike.support, discreteVertices]

/-- Assemble a concrete nondegenerate interval with one component edge. -/
private theorem interval_edge :
    ∃ (G : GraphLike ℝ) (e : Set ℝ), e ∈ E(G) ∧ e = segment ℝ (0 : ℝ) 1 := by
  let Z : Set ℝ := {0, 1}
  let a (_ : Unit) : Z := ⟨0, by simp [Z]⟩
  let b (_ : Unit) : Z := ⟨1, by simp [Z]⟩
  let q := GraphLike.ofFiniteLinksEdgeEquiv Z
    ((finite_singleton 1).insert 0) a b (fun _ : Unit ↦ segment ℝ (0 : ℝ) 1)
    (fun _ ↦ isPrimitiveLink_segment (by norm_num))
    (fun _ ↦ by
      apply inter_eq_right.mpr
      intro x hx
      rcases hx with rfl | hx
      · exact left_mem_segment ℝ _ _
      · have : x = 1 := hx
        subst x
        exact right_mem_segment ℝ _ _)
    (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
  exact ⟨_, (q ()).1, (q ()).2, GraphLike.ofFiniteLinksEdgeEquiv_coe ..⟩

/-- Removing both endpoints of a retained interval restores them under relative closure. -/
example : ∃ (G : GraphLike ℝ) (e : Set ℝ), e ∈ E(G) ∧
    G.carrier ∩ closure (G.support ∅ {e} \ G.support univ ∅) =
      segment ℝ (0 : ℝ) 1 := by
  obtain ⟨G, e, he, hr⟩ := interval_edge
  refine ⟨G, e, he, ?_⟩
  rw [G.closure_support_sdiff ∅ univ {e} ∅ finite_empty (finite_singleton e)]
  simpa [GraphLike.support, he] using hr

section General

variable {X : Type*} [TopologicalSpace X] (G : GraphLike X)

example : (G.restrict ∅ ∅).carrier = ∅ := by simp

example (e : Set X) (he : e ∈ E(G)) : E(G.restrict ∅ {e}) = {e} := by
  simp [he]

/-- A loop retains its coincident boundary vertex. -/
example (e : Set X) (he : e ∈ E(G)) (v : X) (h : G.edgeBoundary e = {v}) :
    (G.restrict ∅ {e}).edgeBoundary e = {v} := by
  simpa only [G.restrict_edgeBoundary ∅ {e} he (mem_singleton e)] using h

/-- Parallel edges are retained as the same distinct point sets. -/
example (e f : Set X) (he : e ∈ E(G)) (hf : f ∈ E(G)) (hne : e ≠ f)
    (_hb : G.edgeBoundary e = G.edgeBoundary f) :
    e ∈ E(G.restrict ∅ {e, f}) ∧ f ∈ E(G.restrict ∅ {e, f}) ∧ e ≠ f := by
  simp [he, hf, hne]

/-- Two retained edges can share a vertex in their support intersection. -/
example (e f : Set X) (he : e ∈ E(G)) (hf : f ∈ E(G)) (v : X)
    (hv : v ∈ G.edgeBoundary e) (hw : v ∈ G.edgeBoundary f) :
    v ∈ G.support ∅ {e} ∩ G.support ∅ {f} := by
  exact ⟨G.edge_subset_support ∅ {e} he (mem_singleton e) hv.1,
    G.edge_subset_support ∅ {f} hf (mem_singleton f) hw.1⟩

example (A C : Set X) (B D : Set (Set X)) :
    (G.restrict A B).restrict C D =
      G.restrict (C ∩ V(G.restrict A B)) (D ∩ E(G.restrict A B)) :=
  G.restrict_restrict A B C D

/-- The deleted selection can be infinite; no ambient separation instance is supplied. -/
example (A C : Set X) (B D : Set (Set X)) (hA : A.Finite) (hB : B.Finite) :
    G.carrier ∩ closure (G.support A B \ G.support C D) =
      G.support (A \ G.support C D) (B \ D) :=
  G.closure_support_sdiff A C B D hA hB

/-- Arbitrary selections are normalized, including nonedges and nonvertices. -/
example (A : Set X) (B : Set (Set X)) :
    G.support (A \ V(G)) (B \ E(G)) = ∅ := by
  simp [GraphLike.support]

example (A : Set X) (B : Set (Set X)) :
    (G.restrict A B).Finite ↔ (A ∩ V(G)).Finite ∧ (B ∩ E(G)).Finite :=
  G.restrict_finite_iff A B

end General

end GraphLikeRestrictionTests

/-- info: 'GraphLike.restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.restrict
/-- info: 'GraphLike.restrict_edgeSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.restrict_edgeSet
/-- info: 'GraphLike.restrict_finite_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.restrict_finite_iff
/-- info: 'GraphLike.restrict_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.restrict_restrict
/-- info: 'GraphLike.closure_support_sdiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.closure_support_sdiff
