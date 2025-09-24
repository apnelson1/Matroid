import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Matroid.Graph.Walk.Path
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Degree.Basic
import Matroid.Graph.Finite
import Matroid.Graph.Subgraph.Basic

-- simple is still broken
-- import Matroid.Graph.Simple

-- connectivity is still broken
-- import Matroid.Graph.Connected.Component

open WList Set

-- we will be using a lot of LEM...
open Classical

namespace Graph

variable {α β : Type*} {x y z u v : Set α} {e f : β} {G H : Graph α β}

/- Theorem 10.1.1 (Dirac 1952)
Every graph with n >= 3 vertices and minimum degree at least n/2 has a Hamiltonian cycle.
-/

-- INITIAL DEFINITIONS

lemma finite_of_ncard_nonzero {s : Set α} (h : s.ncard ≠ 0) : s.Finite := by
  by_contra hyp
  replace hyp : s.Infinite := hyp
  apply h
  exact Infinite.ncard hyp

lemma finite_of_ncard_positive {s : Set α} (h : 0 < s.ncard) : s.Finite := by
  apply finite_of_ncard_nonzero ; linarith

def NeBot (G : Graph α β) : Prop :=
  G ≠ ⊥

@[simp]
lemma NeBot_iff_vertexSet_nonempty {G : Graph α β} :
    G.NeBot ↔ V(G).Nonempty := by
  simp [NeBot]

lemma vertexSet_nonempty_of_NeBot {G : Graph α β} (h : G.NeBot) :
    V(G).Nonempty := by
  rwa [←NeBot_iff_vertexSet_nonempty]

lemma NeBot_iff_encard_positive {G : Graph α β} :
    G.NeBot ↔ 0 < V(G).encard := by
  simp

lemma NeBot_of_ncard_positive {G : Graph α β} (h : 0 < V(G).ncard) : G.NeBot := by
  rw [NeBot, ne_eq, ←vertexSet_eq_empty_iff, ←ne_eq, ←Set.nonempty_iff_ne_empty]
  apply nonempty_of_ncard_ne_zero
  linarith

def degreeSet (G : Graph α β) : Set ℕ :=
  G.degree '' V(G)

@[simp]
lemma degreeSet_eq {G : Graph α β} :
    G.degreeSet = G.degree '' V(G) := rfl

lemma degreeSet_finite_of_finite {G : Graph α β} (hFinite : G.Finite) :
    G.degreeSet.Finite := by
  simp [degreeSet]
  refine Set.Finite.image ?_ ?_
  exact vertexSet_finite

lemma degreeSet_nonempty {G : Graph α β} (hNeBot : G ≠ ⊥) : G.degreeSet.Nonempty := by
  simpa [degreeSet]

-- lemma exists_minDegreeVx (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
--     ∃ v, MinimalFor (· ∈ V(G)) G.degree v := by
--   refine Set.Finite.exists_minimalFor G.degree V(G) vertexSet_finite ?_
--   apply vertexSet_nonempty_of_NeBot; trivial

-- noncomputable def minDegreeVx (G : Graph α β) : Set α :=
--   open Classical in
--   if h : G.Finite ∧ G.NeBot then
--     Classical.choose (G.exists_minDegreeVx h.1 h.2)
--   else
--     ∅

-- G.minDegree returns the minimum degree of its vertices if G is finite, else it returns 0
noncomputable def minDegree (G : Graph α β) : ℕ :=
  open Classical in
  if h : G.Finite ∧ G.NeBot then
    Classical.choose <|
    Set.Finite.exists_minimal (degreeSet_finite_of_finite h.1) (degreeSet_nonempty h.2)
  else 0

lemma minimal_is_lower_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Minimal P x) :
    ∀ y, P y → x ≤ y := by
  intro y hy
  simp [Minimal] at h
  obtain (_|_) := le_total x y
  · assumption
  · tauto

lemma minimalFor_is_lower_bound
    {ι} [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι} (h : MinimalFor P f i) :
    ∀ j, P j → f i ≤ f j := by
  intro j hj
  simp [MinimalFor] at h
  obtain (_|_) := le_total (f i) (f j)
  · assumption
  · tauto

-- this is the price we pay for choice
@[simp]
lemma minDegree_eq (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    G.minDegree =
    (Classical.choose <|
    Set.Finite.exists_minimal
      (degreeSet_finite_of_finite hFinite)
      (degreeSet_nonempty hNeBot)) := by
  have : G.Finite ∧ G.NeBot = True := by
    simp
    refine ⟨?_, ?_⟩ <;> assumption
  simp only [minDegree]
  simp only [this, and_self, ↓reduceDIte, degreeSet_eq, mem_image]

@[simp]
lemma minDegree_eq' (G : Graph α β) (h : ¬ (G.Finite ∧ G.NeBot)) :
    G.minDegree = 0 := by
  simp [minDegree]
  tauto

lemma minDegree_spec (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    Minimal (· ∈ G.degreeSet) G.minDegree := by
  have hspec :=
    Classical.choose_spec <|
    Set.Finite.exists_minimal (degreeSet_finite_of_finite hFinite) (degreeSet_nonempty hNeBot)
  rw [minDegree_eq] <;> assumption

lemma exists_minDegreeVx (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    ∃ v ∈ V(G), G.minDegree = G.degree v := by
  have ⟨⟨v, vspec⟩, dspec⟩ := G.minDegree_spec hFinite hNeBot
  use v
  tauto

-- minDegree is indeed a lower bound
lemma minDegree_le_degree (G : Graph α β) :
    ∀ v ∈ V(G), G.minDegree ≤ G.degree v := by
  intro v hv
  obtain (p|p) := Classical.em (G.Finite ∧ G.NeBot)
  · have hspec := G.minDegree_spec p.1 p.2
    suffices h : G.degree v ∈ G.degreeSet by
      refine minimal_is_lower_bound hspec ?_ ?_
      assumption
    simp
    use v
  · simp [G.minDegree_eq' p]


-- !!!! TEMP DEFINITIONS !!!!
-- REPLACE AS SOON AS THINGS START WORKING
def Connected (G : Graph α β) : Prop := G.IsCompOf G
def Components (G : Graph α β) : Set (Graph α β) := {H | H.IsCompOf G}

@[simp]
lemma mem_components_iff_isCompOf : H ∈ G.Components ↔ H.IsCompOf G := by
  simp [Components]

@[simp]
lemma bot_notMem_components (G : Graph α β) : ⊥ ∉ G.Components := sorry

lemma components_pairwise_stronglyDisjoint (G : Graph α β) :
    G.Components.Pairwise StronglyDisjoint := sorry

lemma components_pairwise_disjoint (G : Graph α β) :
    G.Components.Pairwise Disjoint := sorry

lemma components_pairwise_compatible (G : Graph α β) : G.Components.Pairwise Compatible :=
  sorry

-- Graph is the union of its components
-- eq_sUnion_components
lemma eq_sUnion_components (G : Graph α β) : G = Graph.sUnion G.Components :=
  sorry

@[simp]
lemma components_eq_empty_iff : G.Components = ∅ ↔ G = ⊥ := sorry

-- Simple graphs
class Simple (G : Graph α β) : Prop where

lemma Simple.mono (hG : G.Simple) (hle : H ≤ G) : H.Simple := sorry

-- MORE THINGS

lemma degree_lt_vertexCount {G : Graph α β} [G.Simple] {v : Set α} (h : v ∈ V(G)) :
    G.degree v < V(G).ncard := by sorry

lemma minDegree_lt_vertexCount {G : Graph α β} [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot) :
    G.minDegree < V(G).ncard := by
  have ⟨v,vspec⟩ := G.exists_minDegreeVx hFinite hNeBot
  rw [vspec.2]
  apply degree_lt_vertexCount
  tauto

lemma minDegree_le_minDegree_of_isCompOf (G H : Graph α β) (hHG : H.IsCompOf G) :
    G.minDegree ≤ H.minDegree := by sorry

lemma ge_two_components_of_not_connected {G : Graph α β} (hNeBot : G.NeBot) (h : ¬ G.Connected) :
    2 ≤ G.Components.encard := by
  sorry

lemma finite_components_of_finite {G : Graph α β} (hFinite : G.Finite) :
  G.Components.Finite := by
  sorry

/- Step 1: WTS G is connected.
Proof: Suppose not. Then the degree of any vertex in the smallest component C of G
would be less than |C| ≤ n/2.
-/


lemma thm1_1_connected {G : Graph α β} [G.Simple] [hFinite : G.Finite]
  (hV : 3 ≤ V(G).ncard) (hDegree : V(G).ncard ≤ 2 * G.minDegree) :
  G.Connected := by
  have encard_eq_ncard : V(G).encard = ↑V(G).ncard := by
    rw [Set.Finite.cast_ncard_eq]
    exact vertexSet_finite
  have hNeBot : G.NeBot := by
    apply NeBot_of_ncard_positive
    linarith

  -- Suppose not.
  by_contra! hyp_contra

  -- There thus must be at least two components.
  have num_components_ge_2 : 2 ≤ G.Components.encard :=
    ge_two_components_of_not_connected hNeBot hyp_contra

  have components_nonempty : G.Components.Nonempty := by
    apply nonempty_of_encard_ne_zero
    intro h; rw [h] at num_components_ge_2; clear h
    have : (2 : ℕ) ≤ (0 : ℕ) := by exact ENat.coe_le_coe.mp num_components_ge_2
    linarith

  -- Choose the smallest component.
  obtain ⟨min_comp, min_comp_spec⟩ :=
    Set.Finite.exists_minimalFor
      (fun H => H.vertexSet.ncard)
      G.Components
      (finite_components_of_finite hFinite)
      components_nonempty

  -- There must be at least one other component.
  have ⟨other_comp, other_comp_spec⟩ :
    ∃ H, H.IsCompOf G ∧ H ≠ min_comp := by
    by_contra! hyp_contra
    have is_singleton : G.Components = {min_comp} := by
      exact (Nonempty.subset_singleton_iff components_nonempty).mp hyp_contra
    have : G.Components.encard = 1 := by
      simp [is_singleton]
    rw [this] at num_components_ge_2; clear this
    have : (2 : ℕ) ≤ (1 : ℕ) := by exact ENat.coe_le_coe.mp num_components_ge_2
    linarith

  -- G, min_comp, other_comp have finite vertexSets
  have G_finite_vertexSet : V(G).Finite := vertexSet_finite
  have min_comp_finite_vertexSet : V(min_comp).Finite := by
    suffices min_comp.Finite by exact vertexSet_finite
    exact Finite.mono hFinite min_comp_spec.1.le
  have other_comp_finite_vertexSet : V(other_comp).Finite := by
    suffices other_comp.Finite by exact vertexSet_finite
    exact Finite.mono hFinite other_comp_spec.1.le

  -- other_comp has at least as many vertices as min_comp
  have other_comp_larger : V(min_comp).ncard ≤ V(other_comp).ncard := by
    refine minimalFor_is_lower_bound (fun H : Graph α β => H.vertexSet.ncard) min_comp_spec ?_ ?_
    simp
    exact other_comp_spec.1
  -- min_comp and other_comp have disjoint vertex sets
  have disjoint_vx_sets : Disjoint V(min_comp) V(other_comp) := by
    suffices StronglyDisjoint min_comp other_comp by
      exact this.vertex
    apply G.components_pairwise_stronglyDisjoint <;> try tauto
    exact min_comp_spec.1

  have G_vertexSet_is_superset : V(min_comp) ∪ V(other_comp) ⊆ V(G) := by
    -- !!! TODO
    have pairwise_dup_agree : G.Components.Pairwise Dup_agree := by sorry
    have h_sUnion := sUnion_vertexSet pairwise_dup_agree
    rw [←G.eq_sUnion_components] at h_sUnion
    rw [h_sUnion, union_subset_iff]
    constructor <;> refine subset_biUnion_of_mem ?_
    · exact min_comp_spec.1
    · exact other_comp_spec.1

  have G_ncard_ge_sum : V(min_comp).ncard + V(other_comp).ncard ≤ V(G).ncard := by
    have : V(min_comp).ncard + V(other_comp).ncard = (V(min_comp) ∪ V(other_comp)).ncard := by
      exact Eq.symm
        (ncard_union_eq disjoint_vx_sets min_comp_finite_vertexSet other_comp_finite_vertexSet)
    rw [this]; clear this
    refine ncard_le_ncard ?_ ?_ <;> assumption

  -- so |min_comp| ≤ n/2
  replace G_ncard_ge_sum : 2 * V(min_comp).ncard ≤ V(G).ncard := by
    linarith

  -- some manipulations left over
  have hle : V(min_comp).ncard ≤ G.minDegree := by linarith
  have hle2 : G.minDegree ≤ min_comp.minDegree := by
    apply minDegree_le_minDegree_of_isCompOf
    rw [←mem_components_iff_isCompOf]
    exact min_comp_spec.1
  replace hle : V(min_comp).ncard ≤ min_comp.minDegree := by linarith
  have hlt : min_comp.minDegree < V(min_comp).ncard := by
    have min_comp_simple : min_comp.Simple := sorry
    refine minDegree_lt_vertexCount ?_ ?_
    · exact Finite.mono hFinite min_comp_spec.1.le
    · rw [NeBot_iff_vertexSet_nonempty]
      exact min_comp_spec.1.nonempty

  linarith

def pathSet (G : Graph α β) := {p | IsPath G p}

lemma pathSet_finite (G : Graph α β) [G.Simple] (hFinite : G.Finite) :
    G.pathSet.Finite := by
  sorry

lemma pathSet_nonempty (G : Graph α β) (hNeBot : G.NeBot) :
    G.pathSet.Nonempty := by
  sorry

def IsLongestPath (G : Graph α β) (p : WList (Set α) β) :=
  MaximalFor (· ∈ G.pathSet) (fun w => w.length) p

lemma exists_longest_path
    (G : Graph α β) [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot) :
    ∃ p, G.IsLongestPath p :=
  Set.Finite.exists_maximalFor _ _ (G.pathSet_finite hFinite) (G.pathSet_nonempty hNeBot)

-- by maximality, each neighbour of is on the path
lemma first_neighbors_mem_path
    (G : Graph α β) [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot)
    {P : WList (Set α) β} (hP : G.IsLongestPath P)
    (x : Set α) (hx : G.Adj x P.first) :
    x ∈ P := by
  sorry

-- similarly, the same statement but reverse in direction
lemma last_neighbors_mem_path
    (G : Graph α β) [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot)
    {P : WList (Set α) β} (hP : G.IsLongestPath P)
    (x : Set α) (hx : G.Adj x P.last) :
    x ∈ P := by
  sorry

lemma exists_left_edge
    (w : WList α β) {x : α} (hxw : x ∈ w) (hx : x ≠ w.first) :
    ∃ e y, w.DInc e y x := by
  sorry
