import Matroid.Graph.Simple
import Matroid.Graph.WList.Sublist
import Matroid.Graph.Subgraph.Delete


/-
This file defined predicates stating that an abstract walk `w` is a walk/trail/path of a graph `G`.
-/

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {A : Set β}
  {W w w₁ w₂ : WList α β} {S T : Set α}

open Graph WList Set

namespace Graph

def IsIndependent (G : Graph α β) (S : Set α) : Prop :=
  S ⊆ V(G) ∧ S.Pairwise (fun x y ↦ ¬ G.Adj x y)

def IndepNumLE (G : Graph α β) (n : ℕ∞) : Prop :=
  ∀ S, G.IsIndependent S → S.encard ≤ n

def IsMaxIndependent (G : Graph α β) (S : Set α) : Prop :=
  IsIndependent G S ∧ (∀ A, IsIndependent G A → A.encard ≤ S.encard )

lemma Indep_Adje {G : Graph α β } {S : Set α} (hS : G.IsIndependent S) :
    ∀ x y : α, x ∈ S → y ∈ S → x ≠ y → ¬ G.Adj x y := by
  exact fun x y hx hy hxy ↦ hS.2 hx hy hxy

lemma Indep_Adje_simp {G : Graph α β } {S : Set α} [G.Simple] (hS : G.IsIndependent S) :
    ∀ x y : α, x ∈ S → y ∈ S → ¬ G.Adj x y := by
  intro x y hx hy
  obtain (h_eq | hnee ) := eq_or_ne x y
  rw [h_eq]
  exact not_adj_self G y
  exact Indep_Adje hS x y hx hy hnee

lemma Indep_le_1 {G : Graph α β } {S : Set α} [G.Simple] (hSV : S ⊆ V(G)) (hS : S.encard ≤ 1) :
    G.IsIndependent S := by
  obtain (h0 | h1 ) := Decidable.em (S.encard = 1 )
  · have ⟨v, hvS ⟩: ∃ v, S = {v} := by exact encard_eq_one.mp h0
    refine ⟨ hSV, ?_ ⟩
    rw[ hvS ]
    simp
  rw [encard_eq_one] at h1
  rw [Set.encard_le_one_iff_eq] at hS
  obtain ( ha | hb ) := hS
  · rw [ha]
    refine ⟨ empty_subset V(G) , (pairwise_empty fun x y ↦ ¬G.Adj x y ) ⟩
  by_contra
  exact h1 hb

lemma IsIndepndent_nee {G : Graph α β } {S : Set α} [G.Simple] (hSV : S ⊆ V(G))
    (hS : ¬G.IsIndependent S) :
    ∃ u v : α, u ∈ S ∧ v ∈ S ∧ G.Adj u v := by
  obtain (h1 | h2 ) := Decidable.em (S.encard ≤ 1 )
  · by_contra hc
    exact hS (Indep_le_1 hSV h1 )
  unfold IsIndependent at hS
  simp at hS
  by_contra hc
  simp at hc
  simp at h2
  exact (hS hSV) (fun a ha b hb hab ↦ hc a ha b hb )

lemma isIndependent_pair_iff_of_ne (h_ne : x ≠ y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.IsIndependent {x, y} ↔ ¬ G.Adj x y := by
  set ind : Set α := {x,y} with h_ind
  refine ⟨ fun h ↦ (Indep_Adje h x y (mem_insert x {y} ) (mem_insert_of_mem x rfl) h_ne ), ?_ ⟩
  intro hc
  refine ⟨ ?_, ?_ ⟩
  refine pair_subset hx hy
  refine pairwise_pair.mpr ?_
  intro hh
  refine ⟨ hc, ?_ ⟩
  --Betty, instead of contradiction we can just rw an if and only if
  rwa [adj_comm]
