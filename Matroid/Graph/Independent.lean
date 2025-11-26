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

lemma Indep_Adje (hS : G.IsIndependent S) :
    ∀ x y : α, x ∈ S → y ∈ S → x ≠ y → ¬ G.Adj x y :=
  fun _ _ hx hy ↦ hS.2 hx hy

lemma Indep_Adje_simp [G.Simple] (hS : G.IsIndependent S) :
    ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ¬ G.Adj x y := by
  intro x hx y hy
  obtain (rfl | hnee) := eq_or_ne x y
  · exact G.not_adj_self x
  · exact hS.2 hx hy hnee

@[simp]
lemma isIndependent_empty : G.IsIndependent ∅ := ⟨empty_subset _, pairwise_empty _⟩

@[simp]
lemma isIndependent_singleton : G.IsIndependent {v} ↔ v ∈ V(G) :=
  ⟨fun h => by simpa using h.1, fun h => ⟨(by simpa), pairwise_singleton ..⟩⟩

lemma Indep_le_1 [G.Simple] (hSV : S ⊆ V(G)) (hS : S.encard ≤ 1) : G.IsIndependent S := by
  obtain (rfl | ⟨v, rfl⟩) := encard_le_one_iff_eq.mp hS
  · simp
  exact ⟨hSV, pairwise_singleton ..⟩

lemma IsIndepndent_nee [G.Simple] (hSV : S ⊆ V(G)) (hS : ¬G.IsIndependent S) :
    ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
  simp only [IsIndependent, not_and, Set.Pairwise] at hS
  by_contra! hc
  exact (hS hSV) (fun a ha b hb _ ↦ hc a ha b hb)

@[simp]
lemma isIndependent_pair_iff_of_ne (h_ne : x ≠ y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.IsIndependent {x, y} ↔ ¬ G.Adj x y := by
  refine ⟨fun h ↦ (h.2 (mem_insert x {y}) (mem_insert_of_mem x rfl) h_ne), ?_⟩
  exact fun hc ↦ ⟨pair_subset hx hy, pairwise_pair.mpr fun _ ↦ ⟨hc, not_symm_not hc⟩⟩

-- lemma nee_IsIndepndent {S : Set α} {x : α} {y : α } (hai : x ∈ S) (hb : y ∈ S)
    --(hadj : G.Adj x y ) :
--     ¬ IsIndependent G S := by sorry
