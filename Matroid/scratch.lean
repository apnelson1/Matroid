import Mathlib.Combinatorics.Graph.Basic
import Matroid.Graph.Degree.Max
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Constructions.Basic

open Set Graph

namespace Graph

variable {α β : Type} {G : Graph α β}

@[mk_iff]
structure IsGammaColouring (γ : Type) (G : Graph α β) (c : α → γ) : Prop where
  adj_colouring : ∀ x y, G.Adj x y → c x ≠ c y

@[mk_iff]
structure IsGammaKColouring (γ : Type) (G : Graph α β) (c : α → γ) (k : ℕ) : Prop where
  is_colouring : IsGammaColouring γ G c
  le_k_colours : (c '' V(G)).encard ≤ k

def IsKColourable (G : Graph α β) (k : ℕ) := ∃ γ : Type, ∃ c : α → γ, IsGammaKColouring γ G c k

theorem n_vertices_of_n_colourable (G : Graph α β) (hl : G.Loopless) (n : ℕ)
    (hn : V(G).encard ≤ n) : IsKColourable G n := by
  rw [loopless_iff_forall_ne_of_adj] at hl
  let c : α → α := fun v ↦ v
  have h₁ : ∀ x y, G.Adj x y → c x ≠ c y := by
    intro x y ha
    specialize hl x y
    apply hl at ha
    unfold c
    exact ha
  have h₂ : (c '' V(G)).encard ≤ n := by
    sorry
  have h₃ : IsGammaKColouring α G c n := by
    sorry
  unfold IsKColourable
  use α
  use c
