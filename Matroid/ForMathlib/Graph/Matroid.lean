import Matroid.Axioms.Circuit
import Matroid.ForMathlib.Graph.Tree

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C w P Q : WList α β}

namespace Graph

def IsCycleSet (G : Graph α β) (C : Set β) : Prop := ∃ C₀, G.IsCycle C₀ ∧ C₀.E = C

def IsAyclicSet (G : Graph α β) (I : Set β) : Prop := ∀ C₀, G.IsCycle C₀ → ¬ (C₀.E ⊆ I)

protected def matroid [DecidableEq β] (G : Graph α β) : Matroid β :=
  FinsetCircuitMatroid.matroid <| FinsetCircuitMatroid.ofFinite G.E G.IsCycleSet
    (by
      simp only [IsCycleSet, not_exists, not_and]
      exact fun C hC hCe ↦ by simpa [hCe] using hC.nonempty.edgeSet_nonempty )
    (by
      -- antichain
      sorry
    )
    (by
      rintro _ _ e ⟨C₁, hC₁, rfl⟩ ⟨C₂, hC₂, rfl⟩ hne he₁ he₂
      sorry
      -- two paths
    )
    sorry
    sorry
    sorry
    sorry
