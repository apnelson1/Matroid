import Matroid.Axioms.Circuit
import Matroid.Graph.Tree

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C w P Q : WList α β}

open Set

namespace Graph

def IsCycleSet (G : Graph α β) (C : Set β) : Prop := ∃ C₀, G.IsCycle C₀ ∧ C₀.E = C

def IsAyclicSet (G : Graph α β) (I : Set β) : Prop := I ⊆ G.E ∧ ∀ C₀, G.IsCycle C₀ → ¬ (C₀.E ⊆ I)

/-- The cycle matroid of a graph `G`. Its circuits are the edge sets of cycles of `G`,
and its independent sets are the edge sets of forests. -/
def cycleMatroid (G : Graph α β) : Matroid β :=
  FiniteCircuitMatroid.matroid <| FiniteCircuitMatroid.mk
    (E := G.E)
    (IsCircuit := G.IsCycleSet)
    (by
      simp only [IsCycleSet, not_exists, not_and]
      exact fun C hC hCe ↦ by simpa [hCe] using hC.nonempty.edgeSet_nonempty )
    (by
      rintro _ ⟨C₁, hC₁, rfl⟩ _ ⟨C₂, hC₂, rfl⟩ hne (hss : C₁.E ⊆ C₂.E)
      have h_eq := hC₂.toGraph_eq_of_le hC₁ <|
        hC₁.isWalk.le_of_edgeSet_subset hC₁.nonempty hC₂.isWalk hss
      exact hne <| by simpa using congrArg Graph.E h_eq )
    (by
      rintro _ _ e ⟨C₁, hC₁, rfl⟩ ⟨C₂, hC₂, rfl⟩ hne he₁ he₂
      obtain ⟨x, y, hxy₁⟩ := C₁.exists_inc₂_of_mem_edge he₁
      have hxy₂ := (hC₁.isWalk.inc₂_iff_inc₂_of_mem he₁).1 hxy₁
      rw [← hC₂.isWalk.inc₂_iff_inc₂_of_mem he₂] at hxy₂
      obtain ⟨P₁, hP₁, hP₁C₁, hx₁, hy₁⟩ := hC₁.exists_isPath_toGraph_eq_delete_edge_of_inc₂ hxy₁
      obtain ⟨P₂, hP₂, hP₂C₂, hx₂, hy₂⟩ := hC₂.exists_isPath_toGraph_eq_delete_edge_of_inc₂ hxy₂
      by_cases h_eq : P₁ = P₂
      · apply_fun (fun P ↦ insert e P.E) at h_eq
        simp [← P₁.toGraph_edgeSet, ← P₂.toGraph_edgeSet, hP₁C₁, hP₂C₂, edgeDelete_edgeSet,
          WList.toGraph_edgeSet, Set.insert_eq_of_mem he₁, Set.insert_eq_of_mem he₂, hne] at h_eq
      obtain ⟨C, hC, hCE⟩ := twoPaths hP₁ hP₂ h_eq (by rw [hx₁, hx₂]) (by rw [hy₁, hy₂])
      have hss : C.E ⊆ (C₁.E ∪ C₂.E) \ {e} := by
        apply_fun Graph.E at hP₁C₁ hP₂C₂
        simp only [WList.toGraph_edgeSet, edgeDelete_edgeSet] at hP₁C₁ hP₂C₂
        rwa [union_diff_distrib, ← hP₁C₁, ← hP₂C₂]
      refine ⟨C.E, ⟨C, hC, rfl⟩, not_mem_subset hss (by simp), fun x hx ↦ ?_⟩
      simpa using (hss.trans diff_subset) hx )
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact C.edgeSet_finite )
    (by
      rintro _ ⟨C, hC, rfl⟩
      simpa using edgeSet_subset_of_le hC.isWalk.toGraph_le )

@[simp]
lemma cycleMatroid_isCircuit_iff {C : Set β} : G.cycleMatroid.IsCircuit C ↔ G.IsCycleSet C := by
  simp [cycleMatroid]

@[simp]
lemma cycleMatroid_indep_iff {I : Set β} : G.cycleMatroid.Indep I ↔ G.IsAyclicSet I := by
  simp only [cycleMatroid, FiniteCircuitMatroid.matroid_indep_iff, IsCycleSet, IsAyclicSet]
  aesop
