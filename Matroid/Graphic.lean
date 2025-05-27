import Matroid.Axioms.Circuit
import Matroid.Graph.Forest

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C w P Q : WList α β}

open Set WList

namespace Graph

/-- The cycle matroid of a graph `G`. Its circuits are the edge sets of cycles of `G`,
and its independent sets are the edge sets of forests. -/
def cycleMatroid (G : Graph α β) : Matroid β :=
  FiniteCircuitMatroid.matroid <| FiniteCircuitMatroid.mk
    (E := E(G))
    (IsCircuit := G.IsCycleSet)
    (by
      simp only [IsCycleSet, not_exists, not_and]
      exact fun C hC hCe ↦ by simpa [hCe] using hC.nonempty.edgeSet_nonempty )
    (by
      rintro _ ⟨C₁, hC₁, rfl⟩ _ ⟨C₂, hC₂, rfl⟩ hne (hss : E(C₁) ⊆ E(C₂))
      have h_eq := hC₂.toGraph_eq_of_le hC₁ <|
        hC₁.isWalk.le_of_edgeSet_subset hC₁.nonempty hC₂.isWalk hss
      exact hne <| by simpa using congrArg Graph.edgeSet h_eq )
    (by
      rintro _ _ e ⟨C₁, hC₁, rfl⟩ ⟨C₂, hC₂, rfl⟩ hne he₁ he₂
      obtain ⟨x, y, hxy₁⟩ := C₁.exists_isLink_of_mem_edge he₁
      have hxy₂ := (hC₁.isWalk.isLink_iff_isLink_of_mem he₁).1 hxy₁
      rw [← hC₂.isWalk.isLink_iff_isLink_of_mem he₂] at hxy₂
      obtain ⟨P₁, hP₁, hP₁C₁, hx₁, hy₁⟩ := hC₁.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy₁
      obtain ⟨P₂, hP₂, hP₂C₂, hx₂, hy₂⟩ := hC₂.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy₂
      by_cases h_eq : P₁ = P₂
      · apply_fun (fun P : WList α β ↦ insert e E(P)) at h_eq
        simp [← P₁.toGraph_edgeSet, ← P₂.toGraph_edgeSet, hP₁C₁, hP₂C₂, edgeDelete_edgeSet,
          WList.toGraph_edgeSet, Set.insert_eq_of_mem he₁, Set.insert_eq_of_mem he₂, hne] at h_eq
      obtain ⟨C, hC, hCE⟩ := twoPaths hP₁ hP₂ h_eq (by rw [hx₁, hx₂]) (by rw [hy₁, hy₂])
      have hss : E(C) ⊆ (E(C₁) ∪ E(C₂)) \ {e} := by
        apply_fun Graph.edgeSet at hP₁C₁ hP₂C₂
        simp only [WList.toGraph_edgeSet, edgeDelete_edgeSet] at hP₁C₁ hP₂C₂
        rwa [union_diff_distrib, ← hP₁C₁, ← hP₂C₂]
      refine ⟨E(C), ⟨C, hC, rfl⟩, not_mem_subset hss (by simp), fun x hx ↦ ?_⟩
      simpa using (hss.trans diff_subset) hx )
    (by
      rintro _ ⟨C, hC, rfl⟩
      exact C.edgeSet_finite )
    (by
      rintro _ ⟨C, hC, rfl⟩
      simpa using edgeSet_mono hC.isWalk.toGraph_le )

@[simp]
lemma cycleMatroid_isCircuit : G.cycleMatroid.IsCircuit = G.IsCycleSet := by
  simp [cycleMatroid]

@[simp]
lemma cycleMatroid_indep : G.cycleMatroid.Indep = G.IsAcyclicSet := by
  ext I
  simp only [cycleMatroid, FiniteCircuitMatroid.matroid_indep_iff, IsCycleSet, IsAcyclicSet]
  aesop
