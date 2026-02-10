import Matroid.Axioms.Circuit
import Matroid.Minor.Contract
import Matroid.Graph.Forest
import Matroid.Graph.Minor.Conn

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C w P Q : WList α β}

open Set WList Matroid

namespace Graph

/-- The cycle matroid of a graph `G`. Its circuits are the edge sets of cycles of `G`,
and its independent sets are the edge sets of forests. -/
@[simps! E]
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
      refine ⟨E(C), ⟨C, hC, rfl⟩, notMem_subset hss (by simp), fun x hx ↦ ?_⟩
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

-- @[simp]
-- lemma cycleMatroid_isCocircuit : G.cycleMatroid.IsCocircuit = G.IsBond := by
--   ext F
--   rw?

@[simp]
lemma cycleMatroid_edgeRestrict (G : Graph α β) (F : Set β) :
    (G ↾ F).cycleMatroid = G.cycleMatroid ↾ (E(G) ∩ F) := by
  refine ext_isCircuit rfl fun I hI ↦ ?_
  obtain ⟨hI, hIF⟩ := by simpa using hI
  simp [restrict_isCircuit_iff, hI, hIF]

@[simp]
lemma cycleMatroid_edgeDelete (G : Graph α β) (F : Set β) :
    (G ＼ F).cycleMatroid = G.cycleMatroid ＼ F :=
  ext_isCircuit rfl fun I hI ↦ by simp

-- lemma cycleMatroid_contract {φ} (hφ : H.connPartition.IsRepFun φ) (hHG : H ≤ G) :
--     (G /[φ, E(H)]).cycleMatroid = G.cycleMatroid ／ E(H) := by
--   refine ext_indep rfl fun I hI ↦ ?_
--   simp only [cycleMatroid_E, contract_edgeSet, cycleMatroid_indep, isAcyclicSet_iff] at hI ⊢
--   refine ⟨fun ⟨_, h⟩ => ?_, fun h => ?_⟩
--   · rw [contract_edgeRestrict_comm] at h

@[simp]
lemma cycleMatroid_vertexDelete_isolatedSet (G : Graph α β) :
    (G - I(G)).cycleMatroid = G.cycleMatroid := by
  refine ext_isCircuit ?_ fun I hI ↦ ?_
  · rw [cycleMatroid_E, cycleMatroid_E, vertexDelete_edgeSet_diff, setincEdges_isolatedSet,
      diff_empty]
  rw [cycleMatroid_isCircuit, cycleMatroid_isCircuit]
  refine ⟨fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_), fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_)⟩
  · exact hxy.1
  simp [hxy, hxy.left_not_isolated, hxy.right_not_isolated]

lemma cycleMatroid_isRestriction_of_isLink (hl : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y) :
    G.cycleMatroid ≤r H.cycleMatroid := by
  have hsu : E(G) ⊆ E(H) := by
    intro e he
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact (hl hxy).edge_mem
  use E(G), hsu, ext_isCircuit rfl fun I hI ↦ ?_
  rw [← inter_eq_right.mpr hsu, ← cycleMatroid_edgeRestrict]
  simp only [cycleMatroid_isCircuit]
  refine ⟨fun h ↦ h.of_isLink (fun e x y hxy ↦ (hl hxy).of_le_of_mem edgeRestrict_le ?_),
    fun h ↦ h.of_isLink (fun e x y hxy ↦ ?_)⟩
  · simp [hxy.edge_mem, (hl hxy).edge_mem]
  obtain ⟨-, he⟩ := by simpa using hxy.edge_mem
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl huv |>.eq_and_eq_or_eq_and_eq (hxy.of_le edgeRestrict_le)
  · exact huv
  exact huv.symm

lemma cycleMatroid_isRestriction_of_le (h : G ≤ H) : G.cycleMatroid ≤r H.cycleMatroid :=
  cycleMatroid_isRestriction_of_isLink h.2
