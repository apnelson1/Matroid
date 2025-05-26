import Matroid.Graph.Simple
import Matroid.Graph.Connected

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}

open Set WList

namespace Graph

/-! ### Paths -/

def IsPathGraph (G : Graph α β) : Prop := ∃ P, G.IsPath P ∧ E(P) = E(G) ∧ V(P) = V(G)
  -- ∃ P : WList α β, P.WellFormed ∧ P.vertex.Nodup ∧ G = P.toGraph

lemma IsPathGraph.exists_eq_toGraph (hG : G.IsPathGraph) :
    ∃ P : WList α β, P.WellFormed ∧ P.vertex.Nodup ∧ G = P.toGraph := by
  obtain ⟨P, hP, hE, hV⟩ := hG
  exact ⟨P, hP.isWalk.wellFormed, hP.nodup,
    G.ext_of_le_le le_rfl hP.isWalk.toGraph_le (by simpa using hV.symm) (by simpa using hE.symm)⟩


lemma Connected.isPathGraph_of_degree {G : Graph α β} {v : α} [G.Finite] (hG : G.Connected)
    (hvG : v ∈ V(G)) (hv : G.degree v ≤ 1) (hdeg : ∀ x ∈ V(G), G.degree x ≤ 2) : G.IsPathGraph := by
  obtain hss | hnt := V(G).subsingleton_or_nontrivial
  · have h_eq := hss.eq_singleton_of_mem hvG
    refine ⟨WList.nil v, by simpa, ?_, by simp [h_eq]⟩
    rw [nil_edgeSet, eq_comm, eq_empty_iff_forall_not_mem]
    refine fun e he ↦ ?_
    obtain ⟨x₁, x₂, he⟩ := exists_isLink_of_mem_edgeSet he
    rw [show x₁ = v by simpa [h_eq] using he.left_mem,
      show x₂ = v by simpa [h_eq] using he.right_mem, isLink_self_iff] at he
    linarith [he.two_le_degree]
  have hleaf : G.IsLeaf v :=
    degree_eq_one_iff.1 <| ((hG.minDegreePos hnt).one_le_degree hvG).antisymm' hv



  have hconn := hleaf.delete_connected hG
  obtain ⟨e, he⟩ := hleaf
  obtain ⟨x, hne, hvx⟩ := he.isNonloopAt
  obtain ⟨y, hyV, hevy, hne, hemem, h_eq⟩ := he.eq_addEdge
  have hdel := encard_delete_vertex_lt hvG
  have hleaf : (G - {v}).degree y ≤ 1 := by
    have hdeg' := (G - {v}).degree_addEdge_right hemem hne.symm
    rw [← h_eq] at hdeg'
    linarith [hdeg y hyV]
  obtain ⟨Q, hQ, hQE, hQV⟩ := hconn.isPathGraph_of_degree (v := y) sorry hleaf sorry
  sorry

  -- sorry
termination_by V(G).encard
    -- rw [← h_eq] at hdeg'
    -- rw [← degree_eq_one_iff, le_antisymm_iff, hconn.minDegreePos.one_le_degree]



  -- have IH := hconn.isPathGraph_of_isLeaf_of_degree_le_two (v := y)


  -- obtain ⟨y, hy⟩ := hG.exists_delete_vertex_connected hv₀.vertexSet_nontrivial

  -- have hnt := hv₀.vertexSet_nontrivial
