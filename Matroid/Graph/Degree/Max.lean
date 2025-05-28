import Matroid.Graph.Degree.Leaf
import Matroid.Graph.Connected
import Matroid.Graph.Small

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}
{d : ℕ}

open Set WList

namespace Graph



/-! ### Maximum degree -/

/-- `G.MaxDegreeLE d` means that `G` has maximum degree at most `d`.  -/
def MaxDegreeLE (G : Graph α β) (d : ℕ) : Prop := ∀ v, G.eDegree v ≤ d

lemma MaxDegreeLE.degree_le (h : G.MaxDegreeLE d) (v : α) : G.degree v ≤ d :=
  ENat.toNat_le_of_le_coe (h v)

lemma MaxDegreeLE.mono (h : G.MaxDegreeLE d) (hle : H ≤ G) : H.MaxDegreeLE d :=
  fun v ↦ (eDegree_mono hle _).trans <| h v

lemma MaxDegreeLE.locallyFinite (h : G.MaxDegreeLE d) : G.LocallyFinite where
  finite x := finite_of_encard_le_coe <| (G.encard_setOf_inc_le_eDegree x).trans (h x)

-- lemma foo (hG : G.Connected) (h : G.MaxDegreeLE 2) {C : WList α β} (hC : G.IsCycle C) :
--     G = C.toGraph := by
--   refine le_antisymm ?_ hC.isWalk.toGraph_le
--   sorry



/-- A nontrivial connected graph with max degree at most two is loopless. -/
lemma Connected.loopless_of_maxDegreeLE_two (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
    (hnt : V(G).Nontrivial) : G.Loopless where
  not_isLoopAt e x h := by
    have := hmax.locallyFinite
    obtain ⟨f, y, hf, hne⟩ := hG.exists_isLink_of_mem hnt h.vertex_mem
    have hle := hmax.degree_le x
    have h1 : 1 ≤ {e | G.IsLoopAt e x}.ncard :=
      Nat.one_le_iff_ne_zero.2 <| ncard_ne_zero_of_mem h G.finite_setOf_isLoopAt
    have h2 : 1 ≤ {e | G.IsNonloopAt e x}.ncard :=
      Nat.one_le_iff_ne_zero.2 <| ncard_ne_zero_of_mem ⟨y, hne, hf⟩ G.finite_setOf_isNonloopAt
    rw [degree_eq_ncard_add_ncard] at hle
    linarith

-- lemma Connected.simple_of_maxDegreeLE_two (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
--     (hcard : 3 ≤ V(G).encard) : G.Simple := by
--   sorry

/-! ### Paths -/

def IsPathGraph (G : Graph α β) : Prop := ∃ P, G.IsPath P ∧ E(P) = E(G) ∧ V(P) = V(G)
  -- ∃ P : WList α β, P.WellFormed ∧ P.vertex.Nodup ∧ G = P.toGraph

lemma IsPathGraph.exists_eq_toGraph (hG : G.IsPathGraph) :
    ∃ P : WList α β, P.WellFormed ∧ P.vertex.Nodup ∧ G = P.toGraph := by
  obtain ⟨P, hP, hE, hV⟩ := hG
  exact ⟨P, hP.isWalk.wellFormed, hP.nodup,
    G.ext_of_le_le le_rfl hP.isWalk.toGraph_le (by simpa using hV.symm) (by simpa using hE.symm)⟩

lemma MaxDegreeLE.eq_path_aux {G : Graph α β} {v : α} [G.Finite] (hG : G.MaxDegreeLE 2)
    (hG : G.Connected) (hv : G.IsLeaf v) :
    ∃ P, G.IsPath P ∧ V(P) = V(G) ∧ E(P) = E(G) ∧ P.first = v := by
  have hnt := hv.vertexSet_nontrivial
  have hconn := hv.delete_connected hG
  obtain ⟨e,he⟩ := hv
  obtain ⟨y, hyv, hevy⟩ := he.isNonloopAt
  have hyG : y ∈ V(G - {v}) := by simp [hevy.right_mem, hyv]
  obtain hs | hnt' := eq_singleton_or_nontrivial hyG
  · refine ⟨cons v e (nil y), ?_⟩
    suffices h : {v, y} = V(G) ∧ {e} = E(G) by simpa [hevy.right_mem, hevy, hyv.symm]
    rw [← insert_eq_of_mem hevy.left_mem, ← insert_diff_singleton (s := V(G)),
      ← vertexDelete_vertexSet, hs, and_iff_right rfl, subset_antisymm_iff,
      and_iff_right (by simpa using hevy.edge_mem)]

    refine fun f h ↦ he.edge_unique <| by_contra fun hcon ↦ ?_

    obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h
    obtain rfl | hne := eq_or_ne z v
    · exact hzw.inc_left

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
