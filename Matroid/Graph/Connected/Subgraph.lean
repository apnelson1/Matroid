import Matroid.Graph.Connected.Basic
import Matroid.Graph.Connected.Vertex.Basic

open Set Function Nat WList symmDiff

variable {α β : Type*} {G G₁ G₂ H H₁ H₂ : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R' B : Set β} {C W P Q : WList α β}

namespace Graph

/-! ### Staying Connected -/

/-- A leaf vertex in a trail is either the first or last vertex of the trail -/
lemma IsLeaf.eq_first_or_eq_last_of_mem_trail {P : WList α β} (hx : G.IsLeaf x)
    (hP : G.IsTrail P) (hxP : x ∈ P) : x = P.first ∨ x = P.last := by
  induction P with
  | nil => simpa using hxP
  | cons u e P ih =>
    simp only [cons_isTrail_iff] at hP
    obtain (rfl : x = u) | (hxP : x ∈ P) := by simpa using hxP
    · simp
    obtain rfl | rfl := (ih hP.1 hxP).symm
    · simp
    obtain v | ⟨v, f, P⟩ := P
    · simp
    simp only [cons_isTrail_iff, first_cons, cons_edge, List.mem_cons, not_or] at hP
    simp [hx.eq_of_inc_inc hP.1.2.1.inc_left hP.2.1.inc_right] at hP

lemma IsLeaf.eq_first_or_eq_last_of_mem_path {P : WList α β} (hx : G.IsLeaf x)
    (hP : G.IsPath P) (hxP : x ∈ P) : x = P.first ∨ x = P.last :=
  hx.eq_first_or_eq_last_of_mem_trail hP.isTrail hxP

lemma IsLeaf.delete_connected (hx : G.IsLeaf x) (hG : G.Connected) : (G - x).Connected := by
  obtain ⟨y, hy : G.Adj x y, hu⟩ := hx.exists_unique_adj
  refine connected_of_vertex ⟨hy.right_mem, fun h : y = x ↦ hx.not_adj_self (h ▸ hy)⟩ fun z hz ↦ ?_
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.connBetween hz.1 hy.right_mem).exists_isPath
  refine IsWalk.connBetween_first_last <| isWalk_vertexDelete_iff.2 ⟨hP.isWalk, ?_⟩
  simp only [disjoint_singleton_right, mem_vertexSet_iff]
  intro hxP
  obtain rfl | rfl := hx.eq_first_or_eq_last_of_mem_path hP hxP
  · simp at hz
  exact hx.not_adj_self hy

/-- Deleting the first vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_first_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - P.first).Connected := by
  cases P with
  | nil u =>
    obtain ⟨e, y, huy, hne⟩ := hG.exists_isLink_of_mem hnt (x := u) (by simpa using hP.prop)
    exact False.elim <| hne.symm <| by
      simpa [huy, huy.right_mem] using hP.eq_of_ge (y := cons u e (nil y))
  | cons u e P =>
    have ⟨he, hP', huP⟩ : G.IsLink e u P.first ∧ G.IsPath P ∧ u ∉ P := by simpa using hP.prop
    by_contra hcon
    simp only [first_cons] at hcon
    have hP'' : (G - u).IsPath P := by simp [isPath_vertexDelete_iff, huP, hP']
    obtain ⟨S, hS⟩ :=
      hP''.isWalk.toGraph_connected.exists_separation_of_le hcon hP''.isWalk.toGraph_le
    have hPS : V(P) ⊆ S.left := by simpa using vertexSet_mono hS
    have huleft : u ∉ S.left := fun huS ↦ by simpa using S.left_subset huS
    have huright : u ∉ S.right := fun huS ↦ by simpa using S.right_subset huS
    suffices hu : ∀ x ∈ S.right, ¬ G.Adj u x by
      refine Separation.not_connected
        ⟨insert u S.left, S.right, by simp, S.nonempty_right, ?_, ?_, ?_⟩ hG
      · simp [S.disjoint, huright]
      · simpa [insert_union, S.union_eq] using he.left_mem
      rintro x y (rfl | hxS) hyS ⟨e, hxy⟩
      · exact hu y hyS hxy.adj
      refine S.not_adj hxS hyS ⟨e, ?_⟩
      simp only [vertexDelete_singleton, vertexDelete_isLink_iff, hxy, mem_singleton_iff, true_and]
      constructor <;> (rintro rfl; contradiction)
    rintro x hx ⟨f, hux⟩
    have hne : u ≠ x := by rintro rfl; contradiction
    refine S.disjoint.notMem_of_mem_left (hPS ?_) hx
    simpa [hne.symm] using mem_of_adj_first_of_maximal_isPath hP hux.symm.adj

/-- Deleting the last vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_last_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - P.last).Connected := by
  suffices aux : Maximal (fun P ↦ G.IsPath P) P.reverse by
    simpa using hG.delete_first_connected_of_maximal_isPath hnt aux
  refine ⟨by simpa using hP.prop, fun Q hQ hPQ ↦ ?_⟩
  simp [hP.eq_of_le (y := Q.reverse) (by simpa) (by simpa using IsSublist.reverse hPQ)]

/-- Every finite connected graph on at least two vertices has a vertex whose deletion
preserves its connectedness.
(This requires a finite graph, since otherwise an infinite path is a counterexample.) -/
lemma Connected.exists_delete_vertex_connected [G.Finite] (hG : G.Connected)
    (hnt : V(G).Nontrivial) : ∃ x ∈ V(G), (G - x).Connected := by
  obtain ⟨x, hx⟩ := hG.nonempty
  obtain ⟨P, hP⟩ := Finite.exists_maximal G.isPath_finite ⟨nil x, by simpa⟩
  exact ⟨_, hP.prop.isWalk.first_mem, hG.delete_first_connected_of_maximal_isPath hnt hP⟩

lemma Preconnected.left_mem_of_edgeDelete_linkEdges (h : G.Preconnected)
    (h' : ¬ (G ＼ E(G, u, v)).Preconnected) : u ∈ V(G) := by
  by_contra huv
  simp [huv, h] at h'

lemma Preconnected.right_mem_of_edgeDelete_linkEdges (h : G.Preconnected)
    (h' : ¬ (G ＼ E(G, u, v)).Preconnected) : v ∈ V(G) := by
  by_contra huv
  simp [huv, h] at h'

-- lemma Preconnected.connBetween_of_edgeDelete_linkEdges (h : G.Preconnected)
--     (h' : ¬ (G ＼ E(G, u, v)).Preconnected) (hx : x ∈ V(G)) :
--     (G ＼ E(G, u, v)).ConnBetween u x ∨ (G ＼ E(G, u, v)).ConnBetween v x := by
--   classical
--   obtain ⟨P, hP, rfl, rfl⟩ := h x u hx (h.left_mem_of_edgeDelete_linkEdges h')
--   let H := (Subgraph.ofEdge G E(G, P.first, v))ᶜ
--   have := hP.prefixUntil_isWalk_subgraph (H := H) ?_
--   simp? [H, Subgraph.compl_compl] at this
--   sorry

lemma IsClosedSubgraph.le_or_le_of_preconnected (hH : H.Preconnected) (hHG : H ≤ G₂)
    (h12 : G₁ ≤c G₂) : H ≤ G₁ ∨ H ≤ G₂ - V(G₁) := by
  by_cases hdj : Disjoint V(G₁) V(H)
  · exact Or.inr <| h12.compl.isInducedSubgraph.le_of_le_subset hHG fun y hyH ↦
      ⟨Graph.vertexSet_mono hHG hyH, hdj.notMem_of_mem_right hyH⟩
  rw [not_disjoint_iff] at hdj
  obtain ⟨x, hx₁, hxH⟩ := hdj
  exact Or.inl <| h12.isInducedSubgraph.le_of_le_subset hHG fun y hyH ↦ hH x y hxH hyH |>.mono hHG
  |>.isClosedSubgraph h12 hx₁ |>.right_mem
