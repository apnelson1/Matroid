import Matroid.Graph.Tree

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}
{P C : WList α β}

open Set WList Function

namespace Graph

/-- A bipartion of `G` is a partition of the vertex set into two parts such that every edge
goes from one to the other. -/
structure Bipartition (G : Graph α β) where
  left : Set α
  right : Set α
  union_eq : left ∪ right = V(G)
  disjoint : Disjoint left right
  forall_edge : ∀ e ∈ E(G), ∃ x ∈ left, ∃ y ∈ right, G.IsLink e x y

def Bipartition.symm (B : G.Bipartition) : G.Bipartition where
  left := B.right
  right := B.left
  union_eq := by rw [union_comm, B.union_eq]
  disjoint := B.disjoint.symm
  forall_edge e he := by
    obtain ⟨x, hx, y, hy, hxy⟩ := B.forall_edge e he
    exact ⟨y, hy, x, hx, hxy.symm⟩

lemma Bipartition.left_subset (B : G.Bipartition) : B.left ⊆ V(G) := by
  simp [← B.union_eq]

lemma Bipartition.right_subset (B : G.Bipartition) : B.right ⊆ V(G) := by
  simp [← B.union_eq]

/-- A graph with a bipartition is bipartite. -/
def Bipartite (G : Graph α β) : Prop := Nonempty G.Bipartition

/-- A subgraph of a bipartite graph is bipartite -/
lemma Bipartite.of_le (hG : G.Bipartite) (hle : H ≤ G) : H.Bipartite := by
  obtain ⟨B⟩ := hG
  refine ⟨⟨B.left ∩ V(H), B.right ∩ V(H), ?_, ?_, fun e he ↦ ?_⟩⟩
  · rw [← union_inter_distrib_right, B.union_eq,
      inter_eq_self_of_subset_right (vertexSet_subset_of_le hle)]
  · exact B.disjoint.mono inter_subset_left inter_subset_left
  obtain ⟨x, hx, y, hy, hxy⟩ := B.forall_edge e (edgeSet_subset_of_le hle he)
  replace hxy := hxy.of_le_of_mem hle he
  exact ⟨x, ⟨hx, hxy.left_mem⟩, y, ⟨hy, hxy.right_mem⟩, hxy⟩

/-- A disjoint union of bipartite graphs is bipartite. -/
lemma iUnion_disjoint_bipartite {ι : Type*} {H : ι → Graph α β}
    (hdj : Pairwise (Graph.Disjoint on H)) (hbp : ∀ i, Bipartite (H i)) :
    Bipartite <| (UCompatible.of_disjoint hdj).iUnion _ := by
  set B : ∀ i, (H i).Bipartition := fun i ↦ (hbp i).some
  refine ⟨⟨⋃ i, (B i).left, ⋃ i, (B i).right, ?_, ?_, ?_⟩⟩
  · simp +contextual [Bipartition.union_eq, ← iUnion_union_distrib]
  · simp only [disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j
    obtain rfl | hne := eq_or_ne i j
    · exact (B i).disjoint
    exact (hdj hne.symm).vertex.mono (B j).left_subset (B i).right_subset
  simp_rw [UCompatible.iUnion_edgeSet, mem_iUnion, UCompatible.iUnion_isLink, forall_exists_index]
  intro e i he
  obtain ⟨x, hx, y, hy, hxy⟩ := (B i).forall_edge _ he
  exact ⟨x, ⟨i, hx⟩, y, ⟨i, hy⟩, ⟨i, hxy⟩⟩

lemma sUnion_disjoint_bipartite {s : Set (Graph α β)} (hdj : s.Pairwise Graph.Disjoint)
    (hbp : ∀ G ∈ s, G.Bipartite) : Bipartite <| (Graph.sUnion s (hdj.mono' (by simp))) := by
  apply iUnion_disjoint_bipartite
  · exact (pairwise_subtype_iff_pairwise_set s Graph.Disjoint).2 hdj
  simpa

lemma bipartite_iff_forall_component :
    G.Bipartite ↔ ∀ (H : Graph α β), H.IsComponent G → H.Bipartite := by
  refine ⟨fun h H hH ↦ h.of_le hH.le, fun h ↦ ?_⟩
  rw [G.eq_sUnion_components]
  exact sUnion_disjoint_bipartite G.pairwiseDisjoint_components <| by simpa

-- lemma foo : G.Bipartite ↔ ∀ C, G.IsCycle C → Even C.length := by
--   wlog hG : G.Connected with aux
--   · rw [bipartite_iff_forall_component]
--     refine ⟨fun h C hC ↦ ?_, fun h H hHG ↦ ?_⟩
--     · obtain ⟨H, hH, hCH⟩ := hC.isWalk.exists_isComponent_isWalk
--       apply (aux (hH.connected)).1 (h H hH)
--       sorry
--     rw [aux hHG.connected]
--     refine fun C hC ↦ h C ?_
--     sorry
--   sorry
    -- have := hC.of_le hHG.le
