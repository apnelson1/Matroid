import Matroid.Graphic

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}
{P C Q : WList α β}
open Set WList

namespace Graph

@[mk_iff]
structure IsTree (T : Graph α β) : Prop where
  isForest : T.IsForest
  connected : T.Connected

lemma IsForest.isTree_of_IsCompOf (hG : G.IsForest) (hT : T.IsCompOf G) : T.IsTree :=
  ⟨hG.mono hT.le, hT.connected⟩

/-- If `G` is connected, then a maximally acylic subgraph of `G` is connected.
The correct statement is that any two vertices connected in the big graph are
connected in the small one.
TODO : Write the proof completely in terms of `IsAcyclicSet`
-/
lemma Connected.isTree_of_maximal_isAcyclicSet (hG : G.Connected) (hF : Maximal G.IsAcyclicSet F) :
    (G ↾ F).IsTree := by
  rw [show G.IsAcyclicSet = fun X ↦ X ⊆ E(G) ∧ (G ↾ X).IsForest by
    ext; exact isAcyclicSet_iff] at hF
  refine ⟨hF.prop.2, by_contra fun hcon ↦ ?_⟩
  obtain ⟨S, e, x, y, heF, hx, hy, hxy⟩ := hG.exists_of_edgeRestrict_not_connected hcon
  have hne : x ≠ y := S.disjoint.ne_of_mem hx hy
  have hx' : x ∉ S.right := S.disjoint.notMem_of_mem_left hx
  have hy' : y ∉ S.left := S.disjoint.notMem_of_mem_right hy
  have hFac : (G ↾ F).IsForest := hF.prop.2
  have h_left : (G ↾ F)[S.left].IsForest := hFac.mono (induce_le S.left_subset)
  have h_right : (G ↾ F)[S.right].IsForest := hFac.mono (induce_le S.right_subset)
  have h_left' := h_left.union_isForest_of_subsingleton_inter (singleEdge_isForest hne e) ?_; swap
  · rw [induce_vertexSet, singleEdge_vertexSet, pair_comm, inter_insert_of_notMem hy']
    exact Subsingleton.inter_singleton
  have h' := h_left'.union_isForest_of_subsingleton_inter h_right ?_; swap
  · simp only [union_vertexSet, induce_vertexSet, singleEdge_vertexSet, union_insert,
      union_singleton]
    rw [insert_inter_of_notMem hx', insert_inter_of_mem hy, S.disjoint.inter_eq]
    simp
  have hins : insert e F ⊆ E(G) := insert_subset hxy.edge_mem hF.prop.1
  refine heF <| hF.mem_of_prop_insert ⟨hins, h'.mono ?_⟩
  rw [(Compatible.of_disjoint_edgeSet (by simp [heF])).union_comm (G := (G ↾ F)[S.left]),
    Graph.union_assoc, ← S.eq_union]
  refine le_of_le_le_subset_subset (G := G) (by simp) (Graph.union_le (by simpa) (by simp))
    (by simp) ?_
  simp [inter_eq_self_of_subset_right hins, inter_eq_self_of_subset_right hF.prop.1]

/-- Every connected graph has a spanning tree -/
lemma Connected.exists_isTree_spanningSubgraph (hG : G.Connected) : ∃ T, T.IsTree ∧ T ≤s G := by
  obtain ⟨B, hB⟩ := G.cycleMatroid.exists_isBase
  refine ⟨G ↾ B, ?_, by simp⟩
  rw [Matroid.isBase_iff_maximal_indep, cycleMatroid_indep] at hB
  exact hG.isTree_of_maximal_isAcyclicSet hB

lemma IsTree.exists_delete_vertex_isTree [T.Finite] (hT : T.IsTree)
    (hnt : V(T).Nontrivial) : ∃ v ∈ V(T), (T - v).IsTree := by
  obtain ⟨x, hxT, hconn⟩ := hT.connected.exists_delete_vertex_connected hnt
  exact ⟨x, hxT, hT.isForest.mono vertexDelete_le, hconn⟩

lemma IsLeaf.delete_isTree (hT : T.IsTree) (hx : T.IsLeaf x) : (T - x).IsTree :=
  ⟨hT.isForest.mono vertexDelete_le, hx.delete_connected hT.connected⟩

lemma IsTree.encard_vertexSet {T : Graph α β} (h : T.IsTree) : V(T).encard = E(T).encard + 1 := by
  have hsimp := h.isForest.simple
  obtain (rfl | ⟨x, rfl⟩ | hnt) := T.eq_noEdge_or_vertexSet_nontrivial
  · simpa using h.connected.nonempty
  · simp
  obtain hinf | hfin := em' T.Finite
  · rw [encard_eq_top_iff.2, encard_eq_top_iff.2, top_add]
    · rwa [Set.Infinite, (h.connected.degreePos hnt).edgeSet_finite_iff]
    simpa [Set.Infinite]
  obtain ⟨e, x, he⟩ := h.isForest.exists_isPendant (h.connected.edgeSet_nonempty hnt)
  have hxV := he.isNonloopAt.vertex_mem
  have hlt := encard_delete_vertex_lt hxV
  have := he.isLeaf.delete_isTree h
  rw [← encard_diff_singleton_add_one hxV, ← vertexDelete_vertexSet, ← vertexDelete_singleton,
    (he.isLeaf.delete_isTree h).encard_vertexSet, he.edgeSet_delete_vertex_eq,
    encard_diff_singleton_add_one he.isNonloopAt.edge_mem]
termination_by V(T).encard

lemma IsTree.ncard_vertexSet [T.Finite] (h : T.IsTree) : V(T).ncard = E(T).ncard + 1 := by
  rw [← Nat.cast_inj (R := ℕ∞), T.vertexSet_finite.cast_ncard_eq, h.encard_vertexSet,
    Nat.cast_add, T.edgeSet_finite.cast_ncard_eq, Nat.cast_one]

lemma IsForest.encard_vertexSet (hG : G.IsForest) :
    V(G).encard = E(G).encard + {C : Graph α β | C.IsCompOf G}.encard := by
  rw [G.eq_sUnion_components, sUnion_vertexSet, ← ENat.tsum_encard_eq_encard_biUnion,
    tsum_congr (β := G.Components) (f := fun C ↦ V(C.1).encard)
      (g := fun C ↦ E(C.1).encard + 1), sUnion_edgeSet, ← ENat.tsum_encard_eq_encard_biUnion,
    ← ENat.tsum_one, ENat.tsum_add, ← G.eq_sUnion_components, Components]
  · exact G.components_pairwise_stronglyDisjoint.mono' <| by simp [Pi.le_def, stronglyDisjoint_iff]
  · simp only [Subtype.forall, mem_components_iff_isCompOf]
    exact fun H hle ↦ (hG.isTree_of_IsCompOf hle).encard_vertexSet
  exact G.components_pairwise_stronglyDisjoint.mono' <| by
    simp +contextual [Pi.le_def, stronglyDisjoint_iff]

lemma IsForest.ncard_vertexSet [G.Finite] (hG : G.IsForest) :
    V(G).ncard = E(G).ncard + {C : Graph α β | C.IsCompOf G}.ncard := by
  rw [← @Nat.cast_inj ℕ∞, G.vertexSet_finite.cast_ncard_eq, hG.encard_vertexSet, Nat.cast_add,
    G.edgeSet_finite.cast_ncard_eq, Finite.cast_ncard_eq]
  exact G.finite_setOf_le.subset fun C hC ↦ hC.le

lemma IsForest.encard_edgeSet_add_one_le (hG : G.IsForest) (hne : V(G).Nonempty) :
    E(G).encard + 1 ≤ V(G).encard := by
  rw [hG.encard_vertexSet]
  gcongr
  simp only [one_le_encard_iff_nonempty]
  exact ⟨_, (G.exists_IsCompOf hne).choose_spec⟩

lemma IsForest.ncard_edgeSet_lt [G.Finite] (hG : G.IsForest) (hne : V(G).Nonempty) :
    E(G).ncard < V(G).ncard := by
  rw [Nat.lt_iff_add_one_le, ← @Nat.cast_le ℕ∞, Nat.cast_add, G.vertexSet_finite.cast_ncard_eq,
    G.edgeSet_finite.cast_ncard_eq]
  exact hG.encard_edgeSet_add_one_le hne

lemma Connected.encard_vertexSet_le (hG : G.Connected) : V(G).encard ≤ E(G).encard + 1 := by
  obtain ⟨T, hT, hTG⟩ := hG.exists_isTree_spanningSubgraph
  grw [← hTG.vertexSet_eq, hT.encard_vertexSet, hTG.le]

lemma Connected.ncard_vertexSet_le [G.Finite] (hG : G.Connected) : V(G).ncard ≤ E(G).ncard + 1 := by
  rw [← @Nat.cast_le ℕ∞, Nat.cast_add, G.vertexSet_finite.cast_ncard_eq,
    G.edgeSet_finite.cast_ncard_eq]
  exact hG.encard_vertexSet_le
