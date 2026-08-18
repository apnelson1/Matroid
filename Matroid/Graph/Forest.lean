module

public import Matroid.Graph.Distance
public import Matroid.Graph.Connected.Subgraph
public import Matroid.Graph.Connected.Bond
import all Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Delete


@[expose] public section

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α}
  {F F' I J : Set β} {P C Q : WList α β}
open Set WList

namespace Graph

/-- If `P` and `Q` are distinct paths with the same ends, their union contains a cycle. -/
theorem twoPaths (hP : G.IsPath P) (hQ : G.IsPath Q) (hPQ : P ≠ Q) (h0 : P.first = Q.first)
    (h1 : P.last = Q.last) : ∃ C, G.IsCyclicWalk C ∧ E(C) ⊆ E(P) ∪ E(Q) := by
  classical
  induction P generalizing Q with
  | nil u => cases Q with | _ => simp_all
  | cons u e P ih =>
    subst h0
    obtain ⟨heP, -⟩ := by simpa only [cons_edge, List.nodup_cons] using hP.edge_nodup
    simp only [cons_isPath_iff] at hP
    obtain ⟨x, rfl⟩ | hne := Q.exists_eq_nil_or_nonempty
    · obtain rfl : P.last = x := h1
      simp at hP
    -- If `e` is an edge of `Q`, then since `e` is incident to the first vertex of `cons u f Q`,
    -- it must be equal to `f`. So `P` and `Q` agree on their first edge; apply induction.
    by_cases heQ : e ∈ Q.edge
    · obtain rfl : e = hne.firstEdge := hQ.eq_firstEdge_of_isLink_first heQ hP.1.inc_left
      cases hne with | cons u f Q =>
      have hfirst : P.first = Q.first := by
        simp only [Nonempty.firstEdge_cons, first_cons, cons_isPath_iff] at hP hQ
        rw [hP.1.isLink_iff_eq] at hQ
        exact hQ.1.symm
      obtain ⟨C, hC, hCss⟩ := ih hP.2.1 hQ.of_cons (by simpa using hPQ) hfirst (by simpa using h1)
      refine ⟨C, hC, hCss.trans ?_⟩
      simp [show E(P) ⊆ insert f E(P) ∪ E(Q) from (subset_insert ..).trans subset_union_left]
    -- Otherwise, `e + P` and `Q` have different first edges. Now `P ∪ Q`
    -- contains a path between the ends of `e` not containing `e`, which gives a cycle.
    have hR_ex : ∃ R, G.IsPath R ∧ e ∉ R.edge ∧
        R.first = Q.first ∧ R.last = P.first ∧ E(R) ⊆ E(P) ∪ E(Q) := by
      refine ⟨(Q ++ P.reverse).dedup, ?_, ?_, ?_, by simp, ?_⟩
      · exact IsWalk.dedup (hQ.isWalk.append hP.2.1.isWalk.reverse (by simpa using h1.symm))
      · rw [← mem_edgeSet_iff]
        refine notMem_subset (t := E(Q ++ P.reverse)) ((dedup_isSublist _).edge_subset) ?_
        simp [heQ, heP]
      · simp [append_first_of_nonempty hne]
      exact (dedup_isSublist _).edge_subset.trans <| by simp
    obtain ⟨R, hR, heR, hfirst, hlast, hss⟩ := hR_ex
    refine ⟨_, hR.concat_isCyclicWalk ?_ heR, ?_⟩
    · rw [hfirst, hlast]
      exact hP.1.symm
    simp only [concat_edgeSet, cons_edgeSet]
    rw [insert_union]
    exact insert_subset_insert hss

def IsForest (G : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → G.IsBridge e

lemma IsForest.isEdgeSep (hG : G.IsForest) (he : e ∈ E(G)) : G.IsEdgeSep {e} where
  subset_edgeSet := by simpa
  not_connected h := by
    have := hG he
    rw [(h.of_isSpanningSubgraph deleteEdges_isSpanningSubgraph).isBridge_iff_isEdgeSep] at this
    exact this.not_connected h

lemma IsForest.isEdgeCutBetween (hG : G.IsForest) (hl : G.IsLink e x y) :
    G.IsEdgeCutBetween {e} x y where
  subset_edgeSet := by simp [hl.edge_mem]
  not_connBetween := by
    exact (hl.isBridge_iff_isEdgeCutBetween.mp <| hG hl.edge_mem).not_connBetween

lemma IsForest.anti (hG : G.IsForest) (hHG : H ≤ G) : H.IsForest :=
  fun _ he ↦ hG (edgeSet_mono hHG he) |>.anti_of_mem hHG he

/-- The union of two forests that intersect in at most one vertex is a forest.  -/
lemma IsForest.union_isForest_of_subsingleton_inter (hG : G.IsForest) (hH : H.IsForest)
    (hi : (V(G) ∩ V(H)).Subsingleton) : (G ∪ H).IsForest := by
  wlog hc : Compatible G H generalizing H with aux
  · have := aux (hH.anti deleteEdges_le : (H ＼ E(G)).IsForest) (by simpa)
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
    rwa [Graph.union_eq_union_deleteEdges]
  intro e he
  wlog heG : e ∈ E(G) generalizing G H with aux
  · obtain heH : e ∈ E(G) ∨ e ∈ E(H) := by simpa using he
    rw [inter_comm] at hi
    have := aux hH hG hi hc.symm (by simpa [or_comm]) (heH.resolve_left heG)
    rwa [hc.symm.union_comm] at this
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heG
  have := hxy.isBridge_iff_not_connBetween.mp (hG (hxy.edge_mem))
  rw [hxy.of_le (Graph.left_le_union ..) |>.isBridge_iff_not_connBetween]
  contrapose! this
  obtain ⟨P, hP, rfl, rfl⟩ := this.exists_isPath
  use P, ?_
  obtain ⟨hP, heP⟩ : (G ∪ H).IsPath P ∧ e ∉ P.edge := by simpa using hP
  simpa [hP.isPath_of_union_of_subsingleton_inter hi hxy.left_mem hxy.right_mem |>.isWalk]

lemma IsForest.of_isCompOf_isForest (h : ∀ H : Graph α β, H.IsCompOf G → H.IsForest) :
    G.IsForest := by
  rintro e he
  rw [G.eq_sUnion_components] at he
  simp only [edgeSet_sUnion, mem_components_iff_isCompOf, mem_iUnion, exists_prop] at he
  obtain ⟨H, hH, heH⟩ := he
  exact h H hH heH |>.of_isClosedSubgraph hH.isClosedSubgraph

lemma IsPath.toGraph_isForest (hG : G.IsPath P) : P.toGraph.IsForest := by
  simp only [IsForest, WList.toGraph_edgeSet, WList.mem_edgeSet_iff]
  exact fun _ ↦ hG.isBridge_of_mem

lemma IsCyclicWalk.toGraph_not_isForest (hC : G.IsCyclicWalk C) : ¬ C.toGraph.IsForest := by
  obtain ⟨u, e, P⟩ := hC.nonempty
  obtain rfl := by simpa only [cons_isClosed_iff] using hC.isClosed
  simp only [IsForest, toGraph_edgeSet, cons_edgeSet, mem_insert_iff, mem_edgeSet_iff,
    forall_eq_or_imp, not_and_or]
  left
  obtain ⟨hP, he, heP⟩ := by simpa only [cons_isTrail_iff] using hC.isTrail
  rw [(he.of_le_of_mem hC.isWalk.toGraph_le (by simp)).isBridge_iff_not_connBetween, not_not,
    connBetween_comm]
  use P, ?_
  simp only [isWalk_deleteEdges_iff, disjoint_singleton_right, mem_edgeSet_iff, heP,
    not_false_eq_true, and_true]
  exact hP.isWalk.wellFormed.isWalk_toGraph.of_le (Graph.left_le_union ..)

lemma IsCyclicWalk.toGraph_eq_of_le {C C₀ : WList α β} (hC : G.IsCyclicWalk C)
    (hC₀ : G.IsCyclicWalk C₀) (hle : C₀.toGraph ≤ C.toGraph) : C₀.toGraph = C.toGraph := by
  have hCE : E(C₀) ⊆ E(C) := by simpa using edgeSet_mono hle
  have hCV : V(C₀) ⊆ V(C) := by simpa using vertexSet_mono hle
  refine hle.antisymm <| G.le_of_le_le_subset_subset hC.isWalk.toGraph_le
    hC₀.isWalk.toGraph_le (fun x hxC ↦ by_contra fun hxC₀ ↦ ?_)
      (fun e heC ↦ by_contra fun heC₀ ↦ ?_)
  · obtain ⟨y, e, rfl⟩ | hnt := hC.loop_or_nontrivial
    · obtain rfl : x = y := by simpa using hxC
      have hfa : ∀ y ∈ C₀, y = x := by simpa using vertexSet_mono hle
      obtain rfl : C₀.first = x := by simpa using hfa C₀.first
      simp at hxC₀
    obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vertex (x := x) hnt
      (by simpa using hxC)
    refine hC₀.toGraph_not_isForest <| hP.toGraph_isForest.anti ?_
    rw [hP_eq, hC.isWalk.toGraph_eq_induce_restrict, hC₀.isWalk.toGraph_eq_induce_restrict,
      restrict_deleteVerts, induce_deleteVerts]
    refine (restrict_mono_right _ hCE).trans (restrict_mono_left (induce_mono_right _ ?_) _)
    simpa [subset_sdiff, hCV] using hxC₀
  obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge <| by simpa using heC
  refine hC₀.toGraph_not_isForest <| hP.toGraph_isForest.anti ?_
  rw [hPC, hC.isWalk.toGraph_eq_induce_restrict, hC₀.isWalk.toGraph_eq_induce_restrict,
    restrict_deleteEdges]
  have hss : E(C₀) ⊆ E(C) \ {e} := subset_sdiff_singleton hCE (by simpa using heC₀)
  refine (restrict_mono_right _ hss).trans ?_
  rw [← restrict_induce, ← restrict_induce]
  exact induce_mono_right _ hCV

lemma IsForest.not_isTour (hG : G.IsForest) : ¬ G.IsTour P := by
  intro h
  obtain ⟨C, hC, -⟩ := h.exists_isCyclicWalk
  exact hC.toGraph_not_isForest <| hG.anti hC.isWalk.toGraph_le

lemma isForest_iff_not_isCyclicWalk : G.IsForest ↔ ∀ C, ¬ G.IsCyclicWalk C := by
  refine ⟨fun hG C hC ↦ hG.not_isTour hC.isTour, fun h ↦ ?_⟩
  contrapose! h
  obtain ⟨e, he, hb⟩ := by simpa only [IsForest, not_forall, Classical.not_imp] using h
  obtain ⟨C, hC, heC⟩ := exists_isCyclicWalk_of_not_isBridge he hb
  use C


def IsCycle (G : Graph α β) : Prop := Minimal (fun G ↦ ¬ G.IsForest) G

lemma isCycle_iff : G.IsCycle ↔ Minimal (fun G : Graph α β ↦ ∃ e ∈ E(G), ¬ G.IsBridge e) G := by
  simp [IsCycle, IsForest]

lemma IsCycle.isForest_of_lt (hG : G.IsCycle) (hH : H < G) : H.IsForest := by
  by_contra! hnotF
  obtain rfl := Minimal.eq_of_le hG hnotF hH.le
  simp at hH

lemma IsCycle.edgeSet_nonempty (hG : G.IsCycle) : E(G).Nonempty := by
  obtain ⟨e, he, hb⟩ := isCycle_iff.mp hG |>.prop
  use e

lemma IsCycle.nonempty (hG : G.IsCycle) : V(G).Nonempty := by
  obtain ⟨e, he, hb⟩ := isCycle_iff.mp hG |>.prop
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  use x, hxy.left_mem

lemma IsCycle.connected (hG : G.IsCycle) : G.Connected := by
  obtain ⟨H, hHc, hHF⟩ := by
    simpa only [not_forall, Classical.not_imp] using mt IsForest.of_isCompOf_isForest hG.prop
  obtain rfl := hG.eq_of_le hHF hHc.le
  exact hHc.connected

lemma IsCyclicWalk.toGraph_isCycle (hC : G.IsCyclicWalk C) : C.toGraph.IsCycle := by
  refine ⟨hC.toGraph_not_isForest, fun H hH hle ↦ ?_⟩
  obtain ⟨e, heC, hb⟩ := by simpa only [IsForest, not_forall, Classical.not_imp] using hH
  obtain ⟨C', hC', heC'⟩ := exists_isCyclicWalk_of_not_isBridge (by simpa) hb
  convert hC'.isWalk.toGraph_le using 1
  apply hC.toGraph_eq_of_le (hC'.of_le <| hle.trans hC.isWalk.toGraph_le) ?_ |>.symm
  exact hC'.isWalk.toGraph_le.trans hle

lemma IsCycle.exists_isCyclicWalk_eq (hG : G.IsCycle) : ∃ C, G.IsCyclicWalk C ∧ C.toGraph = G := by
  obtain ⟨e, he, hb⟩ := isCycle_iff.mp hG |>.prop
  obtain ⟨C, hC, heC⟩ := exists_isCyclicWalk_of_not_isBridge he hb
  use C, hC
  have hle : C.toGraph ≤ G := hC.isWalk.toGraph_le
  exact hG.eq_of_le hC.toGraph_not_isForest hle

lemma isCycle_iff_exists_isCyclicWalk_eq : G.IsCycle ↔ ∃ C, G.IsCyclicWalk C ∧ C.toGraph = G :=
  ⟨fun hG ↦ hG.exists_isCyclicWalk_eq, fun ⟨_, hC, hC_eq⟩ ↦ hC_eq ▸ hC.toGraph_isCycle⟩

lemma IsCycle.not_isBridge (hG : G.IsCycle) : ¬ G.IsBridge e := by
  wlog he : e ∈ E(G)
  · grind
  rw [isCycle_iff_exists_isCyclicWalk_eq] at hG
  obtain ⟨C, hC, rfl⟩ := hG
  exact not_isBridge_of_exists_isCyclicWalk ⟨C, hC, by simpa using he⟩

/-- Given a cycle and the 'orientation to traverse the cycle' in the form of a link, there exists a
cyclic walk that starts with `x, y`. -/
lemma IsLink.exists_cons_isCyclicWalk_eq_of_IsCycle (hG : G.IsCycle) (hxy : G.IsLink e x y) :
    ∃ C, G.IsCyclicWalk (cons x e C) ∧ C.first = y ∧ (cons x e C).toGraph = G := by
  obtain ⟨C, hC, rfl⟩ := hxy.exists_cons_isCyclicWalk_of_not_isBridge hG.not_isBridge
  use C, hC, rfl
  have hle : WList.toGraph _ ≤ G := hC.isWalk.toGraph_le
  exact hG.eq_of_le hC.toGraph_not_isForest hle

lemma IsCycle.finite (hG : G.IsCycle) : G.Finite := by
  rw [isCycle_iff_exists_isCyclicWalk_eq] at hG
  obtain ⟨C, hC, rfl⟩ := hG
  infer_instance

lemma IsCycle.regular_two {C : Graph α β} (hC : C.IsCycle) : C.Regular 2 := by
  obtain ⟨C', hC', rfl⟩ := by simpa only [isCycle_iff_exists_isCyclicWalk_eq] using hC
  exact hC'.toGraph_regular

lemma IsCycle.three_le_encard_of_simple [G.Simple] (hG : G.IsCycle) : 3 ≤ V(G).encard := by
  obtain ⟨x, hx⟩ := hG.nonempty
  have h := eDegree_le_encard hx
  rw [hG.regular_two hx] at h
  exact (by norm_num : (3 : ℕ∞) ≤ 2 + 1).trans h

/-- A cycle on at least three vertices is `2`-connected. -/
lemma IsCycle.connGE_two (hG : G.IsCycle) (h3 : 3 ≤ V(G).encard) : G.ConnGE 2 where
  le_card := Or.inr <| (by norm_num : (2 : ℕ∞) < 3).trans_le h3
  le_cut C hC := by
    by_contra hlt
    have hle1 : C.encard ≤ 1 := by
      contrapose! hlt
      convert Order.add_one_le_of_lt hlt
      · rfl
      norm_num
    obtain rfl | ⟨x, rfl⟩ := encard_le_one_iff_eq.1 hle1
    · exact empty_isSep_iff.mp hC hG.connected
    obtain ⟨W, hW, rfl⟩ := hG.exists_isCyclicWalk_eq
    have hx : x ∈ W := by simpa [mem_vertexSet_iff] using hC.subset_vx (mem_singleton x)
    have hnt : W.Nontrivial := hW.nontrivial_iff_vertexSet_nontrivial.2 <|
      one_lt_encard_iff_nontrivial.1 <| (by norm_num : (1 : ℕ∞) < 3).trans_le (by simpa using h3)
    obtain ⟨P, hP, hPeq⟩ := hW.exists_isPath_toGraph_eq_delete_vertex hnt hx
    exact hC.not_connected <| hPeq ▸ hP.isWalk.toGraph_connected

lemma IsCycle.eq_of_le (hG : G.IsCycle) (hH : H.IsCycle) (hle : G ≤ H) : G = H := by
  obtain ⟨C', hC', rfl⟩ := by simpa only [isCycle_iff_exists_isCyclicWalk_eq] using hG
  obtain ⟨C'', hC'', rfl⟩ := by simpa only [isCycle_iff_exists_isCyclicWalk_eq] using hH
  exact hC''.toGraph_eq_of_le (hC'.of_le hle) hle

lemma IsCycle.toGraph_of_isCyclicWalk {C : WList α β} (hG : G.IsCycle)
    (hC : G.IsCyclicWalk C) : C.toGraph = G := by
  obtain ⟨C', hC', rfl⟩ := by simpa only [isCycle_iff_exists_isCyclicWalk_eq] using hG
  exact hC'.toGraph_eq_of_le hC <| hC.isWalk.toGraph_le

lemma IsCycle.loopless_iff (hG : G.IsCycle) : G.Loopless ↔ V(G).Nontrivial := by
  obtain ⟨C, hC, rfl⟩ := hG.exists_isCyclicWalk_eq
  rw [hC.toGraph_loopless_iff, toGraph_vertexSet, ← two_le_encard_iff_nontrivial,
    hC.encard_vertexSet]
  have := hC.nonempty.length_pos
  enat_to_nat!
  lia

lemma IsCycle.simple_iff (hG : G.IsCycle) : G.Simple ↔ 3 ≤ V(G).encard := by
  obtain ⟨C, hC, rfl⟩ := hG.exists_isCyclicWalk_eq
  rw [hC.toGraph_simple_iff, toGraph_vertexSet, hC.encard_vertexSet]
  enat_to_nat!

/-- Given a cycle and a vertex in the cycle, there exists a cyclic walk that starts with the vertex.
The direction of the cyclic walk is not known. -/
lemma IsCycle.exists_isCyclicWalk_of_vertex (hG : G.IsCycle) (hx : x ∈ V(G)) :
    ∃ C, G.IsCyclicWalk C ∧ C.first = x ∧ C.toGraph = G := by
  have := eDegree_eq_zero_iff_inc.not.mp (by rw [hG.regular_two hx]; simp)
  push Not at this
  obtain ⟨e, y, he⟩ := this
  obtain ⟨C, hC, rfl, rfl⟩ := he.exists_cons_isCyclicWalk_eq_of_IsCycle hG
  use (cons x e C), hC, rfl

/-- Without assuming `x ≠ y`, output maybe a trivial path and the entire cycle. See
`IsCycle.exists_two_paths_of_ne`. -/
lemma IsCycle.exists_isPath_isTrail (hG : G.IsCycle) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    ∃ P Q : WList α β, G.IsPath P ∧ G.IsTrail Q ∧ P.first = x ∧ P.last = y ∧ Q.first = y ∧
    Q.last = x ∧ G.IsCyclicWalk (P ++ Q) := by
  classical
  obtain ⟨P, hP, rfl, rfl⟩ := hG.exists_isCyclicWalk_of_vertex hx; clear hx
  refine ⟨P.prefixUntilVertex y, P.suffixFromVertex y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP.ne_iff_isPath_of_isSublist (P.prefixUntilVertex_isPrefix y).isSublist,
      prefixUntilVertex, ne_eq, prefixUntil_eq_self_iff]
    simp only [toGraph_vertexSet, mem_vertexSet_iff, not_forall, Decidable.not_not] at hy ⊢
    obtain hyP | rfl := mem_iff_eq_mem_dropLast_or_eq_last.mp hy
    · have hhh' : y ∈ P.dropLast.vertex := by simpa [mem_vertex] using hyP
      simpa [hP.nonempty.vertex_dropLast] using hhh'
    rw [← hP.isClosed]
    simp [List.mem_dropLast_iff_idxOf_lt]
    rw [List.idxOf_eq_zero_iff_head_eq P.vertex_ne_nil |>.mpr (by simp)]
    exact hP.nonempty.length_pos
  · exact hP.isTrail.sublist (P.suffixFromVertex_isSuffix y).isSublist
  · exact P.prefixUntilVertex_first _
  · exact P.prefixUntilVertex_last (by simpa using hy)
  · exact P.suffixFromVertex_first (by simpa using hy)
  · exact hP.isClosed ▸ P.suffixFromVertex_last y
  rwa [P.prefixUntilVertex_append_suffixFromVertex y]

-- Idea: Define IsCycle.vertexCycle : Cycle α and partition cycle using a subcycle of vertexCycle.
-- and edge version too.
lemma IsCycle.exists_two_paths_of_ne (hG : G.IsCycle) (hx : x ∈ V(G)) (hy : y ∈ V(G)) (hxy : x ≠ y):
    ∃ P Q : WList α β, G.IsPath P ∧ G.IsPath Q ∧ P.first = x ∧ P.last = y ∧ Q.first = y ∧
    Q.last = x ∧ G.IsCyclicWalk (P ++ Q) := by
  classical
  obtain ⟨P, hP, rfl, rfl⟩ := hG.exists_isCyclicWalk_of_vertex hx
  clear hx
  refine ⟨P.prefixUntilVertex y, P.suffixFromVertex y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP.ne_iff_isPath_of_isSublist (P.prefixUntilVertex_isPrefix y).isSublist,
      prefixUntilVertex, ne_eq, prefixUntil_eq_self_iff]
    simp only [toGraph_vertexSet, mem_vertexSet_iff] at hy
    obtain hhh := mem_iff_eq_mem_dropLast_or_eq_last.mp hy |>.resolve_right (hP.isClosed ▸ hxy.symm)
    have hhh' : y ∈ P.dropLast.vertex := by simpa [mem_vertex] using hhh
    simpa [hP.nonempty.vertex_dropLast] using hhh'
  · rw [← hP.ne_iff_isPath_of_isSublist (P.suffixFromVertex_isSuffix y).isSublist]
    simp [hP.nonempty, hxy]
  · exact P.prefixUntilVertex_first _
  · exact P.prefixUntilVertex_last (by simpa using hy)
  · exact P.suffixFromVertex_first (by simpa using hy)
  · exact hP.isClosed ▸ P.suffixFromVertex_last y
  rwa [P.prefixUntilVertex_append_suffixFromVertex y]

lemma IsPath.isPrefix_of_isTrail_toGraph_of_first {P Q : WList α β} (hP : G.IsPath P)
    (hQ : P.toGraph.IsTrail Q) (hfirst : Q.first = P.first) : Q.IsPrefix P := by
  match P, Q with
  | nil u, nil v => simpa using hfirst
  | nil u, cons v e w => simp [cons_isTrail_iff, WList.toGraph] at hQ
  | cons u e w, nil v => simp [hfirst.symm]
  | cons u e P, cons v f Q => _
  simp only [first_cons] at hfirst
  subst v
  obtain ⟨hQ_tail_big, hf, hfQ⟩ := by simpa only [cons_isTrail_iff] using hQ
  obtain ⟨-, hP_tail, hnP⟩ := by simpa only [cons_isPath_iff] using hP
  obtain ⟨rfl, hQ_first⟩ : f = e ∧ Q.first = P.first := by
    rw [hP.isWalk.wellFormed.toGraph_isLink, isLink_cons_iff'] at hf
    obtain ⟨rfl, (⟨-, hQ_first⟩ | ⟨h_eq, rfl⟩)⟩ | hfW' := hf
    · exact ⟨rfl.symm, hQ_first⟩
    · exact (hnP (h_eq ▸ first_mem)).elim
    exact (hnP hfW'.left_mem).elim
  refine (hP_tail.isPrefix_of_isTrail_toGraph_of_first ?_ hQ_first).cons u f Q P
  refine hQ_tail_big.isTrail_le (by simp [toGraph_cons]) (fun g hg ↦ ?_) (by simp [hQ_first])
  exact (hQ_tail_big.edgeSet_subset hg).elim id fun hg_eq ↦
    (hfQ (hg_eq ▸ by simpa only [WList.mem_edgeSet_iff] using hg)).elim

lemma _root_.WList.IsPrefix.isPrefix_of_isPrefix_of_length_le {w₁ w₂ P : WList α β}
    (h₁ : w₁.IsPrefix P) (h₂ : w₂.IsPrefix P) (hle : w₁.length ≤ w₂.length) : w₁.IsPrefix w₂ := by
  rw [← show w₂.take w₁.length = w₁ from
    by rw [h₂.eq_take_length, take_take, min_eq_left hle, h₁.take_eq]]
  exact take_isPrefix w₂ w₁.length

lemma IsCycle.isPrefix_of_isTrail_of_length_le {w₁ w₂ : WList α β} (hG : G.IsCycle)
    (h₁ : G.IsTrail (cons x e w₁)) (h₂ : G.IsTrail (cons x e w₂)) (hle : w₁.length ≤ w₂.length) :
    w₁.IsPrefix w₂ := by
  rw [cons_isTrail_iff] at h₁ h₂
  obtain ⟨C, hC, hC_first, hC_eq⟩ := h₁.2.1.exists_cons_isCyclicWalk_eq_of_IsCycle hG
  have hC_le : C.toGraph ≤ G := by simp [← hC_eq]
  have edge_subset {w : WList α β} (hw : G.IsTrail w) (he : e ∉ w.edge) : E(w) ⊆ E(C.toGraph) := by
    rintro f hf
    have hfG := hw.edgeSet_subset hf
    simp only [← hC_eq, toGraph_cons, edgeSet_union, edgeSet_singleEdge, mem_union,
      mem_singleton_iff] at hfG
    exact hfG.elim id fun hfe ↦ (he <| by simpa [WList.mem_edgeSet_iff, hfe] using hf).elim
  have hC_path := hC.tail_isPath
  have hw₂_first : w₂.first = C.first := (h₂.2.1.right_unique h₁.2.1).trans hC_first.symm
  exact IsPrefix.isPrefix_of_isPrefix_of_length_le
    (hC_path.isPrefix_of_isTrail_toGraph_of_first (h₁.1.isTrail_le hC_le (edge_subset h₁.1 h₁.2.2)
      (by simp [toGraph_vertexSet, ← hC_first])) hC_first.symm)
    (hC_path.isPrefix_of_isTrail_toGraph_of_first (h₂.1.isTrail_le hC_le (edge_subset h₂.1 h₂.2.2)
      (by simp [toGraph_vertexSet, hw₂_first])) hw₂_first) hle

lemma IsCycle.exists_isCyclicWalk_isPrefix_of_isTrail (hG : G.IsCycle) (hP : G.IsTrail P) :
    ∃ C : WList α β, G.IsCyclicWalk C ∧ P.IsPrefix C ∧ C.toGraph = G := by
  obtain ⟨x, rfl⟩ | hne := P.exists_eq_nil_or_nonempty
  · obtain ⟨Cw, hCw, rfl, rfl⟩ := hG.exists_isCyclicWalk_of_vertex (by simpa using hP)
    refine ⟨Cw, hCw, by simp, rfl⟩
  obtain ⟨x, e, w, rfl⟩ := hne.exists_cons
  obtain ⟨hw, he, hew⟩ := by simpa only [cons_isTrail_iff] using hP
  obtain ⟨Cw, hCw, hf, rfl⟩ := he.exists_cons_isCyclicWalk_eq_of_IsCycle hG
  have hwPre : w.IsPrefix Cw := by
    refine hCw.tail_isPath.isPrefix_of_isTrail_toGraph_of_first ?_ (by simpa using hf.symm)
    refine hw.isTrail_le (by simp) ?_ (by simp [← hf, toGraph_vertexSet])
    grind [hw.isWalk.edgeSet_subset]
  use (cons x e Cw), hCw, hwPre.cons ..

lemma IsCycle.exists_path_of_exists_prop {p q : α → Prop} (hG : G.IsCycle) (hp : ∃ x ∈ V(G), p x)
    (hq : ∃ x ∈ V(G), q x) : ∃ P : WList α β, G.IsPath P ∧ p P.first ∧ q P.last ∧
      (∀ x ∈ P.vertex.tail, ¬ p x) ∧ (∀ x ∈ P.vertex.dropLast, ¬ q x) := by
  obtain ⟨Cw, hCw, rfl⟩ := hG.exists_isCyclicWalk_eq
  obtain ⟨P, hP, (⟨hpP, hqP, hPtl, hPdl⟩ | ⟨hqP, hpP, hPtl, hPdl⟩)⟩ :=
    Cw.exists_infix_of_exists_prop (by simpa using hp) (by simpa using hq) <;>
    have hP' : Cw.toGraph.IsPath P := by
      rw [← hCw.ne_iff_isPath_of_isSublist hP.isSublist, ne_eq]
      rintro rfl
      refine hPtl P.last ?_ (hCw.isClosed ▸ by assumption)
      rw [← hCw.nonempty.vertex_tail, mem_vertex, ← tail_last]
      exact last_mem
  · use P, hP', hpP, hqP, hPtl, hPdl
  use P.reverse, hP'.reverse, reverse_first ▸ hpP, reverse_last ▸ hqP, by simpa, by simpa

lemma IsCycle.exists_compl_path_of_isTrail (hG : G.IsCycle) (hP : G.IsTrail P) (hne : P.Nonempty) :
    ∃ Q : WList α β, G.IsPath Q ∧ P.last = Q.first ∧ P.first = Q.last ∧
    G.IsCyclicWalk (P ++ Q) := by
  obtain ⟨Cw, hCw, hwPre, rfl⟩ := hG.exists_isCyclicWalk_isPrefix_of_isTrail hP
  obtain ⟨x, e, w, rfl⟩ := hne.exists_cons
  obtain ⟨Q, hQ, rfl⟩ := isPrefix_iff_exists_eq_append.mp hwPre
  exact ⟨Q, (tail_cons .. ▸ hCw.tail_isPath).of_append_right, hQ, by simpa using hCw.isClosed, hCw⟩

lemma IsCycle.exists_compl_path (hG : G.IsCycle) (hP : G.IsPath P) (hne : P.Nonempty) :
    ∃ Q : WList α β, G.IsPath Q ∧ Q.Nonempty ∧ P.last = Q.first ∧ P.first = Q.last ∧
    G.IsCyclicWalk (P ++ Q) := by
  obtain ⟨Cw, hCw, hwPre, rfl⟩ := hG.exists_isCyclicWalk_isPrefix_of_isTrail hP.isTrail
  obtain ⟨x, e, w, rfl⟩ := hne.exists_cons
  obtain ⟨Q, hQ, rfl⟩ := isPrefix_iff_exists_eq_append.mp hwPre
  refine ⟨Q, (tail_cons .. ▸ hCw.tail_isPath).of_append_right, ?_, hQ, by simpa using hCw.isClosed,
    hCw⟩
  by_contra! hnil
  rw [hnil.eq_nil_first, append_nil hQ] at hP hCw
  exact (hCw.ne_iff_isPath_of_isSublist le_rfl).mpr hP rfl

lemma IsCycle.exists_compl_trail (hG : G.IsCycle) (hP : G.IsTrail P) : ∃ Q : WList α β,
    G.IsTrail Q ∧ P.last = Q.first ∧ P.first = Q.last ∧ G.IsCyclicWalk (P ++ Q) := by
  obtain ⟨Cw, hCw, hwPre, rfl⟩ := hG.exists_isCyclicWalk_isPrefix_of_isTrail hP
  obtain ⟨Q, hQ, rfl⟩ := isPrefix_iff_exists_eq_append.mp hwPre
  refine ⟨Q, hCw.isTrail.sublist (WList.isSuffix_append_left ..).isSublist, hQ, ?_, hCw⟩
  simpa [WList.IsClosed, hQ] using hCw.isClosed

@[simp]
lemma singleEdge_isForest (hxy : x ≠ y) (e : β) : (Graph.singleEdge x y e).IsForest := by
  rw [isForest_iff_not_isCyclicWalk]
  intro C hC
  obtain ⟨u, f, rfl⟩ | hnt := hC.loop_or_nontrivial
  · obtain ⟨z, z', h⟩ := WList.exists_dInc_of_mem_edge (e := f) (w := .cons u f (.nil u)) (by simp)
    have h' := hC.isWalk.isLink_of_dInc h
    aesop
  refine hnt.firstEdge_ne_lastEdge hC.edge_nodup ?_
  have h_const := hC.isWalk.edgeSet_subset
  simp only [edgeSet_singleEdge, subset_singleton_iff, WList.mem_edgeSet_iff] at h_const
  rw [h_const hnt.nonempty.firstEdge (by simp), h_const hnt.nonempty.lastEdge (by simp)]

lemma IsForest.eq_of_isPath_eq_eq (hG : G.IsForest) (hP : G.IsPath P) (hQ : G.IsPath Q)
    (hfirst : P.first = Q.first) (hlast : P.last = Q.last) : P = Q := by
  by_contra hne
  obtain ⟨C, hC, -⟩ := twoPaths hP hQ hne hfirst hlast
  rw [isForest_iff_not_isCyclicWalk] at hG
  exact hG C hC

lemma IsForest.isPath_of_isTrail (hG : G.IsForest) (hP : G.IsTrail P) : G.IsPath P where
  isWalk := hP.isWalk
  nodup := by
    classical
    induction P with
    | nil u => simp
    | cons u e w ih =>
    obtain ⟨hw, hl, hew⟩ := by simpa only [cons_isTrail_iff] using hP
    simp only [cons_vertex, List.nodup_cons, mem_vertex, ih hw, and_true]
    rintro huw
    refine hG.not_isTour (P := cons u e <| w.prefixUntilVertex u) ⟨?_, by simp, by simp [huw]⟩
    simp only [cons_isTrail_iff, prefixUntilVertex_first]
    have hp := w.prefixUntilVertex_isPrefix u
    exact ⟨hw.sublist hp.isSublist, hl, mt (hp.mem_edge) hew⟩

lemma IsForest.eq_of_isTrail_eq_eq (hG : G.IsForest) (hP : G.IsTrail P) (hQ : G.IsTrail Q)
    (hfirst : P.first = Q.first) (hlast : P.last = Q.last) : P = Q :=
  hG.eq_of_isPath_eq_eq (hG.isPath_of_isTrail hP) (hG.isPath_of_isTrail hQ) hfirst hlast

lemma isForest_of_minimal_connected (hF : Minimal (fun F ↦ (G ↾ F).Connected) F) :
    (G ↾ F).IsForest := by
  rw [isForest_iff_not_isCyclicWalk]
  intro C hC
  obtain ⟨e, he⟩ := hC.nonempty.edgeSet_nonempty
  refine hF.notMem_of_prop_sdiff_singleton (x := e) ?_ (hC.isWalk.edgeSet_subset he).2
  rw [← restrict_deleteEdges]
  exact hF.prop.deleteEdges_singleton_connected <| hC.not_isBridge_of_mem he

lemma IsForest.isShortestPath_of_isPath (hG : G.IsForest) (hP : G.IsPath P) :
    G.IsShortestPath P := by
  obtain ⟨Q, hQ, h1, h2⟩ := hP.isWalk.connBetween_first_last.exists_isShortestPath
  rwa [hG.eq_of_isPath_eq_eq hP hQ.isPath h1.symm h2.symm]

lemma IsForest.loopless (hG : G.IsForest) : G.Loopless := by
  rw [loopless_iff_forall_ne_of_adj]
  rintro x _ ⟨e, he⟩ rfl
  rw [isForest_iff_not_isCyclicWalk] at hG
  exact hG (WList.cons x e (nil x))
  <| by simp [isCyclicWalk_iff, isTour_iff, he.left_mem, isLink_self_iff.1 he]

lemma IsForest.simple (hG : G.IsForest) : G.Simple where
  not_isLoopAt := hG.loopless.not_isLoopAt
  eq_of_isLink e f x y he hf := by
    have := hG.loopless
    rw [isForest_iff_not_isCyclicWalk] at hG
    simpa [isCyclicWalk_iff, isTour_iff, he.left_mem, hf.symm, he, he.adj.ne.symm] using
      hG (cons x e (cons y f (nil x)))

-- set_option backward.isDefEq.respectTransparency false in
lemma isForest_iff_isTrail_eq_eq : G.IsForest ↔ ∀ ⦃P Q⦄, G.IsTrail P → G.IsTrail Q →
    P.first = Q.first → P.last = Q.last → P = Q := by
  refine ⟨fun hG P Q hP hQ hfirst hlast ↦ hG.eq_of_isTrail_eq_eq hP hQ hfirst hlast, fun h ↦ ?_⟩
  have hG : G.Loopless := ⟨fun e x hex ↦ by
    simpa [IsLink.walk] using congrArg length <| h hex.walk_isTrail (Q := nil x)
      (by simp [hex.left_mem]) (by grind [IsLink.walk_first]) (by grind [IsLink.walk_last])⟩
  intro e he
  rw [isBridge_iff_notMem_isCyclicWalk he]
  intro C hC heC
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have hCxy := hC.isWalk.isLink_iff_isLink_of_mem heC |>.mpr hxy
  obtain ⟨P, hP, hP_eq, rfl, rfl⟩ := hC.exists_isPath_toGraph_eq_delete_edge_of_isLink hCxy
  have hQ := hxy.walk_isPath hxy.adj.ne
  rw [h hP.isTrail hQ.isTrail (by simp) (by simp)] at hP_eq
  simpa using congrArg (fun x : Graph α β ↦ e ∈ E(x)) hP_eq

lemma not_isForest_iff_exists_isCycle : ¬ G.IsForest ↔ ∃ H, H.IsCycle ∧ H ≤ G := by
  simp only [isForest_iff_not_isCyclicWalk, not_forall, not_not, isCycle_iff_exists_isCyclicWalk_eq,
    ↓existsAndEq, and_true]
  exact ⟨fun ⟨C, hC⟩ => ⟨C, hC.isCyclicWalk_toGraph, hC.isWalk.toGraph_le⟩,
    fun ⟨H, hH, hHle⟩ => ⟨H, hH.of_le hHle⟩⟩

lemma isForest_iff_not_isCycle : G.IsForest ↔ ∀ H ≤ G, ¬ H.IsCycle := by
  rw [not_isForest_iff_exists_isCycle.not_right]
  grind

/-! ### Cycles and 2-connectivity -/

/-- A `2`-connected graph has, through each of its vertices, a cycle on at least three vertices.

The bound on `V(C)` matters: `IsCycle` is `Minimal (¬ IsForest ·)`, which admits loops and
digons, and neither is `2`-connected. No finiteness instance is needed: the cycle is built, not
extracted. -/
theorem ConnGE.exists_isCycle_le (hG : G.ConnGE 2) (hx : x ∈ V(G)) :
    ∃ C₀, C₀.IsCycle ∧ C₀ ≤ G ∧ x ∈ V(C₀) ∧ 3 ≤ V(C₀).encard := by
  have : (⊥ : Graph α β).Simple := by rw [← noEdge_empty]; infer_instance
  obtain ⟨G', -, hsimp⟩ := exists_isSimpleficationOf_of_le (G := ⊥) (H := G) bot_le
  have hG' : G'.ConnGE 2 := (connGE_iff_le_connectivity 2).2 <|
    connectivity_simplify hsimp ▸ (connGE_iff_le_connectivity 2).1 hG
  have hx' : x ∈ V(G') := hsimp.isSpanningSubgraph.vertexSet_eq ▸ hx
  have hN : 2 ≤ (N(G', x) \ {x}).encard := by
    by_contra hlt
    have hle1 : (N(G', x) \ {x}).encard ≤ 1 := by
      rw [not_le] at hlt
      eomega
    have hSle : ({x} ∪ (N(G', x) \ {x})).encard ≤ 2 := by
      refine (encard_union_le ..).trans ?_
      rw [encard_singleton, add_comm]
      exact (add_le_add_left hle1 1).trans_eq (by norm_num)
    obtain ⟨y, hyV, hyS⟩ := diff_nonempty_of_encard_lt_encard <|
      hSle.trans_lt (hG'.lt_encard_vertexSet le_rfl)
    have hyx : y ≠ x := fun h ↦ hyS (by simp [h])
    exact hlt <| hG'.le_cut <| G'.neighbor_isSep hx'
      ⟨y, hyV, hyx, fun hadj ↦ hyS (Or.inr ⟨hadj, hyx⟩)⟩
  obtain ⟨u, hu, v, hv, huv⟩ :=
    one_lt_encard_iff_nontrivial.1 ((by simp : (1 : ℕ∞) < 2).trans_le hN)
  simp only [mem_sdiff, mem_singleton_iff] at hu hv
  obtain ⟨e1, he1⟩ := hu.1
  obtain ⟨e2, he2⟩ := hv.1
  have huV : u ∈ V(G' - ({x} : Set α)) := by
    simp [vertexSet_deleteVerts, he1.right_mem, hu.2]
  have hvV : v ∈ V(G' - ({x} : Set α)) := by
    simp [vertexSet_deleteVerts, he2.right_mem, hv.2]
  obtain ⟨Q, hQ, rfl, rfl⟩ := (hG'.deleteVert_connected hx').connBetween huV hvV |>.exists_isPath
  simp only [isPath_deleteVerts_iff, disjoint_singleton_right, mem_vertexSet_iff] at hQ
  have hC : G'.IsCyclicWalk ((cons x e1 Q).concat e2 x) :=
    ((show G'.IsPath (cons x e1 Q) from cons_isPath_iff.2 ⟨he1,
      hQ.1, hQ.2⟩).concat_isCyclicWalk) he2.symm <| by
      simp only [cons_edge, List.mem_cons, not_or]
      exact ⟨fun h ↦ huv (he1.right_unique (h ▸ he2)),
        fun he ↦ hQ.2 <| hQ.1.isWalk.vertex_mem_of_edge_mem he he2.inc_left⟩
  refine ⟨_, hC.toGraph_isCycle, hC.isWalk.toGraph_le.trans hsimp.le, ?_, ?_⟩
  · simp [toGraph_vertexSet]
  rw [toGraph_vertexSet, concat_vertexSet_eq, cons_vertexSet, insert_eq_of_mem (mem_insert ..)]
  have hxuv : x ∉ ({Q.first, Q.last} : Set α) := by
    intro hxQ
    simp only [mem_insert_iff, mem_singleton_iff] at hxQ
    exact hxQ.elim (hu.2 ∘ Eq.symm) (hv.2 ∘ Eq.symm)
  have hcard : ({x, Q.first, Q.last} : Set α).encard = 3 := by
    rw [encard_insert_of_notMem hxuv, encard_pair huv]
    norm_num
  rw [← hcard]
  have hf : Q.first ∈ insert x V(Q) :=
    mem_insert_of_mem _ (mem_vertexSet_iff.2 (first_mem (w := Q)))
  have hl : Q.last ∈ insert x V(Q) := mem_insert_of_mem _ (mem_vertexSet_iff.2 (last_mem (w := Q)))
  exact encard_le_encard <|
    insert_subset (mem_insert ..) (insert_subset hf (singleton_subset_iff.2 hl))

lemma ConnGE.not_isForest (hG : G.ConnGE 2) : ¬ G.IsForest := by
  obtain ⟨x, hx⟩ := (hG.connected one_le_two).nonempty
  obtain ⟨C, hC, hle, -, -⟩ := hG.exists_isCycle_le hx
  exact not_isForest_iff_exists_isCycle.2 ⟨C, hC, hle⟩

lemma isCycle_iff_minimal_connGE_two [G.Simple] : G.IsCycle ↔ Minimal (·.ConnGE 2) G := by
  refine ⟨fun hG ↦ ⟨hG.connGE_two hG.three_le_encard_of_simple,
    (fun H hH hle ↦ hG.le_of_le hH.not_isForest hle)⟩, fun hG ↦ ⟨hG.prop.not_isForest,
    fun H hH hle ↦ ?_⟩⟩
  obtain ⟨C, hC, hCle⟩ := not_isForest_iff_exists_isCycle.1 hH
  have : C.Simple := ‹G.Simple›.mono (hCle.trans hle)
  exact (hG.le_of_le (hC.connGE_two hC.three_le_encard_of_simple) (hCle.trans hle)).trans hCle

lemma IsForest.of_deleteEdges_singleton (he : G.IsBridge e) (hG : (G ＼ {e}).IsForest) :
    G.IsForest := by
  by_contra! h
  rw [not_isForest_iff_exists_isCycle] at h
  obtain ⟨H, hH, hHle⟩ := h
  have hHGe : H ≤ G ＼ {e} := by simpa [hHle] using (hH.not_isBridge <| he.anti_of_mem hHle ·)
  rw [isForest_iff_not_isCycle] at hG
  exact hG H hHGe hH

@[mk_iff]
structure IsTree (T : Graph α β) : Prop where
  isForest : T.IsForest
  connected : T.Connected

lemma IsForest.isTree_of_IsCompOf (hG : G.IsForest) (hT : T.IsCompOf G) : T.IsTree :=
  ⟨hG.anti hT.le, hT.connected⟩

lemma IsTree.exists_delete_vertex_isTree [T.Finite] (hT : T.IsTree)
    (hnt : V(T).Nontrivial) : ∃ v ∈ V(T), (T - {v}).IsTree := by
  obtain ⟨x, hxT, hconn⟩ := hT.connected.exists_delete_vertex_connected hnt
  exact ⟨x, hxT, hT.isForest.anti deleteVerts_le, hconn⟩

lemma IsLeaf.delete_isTree (hT : T.IsTree) (hx : T.IsLeaf x) : (T - {x}).IsTree :=
  ⟨hT.isForest.anti deleteVerts_le, hx.delete_connected hT.connected⟩

/-! ### Leaves -/

/-- Every forest with at least one edge has a pendant. -/
lemma IsForest.exists_isPendant [G.EdgeFinite] (hG : G.IsForest) (hne : E(G).Nonempty) :
    ∃ e x, G.IsPendant e x := by
  classical
  have := hG.simple
  rw [isForest_iff_not_isCyclicWalk] at hG
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨x₀, y₀, he₀⟩ := exists_isLink_of_mem_edgeSet he₀
  obtain ⟨P, heP, hmax⟩ := exists_le_maximal_isPath (he₀.walk_isPath he₀.adj.ne)
  simp only [IsLink.walk, le_iff_isSublist] at heP
  cases P with | nil => simp at heP | cons u f P =>
  have ⟨hfuP, hP, huP⟩ : G.IsLink f u P.first ∧ G.IsPath P ∧ u ∉ P := by simpa using hmax.prop
  refine ⟨f, u, hfuP.inc_left.isNonloopAt, fun e ⟨w, he⟩ ↦ ?_⟩
  have hwP := mem_of_adj_first_of_maximal_isPath hmax he.symm.adj
  have h_app := prefixUntilVertex_append_suffixFromVertex P w
  obtain rfl | hne := eq_or_ne w P.first
  · exact Simple.eq_of_isLink he hfuP
  have hP' := IsPath.prefix hmax.prop ((cons u f P).prefixUntilVertex_isPrefix w)
  refine False.elim <| hG _ <| (hP'.cons_isCyclicWalk_of_nontrivial (e := e) ?_ ?_)
  · simpa only [prefixUntilVertex_first, first_cons, prefixUntilVertex_last hwP]
  rw [prefixUntilVertex_cons_of_ne _ he.adj.ne, cons_nontrivial_iff, ← not_nil_iff]
  contrapose! hne
  replace hne := hne.first_eq_last
  rwa [prefixUntilVertex_last, eq_comm, prefixUntilVertex_first] at hne
  rwa [mem_cons_iff, or_iff_right he.adj.ne.symm] at hwP

lemma IsForest.exists_isLeaf [G.EdgeFinite] (hG : G.IsForest) (hne : E(G).Nonempty) :
    ∃ x, G.IsLeaf x := by
  obtain ⟨e, x, h⟩ := hG.exists_isPendant hne
  exact ⟨x, h.isLeaf⟩

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
  rw [← encard_sdiff_singleton_add_one hxV, ← vertexSet_deleteVerts,
    (he.isLeaf.delete_isTree h).encard_vertexSet, he.edgeSet_delete_vertex_eq,
    encard_sdiff_singleton_add_one he.isNonloopAt.edge_mem]
termination_by V(T).encard

lemma IsTree.ncard_vertexSet [T.Finite] (h : T.IsTree) : V(T).ncard = E(T).ncard + 1 := by
  rw [← ENat.natCast_inj, T.vertexSet_finite.cast_ncard_eq, h.encard_vertexSet,
    Nat.cast_add, T.edgeSet_finite.cast_ncard_eq, Nat.cast_one]

lemma IsForest.encard_vertexSet (hG : G.IsForest) :
    V(G).encard = E(G).encard + G.Components.encard := by
  rw [G.eq_sUnion_components, vertexSet_sUnion, ← ENat.tsum_encard_eq_encard_biUnion,
    tsum_congr (β := G.Components) (f := fun C ↦ V(C.1).encard)
      (g := fun C ↦ E(C.1).encard + 1), edgeSet_sUnion, ← ENat.tsum_encard_eq_encard_biUnion,
    ← ENat.tsum_one, tsum_add, ← G.eq_sUnion_components, Components]
  · exact G.components_pairwise_stronglyDisjoint.mono' <| by simp [Pi.le_def, stronglyDisjoint_iff]
  · simp only [Subtype.forall, mem_components_iff_isCompOf]
    exact fun H hle ↦ (hG.isTree_of_IsCompOf hle).encard_vertexSet
  exact G.components_pairwise_stronglyDisjoint.mono' <| by
    simp +contextual [Pi.le_def, stronglyDisjoint_iff]

lemma IsForest.ncard_vertexSet [G.Finite] (hG : G.IsForest) :
    V(G).ncard = E(G).ncard + G.Components.ncard := by
  rw [← ENat.natCast_inj, G.vertexSet_finite.cast_ncard_eq, hG.encard_vertexSet, Nat.cast_add,
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
  rw [Nat.lt_iff_add_one_le, ← ENat.natCast_le_natCast, Nat.cast_add,
    G.vertexSet_finite.cast_ncard_eq, G.edgeSet_finite.cast_ncard_eq]
  exact hG.encard_edgeSet_add_one_le hne
