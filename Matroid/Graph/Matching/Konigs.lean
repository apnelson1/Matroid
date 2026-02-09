import Matroid.Graph.Matching.Defs

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}
  {hM : G.IsMatching M} {P P' : WList α β}

open Set symmDiff WList

namespace Graph

lemma IsCover.mem_or_mem_or_isLink (h : G.IsCover S) (he : G.IsLink e u v) : u ∈ S ∨ v ∈ S := by
  sorry

lemma IsCover.le_encard (h : G.IsCover S) : τ(G) ≤ S.encard := by
  sorry

lemma IsMinCover.encard (h : G.IsMinCover S) : S.encard = τ(G) := by
  sorry

lemma isMinCover_iff_minimalFor : G.IsMinCover S ↔ MinimalFor G.IsCover Set.encard S :=
  ⟨fun h => ⟨h.toIsCover, fun T hT _ ↦ h.min T hT⟩,
    fun h => ⟨h.1, fun T hT ↦ (le_total T.encard S.encard).elim (h.2 hT) id⟩⟩

lemma IsCover.of_vertexDelete (h : (G - X).IsCover S) : G.IsCover ((V(G) ∩ X) ∪ S) where
  subset := sorry
  cover e he := sorry

lemma IsCover.isMinCover_of_encard_eq (hC : G.IsCover S) (h : S.encard = τ(G)) :
    G.IsMinCover S where
  toIsCover := hC
  min T hT := by
    sorry

def IsMatching.mapToCover (hM : G.IsMatching M) (hC : G.IsCover S) : M → S := by
  sorry

lemma IsMatching.mapToCover_inj (hM : G.IsMatching M) (hC : G.IsCover S) :
    Function.Injective (hM.mapToCover hC) := by
  sorry

lemma IsMatching.mapToCover_inc (hM : G.IsMatching M) (hC : G.IsCover S) (he : e ∈ M) :
    G.Inc e (hM.mapToCover hC ⟨e, he⟩) := by
  sorry

lemma matchingNumber_le_coverNumber : ν(G) ≤ τ(G) := by
  sorry

lemma IsMatching.mapToCover_range_eq_of_encard_eq (hC : G.IsCover S) (hM : G.IsMatching M)
    (h : S.encard = M.encard) : range (hM.mapToCover hC) = ⊤ := by
  sorry

lemma coverNumber_mono (hle : G ≤ H) : τ(G) ≤ τ(H) := by
  sorry

end Graph

namespace WList
open Graph

def pathCover : WList α β → Set α
| nil _ => ∅
| cons _ _ (nil v) => {v}
| cons _ _ (cons v _ w) => insert v (pathCover w)

lemma pathCover_subset (P : WList α β) : P.pathCover ⊆ V(P) := by
  match P with
  | nil _ => simp [pathCover]
  | cons _ _ (nil v) => simp [pathCover]
  | cons _ _ (cons v _ w) =>
    simp only [pathCover, cons_vertexSet]
    exact subset_trans (insert_subset_insert w.pathCover_subset) <| subset_insert ..

lemma pathCover_inc {P : WList α β} (hw : P.WellFormed) (he : e ∈ E(P)) :
    e ∈ E(P.toGraph, P.pathCover) := by
  match P with
  | nil _ => simp at he
  | cons u f (nil v) =>
    simp only [cons_edgeSet, nil_edgeSet, insert_empty_eq, mem_singleton_iff,
      mem_setIncEdges_iff] at he ⊢
    subst f
    use v, by simp [pathCover], u
    simp [hw.toGraph_isLink, isLink_cons_iff']
  | cons u e₁ (cons v e₂ w) =>
    simp only [cons_edgeSet, mem_insert_iff, mem_edgeSet_iff] at he
    obtain rfl | rfl | h := he <;> simp only [pathCover, mem_setIncEdges_iff, mem_insert_iff,
    exists_eq_or_imp]
    · left
      use u
      simp [hw, isLink_cons_iff']
    · left
      use w.first
      simp [hw, isLink_cons_iff']
    right
    have hwW : w.WellFormed := hw.of_cons.of_cons
    obtain ⟨x, hx, y, h⟩ := pathCover_inc hwW h
    rw [hwW.toGraph_isLink] at h
    use x, hx, y
    simp [hw.toGraph_isLink, isLink_cons_iff', h]

lemma pathCover_isCover (hw : P.WellFormed) : P.toGraph.IsCover P.pathCover where
  subset := by
    rw [toGraph_vertexSet]
    exact P.pathCover_subset
  cover e he := pathCover_inc hw (by simpa using he)

lemma pathCover_ncard {P : WList α β} (hw : P.vertex.Nodup) :
    P.pathCover.ncard = V(P).ncard / 2 := by
  match P with
  | nil _ => simp [pathCover]
  | cons _ _ (nil v) =>
    simp only [pathCover, ncard_singleton, cons_vertexSet, nil_vertexSet]
    simp only [cons_vertex, nil_vertex, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_false_eq_true, List.nodup_nil, and_self, and_true] at hw
    rw [ncard_pair hw]
  | cons _ _ (cons v _ w) =>
    simp only [cons_vertex, List.nodup_cons, List.mem_cons, mem_vertex, not_or, pathCover,
      cons_vertexSet] at hw ⊢
    obtain ⟨⟨hne, huw⟩, hvw, hw⟩ := hw
    have : w.pathCover.Finite := w.vertexSet_finite.subset w.pathCover_subset
    rw [ncard_insert_of_notMem (fun h ↦ hvw <| w.pathCover_subset h) this,
      ncard_insert_of_notMem (by simp [hne, huw]) (by simp),
      ncard_insert_of_notMem (by simpa) (by simp), pathCover_ncard hw]
    omega

def pathMatching : WList α β → Set β
| nil _ => ∅
| cons _ e (nil _) => {e}
| cons _ e (cons _ _ w) => insert e (pathMatching w)

lemma pathMatching_subset (P : WList α β) : P.pathMatching ⊆ E(P) := by
  match P with
  | nil _ => simp [pathMatching]
  | cons _ e (nil _) => simp [pathMatching]
  | cons _ e (cons _ _ w) =>
    simp only [pathMatching, cons_edgeSet]
    exact insert_subset_insert <| w.pathMatching_subset.trans <| subset_insert ..

end WList

-- lemma Graph.IsPath.pathMatching_isMatching (hP : G.IsPath P) :
--     P.toGraph.IsMatching P.pathMatching where
--   subset := by
--     rw [toGraph_edgeSet]
--     exact P.pathMatching_subset
--   disjoint e f he hf hne := by
--     match P with
--     | nil _ => simp [pathMatching] at he hf
--     | cons _ e (nil _) => simp_all [pathMatching]
--     | cons u a (cons v b w) =>
--     obtain ⟨⟨hw, hvwf, hvw⟩, hauv, huv, huw⟩ := by simpa [← ne_eq] using hP
--     obtain ⟨⟨-, -, hbw⟩, -, hab, haw⟩ := by simpa [← ne_eq] using hP.isTrail
--     simp only [pathMatching, mem_insert_iff] at he hf
--     rw [disjoint_iff_forall_notMem]
--     intro x ⟨x', hx⟩ ⟨y', hy⟩
--     -- simp only [hP.isWalk.wellFormed.toGraph_isLink, isLink_cons_iff', first_cons] at hx hy
--     obtain (rfl| he) := he <;> obtain (rfl| hf) := hf
--     · exact hne rfl
--     · replace hf := w.pathMatching_subset hf
--       have := by simpa [hne.symm] using hy.edge_mem



namespace Graph

lemma IsPathGraph.konig (h : G.IsPathGraph) : τ(G) = ν(G) := by
  have := h.finite
  obtain ⟨P, hP, rfl⟩ := h
  refine matchingNumber_le_coverNumber.antisymm' <| le_trans (b := ↑(V(P).ncard / 2)) ?_ ?_
  · rw [← pathCover_ncard hP.nodup,
    (this.vertexSet_finite.subset <| by simpa using P.pathCover_subset).cast_ncard_eq]
    exact (pathCover_isCover hP.isWalk.wellFormed).le_encard
  sorry

lemma IsCycleGraph.konig (hB : G.Bipartite) (h : G.IsCycleGraph) : τ(G) = ν(G) := by
  sorry

/-!
### König's Matching Theorem
Source: Romeo Rizzi (2000) [cite: 2]

Theorem: Let G be a bipartite graph. Then ν(G) = τ(G).

Proof:
Let G be a minimal counterexample. Then G is connected, is not a circuit, nor a path. [cite: 14]
So, G has a node of degree at least 3. Let u be such a node and v one of its neighbors. [cite: 15]

Case 1: If ν(G \ v) < ν(G). [cite: 16]
By minimality, G \ v has a cover W' with |W'| < ν(G). [cite: 16]
Hence, W' ∪ {v} is a cover of G with cardinality ν(G) at most. [cite: 17]

Case 2: Assume there exists a maximum matching M of G having no edge incident at v. [cite: 18]
Let f be an edge of G \ M incident at u but not at v. [cite: 18]
Let W' be a cover of G \ f with |W'| = ν(G). [cite: 22]
Since no edge of M is incident at v, it follows that W' does not contain v. [cite: 22]
So W' contains u and is a cover of G. [cite: 22]
-/
theorem Konig'sTheorem [H.Finite] (hB : H.Bipartite) : τ(H) = ν(H) := by
  refine of_not_exists_minimal (P := fun H ↦ τ(H) = ν(H)) fun G hle _ hMin ↦ ?_
  push_neg at hMin
  replace hB := hB.of_le hle
  have hcon : G.Connected := by
    /- Otherwise, by def of `Connected`, there is a strictly smaller component of `G`.
    `τ` and `ν` are additive over the components so at least one component must have `τ` or `ν`
    different.
    That component is a smaller counterexample to the theorem, contradicting minimality.-/
    sorry
  obtain ⟨u, hu, hdegu⟩ : ∃ u ∈ V(G), 3 ≤ G.degree u := by
    /- Otherwise, by `isPathGraph_or_isCycleGraph_of_maxDegreeLE`, `G` would be a path or cycle,
    By lemmas above, any path graph or cycle graph has `τ = ν`, contradicting `τ ≠ ν` assumption.-/
    sorry
  obtain ⟨e, v, huv⟩ := G.degree_ne_zero_iff_inc (v := u) |>.mp (by omega)

  -- have hlt := G.coverNumber_le_matchingNumber.lt_of_ne hne
  sorry

end Graph
