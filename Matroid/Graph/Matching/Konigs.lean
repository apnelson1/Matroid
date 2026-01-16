import Matroid.Graph.Matching.Defs

namespace Graph

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}
  {hM : G.IsMatching M} {P P' : WList α β}

open Set symmDiff WList

lemma IsCover.mem_or_mem_or_isLink (h : G.IsCover S) (he : G.IsLink e u v) : u ∈ S ∨ v ∈ S := by
  sorry

lemma IsCover.le_encard (h : G.IsCover S) : τ(G) ≤ S.encard := by
  sorry

lemma IsMinCover.encard (h : G.IsMinCover S) : S.encard = τ(G) := by
  sorry

lemma isMinCover_iff_minimalFor : G.IsMinCover S ↔ MinimalFor G.IsCover Set.encard S :=
  ⟨fun h => ⟨h.toIsCover, fun T hT _ ↦ h.minimal T hT⟩,
    fun h => ⟨h.1, fun T hT ↦ (le_total T.encard S.encard).elim (h.2 hT) id⟩⟩

lemma IsCover.of_vertexDelete (h : (G - X).IsCover S) : G.IsCover ((V(G) ∩ X) ∪ S) where
  subset := sorry
  cover e he := sorry

lemma IsCover.isMinCover_of_encard_eq (hC : G.IsCover S) (h : S.encard = τ(G)) :
    G.IsMinCover S where
  toIsCover := hC
  minimal T hT := by
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

lemma IsPathGraph.konig (h : G.IsPathGraph) : τ(G) = ν(G) := by
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
  have hloopless := hB.loopless
  by_contra! hne
  let P := fun (G : H.Subgraph) ↦ G.val.Bipartite ∧ τ(G.val) ≠ ν(G.val)
  obtain ⟨⟨G, hle⟩, ⟨hB, hne⟩, hMin⟩ := exists_minimal_of_wellFoundedLT P ⟨⟨H, le_refl _⟩, hB, hne⟩
  simp only [Subgraph.le_mk_iff, Subgraph.mk_le_iff, and_imp, Subtype.forall, P] at hB hMin hne
  have : G.Finite := finite_of_le hle
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
  obtain ⟨v, hv⟩ := G.degree_ne_zero_iff_inc (v := u) |>.mp (by omega)
  -- have hlt := G.coverNumber_le_matchingNumber.lt_of_ne hne
  sorry

end Graph
