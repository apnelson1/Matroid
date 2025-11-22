import Matroid.Graph.Simple
import Matroid.Graph.WList.Sublist
import Matroid.Graph.Subgraph.Delete
import Matroid.Graph.Connected.Basic

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {A : Set β}
  {W w w₁ w₂ : WList α β} {S S' T : Set α}

open WList Set

namespace Graph

-- @[mk_iff]
-- structure IsSepSet (G : Graph α β) (S : Set α) : Prop where
--   subset_vx : S ⊆ V(G)
--   not_connected : ¬ (G - S).Connected

def IsSepSet (G : Graph α β) (S : Set α) : Prop :=
  (S ⊆ V(G)) ∧ ¬ (G - S).Connected

def IsMinSepSet (G : Graph α β) (S : Set α) : Prop :=
  IsSepSet G S  ∧ ( ∀ A, IsSepSet G A → S.encard ≤ A.encard )

lemma MinSep_SepSet (hM : IsMinSepSet G S) (hSS' : S'.encard < S.encard) : ¬ IsSepSet G S' := by
  by_contra hc
  grw [hM.2 S' hc, lt_self_iff_false S'.encard] at hSS'
  exact hSS'

lemma IsSep_con (hV : S ⊆ V(G)) (hS : ¬ (G - S).Connected) : IsSepSet G S := ⟨hV, hS⟩

lemma NeIsSep (hV : S ⊆ V(G)) (hS : ¬ IsSepSet G S) : (G - S).Connected := by
  by_contra hc
  exact hS (IsSep_con hV hc)

lemma MinSep_vertexSer_completeGraph [G.Finite] (hV : IsMinSepSet G V(G)) :
    ∀ v w, v ∈ V(G) → w ∈ V(G) → v ≠ w → G.Adj v w := by
  intro v w hv hw hvw
  by_contra hc
  have hle : (V(G) \ {v,w}).encard < V(G).encard :=
     vertexSet_finite.diff.encard_lt_encard
     (HasSubset.Subset.diff_ssubset_of_nonempty (pair_subset hv hw) (insert_nonempty v {w}))
  have h2 := NeIsSep diff_subset (MinSep_SepSet hV hle)
  have hvh : v ∈ V(G - (V(G) \ {v, w})) := by simpa
  have hwh : w ∈ V(G - (V(G) \ {v, w})) := by simpa
  have hnt : (V(G - (V(G) \ {v, w}))).Nontrivial :=
    not_subsingleton_iff.mp fun a ↦ hvw (a hvh hwh)
  have ⟨e, y, hye, hvy⟩ := h2.exists_isLink_of_mem hnt hvh
  obtain rfl : w = y := (show y ∈ V(G) ∧ (y = v ∨ y = w) by simpa using hye.right_mem)
  |>.2.resolve_left hvy |>.symm
  exact hc ⟨e, hye.of_le vertexDelete_le⟩

lemma Connected_comp_Sep (hH : H.IsCompOf (G - S)) (hv : v ∈ V(H)) (huV : u ∈ V(G))
    (hu : u ∉ V(H) ∪ S) : ∃ T : (G - S).Separation, v ∈ T.left ∧ u ∈ T.right := by
  refine ⟨⟨V(H), V(G-S)\V(H), ⟨v, by simpa⟩, ⟨u, by simp_all⟩, disjoint_sdiff_right, ?_, ?_⟩, ?_⟩
  · simpa using (hH.isClosedSubgraph).vertexSet_mono
  · intro x y hx hy
    by_contra hc
    exact (notMem_of_mem_diff hy) (((hH.isClosedSubgraph).mem_iff_mem_of_adj hc).1 hx)
  simp only [mem_union, not_or] at hu
  simp_all

lemma Del_connected_comp_Adj (hH : H.IsCompOf (G - S)) (hv : v ∈ V(H)) (hu : u ∉ V(H) ∪ S) :
    ¬ G.Adj v u := by
  by_contra hc
  simp only [mem_union, not_or] at hu
  have hhe : (G - S).Adj v u := by
    rw [vertexDelete_adj_iff]
    exact ⟨hc, notMem_of_mem_diff (hH.subsetV hv), hu.2⟩
  exact hu.1 (((hH.isClosedSubgraph).mem_iff_mem_of_adj hhe).1 hv)
