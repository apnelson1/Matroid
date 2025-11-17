import Matroid.Graph.Simple
import Matroid.Graph.WList.Sublist
import Matroid.Graph.Subgraph.Delete
import Matroid.Graph.Connected.Defs


/-
This file defined predicates stating that an abstract walk `w` is a walk/trail/path of a graph `G`.
-/

variable {α β : Type*} [CompleteLattice α] {x y z u v : α} {e f : β} {G H : Graph α β} {A : Set β}
  {W w w₁ w₂ : WList α β} {S T : Set α}

open Graph WList Set

namespace Graph

def IsSepSet (G : Graph α β) (S : Set (α)) : Prop :=
  (S ⊆ V(G)) ∧ ¬ (G - S).Connected

def IsMinSepSet (G : Graph α β) (S : Set (α)) : Prop :=
  IsSepSet G S  ∧ ( ∀ A, IsSepSet G A → S.encard ≤ A.encard )

lemma MinSep_SepSet {G : Graph α β} (S : Set α) (S' : Set α) (hM : IsMinSepSet G S)
    (hSS' : S'.encard < S.encard) : ¬  IsSepSet G S' := by
  by_contra hc
  have h1 := hM.2 S' hc
  grw [h1] at hSS'
  exact (lt_self_iff_false S'.encard).mp hSS'

lemma IsSep_con {G : Graph α β} (S : Set (α)) (hV : S ⊆ V(G)) (hS : ¬ (G - S).Connected) :
    IsSepSet G S := by
  refine ⟨hV, hS ⟩

lemma NeIsSep {G : Graph α β} (S : Set (α)) (hV : S ⊆ V(G)) (hS : ¬ IsSepSet G S) :
    (G - S).Connected := by
  by_contra hc
  exact hS (IsSep_con S hV hc)

lemma MinSep_vertexSer_completeGraph {G : Graph α β} [G.Finite] (hV : IsMinSepSet G V(G))
    : ∀ v w, v ∈ V(G) → w ∈ V(G) → v ≠ w → G.Adj v w := by
  intro v w hv hw hvw
  by_contra hc
  have hle : (V(G) \ {v,w}).encard < V(G).encard := by
    refine Finite.encard_lt_encard (Finite.diff vertexSet_finite)
     (HasSubset.Subset.diff_ssubset_of_nonempty (pair_subset hv hw ) (insert_nonempty v {w}))
  have h2 := NeIsSep (V(G) \ {v, w}) (diff_subset ) (MinSep_SepSet V(G) (V(G)\{v,w}) hV hle )
  have hvh : v ∈ V(G - (V(G) \ {v, w})) := by simpa
  have hwh : w ∈ V(G - (V(G) \ {v, w})) := by simpa
  have hnt : (V(G - (V(G) \ {v, w}))).Nontrivial := by
    exact not_subsingleton_iff.mp fun a ↦ hvw (a hvh hwh)
  have ⟨e, y, hye, hvy ⟩ := Connected.exists_isLink_of_mem h2 hnt hvh
  have hwy : w = y := by
    have hyyy : y ∈ V(G - (V(G) \ {v, w})) := IsLink.right_mem hye
    simp at hyyy
    have := hyyy.2
    obtain (ha | hb) := hyyy.2
    exact False.elim (hvy ha)
    exact id (Eq.symm hb)
  have h : G.Adj v w := by
    have hrw : G[V(G) \ (V(G) \ {v, w})] =  G - (V(G) \ {v, w}) :=
        vertexDelete_def G (V(G) \ {v, w})
    have hee : e ∈ E(G[V(G) \ (V(G) \ {v, w})]) := by
      rw [hrw]
      exact IsLink.edge_mem hye
    have he1 :  G[V(G) \ (V(G) \ {v, w})].IsLink e v w := by
      rw [(hrw)]
      exact (IsLink.isLink_iff_eq hye).mpr hwy
    refine ⟨ e, ((induce_isLink_iff_of_mem_edgeSet hee).1 he1) ⟩
  exact hc h

lemma Connected_comp_Sep {G : Graph α β} (H : Graph α β) (S : Set (α))
    (hH : H.IsCompOf (G - S )) (v w : α) (hv : v ∈ V(H)) (hwV : w ∈ V(G)) (hw : w ∉ V(H) ∪ S) :
    ∃ T : (G - S).Separation, v ∈ T.left ∧ w ∈ T.right := by

  refine ⟨⟨V(H), V(G-S)\V(H) , ⟨v, by simpa⟩ , ⟨w, ?_⟩, disjoint_sdiff_right , ?_, ?_ ⟩,?_⟩
  · simp at hw
    simp
    refine ⟨ ⟨ hwV, hw.2 ⟩, hw.1 ⟩
  simp
  · have hh : V(H) ⊆ V(G - S) :=  (hH.isClosedSubgraph).vertexSet_mono
    simp only [vertexDelete_vertexSet] at hh
    exact hh
  · intro x y hx hy
    by_contra hc
    exact (notMem_of_mem_diff hy ) (((hH.isClosedSubgraph).mem_iff_mem_of_adj hc).1 hx )
  simp
  simp at hw
  refine ⟨ hv, ⟨ hwV, hw.2 ⟩, hw.1 ⟩

lemma Del_connected_comp_Adj {G : Graph α β} (H : Graph α β) (S : Set (α))
    (hH : H.IsCompOf (G - S )) (v w : α) (hv : v ∈ V(H)) (hw : w ∉ V(H) ∪ S) :
    ¬ G.Adj v w := by
  by_contra hc
  simp only [mem_union, not_or] at hw
  have hhe : (G - S).Adj v w := by
    simp
    refine ⟨hc, ?_, hw.2 ⟩
    · have h1 : V(H) ⊆ V(G - S) := IsCompOf.subsetV hH
      have h :=  vertexDelete_vertexSet G S
      rw [h] at h1
      exact notMem_of_mem_diff (h1 hv)
  exact hw.1 (((hH.isClosedSubgraph).mem_iff_mem_of_adj hhe).1 hv)
