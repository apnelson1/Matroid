import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.Graph.Degree.Basic
import Matroid.Graph.Connected.Basic

open Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}

noncomputable def minEDegree (G : Graph α β) : ℕ∞ :=
  ⨅ x ∈ V(G), G.eDegree x

-- G.minDegree returns the minimum degree of its vertices if G is finite, else it returns 0
noncomputable def minDegree (G : Graph α β) : ℕ :=
  G.minEDegree.toNat

-- if G is Nonempty and LocallyFinite, then the two definitions agree
lemma natCast_minDegree_eq [G.LocallyFinite] (hG : V(G).Nonempty) :
    (G.minDegree : ℕ∞) = G.minEDegree := by
  simpa [minDegree, minEDegree]

@[simp]
lemma minEDegree_bot : (⊥ : Graph α β).minEDegree = ⊤ := by
  simp [minEDegree]

lemma minEDegree_eq_top (hG : G.minEDegree = ⊤) : G = ⊥ ∨ ¬ G.LocallyFinite := by
  by_contra! hcon
  obtain ⟨⟨x, hx⟩, hcon₂⟩ := hcon
  simp only [minEDegree, iInf_eq_top, eDegree_ne_top, imp_false] at hG
  exact hG _ hx

@[simp]
lemma minDegree_bot : (⊥ : Graph α β).minDegree = 0 := by
  simp [minDegree]

-- minEDegree is minimal among all degrees
lemma minEDegree_le_eDegree (hx : x ∈ V(G)) : G.minEDegree ≤ G.eDegree x :=
  biInf_le G.eDegree hx

lemma minDegree_le_degree [G.LocallyFinite] (hx : x ∈ V(G)) : G.minDegree ≤ G.degree x :=
  ENat.toNat_le_toNat (minEDegree_le_eDegree hx) eDegree_ne_top

-- TODO: shuffle into ENat
lemma ENat.exists_eq_biInf {S : Set ι} (hS : S.Nonempty) (f : ι → ℕ∞) :
    ∃ a ∈ S, f a = ⨅ x ∈ S, f x := by
  rw [←sInf_image]
  exact csInf_mem (hS.image f)

lemma exists_vertex_minEDegree (hG : V(G).Nonempty) : ∃ x ∈ V(G), G.eDegree x = G.minEDegree :=
  ENat.exists_eq_biInf hG _

lemma exists_vertex_minDegree (hG : V(G).Nonempty) : ∃ x ∈ V(G), G.degree x = G.minDegree := by
  obtain ⟨x, hxG, hx⟩ := exists_vertex_minEDegree hG
  refine ⟨x, hxG, ?_⟩
  simp [degree, minDegree, hx]

-- TODO: this should be moved to Graph.Basic
lemma encard_neighbors_le [G.Simple] (h : x ∈ V(G)) : N(G, x).encard + 1 ≤ V(G).encard := by
  rw [show 1 = ({x} : Set α).encard by simp, ← Set.encard_union_eq (by simp [not_adj_self])]
  exact encard_le_encard <| union_subset (neighbor_subset ..) (by simpa)

lemma eDegree_le_encard [G.Simple] (h : x ∈ V(G)) : G.eDegree x + 1 ≤ V(G).encard := by
  have solver : E(G, x) ≃ N(G, x) := G.incAdjEquiv x
  simp only [eDegree_eq_encard_inc, ge_iff_le]
  rw [solver.encard_eq]
  exact encard_neighbors_le h

lemma degree_le_ncard [G.Simple] [G.Finite] (h : x ∈ V(G)) : G.degree x + 1 ≤ V(G).ncard := by
  suffices hyp : G.eDegree x + 1 ≤ V(G).encard by
    rw [←natCast_degree_eq, ←Set.Finite.cast_ncard_eq vertexSet_finite] at hyp
    enat_to_nat!; assumption
  exact eDegree_le_encard h

lemma degree_lt_ncard [G.Simple] [G.Finite] (h : x ∈ V(G)) : G.degree x < V(G).ncard := by
  linarith [degree_le_ncard h]

lemma minEDegree_le_encard [G.Simple] (hne : V(G).Nonempty) : G.minEDegree + 1 ≤ V(G).encard := by
  obtain ⟨x, hx⟩ := hne
  have := eDegree_le_encard hx
  have h1 := minEDegree_le_eDegree hx
  enat_to_nat!
  omega

lemma minDegree_lt_ncard [G.Simple] [G.Finite] (hNe : V(G).Nonempty) :G.minDegree < V(G).ncard := by
  have ⟨v, hvG, vspec⟩ := G.exists_vertex_minDegree hNe
  rw [← vspec]
  exact degree_lt_ncard hvG

lemma unique_neighbor_of_eDegree_eq_one (hx : G.eDegree x = 1) (hxy : G.Adj x y) (hxz : G.Adj x z) :
    y = z := by
  have heq := hx ▸ G.eDegree_eq_encard_add_encard x
  have no_loops : {e | G.IsLoopAt e x}.encard = 0 := by
    enat_to_nat!
    omega
  rw [no_loops, mul_zero, zero_add, eq_comm] at heq
  simp only [encard_eq_zero, Set.ext_iff, mem_setOf_eq, mem_empty_iff_false, iff_false] at no_loops
  have h : {e | G.Inc e x}.Subsingleton := by
    intro e he f hf
    simp only [inc_iff_isLoopAt_or_isNonloopAt, no_loops, false_or, mem_setOf_eq] at he hf
    exact encard_le_one_iff.mp heq.le e f he hf
  have hh : N(G, x).Subsingleton := by
    rw [← encard_le_one_iff_subsingleton] at h ⊢
    exact encard_adj_le_encard_inc.trans h
  exact hh hxy hxz
