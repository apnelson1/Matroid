import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.Graph.Degree.Basic

import Matroid.Exercises.HamiltonianCycle.NeBot

open Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}

@[simp]
lemma eDegree_eq_top (hx : G.eDegree x = ⊤) : ¬ G.LocallyFinite :=
  fun _ ↦ eDegree_ne_top hx

-- TODO: this should be added directly to the definition
attribute [mk_iff] Graph.LocallyFinite

lemma locallyFinite_of_eDegree_ne_top (hG : ∀ x, G.eDegree x ≠ ⊤) : G.LocallyFinite := by
  by_contra! hcon
  simp [locallyFinite_iff] at hcon
  obtain ⟨x, hx⟩ := hcon
  refine hG x ?_
  rw [eq_top_iff]
  suffices {e | G.Inc e x}.encard = ⊤ by
   rw [←this]
   exact G.encard_setOf_inc_le_eDegree x
  simpa

lemma forall_eDegree_ne_top_iff : (∀ x, G.eDegree x ≠ ⊤) ↔ G.LocallyFinite :=
  ⟨locallyFinite_of_eDegree_ne_top, fun _ _ ↦ eDegree_ne_top⟩

lemma exists_eDegree_eq_top_of_not_locallyFinite (hG : ¬ G.LocallyFinite) :
    ∃ x, G.eDegree x = ⊤ := by
  simp [←forall_eDegree_ne_top_iff] at hG
  assumption

lemma exists_eDegree_eq_top_iff : (∃ x, G.eDegree x = ⊤) ↔ ¬ G.LocallyFinite := by
  refine ⟨fun ⟨_, hx⟩ ↦ eDegree_eq_top hx, exists_eDegree_eq_top_of_not_locallyFinite⟩

noncomputable def minEDegree (G : Graph α β) : ℕ∞ :=
  ⨅ x ∈ V(G), G.eDegree x

-- G.minDegree returns the minimum degree of its vertices if G is finite, else it returns 0
noncomputable def minDegree (G : Graph α β) : ℕ :=
  G.minEDegree.toNat

-- if G is Nonempty and LocallyFinite, then the two definitions agree
lemma natCast_minDegree_eq [G.LocallyFinite] (hG : G.NeBot) :(G.minDegree : ℕ∞) = G.minEDegree := by
  simp only [minDegree, minEDegree, ENat.coe_toNat_eq_self, ne_eq, iInf_eq_top, eDegree_ne_top,
    imp_false, not_forall, not_not]
  rwa [NeBot_iff_vertexSet_nonempty] at hG

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

-- TODO: the prime versions of these lemmas only currently exist because Graph.Nonempty
-- doesn't exist.
lemma exists_vertex_minEDegree (hG : G ≠ ⊥) : ∃ x ∈ V(G), G.eDegree x = G.minEDegree := by
  apply ENat.exists_eq_biInf
  exact ne_bot_iff.mp hG

lemma exists_vertex_minEDegree' (hG : V(G).Nonempty) : ∃ x ∈ V(G), G.eDegree x = G.minEDegree :=
  ENat.exists_eq_biInf hG _

lemma exists_vertex_minDegree (hG : G ≠ ⊥) : ∃ x ∈ V(G), G.degree x = G.minDegree := by
  obtain ⟨x, hxG, hx⟩ := exists_vertex_minEDegree hG
  refine ⟨x, hxG, ?_⟩
  simp [degree, minDegree, hx]

lemma exists_vertex_minDegree' (hG : V(G).Nonempty) : ∃ x ∈ V(G), G.degree x = G.minDegree := by
  obtain ⟨x, hxG, hx⟩ := exists_vertex_minEDegree' hG
  refine ⟨x, hxG, ?_⟩
  simp [degree, minDegree, hx]

-- TODO: this should be moved to Graph.Basic
lemma setOf_adj_subset {G : Graph α β} (x : α) : {y | G.Adj x y} ⊆ V(G) := by
  intro y hy
  simp at hy
  exact hy.right_mem

-- TODO: this should be moved to Graph.Basic
-- maybe this should be `Neighbor`?
lemma encard_setOf_adj_le {G : Graph α β} [G.Simple] {x : α} (h : x ∈ V(G)) :
    {y | G.Adj x y}.encard + 1 ≤ V(G).encard := by
  have : ({x} : Set α).encard = 1 := by simp
  rw [← this]; clear this
  rw [←Set.encard_union_eq]
  swap
  · simp; apply not_adj_self
  apply encard_le_encard
  simp
  refine insert_subset h ?_
  exact setOf_adj_subset _

lemma eDegree_le_encard {G : Graph α β} [G.Simple] {x : α} (h : x ∈ V(G)) :
    G.eDegree x + 1 ≤ V(G).encard := by
  have solver := G.incAdjEquiv x
  simp [eDegree_eq_encard_inc]
  change {e // e ∈ {e | G.Inc e x}} ≃ {y // y ∈ {y | G.Adj x y}} at solver
  repeat rw [←coe_eq_subtype] at solver
  rw [solver.encard_eq]
  exact encard_setOf_adj_le h

lemma degree_le_ncard {G : Graph α β} [G.Simple] [G.Finite] {x : α} (h : x ∈ V(G)) :
    G.degree x + 1 ≤ V(G).ncard := by
  suffices hyp : G.eDegree x + 1 ≤ V(G).encard
  · rw [←natCast_degree_eq, ←Set.Finite.cast_ncard_eq vertexSet_finite] at hyp
    enat_to_nat!; assumption
  exact eDegree_le_encard h

lemma degree_lt_ncard {G : Graph α β} [G.Simple] [G.Finite] {x : α} (h : x ∈ V(G)) :
    G.degree x < V(G).ncard := by
  linarith [degree_le_ncard h]

lemma minDegree_lt_ncard {G : Graph α β} [G.Simple] [G.Finite] (hNeBot : G.NeBot) :
    G.minDegree < V(G).ncard := by
  have ⟨v,hvG, vspec⟩ := G.exists_vertex_minDegree hNeBot
  rw [←vspec]
  apply degree_lt_ncard
  tauto

lemma minEDegree_ge_one_of_connected_nontrivial (hConn : G.Connected)
    (hNontrivial : 1 < V(G).encard) : ∀ x ∈ V(G), 1 ≤ G.eDegree x := by
  have hnt : V(G).Nontrivial := one_lt_encard_iff_nontrivial.mp hNontrivial
  by_contra! hyp
  obtain ⟨x, hxG, hx⟩ := hyp
  rw [connected_iff_forall_exists_adj (by use x)] at hConn
  have : {x} ⊂ V(G) := ⟨by simpa, (not_nontrivial_singleton <| hnt.mono ·)⟩
  obtain ⟨y, ⟨hyG, hne⟩, hadj⟩ := by simpa using hConn _ this
  rw [ENat.lt_one_iff_eq_zero, eDegree_eq_zero_iff_adj] at hx
  exact hx y hadj

lemma unique_neighbor_of_eDegree_eq_one (hx : G.eDegree x = 1) (hxy : G.Adj x y) (hxz : G.Adj x z) :
    y = z := by
  have heq := hx ▸ G.eDegree_eq_encard_add_encard x
  have no_loops : {e | G.IsLoopAt e x}.encard = 0 := by
    by_contra! hyp
    rw [←ENat.one_le_iff_ne_zero] at hyp
    replace hyp : 2 ≤ 2 * {e | G.IsLoopAt e x}.encard := le_mul_of_one_le_right' hyp
    have hle : 2 * {e | G.IsLoopAt e x}.encard ≤ 1 := by
      simp [heq]
    simpa using hyp.trans hle
  rw [no_loops, mul_zero, zero_add, eq_comm, encard_eq_one] at heq
  obtain ⟨e, he⟩ := heq
  have setOf_inc_le : {e | G.Inc e x} ⊆ {e} := by
    simp only [inc_iff_isLoopAt_or_isNonloopAt, subset_singleton_iff, mem_setOf_eq]
    rintro f (h|h)
    · suffices f ∈ {e | G.IsLoopAt e x} by simp_all
      exact h
    suffices f ∈ {e | G.IsNonloopAt e x} by simp_all
    exact h
  simp only [subset_singleton_iff, mem_setOf_eq] at setOf_inc_le
  obtain ⟨xy, hxy⟩ := hxy
  obtain ⟨xz, hxz⟩ := hxz
  obtain rfl : xy = e := setOf_inc_le _ hxy.inc_left
  obtain rfl : xz = xy := setOf_inc_le _ hxz.inc_left
  exact hxy.right_unique hxz
