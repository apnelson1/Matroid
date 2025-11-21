import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Qq
-- TODO: remember to remove this Loogle import at the end of the project
import Loogle.Find

import Matroid.Graph.Connected.Basic
import Matroid.Graph.Connected.Component
import Matroid.Graph.Connected.Separating
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Basic
import Matroid.Graph.Independent
import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Tree
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Walk.Path
import Matroid.Graph.WList.Defs
import Matroid.Graph.WList.Cycle

open Qq Lean Meta Elab Tactic
open WList Set

section NonGraphThings

variable {α β : Type*} {P₀ P₁ : WList α β} {e f : β}

lemma finite_of_ncard_nonzero {s : Set α} (h : s.ncard ≠ 0) : s.Finite := by
  by_contra hyp
  replace hyp : s.Infinite := hyp
  apply h
  exact Infinite.ncard hyp

lemma finite_of_ncard_positive {s : Set α} (h : 0 < s.ncard) : s.Finite := by
  apply finite_of_ncard_nonzero ; linarith

lemma minimal_is_lower_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Minimal P x) :
    ∀ y, P y → x ≤ y := by
  intro y hy
  simp [Minimal] at h
  obtain (_|_) := le_total x y
  · assumption
  · tauto

lemma minimalFor_is_lower_bound
    {ι} [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι} (h : MinimalFor P f i) :
    ∀ j, P j → f i ≤ f j := by
  intro j hj
  simp [MinimalFor] at h
  obtain (_|_) := le_total (f i) (f j)
  · assumption
  · tauto

end NonGraphThings

namespace Graph

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}

/- Theorem 10.1.1 (Dirac 1952)
Every graph with n >= 3 vertices and minimum degree at least n/2 has a Hamiltonian cycle.
-/

-- INITIAL DEFINITIONS

def NeBot (G : Graph α β) : Prop :=
  G ≠ ⊥

@[simp]
lemma NeBot_iff_vertexSet_nonempty {G : Graph α β} :
    G.NeBot ↔ V(G).Nonempty := by
  simp [NeBot]

lemma vertexSet_nonempty_of_NeBot {G : Graph α β} (h : G.NeBot) :
    V(G).Nonempty := by
  rwa [←NeBot_iff_vertexSet_nonempty]

lemma NeBot_iff_encard_positive {G : Graph α β} :
    G.NeBot ↔ 0 < V(G).encard := by
  simp

lemma NeBot_of_ncard_positive {G : Graph α β} (h : 0 < V(G).ncard) : G.NeBot := by
  rw [NeBot, ne_eq, ←vertexSet_eq_empty_iff, ←ne_eq, ←Set.nonempty_iff_ne_empty]
  apply nonempty_of_ncard_ne_zero
  linarith

@[simp]
lemma eDegree_eq_top (hx : G.eDegree x = ⊤) : ¬ G.LocallyFinite :=
  fun _ ↦ eDegree_ne_top hx

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
lemma natCast_minDegree_eq (G : Graph α β) [G.LocallyFinite] (hG : G.NeBot) :
    (G.minDegree : ℕ∞) = G.minEDegree := by
  simp [minDegree, minEDegree]
  rw [NeBot_iff_vertexSet_nonempty] at hG
  exact hG

lemma minEDegree_eq_top_of_empty (hG : G = ⊥) :
    G.minEDegree = ⊤ := by
  simp only [minEDegree]
  have : V(G) = ∅ := by simpa
  simp [this]

lemma minEDegree_eq_top (hG : G.minEDegree = ⊤) :
    G = ⊥ ∨ ¬ G.LocallyFinite := by
  by_contra! hcon
  obtain ⟨hcon₁, hcon₂⟩ := hcon
  have ⟨x, hx⟩ : V(G).Nonempty := by
    rw [←NeBot_iff_vertexSet_nonempty]
    exact hcon₁
  simp [minEDegree] at hG
  specialize hG _ hx
  assumption

lemma minDegree_eq_zero_of_empty (hG : G = ⊥) :
    G.minDegree = 0 := by
  unfold minDegree
  simp [minEDegree_eq_top_of_empty hG]

-- minEDegree is minimal among all degrees
lemma minEDegree_le_eDegree (hx : x ∈ V(G)) :
    G.minEDegree ≤ G.eDegree x := by
  exact biInf_le G.eDegree hx

lemma minDegree_le_degree [G.LocallyFinite] (hx : x ∈ V(G)) :
    G.minDegree ≤ G.degree x := by
  simp [minDegree,  minEDegree, degree]
  refine ENat.toNat_le_toNat (minEDegree_le_eDegree hx) eDegree_ne_top

-- TODO: shuffle into ENat
lemma ENat.exists_eq_biInf {ι} {S : Set ι} (hS : S.Nonempty) (f : ι → ℕ∞) :
    ∃ a ∈ S, f a = ⨅ x ∈ S, f x := by
  rw [←sInf_image]
  exact csInf_mem (hS.image f)

lemma exists_vertex_minEDegree (hG : G ≠ ⊥) : ∃ x ∈ V(G), G.eDegree x = G.minEDegree := by
  unfold minEDegree
  apply ENat.exists_eq_biInf
  simpa

lemma exists_vertex_minDegree (hG : G ≠ ⊥) : ∃ x ∈ V(G), G.degree x = G.minDegree := by
  obtain ⟨x, hxG, hx⟩ := exists_vertex_minEDegree hG
  refine ⟨x, hxG, ?_⟩
  simp [degree, minDegree]
  tauto

-- MORE THINGS

lemma degree_lt_vertexCount {G : Graph α β} [G.Simple] {v : α} (h : v ∈ V(G)) :
    G.degree v < V(G).ncard := by sorry

lemma minDegree_lt_vertexCount {G : Graph α β} [G.Simple] (hNeBot : G.NeBot) :
    G.minDegree < V(G).ncard := by
  have ⟨v,hvG, vspec⟩ := G.exists_vertex_minDegree hNeBot
  rw [←vspec]
  apply degree_lt_vertexCount
  tauto

--The exercises start here
--I added this lemma. Seems important. Do we need to prove it or already exists but is not working?
lemma isCompOf_subset (G H : Graph α β) (hHG : H.IsCompOf G) : V(H) ⊆ V(G) := by
  have hclo : H ≤c G := by
      --Richard already has a lemma for this
      exact IsCompOf.isClosedSubgraph hHG
  exact IsClosedSubgraph.vertexSet_mono hclo
  -- Use IsClosedSubgraph.vertexSet_mono to finsih


lemma minDegree_le_minDegree_of_isCompOf (G H : Graph α β) [G.Finite] (hHG : H.IsCompOf G) :
    G.minDegree ≤ H.minDegree := by
    obtain ⟨v, hv, hveq⟩ := H.exists_vertex_minDegree
      (NeBot_iff_vertexSet_nonempty.2 hHG.nonempty)
    rw [←hveq]
    have hvG : v ∈ V(G) := by
      --I cheated and added the lemma above
      have hcheat : V(H) ⊆ V(G) := isCompOf_subset G H hHG
      -- Have should follow now
      exact hcheat hv
    have hclo : H ≤c G := by
      --Richard already has a lemma for this
      exact IsCompOf.isClosedSubgraph hHG
    have heq : H.degree v = G.degree v := by
      --Use IsClosedSubgraph.degree_eq
      exact IsClosedSubgraph.degree_eq hHG.isClosedSubgraph hv
    rw [heq]
    exact minDegree_le_degree hvG

  --Somhow I did this exercise instead
lemma minDegree_le_minDegree_of_Subgraph (G H : Graph α β) [G.Finite] (hHG : H ≤s G) :
    H.minDegree ≤ G.minDegree := by
    --The following two haves are used in the obtain.
    --First one follows from H being a component of a finite graph
  have Hfin: H.Finite := finite_of_le hHG.le
  obtain (hne | hni) := Classical.em (H.NeBot)
  · have gne : G.NeBot := by
      rw [NeBot_iff_vertexSet_nonempty]
      rw [NeBot_iff_vertexSet_nonempty] at hne
      have VHseVG : V(H) ⊆ V(G) := hHG.le.vertex_subset
      exact Nonempty.mono VHseVG hne
    obtain ⟨v, hv, hveq⟩ := H.exists_vertex_minDegree hne
    rw [←hveq]
    have hvG: v ∈ V(G) := hHG.le.vertex_subset hv
    obtain ⟨w, gw, gweq⟩ := G.exists_vertex_minDegree gne
    have wvH: w ∈ V(H) := by
      rw [hHG.vertexSet_eq]
      exact gw
    have h1 : H.degree w ≤ G.degree w := degree_mono hHG.le w
    rw [← gweq, hveq]
    have h2 : H.minDegree ≤ H.degree w := minDegree_le_degree wvH
    linarith


  --This is the case the graph is empty. Richard has a nice lemma that if the graph is
  --empty or infinite then the min degree is 0. We just need to rw that
  rw [H.minDegree_eq_zero_of_empty (by simp at hni; assumption)]
  exact Nat.zero_le G.minDegree

lemma ge_two_components_of_not_connected {G : Graph α β} (hNeBot : G.NeBot) (h : ¬ G.Connected) :
    2 ≤ G.Components.encard := by
  -- G has a vertex
  obtain ⟨ v, hv ⟩ := vertexSet_nonempty_of_NeBot hNeBot
  -- I cheated here, but this lemma is missing and I'm guessing it should be in connected
  obtain ⟨ H, hH, hvH ⟩ := G.exists_IsCompOf_vertex_mem hv
  have hbig : ∃ w ∈ V(G), w ∉ V(H) := by
    by_contra! hw
    --Our contradiction is that G is connected. The following have is the hardest.
    have hcon : G = H := by
    -- I think I went overboard on this refine, try refine ext_inc ?_ ?_ and see what happens
      refine ext_inc (Subset.antisymm_iff.mpr ⟨hw, isCompOf_subset G H hH ⟩  ) ?_
      intro e x
      -- Here is a one line proof, try to write this in steps.
      refine ⟨ fun hh ↦ (Inc.of_isClosedSubgraph_of_mem hh (IsCompOf.isClosedSubgraph hH)
          (hw x (Inc.vertex_mem hh))), fun hh ↦ (Inc.of_le hh (IsCompOf.le hH)) ⟩
    rw [ hcon ] at hH
    -- Just state the contradiction
    sorry
  obtain ⟨ w, hw, hwH ⟩ := hbig
  obtain ⟨ H₁, hH1, hvH1 ⟩ := G.exists_IsCompOf_vertex_mem hw
  have : H ≠ H₁ := by sorry
  sorry

def ConnectivityGE (G : Graph α β) (k : ℕ∞) : Prop :=
  ∀ S, S.encard < k → (G - S).Connected

lemma minEDegree_ge_one_of_connected_nontrivial
    {G : Graph α β} (hConn : G.Connected) (hNontrivial : 1 < V(G).encard) :
    ∀ x ∈ V(G), 1 ≤ G.eDegree x := by
  by_contra! hyp; obtain ⟨x, hxG, hx⟩ := hyp
  rw [ENat.lt_one_iff_eq_zero] at hx
  rw [connected_iff_forall_exists_adj] at hConn
    <;> [skip; use x]
  specialize hConn {x}
  have : {x} ⊂ V(G) := by
    refine ⟨by simp; tauto, ?_⟩
    intro bad
    have := Set.encard_le_encard bad
    have := hNontrivial.trans_le this
    simp at this
  simp at hConn
  specialize hConn this; clear this
  obtain ⟨y, ⟨hyG, hne⟩, hadj⟩ := hConn
  rw [eDegree_eq_zero_iff_adj] at hx
  exact hx y hadj

lemma unique_neighbor_of_eDegree_eq_one
    {G : Graph α β} {x : α} (hx : G.eDegree x = 1)
    {y z : α} (hxy : G.Adj x y) (hxz : G.Adj x z) :
    y = z := by
  have heq := G.eDegree_eq_encard_add_encard x
  rw [hx] at heq
  have no_loops : {e | G.IsLoopAt e x}.encard = 0 := by
    by_contra! hyp
    rw [←ENat.one_le_iff_ne_zero] at hyp
    replace hyp : 2 ≤ 2 * {e | G.IsLoopAt e x}.encard :=
      le_mul_of_one_le_right' hyp
    have hle : 2 * {e | G.IsLoopAt e x}.encard ≤ 1 := by
      simp [heq]
    have := hyp.trans hle
    simp at this
  rw [no_loops] at heq; simp at heq; symm at heq
  rw [Set.encard_eq_one] at heq
  obtain ⟨e, he⟩ := heq
  have setOf_inc_le : {e | G.Inc e x} ⊆ {e} := by
    simp [inc_iff_isLoopAt_or_isNonloopAt]
    rintro f (h|h) <;> [exfalso; skip]
    · suffices f ∈ {e | G.IsLoopAt e x} by simp_all
      exact h
    suffices f ∈ {e | G.IsNonloopAt e x} by simp_all
    exact h
  simp at setOf_inc_le
  obtain ⟨xy, hxy⟩ := hxy
  obtain ⟨xz, hxz⟩ := hxz
  suffices xy = xz by
    subst this; exact IsLink.right_unique hxy hxz
  have hxy' : xy = e := setOf_inc_le _ hxy.inc_left
  have hxz' : xz = e := setOf_inc_le _ hxz.inc_left
  simp_all

lemma exists_isSepSet_of_isTree
    {T : Graph α β} (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ S, IsSepSet T S ∧ S.encard = 1 := by
  have hMinDeg : ∀ x ∈ V(T), 1 ≤ T.eDegree x := by
    refine minEDegree_ge_one_of_connected_nontrivial hT.connected ?_
    suffices (1 : ℕ∞) < 3 by
      exact this.trans_le hV
    simp
  -- we show there exists a vertex x of degree at least 2, in which case
  -- the singleton {x} is exactly our sepset
  have ⟨x, hxT, hx⟩ : ∃ x ∈ V(T), 2 ≤ T.eDegree x := by
    by_contra! hyp
    replace hyp : ∀ x ∈ V(T), T.eDegree x = 1 := by
      intro x hxT
      specialize hyp _ hxT
      specialize hMinDeg _ hxT
      change T.eDegree x < 1 + 1 at hyp
      rw [ENat.lt_add_one_iff] at hyp
        <;> [exact hyp.antisymm hMinDeg; simp]
    clear hMinDeg
    have hT_nonempty : V(T).Nonempty := by
      simp only [←Set.encard_pos]
      suffices (0 : ℕ∞) < 3 by
        exact this.trans_le hV
      simp
    have ⟨x, hxT⟩ := hT_nonempty
    have hx_ssub : {x} ⊂ V(T) := by
      refine ⟨by simp; tauto, ?_⟩
      intro bad
      have := Set.encard_le_encard bad
      have := hV.trans this
      simp at this
    have hconn := hT.connected
    rw [connected_iff_forall_exists_adj hT_nonempty] at hconn
    have hy := hconn _ hx_ssub (by simp)
    simp at hy
    obtain ⟨y, ⟨hyT, hne⟩, hadj⟩ := hy
    have hxy_ssub : {x,y} ⊂ V(T) := by
      refine ⟨?_, ?_⟩
      · simp [pair_subset_iff]; tauto
      intro bad
      have := Set.encard_le_encard bad
      have := hV.trans this
      replace hne : x ≠ y := fun a ↦ hne (id (Eq.symm a))
      simp [Set.encard_pair hne] at this
      norm_num at this
    have hz := hconn _ hxy_ssub (by simp)
    obtain ⟨x', hx', z, hz⟩ := hz
    apply hz.1.2
    simp at hx'; obtain (hx'|hx') := hx'
      <;> symm at hx'
      <;> subst hx'
      <;> [(right; simp); (left; symm at hadj)]
      <;> exact unique_neighbor_of_eDegree_eq_one (hyp _ ‹_›) hz.2 ‹_›
  -- now we have our vertex x of degree ≥ 2
  use {x}
  refine ⟨?_, by simp⟩
  simp [IsSepSet]
  refine ⟨by assumption, ?_⟩
  -- choose any two neighbors of x; they must be separated by x
  intro bad
  have T_simple := hT.isForest.simple
  rw [eDegree_eq_encard_adj] at hx
  have ⟨N, hN_sub, hN_encard⟩ := Set.exists_subset_encard_eq hx
  rw [Set.encard_eq_two] at hN_encard
  obtain ⟨y,z,hne,rfl⟩ := hN_encard
  -- pick a path between y and z which does not go through x
  obtain ⟨hy, hz⟩ : T.Adj x y ∧ T.Adj x z := by
    refine ⟨hN_sub ?_, hN_sub ?_⟩ <;> simp
  have ⟨hyT', hzT'⟩ : y ∈ V(T - {x}) ∧ z ∈ V(T - {x}) := by
    simp
    have := hT.isForest.loopless
    refine ⟨⟨hy.right_mem, ?_⟩, ⟨hz.right_mem, ?_⟩⟩
      <;> rintro rfl <;> apply T.not_adj_self <;> assumption
  obtain ⟨P, hP, hP_first, hP_last⟩ := (bad.connectedBetween hyT' hzT').exists_isPath
  obtain ⟨xy, hxy⟩ := hy
  obtain ⟨xz, hxz⟩ := hz
  let Q' := cons x xy P
  have hQ'_isPath : T.IsPath Q' := by
    simp [Q']
    refine ⟨hP.of_le vertexDelete_le, by rwa [hP_first], ?_⟩
    intro bad
    replace hP := hP.vertexSet_subset
    apply hP at bad
    rw [vertexDelete_vertexSet] at bad
    apply bad.2
    simp
  let Q := cons z xz Q'
  have hQ_isCycle : T.IsCycle Q := by
    simp [Q]
    have := hQ'_isPath.cons_isCycle_of_nontrivial (G := T) (P := Q') (e := xz)
    simp [Q', hP_last, hxz] at this
    apply this
    by_contra! bad
    simp at bad
    apply hne
    rw [←hP_first, ←hP_last]
    exact Nil.first_eq_last bad
  exact hT.isForest _ hQ_isCycle

lemma Bound_on_indepSet {G : Graph α β} [G.Simple] [G.Finite]
    (S : Set (α)) (hS : IsSepSet G S)
    (H : Graph α β ) (hH : IsCompOf H (G-S) )
    (A : Set (α)) (hA : IsMaxIndependent G A) ( v : α ) (hx : v ∈ V(H) ∩ A )
    : G.degree v + (A ∩ V(H)).ncard ≤ (V(H)).ncard + S.ncard := by
    -- Need degree_eq_ncard_adj, will work after update
  let Inc := {w | G.Adj v w}
  let IncW := {w | G.Adj v w} ∩ V(H)

  have disjoint : Inc ∩ (A ∩ V(H)) = ∅ := by
    by_contra hcon
    have ⟨ w, hw ⟩ : ∃ e, e ∈ Inc ∩ (A ∩ V(H)) := by
      refine nonempty_def.mp (nonempty_iff_ne_empty.mpr hcon)
    have hwvAdj: G.Adj v w := by
      have h1 : w ∈ Inc := mem_of_mem_inter_left hw
      exact h1
    have hco : ¬ G.Adj v w := by
      have hAindep : IsIndependent G A := by exact hA.1
      have hvA : v ∈ A := mem_of_mem_inter_right hx
      have hwA := mem_of_mem_inter_left ( mem_of_mem_inter_right hw)
      apply hAindep.2 hvA hwA
      by_contra hc
      rw [hc] at hwvAdj
      exact (not_adj_self G w) hwvAdj
    exact hco hwvAdj

  --For the following you need that the sets are disjoint
  have hf1 : (Inc ∪ (A ∩ V(H))).ncard = Inc.ncard + (A ∩ V(H)).ncard := by
    -- have hfin2 : (A ∩ V(H)).Finite := by
    --   have : (A ∩ V(H)) ⊆ V(G) := by
    --     exact fun ⦃a⦄ a_1 ↦ (hA.1.1) (inter_subset_left a_1)
    --   have : V(G).Finite := by exact vertexSet_finite
    --   exact Finite.subset vertexSet_finite (fun ⦃a⦄ a_1 ↦ (hA.1.1) (inter_subset_left a_1))
    apply ncard_union_eq
    exact disjoint_iff_inter_eq_empty.mpr disjoint
    exact finite_setOf_adj G
    exact Finite.subset vertexSet_finite (fun ⦃a⦄ a_1 ↦ (hA.1.1) (inter_subset_left a_1))
  have hf2 : (V(H) ∪ S).ncard = V(H).ncard + S.ncard := sorry
  --Use degree_eq_ncard_adj
  have hdeg : G.degree v = Inc.ncard := sorry
  --This one should be straight forward
  have h1 : Inc ∪ (A ∩ V(H)) = (IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) := by
    have hinc : Inc = IncW ∪ (Inc\IncW) := by
      refine Eq.symm (union_diff_cancel' (fun ⦃a⦄ a_1 ↦ a_1) inter_subset_left)
    --conv => lhs ; rhs
    nth_rewrite 1 [hinc]
    exact union_right_comm IncW (Inc \ IncW) (A ∩ V(H))
  --Again, disjoint sets
  have hf3 : ((IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) ).ncard =
      (IncW ∪ (A ∩ V(H))).ncard + (Inc\IncW).ncard
    := by
      sorry
  --Very important
  rw [←hf2,hdeg,←hf1,h1, hf3 ]

  --Inequalities to finish
  have hH : (IncW ∪ (A ∩ V(H))).ncard ≤ V(H).ncard := by
    have hH1 : (IncW ∪ (A ∩ V(H))) ⊆ V(H) := by
      exact union_subset (inter_subset_right) (inter_subset_right)
    refine ncard_le_ncard hH1 ?_
    have hP : V(G-S) ⊆ V(G) := by
      simp [vertexDelete_vertexSet]
      exact diff_subset
    exact Finite.subset (vertexSet_finite) (fun ⦃a⦄ a_1 ↦ hP ((isCompOf_subset (G - S) H hH ) a_1))

  have hS : (Inc\IncW).ncard ≤ S.ncard := by
    have hH1 :(Inc\IncW) ⊆ S := by
      intro w hwsub
      have hAdj : G.Adj v w := by
        have h : w ∈ Inc := mem_of_mem_inter_left hwsub
        exact h
      sorry
    sorry
  linarith

--Again, is missing when G is complete but whatever
lemma indep_to_Dirac {G : Graph α β} [G.Simple] [G.Finite] (h3 : 3 ≤ V(G).ncard)
    (S : Set (α)) (HS : IsMinSepSet G S )
    (A : Set (α)) (hA : IsMaxIndependent G A)
    (hDirac : V(G).ncard ≤ 2 * G.minDegree ) : A.ncard ≤ S.ncard := by
  --Trivial case: Independent set is completely contained in the separator
  obtain ( HAS| he ) := Classical.em (A ⊆ S)
  · have : S.Finite := Set.Finite.subset vertexSet_finite HS.1.1
    exact ncard_le_ncard HAS this
  have ⟨x, hxA, hvS ⟩ : ∃ x ∈ A, x ∉ S := by exact not_subset.mp he
  -- Add hDirac applyed to x. You won't need it immediatly but will need it in all cases

  --We want to use ge_two_components_of_not_connected with G-S so we need:
  have hxS: x ∈ V(G - S) := by
    simp
    have := hA.1.1
    tauto

  have hNeBotS : (G - S).NeBot := by
    apply NeBot_iff_vertexSet_nonempty.2
    tauto

  have hcomp := ge_two_components_of_not_connected hNeBotS sorry
  have ⟨ H1, hccH1, hcH1 ⟩ : ∃ H, IsCompOf H (G-S) ∧ x ∈ V(H) := by
    exact exists_IsCompOf_vertex_mem hxS

  --Here are two options to finish the proof, either define H2 as follows, but it won't be conencted
  --let H2 := G - (V(H1) ∪ S)
  --In this case use hcomp to get V(H2)≠ ∅

  --Second option is to use and prove this
  -- have ⟨ H2, hccH2, h12 ⟩  : ∃ H, IsCompOf H (G-S) ∧ H ≠ H1 := by
  --   sorry
  --see Richards proof using hcomp
  --In this case you will need (V(H2)).ncard ≤ (V(G)\ (V(H1) ∪ S) ).ncard + S.ncard (or something)

  have ⟨H2, ⟨H2comp, H2ne⟩⟩ :
    ∃ H, H.IsCompOf (G - S) ∧ H ≠ H1 := by
    have components_nonempty : (G - S).Components.Nonempty := by
      apply nonempty_of_encard_ne_zero
      intro h; rw [h] at hcomp; clear h
      norm_num at hcomp
    by_contra! hyp_contra
    have is_singleton : (G - S).Components = {H1} := by
      exact (Nonempty.subset_singleton_iff (components_nonempty)).mp hyp_contra
    have : (G - S).Components.encard = 1 := by
      simp [is_singleton]
    rw [this] at hcomp; clear this
    have : (2 : ℕ) ≤ (1 : ℕ) := by exact ENat.coe_le_coe.mp hcomp
    linarith

  -- Second annoying case
  obtain ( Hemp| hAH1 ) := Classical.em ( A ∩ V(H2) = ∅)
  · have ⟨y, hy ⟩ : ∃ y, y ∈ V(H2) \ A := by
      -- Managed to simplify this part a lot - Noah
      rw [← Set.diff_self_inter, Set.inter_comm, Hemp, Set.diff_empty]
      exact H2comp.1.2
    --Apply Bound_on_indepSet with modifications since H2 is not a connected component
    -- You will nee hDirac applied to y
    have := Bound_on_indepSet S HS.1 H1 hccH1 A hA x (by tauto)

    sorry

  --Easy case
  obtain ⟨y, yA2 ⟩ := nonempty_iff_ne_empty.mpr hAH1

  --Use Bound_on_indepSet twice and linarith to conclude. You'll also need
  have h1 : (V(H1)).ncard + S.ncard + (V(H2)).ncard + S.ncard = V(G).ncard + S.ncard := by sorry
  -- Add hDirac applied to y
  sorry

def Is_hamiltonian_cycle (G : Graph α β) (C : WList α β) : Prop :=
  G.IsCycle C ∧ C.length = V(G).ncard

lemma Is_hamiltonian_encard (G : Graph α β) (C : WList α β) (hC : G.IsCycle C )
    (hen : C.vertexSet.encard = V(G).encard ) : Is_hamiltonian_cycle G C := by sorry

def neighbour_of_Set (G : Graph α β) (H : Set α) (v : α ) : Prop :=
    ∃ w, w ∈ H ∧  Adj G v w


--I think this lemma is important and useful for us

lemma IsCycle_length_to_vertex {G : Graph α β} {C : WList α β} (hC : G.IsCycle C ) :
    C.length = V(C).encard := by

  sorry

lemma IsCycle_length_bound {G : Graph α β} {C : WList α β} (hC : G.IsCycle C ) :
    C.length ≤ V(G).encard := by

  have hsubs := hC.isWalk.vertexSet_subset
  have : C.length = V(C).encard := by
    sorry
  sorry



lemma Adj_exists_edge (G : Graph α β) (x y : α) (hA : G.Adj x y) : ∃ e, G.IsLink e x y := hA

--Noah, here is the lemma thats not liking me
lemma Complete_to_cycle {G : Graph α β} [G.Finite] (n : ℕ) (hn : n + 3 ≤ V(G).encard)
    (hcomplete : ∀ v w, v ∈ V(G) → w ∈ V(G) → v ≠ w → G.Adj v w)
    : ∃ C : WList α β, G.IsCycle C ∧ V(C).encard = n + 3 := by
  induction n with
  | zero =>
    simp
    have ⟨ T, hT, hT3 ⟩ := V(G).exists_subset_encard_eq hn
    have ⟨ v, u, w, hvu, hvw, huw, hTel ⟩ := (T.encard_eq_three).1 hT3
    have hv : v ∈ V(G) := by sorry
    have hu : u ∈ V(G) := by sorry
    have hw : w ∈ V(G) := by sorry
    have ⟨ euv, heuv ⟩ := Adj_exists_edge G v u (hcomplete v u hv hu hvu )
    have ⟨ euw, heuw ⟩ := Adj_exists_edge G u w (hcomplete u w hu hw huw )
    have ⟨ ewv, hewv ⟩ := Adj_exists_edge G w v (hcomplete w v hw hv hvw.symm )
    --have : G.IsWalk [ v ] := by sorry
    · have hv : v ∈ V(G) := by
        have : v ∈ T := by
          rw[hTel]
          exact mem_insert v {u, w}
        exact hT this
      have hu : u ∈ V(G) := by
        have : u ∈ T := by
          rw[hTel]
          refine mem_insert_of_mem v (mem_insert u {w})
        exact hT this
      have hw : w ∈ V(G) := by
        have : w ∈ T := by
          rw[hTel]
          refine mem_insert_of_mem v (mem_insert_of_mem u rfl)
        exact hT this
      --have ⟨euv, hh ⟩ : ∃ evu, G.IsLink evu v u := hcomplete v u hv hu hvu
      --use [u v w]
      sorry

  | succ n IH =>

    sorry

lemma Hamiltonian_to_cyle {G : Graph α β}
    (hham : ∃ C : WList α β, Is_hamiltonian_cycle G C)
    : ∃ C : WList α β, G.IsCycle C  := by
  obtain ⟨ C, hC ⟩ := hham
  use C
  exact hC.1

variable [DecidableEq α]

lemma IsPath.exists_isPath_vertex (P : WList α β) (hP : G.IsPath P) (hu : u ∈ P) :
    ∃ P₀ P₁, G.IsPath P₀ ∧ G.IsPath P₁ ∧ u = P₀.last ∧ u = P₁.first ∧
    P₀.length + P₁.length = P.length ∧ P = (P₀ ++ P₁) := by
  set Pre : WList α β := prefixUntilVertex P u with h_pre
  set Suf : WList α β := suffixFromVertex P u with h_suf
  use Pre
  use Suf
  rw [h_pre,h_suf]
  refine ⟨ IsPath.prefix hP (prefixUntilVertex_isPrefix P u),
  (IsPath.suffix hP (suffixFromVertex_isSuffix P u)),
  Eq.symm (prefixUntilVertex_last hu) , Eq.symm (suffixFromVertex_first hu),
  prefixUntilVertex_suffixFromVertex_length P u hu,
  Eq.symm (prefixUntilVertex_append_suffixFromVertex P u) ⟩

lemma idxOf_concat_ne (w : WList α β) (e) (hx : x ∈ w) :
    (w.concat e y).idxOf x = w.idxOf x := by
  induction w with
  | nil u => simp_all
  | cons u f w ih =>
  simp
  obtain rfl | hu := eq_or_ne x u
  · rw [idxOf_cons_self, idxOf_cons_self]
  rw[idxOf_cons_ne hu.symm, idxOf_cons_ne hu.symm ]
  simp_all

lemma Cycle_conc_index
    (huv : v ≠ u) {P : WList α β} (hCP : v ∈ cons u e (P.concat f u))
    : v ∈ P ∧ (cons u e (P.concat f u)).idxOf v = P.idxOf v + 1 := by
  simp at hCP
  obtain (rfl | h2 | rfl) := hCP
  · exact False.elim (huv rfl)
  · refine ⟨ h2, ?_ ⟩
    rw [idxOf_cons_ne huv.symm e (P.concat f u) ]
    simp
    --refine Eq.symm (IsPrefix.idxOf_eq_of_mem ?_ h2)
    rwa [idxOf_concat_ne P f ]
  · exact False.elim (huv rfl)

lemma prefixUntilVertex_index (w : WList α β) (x : α) (hx : x ∈ w)
    (hle : w.idxOf y ≤ w.idxOf x ) :
    w.idxOf y = (w.prefixUntilVertex x).idxOf y := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  simp at hx
  obtain rfl | hu := eq_or_ne x u
  · obtain rfl | hxy := eq_or_ne x y
    simp
    have h1 : (cons x e w).first = x := by exact rfl
    rw [←prefixUntilVertex_first (cons x e w) x] at h1
    have h := idxOf_first ((cons x e w).prefixUntilVertex x)
    nth_rw 3 [←h1]
    exact id (Eq.symm h)
    · simp at hle
      rw [hle]
      rw [idxOf_cons_ne hxy] at hle
      by_contra!
      have hcon : 0 ≤ w.idxOf y := by exact Nat.zero_le (w.idxOf y)
      rw [←hle ] at hcon
      linarith
  simp_all [prefixUntilVertex, hu.symm, idxOf_cons_ne hu.symm]
  obtain rfl | huy := eq_or_ne y u
  · simp
  simp_all [ idxOf_cons_ne huy.symm]

lemma prefixUntilVertex_Nil (w : WList α β) (x : α) :
    Nil ((cons x e w).prefixUntilVertex x) := by
  refine length_eq_zero.mp ?_
  rw [prefixUntilVertex_length (w := cons x e w)]
  exact idxOf_cons_self x e w
  simp

lemma prefixUntilVertex_nil (w : WList α β) (x : α) :
    (cons x e w).prefixUntilVertex x = .nil x := by
  refine Nil.eq_nil_of_mem (prefixUntilVertex_Nil w x) ?_
  have h1 : x = ((cons x e w).prefixUntilVertex x).first := by
    rw [prefixUntilVertex_first (cons x e w) x]
    exact rfl
  have h2 : ((cons x e w).prefixUntilVertex x).first ∈ (cons x e w).prefixUntilVertex x := by
    exact first_mem
  rwa [←h1 ] at h2

lemma prefixUntilVertex_index_iff (w : WList α β) (x : α) (hx : x ∈ w) (hy : y ∈ w)
    : y ∈ (w.prefixUntilVertex x) ↔  w.idxOf y ≤ w.idxOf x := by
refine ⟨ ?_, ?_ ⟩
· intro hyP
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp
    rw [prefixUntilVertex_nil w x] at hyP
    simp at hyP
    rw[hyP]
    simp
  simp [hu] at hx
  obtain rfl | huy := eq_or_ne y u
  · simp
  simp [huy] at hy
  simp [idxOf_cons u e w, huy.symm, hu.symm]
  rw [prefixUntilVertex_cons_of_ne w hu.symm] at hyP
  simp only [mem_cons_iff, huy, false_or] at hyP
  exact ih hx hy hyP
intro hle
by_contra hc
have h1 := idxOf_notMem hc
rw [prefixUntilVertex_length hx, ←prefixUntilVertex_index w x hx hle] at h1
linarith

lemma idx_Of_tail {w : WList α β} {a : α} (hw : w.Nonempty) (haf : w.first ≠ a)
    (ha : a ∈ w) :
    (w.tail).idxOf a + 1 = w.idxOf a := by
  induction w with
  | nil w =>
  simp
  rw [nil_first] at haf
  exact haf (mem_nil_iff.1 ha).symm
  | cons u e w ih =>
  simp
  obtain rfl | hu := eq_or_ne a u
  simp
  exact haf rfl
  simp [hu.symm]

lemma idx_Of_dropLast {w : WList α β} {a : α} (hw : w.Nonempty) (ha : a ∈ w) :
    (w.dropLast).idxOf a = w.idxOf a := by
  induction w with
  | nil w => rfl
  | cons u e w ih =>
  obtain he | hwN := exists_eq_nil_or_nonempty w
  obtain ⟨x, hx ⟩ := he
  rw [hx]
  simp
  obtain rfl | hu := eq_or_ne a u
  simp
  simp [hu.symm]
  simp [hu, hx] at ha
  exact id (Eq.symm ha)
  rw [hwN.dropLast_cons]
  obtain rfl | hu := eq_or_ne a u
  simp_all
  simp [hu.symm ]
  simp_all

omit [DecidableEq α] in
lemma IsCycle.rotate_one {C : WList α β} (hC : G.IsCycle C)
    : ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  set e := hC.nonempty.firstEdge
  use e
  have hCn : C = cons C.first e C.tail := by
    exact Eq.symm (Nonempty.cons_tail hC.nonempty)
  nth_rw 1 [hCn]
  rw [cons_rotate_one ]

lemma IsCycle.idxOf_rotate_one {a  : α} {C : WList α β} (hC : G.IsCycle C)
    (hnt : C.Nonempty) (h1 : C.first ≠ a ) (ha : a ∈ C) :
    (C.rotate 1).idxOf a + 1 = C.idxOf a := by
  obtain ⟨e, h ⟩ :=  hC.rotate_one
  have hat : a ∈ C.tail := by
    obtain hfirst | h1 := eq_first_or_mem_tail ha
    · by_contra
      exact h1 (id (Eq.symm hfirst))
    exact h1
  have := idx_Of_tail hnt h1 ha
  rwa [h, idxOf_concat_ne C.tail e hat]

lemma IsCycle.idxOf_rotate_first {a  : α} {n : ℕ} {C : WList α β} (hC : G.IsCycle C)
    (hn : n < C.length) (hle : n + 1 ≤ C.idxOf a ) : (C.rotate n).first ≠ a := by
  rw [rotate_first C n (Nat.le_of_succ_le hn) ]
  by_contra hc
  rw[←hc] at hle
  rw [idxOf_get hC hn ] at hle
  linarith

lemma IsCycle.idxOf_rotate_n_le {a  : α} {n : ℕ} (C : WList α β) (hC : G.IsCycle C)
    (hnt : C.Nonempty) (ha : a ∈ C) (hn : n < C.length)
    (hle : n + 1 ≤ C.idxOf a ) :
    (C.rotate n).idxOf a + n  = C.idxOf a := by
  induction n with
  | zero =>
  simp_all
  -- have h1 : C.first ≠ a := by
  --   by_contra hc
  --   rw[←hc, idxOf_first ] at hle
  --   linarith
  -- exact hC.idxOf_rotate_one C hnt h1 ha
  | succ n hi =>
  rw[←rotate_rotate C n 1]
  have hlen : n ≤ C.length := by
    linarith
  have hle' : n + 1 ≤ C.idxOf a := by
    linarith
  have han : (C.rotate n).first ≠ a := by
    rw [rotate_first C n hlen ]
    by_contra hc
    rw[←hc, idxOf_get hC (Nat.lt_of_succ_lt hn) ] at hle
    linarith
  have hf := (rotate hC n ).idxOf_rotate_one ((rotate_nonempty_iff n).mpr hnt )
      han (((hC.isClosed).mem_rotate).2 ha)
  have := hi (Nat.lt_of_succ_lt hn) hle'
  linarith

lemma IsCycle.idxOf_rotate_one_first {a  : α} {C : WList α β} (hC : G.IsCycle C)
    (hnt : C.Nonempty) (h1 : C.first = a ) (ha : a ∈ C) :
    (C.rotate 1).idxOf a = C.length := by sorry

lemma IsCycle.idxOf_rotate_n {a  : α} {n : ℕ} (C : WList α β) (hC : G.IsCycle C)
    (hnt : C.Nonempty) (ha : a ∈ C) (hn : n < C.length)
    (hle : C.idxOf a < n ) : (C.rotate n).idxOf a + n = C.length + 1 + C.idxOf a := by sorry



lemma Hamiltonian_alpha_kappa {G : Graph α β} [G.Simple] [G.Finite] (h3 : 3 ≤ V(G).encard)
    (S : Set α) (HS : IsMinSepSet G S )
    (A : Set α) (hA : IsMaxIndependent G A)
    (hAS : A.encard ≤ S.encard ) : ∃ C : WList α β, Is_hamiltonian_cycle G C := by
--grw

  -- To find a longest cycle, we first need to show the existence of some cycle C'
  have ⟨ C', hC'⟩ : ∃ C, G.IsCycle C := by
    by_contra! hCon
    -- if there is no cycle, then since G is a forest,
    -- any vertex v of degree >= 2 is a separating set
    obtain (h1 | h2) := Classical.em (∃ v, v ∈ V(G) ∧ G.degree v ≥ 2)
    · -- So, S.encard = 1, and thus A.encard <= 1
      have ⟨v, ⟨hvG, hv⟩⟩ := h1
      -- since v has degree at least 2, we can obtain two neighbours
      have hn2 : 1 < {x | G.Adj v x}.ncard := by
        rw [← G.degree_eq_ncard_adj]
        assumption
      have nsFinite : {x | G.Adj v x}.Finite :=
        G.finite_setOf_adj
      rw [one_lt_ncard_iff nsFinite] at hn2
      have ⟨a, b, ha, hb, hab⟩ := hn2
      simp_all
      -- Show that {v} is a separating set
      have vSep : G.IsSepSet {v} := by
        refine ⟨singleton_subset_iff.mpr hvG, ?_⟩
        -- those two neighbours a and b are not connected in G - {v},
        -- because otherwise there would be a cycle
        -- for a contradiction, let's construct the cycle
        by_contra! hCon
        have aVGv : a ∈ V(G - {v}) := by
          have := Adj.right_mem ha
          simp_all only [ne_eq, vertexDelete_vertexSet, mem_diff, mem_singleton_iff, true_and]
          exact fun a_1 ↦ (Adj.ne ha) (id (Eq.symm a_1))
        have bVGv : b ∈ V(G - {v}) := by
          have := Adj.right_mem hb
          simp_all only [ne_eq, vertexDelete_vertexSet, mem_diff, mem_singleton_iff, true_and]
          exact fun a_1 ↦ (Adj.ne hb) (id (Eq.symm a_1))
        have abCon : (G - {v}).ConnectedBetween a b := Connected.connectedBetween hCon aVGv bVGv
        have ⟨abPath, habPath⟩ := ConnectedBetween.exists_isPath abCon
        have ⟨abPathG, vnP⟩ := (isPath_vertexDelete_iff.1 habPath.1)
        -- need to first add v to the ab path
        rw [Adj.eq_1 G] at ha
        have ⟨e, eLink⟩ := ha
        have ⟨e2, e2Link⟩ := hb
        have e2LinkOrig := e2Link
        have enee2 : e ≠ e2 := by
          by_contra!
          rw [← this] at e2Link
          rw [IsLink.isLink_iff eLink] at e2Link
          cases e2Link
          · simp_all only [not_true_eq_false]
          simp_all only [isLink_self_iff, not_isLoopAt, exists_false]
        have vnP : v ∉ abPath := by simp_all
        rw [← habPath.2.1] at eLink
        have vbPath := cons_isPath_iff.2 ⟨abPathG, eLink, vnP⟩
        rw [Adj.eq_1 G] at hb
        have vfirst : v = (cons v e abPath).first := rfl
        have blast : b = (cons v e abPath).last := by tauto
        rw [vfirst, blast] at e2Link
        have e2npe : e2 ∉ (cons v e abPath).edge := by
          simp
          refine ⟨by tauto, ?_⟩
          by_contra!
          have := IsWalk.edge_mem_of_mem habPath.1.isWalk this
          have := (IsLink.mem_vertexDelete_iff e2LinkOrig).1 this
          tauto
        -- then link it up to a cycle, contradicting that G doesn't have any cycle
        have := IsPath.cons_isCycle vbPath e2Link e2npe
        tauto
      -- finally, we have that {v} is a separating set in G
      have hS1 : S.encard ≤ 1 := by
        have := HS.2 {v} vSep
        simp_all only [encard_singleton]
      -- But then the two neighbours of v cannot be adjacent,
      -- because otherwise there would be a cycle
      -- So, A.encard >= 2, contradiction
      have anev : ¬a = v := by
        have := loopless_iff_forall_ne_of_adj.1 (IsForest.loopless hCon) v a ha
        rw [ne_comm, ne_eq] at this
        assumption
      have bnev : ¬b = v := by
        have := loopless_iff_forall_ne_of_adj.1 (IsForest.loopless hCon) v b hb
        rw [ne_comm, ne_eq] at this
        assumption
      obtain (h3 | h4) := Classical.em (G.Adj a b)
      · -- First, the case where a and b are adjacent
        -- Need to construct the cycle a-b-v
        have ⟨e, eLink⟩ := ha
        have ⟨e2, e2Link⟩ := hb
        have ⟨e3, e3Link⟩ := h3
        have avPath := cons_isPath_iff.2 ⟨nil_isPath hvG, ⟨IsLink.symm eLink, by
          rw [mem_nil_iff]
          assumption⟩⟩
        have bavPath := cons_isPath_iff.2 ⟨avPath, ⟨IsLink.symm e3Link, by
          simp_all [mem_cons_iff]
          tauto⟩⟩
        let bav := (cons b e3 (cons a e (nil v)))
        have flLink : G.IsLink e2 bav.first bav.last := by
          simp_all
          exact id (IsLink.symm e2Link)
        have eDis : e2 ∉ (cons b e3 (cons a e (nil v))).edge := by
          simp_all
          refine ⟨?_, ?_⟩
          · by_contra!
            simp_all
            have := G.eq_or_eq_of_isLink_of_isLink e2Link e3Link
            tauto
          by_contra!
          simp_all
          have := IsLink.eq_and_eq_or_eq_and_eq eLink e2Link
          tauto
        have := IsPath.cons_isCycle bavPath flLink eDis
        tauto
      -- Now, a and b are not adjacent
      -- We show {a, b} is independent for a contradiction
      have hI : G.IsIndependent {a, b} := by
        refine ⟨?_, ?_⟩
        · have : a ∈ V(G) := ha.right_mem
          have : b ∈ V(G) := hb.right_mem
          grind only [= subset_def, usr subset_insert, = singleton_subset_iff, = mem_insert_iff,
            = setOf_true, = mem_singleton_iff, = setOf_false, cases Or]
        intro x hx y hy hxy
        simp_all only [mem_insert_iff, mem_singleton_iff, ne_eq]
        have : ¬G.Adj b a := by exact fun a_1 ↦ h4 (id (Adj.symm a_1))
        grind only [= setOf_true, = setOf_false, cases Or]
      have Age2 : 2 ≤ A.encard := by
        have hA2 := hA.2 {a, b} hI
        have : ({a, b} : Set α).encard = 2 := encard_pair hab
        rw [this] at hA2
        exact hA2
      have Ale1 : A.encard ≤ 1 := Std.IsPreorder.le_trans A.encard S.encard 1 hAS hS1
      have : 2 ≤ (1 : ℕ∞) := Std.IsPreorder.le_trans 2 A.encard 1 Age2 Ale1
      simp_all only [Nat.not_ofNat_le_one]

    -- If every vertex has degree <= 1, then S.encard = 0, so we are done
    have Vnz : V(G).Nonempty := by
      rw [←encard_pos]
      suffices (0 : ℕ∞) < 3 by exact this.trans_le h3
      simp
    obtain ⟨v, hv⟩ : ∃ v, v ∈ V(G) := Vnz
    have : ¬G.Connected := by
      -- We know there are ≥ 3 vertices
      -- But all have degree ≤ 1
      have : G.degree v ≤ 1 := by grind only
      sorry
    have Sempty : S.encard = 0 := by
      have esSep : IsSepSet G ∅ := by
        refine ⟨empty_subset V(G), ?_⟩
        rw [vertexDelete_empty]
        assumption
      have : S.encard = (∅ : Set α).encard := by
        have := HS.2 ∅ esSep
        simp_all
      simp_all
    have hGI : G.IsIndependent {v} := ⟨by simp_all, by simp_all⟩
    have := hA.2 {v} hGI
    simp_all

  let S := {C : WList α β | G.IsCycle C }
  have hsne : S.Nonempty := by
    exact nonempty_of_mem hC'
  have hsfin : ((length ) '' S).Finite := by sorry

  --The following obtains a cycle of G that is maximal in length
  obtain ⟨C, hCs⟩ := hsfin.exists_maximalFor' _ _ hsne
  --Now that we got a max cycle, we have two cases
  obtain ( hn| hlen ) := Classical.em (V(C).encard = V(G).encard  )
  · use C
    apply Is_hamiltonian_encard G C (hCs.prop) hn
  --There should be an obvious bound on the size of a cycle
  have hCle : V(C).encard < V(G).encard := by
    have hVCG : V(C) ⊆ V(G) := by sorry
    refine Finite.encard_lt_encard ?_ ?_
    --have := hlen (congrArg encard a)
      --simp [hlen]
    exact WList.vertexSet_finite C
    exact HasSubset.Subset.ssubset_of_ne hVCG fun a ↦ hlen (congrArg encard a)
--VC = V(C)
  --have ⟨v, hvV ⟩ : ∃ v, v ∉ C.vertex := sorry
  have hG : V(G-V(C)).Nonempty := by
    by_contra hc
    have hg1 : V(C) ⊆ V(G) := by sorry
    rw[vertexDelete_vertexSet] at hc
    have hconcl : V(G) ⊆ V(C) := by
      intro v hv
      obtain h1 | h2 := Classical.em (v ∈ V(C))
      · exact h1
      by_contra
      have hh : v ∈ V(G)\V(C) := by exact mem_diff_of_mem hv h2
      have hhh : (V(G)\ V(C)).Nonempty := by
        use v
      exact hc hhh
      --rw [←NeBot_iff_vertexSet_nonempty ] at hc
    have hconclusion : V(G) = V(C)  := by exact hconcl.antisymm hg1
    rw[ hconclusion ] at hCle
    exact hlen (congrArg encard (id (Eq.symm hconclusion)))
    --obtain ⟨v, hv ⟩ := hc
    -- have hg : V(G) \ VC = ∅ := by sorry
    -- have hg1 : VC ⊆ V(G) := by sorry
    -- have hconcl : V(G) ⊆ VC  := by exact diff_eq_empty.mp hg
    -- have hconclusion : V(G) = VC  := by exact Subset.antisymm hconcl hg1
  have ⟨D, hD ⟩ := exists_IsCompOf hG
  set Neig : Set α := {v : α | v ∈ C ∧ (neighbour_of_Set G V(D) v) } with h_neig
  --This is the second worst sorry
  have hDadj : ∀ v, v ∈ Neig → ∀ u, u ∈ Neig
      → C.idxOf v ≠ C.idxOf u + 1 := by
    intro v hvN u huN
    by_contra hcon
    obtain ⟨ w, hwD, hwad ⟩ := hvN.2
    obtain ⟨ w', huD, huad ⟩ := huN.2
    --Need to take path in D from w to w' and extend cycle
    sorry
  set NextNeigh : Set α := {v ∈ C | ∃ w ∈ Neig, C.idxOf v + 1 = C.idxOf w  } with h_NN
  have hNNV : NextNeigh ⊆ V(G) :=
    fun ⦃a⦄ b ↦ ((IsCycle.isTrail hCs.prop ).vertexSet_subset)
        ((sep_subset (fun x ↦ List.Mem x C.vertex)
        fun x ↦ ∃ w ∈ Neig, C.idxOf x + 1 = C.idxOf w) b)

    --sep_subset V(G) fun x ↦ ∃ w ∈ Neig, C.idxOf x = C.idxOf w + 1
  have ⟨ v, hvD ⟩ : ∃ v, v ∈ V(D) := IsCompOf.nonempty hD

  have hCNT : C.Nontrivial := by sorry
  --Worst sorry, I will take this one
  have hNNI : IsIndependent G NextNeigh := by
    by_contra hc
    obtain ⟨a, b, ha, hb, hab⟩ := IsIndepndent_nee hNNV hc
    --rw[h_NN] at ha
    obtain ⟨P,e,f, hPath, haP, heP, hfP, hef, hC ⟩ :=
        IsCycle.exists_isPath_vertex hCs.prop hCNT ha.1
    have hbP : b ∈ P := by
      have hhh : b ∈ C.rotate (C.idxOf a)  := by
        refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb.1
      rw [hC] at hhh
      exact (Cycle_conc_index (hab.ne).symm hhh).1

    obtain ⟨ b₁, hb1N, hbind ⟩ := hb.2
    obtain ⟨ a₁, ha1N, haind ⟩ := ha.2
    have hab₁ : b₁ ≠ a := by sorry
    --Basically if b₁ = a then a ∈ Neigh and a,a₁ are adj
    --obtain ⟨P₀,P₁,hP₁,hP₂,hP₀last,hP₀first,hP01d,hP01 ⟩ := IsPath.exists_isPath_vertex P hPath hbP
    set P₀ : WList α β := prefixUntilVertex P b with h_pre
    set P₁ : WList α β := suffixFromVertex P b with h_suf
    have hP₀ := IsPath.prefix hPath (prefixUntilVertex_isPrefix P b)
    have hP₁ := IsPath.suffix hPath (suffixFromVertex_isSuffix P b)
    --have hP₀P₁ := Eq.symm (prefixUntilVertex_append_suffixFromVertex P b)
    rw [←h_pre] at hP₀
    rw [←h_suf] at hP₁
    --rw [←h_pre, ←h_suf] at hP₀P₁
    have hb1P' : b₁ ∈ P := by
        have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
          refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
        rw [hC] at hhh
        exact (Cycle_conc_index hab₁ hhh).1
    have hb1P1 : b₁ ∈ P₁ := by
      have hb1P : b₁ ∈ P := by
        have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
          refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
        rw [hC] at hhh
        exact (Cycle_conc_index hab₁ hhh).1
      rw [Eq.symm (prefixUntilVertex_append_suffixFromVertex P b),←h_pre, ←h_suf] at hb1P
      obtain (hf | hg ):= mem_of_mem_append hb1P
      · rw [h_pre] at hf
        --rw [←Eq.symm (prefixUntilVertex_append_suffixFromVertex P b)] at hb1P
        have hcon := (prefixUntilVertex_index_iff P b hbP hb1P').1 hf
        have hbindP : P.idxOf b + 1 = P.idxOf b₁ := by
          have hhh : b ∈ C.rotate (C.idxOf a)  := by
            refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb.1
          rw[hC] at hhh
          have hg1 := (Cycle_conc_index (hab.ne).symm hhh).2
          have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
            refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
          rw[hC] at hhh
          have hg2 := (Cycle_conc_index (hab₁) hhh).2
          rw [←hC] at hg1
          rw [←hC] at hg2

          sorry
        rw [←hbindP ] at hcon
        linarith
      exact hg
    set P₂ : WList α β := prefixUntilVertex P₁ b₁ with h_pre2
    set P₃ : WList α β := suffixFromVertex P₁ b₁ with h_suf2
    have hP₂ := IsPath.prefix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
        (prefixUntilVertex_isPrefix P₁ b₁)
    have hP₃ := IsPath.suffix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
        (suffixFromVertex_isSuffix P₁ b₁)
    --have hP₂P₃ := Eq.symm (prefixUntilVertex_append_suffixFromVertex P₁ b₁)
    rw [←h_pre2] at hP₂
    rw [←h_suf2] at hP₃
    --rw [←h_pre2, ←h_suf2] at hP₂P₃
    --append_length


    --rw [h_pre,h_suf]
      -- refine ⟨ IsPath.prefix hP (prefixUntilVertex_isPrefix P u),
      -- (IsPath.suffix hP (suffixFromVertex_isSuffix P u)),
      -- Eq.symm (prefixUntilVertex_last hu) , Eq.symm (suffixFromVertex_first hu),
      -- prefixUntilVertex_suffixFromVertex_length P u hu,
      -- Eq.symm (prefixUntilVertex_append_suffixFromVertex P u) ⟩


    --have ⟨ P,  := hCs.prop.exists_isPath_edge hNonTC

    --IsPath.append
    --IsPath.cons_isCycle


    sorry
  have hNNIv : IsIndependent G ( insert v NextNeigh) := by
    --Should not be too bad doing cases
    sorry
  --Finish
  sorry


lemma finite_components_of_finite {G : Graph α β} (hFinite : G.Finite) :
  G.Components.Finite := by
  sorry

/- Step 1: WTS G is connected.
Proof: Suppose not. Then the degree of any vertex in the smallest component C of G
would be less than |C| ≤ n/2.
-/


lemma thm1_1_connected {G : Graph α β} [G.Simple] [hFinite : G.Finite]
  (hV : 3 ≤ V(G).ncard) (hDegree : V(G).ncard ≤ 2 * G.minDegree) :
  G.Connected := by
  have encard_eq_ncard : V(G).encard = ↑V(G).ncard := by
    rw [Set.Finite.cast_ncard_eq]
    exact vertexSet_finite
  have hNeBot : G.NeBot := by
    apply NeBot_of_ncard_positive
    linarith

  -- Suppose not.
  by_contra! hyp_contra

  -- There thus must be at least two components.
  have num_components_ge_2 : 2 ≤ G.Components.encard :=
    ge_two_components_of_not_connected hNeBot hyp_contra

  have components_nonempty : G.Components.Nonempty := by
    apply nonempty_of_encard_ne_zero
    intro h; rw [h] at num_components_ge_2; clear h
    norm_num at num_components_ge_2

  -- Choose the smallest component.
  obtain ⟨min_comp, min_comp_spec⟩ :=
    Set.Finite.exists_minimalFor
      (fun H => H.vertexSet.ncard)
      G.Components
      (finite_components_of_finite hFinite)
      components_nonempty

  -- There must be at least one other component.
  have ⟨other_comp, other_comp_spec⟩ :
    ∃ H, H.IsCompOf G ∧ H ≠ min_comp := by
    by_contra! hyp_contra
    have is_singleton : G.Components = {min_comp} := by
      exact (Nonempty.subset_singleton_iff components_nonempty).mp hyp_contra
    have : G.Components.encard = 1 := by
      simp [is_singleton]
    rw [this] at num_components_ge_2; clear this
    have : (2 : ℕ) ≤ (1 : ℕ) := by exact ENat.coe_le_coe.mp num_components_ge_2
    linarith

  -- G, min_comp, other_comp have finite vertexSets
  have G_finite_vertexSet : V(G).Finite := vertexSet_finite
  have min_comp_finite_vertexSet : V(min_comp).Finite := by
    suffices min_comp.Finite by exact vertexSet_finite
    exact Finite.mono hFinite min_comp_spec.1.le
  have other_comp_finite_vertexSet : V(other_comp).Finite := by
    suffices other_comp.Finite by exact vertexSet_finite
    exact Finite.mono hFinite other_comp_spec.1.le

  -- other_comp has at least as many vertices as min_comp
  have other_comp_larger : V(min_comp).ncard ≤ V(other_comp).ncard := by
    refine minimalFor_is_lower_bound (fun H : Graph α β => H.vertexSet.ncard) min_comp_spec ?_ ?_
    simp
    exact other_comp_spec.1
  -- min_comp and other_comp have disjoint vertex sets
  have disjoint_vx_sets : Disjoint V(min_comp) V(other_comp) := by
    suffices StronglyDisjoint min_comp other_comp by
      exact this.vertex
    apply G.components_pairwise_stronglyDisjoint <;> try tauto
    exact min_comp_spec.1

  have G_vertexSet_is_superset : V(min_comp) ∪ V(other_comp) ⊆ V(G) := by
    rw [union_subset_iff]; constructor <;> apply vertexSet_mono
    -- This works: it does exactly what the two following bulleted lines do:
    /-
     · exact min_comp_spec.1.le
     · exact other_comp_spec.1.le
    -/
    -- But it does so without referring to names explicitly.
    run_tacq
      for ldecl in ← getLCtx do
        let hyp := mkIdent ldecl.userName
        let some ty := ← checkTypeQ (← whnf ldecl.type) q(Prop) | continue
        if let ~q($p ∧ $q) := ty then
          evalTactic (← `(tactic| try exact $hyp.1.le))
    -- The type-checking is completely unnecessary, the following code would suffice as well:
    /-
    run_tacq
      for ldecl in ← getLCtx do
        let hyp := mkIdent ldecl.userName
        evalTactic (← `(tactic| try exact $hyp.1.le))
    -/
    -- But the longer example above just shows how one might match on types in
    -- more elaborate scenarios.

  have G_ncard_ge_sum : V(min_comp).ncard + V(other_comp).ncard ≤ V(G).ncard := by
    have : V(min_comp).ncard + V(other_comp).ncard = (V(min_comp) ∪ V(other_comp)).ncard := by
      exact Eq.symm
        (ncard_union_eq disjoint_vx_sets min_comp_finite_vertexSet other_comp_finite_vertexSet)
    rw [this]; clear this
    refine ncard_le_ncard ?_ ?_ <;> assumption

  -- so |min_comp| ≤ n/2
  replace G_ncard_ge_sum : 2 * V(min_comp).ncard ≤ V(G).ncard := by
    linarith

  -- some manipulations left over
  have hle : V(min_comp).ncard ≤ G.minDegree := by linarith
  have hle2 : G.minDegree ≤ min_comp.minDegree := by
    apply minDegree_le_minDegree_of_isCompOf
    rw [←mem_components_iff_isCompOf]
    exact min_comp_spec.1
  replace hle : V(min_comp).ncard ≤ min_comp.minDegree := by linarith
  have hlt : min_comp.minDegree < V(min_comp).ncard := by
    have min_comp_simple : min_comp.Simple := sorry
    refine minDegree_lt_vertexCount ?_ ?_
    · exact Finite.mono hFinite min_comp_spec.1.le
    · rw [NeBot_iff_vertexSet_nonempty]
      exact min_comp_spec.1.nonempty

  linarith

def pathSet (G : Graph α β) := {p | IsPath G p}

lemma pathSet_finite (G : Graph α β) [G.Simple] (hFinite : G.Finite) :
    G.pathSet.Finite := by
  sorry

lemma pathSet_nonempty (G : Graph α β) (hNeBot : G.NeBot) :
    G.pathSet.Nonempty := by
  sorry

def IsLongestPath (G : Graph α β) (p : WList (α) β) :=
  MaximalFor (· ∈ G.pathSet) (fun w => w.length) p

lemma exists_longest_path
    (G : Graph α β) [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot) :
    ∃ p, G.IsLongestPath p :=
  Set.Finite.exists_maximalFor _ _ (G.pathSet_finite hFinite) (G.pathSet_nonempty hNeBot)

-- by maximality, each neighbour of is on the path
lemma first_neighbors_mem_path
    (G : Graph α β) [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot)
    {P : WList (α) β} (hP : G.IsLongestPath P)
    (x : α) (hx : G.Adj x P.first) :
    x ∈ P := by
  sorry

-- similarly, the same statement but reverse in direction
lemma last_neighbors_mem_path
    (G : Graph α β) [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot)
    {P : WList (α) β} (hP : G.IsLongestPath P)
    (x : α) (hx : G.Adj x P.last) :
    x ∈ P := by
  sorry

lemma exists_left_edge
    (w : WList α β) {x : α} (hxw : x ∈ w) (hx : x ≠ w.first) :
    ∃ e y, w.DInc e y x := by
  sorry
