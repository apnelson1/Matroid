import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Matroid.Graph.Walk.Path
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Degree.Basic
import Matroid.Graph.Finite
import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Connected.Defs
import Matroid.Graph.Connected.Component

-- Tree is currently not building, because Matroid.Graph.Walk.toGraph is broken
-- import Matroid.Graph.Tree

import Matroid.Graph.WList.Defs

import Qq open Qq Lean Meta Elab Tactic
-- simple is still broken
-- import Matroid.Graph.Simple

-- connectivity is still broken
-- import Matroid.Graph.Connected.Component

open WList Set

-- we will be using a lot of LEM...
open Classical


section NonGraphThings

variable {α : Type*}

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

variable {α β : Type*} [CompleteLattice α] {x y z u v : α} {e f : β} {G H : Graph α β}

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

def degreeSet (G : Graph α β) : Set ℕ :=
  G.degree '' V(G)

@[simp]
lemma degreeSet_eq {G : Graph α β} :
    G.degreeSet = G.degree '' V(G) := rfl

lemma degreeSet_finite_of_finite {G : Graph α β} (hFinite : G.Finite) :
    G.degreeSet.Finite := by
  simp [degreeSet]
  refine Set.Finite.image ?_ ?_
  exact vertexSet_finite

lemma degreeSet_nonempty {G : Graph α β} (hNeBot : G ≠ ⊥) : G.degreeSet.Nonempty := by
  simpa [degreeSet]

-- lemma exists_minDegreeVx (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
--     ∃ v, MinimalFor (· ∈ V(G)) G.degree v := by
--   refine Set.Finite.exists_minimalFor G.degree V(G) vertexSet_finite ?_
--   apply vertexSet_nonempty_of_NeBot; trivial

-- noncomputable def minDegreeVx (G : Graph α β) : α :=
--   open Classical in
--   if h : G.Finite ∧ G.NeBot then
--     Classical.choose (G.exists_minDegreeVx h.1 h.2)
--   else
--     ∅

-- G.minDegree returns the minimum degree of its vertices if G is finite, else it returns 0
noncomputable def minDegree (G : Graph α β) : ℕ :=
  open Classical in
  if h : G.Finite ∧ G.NeBot then
    Classical.choose <|
    Set.Finite.exists_minimal (degreeSet_finite_of_finite h.1) (degreeSet_nonempty h.2)
  else 0

-- this is the price we pay for choice
@[simp]
lemma minDegree_eq (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    G.minDegree =
    (Classical.choose <|
    Set.Finite.exists_minimal
      (degreeSet_finite_of_finite hFinite)
      (degreeSet_nonempty hNeBot)) := by
  have : G.Finite ∧ G.NeBot = True := by
    simp
    refine ⟨?_, ?_⟩ <;> assumption
  simp only [minDegree]
  simp only [this, and_self, ↓reduceDIte, degreeSet_eq, mem_image]

@[simp]
lemma minDegree_eq' (G : Graph α β) (h : ¬ (G.Finite ∧ G.NeBot)) :
    G.minDegree = 0 := by
  simp [minDegree]
  tauto

lemma minDegree_spec (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    Minimal (· ∈ G.degreeSet) G.minDegree := by
  have hspec :=
    Classical.choose_spec <|
    Set.Finite.exists_minimal (degreeSet_finite_of_finite hFinite) (degreeSet_nonempty hNeBot)
  rw [minDegree_eq] <;> assumption

lemma exists_minDegreeVx (G : Graph α β) (hFinite : G.Finite) (hNeBot : G.NeBot) :
    ∃ v ∈ V(G), G.minDegree = G.degree v := by
  have ⟨⟨v, vspec⟩, dspec⟩ := G.minDegree_spec hFinite hNeBot
  use v
  tauto

-- minDegree is indeed a lower bound
lemma minDegree_le_degree (G : Graph α β) :
    ∀ v ∈ V(G), G.minDegree ≤ G.degree v := by
  intro v hv
  obtain (p|p) := Classical.em (G.Finite ∧ G.NeBot)
  · have hspec := G.minDegree_spec p.1 p.2
    suffices h : G.degree v ∈ G.degreeSet by
      refine minimal_is_lower_bound hspec ?_ ?_
      assumption
    simp
    use v
  · simp [G.minDegree_eq' p]

-- MORE THINGS

lemma degree_lt_vertexCount {G : Graph α β} [G.Simple] {v : α} (h : v ∈ V(G)) :
    G.degree v < V(G).ncard := by sorry

lemma minDegree_lt_vertexCount {G : Graph α β} [G.Simple] (hFinite : G.Finite) (hNeBot : G.NeBot) :
    G.minDegree < V(G).ncard := by
  have ⟨v,vspec⟩ := G.exists_minDegreeVx hFinite hNeBot
  rw [vspec.2]
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
    obtain ⟨v, hv, hveq⟩ := H.exists_minDegreeVx
      (finite_of_le hHG.le)
      (NeBot_iff_vertexSet_nonempty.2 hHG.nonempty)
    rw [hveq]
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
    exact minDegree_le_degree G v hvG

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
      have VHseVG : V(H) ⊆ V(G) := hHG.le.vertexSet_subset
      exact Nonempty.mono VHseVG hne
    obtain ⟨v, hv, hveq⟩ := H.exists_minDegreeVx Hfin hne
    rw [hveq]
    have hvG: v ∈ V(G) := hHG.le.vertexSet_subset hv
    obtain ⟨w, gw, gweq⟩ := G.exists_minDegreeVx ‹G.Finite› gne
    have wvH: w ∈ V(H) := by
      rw [hHG.vertexSet_eq]
      exact gw
    have h1 : H.degree w ≤ G.degree w := degree_mono hHG.le w
    rw [gweq]
    rw [← hveq]
    have h2 : H.minDegree ≤ H.degree w := minDegree_le_degree H w wvH
    linarith

  --This is the case the graph is empty. Richard has a nice lemma that if the graph is
  --empty or infinite then the min degree is 0. We just need to rw that
  rw [H.minDegree_eq' (not_and.mpr fun a ↦ hni)]
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

def IsIndependent (G : Graph α β) (S : Set (α)) : Prop :=
  S ⊆ V(G) ∧ S.Pairwise (fun x y ↦ ¬ G.Adj x y)

def IndepNumLE (G : Graph α β) (n : ℕ∞) : Prop :=
  ∀ S, G.IsIndependent S → S.encard ≤ n

def IsMaxIndependent (G : Graph α β) (S : Set (α)) : Prop :=
  IsIndependent G S ∧ (∀ A, IsIndependent G A → A.encard ≤ S.encard )

def ConnectivityGE (G : Graph α β) (k : ℕ∞) : Prop :=
  ∀ S, S.encard < k → (G - S).Connected

def IsSepSet (G : Graph α β) (S : Set (α)) : Prop :=
  (S ⊆ V(G)) ∧ ¬ (G - S).Connected

def IsMinSepSet (G : Graph α β) (S : Set (α)) : Prop :=
  IsSepSet G S  ∧ ( ∀ A, IsSepSet G A → S.encard ≤ A.encard )

-- Temporary, Tree is broken
def IsForest (G : Graph α β) : Prop := ∀ C, ¬ G.IsCycle C

@[mk_iff]
structure IsTree (T : Graph α β) : Prop where
  isForest : T.IsForest
  connected : T.Connected

lemma IsForest.simple (hG : G.IsForest) : G.Simple := sorry
lemma IsForest.loopless (hG : G.IsForest) : G.Loopless := sorry

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
    · have h1 : V(H) ⊆ V(G - S) := isCompOf_subset (G - S) H hH
      have h :=  vertexDelete_vertexSet G S
      rw [h] at h1
      exact notMem_of_mem_diff (h1 hv)
  exact hw.1 (((hH.isClosedSubgraph).mem_iff_mem_of_adj hhe).1 hv)

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
  obtain ⟨P, hP, hP_first, hP_last⟩ := (bad.vertexConnected hyT' hzT').exists_isPath
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
    have hP : V(G-S) ⊆ V(G) :=
      inter_eq_right.mp (congrArg (Inter.inter V(G)) (vertexDelete_vertexSet G S ))
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
  obtain ( HAS| he ) := Decidable.em (A ⊆ S)
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

  have hcomp := ge_two_components_of_not_connected hNeBotS HS.1.2.1
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
  obtain ( Hemp| hAH1 ) := Decidable.em ( A ∩ V(H2) = ∅)
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

def neighbour_of_Set (G : Graph α β) (H : Set α) (v : α ) : Prop :=
    ∃ w, w ∈ H ∧  Adj G v w

--I think this lemma is important and useful for us

lemma IsCycle_length_bound {G : Graph α β} {C : WList α β} (hC : G.IsCycle C ) :
    C.length ≤ V(G).ncard := by

  have hsubs := hC.isWalk.vertexSet_subset
  have : C.length = V(C).ncard := by
    sorry
  sorry

lemma foo (P : Prop) (Q : Prop ) (h : P ↔ Q) : ¬ P ↔ ¬ Q := by exact not_congr h

lemma Hamiltonian_alpha_kappa {G : Graph α β} [G.Simple] (h3 : 3 ≤ V(G).ncard)
    (S : Set (α)) (HS : IsMinSepSet G S )
    (A : Set (α)) (hA : IsMaxIndependent G A)
    (hAS : A.encard ≤ S.encard ) : ∃ C : WList α β, Is_hamiltonian_cycle G C := by
--grw

  -- To find a longest cycle, we first need to show the existence of some cycle C'
  have ⟨ C', hC'⟩ : ∃ C, G.IsCycle C := by
    by_contra! hCon
    -- if there is no cycle, then since G is a forest, any vertex v of degree >= 2 is a separating set
    obtain (h1 | h2) := Decidable.em (∃ v, v ∈ V(G) ∧ G.degree v ≥ 2)
    · -- So, S.encard = 1, and thus A.encard <= 1
      have ⟨v, ⟨hvG, hv⟩⟩ := h1
      have vSep : G.IsSepSet {v} := by
        refine ⟨singleton_subset_iff.mpr hvG, ?_⟩
        -- since v has degree at least 2, we can obtain two neighbours
        have hn2 : 1 < {x | G.Adj v x}.ncard := by
          rw [← G.degree_eq_ncard_adj]
          assumption
        have nsFinite : {x | G.Adj v x}.Finite := by
          have : G.Finite := Simple.vertexSet_finite_iff.mp $ finite_of_ncard_nonzero $ Nat.ne_zero_of_lt h3
          exact G.finite_setOf_adj
        rw [one_lt_ncard_iff nsFinite] at hn2
        have ⟨a, b, ha, hb, hab⟩ := hn2
        simp_all
        -- those two neighbours a and b are not connected in G - {v}, because otherwise there would be a cycle
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
        have abCon : (G - {v}).VertexConnected a b := Connected.vertexConnected hCon aVGv bVGv
        have ⟨abPath, habPath⟩ := VertexConnected.exists_isPath abCon
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
      -- But then the two neighbours of v cannot be adjacent, because otherwise there would be a cycle
      -- So, A.encard >= 2, contradiction
      sorry

    -- If every vertex has degree <= 1, then S.encard = 0, so we are done
    have : ¬G.Connected := by sorry
    have Sempty : S.encard = 0 := by
      have esSep : IsSepSet G ∅ := by
        refine ⟨empty_subset V(G), ?_⟩
        rw [vertexDelete_empty]
        assumption
      have : S.encard = (∅ : Set α).encard := by
        have := HS.2 ∅ esSep
        simp_all
      simp_all
    have Vnz : V(G).ncard ≠ 0 := by linarith
    simp at Vnz
    rw [ncard_eq_zero (finite_of_ncard_nonzero Vnz)] at Vnz
    have ⟨v, hv⟩ : ∃ v, v ∈ V(G) := by grind only [= mem_empty_iff_false]
    have hGI : G.IsIndependent {v} := ⟨by simp_all, by simp_all⟩
    have := hA.2 {v} hGI
    simp_all

  let S := {C : WList α β | G.IsCycle C }
  have hsne : S.Nonempty := by
    exact nonempty_of_mem hC'
  have hsfin : ((length ) '' S).Finite := sorry
  --THe following obtains a cycle of G that is maximal in length
  obtain ⟨C, hCs⟩ := hsfin.exists_maximalFor' _ _ hsne
  --Now that we got a max cycle, we have two cases
  obtain ( hn| hlen ) := Decidable.em (C.length = V(G).ncard  )
  · use C
    refine ⟨ hCs.prop , hn ⟩
  --There should be an obvious bound on the size of a cycle
  have hCle : C.length < V(G).ncard := by sorry
  let VC := {v ∈ V(G) | v ∈ C.vertex}
  --have ⟨v, hvV ⟩ : ∃ v, v ∉ C.vertex := sorry
  have hG : V(G-(VC)).Nonempty := by
    -- have hg : V(G) \ VC = ∅ := by sorry
    -- have hg1 : VC ⊆ V(G) := by sorry
    -- have hconcl : V(G) ⊆ VC  := by exact diff_eq_empty.mp hg
    -- have hconclusion : V(G) = VC  := by exact Subset.antisymm hconcl hg1
    sorry
  have ⟨D, hD ⟩ := exists_IsCompOf hG
  let Neig := {v : α | v ∈ C.vertex ∧ (neighbour_of_Set G V(D) v) }
  --This is the second worst sorry
  have hDadj : ∀ v, v ∈ Neig → ∀ u, u ∈ Neig
      → C.idxOf v ≠ C.idxOf u + 1 := by
    intro v hvN u huN
    by_contra hcon
    obtain ⟨ w, hwD, hwad ⟩ := hvN.2
    obtain ⟨ w', huD, huad ⟩ := huN.2
    --Need to take path in D from w to w' and extend cycle
    sorry
  let NextNeigh := {v ∈ V(G) | ∃ w ∈ Neig, C.idxOf v = C.idxOf w + 1 }
  have ⟨ v, hvD ⟩ : ∃ v, v ∈ V(D) := by
    have : V(D).Nonempty := by sorry
    sorry
  --I'm not sure how much you need this one
  --Worst sorry
  have hNNI : IsIndependent G NextNeigh := by sorry
  have hNNIv : IsIndependent G ( insert v NextNeigh) := by sorry
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
