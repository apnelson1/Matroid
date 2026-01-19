import Matroid.Graph.Independent
import Matroid.Graph.Connected.Menger
import Matroid.ForMathlib.Minimal

import Matroid.Exercises.HamiltonianCycle.Degree
import Matroid.Exercises.HamiltonianCycle.Walk
import Matroid.Exercises.HamiltonianCycle.Connected
import Matroid.Exercises.HamiltonianCycle.Bipartite

-- TODO: remember to remove this Loogle import at the end of the project
import Loogle.Find

open Qq Lean Meta Elab Tactic WList Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H T : Graph α β} {P C w w₁ w₂ : WList α β}
  {A S : Set α}

/- Theorem 10.1.1 (Dirac 1952)
Every graph with n >= 3 vertices and minimum degree at least n/2 has a Hamiltonian cycle.
-/

--The exercises start here
@[deprecated "use IsCompOf.subset" (since := "2025-11-28")]
lemma isCompOf_subset (hHG : H.IsCompOf G) : V(H) ⊆ V(G) :=
  hHG.isClosedSubgraph.vertexSet_mono

@[gcongr]
lemma IsClosedSubgraph.minDegree_le_minDegree [G.LocallyFinite] (hHG : H ≤c G)
    (hHne : V(H).Nonempty) : G.minDegree ≤ H.minDegree := by
  obtain ⟨v, hv, hveq⟩ := H.exists_vertex_minDegree hHne
  rw [←hveq, hHG.degree_eq hv]
  exact minDegree_le_degree <| hHG.vertexSet_mono hv

@[gcongr]
lemma IsCompOf.minDegree_le_minDegree [G.LocallyFinite] (hHG : H.IsCompOf G) :
    G.minDegree ≤ H.minDegree :=
  hHG.isClosedSubgraph.minDegree_le_minDegree hHG.nonempty

lemma IsSpanningSubgraph.minDegree_le_minDegree [G.LocallyFinite] (hHG : H ≤s G) :
    H.minDegree ≤ G.minDegree := by
    --The following two haves are used in the obtain.
    --First one follows from H being a component of a finite graph
  have Hfin : H.LocallyFinite := LocallyFinite.mono (by assumption) hHG.le
  obtain rfl | hH := H.eq_bot_or_vertexSet_nonempty
  · simp
  obtain ⟨v, hv, hveq⟩ := H.exists_vertex_minDegree hH
  obtain ⟨w, gw, gweq⟩ := G.exists_vertex_minDegree (hHG.vertexSet_eq ▸ hH)
  have h1 : H.degree w ≤ G.degree w := degree_mono hHG.le w
  have h2 : H.minDegree ≤ H.degree w := minDegree_le_degree <| hHG.vertexSet_eq ▸ gw
  omega

def ConnectivityGE (G : Graph α β) (k : ℕ∞) : Prop :=
  ∀ S : Set α, S.encard < k → (G - S).Connected

lemma Connected.exists_vertex_eDegree_ge_two (hT : T.Connected) (hV : 3 ≤ V(T).encard) :
    ∃ x ∈ V(T), 2 ≤ T.eDegree x := by
  have hMinDeg := hT.degreePos (by rw [← one_lt_encard_iff_nontrivial]; enat_to_nat!; omega)
  by_contra! hyp
  replace hyp : ∀ x ∈ V(T), T.eDegree x = 1 := by
    intro x hxT
    specialize hyp _ hxT
    have := hMinDeg.one_le_eDegree hxT
    enat_to_nat! <;> omega
  clear hMinDeg
  have hT_nonempty : V(T).Nonempty := by
    simp only [←Set.encard_pos]
    enat_to_nat!
    omega
  have ⟨x, hxT⟩ := hT_nonempty
  have hx_ssub : {x} ⊂ V(T) := by
    refine ⟨by rw [singleton_subset_iff]; tauto, fun bad ↦ ?_⟩
    have := encard_singleton _ ▸ Set.encard_le_encard bad
    enat_to_nat!
    omega
  rw [connected_iff_forall_exists_adj hT_nonempty] at hT
  obtain ⟨y, ⟨hyT, hne⟩, hadj⟩ := by simpa [←ne_eq] using hT _ hx_ssub (by simp)
  have hxy_ssub : {x, y} ⊂ V(T) := by
    refine ssubset_of_subset_of_ne (pair_subset hxT hyT) ?_
    apply_fun Set.encard
    have := encard_pair_le x y
    enat_to_nat!
    omega
  obtain ⟨x', (rfl | rfl), z, hz⟩ := hT _ hxy_ssub (by simp)
    <;> apply hz.1.2
    <;> [right; (left; symm at hadj)]
    <;> exact unique_neighbor_of_eDegree_eq_one (hyp _ ‹_›) hz.2 ‹_›

lemma IsTree.exists_vertex_eDegree_ge_two (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ x ∈ V(T), 2 ≤ T.eDegree x :=
  hT.connected.exists_vertex_eDegree_ge_two hV

lemma Connected.exists_length_two_path_of_simple [T.Simple] (hT : T.Connected)
    (hV : 3 ≤ V(T).encard) : ∃ P, T.IsPath P ∧ P.length = 2 := by
  have ⟨x, hxT, hx⟩ : ∃ x ∈ V(T), 2 ≤ T.eDegree x := hT.exists_vertex_eDegree_ge_two hV
  rw [eDegree_eq_encard_adj] at hx
  have ⟨N, hN_sub, hN_encard⟩ := Set.exists_subset_encard_eq hx
  rw [Set.encard_eq_two] at hN_encard
  obtain ⟨y, z, hne, rfl⟩ := hN_encard
  -- pick a path between y and z which does not go through x
  obtain ⟨⟨ey, hey⟩, ⟨ez, hez⟩⟩ := by simpa [pair_subset_iff] using hN_sub
  refine ⟨cons y ey (cons x ez (nil z)), ?_, by simp⟩
  simp [hey.adj.ne.symm, hez.adj.ne, hez, hey.symm, hne, hez.right_mem]

lemma IsTree.exists_length_two_path (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ P, T.IsPath P ∧ P.length = 2 := by
  have := hT.isForest.simple
  exact hT.connected.exists_length_two_path_of_simple hV

-- the same as previous lemma, just reworded
lemma IsTree.exists_nontrivial_path (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ P, T.IsPath P ∧ P.Nontrivial := by
  obtain ⟨P, P_isPath, P_length⟩ := hT.exists_length_two_path hV
  refine ⟨P, P_isPath, ?_⟩
  rw [←WList.two_le_length_iff]
  omega

-- lemma IsForest.exists_not_adj (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
--     ∃ x ∈ V(G), ∃ y ∈ V(G), ¬ T.Adj x y := by
--   by_contra! h
--   have ⟨x, hx⟩ : V(T).Nonempty := nonempty_of_encard_ne_zero (by sorry)

lemma IsForest.exists_isSepSet' (hT : T.IsForest) (hV : 3 ≤ V(T).encard) :
    ∃ S, IsSep T S ∧ S.encard = 1 := by

  sorry

lemma IsForest.exists_isSepSet (hT : T.IsForest) (hV : 3 ≤ V(T).encard) :
    ∃ S, IsSep T S ∧ S.encard = 1 := by
  -- If T is not connected (ie. not a tree), then the result is """vacuously""" true.
  obtain (h | hConn) := em' T.Connected
  · exact exists_isSepSet_size_one_of_not_connected hV h
  replace hT : T.IsTree := ⟨hT, hConn⟩

  -- we show there exists a vertex x of degree at least 2, in which case
  -- the singleton {x} is exactly our sepset
  have ⟨x, hxT, hx⟩ : ∃ x ∈ V(T), 2 ≤ T.eDegree x :=
    hT.exists_vertex_eDegree_ge_two hV

  -- now we have our vertex x of degree ≥ 2
  refine ⟨{x}, ?_, by simp⟩
  simp only [isSep_iff, singleton_subset_iff]
  refine ⟨hxT, ?_⟩
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
  have ⟨hyT', hzT'⟩ : y ∈ V(T - x) ∧ z ∈ V(T - x) := by
    simp
    have := hT.isForest.loopless
    refine ⟨⟨hy.right_mem, ?_⟩, ⟨hz.right_mem, ?_⟩⟩
      <;> rintro rfl <;> apply T.not_adj_self <;> assumption
  obtain ⟨P, hP, hP_first, hP_last⟩ := (bad.connBetween hyT' hzT').exists_isPath
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
    have := hQ'_isPath.cons_isCycle_of_nontrivial (G := T) (P := Q') (e := xz)
    simp only [first_cons, last_cons, hP_last, hxz, cons_nontrivial_iff, forall_const, Q'] at this
    apply this
    by_contra! bad
    apply hne
    rw [←hP_first, ←hP_last]
    exact Nil.first_eq_last bad
  exact hT.isForest _ hQ_isCycle

lemma IsTree.exists_isMinSepSet (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ S, IsMinSep T S ∧ S.encard = 1 := by
  obtain ⟨S, hS, hS_encard⟩ := hT.isForest.exists_isSepSet hV
  refine ⟨S, ⟨hS, ?_⟩, hS_encard⟩
  intro A hA
  by_contra! hcon
  replace hcon : A.encard = 0 := by enat_to_nat! <;> omega
  obtain rfl := by simpa using hcon
  simp [hT.connected] at hA

lemma Bound_on_indepSet {G : Graph α β} [G.Simple] [G.Finite]
    (S : Set (α)) (hS : IsSep G S)
    (H : Graph α β ) (hH : IsCompOf H (G-S) )
    (A : Set (α)) (hA : IsMaxIndependent G A) ( v : α ) (hx : v ∈ V(H) ∩ A )
    : G.degree v + (A ∩ V(H)).ncard ≤ (V(H)).ncard + S.ncard := by
    -- Need degree_eq_ncard_adj, will work after update
  let Inc := {w | G.Adj v w}
  let IncW := {w | G.Adj v w} ∩ V(H)
  have gfin : V(G).Finite := by exact vertexSet_finite
  have hc1 : IncW ⊆ V(H) := by
    exact inter_subset_right
  have hc2 : (A ∩ V(H)) ⊆ V(H) := by
    exact inter_subset_right
  have hfin1 : IncW ∪ (A∩ V(H))  ⊆ V(H) := by exact union_subset hc1 hc2
  have hfin : V(H).Finite := by
    have : V(H) ⊆ V(G) := by
      have := (hH.isClosedSubgraph).vertexSet_mono
      rw [vertexDelete_vertexSet] at this
      -- have : V(G) \ S ⊆ V(G) := by
      --   exact diff_subset
      (expose_names; exact fun ⦃a⦄ a_1 ↦ diff_subset (this a_1))
      -- sorry -- look up set difference is subset
      --IsClosedSubgraph.vertexSet_mono
    exact Finite.subset gfin this
  --For the following you need that the sets are disjoint
  have disjoint : Inc ∩ (A ∩ V(H)) = ∅ := by
    by_contra hcon
    have ⟨ w, hw ⟩  : ∃ e, e ∈ Inc ∩ (A ∩ V(H)) := by
      refine nonempty_def.mp (nonempty_iff_ne_empty.mpr hcon)
      -- exact nonempty_iff_ne_empty.mpr hcon
    have hvw : G.Adj v w := by
      have h1 : w ∈ Inc := by exact mem_of_mem_inter_left hw
      exact h1
    -- want contradiction: w and v are not adjacent
    have hco: ¬ G.Adj v w := by
      have h2 : IsIndependent G A := by exact hA.1
      -- want v ∈ A and w ∈ A
      have hvA : v ∈ A := by exact mem_of_mem_inter_right hx
      have hwA : w ∈ A := by
        have hwAVH : w ∈ A ∩ V(H) := by exact mem_of_mem_inter_right hw
        exact mem_of_mem_inter_left hwAVH
      apply h2.2
      exact hvA
      exact hwA
      by_contra hc
      rw [hc] at hvw
      -- have : ¬ G.Adj w w := by exact not_adj_self G w
      exact (not_adj_self G w) hvw
    exact hco hvw

  have hf1 : (Inc ∪ (A ∩ V(H))).ncard = Inc.ncard + (A ∩ V(H)).ncard := by
    -- have finite : (A ∩ V(H)).Finite := by
    --   have : (A ∩ V(H)) ⊆ V(G) := by
    --     have : (A ∩ V(H)) ⊆ A := by exact inter_subset_left
    --     -- H is a component of G
    --     have : A ⊆ V(G) := by
    --       exact hA.1.1
    --     exact fun ⦃a⦄ a_1 ↦ hA.1.1 (inter_subset_left a_1)
    --   exact Finite.inter_of_right hfin A
    apply ncard_union_eq
    exact disjoint_iff_inter_eq_empty.mpr disjoint
    have incfin : Inc.Finite := by
      refine Set.Finite.subset ?_ (G.neighbor_subset v)
      exact gfin
    -- exact finite_setOf_adj G
    -- exact Finite.subset gfin ( fun ⦃a⦄ a_1 ↦ (hA.1.1) (inter_subset_left a_1))
    exact incfin
    exact Finite.inter_of_right hfin A


-- S: separating set such that V(G) - S is not connected
  have hf2 : (V(H) ∪ S).ncard = V(H).ncard + S.ncard := by
    have hsdisjoint : V(H) ∩ S = ∅ := by
      by_contra hcon
      have ⟨ w, hw ⟩ : ∃ e, e ∈ V(H) ∩ S := by
        refine nonempty_def.mp (nonempty_iff_ne_empty.mpr hcon)
        -- exact nonempty_iff_ne_empty.mpr hcon
      -- hH: H is comp of G - S
      rcases hw with ⟨ hwH, hwS ⟩
      -- have hHsubset : V(H) ⊆ V(G - S) := by
      --   exact IsCompOf.subset hH
      have hwnotinS : w ∈ V(G - S) := by
        exact (IsCompOf.subset hH) hwH
      have hwnotinS1 : w ∉ S := by
        rw [vertexDelete_vertexSet] at hwnotinS
        simp at hwnotinS
        exact notMem_of_mem_diff hwnotinS
      exact hwnotinS1 hwS
    -- have hfin : V(H).Finite := by
    --   have : V(H) ⊆ V(G) := by
    --     have := (hH.isClosedSubgraph).vertexSet_mono
    --     rw [vertexDelete_vertexSet] at this
    --     sorry -- look up set difference is subset
    --     --IsClosedSubgraph.vertexSet_mono
    --   exact Finite.subset gfin this
    apply ncard_union_eq
    exact disjoint_iff_inter_eq_empty.mpr hsdisjoint
    -- have sfin : S.Finite := by exact Finite.subset gfin hS.1
    exact hfin
    exact Finite.subset gfin hS.1
  --Use degree_eq_ncard_adj
  -- should be the same as hf1

  -- deg of v is the cardinality of Inc
  have hdeg : G.degree v = Inc.ncard := by exact degree_eq_ncard_adj
  --This one should be straight forward

  have h1 : Inc ∪ (A ∩ V(H)) = (IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) := by
    have hinc : Inc = IncW ∪ (Inc\IncW) := by
      refine Eq.symm (union_diff_cancel' (fun ⦃a⦄ a_1 ↦ a_1) inter_subset_left)
    nth_rewrite 1 [hinc]
    exact union_right_comm IncW (Inc \ IncW) (A ∩ V(H))

 --Again, disjoint sets
  have hf3 : ((IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) ).ncard =
      (IncW ∪ (A ∩ V(H))).ncard + (Inc\IncW).ncard
    := by
      have disjoint : (IncW ∪ (A ∩ V(H))) ∩ (Inc\IncW) = ∅ := by
        by_contra hcon
        have ⟨ w, hw ⟩ : ∃ e, e ∈ (IncW ∪ (A ∩ V(H))) ∩ (Inc\IncW) := by
          refine nonempty_def.mp (nonempty_iff_ne_empty.mpr hcon)
        -- elements in IncW are in Inc ∩ V(H), so elements in Inc\IncW are not in V(H)
        --have hw1 : w ∈ (IncW ∪ A ∩ V(H)) := by exact mem_of_mem_inter_left hw
        --have hw2 := by exact mem_of_mem_inter_right hw
        rcases hw with ⟨ hw1, hw2 ⟩
        -- prove that in (Inc\IncW), w ∉ V(H)
        have wnotinInc : w ∉ IncW := by exact notMem_of_mem_diff hw2
        have wnotinH : w ∉ V(H) := by
          intro winH
          have winInc : w ∈ IncW := by
            exact ⟨ hw2.left, winH ⟩
          exact wnotinInc winInc
        -- rcases hw1 with ⟨ hw1inc, hw2a ⟩
        -- have wnotinInc : w ∉ IncW := by exact notMem_of_mem_diff hw2
        -- -- prove that in (IncW ∪ (A ∩ V(H))), w ∈ V(H)??
        have winH : w ∈ V(H) := by
          exact hfin1 hw1
        exact wnotinH winH
      refine ncard_union_eq (disjoint_iff_inter_eq_empty.mpr disjoint) ?_ ?_
      -- exact disjoint_iff_inter_eq_empty.mpr disjoint
      have incWfin : IncW.Finite := by
        refine Finite.inter_of_right ?_ {w | G.Adj v w}
        exact hfin
      have incfin : (IncW ∪ (A ∩ V(H))).Finite := by
        have : (A ∩ V(H)).Finite := by
          have : (A ∩ V(H)) ⊆ A := by exact inter_subset_left
          have : A ⊆ V(G) := by exact hA.1.1
          have : (A ∩ V(H)) ⊆ V(G) := by (expose_names; exact fun ⦃a⦄ a_1 ↦ this (this_1 a_1))
          exact Finite.subset gfin this -- clean this up later
        exact Finite.union incWfin this
      exact incfin

      have : (Inc \ IncW) ⊆ V(G) := by
        have : (Inc \ IncW) ⊆ Inc := by exact diff_subset
        have : Inc ⊆ V(G) := by
          intro u hu
          exact hu.right_mem
        (expose_names; exact fun ⦃a⦄ a_1 ↦ this (this_1 a_1))
      exact Finite.subset gfin this
  --Very important
  rw [←hf2,hdeg,←hf1,h1, hf3 ]

  --Inequalities to finish
  -- IncW ∪ (A ∩ V(H)) is
  have hH : (IncW ∪ (A ∩ V(H))).ncard ≤ V(H).ncard := by
    have hH1 : (IncW ∪ (A ∩ V(H))) ⊆ V(H) := by
      -- have : (A ∩ V(H)) ⊆ V(H) := by exact inter_subset_right
      -- have : IncW ⊆ V(H) := by exact inter_subset_right
      exact union_subset inter_subset_right inter_subset_right
    refine ncard_le_ncard hH1 ?_
    -- have : V(H) ⊆ V(G-S) := by exact isCompOf_subset (G - S) H hH
    have hs : V(G-S) ⊆ V(G) := by
      rw [vertexDelete_vertexSet]
      exact diff_subset
    have : V(H) ⊆ V(G) := by exact fun ⦃a⦄ a_1 ↦ hs (IsCompOf.subset hH a_1)
    have gfin : V(G).Finite := by exact vertexSet_finite
    exact Finite.subset gfin this

  have hS : (Inc\IncW).ncard ≤ S.ncard := by
    have hH1 :(Inc\IncW) ⊆ S := by
      -- want to prove that w ∈ Inc\IncW => w ∈ S
      -- things in Inc cannot be in H?, look for lemma in connected file
      -- by cases: if Inc, then in IncW, otherwise contradiction from connectedness
      intro w hw
      rcases hw with ⟨ hwInc, hwnotinIncW ⟩
      -- if w is in Inc and not in IncW, then w is also not in V(H) since IncW = Inc ∩ V(H)
      have hwnotinH : w ∉ V(H) := by
        by_contra hcon1
        -- have : w ∈ IncW := by exact mem_inter hwInc hcon1
        exact hwnotinIncW (mem_inter hwInc hcon1)
      -- need w ∈ S
      -- if w not in V(H) ⊆ V(G - S), then w must be in S?

      sorry
    refine ncard_le_ncard hH1 (Finite.subset gfin hS.1)
    -- exact Finite.subset gfin hS.1
  linarith

--Again, is missing when G is complete but whatever
lemma indep_to_Dirac [G.Simple] [G.Finite] (h3 : 3 ≤ V(G).ncard)
    (S : Set (α)) (HS : IsMinSep G S )
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

  have hNeBotS : V(G - S).Nonempty := by
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
    have := Bound_on_indepSet _ HS.1 _ hccH1 _ hA (by tauto)

    sorry

  --Easy case
  obtain ⟨y, yA2⟩ := nonempty_iff_ne_empty.mpr hAH1

  --Use Bound_on_indepSet twice and linarith to conclude. You'll also need
  have h1 : (V(H1)).ncard + S.ncard + (V(H2)).ncard + S.ncard = V(G).ncard + S.ncard := by sorry
  -- Add hDirac applied to y
  sorry

def IsHamiltonCycle (G : Graph α β) (C : WList α β) : Prop :=
  G.IsCycle C ∧ V(G) ⊆ V(C)

lemma IsHamiltonCycle.isCycle (hC : G.IsHamiltonCycle C) : G.IsCycle C := hC.1
lemma IsHamiltonCycle.vertexSet_supset (hC : G.IsHamiltonCycle C) : V(G) ⊆ V(C) := hC.2

lemma IsHamiltonCycle.vertexSet_eq (hC : G.IsHamiltonCycle C) : V(C) = V(G) := by
  refine hC.isCycle.vertexSet_subset.antisymm hC.vertexSet_supset

lemma IsHamiltonCycle.vertexSet_encard_eq
    (hC : G.IsHamiltonCycle C) : V(C).encard = V(G).encard :=
  congr_arg Set.encard hC.vertexSet_eq

lemma isHamiltonianCycle_iff : G.IsHamiltonCycle C ↔ G.IsCycle C ∧ V(G) = V(C) :=
  ⟨fun h ↦ ⟨h.isCycle, h.vertexSet_eq.symm⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂.subset⟩⟩

protected
lemma IsCycle.isHamiltonianCycle_iff (hC : G.IsCycle C) : G.IsHamiltonCycle C ↔ V(G) = V(C) :=
  ⟨fun h ↦ (isHamiltonianCycle_iff.mp h).2, fun h ↦ ⟨hC, h.le⟩⟩

-- Note: this is always true because WLists are finite
lemma isHamilonianCycle_of_vertexSet_encard_eq
    (hC : G.IsCycle C) (hen : V(C).encard = V(G).encard) : G.IsHamiltonCycle C := by
  refine ⟨hC, Eq.subset ?_⟩
  symm
  exact Set.Finite.eq_of_subset_of_encard_le C.vertexSet_finite hC.vertexSet_subset hen.symm.le

def SetVxAdj (G : Graph α β) (H : Set α) (v : α) : Prop :=
    ∃ w, w ∈ H ∧ G.Adj v w

lemma IsCycle_length_bound (hC : G.IsCycle C) : C.length ≤ V(G).encard := by
  have hsubs := hC.isWalk.vertexSet_subset
  have : C.length = V(C).encard := by
    sorry
  sorry

--Noah, here is the lemma thats not liking me

lemma Hamiltonian_to_cycle (hham : ∃ C, G.IsHamiltonCycle C) : ∃ C, G.IsCycle C  := by
  obtain ⟨C, hC⟩ := hham
  exact ⟨C, hC.1⟩

variable [DecidableEq α]

lemma IsPath.exists_isPath_vertex (hP : G.IsPath P) (hu : u ∈ P) :
    ∃ P₀ P₁, G.IsPath P₀ ∧ G.IsPath P₁ ∧ u = P₀.last ∧ u = P₁.first ∧ P = (P₀ ++ P₁) := by
  set Pre : WList α β := prefixUntilVertex P u with h_pre
  set Suf : WList α β := suffixFromVertex P u with h_suf
  use Pre, Suf
  rw [h_pre,h_suf]
  refine ⟨hP.prefix (P.prefixUntilVertex_isPrefix u), hP.suffix (P.suffixFromVertex_isSuffix u),
    (prefixUntilVertex_last hu).symm, (suffixFromVertex_first hu).symm,
    (prefixUntilVertex_append_suffixFromVertex P u).symm⟩

omit [DecidableEq α] in
lemma IsCompOf.exists_path (hHco : H.IsCompOf G) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    ∃ P, H.IsPath P ∧ P.first = x ∧ P.last = y := by
  apply ConnBetween.exists_isPath
  rw [hHco.eq_walkable_of_mem_walkable hx] at hy
  exact (connBetween_iff_mem_walkable_of_mem.2 hy).isClosedSubgraph hHco.isClosedSubgraph hx

omit [DecidableEq α] in
lemma Hamiltonian_alpha_kappa_exists_cycle [G.Simple] [G.Finite] (h3 : 3 ≤ V(G).encard)
    (hS : IsMinSep G S) (hA : IsMaxIndependent G A) (hAS : A.encard ≤ S.encard) :
    ∃ C, G.IsCycle C := by
  -- The proof should be an easy combination of a few things:
  -- 1 : In a tree on at least three vertices, the `MinSepSet` has size `1`.
  -- 2 : In a bipartite graph, the `MaxIndependentSet` contains at least half the vertices.
  -- 3 : Trees are bipartite.
  -- 4 : Therefore, in a tree on at least three vertices, the hypothesis `A.encard ≤ S.encard` is
  --      impossible.
  -- 5 : Therefore, `G` has a cycle.

  -- First, we show that it must be connected.
  obtain (rfl | hConn) := S.eq_empty_or_nonempty
  · obtain rfl := by simpa using hAS
    obtain rfl := by simpa using hA
    simp at h3
  rw [← hS.connected_iff] at hConn

  -- Now, proceed by contradiction.
  by_contra! h_isForest
  have h_isTree : G.IsTree := ⟨h_isForest, hConn⟩
  -- 1 : In a tree on at least three vertices, the `MinSepSet` has size `1`.
  have S_encard : S.encard = 1 := by
    obtain ⟨S', hS', hS'_encard⟩ := h_isTree.exists_isMinSepSet h3
    rw [←hS'_encard]
    exact hS.encard_eq_encard_of_isMinSep hS'
  -- 3 : Trees are bipartite.
  have ⟨B⟩ := IsForest.bipartite h_isForest
  -- 2 : In a bipartite graph, the `MaxIndependentSet` contains at least half the vertices.
  have A_encard : V(G).encard ≤ 2 * A.encard := B.isMaxIndependent_encard_ge hA
  -- 4 : Therefore, in a tree on at least three vertices, the hypothesis `A.encard ≤ S.encard` is
  --      impossible.
  enat_to_nat!; omega

omit [DecidableEq α] in
lemma Connected.exist_path {D : Graph α β } (hDconn : D.Connected) (hx : x ∈ V(D)) (hy : y ∈ V(D)) :
    ∃ P, D.IsPath P ∧ P.first = x ∧ P.last = y := by
  apply ConnBetween.exists_isPath
  exact hDconn.connBetween hx hy



lemma indep_nbrs [G.Simple] [G.Finite] {i j : ℕ} {G D : Graph α β} {C : WList α β}
    (hCs : MaximalFor G.IsCycle length C) (hDC : D ≤ G - V(C)) (hDconn : D.Connected)
    (hnt : C.Nonempty)
    (hi : i ∈  {i ≤ C.length | G.SetVxAdj V(D) (C.get i)})
    (hj : j ∈ {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} ) (hij : i ≤ j ) : j ≠ i + 1 := by
  by_contra hindex
  wlog hi0 : i = 0 generalizing i j C with aux
  · refine aux (C := C.rotate i) (i := 0) (j := 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rwa [maximalFor_congr_val (y := C) (by simp) (by simp [hCs.prop, hCs.prop.rotate])]
    · rwa [hCs.prop.isClosed.rotate_vertexSet]
    · exact (rotate_nonempty_iff i).mpr hnt
    · simp only [length_rotate, mem_setOf_eq, zero_le, true_and]
      have : i + 0 ≤ C.length := by
        simp only [add_zero]
        exact hi.1
      rw[get_rotate C this ]
      simp only [add_zero]
      exact hi.2
    · simp only [length_rotate, mem_setOf_eq, one_le_length_iff]
      refine ⟨hnt, ?_ ⟩
      have : i + 1 ≤ C.length := by
        rw[← hindex ]
        exact hj.1
      rw[get_rotate C this ]
      rw[←hindex]
      exact hj.2
    · omega
    · omega
    omega

  sorry


-- lemma indep_nbrs [G.Simple] [G.Finite] {G D : Graph α β} {C : WList α β}
--     (hCs : MaximalFor G.IsCycle length C) (hDC : D ≤ G - V(C)) (hDconn : D.Connected)
--     (hnt : C.Nonempty) :
--     G.IsIndependent <| C.get '' {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} := by
--   rw [isIndependent_iff (by grw [image_subset_range, range_get, hCs.prop.vertexSet_subset])]
--   simp only [mem_image, mem_setOf_eq, ne_eq, forall_exists_index, and_imp]
--   rintro _ _ i hi hiD rfl j hj hjD rfl hij hadj
--   wlog hlt : i ≤ j generalizing i j with aux
--   · exact aux j hj hjD i hi hiD (Ne.symm hij) hadj.symm (not_le.1 hlt).le
--   obtain ⟨d, rfl⟩ := exists_add_of_le hlt

--   wlog hi0 : i = 0 generalizing i d C with aux
--   · refine aux (C := C.rotate i) ?_ ?_ ?_ 0 ?_ ?_ d ?_ ?_ ?_ ?_ ?_ ?_
--     · rwa [maximalFor_congr_val (y := C) (by simp) (by simp [hCs.prop, hCs.prop.rotate])]
--     · rwa [hCs.prop.isClosed.rotate_vertexSet]
--     · sorry
--     · simp only [length_rotate, zero_le]
--     · rwa [get_zero, rotate_first _ _ hi]
--     · simp only [zero_add, length_rotate]
--       omega
--     · simp only [zero_add]
--       --rwa [get_rotate _ hj]
--       sorry
--     · simp only [get_zero, zero_add]
--       --rwa [get_rotate _ hj, rotate_first _ _ hi.le]
--       sorry
--     · simp only [get_zero, zero_add]
--       --rwa [rotate_first _ _ hi.le, get_rotate _ hj]
--       sorry
--     · simp
--     rfl
--   obtain rfl := hi0
--   -- now `i` is zero!
--   simp_all only [ zero_add, get_zero, zero_le]
--   set a : α := C.get (0) with h_a
--   set b : α := C.get (d) with h_b
--   have ha : a ∈ C := by exact get_mem C 0
--   have hb : b ∈ C := by exact get_mem C d
--   obtain ⟨ wb, h1D, hadjaw ⟩ := hiD
--   obtain ⟨ wa, h2D, hadjbw ⟩ := hjD
--   have hC : G.IsCycle C := by exact hCs.prop
--   have hCNT : C.Nontrivial := by sorry
--   have : G.Loopless := by sorry
--   -- set P : WList α β  := C.tail.dropLast with h_P
--   -- set e : β := hC.nonempty.firstEdge with h_e
--   -- set f : β := hC.nonempty.lastEdge with h_f
--   -- have hP := hC.tail_dropLast_isPath
--   have hafirst : a = C.first := by exact get_zero C
--   rw[←hafirst] at hadj
--   have halast : a = C.last := by
--     rw[←hC.isClosed]
--     exact hafirst
--   obtain ⟨P,e,f, hPath, haP, heP, hfP, hef, hC'⟩ :=
--       IsCycle.exists_isPath_vertex hCs.prop hCNT (get_mem C 0 )
--   rw[ hC.idxOf_get (Nonempty.length_pos hnt) ] at hC'
--   simp only [rotate_zero, get_zero] at hC'
--   rw[←hafirst] at hC'
--   have : a ≠ b := by

--     sorry
--     -- Apply IsCycle.idxOf_Adj




--   sorry

-- lemma indep_nbrsnext [G.Simple] [G.Finite] {G D : Graph α β} {C : WList α β}
--     (hCs : MaximalFor G.IsCycle length C) (hDC : D ≤ G - V(C)) (hDconn : D.Connected) :
--     G.IsIndependent <| C.get '' {i < C.length | G.SetVxAdj V(D) (C.get (i + 1))} := by
lemma indep_nbrsnext [G.Simple] [G.Finite] {D : Graph α β} (hCs : MaximalFor G.IsCycle length C)
    (hDC : D ≤ G - V(C)) (hDconn : D.Connected) :
    G.IsIndependent <| C.get '' {i  < C.length  | G.SetVxAdj V(D) (C.get (i + 1))} := by
    --G.IsIndependent <| C.get '' ((· + 1) '' {i < C.length | G.SetVxAdj V(D) (C.get i)}) := by

  rw [isIndependent_iff (by grw [image_subset_range, range_get, hCs.prop.vertexSet_subset])]
  simp only [mem_image, mem_setOf_eq, ne_eq, forall_exists_index, and_imp]
  rintro _ _ i hi haD rfl j hj hbD rfl hij hadj
  -- _ _ i hi hiD rfl j hj hjD rfl hij hadj
  wlog hlt : i ≤ j generalizing i j with aux
  · exact aux j hj hbD i hi haD (Ne.symm hij) hadj.symm (not_le.1 hlt).le
  obtain ⟨d, rfl⟩ := exists_add_of_le hlt
  wlog hi0 : i = 0 generalizing i d C with aux
  · refine aux (C := C.rotate i) ?_ ?_ 0 ?_ ?_ d ?_ ?_ ?_ ?_ ?_ ?_
    · rwa [maximalFor_congr_val (y := C) (by simp) (by simp [hCs.prop, hCs.prop.rotate])]
    · rwa [hCs.prop.isClosed.rotate_vertexSet]
    · --have := hC.prop.nonempty
      simp [hCs.prop.nonempty]
    · simp only [zero_add]
      have : i + 1 ≤ C.length := by omega
      rw[get_rotate C this]
      exact haD
    · simp only [zero_add, length_rotate]
      omega
    · simp only [zero_add]
      have : i + (d + 1) ≤ C.length := by omega
      rw[get_rotate C this]
      exact hbD
    · simp only [get_zero, zero_add]
      have : i + d ≤ C.length := by omega
      have h0' : i + 0 ≤ C.length := by omega
      rw[get_rotate C this, ←get_zero, get_rotate C h0', add_zero]
      exact hij
    · simp only [get_zero, zero_add]
      --rwa [rotate_first _ _ hi.le, get_rotate _ hj]
      have h0' : i + 0 ≤ C.length := by omega
      have : i + d ≤ C.length := by omega
      rw[←get_zero, get_rotate C this, get_rotate C h0', add_zero]
      exact hadj
    · simp only [zero_add, zero_le]
    rfl
  obtain rfl := hi0
  simp_all only [ length_pos_iff, zero_add, get_zero, zero_le]
  set a : α := C.get (0) with h_a
  set b : α := C.get (d) with h_b
  set a₁ : α := C.get (1) with h_a1
  set b₁ : α := C.get (d + 1) with h_b1
  have ha : a ∈ C := by exact get_mem C 0
  have hb : b ∈ C := by exact get_mem C d
  have ha₁ : a₁ ∈ C := by exact get_mem C 1
  have hb₁ : b₁ ∈ C := by exact get_mem C (d + 1)
  obtain ⟨ wb, h1D, hadjaw ⟩ := hbD
  obtain ⟨ wa, h2D, hadjbw ⟩ := haD
  have hC : G.IsCycle C := by exact hCs.prop
  have hCNT : C.Nontrivial := by sorry
  have : G.Loopless := by sorry
  -- set P : WList α β  := C.tail.dropLast with h_P
  -- set e : β := hC.nonempty.firstEdge with h_e
  -- set f : β := hC.nonempty.lastEdge with h_f
  -- have hP := hC.tail_dropLast_isPath
  have hafirst : a = C.first := by exact get_zero C
  rw[←hafirst] at hadj
  have halast : a = C.last := by
    rw[←hC.isClosed]
    exact hafirst
  obtain ⟨P,e,f, hPath, haP, heP, hfP, hef, hC'⟩ :=
      IsCycle.exists_isPath_vertex hCs.prop hCNT (get_mem C 0 )
  rw[ hC.idxOf_get (Nonempty.length_pos hi) ] at hC'
  simp only [rotate_zero, get_zero] at hC'
  --I think you can skip all of the next part until the next comment
  have haindices : C.idxOf a + 1 = C.idxOf a₁ := by
    rw[h_a,h_a1, hC.idxOf_get (Nonempty.length_pos hi),
        hC.idxOf_get (Nontrivial.one_lt_length hCNT )]
  have hbP : b ∈ P := by
    rw[hC',←hafirst] at hb
    simp only [mem_cons_iff, mem_concat] at hb
    obtain h1 | h2 := hb
    · exact False.elim (hadj.ne  (id (Eq.symm h1)))
    obtain h3 | h4 := h2
    · exact h3
    exact False.elim (hadj.ne  (id (Eq.symm h4)))
  have hab₁ : b₁ ≠ a := by
    by_contra hc
    rw[h_b1, h_a ] at hc
    have h0s : 0 ∈ {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} := by
      simp only [mem_setOf_eq, zero_le, true_and]
      rw[←hc, ←h_b1]
      refine ⟨ wb, h1D, hadjaw ⟩
    have h1s : 1 ∈ {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} := by
      simp only [mem_setOf_eq, one_le_length_iff]
      refine ⟨ hi, ⟨ wa, h2D, hadjbw ⟩ ⟩
    have h01 : 0 ≤ 1 := by omega
    have : 1 ≠ 0 + 1 := by sorry
      --exact indep_nbrs hCs hDC hDconn hi h0s h1s h01
    omega
    -- have hab1 : a₁ ≠ b₁ := by
    --   rw[hc]
    --   by_contra hcc
    --   have hf := hC.idxOf_get (Nonempty.length_pos hi)
    --   rw[←h_a, ←hcc, h_a1, hC.idxOf_get (Nontrivial.one_lt_length hCNT ) ] at hf
    --   omega
    -- have hyes : G.Adj a₁ b₁ := by
    --   rw[hc]
    --   exact (idxOf_Adj (hC.toIsTrail) ha ha₁ haindices.symm).symm
    -- have hS : C.get '' {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} ⊆ V(G) := by
    --   intro x hx
    --   simp only [mem_image, mem_setOf_eq] at hx
    --   obtain ⟨k, hk ⟩ := hx
    --   obtain ⟨ w, hw, hww ⟩ := hk.1.2
    --   have : (C.get k) ∈ V(G) := by exact Adj.right_mem (id (Adj.symm hww))
    --   rwa[hk.2] at this
    -- have hSa : a₁ ∈ C.get '' {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} := by
    --   simp only [mem_image, mem_setOf_eq]
    --   use 1
    --   simp only [one_le_length_iff]
    --   refine ⟨⟨hi, ⟨ wa, h2D, hadjbw ⟩⟩, h_a1 ⟩
    -- have hSb : b₁ ∈ C.get '' {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} := by
    --   simp only [mem_image, mem_setOf_eq]
    --   use d + 1
    --   refine ⟨⟨hj, ⟨ wb, h1D, hadjaw ⟩⟩, h_b1 ⟩

    -- G.IsIndependent <| C.get '' {i ≤ C.length | G.SetVxAdj V(D) (C.get i)} := by
    --   sorry
    --have : ¬ G.Adj a₁ b₁ := by
    --rw[← hc] at haindices



    --(isIndependent_iff hS).1 (hprevlemma) hSa hSb hab1
    --exact this hyes
  have hbindices : C.idxOf b + 1 = C.idxOf b₁ := by
    rw[h_b,h_b1, hC.idxOf_get hj, hC.idxOf_get ]
    by_contra hc
    have hd1 : d + 1 = C.length := by omega
    rw[hd1] at h_b1
    simp only [get_length] at h_b1
    rw[←halast] at h_b1
    exact hab₁ h_b1
  set P₀ : WList α β := prefixUntilVertex P b with h_pre
  set P₁ : WList α β := suffixFromVertex P b with h_suf
  have hP₀ := IsPath.prefix hPath (prefixUntilVertex_isPrefix P b)
  have hP₁ := IsPath.suffix hPath (suffixFromVertex_isSuffix P b)
  rw [←h_pre] at hP₀
  rw [←h_suf] at hP₁
  have hb1P' : b₁ ∈ P := by
    rw [hC',←hafirst] at hb₁
    exact (Cycle_conc_index hab₁ hb₁).1
  have hb1P1 : b₁ ∈ P₁ := by
    have hb1P : b₁ ∈ P := by
      rw [hC',←hafirst] at hb₁
      exact (Cycle_conc_index hab₁ hb₁).1
    rw [Eq.symm (prefixUntilVertex_append_suffixFromVertex P b),←h_pre, ←h_suf] at hb1P
    obtain (hf | hg ):= mem_of_mem_append hb1P
    · rw [h_pre] at hf
      have hcon := (prefixUntilVertex_index_iff hbP hb1P').1 hf
      have hbindP : P.idxOf b + 1 = P.idxOf b₁ := by
        rw[hC',←hafirst] at hb
        have hg1 := (Cycle_conc_index (hadj.ne).symm hb).2
        rw[hC',←hafirst] at hb₁
        have hg2 := (Cycle_conc_index (hab₁) hb₁).2
        rw [hafirst,←hC'] at hg1
        rw [hafirst,←hC'] at hg2
        omega
      omega
    exact hg
  set P₂ : WList α β := prefixUntilVertex P₁ b₁ with h_pre2
  set P₃ : WList α β := suffixFromVertex P₁ b₁ with h_suf2
  have hP₂ := IsPath.prefix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
      (prefixUntilVertex_isPrefix P₁ b₁)
  have hP₃ := IsPath.suffix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
      (suffixFromVertex_isSuffix P₁ b₁)
  rw [←h_pre2] at hP₂
  rw [←h_suf2] at hP₃
  --Elaine, here is the path in D
  obtain ⟨PD, hPD, hPD1,hPD2 ⟩ := hDconn.exist_path h2D h1D
  --Obtain the edge from wb to b₁
  obtain ⟨e₁, he1 ⟩ := hadjaw.symm
  --Adding that edge with the vertex b₁ to the path
  have hPc1 : G.IsPath (PD.concat e₁ b₁) := by
    apply concat_isPath_iff.2
    refine and_assoc.mp ?_
    refine ⟨⟨hPD.of_le (Std.IsPreorder.le_trans D (G - V(C)) G hDC vertexDelete_le), ?_ ⟩, ?_ ⟩
    · rw[←hPD2] at he1
      exact he1
    by_contra hc
    have : V(PD) ⊆ V(G) \ V(C) :=
      fun ⦃a⦄ a_1 ↦ (hDC.vertex_subset) ((hPD.vertexSet_subset ) a_1)
    exact (((this) hc).2) (hb₁ )
  obtain ⟨e₂, he2 ⟩ := (hC.toIsTrail).idxOf_Adj  hb hb₁ hbindices.symm
  have hPlast : (PD.concat e₁ b₁).last = b₁ := by simp
  have hPfirst : P₃.first = b₁ := by
    exact suffixFromVertex_first hb1P1
  --Joining the path P₃ at the end of the path I've been building.
  --You need to check the end of one path is the start of the next one and thats the only vertices
  --they share.
  have hQ₁ : G.IsPath ((PD.concat e₁ b₁) ++ P₃) := by
    apply hPc1.append hP₃ ?_ ?_
    · rw[hPlast, hPfirst]
    intro x hx hx3
    simp only [concat_last]
    simp only [mem_concat] at hx
    obtain hfalse | hgood := hx
    · by_contra
      have hP3C : V(P₃) ⊆ V(C) := by
        have : V(P) ⊆ V(C) := by
          rw[hC']
          simp only [cons_vertexSet, concat_vertexSet_eq, mem_insert_iff, mem_vertexSet_iff,
            true_or, insert_eq_of_mem, subset_insert]
        rw[h_suf2, h_suf]
        have h1 : V((P.suffixFromVertex b).suffixFromVertex b₁) ⊆ V(P) := by
          exact fun ⦃a⦄ a_1 ↦ (suffixFromVertex_vertex P b  )
            ((suffixFromVertex_vertex (P.suffixFromVertex b) b₁) a_1)
        exact fun ⦃a⦄ a_1 ↦ this (h1 a_1)
      have hxnC : x ∉ V(C) := by
        have : V(PD) ⊆ V(G) \ V(C) :=
          fun ⦃a⦄ a_1 ↦ (hDC.vertex_subset) ((hPD.vertexSet_subset ) a_1)
        exact (((this) hfalse).2)
      exact hxnC (hP3C hx3)
    exact hgood
  --End of the concatination
  have hQ₂ : G.IsPath (((PD.concat e₁ b₁) ++ P₃).concat f a) := by
    apply concat_isPath_iff.2
    refine ⟨ hQ₁, ?_, ?_ ⟩
    · simp only [WList.concat_append, append_last, last_cons]
      have h3last : P₃.last = P.last := by
        rw [h_suf2]
        simp only [suffixFromVertex_last]
        rw[h_suf]
        simp only [suffixFromVertex_last]
      rw[h3last]
      have hpcon : G.IsPath (P.concat f a) := by
        rw[hC'] at hC
        have := hC.tail_isPath
        rwa[tail_cons,←hafirst] at this
      exact (concat_isPath_iff.1 hpcon).2.1
    simp only [WList.concat_append, first_cons, mem_append_iff_of_eq, mem_cons_iff, not_or]
    have ha1D : a ∉ V(D) := by
      by_contra hc
      exact (((hDC.vertex_subset ) hc).2) (ha )
    refine ⟨ ?_, ?_, ?_ ⟩
    · by_contra hc
      exact ha1D ((IsPath.vertexSet_subset hPD) hc)
    · by_contra hc
      have hcc : PD.last ∈ V(PD) := by exact last_mem
      rw[←hc] at hcc
      exact ha1D ((IsPath.vertexSet_subset hPD) hcc)
    rw[h_suf2, h_suf]
    have h1 : V((P.suffixFromVertex b).suffixFromVertex b₁) ⊆ V(P) := by
      exact fun ⦃a⦄ a_1 ↦ (suffixFromVertex_vertex P b  )
        ((suffixFromVertex_vertex (P.suffixFromVertex b) b₁) a_1)
    by_contra hc
    exact haP (h1 hc)
  have hab' := hadj
  obtain ⟨eab, heab ⟩ := hadj
  have hQ₃ : G.IsPath ((((PD.concat e₁ b₁) ++ P₃).concat f a).concat eab b) := by
    apply concat_isPath_iff.2
    refine ⟨hQ₂, ?_, ?_ ⟩
    · have : ((PD.concat e₁ b₁ ++ P₃).concat f a).last = a := by simp
      rwa[this]
    simp only [WList.concat_append, mem_concat, first_cons, mem_append_iff_of_eq, mem_cons_iff,
      not_or]
    have hb1D : b ∉ V(D) := by
      by_contra hc
      exact (((hDC.vertex_subset ) hc).2) (hb )
    refine ⟨ ⟨?_, ?_, ?_⟩, (ne_of_mem_of_not_mem hbP haP ) ⟩
    · by_contra hc
      exact hb1D ((IsPath.vertexSet_subset hPD) hc)
    · by_contra hc
      have hcc : PD.last ∈ V(PD) := by exact last_mem
      rw[←hc] at hcc
      exact hb1D ((IsPath.vertexSet_subset hPD) hcc)
    · rw[h_suf2 ]
      have hbPre : b ∈ P₁.prefixUntilVertex b₁ := by
        rw[h_suf ]
        have : b = ((P.suffixFromVertex b).prefixUntilVertex b₁).first := by
          simp only [prefixUntilVertex_first]
          exact Eq.symm (suffixFromVertex_first hbP)
        rw [this]
        nth_rw 1 [←this]
        exact first_mem
      by_contra hc
      exact ((hC.isTrail).idxOf_Adj hb hb₁ hbindices.symm).ne.symm
        (Prefix_Suffix_int hP₁ hbPre hc hb1P1 )
  have hQ₄ : G.IsPath (((((PD.concat e₁ b₁) ++ P₃).concat f a).concat eab b) ++ P₀.reverse) := by
    apply hQ₃.append (reverse_isPath_iff.mpr hP₀ ) ?_ ?_
    · simp only [WList.concat_append, concat_last, reverse_first]
      rw[h_pre]
      exact Eq.symm (prefixUntilVertex_last hbP)
    intro x hx hxx
    simp only [WList.concat_append, concat_last]
    simp only [WList.concat_append, mem_concat, first_cons, mem_append_iff_of_eq,
      mem_cons_iff] at hx
    obtain h1 | h2 := hx
    · have hsi : x ∉ PD := by
        by_contra hc
        have hxC : x ∈ V(C) := by
          rw[hC']
          rw[h_pre] at hxx
          simp only [mem_reverse] at hxx
          simp only [cons_vertexSet, concat_vertexSet_eq, mem_insert_iff, mem_vertexSet_iff,
            true_or, insert_eq_of_mem]
          right
          exact ((prefixUntilVertex_vertex P b ) hxx )
        have hxD : x ∉ V(D) := by
          by_contra hcc
          exact (((hDC.vertex_subset ) hcc).2) (hxC )
        exact hxD ((IsPath.vertexSet_subset hPD) hc)
      simp only [hsi, false_or] at h1
      obtain h3 | h4 := h1
      · obtain h5 | h6 := h3
        · have : PD.last ∈ PD := by exact last_mem
          by_contra h
          rw[←h5] at this
          exact hsi this
        rw[h_suf2,h_suf ] at h6
        have hxx2 := mem_reverse.2 hxx
        simp only [reverse_reverse] at hxx2
        rw[h_pre] at hxx2
        have hh : x ∈ (P.suffixFromVertex b) := by exact
          (suffixFromVertex_vertex (P.suffixFromVertex b) b₁) h6
        have hxP : b ∈ P := by
          have hbC := hb
          rw[hC'] at hbC
          --simp [(hab'.ne ).symm] at hbC
          exact hbP
        exact (Prefix_Suffix_int hPath hxx2 hh hxP).symm
      rw[h4,h_pre] at hxx
      simp only [mem_reverse] at hxx
      exact False.elim (haP (((prefixUntilVertex_vertex P b ) ) hxx))
    exact h2
  obtain ⟨ef, hef ⟩:= hadjbw.symm
  set Q : WList α β := (((((PD.concat e₁ b₁) ++ P₃).concat f a).concat eab b) ++ P₀.reverse)
      with h_Q
  have hCB : G.IsCycle (cons Q.last ef Q) := by
    apply hQ₄.cons_isCycle ?_ ?_
    · have hqfirst : Q.first = wa := by
        rw[h_Q]
        simp only [WList.concat_append, concat_last, append_last, last_cons, first_cons,
          append_first_of_eq]
        exact hPD1
      have hqlast : Q.last = a₁ := by
        rw[h_Q, h_pre]
        simp only [WList.concat_append, concat_last, append_last, last_cons, reverse_last,
          prefixUntilVertex_first]
        have hget : C.get (1) = P.get (0) := by
          rw[hC']
          rw[get_cons_add]
          simp only [get_zero, concat_first]
        rw[(get_idxOf P first_mem).symm, idxOf_first P, ←hget ]
      rw[hqfirst, hqlast]
      exact hef
    rw[h_Q]
    simp only [WList.concat_append, concat_last, append_last, last_cons, append_edge, cons_edge,
      reverse_edge, List.append_assoc, List.cons_append, List.mem_append, List.mem_cons,
      List.mem_reverse, not_or]
    have hefC : ef ∉ E(C) := by
      by_contra hcef
      exact (((hDC.vertex_subset ) h2D).2) (hC.toIsTrail.isWalk.vertex_mem_of_edge_mem hcef
        (IsLink.inc_left hef ))
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    · by_contra hefc
      have hefneq : ef ∉ E(D) := by
        by_contra hc
        exact ((hef.mem_vertexDelete_iff.1) ((edgeSet_mono hDC ) hc)).2 ha₁
      exact (fun a ↦ hefneq ((hPD.isWalk).edgeSet_subset hefc)) hefc
    · by_contra hc
      rw[←hc] at he1
      obtain haw | h2 := hef.right_eq_or_eq he1
      · have ha1D : a₁ ∉ V(D) := by
          by_contra hc
          exact (((hDC.vertex_subset ) hc).2) (ha₁ )
        rw[haw] at ha1D
        exact ha1D h1D
      have ht2 : a₁ ≠ b₁ := by
        by_contra hc
        rw[ hc, ←hbindices] at haindices
        simp only [Nat.add_right_cancel_iff] at haindices
        exact hab'.ne <| idxOf_inj_of_left_mem ha haindices
      exact ht2 h2
    · by_contra hc
      have := mem_edgeSet_iff.2 hc
      have hP3C : E(P₃) ⊆ E(C) := by
        rw[h_suf2]
        have hP1C : E(P₁) ⊆ E(C) := by
          have hEPC : E(P) ⊆ E(C) := by
            rw[hC']
            simp only [cons_edgeSet, concat_edgeSet]
            exact fun g hg ↦ (mem_insert_of_mem e (mem_insert_of_mem f hg))
          have hP1s : E(P₁) ⊆ E(P) := by
            rw[h_suf]
            exact suffixFromVertex_edge P b
          exact fun ⦃a⦄ a_1 ↦ hEPC (hP1s a_1)
        have := suffixFromVertex_edge P₁ b₁
        exact fun ⦃a⦄ a_1 ↦ hP1C ((suffixFromVertex_edge P₁ b₁) a_1)
      exact hefC (hP3C hc)
    · have hfC : f ∈ E(C) := by
        rw[hC']
        simp only [cons_edgeSet, concat_edgeSet, mem_insert_iff, mem_edgeSet_iff, true_or, or_true]
      by_contra hc
      rw[←hc] at hfC
      exact hefC hfC
    · by_contra hc
      rw[← hc] at heab
      obtain haw | h2 := hef.left_eq_or_eq heab
      · have ha1D : a ∉ V(D) := by
          by_contra hc
          exact (((hDC.vertex_subset ) hc).2) (ha )
        rw[←haw] at ha1D
        exact ha1D h2D
      have ha1D : b ∉ V(D) := by
        by_contra hc
        exact (((hDC.vertex_subset ) hc).2) (hb )
      rw[←h2] at ha1D
      exact ha1D h2D
    · by_contra hc
      have hcon := mem_edgeSet_iff.2 hc
      rw[h_pre ] at hcon
      have h2 : E(P) ⊆ E(C) := by
        rw[hC']
        simp only [cons_edgeSet, concat_edgeSet]
        exact fun g hg ↦ (mem_insert_of_mem e (mem_insert_of_mem f hg))
      exact hefC (h2 (prefixUntilVertex_edge P b  hc) )
  have hlength : C.length < (cons Q.last ef Q).length := by
    rw[h_Q]
    simp only [WList.concat_append, concat_last, append_last, last_cons, reverse_last, cons_length,
      append_length, reverse_length]
    rw[h_suf2, h_pre ]
    have : PD.length + ((P₁.suffixFromVertex b₁).length + 1) +
        ((P.prefixUntilVertex b).length + 1 + 1) + 1
        = PD.length + (P₁.suffixFromVertex b₁).length  + (P.prefixUntilVertex b).length + 4 := by
      omega
    rw [this]
    have hsb : (P.suffixFromVertex b).idxOf b₁ = 1 := by
      have hb₁ := get_mem C (d + 1)
      rw[←h_b1, hC', ←hafirst] at hb₁
      have hb := get_mem C (d)
      rw[←h_b, hC', ←hafirst] at hb
      have hPb1ind := (Cycle_conc_index hab₁ hb₁ ).2
      have hPind := (Cycle_conc_index (hab'.ne).symm hb ).2
      rw[hafirst, ← hC'] at hPb1ind
      rw[hafirst, ← hC'] at hPind
      have hle : P.idxOf b ≤ P.idxOf b₁ := by omega
      have := suffixFromVertex_index hbP hle
      omega
    have : C.length + P₁.idxOf b₁ < PD.length + ((P₁.suffixFromVertex b₁).length + P₁.idxOf b₁)
        + (P.prefixUntilVertex b).length + 4 := by
      rw[sufixFromVertex_length P₁ b₁ hb1P1, h_suf,
      (add_assoc PD.length ((P.suffixFromVertex b).length) ((P.prefixUntilVertex b).length)),
      (add_comm ((P.suffixFromVertex b).length) ((P.prefixUntilVertex b).length)),
      prefixUntilVertex_suffixFromVertex_length P b hbP  ]
      rw[hC',hsb]
      simp only [cons_length, concat_length, add_lt_add_iff_right]
      omega
    omega
  sorry

lemma Hamiltonian_alpha_kappa [G.Simple] [G.Finite] (h3 : 3 ≤ V(G).encard)
    (S : Set α) (HS : IsMinSep G S )
    (A : Set α) (hA : IsMaxIndependent G A)
    (hAS : A.encard ≤ S.encard ) : ∃ C : WList α β, IsHamiltonCycle G C := by
--grw
  -- To find a longest cycle, we first need to show the existence of some cycle C'
  have ⟨C', hC'⟩ : ∃ C, G.IsCycle C :=
    Hamiltonian_alpha_kappa_exists_cycle h3 HS hA hAS
  -- have := Finite.exists_maximalFor

  have hsne : {C : WList α β | G.IsCycle C}.Nonempty := nonempty_of_mem hC'
  have hsfin : ((length ) '' {C : WList α β | G.IsCycle C}).Finite := by sorry
  --The following obtains a cycle of G that is maximal in length

  obtain ⟨C, hCs : MaximalFor G.IsCycle length C⟩ := hsfin.exists_maximalFor' _ _ hsne

  --Now that we got a max cycle, we have two cases

  obtain h_eq | hssu := hCs.prop.vertexSet_subset.eq_or_ssubset
  · use C
    refine ⟨ hCs.prop, Eq.subset (id (Eq.symm h_eq)) ⟩
  have hG : V(G - V(C)).Nonempty := by
    rw [vertexDelete_vertexSet, diff_nonempty]
    exact hssu.not_subset
  -- `C` is a Hamilton cycle
  --There should be an obvious bound on the size of a cycle
  have hC : G.IsCycle C := (hCs.prop)
  -- have hCle : V(C).encard < V(G).encard := by
  --   have hVCG : V(C) ⊆ V(G) := by sorry
  --   refine Finite.encard_lt_encard ?_ ?_
  --   --have := hlen (congrArg encard a)
  --     --simp [hlen]
  --   exact WList.vertexSet_finite C
  --   exact HasSubset.Subset.ssubset_of_ne hVCG fun a ↦ hlen (congrArg encard a)
--VC = V(C)
  --have ⟨v, hvV ⟩ : ∃ v, v ∉ C.vertex := sorry

    --obtain ⟨v, hv ⟩ := hc
    -- have hg : V(G) \ VC = ∅ := by sorry
    -- have hg1 : VC ⊆ V(G) := by sorry
    -- have hconcl : V(G) ⊆ VC  := by exact diff_eq_empty.mp hg
    -- have hconclusion : V(G) = VC  := by exact Subset.antisymm hconcl hg1
  have ⟨D, hD⟩ := exists_IsCompOf hG
  --{i ≤ C.length | G.SetVxAdj V(D) (C.get i)}


  --set nbrIndices := {i | i < C.length ∧ G.SetVxAdj V(D) (C.get i)}
  have hDC : D ≤ G - V(C) := by exact IsCompOf.le hD
  have hDconn : D.Connected := by exact IsCompOf.connected hD
  have hindep := indep_nbrsnext hCs hDC hDconn
  set nbrIndepSet :=  (C.get '' {i | i < C.length ∧ G.SetVxAdj V(D) (C.get (i + 1))})
  have ⟨d, hdD ⟩ : ∃ d, d ∈ V(D) := by
    have := hD.nonempty
    exact this
  have hI : G.IsIndependent (insert d nbrIndepSet) := by sorry
  -- Use isIndependent_insert_iff (It's in Matroid/Graph/Independent.lean)
  have hS : G.IsSep nbrIndepSet := by
    have hVn : nbrIndepSet ⊆ V(G) := by exact hindep.subset
    have hnconn : ¬ (G - nbrIndepSet).Connected := by
      by_contra hcon
      --You want to use connected_iff_forall_closed
      have hne: V(G - nbrIndepSet).Nonempty := by sorry
      have hDcG : D ≤c G - nbrIndepSet := by sorry
      have := ((connected_iff_forall_closed hne).1 hcon) hDcG (hD.nonempty )
      have ⟨x, hx ⟩ : ∃ x, x ∈ V(G - nbrIndepSet) \ V(D) := by sorry
      have : G - nbrIndepSet ≠ D := by
        sorry
      sorry
    exact { subset_vx := hVn, not_connected := hnconn }

  have hsize : nbrIndepSet.encard < (insert d nbrIndepSet).encard := by sorry
  have hcontra : S.encard < A.encard := by sorry
  by_contra hc
  grw[hAS] at hcontra
  exact (lt_self_iff_false S.encard).mp hcontra


















  -- obtain h_not | h_ind := em' <| G.IsIndependent (C.get '' nbrIndices)
  -- · rw [isIndependent_iff (by grw [← hC.vertexSet_subset, image_subset_range, range_get])] at h_not
  --   simp only [mem_image, mem_setOf_eq, ne_eq, forall_exists_index, and_imp, not_forall,
  --     exists_prop, not_not, ↓existsAndEq, true_and, exists_and_left, nbrIndices] at h_not
  --   obtain ⟨i, hi, hi', j, hj, hj', hij, hadj⟩ := h_not
  --   sorry


    -- ·
    -- wlog h : 0 ∈ nbrIndices generalizing C with aux

  -- wlog h0 : 0 ∈ nbrIndices generalizing C with aux
  -- set succIndices := (· + 1) '' nbrIndices
  -- have nbrs_independent : G.IsIndependent (C.get '' nbrIndices) := by

  --   -- wlog h0 : 0 ∈ nbrIndices with aux
  --   -- ·
  --   rw [isIndependent_iff (by grw [← hC.vertexSet_subset, image_subset_range, range_get])]
  --   simp only [mem_image, ne_eq, forall_exists_index, and_imp]
  --   rintro x y i hi rfl j hj rfl hne hij
  --   apply hne
  --   simp [nbrIndices] at *
  --   sorry
    --wlog hi0 : i = 0 generalizing C with aux



  -- set Neig : Set α := {v : α | v ∈ C ∧ (SetVxAdj G V(D) v) } with h_neig
  -- --This is the second worst sorry
  -- have hDadj : ∀ v, v ∈ Neig → ∀ u, u ∈ Neig
  --     → C.idxOf v ≠ C.idxOf u + 1 ∧ (C.idxOf v + C.length ≠ C.idxOf u + 1) := by
  --   intro v hvN u huN
  --   by_contra hcon
  --   obtain ⟨ w, hwD, hwad ⟩ := hvN.2
  --   obtain ⟨ w', huD, huad ⟩ := huN.2
  --   --Need to take path in D from w to w' and extend cycle
  --   sorry
  -- set NextNeigh : Set α := {v ∈ C | ∃ w ∈ Neig, C.idxOf v + 1 = C.idxOf w ∨
  -- (C.idxOf v = C.length - 1 ∧ C.idxOf w = 0 )} with h_NN


  -- have hNNV : NextNeigh ⊆ V(G) :=
  --   fun ⦃a⦄ b ↦ ((IsCycle.isTrail hCs.prop ).vertexSet_subset)
  --       ((sep_subset (fun x ↦ List.Mem x C.vertex)
  --       fun x ↦ ∃ w ∈ Neig, C.idxOf x + 1 = C.idxOf w ∨
  --     (C.idxOf x = C.length - 1 ∧ C.idxOf w = 0 )) b)

  --   --sep_subset V(G) fun x ↦ ∃ w ∈ Neig, C.idxOf x = C.idxOf w + 1
  -- have ⟨ v, hvD ⟩ : ∃ v, v ∈ V(D) := IsCompOf.nonempty hD

  -- have hCNT : C.Nontrivial := by sorry
  -- --Worst sorry, I will take this one
  -- have hNNI : IsIndependent G NextNeigh := by
  --   by_contra hc
  --   obtain ⟨a, ha, b, hb, hab⟩ := IsIndepndent_nee hNNV hc
  --   wlog ha0 : C.idxOf a = 0 generalizing C with aux

  --   · specialize aux (C.rotate (C.idxOf a)) ?_ ?_ (IsCycle.rotate hC (C.idxOf a))
  --       ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  --     · simp [MaximalFor]
  --       simp [MaximalFor] at hCs

  --       have : length (C.rotate (C.idxOf a)) = length C := by
  --         exact length_rotate C (C.idxOf a)
  --       sorry
  --     · rw[(hCs.prop).isClosed.rotate_vertexSet (C.idxOf a) ]
  --       exact hlen
  --     · rw [(hCs.prop).isClosed.rotate_vertexSet (C.idxOf a)]
  --       exact hCle
  --     · rw[(hCs.prop).isClosed.rotate_vertexSet (C.idxOf a) ]
  --       exact hG
  --     · rw[(hCs.prop).isClosed.rotate_vertexSet (C.idxOf a) ]
  --       exact hD
  --     · simp
  --     · simp
  --       intro v hvr hDv u hur hDu
  --       rw[ (hCs.prop).isClosed.mem_rotate ] at hur
  --       rw[ (hCs.prop).isClosed.mem_rotate ] at hvr
  --       constructor
  --       · by_contra hc
  --         have haClength : (C.idxOf a) < C.length := (hCs.prop).isClosed.idxOf_lt_length ha.1
  --           (WList.Nontrivial.nonempty hCNT)
  --         obtain hle | hlt := le_or_gt (C.idxOf a) (C.idxOf v)
  --         · have hvle := hC.idxOf_rotate_n_le hvr hle
  --           obtain hmiss | hltu := le_or_gt (C.idxOf a) (C.idxOf u)
  --           · --have hmiss : C.idxOf a ≤ C.idxOf u := by sorry
  --             have := hC.idxOf_rotate_n_le hur hmiss

  --             have hfin : C.idxOf v = C.idxOf u + 1 := by omega
  --             exact (hDadj v (mem_sep hvr hDv  ) u (mem_sep hur hDu  )).1 hfin
  --           have := hC.idxOf_rotate_n hur haClength hltu
  --           rw[hc, add_assoc, add_comm 1, ←add_assoc, this ] at hvle
  --           have : C.idxOf v < C.length + 1 := by
  --             have := idxOf_mem_le hvr
  --             omega
  --           omega
  --         · have hi := hC.idxOf_rotate_n hvr haClength hlt
  --           obtain hmiss | hltu := le_or_gt (C.idxOf a) (C.idxOf u)
  --           · have := hC.idxOf_rotate_n_le hur hmiss
  --             rw[hc, add_assoc, add_comm 1, ←add_assoc, this ] at hi
  --             have := (hDadj v (mem_sep hvr hDv  ) u (mem_sep hur hDu  )).2
  --             rw [hi, add_comm ] at this
  --             exact this rfl
  --           have hiu := hC.idxOf_rotate_n hur haClength hltu
  --           rw[hc, add_assoc, add_comm 1, ←add_assoc, hiu ] at hi
  --           exact ((hDadj v (mem_sep hvr hDv  ) u (mem_sep hur hDu  )).1)
  --             (id ((Nat.add_left_cancel (id (Eq.symm hi)))))
  --       by_contra hc
  --       have : C.length ≤ (C.rotate (C.idxOf a)).idxOf v + C.length := by
  --         exact Nat.le_add_left C.length ((C.rotate (C.idxOf a)).idxOf v)
  --       have : (C.rotate (C.idxOf a)).idxOf u < C.length := by
  --         rw [Eq.symm (length_rotate C (C.idxOf a))]
  --         have hvrr : u ∈ (C.rotate (C.idxOf a)) := by
  --           apply (hC.isClosed).mem_rotate.2 hur
  --         have hntr : (C.rotate (C.idxOf a)).Nonempty := by
  --           apply (WList.Nontrivial.nonempty hCNT).rotate
  --         exact ((hC.rotate (C.idxOf a)).isClosed).idxOf_lt_length hvrr hntr
  --       have : C.length =  (C.rotate (C.idxOf a)).idxOf v + C.length := by omega
  --       have h1u : (C.rotate (C.idxOf a)).idxOf u + (C.idxOf a) = C.length - 1 + (C.idxOf a):= by
  --         omega
  --       have h1v : (C.rotate (C.idxOf a)).idxOf v + (C.idxOf a) = (C.idxOf a) := by omega
  --       have hccc : (C.idxOf a) < C.length := (hCs.prop).isClosed.idxOf_lt_length ha.1
  --         (WList.Nontrivial.nonempty hCNT)
  --       have hf := hDadj v (mem_sep hvr hDv ) u (mem_sep hur hDu )
  --       have hn : (C.idxOf a) < C.length := (hCs.prop).isClosed.idxOf_lt_length ha.1
  --           (WList.Nontrivial.nonempty hCNT)
  --       obtain hle | hlt := le_or_gt (C.idxOf a) (C.idxOf v)
  --       · rw [ hC.idxOf_rotate_n_le hvr hle] at h1v
  --         rw[h1v ] at hf
  --         obtain hleu | hltu := le_or_gt (C.idxOf a) (C.idxOf u)
  --         · rw [ hC.idxOf_rotate_n_le hur hleu, ←h1v ] at h1u
  --           omega
  --         rw [hC.idxOf_rotate_n hur hn hltu] at h1u
  --         omega
  --       rw [hC.idxOf_rotate_n hvr hn hlt, add_comm] at h1v
  --       rw[h1v ] at hf
  --       omega
  --     · simp
  --     · exact fun v hv ↦ ((hC.isTrail.vertexSet_subset  )
  --         (((hCs.prop).isClosed.mem_rotate).1 hv.1 ))
  --     · exact (rotate_nontrivial_iff (C.idxOf a)).mpr hCNT
  --     · obtain ⟨ a₁, ha1N, haind ⟩ := ha.2
  --       obtain ⟨ b₁, hb1N, hbind ⟩ := hb.2
  --       simp
  --       by_contra hc
  --       have hnadj : ¬G.Adj a b := by
  --         apply Indep_Adje hc
  --         simp
  --         refine ⟨ (((hCs.prop).isClosed.mem_rotate).2 ha.1 ), a₁,
  --         ⟨ (((hCs.prop).isClosed.mem_rotate).2 ha1N.1 ), ha1N.2 ⟩, ?_⟩
  --         rw [hC.idxOf_rotate_idxOf ha.1 ]
  --         simp
  --         have hnt : (C.idxOf a) < C.length := (hCs.prop).isClosed.idxOf_lt_length ha.1
  --           (WList.Nontrivial.nonempty hCNT)
  --         left
  --         obtain h1 | h2 := haind
  --         · have hle : C.idxOf a ≤ C.idxOf a₁ := by
  --             omega
  --           have := hC.idxOf_rotate_n_le ha1N.1 hle
  --           omega
  --         have hle : C.idxOf a₁ < C.idxOf a := by
  --           omega
  --         have := hC.idxOf_rotate_n ha1N.1 hnt hle
  --         nth_rw 2 [h2.1] at this
  --         rw [h2.2] at this
  --         omega
  --         refine ⟨ (((hCs.prop).isClosed.mem_rotate).2 hb.1 ), b₁,
  --         ⟨ (((hCs.prop).isClosed.mem_rotate).2 hb1N.1 ), hb1N.2 ⟩, ?_⟩
  --         have hnt : (C.idxOf a) < C.length := (hCs.prop).isClosed.idxOf_lt_length ha.1
  --           (WList.Nontrivial.nonempty hCNT)
  --         have : C.idxOf b₁ = C.idxOf b + 1 ∨ C.idxOf b₁ = 0 ∧ C.idxOf b = C.length - 1 := by omega
  --         have := (hC.idxOf_Adj_rotate hb.1 hb1N.1 hnt).1 this
  --         omega
  --         exact hab.ne
  --       exact hnadj hab
  --     · simp
  --       obtain ⟨ a₁, ha1N, haind ⟩ := ha.2
  --       refine ⟨ (((hCs.prop).isClosed.mem_rotate).2 ha.1 ), a₁,
  --         ⟨ (((hCs.prop).isClosed.mem_rotate).2 ha1N.1 ), ha1N.2 ⟩, ?_⟩
  --       rw [hC.idxOf_rotate_idxOf ha.1 ]
  --       simp
  --       left
  --       obtain h1 | h2 := haind
  --       · have hle : C.idxOf a ≤ C.idxOf a₁ := by
  --             omega
  --         have := hC.idxOf_rotate_n_le ha1N.1 hle
  --         omega
  --       have hle : C.idxOf a₁ < C.idxOf a := by
  --         omega
  --       have hnt : (C.idxOf a) < C.length := (hCs.prop).isClosed.idxOf_lt_length ha.1
  --         (WList.Nontrivial.nonempty hCNT)
  --       have := hC.idxOf_rotate_n ha1N.1 hnt hle
  --       nth_rw 2 [h2.1] at this
  --       rw [h2.2] at this
  --       omega
  --     · obtain ⟨ b₁, hb1N, hbind ⟩ := hb.2
  --       refine ⟨ (((hCs.prop).isClosed.mem_rotate).2 hb.1 ), b₁,
  --       ⟨ (((hCs.prop).isClosed.mem_rotate).2 hb1N.1 ), hb1N.2 ⟩, ?_⟩
  --       have hnt : (C.idxOf a) < C.length := (hCs.prop).isClosed.idxOf_lt_length ha.1
  --         (WList.Nontrivial.nonempty hCNT)
  --       simp
  --       have : C.idxOf b₁ = C.idxOf b + 1 ∨ C.idxOf b₁ = 0 ∧ C.idxOf b = C.length - 1 := by omega
  --       have := (hC.idxOf_Adj_rotate hb.1 hb1N.1 hnt).1 this
  --       omega
  --     · have := hC.idxOf_rotate_n_le ha.1 (Nat.le_refl (C.idxOf a) )
  --       omega
  --     exact aux
  --   --We can now assume nice things
  --   -- prove the theorem with an added assumption

  --   obtain ⟨ b₁, hb1N, hbind ⟩ := hb.2
  --   obtain ⟨ a₁, ha1N, haind ⟩ := ha.2
  --   obtain ⟨P,e,f, hPath, haP, heP, hfP, hef, hC'⟩ :=
  --       IsCycle.exists_isPath_vertex hCs.prop hCNT ha.1
  --   have hbP : b ∈ P := by
  --     have hhh : b ∈ C.rotate (C.idxOf a)  := by
  --       refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb.1
  --     rw [hC'] at hhh
  --     exact (Cycle_conc_index (hab.ne).symm hhh).1
  --   have hab₁ : b₁ ≠ a := by
  --     by_contra hcc
  --     rw[←hcc] at haind
  --     have hcon := hDadj a₁ ha1N b₁ hb1N
  --     have : ¬ (C.idxOf a₁ ≠ C.idxOf b₁ + 1 ∧ C.idxOf a₁ + C.length ≠ C.idxOf b₁ + 1) := by
  --       simp
  --       intro h
  --       obtain htrue | hfalse := haind
  --       · exact False.elim (h (id (Eq.symm htrue)))
  --       rw[hfalse.2]
  --       simp
  --       rw[hfalse.1]
  --       refine (Nat.sub_eq_iff_eq_add (one_le_length_iff.mpr
  --         (WList.Nontrivial.nonempty hCNT))).mp rfl
  --     exact this (hDadj a₁ ha1N b₁ hb1N)
  --   --obtain ⟨P₀,P₁,hP₁,hP₂,hP₀last,hP₀first,hP01d,hP01 ⟩ := IsPath.exists_isPath_vertex P hPath hbP
  --   set P₀ : WList α β := prefixUntilVertex P b with h_pre
  --   set P₁ : WList α β := suffixFromVertex P b with h_suf
  --   have hP₀ := IsPath.prefix hPath (prefixUntilVertex_isPrefix P b)
  --   have hP₁ := IsPath.suffix hPath (suffixFromVertex_isSuffix P b)
  --   rw [←h_pre] at hP₀
  --   rw [←h_suf] at hP₁
  --   have hb1P' : b₁ ∈ P := by
  --       have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
  --         refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
  --       rw [hC'] at hhh
  --       exact (Cycle_conc_index hab₁ hhh).1
  --   have hb1P1 : b₁ ∈ P₁ := by
  --     have hb1P : b₁ ∈ P := by
  --       have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
  --         refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
  --       rw [hC'] at hhh
  --       exact (Cycle_conc_index hab₁ hhh).1
  --     rw [Eq.symm (prefixUntilVertex_append_suffixFromVertex P b),←h_pre, ←h_suf] at hb1P
  --     obtain (hf | hg ):= mem_of_mem_append hb1P
  --     · rw [h_pre] at hf
  --       have hcon := (prefixUntilVertex_index_iff P b hbP hb1P').1 hf
  --       have hbindP : P.idxOf b + 1 = P.idxOf b₁ := by
  --         have hhh : b ∈ C.rotate (C.idxOf a)  := by
  --           refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb.1
  --         rw[hC'] at hhh
  --         have hg1 := (Cycle_conc_index (hab.ne).symm hhh).2
  --         have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
  --           refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
  --         rw[hC'] at hhh
  --         have hg2 := (Cycle_conc_index (hab₁) hhh).2
  --         rw [←hC', ha0, rotate_zero] at hg1
  --         rw [←hC', ha0, rotate_zero] at hg2
  --         rw[ha0, rotate_zero ] at hC'
  --         omega
  --       rw [←hbindP ] at hcon
  --       linarith
  --     exact hg
  --   rw[ha0, rotate_zero ] at hC'
  --   set P₂ : WList α β := prefixUntilVertex P₁ b₁ with h_pre2
  --   set P₃ : WList α β := suffixFromVertex P₁ b₁ with h_suf2
  --   have hP₂ := IsPath.prefix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
  --       (prefixUntilVertex_isPrefix P₁ b₁)
  --   have hP₃ := IsPath.suffix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
  --       (suffixFromVertex_isSuffix P₁ b₁)
  --   rw [←h_pre2] at hP₂
  --   rw [←h_suf2] at hP₃
  --   rw[h_neig] at hb1N
  --   rw[h_neig] at ha1N
  --   obtain ⟨ wb, hwb, hwb2 ⟩ := hb1N.2
  --   obtain ⟨ wa, hwa, hwa2 ⟩ := ha1N.2
  --   obtain ⟨PD, hPD, hPD1,hPD2 ⟩ := hD.exist_pathh hwa hwb
  --   obtain ⟨e₁, he1 ⟩ := hwb2.symm
  --   have hPc1 : G.IsPath (PD.concat e₁ b₁) := by
  --     apply concat_isPath_iff.2
  --     refine ⟨hPD.of_le (Std.IsPreorder.le_trans D (G - V(C)) G hD.le vertexDelete_le), ?_, ?_ ⟩
  --     · rw[←hPD2] at he1
  --       exact he1
  --     have : b₁ ∉ V(D) := by
  --       by_contra hc
  --       exact (((hD.subset ) hc).2) (hb1N.1 )
  --     exact fun b ↦ this ((IsPath.vertexSet_subset hPD ) b)
  --   have hAdb : Adj G b b₁ := by
  --     have : G.IsTrail C := by exact hC.toIsTrail
  --     obtain hgood | hannoying := hbind
  --     · exact idxOf_Adj (hC.toIsTrail ) hb.1 hb1N.1 hgood.symm
  --     have hbb1 : b ≠ b₁ := by
  --       by_contra hc
  --       rw[←hc] at hannoying
  --       rw[hannoying.2] at hannoying
  --       simp at hannoying
  --       have : C.length > 1 := by exact Nontrivial.one_lt_length hCNT
  --       omega
  --     exact (hC.idxOf_Adj_first hbb1.symm hannoying.2 hannoying.1).symm
  --   obtain ⟨e₂, he2 ⟩ := hAdb.symm
  --   have hPlast : (PD.concat e₁ b₁).last = b₁ := by simp
  --   have hPfirst : P₃.first = b₁ := by
  --     exact suffixFromVertex_first hb1P1
  --   have hQ₁ : G.IsPath ((PD.concat e₁ b₁) ++ P₃) := by
  --     apply hPc1.append hP₃ ?_ ?_
  --     · rw[hPlast, hPfirst]
  --     intro x hx hx3
  --     simp
  --     simp at hx
  --     obtain hfalse | hgood := hx
  --     · by_contra h
  --       have hP3C : V(P₃) ⊆ V(C) := by
  --         have : V(P) ⊆ V(C) := by
  --           rw[hC']
  --           simp
  --         rw[h_suf2, h_suf]
  --         have h1 : V((P.suffixFromVertex b).suffixFromVertex b₁) ⊆ V(P) := by
  --           exact fun ⦃a⦄ a_1 ↦ (suffixFromVertex_vertex P b  )
  --             ((suffixFromVertex_vertex (P.suffixFromVertex b) b₁) a_1)
  --         exact fun ⦃a⦄ a_1 ↦ this (h1 a_1)
  --       have : x ∉ V(C) := by
  --         have hob : V(D) ⊆ V(G) \ V(C) := by
  --           have := (hD.subset )
  --           simp at this
  --           exact this
  --         have : x ∈ V(G) \ V(C) := by exact hob (IsPath.vertexSet_subset hPD hfalse)
  --         simp at this
  --         exact this.2
  --       exact this (hP3C hx3)
  --     exact hgood
  --   have hQ₂ : G.IsPath (((PD.concat e₁ b₁) ++ P₃).concat f a) := by
  --     apply concat_isPath_iff.2
  --     refine ⟨ hQ₁, ?_, ?_ ⟩
  --     · simp
  --       have h3last : P₃.last = P.last := by
  --         rw [h_suf2]
  --         simp
  --         rw[h_suf]
  --         simp
  --       rw[h3last]
  --       have hpcon : G.IsPath (P.concat f a) := by
  --         rw[hC'] at hC
  --         have := hC.tail_isPath
  --         rwa[tail_cons] at this
  --       exact (concat_isPath_iff.1 hpcon).2.1
  --     simp
  --     have ha1D : a ∉ V(D) := by
  --           by_contra hc
  --           exact (((hD.subset ) hc).2) (ha.1 )
  --     --have : V(PD) ⊆ V(D) := by exact IsPath.vertexSet_subset hPD
  --     refine ⟨ ?_, ?_, ?_ ⟩
  --     · by_contra hc
  --       exact ha1D ((IsPath.vertexSet_subset hPD) hc)
  --     · by_contra hc
  --       have hcc : PD.last ∈ V(PD) := by exact last_mem
  --       rw[←hc] at hcc
  --       exact ha1D ((IsPath.vertexSet_subset hPD) hcc)
  --     rw[h_suf2, h_suf]
  --     have h1 : V((P.suffixFromVertex b).suffixFromVertex b₁) ⊆ V(P) := by
  --           exact fun ⦃a⦄ a_1 ↦ (suffixFromVertex_vertex P b  )
  --             ((suffixFromVertex_vertex (P.suffixFromVertex b) b₁) a_1)
  --     by_contra hc
  --     exact haP (h1 hc)
  --   have hab' := hab
  --   obtain ⟨eab, heab ⟩ := hab
  --   have hQ₃ : G.IsPath ((((PD.concat e₁ b₁) ++ P₃).concat f a).concat eab b) := by
  --     apply concat_isPath_iff.2
  --     refine ⟨hQ₂, ?_, ?_ ⟩
  --     · have : ((PD.concat e₁ b₁ ++ P₃).concat f a).last = a := by simp
  --       rwa[this]
  --     simp
  --     have hb1D : b ∉ V(D) := by
  --           by_contra hc
  --           exact (((hD.subset ) hc).2) (hb.1 )
  --     refine ⟨ ⟨?_, ?_, ?_⟩, (ne_of_mem_of_not_mem hbP haP ) ⟩
  --     · by_contra hc
  --       exact hb1D ((IsPath.vertexSet_subset hPD) hc)
  --     · by_contra hc
  --       have hcc : PD.last ∈ V(PD) := by exact last_mem
  --       rw[←hc] at hcc
  --       exact hb1D ((IsPath.vertexSet_subset hPD) hcc)
  --     · rw[h_suf2 ]
  --       have hbPre : b ∈ P₁.prefixUntilVertex b₁ := by
  --         rw[h_suf ]
  --         have : b = ((P.suffixFromVertex b).prefixUntilVertex b₁).first := by
  --           simp
  --           exact Eq.symm (suffixFromVertex_first hbP)
  --         rw [this]
  --         nth_rw 1 [←this]
  --         exact first_mem
  --       by_contra hc
  --       exact (hAdb.ne.symm) (Prefix_Sufix_int hP₁ hbPre hc hb1P1 )
  --   have hQ₄ : G.IsPath (((((PD.concat e₁ b₁) ++ P₃).concat f a).concat eab b) ++ P₀.reverse) := by
  --     apply hQ₃.append (reverse_isPath_iff.mpr hP₀ ) ?_ ?_
  --     · simp
  --       rw[h_pre]
  --       exact Eq.symm (prefixUntilVertex_last hbP)
  --     intro x hx hxx
  --     simp
  --     simp at hx
  --     obtain h1 | h2 := hx
  --     · have hsi : x ∉ PD := by
  --         by_contra hc
  --         have hxC : x ∈ V(C) := by
  --           rw[hC']
  --           rw[h_pre] at hxx
  --           simp at hxx
  --           simp
  --           right
  --           exact ((prefixUntilVertex_vertex P b ) hxx )
  --         have hxD : x ∉ V(D) := by
  --           by_contra hcc
  --           exact (((hD.subset ) hcc).2) (hxC )
  --         exact hxD ((IsPath.vertexSet_subset hPD) hc)
  --       simp [hsi] at h1
  --       obtain h3 | h4 := h1
  --       · obtain h5 | h6 := h3
  --         · have : PD.last ∈ PD := by exact last_mem
  --           by_contra h
  --           rw[←h5] at this
  --           exact hsi this
  --         rw[h_suf2,h_suf ] at h6
  --         have hxx2 := mem_reverse.2 hxx
  --         simp at hxx2
  --         rw[h_pre] at hxx2
  --         have hh : x ∈ (P.suffixFromVertex b) := by exact
  --           (suffixFromVertex_vertex (P.suffixFromVertex b) b₁) h6
  --         have hxP : b ∈ P := by
  --           have hbC := hb.1
  --           rw[hC'] at hbC
  --           simp [(hab'.ne ).symm] at hbC
  --           exact hbP
  --         exact (Prefix_Sufix_int hPath hxx2 hh hxP).symm
  --       rw[h4,h_pre] at hxx
  --       simp at hxx
  --       exact False.elim (haP (((prefixUntilVertex_vertex P b ) ) hxx))
  --     exact h2
  --   obtain ⟨ef, hef ⟩:= hwa2.symm
  --   set Q : WList α β := (((((PD.concat e₁ b₁) ++ P₃).concat f a).concat eab b) ++ P₀.reverse)
  --       with h_Q
  --   have hCB : G.IsCycle (cons Q.last ef Q) := by
  --     apply hQ₄.cons_isCycle ?_ ?_
  --     · have hqfirst : Q.first = wa := by
  --         rw[h_Q]
  --         simp
  --         exact hPD1
  --       have hqlast : Q.last = a₁ := by
  --         rw[h_Q, h_pre]
  --         simp
  --         have hget : C.get (1) = P.get (0) := by
  --           rw[hC']
  --           rw[get_cons_add]
  --           simp
  --         rw[(get_idxOf P first_mem).symm, idxOf_first P, ←hget ]

  --         have : C.idxOf a₁ = 1 := by
  --           obtain hgood | hfalse := haind
  --           · rw[← hgood]
  --             simp
  --             exact ha0
  --           by_contra
  --           rw[ha0] at hfalse
  --           have hcc : C.length -1 ≠ 0 := by
  --             refine Nat.sub_ne_zero_iff_lt.mpr (Nontrivial.one_lt_length hCNT )
  --           exact hcc (hfalse.1).symm
  --         rw[←this]
  --         exact get_idxOf C ha1N.1
  --       rw[hqfirst, hqlast]
  --       exact hef
  --     rw[h_Q]
  --     simp
  --     have hefC : ef ∉ E(C) := by
  --       by_contra hcef
  --       exact ((isCompOf_subset hD ) hwa ).2 (hC.toIsTrail.isWalk.vertex_mem_of_edge_mem hcef
  --           (IsLink.inc_left hef ))
  --     refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
  --     · by_contra hefc
  --       have hefneq : ef ∉ E(D) := by
  --         by_contra hc
  --         exact (hef.mem_vertexDelete_iff.1 ((hD.isClosedSubgraph.edgeSet_mono) hc)).2 ha1N.1
  --       exact (fun a ↦ hefneq ((hPD.isWalk).edgeSet_subset hefc)) hefc
  --     · by_contra hc
  --       rw[←hc] at he1
  --       obtain haw | h2 := hef.right_eq_or_eq he1
  --       · have ha1D : a₁ ∉ V(D) := by
  --           by_contra hc
  --           exact (((hD.subset ) hc).2) (ha1N.1 )
  --         rw[haw] at ha1D
  --         exact ha1D hwb
  --       have ht2 : a₁ ≠ b₁ := by
  --         have hleght0 : ¬  (0 = C.length - 1 ∧ C.idxOf b₁ = 0) := by
  --           simp
  --           intro h
  --           by_contra
  --           exact (Nat.sub_ne_zero_iff_lt.mpr (Nontrivial.one_lt_length hCNT )) (id (Eq.symm h))
  --         by_contra hc
  --         rw[ha0, hc] at haind
  --         simp at haind
  --         simp [hleght0] at haind
  --         obtain hc1 | hc2 := hbind
  --         · have habeq : a = b := by
  --             rw[←haind] at hc1
  --             simp at hc1
  --             rw[←ha0] at hc1
  --             exact idxOf_eq C ha.1 hc1.symm
  --           have := (hab'.ne)
  --           exact (hab'.ne) habeq
  --         rw[←hc,←ha0] at hc2
  --         rw[←hc, (idxOf_eq C ha1N.1 hc2.2), ha0 ] at haind
  --         omega
  --       exact ht2 h2
  --     · by_contra hc
  --       have := mem_edgeSet_iff.2 hc
  --       have hP3C : E(P₃) ⊆ E(C) := by
  --         rw[h_suf2]
  --         have hP1C : E(P₁) ⊆ E(C) := by
  --           have hEPC : E(P) ⊆ E(C) := by
  --             rw[hC']
  --             simp
  --             exact fun g hg ↦ (mem_insert_of_mem e (mem_insert_of_mem f hg))
  --           have hP1s : E(P₁) ⊆ E(P) := by
  --             rw[h_suf]
  --             exact suffixFromVertex_edge P b
  --           exact fun ⦃a⦄ a_1 ↦ hEPC (hP1s a_1)
  --         have := suffixFromVertex_edge P₁ b₁
  --         exact fun ⦃a⦄ a_1 ↦ hP1C ((suffixFromVertex_edge P₁ b₁) a_1)
  --       exact hefC (hP3C hc)
  --     · have hfC : f ∈ E(C) := by
  --         rw[hC']
  --         simp
  --       by_contra hc
  --       rw[←hc] at hfC
  --       exact hefC hfC
  --     · by_contra hc
  --       rw[← hc] at heab
  --       obtain haw | h2 := hef.left_eq_or_eq heab
  --       · have ha1D : a ∉ V(D) := by
  --           by_contra hc
  --           exact (((hD.subset ) hc).2) (ha.1 )
  --         rw[←haw] at ha1D
  --         exact ha1D hwa
  --       have ha1D : b ∉ V(D) := by
  --         by_contra hc
  --         exact (((hD.subset ) hc).2) (hb.1 )
  --       rw[←h2] at ha1D
  --       exact ha1D hwa
  --     · by_contra hc
  --       have hcon := mem_edgeSet_iff.2 hc
  --       rw[h_pre ] at hcon
  --       have h2 : E(P) ⊆ E(C) := by
  --         rw[hC']
  --         simp
  --         exact fun g hg ↦ (mem_insert_of_mem e (mem_insert_of_mem f hg))
  --       exact hefC (h2 (prefixUntilVertex_edge P b  hc) )
  --   have hlength : C.length < (cons Q.last ef Q).length := by
  --     rw[h_Q]
  --     simp
  --     rw[h_suf2, h_pre ]
  --     have : PD.length + ((P₁.suffixFromVertex b₁).length + 1) +
  --         ((P.prefixUntilVertex b).length + 1 + 1) + 1
  --         = PD.length + (P₁.suffixFromVertex b₁).length  + (P.prefixUntilVertex b).length + 4 := by
  --       omega
  --     rw [this]
  --     have hsb : (P.suffixFromVertex b).idxOf b₁ = 1 := by sorry
  --     have : C.length + P₁.idxOf b₁ < PD.length + ((P₁.suffixFromVertex b₁).length + P₁.idxOf b₁)
  --         + (P.prefixUntilVertex b).length + 4 := by
  --       rw[sufixFromVertex_length P₁ b₁ hb1P1, h_suf,
  --       (add_assoc PD.length ((P.suffixFromVertex b).length) ((P.prefixUntilVertex b).length)),
  --       (add_comm ((P.suffixFromVertex b).length) ((P.prefixUntilVertex b).length)),
  --       prefixUntilVertex_suffixFromVertex_length P b hbP  ]
  --       rw[hC',hsb]
  --       simp
  --       omega
  --     omega
  --   sorry


  -- have hNNIv : IsIndependent G ( insert v NextNeigh) := by
  --   --Should not be too bad doing cases
  --   sorry
  -- --Finish
  -- sorry








/- Step 1: WTS G is connected.
Proof: Suppose not. Then the degree of any vertex in the smallest component C of G
would be less than |C| ≤ n/2.
-/

omit [DecidableEq α] in
lemma dirac_connected [G.Simple] [hFinite : G.Finite] (hV : 3 ≤ V(G).encard)
    (hDegree : V(G).encard ≤ 2 * G.minEDegree) : G.Connected := by
  have encard_eq_ncard : V(G).encard = ↑V(G).ncard := by
    rw [Set.Finite.cast_ncard_eq]
    exact vertexSet_finite
  have hNeBot : V(G).Nonempty := by
    rw [← Set.encard_pos]
    enat_to_nat! <;> omega
  simp only [← G.natCast_minDegree_eq hNeBot] at hDegree
  rw [encard_eq_ncard] at hV hDegree
  enat_to_nat

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
      G.Components finite_components_of_finite
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
    enat_to_nat; omega

  -- G, min_comp, other_comp have finite vertexSets
  have G_finite_vertexSet : V(G).Finite := vertexSet_finite
  have min_comp_finite : min_comp.Finite := hFinite.mono min_comp_spec.1.le
  have min_comp_finite_vertexSet : V(min_comp).Finite := vertexSet_finite
  have other_comp_finite : other_comp.Finite := hFinite.mono other_comp_spec.1.le
  have other_comp_finite_vertexSet : V(other_comp).Finite := vertexSet_finite

  -- other_comp has at least as many vertices as min_comp
  have other_comp_larger : V(min_comp).ncard ≤ V(other_comp).ncard := by
    refine minimalFor_is_lower_bound (fun H : Graph α β => H.vertexSet.ncard) min_comp_spec ?_ ?_
    rw [mem_components_iff_isCompOf]
    exact other_comp_spec.1
  -- min_comp and other_comp have disjoint vertex sets
  have disjoint_vx_sets : Disjoint V(min_comp) V(other_comp) := by
    suffices StronglyDisjoint min_comp other_comp by exact this.vertex
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
    have : V(min_comp).ncard + V(other_comp).ncard = (V(min_comp) ∪ V(other_comp)).ncard :=
      (ncard_union_eq disjoint_vx_sets min_comp_finite_vertexSet other_comp_finite_vertexSet).symm
    rw [this]; clear this
    refine ncard_le_ncard ?_ ?_ <;> assumption

  -- so |min_comp| ≤ n/2
  replace G_ncard_ge_sum : 2 * V(min_comp).ncard ≤ V(G).ncard := by
    linarith

  -- some manipulations left over
  have hle : V(min_comp).ncard ≤ G.minDegree := by linarith
  have hle2 : G.minDegree ≤ min_comp.minDegree := by
    apply IsCompOf.minDegree_le_minDegree
    rw [←mem_components_iff_isCompOf]
    exact min_comp_spec.1
  replace hle : V(min_comp).ncard ≤ min_comp.minDegree := by linarith
  have hlt : min_comp.minDegree < V(min_comp).ncard := by
    have min_comp_simple : min_comp.Simple := ‹G.Simple›.mono min_comp_spec.1.le
    exact minDegree_lt_ncard min_comp_spec.1.nonempty

  linarith

omit [DecidableEq α]


/- gist of the proof of the next part:
Goal: there's a cycle which contains the vertices of the longest path (which we will call P)
Proof:
- first, note that each neighbour of P.first must be on P by maximality of P
- symmetrically, each neighbour of P.last must be on P as well
- each neighbour of P.first has an edge of P to its left,
  each neighbour of P.last has an edge of P to its right
- since min degree >= n/2, there are n/2 edges of P with a neighbour of
  of P.first on its right and n/2 edges of P with a neighbour of P.last on its left
- P can only have at most n - 1 edges, so by pigeonhole, there must be at least
  one edge of P with a neighbour of P.last on its left and a neighbour of P.first on
  its right, say x - e - y with (G.Adj P.first x), (G.Adj P.last y)
- so if we let:
  * u := P.first
  * v := P.last
  * P₁ be the prefix u ... x,
  * P₂ be the suffix y ... v,
  then P₁ + xv - P₂ + yu is a cycle containing all of V(P)
-/

lemma existsUnique_left_edge (hw : G.IsPath w) (hyw : y ∈ w) (hy : y ≠ w.first) :
    ∃! e, ∃ x, w.DInc e x y := by
  obtain ⟨e, x, h⟩ := exists_left_edge hyw hy
  refine ⟨e, ⟨x, h⟩, ?_⟩
  simp only [forall_exists_index]
  intro e' x' h'
  simp only [dInc_iff_eq_of_dInc_of_vertex_nodup_right hw.nodup h] at h'
  tauto

lemma existsUnique_right_edge (hw : G.IsPath w) (hxw : x ∈ w) (hx : x ≠ w.last) :
    ∃! e, ∃ y, w.DInc e x y := by
  generalize hw'_def : w.reverse = w'
  symm at hw'_def
  have hw' : G.IsPath w' := by simp_all
  have hx' : x ≠ w'.first := by simp_all
  have hxw' : x ∈ w' := by simp_all
  obtain ⟨e, he⟩ := existsUnique_left_edge hw' hxw' hx'
  simp_all only [ne_eq, reverse_isPath_iff, reverse_first, not_false_eq_true, mem_reverse,
    dInc_reverse_iff, forall_exists_index]
  refine ⟨e, he.1, ?_⟩
  simp only [forall_exists_index]
  exact he.2

lemma IsLongestPath.nontrivial_of_connected_of_encard_ge_three (hP : G.IsLongestPath P)
    (hConn : G.Connected) (hNontrivial : 3 ≤ V(G).encard) : P.Nontrivial := by
  -- we will just leverage our result on trees
  obtain ⟨T, hT, hles⟩ := hConn.exists_isTree_spanningSubgraph
  have hT_encard : 3 ≤ V(T).encard := by simpa [hles.vertexSet_eq]
  have ⟨Q, hQ, hQ_length⟩ := hT.exists_length_two_path hT_encard
  replace hQ : G.IsPath Q := hQ.of_le hles.le
  rw [← WList.two_le_length_iff]
  have solver := maximalFor_is_upper_bound WList.length hP _ hQ
  omega

lemma dirac_exists_cycle [G.Simple] [G.Finite] (hNontrivial : 3 ≤ V(G).encard)
    (hDegree : V(G).encard ≤ 2 * G.minEDegree) (hP : G.IsLongestPath P) :
    ∃ C, G.IsCycle C ∧ V(C) = V(P) := by
  classical
  -- every max-length path in G must be of length at least 2
  have P_nontrivial : P.Nontrivial :=
    hP.nontrivial_of_connected_of_encard_ge_three (dirac_connected hNontrivial hDegree) hNontrivial

  -- enat_to_nat away encard → ncard
  have G_nonempty : V(G).Nonempty := by
    rw [←encard_ne_zero]
    enat_to_nat! <;> omega
  have vx_finite : V(G).Finite := vertexSet_finite
  simp only [← vx_finite.cast_ncard_eq, Nat.ofNat_le_cast] at hDegree hNontrivial
  simp only [← G.natCast_minDegree_eq G_nonempty] at hDegree
  enat_to_nat

  have first_edge (y : N(G, P.first)) : ∃! e, ∃ x, P.DInc e x y := by
    obtain ⟨y, hy⟩ := y
    have ne_first : y ≠ P.first := hy.ne.symm
    refine existsUnique_left_edge hP.isPath ?_ ne_first
    exact G.first_neighbors_mem_path hP hy
  have last_edge (x : N(G, P.last)) : ∃! e, ∃ y, P.DInc e x y := by
    obtain ⟨x, hx⟩ := x
    have ne_last : x ≠ P.last := hx.ne.symm
    refine existsUnique_right_edge hP.isPath ?_ ne_last
    exact G.last_neighbors_mem_path hP hx
  rw [forall_existsUnique_iff] at first_edge last_edge
  obtain ⟨left_edge, left_edge_spec⟩ := first_edge
  obtain ⟨right_edge, right_edge_spec⟩ := last_edge
  have left_edge_inj : Function.Injective left_edge := by
    intro ⟨y, hy⟩ ⟨y', hy'⟩ heq
    simp only [Subtype.mk.injEq]
    generalize e_def : left_edge ⟨y, hy⟩ = e
    generalize e'_def : left_edge ⟨y', hy'⟩ = e'
    obtain rfl : e = e' := (e_def.symm.trans heq).trans e'_def
    rw [←left_edge_spec] at e_def e'_def
    obtain ⟨x, hx⟩ := e_def
    obtain ⟨x', hx'⟩ := e'_def
    rw [hP.isPath.isTrail.dInc_iff_eq_of_dInc hx (x := x') (y := y')] at hx'
    tauto
  have right_edge_inj : Function.Injective right_edge := by
    intro ⟨x, hx⟩ ⟨x', hx'⟩ heq
    simp only [Subtype.mk.injEq]
    generalize e_def : right_edge ⟨x, hx⟩ = e
    generalize e'_def : right_edge ⟨x', hx'⟩ = e'
    obtain rfl : e = e' := (e_def.symm.trans heq).trans e'_def
    rw [←right_edge_spec] at e_def e'_def
    obtain ⟨y, hy⟩ := e_def
    obtain ⟨y', hy'⟩ := e'_def
    rw [hP.isPath.isTrail.dInc_iff_eq_of_dInc hy (x := x') (y := y')] at hy'
    tauto
  have left_edge_range_le : Set.range left_edge ⊆ E(P) := by
    intro e ⟨y, hy⟩
    rw [←left_edge_spec] at hy
    obtain ⟨x, h⟩ := hy
    exact h.edge_mem
  have right_edge_range_le : Set.range right_edge ⊆ E(P) := by
    intro e ⟨x, hx⟩
    rw [←right_edge_spec] at hx
    obtain ⟨y, h⟩ := hx
    exact h.edge_mem
  let equiv_first := G.incAdjEquiv P.first
  let equiv_last := G.incAdjEquiv P.last

  -- there exists some edge which is both a left edge and a right edge
  have ⟨e, he⟩ : (range left_edge ∩ range right_edge).Nonempty := by
    rw [←not_disjoint_iff_nonempty_inter]
    intro h_disj
    have P_edge_finite : E(P).Finite :=
      G.edgeSet_finite.subset <| hP.isPath.isWalk.edgeSet_subset
    have left_edge_range_finite : (range left_edge).Finite :=
      P_edge_finite.subset left_edge_range_le
    have right_edge_range_finite : (range right_edge).Finite :=
      P_edge_finite.subset right_edge_range_le
    have left_edge_range_card : (range left_edge).ncard = G.degree P.first := by
      rw [←Nat.card_coe_set_eq, Nat.card_range_of_injective, Nat.card_congr equiv_first.symm]
        <;> [skip ; assumption]
      change Nat.card {e | G.Inc e P.first} = G.degree P.first
      rw [Nat.card_coe_set_eq]
      exact degree_eq_ncard_inc.symm
    have right_edge_range_card : (range right_edge).ncard = G.degree P.last := by
      rw [←Nat.card_coe_set_eq, Nat.card_range_of_injective, Nat.card_congr equiv_last.symm]
        <;> [skip ; assumption]
      change Nat.card {e | G.Inc e P.last} = G.degree P.last
      rw [Nat.card_coe_set_eq]
      exact degree_eq_ncard_inc.symm
    have sum :
        ((range left_edge) ∪ (range right_edge)).ncard = G.degree P.first + G.degree P.last := by
      rw [ncard_union_eq h_disj left_edge_range_finite right_edge_range_finite,
        left_edge_range_card, right_edge_range_card]
    replace sum : V(G).ncard ≤ (range left_edge ∪ range right_edge).ncard := by
      have le₁ : G.minDegree ≤ G.degree P.first :=
        minDegree_le_degree hP.isPath.isWalk.first_mem
      have le₂ : G.minDegree ≤ G.degree P.last :=
        minDegree_le_degree hP.isPath.isWalk.last_mem
      omega
    have killer₁ : E(P).ncard + 1 ≤ V(G).ncard := by
      rw [hP.isPath.isTrail.edge_ncard_eq_length]
      exact hP.isPath.length_le_ncard
    have killer₂ : (range left_edge ∪ range right_edge).ncard ≤ E(P).ncard := by
      refine ncard_le_ncard ?_ P_edge_finite
      simp
      tauto
    omega

  obtain ⟨⟨y, he_left⟩, ⟨x, he_right⟩⟩ := he
  have h_dinc : P.DInc e x y := by
    rw [←left_edge_spec] at he_left
    rw [←right_edge_spec] at he_right
    obtain ⟨x', hx'⟩ := he_left
    obtain ⟨y', hy'⟩ := he_right
    rw [hP.isPath.isTrail.dInc_iff_eq_of_dInc hy' (x := x') (y := y)] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    assumption
  obtain ⟨y, ey, hy⟩ := y
  obtain ⟨x, ex, hx⟩ := x
  simp only at h_dinc
  clear left_edge_spec left_edge_inj left_edge_range_le he_left left_edge
  clear right_edge_spec right_edge_inj right_edge_range_le he_right right_edge
  clear equiv_first equiv_last

  -- Two trivial cases: when ex ∈ P.edge or when ey ∈ P.edge.
  -- In either case, we can directly close the path up.
  obtain (hey|ey_notMem) := Classical.em (ey ∈ P.edge)
  · -- In this case, we must have P.DInc ey P.first y.
    -- But we already know P.DInc e x y, so we must have x = P.first.
    -- Thus, we can directly close up the loop with ex.
    have h_dinc' : P.DInc ey P.first y := by
      have h_isLink' : P.IsLink ey P.first y := by
        simpa [hP.isPath.isWalk.isLink_iff_isLink_of_mem hey]
      rw [isLink_iff_dInc] at h_isLink'
      obtain (h|h) := h_isLink' <;> [assumption; exfalso]
      -- this is impossible, can't have P.first as RHS of DInc.
      have := h.ne_first hP.isPath.nodup
      contradiction
    rw [dInc_iff_eq_of_dInc_of_vertex_nodup_right hP.isPath.nodup h_dinc (f := ey) (x := P.first)]
      at h_dinc'
    obtain ⟨rfl, rfl⟩ := h_dinc'
    have hC : G.IsCycle (cons P.last ex P) :=
      hP.isPath.cons_isCycle_of_nontrivial hx.symm P_nontrivial
    refine ⟨cons P.last ex P, hC, ?_⟩
    simp [←hC.isClosed.vertexSet_tail]
  -- ditto for ex ∈ P.edge
  obtain (hex|ex_notMem) := Classical.em (ex ∈ P.edge)
  · have h_dinc' : P.DInc ex x P.last := by
      have h_isLink' : P.IsLink ex P.last x := by
        simpa [hP.isPath.isWalk.isLink_iff_isLink_of_mem hex]
      rw [isLink_iff_dInc] at h_isLink'
      obtain (h|h) := h_isLink' <;> [exfalso; assumption]
      have := h.ne_last hP.isPath.nodup
      contradiction
    rw [dInc_iff_eq_of_dInc_of_vertex_nodup_left hP.isPath.nodup h_dinc (f := ex) (y := P.last)]
      at h_dinc'
    obtain ⟨rfl, rfl⟩ := h_dinc'
    have hC : G.IsCycle (cons P.last ey P) :=
      hP.isPath.cons_isCycle_of_nontrivial hy P_nontrivial
    refine ⟨cons P.last ey P, hC, ?_⟩
    simp [←hC.isClosed.vertexSet_tail]

  -- we now do surgery on a grape
  let pref := P.prefixUntilVertex x
  let suff := P.suffixFromVertex y
  have pref_dinc_suff_eq : pref ++ cons x e suff = P := by
    simp only [pref, suff, IsPath.prefixUntilVertex_dInc_suffixFromVertex hP.isPath h_dinc]
  have x_notMem_suff : x ∉ suff := by
    have h_isSuff : (cons x e suff).IsSuffix P := by
      rw [← pref_dinc_suff_eq]
      exact WList.isSuffix_append_left _ _
    apply hP.isPath.suffix at h_isSuff
    simp only [cons_isPath_iff] at h_isSuff
    tauto

  have h_disj : Disjoint V(pref) V(suff) := by
    by_contra! hcon
    rw [not_disjoint_iff_nonempty_inter] at hcon
    obtain ⟨u, hu_pref, hu_suff⟩ := hcon
    have h_isPath := hP.isPath.reverse
    rw [← pref_dinc_suff_eq, WList.reverse_append] at h_isPath
      <;> [skip ; exact P.prefixUntilVertex_last h_dinc.left_mem]
    rw [reverse_cons] at h_isPath
    have disj := h_isPath.diff_Last_disjoint_of_append
    simp only [concat_vertexSet_eq, reverse_vertexSet, concat_last, mem_singleton_iff,
      insert_diff_of_mem, mem_vertexSet_iff, x_notMem_suff, not_false_eq_true,
      diff_singleton_eq_self] at disj
    exact disj.notMem_of_mem_right hu_pref hu_suff

  have y_notMem_pref : y ∉ pref := by
    intro h_y_pref
    have h_y_suff : y ∈ suff := by
      simp [suff]; nth_rewrite 2 [←P.suffixFromVertex_first h_dinc.right_mem]
      exact WList.first_mem
    exact h_disj.notMem_of_mem_left h_y_pref h_y_suff
  have notMem_pref_edge_of_notMem_edge {e} (h : e ∉ P.edge) : e ∉ pref.edge := by
    intro bad
    simp only [pref] at bad
    have := WList.IsPrefix.mem_edge (P.prefixUntilVertex_isPrefix x) bad
    contradiction
  have notMem_suff_edge_of_notMem_edge {e} (h : e ∉ P.edge) : e ∉ suff.edge := by
    intro bad
    simp only [suff] at bad
    have := WList.IsSuffix.mem_edge (P.suffixFromVertex_isSuffix y) bad
    contradiction

  have h₁ : G.IsPath (cons P.first ey suff) := by
    simp
    refine ⟨?_, ?_, ?_⟩
    · refine hP.isPath.suffix (P.suffixFromVertex_isSuffix y)
    · suffices suff.first = y by simpa [this]
      refine suffixFromVertex_first h_dinc.right_mem
    intro bad
    have := hP.isPath.first_in_suffixFromVertex_iff h_dinc.right_mem
    simp [suff, this] at bad
    exact hy.ne bad
  have h₂ : G.IsPath (pref.reverse ++ (cons P.first ey suff)) := by
    have pref'_isPath : G.IsPath pref.reverse := by
      refine IsPath.reverse ?_
      refine hP.isPath.prefix (P.prefixUntilVertex_isPrefix x)
    refine pref'_isPath.append h₁ (by simp [pref, suff]) ?_
    intro u hu_pref' hu_cons
    simp only [mem_cons_iff] at hu_cons
    obtain (h|h) := hu_cons
    · simpa [pref]
    change u ∈ V(suff) at h
    replace hu_pref' : u ∈ V(pref) := by
      rwa [WList.mem_reverse] at hu_pref'
    exfalso
    exact h_disj.notMem_of_mem_left hu_pref' h
  have h₃ : G.IsCycle (cons P.last ex (pref.reverse ++ (cons P.first ey suff))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [cons_isTrail_iff, append_edge, reverse_edge, cons_edge, List.mem_append,
      List.mem_reverse, List.mem_cons, not_or]
      refine ⟨h₂.isTrail, ?_, ?_⟩
      · simpa [pref, P.prefixUntilVertex_last h_dinc.left_mem]
      refine ⟨by tauto, ?_, by tauto⟩
      intro rfl
      suffices : P.first = P.last
      · rw [WList.first_eq_last_iff hP.isPath.nodup, ←WList.length_eq_zero] at this
        rw [←WList.two_le_length_iff] at P_nontrivial
        omega
      obtain (h|h) := hx.eq_and_eq_or_eq_and_eq hy <;> [exact h.1.symm; exfalso]
      apply ex_notMem
      rw [←h.2] at hy
      have e_isLink : G.IsLink e x y := hP.isPath.isWalk.isLink_of_isLink h_dinc.isLink
      rw [hy.unique_edge e_isLink]
      exact h_dinc.edge_mem
    · simp
    · simp only [cons_isClosed_iff, append_last, last_cons]
      show P.last = suff.last
      simp [suff]
    simp only [tail_cons]
    exact h₂.nodup
  refine ⟨cons P.last ex (pref.reverse ++ cons P.first ey suff), h₃, ?_⟩
  simp only [← h₃.isClosed.vertexSet_tail, tail_cons]
  rw [WList.append_vertexSet_of_eq (by simp [pref]), WList.reverse_vertexSet]
  nth_rewrite 2 [← pref_dinc_suff_eq]
  rw [WList.append_vertexSet_of_eq]
  swap
  · simp only [first_cons, pref]
    exact P.prefixUntilVertex_last h_dinc.left_mem
  simp only [cons_vertexSet, union_insert]
  ext u
  refine ⟨?_, ?_⟩
  · rintro (rfl|hu)
    · right; left
      rw [← P.prefixUntilVertex_first x]
      exact WList.first_mem
    right; assumption
  rintro (rfl|hu)
  · right; left
    rw [← P.prefixUntilVertex_last h_dinc.left_mem]
    exact WList.last_mem
  right; assumption

lemma dirac_isHamiltonianCycle [G.Simple] [G.Finite] (hNontrivial : 3 ≤ V(G).encard)
    (hDegree : V(G).encard ≤ 2 * G.minEDegree) (hP : G.IsLongestPath P)
    (hC : G.IsCycle C ∧ V(C) = V(P)) : G.IsHamiltonCycle C := by
  classical
  -- Suppose not. Then there exists some x ∈ V(G) - V(C).
  -- Since G is connected, we can find a path from x to C, say Q.
  -- Let z be the last element of Q which is not in C.
  -- Then we can extend P by z to contradict the maximality of P.
  by_contra! hcon
  have vx_finite : V(G).Finite := vertexSet_finite
  obtain ⟨hC, hCP⟩ := hC
  simp only [IsHamiltonCycle, not_and] at hcon
  simp_all only [vertexSet_finite, forall_const]
  have hCG : V(C) ⊆ V(G) := hC.isWalk.vertexSet_subset
  have hCG_ssub : V(C) ⊂ V(G) := ⟨hCG, by rwa [hCP]⟩
  rw [ssubset_iff_of_subset hCG] at hCG_ssub
  -- we now have our element x ∈ V(G - C)
  obtain ⟨x, hxG, hnxC⟩ := hCG_ssub

  -- pick up any element of C
  have ⟨y, hy⟩ : V(C).Nonempty := C.vertexSet_nonempty

  have hConn := dirac_connected hNontrivial hDegree
  -- find a path between x, y
  have hyG : y ∈ V(G) := hCG hy
  have ⟨Q, hQ, hQ_first, hQ_last⟩ := (hConn.connBetween hxG hyG).exists_isPath
  symm at hQ_first hQ_last
  let pref := Q.prefixUntil V(C)
  have pref_isPath : G.IsPath pref := hQ.prefix (Q.prefixUntil_isPrefix V(C))
  have pref_last : V(C) pref.last := by
    apply Q.prefixUntil_prop_last
    refine ⟨y, ?_, hy⟩
    rw [hQ_last]
    exact Q.last_mem
  have last_ne_first : pref.last ≠ pref.first := by
    conv => rhs; simp only [pref]
    intro heq
    rw [Q.prefixUntil_first V(C)] at heq
    rw [heq, ← hQ_first] at pref_last
    contradiction
  -- choose the last element which is not on C
  have ⟨e, z, h_dinc⟩ := pref.exists_left_edge pref.last_mem last_ne_first
  have z_ne_last : z ≠ pref.last :=
    (pref_isPath.isWalk.isLink_of_dInc h_dinc).adj.ne
  have hnzC : ¬ V(C) z := prefixUntil_not_prop h_dinc.left_mem z_ne_last.symm

  have C_nontrivial : C.Nontrivial := by
    rw [←one_lt_length_iff]
    have := hC.three_le_length_of_simple
    omega
  have ⟨P', f, f', hP', hP'_last, hP'_f, hP'_f', f_ne_f', heq⟩ :=
    hC.exists_isPath_vertex C_nontrivial pref_last
  generalize P''_def : P'.concat f' pref.last = P''; symm at P''_def
  have h_isCycle : G.IsCycle (cons pref.last f P'') := by
    rw [P''_def, ←heq]
    exact hC.rotate (C.idxOf pref.last)
  have P''_isPath : G.IsPath P'' := by
    simpa using h_isCycle.tail_isPath
  have P''_vertexSet_eq : V(P'') = V(P) := by
    rw [← hCP]
    apply congr_arg WList.vertexSet at heq
    rw [← P''_def, hC.isClosed.rotate_vertexSet] at heq
    rw [heq, ← h_isCycle.isClosed.vertexSet_tail]
    simp
  -- e x t e n d
  generalize P'''_def : P''.concat e z = P'''
  symm at P'''_def
  have P'''_isPath : G.IsPath P''' := by
    simp only [P'''_def, concat_isPath_iff]
    refine ⟨P''_isPath, ?_, ?_⟩
    · simp only [P''_def, concat_last]
      exact (pref_isPath.isWalk.isLink_of_dInc h_dinc).symm
    change z ∉ V(P'')
    rw [P''_vertexSet_eq, ←hCP]
    exact hnzC
  have P'''_length : P'''.length = P''.length + 1 := by
    simp [P'''_def]
  rw [← length_vertex P'', P''_isPath.vertex_length_eq_vertexSet_ncard, P''_vertexSet_eq,
    ← hP.isPath.vertex_length_eq_vertexSet_ncard, length_vertex P] at P'''_length
  have := maximalFor_is_upper_bound WList.length hP _ P'''_isPath
  omega

lemma dirac [G.Simple] [G.Finite] (hV : 3 ≤ V(G).encard) (hDegree : V(G).encard ≤ 2 * G.minEDegree):
    ∃ C, G.IsHamiltonCycle C := by
  have hnonempty : V(G).Nonempty := by
    rw [← Set.encard_pos]
    enat_to_nat! <;> omega
  have ⟨P, hP⟩ := G.exists_longest_path hnonempty
  have ⟨C, hC⟩ := dirac_exists_cycle hV hDegree hP
  exact ⟨C, dirac_isHamiltonianCycle hV hDegree hP hC⟩

-- #print axioms dirac
