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
  have ⟨hyT', hzT'⟩ : y ∈ V(T - {x}) ∧ z ∈ V(T - {x}) := by
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
    refine ⟨by rwa [hP_first], hP.of_le deleteVerts_le, ?_⟩
    intro bad
    replace hP := hP.vertexSet_subset
    apply hP at bad
    rw [deleteVerts_vertexSet] at bad
    apply bad.2
    simp
  let Q := cons z xz Q'
  have hQ_isCycle : T.IsCyclicWalk Q := by
    have := hQ'_isPath.cons_isCyclicWalk_of_nontrivial (G := T) (P := Q') (e := xz)
    simp only [first_cons, last_cons, hP_last, hxz, cons_nontrivial_iff, forall_const, Q'] at this
    apply this
    by_contra! bad
    apply hne
    rw [←hP_first, ←hP_last]
    exact Nil.first_eq_last bad
  exact (isForest_iff_not_isCyclicWalk.mp hT.isForest) _ hQ_isCycle

lemma IsTree.exists_isMinSepSet (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ S, IsMinSep T S ∧ S.encard = 1 := by
  obtain ⟨S, hS, hS_encard⟩ := hT.isForest.exists_isSepSet hV
  refine ⟨S, ⟨hS, ?_⟩, hS_encard⟩
  intro A hA
  by_contra! hcon
  replace hcon : A.encard = 0 := by enat_to_nat! <;> omega
  obtain rfl := by simpa using hcon
  simp [hT.connected] at hA

def IsHamiltonCycle (G : Graph α β) (C : WList α β) : Prop :=
  G.IsCyclicWalk C ∧ V(G) ⊆ V(C)

lemma IsHamiltonCycle.isCycle (hC : G.IsHamiltonCycle C) : G.IsCyclicWalk C := hC.1
lemma IsHamiltonCycle.vertexSet_supset (hC : G.IsHamiltonCycle C) : V(G) ⊆ V(C) := hC.2

lemma IsHamiltonCycle.vertexSet_eq (hC : G.IsHamiltonCycle C) : V(C) = V(G) := by
  refine hC.isCycle.vertexSet_subset.antisymm hC.vertexSet_supset

lemma IsHamiltonCycle.vertexSet_encard_eq
    (hC : G.IsHamiltonCycle C) : V(C).encard = V(G).encard :=
  congr_arg Set.encard hC.vertexSet_eq

lemma isHamiltonianCycle_iff : G.IsHamiltonCycle C ↔ G.IsCyclicWalk C ∧ V(G) = V(C) :=
  ⟨fun h ↦ ⟨h.isCycle, h.vertexSet_eq.symm⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂.subset⟩⟩

protected
lemma IsCyclicWalk.isHamiltonianCycle_iff (hC : G.IsCyclicWalk C) :
    G.IsHamiltonCycle C ↔ V(G) = V(C) :=
  ⟨fun h ↦ (isHamiltonianCycle_iff.mp h).2, fun h ↦ ⟨hC, h.le⟩⟩

-- Note: this is always true because WLists are finite
lemma isHamilonianCycle_of_vertexSet_encard_eq
    (hC : G.IsCyclicWalk C) (hen : V(C).encard = V(G).encard) : G.IsHamiltonCycle C := by
  refine ⟨hC, Eq.subset ?_⟩
  symm
  exact Set.Finite.eq_of_subset_of_encard_le C.vertexSet_finite hC.vertexSet_subset hen.symm.le

def SetVxAdj (G : Graph α β) (H : Set α) (v : α) : Prop :=
    ∃ w, w ∈ H ∧ G.Adj v w

lemma Hamiltonian_to_cycle (hham : ∃ C, G.IsHamiltonCycle C) : ∃ C, G.IsCyclicWalk C  := by
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
    ∃ C, G.IsCyclicWalk C := by
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
  rw [← isForest_iff_not_isCyclicWalk] at h_isForest
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
    ∃ P, D.IsPath P ∧ P.first = x ∧ P.last = y :=
  (hDconn.connBetween hx hy).exists_isPath


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
    refine MinimalFor.le (f := fun H : Graph α β => H.vertexSet.ncard) min_comp_spec ?_
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
  have solver := MaximalFor.le (f := WList.length) hP hQ
  omega

lemma dirac_exists_cycle [G.Simple] [G.Finite] (hNontrivial : 3 ≤ V(G).encard)
    (hDegree : V(G).encard ≤ 2 * G.minEDegree) (hP : G.IsLongestPath P) :
    ∃ C, G.IsCyclicWalk C ∧ V(C) = V(P) := by
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
    have hC : G.IsCyclicWalk (cons P.last ex P) :=
      hP.isPath.cons_isCyclicWalk_of_nontrivial hx.symm P_nontrivial
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
    have hC : G.IsCyclicWalk (cons P.last ey P) :=
      hP.isPath.cons_isCyclicWalk_of_nontrivial hy P_nontrivial
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
      insert_sdiff_of_mem, mem_vertexSet_iff, x_notMem_suff, not_false_eq_true,
      sdiff_singleton_eq_self] at disj
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
    refine ⟨?_, hP.isPath.suffix (P.suffixFromVertex_isSuffix y), ?_⟩
    · suffices suff.first = y by simpa [this]
      refine suffixFromVertex_first h_dinc.right_mem
    intro bad
    have := hP.isPath.first_mem_suffixFromVertex_iff h_dinc.right_mem
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
  have h₃ : G.IsCyclicWalk (cons P.last ex (pref.reverse ++ (cons P.first ey suff))) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [cons_isTrail_iff, append_edge, reverse_edge, cons_edge, List.mem_append,
      List.mem_reverse, List.mem_cons, not_or]
      refine ⟨h₂.isTrail, ?_, ?_⟩
      · unfold pref
        rwa [append_first_of_eq (by simp), reverse_first, prefixUntilVertex_last]
        exact h_dinc.left_mem
      refine ⟨by tauto, ?_, by tauto⟩
      intro rfl
      suffices : P.first = P.last
      · rw [WList.first_eq_last_iff hP.isPath.nodup, ←WList.length_eq_zero] at this
        rw [←WList.two_le_length_iff] at P_nontrivial
        omega
      obtain (h|h) := hx.eq_and_eq_or_eq_and_eq hy <;> [exact h.1.symm; exfalso]
      apply ex_notMem
      rw [←h.2] at hy
      have e_isLink : G.IsLink e x y := hP.isPath.isWalk.isLink_mono h_dinc.isLink
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
    (hC : G.IsCyclicWalk C ∧ V(C) = V(P)) : G.IsHamiltonCycle C := by
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
  let pref := Q.prefixUntil (· ∈ V(C))
  have pref_isPath : G.IsPath pref := hQ.prefix (Q.prefixUntil_isPrefix (· ∈ V(C)))
  have pref_last : V(C) pref.last := by
    apply Q.prefixUntil_prop_last
    refine ⟨y, ?_, hy⟩
    rw [hQ_last]
    exact Q.last_mem
  have last_ne_first : pref.last ≠ pref.first := by
    conv => rhs; simp only [pref]
    intro heq
    rw [Q.prefixUntil_first (· ∈ V(C))] at heq
    rw [heq, ← hQ_first] at pref_last
    contradiction
  -- choose the last element which is not on C
  have ⟨e, z, h_dinc⟩ := pref.exists_left_edge pref.last_mem last_ne_first
  have z_ne_last : z ≠ pref.last :=
    (pref_isPath.isWalk.isLink_of_dInc h_dinc).adj.ne
  have hnzC : z ∉ V(C) := prefixUntil_not_prop h_dinc.left_mem z_ne_last.symm

  have C_nontrivial : C.Nontrivial := by
    rw [←one_lt_length_iff]
    have := hC.three_le_length_of_simple
    omega
  have ⟨P', f, f', hP', hP'_last, hP'_f, hP'_f', f_ne_f', heq⟩ :=
    hC.exists_isPath_vertex C_nontrivial pref_last
  generalize P''_def : P'.concat f' pref.last = P''; symm at P''_def
  have h_isCycle : G.IsCyclicWalk (cons pref.last f P'') := by
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
  rw [← length_vertex P'', P''_isPath.vertex_length_eq_ncard, P''_vertexSet_eq,
    ← hP.isPath.vertex_length_eq_ncard, length_vertex P] at P'''_length
  have := MaximalFor.le (f := WList.length) hP P'''_isPath
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
