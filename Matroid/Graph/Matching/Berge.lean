import Matroid.Graph.Matching.Defs

namespace Graph

variable {α β : Type*} {G H C P : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α}
  {e f : β}

open Set symmDiff WList

-- `IsAugmenter` takes the place of augmenting paths; it is a strict generalization.
structure IsAugmenter (G : Graph α β) (M : Set β) (P : Graph α β) : Prop where
  le : P ≤ G
  -- effectively, MaxDegreeLE 2, but also we have no isolated vertices
  eDegree_eq_one_or_two : ∀ ⦃x⦄, x ∈ V(P) → P.eDegree x = 1 ∨ P.eDegree x = 2
  -- there is at least one leaf (this shows that there is at least one augmenting path in our graph)
  exists_isLeaf : ∃ x, P.IsLeaf x
  -- all internal vx of P are matched by M, by edges of P
  match_nonleaf : ∀ ⦃x⦄, P.eDegree x = 2 → x ∈ V(P, M)
  -- neither of the leaf vxs of P are matched by M
  no_match_leaf : ∀ ⦃x⦄, P.eDegree x = 1 → x ∉ V(G, M)

attribute [grind →, grind <=]
    IsAugmenter.le IsAugmenter.eDegree_eq_one_or_two IsAugmenter.exists_isLeaf
    IsAugmenter.match_nonleaf IsAugmenter.no_match_leaf

lemma IsAugmenter.matched_vertexSet_eq (hP : G.IsAugmenter M P) :
    V(P, M) = {x ∈ V(P) | P.eDegree x = 2} := by
  ext x
  refine ⟨?_, ?_⟩
  · intro hx
    refine ⟨by grind, ?_⟩
    by_contra! bad
    replace bad : P.eDegree x = 1 := by
      have := hP.eDegree_eq_one_or_two (incVertexSet_subset _ _ hx)
      grind only
    exact hP.no_match_leaf bad (incVertexSet_mono hP.le _ hx)
  grind

lemma IsAugmenter.matched_vertexSet_eq' (hP : G.IsAugmenter M P) :
    V(P, E(P) ∩ M) = {x ∈ V(P) | P.eDegree x = 2} := by
  rw [← hP.matched_vertexSet_eq, inter_comm, incVertexSet_inter_edgeSet]

lemma IsAugmenter.maxDegreeLE_two (hP : G.IsAugmenter M P) : P.MaxDegreeLE 2 := by
  rw [maxDegreeLE_iff']
  intro x hx
  obtain (h|h) := hP.eDegree_eq_one_or_two hx
    <;> (enat_to_nat!; omega)

lemma IsAugmenter.degreePos (hP : G.IsAugmenter M P) : P.DegreePos := by
  rw [degreePos_iff']
  intro x hx
  obtain (h|h) := hP.eDegree_eq_one_or_two hx
    <;> (enat_to_nat!; omega)

lemma IsAugmenter.edgeSet_nonempty (hP : G.IsAugmenter M P) : E(P).Nonempty := by
  have ⟨x, e, hex⟩ := hP.exists_isLeaf
  exact ⟨e, hex.edge_mem⟩

lemma IsAugmenter.diff_matching_isMatching [P.Loopless] (hP : G.IsAugmenter M P) :
    P.IsMatching (E(P) \ M) where
  subset := by
    grw [diff_subset]
  disjoint e f he hf hne := by
    rw [disjoint_left]
    intro x hxe hxf
    change e ∈ E(P, x) at hxe
    change f ∈ E(P, x) at hxf
    have deg : P.eDegree x = 2 := by
      refine (hP.maxDegreeLE_two x).antisymm ?_
      rw [eDegree_eq_encard_inc, Nat.cast_ofNat, two_le_encard_iff_nontrivial]
      refine ⟨e, hxe, f, hxf, hne⟩
    have h_incEdges : E(P, x) = {e, f} := by
      symm
      rw [←Nat.cast_ofNat, eDegree_eq_encard_inc] at deg
      have fin : E(P, x).Finite := by
        exact finite_of_encard_le_coe (le_of_eq deg)
      refine eq_of_subset_of_ncard_le ?_ ?_ ‹_›
      · rintro e' (rfl|rfl) <;> assumption
      apply congr_arg ENat.toNat at deg
      simp [← ncard_def] at deg
      grw [deg, ncard_pair hne]
    have bad := hP.match_nonleaf deg
    simp at bad
    obtain ⟨e', he'M, he'⟩ := bad
    change e' ∈ E(P, x) at he'
    simp [h_incEdges] at he'
    obtain (rfl|rfl) := he'
      <;> [exact he.2 ‹_›; exact hf.2 ‹_›]

lemma IsAugmenter.vertexSet_disjoint (hM : G.IsMatching M) (hP : G.IsAugmenter M P) :
    Disjoint V(P) V(G, M \ E(P)) := by
  rw [disjoint_left]
  intro x hxP hxGM'
  have hxGM : x ∈ V(G, M) := by
    simp at hxGM'
    obtain ⟨e, he⟩ := hxGM'
    refine ⟨e, he.1.1, he.2⟩
  obtain (h|h) := hP.eDegree_eq_one_or_two hxP
  · exact hP.no_match_leaf ‹_› hxGM
  have M_diff_matching : G.IsMatching (M \ E(P)) :=
    hM.anti_right diff_subset
  have P_matching : P.IsMatching (E(P) ∩ M) :=
    hM.anti_left' hP.le
  have hxPM : x ∈ V(P, E(P) ∩ M) := by
    have ⟨e, he⟩ := hP.match_nonleaf h
    exact ⟨e, ⟨he.2.edge_mem, he.1⟩, he.2⟩
  have ⟨e, he, e_unique⟩ := hM.existsUnique_covering_edge hxGM
  obtain ⟨e', he', -⟩ := M_diff_matching.existsUnique_covering_edge hxGM'
  obtain ⟨f, hf, -⟩ := P_matching.existsUnique_covering_edge hxPM
  simp at e_unique he he' hf
  have : e' = f := by
    rw [e_unique _ he'.1.1 he'.2, e_unique _ hf.1.2 (hf.2.of_le hP.le)]
  rw [this] at he'
  exact he'.1.2 hf.2.edge_mem

/-- Given a matching M and an augmenting path P for M, we can get back a larger matching --/
lemma IsAugmenter.symmDiff_matching_isMatching [P.Loopless] (hM : G.IsMatching M)
    (hP : G.IsAugmenter M P) : G.IsMatching (E(P) ∆ M) := by
  rw [symmDiff_comm]
  have disj : P.StronglyDisjoint (Subgraph.ofEdge G (M \ E(P))) := by
    refine ⟨?_, ?_⟩
    · simp
      exact hP.vertexSet_disjoint hM
    rw [disjoint_left]
    simp
    grind only
  have P_matching : P.IsMatching (E(P) \ M) := hP.diff_matching_isMatching
  set G' := Subgraph.ofEdge G (M \ E(P))
  have G'_matching : G'.val.IsMatching (M \ E(P)) := by
    have matching : G.IsMatching (M \ E(P)) :=
      hM.anti_right diff_subset
    refine matching.anti_left G'.le ?_
    simp [G']
    grw [← subset_union_right, hM.subset]
  have := P_matching.union G'_matching disj
  rw [symmDiff_comm, Set.symmDiff_def]
  refine this.mono_left ?_
  refine Graph.union_le hP.le G'.le

lemma IsAugmenter.diff_matching_vertexSet [P.Loopless] (hM : G.IsMatching M)
    (hP : G.IsAugmenter M P) : V(P, E(P) \ M) = V(P) := by
  -- every degree-2 vertex gets matched by the other edge
  -- every degree-1 vertex must have previously been unmatched, and hence must now be matched
  refine eq_of_subset_of_subset (incVertexSet_subset _ _) ?_
  intro x hxP
  obtain (deg|deg) := hP.eDegree_eq_one_or_two hxP
  · -- degree 1
    have h : P.eDegree x = 1 := deg
    rw [eDegree_eq_encard_inc, encard_eq_one] at h
    obtain ⟨e, heq⟩ := h
    have he : P.Inc e x := by
      change e ∈ E(P, x)
      simp [heq]
    have he_notMem_M : e ∉ M := by
      intro heM
      refine hP.no_match_leaf deg ?_
      refine ⟨e, heM, he.of_le hP.le⟩
    refine ⟨e, ⟨he.edge_mem, he_notMem_M⟩, he⟩
  -- degree 2
  have ⟨e, he⟩ := hP.match_nonleaf deg
  rw [eDegree_eq_encard_inc] at deg
  symm at deg; apply le_of_eq at deg
  rw [two_le_encard_iff_nontrivial] at deg
  have ⟨f, hf⟩ := deg.exists_ne e
  refine ⟨f, ⟨hf.1.edge_mem, ?_⟩, hf.1⟩
  intro hfM
  have := hM.disjoint hfM he.1 hf.2
  rw [disjoint_left] at this
  exact this (hf.1.of_le hP.le) (he.2.of_le hP.le)

-- TODO: move
lemma incVertexSet_mono_right {F F' : Set β} (G : Graph α β) (hsub : F ⊆ F') :
    V(G, F) ⊆ V(G, F') := by
  rintro x ⟨e, heF, hex⟩
  refine ⟨e, hsub heF, hex⟩

lemma IsAugmenter.symmDiff_matching_vertexSet [P.Loopless] (hM : G.IsMatching M)
    (hP : G.IsAugmenter M P) : V(P, E(P) ∆ M) = V(P) := by
  refine eq_of_subset_of_subset (incVertexSet_subset _ _) ?_
  grw [Set.symmDiff_def, ← incVertexSet_mono_right _ (subset_union_left),
    hP.diff_matching_vertexSet hM]

-- TODO: rename; what a mouthful
-- TODO: also, is this even useful in this form? statements about encard ≤ encard are really weak...
--       we really want to say that there is at least one more element.
-- this can't even be _ < _ anymore, since we are no longer assuming a path (which is guaranteed to
-- be finite).
lemma IsAugmenter.matching_encard_add_one_le_diff_matching_encard [P.Loopless]
    (hM : G.IsMatching M) (hP : G.IsAugmenter M P) : (E(P) ∩ M).encard + 1 ≤ (E(P) \ M).encard := by
  -- (E(P) \ M) matches all of V(P)
  -- so 2 * |E(P) \ M| = |V(P)|
  -- meanwhile, (E(P) ∩ M) matches V(P) \ {P.first, P.last}
  -- so 2 * |E(P) ∩ M| = |V(P) \ {P.first, P.last}| = |V(P)| - 2
  -- so |E(P) \ M| = 1 + |E(P) ∩ M|
  have M'_isMatching : P.IsMatching (E(P) \ M) := diff_matching_isMatching hP
  have M'_matched_vertexSet : V(P, E(P) \ M) = V(P) := hP.diff_matching_vertexSet hM
  have M'_encard : 2 * (E(P) \ M).encard = V(P).encard := by
    rw [← M'_isMatching.matched_vertexSet_encard_eq, M'_matched_vertexSet]
  have M_matching : P.IsMatching (E(P) ∩ M) :=
    hM.anti_left' hP.le
  have M_matched_vertexSet : V(P, E(P) ∩ M) = {x ∈ V(P) | P.eDegree x = 2} :=
    hP.matched_vertexSet_eq'
  have M_encard : 2 * (E(P) ∩ M).encard = V(P, E(P) ∩ M).encard :=
    M_matching.matched_vertexSet_encard_eq.symm
  obtain (h_top|h_ne_top) := em (V(P).encard = ⊤)
  · rw [h_top, ENat.mul_eq_top_iff] at M'_encard
    obtain (h|h) := M'_encard
    · enat_to_nat
    rw [h.2]
    exact le_top
  have VP_fin : V(P).Finite := by
    rw [← ne_eq, encard_ne_top_iff] at h_ne_top
    assumption
  have VPM_fin : V(P, E(P) ∩ M).Finite :=
    VP_fin.subset (incVertexSet_subset _ _)
  suffices hssub : V(P, E(P) ∩ M) ⊂ V(P)
  · have hlt := VPM_fin.encard_lt_encard hssub
    enat_to_nat!; omega
  rw [ssubset_iff_exists]
  refine ⟨incVertexSet_subset _ _, ?_⟩
  obtain ⟨x, hx⟩ := hP.exists_isLeaf
  refine ⟨x, hx.mem, ?_⟩
  rintro ⟨e, hePM, hex⟩
  refine hP.no_match_leaf hx.eDegree ?_
  refine ⟨e, hePM.2, hex.of_le hP.le⟩

lemma IsAugmenter.matching_encard_add_one_le_symmDiff_matching_encard [P.Loopless]
    (hM : G.IsMatching M) (hP: G.IsAugmenter M P) : M.encard + 1 ≤ (E(P) ∆ M).encard := by
  have hdisj : Disjoint (E(P) \ M) (M \ E(P)) := disjoint_sdiff_sdiff
  conv_rhs => rw [Set.symmDiff_def, encard_union_eq hdisj, add_comm]
  conv_lhs => rw [show M = (M \ E(P)) ∪ (M ∩ E(P)) by grind, encard_union_eq disjoint_sdiff_inter,
    add_assoc]
  obtain (h_top|h_ne_top) := em ((M \ E(P)).encard = ⊤)
  · simp only [h_top, top_add, le_refl]
  refine (ENat.add_le_add_iff_left h_ne_top).mpr ?_
  rw [inter_comm]
  exact hP.matching_encard_add_one_le_diff_matching_encard hM

-- for finite graphs then (or more generally, graphs with finite matching number),
-- there must not be an augmenting path whenever we have a max matching
lemma IsMaxMatching.not_isAugmenter [G.EdgeFinite]
    (hM : G.IsMaxMatching M) (P : Graph α β) [P.Loopless] :
    ¬ G.IsAugmenter M P := by
  intro hP
  -- TODO: wish this would be automatically detected by `enat_to_nat`
  have M_encard_fin : M.encard < ⊤ := by
    rw [encard_lt_top_iff]
    refine Finite.subset edgeSet_finite hM.subset
  have M'_isMatching : G.IsMatching (E(P) ∆ M) :=
    hP.symmDiff_matching_isMatching hM.toIsMatching
  have := hP.matching_encard_add_one_le_symmDiff_matching_encard hM.toIsMatching
  have := hM.max _ M'_isMatching
  enat_to_nat!; omega

/-
 sketch of other direction:
 first, for matchings M, M' on G, let G' := Subgraph.ofEdges G (M ∆ M')
 then, components of G' must be one of:
 * isolated vertex
 * even cycle with edges alternating b/n M and M'
 * paths with edges alternating b/n M and M'

 showing that the components are cycles / paths shouldnt be hard; more attention needs to be paid
 perhaps to "edges alternating b/n M and M'"

 now, suppose M is not a max matching for G. then there exists a matching M' with |M'| > |M|.
 so there must be a component which is a path and has more edges from M' than from M;
 thus this component must be an augmenting path.
-/

@[simp]
lemma Subgraph.ofEdge_inc_iff (F : Set β) :
    (Subgraph.ofEdge G F).val.Inc e x ↔ e ∈ F ∧ G.Inc e x := by
  simp [Inc]

@[simp]
lemma Subgraph.ofEdge_incEdges_eq (F : Set β) :
    E(Subgraph.ofEdge G F, x) = E(G, x) ∩ F := by
  ext e; simp [IncEdges]; rw [and_comm]

lemma IsCycle.regular (h : G.IsCycle) : G.Regular 2 := by
  rw [isCycle_iff_exists_isCyclicWalk_eq] at h
  obtain ⟨C, hC, heq⟩ := h
  rw [← heq]
  exact hC.toGraph_regular

-- TODO (NB?): `grind` seems to cope better when `e` is passed in as an explicit parameter,
-- rather than as an implicit.
-- (As in, even if `e ∈ E(H)` is in context, if the conclusion is dealing with `e ∈ ...`,
-- then it's better equipped to figure things out, it seems...)
private
lemma symmDiff_edge_mem_or_mem
    [G.Loopless]
    (hle : H ≤ Subgraph.ofEdge G (M ∆ M')) (e : β) (he : e ∈ E(H)) :
    e ∈ M \ M' ∨ e ∈ M' \ M := by
  have := edgeSet_mono hle
  simp at this
  apply this.2 at he
  rw [Set.symmDiff_def] at he
  exact he

private
lemma symmDiff_matching_edge_at
    [G.Loopless]
    (hM : G.IsMatching M)
    (hle : H ≤ Subgraph.ofEdge G (M ∆ M'))
    (hex : e ∈ E(H, x)) (hfx : f ∈ E(H, x)) (hne : e ≠ f) (heM : e ∈ M) :
    f ∈ M' := by
  by_contra! hfM
  replace hfM : f ∈ M := by
    have := symmDiff_edge_mem_or_mem hle f (H.incEdges_subset x hfx)
    grind only [= mem_diff]
  -- here is a case where matching is baring its teeth...
  replace hex : e ∈ E(H ↾ M, x) := by
    simp only [incEdges_edgeRestrict]
    refine ⟨?_, ?_⟩ <;> assumption
  replace hfx : f ∈ E(H ↾ M, x) := by
    simp only [incEdges_edgeRestrict]
    refine ⟨?_, ?_⟩ <;> assumption
  have H_le_G : H ≤ G := hle.trans (Subgraph.le _)
  have := hM.incEdges_subsingleton' H_le_G x hex hfx
  contradiction

private
lemma symmDiff_matching_internal_vx
    [G.Loopless]
    (hM : G.IsMatching M) (hM' : G.IsMatching M')
    (hle : H ≤ Subgraph.ofEdge G (M ∆ M'))
    (hdeg : H.eDegree x = 2) :
    x ∈ V(H, M) ∧ x ∈ V(H, M') := by
  have H_le_G : H ≤ G := hle.trans <| Subgraph.le _
  have _ : H.Loopless := ‹G.Loopless›.mono H_le_G
  have edge_mem_or_mem := symmDiff_edge_mem_or_mem hle
  rw [eDegree_eq_encard_inc, encard_eq_two] at hdeg
  obtain ⟨e, f, hne, heq⟩ := hdeg
  wlog heM : e ∈ M generalizing e f with aux
  · refine aux f e hne.symm (by rw [heq, pair_comm]) ?_
    have he : e ∈ E(H, x) := by
      grind only [= mem_insert_iff]
    have hf : f ∈ E(H, x) := by
      grind only [= mem_insert_iff, = mem_singleton_iff]
    have heM' : e ∈ M' := by
      have := H.incEdges_subset x he
      grind only [= mem_diff]
    rw [symmDiff_comm] at hle
    exact symmDiff_matching_edge_at hM' hle he hf hne heM'
  have hfM' : f ∉ M := by
    intro hfM
    have he : e ∈ E(H ↾ M, x) := by
      grind only [= incEdges_edgeRestrict, = mem_inter_iff, = mem_insert_iff]
    have hf : f ∈ E(H ↾ M, x) := by
      grind only [= incEdges_edgeRestrict, = mem_inter_iff, = mem_insert_iff, = mem_singleton_iff]
    have := hM.incEdges_subsingleton' H_le_G x he hf
    contradiction
  replace hfM' : f ∈ M' := by grind
  refine ⟨?_, ?_⟩
    <;> [refine ⟨e, ?_⟩ ; refine ⟨f, ?_⟩]
  all_goals
    refine ⟨‹_›, ?_⟩
    change _ ∈ E(H, x)
    rw [heq]
    grind

private
lemma symmDiff_leaf_vx
    [G.Loopless]
    (hle : H ≤ Subgraph.ofEdge G (M ∆ M'))
    (hdeg : H.eDegree x = 1) :
    x ∈ V(H, M) \ V(H, M') ∨ x ∈ V(H, M') \ V(H, M) := by
  -- technically, this lemma doesn't need loopless since the degree condition already ensures that
  -- the edge at x is a nonloop. but it probably just makes life easier.
  have H_le_G : H ≤ G := hle.trans <| Subgraph.le _
  have _ : H.Loopless := ‹G.Loopless›.mono H_le_G
  rw [eDegree_eq_one_iff] at hdeg
  obtain ⟨e, he⟩ := hdeg
  wlog heM : e ∈ M generalizing M M' with aux
  · rw [symmDiff_comm] at hle
    have edge_mem_or_mem := symmDiff_edge_mem_or_mem hle
    specialize aux hle
    -- TODO: here, if `IsPendant.edge_mem` is hinted with `→`, then `grind` does do the right thing;
    -- however, it is otherwise too stupid to figure out that it should be using
    -- `he : H.IsPendant e x` otherwise, and you need to instead put
    -- `grind only [IsPendant.edge_mem he, = mem_diff]`.
    grind only [→ IsPendant.edge_mem, = mem_diff]
  left
  refine ⟨⟨e, heM, he.inc⟩, ?_⟩
  rintro ⟨f, hf⟩
  have := he.edge_unique hf.2
  have := symmDiff_edge_mem_or_mem hle
  grind only [→ Inc.edge_mem, = mem_diff]

private
lemma symmDiff_matching_cycle_edge_encard
    [G.Loopless]
    (hM : G.IsMatching M) (hM' : G.IsMatching M')
    (hle : H ≤ Subgraph.ofEdge G (M ∆ M'))
    (h_cycle : H.IsCycle) :
    (E(H) ∩ M).encard = (E(H) ∩ M').encard := by

  -- any edge in H must be in exactly one of M or M'
  have h_edge := symmDiff_edge_mem_or_mem hle

  have H_le_G : H ≤ G := hle.trans <| Subgraph.le _

  have _ : H.Loopless :=
    ‹G.Loopless›.mono H_le_G

  have h_vx : ∀ x ∈ V(H), x ∈ V(H, M) ∧ x ∈ V(H, M') := by
    intro x hx
    -- H is 2-regular, so there are two edges
    have hdeg := h_cycle.regular hx
    -- TODO: can you avoid needing `change` here?
    change H.eDegree x = 2 at hdeg
    exact symmDiff_matching_internal_vx hM hM' hle hdeg

  have vertexSet_eq₁ : V(H, M) = V(H) := by
    refine eq_of_subset_of_subset (incVertexSet_subset _ _) ?_
    exact fun x hx ↦ h_vx x hx |>.1
  have vertexSet_eq₂ : V(H, M') = V(H) := by
    refine eq_of_subset_of_subset (incVertexSet_subset _ _) ?_
    exact fun x hx ↦ h_vx x hx |>.2
  iterate rw [← edgeRestrict_edgeSet]
  have heq : 2 * E(H ↾ M).encard = 2 * E(H ↾ M').encard := by
    grind only [IsMatching.matched_vertexSet_encard_eq']
  -- TODO: grind dies here
  exact ENat.mul_left_cancel (n := 2) (by simp) (by simp) heq


lemma exists_isAugmenter_of_matching_encard_lt
    [G.Loopless] [G.EdgeFinite]
    (hM : G.IsMatching M) (hM' : G.IsMatching M') (hlt : M.encard < M'.encard) :
    ∃ P, G.IsAugmenter M P := by
  let P := Subgraph.ofEdge G (M ∆ M')
  have P_loopless : P.val.Loopless :=
    ‹G.Loopless›.mono P.2
  have P_degPos : P.val.DegreePos := by
    rw [degreePos_iff']
    intro x ⟨e, he⟩
    grw [← ENat.one_le_iff_ne_zero, ← encard_inc_le_eDegree, one_le_encard_iff_nonempty,
      Subgraph.ofEdge_incEdges_eq]
    refine ⟨e, he.2, he.1⟩
  have P_maxDegreeLE : P.val.MaxDegreeLE 2 := by
    rw [maxDegreeLE_iff']
    intro x hx
    simp only [eDegree_eq_encard_inc, P, Subgraph.ofEdge_incEdges_eq]
    rw [show E(G, x) ∩ M ∆ M' = E(G, x) ∩ (M \ M') ∪ E(G, x) ∩ (M' \ M) by grind]
    rw [encard_union_eq (by grind)]
    rw [show (2 : ℕ) = (1 : ℕ∞) + 1 by enat_to_nat]
    refine add_le_add ?_ ?_
    all_goals
      rw [← incEdges_edgeRestrict]
      refine IsMatching.incEdges_encard_le_one ?_ _
      exact IsMatching.anti_right ‹_› diff_subset
  have M_finite : M.Finite := by
    rw [← encard_lt_top_iff]
    exact lt_of_lt_of_le hlt le_top

  -- TODO:
  -- not just directly P, we want just the one augmenting path that must exist?
  obtain ⟨P', hP'P, hP'_encard⟩ :
      ∃ P' : Graph α β, P'.IsCompOf P ∧ (E(P') ∩ M).encard < (E(P') ∩ M').encard := by
    -- Suppose not.
    -- Then every component P' of P must satisfy |E(P') ∩ M'| ≤ |E(P') ∩ M|.
    -- Since P is equal to the union of its components,
    -- therefore |E(P) ∩ M'| ≤ |E(P) ∩ M| as well.
    -- But note, P is the smallest subgraph whose edges contrain M ∆ M',
    -- so E(P) = M ∆ M', so (E(P) ∩ M') = (M ∆ M') ∩ M' = M' \ M,
    -- and similarly (E(P) ∩ M) = M \ M'.
    -- Thus, |M' \ M| ≤ |M \ M'|, contradicting our outer assumption that |M| < |M'|.
    by_contra! hcon
    have P_edgeSet : E(P.val) = ⋃ i ∈ P.val.Components, E(i) := by
      change ∀ P' ∈ P.val.Components, (E(P') ∩ M').encard ≤ (E(P') ∩ M).encard at hcon
      conv_lhs => rw [P.val.eq_sUnion_components, sUnion_edgeSet]
    have PM'_edges : E(P.val) ∩ M' = ⋃ i : P.val.Components, E(i.val) ∩ M' := by
      simp only [P_edgeSet, iUnion_inter, iUnion_coe_set, mem_components_iff_isCompOf]
    have PM_edges : E(P.val) ∩ M = ⋃ i : P.val.Components, E(i.val) ∩ M := by
      simp only [P_edgeSet, iUnion_inter, iUnion_coe_set, mem_components_iff_isCompOf]
    have h_encard_le_encard : (E(P.val) ∩ M').encard ≤ (E(P.val) ∩ M).encard := by
      rw [PM'_edges, PM_edges]
      iterate rw [← ENat.tsum_encard_eq_encard_iUnion]
      · refine ENat.tsum_le_tsum ?_
        intro ⟨P', hP'⟩
        simp
        exact hcon P' hP'
      all_goals
        have hle : ∀ (F : Set β),
           (fun x : P.val.Components ↦ E(x.val) ∩ F) ≤ (fun x : P.val.Components ↦ E(x.val)) := by
          intro F C
          simp
        refine pairwise_disjoint_mono ?_ (hle _)
        intro P' P'' hne
        have := P.val.components_pairwise_stronglyDisjoint P'.2 P''.2 (by grind only) |>.edge
        grind only
    replace h_encard_le_encard : (M' \ M).encard ≤ (M \ M').encard := by
      simp [P] at h_encard_le_encard
      have hsub : M ∆ M' ⊆ E(G) := by
        grw [symmDiff_subset_union]
        grind only [IsMatching.anti_left, = subset_def, IsMatching.subset, = mem_union]
      rw [inter_eq_right.mpr hsub, Set.symmDiff_def] at h_encard_le_encard
      simp [union_inter_distrib_right] at h_encard_le_encard
      rw [inter_eq_left.mpr (by grind)] at h_encard_le_encard
      rw [inter_eq_left.mpr (by grind)] at h_encard_le_encard
      assumption
    rw [← encard_le_encard_iff_encard_diff_le_encard_diff] at h_encard_le_encard
    · rw [← not_le] at hlt
      exact hlt h_encard_le_encard
    exact M_finite.subset (by grind)

  have _ : P.val.EdgeFinite := edgeFinite_of_le P.2
  have hP'_path : P'.IsPathGraph := by
    -- Since P has MaxDegreeLE 2, therefore every component of P is either a cycle or a path.
    -- Since every cycle component of P (say P') has an equal number of edges in M as it does in M',
    -- it can't satisfy the condition that |E(P') ∩ M| < |E(P') ∩ M'|.
    -- Thus, it must be a path component.
    obtain (h|h) := hP'P.isPathGraph_or_isCycle_of_maxDegreeLE P_maxDegreeLE
      <;> [assumption ; exfalso]
    have := symmDiff_matching_cycle_edge_encard hM hM' hP'P.le h
    exact hP'_encard.ne ‹_›
  have _ : P'.Finite := hP'_path.finite

  have P'_deg : ∀ x ∈ V(P'), P'.eDegree x = 1 ∨ P'.eDegree x = 2 := by
    intro x hx
    have := P_maxDegreeLE x
    rw [degreePos_iff'] at P_degPos
    have := P_degPos (vertexSet_mono hP'P.le hx)
    rw [hP'P.isClosedSubgraph.eDegree_eq hx]
    enat_to_nat! <;> omega
  have _ : P'.Loopless := ‹P.val.Loopless›.mono hP'P.le

  refine ⟨P', ?_⟩
  constructor
  case le =>
    exact hP'P.le.trans P.2
  case eDegree_eq_one_or_two =>
    exact P'_deg
  case exists_isLeaf =>
    -- P' is a path, so we must have a leaf?
    refine ⟨hP'_path.first, hP'_path.isLeaf_first ?_⟩
    rw [← encard_ne_zero]
    -- TODO: this is as annoying case where i wish we could just have a tactic that clears this
    -- obligation.
    -- we have (E(P') ∩ M).encard < (E(P') ∩ M').encard, and we want to show that E(P').encard ≠ 0
    intro bad
    have : (E(P') ∩ M').encard ≤ E(P').encard :=
      encard_le_encard (inter_subset_left)
    enat_to_nat! <;> omega

  case match_nonleaf =>
    intro x hx
    exact symmDiff_matching_internal_vx hM hM' hP'P.le hx |>.1

  case no_match_leaf =>
  -- the leaf vertices of P' are exactly those matched by one of M or M'
  have P'_leaf : {x | P'.eDegree x = 1} = V(P', M) \ V(P', M') ∪ V(P', M') \ V(P', M) := by
    ext x
    simp only [mem_setOf_eq, mem_union]
    refine ⟨?_, ?_⟩
    · exact symmDiff_leaf_vx hP'P.le
    intro hx
    have hxP' : x ∈ V(P') := by grind only [!incVertexSet_subset, = mem_diff, = subset_def]
    by_contra! hdeg
    replace hdeg : P'.eDegree x = 2 := by grind only
    clear P'_deg
    have := symmDiff_matching_internal_vx hM hM' hP'P.le hdeg
    grind only [= mem_diff]

  have bruh : V(P', M).encard < V(P', M').encard := by
    rwa [hM.matched_vertexSet_encard_eq' (hP'P.le.trans P.2),
       hM'.matched_vertexSet_encard_eq' (hP'P.le.trans P.2),
       ENat.mul_lt_mul_left_iff (by simp) (by simp),
       edgeRestrict_edgeSet, edgeRestrict_edgeSet]
  rw [encard_lt_encard_iff_encard_diff_lt_encard_diff] at bruh
  swap
  · refine Finite.subset ?_ (inter_subset_left)
    refine (incVertexSet_finite P' _)
  -- there are exactly 2 leaves. so...
  replace P'_leaf : {x | P'.eDegree x = 1} = V(P', M') \ V(P', M) := by
    suffices emp : V(P', M) \ V(P', M') = ∅
    · simp only [emp, empty_union] at P'_leaf
      assumption
    rw [← encard_eq_zero]
    suffices leaf_encard : {x | P'.eDegree x = 1}.encard = 2
    · apply congr_arg Set.encard at P'_leaf
      rw [leaf_encard, encard_union_eq (disjoint_sdiff_sdiff)]
        at P'_leaf
      by_contra hcon
      rw [← ne_eq, ← ENat.one_le_iff_ne_zero] at hcon
      have h := lt_of_le_of_lt hcon bruh
      rw [← ENat.add_one_le_iff (by simp)] at h
      have winner := add_le_add hcon h
      rw [← P'_leaf] at winner
      enat_to_nat; omega
    have nontrivial : E(P').Nonempty := by
      rw [← encard_ne_zero]
      by_contra! hcon
      have h : (E(P') ∩ M').encard ≤ E(P').encard := encard_le_encard (inter_subset_left)
      clear P'_deg
      enat_to_nat! <;> omega
    simp only [eDegree_eq_one_iff, hP'_path.setOf_isLeaf_eq nontrivial]
    exact encard_pair <| hP'_path.first_ne_last nontrivial

  clear P'_deg
  intro x hdeg ⟨e, heM, hexG⟩
  have hx := hdeg
  rw [show P'.eDegree x = 1 ↔ x ∈ {x | P'.eDegree x = 1} by rfl, P'_leaf] at hx
  -- casework bash.
  rw [eDegree_eq_one_iff] at hdeg
  obtain ⟨f, hf⟩ := hdeg
  have hfM' : f ∈ M' := by
    obtain ⟨f', hf'⟩ := hx.1
    grind only
  have hfP' : f ∈ E(P') := by grind only [→ IsPendant.edge_mem]

  obtain (heM'|he_notMem_M') := em (e ∈ M')
  · -- if e ∈ M', then e cannot be in M ∆ M', so e cannot be f.
    -- but this violates the disjointness condition for the matching M'.
    have hfxGM' : f ∈ E(G ↾ M', x) := by
      simp only [incEdges_edgeRestrict, mem_inter_iff, mem_incEdges_iff]
      refine ⟨hf.inc.of_le hP'P.le |>.of_le P.2, hfM'⟩
    have hexGM' : e ∈ E(G ↾ M', x) := by
      simp only [incEdges_edgeRestrict, mem_inter_iff, mem_incEdges_iff]
      refine ⟨?_, ?_⟩ <;> assumption
    have := hM'.incEdges_subsingleton x hexGM' hfxGM'
    have := symmDiff_edge_mem_or_mem hP'P.le _ hfP'
    grind only [= mem_diff]
  -- now suppose e ∉ M'. then e ∈ M ∆ M', so e ∈ E(P).
  -- and since P' is a component of P, therefore e ∈ E(P') as well.
  -- and since we have `P'.IsPendant f x`, we must have e = f, again a contradiction.
  have hexP : P.val.Inc e x := by
    simp [P]
    grind only [= mem_symmDiff, → Inc.edge_mem]
  have hexP' : P'.Inc e x := by
    refine hexP.of_isClosedSubgraph_of_mem hP'P.isClosedSubgraph ?_
    grind only [!incVertexSet_subset, = mem_diff, = subset_def]
  have heq := hf.edge_unique hexP'
  grind only

/-- Berge's Theorem: A matching is maximal iff there do not exist any augmenting paths.
-/
lemma berge [G.Loopless] [G.EdgeFinite] (hM : G.IsMatching M) :
    ¬ G.IsMaxMatching M ↔ ∃ P, G.IsAugmenter M P := by
  refine ⟨?_, ?_⟩
  · intro h_notMax
    simp [isMaxMatching_iff] at h_notMax
    specialize h_notMax hM
    obtain ⟨M', hM', hlt⟩ := h_notMax
    exact exists_isAugmenter_of_matching_encard_lt hM hM' hlt
  intro ⟨P, hP⟩ hM_max
  have _ : P.Loopless := ‹G.Loopless›.mono hP.le
  exact hM_max.not_isAugmenter _ hP

end Graph
