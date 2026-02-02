import Matroid.Graph.Forest

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H C : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α} {d : ℕ}

open Set WList

namespace Graph


/-! ### Maximum degree -/

/-- A nontrivial connected graph with max degree at most two is loopless. -/
lemma Connected.loopless_of_maxDegreeLE_two (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
    (hnt : V(G).Nontrivial) : G.Loopless where
  not_isLoopAt e x h := by
    have := hmax.locallyFinite
    obtain ⟨f, y, hf, hne⟩ := hG.exists_isLink_of_mem hnt h.vertex_mem
    have hle := hmax.degree_le x
    have h1 : 1 ≤ {e | G.IsLoopAt e x}.ncard :=
      Nat.one_le_iff_ne_zero.2 <| ncard_ne_zero_of_mem h G.finite_setOf_isLoopAt
    have h2 : 1 ≤ {e | G.IsNonloopAt e x}.ncard :=
      Nat.one_le_iff_ne_zero.2 <| ncard_ne_zero_of_mem ⟨y, hne, hf⟩ G.finite_setOf_isNonloopAt
    rw [degree_eq_ncard_add_ncard] at hle
    linarith

-- lemma Connected.simple_of_maxDegreeLE_two (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
--     (hcard : 3 ≤ V(G).encard) : G.Simple := by
--   sorry

/-! ### Paths -/

def IsPathGraph (G : Graph α β) : Prop := ∃ P, G.IsPath P ∧ G = P.toGraph

lemma IsPathGraph.connected (hP : H.IsPathGraph) : H.Connected := by
  obtain ⟨P', hP', rfl⟩ := hP
  exact hP'.isWalk.toGraph_connected

lemma IsCycleGraph.connected (hC : C.IsCycleGraph) : C.Connected := by
  obtain ⟨C', hC', hV, hE⟩ := by rwa [isCycleGraph_iff_toGraph_isCyclicWalk] at hC
  exact hC'.isWalk.toGraph_connected

lemma IsPathGraph.finite (hP : G.IsPathGraph) : G.Finite where
  vertexSet_finite := by
    obtain ⟨P, hP, rfl⟩ := hP
    simp
  edgeSet_finite := by
    obtain ⟨P, hP, rfl⟩ := hP
    simp

/-- If `v` and `w` are leaves of a connected graph `G` with maximum degree at most `2`,
then `G` is a path from `v` to `w`. -/
lemma Connected.exists_isPath_of_leaves [G.EdgeFinite] (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
    (hv : G.IsLeaf v) (hw : G.IsLeaf w) (hne : v ≠ w) :
    ∃ P, G.IsPath P ∧ P.first = v ∧ P.last = w ∧ G = P.toGraph := by
  have hlf := hmax.locallyFinite
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.connBetween hv.mem hw.mem).exists_isPath
  refine ⟨P, hP, rfl, rfl, Eq.symm ?_⟩
  refine eq_of_le_of_forall_degree_ge hG hP.isWalk.toGraph_le (by simp) fun x hx ↦ ?_
  have hPne : P.Nonempty := by rwa [first_ne_last_iff hP.nodup] at hne
  obtain rfl | hne0 := eq_or_ne x P.first
  · rw [(hP.first_isLeaf_toGraph hPne).degree, hv.degree]
  obtain rfl | hne1 := eq_or_ne x P.last
  · rw [(hP.last_isLeaf_toGraph hPne).degree, hw.degree]
  rw [hP.degree_toGraph_eq_two (by simpa using hx) hne0 hne1]
  apply hmax.degree_le

/-- Every finite non-regular connected graph with max degree at most `2` is a path. -/
lemma Connected.isPathGraph_of_maxDegreeLE [G.EdgeFinite] (hG : G.Connected)
    (hmax : G.MaxDegreeLE 2) (hv : ∃ v ∈ V(G), G.degree v ≤ 1) : G.IsPathGraph := by
  have := hG.finite
  simp_rw [Nat.le_one_iff_eq_zero_or_eq_one, degree_eq_one_iff] at hv
  obtain ⟨v, hvG, h0 | hv⟩ := hv
  · obtain hV | hnt := eq_singleton_or_nontrivial hvG
    · exact ⟨nil v, by simpa, Eq.symm <|
        hG.eq_of_le_of_forall_degree_ge (by simpa) (by simp) (by simpa)⟩
    simpa [h0] using (hG.degreePos hnt).one_le_degree hvG
  obtain ⟨w, hwv, hw⟩ : ∃ w ≠ v, G.IsLeaf w := by
    simp_rw [← degree_eq_one_iff]
    by_contra! hcon
    have h2 : ∀ w ∈ V(G), w ≠ v → G.degree w = 2 := by
      refine fun w hw hwv ↦ (hmax.degree_le w).antisymm <| not_lt.1 fun hlt ↦ hcon _ hwv ?_
      have := (hG.degreePos hv.vertexSet_nontrivial).one_le_degree hw
      omega
    have hhs := G.handshake_degree_subtype
    rw [← finsum_mem_add_diff (s := {v}) (by simpa using hv.mem) (by simp)] at hhs
    simp only [mem_singleton_iff, finsum_cond_eq_left, hv.degree] at hhs
    rw [finsum_mem_congr (s := V(G) \ {v}) rfl (g := 2) (by simpa)] at hhs
    simp_rw [Pi.ofNat_apply, finsum_mem_const, smul_eq_mul] at hhs
    have hmod := congr_arg (fun x ↦ x % 2) hhs
    simp at hmod
  obtain ⟨P, hP, rfl, rfl, rfl⟩ := hG.exists_isPath_of_leaves hmax hv hw hwv.symm
  exact ⟨P, hP, rfl⟩

/-- Every finite `2`-regular connected graph is a cycle. -/
lemma Connected.isCycleGraph_of_regular [G.EdgeFinite] (hG : G.Connected) (hreg : G.Regular 2) :
    G.IsCycleGraph := by
  have hE := (hreg.degreePos (by simp)).edgeSet_nonempty hG.nonempty
  by_cases hF : G.IsForest
  · obtain ⟨x, hx⟩ := hF.exists_isLeaf hE
    simpa [hx.degree] using hreg.degree hx.mem
  obtain ⟨C, hC : G.IsCyclicWalk C⟩ := by simpa [isForest_iff_not_isCyclicWalk] using hF
  rw [← hG.eq_of_le_of_forall_degree_ge hC.isWalk.toGraph_le (by simp) ?_]
  · exact hC.toGraph_isCycleGraph
  simp +contextual only [toGraph_vertexSet, mem_vertexSet_iff, hC.toGraph_regular.degree]
  exact fun x hxC ↦ (hreg.degree (hC.isWalk.vertex_mem_of_mem hxC)).le

/-- Every finite connected graph with maximum degree `2` is a path or a cycle. -/
lemma Connected.isPathGraph_or_isCycleGraph_of_maxDegreeLE [G.EdgeFinite] (hG : G.Connected)
    (hmax : G.MaxDegreeLE 2) : G.IsPathGraph ∨ G.IsCycleGraph := by
  obtain h | h := exists_or_forall_not (fun v ↦ v ∈ V(G) ∧ G.degree v ≤ 1)
  · exact .inl <| hG.isPathGraph_of_maxDegreeLE hmax h
  exact .inr <| hG.isCycleGraph_of_regular <| regular_iff.2
    fun v hv ↦ (hmax.degree_le v).antisymm <| by aesop

lemma IsCompOf.isPathGraph_or_isCycleGraph_of_maxDegreeLE [G.EdgeFinite] (hH : H.IsCompOf G)
    (hmax : G.MaxDegreeLE 2) : H.IsPathGraph ∨ H.IsCycleGraph := by
  have hHFin : H.EdgeFinite := edgeFinite_of_le hH.le
  exact hH.connected.isPathGraph_or_isCycleGraph_of_maxDegreeLE <| hmax.mono hH.le

lemma IsCycleGraph.isCompOf_of_maxDegreeLE (hC : C.IsCycleGraph) (hmax : G.MaxDegreeLE 2)
    (hle : C ≤ G) : C.IsCompOf G := by
  refine hC.connected.IsCompOf_of_isClosedSubgraph ⟨hle, fun e x hex hxC ↦ ?_⟩
  have := hmax.locallyFinite
  have : E(C, x) = E(G, x) := by
    refine incEdges_of_degree hle (le_antisymm (degree_mono hle _) ?_)
    rw [hC.regular_two |>.degree hxC]
    exact hmax.degree_le x
  rw [Set.ext_iff] at this
  exact this e |>.mpr hex |>.edge_mem
