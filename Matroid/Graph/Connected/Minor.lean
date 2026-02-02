import Matroid.Graph.Connected.Basic
import Matroid.Graph.Minor.Defs

open Set Function Nat WList

variable {α α' β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R' C : Set β} {W P Q : WList α β} {φ : α → α}

namespace Graph

lemma ConnBetween.map (f : α → α') (h : G.ConnBetween x y) :
    (f ''ᴳ G).ConnBetween (f x) (f y) := by
  obtain ⟨W, hW, rfl, rfl⟩ := h
  exact ⟨W.map f, hW.map f, by simp, by simp⟩

lemma Preconnected.map (f : α → α') (h : G.Preconnected) : (f ''ᴳ G).Preconnected := by
  intro x' y' hx' hy'
  obtain ⟨x, hx, rfl⟩ := by simpa [map_vertexSet] using hx'
  obtain ⟨y, hy, rfl⟩ := by simpa [map_vertexSet] using hy'
  exact (h _ _ hx hy).map f

@[simp]
lemma Connected.map (f : α → α') (h : G.Connected) : (f ''ᴳ G).Connected := by
  obtain ⟨⟨v, hv⟩, hpre⟩ := connected_iff.mp h
  exact connected_iff.mpr ⟨⟨f v, by simpa [map_vertexSet] using Set.mem_image_of_mem f hv⟩,
      hpre.map f⟩

/-! ### Pulling separators back along a map -/

lemma IsSep.of_map {f : α → α'} {S : Set α'} (hS : (f ''ᴳ G).IsSep S) :
    G.IsSep (V(G) ∩ f ⁻¹' S) := by
  refine ⟨inter_subset_left, ?_⟩
  by_contra hcon
  have hcon' : (G - (f ⁻¹' S)).Connected := by
    -- deleting vertices outside `V(G)` has no effect
    simpa [vertexDelete_vertexSet_inter] using hcon
  have : ((f ''ᴳ G) - S).Connected := by
    simpa [map_vertexDelete_preimage] using (Connected.map (G := G - (f ⁻¹' S)) f hcon')
  exact hS.not_connected this

lemma IsSep.of_contract (hφ : (G ↾ C).connPartition.IsRepFun φ) (hS : (G /[φ, C]).IsSep S) :
    G.IsSep (φ ⁻¹' S) where
  subset_vx v hvS := by
    obtain ⟨x, hx, hvx⟩ := by simpa using hS.subset_vx (mem_preimage.mp hvS)
    rw [hφ.apply_eq_apply_iff_rel (by simpa)] at hvx
    simpa using hvx.right_mem
  not_connected hcon := by
    absurd hS.not_connected
    have hsc : G.IsContractClosed (φ : α → α) C := hφ.isContractClosed
    have hmap : ((φ ''ᴳ G) - S).Connected := by
      simpa [map_vertexDelete_preimage] using hcon.map φ
    have hdel : (((φ ''ᴳ G) - S) ＼ C).Connected := by
      rw [← edgeDelete_inter_edgeSet]
      refine (edgeDelete_connected_iff_of_forall_isLoopAt ?hloops).2 hmap
      intro e he
      simpa using hsc.exists_isLoopAt_map_vertexDelete_of_mem S he
    simpa [contract] using hdel

/-! ### Connectivity bounds under contracting a single edge -/

private lemma IsLink.repFun_preimage_subset (hl : G.IsLink e x y) (S : Set α) [DecidableEq α] :
    hl.repFun ⁻¹' S ⊆ insert y S := by
  intro v hv
  obtain rfl | hvy := eq_or_ne v y
  · simp
  right
  -- if `v ≠ y`, then `hl.repFun v = v`
  have : hl.repFun v ∈ S := by
    simpa [Set.mem_preimage] using hv
  exact hl.repFun_apply_of_ne hvy ▸ this

private lemma IsLink.encard_preimage_le (hl : G.IsLink e x y) (S : Set α) [DecidableEq α] :
    (hl.repFun ⁻¹' S).encard ≤ S.encard + 1 := by
  have hsub : (hl.repFun ⁻¹' S) ⊆ insert y S := hl.repFun_preimage_subset S
  calc
    (hl.repFun ⁻¹' S).encard ≤ (insert y S).encard :=
      encard_le_encard hsub
    _ ≤ S.encard + 1 := by
      simpa using (encard_insert_le _ _)

lemma ConnGE.contract_isLink {n : ℕ} (hG : G.ConnGE (n + 1)) (hl : G.IsLink e x y) :
    hl.contract.ConnGE n where
  le_cut S hS := by
    classical
    simpa using (hG.le_cut <| (hl.contract' ▸ hS).of_contract hl.isRepFun).trans
    <| hl.encard_preimage_le S
  le_card := by
    obtain h1 | h2 := hG.le_card
    · left
      apply h1.anti
      simp [hl.left_mem, insert_subset_iff]
    right
    rw [IsLink.contract_vertexSet]
    apply lt_of_lt_of_le ?_ <| encard_le_encard (subset_insert ..)
    rw [encard_diff_singleton_of_mem hl.right_mem]
    enat_to_nat!
    omega

/-!
### Endpoint separators from bad single-edge contractions

If contracting a nonloop edge destroys `ConnGE (n+1)` (and the contracted graph still has at least
`n+2` vertices), then there is a separator in `G` of size at most `n+1` containing both endpoints
of the edge.
-/

lemma ConnGE.exists_isSepSet_endpoints_of_not_connGE_contract_isLink {n : ℕ} (hG : G.ConnGE (n + 1))
    (hl : G.IsLink e x y) (hnV : n + 1 < V(hl.contract).encard)
    (hbad : ¬ hl.contract.ConnGE (n + 1)) :
    ∃ T, G.IsSep T ∧ T.encard ≤ (n + 1) ∧ x ∈ T ∧ y ∈ T := by
  classical
  obtain ⟨S, hSsep, hScard⟩ := exists_isSepSet_encard_le_of_not_connGE hnV hbad
  have hTsep : G.IsSep (hl.repFun ⁻¹' S) := (hl.contract' ▸ hSsep).of_contract hl.isRepFun
  rw [hl.repFun_preimage] at hTsep
  split_ifs at hTsep with hxS; swap
  · simpa using hG.le_cut hTsep |>.trans (encard_le_encard diff_subset) |>.trans hScard
  refine ⟨_, hTsep, ?_, by simp [hxS], by simp⟩
  exact (encard_insert_le ..).trans <| ENat.add_one_le_add_one_iff.mpr hScard

theorem exists_contract_connGE_three [G.Finite] (hG : G.ConnGE 3) (hV : 5 ≤ V(G).encard) :
    ∃ (e : β) (x y : α) (h : G.IsLink e x y), h.contract.ConnGE 3 := by
  -- If the conclusion fails, then every edge-contraction is "bad".
  by_contra! hbad
  letI P := fun C : Graph α β ↦ ∃ (x y z : α), G.IsSep {x, y, z} ∧
    C.IsCompOf (G - ({x, y, z} : Set α)) ∧ G.Adj x y ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z
  have hexP : ∃ C : Graph α β, P C := by
    -- Pick a nonloop edge; by `hbad`, contracting it destroys `ConnGE 3`,
    -- so we get a small separator containing its endpoints.
    obtain ⟨e, x, hnl⟩ := hG.exists_isNonloopAt (by decide : 2 ≤ 3)
    set y : α := hnl.inc.other
    have hl : G.IsLink e x y := hnl.inc.isLink_other
    have hxy : x ≠ y := by simpa [y] using hnl.other_ne.symm
    have hAdj : G.Adj x y := hl.adj
    have hnV : ((3 : ℕ) : ℕ∞) < V(hl.contract).encard := by
      rw [hl.contract_vertexSet_of_ne hxy, encard_diff_singleton_of_mem hl.right_mem]
      enat_to_nat!
      omega
    obtain ⟨T, hTsep, hTcard, hxT, hyT⟩ :=
      hG.exists_isSepSet_endpoints_of_not_connGE_contract_isLink hl hnV (hbad e x y hl); clear hnV

    -- Reduce the small separator `T` to a triple `{x, y, z}` (allowing repetitions).
    norm_num1 at hTcard
    replace hTcard : T.encard = 3 := hTcard.antisymm <| hG.le_cut hTsep
    have hT'card : (T \ ({x, y} : Set α)).encard = 1 := by
      rw [← diff_singleton_diff_eq, encard_diff_singleton_of_mem (by simpa [hxy.symm]),
      encard_diff_singleton_of_mem hxT, hTcard]
      rfl
    obtain ⟨z, hz⟩ := encard_eq_one.mp hT'card
    obtain rfl : (T : Set α) = ({x, y, z} : Set α) := by grind
    clear hxT hyT

    simp only [mem_insert_iff, mem_singleton_iff, true_or, insert_diff_of_mem, or_true,
      sdiff_eq_left, disjoint_singleton_left, not_or, ← ne_eq] at hz
    -- Pick a vertex outside the separator and take its walkable component.
    have hlt : ({x, y, z} : Set α).encard < V(G).encard := by
      rw [hTcard]
      exact (by decide : (3 : ℕ∞) < 5).trans_le hV
    obtain ⟨w, hw⟩ := diff_nonempty_of_encard_lt_encard (s := ({x, y, z} : Set α)) (t := V(G)) hlt
    refine ⟨(G - ({x, y, z} : Set α)).walkable w, ⟨x, y, z, ?_, walkable_isCompOf hw, ?_⟩⟩
    · simpa using hTsep
    · simpa [y, hxy, hz.1.symm, hz.2.symm] using hAdj
  obtain ⟨C, ⟨x, y, z, hMsep, hC, hxy, hxyne, hzxne, hzyne⟩, hMin⟩ :=
    exists_minimalFor_of_wellFoundedLT P (fun G ↦ V(G).encard) hexP; clear hexP

  -- 1. `{x, y, z}` is a minimum separator of `G` as `G` is 3-connected.
  replace hMsep : G.IsMinSep {x, y, z} := {
    toIsSep := hMsep
    minimal A hA := by
      refine le_trans ?_ (hG.le_cut hA)
      rw [(by norm_num : ((3: ℕ) : ℕ∞) = 1 + 1 + 1)]
      refine (encard_insert_le _ _).trans <| ENat.add_one_le_add_one_iff.mpr ?_
      refine (encard_insert_le _ _).trans <| ENat.add_one_le_add_one_iff.mpr ?_
      simp}
  obtain ⟨w, hwC, f, hzw⟩ := hMsep.exists_adj_of_isCompOf_vertexDelete hC (x := z) (by simp)
    (by simp); clear hMsep
  -- `z ≠ w` since `z ∉ C` and `w ∈ C`
  have hzwne : z ≠ w := by
    rintro rfl
    obtain ⟨-, -, -, hzC⟩ := by simpa [subset_diff] using vertexSet_mono hC.le
    exact hzC hwC

  -- 2. Every edge is bad. Hence, there is a 3-sep that contains `w` and `z`.
  have := hG.exists_isSepSet_endpoints_of_not_connGE_contract_isLink hzw ?_ (hbad _ _ _ hzw)
  swap
  · rw [hzw.contract_vertex_encard_eq_add_one hzwne] at hV
    enat_to_nat! <;> omega
  obtain ⟨T, hTsep, hTcard, hzT, hwT⟩ := this; clear hbad hV

  -- 3. Either `x` or `y` is not in `T`. WLOG, assume `x ∉ T`.
  norm_num1 at hTcard
  replace hTcard : T.encard = 3 := hTcard.antisymm <| hG.le_cut hTsep
  have hTdiff : (T \ {w, z}).encard = 1 := by
    rw [← diff_singleton_diff_eq, encard_diff_singleton_of_mem (by simpa [hzwne] using hzT: z ∈ _),
      encard_diff_singleton_of_mem hwT, hTcard]
    rfl
  obtain ⟨w', hw'⟩ := encard_eq_one.mp hTdiff
  obtain rfl : T = ({w, z, w'} : Set α) := by grind
  simp_all only [mem_insert_iff, mem_singleton_iff, true_or, or_true, hzwne.symm, false_or,
    encard_singleton, or_false, insert_diff_of_mem, sdiff_eq_left, disjoint_singleton_left, not_or,
    ← ne_eq]

  have hor : x ∉ ({w, z, w'} : Set α) ∨ y ∉ ({w, z, w'} : Set α) := by
    obtain ⟨-, hxC, hyC, hzC⟩ := by simpa [subset_diff] using vertexSet_mono hC.le
    by_contra! h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    obtain ⟨(rfl | rfl | rfl), (rfl | rfl | rfl)⟩ := h <;> tauto
  clear hxyne hzxne hzyne
  wlog hxnT : x ∉ ({w, z, w'} : Set α)
  · have hh : ({y, x, z} : Set α) = {x, y, z} := insert_comm y x {z}
    exact this hG C y x z w f w' hMin (hh ▸ hC) hxy.symm hwC hzw hzwne hTsep hTcard hw'
      hor.symm (hor.resolve_left hxnT)
  clear hor

  -- 3.a. `x` and `y` is adjacent in `G - T` and therefore connected in `G - T`.
  have hxy' : y ∉ ({w, z, w'} : Set α) → (G - ({w, z, w'} : Set α)).Adj x y := by
    simp +contextual [hxy, hxnT]
  -- 4. This 3-sep, `T`, is also a minimum separator of `G` as `G` is 3-connected.
  replace hTsep : G.IsMinSep ({w, z, w'} : Set α) := {
    toIsSep := hTsep
    minimal A hA := hTcard ▸ (hG.le_cut hA)}
  -- 5. There is some `v` in `G - T` that is not connected to `x` and therefore `y`.
  have := hTsep.not_connected
  rw [connected_iff, not_and] at this
  obtain ⟨v, hv, hvx⟩ := exists_not_connBetween_of_not_preconnected (this ⟨x, hxy.left_mem, hxnT⟩)
    ⟨hxy.left_mem, hxnT⟩
  -- 6. In the component containing `v`, there is some `u` that is adjacent to `w`.
  obtain ⟨u, huv, hwuadj⟩ := hTsep.exists_adj_of_isCompOf_vertexDelete (walkable_isCompOf hv)
    (by simp : w ∈ _) (vertexSet_finite.subset hTsep.subset_vx)
  clear this hTcard hv
  -- 7. `u ∈ C` since `w ∈ C`, `G.Adj w u`, `u ∉ T` and `u ∉ {x, y, z}`.
  have huT := (by exact huv : (G - ({w, z, w'} : Set α)).ConnBetween v u).right_mem
  have hxuconn : ¬ (G - ({w, z, w'} : Set α)).ConnBetween x u :=
    fun hxu ↦ hvx <| hxu.trans (by exact huv : (G - ({w, z, w'} : Set α)).ConnBetween v u).symm
  -- 8. The entire `(G - T).walkable u` must be strictly contained in `C`.
  have hC' := walkable_isCompOf huT
  have h := hC'.of_vertexDelete (S := {x, y, z}) <| by
    rw [connBetween_comm] at hxuconn
    simp only [disjoint_insert_right, ← connBetween_iff_mem_walkable_of_mem, hxuconn,
      not_false_eq_true, disjoint_singleton_right, vertexDelete_vertexSet, mem_diff, mem_insert_iff,
      mem_singleton_iff, true_or, or_true, not_true_eq_false, and_false,
      not_connBetween_of_right_not_mem, and_true, true_and]
    by_cases hy : y ∈ ({w, z, w'} : Set α)
    · simp [hy]
    exact fun h ↦ hxuconn <| h.trans (hxy' hy |>.connBetween).symm
  replace h := h.eq_walkable_of_mem_walkable (x := u) (by simpa using huT)
  rw [vertexDelete_vertexDelete_comm] at h
  have hC'C : (G - ({w, z, w'} : Set α)).walkable u ≤ C := by
    suffices huC : u ∈ V(C) by
      rw [hC.eq_walkable_of_mem_walkable huC, h]
      exact walkable_mono vertexDelete_le u
    refine hC.isClosedSubgraph.adj_of_adj_of_mem hwC (y := u) ?_ |>.right_mem
    rw [vertexDelete_adj_iff]
    use hwuadj, (vertexSet_mono hC.le) hwC |>.2
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
    · simp [hxnT, hxy.left_mem] at hxuconn
    · exact hxuconn <| hxy' huT.2 |>.connBetween
    · exact huT.2 (by simp)
  have hsub : V((G - ({w, z, w'} : Set α)).walkable u) ⊂ V(C) := by
    refine ssubset_of_ne_of_subset (fun hVeq ↦ ?_) (vertexSet_mono hC'C)
    rw [← hVeq] at hwC
    simpa using vertexSet_mono hC'.le hwC

  -- 9. Therefore, `T` and `(G - T).walkable u` is a smaller component than `{x, y, z}` and `C`.
  -- contradiction!
  have hlt := Finite.encard_lt_encard (vertexSet_finite.subset <| vertexSet_mono hC'.le) hsub
  refine hlt.ne' <| hMin (j := (G - ({w, z, w'} : Set α)).walkable u) ?_ hlt.le |>.antisymm hlt.le
  use w, z, w', hTsep.toIsSep, hC', ⟨f, hzw.symm⟩, hzwne.symm, hw'.1.symm, hw'.2.symm

-- #print axioms exists_contract_connGE_three

end Graph
