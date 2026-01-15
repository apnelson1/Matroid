import Matroid.Graph.Connected.Basic
import Matroid.Graph.Minor.Defs

open Set Function Nat WList

variable {α α' β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R' C : Set β} {W P Q : WList α β}

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

lemma IsSepSet.of_map {f : α → α'} {S : Set α'} (hS : (f ''ᴳ G).IsSepSet S) :
    G.IsSepSet (V(G) ∩ f ⁻¹' S) := by
  refine ⟨inter_subset_left, ?_⟩
  by_contra hcon
  have hcon' : (G - (f ⁻¹' S)).Connected := by
    -- deleting vertices outside `V(G)` has no effect
    simpa [vertexDelete_vertexSet_inter] using hcon
  have : ((f ''ᴳ G) - S).Connected := by
    simpa [map_vertexDelete_preimage] using (Connected.map (G := G - (f ⁻¹' S)) f hcon')
  exact hS.not_connected this

lemma IsSepSet.of_contract (φ : (G ↾ C).connPartition.RepFun) (hS : (G /[φ, C]).IsSepSet S) :
    G.IsSepSet (φ ⁻¹' S) := by
  have hSV : S ⊆ V(G) :=
    (hS.subset_vx).trans (Graph.contract_vertex_mono (H := G) (C := C) φ)
  have hpreV : φ ⁻¹' S ⊆ V(G) := by
    intro v hv
    by_contra hvG
    have hvG' : v ∉ (G ↾ C).connPartition.supp := by
      -- `supp = V(G)` for `connPartition` on `G ↾ C`
      simpa [connPartition_supp, edgeRestrict_vertexSet] using hvG
    have hφv : φ v = v := φ.apply_eq_self_of_notMem v hvG'
    have : v ∈ S := by
      -- outside `V(G)`, `φ` is the identity
      simpa [hφv] using hv
    exact hvG (hSV this)
  refine ⟨hpreV, fun hcon ↦ ?_⟩
  have hcon' : (G - φ ⁻¹' S).Connected := by
    simpa using hcon
  have hmap : ((φ ''ᴳ G) - S).Connected := by
    simpa [map_vertexDelete_preimage] using (Connected.map (G := G - φ ⁻¹' S) φ hcon')

  have hsc : G.SoundContract (φ : α → α) C :=
    SoundContract.of_connPartition_repFun (G := G) (C := C) φ
  have hloops : ∀ e ∈ (C ∩ E((φ ''ᴳ G) - S)), ∃ x, ((φ ''ᴳ G) - S).IsLoopAt e x := by
    intro e he
    simpa using (_root_.Graph.SoundContract.exists_isLoopAt_map_vertexDelete_of_mem
      (G := G) (φ := (φ : α → α)) (C := C) hsc S he)

  have hdel : (((φ ''ᴳ G) - S) ＼ C).Connected := by
    rw [← edgeDelete_inter_edgeSet]
    exact (edgeDelete_connected_iff_of_forall_isLoopAt hloops).2 hmap

  have : ((G /[φ, C]) - S).Connected := by
    simpa [Graph.contract, contract, edgeDelete_vertexDelete] using hdel
  exact hS.not_connected this

/-! ### Connectivity bounds under contracting a single edge -/

private lemma IsLink.repFun_preimage_subset (hl : G.IsLink e x y) (S : Set α) :
    hl.repFun ⁻¹' S ⊆ insert y S := by
  intro v hv
  obtain rfl | hvy := eq_or_ne v y
  · simp
  right
  -- if `v ≠ y`, then `hl.repFun v = v`
  have : hl.repFun v ∈ S := by
    simpa [Set.mem_preimage] using hv
  simpa [hl.repFun_apply_of_ne hvy] using this

private lemma IsLink.encard_preimage_le (hl : G.IsLink e x y) (S : Set α) :
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
    have hS' : (G /[(hl.repFun : α → α), ({e} : Set β)]).IsSepSet S := by
      simpa [hl.contract'] using hS
    have hSepG : G.IsSepSet (hl.repFun ⁻¹' S) :=
      hS'.of_contract hl.repFun
    have hcut : (n : ℕ∞) + 1 ≤ (hl.repFun ⁻¹' S).encard := by
      simpa using hG.le_cut hSepG
    have hle' : (hl.repFun ⁻¹' S).encard ≤ S.encard + 1 := hl.encard_preimage_le S
    have hcut' : (n : ℕ∞) + 1 ≤ S.encard + 1 := le_trans hcut hle'
    exact (ENat.add_one_le_add_one_iff).1 hcut'
  le_card := by
    classical
    have hsubV : V(hl.contract) ⊆ V(G) := by
      intro v hv
      have hv' : v = x ∨ v ∈ (V(G) \ ({y} : Set α)) := by
        simpa [IsLink.contract, Set.mem_insert_iff] using hv
      rcases hv' with rfl | hv'
      · exact hl.left_mem
      exact hv'.1
    have hVle : V(G).encard ≤ V(hl.contract).encard + 1 := by
      have hsub : V(G) ⊆ V(hl.contract) ∪ ({y} : Set α) := by
        intro v hv
        obtain rfl | hvy := eq_or_ne v y
        · simp
        · left
          have : v ∈ (V(G) \ ({y} : Set α)) := by
            exact ⟨hv, by simpa [Set.mem_singleton_iff] using hvy⟩
          -- everything in `V(G) \ {y}` lies in the contracted vertex set
          have : v ∈ V(hl.contract) := by
            simp [IsLink.contract, this]
          exact this
      calc
        V(G).encard ≤ (V(hl.contract) ∪ ({y} : Set α)).encard := encard_le_encard hsub
        _ ≤ V(hl.contract).encard + ({y} : Set α).encard := encard_union_le _ _
        _ = V(hl.contract).encard + 1 := by simp
    rcases hG.le_card with hss | hlt
    · left
      intro a ha b hb
      exact hss (hsubV ha) (hsubV hb)
    · right
      have hlt' : (n : ℕ∞) + 1 < V(G).encard := by simpa using hlt
      have : (n : ℕ∞) + 1 < V(hl.contract).encard + 1 := lt_of_lt_of_le hlt' hVle
      exact (ENat.add_one_lt_add_one_iff).1 this

/-!
### Endpoint separators from bad single-edge contractions

If contracting a nonloop edge destroys `ConnGE (n+1)` (and the contracted graph still has at least
`n+2` vertices), then there is a separator in `G` of size at most `n+1` containing both endpoints
of the edge.
-/

lemma ConnGE.exists_isSepSet_endpoints_of_not_connGE_contract_isLink
    {n : ℕ} (hG : G.ConnGE (n + 1)) (hl : G.IsLink e x y) (hxy : x ≠ y)
    (hnV : ((n + 1 : ℕ) : ℕ∞) < V(hl.contract).encard) (hbad : ¬ hl.contract.ConnGE (n + 1)) :
    ∃ T, G.IsSepSet T ∧ T.encard ≤ (n + 1) ∧ x ∈ T ∧ y ∈ T := by
  classical
  -- an `n`-separator in the contracted graph
  obtain ⟨S, hSsep, hScard⟩ :=
    exists_isSepSet_encard_le_of_not_connGE hnV hbad

  -- pull it back to `G`
  have hSsep' : (G /[(hl.repFun : α → α), ({e} : Set β)]).IsSepSet S := by
    simpa [hl.contract'] using hSsep
  have hTsep : G.IsSepSet (hl.repFun ⁻¹' S) := IsSepSet.of_contract hl.repFun hSsep'

  -- show `x ∈ S`; otherwise we get an `n`-separator of `G`, contradicting `ConnGE (n+1)`
  have hxS : x ∈ S := by
    by_contra hxS
    have hpre : hl.repFun ⁻¹' S ⊆ S := by
      intro v hv
      obtain rfl | hvy := eq_or_ne v y
      · have : x ∈ S := by
          have : hl.repFun v ∈ S := by simpa [Set.mem_preimage] using hv
          simpa [hl.repFun_apply_right] using this
        exact (hxS this).elim
      have hv' : hl.repFun v = v := hl.repFun_apply_of_ne hvy
      have hvS : hl.repFun v ∈ S := by
        simpa [Set.mem_preimage] using hv
      simpa [hv'] using hvS
    have hle : (hl.repFun ⁻¹' S).encard ≤ n :=
      (encard_le_encard hpre).trans hScard
    have hge : ((n + 1 : ℕ) : ℕ∞) ≤ (hl.repFun ⁻¹' S).encard := by
      simpa using hG.le_cut hTsep
    have hnlt : (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast (Nat.lt_succ_self n)
    exact hge.not_gt (hle.trans_lt hnlt)

  refine ⟨hl.repFun ⁻¹' S, hTsep, ?_, ?_, ?_⟩
  · have hle : (hl.repFun ⁻¹' S).encard ≤ S.encard + 1 := hl.encard_preimage_le S
    have hSle : S.encard + 1 ≤ (n + 1) := by
      -- `S.encard ≤ n` implies `S.encard + 1 ≤ n + 1`
      have : S.encard ≤ n := hScard
      enat_to_nat! <;> omega
    exact hle.trans hSle
  · have hxfix : hl.repFun x = x := by simp
    simpa [Set.mem_preimage, hxfix] using hxS
  · -- `hi.repFun y = x`, so `y ∈ preimage S` iff `x ∈ S`
    have hrep : hl.repFun y = x := by simp
    have : hl.repFun y ∈ S := by simpa [hrep] using hxS
    simpa [Set.mem_preimage] using this

lemma ConnGE.connected {n : ℕ} (hG : G.ConnGE n) (hn : 1 ≤ n) : G.Connected := by
  have h1 : G.ConnGE 1 := hG.anti_right hn
  simpa [connGE_one_iff] using h1

lemma Preconnected.exists_isNonloopAt_of_nontrivial (hG : G.Preconnected)
    (hnt : V(G).Nontrivial) : ∃ e x, G.IsNonloopAt e x := by
  obtain ⟨x, hx⟩ := hnt.nonempty
  obtain ⟨e, y, hxy, hne⟩ := hG.exists_isLink_of_mem hnt hx
  exact ⟨e, x, ⟨y, hne, hxy⟩⟩

lemma ConnGE.exists_isNonloopAt {k : ℕ} (hG : G.ConnGE k) (hk : 2 ≤ k) :
    ∃ e x, G.IsNonloopAt e x := by
  have hconn : G.Connected := hG.connected (show 1 ≤ k from (by decide : 1 ≤ 2).trans hk)
  have hle : (k : ℕ∞) ≤ V(G).encard := by simpa using hG.le_cut vertexSet_isSepSet
  have hnt : V(G).Nontrivial := by
    exact two_le_encard_iff_nontrivial.mp <| (by norm_cast : (2 : ℕ∞) ≤ k).trans hle
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨e, y, hxy, hne⟩ := hconn.exists_isLink_of_mem hnt hx
  exact ⟨e, x, ⟨y, hne, hxy⟩⟩

theorem exists_contract_connGE_three [G.Finite] (hG : G.ConnGE 3) (hV : 5 ≤ V(G).encard) :
    ∃ (e : β) (x y : α) (h : G.IsLink e x y), h.contract.ConnGE 3 := by
  obtain h4conn | h4nconn := em (G.ConnGE 4)
  · -- if `G` is 4-connected, then we can contract any edge to get a 3-connected graph
    obtain ⟨e, x, hx⟩ := ConnGE.exists_isNonloopAt h4conn (by decide : 2 ≤ 4)
    refine ⟨e, x, hx.inc.other, hx.inc.isLink_other, ?_⟩
    simpa using h4conn.contract_isLink hx.inc.isLink_other

  -- If the conclusion fails, then every edge-contraction is "bad".
  by_contra! hbad
  letI P := fun C : Graph α β ↦ ∃ (x y z : α), G.IsSepSet {x, y, z} ∧
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
      hG.exists_isSepSet_endpoints_of_not_connGE_contract_isLink hl hxy hnV (hbad e x y hl)

    -- Reduce the small separator `T` to a triple `{x, y, z}` (allowing repetitions).
    norm_num at hTcard
    replace hTcard : T.encard = 3 := hTcard.antisymm <| hG.le_cut hTsep
    have hT'card : (T \ ({x, y} : Set α)).encard = 1 := by
      rw [← diff_singleton_diff_eq, encard_diff_singleton_of_mem (by simpa [hxy.symm]),
      encard_diff_singleton_of_mem hxT, hTcard]
      rfl
    obtain ⟨z, hz⟩ := encard_eq_one.mp hT'card
    obtain rfl : (T : Set α) = ({x, y, z} : Set α) := by
      ext t
      obtain rfl | hnex := eq_or_ne t x
      · simpa
      obtain rfl | hney := eq_or_ne t y
      · simpa
      have htTR : (t ∈ T) ↔ (t ∈ (T \ ({x, y} : Set α))) := by
        simp [hnex, hney]
      rw [htTR, hz]
      simp [hnex, hney]

    simp only [mem_insert_iff, mem_singleton_iff, true_or, insert_diff_of_mem, or_true,
      sdiff_eq_left, disjoint_singleton_left, not_or, ← ne_eq] at hz
    clear hxT hyT
    -- Pick a vertex outside the separator and take its walkable component.
    have hlt : ({x, y, z} : Set α).encard < V(G).encard := by
      rw [hTcard]
      exact (by decide : (3 : ℕ∞) < 5).trans_le hV
    obtain ⟨w, hw⟩ := diff_nonempty_of_encard_lt_encard (s := ({x, y, z} : Set α)) (t := V(G)) hlt
    refine ⟨(G - ({x, y, z} : Set α)).walkable w, ⟨x, y, z, ?_, walkable_isCompOf hw, ?_⟩⟩
    · simpa using hTsep
    · simpa [y, hxy, hz.1.symm, hz.2.symm] using hAdj
  obtain ⟨C, ⟨x, y, z, hsep, hC, hxy, hxyne, hzxne, hzyne⟩, hMin⟩ :=
    exists_minimalFor_of_wellFoundedLT P (fun G ↦ V(G).encard) hexP
  clear hexP
  obtain ⟨-, hxC, hyC, hzC⟩ := by simpa [subset_diff] using vertexSet_mono hC.le

  -- 1. `{x, y, z}` is a minimum separator of `G` as `G` is 3-connected.
  have hMsep : G.IsMinSepSet {x, y, z} := {
    toIsSepSet := hsep
    minimal A hA := by
      refine le_trans ?_ (hG.le_cut hA)
      rw [(by norm_num : ((3: ℕ) : ℕ∞) = 1 + 1 + 1)]
      refine (encard_insert_le _ _).trans <| ENat.add_one_le_add_one_iff.mpr ?_
      refine (encard_insert_le _ _).trans <| ENat.add_one_le_add_one_iff.mpr ?_
      simp}
  clear hsep
  obtain ⟨w, hwC, f, hzw⟩ := hMsep.exists_adj_of_isCompOf_vertexDelete (hG.connected (by simp)) hC
    (x := z) (by simp) (by simp)
  -- `z ≠ w` since `z ∉ C` and `w ∈ C`
  have hzwne : z ≠ w := by
    rintro rfl
    obtain ⟨-, -, -, hzC⟩ := by simpa [subset_diff] using vertexSet_mono hC.le
    exact hzC hwC

  -- 2. Every edge is bad. Hence, there is a 3-sep that contains `w` and `z`.
  have := hG.exists_isSepSet_endpoints_of_not_connGE_contract_isLink hzw hzwne ?_ (hbad _ _ _ hzw)
  rotate_left
  · rw [hzw.contract_vertex_encard_eq_add_one hzwne] at hV
    enat_to_nat! <;> omega
  obtain ⟨T, hTsep, hTcard, hzT, hwT⟩ := this
  clear hbad

  -- 3. Either `x` or `y` is not in `T`. WLOG, assume `x ∉ T`.
  norm_num at hTcard
  replace hTcard : T.encard = 3 := hTcard.antisymm <| hG.le_cut hTsep
  have hT'card : (T \ ({w, z} : Set α)).encard = 1 := by
    rw [← diff_singleton_diff_eq, encard_diff_singleton_of_mem (by simpa [hzwne]),
    encard_diff_singleton_of_mem hwT, hTcard]
    rfl
  obtain ⟨w', hw'⟩ := encard_eq_one.mp hT'card
  obtain rfl : (T : Set α) = ({w, z, w'} : Set α) := by
    ext t
    obtain rfl | hnew := eq_or_ne t w
    · simpa
    obtain rfl | hnez := eq_or_ne t z
    · simpa
    have htTR : (t ∈ T) ↔ (t ∈ (T \ ({w, z} : Set α))) := by
      simp [hnew, hnez]
    rw [htTR, hw']
    simp [hnez, hnew]
  clear hzT hT'card
  simp only [mem_insert_iff, mem_singleton_iff, true_or, insert_diff_of_mem, or_true, sdiff_eq_left,
    disjoint_singleton_left, not_or, ← ne_eq] at hw'
  have hor : x ∉ ({w, z, w'} : Set α) ∨ y ∉ ({w, z, w'} : Set α) := by
    by_contra! h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    obtain ⟨(rfl | rfl | rfl), (rfl | rfl | rfl)⟩ := h <;> tauto

  wlog hxnT : x ∉ ({w, z, w'} : Set α)
  · have hh : ({y, x, z} : Set α) = {x, y, z} := insert_comm y x {z}
    exact this hG hV h4nconn C hMin y x z (hh ▸ hC) hxy.symm hxyne.symm hzyne hzxne hyC hxC hzC
      (hh ▸ hMsep) w hwC f hzw hzwne w' hTsep hwT hTcard hw' hor.symm
      (hor.resolve_left hxnT)
  clear hor
  -- 3.a. `x` and `y` is adjacent in `G - T` and therefore connected in `G - T`.
  have hxy' : y ∉ ({w, z, w'} : Set α) → (G - ({w, z, w'} : Set α)).Adj x y := by
    simp +contextual [hxy, hxnT]
  -- 4. This 3-sep, `T`, is also a minimum separator of `G` as `G` is 3-connected.
  have hMsep' : G.IsMinSepSet ({w, z, w'} : Set α) := {
    toIsSepSet := hTsep
    minimal A hA := hTcard ▸ (hG.le_cut hA)}
  clear hTsep
  -- 5. There is some `v` in `G - T` that is not connected to `x` and therefore `y`.
  have := hMsep'.not_connected
  rw [connected_iff, not_and] at this
  obtain ⟨v, hv, hvx⟩ := exists_not_connBetween_of_not_preconnected (this ⟨x, hxy.left_mem, hxnT⟩)
    ⟨hxy.left_mem, hxnT⟩
  clear this
  -- 6. In the component containing `v`, there is some `u` that is adjacent to `w`.
  obtain ⟨u, huv, hwuadj⟩ := hMsep'.exists_adj_of_isCompOf_vertexDelete (hG.connected (by simp))
    (walkable_isCompOf hv) hwT (vertexSet_finite.subset hMsep'.subset_vx)

  -- 7. `u ∈ C` since `w ∈ C`, `G.Adj w u`, `u ∉ T` and `u ∉ {x, y, z}`.
  have huT := (by exact huv : (G - ({w, z, w'} : Set α)).ConnBetween v u).right_mem
  have hxuconn : ¬ (G - ({w, z, w'} : Set α)).ConnBetween x u :=
    fun hxu ↦ hvx <| hxu.trans (by exact huv : (G - ({w, z, w'} : Set α)).ConnBetween v u).symm
  have hxu : u ≠ x := by
    rintro rfl
    simp [hxnT, hxy.left_mem] at hxuconn
  have hyu : u ≠ y := by
    rintro rfl
    exact hxuconn <| hxy' huT.2 |>.connBetween
  have hzu : u ≠ z := by
    rintro rfl
    exact huT.2 (by simp)
  have hwu : u ≠ w := by
    rintro rfl
    exact huT.2 hwT
  have huC : u ∈ V(C) := by
    refine hC.isClosedSubgraph.adj_of_adj_of_mem hwC (y := u) ?_ |>.right_mem
    rw [vertexDelete_adj_iff]
    use hwuadj, (vertexSet_mono hC.le) hwC |>.2
    simp [hxu, hyu, hzu]

  -- 8. The entire `(G - T).walkable u` must be strictly contained in `C`.
  have hC' := walkable_isCompOf huT
  have := hC'.of_vertexDelete (S := {x, y, z}) <| by
    rw [connBetween_comm] at hxuconn
    simp only [disjoint_insert_right, ← connBetween_iff_mem_walkable_of_mem, hxuconn,
      not_false_eq_true, disjoint_singleton_right, vertexDelete_vertexSet, mem_diff, mem_insert_iff,
      mem_singleton_iff, true_or, or_true, not_true_eq_false, and_false,
      not_connBetween_of_right_not_mem, and_true, true_and]
    by_cases hy : y ∈ ({w, z, w'} : Set α)
    · simp [hy]
    intro h
    exact hxuconn <| h.trans (hxy' hy |>.connBetween).symm

  have := this.eq_walkable_of_mem_walkable (x := u) (by simpa using huT)
  rw [vertexDelete_vertexDelete_comm] at this
  have hC'C : (G - ({w, z, w'} : Set α)).walkable u ≤ C := by
    rw [hC.eq_walkable_of_mem_walkable huC, this]
    exact walkable_mono vertexDelete_le u
  have hsub : V((G - ({w, z, w'} : Set α)).walkable u) ⊂ V(C) := by
    apply ssubset_of_ne_of_subset ?_ (vertexSet_mono hC'C)
    intro hVeq
    rw [← hVeq] at hwC
    simpa [hwT] using vertexSet_mono hC'.le hwC

  -- 9. Therefore, `T` and `(G - T).walkable u` is a smaller component than `{x, y, z}` and `C`.
  -- contradiction!
  have hlt := Finite.encard_lt_encard (vertexSet_finite.subset <|
    vertexSet_mono hC'.le) hsub
  refine hlt.ne' <| hMin (j := (G - ({w, z, w'} : Set α)).walkable u) ?_ hlt.le |>.antisymm hlt.le
  use w, z, w', hMsep'.isSepSet, hC', ⟨f, hzw.symm⟩, hzwne.symm, hw'.1.symm,
    hw'.2.symm

-- #print axioms exists_contract_connGE_three

end Graph
