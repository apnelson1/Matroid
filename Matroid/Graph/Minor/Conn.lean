import Matroid.Graph.Minor.Defs
import Matroid.Graph.Forest

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ I : Graph α β}
  {C D F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)} {W w w' P Q c : WList α β}
  {φ : α → α}

open Set Function WList

namespace Graph

lemma IsWalk.edgeRemove_contract_nil [DecidablePred (· ∈ E(G))] {w} (φ : α → α) (hw : G.IsWalk w) :
    ((w.map φ).edgeRemove E(G)).Nil := by
  rw [nil_iff_edge_nil, edgeRemove_edge]
  simpa using fun _ ↦ hw.edge_mem_of_mem

lemma IsWalk.mem_map_iff_first_of_isRepFun [DecidablePred (· ∈ E(G))]
    (hφ : G.connPartition.IsRepFun φ) {w} (hw : G.IsWalk w) : x ∈ w.map φ ↔ x = φ w.first := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    rw [cons_isWalk_iff] at hw
    obtain ⟨hl, h⟩ := hw
    simp only [map_cons, mem_cons_iff, ih h, first_cons, or_iff_left_iff_imp]
    rintro rfl
    exact hφ.apply_eq_apply <| by simpa using hl.symm.connBetween

lemma IsWalk.mem_map_iff_last_of_isRepFun [DecidablePred (· ∈ E(G))]
    (hφ : G.connPartition.IsRepFun φ) {w} (hw : G.IsWalk w) : x ∈ w.map φ ↔ x = φ w.last := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    rw [cons_isWalk_iff] at hw
    obtain ⟨hl, h⟩ := hw
    simp only [map_cons, mem_cons_iff, ih h, last_cons, or_iff_right_iff_imp]
    rintro rfl
    apply hφ.apply_eq_apply
    simp only [connPartition_rel_iff]
    exact hl.connBetween.trans <| by use w

noncomputable def IsWalk.uncontract_aux (hφ : G.connPartition.IsRepFun φ) {u v W}
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    {w : WList α β // w.first = u ∧ w.last = v} :=
  match W with
  | .nil x => by
    classical
    simp only [nil_first, nil_last, nil_isWalk_iff, contract_vertexSet, mem_image] at hu hv hw
    subst x
    simp only [hφ.apply_eq_apply_iff, connPartition_rel_iff] at hv
    use if huv : u = v then .nil u else (hv.resolve_left huv).exists_isPath.choose
    split_ifs with huv
    · simpa
    generalize_proofs hP
    exact hP.choose_spec.2
  | .cons z e w => by
    classical
    simp only [cons_isWalk_iff, contract_isLink] at hw
    choose x y hxy hux hwfy using hw.1.1
    simp only [first_cons, last_cons] at hu hv
    let wIH := hw.2.uncontract_aux hφ hwfy hv
    have hu' := hux.symm.trans hu
    simp only [hφ.apply_eq_apply_iff, connPartition_rel_iff] at hu'
    use if heq : x = u then WList.cons x e wIH.val else
      ((hu'.resolve_left heq |>.symm.exists_isPath.choose) ++ (WList.cons x e wIH.val))
    split_ifs with heq
    · simp [heq, wIH.prop.2]
    generalize_proofs hP
    rw [append_first_of_eq (by simpa using hP.choose_spec.2.2)]
    simp [hP.choose_spec.2.1, wIH.prop.2]

noncomputable def IsWalk.uncontract (hφ : G.connPartition.IsRepFun φ)
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :=
  (hw.uncontract_aux hφ hu hv).val

@[simp, grind =]
lemma IsWalk.uncontract_first (hφ : G.connPartition.IsRepFun φ) (hw : H /[φ, E(G)].IsWalk W)
    (hu : W.first = φ u) (hv : W.last = φ v) : (hw.uncontract hφ hu hv).first = u :=
  (hw.uncontract_aux hφ hu hv).prop.1

@[simp, grind =]
lemma IsWalk.uncontract_last (hφ : G.connPartition.IsRepFun φ) (hw : H /[φ, E(G)].IsWalk W)
    (hu : W.first = φ u) (hv : W.last = φ v) : (hw.uncontract hφ hu hv).last = v :=
  (hw.uncontract_aux hφ hu hv).prop.2

lemma IsWalk.uncontract_map_edgeRemove (hφ : G.connPartition.IsRepFun φ) [DecidablePred (· ∈ E(G))]
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    ((hw.uncontract hφ hu hv).map φ).edgeRemove E(G) = W := by
  classical
  induction W generalizing u with
  | nil z =>
    simp only [nil_first, nil_last] at hu hv
    subst z
    simp only [nil_isWalk_iff, contract_vertexSet, mem_image, uncontract, uncontract_aux] at hw ⊢
    split_ifs with heq
    · simp
    generalize_proofs hP
    classical
    rw [hP.choose_spec.1.isWalk.edgeRemove_contract_nil φ |>.eq_nil_first]
    rw [edgeRemove_first ?_ (hP.choose_spec.1.isWalk.map φ), map_first, hP.choose_spec.2.1]
    exact hφ.isContractClosed_of_ge le_rfl |>.exists_isLoopAt_of_isWalk hP.choose_spec.1.isWalk
  | cons z e w ih =>
    simp only [first_cons, last_cons, cons_isWalk_iff, contract_isLink] at hu hv hw ⊢
    simp only [uncontract, uncontract_aux, hu]
    generalize_proofs hw11 hw11' hw112 hw2 hwf
    replace ih := ih hw2 hwf hv
    split_ifs with heq
    · simp only [heq, map_cons, edgeRemove_cons_of_notMem hw.1.2, cons.injEq, true_and]
      exact ih
    generalize_proofs hP
    rw [map_append, edgeRemove_append_eq_right _ _
      (by simpa using hP.choose_spec.1.isWalk.edgeSet_subset)]
    simpa [map_cons, edgeRemove_cons_of_notMem hw.1.2, cons.injEq, true_and,
      hw11.choose_spec.choose_spec.2.1.symm]

@[simp]
lemma IsWalk.uncontract_edgeSet_diff (hφ : G.connPartition.IsRepFun φ) {W}
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    E(hw.uncontract hφ hu hv) \ E(G) = E(W) := by
  classical
  conv_rhs => rw [← hw.uncontract_map_edgeRemove hφ hu hv]
  simp

@[simp]
lemma IsWalk.subset_uncontract_edgeSet (hφ : G.connPartition.IsRepFun φ) {W}
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    E(W) ⊆ E(hw.uncontract hφ hu hv) := by
  rw [← hw.uncontract_edgeSet_diff hφ hu hv]
  exact diff_subset

@[simp]
lemma IsWalk.uncontract_edgeSet_subset (hφ : G.connPartition.IsRepFun φ) {W}
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    E(hw.uncontract hφ hu hv) ⊆ E(W) ∪ E(G) := by
  rw [← hw.uncontract_edgeSet_diff hφ hu hv, diff_union_eq_union_of_subset _ subset_rfl]
  exact subset_union_left

lemma IsWalk.uncontract_isWalk (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) {W}
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    H.IsWalk (hw.uncontract hφ hu hv) := by
  classical
  induction W generalizing u with
  | nil z =>
    simp only [nil_first, nil_last] at hu hv
    subst z
    simp only [nil_isWalk_iff, contract_vertexSet, uncontract, uncontract_aux] at hw ⊢
    split_ifs with huv
    · subst u
      simp only [nil_isWalk_iff]
      have := hφ.image_subset (by simpa using vertexSet_mono hGH) hw
      rwa [hφ.apply_mem_iff_of_subset (by simpa using vertexSet_mono hGH)] at this
    generalize_proofs hP
    exact (hP.choose_spec.1.of_le hGH).isWalk
  | cons z e w ih =>
    simp only [first_cons, last_cons, cons_isWalk_iff, contract_isLink] at hu hv hw ⊢
    simp only [uncontract, uncontract_aux, hu]
    subst z
    generalize_proofs hw11 hw112 hw2 hwf
    replace ih := ih hw2 hwf hv
    split_ifs with heq
    · simp only [heq, cons_isWalk_iff, (hw2.uncontract_aux hφ hwf hv).prop.1]
      use ?_, ih
      generalize_proofs h
      exact h.choose_spec.1
    generalize_proofs hP
    refine (hP.choose_spec.1.of_le hGH).isWalk.append ?_ <| by simp [hP.choose_spec.2.2]
    simp only [cons_isWalk_iff, (hw2.uncontract_aux hφ hwf hv).prop.1]
    exact ⟨hw112.choose_spec.1, ih⟩

@[simp]
lemma IsWalk.mem_uncontract_map_iff (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H)
    (hw : H /[φ, E(G)].IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    x ∈ (hw.uncontract hφ hu hv).map φ ↔ x ∈ W := by
  classical
  conv_rhs => rw [← hw.uncontract_map_edgeRemove hφ hu hv]
  rw [mem_edgeRemove_iff ?_ <| (hw.uncontract_isWalk hφ hGH hu hv).map φ]
  exact hφ.isContractClosed_of_ge hGH |>.exists_isLoopAt_of_isWalk
    (hw.uncontract_isWalk hφ hGH hu hv)

lemma IsPath.uncontract_isPath (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) {W}
    (hw : H /[φ, E(G)].IsPath W) (hu : W.first = φ u) (hv : W.last = φ v) :
    H.IsPath (hw.isWalk.uncontract hφ hu hv) := by
  classical
  refine ⟨hw.isWalk.uncontract_isWalk hφ hGH hu hv, ?_⟩
  induction W generalizing u with
  | nil z =>
    simp only [nil_first, nil_last] at hu hv
    subst z
    simp only [nil_isPath_iff, contract_vertexSet, mem_image, IsWalk.uncontract,
      IsWalk.uncontract_aux] at hw ⊢
    split_ifs with heq
    · simp
    generalize_proofs hP
    exact hP.choose_spec.1.nodup
  | cons z e w ih =>
    simp only [cons_isPath_iff, contract_isLink, first_cons, last_cons] at hw hu hv ⊢
    obtain ⟨⟨hw11, heG⟩, hw2, huw⟩ := hw
    simp only [IsWalk.uncontract, IsWalk.uncontract_aux]
    subst z
    generalize_proofs hw112 hw22 hwf
    replace ih := ih hw2 hwf hv
    unfold IsWalk.uncontract at ih
    have A : hw11.choose ∉ IsWalk.uncontract hφ hw22 hwf hv := by
      contrapose! huw
      have : _ ∈ (hw2.isWalk.uncontract hφ hwf hv).map φ := mem_map_iff _ φ _ |>.mpr ⟨_, huw, rfl⟩
      rwa [hw2.isWalk.mem_uncontract_map_iff hφ hGH hwf hv,
        ← hw11.choose_spec.choose_spec.2.1] at this
    split_ifs with heq
    · simpa [ih]
    generalize_proofs hP
    simp only [append_vertex, cons_vertex, List.nodup_append', List.nodup_cons, mem_vertex, ih,
      and_true, List.disjoint_cons_right]
    refine ⟨hP.choose_spec.1.nodup.sublist (List.dropLast_sublist ..), A, ?_, ?_⟩
    · simp [List.mem_dropLast_iff hP.choose_spec.1.nodup (by simp), hP.choose_spec.2.2]
    rintro x hxP hxw
    have hxP' := (mem_map_iff _ φ _).mpr ⟨_, List.dropLast_subset _ hxP, rfl⟩
    rw [hP.choose_spec.1.isWalk.mem_map_iff_first_of_isRepFun hφ, hP.choose_spec.2.1] at hxP'
    have hxw' := (mem_map_iff (hw22.uncontract hφ hwf hv) φ _).mpr ⟨_, hxw, rfl⟩
    rw [hw22.mem_uncontract_map_iff hφ hGH] at hxw'
    grind

lemma IsCyclicWalk.exists_isCyclicWalk_of_contract (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H)
    (hw : H /[φ, E(G)].IsCyclicWalk W) : ∃ C, H.IsCyclicWalk C ∧ E(C) \ E(G) = E(W) := by
  obtain ⟨z, e, w⟩ := hw.nonempty
  obtain ⟨-, ⟨⟨x, y, hxy, rfl, hwf⟩, heG⟩, hew⟩ := by simpa using hw.isTrail
  have hwP := by simpa using hw.tail_isPath
  have hv : w.last = φ x := by simpa using hw.isClosed.symm
  have hwP' := hwP.uncontract_isPath hφ hGH hwf hv
  have he : e ∉ E(IsWalk.uncontract hφ hwP.isWalk hwf hv) := by
    apply notMem_subset (hwP.isWalk.uncontract_edgeSet_subset hφ hwf hv)
    simp [hew, heG]
  have hew' := hwP'.cons_isCyclicWalk (e := e) (by simp [hxy.symm]) he
  exact ⟨_, hew', by simp [insert_diff_of_notMem _ heG]⟩

lemma contract_connBetween_iff (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) (u v) :
    (H /[φ, E(G)]).ConnBetween (φ u) (φ v) ↔ H.ConnBetween u v := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨W, hW, hWf, hWl⟩ := h
    use hW.uncontract hφ hWf hWl, hW.uncontract_isWalk hφ hGH hWf hWl
    simp
  · obtain ⟨W, hW, rfl, rfl⟩ := h
    classical
    use (W.map φ).edgeRemove E(G), hW.edgeRemove_contract hGH hφ
    rw [edgeRemove_first (hφ.isContractClosed_of_ge hGH |>.exists_isLoopAt_of_isWalk hW) (hW.map φ)]
    simp

@[simp]
lemma contract_preconnected_iff (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) :
    (H /[φ, E(G)]).Preconnected ↔ H.Preconnected := by
  unfold Preconnected
  refine ⟨fun h x y hx hy ↦ ?_, ?_⟩
  · rw [← contract_connBetween_iff hφ hGH]
    exact h _ _ (by use x) (by use y)
  rintro h _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  rw [contract_connBetween_iff hφ hGH]
  exact h x y hx hy

@[simp]
lemma contract_connected_iff (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) :
    (H /[φ, E(G)]).Connected ↔ H.Connected := by
  simp [connected_iff, contract_preconnected_iff hφ hGH]

lemma contract_isBridge_iff (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) (he : e ∈ E(H) \ E(G)) :
    (H /[φ, E(G)]).IsBridge e ↔ H.IsBridge e := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he.1
  have := contract_isLink H φ E(G) e (φ x) (φ y) |>.mpr ⟨by grind, he.2⟩
  rw [hxy.isBridge_iff_not_connBetween, this.isBridge_iff_not_connBetween, contract_edgeDelete_comm,
    not_iff_not, contract_connBetween_iff hφ (by simp [hGH, he.2])]

lemma IsForest.contract (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) (hH : H.IsForest) :
    (H /[φ, E(G)]).IsForest := by
  rintro e he
  rw [contract_isBridge_iff hφ hGH he]
  exact hH he.1

-- lemma eq_contract_edgeDelete (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) :
--     ∃ F ≤ G, F.IsForest ∧ H /[φ, E(G)] = (H ＼ (E(G) \ E(F))) /[φ, E(F)] := by
--   have :=
--   sorry

end Graph
