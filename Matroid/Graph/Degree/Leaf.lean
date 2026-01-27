import Matroid.Graph.Degree.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}

open Set WList

namespace Graph

/-! ### Isolated vertices -/

lemma Isolated.eDegree (h : G.Isolated x) : G.eDegree x = 0 := by
  simp [eDegree_eq_tsum_mem, h.not_inc]

@[simp ←]
lemma isolated_iff_eDegree (hx : x ∈ V(G)) : G.Isolated x ↔ G.eDegree x = 0 := by
  simp [isolated_iff, hx, eDegree_eq_tsum_mem]

lemma Isolated.degree (h : G.Isolated x) : G.degree x = 0 := by
  rw [Graph.degree, h.eDegree, ENat.toNat_zero]

@[simp ←]
lemma isolated_iff_degree [G.LocallyFinite] (hx : x ∈ V(G)) : G.Isolated x ↔ G.degree x = 0 := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, isolated_iff_eDegree hx, Nat.cast_zero]


/-! ### Leaves -/

lemma IsPendant.eDegree (h : G.IsPendant e x) : G.eDegree x = 1 := by
  have hrw : {e | G.IsNonloopAt e x} = {e} := by
    simp +contextual only [Set.ext_iff, mem_setOf_eq, mem_singleton_iff, iff_def, h.isNonloopAt,
      implies_true, and_true]
    exact fun f hf ↦ h.edge_unique hf.inc
  simp [eDegree_eq_encard_add_encard, h.not_isLoopAt, hrw]

lemma Inc.isPendant_of_eDegree_le_one (h : G.Inc e x) (hdeg : G.eDegree x ≤ 1) :
    G.IsPendant e x := by
  replace hdeg := hdeg.antisymm h.one_le_eDegree
  have hnl : ∀ f, ¬ G.IsLoopAt f x := fun f hf ↦ by simpa using hf.two_le_eDegree.trans_eq hdeg
  refine ⟨h.isLoopAt_or_isNonloopAt.elim (fun h ↦ (hnl _ h).elim) id, fun f hf ↦ ?_⟩
  rw [inc_iff_isLoopAt_or_isNonloopAt, or_iff_right (hnl _)] at h hf
  rw [eDegree_eq_encard_add_encard] at hdeg
  have hss := encard_le_one_iff_subsingleton.1 <| le_add_self.trans hdeg.le
  exact hss hf h

lemma Inc.isPendant_of_degree_eq_one (h : G.Inc e x) (hdeg : G.degree x = 1) : G.IsPendant e x := by
  refine h.isPendant_of_eDegree_le_one ?_
  simp only [degree, ENat.toNat_eq_iff_eq_coe, Nat.cast_one] at hdeg
  exact hdeg.le

lemma Inc.isPendant_of_degree_le_one [G.LocallyFinite] (h : G.Inc e x) (hdeg : G.degree x ≤ 1) :
    G.IsPendant e x :=
  h.isPendant_of_eDegree_le_one <| by rwa [← natCast_degree_eq, ← Nat.cast_one, Nat.cast_le]

lemma IsPendant.edgeSet_delete_vertex_eq (h : G.IsPendant e x) : E(G - x) = E(G) \ {e} := by
  ext f
  simp only [vertexDelete_singleton, vertexDelete_edgeSet, mem_singleton_iff, mem_setOf_eq,
    mem_diff]
  refine ⟨fun ⟨z, y, h'⟩ ↦ ⟨h'.1.edge_mem, ?_⟩, fun ⟨hfE, hfe⟩ ↦ ?_⟩
  · rintro rfl
    cases h.isNonloopAt.inc.eq_or_eq_of_isLink h'.1 <;> simp_all
  obtain ⟨y, hyx, hy⟩ := h.isNonloopAt
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet hfE
  refine ⟨z, w, hzw, fun h_eq ↦ hfe ?_, fun h_eq ↦ hfe ?_⟩
  · exact h.edge_unique ((h_eq ▸ hzw).inc_left)
  exact h.edge_unique (h_eq ▸ hzw.inc_right)

lemma IsPendant.eq_addEdge (h : G.IsPendant e x) :
    ∃ y ∈ V(G), G.IsLink e x y ∧ y ≠ x ∧ e ∉ E(G - x) ∧ G = (G - x).addEdge e x y := by
  obtain ⟨y, hne, hexy⟩ := h.isNonloopAt
  refine ⟨y, hexy.right_mem, hexy, hne, ?_, ext_of_le_le le_rfl ?_ ?_ ?_⟩
  · rw [h.edgeSet_delete_vertex_eq]
    simp
  · exact Graph.union_le (by simpa) (by simp)
  · rw [addEdge_vertexSet, vertexDelete_singleton, vertexDelete_vertexSet, ← union_singleton,
      union_assoc]
    simp [insert_eq_of_mem hexy.right_mem, insert_eq_of_mem hexy.left_mem]
  rw [addEdge_edgeSet, h.edgeSet_delete_vertex_eq, insert_diff_singleton,
    insert_eq_of_mem hexy.edge_mem]

lemma IsPendant.exists_eq_addEdge (h : G.IsPendant e x) :
    ∃ (y : α) (H : Graph α β), x ∉ V(H) ∧ y ∈ V(H) ∧ e ∉ E(H) ∧ G = H.addEdge e x y := by
  obtain ⟨y, hyV, -, hyx, -, h_eq⟩ := h.eq_addEdge
  refine ⟨y, _, by simp, by simp [hyV, hyx], ?_, h_eq⟩
  rw [h.edgeSet_delete_vertex_eq]
  simp

@[simp]
lemma eDegree_eq_one_iff : G.eDegree v = 1 ↔ G.IsLeaf v := by
  refine ⟨fun h ↦ ?_, fun ⟨e, h⟩ ↦ h.eDegree⟩
  obtain ⟨e, he⟩ | hn := em <| ∃ e, G.Inc e v
  · exact ⟨e, he.isPendant_of_eDegree_le_one h.le⟩
  simp [← eDegree_eq_zero_iff_inc, h] at hn

@[simp]
lemma degree_eq_one_iff : G.degree v = 1 ↔ G.IsLeaf v := by
  simp [← eDegree_eq_one_iff, degree]

lemma IsLeaf.eDegree (h : G.IsLeaf v) : G.eDegree v = 1 := by
  simpa

lemma IsLeaf.degree (h : G.IsLeaf v) : G.degree v = 1 := by
  simpa

lemma IsTrail.eq_first_or_last_of_degree_eq_one {P} (hP : G.IsTrail P) (hx : x ∈ P)
    (hdeg : G.IsLeaf x) : x = P.first ∨ x = P.last := by
  by_contra! h
  obtain ⟨e₁, y₁, h₁⟩ := exists_left_edge hx h.1
  obtain ⟨e₂, y₂, h₂⟩ := exists_right_edge hx h.2
  have hinc₁ : G.Inc e₁ x := (hP.isWalk.isLink_of_dInc h₁).inc_right
  have hinc₂ : G.Inc e₂ x := (hP.isWalk.isLink_of_dInc h₂).inc_left
  obtain rfl := hdeg.eq_of_inc_inc hinc₁ hinc₂
  obtain ⟨rfl, rfl⟩ := (dInc_iff_eq_of_dInc_of_edge_nodup hP.edge_nodup h₁).mp h₂
  exact hdeg.not_isLoopAt e₁ (hP.isWalk.isLink_of_dInc h₁)

lemma IsTrail.eq_first_or_last_of_eDegree_le_one {P} (hP : G.IsTrail P) (hxP : x ∈ P)
    (hdeg : G.eDegree x ≤ 1) : x = P.first ∨ x = P.last := by
  have hx : x ∈ V(G) := hP.vertexSet_subset hxP
  simp only [le_iff_lt_or_eq, ENat.lt_one_iff_eq_zero, hx, ← isolated_iff_eDegree,
    eDegree_eq_one_iff] at hdeg
  obtain h | h := hdeg
  · exact Or.inl <| h.eq_first_of_mem hP.isWalk hxP
  exact hP.eq_first_or_last_of_degree_eq_one hxP h

lemma IsTrail.disjoint_of_degree_le_one {w X} (hw : G.IsTrail w) (hX : ∀ x ∈ X, G.eDegree x ≤ 1)
    (hf : w.first ∉ X) (hl : w.last ∉ X) : Disjoint V(w) X := by
  rw [disjoint_comm, disjoint_iff_forall_notMem]
  intro x hxX hxw
  apply hw.eq_first_or_last_of_eDegree_le_one hxw (hX x hxX) |>.elim <;> grind
