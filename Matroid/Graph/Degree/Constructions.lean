import Matroid.Graph.Degree.Leaf

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {P C : WList α β}

open Set WList

namespace Graph

/-! ### Constructions -/

@[simp]
lemma noEdge_eDegree (V : Set α) (β : Type*) (x : α) : (Graph.noEdge V β).eDegree x = 0 := by
  simp [eDegree]

@[simp]
lemma noEdge_degree (V : Set α) (β : Type*) (x : α) : (Graph.noEdge V β).degree x = 0 := by
  simp [degree]

lemma singleEdge_eDegree_left (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).eDegree x = 1 := by
  rw [eDegree_eq_encard_add_encard, encard_eq_zero.2, ← encard_singleton e, mul_zero, zero_add]
  · convert rfl
    suffices ∃ z, ¬z = x ∧ (z = y ∨ x = y ∧ z = x) by
      simpa +contextual [iff_def, IsNonloopAt, Set.ext_iff]
    exact ⟨y, hxy.symm, by simp [hxy]⟩
  simp_rw [IsLoopAt, singleEdge_isLink_iff]
  simp [hxy]

lemma singleEdge_eDegree_right (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).eDegree y = 1 := by
  rw [singleEdge_comm, singleEdge_eDegree_left hxy.symm]

lemma singleEdge_eDegree_of_ne (e : β) (hx : z ≠ x) (hy : z ≠ y) :
    (Graph.singleEdge x y e).eDegree z = 0 := by
  simpa [eDegree_eq_zero_iff_adj, hx]

lemma singleEdge_degree_left (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).degree x = 1 := by
  simp [degree, singleEdge_eDegree_left hxy]

lemma singleEdge_degree_right (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).degree y = 1 := by
  simp [degree, singleEdge_eDegree_right hxy]

lemma singleEdge_degree_of_ne (e : β) (hx : z ≠ x) (hy : z ≠ y) :
    (Graph.singleEdge x y e).degree z = 0 := by
  simp [degree, singleEdge_eDegree_of_ne _ hx hy]

@[simp]
lemma singleEdge_self_eDegree (x : α) (e : β) : (Graph.singleEdge x x e).eDegree x = 2 := by
  rw [eDegree_eq_encard_add_encard]
  simp [← isLink_self_iff, IsNonloopAt]

@[simp]
lemma singleEdge_self_degree (x : α) (e : β) : (Graph.singleEdge x x e).degree x = 2 := by
  simp [degree]

lemma union_incFun_eq (hdj : Disjoint E(G) E(H)) : (G ∪ H).incFun = G.incFun + H.incFun := by
  ext e x
  rw [Pi.add_apply, Finsupp.add_apply]
  by_cases heG : e ∈ E(G)
  · rw [incFun_eq_of_le (Graph.left_le_union G H) heG, Nat.left_eq_add, incFun_vertex_eq_zero_iff]
    exact fun h ↦ hdj.not_mem_of_mem_right h.edge_mem heG
  rw [incFun_eq_zero_of_not_mem heG, Finsupp.coe_zero, Pi.zero_apply, zero_add]
  by_cases heH : e ∈ E(H)
  · rw [incFun_eq_of_le (Compatible.of_disjoint_edgeSet hdj).right_le_union heH]
  rw [incFun_eq_zero_of_not_mem (by simp [heH, heG]), incFun_eq_zero_of_not_mem heH]

lemma union_eDegree_eq (hdj : Disjoint E(G) E(H)) (x : α) :
    (G ∪ H).eDegree x = G.eDegree x + H.eDegree x := by
  simp [eDegree, union_incFun_eq hdj, ENat.tsum_add]

lemma eDegree_addEdge_left {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).eDegree a = G.eDegree a + 1 := by
  rw [Graph.addEdge, union_eDegree_eq (by simpa), add_comm, singleEdge_eDegree_left hab]

lemma eDegree_addEdge_right {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).eDegree b = G.eDegree b + 1 := by
  rw [Graph.addEdge, union_eDegree_eq (by simpa), add_comm, singleEdge_eDegree_right hab]

lemma eDegree_addEdge_of_ne {a b : α} (he : e ∉ E(G)) (hxa : x ≠ a) (hxb : x ≠ b) :
    (G.addEdge e a b).eDegree x = G.eDegree x := by
  rw [Graph.addEdge, union_eDegree_eq (by simpa), singleEdge_eDegree_of_ne _ hxa hxb, zero_add]

lemma union_degree_eq [G.LocallyFinite] [H.LocallyFinite] (hdj : Disjoint E(G) E(H)) (x : α) :
    (G ∪ H).degree x = G.degree x + H.degree x := by
  simp only [degree, union_eDegree_eq hdj]
  rw [ENat.toNat_add (by simp) (by simp)]

lemma degree_addEdge_left [G.LocallyFinite] {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).degree a = G.degree a + 1 := by
  rw [Graph.addEdge, union_degree_eq (by simpa), add_comm, singleEdge_degree_left hab]

lemma degree_addEdge_right [G.LocallyFinite] {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).degree b = G.degree b + 1 := by
  rw [Graph.addEdge, singleEdge_comm, ← Graph.addEdge, degree_addEdge_left he hab.symm]

lemma degree_addEdge_of_ne {a b : α} (he : e ∉ E(G)) (hxa : x ≠ a) (hxb : x ≠ b) :
    (G.addEdge e a b).degree x = G.degree x := by
  rw [degree, eDegree_addEdge_of_ne he hxa hxb, degree]

lemma IsNonloopAt.eDegree_delete_add_one (he : G.IsNonloopAt e x) :
    (G ＼ {e}).eDegree x + 1 = G.eDegree x := by
  obtain ⟨y, hxy, hy⟩ := he
  nth_rewrite 1 [eq_comm, ← hy.deleteEdge_addEdge, eDegree_addEdge_left (by simp) hxy.symm]
  rfl

lemma IsNonloopAt.degree_delete_add_one [G.LocallyFinite] (he : G.IsNonloopAt e x) :
    (G ＼ {e}).degree x + 1 = G.degree x := by
  obtain ⟨y, hxy, hy⟩ := he
  nth_rewrite 1 [eq_comm, ← hy.deleteEdge_addEdge, degree_addEdge_left (by simp) hxy.symm]
  rfl

lemma IsLoopAt.eDegree_delete_add_two (h : G.IsLoopAt e x) :
    (G ＼ {e}).eDegree x + 2 = G.eDegree x := by
  have hrw : {f | G.IsLoopAt f x} = insert e {f | (G ＼ {e}).IsLoopAt f x} := by
    simp only [edgeDelete_isLoopAt_iff, mem_singleton_iff]
    ext f
    have := eq_or_ne f e
    aesop
  rw [eDegree_eq_encard_add_encard, eDegree_eq_encard_add_encard, h.isNonloopAt_delete,
    add_right_comm, hrw, encard_insert_of_not_mem, mul_add, mul_one]
  simp only [mem_setOf_eq]
  exact fun (h : IsLoopAt _ _ _) ↦ h.edge_mem.2 rfl

lemma IsLoopAt.degree_delete_add_two [G.LocallyFinite] (h : G.IsLoopAt e x) :
    (G ＼ {e}).degree x + 2 = G.degree x := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, ← h.eDegree_delete_add_two]
  simp

lemma Inc.degree_delete_lt [G.LocallyFinite] (he : G.Inc e x) :
    (G ＼ {e}).degree x < G.degree x := by
  obtain he | he := he.isLoopAt_or_isNonloopAt
  · rw [← he.degree_delete_add_two]
    simp
  rw [← he.degree_delete_add_one]
  simp

lemma IsLink.eDegree_delete_of_ne (h : G.IsLink e x y) (hx : z ≠ x) (hy : z ≠ y) :
    (G ＼ {e}).eDegree z = G.eDegree z := by
  nth_rewrite 2 [← h.deleteEdge_addEdge]
  rw [eDegree_addEdge_of_ne (by simp) hx hy]

lemma IsLink.degree_delete_of_ne (h : G.IsLink e x y) (hx : z ≠ x) (hy : z ≠ y) :
    (G ＼ {e}).degree z = G.degree z := by
  simp [degree, h.eDegree_delete_of_ne hx hy]

/-! ### Paths -/

lemma IsPath.first_isLeaf_toGraph (hP : G.IsPath P) (hne : P.Nonempty) :
    P.toGraph.IsLeaf P.first := by
  obtain ⟨v, e, P⟩ := hne
  simp only [IsLeaf, first_cons, isPendant_iff, IsNonloopAt, ne_eq,
    hP.isWalk.wellFormed.toGraph_isLink, isLink_cons_iff', true_and, Inc, forall_exists_index]
  simp only [cons_isPath_iff] at hP
  refine ⟨e, ⟨P.first, ?_⟩, fun f x ↦ ?_⟩
  · simp only [true_or, and_self, and_true]
    rintro rfl
    simp at hP
  obtain rfl | hne := eq_or_ne e f
  · simp
  simp [hne, show ¬ P.IsLink f v x from fun h ↦ hP.2.2 h.left_mem]

lemma IsPath.last_isLeaf_toGraph (hP : G.IsPath P) (hne : P.Nonempty) :
    P.toGraph.IsLeaf P.last := by
  simpa [hP.isWalk.wellFormed.reverse_toGraph] using hP.reverse.first_isLeaf_toGraph (by simpa)

lemma IsPath.degree_toGraph_eq_two (hP : G.IsPath P) (hvP : v ∈ P) (hne_first : v ≠ P.first)
    (hne_last : v ≠ P.last) : P.toGraph.degree v = 2 := by
  induction P with
  | nil => simp_all
  | cons u e P ih =>
  · simp only [last_cons, ne_eq, first_cons] at hne_last hne_first
    have hPe := hP.edge_nodup
    simp only [cons_edge, List.nodup_cons] at hPe
    simp only [mem_cons_iff, hne_first, false_or] at hvP
    simp only [cons_isPath_iff] at hP
    rw [toGraph_cons, union_degree_eq (by simpa using hPe.1)]
    obtain rfl | hne1 := eq_or_ne v P.first
    · rw [singleEdge_degree_right (Ne.symm hne_first), (hP.1.first_isLeaf_toGraph ?_).degree]
      rwa [first_eq_last_iff hP.1.nodup, not_nil_iff] at hne_last
    rw [ singleEdge_degree_of_ne _ hne_first hne1, ih hP.1 hvP hne1 hne_last]

/-! ### Cycles -/

-- lemma IsCycle.degree_toGraph_eq_two (hC : G.IsCycle C) (hvC : v ∈ C) :
--     C.toGraph.degree v = 2 := by

--   obtain ⟨x, e, rfl⟩ | hCnt := hC.loop_or_nontrivial
--   · obtain rfl : v = x := by simpa using hvC
--     rw [toGraph_cons, union_degree_eq (by simp)]
--     simp
--   obtain ⟨P, u, e, f, huP, hPf, hef, rfl⟩ := hC.exists_isPath' hCnt
--   obtain rfl | hvu := eq_or_ne v u
--   · rw [toGraph]
  -- obtain ⟨P, u, e, f, hP, huP, heP, hfP, hne, rfl⟩ := hC.exists_isPath hCnt
  -- have hPconc : G.IsPath (P.concat f u) := by
  --   rw [← reverse_isPath_iff, concat_reverse]

  -- obtain rfl | hvu := eq_or_ne v u
  -- ·
  --   rw [toGraph_cons, union_degree_eq, singleEdge_degree_left]
  --   · nth_rw 2 [show v = (P.concat f v).last by simp]
  --     rw [(IsPath.last_isLeaf_toGraph _ _).degree]
  -- obtain ⟨e, heC⟩ := hC.nonempty.edgeSet_nonempty
  -- obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edge heC
  -- obtain ⟨P, hP, hPC, rfl, rfl⟩ := hC.exists_isPath_toGraph_eq_delete_edge_of_isLink hxy

  -- obtain rfl | hne_first := eq_or_ne v P.first
  -- · rw [← IsNonloopAt.degree_delete_add_one (e := e), ← hPC, (hP.first_isLeaf_toGraph _).degree]
  --   · rw [← hP.vertexSet_nontrivial_iff, ← toGraph_vertexSet, hPC]
  --     simp [hC.vertexSet_nontrivial hCnt]



  -- ·
  -- obtain ⟨P, hP, hPG⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  -- rw [← IsNonloopAt.degree_delete_add_one (e := e), ← hPG]
