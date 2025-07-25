import Matroid.Graph.Walk.Basic
import Mathlib.Order.Minimal

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {W w w₀ w₁ w₂ P P₀ P₁ P₂ : WList α β} {S T X : Set α}

open WList Set

namespace Graph

/-! ### Trails -/

/-- `G.IsTrail w` means that `w` is a walk of `G` with no repeated edges. -/
@[mk_iff]
structure IsTrail (G : Graph α β) (W : WList α β) : Prop where
  isWalk : G.IsWalk W
  edge_nodup : W.edge.Nodup

lemma IsTrail.sublist (h : G.IsTrail w₂) (hle : w₁.IsSublist w₂) : G.IsTrail w₁ :=
  ⟨h.isWalk.sublist hle, hle.edge_sublist.nodup h.edge_nodup⟩

@[simp]
lemma nil_isTrail_iff : G.IsTrail (nil x) ↔ x ∈ V(G) := by
  simp [isTrail_iff]

@[simp]
lemma cons_isTrail_iff : G.IsTrail (cons x e w) ↔
    G.IsTrail w ∧ G.IsLink e x w.first ∧ e ∉ w.edge := by
  simp only [isTrail_iff, cons_isWalk_iff, cons_edge, List.nodup_cons]
  tauto

@[simp]
lemma IsTrail.of_cons (h : G.IsTrail (cons x e w)) : G.IsTrail w := by
  simp_all

lemma nil_isTrail (hx : x ∈ V(G)) : G.IsTrail (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

lemma IsTrail.reverse (h : G.IsTrail w) : G.IsTrail w.reverse :=
  ⟨h.isWalk.reverse, by simp [h.edge_nodup]⟩

@[simp]
lemma reverse_isTrail_iff : G.IsTrail (reverse w) ↔ G.IsTrail w :=
  ⟨fun h ↦ by simpa using h.reverse, IsTrail.reverse⟩

lemma IsTrail.of_isLabelSubgraph (h : H.IsTrail w) (hlle : H ≤l G) : G.IsTrail w :=
  ⟨h.isWalk.of_isLabelSubgraph hlle, h.edge_nodup⟩

lemma IsTrail.of_le (hw : G.IsTrail w) (hle : G ≤ H) : H.IsTrail w :=
  ⟨hw.isWalk.of_le hle, hw.edge_nodup⟩

lemma IsTrail.vertexSet_subset (hw : G.IsTrail w) : V(w) ⊆ V(G) :=
  hw.isWalk.vertexSet_subset

-- lemma IsTrail.induce (hw : G.IsTrail w) (hX : V(w) ⊆ X) : G[X].IsTrail w :=
--   ⟨hw.isWalk.induce hX, hw.edge_nodup⟩

-- /-- This is almost true without the `X ⊆ V(G)` assumption; the exception is where
-- `w` is a nil walk on a vertex in `X \ V(G)`. -/
-- lemma isTrail_induce_iff (hXV : X ⊆ V(G)) :
--     (G.induce X).IsTrail w ↔ G.IsTrail w ∧ V(w) ⊆ X :=
--   ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩

-- lemma isTrail_induce_iff' (hw : w.Nonempty) : G[X].IsTrail w ↔ G.IsTrail w ∧ V(w) ⊆ X := by
--   rw [isTrail_iff, isWalk_induce_iff' hw, and_assoc, isTrail_iff]
--   tauto

@[simp]
lemma isTrail_vertexDelete_iff : (G - X).IsTrail w ↔ G.IsTrail w ∧ Disjoint V(w) X := by
  simp_rw [isTrail_iff, isWalk_vertexDelete_iff]
  tauto

lemma IsTrail.isTrail_isLabelSubgraph (h : G.IsTrail w) (hlle : H ≤l G) (hE : E(w) ⊆ E(H))
    (hV : V(w) ⊆ V(H)) : H.IsTrail w where
  isWalk := h.isWalk.isWalk_isLabelSubgraph hlle hE hV
  edge_nodup := h.edge_nodup

lemma IsTrail.isTrail_le (h : G.IsTrail w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hfirst : w.first ∈ V(H)) : H.IsTrail w where
  isWalk := h.isWalk.isWalk_le hle hE hfirst
  edge_nodup := h.edge_nodup

lemma IsTrail.isTrail_le_of_nonempty (h : G.IsTrail w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hne : w.Nonempty) : H.IsTrail w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE hne
  edge_nodup := h.edge_nodup

lemma IsTrail.eq_append_cons_of_edge_mem (hW : G.IsTrail W) (heW : e ∈ W.edge) :
    ∃ W₁ W₂, G.IsTrail W₁ ∧ G.IsTrail W₂ ∧ e ∉ W₁.edge ∧ e ∉ W₂.edge ∧ W₁.edge.Disjoint W₂.edge ∧
    W = W₁ ++ WList.cons W₁.last e W₂ := by
  obtain ⟨W₁, W₂, hW₁, hW₂, heW₁, rfl⟩ := hW.isWalk.eq_append_cons_of_edge_mem heW
  have hnd := hW.edge_nodup
  simp only [append_edge, cons_edge, List.nodup_append', List.nodup_cons,
    List.disjoint_cons_right] at hnd
  use W₁, W₂
  simp_all [isTrail_iff]

lemma IsTrail.dInc_iff_eq_of_dInc (hW : G.IsTrail W) (he : W.DInc e u v) :
    W.DInc e x y ↔ (x = u) ∧ (y = v) := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction W with
  | nil u => simp at he
  | cons z f W IH =>
    rw [dInc_cons_iff] at h he
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨rfl, he, rfl⟩ | he := he
      · simp
      simpa [he.edge_mem] using hW.edge_nodup
    obtain ⟨rfl, rfl, rfl⟩ | he := he
    · simpa [h.edge_mem] using hW.edge_nodup
    exact IH hW.of_cons he h

/-! ### Paths -/

/-- `G.IsPath P` means that `w` is a walk of `G` with no repeated vertices
(and therefore no repeated edges). -/
@[mk_iff]
structure IsPath (G : Graph α β) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  nodup : w.vertex.Nodup

lemma nil_isPath (hx : x ∈ V(G)) : G.IsPath (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

@[simp] lemma nil_isPath_iff : G.IsPath (nil x) ↔ x ∈ V(G) := by
  simp [isPath_iff]

@[simp]
lemma cons_isPath_iff : G.IsPath (cons x e P) ↔ G.IsPath P ∧ G.IsLink e x P.first ∧ x ∉ P := by
  simp only [isPath_iff, cons_isWalk_iff, cons_vertex, List.nodup_cons, mem_vertex]
  tauto

@[simp]
lemma IsPath.of_cons (h : G.IsPath (cons x e P)) : G.IsPath P := by
  simp_all

lemma IsPath.isTrail (h : G.IsPath P) : G.IsTrail P where
  isWalk := h.1
  edge_nodup := by
    induction P with
    | nil u => simp
    | cons u e w ih =>
      simp_all only [cons_isPath_iff, cons_edge, List.nodup_cons, and_true, forall_const]
      exact fun he ↦ h.2.2 <| h.1.isWalk.vertex_mem_of_edge_mem he h.2.1.inc_left

lemma IsPath.reverse (hp : G.IsPath P) : G.IsPath P.reverse where
  isWalk := hp.isWalk.reverse
  nodup := by simp [hp.nodup]

@[simp]
lemma reverse_isPath_iff : G.IsPath (reverse P) ↔ G.IsPath P :=
  ⟨fun h ↦ by simpa using h.reverse, IsPath.reverse⟩

@[simp]
lemma concat_isPath_iff : G.IsPath (P.concat e x) ↔ G.IsPath P ∧ G.IsLink e P.last x ∧ x ∉ P := by
  rw [← reverse_isPath_iff, concat_reverse, cons_isPath_iff]
  simp +contextual [iff_def, IsLink.symm]

lemma IsWalk.dedup_isPath [DecidableEq α] (h : G.IsWalk P) : G.IsPath P.dedup :=
  ⟨h.dedup, P.dedup_vertex_nodup⟩

lemma IsLink.walk_isPath (h : G.IsLink e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_isWalk, by simp [hne]⟩

lemma IsPath.edge_nodup (h : G.IsPath P) : P.edge.Nodup :=
  h.isTrail.edge_nodup

lemma IsPath.of_le (hP : G.IsPath P) (hle : G ≤ H) : H.IsPath P :=
  ⟨hP.isWalk.of_le hle, hP.nodup⟩

lemma IsPath.vertexSet_subset (hP : G.IsPath P) : V(P) ⊆ V(G) :=
  hP.isWalk.vertexSet_subset

lemma IsPath.induce (hP : G.IsPath P) (hX : V(P) ⊆ X) : (G[X]).IsPath P :=
  ⟨hP.isWalk.induce hX, hP.nodup⟩

lemma IsPath.prefix (hP : G.IsPath P) (hP₀ : P₀.IsPrefix P) : G.IsPath P₀ where
  isWalk := hP.isWalk.prefix hP₀
  nodup := hP.nodup.sublist hP₀.vertex_isPrefix.sublist

lemma IsPath.suffix (hP : G.IsPath P) (hP₀ : P₀.IsSuffix P) : G.IsPath P₀ where
  isWalk := hP.isWalk.suffix hP₀
  nodup := hP.nodup.sublist hP₀.vertex_isSuffix.sublist

/-- This is almost true without the `X ⊆ V(G)` assumption; the exception is where
`w` is a nil walk on a vertex in `X \ V(G)`. -/
lemma isPath_induce_iff (hXV : X ⊆ V(G)) : G[X].IsPath P ↔ G.IsPath P ∧ V(P) ⊆ X :=
  ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩

lemma isPath_induce_iff' (hP : P.Nonempty) : G[X].IsPath P ↔ G.IsPath P ∧ V(P) ⊆ X := by
  rw [isPath_iff, isWalk_induce_iff' hP, and_assoc, isPath_iff]
  tauto

@[simp]
lemma isPath_vertexDelete_iff : (G - X).IsPath P ↔ G.IsPath P ∧ Disjoint V(P) X := by
  rw [vertexDelete_def, isPath_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.vertexSet_subset

lemma IsPath.isPath_le (h : G.IsPath w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hfirst : w.first ∈ V(H)) : H.IsPath w where
  isWalk := h.isWalk.isWalk_le hle hE hfirst
  nodup := h.nodup

lemma IsPath.isPath_le_of_nonempty (h : G.IsPath w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hne : w.Nonempty) : H.IsPath w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE hne
  nodup := h.nodup

@[simp]
lemma isPath_edgeRestrict_iff {F : Set β} : (G ↾ F).IsPath P ↔ G.IsPath P ∧ E(P) ⊆ F := by
  simp [isPath_iff, and_right_comm]

@[simp]
lemma isPath_edgeDelete_iff {F : Set β} : (G ＼ F).IsPath P ↔ G.IsPath P ∧ Disjoint E(P) F := by
  rw [isPath_iff, isWalk_edgeDelete_iff, isPath_iff, and_right_comm]

lemma IsPath.append {P Q : WList α β} (hP : G.IsPath P) (hQ : G.IsPath Q) (hPQ : P.last = Q.first)
    (h_inter : ∀ x, x ∈ P → x ∈ Q → x = P.last) : G.IsPath (P ++ Q) := by
  induction P with
  | nil u => simpa
  | cons u e w ih =>
    simp_all only [mem_cons_iff, true_or, last_mem, or_true, implies_true, nonempty_prop,
      forall_const, cons_isPath_iff, first_mem, or_false, last_cons, forall_eq_or_imp, cons_append,
      append_first_of_eq, true_and]
    rw [← mem_vertexSet_iff, append_vertexSet hPQ, mem_union, not_or, mem_vertexSet_iff,
      mem_vertexSet_iff]
    refine ⟨hP.2.2, fun huQ ↦ ?_⟩
    rw [← h_inter.1 huQ] at hPQ
    exact hP.2.2 (by simp [← hPQ])

lemma IsPath.eq_append_cons_of_edge_mem (hP : G.IsPath P) (heP : e ∈ P.edge) :
    ∃ P₁ P₂, G.IsPath P₁ ∧ G.IsPath P₂ ∧ e ∉ P₁.edge ∧ e ∉ P₂.edge ∧
      P₁.vertex.Disjoint P₂.vertex ∧ P₁.edge.Disjoint P₂.edge ∧ P = P₁ ++ cons P₁.last e P₂ := by
  obtain ⟨P₁, P₂, hP₁, hP₂, heP₁, heP₂, hdj, rfl⟩ := hP.isTrail.eq_append_cons_of_edge_mem heP
  have hnd := hP.nodup
  rw [append_vertex' rfl, List.nodup_append] at hnd
  simp only [cons_vertex, List.tail_cons] at hnd
  use P₁, P₂
  simp_all [hdj, isPath_iff, hP₁.isWalk, hP₂.isWalk]

/-- An edge of a path `P` incident to the first vertex is the first edge.  -/
lemma IsPath.eq_firstEdge_of_isLink_first (hP : G.IsPath P) (heP : e ∈ P.edge)
    (he : G.Inc e P.first) : e = Nonempty.firstEdge P (by cases P with simp_all) := by
  obtain ⟨z, hex⟩ := he
  rw [← hP.isWalk.isLink_iff_isLink_of_mem heP] at hex
  exact hex.eq_firstEdge_of_isLink_first hP.nodup

lemma IsPath.vertexSet_nontrivial_iff (hP : G.IsPath P) : V(P).Nontrivial ↔ P.Nonempty := by
  obtain u | ⟨u, e, P⟩ := P
  · simp
  simp only [cons_vertexSet, cons_nonempty, iff_true]
  simp only [cons_isPath_iff] at hP
  exact nontrivial_of_exists_ne (mem_insert ..) ⟨P.first, by simp, fun h ↦ hP.2.2 (by simp [← h])⟩


/-! ### Fixed ends. (To be cleaned up) -/


@[mk_iff]
structure IsTrailFrom (G : Graph α β) (S T : Set α) (W : WList α β) : Prop extends
  G.IsTrail W, G.IsWalkFrom S T W

@[mk_iff]
structure IsPathFrom (G : Graph α β) (S T : Set α) (P : WList α β) :
  Prop extends G.IsPath P, G.IsWalkFrom S T P where
  eq_first_of_mem : ∀ ⦃x⦄, x ∈ P → x ∈ S → x = P.first
  eq_last_of_mem : ∀ ⦃y⦄, y ∈ P → y ∈ T → y = P.last

lemma IsPathFrom.isPath (h : G.IsPathFrom S T P) : G.IsPath P where
  isWalk := h.isWalk
  nodup := h.nodup

@[simp] lemma nil_isPathFrom : G.IsPathFrom S T (nil x) ↔ x ∈ V(G) ∧ x ∈ S ∧ x ∈ T := by
  simp [isPathFrom_iff]

lemma IsPathFrom.reverse (h : G.IsPathFrom S T w) : G.IsPathFrom T S w.reverse where
  isWalk := h.isWalk.reverse
  nodup := by simp [h.nodup]
  first_mem := by simp [h.last_mem]
  last_mem := by simp [h.first_mem]
  eq_first_of_mem x hx hxT := by simp [h.eq_last_of_mem (y := x) (by simpa using hx) hxT]
  eq_last_of_mem x hx hxS := by simp [h.eq_first_of_mem (x := x) (by simpa using hx) hxS]

lemma IsPathFrom.subset_left {S₀ : Set α} (hP : G.IsPathFrom S T P) (hS₀ : S₀ ⊆ S)
    (hx : P.first ∈ S₀) : G.IsPathFrom S₀ T P where
  isWalk := hP.isWalk
  nodup := hP.nodup
  first_mem := hx
  last_mem := hP.last_mem
  eq_first_of_mem _ hxP hxS₀ := hP.eq_first_of_mem hxP <| hS₀ hxS₀
  eq_last_of_mem := hP.eq_last_of_mem

lemma IsPathFrom.subset_right {T₀ : Set α} (hP : G.IsPathFrom S T P) (hT₀ : T₀ ⊆ T)
    (hx : P.last ∈ T₀) : G.IsPathFrom S T₀ P := by
  simpa using (hP.reverse.subset_left hT₀ (by simpa)).reverse

lemma IsPathFrom.of_le (h : H.IsPathFrom S T P) (hle : H ≤ G) : G.IsPathFrom S T P where
  isWalk := h.isWalk.of_le hle
  nodup := h.nodup
  first_mem := h.first_mem
  last_mem := h.last_mem
  eq_first_of_mem := h.eq_first_of_mem
  eq_last_of_mem := h.eq_last_of_mem

lemma IsPathFrom.isPathFrom_le (h : G.IsPathFrom S T P) (hle : H ≤ G) (hss : E(P) ⊆ E(H))
    (hne : P.first ∈ V(H)) : H.IsPathFrom S T P where
  isWalk := h.isWalk.isWalk_le hle hss hne
  nodup := h.nodup
  first_mem := h.first_mem
  last_mem := h.last_mem
  eq_first_of_mem := h.eq_first_of_mem
  eq_last_of_mem := h.eq_last_of_mem

lemma isPathFrom_cons : G.IsPathFrom S T (cons x e P) ↔
    x ∈ S ∧ x ∉ T ∧ G.IsLink e x P.first ∧ Disjoint S V(P) ∧ G.IsPathFrom {P.first} T P := by
  refine ⟨fun h ↦ ⟨h.first_mem, fun hxT ↦ ?_, ?_, disjoint_left.2 fun v hvS hv ↦ ?_, ?_⟩,
    fun ⟨hxS, hxT, hinc, hdj, h⟩ ↦ ?_⟩
  · obtain rfl : x = P.last := h.eq_last_of_mem (y := x) (by simp) hxT
    simpa using h.isPath.nodup
  · exact (cons_isPath_iff.1 h.isPath).2.1
  · obtain rfl : v = x := h.eq_first_of_mem (x := v) (by simp [mem_vertexSet_iff.1 hv]) hvS
    have hnd := h.isPath.nodup
    simp only [cons_vertex, List.nodup_cons, mem_vertex] at hnd
    exact hnd.1 hv
  · refine IsPathFrom.mk (h.isPath.suffix (by simp)) rfl (by simpa using h.last_mem) (by simp) ?_
    exact fun y hyP hyT ↦ h.eq_last_of_mem (by simp [hyP]) hyT
  have hxP : x ∉ P := hdj.notMem_of_mem_left hxS
  refine IsPathFrom.mk (cons_isPath_iff.2 ⟨h.isPath, hinc, hxP⟩) (by simpa) h.last_mem ?_ ?_
  · simp only [mem_cons_iff, first_cons, forall_eq_or_imp, implies_true, true_and]
    exact fun a haP haS ↦ (hdj.notMem_of_mem_left haS haP).elim
  simpa [hxT] using h.eq_last_of_mem

/-- A version of `isPathFrom_cons` where the source set is a subgraph `H`,
and we get the additional condition that the first edge is not an edge of `H`. -/
lemma isPathFrom_cons_subgraph (hle : H ≤ G) : G.IsPathFrom V(H) T (cons x e P) ↔
    x ∈ V(H) ∧ x ∉ T ∧ G.IsLink e x P.first ∧ e ∉ E(H) ∧ Disjoint V(H) V(P) ∧
      G.IsPathFrom {P.first} T P := by
  simp only [and_congr_right_iff, iff_and_self, and_imp, isPathFrom_cons]
  exact fun _ _ he hdj _ heH ↦ hdj.notMem_of_mem_right (a := P.first) (by simp)
    ((he.of_le_of_mem hle heH).right_mem)

lemma IsPathFrom.notMem_left_of_dInc (h : G.IsPathFrom S T P) (hP : P.DInc e x y) : y ∉ S :=
  fun hyS ↦ hP.ne_first h.nodup (h.eq_first_of_mem hP.right_mem hyS)

lemma IsPathFrom.notMem_right_of_dInc (h : G.IsPathFrom S T P) (hP : P.DInc e x y) : x ∉ T :=
  fun hyT ↦ hP.ne_last h.nodup (h.eq_last_of_mem hP.left_mem hyT)

lemma IsTrailFrom.isTrail (h : G.IsTrailFrom S T w) : G.IsTrail w where
  isWalk := h.isWalk
  edge_nodup := h.edge_nodup

lemma IsTrailFrom.isWalkFrom (h : G.IsTrailFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem


lemma IsPathFrom.isWalkFrom (h : G.IsPathFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem

-- lemma IsPathFrom.isTrailFrom (h : G.IsPathFrom S T w) : G.IsTrailFrom S T w where
--   isWalk := h.isWalk
--   edge_nodup := h.isPath.isTrail.edge_nodup
--   first_mem := h.first_mem
--   last_mem := h.last_mem

-- lemma IsWalk.isTrail (hVd : G.IsWalk w) (hedge : w.edge.Nodup) : G.IsTrail w := ⟨hVd, hedge⟩

-- lemma IsWalk.isPath (hw : G.IsWalk w) (hvertex : w.vertex.Nodup) : G.IsPath w := ⟨hw, hvertex⟩

lemma IsWalk.isWalkFrom (hVd : G.IsWalk w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsWalkFrom S T w := ⟨hVd, hfirst, hlast⟩

lemma IsWalk.isTrailFrom (hVd : G.IsWalk w) (hedge : w.edge.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsTrailFrom S T w := ⟨⟨hVd, hedge⟩, hfirst, hlast⟩

lemma IsTrail.isPath (hT : G.IsTrail w) (hvertex : w.vertex.Nodup) : G.IsPath w :=
  ⟨hT.isWalk, hvertex⟩

lemma IsTrail.isTrailFrom (hT : G.IsTrail w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsTrailFrom S T w := ⟨hT, hfirst, hlast⟩

lemma nil_isWalkFrom (hx : x ∈ V(G)) (hxS : x ∈ S) (hxT : x ∈ T) : G.IsWalkFrom S T (nil x) :=
  ⟨IsWalk.nil hx, hxS, hxT⟩

@[simp] lemma nil_isWalkFrom_iff : G.IsWalkFrom S T (nil x) ↔ x ∈ V(G) ∧ x ∈ S ∧ x ∈ T := by
  simp [isWalkFrom_iff]

@[simp]
lemma cons_isTrailFrom : G.IsTrailFrom S T (cons x e w) ↔
    G.IsTrail w ∧ G.IsLink e x w.first ∧ e ∉ w.edge ∧ x ∈ S ∧ w.last ∈ T := by
  simp [isTrailFrom_iff, and_assoc]

-- @[simp]
-- lemma cons_isPathFrom : G.IsPathFrom S T (cons x e P) ↔
--     G.IsPath P ∧ G.IsLink e x P.first ∧ x ∉ P ∧ x ∈ S ∧ P.last ∈ T := by
--   simp [isPathFrom_iff, and_assoc]

@[simp]
lemma nil_isTrailFrom : G.IsTrailFrom S T (nil x) ↔ x ∈ V(G) ∧ x ∈ S ∧ x ∈ T := by
  simp [isTrailFrom_iff]


-- /-! ### The type of paths -/

-- protected def Path (G : Graph α β) : Type _ := {P // G.IsPath P}


/-! ### Longest Paths -/

lemma mem_of_adj_first_of_maximal_isPath (hP : Maximal (fun P ↦ G.IsPath P) P)
    (hx : G.Adj x P.first) : x ∈ P := by
  obtain ⟨e, he⟩ := hx
  refine by_contra fun hcon ↦ hcon ?_
  rw [show P = cons x e P by simpa [hP.prop, he, hcon] using hP.eq_of_le (y := cons x e P)]
  simp





end Graph
