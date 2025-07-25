import Matroid.Graph.WList.Sublist
import Matroid.Graph.Constructions.Basic

/-
This file defined predicates stating that an abstract walk `w` is a walk/trail/path of a graph `G`.
-/

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {F : Set β}
  {W w w₁ w₂ : WList α β} {S T : Set α}

open Graph WList Set

namespace Graph

/-- `G.IsWalk w` means that `w : WList α β` is a walk of `G : Graph α β`. -/
inductive IsWalk (G : Graph α β) : WList α β → Prop
  | nil {x} (hx : x ∈ V(G)) : G.IsWalk (nil x)
  | cons {x e w} (hw : G.IsWalk w) (h : G.IsLink e x w.first) : G.IsWalk (cons x e w)

@[simp]
lemma nil_isWalk_iff : G.IsWalk (nil x) ↔ x ∈ V(G) :=
  ⟨fun h ↦ by cases h with | _ => simp_all, IsWalk.nil⟩

@[simp]
lemma cons_isWalk_iff : G.IsWalk (cons x e w) ↔ G.IsLink e x w.first ∧ G.IsWalk w :=
  ⟨fun h ↦ by cases h with | _ => simp_all, fun h ↦ h.2.cons h.1⟩

@[simp]
lemma IsWalk.of_cons (hw : G.IsWalk (.cons x e w)) : G.IsWalk w := by
  simp_all

lemma IsWalk.vertex_mem_of_mem (h : G.IsWalk w) (hmem : x ∈ w) : x ∈ V(G) := by
  induction h with | nil => simp_all | @cons y f w hw h ih =>
    simp_all only [mem_cons_iff]
    exact hmem.elim (fun h' ↦ h' ▸ h.left_mem) ih

lemma IsWalk.edge_mem_of_mem (h : G.IsWalk w) (hmem : e ∈ w.edge) : e ∈ E(G) := by
  induction h with | nil => simp_all | @cons x f w hw h ih =>
    simp_all only [cons_edge, List.mem_cons]
    exact hmem.elim (fun h' ↦ h' ▸ h.edge_mem) ih

lemma IsWalk.exists_vertex_mem_of_edge_mem (h : G.IsWalk w) (he : e ∈ w.edge) :
    ∃ u v, u ∈ w ∧ v ∈ w ∧ G.IsLink e u v := by
  induction h with
  | nil => simp at he
  | @cons x f w hw h ih =>
    simp_all only [cons_edge, List.mem_cons, mem_cons_iff]
    refine he.elim ?_ fun h' ↦ ?_
    · rintro rfl
      use x, w.first
      simpa
    obtain ⟨u, v, hu, hv, huv⟩ := ih h'
    use u, v
    tauto

lemma IsWalk.mem_of_mem_edge_of_inc [Nodup G] (hw : G.IsWalk w) (he : e ∈ w.edge) (h : G.Inc e u) :
    u ∈ w := by
  induction w with
  | nil x => simp at he
  | cons x e' w ih =>
    simp_all only [forall_const, cons_edge, List.mem_cons, mem_cons_iff, cons_isWalk_iff]
    obtain rfl | he := he
    · obtain rfl | rfl := h.eq_or_eq_of_isLink hw.1 <;> simp
    exact .inr (ih he)

lemma IsWalk.first_mem (h : G.IsWalk w) : w.first ∈ V(G) :=
  h.vertex_mem_of_mem (by simp)

lemma IsWalk.last_mem (h : G.IsWalk w) : w.last ∈ V(G) :=
  h.vertex_mem_of_mem (by simp)

lemma IsWalk.vertexSet_subset (hVd : G.IsWalk w) : V(w) ⊆ V(G) :=
  fun _ ↦ hVd.vertex_mem_of_mem

lemma IsWalk.edgeSet_subset (h : G.IsWalk w) : E(w) ⊆ E(G) := fun _ ↦ h.edge_mem_of_mem

lemma IsWalk.sublist (hw₂ : G.IsWalk w₂) (h : w₁.IsSublist w₂) : G.IsWalk w₁ := by
  induction h with
  | nil h => simp [hw₂.vertex_mem_of_mem h]
  | cons x e h ih => exact ih hw₂.of_cons
  | cons₂ x e h h_eq ih =>
    rw [cons_isWalk_iff] at hw₂ ⊢
    rw [h_eq]
    exact ⟨hw₂.1, ih hw₂.2⟩

lemma IsWalk.prefix (hw : G.IsWalk w) (h : w₁.IsPrefix w) : G.IsWalk w₁ :=
  hw.sublist h.isSublist

lemma IsWalk.suffix (hw : G.IsWalk w) (h : w₁.IsSuffix w) : G.IsWalk w₁ :=
  hw.sublist h.isSublist

lemma IsWalk.tail (hw : G.IsWalk w) : G.IsWalk w.tail :=
  hw.suffix w.tail_isSuffix

lemma IsWalk.dropLast (hw : G.IsWalk w) : G.IsWalk w.dropLast :=
  hw.prefix w.dropLast_isPrefix

lemma IsWalk.append (h₁ : G.IsWalk w₁) (h₂ : G.IsWalk w₂) (h : w₁.last = w₂.first) :
  G.IsWalk (w₁ ++ w₂) := by
  induction h₁ with simp_all

lemma IsWalk.concat (h : G.IsWalk w) (he : G.IsLink e w.last x) : G.IsWalk (w.concat e x) := by
  induction h with simp_all [he.right_mem]

lemma IsWalk.of_concat (h : G.IsWalk (w.concat e x)) : G.IsWalk w := by
  induction w with
  | nil u =>
    simp_all only [nil_concat, cons_isWalk_iff, nil_first, nil_isWalk_iff]
    exact h.1.left_mem
  | cons u f w ih =>
    rw [cons_concat, cons_isWalk_iff] at h
    exact (ih h.2).cons (by simpa using h.1)

@[simp]
lemma isWalk_concat_iff : G.IsWalk (w.concat e x) ↔ G.IsWalk w ∧ G.IsLink e w.last x :=
  ⟨fun h ↦ ⟨h.of_concat, by induction w with simp_all⟩, fun h ↦ h.1.concat h.2⟩

lemma IsWalk.of_append_left (h : G.IsWalk (w₁ ++ w₂)) (h_eq : w₁.last = w₂.first) :
    G.IsWalk w₁ :=
  h.prefix <| isPrefix_append_right h_eq

lemma IsWalk.of_append_right (h : G.IsWalk (w₁ ++ w₂)) : G.IsWalk w₂ :=
  h.suffix <| isSuffix_append_left ..

lemma IsWalk.last_dup_first (h : G.IsWalk (w₁ ++ w₂)) (hw₁ : G.IsWalk w₁) (hne : w₁.Nonempty) :
    G.Dup w₁.last w₂.first := by
  induction hw₁ with
  | nil => simp_all
  | @cons x e w hw h' IH => cases w with
    | nil u =>
      simp only [nil_first, WList.cons_append, WList.nil_append, cons_isWalk_iff] at h' h
      exact h'.right_unique_dup h.1
    | cons => simp_all

lemma IsWalk.last_eq_first [Nodup G] (h : G.IsWalk (w₁ ++ w₂)) (hw₁ : G.IsWalk w₁)
    (hne : w₁.Nonempty) : w₁.last = w₂.first := by
  induction hw₁ with
  | nil => simp_all
  | @cons x e w hw h' IH => cases w with
    | nil u =>
      simp only [nil_first, WList.cons_append, WList.nil_append, cons_isWalk_iff] at h' h
      exact h'.right_unique h.1
    | cons => simp_all

lemma IsWalk.reverse (hw : G.IsWalk w) : G.IsWalk w.reverse := by
  induction hw with
  | nil => simp_all
  | cons hw h ih =>
    simp_all only [WList.reverse_cons]
    apply ih.concat <| by simpa using h.symm

@[simp]
lemma isWalk_reverse_iff : G.IsWalk w.reverse ↔ G.IsWalk w :=
  ⟨fun h ↦ by simpa using h.reverse, IsWalk.reverse⟩

lemma IsWalk.of_isLabelSubgraph (h : H.IsWalk w) (hlle : H ≤l G) : G.IsWalk w := by
  induction h with
  | nil hx => simp [hlle.vertexSet hx]
  | cons _ h ih => simp [ih, hlle.isLink h]

lemma IsWalk.of_le (h : H.IsWalk w) (hle : H ≤ G) : G.IsWalk w := by
  induction h with
  | nil hx => simp [vertexSet_mono hle hx]
  | cons _ h ih => simp [ih, h.of_le hle]

lemma IsWalk.isWalk_isLabelSubgraph (h : G.IsWalk w) (hlle : H ≤l G) (hE : E(w) ⊆ E(H))
    (hV : V(w) ⊆ V(H)) : H.IsWalk w := by
  induction h with
  | nil => simp_all
  | @cons x e w hw h ih =>
    simp_all only [cons_edgeSet, insert_subset_iff, cons_vertexSet, cons_isWalk_iff, and_true,
      forall_const]
    exact h.of_isLabelSubgraph_of_mem_mem hlle hE.1 hV.1 (hV.2 <| by simp)

lemma IsWalk.isWalk_le (h : G.IsWalk w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hfirst : w.first ∈ V(H)) : H.IsWalk w := by
  induction h with
  | nil => simp_all
  | @cons x e w hw h ih =>
    simp_all only [cons_edgeSet, insert_subset_iff, cons_isWalk_iff, forall_const]
    exact ⟨h.of_le_of_mem hle hE.1, ih (h.of_le_of_mem hle hE.1).right_mem⟩

lemma IsWalk.isWalk_isInducedSubgraph (h : G.IsWalk w) (hind : H ≤i G) (hX : V(w) ⊆ V(H)) :
    H.IsWalk w := by
  induction h with
  | nil => simp_all
  | @cons x e w hw h ih =>
    simp_all only [cons_vertexSet, insert_subset_iff, cons_isWalk_iff, and_true, forall_const]
    exact hind.isLink_of_mem_mem h hX.1 <| ih.first_mem

lemma IsWalk.isWalk_isClosedSubgraph (h : G.IsWalk w) (hcl : H ≤c G) (hfirst : w.first ∈ V(H)) :
    H.IsWalk w := by
  refine h.isWalk_isInducedSubgraph hcl.isInducedSubgraph fun x hx => ?_
  induction h with
  | nil hx => simp_all
  | cons hw h ih =>
    simp_all only [mem_vertexSet_iff, first_cons, cons_vertexSet, mem_insert_iff]
    obtain rfl | hx := hx
    · exact hfirst
    exact ih ((hcl.mem_iff_mem_of_isLink h).mp hfirst) hx

lemma IsWalk.isWalk_le_of_nonempty (h : G.IsWalk w) (hle : H ≤ G) (hE : E(w) ⊆ E(H))
    (hne : w.Nonempty) : H.IsWalk w := by
  by_cases hfirst : w.first ∈ V(H)
  · exact h.isWalk_le hle hE hfirst
  cases w with
  | nil => simp at hne
  | cons u e w =>
    simp only [cons_edgeSet, insert_subset_iff] at hE
    rw [cons_isWalk_iff] at h
    simp_all [(h.1.of_le_of_mem hle hE.1).left_mem]

lemma IsWalk.isLink_of_isLink (h : G.IsWalk w) (hexy : w.IsLink e x y) : G.IsLink e x y := by
  induction hexy with
  | cons_left => simp_all
  | cons_right => exact IsLink.symm <| by simp_all
  | cons => simp_all

lemma IsWalk.isLink_of_dInc (h : G.IsWalk w) (hexy : w.DInc e x y) : G.IsLink e x y :=
  h.isLink_of_isLink hexy.isLink

lemma IsWalk.wellFormed [Nodup G] (h : G.IsWalk w) : w.WellFormed := by
  induction w with
  | nil u => simp [WellFormed]
  | cons u e w ih =>
    simp only [cons_isWalk_iff] at h
    rw [cons_wellFormed_iff, and_iff_right (ih h.2)]
    exact fun y₁ y₂ h' ↦ (h.2.isLink_of_isLink h').isLink_iff_sym2_eq.1 h.1

lemma IsWalk.isLink_iff_isLink_of_mem [Nodup G] (h : G.IsWalk w) (hew : e ∈ w.edge) :
    w.IsLink e x y ↔ G.IsLink e x y := by
  refine ⟨h.isLink_of_isLink, fun h' ↦ ?_⟩
  obtain ⟨x', y', hx'y'⟩ := exists_isLink_of_mem_edge hew
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h'.eq_and_eq_or_eq_and_eq (h.isLink_of_isLink hx'y')
  · assumption
  exact hx'y'.symm

lemma IsWalk.eq_of_edge_eq_first_eq [Nodup G] (h₁ : G.IsWalk w₁) (h₂ : G.IsWalk w₂)
    (h_first : w₁.first = w₂.first) (h_edge : w₁.edge = w₂.edge) : w₁ = w₂ := by
  induction h₁ generalizing w₂ with
  | @nil x h => cases w₂ with
    | nil u => simpa using h_first
    | cons u e w => simp at h_edge
  | @cons x e w₁ hw h ih =>
    cases w₂ with
    | nil u => simp at h_edge
    | cons u f w₂ =>
    · simp only [cons_edge, List.cons.injEq, first_cons, cons_isWalk_iff] at h_edge h_first h₂
      rw [← h_edge.1, ← h_first, h.isLink_iff_eq] at h₂
      rw [h_edge.1, h_first, ih h₂.2 h₂.1.symm h_edge.2]

/-- `G.IsWalkFrom S T w` means that `w` is a walk of `G` with one end in `S` and the other in `T`.-/
@[mk_iff]
structure IsWalkFrom (G : Graph α β) (S T : Set α) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  first_mem : w.first ∈ S
  last_mem : w.last ∈ T

lemma IsWalkFrom.of_isLabelSubgraph (h : H.IsWalkFrom S T w) (hlle : H ≤l G) : G.IsWalkFrom S T w :=
  ⟨h.isWalk.of_isLabelSubgraph hlle, h.first_mem, h.last_mem⟩

lemma IsWalkFrom.of_le (h : G.IsWalkFrom S T w) (hle : G ≤ H) : H.IsWalkFrom S T w :=
  ⟨h.isWalk.of_le hle, h.first_mem, h.last_mem⟩

lemma IsWalkFrom.reverse (h : G.IsWalkFrom S T w) : G.IsWalkFrom T S w.reverse where
  isWalk := h.isWalk.reverse
  first_mem := by simp [h.last_mem]
  last_mem := by simp [h.first_mem]

/-- The walk corresponding to an incidence `G.IsLink e u v`. -/
def IsLink.walk (_h : G.IsLink e u v) : WList α β := cons u e (nil v)

namespace IsLink

@[simp]
lemma walk_first (h : G.IsLink e u v): h.walk.first = u := rfl

@[simp]
lemma walk_last (h : G.IsLink e u v): h.walk.last = v := rfl

@[simp]
lemma walk_vertex (h : G.IsLink e u v): h.walk.vertex = [u, v] := rfl

lemma mem_walk_iff (h : G.IsLink e u v) (x : α) : x ∈ h.walk ↔ x = u ∨ x = v := by
  simp [walk]

@[simp]
lemma walk_vertexSet (h : G.IsLink e u v): V(h.walk) = {u, v} := by
  simp [mem_walk_iff, Set.ext_iff]

@[simp]
lemma walk_edge (h : G.IsLink e u v): h.walk.edge = [e] := rfl

@[simp]
lemma walk_edgeSet (h : G.IsLink e u v): E(h.walk) = {e} := by
  simp [WList.edgeSet]

@[simp]
lemma walk_length (h : G.IsLink e u v): h.walk.length = 1 := rfl

@[simp]
lemma walk_isWalk (h : G.IsLink e u v) : G.IsWalk h.walk := by
  simp [walk, h, h.right_mem]

end IsLink

section Subgraph

variable {X : Set α}

-- lemma IsWalk.induce (hw : G.IsWalk w) (hX : V(w) ⊆ X) : G[X].IsWalk w := by
--   induction hw with
--   | nil => simp_all
--   | @cons x e w hw h ih =>
--     simp_all only [cons_vertexSet, insert_subset_iff, cons_isWalk_iff, induce_isLink_iff, true_and,
--       and_true, forall_const]
--     refine hX.2 <| by simp

-- lemma isWalk_induce_iff' (hw : w.Nonempty) : G[X].IsWalk w ↔ G.IsWalk w ∧ V(w) ⊆ X := by
--   refine ⟨fun h ↦ ⟨?_, h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩
--   induction w with
--   | nil => simp at hw
--   | cons u e w ih => cases w with
--     | nil v =>
--       simp only [cons_isWalk_iff, nil_first, induce_isLink_iff, nil_isWalk_iff,
--         induce_vertexSet] at h ⊢
--       exact ⟨h.1.1, h.1.1.right_mem⟩
--     | cons v f w => simp_all

-- /-- This is almost true without the `X ⊆ V(G)` assumption; the exception is where
-- `w` is a nil walk on a vertex in `X \ V(G)`. -/
-- lemma isWalk_induce_iff (hXV : X ⊆ V(G)) : G[X].IsWalk w ↔ G.IsWalk w ∧ V(w) ⊆ X :=
--   ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩

-- lemma IsWalk.vertexSet_subset_of_induce (hw : G[X].IsWalk w) : V(w) ⊆ X :=
--   fun _ hxw => hw.vertex_mem_of_mem hxw

@[simp]
lemma isWalk_vertexDelete_iff : (G - X).IsWalk w ↔ G.IsWalk w ∧ Disjoint V(w) X := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp +contextual only [cons_isWalk_iff, vertexDelete_isLink, ih, cons_vertexSet,
      disjoint_insert_left, iff_def, and_self, not_false_eq_true, implies_true, true_and, and_true,
      and_imp]
    exact fun _ _ _ hdisj ↦ hdisj.notMem_of_mem_left first_mem

lemma IsWalk.vertexDelete (hw : G.IsWalk w) (hdisj : Disjoint V(w) X) : (G - X).IsWalk w := by
  simp [hw, hdisj]

lemma IsWalk.disjoint_of_vertexDelete (hw : (G - X).IsWalk w) : Disjoint V(w) X :=
  (isWalk_vertexDelete_iff.mp hw).2

lemma IsWalk.edgeRestrict (hw : G.IsWalk w) (hE : E(w) ⊆ F) : (G ↾ F).IsWalk w := by
  induction hw with simp_all [insert_subset_iff]

@[simp]
lemma isWalk_edgeRestrict_iff {F : Set β} : (G ↾ F).IsWalk w ↔ G.IsWalk w ∧ E(w) ⊆ F :=
  ⟨fun h ↦ ⟨h.of_le (by simp), h.edgeSet_subset.trans inter_subset_left⟩,
    fun h ↦ h.1.edgeRestrict h.2⟩

lemma IsWalk.edgeSet_subset_of_edgeRestrict (hw : (G ↾ F).IsWalk w) : E(w) ⊆ F :=
  (isWalk_edgeRestrict_iff.mp hw).2

@[simp]
lemma isWalk_edgeDelete_iff {F : Set β} : (G ＼ F).IsWalk w ↔ G.IsWalk w ∧ Disjoint E(w) F := by
  simp only [edgeDelete_eq_edgeRestrict, isWalk_edgeRestrict_iff, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.edgeSet_subset

lemma IsWalk.disjoint_of_edgeDelete (hw : (G ＼ F).IsWalk w) : Disjoint E(w) F :=
  (isWalk_edgeDelete_iff.mp hw).2

lemma IsWalk.eq_append_cons_of_edge_mem (hW : G.IsWalk W) (heW : e ∈ W.edge) :
    ∃ W₁ W₂, G.IsWalk W₁ ∧ G.IsWalk W₂ ∧ e ∉ W₁.edge ∧ W = W₁ ++ WList.cons W₁.last e W₂ := by
  obtain ⟨W₁, W₂, rfl, heW₁⟩ := WList.eq_append_cons_of_edge_mem heW
  refine ⟨W₁, W₂, hW.prefix (isPrefix_append_right rfl), hW.suffix ?_, heW₁, rfl⟩
  exact IsSuffix.trans (isSuffix_cons_self W₂ e W₁.last) <| isSuffix_append_left ..

end Subgraph


-- lemma IsPath.prefix (hP : G.IsPath w) (hPf : w₁.IsPrefix w) : G.IsPath w₁ := by
--   refine ⟨hP.isWalk.prefix hPf, ?_⟩

  -- obtain ⟨w₂, heq, rfl⟩ := hPf.exists_eq_append
  -- exact append_left_isPath heq hP



-- lemma append_isWalkFrom (h : w₁.last = w₂.first) (h₁ : G.IsWalkFrom S T w₁)
--     (h₂ : G.IsWalkFrom T U w₂) : G.IsWalkFrom S U (w₁ ++ w₂) := by
--   obtain ⟨hw₁Vd, hw₁first, hw₁last⟩ := h₁
--   obtain ⟨hw₂Vd, hw₂first, hw₂last⟩ := h₂
--   refine ⟨?_, ?_, ?_⟩
--   · exact WList.append_isWalk h hw₁Vd hw₂Vd
--   · simpa [h]
--   · simpa



-- lemma append_isPath (h : w₁.last = w₂.first) (h₁ : G.IsPath w₁) (h₂ : G.IsPath w₂)
--     (hvertexSet : w₁.vertexSet ∩ w₂.vertexSet ⊆ {w₁.last}) : G.IsPath (w₁ ++ w₂) where
--   isWalk := append_isWalk h h₁.isWalk h₂.isWalk
--   nodup := by
--     simp only [Set.subset_singleton_iff, Set.mem_inter_iff, mem_vertexSet_iff,
-- and_imp, append_vertex,
--       nodup_append, h₁.nodup.sublist w₁.vertex.dropLast_sublist, h₂.nodup, true_and] at
-- hvertexSet ⊢
--     rintro x hx₁ hx₂
--     obtain rfl := hvertexSet x (List.mem_of_mem_dropLast hx₁) hx₂
--     /- This should be its own lemma -/
--     have aux {l : List α} (hl : l ≠ []) (hl' : l.Nodup) : l.getLast hl ∉ l.dropLast := by
--       rw [← dropLast_append_getLast hl, nodup_append] at hl'
--       obtain ⟨-, h'⟩ := by simpa using hl'
--       assumption
--     rw [last_eq_vertex_getLast] at hx₁
--     apply aux (by simp) h₁.nodup hx₁

-- @[simp] lemma cons_isWalkFrom : G.IsWalkFrom S T (cons x e w) ↔
--     G.IsWalk w ∧ G.IsLink e x w.first ∧ x ∈ S ∧ w.last ∈ T := by
--   refine ⟨fun ⟨h, hS, hT⟩ ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hV, hS, hVd, hT⟩ ↦ ⟨?_, ?_, ?_⟩⟩
--   <;> simp_all only [cons_isWalk, first_cons, last_cons, and_self]


  -- induction w with
  -- | nil x => simp [reverse, hVd]
  -- | cons x e w ih =>
  --   simp only [cons_isWalk, reverse_cons] at hVd ⊢
  --   refine ValidIn.concat (ih hVd.2) ?_
  --   simp [hVd.1.symm]


@[simp]
lemma reverse_isWalk_iff : G.IsWalk w.reverse ↔ G.IsWalk w :=
  ⟨fun h ↦ by simpa using h.reverse, IsWalk.reverse⟩


lemma IsWalk.dedup [DecidableEq α] (h : G.IsWalk w) : G.IsWalk w.dedup :=
  h.sublist w.dedup_isSublist


-- lemma _root_.Graph.IsPath.IsSuffix (hPf : w₁.IsSuffix w) (hP : G.IsPath w) : G.IsPath w₁ := by
--   simpa using hP.reverse.IsPrefix <| reverse_isPrefix_reverse_iff.2 hPf
