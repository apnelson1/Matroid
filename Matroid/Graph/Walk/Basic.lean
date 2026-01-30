import Matroid.Graph.WList.TakeDrop
import Matroid.Graph.Subgraph.Delete

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

lemma IsWalk.vertex_mem_of_edge_mem (h : G.IsWalk w) (he : e ∈ w.edge) (heu : G.Inc e u) :
    u ∈ w := by
  induction h with
  | nil => simp at he
  | @cons x f w hw h ih =>
    simp_all only [cons_edge, List.mem_cons, mem_cons_iff]
    refine he.elim ?_ fun h' ↦ .inr <| ih h'
    rintro rfl
    obtain rfl | rfl := heu.eq_or_eq_of_isLink h <;> simp

lemma IsWalk.first_mem (h : G.IsWalk w) : w.first ∈ V(G) :=
  h.vertex_mem_of_mem (by simp)

lemma IsWalk.last_mem (h : G.IsWalk w) : w.last ∈ V(G) :=
  h.vertex_mem_of_mem (by simp)

lemma IsWalk.vertexSet_subset (hVd : G.IsWalk w) : V(w) ⊆ V(G) :=
  fun _ ↦ hVd.vertex_mem_of_mem

lemma IsWalk.edgeSet_subset (h : G.IsWalk w) : E(w) ⊆ E(G) := fun _ ↦ h.edge_mem_of_mem

@[simp]
lemma not_isWalk_bot : ¬ (⊥ : Graph α β).IsWalk w := by
  rintro h
  simpa using h.first_mem

lemma IsWalk.mem_of_mem_edge_of_inc (hw : G.IsWalk w) (he : e ∈ w.edge) (h : G.Inc e u) :
    u ∈ w := by
  induction w with
  | nil x => simp at he
  | cons x e' w ih =>
    simp_all only [forall_const, cons_edge, List.mem_cons, mem_cons_iff, cons_isWalk_iff]
    obtain rfl | he := he
    · obtain rfl | rfl := h.eq_or_eq_of_isLink hw.1 <;> simp
    exact .inr (ih he)

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
lemma concat_isWalk_iff : G.IsWalk (w.concat e x) ↔ G.IsWalk w ∧ G.IsLink e w.last x :=
  ⟨fun h ↦ ⟨h.of_concat, by induction w with simp_all⟩, fun h ↦ h.1.concat h.2⟩

lemma IsWalk.of_append_left (h : G.IsWalk (w₁ ++ w₂)) (h_eq : w₁.last = w₂.first) :
    G.IsWalk w₁ :=
  h.prefix <| isPrefix_append_right h_eq

lemma IsWalk.of_append_right (h : G.IsWalk (w₁ ++ w₂)) : G.IsWalk w₂ :=
  h.suffix <| isSuffix_append_left ..

lemma IsWalk.last_eq_first (h : G.IsWalk (w₁ ++ w₂)) (hw₁ : G.IsWalk w₁) (hne : w₁.Nonempty) :
    w₁.last = w₂.first := by
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

lemma IsWalk.deloop [DecidableEq α] (h : G.IsWalk w) : G.IsWalk w.deloop :=
  h.sublist w.deloop_isSublist

lemma IsWalk.deloop_edge_eq_filter [DecidableEq α] [DecidablePred (∀ x, ¬ G.IsLoopAt · x)]
    (h : G.IsWalk w) : w.deloop.edge = w.edge.filter (∀ x, ¬ G.IsLoopAt · x) := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [cons_isWalk_iff, deloop_cons_eq_ite, cons_edge] at h ⊢
    specialize ih h.2
    split_ifs with heq
    · subst heq
      rwa [List.filter_cons_of_neg]
      simp only [decide_eq_true_eq, not_forall, not_not]
      use w.first, h.1
    rw [List.filter_cons_of_pos, WList.cons_edge, ih]
    simp only [decide_eq_true_eq]
    rintro x hex
    obtain rfl := hex.eq_of_inc h.1.inc_left
    exact heq <| hex.eq_of_inc h.1.inc_right

@[simp]
lemma IsWalk.mem_deloop_edge_iff [DecidableEq α] (h : G.IsWalk w) (e : β) :
    e ∈ w.deloop.edge ↔ e ∈ w.edge ∧ ∀ x, ¬ G.IsLoopAt e x := by
  classical
  simp [h.deloop_edge_eq_filter]

lemma edgeRemove_first (hF : ∀ e ∈ w.edge, e ∈ F → ∃ x, G.IsLoopAt e x)
    [DecidablePred (· ∈ F)] (hw : G.IsWalk w) : (w.edgeRemove F).first = w.first := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_isWalk_iff, cons_edge, List.mem_cons] at hw hF
    rw [edgeRemove_cons]
    split_ifs with he; swap
    · simp
    obtain ⟨x, hex⟩ := hF e (.inl rfl) he
    obtain rfl := hex.eq_of_inc hw.1.inc_left
    obtain rfl := hex.eq_of_inc hw.1.inc_right
    exact ih (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2

lemma edgeRemove_isSublist (hF : ∀ e ∈ w.edge, e ∈ F → ∃ x, G.IsLoopAt e x)
    [DecidablePred (· ∈ F)] (hw : G.IsWalk w) : (w.edgeRemove F).IsSublist w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_isWalk_iff, cons_edge, List.mem_cons] at hw hF
    rw [edgeRemove_cons]
    split_ifs with he
    · exact (ih (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2).trans (by simp)
    · exact (ih (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2).cons₂ _ _
        (edgeRemove_first (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2)

@[simp]
lemma mem_edgeRemove_iff (hF : ∀ e ∈ w.edge, e ∈ F → ∃ x, G.IsLoopAt e x)
    [DecidablePred (· ∈ F)] (hw : G.IsWalk w) : x ∈ w.edgeRemove F ↔ x ∈ w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_isWalk_iff, cons_edge, List.mem_cons, mem_cons_iff] at hw hF ⊢
    rw [edgeRemove_cons]
    split_ifs with he; swap
    · simp [ih (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2]
    obtain ⟨y, hey⟩ := hF e (.inl rfl) he
    obtain rfl := hey.eq_of_inc hw.1.inc_left
    obtain rfl := hey.eq_of_inc hw.1.inc_right
    simp only [ih (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2, iff_or_self]
    exact fun h ↦ h ▸ first_mem

lemma IsWalk.edgeRemove [DecidablePred (· ∈ F)] (hw : G.IsWalk w)
    (hF : ∀ e ∈ w.edge, e ∈ F → ∃ x, G.IsLoopAt e x) : G.IsWalk (w.edgeRemove F) := by
  induction w with
  | nil => simp_all
  | cons u e w ih =>
    simp only [cons_isWalk_iff, cons_edge, List.mem_cons] at hw hF
    rw [edgeRemove_cons]
    split_ifs with he
    · exact ih hw.2 (fun f hf hfF ↦ hF f (.inr hf) hfF)
    · refine cons_isWalk_iff.mpr ⟨?_, ih hw.2 (fun f hf hfF ↦ hF f (.inr hf) hfF)⟩
      rw [edgeRemove_first (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2]
      exact hw.1

lemma deloop_isSublist_edgeRemove [DecidableEq α] [DecidablePred (· ∈ F)]
    (hw : G.IsWalk w) (hF : ∀ e ∈ w.edge, e ∈ F → ∃ x, G.IsLoopAt e x) :
    w.deloop.IsSublist (w.edgeRemove F) := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_isWalk_iff, cons_edge, List.mem_cons] at hw hF
    rw [deloop_cons_eq_ite, edgeRemove_cons]
    split_ifs with huwf heF heF
    · exact ih hw.2 (fun f hf hfF ↦ hF f (.inr hf) hfF)
    · subst u
      exact (ih hw.2 (fun f hf hfF ↦ hF f (.inr hf) hfF)).cons ..
    · obtain ⟨x, hex⟩ := hF e (.inl rfl) heF
      obtain rfl := hex.eq_of_inc hw.1.inc_left
      exact (huwf <| hex.eq_of_inc hw.1.inc_right).elim
    apply (ih hw.2 (fun f hf hfF ↦ hF f (.inr hf) hfF)).cons₂
    rw [edgeRemove_first (fun f hf hfF ↦ hF f (.inr hf) hfF) hw.2, deloop_first]

lemma edgeRemove_eq_deloop [DecidableEq α] [DecidablePred (· ∈ F)]
    (hw : G.IsWalk w) (hF : ∀ e ∈ w.edge, e ∈ F ↔ (∃ x, G.IsLoopAt e x)) :
    w.edgeRemove F = w.deloop := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    simp only [cons_isWalk_iff, cons_edge, List.mem_cons] at hw hF
    rw [deloop_cons_eq_ite, edgeRemove_cons]
    split_ifs with heF huwf huwf
    on_goal 2 =>
      obtain ⟨x, hex⟩ := hF e (.inl rfl) |>.mp heF
      obtain rfl := hex.eq_of_inc hw.1.inc_left
      exact (huwf <| hex.eq_of_inc hw.1.inc_right).elim
    all_goals simp_all

lemma edgeRemove_eq_self_of_noloop [DecidablePred (· ∈ F)] (hw : G.IsWalk w)
    (hF : ∀ e ∈ w.edge, e ∈ F → ∃ x, G.IsLoopAt e x) (hnl : w.NoLoop) : w.edgeRemove F = w := by
  classical
  apply (edgeRemove_isSublist hF hw).antisymm
  nth_rw 1 [← deloop_eq_self_iff.mpr hnl]
  exact deloop_isSublist_edgeRemove hw hF

lemma IsWalk.of_forall_isLink (h : G.IsWalk w) (he : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink e x y)
    (hne : w.Nonempty) : H.IsWalk w := by
  induction h with
  | nil hx => simp at hne
  | cons hw h ih =>
    rename_i w
    simp only [cons_isWalk_iff, he h, true_and]
    refine w.nil_or_nonempty.elim (fun hnil ↦ ?_) ih
    rw [hnil.eq_nil_first]
    simp [he h |>.right_mem]

lemma IsWalk.of_le (h : H.IsWalk w) (hle : H ≤ G) : G.IsWalk w := by
  induction h with
  | nil hx => simp [vertexSet_mono hle hx]
  | cons _ h ih => simp [ih, h.of_le hle]

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

lemma IsWalk.subset_of_first_mem_isClosedSubgraph (h : G.IsWalk w) (hcl : H ≤c G)
    (hfirst : w.first ∈ V(H)) : V(w) ⊆ V(H) := by
  rintro x hx
  induction h with
  | nil hx => simp_all
  | cons hw h ih =>
    simp_all only [mem_vertexSet_iff, first_cons, cons_vertexSet, mem_insert_iff]
    obtain rfl | hx := hx
    · exact hfirst
    exact ih ((IsClosedSubgraph.mem_iff_mem_of_isLink hcl h).mp hfirst) hx

lemma IsWalk.subset_of_isClosedSubgraph (h : G.IsWalk w) (hcl : H ≤c G)
    (hx : ∃ x ∈ V(w), x ∈ V(H)) : V(w) ⊆ V(H) := by
  classical
  rw [← w.prefixUntil_append_suffixFrom (· ∈ V(H)), append_vertexSet_of_eq (by simp),
    union_subset_iff]
  refine ⟨?_, (h.suffix (w.suffixFrom_isSuffix _)).subset_of_first_mem_isClosedSubgraph hcl
  <| suffixFrom_prop_first hx⟩
  rw [← reverse_vertexSet]
  apply (h.prefix (w.prefixUntil_isPrefix _) |>.reverse).subset_of_first_mem_isClosedSubgraph hcl
  rw [reverse_first]
  exact prefixUntil_prop_last hx

lemma IsWalk.isWalk_isClosedSubgraph_of_first_mem (h : G.IsWalk w) (hcl : H ≤c G)
    (hfirst : w.first ∈ V(H)) : H.IsWalk w :=
  h.isWalk_isInducedSubgraph hcl.isInducedSubgraph
  <| h.subset_of_first_mem_isClosedSubgraph hcl hfirst

lemma IsWalk.isWalk_isClosedSubgraph (h : G.IsWalk w) (hcl : H ≤c G)
    (hx : ∃ x ∈ V(w), x ∈ V(H)) : H.IsWalk w :=
  h.isWalk_isInducedSubgraph hcl.isInducedSubgraph
  <| h.subset_of_isClosedSubgraph hcl hx

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

lemma IsWalk.wellFormed (h : G.IsWalk w) : w.WellFormed := by
  induction w with
  | nil u => simp [WellFormed]
  | cons u e w ih =>
    simp only [cons_isWalk_iff] at h
    rw [cons_wellFormed_iff, and_iff_right (ih h.2)]
    exact fun y₁ y₂ h' ↦ (h.2.isLink_of_isLink h').isLink_iff_sym2_eq.1 h.1

lemma IsWalk.isLink_iff_isLink_of_mem (h : G.IsWalk w) (hew : e ∈ w.edge) :
    w.IsLink e x y ↔ G.IsLink e x y := by
  refine ⟨h.isLink_of_isLink, fun h' ↦ ?_⟩
  obtain ⟨x', y', hx'y'⟩ := exists_isLink_of_mem_edge hew
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h'.eq_and_eq_or_eq_and_eq (h.isLink_of_isLink hx'y')
  · assumption
  exact hx'y'.symm

lemma IsWalk.eq_of_edge_eq_first_eq (h₁ : G.IsWalk w₁) (h₂ : G.IsWalk w₂)
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

lemma IsWalk.not_loopAt_of_noLoop (h : G.IsWalk w) (hloop : w.NoLoop) (he : e ∈ w.edge) :
    ∀ x, ¬ G.IsLoopAt e x := by
  rintro x hx
  rw [IsLoopAt, ← h.isLink_iff_isLink_of_mem he] at hx
  simp [hloop] at hx

/-- `G.IsWalkFrom S T w` means that `w` is a walk of `G` with one end in `S` and the other in `T`.-/
@[mk_iff]
structure IsWalkFrom (G : Graph α β) (S T : Set α) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  first_mem : w.first ∈ S
  last_mem : w.last ∈ T

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

lemma Isolated.eq_last_of_mem (hisol : G.Isolated x) {w} (hw : G.IsWalk w) (hx : x ∈ w) :
    x = w.last := by
  classical
  obtain hw' | hw' := (w.suffixFromVertex x).nil_or_nonempty
  · obtain heq := w.suffixFromVertex_first hx
    rw [hw'.first_eq_last, suffixFromVertex_last] at heq
    exact heq.symm
  exfalso
  obtain ⟨u, e, w', heq⟩ := hw'.exists_cons
  obtain rfl := by simpa [heq] using w.suffixFromVertex_first hx
  have := heq ▸ (hw.suffix <| w.suffixFromVertex_isSuffix u)
  simp only [cons_isWalk_iff] at this
  exact hisol.not_isLink this.1

lemma Isolated.eq_first_of_mem (hisol : G.Isolated x) (hw : G.IsWalk w) (hx : x ∈ w) :
    x = w.first := by
  simpa using hisol.eq_last_of_mem (w := w.reverse) hw.reverse (by simpa)

lemma Isolated.isWalk_nil_of_mem (hisol : G.Isolated x) (hw : G.IsWalk w) (hx : x ∈ w) :
    w.Nil := by
  match w with
  | .nil u => simp
  | .cons u e w =>
    obtain rfl := by simpa using hisol.eq_first_of_mem hw hx
    simp only [cons_isWalk_iff] at hw
    exact (hisol.not_isLink hw.1).elim

@[simp]
lemma Isolated.eq_nil_of_mem (hisol : G.Isolated x) (hw : G.IsWalk w) (hx : x ∈ w) : w = nil x :=
  hisol.isWalk_nil_of_mem hw hx |>.eq_nil_of_mem hx

section Subgraph

variable {X : Set α}

lemma IsWalk.induce (hw : G.IsWalk w) (hX : V(w) ⊆ X) : G[X].IsWalk w := by
  induction hw with
  | nil => simp_all
  | @cons x e w hw h ih =>
    simp_all only [cons_vertexSet, insert_subset_iff, cons_isWalk_iff, induce_isLink, true_and,
      and_true, forall_const]
    refine hX.2 <| by simp

lemma isWalk_induce_iff' (hw : w.Nonempty) : G[X].IsWalk w ↔ G.IsWalk w ∧ V(w) ⊆ X := by
  refine ⟨fun h ↦ ⟨?_, h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩
  induction w with
  | nil => simp at hw
  | cons u e w ih => cases w with
    | nil v =>
      simp only [cons_isWalk_iff, nil_first, induce_isLink, nil_isWalk_iff,
        induce_vertexSet] at h ⊢
      exact ⟨h.1.1, h.1.1.right_mem⟩
    | cons v f w => simp_all

/-- This is almost true without the `X ⊆ V(G)` assumption; the exception is where
`w` is a nil walk on a vertex in `X \ V(G)`. -/
lemma isWalk_induce_iff_of_subset (hXV : X ⊆ V(G)) : G[X].IsWalk w ↔ G.IsWalk w ∧ V(w) ⊆ X :=
  ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vertexSet_subset⟩, fun h ↦ h.1.induce h.2⟩

lemma isWalk_induce_iff : G[X].IsWalk w ↔ (∃ x ∈ X \ V(G), w = nil x) ∨ G.IsWalk w ∧ V(w) ⊆ X := by
  have hile : G[V(G) ∩ X] ≤i G := induce_isInducedSubgraph inter_subset_left
  have hileX : G[V(G) ∩ X] ≤i G[X] := G.induce_isInducedSubgraph_mono_right inter_subset_right
  refine ⟨fun h ↦ ?_, ?_⟩; swap
  · rintro (⟨x, hxX, rfl⟩ | ⟨hw, hwX⟩)
    · simp [hxX.1]
    exact hw.isWalk_isInducedSubgraph hile (by simp [hwX, hw.vertexSet_subset]) |>.of_le hileX.le
  have hwX := by simpa using h.vertexSet_subset
  refine (em (Disjoint V(w) (X \ V(G))) |>.symm).imp (fun h1 ↦ ?_) (fun hw ↦ ?_)
  · obtain ⟨x, hxw, hxX⟩ := not_disjoint_iff.mp h1
    exact ⟨x, hxX, (G.diff_subset_isolatedSet_induce X hxX).eq_nil_of_mem h hxw⟩
  rw [disjoint_comm, disjoint_diff_iff, inter_eq_right.mpr <| by exact h.vertexSet_subset] at hw
  exact ⟨h.isWalk_isInducedSubgraph hileX (by simp [hw, hwX]) |>.of_le hile.le, hwX⟩

lemma IsWalk.vertexSet_subset_of_induce (hw : G[X].IsWalk w) : V(w) ⊆ X :=
  fun _ hxw => hw.vertex_mem_of_mem hxw

@[simp]
lemma isWalk_vertexDelete_iff : (G - X).IsWalk w ↔ G.IsWalk w ∧ Disjoint V(w) X := by
  rw [vertexDelete_def, isWalk_induce_iff_of_subset diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.vertexSet_subset

lemma IsWalk.vertexDelete (hw : G.IsWalk w) (hdisj : Disjoint V(w) X) : (G - X).IsWalk w := by
  simp [hw, hdisj]

lemma IsWalk.disjoint_of_vertexDelete (hw : (G - X).IsWalk w) : Disjoint V(w) X :=
  (isWalk_vertexDelete_iff.mp hw).2

lemma IsWalk.edgeRestrict (hw : G.IsWalk w) (hE : E(w) ⊆ F) : (G ↾ F).IsWalk w := by
  induction hw with simp_all [insert_subset_iff]

@[simp]
lemma isWalk_edgeRestrict_iff {F : Set β} : (G ↾ F).IsWalk w ↔ G.IsWalk w ∧ E(w) ⊆ F :=
  ⟨fun h ↦ ⟨h.of_le (by simp), h.edgeSet_subset.trans inter_subset_right⟩,
    fun h ↦ h.1.edgeRestrict h.2⟩

lemma IsWalk.edgeSet_subset_of_edgeRestrict (hw : (G ↾ F).IsWalk w) : E(w) ⊆ F :=
  (isWalk_edgeRestrict_iff.mp hw).2

@[simp]
lemma isWalk_edgeDelete_iff {F : Set β} : (G ＼ F).IsWalk w ↔ G.IsWalk w ∧ Disjoint E(w) F := by
  simp only [edgeDelete_eq_edgeRestrict, isWalk_edgeRestrict_iff, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.edgeSet_subset

lemma IsWalk.edgeDelete (hw : G.IsWalk w) (hdisj : Disjoint E(w) F) : (G ＼ F).IsWalk w := by
  simp [hw, hdisj]

lemma IsWalk.disjoint_of_edgeDelete (hw : (G ＼ F).IsWalk w) : Disjoint E(w) F :=
  (isWalk_edgeDelete_iff.mp hw).2

lemma IsWalk.isWalk_left_of_subset (hw : (G ∪ H).IsWalk w) (hE : E(w) ⊆ E(G))
    (h1 : w.first ∈ V(G)) : G.IsWalk w := by
  induction hw with
  | nil => simp_all
  | @cons x e w hw h ih =>
    simp_all only [union_isLink_iff, cons_edgeSet, insert_subset_iff, first_cons, cons_isWalk_iff,
      not_true_eq_false, and_false, or_false, forall_const, true_and]
    exact ih h.right_mem

lemma IsWalk.isWalk_left_of_subset_of_nonempty (hw : (G ∪ H).IsWalk w) (hE : E(w) ⊆ E(G))
    (hne : w.Nonempty) : G.IsWalk w := by
  by_cases h1 : w.first ∈ V(G)
  · exact hw.isWalk_left_of_subset hE h1
  cases w with
  | nil => simp_all
  | cons u e w =>
  simp only [cons_edgeSet, insert_subset_iff] at hE
  simp only [cons_isWalk_iff, union_isLink_iff, hE.1, not_true_eq_false, and_false, or_false] at hw
  rw [first_cons] at h1
  exact (h1 hw.1.left_mem).elim

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

lemma IsWalk.nontrivial_of_ne_not_adj (h : G.IsWalk w) (hne : w.first ≠ w.last)
    (hadj : ¬ G.Adj w.first w.last) : w.Nontrivial := by
  match w with
  | .nil u => simp at hne
  | .cons u e (.nil v) =>
    simp only [first_cons, last_cons, nil_last, cons_isWalk_iff, nil_first,
      nil_isWalk_iff] at hadj h
    exact (hadj ⟨e, h.1⟩).elim
  | .cons u e (.cons v f w) => simp



-- lemma _root_.Graph.IsPath.IsSuffix (hPf : w₁.IsSuffix w) (hP : G.IsPath w) : G.IsPath w₁ := by
--   simpa using hP.reverse.IsPrefix <| reverse_isPrefix_reverse_iff.2 hPf

end Graph

namespace WList

/-- Turn `w : WList α β` into a `Graph α β`. If the list is not well-formed
(i.e. it contains an edge appearing twice with different ends),
then the first occurence of the edge determines its ends in `w.toGraph`. -/
protected def toGraph : WList α β → Graph α β
  | nil u => Graph.noEdge {u} β
  | cons u e w => w.toGraph ∪ (Graph.singleEdge u w.first e)

@[simp]
lemma toGraph_nil : (WList.nil u (β := β)).toGraph = Graph.noEdge {u} β := rfl

lemma toGraph_cons : (w.cons u e).toGraph = w.toGraph ∪ (Graph.singleEdge u w.first e) := rfl

lemma toGraph_concat (w : WList α β) (e u) :
    (w.concat e u).toGraph = (Graph.singleEdge u w.last e) ∪ w.toGraph := by
  induction w with
  | nil v =>
    refine Graph.ext (by simp [toGraph_cons, pair_comm]) fun f x y ↦ ?_
    simp only [nil_concat, toGraph_cons, toGraph_nil, nil_first, union_isLink_iff, noEdge_edgeSet,
      mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet, singleEdge_isLink,
      and_true, false_or, nil_last, singleEdge_edgeSet, mem_singleton_iff, false_and, or_false,
      and_congr_right_iff]
    tauto
  | cons v f w ih =>
    ext a x y <;>
    · simp only [cons_concat, toGraph_cons, ih, concat_first, union_vertexSet, union_isLink_iff,
      singleEdge_isLink, singleEdge_vertexSet, union_insert, union_singleton, mem_insert_iff,
      mem_union, singleEdge_edgeSet, union_edgeSet, singleton_union, mem_singleton_iff]
      tauto

@[simp]
lemma toGraph_vertexSet (w : WList α β) : V(w.toGraph) = V(w) := by
  induction w with simp_all [toGraph_cons]

@[simp]
lemma toGraph_edgeSet (w : WList α β) : E(w.toGraph) = E(w) := by
  induction w with simp_all [toGraph_cons]

lemma toGraph_vertexSet_nonempty (w : WList α β) : V(w.toGraph).Nonempty := by
  simp

@[simp]
lemma WellFormed.toGraph_isLink (h : w.WellFormed) : w.toGraph.IsLink = w.IsLink := by
  ext e x y
  induction w with
  | nil => simp
  | cons u f w ih =>
    rw [cons_wellFormed_iff] at h
    rw [toGraph_cons, union_isLink_iff, isLink_cons_iff, ih h.1, toGraph_edgeSet, mem_edgeSet_iff,
      singleEdge_isLink_iff, eq_comm (a := e), iff_def, or_imp, and_iff_right (by tauto), or_imp,
      and_iff_left (by tauto)]
    rintro ⟨rfl, h_eq⟩
    rw [and_iff_right rfl, and_iff_right h_eq, ← imp_iff_or_not]
    intro hf
    obtain ⟨y₁, y₂, hinc⟩ := exists_isLink_of_mem_edge hf
    rw [← h.2 y₁ y₂ hinc] at h_eq
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Sym2.eq_iff.1 h_eq
    · assumption
    exact hinc.symm

lemma IsSublist.toGraph_le (h : w₁.IsSublist w₂) (hw₂ : w₂.WellFormed) :
    w₁.toGraph ≤ w₂.toGraph where
  vertex_subset := by
    refine fun x hx ↦ ?_
    simp only [toGraph_vertexSet, mem_vertexSet_iff] at hx ⊢
    exact h.mem hx
  isLink_of_isLink e x y h' := by
    rw [hw₂.toGraph_isLink]
    rw [(hw₂.sublist h).toGraph_isLink] at h'
    exact h'.of_isSublist h

lemma WellFormed.reverse_toGraph (h : w.WellFormed) : w.reverse.toGraph = w.toGraph :=
    Graph.ext (by simp) fun e x y ↦ by
    rw [h.toGraph_isLink, h.reverse.toGraph_isLink, isLink_reverse_iff]

lemma WellFormed.isWalk_toGraph (hw : w.WellFormed) : w.toGraph.IsWalk w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    rw [cons_wellFormed_iff] at hw
    refine ((ih hw.1).of_le (by simp [toGraph_cons])).cons ?_
    suffices w.toGraph.IsLink e u w.first ∨ e ∉ w.edge by simpa [toGraph_cons, union_isLink_iff]
    rw [← imp_iff_or_not]
    intro he
    obtain ⟨y₁, y₂, h⟩ := exists_isLink_of_mem_edge he
    rw [((ih hw.1).isLink_of_isLink h).isLink_iff_sym2_eq, hw.2 _ _ h]

end WList

namespace Graph

lemma IsWalk.toGraph_le (h : G.IsWalk w) : w.toGraph ≤ G := by
  induction w with
  | nil u => simpa [WList.toGraph] using h
  | cons u e W ih =>
    simp only [cons_isWalk_iff] at h
    exact Graph.union_le (ih h.2) (by simpa using h.1)

lemma _root_.WList.WellFormed.toGraph_le_iff (hW : W.WellFormed) : W.toGraph ≤ G ↔ G.IsWalk W := by
  refine ⟨fun hle ↦ ?_, IsWalk.toGraph_le⟩
  induction W with
  | nil => simpa using hle
  | cons u e W IH =>
    simp_all only [cons_isWalk_iff]
    rw [cons_wellFormed_iff] at hW
    rw [toGraph_cons, Compatible.union_le_iff] at hle
    · simp only [singleEdge_le_iff] at hle
      refine ⟨hle.2, IH hW.1 hle.1⟩
    rw [comm_of Compatible, singleEdge_compatible_iff, toGraph_edgeSet, mem_edgeSet_iff]
    intro he
    obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edge he
    have := hW.2 _ _ hexy
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := this
    · rwa [hW.1.toGraph_isLink]
    rw [hW.1.toGraph_isLink]
    exact hexy.symm

lemma IsWalk.edgeSet_subset_induce_edgeSet (hw : G.IsWalk w) : E(w) ⊆ E(G[V(w)]) := by
  intro e hew
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edge hew
  rw [(hw.isLink_of_isLink h).mem_induce_iff]
  exact ⟨h.left_mem, h.right_mem⟩

lemma IsWalk.toGraph_eq_induce_restrict (h : G.IsWalk w) : w.toGraph = G[V(w)] ↾ E(w) := by
  induction w with
  | nil => ext <;> simp
  | cons u e w ih =>
    have hss' := h.edgeSet_subset_induce_edgeSet
    simp_all only [cons_isWalk_iff, cons_vertexSet, cons_edgeSet, forall_const]
    rw [toGraph_cons, ih]
    refine G.ext_of_le_le (Graph.union_le ?_ ?_) ?_ (by simp) ?_
    · exact (edgeRestrict_le ..).trans (induce_le h.2.vertexSet_subset)
    · simpa using h.1
    · refine (edgeRestrict_le ..).trans (induce_le ?_)
      simp [insert_subset_iff, h.1.left_mem, h.2.vertexSet_subset]
    simp only [union_edgeSet, edgeRestrict_edgeSet, singleEdge_edgeSet, union_singleton]
    rw [inter_eq_self_of_subset_right h.2.edgeSet_subset_induce_edgeSet,
      inter_eq_self_of_subset_right hss']

lemma IsWalk.le_of_edgeSet_subset (hw₁ : G.IsWalk w₁) (hne : w₁.Nonempty) (hw₂ : G.IsWalk w₂)
    (hss : E(w₁) ⊆ E(w₂)) : w₁.toGraph ≤ w₂.toGraph := by
  have h₁ := hw₁.toGraph_le
  have h₂ := hw₂.toGraph_le
  refine G.le_of_le_le_subset_subset h₁ h₂ (fun x hxV ↦ ?_) (by simpa using hss)
  rw [toGraph_vertexSet, mem_vertexSet_iff, hne.mem_iff_exists_isLink] at hxV
  obtain ⟨y, e, h⟩ := hxV
  have hew₂ := hss h.edge_mem
  rw [hw₁.isLink_iff_isLink_of_mem h.edge_mem, ← hw₂.isLink_iff_isLink_of_mem hew₂] at h
  simpa using h.left_mem

end Graph
