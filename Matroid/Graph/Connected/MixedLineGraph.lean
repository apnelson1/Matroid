import Matroid.Graph.Connected.Basic
import Matroid.Graph.Degree.Leaf

open Set Function Nat WList Sum

variable {α β ι : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z s t : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W w P Q : WList α β} {n m : ℕ}

namespace Graph

-- TODO: find home for this lemma
@[gcongr]
lemma neighbors_mono (hle : H ≤ G) (x : α) : N(H, x) ⊆ N(G, x) := by
  rintro y ⟨e, hl⟩
  use e, hl.of_le hle

-- TODO: find home for this lemma
lemma Inc.eq_or_isLink_of_inc (h1 : G.Inc e x) (h2 : G.Inc e y) : x = y ∨ G.IsLink e x y := by
  obtain ⟨a, ha⟩ := h2
  obtain rfl | rfl := h1.eq_or_eq_of_isLink ha
  · tauto
  exact Or.inr ha.symm

-- TODO: find home for this lemma
lemma Inc.isLink_of_inc_of_ne (h1 : G.Inc e x) (h2 : G.Inc e y) (hne : x ≠ y) : G.IsLink e x y := by
  obtain rfl | h := h1.eq_or_isLink_of_inc h2 <;> tauto

lemma connBetween_vertexDelete_iff_of_degree_le_one (hX : ∀ x ∈ X, G.eDegree x ≤ 1) (hs : s ∉ X)
    (ht : t ∉ X) : (G - X).ConnBetween s t ↔ G.ConnBetween s t := by
  refine ⟨fun h ↦ h.mono vertexDelete_le, fun h ↦ ?_⟩
  obtain ⟨w, hw, rfl, rfl⟩ := h.exists_isPath
  use w, by simp [hw.isWalk, hw.isTrail.disjoint_of_degree_le_one hX hs ht]

instance (G : Graph α β) : Simple L'(G) where
  not_isLoopAt ab x h := by
    unfold IsLoopAt at h
    rw [mixedLineGraph_isLink] at h
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, or_self] at h
    obtain rfl := h.2.2
    simpa using h.2.1
  eq_of_isLink e f x y h1 h2 := by
    cases e
    cases f
    rw [mixedLineGraph_isLink] at h1 h2
    rw [← h1.2] at h2
    simp_all

instance [G.Finite] : L'(G).Finite := by
  apply Graph.Simple.vertexSet_finite_iff.mp
  simp only [mixedLineGraph_vertexSet, finite_union]
  exact ⟨G.vertexSet_finite.image inl, G.edgeSet_finite.image inr⟩

instance [G.LocallyFinite] : L'(G).LocallyFinite where
  finite x := by match x with
  | inl v =>
    simp only [IncEdges, mixedLineGraph_inc, reduceCtorEq, inl.injEq, false_or]
    convert G.finite_incEdges v |>.image (fun e ↦ (v, e))
    refine Set.ext fun ⟨a, b⟩ ↦ ?_
    simp only [eq_comm, mem_setOf_eq, mem_image, mem_incEdges_iff, Prod.mk.injEq,
      exists_eq_right_right', and_congr_left_iff]
    rintro rfl
    tauto
  | inr e =>
    simp only [IncEdges, mixedLineGraph_inc, inr.injEq, reduceCtorEq, or_false]
    convert G.endSet_finite e |>.image fun x ↦ (x, e)
    refine Set.ext fun ⟨a, b⟩ ↦ ?_
    simp only [eq_comm, mem_setOf_eq, mem_image, mem_endSet_iff, Prod.mk.injEq, ↓existsAndEq,
      true_and, and_congr_left_iff]
    rintro rfl
    tauto

@[simp]
lemma mixedLineGraph_neighbor_inr : N(L'(G), .inr e) = .inl '' G.endSet e := by
  ext x
  unfold Neighbor
  simp [mixedLineGraph_adj]

@[simp]
lemma mixedLineGraph_neighbor_inl : N(L'(G), .inl v) = .inr '' E(G, v) := by
  ext e
  unfold Neighbor
  simp [mixedLineGraph_adj]

lemma mixedLineGraph_inr_eDegree_le_two : L'(G).eDegree (Sum.inr e) ≤ 2 := by
  rw [eDegree_eq_encard_adj, mixedLineGraph_neighbor_inr, inl_injective.encard_image]
  exact G.endSet_encard_le e

lemma mixedLineGraph_edgeDelete : L'(G ＼ F) = L'(G) - (Sum.inr '' F : Set (α ⊕ β)) := by
  ext a b c
  · simp only [mixedLineGraph_vertexSet, edgeDelete_vertexSet, edgeDelete_edgeSet,
      vertexDelete_vertexSet, image_diff Sum.inr_injective, union_diff_distrib]
    convert Iff.rfl
    apply Disjoint.sdiff_eq_left
    simp
  cases b <;> cases c <;> simp only [mixedLineGraph_isLink, edgeDelete_inc_iff, Sym2.eq,
    Sym2.rel_iff', Prod.mk.injEq, Sum.inl.injEq, reduceCtorEq, and_false, Prod.swap_prod_mk,
    or_self, vertexDelete_isLink_iff, mem_image, exists_false, not_false_eq_true, and_self,
    and_true, Sum.inr.injEq, false_and, or_self, and_false, exists_eq_right] <;> aesop

lemma mixedLineGraph_vertexDelete : L'(G - X) = L'(G) - (Sum.inl '' X ∪ Sum.inr '' E(G, X)) := by
  ext a b c
  · simp only [mixedLineGraph_vertexSet, vertexDelete_vertexSet, vertexDelete_edgeSet_diff]
    rw [image_diff Sum.inl_injective, union_diff_distrib, ← diff_diff, ← diff_diff]
    convert Iff.rfl using 3
    · apply Disjoint.sdiff_eq_left
      rw [← image_diff Sum.inl_injective]
      simp
    rw [disjoint_image_inl_image_inr.symm.sdiff_eq_left, ← image_diff Sum.inr_injective]
  cases b <;> cases c <;> simp only [mixedLineGraph_isLink, vertexDelete_inc_iff,
    mem_setIncEdges_iff, not_exists, not_and, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Sum.inl.injEq, reduceCtorEq, and_false, Prod.swap_prod_mk, or_self, vertexDelete_isLink_iff,
    mem_union, mem_image, exists_eq_right, exists_false, or_false, false_and, Sum.inr.injEq,
    exists_eq_right, false_or, not_exists, not_and]
  · refine ⟨?_, ?_⟩
    · rintro ⟨⟨hav, ha2⟩, rfl, rfl⟩
      simpa [hav, and_self, true_and, mt (ha2 a.1) (not_not_intro hav)]
    rintro ⟨⟨hinc, rfl, rfl⟩, ha1, hX⟩
    simpa [hinc]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨hinc, hX⟩, rfl, rfl⟩
    simpa [hinc, mt (hX a.1)]
  rintro ⟨⟨hinc, rfl, rfl⟩, hX, ha1⟩
  simpa [hinc]

@[simp]
def mixedLineGraph_walkMap : WList α β → WList (α ⊕ β) (α × β)
| nil x => nil (Sum.inl x)
| cons x e w => cons (Sum.inl x) (x, e) (cons (Sum.inr e) (w.first, e) (mixedLineGraph_walkMap w))

@[simp]
lemma mixedLineGraph_walkMap_first : (mixedLineGraph_walkMap W).first = Sum.inl W.first := by
  induction W with
  | nil x => simp
  | cons x e w ih => simp

@[simp]
lemma mixedLineGraph_walkMap_last : (mixedLineGraph_walkMap W).last = Sum.inl W.last := by
  induction W with
  | nil x => simp
  | cons x e w ih => simpa

@[simp]
lemma inl_mem_mixedLineGraph_walkMap_iff (W : WList α β) :
    Sum.inl x ∈ mixedLineGraph_walkMap W ↔ x ∈ W := by
  match W with
  | .nil u => simp
  | .cons u e w =>
    simp only [mixedLineGraph_walkMap, mem_cons_iff, Sum.inl.injEq, reduceCtorEq, false_or]
    exact or_congr_right <| inl_mem_mixedLineGraph_walkMap_iff w

@[simp]
lemma inr_mem_mixedLineGraph_walkMap_iff (W : WList α β) :
    Sum.inr e ∈ mixedLineGraph_walkMap W ↔ e ∈ E(W) := by
  match W with
  | .nil u => simp
  | .cons u f w =>
    simp only [mixedLineGraph_walkMap, mem_cons_iff, reduceCtorEq, Sum.inr.injEq, false_or,
      cons_edgeSet, mem_insert_iff, mem_edgeSet_iff]
    exact or_congr_right <| inr_mem_mixedLineGraph_walkMap_iff w

@[simp]
lemma mixedLineGraph_walkMap_concat (x : α) (e : β) (w) : (mixedLineGraph_walkMap <| w.concat e x) =
    ((mixedLineGraph_walkMap w).concat (w.last, e) (Sum.inr e)).concat (x, e) (Sum.inl x) := by
  match w with
  | nil a => simp
  | cons a b w =>
    simp only [cons_concat, mixedLineGraph_walkMap, concat_first, last_cons, cons.injEq, true_and]
    exact mixedLineGraph_walkMap_concat ..

@[simp]
lemma mixedLineGraph_walkmap_reverse (W : WList α β) :
    mixedLineGraph_walkMap W.reverse = (mixedLineGraph_walkMap W).reverse := by
  match W with
  | nil x => simp
  | cons x e w =>
    simp only [mixedLineGraph_walkMap, reverse_cons, mixedLineGraph_walkMap_concat, reverse_last]
    rw [mixedLineGraph_walkmap_reverse w]

@[simp]
lemma IsWalk.mixedLineGraph_walkMap (hW : G.IsWalk W) :L'(G).IsWalk (mixedLineGraph_walkMap W) := by
  induction hW with
  | nil hx => simpa
  | cons hw h ih => simp [ih, h.inc_left, h.inc_right]

@[simp]
lemma IsPath.mixedLineGraph_walkMap {P} (hP : G.IsPath P) :
    L'(G).IsPath (mixedLineGraph_walkMap P) := by
  use hP.isWalk.mixedLineGraph_walkMap
  match P with
  | .nil u => simp
  | .cons u e w =>
    have := hP.isTrail
    simp_all only [cons_isPath_iff, cons_isTrail_iff, true_and, Graph.mixedLineGraph_walkMap,
      cons_vertex, List.nodup_cons, List.mem_cons, reduceCtorEq, mem_vertex,
      inl_mem_mixedLineGraph_walkMap_iff, or_self, not_false_eq_true,
      inr_mem_mixedLineGraph_walkMap_iff, mem_edgeSet_iff]
    use hP.2.1.mixedLineGraph_walkMap.nodup

@[simp]
lemma mixedLineGraph_walkMap_vertexSet :
    V(mixedLineGraph_walkMap W) = Sum.inl '' V(W) ∪ Sum.inr '' E(W) := by
  induction W with
  | nil x => simp
  | cons x e w ih => simp [ih, image_insert_eq, insert_union, insert_comm]

@[simp]
lemma mem_mixedLineGraph_walkMap_iff {x} : x ∈ mixedLineGraph_walkMap W ↔ (∃ v ∈ W, Sum.inl v = x) ∨
    (∃ e ∈ E(W), Sum.inr e = x) := by
  rw [← WList.mem_vertexSet_iff]
  simp

def mixedLineEnsembleMap (A : G.VertexEnsemble s t ι) (hA : A.edgeDisjoint) :
    L'(G).VertexEnsemble (inl s) (inl t) ι where
  f i := mixedLineGraph_walkMap (A.f i)
  isPath i := A.isPath i |>.mixedLineGraph_walkMap
  first_eq i := by simp [A.first_eq i]
  last_eq i := by simp [A.last_eq i]
  internallyDisjoint i j hne := by
    ext x
    simp only [mixedLineGraph_walkMap_vertexSet, mem_inter_iff, mem_union, mem_image,
      mem_vertexSet_iff, mem_edgeSet_iff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨h1, h2⟩ ↦ ?_, ?_⟩
    · obtain ⟨u, hu, rfl⟩ | ⟨e, he, rfl⟩ := h1 <;> obtain ⟨v, hv, hveq⟩ | ⟨f, hf, heeq⟩ := h2
      · obtain rfl := by simpa using hveq
        obtain rfl | rfl := A.eq_or_eq_of_mem hu hv hne <;> tauto
      · simp at heeq
      · simp at hveq
      · obtain rfl := by simpa using heeq
        exact hA hne |>.ne_of_mem he hf rfl |>.elim
    rintro (rfl | rfl)
    · simp [A.first_eq i ▸ first_mem, A.first_eq j ▸ first_mem]
    · simp [A.last_eq i ▸ last_mem, A.last_eq j ▸ last_mem]

-- lemma neighbors_mixedLineGraph_inl : N(L'(G), Sum.inl '' X) = Sum.inr '' E(G, X) := by
--   sorry

@[simp]
def WalkOfMixedLineGraph (w : WList (α ⊕ β) (α × β)) {s t} (h : L'(G).IsWalk w) [DecidableEq α]
    (hf : w.first = Sum.inl s) (hl : w.last = Sum.inl t) : WList α β := by
  match w with
  | .nil (inl s) => exact WList.nil s
  | .cons (inl s) e (.nil (inl t)) => simp at h
  | .cons (inl s) (a, b) (.cons v (c, d) w) =>
    have hw : L'(G).IsWalk w := by
      simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
        Prod.mk.injEq, inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
      obtain ⟨⟨he, rfl, rfl⟩, ⟨hf, hh⟩, hw⟩ := h
      exact hw
    have hf : w.first = inl c := by
      simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
        Prod.mk.injEq, inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
      obtain ⟨⟨he, rfl, rfl⟩, ⟨hf, hh⟩, hw⟩ := h
      simp only [reduceCtorEq, false_and, inr.injEq, false_or] at hh
      exact hh.1.symm
    if hsc : s = c
    then refine (WalkOfMixedLineGraph w (s := s) hw (hsc ▸ hf) hl)
    else refine WList.cons a d (WalkOfMixedLineGraph w (s := c) hw hf hl)

@[simp]
lemma WalkOfMixedLineGraph_first [DecidableEq α] {w : WList (α ⊕ β) (α × β)} {s t}
    (h : L'(G).IsWalk w) (hf : w.first = inl s) (hl : w.last = inl t) :
    (WalkOfMixedLineGraph w h hf hl).first = s := by
  match w with
  | .nil (inl s) => simpa using hf
  | .cons (inl s) e (.nil (inl t)) => simp at h
  | .cons (inl s) (a, b) (.cons v (c, d) w) =>
    simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨hbs, rfl, rfl⟩, ⟨hdc, hh⟩, hw⟩ := h
    simp only [last_cons, first_cons, inl.injEq, WalkOfMixedLineGraph] at hl hf ⊢
    split_ifs with hsc
    · subst c a
      simp only [reduceCtorEq, false_and, inr.injEq, false_or] at hh
      obtain ⟨hh, rfl⟩ := hh
      exact WalkOfMixedLineGraph_first hw hh.symm hl
    simpa

@[simp]
lemma WalkOfMixedLineGraph_last [DecidableEq α] {w : WList (α ⊕ β) (α × β)} {s t}
    (h : L'(G).IsWalk w) (hf : w.first = inl s) (hl : w.last = inl t) :
    (WalkOfMixedLineGraph w h hf hl).last = t := by
  match w with
  | .nil (inl s) => simpa using hl
  | .cons (inl s) e (.nil (inl t)) => simp at h
  | .cons (inl s) (a, b) (.cons v (c, d) w) =>
    simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨hbs, rfl, rfl⟩, ⟨hdc, hh⟩, hw⟩ := h
    simp only [last_cons, first_cons, inl.injEq, WalkOfMixedLineGraph] at hl hf ⊢
    simp only [reduceCtorEq, false_and, inr.injEq, false_or] at hh
    obtain ⟨hh, rfl⟩ := hh
    split_ifs with hsc
    · subst c a
      exact WalkOfMixedLineGraph_last hw hh.symm hl
    exact WalkOfMixedLineGraph_last hw hh.symm hl

@[simp]
lemma mem_walkOfMixedLineGraph_iff [DecidableEq α] {w : WList (α ⊕ β) (α × β)} {s t}
    (h : L'(G).IsWalk w) (hf : w.first = inl s) (hl : w.last = inl t) :
    x ∈ WalkOfMixedLineGraph w h hf hl ↔ inl x ∈ w := by
  match w with
  | .nil (inl s) => simp
  | .cons (inl s) e (.nil (inl t)) => simp at h
  | .cons (inl s) (a, b) (.cons v (c, d) w) =>
    simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨hds, rfl, rfl⟩, ⟨hdc, hh⟩, hw⟩ := h
    simp only [first_cons, inl.injEq, reduceCtorEq, false_and, inr.injEq, false_or,
      Graph.WalkOfMixedLineGraph] at hf hh ⊢
    obtain ⟨hh, rfl⟩ := hh
    subst a
    split_ifs with hsc
    · subst c
      simp only [mem_walkOfMixedLineGraph_iff, mem_cons_iff, inl.injEq, reduceCtorEq, false_or,
        iff_or_self]
      exact fun h ↦ (h ▸ hh) ▸ first_mem
    simp [mem_walkOfMixedLineGraph_iff]

@[simp]
lemma mem_of_mem_walkOfMixedLineGraph_edge [DecidableEq α] {w : WList (α ⊕ β) (α × β)} {s t}
    (h : L'(G).IsWalk w) (hf : w.first = inl s) (hl : w.last = inl t)
    (he : e ∈ (WalkOfMixedLineGraph w h hf hl).edge) : inr e ∈ w := by
  match w with
  | .nil (inl s) => simp at he
  | .cons (inl s) e (.nil (inl t)) => simp at h
  | .cons (inl s) (a, b) (.cons v (c, d) w) =>
    simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨hds, rfl, rfl⟩, ⟨hdc, hh⟩, hw⟩ := h
    simp only [first_cons, inl.injEq, reduceCtorEq, false_and, inr.injEq, false_or, last_cons,
      WalkOfMixedLineGraph, mem_cons_iff] at hf hh hl he ⊢
    obtain ⟨hh, rfl⟩ := hh
    subst a
    split_ifs at he with hsc
    · subst c
      right
      exact mem_of_mem_walkOfMixedLineGraph_edge hw hh.symm hl he
    simp only [cons_edge, List.mem_cons] at he
    exact he.imp id (mem_of_mem_walkOfMixedLineGraph_edge hw hh.symm hl ·)

lemma IsWalk.WalkOfMixedLineGraph [DecidableEq α] {w : WList (α ⊕ β) (α × β)} (h : L'(G).IsWalk w)
    {s t} (hf : w.first = inl s) (hl : w.last = inl t) :
    G.IsWalk (WalkOfMixedLineGraph w h hf hl) := by
  match w with
  | .nil (inl s) => simpa using h
  | .cons (inl s) e (.nil (inl t)) => simp at h
  | .cons (inl s) (a, b) (.cons v (c, d) w) =>
    simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨hds, rfl, rfl⟩, ⟨hdc, hh⟩, hw⟩ := h
    simp only [first_cons, inl.injEq, reduceCtorEq, false_and, inr.injEq, false_or,
      Graph.WalkOfMixedLineGraph] at hf hh ⊢
    obtain ⟨hh, rfl⟩ := hh
    subst a
    split_ifs with hsc
    · subst c
      apply hw.WalkOfMixedLineGraph
    simp only [cons_isWalk_iff, WalkOfMixedLineGraph_first]
    exact ⟨hds.isLink_of_inc_of_ne hdc hsc, hw.WalkOfMixedLineGraph _ hl⟩

lemma IsPath.WalkOfMixedLineGraph [DecidableEq α] {w : WList (α ⊕ β) (α × β)} (h : L'(G).IsPath w)
    {s t} (hf : w.first = inl s) (hl : w.last = inl t) :
    G.IsPath (WalkOfMixedLineGraph w h.isWalk hf hl) := by
  use h.isWalk.WalkOfMixedLineGraph hf hl
  match w with
  | .nil (inl s) => simp
  | .cons (inl s) e (.nil (inl t)) => simp at h
  | .cons (inl s) (a, b) (.cons v (c, d) w) =>
    simp only [cons_isPath_iff, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, first_cons, inl.injEq, reduceCtorEq, and_false, or_false, mem_cons_iff,
      not_or, ne_eq] at h
    obtain ⟨⟨hbs, rfl, rfl⟩, ⟨⟨hdc, hh⟩, hw, hbw⟩, -, hsw⟩ := h
    simp only [first_cons, inl.injEq, reduceCtorEq, false_and, inr.injEq, false_or,
      Graph.WalkOfMixedLineGraph] at hf hh ⊢
    obtain ⟨hcw, rfl⟩ := hh
    subst a
    split_ifs with hsc
    · subst c
      exact hw.WalkOfMixedLineGraph hcw.symm hl |>.nodup
    simp only [cons_vertex, List.nodup_cons, mem_vertex]
    use by simpa, (hw.WalkOfMixedLineGraph hcw.symm hl |>.nodup)

lemma IsWalk.connBetween_of_mixedLineGraph {w : WList (α ⊕ β) (α × β)} {s t} (h : L'(G).IsWalk w)
    (hf : w.first = Sum.inl s) (hl : w.last = Sum.inl t) : G.ConnBetween s t := by
  classical
  use Graph.WalkOfMixedLineGraph w h hf hl, h.WalkOfMixedLineGraph hf hl, by simp, by simp

@[simp]
lemma connBetween_mixedLineGraph_iff :
    L'(G).ConnBetween (Sum.inl s) (Sum.inl t) ↔ G.ConnBetween s t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw, hf, hl⟩ := h
    exact hw.connBetween_of_mixedLineGraph hf hl
  obtain ⟨w, hw, rfl, rfl⟩ := h
  use mixedLineGraph_walkMap w, hw.mixedLineGraph_walkMap, by simp, by simp

lemma connBetween_mixedLineGraph_del_iff :
    (L'(G) - (Sum.inl '' X ∪ Sum.inr '' F)).ConnBetween (Sum.inl s) (Sum.inl t) ↔
    ((G - X) ＼ F).ConnBetween s t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rwa [← connBetween_vertexDelete_iff_of_degree_le_one (X := inr '' E(G, X)) ?_ (by simp)
    (by simp), ← vertexDelete_vertexDelete, vertexDelete_vertexDelete_comm,
    vertexDelete_vertexDelete _ (inl '' _), ← mixedLineGraph_vertexDelete,
    ← mixedLineGraph_edgeDelete, connBetween_mixedLineGraph_iff] at h
    -- inr '' E(G, X) vertices are either isolated or is a leaf so does not affect the connection
    rintro _ ⟨e, he, rfl⟩
    grw [eDegree_eq_encard_adj, ← vertexDelete_vertexDelete, neighbors_mono vertexDelete_le,
      encard_le_one_iff_subsingleton]
    intro _ ⟨⟨a, b⟩, ha⟩ _ ⟨⟨c, d⟩, hc⟩
    simp only [vertexDelete_isLink_iff, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, reduceCtorEq, false_and, Prod.swap_prod_mk, inr.injEq, false_or, mem_image,
      and_false, exists_false, not_false_eq_true, not_exists, not_and, ne_eq, true_and] at ha hc
    obtain ⟨⟨hda, rfl, rfl⟩, h1⟩ := ha
    obtain ⟨⟨hdc, rfl, rfl⟩, h2⟩ := hc
    obtain ⟨x, hx, hdx⟩ := he
    obtain rfl | rfl | rfl := hdx.eq_or_eq_or_eq hda hdc
    · simpa using h1 x hx
    · simpa using h2 x hx
    rfl
  rw [← connBetween_mixedLineGraph_iff, mixedLineGraph_edgeDelete, mixedLineGraph_vertexDelete] at h
  refine h.mono ?_
  rw [← vertexDelete_vertexDelete, ← vertexDelete_vertexDelete, vertexDelete_vertexDelete_comm]
  exact vertexDelete_le

@[simps (attr := grind =)]
def mixedLineOfEnsembleMap [DecidableEq α] (A : L'(G).VertexEnsemble (inl s) (inl t) ι) :
    G.VertexEnsemble s t ι where
  f i := WalkOfMixedLineGraph (A.f i) (A.isPath i).isWalk (A.first_eq i) (A.last_eq i)
  isPath i := (A.isPath i).WalkOfMixedLineGraph (A.first_eq i) (A.last_eq i)
  first_eq i := by simp
  last_eq i := by simp
  internallyDisjoint i j hne := by
    ext x
    have := Set.ext_iff.mp (A.internallyDisjoint hne) (inl x)
    simpa

lemma mixedLineOfEnsembleMap_edgeDisjoint [DecidableEq α]
    (A : L'(G).VertexEnsemble (inl s) (inl t) ι) : (mixedLineOfEnsembleMap A).edgeDisjoint := by
  classical
  rintro i j hne
  simp only [onFun, mixedLineOfEnsembleMap, disjoint_iff_forall_notMem, mem_edgeSet_iff]
  intro e hei hej
  have h1 := mem_of_mem_walkOfMixedLineGraph_edge (A.isPath i).isWalk (A.first_eq i) (A.last_eq i)
    hei
  have h2 := mem_of_mem_walkOfMixedLineGraph_edge (A.isPath j).isWalk (A.first_eq j) (A.last_eq j)
    hej
  have := A.internallyDisjoint hne ▸ (show inr e ∈ V(A.f i) ∩ V(A.f j) by simp [h1, h2])
  simp at this

-- If e is not a loop, then we could even get a path rather than a walk.
lemma Preconnected.exists_isWalk_first_lastEdge (h : G.Preconnected) (hx : x ∈ V(G))(he : e ∈ E(G)):
    ∃ (P : WList α β) (hP : P.Nonempty), G.IsWalk P ∧ P.first = x ∧ hP.lastEdge = e := by
  have ⟨a, b, he⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨P, hP, rfl, rfl⟩ := h x a hx he.left_mem
  use P.concat e b
  simp [hP, he]

lemma Preconnected.exists_isWalk_firstEdge_lastEdge (h : G.Preconnected) (he : e ∈ E(G))
    (hf : f ∈ E(G)) : ∃ (W : WList α β) (hW : W.Nonempty), G.IsWalk W ∧ hW.firstEdge = e ∧
    hW.lastEdge = f := by
  have ⟨a, b, he⟩ := G.exists_isLink_of_mem_edgeSet he
  have ⟨c, d, hf⟩ := G.exists_isLink_of_mem_edgeSet hf
  obtain ⟨P, hP, rfl, rfl⟩ := h b c he.right_mem hf.left_mem
  use (P.cons a e).concat f d
  simp [hP, he, hf, Nonempty.lastEdge_cons]

lemma Preconnected.mixedLineGraph (h : G.Preconnected) : L'(G).Preconnected := by
  rintro (a | a) (b | b) ha hb <;> simp only [mixedLineGraph_vertexSet, mem_union, mem_image,
    Sum.inl.injEq, Sum.inr.injEq, exists_eq_right, reduceCtorEq, and_false, exists_false, or_false,
    false_or] at ha hb
  · obtain ⟨W, hW, rfl, rfl⟩ := h a b ha hb
    use mixedLineGraph_walkMap W, hW.mixedLineGraph_walkMap
    simp
  · obtain ⟨W, hWne, hW, rfl, rfl⟩ := h.exists_isWalk_first_lastEdge ha hb
    use (mixedLineGraph_walkMap W).dropLast, (hW.mixedLineGraph_walkMap).dropLast, by simp
    obtain ⟨w, e, x, rfl⟩ := hWne.exists_concat
    simp
  · obtain ⟨W, hWne, hW, rfl, rfl⟩ := h.exists_isWalk_first_lastEdge hb ha
    use (mixedLineGraph_walkMap W).dropLast.reverse, (hW.mixedLineGraph_walkMap).dropLast.reverse,
      ?_, by simp
    obtain ⟨w, e, x, rfl⟩ := hWne.exists_concat
    simp
  · obtain ⟨W, ⟨x, e, w⟩, hW, rfl, rfl⟩ := h.exists_isWalk_firstEdge_lastEdge ha hb
    use (mixedLineGraph_walkMap (cons x e w)).tail.dropLast,
    (hW.mixedLineGraph_walkMap).tail.dropLast, by simp, ?_
    simp only [mixedLineGraph_walkMap, tail_cons]
    obtain ⟨y, rfl⟩ | h := w.exists_eq_nil_or_nonempty
    · simp
    obtain ⟨w, f, y, rfl⟩ := h.exists_concat
    simp only [concat_first, mixedLineGraph_walkMap_concat]
    rw [← cons_concat, dropLast_concat]
    simp [(w.concat_nonempty f y).lastEdge_cons]

lemma notMem_iff_forall_mem_ne (S : Set α) (x : α) : (∀ y ∈ S, y ≠ x) ↔ x ∉ S := by
  aesop

end Graph
