import Matroid.Graph.Connected.Basic
import Matroid.Graph.Degree.Leaf

open Set Function Nat WList

variable {α β ι : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z s t : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β} {n m : ℕ}

namespace Graph

lemma mixedLineGraph_edgeDelete : L'(G ＼ F) = L'(G) - (Sum.inr '' F) := by
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
    use hP.1.mixedLineGraph_walkMap.nodup

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

lemma Inc.eq_or_isLink_of_inc (h1 : G.Inc e x) (h2 : G.Inc e y) : x = y ∨ G.IsLink e x y := by
  obtain ⟨a, ha⟩ := h2
  obtain rfl | rfl := h1.eq_or_eq_of_isLink ha
  · tauto
  exact Or.inr ha.symm

-- lemma neighbors_mixedLineGraph_inl : N(L'(G), Sum.inl '' X) = Sum.inr '' E(G, X) := by
--   sorry

lemma IsWalk.connBetween_of_mixedLineGraph {w : WList (α ⊕ β) (α × β)} {s t} (h : L'(G).IsWalk w)
    (hf : w.first = Sum.inl s) (hl : w.last = Sum.inl t) : G.ConnectedBetween s t := by
  match w with
  | .nil u => simp_all only [nil_isWalk_iff, mixedLineGraph_vertexSet, mem_union, mem_image,
    nil_first, nil_last, Sum.inl.injEq, connectedBetween_self, exists_eq_right, reduceCtorEq,
    and_false, exists_false, or_false]
  | .cons u e (.nil v) => simp_all only [cons_isWalk_iff, nil_first, mixedLineGraph_isLink, Sym2.eq,
    Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, nil_isWalk_iff, mixedLineGraph_vertexSet,
    mem_union, mem_image, first_cons, last_cons, nil_last, Sum.inl.injEq, reduceCtorEq, and_false,
    or_self, exists_eq_right, exists_false, or_false, false_and]
  | .cons u e (.cons v f w) =>
    simp only [last_cons] at hl
    obtain rfl := by simpa using hf
    simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Sum.inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at h
    obtain ⟨⟨he, rfl, rfl⟩, ⟨hf, ⟨hfe, hfw⟩ | ⟨hfw, hfe⟩⟩, hw⟩ := h <;> simp at hfe
    obtain heq | hlk := he.eq_or_isLink_of_inc (hfe ▸ hf)
    · exact hw.connBetween_of_mixedLineGraph (heq ▸ hfw.symm) hl
    exact hlk.connectedBetween.trans <|  hw.connBetween_of_mixedLineGraph hfw.symm hl

@[simp]
lemma connBetween_mixedLineGraph_iff :
    L'(G).ConnectedBetween (Sum.inl s) (Sum.inl t) ↔ G.ConnectedBetween s t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw, hf, hl⟩ := h
    exact hw.connBetween_of_mixedLineGraph hf hl
  obtain ⟨w, hw, rfl, rfl⟩ := h
  use mixedLineGraph_walkMap w, hw.mixedLineGraph_walkMap, by simp, by simp

lemma connBetween_mixedLineGraph_del_iff :
    (L'(G) - (Sum.inl '' X ∪ Sum.inr '' F)).ConnectedBetween (Sum.inl s) (Sum.inl t) ↔
    (G - X ＼ F).ConnectedBetween s t := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw, hf, hl⟩ := h
    obtain ⟨hw, hV, hE⟩ := by simpa only [isWalk_vertexDelete_iff, disjoint_union_right] using hw
    sorry
  sorry

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

-- lemma alternates {a b e w} (hP : L'(G).IsWalk (cons (Sum.inl x) a (cons e b w))) :
--     Sum.isRight e := by
--   simp only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
--     Prod.mk.injEq, Sum.inl.injEq, Prod.swap_prod_mk, reduceCtorEq, and_false, or_false] at hP
--   obtain ⟨⟨ha, rfl, hab⟩, ⟨hb, (⟨rfl, hwf⟩ | ⟨hwf, rfl⟩)⟩, hw⟩ := hP
--   · simp at hab
--   simp

-- lemma match_stuff {w : WList (α ⊕ β) (α × β)} (hP : L'(G).IsWalk w) (hwf : Sum.isLeft w.first)
--     (hwl : Sum.isLeft w.last) : (∃ x : α, w = nil (Sum.inl x)) ∨
--     ∃ x e y w', w = cons (Sum.inl x) (x, e) (cons (Sum.inr e) (y, e) w') ∧ w'.first = Sum.inl y :=by
--   match w with
--   | .nil (Sum.inl x) => simp
--   | .cons (Sum.inl x) (a, b) (nil (Sum.inl y)) => simp at hP
--   | .cons (Sum.inl x) (a, b) (cons c d w') =>
--     have := alternates hP
--     match c with
--     | Sum.inr e =>
--     simp_all only [cons_isWalk_iff, first_cons, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff',
--       Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Prod.swap_prod_mk, reduceCtorEq, and_self,
--       or_false, false_and, false_or, Sum.isLeft_inl, last_cons, Sum.isRight_inr, exists_false,
--       cons.injEq, ↓existsAndEq, and_true, true_and, and_self_left]
--     obtain ⟨⟨hda, rfl, rfl⟩, ⟨hd, hwf, rfl⟩, hw⟩ := hP
--     use d.1, rfl, hwf.symm

-- def bar [DecidableEq α] :
--     {P // L'(G).IsPath P ∧ Sum.isLeft P.first ∧ Sum.isLeft P.last} → {P // G.IsPath P} := by
--   rintro ⟨P, hP, hPf, hPl⟩
--   match P with
--   | .nil (Sum.inl u) =>
--     simp only [nil_isPath_iff, mixedLineGraph_vertexSet, mem_union, mem_image, Sum.inl.injEq,
--       exists_eq_right, reduceCtorEq, and_false, exists_false, or_false] at hP
--     use nil u, by simpa, by simp
--   | .cons (Sum.inl x) (a, b) (nil (Sum.inl y)) => simp at hP
--   | .cons (Sum.inl u) (a, b) (cons c d w) =>
--     have := alternates hP.isWalk
--     match c with
--     | Sum.inr e =>
--     simp only [cons_isPath_iff, mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
--       reduceCtorEq, false_and, Prod.swap_prod_mk, Sum.inr.injEq, false_or, first_cons,
--       Sum.inl.injEq, and_self, or_false, mem_cons_iff] at hP
--     obtain ⟨⟨hw, ⟨hd, hwf, rfl⟩, hdw⟩, ⟨hda, rfl, rfl⟩, haw⟩ := hP
--     obtain ⟨P', hP'⟩ := bar ⟨w, hw, by sorry, by simpa using hPl⟩
--     use cons a d.2 P'
--     simp [hP']
--     sorry

-- def EquivPathmixedLineGraphPath :
--     {P // G.IsPath P} ≃ {P // L'(G).IsPath P ∧ Sum.isLeft P.first ∧ Sum.isLeft P.last} where
--   toFun P := by
--     obtain ⟨P, hP⟩ := P
--     use mixedLineGraph_walkMap P, hP.mixedLineGraph_walkMap, by simp, by simp
--   invFun P := by
--     obtain ⟨P, hP, hPf, hPl⟩ := P

theorem Menger'sTheorem_mixed [G.Finite] (hs : s ∈ V(G)) (ht : t ∈ V(G)) (hι : ENat.card ι = n) :
    (∀ X ⊆ V(G), s ∉ X ∧ t ∉ X → ∀ F ⊆ E(G), ¬ (G - X ＼ F).ConnectedBetween s t →
    n ≤ X.encard + F.encard) ↔ ∃ A : G.VertexEnsemble s t ι, A.edgeDisjoint := by
  have : L'(G).Finite := by sorry
  convert (L'(G)).Menger'sTheorem_vertex (by simpa : Sum.inl s ∈ _) (by simpa : Sum.inl t ∈ _) hι
  · refine ⟨fun h ⟨C, hC, hsC, htC, hCconn⟩ ↦ ?_, fun h X hX ⟨hsX, htX⟩ F hF hXF ↦ ?_⟩
    · change n ≤ C.encard
      rw [← image_preimage_inl_union_image_preimage_inr C, encard_union_eq (by simp),
      Sum.inl_injective.encard_image, Sum.inr_injective.encard_image]
      refine h (Sum.inl ⁻¹' C) ?_ (by tauto) (Sum.inr ⁻¹' C) ?_ ?_
      · exact preimage_subset_iff.mpr fun x hxC ↦ by simpa using hC hxC
      · exact preimage_subset_iff.mpr fun e heC ↦ by simpa using hC heC
      contrapose! hCconn
      clear h hι
      obtain ⟨w, hw, rfl, rfl⟩ := hCconn
      use mixedLineGraph_walkMap w, ?_, by simp, by simp
      simp only [isWalk_edgeDelete_iff, isWalk_vertexDelete_iff, mixedLineGraph_walkMap_vertexSet,
        disjoint_union_left] at hw ⊢
      use hw.1.1.mixedLineGraph_walkMap, ?_, ?_ <;> simp_rw [disjoint_iff_forall_notMem] at hw ⊢
      <;> rintro a ⟨x, hx, rfl⟩
      · simpa using hw.1.2 hx
      simpa using hw.2 hx
    specialize h ⟨Sum.inl '' X ∪ Sum.inr '' F, ?_, by simpa, by simpa, ?_⟩
    · simp [Sum.inl_injective.preimage_image, Sum.inr_injective.preimage_image, hX, hF]
    · contrapose! hXF
      sorry
      -- rwa [← connBetween_mixedLineGraph_iff, mixedLineGraph_edgeDelete, mixedLineGraph_vertexDelete,
      -- vertexDelete_vertexDelete]
    change n ≤ (Sum.inl '' X ∪ Sum.inr '' F).encard at h
    rwa [encard_union_eq (by simp), Sum.inl_injective.encard_image,
    Sum.inr_injective.encard_image] at h
  sorry

variable {α' β' : Type*} {H H' : Graph α' β'}

-- def Walk.IsPrefix (w w' : G.Walk) : Prop := w.val.IsPrefix w'.val

-- def Walk.reverse (w : G.Walk) : G.Walk := ⟨w.val.reverse, w.prop.reverse⟩

-- structure WalkHom (G : Graph α β) (H : Graph α' β') where
--   walkMap : G.Walk → H.Walk
--   IsPrefix' ⦃w w' : G.Walk⦄ : w.IsPrefix w' → (walkMap w).IsPrefix (walkMap w')
--   reverse' ⦃w⦄ : walkMap w.reverse = (walkMap w).reverse

-- def vxMap (F : G.WalkHom H) : α → α'

end Graph
