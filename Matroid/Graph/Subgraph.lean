import Matroid.Graph.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.TFAE
import Mathlib.Data.Set.Card

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

open Set Partition

open scoped Sym2

namespace Graph

/-- `Copy` creates an identical graph with different definitions for its vertex set and edge set.
  This is mainly used to create graphs with improved definitional properties. -/
@[simps]
def copy (G : Graph α β) {dup : Partition (Set α)} {E : Set β} {IsLink : β → α → α → Prop}
    (hdup : G.Dup = dup) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    Graph α β where
  Dup := dup
  edgeSet := E
  IsLink := IsLink
  isLink_symm e he x y := by
    simp_rw [← h_isLink]
    apply G.isLink_symm (hE ▸ he)
  dup_or_dup_of_isLink_of_isLink := by
    simp_rw [← h_isLink, ← hdup]
    exact G.dup_or_dup_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← h_isLink, ← hE]
    exact G.edge_mem_iff_exists_isLink
  refl_of_isLink := by
    simp_rw [← h_isLink, ← hdup, ]
    exact G.refl_of_isLink
  isLink_of_dup := by
    simp_rw [← h_isLink, ← hdup]
    exact G.isLink_of_dup

lemma copy_eq_self (G : Graph α β) {dup : Partition (Set α)} {E : Set β} {IsLink : β → α → α → Prop}
    (hdup : G.Dup = dup) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hdup hE h_isLink = G := by
  ext <;> simp_all

/-- `foo H G` means that `V(H) ⊆ V(G)`, and every link in `H` is a link in `G`. -/
structure IsLabelSubgraph (H G : Graph α β) : Prop where
  dup_induce : G.Dup.induce V(H) = H.Dup
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

/-- `H ≤l G` means that `H` is a label subgraph of `G`. -/
scoped infixl:50 " ≤l " => Graph.IsLabelSubgraph

lemma IsLabelSubgraph.dup_iff (hlle : H ≤l G) :
    ∀ ⦃x y⦄, x ∈ V(H) → y ∈ V(H) → (G.Dup x y ↔ H.Dup x y) := by
  intro x y hx hy
  rw [← hlle.dup_induce]
  simp [induce_rel, hx, hy]

lemma isLabelSubgraph_rfl {G : Graph α β} : G ≤l G := ⟨by simp [induce_eq_self_iff], by simp⟩

instance : IsRefl (Graph α β) IsLabelSubgraph where
  refl _ := isLabelSubgraph_rfl

lemma IsLabelSubgraph.trans (h₁ : H ≤l G) (h₂ : G ≤l K) : H ≤l K where
  dup_induce := by
    rw [← h₁.dup_induce, ← h₂.dup_induce, induce_induce]
    congr
    exact right_eq_inter.mpr <| supp_le_of_le <| h₁.dup_induce ▸ induce_le
  isLink_of_isLink _ _ _ h := h₂.2 (h₁.2 h)

instance : IsTrans (Graph α β) IsLabelSubgraph where
  trans _ _ _ := IsLabelSubgraph.trans

lemma IsLabelSubgraph.antisymm (h₁ : G ≤l H) (h₂ : H ≤l G) : G = H := by
  refine Graph.ext ?_ fun e x y ↦ ⟨fun a ↦ h₁.isLink_of_isLink a, fun a ↦ h₂.isLink_of_isLink a⟩
  ext x y
  by_cases hx : x ∈ V(G)
  · by_cases hy : y ∈ V(G)
    · exact (h₁.dup_iff hx hy).symm
    simp only [not_dup_of_not_right_mem hy, false_iff]
    contrapose! hy
    rw [← h₂.dup_iff hy.left_mem hy.right_mem] at hy
    exact hy.symm.left_mem
  simp only [not_dup_of_not_left_mem hx, false_iff]
  contrapose! hx
  rw [← h₂.dup_iff hx.left_mem hx.right_mem] at hx
  exact hx.left_mem

instance : IsAntisymm (Graph α β) IsLabelSubgraph where
  antisymm _ _ := IsLabelSubgraph.antisymm

lemma IsLabelSubgraph.dup (h : H.Dup x y) (hlle : H ≤l G) : G.Dup x y := by
  rwa [hlle.dup_iff h.left_mem h.right_mem]

lemma IsLabelSubgraph.dup_of_mem (h : G.Dup x y) (hlle : H ≤l G) (hx : x ∈ V(H))
    (hy : y ∈ V(H)) : H.Dup x y := by rwa [← hlle.dup_iff hx hy]

lemma IsLabelSubgraph.not_dup (h : ¬ G.Dup x y) (hlle : H ≤l G) : ¬ H.Dup x y :=
  fun h' ↦ h <| hlle.dup h'

lemma IsLabelSubgraph.not_dup_of_mem (h : ¬ H.Dup x y) (hlle : H ≤l G)
    (hx : x ∈ V(H)) (hy : y ∈ V(H)) : ¬ G.Dup x y :=
  fun h' ↦ h <| hlle.dup_of_mem h' hx hy

lemma IsLabelSubgraph.dup_iff_dup_of_mem (hlle : H ≤l G) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    G.Dup x y ↔ H.Dup x y :=
  ⟨(hlle.dup_of_mem · hx hy), hlle.dup⟩

lemma IsLink.of_isLabelSubgraph (h : H.IsLink e x y) (hlle : H ≤l G) : G.IsLink e x y :=
  hlle.isLink_of_isLink h
alias IsLabelSubgraph.isLink := IsLink.of_isLabelSubgraph

lemma LabelUnique.of_isLabelSubgraph (hlle : H ≤l G) [G.Nodup] : H.Nodup where
  le_eq _ _ hdup := dup_eq <| hlle.dup hdup

lemma IsLink.of_isLabelSubgraph_of_mem_mem (h : G.IsLink e x y) (hlle : H ≤l G) (he : e ∈ E(H))
    (hx : x ∈ V(H)) (hy : y ∈ V(H)) : H.IsLink e x y := by
  obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩ := h.dup_and_dup_or_dup_and_dup <| hlle.isLink_of_isLink hl
  · have hxu' := hlle.dup_of_mem hxu hx hl.left_mem
    have hyv' := hlle.dup_of_mem hyv hy hl.right_mem
    rwa [isLink_left_rw hxu', isLink_right_rw hyv']
  · have hxv' := hlle.dup_of_mem hxv hx hl.right_mem
    have hyu' := hlle.dup_of_mem hyu hy hl.left_mem
    rwa [isLink_left_rw hxv', isLink_right_rw hyu', isLink_comm]
alias IsLabelSubgraph.isLink_of_mem_mem := IsLink.of_isLabelSubgraph_of_mem_mem

lemma IsLabelSubgraph.isLink_iff_isLink_of_mem_mem (hlle : H ≤l G) (he : e ∈ E(H)) (hx : x ∈ V(H))
    (hy : y ∈ V(H)) : G.IsLink e x y ↔ H.IsLink e x y :=
  ⟨(·.of_isLabelSubgraph_of_mem_mem hlle he hx hy), (hlle.isLink_of_isLink ·)⟩

lemma IsLabelSubgraph.vertexSet (hlle : H ≤l G) : V(H) ⊆ V(G) := by
  rintro x hxH
  rwa [← G.dup_refl_iff, hlle.dup_iff hxH hxH, H.dup_refl_iff]

lemma IsLabelSubgraph.edgeSet (hlle : H ≤l G) : E(H) ⊆ E(G) := by
  rintro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_isLabelSubgraph hlle).edge_mem

lemma exists_isLink_of_isLabelSubgraph_of_mem_edgeSet (hlle : H ≤l G) (he : e ∈ E(H)) :
    ∃ u v, G.IsLink e u v ∧ H.IsLink e u v := by
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, hlle.isLink_of_isLink h', h'⟩

lemma isLabelSubgraph_iff : H ≤l G ↔ (G.Dup.induce V(H) = H.Dup) ∧
    ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.dup_induce, h.isLink_of_isLink⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma isLabelSubgraph_of (hdup : G.Dup.induce V(H) = H.Dup)
    (hlink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y) : H ≤l G :=
  ⟨hdup, hlink⟩

-- lemma isLabelSubgraph_iff_of_Nodup [G.Nodup] [H.Nodup] :
--     H ≤l G ↔ (V(H) ⊆ V(G)) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
--   ⟨fun h ↦ ⟨h.vertexSet, h.isLink_of_isLink⟩,
--     fun h ↦ ⟨by sorry, h.2⟩⟩

lemma Inc.of_isLabelSubgraph (h : H.Inc e x) (hlle : H ≤l G) : G.Inc e x :=
  (h.choose_spec.of_isLabelSubgraph hlle).inc_left
alias IsLabelSubgraph.Inc := Inc.of_isLabelSubgraph

lemma Inc.of_isLabelSubgraph_of_mem_mem (h : G.Inc e x) (hlle : H ≤l G) (he : e ∈ E(H))
    (hx : x ∈ V(H)) : H.Inc e x := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain hxu | hxv := h.dup_or_dup_of_isLink (huv.of_isLabelSubgraph hlle)
  · rw [hlle.dup_iff hx huv.left_mem] at hxu
    exact ⟨v, huv.dup_left hxu.symm⟩
  rw [hlle.dup_iff hx huv.right_mem] at hxv
  exact ⟨u, huv.symm.dup_left hxv.symm⟩
alias IsLabelSubgraph.Inc_of_mem_mem := Inc.of_isLabelSubgraph_of_mem_mem

lemma exists_inc_of_isLabelSubgraph_of_mem (hlle : H ≤l G) (he : e ∈ E(H)) :
    ∃ u, G.Inc e u ∧ H.Inc e u := by
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, ⟨y, hlle.isLink_of_isLink h'⟩, ⟨y, h'⟩⟩

lemma IsLoopAt.of_isLabelSubgraph (h : H.IsLoopAt e x) (hlle : H ≤l G) : G.IsLoopAt e x :=
  IsLink.of_isLabelSubgraph h hlle
alias IsLabelSubgraph.isLoopAt := IsLoopAt.of_isLabelSubgraph

lemma IsNonloopAt.of_isLabelSubgraph (h : H.IsNonloopAt e x) (hlle : H ≤l G) :
    G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hlle.not_dup_of_mem hxy he.left_mem he.right_mem, he.of_isLabelSubgraph hlle⟩
alias IsLabelSubgraph.isNonloopAt := IsNonloopAt.of_isLabelSubgraph

lemma Adj.of_isLabelSubgraph (h : H.Adj x y) (hlle : H ≤l G) : G.Adj x y :=
  (h.choose_spec.of_isLabelSubgraph hlle).adj
alias IsLabelSubgraph.adj := Adj.of_isLabelSubgraph

-- lemma IsLabelSubgraph.of_isLabelSubgraph_isLabelSubgraph_subset_subset {H₁ H₂ : Graph α β}
--     (h₁ : H₁ ≤l G) (h₂ : H₂ ≤l G) (hV : V(H₁) ⊆ V(H₂)) (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤l H₂ where
--   dup_iff x y hxH hyH := by rw [← h₁.dup_iff hxH hyH, h₂.dup_iff (hV hxH) (hV hyH)]
--   isLink_of_isLink e x y h :=
--     (h.of_isLabelSubgraph h₁).of_isLabelSubgraph_of_mem_mem h₂
--     (hE h.edge_mem) (hV h.left_mem) (hV h.right_mem)

-- lemma ext_of_isLabelSubgraph_eq_Set {H₁ H₂ : Graph α β} (h₁ : H₁ ≤l G) (h₂ : H₂ ≤l G)
--     (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
--   (h₁.of_isLabelSubgraph_isLabelSubgraph_subset_subset h₂ hV.subset hE.subset).antisymm <|
--     (h₂.of_isLabelSubgraph_isLabelSubgraph_subset_subset h₁ hV.symm.subset hE.symm.subset)

/-- A label subgraph of `G` is a subgraph where each vertex retains all of its labels. -/
@[mk_iff]
structure IsSubgraph (H G : Graph α β) : Prop where
  dup_subset : H.Dup ⊆ G.Dup
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

instance : LE (Graph α β) where
  le := IsSubgraph

-- @[simp]
-- def isLabelSubgraph_of_le (h : H ≤ G) : H ≤l G where
--   dup_iff a b hx hy := by
--     refine ⟨Partition.subset⟩
--   isLink_of_isLink := h.isLink_of_isLink

-- lemma le_of_isLabelSubgraph [G.Nodup] (h : H ≤l G) : H ≤ G where
--   toIsLabelSubgraph := h
--   dup_closed _ _ hxy hx := hxy.eq ▸ hx

lemma dup_of_le (hdup : H.Dup x y) (hle : H ≤ G) : G.Dup x y :=
  Partition.rel_le_of_subset hle.dup_subset _ _ hdup

lemma dup_of_le_of_mem (hdup : G.Dup x y) (hle : H ≤ G) (hx : x ∈ V(H)) : H.Dup x y :=
  rel_of_subset_mem hle.dup_subset hx hdup

lemma not_dup_of_le (h : ¬ G.Dup x y) (hle : H ≤ G) : ¬ H.Dup x y :=
  fun h' ↦ h (dup_of_le h' hle)

lemma not_dup_of_le_of_mem (h : ¬ H.Dup x y) (hle : H ≤ G) (hx : x ∈ V(H)) : ¬ G.Dup x y :=
  fun h' ↦ h (dup_of_le_of_mem h' hle hx)

lemma dup_iff_dup_of_le_of_mem (hle : H ≤ G) (hx : x ∈ V(H)) : G.Dup x y ↔ H.Dup x y :=
  ⟨(dup_of_le_of_mem · hle hx), (dup_of_le · hle)⟩

lemma le_iff : H ≤ G ↔ (H.Dup ⊆ G.Dup) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.dup_subset, h.isLink_of_isLink⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma le_of (hsu : H.Dup ⊆ G.Dup) (hlink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y) :
    H ≤ G := by
  rw [le_iff]
  exact ⟨hsu, hlink⟩

lemma mem_iff_mem_of_le_dup (hdup : G.Dup x y) (hle : H ≤ G) : x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  on_goal 2 => rw [comm_of G.Dup] at hdup
  all_goals rw [dup_iff_dup_of_le_of_mem hle h] at hdup; exact hdup.right_mem

lemma Nodup.of_le (hle : H ≤ G) [G.Nodup] : H.Nodup where
  le_eq _ _ hdup := dup_eq <| dup_of_le hdup hle

lemma IsLink.of_le (h : H.IsLink e x y) (hle : H ≤ G) : G.IsLink e x y :=
  hle.isLink_of_isLink h

lemma IsLink.of_le_of_mem (h : G.IsLink e x y) (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨hux, hvy⟩ | ⟨huy, hvx⟩ := (huv.of_le hle).dup_and_dup_or_dup_and_dup h
  · rw [dup_iff_dup_of_le_of_mem hle huv.left_mem] at hux
    rw [dup_iff_dup_of_le_of_mem hle huv.right_mem] at hvy
    rwa [isLink_left_rw hux.symm, isLink_right_rw hvy.symm]
  · rw [dup_iff_dup_of_le_of_mem hle huv.left_mem] at huy
    rw [dup_iff_dup_of_le_of_mem hle huv.right_mem] at hvx
    rwa [isLink_right_rw huy.symm, isLink_left_rw hvx.symm, isLink_comm]

lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y := ⟨(·.of_le_of_mem hle he), (·.of_le hle)⟩

lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) := supp_le_of_subset h.dup_subset

lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  rintro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

/-- The subgraph order is a partial order on graphs. -/
instance : PartialOrder (Graph α β) where
  le_refl _ := sorry
  le_trans G₁ G₂ G₃ h₁ h₂ :=
    ⟨h₁.toIsLabelSubgraph.trans h₂.toIsLabelSubgraph,
    fun x y hdup hx => h₁.dup_closed (hdup.of_le_of_mem h₂ <| vertexSet_mono h₁ hx) hx⟩
  le_antisymm G H h₁ h₂ := h₁.toIsLabelSubgraph.antisymm h₂.toIsLabelSubgraph

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  h.of_isLabelSubgraph hle.toIsLabelSubgraph

lemma Inc.of_le_of_mem (h : G.Inc e x) (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e x :=
  h.of_isLabelSubgraph_of_mem_mem hle.toIsLabelSubgraph he
  <| h.choose_spec.of_le_of_mem hle he |>.left_mem

lemma IsLoopAt.of_le (h : H.IsLoopAt e x) (hle : H ≤ G) : G.IsLoopAt e x :=
  IsLink.of_le h hle

lemma IsNonloopAt.of_le (h : H.IsNonloopAt e x) (hle : H ≤ G) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, not_dup_of_le_of_mem hxy hle he.left_mem, he.of_le hle⟩

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma le_of_le_isLabelSubgraph_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤l G)
    (hV : V(H₁) ⊆ V(H₂)) (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  toIsLabelSubgraph :=
    h₁.toIsLabelSubgraph.of_isLabelSubgraph_isLabelSubgraph_subset_subset h₂ hV hE
  dup_closed _ _ hxy hx := hxy.of_isLabelSubgraph h₂ |>.mem_iff_mem_of_le h₁ |>.mp hx

lemma le_of_isLabelSubgraph_of_isLabelSubgraph {G₁ : Graph α β} (hHG : H ≤ G) (hHG₁ : H ≤l G₁)
    (hG₁ : G₁ ≤l G): H ≤ G₁ where
  toIsLabelSubgraph := hHG₁
  dup_closed _ _ hxy hx := hHG.Dup_closed (hxy.of_isLabelSubgraph hG₁) hx

lemma isLink_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e = G.IsLink e := by
  ext x y
  exact ⟨fun h ↦ h.of_le hle, fun h ↦ h.of_le_of_mem hle he⟩

lemma isLink_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLink G.IsLink E(H) :=
  fun _ ↦ isLink_eq_of_le hle

lemma inc_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e = G.Inc e := by
  unfold Graph.Inc
  rw [isLink_eq_of_le hle he]

lemma inc_eqOn_of_le (hle : H ≤ G) : EqOn H.Inc G.Inc E(H) :=
  fun _ ↦ inc_eq_of_le hle

lemma isLoopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLoopAt e = G.IsLoopAt e := by
  unfold Graph.IsLoopAt
  rw [isLink_eq_of_le hle he]

lemma isLoopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) :=
  fun _ ↦ isLoopAt_eq_of_le hle

lemma isNonloopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) :
    H.IsNonloopAt e = G.IsNonloopAt e := by
  ext x
  refine exists_congr fun y ↦ ?_
  simp only [isLink_eq_of_le hle he, and_congr_left_iff, not_iff_not]
  exact fun hl => hle.dup_iff (hl.of_le_of_mem hle he).left_mem
    (hl.of_le_of_mem hle he).right_mem |>.symm

lemma isNonloopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) :=
  fun _ ↦ isNonloopAt_eq_of_le hle

/- TODO : Is is reasonable to only keep the `EqOn` versions of the above?
Also, what about functional `≤` versions? -/

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (h : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at h
  obtain ⟨hle, hne⟩ := h
  simp only [ssubset_iff_subset_ne, vertexSet_mono hle, ne_eq, true_and, edgeSet_mono hle]
  contrapose! hne
  exact ext_of_isLabelSubgraph_eq_Set hle.toIsLabelSubgraph isLabelSubgraph_rfl hne.1 hne.2

lemma sum_ncard_lt_of_lt [Finite α] [Finite β] (h : G < H) :
    V(G).ncard + E(G).ncard < V(H).ncard + E(H).ncard := by
  obtain hV | hE := vertexSet_ssubset_or_edgeSet_ssubset_of_lt h
  · have hE' : E(G) ⊆ E(H) := edgeSet_mono h.1
    have hVncard : V(G).ncard < V(H).ncard := ncard_lt_ncard hV
    have hEncard : E(G).ncard ≤ E(H).ncard := ncard_le_ncard hE'
    omega
  · have hV' : V(G) ⊆ V(H) := vertexSet_mono h.1
    have hVncard : V(G).ncard ≤ V(H).ncard := ncard_le_ncard hV'
    have hEncard : E(G).ncard < E(H).ncard := ncard_lt_ncard hE
    omega

instance [Finite α] [Finite β] : WellFoundedLT (Graph α β) :=
  ⟨Subrelation.wf sum_ncard_lt_of_lt (measure fun (G : Graph α β) => V(G).ncard + E(G).ncard).2⟩


/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps isLink]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  dup := G.Dup
  dup_refl_iff := G.Dup_refl_iff
  dup_symm := G.Dup_symm
  dup_trans := G.Dup_trans
  edgeSet := E₀ ∩ E(G)
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1, h.2.symm⟩
  isLink_of_dup _ _ _ _ hxy := by simp [hxy.isLink_left]
  dup_or_dup_of_isLink_of_isLink _ _ _ _ _ h h' :=
    G.Dup_or_dup_of_isLink_of_isLink h.2 h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [h, G.exists_isLink_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  left_mem_of_isLink _ _ _ h := h.2.left_mem

/-- `G ↾ F` is the subgraph of `G` restricted to the edges in `F`. Vertices are not changed. -/
scoped infixl:65 " ↾ "  => Graph.edgeRestrict

@[simp]
lemma edgeRestrict_edgeSet (G : Graph α β) (E₀ : Set β) : E(G ↾ E₀) = E₀ ∩ E(G) := rfl

@[simp]
lemma edgeRestrict_vertexSet (G : Graph α β) (E₀ : Set β) : V(G ↾ E₀) = V(G) := rfl

@[simp]
lemma edgeRestrict_dup (G : Graph α β) (E₀ : Set β) (x y : α) : (G ↾ E₀).dup x y ↔ G.Dup x y := by
  rfl

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  dup_iff x y hx := by simp [edgeRestrict]
  isLink_of_isLink := by simp
  dup_closed x y hxy hx := hxy.right_mem

instance [G.Nodup] : LabelUnique (G ↾ F) := LabelUnique.of_le (edgeRestrict_le)

@[simp]
lemma edgeRestrict_inc_iff : (G ↾ F).Inc e x ↔ G.Inc e x ∧ e ∈ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeRestrict_isLoopAt_iff : (G ↾ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∈ F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
lemma edgeRestrict_isNonloopAt_iff : (G ↾ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∈ F := by
  simp_rw [IsNonloopAt]
  aesop

lemma edgeRestrict_mono_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  dup_iff x y hx := by simp [edgeRestrict]
  isLink_of_isLink _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩
  dup_closed x y hxy hx := hxy.right_mem

lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F :=
  le_of_le_isLabelSubgraph_subset_subset (edgeRestrict_le.trans h)
    (edgeRestrict_le).toIsLabelSubgraph (by simpa using vertexSet_mono h)
    <| by simp [inter_subset_right.trans (edgeSet_mono h)]

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F :=
  ext_of_isLabelSubgraph_eq_Set (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F := by
  rw [inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  ext_of_isLabelSubgraph_eq_Set (G := G) (by simp) (by simp) rfl (by simp)

lemma edgeRestrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_isLabelSubgraph_eq_Set ?_ (by simp) (by simp) ?_
  · exact (edgeRestrict_le).toIsLabelSubgraph.trans (by simp)
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm F₂]

@[simp]
lemma le_edgeRestrict_iff : H ≤ (G ↾ F) ↔ H ≤ G ∧ E(H) ⊆ F :=
  ⟨fun h ↦ ⟨h.trans (by simp), (edgeSet_mono h).trans (by simp)⟩,
    fun h ↦ le_of_le_isLabelSubgraph_subset_subset h.1 (by simp) (by simpa using vertexSet_mono h.1)
    <| subset_inter h.2 (edgeSet_mono h.1)⟩

/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[simps!]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (E := E(G) \ F)
  (IsLink := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl
  (by simp [diff_subset])
  (fun e x y ↦ by
    simp only [edgeRestrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

/-- `G ＼ F` is the subgraph of `G` with the edges in `F` deleted. Vertices are not changed. -/
scoped infixl:65 " ＼ "  => Graph.edgeDelete

lemma edgeDelete_eq_edgeRestrict (G : Graph α β) (F : Set β) :
    G ＼ F = G ↾ (E(G) \ F) := copy_eq_self ..

@[simp]
lemma edgeDelete_inc_iff : (G ＼ F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeDelete_isLoopAt_iff : (G ＼ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isLoopAt_iff, mem_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem
lemma edgeDelete_isNonloopAt_iff : (G ＼ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isNonloopAt_iff, mem_diff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma edgeDelete_le : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

instance [G.Nodup] : LabelUnique (G ＼ F) := LabelUnique.of_le (edgeDelete_le)

@[simp]
lemma edgeDelete_inter_edgeSet : G ＼ (F ∩ E(G)) = G ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeDelete_eq_edgeRestrict, diff_inter_self_eq_diff]

lemma edgeDelete_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

lemma edgeDelete_mono_left (h : H ≤ G) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (E(H) \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left (edgeSet_mono h)

@[simp]
lemma edgeDelete_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ＼ F₂ = G ＼ (F₁ ∪ F₂) := by
  simp only [edgeDelete_eq_edgeRestrict, diff_eq_compl_inter, edgeRestrict_inter_edgeSet,
    edgeRestrict_edgeSet, edgeRestrict_edgeRestrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ↾ F₁ ＼ F₂ = G ↾ (F₁ \ F₂) := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_edgeSet, diff_eq,
    ← inter_assoc, ← inter_assoc, inter_self, inter_comm F₁, inter_assoc,
    edgeRestrict_edgeSet_inter, diff_eq]

lemma edgeDelete_eq_self (G : Graph α β) (hF : Disjoint E(G) F) : G ＼ F = G := by
  simp [edgeDelete_eq_edgeRestrict, hF.sdiff_eq_left]

@[simp]
lemma le_edgeDelete_iff : H ≤ G ＼ F ↔ H ≤ G ∧ Disjoint E(H) F := by
  simp only [edgeDelete_eq_edgeRestrict, le_edgeRestrict_iff, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun hle _ ↦ edgeSet_mono hle

lemma IsNonloopAt.isLoopAt_delete (h : G.IsNonloopAt e x) : (G ＼ {e}).IsLoopAt = G.IsLoopAt := by
  ext f y
  simp only [← isLink_self_iff, edgeDelete_isLink, mem_singleton_iff, and_iff_left_iff_imp]
  rintro h' rfl
  exact h.not_isLoopAt y h'

lemma IsLoopAt.isNonloopAt_delete (h : G.IsLoopAt e x) :
    (G ＼ {e}).IsNonloopAt = G.IsNonloopAt := by
  ext f y
  simp only [isNonloopAt_iff_inc_not_isLoopAt, edgeDelete_inc_iff, mem_singleton_iff, ←
    isLink_self_iff, edgeDelete_isLink, not_and, not_not]
  obtain rfl | hne := eq_or_ne f e
  · simp only [not_true_eq_false, and_false, isLink_self_iff, implies_true, and_true,
      false_iff, not_and, not_not]
    exact fun h' ↦ h.dup (h.dup_of_inc h')
  simp [hne]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[simps! dup vertexSet]
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  dup x y := x ∈ X ∧ y ∈ X ∧ (G.Dup x y ∨ x = y)
  dup_refl_iff := by simp
  dup_symm x y := by
    rintro ⟨hx, hy, h | rfl⟩
    on_goal 1 => simp only [G.Dup_symm h, true_or, and_true]
    all_goals simp [hx, hy]
  dup_trans x y z := by
    rintro ⟨hx, hy, h | rfl⟩ ⟨hy', hz, h' | rfl⟩ <;> simp [hx, hy, hy', hz] <;> left <;> try tauto
    exact h.trans h'
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm _ _ x := by simp +contextual [G.isLink_comm (x := x)]
  dup_or_dup_of_isLink_of_isLink e a b c d := by
    rintro ⟨hl, ha, hb⟩ ⟨hl', hc, hd⟩
    simp only [ha, hc, true_and, hd]
    refine (G.Dup_or_dup_of_isLink_of_isLink hl hl').imp ?_ ?_ <;> tauto
  left_mem_of_isLink := by simp +contextual
  isLink_of_dup e x y z := by
    rintro ⟨hx, hy, h | rfl⟩ <;> simp only [hx, true_and, hy, imp_self]
    rw [h.isLink_left]
    exact id

/-- `G[X]` is the subgraph of `G` induced by the set `X` of vertices. -/
notation:max G:1000 "[" S "]" => Graph.induce G S

@[simp]
lemma induce_isLink_iff {X : Set α} : G[X].IsLink e x y ↔ G.IsLink e x y ∧ x ∈ X ∧ y ∈ X := Iff.rfl

lemma IsLink.induce (h : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].IsLink e x y :=
  ⟨h, hx, hy⟩

@[simp]
lemma induce_adj_iff {X : Set α} : G[X].Adj x y ↔ G.Adj x y ∧ x ∈ X ∧ y ∈ X := by simp [Adj]

lemma Adj.induce (h : G.Adj x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].Adj x y :=
  induce_adj_iff.mpr ⟨h, hx, hy⟩

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α β) (X : Set α) :
    E(G.induce X) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp]
lemma induce_edgeSet_subset (G : Graph α β) (X : Set α) : E(G.induce X) ⊆ E(G) := by
  rintro e ⟨x,y,h, -, -⟩
  exact h.edge_mem

lemma IsLink.mem_induce_iff [G.Nodup] {X : Set α} (hG : G.IsLink e x y) :
    e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq he <;> simp [hx', hy']

lemma induce_induce (G : Graph α β) [G.Nodup] (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · ext x y
    simp only [induce_dup, dup_iff_eq, edgeRestrict_dup]
    tauto
  simp only [induce_isLink_iff, edgeRestrict_isLink]
  obtain he | he := em' (G.IsLink e x y)
  · simp [he]
  rw [he.mem_induce_iff]
  tauto

lemma induce_isLabelSubgraph (hX : X ⊆ V(G)) : G[X] ≤l G where
  dup_iff x y hx hy := by
    simp_all only [induce_vertexSet, induce_dup, true_and, iff_self_or]
    rintro rfl
    exact G.Dup_refl_iff.mp <| hX hx
  isLink_of_isLink e x y h := h.1

instance [G.Nodup] : LabelUnique (G[X]) where
  labelUniqueAt x y hdup := by
    rw [induce_dup, dup_iff_eq] at hdup
    obtain ⟨-, -, (⟨rfl, -⟩ | rfl)⟩ := hdup <;> rfl

@[simp]
lemma induce_isLabelSubgraph_iff : G[X] ≤l G ↔ X ⊆ V(G) :=
  ⟨IsLabelSubgraph.vertexSet, induce_isLabelSubgraph⟩

lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤l G[Y] where
  dup_iff x y hx hy := by
    simp only [induce_vertexSet] at hx hy
    simp [hx, hy, hXY hx, hXY hy]
  isLink_of_isLink _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

@[simp]
lemma induce_mono_right_iff (G : Graph α β) : G[X] ≤l G[Y] ↔ X ⊆ Y :=
  ⟨IsLabelSubgraph.vertexSet, induce_mono_right G⟩

lemma induce_mono_left [G.Nodup] (h : H ≤l G) (X : Set α) : H[X] ≤l G[X] := by
  have := LabelUnique.of_isLabelSubgraph h
  rw [isLabelSubgraph_iff]
  exact ⟨by simp, fun e x y ⟨hl, hx, hy⟩ => ⟨hl.of_isLabelSubgraph h, hx, hy⟩⟩

lemma induce_mono [G.Nodup] (h : H ≤l G) (hXY : X ⊆ Y) : H[X] ≤l G[Y] :=
  (induce_mono_left h X).trans (G.induce_mono_right hXY)

@[simp]
lemma induce_vertexSet_self (G : Graph α β) : G[V(G)] = G := by
  refine G.ext_of_isLabelSubgraph_eq_Set (by simp) (by simp) rfl <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

lemma le_induce_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ X) : H ≤ G[X] where
  dup_iff x y hx hy := by
    simp only [induce_dup, hV hx, hV hy, h.dup_iff hx hy, true_and, or_iff_left_iff_imp]
    rintro rfl
    rwa [← H.dup_refl_iff]
  isLink_of_isLink _ _ _ h' := ⟨h'.of_le h, hV h'.left_mem, hV h'.right_mem⟩
  dup_closed x y hxy hx := by
    obtain ⟨hxX, hyX, hdup | rfl⟩ := hxy
    · exact h.dup_closed hdup hx
    exact hx

lemma le_induce_self (h : H ≤ G) : H ≤ G[V(H)] :=
  le_induce_of_le_of_subset h rfl.subset

-- lemma le_induce_iff (hX : X ⊆ V(G)) : H ≤ G[X] ↔ H ≤ G ∧ V(H) ⊆ X :=
--   ⟨fun h ↦ ⟨h.trans (by simpa), vertexSet_mono h⟩, fun h ↦ le_induce_of_le_of_subset h.1 h.2⟩

@[simp]
lemma edgeRestrict_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by ext ; simp) fun e x y ↦ ?_
  simp only [induce_isLink_iff, edgeRestrict_isLink]
  tauto

/-- The graph obtained from `G` by deleting a set of vertices. -/
protected def vertexDelete (G : Graph α β) (X : Set α) : Graph α β := G [V(G) \ X]

/-- `G - X` is the graph obtained from `G` by deleting the set `X` of vertices. -/
notation:max G:1000 " - " S:1000 => Graph.vertexDelete G S

-- instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
--   hSub := Graph.vertexDelete

lemma vertexDelete_def (G : Graph α β) (X : Set α) : G - X = G [V(G) \ X] := rfl

@[simp]
lemma vertexDelete_dup (G : Graph α β) (X : Set α) (x y : α) :
    (G - X).dup x y ↔ G.Dup x y ∧ x ∉ X ∧ y ∉ X := by
  simp +contextual only [vertexDelete_def, induce_dup, mem_diff, iff_def, not_false_eq_true,
    and_self, and_true, and_imp, true_or]
  refine ⟨fun hx hxX hy hyX => ?_, fun hdup hxX hyX => ⟨hdup.left_mem, hdup.right_mem⟩⟩
  rintro (hdup | rfl)
  · exact hdup
  rwa [← G.Dup_refl_iff]

@[simp]
lemma vertexDelete_vertexSet (G : Graph α β) (X : Set α) : V(G - X) = V(G) \ X := rfl

@[simp]
lemma vertexDelete_isLink_iff (G : Graph α β) (X : Set α) :
    (G - X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [vertexDelete_def, induce_isLink_iff, mem_diff, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
lemma vertexDelete_edgeSet (G : Graph α β) (X : Set α) :
    E(G - X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOf_exists_isLink]

@[simp]
lemma vertexDelete_empty (G : Graph α β) : G - ∅ = G := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_adj_iff (G : Graph α β) (X : Set α) :
    (G - X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  simp [Adj]

@[simp]
lemma vertexDelete_isLabelSubgraph : G - X ≤l G := G.induce_isLabelSubgraph diff_subset

instance [G.Nodup] : LabelUnique (G - X) :=
  LabelUnique.of_isLabelSubgraph (vertexDelete_isLabelSubgraph)

lemma IsLink.mem_vertexDelete_iff [G.Nodup] {X : Set α} (hG : G.IsLink e x y) :
    e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [vertexDelete_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.left_mem,
    and_iff_right hG.right_mem]

lemma vertexDelete_mono_left (h : H ≤ G) : H - X ≤ G - X where
  dup_iff x y hx hy := by simp [h.dup_iff hx.1 hy.1]
  isLink_of_isLink _ _ _ h' := by simp_all [h.isLink_of_isLink h'.1]
  dup_closed x y hxy hx :=
    ⟨h.dup_closed (vertexDelete_isLabelSubgraph.dup hxy) hx.1, hxy.right_mem.2⟩

lemma vertexDelete_anti_right (hXY : X ⊆ Y) : G - Y ≤l G - X :=
  induce_mono_right _ <| diff_subset_diff_right hXY

lemma edgeRestrict_vertexDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vertexDelete_isLink_iff, edgeRestrict_isLink, edgeRestrict_vertexSet]
  tauto

@[simp]
lemma edgeDelete_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ＼ F)[X] = G[X] ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]

@[simp]
lemma induce_vertexDelete (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
  Graph.ext (by ext; simp +contextual [iff_def]) <| by
  simp only [vertexDelete_isLink_iff, induce_isLink_iff, mem_diff]
  tauto

lemma vertexDelete_vertexDelete (G : Graph α β) (X Y : Set α) : (G - X) - Y = G - (X ∪ Y) := by
  rw [G.vertexDelete_def, induce_vertexDelete, diff_diff, ← vertexDelete_def]

lemma vertexDelete_vertexDelete_comm (G : Graph α β) (X Y : Set α) : (G - X) - Y = (G - Y) - X := by
  rw [vertexDelete_vertexDelete, vertexDelete_vertexDelete, union_comm]

-- @[simp]
-- lemma le_vertexDelete_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
--   simp only [vertexDelete_def]
--   exact fun h _ ↦ vertexSet_mono h

/-! ### Spanning Subgraphs -/

/-- A spanning subgraph of `G` is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop where
  isLabelSubgraph : H ≤l G
  vertexSet_eq : V(H) = V(G)

/-- `H ≤s G` means that `H` is a spanning subgraph of `G`. -/
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

@[simp]
lemma edgeRestrict_isSpanningSubgraph : G ↾ F ≤s G :=
  ⟨by simp, rfl⟩

@[simp]
lemma edgeDelete_isSpanningSubgraph : G ＼ F ≤s G :=
  ⟨by simp, by simp [vertexSet_eq_setOf_dup]⟩

lemma IsSpanningSubgraph.le (hsle : H ≤s G) : H ≤ G where
  toIsLabelSubgraph := hsle.isLabelSubgraph
  dup_closed _ _ hxy _ := hsle.vertexSet_eq ▸ hxy.right_mem

lemma Dup.of_isSpanningSubgraph (hdup : G.Dup x y) (hsle : H ≤s G) : H.dup x y :=
  hdup.of_le_of_mem hsle.le (hsle.vertexSet_eq ▸ hdup.left_mem)

lemma IsSpanningSubgraph.dup_iff_dup (hsle : H ≤s G) : G.Dup x y ↔ H.dup x y :=
  ⟨(·.of_isSpanningSubgraph hsle), (·.of_le hsle.le)⟩

lemma IsSpanningSubgraph.of_isSpanningSubgraph_left (h : H ≤s G) (hHK : H ≤l K) (hKG : K ≤l G) :
    H ≤s K where
  isLabelSubgraph := hHK
  vertexSet_eq := hHK.vertexSet.antisymm (hKG.vertexSet.trans_eq h.vertexSet_eq.symm)

lemma IsSpanningSubgraph.of_isSpanningSubgraph_right (hsle : H ≤s G) (hHK : H ≤l K) (hKG : K ≤l G) :
    K ≤s G where
  isLabelSubgraph := hKG
  vertexSet_eq := hKG.vertexSet.antisymm <| hsle.vertexSet_eq.symm.le.trans hHK.vertexSet

lemma IsSpanningSubgraph.labelUnique [H.LabelUnique] (hsle : H ≤s G) : G.Nodup where
  labelUniqueAt x y hdup := by
    rw [hsle.dup_iff_dup] at hdup
    exact hdup.eq

/-! ### Induced Subgraphs -/

/-- An induced subgraph of `G` is a subgraph `H` of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
structure IsInducedSubgraph (H G : Graph α β) : Prop where
  isLabelSubgraph : H ≤l G
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

/-- `H ≤i G` means that `H` is an induced subgraph of `G`. -/
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

lemma IsInducedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁₂ : G₁ ≤i G₂) (h₂₃ : G₂ ≤i G₃) :
    G₁ ≤i G₃ :=
  ⟨h₁₂.isLabelSubgraph.trans h₂₃.isLabelSubgraph, fun _ _ _ h hx hy ↦ h₁₂.isLink_of_mem_mem
    (h₂₃.isLink_of_mem_mem h (h₁₂.isLabelSubgraph.vertexSet hx) (h₁₂.isLabelSubgraph.vertexSet hy))
    hx hy⟩

lemma isInducedSubgraph_iff :
    H ≤i G ↔ H ≤l G ∧ ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma induce_isInducedSubgraph (hX : X ⊆ V(G)) : G[X] ≤i G :=
  ⟨by simpa, fun e x y h (hx : x ∈ X) (hy : y ∈ X) ↦ by simp_all⟩

@[simp]
lemma induce_isInducedSubgraph_iff : G[X] ≤i G ↔ X ⊆ V(G) := by
  simp +contextual [isInducedSubgraph_iff]

lemma IsInducedSubgraph.induce_vertexSet_eq (h : H ≤i G) : G[V(H)] = H := by
  have hle : G[V(H)] ≤l G := by simp [h.isLabelSubgraph.vertexSet]
  refine G.ext_of_isLabelSubgraph_eq_Set hle h.isLabelSubgraph rfl <| Set.ext fun e ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x, y, h', hx, hy⟩ ↦ (h.isLink_of_mem_mem h' hx hy).edge_mem, fun h' ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h'
  exact ⟨x, y, hxy.of_isLabelSubgraph h.isLabelSubgraph, hxy.left_mem, hxy.right_mem⟩

/-- An induced subgraph is precisely a subgraph of the form `G[X]` for some `X ⊆ V(G)`.
This version of the lemma can be used with `subst` or `obtain rfl` to replace `H` with `G[X]`. -/
lemma IsInducedSubgraph.exists_eq_induce (h : H ≤i G) : ∃ X ⊆ V(G), H = G[X] :=
  ⟨V(H), h.isLabelSubgraph.vertexSet, h.induce_vertexSet_eq.symm⟩

lemma IsInducedSubgraph.adj_of_adj (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    H.Adj x y := by
  obtain ⟨e, hxy⟩ := hxy
  exact (h.isLink_of_mem_mem hxy hx hy).adj

lemma IsInducedSubgraph.eq_of_isSpanningSubgraph (hi : H ≤i G) (hs : H ≤s G) : H = G := by
  obtain ⟨X, hX, rfl⟩ := hi.exists_eq_induce
  simp [show X = V(G) by simpa using hs.vertexSet_eq]

/-! ### Closed Subgraphs -/

/-- A closed subgraph of `G` is a union of components of `G`.  -/
@[mk_iff]
structure IsClosedSubgraph (H G : Graph α β) : Prop extends H ≤ G where
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

/-- `H ≤c G` means that `H` is a closed subgraph of `G`. i.e. a union of components of `G`. -/
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

lemma IsClosedSubgraph.vertexSet (h : H ≤c G) : V(H) ⊆ V(G) := h.toIsLabelSubgraph.vertexSet

lemma IsClosedSubgraph.edgeSet (h : H ≤c G) : E(H) ⊆ E(G) := h.toIsLabelSubgraph.edgeSet

lemma IsClosedSubgraph.le (h : H ≤c G) : H ≤ G := h.toIsSubgraph

lemma IsClosedSubgraph.isInducedSubgraph (h : H ≤c G) : H ≤i G where
  isLabelSubgraph := h.toIsLabelSubgraph
  isLink_of_mem_mem _ _ _ he hx _ := he.of_le_of_mem h.le (h.closed he.inc_left hx)

lemma IsClosedSubgraph.isLabelSubgraph (h : H ≤c G) : H ≤l G := h.toIsLabelSubgraph

lemma Dup.of_isClosedSubgraph (h : H ≤c G) (hdup : H.dup x y) : G.Dup x y := hdup.of_le h.le
alias IsClosedSubgraph.dup := Dup.of_isClosedSubgraph

lemma IsClosedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁ : G₁ ≤c G₂) (h₂ : G₂ ≤c G₃) : G₁ ≤c G₃ where
  toIsSubgraph := le_trans h₁.le h₂.le
  closed _ _ hi hy := h₁.closed (hi.of_le_of_mem h₂.le <| h₂.closed hi <| h₁.vertexSet hy) hy

@[simp]
lemma isClosedSubgraph_self : G ≤c G where
  toIsSubgraph := le_refl G
  closed _ _ he _ := he.edge_mem

lemma Inc.of_isClosedSubgraph_of_mem (h : G.Inc e x) (hle : H ≤c G) (hx : x ∈ V(H)) : H.Inc e x :=
  h.of_le_of_mem hle.le (hle.closed h hx)
alias IsClosedSubgraph.inc_of_mem := Inc.of_isClosedSubgraph_of_mem

lemma Adj.right_mem_of_isClosedSubgraph_of_left_mem (hle : H ≤c G) (hxy : G.Adj x y)
    (hx : x ∈ V(H)) : y ∈ V(H) := by
  obtain ⟨e, h⟩ := hxy
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet <| hle.closed h.inc_left hx
  obtain ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩ := h.dup_and_dup_or_dup_and_dup <| huv.of_le hle.le
  · exact hle.dup_closed hyv.symm huv.right_mem
  exact hle.dup_closed hyu.symm huv.left_mem
alias IsClosedSubgraph.right_mem_of_adj_of_left_mem := Adj.right_mem_of_isClosedSubgraph_of_left_mem

lemma Adj.left_mem_of_isClosedSubgraph_of_right_mem (hle : H ≤c G) (hxy : G.Adj x y)
    (hy : y ∈ V(H)) : x ∈ V(H) :=
  hxy.symm.right_mem_of_isClosedSubgraph_of_left_mem hle hy
alias IsClosedSubgraph.left_mem_of_adj_of_right_mem := Adj.left_mem_of_isClosedSubgraph_of_right_mem

lemma IsLink.of_isClosedSubgraph_of_mem_vertexSet
    (h : G.IsLink e x y) (hle : H ≤c G) (hx : x ∈ V(H)) : H.IsLink e x y :=
  h.of_le_of_mem hle.le (h.inc_left.of_isClosedSubgraph_of_mem hle hx).edge_mem
alias IsClosedSubgraph.isLink_of_mem := IsLink.of_isClosedSubgraph_of_mem_vertexSet

lemma IsClosedSubgraph.isLink_iff_isLink_of_mem (h : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun he ↦ he.of_le h.le, fun he ↦ he.of_isClosedSubgraph_of_mem_vertexSet h hx⟩

lemma IsClosedSubgraph.mem_iff_mem_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← h.isLink_iff_isLink_of_mem hin] at he; exact he.right_mem
alias IsLink.mem_iff_mem_of_isClosedSubgraph := IsClosedSubgraph.mem_iff_mem_of_isLink

lemma IsClosedSubgraph.mem_tfae_of_isLink (h : H ≤c G) (hl : G.IsLink e x y) :
    List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
  tfae_have 1 → 2 := (h.mem_iff_mem_of_isLink hl).mp
  tfae_have 2 → 3 := (hl.symm.of_isClosedSubgraph_of_mem_vertexSet h · |>.edge_mem)
  tfae_have 3 → 1 := (hl.of_le_of_mem h.le · |>.left_mem)
  tfae_finish
alias IsLink.mem_tfae_of_isClosedSubgraph := IsClosedSubgraph.mem_tfae_of_isLink

lemma IsClosedSubgraph.adj_of_mem (h : H ≤c G) (hx : x ∈ V(H)) (hxy : G.Adj x y) :
    H.Adj x y := by
  obtain ⟨e, hexy⟩ := hxy
  exact (hexy.of_isClosedSubgraph_of_mem_vertexSet h hx).adj
alias Adj.of_isClosedSubgraph_of_mem := IsClosedSubgraph.adj_of_mem

lemma IsClosedSubgraph.mem_iff_mem_of_adj (h : H ≤c G) (hxy : G.Adj x y) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  obtain ⟨e, hexy⟩ := hxy
  exact mem_iff_mem_of_isLink h hexy
alias Adj.mem_iff_mem_of_isClosedSubgraph := IsClosedSubgraph.mem_iff_mem_of_adj

lemma IsClosedSubgraph.of_le_of_isLabelSubgraph {G₁ : Graph α β} (hHG : H ≤c G) (hHG₁ : H ≤ G₁)
    (hG₁ : G₁ ≤l G) : H ≤c G₁ where
  toIsSubgraph := hHG₁
  closed _ _ he hx := ((he.of_isLabelSubgraph hG₁).of_isClosedSubgraph_of_mem hHG hx).edge_mem

lemma IsClosedSubgraph.diff {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) :
    H₁ - V(H₂) ≤c G where
  toIsLabelSubgraph := vertexDelete_isLabelSubgraph.trans h₁.toIsLabelSubgraph
  closed e x he hx := by
    simp only [vertexDelete_edgeSet, mem_setOf_eq]
    simp only [vertexDelete_vertexSet, mem_diff] at hx
    obtain ⟨y, hexy⟩ := he
    refine ⟨x, y, hexy.of_isClosedSubgraph_of_mem_vertexSet h₁ hx.1, hx.2, fun hy ↦ hx.2 ?_⟩
    refine (hexy.symm.of_isClosedSubgraph_of_mem_vertexSet h₂ hy).right_mem
  dup_closed x y hxy := by
    simp only [vertexDelete_vertexSet, mem_diff, and_imp]
    rintro hx₁ hx₂
    exact ⟨h₁.dup_closed hxy hx₁, fun hy₂ => hx₂ <| h₂.dup_closed hxy.symm hy₂⟩

lemma IsClosedSubgraph.compl (h : H ≤c G) : G - V(H) ≤c G :=
  G.isClosedSubgraph_self.diff h

-- lemma not_isClosedSubgraph_iff_of_IsInducedSubgraph (hile : H ≤i G) :
--     ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧ x ∈ V(H) ∧ y ∉ V(H) := by
--   rw [not_iff_comm]
--   push_neg
--   exact ⟨fun hncl => ⟨⟨hile.isLabelSubgraph, sorry⟩, fun e x ⟨y, hl⟩ hx =>
--     hile.isLink_of_mem_mem hl hx (hncl x y ⟨e, hl⟩ hx) |>.edge_mem⟩, fun hcl _ _ hxy =>
--     (hcl.mem_iff_mem_of_adj hxy).mp⟩

lemma IsClosedSubgraph.of_edgeDelete_iff (hclF : H ≤c G ＼ F) : H ≤c G ↔ E(G) ∩ F ⊆ E(G - V(H)) := by
  rw [vertexDelete_edgeSet]
  refine ⟨fun hcl f hf ↦ ?_,
    fun hF ↦ ⟨⟨hclF.toIsLabelSubgraph.trans edgeDelete_le.toIsLabelSubgraph,
    fun x y hxy hx => hclF.dup_closed (hxy.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph) hx⟩,
    fun e x he hxH => ?_⟩⟩
  · by_contra! hfH
    simp only [mem_setOf_eq, not_exists, not_and, not_not] at hfH
    refine (hclF.edgeSet ?_).2 hf.2
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hf.1
    obtain hx | hy := or_iff_not_imp_left.mpr <| hfH x y hxy
    · exact hcl.closed ⟨_, hxy⟩ hx
    · exact hcl.closed ⟨_, hxy.symm⟩ hy
  · have heF : e ∉ F := fun heF => by
      obtain ⟨u, v, heuv, hunH, hvnH⟩ := hF ⟨he.edge_mem, heF⟩
      obtain hxu | hxv := he.dup_or_dup_of_isLink heuv
      · exact hunH (hxu.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph
          |>.of_le_of_mem hclF.le hxH |>.right_mem)
      · exact hvnH (hxv.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph
          |>.of_le_of_mem hclF.le hxH |>.right_mem)
    exact hclF.closed (by simp [he, heF]) hxH

/-! ### Components -/

/-- A component of `G` is a minimal nonempty closed subgraph of `G`. -/
def IsCompOf (H G : Graph α β) : Prop := Minimal (fun H ↦ H ≤c G ∧ V(H).Nonempty) H

lemma IsCompOf.isClosedSubgraph (h : H.IsCompOf G) : H ≤c G :=
  h.prop.1

lemma IsCompOf.isInducedSubgraph (hHco : H.IsCompOf G) : H ≤i G :=
  hHco.isClosedSubgraph.isInducedSubgraph

lemma IsCompOf.le (h : H.IsCompOf G) : H ≤ G :=
  h.isClosedSubgraph.le

lemma IsCompOf.nonempty (h : H.IsCompOf G) : V(H).Nonempty :=
  h.prop.2
