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
def copy (G : Graph α β) {V : Set α} {dup : Partition (Set α)} {E : Set β}
    {IsLink : β → α → α → Prop} (hV : V(G) = V) (hdup : G.Dup = dup) (hE : E(G) = E)
    (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  Dup := dup
  vertexSet := V
  vertexSet_eq := hdup ▸ (hV.symm.trans G.vertexSet_eq)
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
  mem_vertexSet_of_isLink := by
    simp_rw [← h_isLink, ← hV]
    exact G.mem_vertexSet_of_isLink
  isLink_of_dup := by
    simp_rw [← h_isLink, ← hdup]
    exact G.isLink_of_dup

lemma copy_eq_self (G : Graph α β) {V : Set α} {dup : Partition (Set α)} {E : Set β}
    {IsLink : β → α → α → Prop} (hV : V(G) = V) (hdup : G.Dup = dup) (hE : E(G) = E)
    (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hdup hE h_isLink = G := by
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
  simp [hx, hy]

lemma IsLabelSubgraph.dup (h : H.Dup x y) (hlle : H ≤l G) : G.Dup x y := by
  rwa [hlle.dup_iff (H.vertexSet_eq ▸ h.left_mem) (H.vertexSet_eq ▸ h.right_mem)]

lemma IsLabelSubgraph.dup_le (hlle : H ≤l G) : H.Dup ≤ G.Dup :=
  le_of_rel_le fun _ _ ↦ hlle.dup

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

lemma IsLabelSubgraph.vertexSet (hlle : H ≤l G) : V(H) ⊆ V(G) := by
  rintro x hxH
  rwa [← G.dup_refl_iff, hlle.dup_iff hxH hxH, H.dup_refl_iff]

lemma isLabelSubgraph_rfl {G : Graph α β} : G ≤l G := ⟨by simp [induce_eq_self_iff], by simp⟩

instance : IsRefl (Graph α β) IsLabelSubgraph where
  refl _ := isLabelSubgraph_rfl

lemma IsLabelSubgraph.trans (h₁ : H ≤l G) (h₂ : G ≤l K) : H ≤l K where
  dup_induce := by
    rw [← h₁.dup_induce, ← h₂.dup_induce, induce_induce]
    congr
    rw [right_eq_inter]
    exact h₁.vertexSet
  isLink_of_isLink _ _ _ h := h₂.2 (h₁.2 h)

instance : IsTrans (Graph α β) IsLabelSubgraph where
  trans _ _ _ := IsLabelSubgraph.trans

lemma IsLabelSubgraph.antisymm (h₁ : G ≤l H) (h₂ : H ≤l G) : G = H := by
  refine Graph.ext ?_ fun e x y ↦ ⟨fun a ↦ h₁.isLink_of_isLink a, fun a ↦ h₂.isLink_of_isLink a⟩
  rw [← h₁.dup_induce, induce_eq_self_iff, H.vertexSet_def]
  exact h₂.vertexSet

instance : IsAntisymm (Graph α β) IsLabelSubgraph where
  antisymm _ _ := IsLabelSubgraph.antisymm

lemma IsLink.of_isLabelSubgraph (h : H.IsLink e x y) (hlle : H ≤l G) : G.IsLink e x y :=
  hlle.isLink_of_isLink h
alias IsLabelSubgraph.isLink := IsLink.of_isLabelSubgraph

lemma Nodup.of_isLabelSubgraph (hlle : H ≤l G) [G.Nodup] : H.Nodup where
  atomic_dup := by
    rw [← hlle.dup_induce]
    exact G.dup_atomic.atomic_of_le induce_le
alias IsLabelSubgraph.Nodup := Nodup.of_isLabelSubgraph

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

lemma IsLabelSubgraph.edgeSet (hlle : H ≤l G) : E(H) ⊆ E(G) := by
  rintro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (hlle.isLink h').edge_mem

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

lemma IsLabelSubgraph.of_isLabelSubgraph_isLabelSubgraph_subset_subset {H₁ H₂ : Graph α β}
    (h₁ : H₁ ≤l G) (h₂ : H₂ ≤l G) (hV : V(H₁) ⊆ V(H₂)) (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤l H₂ where
  dup_induce := by
    rw [← h₁.dup_induce, ← h₂.dup_induce, induce_induce]
    congr
    simp [hV]
  isLink_of_isLink e x y h :=
    (h.of_isLabelSubgraph h₁).of_isLabelSubgraph_of_mem_mem h₂
    (hE h.edge_mem) (hV h.left_mem) (hV h.right_mem)

lemma ext_of_isLabelSubgraph_eq_Set {H₁ H₂ : Graph α β} (h₁ : H₁ ≤l G) (h₂ : H₂ ≤l G)
    (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (h₁.of_isLabelSubgraph_isLabelSubgraph_subset_subset h₂ hV.subset hE.subset).antisymm <|
    (h₂.of_isLabelSubgraph_isLabelSubgraph_subset_subset h₁ hV.symm.subset hE.symm.subset)

/-- A label subgraph of `G` is a subgraph where each vertex retains all of its labels. -/
@[mk_iff]
structure IsSubgraph (H G : Graph α β) : Prop where
  dup_subset : H.Dup ⊆ G.Dup
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

instance : LE (Graph α β) where
  le := IsSubgraph

@[simp]
def isLabelSubgraph_of_le (h : H ≤ G) : H ≤l G where
  dup_induce := H.vertexSet_eq ▸ induce_eq_of_subset h.dup_subset
  isLink_of_isLink := h.isLink_of_isLink

-- lemma le_of_isLabelSubgraph [G.Nodup] (h : H ≤l G) : H ≤ G where
--   toIsLabelSubgraph := h
--   dup_closed _ _ hxy hx := hxy.eq ▸ hx

lemma dup_of_le (hle : H ≤ G) (hdup : H.Dup x y) : G.Dup x y :=
  rel_le_of_subset hle.dup_subset _ _ hdup

lemma dup_le_of_le (hle : H ≤ G) : H.Dup ≤ G.Dup :=
  le_of_subset hle.dup_subset

lemma dup_of_le_of_mem (hle : H ≤ G) (hx : x ∈ V(H)) (hdup : G.Dup x y) : H.Dup x y :=
  rel_of_subset_mem hle.dup_subset (H.vertexSet_eq ▸ hx) hdup

lemma not_dup_of_le (hle : H ≤ G) (h : ¬ G.Dup x y) : ¬ H.Dup x y :=
  fun h' ↦ h (dup_of_le hle h')

lemma not_dup_of_le_of_mem (hle : H ≤ G) (hx : x ∈ V(H)) (h : ¬ H.Dup x y) : ¬ G.Dup x y :=
  fun h' ↦ h (dup_of_le_of_mem hle hx h')

lemma dup_iff_dup_of_le (hle : H ≤ G) (hx : x ∈ V(H)) : G.Dup x y ↔ H.Dup x y :=
  ⟨dup_of_le_of_mem hle hx, dup_of_le hle⟩

lemma le_iff : H ≤ G ↔ (H.Dup ⊆ G.Dup) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.dup_subset, h.isLink_of_isLink⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma le_of (hsu : H.Dup ⊆ G.Dup) (hlink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y) :
    H ≤ G := by
  rw [le_iff]
  exact ⟨hsu, hlink⟩

lemma mem_iff_mem_of_le_dup (hle : H ≤ G) (hdup : G.Dup x y) : x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  on_goal 2 => rw [comm_of G.Dup] at hdup
  all_goals rw [dup_iff_dup_of_le hle h] at hdup; exact dup_right_mem hdup

lemma Nodup.of_le (hle : H ≤ G) [G.Nodup] : H.Nodup :=
  Nodup.of_isLabelSubgraph <| isLabelSubgraph_of_le hle

lemma IsLink.of_le (h : H.IsLink e x y) (hle : H ≤ G) : G.IsLink e x y :=
  hle.isLink_of_isLink h

lemma IsLink.of_le_of_mem (h : G.IsLink e x y) (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨hux, hvy⟩ | ⟨huy, hvx⟩ := (huv.of_le hle).dup_and_dup_or_dup_and_dup h
  · rw [dup_iff_dup_of_le hle huv.left_mem] at hux
    rw [dup_iff_dup_of_le hle huv.right_mem] at hvy
    rwa [isLink_left_rw hux.symm, isLink_right_rw hvy.symm]
  · rw [dup_iff_dup_of_le hle huv.left_mem] at huy
    rw [dup_iff_dup_of_le hle huv.right_mem] at hvx
    rwa [isLink_right_rw huy.symm, isLink_left_rw hvx.symm, isLink_comm]

lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y := ⟨(·.of_le_of_mem hle he), (·.of_le hle)⟩

lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) :=
  G.vertexSet_eq ▸ H.vertexSet_eq ▸ supp_le_of_subset h.dup_subset

lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  rintro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

/-- The subgraph order is a partial order on graphs. -/
instance : PartialOrder (Graph α β) where
  le_refl _ := ⟨subset_refl _, fun _ _ _ => id⟩
  le_trans G₁ G₂ G₃ h₁ h₂ := ⟨h₁.dup_subset.trans h₂.dup_subset,
    fun _ _ _ hl => h₂.isLink_of_isLink (h₁.isLink_of_isLink hl)⟩
  le_antisymm G H h₁ h₂ := (isLabelSubgraph_of_le h₁).antisymm (isLabelSubgraph_of_le h₂)

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  h.of_isLabelSubgraph (isLabelSubgraph_of_le hle)

lemma Inc.of_le_of_mem (h : G.Inc e x) (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e x :=
  h.of_isLabelSubgraph_of_mem_mem (isLabelSubgraph_of_le hle) he
  <| h.choose_spec.of_le_of_mem hle he |>.left_mem

lemma IsLoopAt.of_le (h : H.IsLoopAt e x) (hle : H ≤ G) : G.IsLoopAt e x :=
  IsLink.of_le h hle

lemma IsNonloopAt.of_le (h : H.IsNonloopAt e x) (hle : H ≤ G) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, not_dup_of_le_of_mem hle he.left_mem hxy, he.of_le hle⟩

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma le_of_le_isLabelSubgraph_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤l G)
    (hV : V(H₁) ⊆ V(H₂)) (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  dup_subset := by
    rw [← h₂.dup_induce]
    exact subset_induce_of_supp_le h₁.dup_subset (H₁.vertexSet_eq ▸ hV)
  isLink_of_isLink e x y h := (h.of_le h₁).of_isLabelSubgraph_of_mem_mem h₂
    (hE h.edge_mem) (hV h.left_mem) (hV h.right_mem)

lemma le_of_isLabelSubgraph_of_isLabelSubgraph {G₁ : Graph α β} (hHG : H ≤ G) (hHG₁ : H ≤l G₁)
    (hG₁ : G₁ ≤l G): H ≤ G₁ where
  dup_subset := by
    rw [← hG₁.dup_induce]
    exact subset_induce_of_supp_le hHG.dup_subset (H.vertexSet_eq ▸ hHG₁.vertexSet)
  isLink_of_isLink := hHG₁.isLink_of_isLink

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
  simp only [isLink_eq_of_le hle he, and_congr_left_iff, not_iff_not, iff_comm]
  exact fun hl => dup_iff_dup_of_le hle (hl.of_le_of_mem hle he).left_mem

lemma isNonloopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) :=
  fun _ ↦ isNonloopAt_eq_of_le hle

/- TODO : Is is reasonable to only keep the `EqOn` versions of the above?
Also, what about functional `≤` versions? -/

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (h : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at h
  obtain ⟨hle, hne⟩ := h
  simp only [ssubset_iff_subset_ne, vertexSet_mono hle, ne_eq, true_and, edgeSet_mono hle]
  contrapose! hne
  exact ext_of_isLabelSubgraph_eq_Set (isLabelSubgraph_of_le hle) isLabelSubgraph_rfl hne.1 hne.2

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

/-! ### Spanning Subgraphs -/

/-- A spanning subgraph of `G` is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop where
  dup_eq : H.Dup = G.Dup
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

/-- `H ≤s G` means that `H` is a spanning subgraph of `G`. -/
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

lemma IsSpanningSubgraph.le (hsle : H ≤s G) : H ≤ G where
  dup_subset := by rw [hsle.dup_eq]
  isLink_of_isLink := hsle.isLink_of_isLink

lemma IsSpanningSubgraph.dup (hsle : H ≤s G) (hdup : G.Dup x y) : H.Dup x y := by
  rwa [hsle.dup_eq]

lemma IsSpanningSubgraph.dup_iff_dup (hsle : H ≤s G) : G.Dup x y ↔ H.Dup x y :=
  ⟨hsle.dup, (dup_of_le hsle.le)⟩

lemma IsSpanningSubgraph.vertexSet (hsle : H ≤s G) : V(H) = V(G) := by
  simp_rw [← vertexSet_def, hsle.dup_eq]

lemma IsSpanningSubgraph.of_isSpanningSubgraph_left (hsle : H ≤s G) (hHK : H ≤l K) (hKG : K ≤l G) :
    H ≤s K where
  dup_eq := by
    simp_rw [← hHK.dup_induce, hsle.vertexSet, induce_eq_self_iff, K.vertexSet_def]
    exact hKG.vertexSet
  isLink_of_isLink := hHK.isLink_of_isLink

lemma IsSpanningSubgraph.of_isSpanningSubgraph_right (hsle : H ≤s G) (hHK : H ≤l K) (hKG : K ≤l G) :
    K ≤s G where
  dup_eq := by
    simp_rw [← hKG.dup_induce, induce_eq_self_iff, G.vertexSet_def, ← hsle.vertexSet]
    exact hHK.vertexSet
  isLink_of_isLink := hKG.isLink_of_isLink

lemma IsSpanningSubgraph.Nodup [H.Nodup] (hsle : H ≤s G) : G.Nodup where
  atomic_dup := hsle.dup_eq ▸ dup_atomic H

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

-- lemma induce_isInducedSubgraph (hX : X ⊆ V(G)) : G[X] ≤i G :=
--   ⟨by simpa, fun e x y h (hx : x ∈ X) (hy : y ∈ X) ↦ by simp_all⟩

-- @[simp]
-- lemma induce_isInducedSubgraph_iff : G[X] ≤i G ↔ X ⊆ V(G) := by
--   simp +contextual [isInducedSubgraph_iff]

-- lemma IsInducedSubgraph.induce_vertexSet_eq (h : H ≤i G) : G[V(H)] = H := by
--   have hle : G[V(H)] ≤l G := by simp [h.isLabelSubgraph.vertexSet]
--   refine G.ext_of_isLabelSubgraph_eq_Set hle h.isLabelSubgraph rfl <| Set.ext fun e ↦ ?_
--   simp only [induce_edgeSet, mem_setOf_eq]
--   refine ⟨fun ⟨x, y, h', hx, hy⟩ ↦ (h.isLink_of_mem_mem h' hx hy).edge_mem, fun h' ↦ ?_⟩
--   obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h'
--   exact ⟨x, y, hxy.of_isLabelSubgraph h.isLabelSubgraph, hxy.left_mem, hxy.right_mem⟩

-- /-- An induced subgraph is precisely a subgraph of the form `G[X]` for some `X ⊆ V(G)`.
-- This version of the lemma can be used with `subst` or `obtain rfl` to replace `H` with `G[X]`. -/
-- lemma IsInducedSubgraph.exists_eq_induce (h : H ≤i G) : ∃ X ⊆ V(G), H = G[X] :=
--   ⟨V(H), h.isLabelSubgraph.vertexSet, h.induce_vertexSet_eq.symm⟩

-- lemma IsInducedSubgraph.adj_of_adj (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H))
--     (hy : y ∈ V(H)) :
--     H.Adj x y := by
--   obtain ⟨e, hxy⟩ := hxy
--   exact (h.isLink_of_mem_mem hxy hx hy).adj

-- lemma IsInducedSubgraph.eq_of_isSpanningSubgraph (hi : H ≤i G) (hs : H ≤s G) : H = G := by
--   obtain ⟨X, hX, rfl⟩ := hi.exists_eq_induce
--   simp [show X = V(G) by simpa using hs.vertexSet_eq]

/-! ### Closed Subgraphs -/

/-- A closed subgraph of `G` is a union of components of `G`.  -/
@[mk_iff]
structure IsClosedSubgraph (H G : Graph α β) : Prop extends H ≤ G where
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

/-- `H ≤c G` means that `H` is a closed subgraph of `G`. i.e. a union of components of `G`. -/
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

lemma IsClosedSubgraph.le (hcl : H ≤c G) : H ≤ G := hcl.toIsSubgraph

lemma IsClosedSubgraph.vertexSet (hcl : H ≤c G) : V(H) ⊆ V(G) := vertexSet_mono hcl.le

lemma IsClosedSubgraph.edgeSet (hcl : H ≤c G) : E(H) ⊆ E(G) := edgeSet_mono hcl.le

lemma IsClosedSubgraph.isLabelSubgraph (hcl : H ≤c G) : H ≤l G := isLabelSubgraph_of_le hcl.le

lemma IsClosedSubgraph.isInducedSubgraph (hcl : H ≤c G) : H ≤i G where
  isLabelSubgraph := isLabelSubgraph_of_le hcl.le
  isLink_of_mem_mem _ _ _ he hx _ := he.of_le_of_mem hcl.le (hcl.closed he.inc_left hx)

lemma IsClosedSubgraph.Dup (hcl : H ≤c G) (hdup : H.Dup x y) : G.Dup x y := dup_of_le hcl.le hdup

lemma IsClosedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁ : G₁ ≤c G₂) (h₂ : G₂ ≤c G₃) : G₁ ≤c G₃ where
  toIsSubgraph := le_trans h₁.le h₂.le
  closed _ _ hi hy := h₁.closed (hi.of_le_of_mem h₂.le <| h₂.closed hi <| h₁.vertexSet hy) hy

@[simp]
lemma isClosedSubgraph_self : G ≤c G where
  toIsSubgraph := le_refl G
  closed _ _ he _ := he.edge_mem

lemma Inc.of_isClosedSubgraph_of_mem (hi : G.Inc e x) (hcle : H ≤c G) (hx : x ∈ V(H)) : H.Inc e x :=
  hi.of_le_of_mem hcle.le (hcle.closed hi hx)
alias IsClosedSubgraph.inc_of_mem := Inc.of_isClosedSubgraph_of_mem

lemma IsLink.of_isClosedSubgraph_of_mem_vertexSet
    (hl : G.IsLink e x y) (hcle : H ≤c G) (hx : x ∈ V(H)) : H.IsLink e x y :=
  hl.of_le_of_mem hcle.le (hcle.closed hl.inc_left hx)
alias IsClosedSubgraph.isLink_of_mem := IsLink.of_isClosedSubgraph_of_mem_vertexSet

lemma Adj.right_mem_of_isClosedSubgraph_of_left_mem (hxy : G.Adj x y) (hcle : H ≤c G)
    (hx : x ∈ V(H)) : y ∈ V(H) := by
  obtain ⟨_, hl⟩ := hxy
  exact hcle.isLink_of_mem hl hx |>.right_mem
alias IsClosedSubgraph.right_mem_of_adj_of_left_mem := Adj.right_mem_of_isClosedSubgraph_of_left_mem

lemma Adj.left_mem_of_isClosedSubgraph_of_right_mem (hxy : G.Adj x y) (hcle : H ≤c G)
    (hy : y ∈ V(H)) : x ∈ V(H) :=
  hcle.right_mem_of_adj_of_left_mem hxy.symm hy
alias IsClosedSubgraph.left_mem_of_adj_of_right_mem := Adj.left_mem_of_isClosedSubgraph_of_right_mem

lemma IsClosedSubgraph.isLink_iff_isLink_of_mem (h : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun he ↦ he.of_le h.le, fun he ↦ he.of_isClosedSubgraph_of_mem_vertexSet h hx⟩

lemma IsLink.mem_iff_mem_of_isClosedSubgraph (hl   : G.IsLink e x y) (hcle : H ≤c G) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
  on_goal 2 => rw [isLink_comm] at hl
  all_goals rw [← hcle.isLink_iff_isLink_of_mem hin] at hl; exact hl.right_mem
alias IsClosedSubgraph.mem_iff_mem_of_isLink := IsLink.mem_iff_mem_of_isClosedSubgraph

lemma IsLink.mem_tfae_of_isClosedSubgraph (hl : G.IsLink e x y) (hcle : H ≤c G) :
    List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
  tfae_have 1 → 2 := (hcle.mem_iff_mem_of_isLink hl).mp
  tfae_have 2 → 3 := (hl.symm.of_isClosedSubgraph_of_mem_vertexSet hcle · |>.edge_mem)
  tfae_have 3 → 1 := (hl.of_le_of_mem hcle.le · |>.left_mem)
  tfae_finish
alias  IsClosedSubgraph.mem_tfae_of_isLink := IsLink.mem_tfae_of_isClosedSubgraph

lemma Adj.of_isClosedSubgraph_of_mem (hxy : G.Adj x y) (hcle : H ≤c G) (hx : x ∈ V(H)) :
    H.Adj x y := by
  obtain ⟨e, hexy⟩ := hxy
  exact (hexy.of_isClosedSubgraph_of_mem_vertexSet hcle hx).adj
alias IsClosedSubgraph.adj_of_mem := Adj.of_isClosedSubgraph_of_mem

lemma Adj.mem_iff_mem_of_isClosedSubgraph (hxy : G.Adj x y) (hcle : H ≤c G) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  obtain ⟨e, hexy⟩ := hxy
  exact hexy.mem_iff_mem_of_isClosedSubgraph hcle
alias IsClosedSubgraph.mem_iff_mem_of_adj := Adj.mem_iff_mem_of_isClosedSubgraph

lemma IsClosedSubgraph.of_le_of_isLabelSubgraph {G₁ : Graph α β} (hHG : H ≤c G) (hHG₁ : H ≤ G₁)
    (hG₁ : G₁ ≤l G) : H ≤c G₁ where
  toIsSubgraph := hHG₁
  closed _ _ he hx := ((he.of_isLabelSubgraph hG₁).of_isClosedSubgraph_of_mem hHG hx).edge_mem

-- lemma IsClosedSubgraph.diff {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) :
--     H₁ - V(H₂) ≤c G where
--   dup_subset := by
--     simp only [vertexDelete_dup]

--     refine subset_trans ?_ h₁.dup_subset


  -- toIsLabelSubgraph := vertexDelete_isLabelSubgraph.trans h₁.toIsLabelSubgraph
  -- closed e x he hx := by
  --   simp only [vertexDelete_edgeSet, mem_setOf_eq]
  --   simp only [vertexDelete_vertexSet, mem_diff] at hx
  --   obtain ⟨y, hexy⟩ := he
  --   refine ⟨x, y, hexy.of_isClosedSubgraph_of_mem_vertexSet h₁ hx.1, hx.2, fun hy ↦ hx.2 ?_⟩
  --   refine (hexy.symm.of_isClosedSubgraph_of_mem_vertexSet h₂ hy).right_mem
  -- dup_closed x y hxy := by
  --   simp only [vertexDelete_vertexSet, mem_diff, and_imp]
  --   rintro hx₁ hx₂
  --   exact ⟨h₁.dup_closed hxy hx₁, fun hy₂ => hx₂ <| h₂.dup_closed hxy.symm hy₂⟩

-- lemma IsClosedSubgraph.compl (h : H ≤c G) : G - V(H) ≤c G :=
--   G.isClosedSubgraph_self.diff h

-- lemma not_isClosedSubgraph_iff_of_IsInducedSubgraph (hile : H ≤i G) :
--     ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧ x ∈ V(H) ∧ y ∉ V(H) := by
--   rw [not_iff_comm]
--   push_neg
--   exact ⟨fun hncl => ⟨⟨hile.isLabelSubgraph, sorry⟩, fun e x ⟨y, hl⟩ hx =>
--     hile.isLink_of_mem_mem hl hx (hncl x y ⟨e, hl⟩ hx) |>.edge_mem⟩, fun hcl _ _ hxy =>
--     (hcl.mem_iff_mem_of_adj hxy).mp⟩

-- ⟨⟨hclF.toIsLabelSubgraph.trans edgeDelete_le.toIsLabelSubgraph,
--     fun x y hxy => hclF.dup_closed (hxy.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph)⟩,
--     fun e x he hxH => ?_⟩

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
