import Matroid.Graph.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.TFAE
import Mathlib.Data.Set.Card

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

initialize_simps_projections Graph (IsLink → isLink)

open Set

open scoped Sym2

namespace Graph

/-- `Copy` creates an identical graph with different definitions for its vertex set and edge set.
  This is mainly used to create graphs with improved definitional properties. -/
@[simps]
def copy (G : Graph α β) {dup : α → α → Prop} {E : Set β} {IsLink : β → α → α → Prop}
    (hdup : G.dup = dup) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    Graph α β where
  dup := dup
  dup_symm := hdup ▸ G.dup_symm
  dup_trans := hdup ▸ G.dup_trans
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
  left_mem_of_isLink := by
    simp_rw [← h_isLink, ← hdup, ← G.dup_refl_iff]
    exact G.left_mem_of_isLink
  isLink_of_dup := by
    simp_rw [← h_isLink, ← hdup]
    exact G.isLink_of_dup

lemma copy_eq_self (G : Graph α β) {dup : α → α → Prop} {E : Set β} {IsLink : β → α → α → Prop}
    (hdup : G.dup = dup) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hdup hE h_isLink = G := by
  ext <;> simp_all

/-- `IsSubgraph H G` means that `V(H) ⊆ V(G)`, and every link in `H` is a link in `G`. -/
structure IsSubgraph (H G : Graph α β) : Prop where
  dup_eq : ∀ ⦃x y⦄, x ∈ V(H) → y ∈ V(H) → (H.dup x y ↔ G.dup x y)
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

/-- The subgraph order is a partial order on graphs. -/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨by simp, by simp⟩
  le_trans _ _ _ h₁ h₂ :=
    ⟨fun x y hxH hyH => (by rw [h₁.dup_eq hxH hyH, h₂.dup_eq
      (by rwa [dup_refl_iff, ← h₁.dup_eq hxH hxH, ← dup_refl_iff])
      (by rwa [dup_refl_iff, ← h₁.dup_eq hyH hyH, ← dup_refl_iff])]), fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := by
    refine Graph.ext ?_
      fun e x y ↦ ⟨fun a ↦ h₁.isLink_of_isLink a, fun a ↦ h₂.isLink_of_isLink a⟩
    ext x y
    by_cases hx : x ∈ V(G)
    · by_cases hy : y ∈ V(G)
      · exact h₁.dup_eq hx hy
      simp only [not_dup_of_not_mem_right hy, false_iff]
      contrapose! hy
      rw [h₂.dup_eq hy.left_mem hy.right_mem] at hy
      exact hy.symm.left_mem
    simp only [not_dup_of_not_mem_left hx, false_iff]
    contrapose! hx
    rw [h₂.dup_eq hx.left_mem hx.right_mem] at hx
    exact hx.left_mem

lemma dup.of_le (h : H.dup x y) (hle : H ≤ G) : G.dup x y := by
  rwa [← hle.dup_eq h.left_mem h.right_mem]

lemma dup.of_le_of_mem (h : G.dup x y) (hle : H ≤ G) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    H.dup x y := by rwa [hle.dup_eq hx hy]

lemma dup.of_le_of_adj (h : G.dup x y) (hle : H ≤ G) (hxy : H.Adj x y) : H.dup x y :=
  h.of_le_of_mem hle hxy.left_mem hxy.right_mem

lemma not_dup_of_le (h : ¬ G.dup x y) (hle : H ≤ G) : ¬ H.dup x y :=
  fun h' ↦ h (h'.of_le hle)

lemma not_dup_of_le_of_mem_mem (h : ¬ H.dup x y) (hle : H ≤ G) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    ¬ G.dup x y := fun h' ↦ h (h'.of_le_of_mem hle hx hy)

lemma not_dup_of_le_of_adj (h : ¬ H.dup x y) (hle : H ≤ G) (hxy : H.Adj x y) : ¬ G.dup x y :=
  not_dup_of_le_of_mem_mem h hle hxy.left_mem hxy.right_mem

lemma IsLink.of_le (h : H.IsLink e x y) (hle : H ≤ G) : G.IsLink e x y :=
  hle.2 h

lemma IsLink.of_le_of_mem (h : G.IsLink e x y) (hle : H ≤ G) (he : e ∈ E(H)) (hx : x ∈ V(H))
    (hy : y ∈ V(H)) : H.IsLink e x y := by
  obtain ⟨u, v, hl⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩ := h.dup_and_dup_or_dup_and_dup <| hle.isLink_of_isLink hl
  · have hxu' := hxu.of_le_of_mem hle hx hl.left_mem
    have hyv' := hyv.of_le_of_mem hle hy hl.right_mem
    rwa [hxu'.isLink_left, hyv'.isLink_right]
  · have hxv' := hxv.of_le_of_mem hle hx hl.right_mem
    have hyu' := hyu.of_le_of_mem hle hy hl.left_mem
    rwa [hxv'.isLink_left, hyu'.isLink_right, isLink_comm]

lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) := by
  rintro x hxH
  rwa [G.dup_refl_iff, ← h.dup_eq hxH hxH, ← H.dup_refl_iff]

lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

lemma exists_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    ∃ u v, G.IsLink e u v ∧ H.IsLink e u v := by
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, hle.isLink_of_isLink h', h'⟩

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  (h.choose_spec.of_le hle).inc_left

lemma Inc.of_le_of_mem (h : G.Inc e x) (hle : H ≤ G) (he : e ∈ E(H)) (hx : x ∈ V(H)) :
    H.Inc e x := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain hxu | hxv := h.dup_or_dup_of_isLink (huv.of_le hle)
  · rw [← hle.dup_eq hx huv.left_mem] at hxu
    exact ⟨v, huv.dup_left hxu.symm⟩
  rw [← hle.dup_eq hx huv.right_mem] at hxv
  exact ⟨u, huv.symm.dup_left hxv.symm⟩

lemma exists_inc_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    ∃ u, G.Inc e u ∧ H.Inc e u := by
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, ⟨y, hle.isLink_of_isLink h'⟩, ⟨y, h'⟩⟩

lemma IsLoopAt.of_le (h : H.IsLoopAt e x) (hle : H ≤ G) : G.IsLoopAt e x :=
  IsLink.of_le h hle

lemma IsNonloopAt.of_le (h : H.IsNonloopAt e x) (hle : H ≤ G) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, not_dup_of_le_of_mem_mem hxy hle he.left_mem he.right_mem, he.of_le hle⟩

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma le_iff : H ≤ G ↔ (∀ ⦃x y⦄, x ∈ V(H) → y ∈ V(H) → (H.dup x y ↔ G.dup x y)) ∧
    ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.dup_eq, h.isLink_of_isLink⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  dup_eq x y hxH hyH := by rw [h₁.dup_eq hxH hyH, h₂.dup_eq (hV hxH) (hV hyH)]
  isLink_of_isLink e x y h :=
    (h.of_le h₁).of_le_of_mem h₂ (hE h.edge_mem) (hV h.left_mem) (hV h.right_mem)

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

-- lemma isLink_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e = G.IsLink e := by
--   ext x y
--   exact ⟨fun h ↦ h.of_le hle, fun h ↦ h.of_le_of_mem hle he⟩

-- lemma isLink_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLink G.IsLink E(H) :=
--   fun _ ↦ isLink_eq_of_le hle

-- lemma inc_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e = G.Inc e := by
--   unfold Graph.Inc
--   rw [isLink_eq_of_le hle he]

-- lemma inc_eqOn_of_le (hle : H ≤ G) : EqOn H.Inc G.Inc E(H) :=
--   fun _ ↦ inc_eq_of_le hle

-- lemma isLoopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLoopAt e = G.IsLoopAt e := by
--   unfold Graph.IsLoopAt
--   rw [isLink_eq_of_le hle he]

-- lemma isLoopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) :=
--   fun _ ↦ isLoopAt_eq_of_le hle

-- lemma isNonloopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsNonloopAt e = G.IsNonloopAt e := by
--   unfold Graph.IsNonloopAt
--   ext x
--   refine exists_congr fun y ↦ ?_
--   simp only [isLink_eq_of_le hle he, and_congr_left_iff, not_iff_not]
--   exact fun hl => hle.dup_eq (hl.of_le_of_mem hle he).left_mem

-- lemma isNonloopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) :=
--   fun _ ↦ isNonloopAt_eq_of_le hle

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (h : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at h
  simp only [ssubset_iff_subset_ne, vertexSet_mono h.1, ne_eq, true_and, edgeSet_mono h.1]
  by_contra! heq
  exact h.2 <| ext_of_le_le h.1 le_rfl heq.1 heq.2

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

/- TODO : Is is reasonable to only keep the `EqOn` versions of the above?
Also, what about functional `≤` versions? -/

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps isLink]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  dup := G.dup
  dup_refl_iff := G.dup_refl_iff
  dup_symm := G.dup_symm
  dup_trans := G.dup_trans
  edgeSet := E₀ ∩ E(G)
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1, h.2.symm⟩
  isLink_of_dup _ _ _ _ hxy := by simp [hxy.isLink_left]
  dup_or_dup_of_isLink_of_isLink _ _ _ _ _ h h' :=
    G.dup_or_dup_of_isLink_of_isLink h.2 h'.2
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
lemma edgeRestrict_dup (G : Graph α β) (E₀ : Set β) (x y : α) : (G ↾ E₀).dup x y ↔ G.dup x y := by
  rfl

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  dup_eq x y hx := by simp [edgeRestrict]
  isLink_of_isLink := by simp

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
  dup_eq x y hx := by simp [edgeRestrict]
  isLink_of_isLink _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F := by
  refine G.le_of_le_le_subset_subset (edgeRestrict_le.trans h) (by simp)
    (by simpa using vertexSet_mono h) ?_
  simp [inter_subset_right.trans (edgeSet_mono h)]

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F :=
  ext_of_le_le (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F := by
  rw [inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  ext_of_le_le (G := G) (by simp) (by simp) rfl (by simp)

lemma edgeRestrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_le_le ?_ (by simp) (by simp) ?_
  · exact edgeRestrict_le.trans (by simp)
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm F₂]

@[simp]
lemma le_edgeRestrict_iff : H ≤ (G ↾ F) ↔ H ≤ G ∧ E(H) ⊆ F :=
  ⟨fun h ↦ ⟨h.trans (by simp), (edgeSet_mono h).trans (by simp)⟩,
    fun h ↦ le_of_le_le_subset_subset h.1 (by simp) (by simpa using vertexSet_mono h.1)
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
  dup x y := x ∈ X ∧ y ∈ X ∧ (G.dup x y ∨ x = y)
  dup_refl_iff := by simp
  dup_symm x y := by
    rintro ⟨hx, hy, h | rfl⟩
    on_goal 1 => simp only [G.dup_symm _ _ h, true_or, and_true]
    all_goals simp [hx, hy]
  dup_trans x y z := by
    rintro ⟨hx, hy, h | rfl⟩ ⟨hy', hz, h' | rfl⟩ <;> simp [hx, hy, hy', hz] <;> left <;> try tauto
    exact h.trans h'
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm _ _ x := by simp +contextual [G.isLink_comm (x := x)]
  dup_or_dup_of_isLink_of_isLink e a b c d := by
    rintro ⟨hl, ha, hb⟩ ⟨hl', hc, hd⟩
    simp only [ha, hc, true_and, hd]
    refine (G.dup_or_dup_of_isLink_of_isLink hl hl').imp ?_ ?_ <;> tauto
  left_mem_of_isLink := by simp +contextual
  isLink_of_dup e x y z := by
    rintro ⟨hx, hy, h | rfl⟩ <;> simp only [hx, true_and, hy, imp_self]
    rw [h.isLink_left]
    exact id

/-- `G[X]` is the subgraph of `G` induced by the set `X` of vertices. -/
notation:max G:1000 "[" S "]" => Graph.induce G S

lemma induce_le (hX : X ⊆ V(G)) : G[X] ≤ G := by
  refine ⟨fun x y hxX hyX => ⟨fun ⟨hxX, hyX, hor⟩ => ?_, fun h => ⟨hxX, hyX, Or.inl h⟩⟩,
    fun _ _ _ h ↦ h.1⟩
  apply hor.elim id
  rintro rfl
  rw [← G.dup_refl_iff]
  exact hX hxX

@[simp]
lemma induce_le_iff : G[X] ≤ G ↔ X ⊆ V(G) :=
  ⟨vertexSet_mono, induce_le⟩

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

-- lemma IsLink.mem_induce_iff {X : Set α} (hG : G.IsLink e x y) : e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
--   simp only [induce_edgeSet, mem_setOf_eq]
--   refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
--   obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.dup_and_dup_or_dup_and_dup he <;> simp [hx', hy']

-- lemma induce_induce (G : Graph α β) (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
--   refine Graph.ext ?_ fun e x y ↦ ?_
--   · ext x y
--     simp only [induce_dup, edgeRestrict_dup, and_congr_right_iff]
--     refine fun hxY hyY => ⟨?_, ?_⟩
--     · rintro (⟨hxX, hyX, hor⟩ | rfl) <;> tauto
--     rintro (hdup | rfl)
--     ·
--       sorry
--     tauto

  -- simp only [induce_isLink_iff, edgeRestrict_isLink]
  -- obtain he | he := em' (G.IsLink e x y)
  -- · simp [he]
  -- rw [he.mem_induce_iff]
  -- tauto

lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤ G[Y] where
  dup_eq x y hx hy := by
    simp only [induce_vertexSet] at hx hy
    simp [hx, hy, hXY hx, hXY hy]
  isLink_of_isLink _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

@[simp]
lemma induce_mono_right_iff (G : Graph α β) : G[X] ≤ G[Y] ↔ X ⊆ Y :=
  ⟨vertexSet_mono, induce_mono_right G⟩

-- lemma induce_mono_left (h : H ≤ G) (X : Set α) : H[X] ≤ G[X] where
--   dup_eq x y hx hy := by
--     simp only [induce_vertexSet] at hx hy
--     simp [hx, hy, vertexSet_mono hXY hx, vertexSet_mono hXY hy]
--   isLink_of_isLink e x y := by
--     simp only [induce_isLink_iff, and_imp]
--     exact fun hl hx hy => ⟨hl.of_le h, hx, hy⟩

-- lemma induce_mono (h : H ≤ G) (hXY : X ⊆ Y) : H[X] ≤ G[Y] :=
--   (induce_mono_left h X).trans (G.induce_mono_right hXY)

@[simp]
lemma induce_vertexSet_self (G : Graph α β) : G[V(G)] = G := by
  refine G.ext_of_le_le (by simp) (by simp) rfl <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

lemma le_induce_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ X) : H ≤ G[X] where
  dup_eq x y hx hy := by
    simp only [h.dup_eq hx hy, induce_dup, hV hx, hV hy, true_and, iff_self_or]
    rintro rfl
    rw [← G.dup_refl_iff]
    exact vertexSet_mono h hx
  isLink_of_isLink _ _ _ h' := ⟨h'.of_le h, hV h'.left_mem, hV h'.right_mem⟩

lemma le_induce_self (h : H ≤ G) : H ≤ G[V(H)] :=
  le_induce_of_le_of_subset h rfl.subset

lemma le_induce_iff (hX : X ⊆ V(G)) : H ≤ G[X] ↔ H ≤ G ∧ V(H) ⊆ X :=
  ⟨fun h ↦ ⟨h.trans (by simpa), vertexSet_mono h⟩, fun h ↦ le_induce_of_le_of_subset h.1 h.2⟩

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
    (G - X).dup x y ↔ G.dup x y ∧ x ∉ X ∧ y ∉ X := by
  simp +contextual only [vertexDelete_def, induce_dup, mem_diff, iff_def, not_false_eq_true,
    and_self, and_true, and_imp, true_or]
  refine ⟨fun hx hxX hy hyX => ?_, fun hdup hxX hyX => ⟨hdup.left_mem, hdup.right_mem⟩⟩
  rintro (hdup | rfl)
  · exact hdup
  rwa [← G.dup_refl_iff]

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
lemma vertexDelete_le : G - X ≤ G :=
  G.induce_le diff_subset

-- lemma IsLink.mem_vertexDelete_iff {X : Set α} (hG : G.IsLink e x y) :
--     e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
--   rw [vertexDelete_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.left_mem,
--     and_iff_right hG.right_mem]

lemma vertexDelete_mono_left (h : H ≤ G) : H - X ≤ G - X where
  dup_eq x y hx hy := by simp [h.dup_eq hx.1 hy.1]
  isLink_of_isLink _ _ _ h' := by simp_all [h.isLink_of_isLink h'.1]

lemma vertexDelete_anti_right (hXY : X ⊆ Y) : G - Y ≤ G - X :=
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

@[simp]
lemma le_vertexDelete_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
  simp only [vertexDelete_def, le_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ vertexSet_mono h

/-! ### Spanning Subgraphs -/

/-- A spanning subgraph of `G` is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  vertexSet_eq : V(H) = V(G)

/-- `H ≤s G` means that `H` is a spanning subgraph of `G`. -/
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

@[simp]
lemma edgeRestrict_isSpanningSubgraph : G ↾ F ≤s G :=
  ⟨by simp, rfl⟩

@[simp]
lemma edgeDelete_isSpanningSubgraph : G ＼ F ≤s G :=
  ⟨by simp, by simp [vertexSet_eq_setOf_dup]⟩

lemma dup.of_isSpanningSubgraph (hdup : G.dup x y) (h : H ≤s G) : H.dup x y :=
  hdup.of_le_of_mem h.le (h.vertexSet_eq ▸ hdup.left_mem) (h.vertexSet_eq ▸ hdup.right_mem)

lemma IsSpanningSubgraph.of_isSpanningSubgraph_left (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) :
    H ≤s K where
  le := hHK
  vertexSet_eq := (vertexSet_mono hHK).antisymm ((vertexSet_mono hKG).trans_eq h.vertexSet_eq.symm)

lemma IsSpanningSubgraph.of_isSpanningSubgraph_right (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) :
    K ≤s G where
  le := hKG
  vertexSet_eq := (vertexSet_mono hKG).antisymm <|
    h.vertexSet_eq.symm.le.trans <| vertexSet_mono hHK

/-! ### Induced Subgraphs -/

/-- An induced subgraph of `G` is a subgraph `H` of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
structure IsInducedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

/-- `H ≤i G` means that `H` is an induced subgraph of `G`. -/
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

lemma IsInducedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁₂ : G₁ ≤i G₂) (h₂₃ : G₂ ≤i G₃) :
    G₁ ≤i G₃ :=
  ⟨h₁₂.le.trans h₂₃.le, fun _ _ _ h hx hy ↦ h₁₂.isLink_of_mem_mem
    (h₂₃.isLink_of_mem_mem h (vertexSet_mono h₁₂.le hx) (vertexSet_mono h₁₂.le hy))
    hx hy⟩

lemma isInducedSubgraph_iff :
    H ≤i G ↔ H ≤ G ∧ ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma induce_isInducedSubgraph (hX : X ⊆ V(G)) : G[X] ≤i G :=
  ⟨by simpa, fun e x y h (hx : x ∈ X) (hy : y ∈ X) ↦ by simp_all⟩

@[simp]
lemma induce_isInducedSubgraph_iff : G[X] ≤i G ↔ X ⊆ V(G) := by
  simp +contextual [isInducedSubgraph_iff]

lemma IsInducedSubgraph.induce_vertexSet_eq (h : H ≤i G) : G[V(H)] = H := by
  have hle : G[V(H)] ≤ G := by simp [vertexSet_mono h.le]
  refine G.ext_of_le_le hle h.le rfl <| Set.ext fun e ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x, y, h', hx, hy⟩ ↦ (h.isLink_of_mem_mem h' hx hy).edge_mem, fun h' ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h'
  exact ⟨x, y, hxy.of_le h.le, hxy.left_mem, hxy.right_mem⟩

/-- An induced subgraph is precisely a subgraph of the form `G[X]` for some `X ⊆ V(G)`.
This version of the lemma can be used with `subst` or `obtain rfl` to replace `H` with `G[X]`. -/
lemma IsInducedSubgraph.exists_eq_induce (h : H ≤i G) : ∃ X ⊆ V(G), H = G[X] :=
  ⟨V(H), vertexSet_mono h.le, h.induce_vertexSet_eq.symm⟩

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
structure IsClosedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)
  dup_closed : ∀ ⦃x y⦄, G.dup x y → x ∈ V(H) → y ∈ V(H)

/-- `H ≤c G` means that `H` is a closed subgraph of `G`. i.e. a union of components of `G`. -/
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

lemma IsClosedSubgraph.vertexSet_mono (h : H ≤c G) : V(H) ⊆ V(G) := Graph.vertexSet_mono h.le

lemma IsClosedSubgraph.edgeSet_mono (h : H ≤c G) : E(H) ⊆ E(G) := Graph.edgeSet_mono h.le

lemma IsClosedSubgraph.isInducedSubgraph (h : H ≤c G) : H ≤i G where
  le := h.le
  isLink_of_mem_mem _ _ _ he hx hy := he.of_le_of_mem h.le (h.closed he.inc_left hx) hx hy

lemma dup.of_isClosedSubgraph (h : H ≤c G) (hdup : H.dup x y) : G.dup x y := hdup.of_le h.le

lemma dup.of_isClosedSubgraph_of_left_mem (h : H ≤c G) (hdup : G.dup x y) (hx : x ∈ V(H)) :
    H.dup x y := hdup.of_le_of_mem h.le hx (h.dup_closed hdup hx)

lemma dup.of_isClosedSubgraph_of_right_mem (h : H ≤c G) (hdup : G.dup x y) (hy : y ∈ V(H)) :
    H.dup x y := hdup.of_le_of_mem h.le (h.dup_closed hdup.symm hy) hy

lemma IsClosedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁ : G₁ ≤c G₂) (h₂ : G₂ ≤c G₃) : G₁ ≤c G₃ where
  le := h₁.le.trans h₂.le
  closed _ _ hi hy := h₁.closed
    (hi.of_le_of_mem h₂.le (h₂.closed hi (h₁.vertexSet_mono hy)) <| vertexSet_mono h₁ hy) hy
  dup_closed _ _ hxy hx :=
    h₁.dup_closed (hxy.of_isClosedSubgraph_of_left_mem h₂ <| h₁.vertexSet_mono hx) hx

@[simp]
lemma isClosedSubgraph_self : G ≤c G where
  le := le_rfl
  closed _ _ he _ := he.edge_mem
  dup_closed _ _ hxy _ := hxy.right_mem

lemma Inc.of_isClosedSubgraph_of_mem (h : G.Inc e x) (hle : H ≤c G) (hx : x ∈ V(H)) : H.Inc e x :=
  h.of_le_of_mem hle.le (hle.closed h hx) hx

lemma Adj.right_mem_of_isClosedSubgraph_of_left_mem (hle : H ≤c G) (hxy : G.Adj x y)
    (hx : x ∈ V(H)) : y ∈ V(H) := by
  obtain ⟨e, h⟩ := hxy
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet <| hle.closed h.inc_left hx
  obtain ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩ := h.dup_and_dup_or_dup_and_dup <| huv.of_le hle.le
  · exact hle.dup_closed hyv.symm huv.right_mem
  exact hle.dup_closed hyu.symm huv.left_mem

lemma Adj.left_mem_of_isClosedSubgraph_of_right_mem (hle : H ≤c G) (hxy : G.Adj x y)
    (hy : y ∈ V(H)) : x ∈ V(H) :=
  hxy.symm.right_mem_of_isClosedSubgraph_of_left_mem hle hy

lemma IsLink.of_isClosedSubgraph_of_mem (h : G.IsLink e x y) (hle : H ≤c G) (hx : x ∈ V(H))
    : H.IsLink e x y :=
  h.of_le_of_mem hle.le (h.inc_left.of_isClosedSubgraph_of_mem hle hx).edge_mem hx <|
    Adj.right_mem_of_isClosedSubgraph_of_left_mem hle ⟨e, h⟩ hx

lemma IsClosedSubgraph.isLink_iff_of_mem (h : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun he ↦ he.of_le h.le, fun he ↦ he.of_isClosedSubgraph_of_mem h hx⟩

-- lemma IsClosedSubgraph.mem_iff_mem_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
--     x ∈ V(H) ↔ y ∈ V(H) := by
--   refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
--   on_goal 2 => rw [isLink_comm] at he
--   all_goals rw [← h.isLink_iff_of_mem hin] at he; exact he.right_mem

-- lemma IsClosedSubgraph.mem_tfae_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
--     List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
--   tfae_have 1 → 2 := (h.mem_iff_mem_of_isLink he).mp
--   tfae_have 2 → 3 := (he.symm.of_isClosedSubgraph_of_mem h · |>.edge_mem)
--   tfae_have 3 → 1 := (he.of_le_of_mem h.le · |>.left_mem)
--   tfae_finish

lemma IsClosedSubgraph.adj_of_adj_of_mem (h : H ≤c G) (hx : x ∈ V(H)) (hxy : G.Adj x y) :
    H.Adj x y := by
  obtain ⟨e, hexy⟩ := hxy
  exact (hexy.of_isClosedSubgraph_of_mem h hx).adj

-- lemma IsClosedSubgraph.mem_iff_mem_of_adj (h : H ≤c G) (hxy : G.Adj x y) :
--     x ∈ V(H) ↔ y ∈ V(H) := by
--   obtain ⟨e, hexy⟩ := hxy
--   exact mem_iff_mem_of_isLink h hexy

lemma IsClosedSubgraph.of_le_of_le {G₁ : Graph α β} (hHG : H ≤c G) (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G):
    H ≤c G₁ where
  le := hHG₁
  closed _ _ he hx := ((he.of_le hG₁).of_isClosedSubgraph_of_mem hHG hx).edge_mem
  dup_closed _ _ hxy hx := hHG.dup_closed (hxy.of_le hG₁) hx

lemma IsClosedSubgraph.diff {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) :
    H₁ - V(H₂) ≤c G where
  le := vertexDelete_le.trans h₁.le
  closed e x he hx := by
    simp only [vertexDelete_edgeSet, mem_setOf_eq]
    simp only [vertexDelete_vertexSet, mem_diff] at hx
    obtain ⟨y, hexy⟩ := he
    refine ⟨x, y, hexy.of_isClosedSubgraph_of_mem h₁ hx.1, hx.2, fun hy ↦ hx.2 ?_⟩
    refine (hexy.symm.of_isClosedSubgraph_of_mem h₂ hy).right_mem
  dup_closed x y hxy := by
    simp only [vertexDelete_vertexSet, mem_diff, and_imp]
    rintro hx₁ hx₂
    exact ⟨h₁.dup_closed hxy hx₁, fun hy₂ => hx₂ <| h₂.dup_closed hxy.symm hy₂⟩

lemma IsClosedSubgraph.compl (h : H ≤c G) : G - V(H) ≤c G :=
  G.isClosedSubgraph_self.diff h

-- lemma not_isClosedSubgraph_iff_of_IsInducedSubgraph (hle : H ≤i G) : ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧
--     x ∈ V(H) ∧ y ∉ V(H) := by
--   rw [not_iff_comm]
--   push_neg
--   refine ⟨fun hncl ↦ ⟨hle.le, fun e x ⟨y, hexy⟩ hxH => hle.isLink_of_mem_mem hexy hxH
--     (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem, fun x y hdup hx =>?_⟩, fun hcl x y hexy hx ↦ ?_⟩
--   ·
    -- ⟨hle.le, fun e x ⟨y, hexy⟩ hxH => hle.isLink_of_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem⟩
  -- (hcl.mem_iff_mem_of_adj hexy).mp hx

lemma IsClosedSubgraph.of_edgeDelete_iff (hclF : H ≤c G ＼ F) : H ≤c G ↔ E(G) ∩ F ⊆ E(G - V(H)) := by
  rw [vertexDelete_edgeSet]
  refine ⟨fun hcl f hf ↦ ?_, fun hF ↦ ⟨hclF.le.trans edgeDelete_le, fun e x he hxH => ?_,
    fun x y hxy hx => hclF.dup_closed (hxy.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph) hx⟩⟩
  · by_contra! hfH
    simp only [mem_setOf_eq, not_exists, not_and, not_not] at hfH
    refine (hclF.edgeSet_mono ?_).2 hf.2
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hf.1
    obtain hx | hy := or_iff_not_imp_left.mpr <| hfH x y hxy
    · exact hcl.closed ⟨_, hxy⟩ hx
    · exact hcl.closed ⟨_, hxy.symm⟩ hy
  · have heF : e ∉ F := fun heF => by
      obtain ⟨u, v, heuv, hunH, hvnH⟩ := hF ⟨he.edge_mem, heF⟩
      obtain hxu | hxv := he.dup_or_dup_of_isLink heuv
      · exact hunH (hxu.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph
          |>.of_isClosedSubgraph_of_left_mem hclF hxH |>.right_mem)
      · exact hvnH (hxv.of_isSpanningSubgraph edgeDelete_isSpanningSubgraph
          |>.of_isClosedSubgraph_of_left_mem hclF hxH |>.right_mem)
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
