import Matroid.ForMathlib.Partition.Rep
import Matroid.Graph.Map
import Matroid.Graph.Connected.Basic


variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)}

open Set Function

namespace Graph

/-! ## Contraction of one edge -/

private lemma contract_vertexSet_lemma [DecidableEq α] (he : G.Inc e x) :
    let map := fun v ↦ if v = he.other then x else v
    V(map ''ᴳ G ＼ {e}) = insert x (V(G) \ {he.other}) := by
  rintro map
  ext a
  simp only [Map_vertexSet, edgeDelete_vertexSet, mem_image, mem_insert_iff, mem_diff,
    mem_singleton_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩
    by_cases hbo : b = he.other <;> simp [hbo, map, hb]
  rintro (rfl | ⟨ha, hne⟩)
  · use a, he.vertex_mem, by simp [map]
  use a, ha, by simp [map, hne]

private lemma contract_isLink_lemma [DecidableEq α] (he : G.Inc e x) :
    let map := fun v ↦ if v = he.other then x else v
    (map ''ᴳ G ＼ {e}).IsLink f u v ↔ ∃ a b, (G.IsLink f a b ∧ f ≠ e) ∧
    (a = he.other ∧ x = u ∨ a ≠ he.other ∧ a = u) ∧
    (b = he.other ∧ x = v ∨ b ≠ he.other ∧ b = v) := by
  rintro map
  simp only [Map_isLink, edgeDelete_isLink, mem_singleton_iff, ne_eq]
  refine exists₂_congr (fun a b ↦ and_congr_right fun _ ↦ ?_)
  rw [eq_comm (a := u), eq_comm (a := v)]
  refine and_congr ?_ ?_ <;> simp [map, ite_eq_iff]

-- A bit of a mess to do (map ''ᴳ G ＼ {e}) without decidability assumptions.
@[simps]
def Inc.contract (G : Graph α β) (he : G.Inc e x) : Graph α β where
  vertexSet := insert x (V(G) \ {he.other})
  edgeSet := E(G) \ {e}
  IsLink f u v := ∃ a b, (G.IsLink f a b ∧ f ≠ e) ∧
    (a = he.other ∧ x = u ∨ a ≠ he.other ∧ a = u) ∧ (b = he.other ∧ x = v ∨ b ≠ he.other ∧ b = v)
  isLink_symm f hf u v h := by
    classical
    exact contract_isLink_lemma he |>.mp (contract_isLink_lemma he |>.mpr h).symm
  eq_or_eq_of_isLink_of_isLink f a b c d h1 h2 := by
    classical
    exact eq_or_eq_of_isLink_of_isLink _ (contract_isLink_lemma he |>.mpr h1)
    <| contract_isLink_lemma he |>.mpr h2
  edge_mem_iff_exists_isLink e' := by
    classical
    simp_rw [← contract_isLink_lemma he]
    exact (_ ''ᴳ G ＼ {e}).edge_mem_iff_exists_isLink e'
  left_mem_of_isLink e' x' y' := by
    classical
    simp_rw [← contract_isLink_lemma he, ← contract_vertexSet_lemma he]
    convert (_ ''ᴳ G ＼ {e}).left_mem_of_isLink (e := e') (x := x') (y := y')

lemma Inc.contract_eq_map_edgeDelete [DecidableEq α] (he : G.Inc e x) :
    he.contract = (fun v ↦ if v = he.other then x else v) ''ᴳ (G ＼ {e}) :=
  Graph.ext (contract_vertexSet_lemma he).symm fun _ _ _ ↦ (contract_isLink_lemma he).symm

@[simp]
lemma IsLoopAt.contract_eq (he : G.IsLoopAt e x) : he.inc.contract = G ＼ {e} := by
  classical
  conv_rhs => rw [← (G ＼ {e}).map_id]
  rw [he.inc.contract_eq_map_edgeDelete]
  refine map_congr_left_of_eqOn fun u hu ↦ ?_
  simp only [he.other_eq, id_eq, ite_eq_right_iff]
  exact (·.symm)

@[simp]
lemma IsNonloopAt.contract_vertexSet (he : G.IsNonloopAt e x) :
    V(he.inc.contract) = V(G) \ {he.inc.other} := by
  simp [he.vertex_mem, he.other_ne.symm]

@[simp]
lemma IsNonloopAt.other_notMem_contract (he : G.IsNonloopAt e x) :
    he.inc.other ∉ V(he.inc.contract) := by
  simp [he.other_ne]

@[simp]
lemma Inc.contract_eq_iff (he : G.Inc e x) : he.contract = G ＼ {e} ↔ G.IsLoopAt e x := by
  refine ⟨fun h ↦ he.isLoopAt_or_isNonloopAt.resolve_right ?_, fun h ↦ h.contract_eq⟩
  rintro hnl
  simpa [h, hnl.inc.other_mem] using hnl.other_notMem_contract

/-! ## Contracting a set of edges -/

variable {α' α'' : Type*}

/-- `Contract G φ C` contracts the edges in set `C` of graph `G`,
    mapping the resulting vertices according to function `φ`.

    This operation creates a new graph where:
    1. Edges in set `C` are removed
    2. Vertices are relabeled according to the mapping function `φ`

    This definition does not enforce that `φ` should relate to `C` in any way.
    For this definition to be sound, `φ` has to have the connected components of `G ↾ C` as fibers.
-/
@[simps!]
def Contract (G : Graph α β) (φ : α → α') (C : Set β) : Graph α' β :=
  (φ ''ᴳ G) ＼ C

notation:70 G " /["φ ", " C"] " => Graph.Contract G φ C

/- lemmas about Contract -/

variable {φ φ' τ : α → α'} {C C' D : Set β}

@[simp]
lemma contract_inc {x : α'} : G /[φ, C].Inc e x ↔ e ∉ C ∧ ∃ v, G.Inc e v ∧ φ v = x := by
  simp +contextual only [Contract, edgeDelete_inc_iff, map_inc, iff_def, not_false_eq_true,
    true_and, and_imp, forall_exists_index, and_true]
  tauto

lemma IsLink.contract (φ : α → α') (heC : e ∉ C) (hbtw : G.IsLink e u v) :
    G /[φ, C].IsLink e (φ u) (φ v) := by
  simp only [Contract, edgeDelete_isLink, Map_isLink, heC, not_false_eq_true, and_true]
  use u, v

@[gcongr]
lemma contract_mono (h : G ≤ H) : G /[φ, C] ≤ H /[φ, C] :=
  edgeDelete_mono_left (map_mono h) C

@[gcongr]
lemma contract_isSpanningSubgraph (h : G ≤s H) : G /[φ, C] ≤s H /[φ, C] :=
  (map_isSpanningSubgraph h).edgeDelete C

@[simp]
lemma contract_contract {φ' : α' → α''} : (G /[φ, C]) /[φ', C'] = G /[φ' ∘ φ, C ∪ C'] := by
  unfold Contract
  rw [map_edgeDelete_comm, map_map, edgeDelete_edgeDelete]

lemma edgeSet_disjoint_of_le_contract {φ : α → α} (h : G ≤ G /[φ, C]) : Disjoint E(G) C := by
  apply_fun edgeSet (α := α) (β := β) at h using edgeSet_monotone (α := α) (β := β)
  simpa [subset_diff] using h

@[simp]
lemma contract_eq_Map_of_disjoint (hdj : Disjoint E(G) C) : G /[φ, C] = φ ''ᴳ G := by
  unfold Contract
  rw [edgeDelete_eq_self _ (by simpa)]

lemma map_eq_self_of_contract_eq_self {φ : α → α} (h : G /[φ, C] = G) : (φ ''ᴳ G) = G := by
  unfold Contract at h
  rwa [edgeDelete_eq_self _ (by simp [edgeSet_disjoint_of_le_contract h.ge])] at h

/- The contract definition is sound when `φ` is a `(H ↾ C).connPartition.RepFun)`. -/
lemma map_repFun_of_walk {φ : (H ↾ C).connPartition.RepFun} {u v : α} {W : WList α β}
    (hw : (φ ''ᴳ H).IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) : H.ConnBetween u v := by
  match W with
  | .nil x =>
  simp_all only [nil_isWalk_iff, WList.nil_first, WList.nil_last]
  obtain ⟨y, hy, hyv⟩ := by simpa using hw
  have := φ.apply_eq_apply_iff_rel (by simp; exact hy) |>.mp (hyv.trans hv.symm)
  have := by simpa using this.symm.trans (φ.apply_eq_apply_iff_rel (by simp; exact hy) |>.mp hyv)
  exact this.of_le edgeRestrict_le
  | .cons x e w =>
  simp only [cons_isWalk_iff, WList.first_cons, WList.last_cons] at hw hu hv
  subst x
  obtain ⟨x, hx, hxeq⟩ := hw.1.right_mem
  refine .trans ?_ <| map_repFun_of_walk hw.2 hxeq.symm hv
  obtain ⟨a, b, hab, hu, hx⟩ := hxeq ▸ hw.1
  have hua := by simpa using φ.apply_eq_apply_iff_rel (by simpa using hab.left_mem) |>.mp hu.symm
  |>.symm
  have hva := by simpa using φ.apply_eq_apply_iff_rel (by simpa using hab.right_mem) |>.mp hx.symm
  exact (hua.of_le edgeRestrict_le).trans hab.connBetween |>.trans (hva.of_le edgeRestrict_le)

@[simp]
lemma map_repFun_connBetween {φ : (H ↾ C).connPartition.RepFun} {u v : α} :
    (φ ''ᴳ H).ConnBetween (φ u) (φ v) ↔ H.ConnBetween u v := by
  refine ⟨fun ⟨w, hw, hu, hv⟩ ↦ map_repFun_of_walk hw hu hv, ?_⟩
  rintro ⟨w, hw, rfl, rfl⟩
  induction w with
  | nil u =>
    simp only [nil_isWalk_iff, WList.nil_first, WList.nil_last, connBetween_self, Map_vertexSet,
      mem_image] at hw ⊢
    use u
  | cons u e w ih =>
    simp_all only [cons_isWalk_iff, WList.first_cons, WList.last_cons, forall_const]
    exact hw.1.map φ |>.connBetween.trans ih

def IsMinor (G H : Graph α β) :=
  ∃ (C : Set β) (φ : (H ↾ C).connPartition.RepFun), G ≤ H /[φ, C]

notation G " ≤ₘ " H => IsMinor G H

namespace IsMinor

lemma vertex_subset (h : G ≤ₘ H) : V(G) ⊆ V(H) := by
  obtain ⟨C, φ, hle⟩ := h
  refine vertexSet_mono (hle.trans edgeDelete_le) |>.trans ?_
  simpa only [connPartition_supp, edgeRestrict_vertexSet] using φ.image_subset_self

lemma edge_subset (h : G ≤ₘ H) : E(G) ⊆ E(H) := by
  obtain ⟨C, φ, hle⟩ := h
  exact (edgeSet_mono (hle.trans edgeDelete_le)).trans (by simp)

-- instance : IsPartialOrder (Graph α β) IsMinor where
--   refl G := by
--     refine ⟨∅, ?_, ?_⟩
--     · use id, by simp, ?_, ?_
--       · intro u hu
--         rwa [id_eq, Partition.rel_self_iff_mem]
--       intro u v huv
--       rw [connPartition_rel_iff, connBetween_iff_of_edgeless (by simp)] at huv
--       exact huv.2
--     simp only [disjoint_empty, contract_eq_Map_of_disjoint]
--     change G ≤ id ''ᴳ G
--     simp
--   trans G H I hGH hHI := by
--     classical
--     obtain ⟨C, φ, hle⟩ := by exact hGH
--     obtain ⟨C', φ', hle'⟩ := by exact hHI
--     refine ⟨C' ∪ C, ⟨φ ∘ (fun x ↦ if φ' x ∈ V(H) then φ' x else x), ?_, ?_, ?_⟩, ?_⟩
--     · simp only [connPartition_supp, edgeRestrict_vertexSet, comp_apply]
--       intro x hx
--       split_ifs with hxH
--       · have heq := φ'.apply_of_notMem (by simpa using hx)
--         exact (hx <| hHI.vertex_subset <| heq ▸ hxH).elim
--       have : x ∉ V(H) := fun hxH ↦ hx <| hHI.vertex_subset hxH
--       exact φ.apply_of_notMem (by simpa)
--     · intro x hx
--       simp only [connPartition_supp, edgeRestrict_vertexSet, comp_apply,
--         connPartition_rel_iff] at hx ⊢
--       split_ifs with hpxH
--       · have h2 := by simpa using φ.rel_apply (by simpa using hpxH)
--         have h1 := by simpa using φ'.rel_apply (by simpa using hx)
--         apply h1.of_le (edgeRestrict_mono_right _ subset_union_left) |>.trans ?_; clear h1
--         have h2' := h2.of_le (edgeRestrict_mono_left hle' C)
--         sorry
--       have hxH : x ∉ V(H) := fun hxH ↦ by
--         obtain ⟨y, hy, rfl⟩ := vertexSet_mono hle' hxH
--         exact (φ'.idem y ▸ hpxH) hxH
--       rw [φ.apply_of_notMem (by simpa using hxH)]
--       simpa using hx
--     · intro u v huv
--       simp_all only [connPartition_rel_iff, comp_apply]
--       sorry

--     sorry
--   antisymm G H hGH hHG := by sorry
