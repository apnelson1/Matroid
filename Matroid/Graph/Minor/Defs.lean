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
  simp only [map_vertexSet, edgeDelete_vertexSet, mem_image, mem_insert_iff, mem_diff,
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
  simp only [map_isLink, edgeDelete_isLink, mem_singleton_iff, ne_eq]
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
def contract (G : Graph α β) (φ : α → α') (C : Set β) : Graph α' β :=
  (φ ''ᴳ G) ＼ C

notation:70 G " /["φ ", " C"] " => Graph.contract G φ C

/- lemmas about Contract -/

variable {φ φ' τ : α → α'} {C C' D : Set β}

@[simp]
lemma contract_inc {x : α'} : G /[φ, C].Inc e x ↔ e ∉ C ∧ ∃ v, G.Inc e v ∧ φ v = x := by
  simp +contextual only [contract, edgeDelete_inc_iff, map_inc, iff_def, not_false_eq_true,
    true_and, and_imp, forall_exists_index, and_true]
  tauto

lemma IsLink.contract (φ : α → α') (heC : e ∉ C) (hbtw : G.IsLink e u v) :
    G /[φ, C].IsLink e (φ u) (φ v) := by
  simp only [contract_isLink, heC, not_false_eq_true, and_true]
  use u, v

@[gcongr]
lemma contract_mono (h : G ≤ H) : G /[φ, C] ≤ H /[φ, C] :=
  edgeDelete_mono_left (map_mono h) C

@[gcongr]
lemma contract_isSpanningSubgraph (h : G ≤s H) : G /[φ, C] ≤s H /[φ, C] :=
  (map_isSpanningSubgraph h).edgeDelete C

@[simp]
lemma contract_contract {φ' : α' → α''} : (G /[φ, C]) /[φ', C'] = G /[φ' ∘ φ, C ∪ C'] := by
  unfold contract
  rw [map_edgeDelete_comm, map_map, edgeDelete_edgeDelete]

lemma edgeSet_disjoint_of_le_contract {φ : α → α} (h : G ≤ G /[φ, C]) : Disjoint E(G) C := by
  apply_fun edgeSet (α := α) (β := β) at h using edgeSet_monotone (α := α) (β := β)
  simpa [subset_diff] using h

@[simp]
lemma contract_eq_map_of_disjoint (hdj : Disjoint E(G) C) : G /[φ, C] = φ ''ᴳ G := by
  unfold contract
  rw [edgeDelete_eq_self _ (by simpa)]

lemma map_eq_self_of_contract_eq_self {φ : α → α} (h : G /[φ, C] = G) : (φ ''ᴳ G) = G := by
  unfold contract at h
  rwa [edgeDelete_eq_self _ (by simp [edgeSet_disjoint_of_le_contract h.ge])] at h

/- The contract definition is sound when `φ` is a `(H ↾ C).connPartition.RepFun)`. -/
lemma contract_vertex_mono (φ : (H ↾ C).connPartition.RepFun) : V(H /[φ, C]) ⊆ V(H) := by
  refine vertexSet_mono edgeDelete_le |>.trans ?_
  simpa only [connPartition_supp, edgeRestrict_vertexSet] using φ.image_subset_self

lemma IsWalk.map_connBetween_foo {φ : (H ↾ C).connPartition.RepFun} {u} {W}
    (hw : ((φ ''ᴳ H) ＼ C ↾ F).IsWalk W) (hu : W.first = φ u) (hv : W.last = φ v) :
    (H ↾ (C ∪ F)).ConnBetween u v := by
  match W with
  | .nil x =>
  simp_all only [edgeDelete_edgeRestrict, nil_isWalk_iff, edgeRestrict_vertexSet, map_vertexSet,
    mem_image, WList.nil_first, WList.nil_last]
  obtain ⟨y, hy, hyv⟩ := by simpa using hw
  have := φ.apply_eq_apply_iff_rel (by simp; exact hy) |>.mp (hyv.trans hv.symm)
  have := by simpa using this.symm.trans (φ.apply_eq_apply_iff_rel (by simp; exact hy) |>.mp hyv)
  exact this.of_le <|H.edgeRestrict_mono_right subset_union_left
  | .cons x e w =>
  simp only [cons_isWalk_iff, edgeRestrict_isLink, edgeDelete_isLink, map_isLink, WList.first_cons,
    WList.last_cons] at hw hu hv
  subst x
  obtain ⟨⟨heF, ⟨x, y, hxy, hux, hwfy⟩, heC⟩, hw⟩ := hw
  refine .trans ?_ <| hw.map_connBetween_foo hwfy hv
  have hua := by simpa using φ.apply_eq_apply_iff_rel (by simpa using hxy.left_mem) |>.mp hux.symm
  |>.symm
  refine (hua.of_le <| H.edgeRestrict_mono_right subset_union_left).trans
  <| IsLink.connBetween (e := e) (by simp [heF, hxy])

@[simp]
lemma contract_edgeRestrict_connBetween (φ : (H ↾ C).connPartition.RepFun) (F : Set β)
    (u v) : (H /[φ, C] ↾ F).ConnBetween (φ u) (φ v) ↔ (H ↾ (C ∪ F)).ConnBetween u v := by
  refine ⟨fun ⟨w, hw, hu, hv⟩ ↦ hw.map_connBetween_foo hu hv, ?_⟩
  rintro ⟨w, hw, rfl, rfl⟩
  induction w with
  | nil u =>
    simp only [nil_isWalk_iff, edgeRestrict_vertexSet, WList.nil_first, WList.nil_last,
      connBetween_self, contract_vertexSet, mem_image] at hw ⊢
    use u
  | cons u e w ih =>
    simp only [cons_isWalk_iff, edgeRestrict_isLink, mem_union, WList.first_cons,
      WList.last_cons] at hw ⊢
    by_cases he : e ∈ C
    · have heq : φ u = φ w.first := φ.apply_eq_of_rel _ _ <| connPartition_rel_iff _ _ _ |>.mpr
        <| hw.1.2.of_le_of_mem edgeRestrict_le (by simp [he, hw.1.2.edge_mem]) |>.connBetween
      rw [heq]
      exact ih hw.2
    specialize ih hw.2
    exact hw.1.2.contract φ he |>.of_le_of_mem edgeRestrict_le
      (by simp [he, hw.1.2.edge_mem, hw.1.1.resolve_left he]) |>.connBetween.trans ih

@[simp]
lemma contract_connBetween (φ : (H ↾ C).connPartition.RepFun) (u v) :
    (H /[φ, C]).ConnBetween (φ u) (φ v) ↔ H.ConnBetween u v := by
  convert contract_edgeRestrict_connBetween φ univ u v using 2 <;> rw [eq_comm] <;> simp

class IsPartitionGraph [Order.Frame α] (G : Graph α β) where
  exists_partition : ∃ P : Partition α, V(G) = P.parts

section IsPartitionGraph
variable [Order.Frame α]

lemma exists_partition (G : Graph α β) [h : G.IsPartitionGraph] :
    ∃ P : Partition α, V(G) = P.parts := h.exists_partition

lemma isPartitionGraph_of_vertex_subset (h : V(G) ⊆ V(H)) [H.IsPartitionGraph] :
    G.IsPartitionGraph := by
  obtain ⟨P, hP⟩ := H.exists_partition
  exact ⟨P.restrict V(G) (hP ▸ h), rfl⟩

lemma isPartitionGraph_of_le (h : G ≤ H) [H.IsPartitionGraph] : G.IsPartitionGraph :=
  isPartitionGraph_of_vertex_subset (vertexSet_mono h)

instance [G.IsPartitionGraph] : (G - X).IsPartitionGraph := isPartitionGraph_of_le vertexDelete_le
instance [G.IsPartitionGraph] : (G ↾ F).IsPartitionGraph := isPartitionGraph_of_le edgeRestrict_le
instance [G.IsPartitionGraph] : (G ＼ F).IsPartitionGraph := isPartitionGraph_of_le edgeDelete_le
instance [G.IsPartitionGraph] {φ : (G ↾ C).connPartition.RepFun} : (G /[φ, C]).IsPartitionGraph :=
  isPartitionGraph_of_vertex_subset (contract_vertex_mono φ)

@[simps!]
def sContract (G : Graph α β) [G.IsPartitionGraph] (C : Set β) : Graph α β :=
  G /[(sSup <| (G ↾ C).connPartition.partOf ·), C]

notation:70 G " /[" C "] " => Graph.sContract G C

lemma sContract_isPartitionGraph [G.IsPartitionGraph] : G/[C].IsPartitionGraph := by
  have hsupp : (G ↾ C).connPartition.supp = V(G) := connPartition_supp (G ↾ C)
  unfold sContract contract
  obtain ⟨P', hP'⟩ := G.exists_partition
  use (G ↾ C).connPartition.flatten <| hsupp.trans hP'
  ext v
  simp only [edgeDelete_vertexSet, map_vertexSet, mem_image, Partition.flatten_parts,
    Partition.mem_parts]
  refine ⟨fun ⟨x, hx, hv⟩ => ?_, fun ⟨x, hx, hv⟩ => ?_⟩ <;> subst v
  · use (G ↾ C).connPartition.partOf x, (G ↾ C).connPartition.partOf_mem (hsupp ▸ hx)
  · obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr <| (G ↾ C).connPartition.ne_bot_of_mem hx
    use v, hsupp ▸ mem_sUnion_of_mem hv hx, by rw [(G ↾ C).connPartition.eq_partOf_of_mem hx hv]

end IsPartitionGraph

structure minorMap (G : Graph α β) (H : Graph α' β) where
  map : V(G) → H.Subgraph
  nonempty : ∀ x, V((map x).val).Nonempty
  disj : Pairwise (Disjoint on map)
  link : ∀ e x y, G.IsLink e x.val y.val →
    ∃ u v, H.IsLink e u v ∧ u ∈ V((map x).val) ∧ v ∈ V((map y).val)

@[ext]
lemma minorMap_ext {F₁ F₂ : minorMap G H} (hmap : F₁.map = F₂.map) : F₁ = F₂ := by
  cases F₁; cases F₂
  simpa

instance : FunLike (minorMap G H) V(G) H.Subgraph where
  coe f := f.map
  coe_injective' _ _ := minorMap_ext

def IsMinor (G H : Graph α β) := Nonempty (minorMap G H)

notation G " ≤ₘ " H => IsMinor G H

lemma minorMap.ne_bot (F : minorMap G H) (x : V(G)) : F.map x ≠ ⊥ := by
  simpa using F.nonempty x

def minorMap_refl (G : Graph α β) : minorMap G G where
  map v := ⟨Graph.noEdge {v.val} β, by simp⟩
  nonempty v := by simp
  disj u v huv := by simpa [Subtype.coe_inj]
  link := by simp

def minorMap.trans {I : Graph α'' β} (F₁ : minorMap G H) (F₂ : minorMap H I) : minorMap G I where
  map v := ⟨
    I[⋃ x : V((F₁.map v).val), V((F₂.map ⟨x.val, vertexSet_mono (F₁.map v).prop x.prop⟩).val)]
    ↾ ⋃ x : V((F₁.map v).val), E((F₂.map ⟨x.val, vertexSet_mono (F₁.map v).prop x.prop⟩).val),
    edgeRestrict_le.trans <| induce_le <| by
      simp only [iUnion_coe_set, iUnion_subset_iff]
      exact fun x hx ↦ vertexSet_mono (F₂.map _).prop⟩
  nonempty v := by
    simp only [iUnion_coe_set, edgeRestrict_vertexSet, induce_vertexSet, nonempty_def, mem_iUnion]
    obtain ⟨x, hx⟩ := F₁.nonempty v
    obtain ⟨y, hy⟩ := F₂.nonempty ⟨x, vertexSet_mono (F₁.map v).prop hx⟩
    exact ⟨y, x, hx, hy⟩
  disj u v huv := by
    simp only [iUnion_coe_set, Subgraph.disjoint_iff, edgeRestrict_vertexSet, induce_vertexSet,
      disjoint_iUnion_right, disjoint_iUnion_left]
    intro x hx y hy
    generalize_proofs hyH hxH
    suffices hne : ⟨y, hyH⟩ ≠ (⟨x, hxH⟩ : V(H)) by simpa using F₂.disj hne
    have h := by simpa [disjoint_iff_forall_ne] using F₁.disj huv
    simp only [ne_eq, Subtype.mk.injEq]
    exact h hy hx
  link e x y hxy := by
    simp only [iUnion_coe_set, edgeRestrict_vertexSet, induce_vertexSet, mem_iUnion]
    obtain ⟨u, v, huv, hu, hv⟩ := F₁.link e x y hxy
    obtain ⟨a, b, hab, ha, hb⟩ := F₂.link e ⟨u, huv.left_mem⟩ ⟨v, huv.right_mem⟩ huv
    exact ⟨a, b, hab, (by use u, hu), (by use v, hv)⟩

instance : IsPreorder (Graph α β) IsMinor where
  refl G := ⟨minorMap_refl G⟩
  trans _ _ _ F₁ F₂ := ⟨F₁.some.trans F₂.some⟩

-- Not antisymm (it is upto vertex relabeling)

private noncomputable def minorMap.some_vx (F : minorMap G H) : V(G) → V(H) :=
  fun x ↦ ⟨(F.nonempty x).some, vertexSet_mono (F.map x).prop (F.nonempty x).some_mem⟩

private lemma minorMap.some_vx_mem (F : minorMap G H) (x : V(G)) :
    (F.some_vx x).val ∈ V((F.map x).val) := by
  simp only [minorMap.some_vx, Subtype.coe_mk]
  exact (F.nonempty x).some_mem

private lemma minorMap.some_vx_injective (F : minorMap G H) :
    Function.Injective (minorMap.some_vx F) := by
  refine fun x y hxy ↦ F.disj.eq ?_
  simp only [Subgraph.disjoint_iff, not_disjoint_iff]
  use F.some_vx x, F.some_vx_mem x, hxy ▸ F.some_vx_mem y

lemma minorMap.vertex_encard_le (F : minorMap G H) : V(G).encard ≤ V(H).encard :=
  ENat.card_le_card_of_injective F.some_vx_injective

lemma minorMap.edgeSet_mono (F : minorMap G H) : E(G) ⊆ E(H) := by
  intro e he
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨_, _, hab, -, -⟩ := F.link e ⟨u, huv.left_mem⟩ ⟨v, huv.right_mem⟩ huv
  exact hab.edge_mem



-- def IsMinor (G H : Graph α β) :=
--   ∃ (C : Set β) (φ : (H ↾ C).connPartition.RepFun), G ≤ H /[φ, C]

-- notation G " ≤ₘ " H => IsMinor G H

-- namespace IsMinor

-- lemma vertex_subset (h : G ≤ₘ H) : V(G) ⊆ V(H) := by
--   obtain ⟨C, φ, hle⟩ := h
--   refine vertexSet_mono (hle.trans edgeDelete_le) |>.trans ?_
--   simpa only [connPartition_supp, edgeRestrict_vertexSet] using φ.image_subset_self

-- lemma edge_subset (h : G ≤ₘ H) : E(G) ⊆ E(H) := by
--   obtain ⟨C, φ, hle⟩ := h
--   exact (edgeSet_mono (hle.trans edgeDelete_le)).trans (by simp)

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
--   antisymm G H hGH hHG := by
--     obtain ⟨C, φ, hle⟩ := by exact hGH
--     obtain ⟨C', φ', hle'⟩ := by exact hHG

--     sorry
