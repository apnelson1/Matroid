import Matroid.ForMathlib.Partition.Rep
import Matroid.Graph.Map
import Matroid.Graph.Connected.Construction
import Matroid.Graph.Connected.Basic


variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ I : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)} {W : WList α β}

open Set Function WList

lemma List.Nodup.getLast_not_mem_dropLast {l : List ι} (hnd : l.Nodup) (hne : l ≠ []) :
    l.getLast hne ∉ l.dropLast := by
  simp [List.mem_dropLast_iff hnd hne]

namespace Graph

lemma ConnBetween.eq_or_isLink_of_edgeSet_singleton (h : G.ConnBetween x y) (hE : E(G) = {e}) :
    x = y ∨ G.IsLink e x y := by
  obtain ⟨w, hw, rfl, rfl⟩ := h.exists_isPath
  match w with
  | .nil x => simp
  | .cons x e (.nil y) =>
    simp_all only [cons_isPath_iff, nil_isPath_iff, WList.nil_first, WList.mem_nil_iff,
      WList.first_cons, WList.last_cons, WList.nil_last, false_or]
    obtain ⟨hlink, hw, hxw⟩ := hw
    obtain rfl := by simpa [hE] using hlink.edge_mem
    exact hlink
  | .cons x e (.cons y f w) =>
    simp_all only [cons_isPath_iff, WList.first_cons, WList.mem_cons_iff, not_or, WList.last_cons]
    obtain ⟨hxy, ⟨hywf, hw, hyw⟩, hne, hxw⟩ := hw
    obtain rfl := by simpa [hE] using hywf.edge_mem
    obtain rfl := by simpa [hE] using hxy.edge_mem
    obtain rfl := hxy.left_unique hywf.symm
    simp at hxw

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
private lemma contract_vertexSet_isLink_lemma [DecidableEq α] (he : G.IsLink e x y) :
    V(((fun v ↦ if v = y then x else v) ''ᴳ G) ＼ {e}) = insert x (V(G) \ {y}) := by
  classical
  let inc : G.Inc e x := ⟨y, he⟩
  have hother : inc.other = y := by
    simpa [inc] using (IsLink.other_eq (G := G) (e := e) (x := x) (y := y) he)
  simpa [hother] using (contract_vertexSet_lemma (G := G) (e := e) (x := x) (he := inc))

private lemma contract_isLink_isLink_lemma [DecidableEq α] :
    (((fun v ↦ if v = y then x else v) ''ᴳ G) ＼ {e}).IsLink f u v ↔
      ∃ a b, (G.IsLink f a b ∧ f ≠ e) ∧
        (a = y ∧ x = u ∨ a ≠ y ∧ a = u) ∧ (b = y ∧ x = v ∨ b ≠ y ∧ b = v) := by
  classical
  simp only [map_isLink, edgeDelete_isLink, mem_singleton_iff, ne_eq]
  grind

/-! ## Contraction of one edge -/

/-- Contracts the edge given in the `IsLink` predicate by removing the second vertex and adding its
  edges to the first vertex. -/
@[simps (attr := grind =)]
def IsLink.contract (G : Graph α β) (he : G.IsLink e x y) : Graph α β where
  vertexSet := insert x (V(G) \ {y})
  edgeSet := E(G) \ {e}
  IsLink f u v := ∃ a b, (G.IsLink f a b ∧ f ≠ e) ∧
    (a = y ∧ x = u ∨ a ≠ y ∧ a = u) ∧ (b = y ∧ x = v ∨ b ≠ y ∧ b = v)
  isLink_symm f hf u v h := by
    classical
    have huv := contract_isLink_isLink_lemma.mpr h
    exact contract_isLink_isLink_lemma.mp huv.symm
  eq_or_eq_of_isLink_of_isLink f a b c d h1 h2 := by
    classical
    exact eq_or_eq_of_isLink_of_isLink _ (contract_isLink_isLink_lemma.mpr h1)
      (contract_isLink_isLink_lemma.mpr h2)
  edge_mem_iff_exists_isLink e' := by
    classical
    -- rewrite our `IsLink` predicate to that of a mapped/deleted graph
    simp_rw [← contract_isLink_isLink_lemma]
    exact (((fun v ↦ if v = y then x else v) ''ᴳ G) ＼ {e}).edge_mem_iff_exists_isLink e'
  left_mem_of_isLink e' x' y' := by
    classical
    simp_rw [← contract_isLink_isLink_lemma, ← contract_vertexSet_isLink_lemma he]
    convert (((fun v ↦ if v = y then x else v) ''ᴳ G) ＼ {e}).left_mem_of_isLink
      (e := e') (x := x') (y := y')

lemma IsLink.contract_vertexSet_of_ne (he : G.IsLink e x y) (hxy : x ≠ y) :
    V(he.contract) = V(G) \ {y} := by
  have hx' : x ∈ V(G) \ ({y} : Set α) := by
    refine ⟨he.left_mem, ?_⟩
    simpa [Set.mem_singleton_iff] using hxy
  -- `x` is already in `V(G) \ {y}`, so inserting it does nothing.
  simp [IsLink.contract, hx']

lemma IsLink.contract_vertex_encard_eq_add_one [G.Finite] (he : G.IsLink e x y) (hxy : x ≠ y) :
    V(G).encard = V(he.contract).encard + 1 := by
  classical
  have hy : y ∈ V(G) := he.right_mem
  -- `encard_diff_singleton_add_one` is in `Mathlib.Data.Set.Card`.
  have hV : V(he.contract) = V(G) \ ({y} : Set α) := he.contract_vertexSet_of_ne hxy
  have henc : (V(G) \ ({y} : Set α)).encard = V(he.contract).encard := by
    simpa using (congrArg Set.encard hV).symm
  calc
    V(G).encard = (V(G) \ ({y} : Set α)).encard + 1 := by
      simpa using (encard_diff_singleton_add_one (s := V(G)) (a := y) hy).symm
    _ = V(he.contract).encard + 1 := by simp [henc]

/-! ### Equality to a map/delete presentation -/

lemma IsLink.contract_eq_map_edgeDelete [DecidableEq α] (he : G.IsLink e x y) :
    he.contract = (fun v ↦ if v = y then x else v) ''ᴳ (G ＼ {e}) := by
  have h' : he.contract = (((fun v ↦ if v = y then x else v) ''ᴳ G) ＼ ({e} : Set β)) := by
    refine Graph.ext ?_ (fun f u v ↦ ?_)
    · simpa [IsLink.contract] using (contract_vertexSet_isLink_lemma he).symm
    simpa [IsLink.contract] using contract_isLink_isLink_lemma.symm
  simpa [map_edgeDelete_comm] using h'

@[simp]
lemma IsLoopAt.contract_eq (he : G.IsLoopAt e x) :
    (show G.IsLink e x x from he).contract = G ＼ {e} := by
  classical
  conv_rhs => rw [← (G ＼ {e}).map_id]
  rw [he.contract_eq_map_edgeDelete]
  refine map_congr_left_of_eqOn (fun u _hu ↦ ?_)
  by_cases hux : u = x <;> simp [hux]

lemma IsLink.contract_vertexDelete_of_notMem (he : G.IsLink e x y) (hx : x ∉ X) :
    he.contract - X = (G.vertexDelete_isInducedSubgraph (X \ {y}) |>.isLink_of_mem_mem
        he (by simp [hx, he.left_mem]) (by simp [he.right_mem]) |>.contract) := by
  ext a b c <;>
  · simp +contextual only [vertexDelete_vertexSet, contract_vertexSet, vertexDelete_isLink_iff,
    contract_isLink, mem_diff, mem_insert_iff, mem_singleton_iff]
    grind

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
@[simps! (attr := grind =)]
def contract (G : Graph α β) (φ : α → α') (C : Set β) : Graph α' β :=
  (φ ''ᴳ G) ＼ C

attribute [grind =] contract_vertexSet contract_edgeSet contract_isLink

notation:70 G " /["φ ", " C"] " => Graph.contract G φ C

/- lemmas about Contract -/

variable {φ φ' τ : α → α'} {C C' D : Set β}

@[simp]
lemma contract_inc {x : α'} : G /[φ, C].Inc e x ↔ e ∉ C ∧ ∃ v, G.Inc e v ∧ φ v = x := by
  simp +contextual only [contract, edgeDelete_inc_iff, map_inc, iff_def, not_false_eq_true,
    true_and, and_imp, forall_exists_index, and_true]
  tauto

lemma IsLink.contract_of_notMem (φ : α → α') (heC : e ∉ C) (hbtw : G.IsLink e u v) :
    G /[φ, C].IsLink e (φ u) (φ v) := by
  simp only [Graph.contract_isLink, heC, not_false_eq_true, and_true]
  use u, v

lemma IsLoopAt.contract_of_notMem (φ : α → α') (heC : e ∉ C) (hbtw : G.IsLoopAt e x) :
    G /[φ, C].IsLoopAt e (φ x) :=
  IsLink.contract_of_notMem φ heC hbtw

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

lemma contract_edgeRestrict_comm : H /[φ, E(G)] ↾ F = (H ↾ F) /[φ, E(G)] := by
  ext x y <;> grind

lemma contract_edgeDelete_comm : (H /[φ, E(G)]) ＼ F = (H ＼ F) /[φ, E(G)] := by
  ext x y <;> grind

lemma edgeSet_disjoint_of_le_contract {φ : α → α} (h : G ≤ G /[φ, C]) : Disjoint E(G) C := by
  apply_fun edgeSet (α := α) (β := β) at h using edgeSet_monotone (α := α) (β := β)
  simpa [subset_diff] using h

@[simp]
lemma contract_eq_map_of_disjoint (hdj : Disjoint E(G) C) : G /[φ, C] = φ ''ᴳ G := by
  unfold contract
  rw [edgeDelete_eq _ (by simpa)]

lemma map_eq_self_of_contract_eq_self {φ : α → α} (h : G /[φ, C] = G) : (φ ''ᴳ G) = G := by
  unfold contract at h
  rwa [edgeDelete_eq _ (by simp [edgeSet_disjoint_of_le_contract h.ge])] at h

variable {φ : α → α}

lemma _root_.Partition.IsRepFun.isContractClosed (hφ : (G ↾ C).connPartition.IsRepFun φ) :
    G.IsContractClosed φ C := by
  intro e u v heC huv
  have huvC : (G ↾ C).IsLink e u v := by
    simpa [edgeRestrict_isLink, heC] using (And.intro huv heC)
  have hrel : (G ↾ C).connPartition u v := by
    exact ((G ↾ C).connPartition_rel_iff u v).2 (huvC.adj.connBetween)
  exact hφ.apply_eq_apply hrel

lemma _root_.Partition.IsRepFun.isContractClosed_of_compatible (hφ : H.connPartition.IsRepFun φ)
    (hGH : Compatible G H) : G.IsContractClosed φ E(H) := by
  intro e u v heH huv
  obtain rfl | hne := eq_or_ne u v
  · rfl
  simp only [hφ.apply_eq_apply_iff_rel_of_ne hne, connPartition_rel_iff]
  exact hGH.isLink_eq huv.edge_mem heH ▸ huv |>.connBetween

lemma _root_.Partition.IsRepFun.isContractClosed_of_ge (hφ : H.connPartition.IsRepFun φ)
    (hHG : H ≤ G) : G.IsContractClosed φ E(H) :=
  hφ.isContractClosed_of_compatible (compatible_of_le hHG).symm

@[simp]
lemma preimage_vertexDelete_contract : (H - φ ⁻¹' X) /[φ, C] = H /[φ, C] - X := by
  rw [contract, contract, edgeDelete_vertexDelete, map_vertexDelete_preimage]

/- The contract definition is sound when `φ` is a `H.connPartition.IsRepFun`. -/
lemma contract_vertex_mono (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) :
    V(H /[φ, E(G)]) ⊆ V(H) := by
  refine vertexSet_mono edgeDelete_le |>.trans <| hφ.image_subset ?_
  simp [vertexSet_mono hGH]

lemma isLoopAt_map_iff_connBetween (hφ : G.connPartition.IsRepFun φ) :
    (φ ''ᴳ H).IsLoopAt e x ↔ ∃ u v, H.IsLink e u v ∧ (u = v ∨ G.ConnBetween u v) ∧ φ u = x := by
  simp only [map_isLoopAt, or_iff_not_imp_left, ← ne_eq]
  refine exists₂_congr (fun u v ↦ and_congr_right fun huv ↦ ⟨?_, ?_⟩)
  · rintro ⟨rfl, heq⟩
    refine ⟨fun huv ↦ ?_, rfl⟩
    simpa using hφ.rel_of_ne_of_apply_eq_apply huv heq
  rintro ⟨huv, rfl⟩
  obtain (rfl | hne) := eq_or_ne u v
  · simp
  simp [hφ.apply_eq_apply (by simpa using huv hne)]

lemma IsWalk.edgeRemove_contract [DecidablePred (· ∈ E(H))] {w} (h : G.IsWalk w) (hHG : H ≤ G)
    (hφ : H.connPartition.IsRepFun φ) : (G /[φ, E(H)]).IsWalk <| (w.map φ).edgeRemove E(H) := by
  induction w with
  | nil x =>
    simp only [nil_isWalk_iff, map_nil, edgeRemove_nil, contract_vertexSet] at h ⊢
    grind
  | cons x e w ih =>
    simp_all only [cons_isWalk_iff, map_cons, forall_const, edgeRemove_cons]
    split_ifs with heH
    · exact ih
    obtain ⟨hl, h⟩ := h
    have := edgeRemove_first (hφ.isContractClosed_of_compatible (compatible_of_le hHG).symm
    |>.exists_isLoopAt_of_isWalk h) (h.map φ)
    simp only [cons_isWalk_iff, this, map_first, contract_isLink, heH, not_false_eq_true,
      and_true, ih]
    use x, w.first, hl

lemma IsTrail.edgeRemove_contract [DecidablePred (· ∈ E(H))] {w} (h : G.IsTrail w) (hHG : H ≤ G)
    (hφ : H.connPartition.IsRepFun φ) : (G /[φ, E(H)]).IsTrail ((w.map φ).edgeRemove E(H)) :=
  ⟨h.isWalk.edgeRemove_contract hHG hφ, h.edge_nodup.sublist <| by simp⟩

lemma IsTour.edgeRemove_contract [DecidablePred (· ∈ E(H))] {w} (h : G.IsTour w) (hHG : H ≤ G)
    (hφ : H.connPartition.IsRepFun φ) (hne : ∃ e, e ∈ w.edge ∧ e ∉ E(H)) :
    (G /[φ, E(H)]).IsTour ((w.map φ).edgeRemove E(H)) := by
  refine ⟨h.toIsTrail.edgeRemove_contract hHG hφ, ?_, ?_⟩
  · obtain ⟨e, he, heH⟩ := hne
    exact nonempty_iff_exists_edge.mpr ⟨e, by simp [he, heH]⟩
  have := edgeRemove_first (hφ.isContractClosed_of_compatible (compatible_of_le hHG).symm
    |>.exists_isLoopAt_of_isWalk h.isWalk) (h.isWalk.map φ)
  simp only [WList.IsClosed, this, map_first, edgeRemove_last, map_last]
  exact congrArg φ h.isClosed

/-! ### A representative function for a single-edge contraction -/

namespace IsLink
variable [DecidableEq α]

/-- A representative function for the connected components of `G ↾ {e}` coming from a link
`G.IsLink e x y`: it identifies `y` with `x` and fixes all other vertices. -/
def repFun (_ : G.IsLink e x y) : α → α :=
  fun v ↦ if v = y then x else v

noncomputable def isRepFun (he : G.IsLink e x y) :
    (G ↾ {e}).connPartition.IsRepFun he.repFun where
  apply_of_notMem v hv := by
    unfold repFun
    split_ifs with hveq
    · subst v
      simp [he.right_mem] at hv
    rfl
  rel_apply v hv := by
    unfold repFun
    split_ifs with hveq
    · subst v
      simp only [connPartition_rel_iff]
      exact Adj.connBetween ⟨e, by simp, he.symm⟩
    simpa [he.right_mem] using hv
  apply_eq_apply v w hvw := by
    rw [connPartition_rel_iff] at hvw
    obtain rfl | hlink := hvw.eq_or_isLink_of_edgeSet_singleton (e := e) (by simp [he.edge_mem])
    · rfl
    simp only [edgeRestrict_isLink, mem_singleton_iff, true_and] at hlink
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink.eq_and_eq_or_eq_and_eq he <;> simp [repFun]

@[simp]
lemma repFun_apply (he : G.IsLink e x y) (v : α) : he.repFun v = if v = y then x else v := by
  simp [repFun]

@[simp]
lemma repFun_apply_of_ne (he : G.IsLink e x y) (hne : v ≠ y) : he.repFun v = v := by
  simp [repFun, hne]

@[simp]
lemma repFun_apply_right (he : G.IsLink e x y) : he.repFun y = x := by
  simp [repFun]

lemma repFun_toFun (he : G.IsLink e x y) : he.repFun = fun v ↦ if v = y then x else v := by
  ext v
  simp [repFun]

lemma contract' (he : G.IsLink e x y) : he.contract = G /[he.repFun, ({e} : Set β)] := by
  rw [he.contract_eq_map_edgeDelete, map_edgeDelete_comm]
  rfl

@[simp]
lemma repFun_preimage (he : G.IsLink e x y) (S : Set α) [DecidablePred (· ∈ S)] :
    he.repFun ⁻¹' S = if x ∈ S then insert y S else S \ {y} := by
  classical
  ext v
  simp only [he.repFun_toFun, mem_preimage]
  obtain (rfl | hvy) := eq_or_ne v y
  · simp only [↓reduceIte]
    split_ifs with hxS <;> simpa
  simp only [hvy, ↓reduceIte]
  split_ifs with hxS <;> simp [hvy]

end IsLink

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
-- instance [G.IsPartitionGraph] {hφ : (G ↾ C).connPartition.IsRepFun φ} :
--     (G /[φ, C]).IsPartitionGraph :=
--   isPartitionGraph_of_vertex_subset (contract_vertex_mono hφ)

@[simps! (attr := grind =)]
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
  disj : Pairwise (Disjoint on map)
  link : ∀ e x y, G.IsLink e x.val y.val →
    ∃ u v, H.IsLink e u v ∧ u ∈ V((map x).val) ∧ v ∈ V((map y).val)
  conn : ∀ x, (map x).val.Connected

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
  simpa using (F.conn x).nonempty

def minorMap_refl (G : Graph α β) : minorMap G G where
  map v := ⟨Graph.noEdge {v.val} β, by simp⟩
  disj u v huv := by simpa [Subtype.coe_inj]
  link := by simp
  conn v := by simp

-- TODO: Given indexed subgraphs of G, their union is G.induce (union of vertex sets)
-- |>.edgeRestrict (union of edge sets)
-- def minorMap.trans {I : Graph α'' β} (F₁ : minorMap G H) (F₂ : minorMap H I) : minorMap G I where
--   map v := ⟨
--     I[⋃ x : V((F₁.map v).val), V((F₂.map ⟨x.val, vertexSet_mono (F₁.map v).prop x.prop⟩).val)]
--     ↾ ⋃ x : V((F₁.map v).val), E((F₂.map ⟨x.val, vertexSet_mono (F₁.map v).prop x.prop⟩).val),
--     edgeRestrict_le.trans <| induce_le <| by
--       simp only [iUnion_coe_set, iUnion_subset_iff]
--       exact fun x hx ↦ vertexSet_mono (F₂.map _).prop⟩
--   disj u v huv := by
--     simp only [iUnion_coe_set, Subgraph.disjoint_iff, edgeRestrict_vertexSet, induce_vertexSet,
--       disjoint_iUnion_right, disjoint_iUnion_left]
--     intro x hx y hy
--     generalize_proofs hyH hxH
--     suffices hne : ⟨y, hyH⟩ ≠ (⟨x, hxH⟩ : V(H)) by simpa using F₂.disj hne
--     have h := by simpa [disjoint_iff_forall_ne] using F₁.disj huv
--     simp only [ne_eq, Subtype.mk.injEq]
--     exact h hy hx
--   link e x y hxy := by
--     simp only [iUnion_coe_set, edgeRestrict_vertexSet, induce_vertexSet, mem_iUnion]
--     obtain ⟨u, v, huv, hu, hv⟩ := F₁.link e x y hxy
--     obtain ⟨a, b, hab, ha, hb⟩ := F₂.link e ⟨u, huv.left_mem⟩ ⟨v, huv.right_mem⟩ huv
--     exact ⟨a, b, hab, (by use u, hu), (by use v, hv)⟩
--   conn v := by
--     simp only [iUnion_coe_set]

--     sorry

-- instance : IsPreorder (Graph α β) IsMinor where
--   refl G := ⟨minorMap_refl G⟩
--   trans _ _ _ F₁ F₂ := ⟨F₁.some.trans F₂.some⟩

-- Not antisymm (only upto vertex relabeling)

def minorMap_of_le (h : G ≤ H) : minorMap G H where
  map v := ⟨Graph.noEdge {v.val} β, by simp [vertexSet_mono h v.prop]⟩
  disj u v huv := by simpa [Subtype.coe_inj]
  link e x y hxy := ⟨x, y, h.isLink_of_isLink hxy, by simp⟩
  conn v := by simp

def minorMap_of_contract (hφ : (G ↾ C).connPartition.IsRepFun φ) : minorMap (G /[φ, C]) G where
  map v := ⟨(G ↾ C).walkable v.val, walkable_isClosedSubgraph.le.trans edgeRestrict_le⟩
  disj u v huv := by
    obtain ⟨u, ⟨x, hx, rfl⟩⟩ := u
    obtain ⟨v, ⟨y, hy, rfl⟩⟩ := v
    simp only [contract_vertexSet, ne_eq, Subtype.mk.injEq, Subgraph.disjoint_iff,
      disjoint_iff_forall_notMem, mem_walkable_iff] at huv ⊢
    intro z hxz hyz
    have := hφ.apply_eq_apply <| by simpa using hxz.trans hyz.symm
    simp [huv, hφ.idem] at this
  link e x y hxy := by
    obtain ⟨x, ⟨x', hx', rfl⟩⟩ := x
    obtain ⟨y, ⟨y', hy', rfl⟩⟩ := y
    simp only [contract_isLink, mem_walkable_iff] at hxy ⊢
    obtain ⟨⟨u, v, huv, hxu, hyv⟩, heC⟩ := hxy
    rw [hxu, hyv]
    refine ⟨u, v, huv, ?_, ?_⟩
    · simpa using hφ.rel_apply (by simpa using huv.left_mem) |>.symm
    · simpa using hφ.rel_apply (by simpa using huv.right_mem) |>.symm
  conn v := by
    simp only [contract_vertexSet]
    refine walkable_connected ?_
    have := by simpa only [connPartition_supp, edgeRestrict_vertexSet] using hφ.image_subset_supp
    exact this v.prop

private noncomputable def minorMap.some_vx (F : minorMap G H) : V(G) → V(H) :=
  fun x ↦ ⟨(F.conn x).nonempty.some, vertexSet_mono (F.map x).prop (F.conn x).nonempty.some_mem⟩

private lemma minorMap.some_vx_mem (F : minorMap G H) (x : V(G)) :
    (F.some_vx x).val ∈ V((F.map x).val) := by
  simp only [minorMap.some_vx, Subtype.coe_mk]
  exact (F.conn x).nonempty.some_mem

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


lemma IsMinor.refl (G : Graph α β) : G ≤ₘ G := ⟨minorMap_refl G⟩

-- lemma IsMinor.trans (hGH : G ≤ₘ H) (hHI : H ≤ₘ I) : G ≤ₘ I := by
--   exact ⟨hGH.some.trans hHI.some⟩

@[simp]
lemma isMinor_of_le (h : G ≤ H) : G ≤ₘ H := ⟨minorMap_of_le h⟩

@[simp]
lemma isMinor_of_contract (hφ : (G ↾ C).connPartition.IsRepFun φ) : G /[φ, C] ≤ₘ G :=
  ⟨minorMap_of_contract hφ⟩

lemma IsMinor.edgeSet_mono (hGH : G ≤ₘ H) : E(G) ⊆ E(H) := hGH.some.edgeSet_mono
