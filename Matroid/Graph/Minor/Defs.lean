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
    obtain rfl := by simpa only [hE, mem_singleton_iff] using hlink.edge_mem
    exact hlink
  | .cons x e (.cons y f w) =>
    simp_all only [cons_isPath_iff, WList.first_cons, WList.mem_cons_iff, not_or, WList.last_cons]
    obtain ⟨hxy, ⟨hywf, hw, hyw⟩, hne, hxw⟩ := hw
    obtain rfl := by simpa only [hE, mem_singleton_iff] using hywf.edge_mem
    obtain rfl := by simpa only [hE, mem_singleton_iff] using hxy.edge_mem
    obtain rfl := hxy.left_unique hywf.symm
    simp at hxw

@[simp]
lemma connBetween_isRepFun_left_iff {φ : α → α} (hφ : G.connPartition.IsRepFun φ) :
    G.ConnBetween (φ x) y ↔ G.ConnBetween x y := by
  wlog hx : x ∈ V(G)
  · have : φ x = x := hφ.apply_of_notMem (by simpa)
    simp [hx, this]
  have h' : G.ConnBetween x (φ x) := by simpa using hφ.rel_apply (by simpa)
  exact ⟨fun h => h'.trans h, fun h => h'.symm.trans h⟩

@[simp]
lemma connBetween_isRepFun_right_iff {φ : α → α} (hφ : G.connPartition.IsRepFun φ) :
    G.ConnBetween x (φ y) ↔ G.ConnBetween x y := by
  wlog hy : y ∈ V(G)
  · have : φ y = y := hφ.apply_of_notMem (by simpa)
    simp [hy, this]
  have h' : G.ConnBetween y (φ y) := by simpa using hφ.rel_apply (by simpa)
  exact ⟨fun h => h.trans h'.symm, fun h => h.trans h'⟩

/-! ## Contracting a set of edges -/

variable {α' α'' : Type*}

/-- `Contract G C φ` contracts the edges in set `C` of graph `G`,
    mapping the resulting vertices according to function `φ`.

    This operation creates a new graph where:
    1. Edges in set `C` are removed
    2. Vertices are relabeled according to the mapping function `φ`

    This definition does not enforce that `φ` should relate to `C` in any way.
    For this definition to be sound, `φ` has to have the connected components of `G ↾ C` as fibers.
-/
@[simps! (attr := grind =)]
def contract (G : Graph α β) (C : Set β) (φ : α → α') : Graph α' β :=
  (φ ''ᴳ G) ＼ C

-- attribute [grind =] vertexSet_contract edgeSet_contract contract_isLink

notation:70 G " /["C ", " φ"]" => Graph.contract G C φ

/- lemmas about Contract -/

variable {φ φ' τ : α → α'} {C C' D : Set β}

@[simp, grind =]
lemma contract_inc {x : α'} : G /[C, φ].Inc e x ↔ e ∉ C ∧ ∃ v, G.Inc e v ∧ φ v = x := by
  simp +contextual only [contract, deleteEdges_inc, map_inc, iff_def, not_false_eq_true,
    true_and, and_imp, forall_exists_index, and_true]
  tauto

lemma IsLink.contract_of_notMem (φ : α → α') (heC : e ∉ C) (hbtw : G.IsLink e u v) :
    G /[C, φ].IsLink e (φ u) (φ v) := by
  simp only [Graph.contract_isLink, heC, not_false_eq_true, and_true]
  use u, v

lemma IsLoopAt.contract_of_notMem (φ : α → α') (heC : e ∉ C) (hbtw : G.IsLoopAt e x) :
    G /[C, φ].IsLoopAt e (φ x) :=
  IsLink.contract_of_notMem φ heC hbtw

@[gcongr]
lemma contract_mono (h : G ≤ H) : G /[C, φ] ≤ H /[C, φ] :=
  deleteEdges_mono_left (map_mono h) C

@[gcongr]
lemma contract_isSpanningSubgraph (h : G ≤s H) : G /[C, φ] ≤s H /[C, φ] :=
  (map_isSpanningSubgraph h).deleteEdges C

@[simp]
lemma contract_contract {φ' : α' → α''} : (G /[C, φ]) /[C', φ'] = G /[C ∪ C', φ' ∘ φ] := by
  unfold contract
  rw [map_deleteEdges_comm, map_map, deleteEdges_deleteEdges]

lemma contract_restrict_comm : H /[C, φ] ↾ F = (H ↾ F) /[C, φ] := by
  rw [contract, ← restrict_deleteEdges_comm, ← map_restrict_comm]
  rfl

lemma contract_deleteEdges_comm : (H /[C, φ]) ＼ F = (H ＼ F) /[C, φ] := by
  ext x y <;> grind

lemma edgeSet_disjoint_of_le_contract {φ : α → α} (h : G ≤ G /[C, φ]) : Disjoint E(G) C := by
  apply_fun edgeSet (α := α) (β := β) at h using edgeSet_monotone (α := α) (β := β)
  simpa [subset_diff] using h

@[simp]
lemma contract_eq_map_of_disjoint (hdj : Disjoint E(G) C) : G /[C, φ] = φ ''ᴳ G := by
  unfold contract
  rw [deleteEdges_eq _ (by simpa)]

lemma map_eq_self_of_contract_eq_self {φ : α → α} (h : G /[C, φ] = G) : (φ ''ᴳ G) = G := by
  unfold contract at h
  rwa [deleteEdges_eq _ (by simp [edgeSet_disjoint_of_le_contract h.ge])] at h

variable {φ : α → α}

lemma _root_.Partition.IsRepFun.isContractClosed (hφ : (G ↾ C).connPartition.IsRepFun φ) :
    G.IsContractClosed φ C := by
  intro e u v heC huv
  have huvC : (G ↾ C).IsLink e u v := by
    simpa [restrict_isLink, heC] using (And.intro huv heC)
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
lemma preimage_deleteVerts_contract : (H - (φ ⁻¹' X)) /[C, φ] = (H /[C, φ]) - X := by
  rw [contract, contract, deleteEdges_deleteVerts, map_deleteVerts_preimage]

/- The contract definition is sound when `φ` is a `H.connPartition.IsRepFun`. -/
lemma contract_vertex_mono (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) :
    V(H /[E(G), φ]) ⊆ V(H) := by
  refine vertexSet_mono deleteEdges_le |>.trans <| hφ.image_subset ?_
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
    (hφ : H.connPartition.IsRepFun φ) : (G /[E(H), φ]).IsWalk <| (w.map φ).edgeRemove E(H) := by
  induction w with
  | nil x =>
    simp only [nil_isWalk_iff, map_nil, edgeRemove_nil, vertexSet_contract] at h ⊢
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
    (hφ : H.connPartition.IsRepFun φ) : (G /[E(H), φ]).IsTrail ((w.map φ).edgeRemove E(H)) :=
  ⟨h.isWalk.edgeRemove_contract hHG hφ, h.edge_nodup.sublist <| by simp⟩

lemma IsTour.edgeRemove_contract [DecidablePred (· ∈ E(H))] {w} (h : G.IsTour w) (hHG : H ≤ G)
    (hφ : H.connPartition.IsRepFun φ) (hne : ∃ e, e ∈ w.edge ∧ e ∉ E(H)) :
    (G /[E(H), φ]).IsTour ((w.map φ).edgeRemove E(H)) := by
  refine ⟨h.toIsTrail.edgeRemove_contract hHG hφ, ?_, ?_⟩
  · obtain ⟨e, he, heH⟩ := hne
    exact nonempty_iff_exists_edge.mpr ⟨e, by simp [he, heH]⟩
  have := edgeRemove_first (hφ.isContractClosed_of_compatible (compatible_of_le hHG).symm
    |>.exists_isLoopAt_of_isWalk h.isWalk) (h.isWalk.map φ)
  simp only [WList.IsClosed, this, map_first, edgeRemove_last, map_last]
  exact congrArg φ h.isClosed

/-! ## Contraction of one edge -/


namespace IsLink

section repFun
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
    simp only [restrict_isLink, mem_singleton_iff, true_and] at hlink
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

-- A bit of a mess to do (map ''ᴳ G ＼ {e}) without decidability assumptions.
private lemma vertexSet_contract_isLink_lemma (he : G.IsLink e x y) :
    V((he.repFun ''ᴳ G) ＼ {e}) = insert x (V(G) \ {y}) := by
  simp only [vertexSet_deleteEdges, vertexSet_map, repFun_apply]
  grind

private lemma contract_isLink_isLink_lemma :
    (((fun v ↦ if v = y then x else v) ''ᴳ G) ＼ {e}).IsLink f u v ↔
      ∃ a b, (G.IsLink f a b ∧ f ≠ e) ∧
        (a = y ∧ x = u ∨ a ≠ y ∧ a = u) ∧ (b = y ∧ x = v ∨ b ≠ y ∧ b = v) := by
  classical
  simp only [map_isLink, deleteEdges_isLink, mem_singleton_iff, ne_eq]
  grind

end repFun

/-- Contracts the edge given in the `IsLink` predicate by removing the second vertex and adding its
  edges to the first vertex. -/
@[simps]
def contract (G : Graph α β) (e : β) (he : G.IsLink e x y) : Graph α β where
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
    exact ((he.repFun ''ᴳ G) ＼ {e}).edge_mem_iff_exists_isLink e'
  left_mem_of_isLink e' x' y' := by
    classical
    simp_rw [← contract_isLink_isLink_lemma, ← vertexSet_contract_isLink_lemma he, he.repFun_toFun]
    convert (((fun v ↦ if v = y then x else v) ''ᴳ G) ＼ {e}).left_mem_of_isLink (e := e') (x := x')
      (y := y')

attribute [grind =] vertexSet_contract edgeSet_contract

notation:70 G " /("e ", " he")" => Graph.IsLink.contract G e he

lemma vertexSet_contract_of_ne (he : G.IsLink e x y) (hxy : x ≠ y) :
    V(G /(e, he)) = V(G) \ {y} := by
  have hx' : x ∈ V(G) \ ({y} : Set α) := by
    refine ⟨he.left_mem, ?_⟩
    simpa [Set.mem_singleton_iff] using hxy
  -- `x` is already in `V(G) \ {y}`, so inserting it does nothing.
  simp [IsLink.contract, hx']

lemma contract_vertex_encard_eq_add_one [G.Finite] (he : G.IsLink e x y) (hxy : x ≠ y) :
    V(G).encard = V(G /(e, he)).encard + 1 := by
  classical
  have hy : y ∈ V(G) := he.right_mem
  -- `encard_diff_singleton_add_one` is in `Mathlib.Data.Set.Card`.
  have hV : V(G /(e, he)) = V(G) \ ({y} : Set α) := he.vertexSet_contract_of_ne hxy
  have henc : (V(G) \ ({y} : Set α)).encard = V(G /(e, he)).encard := by
    simpa using (congrArg Set.encard hV).symm
  calc
    V(G).encard = (V(G) \ ({y} : Set α)).encard + 1 := by
      simpa using (encard_diff_singleton_add_one (s := V(G)) (a := y) hy).symm
    _ = V(G /(e, he)).encard + 1 := by simp [henc]

/-! ### Equality to a map/delete presentation -/

lemma contract_deleteVerts_of_notMem (he : G.IsLink e x y) (hx : x ∉ X) :
    (G /(e, he)) - X = (G.deleteVerts_isInducedSubgraph (X \ {y}) |>.isLink_of_mem_mem
        he (by simp [hx, he.left_mem]) (by simp [he.right_mem]) |>.contract) := by
  ext a b c <;>
  · simp +contextual only [vertexSet_deleteVerts, vertexSet_contract, deleteVerts_isLink_iff,
    contract_isLink, mem_diff, mem_insert_iff, mem_singleton_iff]
    grind

variable [DecidableEq α]

lemma contract_eq_map_deleteEdges (he : G.IsLink e x y) :
    G /(e, he) = he.repFun ''ᴳ (G ＼ {e}) := by
  have h' : G /(e, he) = ((he.repFun ''ᴳ G) ＼ ({e} : Set β)) := by
    refine Graph.ext ?_ (fun f u v ↦ ?_)
    · simpa [IsLink.contract] using (vertexSet_contract_isLink_lemma he).symm
    simpa [IsLink.contract] using contract_isLink_isLink_lemma.symm
  simpa [map_deleteEdges_comm] using h'

@[simp]
lemma _root_.Graph.IsLoopAt.contract_eq (he : G.IsLoopAt e x) :
    (show G.IsLink e x x from he).contract = G ＼ {e} := by
  classical
  conv_rhs => rw [← (G ＼ {e}).map_id]
  rw [he.contract_eq_map_deleteEdges]
  refine map_congr_left_of_eqOn (fun u _hu ↦ ?_)
  by_cases hux : u = x <;> simp [hux]

lemma contract_eq (he : G.IsLink e x y) : G /(e, he) = G /[({e} : Set β), he.repFun] := by
  rw [he.contract_eq_map_deleteEdges, map_deleteEdges_comm]
  rfl

lemma contract_isLink_of_ne (he : G.IsLink e x y) (hf : G.IsLink f u v) (hef : e ≠ f) :
    G /(e, he).IsLink f (he.repFun u) (he.repFun v) := by
  rw [contract_eq]
  grind

lemma contract_deleteEdges_comm (he : G.IsLink e x y) (heF : e ∉ F) :
    (G /(e, he)) ＼ F = G ＼ F /(e, ⟨he, heF⟩) := by
  simp_rw [contract_eq]
  rw [Graph.contract_deleteEdges_comm]
  congr 1

lemma contract_contract_comm_of_ne (he : G.IsLink e x y) (hf : G.IsLink f u v) (hyv : y ≠ v)
    (hor : x ≠ v ∨ y ≠ u) (hef : e ≠ f) :
    G /(e, he) /(f, he.contract_isLink_of_ne hf hef) =
    G /(f, hf) /(e, hf.contract_isLink_of_ne he hef.symm) := by
  simp_rw [contract_eq, contract_contract]
  rw [union_comm]
  congr 1
  ext a
  simp only [comp_apply, repFun_apply]
  grind

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

instance [G.IsPartitionGraph] : (G - X).IsPartitionGraph := isPartitionGraph_of_le deleteVerts_le
instance [G.IsPartitionGraph] : (G ↾ F).IsPartitionGraph := isPartitionGraph_of_le restrict_le
instance [G.IsPartitionGraph] : (G ＼ F).IsPartitionGraph := isPartitionGraph_of_le deleteEdges_le
-- instance [G.IsPartitionGraph] {hφ : (G ↾ C).connPartition.IsRepFun φ} :
--     (G /[C, φ]).IsPartitionGraph :=
--   isPartitionGraph_of_vertex_subset (contract_vertex_mono hφ)

@[simps! (attr := grind =)]
def sContract (G : Graph α β) [G.IsPartitionGraph] (C : Set β) : Graph α β :=
  G /[C, (sSup <| (G ↾ C).connPartition.partOf ·)]

notation:70 G " /[" C "] " => Graph.sContract G C

lemma sContract_isPartitionGraph [G.IsPartitionGraph] : G/[C].IsPartitionGraph := by
  have hsupp : (G ↾ C).connPartition.supp = V(G) := connPartition_supp (G ↾ C)
  unfold sContract contract
  obtain ⟨P', hP'⟩ := G.exists_partition
  use (G ↾ C).connPartition.flatten <| hsupp.trans hP'
  ext v
  simp only [vertexSet_deleteEdges, vertexSet_map, mem_image, Partition.flatten_parts,
    Partition.mem_parts]
  refine ⟨fun ⟨x, hx, hv⟩ => ?_, fun ⟨x, hx, hv⟩ => ?_⟩ <;> subst v
  · use (G ↾ C).connPartition.partOf x, (G ↾ C).connPartition.partOf_mem (hsupp ▸ hx)
  · obtain ⟨v, hv⟩ := nonempty_iff_ne_empty.mpr <| (G ↾ C).connPartition.ne_bot_of_mem hx
    use v, hsupp ▸ mem_sUnion_of_mem hv hx, by rw [(G ↾ C).connPartition.eq_partOf_of_mem hx hv]

end IsPartitionGraph

structure minorMap (G H : Graph α β) where
  map : V(G) → Graph α β
  map_le : ∀ x, map x ≤ H
  mem_map : ∀ x, x.val ∈ V(map x)
  disj : Pairwise (Disjoint on map)
  edge_disj : ∀ x, Disjoint E(G) E(map x)
  link : ∀ e x y, G.IsLink e x.val y.val → ∃ u v, H.IsLink e u v ∧ u ∈ V(map x) ∧ v ∈ V(map y)
  -- Relation.Map (G.IsLink e ·.val ·.val) map map
  conn : ∀ x, (map x).Connected

@[ext]
lemma minorMap_ext {F₁ F₂ : minorMap G H} (hmap : F₁.map = F₂.map) : F₁ = F₂ := by
  cases F₁; cases F₂
  simpa

instance : FunLike (minorMap G H) V(G) (Graph α β) where
  coe f := f.map
  coe_injective' _ _ := minorMap_ext

def IsMinor (G H : Graph α β) := Nonempty (minorMap G H)

notation G " ≤m " H => IsMinor G H

set_option backward.isDefEq.respectTransparency false in
lemma minorMap.ne_bot (F : minorMap G H) (x : V(G)) : F.map x ≠ ⊥ := by
  simpa using (F.conn x).nonempty

lemma minorMap.vertexSet_mono (F : minorMap G H) : V(G) ⊆ V(H) :=
  fun x hx ↦ (F.map_le ⟨x, hx⟩).vertexSet_mono (F.mem_map ⟨x, hx⟩)

lemma minorMap.edgeSet_mono (F : minorMap G H) : E(G) ⊆ E(H) := by
  intro e he
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨_, _, hab, -, -⟩ := F.link e ⟨u, huv.left_mem⟩ ⟨v, huv.right_mem⟩ huv
  exact hab.edge_mem

lemma minorMap.mem_iff_eq (F : minorMap G H) (x : V(G)) (hy : y ∈ V(F.map x)) :
    y ∈ V(G) ↔ x = y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := by simpa only [Graph.disjoint_iff, Subtype.ext_iff, not_disjoint_iff] using
      F.disj.eq (a := x) (b := ⟨y, h⟩)
    exact this ⟨y, hy, F.mem_map ⟨y, h⟩⟩
  rintro rfl
  exact x.prop

lemma minorMap.inj_of_mem (F : minorMap G H) {x y : V(G)} (hvx : v ∈ V(F.map x))
    (hvy : v ∈ V(F.map y)) : x = y :=
  F.disj.eq (a := x) (b := y) <| by
    simp only [Graph.disjoint_iff, not_disjoint_iff]
    exact ⟨v, hvx, hvy⟩

def minorMap_refl (G : Graph α β) : minorMap G G where
  map v := Graph.noEdge {v.val} β
  map_le v := by simp
  mem_map v := by simp
  disj u v huv := by simpa [Subtype.coe_inj]
  edge_disj v := by simp
  link := by simp
  conn v := by simp

lemma iUnion_eq_of_forall_le {ι : Type*} {Gι : ι → Graph α β} (hG : ∀ i, Gι i ≤ G) :
    Graph.iUnion Gι (compatible_of_forall_map_le hG) = G[⋃ i, V(Gι i)] ↾ ⋃ i, E(Gι i) := by
  let hcomp := compatible_of_forall_map_le hG
  refine Compatible.ext (by simp) ?_ ?_
  · simp only [edgeSet_iUnion, edgeSet_restrict, right_eq_inter, iUnion_subset_iff]
    intro i e hei
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet hei
    exact ⟨u, v, (hG i).isLink_mono huv, by grind [mem_iUnion]⟩
  exact G.compatible_of_le_le ((Graph.iUnion_le_iff hcomp).mpr hG)
    <| restrict_le.trans <| induce_le <| by simp [fun i ↦ vertexSet_mono (hG i)]

-- def minorMap.trans {I : Graph α'' β} (F₁ : minorMap G H) (F₂ : minorMap H I) : minorMap G I where
--   map v :=
--     I[⋃ x : V(F₁.map v), V(F₂.map ⟨x.val, (F₁.map_le v).vertexSet_mono x.prop⟩)]
--     ↾ (E(F₁.map v) ∪ ⋃ x : V(F₁.map v), E(F₂.map ⟨x.val, (F₁.map_le v).vertexSet_mono x.prop⟩))
--   map_le v := restrict_le.trans <| induce_le <| by
--       simp only [iUnion_coe_set, iUnion_subset_iff]
--       exact fun x hx ↦ vertexSet_mono (F₂.map_le _)
--   disj u v huv := by
--     simp only [iUnion_coe_set, Graph.disjoint_iff, vertexSet_restrict, vertexSet_induce,
--       disjoint_iUnion_right, disjoint_iUnion_left]
--     intro x hx y hy
--     generalize_proofs hyH hxH
--     suffices hne : ⟨y, hyH⟩ ≠ (⟨x, hxH⟩ : V(H)) by simpa using F₂.disj hne
--     have h := by simpa [disjoint_iff_forall_ne] using F₁.disj huv
--     simp only [ne_eq, Subtype.mk.injEq]
--     exact h hy hx
--   link e x y hxy := by
--     simp only [iUnion_coe_set, vertexSet_restrict, vertexSet_induce, mem_iUnion]
--     obtain ⟨u, v, huv, hu, hv⟩ := F₁.link e x y hxy
--     obtain ⟨a, b, hab, ha, hb⟩ := F₂.link e ⟨u, huv.left_mem⟩ ⟨v, huv.right_mem⟩ huv
--     exact ⟨a, b, hab, (by use u, hu), (by use v, hv)⟩
--   conn v := by
--     refine connected_iff.mpr ⟨?_, fun a b ha hb↦ ?_⟩
--     · simp only [iUnion_coe_set, vertexSet_restrict, vertexSet_induce, nonempty_iUnion]
--       exact ⟨_, (F₁.conn v).nonempty.some_mem, (F₂.conn _).nonempty⟩
--     simp only [iUnion_coe_set, vertexSet_restrict, vertexSet_induce, mem_iUnion] at ha hb
--     obtain ⟨x, hx, ha⟩ := ha
--     obtain ⟨y, hy, hb⟩ := hb
--     have hxy := F₁.conn v |>.pre x y hx hy
--     sorry

-- instance : IsPreorder (Graph α β) IsMinor where
--   refl G := ⟨minorMap_refl G⟩
--   trans _ _ _ F₁ F₂ := ⟨F₁.some.trans F₂.some⟩

-- Not antisymm (only upto vertex relabeling)

def minorMap_of_le (h : G ≤ H) : minorMap G H where
  map v := Graph.noEdge {v.val} β
  map_le v := by simp [vertexSet_mono h v.prop]
  mem_map v := by simp
  disj u v huv := by simpa [Subtype.coe_inj]
  edge_disj v := by simp
  link e x y hxy := ⟨x, y, h.isLink_mono hxy, by simp⟩
  conn v := by simp

def minorMap_of_contract (hφ : (G ↾ C).connPartition.IsRepFun φ) : minorMap (G /[C, φ]) G where
  map v := (G ↾ C).walkable v.val
  map_le v := walkable_isClosedSubgraph.le.trans restrict_le
  mem_map v := by simpa using hφ.image_subset_supp (by simpa [-Subtype.coe_prop] using v.prop)
  disj u v huv := by
    obtain ⟨u, ⟨x, hx, rfl⟩⟩ := u
    obtain ⟨v, ⟨y, hy, rfl⟩⟩ := v
    simpa [hφ.apply_eq_apply_iff_rel (by simpa : x ∈ _), hφ] using huv
  edge_disj v := by
    simp only [edgeSet_contract, vertexSet_contract]
    refine disjoint_sdiff_inter.mono_right (walkable_isCompOf ?_).le.edgeSet_mono
    rw [vertexSet_restrict]
    exact contract_vertex_mono hφ restrict_le v.prop
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
    simp only [vertexSet_contract]
    refine walkable_connected ?_
    have := by simpa only [connPartition_supp, vertexSet_restrict] using hφ.image_subset_supp
    exact this v.prop

lemma minorMap.mem_iUnion_of_edge_mem (F : minorMap G H) (he : e ∈ E(G) ∪ ⋃ v, E(F.map v))
    (h : H.Inc e x) : x ∈ ⋃ v, V(F.map v) := by
  rw [mem_iUnion]
  obtain (he | ⟨v, ⟨a, rfl⟩, he⟩) := he
  · obtain ⟨u, v, heG⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain ⟨a, b, hab, ha, hb⟩ := F.link e ⟨u, heG.left_mem⟩ ⟨v, heG.right_mem⟩ heG
    grind
  use a, h.of_le_of_mem (F.map_le a) he |>.vertex_mem

private def minorMap.intermediate (F : minorMap G H) : Graph α β :=
  H[⋃ x, V(F.map x)] ↾ (E(G) ∪ ⋃ x, E(F.map x))

@[simp]
private lemma minorMap.vertexSet_intermediate (F : minorMap G H) :
    V(F.intermediate) = ⋃ x, V(F.map x) := by
  simp [intermediate]

@[simp]
private lemma minorMap.edgeSet_intermediate (F : minorMap G H) :
    E(F.intermediate) = E(G) ∪ ⋃ x, E(F.map x) := by
  rw [intermediate, edgeSet_restrict, inter_eq_right, edgeSet_induce_eq_diff, subset_diff,
    union_subset_iff]
  refine ⟨⟨F.edgeSet_mono, ?_⟩, ?_⟩
  · simp only [iUnion_coe_set, iUnion_subset_iff]
    intro x hx
    exact F.map_le ⟨x, hx⟩ |>.edgeSet_mono
  simp only [disjoint_iff_forall_notMem, mem_setIncEdges_iff, mem_diff, not_exists, not_and,
    and_imp]
  exact fun _ he _ _ hy hey ↦ hy <| F.mem_iUnion_of_edge_mem he hey

private lemma minorMap.intermediate_le (F : minorMap G H) : F.intermediate ≤ H := by
  refine restrict_le.trans <| induce_le ?_
  simp only [iUnion_coe_set, iUnion_subset_iff]
  exact fun x hx ↦ (F.map_le ⟨x, hx⟩).vertexSet_mono

private lemma minorMap.vertexSet_subset_intermediate (F : minorMap G H) :
    V(G) ⊆ V(F.intermediate) := by
  intro x hx
  simp only [vertexSet_intermediate, mem_iUnion]
  use ⟨x, hx⟩, F.mem_map ⟨x, hx⟩

private lemma minorMap.edgeSet_subset_intermediate (F : minorMap G H) :
    E(G) ⊆ E(F.intermediate) := by
  intro e he
  simp [edgeSet_intermediate, mem_iUnion, he]

private lemma minorMap.map_isCompOf_intermediate (F : minorMap G H) (v : V(G)) :
    (F.map v).IsCompOf (F.intermediate ↾ ⋃ x, E(F.map x)) := by
  unfold intermediate
  rw [restrict_restrict, inter_eq_right.mpr subset_union_right, ← iUnion_eq_of_forall_le F.map_le]
  refine (F.conn v).IsCompOf_of_isClosedSubgraph <| IsClosedSubgraph.mk' (Graph.le_iUnion ..) ?_
  intro e x he hx
  simp only [iUnion_inc_iff, Subtype.exists] at he
  obtain ⟨u, hu, heu⟩ := he
  obtain rfl := F.disj.eq <| Graph.disjoint_iff.not.mpr <| not_disjoint_iff.mpr
    ⟨x, hx, heu.vertex_mem⟩
  exact heu.edge_mem

private noncomputable def minorMap.repFun (F : minorMap G H) : α → α :=
  letI : DecidablePred (∃ v : V(G), · ∈ V(F.map v)) := Classical.decPred _
  fun x ↦ if h : ∃ v : V(G), x ∈ V(F.map v) then h.choose else x

private lemma minorMap.repFun_of_mem_map (F : minorMap G H) {x : V(G)} (hx : v ∈ V(F.map x)) :
    F.repFun v = x := by
  have h : ∃ u, v ∈ V(F.map u) := by use x
  simp only [repFun, h, ↓reduceDIte, ← Subtype.ext_iff]
  exact F.disj.eq <| Graph.disjoint_iff.not.mpr <| not_disjoint_iff.mpr ⟨v, h.choose_spec, hx⟩

private lemma minorMap.repFun_of (F : minorMap G H) (x : V(G)) : F.repFun x.val = x.val := by
  simp only [dite_eq_right_iff, repFun]
  intro h
  rw [← F.mem_iff_eq _ h.choose_spec]
  exact x.prop

private lemma minorMap.repFun_mapsTo (F : minorMap G H) :
    MapsTo F.repFun V(F.intermediate) V(G) := by
  intro x hx
  simp only [intermediate, vertexSet_restrict, vertexSet_induce, mem_iUnion] at hx
  simp [repFun, hx]

private lemma minorMap.repFun_prop (F : minorMap G H) (x : α) (hx : x ∈ V(F.intermediate)) :
    x ∈ V(F.map (⟨F.repFun x, F.repFun_mapsTo hx⟩)) := by
  simp only [intermediate, vertexSet_restrict, vertexSet_induce, mem_iUnion] at hx
  simp only [repFun, hx, ↓reduceDIte, Subtype.coe_eta]
  exact hx.choose_spec

private lemma minorMap.repFun_isRepFun (F : minorMap G H) :
    (F.intermediate ↾ ⋃ x, E(F.map x)).connPartition.IsRepFun F.repFun where
  apply_of_notMem x hx := by
    simp only [connPartition_supp, vertexSet_restrict, vertexSet_intermediate] at hx ⊢
    grind [repFun, mem_iUnion]
  rel_apply x hx := by
    simp only [connPartition_supp, vertexSet_restrict, vertexSet_intermediate, mem_iUnion,
      Subtype.exists, connPartition_rel_iff] at hx ⊢
    obtain ⟨v, hv, hxv⟩ := hx
    rw [F.repFun_of_mem_map hxv]
    exact F.conn ⟨v, hv⟩ |>.pre x v hxv (F.mem_map ⟨v, hv⟩) |>.mono
      (F.map_isCompOf_intermediate ⟨v, hv⟩).le
  apply_eq_apply x y hxy := by
    have hx : ∃ u, x ∈ V(F.map u) := by simpa using hxy.left_mem
    have hy : ∃ v, y ∈ V(F.map v) := by simpa using hxy.right_mem
    simp only [connPartition_rel_iff, repFun, hx, ↓reduceDIte, hy, ← Subtype.ext_iff] at hxy ⊢
    refine F.inj_of_mem (hx.choose_spec) ?_
    rw [F.map_isCompOf_intermediate hy.choose |>.eq_walkable_of_mem_walkable hy.choose_spec]
    exact hxy.symm

@[simp]
private lemma minorMap.intermediate_isLink (F : minorMap G H) :
    F.intermediate.IsLink e x y ↔ H.IsLink e x y ∧ e ∈ (E(G) ∪ ⋃ x, E(F.map x)) := by
  refine ⟨fun h ↦ ⟨F.intermediate_le.isLink_mono h, F.edgeSet_intermediate ▸ h.edge_mem⟩,
    fun ⟨hH, he⟩ ↦ ?_⟩
  rw [intermediate, restrict_isLink, induce_isLink]
  exact ⟨he, hH, F.mem_iUnion_of_edge_mem he hH.inc_left, F.mem_iUnion_of_edge_mem he hH.inc_right⟩

lemma minorMap.exists_le_contract (F : minorMap G H) :
    ∃ H' C φ, H' ≤ H ∧ (H' ↾ C).connPartition.IsRepFun φ ∧ G = H' /[C, φ] := by
  use F.intermediate, ⋃ x, E(F.map x), F.repFun, F.intermediate_le, F.repFun_isRepFun
  ext a b c
  · simp only [iUnion_coe_set, vertexSet_contract, mem_image]
    refine ⟨fun haG ↦ ⟨a, F.vertexSet_subset_intermediate haG, F.repFun_of ⟨a, haG⟩⟩, ?_⟩
    rintro ⟨b, hb, rfl⟩
    exact F.repFun_mapsTo hb
  simp only [contract_isLink, intermediate_isLink]
  refine ⟨fun habc ↦ ?_, ?_⟩
  · have habc' : G.IsLink a (⟨b, habc.left_mem⟩ : V(G)).val (⟨c, habc.right_mem⟩ : V(G)).val := habc
    obtain ⟨x, y, hxy, hx, hy⟩ := F.link a _ _ habc'
    refine ⟨⟨x, y, ⟨hxy, Or.inl habc.edge_mem⟩, ?_, ?_⟩, ?_⟩
    · rw [F.repFun_of_mem_map hx]
    · rw [F.repFun_of_mem_map hy]
    simp only [mem_iUnion, not_exists]
    exact fun v ↦ F.edge_disj v |>.notMem_of_mem_left habc.edge_mem
  rintro ⟨⟨x, y, ⟨hxy, ha⟩, rfl, rfl⟩, hamap⟩
  replace ha := ha.resolve_right hamap
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet ha
  obtain ⟨n, m, hnm, hn, hm⟩ := F.link a ⟨u, huv.left_mem⟩ ⟨v, huv.right_mem⟩ huv
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hxy.eq_and_eq_or_eq_and_eq hnm <;>
    rw [F.repFun_of_mem_map hn, F.repFun_of_mem_map hm]
  · exact huv
  exact huv.symm

lemma IsMinor.refl (G : Graph α β) : G ≤m G := ⟨minorMap_refl G⟩

-- lemma IsMinor.trans (hGH : G ≤ₘ H) (hHI : H ≤ₘ I) : G ≤ₘ I := by
--   exact ⟨hGH.some.trans hHI.some⟩

@[simp]
lemma isMinor_of_le (h : G ≤ H) : G ≤m H := ⟨minorMap_of_le h⟩

@[simp]
lemma isMinor_of_contract (hφ : (G ↾ C).connPartition.IsRepFun φ) : G /[C, φ] ≤m G :=
  ⟨minorMap_of_contract hφ⟩

lemma IsMinor.edgeSet_mono (hGH : G ≤m H) : E(G) ⊆ E(H) := hGH.some.edgeSet_mono
