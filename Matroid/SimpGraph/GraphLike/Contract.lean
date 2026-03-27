import Matroid.Graph.GraphLike.Graph
import Matroid.Graph.Map
import Matroid.Graph.Connected.Construction
import Matroid.Graph.Connected.Basic
import Matroid.ForMathlib.Partition.Rep

open Set Function WList

namespace Graph

/-! ## Contracting a set of edges -/

variable {α α' α'' β : Type*} {G H : Graph α β} {X : Set α} {C F : Set β} {φ : α → α'} {e : β}
  {u v x y z : α}

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

-- attribute [grind =] contract_vertexSet contract_edgeSet contract_isLink

notation:70 G " /["C ", " φ"] " => Graph.contract G C φ

/- lemmas about Contract -/

variable {φ φ' τ : α → α'} {C C' D : Set β}

@[simp, grind =]
lemma contract_inc {x : α'} : G /[C, φ].Inc e x ↔ e ∉ C ∧ ∃ v, G.Inc e v ∧ φ v = x := by
  simp +contextual only [contract, edgeDelete_inc_iff, map_inc, iff_def, not_false_eq_true,
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
  edgeDelete_mono_left (map_mono h) C

@[gcongr]
lemma contract_isSpanningSubgraph (h : G ≤s H) : G /[C, φ] ≤s H /[C, φ] :=
  (map_isSpanningSubgraph h).edgeDelete C

@[simp]
lemma contract_contract {φ' : α' → α''} : (G /[C, φ]) /[C', φ'] = G /[C ∪ C', φ' ∘ φ] := by
  unfold contract
  rw [map_edgeDelete_comm, map_map, edgeDelete_edgeDelete]

lemma contract_edgeRestrict_comm : H /[C, φ] ↾ F = (H ↾ F) /[C, φ] := by
  rw [contract, ← edgeRestrict_edgeDelete_comm, ← map_edgeRestrict_comm]
  rfl

lemma contract_edgeDelete_comm : (H /[C, φ]) ＼ F = (H ＼ F) /[C, φ] := by
  ext x y <;> grind

lemma edgeSet_disjoint_of_le_contract {φ : α → α} (h : G ≤ G /[C, φ]) : Disjoint E(G) C := by
  apply_fun edgeSet (α := α) (β := β) at h using edgeSet_monotone (α := α) (β := β)
  simpa [subset_diff] using h

@[simp]
lemma contract_eq_map_of_disjoint (hdj : Disjoint E(G) C) : G /[C, φ] = φ ''ᴳ G := by
  unfold contract
  rw [edgeDelete_eq _ (by simpa)]

lemma map_eq_self_of_contract_eq_self {φ : α → α} (h : G /[C, φ] = G) : (φ ''ᴳ G) = G := by
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
lemma preimage_vertexDelete_contract : (H - φ ⁻¹' X) /[C, φ] = H /[C, φ] - X := by
  rw [contract, contract, edgeDelete_vertexDelete, map_vertexDelete_preimage]

/- The contract definition is sound when `φ` is a `H.connPartition.IsRepFun`. -/
lemma contract_vertex_mono (hφ : G.connPartition.IsRepFun φ) (hGH : G ≤ H) :
    V(H /[E(G), φ]) ⊆ V(H) := by
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
    (hφ : H.connPartition.IsRepFun φ) : (G /[E(H), φ]).IsWalk <| (w.map φ).edgeRemove E(H) := by
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
