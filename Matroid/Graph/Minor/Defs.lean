import Matroid.Graph.Map
import Matroid.ForMathlib.Partition.Rep


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

    This is the fundamental operation for creating graph minors. -/
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

lemma Map_eq_self_of_contract_eq_self {φ : α → α} (h : G /[φ, C] = G) : (φ ''ᴳ G) = G := by
  unfold Contract at h
  rwa [edgeDelete_eq_self _ (by simp [edgeSet_disjoint_of_le_contract h.ge])] at h

namespace Contract

/-- A function `φ` is valid on a graph `G` with respect to a set of edges `C` if
    it maps two vertices to the same vertex precisely when they are connected
    in the subgraph induced by the edges in `C`.

    This property ensures that contraction preserves the structure of the graph
    in a well-defined way. -/
def _root_.Graph.ValidIn (G : Graph α β) (φ : α → α') (C : Set β) :=
  ∀ v ∈ V(G), G[φ ⁻¹' {φ v}].IsCompOf (G ↾ C)

@[simp]
lemma map_mem (φ : α → α') (C : Set β) (hx : u ∈ V(G)) : φ u ∈ V(G /[φ, C]) := by
  use u

lemma ValidIn.of_inter_eq (hC : ValidIn G φ C) (h : E(G) ∩ C = E(G) ∩ D) :
    ValidIn G φ D := by
  rwa [ValidIn, ← (G.edgeRestrict_eq_edgeRestrict_iff C D).mpr h]

def IsMinor (G H : Graph α β) :=
  ∃ (φ : H.Retr) (C : Set β), H.ValidIn φ C ∧ G ≤ H /[φ, C]

notation G " ≤ₘ " H => IsMinor G H

-- instance : IsRefl (Graph α β) IsMinor where
--   refl G := ⟨id, ∅, by simp, by simp, fun ⦃x⦄ a ↦ a, by simp [Contract]⟩

-- instance : IsTrans (Graph α β) IsMinor where
--   trans G H I hGH hHI := by
--     obtain ⟨φ, C, hφ, hle⟩ := hGH
--     obtain ⟨φ', C', hφ', hle'⟩ := hHI
--     refine ⟨⟨φ ∘ φ', ?_, ?_⟩, C' ∪ C, ?_, hle.trans <| contract_contract ▸ contract_mono hle'⟩
--     · intro x hx
--       simp only [comp_apply]
--       have := φ'.mapsTo hx
--       have := by simpa using vertexSet_mono hle'
--       have := φ.mapsTo.image_subset.trans this


--       sorry
--     · rintro x hx
--       simp
--       sorry
--     sorry

-- instance : IsAntisymm (Graph α β) IsMinor where
--   antisymm G H hGH hHG := by
--     obtain ⟨φ, C, hφidem, hφto, hle⟩ := hGH
--     obtain ⟨φ', C', hφ'idem, hφ'to, hle'⟩ := hHG
--     have hLe := hle.trans <| contract_mono hle'
--     rw [contract_contract] at hLe
--     have hdj := edgeSet_disjoint_of_le_contract hLe
--     rw [disjoint_union_right] at hdj
--     rw [contract_eq_Map_of_disjoint hdj.1] at hle'
--     rw [contract_eq_Map_of_disjoint (hdj.2.mono_left <| by simpa using edgeSet_mono hle')]
--at hle
--     clear hdj hLe C C'
