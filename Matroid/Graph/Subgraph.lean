import Matroid.Graph.Basic


variable {α α' β β' : Type*} {G H : Graph α β} {e : β} {v x y : α}

namespace Graph

/-- Restrict a graph to a subset `R` of the edge set. -/
noncomputable def edgeRestrict (G : Graph α β) (R : Set β) : Graph α β where
  V := G.V
  E := G.E ∩ R
  incFun e :=
    have := Classical.dec (e ∈ R)
    if e ∈ R then G.incFun e else 0
  sum_eq e he := by simp [he.2, G.sum_eq he.1]
  vertex_support e v h := G.vertex_support (e := e) <| by aesop
  edge_support e v h := ⟨G.edge_support (v := v) (by aesop), by aesop⟩

@[simp]
lemma edgeRestrict_inc_iff {R : Set β} : (G.edgeRestrict R).Inc e x ↔ G.Inc e x ∧ e ∈ R := by
  simp_rw [edgeRestrict, Inc]
  split_ifs with h <;>
  simp [h]

@[simp]
lemma edgeRestrict_inc₂_iff {R : Set β} : (G.edgeRestrict R).Inc₂ e x y ↔ G.Inc₂ e x y ∧ e ∈ R := by
  simp only [Inc₂, isNonloopAt_iff, edgeRestrict_inc_iff, ne_eq, isLoopAt_iff, and_imp]
  aesop

/-- Delete a subset `D` of the edges. -/
noncomputable def edgeDel (G : Graph α β) (D : Set β) := G.edgeRestrict (G.E \ D)

lemma vxMap_aux (G : Graph α β) {f : α → α'} {x : α'} :
    (G.incFun e).mapDomain f x ≠ 0 ↔ ∃ v, f v = x ∧ G.Inc e v := by
  classical
  simp +contextual [← incFun_eq_zero, Finsupp.mapDomain, Finsupp.sum,
    Finsupp.single_apply, and_comm, ← incFun_ne_zero]

/-- Transport a graph to a new vertex type by mapping along a function.
Edges between identified vertices become loops. -/
noncomputable def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  V := f '' G.V
  E := G.E
  incFun e := (G.incFun e).mapDomain f
  sum_eq e he := by rwa [Finsupp.sum_mapDomain_index (by simp) (by simp), G.sum_eq]
  vertex_support e v := by
    simp only [ne_eq, vxMap_aux, Set.mem_image, forall_exists_index, and_imp]
    exact fun x hxv h ↦ ⟨x, h.vx_mem, hxv⟩
  edge_support e v := by
    simp only [ne_eq, vxMap_aux, forall_exists_index, and_imp]
    exact fun _ _ ↦ Inc.edge_mem

/-- `vxMap` has the expected incidence predicate. -/
@[simp]
lemma vxMap_inc_iff {α' : Type*} (G : Graph α β) (f : α → α') (x : α') (e : β) :
    (G.vxMap f).Inc e x ↔ ∃ v, f v = x ∧ G.Inc e v := by
  rw [← incFun_ne_zero, ← vxMap_aux]
  rfl

@[mk_iff]
structure IsSubgraph (H G : Graph α β) : Prop where
  vertex_subset : H.V ⊆ G.V
  inc₂_of_inc₂ : ∀ ⦃e x y⦄, H.Inc₂ e x y → G.Inc₂ e x y

lemma IsSubgraph.edge_subset (h : IsSubgraph H G) : H.E ⊆ G.E := by
  intro e he
  obtain ⟨x, y, hex⟩ := exists_inc₂_of_mem he
  exact (h.inc₂_of_inc₂ hex).edge_mem

instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl G := by simp [isSubgraph_iff]
  le_trans := fun G₁ G₂ G₃ ⟨hv, h⟩ ⟨hv', h'⟩ ↦ ⟨hv.trans hv', fun e x y h1 ↦ h' (h h1)⟩
  le_antisymm G G' h h' := ext_inc₂ (h.vertex_subset.antisymm h'.vertex_subset) fun e x y ↦
    ⟨fun hinc ↦ h.inc₂_of_inc₂ hinc, fun hinc ↦ h'.inc₂_of_inc₂ hinc⟩

lemma Inc₂.of_le (hexy : H.Inc₂ e x y) (hle : H ≤ G) : G.Inc₂ e x y :=
  hle.inc₂_of_inc₂ hexy

lemma Inc.of_le (hex : H.Inc e x) (hle : H ≤ G) : G.Inc e x := by
  obtain ⟨y, hy⟩ := hex.exists_inc₂
  exact (hy.of_le hle).inc_left

lemma isLoopAt.of_le (h : H.IsLoopAt e x) (hle : H ≤ G) : G.IsLoopAt e x := by
  rw [← inc₂_self_iff] at ⊢ h
  exact h.of_le hle

lemma IsNonloopAt.of_le (h : H.IsNonloopAt e x) (hle : H ≤ G) : G.IsNonloopAt e x := by
  obtain ⟨y, hy⟩ := h.exists_inc₂_ne
  exact (hy.2.of_le hle).isNonloop_at_left_of_ne hy.1.symm

lemma edgeRestrict_le (G : Graph α β) (R : Set β) : G.edgeRestrict R ≤ G :=
  ⟨rfl.subset, by simp +contextual⟩

/-- A cycle embedded in `G`. -/
structure CycleEmb (G : Graph α β) where
  n : ℕ
  pos : 0 < n
  vxFun : ZMod n ↪ α
  edgeFun : ZMod n → β
  forall_inc₂ : ∀ i, G.Inc₂ (edgeFun i) (vxFun i) (vxFun (i+1))

def CycleEmb.of_le (C : H.CycleEmb) (hle : H ≤ G) : G.CycleEmb where
  n := C.n
  pos := C.pos
  vxFun := C.vxFun
  edgeFun := C.edgeFun
  forall_inc₂ i := (C.forall_inc₂ i).of_le hle

def IsAcyclic (G : Graph α β) : Prop := IsEmpty G.CycleEmb

lemma IsAcyclic.mono (hG : G.IsAcyclic) (hle : H ≤ G) : H.IsAcyclic := by
  rw [IsAcyclic, isEmpty_iff] at hG ⊢
  exact fun C ↦ hG <| C.of_le hle
