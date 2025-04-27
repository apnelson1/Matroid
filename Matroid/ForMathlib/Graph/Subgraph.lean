import Matroid.ForMathlib.Graph.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Sym.Sym2

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}

open Set

open scoped Sym2

namespace Graph

structure IsSubgraph (H G : Graph α β) : Prop where
  vx_subset : H.V ⊆ G.V
  inc₂_of_inc₂ : ∀ ⦃e x y⦄, H.Inc₂ e x y → G.Inc₂ e x y

/-- The subgraph order -/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨rfl.le, by simp⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1)
    fun e x y ↦ ⟨fun a ↦ h₁.inc₂_of_inc₂ a, fun a ↦ h₂.inc₂_of_inc₂ a⟩

lemma Inc₂.of_le (h : H.Inc₂ e x y) (hle : H ≤ G) : G.Inc₂ e x y :=
  hle.2 h

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  (h.choose_spec.of_le hle).inc_left

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma vxSet_subset_of_le (h : H ≤ G) : H.V ⊆ G.V :=
  h.1

lemma edgeSet_subset_of_le (h : H ≤ G) : H.E ⊆ G.E := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_inc₂_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

lemma le_iff : H ≤ G ↔ (H.V ⊆ G.V) ∧ ∀ ⦃e x y⦄, H.Inc₂ e x y → G.Inc₂ e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma Inc₂.of_le_of_mem (h : G.Inc₂ e x y) (hle : H ≤ G) (he : e ∈ H.E) : H.Inc₂ e x y := by
  obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ := (huv.of_le hle).eq_and_eq_or_eq_and_eq_of_inc₂ h
  · assumption
  exact huv.symm

lemma inc₂_iff_inc₂_of_le_of_mem (hle : H ≤ G) (he : e ∈ H.E) :
    G.Inc₂ e x y ↔ H.Inc₂ e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps] def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  V := G.V
  E := E₀ ∩ G.E
  Inc₂ e x y := e ∈ E₀ ∧ G.Inc₂ e x y
  inc₂_symm e x y h := by rwa [G.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ _ _ _ _ _ h h' := h.2.left_eq_or_eq_of_inc₂ h'.2
  edge_mem_iff_exists_inc₂ e := ⟨fun h ↦ by simp [h, G.exists_inc₂_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  vx_mem_left_of_inc₂ _ _ _ h := h.2.vx_mem_left

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
@[simps] def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  V := f '' G.V
  E := G.E
  Inc₂ e x' y' := ∃ x y, G.Inc₂ e x y ∧ x' = f x ∧ y' = f y
  inc₂_symm := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩
  eq_or_eq_of_inc₂_of_inc₂ := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq_of_inc₂ hzw <;> simp
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet h
      exact ⟨_, _, _, _, hxy, rfl, rfl⟩
    rintro ⟨-, -, x, y, h, rfl, rfl⟩
    exact h.edge_mem
  vx_mem_left_of_inc₂ := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.vx_mem_left

/-- The graph with vertex set `V` and no edges -/
@[simps] protected def noEdge (V : Set α) (β : Type*) : Graph α β where
  V := V
  E := ∅
  Inc₂ _ _ _ := False
  inc₂_symm := by simp
  eq_or_eq_of_inc₂_of_inc₂ := by simp
  edge_mem_iff_exists_inc₂ := by simp
  vx_mem_left_of_inc₂ := by simp

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V β ≤ G ↔ V ⊆ G.V := by
  simp [le_iff]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `G.V` for this definition to work,
even though this is the standard use case) -/
@[simps!]
protected def vxRestrict (G : Graph α β) (X : Set α) : Graph α β := Graph.mk'
  (V := X)
  (Inc₂ := fun e x y ↦ G.Inc₂ e x y ∧ x ∈ X ∧ y ∈ X)
  (inc₂_symm := fun e x y ↦ by simp [G.inc₂_comm, and_comm (a := (x ∈ X))])
  (eq_or_eq_of_inc₂_of_inc₂ := fun e x y u v ⟨h, _⟩ ⟨h', _⟩ ↦ G.eq_or_eq_of_inc₂_of_inc₂ h h')
  (vx_mem_left_of_inc₂ := fun _ _ _ ⟨_, h⟩ ↦ h.1)

lemma vxRestrict_le (G : Graph α β) {X : Set α} (hX : X ⊆ G.V) : G.vxRestrict X ≤ G :=
  ⟨hX, fun _ _ _ h ↦ h.1⟩

/-- The graph obtained from `G` by deleting a set of vertices. -/
@[simps!]
protected def vxDelete (G : Graph α β) (X : Set α) : Graph α β := G.vxRestrict (G.V \ X)

@[simp]
lemma vxDelete_le (G : Graph α β) (X : Set α) : G.vxDelete X ≤ G :=
  G.vxRestrict_le diff_subset

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps]
protected def singleEdge (u v : α) (e : β) : Graph α β where
  V := {u,v}
  E := {e}
  Inc₂ e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  inc₂_symm := by tauto
  eq_or_eq_of_inc₂_of_inc₂ := by aesop
  edge_mem_iff_exists_inc₂ := by tauto
  vx_mem_left_of_inc₂ := by tauto

lemma singleEdge_inc₂_iff : (Graph.singleEdge u v e).Inc₂ f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]

@[simp] lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.Inc₂ e u v := by
  simp only [le_iff, singleEdge_V, Set.pair_subset_iff, singleEdge_inc₂_iff, and_imp, Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.vx_mem_left, h.vx_mem_right⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ G.E → e ∈ H.E → G.Inc₂ e = H.Inc₂ e

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ hH hG ↦ (h hG hH).symm

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    H₁.Compatible H₂ := by
  intro e he₁ he₂
  ext x y
  rw [← inc₂_iff_inc₂_of_le_of_mem h₁ he₁, ← inc₂_iff_inc₂_of_le_of_mem h₂ he₂]

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.

(If `G` and `H` are `Compatible`, this doesn't occur.)  -/
protected def union (G H : Graph α β) : Graph α β where
  V := G.V ∪ H.V
  E := G.E ∪ H.E
  Inc₂ e x y := G.Inc₂ e x y ∨ (e ∉ G.E ∧ H.Inc₂ e x y)
  inc₂_symm e x y h := by rwa [G.inc₂_comm, H.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ := by
    rintro e x y v w (h | h) (h' | h')
    · exact h.left_eq_or_eq_of_inc₂ h'
    · exact False.elim <| h'.1 h.edge_mem
    · exact False.elim <| h.1 h'.edge_mem
    exact h.2.left_eq_or_eq_of_inc₂ h'.2
  edge_mem_iff_exists_inc₂ e := by
    refine ⟨?_, fun ⟨x, y, h⟩ ↦ h.elim (fun h' ↦ .inl h'.edge_mem) (fun h' ↦ .inr h'.2.edge_mem)⟩
    rw [← Set.union_diff_self]
    rintro (he | ⟨heH, heG⟩)
    · obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet he
      exact ⟨x, y, .inl h⟩
    obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet heH
    exact ⟨x, y, .inr ⟨heG, h⟩⟩
  vx_mem_left_of_inc₂ := by
    rintro e x y (h | h)
    · exact .inl h.vx_mem_left
    exact .inr h.2.vx_mem_left

instance : Union (Graph α β) where union := Graph.union

@[simp]
lemma union_vxSet (G H : Graph α β) : (G ∪ H).V = G.V ∪ H.V := rfl

@[simp]
lemma union_edgeSet (G H : Graph α β) : (G ∪ H).E = G.E ∪ H.E := rfl

lemma union_inc₂_iff : (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ (e ∉ G.E ∧ H.Inc₂ e x y) := Iff.rfl

lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  suffices ∀ ⦃e : β⦄ ⦃x y : α⦄, H₁.Inc₂ e x y ∨ e ∉ H₁.E ∧ H₂.Inc₂ e x y → G.Inc₂ e x y by
    simpa [le_iff, vxSet_subset_of_le h₁, vxSet_subset_of_le h₂, union_inc₂_iff]
  rintro e x y (h | ⟨-, h⟩) <;>
  exact h.of_le <| by assumption

lemma inc₂_or_inc₂_of_union (h : (G ∪ H).Inc₂ e x y) : G.Inc₂ e x y ∨ H.Inc₂ e x y := by
  rw [union_inc₂_iff] at h
  tauto

@[simp]
lemma left_le_union (G H : Graph α β) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_inc₂_iff]
  tauto

lemma Compatible.union_inc₂_iff (h : Compatible G H) :
    (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ H.Inc₂ e x y := by
  by_cases heG : e ∈ G.E
  · simp only [Graph.union_inc₂_iff, heG, not_true_eq_false, false_and, or_false, iff_self_or]
    exact fun heH ↦ by rwa [h heG heH.edge_mem]
  simp [Graph.union_inc₂_iff, heG]

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G :=
  Graph.ext (Set.union_comm ..) fun _ _ _ ↦ by rw [h.union_inc₂_iff, h.symm.union_inc₂_iff, or_comm]

lemma Compatible.right_le_union (h : Compatible G H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G :=
  ⟨fun h ↦ ⟨(left_le_union ..).trans h, (h_compat.right_le_union ..).trans h⟩,
    fun h ↦ union_le h.1 h.2⟩

lemma Compatible.of_disjoint_edgeSet (h : Disjoint G.E H.E) : Compatible G H :=
  fun _ heG heH ↦ False.elim <| h.not_mem_of_mem_left heG heH

@[simp]
lemma singleEdge_compatible_iff :
    (Graph.singleEdge x y e).Compatible G ↔ (e ∈ G.E → G.Inc₂ e x y) := by
  refine ⟨fun h he ↦ by simp [← h (by simp) he, singleEdge_inc₂_iff] , fun h f hf hfE ↦ ?_⟩
  obtain rfl : f = e := by simpa using hf
  ext u v
  rw [(h hfE).inc₂_iff, Graph.singleEdge_inc₂_iff, and_iff_right rfl, Sym2.eq_iff]
  tauto

  -- simp +contextual [Graph.singleEdge_Inc₂, iff_def, or_imp]
