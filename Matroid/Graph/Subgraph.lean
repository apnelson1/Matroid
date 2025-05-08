import Matroid.Graph.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Sym.Sym2

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

structure IsSubgraph (H G : Graph α β) : Prop where
  vx_subset : V(H) ⊆ V(G)
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

lemma vxSet_subset_of_le (h : H ≤ G) : V(H) ⊆ V(G) :=
  h.1

lemma edgeSet_subset_of_le (h : H ≤ G) : E(H) ⊆ E(G) := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_inc₂_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

lemma le_iff : H ≤ G ↔ (V(H) ⊆ V(G)) ∧ ∀ ⦃e x y⦄, H.Inc₂ e x y → G.Inc₂ e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma Inc₂.of_le_of_mem (h : G.Inc₂ e x y) (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc₂ e x y := by
  obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ := (huv.of_le hle).eq_and_eq_or_eq_and_eq_of_inc₂ h
  · assumption
  exact huv.symm

lemma inc₂_iff_inc₂_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.Inc₂ e x y ↔ H.Inc₂ e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  vx_subset := hV
  inc₂_of_inc₂ e x y h := by
    rw [← G.inc₂_iff_inc₂_of_le_of_mem h₂ (hE h.edge_mem)]
    exact h.of_le h₁

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps inc₂]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vxSet := V(G)
  edgeSet := E₀ ∩ E(G)
  Inc₂ e x y := e ∈ E₀ ∧ G.Inc₂ e x y
  inc₂_symm e x y h := by rwa [G.inc₂_comm]
  eq_or_eq_of_inc₂_of_inc₂ _ _ _ _ _ h h' := h.2.left_eq_or_eq_of_inc₂ h'.2
  edge_mem_iff_exists_inc₂ e := ⟨fun h ↦ by simp [h, G.exists_inc₂_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  vx_mem_left_of_inc₂ _ _ _ h := h.2.vx_mem_left

scoped infixl:65 " ↾ "  => Graph.edgeRestrict

@[simp]
lemma edgeRestrict_edgeSet (G : Graph α β) (E₀ : Set β) : E(G ↾ E₀) = E₀ ∩ E(G) := rfl

@[simp]
lemma edgeRestrict_vxSet (G : Graph α β) (E₀ : Set β) : V(G ↾ E₀) = V(G) := rfl

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  vx_subset := rfl.le
  inc₂_of_inc₂ := by simp

lemma edgeRestrict_mono_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  vx_subset := rfl.subset
  inc₂_of_inc₂ _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F := by
  refine G.le_of_le_le_subset_subset (edgeRestrict_le.trans h) (by simp)
    (by simpa using vxSet_subset_of_le h) ?_
  simp [inter_subset_right.trans (edgeSet_subset_of_le h)]

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

/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`, but we also
use `copy` for better definitional properties. -/
@[simps!]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (E := E(G) \ F) (Inc₂ := fun e x y ↦ G.Inc₂ e x y ∧ e ∉ F) rfl
    (by simp [diff_subset])
    (fun e x y ↦ by
      simp only [edgeRestrict_inc₂, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
      exact fun h _ ↦ h.edge_mem)

scoped infixl:65 " ＼ "  => Graph.edgeDelete

lemma edgeDelete_eq_edgeRestrict (G : Graph α β) (F : Set β) :
    G ＼ F = G ↾ (E(G) \ F) := copy_eq_self ..

@[simp]
lemma edgeDelete_le (G : Graph α β) (F : Set β) : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

lemma edgeDelete_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

lemma edgeDelete_mono_left (h : H ≤ G) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (E(H) \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left (edgeSet_subset_of_le h)

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

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
@[simps]
def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  vxSet := f '' V(G)
  edgeSet := E(G)
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
  vxSet := V
  edgeSet := ∅
  Inc₂ _ _ _ := False
  inc₂_symm := by simp
  eq_or_eq_of_inc₂_of_inc₂ := by simp
  edge_mem_iff_exists_inc₂ := by simp
  vx_mem_left_of_inc₂ := by simp

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V β ≤ G ↔ V ⊆ V(G) := by
  simp [le_iff]

lemma edgeDelete_eq_noEdge (G : Graph α β) (hF : E(G) ⊆ F) : G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [edgeDelete_inc₂, noEdge_inc₂, iff_false, not_and, not_not]
  exact fun h ↦ hF h.edge_mem

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[simps! vxSet]
protected def induce (G : Graph α β) (X : Set α) : Graph α β := Graph.mk'
  (V := X)
  (Inc₂ := fun e x y ↦ G.Inc₂ e x y ∧ x ∈ X ∧ y ∈ X)
  (inc₂_symm := fun e x y ↦ by simp [G.inc₂_comm, and_comm (a := (x ∈ X))])
  (eq_or_eq_of_inc₂_of_inc₂ := fun e x y u v ⟨h, _⟩ ⟨h', _⟩ ↦ G.eq_or_eq_of_inc₂_of_inc₂ h h')
  (vx_mem_left_of_inc₂ := fun _ _ _ ⟨_, h⟩ ↦ h.1)

notation:max G:1000 "[" S "]" => Graph.induce G S

lemma induce_le (hX : X ⊆ V(G)) : G[X] ≤ G :=
  ⟨hX, fun _ _ _ h ↦ h.1⟩

@[simp]
lemma induce_inc₂_iff {X : Set α} : G[X].Inc₂ e x y ↔ G.Inc₂ e x y ∧ x ∈ X ∧ y ∈ X := Iff.rfl

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α β) (X : Set α) :
    E(G.induce X) = {e | ∃ x y, G.Inc₂ e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp]
lemma induce_edgeSet_subset (G : Graph α β) (X : Set α) : E(G.induce X) ⊆ E(G) := by
  rintro e ⟨x,y,h, -, -⟩
  exact h.edge_mem

lemma Inc₂.mem_induce_iff {X : Set α} (hG : G.Inc₂ e x y) : e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq_of_inc₂ he <;> simp [hx', hy']

lemma induce_induce (G : Graph α β) (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_inc₂_iff, edgeRestrict_inc₂]
  obtain he | he := em' (G.Inc₂ e x y)
  · simp [he]
  rw [he.mem_induce_iff]
  tauto

lemma induce_mono (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤ G[Y] where
  vx_subset := hXY
  inc₂_of_inc₂ _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

/-- The graph obtained from `G` by deleting a set of vertices. -/
protected def vxDelete (G : Graph α β) (X : Set α) : Graph α β := G [V(G) \ X]

instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
  hSub := Graph.vxDelete

lemma vxDelete_def (G : Graph α β) (X : Set α) : G - X = G [V(G) \ X] := rfl

@[simp]
lemma vxDelete_vxSet (G : Graph α β) (X : Set α) : V(G - X) = V(G) \ X := rfl

@[simp]
lemma vxDelete_edgeSet (G : Graph α β) (X : Set α) :
  E(G - X) = {e | ∃ x y, G.Inc₂ e x y ∧ (x ∈ V(G) ∧ x ∉ X) ∧ y ∈ V(G) ∧ y ∉ X}  := rfl

@[simp]
lemma vxDelete_inc₂_iff (G : Graph α β) (X : Set α) :
    (G - X).Inc₂ e x y ↔ (G.Inc₂ e x y ∧ (x ∈ V(G) ∧ x ∉ X) ∧ y ∈ V(G) ∧ y ∉ X) := Iff.rfl

@[simp]
lemma vxDelete_le : G - X ≤ G :=
  G.induce_le diff_subset

lemma Inc₂.mem_vxDelete_iff {X : Set α} (hG : G.Inc₂ e x y) : e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [vxDelete_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.vx_mem_left,
    and_iff_right hG.vx_mem_right]

@[simp]
lemma edgeRestrict_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_inc₂_iff, edgeRestrict_inc₂]
  tauto

lemma edgeRestrict_vxDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vxDelete_inc₂_iff, edgeRestrict_inc₂, edgeRestrict_vxSet]
  tauto

@[simp]
lemma edgeDelete_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ＼ F)[X] = G[X] ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]

@[simp]
lemma induce_vxDelete (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
  Graph.ext rfl <| by simp +contextual

/-- A graph with a single edge `e` from `u` to `v` -/
@[simps]
protected def singleEdge (u v : α) (e : β) : Graph α β where
  vxSet := {u,v}
  edgeSet := {e}
  Inc₂ e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  inc₂_symm := by tauto
  eq_or_eq_of_inc₂_of_inc₂ := by aesop
  edge_mem_iff_exists_inc₂ := by tauto
  vx_mem_left_of_inc₂ := by tauto

lemma singleEdge_comm (u v : α) (e : β) : Graph.singleEdge u v e = Graph.singleEdge v u e := by
  ext <;> simp [or_comm]

lemma singleEdge_inc₂_iff : (Graph.singleEdge u v e).Inc₂ f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]

@[simp] lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.Inc₂ e u v := by
  simp only [le_iff, singleEdge_vxSet, Set.pair_subset_iff, singleEdge_inc₂_iff, and_imp,
    Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.vx_mem_left, h.vx_mem_right⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → G.Inc₂ e = H.Inc₂ e

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ hH hG ↦ (h hG hH).symm

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ := by
  intro e he₁ he₂
  ext x y
  rw [← inc₂_iff_inc₂_of_le_of_mem h₁ he₁, ← inc₂_iff_inc₂_of_le_of_mem h₂ he₂]

lemma compatible_self (G : Graph α β) : G.Compatible G := by
  simp [Compatible]

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.

(If `G` and `H` are `Compatible`, this doesn't occur.)  -/
protected def union (G H : Graph α β) : Graph α β where
  vxSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  Inc₂ e x y := G.Inc₂ e x y ∨ (e ∉ E(G) ∧ H.Inc₂ e x y)
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
lemma union_vxSet (G H : Graph α β) : V(G ∪ H) = V(G) ∪ V(H) := rfl

@[simp]
lemma union_edgeSet (G H : Graph α β) : E(G ∪ H) = E(G) ∪ E(H) := rfl

lemma union_inc₂_iff : (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ (e ∉ E(G) ∧ H.Inc₂ e x y) := Iff.rfl

lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  suffices ∀ ⦃e : β⦄ ⦃x y : α⦄, H₁.Inc₂ e x y ∨ e ∉ E(H₁) ∧ H₂.Inc₂ e x y → G.Inc₂ e x y by
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

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_inc₂_iff]
  tauto

lemma Compatible.union_inc₂_iff (h : Compatible G H) :
    (G ∪ H).Inc₂ e x y ↔ G.Inc₂ e x y ∨ H.Inc₂ e x y := by
  by_cases heG : e ∈ E(G)
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

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H :=
  fun _ heG heH ↦ False.elim <| h.not_mem_of_mem_left heG heH

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) :=
  Graph.ext rfl fun e x y ↦ by rw [union_inc₂_iff,
    (Compatible.of_disjoint_edgeSet disjoint_sdiff_right).union_inc₂_iff, edgeDelete_inc₂, and_comm]

lemma Compatible.mono_left {G₀ : Graph α β} (h : Compatible G H) (hG₀ : G₀ ≤ G) :
    Compatible G₀ H := by
  intro e heG heH
  ext x y
  rw [← inc₂_iff_inc₂_of_le_of_mem hG₀ heG, h (edgeSet_subset_of_le hG₀ heG) heH]

lemma Compatible.mono_right {H₀ : Graph α β} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α β} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ :=
  (h.mono_left hG).mono_right hH

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (union_le hle rfl.le).antisymm (Compatible.right_le_union (H.compatible_self.mono_left hle))

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (union_le rfl.le hle).antisymm <| left_le_union ..

lemma Compatible.induce_left (h : Compatible G H) (X : Set α) : G[X].Compatible H := by
  intro e heG heH
  ext x y
  obtain ⟨u, v, heuv : G.Inc₂ e u v, hu, hv⟩ := heG
  simp only [induce_inc₂_iff, ← h heuv.edge_mem heH, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq_of_inc₂ heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (X : Set α) :
    G.Compatible H[X] :=
  (h.symm.induce_left X).symm

lemma Compatible.induce (h : Compatible G H) {X : Set α} :
    G[X].Compatible H[X] :=
  (h.induce_left X).induce_right X

@[simp]
lemma Compatible.induce_induce : G[X].Compatible G[Y] :=
  Compatible.induce_left (Compatible.induce_right G.compatible_self _) _

lemma Compatible.induce_union (h : G.Compatible H) (X : Set α) : (G ∪ H)[X] = G[X] ∪ H[X] := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_inc₂_iff, h.union_inc₂_iff, h.induce.union_inc₂_iff]
  tauto

lemma induce_union (G : Graph α β) (X Y : Set α) (hX : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    G [X ∪ Y] = G [X] ∪ G [Y] := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_inc₂_iff, mem_union, Compatible.induce_induce.union_inc₂_iff]
  by_cases hxy : G.Inc₂ e x y
  · by_cases hx : x ∈ X
    · simp [hx, show y ∉ Y from fun hy ↦ hX x hx y hy hxy.adj]
    by_cases hy : y ∈ X
    · simp [hy, show x ∉ Y from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
    simp [hx, hy]
  simp [hxy]

lemma Compatible.vxDelete_union (h : G.Compatible H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  refine Graph.ext union_diff_distrib fun e x y ↦ ?_
  simp only [vxDelete_inc₂_iff, union_vxSet, mem_union]
  rw [vxDelete_def, vxDelete_def, ((h.induce_left _).induce_right _).union_inc₂_iff,
    h.union_inc₂_iff]
  simp only [induce_inc₂_iff, mem_diff]
  by_cases hG : G.Inc₂ e x y
  · simp +contextual [hG, hG.vx_mem_left, hG.vx_mem_right]
  by_cases hH : H.Inc₂ e x y
  · simp +contextual [hH, hH.vx_mem_left, hH.vx_mem_right]
  simp [hG, hH]

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_inc₂_iff]
  simp only [edgeRestrict_inc₂, mem_union]
  tauto

lemma edgeRestrict_union_edgeDelete (G : Graph α β) (F : Set β) : (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α β) (F : Set β) : (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Compatible.union_comm]
  apply G.compatible_of_le_le (by simp) (by simp)

lemma induce_union_edgeDelete (G : Graph α β) (hX : X ⊆ V(G)) : G[X] ∪ (G ＼ E(G[X])) = G := by
  rw [← union_eq_union_edgeDelete, union_eq_self_of_le_left (induce_le hX)]

lemma edgeDelete_union_incude (G : Graph α β) (hX : X ⊆ V(G)) : (G ＼ E(G[X])) ∪ G[X] = G := by
  rw [(Compatible.of_disjoint_edgeSet _).union_comm, induce_union_edgeDelete _ hX]
  simp [disjoint_sdiff_left]

@[simp]
lemma singleEdge_compatible_iff :
    (Graph.singleEdge x y e).Compatible G ↔ (e ∈ E(G) → G.Inc₂ e x y) := by
  refine ⟨fun h he ↦ by simp [← h (by simp) he, singleEdge_inc₂_iff] , fun h f hf hfE ↦ ?_⟩
  obtain rfl : f = e := by simpa using hf
  ext u v
  rw [(h hfE).inc₂_iff, Graph.singleEdge_inc₂_iff, and_iff_right rfl, Sym2.eq_iff]
  tauto

/-! ### Induced Subgraphs -/

structure IsInducedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  inc₂_of_mem : ∀ ⦃e x y⦄, G.Inc₂ e x y → x ∈ V(H) → y ∈ V(H) → H.Inc₂ e x y

infixl:50 " ≤i " => Graph.IsInducedSubgraph
