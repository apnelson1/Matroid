import Matroid.Graph.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}

open Set Function

open scoped Sym2

namespace Graph

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
@[simps]
def vertexMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  vertexSet := f '' V(G)
  edgeSet := E(G)
  IsLink e x' y' := ∃ x y, G.IsLink e x y ∧ x' = f x ∧ y' = f y
  isLink_symm := by
    rintro e he - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
      exact ⟨_, _, _, _, hxy, rfl, rfl⟩
    rintro ⟨-, -, x, y, h, rfl, rfl⟩
    exact h.edge_mem
  left_mem_of_isLink := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.left_mem

/-- The graph with vertex set `V` and no edges -/
@[simps]
protected def noEdge (V : Set α) (β : Type*) : Graph α β where
  vertexSet := V
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp
  left_mem_of_isLink := by simp

lemma eq_empty_or_vertexSet_nonempty (G : Graph α β) : G = Graph.noEdge ∅ β ∨ V(G).Nonempty := by
  refine V(G).eq_empty_or_nonempty.elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) Or.inr
  simp only [noEdge_isLink, iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

@[simp]
lemma noEdge_le_iff {V : Set α} : Graph.noEdge V β ≤ G ↔ V ⊆ V(G) := by
  simp [le_iff]

@[simp]
lemma noEdge_not_inc {V : Set α} : ¬ (Graph.noEdge V β).Inc e x := by
  simp [Inc]

@[simp]
lemma noEdge_not_isLoopAt {V : Set α} : ¬ (Graph.noEdge V β).IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma noEdge_not_isNonloopAt {V : Set α} : ¬ (Graph.noEdge V β).IsNonloopAt e x := by
  simp [IsNonloopAt]

@[simp]
lemma noEdge_not_adj {V : Set α} : ¬ (Graph.noEdge V β).Adj x y := by
  simp [Adj]

lemma edgeDelete_eq_noEdge (G : Graph α β) (hF : E(G) ⊆ F) : G ＼ F = Graph.noEdge V(G) β := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [edgeDelete_isLink, noEdge_isLink, iff_false, not_and, not_not]
  exact fun h ↦ hF h.edge_mem

lemma edgeSet_eq_empty_iff : E(G) = ∅ ↔ G = Graph.noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext rfl ?_, fun h ↦ by rw [h, noEdge_edgeSet]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this


/-- A graph with a single edge `e` from `u` to `v` -/
@[simps]
protected def singleEdge (u v : α) (e : β) : Graph α β where
  vertexSet := {u,v}
  edgeSet := {e}
  IsLink e' x y := e' = e ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by tauto
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by tauto
  left_mem_of_isLink := by tauto

lemma singleEdge_comm (u v : α) (e : β) : Graph.singleEdge u v e = Graph.singleEdge v u e := by
  ext <;> simp [or_comm]

lemma singleEdge_isLink_iff :
    (Graph.singleEdge u v e).IsLink f x y ↔ (f = e) ∧ s(x,y) = s(u,v) := by
  simp [Graph.singleEdge]

@[simp]
lemma singleEdge_inc_iff :
    (Graph.singleEdge u v e).Inc f x ↔ f = e ∧ (x = u ∨ x = v) := by
  simp only [Inc, singleEdge_isLink, exists_and_left, and_congr_right_iff]
  aesop

@[simp]
lemma singleEdge_adj_iff :
    (Graph.singleEdge u v e).Adj x y ↔ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  simp [Adj]

@[simp]
lemma singleEdge_le_iff : Graph.singleEdge u v e ≤ G ↔ G.IsLink e u v := by
  simp only [le_iff, singleEdge_vertexSet, Set.pair_subset_iff, singleEdge_isLink_iff, and_imp,
    Sym2.eq_iff]
  refine ⟨fun h ↦ h.2 rfl (.inl ⟨rfl, rfl⟩), fun h ↦ ⟨⟨h.left_mem, h.right_mem⟩, ?_⟩⟩
  rintro e x y rfl (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm


@[simp]
lemma singleEdge_compatible_iff :
    Compatible (Graph.singleEdge u v e) G ↔ (e ∈ E(G) → G.IsLink e u v) := by
  refine ⟨fun h he ↦ by simp [← h ⟨by simp, he⟩], fun h f ⟨hfe, hf⟩ ↦ ?_⟩
  obtain rfl : f = e := by simpa using hfe
  ext x y
  simp only [singleEdge_isLink, (h hf).isLink_iff]
  tauto

/-! ### Adding one edge -/

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
@[simps! edgeSet vertexSet]
protected def addEdge (G : Graph α β) (e : β) (a b : α) : Graph α β :=
  Graph.singleEdge a b e ∪ G

lemma addEdge_isLink (G : Graph α β) (e : β) (a b : α) : (G.addEdge e a b).IsLink e a b := by
  simp [Graph.addEdge, union_isLink_iff]

lemma addEdge_isLink_of_ne (hf : G.IsLink f x y) (hne : f ≠ e) (a b : α) :
    (G.addEdge e a b).IsLink f x y := by
  simpa [Graph.addEdge, union_isLink_iff, hne]

lemma addEdge_isLink_iff {a b : α} (he : e ∉ E(G)) :
    (G.addEdge e a b).IsLink f x y ↔ (f = e ∧ s(a,b) = s(x,y)) ∨ G.IsLink f x y := by
  have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
  simp only [Graph.addEdge, union_isLink_iff, singleEdge_isLink, singleEdge_edgeSet,
    mem_singleton_iff, edgeDelete_isLink, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  obtain rfl | hne := eq_or_ne e f
  · have hl : ¬ G.IsLink e x y := fun h ↦ he h.edge_mem
    simp only [true_and, not_true_eq_false, hl, and_self, or_false]
    tauto
  simp [hne.symm]

lemma addEdge_deleteEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (G.addEdge e x y) ＼ {e} = G := by
  have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
  simp only [Graph.addEdge, Graph.ext_iff, edgeDelete_vertexSet, union_vertexSet,
    singleEdge_vertexSet, union_eq_right, insert_subset_iff, hx, singleton_subset_iff, hy, and_self,
    edgeDelete_isLink, hc.union_isLink_iff, singleEdge_isLink, mem_singleton_iff, true_and]
  intro f p q
  obtain rfl | hne := eq_or_ne f e
  · suffices ¬ G.IsLink f p q by simpa
    exact fun hf ↦ he hf.edge_mem
  simp [hne]

lemma addEdge_le (hle : H ≤ G) (he : G.IsLink e x y) : H.addEdge e x y ≤ G where
  vertex_subset := union_subset (by simp [pair_subset_iff, he.left_mem, he.right_mem])
    (vertexSet_mono hle)
  isLink_of_isLink f z w hH := by
    simp only [Graph.addEdge, union_isLink_iff, singleEdge_isLink, singleEdge_edgeSet,
      mem_singleton_iff] at hH
    obtain (⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩) | ⟨-, hzw⟩ := hH
    · exact he
    · exact he.symm
    exact hzw.of_le hle

lemma le_addEdge (he : e ∉ E(G)) : G ≤ G.addEdge e x y :=
  Compatible.right_le_union <| by simp [he]

lemma IsLink.deleteEdge_addEdge (h : G.IsLink e x y) : (G ＼ {e}).addEdge e x y = G :=
  ext_of_le_le (addEdge_le (by simp) h) le_rfl (by simp [pair_subset_iff, h.left_mem, h.right_mem])
    <| by simp [h.edge_mem]



/-! ### Families of Graphs -/

variable {ι : Type*} {H : ι → Graph α β} {s : Set (Graph α β)}

/-- An indexed family of graphs is `UCompatible` if no two of them disagree on incidences,
or equivalently if there is a common supergraph of all the graphs in the family.
TODO : Change this to `Pairwise (Compatible on H)`.
  -/
def UCompatible (H : ι → Graph α β) : Prop :=
  ∀ ⦃i j e x y⦄, (H i).IsLink e x y → e ∈ E(H j) → (H j).IsLink e x y

lemma uCompatible_iff_pairwise_compatible : UCompatible H ↔ Pairwise (Compatible on H) := by
  refine ⟨fun h i j hne e ⟨hei, hej⟩ ↦ ?_, fun h i j e x y hei hej ↦ ?_⟩
  · ext x y
    exact ⟨fun h' ↦ h h' hej, fun h' ↦ h h' hei⟩
  obtain rfl | hne := eq_or_ne i j
  · assumption
  rwa [(h hne).symm hej hei.edge_mem]

lemma UCompatible.of_forall_subgraph (h : ∀ i, H i ≤ G) : UCompatible H :=
  fun i j _ _ _ hi hj ↦ (hi.of_le (h i)).of_le_of_mem (h j) hj

lemma Compatible.UCompatible_cond {H : Graph α β} (h : G.Compatible H) :
    UCompatible (fun b : Bool ↦ bif b then G else H) := by
  rwa [uCompatible_iff_pairwise_compatible, pairwise_on_bool]
  exact fun _ _ h ↦ h.symm

lemma UCompatible.of_disjoint_edgeSet (h : Pairwise (Disjoint on (fun i ↦ E(H i)))) :
    UCompatible H := by
  refine fun i j e x y hi hj ↦ ?_
  obtain rfl | hne := eq_or_ne i j
  · assumption
  exact False.elim <| (disjoint_left.1 <| h hne) hi.edge_mem hj

lemma UCompatible.of_disjoint (h : Pairwise (Graph.Disjoint on H)) : UCompatible H :=
  UCompatible.of_disjoint_edgeSet <| h.mono fun _ _ ↦ Graph.Disjoint.edge

/-- The union of a `UCompatible` collection of graphs. -/
@[simps]
protected def UCompatible.iUnion (H : ι → Graph α β) (hH : UCompatible H) : Graph α β where
  vertexSet := ⋃ i, V(H i)
  edgeSet := ⋃ i, E(H i)
  IsLink e x y := ∃ i, (H i).IsLink e x y
  isLink_symm := by
    simp only [mem_iUnion, Symmetric, forall_exists_index]
    rintro e i hei x y j hi
    exact ⟨j, hi.symm⟩
  eq_or_eq_of_isLink_of_isLink :=
    fun e x y v w ⟨i, hexy⟩ ⟨j, hevw⟩ ↦ (hH hexy hevw.edge_mem).left_eq_or_eq hevw
  edge_mem_iff_exists_isLink := by
    simp_rw [mem_iUnion]
    refine fun e ↦ ⟨fun ⟨i, hei⟩ ↦ ?_, fun ⟨x, y, i, h⟩ ↦ ⟨i, h.edge_mem⟩⟩
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet hei
    exact ⟨_, _, _, h⟩
  left_mem_of_isLink := fun e x y ⟨i, h⟩ ↦ mem_iUnion.2 ⟨i, h.left_mem⟩

lemma UCompatible.le_iUnion (hH : UCompatible H) (i : ι) : H i ≤ hH.iUnion H :=
  ⟨subset_iUnion (fun i ↦ V(H i)) i , by aesop⟩

@[simp]
lemma UCompatible.iUnion_le_iff (hH : UCompatible H) : hH.iUnion H ≤ G ↔ ∀ i, H i ≤ G := by
  refine ⟨fun h i ↦ (hH.le_iUnion i).trans h, fun h ↦ ⟨?_, fun e x y ⟨i, hexy⟩ ↦ hexy.of_le (h i)⟩⟩
  simpa using fun i ↦ vertexSet_mono (h i)

lemma Compatible.union_eq_iUnion {H : Graph α β} (h : G.Compatible H) :
    G ∪ H = h.UCompatible_cond.iUnion _ := by
  refine Graph.ext ?_ fun e x y ↦ ?_
  · simp only [union_vertexSet, UCompatible.iUnion_vertexSet, Bool.apply_cond]
    rw [← Set.union_eq_iUnion]
  simp [h.union_isLink_iff, or_comm]

@[simps!]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β :=
  UCompatible.iUnion (fun G : s ↦ G.1) <|
    uCompatible_iff_pairwise_compatible.2 <| (pairwise_subtype_iff_pairwise_set s Compatible).2 hs

protected lemma le_sUnion (hs : s.Pairwise Compatible) (hG : G ∈ s) : G ≤ Graph.sUnion s hs :=
  UCompatible.le_iUnion (H := Subtype.val) (i := ⟨G, hG⟩) _

@[simp]
protected lemma sUnion_le_iff (hs : s.Pairwise Compatible) :
    Graph.sUnion s hs ≤ G ↔ ∀ H ∈ s, H ≤ G := by
  convert UCompatible.iUnion_le_iff (H := fun i : s ↦ i.1) (G := G) _
  simp

lemma isClosedSubgraph_sUnion_of_disjoint (s : Set (Graph α β)) (hs : s.Pairwise Graph.Disjoint)
    (hG : G ∈ s) : G ≤c Graph.sUnion s (hs.mono' (by simp)) where
  le :=  Graph.le_sUnion _ hG
  closed e x he hx := by
    simp only [Inc, Graph.sUnion, UCompatible.iUnion_isLink, Subtype.exists, exists_prop] at he
    obtain ⟨y, G', hGs, hexy⟩ := he
    obtain rfl | hne := eq_or_ne G' G
    · exact hexy.edge_mem
    exact False.elim <| (hs hG hGs hne.symm).vertex.not_mem_of_mem_left hx hexy.left_mem
