import Matroid.Graph.Subgraph
import Matroid.Graph.Finite
import Matroid.Graph.Degree
import Mathlib.Data.Set.Insert
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic

open Set Function Nat

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

open WList Graph

lemma Set.Subsingleton.elim {s : Set α} (hs : s.Subsingleton) (hxs : x ∈ s) (hys : y ∈ s) :
    x = y := by
  obtain rfl | ⟨a, rfl⟩ := hs.eq_empty_or_singleton <;> simp_all


namespace Graph

/-- `G.VertexConnected v w` means that `G` contains a walk from `v` to `w`. -/
def VertexConnected (G : Graph α β) : α → α → Prop :=
    Relation.TransGen (fun x y ↦ G.Adj x y ∨ (x = y ∧ x ∈ V(G)))

lemma VertexConnected.refl (h : v ∈ V(G)) : G.VertexConnected v v := by
  rw [VertexConnected, Relation.transGen_iff]
  simp [h]

lemma VertexConnected.trans (hxy : G.VertexConnected x y) (hyz : G.VertexConnected y z) :
    G.VertexConnected x z :=
  Relation.TransGen.trans hxy hyz

lemma VertexConnected.symm (hxy : G.VertexConnected x y) : G.VertexConnected y x := by
  rw [VertexConnected, Relation.transGen_swap]
  rw [VertexConnected] at hxy
  convert hxy using 4 with x y
  · rw [adj_comm]
  aesop

lemma VertexConnected.left_mem (hxy : G.VertexConnected x y) : x ∈ V(G) := by
  induction hxy with
  | single h => exact h.elim Adj.left_mem And.right
  | tail _ _ h => exact h

lemma VertexConnected.right_mem (hxy : G.VertexConnected x y) : y ∈ V(G) :=
  hxy.symm.left_mem

@[simp]
lemma vertexConnected_self : G.VertexConnected x x ↔ x ∈ V(G) :=
  ⟨VertexConnected.left_mem, VertexConnected.refl⟩

lemma Adj.vertexConnected (h : G.Adj x y) : G.VertexConnected x y := by
  rw [VertexConnected, Relation.transGen_iff]
  simp [h]

lemma IsLink.vertexConnected (h : G.IsLink e x y) : G.VertexConnected x y :=
  h.adj.vertexConnected

lemma IsWalk.vertexConnected_of_mem_of_mem (hW : G.IsWalk W) (hx : x ∈ W) (hy : y ∈ W) :
    G.VertexConnected x y := by
  suffices aux : ∀ ⦃z⦄, z ∈ W → G.VertexConnected z W.last from (aux hx).trans (aux hy).symm
  clear hx hy
  intro z hz
  induction hW generalizing z with
  | nil => simp_all
  | cons hW h ih =>
    obtain rfl | hz := by simpa using hz
    · exact h.vertexConnected.trans <| by simpa only [last_cons] using ih <| by simp
    simpa using ih hz

lemma IsWalk.vertexConnected_first_last (hW : G.IsWalk W) : G.VertexConnected W.first W.last :=
  hW.vertexConnected_of_mem_of_mem (by simp) <| by simp

lemma VertexConnected.exists_isWalk (h : G.VertexConnected x y) :
    ∃ W, G.IsWalk W ∧ W.first = x ∧ W.last = y := by
  rw [VertexConnected] at h
  induction h using Relation.TransGen.head_induction_on with
  | @base a h =>
    obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h
    · exact ⟨he.walk, by simp⟩
    exact ⟨.nil a, by simp [h]⟩
  | @ih u v h₁ h₂ h₃ =>
    obtain ⟨W, hW, rfl, rfl⟩ := h₃
    obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h₁
    · exact ⟨.cons u e W, by simp [he, hW]⟩
    exact ⟨W, hW, rfl, rfl⟩

lemma vertexConnected_iff_exists_walk :
    G.VertexConnected x y ↔ ∃ W, G.IsWalk W ∧ W.first = x ∧ W.last = y := by
  refine ⟨VertexConnected.exists_isWalk, ?_⟩
  rintro ⟨W, hW, rfl, rfl⟩
  exact hW.vertexConnected_first_last

lemma VertexConnected.exists_isPath (h : G.VertexConnected x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y := by
  classical
  obtain ⟨W, hW, rfl, rfl⟩ := h.exists_isWalk
  exact ⟨W.dedup, by simp [hW.dedup_isPath]⟩

lemma VertexConnected.of_le (h : H.VertexConnected x y) (hle : H ≤ G) : G.VertexConnected x y := by
  obtain ⟨W, hW, rfl, rfl⟩ := h.exists_isWalk
  exact (hW.of_le hle).vertexConnected_first_last

lemma vertexConnected_induce_iff {X : Set α} (hx : x ∈ V(G)) :
    G[X].VertexConnected x y ↔ ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ V(P) ⊆ X := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
    refine ⟨P, ?_, rfl, rfl, hP.vertexSet_subset⟩
    cases P with
    | nil => simpa
    | cons u e W =>
      rw [isPath_induce_iff' (by simp)] at hP
      exact hP.1
  rintro ⟨P, h, rfl, rfl, hPX⟩
  cases P with
  | nil => simpa using hPX
  | cons u e W =>
    apply IsWalk.vertexConnected_first_last
    rw [isWalk_induce_iff' (by simp)]
    simp_all only [cons_isPath_iff, first_cons, cons_vertexSet, cons_isWalk_iff, true_and, and_true]
    exact h.1.isWalk

/-- A graph is `Connected` if it is nonempty, and every pair of vertices is `VertexConnected`. -/
@[mk_iff]
structure Connected (G : Graph α β) : Prop where
  nonempty : V(G).Nonempty
  vertexConnected : ∀ ⦃x y⦄, x ∈ V(G) → y ∈ V(G) → G.VertexConnected x y

/-- If `G` has one vertex connected to all others, then `G` is connected. -/
lemma connected_of_vertex (hu : u ∈ V(G)) (h : ∀ y ∈ V(G), G.VertexConnected y u) : G.Connected :=
  ⟨⟨u, hu⟩, fun x y hx hy ↦ (h x hx).trans (h y hy).symm⟩

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : V(G).Nonempty) :
    ∃ X ⊂ V(G), X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp,
    exists_prop, exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.VertexConnected x z}, ?_, ⟨x, by simpa⟩,
    fun u v (h : G.VertexConnected x u) huv ↦ ?_⟩
  · exact HasSubset.Subset.ssubset_of_mem_not_mem
      (fun z hz ↦ VertexConnected.right_mem hz) hy (by simpa)
  exact h.trans huv.vertexConnected

lemma connected_iff_forall_exists_adj (hne : V(G).Nonempty) :
    G.Connected ↔ ∀ X ⊂ V(G), X.Nonempty → ∃ x ∈ X, ∃ y ∈ V(G) \ X, G.Adj x y := by
  refine ⟨fun h X hXV ⟨x, hxV⟩ ↦ ?_, fun h ↦ by_contra fun hnc ↦ ?_⟩
  · obtain ⟨y', hy'V, hy'X⟩ := exists_of_ssubset hXV
    obtain ⟨W, hW, rfl, rfl⟩ := (h.vertexConnected (hXV.subset hxV) hy'V).exists_isWalk
    obtain ⟨e, x₁, y₁, h, hx₁, hy₁⟩ := exists_dInc_prop_not_prop hxV hy'X
    exact ⟨x₁, hx₁, y₁, ⟨hW.vertex_mem_of_mem h.right_mem, hy₁⟩, (hW.isLink_of_dInc h).adj⟩
  obtain ⟨X, hXV, hXne, h'⟩ := exists_of_not_connected hnc hne
  obtain ⟨x, hX, y, hy, hxy⟩ := h X hXV hXne
  exact hy.2 <| h' hX hxy

/-- A `WList` that is `WellFormed` produces a connected graph. -/
lemma _root_.WList.WellFormed.toGraph_connected (hW : W.WellFormed) : W.toGraph.Connected :=
  ⟨by simp, fun x y hx hy ↦
    hW.isWalk_toGraph.vertexConnected_of_mem_of_mem (by simpa using hx) (by simpa using hy)⟩

lemma IsWalk.toGraph_connected (hW : G.IsWalk W) : W.toGraph.Connected :=
  hW.wellFormed.toGraph_connected

lemma singleVertex_connected (hG : V(G) = {x}) : G.Connected := by
  simp [connected_iff, hG]

@[simp]
lemma singleEdge_connected (e : β) (x y : α) : (Graph.singleEdge x y e).Connected := by
  refine connected_of_vertex (u := x) (by simp) ?_
  simp only [singleEdge_vertexSet, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
    vertexConnected_self, true_or, forall_eq, true_and]
  exact Adj.vertexConnected <| by simp [Adj]

lemma Connected.exists_vertexConnected_deleteEdge_set {X : Set α} (hG : G.Connected)
    (hX : (X ∩ V(G)).Nonempty) (hu : u ∈ V(G)) : ∃ x ∈ X, (G ＼ E(G[X])).VertexConnected u x := by
  obtain ⟨x', hx'X, hx'V⟩ := hX
  obtain ⟨W, hW, hu, rfl⟩ := (hG.vertexConnected hu hx'V).exists_isWalk
  induction hW generalizing u with
  | nil => exact ⟨_, hx'X, by simp_all⟩
  | @cons x e W hW h ih =>
    obtain rfl : x = u := hu
    by_cases hmem : e ∈ E(G ＼ E(G[X]))
    · obtain ⟨x', hx', hWx'⟩ := ih (u := W.first) (hW.vertex_mem_of_mem (by simp)) rfl
        (by simpa using hx'X) (by simpa using hx'V)
      have hconn := (h.of_le_of_mem edgeDelete_le hmem).vertexConnected
      exact ⟨x', hx', hconn.trans hWx'⟩
    rw [edgeDelete_edgeSet, mem_diff, and_iff_right h.edge_mem, h.mem_induce_iff, not_not] at hmem
    exact ⟨x, hmem.1, by simpa⟩

lemma Connected.exists_isPathFrom (hG : G.Connected) (hS : (S ∩ V(G)).Nonempty)
    (hT : (T ∩ V(G)).Nonempty) : ∃ P, G.IsPathFrom S T P := by
  obtain ⟨x, hxS, hx⟩ := hS
  obtain ⟨y, hyT, hy⟩ := hT
  obtain ⟨W, hW, rfl, rfl⟩ := (hG.vertexConnected hx hy).exists_isWalk
  clear hx hy
  induction hW generalizing S with
  | @nil x hx => exact ⟨nil x, by simp_all⟩
  | @cons x e P hP h ih =>
    simp_all only [cons_vertex, List.nodup_cons, mem_vertex, first_cons, last_cons, forall_const]
    by_cases hPS : P.first ∈ S
    · apply ih hPS
    obtain ⟨P₀, hP₀⟩ := ih (mem_insert P.first S)
    obtain (hP₀S | h_eq) := hP₀.first_mem.symm
    · exact ⟨P₀, hP₀.subset_left (by simp) hP₀S⟩
    by_cases hxT : x ∈ T
    · exact ⟨nil x, by simp [hxS, hxT, h.left_mem]⟩
    use cons x e P₀
    simp only [isPathFrom_iff, cons_isPath_iff, first_cons, last_cons]
    refine ⟨⟨hP₀.isPath, by rwa [h_eq], fun hxP₀ ↦ hPS ?_⟩, hxS, hP₀.last_mem, ?_, ?_⟩
    · rwa [← h_eq, ← hP₀.eq_first_of_mem hxP₀ (by simp [hxS])]
    · simp only [mem_cons_iff, forall_eq_or_imp, implies_true, true_and]
      exact fun a haP haS ↦ hPS.elim <| by rwa [← h_eq, ← hP₀.eq_first_of_mem haP (by simp [haS])]
    simp only [mem_cons_iff, forall_eq_or_imp, hxT, IsEmpty.forall_iff, true_and]
    exact fun a haP₀ haT ↦ hP₀.eq_last_of_mem haP₀ haT

lemma Connected.exists_vertexConnected_deleteEdge_set_set (hG : G.Connected)
    (hS : (S ∩ V(G)).Nonempty) (hT : (T ∩ V(G)).Nonempty) :
    ∃ x ∈ S, ∃ y ∈ T, (G ＼ (E(G[S]) ∪ E(G[T]))).VertexConnected x y := by
  obtain ⟨P, hP⟩ := hG.exists_isPathFrom hS hT
  have h0 : P.first ∈ V(G ＼ (E(G[S]) ∪ E(G[T]))) := by
    simpa using hP.isWalk.vertex_mem_of_mem (by simp)
  refine ⟨_, hP.first_mem, _, hP.last_mem,
    (hP.isPathFrom_le (by simp) (fun e heP ↦ ?_) h0).isWalk.vertexConnected_first_last⟩
  obtain ⟨x, y, hxy⟩ := exists_dInc_of_mem_edge heP
  have hxy' := hP.isWalk.isLink_of_dInc hxy
  rw [edgeDelete_edgeSet, mem_diff, mem_union, hxy'.mem_induce_iff,
    hxy'.mem_induce_iff, and_iff_right hxy'.edge_mem]
  simp [hP.not_mem_left_of_dInc hxy, hP.not_mem_right_of_dInc hxy]

lemma Connected.exists_adj_of_mem (hG : G.Connected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)) :
    ∃ y ≠ x, G.Adj x y := by
  obtain ⟨z, hz, hne⟩ := hV.exists_ne x
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vertexConnected hx hz).exists_isPath
  rw [ne_comm, first_ne_last_iff hP.nodup] at hne
  cases hne with | cons x e P =>
  simp only [cons_isPath_iff] at hP
  exact ⟨P.first, mt (by simp +contextual [eq_comm]) hP.2.2, hP.2.1.adj⟩

lemma Connected.of_isSpanningSubgraph (h : H ≤s G) (hH : H.Connected) : G.Connected :=
  ⟨h.vertexSet_eq ▸ hH.nonempty,
    fun _ _ hx hy ↦ (hH.vertexConnected (h.vertexSet_eq ▸ hx) (h.vertexSet_eq ▸ hy)).of_le h.le ⟩

/- ### Separations -/

/-- A partition of `G.V` into two parts with no edge between them. -/
structure Separation (G : Graph α β) where
  left : Set α
  right : Set α
  nonempty_left : left.Nonempty
  nonempty_right : right.Nonempty
  disjoint : Disjoint left right
  union_eq : left ∪ right = V(G)
  not_adj : ∀ ⦃x y⦄, x ∈ left → y ∈ right → ¬ G.Adj x y

lemma Separation.left_subset (S : G.Separation) : S.left ⊆ V(G) := by
  simp [← S.union_eq]

lemma Separation.right_subset (S : G.Separation) : S.right ⊆ V(G) := by
  simp [← S.union_eq]

@[simps]
def Separation.symm (S : G.Separation) : G.Separation where
  left := S.right
  right := S.left
  nonempty_left := S.nonempty_right
  nonempty_right := S.nonempty_left
  disjoint := S.disjoint.symm
  union_eq := by rw [← S.union_eq, union_comm]
  not_adj x y hx hy := by simpa [adj_comm] using S.not_adj hy hx

lemma Separation.not_left_mem_iff (S : G.Separation) (hxV : x ∈ V(G)) :
    x ∉ S.left ↔ x ∈ S.right := by
  rw [← S.union_eq, mem_union] at hxV
  have := S.disjoint.not_mem_of_mem_left (a := x)
  tauto

lemma Separation.not_right_mem_iff (S : G.Separation) (hxV : x ∈ V(G)) :
    x ∉ S.right ↔ x ∈ S.left := by
  simpa using S.symm.not_left_mem_iff hxV

lemma Separation.left_mem_of_adj {S : G.Separation} (hx : x ∈ S.left) (hxy : G.Adj x y) :
    y ∈ S.left := by
  rw [← S.not_right_mem_iff hxy.right_mem]
  exact fun hy ↦ S.not_adj hx hy hxy

lemma Separation.right_mem_of_adj {S : G.Separation} (hx : x ∈ S.right) (hxy : G.Adj x y) :
    y ∈ S.right :=
  S.symm.left_mem_of_adj hx (y := y) hxy

lemma Separation.mem_or_mem (S : G.Separation) (hxV : x ∈ V(G)) : x ∈ S.left ∨ x ∈ S.right := by
  rwa [← mem_union, S.union_eq]

lemma Separation.not_vertexConnected (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.VertexConnected x y := by
  intro h
  obtain ⟨W, hW, rfl, rfl⟩ := h.exists_isWalk
  rw [← S.not_left_mem_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.left_mem_of_adj hx (hW.isLink_of_dInc hinc).adj

lemma Separation.not_connected (S : G.Separation) : ¬ G.Connected := by
  obtain ⟨x, hx⟩ := S.nonempty_left
  obtain ⟨y, hy⟩ := S.nonempty_right
  exact fun h ↦ S.not_vertexConnected hx hy <| h.vertexConnected (S.left_subset hx)
    (S.right_subset hy)

lemma Connected.isEmpty_separation (hG : G.Connected) : IsEmpty G.Separation :=
  isEmpty_iff.2 fun S ↦ S.not_connected hG

lemma exists_separation_of_not_vertexConnected (hxV : x ∈ V(G)) (hyV : y ∈ V(G))
    (hxy : ¬ G.VertexConnected x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ V(G) | G.VertexConnected x w}, {w ∈ V(G) | ¬ G.VertexConnected x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.vertexConnected⟩, by simp_all⟩

lemma nonempty_separation_of_not_connected (hne : V(G).Nonempty) (hG : ¬ G.Connected) :
    Nonempty G.Separation := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp, exists_and_left] at hG
  obtain ⟨x, y, hx, hy, hxy⟩ := hG
  exact ⟨(exists_separation_of_not_vertexConnected hx hy hxy).choose⟩


/-- If `G` is connected but its restriction to some set `F` of edges is not,
then there is an edge of `G` joining two vertices that are not connected in the restriction. -/
lemma Connected.exists_of_edgeRestrict_not_connected (hG : G.Connected)
    (hF : ¬ (G.edgeRestrict F).Connected) :
    ∃ (S : (G.edgeRestrict F).Separation) (e : β) (x : α) (y : α),
    e ∉ F ∧ x ∈ S.left ∧ y ∈ S.right ∧ G.IsLink e x y := by
  obtain ⟨S⟩ := nonempty_separation_of_not_connected (by simpa using hG.nonempty) hF
  obtain ⟨x₀, hx₀⟩ := S.nonempty_left
  obtain ⟨y₀, hy₀⟩ := S.nonempty_right
  obtain ⟨W, hW, rfl, rfl⟩ :=
    (hG.vertexConnected (S.left_subset hx₀) (S.right_subset hy₀)).exists_isWalk
  rw [← S.not_left_mem_iff (S.right_subset hy₀)] at hy₀
  obtain ⟨e, x, y, hexy, hx, hy⟩ := W.exists_dInc_prop_not_prop hx₀ hy₀
  have h' := hW.isLink_of_dInc hexy
  rw [S.not_left_mem_iff h'.right_mem] at hy
  refine ⟨S, e, x, y, fun heF ↦ ?_, hx, hy, h'⟩
  exact S.not_adj hx hy <| IsLink.adj <| h'.of_le_of_mem (by simp) <| by simpa [h'.edge_mem]

lemma Connected.of_subgraph (hH : H.Connected) (hle : H ≤ G) (hV : V(H) = V(G)) : G.Connected := by
  obtain ⟨x, hx⟩ := hH.nonempty
  refine connected_of_vertex (vertexSet_subset_of_le hle hx) fun y hy ↦ ?_
  exact (hH.vertexConnected (y := x) (by rwa [hV]) hx).of_le hle

lemma Separation.edge_induce_disjoint (S : G.Separation) : Disjoint E(G[S.left]) E(G[S.right]) := by
  refine disjoint_left.2 fun e he he' ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq] at he he'
  obtain ⟨x, y, hexy, hx, hy⟩ := he
  obtain ⟨x', y', hexy', hx', hy'⟩ := he'
  obtain rfl | rfl := hexy.left_eq_or_eq hexy'
  · exact S.disjoint.not_mem_of_mem_left hx hx'
  exact S.disjoint.not_mem_of_mem_left hx hy'

lemma Separation.eq_union (S : G.Separation) : G = G [S.left] ∪ G [S.right] := by
  refine Graph.ext (by simp [S.union_eq]) fun e x y ↦ ?_
  simp only [(Compatible.of_disjoint_edgeSet S.edge_induce_disjoint).union_isLink_iff,
    induce_isLink_iff, ← and_or_left, iff_self_and]
  exact fun h ↦ (S.mem_or_mem h.left_mem).elim
    (.inl ∘ fun h' ↦ ⟨h', S.left_mem_of_adj h' h.adj⟩)
    (.inr ∘ fun h' ↦ ⟨h', S.right_mem_of_adj h' h.adj⟩)

/- ### Unions -/

lemma Compatible.union_connected_of_forall (h : G.Compatible H) (hG : G.Connected)
    (hH : ∀ x ∈ V(H), ∃ y ∈ V(G), H.VertexConnected x y) : (G ∪ H).Connected := by
  obtain ⟨v, hv⟩ := hG.nonempty
  refine connected_of_vertex (u := v) (by simp [hv]) ?_
  rintro y (hy | hy)
  · exact (hG.vertexConnected hy hv).of_le <| left_le_union ..
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.of_le h.right_le_union).trans <| (hG.vertexConnected hzG hv).of_le <| left_le_union ..

lemma Compatible.union_connected_of_nonempty_inter (h : Compatible G H) (hG : G.Connected)
    (hH : H.Connected) (hne : (V(G) ∩ V(H)).Nonempty) : (G ∪ H).Connected :=
  let ⟨z, hzG, hzH⟩ := hne
  h.union_connected_of_forall hG fun _ hx ↦ ⟨z, hzG, hH.vertexConnected hx hzH⟩

lemma IsWalk.exists_mem_mem_of_union (h : (G ∪ H).IsWalk W) (hG : W.first ∈ V(G))
    (hH : W.last ∈ V(H)) : ∃ x ∈ W, x ∈ V(G) ∧ x ∈ V(H) := by
  by_cases hH' : W.last ∈ V(G)
  · exact ⟨W.last, by simp, hH', hH⟩
  obtain ⟨e, x, y, hxy, hx, hy⟩ := W.exists_dInc_prop_not_prop hG hH'
  obtain hxy' | hxy' := isLink_or_isLink_of_union <| h.isLink_of_dInc hxy
  · exact False.elim <| hy <| hxy'.right_mem
  exact ⟨x, hxy.left_mem, hx, hxy'.left_mem⟩

lemma union_not_connected_of_disjoint_vertexSet (hV : Disjoint V(G) V(H)) (hG : V(G).Nonempty)
    (hH : V(H).Nonempty) : ¬ (G ∪ H).Connected := by
  obtain ⟨x, hx⟩ := hG
  obtain ⟨y, hy⟩ := hH
  intro h
  obtain ⟨W, hW, rfl, rfl⟩ :=
    (h.vertexConnected (x := x) (y := y) (by simp [hx]) (by simp [hy])).exists_isWalk
  obtain ⟨u, -, huG, huH⟩ := hW.exists_mem_mem_of_union hx hy
  exact hV.not_mem_of_mem_left huG huH

/-! ### Cycles -/

/-- Two vertices of a cycle are connected after deleting any other vertex.  -/
lemma IsCycle.vertexConnected_deleteVertex_of_mem_of_mem (hC : G.IsCycle C) (x : α) (hy₁ : y₁ ∈ C)
    (hy₂ : y₂ ∈ C) (hne₁ : y₁ ≠ x) (hne₂ : y₂ ≠ x) : (G - ({x} : Set α)).VertexConnected y₁ y₂ := by
  obtain rfl | hne := eq_or_ne y₁ y₂
  · simpa [hC.vertexSet_subset hy₁]
  obtain ⟨u, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · simp_all
  by_cases hxC : x ∈ C
  · obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vertex hnt hxC
    refine IsWalk.vertexConnected_of_mem_of_mem (W := P) ?_ ?_ ?_
    · simp [hP.isWalk, ← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq]
    all_goals simp_all [← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq]
  exact IsWalk.vertexConnected_of_mem_of_mem (W := C) (by simp [hxC, hC.isWalk]) hy₁ hy₂

 /-- Two vertices of a cycle are connected after deleting any edge. -/
lemma IsCycle.vertexConnected_deleteEdge_of_mem_of_mem (hC : G.IsCycle C) (e : β)
    (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) : (G ＼ {e}).VertexConnected x₁ x₂ := by
  obtain heC | heC := em' <| e ∈ C.edge
  · exact IsWalk.vertexConnected_of_mem_of_mem (by simp [hC.isWalk, heC]) hx₁ hx₂
  obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  apply IsWalk.vertexConnected_of_mem_of_mem (W := P)
    (by simp [hP.isWalk, ← toGraph_edgeSet, hP_eq])
  all_goals rwa [← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq, edgeDelete_vertexSet,
    toGraph_vertexSet, mem_vertexSet_iff]

/-- If two graphs intersect in at most one vertex,
then any cycle of their union is a cycle of one of the graphs. -/
lemma IsCycle.isCycle_or_isCycle_of_union_of_subsingleton_inter (hC : (G ∪ H).IsCycle C)
    (hi : (V(G) ∩ V(H)).Subsingleton) : G.IsCycle C ∨ H.IsCycle C := by
  wlog hcompat : Compatible G H generalizing H with aux
  · obtain (hG | hH) := aux (union_eq_union_edgeDelete .. ▸ hC) (hi.anti (by simp))
      (Compatible.of_disjoint_edgeSet disjoint_sdiff_right)
    · exact .inl hG
    exact .inr <| hH.isCycle_of_ge <| by simp
  -- If the cycle is a loop, this is easy.
  obtain ⟨x, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · obtain heG | heH := hC.isWalk.edge_mem_of_mem (e := e) (by simp)
    · exact .inl <| hC.isCycle_of_le (left_le_union ..) (by simpa)
    exact .inr <| hC.isCycle_of_le hcompat.right_le_union (by simpa)
  -- Every edge of `C` has distinct ends in `G` or in `H`.
  have aux1 (e) (he : e ∈ E(C)) :
      ∃ x y, x ≠ y ∧ x ∈ V(C) ∧ y ∈ V(C) ∧ (G.IsLink e x y ∨ H.IsLink e x y) := by
    obtain ⟨x, y, hxy⟩ := C.exists_isLink_of_mem_edge he
    exact ⟨x, y, hC.ne_of_isLink hnt hxy, hxy.left_mem, hxy.right_mem,
      by simpa [hcompat.union_isLink_iff] using hC.isWalk.isLink_of_isLink hxy ⟩
  -- If the vertices of `C` are contained in `G` or `H`, then `C` is contained in `G` or `H`.
  by_cases hCG : V(C) ⊆ V(G)
  · refine .inl <| hC.isCycle_of_le (left_le_union ..) fun e heC ↦ ?_
    obtain ⟨x, y, hne, hxC, hyC, hxy | hxy⟩ := aux1 e heC
    · exact hxy.edge_mem
    exact False.elim <| hne <| hi.elim ⟨hCG hxC, hxy.left_mem⟩ ⟨hCG hyC, hxy.right_mem⟩
  by_cases hCH : V(C) ⊆ V(H)
  · refine .inr <| hC.isCycle_of_le hcompat.right_le_union fun e heC ↦ ?_
    obtain ⟨x, y, hne, hxC, hyC, hxy | hxy⟩ := aux1 e heC
    · exact False.elim <| hne <| hi.elim ⟨hxy.left_mem, hCH hxC⟩ ⟨hxy.right_mem, hCH hyC⟩
    exact hxy.edge_mem
  -- Take a path from a vertex `x` of `C ∩ (G \ H)` to a vertex `y` of `C ∩ (H \ G)`.
  -- This path must intersect `V(G) ∩ V(H)` in a vertex `a`.
  obtain ⟨x, hxC, hxH⟩ := not_subset.1 hCH
  obtain ⟨y, hyC, hyG⟩ := not_subset.1 hCG
  have hxG : x ∈ V(G) := by simpa [hxH] using hC.vertexSet_subset hxC
  have hyH : y ∈ V(H) := by simpa [hyG] using hC.vertexSet_subset hyC
  obtain ⟨W, hW, rfl, rfl⟩ := (hC.isWalk.vertexConnected_of_mem_of_mem hxC hyC).exists_isWalk
  obtain ⟨a, -, haG, haH⟩ := hW.exists_mem_mem_of_union hxG hyH
  have hxa : W.first ≠ a := by rintro rfl; contradiction
  have hya : W.last ≠ a := by rintro rfl; contradiction
  -- Now take an `xy`-path in `C` that doesn't use `a`. This must intersect `V(G) ∩ V(H)`
  -- in another vertex `b`, contradicting the fact that the intersection is a subsingleton.
  obtain ⟨w', hW', h1', h2'⟩ :=
    (hC.vertexConnected_deleteVertex_of_mem_of_mem a hxC hyC hxa hya).exists_isWalk
  rw [hcompat.vertexDelete_union] at hW'
  obtain ⟨b, -, hbG, hbH⟩ :=
    hW'.exists_mem_mem_of_union (by simp [h1', hxG, hxa]) (by simp [h2', hyH, hya])
  rw [vertexDelete_vertexSet, mem_diff, mem_singleton_iff] at hbG hbH
  refine False.elim <| hbG.2 (hi.elim ?_ ?_) <;> simp_all

lemma Compatible.isCycle_union_iff_of_subsingleton_inter (hcompat : G.Compatible H)
    (hi : (V(G) ∩ V(H)).Subsingleton) : (G ∪ H).IsCycle C ↔ G.IsCycle C ∨ H.IsCycle C :=
  ⟨fun h ↦ h.isCycle_or_isCycle_of_union_of_subsingleton_inter hi,
    fun h ↦ h.elim (fun h' ↦ h'.isCycle_of_ge (left_le_union ..))
    (fun h' ↦ h'.isCycle_of_ge hcompat.right_le_union)⟩

/-! ### Bridges -/

/-- A bridge is an edge in no cycle-/
@[mk_iff]
structure IsBridge (G : Graph α β) (e : β) : Prop where
  mem_edgeSet : e ∈ E(G)
  not_mem_cycle : ∀ ⦃C⦄, G.IsCycle C → e ∉ C.edge

lemma not_isBridge (he : e ∈ E(G)) : ¬ G.IsBridge e ↔ ∃ C, G.IsCycle C ∧ e ∈ C.edge := by
  simp [isBridge_iff, he]

lemma IsCycle.not_isBridge_of_mem (hC : G.IsCycle C) (heC : e ∈ C.edge) : ¬ G.IsBridge e := by
  rw [not_isBridge (hC.isWalk.edgeSet_subset heC)]
  exact ⟨C, hC, heC⟩

lemma IsLink.isBridge_iff_not_vertexConnected (he : G.IsLink e x y) :
    G.IsBridge e ↔ ¬ (G ＼ {e}).VertexConnected x y := by
  refine ⟨fun h hconn ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := hconn.exists_isPath
    simp only [isPath_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
    exact (hP.1.cons_isCycle he hP.2).not_isBridge_of_mem (by simp) h
  contrapose! h
  obtain ⟨C, hC, heC⟩ := (not_isBridge he.edge_mem).1 h
  rw [← hC.isWalk.isLink_iff_isLink_of_mem heC] at he
  exact hC.vertexConnected_deleteEdge_of_mem_of_mem _ he.left_mem he.right_mem

lemma Connected.edgeDelete_singleton_connected (hG : G.Connected) (he : ¬ G.IsBridge e) :
    (G ＼ {e}).Connected := by
  obtain heE | heE := em' <| e ∈ E(G)
  · rwa [edgeDelete_eq_self _ (by simpa)]
  obtain ⟨C, hC, heC⟩ := (not_isBridge heE).1 he
  rw [← (G ＼ {e}).induce_union_edgeDelete (X := V(C)) (by simp [hC.vertexSet_subset])]
  refine Compatible.union_connected_of_forall (G.compatible_of_le_le ?_ (by simp)) ?_ ?_
  · exact le_trans (induce_le (by simp [hC.vertexSet_subset])) edgeDelete_le
  · obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
    refine (hP.isWalk.toGraph_connected.of_subgraph ?_ ?_)
    · rw [hPC, edgeDelete_induce, hC.isWalk.toGraph_eq_induce_restrict]
      exact edgeDelete_mono_left (by simp)
    rw [hPC]
    simp
  simp only [edgeDelete_induce, edgeDelete_edgeSet, edgeDelete_edgeDelete, union_diff_self,
    singleton_union, edgeDelete_vertexSet, induce_vertexSet, mem_vertexSet_iff]
  intro x hx
  obtain ⟨y, hy, hconn⟩ := hG.exists_vertexConnected_deleteEdge_set (X := V(C))
    (by simp [inter_eq_self_of_subset_left hC.vertexSet_subset]) hx
  refine ⟨y, hy, ?_⟩
  rwa [insert_eq_of_mem (hC.isWalk.edgeSet_subset_induce_edgeSet heC )]

lemma Connected.edgeDelete_singleton_connected_iff (hG : G.Connected) :
    (G ＼ {e}).Connected ↔ ¬ G.IsBridge e := by
  obtain heE | heE := em' <| e ∈ E(G)
  · simp [edgeDelete_eq_self G (F := {e}) (by simpa), hG, isBridge_iff, heE]
  refine ⟨fun h hbr ↦ ?_, hG.edgeDelete_singleton_connected⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heE
  obtain ⟨P, hP, rfl, rfl⟩ := (h.vertexConnected hxy.left_mem hxy.right_mem).exists_isPath
  simp only [isPath_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
  simpa using hbr.not_mem_cycle <| hP.1.cons_isCycle hxy hP.2

lemma Connected.isBridge_iff (hG : G.Connected) : G.IsBridge e ↔ ¬ (G ＼ {e}).Connected := by
  rw [hG.edgeDelete_singleton_connected_iff, not_not]

/-- Every edge of a path is a bridge -/
lemma IsPath.isBridge_of_mem (hP : G.IsPath P) (heP : e ∈ P.edge) : P.toGraph.IsBridge e := by
  rw [hP.isWalk.toGraph_connected.isBridge_iff, hP.isWalk.toGraph_eq_induce_restrict]
  obtain ⟨P₁, P₂, hP₁, hP₂, heP₁, heP₂, hdj, hedj, rfl⟩ := hP.eq_append_cons_of_edge_mem heP
  rw [append_vertexSet (by simp)]
  suffices ¬(G[V(P₁) ∪ V(P₂)] ↾ (E(P₁) ∪ E(P₂)) \ {e}).Connected by simpa
  rw [diff_singleton_eq_self (by simp [heP₁, heP₂]), ← edgeRestrict_induce, induce_union,
    edgeRestrict_induce, edgeRestrict_induce]
  · exact union_not_connected_of_disjoint_vertexSet
      (by simpa [vertexSet_disjoint_iff]) (by simp) (by simp)
  rintro x hx y hy ⟨f, hf⟩
  simp only [edgeRestrict_isLink, mem_union, mem_edgeSet_iff] at hf
  obtain ⟨(hf | hf), hfxy⟩ := hf
  · rw [← hP₁.isWalk.isLink_iff_isLink_of_mem hf] at hfxy
    exact List.disjoint_right.1 hdj hy hfxy.right_mem
  rw [← hP₂.isWalk.isLink_iff_isLink_of_mem hf] at hfxy
  exact List.disjoint_left.1 hdj hx hfxy.left_mem


/-! ### Components -/

/-- `H.IsComponent G` if `H` is a maximal connected subgraph of `G`. -/
def IsComponent (H G : Graph α β) := Maximal (fun H ↦ H.Connected ∧ H ≤ G) H

lemma IsComponent.le (h : H.IsComponent G) : H ≤ G :=
  h.prop.2

lemma IsComponent.connected (h : H.IsComponent G) : H.Connected :=
  h.prop.1

lemma IsComponent.isInducedSubgraph (h : H.IsComponent G) : H ≤i G := by
  have hss := vertexSet_subset_of_le h.le
  rw [← h.eq_of_ge (y := G[V(H)])]
  · simpa
  · simpa [h.connected.of_isSpanningSubgraph ⟨le_induce_self h.le, by simp⟩]
  exact le_induce_self h.le

/-- If `x` is a vertex of `G`, the set of vertices connected to `x` induces a component of `G`. -/
lemma induce_setOf_vertexConnected_isComponent (hx : x ∈ V(G)) :
    (G[{y | G.VertexConnected x y}]).IsComponent G := by
  refine ⟨⟨⟨⟨x, by simpa⟩, fun y y' h h' ↦ ?_⟩, ?_⟩, fun H' ⟨hc, hH'le⟩ hle ↦ ?_⟩
  · obtain ⟨W, hW, rfl, rfl⟩ := (VertexConnected.trans h.symm h').exists_isWalk
    refine (hW.induce fun y hy ↦ ?_).vertexConnected_first_last
    simp only [induce_vertexSet, mem_setOf_eq] at h h'
    exact h.trans <| hW.vertexConnected_of_mem_of_mem (by simp) hy
  · exact induce_le_iff.2 fun y hy ↦ VertexConnected.right_mem hy
  refine le_induce_of_le_of_subset hH'le fun z hz ↦ ?_
  exact (hc.vertexConnected (x := x) (vertexSet_subset_of_le hle (by simpa)) hz).of_le hH'le

/-- Every connected subgraph of `G` is a subgraph of a component of `G`. -/
lemma Connected.exists_component_ge (hH : H.Connected) (hle : H ≤ G) :
    ∃ G₁, G₁.IsComponent G ∧ H ≤ G₁ := by
  obtain ⟨x, hx⟩ := hH.nonempty
  refine ⟨_, induce_setOf_vertexConnected_isComponent (vertexSet_subset_of_le hle hx), ?_⟩
  exact le_induce_of_le_of_subset hle fun y hy ↦ (hH.vertexConnected hx hy).of_le hle

lemma exists_isComponent_vertex_mem (hx : x ∈ V(G)) :
    ∃ (H : Graph α β), H.IsComponent G ∧ x ∈ V(H) :=
  ⟨_, induce_setOf_vertexConnected_isComponent hx, by simpa⟩

lemma exists_isComponent_edge_mem (he : e ∈ E(G)) :
    ∃ (H : Graph α β), H.IsComponent G ∧ e ∈ E(H) := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨H, hH, hle⟩ := (singleEdge_connected e x y).exists_component_ge (G := G) (by simpa)
  simp only [singleEdge_le_iff] at hle
  exact ⟨H, hH, hle.edge_mem⟩

lemma IsWalk.exists_isComponent_isWalk (hW : G.IsWalk W) :
    ∃ (H : Graph α β), H.IsComponent G ∧ H.IsWalk W := by
  obtain ⟨H, hle, hWH⟩ := hW.toGraph_connected.exists_component_ge hW.toGraph_le
  exact ⟨H, hle, by rwa [← hW.wellFormed.toGraph_le_iff]⟩

/-- Distinct components are vertex-disjoint. -/
lemma IsComponent.disjoint_of_ne {H₁ H₂ : Graph α β}
    (hH₁ : H₁.IsComponent G) (hH₂ : H₂.IsComponent G) (hne : H₁ ≠ H₂) : H₁.Disjoint H₂ := by
  refine Compatible.disjoint_of_vertexSet_disjoint (G.compatible_of_le_le hH₁.le hH₂.le) ?_
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  contrapose! hne
  have hc : Compatible H₁ H₂ := compatible_of_le_le hH₁.le hH₂.le
  rw [← hH₁.eq_of_ge ⟨(hc.union_connected_of_nonempty_inter hH₁.connected hH₂.connected hne),
      (union_le hH₁.le hH₂.le)⟩ (left_le_union ..), hc.union_comm,
    hH₂.eq_of_ge ⟨(hc.symm.union_connected_of_nonempty_inter hH₂.connected hH₁.connected
      (by rwa [inter_comm])), (union_le hH₂.le hH₁.le)⟩ (left_le_union ..)]

lemma pairwiseDisjoint_components (G : Graph α β) :
    {H : Graph α β | H.IsComponent G}.Pairwise Graph.Disjoint :=
  fun _ hC _ hC' ↦ hC.disjoint_of_ne hC'

/-- A graph is connected if and only if it is a component of itself. -/
@[simp]
lemma isComponent_self_iff : G.IsComponent G ↔ G.Connected :=
  ⟨IsComponent.connected, fun h ↦ ⟨⟨h, le_rfl⟩, fun _ h _ ↦ h.2⟩⟩

/-- A graph is the union of its components -/
-- lemma eq_iUnion_components (G : Graph α β) :
--     ∃ (h : UCompatible (fun C : {H // H.IsComponent G} ↦ C.1)), G = h.iUnion _ := by
--   refine ⟨UCompatible.of_forall_subgraph (G := G) fun C ↦ C.2.le, G.ext_of_le_le le_rfl ?_ ?_ ?_⟩
--   · simp +contextual [IsComponent.le]
--   · refine subset_antisymm (fun x hxV ↦ ?_) ?_
--     · simpa using exists_isComponent_vertex_mem hxV
--     simpa using fun _ h ↦ (vertexSet_subset_of_le h.le)
--   refine subset_antisymm (fun e he ↦ ?_) ?_
--   · simpa using exists_isComponent_edge_mem he
--   simpa using fun _ h ↦ (edgeSet_subset_of_le h.le)

lemma eq_sUnion_components (G : Graph α β) :
    G = Graph.sUnion {C | C.IsComponent G} (G.pairwiseDisjoint_components.mono' (by simp)) := by
  refine G.ext_of_le_le le_rfl ?_ ?_ ?_
  · simp +contextual [IsComponent.le]
  · refine subset_antisymm (fun v hv ↦ ?_) ?_
    · simpa using exists_isComponent_vertex_mem hv
    simpa using fun _ h ↦ (vertexSet_subset_of_le h.le)
  refine subset_antisymm (fun e he ↦ ?_) ?_
  · simpa using exists_isComponent_edge_mem he
  simpa using fun _ h ↦ (edgeSet_subset_of_le h.le)

lemma IsComponent.isLink_of_isLink_of_mem (h : H.IsComponent G) (hx : x ∈ V(H))
    (hxy : G.IsLink e x y) : H.IsLink e x y := by
  obtain ⟨H', hH'G, heH'⟩ := hxy.walk_isWalk.exists_isComponent_isWalk
  simp only [IsLink.walk, cons_isWalk_iff, nil_first, nil_isWalk_iff] at heH'
  obtain rfl | hne := eq_or_ne H H'
  · exact heH'.1
  exact False.elim <| (hH'G.disjoint_of_ne h hne.symm).vertex.not_mem_of_mem_left heH'.1.left_mem hx

lemma IsComponent.adj_of_adj_of_mem (h : H.IsComponent G) (hx : x ∈ V(H)) (hxy : G.Adj x y) :
    H.Adj x y := by
  obtain ⟨e, hexy⟩ := hxy
  exact (h.isLink_of_isLink_of_mem hx hexy).adj

lemma IsComponent.inc_of_inc_of_mem (h : H.IsComponent G) (hx : x ∈ V(H)) (hxe : G.Inc e x) :
    H.Inc e x := by
  obtain ⟨y, hexy⟩ := hxe
  exact (h.isLink_of_isLink_of_mem hx hexy).inc_left

/-- For a proper component `H`, the separation with parts `V(H)` and `V(G) \ V(H)`. -/
@[simps]
def IsComponent.separation_of_ne (h : H.IsComponent G) (hne : H ≠ G) : G.Separation where
  left := V(H)
  right := V(G) \ V(H)
  nonempty_left := h.connected.nonempty
  nonempty_right := diff_nonempty.2 fun hss ↦ hne <|
    h.isInducedSubgraph.eq_of_isSpanningSubgraph ⟨h.le, hss.antisymm' (vertexSet_subset_of_le h.le)⟩
  disjoint := disjoint_sdiff_right
  union_eq := by simp [vertexSet_subset_of_le h.le]
  not_adj x y hx hy hxy := hy.2 <| (h.adj_of_adj_of_mem hx hxy).right_mem

/-- If `H` is a connected subgraph of a disconnected graph `G`,
then there is a separation of `G` with `H` on the left. -/
lemma Connected.exists_separation_of_le (hH : H.Connected) (hG : ¬ G.Connected) (hle : H ≤ G) :
    ∃ S : G.Separation, H ≤ G[S.left] := by
  obtain ⟨H', hH'H, hle'⟩ := hH.exists_component_ge hle
  refine ⟨hH'H.separation_of_ne ?_, ?_⟩
  · rintro rfl
    exact hG hH'H.connected
  simp only [IsComponent.separation_of_ne_left]
  exact hle'.trans <| le_induce_self hH'H.le

/-! ### Staying Connected -/

/-- A leaf vertex in a trail is either the first or last vertex of the trail-/
lemma IsLeafVertex.eq_first_or_eq_last_of_mem_trail {P : WList α β} (hx : G.IsLeafVertex x)
    (hP : G.IsTrail P) (hxP : x ∈ P) : x = P.first ∨ x = P.last := by
  induction P with
  | nil => simpa using hxP
  | cons u e P ih =>
    simp only [cons_isTrail_iff] at hP
    obtain (rfl : x = u) | (hxP : x ∈ P) := by simpa using hxP
    · simp
    obtain rfl | rfl := (ih hP.1 hxP).symm
    · simp
    cases P with
    | nil => simp
    | cons v f P =>
      simp only [cons_isTrail_iff, first_cons, cons_edge, List.mem_cons, not_or] at hP
      simp [hx.eq_of_inc_inc hP.1.2.1.inc_left hP.2.1.inc_right] at hP

lemma IsLeafVertex.eq_first_or_eq_last_of_mem_path {P : WList α β} (hx : G.IsLeafVertex x)
    (hP : G.IsPath P) (hxP : x ∈ P) : x = P.first ∨ x = P.last :=
  hx.eq_first_or_eq_last_of_mem_trail hP.isTrail hxP

lemma IsLeafVertex.delete_connected (hx : G.IsLeafVertex x) (hG : G.Connected) :
    (G - {x}).Connected := by
  obtain ⟨y, hy : G.Adj x y, hu⟩ := hx.exists_unique_adj
  refine connected_of_vertex ⟨hy.right_mem, fun h : y = x ↦ hx.not_adj_self (h ▸ hy)⟩ fun z hz ↦ ?_
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vertexConnected hz.1 hy.right_mem).exists_isPath
  refine IsWalk.vertexConnected_first_last <| isWalk_vertexDelete_iff.2 ⟨hP.isWalk, ?_⟩
  simp only [disjoint_singleton_right, mem_vertexSet_iff]
  intro hxP
  obtain rfl | rfl := hx.eq_first_or_eq_last_of_mem_path hP hxP
  · simp at hz
  exact hx.not_adj_self hy

/-- Deleting the first vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_first_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - {P.first}).Connected := by
  cases P with
  | nil u =>
    obtain ⟨y, hne, ⟨e, huy⟩⟩ := hG.exists_adj_of_mem (x := u) hnt (by simpa using hP.prop)
    exact False.elim <| hne.symm <| by
      simpa [huy, huy.right_mem] using hP.eq_of_ge (y := cons u e (nil y))
  | cons u e P =>
    have ⟨hP', he, huP⟩ : G.IsPath P ∧ G.IsLink e u P.first ∧ u ∉ P := by simpa using hP.prop
    by_contra hcon
    simp only [first_cons] at hcon
    have hP'' : (G - {u}).IsPath P := by simp [isPath_vertexDelete_iff, huP, hP']
    obtain ⟨S, hS⟩ :=
      hP''.isWalk.toGraph_connected.exists_separation_of_le hcon hP''.isWalk.toGraph_le
    have hPS : V(P) ⊆ S.left := by simpa using vertexSet_subset_of_le hS
    have huleft : u ∉ S.left := fun huS ↦ by simpa using S.left_subset huS
    have huright : u ∉ S.right := fun huS ↦ by simpa using S.right_subset huS
    suffices hu : ∀ x ∈ S.right, ¬ G.Adj u x by
      refine Separation.not_connected
        ⟨insert u S.left, S.right, by simp, S.nonempty_right, ?_, ?_, ?_⟩ hG
      · simp [S.disjoint, huright]
      · simpa [insert_union, S.union_eq] using he.left_mem
      rintro x y (rfl | hxS) hyS ⟨e, hxy⟩
      · exact hu y hyS hxy.adj
      refine S.not_adj hxS hyS ⟨e, ?_⟩
      simp only [vertexDelete_isLink_iff, hxy, mem_singleton_iff, true_and]
      constructor <;> (rintro rfl; contradiction)
    rintro x hx ⟨f, hux⟩
    have hne : u ≠ x := by rintro rfl; contradiction
    refine S.disjoint.not_mem_of_mem_left (hPS ?_) hx
    simpa [hne.symm] using mem_of_adj_first_of_maximal_isPath hP hux.symm.adj

/-- Deleting the last vertex of a maximal path of a connected graph gives a connected graph. -/
lemma Connected.delete_last_connected_of_maximal_isPath (hG : G.Connected) (hnt : V(G).Nontrivial)
    (hP : Maximal (fun P ↦ G.IsPath P) P) : (G - {P.last}).Connected := by
  suffices aux : Maximal (fun P ↦ G.IsPath P) P.reverse by
    simpa using hG.delete_first_connected_of_maximal_isPath hnt aux
  refine ⟨by simpa using hP.prop, fun Q hQ hPQ ↦ ?_⟩
  simp [hP.eq_of_le (y := Q.reverse) (by simpa) (by simpa using IsSublist.reverse hPQ)]

/-- Every finite connected graph on at least two vertices has a vertex whose deletion
preserves its connectedness.
(This requires a finite graph, since otherwise an infinite path is a counterexample.) -/
lemma Connected.exists_delete_vertex_connected [G.Finite] (hG : G.Connected)
    (hnt : V(G).Nontrivial) : ∃ x ∈ V(G), (G - {x}).Connected := by
  obtain ⟨x, hx⟩ := hG.nonempty
  obtain ⟨P, hP⟩ := Finite.exists_maximal G.isPath_finite ⟨nil x, by simpa⟩
  exact ⟨_, hP.prop.isWalk.first_mem, hG.delete_first_connected_of_maximal_isPath hnt hP⟩


end Graph
