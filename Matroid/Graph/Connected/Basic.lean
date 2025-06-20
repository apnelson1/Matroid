import Matroid.Graph.Subgraph
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Defs
import Matroid.Graph.Degree.Constructions
import Mathlib.Data.Set.Insert
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic

open Set Function Nat WList

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

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
  · exact HasSubset.Subset.ssubset_of_mem_notMem
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
  simp [hP.notMem_left_of_dInc hxy, hP.notMem_right_of_dInc hxy]

/-- If `H` is a nonempty proper subgraph of a connected graph `G`,
then there is an edge of `G` that is not in `H` but has an end in `H`. -/
lemma Connected.exists_inc_notMem_of_lt (hG : G.Connected) (hlt : H < G) (hne : V(H).Nonempty) :
    ∃ e x, G.Inc e x ∧ e ∉ E(H) ∧ x ∈ V(H) := by
  obtain hV | hssu := (vertexSet_mono hlt.le).eq_or_ssubset
  · obtain hE | hssu' := (edgeSet_mono hlt.le).eq_or_ssubset
    · simp [ext_of_le_le hlt.le le_rfl hV hE] at hlt
    obtain ⟨e, he, heH⟩ := exists_of_ssubset hssu'
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
    exact ⟨e, x, hxy.inc_left, heH, hV ▸ hxy.left_mem⟩
  obtain ⟨v, hvH, hvG⟩ := exists_of_ssubset hssu
  obtain ⟨P, hP⟩ := hG.exists_isPathFrom (S := V(H)) (T := {v})
    (by rwa [inter_eq_self_of_subset_left hssu.subset]) (by simpa)
  obtain (⟨u⟩ | ⟨u, e, P⟩) := P
  · obtain ⟨-, huG, rfl⟩ := by simpa using hP
    contradiction
  rw [isPathFrom_cons_subgraph hlt.le] at hP
  obtain ⟨huH, hne : u ≠ v, heuP, heH, hHP, hP⟩ := hP
  exact ⟨e, u, heuP.inc_left, heH, huH⟩

lemma Connected.exists_isLink_of_mem (hG : G.Connected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)) :
    ∃ e y, G.IsLink e x y ∧ y ≠ x := by
  obtain ⟨z, hz, hne⟩ := hV.exists_ne x
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vertexConnected hx hz).exists_isPath
  rw [ne_comm, first_ne_last_iff hP.nodup] at hne
  obtain ⟨x, e, P⟩ := hne
  simp only [cons_isPath_iff] at hP
  exact ⟨e, P.first, hP.2.1, mt (by simp +contextual [eq_comm]) hP.2.2⟩

lemma Isolated.not_connected (hx : G.Isolated x) (hnt : V(G).Nontrivial) : ¬ G.Connected :=
  fun h ↦ by simpa [hx.not_isLink] using h.exists_isLink_of_mem hnt hx.mem

lemma Connected.of_isSpanningSubgraph (h : H ≤s G) (hH : H.Connected) : G.Connected :=
  ⟨h.vertexSet_eq ▸ hH.nonempty,
    fun _ _ hx hy ↦ (hH.vertexConnected (h.vertexSet_eq ▸ hx) (h.vertexSet_eq ▸ hy)).of_le h.le ⟩

lemma Connected.degreePos (h : G.Connected) (hnt : V(G).Nontrivial) : G.DegreePos := by
  intro x hx
  obtain ⟨e, y, h, -⟩ := h.exists_isLink_of_mem hnt hx
  exact ⟨e, h.inc_left⟩

lemma Connected.edgeSet_nonempty (h : G.Connected) (hnt : V(G).Nontrivial) : E(G).Nonempty := by
  obtain ⟨x, hx⟩ := hnt.nonempty
  obtain ⟨e, y, he, -⟩ := h.exists_isLink_of_mem hnt hx
  exact ⟨e, he.edge_mem⟩

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
  have := S.disjoint.notMem_of_mem_left (a := x)
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
  refine connected_of_vertex (vertexSet_mono hle hx) fun y hy ↦ ?_
  exact (hH.vertexConnected (y := x) (by rwa [hV]) hx).of_le hle

lemma Separation.edge_induce_disjoint (S : G.Separation) : Disjoint E(G[S.left]) E(G[S.right]) := by
  refine disjoint_left.2 fun e he he' ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq] at he he'
  obtain ⟨x, y, hexy, hx, hy⟩ := he
  obtain ⟨x', y', hexy', hx', hy'⟩ := he'
  obtain rfl | rfl := hexy.left_eq_or_eq hexy'
  · exact S.disjoint.notMem_of_mem_left hx hx'
  exact S.disjoint.notMem_of_mem_left hx hy'

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
  · exact (hG.vertexConnected hy hv).of_le <| Graph.left_le_union ..
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.of_le h.right_le_union).trans <| (hG.vertexConnected hzG hv).of_le <|
    Graph.left_le_union ..

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
    · exact .inl <| hC.isCycle_of_le (Graph.left_le_union ..) (by simpa)
    exact .inr <| hC.isCycle_of_le hcompat.right_le_union (by simpa)
  -- Every edge of `C` has distinct ends in `G` or in `H`.
  have aux1 (e) (he : e ∈ E(C)) :
      ∃ x y, x ≠ y ∧ x ∈ V(C) ∧ y ∈ V(C) ∧ (G.IsLink e x y ∨ H.IsLink e x y) := by
    obtain ⟨x, y, hxy⟩ := C.exists_isLink_of_mem_edge he
    exact ⟨x, y, hC.ne_of_isLink hnt hxy, hxy.left_mem, hxy.right_mem,
      by simpa [hcompat.union_isLink_iff] using hC.isWalk.isLink_of_isLink hxy ⟩
  -- If the vertices of `C` are contained in `G` or `H`, then `C` is contained in `G` or `H`.
  by_cases hCG : V(C) ⊆ V(G)
  · refine .inl <| hC.isCycle_of_le (Graph.left_le_union ..) fun e heC ↦ ?_
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
    fun h ↦ h.elim (fun h' ↦ h'.isCycle_of_ge (Graph.left_le_union ..))
    (fun h' ↦ h'.isCycle_of_ge hcompat.right_le_union)⟩


end Graph
