import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Subgraph
import Mathlib.Data.Set.Insert

open Set Function Nat

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C w P Q : WList α β}

open WList Graph

lemma Set.Subsingleton.elim {s : Set α} (hs : s.Subsingleton) (hxs : x ∈ s) (hys : y ∈ s) :
    x = y := by
  obtain rfl | ⟨a, rfl⟩ := hs.eq_empty_or_singleton <;> simp_all


namespace Graph

/-- `G.VxConnected v w` means that `G` contains a walk from `v` to `w`. -/
def VxConnected (G : Graph α β) : α → α → Prop :=
    Relation.TransGen (fun x y ↦ G.Adj x y ∨ (x = y ∧ x ∈ V(G)))

lemma VxConnected.refl (h : v ∈ V(G)) : G.VxConnected v v := by
  rw [VxConnected, Relation.transGen_iff]
  simp [h]

lemma VxConnected.trans (hxy : G.VxConnected x y) (hyz : G.VxConnected y z) : G.VxConnected x z :=
  Relation.TransGen.trans hxy hyz

lemma VxConnected.symm (hxy : G.VxConnected x y) : G.VxConnected y x := by
  rw [VxConnected, Relation.transGen_swap]
  rw [VxConnected] at hxy
  convert hxy using 4 with x y
  · rw [adj_comm]
  aesop

lemma VxConnected.mem_left (hxy : G.VxConnected x y) : x ∈ V(G) := by
  induction hxy with
  | single h => exact h.elim Adj.left_mem And.right
  | tail _ _ h => exact h

lemma VxConnected.mem_right (hxy : G.VxConnected x y) : y ∈ V(G) :=
  hxy.symm.mem_left

@[simp]
lemma vxConnected_self : G.VxConnected x x ↔ x ∈ V(G) :=
  ⟨VxConnected.mem_left, VxConnected.refl⟩

lemma Adj.vxConnected (h : G.Adj x y) : G.VxConnected x y := by
  rw [VxConnected, Relation.transGen_iff]
  simp [h]

lemma IsLink.vxConnected (h : G.IsLink e x y) : G.VxConnected x y :=
  h.adj.vxConnected

lemma IsWalk.vxConnected_of_mem_of_mem (hw : G.IsWalk w) (hx : x ∈ w) (hy : y ∈ w) :
    G.VxConnected x y := by
  suffices aux : ∀ ⦃z⦄, z ∈ w → G.VxConnected z w.last from (aux hx).trans (aux hy).symm
  clear hx hy
  intro z hz
  induction hw generalizing z with
  | nil => simp_all
  | cons hw h ih =>
    obtain rfl | hz := by simpa using hz
    · exact h.vxConnected.trans <| by simpa only [last_cons] using ih <| by simp
    simpa using ih hz

lemma IsWalk.vxConnected_first_last (hw : G.IsWalk w) : G.VxConnected w.first w.last :=
  hw.vxConnected_of_mem_of_mem (by simp) <| by simp

lemma VxConnected.exists_isWalk (h : G.VxConnected x y) :
    ∃ w, G.IsWalk w ∧ w.first = x ∧ w.last = y := by
  rw [VxConnected] at h
  induction h using Relation.TransGen.head_induction_on with
  | @base a h =>
    obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h
    · exact ⟨he.walk, by simp⟩
    exact ⟨.nil a, by simp [h]⟩
  | @ih u v h₁ h₂ h₃ =>
    obtain ⟨w, hw, rfl, rfl⟩ := h₃
    obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h₁
    · exact ⟨.cons u e w, by simp [he, hw]⟩
    exact ⟨w, hw, rfl, rfl⟩

lemma vxConnected_iff_exists_walk :
    G.VxConnected x y ↔ ∃ w, G.IsWalk w ∧ w.first = x ∧ w.last = y := by
  refine ⟨VxConnected.exists_isWalk, ?_⟩
  rintro ⟨w, hw, rfl, rfl⟩
  exact hw.vxConnected_first_last

lemma VxConnected.exists_isPath (h : G.VxConnected x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y := by
  classical
  obtain ⟨w, hw, rfl, rfl⟩ := h.exists_isWalk
  exact ⟨w.dedup, by simp [hw.dedup_isPath]⟩

lemma VxConnected.of_le (h : H.VxConnected x y) (hle : H ≤ G) : G.VxConnected x y := by
  obtain ⟨w, hw, rfl, rfl⟩ := h.exists_isWalk
  exact (hw.of_le hle).vxConnected_first_last

lemma vxConnected_induce_iff {X : Set α} (hx : x ∈ V(G)) :
    G[X].VxConnected x y ↔ ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ V(P) ⊆ X := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
    refine ⟨P, ?_, rfl, rfl, hP.vertexSet_subset⟩
    cases P with
    | nil => simpa
    | cons u e w =>
      rw [isPath_induce_iff' (by simp)] at hP
      exact hP.1
  rintro ⟨P, h, rfl, rfl, hPX⟩
  cases P with
  | nil => simpa using hPX
  | cons u e w =>
    apply IsWalk.vxConnected_first_last
    rw [isWalk_induce_iff' (by simp)]
    simp_all only [cons_isPath_iff, first_cons, cons_vertexSet, cons_isWalk_iff, true_and, and_true]
    exact h.1.isWalk

/-- A graph is `Connected` if it is nonempty, and every pair of vertices is `VxConnected`. -/
@[mk_iff]
structure Connected (G : Graph α β) : Prop where
  nonempty : V(G).Nonempty
  vxConnected : ∀ ⦃x y⦄, x ∈ V(G) → y ∈ V(G) → G.VxConnected x y

/-- If `G` has one vertex connected to all others, then `G` is connected. -/
lemma connected_of_vx (hu : u ∈ V(G)) (h : ∀ y ∈ V(G), G.VxConnected y u) : G.Connected :=
  ⟨⟨u, hu⟩, fun x y hx hy ↦ (h x hx).trans (h y hy).symm⟩

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : V(G).Nonempty) :
    ∃ X ⊂ V(G), X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp,
    exists_prop, exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.VxConnected x z}, ?_, ⟨x, by simpa⟩, fun u v (h : G.VxConnected x u) huv ↦ ?_⟩
  · exact HasSubset.Subset.ssubset_of_mem_not_mem
      (fun z hz ↦ VxConnected.mem_right hz) hy (by simpa)
  exact h.trans huv.vxConnected

lemma connected_iff_forall_exists_adj (hne : V(G).Nonempty) :
    G.Connected ↔ ∀ X ⊂ V(G), X.Nonempty → ∃ x ∈ X, ∃ y ∈ V(G) \ X, G.Adj x y := by
  refine ⟨fun h X hXV ⟨x, hxV⟩ ↦ ?_, fun h ↦ by_contra fun hnc ↦ ?_⟩
  · obtain ⟨y', hy'V, hy'X⟩ := exists_of_ssubset hXV
    obtain ⟨w, hw, rfl, rfl⟩ := (h.vxConnected (hXV.subset hxV) hy'V).exists_isWalk
    obtain ⟨e, x₁, y₁, h, hx₁, hy₁⟩ := exists_dInc_prop_not_prop hxV hy'X
    exact ⟨x₁, hx₁, y₁, ⟨hw.vx_mem_of_mem h.right_mem, hy₁⟩, (hw.isLink_of_dInc h).adj⟩
  obtain ⟨X, hXV, hXne, h'⟩ := exists_of_not_connected hnc hne
  obtain ⟨x, hX, y, hy, hxy⟩ := h X hXV hXne
  exact hy.2 <| h' hX hxy

/-- A `WList` that is `WellFormed` produces a connected graph. -/
lemma _root_.WList.WellFormed.toGraph_connected (hw : w.WellFormed) : w.toGraph.Connected :=
  ⟨by simp, fun x y hx hy ↦
    hw.isWalk_toGraph.vxConnected_of_mem_of_mem (by simpa using hx) (by simpa using hy)⟩

lemma IsWalk.toGraph_connected (hw : G.IsWalk w) : w.toGraph.Connected :=
  hw.wellFormed.toGraph_connected

lemma Connected.exists_vxConnected_deleteEdge_set {X : Set α} (hG : G.Connected)
    (hX : (X ∩ V(G)).Nonempty) (hu : u ∈ V(G)) : ∃ x ∈ X, (G ＼ E(G[X])).VxConnected u x := by
  obtain ⟨x', hx'X, hx'V⟩ := hX
  obtain ⟨w, hw, hu, rfl⟩ := (hG.vxConnected hu hx'V).exists_isWalk
  induction hw generalizing u with
  | nil => exact ⟨_, hx'X, by simp_all⟩
  | @cons x e w hw h ih =>
    obtain rfl : x = u := hu
    by_cases hmem : e ∈ E(G ＼ E(G[X]))
    · obtain ⟨x', hx', hwx'⟩ := ih (u := w.first) (hw.vx_mem_of_mem (by simp)) rfl
        (by simpa using hx'X) (by simpa using hx'V)
      have hconn := ((h.of_le_of_mem (edgeDelete_le _ E(G[X]))) hmem).vxConnected
      exact ⟨x', hx', hconn.trans hwx'⟩
    rw [edgeDelete_edgeSet, mem_diff, and_iff_right h.edge_mem, h.mem_induce_iff, not_not] at hmem
    exact ⟨x, hmem.1, by simpa⟩

lemma Connected.exists_isPathFrom (hG : G.Connected) (hS : (S ∩ V(G)).Nonempty)
    (hT : (T ∩ V(G)).Nonempty) : ∃ P, G.IsPathFrom S T P := by
  obtain ⟨x, hxS, hx⟩ := hS
  obtain ⟨y, hyT, hy⟩ := hT
  obtain ⟨w, hw, rfl, rfl⟩ := (hG.vxConnected hx hy).exists_isWalk
  clear hx hy
  induction hw generalizing S with
  | @nil x hx => exact ⟨nil x, by simp_all⟩
  | @cons x e P hP h ih =>
    simp_all only [cons_vx, List.nodup_cons, mem_vx, first_cons, last_cons, forall_const]
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

lemma Connected.exists_vxConnected_deleteEdge_set_set (hG : G.Connected)
    (hS : (S ∩ V(G)).Nonempty) (hT : (T ∩ V(G)).Nonempty) :
    ∃ x ∈ S, ∃ y ∈ T, (G ＼ (E(G[S]) ∪ E(G[T]))).VxConnected x y := by
  obtain ⟨P, hP⟩ := hG.exists_isPathFrom hS hT
  have h0 : P.first ∈ V(G ＼ (E(G[S]) ∪ E(G[T]))) := by
    simpa using hP.isWalk.vx_mem_of_mem (by simp)
  refine ⟨_, hP.first_mem, _, hP.last_mem,
    (hP.isPathFrom_le (by simp) (fun e heP ↦ ?_) h0).isWalk.vxConnected_first_last⟩
  obtain ⟨x, y, hxy⟩ := exists_dInc_of_mem_edge heP
  have hxy' := hP.isWalk.isLink_of_dInc hxy
  rw [edgeDelete_edgeSet, mem_diff, mem_union, hxy'.mem_induce_iff,
    hxy'.mem_induce_iff, and_iff_right hxy'.edge_mem]
  simp [hP.not_mem_left_of_dInc hxy, hP.not_mem_right_of_dInc hxy]

lemma Connected.exists_adj_of_mem (hG : G.Connected) (hV : V(G).Nontrivial) (hx : x ∈ V(G)) :
    ∃ y ≠ x, G.Adj x y := by
  obtain ⟨z, hz, hne⟩ := hV.exists_ne x
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vxConnected hx hz).exists_isPath
  rw [ne_comm, first_ne_last_iff hP.nodup] at hne
  cases hne with | cons x e P =>
  simp only [cons_isPath_iff] at hP
  exact ⟨P.first, mt (by simp +contextual [eq_comm]) hP.2.2, hP.2.1.adj⟩

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

lemma Separation.not_mem_left_iff (S : G.Separation) (hxV : x ∈ V(G)) :
    x ∉ S.left ↔ x ∈ S.right := by
  rw [← S.union_eq, mem_union] at hxV
  have := S.disjoint.not_mem_of_mem_left (a := x)
  tauto

lemma Separation.not_mem_right_iff (S : G.Separation) (hxV : x ∈ V(G)) :
    x ∉ S.right ↔ x ∈ S.left := by
  simpa using S.symm.not_mem_left_iff hxV

lemma Separation.mem_left_of_adj {S : G.Separation} (hx : x ∈ S.left) (hxy : G.Adj x y) :
    y ∈ S.left := by
  rw [← S.not_mem_right_iff hxy.right_mem]
  exact fun hy ↦ S.not_adj hx hy hxy

lemma Separation.mem_right_of_adj {S : G.Separation} (hx : x ∈ S.right) (hxy : G.Adj x y) :
    y ∈ S.right :=
  S.symm.mem_left_of_adj hx (y := y) hxy

lemma Separation.mem_or_mem (S : G.Separation) (hxV : x ∈ V(G)) : x ∈ S.left ∨ x ∈ S.right := by
  rwa [← mem_union, S.union_eq]

lemma Separation.not_vxConnected (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.VxConnected x y := by
  intro h
  obtain ⟨w, hw, rfl, rfl⟩ := h.exists_isWalk
  rw [← S.not_mem_left_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.mem_left_of_adj hx (hw.isLink_of_dInc hinc).adj

lemma Separation.not_connected (S : G.Separation) : ¬ G.Connected := by
  obtain ⟨x, hx⟩ := S.nonempty_left
  obtain ⟨y, hy⟩ := S.nonempty_right
  exact fun h ↦ S.not_vxConnected hx hy <| h.vxConnected (S.left_subset hx) (S.right_subset hy)

lemma Connected.isEmpty_separation (hG : G.Connected) : IsEmpty G.Separation :=
  isEmpty_iff.2 fun S ↦ S.not_connected hG

lemma exists_separation_of_not_vxConnected (hxV : x ∈ V(G)) (hyV : y ∈ V(G))
    (hxy : ¬ G.VxConnected x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ V(G) | G.VxConnected x w}, {w ∈ V(G) | ¬ G.VxConnected x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.vxConnected⟩, by simp_all⟩

lemma nonempty_separation_of_not_connected (hne : V(G).Nonempty) (hG : ¬ G.Connected) :
    Nonempty G.Separation := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp, exists_and_left] at hG
  obtain ⟨x, y, hx, hy, hxy⟩ := hG
  exact ⟨(exists_separation_of_not_vxConnected hx hy hxy).choose⟩

/-- If `G` is connected but its restriction to some set `F` of edges is not,
then there is an edge of `G` joining two vertices that are not connected in the restriction. -/
lemma Connected.exists_of_edgeRestrict_not_connected (hG : G.Connected)
    (hF : ¬ (G.edgeRestrict F).Connected) :
    ∃ (S : (G.edgeRestrict F).Separation) (e : β) (x : α) (y : α),
    e ∉ F ∧ x ∈ S.left ∧ y ∈ S.right ∧ G.IsLink e x y := by
  obtain ⟨S⟩ := nonempty_separation_of_not_connected (by simpa using hG.nonempty) hF
  obtain ⟨x₀, hx₀⟩ := S.nonempty_left
  obtain ⟨y₀, hy₀⟩ := S.nonempty_right
  obtain ⟨w, hw, rfl, rfl⟩ :=
    (hG.vxConnected (S.left_subset hx₀) (S.right_subset hy₀)).exists_isWalk
  rw [← S.not_mem_left_iff (S.right_subset hy₀)] at hy₀
  obtain ⟨e, x, y, hexy, hx, hy⟩ := w.exists_dInc_prop_not_prop hx₀ hy₀
  have h' := hw.isLink_of_dInc hexy
  rw [S.not_mem_left_iff h'.right_mem] at hy
  refine ⟨S, e, x, y, fun heF ↦ ?_, hx, hy, h'⟩
  exact S.not_adj hx hy <| IsLink.adj <| h'.of_le_of_mem (by simp) <| by simpa [h'.edge_mem]

lemma Connected.of_subgraph (hH : H.Connected) (hle : H ≤ G) (hV : V(H) = V(G)) : G.Connected := by
  obtain ⟨x, hx⟩ := hH.nonempty
  refine connected_of_vx (vertexSet_subset_of_le hle hx) fun y hy ↦ ?_
  exact (hH.vxConnected (y := x) (by rwa [hV]) hx).of_le hle

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
    (.inl ∘ fun h' ↦ ⟨h', S.mem_left_of_adj h' h.adj⟩)
    (.inr ∘ fun h' ↦ ⟨h', S.mem_right_of_adj h' h.adj⟩)

/- ### Unions -/

lemma Compatible.union_connected_of_forall (h : G.Compatible H) (hG : G.Connected)
    (hH : ∀ x ∈ V(H), ∃ y ∈ V(G), H.VxConnected x y) : (G ∪ H).Connected := by
  obtain ⟨v, hv⟩ := hG.nonempty
  refine connected_of_vx (u := v) (by simp [hv]) ?_
  rintro y (hy | hy)
  · exact (hG.vxConnected hy hv).of_le <| left_le_union ..
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.of_le h.right_le_union).trans <| (hG.vxConnected hzG hv).of_le <| left_le_union ..

lemma Compatible.union_connected_of_nonempty_inter (h : Compatible G H) (hG : G.Connected)
    (hH : H.Connected) (hne : (V(G) ∩ V(H)).Nonempty) : (G ∪ H).Connected :=
  let ⟨z, hzG, hzH⟩ := hne
  h.union_connected_of_forall hG fun _ hx ↦ ⟨z, hzG, hH.vxConnected hx hzH⟩

lemma IsWalk.exists_mem_mem_of_union (h : (G ∪ H).IsWalk w) (hG : w.first ∈ V(G))
    (hH : w.last ∈ V(H)) : ∃ x ∈ w, x ∈ V(G) ∧ x ∈ V(H) := by
  by_cases hH' : w.last ∈ V(G)
  · exact ⟨w.last, by simp, hH', hH⟩
  obtain ⟨e, x, y, hxy, hx, hy⟩ := w.exists_dInc_prop_not_prop hG hH'
  obtain hxy' | hxy' := isLink_or_isLink_of_union <| h.isLink_of_dInc hxy
  · exact False.elim <| hy <| hxy'.right_mem
  exact ⟨x, hxy.left_mem, hx, hxy'.left_mem⟩

lemma union_not_connected_of_disjoint_vertexSet (hV : Disjoint V(G) V(H)) (hG : V(G).Nonempty)
    (hH : V(H).Nonempty) : ¬ (G ∪ H).Connected := by
  obtain ⟨x, hx⟩ := hG
  obtain ⟨y, hy⟩ := hH
  intro h
  obtain ⟨w, hw, rfl, rfl⟩ :=
    (h.vxConnected (x := x) (y := y) (by simp [hx]) (by simp [hy])).exists_isWalk
  obtain ⟨u, -, huG, huH⟩ := hw.exists_mem_mem_of_union hx hy
  exact hV.not_mem_of_mem_left huG huH

/-! ### Cycles -/

/-- Two vertices of a cycle are connected after deleting any other vertex.  -/
lemma IsCycle.vxConnected_deleteVx_of_mem_of_mem (hC : G.IsCycle C) (x : α) (hy₁ : y₁ ∈ C)
    (hy₂ : y₂ ∈ C) (hne₁ : y₁ ≠ x) (hne₂ : y₂ ≠ x) : (G - ({x} : Set α)).VxConnected y₁ y₂ := by
  obtain rfl | hne := eq_or_ne y₁ y₂
  · simpa [hC.vertexSet_subset hy₁]
  obtain ⟨u, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · simp_all
  by_cases hxC : x ∈ C
  · obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vx hnt hxC
    refine IsWalk.vxConnected_of_mem_of_mem (w := P) ?_ ?_ ?_
    · simp [hP.isWalk, ← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq]
    all_goals simp_all [← mem_vertexSet_iff, ← toGraph_vertexSet, hP_eq]
  exact IsWalk.vxConnected_of_mem_of_mem (w := C) (by simp [hxC, hC.isWalk]) hy₁ hy₂

 /-- Two vertices of a cycle are connected after deleting any edge. -/
lemma IsCycle.vxConnected_deleteEdge_of_mem_of_mem (hC : G.IsCycle C) (e : β)
    (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) : (G ＼ {e}).VxConnected x₁ x₂ := by
  obtain heC | heC := em' <| e ∈ C.edge
  · exact IsWalk.vxConnected_of_mem_of_mem (by simp [hC.isWalk, heC]) hx₁ hx₂
  obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  apply IsWalk.vxConnected_of_mem_of_mem (w := P) (by simp [hP.isWalk, ← toGraph_edgeSet, hP_eq])
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
  obtain ⟨w, hw, rfl, rfl⟩ := (hC.isWalk.vxConnected_of_mem_of_mem hxC hyC).exists_isWalk
  obtain ⟨a, -, haG, haH⟩ := hw.exists_mem_mem_of_union hxG hyH
  have hxa : w.first ≠ a := by rintro rfl; contradiction
  have hya : w.last ≠ a := by rintro rfl; contradiction
  -- Now take an `xy`-path in `C` that doesn't use `a`. This must intersect `V(G) ∩ V(H)`
  -- in another vertex `b`, contradicting the fact that the intersection is a subsingleton.
  obtain ⟨w', hw', h1', h2'⟩ :=
    (hC.vxConnected_deleteVx_of_mem_of_mem a hxC hyC hxa hya).exists_isWalk
  rw [hcompat.vxDelete_union] at hw'
  obtain ⟨b, -, hbG, hbH⟩ :=
    hw'.exists_mem_mem_of_union (by simp [h1', hxG, hxa]) (by simp [h2', hyH, hya])
  rw [vxDelete_vertexSet, mem_diff, mem_singleton_iff] at hbG hbH
  refine False.elim <| hbG.2 (hi.elim ?_ ?_) <;> simp_all

lemma Compatible.isCycle_union_iff_of_subsingleton_inter (hcompat : G.Compatible H)
    (hi : (V(G) ∩ V(H)).Subsingleton) :
    (G ∪ H).IsCycle C ↔ G.IsCycle C ∨ H.IsCycle C :=
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

lemma IsLink.isBridge_iff_not_vxConnected (he : G.IsLink e x y) :
    G.IsBridge e ↔ ¬ (G ＼ {e}).VxConnected x y := by
  refine ⟨fun h hconn ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := hconn.exists_isPath
    simp only [isPath_edgeDelete_iff, disjoint_singleton_right, mem_edgeSet_iff] at hP
    exact (hP.1.cons_isCycle he hP.2).not_isBridge_of_mem (by simp) h
  contrapose! h
  obtain ⟨C, hC, heC⟩ := (not_isBridge he.edge_mem).1 h
  rw [← hC.isWalk.isLink_iff_isLink_of_mem heC] at he
  exact hC.vxConnected_deleteEdge_of_mem_of_mem _ he.left_mem he.right_mem

lemma Connected.edgeDelete_singleton_connected (hG : G.Connected) (he : ¬ G.IsBridge e) :
    (G ＼ {e}).Connected := by
  obtain heE | heE := em' <| e ∈ E(G)
  · rwa [edgeDelete_eq_self _ (by simpa)]
  obtain ⟨C, hC, heC⟩ := (not_isBridge heE).1 he
  rw [← (G ＼ {e}).induce_union_edgeDelete (X := V(C)) (by simp [hC.vertexSet_subset])]
  refine Compatible.union_connected_of_forall (G.compatible_of_le_le ?_ (by simp)) ?_ ?_
  · exact le_trans (induce_le (by simp [hC.vertexSet_subset])) (G.edgeDelete_le {e})
  · obtain ⟨P, hP, hPC⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
    refine (hP.isWalk.toGraph_connected.of_subgraph ?_ ?_)
    · rw [hPC, edgeDelete_induce, hC.isWalk.toGraph_eq_induce_restrict]
      exact edgeDelete_mono_left (by simp)
    rw [hPC]
    simp
  simp only [edgeDelete_induce, edgeDelete_edgeSet, edgeDelete_edgeDelete, union_diff_self,
    singleton_union, edgeDelete_vertexSet, induce_vertexSet, mem_vertexSet_iff]
  intro x hx
  obtain ⟨y, hy, hconn⟩ := hG.exists_vxConnected_deleteEdge_set (X := V(C))
    (by simp [inter_eq_self_of_subset_left hC.vertexSet_subset]) hx
  refine ⟨y, hy, ?_⟩
  rwa [insert_eq_of_mem (hC.isWalk.edgeSet_subset_induce_edgeSet heC )]

lemma Connected.edgeDelete_singleton_connected_iff (hG : G.Connected) :
    (G ＼ {e}).Connected ↔ ¬ G.IsBridge e := by
  obtain heE | heE := em' <| e ∈ E(G)
  · simp [edgeDelete_eq_self G (F := {e}) (by simpa), hG, isBridge_iff, heE]
  refine ⟨fun h hbr ↦ ?_, hG.edgeDelete_singleton_connected⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heE
  obtain ⟨P, hP, rfl, rfl⟩ := (h.vxConnected hxy.left_mem hxy.right_mem).exists_isPath
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

/-- If `P` and `Q` are distinct paths with the same ends, their union contains a cycle. -/
theorem twoPaths (hP : G.IsPath P) (hQ : G.IsPath Q) (hPQ : P ≠ Q) (h0 : P.first = Q.first)
    (h1 : P.last = Q.last) : ∃ C, G.IsCycle C ∧ E(C) ⊆ E(P) ∪ E(Q) := by
  classical
  induction P generalizing Q with
  | nil u => cases Q with | _ => simp_all
  | cons u e P ih =>
    subst h0
    obtain ⟨heP : e ∉ P.edge, -⟩ := by simpa using hP.edge_nodup
    simp only [cons_isPath_iff] at hP
    obtain ⟨x, rfl⟩ | hne := Q.exists_eq_nil_or_nonempty
    · obtain rfl : P.last = x := h1
      simp at hP
    -- If `e` is an edge of `Q`, then since `e` is incident to the first vertex of `cons u f Q`,
    -- it must be equal to `f`. So `P` and `Q` agree on their first edge; apply induction.
    by_cases heQ : e ∈ Q.edge
    · obtain rfl : e = hne.firstEdge := hQ.eq_firstEdge_of_isLink_first heQ hP.2.1.inc_left
      cases hne with | cons u f Q =>
      have hfirst : P.first = Q.first := by
        simp only [Nonempty.firstEdge_cons, first_cons, cons_isPath_iff] at hP hQ
        rw [hP.2.1.isLink_iff_eq] at hQ
        exact hQ.2.1.symm
      obtain ⟨C, hC, hCss⟩ := ih hP.1 hQ.of_cons (by simpa using hPQ) hfirst (by simpa using h1)
      refine ⟨C, hC, hCss.trans ?_⟩
      simp [show E(P) ⊆ insert f E(P) ∪ E(Q) from (subset_insert ..).trans subset_union_left]
    -- Otherwise, `e + P` and `Q` have different first edges. Now `P ∪ Q`
    -- contains a path between the ends of `e` not containing `e`, which gives a cycle.
    have hR_ex : ∃ R, G.IsPath R ∧ e ∉ R.edge ∧
        R.first = Q.first ∧ R.last = P.first ∧ E(R) ⊆ E(P) ∪ E(Q) := by
      refine ⟨(Q ++ P.reverse).dedup, ?_, ?_, ?_, by simp, ?_⟩
      · exact IsWalk.dedup_isPath (hQ.isWalk.append hP.1.isWalk.reverse (by simpa using h1.symm))
      · rw [← mem_edgeSet_iff]
        refine not_mem_subset (t := E(Q ++ P.reverse)) ((dedup_isSublist _).edgeSet_subset) ?_
        simp [heQ, heP]
      · simp [append_first_of_nonempty hne]
      exact (dedup_isSublist _).edgeSet_subset.trans <| by simp
    obtain ⟨R, hR, heR, hfirst, hlast, hss⟩ := hR_ex
    refine ⟨_, hR.concat_isCycle ?_ heR, ?_⟩
    · rw [hfirst, hlast]
      exact hP.2.1.symm
    simp only [concat_edgeSet, cons_edgeSet]
    rw [insert_union]
    exact insert_subset_insert hss



end Graph

namespace WList

end WList
