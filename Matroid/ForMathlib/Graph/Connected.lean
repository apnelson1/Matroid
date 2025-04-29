import Matroid.ForMathlib.Graph.Walk.Cycle
import Matroid.ForMathlib.Graph.Subgraph
import Mathlib.Data.Set.Insert

open Set Function Nat

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β} {U V : Set α}
  {F F' R R': Set β} {C w : WList α β}

open WList Graph

lemma Set.Subsingleton.elim {s : Set α} (hs : s.Subsingleton) (hxs : x ∈ s) (hys : y ∈ s) :
    x = y := by
  obtain rfl | ⟨a, rfl⟩ := hs.eq_empty_or_singleton <;> simp_all


namespace Graph

/-- `G.VxConnected v w` means that `G` contains a walk from `v` to `w`. -/
def VxConnected (G : Graph α β) : α → α → Prop :=
    Relation.TransGen (fun x y ↦ G.Adj x y ∨ (x = y ∧ x ∈ G.V))

lemma VxConnected.refl (h : v ∈ G.V) : G.VxConnected v v := by
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

lemma VxConnected.mem_left (hxy : G.VxConnected x y) : x ∈ G.V := by
  induction hxy with
  | single h => exact h.elim Adj.mem_left And.right
  | tail _ _ h => exact h

lemma VxConnected.mem_right (hxy : G.VxConnected x y) : y ∈ G.V :=
  hxy.symm.mem_left

@[simp]
lemma vxConnected_self : G.VxConnected x x ↔ x ∈ G.V :=
  ⟨VxConnected.mem_left, VxConnected.refl⟩

lemma Adj.vxConnected (h : G.Adj x y) : G.VxConnected x y := by
  rw [VxConnected, Relation.transGen_iff]
  simp [h]

lemma Inc₂.vxConnected (h : G.Inc₂ e x y) : G.VxConnected x y :=
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

lemma vxConnected_induce_iff {X : Set α} (hx : x ∈ G.V) :
    G[X].VxConnected x y ↔ ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ P.V ⊆ X := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
    refine ⟨P, ?_, rfl, rfl, hP.vxSet_subset⟩
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
    simp_all only [cons_isPath_iff, first_cons, cons_vxSet, cons_isWalk_iff, true_and, and_true]
    exact h.1.isWalk

/-- A graph is `Connected` if it is nonempty, and every pair of vertices is `VxConnected`. -/
@[mk_iff]
structure Connected (G : Graph α β) : Prop where
  nonempty : G.V.Nonempty
  vxConnected : ∀ ⦃x y⦄, x ∈ G.V → y ∈ G.V → G.VxConnected x y

/-- If `G` has one vertex connected to all others, then `G` is connected. -/
lemma connected_of_vx (hu : u ∈ G.V) (h : ∀ y ∈ G.V, G.VxConnected y u) : G.Connected :=
  ⟨⟨u, hu⟩, fun x y hx hy ↦ (h x hx).trans (h y hy).symm⟩

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : G.V.Nonempty) :
    ∃ X ⊂ G.V, X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp,
    exists_prop, exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.VxConnected x z}, ?_, ⟨x, by simpa⟩, fun u v (h : G.VxConnected x u) huv ↦ ?_⟩
  · exact HasSubset.Subset.ssubset_of_mem_not_mem
      (fun z hz ↦ VxConnected.mem_right hz) hy (by simpa)
  exact h.trans huv.vxConnected

lemma connected_iff_forall_exists_adj (hne : G.V.Nonempty) :
    G.Connected ↔ ∀ X ⊂ G.V, X.Nonempty → ∃ x ∈ X, ∃ y ∈ G.V \ X, G.Adj x y := by
  refine ⟨fun h X hXV ⟨x, hxV⟩ ↦ ?_, fun h ↦ by_contra fun hnc ↦ ?_⟩
  · obtain ⟨y', hy'V, hy'X⟩ := exists_of_ssubset hXV
    obtain ⟨w, hw, rfl, rfl⟩ := (h.vxConnected (hXV.subset hxV) hy'V).exists_isWalk
    obtain ⟨e, x₁, y₁, h, hx₁, hy₁⟩ := exists_dInc_prop_not_prop hxV hy'X
    exact ⟨x₁, hx₁, y₁, ⟨hw.vx_mem_of_mem h.vx_mem_right, hy₁⟩, (hw.inc₂_of_dInc h).adj⟩
  obtain ⟨X, hXV, hXne, h'⟩ := exists_of_not_connected hnc hne
  obtain ⟨x, hX, y, hy, hxy⟩ := h X hXV hXne
  exact hy.2 <| h' hX hxy

lemma Connected.exists_vxConnected_deleteEdge_set {X Y : Set α} (hG : G.Connected)
    (hX : (X ∩ G.V).Nonempty) (hY : (Y ∩ G.V).Nonempty) :
    ∃ x ∈ X, ∃ y ∈ Y, (G ＼ (G[X].E ∪ G[Y].E)).VxConnected x y := by
  classical
  obtain ⟨x', hx'X, hx'⟩ := hX
  obtain ⟨y', hy'Y, hy'⟩ := hY
  obtain ⟨w, hw, rfl, rfl⟩ := (hG.vxConnected hx' hy').exists_isWalk

  let w' := (w.suffixFromLast (· ∈ X)).prefixUntil (· ∈ Y)
  refine ⟨w'.first, ?_, w'.last, ?_, ?_⟩
  · simp only [prefixUntil_first, w']
    exact suffixFromLast_prop_first ⟨w.first, by simp, hx'X⟩
  · simp only [w']
    apply prefixUntil_prop_last ⟨w.last, ?_, hy'Y⟩
    simp [← (w.suffixFromLast_isSuffix (· ∈ X)).last_eq]




/- ### Separations -/

/-- A partition of `G.V` into two parts with no edge between them. -/
structure Separation (G : Graph α β) where
  left : Set α
  right : Set α
  nonempty_left : left.Nonempty
  nonempty_right : right.Nonempty
  disjoint : Disjoint left right
  union_eq : left ∪ right = G.V
  not_adj : ∀ ⦃x y⦄, x ∈ left → y ∈ right → ¬ G.Adj x y

lemma Separation.left_subset (S : G.Separation) : S.left ⊆ G.V := by
  simp [← S.union_eq]

lemma Separation.right_subset (S : G.Separation) : S.right ⊆ G.V := by
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

lemma Separation.not_mem_left_iff (S : G.Separation) (hxV : x ∈ G.V) :
    x ∉ S.left ↔ x ∈ S.right := by
  rw [← S.union_eq, mem_union] at hxV
  have := S.disjoint.not_mem_of_mem_left (a := x)
  tauto

lemma Separation.not_mem_right_iff (S : G.Separation) (hxV : x ∈ G.V) :
    x ∉ S.right ↔ x ∈ S.left := by
  simpa using S.symm.not_mem_left_iff hxV

lemma Separation.mem_left_of_adj {S : G.Separation} (hx : x ∈ S.left) (hxy : G.Adj x y) :
    y ∈ S.left := by
  rw [← S.not_mem_right_iff hxy.mem_right]
  exact fun hy ↦ S.not_adj hx hy hxy

lemma Separation.mem_right_of_adj {S : G.Separation} (hx : x ∈ S.right) (hxy : G.Adj x y) :
    y ∈ S.right :=
  S.symm.mem_left_of_adj hx (y := y) hxy

lemma Separation.mem_or_mem (S : G.Separation) (hxV : x ∈ G.V) : x ∈ S.left ∨ x ∈ S.right := by
  rwa [← mem_union, S.union_eq]

lemma Separation.not_vxConnected (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.VxConnected x y := by
  intro h
  obtain ⟨w, hw, rfl, rfl⟩ := h.exists_isWalk
  rw [← S.not_mem_left_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.mem_left_of_adj hx (hw.inc₂_of_dInc hinc).adj

lemma Separation.not_connected (S : G.Separation) : ¬ G.Connected := by
  obtain ⟨x, hx⟩ := S.nonempty_left
  obtain ⟨y, hy⟩ := S.nonempty_right
  exact fun h ↦ S.not_vxConnected hx hy <| h.vxConnected (S.left_subset hx) (S.right_subset hy)

lemma Connected.isEmpty_separation (hG : G.Connected) : IsEmpty G.Separation :=
  isEmpty_iff.2 fun S ↦ S.not_connected hG

lemma exists_separation_of_not_vxConnected (hxV : x ∈ G.V) (hyV : y ∈ G.V)
    (hxy : ¬ G.VxConnected x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ G.V | G.VxConnected x w}, {w ∈ G.V | ¬ G.VxConnected x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.vxConnected⟩, by simp_all⟩

lemma nonempty_separation_of_not_connected (hne : G.V.Nonempty) (hG : ¬ G.Connected) :
    Nonempty G.Separation := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp, exists_and_left] at hG
  obtain ⟨x, y, hx, hy, hxy⟩ := hG
  exact ⟨(exists_separation_of_not_vxConnected hx hy hxy).choose⟩

/-- If `G` is connected but its restriction to some set `F` of edges is not,
then there is an edge of `G` joining two vertices that are not connected in the restriction. -/
lemma Connected.exists_of_edgeRestrict_not_connected (hG : G.Connected)
    (hF : ¬ (G.edgeRestrict F).Connected) :
    ∃ (S : (G.edgeRestrict F).Separation) (e : β) (x : α) (y : α),
    e ∉ F ∧ x ∈ S.left ∧ y ∈ S.right ∧ G.Inc₂ e x y := by
  obtain ⟨S⟩ := nonempty_separation_of_not_connected (by simpa using hG.nonempty) hF
  obtain ⟨x₀, hx₀⟩ := S.nonempty_left
  obtain ⟨y₀, hy₀⟩ := S.nonempty_right
  obtain ⟨w, hw, rfl, rfl⟩ :=
    (hG.vxConnected (S.left_subset hx₀) (S.right_subset hy₀)).exists_isWalk
  rw [← S.not_mem_left_iff (S.right_subset hy₀)] at hy₀
  obtain ⟨e, x, y, hexy, hx, hy⟩ := w.exists_dInc_prop_not_prop hx₀ hy₀
  have h' := hw.inc₂_of_dInc hexy
  rw [S.not_mem_left_iff h'.vx_mem_right] at hy
  refine ⟨S, e, x, y, fun heF ↦ ?_, hx, hy, h'⟩
  exact S.not_adj hx hy <| Inc₂.adj <| h'.of_le_of_mem (by simp) <| by simpa [h'.edge_mem]

-- /-- The subgraph on the left of the separation. -/
-- def Separation.subgraph_left (S : G.Separation) : Graph α β := G.induce S.left

-- /-- The edges on the right of the separation. -/
-- def Separation.subgraph_right (S : G.Separation) : Graph α β := G.induce S.right



lemma Separation.edge_induce_disjoint (S : G.Separation) : Disjoint G[S.left].E G[S.right].E := by
  refine disjoint_left.2 fun e he he' ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq] at he he'
  obtain ⟨x, y, hexy, hx, hy⟩ := he
  obtain ⟨x', y', hexy', hx', hy'⟩ := he'
  obtain rfl | rfl := hexy.left_eq_or_eq_of_inc₂ hexy'
  · exact S.disjoint.not_mem_of_mem_left hx hx'
  exact S.disjoint.not_mem_of_mem_left hx hy'

lemma Separation.eq_union (S : G.Separation) : G = G [S.left] ∪ G [S.right] := by
  refine Graph.ext (by simp [S.union_eq]) fun e x y ↦ ?_
  simp only [(Compatible.of_disjoint_edgeSet S.edge_induce_disjoint).union_inc₂_iff,
    induce_inc₂_iff, ← and_or_left, iff_self_and]
  exact fun h ↦ (S.mem_or_mem h.vx_mem_left).elim
    (.inl ∘ fun h' ↦ ⟨h', S.mem_left_of_adj h' h.adj⟩)
    (.inr ∘ fun h' ↦ ⟨h', S.mem_right_of_adj h' h.adj⟩)

/- ### Unions -/

lemma Compatible.union_connected_of_forall (h : G.Compatible H) (hG : G.Connected)
    (hH : ∀ x ∈ H.V, ∃ y ∈ G.V, H.VxConnected x y) : (G ∪ H).Connected := by
  obtain ⟨v, hv⟩ := hG.nonempty
  refine connected_of_vx (u := v) (by simp [hv]) ?_
  rintro y (hy | hy)
  · exact (hG.vxConnected hy hv).of_le <| left_le_union ..
  obtain ⟨z, hzG, hyz⟩ := hH _ hy
  exact (hyz.of_le h.right_le_union).trans <| (hG.vxConnected hzG hv).of_le <| left_le_union ..

lemma Compatible.union_connected_of_nonempty_inter (h : Compatible G H) (hG : G.Connected)
    (hH : H.Connected) (hne : (G.V ∩ H.V).Nonempty) : (G ∪ H).Connected :=
  let ⟨z, hzG, hzH⟩ := hne
  h.union_connected_of_forall hG fun _ hx ↦ ⟨z, hzG, hH.vxConnected hx hzH⟩

lemma IsWalk.exists_mem_mem_of_union (h : (G ∪ H).IsWalk w) (hG : w.first ∈ G.V)
    (hH : w.last ∈ H.V) : ∃ x ∈ w, x ∈ G.V ∧ x ∈ H.V := by
  by_cases hH' : w.last ∈ G.V
  · exact ⟨w.last, by simp, hH', hH⟩
  obtain ⟨e, x, y, hxy, hx, hy⟩ := w.exists_dInc_prop_not_prop hG hH'
  obtain hxy' | hxy' := inc₂_or_inc₂_of_union <| h.inc₂_of_dInc hxy
  · exact False.elim <| hy <| hxy'.vx_mem_right
  exact ⟨x, hxy.vx_mem_left, hx, hxy'.vx_mem_left⟩

lemma union_not_connected_of_disjoint_vxSet (hV : Disjoint G.V H.V) (hG : G.V.Nonempty)
    (hH : H.V.Nonempty) : ¬ (G ∪ H).Connected := by
  obtain ⟨x, hx⟩ := hG
  obtain ⟨y, hy⟩ := hH
  intro h
  obtain ⟨w, hw, rfl, rfl⟩ :=
    (h.vxConnected (x := x) (y := y) (by simp [hx]) (by simp [hy])).exists_isWalk
  obtain ⟨u, -, huG, huH⟩ := hw.exists_mem_mem_of_union hx hy
  exact hV.not_mem_of_mem_left huG huH

/-- Two vertices of a cycle are connected after deleting any other vertex.  -/
lemma IsCycle.vxConnected_deleteVx_of_mem_of_mem (hC : G.IsCycle C) (x : α) (hy₁ : y₁ ∈ C)
    (hy₂ : y₂ ∈ C) (hne₁ : y₁ ≠ x) (hne₂ : y₂ ≠ x) : (G - ({x} : Set α)).VxConnected y₁ y₂ := by
  obtain rfl | hne := eq_or_ne y₁ y₂
  · simpa [hC.vxSet_subset hy₁]
  obtain ⟨u, e, rfl⟩ | hnt := hC.loop_or_nontrivial
  · simp_all
  by_cases hxC : x ∈ C
  · obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_vx hnt hxC
    refine IsWalk.vxConnected_of_mem_of_mem (w := P) ?_ ?_ ?_
    · simp [hP.isWalk, ← mem_vxSet_iff, ← toGraph_vxSet, hP_eq]
    all_goals simp_all [← mem_vxSet_iff, ← toGraph_vxSet, hP_eq]
  exact IsWalk.vxConnected_of_mem_of_mem (w := C) (by simp [hxC, hC.isWalk]) hy₁ hy₂

 /-- Two vertices of a cycle are connected after deleting any edge. -/
lemma IsCycle.vxConnected_deleteEdge_of_mem_of_mem (hC : G.IsCycle C) (e : β)
    (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) : (G ＼ {e}).VxConnected x₁ x₂ := by
  obtain heC | heC := em' <| e ∈ C.edge
  · exact IsWalk.vxConnected_of_mem_of_mem (by simp [hC.isWalk, heC]) hx₁ hx₂
  obtain ⟨P, hP, hP_eq⟩ := hC.exists_isPath_toGraph_eq_delete_edge heC
  apply IsWalk.vxConnected_of_mem_of_mem (w := P) (by simp [hP.isWalk, ← toGraph_edgeSet, hP_eq])
  all_goals
    rwa [← mem_vxSet_iff, ← toGraph_vxSet, hP_eq, edgeDelete_vxSet, toGraph_vxSet, mem_vxSet_iff]

/-- If two graphs intersect in at most one vertex,
then any cycle of their union is a cycle of one of the graphs. -/
lemma IsCycle.isCycle_or_isCycle_of_union_of_subsingleton_inter (hC : (G ∪ H).IsCycle C)
    (hi : (G.V ∩ H.V).Subsingleton) : G.IsCycle C ∨ H.IsCycle C := by
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
  have aux1 (e) (he : e ∈ C.E) :
      ∃ x y, x ≠ y ∧ x ∈ C.V ∧ y ∈ C.V ∧ (G.Inc₂ e x y ∨ H.Inc₂ e x y) := by
    obtain ⟨x, y, hxy⟩ := C.exists_inc₂_of_mem_edge he
    exact ⟨x, y, hC.ne_of_inc₂ hnt hxy, hxy.vx_mem_left, hxy.vx_mem_right,
      by simpa [hcompat.union_inc₂_iff] using hC.isWalk.inc₂_of_inc₂ hxy ⟩
  -- If the vertices of `C` are contained in `G` or `H`, then `C` is contained in `G` or `H`.
  by_cases hCG : C.V ⊆ G.V
  · refine .inl <| hC.isCycle_of_le (left_le_union ..) fun e heC ↦ ?_
    obtain ⟨x, y, hne, hxC, hyC, hxy | hxy⟩ := aux1 e heC
    · exact hxy.edge_mem
    exact False.elim <| hne <| hi.elim ⟨hCG hxC, hxy.vx_mem_left⟩ ⟨hCG hyC, hxy.vx_mem_right⟩
  by_cases hCH : C.V ⊆ H.V
  · refine .inr <| hC.isCycle_of_le hcompat.right_le_union fun e heC ↦ ?_
    obtain ⟨x, y, hne, hxC, hyC, hxy | hxy⟩ := aux1 e heC
    · exact False.elim <| hne <| hi.elim ⟨hxy.vx_mem_left, hCH hxC⟩ ⟨hxy.vx_mem_right, hCH hyC⟩
    exact hxy.edge_mem
  -- Take a path from a vertex `x` of `C ∩ (G \ H)` to a vertex `y` of `C ∩ (H \ G)`.
  -- This path must intersect `G.V ∩ H.V` in a vertex `a`.
  obtain ⟨x, hxC, hxH⟩ := not_subset.1 hCH
  obtain ⟨y, hyC, hyG⟩ := not_subset.1 hCG
  have hxG : x ∈ G.V := by simpa [hxH] using hC.vxSet_subset hxC
  have hyH : y ∈ H.V := by simpa [hyG] using hC.vxSet_subset hyC
  obtain ⟨w, hw, rfl, rfl⟩ := (hC.isWalk.vxConnected_of_mem_of_mem hxC hyC).exists_isWalk
  obtain ⟨a, -, haG, haH⟩ := hw.exists_mem_mem_of_union hxG hyH
  have hxa : w.first ≠ a := by rintro rfl; contradiction
  have hya : w.last ≠ a := by rintro rfl; contradiction
  -- Now take an `xy`-path in `C` that doesn't use `a`. This must intersect `G.V ∩ H.V`
  -- in another vertex `b`, contradicting the fact that the intersection is a subsingleton.
  obtain ⟨w', hw', h1', h2'⟩ :=
    (hC.vxConnected_deleteVx_of_mem_of_mem a hxC hyC hxa hya).exists_isWalk
  rw [hcompat.vxDelete_union] at hw'
  obtain ⟨b, -, hbG, hbH⟩ :=
    hw'.exists_mem_mem_of_union (by simp [h1', hxG, hxa]) (by simp [h2', hyH, hya])
  rw [vxDelete_vxSet, mem_diff, mem_singleton_iff] at hbG hbH
  refine False.elim <| hbG.2 (hi.elim ?_ ?_) <;> simp_all

lemma Compatible.isCycle_union_iff_of_subsingleton_inter (hcompat : G.Compatible H)
    (hi : (G.V ∩ H.V).Subsingleton) :
    (G ∪ H).IsCycle C ↔ G.IsCycle C ∨ H.IsCycle C :=
  ⟨fun h ↦ h.isCycle_or_isCycle_of_union_of_subsingleton_inter hi,
    fun h ↦ h.elim (fun h' ↦ h'.isCycle_of_ge (left_le_union ..))
    (fun h' ↦ h'.isCycle_of_ge hcompat.right_le_union)⟩

end Graph

namespace WList

/-- A `WList` that is `WellFormed` produces a connected graph. -/
lemma WellFormed.toGraph_connected (hw : w.WellFormed) : w.toGraph.Connected :=
  ⟨by simp, fun x y hx hy ↦
    hw.isWalk_toGraph.vxConnected_of_mem_of_mem (by simpa using hx) (by simpa using hy)⟩

end WList






-- structure VxSeparation (G : Graph α β) (k : ℕ) where
--   left : Set α
--   right : Set α
--   union_eq : left ∪ right = G.V
--   disjoint : Disjoint left right


-- lemma exists_partition_of_not_connected {G : Graph α β} (h : ¬ G.Connected) :
--     ∃ X Y, X.Nonempty ∧ Y.Nonempty ∧



-- section Connected

-- @[simp]
-- def reflAdj (G : Graph α β) (x y : α) :=
--   G.Adj x y ∨ x = y ∧ x ∈ G.V

-- lemma reflAdj.of_vxMem (h : x ∈ G.V) : G.reflAdj x x := by
--   simp only [reflAdj, h, and_self, or_true]

-- @[simp]
-- lemma reflAdj.refl (h : x ∈ G.V) : G.reflAdj x x := reflAdj.of_vxMem h

-- lemma reflAdj.symm (h : G.reflAdj x y) : G.reflAdj y x := by
--   apply h.imp
--   · exact fun h ↦ h.symm
--   · rintro ⟨rfl, hx⟩
--     exact ⟨rfl, hx⟩

-- lemma reflAdj.comm : G.reflAdj x y ↔ G.reflAdj y x := by
--   refine ⟨reflAdj.symm, reflAdj.symm⟩

-- lemma Inc.reflAdj_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.reflAdj x y := by
--   by_cases hxy : x = y
--   · subst y
--     right
--     exact ⟨rfl, hx.vx_mem⟩
--   · left
--     use e
--     rw [inc₂_iff_inc_and_loop]
--     use hx, hy, fun h ↦ (hxy h).elim

-- @[simp]
-- lemma reflAdj.mem_left (h : G.reflAdj x y) : x ∈ G.V := by
--   apply h.elim
--   · exact fun a ↦ a.mem_left
--   · tauto

-- @[simp]
-- lemma reflAdj.mem_right (h : G.reflAdj x y) : y ∈ G.V := by
--   rw [reflAdj.comm] at h
--   exact h.mem_left

-- @[simp]
-- lemma Inc₂.reflAdj (h : G.Inc₂ e x y) : G.reflAdj x y := by
--   left
--   use e

-- @[simp]
-- lemma Adj.reflAdj (h : G.Adj x y) : G.reflAdj x y := by
--   left
--   exact h

-- lemma reflAdj.Adj_of_ne (h : G.reflAdj x y) (hne : x ≠ y) : G.Adj x y := by
--   obtain ⟨e, h⟩ | ⟨rfl, hx⟩ := h
--   · use e
--   · contradiction

-- @[simp]
-- lemma reflAdj.Adj_iff_ne (hne : x ≠ y) : G.reflAdj x y ↔ G.Adj x y :=
--   ⟨fun h => h.Adj_of_ne hne, fun h => h.reflAdj⟩

-- lemma reflAdj.le (h : G.reflAdj u v) (hle : G ≤ H) : H.reflAdj u v := by
--   obtain hadj | ⟨rfl, hu⟩ := h
--   · left
--     exact hadj.le hle
--   · right
--     simp only [vx_subset_of_le hle hu, and_self]


-- def Connected (G : Graph α β) := Relation.TransGen G.reflAdj

-- @[simp]
-- lemma Inc₂.connected (h : G.Inc₂ e x y) : G.Connected x y :=
--   Relation.TransGen.single h.reflAdj

-- @[simp]
-- lemma Adj.connected (h : G.Adj x y) : G.Connected x y := Relation.TransGen.single h.reflAdj

-- @[simp]
-- lemma reflAdj.connected (h : G.reflAdj x y) : G.Connected x y := Relation.TransGen.single h

-- lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
--   Relation.TransGen.single <| reflAdj.of_vxMem hx

-- lemma Inc.connected_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.Connected x y :=
--   reflAdj.connected (hx.reflAdj_of_inc hy)

-- lemma Connected.comm : G.Connected x y ↔ G.Connected y x := by
--   unfold Connected
--   rw [Relation.transGen_swap]
--   congr! 1
--   ext
--   exact reflAdj.comm

-- @[simp]
-- lemma Connected.refl (hx : x ∈ G.V) : G.Connected x x :=
--   connected_self hx

-- @[simp]
-- lemma Connected.exists_connected (hx : x ∈ G.V) : ∃ y, G.Connected x y := by
--   use x, Connected.refl hx

-- lemma Connected.symm (h : G.Connected x y) : G.Connected y x := by
--   rwa [Connected.comm]

-- instance : IsSymm α (G.Connected) := ⟨fun _ _ ↦ Connected.symm⟩

-- lemma Connected.trans (hxy : G.Connected x y) (hyz : G.Connected y z) :
--     G.Connected x z := Relation.TransGen.trans hxy hyz

-- instance : IsTrans α (G.Connected) := ⟨fun _ _ _ ↦ Connected.trans⟩

-- @[simp]
-- lemma Connected.mem_left (hconn : G.Connected x y) : x ∈ G.V := by
--   simp only [Connected, Relation.TransGen.head'_iff, not_exists, not_and, not_or] at hconn
--   obtain ⟨a, hradj, hTG⟩ := hconn
--   exact hradj.mem_left

-- @[simp]
-- lemma Connected.mem_right (hconn : G.Connected x y) : y ∈ G.V := by
--   rw [Connected.comm] at hconn
--   exact hconn.mem_left

-- @[simp]
-- lemma not_connected_of_not_mem (h : x ∉ G.V) : ¬G.Connected x y := by
--   contrapose! h
--   exact h.mem_left

-- @[simp]
-- lemma not_connected_of_not_mem' (h : y ∉ G.V) : ¬G.Connected x y := by
--   rw [Connected.comm]
--   exact not_connected_of_not_mem h

-- @[simp]
-- lemma Connected.refl_iff : G.Connected x x ↔ x ∈ G.V := by
--   refine ⟨?_, Connected.refl⟩
--   rintro h
--   exact h.mem_left

-- lemma Connected.le (h : G.Connected u v) (hle : G ≤ H) : H.Connected u v := by
--   induction h with
--   | single huv => exact Relation.TransGen.single (huv.le hle)
--   | tail huv h ih => exact Relation.TransGen.tail ih (h.le hle)

-- class Conn (G : Graph α β) : Prop where
--   all_conn : ∃ x, ∀ y ∈ G.V, G.Connected x y

-- open Partition

-- def ConnectedPartition (G : Graph α β) : Partition (Set α) := Partition.ofRel (G.Connected)

-- def Component (G : Graph α β) (v : α) := {u | G.Connected v u}

-- def ComponentSets (G : Graph α β) (V : Set α) := {Component G u | u ∈ V}

-- @[simp]
-- lemma ComponentPartition.supp : G.ConnectedPartition.supp = G.V := by
--   simp [ConnectedPartition]

-- @[simp]
-- lemma set_spec_connected_comm : {x | G.Connected x y} = {x | G.Connected y x} := by
--   simp_rw [Connected.comm]

-- @[simp] lemma set_spec_connected_eq_componentSet : {x | G.Connected y x} = G.Component y := rfl

-- @[simp]
-- lemma Component.empty : G.Component x = ∅ ↔ x ∉ G.V := by
--   constructor
--   · intro h hx
--     rw [← mem_empty_iff_false, ← h]
--     exact Connected.refl hx
--   · intro h
--     ext y
--     simp [Component, h]

-- @[simp]
-- lemma Component.eq (hx : x ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y :=
--   (rel_iff_eqv_class_eq_left (Connected.refl hx)).symm

-- @[simp]
-- lemma Component.eq' (hy : y ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y := by
--   rw [eq_comm, Connected.comm, eq hy]

-- @[simp]
-- lemma Component.mem_partition : G.Component x ∈ G.ConnectedPartition ↔ x ∈ G.V := by
--   refine mem_ofRel_iff.trans ?_
--   simp +contextual only [Connected.refl_iff, set_spec_connected_eq_componentSet, iff_def,
--     forall_exists_index, and_imp, eq', eq]
--   refine ⟨fun y hy hconn ↦ hconn.mem_left, fun h ↦ ?_⟩
--   use x, h, Connected.refl h

-- @[simp] lemma Component.mem : y ∈ G.Component x ↔ G.Connected x y := by rfl

-- lemma Component.mem' : y ∈ G.Component x ↔ G.Connected y x := by
--   rw [Connected.comm, Component.mem]

-- -- @[simp] lemma ComponentSet.self_mem : x ∈ G.ComponentSet x ↔ x ∈ G.V := by simp

-- @[simp]
-- lemma ComponentSets.mem (hx : x ∈ G.V) :
--     G.Component x ∈ G.ComponentSets T ↔ ∃ y ∈ T, G.Connected x y := by
--   simp only [ComponentSets, mem_setOf_eq, hx, Component.eq']
--   simp_rw [Connected.comm]

-- lemma ComponentSets.componentSet (hx : x ∈ G.V) :
--     G.ComponentSets (G.Component x) = {G.Component x} := by
--   ext S
--   simp +contextual only [mem_singleton_iff, iff_def, hx, mem, Component.mem, and_self,
--     Connected.exists_connected, implies_true, and_true]
--   rintro ⟨y, hy, rfl⟩
--   simpa [hx, Connected.comm] using hy

-- lemma ConnectedPartition.le (hle : G ≤ H) : G.ConnectedPartition ≤ H.ConnectedPartition := by
--   simpa [ConnectedPartition] using fun u v ↦ (Connected.le · hle)

-- @[simp]
-- lemma ConnectedPartition.Rel : G.ConnectedPartition.Rel = G.Connected := by
--   unfold ConnectedPartition
--   rw [rel_ofRel_eq]

-- def SetConnected (G : Graph α β) (S T : Set α) : Prop := ∃ s ∈ S, ∃ t ∈ T, G.Connected s t

-- namespace SetConnected
-- variable {G : Graph α β} {S S' T T' U V : Set α}

-- lemma refl (h : ∃ x ∈ S, x ∈ G.V) : G.SetConnected S S := by
--   obtain ⟨x, hxS, hxV⟩ := h
--   use x, hxS, x, hxS, Connected.refl hxV

-- lemma symm (h : G.SetConnected S T) : G.SetConnected T S := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   exact ⟨t, ht, s, hs, h.symm⟩

-- lemma comm : G.SetConnected S T ↔ G.SetConnected T S := ⟨SetConnected.symm, SetConnected.symm⟩

-- lemma left_subset (h : G.SetConnected S T) (hS : S ⊆ S') : G.SetConnected S' T := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   use s, hS hs, t, ht

-- lemma right_subset (h : G.SetConnected S T) (hT : T ⊆ T') : G.SetConnected S T' := by
--   rw [SetConnected.comm] at h ⊢
--   exact h.left_subset hT

-- lemma subset (h : G.SetConnected S T) (hS : S ⊆ S') (hT : T ⊆ T') : G.SetConnected S' T' :=
--   (h.left_subset hS).right_subset hT

-- lemma left_supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) T := by
--   constructor
--   · rintro ⟨s, hsS, t, htT, h⟩
--     use s, ⟨hsS, h.mem_left⟩, t, htT
--   · rintro ⟨s, ⟨hsS, hs⟩, t, htT, h⟩
--     use s, hsS, t, htT

-- lemma right_supported : G.SetConnected S T ↔ G.SetConnected S (T ∩ G.V) := by
--   rw [comm, left_supported, comm]

-- lemma supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) (T ∩ G.V) := by
--   rw [left_supported, right_supported]

-- lemma le (h : G.SetConnected S T) (hle : G ≤ H) : H.SetConnected S T := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   exact ⟨s, hs, t, ht, h.le hle⟩

-- @[simp]
-- lemma empty_source : ¬ G.SetConnected ∅ T := by
--   rintro ⟨s, hs, t, ht, h⟩
--   simp at hs

-- @[simp]
-- lemma empty_target : ¬ G.SetConnected S ∅ := by
--   rw [SetConnected.comm]
--   exact empty_source

-- @[simp]
-- lemma nonempty_inter (h : (S ∩ T ∩ G.V).Nonempty) : G.SetConnected S T := by
--   obtain ⟨x, ⟨hxS, hxT⟩, hx⟩ := h
--   use x, hxS, x, hxT, Connected.refl hx

-- lemma exists_mem_left (h : G.SetConnected S T) : ∃ x ∈ S, x ∈ G.V := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   exact ⟨s, hs, h.mem_left⟩

-- lemma exists_mem_right (h : G.SetConnected S T) : ∃ x ∈ T, x ∈ G.V := by
--   rw [SetConnected.comm] at h
--   exact exists_mem_left h

-- end SetConnected
