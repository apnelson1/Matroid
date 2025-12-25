import Matroid.Graph.Walk.Path
import Matroid.Graph.WList.Cycle

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ C C₁ C₂ : WList α β} {S T : Set α}

open WList

lemma WList.WellFormed.rotate_toGraph (hw : w.WellFormed) (h_closed : w.IsClosed) (n : ℕ) :
    (w.rotate n).toGraph = w.toGraph := by
  refine Graph.ext (by simp [h_closed.rotate_vertexSet]) fun e x y ↦ ?_
  rw [(hw.rotate h_closed n).toGraph_isLink, h_closed.isLink_rotate_iff, hw.toGraph_isLink]

namespace Graph

lemma IsWalk.rotate (hw : G.IsWalk w) (hc : w.IsClosed) (n) : G.IsWalk (w.rotate n) := by
  have aux {w'} (hw' : G.IsWalk w') (hc' : w'.IsClosed) : G.IsWalk (w'.rotate 1) := by
    induction hw' with
    | nil => simpa
    | @cons x e w hw h ih =>
      simp only [rotate_cons_succ, rotate_zero]
      obtain rfl : x = w.last := by simpa using hc'
      exact hw.concat h
  induction n with
  | zero => simpa
  | succ n IH => simpa [← rotate_rotate] using aux IH (hc.rotate n)

lemma IsWalk.intRotate (hw : G.IsWalk w) (hc : w.IsClosed) (n) : G.IsWalk (w.intRotate n) :=
  hw.rotate hc _

@[simp]
lemma IsClosed.isWalk_rotate_iff (hc : w.IsClosed) {n} : G.IsWalk (w.rotate n) ↔ G.IsWalk w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.rotate hc _⟩
  have h' := h.intRotate (hc.rotate _) (-n)
  rwa [← hc.intRotate_eq_rotate, hc.intRotate_intRotate, add_neg_cancel, intRotate_zero] at h'


/-- `G.IsCycle C` means that `C` is a nonempty closed walk with no repeated vertices or edges. -/
@[mk_iff]
structure IsCycle (G : Graph α β) (C : WList α β) : Prop extends G.IsTrail C where
  nonempty : C.Nonempty
  /-- The start and end vertex are the same -/
  isClosed : C.IsClosed
  /-- There are no repeated vertices except for the first and last. -/
  nodup : C.tail.vertex.Nodup

/-- If `C` has at least three edges, then the assumption that `C` has distinct edges follows
from its distinct vertices, so is not needed. -/
lemma IsWalk.isCycle_of_closed_nodup (hC : G.IsWalk C) (hlen : 2 < C.length)
    (h_closed : C.IsClosed) (nodup : C.tail.vertex.Nodup) : G.IsCycle C where
  isWalk := hC
  edge_nodup := by
    cases C with | nil  => simp | cons u e W =>
    simp only [cons_edge, List.nodup_cons]
    simp only [cons_isWalk_iff] at hC
    simp only [tail_cons] at nodup
    obtain rfl : u = W.last := h_closed
    refine ⟨fun heW ↦ ?_, IsTrail.edge_nodup (G := G) (IsPath.isTrail ⟨hC.2, nodup⟩)⟩
    cases W with | nil => simp at hlen | cons v f W =>
    simp only [cons_vertex, List.nodup_cons, mem_vertex] at nodup
    have hne : W.first ≠ W.last := by simpa [← first_ne_last_iff nodup.2] using hlen
    simp only [last_cons, first_cons, cons_isWalk_iff] at hC
    obtain (rfl : e = f) | (heW : e ∈ W.edge) := by simpa using heW
    · exact hne <| hC.2.1.right_unique hC.1.symm
    exact nodup.1 <| hC.2.2.vertex_mem_of_edge_mem heW hC.1.inc_right
  nonempty := by cases C with simp_all
  isClosed := h_closed
  nodup := nodup

lemma IsCycle.idxOf_get [DecidableEq α] (hC : G.IsCycle C) {n} (hn : n < C.length) :
    C.idxOf (C.get n) = n := hC.isClosed.idxOf_get hC.nodup hn

lemma IsCycle.isTrail (hC : G.IsCycle C) : G.IsTrail C where
  isWalk := hC.isWalk
  edge_nodup := hC.edge_nodup

lemma IsCycle.rotate (hC : G.IsCycle C) (n : ℕ) : G.IsCycle (C.rotate n) where
  nonempty := by simpa using hC.nonempty
  isWalk := hC.isWalk.rotate hC.isClosed n
  edge_nodup := by simpa using hC.edge_nodup
  isClosed := hC.isClosed.rotate n
  nodup := by simpa [rotate_vertex_tail, List.nodup_rotate] using hC.nodup

@[simp]
lemma not_isCycle_nil (x : α) : ¬ G.IsCycle (nil x : WList α β) :=
  fun h ↦ by simpa using h.nonempty

lemma IsCycle.intRotate (hC : G.IsCycle C) (n : ℤ) : G.IsCycle (C.intRotate n) :=
  hC.rotate ..

lemma IsCycle.tail_isPath (hC : G.IsCycle C) : G.IsPath C.tail where
  isWalk := hC.isWalk.suffix <| tail_isSuffix C
  nodup := hC.nodup

lemma IsCycle.dropLast_isPath (hC : G.IsCycle C) : G.IsPath C.dropLast := by
  have h := (hC.intRotate (-1)).isClosed.rotate_one_dropLast
  rw [← IsClosed.intRotate_eq_rotate, hC.isClosed.intRotate_intRotate] at h
  · simp only [Int.reduceNeg, Int.cast_ofNat_Int, neg_add_cancel, intRotate_zero] at h
    rw [h]
    exact (hC.intRotate (-1)).tail_isPath
  exact (hC.intRotate _).isClosed

lemma IsCycle.tail_dropLast_isPath (hC : G.IsCycle C) : G.IsPath C.tail.dropLast :=
  hC.tail_isPath.prefix C.tail.dropLast_isPrefix

lemma IsCycle.mem_tail_dropLast_of_ne_first (hC : G.IsCycle C) (hxC : x ∈ C) (hx : x ≠ C.first) :
    x ∈ C.tail.dropLast := by
  rwa [mem_iff_eq_first_or_mem_tail, or_iff_right hx, mem_iff_eq_mem_dropLast_or_eq_last,
    tail_last, ← hC.isClosed, or_iff_left hx] at hxC

lemma IsCycle.tail_dropLast_vertexSet (hC : G.IsCycle C) (hnt : C.Nontrivial) :
    V(C.tail.dropLast) = V(C) \ {C.first} := by
  cases C with
  | nil => simp at hC
  | cons u e w =>
    simp only [tail_cons, cons_vertexSet, first_cons, Set.mem_singleton_iff, Set.insert_diff_of_mem]
    rw [dropLast_vertexSet_of_nodup (by simpa using hC.tail_isPath.nodup) (by simpa using hnt),
      show u = w.last from hC.isClosed]

lemma IsCycle.reverse (hC : G.IsCycle C) : G.IsCycle C.reverse where
  isWalk := hC.isWalk.reverse
  edge_nodup := by simpa using hC.edge_nodup
  nonempty := by simp [hC.nonempty]
  isClosed := by simp [hC.isClosed]
  nodup := by simp [hC.dropLast_isPath.nodup]

lemma IsCycle.of_le (hC : H.IsCycle C) (hle : H ≤ G) : G.IsCycle C where
  isWalk := hC.isWalk.of_le hle
  edge_nodup := hC.edge_nodup
  nonempty := hC.nonempty
  isClosed := hC.isClosed
  nodup := hC.nodup

lemma IsCycle.isCycle_of_ge (h : H.IsCycle w) (hle : H ≤ G) : G.IsCycle w where
  isWalk := h.isWalk.of_le hle
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed
  nodup := h.nodup

lemma IsCycle.isCycle_of_le (h : G.IsCycle w) (hle : H ≤ G) (hE : E(w) ⊆ E(H)) :
    H.IsCycle w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE h.nonempty
  edge_nodup := h.edge_nodup
  nonempty := h.nonempty
  isClosed := h.isClosed
  nodup := h.nodup

lemma IsCycle.eq_loop_of_isLink_self (h : G.IsCycle C) (hC : C.IsLink e x x) :
    C = cons x e (nil x) := by
  cases C with
  | nil u => simp at hC
  | cons u f w =>
    have hnd : w.vertex.Nodup := by simpa using h.tail_isPath.nodup
    rw [isLink_iff_dInc, or_self, dInc_cons_iff] at hC
    obtain rfl : u = w.last := by simpa using h.isClosed
    obtain ⟨rfl, rfl, hu⟩ | h' := hC
    · cases w with simp_all
    rw [List.nodup_iff_sublist] at hnd
    exact False.elim <| hnd x h'.sublist

lemma IsCycle.isCycle_toGraph (hC : G.IsCycle C) : C.toGraph.IsCycle C :=
  hC.isCycle_of_le hC.isWalk.toGraph_le <| by simp

lemma IsCycle.ne_of_isLink (hC : G.IsCycle C) (hnt : C.Nontrivial) (hinc : C.IsLink e x y) :
    x ≠ y := by
  rintro rfl
  obtain ⟨x, e, rfl⟩ := hC.eq_loop_of_isLink_self hinc
  simp at hnt

lemma IsCycle.length_eq_one_iff (h : G.IsCycle C) : C.length = 1 ↔ ∃ x e, C = cons x e (nil x) := by
  cases C with
  | nil => simp
  | cons u e w =>
    suffices w.Nil → w = nil u by simpa +contextual [iff_def]
    rw [show u = w.last from h.isClosed]
    exact Nil.eq_nil_last

lemma IsCycle.length_eq_two_iff (h : G.IsCycle C) :
    C.length = 2 ↔ ∃ x y e f, x ≠ y ∧ e ≠ f ∧ C = cons x e (cons y f (nil x)) := by
  cases C with
  | nil => simp
  | cons u e' w => cases w with
    | nil => simp
    | cons v e'' w =>
      obtain ⟨⟨he : e' ≠ e'', -⟩, -⟩ := by simpa using h.edge_nodup
      obtain ⟨hvw : v ∉ w, -⟩ := by simpa using h.tail_isPath.nodup
      suffices w.Nil ↔ w = nil w.last by
        simpa [he, show u = w.last from h.isClosed, show w.last ≠ v by rintro rfl; simp_all]
      exact ⟨Nil.eq_nil_last, fun h ↦ by rw [h]; simp⟩

lemma IsCycle.encard_vxSet (h : G.IsCycle C) : V(C).encard = C.length := by
  rw [← h.nonempty.cons_tail, cons_length, cons_vertexSet, Set.insert_eq_of_mem,
    encard_vxSet_of_nodup h.nodup, Nat.cast_add, Nat.cast_one]
  rw [h.isClosed.eq, ← tail_last, mem_vertexSet_iff]
  exact last_mem

@[simp]
lemma rotate_toGraph {n : ℕ} (hC : C.IsClosed) (hCwf : C.WellFormed) :
    (C.rotate n).toGraph = C.toGraph := by
  ext a b c
  · simp [hC.mem_rotate]
  simp [hCwf.toGraph_isLink, (hCwf.rotate hC n).toGraph_isLink, hC]

def IsCycleGraph (G : Graph α β) := ∃ C, G.IsCycle C ∧ V(G) ⊆ V(C) ∧ E(G) ⊆ E(C)

lemma IsCycle.toGraph_isCycleGraph (hC : G.IsCycle C) : C.toGraph.IsCycleGraph :=
  ⟨C, hC.isCycle_toGraph, by simp, by simp⟩

lemma isCycleGraph_iff_toGraph_isCycle : G.IsCycleGraph ↔ ∃ C, G.IsCycle C ∧ G = C.toGraph := by
  refine ⟨fun ⟨C, hC, hV, hE⟩ ↦ ?_, fun ⟨C, hC, heq⟩ ↦ heq ▸ hC.toGraph_isCycleGraph⟩
  use C, hC, ext_of_le_le le_rfl hC.isWalk.toGraph_le
    (antisymm (by simpa) <| vertexSet_mono hC.isWalk.toGraph_le)
    (antisymm (by simpa) <| edgeSet_mono hC.isWalk.toGraph_le)

lemma IsCycleGraph.exists_cycle_from (hG : G.IsCycleGraph) (hx : x ∈ V(G)) :
    ∃ C, G.IsCycle C ∧ V(G) ⊆ V(C) ∧ E(G) ⊆ E(C) ∧ C.first = x := by
  obtain ⟨C, hC, hV, hE⟩ := hG
  obtain ⟨n, hn, rfl⟩ := hC.isClosed.exists_rotate_first_eq hC.nonempty (hV hx)
  use (C.rotate n), hC.rotate n
  simp [hC.isClosed.rotate_vertexSet, hE, hV]

/-- Given a cycle graph, it can be oriented to a cyclic walk with an arbitrary starting vertex and
  arbitrary starting edge. -/
lemma IsCycleGraph.exists_cycle_of_isLink (hG : G.IsCycleGraph) (he : G.IsLink e x y) :
    ∃ C, G.IsCycle (cons x e C) ∧ V(G) ⊆ V(cons x e C) ∧ E(G) ⊆ E(cons x e C) ∧ C.first = y := by
  obtain ⟨C, hC, hV, hE⟩ := hG
  rw [← hC.isWalk.isLink_iff_isLink_of_mem <| hE he.edge_mem, isLink_iff_dInc] at he
  obtain h | h := he
  · obtain ⟨w', n, h', rfl⟩ := hC.isClosed.exists_first_of_dInc h
    use w'
    rw [← h', rotate_edgeSet, hC.isClosed.rotate_vertexSet]
    use hC.rotate n
  rw [← dInc_reverse_iff] at h
  obtain ⟨w', n, h', rfl⟩ := reverse_isClosed_iff.mpr hC.isClosed |>.exists_first_of_dInc h
  use w'
  rw [← h', rotate_edgeSet, reverse_edgeSet, hC.reverse.isClosed.rotate_vertexSet,
    reverse_vertexSet]
  use hC.reverse.rotate n

-- lemma IsCycleGraph.exists_cycle_of_adj (hG : G.IsCycleGraph) (hadj : G.Adj x y) :
--     ∃ C, G.IsCycle C ∧ V(G) ⊆ V(C) ∧ E(G) ⊆ E(C) ∧ C.first = x ∧ C.get 1 = y := by
--   obtain ⟨e, he⟩ := hadj
--   obtain ⟨C, hC, hV, hE, rfl⟩ := hG.exists_cycle_of_isLink he
--   use (cons x e C), hC, hV, hE, by simp, by simp

/-- List of vertices in the cycle graph is the cyclic order-/
noncomputable def IsCycleGraph.vertices (hG : G.IsCycleGraph) (hx : x ∈ V(G)) : List α :=
  hG.exists_cycle_from hx |>.choose.vertex.dropLast

lemma IsCycle.exists_isPath (hC : G.IsCycle C) (hnt : C.Nontrivial) : ∃ P u e f,
    G.IsPath P ∧ u ∉ P ∧ e ∉ P.edge ∧ f ∉ P.edge ∧ e ≠ f ∧ C = cons u e (P.concat f u) := by
  refine ⟨C.tail.dropLast, C.first, hC.nonempty.firstEdge, hC.nonempty.lastEdge,
    hC.tail_dropLast_isPath, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dropLast_first, hnt.tail_dropLast]
    exact first_notMem_tail_of_nodup hC.dropLast_isPath.nodup hnt.dropLast_nonempty
  · refine mt (fun h ↦ ?_) (hC.nonempty.firstEdge_notMem_tail hC.edge_nodup)
    exact List.IsPrefix.mem h <| by simpa using List.dropLast_prefix C.tail.edge
  · refine mt (fun h ↦ ?_) (hC.nonempty.lastEdge_notMem_dropLast hC.edge_nodup)
    refine List.IsSuffix.mem h ?_
    simp only [dropLast_edge, tail_edge, ← List.tail_dropLast]
    exact List.tail_suffix C.edge.dropLast
  · refine mt (fun h_eq ↦ ?_) <| hC.nonempty.firstEdge_notMem_tail hC.edge_nodup
    rw [h_eq, ← hnt.tail_lastEdge]
    exact (Nontrivial.tail_nonempty hnt).lastEdge_mem
  cases C with
  | nil => simp at hnt
  | cons u e w =>
    have hw : w.Nonempty := hnt.tail_nonempty
    simpa [show u = w.last from hC.isClosed, hw.lastEdge_cons] using hw.concat_dropLast.symm

/-- An alternative version of `IsCycle.exists_isPath` where the tail and the head
of the cycle are explictly given as paths. -/
lemma IsCycle.exists_isPath' (hC : G.IsCycle C) (hnt : C.Nontrivial) : ∃ P u e f,
    G.IsPath (cons u e P) ∧ G.IsPath (P.concat f u) ∧ e ≠ f ∧ C = cons u e (P.concat f u) := by
  obtain ⟨P, u, e, f, hP, huP, heP, hfP, hef, rfl⟩ := hC.exists_isPath hnt
  use P, u, e, f
  have ht := hC.tail_isPath
  simp only [tail_cons, concat_isPath_iff] at ht
  have ht' := hC.reverse.tail_isPath
  simp only [reverse_cons, concat_reverse, cons_concat, tail_cons, concat_isPath_iff,
    reverse_isPath_iff, reverse_last, mem_reverse] at ht'
  simp [cons_isPath_iff, hP, huP, ht'.2.1.symm, ht.2.1, hef]

lemma IsCycle.exists_isPath_vertex [DecidableEq α] (hC : G.IsCycle C) (hnt : C.Nontrivial)
    (hu : u ∈ C) : ∃ P e f, G.IsPath P ∧ u ∉ P ∧ e ∉ P.edge ∧ f ∉ P.edge ∧ e ≠ f ∧
    C.rotate (C.idxOf u) = cons u e (P.concat f u) := by
  obtain ⟨n, hn, rfl⟩ := hC.isClosed.exists_rotate_first_eq hnt.nonempty hu
  obtain ⟨P, u, e, f, hP, huP, heP, hfP, hne, hP'⟩ := (hC.rotate n).exists_isPath (hnt.rotate n)
  use P, e, f, hP, ?_, heP, hfP, hne, ?_
  · simpa [hP']
  rw [hP', first_cons, ← hP']
  congr
  apply_fun WList.first at hP'
  obtain rfl := by simpa [first_cons] using hP'
  rw [C.rotate_first _ hn.le]
  exact hC.idxOf_get hn

lemma IsCycle.exists_isPath_edge (hC : G.IsCycle C) (hnt : C.Nontrivial)
    (he : e ∈ C.edge) : ∃ n P, G.IsPath P ∧ e ∉ P.edge ∧ C.rotate n = cons P.last e P := by
  obtain ⟨n, hn, hCne, rfl⟩ := exists_rotate_firstEdge_eq he
  obtain ⟨P, u, e, f, heP, hPf, hne, hC'⟩ := (hC.rotate n).exists_isPath' (hnt.rotate n)
  use n, P.concat f u, hPf, ?_, ?_
  · have := by simpa using heP.edge_nodup
    simp [hC', hne, this.1]
  convert hC' using 1
  simp [hC']

lemma IsCycle.loop_or_nontrivial (hC : G.IsCycle C) :
    (∃ x e, C = cons x e (nil x)) ∨ C.Nontrivial := by
  cases hC.nonempty with
  | cons x e w => cases w with | nil u => simp [show x = u from hC.isClosed] | cons => simp

lemma IsCycle.toGraph_vertexDelete_first_eq (hC : G.IsCycle C) (hnt : C.Nontrivial) :
    C.toGraph - ({C.first} : Set α) = C.tail.dropLast.toGraph := by
  obtain ⟨P, u, e, f, hP, huP, heP, hfP, hef, rfl⟩ := hC.exists_isPath hnt
  refine Graph.ext (by simpa) fun g x y ↦ ?_
  have h1 : P.IsLink g x y → x ∈ P := fun h ↦ h.left_mem
  have h2 : P.IsLink g x y → y ∈ P := fun h ↦ h.right_mem
  simp only [vertexDelete_isLink_iff, hC.isWalk.wellFormed.toGraph_isLink, isLink_cons_iff',
    concat_first, isLink_concat_iff, tail_cons, dropLast_concat,
    hP.isWalk.wellFormed.toGraph_isLink]
  aesop

lemma IsCycle.vertexSet_nontrivial (hC : G.IsCycle C) (hnt : C.Nontrivial) : V(C).Nontrivial := by
  obtain ⟨P, u, -, -, -, huP, -, -, -, rfl⟩ := hC.exists_isPath hnt
  refine Set.nontrivial_of_exists_ne (x := u) (by simp) ⟨P.first, ?_⟩
  simp [show P.first ≠ u by rintro rfl; simp at huP]

/-- Deleting a vertex from the graph of a nontrivial cycle gives the graph of a path. -/
lemma IsCycle.exists_isPath_toGraph_eq_delete_vertex (hC : G.IsCycle C) (hnt : C.Nontrivial)
    (hx : x ∈ C) : ∃ P, G.IsPath P ∧ P.toGraph = C.toGraph - ({x} : Set α) := by
  wlog hxC : x = C.first generalizing C with aux
  · obtain ⟨n, -, rfl⟩ := exists_rotate_first_eq hx
    obtain ⟨P, hP, hP'⟩ := aux (C := C.rotate n) (hC.rotate n) (hnt.rotate n) (by simp) rfl
    exact ⟨P, hP, by rw [hP', WellFormed.rotate_toGraph hC.isWalk.wellFormed hC.isClosed]⟩
  exact ⟨_, hC.tail_dropLast_isPath, by rw [hxC, hC.toGraph_vertexDelete_first_eq hnt]⟩

lemma IsCycle.exists_isPath_toGraph_eq_delete_edge_of_isLink (hC : G.IsCycle C)
    (he : C.IsLink e x y) :
    ∃ P, G.IsPath P ∧ P.toGraph = C.toGraph ＼ {e} ∧ P.first = x ∧ P.last = y := by
  wlog he' : C.DInc e y x with aux
  · obtain hxy | hxy := isLink_iff_dInc.1 he.symm
    · exact aux hC he hxy
    obtain ⟨P, hP, hPC, rfl, rfl⟩ := aux hC he.symm hxy
    exact ⟨P.reverse, hP.reverse, by rwa [hP.isWalk.wellFormed.reverse_toGraph], by simp⟩
  clear he
  wlog hxC : e = hC.nonempty.firstEdge generalizing C with aux
  · obtain ⟨n, -, _, rfl⟩ := exists_rotate_firstEdge_eq he'.edge_mem
    simpa [hC.isWalk.wellFormed.rotate_toGraph hC.isClosed] using
      aux (hC.rotate n) (hC.isClosed.dInc_rotate he' n) rfl
  refine ⟨C.tail, hC.tail_isPath, Graph.ext (by simp [hC.isClosed.vertexSet_tail])
    fun f z z' ↦ ?_, ?_⟩
  · rw [hC.tail_isPath.isWalk.wellFormed.toGraph_isLink, edgeDelete_isLink, Set.mem_singleton_iff,
      hC.isWalk.wellFormed.toGraph_isLink, hC.nonempty.tail_isLink_iff hC.edge_nodup, ← hxC]
  rw [tail_last, ← hC.isClosed.eq, and_comm, ← hC.toIsTrail.dInc_iff_eq_of_dInc he', hxC]
  cases C with | _ => simp_all

/-- Deleting an edge from the graph of a cycle gives the graph of a path. -/
lemma IsCycle.exists_isPath_toGraph_eq_delete_edge (hC : G.IsCycle C) (heC : e ∈ C.edge) :
    ∃ P, G.IsPath P ∧ P.toGraph = C.toGraph ＼ {e} := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edge heC
  obtain ⟨P, hP, hPC, -, -⟩ := hC.exists_isPath_toGraph_eq_delete_edge_of_isLink h
  exact ⟨P, hP, hPC⟩

lemma IsPath.cons_isCycle {P : WList α β} (hP : G.IsPath P) (he : G.IsLink e P.first P.last)
    (heP : e ∉ P.edge) : G.IsCycle (cons P.last e P) where
  isWalk := by simp [he.symm, hP.isWalk]
  edge_nodup := by simp [heP, hP.edge_nodup]
  nonempty := by simp
  isClosed := by simp
  nodup := by simp [hP.nodup]

/-- If `P` is nontrivial, then the edge assumption from `IsPath.cons_isCycle` isn't needed. -/
lemma IsPath.cons_isCycle_of_nontrivial {P : WList α β} (hP : G.IsPath P)
    (he : G.IsLink e P.first P.last) (hPnt : P.Nontrivial) : G.IsCycle (cons P.last e P) := by
  refine IsWalk.isCycle_of_closed_nodup (by simp [he.symm, hP.isWalk]) ?_ (by simp)
    (by simp [hP.nodup])
  have := hPnt.one_lt_length
  rw [cons_length]
  omega

lemma IsPath.concat_isCycle {P : WList α β} (hP : G.IsPath P) (he : G.IsLink e P.last P.first)
    (heP : e ∉ P.edge) : G.IsCycle (P.concat e P.first) := by
  simpa using (hP.reverse.cons_isCycle (e := e) (by simpa using he) (by simpa)).reverse

end Graph
