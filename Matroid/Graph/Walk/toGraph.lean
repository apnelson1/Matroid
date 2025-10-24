import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Subgraph.Union
import Matroid.Graph.Constructions.Small

variable {α β ι ι' : Type*} [CompleteLattice α] {x y z u v : α} {e f : β} {W w : WList α β}
  {G G₁ G₂ H H₁ H₂ : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open scoped Sym2
open WList Set Function Partition Graph

namespace Graph

lemma IsWalk.isWalk_left_of_subset (hw : (G ∪ H).IsWalk w) (hG : Agree {G, H}) (hE : E(w) ⊆ E(G))
    (h1 : w.first ∈ V(G)) : G.IsWalk w := by
  induction hw with
  | nil => simp_all
  | @cons x e w hw h ih =>
    simp_all only [union_eq_sUnion', mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
      sUnion'_isLink, exists_eq_or_imp, ↓existsAndEq, true_and, cons_edgeSet, insert_subset_iff,
      first_cons, cons_isWalk_iff, forall_const]
    have hlink : G.IsLink e x w.first :=
      h.elim id (fun hH ↦ hH.isLink_of_agree_of_edge_mem hG (by simp) (by simp) hE.1)
    exact ⟨hlink, ih hlink.right_mem⟩

lemma IsWalk.isWalk_left_of_subset_of_nonempty (hw : (G ∪ H).IsWalk w) (hG : Agree {G, H})
    (hE : E(w) ⊆ E(G)) (hne : w.Nonempty) : G.IsWalk w := by
  by_cases h1 : w.first ∈ V(G)
  · exact hw.isWalk_left_of_subset hG hE h1
  cases w with
  | nil => simp_all
  | cons u e w =>
  simp_all only [union_eq_sUnion', mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
    cons_isWalk_iff, sUnion'_isLink, exists_eq_or_imp, ↓existsAndEq, true_and, cons_edgeSet,
    cons_nonempty, first_cons, insert_subset_iff]
  have hlink : G.IsLink e u w.first :=
    hw.1.elim id (fun hH ↦ hH.isLink_of_agree_of_edge_mem hG (by simp) (by simp) hE.1)
  exact ⟨hlink, (h1 hlink.left_mem).elim⟩

end Graph

namespace WList

/-- Turn `w : WList (Set α) β` into a `Graph α β`. If the list is not well-formed
(i.e. it contains an edge appearing twice with different ends),
then the first occurence of the edge determines its ends in `w.toGraph`. -/
protected noncomputable def toGraph : WList α β → Graph α β
  | nil u => Graph.noEdge (indiscrete' u) β
  | cons u e w => w.toGraph ∪ (banana u w.first {e})

@[simp]
lemma toGraph_nil : (WList.nil u (β := β)).toGraph = Graph.noEdge (indiscrete' u) β := rfl

lemma toGraph_cons : (w.cons u e).toGraph = w.toGraph ∪ (banana u w.first {e}) := rfl

lemma toGraph_concat (w : WList (Set α) β) (e u) :
    (w.concat e u).toGraph = (banana u w.last {e}) ∪ w.toGraph := by
  induction w with
  | nil v =>
    simp only [concat, toGraph_cons, toGraph_nil, nil_first, banana_comm, nil_last]
    refine Graph.ext ?_ fun f x y ↦ ?_
    · rw [union_vertexSet, union_vertexSet, sup_eq_right.mpr, sup_eq_left.mpr] <;> simp
    rw [noEdge_union_eq_self.mpr (by simp), union_noEdge_eq_self.mpr (by simp)]
  | cons v f w ih =>
    apply vertexPartition_ext ?_ fun f' x y ↦ ?_
    · simp [concat, sup_assoc, toGraph_cons, ih]
    simp [concat, toGraph_cons, ih, Graph.union_assoc]

@[simp]
lemma toGraph_vertexSet (w : WList (Set α) β) : V(w.toGraph) = V(w) \ {∅} := by
  induction w with
  | nil u =>
    ext x
    simp +contextual [and_comm]
  | cons u e w ih =>
    simp_all [toGraph_cons]

@[simp]
lemma toGraph_edgeSet (w : WList α β) : E(w.toGraph) = E(w) := by
  induction w with simp_all [toGraph_cons]

lemma toGraph_vertexSet_nonempty (w : WList α β) : V(w.toGraph).Nonempty := by
  simp

lemma WellFormed.toGraph_isLink (h : w.WellFormed) : w.toGraph.IsLink = w.IsLink := by
  ext e x y
  induction w with
  | nil => simp
  | cons u f w ih =>
    rw [cons_wellFormed_iff] at h
    rw [toGraph_cons, union_isLink, isLink_cons_iff, ih h.1, toGraph_edgeSet, mem_edgeSet_iff,
      singleEdge_isLink_iff, eq_comm (a := e), iff_def, or_imp, and_iff_right (by tauto), or_imp,
      and_iff_left (by tauto)]
    rintro ⟨rfl, h_eq⟩
    rw [and_iff_right rfl, and_iff_right h_eq, ← imp_iff_or_not]
    intro hf
    obtain ⟨y₁, y₂, hinc⟩ := exists_isLink_of_mem_edge hf
    rw [← h.2 y₁ y₂ hinc] at h_eq
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Sym2.eq_iff.1 h_eq
    · assumption
    exact hinc.symm

lemma IsSublist.toGraph_le (h : w₁.IsSublist w₂) (hw₂ : w₂.WellFormed) :
    w₁.toGraph ≤ w₂.toGraph where
  vertex_subset := by
    refine fun x hx ↦ ?_
    simp only [toGraph_vertexSet, mem_vertexSet_iff] at hx ⊢
    exact h.mem hx
  isLink_of_isLink e x y h' := by
    rw [hw₂.toGraph_isLink]
    rw [(hw₂.sublist h).toGraph_isLink] at h'
    exact h'.of_isSublist h

lemma WellFormed.reverse_toGraph (h : w.WellFormed) : w.reverse.toGraph = w.toGraph :=
    Graph.ext (by simp) fun e x y ↦ by
    rw [h.toGraph_isLink, h.reverse.toGraph_isLink, isLink_reverse_iff]

lemma WellFormed.isWalk_toGraph (hw : w.WellFormed) : w.toGraph.IsWalk w := by
  induction w with
  | nil => simp
  | cons u e w ih =>
    rw [cons_wellFormed_iff] at hw
    refine ((ih hw.1).of_le (by simp [toGraph_cons])).cons ?_
    suffices w.toGraph.IsLink e u w.first ∨ e ∉ w.edge by simpa [toGraph_cons, union_isLink_iff]
    rw [← imp_iff_or_not]
    intro he
    obtain ⟨y₁, y₂, h⟩ := exists_isLink_of_mem_edge he
    rw [((ih hw.1).isLink_of_isLink h).isLink_iff_sym2_eq, hw.2 _ _ h]

end WList

namespace Graph

lemma IsWalk.toGraph_le (h : G.IsWalk w) : w.toGraph ≤ G := by
  induction w with
  | nil u => simpa [WList.toGraph] using h
  | cons u e W ih =>
    simp only [cons_isWalk_iff] at h
    exact Graph.union_le (ih h.2) (by simpa using h.1)

lemma _root_.WList.WellFormed.toGraph_le_iff (hW : W.WellFormed) : W.toGraph ≤ G ↔ G.IsWalk W := by
  refine ⟨fun hle ↦ ?_, IsWalk.toGraph_le⟩
  induction W with
  | nil => simpa using hle
  | cons u e W IH =>
    simp_all only [cons_isWalk_iff]
    rw [cons_wellFormed_iff] at hW
    rw [toGraph_cons, Compatible.union_le_iff] at hle
    · simp only [singleEdge_le_iff] at hle
      refine ⟨hle.2, IH hW.1 hle.1⟩
    rw [compatible_comm, singleEdge_compatible_iff, toGraph_edgeSet, mem_edgeSet_iff]
    intro he
    obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edge he
    have := hW.2 _ _ hexy
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := this
    · rwa [hW.1.toGraph_isLink]
    rw [hW.1.toGraph_isLink]
    exact hexy.symm

lemma IsWalk.edgeSet_subset_induce_edgeSet (hw : G.IsWalk w) : E(w) ⊆ E(G[V(w)]) := by
  intro e hew
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edge hew
  rw [(hw.isLink_of_isLink h).mem_induce_iff]
  exact ⟨h.left_mem, h.right_mem⟩

lemma IsWalk.toGraph_eq_induce_restrict (h : G.IsWalk w) : w.toGraph = G[V(w)] ↾ E(w) := by
  induction w with
  | nil => ext <;> simp
  | cons u e w ih =>
    have hss' := h.edgeSet_subset_induce_edgeSet
    simp_all only [cons_isWalk_iff, cons_vertexSet, cons_edgeSet, forall_const]
    rw [toGraph_cons, ih]
    refine G.ext_of_le_le (Graph.union_le ?_ ?_) ?_ (by simp) ?_
    · exact (edgeRestrict_le ..).trans (induce_le h.2.vertexSet_subset)
    · simpa using h.1
    · refine (edgeRestrict_le ..).trans (induce_le ?_)
      simp [insert_subset_iff, h.1.left_mem, h.2.vertexSet_subset]
    simp only [union_edgeSet, edgeRestrict_edgeSet, singleEdge_edgeSet, union_singleton]
    rw [inter_eq_self_of_subset_left h.2.edgeSet_subset_induce_edgeSet,
      inter_eq_self_of_subset_left hss']

lemma IsWalk.le_of_edgeSet_subset (hw₁ : G.IsWalk w₁) (hne : w₁.Nonempty) (hw₂ : G.IsWalk w₂)
    (hss : E(w₁) ⊆ E(w₂)) : w₁.toGraph ≤ w₂.toGraph := by
  have h₁ := hw₁.toGraph_le
  have h₂ := hw₂.toGraph_le
  refine G.le_of_le_le_subset_subset h₁ h₂ (fun x hxV ↦ ?_) (by simpa using hss)
  rw [toGraph_vertexSet, mem_vertexSet_iff, hne.mem_iff_exists_isLink] at hxV
  obtain ⟨y, e, h⟩ := hxV
  have hew₂ := hss h.edge_mem
  rw [hw₁.isLink_iff_isLink_of_mem h.edge_mem, ← hw₂.isLink_iff_isLink_of_mem hew₂] at h
  simpa using h.left_mem

lemma WList.WellFormed.rotate_toGraph (hw : w.WellFormed) (h_closed : w.IsClosed) (n : ℕ) :
    (w.rotate n).toGraph = w.toGraph := by
  refine Graph.ext (by simp [h_closed.rotate_vertexSet]) fun e x y ↦ ?_
  rw [(hw.rotate h_closed n).toGraph_isLink, h_closed.isLink_rotate_iff, hw.toGraph_isLink]

lemma IsCycle.isCycle_toGraph (hC : G.IsCycle C) : C.toGraph.IsCycle C :=
  hC.isCycle_of_le hC.isWalk.toGraph_le <| by simp

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

end Graph
