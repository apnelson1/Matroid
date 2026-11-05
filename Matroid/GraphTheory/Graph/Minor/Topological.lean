module

public import Matroid.Graph.Subdivision
public import Matroid.Graph.Minor.Defs

/-!
# Topological minors, subdivisions, and contraction

This file is the bridge between topological-minor theory and the ordinary graph-minor API.
Its central theorem is stronger than merely saying that a subdivision gives a minor:

* a label-coherent subdivision contracts *exactly* back to its pattern, by contracting precisely
  the host edges that are not pattern-edge labels;
* a general topological-minor witness therefore exhibits its pattern as a contraction of its
  `usedSubgraph`;
* `TopologicalMinor.isMinor` is a short corollary.

The contraction branch at a pattern vertex is built by splitting every incident route at the
route's distinguished pattern edge.  The prefix/suffix lemmas below isolate that geometry into
small statements before constructing a `minorMap`.
-/

@[expose] public section

variable {α β γ δ : Type*} {G H K : Graph α β} {J : Graph γ δ} {u v x y z : α} {e f : β}

open Set WList Function

namespace Graph

namespace Subdivision

variable (S : H.Subdivision G) [DecidableEq α] [DecidableEq β]

/-! ## Contraction branches of a subdivision -/

/-- Vertices on the side of the route of `e` that contracts to `v`.

The distinguished edge label `e` is retained.  The prefix before `e` contracts toward the first
end and the suffix after `e` contracts toward the last end.  For a loop both sides belong to the
same branch. -/
def branchVerts (e : E(H)) (v : α) : Set α := by
  let w := S.route e
  exact (if w.first = v then V(w.prefixUntilEdgeLabel e.val) else ∅) ∪
    (if w.last = v then V(w.suffixFromEdgeLabel e.val) else ∅)

/-- Edges on the side(s) of the route of `e` that contract to `v`. -/
def branchEdges (e : E(H)) (v : α) : Set β := by
  let w := S.route e
  exact (if w.first = v then E(w.prefixUntilEdgeLabel e.val) else ∅) ∪
    (if w.last = v then E(w.suffixFromEdgeLabel e.val) else ∅)

@[grind =]
lemma branchVerts_eq_prefix (e : E(H)) (hv : v = (S.route e).first)
    (hne : (S.route e).first ≠ (S.route e).last) :
    S.branchVerts e v = V((S.route e).prefixUntilEdgeLabel e.val) := by
  have hvfirst : (S.route e).first = v := hv.symm
  have hvlast : (S.route e).last ≠ v := hvfirst ▸ hne.symm
  simp [branchVerts, ite_eq_left hvfirst, ite_eq_right hvlast]

@[grind =]
lemma branchVerts_eq_union (e : E(H)) (hv : v = (S.route e).first)
    (hloop : (S.route e).first = (S.route e).last) : S.branchVerts e v =
    V((S.route e).prefixUntilEdgeLabel e.val) ∪ V((S.route e).suffixFromEdgeLabel e.val) := by
  have hvfirst : (S.route e).first = v := hv.symm
  have hvlast : (S.route e).last = v := (hv.trans hloop).symm
  simp [branchVerts, ite_eq_left hvfirst, ite_eq_left hvlast]

@[grind =]
lemma branchVerts_eq_suffix (e : E(H)) (hv : v = (S.route e).last)
    (hne : (S.route e).first ≠ (S.route e).last) :
    S.branchVerts e v = V((S.route e).suffixFromEdgeLabel e.val) := by
  have hvlast : (S.route e).last = v := hv.symm
  have hvfirst : (S.route e).first ≠ v := hvlast ▸ hne
  simp [branchVerts, ite_eq_right hvfirst, ite_eq_left hvlast]

lemma branchVerts_subset_route (e : E(H)) (v : α) : S.branchVerts e v ⊆ V(S.route e) := by
  rintro z hz
  simp only [branchVerts, mem_union, mem_ite_empty_right, mem_vertexSet_iff] at hz
  obtain ⟨-, hz⟩ | ⟨-, hz⟩ := hz
  · exact (S.route e).prefixUntilEdge_isPrefix (· = e.val) |>.subset hz
  exact (S.route e).suffixFromEdge_isSuffix (· = e.val) |>.subset hz

lemma branchVerts_subset_host (e : E(H)) (v : α) : S.branchVerts e v ⊆ V(G) :=
  (S.branchVerts_subset_route e v).trans (S.toTopologicalMinor.route_isTrail e).vertexSet_subset

lemma branchEdges_subset_route (e : E(H)) (v : α) : S.branchEdges e v ⊆ E(S.route e) := by
  intro g hg
  simp only [branchEdges, mem_union, mem_ite_empty_right] at hg
  obtain ⟨-, hg⟩ | ⟨-, hg⟩ := hg
  · exact (S.route e).prefixUntilEdge_isPrefix (· = e.val) |>.edge_subset hg
  exact (S.route e).suffixFromEdge_isSuffix (· = e.val) |>.edge_subset hg

lemma branchEdges_subset_host (e : E(H)) (v : α) : S.branchEdges e v ⊆ E(G) :=
  (S.branchEdges_subset_route e v).trans (S.toTopologicalMinor.route_isTrail e).edgeSet_subset

lemma branchVerts_nonempty_iff_mem (e : E(H)) :
    (S.branchVerts e v).Nonempty ↔ v ∈ S.branchVerts e v := by
  obtain rfl | hf := eq_or_ne (S.route e).first v
  · simp only [branchVerts, ↓reduceIte, union_nonempty, vertexSet_nonempty, true_or, mem_union,
      mem_vertexSet_iff, mem_ite_empty_right, true_iff]
    left
    convert first_mem using 1
    exact (S.route e).prefixUntilEdge_isPrefix (· = e.val) |>.first_eq.symm
  obtain rfl | hl := eq_or_ne (S.route e).last v
  · simp only [branchVerts, hf, ↓reduceIte, empty_union, vertexSet_nonempty, mem_vertexSet_iff,
      true_iff]
    convert last_mem using 1
    exact (S.route e).suffixFromEdge_isSuffix (· = e.val) |>.last_eq.symm
  simp [branchVerts, hf, hl]

/-- Splitting a route at its distinguished edge covers every route vertex by one of the two end
branches. -/
lemma mem_branchVerts_first_or_last (e : E(H)) {x : α} (hx : x ∈ S.route e) :
    x ∈ S.branchVerts e (S.route e).first ∨ x ∈ S.branchVerts e (S.route e).last := by
  have h := (S.route e).prefixUntilEdgeLabel_append_cons_suffixFromEdgeLabel
    (S.route_edge_mem e) ▸ hx
  rw [mem_append_iff, mem_cons_iff, ← or_assoc, ← mem_iff_eq_mem_vertex_dropLast_or_eq_last] at h
  grind [branchVerts]

/-- A branch at `v` contains no other pattern vertex. -/
lemma branchVerts_inter_vertexSet (e : E(H)) (v : α) : S.branchVerts e v ∩ V(H) ⊆ {v} := by
  rintro x ⟨hxv, hxH⟩
  simp only [branchVerts, mem_union, mem_ite_empty_right, mem_vertexSet_iff] at hxv
  obtain ⟨rfl, h1⟩ | ⟨rfl, h2⟩ := hxv
  · have hxdl := S.route e |>.prefixUntilEdge_vertex_isPrefix_dropLast
      (by use e.val, S.route_edge_mem e) |>.mem h1
    have hnot := (S.route_internal_disjoint_branchVertices e).notMem_of_mem_right hxH
    simp only [internalVertexSet, mem_ofPred_eq] at hnot
    rw [← List.tail_dropLast] at hnot
    rw [List.mem_iff_eq_head_or_mem_tail (List.ne_nil_of_mem hxdl)] at hxdl
    rw [hxdl.resolve_right hnot, ← vertex_head, mem_singleton_iff, List.head_dropLast]
  have hxT := (S.route e |>.suffixFromEdge_vertex_isSuffix_tail
    (by use e.val, S.route_edge_mem e)).mem h2
  have hnot := (S.route_internal_disjoint_branchVertices e).notMem_of_mem_right hxH
  simp only [internalVertexSet, mem_ofPred_eq] at hnot
  rw [List.mem_iff_mem_dropLast_or_eq_getLast (List.ne_nil_of_mem hxT)] at hxT
  rw [hxT.resolve_left hnot, ← vertex_getLast, mem_singleton_iff, List.getLast_tail]

/-- Contraction branches at distinct pattern vertices are disjoint. -/
lemma branchVerts_disjoint_of_vertex_ne (e f : E(H)) (u v : V(H)) (hne : u ≠ v) :
    Disjoint (S.branchVerts e u) (S.branchVerts f v) := by
  obtain rfl | hfe := eq_or_ne f e
  · obtain hc | hp := S.route_isSimple f |>.symm
    · obtain hxf | hxf := eq_or_ne (S.route f).first u
      · have hyl : (S.route f).last ≠ v :=
          hc.isClosed ▸ (hne <| Subtype.coe_inj.mp <| hxf.symm.trans ·)
        simp [hxf, hyl, Subtype.coe_ne_coe.mpr hne, branchVerts]
      have hxl : (S.route f).last ≠ u := by rwa [← hc.isClosed]
      simp [hxf, hxl, branchVerts]
    have hdj : Disjoint V((S.route f).prefixUntilEdgeLabel f.val)
        V((S.route f).suffixFromEdgeLabel f.val) := by
      rw [← (S.route f).prefixUntilEdgeLabel_append_cons_suffixFromEdgeLabel (S.route_edge_mem f),
        ← (S.route f |>.suffixFromEdgeLabel f.val).nil_append (x := u.val), ← cons_append,
        ← append_assoc] at hp
      exact hp.disjoint_of_append_append rfl (by simp)
    simp only [branchVerts]
    split_ifs <;> grind
  refine disjoint_left.mpr fun z hzx hzy ↦ ?_
  obtain rfl | rfl := S.toTopologicalMinor.eq_end_of_mem_of_mem_route (e := f) (f := e)
    (by simpa using hfe) (S.branchVerts_subset_route f v hzy)
    (S.branchVerts_subset_route e u hzx) <;>
  have hzx' := S.branchVerts_inter_vertexSet e u
    ⟨hzx, by grind [S.toTopologicalMinor.route_isLink f]⟩ <;>
  have hzy' := S.branchVerts_inter_vertexSet f v
    ⟨hzy, by grind [S.toTopologicalMinor.route_isLink f]⟩ <;>
  exact hne (Subtype.ext <| hzx'.symm.trans hzy')

/-- The distinguished pattern edge is never contracted by either side of its route. -/
lemma edge_notMem_branchEdges (e : E(H)) (v : α) : e.val ∉ S.branchEdges e v := by
  simp only [branchEdges, mem_union, mem_ite_empty_right, not_or]
  constructor <;> rintro ⟨_, he⟩
  · exact (S.route e).prefixUntilEdgeLabel_edge_notMem he
  exact (S.route e).suffixFromEdgeLabel_edge_notMem
    (S.toTopologicalMinor.route_isTrail e).edge_nodup he

/-- Every route edge other than the distinguished retained edge lies on the contraction side of
one of the two route ends. -/
lemma mem_branchEdges_first_or_last_of_ne (e : E(H)) {g : β} (hg : g ∈ E(S.route e))
    (hne : g ≠ e.val) :
    g ∈ S.branchEdges e (S.route e).first ∨ g ∈ S.branchEdges e (S.route e).last := by
  have hdecomp := (S.route e).prefixUntilEdgeLabel_append_cons_suffixFromEdgeLabel
    (S.route_edge_mem e)
  rw [← hdecomp, append_edgeSet, cons_edgeSet, mem_union, mem_insert_iff] at hg
  obtain hpre | rfl | hsuf := hg
  · exact Or.inl <| by simp [branchEdges, hpre]
  · exact (hne rfl).elim
  exact Or.inr <| by simp [branchEdges, hsuf]

/-! ## The contraction branch subgraphs -/

/-- The connected subgraph of the subdivision that contracts to a pattern vertex. -/
noncomputable def contractBranch (v : V(H)) : Graph α β :=
  G[{v.val} ∪ ⋃ e : E(H), S.branchVerts e v.val] ↾ ⋃ e : E(H), S.branchEdges e v.val

lemma contractBranch_le (v : V(H)) : S.contractBranch v ≤ G := by
  refine restrict_le.trans <| induce_le ?_
  simp only [iUnion_coe_set, singleton_union, insert_subset_iff,
    S.toTopologicalMinor.vertexSet_mono v.prop, iUnion_subset_iff, true_and]
  exact fun e he ↦ S.branchVerts_subset_host ⟨e, he⟩ v.val

lemma mem_contractBranch (v : V(H)) : v.val ∈ V(S.contractBranch v) := by
  simp [contractBranch]

lemma contractBranch_disjoint_of_ne {u v : V(H)} (huv : u ≠ v) :
    Disjoint (S.contractBranch u) (S.contractBranch v) := by
  simp only [contractBranch, iUnion_coe_set, singleton_union, Graph.disjoint_iff,
    vertexSet_restrict, vertexSet_induce, disjoint_insert_right, mem_insert_iff, mem_iUnion,
    not_or, not_exists, disjoint_iUnion_right, disjoint_insert_left, disjoint_iUnion_left]
  refine ⟨⟨Subtype.coe_ne_coe.mpr huv.symm, fun e he h ↦ ?_⟩,
    fun e he ↦ ⟨fun h ↦ ?_, fun f hf ↦ ?_⟩⟩
  · exact huv.symm <| Subtype.coe_inj.mp <| mem_singleton_iff.mp <|
      S.branchVerts_inter_vertexSet ⟨e, he⟩ u ⟨h, v.prop⟩
  · exact huv <| Subtype.coe_inj.mp <| mem_singleton_iff.mp <|
      S.branchVerts_inter_vertexSet ⟨e, he⟩ v ⟨h, u.prop⟩
  exact S.branchVerts_disjoint_of_vertex_ne ⟨f, hf⟩ ⟨e, he⟩ u v huv

lemma contractBranch_edge_disjoint_pattern (v : V(H)) : Disjoint E(H) E(S.contractBranch v) := by
  rw [contractBranch, edgeSet_restrict]
  refine (disjoint_iUnion_right.mpr fun f ↦ ?_).mono_right inter_subset_right
  rw [disjoint_iff_forall_notMem]
  rintro a haH ha
  simp only [branchEdges, mem_union, mem_ite_empty_right] at ha
  obtain ⟨-, ha⟩ | ⟨-, ha⟩ := ha
  · obtain rfl := S.toTopologicalMinor.route_inter_edgeSet f |>.subset
      ⟨(S.route f).prefixUntilEdge_isPrefix (· = f.val) |>.edge_subset ha, haH⟩
    exact (S.route f).prefixUntilEdgeLabel_edge_notMem ha
  · obtain rfl := S.toTopologicalMinor.route_inter_edgeSet f |>.subset
      ⟨(S.route f).suffixFromEdge_isSuffix (· = f.val) |>.edge_subset ha, haH⟩
    exact (S.route f).suffixFromEdgeLabel_edge_notMem
      (S.toTopologicalMinor.route_isTrail f).edge_nodup ha

lemma mem_contractBranch_of_mem_branchVerts (e : E(H)) (v : V(H)) {u : α}
    (hu : u ∈ S.branchVerts e v.val) : u ∈ V(S.contractBranch v) := by
  simp only [contractBranch, vertexSet_restrict, vertexSet_induce, mem_union, mem_singleton_iff,
    mem_iUnion]
  exact Or.inr ⟨e, hu⟩

/-- Every edge selected for the branch at `v` really occurs in the corresponding branch subgraph. -/
lemma branchEdges_subset_contractBranch (e : E(H)) (v : V(H)) :
    S.branchEdges e v.val ⊆ E(S.contractBranch v) := by
  intro g hg
  simp only [contractBranch, edgeSet_restrict, mem_inter_iff, mem_iUnion]
  refine ⟨?_, ⟨e, hg⟩⟩
  simp only [branchEdges, mem_union, mem_ite_empty_right] at hg
  obtain ⟨hfirst, hg⟩ | ⟨hlast, hg⟩ := hg
  · have hw : G.IsWalk ((S.route e).prefixUntilEdgeLabel e.val) :=
      ((S.toTopologicalMinor.route_isTrail e).isWalk.prefix
        ((S.route e).prefixUntilEdge_isPrefix (· = e.val)))
    refine edgeSet_mono (G.induce_mono_right ?_) (hw.edgeSet_subset_edgeSet_induce hg)
    refine subset_union_of_subset_right (subset_iUnion_of_subset e ?_) _
    simp [branchVerts, hfirst]
  have hw : G.IsWalk ((S.route e).suffixFromEdgeLabel e.val) :=
    ((S.toTopologicalMinor.route_isTrail e).isWalk.suffix
      ((S.route e).suffixFromEdge_isSuffix (· = e.val)))
  refine edgeSet_mono (G.induce_mono_right ?_) (hw.edgeSet_subset_edgeSet_induce hg)
  refine subset_union_of_subset_right (subset_iUnion_of_subset e ?_) _
  simp [branchVerts, hlast]

/-- A pattern edge is represented in the host by an edge joining the contraction branches of its
two pattern ends. -/
lemma exists_isLink_contractBranch {e : β} {x y : V(H)} (hxy : H.IsLink e x y) :
    ∃ a b, G.IsLink e a b ∧ a ∈ V(S.contractBranch x) ∧ b ∈ V(S.contractBranch y) := by
  classical
  set ee : E(H) := ⟨e, hxy.edge_mem⟩
  set pre := (S.route ee).prefixUntilEdgeLabel e
  set suf := (S.route ee).suffixFromEdgeLabel e
  have hlink : G.IsLink e pre.last suf.first :=
    S.toTopologicalMinor.route_isTrail ee |>.isWalk.isLink_mono
      (isLink_prefixUntilEdgeLabel_suffixFromEdgeLabel (S.route_edge_mem ee))
  obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := hxy.eq_and_eq_or_eq_and_eq (S.toTopologicalMinor.route_isLink ee)
  · refine ⟨pre.last, suf.first, hlink, S.mem_contractBranch_of_mem_branchVerts ee x ?_,
      S.mem_contractBranch_of_mem_branchVerts ee y ?_⟩ <;>
      by_cases hne : (S.route ee).first = (S.route ee).last
    · rw [S.branchVerts_eq_union ee hx hne]
      exact Or.inl pre.last_mem
    · rw [S.branchVerts_eq_prefix ee hx hne]
      exact pre.last_mem
    · rw [S.branchVerts_eq_union ee (hne ▸ hy) hne]
      exact Or.inr suf.first_mem
    · rw [S.branchVerts_eq_suffix ee hy hne]
      exact suf.first_mem
  · refine ⟨suf.first, pre.last, hlink.symm,
      S.mem_contractBranch_of_mem_branchVerts ee x ?_,
      S.mem_contractBranch_of_mem_branchVerts ee y ?_⟩ <;>
      by_cases hne : (S.route ee).first = (S.route ee).last
    · rw [S.branchVerts_eq_union ee (hne ▸ hx) hne]
      exact Or.inr suf.first_mem
    · rw [S.branchVerts_eq_suffix ee hx hne]
      exact suf.first_mem
    · rw [S.branchVerts_eq_union ee (hne ▸ hy) hne]
      exact Or.inl pre.last_mem
    · rw [S.branchVerts_eq_prefix ee hy hne]
      exact pre.last_mem

lemma contractBranch_connected (v : V(H)) : (S.contractBranch v).Connected := by
  classical
  refine connected_of_vertex (u := v.val) (S.mem_contractBranch v) fun y hy ↦ ?_
  simp only [contractBranch, vertexSet_restrict, vertexSet_induce, mem_union, mem_singleton_iff,
    mem_iUnion] at hy
  obtain rfl | ⟨e, hy⟩ := hy
  · exact ConnBetween.refl (S.mem_contractBranch v)
  simp only [branchVerts, mem_union, mem_ite_empty_right, mem_vertexSet_iff] at hy
  obtain ⟨hfirst, hy⟩ | ⟨hlast, hy⟩ := hy <;> refine IsWalk.connBetween_of_mem_of_mem ?_ hy ?_
  · have hpre : G[{v.val} ∪ ⋃ f : E(H), S.branchVerts f v.val].IsWalk
        ((S.route e).prefixUntilEdgeLabel e.val) := by
      refine ((S.toTopologicalMinor.route_isTrail e).isWalk.prefix
        ((S.route e).prefixUntilEdge_isPrefix (· = e.val))).induce fun z hz ↦ ?_
      simp only [mem_union, mem_singleton_iff, mem_iUnion]
      exact Or.inr ⟨e, Or.inl <| by simpa [hfirst]⟩
    refine hpre.isWalk_le restrict_le (fun f hf ↦ ?_) <| by
      simpa only [contractBranch, vertexSet_restrict] using hpre.first_mem
    simp only [contractBranch, edgeSet_restrict, mem_inter_iff, mem_iUnion]
    refine ⟨hpre.edgeSet_subset hf, ⟨e, Or.inl ?_⟩⟩
    simpa only [hfirst, ↓reduceIte, mem_edgeSet_iff] using hf
  · exact hfirst ▸ ((S.route e).prefixUntilEdge_isPrefix (· = e.val)).first_eq.symm ▸ first_mem
  · have hsuf : G[{v.val} ∪ ⋃ f : E(H), S.branchVerts f v.val].IsWalk
        ((S.route e).suffixFromEdgeLabel e.val) := by
      refine ((S.toTopologicalMinor.route_isTrail e).isWalk.suffix
        ((S.route e).suffixFromEdge_isSuffix (· = e.val))).induce fun z hz ↦ ?_
      simp only [mem_union, mem_singleton_iff, mem_iUnion]
      exact Or.inr ⟨e, Or.inr <| by simpa [hlast]⟩
    refine hsuf.isWalk_le restrict_le (fun f hf ↦ ?_) <| by
      simpa only [contractBranch, vertexSet_restrict] using hsuf.first_mem
    simp only [contractBranch, edgeSet_restrict, mem_inter_iff, mem_iUnion]
    refine ⟨hsuf.edgeSet_subset hf, ⟨e, Or.inr ?_⟩⟩
    simpa only [hlast, ↓reduceIte, mem_edgeSet_iff] using hf
  exact hlast ▸ ((S.route e).suffixFromEdge_isSuffix (· = e.val)).last_eq.symm ▸ last_mem

/-- The minor-map witness obtained by contracting the subdivision branches. -/
noncomputable def toMinorMap : minorMap H G where
  map := S.contractBranch
  map_le := S.contractBranch_le
  mem_map := S.mem_contractBranch
  disj := fun _ _ huv ↦ S.contractBranch_disjoint_of_ne huv
  edge_disj := S.contractBranch_edge_disjoint_pattern
  link := fun _ _ _ hxy ↦ S.exists_isLink_contractBranch hxy
  conn := S.contractBranch_connected

/-! ## A subdivision contracts exactly to its pattern -/

/-- All edges lying in contraction branches. -/
noncomputable def contractionEdgeSet : Set β :=
  ⋃ v : V(H), E(S.contractBranch v)

lemma contractionEdgeSet_subset_host : S.contractionEdgeSet ⊆ E(G) := by
  simp only [contractionEdgeSet, iUnion_subset_iff]
  exact fun v ↦ (S.contractBranch_le v).edgeSet_mono

lemma contractionEdgeSet_disjoint_pattern : Disjoint E(H) S.contractionEdgeSet := by
  simp only [contractionEdgeSet, disjoint_iUnion_right]
  exact S.contractBranch_edge_disjoint_pattern

lemma contractionEdgeSet_subset_diff : S.contractionEdgeSet ⊆ E(G) \ E(H) :=
  subset_sdiff.mpr ⟨S.contractionEdgeSet_subset_host, S.contractionEdgeSet_disjoint_pattern.symm⟩

/-- Exhaustiveness and route splitting show that every non-pattern host edge belongs to a
contraction branch. -/
lemma diff_subset_contractionEdgeSet : E(G) \ E(H) ⊆ S.contractionEdgeSet := by
  rintro g ⟨hgG, hgH⟩
  have hcover := S.edge_covers hgG
  simp only [mem_iUnion] at hcover
  obtain ⟨e, hge⟩ := hcover
  have hne : g ≠ e.val := fun h ↦ hgH (h ▸ e.prop)
  obtain hfirst | hlast := S.mem_branchEdges_first_or_last_of_ne e hge hne
  · have hends := S.toTopologicalMinor.route_ends_mem_vertexSet e
    exact mem_iUnion.mpr ⟨⟨(S.route e).first, hends.1⟩,
      S.branchEdges_subset_contractBranch e _ hfirst⟩
  have hends := S.toTopologicalMinor.route_ends_mem_vertexSet e
  exact mem_iUnion.mpr ⟨⟨(S.route e).last, hends.2⟩,
    S.branchEdges_subset_contractBranch e _ hlast⟩

/-- The contraction branches contain exactly the subdivision edges that are not retained pattern
edge labels. -/
theorem contractionEdgeSet_eq : S.contractionEdgeSet = E(G) \ E(H) :=
  S.contractionEdgeSet_subset_diff.antisymm S.diff_subset_contractionEdgeSet

lemma iUnion_contractBranch_vertexSet_subset : (⋃ v : V(H), V(S.contractBranch v)) ⊆ V(G) :=
  iUnion_subset fun v ↦ (S.contractBranch_le v).vertexSet_mono

/-- Exhaustiveness says every host vertex belongs to one of the contraction branches. -/
lemma vertexSet_subset_iUnion_contractBranch : V(G) ⊆ ⋃ v : V(H), V(S.contractBranch v) := by
  intro x hx
  have hcover := S.vertex_covers hx
  simp only [mem_union, mem_iUnion] at hcover
  obtain hxH | ⟨e, hxint⟩ := hcover
  · exact mem_iUnion.mpr ⟨⟨x, hxH⟩, S.mem_contractBranch ⟨x, hxH⟩⟩
  have hxroute : x ∈ S.route e :=
    mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mpr (Or.inr (Or.inl hxint))
  obtain hfirst | hlast := S.mem_branchVerts_first_or_last e hxroute
  · have hends := S.toTopologicalMinor.route_ends_mem_vertexSet e
    exact mem_iUnion.mpr ⟨⟨(S.route e).first, hends.1⟩,
      S.mem_contractBranch_of_mem_branchVerts e _ hfirst⟩
  have hends := S.toTopologicalMinor.route_ends_mem_vertexSet e
  exact mem_iUnion.mpr ⟨⟨(S.route e).last, hends.2⟩,
    S.mem_contractBranch_of_mem_branchVerts e _ hlast⟩

lemma iUnion_contractBranch_vertexSet_eq : (⋃ v : V(H), V(S.contractBranch v)) = V(G) :=
  subset_antisymm S.iUnion_contractBranch_vertexSet_subset S.vertexSet_subset_iUnion_contractBranch

lemma pattern_union_contractionEdgeSet_eq : E(H) ∪ S.contractionEdgeSet = E(G) := by
  rw [S.contractionEdgeSet_eq]
  ext g
  simp only [union_sdiff_self, mem_union, or_iff_right_iff_imp]
  exact (S.toTopologicalMinor.edgeSet_mono ·)

/-- The intermediate graph of the subdivision minor map is the whole subdivision host. -/
theorem minorMap_intermediate_eq : S.toMinorMap.intermediate = G := by
  change G[⋃ v : V(H), V(S.contractBranch v)] ↾ (E(H) ∪ ⋃ v : V(H), E(S.contractBranch v)) = G
  rw [S.iUnion_contractBranch_vertexSet_eq]
  change G[V(G)] ↾ (E(H) ∪ S.contractionEdgeSet) = G
  rw [S.pattern_union_contractionEdgeSet_eq]
  simp

/-- The canonical representative function collapsing each contraction branch to its pattern
vertex. -/
noncomputable def contractRepFun : α → α := S.toMinorMap.repFun

lemma contractRepFun_isRepFun : (G ↾ (E(G) \ E(H))).connPartition.IsRepFun S.contractRepFun := by
  have h := S.toMinorMap.repFun_isRepFun
  have hE : (⋃ x, E(S.toMinorMap.map x)) = E(G) \ E(H) := S.contractionEdgeSet_eq
  rw [S.minorMap_intermediate_eq, hE] at h
  exact h

/-- Contraction is inverse to a label-coherent subdivision: contracting every host edge other than
the retained pattern-edge labels recovers the pattern *on the nose*. -/
theorem eq_contract : H = G /[E(G) \ E(H), S.contractRepFun] := by
  have h := S.toMinorMap.eq_contract_of_intermediate
  have hE : (⋃ x, E(S.toMinorMap.map x)) = E(G) \ E(H) := S.contractionEdgeSet_eq
  rw [S.minorMap_intermediate_eq, hE] at h
  exact h

/-- A subdivision is, in particular, an ordinary graph minor. -/
theorem isMinor (S : H.Subdivision G) : H ≤m G := ⟨S.toMinorMap⟩

end Subdivision

/-! ## General topological minors -/

namespace TopologicalMinor

variable (M : H.TopologicalMinor G)

open scoped Classical

/-- The ordinary minor-map witness obtained by first restricting to the used subdivision and then
including that subgraph in the original host. -/
noncomputable def toMinorMap : minorMap H G :=
  M.subdivisionUsedSubgraph.toMinorMap |>.mono_right M.usedSubgraph_le

/-- A topological minor is an ordinary graph minor. -/
theorem isMinor (M : H.TopologicalMinor G) : H ≤m G := ⟨M.toMinorMap⟩

/-- The pattern is literally a contraction of the subgraph used by a topological-minor witness. -/
theorem eq_contract_usedSubgraph :
    H = M.usedSubgraph /[E(M.usedSubgraph) \ E(H), M.subdivisionUsedSubgraph.contractRepFun] :=
  M.subdivisionUsedSubgraph.eq_contract

/-- A topological-minor witness exhibits a subgraph of the host that contracts exactly to the
pattern. -/
theorem exists_subgraph_eq_contract (M : H.TopologicalMinor G) : ∃ K : Graph α β, K ≤ G ∧
    ∃ φ : α → α, (K ↾ (E(K) \ E(H))).connPartition.IsRepFun φ ∧ H = K /[E(K) \ E(H), φ] :=
  ⟨M.usedSubgraph, M.usedSubgraph_le, M.subdivisionUsedSubgraph.contractRepFun,
    M.subdivisionUsedSubgraph.contractRepFun_isRepFun, M.eq_contract_usedSubgraph⟩

end TopologicalMinor

lemma IsTopologicalMinor.isMinor {H G : Graph α β} (h : H.IsTopologicalMinor G) : H ≤m G :=
  h.some.isMinor

/-! ## Heterogeneous topological minors and ordinary minors -/

namespace IsoTopologicalMinor

variable (M : J.IsoTopologicalMinor G)

/-- A heterogeneous topological minor has an isomorphic same-carrier copy that is an ordinary
minor of the host. -/
theorem exists_iso_minor (M : J.IsoTopologicalMinor G) :
    ∃ K : Graph α β, Nonempty (Iso J K) ∧ K ≤m G :=
  ⟨M.normalized, ⟨M.isoNormalized⟩, M.toTopologicalMinor.isMinor⟩

end IsoTopologicalMinor

lemma IsIsoTopologicalMinor.exists_iso_minor {J : Graph γ δ} {G : Graph α β}
    (h : J.IsIsoTopologicalMinor G) : ∃ K : Graph α β, Nonempty (Iso J K) ∧ K ≤m G :=
  h.some.exists_iso_minor

namespace IsoSubdivision

open scoped Classical

/-- A heterogeneous subdivision has an isomorphic same-carrier copy obtained by contraction of the
host. -/
theorem exists_iso_eq_contract (S : J.IsoSubdivision G) : ∃ K : Graph α β, Nonempty (Iso J K) ∧
    ∃ φ : α → α, (G ↾ (E(G) \ E(K))).connPartition.IsRepFun φ ∧ K = G /[E(G) \ E(K), φ] := by
  obtain ⟨K, ⟨F⟩, ⟨T⟩⟩ := S.exists_iso_subdivision
  exact ⟨K, ⟨F⟩, T.contractRepFun, T.contractRepFun_isRepFun, T.eq_contract⟩

end IsoSubdivision

lemma IsIsoSubdivision.exists_iso_eq_contract {J : Graph γ δ} {G : Graph α β}
    (h : J.IsIsoSubdivision G) : ∃ K : Graph α β, Nonempty (Iso J K) ∧
    ∃ φ : α → α, (G ↾ (E(G) \ E(K))).connPartition.IsRepFun φ ∧ K = G /[E(G) \ E(K), φ] :=
  h.some.exists_iso_eq_contract

end Graph
