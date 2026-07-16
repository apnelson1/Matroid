import Matroid.Graph.Minor.Defs
import Matroid.Graph.WList.TakeDrop.Index

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e f g : β} {X : Set α} {F : Set β}
{P C W : WList α β} {n : ℕ}

open Set WList Function

namespace Graph

/-- `G` is a topological minor of `H` if `V(G) ⊆ V(H)` and there is a map `F : E(G) → WList α β`,
where `F e` is a path in `H` between `u` and `v` with property that `V(F e) ∩ V(G) = {u, v}` where
`e` is an edge between `u` and `v` in `G`. -/
structure TopologicalMinor (G : Graph α β) (H : Graph α β) where
  vertex_subset : V(G) ⊆ V(H)
  map : E(G) → WList α β
  mem_map : ∀ e, e.val ∈ E(map e)
  map_isSimple : ∀ e, H.IsPath (map e) ∨ H.IsCyclicWalk (map e)
  map_isLink : ∀ e : E(G), G.IsLink e (map e).first (map e).last
  map_ends : ∀ e, Disjoint {v | v ∈ (map e).vertex.tail.dropLast} V(G)
  map_internally_disjoint : ∀ e f, e ≠ f →
    V(map e) ∩ V(map f) ⊆ {(map e).first, (map e).last}

namespace TopologicalMinor

variable (h : G.TopologicalMinor H)

lemma vertexSet_mono (h : G.TopologicalMinor H) : V(G) ⊆ V(H) := h.vertex_subset

lemma map_isTrail (e : E(G)) : H.IsTrail (h.map e) :=
  (h.map_isSimple e).elim IsPath.isTrail IsCyclicWalk.isTrail

lemma edgeSet_mono (h : G.TopologicalMinor H) : E(G) ⊆ E(H) :=
  fun e he ↦ h.map_isTrail ⟨e, he⟩ |>.edgeSet_subset (h.mem_map ⟨e, he⟩)

lemma map_nonempty (e : E(G)) : h.map e |>.Nonempty := by
  refine nonempty_iff_exists_edge.mpr ?_
  use e
  simpa using h.mem_map e

lemma map_inter_vertexSet (e : E(G)) : V(h.map e) ∩ V(G) = {(h.map e).first, (h.map e).last} := by
  refine subset_antisymm (fun x ⟨hxW, hxG⟩ ↦ ?_) ?_
  · grind [h.map_isLink e]
  simp only [mem_vertexSet_iff] at hxW ⊢
  rw [mem_iff_eq_vertex_first_or_mem_tail] at hxW
  obtain rfl | hxW := hxW
  · simp
  have hne : (h.map e).vertex.tail ≠ [] := List.ne_nil_of_mem hxW
  rw [List.mem_iff_mem_dropLast_or_eq_getLast hne] at hxW
  grind [h.map_ends e]

lemma map_inter_edgeSet (e : E(G)) : E(h.map e) ∩ E(G) = {e.val} := by
  refine subset_antisymm (fun f ⟨hfW, hfG⟩ ↦ ?_) (singleton_subset_iff.mpr ⟨h.mem_map e, e.prop⟩)
  by_contra hne
  rw [mem_singleton_iff, ← ne_eq] at hne
  have hef : e ≠ ⟨f, hfG⟩ := Subtype.coe_ne_coe.1 hne.symm
  obtain ⟨u, v, huv⟩ := exists_dInc_of_mem_edge hfW
  obtain ⟨p, q, hpq⟩ := exists_dInc_of_mem_edge (h.mem_map ⟨f, hfG⟩)
  have huvH := (h.map_isTrail e).isWalk.isLink_of_dInc huv
  have hpqH := (h.map_isTrail ⟨f, hfG⟩).isWalk.isLink_of_dInc hpq
  have hf : {u, v} ⊆ V(h.map ⟨f, hfG⟩) := by
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := huvH.eq_and_eq_or_eq_and_eq hpqH <;>
    grind [hpq.left_mem, hpq.right_mem]
  have hu_end : u = (h.map e).first ∨ u = (h.map e).last :=
    h.map_internally_disjoint e ⟨f, hfG⟩ hef ⟨huv.left_mem, hf (by grind)⟩
  have hv_end : v = (h.map e).first ∨ v = (h.map e).last :=
    h.map_internally_disjoint e ⟨f, hfG⟩ hef ⟨huv.right_mem, hf (by grind)⟩
  obtain hp | hc := h.map_isSimple e
  · have hle := Nat.succ_le_of_lt (h.map_nonempty e).length_pos |>.eq_of_not_lt'
      <| one_lt_length_iff.not.mpr <| hp.not_nontrivial_of_dInc rfl rfl huv hu_end hv_end
    rw [(h.map e).length_eq_one_iff] at hle
    grind [h.mem_map e]
  · obtain rfl : v = u := by
      grind [hc.isClosed, hc.isClosed.symm]
    exact hne (Eq.symm (by
      simpa [hc.eq_loop_of_isLink_self (isLink_iff_dInc.mpr (Or.inl huv))] using h.mem_map e))

noncomputable def of_le (hle : G ≤ H) : G.TopologicalMinor H where
  vertex_subset := hle.vertexSet_mono
  map e :=
    let h := exists_isLink_of_mem_edgeSet e.prop
    cons h.choose e (nil h.choose_spec.choose)
  mem_map e := by simp
  map_isSimple e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    obtain hxy | hxy := eq_or_ne h.choose h.choose_spec.choose
    · right
      have hlink := h.choose_spec.choose_spec.of_le hle
      change H.IsCyclicWalk (cons h.choose e (nil h.choose_spec.choose))
      rw [← hxy] at hlink ⊢
      exact (nil_isPath hlink.left_mem).cons_isCyclicWalk hlink (by simp)
    left
    simp [isPath_iff, h.choose_spec.choose_spec.of_le hle,
      (h.choose_spec.choose_spec.of_le hle).right_mem, hxy]
  map_isLink e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    simp only [first_cons, last_cons, nil_last]
    exact h.choose_spec.choose_spec
  map_ends e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    simp only [cons_vertex, nil_vertex, List.tail_cons, List.dropLast_singleton, List.not_mem_nil,
      setOf_false, empty_disjoint]
  map_internally_disjoint e f hne := by simp

def mapFrom [DecidableEq α] (e : E(G)) (v : α) : WList α β :=
  if (h.map e).first = v then (h.map e)
  else if (h.map e).last = v then (h.map e).reverse
  else nil v

lemma mapFrom_first [DecidableEq α] (e : E(G)) (v : α) : (h.mapFrom e v).first = v := by
  unfold mapFrom
  split_ifs with h1 h2 <;> grind

lemma mapFrom_isTrail [DecidableEq α] (e : E(G)) (hv : v ∈ V(G)) : H.IsTrail (h.mapFrom e v) := by
  unfold mapFrom
  split_ifs with h1 h2
  · exact h.map_isTrail e
  · exact h.map_isTrail e |>.reverse
  simpa using (h.vertexSet_mono hv)

section minor

variable [DecidableEq α] [DecidableEq β] (e : E(G))

/-- Vertices contributed by the branch of `e` at `v`. On loops, use both sides. -/
def branchVerts (v : α) : Set α :=
  let w := h.map e
  (if w.first = v then V(w.prefixUntilEdgeLabel e.val) else ∅) ∪
  (if w.last = v then V(w.suffixFromEdgeLabel e.val) else ∅)

/-- Edges contributed by the branch of `e` at `v`. On loops, use both sides. -/
def branchEdges (v : α) : Set β :=
  let w := h.map e
  (if w.first = v then E(w.prefixUntilEdgeLabel e.val) else ∅) ∪
  (if w.last = v then E(w.suffixFromEdgeLabel e.val) else ∅)

lemma branchVerts_eq_prefix (hv : v = (h.map e).first) (hne : (h.map e).first ≠ (h.map e).last) :
    h.branchVerts e v = V((h.map e).prefixUntilEdgeLabel e.val) := by
  have hvfirst : (h.map e).first = v := hv.symm
  have hvlast : (h.map e).last ≠ v := fun h ↦ hne (hvfirst.trans h.symm)
  simp [branchVerts, if_pos hvfirst, if_neg hvlast]

lemma branchVerts_eq_union (hv : v = (h.map e).first) (hloop : (h.map e).first = (h.map e).last) :
    h.branchVerts e v = V((h.map e).prefixUntilEdgeLabel e.val) ∪
    V((h.map e).suffixFromEdgeLabel e.val) := by
  have hvfirst : (h.map e).first = v := hv.symm
  simp [branchVerts, if_pos (hloop.symm.trans hvfirst), if_pos hvfirst]

lemma branchVerts_eq_suffix (hv : v = (h.map e).last) (hne : (h.map e).first ≠ (h.map e).last) :
    h.branchVerts e v = V((h.map e).suffixFromEdgeLabel e.val) := by
  have hvlast : (h.map e).last = v := hv.symm
  have hvfirst : (h.map e).first ≠ v := fun h ↦ hne (h.trans hvlast.symm)
  simp [branchVerts, if_neg hvfirst, if_pos hvlast]

lemma branchVerts_subset_vertexSet_walk (e : E(G)) (v : α) : h.branchVerts e v ⊆ V(h.map e) := by
  rintro z hz
  simp only [branchVerts, mem_union, mem_ite_empty_right, mem_vertexSet_iff] at hz
  obtain ⟨-, hz⟩ | ⟨-, hz⟩ := hz
  · exact (h.map e).prefixUntilEdge_isPrefix (· = e) |>.subset hz
  exact (h.map e).suffixFromEdge_isSuffix (· = e) |>.subset hz

lemma branchVerts_subset (e : E(G)) (v : α) : h.branchVerts e v ⊆ V(H) :=
  h.branchVerts_subset_vertexSet_walk e v |>.trans (h.map_isTrail e).vertexSet_subset

lemma mem_vertexSet_minorMap_map (x : V(G)) (hu : u ∈ h.branchVerts e x.val) :
    u ∈ V(H[{x.val} ∪ ⋃ e : E(G), h.branchVerts e x.val] ↾ ⋃ e : E(G), h.branchEdges e x.val) := by
  simp only [vertexSet_restrict, vertexSet_induce, mem_union, mem_iUnion]
  exact Or.inr ⟨e, hu⟩

lemma branchVerts_nonempty_iff_mem : (h.branchVerts e v).Nonempty ↔ v ∈ h.branchVerts e v := by
  by_cases hf : (h.map e).first = v
  · simp only [branchVerts, hf, ↓reduceIte, union_nonempty, vertexSet_nonempty, true_or, mem_union,
    mem_vertexSet_iff, mem_ite_empty_right, true_iff]
    left
    convert first_mem
    rw [← hf]
    exact (h.map e).prefixUntilEdge_isPrefix (· = e) |>.first_eq.symm
  by_cases hl : (h.map e).last = v
  · simp only [branchVerts, hf, ↓reduceIte, hl, empty_union, vertexSet_nonempty, mem_vertexSet_iff,
    true_iff]
    convert last_mem
    rw [← hl]
    exact (h.map e).suffixFromEdge_isSuffix (· = e) |>.last_eq.symm
  simp [branchVerts, hf, hl]

lemma foo (hx : x ∈ h.map e) :
    x ∈ h.branchVerts e (h.map e).first ∨ x ∈ h.branchVerts e (h.map e).last := by
  have := (h.map e).prefixUntilEdgeLabel_append_cons_suffixFromEdgeLabel (h.mem_map e) ▸ hx
  rw [mem_append_iff, mem_cons_iff, ← or_assoc, ← mem_iff_eq_mem_vertex_dropLast_or_eq_last] at this
  grind [branchVerts]

lemma branchVerts_inter_vertexSet : h.branchVerts e v ∩ V(G) ⊆ {v} := by
  rintro x ⟨hxv, hx⟩
  simp only [branchVerts, mem_union, mem_ite_empty_right, mem_vertexSet_iff] at hxv
  obtain ⟨rfl, h1⟩ | ⟨rfl, h2⟩ := hxv
  · have hxdl := h.map e |>.prefixUntilEdge_vertex_isPrefix_dropLast (by use e, h.mem_map e)
      |>.mem h1
    have := h.map_ends e |>.notMem_of_mem_right hx
    rw [mem_setOf_eq, ← List.tail_dropLast] at this
    rw [List.mem_iff_eq_head_or_mem_tail (List.ne_nil_of_mem hxdl)] at hxdl
    rw [hxdl.resolve_right this, ← vertex_head, mem_singleton_iff, List.head_dropLast]
  have hxT := (h.map e |>.suffixFromEdge_vertex_isSuffix_tail (by use e, h.mem_map e)).mem h2
  have := h.map_ends e |>.notMem_of_mem_right hx
  rw [mem_setOf_eq] at this
  rw [List.mem_iff_mem_dropLast_or_eq_getLast (List.ne_nil_of_mem hxT)] at hxT
  rw [hxT.resolve_left this, ← vertex_getLast, mem_singleton_iff, List.getLast_tail]

lemma branchVerts_disjoint_of_vertex_ne (e f : E(G)) (u v : V(G)) (hne : u ≠ v) :
    Disjoint (h.branchVerts e u) (h.branchVerts f v) := by
  obtain rfl | hfe := eq_or_ne f e
  · obtain hc | hp := h.map_isSimple f |>.symm
    · obtain hxf | hxf := eq_or_ne (h.map f).first u
      · have hyl : (h.map f).last ≠ v :=
          hc.isClosed ▸ (hne <| Subtype.coe_inj.mp <| hxf.symm.trans ·)
        simp [hxf, hyl, Subtype.coe_ne_coe.mpr hne, branchVerts]
      have hxl : (h.map f).last ≠ u := by rwa [← hc.isClosed]
      simp [hxf, hxl, branchVerts]
    have hdj : Disjoint V((h.map f).prefixUntilEdgeLabel f) V((h.map f).suffixFromEdgeLabel f) := by
      rw [← (h.map f).prefixUntilEdgeLabel_append_cons_suffixFromEdgeLabel (h.mem_map f),
        ← (h.map f |>.suffixFromEdgeLabel f).nil_append (x := u.val), ← cons_append,
        ← append_assoc] at hp
      exact hp.disjoint_of_append_append rfl (by simp)
    simp only [branchVerts]
    split_ifs <;> grind
  refine disjoint_left.mpr fun z hzx hzy ↦ ?_
  obtain rfl | rfl := h.map_internally_disjoint f e (by simpa using hfe)
    ⟨h.branchVerts_subset_vertexSet_walk f v hzy, h.branchVerts_subset_vertexSet_walk e u hzx⟩ <;>
  have hzx' := branchVerts_inter_vertexSet h e ⟨hzx, by grind [h.map_isLink f]⟩ <;>
  have hzy' := branchVerts_inter_vertexSet h f ⟨hzy, by grind [h.map_isLink f]⟩ <;>
  exact hne (Subtype.ext <| hzx'.symm.trans hzy')

/- Given a vertex, for each edge `e`, split `h.map e` at `e.val` and use the side incident with
the vertex. Induce `H` on the union of all such side walks, plus the singleton vertex, and restrict
to the side-walk edges. -/
noncomputable def minorMap (h : G.TopologicalMinor H) : minorMap G H where
  map v := H[{v.val} ∪ ⋃ e : E(G), h.branchVerts e v.val] ↾ ⋃ e : E(G), h.branchEdges e v.val
  map_le v := by
    refine restrict_le.trans <| induce_le ?_
    simp only [iUnion_coe_set, singleton_union, insert_subset_iff, h.vertexSet_mono v.prop,
      iUnion_subset_iff, true_and]
    exact fun e he ↦ h.branchVerts_subset ⟨e, he⟩ v.val
  mem_map v := by simp only [iUnion_coe_set, singleton_union, vertexSet_restrict, vertexSet_induce,
    mem_insert_iff, mem_iUnion, true_or]
  disj x y hxy := by
    simp only [iUnion_coe_set, singleton_union, Graph.disjoint_iff, vertexSet_restrict,
      vertexSet_induce, disjoint_insert_right, mem_insert_iff, mem_iUnion, not_or, not_exists,
      disjoint_iUnion_right, disjoint_insert_left, disjoint_iUnion_left]
    refine ⟨⟨Subtype.coe_ne_coe.mpr hxy.symm, fun e he ↦ ?_⟩, fun e he ↦ ⟨?_, fun f hf ↦ ?_⟩⟩
    · exact (hxy.symm <| Subtype.coe_inj.mp <| branchVerts_inter_vertexSet h ⟨e, he⟩ ⟨·, y.prop⟩)
    · exact (hxy <| Subtype.coe_inj.mp <| branchVerts_inter_vertexSet h ⟨e, he⟩ ⟨·, x.prop⟩)
    exact branchVerts_disjoint_of_vertex_ne h ⟨f, hf⟩ ⟨e, he⟩ x y hxy
  edge_disj v := by
    refine (disjoint_iUnion_right.mpr fun f ↦ ?_).mono_right inter_subset_right
    rw [disjoint_iff_forall_notMem]
    rintro a haG ha
    simp only [branchEdges, mem_union, mem_ite_empty_right] at ha
    obtain ⟨-, ha⟩ | ⟨-, ha⟩ := ha
    · obtain rfl := h.map_inter_edgeSet f |>.subset ⟨(h.map f).prefixUntilEdge_isPrefix (· = f)
        |>.edge_subset ha, haG⟩
      exact (h.map f).prefixUntilEdgeLabel_edge_notMem ha
    obtain rfl := h.map_inter_edgeSet f |>.subset ⟨(h.map f).suffixFromEdge_isSuffix (· = f)
      |>.edge_subset ha, haG⟩
    exact (h.map f).suffixFromEdgeLabel_edge_notMem (h.map_isTrail f).edge_nodup ha
  link e x y hxy := by
    set ee : E(G) := ⟨e, hxy.edge_mem⟩
    set pre := (h.map ee).prefixUntilEdgeLabel e
    set suf := (h.map ee).suffixFromEdgeLabel e
    have hlink : H.IsLink e pre.last suf.first :=
      h.map_isTrail ee |>.isWalk.isLink_mono (isLink_prefixUntilEdgeLabel_suffixFromEdgeLabel
      (h.mem_map ee))
    obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := hxy.eq_and_eq_or_eq_and_eq (h.map_isLink ee)
    · refine ⟨pre.last, suf.first, hlink, h.mem_vertexSet_minorMap_map ee x ?_,
        h.mem_vertexSet_minorMap_map ee y ?_⟩ <;> by_cases hne : (h.map ee).first = (h.map ee).last
      · rw [h.branchVerts_eq_union ee hx hne]
        exact Or.inl pre.last_mem
      · rw [h.branchVerts_eq_prefix ee hx hne]
        exact pre.last_mem
      · rw [h.branchVerts_eq_union ee (hne ▸ hy) hne]
        exact Or.inr suf.first_mem
      · rw [h.branchVerts_eq_suffix ee hy hne]
        exact suf.first_mem
    · refine ⟨suf.first, pre.last, hlink.symm, h.mem_vertexSet_minorMap_map ee x ?_,
        h.mem_vertexSet_minorMap_map ee y ?_⟩ <;> by_cases hne : (h.map ee).first = (h.map ee).last
      · rw [h.branchVerts_eq_union ee (hne ▸ hx) hne]
        exact Or.inr suf.first_mem
      · rw [h.branchVerts_eq_suffix ee hx hne]
        exact suf.first_mem
      · rw [h.branchVerts_eq_union ee (hne ▸ hy) hne]
        exact Or.inl pre.last_mem
      · rw [h.branchVerts_eq_prefix ee hy hne]
        exact pre.last_mem
  conn v := by
    refine connected_of_vertex (u := v.val) (by grind) fun y hy ↦ ?_
    simp only [vertexSet_restrict, vertexSet_induce, mem_union, mem_iUnion] at hy
    obtain rfl | ⟨e, hy⟩ := hy
    · grind
    simp only [branchVerts, mem_union, mem_ite_empty_right, mem_vertexSet_iff] at hy
    obtain ⟨hfirst, hy⟩ | ⟨hlast, hy⟩ := hy <;> refine IsWalk.connBetween_of_mem_of_mem ?_ hy ?_
    · have hpre : H[{v.val} ∪ ⋃ f : E(G), h.branchVerts f v.val].IsWalk
          ((h.map e).prefixUntilEdgeLabel e.val) := by
        refine ((h.map_isTrail e).isWalk.prefix
          ((h.map e).prefixUntilEdge_isPrefix (· = e))).induce fun z hz ↦ ?_
        simp only [mem_union, mem_singleton_iff, mem_iUnion]
        exact Or.inr ⟨e, Or.inl <| by simpa [branchVerts, hfirst] using hz⟩
      refine hpre.isWalk_le restrict_le (fun f hf ↦ ?_) <| by
        simpa only [vertexSet_restrict] using hpre.first_mem
      simp only [edgeSet_restrict, mem_inter_iff, mem_iUnion]
      refine ⟨hpre.edgeSet_subset hf, ⟨e, Or.inl ?_⟩⟩
      simpa only [hfirst, ↓reduceIte, mem_edgeSet_iff] using hf
    · exact hfirst ▸ ((h.map e).prefixUntilEdge_isPrefix (· = e)).first_eq.symm ▸ first_mem
    · have hsuf : H[{v.val} ∪ ⋃ f : E(G), h.branchVerts f v.val].IsWalk
          ((h.map e).suffixFromEdgeLabel e.val) := by
        refine ((h.map_isTrail e).isWalk.suffix
          ((h.map e).suffixFromEdge_isSuffix (· = e))).induce fun z hz ↦ ?_
        simp only [mem_union, mem_singleton_iff, mem_iUnion]
        exact Or.inr ⟨e, Or.inr <| by simpa [branchVerts, hlast] using hz⟩
      refine hsuf.isWalk_le restrict_le (fun f hf ↦ ?_) <| by
        simpa only [vertexSet_restrict] using hsuf.first_mem
      simp only [edgeSet_restrict, mem_inter_iff, mem_iUnion]
      refine ⟨hsuf.edgeSet_subset hf, ⟨e, Or.inr ?_⟩⟩
      simpa only [hlast, ↓reduceIte, mem_edgeSet_iff] using hf
    exact hlast ▸ ((h.map e).suffixFromEdge_isSuffix (· = e)).last_eq.symm ▸ last_mem

/-- A topological minor is a minor. -/
lemma isMinor (h : G.TopologicalMinor H) : G ≤m H := by
  classical
  exact ⟨h.minorMap⟩



end Graph.TopologicalMinor.minor
