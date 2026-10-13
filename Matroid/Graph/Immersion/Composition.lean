module

public import Matroid.Graph.Immersion.Basic

/-!
# Composition of immersions

`Immersion.expand` substitutes the routes of an immersion into a walk, reversing a route when
its prescribed direction requires it. `Immersion.comp` applies this substitution to every route.
The membership lemmas record exactly which edges, vertices, and internal vertices are retained.
Composition preserves strongness, topological immersions, and surjectivity without simplifying
the substituted routes.
-/

@[expose] public section

open Set Function WList Graph
open scoped Sym2

variable {α β γ δ ε ζ : Type*} {G : Graph α β} {H : Graph γ δ} {K : Graph ε ζ} {e : β} {x y : α}
  (M : Immersion G H) {w w₁ w₂ : WList α β}

namespace Graph.Immersion

open Classical in
/-- The route for an edge, oriented from the first specified endpoint to the second.
For a loop, retain the stored route direction: its endpoints cannot distinguish a reversal. -/
noncomputable def routeFrom (M : Immersion G H) (h : G.IsLink e x y) : WList γ δ :=
  if (M.route ⟨e, h.edge_mem⟩).first = (M.vertex ⟨x, h.left_mem⟩).val
  then M.route ⟨e, h.edge_mem⟩ else (M.route ⟨e, h.edge_mem⟩).reverse

private lemma routeFrom_ends (h : G.IsLink e x y) :
    (M.routeFrom h).first = (M.vertex ⟨x, h.left_mem⟩).val ∧
      (M.routeFrom h).last = (M.vertex ⟨y, h.right_mem⟩).val := by
  have he := M.route_ends ⟨e, h.edge_mem⟩
  rw [h.ends_eq, Sym2.map_mk] at he
  obtain he | he := Sym2.eq_iff.mp he <;> simp only [Function.comp_apply] at he <;>
    simp_all only [routeFrom] <;> split_ifs <;> simp_all

@[simp]
lemma routeFrom_first (h : G.IsLink e x y) :
    (M.routeFrom h).first = (M.vertex ⟨x, h.left_mem⟩).val := (M.routeFrom_ends h).1

@[simp]
lemma routeFrom_last (h : G.IsLink e x y) :
    (M.routeFrom h).last = (M.vertex ⟨y, h.right_mem⟩).val := (M.routeFrom_ends h).2

lemma routeFrom_isTrail (h : G.IsLink e x y) : H.IsTrail (M.routeFrom h) := by
  unfold routeFrom
  split_ifs <;> simp [M.route_isTrail]

lemma routeFrom_nonempty (h : G.IsLink e x y) : (M.routeFrom h).Nonempty := by
  unfold routeFrom
  split_ifs <;> simp [M.route_nonempty]

@[simp]
lemma routeFrom_edgeSet (h : G.IsLink e x y) : E(M.routeFrom h) = E(M.route ⟨e, h.edge_mem⟩) := by
  unfold routeFrom
  split_ifs <;> simp

@[simp]
lemma routeFrom_vertexSet (h : G.IsLink e x y) : V(M.routeFrom h) = V(M.route ⟨e, h.edge_mem⟩) := by
  unfold routeFrom
  split_ifs <;> simp

@[simp]
lemma routeFrom_internalVertexSet (h : G.IsLink e x y) :
    (M.routeFrom h).internalVertexSet = (M.route ⟨e, h.edge_mem⟩).internalVertexSet := by
  unfold routeFrom
  split_ifs <;> simp [internalVertexSet_reverse]

/-- Substitute the oriented routes of an immersion for the edges of a walk.
A loop uses the stored route direction even when the walk is reversed, so substitution does not
in general commute with reversal. -/
noncomputable def expand (M : Immersion G H) : (w : WList α β) → G.IsWalk w → WList γ δ
  | .nil x, hw => .nil (M.vertex ⟨x, hw.first_mem⟩).val
  | .cons _ _ w, hw => M.routeFrom (cons_isWalk_iff.mp hw).1 ++ M.expand w hw.of_cons

@[simp]
lemma expand_nil (hx : x ∈ V(G)) : M.expand (.nil x) (.nil hx) = .nil (M.vertex ⟨x, hx⟩).val :=
  rfl

@[simp]
lemma expand_cons  (hw : G.IsWalk (.cons x e w)) :
    M.expand (.cons x e w) hw = M.routeFrom (cons_isWalk_iff.mp hw).1 ++ M.expand w hw.of_cons :=
  rfl

@[simp]
lemma expand_first (hw : G.IsWalk w) :
    (M.expand w hw).first = (M.vertex ⟨w.first, hw.first_mem⟩).val := by
  cases w with
  | nil x => rfl
  | cons x e w =>
    rw [expand_cons, append_first_of_nonempty (M.routeFrom_nonempty _)]
    simp

@[simp]
lemma expand_last (hw : G.IsWalk w) :
    (M.expand w hw).last = (M.vertex ⟨w.last, hw.last_mem⟩).val := by
  induction w with
  | nil x => rfl
  | cons x e w ih => simpa using ih hw.of_cons

lemma expand_isWalk (hw : G.IsWalk w) : H.IsWalk (M.expand w hw) := by
  induction w with
  | nil x => exact .nil (M.vertex ⟨x, hw.first_mem⟩).property
  | cons x e w ih => exact (M.routeFrom_isTrail _).isWalk.append (ih hw.of_cons) (by simp)

@[simp]
lemma expand_nonempty_iff (hw : G.IsWalk w) : (M.expand w hw).Nonempty ↔ w.Nonempty := by
  cases w with
  | nil x => simp [expand]
  | cons x e w => simp [M.routeFrom_nonempty]

lemma expand_nonempty (hw : G.IsWalk w) (hne : w.Nonempty) : (M.expand w hw).Nonempty :=
  (M.expand_nonempty_iff hw).mpr hne

@[simp]
lemma expand_isClosed_iff (hw : G.IsWalk w) : (M.expand w hw).IsClosed ↔ w.IsClosed := by
  change (M.expand w hw).first = (M.expand w hw).last ↔ w.first = w.last
  simp only [expand_first, expand_last]
  exact ⟨fun h ↦ congrArg Subtype.val (M.vertex.injective (Subtype.ext h)),
    fun h ↦ congrArg (fun v ↦ (M.vertex v).val) (Subtype.ext h)⟩

lemma expand_append (M : Immersion G H) (h₁ : G.IsWalk w₁) (h₂ : G.IsWalk w₂)
    (heq : w₁.last = w₂.first) :
    M.expand (w₁ ++ w₂) (h₁.append h₂ heq) = M.expand w₁ h₁ ++ M.expand w₂ h₂ := by
  induction w₁ with
  | nil x => rfl
  | cons x e w ih =>
    simp only [cons_append, expand_cons, append_assoc]
    rw [ih h₁.of_cons (by simpa using heq)]
    rfl

lemma mem_expand_edgeSet (M : Immersion G H) (hw : G.IsWalk w) (f : δ) :
    f ∈ E(M.expand w hw) ↔ ∃ e : E(G), e.val ∈ w.edge ∧ f ∈ E(M.route e) := by
  induction w with
  | nil x => simp [expand]
  | cons x e w ih =>
    simp only [expand_cons, append_edgeSet, mem_union, routeFrom_edgeSet, ih, cons_edge,
      List.mem_cons]
    constructor
    · rintro (hf | ⟨e', he', hf⟩)
      · exact ⟨⟨e, (cons_isWalk_iff.mp hw).1.edge_mem⟩, .inl rfl, hf⟩
      · exact ⟨e', .inr he', hf⟩
    rintro ⟨⟨e', he'⟩, rfl | he'w, hf⟩
    · exact .inl hf
    · exact .inr ⟨⟨e', he'⟩, he'w, hf⟩

lemma expand_isTrail (hw : G.IsTrail w) : H.IsTrail (M.expand w hw.isWalk) := by
  refine ⟨M.expand_isWalk hw.isWalk, ?_⟩
  induction w with
  | nil x => simp [expand]
  | cons x e w ih =>
    have h := cons_isTrail_iff.mp hw
    rw [expand_cons, append_edge, List.nodup_append]
    refine ⟨(M.routeFrom_isTrail _).edge_nodup, ih h.1, ?_⟩
    rintro f hf f' hg rfl
    have hf' : f ∈ E(M.route ⟨e, h.2.1.edge_mem⟩) := by
      simpa only [← mem_edgeSet_iff, routeFrom_edgeSet] using hf
    obtain ⟨e', he', hf''⟩ := (M.mem_expand_edgeSet hw.isWalk.of_cons f).mp hg
    exact (M.route_edge_disjoint (by rintro rfl; exact h.2.2 he')).notMem_of_mem_left hf' hf''

/-- Nonempty replacement routes cannot remove a repeated edge of the original walk. -/
lemma isTrail_of_expand_isTrail (hw : G.IsWalk w) (hmap : H.IsTrail (M.expand w hw)) :
    G.IsTrail w := by
  induction w with
  | nil x => exact nil_isTrail hw.first_mem
  | cons x e w ih =>
    have he := (cons_isWalk_iff.mp hw).1
    have hnodup : ((M.routeFrom he).edge ++ (M.expand w hw.of_cons).edge).Nodup := by
      simpa only [expand_cons, append_edge] using hmap.edge_nodup
    have htail : H.IsTrail (M.expand w hw.of_cons) :=
      ⟨M.expand_isWalk hw.of_cons, (List.nodup_append.mp hnodup).2.1⟩
    refine cons_isTrail_iff.mpr ⟨ih hw.of_cons htail, he, fun hew ↦ ?_⟩
    have hne := M.route_nonempty ⟨e, he.edge_mem⟩
    have hfirst : hne.firstEdge _ ∈ E(M.routeFrom he) := by
      simpa only [routeFrom_edgeSet, mem_edgeSet_iff] using hne.firstEdge_mem
    have hsecond : hne.firstEdge _ ∈ E(M.expand w hw.of_cons) :=
      (M.mem_expand_edgeSet hw.of_cons _).mpr ⟨⟨e, he.edge_mem⟩, hew, hne.firstEdge_mem⟩
    exact (edgeSet_disjoint_of_append_nodup hmap.edge_nodup).notMem_of_mem_left hfirst hsecond

@[simp]
lemma expand_isTrail_iff (hw : G.IsWalk w) : H.IsTrail (M.expand w hw) ↔ G.IsTrail w :=
  ⟨M.isTrail_of_expand_isTrail hw, fun h ↦ M.expand_isTrail h⟩

/-- Compose immersions by substituting whole routes; no edges are discarded. -/
noncomputable def comp (M : Immersion G H) (N : Immersion H K) : Immersion G K where
  vertex := M.vertex.trans N.vertex
  route e := N.expand (M.route e) (M.route_isTrail e).isWalk
  route_isTrail e := N.expand_isTrail (M.route_isTrail e)
  route_nonempty e := N.expand_nonempty (M.route_isTrail e).isWalk (M.route_nonempty e)
  route_ends e := by
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet e.property
    have he := M.route_ends e
    rw [hxy.ends_eq, Sym2.map_mk] at he ⊢
    simp only [comp_apply] at he
    simp only [comp_apply, Embedding.trans_apply, expand_first, expand_last]
    obtain he | he := Sym2.eq_iff.mp he
    · exact Sym2.eq_iff.mpr <| Or.inl <| ⟨congrArg (fun v ↦ (N.vertex v).val) (Subtype.ext he.1),
        congrArg (fun v ↦ (N.vertex v).val) (Subtype.ext he.2)⟩
    · exact Sym2.eq_iff.mpr <| Or.inr <| ⟨congrArg (fun v ↦ (N.vertex v).val) (Subtype.ext he.1),
        congrArg (fun v ↦ (N.vertex v).val) (Subtype.ext he.2)⟩
  route_edge_disjoint e f hef := by
    refine disjoint_left.mpr fun g hg hg' ↦ ?_
    obtain ⟨i, hi, hgi⟩ := (N.mem_expand_edgeSet _ _).mp hg
    obtain ⟨j, hj, hgj⟩ := (N.mem_expand_edgeSet _ _).mp hg'
    have hij : i ≠ j := by
      rintro rfl
      exact (M.route_edge_disjoint hef).notMem_of_mem_left hi hj
    exact (N.route_edge_disjoint hij).notMem_of_mem_left hgi hgj

@[simp]
lemma comp_vertex (M : Immersion G H) (N : Immersion H K) (v : V(G)) :
    (M.comp N).vertex v = N.vertex (M.vertex v) := rfl

@[simp]
lemma comp_route (M : Immersion G H) (N : Immersion H K) (e : E(G)) :
    (M.comp N).route e = N.expand (M.route e) (M.route_isTrail e).isWalk := rfl

lemma mem_expand_vertexSet (hw : G.IsWalk w) (y : γ) :
    y ∈ V(M.expand w hw) ↔
      (∃ x : V(G), x.val ∈ w ∧ (M.vertex x).val = y) ∨
        ∃ e : E(G), e.val ∈ w.edge ∧ y ∈ V(M.route e) := by
  induction w with
  | nil x =>
    simp only [expand, nil_vertexSet, mem_singleton_iff, mem_nil_iff, nil_edge,
      List.not_mem_nil, false_and, exists_false, or_false]
    exact ⟨fun hy ↦ ⟨⟨x, hw.first_mem⟩, rfl, hy.symm⟩, fun ⟨⟨x', hx'⟩, hxx, hy⟩ ↦ hxx ▸ hy.symm⟩
  | cons x e w ih =>
    rw [expand_cons, append_vertexSet_of_eq (by simp), routeFrom_vertexSet]
    simp only [mem_union, ih, mem_cons_iff, cons_edge, List.mem_cons]
    constructor
    · rintro (hy | ⟨x', hx', hy⟩ | ⟨e', he', hy⟩)
      · exact .inr ⟨⟨e, (cons_isWalk_iff.mp hw).1.edge_mem⟩, .inl rfl, hy⟩
      · exact .inl ⟨x', .inr hx', hy⟩
      · exact .inr ⟨e', .inr he', hy⟩
    rintro (⟨⟨x', hx'⟩, rfl | hx, hy⟩ | ⟨⟨e', he'⟩, rfl | he, hy⟩)
    · left
      rw [← hy, ← routeFrom_vertexSet M (cons_isWalk_iff.mp hw).1]
      change _ ∈ M.routeFrom (cons_isWalk_iff.mp hw).1
      simpa only [routeFrom_first] using (first_mem (w := M.routeFrom (cons_isWalk_iff.mp hw).1))
    · exact .inr (.inl ⟨⟨x', hx'⟩, hx, hy⟩)
    · exact .inl hy
    · exact .inr (.inr ⟨⟨e', he'⟩, he, hy⟩)

/-- Nonempty replacement routes cannot remove a repeated vertex of the original walk. -/
lemma isPath_of_expand_isPath (M : Immersion G H) (hw : G.IsWalk w)
    (hmap : H.IsPath (M.expand w hw)) : G.IsPath w := by
  induction w with
  | nil x => exact nil_isPath hw.first_mem
  | cons x e w ih =>
    have he := (cons_isWalk_iff.mp hw).1
    refine cons_isPath_iff.mpr ⟨he, ih hw.of_cons hmap.of_append_right, fun hxw ↦ ?_⟩
    have hnd : ((M.routeFrom he).vertex.dropLast ++ (M.expand w hw.of_cons).vertex).Nodup := by
      simpa only [expand_cons, append_vertex] using hmap.nodup
    have hfirst : (M.vertex ⟨x, he.left_mem⟩).val ∈ (M.routeFrom he).vertex.dropLast := by
      simpa only [routeFrom_first] using (M.routeFrom_nonempty he).mem_first_vertex_dropLast
    have hsecond : (M.vertex ⟨x, he.left_mem⟩).val ∈ (M.expand w hw.of_cons).vertex :=
      (M.mem_expand_vertexSet hw.of_cons _).mpr (.inl ⟨⟨x, he.left_mem⟩, hxw, rfl⟩)
    exact List.disjoint_of_nodup_append hnd hfirst hsecond

/-- Substitution cannot remove an extra visit to a vertex of a closed walk. -/
lemma isCyclicWalk_of_expand_isCyclicWalk (hw : G.IsWalk w)
    (hmap : H.IsCyclicWalk (M.expand w hw)) : G.IsCyclicWalk w := by
  have hn := (M.expand_nonempty_iff hw).mp hmap.nonempty
  refine ⟨⟨M.isTrail_of_expand_isTrail hw hmap.isTrail, hn,
    (M.expand_isClosed_iff hw).mp hmap.isClosed⟩, ?_⟩
  cases w with
  | nil x => exact (nil_not_nonempty hn).elim
  | cons x e w =>
    have hp := hmap.tail_isPath
    rw [expand_cons, tail_append (M.routeFrom_nonempty _)] at hp
    exact (M.isPath_of_expand_isPath hw.of_cons hp.of_append_right).nodup

lemma mem_expand_internalVertexSet (M : Immersion G H) (hw : G.IsWalk w) (y : γ) :
    y ∈ (M.expand w hw).internalVertexSet ↔
      (∃ x : V(G), x.val ∈ w.internalVertexSet ∧ (M.vertex x).val = y) ∨
        ∃ e : E(G), e.val ∈ w.edge ∧ y ∈ (M.route e).internalVertexSet := by
  induction w with | nil x => simp [expand, internalVertexSet] | cons x e w ih => _
  cases w with
  | nil z =>
    have heq : (M.routeFrom (cons_isWalk_iff.mp hw).1).last =
        (M.vertex ⟨z, hw.of_cons.first_mem⟩).val := M.routeFrom_last _
    rw [expand_cons, expand, append_nil heq, routeFrom_internalVertexSet]
    simp only [internalVertexSet_cons_nil, mem_empty_iff_false, false_and, exists_false,
      false_or, cons_edge, nil_edge, List.mem_singleton]
    exact ⟨fun hy ↦ ⟨⟨e, (cons_isWalk_iff.mp hw).1.edge_mem⟩, rfl, hy⟩,
      fun ⟨⟨e', he'⟩, h, hy⟩ ↦ h ▸ hy⟩
  | cons z f w =>
    rw [expand_cons, internalVertexSet_append_of_nonempty (M.routeFrom_nonempty _)
      (M.expand_nonempty _ (by simp)), routeFrom_internalVertexSet, expand_first]
    simp only [mem_union, mem_insert_iff, ih, internalVertexSet_cons_cons, cons_edge,
      List.mem_cons, first_cons]
    constructor
    · rintro (hy | hy | ⟨v, hv, hy⟩ | ⟨e', he', hy⟩) <;> grind
    rintro (⟨⟨v, hv⟩, rfl | hv', hy⟩ | ⟨⟨e', he'⟩, rfl | he, hy⟩) <;> grind

variable {M} {N : Immersion H K}

lemma Strong.comp (hM : M.Strong) (hN : N.Strong) : (M.comp N).Strong := by
  refine fun e ↦ disjoint_left.mpr fun y hy ⟨x, hxy⟩ ↦ ?_
  obtain ⟨v, hv, hvy⟩ | ⟨f, hf, hfy⟩ :=
    (N.mem_expand_internalVertexSet (M.route_isTrail e).isWalk y).mp hy
  · obtain rfl : v = M.vertex x := N.vertex.injective (Subtype.ext (hvy.trans hxy.symm))
    exact (hM e).notMem_of_mem_left hv ⟨x, rfl⟩
  exact (hN f).notMem_of_mem_left hfy ⟨M.vertex x, hxy⟩

lemma Strong.vertex_mem_routeFrom_iff (hM : M.Strong) (he : G.IsLink e x y) (v : V(G)) :
    (M.vertex v).val ∈ M.routeFrom he ↔ v.val = x ∨ v.val = y := by
  rw [mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last, routeFrom_first, routeFrom_last,
    routeFrom_internalVertexSet]
  have hint : (M.vertex v).val ∉ (M.route ⟨e, he.edge_mem⟩).internalVertexSet :=
    (hM _).notMem_of_mem_right ⟨v, rfl⟩
  simp only [hint, false_or]
  constructor <;> rintro (hv | hv)
  · exact .inl (congrArg Subtype.val (M.vertex.injective (Subtype.ext hv)))
  · exact .inr (congrArg Subtype.val (M.vertex.injective (Subtype.ext hv)))
  · exact .inl (congrArg (fun v ↦ (M.vertex v).val) (Subtype.ext hv))
  · exact .inr (congrArg (fun v ↦ (M.vertex v).val) (Subtype.ext hv))

lemma Strong.vertex_mem_expand_iff (hM : M.Strong) (hw : G.IsWalk w) (v : V(G)) :
    (M.vertex v).val ∈ M.expand w hw ↔ v.val ∈ w := by
  induction w with
  | nil x =>
    simp only [expand, mem_nil_iff]
    exact ⟨fun h ↦ congrArg Subtype.val (M.vertex.injective (Subtype.ext h)),
      fun h ↦ congrArg (fun v ↦ (M.vertex v).val) (Subtype.ext h)⟩
  | cons x e w ih =>
    rw [expand_cons, mem_append_iff_of_eq (by simp), hM.vertex_mem_routeFrom_iff, ih]
    grind

@[simp]
lemma routeFrom_isPath_iff (M : Immersion G H) (he : G.IsLink e x y) :
    H.IsPath (M.routeFrom he) ↔ H.IsPath (M.route ⟨e, he.edge_mem⟩) := by
  unfold routeFrom
  split_ifs <;> simp

@[simp]
lemma routeFrom_isCyclicWalk_iff (M : Immersion G H) (he : G.IsLink e x y) :
    H.IsCyclicWalk (M.routeFrom he) ↔ H.IsCyclicWalk (M.route ⟨e, he.edge_mem⟩) := by
  unfold routeFrom
  split_ifs
  · rfl
  exact ⟨fun h ↦ by simpa using h.reverse, IsCyclicWalk.reverse⟩

private lemma routeFrom_isSimple (M : Immersion G H) (he : G.IsLink e x y)
    (hs : H.IsPath (M.route ⟨e, he.edge_mem⟩) ∨ H.IsCyclicWalk (M.route ⟨e, he.edge_mem⟩)) :
    H.IsPath (M.routeFrom he) ∨ H.IsCyclicWalk (M.routeFrom he) := by
  simpa using hs

private lemma routeFrom_isPath (M : Immersion G H) (he : G.IsLink e x y)
    (hs : H.IsPath (M.route ⟨e, he.edge_mem⟩) ∨ H.IsCyclicWalk (M.route ⟨e, he.edge_mem⟩))
    (hxy : x ≠ y) : H.IsPath (M.routeFrom he) := by
  obtain h | h := M.routeFrom_isSimple he hs
  · exact h
  have hends : (M.vertex ⟨x, he.left_mem⟩).val = (M.vertex ⟨y, he.right_mem⟩).val := by
    simpa using h.isClosed.eq
  exact (hxy (congrArg Subtype.val (M.vertex.injective (Subtype.ext hends)))).elim

private lemma eq_end_of_mem_routeFrom_of_mem_expand (hM : M.Strong)
    (hdisj : Pairwise (Disjoint on fun e ↦ (M.route e).internalVertexSet))
    (he : G.IsLink e x y) (hw : G.IsWalk w) (hew : e ∉ w.edge) {z : γ}
    (hz : z ∈ M.routeFrom he) (hzw : z ∈ M.expand w hw) :
    z = (M.routeFrom he).first ∨ z = (M.routeFrom he).last := by
  obtain hz | hz | hz := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hz
  · exact .inl hz
  · rw [routeFrom_internalVertexSet] at hz
    obtain ⟨v, hv, hvz⟩ | ⟨f, hf, hfz⟩ := (M.mem_expand_vertexSet hw z).mp hzw
    · exact ((hM _).notMem_of_mem_left hz ⟨v, hvz⟩).elim
    obtain hfz | hfz | hfz := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hfz
    · exact ((hM _).notMem_of_mem_left hz (hfz ▸ (M.ends_mem_vertex_range f).1)).elim
    · exact ((hdisj (by rintro rfl; exact hew hf)).notMem_of_mem_left hz hfz).elim
    · exact ((hM _).notMem_of_mem_left hz (hfz ▸ (M.ends_mem_vertex_range f).2)).elim
  exact .inr hz

lemma Topological.expand_isPath (hM : M.Topological) (hw : G.IsPath w) :
    H.IsPath (M.expand w hw.isWalk) := by
  induction w with
  | nil x => exact nil_isPath (M.vertex ⟨x, hw.isWalk.first_mem⟩).property
  | cons x e w ih =>
    have hp := cons_isPath_iff.mp hw
    have hxy : x ≠ w.first := fun h ↦ hp.2.2 (h ▸ first_mem)
    refine (M.routeFrom_isPath hp.1 (hM.2.1 _) hxy).append (ih hp.2.1) (by simp) fun y hy hyw ↦ ?_
    obtain hy | hy := eq_end_of_mem_routeFrom_of_mem_expand hM.1 hM.2.2 hp.1 hp.2.1.isWalk
      (cons_isTrail_iff.mp hw.isTrail).2.2 hy hyw
    · rw [hy, routeFrom_first] at hyw
      exact (hp.2.2 ((hM.1.vertex_mem_expand_iff hp.2.1.isWalk _).mp hyw)).elim
    exact hy

lemma Topological.expand_isCyclicWalk (hM : M.Topological) (hw : G.IsCyclicWalk w) :
    H.IsCyclicWalk (M.expand w hw.isWalk) := by
  have hclosed := (M.expand_isClosed_iff hw.isWalk).mpr hw.isClosed
  cases w with
  | nil x => exact (nil_not_nonempty hw.nonempty).elim
  | cons x e w =>
    have he := (cons_isWalk_iff.mp hw.isWalk).1
    have hp : G.IsPath w := by simpa using hw.tail_isPath
    obtain rfl : x = w.last := hw.isClosed
    cases w with
    | nil y =>
      have horient : H.IsCyclicWalk (M.routeFrom he) := by
        obtain h | h := M.routeFrom_isSimple he (hM.2.1 _)
        · have hends : (M.routeFrom he).first = (M.routeFrom he).last := by simp
          exact ((M.routeFrom_nonempty he).not_nil (h.first_eq_last_iff.mp hends)).elim
        exact h
      have hy : y ∈ V(G) := nil_isWalk_iff.mp hw.isWalk.of_cons
      have hlast : (M.routeFrom he).last = (M.vertex ⟨y, hy⟩).val := by
        simpa only [nil_first] using M.routeFrom_last he
      change H.IsCyclicWalk (M.routeFrom he ++ nil (M.vertex ⟨y, hy⟩).val)
      rwa [append_nil hlast]
    | cons y f w =>
      have hxy : w.last ≠ (cons y f w).first :=
         ((show (cons y f w).Nonempty by simp).first_ne_last_of_nodup hp.nodup).symm
      have ho := M.routeFrom_isPath he (hM.2.1 _) hxy
      have htail : H.IsPath (M.expand (cons _ e (cons y f w)) hw.isWalk).tail := by
        rw [expand_cons, tail_append (M.routeFrom_nonempty he)]
        apply (ho.sublist (tail_isSuffix _).isSublist).append (hM.expand_isPath hp) (by simp)
        intro z hz hzw
        obtain hz' | hz' := eq_end_of_mem_routeFrom_of_mem_expand hM.1 hM.2.2 he hp.isWalk
          ((cons_isTrail_iff.mp hw.isTrail).2.2) ((tail_isSuffix _).mem hz) hzw
        · exact (first_notMem_tail_of_nodup ho.nodup (M.routeFrom_nonempty he) (hz' ▸ hz)).elim
        · simpa using hz'
      exact ⟨⟨M.expand_isTrail hw.isTrail, M.expand_nonempty hw.isWalk hw.nonempty, hclosed⟩,
        htail.nodup⟩

@[simp]
lemma Topological.expand_isPath_iff (hM : M.Topological) (hw : G.IsWalk w) :
    H.IsPath (M.expand w hw) ↔ G.IsPath w :=
  ⟨M.isPath_of_expand_isPath hw, fun h ↦ hM.expand_isPath h⟩

@[simp]
lemma Topological.expand_isCyclicWalk_iff (hM : M.Topological) (hw : G.IsWalk w) :
    H.IsCyclicWalk (M.expand w hw) ↔ G.IsCyclicWalk w :=
  ⟨M.isCyclicWalk_of_expand_isCyclicWalk hw, fun h ↦ hM.expand_isCyclicWalk h⟩

lemma Topological.comp (hM : M.Topological) (hN : N.Topological) : (M.comp N).Topological := by
  refine ⟨hM.1.comp hN.1, fun e ↦ (hM.2.1 e).elim (fun h ↦ .inl (hN.expand_isPath h))
    (fun h ↦ .inr (hN.expand_isCyclicWalk h)), fun e f hef ↦ disjoint_left.mpr fun y hye hyf ↦ ?_⟩
  obtain ⟨u, hu, huy⟩ | ⟨i, hi, hiy⟩ := (N.mem_expand_internalVertexSet _ _).mp hye <;>
    obtain ⟨v, hv, hvy⟩ | ⟨j, hj, hjy⟩ := (N.mem_expand_internalVertexSet _ _).mp hyf
  · obtain rfl : u = v := N.vertex.injective (Subtype.ext (huy.trans hvy.symm))
    exact (hM.2.2 hef).notMem_of_mem_left hu hv
  · exact (hN.1 j).notMem_of_mem_left hjy ⟨u, huy⟩
  · exact (hN.1 i).notMem_of_mem_left hiy ⟨v, hvy⟩
  · have hij : i ≠ j := by
      rintro rfl
      exact (M.route_edge_disjoint hef).notMem_of_mem_left hi hj
    exact (hN.2.2 hij).notMem_of_mem_left hiy hjy

/-- Every vertex and edge of a composite image already belongs to the second image. -/
lemma comp_image_le (M : Immersion G H) (N : Immersion H K) : (M.comp N).Image ≤ N.Image := by
  refine le_of_le_le_subset_subset (M.comp N).image_le N.image_le (fun y hy ↦ ?_) (fun f hf ↦ ?_)
  · rw [(M.comp N).image_vertexSet] at hy
    rw [N.image_vertexSet]
    obtain ⟨v, rfl⟩ | hy := hy
    · exact .inl ⟨M.vertex v, rfl⟩
    obtain ⟨e, he⟩ := mem_iUnion.mp hy
    obtain ⟨v, hv, hvy⟩ | ⟨f, hf, hfy⟩ := (N.mem_expand_vertexSet _ _).mp he
    · exact .inl ⟨v, hvy⟩
    · exact .inr (mem_iUnion.mpr ⟨f, hfy⟩)
  rw [(M.comp N).image_edgeSet] at hf
  rw [N.image_edgeSet]
  obtain ⟨e, he⟩ := mem_iUnion.mp hf
  obtain ⟨g, hg, hgf⟩ := (N.mem_expand_edgeSet _ _).mp he
  exact mem_iUnion.mpr ⟨g, hgf⟩

/-- A surjective first factor preserves the entire image of the second factor, including
its isolated branch vertices. -/
lemma Surjective.comp_image (hM : M.Surjective) (N : Immersion H K) :
    (M.comp N).Image = N.Image := by
  refine ext_of_le_le (M.comp N).image_le N.image_le ?_ ?_
  · refine (M.comp_image_le N).vertexSet_mono.antisymm fun y hy ↦ ?_
    rw [(M.comp N).image_vertexSet]
    rw [N.image_vertexSet] at hy
    obtain ⟨x, rfl⟩ | hy := hy
    · obtain ⟨v, hv⟩ | hx := hM.vertexSet_eq.ge x.property
      · exact Or.inl ⟨v, congrArg (fun z : V(H) ↦ (N.vertex z).1) (Subtype.ext hv)⟩
      obtain ⟨e, he⟩ := mem_iUnion.mp hx
      exact Or.inr <| mem_iUnion.mpr ⟨e, (N.mem_expand_vertexSet _ _).mpr (.inl ⟨x, he, rfl⟩)⟩
    obtain ⟨e, he⟩ := mem_iUnion.mp hy
    obtain ⟨f, hf⟩ := mem_iUnion.mp (hM.edgeSet_eq.ge e.property)
    exact Or.inr <| mem_iUnion.mpr ⟨f, (N.mem_expand_vertexSet _ _).mpr (.inr ⟨e, hf, he⟩)⟩
  refine (M.comp_image_le N).edgeSet_mono.antisymm fun e he ↦ ?_
  rw [(M.comp N).image_edgeSet]
  rw [N.image_edgeSet] at he
  obtain ⟨f, hf⟩ := mem_iUnion.mp he
  obtain ⟨g, hg⟩ := mem_iUnion.mp <| hM.edgeSet_eq.ge f.property
  exact mem_iUnion.mpr ⟨g, (N.mem_expand_edgeSet _ _).mpr ⟨f, hg, hf⟩⟩

lemma Surjective.comp_iff (hM : M.Surjective) (N : Immersion H K) :
    (M.comp N).Surjective ↔ N.Surjective := by
  change (M.comp N).Image = K ↔ N.Image = K
  rw [hM.comp_image N]

lemma Surjective.comp (hM : M.Surjective) (hN : N.Surjective) : (M.comp N).Surjective :=
  (hM.comp_iff N).mpr hN

end Graph.Immersion
