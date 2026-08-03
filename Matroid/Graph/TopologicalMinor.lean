module

public import Matroid.Graph.Hom
public import Matroid.Graph.Map
public import Matroid.Graph.Minor.Defs
public import Matroid.Graph.Simple
public import Matroid.Graph.WList.TakeDrop.Index

@[expose] public section

variable {α β γ δ ι : Type*} {G H : Graph α β} {u v x y z : α} {e f g : β}
  {X : Set α} {F : Set β} {P C W : WList α β} {n : ℕ}

open Set WList Function
open scoped Sym2

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

/-- A subdivision model of the graph `H` in `G`.

Unlike `TopologicalMinor`, the pattern and host graphs may have different vertex and edge types.
Thus an edge label of `H` need not occur in its corresponding route in `G`.

Supports loops (via cyclic-walk routes) and parallel edges (via `route_edge_disjoint`). -/
structure TopologicalModel (H : Graph γ δ) (G : Graph α β) where
  branchVertex : V(H) ↪ V(G)
  route : E(H) → WList α β
  route_isSimple : ∀ e, G.IsPath (route e) ∨ G.IsCyclicWalk (route e)
  route_nonempty : ∀ e, (route e).Nonempty
  route_ends : ∀ e,
    Sym2.map (fun x : V(H) ↦ (branchVertex x).1) (H.ends e) =
      s((route e).first, (route e).last)
  route_internal_disjoint_branchVertices : ∀ e,
    Disjoint (route e).internalVertexSet (range fun x : V(H) ↦ (branchVertex x).1)
  route_internal_disjoint : ∀ e f, e ≠ f →
    Disjoint (route e).internalVertexSet (route f).internalVertexSet
  route_edge_disjoint : ∀ e f, e ≠ f → Disjoint E(route e) E(route f)

namespace TopologicalModel

/-- Construct a topological model of a simple graph from paths joining its branch vertices.

This is the convenient constructor for the one-off `K₃,₃` and `K₅` constructions. The general
`TopologicalModel` structure also permits cyclic routes for loops and distinct routes for parallel
edges. -/
noncomputable def ofPathRoutes {H : Graph γ δ} {G : Graph α β} [H.Simple]
    (branch : V(H) → α)
    (branch_mem : ∀ x, branch x ∈ V(G)) (branch_injective : Function.Injective branch)
    (route : E(H) → WList α β) (route_isPath : ∀ e, G.IsPath (route e))
    (route_ends : ∀ e, Sym2.map branch (H.ends e) = s((route e).first, (route e).last))
    (route_internal_disjoint_branch : ∀ e,
      Disjoint (route e).internalVertexSet (Set.range branch))
    (route_internal_disjoint : ∀ e f, e ≠ f →
      Disjoint (route e).internalVertexSet (route f).internalVertexSet) :
    H.TopologicalModel G := by
  let branchVertex : V(H) ↪ V(G) :=
    { toFun := fun x ↦ ⟨branch x, branch_mem x⟩
      inj' := fun _ _ h ↦ branch_injective (congrArg Subtype.val h) }
  have hends : ∀ e : E(H), ∃ u v : V(H), u ≠ v ∧
      s(branch u, branch v) = s((route e).first, (route e).last) := by
    rintro e
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
    have h : H.ends e = s(⟨u, huv.left_mem⟩, ⟨v, huv.right_mem⟩) := huv.ends_eq
    refine ⟨⟨u, huv.left_mem⟩, ⟨v, huv.right_mem⟩,
      fun hne ↦ huv.ne (congrArg Subtype.val hne), ?_⟩
    rw [← route_ends e, h, Sym2.map_mk]
  have hmem_range : ∀ (e : E(H)) {x : α}, x = (route e).first ∨ x = (route e).last →
      x ∈ range branch := by
    rintro e x hx
    obtain ⟨u, v, -, hend⟩ := hends e
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hend <;> obtain rfl | rfl := hx
    · exact ⟨u, h1⟩
    · exact ⟨v, h2⟩
    · exact ⟨v, h2⟩
    exact ⟨u, h1⟩
  have route_nonempty : ∀ e, (route e).Nonempty := by
    rintro e
    obtain ⟨u, v, huv, hend⟩ := hends e
    refine (first_ne_last_iff (route_isPath e).nodup).mp fun h ↦ huv (branch_injective ?_)
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hend
    · exact h1.trans (h.trans h2.symm)
    exact h1.trans (h.symm.trans h2.symm)
  have hinter : ∀ (e f : E(H)), e ≠ f → ∀ x ∈ route e, x ∈ route f →
      x = (route e).first ∨ x = (route e).last := by
    rintro e f hef x hxe hxf
    by_contra hx
    simp only [not_or] at hx
    have hxi := ((mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxe).resolve_left
      hx.1).resolve_right hx.2
    obtain h1 | h1 | h1 := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxf
    · exact (route_internal_disjoint_branch e).notMem_of_mem_left hxi (hmem_range f (Or.inl h1))
    · exact (route_internal_disjoint e f hef).notMem_of_mem_left hxi h1
    exact (route_internal_disjoint_branch e).notMem_of_mem_left hxi (hmem_range f (Or.inr h1))
  have key : ∀ (g : β) (p q : E(H)), p ≠ q → g ∈ E(route p) → g ∈ E(route q) →
      G.IsLink g (route p).first (route p).last := by
    rintro g p q hpq hgp hgq
    obtain ⟨a, b, hab⟩ := exists_dInc_of_mem_edge hgp
    obtain ⟨c, d, hcd⟩ := exists_dInc_of_mem_edge hgq
    have hmem : a ∈ route q ∧ b ∈ route q := by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := ((route_isPath p).isWalk.isLink_of_dInc hab)
        |>.eq_and_eq_or_eq_and_eq ((route_isPath q).isWalk.isLink_of_dInc hcd)
      · exact ⟨hcd.left_mem, hcd.right_mem⟩
      exact ⟨hcd.right_mem, hcd.left_mem⟩
    have hlen := Nat.succ_le_of_lt (route_nonempty p).length_pos |>.eq_of_not_lt'
      <| one_lt_length_iff.not.mpr <| (route_isPath p).not_nontrivial_of_dInc rfl rfl hab
      (hinter p q hpq a hab.left_mem hmem.1) (hinter p q hpq b hab.right_mem hmem.2)
    obtain ⟨u, g', v, heq⟩ := (route p).length_eq_one_iff.mp hlen
    obtain rfl : g = g' := by simpa [heq] using hgp
    have hw := (route_isPath p).isWalk
    rw [heq] at hw ⊢
    exact (cons_isWalk_iff.mp hw).1
  have route_edge_disjoint : ∀ e f, e ≠ f → Disjoint E(route e) E(route f) := by
    rintro e f hef
    refine disjoint_left.mpr fun g hge hgf ↦ hef (ends_injective H
      (Sym2.map.injective branch_injective ?_))
    rw [route_ends e, route_ends f]
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := (key g e f hef hge hgf).eq_and_eq_or_eq_and_eq
      (key g f e hef.symm hgf hge)
    · rw [h1, h2]
    rw [h1, h2, Sym2.eq_swap]
  exact
    { branchVertex := branchVertex
      route := route
      route_isSimple := fun e ↦ Or.inl (route_isPath e)
      route_nonempty := route_nonempty
      route_ends := route_ends
      route_internal_disjoint_branchVertices := route_internal_disjoint_branch
      route_internal_disjoint := route_internal_disjoint
      route_edge_disjoint := route_edge_disjoint }

end TopologicalModel

/-- The isomorphism-invariant statement that `H` is a topological minor of `G`. -/
def IsTopologicalMinor (H : Graph γ δ) (G : Graph α β) : Prop :=
  Nonempty (H.TopologicalModel G)

/-- An indexed family of subgraphs of `G`, each collapsed to a single edge between two
distinguished vertices. Internal vertices of each component appear in no other component. -/
structure SubgraphReplacement (G : Graph α β) (ι : Type*) where
  component : ι → Graph α β
  left : ι → α
  right : ι → α
  edge : ι → β
  component_le : ∀ i, component i ≤ G
  realization : ∀ i, ∃ W, ((component i).IsPath W ∨ (component i).IsCyclicWalk W) ∧
    edge i ∈ E(W) ∧ W.first = left i ∧ W.last = right i
  interior_disjoint : ∀ ⦃i j⦄, i ≠ j →
    Disjoint (V(component i) \ {left i, right i}) V(component j)
  edge_injective : Function.Injective edge

namespace SubgraphReplacement

variable (M : G.SubgraphReplacement ι)

noncomputable def walk (i : ι) : WList α β := (M.realization i).choose

lemma walk_isSimple (i : ι) :
    (M.component i).IsPath (M.walk i) ∨ (M.component i).IsCyclicWalk (M.walk i) :=
  (M.realization i).choose_spec.1

lemma walk_isTrail (i : ι) : (M.component i).IsTrail (M.walk i) :=
  (M.walk_isSimple i).elim (·.isTrail) (·.isTrail)

lemma edge_mem_walk (i : ι) : M.edge i ∈ E(M.walk i) :=
  (M.realization i).choose_spec.2.1

lemma walk_first (i : ι) : (M.walk i).first = M.left i :=
  (M.realization i).choose_spec.2.2.1

lemma walk_last (i : ι) : (M.walk i).last = M.right i :=
  (M.realization i).choose_spec.2.2.2

/-- The graph obtained by replacing each component with its selected edge. -/
@[simps]
def replacementGraph : Graph α β where
  vertexSet := ⋃ i, {M.left i, M.right i}
  edgeSet := range M.edge
  IsLink e x y := ∃ i, e = M.edge i ∧
    ((x = M.left i ∧ y = M.right i) ∨ (x = M.right i ∧ y = M.left i))
  isLink_symm e _ := ⟨by
    rintro x y ⟨i, rfl, hxy | hxy⟩
    · exact ⟨i, rfl, Or.inr ⟨hxy.2, hxy.1⟩⟩
    · exact ⟨i, rfl, Or.inl ⟨hxy.2, hxy.1⟩⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨i, rfl, hxy⟩ ⟨j, hj, hvw⟩
    obtain rfl := M.edge_injective hj
    grind
  left_mem_of_isLink := by
    rintro e x y ⟨i, rfl, hxy | hxy⟩ <;> exact mem_iUnion.2 ⟨i, by simp [hxy]⟩
  edge_mem_iff_exists_isLink e :=
    ⟨fun ⟨i, hi⟩ ↦ hi ▸ ⟨M.left i, M.right i, ⟨i, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩,
      fun ⟨x, y, i, hei, _⟩ ↦ ⟨i, hei.symm⟩⟩

lemma replacementGraph_isLink_left_right (i : ι) :
    M.replacementGraph.IsLink (M.edge i) (M.left i) (M.right i) :=
  ⟨i, rfl, Or.inl ⟨rfl, rfl⟩⟩

noncomputable def source (e : E(M.replacementGraph)) : ι :=
  (congrArg (e.val ∈ ·) M.edgeSet_replacementGraph) ▸ e.prop |>.choose

lemma edge_source (e : E(M.replacementGraph)) : M.edge (M.source e) = e.val :=
  (congrArg (e.val ∈ ·) M.edgeSet_replacementGraph) ▸ e.prop |>.choose_spec

lemma source_eq_of_edge_eq {i : ι} {e : E(M.replacementGraph)} (hi : M.edge i = e.val) :
    M.source e = i := M.edge_injective ((M.edge_source e).trans hi.symm)

/-- Internal vertices of the chosen realization of component `i`. -/
def internal (i : ι) : Set α := {x | x ∈ (M.walk i).vertex.tail.dropLast}

lemma walk_nonempty (i : ι) : (M.walk i).Nonempty :=
  nonempty_iff_exists_edge.mpr ⟨M.edge i, M.edge_mem_walk i⟩

lemma internal_subset_component (i : ι) : M.internal i ⊆ V(M.component i) := by
  rintro x hx
  exact M.walk_isTrail i |>.vertexSet_subset <| List.mem_of_mem_tail (List.mem_of_mem_dropLast hx)

lemma walk_tail_getLast (i : ι) (htail_ne : (M.walk i).vertex.tail ≠ []) :
    (M.walk i).vertex.tail.getLast htail_ne = (M.walk i).last := by
  rw [List.getLast_tail, vertex_getLast]

lemma vertex_tail_nodup_of_isSimple {i : ι}
    (h : (M.component i).IsPath (M.walk i) ∨ (M.component i).IsCyclicWalk (M.walk i)) :
    (M.walk i).vertex.tail.Nodup := by
  obtain hP | hC := h
  · exact hP.nodup.tail
  simpa [(M.walk_nonempty i).vertex_tail] using hC.nodup

lemma internal_disjoint_ends (i : ι) : Disjoint (M.internal i) {M.left i, M.right i} := by
  refine disjoint_left.mpr fun x hxI hxEnds ↦ ?_
  simp only [internal] at hxI
  rw [← M.walk_first i, ← M.walk_last i] at hxEnds
  have hx_tail : x ∈ (M.walk i).vertex.tail := List.mem_of_mem_dropLast hxI
  have htail_ne : (M.walk i).vertex.tail ≠ [] := List.ne_nil_of_mem hx_tail
  have hnd_tail := M.vertex_tail_nodup_of_isSimple (M.walk_isSimple i)
  obtain hP | hC := M.walk_isSimple i
  · have hx_mem_tail : x ∈ (M.walk i).tail := by
      change x ∈ (M.walk i).tail.vertex
      rwa [(M.walk_nonempty i).vertex_tail]
    have hne_first : x ≠ (M.walk i).first :=
      fun h ↦ first_notMem_tail_of_nodup hP.nodup (M.walk_nonempty i) (h ▸ hx_mem_tail)
    obtain rfl | rfl := hxEnds
    · exact hne_first rfl
    exact hnd_tail.getLast_not_mem_dropLast htail_ne <| (M.walk_tail_getLast i htail_ne).symm ▸ hxI
  · obtain rfl | rfl := hxEnds
    · exact hnd_tail.getLast_not_mem_dropLast htail_ne
        <| (M.walk_tail_getLast i htail_ne).trans hC.isClosed.symm ▸ hxI
    · exact hnd_tail.getLast_not_mem_dropLast htail_ne <|
        (M.walk_tail_getLast i htail_ne).symm ▸ hxI

-- lemma internal_subset_component_interior (i : ι) :
--     M.internal i ⊆ V(M.component i) \ {M.left i, M.right i} :=
--   subset_diff.mpr ⟨M.internal_subset_component i, M.internal_disjoint_ends i⟩

lemma internal_disjoint_component_of_ne {i j : ι} (hij : i ≠ j) :
    Disjoint (M.internal i) V(M.component j) :=
  (M.interior_disjoint hij).mono_left <|
    subset_sdiff.mpr ⟨M.internal_subset_component i, M.internal_disjoint_ends i⟩

lemma ends_mem_component (i : ι) : M.left i ∈ V(M.component i) ∧ M.right i ∈ V(M.component i) :=
  ⟨M.walk_first i ▸ (M.walk_isTrail i |>.vertexSet_subset first_mem),
    M.walk_last i ▸ (M.walk_isTrail i |>.vertexSet_subset last_mem)⟩

lemma internal_disjoint_replacement_vertices (i : ι) :
    Disjoint (M.internal i) V(M.replacementGraph) := by
  simp only [vertexSet_replacementGraph, disjoint_iUnion_right]
  rintro j
  obtain rfl | hij := eq_or_ne i j
  · exact M.internal_disjoint_ends i
  refine (M.internal_disjoint_component_of_ne hij).mono_right fun x ↦ ?_
  grind [M.ends_mem_component j]

lemma mem_internal_of_mem_ne_ends {i : ι} {x : α} (hx : x ∈ M.walk i)
    (hne : x ≠ M.left i ∧ x ≠ M.right i) : x ∈ M.internal i := by
  rw [← M.walk_first i, ← M.walk_last i] at hne
  obtain rfl | hx_tail := (mem_iff_eq_vertex_first_or_mem_tail).mp hx
  · exact (hne.1 rfl).elim
  have htail_ne : (M.walk i).vertex.tail ≠ [] := List.ne_nil_of_mem hx_tail
  obtain hx_dl | rfl := (List.mem_iff_mem_dropLast_or_eq_getLast htail_ne).mp hx_tail
  · exact hx_dl
  exact (hne.2 ((M.walk_tail_getLast i htail_ne).symm ▸ rfl)).elim

lemma walk_inter_subset_ends {i j : ι} (hij : i ≠ j) :
    V(M.walk i) ∩ V(M.walk j) ⊆ {M.left i, M.right i} := by
  rintro x ⟨hxi, hxj⟩
  by_contra hx
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
  have hxI : x ∈ M.internal i := M.mem_internal_of_mem_ne_ends hxi hx
  have hxj' : x ∈ V(M.component j) := M.walk_isTrail j |>.vertexSet_subset hxj
  exact (M.internal_disjoint_component_of_ne hij).notMem_of_mem_left hxI hxj'

/-- The replacement graph is a topological minor of the ambient graph. -/
noncomputable def topologicalMinor : M.replacementGraph.TopologicalMinor G where
  vertex_subset x hx := by
    simp only [vertexSet_replacementGraph, mem_iUnion, mem_insert_iff, mem_singleton_iff] at hx
    obtain ⟨i, rfl | rfl⟩ := hx
    · exact (M.component_le i).vertexSet_mono (M.ends_mem_component i).1
    exact (M.component_le i).vertexSet_mono (M.ends_mem_component i).2
  map e := M.walk (M.source e)
  mem_map e := by
    simpa [← M.edge_source e] using M.edge_mem_walk (M.source e)
  map_isSimple e :=
    (M.walk_isSimple (M.source e)).imp (·.of_le (M.component_le _)) (·.of_le (M.component_le _))
  map_isLink e := by simpa [M.edge_source e, M.walk_first, M.walk_last] using
    M.replacementGraph_isLink_left_right (M.source e)
  map_ends e := M.internal_disjoint_replacement_vertices (M.source e)
  map_internally_disjoint e f hef := by
    have hsf : M.source e ≠ M.source f := fun h ↦ hef <| Subtype.ext <|
      (M.edge_source e).symm.trans ((congrArg M.edge h).trans (M.edge_source f))
    simpa [M.walk_first, M.walk_last] using M.walk_inter_subset_ends hsf

end SubgraphReplacement

namespace TopologicalModel

variable {J : Graph γ δ} (M : J.TopologicalModel G)

/-- A representative edge label appearing on the route of `e`. -/
noncomputable def repEdge (e : E(J)) : β := (M.route_nonempty e).exists_edge.choose

lemma repEdge_mem (e : E(J)) : M.repEdge e ∈ E(M.route e) :=
  (M.route_nonempty e).exists_edge.choose_spec

lemma repEdge_injective : Injective M.repEdge :=
  fun e f hef ↦ by_contra fun hne ↦
    (M.route_edge_disjoint e f hne).notMem_of_mem_left (M.repEdge_mem e) (hef ▸ M.repEdge_mem f)

lemma mem_internalVertexSet_of_mem_ne_ends {W : WList α β} {x : α} (hx : x ∈ W)
    (hne : x ≠ W.first ∧ x ≠ W.last) : x ∈ W.internalVertexSet := by
  obtain rfl | hx_tail := (mem_iff_eq_vertex_first_or_mem_tail).mp hx
  · exact (hne.1 rfl).elim
  have htail_ne : W.vertex.tail ≠ [] := List.ne_nil_of_mem hx_tail
  obtain hx_dl | rfl := (List.mem_iff_mem_dropLast_or_eq_getLast htail_ne).mp hx_tail
  · exact hx_dl
  exact (hne.2 (by rw [← vertex_getLast, ← List.getLast_tail htail_ne])).elim

variable (M : J.TopologicalModel G)
open Classical

/-- Image of a branch vertex under the model embedding. -/
abbrev branchVal (x : V(J)) : α := (M.branchVertex x).1

lemma branchVal_injective : Injective M.branchVal :=
  fun _ _ h ↦ Subtype.ext <| Subtype.ext_iff.mp <| M.branchVertex.injective (Subtype.ext h)

lemma branchVal_mem (x : V(J)) : M.branchVal x ∈ V(G) := (M.branchVertex x).2

lemma route_ends_eq {e : E(J)} {u v : γ} (huv : J.IsLink e.val u v) :
    s(M.branchVal ⟨u, huv.left_mem⟩, M.branchVal ⟨v, huv.right_mem⟩) =
      s((M.route e).first, (M.route e).last) := by
  have hends : J.ends e = s(⟨u, huv.left_mem⟩, ⟨v, huv.right_mem⟩) := huv.ends_eq
  rw [← M.route_ends e, hends, Sym2.map_mk]

lemma ends_mem_range_branchVal (e : E(J)) : (M.route e).first ∈ range M.branchVal ∧
    (M.route e).last ∈ range M.branchVal := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp (M.route_ends_eq huv)
  · exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  exact ⟨⟨_, h2⟩, ⟨_, h1⟩⟩

lemma eq_ends_of_mem_of_mem_route {e f : E(J)} {x : α} (hef : e ≠ f) (hxe : x ∈ M.route e)
    (hxf : x ∈ M.route f) : x = (M.route e).first ∨ x = (M.route e).last := by
  by_contra hx
  simp only [not_or] at hx
  have hxi := mem_internalVertexSet_of_mem_ne_ends hxe hx
  obtain h1 | h1 | h1 := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxf
  · exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hxi
      (h1 ▸ (M.ends_mem_range_branchVal f).1)
  · exact (M.route_internal_disjoint e f hef).notMem_of_mem_left hxi h1
  exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hxi
    (h1 ▸ (M.ends_mem_range_branchVal f).2)

/-- `PEquiv` associated to an injection out of a subtype. -/
noncomputable def pequivOfSubtypeInj {α β} {s : Set α} (f : ↑s → β) (hf : Injective f) :
    α ≃. β where
  toFun x := if hx : x ∈ s then some (f ⟨x, hx⟩) else none
  invFun y := if hy : ∃ x : ↑s, f x = y then some (Classical.choose hy).1 else none
  inv x y := by split_ifs with hx hy hy <;> grind

lemma pequivOfSubtypeInj_eq {α β} {s : Set α} (f : ↑s → β) (hf : Injective f) {x : α}
    (hx : x ∈ s) : pequivOfSubtypeInj f hf x = some (f ⟨x, hx⟩) := dif_pos hx

/-- Same-carrier copy of `J` whose edges are representative labels from the model routes. -/
noncomputable def normalized : Graph α β where
  vertexSet := range M.branchVal
  edgeSet := range M.repEdge
  IsLink e' x y := ∃ (e : E(J)) (u v : γ) (huv : J.IsLink e.val u v),
    M.repEdge e = e' ∧ x = M.branchVal ⟨u, huv.left_mem⟩ ∧ y = M.branchVal ⟨v, huv.right_mem⟩
  isLink_symm _ _ := ⟨by
    rintro _ _ ⟨e, u, v, huv, rfl, rfl, rfl⟩
    exact ⟨e, v, u, huv.symm, rfl, rfl, rfl⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro _ _ _ _ _ ⟨e, u, v, huv, rfl, rfl, rfl⟩ ⟨_, _, _, huv₂, he, rfl, rfl⟩
    obtain rfl := M.repEdge_injective he
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := huv.left_eq_or_eq huv₂ <;> simp
  left_mem_of_isLink := by
    rintro _ _ _ ⟨_, _, _, _, rfl, rfl, rfl⟩
    exact mem_range_self _
  edge_mem_iff_exists_isLink e' := by
    refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨_, _, e, _, _, _, he, _, _⟩ ↦ ⟨e, he⟩⟩
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
    exact ⟨_, _, e, u, v, huv, he, rfl, rfl⟩

lemma vertexSet_normalized : V(M.normalized) = range M.branchVal := rfl

lemma edgeSet_normalized : E(M.normalized) = range M.repEdge := rfl

lemma normalized_isLink {e : δ} {x y : γ} (hxy : J.IsLink e x y) :
    M.normalized.IsLink (M.repEdge ⟨e, hxy.edge_mem⟩)
      (M.branchVal ⟨x, hxy.left_mem⟩) (M.branchVal ⟨y, hxy.right_mem⟩) :=
  ⟨⟨e, hxy.edge_mem⟩, x, y, hxy, rfl, rfl, rfl⟩

/-- Source edge in `J` of an edge of the normalized copy. -/
noncomputable def source (e : E(M.normalized)) : E(J) :=
  (Equiv.ofInjective M.repEdge M.repEdge_injective).symm ⟨e.val, by
    simpa [edgeSet_normalized] using e.prop⟩

lemma repEdge_source (e : E(M.normalized)) : M.repEdge (M.source e) = e.val :=
  congrArg Subtype.val <|
    (Equiv.ofInjective M.repEdge M.repEdge_injective).apply_symm_apply ⟨e.val, by
      simpa [edgeSet_normalized] using e.prop⟩

/-- Partial equivalence sending each pattern vertex to its branch vertex. -/
noncomputable def vertPEquiv : γ ≃. α :=
  pequivOfSubtypeInj M.branchVal M.branchVal_injective

/-- Partial equivalence sending each pattern edge to its representative route edge. -/
noncomputable def edgePEquiv : δ ≃. β :=
  pequivOfSubtypeInj M.repEdge M.repEdge_injective

lemma vertPEquiv_eq {x : γ} (hx : x ∈ V(J)) :
    M.vertPEquiv x = some (M.branchVal ⟨x, hx⟩) :=
  pequivOfSubtypeInj_eq _ _ hx

lemma edgePEquiv_eq {e : δ} (he : e ∈ E(J)) :
    M.edgePEquiv e = some (M.repEdge ⟨e, he⟩) :=
  pequivOfSubtypeInj_eq _ _ he

lemma mem_symm_pequivOfSubtypeInj {α β} {s : Set α} (f : ↑s → β) (hf : Injective f)
    {a : α} {b : β} (h : a ∈ (pequivOfSubtypeInj f hf).symm b) :
    ∃ ha : a ∈ s, f ⟨a, ha⟩ = b := by
  have h := (PEquiv.eq_some_iff (pequivOfSubtypeInj f hf)).mp (Option.mem_def.mp h)
  have ha : a ∈ s := by
    simpa [pequivOfSubtypeInj, Option.isSome_dite] using congrArg Option.isSome h
  exact ⟨ha, by simpa [pequivOfSubtypeInj_eq f hf ha] using h⟩

/-- The isomorphism from the abstract pattern to its normalized same-carrier copy. -/
noncomputable def isoNormalized : Iso J M.normalized where
  vertMap := M.vertPEquiv
  vertMap_isSome_iff x := by simp [vertPEquiv, pequivOfSubtypeInj, Option.isSome_dite]
  invVertMap_isSome_iff y := by
    simp [vertPEquiv, pequivOfSubtypeInj, PEquiv.symm, Option.isSome_dite, vertexSet_normalized,
      mem_range]
  edgeMap := M.edgePEquiv
  edgeMap_isSome_iff e := by simp [edgePEquiv, pequivOfSubtypeInj, Option.isSome_dite]
  invEdgeMap_isSome_iff e' := by
    simp [edgePEquiv, pequivOfSubtypeInj, PEquiv.symm, Option.isSome_dite, edgeSet_normalized,
      mem_range]
  map_isLink := fun _ _ _ _ _ _ hxy he' hx' hy' ↦ by
    simp only [M.edgePEquiv_eq hxy.edge_mem, M.vertPEquiv_eq hxy.left_mem,
      M.vertPEquiv_eq hxy.right_mem, Option.mem_def, Option.some.injEq] at he' hx' hy'
    subst he' hx' hy'
    exact M.normalized_isLink hxy
  invMap_isLink := fun _ _ _ e x y hxy he hx hy ↦ by
    obtain ⟨e₀, u, v, huv, rfl, rfl, rfl⟩ := hxy
    obtain ⟨heE, he⟩ := mem_symm_pequivOfSubtypeInj _ _ he
    obtain ⟨hxV, hx⟩ := mem_symm_pequivOfSubtypeInj _ _ hx
    obtain ⟨hyV, hy⟩ := mem_symm_pequivOfSubtypeInj _ _ hy
    obtain rfl := congrArg Subtype.val (M.repEdge_injective he)
    obtain rfl := congrArg Subtype.val (M.branchVal_injective hx)
    obtain rfl := congrArg Subtype.val (M.branchVal_injective hy)
    exact huv

/-- The normalized copy is a topological minor of the host. -/
noncomputable def toTopologicalMinor : M.normalized.TopologicalMinor G where
  vertex_subset := by
    rintro _ ⟨x, rfl⟩
    exact M.branchVal_mem x
  map e := M.route (M.source e)
  mem_map e := by simpa [← M.repEdge_source e] using M.repEdge_mem (M.source e)
  map_isSimple e := M.route_isSimple (M.source e)
  map_isLink e := by
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet (M.source e).prop
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp (M.route_ends_eq huv)
    · rw [← M.repEdge_source e, ← h1, ← h2]
      exact M.normalized_isLink huv
    rw [← M.repEdge_source e, ← h1, ← h2]
    exact (M.normalized_isLink huv).symm
  map_ends e := by
    rw [show ({v | v ∈ (M.route (M.source e)).vertex.tail.dropLast} : Set α) =
        (M.route (M.source e)).internalVertexSet from rfl, vertexSet_normalized]
    exact M.route_internal_disjoint_branchVertices (M.source e)
  map_internally_disjoint e f hef := by
    have hsf : M.source e ≠ M.source f := fun h ↦ hef <| Subtype.ext <|
      (M.repEdge_source e).symm.trans <| (congrArg M.repEdge h).trans (M.repEdge_source f)
    exact fun x hx ↦ M.eq_ends_of_mem_of_mem_route hsf hx.1 hx.2

include M in
/-- Normalize an abstract topological model by choosing a same-carrier copy of the pattern
whose edge labels are representative edges of the model routes. -/
theorem exists_iso_topologicalMinor :
    ∃ K : Graph α β, Nonempty (Iso J K) ∧ Nonempty (K.TopologicalMinor G) :=
  ⟨normalized M, ⟨isoNormalized M⟩, ⟨toTopologicalMinor M⟩⟩

end TopologicalModel

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

/-- An edge shared by the branches of two distinct edges is the label of both, hence they agree. -/
lemma eq_of_mem_edgeSet_map {e f : E(G)} {g : β} (hef : e ≠ f) (hge : g ∈ E(h.map e))
    (hgf : g ∈ E(h.map f)) : e.val = g := by
  obtain ⟨a, b, hab⟩ := exists_dInc_of_mem_edge hge
  obtain ⟨c, d, hcd⟩ := exists_dInc_of_mem_edge hgf
  have hmem : a ∈ h.map f ∧ b ∈ h.map f := by
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := ((h.map_isTrail e).isWalk.isLink_of_dInc hab)
      |>.eq_and_eq_or_eq_and_eq ((h.map_isTrail f).isWalk.isLink_of_dInc hcd)
    · exact ⟨hcd.left_mem, hcd.right_mem⟩
    exact ⟨hcd.right_mem, hcd.left_mem⟩
  have ha := h.map_internally_disjoint e f hef ⟨hab.left_mem, hmem.1⟩
  have hb := h.map_internally_disjoint e f hef ⟨hab.right_mem, hmem.2⟩
  simp only [mem_insert_iff, mem_singleton_iff] at ha hb
  obtain hp | hc := h.map_isSimple e
  · have hlen := Nat.succ_le_of_lt (h.map_nonempty e).length_pos |>.eq_of_not_lt'
      <| one_lt_length_iff.not.mpr <| hp.not_nontrivial_of_dInc rfl rfl hab ha hb
    obtain ⟨u, g', v, heq⟩ := (h.map e).length_eq_one_iff.mp hlen
    obtain rfl : g = g' := by simpa [heq] using hge
    simpa [heq] using h.mem_map e
  obtain rfl : b = a := by grind [hc.isClosed, hc.isClosed.symm]
  simpa [hc.eq_loop_of_isLink_self (isLink_iff_dInc.mpr (Or.inl hab))] using h.mem_map e

lemma map_edgeSet_disjoint {e f : E(G)} (hef : e ≠ f) : Disjoint E(h.map e) E(h.map f) :=
  disjoint_left.mpr fun _ hge hgf ↦ hef <| Subtype.ext <|
    (h.eq_of_mem_edgeSet_map hef hge hgf).trans (h.eq_of_mem_edgeSet_map hef.symm hgf hge).symm

/-- Every topological minor is a topological model of itself inside the host graph. -/
def toTopologicalModel : G.TopologicalModel H :=
  let branchVertex : V(G) ↪ V(H) :=
    ⟨fun x ↦ ⟨x.val, h.vertex_subset x.prop⟩,
      fun _ _ hxy ↦ Subtype.ext <| by simpa using hxy⟩
  { branchVertex := branchVertex
    route := h.map
    route_isSimple := h.map_isSimple
    route_nonempty := h.map_nonempty
    route_ends e := by
      have hlink := h.map_isLink e
      have hends : G.ends e =
          s(⟨_, hlink.left_mem⟩, ⟨_, hlink.right_mem⟩) := hlink.ends_eq
      rw [hends, Sym2.map_mk]
      rfl
    route_internal_disjoint_branchVertices e :=
      (h.map_ends e).mono_right fun _ ⟨x, hx⟩ ↦ hx ▸ x.prop
    route_internal_disjoint e f hef := disjoint_left.mpr fun z hze hzf ↦ by
      have hz := h.map_internally_disjoint e f hef
        ⟨mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mpr (Or.inr (Or.inl hze)),
          mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mpr (Or.inr (Or.inl hzf))⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hz
      refine (h.map_ends e).notMem_of_mem_left hze ?_
      obtain rfl | rfl := hz
      · exact (h.map_isLink e).left_mem
      exact (h.map_isLink e).right_mem
    route_edge_disjoint _ _ hef := h.map_edgeSet_disjoint hef }

end TopologicalMinor

namespace TopologicalModel

variable {J : Graph γ δ} {K : Graph α β}

lemma pequiv_inj {α' β'} (F : α' ≃. β') {x y : α'} {z : β'} (hx : F x = some z)
    (hy : F y = some z) : x = y :=
  Option.some_injective _ <| ((PEquiv.eq_some_iff F).mpr hx).symm.trans
    ((PEquiv.eq_some_iff F).mpr hy)

/-- The vertex of `K` matched with a vertex of `J` by an isomorphism. -/
noncomputable def isoVert (F : Iso J K) (x : V(J)) : V(K) :=
  ⟨(F.vertMap x.val).get ((F.vertMap_isSome_iff x.val).mpr x.prop),
    F.toEmb.vertMap_vertexSet (Option.get_mem _)⟩

lemma isoVert_spec (F : Iso J K) (x : V(J)) : F.vertMap x.val = some (isoVert F x).1 :=
  (Option.some_get _).symm

lemma isoVert_injective (F : Iso J K) : Injective (isoVert F) := fun x y hxy ↦
  Subtype.ext <| pequiv_inj F.vertMap (isoVert_spec F x) (hxy ▸ isoVert_spec F y)

/-- The edge of `K` matched with an edge of `J` by an isomorphism. -/
noncomputable def isoEdge (F : Iso J K) (e : E(J)) : E(K) :=
  ⟨(F.edgeMap e.val).get ((F.edgeMap_isSome_iff e.val).mpr e.prop),
    F.toEmb.toHom.edgeMap_edgeSet (Option.get_mem _)⟩

lemma isoEdge_spec (F : Iso J K) (e : E(J)) : F.edgeMap e.val = some (isoEdge F e).1 :=
  (Option.some_get _).symm

lemma isoEdge_injective (F : Iso J K) : Injective (isoEdge F) := fun e f hef ↦
  Subtype.ext <| pequiv_inj F.edgeMap (isoEdge_spec F e) (hef ▸ isoEdge_spec F f)

lemma isoVert_ends (F : Iso J K) (e : E(J)) :
    Sym2.map (isoVert F) (J.ends e) = K.ends (isoEdge F e) := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
  have hJ : J.ends e = s(⟨u, huv.left_mem⟩, ⟨v, huv.right_mem⟩) := huv.ends_eq
  have hK : K.ends (isoEdge F e) =
      s(isoVert F ⟨u, huv.left_mem⟩, isoVert F ⟨v, huv.right_mem⟩) :=
    IsLink.ends_eq <| F.map_isLink huv (isoEdge_spec F e) (isoVert_spec F ⟨u, huv.left_mem⟩)
      (isoVert_spec F ⟨v, huv.right_mem⟩)
  rw [hJ, Sym2.map_mk, hK]

/-- Transport a topological model along an isomorphism of the pattern graph. -/
noncomputable def ofIso (F : Iso J K) (M : K.TopologicalModel G) : J.TopologicalModel G where
  branchVertex := (⟨isoVert F, isoVert_injective F⟩ : V(J) ↪ V(K)).trans M.branchVertex
  route e := M.route (isoEdge F e)
  route_isSimple e := M.route_isSimple _
  route_nonempty e := M.route_nonempty _
  route_ends e := by
    rw [← M.route_ends (isoEdge F e), ← isoVert_ends F e, Sym2.map_map]
    rfl
  route_internal_disjoint_branchVertices e := by
    refine (M.route_internal_disjoint_branchVertices (isoEdge F e)).mono_right ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨isoVert F x, rfl⟩
  route_internal_disjoint _ _ hef :=
    M.route_internal_disjoint _ _ fun heq ↦ hef (isoEdge_injective F heq)
  route_edge_disjoint _ _ hef :=
    M.route_edge_disjoint _ _ fun heq ↦ hef (isoEdge_injective F heq)

end TopologicalModel

/-- The abstract model definition is equivalent to the existing formulation using an isomorphic
same-carrier copy and the label-preserving `TopologicalMinor` structure. -/
theorem isTopologicalMinor_iff_exists_iso_topologicalMinor {J : Graph γ δ} :
    J.IsTopologicalMinor G ↔
      ∃ K : Graph α β, Nonempty (Iso J K) ∧ Nonempty (K.TopologicalMinor G) :=
  ⟨fun ⟨M⟩ ↦ TopologicalModel.exists_iso_topologicalMinor M,
    fun ⟨_, ⟨F⟩, ⟨h⟩⟩ ↦ ⟨TopologicalModel.ofIso F h.toTopologicalModel⟩⟩


section examples

/-- A non-loop edge, packaged as a one-component subgraph replacement. -/
noncomputable def pathReplacement (he : G.IsLink e u v) (hne : u ≠ v) :
    G.SubgraphReplacement PUnit where
  component _ := Graph.singleEdge u v e
  left _ := u
  right _ := v
  edge _ := e
  component_le _ := singleEdge_le_iff.mpr he
  realization _ := by
    have hse : (Graph.singleEdge u v e).IsLink e u v := by simp
    exact ⟨hse.walk, Or.inl (hse.walk_isPath hne), by simp [IsLink.walk], rfl, rfl⟩
  interior_disjoint := by
    rintro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  edge_injective := fun _ _ _ ↦ Subsingleton.elim _ _

/-- A loop edge, packaged as a one-component subgraph replacement. -/
noncomputable def loopReplacement (he : G.IsLink e u u) :
    G.SubgraphReplacement PUnit where
  component _ := Graph.singleEdge u u e
  left _ := u
  right _ := u
  edge _ := e
  component_le _ := singleEdge_le_iff.mpr he
  realization _ := by
    have hse : (Graph.singleEdge u u e).IsLink e u u := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    refine ⟨hse.walk, Or.inr ?_, by simp [IsLink.walk], rfl, rfl⟩
    exact (nil_isPath hse.left_mem).cons_isCyclicWalk hse (by simp)
  interior_disjoint := by
    rintro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  edge_injective := fun _ _ _ ↦ Subsingleton.elim _ _

/-- Two path edges sharing an endpoint, as a two-component replacement. -/
noncomputable def twoPathReplacement (he : G.IsLink e u v) (hf : G.IsLink f v z)
    (hneef : e ≠ f) (huv : u ≠ v) (hvz : v ≠ z) :
    G.SubgraphReplacement Bool where
  component b := bif b then Graph.singleEdge u v e else Graph.singleEdge v z f
  left b := bif b then u else v
  right b := bif b then v else z
  edge b := bif b then e else f
  component_le b := by cases b <;> exact singleEdge_le_iff.mpr ‹_›
  realization b := by
    cases b with
    | true =>
      have hse : (Graph.singleEdge u v e).IsLink e u v := by simp
      exact ⟨hse.walk, Or.inl (hse.walk_isPath huv), by simp [IsLink.walk], rfl, rfl⟩
    | false =>
      have hsf : (Graph.singleEdge v z f).IsLink f v z := by simp
      exact ⟨hsf.walk, Or.inl (hsf.walk_isPath hvz), by simp [IsLink.walk], rfl, rfl⟩
  interior_disjoint := by
    rintro i j hij
    cases i <;> cases j <;> try exact (hij rfl).elim
    all_goals simp [vertexSet_singleEdge]
  edge_injective := by
    rintro b₁ b₂ h
    cases b₁ <;> cases b₂ <;> simp_all [hneef.symm]

example (he : G.IsLink e u v) (hne : u ≠ v) :
    Nonempty ((pathReplacement he hne).replacementGraph.TopologicalMinor G) :=
  ⟨(pathReplacement he hne).topologicalMinor⟩

example (he : G.IsLink e u u) :
    Nonempty ((loopReplacement he).replacementGraph.TopologicalMinor G) :=
  ⟨(loopReplacement he).topologicalMinor⟩

example (he : G.IsLink e u v) (hf : G.IsLink f v z) (hneef : e ≠ f) (huv : u ≠ v) (hvz : v ≠ z) :
    Nonempty ((twoPathReplacement he hf hneef huv hvz).replacementGraph.TopologicalMinor G) :=
  ⟨(twoPathReplacement he hf hneef huv hvz).topologicalMinor⟩

end examples

namespace TopologicalMinor

variable (h : G.TopologicalMinor H)

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
      ofPred_false, empty_disjoint]
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
    rw [mem_ofPred_eq, ← List.tail_dropLast] at this
    rw [List.mem_iff_eq_head_or_mem_tail (List.ne_nil_of_mem hxdl)] at hxdl
    rw [hxdl.resolve_right this, ← vertex_head, mem_singleton_iff, List.head_dropLast]
  have hxT := (h.map e |>.suffixFromEdge_vertex_isSuffix_tail (by use e, h.mem_map e)).mem h2
  have := h.map_ends e |>.notMem_of_mem_right hx
  rw [mem_ofPred_eq] at this
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
        refine Or.inr ⟨e, Or.inl <| by simpa [hfirst]⟩
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
        exact Or.inr ⟨e, Or.inr <| by simpa [hlast]⟩
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
