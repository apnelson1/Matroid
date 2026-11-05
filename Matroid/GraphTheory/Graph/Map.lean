module

public import Matroid.Graph.Subgraph.Compatible
public import Matroid.Graph.Subgraph.Delete
public import Matroid.Graph.Walk.Cycle
import all Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Delete


@[expose] public section

variable {α β : Type*} {x y z u v w a b : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α} {W : WList α β}

open Set Function WList

open scoped Sym2

namespace Graph

@[simps (attr := grind =)]
def ofPFun (f : β →. Sym2 α) : Graph α β where
  vertexSet := {x | ∃ y e, f e = s(x, y)}
  edgeSet := f.Dom
  IsLink e x y := f e = s(x, y)
  edge_mem_iff_exists_isLink e := by
    simp +contextual only [PFun.mem_dom, Part.coe_some, iff_def, forall_exists_index,
      Part.mem_some_iff, exists_eq, implies_true, and_true]
    rintro s hs
    induction s with | h u v => use u, v, Part.eq_some_iff.mpr hs
  isLink_symm e he := ⟨fun x y hxy ↦ by
    simp only [Part.coe_some] at hxy ⊢
    rw [hxy, Part.some_inj, Sym2.eq_swap]⟩
  eq_or_eq_of_isLink_of_isLink e a b c d hab hcd := by
    have : a = c ∧ b = d ∨ a = d ∧ b = c := by simpa using hab.symm.trans hcd
    tauto
  left_mem_of_isLink e x y he := by use y, e

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
@[simps (attr := grind =)]
def map {α' : Type*} (f : α → α') (G : Graph α β) : Graph α' β where
  vertexSet := f '' V(G)
  edgeSet := E(G)
  IsLink e x' y' := ∃ x y, G.IsLink e x y ∧ x' = f x ∧ y' = f y
  isLink_symm e he := ⟨by
    rintro - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
      exact ⟨_, _, _, _, hxy, rfl, rfl⟩
    rintro ⟨-, -, x, y, h, rfl, rfl⟩
    exact h.edge_mem
  left_mem_of_isLink := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.left_mem

scoped infix:51 " ''ᴳ " => map

variable {α' α'' : Type*} {f g : α → α'} {f' g' : α' → α} {x y z : α'} {G' H' : Graph α' β}
  {w : WList α β}

/-- `Map` has the expected incidence predicate. -/
@[simp]
lemma map_inc : (f ''ᴳ G).Inc e x ↔ ∃ v, G.Inc e v ∧ x = f v := by
  simp only [Inc, map_isLink]
  tauto

@[simp]
lemma vertexSet_map_subset (h : X ⊆ V(G)) : f '' X ⊆ V(f ''ᴳ G) := by
  rw [vertexSet_map]
  gcongr

lemma IsLink.map (h : G.IsLink e u v) (f : α → α') : (f ''ᴳ G).IsLink e (f u) (f v) := by
  simp only [map_isLink]
  use u, v, h

@[simp]
lemma map_isLoopAt : (f ''ᴳ G).IsLoopAt e x ↔ ∃ u v, G.IsLink e u v ∧ x = f u ∧ x = f v := Iff.rfl

@[gcongr only]
lemma map_congr_left_of_eqOn (h : EqOn f g V(G)) : (f ''ᴳ G) = (g ''ᴳ G) := by
  apply Graph.ext ?_ fun e x y ↦ ?_
  · rw [vertexSet_map, vertexSet_map]
    exact image_congr h
  · simp_rw [map_isLink]
    refine ⟨fun ⟨v, w, hvw, _, _⟩ ↦ ?_, fun ⟨v, w, hvw, _, _⟩ ↦ ?_⟩ <;> subst x y
    · use v, w, hvw, h hvw.left_mem, h hvw.right_mem
    · use v, w, hvw, (h hvw.left_mem).symm, (h hvw.right_mem).symm

@[simp]
lemma map_id : (id ''ᴳ G) = G := by
  ext a b c <;> simp

@[simp]
lemma map_map {α'' : Type*} {f : α' → α''} : (f ''ᴳ (g ''ᴳ G)) = (f ∘ g) ''ᴳ G := by
  ext a b c <;> simp

/-- To prove that `H` is an image of `G`, it suffices to show some set containments,
and mapping links in one direction. -/
lemma eq_map_of_forall_isLink {H : Graph α' β} {φ : α → α'} (hf : InjOn φ V(G))
    (hV : φ '' V(G) = V(H)) (hE : E(H) ⊆ E(G))
    (h : ∀ e x y, G.IsLink e x y → H.IsLink e (φ x) (φ y)) : φ ''ᴳ G = H := by
  refine Graph.ext hV fun e x y ↦ ⟨fun ⟨x', y', hxy, hx', hy'⟩ ↦ ?_, fun h' ↦ ?_⟩
  · rw [hx', hy']
    exact h _ _ _ hxy
  obtain ⟨x, hx, rfl⟩ := hV.superset h'.left_mem
  obtain ⟨y, hy, rfl⟩ := hV.superset h'.right_mem
  obtain ⟨x', y', hxy'⟩ := G.exists_isLink_of_mem_edgeSet <| hE h'.edge_mem
  specialize h _ _ _ hxy'
  obtain ⟨hxeq, hyeq⟩ | ⟨hxeq, hyeq⟩ := h'.eq_and_eq_or_eq_and_eq h
  · obtain rfl : x = x' := hf hx hxy'.left_mem hxeq
    obtain rfl : y = y' := hf hy hxy'.right_mem hyeq
    exact hxy'.map φ
  obtain rfl : x = y' := hf hx hxy'.right_mem hxeq
  obtain rfl : y = x' := hf hy hxy'.left_mem hyeq
  exact hxy'.symm.map φ

lemma Compatible.map (h : G.Compatible H) : (f ''ᴳ G).Compatible (f ''ᴳ H) := by
  grind [Compatible, h.isLink_eq]

lemma map_union (G H : Graph α β) (f : α → α') : f ''ᴳ (G ∪ H) = (f ''ᴳ G) ∪ (f ''ᴳ H) :=
  Graph.ext (by grind) <| by grind only [= map_isLink, = union_isLink_iff, = edgeSet_map]

@[gcongr]
lemma map_mono (h : G ≤ H) : f ''ᴳ G ≤ f ''ᴳ H where
  vertexSet_mono v := by
    simp only [vertexSet_map, mem_image, forall_exists_index, and_imp]
    rintro u hu rfl
    use u, vertexSet_mono h hu
  isLink_mono e x y := by
    simp only [map_isLink, forall_exists_index, and_imp]
    rintro a b hab rfl rfl
    use a, b, hab.of_le h

@[simp]
lemma map_eq_bot_iff (G : Graph α β) (φ : α → α') : φ ''ᴳ G = ⊥ ↔ G = ⊥ := by
  rw [← vertexSet_eq_empty_iff, vertexSet_map, image_eq_empty, vertexSet_eq_empty_iff]

@[simp]
lemma map_noEdge (V : Set α) (β : Type*) (φ : α → α') : (noEdge V β).map φ = noEdge (φ '' V) β := by
  ext <;> simp

@[gcongr]
lemma map_isSpanningSubgraph (hsle : G ≤s H) : f ''ᴳ G ≤s f ''ᴳ H where
  vertexSet_eq := by simp [hsle.vertexSet_eq]
  vertexSet_mono := by simp [hsle.vertexSet_eq]
  isLink_mono := (map_mono hsle.le).isLink_mono

lemma map_restrict_comm : f ''ᴳ (G ↾ F) = (f ''ᴳ G) ↾ F := by
  ext a b c
  · simp
  simp only [map_isLink, restrict_isLink]
  tauto

lemma map_deleteEdges_comm : f ''ᴳ (G ＼ F) = (f ''ᴳ G) ＼ F := by
  ext a b c
  · simp
  simp only [map_isLink, deleteEdges_isLink]
  tauto

variable {x y : α}

lemma Adj.map (hG : G.Adj x y) (φ : α → α') : (G.map φ).Adj (φ x) (φ y) := by
  obtain ⟨e, he⟩ := hG
  exact ⟨e, he.map φ⟩

lemma map_adj_iff {φ : α → α'} {x y : α'} :
    (G.map φ).Adj x y ↔ ∃ x₀ y₀, G.Adj x₀ y₀ ∧ φ x₀ = x ∧ φ y₀ = y := by
  constructor
  · rintro ⟨e, ⟨x₀, y₀, he, rfl, rfl⟩⟩
    exact ⟨_, _, he.adj, rfl, rfl⟩
  rintro ⟨x₀, y₀, ⟨e, he⟩, rfl, rfl⟩
  exact ⟨e, he.map φ⟩

lemma map_adj_iff_of_injective {φ : α → α'} {x y : α} (hφ : φ.Injective) :
    (G.map φ).Adj (φ x) (φ y) ↔ G.Adj x y :=
  ⟨fun ⟨e, he⟩ ↦ ⟨e, by simpa [hφ.eq_iff] using he⟩, fun h ↦ h.map φ⟩

lemma map_adj_iff_of_injOn {φ : α → α'} {x y : α} (hφ : InjOn φ V(G))
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) : (G.map φ).Adj (φ x) (φ y) ↔ G.Adj x y := by
  refine ⟨fun ⟨e, he⟩ ↦ ⟨e, ?_⟩, fun h ↦ h.map φ⟩
  obtain ⟨x', y', h, hx', hy'⟩ := he
  rw [hφ.eq_iff hx h.left_mem] at hx'
  rw [hφ.eq_iff hy h.right_mem] at hy'
  rwa [hx', hy']

lemma IsComplete.map (hG : G.IsComplete) {α' : Type*} (φ : α → α') : (G.map φ).IsComplete := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  exact (hG x hx y hy (by grind)).map φ

lemma isComplete_map_iff {φ : α → α'} (hφ : InjOn φ V(G)) :
    (G.map φ).IsComplete ↔ G.IsComplete := by
  refine ⟨fun h x hx y hy hxy ↦ ?_, fun h ↦ h.map φ⟩
  specialize h _ (mem_image_of_mem φ hx) _ (mem_image_of_mem φ hy) (by rwa [Ne, hφ.eq_iff hx hy])
  rwa [map_adj_iff_of_injOn hφ hx hy] at h

@[simp]
lemma IsWalk.map (f : α → α') (hw : G.IsWalk w) : (f ''ᴳ G).IsWalk (w.map f) := by
  refine hw.recOn ?hnil ?hcons
  · intro x hx
    have hx' : f x ∈ V(f ''ᴳ G) := by
      simpa [vertexSet_map] using Set.mem_image_of_mem f hx
    simpa [map] using IsWalk.nil hx'
  · intro x e w hw hlink ih
    have hlink' : (f ''ᴳ G).IsLink e (f x) (w.map f).first := by
      simpa [map_first] using hlink.map f
    simpa [map, map_first] using ih.cons hlink'

lemma IsWalk.map_invFunOn [Nonempty α] (hf : InjOn f V(G)) {w : WList α' β}
    (hw : (f ''ᴳ G).IsWalk w) : G.IsWalk (w.map (invFunOn f V(G))) := by
  induction hw with
  | nil hx => simpa [nil_isWalk_iff] using invFunOn_mem hx
  | cons hw he ih =>
    simp only [WList.map_cons, cons_isWalk_iff, WList.map_first]
    obtain ⟨a, b, hab, rfl, hfb⟩ := by simpa only [map_isLink] using he
    grind [hf.leftInvOn_invFunOn hab.left_mem, hf.leftInvOn_invFunOn hab.right_mem]

lemma IsWalk.map_invFunOn_map [Nonempty α] {w : WList α' β}
    (hw : (f ''ᴳ G).IsWalk w) : (w.map (invFunOn f V(G))).map f = w :=
  WList.map_invFunOn_map (by simpa using hw.vertexSet_subset)

@[simp]
lemma IsTrail.map (f : α → α') (hw : G.IsTrail w) : (f ''ᴳ G).IsTrail (w.map f) where
  isWalk := hw.isWalk.map f
  edge_nodup := by simpa using hw.edge_nodup

@[simp]
lemma IsTour.map (f : α → α') (hw : G.IsTour w) : (f ''ᴳ G).IsTour (w.map f) where
  toIsTrail := hw.isTrail.map f
  nonempty := by simpa using hw.nonempty
  isClosed := by
    simp only [IsClosed, map_first, map_last]
    rw [hw.isClosed]

@[simp]
lemma IsPath.map (hf : InjOn f V(w)) (hw : G.IsPath w) : (f ''ᴳ G).IsPath (w.map f) where
  isWalk := hw.isWalk.map f
  nodup := by
    rw [map_vertex]
    exact (List.nodup_map_iff_inj_on hw.nodup).mpr hf

@[simp]
lemma IsCyclicWalk.map (hf : InjOn f V(w)) (hw : G.IsCyclicWalk w) :
    (f ''ᴳ G).IsCyclicWalk (w.map f) where
  toIsTour := hw.isTour.map f
  nodup := by
    match w with
    | .nil u => simp
    | .cons u e w =>
    simp only [map_cons, tail_cons, map_vertex]
    refine (List.nodup_map_iff_inj_on hw.nodup).mpr ?_
    grind [InjOn]

lemma IsCyclicWalk.exists_of_map_of_injOn {φ : α → α'} (hφ : InjOn φ V(H)) {C : WList α' β}
    (hC : (φ ''ᴳ H).IsCyclicWalk C) : ∃ C₀, H.IsCyclicWalk C₀ ∧ C₀.map φ = C := by
  have : Nonempty α := ⟨hC.isWalk.vertex_mem_of_mem first_mem |>.choose⟩
  refine ⟨C.map (invFunOn φ V(H)), ⟨⟨⟨by simpa using hC.isWalk.map_invFunOn hφ, by
    simpa [WList.map_edge] using hC.edge_nodup⟩, by simpa using hC.nonempty, by
    simpa [WList.IsClosed] using congrArg _ hC.isClosed⟩, ?_⟩, by
    simpa using hC.isWalk.map_invFunOn_map⟩
  cases C with
  | nil y => simp at hC
  | cons y e W =>
    simp only [map_cons, tail_cons, map_vertex]
    exact (List.nodup_map_iff_inj_on hC.nodup).mpr fun a ha b hb hab ↦
      invFunOn_injOn_image φ V(H) |>.mono hC.isWalk.vertexSet_subset (by simp_all) (by simp_all) hab

lemma induce_map_isSpanningSubgraph : f ''ᴳ (G[X]) ≤s (f ''ᴳ G)[f '' X] where
  vertexSet_eq := by simp
  isLink_mono e x y := by
    simp only [map_isLink, induce_isLink, mem_image, forall_exists_index, and_imp]
    grind

lemma map_deleteVerts_isInducedSubgraph : (f ''ᴳ G) - (f '' X) ≤i f ''ᴳ (G - X) where
  le := by
    constructor
    · grind [vertexSet_map]
    simp only [deleteVerts_isLink_iff, map_isLink, mem_image, not_exists, not_and, and_imp,
      forall_exists_index]
    grind
  isLink_of_mem_mem e x y := by
    simp only [map_isLink, deleteVerts_isLink_iff, vertexSet_deleteVerts, vertexSet_map, mem_sdiff,
      mem_image, not_exists, not_and, and_imp, forall_exists_index]
    grind

@[simp]
lemma map_deleteVerts_preimage {X : Set α'} : f ''ᴳ (G - (f ⁻¹' X)) = (f ''ᴳ G) - X := by
  ext a b c
  · simp only [vertexSet_map, vertexSet_deleteVerts, mem_image, mem_sdiff, mem_preimage]
    grind
  · simp only [map_isLink, deleteVerts_isLink_iff, mem_preimage, ← exists_and_right, and_assoc]
    grind

lemma map_deleteVerts_of_injOn {X : Set α} (hf : InjOn f V(G)) (hX : X ⊆ V(G)) :
    f ''ᴳ (G - X) = (f ''ᴳ G) - (f '' X) := by
  nth_rw 1 [← hf.preimage_image_inter hX, inter_comm, deleteVerts_vertexSet_inter,
    map_deleteVerts_preimage]

lemma map_deleteVerts_of_injective {X : Set α} (hf : Injective f) :
    f ''ᴳ (G - X) = (f ''ᴳ G) - (f '' X) := by
  nth_rw 1 [← deleteVerts_vertexSet_inter, map_deleteVerts_of_injOn hf.injOn inter_subset_left,
    image_inter hf, ← vertexSet_map, deleteVerts_vertexSet_inter]

@[simp]
lemma induce_preimage_map {X : Set α'} (h : X ⊆ f '' V(H)) : f ''ᴳ (H[f ⁻¹' X]) = (f ''ᴳ H)[X] := by
  refine Graph.ext (by grind) ?_
  grind only [→ IsLink.right_mem, = map_isLink, = induce_isLink, = edgeSet_induce_eq_diff,
    = mem_preimage]

lemma surjOn_of_le_map {G} (h : G ≤ f ''ᴳ H) : SurjOn f V(H) V(G) := by
  intro a' ha'
  exact vertexSet_mono h ha'

lemma exists_map_eq_of_le_map {G} (h : G ≤ f ''ᴳ H) : ∃ H' ≤ H, f ''ᴳ H' = G := by
  use H[V(H) ∩ f ⁻¹' V(G)] ↾ E(G), .trans restrict_le <| induce_le inter_subset_left, ?_
  refine ext_of_le_le ?_ h ?_ ?_
  · gcongr
    exact .trans restrict_le <| induce_le inter_subset_left
  · ext x
    simp only [vertexSet_map, vertexSet_restrict, vertexSet_induce, mem_image, mem_inter_iff,
      mem_preimage]
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, ⟨hyH, hy⟩, rfl⟩
      exact hy
    obtain ⟨y, hy, rfl⟩ := by simpa only [vertexSet_map, mem_image] using vertexSet_mono h hx
    use y
  simp only [edgeSet_map, edgeSet_restrict, inter_eq_right, edgeSet_induce, mem_inter_iff,
    mem_preimage]
  intro e he
  obtain ⟨x', y', hxy'⟩ := exists_isLink_of_mem_edgeSet <| edgeSet_mono h he
  obtain ⟨x, y, hxy, rfl, rfl⟩ := by simpa only [map_isLink] using hxy'
  have hxy'' := hxy'.of_le_of_mem h he
  use x, y, hxy, ⟨hxy.left_mem, hxy''.left_mem⟩, hxy.right_mem, hxy''.right_mem

lemma exists_le_map_comm {G} (f : α → α') : G ≤ f ''ᴳ H ↔ ∃ H', H' ≤ H ∧ f ''ᴳ H' = G := by
  refine ⟨fun hf ↦ exists_map_eq_of_le_map hf, ?_⟩
  rintro ⟨H', hH', rfl⟩
  grw [hH']

/-! ### IsContractClosed predicate

Similar to how combining injecitivity and surjectivity gives a bijection,
`IsContractClosed` is one half of predicate that ensures that `contract` is sound.

`IsContractClosed G φ C` means that `φ` identifies the endpoints of every edge in `C`. So each fiber
of `φ` is a closed subgraph of `G ↾ C`.

Notice that each fiber may not be the components of `G ↾ C`. However, it is sometime useful to
use this half-predicate in proofs since it is well-behaved under subgraphs and subsets of `C`.
-/
def IsContractClosed (G : Graph α β) (φ : α → α') (C : Set β) : Prop :=
  ∀ ⦃e u v⦄, e ∈ C → G.IsLink e u v → φ u = φ v

namespace IsContractClosed

variable {α' : Type*} {φ : α → α'} {C D : Set β}

lemma subset (hφ : G.IsContractClosed φ C) (hDC : D ⊆ C) : G.IsContractClosed φ D := by
  intro e u v heD
  exact hφ (hDC heD)

lemma of_le (hGH : G ≤ H) (hφ : H.IsContractClosed φ C) : G.IsContractClosed φ C := by
  intro e u v heC huv
  exact hφ heC (hGH.isLink_mono huv)

lemma isLoopAt_map_of_mem (hφ : G.IsContractClosed φ C) (heC : e ∈ C) (huv : G.IsLink e u v) :
    (φ ''ᴳ G).IsLoopAt e (φ u) := by
  -- build a self-link in the mapped graph, then use `isLink_self_iff`.
  refine ⟨u, v, huv, rfl, ?_⟩
  simpa using hφ heC huv

/-- Under `IsContractClosed`, every edge in `C` becomes a loop after mapping. -/
lemma exists_isLoopAt_map_of_mem_edgeSet (hφ : G.IsContractClosed φ C) (he : e ∈ C ∩ E(G)) :
    ∃ x, (φ ''ᴳ G).IsLoopAt e x := by
  obtain ⟨heC, heG⟩ := he
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet heG
  exact ⟨φ u, hφ.isLoopAt_map_of_mem heC huv⟩

/-- A vertex-deletion-stable version: if `e ∈ C` and `e` survives deleting `S` from the mapped
graph, then `e` is a loop in `((φ ''ᴳ G) - S)`. -/
lemma exists_isLoopAt_map_deleteVerts_of_mem (hφ : G.IsContractClosed φ C) (S : Set α')
    (he : e ∈ C ∩ E((φ ''ᴳ G) - S)) : ∃ x, ((φ ''ᴳ G) - S).IsLoopAt e x := by
  obtain ⟨heC, heE⟩ := he
  have heG : e ∈ E(G) := by simpa only [edgeSet_map] using (edgeSet_mono deleteVerts_le) heE
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet heG
  have hloop : (φ ''ᴳ G).IsLoopAt e (φ u) := hφ.isLoopAt_map_of_mem heC huv
  have huS : (φ u) ∉ S := by
    intro huS
    exact (hloop.inc.not_mem_of_mem huS) heE
  refine ⟨φ u, ((φ ''ᴳ G).deleteVerts_isLink_iff S).mpr ⟨hloop, huS, huS⟩⟩

lemma disjoint_of_isWalk_noLoop (hφ : G.IsContractClosed φ C) {W : WList α' β}
    (h : (φ ''ᴳ G).IsWalk W) (hloop : W.NoLoop) : Disjoint E(W) C := by
  rw [disjoint_iff_forall_notMem]
  rintro e heW heC
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet <| h.edge_mem_of_mem heW
  have hl := hφ.isLoopAt_map_of_mem heC hxy
  rw [IsLoopAt, ← h.isLink_iff_isLink_of_mem heW] at hl
  exact hloop.not_isLink e (φ x) hl

lemma exists_isLoopAt_of_isWalk (hφ : G.IsContractClosed φ C) (hw : G.IsWalk W) :
    ∀ e ∈ (W.map φ).edge, e ∈ C → ∃ x, (φ ''ᴳ G).IsLoopAt e x := by
  rintro e heW heC
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet <| hw.edge_mem_of_mem (by simpa using heW)
  exact ⟨φ x, hφ.isLoopAt_map_of_mem heC hxy⟩

end IsContractClosed



@[simps (attr := grind =)]
noncomputable def edgePreimg {β' : Type*} (G : Graph α β) (σ : β' → β) : Graph α β' where
  vertexSet := V(G)
  edgeSet := σ ⁻¹' E(G)
  IsLink e x y := ∃ e', σ e = e' ∧ G.IsLink e' x y
  isLink_symm e he := ⟨by
    rintro a b ⟨-, rfl, hbtw'⟩
    exact ⟨σ e, rfl, hbtw'.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e a b c d ⟨-, rfl, hbtw₁⟩ ⟨-, rfl, hbtw₂⟩
    exact G.eq_or_eq_of_isLink_of_isLink hbtw₁ hbtw₂
  edge_mem_iff_exists_isLink e := by
    simp [G.edge_mem_iff_exists_isLink]
  left_mem_of_isLink := by
    rintro e a b ⟨-, rfl, hbtw⟩
    exact G.left_mem_of_isLink hbtw

variable {β' : Type*} {e' : β'} {σ : β' → β}

@[simp]
lemma edgePreimg_inc : (G.edgePreimg σ).Inc e' u ↔ ∃ e, σ e' = e ∧ G.Inc e u := by
  simp [Inc]

variable {β' : Type*} {σ : β → β'} {e' : β'}

/-- A tactic for providing the proof required in `edgeMap` in the case where the function
is known to be injective on the edge set. -/
syntax "edgeMap_tac" : tactic

macro_rules
  | `(tactic| edgeMap_tac) =>
    `(tactic| simp +contextual)

macro_rules
  | `(tactic| edgeMap_tac) =>
    `(tactic| simp +contextual [Injective.eq_iff (by assumption)])

macro_rules
  | `(tactic| edgeMap_tac) =>
    `(tactic| simp +contextual [InjOn.eq_iff (by assumption)])

-- @[simps (attr := grind =)]
/-- The assumption `hσ` is needed for an edge-map to be well-defined without choice.
It holds in particular if `InjOn σ E(G)`, and the `autoParam` will prove it if this is known.
`simps` doesn't play nice with the `autoParam`, so the simp lemms are proved manually. -/
def edgeMap (G : Graph α β) (σ : β → β')
    (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂ := by edgeMap_tac) :
    Graph α β' where
  vertexSet := V(G)
  edgeSet := σ '' E(G)
  IsLink e x y := ∃ e', σ e' = e ∧ G.IsLink e' x y
  isLink_symm e he := ⟨by
    rintro x y ⟨f, rfl, hbtw⟩
    exact ⟨f, rfl, hbtw.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e a b c d ⟨f, rfl, hbtw₁⟩ ⟨g, hfeqg, hbtw₂⟩
    exact G.eq_or_eq_of_isLink_of_isLink hbtw₁ <|
      (hσ g hbtw₂.edge_mem f hbtw₁.edge_mem hfeqg) ▸ hbtw₂
  edge_mem_iff_exists_isLink := by
    simp only [mem_image, G.edge_mem_iff_exists_isLink]
    tauto
  left_mem_of_isLink := by
    rintro e a b ⟨f, rfl, hbtw⟩
    exact G.left_mem_of_isLink hbtw

@[simp, grind =]
lemma edgeMap_isLink {e x y} {σ : β → β'} {hσ} :
    (G.edgeMap σ hσ).IsLink e x y ↔ ∃ e', σ e' = e ∧ G.IsLink e' x y := Iff.rfl

@[simp, grind =]
lemma vertexSet_edgeMap (G : Graph α β) (σ : β → β') {hσ} : V(G.edgeMap σ hσ) = V(G) := rfl

@[simp, grind =]
lemma edgeSet_edgeMap (G : Graph α β) (σ : β → β') {hσ} : E(G.edgeMap σ hσ) = σ '' E(G) := rfl

@[simp]
lemma edgeMap_inc (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂) :
    (G.edgeMap σ hσ).Inc e' u ↔ ∃ e, σ e = e' ∧ G.Inc e u := by
  simp only [Inc, edgeMap_isLink]
  tauto

@[simp]
lemma edgeMap_isLoopAt {e x hσ} :
    (G.edgeMap σ hσ).IsLoopAt e x ↔ ∃ f, σ f = e ∧ G.IsLoopAt f x := by
  simp_rw [IsLoopAt, edgeMap_isLink]

@[simp]
lemma edgeMap_isNonloopAt {e x hσ} :
    (G.edgeMap σ hσ).IsNonloopAt e x ↔ ∃ f, σ f = e ∧ G.IsNonloopAt f x := by
  simp_rw [IsNonloopAt, edgeMap_isLink]
  grind

@[simp]
lemma edgeMap_noEdge (V : Set α) {β β' : Type*} {σ : β → β'} {hσ} :
    ((noEdge V β ).edgeMap σ hσ) = noEdge V β' := by
  ext <;> simp

lemma IsLink.edgeMap (h : G.IsLink e x y) (φ : β → β') (hφ) : (G.edgeMap φ hφ).IsLink (φ e) x y :=
  ⟨e, rfl, h⟩

@[simp]
lemma edgeMap_adj_iff {φ : β → β'} {hφ} : (G.edgeMap φ hφ).Adj x y ↔ G.Adj x y := by
  simp [Adj]

lemma edgeMap_adj_eq {φ : β → β'} {hφ} : (G.edgeMap φ hφ).Adj = G.Adj := by
  simp [funext_iff]

@[simp]
lemma isComplete_edgeMap_iff {φ : β → β'} {hφ} : (G.edgeMap φ hφ).IsComplete ↔ G.IsComplete := by
  simp [IsComplete]

@[simp]
lemma edgeMap_eq_bot_iff {φ : β → β'} {hφ} : G.edgeMap φ hφ = ⊥ ↔ G = ⊥ := by
  rw [← vertexSet_eq_empty_iff, ← vertexSet_eq_empty_iff, vertexSet_edgeMap]

@[simp]
lemma edgeMap_deleteVerts (G : Graph α β) {φ : β → β'} (hφ) (X : Set α) : (G - X).edgeMap φ
    (fun e₁ he₁ e₂ he₂ he ↦ by simp [funext_iff, hφ _ (edgeSet_mono deleteVerts_le he₁) _
      (edgeSet_mono deleteVerts_le he₂) he]) = (G.edgeMap φ hφ) - X :=
  Graph.ext (by simp) <| by grind only [→ IsLink.right_mem, → IsLink.left_mem, = edgeMap_isLink,
    = deleteVerts_isLink]


@[simp]
lemma IsWalk.edgeMap (hw : G.IsWalk w) (σ : β → β') (hσ) :
    (G.edgeMap σ hσ).IsWalk (w.edgeMap σ) := by
  induction hw with
  | nil => simpa
  | cons hw h ih => exact edgeMap_cons .. ▸ ih.cons (by simpa using h.edgeMap σ hσ)

lemma IsWalk.edgeMap_invFunOn [Nonempty β] {w hσ} (hw : (G.edgeMap σ hσ).IsWalk w)
    (hinj : InjOn σ E(G)) : G.IsWalk (w.edgeMap (invFunOn σ E(G))) := by
  induction hw with
  | @nil x hx => simpa using hx
  | @cons x e w hw h ih =>
    obtain ⟨e, rfl, h⟩ := h
    simpa [hinj.leftInvOn_invFunOn h.edge_mem, h]

lemma IsWalk.edgeMap_invFunOn_edgeMap [Nonempty β] {w} {hσ} (hw : (G.edgeMap σ hσ).IsWalk w)
    (hinj : InjOn σ E(G)) : (w.edgeMap (invFunOn σ E(G))).edgeMap σ = w := by
  induction hw with
  | nil => simp
  | @cons x e w hw h ih =>
    obtain ⟨e, rfl, h⟩ := h
    simpa [hinj.leftInvOn_invFunOn h.edge_mem]

@[simp]
lemma IsTrail.edgeMap (hw : G.IsTrail w) (σ : β → β') (hσ : InjOn σ E(G)) :
    (G.edgeMap σ).IsTrail (w.edgeMap σ) where
  isWalk := hw.isWalk.edgeMap σ _
  edge_nodup := by
    rw [edgeMap_edge, List.nodup_map_iff_inj_on]
    · intro x hx y hy hxy
      rwa [← hσ.eq_iff (hw.edgeSet_subset hx) (hw.edgeSet_subset hy)]
    exact hw.edge_nodup

@[simp]
lemma IsTour.edgeMap (hw : G.IsTour w) (σ : β → β') (hσ : InjOn σ E(G)) :
    (G.edgeMap σ).IsTour (w.edgeMap σ) where
  toIsTrail := hw.isTrail.edgeMap σ hσ
  nonempty := by simpa using hw.nonempty
  isClosed := by simpa [IsClosed] using hw.isClosed

@[simp]
lemma IsPath.edgeMap (hw : G.IsPath w) (σ : β → β') (hσ : InjOn σ E(G)) :
    (G.edgeMap σ).IsPath (w.edgeMap σ) where
  isWalk := hw.isWalk.edgeMap σ _
  nodup := by simpa using hw.nodup

@[simp]
lemma IsCyclicWalk.edgeMap (hw : G.IsCyclicWalk w) (σ : β → β') (hσ : InjOn σ E(G)) :
    (G.edgeMap σ).IsCyclicWalk (w.edgeMap σ) where
  toIsTour := hw.isTour.edgeMap σ hσ
  nodup := by
    rw [edgeMap_tail, edgeMap_vertex]
    exact hw.nodup

lemma IsCyclicWalk.exists_of_edgeMap_of_injOn {σ : β → β'} (hσ : InjOn σ E(G)) {C}
    (hC : (G.edgeMap σ).IsCyclicWalk C) : ∃ C₀, G.IsCyclicWalk C₀ ∧ C₀.edgeMap σ = C := by
  obtain hβ | hβ := isEmpty_or_nonempty β
  · obtain ⟨e, heC⟩ := hC.nonempty.exists_edge
    simpa using hC.edgeSet_subset heC
  use WList.edgeMap (invFunOn σ E(G)) C
  simp only [isCyclicWalk_iff, isTour_iff, isTrail_iff, hC.isWalk.edgeMap_invFunOn hσ, edgeMap_edge,
    true_and, edgeMap_nonempty, hC.nonempty, IsClosed, edgeMap_first, hC.isClosed.eq, edgeMap_last,
    and_self, and_true, Nonempty.vertex_tail, edgeMap_vertex, hC.isWalk.edgeMap_invFunOn_edgeMap hσ]
  rw [← hC.nonempty.vertex_tail, List.nodup_map_iff_inj_on hC.edge_nodup, and_iff_left hC.nodup]
  refine fun x hx y hy hxy ↦ ?_
  rwa [(invFunOn_injOn_image _ _).eq_iff] at hxy
  · simpa using hC.edgeSet_subset hx
  simpa using hC.edgeSet_subset hy

lemma eq_edgeMap_of_forall_isLink {β' : Type*} {H : Graph α β'} {φ : β → β'} (hφ : InjOn φ E(G))
    (hH : V(G) = V(H)) (hss : E(H) ⊆ φ '' (E(G)))
    (h : ∀ e x y, G.IsLink e x y → H.IsLink (φ e) x y) : H = G.edgeMap φ
      (fun e he f hf hef ↦ by simp [hφ he hf hef]) := by
  refine Graph.ext (by simp [hH]) fun e x y ↦ ⟨fun h' ↦ ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := hss h'.edge_mem
    obtain ⟨x', y', hxy'⟩ := exists_isLink_of_mem_edgeSet he
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (h _ _ _ hxy').eq_and_eq_or_eq_and_eq h'
    · exact ⟨e, rfl, hxy'⟩
    exact ⟨e, rfl, hxy'.symm⟩
  rintro ⟨e, rfl, he⟩
  exact h e x y he

lemma eq_edgeMap_of_forall_isLink' {β' : Type*} {H : Graph α β'} {φ : β → β'} (hφ : InjOn φ E(G))
    (hV : V(G) = V(H))
    (hH : ∀ ⦃e x y⦄, H.IsLink e x y → ∃ e', G.IsLink e' x y ∧ φ e' = e)
    (hG : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink (φ e) x y) : H = G.edgeMap φ
      (fun e he f hf hef ↦ by simp [hφ he hf hef]) := by
  refine Graph.ext (by simp [hV]) fun e x y ↦ ⟨fun h' ↦ ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := hH h'
    exact he.edgeMap ..
  rintro ⟨e, rfl, he⟩
  exact hG he

/-- If `φ` and `ψ` are functions out of the vertex and edge sets respectively,
a sufficient condition for a graph `H` to be a map of `G` by `φ` and `ψ`.
This will only apply if `φ` and `ψ` give an isomorphism from `G` to `H`. -/
lemma eq_map_edgeMap_of_forall {α' β' : Type*} {φ : α → α'} {ψ : β → β'} {H : Graph α' β'}
    (hψ : InjOn ψ E(G)) (hV : V(H) = φ '' V(G))
    (hG : ∀ ⦃e x y⦄, G.IsLink e x y → H.IsLink (ψ e) (φ x) (φ y))
    (hH : ∀ ⦃e x y⦄, H.IsLink e x y → ∃ e' x' y', G.IsLink e' x' y' ∧ ψ e' = e) :
    H = (φ ''ᴳ G).edgeMap ψ (fun e he f hf hef ↦ by simp [hψ he hf hef]) := by
  refine eq_edgeMap_of_forall_isLink' (by simpa) hV.symm (fun e' x' y' he' ↦ ?_) ?_
  · obtain ⟨e', x'', y'', he'', rfl⟩ := hH he'
    obtain ⟨rfl , rfl⟩ | ⟨rfl, rfl⟩ := (hG he'' ).eq_and_eq_or_eq_and_eq he'
    · exact ⟨_, he''.map φ, rfl⟩
    exact ⟨_, he''.symm.map φ, rfl⟩
  rintro e _ _ ⟨x, y, hxy, rfl, rfl⟩
  exact hG hxy

/-- If `φ` and `ψ` are functions out of the vertex and edge sets respectively,
a sufficient condition for a graph `H` to be a map of `G` by `φ` and `ψ`.
This will only apply if `φ` and `ψ` give an isomorphism from `G` to `H`. -/
lemma eq_map_edgeMap_of_forall_inc {α' β' : Type*} {φ : α → α'} {ψ : β → β'} {H : Graph α' β'}
    (hψ : InjOn ψ E(G)) (hV : V(H) = φ '' V(G)) (hG : ∀ ⦃e x⦄, G.Inc e x → H.Inc (ψ e) (φ x))
    (hH : ∀ ⦃e x⦄, H.Inc e x → ∃ e' x', G.Inc e' x' ∧ φ x' = x ∧ ψ e' = e) :
    H = (φ ''ᴳ G).edgeMap ψ (fun e he f hf hef ↦ by simp [hψ he hf hef]) := by
  refine eq_map_edgeMap_of_forall hψ hV (fun e x y he ↦ ?_) fun e x y he ↦ ?_
  · obtain ⟨x', hx'⟩ := hG he.inc_left
    obtain hxy | rfl := (hG he.inc_right).eq_or_eq_of_isLink hx'
    · obtain ⟨e', x'', he', rfl, hee'⟩ := hH hx'.inc_right
      obtain rfl : e' = e := hψ he'.edge_mem he.edge_mem hee'
      obtain rfl | rfl := he'.eq_or_eq_of_isLink he
      · rwa [hxy]
      assumption
    exact hx'
  obtain ⟨e', x', ⟨z, hz⟩, rfl, rfl⟩ := hH he.inc_left
  exact ⟨_, _, _, hz, rfl⟩

lemma setLinkEdges_map_image (G : Graph α β) {S T : Set α} (hS : S ⊆ V(G)) (hT : T ⊆ V(G))
    {α' : Type*} {φ : α → α'} (hφ : InjOn φ V(G)) : E(φ ''ᴳ G, φ '' S, φ '' T) = E(G, S, T) := by
  ext e
  simp only [mem_setLinkEdges_iff, mem_image, map_isLink, exists_exists_and_eq_and]
  refine ⟨fun ⟨a, haS, b, hbT, x, y, he, hax, hby⟩  ↦ ?_, fun ⟨a, haS, b, hbT, he⟩ ↦ by grind⟩
  rw [hφ.eq_iff (hS haS) he.left_mem] at hax
  rw [hφ.eq_iff (hT hbT) he.right_mem] at hby
  exact ⟨a, haS, b, hbT, by rwa [hax, hby]⟩

lemma setLinkEdges_map_image_of_injective (G : Graph α β) (S T : Set α) {α' : Type*} {φ : α → α'}
    (hφ : Injective φ) : E(φ ''ᴳ G, φ '' S, φ '' T) = E(G, S, T) := by
  rw [← setLinkEdges_vertexSet_inter_left, ← setLinkEdges_vertexSet_inter_right,
    vertexSet_map, ← image_inter hφ, ← image_inter hφ, setLinkEdges_map_image _ (by simp) (by simp)
    hφ.injOn, setLinkEdges_vertexSet_inter_left, setLinkEdges_vertexSet_inter_right]

lemma setLinkEdges_map (G : Graph α β) {α' : Type*} {φ : α → α'} {S T : Set α'}
    (hφ : InjOn φ V(G)) : E(φ ''ᴳ G, S, T) = E(G, φ ⁻¹' S, φ ⁻¹' T) := by
  rw [← G.setLinkEdges_vertexSet_inter_left, ← G.setLinkEdges_vertexSet_inter_right,
    ← G.setLinkEdges_map_image inter_subset_left inter_subset_left hφ, image_inter_preimage,
    image_inter_preimage, ← vertexSet_map, setLinkEdges_vertexSet_inter_left,
    setLinkEdges_vertexSet_inter_right]

@[simp]
lemma setLinkEdges_edgeMap (G : Graph α β) (S T : Set α) {β' : Type*} {σ : β → β'} {hσ} :
    E(G.edgeMap σ hσ, S, T) = σ '' E(G, S, T) := by
  ext e
  simp only [mem_setLinkEdges_iff, edgeMap_isLink, mem_image]
  grind

-- @[simps! (attr := grind =) vertexSet edgeSet]
-- def map (G : Graph α β) (f : α → α') (σ : β → β')
--     (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂) : Graph α' β' :=
--   f ''ᴳ G.edgeMap σ hσ

-- variable {G : Graph α β} {f : α → α'} {σ : β → β'}
--   (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂)

-- @[simp]
-- lemma map_isLink : (G.map f σ hσ).IsLink e' x y ↔ ∃ u v e, σ e = e' ∧ x = f u ∧ y = f v ∧
--     G.IsLink e u v := by
--   simp +contextual only [map, Map_isLink, edgeMap_isLink, iff_def, forall_exists_index,
--     and_imp]
--   tauto

-- lemma IsLink.map (hbtw : G.IsLink e u v) : (G.map f σ hσ).IsLink (σ e) (f u) (f v) := by
--   rw [map_isLink]
--   use u, v, e

-- lemma mem_vertexSet_map (hin : u ∈ V(G)) : f u ∈ V(G.map f σ hσ) := by
--   rw [vertexSet_map]
--   exact ⟨u, hin, rfl⟩

-- lemma mem_edgeSet_map (hin : e ∈ E(G)) : σ e ∈ E(G.map f σ hσ) := by
--   rw [edgeSet_map]
--   use e

-- @[simp]
-- lemma map_eq_Map (f : α → α') : G.map f id (by simp_all) = (f ''ᴳ G) := by
--   ext a b c
--   · simp
--   · simp +contextual only [map_isLink, id_eq, exists_eq_left, exists_and_left, Map_isLink,
--     iff_def, forall_exists_index, and_imp]
--     tauto
