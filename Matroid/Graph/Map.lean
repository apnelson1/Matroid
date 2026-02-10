import Matroid.Graph.Subgraph.Delete
import Matroid.Graph.Walk.Basic

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
  isLink_symm e he x y hxy := by
    simp only [Part.coe_some] at hxy ⊢
    rw [hxy, Part.some_inj, Sym2.eq_swap]
  eq_or_eq_of_isLink_of_isLink e a b c d hab hcd := by
    have := by simpa using hab.symm.trans hcd
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
  isLink_symm := by
    rintro e he - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩
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

/-- `Map` has the expected incidence predicate. -/
@[simp]
lemma map_inc : (f ''ᴳ G).Inc e x ↔ ∃ v, G.Inc e v ∧ x = f v := by
  simp only [Inc, map_isLink]
  tauto

@[simp]
lemma map_vertexSet_subset (h : X ⊆ V(G)) : f '' X ⊆ V(f ''ᴳ G) := by
  rw [map_vertexSet]
  gcongr

lemma IsLink.map (h : G.IsLink e u v) (f : α → α') : (f ''ᴳ G).IsLink e (f u) (f v) := by
  simp only [map_isLink]
  use u, v, h

@[simp]
lemma map_isLoopAt : (f ''ᴳ G).IsLoopAt e x ↔ ∃ u v, G.IsLink e u v ∧ x = f u ∧ x = f v := Iff.rfl

@[gcongr]
lemma map_congr_left_of_eqOn (h : EqOn f g V(G)) : (f ''ᴳ G) = (g ''ᴳ G) := by
  apply Graph.ext ?_ fun e x y ↦ ?_
  · rw [map_vertexSet, map_vertexSet]
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

@[gcongr]
lemma map_mono (h : G ≤ H) : f ''ᴳ G ≤ f ''ᴳ H where
  vertex_subset v := by
    simp only [map_vertexSet, mem_image, forall_exists_index, and_imp]
    rintro u hu rfl
    use u, vertexSet_mono h hu
  isLink_of_isLink e x y := by
    simp only [map_isLink, forall_exists_index, and_imp]
    rintro a b hab rfl rfl
    use a, b, hab.of_le h

@[gcongr]
lemma map_isSpanningSubgraph (hsle : G ≤s H) : f ''ᴳ G ≤s f ''ᴳ H where
  vertexSet_eq := by simp [hsle.vertexSet_eq]
  isLink_of_isLink := (map_mono hsle.le).isLink_of_isLink

lemma map_edgeRestrict_comm : f ''ᴳ (G ↾ F) = (f ''ᴳ G) ↾ F := by
  ext a b c
  · simp
  simp only [map_isLink, edgeRestrict_isLink]
  tauto

lemma map_edgeDelete_comm : f ''ᴳ (G ＼ F) = (f ''ᴳ G) ＼ F := by
  ext a b c
  · simp
  simp only [map_isLink, edgeDelete_isLink]
  tauto

@[simp]
lemma IsWalk.map (f : α → α') {w : WList α β} (hw : G.IsWalk w) : (f ''ᴳ G).IsWalk (w.map f) := by
  refine hw.recOn ?hnil ?hcons
  · intro x hx
    have hx' : f x ∈ V(f ''ᴳ G) := by
      simpa [map_vertexSet] using Set.mem_image_of_mem f hx
    simpa [map] using IsWalk.nil hx'
  · intro x e w hw hlink ih
    have hlink' : (f ''ᴳ G).IsLink e (f x) (w.map f).first := by
      simpa [map_first] using hlink.map f
    simpa [map, map_first] using ih.cons hlink'

lemma induce_map_isSpanningSubgraph : f ''ᴳ (G[X]) ≤s (f ''ᴳ G)[f '' X] where
  vertexSet_eq := by simp
  isLink_of_isLink e x y := by
    simp only [map_isLink, induce_isLink, mem_image, forall_exists_index, and_imp]
    grind

lemma map_vertexDelete_isInducedSubgraph : (f ''ᴳ G) - (f '' X) ≤i f ''ᴳ (G - X) where
  le := by
    constructor
    · simp [subset_image_diff]
    simp only [vertexDelete_isLink_iff, map_isLink, mem_image, not_exists, not_and, and_imp,
      forall_exists_index]
    grind
  isLink_of_mem_mem e x y := by
    simp only [map_isLink, vertexDelete_isLink_iff, vertexDelete_vertexSet, map_vertexSet, mem_diff,
      mem_image, not_exists, not_and, and_imp, forall_exists_index]
    grind

@[simp]
lemma map_vertexDelete_preimage {X : Set α'} : f ''ᴳ (G - (f ⁻¹' X)) = (f ''ᴳ G) - X := by
  ext a b c
  · simp only [map_vertexSet, vertexDelete_vertexSet, mem_image, mem_diff, mem_preimage]
    grind
  · simp only [map_isLink, vertexDelete_isLink_iff, mem_preimage, ← exists_and_right, and_assoc]
    grind

lemma surjOn_of_le_map {G} (h : G ≤ f ''ᴳ H) : SurjOn f V(H) V(G) := by
  intro a' ha'
  exact vertexSet_mono h ha'

lemma exists_map_eq_of_le_map {G} (h : G ≤ f ''ᴳ H) : ∃ H' ≤ H, f ''ᴳ H' = G := by
  use H[V(H) ∩ f ⁻¹' V(G)] ↾ E(G), .trans edgeRestrict_le <| induce_le inter_subset_left, ?_
  refine ext_of_le_le ?_ h ?_ ?_
  · gcongr
    exact .trans edgeRestrict_le <| induce_le inter_subset_left
  · ext x
    simp only [map_vertexSet, edgeRestrict_vertexSet, induce_vertexSet, mem_image, mem_inter_iff,
      mem_preimage]
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, ⟨hyH, hy⟩, rfl⟩
      exact hy
    obtain ⟨y, hy, rfl⟩ := by simpa using vertexSet_mono h hx
    use y
  simp only [map_edgeSet, edgeRestrict_edgeSet, inter_eq_right, induce_edgeSet, mem_inter_iff,
    mem_preimage]
  intro e he
  obtain ⟨x', y', hxy'⟩ := exists_isLink_of_mem_edgeSet <| edgeSet_mono h he
  obtain ⟨x, y, hxy, rfl, rfl⟩ := by simpa using hxy'
  have hxy'' := hxy'.of_le_of_mem h he
  use x, y, hxy, ⟨hxy.left_mem, hxy''.left_mem⟩, hxy.right_mem, hxy''.right_mem

lemma exists_le_map_comm {G} : (∃ f : α → α', G ≤ f ''ᴳ H) ↔ ∃ f H', H' ≤ H ∧ f ''ᴳ H' = G := by
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f, exists_map_eq_of_le_map hf⟩, ?_⟩
  rintro ⟨f, H', hH', rfl⟩
  use f
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
  exact hφ heC (hGH.isLink_of_isLink huv)

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
lemma exists_isLoopAt_map_vertexDelete_of_mem (hφ : G.IsContractClosed φ C) (S : Set α')
    (he : e ∈ C ∩ E((φ ''ᴳ G) - S)) : ∃ x, ((φ ''ᴳ G) - S).IsLoopAt e x := by
  obtain ⟨heC, heE⟩ := he
  have heG : e ∈ E(G) := by simpa using (edgeSet_mono vertexDelete_le) heE
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet heG
  have hloop : (φ ''ᴳ G).IsLoopAt e (φ u) := hφ.isLoopAt_map_of_mem heC huv
  have huS : (φ u) ∉ S := by
    intro huS
    exact (hloop.inc.not_mem_of_mem huS) heE
  refine ⟨φ u, ((φ ''ᴳ G).vertexDelete_isLink_iff S).mpr ⟨hloop, huS, huS⟩⟩

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
  isLink_symm := by
    rintro e he a b ⟨-, rfl, hbtw'⟩
    exact ⟨σ e, rfl, hbtw'.symm⟩
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

@[simps (attr := grind =)]
def edgeMap (G : Graph α β) (σ : β → β')
    (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂) : Graph α β' where
  vertexSet := V(G)
  edgeSet := σ '' E(G)
  IsLink e x y := ∃ e', σ e' = e ∧ G.IsLink e' x y
  isLink_symm := by
    rintro e he x y ⟨f, rfl, hbtw⟩
    exact ⟨f, rfl, hbtw.symm⟩
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

@[simp]
lemma edgeMap_inc (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂) :
    (G.edgeMap σ hσ).Inc e' u ↔ ∃ e, σ e = e' ∧ G.Inc e u := by
  simp only [Inc, edgeMap_isLink]
  tauto

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
--   rw [map_vertexSet]
--   exact ⟨u, hin, rfl⟩

-- lemma mem_edgeSet_map (hin : e ∈ E(G)) : σ e ∈ E(G.map f σ hσ) := by
--   rw [map_edgeSet]
--   use e

-- @[simp]
-- lemma map_eq_Map (f : α → α') : G.map f id (by simp_all) = (f ''ᴳ G) := by
--   ext a b c
--   · simp
--   · simp +contextual only [map_isLink, id_eq, exists_eq_left, exists_and_left, Map_isLink,
--     iff_def, forall_exists_index, and_imp]
--     tauto
