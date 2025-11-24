import Matroid.Graph.Subgraph.Delete

variable {α β : Type*} {x y z u v w a b : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set Function

open scoped Sym2

namespace Graph

@[simps]
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
@[simps]
def Map {α' : Type*} (f : α → α') (G : Graph α β) : Graph α' β where
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

scoped infix:51 " ''ᴳ " => Map

variable {α' α'' : Type*} {f g : α → α'} {f' g' : α' → α} {x y z : α'} {G' H' : Graph α' β}

/-- `Map` has the expected incidence predicate. -/
@[simp]
lemma map_inc : (f ''ᴳ G).Inc e x ↔ ∃ v, G.Inc e v ∧ x = f v := by
  simp only [Inc, Map_isLink]
  tauto

lemma IsLink.Map (h : G.IsLink e u v) (f : α → α') : (f ''ᴳ G).IsLink e (f u) (f v) := by
  simp only [Map_isLink]
  use u, v, h

@[gcongr]
lemma map_congr_left_of_eqOn (h : EqOn f g V(G)) : (f ''ᴳ G) = (g ''ᴳ G) := by
  apply Graph.ext ?_ fun e x y ↦ ?_
  · rw [Map_vertexSet, Map_vertexSet]
    exact image_congr h
  · simp_rw [Map_isLink]
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
    simp only [Map_vertexSet, mem_image, forall_exists_index, and_imp]
    rintro u hu rfl
    use u, vertexSet_mono h hu
  isLink_of_isLink e x y := by
    simp only [Map_isLink, forall_exists_index, and_imp]
    rintro a b hab rfl rfl
    use a, b, hab.of_le h

@[gcongr]
lemma map_isSpanningSubgraph (hsle : G ≤s H) : f ''ᴳ G ≤s f ''ᴳ H where
  vertexSet_eq := by simp [hsle.vertexSet_eq]
  isLink_of_isLink := (map_mono hsle.le).isLink_of_isLink

lemma map_edgeRestrict_comm : f ''ᴳ (G ↾ F) = (f ''ᴳ G) ↾ F := by
  ext a b c
  · simp
  simp only [Map_isLink, edgeRestrict_isLink]
  tauto

lemma map_edgeDelete_comm : f ''ᴳ (G ＼ F) = (f ''ᴳ G) ＼ F := by
  ext a b c
  · simp
  simp only [Map_isLink, edgeDelete_isLink]
  tauto

lemma induce_map_isSpanningSubgraph : f ''ᴳ (G[X]) ≤s (f ''ᴳ G)[f '' X] where
  vertexSet_eq := by simp
  isLink_of_isLink e x y := by
    simp only [Map_isLink, induce_isLink, mem_image, forall_exists_index, and_imp]
    intro a b hab ha hb rfl rfl
    use (by use a, b), (by use a), by use b

lemma map_vertexDelete_isInducedSubgraph : (f ''ᴳ G) - (f '' X) ≤i f ''ᴳ (G - X) where
  le := by
    constructor
    · simp [subset_image_diff]
    simp only [vertexDelete_isLink_iff, Map_isLink, mem_image, not_exists, not_and, and_imp,
      forall_exists_index]
    intro e u v x y hxy rfl rfl hnex hney
    have hx := by simpa using hnex x
    have hy := by simpa using hney y
    use x, y
  isLink_of_mem_mem e x y := by
    simp +contextual only [Map_isLink, vertexDelete_isLink_iff, vertexDelete_vertexSet,
      Map_vertexSet, mem_diff, mem_image, not_exists, not_and, not_false_eq_true, implies_true,
      and_self, and_true, and_imp, forall_exists_index]
    intro u v huv huX hvX rfl rfl a ha hau hneu b hb hbv hnev
    use u, v

lemma surjOn_of_le_map {G} (h : G ≤ f ''ᴳ H) : SurjOn f V(H) V(G) := by
  intro a' ha'
  exact vertexSet_mono h ha'

lemma exists_map_eq_of_le_map {G} (h : G ≤ f ''ᴳ H) : ∃ H' ≤ H, f ''ᴳ H' = G := by
  use H[V(H) ∩ f ⁻¹' V(G)] ↾ E(G), .trans edgeRestrict_le <| induce_le inter_subset_left, ?_
  refine ext_of_le_le ?_ h ?_ ?_
  · gcongr
    exact .trans edgeRestrict_le <| induce_le inter_subset_left
  · ext x
    simp only [Map_vertexSet, edgeRestrict_vertexSet, induce_vertexSet, mem_image, mem_inter_iff,
      mem_preimage]
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, ⟨hyH, hy⟩, rfl⟩
      exact hy
    obtain ⟨y, hy, rfl⟩ := by simpa using vertexSet_mono h hx
    use y
  simp only [Map_edgeSet, edgeRestrict_edgeSet, inter_eq_right, induce_edgeSet, mem_inter_iff,
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

structure IsRetr (G : Graph α β) (f : α → α) where
  mapsTo : Set.MapsTo f V(G) V(G)
  isIdem : ∀ v ∈ V(G), f (f v) = f v

variable {f f' : α → α}

@[simp]
lemma IsRetr.vertexSet_subset (hf : G.IsRetr f) : V(f ''ᴳ G) ⊆ V(G) :=
  hf.mapsTo.image_subset

@[simp]
lemma IsRetr.idem (hf : G.IsRetr f) : f ''ᴳ (f ''ᴳ G) = f ''ᴳ G := by
  ext a b c
  · simp only [map_map, Map_vertexSet, comp_apply, mem_image]
    refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
    rw [hf.isIdem x hx]
  simp only [map_map, Map_isLink, comp_apply]
  refine exists₂_congr fun x y ↦ and_congr_right fun hxy ↦ ?_
  rw [hf.isIdem x hxy.left_mem, hf.isIdem y hxy.right_mem]

lemma IsRetr.eqOn_id_of_Map_eq (hf : G.IsRetr f) (h : f ''ᴳ G = G) : V(G).EqOn f id := by
  rintro x hx
  simp only [id_eq]
  have hV := by simpa using congr_arg vertexSet h
  rw [← hV] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hf.isIdem y hy

lemma IsRetr.Map_eq_self_iff (hf : G.IsRetr f) : f ''ᴳ G = G ↔ V(G).EqOn f id :=
  ⟨hf.eqOn_id_of_Map_eq, fun h ↦ by simpa using map_congr_left_of_eqOn h⟩

lemma IsRetr.map_eq_of_le_map_le_map (hf : G.IsRetr f) (hf' : H.IsRetr f') (hGH : G ≤ f' ''ᴳ H)
    (hHG : H ≤ f ''ᴳ G) : G = f' ''ᴳ H ∧ H = f ''ᴳ G := by
  have hV : V(G) = V(H) := antisymm (vertexSet_mono hGH |>.trans hf'.mapsTo.image_subset)
    (vertexSet_mono hHG |>.trans hf.mapsTo.image_subset)
  have hFG : f '' V(G) = V(G) :=
    hf.mapsTo.image_subset.antisymm <| by simpa [hV] using vertexSet_mono hHG
  have hF'H : f' '' V(H) = V(H) :=
    hf'.mapsTo.image_subset.antisymm <| by simpa [hV] using vertexSet_mono hGH
  have hE : E(G) = E(H) := by
    apply_fun edgeSet (α := α) (β := β) at hHG hGH using edgeSet_monotone (α := α) (β := β)
    simp only [Map_edgeSet, le_eq_subset] at hHG hGH
    exact hGH.antisymm hHG
  refine ⟨?_, ?_⟩
  · exact ext_of_le_le hGH le_rfl (by simp [hF'H, hV]) (by simpa)
  · exact ext_of_le_le hHG le_rfl (by simp [hFG, ← hV]) (by simp [hE])

@[simp]
lemma IsRetr.map_le_self_iff (hf : G.IsRetr f) : f ''ᴳ G ≤ G ↔ (f ''ᴳ G).IsLink = G.IsLink := by
  refine ⟨fun hle ↦ ?_, fun heq ↦ ⟨hf.vertexSet_subset, ?_⟩⟩
  · ext e u v
    exact ⟨fun h ↦ h.of_le hle, fun h ↦ h.of_le_of_mem hle (by simp [h.edge_mem])⟩
  simp_rw [heq]
  tauto

@[simps]
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

@[simps]
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

-- @[simps! vertexSet edgeSet]
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
