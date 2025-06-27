import Matroid.Graph.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card

variable {α β : Type*} {x y z u v w a b : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set Function

open scoped Sym2

namespace Graph

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set
by applying a function `f : α → α'` to each vertex.
Edges between identified vertices become loops. -/
@[simps]
def vertexMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
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

scoped infix:50 " '' " => fun f G ↦ vertexMap G f

variable {α' : Type*} {f g : α → α'} {x y z : α'}

/-- `vertexMap` has the expected incidence predicate. -/
@[simp]
lemma vertexMap_inc : (f '' G).Inc e x ↔ ∃ v, G.Inc e v ∧ x = f v := by
  simp only [Inc, vertexMap_isLink]
  tauto

lemma vertexMap_eq_vertexMap_of_eqOn (h : EqOn f g V(G)) : (f '' G) = (g '' G) := by
  apply Graph.ext ?_ fun e x y ↦ ?_
  · rw [vertexMap_vertexSet, vertexMap_vertexSet]
    exact image_congr h
  · simp_rw [vertexMap_isLink]
    refine ⟨fun ⟨v, w, hvw, _, _⟩ ↦ ?_, fun ⟨v, w, hvw, _, _⟩ ↦ ?_⟩ <;> subst x y
    · use v, w, hvw, h hvw.left_mem, h hvw.right_mem
    · use v, w, hvw, (h hvw.left_mem).symm, (h hvw.right_mem).symm

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
  simp [Inc, exists_eq_left']

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

@[simps! vertexSet edgeSet]
def map (G : Graph α β) (f : α → α') (σ : β → β')
    (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂) : Graph α' β' :=
  f '' G.edgeMap σ hσ

variable {G : Graph α β} {f : α → α'} {σ : β → β'}
  (hσ : ∀ e₁ ∈ E(G), ∀ e₂ ∈ E(G), σ e₁ = σ e₂ → G.IsLink e₁ = G.IsLink e₂)

-- #print map_isLink

@[simp]
lemma map_isLink : (G.map f σ hσ).IsLink e' x y ↔ ∃ u v e, σ e = e' ∧ x = f u ∧ y = f v ∧
    G.IsLink e u v := by
  simp +contextual only [map, vertexMap_isLink, edgeMap_isLink, iff_def, forall_exists_index,
    and_imp]
  tauto

lemma IsLink.map (hbtw : G.IsLink e u v) : (G.map f σ hσ).IsLink (σ e) (f u) (f v) := by
  rw [map_isLink]
  use u, v, e

lemma mem_vertexSet_map (hin : u ∈ V(G)) : f u ∈ V(G.map f σ hσ) := by
  rw [map_vertexSet]
  exact ⟨u, hin, rfl⟩

lemma mem_edgeSet_map (hin : e ∈ E(G)) : σ e ∈ E(G.map f σ hσ) := by
  rw [map_edgeSet]
  use e

@[simp]
lemma map_eq_vertexMap (f : α → α') : G.map f id (by simp_all) = (f '' G) := by
  ext a b c
  · simp
  · simp +contextual only [map_isLink, id_eq, exists_eq_left, exists_and_left, vertexMap_isLink,
    iff_def, forall_exists_index, and_imp]
    tauto
