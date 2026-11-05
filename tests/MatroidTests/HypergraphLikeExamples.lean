import Matroid.GraphTheory.HypergraphLike.Examples

universe u v

open Set HypergraphLike

example {α : Type*} [L : Lattice α] {x y : α} (h : x ⋖ y) :
    IsLink L (x, y) x y := by
  exact ⟨⟨((x, y), true), ((x, y), false), by simp, ⟨rfl, h⟩,
    ⟨Bool.false_ne_true, h⟩, rfl, rfl, rfl, rfl⟩⟩

example {α : Type*} [L : Lattice α] (x : α) :
    ¬ IsLink L (x, x) x x := by
  intro h
  have hx : x ⋖ x := h.edge_mem_edgeSet
  exact hx.ne rfl

private theorem cayley_link {α : Type*} [G : Group α] (g x : α) :
    IsLink (G, g) x x (x * g) := by
  exact ⟨⟨(x, true), (x, false), by simp, rfl, Bool.false_ne_true, rfl, rfl, rfl, rfl⟩⟩

example {α : Type*} [G : Group α] (x : α) : IsLink (G, (1 : α)) x x x := by
  simpa using cayley_link (1 : α) x

example {V : Type u} (Q : Quiver.{v} V) (x y : V) (f : Q.Hom x y) :
    IsLink Q ⟨x, y, f⟩ x y := by
  exact ⟨⟨(⟨x, y, f⟩, true), (⟨x, y, f⟩, false), by simp,
    rfl, Bool.false_ne_true, rfl, rfl, rfl, rfl⟩⟩

example (Q : Quiver.{v} Unit) (f g : Q.Hom () ()) (hfg : f ≠ g) :
    ∃ e f : (Σ x y : Unit, Q.Hom x y), e ≠ f ∧ IsLink Q e () () ∧ IsLink Q f () () := by
  refine ⟨⟨(), (), f⟩, ⟨(), (), g⟩, ?_, ?_, ?_⟩
  · simpa using hfg
  · exact ⟨⟨(⟨(), (), f⟩, true), (⟨(), (), f⟩, false), by simp,
      rfl, Bool.false_ne_true, rfl, rfl, rfl, rfl⟩⟩
  · exact ⟨⟨(⟨(), (), g⟩, true), (⟨(), (), g⟩, false), by simp,
      rfl, Bool.false_ne_true, rfl, rfl, rfl, rfl⟩⟩

example {X : Type*} [TopologicalSpace X] (G : _root_.GraphLike X) {e : Set X} {x y : X}
    (h : G.IsLink e x y) : IsLink G e x y := by
  have hx : x ∈ G.edgeBoundary e := h.2 ▸ mem_insert x {y}
  have hy : y ∈ G.edgeBoundary e := h.2 ▸ mem_insert_of_mem x (mem_singleton y)
  by_cases hxy : x = y
  · subst y
    refine ⟨⟨(e, x, false), (e, x, true), by simp,
      ⟨h.1, hx, by simp⟩, ⟨h.1, hx, ?_⟩, rfl, rfl, rfl, rfl⟩⟩
    simpa using h.2
  · exact ⟨⟨(e, x, false), (e, y, false), by simpa using hxy,
      ⟨h.1, hx, by simp⟩, ⟨h.1, hy, by simp⟩, rfl, rfl, rfl, rfl⟩⟩

example {X : Type*} [TopologicalSpace X] (G : _root_.GraphLike X) {e : Set X} {x y : X}
    (hb : G.edgeBoundary e = {x, y}) (hxy : x ≠ y) : ¬ IsLink G e x x := by
  rintro ⟨l⟩
  rcases l with ⟨⟨e₁, x₁, b₁⟩, ⟨e₂, x₂, b₂⟩, hne, hs, ht, he₁, he₂, hx₁, hx₂⟩
  change e₁ = e at he₁
  change e₂ = e at he₂
  change x₁ = x at hx₁
  change x₂ = x at hx₂
  subst e₁ e₂ x₁ x₂
  change _ ∧ _ ∧ (b₁ = true → G.edgeBoundary e = {x}) at hs
  change _ ∧ _ ∧ (b₂ = true → G.edgeBoundary e = {x}) at ht
  have hn : G.edgeBoundary e ≠ {x} := by
    rw [hb]
    intro h
    have hy : y ∈ ({x} : Set X) := h ▸ (by simp : y ∈ ({x, y} : Set X))
    exact hxy (mem_singleton_iff.mp hy).symm
  have h₁ : b₁ = false := Bool.eq_false_iff.mpr fun h ↦ hn (hs.2.2 h)
  have h₂ : b₂ = false := Bool.eq_false_iff.mpr fun h ↦ hn (ht.2.2 h)
  exact hne (by simp [h₁, h₂])
