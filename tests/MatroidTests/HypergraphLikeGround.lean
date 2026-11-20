module

public import Matroid.GraphTheory.HypergraphLike.Hom
public import Matroid.GraphTheory.HypergraphLike.Subgraph
public import Matroid.GraphTheory.IncidenceHypergraph.Basic

/-! # Regression tests for HypergraphLike ground-set automation -/

open Set HypergraphLike

section Ground

variable {V I E Gr Gr₂ : Type*} {G : Gr} {H : Gr₂}
  [HypergraphLike V I E G] [HypergraphLike V I E H] {e : E} {v : V} {i : I}

example (hs : IsSource G i) (hi : i ∉ I(G)) : False := by grind
example (ht : IsTarget G i) (hGH : IsSubgraph G H) : i ∈ I(H) := by grind

example (hi : i ∈ edgeFiber G e) : i ∈ I(G) ∧ e ∈ E(G) := by grind
example (hi : i ∈ vertexFiber G v) : i ∈ I(G) ∧ v ∈ V(G) := by grind
example (hGH : IsSubgraph G H) : edgeFiber G e ⊆ I(H) := by grind

example {κ : Type*} (f : κ → E) : (⋃ k, edgeFiber G (f k)) ⊆ I(G) := by grind
example (S : Set V) (hi : i ∈ ⋃ v ∈ S, vertexFiber G v) : i ∈ I(G) := by grind

example [Nonempty V] (hi : i ∈ edgeFiber G e) : attach G i ∈ V(G) := by grind
example [Nonempty E] (hs : IsSource G i) : edgeMap G i ∈ E(G) := by grind

private def incidence (H : Gr₂) [HypergraphLike V I E H] (i : I)
    (hi : i ∈ I(H) := by grind) : I(H) :=
  ⟨i, hi⟩

example (hGH : IsSubgraph G H) (hi : i ∈ edgeFiber G e) : I(H) :=
  incidence H i

end Ground

section Hom

variable {V I E V' I' E' Gr Gr₂ : Type*} {G : Gr} {H : Gr₂}
  [HypergraphLike V I E G] [HypergraphLike V' I' E' H] {e : E} {u v : V} {i : I}

example [Nonempty V'] (F : IncHom G H) (h : IsLink G e u v) : F.vertMap u ∈ V(H) := by grind
example [Nonempty I'] (F : IncHom G H) (ht : IsTarget G i) : F.incMap i ∈ I(H) := by grind
example [Nonempty E'] (F : IncHom G H) (h : IsLink G e u v) : F.edgeMap e ∈ E(H) := by grind

end Hom

section Dual

variable {V I E : Type*} {G : IncidenceHypergraph V I E} {e : E} {v : V} {i : I}

example (hi : i ∈ edgeFiber G e) : e ∈ V(G.dual) := by grind
example (hi : i ∈ vertexFiber G v) : i ∈ I(G.dual) ∧ v ∈ E(G.dual) := by grind

end Dual
