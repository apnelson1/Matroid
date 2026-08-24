module

public import Matroid.IRw
public import Matroid.Graph.IRw
public import Matroid.Graph.Relabel
public import Matroid.Graph.Walk.Iso
public import Matroid.Transport
public import Matroid.ForMathlib.Tactic.IRw.Equiv

@[expose] public section

open Set

/-!
# `irw` regression tests

This file consolidates the transport, registration, locality, naturality, priority,
supported-domain, path, walk, and former frontier regressions for `irw`.

The opening section is intentionally much more aggressive than a normal API test. It asks whether
`irw` can traverse a proposition of arbitrary logical depth while alternately transporting binders
and applying registered atomic facts.
-/

namespace MatroidIRwTests

universe uα uβ
variable {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β}

example (i : M ≂ N) (I : Set M.E) (h : N.Indep (↑(i '' I) : Set β)) :
    M.Indep (↑I : Set α) := by
  irw i
  exact h

example (i : M ≂ N) (I : Set M.E) (h : M.Indep (↑I : Set α)) :
    N.Indep (↑(i '' I) : Set β) := by
  irw i at h
  exact h

-- Arbitrarily many simultaneously live set variables.  This is exactly the shape that hit the
-- typeclass arity ceiling.
example (i : M ≂ N)
    (h : ∀ I J K : Set N.E,
      (N.Indep (↑I : Set β) ∧ N.Dep (↑J : Set β)) →
        (N.IsBasis (↑I : Set β) (↑K : Set β) ∨
          (N.Spanning (↑J : Set β) ↔ N.Nonspanning (↑K : Set β)))) :
    ∀ I J K : Set M.E,
      (M.Indep (↑I : Set α) ∧ M.Dep (↑J : Set α)) →
        (M.IsBasis (↑I : Set α) (↑K : Set α) ∨
          (M.Spanning (↑J : Set α) ↔ M.Nonspanning (↑K : Set α))) := by
  irw i
  exact h

-- Deep alternation of forall/exists with all binders intrinsic.
example (i : M ≂ N)
    (h : ∀ I : Set N.E, N.Indep (↑I : Set β) →
      ∃ B : Set N.E, N.IsBasis (↑I : Set β) (↑B : Set β) ∧
        ∀ D : Set N.E, N.Dep (↑D : Set β) →
          ∃ X : Set N.E,
            (N.Spanning (↑X : Set β) ∨ N.Coindep (↑D : Set β)) ∧
            (N.Codep (↑B : Set β) → N.Nonspanning (↑X : Set β))) :
    ∀ I : Set M.E, M.Indep (↑I : Set α) →
      ∃ B : Set M.E, M.IsBasis (↑I : Set α) (↑B : Set α) ∧
        ∀ D : Set M.E, M.Dep (↑D : Set α) →
          ∃ X : Set M.E,
            (M.Spanning (↑X : Set α) ∨ M.Coindep (↑D : Set α)) ∧
            (M.Codep (↑B : Set α) → M.Nonspanning (↑X : Set α)) := by
  irw i
  exact h

-- Ambient bounded forall/exists.  This is the decisive bounded-domain test: none of the ambient
-- types `Set α` / `Set β` are transported; only the supported subtypes are.
example (i : M ≂ N)
    (h : ∀ I : Set β, I ⊆ N.E → N.Indep I →
      ∃ B : Set β, B ⊆ N.E ∧ N.IsBasis I B ∧
        ∀ D : Set β, D ⊆ N.E → N.Dep D →
          ∃ X : Set β, X ⊆ N.E ∧
            (N.Spanning X ∨ N.Coindep D) ∧
            (N.Codep B → N.Nonspanning X)) :
    ∀ I : Set α, I ⊆ M.E → M.Indep I →
      ∃ B : Set α, B ⊆ M.E ∧ M.IsBasis I B ∧
        ∀ D : Set α, D ⊆ M.E → M.Dep D →
          ∃ X : Set α, X ⊆ M.E ∧
            (M.Spanning X ∨ M.Coindep D) ∧
            (M.Codep B → M.Nonspanning X) := by
  irw i
  exact h

-- Several independent bounded variables remain live simultaneously.
example (i : M ≂ N)
    (h : ∀ I J K : Set β,
      I ⊆ N.E → J ⊆ N.E → K ⊆ N.E →
      (N.Indep I ∧ N.Dep J) → N.IsBasis I K) :
    ∀ I J K : Set α,
      I ⊆ M.E → J ⊆ M.E → K ⊆ M.E →
      (M.Indep I ∧ M.Dep J) → M.IsBasis I K := by
  irw i
  exact h

-- A later set may be supported only indirectly through an earlier transported set.  The local
-- support prover closes `B ⊆ A ⊆ E`, while subset transport keeps the two dependent bounds
-- coherent.
example (i : M ≂ N)
    (h : ∀ A B : Set β, A ⊆ N.E → B ⊆ A → N.Indep B → N.Spanning A) :
    ∀ A B : Set α, A ⊆ M.E → B ⊆ A → M.Indep B → M.Spanning A := by
  irw i
  exact h

-- Support chains are not limited to one indirect step.
example (i : M ≂ N)
    (h : ∀ A : Set β, A ⊆ N.E →
      ∀ B : Set β, B ⊆ A →
        ∀ C : Set β, C ⊆ B →
          ∀ D : Set β, D ⊆ C → N.Indep D → N.Spanning A) :
    ∀ A : Set α, A ⊆ M.E →
      ∀ B : Set α, B ⊆ A →
        ∀ C : Set α, C ⊆ B →
          ∀ D : Set α, D ⊆ C → M.Indep D → M.Spanning A := by
  irw i
  exact h

-- Support may be available through either branch of a local disjunction.
example (i : M ≂ N)
    (h : ∀ A : Set β, A ⊆ N.E →
      ∀ C : Set β, C ⊆ N.E →
        ∀ B : Set β, (B ⊆ A ∨ B ⊆ C) → N.Indep B → N.Spanning A) :
    ∀ A : Set α, A ⊆ M.E →
      ∀ C : Set α, C ⊆ M.E →
        ∀ B : Set α, (B ⊆ A ∨ B ⊆ C) → M.Indep B → M.Spanning A := by
  irw i
  exact h

-- The failure reported in IRw.md: all support guards are batched after all set binders.
example (i : M ≂ N)
    (h : ∀ I J K : Set β,
      I ⊆ N.E → J ⊆ N.E → K ⊆ N.E →
      (N.Indep I ∧ N.Dep J) → N.IsBasis I K) :
    ∀ I J K : Set α,
      I ⊆ M.E → J ⊆ M.E → K ⊆ M.E →
      (M.Indep I ∧ M.Dep J) → M.IsBasis I K := by
  irw i
  exact h

-- Guard order need not agree with binder order.  `irw` must restore the original order on the
-- transported target rather than merely leave the normalized telescope exposed.
example (i : M ≂ N)
    (h : ∀ I J K : Set β,
      K ⊆ N.E → I ⊆ N.E → J ⊆ N.E →
      N.Indep I → N.IsBasis J K) :
    ∀ I J K : Set α,
      K ⊆ M.E → I ⊆ M.E → J ⊆ M.E →
      M.Indep I → M.IsBasis J K := by
  irw i
  exact h

-- An unrelated implication may sit among the batched guards.  Its relative position must also be
-- restored after transport.
example (i : M ≂ N)
    (h : ∀ I J : Set β,
      N.Spanning I → I ⊆ N.E → J ⊆ N.E → N.Dep J → N.IsBasis I J) :
    ∀ I J : Set α,
      M.Spanning I → I ⊆ M.E → J ⊆ M.E → M.Dep J → M.IsBasis I J := by
  irw i
  exact h

-- The normalization must work recursively under ordinary logical structure and when rewriting a
-- local hypothesis rather than the target.
example (i : M ≂ N)
    (h : ¬ (∀ I J : Set α,
      I ⊆ M.E → J ⊆ M.E → (M.Indep I → M.Dep J))) :
    ¬ (∀ I J : Set β,
      I ⊆ N.E → J ⊆ N.E → (N.Indep I → N.Dep J)) := by
  irw i at h
  exact h

example (i : M ≂ N)
    (h : ∀ A B C D E : Set N.E,
      (N.Indep A ∧ ¬ N.Dep B) →
      ((N.IsBasis A C ∨ N.Spanning D) ↔
        (N.Coindep E → (N.Codep C ∨ ¬ N.Nonspanning B)))) :
    ∀ A B C D E : Set M.E,
      (M.Indep A ∧ ¬ M.Dep B) →
      ((M.IsBasis A C ∨ M.Spanning D) ↔
        (M.Coindep E → (M.Codep C ∨ ¬ M.Nonspanning B))) := by
  irw i
  exact h

-- Deep quantifier alternation; five sets remain live at the deepest leaf.
example (i : M ≂ N)
    (h : ∀ A : Set N.E, N.Indep A →
      ∃ B : Set N.E, N.IsBasis A B ∧
      ∀ C : Set N.E, N.Dep C →
      ∃ D : Set N.E, N.Spanning D ∧
      ∀ E : Set N.E,
        (N.Coindep E ∨ N.Codep B) ↔ (N.Nonspanning C → N.Indep A)) :
    ∀ A : Set M.E, M.Indep A →
      ∃ B : Set M.E, M.IsBasis A B ∧
      ∀ C : Set M.E, M.Dep C →
      ∃ D : Set M.E, M.Spanning D ∧
      ∀ E : Set M.E,
        (M.Coindep E ∨ M.Codep B) ↔ (M.Nonspanning C → M.Indep A) := by
  irw i
  exact h

/-! ## Batched and scrambled ambient support guards -/

example (i : M ≂ N)
    (h : ∀ A B C D E : Set β,
      A ⊆ N.E → B ⊆ N.E → C ⊆ N.E → D ⊆ N.E → E ⊆ N.E →
      (N.Indep A ∧ N.Dep B) →
      (N.IsBasis C D ∨ (N.Spanning E ↔ N.Nonspanning A))) :
    ∀ A B C D E : Set α,
      A ⊆ M.E → B ⊆ M.E → C ⊆ M.E → D ⊆ M.E → E ⊆ M.E →
      (M.Indep A ∧ M.Dep B) →
      (M.IsBasis C D ∨ (M.Spanning E ↔ M.Nonspanning A)) := by
  irw i
  exact h

-- Same guards, intentionally in a different order from the binders.
example (i : M ≂ N)
    (h : ∀ A B C D : Set β,
      D ⊆ N.E → B ⊆ N.E → A ⊆ N.E → C ⊆ N.E →
      N.Indep A → N.IsBasis B C → N.Spanning D) :
    ∀ A B C D : Set α,
      D ⊆ M.E → B ⊆ M.E → A ⊆ M.E → C ⊆ M.E →
      M.Indep A → M.IsBasis B C → M.Spanning D := by
  irw i
  exact h

-- Bounded exists nested under a batched bounded forall prefix.
example (i : M ≂ N)
    (h : ∀ A B : Set β, A ⊆ N.E → B ⊆ N.E → N.Indep A →
      ∃ C : Set β, C ⊆ N.E ∧ N.IsBasis A C ∧
        ∃ D : Set β, D ⊆ N.E ∧ (N.Dep D ∨ N.Spanning B)) :
    ∀ A B : Set α, A ⊆ M.E → B ⊆ M.E → M.Indep A →
      ∃ C : Set α, C ⊆ M.E ∧ M.IsBasis A C ∧
        ∃ D : Set α, D ⊆ M.E ∧ (M.Dep D ∨ M.Spanning B) := by
  irw i
  exact h

/-! ## Structural binder types above the active ground type -/

example (i : M ≂ N)
    (h : ∀ p : Set N.E × Set N.E,
      N.Indep p.1 → N.Dep p.2 → N.IsBasis p.1 p.2) :
    ∀ p : Set M.E × Set M.E,
      M.Indep p.1 → M.Dep p.2 → M.IsBasis p.1 p.2 := by
  irw i
  exact h

example (i : M ≂ N)
    (h : ∀ S : Set (Set N.E), ∀ A : Set N.E,
      A ∈ S → N.Indep A → N.Spanning A) :
    ∀ S : Set (Set M.E), ∀ A : Set M.E,
      A ∈ S → M.Indep A → M.Spanning A := by
  irw i
  exact h

example (i : M ≂ N)
    (h : ∀ o p : Option (Set N.E), o = p ↔ p = o) :
    ∀ o p : Option (Set M.E), o = p ↔ p = o := by
  irw i
  exact h

example (i : M ≂ N)
    (h : ∀ s t : (Set N.E ⊕ Set N.E), s = t ↔ t = s) :
    ∀ s t : (Set M.E ⊕ Set M.E), s = t ↔ t = s := by
  irw i
  exact h

/-! ## The supplied iso may itself be constructed -/

example (i : M ≂ N)
    (h : ∀ A : Set N✶.E, N✶.Indep A → N✶.Spanning A) :
    ∀ A : Set M✶.E, M✶.Indep A → M✶.Spanning A := by
  irw i.dual
  exact h

-- Restriction is deliberately constructed by hand; `irw` consumes the resulting isomorphism.
example (i : M ≂ N)
    (h : ∀ A : Set (N.restrict N.E).E, (N.restrict N.E).Indep A → (N.restrict N.E).Spanning A) :
    ∀ A : Set (M.restrict M.E).E, (M.restrict M.E).Indep A → (M.restrict M.E).Spanning A := by
  let j : (M.restrict M.E) ≂ (N.restrict N.E) :=
    i.restrict (R := M.E) (S := N.E) (by simp) (by simp) (by simp)
  irw j
  exact h

/-! ## Direction, identity and locations -/

example (i : M ≂ N)
    (h : ∀ A B : Set M.E, M.Indep A → M.IsBasis A B) :
    ∀ A B : Set M.E, M.Indep A → M.IsBasis A B := by
  have h' := h
  irw i at h'
  irw i.symm at h'
  exact h'

example (h : ∀ A : Set M.E, M.Indep A ↔ ¬ M.Dep A) :
    ∀ A : Set M.E, M.Indep A ↔ ¬ M.Dep A := by
  have h' := h
  irw (Matroid.Iso.refl (M := M)) at h'
  exact h'

example (i : M ≂ N) (A B : Set M.E)
    (hA : M.Indep A) (hB : M.Dep B) : M.Indep A ∧ M.Dep B := by
  irw i at hA hB ⊢
  exact ⟨hA, hB⟩

end MatroidIRwTests

namespace GraphIRwTests

open Graph

universe uV uE uV' uE' uV'' uE''
variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {V'' : Type uV''} {E'' : Type uE''}
  {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}

example (i : Graph.Iso G H) (x y : V(G))
    (h : H.Adj (i.vertexEquiv x).1 (i.vertexEquiv y).1) : G.Adj x.1 y.1 := by
  irw i
  exact h

-- Intrinsic active vertices/edges plus deeply nested logic.
example (i : Graph.Iso G H)
    (h : ∀ x y : V(H),
      H.Adj x.1 y.1 →
        ∃ e : E(H),
          H.IsLink e.1 x.1 y.1 ∧
          (H.Adj y.1 x.1 ↔ ¬¬ H.Adj x.1 y.1)) :
    ∀ x y : V(G),
      G.Adj x.1 y.1 →
        ∃ e : E(G),
          G.IsLink e.1 x.1 y.1 ∧
          (G.Adj y.1 x.1 ↔ ¬¬ G.Adj x.1 y.1) := by
  irw i
  exact h

-- Ambient bounded graph variables.  The active-set guards are bundled into the subtypes V(G), E(G)
-- by the generic bounded quantifier machinery.
example (i : Graph.Iso G H)
    (h : ∀ x : V', x ∈ V(H) →
      ∀ y : V', y ∈ V(H) →
        H.Adj x y →
          ∃ e : E', e ∈ E(H) ∧ H.IsLink e x y) :
    ∀ x : V, x ∈ V(G) →
      ∀ y : V, y ∈ V(G) →
        G.Adj x y →
          ∃ e : E, e ∈ E(G) ∧ G.IsLink e x y := by
  irw i
  exact h

/-! ## Ambient variables whose graph atoms infer active-set support -/

-- Neither endpoint is explicitly guarded: adjacency supplies both support certificates.
example (i : Graph.Iso G H)
    (h : ∀ x y : V', H.Adj x y → H.Adj y x) :
    ∀ x y : V, G.Adj x y → G.Adj y x := by
  irw i
  exact h

-- Incidence distinguishes and supports an ambient edge and an ambient vertex.
example (i : Graph.Iso G H)
    (h : ∀ e : E', ∀ x : V', H.Inc e x → H.Inc e x) :
    ∀ e : E, ∀ x : V, G.Inc e x → G.Inc e x := by
  irw i
  exact h

-- A link supplies support for its edge and both endpoints.
example (i : Graph.Iso G H)
    (h : ∀ e : E', ∀ x y : V', H.IsLink e x y → H.Adj x y) :
    ∀ e : E, ∀ x y : V, G.IsLink e x y → G.Adj x y := by
  irw i
  exact h

-- Support evidence may occur several implications after the ambient binders.
example (i : Graph.Iso G H)
    (h : ∀ e : E', ∀ x : V', True →
      (H.Inc e x → H.Adj x x) → H.Inc e x → H.Adj x x) :
    ∀ e : E, ∀ x : V, True →
      (G.Inc e x → G.Adj x x) → G.Inc e x → G.Adj x x := by
  irw i
  exact h

-- Branching is independent of guard adjacency; the stable target normal form retains its inferred
-- support guard for a top-level disjunction.
example (i : Graph.Iso G H)
    (h : ∀ x : V', x ∈ V(H) →
      (H.Adj x x → H.Adj x x) ∨ (H.Adj x x → H.Adj x x)) :
    ∀ x : V,
      (G.Adj x x → G.Adj x x) ∨ (G.Adj x x → G.Adj x x) := by
  irw i
  exact h

-- Mixed bounded/unbounded depth with several simultaneously live vertices.
example (i : Graph.Iso G H)
    (h : ∀ x : V', x ∈ V(H) →
      ∀ y : V', y ∈ V(H) →
      ∀ z : V', z ∈ V(H) →
        (H.Adj x y ∧ H.Adj y z) →
          (H.Adj x z ∨ ∃ e : E', e ∈ E(H) ∧ H.IsLink e x z)) :
    ∀ x : V, x ∈ V(G) →
      ∀ y : V, y ∈ V(G) →
      ∀ z : V, z ∈ V(G) →
        (G.Adj x y ∧ G.Adj y z) →
          (G.Adj x z ∨ ∃ e : E, e ∈ E(G) ∧ G.IsLink e x z) := by
  irw i
  exact h

/-! ## Every registered local graph predicate individually -/

example (i : Graph.Iso G H) (e : E(G)) (x : V(G))
    (h : H.Inc (i.edgeEquiv e).1 (i.vertexEquiv x).1) : G.Inc e.1 x.1 := by
  irw i
  exact h

example (i : Graph.Iso G H) (e : E(G)) (x : V(G))
    (h : H.IsLoopAt (i.edgeEquiv e).1 (i.vertexEquiv x).1) :
    G.IsLoopAt e.1 x.1 := by
  irw i
  exact h

example (i : Graph.Iso G H) (e : E(G)) (x : V(G))
    (h : H.IsNonloopAt (i.edgeEquiv e).1 (i.vertexEquiv x).1) :
    G.IsNonloopAt e.1 x.1 := by
  irw i
  exact h

example (i : Graph.Iso G H) (e : E(G)) (x : V(G))
    (h : (i.edgeEquiv e).1 ∈ H.incidenceSet (i.vertexEquiv x).1) :
    e.1 ∈ G.incidenceSet x.1 := by
  irw i
  exact h

example (i : Graph.Iso G H) (e : E(G)) (x : V(G))
    (h : (i.edgeEquiv e).1 ∈ H.loopSet (i.vertexEquiv x).1) :
    e.1 ∈ G.loopSet x.1 := by
  irw i
  exact h

example (i : Graph.Iso G H) (h : H.Loopless) : G.Loopless := by
  irw i
  exact h

example (i : Graph.Iso G H) (h : H.Simple) : G.Simple := by
  irw i
  exact h

example (i : Graph.Iso G H) (h : V(H).Nonempty ∧ E(H).Nonempty) :
    V(G).Nonempty ∧ E(G).Nonempty := by
  irw i
  exact h

example (i : Graph.Iso G H) (h : V(H).Finite ∧ E(H).Finite) :
    V(G).Finite ∧ E(G).Finite := by
  irw i
  exact h

/-! ## Composition of the graph rules inside one expression -/

example (i : Graph.Iso G H)
    (h : ∀ x y z : V(H), ∀ e f : E(H),
      H.IsLink e.1 x.1 y.1 →
      (H.Inc f.1 z.1 ∧
        (H.IsLoopAt e.1 x.1 ∨ H.IsNonloopAt e.1 x.1)) →
      ((e.1 ∈ H.loopSet x.1 ∨ f.1 ∈ H.incidenceSet z.1) ↔
        (H.Adj x.1 y.1 ∨ ¬ H.Adj y.1 z.1))) :
    ∀ x y z : V(G), ∀ e f : E(G),
      G.IsLink e.1 x.1 y.1 →
      (G.Inc f.1 z.1 ∧
        (G.IsLoopAt e.1 x.1 ∨ G.IsNonloopAt e.1 x.1)) →
      ((e.1 ∈ G.loopSet x.1 ∨ f.1 ∈ G.incidenceSet z.1) ↔
        (G.Adj x.1 y.1 ∨ ¬ G.Adj y.1 z.1)) := by
  irw i
  exact h

-- Alternating vertex/edge quantifiers to significant depth.
example (i : Graph.Iso G H)
    (h : ∀ x : V(H),
      ∃ e : E(H), H.Inc e.1 x.1 ∧
      ∀ y : V(H), H.Adj x.1 y.1 →
      ∃ f : E(H), H.IsLink f.1 x.1 y.1 ∧
      ∀ z : V(H),
        H.IsLoopAt e.1 z.1 ∨ H.IsNonloopAt f.1 z.1 ∨ ¬ H.Adj y.1 z.1) :
    ∀ x : V(G),
      ∃ e : E(G), G.Inc e.1 x.1 ∧
      ∀ y : V(G), G.Adj x.1 y.1 →
      ∃ f : E(G), G.IsLink f.1 x.1 y.1 ∧
      ∀ z : V(G),
        G.IsLoopAt e.1 z.1 ∨ G.IsNonloopAt f.1 z.1 ∨ ¬ G.Adj y.1 z.1 := by
  irw i
  exact h

-- Whole-graph and local invariants mixed together.
example (i : Graph.Iso G H)
    (h : (H.Loopless ∧ H.Simple ∧ V(H).Nonempty) →
      ∀ x y : V(H), H.Adj x.1 y.1 →
        ∃ e : E(H), H.IsLink e.1 x.1 y.1 ∧ H.IsNonloopAt e.1 x.1) :
    (G.Loopless ∧ G.Simple ∧ V(G).Nonempty) →
      ∀ x y : V(G), G.Adj x.1 y.1 →
        ∃ e : E(G), G.IsLink e.1 x.1 y.1 ∧ G.IsNonloopAt e.1 x.1 := by
  irw i
  exact h

/-! ## Ambient bounded variables, including batched mixed vertex/edge guards -/

example (i : Graph.Iso G H)
    (h : ∀ x y z : V', ∀ e f : E',
      x ∈ V(H) → y ∈ V(H) → z ∈ V(H) → e ∈ E(H) → f ∈ E(H) →
      H.IsLink e x y → H.Inc f z →
        (H.IsLoopAt e x ∨ H.IsNonloopAt f z) → H.Adj y z) :
    ∀ x y z : V, ∀ e f : E,
      x ∈ V(G) → y ∈ V(G) → z ∈ V(G) → e ∈ E(G) → f ∈ E(G) →
      G.IsLink e x y → G.Inc f z →
        (G.IsLoopAt e x ∨ G.IsNonloopAt f z) → G.Adj y z := by
  irw i
  exact h

-- Scrambled guard order across two different ambient carrier types.
example (i : Graph.Iso G H)
    (h : ∀ x y : V', ∀ e f : E',
      f ∈ E(H) → y ∈ V(H) → e ∈ E(H) → x ∈ V(H) →
      H.Inc e x → H.IsLink f x y → H.Adj x y) :
    ∀ x y : V, ∀ e f : E,
      f ∈ E(G) → y ∈ V(G) → e ∈ E(G) → x ∈ V(G) →
      G.Inc e x → G.IsLink f x y → G.Adj x y := by
  irw i
  exact h

-- Bounded exists nested under ambient bounded vertices.
example (i : Graph.Iso G H)
    (h : ∀ x y : V', x ∈ V(H) → y ∈ V(H) → H.Adj x y →
      ∃ e : E', e ∈ E(H) ∧
        H.IsLink e x y ∧ (H.IsLoopAt e x ∨ H.IsNonloopAt e x)) :
    ∀ x y : V, x ∈ V(G) → y ∈ V(G) → G.Adj x y →
      ∃ e : E, e ∈ E(G) ∧
        G.IsLink e x y ∧ (G.IsLoopAt e x ∨ G.IsNonloopAt e x) := by
  irw i
  exact h

/-! ## Structural binder equivalences composed with graph rules -/

example (i : Graph.Iso G H)
    (h : ∀ p : V(H) × E(H), H.Inc p.2.1 p.1.1 → H.IsNonloopAt p.2.1 p.1.1) :
    ∀ p : V(G) × E(G), G.Inc p.2.1 p.1.1 → G.IsNonloopAt p.2.1 p.1.1 := by
  irw i
  exact h

example (i : Graph.Iso G H)
    (h : ∀ X : Set V(H), ∀ x y : V(H),
      x ∈ X → H.Adj x.1 y.1 → H.Adj y.1 x.1) :
    ∀ X : Set V(G), ∀ x y : V(G),
      x ∈ X → G.Adj x.1 y.1 → G.Adj y.1 x.1 := by
  irw i
  exact h

example (i : Graph.Iso G H)
    (h : ∀ S : Set (V(H) × E(H)), ∀ p : V(H) × E(H),
      p ∈ S → H.Inc p.2.1 p.1.1) :
    ∀ S : Set (V(G) × E(G)), ∀ p : V(G) × E(G),
      p ∈ S → G.Inc p.2.1 p.1.1 := by
  irw i
  exact h

example (i : Graph.Iso G H)
    (h : ∀ o p : Option V(H), o = p ↔ p = o) :
    ∀ o p : Option V(G), o = p ↔ p = o := by
  irw i
  exact h

example (i : Graph.Iso G H)
    (h : ∀ s t : (V(H) ⊕ E(H)), s = t ↔ t = s) :
    ∀ s t : (V(G) ⊕ E(G)), s = t ↔ t = s := by
  irw i
  exact h

/-! ## Composition, symmetry, identity and rewriting locations -/

example (i : Graph.Iso G H) (j : Graph.Iso H K)
    (h : ∀ x y : V(K), ∀ e : E(K),
      K.IsLink e.1 x.1 y.1 → K.Inc e.1 x.1 → K.Adj x.1 y.1) :
    ∀ x y : V(G), ∀ e : E(G),
      G.IsLink e.1 x.1 y.1 → G.Inc e.1 x.1 → G.Adj x.1 y.1 := by
  irw (i.comp j)
  exact h

example (i : Graph.Iso G H) (j : Graph.Iso H K)
    (h : ∀ x y : V(G), ∀ e : E(G), G.IsLink e.1 x.1 y.1 → G.Inc e.1 x.1) :
    ∀ x y : V(K), ∀ e : E(K), K.IsLink e.1 x.1 y.1 → K.Inc e.1 x.1 := by
  have h' := h
  irw i at h'
  irw j at h'
  exact h'

example (i : Graph.Iso G H)
    (h : ∀ x y : V(G), ∀ e : E(G), G.IsLink e.1 x.1 y.1 → G.Inc e.1 x.1) :
    ∀ x y : V(G), ∀ e : E(G), G.IsLink e.1 x.1 y.1 → G.Inc e.1 x.1 := by
  have h' := h
  irw i at h'
  irw i.symm at h'
  exact h'

example (h : G.Loopless → ∀ x y : V(G), G.Adj x.1 y.1 → x ≠ y) :
    G.Loopless → ∀ x y : V(G), G.Adj x.1 y.1 → x ≠ y := by
  have h' := h
  irw (Graph.Iso.id G) at h'
  exact h'

example (i : Graph.Iso G H) (x y : V(G)) (e : E(G))
    (ha : G.Adj x.1 y.1) (hi : G.Inc e.1 x.1) :
    G.Adj x.1 y.1 ∧ G.Inc e.1 x.1 := by
  irw i at ha hi ⊢
  exact ⟨ha, hi⟩

/-! ## The supplied iso may come from a graph construction -/

example (i : Graph.Iso G H)
    (h : ∀ f : V(H) → V(H), ∀ x : V(H), f x = x → H.Adj x.1 x.1) :
    ∀ f : V(G) → V(G), ∀ x : V(G), f x = x → G.Adj x.1 x.1 := by
  irw i
  exact h

/-- Exact instantiated domain matches must outrank merely definitionally equal ones.  Here the
active vertex and edge types are definitionally the same subtype, but the relabeling uses different
maps for the two roles. -/
def roleCollisionGraph {γ : Type uV} (u v : γ) : Graph γ γ :=
  Graph.banana u v ({u, v} : Set γ)

example {γ : Type uV} (u v : γ)
    (fv : V(roleCollisionGraph u v) ↪ V') (fe : E(roleCollisionGraph u v) ↪ E')
    (h : ∀ e : E((roleCollisionGraph u v).relabel fv fe),
      ∃ x : V((roleCollisionGraph u v).relabel fv fe),
        ((roleCollisionGraph u v).relabel fv fe).Inc e.1 x.1) :
    ∀ e : E(roleCollisionGraph u v),
      ∃ x : V(roleCollisionGraph u v), (roleCollisionGraph u v).Inc e.1 x.1 := by
  irw ((roleCollisionGraph u v).relabelIso fv fe)
  exact h

-- Without any role-bearing use of the raw carrier, both supported domains remain genuinely
-- possible; the resolver must retain its ambiguity diagnostic rather than choose by declaration
-- order.
example {γ : Type uV} (u v : γ)
    (_fv : V(roleCollisionGraph u v) ↪ V') (_fe : E(roleCollisionGraph u v) ↪ E') :
    ∀ _x : γ, True := by
  fail_if_success irw ((roleCollisionGraph u v).relabelIso _fv _fe)
  exact fun _ => True.intro

-- Ambient binders have the same raw carrier here, so their graph role must be inferred from the
-- later incidence atom rather than from the binder type alone.
example {γ : Type uV} (u v : γ)
    (fv : V(roleCollisionGraph u v) ↪ V') (fe : E(roleCollisionGraph u v) ↪ E')
    (h : ∀ e : E', ∀ x : V',
      ((roleCollisionGraph u v).relabel fv fe).Inc e x →
        ((roleCollisionGraph u v).relabel fv fe).Inc e x) :
    ∀ e : γ, ∀ x : γ,
      (roleCollisionGraph u v).Inc e x → (roleCollisionGraph u v).Inc e x := by
  irw ((roleCollisionGraph u v).relabelIso fv fe)
  exact h

-- example (fv : V(G) ↪ V') (fe : E(G) ↪ E')
--     (h : (G.relabel fv fe).Loopless) : G.Loopless := by
--   irw (G.relabelIso fv fe)
--   exact h

-- example (fv : V(G) ↪ V') (fe : E(G) ↪ E')
--     (h : ∀ x y : V(G.relabel fv fe), ∀ e : E(G.relabel fv fe),
--       (G.relabel fv fe).IsLink e.1 x.1 y.1 → (G.relabel fv fe).Adj x.1 y.1) :
--     ∀ x y : V(G), ∀ e : E(G), G.IsLink e.1 x.1 y.1 → G.Adj x.1 y.1 := by
--   irw (G.relabelIso fv fe)
--   exact h

end GraphIRwTests

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/



open Set
open scoped Cardinal

namespace IRwEquivTests

universe u v
variable {α γ : Type u} {β : Type v}

example (e : α ≃ β)
    (h : ∀ f : β → β, ∀ S : Set β, ∀ x : β,
      f x ∈ S → f (f x) = x) :
    ∀ f : α → α, ∀ S : Set α, ∀ x : α,
      f x ∈ S → f (f x) = x := by
  irw e
  exact h

example (e : α ≃ β)
    (h : ∀ p : β × Option β, p.2 = none ∨ ∃ x, p.2 = some x) :
    ∀ p : α × Option α, p.2 = none ∨ ∃ x, p.2 = some x := by
  irw e
  exact h

example (e : α ≃ β)
    (h : ∀ S : Set (Set β), ∀ T : Set β, T ∈ S → T ⊆ T) :
    ∀ S : Set (Set α), ∀ T : Set α, T ∈ S → T ⊆ T := by
  irw e
  exact h

example (e : α ≃ β)
    (h : ∃ f : β → β, ∀ x, f (f x) = x) :
    ∃ f : α → α, ∀ x, f (f x) = x := by
  irw e
  exact h

example (e : α ≃ γ) (c : Cardinal) (h : #γ = c) : #α = c := by
  irw e
  exact h

/-! ## Context-sensitive nested binders -/

example (e : α ≃ β)
    (h : ∀ x : β, ∀ f : β → β, ∀ S : Set β,
      f x ∈ S → ∃ y : β, y = f x ∧ y ∈ S) :
    ∀ x : α, ∀ f : α → α, ∀ S : Set α,
      f x ∈ S → ∃ y : α, y = f x ∧ y ∈ S := by
  irw e
  exact h

example (e : α ≃ β)
    (h : ∀ f g : β → β, f = g ↔ ∀ x, f x = g x) :
    ∀ f g : α → α, f = g ↔ ∀ x, f x = g x := by
  irw e
  exact h

example (e : α ≃ β)
    (h : ∀ p : (β → β) × Set β, ∀ x : β,
      p.1 x ∈ p.2 → p.1 (p.1 x) = x) :
    ∀ p : (α → α) × Set α, ∀ x : α,
      p.1 x ∈ p.2 → p.1 (p.1 x) = x := by
  irw e
  exact h

/-! ## Forward constructor cleanup for structural equivalences -/

example (e : α ≃ β) (Fixed : Prop)
    (h : ∀ F : Option (β → β), F = some (fun x => x) → Fixed) :
    ∀ F : Option (α → α), F = some (fun x => x) → Fixed := by
  irw e
  exact h

example (e : α ≃ β) (Fixed : Prop)
    (h : ∀ p q : β × β, q = (p.1, p.2) → Fixed) :
    ∀ p q : α × α, q = (p.1, p.2) → Fixed := by
  irw e
  exact h

example (e : α ≃ β) (Fixed : Prop)
    (h : ∀ s : β ⊕ β, ∀ x y : β, (s = Sum.inl x ∨ s = Sum.inr y) → Fixed) :
    ∀ s : α ⊕ α, ∀ x y : α, (s = Sum.inl x ∨ s = Sum.inr y) → Fixed := by
  irw e
  exact h

end IRwEquivTests




open Set

/-!
# `irw` former frontier tests

These adversarial examples drove extensions of the generic transport architecture. They now form
part of the expected-pass regression suite.
-/

namespace IRwFrontier

open Graph

universe uα uβ uV uE uV' uE'

/-! ## 1. Opaque object-independent atoms

A proposition parameter `P` stays fixed because neither it nor the types of its free variables
depend on the source graph. This does not provide a general unmatched-atom escape hatch: opaque
atoms that depend on the source object remain errors.
-/

example {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Graph.Iso G H) (P : Prop)
    (h : P → H.Loopless) : P → G.Loopless := by
  irw i
  exact h

example {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (_i : Graph.Iso G H)
    (Q : Graph V E → Prop) (h : Q G) : Q G := by
  fail_if_success irw _i
  exact h

/-! ## 2. Dependent ambient bounds

`B ⊆ A` is a perfectly natural second-stage bound once `A ⊆ M.E` is known.  This probe graduated
when supported domains gained structural `Set` closure, subset-preserving transport, and local
support search under implication antecedents.
-/

example {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β} (i : M ≂ N)
    (h : ∀ A B : Set β, A ⊆ N.E → B ⊆ A → N.Indep B → N.Spanning A) :
    ∀ A B : Set α, A ⊆ M.E → B ⊆ A → M.Indep B → M.Spanning A := by
  irw i
  exact h

/-! ## 3. Batched existential guards

The existential reassociation layer moves each guard next to its witness, reuses ordinary bounded
existential transport, and restores the original batched target shape.
-/

example {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β} (i : M ≂ N)
    (h : ∃ A B : Set β, A ⊆ N.E ∧ B ⊆ N.E ∧ N.Indep A ∧ N.Dep B) :
    ∃ A B : Set α, A ⊆ M.E ∧ B ⊆ M.E ∧ M.Indep A ∧ M.Dep B := by
  irw i
  exact h

example {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β} (i : M ≂ N)
    (h : ∃ A B C : Set β, A ⊆ N.E ∧ B ⊆ N.E ∧ C ⊆ N.E ∧
      N.Indep A ∧ N.Dep B ∧ N.Spanning C) :
    ∃ A B C : Set α, A ⊆ M.E ∧ B ⊆ M.E ∧ C ⊆ M.E ∧
      M.Indep A ∧ M.Dep B ∧ M.Spanning C := by
  irw i
  exact h

/-! ## 4. Function-valued binder types

`deriveEquiv` now closes structurally under Arrow using `Equiv.arrowCongr`. This test is retained to
guard the accompanying application-coherence normalization.
-/

example {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Graph.Iso G H)
    (h : ∀ f : V(H) → V(H), ∀ x : V(H), f x = x → H.Adj x.1 x.1) :
    ∀ f : V(G) → V(G), ∀ x : V(G), f x = x → G.Adj x.1 x.1 := by
  irw i
  exact h

/-! ## 5. Graph role ambiguity when `V(G)` and `E(G)` are definitionally the same type

This is the most important adversarial Graph test.  `banana u v {u,v}` has the same defining set
for its vertex and edge subtypes when the ambient vertex and edge carrier is the same type.  Its
`relabelIso` may nevertheless use *different* embeddings for vertices and edges.  A binder's type
alone then cannot tell `deriveEquiv` which equivalence is intended; its usage in `Inc`/`IsLink`
carries the role information.

Exact instantiated matches now distinguish the written `E(G)` and `V(G)` heads before falling back
to definitional equality, so this test passes. If elaboration later erases that syntax or this test
regresses, the engine may still need role-sensitive/backtracking binder transport.
-/

def G {γ : Type uV} (u v : γ) : Graph γ γ := Graph.banana u v ({u, v} : Set γ)

example {γ : Type uV} {V' : Type uV'} {E' : Type uE'} (u v : γ)
    (fv : V(G u v) ↪ V') (fe : E(G u v) ↪ E') (h : ∀ e : E((G u v).relabel fv fe),
    ∃ x : V((G u v).relabel fv fe), ((G u v).relabel fv fe).Inc e.1 x.1) :
    ∀ e : E(G u v), ∃ x : V(G u v), (G u v).Inc e.1 x.1 := by
  irw ((G u v).relabelIso fv fe)
  exact h

end IRwFrontier

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/



open Set Graph

namespace IRwLocalityTests

universe uα uβ uV uE uV' uE'

/-! These tests intentionally avoid the Graph/Matroid Mathlib-registration adapters. They verify
that project-owned systems, equivalences, domains, and naturality laws are active from the ordinary
modules containing their definitions. -/

example {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
    {G : Graph V E} {H : Graph V' E'} (i : Graph.Iso G H)
    (h : ∀ P : H.Path, P.first = P.last) : ∀ P : G.Path, P.first = P.last := by
  irw i
  exact h

example {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β} (i : M ≂ N)
    (h : ∀ x y : N.E, x = y → y = x) : ∀ x y : M.E, x = y → y = x := by
  irw i
  exact h

example {α : Type uα} {β : Type uβ} {M : Matroid α} {N : Matroid β} (i : M ≂ N)
    (h : ∀ X Y : {X : Set β // X ⊆ N.E}, X = Y → Y = X) :
    ∀ X Y : {X : Set α // X ⊆ M.E}, X = Y → Y = X := by
  irw i
  exact h

end IRwLocalityTests

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/



namespace IRwNaturalityTests

universe u v

/-- A synthetic dependent datum used to test canonical normalization independently of Graph. -/
structure Foo (α : Type u) where
  head : α

/-- Mechanical transport for the synthetic family. -/
def fooEquiv {α : Type u} {β : Type v} (e : α ≃ β) : Foo α ≃ Foo β where
  toFun x := ⟨e x.head⟩
  invFun y := ⟨e.symm y.head⟩
  left_inv x := by simp
  right_inv y := by simp

/-- `Foo` is a total domain for an ordinary equivalence. -/
@[irw_domain]
def Equiv.irw_fooDomain {α : Type u} {β : Type v} (e : α ≃ β) :
    IRw.TotalDomain (Foo α) (Foo β) :=
  ⟨fooEquiv e⟩

/-- Canonical target syntax for the head of a mechanically transported `Foo`. -/
@[irw_naturality]
theorem fooEquiv_head {α : Type u} {β : Type v} (e : α ≃ β) (y : Foo β) :
    (IRw.Equiv.irw_domain e) ((Equiv.irw_fooDomain e).equiv.symm y).head = y.head := by
  simp [IRw.Equiv.irw_domain, Equiv.irw_fooDomain, fooEquiv]

example {α : Type u} {β : Type v} (e : α ≃ β)
    (h : ∀ x y : Foo β, x.head = y.head) :
    ∀ x y : Foo α, x.head = y.head := by
  irw e
  exact h

/-! ## Explicit priority is an expert escape hatch

Exact matching still outranks definitional matching. Within one match class, a higher-priority
registration wins independently of declaration order. Ordinary registrations should omit it. -/

def SourcePred {α : Type u} (_ : α) : Prop := True
def LowTargetPred {β : Type v} (_ : β) : Prop := True
def HighTargetPred {β : Type v} (_ : β) : Prop := True

@[irw_naturality high]
theorem sourcePred_high {α : Type u} {β : Type v} (e : α ≃ β) (x : α) :
    SourcePred x ↔ HighTargetPred (e x) := by simp [SourcePred, HighTargetPred]

-- Deliberately declared later: priority, not import/declaration order, selects the rule above.
@[irw_naturality low]
theorem sourcePred_low {α : Type u} {β : Type v} (e : α ≃ β) (x : α) :
    SourcePred x ↔ LowTargetPred (e x) := by simp [SourcePred, LowTargetPred]

example {α : Type u} {β : Type v} (e : α ≃ β)
    (h : ∀ y : β, HighTargetPred y) : ∀ x : α, SourcePred x := by
  irw e
  exact h

def GenericSourcePred {α : Type u} (_ : α) : Prop := True
def ExactSourcePred {α : Type u} (x : α) : Prop := GenericSourcePred x
def HighGenericTargetPred {β : Type v} (_ : β) : Prop := True
def LowExactTargetPred {β : Type v} (_ : β) : Prop := True

@[irw_naturality high]
theorem genericSourcePred_high {α : Type u} {β : Type v} (e : α ≃ β) (x : α) :
    GenericSourcePred x ↔ HighGenericTargetPred (e x) := by
  simp [GenericSourcePred, HighGenericTargetPred]

@[irw_naturality low]
theorem exactSourcePred_low {α : Type u} {β : Type v} (e : α ≃ β) (x : α) :
    ExactSourcePred x ↔ LowExactTargetPred (e x) := by
  simp [ExactSourcePred, GenericSourcePred, LowExactTargetPred]

-- Exact matching is a stronger signal than priority: the specific low-priority rule wins.
example {α : Type u} {β : Type v} (e : α ≃ β)
    (h : ∀ y : β, LowExactTargetPred y) : ∀ x : α, ExactSourcePred x := by
  irw e
  exact h

inductive AmbiguousSource {α : Type u} (_ : α) : Prop
  | intro

inductive FirstTarget {β : Type v} (_ : β) : Prop
  | intro

inductive SecondTarget {β : Type v} (_ : β) : Prop
  | intro

@[irw_naturality]
theorem ambiguous_first {α : Type u} {β : Type v} (e : α ≃ β) (x : α) :
    AmbiguousSource x ↔ FirstTarget (e x) :=
  ⟨fun _ ↦ .intro, fun _ ↦ .intro⟩

/--
error: @[irw_naturality] rule `IRwNaturalityTests.ambiguous_second` overlaps
`IRwNaturalityTests.ambiguous_first` at priority 1000, but they produce different canonical forms.
Use one canonical primitive rule, or give the genuinely more specific rule a higher priority.
-/
#guard_msgs (whitespace := lax) in
@[irw_naturality]
theorem ambiguous_second {α : Type u} {β : Type v} (e : α ≃ β) (x : α) :
    AmbiguousSource x ↔ SecondTarget (e x) :=
  ⟨fun _ ↦ .intro, fun _ ↦ .intro⟩

end IRwNaturalityTests

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/



namespace GraphIRwPathTests

open Graph

universe uV uE uV' uE' uC

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {G : Graph V E} {H : Graph V' E'}

/-! ## Canonical endpoint syntax -/

example (i : Graph.Iso G H)
    (h : ∀ P : H.Path, P.first = P.last) :
    ∀ P : G.Path, P.first = P.last := by
  irw i
  exact h

example (i : Graph.Iso G H)
    (h : ∀ P Q : H.Path, P.reverse.first = Q.last) :
    ∀ P Q : G.Path, P.reverse.first = Q.last := by
  irw i
  exact h

example (i : Graph.Iso G H)
    (h : ∀ P Q : H.Path, P.vertexSet ⊆ Q.vertexSet → P.edgeSet = Q.edgeSet) :
    ∀ P Q : G.Path, P.vertexSet ⊆ Q.vertexSet → P.edgeSet = Q.edgeSet := by
  irw i
  exact h

/-! ## Arbitrary transported functions -/

example {Color : Type uC} (red : Color) (i : Graph.Iso G H)
    (h : ∀ c : V(H) → Color, ∀ P : H.Path, c P.first = red) :
    ∀ c : V(G) → Color, ∀ P : G.Path, c P.first = red := by
  irw i
  exact h

example (i : Graph.Iso G H)
    (h : ∀ f : H.Path → V(H), ∀ P : H.Path, f P = P.first) :
    ∀ f : G.Path → V(G), ∀ P : G.Path, f P = P.first := by
  irw i
  exact h

end GraphIRwPathTests

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/



namespace IRwPriorityTests

universe u v

/-! The domain and equivalence priority registries are tested here. The higher-priority
declaration is deliberately written first, so success cannot be explained by a
last-registration-wins policy. -/

structure EquivSource (α : Type u) where
  val : α

structure EquivHighTarget (β : Type v) where
  val : β

structure EquivLowTarget (β : Type v) where
  val : β

@[irw_equiv high]
def Equiv.priorityHighEquiv {α : Type u} {β : Type v} (e : α ≃ β) :
    EquivSource α ≃ EquivHighTarget β where
  toFun x := ⟨e x.val⟩
  invFun y := ⟨e.symm y.val⟩
  left_inv x := by cases x; simp
  right_inv y := by cases y; simp

@[irw_equiv low]
def Equiv.priorityLowEquiv {α : Type u} {β : Type v} (e : α ≃ β) :
    EquivSource α ≃ EquivLowTarget β where
  toFun x := ⟨e x.val⟩
  invFun y := ⟨e.symm y.val⟩
  left_inv x := by cases x; simp
  right_inv y := by cases y; simp

example {α : Type u} {β : Type v} (e : α ≃ β)
    (h : ∀ x y : EquivHighTarget β, x = y → y = x) :
    ∀ x y : EquivSource α, x = y → y = x := by
  irw e
  exact h

structure DomainSource (α : Type u) where
  val : α

structure DomainHighTarget (β : Type v) where
  val : β

structure DomainLowTarget (β : Type v) where
  val : β

def domainHighEquiv {α : Type u} {β : Type v} (e : α ≃ β) :
    DomainSource α ≃ DomainHighTarget β where
  toFun x := ⟨e x.val⟩
  invFun y := ⟨e.symm y.val⟩
  left_inv x := by cases x; simp
  right_inv y := by cases y; simp

def domainLowEquiv {α : Type u} {β : Type v} (e : α ≃ β) :
    DomainSource α ≃ DomainLowTarget β where
  toFun x := ⟨e x.val⟩
  invFun y := ⟨e.symm y.val⟩
  left_inv x := by cases x; simp
  right_inv y := by cases y; simp

@[irw_domain high]
def Equiv.priorityHighDomain {α : Type u} {β : Type v} (e : α ≃ β) :
    IRw.TotalDomain (DomainSource α) (DomainHighTarget β) :=
  ⟨domainHighEquiv e⟩

@[irw_domain low]
def Equiv.priorityLowDomain {α : Type u} {β : Type v} (e : α ≃ β) :
    IRw.TotalDomain (DomainSource α) (DomainLowTarget β) :=
  ⟨domainLowEquiv e⟩

example {α : Type u} {β : Type v} (e : α ≃ β)
    (h : ∀ x y : DomainHighTarget β, x = y → y = x) :
    ∀ x y : DomainSource α, x = y → y = x := by
  irw e
  exact h

theorem transformation_not_first {α : Type u} {β : Type v} (x : α) (e : α ≃ β) :
    x = x ↔ e x = e x := by simp

/--
error: IRw registration `IRwPriorityTests.transformation_not_first` must take its Equiv
transformation as its first explicit argument
-/
#guard_msgs (whitespace := lax) in
attribute [irw_naturality] transformation_not_first

end IRwPriorityTests

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/



namespace IRwSupportedTests

universe u v

/-! ## Total-domain descriptor smoke test -/

structure WrappedEquiv (α : Type u) (β : Type v) where
  equiv : α ≃ β

attribute [irw_system] WrappedEquiv

@[irw_domain]
def WrappedEquiv.irw_domain {α : Type u} {β : Type v} (e : WrappedEquiv α β) :
    IRw.TotalDomain α β := ⟨e.equiv⟩

example {α : Type u} {β : Type v} (e : WrappedEquiv α β)
    (h : ∀ f : β → β, ∀ S : Set β, ∀ x : β,
      f x ∈ S → f (f x) = x) :
    ∀ f : α → α, ∀ S : Set α, ∀ x : α,
      f x ∈ S → f (f x) = x := by
  irw e
  exact h

/-! ## Supported-domain descriptor smoke tests -/

/-- Synthetic partial change of coordinates used to test the generic supported-domain core without
Graph or Matroid imports. -/
structure PartialEquiv (α : Type u) (β : Type v) where
  sourceSupport : α → Prop
  targetSupport : β → Prop
  equiv : {x // sourceSupport x} ≃ {y // targetSupport y}

attribute [irw_system] PartialEquiv

@[irw_domain]
def PartialEquiv.irw_domain {α : Type u} {β : Type v} (e : PartialEquiv α β) :
    IRw.SupportedDomain α β where
  sourceSupport := e.sourceSupport
  targetSupport := e.targetSupport
  equiv := e.equiv

@[irw_naturality]
theorem PartialEquiv.irw_support {α : Type u} {β : Type v} (e : PartialEquiv α β)
    (x : {x // e.sourceSupport x}) :
    e.sourceSupport x.1 ↔ e.targetSupport (e.irw_domain.equiv x).1 :=
  ⟨fun _ => (e.equiv x).2, fun _ => x.2⟩

/-! ## Restricted support automation -/

/-- An opaque evidence wrapper whose implication to support is intentionally available only to the
support-certificate solver. -/
inductive Covered {α : Type u} (S : α → Prop) (x : α) : Prop where
  | intro : S x → Covered S x

@[irw_support →]
theorem Covered.support {α : Type u} {S : α → Prop} {x : α} (h : Covered S x) : S x := by
  exact h.rec id

@[irw_naturality]
theorem PartialEquiv.irw_covered {α : Type u} {β : Type v} (e : PartialEquiv α β)
    (x : {x // e.sourceSupport x}) :
    Covered e.sourceSupport x.1 ↔
      Covered e.targetSupport (e.irw_domain.equiv x).1 :=
  ⟨fun _ => .intro (e.equiv x).2, fun _ => .intro x.2⟩

/-- This analogous wrapper is deliberately registered with ordinary `grind`, not `irw_support`,
to check that the support solver does not consume the global theorem database. -/
inductive GloballyCovered {α : Type u} (S : α → Prop) (x : α) : Prop where
  | intro : S x → GloballyCovered S x

@[grind →]
theorem GloballyCovered.support {α : Type u} {S : α → Prop} {x : α}
    (h : GloballyCovered S x) : S x := by
  exact h.rec id

@[irw_naturality]
theorem PartialEquiv.irw_globallyCovered {α : Type u} {β : Type v} (e : PartialEquiv α β)
    (x : {x // e.sourceSupport x}) :
    GloballyCovered e.sourceSupport x.1 ↔
      GloballyCovered e.targetSupport (e.irw_domain.equiv x).1 :=
  ⟨fun _ => .intro (e.equiv x).2, fun _ => .intro x.2⟩

variable {α : Type u} {β : Type v}

example (e : PartialEquiv α β)
    (h : ∀ y : β, e.targetSupport y → True) :
    ∀ _x : α, True := by
  irw e
  exact h

-- The hand-written prover cannot see through `Covered`; the restricted fallback uses the single
-- `@[irw_support]` rule and removes the inferred target guard again.
example (e : PartialEquiv α β)
    (h : ∀ y : β, Covered e.targetSupport y → e.targetSupport y) :
    ∀ x : α, Covered e.sourceSupport x → e.sourceSupport x := by
  irw e
  exact h

-- An unrelated antecedent may precede the evidence-producing hypothesis.
example (e : PartialEquiv α β)
    (h : ∀ y : β, True → Covered e.targetSupport y → e.targetSupport y) :
    ∀ x : α, True → Covered e.sourceSupport x → e.sourceSupport x := by
  irw e
  exact h

-- Logical branching is handled by the same certificate backend, independently of adjacency.
example (e : PartialEquiv α β)
    (h : ∀ y : β, e.targetSupport y →
      (Covered e.targetSupport y → e.targetSupport y) ∨
      (Covered e.targetSupport y → e.targetSupport y)) :
    ∀ x : α,
      (Covered e.sourceSupport x → e.sourceSupport x) ∨
      (Covered e.sourceSupport x → e.sourceSupport x) := by
  irw e
  exact h

example (e : PartialEquiv α β)
    (h : ∃ y : β, e.targetSupport y ∧
      (Covered e.targetSupport y ∨ Covered e.targetSupport y)) :
    ∃ x : α, Covered e.sourceSupport x ∨ Covered e.sourceSupport x := by
  irw e
  exact h

-- An ordinary global `@[grind]` theorem is intentionally invisible to support search.
example (e : PartialEquiv α β) :
    ∀ x : α, GloballyCovered e.sourceSupport x → e.sourceSupport x := by
  fail_if_success irw e
  intro x hx
  exact hx.support

example (e : PartialEquiv α β)
    (h : ∀ y : β, e.targetSupport y → e.targetSupport y → True) :
    ∀ x : α, e.sourceSupport x → True := by
  irw e
  exact h

example (e : PartialEquiv α β)
    (h : ∃ y : β, e.targetSupport y ∧ e.targetSupport y) :
    ∃ x : α, e.sourceSupport x := by
  irw e
  exact h

example (e : PartialEquiv α β)
    (h : ∃ y : β, e.targetSupport y ∧ (True ∧ e.targetSupport y)) :
    ∃ x : α, True ∧ e.sourceSupport x := by
  irw e
  exact h

end IRwSupportedTests

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/



open Set Graph

namespace GraphIRwWalkTests

universe uV uE uV' uE'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {G : Graph V E} {H : Graph V' E'}

/-! ## Raw walk lists supported by `IsWalk` -/

-- These expressions deliberately need no naturality theorem yet: equality transports the
-- mechanically produced data, whatever its eventual canonical target-side spelling will be.
example (i : Graph.Iso G H) :
    ∀ W : WList V E, G.IsWalk W →
      W = W ∧ W.first = W.first ∧ W.last = W.last ∧
        W.edge = W.edge ∧ W.vertex = W.vertex := by
  irw i
  simp

/-! ## Stronger predicates as support certificates -/

example (i : Graph.Iso G H) :
    ∀ W : WList V E, G.IsTrail W → W = W := by
  irw i
  simp

example (i : Graph.Iso G H) :
    ∀ W : WList V E, G.IsPath W → W.first = W.first := by
  irw i
  simp

example (i : Graph.Iso G H) :
    ∀ W : WList V E, G.IsTour W → W.edge = W.edge := by
  irw i
  simp

-- `IsCyclicWalk` is deliberately separated from the binder by unrelated positive implications.
-- The supported-domain solver must discover `IsWalk W` before it can transport the raw binder.
example (i : Graph.Iso G H) (v : V) (hv : v ∈ V(G))
    (h : ∀ W : WList V' E', H.IsCyclicWalk W → W.last = (i.vertexEquiv ⟨v, hv⟩).1) :
    ∀ W : WList V E, G.IsCyclicWalk W → W.last = v := by
  irw i
  exact h

-- The stronger graph predicate itself also has to land in the canonical target vocabulary.
example (i : Graph.Iso G H)
    (h : ∀ W : WList V' E', H.IsCyclicWalk W → H.IsCyclicWalk W) :
    ∀ W : WList V E, G.IsCyclicWalk W → G.IsCyclicWalk W := by
  irw i
  exact h

end GraphIRwWalkTests
