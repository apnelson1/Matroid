import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Logic.Equiv.PartialEquiv

variable {α β γ : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F : Set β} {S T : Set α}

open Set

namespace Graph

-- class isHalfEdge (G : Graph α β) (γ : Type*) where
--   halfEdgeSet : Set γ
--   link : γ → γ
--   link_invol : ∀ ⦃d⦄, link (link d) = d
--   link_ne : ∀ ⦃d⦄, d ∈ halfEdgeSet → link d ≠ d
--   link_mem : ∀ ⦃d⦄, d ∈ halfEdgeSet → link d ∈ halfEdgeSet
--   toEdge : γ → β
--   toEdge_link : ∀ ⦃d⦄, d ∈ halfEdgeSet → toEdge (link d) = toEdge d
--   basePt : γ → α
--   basePt_isLoopAt : ∀ ⦃d⦄, d ∈ halfEdgeSet → basePt (link d) = basePt d →
--     G.IsLoopAt (toEdge d) (basePt d)
--   isLink_toEdge_basePt : ∀ ⦃d⦄, d ∈ halfEdgeSet →
--     G.IsLink (toEdge d) (basePt d) (basePt (link d))

structure Orientation (G : Graph α β) where
  dInc : β → α → α → Prop
  dInc_antisymm : ∀ ⦃e u v⦄, dInc e u v → dInc e v u → u = v
  symm_dInc_iff_isLink : ∀ ⦃e u v⦄, dInc e u v ∨ dInc e v u ↔ G.IsLink e u v

-- inductive Orientation.Dart (D : Orientation G) : α → α → Type _
--   | forward {u v} (e) (h : D.dInc e u v) : D.Dart u v
--   | backward {u v} (e) (h : D.dInc e u v) : D.Dart v u

variable {D D₁ : Orientation G}

lemma Orientation.dInc.isLink (h : D.dInc e u v) : G.IsLink e u v := by
  rw [← D.symm_dInc_iff_isLink]
  tauto

lemma Orientation.compare (h : D₁.dInc e u v) (D₂ : Orientation G) :
    D₂.dInc e u v ∨ D₂.dInc e v u := D₂.symm_dInc_iff_isLink.mpr h.isLink

-- noncomputable def Orientation.Dart.changeOrientation {u v} (D₁ D₂ : Orientation G) :
--     D₁.Dart u v → D₂.Dart u v
--   | forward e h =>
--     letI : Decidable (D₂.dInc e u v) := Classical.propDecidable _
--     if h' : D₂.dInc e u v -- In the case `u = v`, prefer `forward`.
--     then Dart.forward e h'
--     else Dart.backward e (D₁.compare h D₂ |>.resolve_left h')
--   | backward e h =>
--     letI : Decidable (D₂.dInc e v u) := Classical.propDecidable _
--     if h' : D₂.dInc e v u -- In the case `u = v`, prefer `backward`.
--     then Dart.backward e h'
--     else Dart.forward e (D₁.compare h D₂ |>.resolve_left h')

inductive Orientation.Walk (D : Orientation G) : α → α → Type _
  | nil {x : α} (hx : x ∈ V(G)) : D.Walk x x
  | forward {u} (e v) {w} (h : D.dInc e u v) (W : D.Walk v w) : D.Walk u w
  | backward {u} (e v) {w} (h : D.dInc e v u) (W : D.Walk v w) : D.Walk u w

noncomputable def Orientation.Walk.changeOrientation {u w} (D₁ D₂ : Orientation G) :
    D₁.Walk u w → D₂.Walk u w
  | nil hx => Walk.nil hx
  | forward e v h W =>
    letI : Decidable (D₂.dInc e u v) := Classical.propDecidable _
    if h' : D₂.dInc e u v
    then Walk.forward e v h' (W.changeOrientation D₁ D₂)
    else Walk.backward e v (D₁.compare h D₂ |>.resolve_left h') (W.changeOrientation D₁ D₂)
  | backward e v h W =>
    letI : Decidable (D₂.dInc e u v) := Classical.propDecidable _
    if h' : D₂.dInc e u v
    then Walk.forward e v h' (W.changeOrientation D₁ D₂)
    else Walk.backward e v (D₁.compare h D₂ |>.resolve_right h') (W.changeOrientation D₁ D₂)
