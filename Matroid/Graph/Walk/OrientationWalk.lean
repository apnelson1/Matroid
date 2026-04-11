import Mathlib.Combinatorics.Graph.Subgraph

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F : Set β} {S T : Set α}

open Set

namespace Graph

structure Orientation (G : Graph α β) where
  dInc : β → α → α → Prop
  dInc_asymm : ∀ ⦃e u v⦄, dInc e u v → dInc e v u → u = v
  symm_dInc_iff_isLink : ∀ ⦃e u v⦄, dInc e u v ∨ dInc e v u ↔ G.IsLink e u v

lemma Orientation.dInc.isLink {D : Orientation G} (h : D.dInc e u v) : G.IsLink e u v := by
  rw [← D.symm_dInc_iff_isLink]
  tauto

lemma Orientation.compare {D₁ : Orientation G} (h : D₁.dInc e u v) (D₂ : Orientation G) :
    D₂.dInc e u v ∨ D₂.dInc e v u := D₂.symm_dInc_iff_isLink.mpr h.isLink

inductive Orientation.Dart (D : Orientation G) : α → α → Type _
  | forward {u v} (e) (h : D.dInc e u v) : D.Dart u v
  | backward {u v} (e) (h : D.dInc e u v) : D.Dart v u

noncomputable def Orientation.Dart.changeOrientation {u v} (D₁ D₂ : Orientation G) :
    D₁.Dart u v → D₂.Dart u v
  | forward e h =>
    letI : Decidable (D₂.dInc e u v) := Classical.propDecidable _
    if h' : D₂.dInc e u v -- In the case `u = v`, prefer `forward`.
    then Dart.forward e h'
    else Dart.backward e (D₁.compare h D₂ |>.resolve_left h')
  | backward e h =>
    letI : Decidable (D₂.dInc e v u) := Classical.propDecidable _
    if h' : D₂.dInc e v u -- In the case `u = v`, prefer `backward`.
    then Dart.backward e h'
    else Dart.forward e (D₁.compare h D₂ |>.resolve_left h')

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

