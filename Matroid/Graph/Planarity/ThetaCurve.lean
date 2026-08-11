import Matroid.Graph.Planarity.StarLemma
import Matroid.ForMathlib.Geometry.Polygon.JordanCurve

/-!
# The θ-curve theorem and its corollaries

Status.md 3.9–3.11. Three arcs sharing exactly their two endpoints cut the sphere into three
regions; a crosscut cuts a face in two; and two disjoint crosscuts of the same face cannot have
interleaved endpoints.

These are the statements §§4–6 run on. Every step that adds an ear to a subgraph, splits a face, or
rules out a configuration is one of the three below. In particular 3.11 is what turns a planar
drawing into the combinatorial dichotomy of §8: two crosscuts of a face whose endpoints alternate
around it are impossible, which is exactly the alternating quadruple that produces a `K₃,₃`.

Unlike the star lemma, these need the Jordan curve theorem — but only its polygonal case, and only
through `PolygonalPath.IsSimpleLoop.exists_sides_onePoint`. 3.9 also needs the star lemma, applied
to the θ-graph: `Θ` is the support of a polygonal drawing of the theta graph, so 3.5–3.8 apply to
it, which is how "at most three" is proved without any further topology.

Everything is on the sphere. On `𝕊` the three regions of a θ-curve are interchangeable; in the
plane one of them would be the unbounded one and every statement would need a case for it.

## Main statements

* `exists_three_regions_theta` : Status.md 3.9.
* `exists_two_regions_crosscut` : Status.md 3.10.
* `not_alternating_crosscut` : Status.md 3.11.
-/

open Function Set Topology

namespace Graph

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊" => OnePoint (EuclideanSpace ℝ (Fin 2))

variable {a b s t s₁ s₂ t₁ t₂ : ℝ²}

/-! ### 3.9, the θ-curve theorem -/

/- **Handoff to formalisation helper** (Status.md 3.9).

Tactic wizard attempted the Status.md route and got stuck on scaffolding, not on a missing lemma
name.

**What works without new API.** For each omitted index `i`, the complementary pair of arcs forms a
simple loop (`isSimpleLoop_append_iff` + `reverse`), and `IsSimpleLoop.exists_sides_onePoint`
supplies two open connected sides with frontier the loop. Picking the side that does *not* contain
`relint (A i)` gives three candidate regions `W i` that are open, connected, pairwise disjoint (shared
point ⇒ same `Θᶜ`-component ⇒ equal frontiers, but `relint (A i)` meets `frontier (W j)` and misses
`frontier (W i)`), and have the stated frontiers. That is the "at least three" half.

**Where it breaks — the cover `⋃ᵢ W i = ((↑) '' Θ)ᶜ`.** Status.md finishes via the star lemma on a
polygonal drawing of the θ-graph: at an endpoint, `ball ∩ Θ` is three radii; sectors inject into
faces of `Θᶜ`; every component meets a sector, so there are at most three components, identified
with the `W i`. That needs either

1. a named bridge `PLDrawing` of `Graph.banana` (two vertices, three edges) from the three arcs via
   `PLDrawing.ofCells`, including orientation/`edgeSource` alignment and the disjointness
   hypotheses, then `exists_radius` / `facesAt` / `ncard_sectors_closure_eq_two`; or
2. an inline graph-free lemma that a union of three simple arcs meeting only at `{a,b}` is a
   three-radius star near `a` (and near `b`), packaged for `DiskMinusRadii.sectors`.

Neither exists. Building (1) or (2) in situ is statement-design / scaffolding scale (≫2× the
intended fill), not a tactic discharge. 3.10–3.11 are Status.md corollaries of 3.9 and inherit the
same blocker.

Also upstream: `IsJordanCurve.exists_sides` / `exists_sides_onePoint` are still `sorry` (allowed
topological input); polygonal specialisations call them.

Escalate: provide the θ-drawing (or graph-free three-radius) bridge, then tactic can finish 3.9–3.11
along Status.md. -/

/-- **The θ-curve theorem.** Three embedded polygonal arcs with the same two endpoints, meeting
nowhere else, cut the sphere into exactly three regions. The region omitted by index `i` is bounded
by the other two arcs.

"Exactly three" is expressed by exhibiting three regions that are open, connected, pairwise
disjoint, and cover the complement: such a family is precisely the set of connected components.
Their frontiers are pairwise distinct, so no two of them coincide. -/
theorem exists_three_regions_theta (hab : a ≠ b) (A : Fin 3 → PolygonalPath a b)
    (hsimple : ∀ i, (A i).IsSimple)
    (hmeet : ∀ i j, i ≠ j → (A i).toSet ∩ (A j).toSet = {a, b}) :
    ∃ W : Fin 3 → Set 𝕊,
      (∀ i, IsOpen (W i)) ∧ (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (⋃ i, W i) = ((↑) '' ⋃ i, (A i).toSet)ᶜ ∧
      ∀ i, frontier (W i) = (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), (A j).toSet := by
  sorry

/-! ### 3.10, cutting a face with a crosscut -/

/-- **Crosscut.** A polygon `J` bounds two regions; an embedded arc across one of them, meeting `J`
exactly at its own two endpoints, cuts that region into two, each bounded by the arc together with
one of the two arcs into which its endpoints divide `J`.

The two arcs of `J` are produced rather than assumed, since `Polygon.IsSimple.exists_arcs` supplies
them at any two points of the boundary; a caller that already has them can rewrite. -/
theorem exists_two_regions_crosscut {n : ℕ} {p : Polygon ℝ² n} (hp : p.IsSimple ℝ)
    {F : Set 𝕊} {q : 𝕊} (hq : q ∈ ((↑) '' p.boundary ℝ)ᶜ)
    (hF : F = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ q)
    (hst : s ≠ t) (hs : s ∈ p.boundary ℝ) (ht : t ∈ p.boundary ℝ)
    (A : PolygonalPath s t) (hA : A.IsSimple) (hAJ : A.toSet ∩ p.boundary ℝ = {s, t})
    (hAF : (↑) '' (A.toSet \ {s, t}) ⊆ F) :
    ∃ (J₁ : PolygonalPath s t) (J₂ : PolygonalPath t s) (W₁ W₂ : Set 𝕊),
      J₁.IsSimple ∧ J₂.IsSimple ∧ J₁.toSet ∩ J₂.toSet = {s, t} ∧
      J₁.toSet ∪ J₂.toSet = p.boundary ℝ ∧
      IsOpen W₁ ∧ IsOpen W₂ ∧ IsConnected W₁ ∧ IsConnected W₂ ∧ Disjoint W₁ W₂ ∧
      W₁ ∪ W₂ = F \ ((↑) '' A.toSet) ∧
      frontier W₁ = (↑) '' (J₁.toSet ∪ A.toSet) ∧
      frontier W₂ = (↑) '' (J₂.toSet ∪ A.toSet) := by
  sorry

/-! ### 3.11, crosscuts do not alternate -/

/-- **Two disjoint crosscuts of the same region cannot interleave.** If `A` and `B` are disjoint
embedded arcs across the same region of a polygon, with endpoints on the polygon, then the endpoints
of `B` do not lie on opposite sides of `A`: they cannot be separated by `A`'s endpoints along `J`.

Separation is expressed through the two arcs `J₁, J₂` into which `A`'s endpoints cut `J`, which is
the form §8 uses to produce an alternating quadruple. -/
theorem not_alternating_crosscut {n : ℕ} {p : Polygon ℝ² n} (hp : p.IsSimple ℝ)
    {F : Set 𝕊} {q : 𝕊} (hq : q ∈ ((↑) '' p.boundary ℝ)ᶜ)
    (hF : F = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ q)
    (A : PolygonalPath s₁ s₂) (B : PolygonalPath t₁ t₂) (hA : A.IsSimple) (hB : B.IsSimple)
    (hAB : Disjoint A.toSet B.toSet)
    (hAJ : A.toSet ∩ p.boundary ℝ = {s₁, s₂}) (hBJ : B.toSet ∩ p.boundary ℝ = {t₁, t₂})
    (hAF : (↑) '' (A.toSet \ {s₁, s₂}) ⊆ F) (hBF : (↑) '' (B.toSet \ {t₁, t₂}) ⊆ F)
    (J₁ : PolygonalPath s₁ s₂) (J₂ : PolygonalPath s₂ s₁)
    (hJ₁ : J₁.IsSimple) (hJ₂ : J₂.IsSimple) (hJmeet : J₁.toSet ∩ J₂.toSet = {s₁, s₂})
    (hJcover : J₁.toSet ∪ J₂.toSet = p.boundary ℝ) :
    ¬ (t₁ ∈ J₁.toSet \ {s₁, s₂} ∧ t₂ ∈ J₂.toSet \ {s₁, s₂}) := by
  sorry

end

end Graph
