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
to `Θ` itself: `Θ` is a union of three polygonal arcs, hence an `IsSegmentFigure`, which is all
3.5–3.8 ever needed. That is how "at most three" is proved without any further topology, and with
no drawing and no graph anywhere — see `Matroid/ForMathlib/Geometry/SegmentFigure.lean` and
Kuratowski `Decisions.md` D16.

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

/- **Proof route for `exists_three_regions_theta`** (formalisation helper).

The previous handoff offered two ways to reach the star lemma at `a`: manufacture a `PLDrawing` of
`Graph.banana`, or reprove the star inline. Both were dead ends — option 1 lands on
`exists_radius_vertex`, which is itself open, and then still owes a translation from banana faces
back to components of `Θᶜ`. The real obstruction was that `exists_radius` was stated about a drawing
when its proof needed only "finite union of segments". It is now stated about the latter, in
`Matroid/ForMathlib/Geometry/SegmentFigure.lean`, and a θ-curve qualifies directly. **No drawing and
no graph is needed anywhere in this file.**

*At least three.* Unchanged, and already working: for each omitted `i` the complementary pair of
arcs is a simple loop (`isSimpleLoop_append_iff` + `reverse`), and
`IsSimpleLoop.exists_sides_onePoint` gives two open connected sides with frontier the loop. Take the
side not containing `relint (A i)`. Pairwise disjointness: a shared point puts two of them in the
same component of `Θᶜ`, hence equal frontiers, but `relint (A i)` meets `frontier (W j)` for `j ≠ i`
and misses `frontier (W i)`.

*The cover `⋃ᵢ W i = ((↑) '' Θ)ᶜ`.* This is the half that was blocked. Now:

1. `Θ := ⋃ i, (A i).toSet` is a segment figure: `PolygonalPath.isSegmentFigure_toSet` on each arc,
   then `IsSegmentFigure.iUnion`.
2. `IsSegmentFigure.exists_radius` at `a` gives `ρ > 0` and `Y` with
   `closedBall a ρ ∩ Θ = {a} ∪ ⋃ y ∈ Y, segment ℝ a y`.
3. **Shrink `ρ` first.** `PolygonalPath.exists_ball_inter_subset_firstSegment` gives, for each arc,
   a radius below which that arc meets `closedBall a ·` in its first segment only; take `ρ'` the
   minimum of those three and of `ρ` and of `dist a b`. `exists_radius_of_le` transports the star
   to `ρ'` **with the same radius count**. This step is not optional: an arc may re-enter a fixed
   ball around `a`, so the bounds in step 4 are simply false at the `ρ` that `exists_radius`
   happens to return.
4. **`Y.card = 3`**, from the two bounds with `U i := (A i).toSet` and `ι := Fin 3`, at `ρ'`:
   * `le_card_radii_of_pairwise` — its `hmeet` is this file's `hmeet`, since `ρ' < dist a b` makes
     `{a, b} ∩ closedBall a ρ' = {a}`; its `hUp` is that each arc leaves `a` along its first
     segment, which step 3 already produced.
   * `card_radii_le_of_cover` — `hcover` is immediate from the definition of `Θ`, and `hUz` is
     exactly what step 3 arranged.
5. `ncard_sectors` then gives exactly three sectors of `ball a ρ' ∖ Θ`, each open and connected
   (`isOpen_of_mem_sectors`, `isConnected_of_mem_sectors`).
6. Each sector is connected and misses `Θ`, so lies in a single component of `((↑) '' Θ)ᶜ`. That
   sends the three sectors onto at most three components. `ncard_sectors_closure_eq_two` is
   Status.md 3.8 and supplies the pairing `Φ_i ⊆ {W_ij, W_ik}` verbatim.
7. Every component `W` of `((↑) '' Θ)ᶜ` has nonempty frontier contained in `Θ`; a frontier point
   lies in some `relint (A i)` or in `{a, b}`, and either way `W` contains a sector at `a` or at
   `b` (the construction at `b` is symmetric). So there are at most three components, and with
   *at least three* above they are exactly the `W i`.

Step 6 wants a graph-free `exists_sector_subset_component`: the current
`exists_sector_subset_faceSet` (`StarLemma.lean`, private) with `connectedComponentIn` in place of
`Drawing.faceSet`. Its proof does not use the drawing either — `hstar` already enters as a
set-level hypothesis — so this is the same kind of hypothesis-weakening as the star lemma itself.
Recover the drawing version through `Face.lean`'s `faceSet_eq_connectedComponentIn`, which that file
records as hypothesis-free. This is the one bridge still to state.

`Y.card = 3` at step 4 is the same obligation as the degree conjunct of
`PLDrawing.exists_radius_vertex`; proving the two bounds once discharges both.

3.10–3.11 below are Status.md corollaries of 3.9 and were blocked only through it. They unblock once
3.9 lands; their own routes are not written yet.

Upstream and permitted: `IsJordanCurve.exists_sides` / `exists_sides_onePoint` are still `sorry`.
That is JCT, the one assumption Status.md §0 allows. -/

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
