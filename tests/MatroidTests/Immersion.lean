module

public import Matroid.Graph.Immersion.Relation

/-!
# Regression tests for immersion routes

Normalization must retain a loop, retain a cycle through the prescribed vertex of a closed
trail, and discard a detour when simplifying an open trail. The axiom checks cover the new
composition proofs and the bridges to the existing subdivision API.
-/

open Set Graph WList
open scoped Sym2

-- A loop may use a trail that visits its branch vertex between its two ends.
private def twoLoopImmersion :
    Immersion (Graph.bouquet (0 : ℕ) ({0} : Set ℕ)) (Graph.bouquet 0 {10, 11}) where
  vertex := Function.Embedding.refl _
  route _ := cons 0 10 (cons 0 11 (nil 0))
  route_isTrail _ := by simp
  route_nonempty _ := by simp
  route_ends e := by
    have he : (Graph.bouquet (0 : ℕ) ({0} : Set ℕ)).IsLink e.1 0 0 := by
      exact (Graph.bouquet_isLink _ _).mpr ⟨e.2, rfl, rfl⟩
    rw [he.ends_eq, Sym2.map_mk]
    rfl
  route_edge_disjoint e f hef := by
    apply (hef ?_).elim
    apply Subtype.ext
    exact e.2.trans f.2.symm

-- The chosen image retains the second loop; normalization is allowed to discard it.
example : 11 ∈ E(twoLoopImmersion.Image) := by
  rw [Immersion.image_edgeSet]
  exact mem_iUnion.mpr ⟨⟨0, by simp⟩, by simp [twoLoopImmersion]⟩

example : 11 ∉ E(twoLoopImmersion.normalize.Image) := by
  simp [Immersion.image_edgeSet, Immersion.normalize, twoLoopImmersion, WList.cycleBypass,
    dedup_cons_eq_ite, suffixFromVertex, suffixFrom]

private lemma twoLoopImmersion_surjective : twoLoopImmersion.Surjective := by
  apply Immersion.surjective_iff_covers.mpr
  constructor
  · intro x hx
    exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · intro e he
    exact mem_iUnion.mpr ⟨⟨0, by simp⟩, by simpa [twoLoopImmersion] using he⟩

-- Composition retains both loops, including the material normalization would discard.
example : 11 ∈ E((twoLoopImmersion.comp (Immersion.refl _)).Image) := by
  rw [twoLoopImmersion_surjective.comp_image, Immersion.refl_surjective]
  simp

-- An isolated vertex survives even though the image contains no edges.
example : V((Immersion.refl (Graph.noEdge ({7} : Set ℕ) ℕ)).Image) = {7} ∧
    E((Immersion.refl (Graph.noEdge ({7} : Set ℕ) ℕ)).Image) = ∅ := by
  rw [Immersion.refl_surjective (Graph.noEdge ({7} : Set ℕ) ℕ)]
  simp

-- Deduplicating the entire vertex list would erase this loop.
example : (cons 0 10 (nil 0) : WList ℕ ℕ).cycleBypass.edge = [10] := by
  simp [WList.cycleBypass]

-- The second visit to vertex 1 shortcuts the triangle, changing the image.
example : (cons 0 10 (cons 1 11 (cons 2 12 (cons 3 13 (cons 1 14 (nil 4))))) :
    WList ℕ ℕ).cycleBypass.edge = [10, 14] := by
  simp [WList.cycleBypass, dedup_cons_eq_ite, suffixFromVertex, suffixFrom]

-- A closed trail with two cycles retains a nonempty cycle through vertex 0.
example : (cons 0 10 (cons 1 11 (cons 2 12 (cons 0 13 (cons 3 14 (cons 4 15 (nil 0)))))) :
    WList ℕ ℕ).cycleBypass.edge = [10, 11, 12] := by
  simp [WList.cycleBypass, dedup_cons_eq_ite, suffixFromVertex, suffixFrom]

section Consumers

variable {α β γ δ ε ζ : Type*} {G : Graph α β} {H : Graph γ δ} {K : Graph ε ζ}

-- Restriction followed by substitution has exactly the second immersion's image.
example (M : Immersion G H) (N : Immersion M.Image K) (y : ε) :
    y ∈ V((M.toImage.comp N).Image) ↔ y ∈ V(N.Image) := by
  rw [M.toImage_surjective.comp_image]

-- A repeated source edge cannot be hidden by substituting a longer route.
example (M : Immersion G H) (w : WList α β) (hw : G.IsWalk w) (h : ¬ G.IsTrail w) :
    ¬ H.IsTrail (M.expand w hw) := by
  simpa using h

-- Reflecting a loop needs injectivity only on vertices, even for a homomorphism.
example (F : G.Hom H) (hF : Function.Injective F.vertMap) (e : E(G)) (x : V(G))
    (h : H.IsLoopAt (F.edgeMap e).1 (F.vertMap x).1) : G.IsLoopAt e.1 x.1 :=
  (Hom.isLink_iff_of_injective hF e x x).mp h

-- Crossing both bridge interfaces preserves the chosen routes exactly.
example (M : Immersion G H) (hM : M.Topological) (hS : M.Surjective) (e : E(G)) :
    ((M.toIsoSubdivision hM hS).toImmersion.toIsoTopologicalMinor
      (M.toIsoSubdivision hM hS).toImmersion_topological).route e = M.route e := by
  simp

-- Normalization is stable on repeated use, and does not change a topological immersion.
example (M : Immersion G H) (e : E(G)) :
    (M.normalize.normalize.route e).edge = (M.normalize.route e).edge := by
  simp

example (M : Immersion G H) (hM : M.Topological) : M.normalize.Image = M.Image := by
  rw [M.normalize_eq_self_iff.mpr hM.2.1]

-- Path preservation can be used on the restriction without rebuilding its Topological proof.
example (M : Immersion G H) (hM : M.Topological) (w : WList α β) (hw : G.IsPath w) :
    M.Image.IsPath (M.toImage.expand w hw.isWalk) := by
  simpa [hM] using hw

end Consumers

/-- info: 'Graph.Immersion.Strong.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Immersion.Strong.comp
/-- info: 'Graph.Immersion.Topological.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Immersion.Topological.comp
/-- info: 'Graph.Immersion.Surjective.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Immersion.Surjective.comp
/-- info: 'Graph.IsIsoSubdivision.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.IsIsoSubdivision.trans
/--
info: 'Graph.isStrongImmersion_iff_exists_simple_routes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isStrongImmersion_iff_exists_simple_routes
