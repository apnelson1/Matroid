module

public import Matroid.Graph.Hom.Map
public import Matroid.Graph.Immersion.Embedding
public import Matroid.Graph.Walk.Iso

/-!
# Regression tests for graph homomorphisms

These consumers exercise empty vertex and edge sets, isolated vertices, and vertex
identifications that turn parallel edges into distinct loops.
-/

open Set Function Graph WList

-- Empty source sets need no default value in either target type.
example {α β γ δ : Type*} (H : Graph γ δ) :
    Hom (Graph.noEdge (∅ : Set α) β) H where
  vertMap x := False.elim x.2
  edgeMap e := False.elim e.2
  map_isLink _ _ _ h := False.elim h.edge_mem

-- An isolated vertex is retained by corestriction and its immersion image.
example : V((Emb.id (Graph.noEdge ({7} : Set ℕ) ℕ)).isoImage.toEmb.toImmersion.Image) =
    {7} := by
  rw [Emb.toImmersion_image, Hom.image_toHom, Hom.image_vertexSet]
  simp [Hom.vertexImage, Emb.id, Hom.id]

-- Transport of a nil walk uses only its vertex, including when the edge type is empty.
example {α γ δ : Type*} {G : Graph α Empty} {H : Graph γ δ}
    (F : Iso G H) (x : V(G)) :
    (F.walkMap ⟨nil x.1, IsWalk.nil x.2⟩).1 = nil (F.vertMap x).1 := rfl

private def isolatedInclusion :
    Emb (Graph.noEdge ({0} : Set ℕ) ℕ) (Graph.noEdge {0, 1} ℕ) :=
  Emb.ofLe (noEdge_le_iff.mpr (by simp))

-- Covering every edge still permits missing an isolated vertex.
example : Function.Surjective isolatedInclusion.edgeMap ∧ ¬ isolatedInclusion.Surjective := by
  refine ⟨?_, ?_⟩
  · rintro ⟨e, he⟩
    exact False.elim he
  · intro h
    obtain ⟨x, hx⟩ := h.vertMap ⟨1, by simp⟩
    have hx0 : x.1 = 0 := by simpa using x.2
    have hx1 : x.1 = 1 := congrArg Subtype.val hx
    simp [hx0] at hx1

-- Existence of a factor does not require coverage of the target's isolated vertices.
example : V(isolatedInclusion.Image) = {0} ∧
    ∃ D, isolatedInclusion.toHom.comp D = isolatedInclusion.toHom := by
  refine ⟨?_, ⟨(Hom.FactorsThrough.rfl isolatedInclusion.toHom).factor,
    (Hom.FactorsThrough.rfl isolatedInclusion.toHom).comp_factor⟩⟩
  simp [isolatedInclusion]

private def twoEdges : Graph ℕ ℕ := Graph.banana 0 1 {10, 11}

-- Identifying the endpoints creates loops without identifying the two edge labels.
example : ((twoEdges.toMap fun _ ↦ (0 : ℕ)).edgeMap ⟨10, by simp [twoEdges]⟩).1 ≠
    ((twoEdges.toMap fun _ ↦ (0 : ℕ)).edgeMap ⟨11, by simp [twoEdges]⟩).1 := by
  simp

example : ((fun _ : ℕ ↦ (0 : ℕ)) ''ᴳ twoEdges).IsLoopAt 10 0 ∧
    ((fun _ : ℕ ↦ (0 : ℕ)) ''ᴳ twoEdges).IsLoopAt 11 0 := by
  constructor
  · exact (twoEdges.toMap fun _ ↦ (0 : ℕ)).map_isLink (e := ⟨10, by simp [twoEdges]⟩)
      (x := ⟨0, by simp [twoEdges]⟩) (y := ⟨1, by simp [twoEdges]⟩) (by simp [twoEdges])
  · exact (twoEdges.toMap fun _ ↦ (0 : ℕ)).map_isLink (e := ⟨11, by simp [twoEdges]⟩)
      (x := ⟨0, by simp [twoEdges]⟩) (y := ⟨1, by simp [twoEdges]⟩) (by simp [twoEdges])

private theorem collapseFactorsThrough :
    FactorsThrough ((fun _ : ℕ ↦ true) ·.val) (fun _ : V(twoEdges) ↦ (0 : ℕ)) :=
  fun _ _ _ ↦ rfl

private theorem collapseFactorsThrough' :
    FactorsThrough (fun _ : V(twoEdges) ↦ (0 : ℕ)) ((fun _ : ℕ ↦ true) ·.val) :=
  fun _ _ _ ↦ rfl

private noncomputable def collapsedIso :
    Iso ((fun _ : ℕ ↦ (0 : ℕ)) ''ᴳ twoEdges) ((fun _ : ℕ ↦ true) ''ᴳ twoEdges) :=
  mapIso collapseFactorsThrough collapseFactorsThrough'

-- The comparison of two vertex identifications preserves each parallel edge.
example : (collapsedIso.edgeMap (⟨10, by simp [twoEdges]⟩ : E(twoEdges))).1 = 10 ∧
    (collapsedIso.invEdgeMap (⟨11, by simp [twoEdges]⟩ : E(twoEdges))).1 = 11 := by
  simp [collapsedIso]

-- The comparison really factors the original map, including its vertex data.
example : (twoEdges.toMap fun _ ↦ (0 : ℕ)).comp collapsedIso.toHom =
    twoEdges.toMap (fun _ ↦ true) := by
  simp only [collapsedIso, mapIso_toHom, toMap_comp_mapHom]

-- Factoring an embedding through its image preserves the associated immersion image.
example {α β γ δ : Type*} {G : Graph α β} {H : Graph γ δ} (F : Emb G H) :
    (F.isoImage.toEmb.comp (Emb.ofLe F.image_le)).toImmersion.Image =
      F.Image := by
  rw [F.isoImage_comp_ofLe, F.toImmersion_image]

/-- info: 'Graph.Hom.factorsThrough_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Hom.factorsThrough_iff

/-- info: 'Graph.mapIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.mapIso
