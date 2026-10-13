module

public import Matroid.Graph.Immersion.Embedding
public import Matroid.Graph.Immersion.Composition
public import Matroid.Graph.Immersion.TopologicalMinor

/-!
# Immersion relations

Reflexivity, transitivity, and embedding transport follow from the corresponding constructions
on immersion witnesses. Composition retains the substituted trails and their entire image.
-/

@[expose] public section

namespace Graph

variable {V E V' E' V'' E'' : Type*} {H : Graph V E} {G : Graph V' E'} {K : Graph V'' E''}

/-- A strong immersion is an immersion. -/
theorem IsStrongImmersion.isImmersion (h : IsStrongImmersion H G) : IsImmersion H G :=
  ⟨h.choose⟩

/-- A topological immersion is strong. -/
theorem IsTopologicalMinor.isStrongImmersion (h : IsTopologicalMinor' H G) :
    IsStrongImmersion H G :=
  ⟨h.choose, h.choose_spec.1⟩

/-- The one-edge routes of the identity graph embedding. -/
noncomputable def Immersion.refl (G : Graph V E) : Immersion G G :=
  (Graph.Iso.id G).toEmb.toImmersion

@[simp]
lemma Immersion.refl_vertex (G : Graph V E) (x : G.vertexSet) :
    (Immersion.refl G).vertex x = x := rfl

@[simp]
lemma Immersion.refl_route_length (G : Graph V E) (e : G.edgeSet) :
    ((Immersion.refl G).route e).length = 1 := rfl

@[simp]
lemma Immersion.refl_route_edgeSet (G : Graph V E) (e : G.edgeSet) :
    ((Immersion.refl G).route e).edgeSet = {e.1} := by
  rw [Immersion.refl, Graph.Emb.toImmersion_route_edgeSet]
  rfl

@[simp]
lemma Immersion.refl_topological (G : Graph V E) : (Immersion.refl G).Topological :=
  (Graph.Iso.id G).toEmb.toImmersion_topological

@[simp]
lemma Immersion.refl_strong (G : Graph V E) : (Immersion.refl G).Strong :=
  (Immersion.refl_topological G).1

@[simp]
lemma Immersion.refl_surjective (G : Graph V E) : (Immersion.refl G).Surjective :=
  (Graph.Iso.id G).toImmersion_surjective

@[refl, simp]
theorem IsImmersion.refl (G : Graph V E) : IsImmersion G G :=
  ⟨Immersion.refl G⟩

@[refl, simp]
theorem IsStrongImmersion.refl (G : Graph V E) : IsStrongImmersion G G :=
  ⟨Immersion.refl G, Immersion.refl_strong G⟩

@[refl, simp]
theorem IsTopologicalMinor'.refl (G : Graph V E) : IsTopologicalMinor' G G :=
  ⟨Immersion.refl G, Immersion.refl_topological G⟩

theorem IsImmersion.trans (hHG : IsImmersion H G) (hGK : IsImmersion G K) :
    IsImmersion H K :=
  ⟨hHG.some.comp hGK.some⟩

theorem IsStrongImmersion.trans (hHG : IsStrongImmersion H G) (hGK : IsStrongImmersion G K) :
    IsStrongImmersion H K :=
  ⟨hHG.choose.comp hGK.choose, Immersion.Strong.comp hHG.choose_spec hGK.choose_spec⟩

theorem IsTopologicalMinor'.trans (hHG : IsTopologicalMinor' H G) (hGK : IsTopologicalMinor' G K) :
    IsTopologicalMinor' H K :=
  ⟨hHG.choose.comp hGK.choose, Immersion.Topological.comp hHG.choose_spec hGK.choose_spec⟩

/-- Pull back the source along a graph embedding. -/
theorem IsImmersion.comap (h : IsImmersion G K) (F : H.Emb G) : IsImmersion H K :=
  ⟨F.toImmersion.comp h.some⟩

/-- Push forward the host along a graph embedding. -/
theorem IsImmersion.map (h : IsImmersion H G) (F : G.Emb K) : IsImmersion H K :=
  ⟨h.some.comp F.toImmersion⟩

theorem IsStrongImmersion.comap (h : IsStrongImmersion G K) (F : H.Emb G) :
    IsStrongImmersion H K :=
  ⟨F.toImmersion.comp h.choose,
    Immersion.Strong.comp F.toImmersion_topological.1 h.choose_spec⟩

theorem IsStrongImmersion.map (h : IsStrongImmersion H G) (F : G.Emb K) :
    IsStrongImmersion H K :=
  ⟨h.choose.comp F.toImmersion,
    Immersion.Strong.comp h.choose_spec F.toImmersion_topological.1⟩

theorem IsTopologicalMinor'.comap (h : IsTopologicalMinor' G K) (F : H.Emb G) :
    IsTopologicalMinor' H K :=
  ⟨F.toImmersion.comp h.choose,
    Immersion.Topological.comp F.toImmersion_topological h.choose_spec⟩

theorem IsTopologicalMinor'.map (h : IsTopologicalMinor' H G) (F : G.Emb K) :
    IsTopologicalMinor' H K :=
  ⟨h.choose.comp F.toImmersion,
    Immersion.Topological.comp h.choose_spec F.toImmersion_topological⟩

theorem IsIsoTopologicalMinor.trans (hHG : H.IsIsoTopologicalMinor G)
    (hGK : G.IsIsoTopologicalMinor K) : H.IsIsoTopologicalMinor K := by
  rw [Graph.isIsoTopologicalMinor_iff_isTopologicalMinor] at hHG hGK ⊢
  exact hHG.trans hGK

theorem IsIsoSubdivision.trans (hHG : H.IsIsoSubdivision G)
    (hGK : G.IsIsoSubdivision K) : H.IsIsoSubdivision K := by
  obtain ⟨M, hM, hMS⟩ := Graph.isIsoSubdivision_iff_exists_immersion.mp hHG
  obtain ⟨N, hN, hNS⟩ := Graph.isIsoSubdivision_iff_exists_immersion.mp hGK
  exact Graph.isIsoSubdivision_iff_exists_immersion.mpr
    ⟨M.comp N, Immersion.Topological.comp hM hN, Immersion.Surjective.comp hMS hNS⟩

end Graph
