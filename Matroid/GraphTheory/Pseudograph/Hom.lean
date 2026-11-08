module

public import Matroid.GraphTheory.Pseudograph.Incidence
public import Matroid.GraphTheory.Graph.Hom.Basic
public import Matroid.GraphTheory.HypergraphLike.Graph.Hom

/-!
# Maps of pseudographs

Homomorphisms, heterogeneous embeddings and isomorphisms use the shared `HypergraphLike` API.
`Pseudograph.Embedding` additionally fixes vertex and edge labels while allowing incidence
relabelling; literal incidence-preserving inclusion remains `HypergraphLike.IsSubgraph`.
-/

open HypergraphLike

@[expose] public section

open Set Function

open Pseudograph

variable {V I E W J F U K L : Type*} {P : Pseudograph V I E} {Q : Pseudograph W J F}
  {R : Pseudograph U K L}

namespace HypergraphLike.Hom

/-- Forget incidence labels in a shared graph homomorphism. -/
def toGraphHom (f : Hom P Q) : P.toGraph.Hom Q.toGraph where
  vertMap := f.vertMap'
  edgeMap := f.edgeMap'
  map_isLink := by
    intro e x y h
    obtain ⟨i, he, hx, hy⟩ := toGraph_isLink_iff.mp h
    apply toGraph_isLink_iff.mpr
    refine ⟨f.incMap' i, ?_, ?_, ?_⟩
    · exact (congrArg Subtype.val (f.map_edgeMap' i)).trans
        (congrArg (fun e ↦ (f.edgeMap' e).val) (Subtype.ext he))
    · exact (congrArg Subtype.val (f.map_attach' i)).trans
        (congrArg (fun v ↦ (f.vertMap' v).val) (Subtype.ext hx))
    · have ho : f.incMap' (P.other' i) = Q.other' (f.incMap' i) := f.map_other' i
      rw [← ho]
      exact (congrArg Subtype.val (f.map_attach' (P.other' i))).trans
        (congrArg (fun v ↦ (f.vertMap' v).val) (Subtype.ext hy))

end HypergraphLike.Hom

namespace HypergraphLike.Emb

/-- Forget incidence labels in a heterogeneous embedding. -/
def toGraphEmb (f : Emb P Q) : P.toGraph.Emb Q.toGraph where
  toHom := f.toHom.toGraphHom
  vertMap_injective := f.vertMap'_injective
  edgeMap_injective := f.edgeMap'_injective

end HypergraphLike.Emb

namespace Pseudograph

variable {Q : Pseudograph V J E} {R : Pseudograph V K E}

/-- An embedding fixing vertex and edge labels, while allowing incidence relabelling. -/
structure Embedding (P : Pseudograph V I E) (Q : Pseudograph V J E) where
  vertexSet_mono : P.vertexSet ⊆ Q.vertexSet
  incidenceEmbedding : I(P) ↪ I(Q)
  map_attach : ∀ i, Q.attach' (incidenceEmbedding i) = P.attach' i
  map_edge : ∀ i, Q.edgeMap' (incidenceEmbedding i) = P.edgeMap' i

attribute [simp] Embedding.map_attach Embedding.map_edge

namespace Embedding

/-- An embedding fixing vertex and edge labels is determined by its incidence map. -/
@[ext]
lemma ext {f g : Embedding P Q} (h : f.incidenceEmbedding = g.incidenceEmbedding) : f = g := by
  cases f
  cases g
  cases h
  rfl

protected def refl (P : Pseudograph V I E) : Embedding P P where
  vertexSet_mono := .rfl
  incidenceEmbedding := .refl _
  map_attach _ := rfl
  map_edge _ := rfl

protected def trans (f : Embedding P Q) (g : Embedding Q R) : Embedding P R where
  vertexSet_mono := f.vertexSet_mono.trans g.vertexSet_mono
  incidenceEmbedding := f.incidenceEmbedding.trans g.incidenceEmbedding
  map_attach i := (g.map_attach _).trans (f.map_attach i)
  map_edge i := (g.map_edge _).trans (f.map_edge i)

def vertexEmbedding (f : Embedding P Q) : V(P) ↪ V(Q) :=
  ⟨fun v ↦ ⟨v.val, f.vertexSet_mono v.property⟩, by
    intro x y h
    exact Subtype.ext (congrArg (fun z : V(Q) ↦ z.val) h)⟩

lemma edgeSet_mono (f : Embedding P Q) : E(P) ⊆ E(Q) := by
  rintro e he
  obtain ⟨i, rfl⟩ := mem_edgeSet_iff.mp he
  rw [← f.map_edge i]
  exact Q.edgeMap'_mem _

def edgeEmbedding (f : Embedding P Q) : E(P) ↪ E(Q) :=
  ⟨fun e ↦ ⟨e.val, f.edgeSet_mono e.property⟩, by
    intro x y h
    exact Subtype.ext (congrArg (fun z : E(Q) ↦ z.val) h)⟩

/-- The shared heterogeneous embedding underlying a label-preserving embedding. -/
def toIsoEmbedding (f : Embedding P Q) : Emb P Q := by
  let g : HypergraphLike.IncEmb P Q := HypergraphLike.IncEmb.ofEmbeddings
    f.vertexEmbedding f.incidenceEmbedding f.edgeEmbedding
    (fun i ↦ Subtype.ext (f.map_attach i)) (fun i ↦ Subtype.ext (f.map_edge i))
    (fun i _ ↦ (f.incidenceEmbedding i).property)
    (fun i _ ↦ (f.incidenceEmbedding i).property)
  exact HypergraphLike.Emb.ofIncEmb g g.isLocallySurjective

def toHom (f : Embedding P Q) : Hom P Q := f.toIsoEmbedding.toHom

@[simp]
lemma map_other (f : Embedding P Q) (i : I(P)) :
    f.incidenceEmbedding (P.other' i) = Q.other' (f.incidenceEmbedding i) :=
  f.toIsoEmbedding.toIncEmb.map_other' i

theorem toGraph_le (f : Embedding P Q) : P.toGraph ≤ Q.toGraph where
  vertexSet_mono := f.vertexSet_mono
  isLink_mono := by
    intro e x y h
    obtain ⟨i, he, hx, hy⟩ := toGraph_isLink_iff.mp h
    apply toGraph_isLink_iff.mpr
    exact ⟨f.incidenceEmbedding i, (f.map_edge i).trans he,
      (f.map_attach i).trans hx, by rw [← f.map_other, f.map_attach, hy]⟩

def toGraphEmb (f : Embedding P Q) : P.toGraph.Emb Q.toGraph :=
  f.toIsoEmbedding.toGraphEmb

end Embedding

end Pseudograph

namespace HypergraphLike.Emb

variable {Q : Pseudograph V J E}

def toEmbedding (f : Emb P Q) (hV : ∀ v : V(P), (f.vertMap' v).val = v.val)
    (hE : ∀ e : E(P), (f.edgeMap' e).val = e.val) : Pseudograph.Embedding P Q where
  vertexSet_mono v hv := by
    have h := (f.vertMap' ⟨v, hv⟩).property
    change (f.vertMap' ⟨v, hv⟩).val ∈ Q.vertexSet at h
    rwa [hV] at h
  incidenceEmbedding := f.incEmbedding
  map_attach i := (congrArg Subtype.val (f.map_attach' i)).trans (hV _)
  map_edge i := (congrArg Subtype.val (f.map_edgeMap' i)).trans (hE _)

end HypergraphLike.Emb
