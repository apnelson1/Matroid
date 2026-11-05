module

public import Matroid.Graph.Presentation.Basic
public import Matroid.Graph.Hom.Basic
public import Matroid.ForMathlib.PEquiv
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Morphisms of incidence presentations

Label-coherent `Embedding` (same ambient `V`, `E`, labels preserved) is a real distinction from
heterogeneous injective morphisms. Those are `IsoEmbedding`. Both convert to `Hom`, which stores
`map_other` because it is not derivable without injectivity.

This file defines combinatorial maps only; maps of realizations belong to the topology layer.
-/

@[expose] public section

open Function Set
universe uV uI uE uV' uI' uE' uV'' uI'' uE''

namespace Graph.Presentation

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'} {V'' : Type uV''}
  {E'' : Type uE''} {I : Type uI} {I' : Type uI'} {I'' : Type uI''}
  {P : Presentation V I E} {Q : Presentation V' I' E'} {R : Presentation V'' I'' E''}

/-- A homomorphism of incidence presentations, on the vertex, edge, and incidence
carriers. `map_other` is stored: without injectivity it is not implied by edge compatibility. -/
structure Hom (P : Presentation V I E) (Q : Presentation V' I' E') where
  /-- The map of vertices. -/
  vertexMap : V(P) → V(Q)
  /-- The map of edges. -/
  edgeMap : E(P) → E(Q)
  /-- The map of incidences. -/
  incidenceMap : I → I'
  /-- Attachment is preserved. -/
  map_attach : ∀ i, vertexMap ⟨P.attach i, P.attach_mem i⟩ =
        ⟨Q.attach (incidenceMap i), Q.attach_mem (incidenceMap i)⟩
  /-- The underlying edge of an incidence is preserved. -/
  map_edge : ∀ i, edgeMap ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩ =
        ⟨Q.edgeMap (incidenceMap i), Q.edgeMap_mem_edgeSet (incidenceMap i)⟩
  /-- The fixed-point-free involution is preserved. -/
  map_other : ∀ i, incidenceMap (P.other i) = Q.other (incidenceMap i)

attribute [simp] Hom.map_attach Hom.map_edge Hom.map_other

namespace Hom

/-- The identity homomorphism of an incidence presentation. -/
protected def id (P : Presentation V I E) : Hom P P where
  vertexMap := id
  edgeMap := id
  incidenceMap := id
  map_attach := fun _ ↦ rfl
  map_edge := fun _ ↦ rfl
  map_other := fun _ ↦ rfl

/-- Compose homomorphisms of incidence presentations. -/
protected def comp (F : Hom P Q) (F' : Hom Q R) : Hom P R where
  vertexMap := F'.vertexMap ∘ F.vertexMap
  edgeMap := F'.edgeMap ∘ F.edgeMap
  incidenceMap := F'.incidenceMap ∘ F.incidenceMap
  map_attach i := by
    change F'.vertexMap (F.vertexMap ⟨P.attach i, P.attach_mem i⟩) = _
    rw [F.map_attach, F'.map_attach]
    rfl
  map_edge i := by
    change F'.edgeMap (F.edgeMap ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩) = _
    rw [F.map_edge, F'.map_edge]
    rfl
  map_other i := by
    change F'.incidenceMap (F.incidenceMap (P.other i)) =
      R.other (F'.incidenceMap (F.incidenceMap i))
    rw [F.map_other, F'.map_other]

/-- Forget incidences and retain the induced graph homomorphism. -/
noncomputable def toGraphHom (F : Hom P Q) : P.toGraph.Hom Q.toGraph := by
  refine
    { vertMap := F.vertexMap
      edgeMap := F.edgeMap
      map_isLink := by
        intro e x y hlink
        obtain ⟨i, he, hx, hy⟩ := hlink
        have heq : e = ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩ :=
          Subtype.ext he.symm
        have hxq : x = ⟨P.attach i, P.attach_mem i⟩ :=
          Subtype.ext hx.symm
        have hyq : y = ⟨P.attach (P.other i), P.attach_mem (P.other i)⟩ :=
          Subtype.ext hy.symm
        subst e
        subst x
        subst y
        refine ⟨F.incidenceMap i, ?_, ?_, ?_⟩
        · exact (congrArg Subtype.val (F.map_edge i)).symm
        · exact (congrArg Subtype.val (F.map_attach i)).symm
        · rw [← F.map_other]
          exact (congrArg Subtype.val (F.map_attach (P.other i))).symm }

end Hom

/-- A heterogeneous embedding of incidence presentations, on the three carriers.
`map_other` is derived from edge compatibility and injectivity of the incidence embedding. -/
structure IsoEmbedding (P : Presentation V I E) (Q : Presentation V' I' E') where
  /-- The embedding of vertices. -/
  vertexEmbedding : V(P) ↪ V(Q)
  /-- The embedding of edges. -/
  edgeEmbedding : E(P) ↪ E(Q)
  /-- The embedding of incidences. -/
  incidenceEmbedding : I ↪ I'
  /-- Attachment is preserved. -/
  map_attach : ∀ i, vertexEmbedding ⟨P.attach i, P.attach_mem i⟩ =
        ⟨Q.attach (incidenceEmbedding i), Q.attach_mem (incidenceEmbedding i)⟩
  /-- The underlying edge of an incidence is preserved. -/
  map_edge : ∀ i, edgeEmbedding ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩ =
    ⟨Q.edgeMap (incidenceEmbedding i), Q.edgeMap_mem_edgeSet (incidenceEmbedding i)⟩

attribute [simp] IsoEmbedding.map_attach IsoEmbedding.map_edge

namespace IsoEmbedding

/-- An incidence embedding automatically commutes with the fixed-point-free involutions. -/
@[simp]
lemma map_other (F : IsoEmbedding P Q) (i : I) :
    F.incidenceEmbedding (P.other i) = Q.other (F.incidenceEmbedding i) := by
  have he : Q.edgeMap (F.incidenceEmbedding i) = Q.edgeMap (F.incidenceEmbedding (P.other i)) := by
    have hp : (⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩ : E(P)) =
        ⟨P.edgeMap (P.other i), P.edgeMap_mem_edgeSet (P.other i)⟩ :=
      Subtype.ext (P.edgeMap_other i).symm
    calc
      Q.edgeMap (F.incidenceEmbedding i) =
          (F.edgeEmbedding ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩).1 :=
        by rw [F.map_edge]
      _ = (F.edgeEmbedding ⟨P.edgeMap (P.other i), P.edgeMap_mem_edgeSet (P.other i)⟩).1 :=
        congrArg (fun e : E(Q) ↦ e.1) (congrArg F.edgeEmbedding hp)
      _ = Q.edgeMap (F.incidenceEmbedding (P.other i)) := by rw [F.map_edge]
  exact (Q.edgeMap_eq_iff (F.incidenceEmbedding i) (F.incidenceEmbedding (P.other i))).1 he
    |>.resolve_left fun hEq ↦ P.other_ne i (F.incidenceEmbedding.injective hEq)

/-- The identity embedding of an incidence presentation. -/
protected def refl (P : Presentation V I E) : IsoEmbedding P P where
  vertexEmbedding := Function.Embedding.refl _
  edgeEmbedding := Function.Embedding.refl _
  incidenceEmbedding := Function.Embedding.refl _
  map_attach := fun _ ↦ rfl
  map_edge := fun _ ↦ rfl

/-- Compose heterogeneous embeddings of incidence presentations. -/
protected def trans (F : IsoEmbedding P Q) (F' : IsoEmbedding Q R) : IsoEmbedding P R where
  vertexEmbedding := F.vertexEmbedding.trans F'.vertexEmbedding
  edgeEmbedding := F.edgeEmbedding.trans F'.edgeEmbedding
  incidenceEmbedding := F.incidenceEmbedding.trans F'.incidenceEmbedding
  map_attach i := by
    change F'.vertexEmbedding (F.vertexEmbedding ⟨P.attach i, P.attach_mem i⟩) = _
    rw [F.map_attach, F'.map_attach]
    rfl
  map_edge i := by
    change F'.edgeEmbedding (F.edgeEmbedding ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩) = _
    rw [F.map_edge, F'.map_edge]
    rfl

/-- Regard a heterogeneous embedding as a homomorphism. -/
def toHom (F : IsoEmbedding P Q) : Hom P Q where
  vertexMap := F.vertexEmbedding
  edgeMap := F.edgeEmbedding
  incidenceMap := F.incidenceEmbedding
  map_attach := F.map_attach
  map_edge := F.map_edge
  map_other := F.map_other

/-- Forget incidences and retain the induced graph embedding. -/
noncomputable def toGraphEmb (F : IsoEmbedding P Q) : P.toGraph.Emb Q.toGraph := by
  refine
    { vertMap := F.vertexEmbedding
      edgeMap := F.edgeEmbedding
      vertMap_injective := F.vertexEmbedding.injective
      edgeMap_injective := F.edgeEmbedding.injective
      map_isLink := by
        intro e x y hlink
        obtain ⟨i, he, hx, hy⟩ := hlink
        have heq : e = ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩ :=
          Subtype.ext he.symm
        have hxq : x = ⟨P.attach i, P.attach_mem i⟩ :=
          Subtype.ext hx.symm
        have hyq : y = ⟨P.attach (P.other i), P.attach_mem (P.other i)⟩ :=
          Subtype.ext hy.symm
        subst e
        subst x
        subst y
        refine ⟨F.incidenceEmbedding i, ?_, ?_, ?_⟩
        · exact (congrArg Subtype.val (F.map_edge i)).symm
        · exact (congrArg Subtype.val (F.map_attach i)).symm
        · rw [← F.map_other]
          exact (congrArg Subtype.val (F.map_attach (P.other i))).symm }

end IsoEmbedding

/-- An isomorphism of incidence presentations, on the vertex, edge, and incidence
carriers. Converts to `IsoEmbedding`. -/
structure Iso (P : Presentation V I E) (Q : Presentation V' I' E') where
  /-- The equivalence of vertices. -/
  vertexEquiv : V(P) ≃ V(Q)
  /-- The equivalence of edges. -/
  edgeEquiv : E(P) ≃ E(Q)
  /-- The equivalence of incidences. -/
  incidenceEquiv : I ≃ I'
  /-- Attachment is preserved. -/
  map_attach : ∀ i, vertexEquiv ⟨P.attach i, P.attach_mem i⟩ =
    ⟨Q.attach (incidenceEquiv i), Q.attach_mem (incidenceEquiv i)⟩
  /-- The underlying edge of an incidence is preserved. -/
  map_edge : ∀ i, edgeEquiv ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩ =
    ⟨Q.edgeMap (incidenceEquiv i), Q.edgeMap_mem_edgeSet (incidenceEquiv i)⟩

attribute [simp] Iso.map_attach Iso.map_edge

namespace Iso

/-- The identity isomorphism of an incidence presentation. -/
protected def refl (P : Presentation V I E) : P.Iso P where
  vertexEquiv := _root_.Equiv.refl _
  edgeEquiv := _root_.Equiv.refl _
  incidenceEquiv := _root_.Equiv.refl _
  map_attach := fun _ ↦ rfl
  map_edge := fun _ ↦ rfl

lemma symm_map_attach (F : P.Iso Q) (j : I') : F.vertexEquiv.symm ⟨Q.attach j, Q.attach_mem j⟩ =
      ⟨P.attach (F.incidenceEquiv.symm j), P.attach_mem (F.incidenceEquiv.symm j)⟩ := by
  apply F.vertexEquiv.injective
  simp

lemma symm_map_edge (F : P.Iso Q) (j : I') :
    F.edgeEquiv.symm ⟨Q.edgeMap j, Q.edgeMap_mem_edgeSet j⟩ =
      ⟨P.edgeMap (F.incidenceEquiv.symm j), P.edgeMap_mem_edgeSet (F.incidenceEquiv.symm j)⟩ := by
  apply F.edgeEquiv.injective
  simp

/-- Inverse of an isomorphism of incidence presentations. -/
protected def symm (F : P.Iso Q) : Q.Iso P where
  vertexEquiv := F.vertexEquiv.symm
  edgeEquiv := F.edgeEquiv.symm
  incidenceEquiv := F.incidenceEquiv.symm
  map_attach := F.symm_map_attach
  map_edge := F.symm_map_edge

lemma trans_map_attach (F : P.Iso Q) (F' : Q.Iso R) (i : I) :
    (F.vertexEquiv.trans F'.vertexEquiv) ⟨P.attach i, P.attach_mem i⟩ =
      ⟨R.attach ((F.incidenceEquiv.trans F'.incidenceEquiv) i),
        R.attach_mem ((F.incidenceEquiv.trans F'.incidenceEquiv) i)⟩ := by
  change F'.vertexEquiv (F.vertexEquiv ⟨P.attach i, P.attach_mem i⟩) =
    ⟨R.attach (F'.incidenceEquiv (F.incidenceEquiv i)),
      R.attach_mem (F'.incidenceEquiv (F.incidenceEquiv i))⟩
  rw [F.map_attach, F'.map_attach]

lemma trans_map_edge (F : P.Iso Q) (F' : Q.Iso R) (i : I) :
    (F.edgeEquiv.trans F'.edgeEquiv) ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩ =
      ⟨R.edgeMap ((F.incidenceEquiv.trans F'.incidenceEquiv) i),
        R.edgeMap_mem_edgeSet ((F.incidenceEquiv.trans F'.incidenceEquiv) i)⟩ := by
  change F'.edgeEquiv (F.edgeEquiv ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩) =
    ⟨R.edgeMap (F'.incidenceEquiv (F.incidenceEquiv i)),
      R.edgeMap_mem_edgeSet (F'.incidenceEquiv (F.incidenceEquiv i))⟩
  rw [F.map_edge, F'.map_edge]

/-- Compose isomorphisms of incidence presentations. -/
protected def trans (F : P.Iso Q) (F' : Q.Iso R) : P.Iso R where
  vertexEquiv := F.vertexEquiv.trans F'.vertexEquiv
  edgeEquiv := F.edgeEquiv.trans F'.edgeEquiv
  incidenceEquiv := F.incidenceEquiv.trans F'.incidenceEquiv
  map_attach := F.trans_map_attach F'
  map_edge := F.trans_map_edge F'

/-- Regard an isomorphism of presentations as a heterogeneous embedding. -/
def toIsoEmbedding (F : P.Iso Q) : IsoEmbedding P Q where
  vertexEmbedding := F.vertexEquiv.toEmbedding
  edgeEmbedding := F.edgeEquiv.toEmbedding
  incidenceEmbedding := F.incidenceEquiv.toEmbedding
  map_attach := F.map_attach
  map_edge := F.map_edge

/-- An incidence isomorphism automatically commutes with the fixed-point-free involutions. -/
@[simp]
lemma map_other (F : P.Iso Q) (i : I) :
    F.incidenceEquiv (P.other i) = Q.other (F.incidenceEquiv i) :=
  F.toIsoEmbedding.map_other i

/-- Regard an isomorphism of presentations as a homomorphism. -/
def toHom (F : P.Iso Q) : Hom P Q := F.toIsoEmbedding.toHom

end Iso

variable {P : Presentation V I E} {Q : Presentation V I' E} {R : Presentation V I'' E}

/-- A literal-label-preserving inclusion of incidence presentations on a shared ambient. -/
structure Embedding (P : Presentation V I E) (Q : Presentation V I' E) where
  /-- Every vertex of the source is a vertex of the target. -/
  vertexSet_mono : P.vertexSet ⊆ Q.vertexSet
  /-- The embedding of incidences. -/
  incidenceEmbedding : I ↪ I'
  /-- Attachment labels are preserved. -/
  map_attach : ∀ i, Q.attach (incidenceEmbedding i) = P.attach i
  /-- Edge labels are preserved. -/
  map_edge : ∀ i, Q.edgeMap (incidenceEmbedding i) = P.edgeMap i

attribute [simp] Embedding.map_attach Embedding.map_edge

namespace Embedding

/-- The identity embedding of an incidence presentation. -/
protected def refl (P : Presentation V I E) : P.Embedding P where
  vertexSet_mono := fun _ h ↦ h
  incidenceEmbedding := Function.Embedding.refl _
  map_attach := fun _ ↦ rfl
  map_edge := fun _ ↦ rfl

/-- Compose embeddings of incidence presentations. -/
protected def trans (F : P.Embedding Q) (F' : Q.Embedding R) : P.Embedding R where
  vertexSet_mono := F.vertexSet_mono.trans F'.vertexSet_mono
  incidenceEmbedding := F.incidenceEmbedding.trans F'.incidenceEmbedding
  map_attach i := (F'.map_attach (F.incidenceEmbedding i)).trans (F.map_attach i)
  map_edge i := (F'.map_edge (F.incidenceEmbedding i)).trans (F.map_edge i)

/-- The vertex embedding induced by an embedding of incidence presentations. -/
def vertexEmbedding (F : P.Embedding Q) : V(P) ↪ V(Q) where
  toFun v := ⟨v.1, F.vertexSet_mono v.2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun z : V(Q) ↦ z.1) h)

/-- An embedding of incidence presentations preserves the underlying edge labels. -/
lemma edgeSet_mono (F : P.Embedding Q) : P.edgeSet ⊆ Q.edgeSet := by
  rintro e ⟨i, hi⟩
  exact ⟨F.incidenceEmbedding i, (F.map_edge i).trans hi⟩

/-- The edge embedding induced by an embedding of incidence presentations. -/
def edgeEmbedding (F : P.Embedding Q) : E(P) ↪ E(Q) where
  toFun e := ⟨e.1, F.edgeSet_mono e.2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun z : E(Q) ↦ z.1) h)

/-- An incidence embedding automatically commutes with the fixed-point-free involutions. -/
@[simp]
lemma map_other (F : P.Embedding Q) (i : I) :
    F.incidenceEmbedding (P.other i) = Q.other (F.incidenceEmbedding i) := by
  have he : Q.edgeMap (F.incidenceEmbedding i) = Q.edgeMap (F.incidenceEmbedding (P.other i)) := by
    rw [F.map_edge, F.map_edge, P.edgeMap_other]
  obtain hEq | hOther :=
    (Q.edgeMap_eq_iff (F.incidenceEmbedding i) (F.incidenceEmbedding (P.other i))).mp he
  · exact (P.other_ne i (F.incidenceEmbedding.injective hEq)).elim
  exact hOther

/-- Embeddings of presentations are determined by their maps on incidences. -/
@[ext]
lemma ext {F F' : P.Embedding Q} (h : F.incidenceEmbedding = F'.incidenceEmbedding) : F = F' := by
  cases F
  cases F'
  cases h
  rfl

/-- Regard a label-coherent embedding as a heterogeneous embedding. -/
def toIsoEmbedding (F : P.Embedding Q) : IsoEmbedding P Q where
  vertexEmbedding := F.vertexEmbedding
  edgeEmbedding := F.edgeEmbedding
  incidenceEmbedding := F.incidenceEmbedding
  map_attach i := Subtype.ext (F.map_attach i).symm
  map_edge i := Subtype.ext (F.map_edge i).symm

/-- Regard a label-coherent embedding as a homomorphism. -/
def toHom (F : P.Embedding Q) : Hom P Q :=
  F.toIsoEmbedding.toHom

/-- A label-coherent presentation embedding is a subgraph of coarse graphs. -/
theorem toGraph_le (F : P.Embedding Q) : P.toGraph ≤ Q.toGraph where
  vertexSet_mono := F.vertexSet_mono
  isLink_mono := fun e x y ⟨i, hiE, hiV, hiO⟩ =>
    ⟨F.incidenceEmbedding i, (F.map_edge i).trans hiE, (F.map_attach i).trans hiV,
      (show Q.attach (Q.other (F.incidenceEmbedding i)) = y by
        rw [← F.map_other, F.map_attach, hiO])⟩

/-- Forget incidences and retain the induced identity-on-labels graph embedding. -/
noncomputable def toGraphEmb (F : P.Embedding Q) : P.toGraph.Emb Q.toGraph :=
  F.toIsoEmbedding.toGraphEmb

end Embedding

namespace IsoEmbedding

variable {P : Presentation V I E} {Q : Presentation V I' E}

/-- Restrict a label-preserving heterogeneous embedding to a label-coherent embedding. -/
def toEmbedding (F : IsoEmbedding P Q) (hV : ∀ v : V(P), (F.vertexEmbedding v).1 = v.1)
    (hE : ∀ e : E(P), (F.edgeEmbedding e).1 = e.1) : Embedding P Q where
  vertexSet_mono := fun v hv => by
    have := (F.vertexEmbedding ⟨v, hv⟩).2
    rwa [hV] at this
  incidenceEmbedding := F.incidenceEmbedding
  map_attach i :=
    (congrArg Subtype.val (F.map_attach i)).symm.trans (hV ⟨P.attach i, P.attach_mem i⟩)
  map_edge i :=
    (congrArg Subtype.val (F.map_edge i)).symm.trans (hE ⟨P.edgeMap i, P.edgeMap_mem_edgeSet i⟩)

end IsoEmbedding

-- variable {P : Presentation V I E} {Q : Presentation V I' E}

-- namespace Equiv

-- /-- Regard an incidence relabelling as a label-coherent embedding. -/
-- def toEmbedding (F : P.Equiv Q) : Embedding P Q where
--   vertexSet_mono := subset_of_eq F.vertexSet_eq
--   incidenceEmbedding := F.incEquiv.toEmbedding
--   map_attach := F.vertex_eq
--   map_edge := F.edge_eq

-- /-- Regard an incidence relabelling as a homomorphism. -/
-- def toHom (F : P.Equiv Q) : Hom P Q :=
--   F.toEmbedding.toHom

-- /-- Forget the label coherence of an incidence relabelling and retain the induced heterogeneous
-- presentation isomorphism. -/
-- def toIso (F : P.Equiv Q) : P.Iso Q where
--   vertexEquiv := F.vertexEquiv
--   edgeEquiv := F.edgeEquiv
--   incidenceEquiv := F.incEquiv
--   map_attach i := Subtype.ext (F.vertex_eq i).symm
--   map_edge i := Subtype.ext (F.edge_eq i).symm

-- end Equiv

end Graph.Presentation
