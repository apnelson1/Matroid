module

public import Matroid.Graph.Presentation.Hom
public import Matroid.Graph.Presentation.Quotient

/-!
# Lifting coarse graph embeddings to chosen presentations

`Graph.Emb G H` is a map of vertices and edges. Independently chosen presentations
`ofGraph G` and `ofGraph H` may order the two ends of an edge differently; the induced incidence
map flips the Boolean coordinate exactly when those orderings disagree under the vertex map.

This is the stable `ofGraph` operation. A subgraph inclusion is the identity-on-labels special
case `Emb.ofLe`.
-/

@[expose] public noncomputable section

open Function Set Classical
universe uV uE uV' uE'

namespace Graph.Presentation

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'} {G : Graph V E}
  {H : Graph V' E'}

/-- Same-Boolean incidence in the target chosen presentation. Implementation of
`ofGraphIsoEmbedding`; not a caller-facing constructor. -/
def incMapUnflipped (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) : ULift.{uV'} (E(H) × Bool) :=
    ULift.up (F.edgeMap i.down.1, i.down.2)

/-- Incidence map of a coarse embedding, flipping when chosen endpoint orderings disagree. -/
noncomputable def incMapOfGraphEmb (F : G.Emb H) :
    ULift.{uV} (E(G) × Bool) → ULift.{uV'} (E(H) × Bool) := fun i ↦
    let j := incMapUnflipped F i
    let vH := F.vertMap ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩
    if (ofGraph H).attach j = vH.1 then j else (ofGraph H).other j

lemma incMapOfGraphEmb_eq_ite (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    incMapOfGraphEmb F i =
      if (ofGraph H).attach (incMapUnflipped F i) =
            (F.vertMap ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩).1 then
        incMapUnflipped F i
      else (ofGraph H).other (incMapUnflipped F i) :=
  rfl

lemma incMapUnflipped_edge (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    (ofGraph H).edgeMap (incMapUnflipped F i) = (F.edgeMap i.down.1).1 :=
  rfl

lemma incMapUnflipped_other (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    incMapUnflipped F ((ofGraph G).other i) = (ofGraph H).other (incMapUnflipped F i) :=
  rfl

lemma isLink_map_unflipped (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    H.IsLink ((ofGraph H).edgeMap (incMapUnflipped F i))
      (F.vertMap ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩).1
      (F.vertMap ⟨(ofGraph G).attach ((ofGraph G).other i),
            (ofGraph G).attach_mem ((ofGraph G).other i)⟩).1 :=
  F.map_isLink (e := i.down.1)
    (x := ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩)
    (y := ⟨(ofGraph G).attach ((ofGraph G).other i),
      (ofGraph G).attach_mem ((ofGraph G).other i)⟩)
    (ofGraph_isLink G i)

lemma incMapUnflipped_attach_iff (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    (ofGraph H).attach (incMapUnflipped F i) =
        (F.vertMap ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩).1 ↔
      (ofGraph H).attach ((ofGraph H).other (incMapUnflipped F i)) =
        (F.vertMap
            ⟨(ofGraph G).attach ((ofGraph G).other i),
              (ofGraph G).attach_mem ((ofGraph G).other i)⟩).1 := by
  have hH := ofGraph_isLink H (incMapUnflipped F i)
  have hF := isLink_map_unflipped F i
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hH.eq_and_eq_or_eq_and_eq hF
  · constructor <;> intro <;> simp_all
  · constructor
    · intro h
      exact h2.trans (h.symm.trans h1)
    · intro h
      exact h1.trans (h.symm.trans h2)

lemma incMapOfGraphEmb_edge (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    (ofGraph H).edgeMap (incMapOfGraphEmb F i) = (F.edgeMap i.down.1).1 := by
  rw [incMapOfGraphEmb_eq_ite]
  split_ifs
  · exact incMapUnflipped_edge F i
  · rw [edgeMap_other, incMapUnflipped_edge]

lemma incMapOfGraphEmb_attach (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    (ofGraph H).attach (incMapOfGraphEmb F i) =
      (F.vertMap ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩).1 := by
  rw [incMapOfGraphEmb_eq_ite]
  split_ifs with hif
  · exact hif
  · have hH := ofGraph_isLink H (incMapUnflipped F i)
    have hF := isLink_map_unflipped F i
    obtain ⟨hatt, -⟩ | ⟨-, hsw⟩ := hH.eq_and_eq_or_eq_and_eq hF
    · exact (hif hatt).elim
    · exact hsw

lemma incMapOfGraphEmb_other (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    incMapOfGraphEmb F ((ofGraph G).other i) = (ofGraph H).other (incMapOfGraphEmb F i) := by
  rw [incMapOfGraphEmb_eq_ite, incMapOfGraphEmb_eq_ite, incMapUnflipped_other]
  split_ifs with h1 h2 h2
  · rfl
  · exact (h2 ((incMapUnflipped_attach_iff F i).mpr h1)).elim
  · exact (h1 ((incMapUnflipped_attach_iff F i).mp h2)).elim
  · rw [other_other]

lemma incMapOfGraphEmb_injective (F : G.Emb H) : Injective (incMapOfGraphEmb F) := by
  intro i i' hij
  have he1 : i.down.1 = i'.down.1 :=
    F.edgeMap_injective <| Subtype.ext <|
      (incMapOfGraphEmb_edge F i).symm.trans <|
      (congrArg (ofGraph H).edgeMap hij).trans (incMapOfGraphEmb_edge F i')
  obtain hb | hb := eq_or_ne i.down.2 i'.down.2
  · exact ULift.ext (Prod.ext he1 hb)
  have hi' : i' = (ofGraph G).other i :=
    ULift.ext <| Prod.ext he1.symm (Bool.eq_not_iff.2 hb.symm)
  rw [hi', incMapOfGraphEmb_other] at hij
  exact ((ofGraph H).other_ne _).elim hij.symm

/-- Transport `E(G)` along `ofGraph_edgeSet`. -/
def edgeEmbeddingOfGraphEmb (F : G.Emb H) : E(ofGraph G) ↪ E(ofGraph H) :=
  (Set.equivOfEq (ofGraph_edgeSet G)).toEmbedding.trans <|
    F.edgeEmbedding.trans (Set.equivOfEq (ofGraph_edgeSet H)).symm.toEmbedding

lemma edgeEmbeddingOfGraphEmb_val (F : G.Emb H) (e : E(ofGraph G)) :
    (edgeEmbeddingOfGraphEmb F e).1 =
      (F.edgeMap ((Set.equivOfEq (ofGraph_edgeSet G)) e)).1 :=
  rfl

/-- Lift a coarse graph embedding to a heterogeneous embedding of the chosen presentations. -/
noncomputable def ofGraphIsoEmbedding (F : G.Emb H) : IsoEmbedding (ofGraph G) (ofGraph H) where
  vertexEmbedding := F.vertEmbedding
  edgeEmbedding := edgeEmbeddingOfGraphEmb F
  incidenceEmbedding := ⟨incMapOfGraphEmb F, incMapOfGraphEmb_injective F⟩
  map_attach i := Subtype.ext (incMapOfGraphEmb_attach F i).symm
  map_edge i := by
    apply Subtype.ext
    have hE : Set.equivOfEq (ofGraph_edgeSet G)
        ⟨(ofGraph G).edgeMap i, (ofGraph G).edgeMap_mem_edgeSet i⟩ = i.down.1 :=
      Subtype.ext rfl
    rw [edgeEmbeddingOfGraphEmb_val, hE]
    exact (incMapOfGraphEmb_edge F i).symm

lemma incMapOfGraphEmb_down_fst (F : G.Emb H) (i : ULift.{uV} (E(G) × Bool)) :
    (incMapOfGraphEmb F i).down.1 = F.edgeMap i.down.1 := by
  rw [incMapOfGraphEmb_eq_ite]
  split_ifs <;> rfl

lemma incMapOfGraphEmb_toEmb_leftInverse (F : Graph.Iso G H) :
    Function.LeftInverse (incMapOfGraphEmb F.symm.toEmb) (incMapOfGraphEmb F.toEmb) := by
  intro i
  have hi : incMapUnflipped F.symm.toEmb (incMapUnflipped F.toEmb i) = i :=
    ULift.ext <| Prod.ext (F.edgeMap_leftInverse i.down.1) rfl
  have hv : (ofGraph G).attach i =
        (F.symm.vertMap ⟨(ofGraph H).attach (incMapUnflipped F.toEmb i),
          (ofGraph H).attach_mem _⟩).1 ↔
      (ofGraph H).attach (incMapUnflipped F.toEmb i) =
        (F.vertMap ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩).1 := by
    constructor
    · intro h
      have h' := congrArg F.vertMap
        (show ⟨(ofGraph G).attach i, (ofGraph G).attach_mem i⟩ = _ from Subtype.ext h)
      simpa [Graph.Iso.symm] using (congrArg Subtype.val h').symm
    · intro h
      have h' := congrArg F.invVertMap
        (show ⟨(ofGraph H).attach (incMapUnflipped F.toEmb i),
          (ofGraph H).attach_mem _⟩ = _ from Subtype.ext h)
      simpa [Graph.Iso.symm] using (congrArg Subtype.val h').symm
  rw [incMapOfGraphEmb_eq_ite F.toEmb]
  split_ifs with h
  · rw [incMapOfGraphEmb_eq_ite, hi, ite_eq_left (hv.mpr h)]
  · rw [incMapOfGraphEmb_other, incMapOfGraphEmb_eq_ite, hi,
      ite_eq_right (mt hv.mp h), other_other]

lemma incMapOfGraphEmb_toEmb_rightInverse (F : Graph.Iso G H) :
    Function.RightInverse (incMapOfGraphEmb F.symm.toEmb) (incMapOfGraphEmb F.toEmb) :=
  incMapOfGraphEmb_toEmb_leftInverse F.symm

/-- The incidence equivalence underlying `isoOfGraph`. -/
noncomputable def incidenceEquivOfGraphIso (F : Graph.Iso G H) :
    ULift.{uV} (E(G) × Bool) ≃ ULift.{uV'} (E(H) × Bool) where
  toFun := incMapOfGraphEmb F.toEmb
  invFun := incMapOfGraphEmb F.symm.toEmb
  left_inv := incMapOfGraphEmb_toEmb_leftInverse F
  right_inv := incMapOfGraphEmb_toEmb_rightInverse F

noncomputable def vertexEquivOfGraphIso (F : Graph.Iso G H) :
    V(ofGraph G) ≃ V(ofGraph H) :=
  (Set.equivOfEq (ofGraph_vertexSet G)).trans <|
    F.vertEquiv.trans (Set.equivOfEq (ofGraph_vertexSet H)).symm

noncomputable def edgeEquivOfGraphIso (F : Graph.Iso G H) :
    E(ofGraph G) ≃ E(ofGraph H) :=
  (Set.equivOfEq (ofGraph_edgeSet G)).trans <|
    F.edgeEquiv.trans (Set.equivOfEq (ofGraph_edgeSet H)).symm

/-- Lift a graph isomorphism to an isomorphism of the chosen incidence presentations.

This is `ofGraphIsoEmbedding F.toEmb` with the inverse supplied by `F.symm`. -/
noncomputable def isoOfGraph (F : Graph.Iso G H) : (ofGraph G).Iso (ofGraph H) where
  vertexEquiv := vertexEquivOfGraphIso F
  edgeEquiv := edgeEquivOfGraphIso F
  incidenceEquiv := incidenceEquivOfGraphIso F
  map_attach i := by
    apply Subtype.ext
    simp [vertexEquivOfGraphIso]
    exact (incMapOfGraphEmb_attach F.toEmb i).symm
  map_edge i := by
    apply Subtype.ext
    simp [edgeEquivOfGraphIso]
    exact (incMapOfGraphEmb_edge F.toEmb i).symm

lemma incMapOfGraphEmb_ofLe {G H : Graph V E} (h : H ≤ G) (i : ULift.{uV} (E(H) × Bool)) :
    incMapOfGraphEmb (Emb.ofLe h) i =
      if (ofGraph G).attach (incMapUnflipped (Emb.ofLe h) i) = (ofGraph H).attach i then
        incMapUnflipped (Emb.ofLe h) i
      else (ofGraph G).other (incMapUnflipped (Emb.ofLe h) i) := by
  rw [incMapOfGraphEmb_eq_ite]
  rfl

lemma incMapUnflipped_ofLe_comp {G H K : Graph V E} (hHK : K ≤ H) (hHG : H ≤ G)
    (i : ULift.{uV} (E(K) × Bool)) :
    incMapUnflipped (Emb.ofLe hHG) (incMapUnflipped (Emb.ofLe hHK) i) =
      incMapUnflipped (Emb.ofLe (hHK.trans hHG)) i := by
  refine ULift.ext (Prod.ext ?_ rfl)
  apply Subtype.ext
  calc
    ((Emb.ofLe hHG).edgeMap (incMapUnflipped (Emb.ofLe hHK) i).down.1).1 =
        (incMapUnflipped (Emb.ofLe hHK) i).down.1.1 :=
      rfl
    _ = ((Emb.ofLe hHK).edgeMap i.down.1).1 := rfl
    _ = i.down.1.1 := rfl
    _ = ((Emb.ofLe (hHK.trans hHG)).edgeMap i.down.1).1 := rfl

end Graph.Presentation
