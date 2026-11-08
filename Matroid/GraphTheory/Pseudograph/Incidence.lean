module

public import Matroid.GraphTheory.Pseudograph.toGraph
public import Matroid.GraphTheory.HypergraphLike.Orientation

/-!
# Incidences of a pseudograph

Incidence fibres and their pairing use the incidence subset of `Pseudograph`.
Unused ambient labels contribute no incidences or realization points.
The chosen endpoints of an incidence or orientation form a link in the coarse graph.
-/

open HypergraphLike

@[expose] public section

open Set Function

namespace Pseudograph

variable {V I E : Type*} {P : Pseudograph V I E} {i j : P.incidenceSet}

lemma mem_edgeSet_iff {e : E} : e ∈ E(P) ↔ ∃ i : I(P), P.edgeMap' i = e := by
  change e ∈ P.edgeSet ↔ _
  rw [← P.edgeMap_range]
  rfl

/-- Describe the ordinary graph link using one of its two incidences. -/
lemma toGraph_isLink_iff {e : E} {x y : V} :
    P.toGraph.IsLink e x y ↔
      ∃ i : I(P), P.edgeMap' i = e ∧ P.attach' i = x ∧ P.attach' (P.other' i) = y := by
  constructor
  · rintro ⟨l⟩
    let i : I(P) := ⟨l.source, l.isSource_source⟩
    let j : I(P) := ⟨l.target, l.isTarget_target⟩
    have hj : j = P.other' i :=
      (P.edgeMap'_eq i j (l.edgeMap'_source.trans l.edgeMap'_target.symm)).resolve_left
        (fun h ↦ l.source_ne_target (congrArg Subtype.val h).symm)
    exact ⟨i, l.edgeMap'_source, l.attach'_source, hj ▸ l.attach'_target⟩
  · rintro ⟨i, he, hx, hy⟩
    exact ⟨⟨i.val, (P.other' i).val, (Subtype.coe_ne_coe.mpr (P.other'_ne i)).symm,
      i.property, (P.other' i).property, he, (P.edgeMap'_other' i).trans he, hx, hy⟩⟩

lemma isLink_edgeMap_attach (P : Pseudograph V I E) (i : I(P)) :
    P.toGraph.IsLink (P.edgeMap' i) (P.attach' i) (P.attach' (P.other' i)) :=
  toGraph_isLink_iff.mpr ⟨i, rfl, rfl, rfl⟩

end Pseudograph

variable {V I E : Type*} {P : Pseudograph V I E} {e : E}

namespace HypergraphLike.IncidenceAt

lemma isLink_source_target (i : IncidenceAt P e) :
    P.toGraph.IsLink e i.source i.target :=
  Pseudograph.toGraph_isLink_iff.mpr ⟨i.1, i.2, rfl, rfl⟩

end HypergraphLike.IncidenceAt

namespace HypergraphLike.Orientation

lemma isLink_source_target (O : Orientation P) (e : E(P)) :
    P.toGraph.IsLink e (O.source e) (O.target e) :=
  (O e).isLink_source_target

end HypergraphLike.Orientation

namespace Pseudograph

-- namespace Equiv

-- /-- Incidence relabelling restricts to an equivalence of the fibres over every ambient edge. -/
-- def incidenceAtEquiv (F : P.Equiv Q) (e : E) : (IncidenceAt P) e ≃ (IncidenceAt Q) e where
--   toFun i := ⟨F.incEquiv i.1, by
--     calc
--       Q.edgeMap' (F.incEquiv i.1) = P.edgeMap' i.1 := F.edge_eq i.1
--       _ = e := i.2⟩
--   invFun j := ⟨F.incEquiv.symm j.1, by
--     have h := F.edge_eq (F.incEquiv.symm j.1)
--     calc
--       P.edgeMap' (F.incEquiv.symm j.1) = Q.edgeMap' j.1 := by simpa using h.symm
--       _ = e := j.2⟩
--   left_inv i := by
--     apply Subtype.ext
--     simp
--   right_inv j := by
--     apply Subtype.ext
--     simp

-- @[simp]
-- lemma incidenceAtEquiv_other (F : P.Equiv Q) (e : E) (i : (IncidenceAt P) e) :
--     F.incidenceAtEquiv e i.other = (F.incidenceAtEquiv e i).other := by
--   apply Subtype.ext
--   exact F.map_other i.1

-- /-- Transport a global orientation through an incidence relabelling. -/
-- def mapOrientation (F : P.Equiv Q) (O : (Orientation P)) : (Orientation Q) :=
--   fun e ↦ F.incidenceAtEquiv e.1 (O (F.edgeEquiv.symm e))

-- @[simp]
-- lemma mapOrientation_apply_val (F : P.Equiv Q) (O : (Orientation P)) (e : E(Q)) :
--     (F.mapOrientation O e).1 = F.incEquiv (O (F.edgeEquiv.symm e)).1 :=
--   rfl

-- @[simp]
-- lemma mapOrientation_reverse (F : P.Equiv Q) (O : (Orientation P)) :
--     F.mapOrientation O.reverse = (F.mapOrientation O).reverse := by
--   funext e
--   apply Subtype.ext
--   exact F.map_other _

-- end Equiv


end Pseudograph
