module

public import Matroid.Graph.Iso.Hom
public import Matroid.Graph.Planarity.Realization.Basic

/-!
# Transporting realizations along a graph isomorphism

An isomorphism `F : Iso K G` matches up vertices and edges, but it need not respect the *chosen*
orientation `edgeSource`/`edgeTarget` of an edge. This file records that discrepancy as
`Graph.Iso.sameOrientation`, uses it to build the reparametrisation `Graph.Iso.orient` of the unit
interval, and assembles the two into

* `Graph.Iso.preRealizationMap`, the induced continuous map on pre-realizations, and
* `Graph.Iso.realizationHomeomorph`, the induced homeomorphism of weak realizations.

`Matroid.Graph.Planarity.Drawing` consumes the last of these to pull a drawing back along an
isomorphism.
-/

@[expose] public section

open Function Set Topology
open scoped unitInterval

namespace Graph

noncomputable section

variable {α β γ δ : Type*} {G : Graph α β} {K : Graph γ δ}

namespace Iso

open unitInterval

lemma isLink_vert_edge (F : Iso K G) (e : E(K)) :
    G.IsLink (F.edgeEquiv e) (F.vertexEquiv (edgeSource e)) (F.vertexEquiv (edgeTarget e)) := by
  rw [← F.isLink_edgeEquiv_vertexEquiv e ..]
  exact isLink_edgeSource_edgeTarget e

/-! ### Orientation -/

/-- Whether `F` sends the preferred orientation of `e` to that of its image. -/
abbrev sameOrientation (F : Iso K G) (e : E(K)) : Prop :=
  F.vertexEquiv (edgeSource e) = edgeSource (F.edgeEquiv e)

lemma sameOrientation_or_swap (F : Iso K G) (e : E(K)) :
    F.sameOrientation e ∨
      (F.vertexEquiv (edgeSource e) = edgeTarget (F.edgeEquiv e) ∧
        F.vertexEquiv (edgeTarget e) = edgeSource (F.edgeEquiv e)) := by
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ :=
    (isLink_edgeSource_edgeTarget (F.edgeEquiv e)).eq_and_eq_or_eq_and_eq (F.isLink_vert_edge e)
  · exact Or.inl <| Subtype.ext h₁.symm
  · exact Or.inr ⟨Subtype.ext h₂.symm, Subtype.ext h₁.symm⟩

lemma vert_edgeTarget_of_sameOrientation (F : Iso K G) {e : E(K)} (h : F.sameOrientation e) :
    F.vertexEquiv (edgeTarget e) = edgeTarget (F.edgeEquiv e) := by
  obtain ⟨_, h₂⟩ | ⟨h₁, h₂⟩ :=
    (isLink_edgeSource_edgeTarget (F.edgeEquiv e)).eq_and_eq_or_eq_and_eq (F.isLink_vert_edge e)
  · exact Subtype.ext h₂.symm
  · have hsrc : F.vertexEquiv (edgeSource e) = F.vertexEquiv (edgeTarget e) := by
      rw [h, Subtype.ext_iff.mpr h₁]
    exact hsrc.symm.trans (Subtype.ext h₂.symm)

lemma vert_of_not_sameOrientation (F : Iso K G) {e : E(K)} (h : ¬ F.sameOrientation e) :
    F.vertexEquiv (edgeSource e) = edgeTarget (F.edgeEquiv e) ∧
      F.vertexEquiv (edgeTarget e) = edgeSource (F.edgeEquiv e) :=
  (F.sameOrientation_or_swap e).resolve_left h

lemma sameOrientation_symm (F : Iso K G) {e : E(K)} (h : F.sameOrientation e) :
    F.symm.sameOrientation (F.edgeEquiv e) := by
  unfold sameOrientation at h ⊢
  simpa [vertexEquiv_symm_apply_apply, edgeEquiv_symm_apply_apply] using
    congrArg F.symm.vertexEquiv h.symm

lemma not_sameOrientation_symm (F : Iso K G) {e : E(K)} (h : ¬ F.sameOrientation e) :
    ¬ F.symm.sameOrientation (F.edgeEquiv e) := by
  intro hs
  unfold sameOrientation at hs
  have hs' : F.symm.vertexEquiv (edgeSource (F.edgeEquiv e)) = edgeSource e := by
    simpa [edgeEquiv_symm_apply_apply] using hs
  have : F.vertexEquiv (edgeSource e) = edgeSource (F.edgeEquiv e) := by
    simpa [vertexEquiv_apply_symm_apply] using congrArg F.vertexEquiv hs'.symm
  exact h this

lemma sameOrientation_edge_symm (F : Iso K G) (e : E(G)) :
    F.sameOrientation (F.symm.edgeEquiv e) ↔ F.symm.sameOrientation e := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> unfold sameOrientation at h ⊢
  · have h' : F.vertexEquiv (edgeSource (F.symm.edgeEquiv e)) = edgeSource e := by
      simpa [edgeEquiv_apply_symm_apply] using h
    simpa [vertexEquiv_symm_apply_apply] using congrArg F.symm.vertexEquiv h'.symm
  · have := congrArg F.vertexEquiv h
    simpa [vertexEquiv_apply_symm_apply, edgeEquiv_apply_symm_apply] using this.symm

/-! ### Reparametrisation of edges -/

/-- Reparametrization of the unit interval along `e`, flipping if `F` reverses orientation. -/
noncomputable def orient (F : Iso K G) (e : E(K)) : I → I :=
  open Classical in fun t ↦ if F.sameOrientation e then t else σ t

lemma continuous_orient (F : Iso K G) (e : E(K)) : Continuous (F.orient e) := by
  classical
  by_cases h : F.sameOrientation e
  · convert continuous_id (X := I)
    ext t
    simp [orient, ite_eq_left h]
  · convert continuous_symm
    ext t
    simp [orient, ite_eq_right h]

lemma orient_symm_orient (F : Iso K G) (e : E(K)) (t : I) :
    F.symm.orient (F.edgeEquiv e) (F.orient e t) = t := by
  by_cases h : F.sameOrientation e
  · simp [orient, ite_eq_left h, ite_eq_left (F.sameOrientation_symm h)]
  · simp [orient, ite_eq_right h, ite_eq_right (F.not_sameOrientation_symm h), symm_symm]

lemma orient_orient_symm (F : Iso K G) (e : E(G)) (t : I) :
    F.orient (F.symm.edgeEquiv e) (F.symm.orient e t) = t := by
  by_cases h : F.symm.sameOrientation e
  · simp [orient, ite_eq_left h, ite_eq_left ((F.sameOrientation_edge_symm e).mpr h)]
  · simp [orient, ite_eq_right h, ite_eq_right (mt (F.sameOrientation_edge_symm e).mp h), symm_symm]

/-! ### The induced maps on realizations -/

/-- The induced map on pre-realizations. -/
noncomputable def preRealizationMap (F : Iso K G) : C(K.PreRealization, G.PreRealization) where
  toFun
    | .inl v => .inl (F.vertexEquiv v)
    | .inr ⟨e, t⟩ => .inr ⟨F.edgeEquiv e, F.orient e t⟩
  continuous_toFun := continuous_sum_dom.mpr ⟨continuous_of_discreteTopology,
    continuous_sigma_iff.mpr fun e ↦ continuous_inr.comp <|
      continuous_sigmaMk.comp (F.continuous_orient e)⟩

lemma preRealizationMap_glueRel (F : Iso K G) ⦃a b : K.PreRealization⦄
    (h : K.glueRel a b) : G.glueRel (F.preRealizationMap a) (F.preRealizationMap b) := by
  classical
  induction h with
  | refl => rfl
  | symm _ _ _ ih => exact Setoid.symm ih
  | trans _ _ _ _ _ h₁ h₂ => exact Setoid.trans h₁ h₂
  | rel x y hxy =>
    match x, y with
    | .inr _, _ => simp [glueRelAux] at hxy
    | .inl u, .inl v => rw [(glueRelAux_inl_inl_iff ..).mp hxy]
    | .inl u, .inr ⟨e, t⟩ =>
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (glueRelAux_inl_inr_iff ..).mp hxy <;>
        by_cases hori : F.sameOrientation e
      · convert (glueRel_inl_inr_iff (edgeSource (F.edgeEquiv e)) (F.edgeEquiv e) 0).mpr
          (.inl ⟨rfl, rfl⟩) using 1
        · simpa only [preRealizationMap, ContinuousMap.coe_mk, Sum.inl.injEq] using hori
        · simp [preRealizationMap, orient, ite_eq_left hori]
      · obtain ⟨hs, _⟩ := F.vert_of_not_sameOrientation hori
        convert (glueRel_inl_inr_iff (edgeTarget (F.edgeEquiv e)) (F.edgeEquiv e) 1).mpr
          (.inr ⟨rfl, rfl⟩) using 1
        · simpa [preRealizationMap] using hs
        · simp [preRealizationMap, orient, ite_eq_right hori]
      · convert (glueRel_inl_inr_iff (edgeTarget (F.edgeEquiv e)) (F.edgeEquiv e) 1).mpr
          (.inr ⟨rfl, rfl⟩) using 1
        · simpa [preRealizationMap] using F.vert_edgeTarget_of_sameOrientation hori
        · simp [preRealizationMap, orient, ite_eq_left hori]
      · obtain ⟨_, ht⟩ := F.vert_of_not_sameOrientation hori
        convert (glueRel_inl_inr_iff (edgeSource (F.edgeEquiv e)) (F.edgeEquiv e) 0).mpr
          (.inl ⟨rfl, rfl⟩) using 1
        · simpa [preRealizationMap] using ht
        · simp [preRealizationMap, orient, ite_eq_right hori]

lemma preRealizationMap_symm_comp (F : Iso K G) (x : K.PreRealization) :
    F.symm.preRealizationMap (F.preRealizationMap x) = x := by
  match x with
  | .inl v => simp only [preRealizationMap, ContinuousMap.coe_mk, vertexEquiv_symm_apply_apply]
  | .inr ⟨e, t⟩ =>
    simp only [preRealizationMap, ContinuousMap.coe_mk, edgeEquiv_symm_apply_apply,
      orient_symm_orient]

lemma preRealizationMap_comp_symm (F : Iso K G) (x : G.PreRealization) :
    F.preRealizationMap (F.symm.preRealizationMap x) = x := by
  match x with
  | .inl v => simp only [preRealizationMap, ContinuousMap.coe_mk, vertexEquiv_apply_symm_apply]
  | .inr ⟨e, t⟩ =>
    simp only [preRealizationMap, ContinuousMap.coe_mk, edgeEquiv_apply_symm_apply,
      orient_orient_symm]

/-- The homeomorphism of weak realizations induced by a graph isomorphism. -/
noncomputable def realizationHomeomorph (F : Iso K G) : Realization K ≃ₜ Realization G where
  toFun := Quotient.map F.preRealizationMap F.preRealizationMap_glueRel
  invFun := Quotient.map F.symm.preRealizationMap F.symm.preRealizationMap_glueRel
  left_inv x := by
    induction x using Realization.ind with | h a =>
    exact congrArg (Realization.mk K) (F.preRealizationMap_symm_comp a)
  right_inv x := by
    induction x using Realization.ind with | h a =>
    exact congrArg (Realization.mk G) (F.preRealizationMap_comp_symm a)
  continuous_toFun :=
    continuous_coinduced_dom.mpr <| continuous_coinduced_rng.comp F.preRealizationMap.continuous
  continuous_invFun := continuous_coinduced_dom.mpr <|
    continuous_coinduced_rng.comp F.symm.preRealizationMap.continuous

end Iso

end

end Graph
