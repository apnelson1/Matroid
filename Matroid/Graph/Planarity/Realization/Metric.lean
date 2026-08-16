module

public import Matroid.Graph.Planarity.Realization.Basic

/-!
# The unit-edge metric realization of a graph

This file equips a tagged copy `Graph.Realization.Metric G` of the point-set realization with the
intrinsic extended path metric in which every edge has length one.  In particular, it deliberately
does not install an `EMetricSpace` instance on the raw quotient `Graph.Realization G`; its quotient
topology and this metric topology can therefore coexist without an instance diamond.
-/

@[expose] public section

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path WList Classical ENNReal
open scoped unitInterval

namespace Graph

variable {α β : Type*} {G : Graph α β} {e : E(G)} {t t' : I} {u v : V(G)}
  {w x y z : G.PreRealization}

namespace Realization

/-- The realization of `G` carrying the intrinsic unit-edge extended metric. -/
def Metric (G : Graph α β) := G.Realization

namespace Metric

/-- Reinterpret a point-set realization as a metric realization. -/
@[match_pattern, implicit_reducible]
def ofRealization : G.Realization ≃ Metric G := Equiv.refl _

/-- Forget the metric topology tag. -/
@[match_pattern, implicit_reducible]
def toRealization : Metric G ≃ G.Realization := Equiv.refl _

end Metric

end Realization

/-- Distance from a pre-realization point to a vertex: graph distance to an endpoint, plus
parameter along the incident edge (when the point lies on an edge). -/
noncomputable def distToVtx (G : Graph α β) (x : PreRealization G) (v : V(G)) : ℝ≥0∞ :=
  match x with
  | Sum.inl w => G.eDist w.val v.val
  | Sum.inr ⟨e, t⟩ => min (G.eDist (edgeSource e).val v.val + ENNReal.ofReal (t : ℝ))
      (G.eDist (edgeTarget e).val v.val + ENNReal.ofReal (1 - (t : ℝ)))

@[simp]
lemma distToVtx_inl_left (u v : V(G)) : distToVtx G (Sum.inl u) v = G.eDist u.val v.val := rfl

/-- Direct distance: `0` for identical vertices, `|t₁ - t₂|` on the same closed edge, otherwise `⊤`.
The full distance is `min` of this with an infimum over vertex detours. -/
noncomputable def directDist (G : Graph α β) (x y : PreRealization G) : ℝ≥0∞ :=
  match x, y with
  | Sum.inl v, Sum.inl w => if v = w then 0 else ⊤
  | Sum.inr ⟨e₁, t₁⟩, Sum.inr ⟨e₂, t₂⟩ =>
    if e₁ = e₂ then ENNReal.ofReal |(t₁ : ℝ) - (t₂ : ℝ)| else ⊤
  | _, _ => ⊤

lemma directDist_comm (G : Graph α β) (x y : PreRealization G) :
    directDist G x y = directDist G y x := by
  cases x <;> cases y <;> simp [directDist, eq_comm, abs_sub_comm]

/-- Intrinsic extended distance: shortest path metric as `min` of the direct segment distance and
`⨅ v, distToVtx x v + distToVtx y v`. -/
noncomputable def preRealizationEDist (G : Graph α β) (a b : PreRealization G) : ℝ≥0∞ :=
  min (directDist G a b) (⨅ v : V(G), distToVtx G a v + distToVtx G b v)

private lemma distToVtx_triangle (x : PreRealization G) (v w : V(G)) :
    distToVtx G x v ≤ distToVtx G x w + (G.eDist w.val v.val : ℝ≥0∞) := by
  match x with
  | inl u =>
    simp only [distToVtx, ← ENat.toENNReal_add, ENat.toENNReal_le]
    exact G.eDist_triangle u.val w.val v.val
  | inr ⟨e, t⟩ =>
    refine le_trans (min_le_min ?_ ?_) <| (min_add_add_right _ _ _).le
    · have hs : (G.eDist (edgeSource e).val v.val : ℝ≥0∞) ≤
          (G.eDist (edgeSource e).val w.val : ℝ≥0∞) + (G.eDist w.val v.val : ℝ≥0∞) := by
        rw [← ENat.toENNReal_add, ENat.toENNReal_le]
        exact G.eDist_triangle (edgeSource e).val w.val v.val
      exact (add_le_add_left hs _).trans (le_of_eq (by ring))
    have ht : (G.eDist (edgeTarget e).val v.val : ℝ≥0∞) ≤
        (G.eDist (edgeTarget e).val w.val : ℝ≥0∞) + (G.eDist w.val v.val : ℝ≥0∞) := by
      rw [← ENat.toENNReal_add, ENat.toENNReal_le]
      exact G.eDist_triangle (edgeTarget e).val w.val v.val
    exact (add_le_add ht le_rfl).trans (le_of_eq (by ring))

private lemma iInf_distToVtx_add (x y : PreRealization G) :
    (⨅ v : V(G), distToVtx G x v + distToVtx G y v) = match x with
    | Sum.inl u => distToVtx G y u
    | Sum.inr ⟨e, t⟩ => min (ENNReal.ofReal (t : ℝ) + distToVtx G y (edgeSource e))
      (ENNReal.ofReal (1 - (t : ℝ)) + distToVtx G y (edgeTarget e)) := by
  match x with
  | Sum.inl u =>
    refine le_antisymm ?_ <| le_iInf fun v ↦ ?_
    · exact iInf_le _ u |>.trans <| by simp [distToVtx, G.eDist_self u.prop]
    simpa [distToVtx, add_comm, G.eDist_comm v.val u.val] using distToVtx_triangle y u v
  | Sum.inr ⟨e, t⟩ =>
    conv in G.distToVtx (inr ⟨e, t⟩) _ + G.distToVtx y _ =>
      rw [distToVtx, add_comm _ (ENNReal.ofReal _), add_comm _ (ENNReal.ofReal _)]
      exact (min_add_add_right _ _ _).symm
    convert iInf_inf_eq
    · rfl
    all_goals
    · simp_rw [add_assoc, ← ENNReal.add_iInf]
      change _ = _ + (⨅ v, distToVtx G (Sum.inl _) v  + _)
      exact congr_arg (ENNReal.ofReal _ + ·) <| by rw [iInf_distToVtx_add]

@[simp]
lemma preRealizationEDist_inl_left (u : V(G)) (x : PreRealization G) :
    preRealizationEDist G (Sum.inl u) x = distToVtx G x u := by
  unfold preRealizationEDist
  rw [iInf_distToVtx_add]
  simp only [inf_eq_right]
  match x with
  | Sum.inl v =>
    obtain rfl | h := eq_or_ne u v
    · simp only [distToVtx, directDist, ↓reduceIte, nonpos_iff_eq_zero]
      norm_cast
      simp
    simp [distToVtx, directDist, h]
  | Sum.inr ⟨e, t⟩ => simp [directDist]

@[simp]
lemma preRealizationEDist_inl_right (u : V(G)) (x : PreRealization G) :
    preRealizationEDist G x (Sum.inl u) = distToVtx G x u := by
  unfold preRealizationEDist
  rw [iInf_distToVtx_add]
  match x with
  | Sum.inl v =>
    obtain rfl | h := eq_or_ne v u
    · simp only [directDist, ↓reduceIte, zero_le, inf_of_le_left, distToVtx]
      norm_cast
      simp [eDist_self]
    simp [h, directDist, eDist_comm]
  | Sum.inr ⟨e, t⟩ =>
    simp only [directDist, le_top, inf_of_le_right, distToVtx]
    ring_nf
    rw [eDist_comm u.val, eDist_comm u.val]

lemma preRealizationEDist_comm (G : Graph α β) (x y : PreRealization G) :
    preRealizationEDist G x y = preRealizationEDist G y x := by
  match x, y with
  | .inl u, .inl v => rw [preRealizationEDist_inl_left, preRealizationEDist_inl_right]
  | .inl u, .inr ⟨e, t⟩ => rw [preRealizationEDist_inl_left, preRealizationEDist_inl_right]
  | .inr ⟨e, t⟩, .inl u => rw [preRealizationEDist_inl_left, preRealizationEDist_inl_right]
  | .inr ⟨e₁, t₁⟩, .inr ⟨e₂, t₂⟩ =>
    simp only [preRealizationEDist, directDist]
    simp_rw [eq_comm (a := e₁), abs_sub_comm, add_comm]

private lemma eDist_edgeSource_edgeTarget_le_one (e : E(G)) :
    G.eDist (edgeSource e).val (edgeTarget e).val ≤ 1 := by
  simpa [IsLink.walk_length, IsLink.walk_first, IsLink.walk_last, edgeSource, edgeTarget] using
    (G.isLink_source_target e.prop).walk_isWalk.eDist_le_length

private lemma directDist_triangle (x y z : PreRealization G) :
    directDist G x z ≤ directDist G x y + directDist G y z := by
  match x, y, z with
  | Sum.inl v, Sum.inl w, Sum.inl u =>
    obtain rfl | hvu := eq_or_ne v u
    · simp [directDist]
    grind [directDist, add_eq_top, zero_ne_top]
  | Sum.inr ⟨e₁, t₁⟩, Sum.inr ⟨e₂, t₂⟩, Sum.inr ⟨e₃, t₃⟩ =>
    obtain rfl | h13 := eq_or_ne e₁ e₃ <;> obtain rfl | h12 := eq_or_ne e₁ e₂
    · simp only [directDist, ↓reduceIte, ← ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ofReal_le_ofReal (abs_sub_le ..)
    · simp [directDist, h12.symm]
    · simp [directDist, h13]
    · simp [directDist, h12, h13]
  | Sum.inl _, Sum.inl _, Sum.inr _ => simp [directDist]
  | Sum.inl _, Sum.inr _, Sum.inl _ => simp [directDist]
  | Sum.inl _, Sum.inr _, Sum.inr _ => simp [directDist]
  | Sum.inr _, Sum.inl _, Sum.inl _ => simp [directDist]
  | Sum.inr _, Sum.inl _, Sum.inr _ => simp [directDist]
  | Sum.inr _, Sum.inr _, Sum.inl _ => simp [directDist]

private lemma distToVtx_le_directDist_add (x y : PreRealization G) (w : V(G)) :
    distToVtx G x w ≤ directDist G x y + distToVtx G y w := by
  obtain vx | ⟨ex, tx⟩ := x <;> obtain vy | ⟨ey, ty⟩ := y
  · obtain rfl | h := eq_or_ne vx vy
    · simp [directDist, distToVtx]
    · simp [directDist, h, distToVtx, top_add, le_top]
  · simp [directDist, distToVtx, top_add, le_top]
  · simp [directDist, distToVtx, top_add, le_top]
  obtain he | rfl := (eq_or_ne ex ey).symm
  · simp [he, directDist, distToVtx]
  simp only [directDist, distToVtx, ↓reduceIte]
  let ε : ℝ≥0∞ := ENNReal.ofReal |(tx : ℝ) - (ty : ℝ)|
  refine le_trans (min_le_min ?_ ?_) (min_add_add_left ..).le <;> rw [add_comm ε, add_assoc]
  <;> refine add_le_add_right ?_ _
  · rw [add_comm, ← ENNReal.ofReal_add (abs_nonneg _) ty.2.1]
    exact ofReal_le_ofReal (by linarith [le_abs_self (tx.val - ty.val)])
  rw [add_comm, ← ENNReal.ofReal_add (abs_nonneg _) (sub_nonneg.mpr ty.2.2)]
  exact ofReal_le_ofReal (by linarith [le_abs_self (ty.val - tx.val), abs_sub_comm tx.val ty.val])

private lemma eDist_le_distToVtx_add (x : PreRealization G) (v w : V(G)) :
    (G.eDist v.val w.val : ℝ≥0∞) ≤ distToVtx G x v + distToVtx G x w := by
  match x with
  | inl u =>
    simp_rw [distToVtx, ← ENat.toENNReal_add, ENat.toENNReal_le, eDist_comm u.val v]
    exact G.eDist_triangle v.val u.val w.val
  | inr ⟨e, t⟩ =>
    refine le_trans ?_ (min_add_add_right _ _ (min _ _)).le
    refine le_trans ?_ (congr_arg₂ min (min_add_add_left ..).symm (min_add_add_left ..).symm).ge
    have h_rearrange (A B t u : ℝ≥0∞) : A + ((t + u) + B) = (A + t) + (B + u) := by ring
    have ht1 : (ENNReal.ofReal (t : ℝ) + ENNReal.ofReal (1 - (t : ℝ)) : ℝ≥0∞) = 1 := by
      simp [← ENNReal.ofReal_add (t : I).2.1 (sub_nonneg.mpr (t : I).2.2)]
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    on_goal 2 =>
      refine le_trans ?_ <| (h_rearrange ..).le
      simp only [← ENNReal.ofReal_add t.2.1 (sub_nonneg.mpr t.2.2), add_sub_cancel, ofReal_one]
      norm_cast
      refine (G.eDist_triangle v.val (edgeSource e).val w.val).trans ?_
      refine add_le_add le_rfl
        (G.eDist_triangle (edgeSource e).val (edgeTarget e).val w.val) |>.trans ?_
      rw [eDist_comm]
      exact add_le_add le_rfl (add_le_add (eDist_edgeSource_edgeTarget_le_one e) le_rfl)
    on_goal 2 =>
      refine le_trans ?_ <| (h_rearrange ..).le
      simp only [← ENNReal.ofReal_add (sub_nonneg.mpr t.2.2) t.2.1, sub_add_cancel, ofReal_one]
      norm_cast
      refine (G.eDist_triangle v.val (edgeTarget e).val w.val).trans ?_
      refine add_le_add le_rfl
        (G.eDist_triangle (edgeTarget e).val (edgeSource e).val w.val) |>.trans ?_
      rw [eDist_comm, eDist_comm (edgeTarget e).val (edgeSource e).val]
      exact add_le_add le_rfl (add_le_add (eDist_edgeSource_edgeTarget_le_one e) le_rfl)
    all_goals
      refine le_trans ?_ <| add_le_add le_self_add le_self_add
      norm_cast
      rw [eDist_comm _ v.val]
      exact G.eDist_triangle v.val _ w.val

private instance h1 : AddRightMono ℝ≥0∞ := IsOrderedAddMonoid.toAddRightMono
private instance h2 : AddLeftMono ℝ≥0∞ := IsOrderedAddMonoid.toAddLeftMono

private lemma preRealizationEDist_triangle (x y z : PreRealization G) :
    preRealizationEDist G x z ≤ preRealizationEDist G x y + preRealizationEDist G y z := by
  conv_rhs => unfold preRealizationEDist; exact (@min_add_add_right _ _ _ h1 ..).symm
  conv => right; left; exact (@min_add_add_left _ _ _ h2 ..).symm
  conv => right; right; exact (@min_add_add_left _ _ _ h2 ..).symm
  refine le_min (le_min ((min_le_left ..).trans <| directDist_triangle ..) ?_) (le_min ?_ ?_)
  <;> refine (min_le_right ..).trans ?_ <;> simp only [add_iInf, add_assoc, iInf_add]
  · simp_rw [← add_assoc]
    exact iInf_mono fun _ ↦ add_le_add_left (distToVtx_le_directDist_add ..) _
  · refine iInf_mono fun _ ↦ add_le_add_right ?_ _
    rw [add_comm, directDist_comm]
    exact distToVtx_le_directDist_add ..
  exact le_iInf₂ fun v w ↦ (iInf_le _ w).trans<|add_le_add_right ((G.distToVtx_triangle z w v).trans
  <| (add_le_add le_rfl (eDist_le_distToVtx_add y v w)).trans (le_of_eq <| by ring) ) _

@[simp]
private lemma preRealizationEDist_zero_iff (x y : PreRealization G) :
    preRealizationEDist G x y = 0 ↔ G.glueRel x y := by
  match x, y with
  | .inl v, .inl w =>
    simp only [preRealizationEDist_inl_right, distToVtx_inl_left, glueRel_inl_iff_glueRelAux,
      glueRelAux_inl_inl_iff]
    norm_cast
    simp [Subtype.coe_inj]
  | .inl v, .inr ⟨e, t⟩ =>
    simp only [preRealizationEDist_inl_left, distToVtx, min_eq_zero, add_eq_zero,
      ofReal_eq_zero, unitInterval.val_le_zero_iff, tsub_le_iff_right, zero_add,
      unitInterval.one_le_val_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff, inl.injEq,
      exists_eq_left']
    norm_cast
    simp only [eDist_eq_zero_iff, Subtype.coe_inj, Subtype.coe_prop, and_true]
    tauto
  | .inr ⟨e, t⟩, .inl v =>
    simp only [preRealizationEDist_inl_right, distToVtx, min_eq_zero, add_eq_zero,
      ofReal_eq_zero, unitInterval.val_le_zero_iff, tsub_le_iff_right, zero_add,
      unitInterval.one_le_val_iff, glueRel_inr_inl_iff]
    norm_cast
    simp only [eDist_eq_zero_iff, Subtype.coe_inj, Subtype.coe_prop]
    tauto
  | .inr ⟨e₁, t₁⟩, .inr ⟨e₂, t₂⟩ =>
    simp only [preRealizationEDist, iInf_distToVtx_add]
    simp only [directDist, distToVtx, min_eq_zero, add_eq_zero, ofReal_eq_zero,
      unitInterval.val_le_zero_iff, tsub_le_iff_right, zero_add, unitInterval.one_le_val_iff,
      glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff, inl.injEq,
      exists_eq_left', Subtype.exists]
    norm_cast
    simp only [eDist_eq_zero_iff, Subtype.coe_prop, and_true]
    grind only [Subtype.coe_inj, top_ne_zero, ofReal_eq_zero, !abs_nonpos_iff, sub_eq_zero]

private lemma preRealizationEDist_eq_of_glueRel (h : G.glueRel x y) (z : PreRealization G) :
    preRealizationEDist G x z = preRealizationEDist G y z := by
  rw [← preRealizationEDist_zero_iff] at h
  refine le_antisymm ?_  ?_
  · refine preRealizationEDist_triangle _ y _ |>.trans ?_
    rw [h, zero_add]
  refine preRealizationEDist_triangle _ x _ |>.trans ?_
  rw [preRealizationEDist_comm, h, zero_add]

theorem preRealizationEDist_respects_quotient (a₁ a₂ b₁ b₂ : G.PreRealization)
    (ha : G.glueRel a₁ b₁) (hb : G.glueRel a₂ b₂) :
    G.preRealizationEDist a₁ a₂ = G.preRealizationEDist b₁ b₂ :=
  (preRealizationEDist_eq_of_glueRel ha a₂).trans <|
    (G.preRealizationEDist_comm b₁ a₂).trans <|
      (preRealizationEDist_eq_of_glueRel hb b₁).trans (G.preRealizationEDist_comm b₂ b₁)

/-- Extended distance on the point-set realization, induced by graph distance and unit edges. -/
noncomputable def Realization.edist (G : Graph α β) (x y : G.Realization) : ℝ≥0∞ :=
  Quotient.lift₂ G.preRealizationEDist preRealizationEDist_respects_quotient x y

/--
The extended metric structure on the point-set realization.

This is a named structure, not an instance: the instance is installed only on
`Graph.Realization.Metric G`.
-/
@[instance_reducible]
noncomputable def Realization.eMetricSpace (G : Graph α β) : EMetricSpace G.Realization where
  edist := Realization.edist G
  edist_self x := Quotient.inductionOn₂ x x fun x y ↦ by simp [Realization.edist]
  edist_comm := Quotient.ind₂ fun x y ↦ by simp [Realization.edist, preRealizationEDist_comm]
  edist_triangle := Quotient.ind₂ fun x y ↦ Quotient.ind fun z ↦ by
    simp [Realization.edist, preRealizationEDist_triangle]
  eq_of_edist_eq_zero {x y} := Quotient.inductionOn₂ x y fun x y ↦ by
    simp [Realization.edist, preRealizationEDist_zero_iff, Quotient.eq]

noncomputable instance (G : Graph α β) : EMetricSpace (Realization.Metric G) :=
  Realization.eMetricSpace G

namespace Realization

lemma metricTopology_eq :
    (inferInstance : TopologicalSpace (Metric G)) =
      (eMetricSpace G).toUniformSpace.toTopologicalSpace := by
  rfl

-- /-- The carrier identity from the weak realization to the metric realization. -/
-- def weakToMetric (x : Weak G) : Metric G := x

-- /-- The carrier identity from the metric realization to the weak realization. -/
-- def metricToWeak (x : Metric G) : Weak G := x

/-- The pre-realization projection with the metric topology on its codomain. -/
def preToMetric (x : G.PreRealization) : Metric G :=
  Quotient.mk' (s := G.glueRel) x

-- /-- The weak and metric realizations have the same underlying points. -/
-- def carrierEquiv : Weak G ≃ Metric G := Equiv.refl _

-- /-- The two pre-realization projections agree on underlying points. -/
-- theorem preToMetric_eq_weakToMetric_comp :
--     preToMetric (G := G) = weakToMetric ∘ preToWeak G := rfl

namespace Metric

/-- Include a graph vertex in the metric realization. -/
def vertexMk (v : V(G)) : Metric G :=
  G.vertexMk v

/-- Include a parameter point of an edge in the metric realization. -/
noncomputable def edgeMk (e : E(G)) (t : I) : Metric G :=
  G.edgePath e t

lemma edist_edgeMk_le (e : E(G)) (s t : I) :
    EDist.edist (edgeMk (G := G) e s) (edgeMk (G := G) e t) ≤
      EDist.edist s t := by
  change G.preRealizationEDist (Sum.inr ⟨e, s⟩) (Sum.inr ⟨e, t⟩) ≤ EDist.edist s t
  refine (min_le_left _ _).trans ?_
  simp [directDist, edist_dist, Subtype.dist_eq, Real.dist_eq]

/-- Every unit-edge parametrization is nonexpanding for the realization metric. -/
lemma edgeMk_lipschitz (e : E(G)) : LipschitzWith 1 (edgeMk (G := G) e) :=
  LipschitzWith.of_edist_le (edist_edgeMk_le e)

/-- Parametrize an edge in the metric realization. -/
noncomputable def edgePath (e : E(G)) :
    Path (vertexMk (G := G) (G.edgeSource e)) (vertexMk (G := G) (G.edgeTarget e)) where
  toFun := edgeMk (G := G) e
  source' := (G.edgePath e).source
  target' := (G.edgePath e).target
  continuous_toFun := (edgeMk_lipschitz e).continuous

@[simp]
lemma toRealization_vertexMk (v : V(G)) :
    toRealization (G := G) (vertexMk (G := G) v) = G.vertexMk v := rfl

@[simp]
lemma toRealization_edgeMk (e : E(G)) (t : I) :
    toRealization (G := G) (edgeMk (G := G) e t) = G.edgePath e t := rfl

@[simp]
lemma toRealization_edgePath (e : E(G)) (t : I) :
    toRealization (G := G) (edgePath (G := G) e t) = G.edgePath e t := rfl

end Metric

/--
The projection from the disjoint union of vertices and edge intervals to the metric realization is
continuous.
-/
theorem continuous_preToMetric : Continuous (preToMetric (G := G)) := by
  refine continuous_sum_dom.mpr ⟨continuous_of_discreteTopology, ?_⟩
  rw [continuous_sigma_iff]
  intro e
  change Continuous (Metric.edgeMk (G := G) e)
  exact (Metric.edgeMk_lipschitz e).continuous

-- /-- The weak topology is finer than the unit-edge metric topology. -/
-- theorem continuous_weakToMetric : Continuous (weakToMetric (G := G)) := by
--   rw [(preToWeak_isQuotientMap G).continuous_iff]
--   rw [← preToMetric_eq_weakToMetric_comp]
--   exact continuous_preToMetric

end Realization

@[reducible]
noncomputable def Preconnected.MetricSpace (h : G.Preconnected) :
    MetricSpace (Realization.Metric G) := by
  refine EMetricSpace.toMetricSpace ?_
  intro x y
  refine Quotient.inductionOn₂ x y fun x y ↦ ?_
  change Realization.edist G ⟦x⟧ ⟦y⟧ ≠ ⊤
  simp only [Realization.edist, Quotient.lift_mk]
  match x, y with
  | inl x, inl y => simp [h x y]
  | inl x, inr ⟨e, t⟩ => simp [distToVtx, h (edgeTarget e)]
  | inr ⟨e, t⟩, inl y => simp [distToVtx, h (edgeSource e)]
  | inr ⟨e₁, t₁⟩, inr ⟨e₂, t₂⟩ =>
    simp [preRealizationEDist, directDist, distToVtx, h (edgeSource e₁), h (edgeTarget e₁),
      h (edgeSource e₂), h (edgeTarget e₂), Subtype.exists_of_subtype (edgeSource e₁)]

end Graph
