import Matroid.Graph.Planarity.Realization.Basic

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path WList Classical ENNReal
open scoped unitInterval

namespace Graph

variable {α β : Type*} {G : Graph α β} {e : E(G)} {t t' : I} {u v : V(G)}
  {w x y z : G.PreRealization}

/-- Distance from a pre-realization point to a vertex: graph distance to an endpoint, plus
parameter along the incident edge (when the point lies on an edge). -/
noncomputable def distToVtx (G : Graph α β) (x : PreRealization G) (v : V(G)) : ℝ≥0∞ :=
  match x with
  | Sum.inl w => G.eDist w.val v.val
  | Sum.inr ⟨e, t⟩ => min (G.eDist (src e).val v.val + ENNReal.ofReal (t : ℝ))
      (G.eDist (tgt e).val v.val + ENNReal.ofReal (1 - (t : ℝ)))

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
    · have hs : (G.eDist (src e).val v.val : ℝ≥0∞) ≤
          (G.eDist (src e).val w.val : ℝ≥0∞) + (G.eDist w.val v.val : ℝ≥0∞) := by
        rw [← ENat.toENNReal_add, ENat.toENNReal_le]
        exact G.eDist_triangle (src e).val w.val v.val
      exact (add_le_add_left hs _).trans (le_of_eq (by ring))
    have ht : (G.eDist (tgt e).val v.val : ℝ≥0∞) ≤
        (G.eDist (tgt e).val w.val : ℝ≥0∞) + (G.eDist w.val v.val : ℝ≥0∞) := by
      rw [← ENat.toENNReal_add, ENat.toENNReal_le]
      exact G.eDist_triangle (tgt e).val w.val v.val
    exact (add_le_add ht le_rfl).trans (le_of_eq (by ring))

private lemma iInf_distToVtx_add (x y : PreRealization G) :
    (⨅ v : V(G), distToVtx G x v + distToVtx G y v) = match x with
    | Sum.inl u => distToVtx G y u
    | Sum.inr ⟨e, t⟩ => min (ENNReal.ofReal (t : ℝ) + distToVtx G y (src e))
      (ENNReal.ofReal (1 - (t : ℝ)) + distToVtx G y (tgt e)) := by
  match x with
  | Sum.inl u =>
    refine le_antisymm ?_ <| le_iInf fun v ↦ ?_
    · exact iInf_le _ u |>.trans <| by simp [distToVtx, G.eDist_self u.prop]
    simpa [distToVtx, add_comm, G.eDist_comm v.val u.val] using distToVtx_triangle y u v
  | Sum.inr ⟨e, t⟩ =>
    conv in G.distToVtx (inr ⟨e, t⟩) _ + G.distToVtx y _ =>
      rw [distToVtx, add_comm _ (ENNReal.ofReal _), add_comm _ (ENNReal.ofReal _)]
      exact (min_add_add_right _ _ _).symm
    convert iInf_inf_eq <;> simp_rw [add_assoc, ← ENNReal.add_iInf]
    <;> change _ = _ + (⨅ v, distToVtx G (Sum.inl _) v  + _)
    <;> refine congr_arg (ENNReal.ofReal _ + ·) <| by rw [iInf_distToVtx_add]

@[simp]
private lemma preRealizationEDist_inl_left (u : V(G)) (x : PreRealization G) :
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
private lemma preRealizationEDist_inl_right (u : V(G)) (x : PreRealization G) :
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

private lemma eDist_src_tgt_le_one (e : E(G)) : G.eDist (src e).val (tgt e).val ≤ 1 := by
  simpa [IsLink.walk_length, IsLink.walk_first, IsLink.walk_last, src, tgt] using
    (G.isLink_source_target e.prop).walk_isWalk.eDist_le_length

-- private lemma eDist_le_add_one_tgt (e : E(G)) (x : α) :
--     (G.eDist x (src e).val : ℝ≥0∞) ≤ (G.eDist x (tgt e).val : ℝ≥0∞) + 1 := by
--   rw [← ENat.toENNReal_one, ← ENat.toENNReal_add, ENat.toENNReal_le]
--   refine (G.eDist_triangle x (tgt e).val (src e).val).trans ?_
--   rw [G.eDist_comm (tgt e).val]
--   exact add_le_add le_rfl (eDist_src_tgt_le_one e)

-- private lemma eDist_le_add_one_src (e : E(G)) (x : α) :
--     (G.eDist x (tgt e).val : ℝ≥0∞) ≤ (G.eDist x (src e).val : ℝ≥0∞) + 1 := by
--   rw [← ENat.toENNReal_one, ← ENat.toENNReal_add, ENat.toENNReal_le]
--   refine (G.eDist_triangle x (src e).val (tgt e).val).trans ?_
--   exact add_le_add le_rfl (eDist_src_tgt_le_one e)

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
      refine (G.eDist_triangle v.val (src e).val w.val).trans ?_
      refine add_le_add le_rfl (G.eDist_triangle (src e).val (tgt e).val w.val) |>.trans ?_
      rw [eDist_comm]
      exact add_le_add le_rfl (add_le_add (eDist_src_tgt_le_one e) le_rfl)
    on_goal 2 =>
      refine le_trans ?_ <| (h_rearrange ..).le
      simp only [← ENNReal.ofReal_add (sub_nonneg.mpr t.2.2) t.2.1, sub_add_cancel, ofReal_one]
      norm_cast
      refine (G.eDist_triangle v.val (tgt e).val w.val).trans ?_
      refine add_le_add le_rfl (G.eDist_triangle (tgt e).val (src e).val w.val) |>.trans ?_
      rw [eDist_comm, eDist_comm (tgt e).val (src e).val]
      exact add_le_add le_rfl (add_le_add (eDist_src_tgt_le_one e) le_rfl)
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
      glueRelAux_inl_inj]
    norm_cast
    simp [Subtype.coe_inj]
  | .inl v, .inr ⟨e, t⟩ =>
    simp only [preRealizationEDist_inl_left, distToVtx, min_eq_zero_iff, add_eq_zero,
      ofReal_eq_zero, unitInterval.val_le_zero_iff, tsub_le_iff_right, zero_add,
      unitInterval.one_le_val_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff, inl.injEq,
      exists_eq_left']
    norm_cast
    simp only [eDist_eq_zero_iff, Subtype.coe_inj, Subtype.coe_prop, and_true]
    tauto
  | .inr ⟨e, t⟩, .inl v =>
    simp only [preRealizationEDist_inl_right, distToVtx, min_eq_zero_iff, add_eq_zero,
      ofReal_eq_zero, unitInterval.val_le_zero_iff, tsub_le_iff_right, zero_add,
      unitInterval.one_le_val_iff, glueRel_inr_inl]
    norm_cast
    simp only [eDist_eq_zero_iff, Subtype.coe_inj, Subtype.coe_prop]
    tauto
  | .inr ⟨e₁, t₁⟩, .inr ⟨e₂, t₂⟩ =>
    simp only [preRealizationEDist, iInf_distToVtx_add]
    simp only [directDist, distToVtx, min_eq_zero_iff, add_eq_zero, ofReal_eq_zero,
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

/-- Extended distance on `Realization G`, induced by `Graph.eDist` on vertices and unit edges. -/
noncomputable def Realization.edist (G : Graph α β) (x y : G.Realization) : ℝ≥0∞ :=
  Quotient.lift₂ G.preRealizationEDist preRealizationEDist_respects_quotient x y

noncomputable instance (G : Graph α β) : EMetricSpace G.Realization where
  edist := Realization.edist G
  edist_self x := Quotient.inductionOn₂ x x fun x y ↦ by simp [Realization.edist]
  edist_comm := Quotient.ind₂ fun x y ↦ by simp [Realization.edist, preRealizationEDist_comm]
  edist_triangle := Quotient.ind₂ fun x y ↦ Quotient.ind fun z ↦ by
    simp [Realization.edist, preRealizationEDist_triangle]
  eq_of_edist_eq_zero {x y} := Quotient.inductionOn₂ x y fun x y ↦ by
    simp [Realization.edist, preRealizationEDist_zero_iff, Quotient.eq]

@[reducible]
noncomputable def Preconnected.MetricSpace (h : G.Preconnected) : MetricSpace G.Realization := by
  refine EMetricSpace.toMetricSpace <| Quotient.ind₂ fun x y ↦ ?_
  simp only [edist, Realization.edist, Quotient.lift_mk]
  match x, y with
  | inl x, inl y => simp [h x y]
  | inl x, inr ⟨e, t⟩ => simp [distToVtx, h (tgt e)]
  | inr ⟨e, t⟩, inl y => simp [distToVtx, h (src e)]
  | inr ⟨e₁, t₁⟩, inr ⟨e₂, t₂⟩ =>
    simp [preRealizationEDist, directDist, distToVtx, h (src e₁), h (tgt e₁), h (src e₂),
      h (tgt e₂), Subtype.exists_of_subtype (src e₁)]

end Graph
