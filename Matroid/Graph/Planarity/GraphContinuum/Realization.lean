import Matroid.Graph.Finite
import Matroid.Graph.GraphLike.ArbRel
import Matroid.Graph.Distance
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Connected.PathConnected

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path WList Classical ENNReal
open scoped unitInterval

@[simp]
lemma unitInterval.val_le_zero_iff (t : I) : t.val ≤ 0 ↔ t = 0 := by
  simp only [t.prop.1.ge_iff_eq, eq_comm, Icc.coe_eq_zero]

@[simp]
lemma unitInterval.one_le_val_iff (t : I) : 1 ≤ t.val ↔ t = 1 := by
  simp only [t.prop.2.ge_iff_eq, Icc.coe_eq_one]

lemma continuous_mul_left_I (t : I) : Continuous (fun s : I => t * s) :=
  Continuous.codRestrict (s := I) ((continuous_const_mul (t : ℝ)).comp continuous_subtype_val)
    fun (s : I) => by
      obtain ⟨t, ht1, ht2⟩ := t
      obtain ⟨s, hs1, hs2⟩ := s
      simp [mul_le_one₀ ht2 hs1 hs2, Left.mul_nonneg ht1 hs1]

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-!
# Topological realization of a multigraph

The *geometric realization* `Graph.Realization G` is a 1-dimensional space: the discrete 0-skeleton
on `V(G)`, a closed 1-cell `I = Icc 0 1` per edge, and the quotient identifying `0`/`1` with chosen
endpoints of each edge (via `Classical.choice` among the two `IsLink` orientations).

This matches `sk₁` of a relative CW complex with stationary higher skeleta.  Concretely it is the
quotient of `V(G) ⊔ ⨆_{e ∈ E(G)} I`, i.e. (up to canonical homeomorphism) the pushout in `Top` of
`Fin 2 × E(G)` against the disjoint union of 1-disks.

`Vtx G` is used so the 0-skeleton carries the discrete topology `⊥`, not the subspace
topology from `α`.

If `G` is finite (finitely many vertices and edges), then `PreRealization G` is a finite disjoint
union of compact pieces (finite discrete spaces and copies of `I`), hence compact, and so is the
quotient `Realization G` (`Quotient.compactSpace`).
-/

/-- Vertices of `G` as a type, equipped with the discrete topology (the 0-skeleton). -/
def Vtx (G : Graph α β) := V(G)

/-- Discrete uniformity (hence discrete topology) on vertices. -/
instance (G : Graph α β) : UniformSpace (Vtx G) := ⊥

instance : DiscreteTopology G.Vtx where
  eq_bot := rfl

def Eg (G : Graph α β) := E(G)

instance (G : Graph α β) : UniformSpace (Eg G) := ⊥

instance instFiniteVtx [G.Finite] : Finite (Vtx G) := G.vertexSet_finite
instance instFiniteEg [G.EdgeFinite] : Finite (Eg G) := G.edgeSet_finite

noncomputable def Eg.src (e : Eg G) : Vtx G :=
  ⟨G.src e.prop, G.src_mem e.prop⟩

noncomputable def Eg.tgt (e : Eg G) : Vtx G :=
  ⟨G.tgt e.prop, G.tgt_mem e.prop⟩

/-- Disjoint union of the discrete 0-skeleton and one copy of `EdgeDisk` per edge. -/
abbrev PreRealization (G : Graph α β) := G.Vtx ⊕ G.Eg × I

variable {e e' : E(G)} {t t' : I} {u v : V(G)} {w x y z : G.PreRealization}

private def glueRel_aux (G : Graph α β) (x y : PreRealization G) : Prop :=
  match x with
  | .inl u => y = Sum.inl u ∨
    (∃ e : E(G), u = Eg.src e ∧ y = Sum.inr ⟨e, (0 : I)⟩) ∨
    (∃ e : E(G), u = Eg.tgt e ∧ y = Sum.inr ⟨e, (1 : I)⟩)
  | .inr _ => False

private lemma glueRel_aux_refl (u : Vtx G) : G.glueRel_aux (Sum.inl u) (Sum.inl u) := Or.inl rfl

@[simp]
private lemma glueRel_aux_inl_inj (u v : Vtx G) :G.glueRel_aux (Sum.inl u) (Sum.inl v) ↔ u = v := by
  simp only [glueRel_aux, reduceCtorEq, and_false, exists_false, or_self, or_false, eq_comm]
  exact Sum.inl_injective.eq_iff

@[simp]
private lemma glueRel_aux_inl_inr_iff (u : Vtx G) (e : E(G)) (t : I) :
    G.glueRel_aux (Sum.inl u) (Sum.inr ⟨e, t⟩) ↔ t = 0 ∧ u = Eg.src e ∨ t = 1 ∧ u = Eg.tgt e := by
  simp only [glueRel_aux, eq_comm, reduceCtorEq, Subtype.exists, false_or]
  grind

@[simp]
private lemma glueRel_aux_inr_iff (x : PreRealization G) (e : E(G)) (t : I) :
    G.glueRel_aux x (Sum.inr ⟨e, t⟩) ↔ ∃ u : G.Vtx, x = Sum.inl u ∧
    (t = 0 ∧ u = Eg.src e ∨ t = 1 ∧ u = Eg.tgt e) := by
  cases x
  · rw [glueRel_aux_inl_inr_iff]
    grind
  simp [glueRel_aux]

private theorem glueRel_aux_inr_boundary (h : glueRel_aux G x (Sum.inr ⟨e', t'⟩)) :
    t' = 0 ∨ t' = 1 := by
  cases x <;> obtain h | ⟨e₁, rfl, h⟩ | ⟨e₁, rfl, h⟩ := h
  · cases h
  all_goals have hp := Prod.mk.injEq _ _ _ _ ▸ Sum.inr_injective h ; tauto

private theorem not_glueRel_aux_inr_interior (ht : t ≠ 0 ∧ t ≠ 1) (y : PreRealization G) :
    ¬glueRel_aux G (Sum.inr ⟨e, t⟩) y ∧ ¬glueRel_aux G y (Sum.inr ⟨e, t⟩) := by
  constructor
  · rintro (⟨_, h, _⟩ | ⟨_, h, _⟩)
  cases y <;> rintro (h | ⟨e', rfl, h⟩ | ⟨e', rfl, h⟩)
  · cases h
  all_goals have hp := Prod.mk.injEq _ _ _ _ ▸ Sum.inr_injective h ; tauto

def glueRel (G : Graph α β) : Setoid (PreRealization G) := EqvGen.setoid (glueRel_aux G)

instance (G : Graph α β) : Setoid (PreRealization G) := EqvGen.setoid (glueRel_aux G)

instance : Std.Symm G.glueRel where
  symm _ _ h := EqvGen.symm _ _ h

instance : IsTrans _ G.glueRel where
  trans _ _ _ := EqvGen.trans _ _ _

private theorem glueRel_aux_eqvGen (u : Vtx G) (h : G.glueRel z w) :
    G.glueRel_aux (Sum.inl u) z ↔ G.glueRel_aux (Sum.inl u) w := by
  induction h generalizing u with
  | refl => rfl
  | rel x y hxy =>
    cases x; swap
    · simp [glueRel_aux] at hxy
    obtain rfl | ⟨e₁, rfl, rfl⟩ | ⟨e₁, rfl, rfl⟩ := hxy <;> simp
  | symm x y _ ih => simpa [iff_comm] using ih u
  | trans x y z _ _ ixy iyz => exact (ixy u).trans (iyz u)

@[simp]
theorem glueRel_inl_iff_glueRel_aux (u : Vtx G) (x : G.PreRealization) :
    G.glueRel (Sum.inl u) x ↔ G.glueRel_aux (Sum.inl u) x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := glueRel_aux_refl u
    rwa [glueRel_aux_eqvGen _ h] at this
  exact EqvGen.rel _ _ h

theorem eqvGen_inr_interior_preserved {a b : G.PreRealization} (ht : t ≠ 0 ∧ t ≠ 1)
    (h : G.glueRel a b) : (a = Sum.inr ⟨e, t⟩ ↔ b = Sum.inr ⟨e, t⟩) := by
  induction h with
  | refl => exact ⟨id, id⟩
  | rel x y hxy =>
    constructor <;> rintro rfl
    · exact ((not_glueRel_aux_inr_interior ht y).1 hxy).elim
    · exact ((not_glueRel_aux_inr_interior ht x).2 hxy).elim
  | symm _ _ _ ih => simpa [iff_comm] using ih
  | trans _ _ _ _ _ ixy iyz => exact ⟨fun hx => iyz.1 (ixy.1 hx), fun hz => ixy.2 (iyz.2 hz)⟩

lemma glueRel_right_unique (ht : t ≠ 0 ∧ t ≠ 1) (s : G.PreRealization) :
    G.glueRel (Sum.inr ⟨e, t⟩) s ↔ s = Sum.inr ⟨e, t⟩ :=
  ⟨fun h => (eqvGen_inr_interior_preserved ht h).mp rfl, fun h => h ▸ EqvGen.refl _⟩

lemma glueRel_inj_left (u v : G.Vtx) : glueRel G (Sum.inl u) (Sum.inl v) ↔ u = v := by simp

theorem glueRel_inl_inr (u : Vtx G) (e : E(G)) (t : I) :
    G.glueRel (Sum.inl u) (Sum.inr ⟨e, t⟩) ↔ t = 0 ∧ u = Eg.src e ∨ t = 1 ∧ u = Eg.tgt e := by simp

@[simp]
theorem glueRel_inr_inl (e : E(G)) (t : I) (v : G.Vtx) : G.glueRel (Sum.inr ⟨e, t⟩) (Sum.inl v) ↔
    t = (0 : I) ∧ v = Eg.src e ∨ t = (1 : I) ∧ v = Eg.tgt e :=
  Iff.trans ⟨EqvGen.symm _ _, EqvGen.symm _ _⟩ (glueRel_inl_inr v e t)

lemma exists_inl_of_glueRel_inr (h : G.glueRel (Sum.inr ⟨e, t⟩) y) (hy : y ≠ Sum.inr ⟨e, t⟩) :
    ∃ u : G.Vtx, G.glueRel (Sum.inl u) (Sum.inr ⟨e, t⟩) := by
  rcases eq_or_ne t 0 with rfl | ht0'
  · exact ⟨Eg.src e, by simp⟩
  rcases eq_or_ne t 1 with rfl | ht1'
  · exact ⟨Eg.tgt e, by simp⟩
  exact absurd ((eqvGen_inr_interior_preserved ⟨ht0', ht1'⟩ h).1 rfl) hy

@[simp]
theorem glueRel_inr_inr_iff (e₁ e₂ : E(G)) (t₁ t₂ : I) :
    G.glueRel (Sum.inr ⟨e₁, t₁⟩) (Sum.inr ⟨e₂, t₂⟩) ↔ (e₁ = e₂ ∧ t₁ = t₂) ∨ ∃ v : G.Vtx,
      G.glueRel (Sum.inl v) (Sum.inr ⟨e₁, t₁⟩) ∧ G.glueRel (Sum.inl v) (Sum.inr ⟨e₂, t₂⟩) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain heq | hne := eq_or_ne (inr ⟨e₁, t₁⟩ : PreRealization G) (inr ⟨e₂, t₂⟩)
    · simp only [inr.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      tauto
    obtain ⟨u, hu⟩ := exists_inl_of_glueRel_inr h hne.symm
    exact Or.inr ⟨u, hu, Setoid.trans hu h⟩
  rintro (⟨rfl, rfl⟩ | ⟨v, h₁, h₂⟩)
  · simp
  exact trans_of G.glueRel (symm_of G.glueRel h₁) h₂

/-- Topological realization: quotient of `PreRealization G` by the equivalence closure of
`glueRel`. -/
abbrev Realization (G : Graph α β) : Type _ := Quotient G.glueRel

/-- Inclusion of a vertex into the realization. -/
def vertexMk (v : Vtx G) : Realization G := Quotient.mk' (s := G.glueRel) (Sum.inl v)

/-- Inclusion of a point of the `e`-th edge interval into the realization. -/
def edgeMk (e : E(G)) (t : I) : Realization G := Quotient.mk' (s := G.glueRel) (Sum.inr ⟨e, t⟩)

lemma continuous_edgeMk (e : E(G)) : Continuous (edgeMk e) :=
  letI : UniformSpace E(G) := ⊥
  continuous_quotient_mk'.comp <| continuous_inr.comp <| Continuous.prodMk_right e

theorem realization_eq_edgeMk_zero (e : E(G)) : vertexMk (Eg.src e) = edgeMk e 0 :=
  Quotient.sound (by simp)

theorem realization_eq_edgeMk_one (e : E(G)) : vertexMk (Eg.tgt e) = edgeMk e 1 :=
  Quotient.sound (by simp)

/-- Distance from a pre-realization point to a vertex: graph distance to an endpoint, plus
parameter along the incident edge (when the point lies on an edge). -/
noncomputable def distToVtx (G : Graph α β) (x : PreRealization G) (v : Vtx G) : ℝ≥0∞ :=
  match x with
  | Sum.inl w => G.eDist w.val v.val
  | Sum.inr ⟨e, t⟩ => min (G.eDist (Eg.src e).val v.val + ENNReal.ofReal (t : ℝ))
      (G.eDist (Eg.tgt e).val v.val + ENNReal.ofReal (1 - (t : ℝ)))

@[simp]
lemma distToVtx_inl_left (u v : Vtx G) : distToVtx G (Sum.inl u) v = G.eDist u.val v.val := rfl

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
  min (directDist G a b) (⨅ v : Vtx G, distToVtx G a v + distToVtx G b v)

private lemma distToVtx_triangle (x : PreRealization G) (v w : Vtx G) :
    distToVtx G x v ≤ distToVtx G x w + (G.eDist w.val v.val : ℝ≥0∞) := by
  match x with
  | inl u =>
    simp only [distToVtx, ← ENat.toENNReal_add, ENat.toENNReal_le]
    exact G.eDist_triangle u.val w.val v.val
  | inr ⟨e, t⟩ =>
    refine le_trans (min_le_min ?_ ?_) <| (min_add_add_right _ _ _).le
    · have hs : (G.eDist (Eg.src e).val v.val : ℝ≥0∞) ≤
          (G.eDist (Eg.src e).val w.val : ℝ≥0∞) + (G.eDist w.val v.val : ℝ≥0∞) := by
        rw [← ENat.toENNReal_add, ENat.toENNReal_le]
        exact G.eDist_triangle (Eg.src e).val w.val v.val
      exact (add_le_add_left hs _).trans (le_of_eq (by ring))
    have ht : (G.eDist (Eg.tgt e).val v.val : ℝ≥0∞) ≤
        (G.eDist (Eg.tgt e).val w.val : ℝ≥0∞) + (G.eDist w.val v.val : ℝ≥0∞) := by
      rw [← ENat.toENNReal_add, ENat.toENNReal_le]
      exact G.eDist_triangle (Eg.tgt e).val w.val v.val
    exact (add_le_add ht le_rfl).trans (le_of_eq (by ring))

private lemma iInf_distToVtx_add (x y : PreRealization G) :
    (⨅ v : Vtx G, distToVtx G x v + distToVtx G y v) = match x with
    | Sum.inl u => distToVtx G y u
    | Sum.inr ⟨e, t⟩ => min (ENNReal.ofReal (t : ℝ) + distToVtx G y (Eg.src e))
      (ENNReal.ofReal (1 - (t : ℝ)) + distToVtx G y (Eg.tgt e)) := by
  match x with
  | Sum.inl u =>
    refine le_antisymm ?_ <| le_iInf fun v ↦ ?_
    · exact iInf_le _ u |>.trans <| by simp [distToVtx, G.eDist_self u.prop]
    simpa [distToVtx, add_comm, G.eDist_comm v.val u.val] using distToVtx_triangle y u v
  | Sum.inr ⟨e, t⟩ =>
    conv in G.distToVtx (inr (e, t)) _ + G.distToVtx y _ =>
      rw [distToVtx, add_comm _ (ENNReal.ofReal _), add_comm _ (ENNReal.ofReal _)]
      exact (min_add_add_right _ _ _).symm
    convert iInf_inf_eq <;> simp_rw [add_assoc, ← ENNReal.add_iInf]
    <;> change _ = _ + (⨅ v, distToVtx G (Sum.inl _) v  + _)
    <;> refine congr_arg (ENNReal.ofReal _ + ·) <| by rw [iInf_distToVtx_add]

@[simp]
private lemma preRealizationEDist_inl_left (u : Vtx G) (x : PreRealization G) :
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
private lemma preRealizationEDist_inl_right (u : Vtx G) (x : PreRealization G) :
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

private lemma eDist_src_tgt_le_one (e : E(G)) : G.eDist (Eg.src e).val (Eg.tgt e).val ≤ 1 := by
  simpa [IsLink.walk_length, IsLink.walk_first, IsLink.walk_last, Eg.src,
    Eg.tgt] using (G.isLink_src_tgt e.prop).walk_isWalk.eDist_le_length

-- private lemma eDist_le_add_one_tgt (e : E(G)) (x : α) :
--     (G.eDist x (Eg.src e).val : ℝ≥0∞) ≤ (G.eDist x (Eg.tgt e).val : ℝ≥0∞) + 1 := by
--   rw [← ENat.toENNReal_one, ← ENat.toENNReal_add, ENat.toENNReal_le]
--   refine (G.eDist_triangle x (Eg.tgt e).val (Eg.src e).val).trans ?_
--   rw [G.eDist_comm (Eg.tgt e).val]
--   exact add_le_add le_rfl (eDist_src_tgt_le_one e)

-- private lemma eDist_le_add_one_src (e : E(G)) (x : α) :
--     (G.eDist x (Eg.tgt e).val : ℝ≥0∞) ≤ (G.eDist x (Eg.src e).val : ℝ≥0∞) + 1 := by
--   rw [← ENat.toENNReal_one, ← ENat.toENNReal_add, ENat.toENNReal_le]
--   refine (G.eDist_triangle x (Eg.src e).val (Eg.tgt e).val).trans ?_
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

private lemma distToVtx_le_directDist_add (x y : PreRealization G) (w : Vtx G) :
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

private lemma eDist_le_distToVtx_add (x : PreRealization G) (v w : Vtx G) :
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
      refine (G.eDist_triangle v.val (Eg.src e).val w.val).trans ?_
      refine add_le_add le_rfl (G.eDist_triangle (Eg.src e).val (Eg.tgt e).val w.val) |>.trans ?_
      rw [eDist_comm]
      exact add_le_add le_rfl (add_le_add (eDist_src_tgt_le_one e) le_rfl)
    on_goal 2 =>
      refine le_trans ?_ <| (h_rearrange ..).le
      simp only [← ENNReal.ofReal_add (sub_nonneg.mpr t.2.2) t.2.1, sub_add_cancel, ofReal_one]
      norm_cast
      refine (G.eDist_triangle v.val (Eg.tgt e).val w.val).trans ?_
      refine add_le_add le_rfl (G.eDist_triangle (Eg.tgt e).val (Eg.src e).val w.val) |>.trans ?_
      rw [eDist_comm, eDist_comm (Eg.tgt e).val (Eg.src e).val]
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
    simp only [preRealizationEDist_inl_right, distToVtx_inl_left, glueRel_inl_iff_glueRel_aux,
      glueRel_aux_inl_inj]
    norm_cast
    simp [Subtype.coe_inj]
  | .inl v, .inr ⟨e, t⟩ =>
    simp only [preRealizationEDist_inl_left, distToVtx, min_eq_zero_iff, add_eq_zero,
      ofReal_eq_zero, unitInterval.val_le_zero_iff, tsub_le_iff_right, zero_add,
      unitInterval.one_le_val_iff, glueRel_inl_iff_glueRel_aux, glueRel_aux_inr_iff, inl.injEq,
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
      glueRel_inr_inr_iff, glueRel_inl_iff_glueRel_aux, glueRel_aux_inr_iff, inl.injEq,
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
  | inl x, inr ⟨e, t⟩ => simp [distToVtx, h (Eg.tgt e)]
  | inr ⟨e, t⟩, inl y => simp [distToVtx, h (Eg.src e)]
  | inr ⟨e₁, t₁⟩, inr ⟨e₂, t₂⟩ =>
    simp [preRealizationEDist, directDist, distToVtx, h (Eg.src e₁), h (Eg.tgt e₁), h (Eg.src e₂),
      h (Eg.tgt e₂), Subtype.exists_of_subtype (Eg.src e₁)]

-- instance : PathConnectedSpace I := sorry
-- instance : LocPathConnectedSpace (G.Eg × I) := sorry -- Why is there no instance for `Prod`?
-- instance : LocPathConnectedSpace G.PreRealization := sorry
-- -- Why does `Sum.locPathConnectedSpace` require the two type to be in the same universe?
-- instance : LocPathConnectedSpace G.Realization := inferInstance

/-- The canonical path along an edge `e` in the realization, from `src e` to `tgt e`. -/
noncomputable def pathAlongEdge (e : E(G)) : Path (vertexMk (Eg.src e)) (vertexMk (Eg.tgt e)) where
  toContinuousMap := ⟨fun t : I ↦ edgeMk e t, continuous_edgeMk e⟩
  source' := (realization_eq_edgeMk_zero e).symm
  target' := (realization_eq_edgeMk_one e).symm

theorem joined_vertexMk_of_isLink {e : β} {x y : α} (h : G.IsLink e x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h.eq_and_eq_or_eq_and_eq <| G.isLink_src_tgt h.edge_mem
  · simpa [h1, h2, Eg.src, Eg.tgt] using ⟨pathAlongEdge ⟨e, h.edge_mem⟩⟩
  · simpa [h1, h2, Eg.src, Eg.tgt] using ⟨pathAlongEdge ⟨e, h.edge_mem⟩ |>.symm⟩

theorem joined_vertexMk_of_isWalk {w : WList α β} (hw : G.IsWalk w) :
    Joined (vertexMk ⟨w.first, hw.first_mem⟩) (vertexMk ⟨w.last, hw.last_mem⟩) := by
  induction hw with
  | @nil x hx => exact Joined.refl _
  | @cons x e w hw' hlink ih => simpa [last_cons] using (joined_vertexMk_of_isLink hlink).trans ih

theorem joined_vertexMk_of_connBetween {x y : α} (h : G.ConnBetween x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact joined_vertexMk_of_isWalk hw

noncomputable def pathAlongEdgeTo (e : E(G)) (t : I) : Path (vertexMk (Eg.src e)) (edgeMk e t) where
  toContinuousMap :=
    ⟨fun s : I ↦ edgeMk e (t * s), (continuous_edgeMk e).comp (continuous_mul_left_I t)⟩
  source' := by simp [realization_eq_edgeMk_zero]
  target' := by simp

theorem joined_vertexMk_edgeMk (e : E(G)) (t : I) : Joined (vertexMk (Eg.src e)) (edgeMk e t) :=
  ⟨pathAlongEdgeTo e t⟩

theorem Preconnected.joined_vertexMk_realMk {v0 : α} (hv0 : v0 ∈ V(G)) (hG : G.Preconnected)
    (a : G.PreRealization) : Joined (vertexMk ⟨v0, hv0⟩) ⟦a⟧ := by
  match a with
  | inl v => simpa using joined_vertexMk_of_connBetween (hG v0 v hv0 v.prop)
  | inr ⟨e, t⟩ =>
    refine (joined_vertexMk_of_connBetween (hG v0 (G.src e.prop) hv0 ?_)).trans ?_
    · exact (G.isLink_src_tgt e.prop).left_mem
    · simpa [Eg.src] using joined_vertexMk_edgeMk e t

theorem Connected.pathConnectedSpace (h : G.Connected) : PathConnectedSpace G.Realization := by
  obtain ⟨v0, hv0⟩ := h.nonempty
  refine ⟨⟨vertexMk ⟨v0, hv0⟩⟩, Quotient.ind₂ fun a b ↦ ?_⟩
  exact (h.pre.joined_vertexMk_realMk hv0 a).symm.trans (h.pre.joined_vertexMk_realMk hv0 b)

-- instance [G.Finite] : CompactSpace G.Realization := inferInstance

end Graph
