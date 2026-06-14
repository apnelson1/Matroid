import Matroid.Graph.Finite
import Matroid.Graph.GraphLike.ArbRel
import Matroid.Graph.Distance
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Matroid.Graph.Planarity.Topology.Path
import Matroid.Graph.Planarity.Topology.ConnPartition

open Set Function TopologicalSpace Topology Relation Sum Path WList ENNReal Set.Notation
open scoped unitInterval

@[simp]
lemma Sum.preimage_image_inr {α β : Type*} (X : Set β) :
    Sum.inr ⁻¹' (Sum.inr '' X : Set (α ⊕ β)) = X := by
  grind

@[simp]
lemma Sum.preimage_image_inl {α β : Type*} (X : Set α) :
    Sum.inl ⁻¹' (Sum.inl '' X : Set (α ⊕ β)) = X := by
  grind

@[simp↓]
lemma Sigma.continuous_snd {ι α: Type*} [TopologicalSpace α] :
    Continuous (Sigma.snd : Sigma (α := ι) (fun _ => α) → α) := by
  simp only [continuous_sigma_iff]
  exact fun i ↦ continuous_id'

@[simp]
lemma dist_eq_zero_of_subsingleton {α : Type*} [PseudoMetricSpace α] [Subsingleton α] (x y : α) :
    dist x y = 0 := by simp [Subsingleton.elim x y]

@[simp]
lemma norm_eq_zero_of_subsingleton {α : Type*} [SeminormedAddGroup α] [Subsingleton α] (x : α) :
  ‖x‖ = 0 := by simp [Subsingleton.elim x 0]

namespace Graph

variable {α β : Type*} {G : Graph α β} {t t₁ t₂ : I}

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

/-- Discrete uniformity (hence discrete topology) on vertices. -/
instance (G : Graph α β) : UniformSpace V(G) := ⊥

instance : DiscreteTopology V(G) where
  eq_bot := rfl

instance instFiniteVtx [G.Finite] : Finite V(G) := G.vertexSet_finite
instance instFiniteEg [G.EdgeFinite] : Finite E(G) := G.edgeSet_finite

noncomputable def src (e : E(G)) : V(G) := ⟨G.source e.val e.prop, G.source_mem e.prop⟩
noncomputable def tgt (e : E(G)) : V(G) := ⟨G.target e.val e.prop, G.target_mem e.prop⟩
lemma isLink_src_tgt (e : E(G)) : G.IsLink e (src e) (tgt e) := G.isLink_source_target e.prop

@[grind →]
lemma IsNonloopAt.src_ne_tgt (e : E(G)) {x : V(G)} (h : G.IsNonloopAt e x) :
    src e ≠ tgt e := by
  obtain ⟨hne, hl⟩ := h.choose_spec
  grind [(isLink_src_tgt e).eq_and_eq_or_eq_and_eq hl]

/-- Disjoint union of the discrete 0-skeleton and one copy of `EdgeDisk` per edge. -/
abbrev PreRealization (G : Graph α β) := V(G) ⊕ Σ (_ : E(G)), I

variable {e : E(G)} {t t' : I} {u v : V(G)} {w x y z : G.PreRealization}

private def glueRelAux (G : Graph α β) (x y : PreRealization G) : Prop :=
  match x with
  | .inl u => y = Sum.inl u ∨
    (∃ e : E(G), u = src e ∧ y = Sum.inr ⟨e, (0 : I)⟩) ∨
    (∃ e : E(G), u = tgt e ∧ y = Sum.inr ⟨e, (1 : I)⟩)
  | .inr _ => False

lemma glueRelAux_refl (u : V(G)) : G.glueRelAux (Sum.inl u) (Sum.inl u) := Or.inl rfl

@[simp]
lemma glueRelAux_inl_inj (u v : V(G)) : G.glueRelAux (Sum.inl u) (Sum.inl v) ↔ u = v := by
  simp only [glueRelAux, reduceCtorEq, and_false, exists_false, or_self, or_false, eq_comm]
  exact Sum.inl_injective.eq_iff

@[simp]
lemma glueRelAux_inl_inr_iff (u : V(G)) (e : E(G)) (t : I) :
    G.glueRelAux (Sum.inl u) (Sum.inr ⟨e, t⟩) ↔ t = 0 ∧ u = src e ∨ t = 1 ∧ u = tgt e := by
  simp only [glueRelAux, eq_comm, reduceCtorEq, Subtype.exists, false_or]
  grind

@[simp]
lemma glueRelAux_inr_iff (x : PreRealization G) (e : E(G)) (t : I) :
    G.glueRelAux x (Sum.inr ⟨e, t⟩) ↔ ∃ u : V(G), x = Sum.inl u ∧
    (t = 0 ∧ u = src e ∨ t = 1 ∧ u = tgt e) := by
  cases x
  · rw [glueRelAux_inl_inr_iff]
    grind
  simp [glueRelAux]

private theorem glueRelAux_inr_boundary {e' : E(G)} (h : glueRelAux G x (Sum.inr ⟨e', t'⟩)) :
    t' = 0 ∨ t' = 1 := by
  cases x <;> obtain h | ⟨e₁, rfl, h⟩ | ⟨e₁, rfl, h⟩ := h
  · cases h
  all_goals simp_all

private theorem not_glueRelAux_inr_interior (ht : t ≠ 0 ∧ t ≠ 1) (y : PreRealization G) :
    ¬glueRelAux G (Sum.inr ⟨e, t⟩) y ∧ ¬glueRelAux G y (Sum.inr ⟨e, t⟩) := by
  constructor
  · rintro (⟨_, h, _⟩ | ⟨_, h, _⟩)
  cases y <;> rintro (h | ⟨e', rfl, h⟩ | ⟨e', rfl, h⟩)
  · cases h
  all_goals simp_all

instance glueRel (G : Graph α β) : Setoid (PreRealization G) := EqvGen.setoid (glueRelAux G)

instance (G : Graph α β) : Setoid (PreRealization G) := EqvGen.setoid (glueRelAux G)

instance : Std.Symm G.glueRel where
  symm _ _ h := EqvGen.symm _ _ h

instance : IsTrans _ G.glueRel where
  trans _ _ _ := EqvGen.trans _ _ _

private theorem glueRelAux_eqvGen (u : V(G)) (h : G.glueRel z w) :
    G.glueRelAux (Sum.inl u) z ↔ G.glueRelAux (Sum.inl u) w := by
  induction h generalizing u with
  | refl => rfl
  | rel x y hxy =>
    cases x; swap
    · simp [glueRelAux] at hxy
    obtain rfl | ⟨e₁, rfl, rfl⟩ | ⟨e₁, rfl, rfl⟩ := hxy <;> simp
  | symm x y _ ih => simpa [iff_comm] using ih u
  | trans x y z _ _ ixy iyz => exact (ixy u).trans (iyz u)

@[simp]
theorem glueRel_inl_iff_glueRelAux (u : V(G)) (x : G.PreRealization) :
    G.glueRel (Sum.inl u) x ↔ G.glueRelAux (Sum.inl u) x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := glueRelAux_refl u
    rwa [glueRelAux_eqvGen _ h] at this
  exact EqvGen.rel _ _ h

theorem eqvGen_inr_interior_preserved {a b : G.PreRealization} (ht : t ≠ 0 ∧ t ≠ 1)
    (h : G.glueRel a b) : (a = Sum.inr ⟨e, t⟩ ↔ b = Sum.inr ⟨e, t⟩) := by
  induction h with
  | refl => exact ⟨id, id⟩
  | rel x y hxy =>
    constructor <;> rintro rfl
    · exact ((not_glueRelAux_inr_interior ht y).1 hxy).elim
    · exact ((not_glueRelAux_inr_interior ht x).2 hxy).elim
  | symm _ _ _ ih => simpa [iff_comm] using ih
  | trans _ _ _ _ _ ixy iyz => exact ⟨fun hx => iyz.1 (ixy.1 hx), fun hz => ixy.2 (iyz.2 hz)⟩

lemma glueRel_right_unique (ht : t ≠ 0 ∧ t ≠ 1) (s : G.PreRealization) :
    G.glueRel (Sum.inr ⟨e, t⟩) s ↔ s = Sum.inr ⟨e, t⟩ :=
  ⟨fun h => (eqvGen_inr_interior_preserved ht h).mp rfl, fun h => h ▸ EqvGen.refl _⟩

lemma glueRel_inj_left (u v : V(G)) : glueRel G (Sum.inl u) (Sum.inl v) ↔ u = v := by simp

theorem glueRel_inl_inr (u : V(G)) (e : E(G)) (t : I) :
    G.glueRel (Sum.inl u) (Sum.inr ⟨e, t⟩) ↔ t = 0 ∧ u = src e ∨ t = 1 ∧ u = tgt e := by simp

@[simp]
theorem glueRel_inr_inl (e : E(G)) (t : I) (v : V(G)) : G.glueRel (Sum.inr ⟨e, t⟩) (Sum.inl v) ↔
    t = (0 : I) ∧ v = src e ∨ t = (1 : I) ∧ v = tgt e :=
  Iff.trans ⟨EqvGen.symm _ _, EqvGen.symm _ _⟩ (glueRel_inl_inr v e t)

lemma exists_inl_of_glueRel_inr (h : G.glueRel (Sum.inr ⟨e, t⟩) y) (hy : y ≠ Sum.inr ⟨e, t⟩) :
    ∃ u : V(G), G.glueRel (Sum.inl u) (Sum.inr ⟨e, t⟩) := by
  rcases eq_or_ne t 0 with rfl | ht0'
  · exact ⟨src e, by simp⟩
  rcases eq_or_ne t 1 with rfl | ht1'
  · exact ⟨tgt e, by simp⟩
  exact absurd ((eqvGen_inr_interior_preserved ⟨ht0', ht1'⟩ h).1 rfl) hy

@[simp]
theorem glueRel_inr_inr_iff (e₁ e₂ : E(G)) (t₁ t₂ : I) :
    G.glueRel (Sum.inr ⟨e₁, t₁⟩) (Sum.inr ⟨e₂, t₂⟩) ↔ (e₁ = e₂ ∧ t₁ = t₂) ∨ ∃ v : V(G),
      G.glueRel (Sum.inl v) (Sum.inr ⟨e₁, t₁⟩) ∧ G.glueRel (Sum.inl v) (Sum.inr ⟨e₂, t₂⟩) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain heq | hne := eq_or_ne (inr ⟨e₁, t₁⟩ : PreRealization G) (inr ⟨e₂, t₂⟩)
    · obtain ⟨rfl, rfl⟩ := heq
      tauto
    obtain ⟨u, hu⟩ := exists_inl_of_glueRel_inr h hne.symm
    exact Or.inr ⟨u, hu, Setoid.trans hu h⟩
  rintro (⟨rfl, rfl⟩ | ⟨v, h₁, h₂⟩)
  · simp
  exact trans_of G.glueRel (symm_of G.glueRel h₁) h₂

@[simp↓]
theorem glueRel_inr_inr_iff' (e : E(G)) (he : G.IsNonloopAt e (src e)) (t₁ t₂ : I) :
    G.glueRel (Sum.inr ⟨e, t₁⟩) (Sum.inr ⟨e, t₂⟩) ↔ t₁ = t₂ := by
  simp only [glueRel_inr_inr_iff, true_and, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff,
    inl.injEq, exists_eq_left', or_iff_left_iff_imp, forall_exists_index, and_imp]
  grind

/-- Topological realization: quotient of `PreRealization G` by the equivalence closure of
`glueRel`. -/
abbrev Realization (G : Graph α β) : Type _ := Quotient G.glueRel

/-- Inclusion of a vertex into the realization. -/
def vertexMk (v : V(G)) : Realization G := Quotient.mk' (s := G.glueRel) (Sum.inl v)

lemma vertexMk_injective : Injective G.vertexMk := fun u v ↦ by simp [vertexMk]

@[simp] lemma vertexMk_inj : vertexMk u = vertexMk v ↔ u = v := G.vertexMk_injective.eq_iff

/-- Inclusion of a point of the `e`-th edge interval into the realization. -/
-- def edgeMk (e : E(G)) (t : I) : Realization G := Quotient.mk' (s := G.glueRel) (Sum.inr ⟨e, t⟩)

def edgePath (e : E(G)) : Path (vertexMk (src e)) (vertexMk (tgt e)) where
  toFun t := Quotient.mk' (s := G.glueRel) (Sum.inr ⟨e, t⟩)
  source' := Quotient.sound (by simp)
  target' := Quotient.sound (by simp)
  continuous_toFun := continuous_quotient_mk'.comp' <| continuous_inr.comp' continuous_sigmaMk

section edgePath

lemma vertexMk_notMem_edgePath_Ioo (v : V(G)) (e : E(G)) : vertexMk v ∉ edgePath e '' Ioo 0 1 := by
  rintro ⟨t, ht, heq⟩
  have := Quotient.exact heq
  simp only [glueRel_inr_inl] at this
  grind

lemma edgePath_Ioo_disjoint_iff_ne (e₁ e₂ : E(G)) :
    Disjoint (edgePath e₁ '' Ioo 0 1) (edgePath e₂ '' Ioo 0 1) ↔ e₁ ≠ e₂ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro rfl
    simp only [disjoint_self, bot_eq_empty, image_eq_empty] at h
    let half : I := ⟨2⁻¹, by simp only [mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]; linarith⟩
    have : half ∈ (Ioo 0 1 : Set I) := by
      refine ⟨(?_ : (0 : ℝ) < 2⁻¹), (?_ : 2⁻¹ < (1 : ℝ))⟩ <;> linarith
    grind
  by_contra! h
  rw [not_disjoint_iff] at h
  obtain ⟨x, ⟨t1, ht1, rfl⟩, ⟨t2, ht2, heq⟩⟩ := h
  have := Quotient.exact heq
  simp only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff] at this
  grind

lemma edgePath_inj_on_Ioo (h₁ : (t₁ : ℝ) ∈ Ioo 0 1) (h : edgePath e t₁ = edgePath e t₂) :
    t₁ = t₂ := by
  obtain ⟨-, rfl⟩ | ⟨v, hv₁, hv₂⟩ := (glueRel_inr_inr_iff ..).mp (Quotient.exact h)
  · rfl
  obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := (glueRel_inl_inr ..).mp hv₁ <;> simp at h₁

private lemma edgePath_injective (e : E(G)) (he : G.IsNonloopAt e (src e)) :
    Injective (edgePath e) := by
  intro t₁ t₂ h
  have hgr : G.glueRel (Sum.inr ⟨e, t₁⟩) (Sum.inr ⟨e, t₂⟩) := (Quotient.eq (r := G.glueRel)).1 h
  obtain ⟨-, rfl⟩ | ⟨v, hv₁, hv₂⟩ := (glueRel_inr_inr_iff ..).mp (Quotient.exact h)
  · rfl
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (glueRel_inl_inr ..).mp hv₁ <;>
  obtain ⟨rfl, h1⟩ | ⟨rfl, h1⟩ := (glueRel_inl_inr ..).mp hv₂ <;> clear h hv₁ hv₂ hgr <;> (try rfl)
  <;> have hval : G.source e.val e.prop = _ := congrArg Subtype.val (by simpa [eq_comm] using h1)
  <;> have hlink := hval ▸ G.isLink_source_target e.prop <;> exact absurd hlink (he.not_isLoopAt _)

lemma edgePath_preimage_image (e : E(G)) {X : Set I} (h0X : 0 ∉ X) (h1X : 1 ∉ X) :
    Quotient.mk' ⁻¹' (edgePath e '' X) = Sum.inr '' (Sigma.mk e '' X) := by
  ext x
  simp only [mem_preimage, mem_image, Sigma.exists, Sigma.mk.injEq, heq_eq_eq,
    exists_eq_right_right]
  refine Iff.symm ⟨?_, fun ⟨t, ht, h_eq⟩ => ?_⟩
  · rintro ⟨e', t', ⟨ht', rfl⟩, rfl⟩
    exact ⟨t', ht', rfl⟩
  simp only [edgePath, coe_mk', ContinuousMap.coe_mk, Quotient.eq'] at h_eq
  match x with
  | inl v => obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := (glueRel_inr_inl ..).mp h_eq <;> tauto
  | inr ⟨e', t'⟩ =>
    simp only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff, inl.injEq,
      exists_eq_left'] at h_eq
    grind

theorem isOpen_edgePath_image (e : E(G)) {X : Set I} (h0X : 0 ∉ X) (h1X : 1 ∉ X) :
    IsOpen (edgePath e '' X) ↔ IsOpen X := by
  change IsOpen (Quotient.mk' ⁻¹' (edgePath e '' X)) ↔ _
  rw [edgePath_preimage_image e h0X h1X, isOpen_sum_iff]
  simp [IsOpenEmbedding.sigmaMk.isOpen_iff_image_isOpen.symm]

private lemma edgePath_preimage_aux_eq_preimage_mk' (e : E(G)) (C : Set I) :
    {z | ∃ t ∈ C, G.glueRel z (Sum.inr ⟨e, t⟩)} = Quotient.mk' ⁻¹' (edgePath e '' C) := by
  ext z
  simp only [mem_setOf_eq, mem_preimage, mem_image]
  constructor
  · rintro ⟨t, ht, hgr⟩
    exact ⟨t, ht, Quotient.eq'.mpr hgr.symm⟩
  · rintro ⟨t, ht, hgr⟩
    exact ⟨t, ht, Quotient.exact hgr.symm⟩

private lemma inr_sigma_mk_preimage_edgePath_preimage_aux (e e' : E(G)) (C : Set I) :
    Sigma.mk e' ⁻¹' (Sum.inr ⁻¹' {z | ∃ t ∈ C, G.glueRel z (Sum.inr ⟨e, t⟩)}) =
      { x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e', x⟩) (Sum.inr ⟨e, t⟩) } := by
  ext x
  simp only [mem_preimage, mem_setOf_eq]

private lemma isClosed_inr_sigma_mk_preimage_edgePath_preimage_aux_of_ne {e' : E(G)} (hne : e' ≠ e)
    (C : Set I) : IsClosed {x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e', x⟩) (Sum.inr ⟨e, t⟩)} := by
  have hF_sub : {x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e', x⟩) (Sum.inr ⟨e, t⟩) } ⊆ {0, 1} := by
    simp only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff]
    grind
  exact (Finite.subset (by simp) hF_sub).isClosed

private lemma inr_inr_same_edge_set_eq_of_isNonloopAt (e : E(G)) (he : G.IsNonloopAt e (src e))
    (C : Set I) : {x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e, x⟩) (Sum.inr ⟨e, t⟩)} = C := by
  simp [glueRel_inr_inr_iff' e he]

private lemma inr_inr_same_edge_set_subset_union_endpoints (e : E(G)) (C : Set I) :
    {x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e, x⟩) (Sum.inr ⟨e, t⟩)} ⊆ C ∪ {0, 1} := by
  rintro t ht
  simp only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff] at ht
  grind

private lemma subset_inr_inr_same_edge_set (e : E(G)) (C : Set I) :
    C ⊆ {x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e, x⟩) (Sum.inr ⟨e, t⟩)} := by
  rintro t ht
  simp only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff]
  grind

private lemma isClosed_inr_sigma_mk_preimage_edgePath_preimage_aux_of_eq (e : E(G)) {C : Set I}
    (hC : IsClosed C) : IsClosed {x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e, x⟩) (Sum.inr ⟨e, t⟩)} := by
  rw [← diff_union_of_subset (subset_inr_inr_same_edge_set e C)]
  exact (Finite.subset (s := {0, 1}) (by simp) <|
      diff_subset_iff.mpr <| inr_inr_same_edge_set_subset_union_endpoints e C).isClosed.union hC

private lemma isClosed_inr_preimage_edgePath_preimage_aux (e₀ : E(G)) {C : Set I}
    (hC : IsClosed C) : IsClosed (Sum.inr ⁻¹' {z | ∃ t ∈ C, G.glueRel z (Sum.inr ⟨e₀, t⟩)}) := by
  rw [isClosed_sigma_iff]
  intro e'
  rw [inr_sigma_mk_preimage_edgePath_preimage_aux e₀ e']
  obtain rfl | hne := eq_or_ne e' e₀
  · exact isClosed_inr_sigma_mk_preimage_edgePath_preimage_aux_of_eq e' hC
  · exact isClosed_inr_sigma_mk_preimage_edgePath_preimage_aux_of_ne hne C

lemma isClosedMap_edgePath (e0 : E(G)) : IsClosedMap (edgePath e0) := by
  intro C hC
  rw [isClosed_coinduced (f := Quotient.mk'), ← edgePath_preimage_aux_eq_preimage_mk',
    isClosed_sum_iff]
  exact ⟨isClosed_discrete _, isClosed_inr_preimage_edgePath_preimage_aux e0 hC⟩

@[simp]
theorem isClosedEmbedding_edgePath (e : E(G)) (he : G.IsNonloopAt e (src e)) :
    IsClosedEmbedding (edgePath e) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap (edgePath e).continuous
    (edgePath_injective e he) (isClosedMap_edgePath e)

end edgePath

theorem joined_vertexMk_of_isLink {e : β} {x y : α} (h : G.IsLink e x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h.eq_and_eq_or_eq_and_eq <| G.isLink_source_target h.edge_mem
  · simpa [h1, h2, src, tgt] using ⟨edgePath ⟨e, h.edge_mem⟩⟩
  · simpa [h1, h2, src, tgt] using ⟨edgePath ⟨e, h.edge_mem⟩ |>.symm⟩

theorem joined_vertexMk_of_isWalk {w : WList α β} (hw : G.IsWalk w) :
    Joined (vertexMk ⟨w.first, hw.first_mem⟩) (vertexMk ⟨w.last, hw.last_mem⟩) := by
  induction hw with
  | @nil x hx => exact Joined.refl _
  | @cons x e w hw' hlink ih => simpa [last_cons] using (joined_vertexMk_of_isLink hlink).trans ih

theorem joined_vertexMk_of_connBetween {x y : α} (h : G.ConnBetween x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact joined_vertexMk_of_isWalk hw

theorem Preconnected.joined_vertexMk_realMk {v0 : α} (hv0 : v0 ∈ V(G)) (hG : G.Preconnected)
    (a : G.PreRealization) : Joined (vertexMk ⟨v0, hv0⟩) ⟦a⟧ := by
  match a with
  | inl v => simpa using joined_vertexMk_of_connBetween (hG v0 v hv0 v.prop)
  | inr ⟨e, t⟩ =>
    refine (joined_vertexMk_of_connBetween (hG v0 (G.source e.val e.prop) hv0 ?_)).trans ?_
    · exact (G.isLink_source_target e.prop).left_mem
    let p : Path (vertexMk (src e)) (edgePath e t) :=
      edgePath e |>.truncate 0 t |>.cast (by simp [t.prop.1]) (by simp)
    use p <;> simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.coe_coe, Path.source,
    vertexMk_inj, Path.target] <;> rfl

theorem Connected.pathConnectedSpace (h : G.Connected) : PathConnectedSpace G.Realization := by
  obtain ⟨v0, hv0⟩ := h.nonempty
  refine ⟨⟨vertexMk ⟨v0, hv0⟩⟩, Quotient.ind₂ fun a b ↦ ?_⟩
  exact (h.pre.joined_vertexMk_realMk hv0 a).symm.trans (h.pre.joined_vertexMk_realMk hv0 b)

-- instance [G.Finite] : CompactSpace G.Realization := inferInstance

lemma vertexMk_or_edgePath (x : G.Realization) :
    (∃ v : V(G), vertexMk v = x) ∨ ∃ (e : E(G)) (t : I), t ∈ Ioo 0 1 ∧ edgePath e t = x := by
  induction x using Quotient.inductionOn with | h a => _
  match a with
  | .inl v => exact Or.inl ⟨v, rfl⟩
  | .inr ⟨e, t⟩ =>
    by_cases ht0 : 0 = t
    · exact Or.inl ⟨src e, Quotient.sound <| by simp [ht0]⟩
    by_cases ht1 : t = 1
    · exact Or.inl ⟨tgt e, Quotient.sound <| by simp [ht1]⟩
    have h0 : 0 < t := t.prop.1.lt_of_ne (by grind)
    have h1 : t < 1 := t.prop.2.lt_of_ne (by grind)
    exact Or.inr ⟨e, t, ⟨h0, h1⟩, rfl⟩

def foo : Set G.Realization := (range vertexMk)ᶜ

@[simp]
lemma union_edges_eq_foo : ⋃ (e : E(G)), edgePath e '' Ioo 0 1 = G.foo := by
  ext y
  simp only [foo, mem_compl_iff, mem_range, mem_iUnion]
  refine ⟨?_, fun hyS ↦ ?_⟩
  · rintro ⟨e', t', ht', rfl⟩
    exact fun ⟨v, hv⟩ ↦ vertexMk_notMem_edgePath_Ioo v e' ⟨t', ht', hv.symm⟩
  obtain ⟨e', t', ht', rfl⟩ := vertexMk_or_edgePath y |>.resolve_left hyS
  grind

lemma preimage_foo_isClopen (e : E(G)) : IsClopen (G.foo ↓∩ edgePath e '' Ioo 0 1) := by
  have hU_open : IsOpen (edgePath e '' Ioo 0 1) := by
    rw [isOpen_edgePath_image e (by simp) (by simp)]
    exact isOpen_Ioo
  have hU_compl : G.foo \ edgePath e '' Ioo 0 1 = ⋃ (e') (_ : e' ≠ e), edgePath e' '' Ioo 0 1 := by
    ext y
    simp only [mem_diff, mem_compl_iff, mem_range, mem_iUnion, exists_prop, foo]
    refine ⟨fun ⟨hyS, hyU⟩ ↦ ?_, ?_⟩
    · obtain ⟨e', t', ht', rfl⟩ := vertexMk_or_edgePath y |>.resolve_left hyS
      exact ⟨e', fun heq => hyU (heq ▸ mem_image_of_mem _ ht'), t', ht', rfl⟩
    rintro ⟨e', hne, t', ht', rfl⟩
    exact ⟨fun ⟨v, hv⟩ ↦ vertexMk_notMem_edgePath_Ioo v e' ⟨t', ht', hv.symm⟩,
      (((edgePath_Ioo_disjoint_iff_ne e' e).mpr hne).le_bot ⟨mem_image_of_mem _ ht', ·⟩)⟩
  have hU_compl_open : IsOpen (G.foo \ edgePath e '' Ioo 0 1) := by
    rw [hU_compl]
    refine isOpen_biUnion fun e' _ ↦ ?_
    rw [isOpen_edgePath_image e' (by simp) (by simp)]
    exact isOpen_Ioo
  refine ⟨?_, hU_open.preimage continuous_subtype_val⟩
  have eq_compl : (G.foo ↓∩ edgePath e '' Ioo 0 1)ᶜ =
      Subtype.val ⁻¹' (G.foo \ edgePath e '' Ioo 0 1) := by
    rw [← preimage_compl]
    grind
  rw [← isOpen_compl_iff, eq_compl]
  exact isOpen_induced_iff.mpr ⟨G.foo \ edgePath e '' Ioo 0 1, hU_compl_open, rfl⟩

lemma pathComponent_eq_edge (T : Set G.Realization)
    (hT : T ∈ PathComponentPartition (range vertexMk)ᶜ) :
    ∃ e : E(G), T = edgePath e '' Ioo 0 1 := by
  obtain ⟨x, hx⟩ := Partition.nonempty_of_mem hT
  obtain ⟨e, t, ht, rfl⟩ := vertexMk_or_edgePath x |>.resolve_left
    <| by simpa using Partition.subset_of_mem hT hx
  use e
  let S := (range G.vertexMk)ᶜ
  let U := edgePath e '' Ioo 0 1
  have hU_clopen : IsClopen (S ↓∩ U) := preimage_foo_isClopen e
  have hU_pathConn : IsPathConnected U := by
    let f : Ioo (0 : ℝ) 1 → G.Realization := fun x ↦ edgePath e ⟨x.val, ⟨x.prop.1.le, x.prop.2.le⟩⟩
    have hf : Continuous f := (edgePath e).continuous.comp
      (continuous_subtype_val.subtype_mk fun x ↦ ⟨x.prop.1.le, x.prop.2.le⟩)
    have hU_eq : U = range f := by
      ext y
      simp only [U, mem_image, mem_range, Subtype.exists]
      refine ⟨by grind, ?_⟩
      rintro ⟨t', ht', rfl⟩
      use t', Ioo_subset_Icc_self ht', ht'
    rw [hU_eq]
    haveI : PathConnectedSpace (Ioo (0:ℝ) 1) := isPathConnected_iff_pathConnectedSpace.mp
      <| (convex_Ioo 0 1).isPathConnected ⟨2⁻¹, by norm_num⟩
    exact isPathConnected_range hf

  have hUS : U ⊆ S := by
    rintro _ ⟨t', ht', rfl⟩ ⟨v, hv⟩
    exact vertexMk_notMem_edgePath_Ioo v e ⟨t', ht', hv.symm⟩
  have hxU : edgePath e t ∈ U := mem_image_of_mem _ ht
  rw [(PathComponentPartition S).eq_partOf_of_mem hT hx, pathComponentPartition_partOf, eq_comm]
  ext y
  refine ⟨fun hyU ↦ ?_, fun ⟨P, hP⟩ ↦ ?_⟩
  · obtain ⟨P, hP⟩ := hU_pathConn.joinedIn _ hxU _ hyU
    exact ⟨P, fun s ↦ hUS (hP s)⟩
  let PT : I → S := fun s => ⟨P s, hP s⟩
  have hPT : Continuous PT := P.continuous.subtype_mk hP
  let A : Set I := PT ⁻¹' (S ↓∩ U)
  have h0 : (0 : I) ∈ A := by simpa [A, PT]
  have h1 : (1 : I) ∈ A :=
    (show IsClopen A from hU_clopen.preimage hPT).eq_univ ⟨0, h0⟩ ▸ mem_univ 1
  simp only [mem_preimage, Path.target, A, PT] at h1
  exact h1

lemma Realization.graphLike (T : Set G.Realization)
    (hT : T ∈ PathComponentPartition (range vertexMk)ᶜ) : Nonempty (T ≃ₜ Ioo (0 : ℝ) 1) := by
  obtain ⟨e, rfl⟩ := pathComponent_eq_edge T hT
  let f : Ioo (0 : ℝ) 1 → G.Realization := fun x ↦ edgePath e ⟨x.val, ⟨x.prop.1.le, x.prop.2.le⟩⟩
  have hf_cont : Continuous f :=
    (edgePath e).continuous.comp (continuous_subtype_val.subtype_mk _)
  have h_inj : Injective f := by
    intro x y hxy
    simpa [Subtype.ext_iff] using edgePath_inj_on_Ioo x.prop hxy
  have h_range : range f = edgePath e '' Ioo (0 : I) 1 := by
    ext y
    simp only [mem_range, mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.val, ⟨x.prop.1.le, x.prop.2.le⟩⟩, ⟨⟨x.prop.1, x.prop.2⟩, rfl⟩⟩
    · rintro ⟨t, ht, rfl⟩
      use ⟨t.val, ⟨ht.1, ht.2⟩⟩

  let E : Ioo (0 : ℝ) 1 ≃ (edgePath e '' Ioo (0 : I) 1) := Equiv.ofBijective
    (fun x ↦ ⟨f x, h_range ▸ mem_range_self x⟩)
    ⟨fun x y hxy ↦ h_inj (Subtype.mk.inj hxy), fun ⟨y, hy⟩ ↦ by
      obtain ⟨x, rfl⟩ := (h_range.symm ▸ hy : y ∈ range f)
      exact ⟨x, rfl⟩⟩

  refine ⟨E.toHomeomorphOfContinuousOpen (hf_cont.subtype_mk _) (fun U hU ↦ ?_) |>.symm⟩
  have hX0 : (0 : I) ∉ Subtype.val ⁻¹' (Subtype.val '' U) := by
    rintro ⟨u, hu, h_eq⟩
    linarith [u.prop.1, show u.val = 0 from h_eq]
  have hX1 : (1 : I) ∉ Subtype.val ⁻¹' (Subtype.val '' U) := by
    rintro ⟨u, hu, h_eq⟩
    linarith [u.prop.2, show u.val = 1 from h_eq]
  have h3 : IsOpen (edgePath e '' Subtype.val ⁻¹' (Subtype.val '' U)) :=
    (isOpen_edgePath_image e hX0 hX1).mpr <| (isOpen_Ioo.isOpenMap_subtype_val U hU).preimage
      continuous_subtype_val
  have h4 : edgePath e '' Subtype.val ⁻¹' (Subtype.val '' U) = Subtype.val '' (E '' U) := by
    ext y
    simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right, exists_eq_right]
    refine ⟨?_, by grind⟩
    rintro ⟨t, htI, ⟨ht, htU⟩, rfl⟩
    exact ⟨⟨t, htI, ht, rfl⟩, ⟨t, ht, htU, rfl⟩⟩
  have h5 : E '' U = Subtype.val ⁻¹' (Subtype.val '' (E '' U)) := by
    ext ⟨y, hy⟩
    simp
  convert h3.preimage continuous_subtype_val
  rw [h5, h4]

end Graph
