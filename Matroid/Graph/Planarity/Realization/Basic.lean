import Matroid.Graph.Finite
import Matroid.Graph.GraphLike.ArbRel
import Matroid.Graph.Distance
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Maps.Basic
import Matroid.Graph.Planarity.Topology.Path

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path WList Classical ENNReal
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
lemma glueRelAux_inl_inj (u v : V(G)) :G.glueRelAux (Sum.inl u) (Sum.inl v) ↔ u = v := by
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
def edgeMk (e : E(G)) (t : I) : Realization G := Quotient.mk' (s := G.glueRel) (Sum.inr ⟨e, t⟩)

section edgeMk

theorem vertexMk_src_eq_edgeMk_zero (e : E(G)) : vertexMk (src e) = edgeMk e 0 :=
  Quotient.sound (by simp)

theorem vertexMk_tgt_eq_edgeMk_one (e : E(G)) : vertexMk (tgt e) = edgeMk e 1 :=
  Quotient.sound (by simp)

lemma vertexMk_notMem_edgeMk_Ioo (v : V(G)) (e : E(G)) : vertexMk v ∉ edgeMk e '' Ioo 0 1 := by
  rintro ⟨t, ht, heq⟩
  have := Quotient.exact heq
  simp only [glueRel_inr_inl] at this
  grind

lemma edgeMk_Ioo_disjoint_iff_ne (e₁ e₂ : E(G)) :
    Disjoint (edgeMk e₁ '' Ioo 0 1) (edgeMk e₂ '' Ioo 0 1) ↔ e₁ ≠ e₂ := by
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

lemma continuous_edgeMk (e : E(G)) : Continuous (edgeMk e) :=
  letI : UniformSpace E(G) := ⊥
  continuous_quotient_mk'.comp <| continuous_inr.comp <| continuous_sigmaMk

lemma edgeMk_inj_on_Ioo {t₁ t₂ : I} (h₁ : (t₁ : ℝ) ∈ Ioo 0 1) (h : edgeMk e t₁ = edgeMk e t₂) :
    t₁ = t₂ := by
  obtain ⟨-, rfl⟩ | ⟨v, hv₁, hv₂⟩ := (glueRel_inr_inr_iff ..).mp (Quotient.exact h)
  · rfl
  obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := (glueRel_inl_inr ..).mp hv₁ <;> simp at h₁

private lemma edgeMk_injective (e : E(G)) (he : G.IsNonloopAt e (src e)) :
    Injective (edgeMk e) := by
  intro t₁ t₂ h
  have hgr : G.glueRel (Sum.inr ⟨e, t₁⟩) (Sum.inr ⟨e, t₂⟩) := (Quotient.eq (r := G.glueRel)).1 h
  obtain ⟨-, rfl⟩ | ⟨v, hv₁, hv₂⟩ := (glueRel_inr_inr_iff ..).mp (Quotient.exact h)
  · rfl
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (glueRel_inl_inr ..).mp hv₁ <;>
  obtain ⟨rfl, h1⟩ | ⟨rfl, h1⟩ := (glueRel_inl_inr ..).mp hv₂ <;> clear h hv₁ hv₂ hgr <;> (try rfl)
  <;> have hval : G.source e.val e.prop = _ := congrArg Subtype.val (by simpa [eq_comm] using h1)
  <;> have hlink := hval ▸ G.isLink_source_target e.prop <;> exact absurd hlink (he.not_isLoopAt _)

private lemma edgeMk_preimage_image (e : E(G)) {X : Set I} (h0X : 0 ∉ X) (h1X : 1 ∉ X) :
    Quotient.mk' ⁻¹' (edgeMk e '' X) = Sum.inr '' (Sigma.mk e '' X) := by
  ext x
  simp only [mem_preimage, mem_image, Sigma.exists, Sigma.mk.injEq, heq_eq_eq,
    exists_eq_right_right]
  refine Iff.symm ⟨?_, fun ⟨t, ht, h_eq⟩ => ?_⟩
  · rintro ⟨e', t', ⟨ht', rfl⟩, rfl⟩
    exact ⟨t', ht', rfl⟩
  simp only [edgeMk, Quotient.eq'] at h_eq
  match x with
  | inl v => obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := (glueRel_inr_inl ..).mp h_eq <;> tauto
  | inr ⟨e', t'⟩ =>
    simp only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff, inl.injEq,
      exists_eq_left'] at h_eq
    grind

theorem isOpen_edgeMk_image (e : E(G)) {X : Set I} (h0X : 0 ∉ X) (h1X : 1 ∉ X) :
    IsOpen (edgeMk e '' X) ↔ IsOpen X := by
  change IsOpen (Quotient.mk' ⁻¹' (edgeMk e '' X)) ↔ _
  rw [edgeMk_preimage_image e h0X h1X, isOpen_sum_iff]
  simp [IsOpenEmbedding.sigmaMk.isOpen_iff_image_isOpen.symm]

private lemma edgeMk_preimage_aux_eq_preimage_mk' (e : E(G)) (C : Set I) :
    {z | ∃ t ∈ C, G.glueRel z (Sum.inr ⟨e, t⟩)} = Quotient.mk' ⁻¹' (edgeMk e '' C) := by
  ext z
  simp only [mem_setOf_eq, mem_preimage, mem_image]
  constructor
  · rintro ⟨t, ht, hgr⟩
    exact ⟨t, ht, Quotient.eq'.mpr hgr.symm⟩
  · rintro ⟨t, ht, hgr⟩
    exact ⟨t, ht, Quotient.exact hgr.symm⟩

private lemma inr_sigma_mk_preimage_edgeMk_preimage_aux (e e' : E(G)) (C : Set I) :
    Sigma.mk e' ⁻¹' (Sum.inr ⁻¹' {z | ∃ t ∈ C, G.glueRel z (Sum.inr ⟨e, t⟩)}) =
      { x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e', x⟩) (Sum.inr ⟨e, t⟩) } := by
  ext x
  simp only [mem_preimage, mem_setOf_eq]

private lemma isClosed_inr_sigma_mk_preimage_edgeMk_preimage_aux_of_ne {e' : E(G)} (hne : e' ≠ e)
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

private lemma isClosed_inr_sigma_mk_preimage_edgeMk_preimage_aux_of_eq (e : E(G)) {C : Set I}
    (hC : IsClosed C) : IsClosed {x | ∃ t ∈ C, G.glueRel (Sum.inr ⟨e, x⟩) (Sum.inr ⟨e, t⟩)} := by
  rw [← diff_union_of_subset (subset_inr_inr_same_edge_set e C)]
  exact (Finite.subset (s := {0, 1}) (by simp) <|
      diff_subset_iff.mpr <| inr_inr_same_edge_set_subset_union_endpoints e C).isClosed.union hC

private lemma isClosed_inr_preimage_edgeMk_preimage_aux (e₀ : E(G)) {C : Set I} (hC : IsClosed C) :
    IsClosed (Sum.inr ⁻¹' {z | ∃ t ∈ C, G.glueRel z (Sum.inr ⟨e₀, t⟩)}) := by
  rw [isClosed_sigma_iff]
  intro e'
  rw [inr_sigma_mk_preimage_edgeMk_preimage_aux e₀ e']
  obtain rfl | hne := eq_or_ne e' e₀
  · exact isClosed_inr_sigma_mk_preimage_edgeMk_preimage_aux_of_eq e' hC
  · exact isClosed_inr_sigma_mk_preimage_edgeMk_preimage_aux_of_ne hne C

lemma isClosedMap_edgeMk (e0 : E(G)) : IsClosedMap (edgeMk e0) := by
  intro C hC
  rw [isClosed_coinduced (f := Quotient.mk'), ← edgeMk_preimage_aux_eq_preimage_mk',
    isClosed_sum_iff]
  exact ⟨isClosed_discrete _, isClosed_inr_preimage_edgeMk_preimage_aux e0 hC⟩

@[simp]
theorem isClosedEmbedding_edgeMk (e : E(G)) (he : G.IsNonloopAt e (src e)) :
    IsClosedEmbedding (edgeMk e) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap (continuous_edgeMk e)
    (edgeMk_injective e he) (isClosedMap_edgeMk e)

end edgeMk

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

/-- The canonical path along an edge `e` in the realization, from `src e` to `tgt e`. -/
noncomputable def pathAlongEdge (e : E(G)) : Path (vertexMk (src e)) (vertexMk (tgt e)) where
  toContinuousMap := ⟨fun t : I ↦ edgeMk e t, continuous_edgeMk e⟩
  source' := (vertexMk_src_eq_edgeMk_zero e).symm
  target' := (vertexMk_tgt_eq_edgeMk_one e).symm

theorem joined_vertexMk_of_isLink {e : β} {x y : α} (h : G.IsLink e x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h.eq_and_eq_or_eq_and_eq <| G.isLink_source_target h.edge_mem
  · simpa [h1, h2, src, tgt] using ⟨pathAlongEdge ⟨e, h.edge_mem⟩⟩
  · simpa [h1, h2, src, tgt] using ⟨pathAlongEdge ⟨e, h.edge_mem⟩ |>.symm⟩

theorem joined_vertexMk_of_isWalk {w : WList α β} (hw : G.IsWalk w) :
    Joined (vertexMk ⟨w.first, hw.first_mem⟩) (vertexMk ⟨w.last, hw.last_mem⟩) := by
  induction hw with
  | @nil x hx => exact Joined.refl _
  | @cons x e w hw' hlink ih => simpa [last_cons] using (joined_vertexMk_of_isLink hlink).trans ih

theorem joined_vertexMk_of_connBetween {x y : α} (h : G.ConnBetween x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact joined_vertexMk_of_isWalk hw

noncomputable def pathAlongEdgeTo (e : E(G)) (t : I) : Path (vertexMk (src e)) (edgeMk e t) where
  toContinuousMap :=
    ⟨fun s : I ↦ edgeMk e (t * s), (continuous_edgeMk e).comp (continuous_const_mul t)⟩
  source' := by simp [vertexMk_src_eq_edgeMk_zero]
  target' := by simp

theorem joined_vertexMk_edgeMk (e : E(G)) (t : I) : Joined (vertexMk (src e)) (edgeMk e t) :=
  ⟨pathAlongEdgeTo e t⟩

theorem Preconnected.joined_vertexMk_realMk {v0 : α} (hv0 : v0 ∈ V(G)) (hG : G.Preconnected)
    (a : G.PreRealization) : Joined (vertexMk ⟨v0, hv0⟩) ⟦a⟧ := by
  match a with
  | inl v => simpa using joined_vertexMk_of_connBetween (hG v0 v hv0 v.prop)
  | inr ⟨e, t⟩ =>
    refine (joined_vertexMk_of_connBetween (hG v0 (G.source e.val e.prop) hv0 ?_)).trans ?_
    · exact (G.isLink_source_target e.prop).left_mem
    · simpa [src] using joined_vertexMk_edgeMk e t

theorem Connected.pathConnectedSpace (h : G.Connected) : PathConnectedSpace G.Realization := by
  obtain ⟨v0, hv0⟩ := h.nonempty
  refine ⟨⟨vertexMk ⟨v0, hv0⟩⟩, Quotient.ind₂ fun a b ↦ ?_⟩
  exact (h.pre.joined_vertexMk_realMk hv0 a).symm.trans (h.pre.joined_vertexMk_realMk hv0 b)

-- instance [G.Finite] : CompactSpace G.Realization := inferInstance

end Graph

private lemma norm_le_one_iff_fin_1 (x : Fin 1 → ℝ) : ‖x‖ ≤ 1 ↔ ‖x 0‖ ≤ 1 := by simp [Pi.norm_def]
private lemma norm_lt_one_iff_fin_1 (x : Fin 1 → ℝ) : ‖x‖ < 1 ↔ ‖x 0‖ < 1 := by simp [Pi.norm_def]
private lemma norm_eq_one_iff_fin_1 (x : Fin 1 → ℝ) : ‖x‖ = 1 ↔ ‖x 0‖ = 1 := by simp [Pi.norm_def]

namespace Graph

universe u v

variable {α : Type u} {β : Type v} {G : Graph α β} {e : E(G)} {t₁ t₂ : I}

def Realization.cell (G : Graph α β) : ℕ → Type (max u v)
  | 0 => ULift.{v, u} V(G)
  | 1 => ULift.{u, v} E(G)
  | _ + 2 => ULift.{max u v, 0} Empty

@[simps]
def partialEquivVertexMk (v : V(G)) : PartialEquiv (Fin 0 → ℝ) G.Realization where
  toFun x := vertexMk v
  invFun v := 0
  source := Metric.ball 0 1
  target := {vertexMk v}
  map_source' _ _ := rfl
  map_target' := by simp
  left_inv' _ _ := Subsingleton.elim _ _
  right_inv' _ hx := hx.symm

@[simps]
noncomputable def partialEquivEdgeMk (e' : E(G)) : PartialEquiv (Fin 1 → ℝ) G.Realization where
  toFun f := edgeMk e' ⟨max 0 (min 1 ((f 0 + 1) / 2)), by simp [zero_le_one]⟩
  invFun x :=
    if h : x ∈ edgeMk e' '' Ioo 0 1 then
      fun _ ↦ 2 * (Classical.choose h).val - 1
    else 0
  source := Metric.ball 0 1
  target := edgeMk e' '' Ioo 0 1
  map_source' x hx := by
    simp only [Metric.mem_ball, dist_zero_right, norm_lt_one_iff_fin_1, Fin.isValue,
      Real.norm_eq_abs, abs_lt] at hx
    refine ⟨⟨_, by simp [zero_le_one]⟩, ?_, rfl⟩
    change (0 : ℝ) < _ ∧ _ < (1 : ℝ)
    simp only [Fin.isValue, left_lt_sup, inf_le_iff, not_or, not_le, zero_lt_one, Nat.ofNat_pos,
      div_pos_iff_of_pos_right, true_and, sup_lt_iff, inf_lt_left]
    constructor <;> linarith
  map_target' x hx := by
    simp only [hx, ↓reduceDIte, Metric.mem_ball, dist_zero_right, norm_lt_one_iff_fin_1,
      Real.norm_eq_abs]
    obtain ⟨⟨(ht1 : (0 : ℝ) < _), (ht2 : _ < (1 : ℝ))⟩, ht_eq⟩ := Classical.choose_spec hx
    refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  left_inv' := fun x hx ↦ by
    simp only [Metric.mem_ball, dist_zero_right, norm_lt_one_iff_fin_1, Real.norm_eq_abs,
      abs_lt] at hx
    have h_mem : edgeMk e' ⟨max 0 (min 1 ((x 0 + 1) / 2)), by simp [zero_le_one]⟩ ∈
        edgeMk e' '' Ioo 0 1 := by
      refine ⟨⟨_, by simp [zero_le_one]⟩, (?_ : (0 : ℝ) < _ ∧ _ < (1 : ℝ)), rfl⟩
      clear t₁ t₂ e; grind
    simp only [h_mem, ↓reduceDIte]
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain ⟨⟨(ht1 : (0 : ℝ) < _), (ht2 : _ < (1 : ℝ))⟩, ht_eq⟩ := Classical.choose_spec h_mem
    clear t₁ t₂ e; grind [edgeMk_inj_on_Ioo ⟨ht1, ht2⟩ ht_eq]
  right_inv' x' hx' := by
    simp only [hx', ↓reduceDIte]
    obtain ⟨⟨(ht1 : (0 : ℝ) < _), (ht2 : _ < (1 : ℝ))⟩, _⟩ := Classical.choose_spec hx'
    clear t₁ t₂ e; grind

noncomputable def Realization.map (G : Graph α β) :
    ∀ n, Realization.cell G n → PartialEquiv (Fin n → ℝ) G.Realization
  | 0, ⟨v⟩ => partialEquivVertexMk v
  | 1, ⟨e⟩ => partialEquivEdgeMk e
  | _ + 2, ⟨i⟩ => Empty.elim i

lemma continuous_partialEquivEdgeMk (e : E(G)) : Continuous (partialEquivEdgeMk e) :=
  (continuous_edgeMk e).comp <| (continuous_const.max <| continuous_const.min
  <| continuous_apply 0 |>.add continuous_const |>.div_const _).subtype_mk _

lemma continuousOn_quotient {Y : Type*} [TopologicalSpace Y] (U : Set G.Realization) (hU : IsOpen U)
    (f : G.Realization → Y) (hf : ContinuousOn (f ∘ Quotient.mk') (Quotient.mk' ⁻¹' U)) :
    ContinuousOn f U := by
  rw [continuousOn_open_iff hU]
  exact (continuousOn_open_iff (hU.preimage continuous_quotient_mk')).mp hf

lemma image_map_closedBall (e : E(G)) :
    Realization.map G 1 ⟨e⟩ '' Metric.closedBall 0 1 = range (edgeMk e) := by
  ext x
  simp only [Realization.map, mem_image, Metric.mem_closedBall, dist_zero_right,
    partialEquivEdgeMk_apply]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨max 0 (min 1 ((f 0 + 1) / 2)), by simp [zero_le_one]⟩, rfl⟩
  rintro ⟨⟨t, ht1, ht2⟩, rfl⟩
  use fun _ ↦ 2 * t - 1, ?_, ?_
  · rw [norm_le_one_iff_fin_1, Real.norm_eq_abs, abs_le]
    grind
  simp [ht1, ht2]

noncomputable instance : Topology.CWComplex (univ : Set G.Realization) where
  cell := Realization.cell G
  map := Realization.map G
  source_eq n i := match n, i with
  | 0, ⟨_⟩ => rfl
  | 1, ⟨_⟩ => rfl
  | _ + 2, ⟨i⟩ => Empty.elim i
  continuousOn n i := match n, i with
  | 0, ⟨_⟩ => continuous_const.continuousOn
  | 1, ⟨e⟩ => (continuous_partialEquivEdgeMk ..).continuousOn
  | _ + 2, ⟨i⟩ => Empty.elim i
  continuousOn_symm n i := match n, i with
  | 0, ⟨_⟩ => continuous_const.continuousOn
  | 1, ⟨e⟩ => by
    change ContinuousOn (partialEquivEdgeMk e).invFun (edgeMk e '' Ioo (0 : I) (1 : I))
    refine continuousOn_quotient _ ?_ _ ?_
    · rw [isOpen_edgeMk_image e (by simp) (by simp)]
      exact isOpen_Ioo
    rw [edgeMk_preimage_image e (by simp) (by simp)]
    let f_pre : G.PreRealization → Fin 1 → ℝ := fun x ↦ match x with
    | Sum.inl _ => 0
    | Sum.inr ⟨e', t'⟩ => fun _ ↦ 2 * t' - 1
    have h_f_pre_cont : Continuous f_pre := by
      refine continuous_sum_dom.mpr ⟨continuous_of_discreteTopology, continuous_pi fun i ↦ ?_⟩
      exact (continuous_const.mul <| continuous_subtype_val.comp Sigma.continuous_snd).sub
        continuous_const
    refine ContinuousOn.congr h_f_pre_cont.continuousOn fun x hx ↦ ?_
    ext i
    simp only [mem_image, Sigma.exists, Sigma.mk.injEq, heq_eq_eq, exists_eq_right_right] at hx
    obtain ⟨e', t', ⟨ht', rfl⟩, rfl⟩ := hx
    have h_mem : Quotient.mk' (Sum.inr ⟨e, t'⟩) ∈ edgeMk e '' Ioo (0 : I) (1 : I) := ⟨t', ht', rfl⟩
    simp only [h_mem, ↓reduceDIte, comp_apply, partialEquivEdgeMk, f_pre,
      ← edgeMk_inj_on_Ioo ht' h_mem.choose_spec.2.symm]
  | _ + 2, ⟨i⟩ => Empty.elim i
  pairwiseDisjoint' := by
    rintro ⟨n₁, i₁⟩ _ ⟨n₂, i₂⟩ _ hne
    have he : ∀ e : E(G), _ '' (Metric.ball 0 1 : Set <| Fin 1 → ℝ) = edgeMk e '' Ioo 0 1 :=
      (partialEquivEdgeMk · |>.image_source_eq_target)
    have hv : ∀ v : V(G), _ '' (Metric.ball 0 1 : Set <| Fin 0 → ℝ) = {vertexMk v} :=
      (partialEquivVertexMk · |>.image_source_eq_target)
    match n₁, i₁, n₂, i₂ with
    | 0, ⟨v₁⟩, 0, ⟨v₂⟩ =>
      replace hne : v₁ ≠ v₂ := by tauto
      simpa [Realization.map, Function.onFun, hv]
    | 0, ⟨v₁⟩, 1, ⟨e₂⟩ =>
      simp only [Realization.map, Function.onFun, he, hv, disjoint_singleton_left]
      exact vertexMk_notMem_edgeMk_Ioo v₁ e₂
    | 1, ⟨e₁⟩, 0, ⟨v₂⟩ =>
      simp only [Realization.map, Function.onFun, he, hv, disjoint_singleton_right]
      exact vertexMk_notMem_edgeMk_Ioo v₂ e₁
    | 1, ⟨e₁⟩, 1, ⟨e₂⟩ =>
      replace hne : e₁ ≠ e₂ := by tauto
      simpa only [Realization.map, Function.onFun, he, edgeMk_Ioo_disjoint_iff_ne]
    | n₁ + 2, ⟨i₁⟩, _, _ => exact Empty.elim i₁
    | _, _, n₂ + 2, ⟨i₂⟩ => exact Empty.elim i₂
  mapsTo' n i :=
    match n, i with
    | 0, ⟨v⟩ => by
      refine ⟨fun _ ↦ ∅, fun _ ↦ ?_⟩
      simp [mem_sphere_iff_norm, norm_eq_zero_of_subsingleton]
    | 1, ⟨e⟩ => by
      refine ⟨fun m ↦ match m with | 0 => {⟨src e⟩, ⟨tgt e⟩} | _ => ∅, fun x hx ↦ ?_⟩
      simp only [mem_sphere_iff_norm, sub_zero, norm_eq_one_iff_fin_1, Fin.isValue,
        Real.norm_eq_abs, zero_le_one, abs_eq] at hx
      obtain hx | hx := hx <;> simp [hx, Realization.map, vertexMk_tgt_eq_edgeMk_one,
        vertexMk_src_eq_edgeMk_zero]
    | n + 2, ⟨i⟩ => Empty.elim i
  closed' A _ h := by
    rw [isClosed_coinduced, isClosed_sum_iff, isClosed_sigma_iff]
    refine ⟨isClosed_discrete _, fun e ↦ ?_⟩
    simpa [image_map_closedBall] using (h 1 ⟨e⟩).preimage (continuous_edgeMk e)
  union' := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    refine Quotient.inductionOn x fun x ↦ ?_
    match x with
    | inl v => exact ⟨0, ⟨v⟩, by simp [Realization.map, vertexMk, Quotient.mk']⟩
    | inr ⟨e, t⟩ =>
      refine ⟨1, ⟨e⟩, ?_⟩
      rw [image_map_closedBall, mem_range]
      exact ⟨t, rfl⟩

end Graph
