module

public import Matroid.Graph.Planarity.Realization.Basic
public import Matroid.ForMathlib.Topology.Path

@[expose] public section

variable {α β E : Type*} [MetricSpace E] {G H : Graph α β} {S T : Set α}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path
open scoped unitInterval

lemma isOpen_of_Ioo_subset {U : Set I} (h : Ioo (0 : I) 1 ⊆ U) : IsOpen U := by
  have huniv : ∀ x : I, x ∈ insert 0 (insert 1 (Ioo (0 : I) 1)) := by
    rintro x
    simp [x.prop.2, ← Subtype.coe_le_coe]
  have h1 : (U = Ioo (0 : I) 1 ∨ U = Ioc (0 : I) 1) ∨ (U = Ico (0 : I) 1 ∨ U = univ) := by
    by_cases h0 : (0 : I) ∈ U <;> [right; left] <;> by_cases h1 : (1 : I) ∈ U
    <;> [right; left; right; left] <;> ext x
    · grind
    · rw [← Ioo_insert_left (by simp)]
      grind
    · rw [← Ioo_insert_right (by simp)]
      grind
    · grind
  rcases h1 with (rfl | rfl) | (rfl | rfl)
  · exact isOpen_Ioo
  · have : Ioc (0 : I) 1 = (fun x : I ↦ (x : ℝ)) ⁻¹' Ioi 0 := by
      ext x
      simp only [mem_Ioc, mem_preimage, mem_Ioi]
      exact ⟨fun h => h.1, fun h => ⟨h, x.prop.2⟩⟩
    rw [this]
    exact continuous_subtype_val.isOpen_preimage _ isOpen_Ioi
  · have : Ico (0 : I) 1 = (fun x : I ↦ (x : ℝ)) ⁻¹' Iio 1 := by
      ext x
      simp only [mem_Ico, mem_preimage, mem_Iio]
      exact ⟨fun h => h.2, fun h => ⟨x.prop.1, h⟩⟩
    rw [this]
    exact continuous_subtype_val.isOpen_preimage _ isOpen_Iio
  · exact isOpen_univ

namespace Graph.IsSubgraph

def RealizationEmbeddingAux (h : H ≤ G) : C(H.PreRealization, G.PreRealization) where
  toFun x := match x with
  | inl v => inl ⟨v.val, h.vertexSet_mono v.prop⟩
  | inr ⟨e, t⟩ => inr ⟨⟨e.val, edgeSet_mono h e.prop⟩, t⟩
  continuous_toFun := continuous_sum_dom.mpr ⟨continuous_of_discreteTopology,
    continuous_sigma_iff.mpr fun _ ↦  continuous_inr.comp continuous_sigmaMk⟩

def RealizationEmbedding (h : H ≤ G) : H.Realization → G.Realization := by
  refine Quotient.map h.RealizationEmbeddingAux fun x y hrel ↦ ?_
  simp only [RealizationEmbeddingAux, ContinuousMap.coe_mk]
  match x, y with
  | inl u, inl v => simp_all
  | inl u, inr ⟨e, t⟩ =>
    simp_all [edgeSource, edgeTarget, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e, t⟩, inl u =>
    simp_all [edgeSource, edgeTarget, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e₁, t₁⟩, inr ⟨e₂, t₂⟩ =>
    simp_all only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff, inl.injEq,
      edgeSource, edgeTarget, exists_eq_left', Subtype.exists, Subtype.mk.injEq,
      exists_and_left, exists_prop]
    obtain ⟨rfl, rfl⟩ | ⟨u, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), h2, (⟨rfl, h1⟩ | ⟨rfl, h1⟩)⟩ := hrel
    · tauto
    all_goals
    · simp only [zero_ne_one, one_ne_zero, exists_eq_left, source_mem, target_mem, and_true,
        true_and, and_false, false_and, or_false, false_or]
      simp [h.source, h.target, h1]

private lemma RealizationEmbedding_injective (h : H ≤ G) : Injective h.RealizationEmbedding := by
  rintro x y
  refine Quotient.inductionOn₂ x y fun x y ↦ ?_
  simp only [RealizationEmbedding, Quotient.map_mk, RealizationEmbeddingAux, ContinuousMap.coe_mk,
    Quotient.eq]
  match x, y with
  | inl u, inl v => simp [Subtype.val_inj]
  | inl u, inr ⟨e, t⟩ =>
    simp [edgeSource, edgeTarget, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e, t⟩, inl u =>
    simp [edgeSource, edgeTarget, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e₁, t₁⟩, inr ⟨e₂, t₂⟩ =>
    simp only [glueRel_inr_inr_iff, Subtype.mk.injEq, glueRel_inl_iff_glueRelAux,
      glueRelAux_inr_iff, inl.injEq, edgeSource, edgeTarget, exists_eq_left',
      Subtype.exists, exists_and_left, exists_prop, Subtype.coe_inj]
    rintro (⟨rfl, rfl⟩ | ⟨u, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), h2, (⟨rfl, h1⟩ | ⟨rfl, h1⟩)⟩)
    · tauto
    all_goals
    · simp only [zero_ne_one, one_ne_zero, exists_eq_left, source_mem, target_mem, and_true,
        true_and, and_false, false_and, or_false, false_or]
      simp_all [h.source, h.target]

/-! ### API for `RealizationEmbedding`

The proof of `RealizationEmbedding_isEmbedding` below currently manipulates `Quotient.mk'` by
hand. The lemmas in this section, together with `Realization.mk` and `Realization.isOpen_iff` in
`Realization.Basic`, are meant to replace that plumbing; each is cross-referenced from a comment
in the proof. -/

@[simp]
lemma RealizationEmbedding_mk (h : H ≤ G) (x : H.PreRealization) :
    h.RealizationEmbedding (Realization.mk H x) = .mk G (h.RealizationEmbeddingAux x) := rfl

@[simp]
lemma RealizationEmbedding_vertexMk (h : H ≤ G) (v : V(H)) :
    h.RealizationEmbedding (vertexMk v) = vertexMk ⟨v.val, h.vertexSet_mono v.prop⟩ := rfl

@[simp]
lemma RealizationEmbedding_edgePath (h : H ≤ G) (e : E(H)) (t : I) :
    h.RealizationEmbedding (edgePath e t) = edgePath ⟨e.val, edgeSet_mono h e.prop⟩ t := rfl

/-- Continuity of `RealizationEmbedding`, proved once from the universal property of the quotient
instead of inline.-/
lemma continuous_RealizationEmbedding (h : H ≤ G) : Continuous h.RealizationEmbedding := by
  rw [continuous_coinduced_dom]
  exact (Realization.mk G).continuous.comp h.RealizationEmbeddingAux.continuous

/-- An edge of `H`, viewed in `G`, meets the image of `s` exactly where the corresponding edge of
`H` meets `s`. This is the injectivity computation. -/
lemma preimage_edgePath_image_RealizationEmbedding (h : H ≤ G) {e : E(G)} (he : e.val ∈ E(H))
    (s : Set H.Realization) :
    edgePath e ⁻¹' (h.RealizationEmbedding '' s) = edgePath ⟨e.val, he⟩ ⁻¹' s := by
  ext t
  simp only [mem_preimage, mem_image]
  exact ⟨fun ⟨x, hx, hx_eq⟩ ↦ (h.RealizationEmbedding_injective
    (RealizationEmbedding_edgePath h ⟨e.val, he⟩ t ▸ hx_eq)) ▸ hx,
    fun ht ↦ ⟨Quotient.mk' (inr ⟨⟨e.val, he⟩, t⟩), ⟨ht, rfl⟩⟩⟩

/-- An edge of `G` that is an edge of `H` lies entirely inside the image. -/
lemma edgePath_mem_range_RealizationEmbedding (h : H ≤ G) {e : E(G)} (he : e.val ∈ E(H)) (t : I) :
    edgePath e t ∈ range h.RealizationEmbedding :=
  ⟨edgePath ⟨e.val, he⟩ t, RealizationEmbedding_edgePath h ⟨e.val, he⟩ t⟩

/-- The form in which `preimage_edgePath_image_RealizationEmbedding` is used: on an edge of `H`
the complement of the range contributes nothing, by
`edgePath_mem_range_RealizationEmbedding`. -/
lemma preimage_edgePath_image_union_compl_range (h : H ≤ G) {e : E(G)} (he : e.val ∈ E(H))
    (s : Set H.Realization) :
    edgePath e ⁻¹' (h.RealizationEmbedding '' s ∪ (range h.RealizationEmbedding)ᶜ) =
      edgePath ⟨e.val, he⟩ ⁻¹' s := by
  rw [preimage_union, preimage_compl, eq_univ_of_forall (show ∀ x,
    x ∈ (edgePath e) ⁻¹' (range (RealizationEmbedding h)) from
    h.edgePath_mem_range_RealizationEmbedding he), compl_univ, union_empty,
    preimage_edgePath_image_RealizationEmbedding h he]

/-- The interior of an edge of `G` that is not an edge of `H` misses the image of `H`. -/
lemma edgePath_notMem_range_RealizationEmbedding (h : H ≤ G) {e : E(G)} (he : e.val ∉ E(H)) {t : I}
    (ht : t ∈ Ioo (0 : I) 1) : edgePath e t ∉ range h.RealizationEmbedding := by
  simp only [mem_range, not_exists, ne_eq]
  intro y
  induction y using Realization.ind with | h x => ?_
  intro hx
  rw [RealizationEmbedding_mk, ← Realization.mk_inr, eq_comm, Realization.mk_eq_mk,
    glueRel_inr_interior_iff_eq ⟨ht.1.ne', ht.2.ne⟩ _] at hx
  obtain v | ⟨e', t'⟩ := x
  · simp [RealizationEmbeddingAux] at hx
  simp only [RealizationEmbeddingAux, ContinuousMap.coe_mk, inr.injEq, Sigma.mk.injEq,
    Subtype.ext_iff, heq_eq_eq] at hx
  exact he (hx.1 ▸ e'.prop)

lemma RealizationEmbedding_isEmbedding (h : H ≤ G) :
    Topology.IsEmbedding h.RealizationEmbedding where
  eq_induced := by
    ext s
    rw [Realization.isOpen_iff s]
    refine ⟨fun hs ↦ ⟨h.RealizationEmbedding '' s ∪ (range h.RealizationEmbedding)ᶜ, ?_,
      by simp [h.RealizationEmbedding_injective.preimage_image]⟩, ?_⟩
    · rw [Realization.isOpen_iff]
      intro e
      by_cases heH : e.val ∈ E(H)
      · rw [preimage_edgePath_image_union_compl_range h heH]
        exact hs ⟨e.val, heH⟩
      · exact isOpen_of_Ioo_subset fun _ ht ↦
          Or.inr (h.edgePath_notMem_range_RealizationEmbedding heH ht)
    rintro ⟨t, ht, rfl⟩
    exact (Realization.isOpen_iff _).mp (ht.preimage h.continuous_RealizationEmbedding)
  injective := h.RealizationEmbedding_injective

def realizationContinuousMap (h : H ≤ G) : C(H.Realization, G.Realization) where
  toFun := h.RealizationEmbedding
  continuous_toFun := h.RealizationEmbedding_isEmbedding.continuous

-- /-- The inclusion of a subgraph between weak realizations. -/
-- def IsSubgraph.weakRealizationEmbedding (h : H ≤ G) :
--     Realization.Weak H → Realization.Weak G :=
--   h.RealizationEmbedding

-- lemma IsSubgraph.weakRealizationEmbedding_isEmbedding (h : H ≤ G) :
--     Topology.IsEmbedding h.weakRealizationEmbedding :=
--   h.RealizationEmbedding_isEmbedding

-- /-- The inclusion of a subgraph as a continuous map between weak realizations. -/
-- def IsSubgraph.weakRealizationContinuousMap (h : H ≤ G) :
--     C(Realization.Weak H, Realization.Weak G) where
--   toFun := h.weakRealizationEmbedding
--   continuous_toFun := h.weakRealizationEmbedding_isEmbedding.continuous
