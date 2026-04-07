import Matroid.Graph.Planarity.Realization.Basic
import Matroid.Graph.Planarity.Topology.Path

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

namespace Graph

def IsSubgraph.RealizationEmbeddingAux (h : H ≤ G) : C(H.PreRealization, G.PreRealization) where
  toFun x := match x with
  | inl v => inl ⟨v.val, h.vertex_subset v.prop⟩
  | inr ⟨e, t⟩ => inr ⟨⟨e.val, edgeSet_mono h e.prop⟩, t⟩
  continuous_toFun := by
    refine continuous_sum_dom.mpr ⟨continuous_of_discreteTopology, ?_⟩
    exact continuous_sigma_iff.mpr fun _ ↦  continuous_inr.comp continuous_sigmaMk

def IsSubgraph.RealizationEmbedding (h : H ≤ G) : H.Realization → G.Realization := by
  refine Quotient.map h.RealizationEmbeddingAux fun x y hrel ↦ ?_
  simp only [RealizationEmbeddingAux, ContinuousMap.coe_mk]
  match x, y with
  | inl u, inl v => simp_all
  | inl u, inr ⟨e, t⟩ => simp_all [src, tgt, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e, t⟩, inl u => simp_all [src, tgt, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e₁, t₁⟩, inr ⟨e₂, t₂⟩ =>
    simp_all only [glueRel_inr_inr_iff, glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff, inl.injEq,
      src, tgt, exists_eq_left', Subtype.exists, Subtype.mk.injEq, exists_and_left, exists_prop]
    obtain ⟨rfl, rfl⟩ | ⟨u, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), h2, (⟨rfl, h1⟩ | ⟨rfl, h1⟩)⟩ := hrel
    · tauto
    all_goals
    · simp only [zero_ne_one, one_ne_zero, exists_eq_left, source_mem, target_mem, and_true,
        true_and, and_false, false_and, or_false, false_or]
      simp [h.source, h.target, h1]

private lemma IsSubgraph.RealizationEmbedding_injective (h : H ≤ G) :
    Injective h.RealizationEmbedding := by
  rintro x y
  refine Quotient.inductionOn₂ x y fun x y ↦ ?_
  simp only [RealizationEmbedding, Quotient.map_mk, RealizationEmbeddingAux, ContinuousMap.coe_mk,
    Quotient.eq]
  match x, y with
  | inl u, inl v => simp [Subtype.val_inj]
  | inl u, inr ⟨e, t⟩ => simp [src, tgt, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e, t⟩, inl u => simp [src, tgt, ← Subtype.val_inj (a := u), h.source, h.target]
  | inr ⟨e₁, t₁⟩, inr ⟨e₂, t₂⟩ =>
    simp only [glueRel_inr_inr_iff, Subtype.mk.injEq, glueRel_inl_iff_glueRelAux,
      glueRelAux_inr_iff, inl.injEq, src, tgt, exists_eq_left', Subtype.exists, exists_and_left,
      exists_prop, Subtype.coe_inj]
    rintro (⟨rfl, rfl⟩ | ⟨u, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), h2, (⟨rfl, h1⟩ | ⟨rfl, h1⟩)⟩)
    · tauto
    all_goals
    · simp only [zero_ne_one, one_ne_zero, exists_eq_left, source_mem, target_mem, and_true,
        true_and, and_false, false_and, or_false, false_or]
      simp_all [h.source, h.target]

lemma IsSubgraph.RealizationEmbedding_isEmbedding (h : H ≤ G) :
    Topology.IsEmbedding h.RealizationEmbedding where
  eq_induced := by
    ext s
    change IsOpen (Quotient.mk' ⁻¹' s) ↔ ∃ t, _
    refine ⟨fun hs ↦ ⟨h.RealizationEmbedding '' s ∪ (range h.RealizationEmbedding)ᶜ, ?_,
      by simp [h.RealizationEmbedding_injective.preimage_image]⟩, ?_⟩
    · rw [isOpen_coinduced, isOpen_sum_iff, isOpen_sigma_iff]
      refine ⟨isOpen_discrete _, fun e ↦ ?_⟩
      simp only [preimage_union, preimage_compl]
      by_cases heH : e.val ∈ E(H)
      · have h1 : (fun t ↦ Quotient.mk' (inr ⟨e, t⟩)) ⁻¹'
          (RealizationEmbedding h '' s ∪ (range (RealizationEmbedding h))ᶜ) =
          (fun t ↦ Quotient.mk' (inr ⟨⟨e.val, heH⟩, t⟩)) ⁻¹' s := by
          ext t
          simp only [preimage_union, preimage_compl, mem_union, mem_preimage, mem_compl_iff,
            mem_range, not_exists]
          constructor
          · rintro (⟨x, hx, hx_eq⟩ | hnot)
            · have h_eq : RealizationEmbedding h (Quotient.mk' (inr ⟨⟨e.val, heH⟩, t⟩)) =
                Quotient.mk' (inr ⟨e, t⟩) := rfl
              rw [← h_eq] at hx_eq
              have := h.RealizationEmbedding_injective hx_eq
              rwa [this] at hx
            · exfalso
              apply hnot (Quotient.mk' (inr ⟨⟨e.val, heH⟩, t⟩))
              rfl
          · intro ht
            left
            use Quotient.mk' (inr ⟨⟨e.val, heH⟩, t⟩)
            exact ⟨ht, rfl⟩
        change IsOpen ((fun t ↦ Quotient.mk' (inr ⟨e, t⟩)) ⁻¹'
          (RealizationEmbedding h '' s ∪ (range (RealizationEmbedding h))ᶜ))
        rw [h1]
        have h2 : IsOpen (Quotient.mk' ⁻¹' s) := hs
        rw [isOpen_sum_iff] at h2
        have h3 := h2.2
        rw [isOpen_sigma_iff] at h3
        exact h3 ⟨e.val, heH⟩
      · change IsOpen ((fun t ↦ Quotient.mk' (inr ⟨e, t⟩)) ⁻¹'
          (RealizationEmbedding h '' s ∪ (range (RealizationEmbedding h))ᶜ))
        apply isOpen_of_Ioo_subset
        intro t ht
        simp only [preimage_union, preimage_compl, mem_union, mem_preimage, mem_compl_iff,
          mem_range, not_exists]
        right
        intro x hx
        revert hx
        refine Quotient.inductionOn x fun x ↦ ?_
        intro hx
        match x with
        | inl v =>
          unfold RealizationEmbedding at hx
          simp only [Quotient.map_mk, RealizationEmbeddingAux, ContinuousMap.coe_mk] at hx
          have hx' := Quotient.exact hx
          simp only [glueRel_inl_iff_glueRelAux, glueRelAux_inr_iff] at hx'
          rcases hx' with ⟨u, hu, (⟨rfl, hu2⟩ | ⟨rfl, hu2⟩)⟩
          · exact ne_of_gt ht.1 rfl
          · exact ne_of_lt ht.2 rfl
        | inr ⟨e', t'⟩ =>
          unfold RealizationEmbedding at hx
          simp only [Quotient.map_mk, RealizationEmbeddingAux, ContinuousMap.coe_mk] at hx
          have hx' := Quotient.exact hx
          simp only [glueRel_inr_inr_iff, Subtype.mk.injEq, glueRel_inl_iff_glueRelAux,
            glueRelAux_inr_iff, inl.injEq, src, tgt, exists_eq_left', Subtype.exists,
            exists_and_left, exists_prop] at hx'
          rcases hx' with ⟨he_eq, ht_eq⟩ |
            ⟨a, (⟨rfl, ha1⟩ | ⟨rfl, ha1⟩), ha2, (⟨rfl, ha3⟩ | ⟨rfl, ha3⟩)⟩
          · rw [← he_eq] at heH
            exact heH e'.prop
          · exact ne_of_gt ht.1 rfl
          · exact ne_of_lt ht.2 rfl
          · exact ne_of_gt ht.1 rfl
          · exact ne_of_lt ht.2 rfl
    rintro ⟨t, ht, rfl⟩
    change IsOpen (Quotient.mk' ⁻¹' t) at ht
    unfold RealizationEmbedding
    rw [← preimage_comp]
    generalize_proofs hh
    have : Quotient.map h.RealizationEmbeddingAux hh ∘ Quotient.mk' =
        Quotient.mk' ∘ h.RealizationEmbeddingAux := by
      ext x
      simp only [Quotient.mk', comp_apply, Quotient.map_mk]
      rfl
    rw [this, preimage_comp]
    exact h.RealizationEmbeddingAux.continuous.isOpen_preimage _ ht
  injective := h.RealizationEmbedding_injective

def IsSubgraph.realizationContinuousMap (h : H ≤ G) : C(H.Realization, G.Realization) where
  toFun := h.RealizationEmbedding
  continuous_toFun := h.RealizationEmbedding_isEmbedding.continuous
