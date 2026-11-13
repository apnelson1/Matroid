module

public import Mathlib.Topology.Order.IntermediateValue
public import Matroid.MiniTauCeti.JCT.Topology.Path

@[expose] public section

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a b c u v w x y z : α}
  {A C X Y : Set α}

open Set Function TopologicalSpace Topology Metric Nat unitInterval Set.Notation AddCircle

def IsArc {α} [TopologicalSpace α] (A : Set α) : Prop :=
  ∃ f : C(unitInterval, α), Injective f ∧ range f = A

lemma IsArc.isPathConnected (hA : IsArc A) : IsPathConnected A := by
  obtain ⟨f, hf, rfl⟩ := hA
  exact isPathConnected_range f.continuous

lemma IsArc.isCompact (hA : IsArc A) : IsCompact A := by
  obtain ⟨f, -, rfl⟩ := hA
  exact isCompact_range f.continuous

lemma unitInterval_isArc : IsArc (univ : Set unitInterval) :=
  ⟨ContinuousMap.id unitInterval, injective_id, by simp⟩

lemma segment_isArc {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
    [ContinuousSMul ℝ E] {a b : E} (hab : a ≠ b) : IsArc (segment ℝ a b) :=
  ⟨(Path.segment a b).toContinuousMap, Path.segment_injective_of_ne hab, Path.range_segment a b⟩

lemma IsArc.image (hA : IsArc A) {f : C(α, β)} (hf : Injective f) :
    IsArc (f '' A) := by
  obtain ⟨f', hf', rfl⟩ := hA
  use f.comp f', hf.comp hf', by simp [range_comp]

lemma range_path_isArc (P : Path x y) (hP : Injective P) : IsArc (range P) :=
  ⟨P, hP, rfl⟩

noncomputable def IsArc.ends (A : Set α) (hA : IsArc A) : Sym2 α :=
  s(hA.choose 0, hA.choose 1)

section UnitIntervalArc

variable {t : unitInterval}

lemma unitInterval_univ_sdiff_zero : (univ \ {0} : Set I) = Ioc 0 1 := by
  ext x
  simp only [mem_sdiff, mem_univ, mem_singleton_iff, true_and, mem_Ioc,
    unitInterval.pos_iff_ne_zero, ne_eq, le_one', and_true]

lemma isPreconnected_unitInterval_sdiff_zero : IsPreconnected (univ \ {0} : Set I) := by
  rw [unitInterval_univ_sdiff_zero]
  exact isPreconnected_Ioc

lemma not_isPreconnected_unitInterval_sdiff_mem_Ioo (ht : t ∈ Ioo (0 : I) 1) :
    ¬ IsPreconnected (univ \ {t} : Set I) := by
  intro h
  have hsub : (univ \ {t} : Set I) ⊆ Iio t ∪ Ioi t := by
    intro x hx
    simp only [mem_sdiff, mem_union, mem_Iio, mem_Ioi] at hx ⊢
    exact lt_or_gt_of_ne hx.2
  have hleft : ((univ \ {t} : Set I) ∩ Iio t).Nonempty :=
    ⟨0, ⟨mem_univ 0, (ne_of_gt ht.1).symm⟩, by simp [mem_Iio, ht.1]⟩
  have hright : ((univ \ {t} : Set I) ∩ Ioi t).Nonempty :=
    ⟨1, ⟨mem_univ 1, (ne_of_lt ht.2).symm⟩, by simp [mem_Ioi, ht.2]⟩
  obtain hlt | hgt := h.subset_or_subset isOpen_Iio isOpen_Ioi Iio_disjoint_Ioi_same hsub
  · exact lt_asymm (by simpa [mem_Iio] using hlt ⟨mem_univ 1, (ne_of_lt ht.2).symm⟩)
      <| by simp [ht.2]
  exact lt_asymm (by simpa [mem_Ioi] using hgt ⟨mem_univ 0, (ne_of_gt ht.1).symm⟩)
    <| show 0 < t by simp [ht.1]

lemma mem_arc_choose_ends_of_range_sdiff_preconnected [T2Space α] {f : C(I, α)}
    (hf : Injective f) {z : α} (hz : z ∈ range f) (hconn : IsPreconnected (range f \ {z})) :
    z = f 0 ∨ z = f 1 := by
  obtain ⟨t, _, rfl⟩ := hz
  by_cases ht0 : t = 0
  · exact Or.inl <| congrArg f ht0
  by_cases ht1 : t = 1
  · exact Or.inr <| congrArg f ht1
  have htIoo : t ∈ Ioo (0 : I) 1 :=
    ⟨lt_of_le_of_ne t.2.1 (fun h => ht0 h.symm), lt_of_le_of_ne t.2.2 ht1⟩
  rw [← image_univ, ← image_singleton, ← image_sdiff hf] at hconn
  exact (not_isPreconnected_unitInterval_sdiff_mem_Ioo htIoo
    <| f.continuous.isClosedEmbedding hf |>.isInducing.isPreconnected_image.mp hconn).elim

end UnitIntervalArc

lemma range_path_sdiff_source_preconnected [T2Space α] (P : Path x y) (hP : Injective P) :
    IsPreconnected (range P \ {x}) := by
  have h : IsPreconnected (range P \ {P 0}) := by
    rw [← image_univ, ← image_singleton, ← image_sdiff hP]
    exact P.continuous.isClosedEmbedding hP |>.isInducing.isPreconnected_image.mpr
      isPreconnected_unitInterval_sdiff_zero
  simpa [P.source] using h

lemma range_path_sdiff_target_preconnected [T2Space α] (P : Path x y) (hP : Injective P) :
    IsPreconnected (range P \ {y}) := by
  have h : IsPreconnected (range P \ {P 1}) := by
    rw [← image_univ, ← image_singleton, ← image_sdiff hP, show (univ \ {1} : Set I) = Ico 0 1 from
      by ext u; simp [mem_Ico, unitInterval.lt_one_iff_ne_one]]
    exact P.continuous.isClosedEmbedding hP |>.isInducing.isPreconnected_image.mpr
      isPreconnected_Ico
  simpa [P.target] using h

lemma IsArc.ends_eq_path_source_target [T2Space α] (P : Path x y) (hP : Injective P)
    (hAP : range P = A) (hA : IsArc A) : IsArc.ends A hA = s(x, y) := by
  subst A
  unfold ends
  set f := hA.choose with hfdef
  have hf_inj : Injective f := hA.choose_spec.1
  have hf_range : range f = range P := hfdef ▸ hA.choose_spec.2
  have hxy : x ≠ y := fun h => hP.ne (by simp) (P.source.trans (h.trans P.target.symm))
  have hx : x = f 0 ∨ x = f 1 :=
    mem_arc_choose_ends_of_range_sdiff_preconnected hf_inj (hf_range ▸ P.source_mem_range)
      (hf_range ▸ range_path_sdiff_source_preconnected P hP)
  have hy : y = f 0 ∨ y = f 1 :=
    mem_arc_choose_ends_of_range_sdiff_preconnected hf_inj (hf_range ▸ Path.target_mem_range P)
      (hf_range ▸ range_path_sdiff_target_preconnected P hP)
  grind

lemma IsArc.exists_path_from (hA : IsArc A) (hx : x ∈ hA.ends) :
    ∃ y, ∃ P : Path x y, Injective P ∧ range P = A := by
  obtain ⟨hf_inj, hf_range⟩ := hA.choose_spec
  let P : Path (hA.choose 0) (hA.choose 1) := ⟨hA.choose, rfl, rfl⟩
  rw [IsArc.ends, Sym2.mem_iff] at hx
  obtain rfl | rfl := hx
  · exact ⟨hA.choose 1, P, hf_inj, hf_range⟩
  · exact ⟨hA.choose 0, P.symm, fun _ _ h ↦ symm_inj.mp (hf_inj h), P.symm_range ▸ hf_range⟩

lemma IsArc.exists_path_between (hA : IsArc A) (hxy : hA.ends = s(x, y)) :
    ∃ P : Path x y, Injective P ∧ range P = A := by
  obtain ⟨hf_inj, hf_range⟩ := hA.choose_spec
  let P : Path (hA.choose 0) (hA.choose 1) := ⟨hA.choose, rfl, rfl⟩
  rw [IsArc.ends, Sym2.eq_iff] at hxy
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hxy
  · exact ⟨P, hf_inj, hf_range⟩
  · exact ⟨P.symm, fun _ _ h ↦ symm_inj.mp (hf_inj h), P.symm_range ▸ hf_range⟩
