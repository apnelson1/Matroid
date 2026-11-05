module

public import Matroid.ForMathlib.Analysis.Convex.Segment

/-! # Cutting a segment at finitely many marked points

Consecutive marked points cover a segment. Collinear pieces with marked endpoints and
no other marked points coincide whenever they meet away from the marked set.
-/

@[expose] public section

open Set

private theorem Icc_eq_of_common_point_avoiding {F : Set ℝ} {a b c d x : ℝ}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hd : d ∈ F)
    (h₁ : Icc a b ∩ F ⊆ {a, b}) (h₂ : Icc c d ∩ F ⊆ {c, d})
    (hx₁ : x ∈ Icc a b) (hx₂ : x ∈ Icc c d) (hxF : x ∉ F) : Icc a b = Icc c d := by
  have hax : a < x := lt_of_le_of_ne hx₁.1 (fun h ↦ hxF (h ▸ ha))
  have hxb : x < b := lt_of_le_of_ne hx₁.2 (fun h ↦ hxF (h ▸ hb))
  have hcx : c < x := lt_of_le_of_ne hx₂.1 (fun h ↦ hxF (h ▸ hc))
  have hxd : x < d := lt_of_le_of_ne hx₂.2 (fun h ↦ hxF (h ▸ hd))
  have hac : a = c := by
    rcases lt_trichotomy a c with h | h | h
    · obtain h | h : c = a ∨ c = b := h₁ ⟨⟨h.le, hcx.le.trans hx₁.2⟩, hc⟩ <;> linarith
    · exact h
    · obtain h | h : a = c ∨ a = d := h₂ ⟨⟨h.le, hax.le.trans hx₂.2⟩, ha⟩ <;> linarith
  have hbd : b = d := by
    rcases lt_trichotomy b d with h | h | h
    · obtain h | h : b = c ∨ b = d := h₂ ⟨⟨hx₂.1.trans hxb.le, h.le⟩, hb⟩ <;> linarith
    · exact h
    · obtain h | h : d = a ∨ d = b := h₁ ⟨⟨hx₁.1.trans hxd.le, h.le⟩, hd⟩ <;> linarith
  rw [hac, hbd]

private theorem exists_Icc_avoiding_finite {F : Set ℝ} (hF : F.Finite) {a b x : ℝ}
    (ha : a ∈ F) (hb : b ∈ F) (hx : x ∈ Icc a b) :
    ∃ u ∈ F, ∃ v ∈ F, x ∈ Icc u v ∧ Icc u v ⊆ Icc a b ∧ Icc u v ∩ F ⊆ {u, v} := by
  let L := F ∩ Icc a x
  let R := F ∩ Icc x b
  have hL : L.Finite := hF.subset inter_subset_left
  have hR : R.Finite := hF.subset inter_subset_left
  have hnL : L.Nonempty := ⟨a, ha, le_rfl, hx.1⟩
  have hnR : R.Nonempty := ⟨b, hb, hx.2, le_rfl⟩
  obtain ⟨hu, humax⟩ := hnL.isGreatest_csSup hL
  obtain ⟨hv, hvmin⟩ := hnR.isLeast_csInf hR
  refine ⟨sSup L, hu.1, sInf R, hv.1, ⟨hu.2.2, hv.2.1⟩, Icc_subset_Icc hu.2.1 hv.2.2, ?_⟩
  intro y hy
  obtain h | h := le_total y x
  · exact Or.inl (le_antisymm (humax ⟨hy.2, hu.2.1.trans hy.1.1, h⟩) hy.1.1)
  exact Or.inr (le_antisymm hy.1.2 (hvmin ⟨hy.2, h, hy.1.2.trans hv.2.2⟩))

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {F : Set V} {a b x : V}

theorem segment_eq_of_common_point_avoiding {c d : V} (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F)
    (hd : d ∈ F) (h₁ : segment ℝ a b ∩ F ⊆ {a, b}) (h₂ : segment ℝ c d ∩ F ⊆ {c, d})
    (hx₁ : x ∈ segment ℝ a b) (hx₂ : x ∈ segment ℝ c d) (hxF : x ∉ F)
    (hcL : c ∈ affineSpan ℝ {a, b}) (hdL : d ∈ affineSpan ℝ {a, b}) :
    segment ℝ a b = segment ℝ c d := by
  have hab : a ≠ b := by
    rintro rfl
    simp only [segment_same, mem_singleton_iff] at hx₁
    exact hxF (hx₁ ▸ ha)
  let f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  obtain ⟨u, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hcL
  obtain ⟨v, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hdL
  rw [segment_eq_image_lineMap] at hx₁
  obtain ⟨t, ht, rfl⟩ := hx₁
  have habim : f '' Icc 0 1 = segment ℝ a b := (segment_eq_image_lineMap ℝ a b).symm
  have hcim : f '' Icc (min u v) (max u v) = segment ℝ (f u) (f v) := by
    rw [← uIcc, ← segment_eq_uIcc, image_segment]
  have hp : ({min u v, max u v} : Set ℝ) = {u, v} := by
    rcases le_total u v with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, pair_comm]
  have ht₂ : t ∈ Icc (min u v) (max u v) := by
    rw [← hcim] at hx₂
    exact (hf.mem_set_image).mp hx₂
  have hF₁ : Icc 0 1 ∩ f ⁻¹' F ⊆ ({0, 1} : Set ℝ) := by
    rintro r ⟨hr, hrF⟩
    have h := h₁ ⟨habim ▸ mem_image_of_mem f hr, hrF⟩
    have h0 : f 0 = a := by simp [f]
    have h1 : f 1 = b := by simp [f]
    rcases h with h | h
    · exact Or.inl (hf (h.trans h0.symm))
    · exact Or.inr (hf (h.trans h1.symm))
  have hF₂ : Icc (min u v) (max u v) ∩ f ⁻¹' F ⊆ {min u v, max u v} := by
    rintro r ⟨hr, hrF⟩
    have h := h₂ ⟨hcim ▸ mem_image_of_mem f hr, hrF⟩
    rw [hp]
    rcases h with h | h
    · exact Or.inl (hf h)
    exact Or.inr (hf h)
  have hmin : min u v ∈ f ⁻¹' F := by
    rcases le_total u v with h | h
    · simpa [min_eq_left h] using hc
    · simpa [min_eq_right h] using hd
  have hmax : max u v ∈ f ⁻¹' F := by
    rcases le_total u v with h | h
    · simpa [max_eq_right h] using hd
    · simpa [max_eq_left h] using hc
  have heq := Icc_eq_of_common_point_avoiding (show (0 : ℝ) ∈ f ⁻¹' F by simpa [f] using ha)
    (show (1 : ℝ) ∈ f ⁻¹' F by simpa [f] using hb) hmin hmax hF₁ hF₂ ht ht₂ hxF
  rw [← habim, heq, hcim]

/-- Every point of a segment lies in a subsegment between consecutive marked points.
Singleton pieces are allowed, so the statement also covers marked points and degenerate segments. -/
theorem exists_subsegment_avoiding_finite (hF : F.Finite) (ha : a ∈ F) (hb : b ∈ F)
    (hx : x ∈ segment ℝ a b) :
    ∃ u ∈ F, ∃ v ∈ F, x ∈ segment ℝ u v ∧ segment ℝ u v ⊆ segment ℝ a b ∧
      segment ℝ u v ∩ F ⊆ {u, v} := by
  obtain rfl | hab := eq_or_ne a b
  · simp only [segment_same, mem_singleton_iff] at hx
    subst x
    exact ⟨a, ha, a, ha, by simp, subset_rfl, by simp⟩
  let f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨u, hu, v, hv, htuv, huv, hav⟩ := exists_Icc_avoiding_finite
    (hF.preimage hf.injOn) (show (0 : ℝ) ∈ f ⁻¹' F by simpa [f] using ha)
    (show (1 : ℝ) ∈ f ⁻¹' F by simpa [f] using hb) ht
  have huv' : u ≤ v := htuv.1.trans htuv.2
  have him : f '' Icc u v = segment ℝ (f u) (f v) := by
    rw [← segment_eq_Icc huv', image_segment]
  refine ⟨f u, hu, f v, hv, him ▸ mem_image_of_mem f htuv, ?_, ?_⟩
  · rw [← him, segment_eq_image_lineMap]
    exact image_mono huv
  rintro y ⟨hy, hyF⟩
  obtain ⟨s, hs, rfl⟩ := him ▸ hy
  grind [hav ⟨hs, hyF⟩]
