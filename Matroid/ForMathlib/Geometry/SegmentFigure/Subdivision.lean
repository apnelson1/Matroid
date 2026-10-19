module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Basic

/-!
# Subdivision at finitely many points

Segments can be split at finitely many marked points. The resulting pieces have marked
endpoints and contain no marked point other than their endpoints.
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

private theorem segment_eq_of_common_point_avoiding {c d : V}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hd : d ∈ F)
    (h₁ : segment ℝ a b ∩ F ⊆ {a, b}) (h₂ : segment ℝ c d ∩ F ⊆ {c, d})
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
    · exact Or.inr (hf h)
  have hmin : min u v ∈ f ⁻¹' F := by
    rcases le_total u v with h | h
    · simpa [min_eq_left h] using hc
    · simpa [min_eq_right h] using hd
  have hmax : max u v ∈ f ⁻¹' F := by
    rcases le_total u v with h | h
    · simpa [max_eq_right h] using hd
    · simpa [max_eq_left h] using hc
  have heq := Icc_eq_of_common_point_avoiding
    (show (0 : ℝ) ∈ f ⁻¹' F by simpa [f] using ha)
    (show (1 : ℝ) ∈ f ⁻¹' F by simpa [f] using hb)
    hmin hmax hF₁ hF₂ ht ht₂ hxF
  rw [← habim, heq, hcim]

/-- Every point of a segment lies in a subsegment between consecutive marked points.
Singleton pieces are allowed, so the statement also covers marked points and degenerate segments. -/
theorem exists_subsegment_avoiding_finite (hF : F.Finite) (ha : a ∈ F) (hb : b ∈ F)
    (hx : x ∈ segment ℝ a b) :
    ∃ u ∈ F, ∃ v ∈ F, x ∈ segment ℝ u v ∧ segment ℝ u v ⊆ segment ℝ a b ∧
      segment ℝ u v ∩ F ⊆ {u, v} := by
  by_cases hab : a = b
  · subst b
    simp only [segment_same, mem_singleton_iff] at hx
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
  · rintro y ⟨hy, hyF⟩
    rw [← him] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    obtain h | h := hav ⟨hs, hyF⟩
    · exact Or.inl (congrArg f h)
    · exact Or.inr (congrArg f h)

/-- A finite segment presentation can be refined at any finite set of marked points.
Each original segment remains a union of pieces of the refinement. -/
private theorem exists_segment_refinement_at {E : Set (V × V)} (hE : E.Finite)
    (hF : F.Finite) :
    ∃ B : Set V, B.Finite ∧ F ⊆ B ∧ B ⊆ F ∪ (⋃ e ∈ E, segment ℝ e.1 e.2) ∧
      ∃ D : Set (Set V), D.Finite ∧
        (∀ d ∈ D, ∃ a ∈ B, ∃ b ∈ B,
          d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
        (∀ e ∈ E, segment ℝ e.1 e.2 = ⋃ d ∈ {d ∈ D | d ⊆ segment ℝ e.1 e.2}, d) ∧
        (∀ d ∈ D, ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2) := by
  let B := F ∪ Prod.fst '' E ∪ Prod.snd '' E
  have hB : B.Finite := (hF.union (hE.image _)).union (hE.image _)
  have hEnds (e) (he : e ∈ E) : e.1 ∈ B ∧ e.2 ∈ B :=
    ⟨Or.inl (Or.inr (mem_image_of_mem _ he)), Or.inr (mem_image_of_mem _ he)⟩
  let D := {d ∈ (fun e : V × V ↦ segment ℝ e.1 e.2) '' (B ×ˢ B) |
    (∃ a ∈ B, ∃ b ∈ B, d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
      ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2}
  refine ⟨B, hB, fun x hx ↦ Or.inl (Or.inl hx), ?_, D,
    ((hB.prod hB).image _).subset (sep_subset _ _), fun d hd ↦ hd.2.1, ?_,
    fun d hd ↦ hd.2.2⟩
  · rintro x ((hx | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr (mem_biUnion he (left_mem_segment ℝ _ _))
    · exact Or.inr (mem_biUnion he (right_mem_segment ℝ _ _))
  intro e he
  refine subset_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, ha, b, hb, hx, hsub, hav⟩ :=
      exists_subsegment_avoiding_finite hB (hEnds e he).1 (hEnds e he).2 hx
    exact mem_biUnion ⟨⟨⟨(a, b), ⟨ha, hb⟩, rfl⟩,
      ⟨a, ha, b, hb, rfl, hav⟩, e, he, hsub⟩, hsub⟩ hx
  · intro x hx
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
    exact hd.2 hxd

private theorem exists_intersection_vertices {E : Set (V × V)} (hE : E.Finite) :
    ∃ F : Set V, F.Finite ∧ F ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2 ∧
      ∀ e ∈ E, ∀ f ∈ E, (segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2).Nonempty →
        ∃ p ∈ F, ∃ q ∈ F, segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 = segment ℝ p q := by
  let J := {ef ∈ E ×ˢ E |
    (segment ℝ ef.1.1 ef.1.2 ∩ segment ℝ ef.2.1 ef.2.2).Nonempty}
  have hJ : J.Finite := (hE.prod hE).subset (sep_subset _ _)
  let := hJ.to_subtype
  choose p q hpq using fun ef : J ↦ segment_inter_segment_eq_segment_of_nonempty ef.2.2
  refine ⟨range p ∪ range q, (finite_range _).union (finite_range _), ?_, ?_⟩
  · rintro x (⟨ef, rfl⟩ | ⟨ef, rfl⟩)
    · exact mem_biUnion ef.2.1.1 ((hpq ef ▸ left_mem_segment ℝ (p ef) (q ef)).1)
    · exact mem_biUnion ef.2.1.1 ((hpq ef ▸ right_mem_segment ℝ (p ef) (q ef)).1)
  intro e he f hf hne
  let ef : J := ⟨(e, f), ⟨he, hf⟩, hne⟩
  exact ⟨p ef, Or.inl (mem_range_self _), q ef, Or.inr (mem_range_self _), hpq ef⟩

/-- A finite family of segments has a common subdivision, with prescribed marked points.
Distinct pieces meet only at vertices, and every original segment is a union of pieces. -/
theorem exists_segment_subdivision {E : Set (V × V)} (hE : E.Finite)
    (hF : F.Finite) :
    ∃ B : Set V, B.Finite ∧ F ⊆ B ∧ B ⊆ F ∪ (⋃ e ∈ E, segment ℝ e.1 e.2) ∧
      ∃ D : Set (Set V), D.Finite ∧
        (∀ d ∈ D, ∃ a ∈ B, ∃ b ∈ B,
          d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
        (∀ e ∈ E, segment ℝ e.1 e.2 = ⋃ d ∈ {d ∈ D | d ⊆ segment ℝ e.1 e.2}, d) ∧
        (∀ d ∈ D, ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2) ∧
        D.Pairwise (fun d d' ↦ d ∩ d' ⊆ B) := by
  obtain ⟨A, hA, hAS, hcross⟩ := exists_intersection_vertices hE
  obtain ⟨B, hB, hFAB, hBS, D, hD, hpieces, hcover, hsub⟩ :=
    exists_segment_refinement_at hE (hF.union hA)
  refine ⟨B, hB, subset_union_left.trans hFAB, hBS.trans ?_, D, hD, hpieces,
    hcover, hsub, ?_⟩
  · exact union_subset (union_subset subset_union_left (hAS.trans subset_union_right))
      subset_union_right
  intro d hd d' hd' hne x hx
  by_contra hxB
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hpieces d hd
  obtain ⟨c, hc, d, hdB, rfl, hcd⟩ := hpieces d' hd'
  obtain ⟨e, he, heSub⟩ := hsub _ hd
  obtain ⟨f, hf, hfSub⟩ := hsub _ hd'
  obtain ⟨p, hp, q, hq, hpq⟩ := hcross e he f hf ⟨x, heSub hx.1, hfSub hx.2⟩
  have hpB := hFAB (Or.inr hp)
  have hpqne : p ≠ q := by
    intro heq
    have hx' : x ∈ segment ℝ p q := hpq ▸ ⟨heSub hx.1, hfSub hx.2⟩
    rw [heq, segment_same, mem_singleton_iff] at hx'
    exact hxB (hx' ▸ heq ▸ hpB)
  have hspan (u v : V) : segment ℝ u v ⊆ (affineSpan ℝ {u, v} : Set V) := by
    rw [← convexHull_pair]
    exact convexHull_subset_affineSpan _
  have hpmem : p ∈ segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 :=
    hpq ▸ left_mem_segment ℝ p q
  have hqmem : q ∈ segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 :=
    hpq ▸ right_mem_segment ℝ p q
  have hlines : affineSpan ℝ {e.1, e.2} = affineSpan ℝ {f.1, f.2} :=
    (affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ hpmem.1)
      (hspan _ _ hqmem.1) hpqne).symm.trans
      (affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ hpmem.2)
        (hspan _ _ hqmem.2) hpqne)
  have habne : a ≠ b := by
    rintro rfl
    have hx' : x = a := by simpa using hx.1
    exact hxB (hx' ▸ ha)
  have habline : affineSpan ℝ {a, b} = affineSpan ℝ {e.1, e.2} :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ (heSub (left_mem_segment ℝ a b)))
      (hspan _ _ (heSub (right_mem_segment ℝ a b))) habne
  apply hne
  refine segment_eq_of_common_point_avoiding ha hb hc hdB hab hcd hx.1 hx.2 hxB ?_ ?_
  · rw [habline, hlines]
    exact hspan _ _ (hfSub (left_mem_segment ℝ c d))
  · rw [habline, hlines]
    exact hspan _ _ (hfSub (right_mem_segment ℝ c d))

/-- A finite family of figures admits one subdivision preserving each figure, including any
prescribed finite set of points as vertices. Pieces are sets, so reversing endpoints does not
create a second piece. -/
theorem IsSegmentFigure.exists_common_subdivision {ι : Type*} [Finite ι] {S : ι → Set V}
    (hS : ∀ i, IsSegmentFigure (S i)) (hF : F.Finite) (hFS : F ⊆ ⋃ i, S i) :
    ∃ B : Set V, B.Finite ∧ F ⊆ B ∧ B ⊆ ⋃ i, S i ∧
      ∃ D : Set (Set V), D.Finite ∧ (⋃ i, S i) = ⋃₀ D ∧
        (∀ d ∈ D, ∃ a ∈ B, ∃ b ∈ B, d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
        D.Pairwise (fun d d' ↦ d ∩ d' ⊆ B) ∧
        ∀ i, S i = ⋃ d ∈ {d ∈ D | d ⊆ S i}, d := by
  choose E hE heq using hS
  have hUnion : (⋃ i, S i) = ⋃ e ∈ ⋃ i, E i, segment ℝ e.1 e.2 := by
    simp_rw [heq, biUnion_iUnion]
  obtain ⟨B, hB, hFB, hBS, D, hD, hpieces, hcover, hsub, hpair⟩ :=
    exists_segment_subdivision (finite_iUnion hE) hF
  have hDS : ⋃₀ D ⊆ ⋃ i, S i := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := mem_sUnion.mp hx
    obtain ⟨e, he, hde⟩ := hsub d hd
    rw [hUnion]
    exact mem_biUnion he (hde hxd)
  have hcoverS (i) : S i = ⋃ d ∈ {d ∈ D | d ⊆ S i}, d := by
    refine subset_antisymm ?_ (fun x hx ↦ ?_)
    · intro x hx
      rw [heq i] at hx
      obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      rw [hcover e (mem_iUnion.mpr ⟨i, he⟩)] at hxe
      obtain ⟨d, ⟨hd, hde⟩, hxd⟩ := mem_iUnion₂.mp hxe
      exact mem_biUnion ⟨hd, fun y hy ↦ (heq i) ▸ mem_biUnion he (hde hy)⟩ hxd
    · obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
      exact hd.2 hxd
  refine ⟨B, hB, hFB, ?_, D, hD, subset_antisymm ?_ hDS, hpieces, hpair, hcoverS⟩
  · exact hBS.trans (union_subset hFS (hUnion ▸ subset_rfl))
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rw [hcoverS i] at hi
  obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hi
  exact mem_sUnion.mpr ⟨d, hd.1, hxd⟩

/-- A segment figure admits a finite subdivision at any prescribed finite subset. -/
theorem IsSegmentFigure.exists_subdivision {S : Set V} (hS : IsSegmentFigure S)
    (hF : F.Finite) (hFS : F ⊆ S) :
    ∃ B : Set V, B.Finite ∧ F ⊆ B ∧ B ⊆ S ∧
      ∃ D : Set (Set V), D.Finite ∧ S = ⋃₀ D ∧
        (∀ d ∈ D, ∃ a ∈ B, ∃ b ∈ B, d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
        D.Pairwise (fun d d' ↦ d ∩ d' ⊆ B) := by
  obtain ⟨B, hB, hFB, hBS, D, hD, hUnion, hpieces, hpair, _⟩ :=
    IsSegmentFigure.exists_common_subdivision (S := fun _ : Unit ↦ S) (fun _ ↦ hS) hF
      (by simpa only [iUnion_const] using hFS)
  exact ⟨B, hB, hFB, by simpa only [iUnion_const] using hBS,
    D, hD, by simpa only [iUnion_const] using hUnion, hpieces, hpair⟩

end
