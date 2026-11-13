module

public import Matroid.MiniTauCeti.JCT.Analysis.Convex.Segment

/-! # Refining and partitioning segment families at marked points

Closed marked parameter sets give segment coverage by consecutive marked points.
Inserting the actual pairwise intersection endpoints makes distinct pieces meet only at
vertices. Finite segment families with finitely many relevant marks have finite piece sets.
The prescribed marks remain vertices, including points outside the original segments.
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

private theorem exists_Icc_avoiding_of_isCompact {F : Set ℝ} {a b x : ℝ}
    (hF : IsCompact (F ∩ Icc a b)) (ha : a ∈ F) (hb : b ∈ F) (hx : x ∈ Icc a b) :
    ∃ u ∈ F, ∃ v ∈ F, x ∈ Icc u v ∧ Icc u v ⊆ Icc a b ∧ Icc u v ∩ F ⊆ {u, v} := by
  let L := F ∩ Icc a x
  let R := F ∩ Icc x b
  have hL : IsCompact L := by
    simpa only [L, inter_assoc, Icc_inter_Icc, max_self, min_eq_right hx.2]
      using hF.inter_right (isClosed_Icc (a := a) (b := x))
  have hR : IsCompact R := by
    simpa only [R, inter_assoc, Icc_inter_Icc, min_self, max_eq_right hx.1]
      using hF.inter_right (isClosed_Icc (a := x) (b := b))
  have hnL : L.Nonempty := ⟨a, ha, le_rfl, hx.1⟩
  have hnR : R.Nonempty := ⟨b, hb, hx.2, le_rfl⟩
  obtain ⟨hu, humax⟩ := hL.isGreatest_sSup hnL
  obtain ⟨hv, hvmin⟩ := hR.isLeast_sInf hnR
  refine ⟨sSup L, hu.1, sInf R, hv.1, ⟨hu.2.2, hv.2.1⟩, Icc_subset_Icc hu.2.1 hv.2.2, ?_⟩
  intro y hy
  obtain h | h := le_total y x
  · exact Or.inl (le_antisymm (humax ⟨hy.2, hu.2.1.trans hy.1.1, h⟩) hy.1.1)
  exact Or.inr (le_antisymm hy.1.2 (hvmin ⟨hy.2, h, hy.1.2.trans hv.2.2⟩))

section Segments

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
theorem exists_subsegment_avoiding_of_isClosed
    (hF : IsClosed {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ F})
    (ha : a ∈ F) (hb : b ∈ F)
    (hx : x ∈ segment ℝ a b) :
    ∃ u ∈ F, ∃ v ∈ F, x ∈ segment ℝ u v ∧ segment ℝ u v ⊆ segment ℝ a b ∧
      segment ℝ u v ∩ F = {u, v} := by
  let f : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hcompact : IsCompact (f ⁻¹' F ∩ Icc (0 : ℝ) 1) := by
    have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' F) := hF
    simpa only [inter_comm] using
      isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨u, hu, v, hv, htuv, huv, hav⟩ := exists_Icc_avoiding_of_isCompact
    hcompact (show (0 : ℝ) ∈ f ⁻¹' F by simpa [f] using ha)
    (show (1 : ℝ) ∈ f ⁻¹' F by simpa [f] using hb) ht
  have huv' : u ≤ v := htuv.1.trans htuv.2
  have him : f '' Icc u v = segment ℝ (f u) (f v) := by
    rw [← segment_eq_Icc huv', image_segment]
  refine ⟨f u, hu, f v, hv, him ▸ mem_image_of_mem f htuv, ?_, ?_⟩
  · rw [← him, segment_eq_image_lineMap]
    exact image_mono huv
  · apply subset_antisymm
    · rintro y ⟨hy, hyF⟩
      rw [← him] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      obtain h | h := hav ⟨hs, hyF⟩
      · exact Or.inl (congrArg f h)
      · exact Or.inr (congrArg f h)
    exact pair_subset_iff.mpr
      ⟨⟨left_mem_segment ℝ _ _, hu⟩, ⟨right_mem_segment ℝ _ _, hv⟩⟩

/-- Finite marked sets have closed parameter sets on every segment. -/
theorem isClosed_setOf_lineMap_mem_finite (hF : F.Finite) (a b : V) :
    IsClosed {t : ℝ | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ F} := by
  obtain rfl | hab := eq_or_ne a b
  · by_cases ha : a ∈ F
    · convert (isClosed_Icc (a := (0 : ℝ)) (b := 1)) using 1
      ext t
      simp [ha]
    · simp [ha]
  exact isClosed_Icc.inter (hF.preimage (AffineMap.lineMap_injective ℝ hab).injOn).isClosed

/-- The finite-marked-set specialization of closed-parameter subsegment coverage. -/
theorem exists_subsegment_avoiding_finite (hF : F.Finite) (ha : a ∈ F) (hb : b ∈ F)
    (hx : x ∈ segment ℝ a b) :
    ∃ u ∈ F, ∃ v ∈ F, x ∈ segment ℝ u v ∧ segment ℝ u v ⊆ segment ℝ a b ∧
      segment ℝ u v ∩ F = {u, v} :=
  exists_subsegment_avoiding_of_isClosed (isClosed_setOf_lineMap_mem_finite hF a b) ha hb hx

end Segments

section Cutting

variable {V : Type*} {F : Set V} {x : V}

/-- The prescribed marked points together with all endpoints of a segment family. -/
def segmentRefinementVertices (E : Set (V × V)) (F : Set V) : Set V :=
  F ∪ Prod.fst '' E ∪ Prod.snd '' E

@[simp]
theorem mem_segmentRefinementVertices {E : Set (V × V)} :
    x ∈ segmentRefinementVertices E F ↔
      x ∈ F ∨ (∃ y, (x, y) ∈ E) ∨ ∃ y, (y, x) ∈ E := by
  simp [segmentRefinementVertices, Prod.exists, or_assoc]

theorem subset_segmentRefinementVertices (E : Set (V × V)) (F : Set V) :
    F ⊆ segmentRefinementVertices E F := fun _ hx ↦ Or.inl (Or.inl hx)

theorem fst_mem_segmentRefinementVertices {E : Set (V × V)} {e : V × V}
    (he : e ∈ E) (F : Set V) : e.1 ∈ segmentRefinementVertices E F :=
  Or.inl (Or.inr (mem_image_of_mem _ he))

theorem snd_mem_segmentRefinementVertices {E : Set (V × V)} {e : V × V}
    (he : e ∈ E) (F : Set V) : e.2 ∈ segmentRefinementVertices E F :=
  Or.inr (mem_image_of_mem _ he)

theorem finite_segmentRefinementVertices {E : Set (V × V)} (hE : E.Finite)
    (hF : F.Finite) : (segmentRefinementVertices E F).Finite :=
  (hF.union (hE.image _)).union (hE.image _)

@[simp]
theorem segmentRefinementVertices_empty (F : Set V) :
    segmentRefinementVertices ∅ F = F := by
  simp [segmentRefinementVertices]

@[simp]
theorem segmentRefinementVertices_swap (E : Set (V × V)) (F : Set V) :
    segmentRefinementVertices (Prod.swap '' E) F = segmentRefinementVertices E F := by
  simp [segmentRefinementVertices, image_image,
    union_assoc, union_left_comm, union_comm]

section Pieces

variable [AddCommMonoid V] [SMul ℝ V]

/-- Nondegenerate subsegments of the original family between consecutive refinement vertices. -/
def segmentRefinementPieces (E : Set (V × V)) (F : Set V) : Set (Set V) :=
  {d | (∃ a ∈ segmentRefinementVertices E F, ∃ b ∈ segmentRefinementVertices E F,
    a ≠ b ∧ d = segment ℝ a b ∧ d ∩ segmentRefinementVertices E F ⊆ {a, b}) ∧
      ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2}

theorem mem_segmentRefinementPieces {E : Set (V × V)} {d : Set V} :
    d ∈ segmentRefinementPieces E F ↔
      (∃ a ∈ segmentRefinementVertices E F, ∃ b ∈ segmentRefinementVertices E F,
        a ≠ b ∧ d = segment ℝ a b ∧ d ∩ segmentRefinementVertices E F ⊆ {a, b}) ∧
      ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2 := Iff.rfl

theorem segmentRefinementPieces_eq_segment {E : Set (V × V)} {d : Set V}
    (hd : d ∈ segmentRefinementPieces E F) :
    ∃ a ∈ segmentRefinementVertices E F, ∃ b ∈ segmentRefinementVertices E F,
      a ≠ b ∧ d = segment ℝ a b ∧ d ∩ segmentRefinementVertices E F ⊆ {a, b} := hd.1

theorem segmentRefinementPieces_subset {E : Set (V × V)} {d : Set V}
    (hd : d ∈ segmentRefinementPieces E F) :
    ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2 := hd.2

theorem finite_segmentRefinementPieces {E : Set (V × V)}
    (hB : (segmentRefinementVertices E F).Finite) : (segmentRefinementPieces E F).Finite := by
  refine ((hB.prod hB).image (fun e : V × V ↦ segment ℝ e.1 e.2)).subset ?_
  intro d hd
  obtain ⟨a, ha, b, hb, _, rfl, _⟩ := segmentRefinementPieces_eq_segment hd
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

@[simp]
theorem segmentRefinementPieces_empty (F : Set V) :
    segmentRefinementPieces ∅ F = ∅ := by
  ext d
  simp [mem_segmentRefinementPieces]

@[simp]
theorem segmentRefinementPieces_swap (E : Set (V × V)) (F : Set V) :
    segmentRefinementPieces (Prod.swap '' E) F = segmentRefinementPieces E F := by
  ext d
  simp only [mem_segmentRefinementPieces, segmentRefinementVertices_swap]
  constructor
  · rintro ⟨hparts, e, ⟨f, hf, rfl⟩, hsub⟩
    exact ⟨hparts, f, hf, by simpa only [Prod.fst_swap, Prod.snd_swap, segment_symm] using hsub⟩
  · rintro ⟨hparts, e, he, hsub⟩
    exact ⟨hparts, e.swap, mem_image_of_mem _ he,
      by simpa only [Prod.fst_swap, Prod.snd_swap, segment_symm] using hsub⟩

end Pieces

section Module

variable [AddCommMonoid V] [Module ℝ V]

theorem segmentRefinementVertices_subset (E : Set (V × V)) (F : Set V) :
    segmentRefinementVertices E F ⊆ F ∪ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  rintro x ((hx | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩)
  · exact Or.inl hx
  · exact Or.inr (mem_biUnion he (left_mem_segment ℝ _ _))
  · exact Or.inr (mem_biUnion he (right_mem_segment ℝ _ _))

/-- A refinement piece meets the vertices in exactly its two endpoints. -/
theorem segmentRefinementPieces_inter_vertices {E : Set (V × V)} {d : Set V}
    (hd : d ∈ segmentRefinementPieces E F) :
    ∃ a ∈ segmentRefinementVertices E F, ∃ b ∈ segmentRefinementVertices E F,
      a ≠ b ∧ d = segment ℝ a b ∧ d ∩ segmentRefinementVertices E F = {a, b} := by
  obtain ⟨a, ha, b, hb, hab, rfl, havoid⟩ := segmentRefinementPieces_eq_segment hd
  refine ⟨a, ha, b, hb, hab, rfl, havoid.antisymm ?_⟩
  exact pair_subset_iff.mpr
    ⟨⟨left_mem_segment ℝ a b, ha⟩, ⟨right_mem_segment ℝ a b, hb⟩⟩

/-- Only marked vertices on the original segments need be finite. -/
theorem finite_segmentRefinementPieces_of_finite_inter {E : Set (V × V)}
    (hB : (segmentRefinementVertices E F ∩ ⋃ e ∈ E, segment ℝ e.1 e.2).Finite) :
    (segmentRefinementPieces E F).Finite := by
  refine ((hB.prod hB).image (fun e : V × V ↦ segment ℝ e.1 e.2)).subset ?_
  intro d hd
  obtain ⟨a, ha, b, hb, _, hseg, _⟩ := segmentRefinementPieces_eq_segment hd
  obtain ⟨e, he, hsub⟩ := segmentRefinementPieces_subset hd
  refine ⟨(a, b), ⟨⟨ha, mem_biUnion he (hsub ?_)⟩,
    ⟨hb, mem_biUnion he (hsub ?_)⟩⟩, hseg.symm⟩
  · exact hseg ▸ left_mem_segment ℝ a b
  · exact hseg ▸ right_mem_segment ℝ a b

@[simp]
theorem segmentRefinementPieces_singleton_same (a : V) (F : Set V) :
    segmentRefinementPieces {(a, a)} F = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨u, _, v, _, huv, rfl, _⟩ := segmentRefinementPieces_eq_segment hd
  obtain ⟨e, he, hsub⟩ := segmentRefinementPieces_subset hd
  obtain rfl : e = (a, a) := he
  have hu : u = a := by simpa using hsub (left_mem_segment ℝ u v)
  have hv : v = a := by simpa using hsub (right_mem_segment ℝ u v)
  exact huv (hu.trans hv.symm)

end Module

variable [AddCommGroup V] [Module ℝ V]

/-- Each input segment is covered by its refinement vertices and the pieces it contains. -/
theorem segmentRefinement_cover {E : Set (V × V)} {e : V × V}
    (hB : IsClosed {t : ℝ | t ∈ Icc 0 1 ∧
      AffineMap.lineMap e.1 e.2 t ∈ segmentRefinementVertices E F}) (he : e ∈ E) :
    segment ℝ e.1 e.2 = (segment ℝ e.1 e.2 ∩ segmentRefinementVertices E F) ∪
      ⋃ d ∈ {d ∈ segmentRefinementPieces E F | d ⊆ segment ℝ e.1 e.2}, d := by
  refine subset_antisymm ?_ ?_
  · intro x hx
    by_cases hxB : x ∈ segmentRefinementVertices E F
    · exact Or.inl ⟨hx, hxB⟩
    obtain ⟨a, ha, b, hb, hx, hsub, hav⟩ := exists_subsegment_avoiding_of_isClosed hB
      (fst_mem_segmentRefinementVertices he F) (snd_mem_segmentRefinementVertices he F) hx
    have hab : a ≠ b := by
      rintro rfl
      exact hxB ((by simpa using hx : x = a) ▸ ha)
    exact Or.inr (mem_biUnion ⟨⟨⟨a, ha, b, hb, hab, rfl, hav.subset⟩,
      e, he, hsub⟩, hsub⟩ hx)
  · rintro x (hx | hx)
    · exact hx.1
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
    exact hd.2 hxd

/-- Finite marked vertices on the covered segment suffice for coverage. -/
theorem segmentRefinement_cover_of_finite {E : Set (V × V)} {e : V × V}
    (hB : (segmentRefinementVertices E F ∩ segment ℝ e.1 e.2).Finite) (he : e ∈ E) :
    segment ℝ e.1 e.2 = (segment ℝ e.1 e.2 ∩ segmentRefinementVertices E F) ∪
      ⋃ d ∈ {d ∈ segmentRefinementPieces E F | d ⊆ segment ℝ e.1 e.2}, d := by
  apply segmentRefinement_cover ?_ he
  have hclosed := isClosed_setOf_lineMap_mem_finite hB e.1 e.2
  convert hclosed using 1
  ext t
  simp only [mem_ofPred_eq, mem_inter_iff]
  exact ⟨fun ht ↦ ⟨ht.1, ht.2, lineMap_mem_segment ℝ _ _ ht.1⟩,
    fun ht ↦ ⟨ht.1, ht.2.1⟩⟩

/-- All intersection endpoints of ordered pairs from a segment family. -/
noncomputable def segmentFamilyIntersectionVertices (E : Set (V × V)) : Set V :=
  ⋃ e ∈ E, ⋃ f ∈ E, segmentIntersectionVertices e.1 e.2 f.1 f.2

theorem finite_segmentFamilyIntersectionVertices {E : Set (V × V)} (hE : E.Finite) :
    (segmentFamilyIntersectionVertices E).Finite :=
  hE.biUnion fun _ _ ↦ hE.biUnion fun _ _ ↦ finite_segmentIntersectionVertices ..

theorem segmentFamilyIntersectionVertices_subset (E : Set (V × V)) :
    segmentFamilyIntersectionVertices E ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  intro x hx
  obtain ⟨e, he, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨f, _, hx⟩ := mem_iUnion₂.mp hx
  exact mem_biUnion he ((segmentIntersectionVertices_subset _ _ _ _ hx).1)

private theorem segmentFamilyIntersectionVertices_eq_segment {E : Set (V × V)}
    {e f : V × V} (he : e ∈ E) (hf : f ∈ E)
    (hne : (segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2).Nonempty) :
    ∃ p ∈ segmentFamilyIntersectionVertices E, ∃ q ∈ segmentFamilyIntersectionVertices E,
      segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 = segment ℝ p q := by
  have hverts := segmentIntersectionVertices_eq_pair hne
  refine ⟨_, mem_biUnion he (mem_biUnion hf (hverts.symm ▸ mem_insert _ _)),
    _, mem_biUnion he (mem_biUnion hf (hverts.symm ▸ mem_insert_of_mem _ (mem_singleton _))),
    segment_inter_eq_segment_sInf_sSup hne⟩

/-- The prescribed marks, original endpoints, and all pairwise intersection endpoints. -/
noncomputable def segmentPartitionVertices (E : Set (V × V)) (F : Set V) : Set V :=
  segmentRefinementVertices E (F ∪ segmentFamilyIntersectionVertices E)

/-- Consecutive subsegments after inserting all pairwise intersection endpoints. -/
noncomputable def segmentPartitionPieces (E : Set (V × V)) (F : Set V) : Set (Set V) :=
  segmentRefinementPieces E (F ∪ segmentFamilyIntersectionVertices E)

@[simp]
theorem segmentPartitionVertices_empty (F : Set V) :
    segmentPartitionVertices ∅ F = F := by
  simp [segmentPartitionVertices, segmentFamilyIntersectionVertices]

@[simp]
theorem segmentPartitionPieces_empty (F : Set V) :
    segmentPartitionPieces ∅ F = ∅ := by
  simp [segmentPartitionPieces]

theorem subset_segmentPartitionVertices (E : Set (V × V)) (F : Set V) :
    F ⊆ segmentPartitionVertices E F :=
  subset_union_left.trans (subset_segmentRefinementVertices E _)

theorem segmentPartitionVertices_subset (E : Set (V × V)) (F : Set V) :
    segmentPartitionVertices E F ⊆ F ∪ ⋃ e ∈ E, segment ℝ e.1 e.2 :=
  (segmentRefinementVertices_subset E _).trans
    (union_subset (union_subset subset_union_left
      ((segmentFamilyIntersectionVertices_subset E).trans subset_union_right)) subset_union_right)

theorem finite_segmentPartitionVertices {E : Set (V × V)} (hE : E.Finite)
    (hF : F.Finite) : (segmentPartitionVertices E F).Finite :=
  finite_segmentRefinementVertices hE (hF.union (finite_segmentFamilyIntersectionVertices hE))

theorem segmentPartitionPieces_eq_segment {E : Set (V × V)} {d : Set V}
    (hd : d ∈ segmentPartitionPieces E F) :
    ∃ a ∈ segmentPartitionVertices E F, ∃ b ∈ segmentPartitionVertices E F,
      a ≠ b ∧ d = segment ℝ a b ∧ d ∩ segmentPartitionVertices E F = {a, b} :=
  segmentRefinementPieces_inter_vertices hd

theorem segmentPartitionPieces_subset {E : Set (V × V)} {d : Set V}
    (hd : d ∈ segmentPartitionPieces E F) :
    ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2 := segmentRefinementPieces_subset hd

/-- Finiteness of prescribed marks is needed only on the original segment union. -/
theorem finite_segmentPartitionPieces {E : Set (V × V)} (hE : E.Finite)
    (hF : (F ∩ ⋃ e ∈ E, segment ℝ e.1 e.2).Finite) :
    (segmentPartitionPieces E F).Finite := by
  apply finite_segmentRefinementPieces_of_finite_inter
  have hA := finite_segmentFamilyIntersectionVertices hE
  simpa only [segmentRefinementVertices, union_inter_distrib_right] using
    ((hF.union (hA.inter_of_left _)).union ((hE.image Prod.fst).inter_of_left _)).union
      ((hE.image Prod.snd).inter_of_left _)

/-- Closed marked parameters suffice even for infinite families and marked sets. -/
theorem segmentPartition_cover {E : Set (V × V)} {e : V × V}
    (hB : IsClosed {t : ℝ | t ∈ Icc 0 1 ∧
      AffineMap.lineMap e.1 e.2 t ∈ segmentPartitionVertices E F}) (he : e ∈ E) :
    segment ℝ e.1 e.2 = (segment ℝ e.1 e.2 ∩ segmentPartitionVertices E F) ∪
      ⋃ d ∈ {d ∈ segmentPartitionPieces E F | d ⊆ segment ℝ e.1 e.2}, d :=
  segmentRefinement_cover hB he

/-- Finite marks on this segment suffice for coverage of a finite segment family. -/
theorem segmentPartition_cover_of_finite {E : Set (V × V)} {e : V × V}
    (hE : E.Finite) (hF : (F ∩ segment ℝ e.1 e.2).Finite) (he : e ∈ E) :
    segment ℝ e.1 e.2 = (segment ℝ e.1 e.2 ∩ segmentPartitionVertices E F) ∪
      ⋃ d ∈ {d ∈ segmentPartitionPieces E F | d ⊆ segment ℝ e.1 e.2}, d := by
  apply segmentRefinement_cover_of_finite ?_ he
  have hA := finite_segmentFamilyIntersectionVertices hE
  simpa only [segmentRefinementVertices, union_inter_distrib_right] using
    ((hF.union (hA.inter_of_left _)).union ((hE.image Prod.fst).inter_of_left _)).union
      ((hE.image Prod.snd).inter_of_left _)

/-- Every union of input segments is a union of partition vertices and whole pieces. -/
theorem segmentPartition_cover_biUnion {E E' : Set (V × V)} (hE : E.Finite)
    (hF : F.Finite) (hE' : E' ⊆ E) :
    (⋃ e ∈ E', segment ℝ e.1 e.2) =
      ((⋃ e ∈ E', segment ℝ e.1 e.2) ∩ segmentPartitionVertices E F) ∪
        ⋃ d ∈ {d ∈ segmentPartitionPieces E F | d ⊆ ⋃ e ∈ E', segment ℝ e.1 e.2}, d := by
  refine subset_antisymm ?_ (union_subset inter_subset_left (iUnion₂_subset fun d hd ↦ hd.2))
  intro x hx
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
  obtain hv | hd := (segmentPartition_cover_of_finite hE
    (hF.subset inter_subset_left) (hE' he)).subset hxe
  · exact Or.inl ⟨hx, hv.2⟩
  obtain ⟨d, ⟨hd, hde⟩, hxd⟩ := mem_iUnion₂.mp hd
  exact Or.inr (mem_biUnion ⟨hd, fun y hy ↦ mem_biUnion he (hde hy)⟩ hxd)

/-- The partition covers the input segments together with the prescribed marks. -/
theorem segmentPartition_union {E : Set (V × V)} (hE : E.Finite) (hF : F.Finite) :
    segmentPartitionVertices E F ∪ ⋃₀ segmentPartitionPieces E F =
      F ∪ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  refine subset_antisymm (union_subset (segmentPartitionVertices_subset E F) ?_)
    (union_subset (fun x hx ↦ Or.inl (subset_segmentPartitionVertices E F hx)) ?_)
  · rintro x ⟨d, hd, hxd⟩
    obtain ⟨e, he, hde⟩ := segmentPartitionPieces_subset hd
    exact Or.inr (mem_biUnion he (hde hxd))
  intro x hx
  obtain hv | hd := (segmentPartition_cover_biUnion hE hF (Subset.rfl)).subset hx
  · exact Or.inl hv.2
  obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hd
  exact Or.inr ⟨d, hd.1, hxd⟩

/-- Distinct partition pieces meet only at partition vertices, without finiteness assumptions. -/
theorem segmentPartitionPieces_pairwise (E : Set (V × V)) (F : Set V) :
    (segmentPartitionPieces E F).Pairwise (fun d d' ↦ d ∩ d' ⊆ segmentPartitionVertices E F) := by
  intro d hd d' hd' hne x hx
  by_contra hxB
  obtain ⟨a, ha, b, hb, habne, rfl, hab⟩ := segmentRefinementPieces_eq_segment hd
  obtain ⟨c, hc, d, hdB, _, rfl, hcd⟩ := segmentRefinementPieces_eq_segment hd'
  obtain ⟨e, he, heSub⟩ := segmentPartitionPieces_subset hd
  obtain ⟨f, hf, hfSub⟩ := segmentPartitionPieces_subset hd'
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    segmentFamilyIntersectionVertices_eq_segment he hf ⟨x, heSub hx.1, hfSub hx.2⟩
  have hpB := subset_segmentRefinementVertices E (F ∪ segmentFamilyIntersectionVertices E)
    (Or.inr hp)
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
  have habline : affineSpan ℝ {a, b} = affineSpan ℝ {e.1, e.2} :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ (heSub (left_mem_segment ℝ a b)))
      (hspan _ _ (heSub (right_mem_segment ℝ a b))) habne
  apply hne
  refine segment_eq_of_common_point_avoiding ha hb hc hdB hab hcd hx.1 hx.2 hxB ?_ ?_
  · rw [habline, hlines]
    exact hspan _ _ (hfSub (left_mem_segment ℝ c d))
  · rw [habline, hlines]
    exact hspan _ _ (hfSub (right_mem_segment ℝ c d))

/-- A finite family has a common subdivision preserving prescribed finite marks.
The witnesses are `segmentPartitionVertices` and `segmentPartitionPieces`. -/
theorem exists_segment_partition {E : Set (V × V)} (hE : E.Finite) (hF : F.Finite) :
    ∃ B : Set V, B.Finite ∧ F ⊆ B ∧ B ⊆ F ∪ (⋃ e ∈ E, segment ℝ e.1 e.2) ∧
      ∃ D : Set (Set V), D.Finite ∧
        (∀ d ∈ D, ∃ a ∈ B, ∃ b ∈ B,
          a ≠ b ∧ d = segment ℝ a b ∧ d ∩ B = {a, b}) ∧
        (∀ e ∈ E, segment ℝ e.1 e.2 = (segment ℝ e.1 e.2 ∩ B) ∪
          ⋃ d ∈ {d ∈ D | d ⊆ segment ℝ e.1 e.2}, d) ∧
        (∀ d ∈ D, ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2) ∧
        D.Pairwise (fun d d' ↦ d ∩ d' ⊆ B) := by
  refine ⟨segmentPartitionVertices E F, finite_segmentPartitionVertices hE hF,
    subset_segmentPartitionVertices E F, segmentPartitionVertices_subset E F,
    segmentPartitionPieces E F, finite_segmentPartitionPieces hE (hF.subset inter_subset_left),
    fun _ hd ↦ segmentPartitionPieces_eq_segment hd,
    fun _ he ↦ segmentPartition_cover_of_finite hE (hF.subset inter_subset_left) he,
    fun _ hd ↦ segmentPartitionPieces_subset hd, segmentPartitionPieces_pairwise E F⟩

end Cutting
