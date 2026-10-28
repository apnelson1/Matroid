module

public import Matroid.GraphLike.StraightLine
public import Matroid.GraphLike.Assembly
public import Matroid.ForMathlib.Analysis.Convex.SegmentCutting

/-! # Finite straight-line presentations

Cut a finite segment family at its intersection endpoints and prescribed points, then assemble
its nondegenerate pieces into geometric edges. Marked points supply the vertices directly.
-/

@[expose] public section

open Set Function Set.Notation
open scoped GraphLike

section Cutting

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {F : Set V}

/-- A finite segment presentation can be refined at any finite set of marked points.
Each original segment is covered by marked points and nondegenerate pieces. -/
private theorem exists_segment_refinement_at {E : Set (V × V)} (hE : E.Finite)
    (hF : F.Finite) :
    ∃ B : Set V, B.Finite ∧ F ⊆ B ∧ B ⊆ F ∪ (⋃ e ∈ E, segment ℝ e.1 e.2) ∧
      ∃ D : Set (Set V), D.Finite ∧
        (∀ d ∈ D, ∃ a ∈ B, ∃ b ∈ B,
          a ≠ b ∧ d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
        (∀ e ∈ E, segment ℝ e.1 e.2 = (segment ℝ e.1 e.2 ∩ B) ∪
          ⋃ d ∈ {d ∈ D | d ⊆ segment ℝ e.1 e.2}, d) ∧
        (∀ d ∈ D, ∃ e ∈ E, d ⊆ segment ℝ e.1 e.2) := by
  let B := F ∪ Prod.fst '' E ∪ Prod.snd '' E
  have hB : B.Finite := (hF.union (hE.image _)).union (hE.image _)
  have hEnds (e) (he : e ∈ E) : e.1 ∈ B ∧ e.2 ∈ B :=
    ⟨Or.inl (Or.inr (mem_image_of_mem _ he)), Or.inr (mem_image_of_mem _ he)⟩
  let D := {d ∈ (fun e : V × V ↦ segment ℝ e.1 e.2) '' (B ×ˢ B) |
    (∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
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
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx, hxB⟩
    obtain ⟨a, ha, b, hb, hx, hsub, hav⟩ :=
      exists_subsegment_avoiding_finite hB (hEnds e he).1 (hEnds e he).2 hx
    have hab : a ≠ b := by
      rintro rfl
      exact hxB ((by simpa using hx : x = a) ▸ ha)
    exact Or.inr (mem_biUnion ⟨⟨⟨(a, b), ⟨ha, hb⟩, rfl⟩,
      ⟨a, ha, b, hb, hab, rfl, hav⟩, e, he, hsub⟩, hsub⟩ hx)
  · rintro x (hx | hx)
    · exact hx.1
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
Pieces are nondegenerate and meet only at marked points. Each original segment is covered
by its marked points and the pieces it contains. This algebraic construction also supports
the legacy subdivision interface. -/
theorem exists_segment_partition {E : Set (V × V)} (hE : E.Finite)
    (hF : F.Finite) :
    ∃ B : Set V, B.Finite ∧ F ⊆ B ∧ B ⊆ F ∪ (⋃ e ∈ E, segment ℝ e.1 e.2) ∧
      ∃ D : Set (Set V), D.Finite ∧
        (∀ d ∈ D, ∃ a ∈ B, ∃ b ∈ B,
          a ≠ b ∧ d = segment ℝ a b ∧ d ∩ B ⊆ {a, b}) ∧
        (∀ e ∈ E, segment ℝ e.1 e.2 = (segment ℝ e.1 e.2 ∩ B) ∪
          ⋃ d ∈ {d ∈ D | d ⊆ segment ℝ e.1 e.2}, d) ∧
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
  obtain ⟨a, ha, b, hb, habne, rfl, hab⟩ := hpieces d hd
  obtain ⟨c, hc, d, hdB, _, rfl, hcd⟩ := hpieces d' hd'
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
  have habline : affineSpan ℝ {a, b} = affineSpan ℝ {e.1, e.2} :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan _ _ (heSub (left_mem_segment ℝ a b)))
      (hspan _ _ (heSub (right_mem_segment ℝ a b))) habne
  apply hne
  refine segment_eq_of_common_point_avoiding ha hb hc hdB hab hcd hx.1 hx.2 hxB ?_ ?_
  · rw [habline, hlines]
    exact hspan _ _ (hfSub (left_mem_segment ℝ c d))
  · rw [habline, hlines]
    exact hspan _ _ (hfSub (right_mem_segment ℝ c d))

end Cutting

section Assembly

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [ContinuousAdd X] [ContinuousSMul ℝ X]

/-- Assemble a finite set of nondegenerate segments meeting only at a finite vertex set.
The edge correspondence preserves the supplied sets, without choosing public orientations. -/
theorem GraphLike.exists_of_finite_segments (Z : Set X) (hZ : Z.Finite)
    (D : Set (Set X)) (hD : D.Finite) [T2Space ↥(Z ∪ ⋃₀ D)]
    (hpieces : ∀ d ∈ D, ∃ a ∈ Z, ∃ b ∈ Z,
      a ≠ b ∧ d = segment ℝ a b ∧ d ∩ Z ⊆ {a, b})
    (hpair : D.Pairwise fun d d' ↦ d ∩ d' ⊆ Z) :
    ∃ (G : GraphLike X) (e : D ≃ ↥E(G)), G.Finite ∧ G.IsStraightLine ∧
      G.carrier = Z ∪ ⋃₀ D ∧ G.vertexSet = Z ∧ ∀ d, (e d).1 = d.1 := by
  classical
  let := hD.to_subtype
  have hp (d : D) : ∃ a b : Z,
      a.1 ≠ b.1 ∧ d.1 = segment ℝ a.1 b.1 ∧ d.1 ∩ Z ⊆ {a.1, b.1} := by
    obtain ⟨a, ha, b, hb, hab, hd, hv⟩ := hpieces d.1 d.2
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, hd, hv⟩
  choose a b hab hd hv using hp
  have hlink (d : D) : IsPrimitiveLink d.1 (a d).1 (b d).1 :=
    hd d ▸ isPrimitiveLink_segment (hab d)
  have hvertices (d : D) : d.1 ∩ Z = {(a d).1, (b d).1} :=
    (hv d).antisymm (pair_subset_iff.mpr
      ⟨⟨(hlink d).left_mem, (a d).2⟩, ⟨(hlink d).right_mem, (b d).2⟩⟩)
  have hdisj : Pairwise fun i j : D ↦ Disjoint (i.1 \ Z) (j.1 \ Z) := by
    intro i j hij
    exact disjoint_left.mpr fun x hx hy ↦
      hx.2 (hpair i.2 j.2 (fun h ↦ hij (Subtype.ext h)) ⟨hx.1, hy.1⟩)
  have hU : (⋃ d : D, d.1) = ⋃₀ D := by ext x; simp
  let : T2Space ↥(Z ∪ ⋃ d : D, d.1) := hU.symm ▸ inferInstance
  let G := GraphLike.ofFiniteLinks Z hZ a b (fun d : D ↦ d.1) hlink hvertices hdisj
  let e := GraphLike.ofFiniteLinksEdgeEquiv Z hZ a b (fun d : D ↦ d.1) hlink hvertices hdisj
  have hrange (d : D) : (e d).1 = d.1 := GraphLike.ofFiniteLinksEdgeEquiv_coe ..
  have hboundary (d : D) : G.edgeBoundary d.1 = {(a d).1, (b d).1} :=
    GraphLike.ofFiniteLinks_edgeBoundary ..
  refine ⟨G, e, GraphLike.ofFiniteLinks_finite Z hZ a b (fun d : D ↦ d.1)
    hlink hvertices hdisj, ?_, congrArg (Z ∪ ·) hU, rfl, hrange⟩
  intro f hf x y hb
  have hmem : f ∈ range (fun d : D ↦ d.1) := by
    simpa only [G, GraphLike.ofFiniteLinks_edgeSet] using hf
  obtain ⟨d, rfl⟩ := hmem
  change d.1 = segment ℝ x y
  rw [hd d]
  rcases pair_eq_pair_iff.mp ((hboundary d).symm.trans hb) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hx, hy]
  · rw [hx, hy, segment_symm]

variable {S F : Set X}

/-- A finite family of figures has a common straight-line presentation preserving each figure
as vertices and whole edges, including any prescribed finite set of vertices. -/
theorem IsSegmentFigure.exists_common_straightLineGraphLike
    {ι : Type*} [Finite ι] {S : ι → Set X} [T2Space ↥(⋃ i, S i)]
    (hS : ∀ i, IsSegmentFigure (S i))
    (hF : F.Finite) (hFS : F ⊆ ⋃ i, S i) :
    ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = ⋃ i, S i ∧
      F ⊆ G.vertexSet ∧
      ∀ i, S i = (S i ∩ G.vertexSet) ∪ ⋃ e ∈ {e ∈ E(G) | e ⊆ S i}, e := by
  classical
  choose E hE heq using hS
  have hUnion : (⋃ i, S i) = ⋃ e ∈ ⋃ i, E i, segment ℝ e.1 e.2 := by
    simp_rw [heq, biUnion_iUnion]
  obtain ⟨B, hB, hFB, hBS, D, hD, hpieces, hcover, hsub, hpair⟩ :=
    exists_segment_partition (finite_iUnion hE) hF
  have hBsub : B ⊆ ⋃ i, S i := hBS.trans (union_subset hFS (hUnion ▸ subset_rfl))
  have hcoverS (i) : S i = (S i ∩ B) ∪ ⋃ d ∈ {d ∈ D | d ⊆ S i}, d := by
    refine subset_antisymm ?_ (union_subset inter_subset_left ?_)
    · intro x hx
      obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp ((heq i).subset hx)
      obtain hxB | hxD := (hcover e (mem_iUnion.mpr ⟨i, he⟩)).subset hxe
      · exact Or.inl ⟨hx, hxB.2⟩
      obtain ⟨d, ⟨hd, hde⟩, hxd⟩ := mem_iUnion₂.mp hxD
      exact Or.inr (mem_biUnion ⟨hd, fun y hy ↦
        (heq i).superset (mem_biUnion he (hde hy))⟩ hxd)
    · exact iUnion₂_subset fun d hd ↦ hd.2
  have hcarrier : B ∪ ⋃₀ D = ⋃ i, S i := by
    refine subset_antisymm (union_subset hBsub ?_) ?_
    · rintro x ⟨d, hd, hx⟩
      obtain ⟨e, he, hde⟩ := hsub d hd
      exact hUnion ▸ mem_biUnion he (hde hx)
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain hv | he := (hcoverS i).subset hi
    · exact Or.inl hv.2
    obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp he
    exact Or.inr ⟨d, hd.1, hxd⟩
  let : T2Space ↥(B ∪ ⋃₀ D) := hcarrier.symm ▸ inferInstance
  obtain ⟨G, e, hfin, hstraight, hG, hV, he⟩ :=
    GraphLike.exists_of_finite_segments B hB D hD hpieces hpair
  refine ⟨G, hfin, hstraight, hG.trans hcarrier, hV ▸ hFB, fun i ↦ ?_⟩
  rw [hV]
  refine (hcoverS i).trans (congrArg ((S i ∩ B) ∪ ·) ?_)
  have hE : E(G) = D := by
    ext d
    constructor
    · intro hd
      obtain ⟨c, hc⟩ := e.surjective ⟨d, hd⟩
      have hval := congrArg Subtype.val hc
      rw [he] at hval
      change c.1 = d at hval
      exact hval ▸ c.2
    · intro hd
      have hval : (e ⟨d, hd⟩).1 = d := he ⟨d, hd⟩
      exact hval ▸ (e ⟨d, hd⟩).2
  rw [hE]

/-- A segment figure has a finite straight-line presentation containing prescribed vertices. -/
theorem IsSegmentFigure.exists_straightLineGraphLike [T2Space S] (hS : IsSegmentFigure S)
    (hF : F.Finite) (hFS : F ⊆ S) :
    ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = S ∧
      F ⊆ G.vertexSet := by
  let : T2Space ↥(⋃ _ : Unit, S) := by
    have hUnion : (⋃ _ : Unit, S) = S := iUnion_const S
    exact hUnion.symm ▸ inferInstance
  obtain ⟨G, hfin, hstraight, hcarrier, hvertices, _⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike (S := fun _ : Unit ↦ S)
      (fun _ ↦ hS) hF (by simpa only [iUnion_const] using hFS)
  exact ⟨G, hfin, hstraight, by simpa only [iUnion_const] using hcarrier, hvertices⟩

/-- Segment figures are precisely the carriers of finite straight-line graph-like spaces. -/
theorem isSegmentFigure_iff_exists_straightLineGraphLike [T2Space S] :
    IsSegmentFigure S ↔
      ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ G.carrier = S := by
  constructor
  · intro hS
    obtain ⟨G, hfin, hstraight, hcarrier, _⟩ :=
      hS.exists_straightLineGraphLike finite_empty (empty_subset S)
    exact ⟨G, hfin, hstraight, hcarrier⟩
  rintro ⟨G, hfin, hstraight, rfl⟩
  let := hfin
  exact hstraight.isSegmentFigure_carrier

end Assembly

