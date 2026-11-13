module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.CompactParametrization
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.PrimitivePath
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.Approximation
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink
public import Matroid.MiniTauCeti.JCT.Analysis.Convex.SegmentAvoidance
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Complex.Convex

/-!
# A finite obstruction to a connected circuit complement

Support points of a compact plane circuit determine an exterior cap. A closest pair on an
intermediate vertical section determines a crossbar through the two complementary subarcs.
If the circuit complement were connected, a trimmed polygonal connector between the cap and
crossbar would supply nine primitive links with the incidences of `K₃,₃`.

The proof uses intrinsic-circuit parametrization and elementary geometry. It does not use
the Jordan curve theorem or the nonplanarity of `K₃,₃`.
-/

@[expose] public section

open Set Topology Function
open scoped unitInterval

namespace JordanConfigurations

private theorem exists_support_points {C : Set ℂ} (hC : IsCircuit C)
    (hcompact : IsCompact C) :
    ∃ a ∈ C, ∃ b ∈ C, ∃ H : ℝ, a.re < b.re ∧
      (∀ z ∈ C, a.re ≤ z.re ∧ z.re ≤ b.re ∧ z.im < H) ∧
      (∀ z ∈ C, z.re = a.re → z.im ≤ a.im) ∧
      (∀ z ∈ C, z.re = b.re → z.im ≤ b.im) := by
  have hwidth : ∃ x ∈ C, ∃ y ∈ C, x.re < y.re := by
    by_contra! h
    have : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
    have him : Injective (fun z : C ↦ (z : ℂ).im) := by
      intro x y hxy
      apply Subtype.ext
      exact Complex.ext ((h y y.prop x x.prop).antisymm (h x x.prop y y.prop)) hxy
    apply not_isCircuit_real (Complex.im '' C)
    apply hC.image
    exact ((Complex.continuous_im.comp continuous_subtype_val).isClosedEmbedding him).isEmbedding
  obtain ⟨x, hx, y, hy, hxy⟩ := hwidth
  obtain ⟨a₀, ha₀, hmin⟩ := hcompact.exists_isMinOn hC.nonempty Complex.continuous_re.continuousOn
  obtain ⟨b₀, hb₀, hmax⟩ := hcompact.exists_isMaxOn hC.nonempty Complex.continuous_re.continuousOn
  obtain ⟨a, ⟨ha, har⟩, hatop⟩ :=
    (hcompact.inter_right (isClosed_eq Complex.continuous_re continuous_const)).exists_isMaxOn
      (show (C ∩ {z | z.re = a₀.re}).Nonempty from ⟨a₀, ha₀, rfl⟩)
      Complex.continuous_im.continuousOn
  obtain ⟨b, ⟨hb, hbr⟩, hbtop⟩ :=
    (hcompact.inter_right (isClosed_eq Complex.continuous_re continuous_const)).exists_isMaxOn
      (show (C ∩ {z | z.re = b₀.re}).Nonempty from ⟨b₀, hb₀, rfl⟩)
      Complex.continuous_im.continuousOn
  obtain ⟨z, hz, hheight⟩ := hcompact.exists_isMaxOn hC.nonempty Complex.continuous_im.continuousOn
  refine ⟨a, ha, b, hb, z.im + 1, ?_, ?_, ?_, ?_⟩
  · change a.re = a₀.re at har
    change b.re = b₀.re at hbr
    rw [har, hbr]
    exact (hmin hx).trans_lt (hxy.trans_le (hmax hy))
  · intro w hw
    exact ⟨har.symm ▸ hmin hw, hbr.symm ▸ hmax hw, (hheight hw).trans_lt (by linarith)⟩
  · intro w hw hwr
    exact hatop ⟨hw, hwr.trans har⟩
  · intro w hw hwr
    exact hbtop ⟨hw, hwr.trans hbr⟩

private theorem re_eq_of_mem_segment {u v w : ℂ} {c : ℝ}
    (hu : u.re = c) (hv : v.re = c) (hw : w ∈ segment ℝ u v) : w.re = c := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hw
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, hu, hv]
  rw [← add_mul, hst, one_mul]

private theorem im_eq_of_mem_segment {u v w : ℂ} {c : ℝ}
    (hu : u.im = c) (hv : v.im = c) (hw : w ∈ segment ℝ u v) : w.im = c := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hw
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hu, hv]
  rw [← add_mul, hst, one_mul]

private theorem exists_cap {C : Set ℂ} {a b : ℂ} {H : ℝ}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a.re < b.re)
    (hheight : ∀ z ∈ C, z.im < H)
    (hatop : ∀ z ∈ C, z.re = a.re → z.im ≤ a.im)
    (hbtop : ∀ z ∈ C, z.re = b.re → z.im ≤ b.im) :
    ∃ R : Set ℂ, IsPrimitiveLink R a b ∧ R ∩ C = {a, b} ∧
      ∀ z ∈ R, z.re = a.re ∨ z.re = b.re ∨ z.im = H := by
  let A : ℂ := ⟨a.re, H⟩
  let B : ℂ := ⟨b.re, H⟩
  have haA : a ≠ A := fun h ↦ (hheight a ha).ne (congrArg Complex.im h)
  have hAB : A ≠ B := fun h ↦ hab.ne (show A.re = B.re from congrArg Complex.re h)
  have hBb : B ≠ b := fun h ↦ (hheight b hb).ne (congrArg Complex.im h).symm
  have hseg₁ : segment ℝ a A ∩ segment ℝ A B ⊆ {A} := by
    intro z hz
    exact Complex.ext (re_eq_of_mem_segment (u := a) (v := A) rfl rfl hz.1)
      (im_eq_of_mem_segment (u := A) (v := B) rfl rfl hz.2)
  have hseg₂ : (segment ℝ a A ∪ segment ℝ A B) ∩ segment ℝ B b ⊆ {B} := by
    rintro z ⟨hz | hz, hzB⟩
    · have hzre := re_eq_of_mem_segment (u := a) (v := A) rfl rfl hz
      have hzre' := re_eq_of_mem_segment (u := B) (v := b) rfl rfl hzB
      exact (hab.ne (hzre.symm.trans hzre')).elim
    · exact Complex.ext (re_eq_of_mem_segment (u := B) (v := b) rfl rfl hzB)
        (im_eq_of_mem_segment (u := A) (v := B) rfl rfl hz)
  have haB : a ≠ B := fun h ↦ hab.ne (show a.re = B.re from congrArg Complex.re h)
  let R := (segment ℝ a A ∪ segment ℝ A B) ∪ segment ℝ B b
  have hR : IsPrimitiveLink R a b :=
    ((isPrimitiveLink_segment haA).union (isPrimitiveLink_segment hAB) haA hAB hseg₁).union
      (isPrimitiveLink_segment hBb) haB hBb hseg₂
  refine ⟨R, hR, subset_antisymm ?_ ?_, ?_⟩
  · rintro z ⟨(hz | hz) | hz, hzC⟩
    · have hzr := re_eq_of_mem_segment (u := a) (v := A) rfl rfl hz
      have hzi : a.im ≤ z.im :=
        (convex_halfSpace_im_ge a.im).segment_subset (by simp) (hheight a ha).le hz
      exact Or.inl (Complex.ext hzr (hzi.antisymm (hatop z hzC hzr)).symm)
    · exact ((hheight z hzC).ne (im_eq_of_mem_segment (u := A) (v := B) rfl rfl hz)).elim
    · have hzr := re_eq_of_mem_segment (u := B) (v := b) rfl rfl hz
      have hzi : b.im ≤ z.im :=
        (convex_halfSpace_im_ge b.im).segment_subset (hheight b hb).le (by simp) hz
      exact Or.inr (Complex.ext hzr (hzi.antisymm (hbtop z hzC hzr)).symm)
  · rintro z (rfl | rfl)
    · exact ⟨hR.left_mem, ha⟩
    · exact ⟨hR.right_mem, hb⟩
  rintro z ((hz | hz) | hz)
  · exact Or.inl (re_eq_of_mem_segment (u := a) (v := A) rfl rfl hz)
  · exact Or.inr (Or.inr (im_eq_of_mem_segment (u := A) (v := B) rfl rfl hz))
  · exact Or.inr (Or.inl (re_eq_of_mem_segment (u := B) (v := b) rfl rfl hz))

private theorem exists_crossbar {P Q : Set ℂ} {a b : ℂ}
    (hP : IsPrimitiveLink P a b) (hQ : IsPrimitiveLink Q a b)
    (hPQ : P ∩ Q = {a, b}) (hab : a.re < b.re) :
    ∃ c : ℝ, a.re < c ∧ c < b.re ∧ ∃ u ∈ P, ∃ v ∈ Q,
      u.re = c ∧ v.re = c ∧ u ≠ v ∧
      segment ℝ u v ∩ P = {u} ∧ segment ℝ u v ∩ Q = {v} := by
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  have hPne : (P ∩ {z | z.re = c}).Nonempty := by
    obtain ⟨u, hu, hur⟩ :=
      (hP.isConnected.isPreconnected.image _ Complex.continuous_re.continuousOn).Icc_subset
        (mem_image_of_mem Complex.re hP.left_mem) (mem_image_of_mem Complex.re hP.right_mem)
        ⟨hac.le, hcb.le⟩
    exact ⟨u, hu, hur⟩
  have hQne : (Q ∩ {z | z.re = c}).Nonempty := by
    obtain ⟨v, hv, hvr⟩ :=
      (hQ.isConnected.isPreconnected.image _ Complex.continuous_re.continuousOn).Icc_subset
        (mem_image_of_mem Complex.re hQ.left_mem) (mem_image_of_mem Complex.re hQ.right_mem)
        ⟨hac.le, hcb.le⟩
    exact ⟨v, hv, hvr⟩
  have hdisj : Disjoint (P ∩ {z | z.re = c}) (Q ∩ {z | z.re = c}) := by
    refine disjoint_left.mpr fun w ⟨hwP, hwr⟩ ⟨hwQ, _⟩ ↦ ?_
    have hw := hPQ.subset ⟨hwP, hwQ⟩
    rcases hw with rfl | rfl <;> simp_all
  obtain ⟨u₀, hu₀⟩ := hPne
  obtain ⟨v₀, hv₀⟩ := hQne
  obtain ⟨u, ⟨hu, hur⟩, v, ⟨hv, hvr⟩, -, huP, hvQ⟩ :=
    IsClosed.exists_segment_inter_eq_singleton
      (hP.isClosed.inter (isClosed_eq Complex.continuous_re continuous_const))
      (hQ.isClosed.inter (isClosed_eq Complex.continuous_re continuous_const)) hu₀ hv₀
  refine ⟨c, hac, hcb, u, hu, v, hv, hur, hvr,
    fun h ↦ hdisj.le_bot ⟨h ▸ ⟨hu, hur⟩, hv, hvr⟩, ?_, ?_⟩
  · convert huP using 1
    ext w
    exact ⟨fun hw ↦ ⟨hw.1, hw.2, re_eq_of_mem_segment hur hvr hw.1⟩,
      fun hw ↦ ⟨hw.1, hw.2.1⟩⟩
  · convert hvQ using 1
    ext w
    exact ⟨fun hw ↦ ⟨hw.1, hw.2, re_eq_of_mem_segment hur hvr hw.1⟩,
      fun hw ↦ ⟨hw.1, hw.2.1⟩⟩

private theorem exists_link_between_closed_sets {U S T : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hS : IsClosed S) (hT : IsClosed T)
    (hST : Disjoint S T) (hUS : (U ∩ S).Nonempty) (hUT : (U ∩ T).Nonempty) :
    ∃ a ∈ U ∩ S, ∃ b ∈ U ∩ T, ∃ L : Set ℂ,
      IsPrimitiveLink L a b ∧ L ⊆ U ∧ L ∩ S = {a} ∧ L ∩ T = {b} := by
  obtain ⟨x, hxU, hxS⟩ := hUS
  obtain ⟨y, hyU, hyT⟩ := hUT
  have hxy : x ≠ y := fun h ↦ hST.le_bot ⟨h ▸ hxS, hyT⟩
  obtain ⟨P, hP, hPU⟩ :=
    (hU.isConnected_iff_isPathConnected.mp ⟨⟨x, hxU⟩, hconn⟩).joinedIn x hxU y hyU
      |>.exists_isSimple_polygonalPath_of_open hU
  have hinj : Injective P.toPath :=
    (PolygonalPath.injective_toPath_iff P).mpr ⟨hP, P.length_pos_of_ne hxy⟩
  let s := P.toPath.lastVisit S
  let t := P.toPath.firstVisitAfter T s
  obtain ⟨hst, hs, ht, hsS, htT⟩ := P.toPath.lastVisit_firstVisitAfter_spec
    (hS.preimage P.toPath.continuous) (isClosed_Ici.inter (hT.preimage P.toPath.continuous))
    (hST.preimage P.toPath) hxS hyT
  have hrange : range P.toPath ⊆ U := by simpa [P.toSet_eq_range_toPath] using hPU
  refine ⟨P.toPath s, ⟨hrange (mem_range_self s), hS.frontier_subset hs⟩,
    P.toPath t, ⟨hrange (mem_range_self t), hT.frontier_subset ht⟩,
    range (P.toPath.subpath s t), IsPrimitiveLink.of_injective (Path.injective_subpath hinj hst.ne),
    ?_, ?_, ?_⟩
  · rw [P.toPath.range_subpath]
    exact (image_subset_range _ _).trans hrange
  · rw [P.toPath.range_subpath_of_le _ _ hst.le, ← image_inter_preimage, hsS,
      image_singleton]
  · rw [P.toPath.range_subpath_of_le _ _ hst.le, ← image_inter_preimage, htT,
      image_singleton]

set_option maxHeartbeats 1600000 in
private theorem assemble {P Q R D T : Set ℂ} {a b d u v r : ℂ}
    (hP : IsPrimitiveLink P a b) (hQ : IsPrimitiveLink Q a b)
    (hR : IsPrimitiveLink R a b) (hD : IsPrimitiveLink D u v) (hT : IsPrimitiveLink T d r)
    (hu : u ∈ P) (hv : v ∈ Q) (hd : d ∈ D) (hr : r ∈ R)
    (hinj : Injective (Sum.elim ![a, b, d] ![u, v, r] : Fin 3 ⊕ Fin 3 → ℂ))
    (hPQ : P ∩ Q = {a, b}) (hPR : P ∩ R = {a, b}) (hQR : Q ∩ R = {a, b})
    (hDP : D ∩ P = {u}) (hDQ : D ∩ Q = {v}) (hDR : Disjoint D R)
    (hTP : Disjoint T P) (hTQ : Disjoint T Q) (hTD : T ∩ D = {d}) (hTR : T ∩ R = {r}) :
    ∃ (w : Fin 3 ⊕ Fin 3 → ℂ) (L : Fin 3 × Fin 3 → Set ℂ),
      Injective w ∧
      (∀ e, IsPrimitiveLink (L e) (w (.inl e.1)) (w (.inr e.2))) ∧
      (∀ e, L e ∩ range w ⊆ {w (.inl e.1), w (.inr e.2)}) ∧
      Pairwise (fun e f ↦ L e ∩ L f ⊆ range w) := by
  let w : Fin 3 ⊕ Fin 3 → ℂ := Sum.elim ![a, b, d] ![u, v, r]
  have hab : a ≠ b := hinj.ne (show (Sum.inl 0 : Fin 3 ⊕ Fin 3) ≠ .inl 1 by decide)
  have hau : a ≠ u := hinj.ne (show (Sum.inl 0 : Fin 3 ⊕ Fin 3) ≠ .inr 0 by decide)
  have hav : a ≠ v := hinj.ne (show (Sum.inl 0 : Fin 3 ⊕ Fin 3) ≠ .inr 1 by decide)
  have har : a ≠ r := hinj.ne (show (Sum.inl 0 : Fin 3 ⊕ Fin 3) ≠ .inr 2 by decide)
  have hbu : b ≠ u := hinj.ne (show (Sum.inl 1 : Fin 3 ⊕ Fin 3) ≠ .inr 0 by decide)
  have hbv : b ≠ v := hinj.ne (show (Sum.inl 1 : Fin 3 ⊕ Fin 3) ≠ .inr 1 by decide)
  have hbr : b ≠ r := hinj.ne (show (Sum.inl 1 : Fin 3 ⊕ Fin 3) ≠ .inr 2 by decide)
  have hdu : d ≠ u := hinj.ne (show (Sum.inl 2 : Fin 3 ⊕ Fin 3) ≠ .inr 0 by decide)
  have hdv : d ≠ v := hinj.ne (show (Sum.inl 2 : Fin 3 ⊕ Fin 3) ≠ .inr 1 by decide)
  have huv : u ≠ v := hinj.ne (show (Sum.inr 0 : Fin 3 ⊕ Fin 3) ≠ .inr 1 by decide)
  let L : Fin 3 × Fin 3 → Set ℂ := fun e ↦
    ![![hP.splitLeft u, hQ.splitLeft v, hR.splitLeft r],
      ![hP.splitRight u, hQ.splitRight v, hR.splitRight r],
      ![hD.splitLeft d, hD.splitRight d, T]] e.1 e.2
  have hPP : hP.splitLeft u ∩ hP.splitRight u = {u} := by
    simpa [hab] using hP.splitLeft_inter_splitRight hu
  have hQQ : hQ.splitLeft v ∩ hQ.splitRight v = {v} := by
    simpa [hab] using hQ.splitLeft_inter_splitRight hv
  have hRR : hR.splitLeft r ∩ hR.splitRight r = {r} := by
    simpa [hab] using hR.splitLeft_inter_splitRight hr
  have hDD : hD.splitLeft d ∩ hD.splitRight d = {d} := by
    simpa [huv] using hD.splitLeft_inter_splitRight hd
  have hPL := hP.splitLeft_subset u
  have hPR' := hP.splitRight_subset u
  have hQL := hQ.splitLeft_subset v
  have hQR' := hQ.splitRight_subset v
  have hRL := hR.splitLeft_subset r
  have hRR' := hR.splitRight_subset r
  have hDL := hD.splitLeft_subset d
  have hDR' := hD.splitRight_subset d
  have haPL := hP.left_mem_splitLeft u
  have hbPR := hP.right_mem_splitRight u
  have huPL := hP.mem_splitLeft hu
  have huPR := hP.mem_splitRight hu
  have haQL := hQ.left_mem_splitLeft v
  have hbQR := hQ.right_mem_splitRight v
  have hvQL := hQ.mem_splitLeft hv
  have hvQR := hQ.mem_splitRight hv
  have haRL := hR.left_mem_splitLeft r
  have hbRR := hR.right_mem_splitRight r
  have hrRL := hR.mem_splitLeft hr
  have hrRR := hR.mem_splitRight hr
  have huDL := hD.left_mem_splitLeft d
  have hvDR := hD.right_mem_splitRight d
  have hdDL := hD.mem_splitLeft hd
  have hdDR := hD.mem_splitRight hd
  have hdT := hT.left_mem
  have hrT := hT.right_mem
  have hw : range w = {a, b, d, u, v, r} := by
    ext z
    simp [w, or_comm, or_left_comm]
  refine ⟨w, L, hinj, ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> dsimp [L, w]
    · exact hP.isPrimitiveLink_splitLeft hu hau.symm
    · exact hQ.isPrimitiveLink_splitLeft hv hav.symm
    · exact hR.isPrimitiveLink_splitLeft hr har.symm
    · exact (hP.isPrimitiveLink_splitRight hu hbu.symm).symm
    · exact (hQ.isPrimitiveLink_splitRight hv hbv.symm).symm
    · exact (hR.isPrimitiveLink_splitRight hr hbr.symm).symm
    · exact (hD.isPrimitiveLink_splitLeft hd hdu).symm
    · exact hD.isPrimitiveLink_splitRight hd hdv
    · exact hT
  · rintro ⟨i, j⟩ z hz
    rw [hw] at hz
    clear hw hinj
    apply_fun (z ∈ ·) at hPQ hPR hQR hDP hDQ hTD hTR hPP hQQ hRR hDD
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      at hPQ hPR hQR hDP hDQ hTD hTR hPP hQQ hRR hDD hz ⊢
    fin_cases i <;> fin_cases j <;> simp only [L, w, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Sum.elim_inl, Sum.elim_inr] at hz ⊢
    all_goals grind -ring -linarith only [disjoint_left, subset_def]
  rintro ⟨i, j⟩ ⟨k, l⟩ hne z hz
  rw [hw]
  by_contra hzout
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzout
  obtain ⟨hza, hzb, hzd, hzu, hzv, hzr⟩ := hzout
  clear hw hinj
  apply_fun (z ∈ ·) at hPQ hPR hQR hDP hDQ hTD hTR hPP hQQ hRR hDD
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff,
    hza, hzb, hzd, hzu, hzv, hzr, or_self, eq_iff_iff, iff_false] at hPQ hPR hQR hDP hDQ hTD hTR hPP hQQ hRR hDD
  have hPL := @hPL z
  have hPR' := @hPR' z
  have hQL := @hQL z
  have hQR' := @hQR' z
  have hRL := @hRL z
  have hRR' := @hRR' z
  have hDL := @hDL z
  have hDR' := @hDR' z
  have hDR : ¬ (z ∈ D ∧ z ∈ R) := fun h ↦ hDR.le_bot h
  have hTP : ¬ (z ∈ T ∧ z ∈ P) := fun h ↦ hTP.le_bot h
  have hTQ : ¬ (z ∈ T ∧ z ∈ Q) := fun h ↦ hTQ.le_bot h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals try exact (hne rfl).elim
  all_goals simp only [L, Matrix.cons_val_zero', Matrix.cons_val_succ', mem_inter_iff] at hz
  all_goals
    clear * - hz hPQ hPR hQR hDP hDQ hTD hTR hPP hQQ hRR hDD hPL hPR' hQL hQR' hRL hRR' hDL hDR' hDR hTP hTQ
    grind -ring -linarith only

/-- A connected complement of a compact intrinsic plane circuit would provide the nine links
of a subdivision of the complete bipartite graph on two sets of three vertices. -/
theorem of_connected_complement {C : Set ℂ}
    (hC : IsCircuit C) (hcompact : IsCompact C) (hconn : IsPreconnected Cᶜ) :
    ∃ (w : Fin 3 ⊕ Fin 3 → ℂ) (L : Fin 3 × Fin 3 → Set ℂ),
      Injective w ∧
      (∀ e, IsPrimitiveLink (L e) (w (.inl e.1)) (w (.inr e.2))) ∧
      (∀ e, L e ∩ range w ⊆ {w (.inl e.1), w (.inr e.2)}) ∧
      Pairwise (fun e f ↦ L e ∩ L f ⊆ range w) := by
  obtain ⟨a, ha, b, hb, H, hab, hbox, hatop, hbtop⟩ := exists_support_points hC hcompact
  have hab' : a ≠ b := fun h ↦ hab.ne (congrArg Complex.re h)
  obtain ⟨P, Q, hP, hQ, hcover, hPQ⟩ := hC.exists_two_arcs hcompact ha hb hab'
  have hPC : P ⊆ C := subset_union_left.trans hcover.subset
  have hQC : Q ⊆ C := subset_union_right.trans hcover.subset
  obtain ⟨c, hac, hcb, u, hu, v, hv, hur, hvr, huv, hDP, hDQ⟩ :=
    exists_crossbar hP hQ hPQ hab
  let D := segment ℝ u v
  have hD : IsPrimitiveLink D u v := isPrimitiveLink_segment huv
  have huC := hPC hu
  have hvC := hQC hv
  obtain ⟨R, hR, hRC, hcap⟩ := exists_cap ha hb hab (fun z hz ↦ (hbox z hz).2.2) hatop hbtop
  have hDC : D ∩ C = {u, v} := by
    rw [← hcover, inter_union_distrib_left, hDP, hDQ]
    simp [pair_comm]
  have hDR : Disjoint D R := by
    refine disjoint_left.mpr fun z hzD hzR ↦ ?_
    have hzr := re_eq_of_mem_segment hur hvr hzD
    have hzi : z.im < H := (convex_halfSpace_im_lt H).segment_subset
      (hbox u huC).2.2 (hbox v hvC).2.2 hzD
    rcases hcap z hzR with hza | hzb | hzH
    · exact hac.ne (hza.symm.trans hzr)
    · exact hcb.ne (hzr.symm.trans hzb)
    · exact hzi.ne hzH
  have hUD : (Cᶜ ∩ D).Nonempty := by
    obtain ⟨z, hzD, hz⟩ := hD.diff_endpoints_nonempty
    exact ⟨z, fun hzC ↦ hz (hDC.subset ⟨hzD, hzC⟩), hzD⟩
  have hUR : (Cᶜ ∩ R).Nonempty := by
    obtain ⟨z, hzR, hz⟩ := hR.diff_endpoints_nonempty
    exact ⟨z, fun hzC ↦ hz (hRC.subset ⟨hzR, hzC⟩), hzR⟩
  obtain ⟨d, ⟨hdC, hdD⟩, r, ⟨hrC, hrR⟩, T, hT, hTC, hTD, hTR⟩ :=
    exists_link_between_closed_sets hcompact.isClosed.isOpen_compl hconn hD.isClosed hR.isClosed
      hDR hUD hUR
  have hau : a ≠ u := fun h ↦ hac.ne ((congrArg Complex.re h).trans hur)
  have hav : a ≠ v := fun h ↦ hac.ne ((congrArg Complex.re h).trans hvr)
  have hbu : b ≠ u := fun h ↦ hcb.ne (hur.symm.trans (congrArg Complex.re h).symm)
  have hbv : b ≠ v := fun h ↦ hcb.ne (hvr.symm.trans (congrArg Complex.re h).symm)
  have hda : d ≠ a := fun h ↦ hdC (h ▸ ha)
  have hdb : d ≠ b := fun h ↦ hdC (h ▸ hb)
  have hdu : d ≠ u := fun h ↦ hdC (h ▸ huC)
  have hdv : d ≠ v := fun h ↦ hdC (h ▸ hvC)
  have hra : r ≠ a := fun h ↦ hrC (h ▸ ha)
  have hrb : r ≠ b := fun h ↦ hrC (h ▸ hb)
  have hru : r ≠ u := fun h ↦ hrC (h ▸ huC)
  have hrv : r ≠ v := fun h ↦ hrC (h ▸ hvC)
  have hdr : d ≠ r := fun h ↦ hDR.le_bot ⟨h ▸ hdD, hrR⟩
  have hinj : Injective (Sum.elim ![a, b, d] ![u, v, r] : Fin 3 ⊕ Fin 3 → ℂ) := by
    intro x y h
    rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j
    all_goals dsimp at h; simp_all only [not_false_eq_true, ne_eq, not_true_eq_false, implies_true]
  have hPR : P ∩ R = {a, b} := subset_antisymm
    (fun z hz ↦ hRC.subset ⟨hz.2, hPC hz.1⟩) (by
      rintro z (rfl | rfl)
      · exact ⟨hP.left_mem, hR.left_mem⟩
      · exact ⟨hP.right_mem, hR.right_mem⟩)
  have hQR : Q ∩ R = {a, b} := subset_antisymm
    (fun z hz ↦ hRC.subset ⟨hz.2, hQC hz.1⟩) (by
      rintro z (rfl | rfl)
      · exact ⟨hQ.left_mem, hR.left_mem⟩
      · exact ⟨hQ.right_mem, hR.right_mem⟩)
  exact assemble hP hQ hR hD hT hu hv hdD hrR hinj hPQ hPR hQR hDP hDQ hDR
    (disjoint_left.mpr fun z hzT hzP ↦ hTC hzT (hPC hzP))
    (disjoint_left.mpr fun z hzT hzQ ↦ hTC hzT (hQC hzQ)) hTD hTR

end JordanConfigurations
