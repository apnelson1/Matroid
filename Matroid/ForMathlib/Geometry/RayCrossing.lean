module

public import Matroid.ForMathlib.Analysis.InnerProductSpace.TwoDim
public import Matroid.ForMathlib.Geometry.AffineCrossing
public import Matroid.ForMathlib.Analysis.LocallyConvex.Bounded

/-! # Crossings of oriented rays

Ray crossings count points where a set approaches both strict sides of the supporting line.
The ray includes its origin. Its crossing set is independent of the choice of orientation.
-/

@[expose] public section

noncomputable section

open Set Module Function Metric

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 2)]

/-- Crossings of the supporting line restricted to the forward ray, including its origin. -/
def rayCrossings (o : Orientation ℝ E (Fin 2)) (S : Set E) (z v : E) : Set E :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ p = z + t • v} ∩
    boundaryCrossings S {q | o.areaForm v z < o.areaForm v q}

variable (o : Orientation ℝ E (Fin 2))

@[simp] theorem rayCrossings_zero (S : Set E) (z : E) :
    rayCrossings o S z 0 = ∅ := by
  simp [rayCrossings, boundaryCrossings]

theorem mem_boundaryCrossings_halfPlane_iff {S : Set E} {v p : E} :
    p ∈ boundaryCrossings S {q | o.areaForm v p < o.areaForm v q} ↔
      p ∈ S ∧ p ∈ closure {q | q ∈ S ∧ o.areaForm v p < o.areaForm v q} ∧
        p ∈ closure {q | q ∈ S ∧ o.areaForm v q < o.areaForm v p} := by
  by_cases hv : v = 0
  · subst v
    simp [boundaryCrossings]
  let f := o.areaForm v
  have hf := LinearMap.continuous_of_finiteDimensional f
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨(c / ‖v‖ ^ 2) • o.rightAngleRotation v, ?_⟩
    change o.areaForm v ((c / ‖v‖ ^ 2) • o.rightAngleRotation v) = c
    rw [map_smul, Orientation.areaForm_rightAngleRotation_right,
      real_inner_self_eq_norm_sq, smul_eq_mul,
      div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hv))]
  have hopen : IsOpenMap f := LinearMap.isOpenMap_of_finiteDimensional f hsurj
  exact hopen.mem_boundaryCrossings_preimage_Ioi_iff hf

theorem mem_rayCrossings_iff {S : Set E} {z v p : E} :
    p ∈ rayCrossings o S z v ↔
      (∃ t : ℝ, 0 ≤ t ∧ p = z + t • v) ∧
        p ∈ boundaryCrossings S {q | o.areaForm v p < o.areaForm v q} := by
  apply and_congr_right
  rintro ⟨t, ht, rfl⟩
  simp only [map_add, map_smul, Orientation.areaForm_apply_self,
    smul_zero, add_zero]

/-- Orientation reversal exchanges the two strict sides, preserving the crossing set. -/
@[simp] theorem rayCrossings_neg_orientation (S : Set E) (z v : E) :
    rayCrossings (-o) S z v = rayCrossings o S z v := by
  ext p
  rw [mem_rayCrossings_iff, mem_rayCrossings_iff,
    mem_boundaryCrossings_halfPlane_iff, mem_boundaryCrossings_halfPlane_iff]
  simp only [Orientation.areaForm_neg_orientation, LinearMap.neg_apply,
    neg_lt_neg_iff]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_comm

theorem rayCrossings_orientation_eq (o' : Orientation ℝ E (Fin 2))
    (S : Set E) (z v : E) : rayCrossings o S z v = rayCrossings o' S z v := by
  obtain h | h := Orientation.eq_or_eq_neg o o' (by simpa using (Fact.out : finrank ℝ E = 2).symm)
  · rw [h]
  · rw [h, rayCrossings_neg_orientation]

/-- The initial point is counted exactly when it is a crossing of the supporting line. -/
theorem origin_mem_rayCrossings_iff (S : Set E) (z v : E) :
    z ∈ o.rayCrossings S z v ↔ z ∈ boundaryCrossings S
      {q | o.areaForm v z < o.areaForm v q} := by
  exact and_iff_right ⟨0, le_rfl, by simp⟩

/-- A set contained in the closed lower half-plane has no crossings of the ray. -/
theorem rayCrossings_eq_empty_of_one_side {S : Set E} {z v : E}
    (hside : S ⊆ {q | o.areaForm v q ≤ o.areaForm v z}) :
    o.rayCrossings S z v = ∅ := by
  have hempty : S ∩ {q | o.areaForm v z < o.areaForm v q} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact (show o.areaForm v q ≤ o.areaForm v z from hside hq.1).not_gt
      (show o.areaForm v z < o.areaForm v q from hq.2)
  have hopen : IsOpen {q | o.areaForm v z < o.areaForm v q} :=
    isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional _)
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hcl := hp.2.2.1
  simp only [hopen.interior_eq, hempty, closure_empty, mem_empty_iff_false] at hcl

/-- Advancing the origin removes precisely the half-open interval before the new origin. -/
theorem rayCrossings_add_smul_of_nonneg (S : Set E) (z v : E) {c : ℝ} (hc : 0 ≤ c) :
    o.rayCrossings S (z + c • v) v = o.rayCrossings S z v \
      ((fun t : ℝ ↦ z + t • v) '' Ico 0 c) := by
  by_cases hv : v = 0
  · simp [hv]
  have hinj : Function.Injective (fun t : ℝ ↦ z + t • v) :=
    fun a b h ↦ (smul_left_injective ℝ hv) (add_left_cancel h)
  ext p
  simp only [rayCrossings, map_add, map_smul, areaForm_apply_self, smul_zero, add_zero,
    mem_sdiff, mem_inter_iff, mem_ofPred_eq, mem_image, mem_Ico]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hp⟩
    have heq : z + c • v + t • v = z + (c + t) • v := by rw [add_smul]; abel
    refine ⟨⟨⟨c + t, add_nonneg hc ht, heq⟩, hp⟩, ?_⟩
    rintro ⟨a, ha, h⟩
    have := hinj (h.trans heq)
    linarith [ha.2]
  · rintro ⟨⟨⟨t, ht, rfl⟩, hp⟩, hnot⟩
    have hct : c ≤ t := by
      by_contra h
      exact hnot ⟨t, ⟨ht, lt_of_not_ge h⟩, rfl⟩
    refine ⟨⟨t - c, sub_nonneg.mpr hct, ?_⟩, hp⟩
    rw [sub_smul]
    abel

/-- Moving the origin backwards adds precisely the preceding half-open interval. -/
theorem rayCrossings_add_smul_of_nonpos (S : Set E) (z v : E) {c : ℝ} (hc : c ≤ 0) :
    o.rayCrossings S (z + c • v) v = o.rayCrossings S z v ∪
      (((fun t : ℝ ↦ z + t • v) '' Ico c 0) ∩
        boundaryCrossings S {q | o.areaForm v z < o.areaForm v q}) := by
  ext p
  simp only [rayCrossings, map_add, map_smul, areaForm_apply_self, smul_zero, add_zero,
    mem_union, mem_inter_iff, mem_ofPred_eq, mem_image, mem_Ico]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hp⟩
    have heq : z + c • v + t • v = z + (c + t) • v := by rw [add_smul]; abel
    by_cases hct : 0 ≤ c + t
    · exact Or.inl ⟨⟨c + t, hct, heq⟩, hp⟩
    · exact Or.inr ⟨⟨c + t, ⟨by linarith, lt_of_not_ge hct⟩, heq.symm⟩, hp⟩
  · rintro (⟨⟨t, ht, rfl⟩, hp⟩ | ⟨⟨t, ht, rfl⟩, hp⟩)
    · refine ⟨⟨t - c, by linarith, ?_⟩, hp⟩
      rw [sub_smul]
      abel
    · refine ⟨⟨t - c, by linarith [ht.1], ?_⟩, hp⟩
      rw [sub_smul]
      abel

theorem mem_boundaryCrossings_halfPlane_lower_iff {S : Set E} {v p : E} :
    p ∈ boundaryCrossings S
        {q | o.areaForm v q < o.areaForm v p} ↔
      p ∈ boundaryCrossings S
        {q | o.areaForm v p < o.areaForm v q} := by
  have heq : {q | o.areaForm v q < o.areaForm v p} =
      {q | o.areaForm (-v) p < o.areaForm (-v) q} := by
    ext q
    simp only [mem_ofPred_eq, map_neg, LinearMap.neg_apply, neg_lt_neg_iff]
  rw [heq, o.mem_boundaryCrossings_halfPlane_iff,
    o.mem_boundaryCrossings_halfPlane_iff]
  simp only [map_neg, LinearMap.neg_apply, neg_lt_neg_iff]
  exact and_congr_right fun _ ↦ and_comm

theorem mem_boundaryCrossings_halfPlane_of_mem_openSegment {S : Set E} {v a b p : E}
    (hseg : openSegment ℝ a b ⊆ S) (hp : p ∈ openSegment ℝ a b)
    (hab : o.areaForm v a ≠ o.areaForm v b) :
    p ∈ boundaryCrossings S
      {q | o.areaForm v p < o.areaForm v q} :=
  (o.areaForm v).toAffineMap.mem_boundaryCrossings_preimage_Ioi_of_mem_openSegment
    (LinearMap.continuous_of_finiteDimensional _) hseg hp hab

/-- Moving the origin across a segment missing the carrier preserves ray crossings. -/
theorem rayCrossings_add_smul_eq {S : Set E} {z v : E} {c : ℝ}
    (hbase : segment ℝ z (z + c • v) ∩ S = ∅) :
    o.rayCrossings S z v = o.rayCrossings S (z + c • v) v := by
  have hseg (t : ℝ) (ht : t ∈ segment ℝ (0 : ℝ) c) :
      z + t • v ∈ segment ℝ z (z + c • v) := by
    have h := mem_image_of_mem (AffineMap.lineMap z (z + v)) ht
    rw [image_segment] at h
    simpa only [AffineMap.lineMap_apply_module', add_sub_cancel_left,
      zero_smul, zero_add, add_comm, add_zero] using h
  have havoid (t : ℝ) (ht : t ∈ segment ℝ (0 : ℝ) c) : z + t • v ∉ S := by
    intro h
    have hmem := hbase ▸ (show z + t • v ∈ segment ℝ z (z + c • v) ∩ S
      from ⟨hseg t ht, h⟩)
    exact hmem
  rcases le_total 0 c with hc | hc
  · symm
    rw [o.rayCrossings_add_smul_of_nonneg S z v hc, sdiff_eq_self_iff_disjoint]
    rw [disjoint_left]
    rintro p ⟨t, ht, rfl⟩ hp
    exact havoid t (by rw [segment_eq_Icc hc]; exact ⟨ht.1, ht.2.le⟩) hp.2.1.1
  · rw [o.rayCrossings_add_smul_of_nonpos S z v hc]
    symm
    apply union_eq_left.mpr
    rintro p ⟨⟨t, ht, rfl⟩, hp⟩
    have htseg : t ∈ segment ℝ (0 : ℝ) c := by
      rw [segment_symm, segment_eq_Icc hc]
      exact ⟨ht.1, ht.2.le⟩
    exact (havoid t htseg hp.1.1).elim

private theorem direction_ne_zero {S : Set E} {v p : E}
    (hp : p ∈ boundaryCrossings S {r | o.areaForm v p < o.areaForm v r}) : v ≠ 0 := by
  rintro rfl
  simp [boundaryCrossings] at hp

private theorem last_crossing_interval
    {S : Set E} {q v : E} {ε : ℝ}
    (hq : q ∈ boundaryCrossings S {r | o.areaForm v q < o.areaForm v r})
    (hlast : ∀ s : ℝ, 0 < s → q + s • v ∉
      boundaryCrossings S {r | o.areaForm v q < o.areaForm v r})
    (hgap : ∀ d ∈ Ioo 0 ε, q - d • v ∉ S) :
    ∀ d ∈ Ioo 0 ε, o.rayCrossings S (q - d • v) v = {q} := by
  intro d hd
  apply subset_antisymm
  · rintro p ⟨⟨s, hs, rfl⟩, hp⟩
    have heq : q - d • v + s • v = q + (s - d) • v := by rw [sub_smul]; abel
    have hp' : q + (s - d) • v ∈ boundaryCrossings S
        {r | o.areaForm v q < o.areaForm v r} := by
      rw [← heq]
      simpa [map_sub, map_smul] using hp
    rcases lt_trichotomy s d with hsd | hsd | hds
    · exfalso
      apply hgap (d - s) ⟨by linarith, by linarith [hd.2]⟩
      convert hp'.1.1 using 1
      rw [sub_smul, sub_smul]
      abel
    · change q - d • v + s • v = q
      rw [hsd, sub_add_cancel]
    · exact (hlast (s - d) (sub_pos.mpr hds) hp').elim
  · rintro p rfl
    exact (o.mem_rayCrossings_iff).mpr ⟨⟨d, hd.1.le, by abel⟩, hq⟩

/-- Exterior singleton-ray origins form a preceding interval exactly at a last crossing
with a preceding gap in the carrier. -/
theorem singleton_interval_iff
    {S : Set E} {q v : E} {ε : ℝ} (hε : 0 < ε) :
    (∀ d ∈ Ioo 0 ε, q - d • v ∉ S ∧ o.rayCrossings S (q - d • v) v = {q}) ↔
      q ∈ boundaryCrossings S {r | o.areaForm v q < o.areaForm v r} ∧
      (∀ s : ℝ, 0 < s → q + s • v ∉
        boundaryCrossings S {r | o.areaForm v q < o.areaForm v r}) ∧
      (∀ d ∈ Ioo 0 ε, q - d • v ∉ S) := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := exists_between hε
    have hqmem : q ∈ o.rayCrossings S (q - d • v) v := (h d hd).2 ▸ mem_singleton q
    have hq := (o.mem_rayCrossings_iff.mp hqmem).2
    refine ⟨hq, ?_, fun d hd ↦ (h d hd).1⟩
    intro s hs hp
    have hpmem : q + s • v ∈ o.rayCrossings S (q - d • v) v := by
      refine ⟨⟨s + d, by linarith [hd.1], ?_⟩, ?_⟩
      · rw [add_smul]
        abel
      · simpa [map_sub, map_smul] using hp
    rw [(h d hd).2, mem_singleton_iff] at hpmem
    have hzero : s • v = 0 := add_eq_left.mp hpmem
    exact (smul_ne_zero hs.ne' (direction_ne_zero o hq)) hzero
  · rintro ⟨hq, hlast, hgap⟩ d hd
    exact ⟨hgap d hd, last_crossing_interval o hq hlast hgap d hd⟩

/-- A finite forward carrier section with a crossing beyond its origin supplies a
preceding interval of exterior singleton-ray origins. -/
theorem exists_singleton_interval_of_finite_ray
    {S : Set E} {z v : E}
    (hfinite : (S ∩ {q | ∃ t : ℝ, 0 ≤ t ∧ q = z + t • v}).Finite)
    (hcross : ∃ q ∈ o.rayCrossings S z v, q ≠ z) :
    ∃ q ∈ o.rayCrossings S z v, ∃ ε : ℝ, 0 < ε ∧
      ∀ d ∈ Ioo 0 ε, q - d • v ∉ S ∧ o.rayCrossings S (q - d • v) v = {q} := by
  obtain ⟨q₀, hq₀, hq₀z⟩ := hcross
  have hv : v ≠ 0 := direction_ne_zero o ((o.mem_rayCrossings_iff.mp hq₀).2)
  obtain ⟨⟨t₀, ht₀, rfl⟩, hcross₀⟩ := hq₀
  have ht₀pos : 0 < t₀ := lt_of_le_of_ne ht₀ (by
    intro h
    exact hq₀z (by simp [← h]))
  let T : Set ℝ := {t | 0 ≤ t ∧ z + t • v ∈ S}
  let C : Set ℝ := {t | 0 ≤ t ∧ z + t • v ∈ boundaryCrossings S
    {r | o.areaForm v z < o.areaForm v r}}
  have hinj : Injective (fun t : ℝ ↦ z + t • v) :=
    fun s t h ↦ smul_left_injective ℝ hv (add_left_cancel h)
  have hT : T.Finite := (hfinite.preimage hinj.injOn).subset fun t ht ↦
    ⟨ht.2, t, ht.1, rfl⟩
  have hCT : C ⊆ T := fun t ht ↦ ⟨ht.1, ht.2.1.1⟩
  obtain ⟨t, ht, hmax⟩ := C.exists_max_image id (hT.subset hCT) ⟨t₀, ht₀, hcross₀⟩
  have htpos : 0 < t := ht₀pos.trans_le (hmax t₀ ⟨ht₀, hcross₀⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (hT.sdiff (t := {t})).isClosed.isOpen_compl t (by simp)
  have hq : z + t • v ∈ boundaryCrossings S
      {r | o.areaForm v (z + t • v) < o.areaForm v r} := by
    simpa only [map_add, map_smul, Orientation.areaForm_apply_self, smul_zero, add_zero]
      using ht.2
  have hlast : ∀ s : ℝ, 0 < s → z + t • v + s • v ∉ boundaryCrossings S
      {r | o.areaForm v (z + t • v) < o.areaForm v r} := by
    intro s hs hmem
    have hCmem : t + s ∈ C := by
      refine ⟨by linarith, ?_⟩
      simpa only [add_smul, add_assoc, map_add, map_smul,
        Orientation.areaForm_apply_self, smul_zero, add_zero] using hmem
    have := hmax _ hCmem
    change t + s ≤ t at this
    linarith
  have hgap : ∀ d ∈ Ioo 0 (min ε t), z + t • v - d • v ∉ S := by
    rintro d ⟨hdpos, hdmin⟩ hmem
    have hdε : d < ε := hdmin.trans_le (min_le_left _ _)
    have hdt : d < t := hdmin.trans_le (min_le_right _ _)
    have htd : z + (t - d) • v = z + t • v - d • v := by rw [sub_smul]; abel
    have hb : t - d ∈ ball t ε := by
      rw [mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    exact hball hb ⟨⟨by linarith, htd ▸ hmem⟩, by simpa using hdpos.ne'⟩
  exact ⟨z + t • v, ⟨⟨t, ht.1, rfl⟩, ht.2⟩, min ε t, lt_min hε htpos,
    fun d hd ↦ ⟨hgap d hd, last_crossing_interval o hq hlast hgap d hd⟩⟩

/-- A finite supporting fibre supplies a singleton-ray interval at a crossing forward
of the supplied crossing. -/
theorem exists_singleton_interval_of_finite_fiber
    {S : Set E} {v p : E}
    (hp : p ∈ boundaryCrossings S {r | o.areaForm v p < o.areaForm v r})
    (hfinite : (S ∩ o.areaForm v ⁻¹' {o.areaForm v p}).Finite) :
    ∃ q ∈ o.rayCrossings S p v,
      ∃ ε : ℝ, 0 < ε ∧ ∀ d ∈ Ioo 0 ε,
        q - d • v ∉ S ∧ o.rayCrossings S (q - d • v) v = {q} := by
  have hv := direction_ne_zero o hp
  have hf : (S ∩ {q | ∃ t : ℝ, 0 ≤ t ∧ q = (p - v) + t • v}).Finite := by
    apply hfinite.subset
    rintro q ⟨hq, t, ht, rfl⟩
    exact ⟨hq, by simp [map_sub, map_add, map_smul]⟩
  have hcross : ∃ q ∈ o.rayCrossings S (p - v) v, q ≠ p - v := by
    refine ⟨p, (o.mem_rayCrossings_iff).mpr ⟨⟨1, zero_le_one, by simp⟩, hp⟩, ?_⟩
    intro h
    exact hv (sub_eq_self.mp h.symm)
  obtain ⟨q, hq, ε, hε, hinterval⟩ := exists_singleton_interval_of_finite_ray o hf hcross
  obtain ⟨⟨t, ht, rfl⟩, hqcross⟩ := hq
  have ht1 : 1 ≤ t := by
    by_contra h
    have hlt : t < 1 := lt_of_not_ge h
    obtain ⟨d, hd⟩ := exists_between hε
    have hpmem : p ∈ o.rayCrossings S ((p - v + t • v) - d • v) v := by
      apply (o.mem_rayCrossings_iff).mpr
      refine ⟨⟨1 - t + d, by linarith [hd.1], ?_⟩, hp⟩
      rw [add_smul, sub_smul, one_smul]
      abel
    rw [(hinterval d hd).2, mem_singleton_iff] at hpmem
    have heq : p - v + t • v = p - v + (1 : ℝ) • v := by
      simpa using hpmem.symm
    have htEq := smul_left_injective ℝ hv (add_left_cancel heq)
    linarith
  refine ⟨p - v + t • v, (o.mem_rayCrossings_iff).mpr ⟨⟨t - 1,
    sub_nonneg.mpr ht1, ?_⟩, ?_⟩, ε, hε, hinterval⟩
  · rw [sub_smul, one_smul]
    abel
  · simpa [map_sub, map_add, map_smul] using hqcross

/-- Positive rescaling of the direction preserves the crossing set. -/
theorem rayCrossings_pos_smul (S : Set E) (z v : E)
    {c : ℝ} (hc : 0 < c) : o.rayCrossings S z (c • v) = o.rayCrossings S z v := by
  have hplane : {q | o.areaForm (c • v) z < o.areaForm (c • v) q} =
      {q | o.areaForm v z < o.areaForm v q} := by
    ext q
    simp only [mem_ofPred_eq, map_smul, LinearMap.smul_apply, smul_eq_mul,
      mul_lt_mul_iff_right₀ hc]
  simp only [Orientation.rayCrossings, hplane]
  congr 1
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * c, mul_nonneg ht hc.le, by rw [smul_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t / c, div_nonneg ht hc.le, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']⟩

/-- A bounded set admits an exterior origin with no ray crossings in a prescribed direction. -/
theorem exists_rayCrossings_eq_empty {S : Set E}
    (hS : Bornology.IsBounded S) (v : E) : ∃ z ∉ S, o.rayCrossings S z v = ∅ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank ℝ E by rw [Fact.out (p := Module.finrank ℝ E = 2)]; norm_num)
  obtain ⟨z, hz, hescape⟩ := ((NormedSpace.isVonNBounded_iff ℝ).mpr hS).exists_ray_avoiding v
  refine ⟨z, hz, eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro q ⟨⟨t, ht, rfl⟩, hq⟩
  exact hescape t ht hq.1.1

end Orientation

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

/-- Ray crossings in the complex plane use its canonical orientation. -/
abbrev rayCrossings (S : Set ℂ) (z v : ℂ) : Set ℂ :=
  Complex.orientation.rayCrossings S z v

/-- A bounded longitudinal coordinate supplies a forward ray missing the carrier. -/
theorem exists_ray_avoiding_of_bddAbove {S : Set ℂ} {v : ℂ} (hv : v ≠ 0)
    (hS : BddAbove ((fun p : ℂ ↦ (p / v).re) '' S)) :
    ∃ z ∉ S, ∀ t : ℝ, 0 ≤ t → z + t • v ∉ S := by
  let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulRight ℝ v⁻¹)
  have hfv : f v = 1 := by simp [f, hv]
  have hf : f ≠ 0 := fun h ↦ by simp [h] at hfv
  have hbound : BddAbove (f.toAffineMap '' S) := by
    change BddAbove ((fun p : ℂ ↦ (p * v⁻¹).re) '' S)
    simpa only [div_eq_mul_inv] using hS
  simpa only [vadd_eq_add, add_comm] using
    AffineMap.exists_ray_avoiding_of_bddAbove f.toAffineMap hf
    (show 0 ≤ f v by rw [hfv]; exact zero_le_one) hbound

end Complex
