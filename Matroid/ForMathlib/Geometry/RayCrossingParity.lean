module

public import Matroid.ForMathlib.Geometry.RayCrossing
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Parity of ray crossings

Boundary-crossing evenness compares ray counts across a carrier-disjoint segment.
Only the two forward carrier sections need be finite. The half-strip coordinates
stay private. Eventual finiteness gives local parity stability away from the carrier's
closure; a closed carrier gives local constancy on its complement.
-/

@[expose] public section

noncomputable section

open Set Metric Function Filter Topology Module
open scoped Classical

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 2)]

private instance : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 1

private def stripCoordinates (b : Basis (Fin 2) ℝ E) (x : E) : E ≃ᴬ[ℝ] ℝ × ℝ :=
  AffineEquiv.toContinuousAffineEquiv
    (((AffineEquiv.constVAdd ℝ E (-x)).trans b.equivFun.toAffineEquiv).trans
      (LinearEquiv.finTwoArrow ℝ ℝ).toAffineEquiv)

private abbrev baseCoord (b : Basis (Fin 2) ℝ E) (x q : E) : ℝ :=
  (stripCoordinates b x q).1

private abbrev heightCoord (b : Basis (Fin 2) ℝ E) (x q : E) : ℝ :=
  (stripCoordinates b x q).2

private theorem coordinates_apply (b : Basis (Fin 2) ℝ E) (x q : E) :
    stripCoordinates b x q = (b.repr (q - x) 0, b.repr (q - x) 1) := by
  change (b.repr (-x + q) 0, b.repr (-x + q) 1) = _
  rw [neg_add_eq_sub]

private theorem coordinate_reconstruction (b : Basis (Fin 2) ℝ E) (x q : E) :
    x + baseCoord b x q • b 0 + heightCoord b x q • b 1 = q := by
  have h := b.sum_repr (q - x)
  rw [Fin.sum_univ_two] at h
  simp only [baseCoord, heightCoord, coordinates_apply]
  rw [add_assoc, h]
  exact add_sub_cancel _ _

@[simp] private theorem coordinates_add_smul (b : Basis (Fin 2) ℝ E) (x : E) (t : ℝ) :
    stripCoordinates b x (x + t • b 1) = (0, t) := by
  rw [coordinates_apply, add_sub_cancel_left]
  simp

@[simp] private theorem coordinates_add_basis_add_smul
    (b : Basis (Fin 2) ℝ E) (x : E) (t : ℝ) :
    stripCoordinates b x (x + b 0 + t • b 1) = (1, t) := by
  rw [coordinates_apply, show x + b 0 + t • b 1 - x = b 0 + t • b 1 by abel]
  simp

private def halfStrip (b : Basis (Fin 2) ℝ E) (x : E) : Set E :=
  stripCoordinates b x ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ))

private theorem mem_halfStrip {b : Basis (Fin 2) ℝ E} {x q : E} :
    q ∈ halfStrip b x ↔
      0 < baseCoord b x q ∧ baseCoord b x q < 1 ∧ 0 < heightCoord b x q := by
  simp [halfStrip, baseCoord, heightCoord, and_assoc]

private theorem isOpen_halfStrip (b : Basis (Fin 2) ℝ E) (x : E) :
    IsOpen (halfStrip b x) :=
  (isOpen_Ioo.prod isOpen_Ioi).preimage (stripCoordinates b x).continuous

private theorem frontier_halfStrip (b : Basis (Fin 2) ℝ E) (x : E) :
    frontier (halfStrip b x) =
      {q | baseCoord b x q = 0 ∧ 0 ≤ heightCoord b x q} ∪
        ({q | baseCoord b x q = 1 ∧ 0 ≤ heightCoord b x q} ∪
          {q | 0 ≤ baseCoord b x q ∧ baseCoord b x q ≤ 1 ∧ heightCoord b x q = 0}) := by
  have hclosure : closure (halfStrip b x) =
      {q | 0 ≤ baseCoord b x q ∧ baseCoord b x q ≤ 1 ∧ 0 ≤ heightCoord b x q} := by
    change closure ((stripCoordinates b x).toHomeomorph ⁻¹' _) = _
    rw [← Homeomorph.preimage_closure, closure_prod_eq,
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi]
    ext q
    change (0 ≤ (stripCoordinates b x q).1 ∧ (stripCoordinates b x q).1 ≤ 1) ∧
      0 ≤ (stripCoordinates b x q).2 ↔ _
    exact and_assoc
  rw [frontier, hclosure, (isOpen_halfStrip b x).interior_eq]
  ext q
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_halfStrip, mem_union]
  grind

private theorem baseCoord_mul (o : Orientation ℝ E (Fin 2))
    (b : Basis (Fin 2) ℝ E) (x q : E) :
    baseCoord b x q * o.areaForm (b 1) (b 0) =
      o.areaForm (b 1) q - o.areaForm (b 1) x := by
  have h := congrArg (o.areaForm (b 1)) (coordinate_reconstruction b x q)
  simp only [map_add, map_smul, smul_eq_mul, areaForm_apply_self, mul_zero, add_zero] at h
  linarith

private theorem baseCoord_eq_div (o : Orientation ℝ E (Fin 2))
    {b : Basis (Fin 2) ℝ E} {x q p : E} (huv : o.areaForm (b 1) (b 0) ≠ 0)
    (hfx : o.areaForm (b 1) p = o.areaForm (b 1) x) :
    baseCoord b x q = (o.areaForm (b 1) q - o.areaForm (b 1) p) /
      o.areaForm (b 1) (b 0) := by
  rw [eq_div_iff huv, hfx]
  exact baseCoord_mul o b x q

private theorem baseCoord_sub_one_eq_div (o : Orientation ℝ E (Fin 2))
    {b : Basis (Fin 2) ℝ E} {x q p : E} (huv : o.areaForm (b 1) (b 0) ≠ 0)
    (hfy : o.areaForm (b 1) p = o.areaForm (b 1) (x + b 0)) :
    baseCoord b x q - 1 = (o.areaForm (b 1) q - o.areaForm (b 1) p) /
      o.areaForm (b 1) (b 0) := by
  rw [eq_div_iff huv, sub_mul, one_mul, baseCoord_mul, hfy, map_add]
  ring

private theorem mem_boundaryCrossings_halfStrip_left_iff
    (o : Orientation ℝ E (Fin 2)) {b : Basis (Fin 2) ℝ E} {x p : E} {S : Set E}
    (huv : o.areaForm (b 1) (b 0) ≠ 0) (hsp : baseCoord b x p = 0)
    (htp : 0 < heightCoord b x p) :
    p ∈ boundaryCrossings S
        {q | o.areaForm (b 1) p < o.areaForm (b 1) q} ↔
      p ∈ boundaryCrossings S (halfStrip b x) := by
  have hfx : o.areaForm (b 1) p = o.areaForm (b 1) x := by
    have h := baseCoord_mul o b x p
    rw [hsp, zero_mul] at h
    linarith
  have hopen : IsOpen {q | baseCoord b x q < 1 ∧ 0 < heightCoord b x q} :=
    (isOpen_lt (stripCoordinates b x).continuous.fst continuous_const).inter
      (isOpen_lt continuous_const (stripCoordinates b x).continuous.snd)
  have hp : p ∈ interior {q | baseCoord b x q < 1 ∧ 0 < heightCoord b x q} := by
    rw [hopen.interior_eq]
    exact ⟨by rw [hsp]; norm_num, htp⟩
  have heq : halfStrip b x = {q | 0 < baseCoord b x q} ∩
      {q | baseCoord b x q < 1 ∧ 0 < heightCoord b x q} := by
    ext q
    exact mem_halfStrip
  rw [heq, mem_boundaryCrossings_inter_of_mem_interior hp]
  rcases lt_or_gt_of_ne huv with hneg | hpos
  · have heq : {q | 0 < baseCoord b x q} =
        {q | o.areaForm (b 1) q < o.areaForm (b 1) p} := by
      ext q
      simp only [mem_ofPred, baseCoord_eq_div o huv hfx,
        lt_div_iff_of_neg hneg, zero_mul, sub_neg]
    rw [heq]
    exact (o.mem_boundaryCrossings_halfPlane_lower_iff).symm
  · have heq : {q | 0 < baseCoord b x q} =
        {q | o.areaForm (b 1) p < o.areaForm (b 1) q} := by
      ext q
      simp only [mem_ofPred, baseCoord_eq_div o huv hfx, lt_div_iff₀ hpos, zero_mul, sub_pos]
    rw [heq]

private theorem mem_boundaryCrossings_halfStrip_right_iff
    (o : Orientation ℝ E (Fin 2)) {b : Basis (Fin 2) ℝ E} {x p : E} {S : Set E}
    (huv : o.areaForm (b 1) (b 0) ≠ 0) (hsp : baseCoord b x p = 1)
    (htp : 0 < heightCoord b x p) :
    p ∈ boundaryCrossings S
        {q | o.areaForm (b 1) p < o.areaForm (b 1) q} ↔
      p ∈ boundaryCrossings S (halfStrip b x) := by
  have hfy : o.areaForm (b 1) p = o.areaForm (b 1) (x + b 0) := by
    have h := baseCoord_mul o b x p
    rw [hsp, one_mul] at h
    rw [map_add]
    linarith
  have hopen : IsOpen {q | 0 < baseCoord b x q ∧ 0 < heightCoord b x q} :=
    (isOpen_lt continuous_const (stripCoordinates b x).continuous.fst).inter
      (isOpen_lt continuous_const (stripCoordinates b x).continuous.snd)
  have hp : p ∈ interior {q | 0 < baseCoord b x q ∧ 0 < heightCoord b x q} := by
    rw [hopen.interior_eq]
    exact ⟨by rw [hsp]; norm_num, htp⟩
  have heq : halfStrip b x = {q | baseCoord b x q < 1} ∩
      {q | 0 < baseCoord b x q ∧ 0 < heightCoord b x q} := by
    ext q
    simp only [mem_halfStrip, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [heq, mem_boundaryCrossings_inter_of_mem_interior hp]
  rcases lt_or_gt_of_ne huv with hneg | hpos
  · have heq : {q | baseCoord b x q < 1} =
        {q | o.areaForm (b 1) p < o.areaForm (b 1) q} := by
      ext q
      change baseCoord b x q < 1 ↔ _
      rw [← sub_neg (a := baseCoord b x q) (b := 1),
        baseCoord_sub_one_eq_div o huv hfy, div_lt_iff_of_neg hneg, zero_mul, sub_pos]
      rfl
    rw [heq]
  · have heq : {q | baseCoord b x q < 1} =
        {q | o.areaForm (b 1) q < o.areaForm (b 1) p} := by
      ext q
      change baseCoord b x q < 1 ↔ _
      rw [← sub_neg (a := baseCoord b x q) (b := 1),
        baseCoord_sub_one_eq_div o huv hfy, div_lt_iff₀ hpos, zero_mul, sub_neg]
      rfl
    rw [heq]
    exact (o.mem_boundaryCrossings_halfPlane_lower_iff).symm

private theorem carrier_frontier_halfStrip_eq {b : Basis (Fin 2) ℝ E} {x : E} {S : Set E}
    (hbase : segment ℝ x (x + b 0) ∩ S = ∅) :
    S ∩ frontier (halfStrip b x) =
      (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = x + t • (b 1)}) ∪
        (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = (x + b 0) + t • (b 1)}) := by
  have hsub : S ∩ frontier (halfStrip b x) ⊆
      (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = x + t • (b 1)}) ∪
        (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = (x + b 0) + t • (b 1)}) := by
    intro p hp
    obtain ⟨hpS, hpfr⟩ := hp
    rw [frontier_halfStrip b x] at hpfr
    have hdec := coordinate_reconstruction b x p
    rcases hpfr with ⟨h0, ht⟩ | ⟨h1, ht⟩ | ⟨hs0, hs1, ht⟩
    · refine Or.inl ⟨hpS, heightCoord b x p, ht, ?_⟩
      simpa only [h0, zero_smul, add_zero] using hdec.symm
    · refine Or.inr ⟨hpS, heightCoord b x p, ht, ?_⟩
      simpa only [h1, one_smul] using hdec.symm
    · exfalso
      rw [ht, zero_smul, add_zero] at hdec
      have hseg : p ∈ segment ℝ x (x + b 0) := by
        rw [segment_eq_image_lineMap]
        exact ⟨baseCoord b x p, ⟨hs0, hs1⟩, by
          rw [AffineMap.lineMap_apply_module', add_sub_cancel_left]
          exact (add_comm _ _).trans hdec⟩
      have hmem : p ∈ segment ℝ x (x + b 0) ∩ S := ⟨hseg, hpS⟩
      rw [hbase] at hmem
      exact hmem
  refine hsub.antisymm ?_
  rintro p (⟨hpS, t, ht, rfl⟩ | ⟨hpS, t, ht, rfl⟩)
  · refine ⟨hpS, ?_⟩
    rw [frontier_halfStrip]
    exact Or.inl ⟨by simp [baseCoord], by simpa [heightCoord] using ht⟩
  · refine ⟨hpS, ?_⟩
    rw [frontier_halfStrip]
    exact Or.inr (Or.inl ⟨by simp [baseCoord], by simpa [heightCoord] using ht⟩)

/-- The crossings of the half-strip boundary are the crossings of the two boundary rays. -/
private theorem boundaryCrossings_halfStrip_eq (o : Orientation ℝ E (Fin 2))
    {b : Basis (Fin 2) ℝ E} {x : E} {S : Set E}
    (huv : o.areaForm (b 1) (b 0) ≠ 0) (hbase : segment ℝ x (x + b 0) ∩ S = ∅) :
    boundaryCrossings S (halfStrip b x) =
      o.rayCrossings S x (b 1) ∪ o.rayCrossings S (x + b 0) (b 1) := by
  have hxS : x ∉ S := by
    intro h
    have hmem : x ∈ segment ℝ x (x + b 0) ∩ S := ⟨left_mem_segment ℝ x (x + b 0), h⟩
    rw [hbase] at hmem
    exact hmem
  have hyS : (x + b 0) ∉ S := by
    intro h
    have hmem : (x + b 0) ∈ segment ℝ x (x + b 0) ∩ S := ⟨right_mem_segment ℝ x (x + b 0), h⟩
    rw [hbase] at hmem
    exact hmem
  ext p
  simp only [mem_union, o.mem_rayCrossings_iff]
  constructor
  · intro hp
    have hpfr := hp.1
    rw [carrier_frontier_halfStrip_eq hbase] at hpfr
    rcases hpfr with ⟨hpS, t, ht, hpt⟩ | ⟨hpS, t, ht, hpt⟩
    · have htne : t ≠ 0 := fun h ↦ hxS (by simpa [hpt, h] using hpS)
      have hpos : 0 < t := lt_of_le_of_ne ht htne.symm
      have hb0 : baseCoord b x p = 0 := by simp [hpt, baseCoord]
      have hheight : 0 < heightCoord b x p := by simpa [hpt, heightCoord] using hpos
      exact Or.inl ⟨⟨t, ht, hpt⟩,
        (mem_boundaryCrossings_halfStrip_left_iff o huv hb0 hheight).mpr hp⟩
    · have htne : t ≠ 0 := fun h ↦ hyS (by simpa [hpt, h] using hpS)
      have hpos : 0 < t := lt_of_le_of_ne ht htne.symm
      have hb1 : baseCoord b x p = 1 := by simp [hpt, baseCoord]
      have hheight : 0 < heightCoord b x p := by simpa [hpt, heightCoord] using hpos
      exact Or.inr ⟨⟨t, ht, hpt⟩,
        (mem_boundaryCrossings_halfStrip_right_iff o huv hb1 hheight).mpr hp⟩
  · rintro (⟨⟨t, ht, hpt⟩, hcr⟩ | ⟨⟨t, ht, hpt⟩, hcr⟩)
    · have hb0 : baseCoord b x p = 0 := by simp only [hpt, baseCoord, coordinates_add_smul]
      have hbt : heightCoord b x p = t := by simp only [hpt, heightCoord, coordinates_add_smul]
      have hpos : 0 < t := by
        rcases eq_or_lt_of_le ht with h | h
        · have hp_eq : p = x := by rw [hpt, ← h, zero_smul, add_zero]
          exact absurd (hp_eq ▸ hcr.1.1) hxS
        · exact h
      exact (mem_boundaryCrossings_halfStrip_left_iff o huv hb0 (by rw [hbt]; exact hpos)).mp hcr
    · have hb1 : baseCoord b x p = 1 := by
        simp only [hpt, baseCoord, coordinates_add_basis_add_smul]
      have hbt : heightCoord b x p = t := by
        simp only [hpt, heightCoord, coordinates_add_basis_add_smul]
      have hpos : 0 < t := by
        rcases eq_or_lt_of_le ht with h | h
        · have hp_eq : p = (x + b 0) := by rw [hpt, ← h, zero_smul, add_zero]
          exact absurd (hp_eq ▸ hcr.1.1) hyS
        · exact h
      exact (mem_boundaryCrossings_halfStrip_right_iff o huv hb1 (by rw [hbt]; exact hpos)).mp hcr

/-- Comparing the two parallel boundary rays uses only their finite intersections
with the carrier. -/
private theorem rayCrossings_ncard_mod_two_eq_of_basis (o : Orientation ℝ E (Fin 2))
    {b : Basis (Fin 2) ℝ E} {S : Set E} {x : E}
    (hEven : ∀ U : Set E, (S ∩ frontier U).Finite →
      Even (boundaryCrossings S U).ncard)
    (hx : (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = x + t • (b 1)}).Finite)
    (hy : (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = (x + b 0) + t • (b 1)}).Finite)
    (hbase : segment ℝ x (x + b 0) ∩ S = ∅)
    (huv : o.areaForm (b 1) (b 0) ≠ 0) :
    (o.rayCrossings S x (b 1)).ncard % 2 = (o.rayCrossings S (x + b 0) (b 1)).ncard % 2 := by
  have hEq := boundaryCrossings_halfStrip_eq o (S := S) huv hbase
  have hxfin : (o.rayCrossings S x (b 1)).Finite :=
    hx.subset fun _ hp ↦ ⟨hp.2.1.1, hp.1⟩
  have hyfin : (o.rayCrossings S (x + b 0) (b 1)).Finite := hy.subset fun _ hp ↦ ⟨hp.2.1.1, hp.1⟩
  have hdisj : Disjoint (o.rayCrossings S x (b 1)) (o.rayCrossings S (x + b 0) (b 1)) := by
    rw [Set.disjoint_left]
    intro p hp1 hp2
    obtain ⟨⟨t, -, hpt⟩, -⟩ := hp1
    obtain ⟨⟨s, -, hps⟩, -⟩ := hp2
    have h1 : baseCoord b x p = 0 := by simp only [hpt, baseCoord, coordinates_add_smul]
    have h2 : baseCoord b x p = 1 := by simp only [hps, baseCoord, coordinates_add_basis_add_smul]
    rw [h1] at h2
    norm_num at h2
  have hfrontfin : (S ∩ frontier (halfStrip b x)).Finite := by
    rw [carrier_frontier_halfStrip_eq hbase]
    exact hx.union hy
  have heven : Even (boundaryCrossings S (halfStrip b x)).ncard :=
    hEven _ hfrontfin
  rw [hEq, Set.ncard_union_eq hdisj hxfin hyfin] at heven
  have h := Nat.even_add.mp heven
  simp only [Nat.even_iff] at h
  omega

private theorem exists_strip_basis (o : Orientation ℝ E (Fin 2)) {u v : E}
    (h : o.areaForm v u ≠ 0) : ∃ b : Basis (Fin 2) ℝ E, b 0 = u ∧ b 1 = v := by
  have hlin : LinearIndependent ℝ ![u, v] :=
    o.areaForm_ne_zero_iff_linearIndependent.mp (by
      rwa [o.areaForm_swap, neg_ne_zero])
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hlin ?_, ?_, ?_⟩
  · simpa using (Fact.out : finrank ℝ E = 2).symm
  · simp [coe_basisOfLinearIndependentOfCardEqFinrank]
  · simp [coe_basisOfLinearIndependentOfCardEqFinrank]

/-- Ray-crossing parity agrees across a disjoint segment if both forward ray
intersections are finite. The direction may be zero or parallel to the segment. -/
theorem rayCrossings_ncard_mod_two_eq_of_even_boundaryCrossings
    (o : Orientation ℝ E (Fin 2)) {S : Set E} {v x y : E}
    (hEven : ∀ U : Set E, (S ∩ frontier U).Finite →
      Even (boundaryCrossings S U).ncard)
    (hx : (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = x + t • v}).Finite)
    (hy : (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = y + t • v}).Finite)
    (hbase : segment ℝ x y ∩ S = ∅) :
    (o.rayCrossings S x v).ncard % 2 = (o.rayCrossings S y v).ncard % 2 := by
  by_cases hv : v = 0
  · subst v
    simp
  by_cases hxy : o.areaForm v y = o.areaForm v x
  · obtain ⟨c, rfl⟩ := (o.areaForm_eq_iff hv).mp hxy
    rw [o.rayCrossings_add_smul_eq hbase]
  · have huv : o.areaForm v (y - x) ≠ 0 := by
      rwa [map_sub, sub_ne_zero]
    obtain ⟨b, hb0, hb1⟩ := exists_strip_basis o huv
    have hy' : x + b 0 = y := by rw [hb0, add_sub_cancel]
    simpa only [hb1, hy'] using rayCrossings_ncard_mod_two_eq_of_basis o (b := b) (x := x) hEven
      (by simpa only [hb1] using hx) (by simpa only [hb1, hy'] using hy)
      (by simpa only [hy'] using hbase) (by simpa only [hb0, hb1] using huv)

/-- Eventual finite forward sections give locally constant parity away from the
carrier's closure. -/
theorem eventually_rayCrossings_parity_eq (o : Orientation ℝ E (Fin 2))
    {S : Set E} {v z : E}
    (hEven : ∀ U : Set E, (S ∩ frontier U).Finite → Even (boundaryCrossings S U).ncard)
    (hz : z ∉ closure S)
    (hfin : ∀ᶠ q in 𝓝 z, (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = q + t • v}).Finite) :
    ∀ᶠ q in 𝓝 z, (o.rayCrossings S q v).ncard % 2 =
      (o.rayCrossings S z v).ncard % 2 := by
  have hseg := (convex_univ (𝕜 := ℝ) (E := E)).eventually_nhdsWithin_segment
    (mem_univ z) (show ∀ᶠ q in 𝓝[univ] z, q ∈ (closure S)ᶜ by
      rw [nhdsWithin_univ]
      exact isClosed_closure.isOpen_compl.mem_nhds hz)
  rw [nhdsWithin_univ] at hseg
  filter_upwards [hfin, hseg] with q hq hqseg
  apply (o.rayCrossings_ncard_mod_two_eq_of_even_boundaryCrossings
    (v := v) (x := z) (y := q) hEven (Filter.Eventually.self_of_nhds (x := z) hfin)
    hq ?_).symm
  exact eq_empty_iff_forall_notMem.mpr fun p hp ↦ hqseg p hp.1 (subset_closure hp.2)

/-- Closed carriers with even boundary cuts and finite forward sections have locally constant
ray-crossing parity on their complements. -/
theorem isLocallyConstant_rayCrossings_parity_of_even_boundaryCrossings
    (o : Orientation ℝ E (Fin 2)) {S : Set E} {v : E}
    (hEven : ∀ U : Set E, (S ∩ frontier U).Finite → Even (boundaryCrossings S U).ncard)
    (hclosed : IsClosed S)
    (hfin : ∀ z ∉ S, (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = z + t • v}).Finite) :
    IsLocallyConstant (fun z : ↥Sᶜ ↦ (o.rayCrossings S z.1 v).ncard % 2) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  have hfin' : ∀ᶠ q in 𝓝 z.1,
      (S ∩ {p | ∃ t : ℝ, 0 ≤ t ∧ p = q + t • v}).Finite :=
    Filter.Eventually.mono (hclosed.isOpen_compl.mem_nhds z.2) fun q hq ↦ hfin q hq
  exact continuous_subtype_val.continuousAt.eventually
    (o.eventually_rayCrossings_parity_eq hEven (by rw [hclosed.closure_eq]; exact z.2) hfin')

end Orientation
