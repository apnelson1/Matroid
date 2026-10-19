module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Star
public import Matroid.ForMathlib.Topology.PrimitiveLink

/-!
# Local stars of polygonal primitive links

Polygonality is a property of the set, expressed by `IsSegmentFigure`. Primitiveness is expressed
by `IsPrimitiveLink`, independently of any polygonal parametrization. Small neighborhoods have
one radius at an arc endpoint and two radii at every other point, including a loop's basepoint.

The segment-figure theorem supplies the star. The arc topology determines its radius count.
-/

@[expose] public section

open Set Metric Function unitInterval
open scoped Classical

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {L : Set V} {a b p : V}

private lemma radii_eq_of_injective {q u v : V} {γ : Path p q} (hinj : Injective γ)
    {r : ℝ} (hr : 0 < r) (hu : u ∈ sphere p r) (hv : v ∈ sphere p r)
    (huseg : segment ℝ p u ⊆ range γ) (hvseg : segment ℝ p v ⊆ range γ) : u = v := by
  obtain ⟨s, rfl⟩ := huseg (right_mem_segment ℝ p u)
  obtain ⟨t, rfl⟩ := hvseg (right_mem_segment ℝ p v)
  have hle {s t : I} (hst : s ≤ t) (hseg : segment ℝ p (γ t) ⊆ range γ) :
      γ s ∈ segment ℝ p (γ t) :=
    γ.image_Icc_subset_of_isConnected hinj (t₁ := 0) (t₂ := t)
      ((convex_segment p (γ t)).isConnected ⟨p, left_mem_segment ..⟩) hseg
      (by simpa only [Path.source] using left_mem_segment ℝ p (γ t)) (right_mem_segment ..)
      ⟨s, ⟨s.prop.1, hst⟩, rfl⟩
  obtain hst | hts := le_total s t
  · exact eq_of_mem_segment_of_mem_sphere p hr hv (hle hst hvseg) hu
  exact (eq_of_mem_segment_of_mem_sphere p hr hu (hle hts huseg) hv).symm

private lemma segment_subset_or_of_inter_subset_singleton {A B : Set V} {y : V}
    (hA : IsClosed A) (hB : IsClosed B) (hmeet : A ∩ B ⊆ {p}) (hne : p ≠ y)
    (hseg : segment ℝ p y ⊆ A ∪ B) : segment ℝ p y ⊆ A ∨ segment ℝ p y ⊆ B := by
  have hsplit : openSegment ℝ p y ⊆ A ∨ openSegment ℝ p y ⊆ B := by
    by_contra! hn
    obtain ⟨u, hu, huA⟩ := Set.not_subset.mp hn.1
    obtain ⟨v, hv, hvB⟩ := Set.not_subset.mp hn.2
    have hsub := (openSegment_subset_segment ℝ p y).trans hseg
    obtain ⟨z, hz, hzA, hzB⟩ := isPreconnected_closed_iff.mp
      (convex_openSegment p y).isPreconnected A B hA hB hsub
      ⟨v, hv, (hsub hv).resolve_right hvB⟩ ⟨u, hu, (hsub hu).resolve_left huA⟩
    exact (ne_of_mem_openSegment_left hne hz).symm (hmeet ⟨hzA, hzB⟩)
  exact hsplit.imp
    (fun h ↦ segment_subset_closure_openSegment.trans (hA.closure_subset_iff.mpr h))
    (fun h ↦ segment_subset_closure_openSegment.trans (hB.closure_subset_iff.mpr h))

private lemma exists_sphere_point {X : Type*} [MetricSpace X] {S : Set X} {p : X}
    (hS : IsPreconnected S) (hp : p ∈ S)
    {q : X} (hq : q ∈ S) {r : ℝ} (hr : 0 < r) (hle : r ≤ dist q p) :
    ∃ z ∈ S, z ∈ sphere p r := by
  obtain ⟨z, hz, hzr⟩ := hS.intermediate_value hp hq
    (continuous_id.dist continuous_const).continuousOn
    (show r ∈ Icc (dist p p) (dist q p) by simpa using And.intro hr.le hle)
  exact ⟨z, hz, hzr⟩

private lemma card_radii_eq_two_of_arcs {q₁ q₂ : V} (A : Path p q₁) (B : Path p q₂)
    (hA : Injective A) (hB : Injective B) {r : ℝ} (hr : 0 < r)
    (hrA : r ≤ dist q₁ p) (hrB : r ≤ dist q₂ p)
    (hmeet : (range A ∩ closedBall p r) ∩ (range B ∩ closedBall p r) ⊆ {p})
    {Y : Finset V} (hY : ↑Y ⊆ sphere p r)
    (hstar : closedBall p r ∩ (range A ∪ range B) = {p} ∪ ⋃ y ∈ Y, segment ℝ p y) :
    Y.card = 2 := by
  classical
  have hsection := coe_eq_sphere_inter_of_star hr hY hstar
  have hseg (y : V) (hy : y ∈ Y) : segment ℝ p y ⊆ range A ∪ range B := by
    intro z hz
    exact (show z ∈ closedBall p r ∩ (range A ∪ range B) from
      hstar ▸ Or.inr (mem_iUnion₂.mpr ⟨y, hy, hz⟩)).2
  have hsplit (y : V) (hy : y ∈ Y) :
      segment ℝ p y ⊆ range A ∨ segment ℝ p y ⊆ range B := by
    have hb : segment ℝ p y ⊆ closedBall p r :=
      (convex_closedBall p r).segment_subset (mem_closedBall_self hr.le)
        (sphere_subset_closedBall (hY hy))
    exact (segment_subset_or_of_inter_subset_singleton
      ((isCompact_range A.continuous).isClosed.inter isClosed_closedBall)
      ((isCompact_range B.continuous).isClosed.inter isClosed_closedBall) hmeet
      (ne_of_mem_sphere (hY hy) hr.ne').symm
      (fun z hz ↦ (hseg y hy hz).elim (fun h ↦ Or.inl ⟨h, hb hz⟩)
        (fun h ↦ Or.inr ⟨h, hb hz⟩))).imp
      (fun h ↦ h.trans inter_subset_left) (fun h ↦ h.trans inter_subset_left)
  have hside (y : V) (hy : y ∈ Y) (hyA : y ∈ range A) : segment ℝ p y ⊆ range A := by
    obtain h | h := hsplit y hy
    · exact h
    exact ((ne_of_mem_sphere (hY hy) hr.ne') (hmeet
      ⟨⟨hyA, sphere_subset_closedBall (hY hy)⟩,
        h (right_mem_segment ..), sphere_subset_closedBall (hY hy)⟩)).elim
  obtain ⟨u, huA, husph⟩ := exists_sphere_point A.range_isPathConnected.isConnected.isPreconnected
    A.source_mem_range A.target_mem_range hr hrA
  obtain ⟨v, hvB, hvsph⟩ := exists_sphere_point B.range_isPathConnected.isConnected.isPreconnected
    B.source_mem_range B.target_mem_range hr hrB
  have huY : u ∈ Y := by
    change u ∈ (Y : Set V)
    rw [hsection]
    exact ⟨husph, Or.inl huA⟩
  have hvY : v ∈ Y := by
    change v ∈ (Y : Set V)
    rw [hsection]
    exact ⟨hvsph, Or.inr hvB⟩
  have huv : u ≠ v := by
    rintro rfl
    exact ne_of_mem_sphere husph hr.ne' (hmeet
      ⟨⟨huA, sphere_subset_closedBall husph⟩, hvB, sphere_subset_closedBall husph⟩)
  have hvseg : segment ℝ p v ⊆ range B := by
    obtain h | h := hsplit v hvY
    · exact ((ne_of_mem_sphere hvsph hr.ne') (hmeet
        ⟨⟨h (right_mem_segment ..), sphere_subset_closedBall hvsph⟩,
          hvB, sphere_subset_closedBall hvsph⟩)).elim
    exact h
  refine Finset.card_eq_two.mpr ⟨u, v, huv, Finset.ext fun y ↦ ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun hy ↦ ?_, fun h ↦ h.elim (fun h ↦ h ▸ huY) (fun h ↦ h ▸ hvY)⟩
  exact (hsplit y hy).imp
    (fun h ↦ radii_eq_of_injective hA hr (hY hy) husph h (hside u huY huA))
    (fun h ↦ radii_eq_of_injective hB hr (hY hy) hvsph h hvseg)

private lemma exists_star_one (hL : IsPrimitiveLink L a b) (hab : a ≠ b)
    (hpoly : IsSegmentFigure L) :
    ∃ r > 0, ∃ Y : Finset V, Y.card = 1 ∧ ↑Y ⊆ sphere a r ∧
      closedBall a r ∩ L = {a} ∪ ⋃ y ∈ Y, segment ℝ a y := by
  obtain ⟨γ, hγ, rfl⟩ := hL
  obtain ⟨r₀, hr₀, Y₀, hY₀, hstar₀⟩ := hpoly.exists_radius γ.source_mem_range
  let r := min r₀ (dist b a)
  have hr : 0 < r := lt_min hr₀ (dist_pos.mpr hab.symm)
  obtain ⟨Y, hY, -, hstar⟩ := exists_radius_of_le hr₀ hY₀ hstar₀ hr (min_le_left ..)
  obtain ⟨u, hu, husph⟩ := exists_sphere_point γ.range_isPathConnected.isConnected.isPreconnected
    γ.source_mem_range γ.target_mem_range hr (min_le_right ..)
  have hsection := coe_eq_sphere_inter_of_star hr hY hstar
  have huY : u ∈ Y := by
    change u ∈ (Y : Set V)
    rw [hsection]
    exact ⟨husph, hu⟩
  have hseg (y : V) (hy : y ∈ Y) : segment ℝ a y ⊆ range γ := by
    intro z hz
    exact (show z ∈ closedBall a r ∩ range γ from
      hstar ▸ Or.inr (mem_iUnion₂.mpr ⟨y, hy, hz⟩)).2
  refine ⟨r, hr, Y, Finset.card_eq_one_iff_existsUnique.mpr ⟨u, huY, ?_⟩, hY, hstar⟩
  exact fun y hy ↦ radii_eq_of_injective (hγ.injective hab) hr (hY hy) husph
    (hseg y hy) (hseg u huY)

private lemma exists_star_two_interior (hL : IsPrimitiveLink L a b)
    (hpoly : IsSegmentFigure L) (hp : p ∈ L \ {a, b}) :
    ∃ r > 0, ∃ Y : Finset V, Y.card = 2 ∧ ↑Y ⊆ sphere p r ∧
      closedBall p r ∩ L = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  obtain ⟨γ, hγ, rfl⟩ := hL
  obtain ⟨t, rfl⟩ := hp.1
  have hpa : γ t ≠ a := fun h ↦ hp.2 (Or.inl h)
  have hpb : γ t ≠ b := fun h ↦ hp.2 (Or.inr h)
  let A := (γ.subpath t 0).cast rfl γ.source.symm
  let B := (γ.subpath t 1).cast rfl γ.target.symm
  have hA : Injective A := hγ.injective_subpath (by simpa using hpa)
  have hB : Injective B := hγ.injective_subpath (by simpa using hpb)
  have hArange : range A = range (γ.subpath 0 t) := by
    simp only [A, Path.cast_coe, Path.range_subpath]
    rw [uIcc_comm]
  have hunion : range A ∪ range B = range γ := by
    rw [hArange]
    simp only [B, Path.cast_coe]
    rw [γ.range_subpath_of_le 0 t t.prop.1, γ.range_subpath_of_le t 1 t.prop.2,
      ← image_union, Icc_union_Icc_eq_Icc (show (0 : I) ≤ t from t.prop.1)
        (show t ≤ (1 : I) from t.prop.2), unitInterval.Icc_eq_univ, image_univ]
  obtain ⟨r₀, hr₀, Y₀, hY₀, hstar₀⟩ := hpoly.exists_radius (mem_range_self t)
  let r := min r₀ (min (dist a (γ t)) (dist b (γ t)) / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos
    (lt_min (dist_pos.mpr hpa.symm) (dist_pos.mpr hpb.symm)))
  have hra : r < dist a (γ t) :=
    (min_le_right ..).trans_lt
      ((div_le_div_of_nonneg_right (min_le_left ..) (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
        (half_lt_self (dist_pos.mpr hpa.symm)))
  have hrb : r ≤ dist b (γ t) := (min_le_right ..).trans
    ((half_le_self (by positivity)).trans (min_le_right ..))
  obtain ⟨Y, hY, -, hstar⟩ := exists_radius_of_le hr₀ hY₀ hstar₀ hr (min_le_left ..)
  refine ⟨r, hr, Y, ?_, hY, hstar⟩
  apply card_radii_eq_two_of_arcs A B hA hB hr hra.le hrb ?_ hY (hunion ▸ hstar)
  rintro z ⟨⟨hzA, hzball⟩, hzB, -⟩
  have hz : z ∈ range (γ.subpath 0 t) ∩ range (γ.subpath t 1) := ⟨hArange ▸ hzA, hzB⟩
  rw [hγ.subpath_range_inter_subpath_range t] at hz
  obtain hz | ⟨rfl, -⟩ := hz
  · exact hz
  exact (hra.not_ge (mem_closedBall.mp hzball)).elim

private lemma exists_star_two (hL : IsPrimitiveLink L a b) (hpoly : IsSegmentFigure L)
    (hp : p ∈ L) (htwo : a = b ∨ p ∉ ({a, b} : Set V)) :
    ∃ r > 0, ∃ Y : Finset V, Y.card = 2 ∧ ↑Y ⊆ sphere p r ∧
      closedBall p r ∩ L = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  obtain rfl | hends := htwo
  · obtain ⟨hC, -⟩ := isPrimitiveLink_iff_isCircuit.mp hL
    obtain ⟨γ, hγ, hrange⟩ := isPrimitiveLink_iff_isCircuit.mpr ⟨hC, hp⟩
    have hq : γ half ∈ L := hrange ▸ mem_range_self half
    have hqne : γ half ≠ p := hγ.half_ne_source
    exact exists_star_two_interior
      (isPrimitiveLink_iff_isCircuit.mpr ⟨hC, hq⟩) hpoly ⟨hp, by simpa using hqne.symm⟩
  exact exists_star_two_interior hL hpoly ⟨hp, hends⟩

namespace IsPrimitiveLink

/-- At every point of a polygonal primitive link, all sufficiently small closed balls cut out a
star. There is one radius at either endpoint of an arc and two everywhere else. In particular,
every point of a loop has two radii, including its specified basepoint. -/
theorem exists_local_star (hL : IsPrimitiveLink L a b) (hpoly : IsSegmentFigure L) (hp : p ∈ L) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃ Y : Finset V,
      Y.card = (if a ≠ b ∧ p ∈ ({a, b} : Set V) then 1 else 2) ∧
      ↑Y ⊆ sphere p r ∧ closedBall p r ∩ L = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  classical
  suffices ∃ r₀ > 0, ∃ Y : Finset V,
      Y.card = (if a ≠ b ∧ p ∈ ({a, b} : Set V) then 1 else 2) ∧
      ↑Y ⊆ sphere p r₀ ∧ closedBall p r₀ ∩ L = {p} ∪ ⋃ y ∈ Y, segment ℝ p y by
    obtain ⟨r₀, hr₀, Y, hcard, hY, hstar⟩ := this
    refine ⟨r₀, hr₀, fun r hr hle ↦ ?_⟩
    obtain ⟨Y', hY', hcard', hstar'⟩ := exists_radius_of_le hr₀ hY hstar hr hle
    exact ⟨Y', hcard'.trans hcard, hY', hstar'⟩
  split_ifs with h
  · obtain ⟨hab, rfl | rfl⟩ := h
    · exact exists_star_one hL hab hpoly
    exact exists_star_one hL.symm hab.symm hpoly
  apply exists_star_two hL hpoly hp
  tauto

/-- Every sufficiently small closed ball about an arc endpoint meets the link in exactly one
radius. The endpoint on the sphere is unique. -/
theorem exists_local_star_one (hL : IsPrimitiveLink L a b) (hab : a ≠ b)
    (hpoly : IsSegmentFigure L) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃! y,
      y ∈ sphere a r ∧ closedBall a r ∩ L = segment ℝ a y := by
  classical
  obtain ⟨r₀, hr₀, hstar⟩ := hL.exists_local_star hpoly hL.left_mem
  refine ⟨r₀, hr₀, fun r hr hle ↦ ?_⟩
  obtain ⟨Y, hcard, hY, heq⟩ := hstar r hr hle
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (by simpa [hab] using hcard)
  have hy : y ∈ sphere a r := hY (Finset.mem_singleton_self y)
  have heq' : closedBall a r ∩ L = segment ℝ a y := by
    simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left, singleton_union,
      insert_eq_of_mem (left_mem_segment ℝ a y)] using heq
  refine ⟨y, ⟨hy, heq'⟩, fun z ⟨hz, hzseg⟩ ↦ ?_⟩
  exact eq_of_mem_segment_of_mem_sphere a hr hy
    (heq' ▸ (hzseg.symm ▸ right_mem_segment ℝ a z)) hz

/-- Every sufficiently small closed ball about a nonendpoint point, or any point of a loop,
meets a polygonal primitive link in exactly two radii. -/
theorem exists_local_star_two (hL : IsPrimitiveLink L a b) (hpoly : IsSegmentFigure L)
    (hp : p ∈ L) (htwo : a = b ∨ p ∉ ({a, b} : Set V)) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∃ Y : Finset V, Y.card = 2 ∧
      ↑Y ⊆ sphere p r ∧ closedBall p r ∩ L = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  obtain ⟨r₀, hr₀, hstar⟩ := hL.exists_local_star hpoly hp
  refine ⟨r₀, hr₀, fun r hr hle ↦ ?_⟩
  have h : ¬ (a ≠ b ∧ p ∈ ({a, b} : Set V)) := by tauto
  simpa only [ite_eq_right h] using hstar r hr hle

/-- The two-radius neighborhood can be chosen below any prescribed positive scale. -/
theorem exists_local_star_two_le (hL : IsPrimitiveLink L a b) (hpoly : IsSegmentFigure L)
    (hp : p ∈ L) (htwo : a = b ∨ p ∉ ({a, b} : Set V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r ≤ ε ∧ ∃ Y : Finset V, Y.card = 2 ∧ ↑Y ⊆ sphere p r ∧
      closedBall p r ∩ L = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  obtain ⟨r₀, hr₀, hstar⟩ := hL.exists_local_star_two hpoly hp htwo
  exact ⟨min ε r₀, lt_min hε hr₀, min_le_left ..,
    hstar _ (lt_min hε hr₀) (min_le_right ..)⟩

end IsPrimitiveLink
