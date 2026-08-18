module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Analysis.Convex.PathConnected

/-!
# A disk with finitely many radii removed

Removing the radii from an open disk in a real inner product plane produces one open connected
sector between each pair of consecutive radii. A point in the relative interior of a removed radius
is in the closure of exactly the two adjacent sectors. The sectors are represented as connected
components of the complement, so their openness, connectedness, and incidence properties can be
stated directly.

## Main definitions

* `sectors x ρ Y` : the connected components of the disk minus the radii, as a set of subsets.

## Main statements

* `ncard_sectors` : there are exactly `Y.card` of them.
* `isOpen_of_mem_sectors`, `isConnected_of_mem_sectors`
* `ncard_sectors_closure_eq_two` : a point interior to a radius lies in the closure of exactly two.

The proof uses polar coordinates after identifying the plane with `ℂ` along an orthonormal basis.
The angular bookkeeping is private; the public API uses only `diskMinusRadii` and `sectors`.
-/

@[expose] public section

open Set Metric Complex Real Function

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The disk of radius `ρ` about `x` with the radii to the points of `Y` removed. -/
def diskMinusRadii (x : V) (ρ : ℝ) (Y : Finset V) : Set V :=
  ball x ρ \ ⋃ y ∈ Y, segment ℝ x y

/-- The sectors: the connected components of `diskMinusRadii`, represented as a set of subsets. -/
def sectors (x : V) (ρ : ℝ) (Y : Finset V) : Set (Set V) :=
  (fun p ↦ connectedComponentIn (diskMinusRadii x ρ Y) p) '' diskMinusRadii x ρ Y

variable {x : V} {ρ : ℝ} {Y : Finset V} {C : Set V} {p : V}

@[simp]
theorem mem_diskMinusRadii : p ∈ diskMinusRadii x ρ Y ↔ p ∈ ball x ρ ∧ p ∉ ⋃ y ∈ Y, segment ℝ x y :=
  Iff.rfl

@[grind →]
theorem subset_diskMinusRadii_of_mem_sectors (hC : C ∈ sectors x ρ Y) :
    C ⊆ diskMinusRadii x ρ Y := by
  obtain ⟨_, _, rfl⟩ := hC
  exact connectedComponentIn_subset ..

@[grind .]
theorem isOpen_diskMinusRadii : IsOpen (diskMinusRadii x ρ Y) :=
  isOpen_ball.sdiff <| Y.finite_toSet.isClosed_biUnion fun _ _ ↦
    closure_openSegment (𝕜 := ℝ) x _ ▸ isClosed_closure

/-- Each sector is open: `diskMinusRadii` is open and the plane is locally connected. -/
@[grind →]
theorem isOpen_of_mem_sectors (hC : C ∈ sectors x ρ Y) : IsOpen C := by
  obtain ⟨_, _, rfl⟩ := hC
  exact isOpen_diskMinusRadii.connectedComponentIn

@[grind →]
theorem isConnected_of_mem_sectors (hC : C ∈ sectors x ρ Y) : IsConnected C := by
  obtain ⟨_, hp, rfl⟩ := hC
  exact isConnected_connectedComponentIn_iff.mpr hp

/-- Distinct sectors are disjoint, and they cover the punctured disk. -/
@[grind =]
theorem sUnion_sectors : ⋃₀ sectors x ρ Y = diskMinusRadii x ρ Y :=
  (sUnion_subset fun _ ↦ subset_diskMinusRadii_of_mem_sectors).antisymm fun _ hp ↦
    mem_sUnion.mpr ⟨_, mem_image_of_mem _ hp, mem_connectedComponentIn hp⟩

theorem pairwiseDisjoint_sectors : (sectors x ρ Y).PairwiseDisjoint id := by
  rintro _ ⟨p, _, rfl⟩ _ ⟨q, _, rfl⟩ hpq
  exact disjoint_left.2 fun _ hp hq ↦
    hpq <| (connectedComponentIn_eq hp).trans (connectedComponentIn_eq hq).symm

/-! ### Private polar helpers -/

variable [Fact (Module.finrank ℝ V = 2)]

/-- A distance-preserving identification of the plane with `ℂ`, along an arbitrary orthonormal
basis. Every statement this file exports is invariant under it — only the `private` angular
bookkeeping below sees the choice — so no orientation is asked for and none is needed. -/
private noncomputable def toPlane : ℂ ≃ₗᵢ[ℝ] V :=
  Complex.isometryOfOrthonormal <| (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)

private noncomputable def toComplex (x p : V) : ℂ :=
  toPlane.symm (p - x)

private noncomputable def polar (x : V) (s θ : ℝ) : V :=
  x + toPlane (↑s * cexp (↑θ * I))

private lemma toComplex_polar (x : V) (s θ : ℝ) :
    toComplex x (polar x s θ) = ↑s * cexp (↑θ * I) := by
  simp [toComplex, polar]

private lemma toComplex_eq_zero {x p : V} : toComplex x p = 0 ↔ p = x := by
  rw [toComplex, LinearIsometryEquiv.map_eq_zero_iff, sub_eq_zero]

private lemma norm_toComplex (x p : V) : ‖toComplex x p‖ = ‖p - x‖ :=
  LinearIsometryEquiv.norm_map ..

private lemma dist_polar (x : V) (s θ : ℝ) : dist (polar x s θ) x = |s| := by
  rw [dist_eq_norm_sub, polar, add_sub_cancel_left, LinearIsometryEquiv.norm_map, norm_mul,
    norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs]

private lemma continuous_uncurry_polar (x : V) :
    Continuous (uncurry (polar x)) := by
  unfold polar uncurry
  fun_prop

private lemma polar_of_toComplex {x p : V} :
    polar x ‖toComplex x p‖ (arg (toComplex x p)) = p := by
  unfold polar
  have h := norm_mul_exp_arg_mul_I (toComplex x p)
  simp only [toComplex] at h ⊢
  rw [h, LinearIsometryEquiv.apply_symm_apply, add_sub_cancel]

private lemma polar_add_two_pi (x : V) (s θ : ℝ) :
    polar x s (θ + 2 * π) = polar x s θ := by
  unfold polar
  congr 1
  rw [ofReal_add, add_mul, Complex.exp_add]
  have : cexp (↑(2 * π) * I) = 1 := by
    convert Complex.exp_two_pi_mul_I
    push_cast
    ring
  rw [this, mul_one]

private lemma sameRay_toComplex_iff {x p q : V} :
    SameRay ℝ (toComplex x p) (toComplex x q) ↔ SameRay ℝ (p - x) (q - x) := by
  simpa [toComplex] using (SameRay.sameRay_map_iff (toPlane.symm : V ≃ₗᵢ[ℝ] ℂ).toLinearEquiv
    (x := p - x) (y := q - x))

private lemma polar_eq_iff_angle {s θ₁ θ₂ : ℝ} (hs : 0 < s) :
    polar x s θ₁ = polar x s θ₂ ↔ ∃ n : ℤ, θ₁ = θ₂ + (n : ℝ) * (2 * π) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hexp : cexp (↑θ₁ * I) = cexp (↑θ₂ * I) := mul_left_cancel₀ (ofReal_ne_zero.mpr hs.ne') <|
      by simpa [toComplex_polar] using congrArg (toComplex x) h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨n, ?_⟩
    exact_mod_cast mul_right_cancel₀ I_ne_zero (show (θ₁ : ℂ) * I = (θ₂ + n * (2 * π)) * I by grind)
  rintro ⟨n, rfl⟩
  unfold polar
  congr 1
  rw [ofReal_add, add_mul, Complex.exp_add]
  congr 2
  nth_rw 2 [Complex.exp_eq_one_iff.mpr ⟨n, by
    push_cast
    ring⟩]
  exact mul_one ..

private lemma polar_inj {s₁ s₂ θ₁ θ₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hθ : |θ₁ - θ₂| < 2 * π)
    (h : polar x s₁ θ₁ = polar x s₂ θ₂) : s₁ = s₂ ∧ θ₁ = θ₂ := by
  obtain rfl : s₁ = s₂ := by
    simpa [dist_polar, abs_of_pos hs₁, abs_of_pos hs₂] using congrArg (dist · x) h
  refine ⟨rfl, ?_⟩
  obtain ⟨n, hn⟩ := (polar_eq_iff_angle hs₁).mp h
  obtain rfl : n = 0 :=
    have : |(n : ℝ)| * (2 * π) < 1 * (2 * π) := by
      simpa [hn, abs_mul, abs_of_pos Real.two_pi_pos] using hθ
    Int.abs_lt_one_iff.mp (by exact_mod_cast (mul_lt_mul_iff_of_pos_right Real.two_pi_pos).mp this)
  simpa using hn

private noncomputable def argFinset (x : V) (Y : Finset V) : Finset ℝ :=
  Y.image fun y ↦ arg (toComplex x y)

private noncomputable def argList (x : V) (Y : Finset V) : List ℝ :=
  (argFinset x Y).sort (· ≤ ·)

private lemma injOn_arg_of_mem_sphere (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) :
    InjOn (fun y ↦ arg (toComplex x y)) (Y : Set _) := by
  intro y₁ hy₁ y₂ hy₂ harg
  have heq : ‖y₁ - x‖ • (y₂ - x) = ‖y₂ - x‖ • (y₁ - x) := sameRay_iff_norm_smul_eq.mp
    (sameRay_toComplex_iff.mp (sameRay_of_arg_eq harg))
  rw [(mem_sphere_iff_norm.mp (hY hy₁)), (mem_sphere_iff_norm.mp (hY hy₂))] at heq
  have : y₂ - y₁ = 0 := by
    have h : y₂ - y₁ = (y₂ - x) - (y₁ - x) := by abel
    rw [h, (smul_right_injective V hρ.ne' heq), sub_self]
  exact (sub_eq_zero.mp this).symm

private lemma card_argFinset (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) : (argFinset x Y).card = Y.card :=
  Finset.card_image_of_injOn (injOn_arg_of_mem_sphere hρ hY)

private lemma length_argList (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) :
    (argList x Y).length = Y.card := by
  simp [argList, Finset.length_sort, card_argFinset hρ hY]

private lemma argList_get_lt {i j : Fin (argList x Y).length} (hij : i < j) :
    (argList x Y).get i < (argList x Y).get j := by
  exact ((argFinset x Y |>.pairwise_sort _).rel_get_of_lt hij).lt_of_ne (fun h ↦ (hij.ne)
    ((argFinset x Y |>.sort_nodup _).get_inj_iff.mp h))

private lemma argList_get_mem_Ioc (i : Fin (argList x Y).length) :
    (argList x Y).get i ∈ Ioc (-π) π := by
  obtain ⟨y, -, hy⟩ :=
    Finset.mem_image.mp ((Finset.mem_sort (· ≤ ·)).mp <| List.get_mem (argList x Y) i)
  exact hy ▸ arg_mem_Ioc _

private noncomputable def openSector (x : V) (ρ θ₁ θ₂ : ℝ) : Set V :=
  (fun p : ℝ × ℝ ↦ polar x p.1 p.2) '' (Ioo 0 ρ ×ˢ Ioo θ₁ θ₂)

private noncomputable def θLeft (x : V) (Y : Finset V) (i : Fin (argList x Y).length) : ℝ :=
  (argList x Y).get i

private noncomputable def θRight (x : V) (Y : Finset V) (i : Fin (argList x Y).length) : ℝ :=
  if h : ↑i + 1 < (argList x Y).length then (argList x Y).get ⟨↑i + 1, h⟩
  else (argList x Y).get ⟨0, i.pos⟩ + 2 * π

private noncomputable def openSectorIdx (x : V) (ρ : ℝ) (Y : Finset V)
    (i : Fin (argList x Y).length) : Set V :=
  openSector x ρ (θLeft x Y i) (θRight x Y i)

private lemma θLeft_lt_θRight (i : Fin (argList x Y).length) : θLeft x Y i < θRight x Y i := by
  simp only [θLeft, θRight]
  split_ifs with h
  · exact argList_get_lt (show (i : ℕ) < i + 1 from Nat.lt_succ_self _)
  linarith [(argList_get_mem_Ioc (x := x) (Y := Y) i).2, (argList_get_mem_Ioc ⟨0, i.pos⟩).1]

omit [Fact (Module.finrank ℝ V = 2)] in
private lemma lineMap_sub_left {t : ℝ} {a b : V} :
    AffineMap.lineMap a b t - a = t • (b - a) := by
  simp [AffineMap.lineMap_apply]

private lemma mem_segment_iff_arg (hρ : 0 < ρ) {y p : V}
    (hy : y ∈ sphere x ρ) (hp : p ∈ ball x ρ) :
    p ∈ segment ℝ x y ↔ p = x ∨ arg (toComplex x p) = arg (toComplex x y) := by
  have hnormy : ‖y - x‖ = ρ := mem_sphere_iff_norm.mp hy
  have hyx : y ≠ x := by
    intro h
    have : ‖y - x‖ = 0 := by simp [h]
    exact hρ.ne' (hnormy.symm.trans this)
  refine ⟨fun hseg ↦ (eq_or_ne p x).imp id fun hpx ↦ ?_, fun h ↦ ?_⟩
  · rw [segment_eq_image_lineMap] at hseg
    obtain ⟨t, ht, rfl⟩ := hseg
    have hsr : SameRay ℝ (AffineMap.lineMap x y t - x) (y - x) :=
      (lineMap_sub_left (t := t) (a := x) (b := y)).symm ▸
        SameRay.sameRay_nonneg_smul_left _ ht.1
    exact (Complex.sameRay_iff.mp (sameRay_toComplex_iff.mpr hsr)).resolve_left
      (mt toComplex_eq_zero.mp hpx) |>.resolve_left (mt toComplex_eq_zero.mp hyx)
  obtain rfl | harg := h
  · exact left_mem_segment ..
  obtain rfl | hpx := eq_or_ne p x
  · exact left_mem_segment ..
  have hsr : SameRay ℝ (p - x) (y - x) := sameRay_toComplex_iff.mp (sameRay_of_arg_eq harg)
  obtain ⟨r, hr0, hr⟩ := hsr.exists_nonneg_right (sub_ne_zero.mpr hyx)
  have hr_eq : r = ‖p - x‖ / ρ := by
    have : ‖p - x‖ = r * ρ := by
      rw [hr, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, hnormy]
    field_simp [hρ.ne']
    linarith
  have ht : r ∈ Icc (0 : ℝ) 1 := by
    refine ⟨hr0, ?_⟩
    rw [hr_eq, div_le_one hρ]
    exact (mem_ball_iff_norm.mp hp).le
  have : p = AffineMap.lineMap x y r := by
    apply eq_of_sub_eq_zero
    calc
      p - AffineMap.lineMap x y r
          = (p - x) - (AffineMap.lineMap x y r - x) := by abel
        _ = r • (y - x) - r • (y - x) := by rw [hr, lineMap_sub_left]
        _ = 0 := by rw [sub_self]
  exact this.symm ▸ lineMap_mem_segment ℝ x y ht


omit [Fact (Module.finrank ℝ V = 2)] in
private lemma ne_center_of_mem_diskMinusRadii (hYne : Y.Nonempty) {p : V}
    (hp : p ∈ diskMinusRadii x ρ Y) : p ≠ x := by
  intro rfl
  obtain ⟨y, hy⟩ := hYne
  exact hp.2 <| mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, left_mem_segment ..⟩⟩

private lemma mem_diskMinusRadii_iff (hρ : 0 < ρ) (hYne : Y.Nonempty) (hY : ↑Y ⊆ sphere x ρ)
    {p : V} : p ∈ diskMinusRadii x ρ Y ↔
      p ∈ ball x ρ ∧ p ≠ x ∧ arg (toComplex x p) ∉ argFinset x Y := by
  refine ⟨fun hp ↦ ⟨hp.1, ne_center_of_mem_diskMinusRadii hYne hp, fun harg ↦ ?_⟩, fun ⟨hp,
    hpx, harg⟩ ↦ ⟨hp, fun h ↦ ?_⟩⟩
  obtain ⟨y, hyY, hy⟩ := Finset.mem_image.mp harg
  have hseg : p ∈ segment ℝ x y := (mem_segment_iff_arg hρ (hY hyY) hp.1).mpr (Or.inr hy.symm)
  exact hp.2 (mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hyY, hseg⟩⟩)
  obtain ⟨y, hy⟩ := mem_iUnion.mp h
  obtain ⟨hyY, hseg⟩ := mem_iUnion.mp hy
  obtain heq | harg' := (mem_segment_iff_arg hρ (hY hyY) hp).mp hseg
  · exact hpx heq
  exact harg (Finset.mem_image.mpr ⟨y, hyY, harg'.symm⟩)

private lemma isPathConnected_openSector {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) (hθ : θ₁ < θ₂) :
    IsPathConnected (openSector x ρ θ₁ θ₂) := by
  have hrect : IsPathConnected (Ioo (0 : ℝ) ρ ×ˢ Ioo θ₁ θ₂) :=
    ((convex_Ioo (0 : ℝ) ρ).isPathConnected (nonempty_Ioo.mpr hρ)).prod
      ((convex_Ioo θ₁ θ₂).isPathConnected (nonempty_Ioo.mpr hθ))
  simpa [openSector] using hrect.image (continuous_uncurry_polar x)

private lemma ofReal_mul_exp_eq {s θ : ℝ} (hs : 0 < s) :
    (↑s : ℂ) * cexp (↑θ * I) = cexp (↑(Real.log s) + ↑θ * I) := by
  rw [← Complex.exp_log (ofReal_ne_zero.mpr hs.ne'), ← Complex.exp_add, ← ofReal_log hs.le]

private lemma isOpen_image_mul_exp {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) :
    IsOpen ((fun p : ℝ × ℝ ↦ (↑p.1 : ℂ) * cexp (↑p.2 * I)) '' (Ioo 0 ρ ×ˢ Ioo θ₁ θ₂)) := by
  let rect : Set (ℝ × ℝ) := Ioo 0 ρ ×ˢ Ioo θ₁ θ₂
  let L : ℝ × ℝ → ℂ := fun p ↦ ↑(Real.log p.1) + ↑p.2 * I
  have hform : (fun p : ℝ × ℝ ↦ (↑p.1 : ℂ) * cexp (↑p.2 * I)) '' rect = cexp '' (L '' rect) := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨p, hmem, rfl⟩
      exact ⟨L p, ⟨p, hmem, rfl⟩, (ofReal_mul_exp_eq hmem.1.1).symm⟩
    rintro ⟨w, ⟨p, hmem, rfl⟩, rfl⟩
    exact ⟨p, hmem, ofReal_mul_exp_eq hmem.1.1⟩
  rw [hform]
  refine isOpenMap_exp _ ?_
  let φ : ℝ × ℝ → ℝ × ℝ := fun p ↦ (Real.log p.1, p.2)
  have hLφ : L = equivRealProd.symm ∘ φ := by
    ext p
    change ↑(Real.log p.1) + ↑p.2 * I = equivRealProd.symm (Real.log p.1, p.2)
    simp [equivRealProd_symm_apply]
  have hφim : φ '' rect = Iio (Real.log ρ) ×ˢ Ioo θ₁ θ₂ := by
    ext q
    refine ⟨?_, ?_⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Real.log_lt_log hp.1.1 hp.1.2, hp.2⟩
    refine fun hq ↦ ⟨(rexp q.1, q.2), ⟨⟨exp_pos _, (Real.lt_log_iff_exp_lt hρ).mp hq.1⟩, hq.2⟩, ?_⟩
    simp [φ, Real.log_exp]
  rw [hLφ, image_comp]
  exact equivRealProdCLM.symm.isOpenMap _ ((hφim.symm ▸ isOpen_Iio.prod isOpen_Ioo))

private lemma isOpen_openSector {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) : IsOpen (openSector x ρ θ₁ θ₂) := by
  have him : openSector x ρ θ₁ θ₂ = (fun z : ℂ ↦ x + toPlane z) ''
        ((fun p : ℝ × ℝ ↦ (↑p.1 : ℂ) * cexp (↑p.2 * I)) '' (Ioo 0 ρ ×ˢ Ioo θ₁ θ₂)) := by
    simp only [openSector, ← image_comp]
    rfl
  rw [him]
  let e : ℂ ≃ₜ V :=
    toPlane.toHomeomorph.trans (Homeomorph.addLeft x)
  exact e.isOpenMap _ (isOpen_image_mul_exp (θ₁ := θ₁) (θ₂ := θ₂) hρ)

private lemma arg_polar {s θ : ℝ} (hs : 0 < s) :
    arg (toComplex x (polar x s θ)) = toIocMod two_pi_pos (-π) θ := by
  rw [toComplex_polar, arg_real_mul _ hs, arg_exp_mul_I]

private lemma toIocMod_eq_of_mem_Ioc {θ : ℝ} (h : θ ∈ Ioc (-π) π) :
    toIocMod two_pi_pos (-π) θ = θ :=
  (toIocMod_eq_self two_pi_pos).mpr (by simpa [two_mul] using h)

private lemma nonempty_openSectorIdx (hρ : 0 < ρ) (i : Fin (argList x Y).length) :
    (openSectorIdx x ρ Y i).Nonempty :=
  (isPathConnected_openSector hρ (θLeft_lt_θRight i)).nonempty

private lemma arg_mem_argFinset_iff {θ : ℝ} :
    θ ∈ argFinset x Y ↔ ∃ i : Fin (argList x Y).length, (argList x Y).get i = θ := by
  refine ⟨fun hθ ↦ ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := List.mem_iff_get.mp ((Finset.mem_sort (· ≤ ·)).mpr hθ)
    exact ⟨n, rfl⟩
  rintro ⟨i, rfl⟩
  exact (Finset.mem_sort (· ≤ ·)).mp <| List.get_mem (argList x Y) i

private lemma argList_get_le_of_le {i j : Fin (argList x Y).length} (hij : i ≤ j) :
    (argList x Y).get i ≤ (argList x Y).get j :=
  (argFinset x Y |>.pairwise_sort _).rel_get_of_le hij

private lemma argList_get_min (i : Fin (argList x Y).length) :
    (argList x Y).get ⟨0, i.pos⟩ ≤ (argList x Y).get i :=
  argList_get_le_of_le (Fin.le_iff_val_le_val.mpr (Nat.zero_le (i : ℕ)))

private lemma argList_get_max (i : Fin (argList x Y).length) (hi : ¬ ↑i + 1 < (argList x Y).length)
    (k : Fin (argList x Y).length) : (argList x Y).get k ≤ (argList x Y).get i := by
  exact argList_get_le_of_le (Fin.mk_le_mk.mpr (by omega))

private lemma toIocMod_not_mem_argFinset (i : Fin (argList x Y).length) {θ : ℝ}
    (hθ : θ ∈ Ioo (θLeft x Y i) (θRight x Y i)) : toIocMod two_pi_pos (-π) θ ∉ argFinset x Y := by
  intro hmem
  obtain ⟨j, hj⟩ := (arg_mem_argFinset_iff (x := x) (Y := Y)).mp hmem
  simp only [θLeft, θRight] at hθ
  split_ifs at hθ with hi
  · have hioc : θ ∈ Ioc (-π) π := ⟨lt_trans (argList_get_mem_Ioc (x := x) (Y := Y) i).1 hθ.1,
    le_of_lt (lt_of_lt_of_le hθ.2 (argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑i + 1, hi⟩).2)⟩
    have hmod : θ = (argList x Y).get j := by
      rw [toIocMod_eq_of_mem_Ioc hioc] at hj
      exact hj.symm
    obtain hji | hji := em ((i : ℕ) < (j : ℕ))
    · exact (not_le_of_gt hθ.2) <| (argList_get_le_of_le (Fin.mk_le_mk.mpr (by omega))).trans_eq
        hmod.symm
    exact (not_le_of_gt hθ.1) <| hmod ▸ argList_get_le_of_le
      (Fin.mk_le_mk.mpr (Nat.le_of_not_gt hji))
  obtain hπ | hπ := em (θ ≤ π)
  · have hioc : θ ∈ Ioc (-π) π := ⟨lt_trans (argList_get_mem_Ioc (x := x) (Y := Y) i).1 hθ.1, hπ⟩
    have hmod : θ = (argList x Y).get j := by
      rw [toIocMod_eq_of_mem_Ioc hioc] at hj
      exact hj.symm
    exact (not_le_of_gt hθ.1) <| hmod ▸ argList_get_max i hi j
  push Not at hπ
  have hmem' : θ - 2 * π ∈ Ioc (-π) π :=
    ⟨by linarith, by linarith [hθ.2, (argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, i.pos⟩).2]⟩
  have hsub : toIocMod two_pi_pos (-π) θ = θ - 2 * π := by
    simpa [toIocMod_sub] using toIocMod_eq_of_mem_Ioc hmem'
  have hmod : θ - 2 * π = (argList x Y).get j := by
    rw [hsub] at hj
    exact hj.symm
  exact (not_le_of_gt (show θ - 2 * π < (argList x Y).get ⟨0, i.pos⟩ by linarith [hθ.2])) <|
    hmod ▸ argList_get_min j

private lemma subset_diskMinusRadii_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) (i : Fin (argList x Y).length) :
    openSectorIdx x ρ Y i ⊆ diskMinusRadii x ρ Y := by
  rintro p ⟨⟨s, θ⟩, ⟨hs, hθ⟩, rfl⟩
  have hs0 : 0 < s := hs.1
  have hball : polar x s θ ∈ ball x ρ := by
    rw [mem_ball, dist_polar, abs_of_pos hs0]
    exact hs.2
  have hne : polar x s θ ≠ x := by
    intro h
    simpa [dist_polar, abs_of_pos hs0, hs0.ne'] using (congrArg (dist · x) h)
  refine (mem_diskMinusRadii_iff hρ hYne hY).mpr ⟨hball, hne, ?_⟩
  simpa [arg_polar hs0] using toIocMod_not_mem_argFinset i hθ

private lemma mem_sector_angles_subset {i : Fin (argList x Y).length} {θ : ℝ}
    (hθ : θ ∈ Ioo (θLeft x Y i) (θRight x Y i)) :
    θ ∈ Ioo ((argList x Y).get ⟨0, i.pos⟩) ((argList x Y).get ⟨0, i.pos⟩ + 2 * π) := by
  refine ⟨(argList_get_min i).trans_lt hθ.1, ?_⟩
  simp only [θLeft, θRight] at hθ
  split_ifs at hθ with hi
  · linarith [hθ.2, (argList_get_min ⟨↑i + 1, hi⟩), (argList_get_mem_Ioc ⟨↑i + 1, hi⟩).2,
    (argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, i.pos⟩).1]
  exact hθ.2

private lemma abs_sub_lt_two_pi_of_mem_sector {i j : Fin (argList x Y).length} {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ Ioo (θLeft x Y i) (θRight x Y i)) (hθ₂ : θ₂ ∈ Ioo (θLeft x Y j) (θRight x Y j)) :
    |θ₁ - θ₂| < 2 * π := by
  have h2 := mem_sector_angles_subset (i := j) hθ₂
  have hbase : (argList x Y).get ⟨0, i.pos⟩ = (argList x Y).get ⟨0, j.pos⟩ := rfl
  rw [← hbase] at h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith [(mem_sector_angles_subset hθ₁).1, (mem_sector_angles_subset hθ₁).2,
    h2.1, h2.2]

private lemma disjoint_Ioo_θ (i j : Fin (argList x Y).length) (hij : i ≠ j) :
    Disjoint (Ioo (θLeft x Y i) (θRight x Y i)) (Ioo (θLeft x Y j) (θRight x Y j)) := by
  wlog hlt : (i : ℕ) < j generalizing i j
  · grind
  refine disjoint_left.2 fun θ hθi hθj ↦ ?_
  have hchain : θRight x Y i ≤ θLeft x Y j := by
    simp only [θLeft, θRight]
    split_ifs with hi
    · exact argList_get_le_of_le (Fin.mk_le_mk.mpr (by omega))
    omega
  linarith [hθi.2, hθj.1, hchain]

private lemma pairwiseDisjoint_openSectorIdx (_hρ : 0 < ρ) :
    Pairwise (Disjoint on openSectorIdx x ρ Y) := by
  refine fun i j hij ↦ disjoint_left.2 fun p hpi hpj ↦ ?_
  obtain ⟨⟨s₁, θ₁⟩, ⟨hs₁, hθ₁⟩, rfl⟩ := hpi
  obtain ⟨⟨s₂, θ₂⟩, ⟨hs₂, hθ₂⟩, heq⟩ := hpj
  obtain ⟨_, hθ_eq⟩ := polar_inj hs₁.1 hs₂.1 (abs_sub_lt_two_pi_of_mem_sector hθ₁ hθ₂) heq.symm
  exact (disjoint_Ioo_θ i j hij).ne_of_mem hθ₁ hθ₂ hθ_eq

/-- Every point of `diskMinusRadii` lies in some polar sector. -/
private lemma exists_mem_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty) (hY : ↑Y ⊆ sphere x ρ)
    {p : V} (hp : p ∈ diskMinusRadii x ρ Y) :
    ∃ i : Fin (argList x Y).length, p ∈ openSectorIdx x ρ Y i := by
  have hp' := (mem_diskMinusRadii_iff hρ hYne hY).mp hp
  have hlen : 0 < (argList x Y).length :=
    (length_argList hρ hY).symm ▸ Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr hYne)
  set α := arg (toComplex x p)
  set r := ‖toComplex x p‖
  have hr0 : 0 < r := by
    dsimp [r]
    rw [norm_toComplex, norm_sub_pos_iff]
    exact hp'.2.1
  have hrρ : r < ρ := by
    dsimp [r]
    rw [norm_toComplex]
    exact mem_ball_iff_norm.mp hp'.1
  have hpole : p = polar x r α := polar_of_toComplex.symm
  have hαIoc : α ∈ Ioc (-π) π := arg_mem_Ioc _
  have hαn : α ∉ argFinset x Y := hp'.2.2
  let θ₀ := (argList x Y).get ⟨0, hlen⟩
  let θLast := (argList x Y).get ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen⟩
  obtain hlt0 | hlt0 := em (α < θ₀)
  · -- below minimum: wrap via α + 2π
    let i : Fin (argList x Y).length := ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen⟩
    refine ⟨i, ?_⟩
    have hi_last : ¬ ↑i + 1 < (argList x Y).length := by
      change ¬ (argList x Y).length - 1 + 1 < (argList x Y).length
      omega
    refine ⟨(r, α + 2 * π), ⟨⟨hr0, hrρ⟩, ?_⟩, ?_⟩
    · change θLeft x Y i < α + 2 * π ∧ α + 2 * π < θRight x Y i
      simp only [θLeft, θRight, hi_last, ↓reduceDIte]
      refine ⟨?_, ?_⟩
      · have : π < α + 2 * π := by linarith [hαIoc.1]
        exact lt_of_le_of_lt (argList_get_mem_Ioc (x := x) (Y := Y) i).2 this
      grind
    grind [polar_add_two_pi]
  push Not at hlt0
  obtain hgt | hgt := em (θLast < α)
  · -- above maximum: wrap with α itself
    let i : Fin (argList x Y).length := ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen⟩
    refine ⟨i, ⟨(r, α), ⟨⟨hr0, hrρ⟩, ?_⟩, hpole.symm⟩⟩
    have hi_last : ¬ ↑i + 1 < (argList x Y).length := by
      change ¬ (argList x Y).length - 1 + 1 < (argList x Y).length
      omega
    change θLeft x Y i < α ∧ α < θRight x Y i
    simp only [θLeft, θRight, hi_last, ↓reduceDIte]
    refine ⟨hgt, ?_⟩
    linarith [hαIoc.2, (argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, hlen⟩).1]
  -- between min and max: find consecutive gap
  push Not at hgt
  let S := Finset.univ.filter (fun k : Fin (argList x Y).length ↦ (argList x Y).get k < α)
  have hSne : S.Nonempty := ⟨⟨0, hlen⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (lt_of_le_of_ne hlt0 ((show α ≠ θ₀ from fun h ↦ hαn ((arg_mem_argFinset_iff).mpr
    ⟨⟨0, hlen⟩, h.symm⟩)).symm))⟩⟩
  let i := S.max' hSne
  have hiα : (argList x Y).get i < α := (Finset.mem_filter.mp (S.max'_mem hSne)).2
  have hi_not_last : ↑i + 1 < (argList x Y).length := by
    by_contra hlast
    have ival : (i : ℕ) = (argList x Y).length - 1 := by omega
    rw [show i = ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen⟩ from Fin.ext ival] at hiα
    exact not_lt_of_ge hgt hiα
  have hnext : ¬ (argList x Y).get ⟨↑i + 1, hi_not_last⟩ < α := by
    intro hlt
    exact Nat.not_succ_le_self _ <| Fin.le_iff_val_le_val.mp (S.le_max' _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
  refine ⟨i, ⟨(r, α), ⟨⟨hr0, hrρ⟩, ?_⟩, hpole.symm⟩⟩
  change θLeft x Y i < α ∧ α < θRight x Y i
  simp only [θLeft, θRight, hi_not_last, ↓reduceDIte]
  exact ⟨hiα, (lt_of_le_of_ne (le_of_not_gt hnext) fun h ↦ hαn ((arg_mem_argFinset_iff).mpr ⟨⟨↑i +
    1, hi_not_last⟩, h.symm⟩))⟩

private lemma iUnion_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty) (hY : ↑Y ⊆ sphere x ρ) :
    ⋃ i : Fin (argList x Y).length, openSectorIdx x ρ Y i = diskMinusRadii x ρ Y := by
  ext p
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact subset_diskMinusRadii_openSectorIdx hρ hYne hY i hi
  obtain ⟨i, hi⟩ := exists_mem_openSectorIdx hρ hYne hY hp
  exact mem_iUnion.mpr ⟨i, hi⟩

private lemma connectedComponentIn_eq_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) {p : V} {i : Fin (argList x Y).length}
    (hp : p ∈ openSectorIdx x ρ Y i) :
    connectedComponentIn (diskMinusRadii x ρ Y) p = openSectorIdx x ρ Y i := by
  have hsub := subset_diskMinusRadii_openSectorIdx hρ hYne hY i
  refine subset_antisymm ?_ (((show IsConnected (openSectorIdx x ρ Y i) from
    (isPathConnected_openSector hρ
    (θLeft_lt_θRight i)).isConnected).isPreconnected).subset_connectedComponentIn hp hsub)
  have hU : connectedComponentIn (diskMinusRadii x ρ Y) p ⊆ openSectorIdx x ρ Y i ∪
        ⋃ j ∈ ({i}ᶜ : Set (Fin (argList x Y).length)), openSectorIdx x ρ Y j := by
    intro q hq
    have hqD := connectedComponentIn_subset _ _ hq
    rw [← iUnion_openSectorIdx hρ hYne hY] at hqD
    obtain ⟨j, hj⟩ := mem_iUnion.mp hqD
    obtain rfl | hji := eq_or_ne j i
    · exact Or.inl hj
    right
    exact mem_biUnion hji hj
  have hdisj : Disjoint (openSectorIdx x ρ Y i)
      (⋃ j ∈ ({i}ᶜ : Set (Fin _)), openSectorIdx x ρ Y j) :=
    disjoint_iUnion₂_right.mpr fun j hj ↦ pairwiseDisjoint_openSectorIdx hρ (Ne.symm hj)
  obtain h | h := ((show IsPreconnected (connectedComponentIn (diskMinusRadii x ρ Y) p)
    from isPreconnected_connectedComponentIn).subset_or_subset)
    (isOpen_openSector hρ) (isOpen_biUnion fun _ _ ↦ isOpen_openSector hρ) hdisj hU
  · exact h
  exfalso
  have : p ∈ ⋃ j ∈ ({i}ᶜ : Set (Fin _)), openSectorIdx x ρ Y j :=
    h (mem_connectedComponentIn (hsub hp))
  obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp this
  exact (pairwiseDisjoint_openSectorIdx hρ (Ne.symm hj)).ne_of_mem hp hpj rfl

private lemma sectors_eq_range_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty) (hY : ↑Y ⊆ sphere x ρ)
    : sectors x ρ Y = range (openSectorIdx x ρ Y) := by
  ext C
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := exists_mem_openSectorIdx hρ hYne hY hp
    exact ⟨i, (connectedComponentIn_eq_openSectorIdx hρ hYne hY hi).symm⟩
  rintro ⟨i, rfl⟩
  obtain ⟨p, hp⟩ := nonempty_openSectorIdx hρ i
  exact ⟨p, subset_diskMinusRadii_openSectorIdx hρ hYne hY i hp,
    connectedComponentIn_eq_openSectorIdx hρ hYne hY hp⟩

private lemma injective_openSectorIdx (hρ : 0 < ρ) : Function.Injective (openSectorIdx x ρ Y) := by
  intro i j hij
  by_contra hne
  obtain ⟨p, hp⟩ := nonempty_openSectorIdx hρ i
  exact (pairwiseDisjoint_openSectorIdx hρ hne).ne_of_mem hp (hij ▸ hp) rfl

/-- **There are exactly `d` sectors.** -/
@[grind =]
theorem ncard_sectors (hρ : 0 < ρ) (hYne : Y.Nonempty) (hY : ↑Y ⊆ sphere x ρ) :
    (sectors x ρ Y).ncard = Y.card := by
  rw [sectors_eq_range_openSectorIdx hρ hYne hY,
    ncard_range_of_injective (injective_openSectorIdx hρ), Nat.card_eq_fintype_card,
    Fintype.card_fin, length_argList hρ hY]

private lemma closure_openSector {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) (hθ : θ₁ < θ₂) :
    closure (openSector x ρ θ₁ θ₂) = (uncurry (polar x)) '' (Icc (0 : ℝ) ρ ×ˢ Icc θ₁ θ₂) := by
  have hcl : closure (Ioo (0 : ℝ) ρ ×ˢ Ioo θ₁ θ₂) = Icc 0 ρ ×ˢ Icc θ₁ θ₂ := by
    rw [closure_prod_eq, closure_Ioo hρ.ne, closure_Ioo hθ.ne]
  refine subset_antisymm ?_ ?_
  · refine ((isCompact_Icc.prod isCompact_Icc).image (continuous_uncurry_polar x)
    |>.isClosed).closure_subset_iff.mpr ?_
    exact image_mono fun _ hp ↦ ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  exact hcl ▸ image_closure_subset_closure_image (continuous_uncurry_polar x)


private lemma θLeft_gt_neg_pi (i : Fin (argList x Y).length) : -π < θLeft x Y i :=
  (argList_get_mem_Ioc (x := x) (Y := Y) i).1

private lemma θRight_le_three_pi (i : Fin (argList x Y).length) : θRight x Y i ≤ 3 * π := by
  simp only [θRight]
  split_ifs with hi
  · linarith [(argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑i + 1, hi⟩).2, Real.pi_pos]
  linarith [(argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, i.pos⟩).2, Real.pi_pos]

private lemma exists_get_eq_arg {y : V} (hy : y ∈ Y) :
    ∃ i : Fin (argList x Y).length, (argList x Y).get i = arg (toComplex x y) :=
  (arg_mem_argFinset_iff (x := x) (Y := Y)).mp <| Finset.mem_image.mpr ⟨y, hy, rfl⟩

private lemma get_eq_arg_unique {i j : Fin (argList x Y).length}
    (hij : (argList x Y).get i = (argList x Y).get j) : i = j :=
  (argFinset x Y |>.sort_nodup _).get_inj_iff.mp hij

private abbrev isEndpoint (α : ℝ) (i : Fin (argList x Y).length) : Prop :=
  θLeft x Y i = α ∨ θRight x Y i = α ∨ θRight x Y i = α + 2 * π

/-- On a removed radius (away from the centre), a sector meets `p` in its closure iff that radius
is one of the two angular endpoints of the sector. -/
private lemma mem_closure_openSectorIdx_iff (hρ : 0 < ρ) {p : V}
    (hr : 0 < ‖p - x‖) (hrρ : ‖p - x‖ < ρ) (hα : arg (toComplex x p) ∈ argFinset x Y)
    (i : Fin (argList x Y).length) :
    p ∈ closure (openSectorIdx x ρ Y i) ↔ isEndpoint (arg (toComplex x p)) i := by
  set α := arg (toComplex x p)
  set r := ‖p - x‖
  have hr0 : 0 < r := hr
  have hpole : polar x r α = p := by
    simpa [r, α, norm_toComplex] using polar_of_toComplex (x := x) (p := p)
  have hαIoc : α ∈ Ioc (-π) π := arg_mem_Ioc _
  refine ⟨fun hp ↦ ?_, fun h ↦ ?_⟩
  · change p ∈ closure (openSector x ρ (θLeft x Y i) (θRight x Y i)) at hp
    rw [closure_openSector hρ (θLeft_lt_θRight i)] at hp
    obtain ⟨⟨s, θ⟩, ⟨hs, hθ⟩, hpol⟩ := hp
    change polar x s θ = p at hpol
    have hs0 : 0 < s := lt_of_le_of_ne hs.1 fun hs00 ↦
      (norm_sub_pos_iff.mp hr) <| by simpa [polar, hs00.symm] using hpol.symm
    obtain rfl : s = r := by
      have h1 : dist (polar x s θ) x = s := by simp [dist_polar, abs_of_pos hs0]
      have h2 : dist p x = r := by simp [r, dist_eq_norm_sub]
      linarith [congrArg (dist · x) hpol ▸ h1, h2]
    obtain ⟨n, hn⟩ := (polar_eq_iff_angle hr0).mp (hpol.trans hpole.symm)
    have hn01 : n = 0 ∨ n = 1 := by
      have hgt : (-1 : ℤ) < n := by
        have : -2 * π < θ - α := by
          linarith [θLeft_gt_neg_pi (x := x) (Y := Y) i, hθ.1, hαIoc.2]
        have : (-1 : ℝ) * (2 * π) < (n : ℝ) * (2 * π) := by linarith [hn]
        exact_mod_cast (mul_lt_mul_iff_of_pos_right Real.two_pi_pos).mp this
      have hlt : n < (2 : ℤ) := by
        have : θ - α < 4 * π := by
          linarith [θRight_le_three_pi (x := x) (Y := Y) i, hθ.2, hαIoc.1]
        have : (n : ℝ) * (2 * π) < (2 : ℝ) * (2 * π) := by linarith [hn]
        exact_mod_cast (mul_lt_mul_iff_of_pos_right Real.two_pi_pos).mp this
      interval_cases n <;> simp
    have hnot_int : α ∉ Ioo (θLeft x Y i) (θRight x Y i) := fun hmem ↦
      (toIocMod_not_mem_argFinset (x := x) (Y := Y) i hmem)
        (by simpa [α, toIocMod_eq_of_mem_Ioc hαIoc] using hα)
    have hnot_int2 : α + 2 * π ∉ Ioo (θLeft x Y i) (θRight x Y i) := by
      refine fun hmem ↦ ?_
      have hmod : toIocMod two_pi_pos (-π) (α + 2 * π) = α := by
        simp [toIocMod_eq_of_mem_Ioc hαIoc]
      exact toIocMod_not_mem_argFinset (x := x) (Y := Y) i hmem (by simpa [hmod, α] using hα)
    obtain rfl | rfl := hn01
    · grind
    obtain rfl : θ = α + 2 * π := by
      rw [hn]
      push_cast
      ring
    obtain hL | hL := eq_or_lt_of_le hθ.1
    · have : θLeft x Y i ≤ π := (argList_get_mem_Ioc (x := x) (Y := Y) i).2
      linarith [hL, hαIoc.1]
    grind
  change p ∈ closure (openSector x ρ (θLeft x Y i) (θRight x Y i))
  rw [closure_openSector hρ (θLeft_lt_θRight i)]
  obtain hL | hR | hRw := h
  · exact ⟨(r, α), ⟨⟨hr0.le, hrρ.le⟩, (hL ▸ ⟨le_rfl, (θLeft_lt_θRight i).le⟩)⟩, hpole⟩
  · exact ⟨(r, α), ⟨⟨hr0.le, hrρ.le⟩, (hR ▸ ⟨(θLeft_lt_θRight i).le, le_rfl⟩)⟩, hpole⟩
  refine ⟨(r, α + 2 * π), ⟨⟨hr0.le, hrρ.le⟩, (hRw ▸ ⟨(θLeft_lt_θRight i).le, le_rfl⟩)⟩, ?_⟩
  change polar x r (α + 2 * π) = p
  rw [polar_add_two_pi, hpole]

private lemma card_endpoint_eq_two (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) (hd : 1 < Y.card)
    {y : V} (hy : y ∈ Y) :
    (Finset.univ.filter fun i : Fin (argList x Y).length ↦
      isEndpoint (arg (toComplex x y)) i).card = 2 := by
  have hlen : 1 < (argList x Y).length := (length_argList hρ hY).symm ▸ hd
  obtain ⟨k, hk⟩ := exists_get_eq_arg (x := x) (Y := Y) hy
  set α := arg (toComplex x y)
  have hαIoc : α ∈ Ioc (-π) π := by simpa [α] using arg_mem_Ioc (toComplex x y)
  let S := Finset.univ.filter fun i : Fin (argList x Y).length ↦ isEndpoint α i
  have hkS : k ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Or.inl (by simpa [θLeft, α] using hk))⟩
  by_cases hk0 : (k : ℕ) = 0
  · have hlen_pos : 0 < (argList x Y).length := lt_trans Nat.zero_lt_one hlen
    let iLast : Fin (argList x Y).length :=
      ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen_pos⟩
    have hne : k ≠ iLast := by
      intro h
      have : (0 : ℕ) = (argList x Y).length - 1 := by
        simpa [hk0] using congrArg Fin.val h
      omega
    have hLast : ¬ ↑iLast + 1 < (argList x Y).length := by
      change ¬ (argList x Y).length - 1 + 1 < (argList x Y).length
      exact Nat.not_lt.mpr (Nat.le_of_eq (Nat.sub_add_cancel hlen_pos).symm)
    have hWrap : isEndpoint α iLast := by
      refine Or.inr (Or.inr ?_)
      simp only [θRight, hLast, ↓reduceDIte]
      simpa [show (⟨0, iLast.pos⟩ : Fin (argList x Y).length) = k from Fin.ext hk0.symm, α] using hk
    have hiS : iLast ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWrap⟩
    have hS : S ⊆ ({k, iLast} : Finset _) := by
      refine fun m hm ↦ Finset.mem_insert.mpr ?_
      obtain hL | hR | hRw := (Finset.mem_filter.mp hm).2
      · exact Or.inl (get_eq_arg_unique (hL.trans hk.symm))
      · simp only [θRight] at hR
        split_ifs at hR with hm'
        · have heq : (⟨↑m + 1, hm'⟩ : Fin _) = k := get_eq_arg_unique (hR.trans hk.symm)
          have : (m : ℕ) + 1 = 0 := by simpa [hk0] using congrArg Fin.val heq
          exact (Nat.succ_ne_zero _).elim this
        grind
      simp only [θRight] at hRw
      split_ifs at hRw with hm'
      · have hmem := argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑m + 1, hm'⟩
        linarith [hmem.2, hαIoc.1]
      grind
    exact Finset.card_eq_two.mpr ⟨k, iLast, hne, Finset.Subset.antisymm hS
      (Finset.insert_subset_iff.mpr ⟨hkS, Finset.singleton_subset_iff.mpr hiS⟩)⟩
  have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
  let iPred : Fin (argList x Y).length :=
    ⟨(k : ℕ) - 1, (Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt)⟩
  have hne : k ≠ iPred := by
    intro h
    have : (k : ℕ) = (k : ℕ) - 1 := congrArg Fin.val h
    omega
  have hpred_succ : ↑iPred + 1 < (argList x Y).length := by
    change (k : ℕ) - 1 + 1 < (argList x Y).length
    omega
  have hLeft : isEndpoint α iPred := by
    refine Or.inr (Or.inl ?_)
    simp only [θRight, hpred_succ, ↓reduceDIte]
    have : (⟨↑iPred + 1, hpred_succ⟩ : Fin _) = k := by
      refine Fin.ext (?_)
      change (k : ℕ) - 1 + 1 = (k : ℕ)
      omega
    simpa [this, α] using hk
  have hiS : iPred ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLeft⟩
  have hS : S ⊆ ({k, iPred} : Finset _) := by
    refine fun m hm ↦ Finset.mem_insert.mpr ?_
    obtain hL | hR | hRw := (Finset.mem_filter.mp hm).2
    · exact Or.inl (get_eq_arg_unique (hL.trans hk.symm))
    · simp only [θRight] at hR
      split_ifs at hR with hm'
      · have heq : (⟨↑m + 1, hm'⟩ : Fin _) = k := get_eq_arg_unique (hR.trans hk.symm)
        exact Or.inr
          (Finset.mem_singleton.mpr (Fin.ext (Nat.eq_sub_of_add_eq (congrArg Fin.val heq))))
      linarith [(argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, m.pos⟩).1, hαIoc.2]
    simp only [θRight] at hRw
    split_ifs at hRw with hm'
    · have hmem := argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑m + 1, hm'⟩
      linarith [hmem.2, hαIoc.1]
    have : (argList x Y).get ⟨0, m.pos⟩ = α := by linarith
    exact (hk0 (congrArg Fin.val (get_eq_arg_unique (hk.trans this.symm)))).elim
  exact Finset.card_eq_two.mpr ⟨k, iPred, hne, Finset.Subset.antisymm hS
    (Finset.insert_subset_iff.mpr ⟨hkS, Finset.singleton_subset_iff.mpr hiS⟩)⟩

private lemma arg_eq_of_mem_segment_radius (hρ : 0 < ρ) {y p : V}
    (hy : y ∈ sphere x ρ) (hp : p ∈ segment ℝ x y \ {x, y}) :
    0 < ‖p - x‖ ∧ ‖p - x‖ < ρ ∧ arg (toComplex x p) = arg (toComplex x y) := by
  have hp' : p ∈ segment ℝ x y := hp.1
  have hpx : p ≠ x := fun h ↦ hp.2 (Or.inl h)
  have hball : p ∈ ball x ρ := by
    -- interior of segment to a sphere point lies in the open ball
    rw [segment_eq_image_lineMap] at hp'
    obtain ⟨t, ht, rfl⟩ := hp'
    rw [mem_ball, dist_eq_norm_sub, lineMap_sub_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, (mem_sphere_iff_norm.mp hy)]
    exact mul_lt_of_lt_one_left hρ ((show t ∈ Ioo (0 : ℝ) 1 from ⟨lt_of_le_of_ne ht.1 ((show t ≠ 0
      from fun h ↦ hpx (by simp [AffineMap.lineMap_apply, h])).symm), lt_of_le_of_ne ht.2 (fun h ↦
      (hp.2 (Or.inr (by simp [AffineMap.lineMap_apply, h]))))⟩).2)
  exact ⟨norm_sub_pos_iff.mpr hpx, mem_ball_iff_norm.mp hball,
    (((mem_segment_iff_arg hρ hy hball).mp hp').resolve_left hpx)⟩

/-- **Adjacency.** A point in the relative interior of one of the radii lies in the closure of
exactly two sectors — the two on either side of that radius. For `d = 1` the same sector lies on
both sides, and the count is one; the theorem assumes `1 < Y.card` to exclude this case. -/
@[grind →]
theorem ncard_sectors_closure_eq_two (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) (hd : 1 < Y.card)
    {y : V} (hy : y ∈ Y) {p : V}
    (hp : p ∈ segment ℝ x y \ {x, y}) : {C ∈ sectors x ρ Y | p ∈ closure C}.ncard = 2 := by
  obtain ⟨hr, hrρ, harg⟩ := arg_eq_of_mem_segment_radius hρ (hY hy) hp
  have hα : arg (toComplex x p) ∈ argFinset x Y := Finset.mem_image.mpr ⟨y, hy, harg.symm⟩
  set α := arg (toComplex x y)
  let S := Finset.univ.filter fun i : Fin (argList x Y).length ↦ isEndpoint α i
  have hScard : S.card = 2 := by
    simpa [S, α] using card_endpoint_eq_two hρ hY hd hy
  have hsectors : sectors x ρ Y = range (openSectorIdx x ρ Y) :=
    sectors_eq_range_openSectorIdx hρ (Finset.card_pos.mp (lt_trans Nat.zero_lt_one hd)) hY
  have hset : {C ∈ sectors x ρ Y | p ∈ closure C} = (openSectorIdx x ρ Y) '' (S : Set _) := by
    ext C
    refine ⟨fun ⟨hCsec, hpC⟩ ↦ ?_, ?_⟩
    · rw [hsectors] at hCsec
      obtain ⟨i, rfl⟩ := hCsec
      refine ⟨i, ?_, rfl⟩
      have : isEndpoint (arg (toComplex x p)) i :=
        (mem_closure_openSectorIdx_iff hρ hr hrρ hα i).mp hpC
      exact Finset.mem_coe.mpr <| Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [α, harg] using this⟩
    rintro ⟨i, hi, rfl⟩
    refine ⟨hsectors ▸ ⟨i, rfl⟩, ?_⟩
    exact (mem_closure_openSectorIdx_iff hρ hr hrρ hα i).mpr (by simpa [α, harg] using
      (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2)
  rw [hset, ncard_image_of_injective _ (injective_openSectorIdx hρ), ncard_coe_finset, hScard]

/-- Every sector has the centre in its closure. -/
theorem mem_closure_of_mem_sectors (hρ : 0 < ρ) (hYne : Y.Nonempty) (hY : ↑Y ⊆ sphere x ρ)
    (hC : C ∈ sectors x ρ Y) : x ∈ closure C := by
  rw [sectors_eq_range_openSectorIdx hρ hYne hY] at hC
  obtain ⟨i, rfl⟩ := hC
  set θ₁ := θLeft x Y i
  set θ₂ := θRight x Y i
  have hθ : θ₁ < θ₂ := θLeft_lt_θRight i
  have hmem : ((0 : ℝ), (θ₁ + θ₂) / 2) ∈ closure (Ioo (0 : ℝ) ρ ×ˢ Ioo θ₁ θ₂) := by
    rw [closure_prod_eq, closure_Ioo hρ.ne, closure_Ioo hθ.ne]
    exact ⟨⟨le_rfl, hρ.le⟩, by constructor <;> linarith⟩
  have hx : polar x 0 ((θ₁ + θ₂) / 2) = x := by simp [polar]
  have hmem' : polar x 0 ((θ₁ + θ₂) / 2) ∈ closure (openSectorIdx x ρ Y i) :=
    image_closure_subset_closure_image (continuous_uncurry_polar x) ⟨_, hmem, rfl⟩
  rwa [hx] at hmem'
