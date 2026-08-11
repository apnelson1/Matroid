module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Data.List.Sort
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# A disk with finitely many radii removed

Remove from an open disk the radii to `d ≥ 1` points of its bounding sphere. What is left falls into
exactly `d` pieces — the open sectors between consecutive radii — and a point in the relative
interior of a radius is in the closure of exactly two of them.

This is Status.md 3.5, and the only place in the Kuratowski development where the plane is used for
its *local* structure rather than for the Jordan curve theorem. It is elementary — polar coordinates
`(s, θ) ↦ x + s · e^{iθ}` carry a rectangle onto a sector — and it is why the polygonal category is
worth the trouble: for an arbitrary drawing the corresponding statement is Schoenflies-strength.

The dimension is essential and is not decoration: in `ℝ³` the complement of finitely many radii in a
ball is connected.

## Statement design

Status.md describes the pieces by their angles. That description is not stated here, for two
reasons: it forces an ordering of the points by argument, which is bookkeeping that no consumer
reads, and it commits the proof to polar coordinates. What the consumers (3.7, 3.8, 3.9) actually
use is three things — how many pieces there are, that each is open and connected, and which pieces a
radius is adjacent to — so those are what is stated, about the connected components themselves.

## Main definitions

* `sectors x ρ Y` : the connected components of the disk minus the radii, as a set of subsets.

## Main statements

* `ncard_sectors` : there are exactly `Y.card` of them.
* `isOpen_of_mem_sectors`, `isConnected_of_mem_sectors`
* `ncard_sectors_closure_eq_two` : a point interior to a radius lies in the closure of exactly two.
-/

@[expose] public section

open Set Metric Complex Real Function

/-- The disk of radius `ρ` about `x` with the radii to the points of `Y` removed. -/
def diskMinusRadii (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (Y : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ball x ρ \ ⋃ y ∈ Y, segment ℝ x y

/-- The sectors: the connected components of `diskMinusRadii`, presented as a set of subsets rather
than as a quotient type, since the consumers count them and take their closures. -/
def sectors (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (Y : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  (fun p ↦ connectedComponentIn (diskMinusRadii x ρ Y) p) '' diskMinusRadii x ρ Y

variable {x : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ} {Y : Finset (EuclideanSpace ℝ (Fin 2))}
  {C : Set (EuclideanSpace ℝ (Fin 2))}

theorem subset_diskMinusRadii_of_mem_sectors (hC : C ∈ sectors x ρ Y) :
    C ⊆ diskMinusRadii x ρ Y := by
  obtain ⟨_, _, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

theorem isOpen_diskMinusRadii : IsOpen (diskMinusRadii x ρ Y) :=
  isOpen_ball.sdiff <| Y.finite_toSet.isClosed_biUnion fun _ _ ↦
    closure_openSegment (𝕜 := ℝ) x _ ▸ isClosed_closure

/-- Each sector is open: `diskMinusRadii` is open and the plane is locally connected. -/
theorem isOpen_of_mem_sectors (hC : C ∈ sectors x ρ Y) : IsOpen C := by
  obtain ⟨_, _, rfl⟩ := hC
  exact isOpen_diskMinusRadii.connectedComponentIn

theorem isConnected_of_mem_sectors (hC : C ∈ sectors x ρ Y) : IsConnected C := by
  obtain ⟨_, hp, rfl⟩ := hC
  exact isConnected_connectedComponentIn_iff.mpr hp

/-- Distinct sectors are disjoint, and they cover the punctured disk. -/
theorem sUnion_sectors (_hρ : 0 < ρ) : ⋃₀ sectors x ρ Y = diskMinusRadii x ρ Y :=
  subset_antisymm (sUnion_subset fun _ ↦ subset_diskMinusRadii_of_mem_sectors) fun _ hp ↦
    mem_sUnion.mpr ⟨_, mem_image_of_mem _ hp, mem_connectedComponentIn hp⟩

theorem pairwiseDisjoint_sectors : (sectors x ρ Y).PairwiseDisjoint id := by
  rintro _ ⟨p, _, rfl⟩ _ ⟨q, _, rfl⟩ hpq
  exact disjoint_left.2 fun _ hp hq ↦
    hpq <| (connectedComponentIn_eq hp).trans (connectedComponentIn_eq hq).symm

/-! ### Private polar helpers -/

noncomputable def toComplex (x p : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  orthonormalBasisOneI.repr.symm (p - x)

noncomputable def polar (x : EuclideanSpace ℝ (Fin 2)) (s θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  x + orthonormalBasisOneI.repr (↑s * cexp (↑θ * I))

private lemma toComplex_polar (x : EuclideanSpace ℝ (Fin 2)) (s θ : ℝ) :
    toComplex x (polar x s θ) = ↑s * cexp (↑θ * I) := by
  simp [toComplex, polar]

private lemma toComplex_eq_zero {x p : EuclideanSpace ℝ (Fin 2)} :
    toComplex x p = 0 ↔ p = x := by
  rw [toComplex, LinearIsometryEquiv.map_eq_zero_iff, sub_eq_zero]

private lemma norm_toComplex (x p : EuclideanSpace ℝ (Fin 2)) :
    ‖toComplex x p‖ = ‖p - x‖ :=
  LinearIsometryEquiv.norm_map _ _

private lemma dist_polar (x : EuclideanSpace ℝ (Fin 2)) (s θ : ℝ) :
    dist (polar x s θ) x = |s| := by
  rw [dist_eq_norm_sub, polar, add_sub_cancel_left, LinearIsometryEquiv.norm_map,
    norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs]

private lemma continuous_uncurry_polar (x : EuclideanSpace ℝ (Fin 2)) :
    Continuous (uncurry (polar x)) := by
  unfold polar uncurry; fun_prop

private lemma polar_of_toComplex {x p : EuclideanSpace ℝ (Fin 2)} (_hp : p ≠ x) :
    polar x ‖toComplex x p‖ (arg (toComplex x p)) = p := by
  unfold polar
  have h := norm_mul_exp_arg_mul_I (toComplex x p)
  simp only [toComplex] at h ⊢
  rw [h, LinearIsometryEquiv.apply_symm_apply, add_sub_cancel]

private lemma polar_add_two_pi (x : EuclideanSpace ℝ (Fin 2)) (s θ : ℝ) :
    polar x s (θ + 2 * π) = polar x s θ := by
  unfold polar
  congr 1
  have : cexp (↑(θ + 2 * π) * I) = cexp (↑θ * I) := by
    rw [ofReal_add, add_mul, Complex.exp_add]
    have : cexp (↑(2 * π) * I) = 1 := by
      convert Complex.exp_two_pi_mul_I
      push_cast; ring
    rw [this, mul_one]
  rw [this]

private lemma sameRay_toComplex_iff {x p q : EuclideanSpace ℝ (Fin 2)} :
    SameRay ℝ (toComplex x p) (toComplex x q) ↔ SameRay ℝ (p - x) (q - x) := by
  simpa [toComplex] using
    (SameRay.sameRay_map_iff
      (orthonormalBasisOneI.repr.symm : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ).toLinearEquiv
      (x := p - x) (y := q - x))

private lemma ofReal_mul_I_eq_iff {a b : ℝ} : (a : ℂ) * I = ↑b * I ↔ a = b := by
  constructor
  · intro h; simpa using congrArg Complex.im h
  · rintro rfl; rfl

private lemma polar_inj {x : EuclideanSpace ℝ (Fin 2)} {s₁ s₂ θ₁ θ₂ : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hθ : |θ₁ - θ₂| < 2 * π)
    (h : polar x s₁ θ₁ = polar x s₂ θ₂) : s₁ = s₂ ∧ θ₁ = θ₂ := by
  have hs : s₁ = s₂ := by
    have := congrArg (dist · x) h
    simpa [dist_polar, abs_of_pos hs₁, abs_of_pos hs₂] using this
  subst hs
  refine ⟨rfl, sub_eq_zero.mp ?_⟩
  have hexp : cexp (↑θ₁ * I) = cexp (↑θ₂ * I) := by
    have hceq : (s₁ : ℂ) * cexp (↑θ₁ * I) = ↑s₁ * cexp (↑θ₂ * I) := by
      simpa [toComplex_polar] using congrArg (toComplex x) h
    exact mul_left_cancel₀ (ofReal_ne_zero.mpr hs₁.ne') hceq
  have h1 : cexp (↑(θ₁ - θ₂) * I) = 1 := by
    rw [ofReal_sub, sub_mul, Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hn' : (↑(θ₁ - θ₂) : ℂ) * I = ↑((n : ℝ) * (2 * π)) * I := by
    convert hn using 1; push_cast; ring
  have hθn : θ₁ - θ₂ = (n : ℝ) * (2 * π) := ofReal_mul_I_eq_iff.mp hn'
  have hn0 : n = 0 := by
    have : |(n : ℝ) * (2 * π)| < 2 * π := by simpa [← hθn] using hθ
    rw [abs_mul, abs_of_pos Real.two_pi_pos] at this
    have hlt : |(n : ℝ)| < 1 :=
      (mul_lt_mul_iff_of_pos_right Real.two_pi_pos).mp (by simpa using this)
    have : |n| < 1 := by
      rw [← Int.cast_abs, ← Int.cast_one] at hlt
      exact_mod_cast hlt
    exact Int.abs_lt_one_iff.mp this
  simpa [hn0] using hθn

noncomputable def argFinset (x : EuclideanSpace ℝ (Fin 2))
    (Y : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  Y.image fun y ↦ arg (toComplex x y)

noncomputable def argList (x : EuclideanSpace ℝ (Fin 2))
    (Y : Finset (EuclideanSpace ℝ (Fin 2))) : List ℝ :=
  (argFinset x Y).sort (· ≤ ·)

private lemma injOn_arg_of_mem_sphere (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) :
    InjOn (fun y ↦ arg (toComplex x y)) (Y : Set _) := by
  intro y₁ hy₁ y₂ hy₂ harg
  have hnorm1 : ‖y₁ - x‖ = ρ := mem_sphere_iff_norm.mp (hY hy₁)
  have hnorm2 : ‖y₂ - x‖ = ρ := mem_sphere_iff_norm.mp (hY hy₂)
  have hsr' : SameRay ℝ (y₁ - x) (y₂ - x) :=
    sameRay_toComplex_iff.mp (sameRay_of_arg_eq harg)
  have heq : ‖y₁ - x‖ • (y₂ - x) = ‖y₂ - x‖ • (y₁ - x) :=
    sameRay_iff_norm_smul_eq.mp hsr'
  rw [hnorm1, hnorm2] at heq
  have hsub : y₂ - x = y₁ - x := smul_right_injective (EuclideanSpace ℝ (Fin 2)) hρ.ne' heq
  have : y₂ - y₁ = 0 := by
    have h : y₂ - y₁ = (y₂ - x) - (y₁ - x) := by abel
    rw [h, hsub, sub_self]
  exact (sub_eq_zero.mp this).symm

private lemma card_argFinset (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) :
    (argFinset x Y).card = Y.card :=
  Finset.card_image_of_injOn (injOn_arg_of_mem_sphere hρ hY)

private lemma length_argList (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) :
    (argList x Y).length = Y.card := by
  simp [argList, Finset.length_sort, card_argFinset hρ hY]

private lemma argList_get_lt {i j : Fin (argList x Y).length} (hij : i < j) :
    (argList x Y).get i < (argList x Y).get j := by
  have hle := (argFinset x Y |>.pairwise_sort _).rel_get_of_lt hij
  have hne : (argList x Y).get i ≠ (argList x Y).get j := fun h ↦
    (ne_of_lt hij) ((argFinset x Y |>.sort_nodup _).get_inj_iff.mp h)
  exact lt_of_le_of_ne hle hne

private lemma argList_get_mem_Ioc (i : Fin (argList x Y).length) :
    (argList x Y).get i ∈ Ioc (-π) π := by
  have hmem : (argList x Y).get i ∈ argFinset x Y :=
    (Finset.mem_sort (· ≤ ·)).mp <| List.get_mem (argList x Y) i
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
  rw [← hy]
  exact arg_mem_Ioc _

noncomputable def openSector (x : EuclideanSpace ℝ (Fin 2)) (ρ θ₁ θ₂ : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun p : ℝ × ℝ ↦ polar x p.1 p.2) '' (Ioo 0 ρ ×ˢ Ioo θ₁ θ₂)

noncomputable def θLeft (x : EuclideanSpace ℝ (Fin 2))
    (Y : Finset (EuclideanSpace ℝ (Fin 2))) (i : Fin (argList x Y).length) : ℝ :=
  (argList x Y).get i

noncomputable def θRight (x : EuclideanSpace ℝ (Fin 2))
    (Y : Finset (EuclideanSpace ℝ (Fin 2))) (i : Fin (argList x Y).length) : ℝ :=
  if h : ↑i + 1 < (argList x Y).length then (argList x Y).get ⟨↑i + 1, h⟩
  else (argList x Y).get ⟨0, i.pos⟩ + 2 * π

noncomputable def openSectorIdx (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (Y : Finset (EuclideanSpace ℝ (Fin 2))) (i : Fin (argList x Y).length) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  openSector x ρ (θLeft x Y i) (θRight x Y i)

private lemma θLeft_lt_θRight (i : Fin (argList x Y).length) :
    θLeft x Y i < θRight x Y i := by
  simp only [θLeft, θRight]
  split_ifs with h
  · exact argList_get_lt (show (i : ℕ) < i + 1 from Nat.lt_succ_self _)
  · have hi := argList_get_mem_Ioc (x := x) (Y := Y) i
    have h0 := argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, i.pos⟩
    linarith [hi.2, h0.1]

private lemma lineMap_sub_left (t : ℝ) (a b : EuclideanSpace ℝ (Fin 2)) :
    AffineMap.lineMap a b t - a = t • (b - a) := by
  simp [AffineMap.lineMap_apply]

private lemma mem_segment_iff_arg (hρ : 0 < ρ) {y p : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ sphere x ρ) (hp : p ∈ ball x ρ) :
    p ∈ segment ℝ x y ↔ p = x ∨ arg (toComplex x p) = arg (toComplex x y) := by
  have hnormy : ‖y - x‖ = ρ := mem_sphere_iff_norm.mp hy
  have hyx : y ≠ x := by
    intro h
    have : ‖y - x‖ = 0 := by simp [h]
    exact hρ.ne' (hnormy.symm.trans this)
  have hpball : ‖p - x‖ < ρ := mem_ball_iff_norm.mp hp
  constructor
  · intro hseg
    by_cases hpx : p = x
    · exact Or.inl hpx
    · right
      rw [segment_eq_image_lineMap] at hseg
      obtain ⟨t, ht, rfl⟩ := hseg
      have hsr : SameRay ℝ (AffineMap.lineMap x y t - x) (y - x) := by
        rw [lineMap_sub_left]
        exact SameRay.sameRay_nonneg_smul_left _ ht.1
      refine (Complex.sameRay_iff.mp (sameRay_toComplex_iff.mpr hsr)).resolve_left ?_ |>.resolve_left ?_
      · exact mt toComplex_eq_zero.mp hpx
      · exact mt toComplex_eq_zero.mp hyx
  · intro h
    rcases h with rfl | harg
    · exact left_mem_segment _ _ _
    · by_cases hpx : p = x
      · subst p; exact left_mem_segment _ _ _
      · have hsr : SameRay ℝ (p - x) (y - x) :=
          sameRay_toComplex_iff.mp (sameRay_of_arg_eq harg)
        obtain ⟨r, hr0, hr⟩ := hsr.exists_nonneg_right (sub_ne_zero.mpr hyx)
        have hr_eq : r = ‖p - x‖ / ρ := by
          have : ‖p - x‖ = r * ρ := by
            rw [hr, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, hnormy]
          field_simp [hρ.ne']; linarith
        have ht : r ∈ Icc (0 : ℝ) 1 :=
          ⟨hr0, by rw [hr_eq, div_le_one hρ]; exact hpball.le⟩
        have : p = AffineMap.lineMap x y r := by
          apply eq_of_sub_eq_zero
          calc
            p - AffineMap.lineMap x y r
                = (p - x) - (AffineMap.lineMap x y r - x) := by abel
              _ = r • (y - x) - r • (y - x) := by rw [hr, lineMap_sub_left]
              _ = 0 := by rw [sub_self]
        rw [this]
        exact lineMap_mem_segment ℝ x y ht


private lemma ne_center_of_mem_diskMinusRadii (hYne : Y.Nonempty)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ diskMinusRadii x ρ Y) : p ≠ x := by
  intro hpx; subst p
  obtain ⟨y, hy⟩ := hYne
  have : x ∈ ⋃ y ∈ Y, segment ℝ x y :=
    mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, left_mem_segment _ _ _⟩⟩
  exact hp.2 this

private lemma mem_diskMinusRadii_iff (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) {p : EuclideanSpace ℝ (Fin 2)} :
    p ∈ diskMinusRadii x ρ Y ↔
      p ∈ ball x ρ ∧ p ≠ x ∧ arg (toComplex x p) ∉ argFinset x Y := by
  constructor
  · intro hp
    refine ⟨hp.1, ne_center_of_mem_diskMinusRadii hYne hp, fun harg ↦ ?_⟩
    obtain ⟨y, hyY, hy⟩ := Finset.mem_image.mp harg
    have hseg : p ∈ segment ℝ x y :=
      (mem_segment_iff_arg hρ (hY hyY) hp.1).mpr (Or.inr hy.symm)
    have : p ∈ ⋃ y ∈ Y, segment ℝ x y :=
      mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hyY, hseg⟩⟩
    exact hp.2 this
  · intro ⟨hp, hpx, harg⟩
    refine ⟨hp, ?_⟩
    intro h
    obtain ⟨y, hy⟩ := mem_iUnion.mp h
    obtain ⟨hyY, hseg⟩ := mem_iUnion.mp hy
    rcases (mem_segment_iff_arg hρ (hY hyY) hp).mp hseg with heq | harg'
    · exact hpx heq
    · exact harg (Finset.mem_image.mpr ⟨y, hyY, harg'.symm⟩)

private lemma isPathConnected_openSector {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) (hθ : θ₁ < θ₂) :
    IsPathConnected (openSector x ρ θ₁ θ₂) := by
  have hrect : IsPathConnected (Ioo (0 : ℝ) ρ ×ˢ Ioo θ₁ θ₂) :=
    ((convex_Ioo (0 : ℝ) ρ).isPathConnected (nonempty_Ioo.mpr hρ)).prod
      ((convex_Ioo θ₁ θ₂).isPathConnected (nonempty_Ioo.mpr hθ))
  simpa [openSector] using hrect.image (continuous_uncurry_polar x)

private lemma ofReal_mul_exp_eq {s θ : ℝ} (hs : 0 < s) :
    (↑s : ℂ) * cexp (↑θ * I) = cexp (↑(Real.log s) + ↑θ * I) := by
  have hs0 : (↑s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  calc
    (↑s : ℂ) * cexp (↑θ * I)
        = cexp (Complex.log ↑s) * cexp (↑θ * I) := by rw [Complex.exp_log hs0]
    _ = cexp (Complex.log ↑s + ↑θ * I) := (Complex.exp_add _ _).symm
    _ = cexp (↑(Real.log s) + ↑θ * I) := by rw [← ofReal_log hs.le]

private lemma isOpen_image_mul_exp {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) :
    IsOpen ((fun p : ℝ × ℝ ↦ (↑p.1 : ℂ) * cexp (↑p.2 * I)) '' (Ioo 0 ρ ×ˢ Ioo θ₁ θ₂)) := by
  let rect : Set (ℝ × ℝ) := Ioo 0 ρ ×ˢ Ioo θ₁ θ₂
  let L : ℝ × ℝ → ℂ := fun p ↦ ↑(Real.log p.1) + ↑p.2 * I
  have hform : (fun p : ℝ × ℝ ↦ (↑p.1 : ℂ) * cexp (↑p.2 * I)) '' rect = cexp '' (L '' rect) := by
    ext z; constructor
    · rintro ⟨p, hmem, rfl⟩
      exact ⟨L p, ⟨p, hmem, rfl⟩, (ofReal_mul_exp_eq hmem.1.1).symm⟩
    · rintro ⟨w, ⟨p, hmem, rfl⟩, rfl⟩
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
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Real.log_lt_log hp.1.1 hp.1.2, hp.2⟩
    · intro hq
      refine ⟨(rexp q.1, q.2), ⟨⟨exp_pos _, (Real.lt_log_iff_exp_lt hρ).mp hq.1⟩, hq.2⟩, ?_⟩
      simp [φ, Real.log_exp]
  have hopenφ : IsOpen (φ '' rect) := by rw [hφim]; exact isOpen_Iio.prod isOpen_Ioo
  rw [hLφ, image_comp]
  exact equivRealProdCLM.symm.isOpenMap _ hopenφ

private lemma isOpen_openSector {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) :
    IsOpen (openSector x ρ θ₁ θ₂) := by
  have h1 := isOpen_image_mul_exp (θ₁ := θ₁) (θ₂ := θ₂) hρ
  have him : openSector x ρ θ₁ θ₂ =
      (fun z : ℂ ↦ x + orthonormalBasisOneI.repr z) ''
        ((fun p : ℝ × ℝ ↦ (↑p.1 : ℂ) * cexp (↑p.2 * I)) '' (Ioo 0 ρ ×ˢ Ioo θ₁ θ₂)) := by
    simp only [openSector, ← image_comp]; rfl
  rw [him]
  let e : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    orthonormalBasisOneI.repr.toHomeomorph.trans (Homeomorph.addLeft x)
  exact e.isOpenMap _ h1

private lemma arg_mul_cexp {s θ : ℝ} (hs : 0 < s) :
    arg (↑s * cexp (↑θ * I)) = toIocMod two_pi_pos (-π) θ := by
  have hθ : (θ : Real.Angle) = ↑(toIocMod two_pi_pos (-π) θ) :=
    (Real.Angle.coe_toIocMod θ (-π)).symm
  have hcos : Real.cos θ = Real.cos (toIocMod two_pi_pos (-π) θ) := by
    have := congrArg Real.Angle.cos hθ
    rwa [Real.Angle.cos_coe, Real.Angle.cos_coe] at this
  have hsin : Real.sin θ = Real.sin (toIocMod two_pi_pos (-π) θ) := by
    have := congrArg Real.Angle.sin hθ
    rwa [Real.Angle.sin_coe, Real.Angle.sin_coe] at this
  have hexp : cexp (↑θ * I) = cexp (↑(toIocMod two_pi_pos (-π) θ) * I) := by
    rw [exp_mul_I, exp_mul_I]
    simp [← ofReal_cos, ← ofReal_sin, hcos, hsin]
  have hmem : toIocMod two_pi_pos (-π) θ ∈ Ioc (-π) π := by
    have h := toIocMod_mem_Ioc two_pi_pos (-π) θ
    rwa [show (-π + 2 * π : ℝ) = π by ring] at h
  have : ↑s * cexp (↑θ * I) =
      ↑s * (Complex.cos ↑(toIocMod two_pi_pos (-π) θ) +
        Complex.sin ↑(toIocMod two_pi_pos (-π) θ) * I) := by
    rw [hexp, exp_mul_I]
  rw [this]
  exact arg_mul_cos_add_sin_mul_I hs ⟨hmem.1, hmem.2⟩

private lemma arg_polar {s θ : ℝ} (hs : 0 < s) :
    arg (toComplex x (polar x s θ)) = toIocMod two_pi_pos (-π) θ := by
  simpa [toComplex_polar] using arg_mul_cexp hs

private lemma toIocMod_eq_of_mem_Ioc {θ : ℝ} (h : θ ∈ Ioc (-π) π) :
    toIocMod two_pi_pos (-π) θ = θ :=
  (toIocMod_eq_self two_pi_pos).mpr <| by
    have : (-π + 2 * π : ℝ) = π := by ring
    rwa [this]

private lemma nonempty_openSectorIdx (hρ : 0 < ρ) (i : Fin (argList x Y).length) :
    (openSectorIdx x ρ Y i).Nonempty :=
  (isPathConnected_openSector hρ (θLeft_lt_θRight i)).nonempty

private lemma arg_mem_argFinset_iff {θ : ℝ} :
    θ ∈ argFinset x Y ↔ ∃ i : Fin (argList x Y).length, (argList x Y).get i = θ := by
  constructor
  · intro hθ
    have hmem : θ ∈ argList x Y := (Finset.mem_sort (· ≤ ·)).mpr hθ
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hmem
    exact ⟨n, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (Finset.mem_sort (· ≤ ·)).mp <| List.get_mem (argList x Y) i

private lemma argList_get_le_of_le {i j : Fin (argList x Y).length} (hij : i ≤ j) :
    (argList x Y).get i ≤ (argList x Y).get j :=
  (argFinset x Y |>.pairwise_sort _).rel_get_of_le hij

private lemma zero_le_fin (i : Fin (argList x Y).length) :
    (⟨0, i.pos⟩ : Fin (argList x Y).length) ≤ i :=
  Fin.le_iff_val_le_val.mpr (Nat.zero_le _)

private lemma argList_get_min (i : Fin (argList x Y).length) :
    (argList x Y).get ⟨0, i.pos⟩ ≤ (argList x Y).get i :=
  argList_get_le_of_le (zero_le_fin i)

private lemma argList_get_max (i : Fin (argList x Y).length)
    (hi : ¬ ↑i + 1 < (argList x Y).length) (k : Fin (argList x Y).length) :
    (argList x Y).get k ≤ (argList x Y).get i := by
  have hki : (k : ℕ) ≤ ↑i := by omega
  exact argList_get_le_of_le (Fin.mk_le_mk.mpr hki)

private lemma toIocMod_not_mem_argFinset
    (i : Fin (argList x Y).length) {θ : ℝ} (hθ : θ ∈ Ioo (θLeft x Y i) (θRight x Y i)) :
    toIocMod two_pi_pos (-π) θ ∉ argFinset x Y := by
  intro hmem
  obtain ⟨j, hj⟩ := (arg_mem_argFinset_iff (x := x) (Y := Y)).mp hmem
  simp only [θLeft, θRight] at hθ
  split_ifs at hθ with hi
  · have hileft := argList_get_mem_Ioc (x := x) (Y := Y) i
    have hiright := argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑i + 1, hi⟩
    have hioc : θ ∈ Ioc (-π) π :=
      ⟨lt_trans hileft.1 hθ.1, le_of_lt (lt_of_lt_of_le hθ.2 hiright.2)⟩
    have hmod : θ = (argList x Y).get j := by
      rw [toIocMod_eq_of_mem_Ioc hioc] at hj; exact hj.symm
    by_cases hji : (i : ℕ) < (j : ℕ)
    · have : (⟨↑i + 1, hi⟩ : Fin _) ≤ j := Fin.mk_le_mk.mpr (by omega)
      exact (not_le_of_gt hθ.2) <| (argList_get_le_of_le this).trans_eq hmod.symm
    · have : j ≤ i := Fin.mk_le_mk.mpr (Nat.le_of_not_gt hji)
      exact (not_le_of_gt hθ.1) <| hmod ▸ argList_get_le_of_le this
  · have hid := argList_get_mem_Ioc (x := x) (Y := Y) i
    have h0 := argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, i.pos⟩
    by_cases hπ : θ ≤ π
    · have hioc : θ ∈ Ioc (-π) π := ⟨lt_trans hid.1 hθ.1, hπ⟩
      have hmod : θ = (argList x Y).get j := by
        rw [toIocMod_eq_of_mem_Ioc hioc] at hj; exact hj.symm
      exact (not_le_of_gt hθ.1) <| hmod ▸ argList_get_max i hi j
    · push Not at hπ
      have hmem' : θ - 2 * π ∈ Ioc (-π) π :=
        ⟨by linarith, by linarith [hθ.2, h0.2]⟩
      have hsub : toIocMod two_pi_pos (-π) θ = θ - 2 * π := by
        have := toIocMod_eq_of_mem_Ioc hmem'
        simpa [toIocMod_sub] using this
      have hmod : θ - 2 * π = (argList x Y).get j := by rw [hsub] at hj; exact hj.symm
      exact (not_le_of_gt (show θ - 2 * π < (argList x Y).get ⟨0, i.pos⟩ by linarith [hθ.2])) <|
        hmod ▸ argList_get_min j

private lemma subset_diskMinusRadii_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) (i : Fin (argList x Y).length) :
    openSectorIdx x ρ Y i ⊆ diskMinusRadii x ρ Y := by
  intro p hp
  obtain ⟨⟨s, θ⟩, ⟨hs, hθ⟩, rfl⟩ := hp
  have hs0 : 0 < s := hs.1
  have hball : polar x s θ ∈ ball x ρ := by
    rw [mem_ball, dist_polar, abs_of_pos hs0]; exact hs.2
  have hne : polar x s θ ≠ x := by
    intro h; have := congrArg (dist · x) h; simp [dist_polar, abs_of_pos hs0, hs0.ne'] at this
  refine (mem_diskMinusRadii_iff hρ hYne hY).mpr ⟨hball, hne, ?_⟩
  simpa [arg_polar hs0] using toIocMod_not_mem_argFinset i hθ

private lemma mem_sector_angles_subset
    {i : Fin (argList x Y).length} {θ : ℝ}
    (hθ : θ ∈ Ioo (θLeft x Y i) (θRight x Y i)) :
    θ ∈ Ioo ((argList x Y).get ⟨0, i.pos⟩) ((argList x Y).get ⟨0, i.pos⟩ + 2 * π) := by
  have h0le_i := argList_get_min i
  refine ⟨lt_of_le_of_lt h0le_i hθ.1, ?_⟩
  simp only [θLeft, θRight] at hθ
  split_ifs at hθ with hi
  · have h0le := argList_get_le_of_le (zero_le_fin ⟨↑i + 1, hi⟩)
    have hmem := argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑i + 1, hi⟩
    have h0 := argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, i.pos⟩
    linarith [hθ.2, h0le, hmem.2, h0.1]
  · exact hθ.2

private lemma abs_sub_lt_two_pi_of_mem_sector
    {i j : Fin (argList x Y).length} {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ Ioo (θLeft x Y i) (θRight x Y i))
    (hθ₂ : θ₂ ∈ Ioo (θLeft x Y j) (θRight x Y j)) :
    |θ₁ - θ₂| < 2 * π := by
  have h1 := mem_sector_angles_subset hθ₁
  have h2 := mem_sector_angles_subset (i := j) hθ₂
  have hbase : (argList x Y).get ⟨0, i.pos⟩ = (argList x Y).get ⟨0, j.pos⟩ := rfl
  rw [← hbase] at h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma disjoint_Ioo_θ (i j : Fin (argList x Y).length) (hij : i ≠ j) :
    Disjoint (Ioo (θLeft x Y i) (θRight x Y i)) (Ioo (θLeft x Y j) (θRight x Y j)) := by
  wlog hlt : (i : ℕ) < j generalizing i j
  · exact (this j i hij.symm (lt_of_le_of_ne (le_of_not_gt hlt)
      (Fin.val_injective.ne hij.symm))).symm
  refine disjoint_left.2 fun θ hθi hθj ↦ ?_
  have hchain : θRight x Y i ≤ θLeft x Y j := by
    simp only [θLeft, θRight]
    split_ifs with hi
    · exact argList_get_le_of_le (Fin.mk_le_mk.mpr (by omega))
    · omega
  linarith [hθi.2, hθj.1, hchain]

private lemma pairwiseDisjoint_openSectorIdx (_hρ : 0 < ρ) :
    Pairwise (Disjoint on openSectorIdx x ρ Y) := by
  intro i j hij
  refine disjoint_left.2 fun p hpi hpj ↦ ?_
  obtain ⟨⟨s₁, θ₁⟩, ⟨hs₁, hθ₁⟩, rfl⟩ := hpi
  obtain ⟨⟨s₂, θ₂⟩, ⟨hs₂, hθ₂⟩, heq⟩ := hpj
  have hδ := abs_sub_lt_two_pi_of_mem_sector hθ₁ hθ₂
  obtain ⟨_, hθ_eq⟩ := polar_inj hs₁.1 hs₂.1 hδ heq.symm
  exact (disjoint_Ioo_θ i j hij).ne_of_mem hθ₁ hθ₂ hθ_eq

/-- Every point of `diskMinusRadii` lies in some polar sector. -/
private lemma exists_mem_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ diskMinusRadii x ρ Y) :
    ∃ i : Fin (argList x Y).length, p ∈ openSectorIdx x ρ Y i := by
  have hp' := (mem_diskMinusRadii_iff hρ hYne hY).mp hp
  have hlen : 0 < (argList x Y).length := by
    rw [length_argList hρ hY]; exact Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr hYne)
  set α := arg (toComplex x p)
  set r := ‖toComplex x p‖
  have hr0 : 0 < r := by
    dsimp [r]; rw [norm_toComplex, norm_sub_pos_iff]; exact hp'.2.1
  have hrρ : r < ρ := by
    dsimp [r]; rw [norm_toComplex]; exact mem_ball_iff_norm.mp hp'.1
  have hpole : p = polar x r α := by
    dsimp [r, α]; exact (polar_of_toComplex hp'.2.1).symm
  have hαIoc : α ∈ Ioc (-π) π := arg_mem_Ioc _
  have hαn : α ∉ argFinset x Y := hp'.2.2
  let θ₀ := (argList x Y).get ⟨0, hlen⟩
  let θLast := (argList x Y).get ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen⟩
  by_cases hlt0 : α < θ₀
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
      · have hid := argList_get_mem_Ioc (x := x) (Y := Y) i
        have : π < α + 2 * π := by linarith [hαIoc.1]
        exact lt_of_le_of_lt hid.2 this
      · have : θ₀ = (argList x Y).get ⟨0, i.pos⟩ := rfl
        linarith [hlt0]
    · change polar x r (α + 2 * π) = p
      rw [polar_add_two_pi, ← hpole]
  · push Not at hlt0
    by_cases hgt : θLast < α
    · -- above maximum: wrap with α itself
      let i : Fin (argList x Y).length := ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen⟩
      refine ⟨i, ⟨(r, α), ⟨⟨hr0, hrρ⟩, ?_⟩, hpole.symm⟩⟩
      have hi_last : ¬ ↑i + 1 < (argList x Y).length := by
        change ¬ (argList x Y).length - 1 + 1 < (argList x Y).length
        omega
      change θLeft x Y i < α ∧ α < θRight x Y i
      simp only [θLeft, θRight, hi_last, ↓reduceDIte]
      refine ⟨hgt, ?_⟩
      have h0 := argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, hlen⟩
      linarith [hαIoc.2, h0.1]
    · -- between min and max: find consecutive gap
      push Not at hgt
      have hne0 : α ≠ θ₀ := fun h ↦
        hαn ((arg_mem_argFinset_iff).mpr ⟨⟨0, hlen⟩, h.symm⟩)
      have hαlt0 : θ₀ < α := lt_of_le_of_ne hlt0 hne0.symm
      let S := Finset.univ.filter (fun k : Fin (argList x Y).length ↦ (argList x Y).get k < α)
      have hSne : S.Nonempty := ⟨⟨0, hlen⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hαlt0⟩⟩
      let i := S.max' hSne
      have hiα : (argList x Y).get i < α := (Finset.mem_filter.mp (S.max'_mem hSne)).2
      have hi_not_last : ↑i + 1 < (argList x Y).length := by
        by_contra hlast
        have ival : (i : ℕ) = (argList x Y).length - 1 := by omega
        have hi_eq : i = ⟨(argList x Y).length - 1, Nat.sub_one_lt_of_lt hlen⟩ := Fin.ext ival
        rw [hi_eq] at hiα
        exact not_lt_of_ge hgt hiα
      have hnext : ¬ (argList x Y).get ⟨↑i + 1, hi_not_last⟩ < α := by
        intro hlt
        have hmem : ⟨↑i + 1, hi_not_last⟩ ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        have := S.le_max' _ hmem
        exact Nat.not_succ_le_self _ <| Fin.le_iff_val_le_val.mp this
      have hαlt : α < (argList x Y).get ⟨↑i + 1, hi_not_last⟩ :=
        lt_of_le_of_ne (le_of_not_gt hnext) fun h ↦
          hαn ((arg_mem_argFinset_iff).mpr ⟨⟨↑i + 1, hi_not_last⟩, h.symm⟩)
      refine ⟨i, ⟨(r, α), ⟨⟨hr0, hrρ⟩, ?_⟩, hpole.symm⟩⟩
      change θLeft x Y i < α ∧ α < θRight x Y i
      simp only [θLeft, θRight, hi_not_last, ↓reduceDIte]
      exact ⟨hiα, hαlt⟩

private lemma iUnion_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) :
    ⋃ i : Fin (argList x Y).length, openSectorIdx x ρ Y i = diskMinusRadii x ρ Y := by
  ext p; constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact subset_diskMinusRadii_openSectorIdx hρ hYne hY i hi
  · intro hp
    obtain ⟨i, hi⟩ := exists_mem_openSectorIdx hρ hYne hY hp
    exact mem_iUnion.mpr ⟨i, hi⟩

private lemma connectedComponentIn_eq_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) {p : EuclideanSpace ℝ (Fin 2)}
    {i : Fin (argList x Y).length} (hp : p ∈ openSectorIdx x ρ Y i) :
    connectedComponentIn (diskMinusRadii x ρ Y) p = openSectorIdx x ρ Y i := by
  have hsub := subset_diskMinusRadii_openSectorIdx hρ hYne hY i
  have hpD : p ∈ diskMinusRadii x ρ Y := hsub hp
  have hconn : IsConnected (openSectorIdx x ρ Y i) :=
    (isPathConnected_openSector hρ (θLeft_lt_θRight i)).isConnected
  have hsubset : openSectorIdx x ρ Y i ⊆ connectedComponentIn (diskMinusRadii x ρ Y) p :=
    hconn.isPreconnected.subset_connectedComponentIn hp hsub
  refine subset_antisymm ?_ hsubset
  have hopen : IsOpen (openSectorIdx x ρ Y i) := isOpen_openSector hρ
  have hU : connectedComponentIn (diskMinusRadii x ρ Y) p ⊆
      openSectorIdx x ρ Y i ∪
        ⋃ j ∈ ({i}ᶜ : Set (Fin (argList x Y).length)), openSectorIdx x ρ Y j := by
    intro q hq
    have hqD := connectedComponentIn_subset _ _ hq
    rw [← iUnion_openSectorIdx hρ hYne hY] at hqD
    obtain ⟨j, hj⟩ := mem_iUnion.mp hqD
    by_cases hji : j = i
    · left; rwa [hji] at hj
    · right; exact mem_biUnion hji hj
  have hVopen : IsOpen (⋃ j ∈ ({i}ᶜ : Set (Fin _)), openSectorIdx x ρ Y j) :=
    isOpen_biUnion fun _ _ ↦ isOpen_openSector hρ
  have hdisj : Disjoint (openSectorIdx x ρ Y i)
      (⋃ j ∈ ({i}ᶜ : Set (Fin _)), openSectorIdx x ρ Y j) :=
    disjoint_iUnion₂_right.mpr fun j hj ↦ pairwiseDisjoint_openSectorIdx hρ (Ne.symm hj)
  have hpre : IsPreconnected (connectedComponentIn (diskMinusRadii x ρ Y) p) :=
    isPreconnected_connectedComponentIn
  rcases hpre.subset_or_subset hopen hVopen hdisj hU with h | h
  · exact h
  · exfalso
    have : p ∈ ⋃ j ∈ ({i}ᶜ : Set (Fin _)), openSectorIdx x ρ Y j :=
      h (mem_connectedComponentIn hpD)
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp this
    exact (pairwiseDisjoint_openSectorIdx hρ (Ne.symm hj)).ne_of_mem hp hpj rfl

private lemma sectors_eq_range_openSectorIdx (hρ : 0 < ρ) (hYne : Y.Nonempty)
    (hY : ↑Y ⊆ sphere x ρ) :
    sectors x ρ Y = range (openSectorIdx x ρ Y) := by
  ext C; constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := exists_mem_openSectorIdx hρ hYne hY hp
    exact ⟨i, (connectedComponentIn_eq_openSectorIdx hρ hYne hY hi).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨p, hp⟩ := nonempty_openSectorIdx hρ i
    exact ⟨p, subset_diskMinusRadii_openSectorIdx hρ hYne hY i hp,
      connectedComponentIn_eq_openSectorIdx hρ hYne hY hp⟩

private lemma injective_openSectorIdx (hρ : 0 < ρ) :
    Function.Injective (openSectorIdx x ρ Y) := by
  intro i j hij
  by_contra hne
  obtain ⟨p, hp⟩ := nonempty_openSectorIdx hρ i
  have hpj : p ∈ openSectorIdx x ρ Y j := hij ▸ hp
  exact (pairwiseDisjoint_openSectorIdx hρ hne).ne_of_mem hp hpj rfl

/-- **There are exactly `d` sectors.** -/
theorem ncard_sectors (hρ : 0 < ρ) (hYne : Y.Nonempty) (hY : ↑Y ⊆ sphere x ρ) :
    (sectors x ρ Y).ncard = Y.card := by
  rw [sectors_eq_range_openSectorIdx hρ hYne hY,
    ncard_range_of_injective (injective_openSectorIdx hρ),
    Nat.card_eq_fintype_card, Fintype.card_fin, length_argList hρ hY]

/- **Proof route for `ncard_sectors_closure_eq_two`** (formalisation helper).

`mem_closure_of_mem_sectors` below is now proved; the two things it was missing were a *statement*
fix — it needed `hYne` and `hY` like its siblings, so that `sectors_eq_range_openSectorIdx` applies,
and that was mine to supply — and the idiom `image_closure_subset_closure_image` against the
existing `continuous_uncurry_polar`. Eleven lines, no new API. The route for the one below is the
same shape but harder, because it has to identify *which* sectors have `p` in their closure, not
just exhibit one: fix the radius `[x, y]` through `p`, and show that the sectors adjacent to it are
exactly the two indices `i` with `θLeft x Y i = arg (toComplex x y)` or
`θRight x Y i = arg (toComplex x y)`, then that no other sector reaches `p`. The last step is where
`polar_inj` and `disjoint_Ioo_θ` are used, and where `1 < Y.card` is needed.

*Rejected alternative, recorded so it is not re-proposed.* `Complex.polarCoord`
(`Mathlib/Analysis/SpecialFunctions/PolarCoord.lean:181`) was considered when this file was written
and deliberately not used. The reasons given, and their status:

* *"It does not touch the partition, component or count argument, only openness boilerplate."*
  **Correct.** The counting in this file stands on its own and no chart shortens it. Any claim that
  adopting `polarCoord` would produce the missing theorems was wrong; `mem_closure_of_mem_sectors`
  is the evidence — it fell to the existing `polar`, with no chart involved.
* *"Its cut is fixed at `π`, so `polarCoord.symm '' (Ioo 0 ρ ×ˢ Ioo θ₁ θ₂)` matches `openSector`
  only when `(θ₁, θ₂) ⊆ (-π, π)`; the wrap sector and the `d = 1` full turn cross the cut."*
  **Correct for a fixed cut, but not an obstruction**, because the cut can be moved onto one of the
  removed radii. With

      polarCoordAt (θ₀ : ℝ) : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
        ((Homeomorph.mulLeft₀ (cexp (-(θ₀ : ℂ) * I)) (Complex.exp_ne_zero _)
          ).transOpenPartialHomeomorph Complex.polarCoord).transHomeomorph
          (Homeomorph.addRight ((0, θ₀) : ℝ × ℝ))

  one gets `target = Ioi 0 ×ˢ Ioo (θ₀ - π) (θ₀ + π)`, a window of width exactly `2 * π`. Taking
  `θ₀ := (θ₁ + θ₂) / 2` puts *every* gap inside it, since gap widths sum to `2 * π`; the `d = 1`
  full turn fits with equality at both ends, because the intervals are open. Compiled against this
  pin, so this is a fact and not a suggestion. It needs
  `Mathlib.Topology.OpenPartialHomeomorph.Constructions` for `transHomeomorph`, and
  `.symm p = p.1 * cexp (p.2 * I)` is not `rfl` (`Homeomorph.mulLeft₀`'s inverse hides behind an
  unexposed `mulAux`).

So the live question is narrower than a rewrite: whether replacing `isOpen_openSector`,
`isOpen_image_mul_exp`, `ofReal_mul_exp_eq`, `polar_inj`, `arg_polar`, `arg_mul_cexp`,
`polar_add_two_pi` and the `toIocMod` block with one chart is worth doing *after*
`ncard_sectors_closure_eq_two` lands. It is not a prerequisite for it. If it is done, `polarCoordAt`
belongs in `Matroid/ForMathlib/Analysis/SpecialFunctions/`, not `private` here. -/

private lemma closure_openSector {θ₁ θ₂ : ℝ} (hρ : 0 < ρ) (hθ : θ₁ < θ₂) :
    closure (openSector x ρ θ₁ θ₂) =
      (uncurry (polar x)) '' (Icc (0 : ℝ) ρ ×ˢ Icc θ₁ θ₂) := by
  have hcl : closure (Ioo (0 : ℝ) ρ ×ˢ Ioo θ₁ θ₂) = Icc 0 ρ ×ˢ Icc θ₁ θ₂ := by
    rw [closure_prod_eq, closure_Ioo hρ.ne, closure_Ioo hθ.ne]
  refine subset_antisymm ?_ ?_
  · have hclosed : IsClosed ((uncurry (polar x)) '' (Icc (0 : ℝ) ρ ×ˢ Icc θ₁ θ₂)) :=
      (isCompact_Icc.prod isCompact_Icc).image (continuous_uncurry_polar x) |>.isClosed
    refine (IsClosed.closure_subset_iff hclosed).mpr ?_
    exact image_mono fun _ hp ↦ ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  · rw [← hcl]
    exact image_closure_subset_closure_image (continuous_uncurry_polar x)

private lemma θRight_sub_θLeft_lt_two_pi (hd : 1 < (argList x Y).length)
    (i : Fin (argList x Y).length) :
    θRight x Y i - θLeft x Y i < 2 * π := by
  simp only [θLeft, θRight]
  split_ifs with hi
  · have hL := argList_get_mem_Ioc (x := x) (Y := Y) i
    have hR := argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑i + 1, hi⟩
    linarith [hL.1, hR.2]
  · have hlt : (argList x Y).get ⟨0, i.pos⟩ < (argList x Y).get i :=
      argList_get_lt (by change 0 < (i : ℕ); omega)
    linarith

private lemma θLeft_gt_neg_pi (i : Fin (argList x Y).length) : -π < θLeft x Y i :=
  (argList_get_mem_Ioc (x := x) (Y := Y) i).1

private lemma θRight_le_three_pi (i : Fin (argList x Y).length) : θRight x Y i ≤ 3 * π := by
  simp only [θRight]
  split_ifs with hi
  · linarith [(argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑i + 1, hi⟩).2, Real.pi_pos]
  · linarith [(argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, i.pos⟩).2, Real.pi_pos]

private lemma polar_eq_iff_angle {s θ₁ θ₂ : ℝ} (hs : 0 < s) :
    polar x s θ₁ = polar x s θ₂ ↔ ∃ n : ℤ, θ₁ = θ₂ + (n : ℝ) * (2 * π) := by
  constructor
  · intro h
    have hexp : cexp (↑θ₁ * I) = cexp (↑θ₂ * I) := by
      have hceq : (s : ℂ) * cexp (↑θ₁ * I) = ↑s * cexp (↑θ₂ * I) := by
        simpa [toComplex_polar] using congrArg (toComplex x) h
      exact mul_left_cancel₀ (ofReal_ne_zero.mpr hs.ne') hceq
    have h1 : cexp (↑(θ₁ - θ₂) * I) = 1 := by
      rw [ofReal_sub, sub_mul, Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have hn' : (↑(θ₁ - θ₂) : ℂ) * I = ↑((n : ℝ) * (2 * π)) * I := by
      convert hn using 1; push_cast; ring
    have := ofReal_mul_I_eq_iff.mp hn'
    linarith
  · rintro ⟨n, rfl⟩
    unfold polar
    congr 1
    have hmul :
        cexp (↑(θ₂ + (n : ℝ) * (2 * π)) * I) =
          cexp (↑θ₂ * I) * cexp (↑((n : ℝ) * (2 * π)) * I) := by
      rw [ofReal_add, add_mul, Complex.exp_add]
    have hone : cexp (↑((n : ℝ) * (2 * π)) * I) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨n, by push_cast; ring⟩
    rw [hmul, hone, mul_one]

private lemma exists_get_eq_arg {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Y) :
    ∃ i : Fin (argList x Y).length, (argList x Y).get i = arg (toComplex x y) :=
  (arg_mem_argFinset_iff (x := x) (Y := Y)).mp <|
    Finset.mem_image.mpr ⟨y, hy, rfl⟩

private lemma get_eq_arg_unique {i j : Fin (argList x Y).length}
    (hij : (argList x Y).get i = (argList x Y).get j) : i = j :=
  (argFinset x Y |>.sort_nodup _).get_inj_iff.mp hij

private abbrev isEndpoint (α : ℝ) (i : Fin (argList x Y).length) : Prop :=
  θLeft x Y i = α ∨ θRight x Y i = α ∨ θRight x Y i = α + 2 * π

/-- On a removed radius (away from the centre), a sector meets `p` in its closure iff that radius
is one of the two angular endpoints of the sector. -/
private lemma mem_closure_openSectorIdx_iff (hρ : 0 < ρ)
    {p : EuclideanSpace ℝ (Fin 2)} (hr : 0 < ‖p - x‖) (hrρ : ‖p - x‖ < ρ)
    (hα : arg (toComplex x p) ∈ argFinset x Y) (i : Fin (argList x Y).length) :
    p ∈ closure (openSectorIdx x ρ Y i) ↔ isEndpoint (arg (toComplex x p)) i := by
  set α := arg (toComplex x p)
  set r := ‖p - x‖
  have hr0 : 0 < r := hr
  have hpx : p ≠ x := norm_sub_pos_iff.mp hr
  have hpole : polar x r α = p := by
    simpa [r, α, norm_toComplex] using polar_of_toComplex hpx
  have hαIoc : α ∈ Ioc (-π) π := arg_mem_Ioc _
  constructor
  · intro hp
    change p ∈ closure (openSector x ρ (θLeft x Y i) (θRight x Y i)) at hp
    rw [closure_openSector hρ (θLeft_lt_θRight i)] at hp
    obtain ⟨⟨s, θ⟩, ⟨hs, hθ⟩, hpol⟩ := hp
    change polar x s θ = p at hpol
    have hs0 : 0 < s := lt_of_le_of_ne hs.1 fun hs00 ↦
      hpx <| by simpa [polar, hs00.symm] using hpol.symm
    have hs_eq : s = r := by
      have h1 : dist (polar x s θ) x = s := by simp [dist_polar, abs_of_pos hs0]
      have h2 : dist p x = r := by simp [r, dist_eq_norm_sub]
      linarith [congrArg (dist · x) hpol ▸ h1, h2]
    subst hs_eq
    have hpol' : polar x r θ = polar x r α := hpol.trans hpole.symm
    obtain ⟨n, hn⟩ := (polar_eq_iff_angle hr0).mp hpol'
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
    have hnot_int2 : α + 2 * π ∉ Ioo (θLeft x Y i) (θRight x Y i) := fun hmem ↦ by
      have hmod : toIocMod two_pi_pos (-π) (α + 2 * π) = α := by
        simpa [one_zsmul, toIocMod_eq_of_mem_Ioc hαIoc] using
          toIocMod_add_zsmul two_pi_pos (-π) α (1 : ℤ)
      exact toIocMod_not_mem_argFinset (x := x) (Y := Y) i hmem (by simpa [hmod, α] using hα)
    rcases hn01 with rfl | rfl
    · have hθα : θ = α := by simp [hn]
      subst hθα
      rcases eq_or_lt_of_le hθ.1 with hL | hL
      · exact Or.inl hL
      · rcases eq_or_lt_of_le hθ.2 with hR | hR
        · exact Or.inr (Or.inl hR.symm)
        · exact (hnot_int ⟨hL, hR⟩).elim
    · have hθα : θ = α + 2 * π := by
        rw [hn]; push_cast; ring
      subst hθα
      rcases eq_or_lt_of_le hθ.1 with hL | hL
      · have : θLeft x Y i ≤ π := (argList_get_mem_Ioc (x := x) (Y := Y) i).2
        linarith [hL, hαIoc.1]
      · rcases eq_or_lt_of_le hθ.2 with hR | hR
        · exact Or.inr (Or.inr hR.symm)
        · exact (hnot_int2 ⟨hL, hR⟩).elim
  · intro h
    change p ∈ closure (openSector x ρ (θLeft x Y i) (θRight x Y i))
    rw [closure_openSector hρ (θLeft_lt_θRight i)]
    rcases h with hL | hR | hRw
    · refine ⟨(r, α), ⟨⟨hr0.le, hrρ.le⟩, ?_⟩, hpole⟩
      rw [← hL]; exact ⟨le_rfl, (θLeft_lt_θRight i).le⟩
    · refine ⟨(r, α), ⟨⟨hr0.le, hrρ.le⟩, ?_⟩, hpole⟩
      rw [← hR]; exact ⟨(θLeft_lt_θRight i).le, le_rfl⟩
    · refine ⟨(r, α + 2 * π), ⟨⟨hr0.le, hrρ.le⟩, ?_⟩, ?_⟩
      · rw [← hRw]; exact ⟨(θLeft_lt_θRight i).le, le_rfl⟩
      · change polar x r (α + 2 * π) = p
        rw [polar_add_two_pi, hpole]

private lemma card_endpoint_eq_two (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) (hd : 1 < Y.card)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Y) :
    (Finset.univ.filter fun i : Fin (argList x Y).length ↦
      isEndpoint (arg (toComplex x y)) i).card = 2 := by
  classical
  have hlen_eq : (argList x Y).length = Y.card := length_argList hρ hY
  have hlen : 1 < (argList x Y).length := by rw [hlen_eq]; exact hd
  obtain ⟨k, hk⟩ := exists_get_eq_arg (x := x) (Y := Y) hy
  set α := arg (toComplex x y)
  have hαIoc : α ∈ Ioc (-π) π := by simpa [α] using arg_mem_Ioc (toComplex x y)
  have hRight : isEndpoint α k := Or.inl (by simpa [θLeft, α] using hk)
  let S := Finset.univ.filter fun i : Fin (argList x Y).length ↦ isEndpoint α i
  have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hRight⟩
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
      have : (⟨0, iLast.pos⟩ : Fin (argList x Y).length) = k := Fin.ext hk0.symm
      simpa [this, α] using hk
    have hiS : iLast ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWrap⟩
    have hS : S ⊆ ({k, iLast} : Finset _) := by
      intro m hm
      have hm' : isEndpoint α m := (Finset.mem_filter.mp hm).2
      refine Finset.mem_insert.mpr ?_
      rcases hm' with hL | hR | hRw
      · exact Or.inl (get_eq_arg_unique (hL.trans hk.symm))
      · simp only [θRight] at hR
        split_ifs at hR with hm'
        · have heq : (⟨↑m + 1, hm'⟩ : Fin _) = k :=
            get_eq_arg_unique (hR.trans hk.symm)
          have : (m : ℕ) + 1 = 0 := by simpa [hk0] using congrArg Fin.val heq
          exact (Nat.succ_ne_zero _).elim this
        · have h0 := argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, m.pos⟩
          linarith [h0.1, hαIoc.2]
      · simp only [θRight] at hRw
        split_ifs at hRw with hm'
        · have hmem := argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑m + 1, hm'⟩
          linarith [hmem.2, hαIoc.1]
        · have : (m : ℕ) = (argList x Y).length - 1 := by omega
          exact Or.inr (Finset.mem_singleton.mpr (Fin.ext this))
    have hcard : ({k, iLast} : Finset _).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hne),
        Finset.card_singleton]
    exact le_antisymm (Finset.card_le_card hS |>.trans hcard.le) <| by
      have : ({k, iLast} : Finset _) ⊆ S := by
        intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hkS
        · rw [Finset.mem_singleton] at hm; rwa [hm]
      exact hcard.symm.le.trans (Finset.card_le_card this)
  · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
    have hiPred_lt : (k : ℕ) - 1 < (argList x Y).length :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt
    let iPred : Fin (argList x Y).length := ⟨(k : ℕ) - 1, hiPred_lt⟩
    have hne : k ≠ iPred := by
      intro h
      have : (k : ℕ) = (k : ℕ) - 1 := congrArg Fin.val h
      omega
    have hpred_succ : ↑iPred + 1 < (argList x Y).length := by
      change (k : ℕ) - 1 + 1 < (argList x Y).length
      simpa [Nat.sub_add_cancel hkpos] using k.isLt
    have hLeft : isEndpoint α iPred := by
      refine Or.inr (Or.inl ?_)
      simp only [θRight, hpred_succ, ↓reduceDIte]
      have : (⟨↑iPred + 1, hpred_succ⟩ : Fin _) = k :=
        Fin.ext (by change (k : ℕ) - 1 + 1 = (k : ℕ); omega)
      simpa [this, α] using hk
    have hiS : iPred ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLeft⟩
    have hS : S ⊆ ({k, iPred} : Finset _) := by
      intro m hm
      have hm' : isEndpoint α m := (Finset.mem_filter.mp hm).2
      refine Finset.mem_insert.mpr ?_
      rcases hm' with hL | hR | hRw
      · exact Or.inl (get_eq_arg_unique (hL.trans hk.symm))
      · simp only [θRight] at hR
        split_ifs at hR with hm'
        · have heq : (⟨↑m + 1, hm'⟩ : Fin _) = k :=
            get_eq_arg_unique (hR.trans hk.symm)
          exact Or.inr (Finset.mem_singleton.mpr (Fin.ext (Nat.eq_sub_of_add_eq
            (congrArg Fin.val heq))))
        · have h0 := argList_get_mem_Ioc (x := x) (Y := Y) ⟨0, m.pos⟩
          linarith [h0.1, hαIoc.2]
      · simp only [θRight] at hRw
        split_ifs at hRw with hm'
        · have hmem := argList_get_mem_Ioc (x := x) (Y := Y) ⟨↑m + 1, hm'⟩
          linarith [hmem.2, hαIoc.1]
        · have : (argList x Y).get ⟨0, m.pos⟩ = α := by linarith
          have : k = ⟨0, k.pos⟩ := get_eq_arg_unique (hk.trans this.symm)
          exact (hk0 (congrArg Fin.val this)).elim
    have hcard : ({k, iPred} : Finset _).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hne),
        Finset.card_singleton]
    exact le_antisymm (Finset.card_le_card hS |>.trans hcard.le) <| by
      have : ({k, iPred} : Finset _) ⊆ S := by
        intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hkS
        · rw [Finset.mem_singleton] at hm; rwa [hm]
      exact hcard.symm.le.trans (Finset.card_le_card this)

private lemma arg_eq_of_mem_segment_radius (hρ : 0 < ρ) {y p : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ sphere x ρ) (hp : p ∈ segment ℝ x y \ {x, y}) :
    0 < ‖p - x‖ ∧ ‖p - x‖ < ρ ∧ arg (toComplex x p) = arg (toComplex x y) := by
  have hp' : p ∈ segment ℝ x y := hp.1
  have hpx : p ≠ x := by
    intro h; exact hp.2 (Or.inl h)
  have hpy : p ≠ y := by
    intro h; exact hp.2 (Or.inr h)
  have hball : p ∈ ball x ρ := by
    -- interior of segment to a sphere point lies in the open ball
    rw [segment_eq_image_lineMap] at hp'
    obtain ⟨t, ht, rfl⟩ := hp'
    have ht0 : t ≠ 0 := fun h ↦ hpx (by simp [AffineMap.lineMap_apply, h])
    have ht1 : t ≠ 1 := fun h ↦ hpy (by simp [AffineMap.lineMap_apply, h])
    have htIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 ht1⟩
    have hnormy : ‖y - x‖ = ρ := mem_sphere_iff_norm.mp hy
    rw [mem_ball, dist_eq_norm_sub, lineMap_sub_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, hnormy]
    exact mul_lt_of_lt_one_left hρ htIoo.2
  have hr : 0 < ‖p - x‖ := norm_sub_pos_iff.mpr hpx
  have hrρ : ‖p - x‖ < ρ := mem_ball_iff_norm.mp hball
  have harg : arg (toComplex x p) = arg (toComplex x y) := by
    have := (mem_segment_iff_arg hρ hy hball).mp hp'
    exact (this.resolve_left hpx)
  exact ⟨hr, hrρ, harg⟩

/-- **Adjacency.** A point in the relative interior of one of the radii lies in the closure of
exactly two sectors — the two on either side of that radius. For `d = 1` the same sector lies on
both sides, and the count is one; that case is excluded here by `1 < Y.card`, which is the only
case the consumers need. -/
theorem ncard_sectors_closure_eq_two (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere x ρ) (hd : 1 < Y.card)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Y) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ segment ℝ x y \ {x, y}) :
    {C ∈ sectors x ρ Y | p ∈ closure C}.ncard = 2 := by
  classical
  have hYne : Y.Nonempty := Finset.card_pos.mp (lt_trans Nat.zero_lt_one hd)
  obtain ⟨hr, hrρ, harg⟩ := arg_eq_of_mem_segment_radius hρ (hY hy) hp
  have hα : arg (toComplex x p) ∈ argFinset x Y := by
    rw [harg]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  set α := arg (toComplex x y)
  let S := Finset.univ.filter fun i : Fin (argList x Y).length ↦ isEndpoint α i
  have hScard : S.card = 2 := by
    simpa [S, α] using card_endpoint_eq_two hρ hY hd hy
  have hsectors : sectors x ρ Y = range (openSectorIdx x ρ Y) :=
    sectors_eq_range_openSectorIdx hρ hYne hY
  have hset :
      {C ∈ sectors x ρ Y | p ∈ closure C} =
        (openSectorIdx x ρ Y) '' (S : Set _) := by
    ext C
    constructor
    · intro hC
      obtain ⟨hCsec, hpC⟩ := hC
      rw [hsectors] at hCsec
      obtain ⟨i, rfl⟩ := hCsec
      refine ⟨i, ?_, rfl⟩
      have : isEndpoint (arg (toComplex x p)) i :=
        (mem_closure_openSectorIdx_iff hρ hr hrρ hα i).mp hpC
      exact Finset.mem_coe.mpr <| Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [α, harg] using this⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' : isEndpoint α i := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      refine ⟨?_, ?_⟩
      · rw [hsectors]; exact ⟨i, rfl⟩
      · exact (mem_closure_openSectorIdx_iff hρ hr hrρ hα i).mpr (by simpa [α, harg] using hi')
  rw [hset, ncard_image_of_injective _ (injective_openSectorIdx hρ), ncard_coe_finset, hScard]

/-- Every sector has the centre in its closure. Used to pass from a sector at a point of the drawing
to the point itself. -/
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
