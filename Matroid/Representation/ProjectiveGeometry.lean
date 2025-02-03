import Matroid.Representation.Minor
import Matroid.Rank.Cardinal
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Basic

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Submodule Set

lemma Submodule.mem_span_singleton₀ {x y : W} (hx : x ≠ 0) :
    x ∈ span 𝔽 {y} ↔ ∃ (a : 𝔽ˣ), a • y = x := by
  rw [mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Units.mk0 a (by rintro rfl; simp at hx), by simp⟩
  rintro ⟨a, rfl⟩
  exact ⟨a, rfl⟩



-- @[simp] lemma Projectivization.span_range_rep

@[simp] lemma Projectivization.span_range_rep (𝔽 W : Type*) [DivisionRing 𝔽] [AddCommGroup W]
    [Module 𝔽 W] : span 𝔽 (range (Projectivization.rep (K := 𝔽) (V := W))) = ⊤ := by
  have b := Basis.ofVectorSpace 𝔽 W
  ext x
  simp only [mem_top, iff_true]
  refine mem_of_mem_of_subset (b.mem_span x) (span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  have hi0 := b.ne_zero i
  have hmem : b i ∈ span 𝔽 {(mk (K := 𝔽) (V := W) (b i) hi0).rep} := by
    rw [mem_span_singleton₀ (b.ne_zero i), ← mk_eq_mk_iff _ _ _ hi0]
    · simp only [mk_rep]
    exact rep_nonzero (mk 𝔽 (b i) hi0)
  exact mem_of_mem_of_subset hmem <| span_mono <| by simp


namespace Matroid

@[simps! E] noncomputable def ProjectiveGeometry (𝔽 W : Type*) [DivisionRing 𝔽] [AddCommGroup W]
    [Module 𝔽 W] : Matroid (Projectivization 𝔽 W) :=
  Matroid.ofFun 𝔽 Set.univ Projectivization.rep

noncomputable def ProjectiveGeometryRep : (ProjectiveGeometry 𝔽 W).Rep 𝔽 W :=
  repOfFun ..

lemma projectiveGeometryRep_fullRank : (ProjectiveGeometryRep (𝔽 := 𝔽) (W := W)).FullRank := by
  rw [Rep.FullRank, ProjectiveGeometryRep, ← image_univ, repOfFun_image_eq, image_univ,
    Projectivization.span_range_rep]

/-- The projective geometry of rank `n+1` over `GF(p^t)`.-/
noncomputable def PG (n p t : ℕ) [Fact p.Prime] :=
    Matroid.ProjectiveGeometry (GaloisField p t) (Fin (n+1) → GaloisField p t)

instance projectiveGeometry_finitary : Finitary (ProjectiveGeometry 𝔽 W) :=
  matroidOfFun_finitary ..

/-- TODO: Generalize this to arbitrary fullrank representations -/
@[simp] lemma projectiveGeometry_cRank : (ProjectiveGeometry 𝔽 W).cRank = Module.rank 𝔽 W := by
  obtain ⟨B, hB⟩ := (ProjectiveGeometry 𝔽 W).exists_base
  have hr := (projectiveGeometryRep_fullRank.basis_of_base hB).mk_eq_rank
  simp only [Cardinal.lift_id] at hr
  rw [← hr, hB.cardinalMk_eq_cRank]

@[simp] lemma projectiveGeometry_rank : (ProjectiveGeometry 𝔽 W).rank = Module.finrank 𝔽 W := by
  rw [← cRank_toNat, projectiveGeometry_cRank]
  rfl

@[simp] lemma PG_rank (n p t : ℕ) [Fact p.Prime] : (PG n p t).rank = n+1 := by
  simp [PG]

lemma Representable.exists_isoRestr_projectiveGeometry [M.Simple] (h : M.Representable 𝔽)
    (hB : M.Base B) : ∃ (i : M ≤ir ProjectiveGeometry 𝔽 (B →₀ 𝔽)), i.Spanning := by

  have v := h.some.standardRep' hB
  refine ⟨⟨fun (e : M.E) ↦ ?_, ?_, ?_⟩ , ?_⟩
  · exact ⟨Projectivization.mk 𝔽 (v e.1) (v.ne_zero_of_nonloop (toNonloop (e := e.1) e.2)), by simp⟩
  · sorry
  · intro I
    rw [ProjectiveGeometryRep.indep_iff]
    simp
