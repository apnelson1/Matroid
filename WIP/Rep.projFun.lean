import Matroid.Representation.Minor
import Matroid.Rank.Cardinal
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Matroid.ForMathlib.LinearAlgebra.Projective

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Projectivization Projectivization.Subspace

namespace Matroid


section projFun

noncomputable def Rep.projFun [Nontrivial W] [DecidableEq W] (v : M.Rep 𝔽 W)
    (e : α) : Projectivization 𝔽 W :=
  if he : v e ≠ 0 then Projectivization.mk 𝔽 (v e) he else Classical.arbitrary _

lemma nontrivial_of_rkPos [RkPos M] (v : M.Rep 𝔽 W) : Nontrivial W where
  exists_pair_ne := ⟨_, 0, v.ne_zero_of_nonloop M.exists_nonloop.choose_spec⟩

variable [Nontrivial W] [DecidableEq W]

lemma Rep.projFun_nonloop_eq (v : M.Rep 𝔽 W) (he : M.Nonloop e) :
    v.projFun e = Projectivization.mk 𝔽 (v e) (v.ne_zero_of_nonloop he) := by
  rw [Rep.projFun, dif_pos]

lemma Rep.projFun_eq [M.Loopless] (v : M.Rep 𝔽 W) (he : e ∈ M.E) :
    v.projFun e = Projectivization.mk 𝔽 (v e) (v.ne_zero_of_nonloop (toNonloop he)) := by
  rw [Rep.projFun, dif_pos]

lemma Rep.projFun_not_nonloop_eq (v : M.Rep 𝔽 W) (he : ¬ M.Nonloop e) :
    v.projFun e = Classical.arbitrary _ := by
  rw [Rep.projFun, dif_neg]
  rwa [v.ne_zero_iff_nonloop]

lemma Rep.projFun_injOn [M.Simple] (v : M.Rep 𝔽 W) : InjOn v.projFun M.E := by
  intro x hx y hy hxy
  rwa [v.projFun_nonloop_eq (toNonloop hx), v.projFun_nonloop_eq (toNonloop hy),
    Projectivization.mk_eq_mk_iff, ← v.parallel_iff' (toNonloop hx), parallel_iff_eq] at hxy

lemma Rep.indep_iff_projFun [M.Loopless] (v : M.Rep 𝔽 W) (hIE : I ⊆ M.E) :
    M.Indep I ↔ (Independent (fun x : I ↦ v.projFun x)) := by
  rw [v.indep_iff, Projectivization.linearIndependent_iff]
  · convert Iff.rfl with e
    simp [v.projFun_eq (hIE e.2)]
  simp [show ∀ e ∈ I, v e ≠ 0 from fun e heI ↦ v.ne_zero_of_nonloop (toNonloop (hIE heI))]

@[simp]
lemma Rep.independent_image_projFun_iff [M.Simple] (v : M.Rep 𝔽 W) (hIE : I ⊆ M.E) :
    Independent (fun (x : (v.projFun '' I)) ↦ x.1) ↔ M.Indep I := by
  rw [v.indep_iff_projFun hIE]
  let e : I ≃ (v.projFun '' I) :=
    Equiv.Set.imageOfInjOn v.projFun I (v.projFun_injOn.mono hIE)
  exact (Projectivization.independent_equiv e).symm

variable {𝔽 W : Type*} [Field 𝔽] [AddCommGroup W] [Module 𝔽 W] [Nontrivial W] [DecidableEq W]

lemma Rep.closure_eq_span_image_projFun [M.Loopless] (v : M.Rep 𝔽 W) (hXE : X ⊆ M.E) :
    M.closure X = v.projFun ⁻¹' (span (V := W) (K := 𝔽) (v.projFun '' X)) := by
  _

end projFun

@[simps! E] noncomputable def projectiveGeometry (𝔽 W : Type*) [DivisionRing 𝔽] [AddCommGroup W]
    [Module 𝔽 W] : Matroid (Projectivization 𝔽 W) :=
  Matroid.ofFun 𝔽 Set.univ Projectivization.rep

noncomputable def projectiveGeometryRep : (projectiveGeometry 𝔽 W).Rep 𝔽 W :=
  repOfFun ..

@[simp] lemma projectiveGeometryRep_apply_eq (e : Projectivization 𝔽 W) :
    projectiveGeometryRep e = e.rep :=
  repOfFun_apply _ (mem_univ e)

@[simp] lemma projectiveGeometry_eq_empty [Subsingleton W] :
    projectiveGeometry 𝔽 W = emptyOn (Projectivization 𝔽 W) :=
  eq_emptyOn (α := Projectivization 𝔽 W) _

lemma projectiveGeometryRep_fullRank : (projectiveGeometryRep (𝔽 := 𝔽) (W := W)).FullRank := by
  rw [Rep.FullRank, projectiveGeometryRep, ← image_univ, repOfFun_image_eq, image_univ,
    Projectivization.submodule_span_range_rep]

instance : (projectiveGeometry 𝔽 W).Loopless := by
  simp_rw [loopless_iff_forall_nonloop]
  rintro e -
  rw [← projectiveGeometryRep.ne_zero_iff_nonloop, projectiveGeometryRep,
    repOfFun_apply _ (by simp)]
  exact rep_nonzero e

lemma projectiveGeometry_indep_iff {I : Set (Projectivization 𝔽 W)} :
    (projectiveGeometry 𝔽 W).Indep I ↔ Projectivization.Independent (fun (x : I) ↦ x.1) := by
  classical
  obtain hW | hW := subsingleton_or_nontrivial W
  · simp [eq_empty_of_isEmpty I]
  rw [projectiveGeometryRep.indep_iff_projFun (by simp)]
  convert Iff.rfl with e
  rw [Rep.projFun_eq _ (by simp)]
  simp

lemma Rep.indep_image_projFun_iff [Nontrivial W] [DecidableEq W] [M.Simple] (v : M.Rep 𝔽 W)
    (hIE : I ⊆ M.E) : (projectiveGeometry 𝔽 W).Indep (v.projFun '' I) ↔ M.Indep I := by
  rwa [projectiveGeometry_indep_iff, v.independent_image_projFun_iff]

instance projectiveGeometry_simple : (projectiveGeometry 𝔽 W).Simple := by
  simp [simple_iff_forall_pair_indep, projectiveGeometry_indep_iff]

/-- The projective geometry of rank `n+1` over `GF(p^t)`.-/
noncomputable def PG (n p t : ℕ) [Fact p.Prime] :=
    Matroid.projectiveGeometry (GaloisField p t) (Fin (n+1) → GaloisField p t)

instance projectiveGeometry_finitary : Finitary (projectiveGeometry 𝔽 W) :=
  matroidOfFun_finitary ..

/-- TODO: Generalize this to arbitrary fullrank representations -/
@[simp] lemma projectiveGeometry_cRank : (projectiveGeometry 𝔽 W).cRank = Module.rank 𝔽 W := by
  obtain ⟨B, hB⟩ := (projectiveGeometry 𝔽 W).exists_base
  have hr := (projectiveGeometryRep_fullRank.basis_of_base hB).mk_eq_rank
  simp only [Cardinal.lift_id] at hr
  rw [← hr, hB.cardinalMk_eq_cRank]

@[simp] lemma projectiveGeometry_rank : (projectiveGeometry 𝔽 W).rank = Module.finrank 𝔽 W := by
  rw [← cRank_toNat, projectiveGeometry_cRank]
  rfl

@[simp] lemma PG_rank (n p t : ℕ) [Fact p.Prime] : (PG n p t).rank = n+1 := by
  simp [PG]

lemma Representable.exists_isoRestr_projectiveGeometry [M.Simple] (h : M.Representable 𝔽)
    (hB : M.Base B) : ∃ (i : M ≤ir projectiveGeometry 𝔽 (B →₀ 𝔽)), i.Spanning := by
  classical
  obtain rfl | hne := M.eq_emptyOn_or_nonempty
  · refine ⟨IsoRestr.ofEmptyOn _, ?_⟩
    obtain rfl : B = ∅ := by simpa using hB
    simp [IsoRestr.Spanning, projectiveGeometry_eq_empty, projectiveGeometry_E, emptyOn_ground]

  have hBne := hB.nonempty.to_subtype
  have v := h.some.standardRep' hB

  refine ⟨IsoRestr.ofFun v.projFun v.projFun_injOn (by simp) ?_,
    IsoRestr.ofFun_spanning _ _ _ ?_⟩
  · intro I hIE
    rwa [projectiveGeometry_indep_iff, v.independent_image_projFun_iff]
  rw [spanning_iff_exists_base_subset]
  refine ⟨v.projFun '' B, ?_, image_subset _ hB.subset_ground⟩
  refine Indep.base_of_forall_insert ?_ fun e he ↦ ?_
  · rw [v.indep_image_projFun_iff hB.subset_ground]
    exact hB.indep
  sorry
  -- rw [v.indep_image_projFun_iff]

lemma Representable.encard_le_of_simple [FiniteRk M] [Simple M] (h : M.Representable 𝔽) :
    M.E.encard ≤ ∑ i ∈ Finset.range (M.rank), (ENat.card 𝔽)^i := by
  classical
  -- If `M` has rank at most `1`, this is trivial.
  obtain hle | hlt := le_or_lt M.eRank 1
  · obtain ⟨E, rfl⟩ := M.eq_unifOn_of_eRank_le_one hle
    have hE := unifOn_simple_iff.1 (by assumption)
    replace hE := show E.Subsingleton by simpa using hE
    obtain rfl | ⟨e, rfl⟩ := hE.eq_empty_or_singleton <;>
    simp [rank]
  have hr : 1 < M.rank := by rwa [← Nat.cast_lt (α := ℕ∞), cast_rank_eq]
  -- If `𝔽` is infinite, this is trivial, because the RHS is infinite.
  obtain hinf | hfin := (finite_or_infinite 𝔽).symm
  · refine le_trans ?_ (CanonicallyOrderedAddCommMonoid.single_le_sum (i := 1) (by simpa))
    simp [ENat.card_eq_top_of_infinite (α := 𝔽)]
  /- Otherwise `v` gives an injection from `M.E` to a finite projective space with
  known cardinality, giving the upper bound on `M.E.encard`. -/

  have : Nonempty (Fin M.rank) := ⟨1, hr⟩
  obtain ⟨v, -⟩ := h.exists_fin_rep
  rw [← v.projFun_injOn.encard_image]
  refine (encard_le_card (subset_univ _)).trans ?_
  simp_rw [encard_univ, ENat.card_eq_coe_natCard]
  norm_cast
  sorry
  -- rw [Projectivization.card_of_finrank]
  -- simp


lemma Representable.encard_le_of_unifOn_two (h : (unifOn E 2).Representable 𝔽) :
    E.encard ≤ ENat.card 𝔽 + 1 := by
  obtain hlt | hle := lt_or_le E.encard (2 : ℕ)
  · exact (show E.encard ≤ 1 from Order.le_of_lt_add_one hlt).trans (by simp)
  convert h.encard_le_of_simple
  simp [unifOn_rank_eq hle]

lemma Representable.encard_le_of_unif_two {a : ℕ} (h : (unif 2 a).Representable 𝔽) :
    a ≤ ENat.card 𝔽 + 1 :=  by
  simpa using h.encard_le_of_unifOn_two

@[simp] lemma removeLoops_representable_iff :
    M.removeLoops.Representable 𝔽 ↔ M.Representable 𝔽 := by
  refine ⟨fun ⟨v⟩ ↦ ?_, fun ⟨v⟩ ↦ ?_⟩
  · rw [M.eq_restrict_removeLoops]
    exact (v.restrict M.E).representable
  rw [removeLoops_eq_restr]
  exact (v.restrict _).representable

lemma Representable.noUniformMinor [Fintype 𝔽] (h : M.Representable 𝔽) :
    M.NoUniformMinor 2 (Fintype.card 𝔽 + 2) := by
  by_contra hcon
  obtain ⟨hm⟩ := not_noUniformMinor_iff.1 hcon
  have hcon := (h.isoMinor hm).encard_le_of_unif_two
  simp only [Nat.cast_add, Nat.cast_ofNat, ENat.card_eq_coe_fintype_card] at hcon
  rw [show (2 :ℕ∞) = 1 + 1 from rfl, ← add_assoc, ENat.add_one_le_iff] at hcon
  · simp at hcon
  simp only [WithTop.add_ne_top, ne_eq, WithTop.one_ne_top, not_false_eq_true, and_true]
  exact ne_of_beq_false rfl
