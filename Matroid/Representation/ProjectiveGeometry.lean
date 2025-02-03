import Matroid.Representation.Minor
import Matroid.Rank.Cardinal
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence
import Matroid.ForMathlib.LinearAlgebra.Projective

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Submodule Set Projectivization

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


section Projectivization

noncomputable def Rep.projectivization [Nontrivial W] [DecidableEq W] (v : M.Rep 𝔽 W)
    (e : α) : Projectivization 𝔽 W :=
  if he : v e ≠ 0 then Projectivization.mk 𝔽 (v e) he else Classical.arbitrary _

lemma nontrivial_of_rkPos [RkPos M] (v : M.Rep 𝔽 W) : Nontrivial W where
  exists_pair_ne := ⟨_, 0, v.ne_zero_of_nonloop M.exists_nonloop.choose_spec⟩

variable [Nontrivial W] [DecidableEq W]

lemma Rep.projectivization_nonloop_eq (v : M.Rep 𝔽 W) (he : M.Nonloop e) :
    v.projectivization e = Projectivization.mk 𝔽 (v e) (v.ne_zero_of_nonloop he) := by
  rw [Rep.projectivization, dif_pos]

lemma Rep.projectivization_eq [M.Loopless] (v : M.Rep 𝔽 W) (he : e ∈ M.E) :
    v.projectivization e = Projectivization.mk 𝔽 (v e) (v.ne_zero_of_nonloop (toNonloop he)) := by
  rw [Rep.projectivization, dif_pos]

lemma Rep.projectivization_not_nonloop_eq (v : M.Rep 𝔽 W) (he : ¬ M.Nonloop e) :
    v.projectivization e = Classical.arbitrary _ := by
  rw [Rep.projectivization, dif_neg]
  rwa [v.ne_zero_iff_nonloop]

lemma Rep.projectivization_injOn [M.Simple] (v : M.Rep 𝔽 W) : InjOn v.projectivization M.E := by
  intro x hx y hy hxy
  rwa [v.projectivization_nonloop_eq (toNonloop hx), v.projectivization_nonloop_eq (toNonloop hy),
    Projectivization.mk_eq_mk_iff, ← v.parallel_iff' (toNonloop hx), parallel_iff_eq] at hxy

lemma Rep.indep_iff_projectivization [M.Loopless] (v : M.Rep 𝔽 W) (hIE : I ⊆ M.E) :
    M.Indep I ↔ (Projectivization.Independent (fun x : I ↦ v.projectivization x)) := by
  rw [v.indep_iff, Projectivization.linearIndependent_iff]
  · convert Iff.rfl with e
    simp [v.projectivization_eq (hIE e.2)]
  simp [show ∀ e ∈ I, v e ≠ 0 from fun e heI ↦ v.ne_zero_of_nonloop (toNonloop (hIE heI))]

end Projectivization

@[simps! E] noncomputable def projectiveGeometry (𝔽 W : Type*) [DivisionRing 𝔽] [AddCommGroup W]
    [Module 𝔽 W] : Matroid (Projectivization 𝔽 W) :=
  Matroid.ofFun 𝔽 Set.univ Projectivization.rep

noncomputable def projectiveGeometryRep : (projectiveGeometry 𝔽 W).Rep 𝔽 W :=
  repOfFun ..

@[simp] lemma projectiveGeometry_eq_empty [Subsingleton W] :
    projectiveGeometry 𝔽 W = emptyOn (Projectivization 𝔽 W) :=
  eq_emptyOn (α := Projectivization 𝔽 W) _

lemma projectiveGeometryRep_fullRank : (projectiveGeometryRep (𝔽 := 𝔽) (W := W)).FullRank := by
  rw [Rep.FullRank, projectiveGeometryRep, ← image_univ, repOfFun_image_eq, image_univ,
    Projectivization.span_range_rep]

instance : (projectiveGeometry 𝔽 W).Loopless := by
  simp_rw [loopless_iff_forall_nonloop]
  rintro e -
  rw [← projectiveGeometryRep.ne_zero_iff_nonloop, projectiveGeometryRep,
    repOfFun_apply _ (by simp)]
  exact rep_nonzero e

lemma foo {I : Set (Projectivization 𝔽 W)} :
    (projectiveGeometry 𝔽 W).Indep I ↔ Projectivization.Independent (fun (x : I) ↦ x.1) := by
  classical
  obtain hW | hW := subsingleton_or_nontrivial W
  · simp
  rw [projectiveGeometryRep.indep_iff_projectivization]

lemma Rep.indep_projectivization_iff [Nontrivial W] [DecidableEq W] [M.Simple] (v : M.Rep 𝔽 W)
    (hIE : I ⊆ M.E) : (projectiveGeometry 𝔽 W).Indep (v.projectivization '' I) ↔ M.Indep I := by
  rw [projectiveGeometryRep.projectivization_indep_iff (by simp), v.projectivization_indep_iff hIE]

  rw [projectiveGeometry, ofFun_indep_iff, v.indep_iff, and_iff_left (subset_univ _),
    restrict_def]

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

@[simp] lemma projectiveGeometry_rank : (ProjectiveGeometry 𝔽 W).rank = Module.finrank 𝔽 W := by
  rw [← cRank_toNat, projectiveGeometry_cRank]
  rfl

@[simp] lemma PG_rank (n p t : ℕ) [Fact p.Prime] : (PG n p t).rank = n+1 := by
  simp [PG]

lemma Representable.exists_isoRestr_projectiveGeometry [M.Simple] (h : M.Representable 𝔽)
    (hB : M.Base B) : ∃ (i : M ≤ir ProjectiveGeometry 𝔽 (B →₀ 𝔽)), i.Spanning := by
  classical
  obtain rfl | hne := M.eq_emptyOn_or_nonempty
  · refine ⟨IsoRestr.ofEmptyOn _, ?_⟩
    obtain rfl : B = ∅ := by simpa using hB
    simp [IsoRestr.Spanning, projectiveGeometry_eq_empty, ProjectiveGeometry_E, emptyOn_ground]

  have hBne := hB.nonempty.to_subtype
  have v := h.some.standardRep' hB

  refine ⟨IsoRestr.ofFun v.projectivization v.projectivization_injOn (by simp) ?_,
    IsoRestr.ofFun_spanning _ _ _ ?_⟩
  ·



  -- refine ⟨⟨fun (e : M.E) ↦ ?_, ?_, ?_⟩ , ?_⟩
  -- · exact ⟨Projectivization.mk 𝔽 (v e.1) (v.ne_zero_of_nonloop (toNonloop (e := e.1) e.2)), by simp⟩
  -- · sorry
  -- · intro I
  --   rw [ProjectiveGeometryRep.indep_iff]
  --   simp


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
  rw [← v.projectivization_injOn.encard_image]
  refine (encard_le_card (subset_univ _)).trans ?_
  simp_rw [encard_univ, ENat.card_eq_coe_natCard]
  norm_cast
  rw [Projectivization.card_of_finrank]
  simp


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
