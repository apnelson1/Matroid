import Matroid.Representation.Minor
import Matroid.Rank.Cardinal
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Matroid.ForMathlib.LinearAlgebra.Projective

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Projectivization Projectivization.Subspace Function Subtype Set.Notation Matroid




section projFun

namespace Matroid

variable [M.OnUniv] [M.Loopless]

abbrev Rep.projFun (v : M.Rep 𝔽 W) (e : α) : Projectivization 𝔽 W :=
  Projectivization.mk 𝔽 (v e) (by simp)

-- lemma nontrivial_of_rankPos [RankPos M] (v : M.Rep 𝔽 W) : Nontrivial W where
--   exists_pair_ne := ⟨_, 0, v.ne_zero_of_isNonloop M.exists_isNonloop.choose_spec⟩

-- variable [Nontrivial W] [DecidableEq W]


lemma Rep.projFun_apply (v : M.Rep 𝔽 W) (e : α) :
    v.projFun e = Projectivization.mk 𝔽 (v e) (by simp) := rfl


lemma Rep.projFun_eq (v : M.Rep 𝔽 W) :
    v.projFun = fun e ↦ Projectivization.mk 𝔽 (v e) (by simp) := rfl

-- lemma Rep.projFun_eq [M.Loopless] (v : M.Rep 𝔽 W) (he : e ∈ M.E) :
--     v.projFun e = Projectivization.mk 𝔽 (v e) (v.ne_zero_of_isNonloop (toIsNonloop he)) := by
--   rw [Rep.projFun, dif_pos]

-- lemma Rep.projFun_not_isNonloop_eq (v : M.Rep 𝔽 W) (he : ¬ M.IsNonloop e) :
--     v.projFun e = Classical.arbitrary _ := by
--   rw [Rep.projFun, dif_neg]
--   rwa [v.ne_zero_iff_isNonloop]

lemma Rep.projFun_injective [M.Simple] (v : M.Rep 𝔽 W) : Injective v.projFun := by
  intro x y hxy
  rwa [projFun_apply, projFun_apply, Projectivization.mk_eq_mk_iff,
    ← v.parallel_iff' (by simp), parallel_iff_eq] at hxy

lemma Rep.indep_iff_projFun (v : M.Rep 𝔽 W) :
    M.Indep I ↔ (Independent (fun x : I ↦ v.projFun x)) := by
  rw [v.indep_iff, ← Projectivization.independent_comp_mk_iff]
  rfl

@[simp]
lemma Rep.independent_image_projFun_iff [M.Simple] (v : M.Rep 𝔽 W) :
    Independent (fun (x : (v.projFun '' I)) ↦ x.1) ↔ M.Indep I := by
  rw [v.indep_iff_projFun]
  let e : I ≃ (v.projFun '' I) := Equiv.Set.imageOfInjOn v.projFun I <| v.projFun_injective.injOn
  exact (Projectivization.independent_equiv e).symm

variable {𝔽 W : Type*} [Field 𝔽] [AddCommGroup W] [Module 𝔽 W]

lemma span_image_projFun_eq (v : M.Rep 𝔽 W) (X : Set α) :
    span (v.projFun '' X) = (Submodule.span 𝔽 (v '' X)).toProjSubspace :=
  (Submodule.toProjSubspace_span_image_eq ..).symm

lemma Rep.closure_eq_span_image_projFun (v : M.Rep 𝔽 W) (X : Set α) :
    M.closure X = v.projFun ⁻¹' (span (v.projFun '' X)) := by
  rw [v.closure_eq, ground_eq_univ, inter_univ, span_image_projFun_eq]
  ext
  simp

lemma Rep.FullRank.spanning_iff_projFun (v : M.Rep 𝔽 W) (hv : FullRank v) (S : Set α) :
    M.Spanning S ↔ span (v.projFun '' S) = ⊤ := by
  rw [hv.spanning_iff, span_image_projFun_eq]
  simp

lemma Rep.isBase_iff_proj {v : M.Rep 𝔽 W} (hv : FullRank v) (B : Set α) :
    M.IsBase B ↔ Independent (fun x : B ↦ v.projFun x) ∧ span (v.projFun '' B) = ⊤ := by
  rw [isBase_iff_indep_closure_eq, ← spanning_iff_closure_eq, v.indep_iff_projFun,
    hv.spanning_iff_projFun]

end Matroid

end projFun

namespace Projectivization

@[simps! E]
protected noncomputable def matroid (𝔽 W : Type*) [DivisionRing 𝔽]
    [AddCommGroup W] [Module 𝔽 W] : Matroid (Projectivization 𝔽 W) :=
  (Module.matroid 𝔽 W).comap Projectivization.rep
  -- Matroid.ofFun 𝔽 Set.univ Projectivization.rep

noncomputable def matroidRep : (Projectivization.matroid 𝔽 W).Rep 𝔽 W :=
  (Module.matroidRep 𝔽 W).comap _

instance matroid_onUniv : OnUniv (Projectivization.matroid 𝔽 W) :=
  ⟨rfl⟩

@[simp] lemma projectiveGeometry_eq_empty [Subsingleton W] :
    Projectivization.matroid 𝔽 W = emptyOn (Projectivization 𝔽 W) :=
  eq_emptyOn (α := Projectivization 𝔽 W) _

@[simp] lemma matroidRep_apply_eq (e : Projectivization 𝔽 W) : matroidRep e = e.rep := rfl

lemma matroidRep_fullRank : (matroidRep (𝔽 := 𝔽) (W := W)).FullRank :=
  Rep.fullRank_iff.2 <| submodule_span_range_rep 𝔽 W ..

instance : (Projectivization.matroid 𝔽 W).Loopless := by
  simp [loopless_iff_forall_isNonloop, ← matroidRep.ne_zero_iff_isNonloop, rep_nonzero]

@[simp]
lemma matroidRep_indep_iff {I : Set (Projectivization 𝔽 W)} :
    (Projectivization.matroid 𝔽 W).Indep I ↔ Projectivization.Independent (fun (x : I) ↦ x.1) := by
  simp [matroidRep.indep_iff_projFun, Rep.projFun_apply]

instance matroid_simple : (Projectivization.matroid 𝔽 W).Simple := by
  simp [simple_iff_forall_pair_indep]

instance matroid_finitary : Finitary (Projectivization.matroid 𝔽 W) := by
  rw [Projectivization.matroid]
  infer_instance

/-- The projective geometry of rank `n+1` over `GF(p^t)`.-/
noncomputable def PG (n p t : ℕ) [Fact p.Prime] :=
    Projectivization.matroid (GaloisField p t) (Fin (n+1) → GaloisField p t)

/-- TODO: Generalize this to arbitrary fullrank representations -/
@[simp]
lemma matroid_cRank : (Projectivization.matroid 𝔽 W).cRank = Module.rank 𝔽 W := by
  obtain ⟨B, hB⟩ := (Projectivization.matroid 𝔽 W).exists_isBase
  have hr := (matroidRep_fullRank.isBasis_of_isBase hB).mk_eq_rank
  simp only [Cardinal.lift_id] at hr
  rw [← hr, hB.cardinalMk_eq_cRank]

@[simp]
lemma projectiveGeometry_rank : (Projectivization.matroid 𝔽 W).rank = Module.finrank 𝔽 W := by
  rw [← cRank_toNat, Projectivization.matroid_cRank]
  rfl

/-- Isomorphic vector spaces give isomorphic projective geometries. -/
noncomputable def matroid_congr {𝔽 W : Type*} [Field 𝔽] [AddCommGroup W] [AddCommGroup W']
    [Module 𝔽 W] [Module 𝔽 W'] (i : W ≃ₗ[𝔽] W') :
    Projectivization.matroid 𝔽 W ≂ Projectivization.matroid 𝔽 W' :=
  let m := Projectivization.mapEquiv (σ := RingHom.id 𝔽) i
  have h_eq : (Projectivization.matroid 𝔽 W).mapEquiv m = Projectivization.matroid 𝔽 W' := by
    refine ext_indep (by simp) fun I hIE ↦ ?_
    simp only [Matroid.mapEquiv_indep_iff, matroidRep_indep_iff]
    rw [← Projectivization.independent_equiv (K := 𝔽) (V := W)
      (Equiv.Set.image m.symm I m.symm.injective), ← Projectivization.mapEquiv_indep_iff i]
    convert Iff.rfl with e
    ext x
    simp only [comp_apply, Equiv.Set.image_apply, mapEquiv_apply]
    rw [eq_comm]
    apply mapEquiv_mapEquiv_symm
  (isoMapEquiv _ m).trans (Iso.ofEq h_eq)

@[simp] lemma PG_rank (n p t : ℕ) [Fact p.Prime] : (PG n p t).rank = n+1 := by
  simp [PG]

end Projectivization

section Representable

variable {𝔽 : Type*} [Field 𝔽]

namespace Matroid.Representable

lemma exists_isoRestr_projectiveGeometry [M.Simple] (h : M.Representable 𝔽) (hB : M.IsBase B) :
    ∃ i : M ≤ir Projectivization.matroid 𝔽 (B →₀ 𝔽), i.Spanning := by
  wlog hM : M.OnUniv generalizing M α with aux
  · obtain ⟨γ, N, hN, ⟨iMN⟩⟩ := M.exists_iso_onUniv
    have := ‹M.Simple›.of_iso iMN
    have hNrep := h.iso iMN
    set B' : Set γ := ↑(iMN '' (M.E ↓∩ B)) with hB'_def
    have hB' : N.IsBase B' := by
      rw [iMN.symm.isBase_image_iff]
      simpa [inter_eq_self_of_subset_right hB.subset_ground]
    have e1 : (M.E ↓∩ B) ≃ B :=
      (Equiv.Set.image val _ val_injective).trans <| Equiv.Set.ofEq <| by simp [hB.subset_ground]
    have e2 : B ≃ B' := by
      refine e1.symm.trans <| ?_
      refine (Equiv.Set.image iMN _ iMN.toEquiv.injective).trans ?_
      exact (Equiv.Set.image val _ val_injective)
    have l1 := Finsupp.domLCongr e2 (M := 𝔽) (R := 𝔽)
    obtain ⟨i', hi'⟩ := aux hNrep hB' hN
    refine ⟨iMN.isoRestr.trans (i'.trans (Iso.isoRestr (matroid_congr l1.symm))), ?_⟩
    exact iMN.isoRestr_spanning.trans (hi'.trans (matroid_congr l1.symm).isoRestr_spanning)
  obtain ⟨v, hv⟩ := h.exists_fullRank_rep hB
  refine ⟨IsoRestr.ofFun v.projFun v.projFun_injective.injOn (by simp) (by simp),
    IsoRestr.ofFun_spanning _ _ _ ?_⟩
  rw [matroidRep_fullRank.spanning_iff _ (by simp), ← top_le_iff,
    ← hv.span_spanning M.ground_spanning, ground_eq_univ, image_univ, image_univ, Submodule.span_le]
  simp only [matroidRep_apply_eq, subset_def, mem_range, SetLike.mem_coe, forall_exists_index,
    forall_apply_eq_imp_iff, Projectivization.Subspace.mem_span_image_rep_iff _ _ (v.ne_zero _)]
  exact fun e ↦ mem_of_mem_of_subset (by simp) (subset_span _)

-- lemma representable_iff_exists_isoRestr.{u} {α : Type*} {M : Matroid α} {𝔽 : Type*} [Field 𝔽]
--     [M.Simple] : M.Representable 𝔽 ↔ ∃ β : Type u,

lemma encard_le_of_simple [RankFinite M] [Simple M] (h : M.Representable 𝔽) :
    M.E.encard ≤ ∑ i ∈ Finset.range (M.rank), (ENat.card 𝔽)^i := by
  classical
  obtain hle | hlt := le_or_lt M.eRank 1
  · obtain ⟨E, rfl⟩ := M.eq_unifOn_of_eRank_le_one hle
    have hE := unifOn_simple_iff.1 (by assumption)
    replace hE := show E.Subsingleton by simpa using hE
    obtain rfl | ⟨e, rfl⟩ := hE.eq_empty_or_singleton <;>
    simp [rank]
  have hr : 1 < M.rank := by rwa [← Nat.cast_lt (α := ℕ∞), cast_rank_eq]
  obtain hinf | hfin := (finite_or_infinite 𝔽).symm
  · refine le_trans ?_ (CanonicallyOrderedAddCommMonoid.single_le_sum (i := 1) (by simpa))
    simp [ENat.card_eq_top_of_infinite (α := 𝔽)]
  have : Nonempty (Fin M.rank) := ⟨1, hr⟩
  obtain ⟨B, hB⟩ := M.exists_isBase_finset
  obtain ⟨i, hi⟩ := h.exists_isoRestr_projectiveGeometry hB
  convert i.isoMinor.encard_ground_le
  have := hB.finite.to_subtype
  have := Fintype.ofFinite ↑B
  have := Fintype.ofFinite 𝔽
  have := Fintype.ofFinite (B →₀ 𝔽)
  simp only [ENat.card_eq_coe_natCard, ground_eq_univ, encard_univ]
  norm_cast
  rw [Projectivization.card_of_finrank 𝔽 (B →₀ 𝔽) (n := M.rank)]
  simp [hB.finset_card]

lemma encard_le_of_unifOn_two (h : (unifOn E 2).Representable 𝔽) : E.encard ≤ ENat.card 𝔽 + 1 := by
  obtain hlt | hle := lt_or_le E.encard (2 : ℕ)
  · exact (show E.encard ≤ 1 from Order.le_of_lt_add_one hlt).trans (by simp)
  convert h.encard_le_of_simple
  simp [unifOn_rank_eq hle]

lemma encard_le_of_unif_two {a : ℕ} (h : (unif 2 a).Representable 𝔽) : a ≤ ENat.card 𝔽 + 1 :=  by
  simpa using h.encard_le_of_unifOn_two

@[simp] lemma removeLoops_representable_iff :
    M.removeLoops.Representable 𝔽 ↔ M.Representable 𝔽 := by
  refine ⟨fun ⟨v⟩ ↦ ?_, fun ⟨v⟩ ↦ ?_⟩
  · rw [M.eq_restrict_removeLoops]
    exact (v.restrict M.E).representable
  rw [removeLoops_eq_restr]
  exact (v.restrict _).representable

lemma noUniformMinor [Fintype 𝔽] (h : M.Representable 𝔽) :
    M.NoUniformMinor 2 (Fintype.card 𝔽 + 2) := by
  by_contra hcon
  obtain ⟨hm⟩ := not_noUniformMinor_iff.1 hcon
  have hcon := (h.isoMinor hm).encard_le_of_unif_two
  simp only [Nat.cast_add, Nat.cast_ofNat, ENat.card_eq_coe_fintype_card] at hcon
  rw [show (2 :ℕ∞) = 1 + 1 from rfl, ← add_assoc, ENat.add_one_le_iff] at hcon
  · simp at hcon
  simp only [WithTop.add_ne_top, ne_eq, WithTop.one_ne_top, not_false_eq_true, and_true]
  exact ne_of_beq_false rfl
