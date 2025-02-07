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

-- lemma nontrivial_of_rkPos [RkPos M] (v : M.Rep 𝔽 W) : Nontrivial W where
--   exists_pair_ne := ⟨_, 0, v.ne_zero_of_nonloop M.exists_nonloop.choose_spec⟩

-- variable [Nontrivial W] [DecidableEq W]

@[simp]
lemma Rep.projFun_apply (v : M.Rep 𝔽 W) (e : α) :
    v.projFun e = Projectivization.mk 𝔽 (v e) (by simp) := rfl


lemma Rep.projFun_eq (v : M.Rep 𝔽 W) :
    v.projFun = fun e ↦ Projectivization.mk 𝔽 (v e) (by simp) := rfl

-- lemma Rep.projFun_eq [M.Loopless] (v : M.Rep 𝔽 W) (he : e ∈ M.E) :
--     v.projFun e = Projectivization.mk 𝔽 (v e) (v.ne_zero_of_nonloop (toNonloop he)) := by
--   rw [Rep.projFun, dif_pos]

-- lemma Rep.projFun_not_nonloop_eq (v : M.Rep 𝔽 W) (he : ¬ M.Nonloop e) :
--     v.projFun e = Classical.arbitrary _ := by
--   rw [Rep.projFun, dif_neg]
--   rwa [v.ne_zero_iff_nonloop]

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

lemma Rep.base_iff_proj {v : M.Rep 𝔽 W} (hv : FullRank v) (B : Set α) :
    M.Base B ↔ Independent (fun x : B ↦ v.projFun x) ∧ span (v.projFun '' B) = ⊤ := by
  rw [base_iff_indep_closure_eq, ← spanning_iff_closure_eq, v.indep_iff_projFun,
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
  simp [loopless_iff_forall_nonloop, ← matroidRep.ne_zero_iff_nonloop, rep_nonzero]

@[simp]
lemma matroidRep_indep_iff {I : Set (Projectivization 𝔽 W)} :
    (Projectivization.matroid 𝔽 W).Indep I ↔ Projectivization.Independent (fun (x : I) ↦ x.1) := by
  simp [matroidRep.indep_iff_projFun]

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
  obtain ⟨B, hB⟩ := (Projectivization.matroid 𝔽 W).exists_base
  have hr := (matroidRep_fullRank.basis_of_base hB).mk_eq_rank
  simp only [Cardinal.lift_id] at hr
  rw [← hr, hB.cardinalMk_eq_cRank]

@[simp]
lemma projectiveGeometry_rank : (Projectivization.matroid 𝔽 W).rank = Module.finrank 𝔽 W := by
  rw [← cRank_toNat, Projectivization.matroid_cRank]
  rfl



/-- Isomorphic vector spaces give isomorphic projective geometries. -/
@[simp]
noncomputable def matroid_congr [DivisionRing 𝔽] [AddCommGroup W] [AddCommGroup W']
    [Module 𝔽 W] [Module 𝔽 W'] (i : W ≃ₗ[𝔽] W') :
    Projectivization.matroid 𝔽 W ≂ Projectivization.matroid 𝔽 W' := by
  let m := Projectivization.map (σ := RingHom.id 𝔽) i (V := W) (W := W') i.injective
  have hm : m.Injective := (Projectivization.map_injective _ i.injective)
  rw [Projectivization.matroid]
  refine (isoMap _ m hm.injOn).trans (Iso.ofEq ?_)

  refine ext_indep ?_ ?_
  · simp
    sorry
  simp only [map_ground, ground_eq_univ, image_univ, map_indep_iff, matroidRep_indep_iff,
    forall_subset_range_iff, image_eq_image hm, exists_eq_right']
  refine fun s ↦ ?_
  set i' := Equiv.Set.imageOfInjOn m s hm.injOn
  rw [independent_iff, independent_iff, ← linearIndependent_equiv i',
    ← i.linearIndependent_iff_of_injOn i.injective.injOn]

  -- have hrw : ∀ e : s, ∃ c, (i ∘ Projectivization.rep ∘ fun x ↦ ↑x) e = c • e  := sorry

  -- simp [i', Equiv.Set.imageOfInjOn]



  -- have i' := Equiv.Set.imageOfInjOn m s hm.injOn
  -- have := independent_equiv
  -- have := independent_equiv' (K := 𝔽) (V := W) (f := Subtype.val) (g := Subtype.val) i'
  -- convert (independent_equiv' (K := 𝔽) (V := W) i'.symm ?_)


  -- refine ⟨(isoMap m ?_).trans ?_, ?_⟩
  -- set f : Projectivization 𝔽 W → Projectivization 𝔽 W' :=
  --   fun x ↦ Projectivization.mk 𝔽 (i x.rep) (by simp [rep_nonzero])
  -- refine (isoMap _ f (fun x _ y _ hxy ↦ ?_)).trans (Iso.ofEq ?_)
  -- ·
  --   rw [mk_eq_mk_iff'] at hxy
  --   obtain ⟨a, ha⟩ := hxy

  --   apply_fun i.symm at ha
  --   rw [map_smul, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, eq_comm] at ha

  --   have : Projectivization.mk 𝔽 x.rep x.rep_nonzero = Projectivization.mk 𝔽 (a • y.rep)
  --     (by rw [← ha]; exact x.rep_nonzero)

  --   rw [← mk_eq_]
  --   have := i.symm.map_smul a (i y.rep)


@[simp] lemma PG_rank (n p t : ℕ) [Fact p.Prime] : (PG n p t).rank = n+1 := by
  simp [PG]

-- set_option diagnostics true
lemma Representable.exists_isoRestr_projectiveGeometry'.{u} {α : Type u} {M : Matroid α} [M.Simple]
    (h : M.Representable 𝔽) :
    ∃ (β : Type u) (i : M ≤ir projectiveGeometry 𝔽 (β →₀ 𝔽)), i.Spanning := by
  wlog hM : M.OnUniv generalizing M α with aux
  · obtain ⟨γ, N, hN, ⟨iMN⟩⟩ := M.exists_iso_onUniv
    have := ‹M.Simple›.of_iso iMN
    have hNrep := h.iso iMN
    obtain ⟨β, i, hi⟩ := aux hNrep hN
    exact ⟨β, iMN.isoRestr.trans i, iMN.isoRestr_spanning.trans hi⟩
  obtain ⟨B, hB⟩ := M.exists_base
  have v := h.some.standardRep' hB
  refine ⟨B, IsoRestr.ofFun v.projFun v.projFun_injective.injOn (by simp) (fun I hIE ↦ ?_), ?_⟩
  · rw [projectiveGeometry_indep_iff]


lemma Representable.exists_isoRestr_projectiveGeometry [M.Simple] (h : M.Representable 𝔽)
    (hB : M.Base B) : ∃ (i : M ≤ir projectiveGeometry 𝔽 (B →₀ 𝔽)), i.Spanning := by
  have v := h.some.standardRep' hB
  have hvr : v.FullRank := sorry
  set f : M.E → Projectivization 𝔽 (B →₀ 𝔽) := fun x ↦ Projectivization.mk 𝔽 (v x) sorry
  have hf : Injective f := sorry
  refine ⟨IsoRestr.ofSubtypeFun f hf (by simp) fun I ↦ ?_, IsoRestr.ofSubtypeFun_spanning _ _ _ ?_⟩
  · simp only [projectiveGeometry_indep_iff]
    let e : I ≃ (f '' I) := Equiv.Set.imageOfInjOn f I hf.injOn
    let e' : I ≃ val '' I := Equiv.Set.imageOfInjOn val I val_injective.injOn
    rw [v.indep_iff, ← independent_comp_mk_iff, ← independent_equiv e, ← independent_equiv e']
    · convert Iff.rfl
      ext x
      simp [e, e', Equiv.Set.imageOfInjOn, f]
    simp only [comp_apply, ne_eq, Subtype.forall, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index, v.ne_zero_iff_nonloop, e', e, f]
    exact fun a ha _ ↦ toNonloop ha

  rw [projectiveGeometryRep_fullRank.spanning_iff]
  simp
  suffices h : Submodule.span 𝔽 (projectiveGeometryRep '' (f '' (M.E ↓∩ B))) = ⊤ by sorry
  convert (hvr.basis_of_base hB).span_eq using 1
  simp only [projectiveGeometryRep_apply_eq, f]
  refine Submodule.span_eq_span ?_ ?_
  · simp [subset_def]
  simp only [Rep.FullRank.basis_of_base, Basis.coe_mk, range_restrict, subset_def, mem_image,
    SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, f]
  refine fun e heB ↦ ?_
  suffices v e ∈ Submodule.span 𝔽 ((Projectivization.mk 𝔽 (v e)))
  -- ext w
  -- simp only [projectiveGeometryRep_apply_eq, mem_image, mem_preimage, Subtype.exists,
  --   exists_and_left, Rep.FullRank.basis_of_base, Basis.coe_mk, range_restrict, f]
  -- constructor
  -- · rintro ⟨u, ⟨z, h1, h, rfl⟩, rfl⟩
  --   refine ⟨z, h1, ?_⟩








  -- refine ⟨IsoRestr.mk f sorry fun I ↦ ?_, ?_⟩
  -- ·
  --   -- have e : (I : Set α) ≃ Subtype.val '' (f '' I) := by
  --   --   have := Equiv.ofInjective f hf
  --   --   refine (Equiv.ofInjective _ Subtype.val_injective).trans ?_
  --   simp only [projectiveGeometry_E, projectiveGeometry_indep_iff]
  --   rw [← independent_equiv (Equiv.Set.univ α).symm]
  --   -- have : α ≃ {x : α // x ∈ univ} := by exact (Equiv.Set.univ α).symm
  --   set s := ((fun a ↦ ↑a) '' (f '' I))
  --   -- rw [v.indep_iff_image_of_inj]
  --   simp only [projectiveGeometry_E, projectiveGeometry_indep_iff,
  --     independent_iff]
  --   rw [v.indep_iff_image_of_inj]



  --   rw [v.indep_iff_image_of_inj, linearIndependent_image]
  --   · set s₁ := Projectivization.rep '' (val '' (f '' I))
  --     set s₂ := v '' (val '' I)




  --   rw [← Projectivization.independent_comp_mk_iff]
  --   · have { x // x ∈ Subtype.val '' I }
  --     refine (independent_equiv (K := 𝔽) (V := B →₀ 𝔽) ?_).symm

  -- wlog aux : M.OnUniv generalizing α with h
  --   have := M.exists_iso

  -- classical
  -- obtain rfl | hne := M.eq_emptyOn_or_nonempty
  -- · refine ⟨IsoRestr.ofEmptyOn _, ?_⟩
  --   obtain rfl : B = ∅ := by simpa using hB
  --   simp [IsoRestr.Spanning, projectiveGeometry_eq_empty, projectiveGeometry_E, emptyOn_ground]

  -- have hBne := hB.nonempty.to_subtype
  -- have v := h.some.standardRep' hB

  -- refine ⟨IsoRestr.ofFun v.projFun v.projFun_injOn (by simp) ?_,
  --   IsoRestr.ofFun_spanning _ _ _ ?_⟩
  -- · intro I hIE
  --   rwa [projectiveGeometry_indep_iff, v.independent_image_projFun_iff]
  -- rw [spanning_iff_exists_base_subset]
  -- refine ⟨v.projFun '' B, ?_, image_subset _ hB.subset_ground⟩
  -- refine Indep.base_of_forall_insert ?_ fun e he ↦ ?_
  -- · rw [v.indep_image_projFun_iff hB.subset_ground]
  --   exact hB.indep
  -- sorry
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
  refine (encard_le_encard (subset_univ _)).trans ?_
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
