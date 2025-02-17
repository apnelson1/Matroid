import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.LinearAlgebra.Projectivization.Basic
import Matroid.Connectivity.Skew
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation
universe u v

section ForMathlib

-- @[simp] lemma linearIndependent_zero_iff : LinearIndependent 𝔽 (0 : α → W) ↔ IsEmpty α :=
--   ⟨fun h ↦ ⟨fun a ↦ h.ne_zero a rfl⟩, fun _ ↦ linearIndependent_empty_type⟩

@[simp] lemma restrict_zero (X : Set α) : X.restrict (0 : α → W) = 0 := rfl

-- lemma foo : LinearIndependent 𝔽 (fun x : I ↦ v x)
--       ∀ c : α →₀ 𝔽, Finsupp.linearCombination 𝔽 v c = 0 → (c.support : Set α) ⊆ I → c = 0 := by

end ForMathlib

namespace Matroid

/-- `M.Rep 𝔽 W` is a function from `α` to a module `W` that represents `M`. -/
@[ext] structure Rep (M : Matroid α) (𝔽 W : Type*) [Semiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (valid' : ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict to_fun))

/-- A `Representable` matroid is one that has a representation over `𝔽` -/
def Representable (M : Matroid α) (𝔽 : Type*) [Semiring 𝔽] : Prop :=
  Nonempty (M.Rep 𝔽 (α → 𝔽))

instance : FunLike (M.Rep 𝔽 W) α W where
  coe v := v.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

@[simp] lemma Rep.to_fun_eq_coe (v : M.Rep 𝔽 W) : v.to_fun = (v : α → W) := rfl

lemma Rep.indep_iff_restrict (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v) :=
  v.valid' I

lemma Rep.indep_iff (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (v ∘ ((↑) : I → α)) :=
  v.valid' I

lemma Rep.indep_iff' (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (fun x : I ↦ v x) :=
  v.valid' I

lemma Rep.onIndep (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (I.restrict v) :=
  v.indep_iff.1 hI

lemma Rep.injOn_of_indep (v : M.Rep 𝔽 W) (hI : M.Indep I) : InjOn v I :=
  injOn_iff_injective.2 ((v.onIndep hI).injective)

lemma Rep.indep_image (v : M.Rep 𝔽 W) (hI : M.Indep I) :
    LinearIndependent 𝔽 ((↑) : (v '' I) → W) := by
  rw [← linearIndependent_image <| v.injOn_of_indep hI]
  exact v.onIndep hI

lemma Rep.indep_iff_image_of_inj (v : M.Rep 𝔽 W) (h_inj : InjOn v I) :
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : (v '' I) → W) := by
  refine ⟨v.indep_image, fun hi ↦ ?_⟩
  rw [v.indep_iff]
  exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

lemma Rep.indep_iff_image (v : M.Rep 𝔽 W) :
    M.Indep I ↔ LinearIndependent 𝔽 ((↑) : (v '' I) → W) ∧ InjOn v I :=
  ⟨fun h ↦ ⟨v.indep_image h, v.injOn_of_indep h⟩,
    fun h ↦ (v.indep_iff_image_of_inj h.2).2 h.1⟩

-- lemma Rep.indep_iff_forall_finsupp (v : M.Rep 𝔽 W) : M.Indep I ↔
--       ∀ c : α →₀ 𝔽, Finsupp.linearCombination 𝔽 v c = 0 → (c.support : Set α) ⊆ I → c = 0 := by
--   classical
--   rw [v.indep_iff']

--   refine ⟨fun h c hc hc0 ↦ h c hc0 hc, fun h c hc hcs ↦ h c hcs hc⟩
  -- rw [v.indep_iff', linearIndependent_iff]
  -- refine ⟨fun h c hc hcs ↦ ?_, fun h c hc0 ↦ ?_⟩
  -- · specialize h <| Finsupp.subtypeDomain (· ∈ I) c
  --   rw [Finsupp.subtypeDomain_eq_zero_iff hcs] at h
  --   refine h ?_
  --   rw [← hc]
  --   simp [Finsupp.linearCombination, Finset.sum_subtype_of_mem (f := fun x ↦ c x • v x) hcs,
  --     Finsupp.sum]
  -- have h' : (Finsupp.linearCombination 𝔽 (v ∘ Subtype.val)) c = 0 → c = 0 := by
  --   simpa using h (c.embDomain (Embedding.subtype (· ∈ I)))
  -- exact h' hc0

-- lemma Rep.exists_finsupp_of_not_indep (v : M.Rep 𝔽 W) (hX : ¬ M.Indep X) :
--     ∃ c : α →₀ 𝔽, Finsupp.linearCombination 𝔽 v c = 0 ∧ (c.support : Set α) ⊆ X ∧ c ≠ 0 := by
--   rw [v.indep_iff'] at hX
--   simpa [v.indep_iff_forall_finsupp] using hX

lemma Rep.eq_zero_iff_not_indep {v : M.Rep 𝔽 W} : v e = 0 ↔ ¬ M.Indep {e} := by
  simp [v.indep_iff, linearIndependent_unique_iff, -indep_singleton]

lemma Rep.eq_zero_of_not_mem_ground (v : M.Rep 𝔽 W) (he : e ∉ M.E) : v e = 0 := by
  rw [v.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

lemma Rep.support_subset_ground (v : M.Rep 𝔽 W) : support v ⊆ M.E :=
  fun _ he ↦ by_contra <| fun h' ↦ he (v.eq_zero_of_not_mem_ground h')

lemma Rep.mem_ground_of_apply_ne_zero {v : M.Rep 𝔽 W} (hv : v e ≠ 0) : e ∈ M.E :=
  v.support_subset_ground hv

lemma Indep.rep_apply_ne_zero_of_mem {v : M.Rep 𝔽 W} (hI : M.Indep I) (heI : e ∈ I) :
    v e ≠ 0 := by
  rw [Ne, Rep.eq_zero_iff_not_indep, not_not]
  exact hI.subset (by simpa)

lemma Rep.closure_eq (v : M.Rep 𝔽 W) (X : Set α) : M.closure X = (v ⁻¹' span 𝔽 (v '' X)) ∩ M.E := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  ext e
  by_cases heI : e ∈ I
  · refine iff_of_true ?_ (mem_inter ?_ ?_)
    · exact mem_closure_of_mem' _ (hI.subset heI) (hI.indep.subset_ground heI)
    exact subset_span (mem_image_of_mem v (hI.subset heI))
    exact hI.indep.subset_ground heI
  simp only [← hI.closure_eq_closure, hI.indep.mem_closure_iff', v.indep_iff_restrict, restrict_def,
    linearIndependent_insert' heI, and_comm, heI, imp_false, not_and, mem_inter_iff, mem_preimage,
    SetLike.mem_coe, and_congr_right_iff]
  rw [← v.indep_iff', iff_true_intro hI.indep, not_true, imp_false, not_not]
  refine fun he ↦ ⟨fun h ↦ mem_of_mem_of_subset h (span_mono (image_subset v hI.subset)),
    fun h ↦ span_le.2 ?_ h⟩
  rintro _ ⟨f, hf, rfl⟩
  refine (em (f ∈ I)).elim (fun hfI ↦ subset_span <| mem_image_of_mem v hfI) (fun hfI ↦ ?_)
  have hni := hI.insert_not_indep ⟨hf, hfI⟩
  rwa [v.indep_iff_restrict, restrict_def, linearIndependent_insert' hfI, ← v.indep_iff',
    and_iff_right hI.indep, not_not] at hni

lemma Rep.mem_closure_iff (v : M.Rep 𝔽 W) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ v e ∈ span 𝔽 (v '' X) := by
  rw [v.closure_eq, mem_inter_iff, and_iff_left heE]
  rfl

/-- If some linear combination of columns of `M.E` is zero, the nonzero indices form a cyclic set.-/
lemma Rep.cyclic_of_linearCombination (v : M.Rep 𝔽 W) (c : α →₀ 𝔽) (hcE : (c.support : Set α) ⊆ M.E)
    (hcv : c.linearCombination 𝔽 v = 0) : M.Cyclic c.support := by
  rw [cyclic_iff_forall_mem_closure_diff_singleton]
  intro e he
  rw [v.mem_closure_iff (hcE he), Finsupp.mem_span_image_iff_linearCombination]
  have hce : c e ≠ 0 := by simpa using he
  use - (c e)⁻¹ • (c - Finsupp.single e (c e))
  suffices ∀ (x : α), (¬c x = 0 → x = e) → c x - (Finsupp.single e (c e)) x = 0 by
    simpa [Finsupp.mem_supported', hcv, hce, ← smul_assoc]
  intro x
  obtain rfl | hne := eq_or_ne x e
  · simp
  simp +contextual [hne, Finsupp.single_apply_eq_zero]

lemma Rep.exists_finsupp_of_isCircuit (v : M.Rep 𝔽 W) {C : Finset α} (hC : M.IsCircuit C) :
    ∃ c : α →₀ 𝔽, c.support = C ∧ c.linearCombination 𝔽 v = 0 := by
  have hC' := hC.not_indep
  rw [v.indep_iff'] at hC'
  obtain ⟨c, h, hc, h0⟩ := linearDependent_comp_subtype'.1 hC'
  refine ⟨c, subset_antisymm (by simpa using h) fun e heC ↦ ?_, hc⟩
  contrapose! h0
  refine (linearIndependent_comp_subtype.1 <| v.indep_iff'.1 <| hC.diff_singleton_indep heC) _ ?_ hc
  simpa [Finsupp.mem_supported, subset_diff_singleton_iff, h0] using h

lemma Rep.span_le_of_closure_subset (v : M.Rep 𝔽 W) (hXY : M.closure X ⊆ M.closure Y) :
    span 𝔽 (v '' X) ≤ span 𝔽 (v '' Y) := by
  rw [span_le]
  rintro _ ⟨e, he, rfl⟩
  obtain heE | heE := em' (e ∈ M.E)
  · simp [v.eq_zero_of_not_mem_ground heE]
  rw [v.closure_eq Y] at hXY
  exact (hXY (M.mem_closure_of_mem' he heE)).1

lemma Rep.closure_subset_iff_span_le (v : M.Rep 𝔽 W) :
    M.closure X ⊆ M.closure Y ↔ span 𝔽 (v '' X) ≤ span 𝔽 (v '' Y) := by
  refine ⟨v.span_le_of_closure_subset, fun h e heX ↦ ?_⟩
  rw [v.closure_eq, mem_inter_iff, mem_preimage, SetLike.mem_coe] at heX ⊢
  exact ⟨h heX.1, heX.2⟩

lemma Rep.span_closure_congr (v : M.Rep 𝔽 W) (hXY : M.closure X = M.closure Y) :
    span 𝔽 (v '' X) = span 𝔽 (v '' Y) :=
  (v.span_le_of_closure_subset hXY.subset).antisymm (v.span_le_of_closure_subset hXY.symm.subset)

lemma Rep.span_closure_congr_iff (v : M.Rep 𝔽 W) :
    M.closure X = M.closure Y ↔ span 𝔽 (v '' X) = span 𝔽 (v '' Y) :=
  ⟨v.span_closure_congr, fun h ↦ by simp [subset_antisymm_iff, v.closure_subset_iff_span_le, h]⟩

@[simp] lemma Rep.span_image_loops (v : M.Rep 𝔽 W) : span 𝔽 (v '' (M.closure ∅)) = ⊥ := by
  simp [v.span_closure_congr (M.closure_closure ∅)]

lemma Rep.skew_iff_span_disjoint (v : M.Rep 𝔽 W) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    M.Skew X Y ↔ Disjoint (span 𝔽 (v '' X)) (span 𝔽 (v '' Y)) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis Y
  rw [← skew_iff_isBases_skew hI hJ, hI.indep.skew_iff_disjoint_union_indep hJ.indep,
    ← v.span_closure_congr hI.closure_eq_closure, ← v.span_closure_congr hJ.closure_eq_closure,
    v.indep_iff_restrict]
  by_cases hdj : Disjoint I J
  ·   rw [linearIndependent_restrict_union_iff hdj, ← v.indep_iff_restrict,
      and_iff_right hdj, ← v.indep_iff_restrict, and_iff_right hI.indep, and_iff_right hJ.indep]
  obtain ⟨x, hxI, hxJ⟩ := not_disjoint_iff.1 hdj
  simp only [hdj, false_and, disjoint_def, false_iff, not_forall, Classical.not_imp, exists_prop,
    exists_and_left]
  refine ⟨v x, (subset_span (mem_image_of_mem v hxI)), (subset_span (mem_image_of_mem v hxJ)), ?_⟩
  rw [v.eq_zero_iff_not_indep, not_not]
  exact hI.indep.subset (by simpa)

/-! ### Constructors -/

/-- A function with support contained in `M.E` that gives the correct independent sets
  within the ground set gives a representation -/
@[simps] def Rep.ofGround (f : α → W) (h_support : support f ⊆ M.E)
    (hf : ∀ I ⊆ M.E, (M.Indep I ↔ LinearIndependent 𝔽 (I.restrict f))) : M.Rep 𝔽 W where
  to_fun := f
  valid' := ( by
    intro I
    by_cases hI : I ⊆ M.E
    · rw [hf _ hI]
    rw [← not_iff_not, iff_true_left (fun hi ↦ hI hi.subset_ground)]
    intro h_ind
    obtain ⟨e, heI, heE⟩ := not_subset.1 hI
    have h0 := h_ind.ne_zero ⟨e, heI⟩
    simp only [Function.comp_apply, ne_eq] at h0
    apply not_mem_subset h_support heE
    exact h0 )

@[simp] lemma Rep.ofGround_apply (f : α → W) (hs : support f ⊆ M.E)
  (hf : ∀ I ⊆ M.E, (M.Indep I ↔ LinearIndependent 𝔽 (I.restrict f))) (a : α) :
    Rep.ofGround f hs hf a = f a := rfl

/-- A function from `M.E` to a module determines a representation -/
@[simps!] noncomputable def Rep.ofSubtypeFun (f : M.E → W) [DecidablePred (· ∈ M.E)]
    (hf : ∀ (I : Set M.E), M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f)) :
    M.Rep 𝔽 W :=
  Rep.ofGround
  ( fun a ↦ if ha : a ∈ M.E then f ⟨a,ha⟩ else 0 )
  ( by aesop )
  ( by
    intro I hI
    rw [← Subtype.range_val (s := M.E), subset_range_iff_exists_image_eq] at hI
    obtain ⟨I, rfl⟩ := hI
    rw [hf]
    apply linearIndependent_equiv' <| Equiv.Set.image _ _ Subtype.val_injective
    ext ⟨⟨x,hx⟩, hx'⟩
    simp [dif_pos hx] )

/-- A representation gives a representation of any restriction -/
noncomputable def Rep.restrict (v : M.Rep 𝔽 W) (X : Set α) : (M ↾ X).Rep 𝔽 W :=
  Rep.ofGround (indicator X v) ( by simp )
  ( by
    simp only [restrict_ground_eq, restrict_indep_iff]
    intro I hIX
    rw [v.indep_iff, and_iff_left hIX]
    convert Iff.rfl using 2
    ext ⟨e, he⟩
    simp [hIX he] )

@[simp] lemma Rep.restrict_apply (v : M.Rep 𝔽 W) (X : Set α) :
    (v.restrict X : α → W) = indicator X v := rfl

section Simple

lemma Rep.eq_zero_iff (v : M.Rep 𝔽 W) (e : α) (he : e ∈ M.E := by aesop_mat) :
    v e = 0 ↔ M.Loop e := by
  rw [← singleton_not_indep he, v.indep_iff, linearIndependent_unique_iff]
  simp

lemma Rep.eq_zero_of_loop (v : M.Rep 𝔽 W) (h : M.Loop e) : v e = 0 :=
  (v.eq_zero_iff e).2 h

lemma Rep.ne_zero_of_nonloop (v : M.Rep 𝔽 W) (h : M.Nonloop e) : v e ≠ 0 := by
  rw [Ne, v.eq_zero_iff e]; exact h.not_loop

lemma Rep.ne_zero_iff_nonloop (v : M.Rep 𝔽 W) (e : α) :
    v e ≠ 0 ↔ M.Nonloop e := by
  refine ⟨fun hne ↦ ?_, v.ne_zero_of_nonloop⟩
  by_cases he : e ∈ M.E
  · rwa [← not_loop_iff, ← v.eq_zero_iff e]
  simp [v.eq_zero_of_not_mem_ground he] at hne

@[simp]
lemma Rep.ne_zero [M.Loopless] [M.OnUniv] (v : M.Rep 𝔽 W) (e : α) : v e ≠ 0 := by
  simp [v.ne_zero_iff_nonloop]

lemma Rep.loopless_iff (v : M.Rep 𝔽 W) : M.Loopless ↔ ∀ e ∈ M.E, v e ≠ 0 := by
  rw [loopless_iff_forall_nonloop]
  exact ⟨fun h e he ↦ (v.ne_zero_iff_nonloop e).2 (h e he),
    fun h e he ↦ (v.ne_zero_iff_nonloop e).1 (h e he)⟩

lemma Rep.parallel_iff (v : M.Rep 𝔽 W) (he : M.Nonloop e) :
    M.Parallel e f ↔ ∃ (c : 𝔽), c ≠ 0 ∧ c • v f = v e := by
  obtain (hfE | hfE) := em' (f ∈ M.E)
  · refine iff_of_false (fun h ↦ hfE h.mem_ground_right) ?_
    simp [v.eq_zero_of_not_mem_ground hfE, iff_true_intro (v.ne_zero_of_nonloop he).symm]
  obtain (hf | hf) := M.loop_or_nonloop f
  · refine iff_of_false (fun h ↦ h.nonloop_right.not_loop hf) ?_
    simp [v.eq_zero_of_loop hf, iff_true_intro (v.ne_zero_of_nonloop he).symm]

  obtain (rfl | hef) := eq_or_ne e f
  · exact iff_of_true hf.parallel_self ⟨1, one_ne_zero, one_smul ..⟩

  rw [he.parallel_iff_dep hf hef, ← not_indep_iff, v.indep_iff_restrict, not_iff_comm,
    linearIndependent_restrict_pair_iff _ hef (v.ne_zero_of_nonloop he)]
  simp only [ne_eq, not_exists, not_and]
  refine ⟨fun h c h' ↦ ?_, fun h c hc h_eq ↦
    h c⁻¹ (by rw [← h_eq, smul_smul, inv_mul_cancel₀ hc, one_smul])⟩
  have hc : c ≠ 0 := by rintro rfl; exact v.ne_zero_of_nonloop hf (by simp [← h'])
  exact h c⁻¹ (by simpa) <| by rw [← h', smul_smul, inv_mul_cancel₀ hc, one_smul]


lemma Rep.parallel_iff' (v : M.Rep 𝔽 W) (he : M.Nonloop e) :
    M.Parallel e f ↔ ∃ (c : 𝔽ˣ), c • v f = v e := by
  rw [v.parallel_iff he]
  exact ⟨fun ⟨c, hne, heq⟩ ↦ ⟨Units.mk0 c hne, by simpa⟩, fun ⟨c, heq⟩ ↦ ⟨c, by simp, heq⟩⟩

lemma Rep.simple_iff [RankPos M] (v : M.Rep 𝔽 W) :
    M.Simple ↔ ∀ {e f} (_ : e ∈ M.E) (_ : f ∈ M.E) (c : 𝔽), c • (v f) = v e → e = f := by
  simp_rw [simple_iff_loopless_eq_of_parallel_forall, v.loopless_iff]
  refine ⟨fun ⟨h0,h1⟩ e f he _ c h_eq ↦ h1 e f ?_, fun h ↦ ⟨fun e he h0 ↦ ?_, fun e f hef ↦ ?_⟩⟩
  · refine (v.parallel_iff ?_).2 ⟨c, ?_, h_eq⟩
    · rw [← v.ne_zero_iff_nonloop e]; exact h0 _ he
    rintro rfl
    exact h0 e he <| by simp [← h_eq]
  · obtain ⟨f, hf⟩ := M.exists_nonloop
    obtain rfl := h he hf.mem_ground 0 (by simp [h0])
    exact v.ne_zero_of_nonloop hf h0
  obtain ⟨c,-,h_eq⟩ := (v.parallel_iff hef.symm.nonloop_right).1 hef
  exact h (by aesop_mat) (by aesop_mat) c h_eq

lemma Rep.injOn_of_simple (v : M.Rep 𝔽 W) (h : M.Simple) : InjOn v M.E := by
  obtain (hl | hpos) := M.eq_loopyOn_or_rankPos
  · rw [simple_iff_loopless_eq_of_parallel_forall, hl, loopyOn_loopless_iff] at h
    simp [h.1]
  exact fun e he f hf h_eq ↦ (v.simple_iff.1 h) he hf 1 <| by rwa [one_smul, eq_comm]




-- @[simp] lemma simplification_representable_iff :
--     M.simplification.Representable 𝔽 ↔ M.Representable 𝔽 := by
--   obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
--   rw [hM]
--   refine ⟨fun ⟨v⟩ ↦ ?_, fun h ↦ h.minor (simplificationWrt_isRestriction hc).minor⟩
--   rw [← removeLoops_representable_iff, ← preimage_simplificationWrt M hc]
--   exact (v.preimage _).representable

end Simple
