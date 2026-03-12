import Mathlib.LinearAlgebra.Dimension.Free
import Matroid.Connectivity.Skew
-- import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.LinearIndepOn

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommMonoid W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation
universe u v

namespace Matroid

/-- `M.Rep 𝔽 W` is a function from `α` to a module `W` that represents `M`. -/
@[ext] structure Rep (M : Matroid α) (𝔽 W : Type*) [Semiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (indep_iff' : ∀ I, M.Indep I ↔ LinearIndepOn 𝔽 to_fun I)


instance : FunLike (M.Rep 𝔽 W) α W where
  coe v := v.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

@[simp] lemma Rep.to_fun_eq_coe (v : M.Rep 𝔽 W) : v.to_fun = (v : α → W) := rfl

lemma Rep.indep_iff (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndepOn 𝔽 v I :=
  v.indep_iff' I

lemma Rep.onIndep (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndepOn 𝔽 v I :=
  v.indep_iff.1 hI

lemma Rep.injOn_of_indep (v : M.Rep 𝔽 W) (hI : M.Indep I) : InjOn v I :=
  injOn_iff_injective.2 ((v.onIndep hI).injective)

-- lemma Rep.indep_image (v : M.Rep 𝔽 W) (hI : M.Indep I) :
--     LinearIndependent 𝔽 ((↑) : (v '' I) → W) := by
--   rw [← linearIndependent_image <| v.injOn_of_indep hI]
--   exact v.onIndep hI

-- lemma Rep.indep_iff_image_of_inj (v : M.Rep 𝔽 W) (h_inj : InjOn v I) :
--     M.Indep I ↔ LinearIndependent 𝔽 ((↑) : (v '' I) → W) := by
--   refine ⟨v.indep_image, fun hi ↦ ?_⟩
--   rw [v.indep_iff]
--   exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

-- lemma Rep.indep_iff_image (v : M.Rep 𝔽 W) :
--     M.Indep I ↔ LinearIndependent 𝔽 ((↑) : (v '' I) → W) ∧ InjOn v I :=
--   ⟨fun h ↦ ⟨v.indep_image h, v.injOn_of_indep h⟩,
--     fun h ↦ (v.indep_iff_image_of_inj h.2).2 h.1⟩

lemma Rep.eq_zero_iff_not_indep {v : M.Rep 𝔽 W} : v e = 0 ↔ ¬ M.Indep {e} := by
  simp [v.indep_iff]

lemma Rep.eq_zero_iff (v : M.Rep 𝔽 W) (e : α) (he : e ∈ M.E := by aesop_mat) :
    v e = 0 ↔ M.IsLoop e := by
  rw [v.eq_zero_iff_not_indep, singleton_not_indep]

lemma Rep.eq_zero_of_notMem_ground (v : M.Rep 𝔽 W) (he : e ∉ M.E) : v e = 0 := by
  rw [v.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

lemma Rep.eq_zero_of_isLoop (v : M.Rep 𝔽 W) (h : M.IsLoop e) : v e = 0 :=
  (v.eq_zero_iff e).2 h

lemma Rep.ne_zero_of_isNonloop (v : M.Rep 𝔽 W) (h : M.IsNonloop e) : v e ≠ 0 := by
  rw [Ne, v.eq_zero_iff e]; exact h.not_isLoop

lemma Rep.ne_zero_iff_isNonloop (v : M.Rep 𝔽 W) (e : α) : v e ≠ 0 ↔ M.IsNonloop e := by
  refine ⟨fun hne ↦ ?_, v.ne_zero_of_isNonloop⟩
  by_cases he : e ∈ M.E
  · rwa [← not_isLoop_iff, ← v.eq_zero_iff e]
  simp [v.eq_zero_of_notMem_ground he] at hne

lemma Rep.support_subset_ground (v : M.Rep 𝔽 W) : support v ⊆ M.E :=
  fun _ he ↦ by_contra <| fun h' ↦ he (v.eq_zero_of_notMem_ground h')

lemma Rep.mem_ground_of_apply_ne_zero {v : M.Rep 𝔽 W} (hv : v e ≠ 0) : e ∈ M.E :=
  v.support_subset_ground hv

lemma Indep.rep_apply_ne_zero_of_mem {v : M.Rep 𝔽 W} (hI : M.Indep I) (heI : e ∈ I) :
    v e ≠ 0 := by
  rw [Ne, Rep.eq_zero_iff_not_indep, not_not]
  exact hI.subset (by simpa)

lemma Rep.isBasis'_iff (v : M.Rep 𝔽 W) :
    M.IsBasis' I X ↔ I ⊆ X ∧ LinearIndepOn 𝔽 v I ∧ v '' X ⊆ span 𝔽 (v '' I) := by
  have aux ⦃I J : Set α⦄ : M.Indep J ∧ J ⊆ X → I ⊆ J → M.Indep I ∧ I ⊆ X :=
    fun h hJI ↦ ⟨h.1.subset hJI, hJI.trans h.2⟩
  simp only [IsBasis', maximal_iff_forall_insert aux, insert_subset_iff, not_and, image_subset_iff]
  simp +contextual only [v.indep_iff, linearIndepOn_insert_iff, imp_false, and_imp, iff_def,
    true_and, not_true_eq_false, not_imp_not, forall_const, and_self]
  refine ⟨fun hI hIX h e heX ↦ (em (e ∈ I)).elim (fun heI ↦ ?_) fun heI ↦ h e heI heX,
    fun hIX hI hX e heI heX ↦ hX heX⟩
  exact mem_of_mem_of_subset heI <| (subset_preimage_image v I).trans <| preimage_mono subset_span

lemma Rep.mem_closure_iff (v : M.Rep 𝔽 W) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ v e ∈ span 𝔽 (v '' X) := by
  obtain ⟨I, hIX⟩ := M.exists_isBasis' X
  have aux : span 𝔽 (v '' I) = span 𝔽 (v '' X) :=
    (span_mono (image_mono hIX.subset)).antisymm <| span_le.2 (v.isBasis'_iff.1 hIX).2.2
  rw [← hIX.closure_eq_closure, ← aux, ← not_iff_not, (v.onIndep hIX.indep).notMem_span_iff,
    hIX.indep.notMem_closure_iff, v.indep_iff]

lemma Rep.closure_eq (v : M.Rep 𝔽 W) (X : Set α) : M.closure X = (v ⁻¹' span 𝔽 (v '' X)) ∩ M.E := by
  ext e
  by_cases he : e ∈ M.E
  · rw [v.mem_closure_iff, mem_inter_iff, and_iff_left he, mem_preimage, SetLike.mem_coe]
  simp [he, notMem_subset (M.closure_subset_ground X) he]

lemma Rep.mem_closure_iff' (v : M.Rep 𝔽 W) :
    e ∈ M.closure X ↔ v e ∈ span 𝔽 (v '' X) ∧ e ∈ M.E := by
  simp [v.closure_eq]

lemma Rep.span_le_of_closure_subset (v : M.Rep 𝔽 W) (hXY : M.closure X ⊆ M.closure Y) :
    span 𝔽 (v '' X) ≤ span 𝔽 (v '' Y) := by
  rw [span_le]
  rintro _ ⟨e, he, rfl⟩
  obtain heE | heE := em' (e ∈ M.E)
  · simp [v.eq_zero_of_notMem_ground heE]
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

@[simp] lemma Rep.span_image_loops (v : M.Rep 𝔽 W) : span 𝔽 (v '' (M.loops)) = ⊥ := by
  simp [v.span_closure_congr (M.closure_loops)]

/- If some linear combination of columns of `M.E` is zero, the nonzero indices form a cyclic set.-/
-- lemma Rep.cyclic_of_linearCombination (v : M.Rep 𝔽 W) (c : α →₀ 𝔽)
-- (hcE : (c.support : Set α) ⊆ M.E)
--     (hcv : c.linearCombination 𝔽 v = 0) : M.Cyclic c.support := by
--   rw [cyclic_iff_forall_mem_closure_diff_singleton]
--   intro e he
--   rw [v.mem_closure_iff (hcE he), Finsupp.mem_span_image_iff_linearCombination]
--   have hce : c e ≠ 0 := by simpa using he
--   use - (c e)⁻¹ • (c - Finsupp.single e (c e))
--   suffices ∀ (x : α), (¬c x = 0 → x = e) → c x - (Finsupp.single e (c e)) x = 0 by
--     simpa [Finsupp.mem_supported', hcv, hce, ← smul_assoc]
--   intro x
--   obtain rfl | hne := eq_or_ne x e
--   · simp
--   simp +contextual [hne, Finsupp.single_apply_eq_zero]

-- lemma Rep.exists_finsupp_of_isCircuit (v : M.Rep 𝔽 W) {C : Finset α} (hC : M.IsCircuit C) :
--     ∃ c : α →₀ 𝔽, c.support = C ∧ c.linearCombination 𝔽 v = 0 := by
--   have hC' := hC.not_indep
--   rw [v.indep_iff] at hC'
--   obtain ⟨c, h, hc, h0⟩ := linearDepOn_iff.1 hC'
--   refine ⟨c, subset_antisymm (by simpa using h) fun e heC ↦ ?_, hc⟩
--   contrapose! h0
--   refine (linearIndepOn_iff.1 <| v.indep_iff.1 <| hC.diff_singleton_indep heC) _ ?_ hc
--   simpa [Finsupp.mem_supported, subset_diff_singleton_iff, h0] using h

lemma Rep.skew_iff_span_disjoint (v : M.Rep 𝔽 W) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    M.Skew X Y ↔ Disjoint (span 𝔽 (v '' X)) (span 𝔽 (v '' Y)) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨J, hJ⟩ := M.exists_isBasis Y
  rw [← skew_iff_isBases_skew hI hJ, hI.indep.skew_iff_disjoint_union_indep hJ.indep,
    ← v.span_closure_congr hI.closure_eq_closure, ← v.span_closure_congr hJ.closure_eq_closure,
    v.indep_iff]
  by_cases hdj : Disjoint I J
  ·  rw [linearIndepOn_union_iff hdj, ← v.indep_iff, ← v.indep_iff, and_iff_right hdj,
      and_iff_right hI.indep, and_iff_right hJ.indep]
  obtain ⟨x, hxI, hxJ⟩ := not_disjoint_iff.1 hdj
  simp only [hdj, false_and, disjoint_def, false_iff, not_forall, exists_prop]
  refine ⟨v x, (subset_span (mem_image_of_mem v hxI)), (subset_span (mem_image_of_mem v hxJ)), ?_⟩
  rw [v.eq_zero_iff_not_indep, not_not]
  exact hI.indep.subset (by simpa)

/-! ### Constructors -/

/-- A function with support contained in `M.E` that gives the correct independent sets
  within the ground set gives a representation -/
@[simps] def Rep.ofGround (v : α → W) (h_support : support v ⊆ M.E)
    (h_indep : ∀ I ⊆ M.E, M.Indep I ↔ LinearIndepOn 𝔽 v I) : M.Rep 𝔽 W where
  to_fun := v
  indep_iff' I := (em (I ⊆ M.E)).elim (h_indep _) fun hI ↦ iff_of_false (mt Indep.subset_ground hI)
    fun hi ↦ hI fun _ heI ↦ h_support <| hi.ne_zero heI

@[simp] lemma Rep.ofGround_apply (f : α → W) (hs : support f ⊆ M.E)
  (hf : ∀ I ⊆ M.E, (M.Indep I ↔ LinearIndependent 𝔽 (I.restrict f))) (a : α) :
    Rep.ofGround f hs hf a = f a := rfl

/-- A function from `M.E` to a module determines a representation -/
@[simps!] noncomputable def Rep.ofSubtypeFun (f : M.E → W) [DecidablePred (· ∈ M.E)]
    (hf : ∀ (I : Set M.E), M.Indep (Subtype.val '' I) ↔ LinearIndepOn 𝔽 f I) :
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
    simp +contextual only [restrict_ground_eq, restrict_indep_iff, v.indep_iff, and_true]
    exact fun I hIX ↦ linearIndepOn_congr <| eqOn_indicator.symm.mono hIX )

@[simp] lemma Rep.restrict_apply (v : M.Rep 𝔽 W) (X : Set α) :
    (v.restrict X : α → W) = indicator X v := rfl

section Simple

@[simp]
lemma Rep.ne_zero [M.Loopless] [M.OnUniv] (v : M.Rep 𝔽 W) (e : α) : v e ≠ 0 := by
  simp [v.ne_zero_iff_isNonloop]

lemma Rep.loopless_iff (v : M.Rep 𝔽 W) : M.Loopless ↔ ∀ e ∈ M.E, v e ≠ 0 := by
  rw [loopless_iff_forall_isNonloop]
  exact ⟨fun h e he ↦ (v.ne_zero_iff_isNonloop e).2 (h e he),
    fun h e he ↦ (v.ne_zero_iff_isNonloop e).1 (h e he)⟩

lemma Rep.parallel_iff (v : M.Rep 𝔽 W) (he : M.IsNonloop e) :
    M.Parallel e f ↔ ∃ (c : 𝔽), c ≠ 0 ∧ c • v f = v e := by
  rw [he.parallel_iff_mem_closure, v.closure_eq]
  simp only [image_singleton, mem_inter_iff, mem_preimage, SetLike.mem_coe, he.mem_ground, and_true,
    ne_eq, mem_span_singleton]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨a, fun ha0 ↦ v.ne_zero_of_isNonloop he ?_, ha⟩, fun ⟨c, hc0, hc⟩ ↦ ⟨c, hc⟩⟩
  rw [← ha, ha0, zero_smul]

lemma Rep.parallel_iff' (v : M.Rep 𝔽 W) (he : M.IsNonloop e) :
    M.Parallel e f ↔ ∃ (c : 𝔽ˣ), c • v f = v e := by
  rw [v.parallel_iff he]
  exact ⟨fun ⟨c, hne, heq⟩ ↦ ⟨Units.mk0 c hne, by simpa⟩, fun ⟨c, heq⟩ ↦ ⟨c, by simp, heq⟩⟩

lemma Rep.simple_iff [RankPos M] (v : M.Rep 𝔽 W) :
    M.Simple ↔ ∀ {e f} (_ : e ∈ M.E) (_ : f ∈ M.E) (c : 𝔽), c • (v f) = v e → e = f := by
  simp_rw [simple_iff_loopless_eq_of_parallel_forall, v.loopless_iff]
  refine ⟨fun ⟨h0,h1⟩ e f he _ c h_eq ↦ h1 e f ?_, fun h ↦ ⟨fun e he h0 ↦ ?_, fun e f hef ↦ ?_⟩⟩
  · refine (v.parallel_iff ?_).2 ⟨c, ?_, h_eq⟩
    · rw [← v.ne_zero_iff_isNonloop e]; exact h0 _ he
    rintro rfl
    exact h0 e he <| by simp [← h_eq]
  · obtain ⟨f, hf⟩ := M.exists_isNonloop
    obtain rfl := h he hf.mem_ground 0 (by simp [h0])
    exact v.ne_zero_of_isNonloop hf h0
  obtain ⟨c,-,h_eq⟩ := (v.parallel_iff hef.symm.isNonloop_right).1 hef
  exact h (by aesop_mat) (by aesop_mat) c h_eq

lemma Rep.injOn_of_simple (v : M.Rep 𝔽 W) [h : M.Simple] : InjOn v M.E := by
  obtain (hl | hpos) := M.eq_loopyOn_or_rankPos
  · rw [simple_iff_loopless_eq_of_parallel_forall, hl, loopyOn_isLoopless_iff] at h
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
