import Matroid.Parallel

open Set Set.Notation

variable {α : Type*} {M N : Matroid α} {e f g : α} {I X P D : Set α}

namespace Matroid
-- section Simple

class Simple (M : Matroid α) : Prop where
  (parallel_iff_eq : ∀ {e f}, e ∈ M.E → (M.Parallel e f ↔ e = f))

theorem Parallel.eq [Simple M] (h : M.Parallel e f) : e = f := by
  rwa [Simple.parallel_iff_eq h.mem_ground_left] at h

theorem parallel_iff_eq [Simple M] (he : e ∈ M.E := by aesop_mat) :
    M.Parallel e f ↔ e = f :=
  Simple.parallel_iff_eq he

theorem not_parallel_of_ne (M : Matroid α) [Simple M] (hef : e ≠ f) : ¬ M.Parallel e f :=
  fun h ↦ hef h.eq

instance [Simple M] : Loopless M := by
  rw [loopless_iff_forall_nonloop]
  exact fun e he ↦ ((parallel_iff_eq he).2 rfl).nonloop_left

instance {α : Type*} : Simple (emptyOn α) :=
  ⟨fun he ↦ by simp at he⟩

theorem simple_iff_loopless_eq_of_parallel_forall:
    Simple M ↔ (M.Loopless ∧ ∀ e f, M.Parallel e f → e = f) :=
  ⟨fun h ↦ ⟨by infer_instance, fun _ _ ↦ Parallel.eq⟩,
    fun ⟨_,h⟩ ↦ ⟨fun heE ↦ ⟨h _ _,by rintro rfl; exact (toNonloop heE).parallel_self⟩⟩⟩

theorem parallel_class_eq [Simple M] (he : e ∈ M.E := by aesop_mat) :
    {f | M.Parallel e f} = {e} := by
  simp_rw [parallel_iff_eq he, setOf_eq_eq_singleton']

@[simp] theorem cl_singleton_eq [Simple M] (he : e ∈ M.E := by aesop_mat) : M.cl {e} = {e} := by
  rw [cl_eq_parallel_class_union_loops, parallel_class_eq he, cl_empty_eq_empty, union_empty]

/-- We need `RkPos` or something similar here, since otherwise the matroid whose only element is
  a loop is a counterexample. -/
theorem simple_iff_cl_subset_self_forall [RkPos M] :
    M.Simple ↔ ∀ e, M.Nonloop e → M.cl {e} ⊆ {e} := by
  refine ⟨fun h e he ↦ by rw [cl_singleton_eq], fun h ↦ ?_⟩
  have hl : M.Loopless := by
    rw [loopless_iff_forall_not_loop]
    intro e _ hel
    obtain ⟨f, hf⟩ := M.exists_nonloop
    obtain (rfl : e = f) := (h f hf).subset (hel.mem_cl _)
    exact hf.not_loop hel
  rw [simple_iff_loopless_eq_of_parallel_forall, and_iff_right hl]
  exact fun e f hp ↦ (h _ hp.nonloop_right) hp.mem_cl

theorem cl_eq_self_of_subset_singleton [Simple M] (he : e ∈ M.E) (hX : X ⊆ {e}) : M.cl X = X := by
  obtain (rfl | rfl) := subset_singleton_iff_eq.1 hX
  · exact M.cl_empty_eq_empty
  exact cl_singleton_eq he

theorem singleton_flat [Simple M] (he : e ∈ M.E := by aesop_mat) : M.Flat {e} := by
  rw [← cl_singleton_eq]; apply cl_flat

theorem pair_indep [Simple M] (he : e ∈ M.E := by aesop_mat) (hf : f ∈ M.E := by aesop_mat) :
    M.Indep {e,f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · rw [pair_eq_singleton, indep_singleton]; exact toNonloop he
  rwa [← not_dep_iff, ← (toNonloop he).parallel_iff_dep (toNonloop hf) hne, parallel_iff_eq he]

theorem indep_of_encard_le_two [Simple M] (h : I.encard ≤ 2) (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  have hne : I.encard ≠ ⊤ := (h.trans_lt (by exact (cmp_eq_lt_iff 2 ⊤).mp rfl : (2 : ℕ∞) < ⊤ )).ne
  rw [le_iff_lt_or_eq, encard_eq_two, ← ENat.add_one_le_iff hne, (by norm_num : (2 : ℕ∞) = 1 + 1),
    WithTop.add_le_add_iff_right, encard_le_one_iff_eq] at h
  · obtain (rfl | ⟨x, rfl⟩) | ⟨x, y, -, rfl⟩ := h
    · exact M.empty_indep
    · refine indep_singleton.2 (toNonloop (by aesop_mat))
    exact pair_indep
  norm_num

theorem er_pair_eq [Simple M] (hef : e ≠ f) (he : e ∈ M.E := by aesop_mat)
    (hf : f ∈ M.E := by aesop_mat) : M.er {e,f} = 2 := by
  rw [(pair_indep he).er, encard_pair hef]

theorem Dep.two_lt_encard [Simple M] (hD : M.Dep D) : 2 < D.encard :=
  lt_of_not_le fun hle ↦ hD.not_indep (indep_of_encard_le_two hle)

theorem simple_iff_three_le_girth : M.Simple ↔ 3 ≤ M.girth := by
  rw [le_girth_iff]
  refine ⟨fun h C hC ↦ le_of_not_lt fun hlt ↦ ?_, fun h ↦ ?_⟩
  · exact hC.dep.not_indep <| indep_of_encard_le_two (ENat.le_of_lt_add_one hlt)
  rw [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_circuit, and_iff_left]
  · exact fun C hC ↦ (show (1 : ℕ∞) < 3 from Nat.one_lt_ofNat).trans_le (h C hC)
  refine fun e f hef ↦ by_contra fun hne ↦ ?_
  have hcon := (h _ (hef.circuit_of_ne hne)).trans_eq (encard_pair hne)
  norm_num at hcon

theorem simple_iff_forall_circuit : M.Simple ↔ ∀ C, M.Circuit C → 2 < C.encard := by
  refine ⟨fun h C hC ↦ hC.dep.two_lt_encard, fun h ↦  ?_⟩
  rw [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_circuit]
  refine ⟨fun C hC ↦ lt_of_le_of_lt (by norm_num) (h C hC), fun e f hef ↦ by_contra fun hne ↦ ?_⟩
  exact (h _ ((parallel_iff_circuit hne).1 hef)).ne (by rw [encard_pair hne])

-- theorem simple_iff_forall_pair_indep :
--     M.Simple ↔ ∀ {e f} (_ : e ∈ M.E) (_ : f ∈ M.E), M.Indep {e,f} := by
--   refine ⟨fun h e f he hf ↦ pair_indep he hf,
--     fun h ↦ ⟨fun {e f} he ↦
--       ⟨fun hp ↦ by_contra fun hef ↦ (hp.dep_of_ne hef).not_indep <| h he hp.mem_ground_right, ?_ ⟩⟩⟩
--   rintro rfl
--   have hee := h he he
--   simp only [mem_singleton_iff, insert_eq_of_mem, indep_singleton] at hee
--   exact hee.parallel_self

-- theorem Simple.map_iso {α β : Type*} {M : Matroid α} {N : Matroid β} (hM : M.Simple) (hMN : M ≂ N) :
--     N.Simple := by
--   rw [simple_iff_forall_pair_indep] at *
--   rintro e f he hf
--   obtain (⟨rfl,rfl⟩ | ⟨⟨i⟩⟩) := hMN
--   · simp at he
--   have := i.on_indep <| hM (i.symm.map_mem he) (i.symm.map_mem hf)
--   rwa [image_pair, i.symm_apply_apply_mem hf, i.symm_apply_apply_mem he] at this

-- theorem simple_iff_forall_parallel_class [Loopless M] :
--     M.Simple ↔ ∀ P ∈ M.parallelClasses, encard P = 1 := by
--   simp only [simple_iff_loopless_eq_of_parallel_forall, and_iff_right (by assumption),
--     mem_parallelClasses_iff, forall_exists_index, and_imp]
--   refine ⟨fun h P e he ↦ ?_, fun h e f hef ↦ ?_⟩
--   · rintro rfl
--     simp [show (∀ f, M.Parallel e f ↔ e = f) from fun f ↦ ⟨h e f, fun h ↦ h ▸ he.parallel_self⟩]
--   specialize h {e | M.Parallel e f} e hef.nonloop_left
--   simp_rw [hef.parallel_iff_right, parallel_comm, true_imp_iff, encard_eq_one] at h
--   obtain ⟨x, hx⟩ := h
--   simp only [ext_iff, mem_setOf_eq, mem_singleton_iff] at hx
--   rw [(hx e).1 hef.symm, (hx f).1 hef.nonloop_right.parallel_self]

-- @[simp] theorem simple_trivialOn_iff {I E : Set α} : (trivialOn I E).Simple ↔ E ⊆ I := by
--   simp only [simple_iff_forall_pair_indep, trivialOn_ground, mem_singleton_iff,
--     trivialOn_indep_iff', subset_inter_iff]
--   refine ⟨fun h x hxE ↦ by simpa using (h hxE hxE).1, fun h {e f} he hf ↦ ⟨subset_trans ?_ h, ?_⟩⟩
--   <;> rintro x (rfl | rfl) <;> assumption

-- instance simple_freeOn {E : Set α} : (freeOn E).Simple := by
--   rw [← trivialOn_eq_freeOn, simple_trivialOn_iff]

-- @[simp] theorem simple_loopyOn_iff {E : Set α} : (loopyOn E).Simple ↔ E = ∅ := by
--   rw [← trivialOn_eq_loopyOn, simple_trivialOn_iff, subset_empty_iff]

-- theorem Indep.restr_simple (hI : M.Indep I) : (M ↾ I).Simple := by
--   simp only [simple_iff_forall_pair_indep, restrict_ground_eq, mem_singleton_iff,
--     restrict_indep_iff, pair_subset_iff]
--   rintro e f he hf
--   exact ⟨hI.subset (pair_subset he hf), he, hf⟩

-- theorem Simple.subset_ground {X : Set α} (_ : (M ↾ X).Simple) : X ⊆ M.E :=
--   fun _ hx ↦ (toNonloop (M := M ↾ X) hx).of_restrict.mem_ground

-- theorem Simple.subset {X Y : Set α} (hY : (M ↾ Y).Simple) (hXY : X ⊆ Y) : (M ↾ X).Simple := by
--   simp only [simple_iff_forall_pair_indep, restrict_ground_eq, mem_singleton_iff,
--     restrict_indep_iff, pair_subset_iff] at *
--   aesop

-- theorem exists_loop_or_para_of_not_simple (hM : ¬ M.Simple) :
--     (∃ e, M.Loop e) ∨ ∃ e f, M.Parallel e f ∧ e ≠ f := by
--   by_contra! h
--   rw [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_not_loop] at hM
--   push_neg at hM
--   obtain ⟨e, f, hef, hne⟩ := hM (fun e _ ↦ h.1 e)
--   exact hne <| h.2 e f hef

-- theorem Loopless.of_restrict_contract {C : Set α} (hC : (M ↾ C).Loopless) (h : (M ／ C).Loopless) :
--     M.Loopless := by
--   rw [loopless_iff_cl_empty] at *
--   rw [contract_loops_eq, diff_eq_empty] at h
--   rw [restrict_cl_eq', empty_inter, union_empty_iff] at hC
--   rw [← inter_union_diff (s := M.cl ∅) (t := C), hC.1, empty_union, diff_eq_empty]
--   exact (M.cl_subset_cl <| empty_subset C).trans h

-- theorem Simple.of_restrict_contract {C : Set α} (hC : (M ↾ C).Simple) (h : (M ／ C).Simple) :
--     M.Simple := by
--   rw [simple_iff_loopless_eq_of_parallel_forall] at h hC ⊢
--   obtain ⟨hl, h⟩ := h
--   obtain ⟨hCl, hC⟩ := hC
--   simp only [restrict_parallel_iff, and_imp] at hC
--   refine ⟨(hCl.of_restrict_contract hl), fun e f hef ↦ ?_⟩
--   by_cases heC : e ∈ C
--   · by_cases hfC : f ∈ C
--     · exact hC _ _ hef heC hfC
--     refine by_contra fun hne ↦ not_loop (M ／ C) f ?_
--     exact (hef.loop_of_contract hne).minor ⟨hef.mem_ground_right, hfC⟩ (contract_minor_of_mem _ heC)
--   by_cases hfC : f ∈ C
--   · refine by_contra fun (hne : e ≠ f) ↦ not_loop (M ／ C) e ?_
--     exact (hef.symm.loop_of_contract hne.symm).minor ⟨hef.mem_ground_left, heC⟩
--       (contract_minor_of_mem _ hfC)
--   apply h
--   rw [parallel_iff, contract_cl_eq, contract_cl_eq, ← cl_union_cl_left_eq, hef.cl_eq_cl,
--     cl_union_cl_left_eq, and_iff_left rfl]
--   exact ⟨toNonloop ⟨hef.mem_ground_left, heC⟩, toNonloop ⟨hef.mem_ground_right, hfC⟩⟩

-- theorem Indep.simple_of_contract_simple (hI : M.Indep I) (h : (M ／ I).Simple) : M.Simple :=
--   hI.restr_simple.of_restrict_contract h


-- end Simple

-- section Simplification

-- variable {M : Matroid α} {c : α → α}

-- /-- A function that chooses a representative from the parallel class for each nonloop,
--   and is the identity elsewhere. Such a function corresponds to a restriction of `M`
--   that is simple  -/
-- def ParallelChoiceFunction (M : Matroid α) (c : α → α) : Prop :=
--   (∀ {e}, ¬ M.Nonloop e → c e = e) ∧ (∀ {e}, M.Nonloop e → M.Parallel e (c e)) ∧
--     (∀ {e f}, M.Nonloop e → M.Nonloop f → (M.Parallel e f ↔ c e = c f))

-- theorem ParallelChoiceFunction.parallel_iff_of_nonloop (hc : M.ParallelChoiceFunction c)
--   (he : M.Nonloop e) (hf : M.Nonloop f) : M.Parallel e f ↔ c e = c f := hc.2.2 he hf

-- theorem ParallelChoiceFunction.eq_of_parallel (hc : M.ParallelChoiceFunction c)
--     (hef : M.Parallel e f) : c e = c f :=
--   (hc.parallel_iff_of_nonloop hef.nonloop_left hef.nonloop_right).1 hef

-- theorem ParallelChoiceFunction.parallel_apply (hc : M.ParallelChoiceFunction c)
--     (he : M.Nonloop e) : M.Parallel e (c e) :=
--   hc.2.1 he

-- theorem ParallelChoiceFunction.nonloop (hc : M.ParallelChoiceFunction c)
--     (he : M.Nonloop e) : M.Nonloop (c e) :=
--   (hc.parallel_apply he).nonloop_right

-- theorem ParallelChoiceFunction.eq_self (hc : M.ParallelChoiceFunction c) (he : ¬M.Nonloop e) :
--     c e = e := hc.1 he

-- theorem ParallelChoiceFunction.idem (hc : M.ParallelChoiceFunction c) (e : α) : c (c e) = c e := by
--   obtain (he | he) := em (M.Nonloop e)
--   · rw [hc.eq_of_parallel]
--     rw [parallel_comm]
--     exact hc.parallel_apply he
--   rw [hc.eq_self he, hc.eq_self he]

-- theorem ParallelChoiceFunction.nonloop_apply_iff (hc : M.ParallelChoiceFunction c) :
--     M.Nonloop (c e) ↔ M.Nonloop e := by
--   refine ⟨fun h ↦ by_contra fun he ↦ ?_, hc.nonloop⟩
--   rw [hc.eq_self he] at h
--   exact he h

-- theorem ParallelChoiceFunction.parallel_of_apply_eq (hc : M.ParallelChoiceFunction c)
--     (he : M.Nonloop e) (hef : c e = c f) : M.Parallel e f := by
--   apply (hc.parallel_iff_of_nonloop he _).2 hef
--   rwa [← hc.nonloop_apply_iff, ← hef, hc.nonloop_apply_iff]

-- theorem ParallelChoiceFunction.preimage_image_setOf_nonloop (hc : M.ParallelChoiceFunction c) :
--     c ⁻¹' (c '' {e | M.Nonloop e}) = {e | M.Nonloop e} := by
--   simp only [ext_iff, mem_preimage, mem_image, mem_setOf_eq]
--   exact fun x ↦ ⟨fun ⟨y, hy, hyx⟩ ↦ (hc.parallel_of_apply_eq hy hyx).nonloop_right,
--     fun hx ↦ ⟨_, hx, rfl⟩⟩

-- theorem ParallelChoiceFunction.image_setOf_nonloop_subset (hc : M.ParallelChoiceFunction c) :
--     c '' {e | M.Nonloop e} ⊆ {e | M.Nonloop e} := by
--   rintro _ ⟨e, he, rfl⟩; exact hc.nonloop he

-- theorem ParallelChoiceFunction.injOn (hc : M.ParallelChoiceFunction c) (hX : (M ↾ X).Simple) :
--     InjOn c X := by
--   simp only [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_nonloop,
--     restrict_ground_eq, restrict_nonloop_iff, restrict_parallel_iff, and_imp] at hX
--   exact fun e he f hf hef ↦ hX.2 _ _ (hc.parallel_of_apply_eq (hX.1 _ he).1 hef) he hf

-- /-- Any simple restriction of `M` can be extended to a parallel choice function. -/
-- theorem extends_to_parallelChoiceFunction {M : Matroid α} {X : Set α} (hX : (M ↾ X).Simple) :
--     ∃ c, M.ParallelChoiceFunction c ∧ EqOn c id X := by
--   classical
--   have hc : ∀ {x}, M.Nonloop x → {y | M.Parallel x y}.Nonempty :=
--     fun {x} hx ↦ ⟨x, hx.parallel_self⟩

--   set φ := fun e ↦ if he : M.Nonloop e then
--     (if heX : ∃ x ∈ X, M.Parallel e x then heX.choose else (hc he).some) else e with hφ_def

--   have hnl : ∀ {e}, M.Nonloop e → M.Parallel e (φ e) := by
--     intro e
--     simp only [hφ_def]
--     split_ifs with h he
--     · exact fun _ ↦ he.choose_spec.2
--     · exact fun _ ↦ (hc h).some_mem
--     exact Nonloop.parallel_self

--   have h_eq : ∀ {e} {f}, M.Parallel (φ e) (φ f) → φ e = φ f := by
--     intro e f
--     simp only [hφ_def]
--     obtain (he | he) := em' (M.Nonloop e)
--     · rw [dif_neg he]
--       exact fun h ↦ (he h.nonloop_left).elim
--     obtain (hf | hf) := em' (M.Nonloop f)
--     · rw [dif_neg hf]
--       exact fun h ↦ (hf h.nonloop_right).elim
--     rw [dif_pos he, dif_pos hf]
--     split_ifs with heX hfX hfX <;> intro hp
--     · refine Parallel.eq (M := M ↾ X) ?_
--       rw [restrict_parallel_iff]
--       exact ⟨hp, heX.choose_spec.1, hfX.choose_spec.1⟩
--     · exact (hfX ⟨heX.choose, heX.choose_spec.1, (hp.trans (hc hf).some_mem.symm).symm⟩).elim
--     · exact (heX ⟨hfX.choose, hfX.choose_spec.1, Parallel.trans (hc he).some_mem hp⟩).elim
--     convert rfl using 2
--     simp only [Set.ext_iff, mem_setOf_eq]
--     have hef := (Parallel.trans (hc he).some_mem hp).trans (hc hf).some_mem.symm
--     exact fun _ ↦ ⟨hef.trans, hef.symm.trans⟩

--   refine ⟨φ, ⟨fun {e} he ↦ by simp [hφ_def,he], fun he ↦ hnl he, fun {e} {f} he hf ↦ ?_⟩,
--     fun e heX ↦ ?_⟩
--   · exact ⟨fun h ↦ h_eq <| (hnl he).symm.trans (h.trans (hnl hf)),
--       fun h ↦ (hnl he).trans (h ▸ (hnl hf).symm)⟩

--   obtain ⟨hnl',-⟩ := restrict_nonloop_iff.1 <| toNonloop (M := M ↾ X) heX

--   refine Parallel.eq (M := M ↾ X) ?_
--   rw [restrict_parallel_iff, id, and_iff_right ((hnl hnl').symm), and_iff_left heX]
--   simp only [hφ_def]
--   have he' : ∃ x ∈ X, M.Parallel e x := by
--     exact ⟨e, heX, hnl'.parallel_self⟩
--   rw [dif_pos hnl', dif_pos he']
--   exact he'.choose_spec.1

-- theorem exists_parallelChoiceFunction (M : Matroid α) : ∃ c, M.ParallelChoiceFunction c := by
--   obtain ⟨c, hc, -⟩ := extends_to_parallelChoiceFunction (M := M) (X := ∅) (by simp; infer_instance)
--   exact ⟨c,hc⟩

-- @[simp] theorem parallelChoiceFunction_removeLoops_iff :
--     M.removeLoops.ParallelChoiceFunction c ↔ M.ParallelChoiceFunction c := by
--   simp [ParallelChoiceFunction]

-- /-- The simplification of `M` (with respect to a choice function `c`) as a restriction of `M`. -/
-- @[pp_dot] def simplificationWrt (M : Matroid α) (c : α → α) : Matroid α :=
--   M ↾ (c '' {e | M.Nonloop e})

-- @[simp] theorem removeLoops_simplificationWrt_eq (M : Matroid α) (c : α → α)
--     (hc : M.ParallelChoiceFunction c) :
--     M.removeLoops.simplificationWrt c = M.simplificationWrt c := by
--   simp_rw [simplificationWrt, removeLoops_eq_restr, restrict_nonloop_iff, mem_setOf_eq, and_self]
--   rw [restrict_restrict_eq]
--   exact ParallelChoiceFunction.image_setOf_nonloop_subset hc

-- /-- The simplification of `M` relative to a classically chosen parallel choice function.
--   Defined to depend only on `M.removeLoops`, so the same choice is made even if loops
--   are removed/added to `M`. -/
-- @[pp_dot] def simplification (M : Matroid α) : Matroid α :=
--   M.removeLoops.simplificationWrt M.removeLoops.exists_parallelChoiceFunction.choose

-- theorem simplification_eq_wrt (M : Matroid α) :
--     M.simplification = M.simplificationWrt M.removeLoops.exists_parallelChoiceFunction.choose := by
--   rw [simplification, removeLoops_simplificationWrt_eq]
--   simpa using M.removeLoops.exists_parallelChoiceFunction.choose_spec

-- theorem exists_simplification_eq_wrt (M : Matroid α) :
--     ∃ c, M.ParallelChoiceFunction c ∧ M.simplification = M.simplificationWrt c := by
--   use M.removeLoops.exists_parallelChoiceFunction.choose
--   rw [simplification_eq_wrt]
--   simpa using M.removeLoops.exists_parallelChoiceFunction.choose_spec

-- @[simp] theorem removeLoops_simplification_eq (M : Matroid α) :
--     M.removeLoops.simplification = M.simplification := by
--   simp [simplification]

-- @[simp] theorem simplificationWrt_ground_eq (M : Matroid α) (c : α → α) :
--   (M.simplificationWrt c).E = c '' {e | M.Nonloop e} := rfl

-- theorem Nonloop.mem_simplificationWrt_ground (he : M.Nonloop e) (c : α → α) :
--     c e ∈ (M.simplificationWrt c).E := ⟨_, he, rfl⟩

-- theorem simplificationWrt_simple (M : Matroid α) {c : α → α}
--     (hc : M.ParallelChoiceFunction c) : (M.simplificationWrt c).Simple := by
--   simp_rw [simple_iff_loopless_eq_of_parallel_forall, loopless_iff_forall_nonloop,
--     simplificationWrt, restrict_ground_eq, restrict_nonloop_iff, mem_image]
--   simp only [mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
--     restrict_parallel_iff, mem_image]
--   use fun e he ↦ ⟨(hc.2.1 he).nonloop_right, ⟨_, he, rfl⟩⟩
--   rintro e f hef x hx rfl y hy rfl
--   rw [← hc.2.2 hx hy]
--   exact ((hef.trans (hc.2.1 hy).symm).symm.trans (hc.2.1 hx).symm).symm

-- instance simplification_simple (M : Matroid α) : M.simplification.Simple := by
--   obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
--   rw [hM]
--   exact simplificationWrt_simple M hc

-- theorem comap_simplificationWrt (M : Matroid α) (hc : M.ParallelChoiceFunction c) :
--     (M.simplificationWrt c).comap c = M.removeLoops := by
--   simp only [simplificationWrt, removeLoops_eq_restr, eq_iff_indep_iff_indep_forall,
--     comap_ground_eq, restrict_ground_eq, hc.preimage_image_setOf_nonloop, comap_indep_iff,
--     restrict_indep_iff, image_subset_iff, true_and]
--   intro I hI
--   simp only [hI, and_true]
--   refine ⟨fun ⟨hi, hinj⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
--   · exact hi.of_parallelMap hinj (fun e heI ↦ hc.parallel_apply (hI heI))
--   · exact h.parallelMap (fun e heI ↦ hc.parallel_apply (hI heI))
--   exact hc.injOn h.restr_simple

-- /-- Any two simplifications are isomorphic -/
-- noncomputable def simplificationWrt_iso {c c' : α → α} (hc : M.ParallelChoiceFunction c)
--   (hc' : M.ParallelChoiceFunction c') : (M.simplificationWrt c).Iso (M.simplificationWrt c') :=
--   let L := {e | M.Nonloop e}
--   have lem :  ∀ {c₁ c₂ : α → α} (_ : M.ParallelChoiceFunction c₁)
--     (_ : M.ParallelChoiceFunction c₂) ⦃x : α⦄, x ∈ c₁ '' L → c₁ (c₂ x) = x := by
--     rintro c₁ c₂ hc₁ hc₂ _ ⟨e, he, rfl⟩
--     apply hc₁.eq_of_parallel
--     apply ((hc₁.parallel_apply he).trans _).symm
--     apply hc₂.parallel_of_apply_eq
--     · rwa [hc₁.nonloop_apply_iff]
--     rw [hc₂.idem]
--   let π : PartialEquiv α α := {
--     toFun := c'
--     invFun := c
--     source := c '' L
--     target := c' '' L
--     map_source' := ( by
--       rintro _ ⟨e, (he : M.Nonloop e), rfl⟩
--       exact mem_image_of_mem c' (hc.nonloop he) )
--     map_target' := ( by
--       rintro _ ⟨e, he, rfl⟩
--       exact mem_image_of_mem c (hc'.nonloop he) )
--     left_inv' := lem hc hc'
--     right_inv' := lem hc' hc }
--   isoOfMapParallelRestr (c '' L) (c' '' L)
--     ( by
--       simp only [image_subset_iff]
--       exact fun e he ↦ (hc.nonloop he).mem_ground)
--     π rfl rfl
--     ( by
--       rintro _ ⟨e,-,rfl⟩ he'
--       change M.Loop (c' _)
--       rwa [hc'.eq_self he'.not_nonloop] )
--     ( by
--       rintro _ ⟨e,-,rfl⟩ he'
--       exact hc'.parallel_apply he' )

-- /-- If `M ↾ X` is a simple restriction of `M`, then every parallel choice function `c`
--   induces an isomorphism from `M ↾ X` to `M ↾ (c '' X)`. -/
-- theorem ParallelChoiceFunction.iso_of_simple_restr (hc : M.ParallelChoiceFunction c)
--     (hX : (M ↾ X).Simple) : ∃ φ : (M ↾ X).Iso (M ↾ (c '' X)), ∀ e ∈ X, φ e = c e  := by
--   obtain ⟨c', hc', hC'X⟩ := extends_to_parallelChoiceFunction hX
--   have hss : X ⊆ {e | M.Nonloop e} := fun e he ↦ (toNonloop (M := M ↾ X) he).of_restrict
--   have hss' : X ⊆ (M.simplificationWrt c').E := by
--     rw [simplificationWrt, restrict_ground_eq, ← hC'X.image_eq_self]
--     exact image_subset _ hss
--   set φ := (simplificationWrt_iso hc' hc).restrict X hss' with hφ
--   refine ⟨((Iso.ofEq ?_).trans φ).trans (Iso.ofEq ?_), ?_⟩
--   · rwa [simplificationWrt, restrict_restrict_eq]
--   · simp only [simplificationWrt_iso, isoOfMapParallelRestr_toPartialEquiv, simplificationWrt]
--     rw [restrict_restrict_eq]
--     exact image_subset _ hss
--   simp [simplificationWrt_iso, hφ]

-- /-- Any simplification is isomorphic to the classical one. This is defined in tactic mode for now -/
-- noncomputable def simplificationWrt_iso_simplification (hc : M.ParallelChoiceFunction c) :
--     (M.simplificationWrt c).Iso M.simplification := by
--   rw [simplification_eq_wrt]
--   apply simplificationWrt_iso hc
--   simpa using M.removeLoops.exists_parallelChoiceFunction.choose_spec

-- theorem simplificationWrt_isIso_simplification (hc : M.ParallelChoiceFunction c) :
--     M.simplificationWrt c ≂ M.simplification :=
--   (simplificationWrt_iso_simplification hc).isIso

-- theorem simplificationWrt_restriction (hc : M.ParallelChoiceFunction c) :
--     M.simplificationWrt c ≤r M :=
--   restrict_restriction _ _ <| hc.image_setOf_nonloop_subset.trans (fun _ ↦ Nonloop.mem_ground)

-- theorem simplification_restriction (M : Matroid α) : M.simplification ≤r M :=
--   (simplificationWrt_restriction M.removeLoops.exists_parallelChoiceFunction.choose_spec).trans
--     M.removeLoops_restriction

-- theorem simplificationWrt_eq_self_iff (hc : M.ParallelChoiceFunction c) :
--     M.simplificationWrt c = M ↔ M.Simple := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · rw [← h]; exact M.simplificationWrt_simple hc
--   rw [eq_comm]
--   apply (simplificationWrt_restriction hc).minor.eq_of_ground_subset
--   exact fun e he ↦ ⟨e, toNonloop he, Parallel.eq (hc.parallel_apply (toNonloop he)).symm⟩

-- @[simp] theorem simplification_eq_self_iff (M : Matroid α) : M.simplification = M ↔ M.Simple := by
--   rw [simplification_eq_wrt, simplificationWrt_eq_self_iff]
--   simpa using M.exists_parallelChoiceFunction.choose_spec

-- @[simp] theorem simplification_eq_self (M : Matroid α) [Simple M] : M.simplification = M := by
--   rwa [simplification_eq_self_iff]

-- theorem exists_loop_or_parallel_of_simplificationWrt_strictRestriction
--     (hc : M.ParallelChoiceFunction c) (hsN : M.simplificationWrt c < r N) (hNM : N ≤r M) :
--     (∃ e, N.Loop e) ∨ (∃ e, N.Parallel e (c e) ∧ e ≠ c e) := by
--   obtain ⟨R, hR, hsi⟩ := hsN.exists_eq_restrict
--   obtain ⟨e, heN, heR⟩ := exists_of_ssubset hR
--   refine (N.loop_or_nonloop e).elim (fun h ↦ Or.inl ⟨e,h⟩)
--     (fun he ↦ Or.inr ⟨e, ?_, fun hce ↦ heR ?_⟩)
--   · refine (hc.parallel_apply (he.of_restriction hNM)).parallel_restriction hNM heN (hR.subset ?_)
--     rw [← restrict_ground_eq (M := N) (R := R), ← hsi]
--     exact (he.of_restriction hNM).mem_simplificationWrt_ground c
--   rw [← restrict_ground_eq (M := N) (R := R), ← hsi, hce]
--   exact (he.of_restriction hNM).mem_simplificationWrt_ground c

-- theorem eq_simplificationWrt_of_restriction [Simple N] (hc : M.ParallelChoiceFunction c)
--     (hsN : M.simplificationWrt c ≤r N) (hNM : N ≤r M)  :
--     N = M.simplificationWrt c := by
--   obtain (rfl | hM) := hsN.eq_or_strictRestriction
--   · rfl
--   obtain (⟨e,he⟩ | ⟨e,hef⟩) := exists_loop_or_parallel_of_simplificationWrt_strictRestriction
--     hc hM hNM
--   · exact (N.not_loop e he).elim
--   exact (hef.2 hef.1.eq).elim

-- /-- If `N` is below `M` but strictly above `M.simplification` in the restriction order, then
--   `N` has a loop or an element parallel to something in the simplification. -/
-- theorem exists_loop_or_parallel_of_simplification_strictRestriction
--     (hsN : M.simplification <r N) (hNM : N ≤r M) :
--     (∃ e, N.Loop e) ∨
--     (∃ e f, N.Parallel e f ∧ e ∉ M.simplification.E ∧ f ∈ M.simplification.E) := by
--   obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
--   obtain (he | ⟨e,he,hce⟩) :=
--     exists_loop_or_parallel_of_simplificationWrt_strictRestriction hc (hM ▸ hsN) hNM
--   · exact Or.inl he
--   refine Or.inr ⟨e,_, he, ?_⟩
--   rw [hM] at hsN ⊢
--   have hr := (he.nonloop_left.of_restriction hNM).mem_simplificationWrt_ground c
--   refine ⟨fun h' ↦ ?_, hr⟩
--   have _ := M.simplificationWrt_simple hc
--   exact hce (he.parallel_restriction hsN.restriction h' hr).eq

-- theorem exists_parallel_of_simplification_strictRestriction [Loopless N]
--     (hsN : M.simplification <r N) (hNM : N ≤r M) :
--     (∃ e f, N.Parallel e f ∧ e ∉ M.simplification.E ∧ f ∈ M.simplification.E) := by
--    obtain (⟨e,he⟩ | h) := exists_loop_or_parallel_of_simplification_strictRestriction hsN hNM
--    · exact (N.not_loop e he).elim
--    assumption

-- theorem eq_simplification_of_restriction [Simple N] (hsN : M.simplification ≤r N) (hNM : N ≤r M) :
--     N = M.simplification := by
--   obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
--   rw [hM]
--   exact eq_simplificationWrt_of_restriction hc (by rwa [← hM]) hNM

-- set_option pp.proofs.withType true

-- /-- Elements of a simplification are equivalent to parallel classes of `M`. -/
-- @[simps] noncomputable def simplificationWrt_equiv (hc : M.ParallelChoiceFunction c) :
--     (M.simplificationWrt c).E ≃ {P // P ∈ M.parallelClasses} where
--   toFun e :=
--     let h : M.Nonloop e := by
--       have _ := M.simplificationWrt_simple hc
--       exact (Matroid.toNonloop e.prop).of_restriction (simplificationWrt_restriction hc)
--     ⟨M.parallelClasses.partOf e, M.parallelClasses.partOf_mem h⟩
--   invFun P := ⟨c <| M.parallelClasses.rep P.prop, by
--     simp only [simplificationWrt_ground_eq, mem_image, mem_setOf_eq]
--     exact ⟨_, M.parallelClasses.rep_mem' _, rfl⟩⟩
--   left_inv e := by
--     obtain ⟨_, ⟨e, (he : M.Nonloop e), rfl⟩⟩ := e
--     simp only [simplificationWrt_ground_eq, Subtype.mk.injEq]
--     refine hc.eq_of_parallel ((hc.parallel_apply he).trans ?_).symm
--     simpa using M.parallelClasses.rep_mem <|
--       M.parallelClasses.partOf_mem (hc.parallel_apply he).nonloop_right
--   right_inv P := by
--     obtain ⟨P, hP⟩ := P
--     simp only [parallelClasses_partOf_eq, Subtype.mk.injEq]
--     convert M.parallelClasses.setOf_rel_rep_eq hP using 1
--     ext f
--     exact (hc.parallel_apply (M.parallelClasses.rep_mem' hP)).symm.parallel_iff_right

-- /-- Elements of the (classical) simplification are equivalent to parallel classes. -/
-- noncomputable def simplification_equiv (M : Matroid α) :
--     M.simplification.E ≃ {P // P ∈ M.parallelClasses} :=
--   let h := M.exists_simplification_eq_wrt
--   (Equiv.Set.ofEq (congr_arg Matroid.E h.choose_spec.2)).trans
--     (simplificationWrt_equiv h.choose_spec.1)




-- -- TODO - API for the above equivalences. (Don't know exactly what this entails. )


-- end Simplification

-- section Minor

-- /-- Any simple restriction of `M` is a restriction of a simplification of `M`-/
-- theorem Restriction.exists_restriction_simplificationWrt (h : N ≤r M) [Simple N] :
--     ∃ c, M.ParallelChoiceFunction c ∧ N ≤r M.simplificationWrt c := by
--   obtain ⟨c, hc, hcN⟩ :=
--     extends_to_parallelChoiceFunction (show (M ↾ N.E).Simple by rwa [h.eq_restrict])
--   refine ⟨c, hc, ?_⟩
--   rw [← h.eq_restrict, simplificationWrt]
--   exact Restriction.of_subset _ (fun e heN ↦ ⟨e, (toNonloop heN).of_restriction h, hcN heN⟩)

-- /-- Any simple minor of `M` is a minor of a simplification of `M`-/
-- theorem Minor.exists_minor_simplificationWrt {N M : Matroid α} [Simple N] (hN : N ≤m M) :
--     ∃ c, M.ParallelChoiceFunction c ∧ N ≤m M.simplificationWrt c := by
--   obtain ⟨I, hI, hr, -⟩ := hN.exists_contract_spanning_restrict
--   have hN' := hr.eq_restrict ▸
--     M.contract_restrict_eq_restrict_contract _ _ (subset_diff.1 hr.subset).2.symm
--   have h : (M ↾ (N.E ∪ I)).Simple := by
--     apply Indep.simple_of_contract_simple (I := I) _ (by rwa [← hN'])
--     refine restrict_indep_iff.2 ⟨hI, subset_union_right _ _⟩
--   have hres := restrict_restriction M _ (union_subset hN.subset hI.subset_ground)
--   obtain ⟨c, hc, hrc⟩ := hres.exists_restriction_simplificationWrt
--   refine ⟨c, hc, ?_⟩
--   rw [← hr.eq_restrict]
--   apply Minor.trans ?_ hrc.minor
--   rw [contract_restrict_eq_restrict_contract _ _ _ (subset_diff.1 hr.subset).2.symm]
--   apply contract_minor

-- theorem minor_iff_minor_simplification {α β : Type*} {N : Matroid α} [Simple N] {M : Matroid β} :
--     N ≤i M ↔ N ≤i M.simplification := by
--   refine ⟨fun h ↦ ?_, fun h ↦ h.trans M.simplification_restriction.minor.isoMinor⟩
--   obtain ⟨N', hN'M, hi⟩ := h
--   have _ := ‹Simple N›.map_iso hi
--   obtain ⟨c, hc, hminor⟩ := hN'M.exists_minor_simplificationWrt
--   exact hi.isoMinor.trans <| hminor.isoMinor.trans
--     (M.simplificationWrt_isIso_simplification hc).isoMinor


-- end Minor
