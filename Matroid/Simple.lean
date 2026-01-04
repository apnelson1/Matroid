import Matroid.Parallel
import Matroid.Minor.Iso
import Matroid.ForMathlib.Card
import Matroid.Closure

open Set Set.Notation

variable {α : Type*} {M N : Matroid α} {e f g : α} {I X P D : Set α}

namespace Matroid

/-- A matroid is `Simple` if it has no loops or nontrivial parallel pairs. -/
class Simple (M : Matroid α) : Prop where
  (parallel_iff_eq : ∀ {e f}, e ∈ M.E → (M.Parallel e f ↔ e = f))

lemma Parallel.eq [Simple M] (h : M.Parallel e f) : e = f := by
  rwa [Simple.parallel_iff_eq h.mem_ground_left] at h

lemma parallel_iff_eq [Simple M] (he : e ∈ M.E := by aesop_mat) : M.Parallel e f ↔ e = f :=
  Simple.parallel_iff_eq he

lemma not_parallel_of_ne (M : Matroid α) [Simple M] (hef : e ≠ f) : ¬ M.Parallel e f :=
  fun h ↦ hef h.eq

instance [Simple M] : Loopless M := by
  rw [loopless_iff_forall_isNonloop]
  exact fun e he ↦ ((parallel_iff_eq he).2 rfl).isNonloop_left

instance {α : Type*} : Simple (emptyOn α) :=
  ⟨fun he ↦ by simp at he⟩

lemma Simple.loopless (hM : M.Simple) : M.Loopless := by
  infer_instance

theorem Simple.isNonloop_of_mem (_ : M.Simple) (he : e ∈ M.E) : M.IsNonloop e :=
  isNonloop_of_loopless he

lemma simple_iff_isLoopless_eq_of_parallel_forall:
    Simple M ↔ (M.Loopless ∧ ∀ e f, M.Parallel e f → e = f) :=
  ⟨fun h ↦ ⟨by infer_instance, fun _ _ ↦ Parallel.eq⟩,
    fun ⟨_,h⟩ ↦ ⟨fun heE ↦ ⟨h _ _,by rintro rfl; exact (isNonloop_of_loopless heE).parallel_self⟩⟩⟩

lemma parallel_class_eq [Simple M] (he : e ∈ M.E := by aesop_mat) :
    {f | M.Parallel e f} = {e} := by
  simp_rw [parallel_iff_eq he, setOf_eq_eq_singleton']

@[simp] lemma closure_singleton_eq [Simple M] (he : e ∈ M.E := by aesop_mat) :
    M.closure {e} = {e} := by
  rw [closure_eq_parallel_class_union_loops, parallel_class_eq he, loops_eq_empty, union_empty]

/-- We need `RankPos` or something similar here, since otherwise the matroid whose only element is
  a loop is a counterexample. -/
lemma simple_iff_closure_subset_self_forall [RankPos M] :
    M.Simple ↔ ∀ e, M.IsNonloop e → M.closure {e} ⊆ {e} := by
  refine ⟨fun h e he ↦ by rw [closure_singleton_eq], fun h ↦ ?_⟩
  have hl : M.Loopless := by
    rw [loopless_iff_forall_not_isLoop]
    intro e _ hel
    obtain ⟨f, hf⟩ := M.exists_isNonloop
    obtain (rfl : e = f) := (h f hf).subset (hel.mem_closure _)
    exact hf.not_isLoop hel
  rw [simple_iff_isLoopless_eq_of_parallel_forall, and_iff_right hl]
  exact fun e f hp ↦ (h _ hp.isNonloop_right) hp.mem_closure

lemma closure_eq_self_of_subset_singleton [Simple M] (he : e ∈ M.E) (hX : X ⊆ {e}) :
    M.closure X = X := by
  obtain (rfl | rfl) := subset_singleton_iff_eq.1 hX
  · exact M.loops_eq_empty
  exact closure_singleton_eq he

lemma singleton_isFlat [Simple M] (he : e ∈ M.E := by aesop_mat) : M.IsFlat {e} := by
  rw [← closure_singleton_eq]; apply closure_isFlat

lemma pair_indep [Simple M] (he : e ∈ M.E := by aesop_mat) (hf : f ∈ M.E := by aesop_mat) :
    M.Indep {e,f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · rw [pair_eq_singleton, indep_singleton]; exact isNonloop_of_loopless he
  rwa [← not_dep_iff, ← (isNonloop_of_loopless he).parallel_iff_dep (isNonloop_of_loopless hf) hne,
    parallel_iff_eq he]

lemma pair_closure_isLine [Simple M] (hne : e ≠ f) (he : e ∈ M.E := by aesop_mat)
    (hf : f ∈ M.E := by aesop_mat) : M.IsLine (M.closure {e,f}) := by
  rwa [IsLine, and_iff_right (M.closure_isFlat _), eRk_closure_eq, (pair_indep he hf).eRk_eq_encard,
    encard_pair]

lemma indep_of_encard_le_two [Simple M] (h : I.encard ≤ 2) (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  have hne : I.encard ≠ ⊤ := (h.trans_lt (by exact (cmp_eq_lt_iff 2 ⊤).mp rfl : (2 : ℕ∞) < ⊤ )).ne
  rw [le_iff_lt_or_eq, encard_eq_two, ← ENat.add_one_le_iff hne, (by norm_num : (2 : ℕ∞) = 1 + 1),
    WithTop.add_le_add_iff_right, encard_le_one_iff_eq] at h
  · obtain (rfl | ⟨x, rfl⟩) | ⟨x, y, -, rfl⟩ := h
    · exact M.empty_indep
    · refine indep_singleton.2 (isNonloop_of_loopless (by aesop_mat))
    exact pair_indep
  norm_num

lemma eRk_pair_eq [Simple M] (hef : e ≠ f) (he : e ∈ M.E := by aesop_mat)
    (hf : f ∈ M.E := by aesop_mat) : M.eRk {e,f} = 2 := by
  rw [(pair_indep he).eRk_eq_encard, encard_pair hef]

lemma Dep.two_lt_encard [Simple M] (hD : M.Dep D) : 2 < D.encard :=
  lt_of_not_ge fun hle ↦ hD.not_indep (indep_of_encard_le_two hle)

lemma three_le_girth_iff : 3 ≤ M.girth ↔ M.Simple := by
  rw [iff_comm, le_girth_iff]
  refine ⟨fun h C hC ↦ le_of_not_gt fun hlt ↦ ?_, fun h ↦ ?_⟩
  · exact hC.dep.not_indep <| indep_of_encard_le_two (Order.le_of_lt_add_one hlt)
  simp_rw [simple_iff_isLoopless_eq_of_parallel_forall, loopless_iff_forall_isCircuit,
    ← one_lt_encard_iff_nontrivial]
  refine ⟨fun C hC ↦ (show (1 : ℕ∞) < 3 by norm_num).trans_le (h C hC),
    fun e f hef ↦ by_contra fun hne ↦ ?_⟩
  have hcon := (h _ (hef.isCircuit_of_ne hne)).trans_eq (encard_pair hne)
  norm_num at hcon

lemma simple_iff_forall_isCircuit : M.Simple ↔ ∀ C, M.IsCircuit C → 2 < C.encard := by
  simp_rw [← ENat.add_one_le_iff (show 2 ≠ ⊤ by norm_num), show (2 : ℕ∞) + 1 = 3 from rfl,
    ← three_le_girth_iff, le_girth_iff]

lemma simple_iff_forall_pair_indep : M.Simple ↔ ∀ ⦃e f⦄, e ∈ M.E → f ∈ M.E → M.Indep {e,f} := by
  refine ⟨fun h _ _ he hf ↦ pair_indep he hf, fun h ↦ ?_⟩
  rw [simple_iff_isLoopless_eq_of_parallel_forall, loopless_iff_forall_not_isLoop]
  exact ⟨fun e he hl ↦ hl.dep.not_indep <| by simpa using h he he,
    fun e f hef ↦ hef.eq_of_indep (h hef.mem_ground_left hef.mem_ground_right) ⟩

@[simp] lemma simple_uniqueBaseOn_iff {E : Set α} : Simple (uniqueBaseOn I E) ↔ E ⊆ I := by
  simp only [simple_iff_forall_pair_indep, uniqueBaseOn_ground, uniqueBaseOn_indep_iff',
    subset_inter_iff, pair_subset_iff]
  exact ⟨fun h e heE ↦ (h heE heE).1.1, by tauto⟩

instance simple_freeOn {E : Set α} : Simple (freeOn E) := by
  simp [← uniqueBaseOn_self]

instance simple_emptyOn {α : Type*} : Simple (emptyOn α) := by
  simp [simple_iff_forall_pair_indep]

lemma Simple.map {β : Type*} (hM : M.Simple) {f : α → β} (hf : M.E.InjOn f) :
    Simple (M.map f hf) := by
  simp only [simple_iff_forall_pair_indep, map_ground, mem_image, map_indep_iff,
    forall_exists_index, and_imp]
  rintro _ _ x hx rfl y hy rfl
  exact ⟨_, pair_indep hx hy, by simp [image_insert_eq]⟩

lemma Simple.of_iso {β : Type*} {N : Matroid β} (hM : M.Simple) (i : M ≂ N) : N.Simple := by
  obtain (h | h) := isEmpty_or_nonempty β
  · rw [eq_emptyOn N]; infer_instance
  obtain ⟨f, hf, rfl⟩ := i.exists_eq_map
  exact hM.map hf

lemma simple_iff_forall_parallel_class [Loopless M] :
    M.Simple ↔ ∀ P ∈ M.parallelClasses, encard P = 1 := by
  simp only [mem_parallelClasses_iff, forall_exists_index, and_imp, encard_eq_one]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro h P x hx rfl
    exact ⟨x, by simp [parallel_iff_eq hx.mem_ground]⟩
  rw [simple_iff_isLoopless_eq_of_parallel_forall, and_iff_right (by assumption)]
  refine fun e f hef ↦ ?_
  obtain ⟨x, hx⟩ := h _ e hef.isNonloop_left rfl
  rw [(show f = x from hx.subset hef), show e = x from hx.subset (hef.isNonloop_left.parallel_self)]

lemma simple_iff_parallelClasses_eq_discrete' :
    M.Simple ↔ M.Loopless ∧ M.parallelClasses = Partition.discrete {e | M.IsNonloop e} := by
  refine ⟨fun h ↦ ⟨by infer_instance, Partition.eq_of_rel_iff_rel ?_⟩, fun ⟨_,h⟩ ↦ ?_⟩
  · simp only [Partition.rel_discrete_iff, mem_setOf_eq,
      show M.parallelClasses = M.Parallel from rfl]
    refine fun x y ↦ ⟨fun hpara ↦ ⟨hpara.eq, hpara.isNonloop_left⟩, ?_⟩
    rintro ⟨rfl, nl⟩
    exact nl.parallel_self
  rw [simple_iff_isLoopless_eq_of_parallel_forall, and_iff_right (by assumption)]
  simp [Parallel, h]

lemma simple_iff_parallelClasses_eq_discrete [Loopless M] :
    M.Simple ↔  M.parallelClasses = Partition.discrete {e | M.IsNonloop e} := by
  rw [simple_iff_parallelClasses_eq_discrete', and_iff_right (by assumption)]

lemma parallelClasses_eq_discrete [Simple M] :
    M.parallelClasses = Partition.discrete {e | M.IsNonloop e} :=
  simple_iff_parallelClasses_eq_discrete.1 (by assumption)

lemma Simple.eq_of_parallel_of_mem (h : (M ↾ X).Simple) (he : e ∈ X) (hf : f ∈ X)
    (hef : M.Parallel e f) : e = f :=
  (parallel_iff_eq (M := M ↾ X) (e := (⟨e,he⟩ : X)) (f := (⟨f,hf⟩ : X)) (by simpa)).1
    (by simp [restrict_parallel_iff, hef, he, hf])

lemma exists_isLoop_or_para_of_not_simple (hM : ¬ M.Simple) :
    (∃ e, M.IsLoop e) ∨ ∃ e f, M.Parallel e f ∧ e ≠ f := by
  by_contra! h
  rw [simple_iff_isLoopless_eq_of_parallel_forall, loopless_iff_forall_not_isLoop] at hM
  push_neg at hM
  obtain ⟨e, f, hef, hne⟩ := hM (fun e _ ↦ h.1 e)
  exact hne <| h.2 e f hef

lemma Indep.restr_simple (hI : M.Indep I) : (M ↾ I).Simple := by
  simp only [simple_iff_forall_pair_indep, restrict_ground_eq, restrict_indep_iff, pair_subset_iff]
  rintro e f he hf
  exact ⟨hI.subset (pair_subset he hf), he, hf⟩

lemma Simple.subset_isNonloops (_ : (M ↾ X).Simple) : X ⊆ {e | M.IsNonloop e} :=
  fun _ hx ↦ (isNonloop_of_loopless (M := M ↾ X) hx).of_restrict

theorem Simple.repFun_injOn (h : (M ↾ X).Simple) (f : M.parallelClasses.RepFun) : X.InjOn f :=
  fun _ hx _ hy hxy ↦ h.eq_of_parallel_of_mem hx hy
    (f.rel_of_apply_eq_apply (parallelClasses_supp M ▸ h.subset_isNonloops hx) hxy)

lemma Simple.subset_ground {X : Set α} (h : (M ↾ X).Simple) : X ⊆ M.E :=
  h.subset_isNonloops.trans (fun _ ↦ IsNonloop.mem_ground)

lemma Simple.subset {X Y : Set α} (hY : (M ↾ Y).Simple) (hXY : X ⊆ Y) : (M ↾ X).Simple := by
  simp only [simple_iff_forall_pair_indep, restrict_ground_eq, restrict_indep_iff,
    pair_subset_iff] at *
  aesop

lemma Loopless.of_restrict_contract {C : Set α} (hC : (M ↾ C).Loopless) (h : (M ／ C).Loopless) :
    M.Loopless := by
  rw [loopless_iff] at *
  rw [contract_loops_eq, diff_eq_empty] at h
  rw [restrict_loops_eq', union_empty_iff] at hC
  rw [← inter_union_diff (s := M.loops) (t := C), hC.1, empty_union, diff_eq_empty]
  exact (M.closure_subset_closure <| empty_subset C).trans h

lemma Simple.of_restrict_contract {C : Set α} (hC : (M ↾ C).Simple) (h : (M ／ C).Simple) :
    M.Simple := by
  rw [simple_iff_isLoopless_eq_of_parallel_forall] at h hC ⊢
  obtain ⟨hl, h⟩ := h
  obtain ⟨hclosure, hC⟩ := hC
  simp only [restrict_parallel_iff, and_imp] at hC
  refine ⟨(hclosure.of_restrict_contract hl), fun e f hef ↦ ?_⟩
  by_cases heC : e ∈ C
  · by_cases hfC : f ∈ C
    · exact hC _ _ hef heC hfC
    refine by_contra fun hne ↦ not_isLoop (M ／ C) f ?_
    exact (hef.isLoop_contractElem hne).of_isMinor
      ⟨hef.mem_ground_right, hfC⟩ (contract_isMinor_of_mem _ heC)
  by_cases hfC : f ∈ C
  · refine by_contra fun (hne : e ≠ f) ↦ not_isLoop (M ／ C) e ?_
    exact (hef.symm.isLoop_contractElem hne.symm).of_isMinor ⟨hef.mem_ground_left, heC⟩
      (contract_isMinor_of_mem _ hfC)
  apply h
  rw [parallel_iff, contract_closure_eq, contract_closure_eq, closure_union_congr_left
    hef.closure_eq_closure, and_iff_left rfl]
  exact ⟨isNonloop_of_loopless ⟨hef.mem_ground_left, heC⟩,
    isNonloop_of_loopless ⟨hef.mem_ground_right, hfC⟩⟩

lemma Indep.simple_of_contract_simple (hI : M.Indep I) (h : (M ／ I).Simple) : M.Simple :=
  hI.restr_simple.of_restrict_contract h

-- @[simp] lemma simple_uniqueBaseOn_iff {I E : Set α} : (uniqueBaseOn I E).Simple ↔ E ⊆ I := by
--   simp only [simple_iff_forall_pair_indep, uniqueBaseOn_ground, mem_singleton_iff,
--     uniqueBaseOn_indep_iff', subset_inter_iff]
--   refine ⟨fun h x hxE ↦ by simpa using (h hxE hxE).1, fun h {e f} he hf ↦
-- ⟨subset_trans ?_ h, ?_⟩⟩
--   <;> rintro x (rfl | rfl) <;> assumption

-- instance simple_freeOn {E : Set α} : (freeOn E).Simple := by
--   rw [← uniqueBaseOn_eq_freeOn, simple_uniqueBaseOn_iff]

@[simp] lemma simple_loopyOn_iff {E : Set α} : (loopyOn E).Simple ↔ E = ∅ := by
  simp [← uniqueBaseOn_empty]




section LE

/-- `N` simplifies `M` if `N` is a restriction of `M`, and every nonloop of `M` is parallel
to an element of `M`. Equivalently, `N` is a restriction of `M` that has some simplification
of `M` as a restriction. -/
@[mk_iff]
structure Simplifies (N M : Matroid α) : Prop where
  isRestriction : N ≤r M
  exists_of_isNonloop : ∀ ⦃e⦄, M.IsNonloop e → ∃ f ∈ N.E, M.Parallel e f

scoped infix:50  " ≤si " => Simplifies

lemma Simplifies.refl : M ≤si M :=
  ⟨IsRestriction.refl, fun e he ↦ ⟨e, he.mem_ground, he.parallel_self⟩⟩

lemma Simplifies.trans {R : Matroid α} (hNM : N ≤si M) (hMR : M ≤si R) : N ≤si R := by
  refine ⟨hNM.isRestriction.trans hMR.isRestriction, fun e he ↦ ?_⟩
  obtain ⟨e', he'E, hee'⟩ := hMR.exists_of_isNonloop he
  obtain ⟨f, hfN, hef⟩ := hNM.exists_of_isNonloop
    (hee'.isNonloop_right.isNonloop_of_isRestriction_of_mem hMR.isRestriction he'E)
  exact ⟨f, hfN, hee'.trans (hef.of_isRestriction hMR.isRestriction)⟩

lemma Simplifies.antisymm (hNM : N ≤si M) (hMN : M ≤si N) : N = M :=
  hNM.isRestriction.antisymm hMN.isRestriction

lemma Simplifies.exists_mem_closure [N.Nonempty] (hM : N ≤si M) (he : e ∈ M.E) :
    ∃ f ∈ N.E, e ∈ M.closure {f} := by
  obtain he | he := M.isLoop_or_isNonloop e
  · obtain ⟨f, hf⟩ := N.ground_nonempty
    exact ⟨f, hf, he.mem_closure {f}⟩
  obtain ⟨f, hf, hef⟩ := hM.exists_of_isNonloop he
  exact ⟨f, hf, hef.mem_closure⟩

lemma Simplifies.exists_mem_closure_subsingleton (hM : N ≤si M) (he : e ∈ M.E) :
    ∃ X ⊆ N.E, X.Subsingleton ∧ e ∈ M.closure X := by
  obtain he | he := M.isLoop_or_isNonloop e
  · exact ⟨∅, by simp, by simp, he⟩
  obtain ⟨f, hfE, hef⟩ := hM.exists_of_isNonloop he
  exact ⟨{f}, by simpa, by simp, hef.mem_closure⟩

lemma Simplifies.isSpanningRestriction (h : N ≤si M) : N ≤sr M := by
  rw [isSpanningRestriction_iff, spanning_iff_ground_subset_closure h.isRestriction.subset,
    and_iff_right h.isRestriction]
  intro e heE
  obtain he | he := M.isLoop_or_isNonloop e
  · exact he.mem_closure _
  obtain ⟨f, hfN, hef⟩ := h.exists_of_isNonloop he
  exact mem_of_mem_of_subset hef.mem_closure <| M.closure_mono <| by simpa

lemma Simplifies.simplifies_of_isRestriction {R : Matroid α} (h : N ≤si M) (hNR : N ≤r R)
    (hRM : R ≤r M) : N ≤si R := by
  refine ⟨hNR, fun e he ↦ ?_⟩
  obtain ⟨f, hfE, hef⟩ := h.exists_of_isNonloop (he.of_isRestriction hRM)
  exact ⟨f, hfE, hef.parallel_isRestriction hRM he.mem_ground (hNR.subset hfE)⟩

lemma Simplifies.simplifies_of_isRestriction_right {R : Matroid α} (h : N ≤si M) (hNR : N ≤r R)
    (hRM : R ≤r M) : R ≤si M := by
  refine ⟨hRM, fun e he ↦ ?_⟩
  obtain ⟨f, hfE, hef⟩ := h.exists_of_isNonloop he
  exact ⟨f, hNR.subset hfE, hef⟩

lemma delete_simplifies_of_subset_loops (h : X ⊆ M.loops) : M ＼ X ≤si M :=
  ⟨delete_isRestriction .., fun e he ↦ ⟨e, ⟨he.mem_ground, notMem_subset h he.not_isLoop⟩,
    he.parallel_self⟩⟩

lemma removeLoops_simplifies (M : Matroid α) : M.removeLoops ≤si M :=
  removeLoops_eq_delete _ ▸ delete_simplifies_of_subset_loops rfl.subset

lemma IsLoop.delete_simplifies (h : M.IsLoop e) : M ＼ {e} ≤si M :=
  delete_simplifies_of_subset_loops (by simpa using h)

lemma Parallel.delete_left_simplifies (h : M.Parallel e f) (hne : e ≠ f) : (M ＼ {e}) ≤si M := by
  refine ⟨delete_isRestriction .., fun x hx ↦ ?_⟩
  obtain rfl | hne := eq_or_ne e x
  · exact ⟨f, ⟨h.mem_ground_right, by simpa using hne.symm⟩, h⟩
  exact ⟨x, ⟨hx.mem_ground, by simpa using hne.symm⟩, hx.parallel_self⟩

lemma Parallel.delete_right_simplifies (h : M.Parallel e f) (hne : e ≠ f) : (M ＼ {f}) ≤si M :=
  h.symm.delete_left_simplifies hne.symm

lemma Simple.eq_of_simplifies (h : M.Simple) (hNM : N ≤si M) : N = M := by
  refine (hNM.isRestriction.isMinor.eq_of_ground_subset fun e he ↦ ?_).symm
  obtain ⟨f, hfN, hef⟩ := hNM.exists_of_isNonloop <| h.isNonloop_of_mem he
  rwa [hef.eq]

@[simp]
lemma simplifies_iff_eq [M.Simple] : N ≤si M ↔ N = M :=
  ⟨fun h ↦ Simple.eq_of_simplifies (by assumption) h, fun h ↦ h ▸ Simplifies.refl⟩

lemma Simple.simplifies_iff_eq (h : M.Simple) : N ≤si M ↔ N = M :=
  _root_.Matroid.simplifies_iff_eq

lemma Simplifies.contract {C : Set α} (h : N ≤si M) (hC : C ⊆ N.E) : N ／ C ≤si M ／ C := by
  refine ⟨h.isRestriction.contract hC, fun e he ↦ ?_⟩
  obtain ⟨f, hfE, hef⟩ := h.exists_of_isNonloop he.of_contract
  simp only [contract_isNonloop_iff, mem_diff] at he
  refine ⟨f, ⟨hfE, fun hfC ↦ he.2 ?_⟩, ?_⟩
  · exact mem_of_mem_of_subset hef.mem_closure <| M.closure_mono <| by simpa
  rw [parallel_comm, contract_parallel_iff, and_iff_left he.2]
  exact mem_of_mem_of_subset hef.mem_closure <| M.closure_mono <| by simp

end LE
-- end Simple

section IsSimplification

variable {x y : α}

/-- `N.IsSimplification M` means that `N` is obtained from `M` by deleting all loops and all but
one element from each parallel class. -/
def IsSimplification (N M : Matroid α) : Prop :=
  ∃ (f : M.parallelClasses.RepFun), N = M ↾ f '' {e | M.IsNonloop e}

/-- Each simplification of `M` corresponds to a function that picks a representative from each
parallel class. Even though the choice is unique, this is noncomputable. -/
noncomputable def IsSimplification.repFun (h : N.IsSimplification M) : M.parallelClasses.RepFun :=
  h.choose

@[simp] lemma IsSimplification.image_restrict_repFun (h : N.IsSimplification M) :
    M ↾ (h.repFun '' {e | M.IsNonloop e}) = N := h.choose_spec.symm

lemma IsSimplification.ground_eq_image_repFun (h : N.IsSimplification M) :
    N.E = h.repFun '' {e | M.IsNonloop e} :=
  Eq.symm <| congr_arg Matroid.E h.image_restrict_repFun

lemma IsSimplification.parallel_repFun (h : N.IsSimplification M) (he : M.IsNonloop e) :
    M.Parallel e (h.repFun e) :=
  h.repFun.rel_apply <| parallelClasses_supp M ▸ he

lemma IsSimplification.repFun_apply_mem_ground (h : N.IsSimplification M) (he : M.IsNonloop e) :
    h.repFun e ∈ N.E := by
  rw [← congr_arg Matroid.E h.image_restrict_repFun, restrict_ground_eq]
  exact mem_image_of_mem h.repFun he

lemma IsSimplification.simple (h : N.IsSimplification M) : N.Simple := by
  obtain ⟨f, rfl⟩ := h
  rw [simple_iff_isLoopless_eq_of_parallel_forall]
  simp only [restrict_parallel_iff, mem_image, mem_setOf_eq, and_imp, forall_exists_index,
    loopless_iff_forall_isNonloop, restrict_ground_eq, mem_image, mem_setOf_eq,
    restrict_isNonloop_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine ⟨fun x hx ↦ ⟨f.apply_mem' mem_parallelClasses_supp_iff hx, ⟨x, hx, rfl⟩⟩, ?_⟩
  rintro _ _ hxy x - rfl y - rfl
  simpa using f.apply_eq_apply hxy

lemma Simple.exists_subset_isSimplification (hX : (M ↾ X).Simple) :
    ∃ (N : Matroid α), N.IsSimplification M ∧ X ⊆ N.E := by
  obtain ⟨f, hf⟩ := M.parallelClasses.exists_extend_partial_repFun'
    (fun _ _ ↦ hX.eq_of_parallel_of_mem)
  refine ⟨_, ⟨f,rfl⟩, ?_⟩
  rw [← image_id X, ← hf.image_eq]
  exact image_mono hX.subset_isNonloops

lemma IsSimplification.isRestriction (h : N.IsSimplification M) : N ≤r M := by
  obtain ⟨f, rfl⟩ := h
  refine restrict_isRestriction _ _ ?_
  rintro _ ⟨x,hx,rfl⟩
  exact IsNonloop.mem_ground <| f.apply_mem' mem_parallelClasses_supp_iff hx

lemma Simple.exists_isRestriction_isSimplification_of_isRestriction (hN : Simple N) (h : N ≤r M) :
    ∃ (M' : Matroid α), M'.IsSimplification M ∧ N ≤r M' := by
  obtain ⟨R, -, rfl⟩ := h.exists_eq_restrict
  obtain ⟨M', hM', hRM'⟩ := hN.exists_subset_isSimplification
  refine ⟨M', hM', ?_⟩
  obtain ⟨R', -, rfl⟩ := hM'.isRestriction.exists_eq_restrict
  exact ⟨R, hRM', by rw [restrict_restrict_eq _ (show R ⊆ R' from hRM')]⟩

lemma IsSimplification.repFun_injOn (h : N.IsSimplification M) : N.E.InjOn h.repFun := by
  apply Simple.repFun_injOn
  rw [h.isRestriction.eq_restrict]
  exact h.simple

lemma IsSimplification.eq_self_iff (h : N.IsSimplification M) : N = M ↔ M.Simple := by
  refine ⟨fun h' ↦ h' ▸ h.simple, fun h' ↦ ?_⟩
  obtain ⟨f, rfl⟩ := h
  rw [restrict_eq_self_iff, f.coeFun_eq_id_of_eq_discrete M.parallelClasses_eq_discrete, image_id,
    Loopless.ground_eq]

lemma IsSimplification.isNonloop_of_mem (h : N.IsSimplification M) (heN : e ∈ N.E) :
    M.IsNonloop e :=
  (h.simple.isNonloop_of_mem heN).of_isRestriction h.isRestriction

lemma IsSimplification.exists_unique (h : N.IsSimplification M) (he : M.IsNonloop e) :
    ∃! f ∈ N.E, M.Parallel e f := by
  obtain ⟨f, rfl⟩ := h
  refine ⟨f e, ⟨⟨e, he, rfl⟩, f.rel_apply' mem_parallelClasses_supp_iff he⟩, ?_⟩
  · rintro _ ⟨⟨y, -, rfl⟩, hey⟩
    simp [f.apply_eq_apply hey]

lemma IsSimplification.simplifies (h : N.IsSimplification M) : N ≤si M :=
  ⟨h.isRestriction, fun _ he ↦ (h.exists_unique he).exists⟩

lemma IsSimplification.eq_of_parallel (h : N.IsSimplification M) (he : e ∈ N.E) (hf : f ∈ N.E)
    (hef : M.Parallel e f) : e = f := by
  have := h.simple
  apply Parallel.eq (M := N)
  obtain ⟨R, hR, rfl⟩ := h.isRestriction
  rwa [restrict_parallel_iff, and_iff_left (show f ∈ R from hf), and_iff_left (show e ∈ R from he)]

lemma IsSimplification.eq_of_simplifies_ge {N₀ : Matroid α} (h : N.IsSimplification M)
    (hN₀ : N₀ ≤si M) (hN₀N : N₀ ≤r N) : N₀ = N := by
  refine Eq.symm <| hN₀N.isMinor.eq_of_ground_subset fun e heN ↦ ?_
  obtain ⟨f, hfN₀, hef⟩ :=
    hN₀.exists_of_isNonloop <| (h.simple.isNonloop_of_mem heN).of_isRestriction h.isRestriction
  rwa [h.eq_of_parallel heN (hN₀N.subset hfN₀) hef]

/-- A simplification of `M` is the restriction of `M` to a transversal of its parallel classes. -/
lemma isSimplification_iff : N.IsSimplification M ↔ N.Loopless ∧ N ≤r M ∧
    ∀ ⦃e⦄, M.IsNonloop e → ∃! f ∈ N.E, M.Parallel e f := by
  classical
  refine ⟨fun h ↦ ⟨h.simple.loopless, h.isRestriction, fun e he ↦ h.exists_unique he⟩,
    fun ⟨h, hr, h'⟩ ↦ ?_⟩
  choose f hf using h'
  refine ⟨Partition.RepFun.mk (fun x ↦ if hx : M.IsNonloop x then f hx else x)
    (fun a ha ↦ ?_) (fun a ha ↦ ?_) fun a b (hab : M.Parallel a b) ↦ ?_, ?_⟩
  · simp_rw [dif_neg (show ¬ M.IsNonloop a from mem_parallelClasses_supp_iff.not.mp ha)]
  · rw [mem_parallelClasses_supp_iff] at ha
    simp [dif_pos ha, (hf ha).1.2]
  · simp only [hab.isNonloop_left, ↓reduceDIte, hab.isNonloop_right]
    exact Eq.symm <| (hf hab.isNonloop_left).2 (f hab.isNonloop_right)
      ⟨(hf hab.isNonloop_right).1.1, hab.trans (hf hab.isNonloop_right).1.2⟩
  convert hr.eq_restrict.symm
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x,(hx : M.IsNonloop x),rfl⟩; simp [hx, (hf hx).1.1]
  have hx := ((isNonloop_of_loopless h).of_isRestriction hr)
  simp only [Partition.RepFun.mk_apply, mem_image, mem_setOf_eq]
  exact ⟨x, hx, by rw [dif_pos hx, ← (hf hx).2 _ ⟨h, hx.parallel_self⟩]⟩

/-- `N` is a simplification of `M` if `N` is minimal in the restriction order simplifying `M`. -/
lemma isSimplification_iff_minimal_simplifies :
    N.IsSimplification M ↔ N ≤si M ∧ ∀ ⦃N₀⦄, N₀ ≤r N → N₀ ≤si M → N₀ = N := by
  refine ⟨fun h ↦ ⟨h.simplifies, fun N₀ hr hN₀N ↦ h.eq_of_simplifies_ge hN₀N hr⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  rw [isSimplification_iff, loopless_iff_forall_not_isLoop]
  have aux {f : α} (hf : f ∈ N.E) : N ＼ {f} <r N :=
    (delete_isRestriction ..).isStrictRestriction_of_ground_ne (by simpa)
  refine ⟨fun e heN he ↦ ?_, h1.isRestriction, fun e he ↦ ?_⟩
  · exact (aux heN).ne <| h2 (aux heN).isRestriction (he.delete_simplifies.trans h1)
  obtain ⟨f, hfN, hef⟩ := h1.exists_of_isNonloop he
  specialize aux hfN
  refine ⟨f, ⟨hfN, hef⟩, fun g ⟨hgE, hgf⟩ ↦ by_contra fun hne ↦ aux.ne (h2 aux.isRestriction ?_)⟩
  have hgf : N.Parallel g f := (hgf.symm.trans hef).parallel_isRestriction h1.isRestriction hgE hfN
  exact (hgf.delete_right_simplifies hne).trans h1

lemma Simple.isSimplification_of_simplifies (hN : N.Simple) (hNM : N ≤si M) :
    N.IsSimplification M := by
  rw [isSimplification_iff_minimal_simplifies, and_iff_right hNM]
  exact fun N' hN' hN'M ↦ by simpa using hN'M.simplifies_of_isRestriction hN' hNM.isRestriction

lemma IsSimplification.isSimplification_of_simplifies {N₀ : Matroid α}
    (hN₀N : N₀.IsSimplification N) (hNM : N ≤si M) : N₀.IsSimplification M :=
  hN₀N.simple.isSimplification_of_simplifies <| hN₀N.simplifies.trans hNM

lemma IsSimplification.of_isRestriction {M' : Matroid α} (h : N.IsSimplification M) (hNM' : N ≤r M')
    (hM'M : M' ≤r M) : N.IsSimplification M' := by
  obtain ⟨R, hR, rfl⟩ := hM'M.exists_eq_restrict
  rw [isSimplification_iff] at h ⊢
  refine ⟨h.1, hNM', fun e he ↦ ?_⟩
  obtain ⟨f, hf, hf'⟩ := h.2.2 (he.of_isRestriction hM'M)
  simp only [restrict_parallel_iff]
  exact ⟨f, ⟨hf.1, hf.2, he.mem_ground, hNM'.subset hf.1⟩, by tauto⟩

lemma IsPoint.mem_simplification (he : M.IsPoint {e}) (hN : N.IsSimplification M) : e ∈ N.E := by
  have hcl := (hN.parallel_repFun he.isNonloop).symm.mem_closure
  rw [he.isFlat.closure, mem_singleton_iff] at hcl
  rw [← hcl]
  exact hN.repFun_apply_mem_ground he.isNonloop

lemma IsSimplification.delete (hN : N.IsSimplification M) (hD : D ⊆ N.E) :
    (N ＼ D).IsSimplification (M ＼ ⋃ e ∈ D, {f | M.Parallel e f}) := by
  rw [isSimplification_iff, and_iff_right (hN.simple.loopless.delete D)]
  simp only [delete_isNonloop_iff, mem_iUnion, exists_prop, not_exists, not_and, delete_ground,
    mem_diff, delete_parallel_iff, and_imp, mem_setOf_eq]
  refine ⟨?_, fun e he hcl ↦ ?_⟩
  · obtain ⟨R, hR, rfl⟩ := hN.isRestriction.exists_eq_restrict
    have hD_eq : D = (⋃ e ∈ D, {f | M.Parallel e f}) ∩ (M ↾ R).E := by
      refine (subset_inter ?_ hD).antisymm ?_
      · nth_rw 1 [← biUnion_of_singleton D]
        refine biUnion_mono rfl.subset fun e heD ↦ ?_
        simp [(hN.simple.isNonloop_of_mem (hD heD)).of_restrict]
      simp only [restrict_ground_eq, subset_def, mem_inter_iff, mem_iUnion, mem_setOf_eq,
        exists_prop, and_imp, forall_exists_index]
      refine fun e f hfD hef heR ↦ ?_
      rwa [← hN.simple.eq_of_parallel_of_mem (hD hfD) heR hef]
    nth_rw 1 [hD_eq, delete_inter_ground_eq, ← delete_compl hR, delete_comm]
    apply delete_isRestriction

  obtain ⟨f, ⟨hfN, hef⟩, h_u⟩ := hN.exists_unique he
  exact ⟨f, ⟨⟨hfN, fun hfD ↦ hcl f hfD hef.symm⟩, hef, hcl,
    fun x hxD hxf ↦ hcl x hxD (hxf.trans hef.symm)⟩, fun y hy ↦ h_u _ ⟨hy.1.1, hy.2.1⟩⟩

/-- Any two simplifications of `M` are isomorphic. -/
noncomputable def IsSimplification.iso {N N' : Matroid α} (hN : N.IsSimplification M)
    (hN' : N'.IsSimplification M) : N ≂ N' :=
  Iso.mk
    (toEquiv := {
      toFun := fun x ↦ ⟨_, hN'.repFun_apply_mem_ground (hN.isNonloop_of_mem x.2)⟩
      invFun := fun x ↦ ⟨_, hN.repFun_apply_mem_ground (hN'.isNonloop_of_mem x.2)⟩
      left_inv := by simp [Function.LeftInverse, hN.ground_eq_image_repFun]
      right_inv := by
        simp [Function.LeftInverse, Function.RightInverse, hN'.ground_eq_image_repFun] })
  (indep_image_iff' := by
    simp only [Equiv.coe_fn_mk, hN.isRestriction.indep_iff, hN'.isRestriction.indep_iff,
      image_subset_iff, Subtype.coe_preimage_self, subset_univ, and_true]
    intro I
    rw [image_image, image_val_image_eq, indep_image_iff_of_injOn_paraMap]
    · refine (Simple.repFun_injOn ?_ hN'.repFun).mono (show ↑I ⊆ N.E by simp)
      rw [hN.isRestriction.eq_restrict]
      exact hN.simple
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index]
    exact fun e he _ ↦ Parallel.parallel' (hN'.repFun.rel_apply
      <| mem_parallelClasses_supp_iff.mpr (hN.isNonloop_of_mem he)) )

lemma IsSimplification.exists_of_isStrictRestriction (hN : N.IsSimplification M) (hNM : N <r M) :
    (∃ e, M.IsLoop e ∧ e ∉ N.E) ∨ (∃ e f, M.Parallel e f ∧ e ∈ M.E ∧ e ∉ N.E ∧ f ∈ N.E) := by
  obtain ⟨e, heM, heN⟩ := exists_of_ssubset hNM.ssubset
  obtain (he | he) := M.isLoop_or_isNonloop e
  · exact .inl ⟨e, he, heN⟩
  obtain ⟨f, hN⟩ := hN
  refine .inr ⟨e, f e, f.rel_apply' mem_parallelClasses_supp_iff he, heM, heN, ?_⟩
  simp only [hN, restrict_ground_eq, mem_image, mem_setOf_eq]
  exact ⟨e, he, rfl⟩

lemma IsSimplification.isSpanningRestriction (hN : N.IsSimplification M) : N ≤sr M :=
  hN.simplifies.isSpanningRestriction

lemma IsSimplification.isBase_of_isBase {B : Set α} (hN : N.IsSimplification M) (hB : N.IsBase B) :
    M.IsBase B :=
  (IsBase.isBasis_of_isRestriction hB hN.isRestriction).isBase_of_spanning
    hN.isSpanningRestriction.spanning

lemma IsSimplification.eRank_eq (hN : N.IsSimplification M) : N.eRank = M.eRank := by
  obtain ⟨R, hR : R ⊆ M.E, rfl⟩ := hN.isRestriction
  exact hN.isSpanningRestriction.spanning.eRank_restrict

lemma IsSimplification.ground_eq_biUnion_setOf_parallel [M.Loopless] (hNM : N.IsSimplification M) :
    M.E = ⋃ e ∈ N.E, {x | M.Parallel e x} := by
  simp only [subset_antisymm_iff, subset_def, mem_iUnion, mem_setOf_eq, exists_prop,
    forall_exists_index, and_imp]
  refine ⟨fun x hx ↦ ?_, fun _ _ _ ↦ Parallel.mem_ground_right⟩
  obtain ⟨f, hf⟩ := hNM.exists_unique (isNonloop_of_loopless hx)
  exact ⟨f, hf.1.1, hf.1.2.symm⟩

lemma IsSimplification.ground_eq_biUnion_closure [M.RankPos] (hNM : N.IsSimplification M) :
    M.E = ⋃ e ∈ N.E, M.closure {e} := by
  simp only [subset_antisymm_iff, subset_def, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  refine ⟨fun x hx ↦ ?_, fun _ _ _ h ↦ mem_ground_of_mem_closure h⟩
  obtain hx' | hx' := M.isLoop_or_isNonloop x hx
  · have hN : N.RankPos :=
      (rankPos_iff _).2 <| fun hN ↦ M.empty_not_isBase <| hNM.isBase_of_isBase hN
    obtain ⟨f, hf⟩ := N.exists_isNonloop
    exact ⟨f, hf.mem_ground, hx'.mem_closure _⟩
  obtain ⟨f, hf⟩ := hNM.exists_unique hx'
  exact ⟨f, hf.1.1, hf.1.2.mem_closure⟩

lemma IsSimplification.setOf_parallel_pairwiseDisjoint (hNM : N.IsSimplification M) :
    N.E.PairwiseDisjoint (fun e ↦ {x | M.Parallel e x}) := by
  intro x hx y hy hne
  simp_rw [disjoint_iff_forall_ne]
  rintro a hax _ hay rfl
  exact hne <| hNM.eq_of_parallel hx hy (Parallel.trans hax (Parallel.symm hay))

lemma IsSimplification.closure_pairwiseDisjoint [M.Loopless] (hNM : N.IsSimplification M) :
    N.E.PairwiseDisjoint (fun e ↦ M.closure {e}) := by
  intro x hx y hy hne
  simp_rw [disjoint_iff_forall_ne]
  rintro a hax _ hay rfl
  rw [← (M.isNonloop_of_loopless).parallel_iff_mem_closure] at hax hay
  exact hne <| hNM.eq_of_parallel hx hy (hax.symm.trans hay)


end IsSimplification

section Simplification

/-- A classically chosen simplification of `M`.
The definition depends on `M.removeLoops` rather than `M`, so the choice is a bit more stable;
deleting a subset of the loops does not change the choice of simplification. -/
def simplification (M : Matroid α) : Matroid α :=
  let si := fun (M : Matroid α) ↦ M ↾ M.parallelClasses.nonempty_repFun.some '' {e | M.IsNonloop e}
  si M.removeLoops

lemma simplification_isSimplification (M : Matroid α) : M.simplification.IsSimplification M := by
  let f := M.removeLoops.parallelClasses.nonempty_repFun.some
  refine ⟨Partition.RepFun.mk' _ f mem_parallelClasses_supp_iff
    (fun a ha ↦ f.apply_of_notMem (by simpa))
    (fun a ha ↦ by simpa [mem_setOf_eq, parallelClasses_rel_eq] using f.rel_apply (by simpa))
    (fun a b hab ↦ f.apply_eq_apply (by simpa)), ?_⟩
  simp only [simplification, removeLoops_isNonloop_iff]
  rw [removeLoops_restrict_eq_restrict]
  rfl
  simpa [M.removeLoops_isNonloop_iff] using f.image_subset_self

lemma exists_isSimplification (M : Matroid α) : ∃ (N : Matroid α), N.IsSimplification M :=
  ⟨M.simplification, M.simplification_isSimplification⟩

@[simp] lemma simplification_eq_self [Simple M] : M.simplification = M := by
  rwa [IsSimplification.eq_self_iff M.simplification_isSimplification]

lemma Simple.simplification_eq_self (h : M.Simple) : M.simplification = M :=
  by simp

instance simplification_simple (M : Matroid α) : Simple M.simplification :=
  IsSimplification.simple M.simplification_isSimplification

lemma simplification_eq_self_iff : M.simplification = M ↔ M.Simple :=
  ⟨fun h ↦ by rw [← h]; exact M.simplification_simple, fun _ ↦ simplification_eq_self⟩

lemma isSimplification_self [M.Simple] : M.IsSimplification M := by
  nth_rw 1 [← M.simplification_eq_self_iff.2 (by assumption)]
  exact M.simplification_isSimplification

lemma simplification_factorsThrough_removeLoops :
    Function.FactorsThrough (α := Matroid α) simplification removeLoops :=
  fun _ _ h ↦ by rw [simplification, h, simplification]

lemma simplification_delete_eq_of_subset_loops (M : Matroid α) (hX : X ⊆ M.loops) :
    (M ＼ X).simplification = M.simplification :=
  simplification_factorsThrough_removeLoops (removeLoops_del_eq_removeLoops hX)

@[simp] lemma simplification_removeLoops_eq (M : Matroid α) :
    M.removeLoops.simplification = M.simplification := by
  rw [removeLoops_eq_delete, simplification_delete_eq_of_subset_loops M Subset.rfl]

@[simp] lemma simplification_idem (M : Matroid α) :
    M.simplification.simplification = M.simplification := by
  rw [simplification_eq_self_iff]
  exact M.simplification_simple

lemma simplification_isRestriction (M : Matroid α) : M.simplification ≤r M :=
  M.simplification_isSimplification.isRestriction

@[simp] lemma simplification_eRank_eq (M : Matroid α) : M.simplification.eRank = M.eRank := by
  rw [M.simplification_isSimplification.eRank_eq]

end Simplification
section minor

lemma IsMinor.exists_isMinor_isSimplification (hNM : N ≤m M) (hN : N.Simple) :
    ∃ M₀, N ≤m M₀ ∧ IsSimplification M₀ M := by
  obtain ⟨I, hI, hr, -⟩ := hNM.exists_spanning_isRestriction_contract
  have hN' := hr.eq_restrict ▸
    M.contract_restrict_eq_restrict_contract (subset_diff.1 hr.subset).2.symm
  have h : (M ↾ (N.E ∪ I)).Simple := by
    apply Indep.simple_of_contract_simple (I := I) _ (by rwa [← hN'])
    refine restrict_indep_iff.2 ⟨hI, subset_union_right⟩
  obtain ⟨M₀, hM₀, h⟩ := h.exists_isRestriction_isSimplification_of_isRestriction (M := M)
    (restrict_isRestriction _ _ (union_subset hNM.subset hI.subset_ground))
  refine ⟨M₀, IsMinor.trans ?_ h.isMinor, hM₀⟩
  rw [hN']
  simpa using contract_isMinor _ _

lemma Simple.isMinor_iff_isMinor_simplification {β : Type*} (hN : N.Simple) {M : Matroid β} :
    Nonempty (N ≤i M) ↔ Nonempty (N ≤i M.simplification) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ ⟨e.trans M.simplification_isRestriction.isMinor.isoMinor⟩⟩
  obtain ⟨M₀, hM₀, ⟨i, -⟩⟩ := e.exists_iso
  obtain ⟨M', hM₀M', hM'⟩ := hM₀.exists_isMinor_isSimplification (hN.of_iso i)
  exact ⟨i.isoMinor.trans
    (hM₀M'.isoMinor.trans (hM'.iso (M.simplification_isSimplification)).isoMinor)⟩

end minor

-- end Simplification

-- section IsMinor

-- /-- Any simple restriction of `M` is a restriction of a simplification of `M`-/
-- lemma IsRestriction.exists_isRestriction_simplificationWrt (h : N ≤r M) [Simple N] :
--     ∃ c, M.ParallelChoiceFunction c ∧ N ≤r M.simplificationWrt c := by
--   obtain ⟨c, hc, hcN⟩ :=
--     extends_to_parallelChoiceFunction (show (M ↾ N.E).Simple by rwa [h.eq_restrict])
--   refine ⟨c, hc, ?_⟩
--   rw [← h.eq_restrict, simplificationWrt]
--   exact IsRestriction.of_subset _
--(fun e heN ↦ ⟨e, (isNonloop_of_loopless heN).of_isRestriction h,
--hcN heN⟩)

-- /-- Any simple minor of `M` is a minor of a simplification of `M`-/
-- lemma IsMinor.exists_minor_simplificationWrt {N M : Matroid α} [Simple N] (hN : N ≤m M) :
--     ∃ c, M.ParallelChoiceFunction c ∧ N ≤m M.simplificationWrt c := by
--   obtain ⟨I, hI, hr, -⟩ := hN.exists_contract_spanning_restrict
--   have hN' := hr.eq_restrict ▸
--     M.contract_restrict_eq_restrict_contract _ _ (subset_diff.1 hr.subset).2.symm
--   have h : (M ↾ (N.E ∪ I)).Simple := by
--     apply Indep.simple_of_contract_simple (I := I) _ (by rwa [← hN'])
--     refine restrict_indep_iff.2 ⟨hI, subset_union_right⟩
--   have hres := restrict_isRestriction M _ (union_subset hN.subset hI.subset_ground)
--   obtain ⟨c, hc, hrc⟩ := hres.exists_isRestriction_simplificationWrt
--   refine ⟨c, hc, ?_⟩
--   rw [← hr.eq_restrict]
--   apply IsMinor.trans ?_ hrc.minor
--   rw [contract_restrict_eq_restrict_contract _ _ _ (subset_diff.1 hr.subset).2.symm]
--   apply contract_minor

-- lemma minor_iff_minor_simplification {α β : Type*} {N : Matroid α} [Simple N] {M : Matroid β} :
--     N ≤i M ↔ N ≤i M.simplification := by
--   refine ⟨fun h ↦ ?_, fun h ↦ h.trans M.simplification_isRestriction.minor.isoMinor⟩
--   obtain ⟨N', hN'M, hi⟩ := h
--   have _ := ‹Simple N›.map_iso hi
--   obtain ⟨c, hc, hminor⟩ := hN'M.exists_minor_simplificationWrt
--   exact hi.isoMinor.trans <| hminor.isoMinor.trans
--     (M.simplificationWrt_isIso_simplification hc).isoMinor


-- end IsMinor
