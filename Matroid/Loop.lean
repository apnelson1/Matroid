import Matroid.Circuit
import Matroid.Constructions.ImagePreimage

/-
  A `Loop` of a matroid_in is a one-element circuit, or, definitionally, a member of `M.cl ∅`.
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of
  `{e | M.loop e}` or similar. A `Nonloop` is an element of the ground set that is not a loop.
-/


variable {α : Type*} {M : Matroid α}

open Set

namespace Matroid

section Loop
/-- A loop is a member of the closure of the empty set -/
@[pp_dot] def Loop (M : Matroid α) (e : α) : Prop :=
  e ∈ M.cl ∅

theorem loop_iff_mem_cl_empty : M.Loop e ↔ e ∈ M.cl ∅ := Iff.rfl

theorem cl_empty_eq_loops (M : Matroid α) : M.cl ∅ = {e | M.Loop e} := rfl

@[aesop unsafe 20% (rule_sets [Matroid])]
theorem Loop.mem_ground (he : M.Loop e) : e ∈ M.E :=
  cl_subset_ground M ∅ he

@[simp] theorem singleton_dep : M.Dep {e} ↔ M.Loop e := by
  rw [loop_iff_mem_cl_empty, M.empty_indep.mem_cl_iff_of_not_mem (not_mem_empty e),insert_emptyc_eq]

@[simp] theorem singleton_not_indep (he : e ∈ M.E := by aesop_mat) : ¬M.Indep {e} ↔ M.Loop e :=
  by rw [←singleton_dep, ←not_indep_iff]

theorem Loop.dep (he : M.Loop e) : M.Dep {e} :=
  singleton_dep.mpr he

theorem singleton_circuit : M.Circuit {e} ↔ M.Loop e := by
  simp_rw [←singleton_dep, circuit_def, mem_minimals_setOf_iff, and_iff_left_iff_imp,
    subset_singleton_iff_eq]
  rintro _ _ hY (rfl | rfl)
  · simpa using hY.nonempty
  rfl

theorem loop_iff_not_mem_base_forall (he : e ∈ M.E := by aesop_mat) :
    M.Loop e ↔ ∀ B, M.Base B → e ∉ B := by
  rw [←singleton_dep, ←not_indep_iff, not_iff_comm, not_forall]
  simp_rw [not_imp, not_not, ←singleton_subset_iff, indep_iff_subset_base]

theorem Loop.circuit (he : M.Loop e) : M.Circuit {e} :=
  singleton_circuit.mpr he

theorem Loop.mem_cl (he : M.Loop e) (X : Set α) : e ∈ M.cl X :=
  M.cl_mono (empty_subset _) he

theorem Loop.mem_flat (he : M.Loop e) {F : Set α} (hF : M.Flat F) : e ∈ F := by
  have := he.mem_cl F; rwa [hF.cl] at this

theorem Flat.loops_subset (hF : M.Flat F) : M.cl ∅ ⊆ F := fun _ he ↦ Loop.mem_flat he hF

theorem Loop.dep_of_mem (he : M.Loop e) (h : e ∈ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  he.dep.superset (singleton_subset_iff.mpr h) hXE

theorem Loop.not_indep_of_mem (he : M.Loop e) (h : e ∈ X) : ¬M.Indep X := fun hX ↦
  he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

theorem Loop.not_mem_of_indep (he : M.Loop e) (hI : M.Indep I) : e ∉ I := fun h ↦
  he.not_indep_of_mem h hI

theorem Loop.eq_of_circuit_mem (he : M.Loop e) (hC : M.Circuit C) (h : e ∈ C) : C = {e} := by
  rw [he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)]

theorem Indep.disjoint_loops (hI : M.Indep I) : Disjoint I (M.cl ∅) :=
  by_contra fun h ↦
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    Loop.not_mem_of_indep he hI heI

theorem Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I ⊆ M.cl ∅) : I = ∅ :=
  eq_empty_iff_forall_not_mem.mpr fun _ he ↦ Loop.not_mem_of_indep (h he) hI he

theorem cl_eq_loops_of_subset (h : X ⊆ M.cl ∅) : M.cl X = M.cl ∅ :=
  (cl_subset_cl_of_subset_cl h).antisymm (M.cl_mono (empty_subset _))

theorem Loop.cl (he : M.Loop e) : M.cl {e} = M.cl ∅ :=
  cl_eq_loops_of_subset (singleton_subset_iff.mpr he)

theorem loop_iff_cl_eq_cl_empty' : M.Loop e ↔ M.cl {e} = M.cl ∅ ∧ e ∈ M.E := by
  rw [←singleton_dep, dep_iff, singleton_subset_iff, and_congr_left_iff]
  intro he
  rw [not_indep_iff, singleton_dep]
  exact ⟨fun h ↦ by rw [h.cl], fun h ↦ by rw [loop_iff_mem_cl_empty, ← h]; exact M.mem_cl_self e⟩

theorem loop_iff_cl_eq_cl_empty (he : e ∈ M.E := by aesop_mat) :
    M.Loop e ↔ M.cl {e} = M.cl ∅ := by rw [loop_iff_cl_eq_cl_empty', and_iff_left he]

theorem loop_iff_forall_mem_compl_base : M.Loop e ↔ ∀ B, M.Base B → e ∈ M.E \ B := by
  refine' ⟨fun h B hB ↦ mem_of_mem_of_subset h _, fun h ↦ _⟩
  · rw [subset_diff, and_iff_right (cl_subset_ground _ _), disjoint_iff_inter_eq_empty,
      hB.indep.cl_inter_eq_self_of_subset (empty_subset B)]
  have he : e ∈ M.E := M.exists_base.elim (fun B hB ↦ (h B hB).1)
  rw [←singleton_dep, ←not_indep_iff]
  intro hei
  obtain ⟨B, hB, heB⟩ := hei.exists_base_superset
  exact (h B hB).2 (singleton_subset_iff.mp heB)

@[simp] theorem restrict_loop_iff {R : Set α}  :
    (M ↾ R).Loop e ↔ e ∈ R ∧ (M.Loop e ∨ e ∉ M.E) := by
  rw [← singleton_dep, restrict_dep_iff, singleton_subset_iff, ← singleton_dep, and_comm,
    and_congr_right_iff, Dep, and_or_right, singleton_subset_iff, and_iff_left or_not,
    or_iff_left_of_imp (fun he hi ↦ he (singleton_subset_iff.1 hi.subset_ground))]
  simp only [singleton_subset_iff, implies_true]

@[simp] theorem preimage_loop_iff {M : Matroid β} {f : α → β} :
    (M.preimage f).Loop e ↔ M.Loop (f e) := by
  rw [← singleton_dep, preimage_dep_iff]
  simp


end Loop

section Nonloop

/-- A `nonloop` is an element that is not a loop -/
@[pp_dot] def Nonloop (M : Matroid α) (e : α) : Prop :=
  ¬M.Loop e ∧ e ∈ M.E

@[reducible, pp_dot] def nonloops (M : Matroid α) : Set α :=
  {e | M.Nonloop e}

@[aesop unsafe 20% (rule_sets [Matroid])]
theorem Nonloop.mem_ground (h : M.Nonloop e) : e ∈ M.E :=
  h.2

theorem Nonloop.not_loop (he : M.Nonloop e) : ¬M.Loop e :=
  he.1

theorem Loop.not_nonloop (he : M.Loop e) : ¬M.Nonloop e :=
  fun h ↦ h.not_loop he

@[simp] theorem mem_nonloops_iff : e ∈ M.nonloops ↔ M.Nonloop e := Iff.rfl

theorem nonloop_of_not_loop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.Loop e) : M.Nonloop e :=
  ⟨h,he⟩

theorem loop_of_not_nonloop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.Nonloop e) : M.Loop e :=
  by rwa [Nonloop, and_iff_left he, not_not] at h

@[simp] theorem not_loop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.Loop e ↔ M.Nonloop e :=
  (and_iff_left he).symm

@[simp] theorem not_nonloop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.Nonloop e ↔ M.Loop e := by
  rw [← not_loop_iff, not_not]

theorem nonloops_eq_compl_cl_empty : M.nonloops = M.E \ M.cl ∅ := by
  ext; simp [Nonloop, Loop, and_comm]

@[simp] theorem compl_nonloops_eq_cl_empty : M.E \ M.nonloops = M.cl ∅ := by
  rw [nonloops_eq_compl_cl_empty, diff_diff_cancel_left (M.cl_subset_ground _)]

theorem loop_or_nonloop (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) :
    M.Loop e ∨ M.Nonloop e := by
  rw [Nonloop, and_iff_left he]; apply em

@[simp] theorem indep_singleton : M.Indep {e} ↔ M.Nonloop e := by
  rw [Nonloop, ←singleton_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, singleton_subset_iff.mp h.subset_ground⟩, fun h ↦ h.1 h.2⟩

alias ⟨Indep.nonloop, Nonloop.indep⟩ := indep_singleton

theorem Indep.nonloop_of_mem (hI : M.Indep I) (h : e ∈ I) : M.Nonloop e := by
  rw [← not_loop_iff (hI.subset_ground h)]; exact fun he ↦ (he.not_mem_of_indep hI) h

theorem Cocircuit.nonloop_of_mem (hK : M.Cocircuit K) (he : e ∈ K) : M.Nonloop e := by
  rw [←not_loop_iff (hK.subset_ground he), ←singleton_circuit]
  intro he'
  have hcon := he'.inter_cocircuit_ne_singleton hK
  rw [inter_eq_self_of_subset_left (singleton_subset_iff.2 he), encard_singleton] at hcon
  exact hcon rfl

theorem Circuit.nonloop_of_mem_of_one_lt_card (hC : M.Circuit C) (h : 1 < C.encard) (he : e ∈ C) :
    M.Nonloop e := by
  refine nonloop_of_not_loop (hC.subset_ground he) (fun hlp ↦ ?_)
  rw [hlp.eq_of_circuit_mem hC he, encard_singleton] at h
  exact h.ne rfl

theorem nonloop_of_not_mem_cl (h : e ∉ M.cl X) (he : e ∈ M.E := by aesop_mat) : M.Nonloop e :=
  nonloop_of_not_loop he (fun hel ↦ h (hel.mem_cl X))

theorem nonloop_iff_not_mem_cl_empty (he : e ∈ M.E := by aesop_mat) :
    M.Nonloop e ↔ e ∉ M.cl ∅ := by rw [Nonloop, loop_iff_mem_cl_empty, and_iff_left he]

theorem Nonloop.mem_cl_singleton (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : f ∈ M.cl {e} := by
  rw [←union_empty {_}, singleton_union] at *
  exact (M.cl_exchange (X := ∅) ⟨hef, (nonloop_iff_not_mem_cl_empty he.mem_ground).1 he⟩).1

theorem Nonloop.mem_cl_comm (he : M.Nonloop e) (hf : M.Nonloop f) : f ∈ M.cl {e} ↔ e ∈ M.cl {f} :=
  ⟨hf.mem_cl_singleton, he.mem_cl_singleton⟩

theorem Nonloop.nonloop_of_mem_cl (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : M.Nonloop f := by
  rw [Nonloop, and_comm];
  by_contra' h; apply he.not_loop
  rw [loop_iff_mem_cl_empty] at *; convert hef using 1
  obtain (hf | hf) := em (f ∈ M.E)
  · rw [←cl_cl _ ∅, ←insert_eq_of_mem (h hf), cl_insert_cl_eq_cl_insert, insert_emptyc_eq]
  rw [eq_comm, cl_eq_cl_inter_ground, inter_comm, inter_singleton_eq_empty.mpr hf]

theorem Nonloop.cl_eq_of_mem_cl (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : M.cl {e} = M.cl {f} := by
  rw [←cl_cl _ {f}, ←insert_eq_of_mem hef, cl_insert_cl_eq_cl_insert,
    ←cl_cl _ {e}, ←insert_eq_of_mem (he.mem_cl_singleton hef), cl_insert_cl_eq_cl_insert,
    pair_comm]

theorem Nonloop.cl_eq_cl_iff_circuit_of_ne (he : M.Nonloop e) (hef : e ≠ f) :
    M.cl {e} = M.cl {f} ↔ M.Circuit {e, f} := by
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · have hf := he.nonloop_of_mem_cl (by rw [←h]; exact M.mem_cl_self e)
    rw [circuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff,
      and_iff_right he.mem_ground, singleton_subset_iff, and_iff_left hf.mem_ground]
    refine' ⟨fun hi ↦ _, _⟩
    · apply hi.not_mem_cl_diff_of_mem (mem_insert _ _)
      rw [insert_diff_of_mem _ (by exact rfl : e ∈ {e}), diff_singleton_eq_self (by simpa), ←h]
      exact mem_cl_self _ _ he.mem_ground
    rintro x (rfl | rfl)
    · rwa [pair_diff_left hef, indep_singleton]
    rwa [pair_diff_right hef, indep_singleton]
  have hcl := (h.cl_diff_singleton_eq_cl e).trans (h.cl_diff_singleton_eq_cl f).symm
  rwa [pair_diff_left hef, pair_diff_right hef, eq_comm] at hcl

theorem Nonloop.cl_eq_cl_iff_eq_or_dep (he : M.Nonloop e) (hf : M.Nonloop f) :
    M.cl {e} = M.cl {f} ↔ e = f ∨ ¬M.Indep {e, f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.cl_eq_cl_iff_circuit_of_ne hne, or_iff_right hne,
    circuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff, singleton_subset_iff,
    and_iff_left hf.mem_ground, and_iff_left he.mem_ground, and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_diff_left hne, indep_singleton]
  rwa [pair_diff_right hne, indep_singleton]

theorem exists_nonloop (M : Matroid α) [RkPos M] : ∃ e, M.Nonloop e :=
  let ⟨_, hB⟩ := M.exists_base
  ⟨_, hB.indep.nonloop_of_mem hB.nonempty.some_mem⟩

theorem Nonloop.rkPos (h : M.Nonloop e) : M.RkPos :=
  h.indep.rkPos_of_nonempty (singleton_nonempty e)

@[simp] theorem restrict_nonloop_iff {R : Set α} : (M ↾ R).Nonloop e ↔ M.Nonloop e ∧ e ∈ R := by
  rw [← indep_singleton, restrict_indep_iff, singleton_subset_iff, indep_singleton]

theorem Nonloop.of_restrict {R : Set α} (h : (M ↾ R).Nonloop e) : M.Nonloop e :=
  (restrict_nonloop_iff.1 h).1

theorem nonloop_iff_restrict_of_mem {R : Set α} (he : e ∈ R) : M.Nonloop e ↔ (M ↾ R).Nonloop e :=
  ⟨fun h ↦ restrict_nonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_restrict⟩

@[simp] theorem preimage_nonloop_iff {M : Matroid β} {f : α → β} :
    (M.preimage f).Nonloop e ↔ M.Nonloop (f e) := by
  rw [← indep_singleton, preimage_indep_iff, image_singleton, indep_singleton,
    and_iff_left (injOn_singleton _ _)]

end Nonloop

section Loopless

/-- A Matroid is loopless if it has no loop -/
@[pp_dot] class Loopless (M : Matroid α) : Prop where
  cl_empty : M.cl ∅ = ∅

theorem loopless_iff_cl_empty : M.Loopless ↔ M.cl ∅ = ∅ :=
  ⟨fun h ↦ h.cl_empty, fun h ↦ ⟨h⟩⟩

theorem cl_empty_eq_empty (M : Matroid α) [Loopless M] : M.cl ∅ = ∅ :=
  ‹Loopless M›.cl_empty

theorem toNonloop [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.Nonloop e := by
  rw [←not_loop_iff, loop_iff_mem_cl_empty, cl_empty_eq_empty]; exact not_mem_empty _

theorem not_loop (M : Matroid α) [Loopless M] (e : α) : ¬ M.Loop e :=
  fun h ↦ (toNonloop (e := e)).not_loop h

theorem loopless_iff_forall_nonloop : M.Loopless ↔ ∀ e ∈ M.E, M.Nonloop e :=
  ⟨fun _ _ he ↦ toNonloop he,
    fun h ↦ ⟨subset_empty_iff.1 (fun e (he : M.Loop e) ↦ (h e he.mem_ground).not_loop he)⟩⟩

theorem loopless_iff_forall_not_loop : M.Loopless ↔ ∀ e ∈ M.E, ¬M.Loop e :=
  ⟨fun _ e _ ↦ M.not_loop e,
    fun h ↦ loopless_iff_forall_nonloop.2 fun e he ↦ (not_loop_iff he).1 (h e he)⟩

theorem loopless_iff_forall_circuit : M.Loopless ↔ ∀ C, M.Circuit C → 1 < C.encard := by
  simp_rw [lt_iff_not_le, encard_le_one_iff_eq, not_or, not_exists, ←nonempty_iff_ne_empty]
  refine ⟨fun h C hC ↦ ⟨hC.nonempty, fun e ↦ ?_⟩,
    fun h ↦ loopless_iff_forall_nonloop.2 fun e he ↦ (not_loop_iff he).1 fun hel ↦
      (h _ (singleton_circuit.2 hel)).2 e rfl⟩
  rintro rfl; rw [singleton_circuit] at hC; exact M.not_loop e hC

theorem Loopless.ground_eq (M : Matroid α) [Loopless M] : M.E = {e | M.Nonloop e} :=
  Set.ext fun _ ↦  ⟨fun he ↦ toNonloop he, Nonloop.mem_ground⟩

instance {M : Matroid α} [Matroid.Nonempty M] [Loopless M] : RkPos M :=
  M.ground_nonempty.elim fun _ he ↦ (toNonloop he).rkPos

/-- The matroid obtained by removing the loops of `e` -/
@[pp_dot] def removeLoops (M : Matroid α) : Matroid α := M ↾ {e | M.Nonloop e}

theorem removeLoops_eq_restr (M : Matroid α) : M.removeLoops = M ↾ {e | M.Nonloop e} := rfl

@[simp] theorem removeLoops_ground_eq (M : Matroid α) : M.removeLoops.E = {e | M.Nonloop e} := rfl

instance removeLoops_loopless (M : Matroid α) : Loopless M.removeLoops := by
  simp [loopless_iff_forall_nonloop, removeLoops]

@[simp] theorem removeLoops_eq_self (M : Matroid α) [Loopless M] : M.removeLoops = M := by
  rw [removeLoops, ← Loopless.ground_eq, restrict_ground_eq_self]

end Loopless
section Coloop

/-- A coloop is a loop of the dual  -/
@[pp_dot, reducible] def Coloop (M : Matroid α) (e : α) : Prop :=
  M﹡.Loop e

@[aesop unsafe 20% (rule_sets [Matroid])]
theorem Coloop.mem_ground (he : M.Coloop e) : e ∈ M.E :=
  @Loop.mem_ground α (M﹡) e he

theorem coloop_iff_mem_cl_empty : M.Coloop e ↔ e ∈ M﹡.cl ∅ := Iff.rfl

theorem coloops_eq_dual_cl_empty : {e | M.Coloop e} = M﹡.cl ∅ := rfl

theorem Coloop.dual_loop (he : M.Coloop e) : M﹡.Loop e :=
  he

theorem Coloop.cocircuit (he : M.Coloop e) : M.Cocircuit {e} :=
  Loop.circuit he

@[simp] theorem singleton_cocircuit : M.Cocircuit {e} ↔ M.Coloop e :=
  singleton_circuit

theorem Loop.dual_coloop (he : M.Loop e) : M﹡.Coloop e :=
  by rwa [Coloop, dual_dual]

@[simp] theorem dual_coloop_iff_loop : M﹡.Coloop e ↔ M.Loop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_loop, Loop.dual_coloop⟩

@[simp] theorem dual_loop_iff_coloop : M﹡.Loop e ↔ M.Coloop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_coloop, Coloop.dual_loop⟩

theorem coloop_iff_forall_mem_base : M.Coloop e ↔ ∀ ⦃B⦄, M.Base B → e ∈ B := by
  simp_rw [←dual_loop_iff_coloop, loop_iff_forall_mem_compl_base, dual_base_iff',
    dual_ground, mem_diff]
  refine' ⟨fun h B hB ↦ _, fun h B ⟨hB, _⟩ ↦ ⟨hB.subset_ground (h hB), (h hB).2⟩⟩
  · rw [←diff_diff_cancel_left hB.subset_ground]
    exact h (M.E \ B) ⟨(by rwa [diff_diff_cancel_left hB.subset_ground]), diff_subset _ _⟩

theorem Base.mem_of_coloop (hB : M.Base B) (he : M.Coloop e) : e ∈ B :=
  coloop_iff_forall_mem_base.mp he hB

theorem Coloop.mem_of_base (he : M.Coloop e) (hB : M.Base B) : e ∈ B :=
  coloop_iff_forall_mem_base.mp he hB

theorem Base.coloops_subset (hB : M.Base B) : M﹡.cl ∅ ⊆ B :=
  fun _ he ↦ Coloop.mem_of_base he hB

theorem Coloop.nonloop (h : M.Coloop e) : M.Nonloop e :=
  let ⟨_, hB⟩ := M.exists_base
  hB.indep.nonloop_of_mem ((coloop_iff_forall_mem_base.mp h) hB)

theorem Loop.not_coloop (h : M.Loop e) : ¬M.Coloop e := by
  rw [← dual_loop_iff_coloop]; rw [← dual_dual M, dual_loop_iff_coloop] at h
  exact h.nonloop.not_loop

theorem Coloop.not_mem_circuit (he : M.Coloop e) (hC : M.Circuit C) : e ∉ C :=
  fun h ↦ (hC.cocircuit.nonloop_of_mem h).not_loop he

theorem coloop_iff_forall_mem_compl_circuit [RkPos M﹡] :
    M.Coloop e ↔ ∀ C, M.Circuit C → e ∈ M.E \ C := by
  refine ⟨fun h C hC ↦ ⟨h.mem_ground, h.not_mem_circuit hC⟩, fun h ↦ ?_⟩
  rw [coloop_iff_forall_mem_base]
  refine fun B hB ↦ by_contra fun heB ↦ ?_
  have heE : e ∈ M.E := Exists.elim M.exists_circuit (fun C hC ↦ (h C hC).1)
  rw [←hB.cl_eq] at heE
  exact (h _ (hB.indep.fundCct_circuit ⟨heE, heB⟩)).2 (mem_fundCct _ _ _)

theorem Circuit.not_coloop_of_mem (hC : M.Circuit C) (heC : e ∈ C) : ¬M.Coloop e :=
  fun h ↦ h.not_mem_circuit hC heC

theorem coloop_iff_forall_mem_cl_iff_mem :
    M.Coloop e ↔ (∀ X, e ∈ M.cl X ↔ e ∈ X) ∧ e ∈ M.E := by
  rw [coloop_iff_forall_mem_base]
  refine' ⟨fun h ↦ _, fun h B hB ↦ _⟩
  · have heE := M.exists_base.elim (fun _ hB ↦ hB.subset_ground (h hB))
    refine' ⟨fun X ↦ ⟨fun heX ↦ _, fun heX ↦ M.mem_cl_of_mem' heX⟩, heE⟩
    obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
    obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_superset
    rw [cl_eq_cl_inter_ground, ←hI.cl_eq_cl] at heX
    exact (hI.subset ((hB.indep.cl_inter_eq_self_of_subset hIB).subset ⟨heX, h hB⟩)).1
  rw [←h.1, hB.cl_eq]
  exact h.2

theorem coloop_iff_forall_mem_cl_iff_mem' :
    M.Coloop e ↔ (∀ X, X ⊆ M.E → (e ∈ M.cl X ↔ e ∈ X)) ∧ e ∈ M.E := by
  rw [coloop_iff_forall_mem_cl_iff_mem, and_congr_left_iff]
  refine fun he ↦ ⟨fun h X _ ↦ h X, fun h X ↦ ?_⟩
  rw [cl_eq_cl_inter_ground, h (X ∩ M.E) (inter_subset_right _ _), mem_inter_iff, and_iff_left he]

theorem Coloop.mem_cl_iff_mem (he : M.Coloop e) : e ∈ M.cl X ↔ e ∈ X :=
  (coloop_iff_forall_mem_cl_iff_mem.1 he).1 X

theorem Coloop.mem_of_mem_cl (he : M.Coloop e) (hX : e ∈ M.cl X) : e ∈ X := by
  rwa [← he.mem_cl_iff_mem]

@[simp] theorem cl_inter_coloops_eq (M : Matroid α) (X : Set α) :
    M.cl X ∩ M﹡.cl ∅ = X ∩ M﹡.cl ∅ := by
  simp_rw [Set.ext_iff, mem_inter_iff, ← coloop_iff_mem_cl_empty, and_congr_left_iff]
  intro e he
  rw [he.mem_cl_iff_mem]

theorem cl_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M﹡.cl ∅) : M.cl X ∩ K = X ∩ K := by
  have hKE : K ∩ M.E = K
  · rw [inter_eq_left, ←dual_ground]; exact hK.trans (cl_subset_ground _ _)
  rw [←hKE, ←inter_assoc X, inter_right_comm, hKE, cl_eq_cl_inter_ground,
    subset_antisymm_iff, and_iff_left (inter_subset_inter_left K (M.subset_cl _)),
    ←inter_eq_self_of_subset_right hK, ←inter_assoc, cl_inter_coloops_eq,
    inter_assoc]

theorem cl_insert_coloop_eq (X : Set α) (he : M.Coloop e) :
    M.cl (insert e X) = insert e (M.cl X) := by
  rw [ subset_antisymm_iff, insert_subset_iff, and_iff_left (M.cl_subset_cl (subset_insert _ _)),
    and_iff_left (M.mem_cl_of_mem' (mem_insert _ _)), ←union_singleton (s := M.cl X),
    ←diff_subset_iff, subset_singleton_iff]
  refine fun f hf ↦ (he.mem_of_mem_cl (cl_exchange hf).1).elim Eq.symm (fun heX ↦ False.elim ?_)
  simp [insert_eq_of_mem heX] at hf

theorem cl_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M﹡.cl ∅) :
    M.cl (X ∪ K) = M.cl X ∪ K := by
  rw [← cl_union_cl_left_eq]
  refine' (M.subset_cl _).antisymm' fun e he ↦ _
  obtain he' | ⟨C, hC, heC, hCss⟩ := (mem_cl_iff_mem_or_exists_circuit
    (union_subset (M.cl_subset_ground _) (hK.trans (M﹡.cl_subset_ground _)))).1 he
  · exact he'
  have hCX : C \ {e} ⊆ M.cl X
  · rw [diff_subset_iff, singleton_union]
    refine (subset_inter hCss Subset.rfl).trans ?_
    rintro f ⟨rfl | h1 | h2, h⟩
    · apply mem_insert
    · exact Or.inr h1
    exact (hC.not_coloop_of_mem h (hK h2)).elim
  exact Or.inl (M.cl_subset_cl_of_subset_cl hCX (hC.mem_cl_diff_singleton_of_mem heC))

theorem cl_eq_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.cl K = K ∪ M.cl ∅ := by
  rw [← empty_union K, cl_union_eq_of_subset_coloops _ hK, empty_union, union_comm]

theorem cl_diff_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M﹡.cl ∅) :
    M.cl (X \ K) = M.cl X \ K := by
  nth_rw 2 [← inter_union_diff X K]
  rw [union_comm, cl_union_eq_of_subset_coloops _ ((inter_subset_right X K).trans hK),
    union_diff_distrib, diff_eq_empty.mpr (inter_subset_right X K), union_empty, eq_comm,
    sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  have he : M.Coloop e := hK heK
  rw [he.mem_cl_iff_mem] at heX
  exact heX.2 heK

theorem cl_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M﹡.cl ∅) :
    Disjoint (M.cl X) K := by
  rwa [disjoint_iff_inter_eq_empty, cl_inter_eq_of_subset_coloops X hK,
    ←disjoint_iff_inter_eq_empty]

theorem cl_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M﹡.cl ∅)) :
    Disjoint (M.cl X) (M﹡.cl ∅) :=
  cl_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

theorem cl_union_coloops_eq (M : Matroid α) (X : Set α) : M.cl (X ∪ M﹡.cl ∅) = M.cl X ∪ M﹡.cl ∅ :=
  cl_union_eq_of_subset_coloops _ Subset.rfl

theorem Coloop.not_mem_cl_of_not_mem (he : M.Coloop e) (hX : e ∉ X) : e ∉ M.cl X :=
  mt he.mem_cl_iff_mem.mp hX

theorem Coloop.insert_indep_of_indep (he : M.Coloop e) (hI : M.Indep I) : M.Indep (insert e I) := by
  refine (em (e ∈ I)).elim (fun h ↦ by rwa [insert_eq_of_mem h]) fun h ↦ ?_
  rw [←hI.not_mem_cl_iff_of_not_mem h]
  exact he.not_mem_cl_of_not_mem h

theorem union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) :
    M.Indep (I ∪ K) ↔ M.Indep I := by
  refine ⟨fun h ↦ h.subset (subset_union_left I K), fun h ↦ ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_base_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he ↦ Coloop.mem_of_base he hB))

theorem diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) :
    M.Indep (I \ K) ↔ M.Indep I := by
  rw [← union_indep_iff_indep_of_subset_coloops hK, diff_union_self,
    union_indep_iff_indep_of_subset_coloops hK]

theorem indep_iff_union_coloops_indep : M.Indep I ↔ M.Indep (I ∪ M﹡.cl ∅) :=
  (union_indep_iff_indep_of_subset_coloops Subset.rfl).symm

theorem indep_iff_diff_coloops_indep : M.Indep I ↔ M.Indep (I \ M﹡.cl ∅) :=
  (diff_indep_iff_indep_of_subset_coloops Subset.rfl).symm

theorem coloops_indep (M : Matroid α) : M.Indep (M﹡.cl ∅) := by
  rw [indep_iff_diff_coloops_indep, diff_self]; exact M.empty_indep

theorem indep_of_subset_coloops (h : I ⊆ M﹡.cl ∅) : M.Indep I :=
  M.coloops_indep.subset h

/-- If two matroids agree on loops and coloops, and have the same independent sets after
  loops/coloops are removed, they are equal. -/
theorem eq_of_indep_iff_indep_forall_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hl : M₁.cl ∅ = M₂.cl ∅) (hc : M₁﹡.cl ∅ = M₂﹡.cl ∅)
    (h : ∀ I, I ⊆ M₁.E → Disjoint I (M₁.cl ∅ ∪ M₁﹡.cl ∅) → (M₁.Indep I ↔ M₂.Indep I)) :
    M₁ = M₂ := by
  refine' eq_of_indep_iff_indep_forall hE fun I hI ↦ _
  rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.cl ∅))
  · rw [h _ ((diff_subset _ _).trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left (diff_subset _ _) hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.Loop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine' iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩) _
  rw [loop_iff_mem_cl_empty, hl, ← loop_iff_mem_cl_empty] at hel ; rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩

end Coloop

section Constructions

theorem eq_trivialOn_of_loops_union_coloops (hE : M.E = M.cl ∅ ∪ M﹡.cl ∅) :
    M = trivialOn (M﹡.cl ∅) M.E := by
  refine eq_of_base_iff_base_forall rfl (fun B hBE ↦ ?_)
  rw [trivialOn_base_iff (show M﹡.cl ∅ ⊆ M.E from M﹡.cl_subset_ground _)]
  rw [hE, ←diff_subset_iff] at hBE
  use fun h ↦ h.coloops_subset.antisymm' (by rwa [sdiff_eq_left.mpr h.indep.disjoint_loops] at hBE)
  rintro rfl
  obtain ⟨B, hB⟩ := M.exists_base
  rwa [hB.coloops_subset.antisymm ]
  refine subset_trans ?_ (diff_subset_iff.2 hE.subset)
  rw [subset_diff, and_iff_right hB.subset_ground]
  exact hB.indep.disjoint_loops

theorem trivialOn_loops_eq (I E : Set α) : (trivialOn I E).cl ∅ = E \ I := by
  simp

@[simp] theorem trivialOn_coloops_eq' (I E : Set α) : (trivialOn I E)﹡.cl ∅ = I ∩ E := by
  simp [inter_comm I]

theorem trivialOn_coloops_eq {I E : Set α} (h : I ⊆ E) : (trivialOn I E)﹡.cl ∅ = I := by
  simp [h]

end Constructions

end Matroid
