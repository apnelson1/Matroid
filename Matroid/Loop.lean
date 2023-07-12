import Matroid.Circuit

/-
  A `loop` of a matroid_in is a one-element circuit, or, definitionally, a member of `M.cl ∅`.  
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of 
  `{e | M.loop e}` or similar. A `nonloop` is simply an element of the ground set that is not 
  a loop, but we give it a definition for the sake of dot notation. 
-/

-- open_locale classical 
-- open_locale classical
variable {α : Type _} {M : Matroid α}
--{M M₁ M₂ : Matroid α} {I C X Y Z K F F₁ F₂ : Set α} {e f x y z : α}

open Set

namespace Matroid

-- ### Loops
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
  he.dep.supset (singleton_subset_iff.mpr h) hXE

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

-- ### Nonloops
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

alias indep_singleton ↔ indep.nonloop nonloop.indep

theorem Indep.nonloop_of_mem (hI : M.Indep I) (h : e ∈ I) : M.Nonloop e := by
  rw [← not_loop_iff (hI.subset_ground h)]; exact fun he ↦ (he.not_mem_of_indep hI) h

theorem Cocircuit.nonloop_of_mem (hK : M.Cocircuit K) (he : e ∈ K) : M.Nonloop e := by
  rw [←not_loop_iff (hK.subset_ground he), ←singleton_circuit]
  intro he'
  have hcon := cocircuit_inter_circuit_ne_singleton he' hK
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

theorem pair_diff_left {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {x} = {y} := by 
  rw [insert_diff_of_mem _ (by exact rfl : x ∈ {x}), diff_singleton_eq_self (by simpa)]

theorem pair_diff_right {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {y} = {x} := by 
  rw [pair_comm, pair_diff_left hne.symm]

-- theorem subset_insert_iff : s ⊆ insert x t ↔ s ⊆ t ∨ (x ∈ s ∧ s \ {x} ⊆ t)

theorem subset_pair_iff {x y : α} : s ⊆ ({x,y} : Set α) ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x,y} := by 
  rw [←union_singleton, ←diff_subset_iff, subset_singleton_iff_eq, diff_eq_empty, 
    subset_singleton_iff_eq]
  constructor
  · rintro ((rfl | rfl) | h); simp; simp;
    have := subset_singleton_iff_eq.mp h.subset

  
  


theorem Nonloop.cl_eq_cl_iff_circuit_of_ne (he : M.Nonloop e) (hef : e ≠ f) :
    M.cl {e} = M.cl {f} ↔ M.Circuit {e, f} := by 
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · have hf := he.nonloop_of_mem_cl (by rw [←h]; exact M.mem_cl_self e)
    rw [circuit_iff, dep_iff, insert_subset_iff, and_iff_right he.mem_ground, 
      singleton_subset_iff, and_iff_left hf.mem_ground]
    refine' ⟨fun hi ↦ _, fun I hI hIss ↦ hIss.antisymm _⟩
    · apply hi.not_mem_cl_diff_of_mem (mem_insert _ _)
      rw [insert_diff_of_mem _ (by exact rfl : e ∈ {e}), diff_singleton_eq_self (by simpa), ←h]
      exact mem_cl_self _ _ he.mem_ground
    rintro x (rfl | rfl)
    · by_contra
  have hcl := (h.cl_diff_singleton_eq_cl e).trans (h.cl_diff_singleton_eq_cl f).symm
  rwa [pair_diff_left hef, pair_diff_right hef, eq_comm] at hcl
  -- rwa [insert_diff_of_mem _ (by exact rfl : e ∈ {e}), pair_comm, 
  --   insert_diff_of_mem _ (by exact rfl : f ∈ {f}), 
  --   diff_singleton_eq_self (by simpa), eq_comm, 
  --   diff_singleton_eq_self (by simpa using hef.symm)] at hcl
  -- refine' ⟨fun h ↦ _, fun h ↦ _⟩

-- theorem Nonloop.cl_eq_cl_iff_dep (he : M.Nonloop e) (hf : M.Nonloop f) :
--     M.cl {e} = M.cl {f} ↔ e = f ∨ ¬M.Indep {e, f} :=
--   by
--   rw [← imp_iff_or_not]
--   refine' ⟨fun hef ↦ _, fun h ↦ he.cl_eq_of_mem_cl (by rwa [hf.indep.mem_cl_iff])⟩
--   have hf : f ∈ M.cl {e} := by rw [hef]; exact M.mem_cl_self f
--   rw [pair_comm, eq_comm, ← mem_singleton_iff]
--   exact he.indep.mem_cl_iff.mp hf
-- #align matroid_in.nonloop.cl_eq_cl_iff_dep Matroid.Nonloop.cl_eq_cl_iff_dep

-- theorem exists_nonloop_of_empty_not_base (h : ¬M.base ∅) : ∃ e, M.Nonloop e :=
--   by
--   obtain ⟨B, hB⟩ := M.exists_base
--   obtain rfl | ⟨e, he⟩ := B.eq_empty_or_nonempty
--   · exact (h hB).elim
--   exact ⟨e, hB.indep.nonloop_of_mem he⟩
-- #align matroid_in.exists_nonloop_of_empty_not_base Matroid.exists_nonloop_of_empty_not_base

-- -- ### Coloops
-- /-- A coloop is a loop of the dual  -/
-- @[reducible] def Coloop (M : Matroid α) (e : α) : Prop :=
--   M﹡.Loop e
-- pp_extended_field_notation Coloop


-- @[ssE_finish_rules]
-- theorem Coloop.mem_ground (he : M.Coloop e) : e ∈ M.E :=
--   @Loop.mem_ground α (M﹡) e he
-- #align matroid_in.coloop.mem_ground Matroid.Coloop.mem_ground

-- theorem coloop_iff_mem_cl_empty : M.Coloop e ↔ e ∈ M﹡.cl ∅ :=
--   Iff.rfl
-- #align matroid_in.coloop_iff_mem_cl_empty Matroid.coloop_iff_mem_cl_empty

-- theorem coloops_eq_dual_cl_empty : {e | M.Coloop e} = M﹡.cl ∅ :=
--   rfl
-- #align matroid_in.coloops_eq_dual_cl_empty Matroid.coloops_eq_dual_cl_empty

-- theorem Coloop.dual_loop (he : M.Coloop e) : M﹡.Loop e :=
--   he
-- #align matroid_in.coloop.dual_loop Matroid.Coloop.dual_loop

-- theorem Loop.dual_coloop (he : M.Loop e) : M﹡.Coloop e := by rwa [coloop, dual_dual]
-- #align matroid_in.loop.dual_coloop Matroid.Loop.dual_coloop

-- @[simp]
-- theorem dual_coloop_iff_loop : M﹡.Coloop e ↔ M.Loop e :=
--   ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_loop, Loop.dual_coloop⟩
-- #align matroid_in.dual_coloop_iff_loop Matroid.dual_coloop_iff_loop

-- @[simp]
-- theorem dual_loop_iff_coloop : M﹡.Loop e ↔ M.Coloop e :=
--   ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_coloop, Coloop.dual_loop⟩
-- #align matroid_in.dual_loop_iff_coloop Matroid.dual_loop_iff_coloop

-- theorem coloop_iff_forall_mem_base : M.Coloop e ↔ ∀ ⦃B⦄, M.base B → e ∈ B :=
--   by
--   obtain he | he := (em (e ∈ M.E)).symm
--   · refine' iff_of_false (he ∘ coloop.mem_ground) (he ∘ fun h ↦ _)
--     obtain ⟨B, hB⟩ := M.exists_base
--     exact hB.subset_ground (h hB)
--   rw [← dual_loop_iff_coloop, loop_iff_not_mem_base_forall]
--   simp_rw [dual_base_iff']
--   refine' ⟨fun h B hB ↦ _, fun h B hB heB ↦ (h hB.1).2 heB⟩
--   have he' := h (M.E \ B) ⟨_, diff_subset _ _⟩
--   · simp only [mem_diff, not_and, not_not_mem] at he' ; exact he' he
--   simp only [sdiff_sdiff_right_self, inf_eq_inter]
--   rwa [inter_eq_self_of_subset_right hB.subset_ground]
-- #align matroid_in.coloop_iff_forall_mem_base Matroid.coloop_iff_forall_mem_base

-- theorem Base.mem_of_coloop {B : Set α} (hB : M.base B) (he : M.Coloop e) : e ∈ B :=
--   coloop_iff_forall_mem_base.mp he hB
-- #align matroid_in.base.mem_of_coloop Matroid.Base.mem_of_coloop

-- theorem Coloop.mem_of_base (he : M.Coloop e) {B : Set α} (hB : M.base B) : e ∈ B :=
--   coloop_iff_forall_mem_base.mp he hB
-- #align matroid_in.coloop.mem_of_base Matroid.Coloop.mem_of_base

-- theorem Coloop.nonloop (h : M.Coloop e) : M.Nonloop e :=
--   let ⟨B, hB⟩ := M.exists_base
--   hB.indep.nonloop_of_mem ((coloop_iff_forall_mem_base.mp h) hB)
-- #align matroid_in.coloop.nonloop Matroid.Coloop.nonloop

-- theorem Loop.not_coloop (h : M.Loop e) : ¬M.Coloop e :=
--   by
--   rw [← dual_loop_iff_coloop]; rw [← dual_dual M, dual_loop_iff_coloop] at h 
--   exact h.nonloop.not_loop
-- #align matroid_in.loop.not_coloop Matroid.Loop.not_coloop

-- theorem Coloop.not_mem_circuit (he : M.Coloop e) (hC : M.Circuit C) : e ∉ C :=
--   by
--   intro heC
--   rw [coloop_iff_forall_mem_base] at he 
--   obtain ⟨B, hB, hCB⟩ := (hC.diff_singleton_indep heC).exists_base_supset
--   have h := insert_subset.mpr ⟨he hB, hCB⟩
--   rw [insert_diff_singleton, insert_eq_of_mem heC] at h 
--   exact hC.dep.not_indep (hB.indep.subset h)
-- #align matroid_in.coloop.not_mem_circuit Matroid.Coloop.not_mem_circuit

-- theorem Circuit.not_coloop_of_mem (hC : M.Circuit C) (heC : e ∈ C) : ¬M.Coloop e := fun h ↦
--   h.not_mem_circuit hC heC
-- #align matroid_in.circuit.not_coloop_of_mem Matroid.Circuit.not_coloop_of_mem

-- /- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
-- theorem coloop_iff_forall_mem_cl_iff_mem
--     (he : e ∈ M.E := by aesop_mat) :
--     M.Coloop e ↔ ∀ X, e ∈ M.cl X ↔ e ∈ X :=
--   by
--   rw [coloop_iff_forall_mem_base]
--   refine' ⟨fun h X ↦ _, fun h B hB ↦ (h B).mp (by rwa [hB.cl])⟩
--   rw [cl_eq_cl_inter_ground]
--   refine' ⟨fun hecl ↦ _, fun heX ↦ _⟩
--   · obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
--     obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_supset
--     have heB := h hB
--     rw [hI.mem_cl_iff, imp_iff_right (hB.indep.subset (insert_subset.mpr ⟨heB, hIB⟩))] at hecl 
--     exact (hI.subset hecl).1
--   exact mem_cl_of_mem' _ ⟨heX, he⟩
-- #align matroid_in.coloop_iff_forall_mem_cl_iff_mem Matroid.coloop_iff_forall_mem_cl_iff_mem

-- /- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » M.E) -/
-- theorem coloop_iff_forall_mem_cl_iff_mem' :
--     M.Coloop e ↔ e ∈ M.E ∧ ∀ (X) (_ : X ⊆ M.e), e ∈ M.cl X ↔ e ∈ X :=
--   by
--   refine'
--     ⟨fun h ↦ ⟨h.mem_ground, fun X hX ↦ ((coloop_iff_forall_mem_cl_iff_mem h.mem_ground).mp h) X⟩,
--       _⟩
--   · rintro ⟨he, h⟩
--     apply (coloop_iff_forall_mem_cl_iff_mem he).mpr
--     intro X
--     have : X ∩ M.E ⊆ M.E := inter_subset_right _ _
--     have := h (X ∩ M.E) this; rw [← cl_eq_cl_inter_ground] at this 
--     rw [this]
--     refine' ⟨fun h ↦ h.1, fun h ↦ _⟩
--     · rw [mem_inter_iff]
--       exact ⟨h, he⟩
-- #align matroid_in.coloop_iff_forall_mem_cl_iff_mem' Matroid.coloop_iff_forall_mem_cl_iff_mem'

-- theorem Coloop.mem_cl_iff_mem (he : M.Coloop e) : e ∈ M.cl X ↔ e ∈ X :=
--   coloop_iff_forall_mem_cl_iff_mem.mp he X
-- #align matroid_in.coloop.mem_cl_iff_mem Matroid.Coloop.mem_cl_iff_mem

-- theorem Coloop.mem_of_mem_cl (he : M.Coloop e) (hX : e ∈ M.cl X) : e ∈ X := by
--   rwa [← he.mem_cl_iff_mem]
-- #align matroid_in.coloop.mem_of_mem_cl Matroid.Coloop.mem_of_mem_cl

-- @[simp]
-- theorem cl_inter_coloops_eq (M : Matroid α) (X : Set α) : M.cl X ∩ M﹡.cl ∅ = X ∩ M﹡.cl ∅ :=
--   by
--   simp_rw [Set.ext_iff, mem_inter_iff, ← coloop_iff_mem_cl_empty, and_congr_left_iff]
--   intro e he
--   rw [he.mem_cl_iff_mem]
-- #align matroid_in.cl_inter_coloops_eq Matroid.cl_inter_coloops_eq

-- theorem cl_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M﹡.cl ∅) : M.cl X ∩ K = X ∩ K :=
--   by
--   rw [M.cl_eq_cl_inter_ground]
--   nth_rw 2 [← inter_eq_self_of_subset_right (hK.trans (cl_subset_ground _ _))]
--   rw [dual_ground, ← inter_assoc]
--   refine' inter_eq_inter_iff_right.mpr ⟨(inter_subset_left _ _).trans (M.subset_cl _), _⟩
--   refine' ((inter_subset_inter_right (M.cl _) hK).trans (M.cl_inter_coloops_eq _).Subset).trans _
--   exact inter_subset_left _ _
-- #align matroid_in.cl_inter_eq_of_subset_coloops Matroid.cl_inter_eq_of_subset_coloops

-- theorem cl_union_eq_of_subset_coloops (X : Set α) {K : Set α} (hK : K ⊆ M﹡.cl ∅) :
--     M.cl (X ∪ K) = M.cl X ∪ K :=
--   by
--   have hKE : K ⊆ M.E := hK.trans (cl_subset_ground _ _)
--   rw [← cl_union_cl_left_eq]
--   refine' (M.subset_cl _).antisymm' fun e he ↦ _
--   obtain he' | ⟨C, hC, heC, hCss⟩ := mem_cl_iff_exists_circuit.mp he; assumption
--   have hCX : C \ {e} ⊆ M.cl X :=
--     by
--     rw [diff_subset_iff, singleton_union]
--     exact fun f hfC ↦
--       (hCss hfC).elim Or.inl fun h' ↦
--         h'.elim Or.inr fun hfK ↦ (hC.not_coloop_of_mem hfC).elim (hK hfK)
--   exact Or.inl (cl_subset_cl hCX (hC.subset_cl_diff_singleton e heC))
-- #align matroid_in.cl_union_eq_of_subset_coloops Matroid.cl_union_eq_of_subset_coloops

-- theorem cl_eq_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.cl K = K ∪ M.cl ∅ := by
--   rw [← empty_union K, cl_union_eq_of_subset_coloops _ hK, empty_union, union_comm]
-- #align matroid_in.cl_eq_of_subset_coloops Matroid.cl_eq_of_subset_coloops

-- theorem cl_diff_eq_of_subset_coloops (X : Set α) {K : Set α} (hK : K ⊆ M﹡.cl ∅) :
--     M.cl (X \ K) = M.cl X \ K := by
--   nth_rw 2 [← inter_union_diff X K]
--   rw [union_comm, cl_union_eq_of_subset_coloops _ ((inter_subset_right X K).trans hK),
--     union_diff_distrib, diff_eq_empty.mpr (inter_subset_right X K), union_empty, eq_comm,
--     sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
--   rintro e heK _ heX rfl
--   have he : M.coloop e := hK heK
--   rw [he.mem_cl_iff_mem] at heX 
--   exact heX.2 heK
-- #align matroid_in.cl_diff_eq_of_subset_coloops Matroid.cl_diff_eq_of_subset_coloops

-- theorem cl_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M﹡.cl ∅) :
--     Disjoint (M.cl X) K := by
--   rwa [disjoint_iff_inter_eq_empty, cl_inter_eq_of_subset_coloops X hK, ←
--     disjoint_iff_inter_eq_empty]
-- #align matroid_in.cl_disjoint_of_disjoint_of_subset_coloops Matroid.cl_disjoint_of_disjoint_of_subset_coloops

-- theorem cl_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M﹡.cl ∅)) :
--     Disjoint (M.cl X) (M﹡.cl ∅) :=
--   cl_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl
-- #align matroid_in.cl_disjoint_coloops_of_disjoint_coloops Matroid.cl_disjoint_coloops_of_disjoint_coloops

-- theorem cl_insert_coloop_eq (X : Set α) {he : M.Coloop e} : M.cl (insert e X) = insert e (M.cl X) :=
--   by
--   rw [← union_singleton, ← union_singleton, cl_union_eq_of_subset_coloops]
--   rwa [singleton_subset_iff]
-- #align matroid_in.cl_insert_coloop_eq Matroid.cl_insert_coloop_eq

-- @[simp]
-- theorem cl_union_coloops_eq (M : Matroid α) (X : Set α) : M.cl (X ∪ M﹡.cl ∅) = M.cl X ∪ M﹡.cl ∅ :=
--   cl_union_eq_of_subset_coloops _ Subset.rfl
-- #align matroid_in.cl_union_coloops_eq Matroid.cl_union_coloops_eq

-- theorem Coloop.not_mem_cl_of_not_mem (he : M.Coloop e) (hX : e ∉ X) : e ∉ M.cl X :=
--   mt he.mem_cl_iff_mem.mp hX
-- #align matroid_in.coloop.not_mem_cl_of_not_mem Matroid.Coloop.not_mem_cl_of_not_mem

-- theorem Coloop.insert_indep_of_indep (he : M.Coloop e) (hI : M.Indep I) : M.Indep (insert e I) :=
--   (em (e ∈ I)).elim (fun h ↦ by rwa [insert_eq_of_mem h]) fun h ↦ by
--     rwa [hI.insert_indep_iff_of_not_mem h, he.mem_cl_iff_mem]
-- #align matroid_in.coloop.insert_indep_of_indep Matroid.Coloop.insert_indep_of_indep

-- theorem union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.Indep (I ∪ K) ↔ M.Indep I :=
--   by
--   refine' ⟨fun h ↦ h.Subset (subset_union_left I K), fun h ↦ _⟩
--   obtain ⟨B, hB, hIB⟩ := h.exists_base_supset
--   exact hB.indep.subset (union_subset hIB (hK.trans fun e he ↦ coloop.mem_of_base he hB))
-- #align matroid_in.union_indep_iff_indep_of_subset_coloops Matroid.union_indep_iff_indep_of_subset_coloops

-- theorem diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.Indep (I \ K) ↔ M.Indep I :=
--   by
--   rw [← union_indep_iff_indep_of_subset_coloops hK, diff_union_self,
--     union_indep_iff_indep_of_subset_coloops hK]
-- #align matroid_in.diff_indep_iff_indep_of_subset_coloops Matroid.diff_indep_iff_indep_of_subset_coloops

-- theorem indep_iff_union_coloops_indep : M.Indep I ↔ M.Indep (I ∪ M﹡.cl ∅) :=
--   (union_indep_iff_indep_of_subset_coloops Subset.rfl).symm
-- #align matroid_in.indep_iff_union_coloops_indep Matroid.indep_iff_union_coloops_indep

-- theorem indep_iff_diff_coloops_indep : M.Indep I ↔ M.Indep (I \ M﹡.cl ∅) :=
--   (diff_indep_iff_indep_of_subset_coloops Subset.rfl).symm
-- #align matroid_in.indep_iff_diff_coloops_indep Matroid.indep_iff_diff_coloops_indep

-- theorem coloops_indep (M : Matroid α) : M.Indep (M﹡.cl ∅) := by
--   rw [indep_iff_diff_coloops_indep, diff_self]; exact M.empty_indep
-- #align matroid_in.coloops_indep Matroid.coloops_indep

-- theorem indep_of_subset_coloops (h : I ⊆ M﹡.cl ∅) : M.Indep I :=
--   M.coloops_indep.Subset h
-- #align matroid_in.indep_of_subset_coloops Matroid.indep_of_subset_coloops

-- theorem Coloop.cocircuit (he : M.Coloop e) : M.Cocircuit {e} := by
--   rwa [← dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit] at he 
-- #align matroid_in.coloop.cocircuit Matroid.Coloop.cocircuit

-- theorem coloop_iff_cocircuit : M.Coloop e ↔ M.Cocircuit {e} := by
--   rw [← dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit]
-- #align matroid_in.coloop_iff_cocircuit Matroid.coloop_iff_cocircuit

-- /- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » M₁.E) -/
-- /-- If two matroid_ins agree on loops and coloops, and have the same independent sets after 
--   loops/coloops are removed, they are equal. -/
-- theorem eq_of_indep_iff_indep_forall_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.e = M₂.e)
--     (hl : M₁.cl ∅ = M₂.cl ∅) (hc : M₁﹡.cl ∅ = M₂﹡.cl ∅)
--     (h : ∀ (I) (_ : I ⊆ M₁.e), Disjoint I (M₁.cl ∅ ∪ M₁﹡.cl ∅) → (M₁.indep I ↔ M₂.indep I)) :
--     M₁ = M₂ := by
--   refine' eq_of_indep_iff_indep_forall hE fun I hI ↦ _
--   rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ← hc]
--   obtain hdj | hndj := em (Disjoint I (M₁.cl ∅))
--   · rw [h _ ((diff_subset _ _).trans hI)]
--     rw [disjoint_union_right]
--     exact ⟨disjoint_of_subset_left (diff_subset _ _) hdj, disjoint_sdiff_left⟩
--   obtain ⟨e, heI, hel : M₁.loop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
--   refine' iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩) _
--   rw [loop_iff_mem_cl_empty, hl, ← loop_iff_mem_cl_empty] at hel ; rw [hc]
--   exact hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩
-- #align matroid_in.eq_of_indep_iff_indep_forall_disjoint_loops_coloops Matroid.eq_of_indep_iff_indep_forall_disjoint_loops_coloops

end Matroid

