import Matroid.Bool
import Matroid.Simple
import Matroid.Uniform
import Matroid.ForMathlib.ENat
-- import Matroid.Connectivity.Separation.Tutte

open Set

variable {α : Type*} {s : Set α} {x y z : α}

namespace Matroid

variable {i b : Bool} {α : Type*} {e f g : α} {C K T X Y : Set α} {M : Matroid α}

@[mk_iff]
structure IsTriangle (M : Matroid α) (T : Set α) : Prop where
  isCircuit : M.IsCircuit T
  three_elements : T.encard = 3

abbrev IsTriad (M : Matroid α) (T : Set α) := M✶.IsTriangle T

lemma isTriad_iff : M.IsTriad T ↔ M.IsCocircuit T ∧ T.encard = 3 :=
  isTriangle_iff (M := M✶) (T := T)

lemma IsTriad.isCocircuit (h : M.IsTriad T) : M.IsCocircuit T :=
  h.1

@[aesop unsafe 20% (rule_sets := [Matroid]), grind →]
lemma IsTriangle.subset_ground (hT : M.IsTriangle T) : T ⊆ M.E := hT.isCircuit.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid]), grind →]
lemma IsTriad.subset_ground (hT : M.IsTriad T) : T ⊆ M.E := hT.isCocircuit.subset_ground

lemma IsTriangle.dual_isTriad (h : M.IsTriangle T) : M✶.IsTriad T := by
  simpa [isTriad_iff, isTriangle_iff] using h

lemma IsTriad.dual_isTriangle (h : M.IsTriad T) : M✶.IsTriangle T := by
  simpa [isTriad_iff, isTriangle_iff] using h

@[simp]
lemma dual_isTriad_iff : M✶.IsTriad T ↔ M.IsTriangle T := by
  simp [isTriangle_iff]

@[simp]
lemma dual_isTriangle_iff : M✶.IsTriangle T ↔ M.IsTriad T := by
  simp [isTriangle_iff]

@[simp]
lemma bDual_isTriad_iff : (M.bDual b).IsTriad X ↔ (M.bDual (!b)).IsTriangle X := by
  simp [← dual_isTriad_iff]

lemma IsTriangle.nonempty (h : M.IsTriangle T) : T.Nonempty := by
  grw [← one_le_encard_iff_nonempty, h.three_elements]
  simp

lemma IsTriangle.nontrivial_diff_singleton (h : M.IsTriangle T) (e) : (T \ {e}).Nontrivial := by
  grw [← two_le_encard_iff_nontrivial, ← ENat.add_one_le_add_one_iff,
    ← encard_le_encard_diff_singleton_add_one, h.three_elements]
  rfl

lemma IsTriangle.nontrivial (h : M.IsTriangle T) : T.Nontrivial :=
  (h.nontrivial_diff_singleton h.nonempty.some).mono diff_subset

lemma IsTriangle.finite (h : M.IsTriangle T) : T.Finite := by
  simp [← encard_lt_top_iff, h.three_elements]

-- the lemmas ahead allow one to comfortably work with terms of the form `IsTriangle {e, f, g}`
-- rather than `IsTriangle T`.

@[grind .]
lemma IsTriangle.ne₁₂ (h : M.IsTriangle {e, f, g}) : e ≠ f := by
  rintro rfl
  have hcard : encard {e,g} = 3 := by simpa using h.three_elements
  have hcon := hcard ▸ encard_pair_le e g
  norm_num at hcon

@[grind .]
lemma IsTriangle.ne₁₃ (h : M.IsTriangle {e, f, g}) : e ≠ g := by
  rw [pair_comm] at h
  exact h.ne₁₂

@[grind .]
lemma IsTriangle.ne₂₃ (h : M.IsTriangle {e, f, g}) : f ≠ g := by
  refine IsTriangle.ne₁₂ (M := M) (g := e) ?_
  convert h using 1
  grind

@[grind →]
lemma IsTriangle.nodup (h : M.IsTriangle {e, f, g}) : [e, f, g].Nodup := by
  grind

lemma IsTriangle.swap_right (h : M.IsTriangle {e, f, g}) : M.IsTriangle {e, g, f} := by
  rwa [pair_comm]

lemma IsTriangle.rotate (h : M.IsTriangle {e, f, g}) : M.IsTriangle {g, e, f} := by
  convert h using 1; grind

lemma IsTriangle.rotate_left (h : M.IsTriangle {e, f, g}) : M.IsTriangle {f, g, e} := by
  convert h using 1; grind

lemma IsTriangle.swap_left (h : M.IsTriangle {e, f, g}) : M.IsTriangle {f, e, g} :=
  h.rotate_left.swap_right

lemma IsTriangle.reverse (h : M.IsTriangle {e, f, g}) : M.IsTriangle {g, f, e} :=
  h.rotate_left.swap_left

lemma IsTriad.swap_right (h : M.IsTriad {e, f, g}) : M.IsTriad {e, g, f} := by
  rwa [pair_comm]

lemma IsTriad.rotate (h : M.IsTriad {e, f, g}) : M.IsTriad {g, e, f} := by
  convert h using 1; grind

lemma IsTriad.rotate_left (h : M.IsTriad {e, f, g}) : M.IsTriad {f, g, e} := by
  convert h using 1; grind

lemma IsTriad.swap_left (h : M.IsTriad {e, f, g}) : M.IsTriad {f, e, g} :=
  h.rotate_left.swap_right

lemma IsTriad.reverse (h : M.IsTriad {e, f, g}) : M.IsTriad {g, f, e} :=
  h.rotate_left.swap_left

lemma IsTriangle.indep₁₂ (h : M.IsTriangle {e, f, g}) : M.Indep {e,f} :=
  (h.isCircuit.diff_singleton_indep (e := g) (by simp)).subset <| by grind [h.ne₁₂, h.ne₂₃, h.ne₁₃]

lemma IsTriangle.indep₁₃ (h : M.IsTriangle {e, f, g}) : M.Indep {e,g} :=
  (h.isCircuit.diff_singleton_indep (e := f) (by simp)).subset <| by grind [h.ne₁₂, h.ne₂₃, h.ne₁₃]

lemma IsTriangle.indep₂₃ (h : M.IsTriangle {e, f, g}) : M.Indep {f,g} :=
  (h.isCircuit.diff_singleton_indep (e := e) (by simp)).subset <| by grind [h.ne₁₂, h.ne₂₃, h.ne₁₃]

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.mem_ground₁ (h : M.IsTriangle {e, f, g}) : e ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.mem_ground₂ (h : M.IsTriangle {e, f, g}) : f ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.mem_ground₃ (h : M.IsTriangle {e, f, g}) : g ∈ M.E :=
  h.subset_ground <| by simp

lemma IsTriangle.mem_closure₁ (h : M.IsTriangle {e, f, g}) : e ∈ M.closure {f,g} := by
  have h' := h.isCircuit.mem_closure_diff_singleton_of_mem (e := e) (by simp)
  rwa [insert_diff_self_of_notMem (by simp [h.ne₁₂, h.ne₁₃])] at h'

lemma IsTriangle.mem_closure₂ (h : M.IsTriangle {e, f, g}) : f ∈ M.closure {e,g} :=
  IsTriangle.mem_closure₁ (M := M) <| by convert h using 1; grind

lemma IsTriangle.mem_closure₃ (h : M.IsTriangle {e, f, g}) : g ∈ M.closure {e,f} :=
  IsTriangle.mem_closure₁ (M := M) <| by convert h using 1; grind

lemma IsTriangle.isNonloop_of_mem (h : M.IsTriangle T) (heT : e ∈ T) : M.IsNonloop e := by
  refine h.isCircuit.isNonloop_of_mem ?_ heT
  rw [← two_le_encard_iff_nontrivial, h.three_elements]
  norm_num

lemma IsTriangle.isNonloop₁ (h : M.IsTriangle {e, f, g}) : M.IsNonloop e :=
  h.isNonloop_of_mem <| by simp

lemma IsTriangle.isNonloop₂ (h : M.IsTriangle {e, f, g}) : M.IsNonloop f :=
  h.isNonloop_of_mem <| by simp

lemma IsTriangle.isNonloop₃ (h : M.IsTriangle {e, f, g}) : M.IsNonloop g :=
  h.isNonloop_of_mem <| by simp

lemma IsTriangle.isNonloop_bDual_of_mem (h : M.IsTriangle T) (heT : e ∈ T) {b : Bool} :
    (M.bDual b).IsNonloop e := by
  cases b
  · exact h.isNonloop_of_mem heT
  exact h.dual_isTriad.isCocircuit.isNonloop_of_mem heT

lemma IsTriangle.isNonloop_of_mem_of_bDual (h : (M.bDual b).IsTriangle T) (heT : e ∈ T) :
    M.IsNonloop e := by
  simpa using h.isNonloop_bDual_of_mem heT (b := b)

lemma IsTriangle.isNonloop_of_bDual₁ (h : (M.bDual b).IsTriangle {e, f, g}) : M.IsNonloop e :=
  h.isNonloop_of_mem_of_bDual (by simp)

lemma IsTriangle.isNonloop_of_bDual₂ (h : (M.bDual b).IsTriangle {e, f, g}) : M.IsNonloop f :=
  h.isNonloop_of_mem_of_bDual (by simp)

lemma IsTriangle.isNonloop_of_bDual₃ (h : (M.bDual b).IsTriangle {e, f, g}) : M.IsNonloop g :=
  h.isNonloop_of_mem_of_bDual (by simp)

lemma IsTriangle.isNonloop_bDual₁ (h : M.IsTriangle {e, f, g}) : (M.bDual b).IsNonloop e :=
  h.isNonloop_bDual_of_mem (by simp)

lemma IsTriangle.isNonloop_bDual₂ (h : M.IsTriangle {e, f, g}) : (M.bDual b).IsNonloop f :=
  h.isNonloop_bDual_of_mem (by simp)

lemma IsTriangle.isNonloop_bDual₃ (h : M.IsTriangle {e, f, g}) : (M.bDual b).IsNonloop g :=
  h.isNonloop_bDual_of_mem (by simp)

lemma IsTriangle.parallel_contract₁ (h : M.IsTriangle {e, f, g}) : (M ／ {e}).Parallel f g := by
  rw [parallel_iff_isCircuit h.ne₂₃]
  convert h.isCircuit.contract_isCircuit (C := {e}) (by grind) using 1
  grind

lemma IsTriangle.parallel_contract₂ (h : M.IsTriangle {e, f, g}) : (M ／ {f}).Parallel e g :=
  h.swap_left.parallel_contract₁

lemma IsTriangle.parallel_contract₃ (h : M.IsTriangle {e, f, g}) : (M ／ {g}).Parallel e f :=
  h.swap_right.parallel_contract₂

lemma isTriangle_iff_parallel_contract {x : α} (hef : ¬ M.Parallel e f) :
      M.IsTriangle {e, f, x} ↔ (M ／ {x}).Parallel e f := by
    refine ⟨fun h ↦ h.parallel_contract₃, fun h ↦ ?_⟩
    obtain he | he := em' <| (M ／ {x}).IsNonloop e
    · exact False.elim <| he <| h.isNonloop_left
    obtain rfl | hne := eq_or_ne e f
    · exact False.elim <| hef he.of_contract.parallel_self
    rw [parallel_iff_isCircuit hne] at h hef
    obtain ⟨C, hC, hefC, hC'ss⟩ := h.exists_subset_isCircuit_of_contract
    by_cases hx : x ∈ C
    · rwa [isTriangle_iff, encard_insert_of_notMem (by grind), encard_pair (by grind),
        and_iff_left two_add_one_eq_three, show {e, f, x} = C by grind]
    rw [show {e, f} = C by grind] at hef
    contradiction

lemma IsTriangle.restrict_simple (hT : M.IsTriangle T) : (M ↾ T).Simple := by
  have hC := hT.isCircuit.restrict_eq_circuitOn
  rw [circuitOn_eq_unifOn (n := 2) (by grind [hT.three_elements])] at hC
  simp [hC, unifOn_simple_iff]

@[simp]
lemma not_isTriangle_pair (M : Matroid α) (e f : α) : ¬ M.IsTriangle {e, f} := by
  intro h
  have hcon := h.three_elements.symm.le.trans <| encard_pair_le ..
  norm_num at hcon

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriad.mem_ground₁ (h : M.IsTriad {e, f, g}) : e ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriad.mem_ground₂ (h : M.IsTriad {e, f, g}) : f ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriad.mem_ground₃ (h : M.IsTriad {e, f, g}) : g ∈ M.E :=
  h.subset_ground <| by simp

lemma IsTriangle.eRk (hT : M.IsTriangle T) : M.eRk T = 2 := by
  have h := hT.three_elements
  rw [← hT.isCircuit.eRk_add_one_eq] at h
  enat_to_nat!; lia

lemma IsTriad.eRk_dual (hT : M.IsTriad T) : M✶.eRk T = 2 :=
  hT.dual_isTriangle.eRk

lemma IsTriangle.eRelRk (hT : M.IsTriangle T) (he : e ∈ T) : M.eRelRk {e} T = 1 := by
  have aux := M.eRelRk_add_eRk_eq {e} T
  rwa [union_eq_self_of_subset_right (by simpa), hT.eRk, (hT.isNonloop_of_mem he).eRk_eq,
    ← one_add_one_eq_two, ENat.add_one_eq_add_one_iff] at aux

lemma IsTriangle.eRk_union_le (hT : M.IsTriangle T) (hTX : (X ∩ T).Nonempty) :
    M.eRk (T ∪ X) ≤ M.eRk X + 1 := by
  obtain ⟨e, he⟩ := hTX
  obtain ⟨f, g, -, -, -, rfl⟩ := exists_eq_of_encard_eq_three_of_mem hT.three_elements he.2
  grw [← M.eRk_insert_le_add_one f X, ← M.eRk_closure_eq (insert f X),
    ← closure_insert_eq_of_mem_closure (e := g), M.eRk_closure_eq]
  · exact M.eRk_mono <| union_subset (by grind) (by grind)
  exact mem_of_mem_of_subset hT.mem_closure₃ <| M.closure_subset_closure (by grind)

lemma isTriangle_of_dep_of_encard_le [h : M.Simple] (hT : M.Dep T) (hcard : T.encard ≤ 3) :
    M.IsTriangle T := by
  rw [← three_le_girth_iff] at h
  refine ⟨hT.isCircuit_of_encard_le_girth ?_ (hcard.trans h),
      hcard.antisymm (h.trans hT.girth_le_card)⟩
  grw [← encard_lt_top_iff]; enat_to_nat!

@[mk_iff]
structure Triassic (M : Matroid α) : Prop where
  -- three_connected : M.TutteConnected (2 + 1)
  forall_mem_triangle : ∀ e ∈ M.E, ∃ T, M.IsTriangle T ∧ e ∈ T
  forall_mem_triad : ∀ e ∈ M.E, ∃ T, M.IsTriad T ∧ e ∈ T

@[simp]
lemma triassic_dual_iff : M✶.Triassic ↔ M.Triassic := by
  simp [triassic_iff, and_comm]

alias ⟨_, Triassic.dual⟩ := triassic_dual_iff

lemma Triassic.mem_triangle_bDual (hM : M.Triassic) (he : e ∈ M.E) (b : Bool) :
    ∃ T, (M.bDual b).IsTriangle T ∧ e ∈ T := by
  cases b
  · exact hM.forall_mem_triangle e he
  exact hM.forall_mem_triad e he

lemma Triassic.exists_triangle_bDual (hM : M.Triassic) (he : e ∈ M.E) (b : Bool) :
    ∃ x y, (M.bDual b).IsTriangle {e, x, y} := by
  obtain ⟨T, hT⟩ := hM.mem_triangle_bDual he b
  obtain ⟨y, z, -, -, -, rfl⟩ := exists_eq_of_encard_eq_three_of_mem hT.1.three_elements hT.2
  exact ⟨y, z, hT.1⟩

lemma IsTriangle.mem_iff_mem_of_isCocircuit (h : M.IsTriangle {e, f, g}) (hK : M.IsCocircuit K)
    (heK : e ∉ K) : f ∈ K ↔ g ∈ K := by
  wlog hfK : f ∈ K generalizing f g with aux
  · exact iff_of_false hfK fun hgK ↦ hfK <| (aux h.swap_right hgK).1 hgK
  obtain ⟨x, hx⟩ := (h.isCircuit.isCocircuit_inter_nontrivial hK ⟨f, by grind⟩).exists_ne f
  exact iff_of_true hfK <| by grind

lemma IsTriad.mem_iff_mem_of_isCircuit (h : M.IsTriad {e, f, g}) (hC : M.IsCircuit C)
    (heC : e ∉ C) : f ∈ C ↔ g ∈ C :=
  h.dual_isTriangle.mem_iff_mem_of_isCocircuit hC.isCocircuit heC

lemma IsTriangle.mem_or_mem_of_isCocircuit (h : M.IsTriangle {e, f, g}) (hK : M.IsCocircuit K)
    (heK : e ∈ K) : f ∈ K ∨ g ∈ K := by
  by_contra! hcon
  exact h.isCircuit.inter_isCocircuit_ne_singleton hK (e := e) <| by grind

lemma IsTriangle.mem_of_mem_of_notMem_of_is_Cocircuit (h : M.IsTriangle {e, f, g})
    (hK : M.IsCocircuit K) (heK : e ∈ K) (hfK : f ∉ K) : g ∈ K := by
  by_contra! hcon
  exact h.isCircuit.inter_isCocircuit_ne_singleton hK (e := e) <| by grind

lemma IsTriangle.mem_or_mem_of_isCircuit_bDual (h : (M.bDual b).IsTriangle {e, f, g})
    (hK : (M.bDual !b).IsCircuit K) (heK : e ∈ K) : f ∈ K ∨ g ∈ K := by
  cases b <;> exact h.mem_or_mem_of_isCocircuit (by simpa using hK.isCocircuit) heK

lemma IsTriangle.mem_iff_mem_of_isCircuit_bDual (h : (M.bDual b).IsTriangle {e, f, g})
    (hK : (M.bDual !b).IsCircuit K) (heK : e ∉ K) : f ∈ K ↔ g ∈ K := by
  cases b <;> exact h.mem_iff_mem_of_isCocircuit (by simpa using hK.isCocircuit) heK

lemma IsTriangle.mem_of_mem_of_notMem_of_isCircuit_bDual {b} (h : (M.bDual b).IsTriangle {e, f, g})
    (hK : (M.bDual (!b)).IsCircuit K) (heK : e ∈ K) (hfK : f ∉ K) : g ∈ K := by
  by_contra! hcon
  exact h.isCircuit.inter_isCocircuit_ne_singleton (by simpa using hK) (e := e) <| by grind

lemma IsTriangle.eq_of_isTriad {x y : α} (h : M.IsTriangle {e, f, g}) (h' : M.IsTriad {e, x, y}) :
    f = x ∨ f = y ∨ g = x ∨ g = y := by
  have h1 := h.reverse.mem_iff_mem_of_isCocircuit h'.isCocircuit
  grind [h.ne₁₃.symm, h.ne₁₂.symm]

lemma IsFinRankUniform.isTriangle_iff (hM : M.IsFinRankUniform 2) :
    M.IsTriangle C ↔ C.encard = 3 ∧ C ⊆ M.E := by
  grind [Matroid.isTriangle_iff, hM.isCircuit_iff]

@[simp]
lemma isTriangle_delete_iff {D} : (M ＼ D).IsTriangle T ↔ M.IsTriangle T ∧ Disjoint T D := by
  grind [isTriangle_iff, delete_isCircuit_iff]

@[simp]
lemma isTriad_contract_iff {C} : (M ／ C).IsTriad T ↔ M.IsTriad T ∧ Disjoint T C := by
  grind [isTriad_iff, contract_isCocircuit_iff]


-- lemma IsTriangle.isFiniteRankUniform_two_four_of_isTriangle_not_parallel {a b c d : α}
--     (habc : M.IsTriangle {a, b, c}) (habd : M.IsTriangle {a, b, d}) (hcd : ¬ M.Parallel c d) :
--     (M ↾ {a, b, c, d}).IsFiniteRankUniform 2 4 := by
--   suffices hM : (M ↾ {a, b, c, d}) = unifOn {a, b, c, d} 2 by
--     rw [hM]
--     convert unifOn_isFiniteRank_uniform (a := 2) ?_
--     sorry
--     sorry
--   refine ext_isCircuit_not_indep rfl ?_ ?_
--   · simp
--   obtain rfl | hne := eq_or_ne c d
--   · simp [habc.isNonloop₃] at hcd
--   rw [habc.isNonloop₃.not_parallel_iff habd.isNonloop₃ hne] at hcd

--   have hs : (M ↾ {a, b, c, d}).Simple := by
--     rw [simple_iff_forall_pair_indep]
--     rintro e f (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
--     · simp
--       grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--       IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--       Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     simp [restrict_indep_iff, insert_subset_iff]
--     grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--       IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--       Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]

--     all_goals sorry
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
--     -- grind [restrict_indep_iff, indep_singleton, IsTriangle.indep₁₂, IsTriangle.indep₂₃,
--     --   IsTriangle.indep₁₃, IsTriangle.isNonloop₁, IsTriangle.isNonloop₂, IsTriangle.isNonloop₃,
--     --   Indep.isNonloop_of_mem, pair_comm, insert_eq_of_mem, IsTriangle.subset_ground]
