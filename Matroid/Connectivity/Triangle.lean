import Matroid.Connectivity.Dual
import Matroid.Connectivity.Separation.Tutte
import Mathlib.Tactic.NormNum.Core

open Set

variable {α : Type*} {s : Set α} {x y z : α}

lemma Set.eq_of_encard_le_two_of_mem_of_mem (hs : s.encard ≤ 2) (hxs : x ∈ s) (hys : y ∈ s)
    (hxy : x ≠ y) : s = {x, y} := by
  rw [← encard_pair hxy] at hs
  refine (Finite.eq_of_subset_of_encard_le' ?_ (by grind) hs).symm
  grw [← encard_lt_top_iff, hs]
  simp

-- for mathlib
lemma Set.exists_eq_of_encard_eq_three_of_mem
    (hs : s.encard = 3) (hxs : x ∈ s) : ∃ y z, y ≠ x ∧ z ≠ x ∧ y ≠ z ∧ s = {x, y, z} := by
  obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := encard_eq_three.1 hs
  obtain rfl | rfl | rfl := by simpa using hxs
  · use b, c; grind
  · use a, c; grind
  use a, b; grind

-- for mathlib
lemma Set.exists_eq_of_encard_eq_three_of_mem_of_mem
    (hs : s.encard = 3) (hxs : x ∈ s) (hys : y ∈ s) (hxy : x ≠ y) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ s = {x,y,z} := by
  obtain ⟨a, b, hax, hbc, hab, rfl⟩ := s.exists_eq_of_encard_eq_three_of_mem hs hxs
  obtain rfl | rfl : y = a ∨ y = b := by simpa [hxy.symm] using hys
  · use b, hbc, hab.symm
  use a, hax, hab, by grind

lemma Set.eq_of_encard_le_three_of_mem_of_mem_of_mem (hs : s.encard ≤ 3) (hxs : x ∈ s) (hys : y ∈ s)
    (hzs : z ∈ s) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : s = {x, y, z} := by
  rw [show (3 : ℕ∞) = 2 + 1 from rfl, ← encard_pair hyz,
    ← encard_insert_of_notMem (a := x) (by grind)] at hs
  refine Eq.symm <| Finite.eq_of_subset_of_encard_le' ?_ (by grind) hs
  grw [← encard_lt_top_iff, hs]
  simp

namespace Matroid

variable {i b : Bool} {α : Type*} {e f g : α} {C K T X Y : Set α} {M : Matroid α}

@[mk_iff]
structure IsTriangle (M : Matroid α) (T : Set α) : Prop where
  isCircuit : M.IsCircuit T
  three_elements : T.encard = 3

abbrev IsTriad (M : Matroid α) (T : Set α) := M✶.IsTriangle T
  -- isCocircuit : M.IsCocircuit T
  -- three_elements : T.encard = 3

lemma isTriad_iff : M.IsTriad T ↔ M.IsCocircuit T ∧ T.encard = 3 :=
  isTriangle_iff (M := M✶) (T := T)

lemma IsTriad.isCocircuit (h : M.IsTriad T) : M.IsCocircuit T :=
  h.1

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.subset_ground (hT : M.IsTriangle T) : T ⊆ M.E := hT.isCircuit.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
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


lemma bDual_isTriad_iff : (M.bDual b).IsTriad X ↔ (M.bDual (!b)).IsTriangle X := by
  simp [← dual_isTriad_iff]


-- the lemmas ahead allow one to comfortably work with terms of the form `IsTriangle {e, f, g}`
-- rather than `IsTriangle T`.

lemma IsTriangle.ne₁₂ (h : M.IsTriangle {e, f, g}) : e ≠ f := by
  rintro rfl
  have hcard : encard {e,g} = 3 := by simpa using h.three_elements
  have hcon := hcard ▸ encard_pair_le e g
  norm_num at hcon

lemma IsTriangle.ne₁₃ (h : M.IsTriangle {e, f, g}) : e ≠ g := by
  rw [pair_comm] at h
  exact h.ne₁₂

lemma IsTriangle.ne₂₃ (h : M.IsTriangle {e, f, g}) : f ≠ g := by
  refine IsTriangle.ne₁₂ (M := M) (g := e) ?_
  convert h using 1
  grind

lemma IsTriangle.swap_right (h : M.IsTriangle {e, f, g}) : M.IsTriangle {e,g,f} := by
  rwa [pair_comm]

lemma IsTriangle.rotate_left (h : M.IsTriangle {e, f, g}) : M.IsTriangle {f,g,e} := by
  convert h using 1; grind

lemma IsTriangle.swap_left (h : M.IsTriangle {e, f, g}) : M.IsTriangle {f,e,g} :=
  h.rotate_left.swap_right

lemma IsTriangle.reverse (h : M.IsTriangle {e, f, g}) : M.IsTriangle {g,f,e} :=
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


-- lemma IsTriad.ne₁₂ (h : M.IsTriad {e, f, g}) : e ≠ f :=
--   h.dual_isTriangle.ne₁₂

-- lemma IsTriad.ne₁₃ (h : M.IsTriad {e, f, g}) : e ≠ g :=
--   h.dual_isTriangle.ne₁₃

-- lemma IsTriad.ne₂₃ (h : M.IsTriad {e, f, g}) : f ≠ g :=
--   h.dual_isTriangle.ne₂₃

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

/-- If `M` is a `3`-connected matroid and `T` is both a triangle and triad, then `M ≃ U₂,₄`. -/
lemma IsTriangle.eq_unifOn_two_four_of_isTriad_of_tutteConnected (hT : M.IsTriangle T)
    (hT' : M.IsTriad T) (hM : M.TutteConnected 3) :
    ∃ (E : Set α), E.encard = 4 ∧ M = unifOn E 2 := by
  obtain ⟨E, r, hr, hE, rfl⟩ :=
    hT.isCircuit.exists_eq_unifOn_of_isCocircuit_of_tutteConnected hT'.isCocircuit (k := 2)
    (by rw [hT.three_elements]; norm_num) (by simp) hM
  obtain rfl : r = 2 := ENat.coe_inj.1 hr
  use E, hE

@[mk_iff]
structure Triadular (M : Matroid α) : Prop where
  three_connected : M.TutteConnected (2 + 1)
  forall_mem_triangle : ∀ e ∈ M.E, ∃ T, M.IsTriangle T ∧ e ∈ T
  forall_mem_triad : ∀ e ∈ M.E, ∃ T, M.IsTriad T ∧ e ∈ T

@[simp]
lemma triadular_dual_iff : M✶.Triadular ↔ M.Triadular := by
  simp [triadular_iff, and_comm]

alias ⟨_, Triadular.dual⟩ := triadular_dual_iff

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

lemma IsTriangle.mem_or_mem_of_isCircuit_bDual (h : (M.bDual b).IsTriangle {e, f, g})
    (hK : (M.bDual !b).IsCircuit K) (heK : e ∈ K) : f ∈ K ∨ g ∈ K := by
  cases b <;> exact h.mem_or_mem_of_isCocircuit (by simpa using hK.isCocircuit) heK

lemma IsTriangle.mem_iff_mem_of_isCircuit_bDual (h : (M.bDual b).IsTriangle {e, f, g})
    (hK : (M.bDual !b).IsCircuit K) (heK : e ∉ K) : f ∈ K ↔ g ∈ K := by
  cases b <;> exact h.mem_iff_mem_of_isCocircuit (by simpa using hK.isCocircuit) heK

lemma IsTriangle.eq_of_isTriad {x y : α} (h : M.IsTriangle {e, f, g}) (h' : M.IsTriad {e, x, y}) :
    f = x ∨ f = y ∨ g = x ∨ g = y := by
  have h1 := h.reverse.mem_iff_mem_of_isCocircuit h'.isCocircuit
  grind [h.ne₁₃.symm, h.ne₁₂.symm]
