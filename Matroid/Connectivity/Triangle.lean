
import Mathlib.Combinatorics.Matroid.Minor.Order
import Matroid.Connectivity.Separation.Vertical

open Set

variable {α : Type*} {s : Set α} {x y z : α}

lemma Set.eq_of_encard_eq_two_of_mem_of_mem (hs : s.encard = 2) (hxs : x ∈ s) (hys : y ∈ s)
    (hxy : x ≠ y) : s = {x,y} := by
  obtain ⟨a, b, hab, rfl⟩ := encard_eq_two.1 hs
  grind

-- for mathlib
lemma Set.exists_eq_of_encard_eq_three_of_mem
    (hs : s.encard = 3) (hxs : x ∈ s) : ∃ y z, y ≠ x ∧ z ≠ x ∧ y ≠ z ∧ s = {x,y,z} := by
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

lemma Set.eq_of_encard_eq_three_of_mem_of_mem_of_mem (hs : s.encard = 3) (hxs : x ∈ s) (hys : y ∈ s)
    (hzs : z ∈ s) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : s = {x,y,z} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := encard_eq_three.1 hs
  grind

namespace Matroid

variable {i : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P Q: M.Separation}

@[mk_iff]
structure IsTriangle (M : Matroid α) (T : Set α) : Prop where
  isCircuit : M.IsCircuit T
  three_elements : T.encard = 3

@[mk_iff]
structure IsTriad (M : Matroid α) (T : Set α) : Prop where
  isCocircuit : M.IsCocircuit T
  three_elements : T.encard = 3

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
  simp [isTriad_iff, isTriangle_iff]

@[simp]
lemma dual_isTriangle_iff : M✶.IsTriangle T ↔ M.IsTriad T := by
  simp [isTriad_iff, isTriangle_iff]

-- the lemmas ahead allow one to comfortably work with terms of the form `IsTriangle {e,f,g}`
-- rather than `IsTriangle T`.

lemma IsTriangle.ne₁₂ (h : M.IsTriangle {e,f,g}) : e ≠ f := by
  rintro rfl
  have hcard : encard {e,g} = 3 := by simpa using h.three_elements
  have hcon := hcard ▸ encard_pair_le e g
  norm_num at hcon

lemma IsTriangle.ne₁₃ (h : M.IsTriangle {e,f,g}) : e ≠ g := by
  rw [pair_comm] at h
  exact h.ne₁₂

lemma IsTriangle.ne₂₃ (h : M.IsTriangle {e,f,g}) : f ≠ g := by
  refine IsTriangle.ne₁₂ (M := M) (g := e) ?_
  convert h using 1
  grind

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.mem_ground₁ (h : M.IsTriangle {e,f,g}) : e ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.mem_ground₂ (h : M.IsTriangle {e,f,g}) : f ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.mem_ground₃ (h : M.IsTriangle {e,f,g}) : g ∈ M.E :=
  h.subset_ground <| by simp

lemma IsTriangle.mem_closure₁ (h : M.IsTriangle {e,f,g}) : e ∈ M.closure {f,g} := by
  have h' := h.isCircuit.mem_closure_diff_singleton_of_mem (e := e) (by simp)
  rwa [insert_diff_self_of_notMem (by simp [h.ne₁₂, h.ne₁₃])] at h'

lemma IsTriangle.mem_closure₂ (h : M.IsTriangle {e,f,g}) : f ∈ M.closure {e,g} :=
  IsTriangle.mem_closure₁ (M := M) <| by convert h using 1; grind

lemma IsTriangle.mem_closure₃ (h : M.IsTriangle {e,f,g}) : g ∈ M.closure {e,f} :=
  IsTriangle.mem_closure₁ (M := M) <| by convert h using 1; grind

lemma IsTriangle.isNonloop_of_mem (h : M.IsTriangle T) (heT : e ∈ T) : M.IsNonloop e := by
  refine h.isCircuit.isNonloop_of_mem ?_ heT
  rw [← two_le_encard_iff_nontrivial, h.three_elements]
  norm_num

lemma IsTriangle.isNonloop₁ (h : M.IsTriangle {e,f,g}) : M.IsNonloop e :=
  h.isNonloop_of_mem <| by simp

lemma IsTriangle.isNonloop₂ (h : M.IsTriangle {e,f,g}) : M.IsNonloop f :=
  h.isNonloop_of_mem <| by simp

lemma IsTriangle.isNonloop₃ (h : M.IsTriangle {e,f,g}) : M.IsNonloop g :=
  h.isNonloop_of_mem <| by simp

lemma IsTriad.ne₁₂ (h : M.IsTriad {e,f,g}) : e ≠ f :=
  h.dual_isTriangle.ne₁₂

lemma IsTriad.ne₁₃ (h : M.IsTriad {e,f,g}) : e ≠ g :=
  h.dual_isTriangle.ne₁₃

lemma IsTriad.ne₂₃ (h : M.IsTriad {e,f,g}) : f ≠ g :=
  h.dual_isTriangle.ne₂₃

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriad.mem_ground₁ (h : M.IsTriad {e,f,g}) : e ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriad.mem_ground₂ (h : M.IsTriad {e,f,g}) : f ∈ M.E :=
  h.subset_ground <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriad.mem_ground₃ (h : M.IsTriad {e,f,g}) : g ∈ M.E :=
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
