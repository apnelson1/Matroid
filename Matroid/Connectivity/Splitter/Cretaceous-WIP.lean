import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Tactic.IntervalCases
import Matroid.ForMathlib.Set
import Matroid.Connectivity.Separation.Two
import Matroid.Connectivity.Separation.Adherent
import Matroid.Triangle
import Matroid.Graph.Basic
import Matroid.Connectivity.Splitter.Cretaceous

open Set Matroid Function Separation

-- lemma Equiv.swap_eqOn_compl {α : Type*} [DecidableEq α] (x y : α) :
--     EqOn (Equiv.swap x y) (Equiv.refl α) {x, y}ᶜ :=
--   fun a ha ↦ by grind

-- lemma Equiv.swap_image_eq_self

namespace Matroid

variable {α β : Type*} {e f x y : α} {B C D C' D' I X Y Z s : Set α} {b i j k l : Bool} {k : ℕ∞}
    {M : Matroid α} {N : Matroid β} {P : M.Separation}

lemma circuit_of_element_contraction (hC : (M ／ {e}).IsCircuit C) :
    M.IsCircuit C ∨ M.IsCircuit (C ∪ {e}) := by
  have h₁ := IsCircuit.exists_subset_isCircuit_of_contract hC
  obtain ⟨C₁, hC₁, hC₂, hC₃⟩ := h₁
  by_cases! h₂ : C₁ = C
  · apply Or.inl
    rwa [h₂] at hC₁
  · apply Or.inr
    have h₃ : C ∪ {e} ⊆ C₁ := by
      grind only [= subset_def, = mem_union, = mem_singleton_iff, #2a2c, #4326, #8c6e, #2acb]
    have h₄ := subset_antisymm hC₃ h₃
    rwa [h₄] at hC₁

lemma exists_circuit_contract_elem_girth_decrease (k : ENat) (hk : k ≠ ⊤) (hg₁ : k ≤ M.girth)
    (hg₂ : (M ／ {e}).girth < k) : ∃ C, M.IsCircuit C ∧ C.encard = k ∧ e ∈ C := by
  by_cases! he : e ∈ M.E
  · rw [girth_lt_iff] at hg₂
    obtain ⟨C, hC₁, hC₂⟩ := hg₂
    use C ∪ {e}
    have h₁ := circuit_of_element_contraction hC₁
    have h₂ : M.IsCircuit (C ∪ {e}) := by
      by_contra! hc
      have h₃ := Or.resolve_right h₁ hc
      rw [le_girth_iff] at hg₁
      specialize hg₁ C h₃
      grind only
    constructor
    · exact h₂
    · constructor
      · rw [le_girth_iff] at hg₁
        specialize hg₁ (C ∪ {e}) h₂
        rw [union_singleton, encard_insert_of_notMem (by grind only [→ IsCircuit.subset_ground,
          = contract_ground, = subset_def, = mem_diff, = mem_singleton_iff, #524e])] at hg₁
        rw [union_singleton, encard_insert_of_notMem (by grind only [→ IsCircuit.subset_ground,
          = contract_ground, = subset_def, = mem_diff, = mem_singleton_iff, #524e])]
        enat_to_nat!
        grind only
      · simp only [union_singleton, mem_insert_iff, true_or]
  · have h : Disjoint {e} M.E := by grind only [= disjoint_left, = mem_singleton_iff]
    rw [← contract_eq_self_iff] at h
    rw [h] at hg₂
    grind only

lemma simple_cosimple_elem_removal {N : Matroid α} (hMsi : M.Simple) (hMsi' : M✶.Simple)
  (hr : ∀ e b T, Nonempty (N ≤i M.remove b {e}) → (M.bDual !b).IsTriangle T → e ∉ T) :
  ∀ b, Nonempty (N ≤i M.remove b {e}) → ((M.remove b {e}).Simple ∧ (M.remove b {e})✶.Simple) := by
intro b
wlog! hb : b = false generalizing N M b with aux
· intro hn'
  rw [Bool.ne_false_iff] at hb
  rw [hb, remove_true, ← nonempty_isoMinor_dual_iff] at hn'
  rw [hb, remove_true]
  have hr' : ∀ e b T, Nonempty (N✶ ≤i M✶.remove b {e}) → (M✶.bDual !b).IsTriangle T → e ∉ T := by
    intro e b T hn' hT
    rw [dual_remove, nonempty_isoMinor_dual_iff] at hn'
    rw [bDual_dual] at hT
    refine hr e (!b) T hn' hT
  specialize aux (N := N✶) (M := M✶) hMsi' (by grind only [= dual_dual]) hr' false
    (by simp only)
  rw [remove_false, ← dual_contract, dual_dual] at aux
  apply aux at hn'
  exact ⟨hn'.2, hn'.1⟩
· rw [hb, remove_false] at *
  intro hn
  constructor
  · simp only [simple_delete]
  · have hgM := hMsi'.three_le_girth
    have hgMe : 3 ≤ (M✶ ／ {e}).girth := by
      by_contra! aux
      obtain ⟨C, hC₁, hC₂, hC₃⟩ := exists_circuit_contract_elem_girth_decrease
        (k := 3) (by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true]) hgM aux
      specialize hr e false C
      rw [remove_false, Bool.not_false, bDual_true] at *
      have hC₄ : M✶.IsTriangle C := by exact ⟨hC₁, hC₂⟩
      have := hr hn hC₄
      contradiction
    rw [← dual_delete, le_girth_iff] at hgMe
    by_contra! aux
    rw [simple_iff_forall_isCircuit] at aux
    push Not at aux
    obtain ⟨C, hC₁, hC₂⟩ := aux
    specialize hgMe C hC₁
    grw [hC₂] at hgMe
    enat_to_nat; lia

lemma splitter_no_triangle_minor {N : Matroid α} (hM : M.TutteConnected 3) (h4 : 4 ≤ M.E.encard)
    (hNM : N <m M) (hN : N.TutteConnected 3)
    (hr : ∀ e b T, Nonempty (N ≤i M.remove b {e}) → (M.bDual !b).IsTriangle T → e ∉ T) :
    ∃ e b, Nonempty (N ≤i M.remove b {e}) ∧ (M.remove b {e}).TutteConnected 3 := by
  obtain ⟨e, heM, heN⟩ := hNM.exists_isMinor_contractElem_or_deleteElem
  wlog hed : N ≤m M ＼ {e} generalizing M N with aux
  · have hec := Or.resolve_right heN hed
    have hr' : ∀ e b T, Nonempty (N✶ ≤i M✶.remove b {e}) → (M✶.bDual !b).IsTriangle T → e ∉ T := by
      intro e b T hni
      specialize hr e (!b) T
      rw [← nonempty_isoMinor_dual_iff, dual_dual, remove_dual, dual_dual] at hni
      specialize hr hni
      rwa [bDual_dual]
    have hec := hec.dual
    rw [dual_contract] at hec
    specialize aux (M := M✶) (N := N✶) hM.dual h4 hNM.dual hN.dual hr' heM (Or.inr hec) hec
    obtain ⟨e, b, hni, hnT⟩ := aux
    use e, (!b)
    constructor
    · rwa [← nonempty_isoMinor_dual_iff, remove_dual, Bool.not_not]
    · rw [← dual_dual M, dual_remove, Bool.not_not]
      exact hnT.dual
  · clear heN
    by_cases! het : (M ＼ {e}).TutteConnected 3
    · use e, false
      rw [remove_false]
      exact ⟨⟨hed.isoMinor⟩, het⟩
    · have aux₁ := simple_cosimple_elem_removal (N := N) (e := e) (hM.simple h4) (hM.dual.simple h4)
          hr false
      rw [remove_false] at aux₁
      obtain ⟨f, hf₁, hf₂⟩ := exists_flexible (N := N) (e := e) hM h4 het
          ((aux₁ ⟨hed.isoMinor⟩).2) hed hN
      use f
      have aux := TutteConnected.contract_or_delete_internallyConnected_three (M := M) hM f
      by_cases! hf₃ : (M ／ {f}).InternallyConnected 3
      · use true
        constructor
        · refine hf₂ true
        · have aux₂ := simple_cosimple_elem_removal (N := N) (e := f) (hM.simple h4)
            (hM.dual.simple h4) hr true (hf₂ true)
          rw [← remove_true] at hf₃
          have : (M.remove true {f}).Simple := aux₂.1
          have : (M.remove true {f})✶.Simple := aux₂.2
          exact InternallyConnected.tutteConnected_three hf₃
      · use false
        have hf₄ := Or.resolve_left aux hf₃
        constructor
        · refine hf₂ false
        · have aux₂ := simple_cosimple_elem_removal (N := N) (e := f) (hM.simple h4)
              (hM.dual.simple h4) hr false (hf₂ false)
          rw [← remove_false] at hf₄
          have : (M.remove false {f}).Simple := aux₂.1
          have : (M.remove false {f})✶.Simple := aux₂.2
          exact InternallyConnected.tutteConnected_three hf₄
