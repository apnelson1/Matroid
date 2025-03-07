/-
Formalizing stuff on Lehman's cut-short Shannon game
-/
import Matroid

open Set

variable {α : Type*} {M : Matroid α} {A B X Y I J : Set α} {e f : α}

namespace Matroid



lemma closure1 (heE : e ∈ M.E) (he : ¬ M.Coloop e)
    (h : ∀ a ∈ M.E, ∃ X Y, Disjoint X Y ∧ a ∉ X ∧ a ∉ Y ∧ e ∉ X ∧ e ∉ Y
      ∧ M.closure (insert a X) = M.closure Y ∧ e ∈ M.closure Y) :
    ∃ X Y, Disjoint X Y ∧ e ∉ X ∧ e ∉ Y ∧ M.closure X = M.closure Y ∧ e ∈ M.closure Y := by
  -- if `{e} = M.E`, pick `X` and `Y` empty.
  obtain h_eq | hssu := (singleton_subset_iff.2 heE).eq_or_ssubset
  · refine ⟨∅, ∅, by simp, by simp, by simp, rfl, ?_⟩
    obtain ⟨B, hB⟩ := M.exists_isBase
    obtain rfl | rfl := subset_singleton_iff_eq.1 <| hB.subset_ground.trans h_eq.symm.subset
    · rwa [hB.closure_eq]
    rwa [coisLoop_iff_not_mem_closure_compl, not_not, h_eq, diff_self] at he
  -- otherwise, let `a ∈ M.E \ {e}`, and let `Xa` and `Ya` be sets given by the hypothesis for `a`.
  obtain ⟨a, haE, hae : a ≠ e⟩ := exists_of_ssubset hssu
  obtain ⟨Xa, Ya, hdj, haX, haY, heX, heY, hclXY, hecl⟩ := h a haE
  -- If `Xa` spans `a`, then `Xa, Ya` satisfy the lemma.
  by_cases hacl : a ∈ M.closure Xa
  · exact ⟨Xa, Ya, hdj, heX, heY, by rwa [closure_insert_eq_of_mem_closure hacl] at hclXY, hecl⟩

  obtain ⟨b, ⟨hbY, hbE⟩, hbcl⟩ : ∃ b ∈ Ya ∩ M.E, M.closure (insert b Xa) = M.closure Ya
  · sorry

  obtain ⟨Xb, Yb, hbX, hbY, heX', heY', hbcl, hebcl⟩ := h b hbE
  refine ⟨Xa ∪ Yb, Xb ∪ Ya,

  -- obtain ⟨C, hCYa, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heY).1 hecl
  -- have hC
