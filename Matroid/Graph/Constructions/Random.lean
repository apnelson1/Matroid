import Mathlib.Data.Sym.Sym2.Order
import Matroid.Graph.Simple

variable {α β : Type*} {G : Graph α β} {x y z u v w : α} {e f : β} {A : Set α} {B : Set β}

open Set Function

lemma Nat.testBit_self (n : ℕ) : n.testBit n = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact ge_two_pow_of_testBit h |>.not_gt Nat.lt_two_pow_self



namespace Graph

/-- Construction of the random simple graph using binary numbers. -/
@[simps (attr := grind =)]
def randomGraph : Graph ℕ (Sym2 ℕ) where
  vertexSet := univ
  edgeSet := {e | Nat.testBit e.sup e.inf}
  IsLink e x y := Nat.testBit e.sup e.inf ∧ e = s(x, y)
  isLink_symm e he x y hxy := by
    simpa only [hxy, Sym2.sup_mk, Sym2.inf_mk, and_true, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, or_true] using hxy
  eq_or_eq_of_isLink_of_isLink e x y z w h₁ h₂ := by
    simp only [h₁, Sym2.sup_mk, Sym2.inf_mk, and_true, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at h₁ h₂
    tauto
  edge_mem_iff_exists_isLink e := by
    simp only [mem_setOf_eq, exists_and_left, iff_def, and_imp, forall_exists_index]
    exact imp_and.mp fun h ↦ ⟨⟨h, ⟨e.out.1, e.out.2, by simp⟩⟩, fun _ _ _ ↦ h⟩
  left_mem_of_isLink e x y h := mem_univ _

@[simp]
lemma randomGraph_inc (e x) : randomGraph.Inc e x ↔ e ∈ E(randomGraph) ∧ x ∈ e := by
  simp_rw [randomGraph_edgeSet, mem_setOf_eq, Inc, randomGraph_isLink, exists_and_left]
  rfl

@[simp]
lemma randomGraph_adj (x y : ℕ) :
    randomGraph.Adj x y ↔ Nat.testBit (max x y) (min x y) = true := by
  simp [Adj]

instance : Simple randomGraph where
  not_isLoopAt e x := by
    unfold IsLoopAt
    rw [randomGraph_isLink, and_comm, not_and]
    rintro rfl
    simp only [Sym2.sup_mk, max_self, Sym2.inf_mk, min_self, Bool.not_eq_true]
    exact Nat.testBit_self x
  eq_of_isLink e f x y he hf := by aesop

-- lemma randomGraph_extension' {A B : Set ℕ} (h : Disjoint A B) (hA : A.Finite) (hB : B.Finite) :
--     ∃ x, x ∉ A ∧ x ∉ B ∧ (∀ a ∈ A, randomGraph.Adj a x) ∧ (∀ b ∈ B, randomGraph.Adj b x) := by
--   classical
--   simp_rw [randomGraph_adj]
--   use (if h : B.Nonempty then 2^((hB.exists_maximal h).choose +1) else 0) + hA.toFinset.sum (2^·),
--     ?_, fun h' ↦ ?_, ?_, ?_
--   · sorry
--   · split_ifs at h' with hBne
--     · have := hB.exists_maximal hBne |>.choose_spec.2 h'
--       sorry
--     rw [Set.Nonempty, not_exists] at hBne
--     exact hBne _ h'
--   · rintro a haA
--     split_ifs with hBne
--     ·
--       sorry
--     sorry
--   · rintro b hbB
--     split_ifs with hBne
--     · sorry
--     sorry

end Graph
