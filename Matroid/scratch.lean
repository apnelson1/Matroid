import Mathlib.Combinatorics.Graph.Basic
import Matroid.Graph.Degree.Max
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Constructions.Basic

set_option linter.style.longLine false

lemma foo {s t r : ℕ} : False := by
  have hlt : r - (s + 2) < r - s := sorry
  exact foo (s := s + 2) (r := r) (t := t)
termination_by r - s


-- /-- If a circuit doesn't contain two particular cojoints `F[s], F[t]` of a fan `F`,
-- but it contains something between them, then it is an interval. -/
-- lemma IsFan.exists_eq_interval_of_notMem_mem_notMem {s t r : ℕ} (hF : M.IsFan F b c) (hsr : s < r)
--     (hrt : r < t) (ht : t < F.length) (hsb : s.bodd = !b) (htb : t.bodd = !b)
--     (hC : M.IsCircuit C) (hsC : F[s] ∉ C) (hrC : F[r] ∈ C) (htC : F[t] ∉ C) :
--     ∃ (p q : ℕ) (_ : s < p) (hpq : p < q) (hq : q < t), p.bodd = b ∧ q.bodd = b ∧
--     C = F.getElems (insert p <| insert q <| {i ∈ Ico p q | i.bodd = !b}) := by
--   by_cases hs1 : F[s + 1] ∈ C
--   · obtain ⟨j, hsj, hjt, rfl, rfl⟩ :=
--       hF.exists_eq_interval_of_notMem_mem_add_one (by lia) ht hsb htb hC hsC hs1 htC
--     refine ⟨s + 1, j, by simp [hsb, hsj, hjt]⟩
--   have hs1i : s + 1 < r := by grind
--   rw [hF.mem_iff_mem₁₂ _ _ (by lia) (by simpa [hsb]) hsC] at hs1
--   have hlt : r - (s + 2) < r - s := by lia
--   have hs2i : s + 2 < r := by grind
--   have hwin := hF.exists_eq_interval_of_notMem_mem_notMem (s := s + 2) (r := r) (t := t) hs2i hrt ht
--     (by simpa) htb hC hs1 hrC htC
--   grind
-- termination_by r - s
