import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Matroid.ForMathlib.Set
import Matroid.Connectivity.Separation.Two
import Matroid.Connectivity.Fan.Cyclic
import Matroid.Connectivity.Separation.Infinite
import Matroid.Constructions.Small
import Matroid.Uniform.Minor

open Set Matroid Function Separation

variable {α β : Type*} {M N : Matroid α} {e f x y z : α}

/-- The statement that the splitter theorem holds for a particular pair of matroids `M`, `N`. -/
def SplitterTheoremHoldsFor (M : Matroid α) (N : Matroid β) : Prop :=
  -- `M` is a cyclic fan.
  (∃ (F : List α) (b : Bool), M.IsCyclicFan F b ∧ {e | e ∈ F} = M.E) ∨
  -- Some element of `M` that can be removed while keeping an `N`-minor and `3`-connectivity. -/
  (∃ (b : Bool) (e : α),
    e ∈ M.E ∧ Nonempty (N ≤i M.remove b {e}) ∧ (M.remove b {e}).TutteConnected 3)

/-- The statement of the splitter theorem. -/
def SplitterTheoremHolds (α β : Type*) : Prop := ∀ (M : Matroid α) (N : Matroid β), M.Finite →
    M.TutteConnected 3 → N.TutteConnected 3 → Nonempty (N <i M) → SplitterTheoremHoldsFor M N

/-- The general splitter theorem easily reduces to the case where `N` is actually a minor of `M`.-/
lemma splitterTheoremHolds_of_isMinor (h : ∀ (M N : Matroid α), M.TutteConnected 3 →
    N.TutteConnected 3 → M.Finite → N <m M → SplitterTheoremHoldsFor M N) :
    SplitterTheoremHolds α β := by
  rintro M N' hMfin hM hN' ⟨im⟩
  obtain ⟨N, hNM, i, -⟩ := im.exists_iso
  obtain hex | ⟨b, e, he, ⟨i'⟩, hconn⟩ := h M N hM (hN'.of_iso i) hMfin hNM
  · exact .inl hex
  exact .inr ⟨b, e, he, ⟨i.isoMinor.trans i'⟩, hconn⟩

/-- The splitter theorem holds if `M` has at most five elements. -/
lemma of_small (hM : M.TutteConnected 3) (h5 : M.E.encard ≤ 5) (hN : N.TutteConnected 3)
    (hNM : N <m M) : SplitterTheoremHoldsFor M N := by
  right
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  have hfin : M.Finite := by
    grw [finite_iff, ← encard_lt_top_iff, h5]
    simp
  obtain ⟨b, hb⟩ := hM.exists_forall_remove_of_isUniform (hM.isUniform_of_encard_le h5) hfin
  clear hfin
  wlog hb' : b = true generalizing M N b with aux
  · obtain rfl : b = false := by grind
    obtain ⟨b, e, he, hne, htc⟩ :=
      aux hM.dual (by simpa) hN.dual hNM.dual true (by simpa using fun e ↦ (hb e).dual) rfl
    refine ⟨!b, e, he, ?_, ?_⟩
    · rwa [dual_remove, nonempty_isoMinor_dual_iff] at hne
    simpa using htc.dual
  subst hb'
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.isMinor.exists_contract_indep_delete_coindep
  obtain ⟨e, heC⟩ | rfl := C.eq_empty_or_nonempty.symm
  · refine ⟨true, e, hC.subset_ground heC, ⟨IsMinor.isoMinor ?_⟩, hb e⟩
    exact (delete_isMinor ..).trans <| contract_isMinor_of_subset _ <| by simpa
  obtain rfl | ⟨e, heD⟩ := D.eq_empty_or_nonempty
  · simp [isStrictMinor_irrefl] at hNM
  simp_rw [contract_empty] at *
  have hmin : M ＼ D ≤m M.remove false {e}:= (delete_isRestriction_of_subset _ (by simpa)).isMinor
  refine ⟨false, e, hD.subset_ground heD, ⟨hmin.isoMinor⟩, ?_⟩
  apply TutteConnected.tutteConnected_of_tutteConnected_isSpanningRestriction hN hM
    hD.delete_isSpanningRestriction hmin (remove_isMinor ..)
