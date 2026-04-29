import Matroid.Extremal.Covers
import Matroid.Order.Quotient

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k d : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' : Matroid α → Set α → Prop}

open Set
namespace Matroid

section Thick

def IsThick (M : Matroid α) (d : ℕ∞) (X : Set α := M.E) : Prop :=
    X.Nonempty → d ≤ X.coverNumber (M ↾ X).Nonspanning

lemma isThick_iff {M : Matroid α} {X : Set α} {d : ℕ∞} (h : X.Nonempty) :
    M.IsThick d X ↔ d ≤ X.coverNumber (M ↾ X).Nonspanning :=
  { mp := fun a ↦ a h, mpr := fun a _ ↦ a }

lemma isThick_empty {M : Matroid α} {d : ℕ∞} : M.IsThick d ∅ := by
  intro hem
  simp only [Set.not_nonempty_empty] at hem

lemma isThick_empty' {M : Matroid α} {d : ℕ∞} (hne : ¬ X.Nonempty) : M.IsThick d X := by
  rw [not_nonempty_iff_eq_empty.mp hne]
  exact isThick_empty

lemma isThick_iff_or {M : Matroid α} {X : Set α} {d : ℕ∞} :
    M.IsThick d X ↔ X = ∅ ∨ d ≤ X.coverNumber (M ↾ X).Nonspanning := by
  refine ⟨?_, ?_ ⟩
  · intro h
    by_cases hem : X.Nonempty
    · exact Or.inr (h hem)
    exact Or.symm (Or.inr (not_nonempty_iff_eq_empty.mp hem))
  intro h
  obtain rfl | ht := h
  · exact isThick_empty
  exact fun ?_ ↦ ht

@[simp]
lemma isThick_inter_ground_iff : M.IsThick d (X ∩ M.E) ↔ M.IsThick d X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro hne
    by_cases hem : (X ∩ M.E).Nonempty
    · rw [nonspanningNumber_intersection_ground hem]
      exact h hem
    rw [nonspanning_empty_intersection (not_nonempty_iff_eq_empty.mp hem) hne]
    simp
  intro hem
  rw [←nonspanningNumber_intersection_ground hem]
  exact h (Nonempty.mono (inter_subset_left) hem)

lemma isThick_iff' {M : Matroid α} {X : Set α} {d : ℕ∞} (h : X.Nonempty) :
    M.IsThick d X ↔ ∀ T, NonspanningCover M T X → d ≤ T.encard := by
  refine ⟨?_, ?_ ⟩
  · intro h T hT
    sorry
  sorry

lemma isThick_two (M : Matroid α) : M.IsThick 2 X := by
  intro hX
  obtain ht | ⟨T, hT, hTe⟩ := X.exists_cover (M ↾ X).Nonspanning
  · rw [ ht]
    simp only [le_top]
  rw [← hTe]
  by_contra hc
  obtain ⟨Y, hY⟩ := encard_eq_one.mp ((ENat.one_le_iff_ne_zero.mpr (encard_ne_zero.mpr
    (hT.nonempty hX ))).antisymm' (Order.le_of_lt_succ (Std.not_le.mp hc)))
  have hc1 : (M ↾ X).Spanning Y := by
    rw [← sUnion_singleton (s := Y), ←hY, hT.sUnion_eq]
    refine ⟨ ?_, IsLoopEquiv.subset_ground rfl fun ⦃a⦄ a_1 ↦ a_1⟩
    nth_rw 2 [← restrict_ground_eq (M := M) (R := X)]
    simp only [closure_ground]
  exact Ne.elim (fun a ↦ (hT.pProp Y (by rw [hY]; exact mem_singleton Y)).not_spanning  hc1) hTe

lemma IsThick.mono {d' : ℕ∞} (hTd : M.IsThick d X) (hd : d' ≤ d) : M.IsThick d' X := by
  intro hne
  grw [hd, hTd hne]

lemma IsThick.minor_mono (hTXd : M.IsThick d X) (hNM : N ≤m M) (hX : X ⊆ N.E) :
    N.IsThick d X := by
  intro hne
  rw [isThick_iff hne] at hTXd
  obtain ⟨C, D, hC, hD, hDC, hrw⟩ := hNM.exists_contract_indep_delete_coindep
  grw[hTXd]
  apply coverNumber_le_prop ((N ↾ X).Nonspanning) (M ↾ X).Nonspanning X
  intro Y hY hYns
  by_contra! hc
  rw [not_nonspanning_iff] at hc
  rw [nonspanning_iff] at hYns
  have hcon : (N ↾ X).Spanning Y := by
    rw [hrw, delete_restrict_eq_restrict (M ／ C) (by grind)]
    apply (restrict_spanning_iff (M := M ／ C ) (R := X) hY (hR := by grind )).2
    rw [restrict_spanning_iff hY (hR := by grind)] at hc
    rw [@contract_closure_eq]
    refine subset_diff.2 ⟨by grw [←closure_subset_closure M (subset_union_left), hc], by grind⟩
  exact hYns.1 hcon

lemma IsThick.contract_mono (hTXd : M.IsThick d X) (hC : C ⊆ X ) :
    (M ／ C).IsThick d (X \ C) := by
  intro hne
  grw [← nonspanningNumber_le_contract_subset hC hne, ←isThick_iff hne.left]
  exact hTXd

lemma IsThick_le_eRk {M : Matroid α} {a b : ℕ} (ht : M.IsThick (Nat.choose (b + 1) a) X)
    (ha : a ≠ 0) (hb : a ≤ b) (hM : NoUniformMinor M (a + 1) (b + 1)) :
    M.eRk X ≤ a := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · specialize aux (X := X ∩ M.E) (isThick_inter_ground_iff.mpr ht) (inter_subset_right)
    rwa [eRk_inter_ground] at aux
  by_contra hc
  simp only [not_le] at hc
  wlog hlt : M.eRk X = a + 1 generalizing M X with aux
  · rw [←eRank_restrict] at hc
    obtain ⟨Y, hY, hYeRK ⟩ := M.exists_contract_eRk_eq X (Order.add_one_le_of_lt hc)
    have := (ht.contract_mono hY)
    exact aux (M := M ／ Y) (X := X \ Y) (hM.minor (contract_isMinor M Y))
      (ht.contract_mono hY) (by grind) (by simp only [hYeRK, ENat.natCast_lt_succ]) hYeRK
  have hne : X.Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty.mp hc, eRk_empty, eq_comm] at hlt
    simp only [add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false] at hlt
  have : (M ↾ X).RankPos := by
    refine (eRank_ne_zero_iff (M ↾ X)).mp ?_
    simp only [eRank_restrict, ne_eq, hlt, add_eq_zero, ENat.coe_eq_zero, one_ne_zero,
      and_false, not_false_eq_true]
  have hle := rankCoverNumber_le_binomial_subset ha hb
    (hM.minor (IsRestriction.isMinor (restrict_isRestriction M X))) hlt
  grw [← nonspanning_le_rankCoverNumber hlt, ←(isThick_iff hne).1 ht, ENat.epow_one,
    ENat.coe_le_coe] at hle
  have : b.choose a < (b + 1).choose a := by
    rw [Nat.choose_succ_left (n := b) (k := a) (by grind) ]
    simp only [lt_add_iff_pos_left]
    refine Nat.zero_lt_of_ne_zero (Nat.choose_ne_zero_iff.2 (by lia))
  omega

end Thick

section Firm

@[mk_iff]
structure IsFirm (M : Matroid α) (d : ℕ∞) (X : Set (Set α)) : Prop where
  subset : ∀ x ∈ X, x ⊆ M.E
  eRk_union : ∀ X' ⊆ X, X.encard < d * X'.encard → M.eRk (⋃₀X) ≤ M.eRk (⋃₀ X')


end Firm
