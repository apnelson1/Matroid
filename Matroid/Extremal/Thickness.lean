import Matroid.Extremal.Covers
import Matroid.Order.Quotient

set_option linter.style.longLine false

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k d : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' : Matroid α → Set α → Prop}

open Set
namespace Matroid

section Thick

def IsThick (M : Matroid α) (X : Set α) (d : ℕ∞) : Prop := d ≤ X.coverNumber (M ↾ X).Nonspanning

lemma isThick_iff {M : Matroid α} {X : Set α} {d : ℕ∞} :
    M.IsThick X d ↔ d ≤ X.coverNumber (M ↾ X).Nonspanning := Eq.to_iff rfl

lemma isThick_iff' {M : Matroid α} {X : Set α} {d : ℕ∞} :
    M.IsThick X d ↔ ∀ T, NonSpanningCover M T X → d ≤ T.encard := by
  refine ⟨?_, ?_ ⟩
  · intro h T hT

    sorry
  sorry

lemma isThick_nonempty (M : Matroid α) (hX: X.Nonempty) : M.IsThick X 2 := by
  rw [isThick_iff ]
  obtain ht | ⟨T, hT, hTe ⟩ := X.exists_cover (M ↾ X).Nonspanning
  · rw [ ht]
    simp only [le_top]
  rw [← hTe ]
  by_contra hc
  obtain ⟨Y, hY ⟩ := encard_eq_one.mp ((ENat.one_le_iff_ne_zero.mpr (encard_ne_zero.mpr
    ( hT.nonempty hX ))).antisymm' (Order.le_of_lt_succ (Std.not_le.mp hc ) ) )
  have hc1 : (M ↾ X).Spanning Y := by
    rw [← sUnion_singleton (s := Y), ←hY, hT.sUnion_eq]
    refine ⟨ ?_, IsLoopEquiv.subset_ground rfl fun ⦃a⦄ a_1 ↦ a_1  ⟩
    nth_rw 2 [← restrict_ground_eq (M := M) (R := X)]
    simp only [closure_ground]
  exact Ne.elim (fun a ↦ (hT.pProp Y ( by rw [hY]; exact mem_singleton Y )).not_spanning  hc1) hTe

lemma IsThick.mono {d' : ℕ∞} (hTd : M.IsThick X d ) (hd : d' ≤ d ) : M.IsThick X d' := by sorry

lemma IsThick.minor_mono (hTXd : M.IsThick X d) (hNM : N ≤m M ) ( hX : X ⊆ N.E ) :
    N.IsThick X d := by
  rw [isThick_iff] at hTXd
  obtain ⟨C, D, hC, hD, hDC, hrw ⟩ := hNM.exists_contract_indep_delete_coindep
  grw[N.isThick_iff, hTXd]
  apply coverNumber_mono X
  intro Y hY hYns
  by_contra! hc
  rw [not_nonspanning_iff ] at hc
  rw [nonspanning_iff ] at hYns
  have hcon : (N ↾ X).Spanning Y := by
    rw [hrw, delete_restrict_eq_restrict (M ／ C) (by grind) ]
    apply (restrict_spanning_iff (M := M ／ C ) (R := X) hY (hR := by grind )).2
    rw [restrict_spanning_iff hY (hR := by grind)] at hc
    rw [@contract_closure_eq ]
    refine subset_diff.2 ⟨?_, by grind ⟩
    grw [←closure_subset_closure M (subset_union_left), hc]
  exact hYns.1 hcon




lemma IsThick.contract_mono (hTXd : M.IsThick X d) (hC : C ⊆ X ) (hne : (X \ C).Nonempty) :
    (M ／ C).IsThick (X \ C) d := by
  grw [isThick_iff, ←nonSpanningNumber_le_contract_subset hC hne  ]
  exact (isThick_iff ).mp hTXd

lemma IsThick_le_eRk {M : Matroid α} {a b : ℕ} (ht : M.IsThick X (Nat.choose (b + 1) a))
    (ha : a ≠ 0) (hb : a ≤ b) (hX : X ⊆ M.E)
    (hM : NoUniformMinor M (a + 1) (b + 1)) :
    M.eRk X ≤ a := by
  by_contra hc
  simp only [not_le] at hc
  wlog hlt : M.eRk X = a + 1 generalizing M X with aux
  · rw [←eRank_restrict] at hc
    obtain ⟨Y, hY, hYeRK ⟩ := M.exists_contract_eRk_eq X (Order.add_one_le_of_lt hc)
    have h3 : (X \ Y).Nonempty := by
      by_contra! hc
      rw [eq_comm, hc] at hYeRK
      simp at hYeRK
    exact aux (M := M ／ Y) (X := X \ Y) (ht.contract_mono hY h3) (by grind)
      (hM.minor (contract_isMinor M Y)) (by simp only [hYeRK, ENat.natCast_lt_succ]) hYeRK
  have : (M ↾ X).RankPos := by
    refine (eRank_ne_zero_iff (M ↾ X)).mp ?_
    simp only [eRank_restrict, ne_eq, hlt, add_eq_zero, ENat.coe_eq_zero, one_ne_zero,
      and_false, not_false_eq_true]
  have hle := coverNumberByRank_le_binomial_subset ha hb
    (hM.minor (IsRestriction.isMinor (restrict_isRestriction M X) ) ) hlt
  grw [← nonSpanning_le_coverNumberByRank hlt, ←isThick_iff.1 ht, ENat.epow_one, ENat.coe_le_coe ] at hle
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
