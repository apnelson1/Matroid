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

lemma IsThick_iff {M : Matroid α} {X : Set α} {d : ℕ∞} :
    M.IsThick X d ↔ d ≤ X.coverNumber (M ↾ X).Nonspanning := Eq.to_iff rfl

lemma IsThick_iff' {M : Matroid α} {X : Set α} {d : ℕ∞} :
    M.IsThick X d ↔ ∀ T, NonSpanningCover M T X → d ≤ T.encard := by
  refine ⟨?_, ?_ ⟩
  · intro h T hT

    sorry
  sorry


-- def IsThick_set (M : Matroid α) (X : Set α ) (d : ℕ∞) : Prop :=
--     (M ↾ X).IsThick d

-- lemma IsThick_set_iff (M : Matroid α) (X : Set α ) (d : ℕ∞) :
--     M.IsThick_set X d ↔ d ≤ (M ↾ X).coverNumber Matroid.Nonspanning := by
--   sorry

lemma IsThick_two (M : Matroid α) (hX: X.Nonempty) : M.IsThick X 2 := by
  rw [IsThick_iff ]
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
    --refine ⟨ by simp only [closure_ground], by simp only [subset_refl] ⟩
  exact Ne.elim (fun a ↦ (hT.pProp Y ( by rw [hY]; exact mem_singleton Y )).not_spanning  hc1) hTe

lemma IsThick.mono {d' : ℕ∞} (hTd : M.IsThick X d ) (hd : d' ≤ d ) : M.IsThick X d' := by sorry

lemma IsThick_set.Minor_mon (hTXd : M.IsThick X d) (hNM : N ≤m M ) ( hX : X ⊆ N.E )
    (hXne : (M ↾ X ).Nonempty) :
    N.IsThick X d := by
  rw [N.IsThick_iff ]
  obtain ⟨C, D, hC, hD, hDC, hrw ⟩ := hNM.exists_contract_indep_delete_coindep
  have hDX : Disjoint D X := by grind
  have hCX : Disjoint C X := by grind
  have hg3 : (C ∩ M.closure X) ⊆ (M ↾ (X ∪ (C ∩ M.closure X))).E := by grind
  have hne : ((M ↾ (X ∪ (C ∩ M.closure X))) ／ (C ∩ M.closure X)).Nonempty := by
    refine (ground_nonempty_iff ((M ↾ (X ∪ C ∩ M.closure X)) ／ (C ∩ M.closure X))).mp ?_
    simp only [contract_ground, restrict_ground_eq, union_diff_right]
    have : (X \ C).Nonempty := by
      rw [ Disjoint.sdiff_eq_right hCX ]
      rwa [←(M ↾ X).ground_nonempty_iff, restrict_ground_eq] at hXne
    refine nonempty_of_not_subset ?_
    have : ¬X ⊆ C := by
      exact not_subset.mpr this
    grind
  sorry
  -- Peter?
  -- have hP : (M ／ C ↾ X) = (M ／ (C ∩ M.closure X) ↾ X) := by sorry
  -- have hCX' : Disjoint (C ∩ M.closure X) X := by grind
  -- grw [hrw, delete_restrict_eq_restrict (M ／ C) hDX, hP,
  --   M.contract_restrict_eq_restrict_contract hCX',
  --   ←NonSpanningNumber_contract hg3 hne, ← NonSpanningNumber_set_closure (inter_subset_right)
  --   (by grind) ]
  -- exact (IsThick_set_iff M X d).mp hTXd

lemma IsThick.Contract_mon (hTXd : M.IsThick X d) (hC : C ⊆ X ) (hne : (X \ C).Nonempty)
    : (M ／ C).IsThick (X \ C) d := by
  grw [IsThick_iff, ←NonSpanningNumber_contract_subset hC hne  ]
  exact (IsThick_iff ).mp hTXd


--Need approval
lemma exists_minor_encard (M : Matroid α) (hr : a ≤ M.eRank ) : ∃ X, X ⊆ M.E ∧ ( M ／ X).eRank = a := by
  obtain ⟨B, hB ⟩ := M.exists_isBase
  grw [← hB.encard_eq_eRank] at hr
  have ⟨Y, hYB, hYen ⟩ : ∃ Y, Y ⊆ B ∧ Y.encard = a := exists_subset_encard_eq hr
  use (B \ Y)
  refine ⟨ by grind, ?_ ⟩
  rw [ M.eRank_contract_eq_eRelRk_ground (B \ Y), (isBasis_self_iff_indep.mpr
    (Indep.diff (IsBase.indep hB) Y)).eRelRk_eq_encard_diff_of_subset_isBasis
    (isBasis_ground_iff.mpr hB) (by grind) ]
  simpa [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_self_of_subset_right hYB ]

--Need approval
lemma RelRk_restriction_eq_of_subset (M : Matroid α) {R : Set α} (hR : R ⊆ M.E) (hX : X ⊆ R)
    (hY : Y ⊆ R) : M.eRelRk X Y = (M ↾ R).eRelRk X Y := by
  rw [←delete_compl]
  exact (eRelRk_delete_eq_of_disjoint M (D := M.E \ R) ((disjoint_sdiff_iff_le (fun ⦃a⦄ a_1 ↦ hR (hX a_1)) hR).mpr hX )
    ((disjoint_sdiff_iff_le (fun ⦃a⦄ a_1 ↦ hR (hY a_1)) hR).mpr hY)).symm

--Need approval
lemma exists_minor_encard_eRk (M : Matroid α) (X : Set α) (hr : a ≤ M.eRk X ) (hX : X ⊆ M.E ) :
    ∃ C, C ⊆ X ∧ ( M ／ C).eRk (X \ C) = a := by
  obtain ⟨C, hCE, hCrk ⟩ := exists_minor_encard (M ↾ X ) (le_of_eq_of_le rfl hr )
  refine ⟨C, by grind , ?_ ⟩
  rw [←eRelRk_eq_eRk_diff_contract M C X]
  rw [eRank_contract_eq_eRelRk_ground (M := M ↾ X) C ] at hCrk
  simp only [restrict_ground_eq] at hCrk
  rw [ RelRk_restriction_eq_of_subset M hX (LE.le.subset hCE) (by grind) , hCrk  ]

lemma thick_Bound {M : Matroid α} [M.RankPos] {a b : ℕ} (ha : a ≠ 0) (hb : a ≤ b) (hX : X ⊆ M.E)
    (hM : NoUniformMinor M ( a + 1 ) (b + 1)) (ht : M.IsThick X (Nat.choose b a)) :
    M.eRk X ≤ a := by
  by_contra hc
  simp only [not_le] at hc
  wlog hlt : M.eRk X = a + 1 generalizing M X with aux
  · rw [←eRank_restrict] at hc
    obtain ⟨Y, hY, hYeRK ⟩ := M.exists_minor_encard_eRk X (Order.add_one_le_of_lt hc) hX
    have h1 : (M ／ Y).RankPos := by
      refine (eRank_ne_zero_iff (M ／ Y)).mp ?_
      have : 0 < (M ／ Y).eRank := by
        grw [←eRk_le_eRank (M ／ Y) (X \ Y), hYeRK]
        exact ENat.add_one_pos
      exact Ne.symm (Std.ne_of_lt this)
    have h3 : (X \ Y).Nonempty := by
      by_contra hc
      rw [nonempty_iff_ne_empty] at hc
      simp only [ne_eq, Decidable.not_not] at hc
      rw [hc] at hYeRK
      simp only [eRk_empty] at hYeRK
      have := ENat.add_one_pos (n := a)
      grind
    exact aux (M := M ／ Y) (X := X \ Y) (by grind ) (hM.minor (contract_isMinor M Y )) (ht.Contract_mon hY h3 )
      (by simp only [hYeRK, ENat.natCast_lt_succ ]) hYeRK

  sorry
end Thick

section Firm

@[mk_iff]
structure IsFirm (M : Matroid α) (d : ℕ∞) (X : Set (Set α)) : Prop where
  subset : ∀ x ∈ X, x ⊆ M.E
  eRk_union : ∀ X' ⊆ X, X.encard < d * X'.encard → M.eRk (⋃₀X) ≤ M.eRk (⋃₀ X')


end Firm
