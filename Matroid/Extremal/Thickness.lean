import Matroid.Extremal.Covers
import Matroid.Order.Quotient

set_option linter.style.longLine false

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k d : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' : Matroid α → Set α → Prop}


open Set
namespace Matroid

section Thick

def IsThick (M : Matroid α) (d : ℕ∞) : Prop := d ≤ M.coverNumber Matroid.Nonspanning

lemma IsThick_iff (M : Matroid α) (d : ℕ∞) :
    M.IsThick d ↔ d ≤ M.coverNumber Matroid.Nonspanning := Eq.to_iff rfl

lemma IsThick_iff' (M : Matroid α) (d : ℕ∞) :
    M.IsThick d ↔ ∀ T, M.IsCover Matroid.Nonspanning T → d ≤ T.encard := by
  refine ⟨?_, ?_ ⟩
  · intro h T hT
    sorry
  sorry



def IsThickSet (M : Matroid α) (X : Set α ) (d : ℕ∞) : Prop :=
    (M ↾ X).IsThick d

lemma isThickSet_iff (M : Matroid α) (X : Set α ) (d : ℕ∞) :
    M.IsThickSet X d ↔ d ≤ (M ↾ X).coverNumber Matroid.Nonspanning := by
  sorry

lemma IsThick.of_isQuotient {M N : Matroid α} (hM : M.IsThick d) (hNM : N ≤q M) : N.IsThick d := by

  rw [IsThick_iff] at ⊢ hM
  grw [hM, coverNumber_le_coverNumber (fun _ X ↦ N.Nonspanning X) Matroid.Nonspanning M ?_]

  -- apply coverNumber_mono


lemma IsThick_two (M : Matroid α) [M.Nonempty] : M.IsThick 2 := by
  rw [M.IsThick_iff 2]
  obtain ht | ⟨T, hT, hTe ⟩ := exists_cover M Matroid.Nonspanning
  · rw [ ht]
    simp only [le_top]
  rw [← hTe ]
  by_contra hc
  obtain ⟨X, hX ⟩ := encard_eq_one.mp ((ENat.one_le_iff_ne_zero.mpr (encard_ne_zero.mpr
    ( hT.nonempty ))).antisymm' (Order.le_of_lt_succ (Std.not_le.mp hc ) ) )
  have hc1 : M.Spanning X := by
    rw [← sUnion_singleton (s := X), ←hX, hT.sUnion_eq]
    refine ⟨ by simp only [closure_ground], by simp only [subset_refl] ⟩
  exact Ne.elim (fun a ↦ (hT.pProp X ( by rw [hX]; exact mem_singleton X )).not_spanning  hc1) hTe

lemma IsThick.mono {d' : ℕ∞} (hTd : M.IsThick d ) (hd : d' ≤ d ) : M.IsThick d' := by sorry

lemma IsThick_ground_set (M : Matroid α) (d : ℕ∞) : M.IsThickSet M.E d ↔ M.IsThick d := by sorry

lemma IsThick_set.Minor_mon (hTXd : M.IsThickSet X d) (hNM : N ≤m M ) ( hX : X ⊆ N.E )
    (hXne : X.Nonempty) : N.IsThickSet X d := by

  rw [N.isThickSet_iff X d]
  obtain ⟨C, D, hC, hD, hDC, hrw ⟩ := hNM.exists_contract_indep_delete_coindep
  have hDX : Disjoint D X := by grind
  have hCX : Disjoint C X := by grind
  have hg3 : (C ∩ M.closure X) ⊆ (M ↾ (X ∪ (C ∩ M.closure X))).E := by grind
  have hne : ((M ↾ (X ∪ (C ∩ M.closure X))) ／ (C ∩ M.closure X)).Nonempty := by
    refine (ground_nonempty_iff ((M ↾ (X ∪ C ∩ M.closure X)) ／ (C ∩ M.closure X))).mp ?_
    simp only [contract_ground, restrict_ground_eq, union_diff_right]
    have : (X \ C).Nonempty := by
      rw [ Disjoint.sdiff_eq_right hCX ]
      assumption
    refine nonempty_of_not_subset ?_
    have : ¬X ⊆ C := by
      exact not_subset.mpr this
    grind
  -- Peter?
  have hP : (M ／ C ↾ X) = (M ／ (C ∩ M.closure X) ↾ X) := sorry

  have hCX' : Disjoint (C ∩ M.closure X) X := by grind
  grw [hrw, delete_restrict_eq_restrict (M ／ C) hDX, hP,
    M.contract_restrict_eq_restrict_contract hCX',
    ←NonSpanningNumber_contract hg3 hne, ← NonSpanningNumber_set_closure (inter_subset_right)
    (by grind) ]
  exact (isThick_set_iff M X d).mp hTXd

lemma IsThick.Contract_mon (hTXd : M.IsThick d) (hC : C ⊆ M.E ) (hne : (M ／ C).Nonempty)
    : (M ／ C).IsThick d := by
  grw [IsThick_iff, ←NonSpanningNumber_contract hC hne  ]
  exact (IsThick_iff M d).mp hTXd


--Need Approval
lemma exists_minor_encard (M : Matroid α) (hr : a ≤ M.eRank) :
    ∃ X, X ⊆ M.E ∧ (M ／ X).eRank = a := by
  obtain ⟨B, hB ⟩ := M.exists_isBase
  grw [← hB.encard_eq_eRank] at hr
  have ⟨Y, hYB, hYen ⟩ : ∃ Y, Y ⊆ B ∧ Y.encard = a := exists_subset_encard_eq hr
  use (B \ Y)
  refine ⟨ by grind, ?_ ⟩
  rw [ M.eRank_contract_eq_eRelRk_ground (B \ Y), (isBasis_self_iff_indep.mpr
    (Indep.diff (IsBase.indep hB) Y)).eRelRk_eq_encard_diff_of_subset_isBasis
    (isBasis_ground_iff.mpr hB) (by grind) ]
  simpa [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_self_of_subset_right hYB ]

lemma thick_Bound {M : Matroid α} [M.RankPos] {a b : ℕ} (ha : a ≠ 0) (hb : a ≤ b)
    (hM : NoUniformMinor M (a + 1) (b + 1)) (ht : M.IsThick (Nat.choose b a)) : M.eRank ≤ a := by
  by_contra hc
  simp only [not_le] at hc
  wlog hlt : M.eRank = a + 1 generalizing M with aux
  · obtain ⟨X, hX, hXeRK ⟩ := M.exists_minor_encard (Order.add_one_le_of_lt hc)
    have : (M ／ X).RankPos := by
      refine (eRank_ne_zero_iff (M ／ X)).mp ?_
      simp only [hXeRK, ne_eq, add_eq_zero, ENat.coe_eq_zero, one_ne_zero, and_false,
        not_false_eq_true]
    exact aux (M := M ／ X) (hM.minor (contract_isMinor M X ))
      (ht.Contract_mon hX (rankPos_nonempty)) (by simp only [hXeRK, ENat.natCast_lt_succ]) hXeRK
  sorry
end Thick

section Firm

@[mk_iff]
structure IsFirm (M : Matroid α) (d : ℕ∞) (X : Set (Set α)) : Prop where
  subset : ∀ x ∈ X, x ⊆ M.E
  eRk_union : ∀ X' ⊆ X, X.encard < d * X'.encard → M.eRk (⋃₀ X) ≤ M.eRk (⋃₀ X')


end Firm
