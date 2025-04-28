--import Matroid.Order.Discrepancy
import Matroid.Rank.Quotient

universe u

open Set
namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {X Y F : Set α} {e f : α}

section Weak

-- Use `Flat.covBy_iff_rk_eq_add_one` instead of this
-- lemma CovBy_rank_one {M : Matroid α} {X Y: Set α} [RankFinite M]
--     (hFX : M.IsFlat X) (hFY : M.IsFlat Y) (hf :M.r Y = M.r X + 1) (hXY : X ⊂ Y ) :
--     X ⋖[M] Y := by

-- lemma CovBy_equal_cont {M₁ : Matroid α} {X Y₁ Y₂: Set α} (hco1 : X ⋖[M₁] Y₁) (hco : X ⋖[M₁] Y₂)
--    (hy : ∃ y, y ∈ Y₁ ∩ Y₂ ∧ y ∉ X ) : Y₁ = Y₂ := by
--   contrapose! hy
--   simp [hco1.inter_eq_of_covby_of_ne hco hy]

theorem Quotient.covBy_of_covBy [RankFinite M₁] (hQ : M₂ ≤q M₁) (hco : X ⋖[M₁] Y)
    (hX2 : M₂.IsFlat X) (hS : M₁.rk X + M₂.rank = M₂.rk X + M₁.rank)
    : ∃ y ∈ Y, Y = M₂.closure (insert y X) := by
  have hYE := hco.subset_ground_right
  have hF1X := hco.isFlat_left
  rw [rank_def, rank_def] at hS
  have hE : M₁.E = M₂.E := (Quotient.ground_eq hQ).symm
  have hfr : RankFinite M₂ := hQ.rankFinite
  have hXY : X ⊆ Y := CovBy.subset hco
  obtain⟨y , hy, _ ⟩:= CovBy.exists_eq_closure_insert hco
  use y
  refine ⟨ mem_of_mem_diff hy , ?_ ⟩
  --rw [hyy.symm]
  have hXy2 : M₂.IsFlat (M₂.closure (insert y X)) := closure_isFlat M₂ (insert y X)
  have hXy1 : M₁.IsFlat (M₂.closure (insert y X)) := Quotient.isFlat_of_isFlat hQ hXy2
  have h1 := hQ.eRelRk_le (M₂.closure (insert y X)) M₂.E
  have h2 := add_le_add_right h1 (M₂.eRk (M₂.closure (insert y X)))
  -- have h1 : M₂.eRelRk (M₂.closure (insert y X)) (M₂.E)
  --≤ M₁.eRelRk (M₂.closure (insert y X)) (M₁.E):= by
  --   have := hQ.eRelRk_le (M₂.closure_subset_ground (insert y X)) hE.symm.subset
  --   rwa [← hE] at this ⊢
  --   sorry
    --exact (TFAE_Quotient hE) hQ
  -- have h2 : M₂.eRelRk (M₂.closure (insert y X)) (M₂.E) + M₂.eRk (M₂.closure (insert y X)) ≤
  --     M₁.eRelRk (M₂.closure (insert y X)) (M₁.E) + M₂.eRk (M₂.closure (insert y X)) := by
  --   exact add_le_add_right h1 (M₂.eRk (M₂.closure (insert y X)))
  have hcE1 : (M₂.closure (insert y X)) ⊆ M₂.E := closure_subset_ground M₂ (insert y X)
  rw [eRelRk_add_eRk_of_subset M₂ hcE1] at h2
  have h3 : M₂.eRk M₂.E + M₁.eRk (M₂.closure (insert y X)) ≤
      M₁.eRelRk (M₂.closure (insert y X)) M₁.E + M₂.eRk (M₂.closure (insert y X)) +
        M₁.eRk (M₂.closure (insert y X)):= by
    convert add_le_add_right h2 _
  rw [hE.symm] at hcE1
  rw [add_assoc, add_comm (M₂.eRk (M₂.closure (insert y X))) (M₁.eRk (M₂.closure (insert y X))),
    ←add_assoc, eRelRk_add_eRk_of_subset M₁ hcE1] at h3
  -- have h4 : M₂.r M₂.E + M₁.r (M₂.closure (insert y X))
  --≤ M₁.r M₁.E + M₂.r (M₂.closure (insert y X)) := by
  simp_rw [← cast_rk_eq] at h3
  norm_cast at h3
  --have hFin1 :  M₁.IsRkFinite
  -- have h4 : M₂.r M₂.E + M₁.r (M₂.closure (insert y X)) ≤ M₁.r M₁.E +
  --M₂.r (M₂.closure (insert y X)) := by
  --   simp_rw [← cast_rk_eq] at h3
  --   norm_cast at h3
  have h5 := Nat.add_le_add_left h3 (M₁.rk X)
  -- have h5 : M₁.r X + (M₂.r M₂.E + M₁.r (M₂.closure (insert y X)))
  --     ≤ M₁.r X + (M₁.r M₁.E + M₂.r (M₂.closure (insert y X))) := Nat.add_le_add_left h3 (M₁.r X)
  rw [←add_assoc, hS, ←add_assoc, add_right_comm, add_right_comm (c := M₂.rk _)] at h5
  --have h6 := Nat.add_le_add_iff_right.mp h5
  -- have h6 : M₂.r X + M₁.r (M₂.closure (insert y X)) + M₁.r M₁.E
  --     ≤ M₁.r X + M₂.r (M₂.closure (insert y X)) + M₁.r M₁.E := by
  --   rwa [add_right_comm, add_right_comm (c := M₂.r _)] at h5
  have h7 : M₂.rk X + M₁.rk (M₂.closure (insert y X))
      ≤ M₁.rk X + M₂.rk (M₂.closure (insert y X)) := Nat.add_le_add_iff_right.mp h5
  have h8 : M₁.rk (M₂.closure (insert y X))
      ≤ M₁.rk X + M₂.rk (M₂.closure (insert y X)) - M₂.rk X  := Nat.le_sub_of_add_le' h7
  --rw[←add_sub_assoc' (M₁.r X) (M₂.r (M₂.closure (insert y X))) (M₂.r X) ] at h8
  have hFin1 := isRkFinite_set M₂ X
  have hXsub : X ⊆ (M₂.closure (insert y X)) :=
    (M₂.subset_closure X hX2.subset_ground).trans <| M₂.closure_subset_closure (subset_insert _ _)
  --have h9 : M₁.r (M₂.closure (insert y X))
    --  ≤ M₁.r X + M₂.eRk (M₂.closure (insert y X)) - M₂.eRk X := by sorry
  --have h10 : M₁.r (M₂.closure (insert y X))
      --≤ M₁.r X + M₂.eRelRk X (M₂.closure (insert y X)):= by sorry
  --rw [IsRkFinite.eRelRk_eq_sub.symm hFin1 hXsub] at h9
  have hclXf : X = M₂.closure X := Eq.symm (IsFlat.closure hX2)
  have hy' : y ∈ M₂.E \ M₂.closure X := by
    rw [← hclXf]
    refine ⟨?_ , not_mem_of_mem_diff hy ⟩
    rw [← hE]
    exact hYE (mem_of_mem_diff hy)
  have hX2E: X ⊆ M₂.E := hX2.subset_ground
  --have hfdsf : M₂.eRk (M₂.closure (insert y X)) - M₂.eRk X = M₂.eRelRk X (M₂.closure (insert y X))
  -- := Eq.symm (IsRkFinite.eRelRk_eq_sub hFin1 hXsub)
  --have hhelp : M₂.eRelRk X (insert y X) = M₂.eRelRk X (M₂.closure (insert y X))
  --:= Eq.symm (eRelRk_closure_right M₂ X (insert y X))
  have hdi : M₂.eRk (M₂.closure (insert y X)) - M₂.eRk X = 1 := by
    rw [← (IsRkFinite.eRelRk_eq_sub hFin1 hXsub), eRelRk_closure_right M₂ X (insert y X)]
    exact eRelRk_insert_eq_one hy' hX2E

  rw [← cast_rk_eq, ← cast_rk_eq, ← ENat.coe_sub, ← Nat.cast_one, Nat.cast_inj] at hdi

  -- This ^^^  is how you convert `hdi` to a statement about `ℕ`,
  -- but it is unlikely you want to use `Nat` subtraction, since
  -- it won't work nicely with `linarith` or `ring` anyway. To exploit `hS`, you will need to
  -- phrase everything in terms of addition, and it probably makes sense to do things this
  -- way in `ℕ∞` in advance.
  have hXaidcl : insert y X ⊆ M₂.E := by
      rw [hE.symm]
      refine insert_subset ?ha fun ⦃a⦄ a_1 ↦ hYE (hXY a_1)
      exact hYE (mem_of_mem_diff hy)
  have hsubcl : insert y X ⊆ M₂.closure (insert y X) :=
    subset_closure_of_subset' M₂ (fun ⦃a⦄ a ↦ a) hXaidcl

  have h9 : M₁.rk (M₂.closure (insert y X))
      ≤ M₁.rk X + (M₂.rk (M₂.closure (insert y X)) - M₂.rk X) :=
    Nat.le_trans h8 (add_tsub_le_assoc )
  rw [hdi] at h9
  have hf : M₁.rk (M₂.closure (insert y X)) = M₁.rk X + 1 := by
    have hhm2 : M₁.rk X + 1 = M₁.rk (insert y X) := by
      have hhel : M₁.rk (insert y X) = M₁.rk (M₁.closure (insert y X)) := Eq.symm (rk_closure_eq M₁)
      have hyEe : y ∈ M₁.E :=  hYE (mem_of_mem_diff hy)
      have hcovy : X ⋖[M₁] M₁.closure (insert y X) := hF1X.covBy_closure_insert
        (not_mem_of_mem_diff hy) (hyEe)
      rw [hhel]
      exact (CovBy.rk_eq_of_isRkFinite hcovy (M₁.isRkFinite_set X)).symm
    exact Nat.le_antisymm h9 (le_of_eq_of_le hhm2 (rk_le_of_subset M₁ hsubcl))

  have hcovcl : X ⋖[M₁] M₂.closure (insert y X) := by
    have hX2 : M₁.IsFlat X := Quotient.isFlat_of_isFlat hQ hX2
    have hcls : X ⊂ M₂.closure (insert y X) := by
      rw [ssubset_iff_of_subset hXsub]
      exact ⟨ y, hsubcl (mem_insert y X) , not_mem_of_mem_diff hy ⟩
    sorry
  sorry
  --   exact CovBy_rank_one hX2 hXy1 hf hcls
  -- apply CovBy_equal_cont hco hcovcl
  -- exact ⟨y,mem_inter (mem_of_mem_diff hy) (hsubcl (mem_insert y X)), not_mem_of_mem_diff hy ⟩

theorem Quotient.forall_superset_k [RankFinite M₁] {k : ℤ} {F F' : Set α} (hQ : M₂ ≤q M₁)
    (hrank : (M₁.rank : ℤ) - M₂.rank = k) (hFF' : F ⊆ F') (hFk : (M₁.rk F : ℤ) - M₂.rk F = k) :
    (M₁.rk F' : ℤ) - M₂.rk F' = k := by
  refine Eq.symm ((fun {x y} ↦ Int.eq_iff_le_and_ge.mpr) ?_)
  refine ⟨ ?_, ?_⟩
  rw[ ←hFk ]
  exact hQ.rank_sub_mono hFF'
  rw [←hrank]
  have hE : M₁.E = M₂.E := Eq.symm hQ.ground_eq
  rw [rank_def M₁, rank_def M₂, ←hE, ← rk_inter_ground (X := F'), ← rk_inter_ground (X := F'),
    hQ.ground_eq]

  exact hQ.rank_sub_mono inter_subset_right

theorem Quotient.forall_superset_isFlat [RankFinite M₁] {k : ℤ} {F F' : Set α} (hQ : M₂ ≤q M₁)
    (hrank : (M₁.rank : ℤ) - M₂.rank = k)
    (hFF' : F ⊆ F') (hF'E : F' ⊆ M₁.E) (hFk : (M₁.rk F : ℤ) - M₂.rk F = k)
    (hF'IsFlat1 : M₁.IsFlat F')
    : M₂.IsFlat F' := by
  by_contra! hcon
  have hE : M₁.E = M₂.E := Eq.symm hQ.ground_eq
  rw [hE] at hF'E
  obtain ⟨e, heEF', hin ⟩ := exists_insert_rk_eq_of_not_isFlat hF'E hcon
  rw [← hE] at hF'E
  rw [← hE] at heEF'
  --have hF'eE : insert e F' ⊆ M₁.E := by exact insert_subset (mem_of_mem_diff heEF') hF'E
  have h1 : M₁.rk (insert e F') - M₂.rk (insert e F') ≤ k := by
    rw[ ←hrank, rank_def M₁, rank_def M₂, ←hE]
    exact hQ.rank_sub_mono (insert_subset (mem_of_mem_diff heEF') hF'E )
  have h2 : k < M₁.rk (insert e F') - M₂.rk (insert e F') := by
    rw [ ←(hQ.forall_superset_k hrank hFF' hFk) ]
    have hme : M₁.rk (F') < M₁.rk (insert e F') := by
      rw [ IsFlat.insert_rk_eq hF'IsFlat1 heEF' ]
      exact lt_add_one (M₁.rk F')
    rw [hin]
    linarith
  linarith


-- theorem Quotient.covBy_of_covBy_gen [RankFinite M₁] (hQ : M₂ ≤q M₁)
--(hsub : X ⊆ Y) (hX2 : M₂.IsFlat X)
--     (hS : M₁.r X + M₂.rank = M₂.r X + M₁.rank) : M₂.IsFlat Y ∧
--( M₁.r Y + M₂.rank = M₂.r Y + M₁.rank ) := by
--   --let k := M₁.r Y - M₁.r X
--   suffices hi : ∀ i : ℕ, M₁.r Y = i + M₁.r X → M₂.IsFlat Y ∧
--( M₁.r Y + M₂.rank = M₂.r Y + M₁.rank )
--   · have hbig : M₁.r X ≤ M₁.r Y := by exact rk_le_of_subset M₁ hsub
--     have hin: ∃ k, M₁.r X + k = M₁.r Y := Nat.le.dest hbig
--     obtain ⟨ k, hk ⟩ := hin
--     apply hi k
--     rw [add_comm] at hk
--     exact id (Eq.symm hk)
--   · intro i hi
--     induction' i with n IH generalizing Y
--     · simp only [zero_add] at hi
--       have h1xf : M₁.IsFlat X := by exact isFlat_of_isFlat hQ hX2
--       have hequal : X = Y := by sorry
--       rw [hequal] at hX2
--       rw [hequal] at hS
--       exact ⟨hX2, hS⟩
--     · sorry

--example {a b c : ℤ} (h : a ≤ b) (h2 : b ≤ c) : a ≤ c := by exact Int.le_trans h h2

  --Int.le_sub_right_of_add_le h
-- eq_sub_of_add_eq h

-- lemma foo {M : Matroid α} {X : Set α} {f : α} (hfX : f ∉ X) (hFlat : M.IsFlat (insert f X)) :
--     (M／ {f}).IsFlat X := by

--   sorry

theorem Quotient.FiniteRank {M₁ M₂ : Matroid α} {X : Set α} [RankFinite M₁] (hQ : M₂ ≤q M₁) :
    M₂.rk X ≤ M₁.rk X := by
  have h1 := hQ.intCast_rank_sub_mono (empty_subset X)
  simp only [rk_empty, CharP.cast_eq_zero, sub_zero, Nat.cast_le] at h1
  exact h1

theorem Numberstuff {a b c d: ℤ} (h1 : d ≤ b) (h2 : a - d ≤ c) : a - b ≤ c := by linarith
  --exact  Nat.eq_sub_of_add_eq' rfl


--lemma numb {a b : ℤ} (hno : ¬ (a = b) ) (hles : a < b) : b < a := by exact?

def Quotient.modularCut_of_k {M₁ M₂ : Matroid α} [RankFinite M₁] (hQ : M₂ ≤q M₁) :
    M₁.ModularCut :=
  ModularCut.ofForallIsModularPairInter M₁
  (U := { F | M₁.IsFlat F ∧ M₂.IsFlat F ∧ hQ.nDiscrepancy F = hQ.nDiscrepancy M₁.E})
  (h_isFlat := fun F hF ↦ hF.1)
  (h_superset := by
    intro F F' hF hF'IsFlat1 hFF'
    have hF'E : F' ⊆ M₁.E := hF'IsFlat1.subset_ground
    refine ⟨ hF'IsFlat1, ?_, ?_⟩
    · apply hQ.forall_superset_isFlat _ hFF' hF'E rfl hF'IsFlat1
      rw [hQ.intCast_rank_sub_rank_eq_nDiscrepancy, hQ.intCast_rk_sub_rk_eq_nDiscrepancy, hF.2.2]
    · refine (hQ.nDiscrepancy_le_of_subset hF'E).antisymm ?_
      rw [← hF.2.2]
      exact hQ.nDiscrepancy_le_of_subset hFF' )
  (h_pair := by
    have := hQ.rankFinite
    rintro F F' ⟨hF₁, hF₂, hFr⟩ ⟨hF'₁, hF'₂, hF'r⟩ hFF'M
    refine ⟨IsFlat.inter hF₁ hF'₁, IsFlat.inter hF₂ hF'₂, ?_ ⟩

    have h1 := M₂.rk_submod F F'
    have h2 := (isModularPair_iff_rk).1 hFF'M
    have hd1 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy F
    have hd2 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy F'
    have hd3 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy (F ∪ F')
    have hd3 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy (F ∩ F')
    have hmono := hQ.nDiscrepancy_le_of_subset (X := F ∪ F') (Y := M₁.E) (by aesop_mat)
    have mono2 := hQ.nDiscrepancy_le_of_subset (X := F ∩ F')
      (inter_subset_left.trans hF₁.subset_ground)
    linarith )

lemma Quotient.exists_extension_quotient_contract_of_rank_lt [RankFinite M₁] {f : α} (hQ : M₂ ≤q M₁)
    (hr : M₂.rank < M₁.rank) (hf : f ∉ M₂.E) :
    ∃ M, M.IsNonloop f ∧ ¬ M.IsColoop f ∧ M ＼ {f} = M₁ ∧ M₂ ≤q M ／ {f} := by
  --have hfin : M₁.RankFinite
  classical
  have hfin : M₂.RankFinite := hQ.rankFinite
  obtain ⟨k, hkpos, hrank⟩ := exists_pos_add_of_lt hr
  use extendBy M₁ f (Quotient.modularCut_of_k hQ)
  have hf1 : f ∉ M₁.E := by rwa [hQ.ground_eq] at hf
  have hfNL : (M₁.extendBy f hQ.modularCut_of_k ).IsNonloop f := by
    by_contra! hcon
    rw[ (M₁.extendBy f (Quotient.modularCut_of_k hQ)).not_isNonloop_iff] at hcon
    have hfcl : f ∈ (M₁.extendBy f (Quotient.modularCut_of_k hQ)).closure (∅) := hcon.mem_closure ∅
    rw [ModularCut.mem_closure_extendBy_iff ] at hfcl
    simp only [mem_empty_iff_false, false_or] at hfcl
    have hcln : M₁.closure ∅ ∉ (Quotient.modularCut_of_k hQ) := by
      have hdef : hQ.nDiscrepancy ∅ < hQ.nDiscrepancy M₁.E := by
        rw [nDiscrepancy_empty hQ]
        by_contra! hzero
        -- have hdisc : hQ.nDiscrepancy M₁.E = hQ.discrepancy M₁.E := by
        --   refine ENat.coe_toNat ?_
        --   exact discrepancy_ne_top hQ M₁.E
        --rw [ hdisc ] at hzero
        --have h1 := eq_of_discrepancy_le_zero hQ ?_
        rw[ congrArg rank (eq_of_discrepancy_le_zero hQ ?_) ] at hr
        exact (lt_self_iff_false M₁.rank).mp hr
        --exact fun
        rw [Nat.le_zero] at hzero
        rw [← cast_nDiscrepancy_eq, hzero]
        simp

      by_contra! hcontra
      have hdis : hQ.nDiscrepancy (M₁.closure ∅) = hQ.nDiscrepancy ∅ := by
        zify
        rw [←intCast_rk_sub_rk_eq_nDiscrepancy, ←intCast_rk_sub_rk_eq_nDiscrepancy]
        simp only [rk_closure_eq, rk_empty, CharP.cast_eq_zero, zero_sub, sub_self, neg_eq_zero,
          Int.natCast_eq_zero]
        have hempty12 : M₂.rk (M₁.closure ∅) ≤ M₁.rk (M₁.closure ∅) := FiniteRank hQ
        have hles : M₁.rk (M₁.closure ∅) = 0 := by simp only [rk_closure_eq, rk_empty]
        rw [hles] at hempty12
        exact Nat.eq_zero_of_le_zero hempty12
      have hco1 : hQ.nDiscrepancy ∅ = hQ.nDiscrepancy M₁.E := by
        have hemp := hcontra.2.2
        rwa[ ←hdis]
      rw[hco1] at hdef
      exact (lt_self_iff_false (hQ.nDiscrepancy M₁.E)).mp hdef
    exact hcln hfcl
    rw [Eq.symm hQ.ground_eq]
    exact hf
  refine ⟨hfNL, ?_, ModularCut.extendBy_deleteElem (Quotient.modularCut_of_k hQ) hf1, ?_ ⟩
  --· exact hfNL
  · by_contra! hcontra
    have hEU : M₁.E ∈ (Quotient.modularCut_of_k hQ) := by
      have hFM1 : M₁.IsFlat M₁.E := ground_isFlat M₁
      have hFM2 : M₂.IsFlat M₁.E :=  by
        rw [←hQ.ground_eq]
        exact ground_isFlat M₂
      change _ ∧ _
      refine ⟨hFM1, hFM2, rfl ⟩
    have hmodE : f ∈ (M₁.extendBy f (Quotient.modularCut_of_k hQ)).closure M₁.E := by
      apply ((Quotient.modularCut_of_k hQ).mem_closure_extendBy_iff hf1).2
      right
      simp only [closure_ground]
      exact hEU
    exact hf1 (hcontra.mem_of_mem_closure hmodE)
  rw [extendBy_contract_eq (Quotient.modularCut_of_k hQ) hf1 ]
  refine ⟨ ?_, ?_ ⟩
  · by_contra! hcon
    obtain ⟨F₀, hF₀2, hF₀bad⟩ := hcon
    have hF₀U : F₀ ∉ (Quotient.modularCut_of_k hQ) := by
      by_contra! hcon0
      have hF₀1 : M₁.IsFlat F₀ := hQ.modularCut_of_k.forall_isFlat F₀ hcon0
      have hFex: F₀ ⊆ (M₁.extendBy f hQ.modularCut_of_k ／ {f}).E := by
        rw [extendBy_contract_eq (Quotient.modularCut_of_k hQ) hf1, projectBy_ground_eq ]
        exact hF₀1.subset_ground
      have hF₀b : (M₁.projectBy hQ.modularCut_of_k).IsFlat F₀ := by
        rw [←extendBy_contract_eq (Quotient.modularCut_of_k hQ) hf1 ]
        apply (isFlat_iff_ssubset_closure_insert_forall hFex).2
        intro e heN
        have hsub : (M₁.extendBy f hQ.modularCut_of_k ／ {f}).closure F₀ ⊆
            (M₁.extendBy f hQ.modularCut_of_k ／ {f}).closure (insert e F₀) :=
          Matroid.closure_subset_closure (M₁.extendBy f hQ.modularCut_of_k ／ {f})
          (subset_insert e F₀)
        by_contra hcontra
        have hcontra1 :(M₁.extendBy f hQ.modularCut_of_k ／ {f}).closure F₀
        = (M₁.extendBy f hQ.modularCut_of_k ／ {f}).closure (insert e F₀):= by
          by_contra hc
          exact hcontra (ssubset_iff_subset_ne.2 (And.symm ⟨hc, hsub⟩))
        have hrnk : (M₁.extendBy f hQ.modularCut_of_k ／ {f}).rk  F₀ =
            (M₁.extendBy f hQ.modularCut_of_k ／ {f}).rk (insert e F₀) := by
          rw [←rk_closure_eq]
          nth_rewrite 2 [←rk_closure_eq]
          exact congrArg (M₁.extendBy f hQ.modularCut_of_k ／ {f}).rk hcontra1
        have hcon1 : (M₁.extendBy f hQ.modularCut_of_k ／ {f}).rk F₀
            < (M₁.extendBy f hQ.modularCut_of_k ／ {f}).rk (insert e F₀) := by
          zify
          have : (M₁.extendBy f hQ.modularCut_of_k).RankFinite :=
            instRankFiniteExtendBy hQ.modularCut_of_k f
          rw [contract_rk_cast_int_eq (M₁.extendBy f hQ.modularCut_of_k),
            contract_rk_cast_int_eq (M₁.extendBy f hQ.modularCut_of_k) ]
          simp only [union_singleton, sub_lt_sub_iff_right, Nat.cast_lt, gt_iff_lt]
          have hfF : f ∉ F₀ := fun a ↦ hf1 (hF₀1.subset_ground a)
          have hfFe : f ∉ insert e F₀ := by
            have hef : f ≠ e := by aesop
            aesop
          have hXSU : M₁.closure F₀ ∈ hQ.modularCut_of_k := by
            rwa [isFlat_iff_closure_eq.mp hF₀1]
          rw [(hQ.modularCut_of_k).extendBy_rk_insert_eq hf1 hfF hXSU]
          have h1 : M₁.rk (insert e F₀)
              ≤ (M₁.extendBy f (hQ.modularCut_of_k)).rk (insert f (insert e F₀)) :=
            (hQ.modularCut_of_k).rank_ge
          have h2 : M₁.rk F₀ < M₁.rk (insert e F₀) := by
            have heFE : e ∈ M₁.E \ F₀ := by
              rwa [extendBy_contract_eq (Quotient.modularCut_of_k hQ) hf1, projectBy_ground_eq ]
              at heN
            rw [hF₀1.rk_insert_eq_add_one (isRkFinite_set M₁ F₀) heFE  ]
            exact lt_add_one (M₁.rk F₀)
          linarith
        rw [hrnk] at hcon1
        simp only [lt_self_iff_false] at hcon1
      exact hF₀bad hF₀b
    --Case 1 ends
    have hF₀1 : M₁.IsFlat F₀ := isFlat_of_isFlat hQ hF₀2
    have hF₀dis : hQ.nDiscrepancy F₀ ≠ hQ.nDiscrepancy M₁.E := by
      by_contra hcond
      have hF₀iU : F₀ ∈ hQ.modularCut_of_k := by
        change _ ∧ _
        refine⟨ hF₀1, hF₀2, hcond ⟩
      exact hF₀U hF₀iU
    have h_covBy : ∃ F' ∈ hQ.modularCut_of_k, F₀ ⋖[M₁] F' := by
      by_contra! hexist
      have hc: (M₁.extendBy f (hQ.modularCut_of_k)).IsFlat (insert f F₀) := by
        apply hQ.modularCut_of_k.insert_isFlat_extendBy_of_not_covBy hf1 hF₀1
        simp only [not_exists, not_and]
        exact hexist
      have hflatpro : ((M₁.extendBy f (hQ.modularCut_of_k)) ／ {f}).IsFlat F₀ := by
        apply (hfNL.contractElem_isFlat_iff).2
        refine ⟨ hc, fun a ↦ hf ((hF₀2.subset_ground) a) ⟩
      rw [extendBy_contract_eq (hQ.modularCut_of_k) hf1 ] at hflatpro
      exact hF₀bad hflatpro
    obtain ⟨ F', hF'U, hF₀F' ⟩ := h_covBy
    have hnotmod : hQ.nDiscrepancy F₀ = hQ.nDiscrepancy M₁.E := by
      have hFF'dis : hQ.nDiscrepancy F₀ = hQ.nDiscrepancy F' := by
        zify
        rw [ ←intCast_rk_sub_rk_eq_nDiscrepancy hQ F₀, ←intCast_rk_sub_rk_eq_nDiscrepancy hQ F']
        have h0 := nDiscrepancy_le_of_subset hQ (hF₀F'.subset)
        zify at h0
        rw [←intCast_rk_sub_rk_eq_nDiscrepancy hQ F₀,
        ←intCast_rk_sub_rk_eq_nDiscrepancy hQ F'] at h0
        have h1 : ( M₁.rk F' : ℤ ) - (M₁.rk F₀ : ℤ ) = 1 := by
          rw [(((hF₀1).covBy_iff_rk_eq_add_one (hF₀F'.2.1)).1 hF₀F').2  ]
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
        have h2 : 1 ≤ (M₂.rk F' : ℤ) - (M₂.rk F₀ : ℤ) := by
          by_contra! hc
          have h3: (M₂.rk F' : ℤ ) = M₂.rk F₀  := by
            have h4 : (M₂.rk F₀ : ℤ ) ≤ M₂.rk F' := by
              simp only [Nat.cast_le]
              exact rk_le_of_subset M₂ (hF₀F'.subset)
            linarith
          have hFF'eq : F₀ = F' := by
            have hle : M₂.rk F' ≤ M₂.rk F₀ := by
              zify
              rw [h3]
            have heee := (hF₀F'.subset_ground_right)
            rw [←hQ.ground_eq] at heee
            exact (hF₀2).eq_of_subset_of_rk_ge (hF₀F'.subset) hle heee
          exact (hF₀F'.ne) hFF'eq
        linarith
      rwa [hF'U.2.2] at hFF'dis
    exact hF₀dis hnotmod
  rw [hQ.ground_eq]
  exact projectBy_ground_eq (Quotient.modularCut_of_k hQ)

    --let s := {F : Set α | M₂.IsFlat F ∧ ¬(M₁.projectBy hQ.modularCut_of_k).IsFlat F}
    --let s := {F : Set α | M₁.IsFlat F ∧ (hQ.nDiscrepancy F ≠ hQ.nDiscrepancy M₁.E)
      --  ∧ (hQ.nDiscrepancy F = hQ.nDiscrepancy F₀)}
    --let s := {F : Set α | M₂.IsFlat F ∧ F ∉ (Quotient.modularCut_of_k hQ)}
    --have hsfin : (M₁.rk '' s).Finite := M₁.range_rk_finite.subset <| image_subset_range ..
    --have hF₀1 : M₁.IsFlat F₀ := by exact isFlat_of_isFlat hQ hF₀2
    --have hsne : s.Nonempty := ⟨F₀, hF₀1, hF₀dis, rfl⟩
    --have hsne : s.Nonempty := ⟨F₀, hF₀2, hF₀U⟩
    --have hsne : s.Nonempty := sorry
    --obtain ⟨F, hFs, hmax⟩ := hsfin.exists_maximal_wrt' _ _ hsne





  -- The discrepancy here is `k`. Now define the extension. The loop conditions stops you
  -- from cheating by choosing trivial modular cuts.




-- theorem Quotient.of_foo_many {M₁ M₂ : Matroid α} {X : Finset α} [RankFinite M₁] (hQ : M₂ ≤q M₁)
--     (hr : M₂.rank + X.card = M₁.rank) (hX₁ : Disjoint (X : Set α) M₁.E) :
--     ∃ (N : Matroid α), (X : Set α) ⊆ N.E ∧ N ＼ (X : Set α) = M₁ ∧ N ／ (X : Set α) = M₂ := by
--   classical
--   have hM₂fin := hQ.rankFinite

--   induction' X using Finset.induction with e Y heY IH generalizing M₁
--   · obtain ⟨B, hB⟩ := M₂.exists_isBase_finset
--     have hB₁ : M₁.IsBase B := by simpa [← hr, hB.finset_card]
--       using (hQ.weakLE.indep_of_indep hB.indep).isBase_of_card
--     simp [hQ.eq_of_isBase_indep hB₁ hB.indep]

--   rw [Finset.card_insert_of_not_mem heY] at hr
--   obtain ⟨-, heM₂⟩ : Disjoint (↑Y) M₂.E ∧ e ∉ M₂.E := by
--     simpa only [Finset.coe_insert, ← union_singleton, ← hQ.ground_eq, disjoint_union_left,
--       disjoint_singleton_left] using hX₁

--   obtain ⟨M, henl, hecl, rfl, hQ'⟩ :=
--     hQ.exists_extension_quotient_contract_of_rank_lt (by linarith) heM₂

--   have hfin' : M.RankFinite
--   · rwa [rankFinite_iff, ← lt_top_iff_ne_top, ← delete_elem_eRank_eq hecl, lt_top_iff_ne_top,
--       ← rankFinite_iff]

--   have hre : (M ／ e).rank + 1 = (M ＼ e).rank
--   · rw [henl.contract_rank_add_one_eq, M.delete_elem_rank_eq hecl]

--   obtain ⟨N, hNss, hN_eq, hNc, hNd⟩ := IH hQ' (by linarith) (hX₁.mono_left (by simp))
--   obtain ⟨P, rfl, rfl⟩ :=
--exists_common_major_of_delete_eq_contractElem (by assumption) hNss hN_eq
--   use P
--   simp only [Finset.coe_insert, ← union_singleton, union_subset_iff, singleton_subset_iff, ←
--     delete_delete, deleteElem, true_and]
--   rw [union_comm, ← contract_contract, ← contractElem, and_iff_left rfl]
--   rw [contractElem, contract_ground, subset_diff] at hNss

--   exact ⟨hNss.1, mem_of_mem_of_subset henl.mem_ground diff_subset⟩


-- theorem Quotient.of_foo {α : Type u} {M₁ M₂ : Matroid α} [RankFinite M₂] (h : M₁ ≤q M₂) :
--   ∃ (β : Type u) (N : Matroid (α ⊕ β)),
--       M₁ = (N ／ (Sum.inr '' univ : Set (α ⊕ β))).comap Sum.inl ∧
--       M₂ = (N ＼ (Sum.inr '' univ : Set (α ⊕ β))).comap Sum.inl := sorry

-- `Sum.inr '' univ : Set (α ⊕ β)` means the set of all the stuff in `α ⊕ β` coming from `β`.

-- Construct a modular cut using `ModularCut.ofForallIsModularPairInter`,
-- which now works for finite-rank matroids.
-- Use `isModularPair_iff_rk` to rewrite `IsModularPair` with the rank definition.

-- lemma something {M₁ M₂ : Matroid α} {X : Finset α} [RankFinite M₂] (h : M₁ ≤q M₂)
--     (hr : M₁.rank + X.card = M₂.rank) (hX₁ : Disjoint (X : Set α) M₁.E) :
