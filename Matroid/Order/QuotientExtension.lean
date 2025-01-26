import Matroid.Order.Discrepancy

universe u

open Set
namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {X Y F : Set α}

section Weak

-- Use `Flat.covBy_iff_rk_eq_add_one` instead of this
-- lemma CovBy_rank_one {M : Matroid α} {X Y: Set α} [FiniteRk M]
--     (hFX : M.Flat X) (hFY : M.Flat Y) (hf :M.r Y = M.r X + 1) (hXY : X ⊂ Y ) :
--     X ⋖[M] Y := by

-- lemma CovBy_equal_cont {M₁ : Matroid α} {X Y₁ Y₂: Set α} (hco1 : X ⋖[M₁] Y₁) (hco : X ⋖[M₁] Y₂)
--    (hy : ∃ y, y ∈ Y₁ ∩ Y₂ ∧ y ∉ X ) : Y₁ = Y₂ := by
--   contrapose! hy
--   simp [hco1.inter_eq_of_covby_of_ne hco hy]

theorem Quotient.covBy_of_covBy [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hco : X ⋖[M₁] Y) (hX2 : M₂.Flat X)
    (hS : M₁.rk X + M₂.rank = M₂.rk X + M₁.rank) : ∃ y ∈ Y, Y = M₂.closure (insert y X) := by
  have hYE := hco.subset_ground_right
  have hF1X := hco.flat_left
  rw [rank_def, rank_def] at hS
  have hE : M₁.E = M₂.E := (Quotient.ground_eq hQ).symm
  have hfr : FiniteRk M₂ := hQ.finiteRk
  have hXY : X ⊆ Y := CovBy.subset hco
  obtain⟨y , hy, _ ⟩:= CovBy.exists_eq_closure_insert hco
  use y
  refine ⟨ mem_of_mem_diff hy , ?_ ⟩
  --rw [hyy.symm]
  have hXy2 : M₂.Flat (M₂.closure (insert y X)) := closure_flat M₂ (insert y X)
  have hXy1 : M₁.Flat (M₂.closure (insert y X)) := Quotient.flat_of_flat hQ hXy2
  have h1 := hQ.relRank_le (M₂.closure (insert y X)) M₂.E
  have h2 := add_le_add_right h1 (M₂.er (M₂.closure (insert y X)))
  -- have h1 : M₂.relRank (M₂.closure (insert y X)) (M₂.E) ≤ M₁.relRank (M₂.closure (insert y X)) (M₁.E):= by
  --   have := hQ.relRank_le (M₂.closure_subset_ground (insert y X)) hE.symm.subset
  --   rwa [← hE] at this ⊢
  --   sorry
    --exact (TFAE_Quotient hE) hQ
  -- have h2 : M₂.relRank (M₂.closure (insert y X)) (M₂.E) + M₂.er (M₂.closure (insert y X)) ≤
  --     M₁.relRank (M₂.closure (insert y X)) (M₁.E) + M₂.er (M₂.closure (insert y X)) := by
  --   exact add_le_add_right h1 (M₂.er (M₂.closure (insert y X)))
  have hcE1 : (M₂.closure (insert y X)) ⊆ M₂.E := closure_subset_ground M₂ (insert y X)
  rw [relRank_add_eRk_of_subset M₂ hcE1] at h2
  have h3 : M₂.er M₂.E + M₁.er (M₂.closure (insert y X)) ≤
      M₁.relRank (M₂.closure (insert y X)) M₁.E + M₂.er (M₂.closure (insert y X)) +
        M₁.er (M₂.closure (insert y X)):= by
    convert add_le_add_right h2 _
  rw [hE.symm] at hcE1
  rw [add_assoc, add_comm (M₂.er (M₂.closure (insert y X))) (M₁.er (M₂.closure (insert y X))),
    ←add_assoc, relRank_add_eRk_of_subset M₁ hcE1] at h3
  -- have h4 : M₂.r M₂.E + M₁.r (M₂.closure (insert y X)) ≤ M₁.r M₁.E + M₂.r (M₂.closure (insert y X)) := by
  simp_rw [← cast_rk_eq] at h3
  norm_cast at h3
  --have hFin1 :  M₁.FinRk
  -- have h4 : M₂.r M₂.E + M₁.r (M₂.closure (insert y X)) ≤ M₁.r M₁.E + M₂.r (M₂.closure (insert y X)) := by
  --   simp_rw [← cast_rk_eq] at h3
  --   norm_cast at h3
  have h5 := Nat.add_le_add_left h3 (M₁.r X)
  -- have h5 : M₁.r X + (M₂.r M₂.E + M₁.r (M₂.closure (insert y X)))
  --     ≤ M₁.r X + (M₁.r M₁.E + M₂.r (M₂.closure (insert y X))) := Nat.add_le_add_left h3 (M₁.r X)
  rw [←add_assoc, hS, ←add_assoc, add_right_comm, add_right_comm (c := M₂.r _)] at h5
  --have h6 := Nat.add_le_add_iff_right.mp h5
  -- have h6 : M₂.r X + M₁.r (M₂.closure (insert y X)) + M₁.r M₁.E
  --     ≤ M₁.r X + M₂.r (M₂.closure (insert y X)) + M₁.r M₁.E := by
  --   rwa [add_right_comm, add_right_comm (c := M₂.r _)] at h5
  have h7 : M₂.r X + M₁.r (M₂.closure (insert y X))
      ≤ M₁.r X + M₂.r (M₂.closure (insert y X)) := Nat.add_le_add_iff_right.mp h5
  have h8 : M₁.r (M₂.closure (insert y X))
      ≤ M₁.r X + M₂.r (M₂.closure (insert y X)) - M₂.r X  := Nat.le_sub_of_add_le' h7
  --rw[←add_sub_assoc' (M₁.r X) (M₂.r (M₂.closure (insert y X))) (M₂.r X) ] at h8
  have hFin1 : M₂.FinRk.X := to_finRk M₂ X
  have hXsub : X ⊆ (M₂.closure (insert y X)) :=
    (M₂.subset_closure X hX2.subset_ground).trans <| M₂.closure_subset_closure (subset_insert _ _)
  --have h9 : M₁.r (M₂.closure (insert y X))
    --  ≤ M₁.r X + M₂.er (M₂.closure (insert y X)) - M₂.er X := by sorry
  --have h10 : M₁.r (M₂.closure (insert y X))
      --≤ M₁.r X + M₂.relRank X (M₂.closure (insert y X)):= by sorry
  --rw [FinRk.relRank_eq_sub.symm hFin1 hXsub] at h9
  have hclXf : X = M₂.closure X := Eq.symm (Flat.closure hX2)
  have hy' : y ∈ M₂.E \ M₂.closure X := by
    rw [← hclXf]
    refine ⟨?_ , not_mem_of_mem_diff hy ⟩
    rw [← hE]
    exact hYE (mem_of_mem_diff hy)
  have hX2E: X ⊆ M₂.E := hX2.subset_ground
  --have hfdsf : M₂.er (M₂.closure (insert y X)) - M₂.er X = M₂.relRank X (M₂.closure (insert y X)) := Eq.symm (FinRk.relRank_eq_sub hFin1 hXsub)
  --have hhelp : M₂.relRank X (insert y X) = M₂.relRank X (M₂.closure (insert y X)) := Eq.symm (relRank_closure_right M₂ X (insert y X))
  have hdi : M₂.er (M₂.closure (insert y X)) - M₂.er X = 1 := by
    rw [← (FinRk.relRank_eq_sub hFin1 hXsub), relRank_closure_right M₂ X (insert y X)]
    exact relRank_insert_eq_one hy' hX2E

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
  have hsubcl : insert y X ⊆ M₂.closure (insert y X) := subset_closure_of_subset' M₂ (fun ⦃a⦄ a ↦ a) hXaidcl

  have h9 : M₁.r (M₂.closure (insert y X)) ≤ M₁.r X + (M₂.r (M₂.closure (insert y X)) - M₂.r X) :=
    Nat.le_trans h8 (add_tsub_le_assoc )
  rw [hdi] at h9
  have hf : M₁.r (M₂.closure (insert y X)) = M₁.r X + 1 := by
    have hhm2 : M₁.r X + 1 = M₁.r (insert y X) := by
      have hhel : M₁.r (insert y X) = M₁.r (M₁.closure (insert y X)) := Eq.symm (rk_closure_eq M₁)
      have hyEe : y ∈ M₁.E :=  hYE (mem_of_mem_diff hy)
      have hcovy : X ⋖[M₁] M₁.closure (insert y X) := hF1X.covBy_closure_insert
        (not_mem_of_mem_diff hy) (hyEe)
      rw [hhel]
      exact (CovBy.rk_eq_of_finRk hcovy (M₁.to_finRk X)).symm
    exact Nat.le_antisymm h9 (le_of_eq_of_le hhm2 (rk_le_of_subset M₁ hsubcl))

  have hcovcl : X ⋖[M₁] M₂.closure (insert y X) := by
    have hX2 : M₁.Flat X := Quotient.flat_of_flat hQ hX2
    have hcls : X ⊂ M₂.closure (insert y X) := by
      rw [ssubset_iff_of_subset hXsub]
      exact ⟨ y, hsubcl (mem_insert y X) , not_mem_of_mem_diff hy ⟩
    sorry
  sorry
  --   exact CovBy_rank_one hX2 hXy1 hf hcls
  -- apply CovBy_equal_cont hco hcovcl
  -- exact ⟨y,mem_inter (mem_of_mem_diff hy) (hsubcl (mem_insert y X)), not_mem_of_mem_diff hy ⟩

theorem Quotient.forall_superset_k [FiniteRk M₁] {k : ℤ} {F F' : Set α} (hQ : M₂ ≤q M₁)
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

theorem Quotient.forall_superset_flat [FiniteRk M₁] {k : ℤ} {F F' : Set α} (hQ : M₂ ≤q M₁)

    (hrank : (M₁.rank : ℤ) - M₂.rank = k)
    (hFF' : F ⊆ F') (hF'E : F' ⊆ M₁.E) (hFk : (M₁.rk F : ℤ) - M₂.rk F = k) (hF'Flat1 : M₁.Flat F')
    : M₂.Flat F' := by
  by_contra! hcon
  have hE : M₁.E = M₂.E := Eq.symm hQ.ground_eq
  rw [hE] at hF'E
  obtain ⟨e, heEF', hin ⟩ := exists_insert_rk_eq_of_not_flat hF'E hcon
  rw [← hE] at hF'E
  rw [← hE] at heEF'
  --have hF'eE : insert e F' ⊆ M₁.E := by exact insert_subset (mem_of_mem_diff heEF') hF'E
  have h1 : M₁.rk (insert e F') - M₂.rk (insert e F') ≤ k := by
    rw[ ←hrank, rank_def M₁, rank_def M₂, ←hE]
    exact hQ.rank_sub_mono (insert_subset (mem_of_mem_diff heEF') hF'E )
  have h2 : k < M₁.rk (insert e F') - M₂.rk (insert e F') := by
    rw [ ←(hQ.forall_superset_k hrank hFF' hFk) ]
    have hme : M₁.rk (F') < M₁.rk (insert e F') := by
      rw [ Flat.insert_rk_eq hF'Flat1 heEF' ]
      exact lt_add_one (M₁.rk F')
    rw [hin]
    linarith
  linarith


-- theorem Quotient.covBy_of_covBy_gen [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hsub : X ⊆ Y) (hX2 : M₂.Flat X)
--     (hS : M₁.r X + M₂.rank = M₂.r X + M₁.rank) : M₂.Flat Y ∧ ( M₁.r Y + M₂.rank = M₂.r Y + M₁.rank ) := by
--   --let k := M₁.r Y - M₁.r X
--   suffices hi : ∀ i : ℕ, M₁.r Y = i + M₁.r X → M₂.Flat Y ∧ ( M₁.r Y + M₂.rank = M₂.r Y + M₁.rank )
--   · have hbig : M₁.r X ≤ M₁.r Y := by exact rk_le_of_subset M₁ hsub
--     have hin: ∃ k, M₁.r X + k = M₁.r Y := Nat.le.dest hbig
--     obtain ⟨ k, hk ⟩ := hin
--     apply hi k
--     rw [add_comm] at hk
--     exact id (Eq.symm hk)
--   · intro i hi
--     induction' i with n IH generalizing Y
--     · simp only [zero_add] at hi
--       have h1xf : M₁.Flat X := by exact flat_of_flat hQ hX2
--       have hequal : X = Y := by sorry
--       rw [hequal] at hX2
--       rw [hequal] at hS
--       exact ⟨hX2, hS⟩
--     · sorry

example {a b c : ℤ} (h : a ≤ b) (h2 : b ≤ c) : a ≤ c := by exact Int.le_trans h h2

  --Int.le_sub_right_of_add_le h
-- eq_sub_of_add_eq h

theorem Quotient.FiniteRank {M₁ M₂ : Matroid α} {X : Set α} [FiniteRk M₁] (hQ : M₂ ≤q M₁) :
    M₂.rk X ≤ M₁.rk X := by
  have h1 := hQ.intCast_rank_sub_mono (empty_subset X)
  simp only [rk_empty, CharP.cast_eq_zero, sub_zero, Nat.cast_le] at h1
  exact h1

theorem Numberstuff {a b c d: ℤ} (h1 : d ≤ b) (h2 : a - d ≤ c) : a - b ≤ c := by linarith
  --exact  Nat.eq_sub_of_add_eq' rfl

--theorem ayuda3 {M : Matroid α} (hE : X ⊆ M.E ) (hE1 : Y ⊆ M.E ) : M.r (X ∩ Y) + M.r ( X ∪ Y) ≤ M.r X + M.r Y :=
  --by sorry

def Quotient.modularCut_of_k {M₁ M₂ : Matroid α} [FiniteRk M₁] (hQ : M₂ ≤q M₁) :
    M₁.ModularCut :=
  ModularCut.ofForallModularPairInter M₁
  (U := { F | M₁.Flat F ∧ M₂.Flat F ∧ hQ.nDiscrepancy F = hQ.nDiscrepancy M₁.E})
  (h_flat := fun F hF ↦ hF.1)
  (h_superset := by
    intro F F' hF hF'Flat1 hFF'
    have hF'E : F' ⊆ M₁.E := hF'Flat1.subset_ground
    refine ⟨ hF'Flat1, ?_, ?_⟩
    · apply hQ.forall_superset_flat _ hFF' hF'E rfl hF'Flat1
      rw [hQ.intCast_rank_sub_rank_eq_nDiscrepancy, hQ.intCast_rk_sub_rk_eq_nDiscrepancy, hF.2.2]
    · refine (hQ.nDiscrepancy_le_of_subset hF'E).antisymm ?_
      rw [← hF.2.2]
      exact hQ.nDiscrepancy_le_of_subset hFF' )
  (h_pair := by
    have := hQ.finiteRk
    rintro F F' ⟨hF₁, hF₂, hFr⟩ ⟨hF'₁, hF'₂, hF'r⟩ hFF'M
    refine ⟨Flat.inter hF₁ hF'₁, Flat.inter hF₂ hF'₂, ?_ ⟩

    have h1 := M₂.rk_submod F F'
    have h2 := (modularPair_iff_rk).1 hFF'M
    have hd1 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy F
    have hd2 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy F'
    have hd3 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy (F ∪ F')
    have hd3 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy (F ∩ F')
    have hmono := hQ.nDiscrepancy_le_of_subset (X := F ∪ F') (Y := M₁.E) (by aesop_mat)
    have mono2 := hQ.nDiscrepancy_le_of_subset (X := F ∩ F')
      (inter_subset_left.trans hF₁.subset_ground)
    linarith )




lemma Quotient.exists_extension_quotient_contract_of_rank_lt {f : α} (hQ : M₂ ≤q M₁)
    (hr : M₂.rank < M₁.rank) (hf : f ∉ M₂.E) :
    ∃ M, M.Nonloop f ∧ ¬ M.Coloop f ∧ M ＼ f = M₁ ∧ M₂ ≤q M ／ f := by
  have hfin : M₁.FiniteRk
  · rw [finiteRk_iff]
    intro h
    simp [rank, h] at hr
  obtain ⟨k, hkpos, hrank⟩ := exists_pos_add_of_lt hr
  -- The discrepancy here is `k`. Now define the extension. The loop conditions stops you
  -- from cheating by choosing trivial modular cuts.
  sorry



theorem Quotient.of_foo_many {M₁ M₂ : Matroid α} {X : Finset α} [FiniteRk M₁] (hQ : M₂ ≤q M₁)
    (hr : M₂.rank + X.card = M₁.rank) (hX₁ : Disjoint (X : Set α) M₁.E) :
    ∃ (N : Matroid α), (X : Set α) ⊆ N.E ∧ N ＼ (X : Set α) = M₁ ∧ N ／ (X : Set α) = M₂ := by
  classical
  have hM₂fin := hQ.finiteRk

  induction' X using Finset.induction with e Y heY IH generalizing M₁
  · obtain ⟨B, hB⟩ := M₂.exists_base_finset
    have hB₁ : M₁.Base B := by simpa [← hr, hB.finset_card]
      using (hQ.weakLE.indep_of_indep hB.indep).base_of_card
    simp [hQ.eq_of_base_indep hB₁ hB.indep]

  rw [Finset.card_insert_of_not_mem heY] at hr
  obtain ⟨-, heM₂⟩ : Disjoint (↑Y) M₂.E ∧ e ∉ M₂.E := by
    simpa only [Finset.coe_insert, ← union_singleton, ← hQ.ground_eq, disjoint_union_left,
      disjoint_singleton_left] using hX₁

  obtain ⟨M, henl, hecl, rfl, hQ'⟩ :=
    hQ.exists_extension_quotient_contract_of_rank_lt (by linarith) heM₂

  have hfin' : M.FiniteRk
  · rwa [finiteRk_iff, ← lt_top_iff_ne_top, ← delete_elem_eRank_eq hecl, lt_top_iff_ne_top,
      ← finiteRk_iff]

  have hre : (M ／ e).rank + 1 = (M ＼ e).rank
  · rw [henl.contract_rank_add_one_eq, M.delete_elem_rank_eq hecl]

  obtain ⟨N, hNss, hN_eq, hNc, hNd⟩ := IH hQ' (by linarith) (hX₁.mono_left (by simp))
  obtain ⟨P, rfl, rfl⟩ := exists_common_major_of_delete_eq_contractElem (by assumption) hNss hN_eq
  use P
  simp only [Finset.coe_insert, ← union_singleton, union_subset_iff, singleton_subset_iff, ←
    delete_delete, deleteElem, true_and]
  rw [union_comm, ← contract_contract, ← contract_elem, and_iff_left rfl]
  rw [contract_elem, contract_ground, subset_diff] at hNss

  exact ⟨hNss.1, mem_of_mem_of_subset henl.mem_ground diff_subset⟩


theorem Quotient.of_foo {α : Type u} {M₁ M₂ : Matroid α} [FiniteRk M₂] (h : M₁ ≤q M₂) :
  ∃ (β : Type u) (N : Matroid (α ⊕ β)),
      M₁ = (N ／ (Sum.inr '' univ : Set (α ⊕ β))).comap Sum.inl ∧
      M₂ = (N ＼ (Sum.inr '' univ : Set (α ⊕ β))).comap Sum.inl := sorry

-- `Sum.inr '' univ : Set (α ⊕ β)` means the set of all the stuff in `α ⊕ β` coming from `β`.

-- Construct a modular cut using `ModularCut.ofForallModularPairInter`,
-- which now works for finite-rank matroids.
-- Use `modularPair_iff_rk` to rewrite `ModularPair` with the rank definition.

-- lemma something {M₁ M₂ : Matroid α} {X : Finset α} [FiniteRk M₂] (h : M₁ ≤q M₂)
--     (hr : M₁.rank + X.card = M₂.rank) (hX₁ : Disjoint (X : Set α) M₁.E) :
