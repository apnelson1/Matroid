import Matroid.Connectivity.Minor

variable {α ι : Type*} {M : Matroid α} {A B C X Y : Set α} {e f : α}

open Set Function

namespace Matroid

lemma exists_big_skew (hB : M.IsBase B) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I ⊆ B, I.encard = M.eRk X ∧ M.Skew (B \ I) X := by
  obtain ⟨IX, hIX⟩ := M.exists_isBasis X
  obtain ⟨B', hB', hIXB', hB'IX⟩ :=  hIX.indep.exists_isBase_subset_union_isBase hB
  refine ⟨B \ (B' \ IX), diff_subset, ?_, ?_⟩
  · rw [hIX.eRk_eq_encard, diff_diff_right,
      encard_union_eq (disjoint_sdiff_left.mono_right (inter_subset_right.trans hIXB')),
      hB.encard_diff_comm hB', ← encard_union_eq (disjoint_sdiff_left.mono_right inter_subset_left)]
    congr
    tauto_set
  rw [diff_diff_right, skew_iff_closure_skew_right, ← hIX.closure_eq_closure,
    ← skew_iff_closure_skew_right]
  simp only [sdiff_self, bot_eq_empty, empty_union]
  exact (hB'.indep.subset_skew_diff hIXB').symm.mono_left inter_subset_right

-- lemma eLocalConn_keep (hB : M.IsBase B) (X Y : Set α) :
--     ∃ I ⊆ B, I.encard ≤ M.eLocalConn X Y ∧
--     ∀ J ⊆ B, Disjoint J I → (M ／ J).eLocalConn X Y = M.eLocalConn X Y := by
--   wlog h_ind : M.Indep X ∧ M.Indep Y generalizing X Y with aux
--   · obtain ⟨IX, hIX⟩ := M.exists_isBasis' X
--     obtain ⟨IY, hIY⟩ := M.exists_isBasis' Y
--     simp_rw [← M.eLocalConn_closure_closure X Y, ← hIX.closure_eq_closure,
-- ← hIY.closure_eq_closure,
--       ← (M ／ _).eLocalConn_closure_closure X Y, contract_closure_eq,
--       ← closure_union_congr_left hIX.closure_eq_closure,
--       ← closure_union_congr_left hIY.closure_eq_closure, ← contract_closure_eq,
--       eLocalConn_closure_closure]
--     exact aux _ _ ⟨hIX.indep, hIY.indep⟩
--   obtain ⟨hX, hY⟩ := h_ind
--   obtain ⟨K, hK, hXK⟩ := hX.subset_isBasis_of_subset (show X ⊆ X ∪ Y from subset_union_left)

--   sorry

-- lemma foo {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (S₁ : ι₁ → Set α) (S₂ : ι₂ → Set α)
--     (h_lt : ∑ i, M.eRk (S₁ i) < ∑ i, M.eRk (S₂ i)) :
--     ∃ (N : Matroid α), (∀ i, (S₁ i ∩ N.E).Finite) ∧ (∀ i, (S₂ i ∩ N.E).Finite)
--       ∧ ∑ i, N.eRk (S₁ i) < ∑ i, N.eRk (S₂ i) := by
--   obtain (⟨i, hi⟩ | forall_fin) := exists_or_forall_not (fun i ↦ M.eRk (S₂ i) = ⊤)
--   · obtain ⟨I, hI⟩ := M.exists_isBasis' (S₂ i)
--     rw [hI.eRk_eq_encard, encard_eq_top_iff] at hi
--     obtain ⟨I₀, hI₀, hlt', hfin⟩ := hi.exists_finite_subset_encard_gt' (h_lt.trans_le le_top).ne
--     refine ⟨M ↾ I₀, fun _ ↦ hfin.inter_of_right _, fun _ ↦ hfin.inter_of_right _, ?_⟩
--     simp only [restrict_eRk_eq']
--     grw [Finset.sum_le_sum (fun i _ ↦ M.eRk_mono inter_subset_left),
--       ← Finset.single_le_sum (a := i) (by simp) (by simp),
--       inter_eq_self_of_subset_right (hI₀.trans hI.subset), (hI.indep.subset hI₀).eRk_eq_encard]
--     assumption
--   simp only [eRk_eq_top_iff, not_not] at forall_fin
--   sorry
    -- have hfin := h_lt.trans_le <| le_top (a := ∑ i, M.eRk (S₂ i))
    -- -- have h_lt := hi ▸ (h_lt.trans_le <| le_top (a := ∑ i, M.eRk (S₂ i)))
    -- grw [← ENat.add_one_le_iff (by intro h; simp [h] at h_lt),
    --   le_top (a := ∑ i, M.eRk (S₂ i)), hi.encard_eq] at h_lt


    -- obtain ⟨J, hJI, ⟩ := exists_subset_encard_eq ()


    -- have h' : B' \ B = IX \ B := by
    --   tauto_set
    -- nth_rw 2 [← diff_union_inter IX B


section Submod

lemma foo0 {J : Set α} {K : ι → Set α} (hdj : Pairwise (Disjoint on K))
    (hK : ∀ i, M.Indep (K i)) (hJK : M.IsBasis J (⋃ i, K i)) :
    -- (hI : ∀ i, (M.project ((⋃ j, K j) \ K i)).IsBasis (I i) (J i)) :
    (ENat.card ι - 1) * M.multiConn K = ∑' i, (M.project ((⋃ j, K j) \ K i)).nullity (J ∩ K i) := by
  obtain (hι | hι) := isEmpty_or_nonempty ι
  · simp
  have hrw (i : ι) : (M.project ((⋃ j, K j) \ K i)).nullity (J ∩ K i) = 0 := by
    rw [← (hJK.indep.inter_right _).eLocalConn_eq_nullity_project_left]
    -- (hJK : ∀ i, J i ⊆ K i)
    -- (hI : M.IsBasis (⋃ i, J i) (⋃ i, K i))
    -- (hJ : ∀ j, (M.project ((⋃ i, (K i)) \ K j)).IsBasis (I j) (J j)) :
    -- M.multiConn X = (⋃ i, (J i \ I i)).encard := by

--   sorry
-- -- (hI : ∀ i, M.isBasis (I i) (X i)) :


-- lemma foo2 {I I₀ J J₀ : Set α} (hIJ : M.IsBasis (I ∪ J) (X ∪ Y)) (hIX : I ⊆ X) (hJY : J ⊆ Y)
--     (hdj : Disjoint X Y) :

lemma foo1 {I : Set α} (h : M.IsBasis I (X ∪ Y)) (hdj : Disjoint X Y) :
    ∃ I₀ ⊆ I, I₀.encard = M.eLocalConn X Y ∧
      (M.project (I \ I₀)).eLocalConn X Y = M.eLocalConn X Y := by

  obtain ⟨JX, hJX, hIJX⟩ := (h.indep.inter_right X).subset_isBasis'_of_subset inter_subset_right
  obtain ⟨JY, hJY, hIJY⟩ := (h.indep.inter_right Y).subset_isBasis'_of_subset inter_subset_right
  obtain ⟨IX, hIX⟩ := (M.project JY).exists_isBasis (I ∩ X)
    (inter_subset_left.trans h.indep.subset_ground)
  obtain ⟨IY, hIY⟩ := (M.project JX).exists_isBasis (I ∩ Y)
    (inter_subset_left.trans h.indep.subset_ground)
  have hIX' := hJY.indep.project_isBasis_iff.1 hIX
  have hIY' := hJX.indep.project_isBasis_iff.1 hIY

  -- have hJss := hJX.subset
  -- have hIss := hIX.subset
  -- have hJXss := hJX.subset
  -- have hJYss := hJY.subset
  -- have hrw : M.eLocalConn X Y = 0 := by
  --   rw [eLocalConn, ← M.multiConn_project_add_of_subset (C := fun b ↦ bif b then IX else IY),
  --     iUnion_bool, cond_true, cond_false, ← eLocalConn]
  refine ⟨I \ (IX ∪ IY), diff_subset, ?_, ?_⟩
  · rw [hJX.eLocalConn_eq_of_disjoint hJY hdj]
    have hb' : M.IsBasis I (JX ∪ JY) := by
      refine h.isBasis_subset ?_ (by grw [hJX.subset, hJY.subset])
      grw [← inter_eq_self_of_subset_left h.subset, inter_union_distrib_left, hIJX, hIJY]
    rw [hb'.nullity_eq]
    have hrw : (I \ (IX ∪ IY)) = ((I ∩ X) \ IX) ∪ ((I ∩ Y) \ IY) := by
      have hss := h.subset
      -- nth_rw 1 [← inter_eq_self_of_subset_left h.subset, inter_union_distrib_left]
      tauto_set
    rw [hrw, encard_union_eq (by tauto_set), ← hIX.nullity_eq, ← hIY.nullity_eq,
      hJY.indep.nullity_project_of_disjoint, union_comm,
      ← (h.indep.inter_right _).nullity_project_of_disjoint,
      hJX.indep.nullity_project_of_disjoint, union_comm,
      ← (h.indep.inter_right _).nullity_project_of_disjoint,
      union_diff_distrib, encard_union_eq, ← diff_inter_self_eq_diff,
       ← IsBasis.nullity_eq (M := M.project (I ∩ Y)),
       ← diff_inter_self_eq_diff, ← IsBasis.nullity_eq (M := M.project (I ∩ X)), add_comm]







  rw [eLocalConn, eLocalConn, diff_diff_cancel_left
    (by grw [hIX.subset, hIY.subset, inter_subset_left, inter_subset_left, union_self]),
    ← M.multiConn_project_add_of_subset (C := fun b ↦ bif b then IX else IY), iUnion_bool,
    cond_true, cond_false, ENat.eq_add_left_iff, ENat.tsum_eq_zero, Bool.forall_bool,
    cond_false, cond_true, cond_false, cond_true, ← eLocalConn_closure_closure,
    ← project_closure_eq_project_closure_union, project_closure,
    ← closure_union_congr_left hJY.closure_eq_closure, ← project_closure,
    eLocalConn_closure_closure]



  simp [hIX.subset.trans inter_subset_right, hIY.subset.trans inter_subset_right,
    pairwise_disjoint_on_bool] at this


  -- obtain ⟨IX, hIX⟩ := (M.project Y).exists_isBasis' X
  -- refine ⟨(I \ IX) \ IY, diff_subset.trans diff_subset, ?_, ?_⟩
  -- have :=
  -- rw [isBasis'_iff_isBasis_inter_ground, project_isBasis_iff, project_ground] at hIX hIY

lemma IsBase.aux {B : Set α} (hB : M.IsBase B) (X : Set α) :
    ∃ I ⊆ B, I.encard ≤ M.eConn X ∧ ∀ J ⊆ B \ I, (M ／ J).eConn X = M.eConn X := by
  obtain ⟨IX, hIX, hBIX⟩ := (hB.indep.inter_left X).subset_isBasis'_of_subset inter_subset_left
  obtain ⟨B', hB', hIXB', hB'IX⟩ := hIX.indep.exists_isBase_subset_union_isBase hB



  simp [eConn_eq_eLocalConn', ← eLocalConn_project_eq_eLocalConn_contract]



lemma aux_subset (M : Matroid α) (X : Set α) (k : ℕ∞) (hk : k ≤ M.eConn X) :
    ∃ N : Matroid α, N ≤ M ∧ N.eConn X = k := sorry

lemma eConn_submod (M : Matroid α) (X Y : Set α) :
    M.eConn (X ∪ Y) + M.eConn (X ∩ Y) ≤ M.eConn X + M.eConn Y := by
  wlog hu : M.eConn (X ∪ Y) < ⊤ generalizing M with aux
  · by_contra! hcon
    simp only [not_lt, top_le_iff] at hu
    obtain ⟨N, hNM, hconn⟩ := M.aux_subset (X ∪ Y) (M.eConn X + M.eConn Y + 1) (by simp [hu])
    have hXY : M.eConn X + M.eConn Y < ⊤ := hcon.trans_le le_top
    specialize aux N
    grw [← le_self_add, hconn, hNM.eConn_le, hNM.eConn_le, ENat.add_one_le_iff hXY.ne,
      ENat.add_lt_top] at aux
    simp [hXY] at aux
  wlog hi : M.eConn (X ∩ Y) < ⊤ generalizing M with aux
  · by_contra! hcon
    simp only [not_lt, top_le_iff] at hi
    obtain ⟨N, hNM, hconn⟩ := M.aux_subset (X ∩ Y) (M.eConn X + M.eConn Y + 1) (by simp [hi])
    have hXY : M.eConn X + M.eConn Y < ⊤ := hcon.trans_le le_top
    specialize aux N ((hNM.eConn_le _).trans_lt hu)
    grw [← le_add_self, hconn, hNM.eConn_le, hNM.eConn_le, ENat.add_one_le_iff hXY.ne,
      ENat.add_lt_top] at aux
    simp [hXY] at aux
  by_contra! hlt
  have hX : M.eConn X < ⊤ := by
    grw [← le_self_add] at hlt
    exact hlt.trans_le le_top
  have hY : M.eConn Y < ⊤ := by
    grw [← le_add_self] at hlt
    exact hlt.trans_le le_top

  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨IX, hIXB, hIXcard, hIX⟩ := hB.aux X
  obtain ⟨IY, hIYB, hIYcard, hIY⟩ := hB.aux Y
  obtain ⟨Ii, hIiB, hIiBcard, hIi⟩ := hB.aux (X ∩ Y)
  obtain ⟨Iu, hIuB, hIuBcard, hIu⟩ := hB.aux (X ∪ Y)

  set N := M ／ (B \ (IX ∪ IY ∪ Iu ∪ Ii)) with hN
  have hbas : N.IsBase (IX ∪ IY ∪ Iu ∪ Ii) := by
    rw [hN, (hB.indep.subset diff_subset).contract_isBase_iff, union_diff_cancel
      (by simp [hIXB, hIYB, hIuB, hIiB])]
    exact ⟨hB, disjoint_sdiff_right⟩

  have hufin := encard_lt_top_iff.1 <| hIuBcard.trans_lt hu
  have hifin := encard_lt_top_iff.1 <| hIiBcard.trans_lt hi
  have hIXfin := encard_lt_top_iff.1 <| hIXcard.trans_lt hX
  have hIYfin := encard_lt_top_iff.1 <| hIYcard.trans_lt hY
  have hfin : RankFinite N := hbas.rankFinite_of_finite <| by simp [hIXfin, hIYfin, hifin, hufin]

  have hcon := N.conn_submod X Y
  rw [← Nat.cast_le (α := ℕ∞), Nat.cast_add, Nat.cast_add, cast_conn_eq,
    cast_conn_eq, cast_conn_eq, cast_conn_eq, hN, hIi _ (by tauto_set), hIu _ (by tauto_set),
    hIX _ (by tauto_set), hIY _ (by tauto_set), add_comm] at hcon
  exact hlt.not_ge hcon







end Submod
