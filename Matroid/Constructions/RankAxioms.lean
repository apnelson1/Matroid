import Matroid.ForMathlib.Other
import Matroid.Minor.Rank

open Set

/-- A matroid as defined by the (relative) rank axioms. The constructed
  `RankMatroid` can be then converted into a `Matroid` with `RankMatroid.matroid` -/
structure RankMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The (relative) rank function -/
  (relRank : Set α → Set α → ℕ∞)

  (relRank_le_encard_diff : ∀ A B, relRank A B ≤ (B \ A).encard)
  (relRank_union_le_relRank_inter : ∀ A B, relRank A (A ∪ B) ≤ relRank (A ∩ B) B)
  (relRank_add_cancel : ∀ ⦃A B C⦄, A ⊆ B → B ⊆ C → relRank A C = relRank A B + relRank B C)
  (relRank_diff_eq_zero : ∀ (A B : Set α), A ⊆ B →
    (∀ x ∈ B \ A, relRank A (insert x A) = 0) → relRank A B = 0)

  (relRank_compl_ground_eq : relRank ∅ Eᶜ = 0)
  (relRank_eq_union_right : ∀ A B, relRank A B = relRank A (B ∪ A))

  (Indep : Set α → Prop)
  (indep_maximal : ∀ ⦃X⦄, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  (indep_iff : ∀ ⦃I⦄, Indep I ↔ ∀ x ∈ I, relRank (I \ {x}) I ≠ 0)

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {x : α} {M : RankMatroid α}

@[simp] lemma relRank_self_eq_zero {M : RankMatroid α} : M.relRank A A = 0 := by
  obtain h := M.relRank_le_encard_diff A A
  simpa only [sdiff_self, bot_eq_empty, encard_empty, nonpos_iff_eq_zero] using h

lemma relRank_insert_eq_one_of_ne {M : RankMatroid α} (h : M.relRank A (insert x A) ≠ 0) :
    M.relRank A (insert x A) = 1 := by
  refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 h)
  refine (M.relRank_le_encard_diff _ _).trans ?_
  simp only [← singleton_union, union_diff_right]
  exact (encard_le_card diff_subset).trans_eq <| by simp

lemma relRank_eq_diff_right {M : RankMatroid α} : M.relRank A B = M.relRank A (B \ A) := by
  rw [M.relRank_eq_union_right A (B \ A), diff_union_self, relRank_eq_union_right]

lemma relRank_mono_right (M : RankMatroid α) (hAB : A ⊆ B) :
    M.relRank X A ≤ M.relRank X B := by
  rw [M.relRank_eq_union_right _ A, M.relRank_eq_union_right _ B,
    M.relRank_add_cancel subset_union_right (union_subset_union_left X hAB)]
  simp only [self_le_add_right]

lemma relRank_mono_left (M : RankMatroid α) (hAB : A ⊆ B) :
    M.relRank B X ≤ M.relRank A X := by
  calc
    M.relRank B X = M.relRank B (X ∪ B) := by rw [relRank_eq_union_right]
    _ ≤ M.relRank (A ∪ B) ((A ∪ B) ∪ (A ∪ X)) := by
      rw [← union_union_distrib_left, ← union_assoc, union_eq_self_of_subset_left hAB, union_comm]
    _ ≤ M.relRank ((A ∪ B) ∩ (A ∪ X)) (A ∪ X) := M.relRank_union_le_relRank_inter _ _
    _ = M.relRank (A ∪ (B ∩ X)) (A ∪ X) := by rw [union_inter_distrib_left]
    _ ≤ M.relRank A (A ∪ (B ∩ X)) + M.relRank (A ∪ (B ∩ X)) (A ∪ X) := le_add_self
    _ = M.relRank A (A ∪ X) := by rw [M.relRank_add_cancel subset_union_left <|
      show (A ∪ (B ∩ X)) ⊆ (A ∪ X) from union_subset_union (subset_refl A) inter_subset_right]
    _ = M.relRank A X := by rw [union_comm, ← relRank_eq_union_right]

lemma relRank_eq_zero_aux (M : RankMatroid α) (A B : Set α) : M.relRank A (A ∪ (B \ M.E)) = 0 := by
  rw [relRank_eq_diff_right, union_diff_left, le_antisymm_iff, and_iff_left (by simp),
    ← M.relRank_compl_ground_eq]
  refine (M.relRank_mono_left (empty_subset _)).trans (M.relRank_mono_right ?_)
  exact diff_subset.trans <| diff_subset_compl _ _

@[simp] lemma relRank_inter_ground_left {M : RankMatroid α} (A B : Set α) :
    M.relRank (A ∩ M.E) B = M.relRank A B := by
  have h0 : 0 = M.relRank (A ∩ M.E) A := by simp [← M.relRank_eq_zero_aux (A ∩ M.E) A]
  refine (M.relRank_mono_left inter_subset_left).antisymm' ?_
  rw [M.relRank_eq_union_right (A := A), ← zero_add (M.relRank A _), h0,
    ← M.relRank_add_cancel inter_subset_left subset_union_right]
  apply M.relRank_mono_right subset_union_left

@[simp] lemma relRank_inter_ground_right {M : RankMatroid α} (A B : Set α) :
    M.relRank A (B ∩ M.E) = M.relRank A B := by
  rw [M.relRank_eq_union_right (B := B ∩ M.E), ← add_zero (M.relRank _ (B ∩ M.E ∪ A)),
    ← M.relRank_eq_zero_aux (B ∩ M.E ∪ A) B, union_right_comm, inter_union_diff,
    ← M.relRank_add_cancel subset_union_right, eq_comm, relRank_eq_union_right]
  exact union_subset_union_left _ inter_subset_left

lemma relRank_inter_ground {M : RankMatroid α} : M.relRank (A ∩ M.E) (B ∩ M.E) = M.relRank A B := by
  simp

lemma Indep.subset_ground {M : RankMatroid α} (h : M.Indep I) : I ⊆ M.E := by
  refine fun e heI ↦ by_contra fun heE ↦ ?_
  have h' := M.indep_iff.1 h e heI
  rw [← relRank_inter_ground, ← inter_diff_right_comm, inter_diff_assoc,
    diff_singleton_eq_self heE, relRank_self_eq_zero] at h'
  exact h' rfl

lemma Indep.relRank_diff_singleton {M : RankMatroid α} (h : M.Indep I) (hx : x ∈ I) :
    M.relRank (I \ {x}) I = 1 := by
  simpa [hx, M.indep_iff.1 h] using M.relRank_insert_eq_one_of_ne (A := I \ {x}) (x := x)

lemma Indep.subset {M : RankMatroid α} (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I := by
  refine M.indep_iff.2 fun x hxI ↦ Ne.symm <| LT.lt.ne ?_
  have hr := M.relRank_union_le_relRank_inter (J \ {x}) I
  rwa [diff_union_eq_union_of_subset _ (by simpa), union_eq_self_of_subset_right hIJ,
    hJ.relRank_diff_singleton (hIJ hxI), ENat.one_le_iff_pos,
    ← inter_diff_right_comm, inter_eq_self_of_subset_right hIJ] at hr

lemma Indep.insert_indep_of_relRank_ne_zero (hI : M.Indep I) (hx : M.relRank I (insert x I) ≠ 0) :
    M.Indep (insert x I) := by
  suffices ∀ a ∈ I, ¬M.relRank (insert x I \ {a}) (insert x I) = 0 by
    simpa [M.indep_iff, M.relRank_add_cancel diff_subset (subset_insert _ _), hx]
  intro a haI hr
  have h' := M.relRank_union_le_relRank_inter I (insert x I \ {a})
  have hcon := M.relRank_add_cancel (show I \ {a} ⊆ I from diff_subset) (subset_insert x I)
  have hax : x ≠ a := by rintro rfl; simp [haI] at hx
  rw [relRank_insert_eq_one_of_ne hx, hI.relRank_diff_singleton haI, M.relRank_add_cancel
      (show I \ {a} ⊆ insert x I \ {a} from diff_subset_diff_left (subset_insert _ _)) diff_subset,
      hr, add_zero, ← insert_diff_singleton_comm hax,
      relRank_insert_eq_one_of_ne (by simp [hcon])] at hcon
  norm_num at hcon

lemma Indep.subset_maximal_iff_relRank_zero (hI_indep : M.Indep I) (hI : I ⊆ X) :
    (I ∈ (maximals (· ⊆ ·) {S | M.Indep S ∧ S ⊆ X}) ↔ M.relRank I X = 0) := by
  suffices (∀ ⦃y : Set α⦄, M.Indep y → y ⊆ X → I ⊆ y → I = y) ↔ M.relRank I X = 0 by
    simpa [mem_maximals_iff, hI_indep, hI]
  refine ⟨fun h ↦ ?_, fun h J hJ hJX hIJ ↦ ?_⟩
  · refine M.relRank_diff_eq_zero I X hI fun x hx ↦ by_contra fun hne ↦ ?_
    rw [h (hI_indep.insert_indep_of_relRank_ne_zero hne) (insert_subset hx.1 hI)
      (subset_insert _ _)] at hx
    simp at hx
  obtain (rfl | hssu) := hIJ.eq_or_ssubset; rfl
  obtain ⟨e, he⟩ := exists_of_ssubset hssu
  rw [M.relRank_add_cancel (subset_insert e I) ((insert_subset he.1 hIJ).trans hJX),
    add_eq_zero_iff] at h
  have hcon := (hJ.subset (insert_subset he.1 hIJ)).relRank_diff_singleton (.inl rfl)
  simp [he.2] at hcon
  simp [hcon] at h

@[simps! E Indep] protected def matroid (M : RankMatroid α) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.mk
  (E := M.E)
  (Indep := M.Indep)
  (indep_empty := by simp [M.indep_iff])
  (indep_subset := fun _ _ ↦ Indep.subset)

  (indep_aug := by
    have hrw : {S | M.Indep S} = {S | M.Indep S ∧ S ⊆ M.E} :=
      Set.ext fun I ↦ ⟨fun h ↦ ⟨h, Indep.subset_ground h⟩, fun h ↦ h.1⟩
    intro I B hI hInmax hBmax
    have hB : M.Indep B := hBmax.1
    rw [hrw, hI.subset_maximal_iff_relRank_zero hI.subset_ground] at hInmax
    rw [hrw, hB.subset_maximal_iff_relRank_zero hB.subset_ground] at hBmax
    have hr : ¬ (M.relRank I (I ∪ B) = 0) := by
      refine fun h0 ↦ hInmax ?_
      rw [M.relRank_add_cancel subset_union_left
        (union_subset hI.subset_ground hB.subset_ground), h0]
      simpa [hBmax] using M.relRank_mono_left (show B ⊆ I ∪ B from subset_union_right) (X := M.E)
    replace hr := show ∃ x, I ⊂ x ∧ M.Indep x ∧ x ⊆ I ∪ B by
      simpa [hI, ← hI.subset_maximal_iff_relRank_zero subset_union_left,
        mem_maximals_iff_forall_ssubset_not_mem] using hr
    obtain ⟨J, hIJ, hJ, hJIB⟩ := hr
    obtain ⟨x, hxJ, hxI⟩ := exists_of_ssubset hIJ
    refine ⟨x, ⟨?_, hxI⟩, hJ.subset <| insert_subset hxJ hIJ.subset⟩
    obtain (h | h) := hJIB hxJ; contradiction; assumption)

  (indep_maximal := fun X hX ↦ M.indep_maximal hX)
  (subset_ground := fun I hI ↦ hI.subset_ground)

end RankMatroid

namespace Matroid

variable {α : Type*} {I : Set α}

lemma basis_of_maximal_extension (M : Matroid α) {I X J : Set α} (hX : X ⊆ M.E)
    (h : J ∈ maximals (· ⊆ ·) {I' | M.Indep I' ∧ I ⊆ I' ∧ I' ⊆ X}) : M.Basis J X := by
  unfold Basis; unfold maximals at h ⊢; simp only [mem_setOf_eq, and_imp] at h ⊢
  obtain ⟨⟨hJ_indep, hIJ, hJX⟩, hJ_max⟩ := h
  refine ⟨⟨⟨hJ_indep, hJX⟩, ?_⟩, hX⟩
  intro J' hJ'_indep hJ'X hJJ'
  exact hJ_max hJ'_indep (hIJ.trans hJJ') hJ'X hJJ'

lemma relRank_intro (M : Matroid α) {A B : Set α} (hA : A ⊆ B) (hB : B ⊆ M.E) :
    ∃ I J : Set α, I ⊆ J ∧ M.Basis I A ∧ M.Basis J B ∧ M.relRank A B = (J \ I).encard := by
  obtain ⟨I, hI⟩ := M.maximality A (hA.trans hB) ∅ M.empty_indep (empty_subset A)
  unfold maximals at hI; simp only [empty_subset, true_and, mem_setOf_eq, and_imp] at hI
  have ⟨⟨hI_indep, hI_subset_A⟩, _⟩ := hI
  obtain ⟨J, hJ⟩ := M.maximality B hB I hI_indep (hI_subset_A.trans hA)
  use I; use J
  unfold Basis
  have hIJ : I ⊆ J := hJ.1.2.1
  have hI_basis : M.Basis I A := by
    refine @basis_of_maximal_extension α M ∅ A I (hA.trans hB) ?_
    unfold maximals; simp only [empty_subset, true_and, mem_setOf_eq, and_imp]
    assumption
  have hJ_basis : M.Basis J B := by
    refine M.basis_of_maximal_extension hB hJ
  refine ⟨hIJ, hI_basis, hJ_basis, ?_⟩
  exact Basis.relRank_eq_encard_diff_of_subset_basis hI_basis hJ_basis hIJ

end Matroid

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {M : RankMatroid α} {x : α}

lemma relRank_indeps_eq_encard_diff (M : RankMatroid α) (hA : A ⊆ B) (hB : M.Indep B) :
    M.relRank A B = (B \ A).encard := by
  classical
  suffices aux : ∀ (D : Finset α), Disjoint A D → (D : Set α) ⊆ B → D.card ≤ M.relRank A (A ∪ D) by
    obtain (hfin | hinf) := (B \ A).finite_or_infinite
    · have hc : (B \ A).encard ≤ M.relRank A (A ∪ B) := by
        simpa [disjoint_sdiff_right, diff_subset, ← hfin.encard_eq_coe_toFinset_card]
        using aux hfin.toFinset
      refine (M.relRank_le_encard_diff A B).antisymm ?_
      rwa [relRank_eq_union_right, union_comm]
    rw [hinf.encard_eq, ENat.eq_top_iff_forall_le]
    refine fun m n hAB ↦ ⟨m, rfl, ?_⟩
    obtain ⟨D, hDss, rfl⟩ := hinf.exists_subset_card_eq m
    suffices (D.card : ℕ∞) ≤ n by norm_num at this; assumption
    rw [subset_diff] at hDss
    exact (aux D hDss.2.symm hDss.1).trans
      ((M.relRank_mono_right (union_subset hA hDss.1)).trans_eq hAB)
  intro D hdj hDB
  induction' D using Finset.induction with a D haD IH; simp
  rw [Finset.card_insert_of_not_mem haD]
  specialize IH (hdj.mono_right (by simp)) (subset_trans (by simp) hDB)
  rw [Nat.cast_add, Nat.cast_one, Finset.coe_insert, union_insert, ← union_singleton,
    M.relRank_add_cancel subset_union_left subset_union_left, union_singleton,
    relRank_insert_eq_one_of_ne]
  · exact add_le_add_right IH 1
  have hAuD : a ∉ A ∪ D := by
    simp only [Finset.coe_insert, ← union_singleton, disjoint_union_right,
      disjoint_singleton_right] at hdj; simp [haD, hdj.2]
  nth_rw 1 [← insert_diff_self_of_not_mem hAuD, Indep.relRank_diff_singleton _ (.inl rfl)]
  · simp
  rw [union_comm, ←insert_union]
  exact hB.subset (union_subset (by simpa using hDB) hA)

@[simp] theorem rankMatroid_relRank_eq_matroid_relRank (M : RankMatroid α) :
    M.matroid.relRank A B = M.relRank A B := by
  suffices h : ∀ {A B}, A ⊆ B → B ⊆ M.E → M.relRank A B = M.matroid.relRank A B by
    rw [← relRank_inter_ground, relRank_eq_union_right, ← Matroid.relRank_inter_ground_left,
      ← Matroid.relRank_inter_ground_right, matroid_E, Matroid.relRank_eq_union_right]
    apply (h _ _).symm <;> simp
  intro A B hA hB
  obtain ⟨I, J, hI, ⟨hI_basis_A, _⟩, ⟨hJ_basis_B, _⟩, h⟩ := M.matroid.relRank_intro hA hB
  rw [h]; clear h;
  unfold maximals at hI_basis_A hJ_basis_B;
  simp only [matroid_Indep, mem_setOf_eq, and_imp] at hI_basis_A hJ_basis_B
  obtain ⟨⟨hI_indep, hI_subset⟩, hI_max⟩ := hI_basis_A
  obtain ⟨⟨hJ_indep, hJ_subset⟩, hJ_max⟩ := hJ_basis_B
  rw [<-M.relRank_indeps_eq_encard_diff hI hJ_indep]
  have hIA : M.relRank I A = 0 := by
    rw [<- hI_indep.subset_maximal_iff_relRank_zero hI_subset]
    unfold maximals; simp only [mem_setOf_eq, and_imp]
    exact ⟨⟨hI_indep, hI_subset⟩, hI_max⟩
  have hJB : M.relRank J B = 0 := by
    rw [<- hJ_indep.subset_maximal_iff_relRank_zero hJ_subset]
    unfold maximals; simp only [mem_setOf_eq, and_imp]
    exact ⟨⟨hJ_indep, hJ_subset⟩, hJ_max⟩
  calc
    M.relRank A B
      = M.relRank I A + M.relRank A B := by rw [hIA, zero_add]
    _ = M.relRank I B                 := by rw [M.relRank_add_cancel hI_subset hA]
    _ = M.relRank I J + M.relRank J B := M.relRank_add_cancel hI hJ_subset
    _ = M.relRank I J                 := by rw [hJB, add_zero]

end RankMatroid

/-- A `ℕ`-valued rank function with domain `Finset α`. Can be converted into a (finitary)
matroid using `FinsetRankMatroid.matroid`. -/
structure FinsetRankMatroid (α : Type*) [DecidableEq α] where
  E : Set α
  r : Finset α → ℕ
  r_empty : r ∅ = 0
  r_singleton : ∀ e, r {e} ≤ 1
  r_insert_insert : ∀ X e f, r X + r (insert e (insert f X)) ≤ r (insert e X) + r (insert f X)
  r_singleton_of_not_mem_ground : ∀ e ∉ E, r {e} = 0
namespace FinsetRankMatroid

variable {α : Type*} {X Y I J : Finset α} {e f : α} [DecidableEq α] {M : FinsetRankMatroid α}

lemma r_mono (h : X ⊆ Y) : M.r X ≤ M.r Y := by
  suffices h' : ∀ D, M.r X ≤ M.r (X ∪ D) by
    simpa [Finset.union_eq_right.2 h] using h' Y
  intro D
  induction' D using Finset.induction with e Y _ hY
  · simp
  rw [X.union_insert]
  exact hY.trans (by simpa [Finset.union_comm, Finset.insert_eq]
    using M.r_insert_insert (X ∪ Y) e e)

lemma r_insert_le : M.r (insert e X) ≤ M.r X + M.r {e} := by
  induction' X using Finset.induction with f X _ hX
  · simp [r_empty, M.r_singleton e]
  linarith [M.r_insert_insert X e f]

lemma r_insert_le' : M.r (insert e X) ≤ M.r X + 1 := by
  refine r_insert_le.trans (add_le_add_left (M.r_singleton e) _)

lemma r_le_card : M.r X ≤ X.card := by
  induction' X using Finset.induction with e X heX hX
  · simp [r_empty]
  rw [Finset.card_insert_of_not_mem (by simpa)]
  exact r_insert_le'.trans (add_le_add_right hX 1)

lemma indep_empty : M.r ∅ = (∅ : Finset α).card :=
  le_antisymm M.r_le_card <| by simp

lemma indep_subset (hJ : M.r J = J.card) (hIJ : I ⊆ J) : M.r I = I.card := by
  suffices h' : ∀ I D : Finset α, (I ∪ D).card ≤ M.r (I ∪ D) → M.r I = I.card from
    h' _ J <| by simpa [Finset.union_eq_right.2 hIJ] using hJ.symm.le
  intro I D
  induction' D using Finset.induction with e D heD hD
  · simp only [Finset.union_empty]
    exact fun h ↦ h.antisymm' M.r_le_card
  rw [Finset.union_insert]
  by_cases heI : e ∈ I
  · rwa [Finset.insert_eq_of_mem (by simp [heI])]
  refine fun hle ↦ hD ?_
  replace hle := hle.trans r_insert_le'
  rwa [Finset.card_insert_of_not_mem (by simp [heI, heD]), add_le_add_iff_right] at hle

lemma indep_aug' (hI : M.r I = I.card) (hlt : M.r I < M.r X) :
    ∃ e ∈ X, e ∉ I ∧ M.r (insert e I) = (insert e I).card := by
  by_contra! hcon
  have haux : ∀ S ⊆ X \ I, M.r (I ∪ S) = M.r I := fun S ↦ by
    induction' S using Finset.induction with e S heS ih
    · simp
    simp only [Finset.insert_subset_iff, Finset.mem_sdiff, Finset.union_insert, and_imp]
    intro heX heI hSJI
    induction' S using Finset.induction with f S _ ih'
    · rw [Finset.union_empty, le_antisymm_iff, ← Nat.lt_add_one_iff,
        hI, ← I.card_insert_of_not_mem heI, lt_iff_le_and_ne, and_iff_right M.r_le_card,
        and_iff_right (hcon e heX heI), ← hI, Finset.insert_eq, Finset.union_comm]
      apply M.r_mono Finset.subset_union_left
    specialize ih hSJI
    have hsm := M.r_insert_insert (I ∪ S) e f
    simp only [Finset.mem_insert, not_or] at heS
    have hIS : M.r (I ∪ S) = M.r I := by
      rw [← ih, Finset.union_insert, le_antisymm_iff, Finset.insert_eq, Finset.union_comm {f},
        and_iff_right (M.r_mono Finset.subset_union_left), Finset.union_assoc, S.union_comm,
        ← S.insert_eq, ih]
      apply M.r_mono I.subset_union_left
    rw [Finset.insert_subset_iff] at hSJI
    rw [ih' heS.2 (fun _ ↦ hIS) hSJI.2, ← Finset.union_insert, ih, hIS] at hsm
    exact le_antisymm (by linarith) <|
      M.r_mono <| Finset.subset_union_left.trans (Finset.subset_insert _ _)
  have h' : M.r (X ∪ I) = M.r I := by simpa [X.union_comm] using haux _ Finset.Subset.rfl
  exact hlt.not_le <| le_trans (M.r_mono Finset.subset_union_left) h'.le

lemma indep_aug (hI : M.r I = I.card) (hJ : M.r J = J.card) (hlt : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ M.r (insert e I) = (insert e I).card :=
  indep_aug' hI (by rwa [hI, hJ])

lemma indep_support (hI : M.r I = I.card) : (I : Set α) ⊆ M.E := by
  refine fun e heI ↦ by_contra fun heE ↦ ?_
  have hle := (r_insert_le (X := I.erase e) (e := e)).trans
    (add_le_add_right M.r_le_card _)
  rw [Finset.insert_erase (by simpa using heI), M.r_singleton_of_not_mem_ground e heE,
    add_zero, hI, ← Finset.card_erase_add_one (by simpa using heI)] at hle
  simp at hle

/-- `FinsetRankMatroid α` gives an `Matroid α`; their rank functions agree on finsets.  -/
@[simps! E] protected def matroid (M : FinsetRankMatroid α) : Matroid α :=
   IndepMatroid.matroid <| IndepMatroid.ofFinset M.E (fun I ↦ M.r I = I.card)
    indep_empty (fun _ _ ↦ indep_subset) (fun _ _ ↦ indep_aug) (fun _ ↦ indep_support)

@[simp] protected lemma matroid_indep_iff {I : Finset α} : M.matroid.Indep I ↔ M.r I = I.card := by
  simp [FinsetRankMatroid.matroid]

instance : M.matroid.Finitary := by
  rw [FinsetRankMatroid.matroid, IndepMatroid.ofFinset]
  infer_instance

protected lemma matroid_indep_iff' {I : Set α} :
    M.matroid.Indep I ↔ ∀ J : Finset α, (J : Set α) ⊆ I → M.r J = J.card := by
  simp [FinsetRankMatroid.matroid, IndepMatroid.ofFinset_indep']

@[simp] protected lemma matroid_r_eq (X : Finset α) : M.matroid.r X = M.r X := by
  obtain ⟨I, hI⟩ := M.matroid.exists_basis' X
  obtain ⟨I, rfl⟩ := (X.finite_toSet.subset hI.subset).exists_finset_coe
  rw [← hI.card, ncard_coe_Finset, ← FinsetRankMatroid.matroid_indep_iff.1 hI.indep]
  refine (M.r_mono (by simpa using hI.subset)).antisymm <| le_of_not_lt fun hlt ↦ ?_
  obtain ⟨e, heX, heI, hr⟩ := M.indep_aug' (by simpa using hI.indep) hlt
  have hi : M.matroid.Indep (insert e I) := by
    rwa [← Finset.coe_insert, FinsetRankMatroid.matroid_indep_iff]
  exact heI <| by simpa using hI.mem_of_insert_indep (e := e) (by simpa) hi

@[simp] protected lemma matroid_er_eq (X : Finset α) : M.matroid.er X = M.r X := by
  rw [← Matroid.coe_r_eq_er_of_finite _ (by simp), FinsetRankMatroid.matroid_r_eq]

protected lemma matroid_er_eq_sup (X : Set α) :
    M.matroid.er X = ⨆ Y ∈ {Y : Finset α | (Y : Set α) ⊆ X}, (M.r Y : ℕ∞) := by
  refine le_antisymm ?_ ?_
  set S := {Y : Finset α | (Y : Set α) ⊆ X}
  · obtain ⟨I, hI⟩ := M.matroid.exists_basis' X
    obtain (hIfin | hIinf) := I.finite_or_infinite
    · obtain ⟨I, rfl⟩ := hIfin.exists_finset_coe
      rw [← hI.er, FinsetRankMatroid.matroid_er_eq]
      exact le_biSup (f := fun X ↦ (M.r X : ℕ∞)) hI.subset
    suffices h : ⨆ Y ∈ S, (M.r Y : ℕ∞) = ⊤ by rw [h]; apply le_top
    rw [ENat.eq_top_iff_forall_le]
    intro b
    obtain ⟨J, hJI, rfl⟩ := hIinf.exists_subset_card_eq b
    rw [← FinsetRankMatroid.matroid_indep_iff.1 (hI.indep.subset hJI)]
    apply le_biSup _ (show J ∈ S from hJI.trans hI.subset)
  simp only [mem_setOf_eq, ← FinsetRankMatroid.matroid_er_eq, iSup_le_iff]
  exact fun Y hYX ↦ M.matroid.er_mono hYX

/-- A rank function on `Finset`s that is bounded above by cardinality, monotone and submodular
gives rise to a `FinsetRankMatroid`. -/
def ofFinitaryRankAxioms [DecidableEq α]
    (E : Set α)
    (r : Finset α → ℕ)
    (rank_le_card : ∀ A, r A ≤ A.card)
    (monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B)
    (submodularity : ∀ (A B : Finset α), r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (r_singleton_of_not_mem_ground : ∀ e ∉ E, r {e} = 0) :
    FinsetRankMatroid α :=
  { E := E
    r := r
    r_empty := by simpa using rank_le_card ∅
    r_singleton := fun e ↦ by simpa using rank_le_card {e}
    r_insert_insert := fun X e f ↦ by
      obtain (rfl | hne) := eq_or_ne f e
      · simp [monotonicity (X.subset_insert f)]
      by_cases hfX : f ∈ X
      · rw [X.insert_eq_of_mem hfX, add_comm]
      refine le_of_eq_of_le ?_ (submodularity _ _)
      rw [Finset.inter_comm, X.insert_inter_of_not_mem (by simp [hfX, hne]),
        Finset.inter_eq_left.2 (by simp), add_comm, Finset.insert_union,
        Finset.union_eq_right.2 (by simp)]
    r_singleton_of_not_mem_ground := r_singleton_of_not_mem_ground }

/-- A rank function on `Set`s that is bounded above by `encard` and is monotone and submodular
gives rise to a `FinsetRankMatroid`. -/
def ofFiniteRankAxioms
    (E : Set α)
    (r : Set α → ℕ)
    (rank_le_encard : ∀ A, r A ≤ A.encard)
    (monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B)
    (submodularity : ∀ A B, r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rank_compl_ground : r Eᶜ = 0) :
    FinsetRankMatroid α :=
  ofFinitaryRankAxioms
  (E := E)
  (r := fun X ↦ r X)
  (rank_le_card := fun A ↦ by
    simpa [encard_coe_eq_coe_finsetCard, Nat.cast_le] using rank_le_encard A)
  (monotonicity := fun _ _ h ↦ monotonicity (by simpa))
  (submodularity := fun A B ↦ by simpa using submodularity A B)
  (r_singleton_of_not_mem_ground := fun e he ↦ by
    simpa using (monotonicity (show {e} ⊆ Eᶜ by simpa)).trans_eq rank_compl_ground )



end FinsetRankMatroid
