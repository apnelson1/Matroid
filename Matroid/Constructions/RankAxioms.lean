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
  -- A simpler version of the axiom from Bruhn et al.
  (relRank_diff_eq_zero : ∀ (A B : Set α), A ⊆ B →
    (∀ x ∈ B \ A, relRank A (insert x A) = 0) → relRank A B = 0)

  (relRank_compl_ground_eq : relRank ∅ Eᶜ = 0)
  (relRank_eq_union_right : ∀ A B, relRank A B = relRank A (B ∪ A))

  (Indep : Set α → Prop)
  (indep_maximal : ∀ ⦃X⦄, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  (indep_iff' : ∀ ⦃I⦄, Indep I ↔ I ⊆ E ∧ ∀ x ∈ I, 0 < relRank (I \ {x}) I)

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {x : α} {M : RankMatroid α}

@[simp] lemma relRank_self_eq_zero {M : RankMatroid α} : M.relRank A A = 0 := by
  obtain h := M.relRank_le_encard_diff A A
  simpa only [sdiff_self, bot_eq_empty, encard_empty, nonpos_iff_eq_zero] using h

lemma Indep.subset_ground {M : RankMatroid α} (h : M.Indep I) : I ⊆ M.E :=
  (M.indep_iff'.mp h).left

lemma relRank_insert_eq_one_of_ne {M : RankMatroid α} (h : M.relRank A (insert x A) ≠ 0) :
    M.relRank A (insert x A) = 1 := by
  refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 h)
  refine (M.relRank_le_encard_diff _ _).trans ?_
  simp only [← singleton_union, union_diff_right]
  exact (encard_le_card diff_subset).trans_eq <| by simp

lemma relRank_diff_singleton_eq_one_of_ne {M : RankMatroid α} (h : M.relRank (A \ {x}) A ≠ 0) :
    M.relRank (A \ {x}) A = 1 := by
  by_cases hxA : x ∈ A
  · simpa [h, hxA] using M.relRank_insert_eq_one_of_ne (A := A \ {x}) (x := x)
  simp [hxA, relRank_self_eq_zero] at h

lemma Indep.relRank_diff_singleton {M : RankMatroid α} (h : M.Indep I) (hx : x ∈ I) :
    M.relRank (I \ {x}) I = 1 :=
  relRank_diff_singleton_eq_one_of_ne ((M.indep_iff'.1 h).2 x hx).ne.symm

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
      rw [union_eq_right.mpr hAB, <-Set.union_assoc, union_eq_left.mpr hAB, union_comm]
    _ ≤ M.relRank ((A ∪ B) ∩ (A ∪ X)) (A ∪ X) := M.relRank_union_le_relRank_inter (A ∪ B) (A ∪ X)
    _ = M.relRank (A ∪ (B ∩ X)) (A ∪ X) := by rw [union_inter_distrib_left]
    _ ≤ M.relRank A (A ∪ (B ∩ X)) + M.relRank (A ∪ (B ∩ X)) (A ∪ X) := le_add_self
    _ = M.relRank A (A ∪ X) := by
      have h : (A ∪ (B ∩ X)) ⊆ (A ∪ X) :=
        union_subset_union (subset_refl A) inter_subset_right
      rw [M.relRank_add_cancel subset_union_left h]
    _ = M.relRank A X := by rw [union_comm, <-relRank_eq_union_right]

lemma relRank_inter_ground {M : RankMatroid α} : M.relRank (A ∩ M.E) (B ∩ M.E) = M.relRank A B := by
  have relRank_inter_ground_self_left : ∀ ⦃A⦄, M.relRank (A ∩ M.E) A = 0 := fun A ↦ by
    rw [relRank_eq_diff_right, diff_self_inter, diff_eq_compl_inter, <-nonpos_iff_eq_zero]
    have h : M.relRank ∅ (M.Eᶜ ∩ A) ≤ 0 := by
      rw [<-M.relRank_compl_ground_eq]
      exact M.relRank_mono_right inter_subset_left
    refine LE.le.trans ?_ h
    exact M.relRank_mono_left <| empty_subset (A ∩ M.E)
  symm
  calc
    M.relRank A B = M.relRank A (B ∪ A) := by rw [relRank_eq_union_right]
    _ = M.relRank (A ∩ M.E) (B ∪ A) := by
      rw [M.relRank_add_cancel inter_subset_left subset_union_right,
        relRank_inter_ground_self_left, zero_add]
    _ = M.relRank (A ∩ M.E) ((B ∪ A) ∩ M.E) := by
      have h : A ∩ M.E ⊆ (B ∪ A) ∩ M.E :=
        inter_subset_inter subset_union_right <| subset_refl M.E
      rw [M.relRank_add_cancel h inter_subset_left, relRank_inter_ground_self_left, add_zero]
    _ = M.relRank (A ∩ M.E) (B ∩ M.E) := by
      rw [union_inter_distrib_right, <-relRank_eq_union_right]

lemma relRank_inter_ground_left {M : RankMatroid α} (A B : Set α) :
    M.relRank (A ∩ M.E) B = M.relRank A B := by
  rw [<-relRank_inter_ground, inter_assoc, inter_self, relRank_inter_ground]

lemma relRank_inter_ground_right {M : RankMatroid α} (A B : Set α) :
    M.relRank A (B ∩ M.E) = M.relRank A B := by
  rw [<-relRank_inter_ground, inter_assoc, inter_self, relRank_inter_ground]

lemma Indep.subset {M : RankMatroid α} (hJ : M.Indep J) (rIJ : I ⊆ J) : M.Indep I := by
  refine M.indep_iff'.mpr ⟨rIJ.trans hJ.subset_ground, fun x hx ↦ ?_⟩
  have e := M.relRank_union_le_relRank_inter (J \ {x}) I
  have hJI : (J \ {x}) ∩ I = I \ {x} := by
    rw [← inter_diff_right_comm, inter_eq_self_of_subset_right rIJ]
  rwa [hJI, diff_union_eq_union_of_subset _ (by simpa), union_eq_self_of_subset_right rIJ,
    hJ.relRank_diff_singleton (rIJ hx), ENat.one_le_iff_pos] at e

lemma indep_iff : M.Indep I ↔ ∀ x ∈ I, M.relRank (I \ {x}) I ≠ 0 := by
  rw [M.indep_iff']
  refine ⟨fun h x hx ↦ (h.2 x hx).ne.symm, fun h ↦ ⟨fun x hx ↦ by_contra fun hxE ↦ h x hx ?_, ?_⟩⟩
  · rw [← relRank_inter_ground_left, ← inter_diff_right_comm, inter_diff_assoc,
      diff_singleton_eq_self hxE, relRank_inter_ground_left, relRank_self_eq_zero]
  exact fun x hx ↦ pos_iff_ne_zero.2 <| h x hx

lemma Indep.insert_indep_of_relRank_ne_zero (hI : M.Indep I) (hx : M.relRank I (insert x I) ≠ 0) :
    M.Indep (insert x I) := by
  suffices ∀ a ∈ I, ¬M.relRank (insert x I \ {a}) (insert x I) = 0 by
    simpa [indep_iff, M.relRank_add_cancel diff_subset (subset_insert _ _), hx]
  intro a haI hr
  have h' := M.relRank_union_le_relRank_inter I (insert x I \ {a})

  -- rw [← inter_diff_right_comm, diff_union_eq_union_of_subset _ (by simpa),
  --   union_eq_self_of_subset_right (subset_insert _ _)] at h'
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

-- This is a proof of the original version of the axiom using the weaker one.
-- lemma relRank_sUnion_eq_zero {S : Set (Set α)} {A : Set α}
--     (h : ∀ B ∈ S, A ⊆ B ∧ M.relRank A B = 0) : M.relRank A (⋃₀ S) = 0 := by
--   obtain (rfl | ⟨B₀, hB₀⟩) := eq_empty_or_nonempty S
--   · simpa using M.relRank_mono_left (empty_subset A) (X := ∅)
--   refine M.relRank_diff_eq_zero _ _ (subset_sUnion_of_subset _ _ (h _ hB₀).1 hB₀) ?_
--   simp only [mem_diff, mem_sUnion, and_imp, forall_exists_index]
--   refine fun e B hBS heB _ ↦ ?_
--   simpa [(h B hBS).2 ] using M.relRank_mono_right (X := A) (insert_subset heB (h B hBS).1)

@[simps!] protected def matroid (M : RankMatroid α) : Matroid α :=
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

namespace IndepMatroid

variable {α : Type*}

def ofFiniteRankAxioms {E : Set α} (hE : E.Finite) (r : Set α → ℕ)
    (rank_le_encard : ∀ X, r X ≤ X.encard)
    (monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B)
    (submodularity : ∀ A B, r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rank_inter_ground : ∀ A, r A = r (A ∩ E))
    : IndepMatroid α := by
  set Indep : Set α → Prop := fun X ↦ r X = X.encard with h_indep
  have rank_le_ncard : {X : Set α} → Finite X → r X ≤ X.ncard := by
    intro X hX
    have := rank_le_encard X
    rwa [<-Set.Finite.cast_ncard_eq, @Nat.cast_le ℕ∞] at this
    exact hX
  have indep_empty : Indep ∅ := by
    rw [h_indep];
    have h := rank_le_ncard finite_empty;
    simp only [encard_empty]
    simp only [ncard_empty] at h
    exact congr_arg _ (Nat.eq_zero_of_le_zero h)
  have indep_empty_ncard : r ∅ = (∅ : Set α).ncard := by
    have h := rank_le_ncard finite_empty;
    simp only [ncard_empty] at h ⊢
    exact Nat.eq_zero_of_le_zero h
  have subset_ground : ∀ ⦃I : Set α⦄, Indep I → I ⊆ E := by
    intro I hI_indep
    have hIE_finite : (I ∩ E).Finite := (Finite.subset hE inter_subset_right)
    have hIE_indep : Indep (I ∩ E) := by
      refine LE.le.antisymm ?_ ?_
      · rw [<-Set.Finite.cast_ncard_eq hIE_finite, @Nat.cast_le ℕ∞]
        exact rank_le_ncard hIE_finite
      have := submodularity (I ∩ E) (I \ E)
      simp only [inter_union_diff, rank_inter_ground (I \ E), inter_assoc,
        inter_diff_self, diff_inter_self, inter_empty, indep_empty_ncard,
        ncard_empty, add_zero] at this
      rw [<-@Nat.cast_le ℕ∞] at this
      refine le_trans ?_ this
      rw [hI_indep]
      exact encard_mono (inter_subset_left)
    rw [h_indep] at hIE_indep hI_indep; rw [rank_inter_ground, hIE_indep] at hI_indep
    rw [<-Set.encard_diff_add_encard_inter I E] at hI_indep
    nth_rewrite 1 [<-zero_add (I ∩ E).encard] at hI_indep
    exact diff_eq_empty.mp (encard_eq_zero.mp (WithTop.add_right_cancel
        (encard_ne_top_iff.mpr hIE_finite) hI_indep).symm)
  have indep_ncard : {I : Set α} → Indep I → r I = I.ncard := by
    intro I hI
    have hI_finite : I.Finite := Finite.subset hE (subset_ground hI)
    rw [h_indep] at hI
    rw [<-Set.Finite.cast_ncard_eq hI_finite] at hI
    refine Nat.le_antisymm (rank_le_ncard hI_finite) ?_
    rw [<-@Nat.cast_le ℕ∞, hI]
  have indep_subset : ∀ ⦃I J : Set α⦄, Indep J → I ⊆ J → Indep I := by
    intro I J hJ_indep hI
    have hJ_finite : Finite J := Finite.subset hE (subset_ground hJ_indep)
    have hI_finite : Finite I := Finite.subset hJ_finite hI
    rw [h_indep]; dsimp only
    rw [<-Set.Finite.cast_ncard_eq hI_finite]
    apply congrArg Nat.cast
    refine LE.le.antisymm (rank_le_ncard hI_finite) ?_
    have := submodularity I (J \ I)
    rw [union_diff_self, inter_diff_self, indep_empty_ncard, ncard_empty,
      add_zero, union_eq_self_of_subset_left hI, indep_ncard hJ_indep] at this
    have := Nat.sub_le_of_le_add (this.trans (add_le_add (le_refl (r I))
      (rank_le_ncard (Finite.subset hJ_finite diff_subset))))
    simpa only [ncard_diff hI hJ_finite,
      Nat.sub_sub_self (ncard_le_ncard hI hJ_finite)] using this
  have indep_finite : ∀ ⦃I : Set α⦄, Indep I → Finite I :=
    fun I hI ↦ Finite.subset hE (subset_ground hI)
  have indep_aug : ∀ ⦃I J : Set α⦄, Indep I → Indep J → I.ncard < J.ncard
      → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I) := by
    intro I J hI_indep hJ_indep hIJ
    by_contra!; rw [h_indep] at this; dsimp only at this
    have hI_finite : Finite I := indep_finite hI_indep
    have hJ_finite : Finite J := indep_finite hJ_indep
    have h : ∀ e ∈ J, e ∉ I → r (insert e I) = I.ncard := by
      intro e he he'
      have h' := this e he he'
      rw [<-Set.Finite.cast_ncard_eq (Finite.insert e hI_finite)] at h'
      refine Nat.le_antisymm ?_ ?_
      · have h : r (insert e I) ≠ (insert e I).ncard := by
          contrapose! h'; exact congrArg _ h'
        have h_lt := Nat.lt_iff_le_and_ne.mpr ⟨(rank_le_ncard (Finite.insert e hI_finite)), h⟩
        rw [ncard_insert_of_not_mem he' hI_finite] at h_lt
        exact Nat.le_of_lt_succ h_lt
      rw [<-indep_ncard hI_indep]
      exact monotonicity (subset_insert e I)
    have h_induc : ∀ n : ℕ, ∀ S ⊆ J \ I, S.ncard = n → r I = r (I ∪ S) := by
      intro n
      induction n with
      | zero =>
        intro S hS hS_ncard
        have hS_finite : Finite S := Finite.subset hJ_finite (hS.trans diff_subset)
        rw [(ncard_eq_zero hS_finite).mp hS_ncard, union_empty]
      | succ n hn =>
        intro S hS hS_ncard
        obtain ⟨y, T, hy, rfl, hT⟩ := eq_insert_of_ncard_eq_succ hS_ncard
        refine LE.le.antisymm (monotonicity (subset_union_left)) ?_
        rw [<-Set.singleton_union, union_union_distrib_left]
        have := submodularity (I ∪ {y}) (I ∪ T)
        nth_rw 3 [union_singleton] at this
        have hT_JI : T ⊆ J \ I := (subset_insert y T).trans hS
        have hy_JI : y ∈ J \ I := hS (mem_insert y T)
        rwa [<-hn T ((subset_insert y T).trans hS) hT,
          h y (mem_of_mem_diff hy_JI) (not_mem_of_mem_diff hy_JI),
          <-Set.union_inter_distrib_left, singleton_inter_eq_empty.mpr hy,
          union_empty, add_le_add_iff_right, <-indep_ncard hI_indep] at this
    have hI_IJ := h_induc (J \ I).ncard (J \ I) subset_rfl rfl
    simp only [union_diff_self] at hI_IJ
    have h_bad : r J ≤ r (I ∪ J) := monotonicity subset_union_right
    rw [<-hI_IJ, indep_ncard hI_indep, indep_ncard hJ_indep] at h_bad
    exact LT.lt.not_le hIJ h_bad
  exact IndepMatroid.ofFinite hE Indep indep_empty indep_subset indep_aug subset_ground

def ofFiniteRankAxioms' {E : Set α} (hE : E.Finite) (r : Set α → ℕ)
    (rank_empty : r ∅ = 0)
    (submodularity : ∀ A B, r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rank_step : ∀ A, ∀ x, r A ≤ r (A ∪ {x}) ∧ r (A ∪ {x}) ≤ r A + 1)
    (rank_inter_ground : ∀ A, r A = r (A ∩ E))
    : IndepMatroid α := by
  have rank_le_ncard : ∀ (X : Set α), r X ≤ X.encard := by
    have h_induc : ∀ (n : ℕ∞), ∀ (X : Set α), X.encard = n → r X ≤ X.encard := by
      intro n X hX
      induction n using ENat.nat_induction generalizing X with
      | h0 =>
        rw [encard_eq_zero.mp hX, rank_empty, encard_empty]
        simp only [CharP.cast_eq_zero, le_refl]
      | hsuc n hn =>
        have hX_finite : Finite X := by
          have : (n.succ : ℕ∞) ≠ ⊤ := by exact ENat.coe_ne_top n.succ
          rw [<-hX, encard_ne_top_iff] at this;
          assumption
        have h : X.ncard = n + 1 := by
          rw [<-Set.Finite.cast_ncard_eq hX_finite, Nat.succ_eq_add_one] at hX
          rwa [<-WithTop.coe_eq_coe]
        obtain ⟨x, Y, hx, rfl, hY⟩ := eq_insert_of_ncard_eq_succ h
        have hY_finite := Finite.subset hX_finite (subset_insert x Y)
        have hY' : Y.encard = n := by
          rw [<-Set.Finite.cast_ncard_eq hY_finite, hY]
        rw [encard_insert_of_not_mem hx, <-Set.union_singleton,
          <-Set.Finite.cast_ncard_eq hY_finite, <-ENat.coe_one,
          <-ENat.coe_add Y.ncard 1, Nat.cast_le]
        have hY : r Y ≤ Y.ncard := by
          have := hn Y hY'
          rwa [<-Set.Finite.cast_ncard_eq hY_finite, @Nat.cast_le] at this
        exact (rank_step Y x).right.trans (add_le_add hY (le_refl 1))
      | htop _ =>
        rw [hX]; exact OrderTop.le_top (r X : ℕ∞)
    exact fun X ↦ h_induc X.encard X rfl
  have monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B := by
    intro A B hA
    suffices h : ∀ A B, A ⊆ B → B ⊆ E → r A ≤ r B by
      rw [rank_inter_ground A, rank_inter_ground B]
      exact h (A ∩ E) (B ∩ E) (inter_subset_inter_left E hA) inter_subset_right
    clear A B hA
    have h_induc : ∀ n : ℕ, ∀ {A B : Set α}, A ⊆ B → B ⊆ E → A.ncard + n = B.ncard → r A ≤ r B := by
      intro n A B hA hB
      have hB_finite := Finite.subset hE hB
      have hA_finite := Finite.subset hB_finite hA
      induction n generalizing A B with
      | zero =>
        intro h; simp [add_zero] at h
        rw [eq_of_subset_of_ncard_le hA h.ge hB_finite]
      | succ n hn =>
        intro h;
        rw [<-Set.ncard_diff_add_ncard_of_subset hA hB_finite, add_comm] at h
        simp only [add_left_inj] at h
        obtain ⟨x, S, _, hxS, hS⟩ := eq_insert_of_ncard_eq_succ h.symm
        have : B = (A ∪ S) ∪ {x} := by
          rw [union_assoc, union_singleton, hxS,
            union_diff_self, union_eq_self_of_subset_left hA]
        have hAS : (A ∪ S) ⊆ B := by rw [this]; exact subset_union_left
        have hAS_disjoint : Disjoint A S := by
          have : S ⊆ B \ A := by rw [<-hxS]; exact subset_insert x S
          exact (subset_diff.mp this).right.symm
        have hAS_finite : (A ∪ S).Finite := Finite.subset hB_finite hAS
        have hAS_encard : A.ncard + n = (A ∪ S).ncard := by
          rw [ncard_union_eq hAS_disjoint hA_finite
            (Finite.subset hAS_finite subset_union_right), add_right_inj, hS]
        rw [this]
        exact le_trans (hn subset_union_left (hAS.trans hB) hAS_finite hA_finite hAS_encard)
          (rank_step (A ∪ S) x).left
    intro A B hA hB
    have h_ncard : A.ncard + (B \ A).ncard = B.ncard := by
      rw [ncard_diff hA (Finite.subset hE hB),
          Nat.add_sub_cancel' (ncard_le_ncard hA (Finite.subset hE hB))]
    exact h_induc (B \ A).ncard hA hB h_ncard
  exact IndepMatroid.ofFiniteRankAxioms hE r
    rank_le_ncard monotonicity submodularity rank_inter_ground
