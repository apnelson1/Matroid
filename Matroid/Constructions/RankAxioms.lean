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

namespace Matroid

variable {α : Type*}

def ofFiniteRankAxioms (E : Set α) (r : Set α → ℕ)
    (rank_le_encard : ∀ A, r A ≤ A.encard)
    (monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B)
    (submodularity : ∀ A B, r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rank_inter_ground : ∀ A, r A = r (A ∩ E)) :
    Matroid α :=
  let Indep := fun X ↦ r X = X.encard
  have indep_empty : Indep ∅ := by
    simp [Indep, le_antisymm (rank_le_encard ∅)]
  have indep_finite : ∀ ⦃I : Set α⦄, Indep I → I.Finite := fun I hI ↦
    finite_of_encard_eq_coe <| Eq.symm <| by simpa using hI
  have subset_ground : ∀ ⦃I : Set α⦄, Indep I → I ⊆ E := fun I hI ↦ by
    have hle := add_le_add_left (rank_le_encard (I ∩ E)) ((I \ E).encard)
    rw [← rank_inter_ground, hI, WithTop.add_le_add_iff_left] at hle
    · simpa using (indep_finite hI).eq_of_subset_of_encard_le inter_subset_left hle
    exact encard_ne_top_iff.2 <| (indep_finite hI).subset diff_subset
  have indep_subset : ∀ ⦃I J : Set α⦄, Indep J → I ⊆ J → Indep I := fun I J hJ hIJ ↦ by
    have hsm := (Nat.cast_le (α := ENat)).2 (submodularity (J \ I) I)
    rw [diff_union_self, union_eq_self_of_subset_right hIJ, diff_inter_self,  Nat.cast_add, hJ,
       Nat.cast_add, ← encard_diff_add_encard_of_subset hIJ, add_assoc] at hsm
    replace hsm := hsm.trans (add_le_add_right (rank_le_encard _) _)
    rw [WithTop.add_le_add_iff_left] at hsm
    · exact (le_self_add.trans hsm).antisymm' <| rank_le_encard I
    exact encard_ne_top_iff.2 <| (indep_finite hJ).subset diff_subset
  have indep_bdd : ∃ (n : ℕ), ∀ (I : Set α), Indep I → I.encard ≤ n :=
    ⟨r E, fun I hI ↦ by simp_rw [<-hI, Nat.cast_le, monotonicity <| subset_ground hI]⟩
  have indep_aug : ∀ ⦃I J : Set α⦄, Indep I → Indep J → I.encard < J.encard
      → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I) := by
    intro I J hI hJ hIJ
    by_contra! h_con
    have h : ∀ e ∈ J, e ∉ I → r (insert e I) = I.encard := by
      refine fun e heJ heI ↦ by_contra fun hne ↦ h_con e heJ heI <| (rank_le_encard _).antisymm ?_
      rw [encard_insert_of_not_mem heI,
        ENat.add_one_le_iff (by simpa [encard_ne_top_iff] using indep_finite hI), lt_iff_le_and_ne,
        and_iff_left <| Ne.symm hne, ← hI, Nat.cast_le]
      exact monotonicity <| subset_insert _ _
    have h_induc : ∀ (S : Finset α), (S : Set α) ⊆ J \ I → r I = r (I ∪ S) := fun S hS ↦ by
      classical
      induction' S using Finset.induction with a S ha IH; simp
      simp only [Finset.coe_insert, insert_subset_iff, mem_diff] at hS
      have hsm := submodularity (insert a I) (S ∪ I)
      rw [insert_inter_of_not_mem (by simp [ha, hS]), ← Nat.cast_le (α := ℕ∞), Nat.cast_add,
        Nat.cast_add, inter_eq_self_of_subset_left subset_union_right, h _ hS.1.1 hS.1.2, hI,
        add_comm, WithTop.add_le_add_iff_left (by rw [encard_ne_top_iff]; exact indep_finite hI),
        insert_union, union_eq_self_of_subset_left subset_union_right, union_comm,
        ← union_insert, ← Finset.coe_insert, ← IH hS.2, Nat.cast_le] at hsm
      exact hsm.antisymm' <| monotonicity subset_union_left
    have hr : r I = r (I ∪ J) := by
      simpa using h_induc ((indep_finite hJ).diff I).toFinset (by simp [Subset.rfl])
    have hle := (monotonicity subset_union_right).trans hr.symm.le
    rw [← Nat.cast_le (α := ℕ∞), hI, hJ] at hle
    exact hle.not_lt hIJ
  IndepMatroid.matroid <|
  IndepMatroid.ofBddAugment E Indep indep_empty indep_subset indep_aug indep_bdd subset_ground

def ofFiniteRankAxioms' (E : Set α) (hE : E.Finite) (r : Set α → ℕ)
    (rank_empty : r ∅ = 0)
    (submodularity : ∀ A B, r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rank_le_insert : ∀ A x, r A ≤ r (insert x A))
    (rank_insert_le : ∀ A x, r (insert x A) ≤ r A + 1)
    (rank_inter_ground : ∀ A, r A = r (A ∩ E)) : Matroid α :=
  have rank_le_ncard : ∀ (X : Set α), r X ≤ X.encard := by
    suffices hfin : ∀ (X : Finset α), r X ≤ X.card by
      intro X
      obtain (hX | hX) := X.finite_or_infinite.symm
      · simp [hX.encard_eq]
      simpa [Finite.encard_eq_coe_toFinset_card hX, Nat.cast_le] using hfin hX.toFinset
    intro X
    classical
    induction' X using Finset.induction with e X heX hX
    · simp [rank_empty]
    rw [Finset.coe_insert, Finset.card_insert_of_not_mem (by simpa)]
    exact (rank_insert_le X e).trans (add_le_add_right hX 1)
  have monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B := by
    classical
    intro A B hAB
    have aux : ∀ I : Finset α, r A ≤ r (A ∪ I) := fun I ↦ by
      induction' I using Finset.induction with e I _ hI
      · simp
      exact hI.trans ((rank_le_insert _ e).trans (by simp))
    refine (aux (hE.inter_of_right B).toFinset).trans ?_
    rw [Finite.coe_toFinset, rank_inter_ground (A ∪ B ∩ E), union_inter_distrib_right,
      inter_assoc, inter_self, ← union_inter_distrib_right, ← rank_inter_ground,
      union_eq_self_of_subset_left hAB]
  ofFiniteRankAxioms E r rank_le_ncard monotonicity submodularity rank_inter_ground

-- def ofFinitaryRankAxioms' [DecidableEq α] (E : Set α) [DecidablePred (· ∈ E)]
--     (r : Finset α → ℕ)
--     (rank_empty : r ∅ = 0)
--     (rank_insert_le : ∀ A x, r (insert x A) ≤ r A + 1)
--     (submodularity : ∀ A (x y : α), r A + r (A ∪ {x,y}) ≤ r (insert x A) + r (insert y A))
--     (rank_inter_ground : ∀ A, r A = r (A.filter (· ∈ E))) :
--     Matroid α := by

--   classical
--   -- let Indep : Finset α → Prop := fun I ↦ r I = I.card
--   have rank_le_card : ∀ X, r X ≤ X.card := by
--     intro X
--     classical
--     induction' X using Finset.induction with e X heX hX
--     · simp [rank_empty]
--     rw [Finset.card_insert_of_not_mem (by simpa)]
--     exact (rank_insert_le X e).trans (add_le_add_right hX 1)
--   have rank_mono : ∀ X Y, r X ≤ r (X ∪ Y) := by
--     intro X Y
--     induction' Y using Finset.induction with e Y heY hY
--     · simp
--     rw [Finset.union_insert]
--     exact hY.trans (by simpa [Finset.union_comm, Finset.insert_eq] using submodularity (X ∪ Y) e e)
--   refine IndepMatroid.matroid <| IndepMatroid.ofFinset E (fun I ↦ r I = I.card) (by simpa) ?_ ?_ ?_
--   · intro I J (hI : _ = _) hIJ
--     suffices h' : ∀ D, (I ∪ D).card ≤ r (I ∪ D) → r I = I.card by
--       exact h' J <| by simpa [Finset.union_eq_right.2 hIJ] using hI.symm.le
--     intro D
--     induction' D using Finset.induction with e D heD hD
--     · rw [Finset.union_empty]
--       exact fun h ↦ h.antisymm' (rank_le_card _)
--     rw [Finset.union_insert]
--     by_cases heI : e ∈ I
--     · rwa [Finset.insert_eq_of_mem (by simp [heI])]
--     refine fun hle ↦ hD ?_
--     replace hle := hle.trans (rank_insert_le _ _)
--     rwa [Finset.card_insert_of_not_mem (by simp [heI, heD]), add_le_add_iff_right] at hle
--   · refine fun I J (hI : _ = _) (hJ : _ = _) hIJ ↦ ?_
--     by_contra! hcon
--     have haux : ∀ S ⊆ J \ I, r (I ∪ S) = r I := by
--       intro S
--       induction' S using Finset.induction with e S heS ih
--       · simp
--       simp only [Finset.insert_subset_iff, Finset.mem_sdiff, Finset.union_insert, and_imp]
--       intro heJ heI hSJI
--       induction' S using Finset.induction with f S hfS ih'
--       · rw [Finset.union_empty, le_antisymm_iff, ← Nat.lt_add_one_iff,
--           hI, ← I.card_insert_of_not_mem heI, lt_iff_le_and_ne, and_iff_right (rank_le_card _),
--           and_iff_right (hcon e heJ heI), ← hI, Finset.insert_eq, Finset.union_comm]
--         apply rank_mono
--       specialize ih hSJI
--       suffices h' : r (I ∪ S ∪ ({e,f})) ≤ r I by
--         rw [Finset.insert_eq, Finset.union_comm, Finset.insert_eq, Finset.union_comm {f},
--           Finset.union_assoc, S.union_assoc, ← Finset.insert_eq, Finset.pair_comm, ← I.union_assoc]
--         exact h'.antisymm (by rw [I.union_assoc]; apply rank_mono)
--       have hsm := submodularity (I ∪ S) e f
--       simp only [Finset.mem_insert, not_or] at heS
--       have hIS : r (I ∪ S) = r I := by
--         rw [← ih, Finset.union_insert, le_antisymm_iff, Finset.insert_eq, Finset.union_comm {f},
--           and_iff_right (rank_mono _ _), Finset.union_assoc, S.union_comm, ← S.insert_eq, ih]
--         apply rank_mono
--       rw [Finset.insert_subset_iff] at hSJI
--       rw [ih' heS.2 (fun _ ↦ hIS) hSJI.2, ← Finset.union_insert, ih, hIS] at hsm
--       linarith
--     have := haux (J \ I)







    -- intro I J (hI : _ = _) hIJ
    -- induction' J using Finset.induction with e J heJ hJ
    -- · simpa [Finset.subset_empty.1 hIJ]



def ofFinitaryRankAxioms [DecidableEq α] (E : Set α) [DecidablePred (· ∈ E)]
    (r : Finset α → ℕ)
    (rank_le_card : ∀ A, r A ≤ A.card)
    (monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B)
    (submodularity : ∀ (A B : Finset α), r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rank_inter_ground : ∀ A, r A = r (A.filter (· ∈ E))) : Matroid α :=
  let Indep : Set α → Prop := fun J ↦ ∀ I, ↑I ⊆ J → r I = I.card
  have r_empty : r ∅ = 0 := by rw [<-nonpos_iff_eq_zero]; exact rank_le_card ∅
  have indep_empty : Indep ∅ := by
    intro I hI
    rw [subset_empty_iff, Finset.coe_eq_empty] at hI
    rw [hI, Finset.card_empty, r_empty]
  have indep_subset : ∀ ⦃I J : Set α⦄, Indep J → I ⊆ J → Indep I := by
    intro I J hJ_indep hI I' hI'
    exact hJ_indep I' <| hI'.trans hI
  have indep_finset_iff : ∀ ⦃I : Finset α⦄, Indep I ↔ r I = I.card := by
    intro I
    refine ⟨fun h ↦ h I (subset_refl _), fun h ↦ ?_⟩
    intro A hA
    rw [Finset.coe_subset] at hA
    by_contra! h_con
    replace h_con := LE.le.lt_of_ne (rank_le_card A) h_con
    have h_bad := submodularity A (I \ A)
    simp only [Finset.union_sdiff_self_eq_union, Finset.inter_sdiff_self,
      Finset.union_eq_right.mpr hA, h, r_empty, add_zero] at h_bad
    replace h_bad := LE.le.trans_lt h_bad <| add_lt_add_of_lt_of_le h_con (rank_le_card (I \ A))
    rwa [add_comm, Finset.card_sdiff_add_card_eq_card hA, lt_self_iff_false] at h_bad
  have indep_aug_finset : ∀ ⦃I J : Finset α⦄, Indep I → Indep J → I.card < J.card →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I) := by
    intro I J hI_indep hJ_indep hIJ
    by_contra! h
    have h_induc : ∀ (S : Finset α), S ⊆ J \ I → r I = r (I ∪ S) := by
      intro S hS
      induction' S using Finset.induction with a S ha IH; simp
      refine LE.le.antisymm (monotonicity (Finset.subset_union_left)) ?_
      have := submodularity (I ∪ {a}) (I ∪ S)
      have ha_JI : a ∈ J \ I := hS <| Finset.mem_insert.mpr (by simp)
      have hr : r (I ∪ {a}) = r I := by
        refine le_antisymm ?_ (monotonicity Finset.subset_union_left)
        rw [hI_indep I (subset_refl _), <-Nat.lt_succ_iff, Nat.succ_eq_add_one,
          <-Finset.card_insert_of_not_mem (Finset.mem_sdiff.mp ha_JI).right,
          Finset.union_comm, <-Finset.insert_eq, LE.le.lt_iff_ne (rank_le_card _), ne_eq,
          <-indep_finset_iff, Finset.coe_insert]
        exact h a (Finset.mem_sdiff.mp ha_JI).left (Finset.mem_sdiff.mp ha_JI).right
      rwa [<-Finset.union_inter_distrib_left, Finset.singleton_inter_of_not_mem ha,
        Finset.union_empty, <-IH <| (Finset.subset_insert a S).trans hS, Finset.union_right_comm,
        <-Finset.union_assoc, Finset.union_self, add_le_add_iff_right, Finset.union_assoc,
        Finset.union_comm S, <-Finset.insert_eq, hr] at this
    have h_con : r J ≤ r (I ∪ J) := monotonicity Finset.subset_union_right
    rw [<-Finset.union_sdiff_self_eq_union, <-h_induc (J \ I) (subset_refl _),
      hI_indep I (subset_refl _), hJ_indep J (subset_refl _)] at h_con
    linarith
  have indep_aug : ∀ ⦃I J : Set α⦄, Indep I → I.Finite → Indep J → J.Finite →
      I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I) := by
    intro I J hI_indep hI_finite hJ_indep hJ_finite hIJ
    set I' : Finset α := hI_finite.toFinset
    set J' : Finset α := hJ_finite.toFinset
    have hII': I = ↑I' := Eq.symm <| Finite.coe_toFinset hI_finite
    have hJJ': J = ↑J' := Eq.symm <| Finite.coe_toFinset hJ_finite
    rw [hII'] at hIJ hI_indep ⊢
    rw [hJJ'] at hIJ hJ_indep ⊢
    simp only [ncard_coe_Finset] at hIJ
    exact indep_aug_finset hI_indep hJ_indep hIJ
  have indep_compact : ∀ (J : Set α), (∀ I ⊆ J, I.Finite → Indep I) → Indep J := by
    intro J h I hI
    exact h ↑I hI (Finset.finite_toSet I) I (subset_refl I)
  have subset_ground : ∀ (I : Set α), Indep I → I ⊆ E := by
    intro I hI_indep
    by_contra! h
    obtain ⟨x, hxI, hxE⟩ := Set.not_subset.mp h
    rw [<-singleton_subset_iff] at hxI
    have hx := indep_subset hI_indep hxI
    specialize hx {x} (Finset.singleton_subset_set_iff.mpr rfl)
    rw [Finset.card_singleton] at hx
    rw [rank_inter_ground {x}, Finset.filter_singleton] at hx
    split at hx
    · contradiction
    rw [r_empty] at hx
    contradiction
  IndepMatroid.matroid <| IndepMatroid.ofFinitary E Indep indep_empty
    indep_subset indep_aug indep_compact subset_ground
