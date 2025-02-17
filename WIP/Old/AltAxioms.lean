import Mathlib.Data.Set.Pairwise.Basic
import Matroid.Basic
import Matroid.Alt.Dual

open Set

namespace Matroid

/- complement API -/
lemma compl_ground {A B E : Set α} (h : A ⊆ E) : A \ B = A ∩ (E \ B) := by
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left h]

-- lemma disjoint_of_diff_subset {A B C : Set α} (h : A ⊆ B) : Disjoint A (C \ B) :=
--   disjoint_of_subset_left h disjoint_sdiff_right

-- lemma compl_diff_compl_iff (A B E : Set α) (h : A ⊆ E) : A \ B = (E \ B) \ (E \ A) := by
--   ext; aesop

/- end of complement API -/

/- singleton API -/
-- lemma inter_singleton_eq_self {a : α} {S : Set α} :
--     S ∩ {a} = {a} ↔ a ∈ S :=
--   ⟨fun h ↦ singleton_subset_iff.mp (h.symm.subset.trans (inter_subset_left S {a})),
--    fun h ↦ subset_antisymm inter_subset_right (singleton_subset_iff.mpr ⟨h, mem_singleton _⟩)⟩
/- end of singleton API -/


/- matroid of forall subset -/

lemma diff_subset_of_subset {A B E : Set α} (h : A ⊆ B) : E \ B ⊆ E \ A :=
  fun _ he ↦ ⟨he.1, fun he' ↦ he.2 (h he')⟩

lemma diff_ssubset_of_ssubset {A B E : Set α} (hA : A ⊆ E) (hB : B ⊆ E) (hAB  : A ⊂ B) :
    E \ B ⊂ E \ A := by
  refine' ⟨diff_subset_of_subset hAB.1, fun h ↦ _⟩
  have := @diff_subset_of_subset α (E \ A) (E \ B) E h
  rw [diff_diff_cancel_left hB, diff_diff_cancel_left hA] at this
  exact hAB.not_subset this

def matroid_of_indep_of_forall_subset_isBase (E : Set α) (Indep : Set α → Prop)
  (h_exists_maximal_indep_subset : ∀ X, X ⊆ E → ∃ I, I ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X})
  (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
  (h_isBasis : ∀ ⦃I I'⦄, Indep I → I' ∈ maximals (· ⊆ ·) {I | Indep I} →
    ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I} ∧ I ⊆ B ∧ B ⊆ I ∪ I')
  (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_indep E Indep
  (by {
    obtain ⟨I, ⟨hI, -⟩⟩ := h_exists_maximal_indep_subset ∅ (empty_subset _)
    rw [← subset_empty_iff.mp hI.2]; exact hI.1
  })
  (fun I J hI hIJ ↦ h_subset hI hIJ)
  (by {
    rintro I B hI h'I hB
    obtain ⟨B', hB'⟩ := h_isBasis hI hB
    obtain ⟨x, hx⟩ := exists_of_ssubset
      (ssubset_iff_subset_ne.mpr ⟨hB'.2.1, fun h ↦ by { rw [h] at h'I; exact h'I hB'.1 }⟩)
    exact ⟨x, ⟨((mem_union _ _ _).mp (hB'.2.2 hx.1)).elim (fun g ↦ by {exfalso; exact hx.2 g})
      (fun g ↦ g), hx.2⟩, h_subset hB'.1.1
      (by { rw [insert_eq, union_subset_iff, singleton_subset_iff]; exact ⟨hx.1, hB'.2.1⟩ })⟩
  })
  (by {
    let IsBase   : Set α → Prop := maximals (· ⊆ ·) { I | Indep I }
    let IsBase'  : Set α → Prop := { B | B ⊆ E ∧ IsBase (E \ B) }
    let Indep' : Set α → Prop := { I | ∃ B, IsBase' B ∧ I ⊆ B }

    have dual_subset : ∀ I J, Indep' J → I ⊆ J → Indep' I :=
      fun I J ⟨B, hB⟩ hIJ ↦ ⟨B, hB.1, hIJ.trans hB.2⟩
    have dual_isBase_compl : ∀ ⦃B⦄, IsBase B → IsBase' (E \ B) :=
      fun B hB ↦ by {rw [← diff_diff_cancel_left (h_support hB.1)] at hB; exact ⟨diff_subset _ _, hB⟩}
    have dual_isBase_indep : ∀ ⦃B⦄, IsBase' B → Indep' B :=
      fun B hB ↦ ⟨B, hB, subset_refl _⟩
    have dual_support : ∀ I, Indep' I → I ⊆ E :=
      fun I ⟨B, hB⟩ ↦ hB.2.trans hB.1.1
    have dual_indep_maximals_eq_dual_isBase : maximals (· ⊆ ·) {I | Indep' I} = IsBase' := by
      ext X; refine' ⟨fun ⟨⟨B, hB⟩, hX⟩ ↦ _, fun hX ↦ _⟩
      · by_contra! h
        have hX' := ssubset_iff_subset_ne.mpr ⟨hB.2, by {rintro rfl; exact h hB.1}⟩
        exact hX'.not_subset (hX (dual_isBase_indep hB.1) hX'.subset)
      · rw [maximals]
        by_contra! h; dsimp at h; push_neg at h
        obtain ⟨I, ⟨⟨B, ⟨hB, hIB⟩⟩, hXI, hIX⟩⟩ := h ⟨X, hX, subset_refl X⟩
        have hBcXc := diff_ssubset_of_ssubset hX.1 hB.1 (ssubset_of_ssubset_of_subset ⟨hXI, hIX⟩ hIB)
        exact hBcXc.not_subset (hB.2.2 hX.2.1 hBcXc.subset)
    have exists_isBase_contains_indep : ∀ I, Indep I → ∃ B, IsBase B ∧ I ⊆ B
    . rintro I hI
      obtain ⟨I', hI'⟩ := h_exists_maximal_indep_subset E (subset_refl _)
      obtain ⟨B, hB⟩ := h_isBasis hI ⟨hI'.1.1, fun X hX hI'X ↦ hI'.2 ⟨hX, h_support hX⟩ hI'X⟩
      exact ⟨B, hB.1, hB.2.1⟩










    have aux2'' : ∀ X B, X ⊆ E → IsBase B →
        (E \ B) ∩ (E \ X) ∈ maximals (· ⊆ ·) {I' | Indep' I' ∧ I' ⊆ (E \ X)} →
        B ∩ X ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X} := by
      {
        refine' fun X B hX hB hBX ↦ ⟨⟨h_subset hB.1 inter_subset_left,
          inter_subset_right⟩, _⟩
        by_contra! g
        obtain ⟨I, h⟩ := g

        obtain ⟨Bt, hBt⟩ := exists_isBase_contains_indep I h.1.1

        have h₁ : B ∩ X ⊂ I :=
          ⟨h.2.1, h.2.2⟩
        rw [← inter_eq_self_of_subset_left h.1.2] at h₁
        have h₂ : (E \ I) ∩ X ⊂ (E \ B) ∩ X :=
          sorry
          -- compl_ssubset_inter (h_support hB.1) (h_support h.1.1) h₁
        have h₃ : (E \ Bt) ∩ X ⊆ (E \ I) ∩ X :=
           inter_subset_inter_left _ (diff_subset_diff_right hBt.2)
        have h₄ : (E \ Bt) ∩ X ⊂ (E \ B) ∩ X :=
           ssubset_of_subset_of_ssubset h₃ h₂


        obtain ⟨I', hI'⟩ : ∃ I', I' ∈ maximals (· ⊆ ·) {I' | Indep' I'} ∧ E \ B ∩ (E \ X) ⊆ I' ∧ I' ⊆ E \ B ∩ (E \ X) ∪ E \ Bt
        . obtain ⟨B'', hB''⟩ := h_isBasis (h_subset hBt.1.1 (diff_subset Bt ((E \ B) ∩ (E \ X)))) hB
          refine' ⟨E \ B'', _, ⟨fun e he ↦ ⟨he.1.1,
            fun g ↦ (hB''.2.2 g).elim (fun he' ↦ he'.2 he) (fun he' ↦ he.1.2 he')⟩,
            fun e he ↦ _⟩⟩
          . rw [dual_indep_maximals_eq_dual_isBase]
            use diff_subset _ _
            rw [diff_diff_cancel_left (h_support hB''.1.1)]
            exact hB''.1
          rw [mem_union]
          by_contra! g; push_neg at g
          obtain ⟨he₁, he₂⟩ := g
          rw [mem_diff, not_and, not_not] at he₂
          exact he.2 (hB''.2.1 ⟨he₂ he.1, he₁⟩)

        have h₅ : (E \ B) ∩ (E \ X) ⊆ I' ∩ (E \ X) := by
          rw [← inter_eq_self_of_subset_left (inter_subset_right (E \ B) (E \ X))]
          exact inter_subset_inter_left (E \ X) hI'.2.1

        have h₆ : I' ∩ (E \ X) ⊆ (E \ B) ∩ (E \ X) :=
          hBX.2 ⟨(fun I J ⟨B, hB⟩ hIJ ↦ ⟨B, hB.1, hIJ.trans hB.2⟩) _ I' hI'.1.1 inter_subset_left, inter_subset_right⟩ h₅

        have h₇ : I' ∩ X ⊆ (E \ Bt) ∩ X := by
          {
            calc
              I' ∩ X ⊆ ((E \ B) ∩ (E \ X) ∪ (E \ Bt)) ∩ X  := inter_subset_inter_left X hI'.2.2
              _ = ((E \ B) ∩ (E \ X)) ∩ X ∪ ((E \ Bt) ∩ X) := by rw [← inter_distrib_right _ _]
              _ = (E \ B) ∩ ((E \ X) ∩ X) ∪ ((E \ Bt) ∩ X) := by rw [inter_assoc]
              _ = (E \ B) ∩ (X ∩ (E \ X)) ∪ ((E \ Bt) ∩ X) := by rw [inter_comm (E \ X) X]
              _ = ((E \ B) ∩ ∅) ∪ ((E \ Bt) ∩ X) := by rw [inter_diff_self _ _]
              _ = ∅ ∪ ((E \ Bt) ∩ X) := by rw [inter_empty _]
              _ = (E \ Bt) ∩ X := by rw [empty_union]
          }
        have h₈ : I' ∩ X ⊂ (E \ B) ∩ X :=
          ssubset_of_subset_of_ssubset h₇ h₄
        have h₉ : I' ⊂ (E \ B) :=
          sorry
          -- ssubset_of_subset_of_compl_ssubset' (dual_support I' hI'.1.1) diff_subset hX h₆ h₈
        exact h₉.not_subset (hI'.1.2 (dual_isBase_indep (dual_isBase_compl hB)) h₉.subset)
      }




    simp_rw [ExistsMaximalSubsetProperty]
    rintro X hX I hI hIX
    obtain ⟨I', hI'⟩ := h_exists_maximal_indep_subset X hX
    obtain ⟨B, hB⟩ : ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X } ∧ I ⊆ B ∧ B ⊆ I ∪ I'
    · obtain ⟨Bh, hBh⟩ := h_exists_maximal_indep_subset E (subset_refl _)
      obtain ⟨B', hB'⟩ := h_isBasis hI'.1.1 ⟨hBh.1.1, fun B hB hBhB ↦ hBh.2 ⟨hB, h_support hB⟩ hBhB⟩

      have I'eq : I' = B' ∩ X :=
        subset_antisymm (subset_inter_iff.mpr ⟨hB'.2.1, hI'.1.2⟩)
          (hI'.2 ⟨h_subset hB'.1.1 inter_subset_left, inter_subset_right⟩
          (subset_inter_iff.mpr ⟨hB'.2.1, hI'.1.2⟩))
      rw [I'eq] at hI'

      have hB'c : E \ B' ∩ (E \ X) ∈ maximals (fun x x_1 ↦ x ⊆ x_1) {I' | Indep' I' ∧ I' ⊆ E \ X}
      · refine' ⟨⟨⟨E \ B', ⟨diff_subset _ _, by { rw [diff_diff_right_self, inter_eq_self_of_subset_right (h_support hB'.1.1)]; exact hB'.1 }⟩, inter_subset_left⟩, inter_subset_right⟩, _⟩
        -- maximality
        by_contra! g
        obtain ⟨B, hB⟩ : ∃ B, IsBase B ∧ (B ∩ (E \ X) ⊂ B' ∩ (E \ X)) := by
          obtain ⟨I, h⟩ := g; obtain ⟨⟨Bt, hBt⟩, _⟩ := h.1
          have h₁ : (E \ B') ∩ (E \ X) ⊂ I :=
            ⟨h.2.1, h.2.2⟩
          rw [← inter_eq_self_of_subset_left h.1.2] at h₁
          have h₂ : (E \ I) ∩ (E \ X) ⊂ B' ∩ (E \ X) :=
            sorry
          exact ⟨E \ Bt, hBt.1.2, ssubset_of_subset_of_ssubset (inter_subset_inter_left _
            (diff_subset_diff_right hBt.2)) h₂⟩
        obtain ⟨J, hJ⟩ := h_isBasis hI'.1.1 hB.1
        have h₁JB : J ∩ X ⊆ B' ∩ X
        · have := inter_subset_inter_left X hJ.2.1
          rw [inter_eq_self_of_subset_left (inter_subset_right B' X)] at this
          exact hI'.2 ⟨h_subset hJ.1.1 inter_subset_left, inter_subset_right⟩ this
        have h₂JB : J ∩ (E \ X) ⊂ B' ∩ (E \ X)
        . have := inter_subset_inter_left (E \ X) hJ.2.2
          rw [union_inter_distrib_right, inter_assoc, inter_diff_self, inter_empty,
            empty_union] at this
          exact ssubset_of_subset_of_ssubset this hB.2
        have hJB : J ⊂ B := sorry
          -- ssubset_of_subset_of_compl_ssubset (h_support hI'.1.1) (h_support hB.1) h₁I'B h₂I'B
        exact hJB.not_subset (hJ.1.2 hB.1.1 hJB.subset)
      obtain ⟨B, hB⟩ := h_isBasis hI hB'.1

      have h : (E \ B') ∩ (E \ X) ⊆ (E \ B) ∩ (E \ X) := by
      { have h₁ : B ∩ (E \ X) ⊆ B' ∩ (E \ X)
        · have tmp := inter_subset_inter_left (E \ X) hB.2.2
          have := inter_subset_inter_left (E \ X) hIX
          rw [inter_diff_self _ _, subset_empty_iff] at this
          rw [inter_distrib_right, this, empty_union] at tmp
          exact tmp
        -- compl_subset_inter h₁
        sorry
      }
      rw [subset_antisymm h (hB'c.2 ⟨⟨E \ B,
          ⟨diff_subset _ _, by { rw [diff_diff_cancel_left (h_support hB.1.1)]; exact hB.1 }⟩,
          inter_subset_left⟩, inter_subset_right⟩ h)] at hB'c
      refine' ⟨B ∩ X, (aux2'' X B hX hB.1) hB'c, subset_inter_iff.mpr ⟨hB.2.1, hIX⟩, _⟩
      · calc B ∩ X ⊆ (I ∪ B') ∩ X    := inter_subset_inter_left X hB.2.2
          _ = (I ∩ X) ∪ (B' ∩ X)     := inter_distrib_right _ _ _
          _ = I ∪ I'                 := by rw [inter_eq_self_of_subset_left hIX, ← I'eq]
    exact ⟨B, ⟨hB.1.1.1, hB.2.1, hB.1.1.2⟩, fun Y hY hBY ↦ hB.1.2 ⟨hY.1, hY.2.2⟩ hBY⟩
  })
  h_support

lemma inter_iUnion_disjoint {ι : Type*} {Es Xs : ι → Set α}
    (hEs : Pairwise (Disjoint on Es)) (hXs : ∀ i, Xs i ⊆ Es i) (j : ι) :
    (⋃ i, Xs i) ∩ Es j = Xs j := by
  ext x
  refine' ⟨_, fun hx ↦ ⟨(subset_iUnion (fun i ↦ Xs i) j) hx, hXs j hx⟩⟩
  intro ⟨hx, hxj⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact (em (i = j)).elim (by { rintro rfl; exact hi })
          fun g ↦ (by { exfalso; exact (disjoint_left.mp (hEs g)) ((hXs i) hi) hxj })

lemma eq_iUnion_inter {ι : Type*} {Es : ι → Set α} {X : Set α} (hX : X ⊆ ⋃ i, Es i) :
    X = ⋃ i, X ∩ Es i :=
  subset_antisymm fun x hx ↦ by { rw [← inter_iUnion]; exact ⟨hx, hX hx⟩ }
                  fun x hx ↦ by { obtain ⟨i, ⟨hi, -⟩⟩ := mem_iUnion.mp hx; exact hi }

-- lemma maximal_union_iff
--     {ι : Type*}
--     (Es : ι → Set α)
--     (hEs : Pairwise (Disjoint on Es))
--     (Is : ι → Set α)
--     (hIs : ∀ i, Is i ⊆ Es i)
--     (h_global : Set α → Prop)
--     (h_local  : ι → Set α → Prop)
--     (h : ∀ (Js : ι → Set α), h_global (iUnion Js) ↔ ∀ i, h_local i (Js i)) :
--     iUnion Is ∈ maximals (· ⊆ ·) { X | h_global X } ↔
--         ∀ i, Is i ∈ maximals (· ⊆ ·) { X | h_local i X } := by
--   sorry

lemma aux {ι : Type*} [DecidableEq ι] {Ms : ι → Matroid α}
    (hEs : Pairwise (Disjoint on fun i ↦ (Ms i).E)) (I : Set α) (hIE : I ⊆ ⋃ i, (Ms i).E) :
  I ∈ maximals (· ⊆ ·) {I | I ⊆ ⋃ i, (Ms i).E ∧ ∀ i, (Ms i).Indep (I ∩ (Ms i).E) } ↔
    ∀ i, (Ms i).IsBase (I ∩ (Ms i).E) := by
  refine' ⟨fun h i ↦ _, fun h ↦ ⟨⟨hIE, fun i ↦ (h i).indep⟩, fun B ⟨hBE, hBs⟩ hIB ↦ _⟩⟩
  · rw [isBase_iff_maximal_indep]
    refine' ⟨h.1.2 i, fun X hX hIiX ↦ _⟩; by_contra! g
    set Js : ι → Set α := fun j ↦ if j = i then X else I ∩ (Ms j).E with heqJs

    have hJs : ∀ j, Js j ⊆ (Ms j).E
    . rintro j; rw [heqJs]; dsimp
      split_ifs with hj
      . rw [hj]; exact hX.subset_ground
      exact inter_subset_right

    have hJ : ⋃ j, Js j ∈ {I | I ⊆ ⋃ j, (Ms j).E ∧ ∀ j, (Ms j).Indep (I ∩ (Ms j).E)}
    · refine' ⟨iUnion_mono hJs, _⟩
      simp_rw [inter_iUnion_disjoint hEs hJs]
      rintro j; split_ifs with hj
      . rw [hj]; exact hX
      exact h.1.2 j

    have hIJ : I ⊆ iUnion Js
    · rw [eq_iUnion_inter hIE]
      refine' iUnion_mono fun j ↦ _
      split_ifs with hj
      · rw [hj]; exact hIiX
      exact subset_refl _

    have := iUnion_subset_iff.mp (h.2 hJ hIJ) i
    simp only [ite_true] at this
    have := inter_subset_inter_left (Ms i).E this
    rw [inter_eq_self_of_subset_left hX.subset_ground] at this
    exact g (subset_antisymm hIiX this)
  rw [eq_iUnion_inter hBE, eq_iUnion_inter hIE]
  exact iUnion_mono fun i ↦
        ((h i).eq_of_subset_indep (hBs i) (inter_subset_inter_left (Ms i).E hIB)).symm.subset

def directSum {ι : Type*} [DecidableEq ι] (Ms : ι → Matroid α)
  (hEs : Pairwise (Disjoint on fun i ↦ (Ms i).E)) :=
  matroid_of_indep_of_forall_subset_isBase
    (⋃ i, (Ms i).E)
    (fun I ↦ I ⊆ ⋃ i, (Ms i).E ∧ ∀ i, (Ms i).Indep (I ∩ (Ms i).E))
    (by {
      rintro X -
      let Xs : ι → Set α := fun i ↦ X ∩ (Ms i).E
      choose! Is hIs using (fun i ↦ exists_isBasis (Ms i) (Xs i))
      use (⋃ i, Is i)
      have hineq := inter_iUnion_disjoint hEs (fun i ↦ (hIs i).left_subset_ground)
      refine' ⟨⟨⟨iUnion_subset_iff.mpr (fun i ↦ (hIs i).left_subset_ground.trans
        (subset_iUnion (fun i ↦ (Ms i).E) i)), fun i ↦ (by { rw [hineq i]; exact (hIs i).indep })⟩,
         iUnion_subset (fun i ↦ (hIs i).subset.trans inter_subset_left)⟩, _⟩
      · rintro B ⟨⟨hBEs, hBs⟩, hBX⟩ hB
        have : B ⊆ ⋃ (i : ι), B ∩ (Ms i).E := by
          { rw [← inter_iUnion]; exact fun e he ↦ ⟨he, hBEs he⟩ }
        refine' this.trans (iUnion_mono (fun i ↦ _))
        · have := inter_subset_inter_left (Ms i).E hB
          rw [hineq i] at this
          exact ((hIs i).eq_of_subset_indep (hBs i) this
            (inter_subset_inter_left _ hBX)).symm.subset
    })
    (fun I J hJ hIJ ↦ ⟨hIJ.trans hJ.1,
      fun i ↦ (hJ.2 i).subset
      (subset_inter (inter_subset_left.trans hIJ) inter_subset_right)⟩)
    (by {
      rintro I I' ⟨hIE, hIs⟩ ⟨⟨hI'E, hI's⟩, hI'max⟩
      choose! Bs hBs using (fun i ↦ (hIs i).exists_isBase_subset_union_isBase
                                            (((aux hEs I' hI'E).mp ⟨⟨hI'E, hI's⟩, hI'max⟩) i))
      refine' ⟨⋃ i, Bs i, (aux hEs (⋃ i, Bs i) (iUnion_mono fun i ↦ (hBs i).1.subset_ground)).mpr
        fun i ↦
        (by { rw [inter_iUnion_disjoint hEs (fun i ↦ (hBs i).1.subset_ground)]; exact (hBs i).1 }),
        _, _⟩
      · have : I ⊆ ⋃ i, I ∩ (Ms i).E :=
          fun e he ↦ (by { rw [← inter_iUnion]; exact ⟨he, hIE he⟩ })
        exact this.trans (iUnion_mono fun i ↦ (hBs i).2.1)
      rw [iUnion_subset_iff]
      exact fun i ↦
        (hBs i).2.2.trans (union_subset_union inter_subset_left inter_subset_left)
    })
    (fun _ hI ↦ hI.1)

end Matroid
