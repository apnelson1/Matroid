import Mathlib.Data.Set.Pairwise.Basic
import Matroid.Basic
import Matroid.Alt.Dual

open Set 

namespace Matroid

/- complement API -/
lemma compl_ground {A B E : Set α} (h : A ⊆ E) : A \ B = A ∩ (E \ B) := by
  rw [←inter_diff_assoc, inter_eq_self_of_subset_left h]

lemma disjoint_of_diff_subset {A B C : Set α} (h : A ⊆ B) : Disjoint A (C \ B) :=
  disjoint_of_subset_left h disjoint_sdiff_right  

lemma compl_diff_compl_iff (A B E : Set α) (h : A ⊆ E) : A \ B = (E \ B) \ (E \ A) := by
  ext; aesop

/- end of complement API -/

/- singleton API -/
lemma inter_singleton_eq_self {a : α} {S : Set α} :
    S ∩ {a} = {a} ↔ a ∈ S :=
  ⟨fun h ↦ singleton_subset_iff.mp (h.symm.subset.trans (inter_subset_left S {a})),
   fun h ↦ subset_antisymm (inter_subset_right _ _) (singleton_subset_iff.mpr ⟨h, mem_singleton _⟩)⟩
/- end of singleton API -/

def matroid_of_indep_of_forall_subset_base (E : Set α) (Indep : Set α → Prop)
  (h_exists_maximal_indep_subset : ∀ X, X ⊆ E → ∃ I, I ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X})
  (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
  (h_basis : ∀ ⦃I I'⦄, Indep I → I' ∈ maximals (· ⊆ ·) {I | Indep I} →
    ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I} ∧ I ⊆ B ∧ B ⊆ I ∪ I')
  (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α :=
  -- made `I` implicit in this def's `h_support`, unlike in that of `matroid_of_indep`
  matroid_of_indep E Indep
  (by {
    obtain ⟨I, ⟨hI, -⟩⟩ := h_exists_maximal_indep_subset ∅ (empty_subset _)
    rw [←subset_empty_iff.mp hI.2]; exact hI.1
  })
  (fun I J hI hIJ ↦ h_subset hI hIJ)
  (by {
    rintro I B hI h'I hB
    obtain ⟨B', hB'⟩ := h_basis hI hB
    have hssu : I ⊂ B' :=
      ssubset_iff_subset_ne.mpr ⟨hB'.2.1, fun h ↦ (by { rw [h] at h'I; exact h'I hB'.1 })⟩
    obtain ⟨x, hx⟩ := exists_of_ssubset hssu
    have hxB : x ∈ B :=
      ((mem_union _ _ _).mp (hB'.2.2 hx.1)).elim (fun g ↦ (by {exfalso; exact hx.2 g})) (fun g ↦ g)
    exact ⟨x, ⟨hxB, hx.2⟩, h_subset hB'.1.1
      (by { rw [insert_eq, union_subset_iff, singleton_subset_iff]; exact ⟨hx.1, hB'.2.1⟩ })⟩
  })
  (by {
    let Base   : Set α → Prop := maximals (· ⊆ ·) { I | Indep I }
    let Base'  : Set α → Prop := { B | B ⊆ E ∧ Base (E \ B) }
    let Indep' : Set α → Prop := { I | ∃ B, Base' B ∧ I ⊆ B }

    have dual_subset : ∀ I J, Indep' J → I ⊆ J → Indep' I :=
      fun I J ⟨B, hB⟩ hIJ ↦ ⟨B, hB.1, hIJ.trans hB.2⟩ 

    have dual_base_compl : ∀ B, Base B → Base' (E \ B) := by
      rintro B hB
      rw [←diff_diff_cancel_left (h_support hB.1)] at hB
      exact ⟨diff_subset _ _, hB⟩

    have dual_base_indep : ∀ ⦃B⦄, Base' B → Indep' B :=
      fun B hB ↦ ⟨B, hB, subset_refl _⟩

    have dual_support : ∀ I, Indep' I → I ⊆ E :=
      fun I ⟨B, hB⟩ ↦ hB.2.trans hB.1.1

    have dual_indep_maximals_eq_dual_base : maximals (· ⊆ ·) {I | Indep' I } = Base' := by
      ext X
      refine' ⟨fun ⟨⟨B, hB⟩, hX⟩ ↦ _, _⟩
      · by_contra' h
        have hX' : X ⊂ B := by
          rw [ssubset_iff_subset_ne]
          refine' ⟨hB.2, _⟩
          rintro rfl
          exact h hB.1
        exact hX'.not_subset (hX (dual_base_indep hB.1) hX'.subset)
      · rintro hX
        rw [maximals]
        by_contra' h
        dsimp at h
        push_neg at h
        obtain ⟨I, ⟨hI, hXI, hIX⟩⟩ := h ⟨X, hX, subset_refl X⟩
        obtain ⟨B, ⟨hB, hIB⟩⟩ := hI

        have hXc : Base (E \ X) := hX.2
        have hBc : Base (E \ B) := hB.2
        sorry
        -- have hBcXc := (compl_ssubset hX.1 hB.1 (ssubset_of_ssubset_of_subset ⟨hXI, hIX⟩ hIB))

        -- exact hBcXc.not_subset (hBc.2 hXc.1 hBcXc.subset)


    have aux0 : ∀ I, Base I → (E \ I) ∈ maximals (· ⊆ ·) { I | Indep' I } := by {
      rintro I hI
      rw [dual_indep_maximals_eq_dual_base]
      use diff_subset _ _
      rw [diff_diff_cancel_left (h_support hI.1)]
      exact hI
    }

    -- Indep' satisfies I3'
    have aux1 : ∀ I I', Indep' I → (I' ∈ maximals (· ⊆ ·) { I' | Indep' I' }) →
                  ∃ B, B ∈ maximals (· ⊆ ·) {I' | Indep' I'} ∧ I ⊆ B ∧ B ⊆ I ∪ I' := by
        rintro I' Bt hI' hBt
        obtain ⟨T, hT⟩ := hI'

        let B := E \ T
        have hB : Base B := hT.1.2
        have hI'B : Disjoint I' B := disjoint_of_subset_left hT.2 disjoint_sdiff_right

  
        rw [dual_indep_maximals_eq_dual_base] at hBt
        let B' := E \ Bt
        have hB' : Base B' := hBt.2
      
        obtain ⟨B'', hB''⟩ := @h_basis (B' \ I') B (h_subset hB'.1 (diff_subset _ _)) hB

        refine' ⟨E \ B'', _, _, _⟩
        · rw [dual_indep_maximals_eq_dual_base]
          exact dual_base_compl B'' hB''.1
        · rintro e he
          use hT.1.1 (hT.2 he)
          rintro he'
          have := hB''.2.2 he'
          rw [mem_union] at this
          rcases this with g | g
          · exact g.2 he
          · exact (singleton_nonempty e).not_subset_empty
             (@hI'B {e} (singleton_subset_iff.mpr he) (singleton_subset_iff.mpr g))
        · {
          have : E \ B'' ⊆ E \ (B' \ I') := diff_subset_diff_right hB''.2.1
          rw [compl_ground (diff_subset E Bt), diff_inter,
              (diff_diff_cancel_left hBt.1), (diff_diff_cancel_left (hT.2.trans hT.1.1)),
              union_comm] at this
          exact this
        }
    
    have aux2' : ∀ X B, X ⊆ E → Base B →
        (B ∩ X ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X} →
        (E \ B) ∩ (E \ X) ∈ maximals (· ⊆ ·) {I' | Indep' I' ∧ I' ⊆ (E \ X)}) := by 
      rintro X B hX hB hBX
      refine' ⟨_, _⟩
      · refine' ⟨_, inter_subset_right _ _⟩
        · refine' ⟨(E \ B), _, inter_subset_left _ _⟩
          have : Base (E \ (E \ B)) := by
            rw [diff_diff_right_self, inter_eq_self_of_subset_right (h_support hB.1)]
            exact hB
          exact ⟨diff_subset _ _, this⟩
      · by_contra' g
        obtain ⟨B', hB'⟩ : ∃ B', Base B' ∧ (B' ∩ (E \ X) ⊂ B ∩ (E \ X)) := by
          obtain ⟨I, h⟩ := g
          obtain ⟨⟨Bt, hBt⟩, _⟩ := h.1
          have h₁ : (E \ B) ∩ (E \ X) ⊂ I :=
            ⟨h.2.1, h.2.2⟩
          rw [←inter_eq_self_of_subset_left h.1.2] at h₁
          have h₂ : (E \ I) ∩ (E \ X) ⊂ B ∩ (E \ X) := by {
            -- have := compl_ssubset_inter (diff_subset _ _) (hBt.2.trans hBt.1.1) h₁
            -- rw [diff_diff_cancel_left (h_support hB.1)] at this
            -- exact this
            sorry
          }
          use E \ Bt
          use hBt.1.2
          exact ssubset_of_subset_of_ssubset (inter_subset_inter_left _ 
            (diff_subset_diff_right hBt.2)) h₂
        obtain ⟨I', hI'⟩ := h_basis hBX.1.1 hB'.1

        have h₁I'B : I' ∩ X ⊆ B ∩ X := by {
          have := inter_subset_inter_left X hI'.2.1
          rw [inter_eq_self_of_subset_left (inter_subset_right B X)] at this
          exact hBX.2 ⟨h_subset hI'.1.1 (inter_subset_left _ _),
                (inter_subset_right _ _)⟩ this
        }
        
        have h₂I'B : I' ∩ (E \ X) ⊂ B ∩ (E \ X) := by {
          have h₁ : I' ∩ (E \ X) ⊆ (B ∩ X ∪ B') ∩ (E \ X) := by {
            exact inter_subset_inter_left (E \ X) hI'.2.2
          }
          have h₂ : (B ∩ X ∪ B') ∩ (E \ X) = B' ∩ (E \ X) := by {
            rw [union_inter_distrib_right, inter_assoc, inter_diff_self, inter_empty, empty_union]
          }
          rw [h₂] at h₁
          exact ssubset_of_subset_of_ssubset h₁ hB'.2
        }

        have hI'B : I' ⊂ B := sorry
          -- ssubset_of_subset_of_compl_ssubset (h_support hI'.1.1) (h_support hB.1) h₁I'B h₂I'B
        
        exact hI'B.not_subset (hI'.1.2 hB.1 hI'B.subset)
    
    have exists_base_contains_indep : ∀ I, Indep I → ∃ B, Base B ∧ I ⊆ B := by {
      rintro I hI
      obtain ⟨I', hI'⟩ := h_exists_maximal_indep_subset E (subset_refl _)
      obtain ⟨B, hB⟩ := h_basis hI ⟨hI'.1.1, fun X hX hI'X ↦ hI'.2 ⟨hX, h_support hX⟩ hI'X⟩
      exact ⟨B, hB.1, hB.2.1⟩
    } 

    have aux2'' : ∀ X B, X ⊆ E → Base B →
        (E \ B) ∩ (E \ X) ∈ maximals (· ⊆ ·) {I' | Indep' I' ∧ I' ⊆ (E \ X)} →
        B ∩ X ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X} := by
      {
        refine' fun X B hX hB hBX ↦ ⟨⟨h_subset hB.1 (inter_subset_left _ _),
          inter_subset_right _ _⟩, _⟩
        by_contra' g
        obtain ⟨I, h⟩ := g

        obtain ⟨Bt, hBt⟩ := exists_base_contains_indep I h.1.1

        have h₁ : B ∩ X ⊂ I :=
          ⟨h.2.1, h.2.2⟩
        rw [←inter_eq_self_of_subset_left h.1.2] at h₁
        have h₂ : (E \ I) ∩ X ⊂ (E \ B) ∩ X :=
          sorry
          -- compl_ssubset_inter (h_support hB.1) (h_support h.1.1) h₁
        have h₃ : (E \ Bt) ∩ X ⊆ (E \ I) ∩ X :=
           inter_subset_inter_left _ (diff_subset_diff_right hBt.2)
        have h₄ : (E \ Bt) ∩ X ⊂ (E \ B) ∩ X :=
           ssubset_of_subset_of_ssubset h₃ h₂
        obtain ⟨I', hI'⟩ := aux1 ((E \ B) ∩ (E \ X)) (E \ Bt) (hBX.1.1) (aux0 Bt hBt.1)

        have h₅ : (E \ B) ∩ (E \ X) ⊆ I' ∩ (E \ X) := by
          rw [←inter_eq_self_of_subset_left (inter_subset_right (E \ B) (E \ X))]
          exact inter_subset_inter_left (E \ X) hI'.2.1
        
        have h₆ : I' ∩ (E \ X) ⊆ (E \ B) ∩ (E \ X) :=
          hBX.2 ⟨dual_subset _ I' hI'.1.1 (inter_subset_left _ _), inter_subset_right _ _⟩ h₅

        have h₇ : I' ∩ X ⊆ (E \ Bt) ∩ X := by
          {
            calc
              I' ∩ X ⊆ ((E \ B) ∩ (E \ X) ∪ (E \ Bt)) ∩ X  := inter_subset_inter_left X hI'.2.2
              _ = ((E \ B) ∩ (E \ X)) ∩ X ∪ ((E \ Bt) ∩ X) := by rw [←inter_distrib_right _ _]
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
          -- ssubset_of_subset_of_compl_ssubset' (dual_support I' hI'.1.1) (diff_subset _ _) hX h₆ h₈

        exact h₉.not_subset (hI'.1.2 (dual_base_indep (dual_base_compl B hB)) h₉.subset)
      }

    have aux2 : ∀ X B, X ⊆ E → Base B →
        (B ∩ X ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X} ↔
        (E \ B) ∩ (E \ X) ∈ maximals (· ⊆ ·) {I' | Indep' I' ∧ I' ⊆ (E \ X)}) :=
      fun X B hX hB ↦ ⟨aux2' X B hX hB, aux2'' X B hX hB⟩

    -- (I3') holds for `Indep ∩ 2^X`
    have aux3 : ∀ X, X ⊆ E →
        (∀ I I', I ∈ {I | Indep I ∧ I ⊆ X } ∧ I' ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X } →
        ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X } ∧ I ⊆ B ∧ B ⊆ I ∪ I') := by
      rintro X hX I I' ⟨hI, hI'⟩
      obtain ⟨Bh, hBh⟩ := h_exists_maximal_indep_subset E (by rfl)

      have : ∀ I, Indep I ∧ I ⊆ E ↔ Indep I :=
        fun I ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, h_support h⟩⟩
      simp_rw [this] at hBh
      obtain ⟨B', hB'⟩ := h_basis hI'.1.1 hBh

      have I'eq : I' = B' ∩ X :=
        subset_antisymm (subset_inter_iff.mpr ⟨hB'.2.1, hI'.1.2⟩)
          (hI'.2 ⟨h_subset hB'.1.1 (inter_subset_left _ _), inter_subset_right _ _⟩
          (subset_inter_iff.mpr ⟨hB'.2.1, hI'.1.2⟩))
      rw [I'eq] at hI'
      have hB'c := (aux2 X B' hX hB'.1).mp hI'

      obtain ⟨B, hB⟩ := h_basis hI.1 hB'.1
      
      have h₁ : B ∩ (E \ X) ⊆ B' ∩ (E \ X) := by {
        have tmp := inter_subset_inter_left (E \ X) hB.2.2
        have : I ∩ (E \ X) ⊆ X ∩ (E \ X) := inter_subset_inter_left _ hI.2
        rw [inter_diff_self _ _, subset_empty_iff] at this
        rw [inter_distrib_right, this, empty_union] at tmp
        exact tmp
      }
      have h₂ : (E \ B') ∩ (E \ X) ⊆ (E \ B) ∩ (E \ X) := 
        sorry
        -- compl_subset_inter h₁
      have h₃ : E \ B ∩ (E \ X) ∈ {I' | Indep' I' ∧ I' ⊆ E \ X} := by {
        refine' ⟨⟨E \ B, _, inter_subset_left _ _⟩, inter_subset_right _ _⟩
        have : Base (E \ (E \ B)) := by {
          rw [diff_diff_right_self, inter_eq_self_of_subset_right (h_support hB.1.1)]
          exact hB.1
        }
        exact ⟨diff_subset _ _, this⟩
      }
      have hBc := hB'c
      rw [subset_antisymm h₂ (hB'c.2 h₃ h₂), ←aux2 X B hX hB.1] at hBc
      refine' ⟨B ∩ X, hBc, subset_inter_iff.mpr ⟨hB.2.1, hI.2⟩, _⟩
      · calc
          B ∩ X ⊆ (I ∪ B') ∩ X    := inter_subset_inter_left X hB.2.2
          _ = (I ∩ X) ∪ (B' ∩ X)  := inter_distrib_right _ _ _
          _ = I ∪ (B' ∩ X)        := by rw [inter_eq_self_of_subset_left hI.2]
          _ = I ∪ I'              := by rw [←I'eq]

    simp_rw [ExistsMaximalSubsetProperty]
    rintro X hX I hI hIX
    obtain ⟨I', hI'⟩ := h_exists_maximal_indep_subset X hX
    obtain ⟨B, hB⟩ := aux3 X hX I I' ⟨⟨hI, hIX⟩, hI'⟩
    exact ⟨B, ⟨hB.1.1.1, hB.2.1, hB.1.1.2⟩, fun Y hY hBY ↦ hB.1.2 ⟨hY.1, hY.2.2⟩ hBY⟩
  })
  h_support


lemma inter_union_disjoint {ι : Type _} {Es Xs : ι → Set α}
    (hEs : Pairwise (Disjoint on (fun i ↦ Es i))) (hIs : ∀ i, Xs i ⊆ Es i) (j : ι) :
    (⋃ i, Xs i) ∩ Es j = Xs j := by
  ext x
  refine' ⟨_, fun hx ↦ ⟨(subset_iUnion (fun i ↦ Xs i) j) hx, hIs j hx⟩⟩
  intro ⟨hx, hxj⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact (em (i = j)).elim (by { rintro rfl; exact hi })
          fun g ↦ (by { exfalso; exact (disjoint_left.mp (hEs g)) ((hIs i) hi) hxj })

lemma maximal_union_iff
    {ι : Type _} [DecidableEq ι]
    (Es : ι → Set α)
    (hEs : Pairwise (Disjoint on Es))
    (Is : ι → Set α)
    (hIs : ∀ i, Is i ⊆ Es i)
    (h_global : Set α → Prop)
    (h_local  : ι → Set α → Prop)
    (h : ∀ (Js : ι → Set α), h_global (iUnion Js) ↔ ∀ i, h_local i (Js i)) :
    ⋃ i, Is i  ∈ maximals (· ⊆ ·) { X | h_global X } ↔
        ∀ i, Is i ∈ maximals (· ⊆ ·) { X | h_local i X } := by
  -- classical
  refine' ⟨_, _⟩
  · rintro h
    have i : ι := sorry  
    have X : Set α := ∅  
    set Js : ι → Set α := fun j ↦ if j = i then X else Is i
    sorry
  sorry

-- lemma maximal_union_iff'
--     {ι : Type _}
--     (Es : ι → Set α)
--     (hEs : Pairwise (Disjoint on Es))
--     (I : Set α)
--     -- (Is : ι → Set α)
--     -- (hIs : ∀ i, Is i ⊆ Es i)
--     -- (h_global : Set α → Prop)
--     (P  : ι → Set α → Prop) 
--     (hP : ∀ i X, P i X → X ⊆ Es i) :
--     -- (h : ∀ (Js : ι → Set α), h_global (iUnion Js) ↔ ∀ i, h_local i (Js i)) :
--     I ∈ maximals (· ⊆ ·) { X | ∀ i, P i (X ∩ Es i) } ↔
--         ∀ i, I ∩ Es i ∈ maximals (· ⊆ ·) { X | P i X } := by
--   refine' ⟨_, _⟩
--   · rintro h
    
--     sorry
--   sorry




-- lemma maximal_union_iff {ι : Type _}
--     (Is : ι → Set α)
--     (hIs : Pairwise (Disjoint on Is))
--     (h_global : Set α → Prop)
--     (h_local  : ι → Set α → Prop)
--     (h : ∀ (Js : ι → Set α), h_global (iUnion Js) ↔ ∀ i, h_local i (Js i))
--     (Js : ι → Set α) :
--     iUnion Js ∈ maximals (· ⊆ ·) { X | h_global X } ↔
--       ∀ i, Js i ∈ maximals (· ⊆ ·) { X | X ⊆ Is i ∧ h_local i X } := by
--   refine' ⟨_, _⟩
--   · rintro hiU i
--     refine' ⟨⟨sorry, (h Js).mp hiU.1 i⟩, _⟩
--     · rintro Bi hBi hJsiBi
--       by_contra' g
--       have hssu : Js i ⊂ Bi := ⟨hJsiBi, g⟩

--       have := (iUnion Js) ∪ Bi
--       sorry
--   sorry

def directSum {ι : Type _} (Ms : ι → Matroid α)
  (hEs : Pairwise (Disjoint on (fun i ↦ (Ms i).E))) :=
  matroid_of_indep_of_forall_subset_base
    (⋃ i, (Ms i).E)
    (fun I ↦ (I ⊆ ⋃ i, (Ms i).E) ∧ ∀ i, (Ms i).Indep (I ∩ (Ms i).E))
    (by {
      rintro X -
      let Xs : ι → Set α := fun i ↦ X ∩ (Ms i).E
      choose! Is hIs using (fun i ↦ exists_basis (Ms i) (Xs i))
      use (⋃ i, Is i)
      have hineq := inter_union_disjoint hEs (fun i ↦ (hIs i).left_subset_ground)
      refine' ⟨⟨⟨iUnion_subset_iff.mpr (fun i ↦ (hIs i).left_subset_ground.trans
        (subset_iUnion (fun i ↦ (Ms i).E) i)), fun i ↦ (by { rw [hineq i]; exact (hIs i).indep })⟩,
         iUnion_subset (fun i ↦ (hIs i).subset.trans (inter_subset_left _ _))⟩, _⟩
      · rintro B ⟨⟨hBEs, hBs⟩, hBX⟩ hB
        have : B ⊆ ⋃ (i : ι), B ∩ (Ms i).E := by
          { rw [←inter_iUnion]; exact fun e he ↦ ⟨he, hBEs he⟩ }
        refine' this.trans (iUnion_mono (fun i ↦ _))
        · have := inter_subset_inter_left (Ms i).E hB
          rw [hineq i] at this
          exact ((hIs i).eq_of_subset_indep (hBs i) this
            (inter_subset_inter_left _ hBX)).symm.subset
    })
    (fun I J hJ hIJ ↦ ⟨hIJ.trans hJ.1,
      fun i ↦ (hJ.2 i).subset
      (subset_inter ((inter_subset_left _ _).trans hIJ) (inter_subset_right _ _))⟩) 
    (by {
      
      -- TODO: factor out aux
      have aux : ∀ I, I ⊆ ⋃ (i : ι), (Ms i).E → ((I ∈ maximals (· ⊆ ·)
        {I | (fun I ↦ I ⊆ ⋃ (i : ι), (Ms i).E ∧ ∀ (i : ι), (Ms i).Indep (I ∩ (Ms i).E)) I}) ↔
        (∀ i, (Ms i).Base (I ∩ (Ms i).E)))
      · rintro I hIE
        have hI : I = iUnion (fun i ↦ (I ∩ (Ms i).E)) := by
          ext e; exact ⟨fun he ↦ (by { rw [←inter_iUnion]; exact ⟨he, hIE he⟩ }),
                        fun he ↦ (by { obtain ⟨i, hi⟩ := mem_iUnion.mp he; exact hi.1 })⟩
        have hIs : Pairwise (Disjoint on (fun i ↦ (I ∩ (Ms i).E))) :=
          fun i j hij ↦ Disjoint.mono (inter_subset_right _ _) (inter_subset_right _ _) (hEs hij)
        have := maximal_union_iff (fun i ↦ (I ∩ (Ms i).E)) hIs
          (fun I ↦ I ⊆ ⋃ (i : ι), (Ms i).E ∧ ∀ (i : ι), (Ms i).Indep (I ∩ (Ms i).E))
          (fun i I ↦ (Ms i).Indep I) ⟨fun ⟨_, h⟩ ↦ (by {simp_rw [inter_union_disjoint hEs
            (fun i ↦ inter_subset_right I (Ms i).E)] at h; exact h}),
          fun h ↦ ⟨iUnion_mono fun i ↦ inter_subset_right _ _,
          (by { simp_rw [inter_union_disjoint hEs (fun i ↦ inter_subset_right I (Ms i).E)]; exact h })⟩⟩
        rw [←hI] at this
        exact ⟨fun h i ↦ (by { have := this.mp h i; rwa [←setOf_base_eq_maximals_setOf_indep] at this }),
          fun h ↦ this.mpr (fun i ↦ (by { rw [←setOf_base_eq_maximals_setOf_indep]; exact h i }))⟩
      -- end of aux

      rintro I I' ⟨hIE, hIs⟩ ⟨⟨hI'E, hI's⟩, hI'max⟩
      choose! Bs hBs using (fun i ↦ (hIs i).exists_base_subset_union_base
                                            (((aux I' hI'E).mp ⟨⟨hI'E, hI's⟩, hI'max⟩) i))
      refine' ⟨⋃ i, Bs i, (aux (⋃ i, Bs i) (iUnion_mono fun i ↦ (hBs i).1.subset_ground)).mpr
        fun i ↦
        (by { rw [inter_union_disjoint hEs (fun i ↦ (hBs i).1.subset_ground)]; exact (hBs i).1 }),
        _, _⟩
      · have : I ⊆ ⋃ i, I ∩ (Ms i).E :=
          fun e he ↦ (by { rw [←inter_iUnion]; exact ⟨he, hIE he⟩ })
        exact this.trans (iUnion_mono fun i ↦ (hBs i).2.1)
      rw [iUnion_subset_iff]
      exact fun i ↦
        (hBs i).2.2.trans (union_subset_union (inter_subset_left _ _) (inter_subset_left _ _))
    })
    (fun _ hI ↦ hI.1)


end Matroid 
