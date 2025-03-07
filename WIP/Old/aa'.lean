import Mathlib.Data.Set.Pairwise.Basic
import Matroid.Basic

open Set

namespace Matroid

/- complement API -/
lemma compl_ground {A B E : Set α} (h : A ⊆ E) : A \ B = A ∩ (E \ B) := by
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left h]

lemma disjoint_of_diff_subset {A B C : Set α} (h : A ⊆ B) : Disjoint A (C \ B) :=
  disjoint_of_subset_left h disjoint_sdiff_right

lemma compl_diff_compl_iff (A B E : Set α) (h : A ⊆ E) : A \ B = (E \ B) \ (E \ A) := by
  ext; aesop

lemma subset_diff_comm {s t r : Set α} (hs : s ⊆ r) (ht : t ⊆ r) : s ⊆ r \ t ↔ t ⊆ r \ s := by
  rw [subset_diff, subset_diff, disjoint_comm, and_iff_right hs, and_iff_right ht]

lemma ssubset_diff_comm {s t r : Set α} (hs : s ⊆ r) (ht : t ⊆ r) : s ⊂ r \ t ↔ t ⊂ r \ s := by
  rw [ssubset_iff_subset_not_subset, ssubset_iff_subset_not_subset, diff_subset_iff,
    diff_subset_iff, union_comm, subset_diff_comm hs ht]


/- end of complement API -/

/- singleton API -/
lemma inter_singleton_eq_self {a : α} {s : Set α} :
    s ∩ {a} = {a} ↔ a ∈ s := by
  simp [Set.ext_iff]

lemma diff_diff_singleton {a : α} {s t : Set α} (hs : a ∈ s) :
    s \ (t \ {a}) = insert a (s \ t) := by
  ext x
  rw [mem_diff, mem_diff, mem_singleton_iff, mem_insert_iff, mem_diff, not_and, not_not,
    or_iff_not_imp_right, not_and, not_not]
  exact ⟨fun h h' ↦ h.2 (h' h.1),
    fun h ↦ ⟨by_contra fun hx ↦ ((h (False.elim ∘ hx)) ▸ hx) hs, fun hxt ↦ h (fun _ ↦ hxt)⟩⟩

/- end of singleton API -/


/- dual matroid -/


/- definition of dual where the bases of the dual
   are definitionally the complements of the
   bases of the primal -/
def dual' (M : Matroid α) : Matroid α :=
  matroid_of_isBase M.E ( fun B ↦ B ⊆ M.E ∧ M.IsBase (M.E \ B) )
    ( by
      obtain ⟨B, hB⟩ := M.exists_isBase'
      refine' ⟨M.E \ B, _⟩
      simp_rw [sdiff_sdiff_right_self, ge_iff_le, le_eq_subset, inf_eq_inter,
        inter_eq_self_of_subset_right hB.subset_ground]
      exact ⟨diff_subset _ _, hB⟩ )
    ( by

      rintro B₁ B₂ hB₁ hB₂ x hx
      have hxE : x ∈ M.E := hB₁.1 hx.1

      obtain ⟨B'', hB'', hB''₁, hB''₂⟩ :=
        (hB₂.2.indep.diff (B₁ \ { x })).exists_isBase_subset_union_isBase hB₁.2

      rw [diff_diff_singleton (show x ∈ M.E \ B₂ from ⟨hxE, hx.2⟩),
        insert_union, ← union_diff_distrib, ← diff_diff_singleton (show x ∈ _ ∪ _ from Or.inr hxE),
        subset_diff] at hB''₂

      have hssu : B₁ \ {x} ⊂ M.E \ B''
      · rw [ssubset_diff_comm (diff_subset.trans hB₁.1) hB''.subset_ground,
          ssubset_iff_subset_ne, subset_diff, and_iff_right hB''.subset_ground,
          and_iff_right hB''₂.2]
        rintro rfl
        rw [diff_diff_singleton hxE] at hB''
        exact hB₁.2.insert_not_isBase (fun h ↦ h.2 hx.1) hB''

      obtain ⟨e, ⟨heE, heB''⟩, heI⟩ := exists_of_ssubset hssu

      refine' (em (x = e)).elim
        (by {rintro rfl; exfalso; exact heB'' (hB''₁ ⟨⟨hB₁.1 hx.1, hx.2⟩, heI⟩)}) (fun hxe ↦ _)

      use e
      simp_rw [mem_diff, insert_subset_iff, and_iff_left heI, and_iff_right heE,
        and_iff_right ((diff_subset B₁ {x}).trans hB₁.1)]
      refine' ⟨by_contra (fun heX ↦ heB'' (hB''₁ ⟨_, heI⟩)), _⟩
      · rw [not_and_or, not_not] at heX
        refine' heX.elim (fun g ↦ ⟨heE, g⟩) (fun g ↦ _)
        · rw [mem_diff, not_and, not_not] at heI
          rw [← mem_singleton_iff.mp (heI g)] at hx
          exact ⟨heE, hx.2⟩

      rw [insert_diff_singleton_comm (Ne.symm hxe), diff_diff_singleton (hB₁.1 hx.1),
        ← union_singleton (a := e), ← diff_diff]

      apply hB₁.2.exchange_isBase_of_indep (fun h ↦ h.2 hx.1)
        (hB''.indep.subset (insert_subset (hB''₁ ⟨⟨hB₁.1 hx.1,hx.2⟩,fun h ↦ h.2 rfl⟩) _))


      -- rw [diff_diff, diff_subset_comm]




      )



          -- have : M.E \ insert e (B₁ \ {x}) = insert x ((M.E \ B₁) \ {e})
          -- . rw [insert_diff_singleton_comm (Ne.symm hxe), diff_diff_singleton (hB₁.1 hx.1),
          --     diff_diff, union_singleton]



          -- -- rw [this]
          -- have : M.Indep (insert x ((M.E \ B₁) \ {e})) := sorry
          -- -- by subset of B''
          -- have : M.IsBase  (insert x ((M.E \ B₁) \ {e})) :=
          --   IsBase.exchange_isBase_of_indep hB₁.2 (not_mem_diff_of_mem hx.1) this
          -- exact this


    ( by
          unfold ExistsMaximalSubsetProperty
      simp only [forall_exists_index, and_imp]
      rintro X hX I Y hY hYb hIY hIX
      obtain ⟨J, hJ⟩ := M.exists_isBasis (M.E \ X)
      obtain ⟨B', hB', hJB', hB'JB⟩ := hJ.indep.exists_isBase_subset_union_isBase hYb

      use X \ B'
      rw [mem_maximals_setOf_iff]
      refine ⟨⟨⟨M.E \ B', ⟨diff_subset _ _,by rwa [diff_diff_cancel_left hB'.subset_ground]⟩,
        diff_subset_diff hX Subset.rfl⟩,
        ?_,diff_subset _ _⟩, ?_⟩
      · rw [subset_diff, and_iff_right hIX]
        apply disjoint_of_subset_right hB'JB (disjoint_union_right.2 ⟨
            disjoint_of_subset_left hIX (subset_diff.1 hJ.subset).2.symm,
            disjoint_of_subset_left hIY disjoint_sdiff_right⟩)
      rintro Z ⟨⟨B'', ⟨hB''E, hB''⟩, hZB''⟩,h⟩ hXB'Z

      -- rintro X hX I' ⟨Bt, ⟨hBt, hI'B⟩⟩ hI'X

      -- set B := M.E \ Bt
      -- have : Bt = M.E \ B :=
      --   (diff_diff_cancel_left hBt.1).symm
      -- rw [this] at hI'B; clear this

      -- obtain ⟨-, hB⟩ := hBt
      -- have hI'E := hI'B.trans (diff_subset M.E B)
      -- have hI'B : Disjoint I' B :=
      --   (subset_diff.mp hI'B).2

      -- obtain ⟨I, hI⟩ :=  M.exists_isBasis (M.E \ X)
      -- obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_isBase_subset_union_isBase hB

      -- refine' ⟨(X \ B') ∩ M.E,
      --   ⟨⟨M.E \ B', ⟨⟨diff_subset _ _, by { rwa [diff_diff_cancel_left hB'.subset_ground] }⟩,
      --    (inter_subset_left (X \ B') M.E).trans (diff_subset_diff_left hX)⟩⟩,
      --    ⟨subset_inter_iff.mpr ⟨_, hI'X.trans hX⟩,
      --     (inter_subset_left (X \ B') M.E).trans (diff_subset X B')⟩⟩, _⟩
      -- · rw [subset_diff, and_iff_right hI'X]
      --   refine' disjoint_of_subset_right hB'IB _
      --   rw [disjoint_union_right, and_iff_left hI'B]
      --   exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right

      -- simp only [mem_setOf_eq, subset_inter_iff, and_imp, forall_exists_index]

      -- rintro J Bt h₁Bt hB'' hJBt _ hJX hssJ

      -- set B'' := M.E \ Bt
      -- have hJE := hJBt.trans h₁Bt
      -- have hdj : Disjoint J B''
      -- · have : J ⊆ M.E \ B''
      --   · rwa [diff_diff_cancel_left h₁Bt]
      --   exact (subset_diff.mp this).2
      -- clear h₁Bt; clear hJBt

      -- rw [and_iff_left hJE]
      -- rw [diff_eq, inter_right_comm, ← diff_eq, diff_subset_iff] at hssJ

      -- have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B'
      -- · rw [union_subset_iff, and_iff_left diff_subset,
      --   ← inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc]

      --   calc _ ⊆ _ := inter_subset_inter_right _ hssJ
      --       _ ⊆ _ := by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty]
      --       _ ⊆ _ := inter_subset_right

      -- obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_isBase_subset_union_isBase hB''
      -- rw [union_comm, ← union_assoc, union_eq_self_of_subset_right inter_subset_left] at hB₁I

      -- have : B₁ = B'
      -- · refine' hB₁.eq_of_subset_indep hB'.indep (fun e he ↦ _)
      --   refine' (hB₁I he).elim (fun heB'' ↦ _) (fun h ↦ h.1)
      --   refine' (em (e ∈ X)).elim (fun heX ↦ hI' (Or.inl ⟨heB'', heX⟩)) (fun heX ↦ hIB' _)
      --   refine' hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩
      --     (hB₁.indep.subset (insert_subset he _))
      --   refine' (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁
      --   refine' disjoint_of_subset_left hI.subset disjoint_sdiff_left
      -- subst this

      -- refine' subset_diff.mpr ⟨hJX, by_contra (fun hne ↦ _)⟩
      -- obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne
      -- obtain (heB'' | ⟨-,heX⟩ ) := hB₁I heB'
      -- · exact hdj.ne_of_mem heJ heB'' rfl
      -- exact heX (hJX heJ)

       )
    (fun B hB ↦ hB.1)

/- end of dual matroid -/

/-
def matroid_of_indep_of_forall_subset_isBase (E : Set α) (Indep : Set α → Prop)
  (h_exists_maximal_indep_subset : ∀ X, X ⊆ E → ∃ I, I ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X})
  (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
  (h_isBasis : ∀ ⦃I I'⦄, Indep I → I' ∈ maximals (· ⊆ ·) {I | Indep I} →
    ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I} ∧ I ⊆ B ∧ B ⊆ I ∪ I')
  (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α :=
  -- made `I` implicit in this def's `h_support`, unlike in that of `matroid_of_indep`
  matroid_of_indep E Indep
  (by {
    obtain ⟨I, ⟨hI, -⟩⟩ := h_exists_maximal_indep_subset ∅ (empty_subset _)
    rw [← subset_empty_iff.mp hI.2]
    exact hI.1
  })
  (fun I J hI hIJ ↦ h_subset hI hIJ)
  (by {
    rintro I B hI h'I hB
    obtain ⟨B', hB'⟩ := h_isBasis hI hB
    obtain ⟨x, hx⟩ : ∃ x, x ∈ B' \ I := by {
      simp_rw [mem_diff]
      by_contra! h
      rw [← subset_def] at h
      have : I = B' := subset_antisymm (hB'.2.1) (h)
      subst this
      exact h'I hB'.1
    }
    have hxB : x ∈ B := by
      have := hB'.2.2 hx.1
      rw [mem_union] at this
      rcases this with g | g
      . { exfalso
          exact hx.2 g }
      . { exact g }
    have : insert x I ⊆ B' := by
      rw [insert_eq, union_subset_iff, singleton_subset_iff]
      exact ⟨hx.1, hB'.2.1⟩
    exact ⟨x, ⟨hxB, hx.2⟩, h_subset hB'.1.1 this⟩
  })
  (by {
    let IsBase   : Set α → Prop := maximals (· ⊆ ·) { I | Indep I }
    let IsBase'  : Set α → Prop := { B | B ⊆ E ∧ IsBase (E \ B) }
    let Indep' : Set α → Prop := { I | ∃ B, IsBase' B ∧ I ⊆ B }

    have dual_subset : ∀ I J, Indep' J → I ⊆ J → Indep' I :=
      fun I J ⟨B, hB⟩ hIJ ↦ ⟨B, hB.1, hIJ.trans hB.2⟩

    have dual_isBase_compl : ∀ B, IsBase B → IsBase' (E \ B) := by
      rintro B hB
      rw [← diff_diff_cancel_left (h_support hB.1)] at hB
      exact ⟨diff_subset _ _, hB⟩

    have dual_isBase_indep : ∀ ⦃B⦄, IsBase' B → Indep' B :=
      fun B hB ↦ ⟨B, hB, subset_refl _⟩

    have dual_support : ∀ I, Indep' I → I ⊆ E :=
      fun I ⟨B, hB⟩ ↦ hB.2.trans hB.1.1

    have dual_indep_maximals_eq_dual_isBase : maximals (· ⊆ ·) {I | Indep' I } = IsBase' := by
      ext X
      refine' ⟨fun ⟨⟨B, hB⟩, hX⟩ ↦ _, _⟩
      . by_contra! h
        have hX' : X ⊂ B := by
          rw [ssubset_iff_subset_ne]
          refine' ⟨hB.2, _⟩
          rintro rfl
          exact h hB.1
        exact hX'.not_subset (hX (dual_isBase_indep hB.1) hX'.subset)
      . rintro hX
        rw [maximals]
        by_contra! h
        dsimp at h
        push_neg at h
        obtain ⟨I, ⟨hI, hXI, hIX⟩⟩ := h ⟨X, hX, subset_refl X⟩
        obtain ⟨B, ⟨hB, hIB⟩⟩ := hI

        have hXc : IsBase (E \ X) := hX.2
        have hBc : IsBase (E \ B) := hB.2
        have hBcXc := (compl_ssubset hX.1 hB.1 (ssubset_of_ssubset_of_subset ⟨hXI, hIX⟩ hIB))

        exact hBcXc.not_subset (hBc.2 hXc.1 hBcXc.subset)


    have aux0 : ∀ I, IsBase I → (E \ I) ∈ maximals (· ⊆ ·) { I | Indep' I } := by {
      rintro I hI
      rw [dual_indep_maximals_eq_dual_isBase]
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
        have hB : IsBase B := hT.1.2
        have hI'B : Disjoint I' B := disjoint_of_subset_left hT.2 disjoint_sdiff_right


        rw [dual_indep_maximals_eq_dual_isBase] at hBt
        let B' := E \ Bt
        have hB' : IsBase B' := hBt.2

        obtain ⟨B'', hB''⟩ := @h_isBasis (B' \ I') B (h_subset hB'.1 diff_subset) hB

        refine' ⟨E \ B'', _, _, _⟩
        . rw [dual_indep_maximals_eq_dual_isBase]
          exact dual_isBase_compl B'' hB''.1
        . rintro e he
          use hT.1.1 (hT.2 he)
          rintro he'
          have := hB''.2.2 he'
          rw [mem_union] at this
          rcases this with g | g
          . exact g.2 he
          . exact (singleton_nonempty e).not_subset_empty
             (@hI'B {e} (singleton_subset_iff.mpr he) (singleton_subset_iff.mpr g))
        . {
          have : E \ B'' ⊆ E \ (B' \ I') := diff_subset_diff_right hB''.2.1
          rw [compl_ground (diff_subset E Bt), diff_inter,
              (diff_diff_cancel_left hBt.1), (diff_diff_cancel_left (hT.2.trans hT.1.1)),
              union_comm] at this
          exact this
        }

    have aux2' : ∀ X B, X ⊆ E → IsBase B →
        (B ∩ X ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X} →
        (E \ B) ∩ (E \ X) ∈ maximals (· ⊆ ·) {I' | Indep' I' ∧ I' ⊆ (E \ X)}) := by
      rintro X B hX hB hBX
      refine' ⟨_, _⟩
      . refine' ⟨_, inter_subset_right⟩
        . refine' ⟨(E \ B), _, inter_subset_left⟩
          have : IsBase (E \ (E \ B)) := by
            rw [diff_diff_right_self, inter_eq_self_of_subset_right (h_support hB.1)]
            exact hB
          exact ⟨diff_subset _ _, this⟩
      . by_contra! g
        obtain ⟨B', hB'⟩ : ∃ B', IsBase B' ∧ (B' ∩ (E \ X) ⊂ B ∩ (E \ X)) := by
          obtain ⟨I, h⟩ := g
          obtain ⟨⟨Bt, hBt⟩, _⟩ := h.1
          have h₁ : (E \ B) ∩ (E \ X) ⊂ I :=
            ⟨h.2.1, h.2.2⟩
          rw [← inter_eq_self_of_subset_left h.1.2] at h₁
          have h₂ : (E \ I) ∩ (E \ X) ⊂ B ∩ (E \ X) := by {
            have := compl_ssubset_inter diff_subset (hBt.2.trans hBt.1.1) h₁
            rw [diff_diff_cancel_left (h_support hB.1)] at this
            exact this
          }
          use E \ Bt
          use hBt.1.2
          exact ssubset_of_subset_of_ssubset (inter_subset_inter_left _
            (diff_subset_diff_right hBt.2)) h₂
        obtain ⟨I', hI'⟩ := h_isBasis hBX.1.1 hB'.1

        have h₁I'B : I' ∩ X ⊆ B ∩ X := by {
          have := inter_subset_inter_left X hI'.2.1
          rw [inter_eq_self_of_subset_left (inter_subset_right B X)] at this
          exact hBX.2 ⟨h_subset hI'.1.1 inter_subset_left,
                inter_subset_right⟩ this
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

        have hI'B : I' ⊂ B :=
          ssubset_of_subset_of_compl_ssubset (h_support hI'.1.1) (h_support hB.1) h₁I'B h₂I'B

        exact hI'B.not_subset (hI'.1.2 hB.1 hI'B.subset)

    have exists_isBase_contains_indep : ∀ I, Indep I → ∃ B, IsBase B ∧ I ⊆ B := by {
      rintro I hI
      obtain ⟨I', hI'⟩ := h_exists_maximal_indep_subset E (subset_refl _)
      obtain ⟨B, hB⟩ := h_isBasis hI ⟨hI'.1.1, fun X hX hI'X ↦ hI'.2 ⟨hX, h_support hX⟩ hI'X⟩
      exact ⟨B, hB.1, hB.2.1⟩
    }

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
          compl_ssubset_inter (h_support hB.1) (h_support h.1.1) h₁
        have h₃ : (E \ Bt) ∩ X ⊆ (E \ I) ∩ X :=
           inter_subset_inter_left _ (diff_subset_diff_right hBt.2)
        have h₄ : (E \ Bt) ∩ X ⊂ (E \ B) ∩ X :=
           ssubset_of_subset_of_ssubset h₃ h₂
        obtain ⟨I', hI'⟩ := aux1 ((E \ B) ∩ (E \ X)) (E \ Bt) (hBX.1.1) (aux0 Bt hBt.1)

        have h₅ : (E \ B) ∩ (E \ X) ⊆ I' ∩ (E \ X) := by
          rw [← inter_eq_self_of_subset_left (inter_subset_right (E \ B) (E \ X))]
          exact inter_subset_inter_left (E \ X) hI'.2.1

        have h₆ : I' ∩ (E \ X) ⊆ (E \ B) ∩ (E \ X) :=
          hBX.2 ⟨dual_subset _ I' hI'.1.1 inter_subset_left, inter_subset_right⟩ h₅

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
          ssubset_of_subset_of_compl_ssubset' (dual_support I' hI'.1.1) diff_subset hX h₆ h₈

        exact h₉.not_subset (hI'.1.2 (dual_isBase_indep (dual_isBase_compl B hB)) h₉.subset)
      }

    have aux2 : ∀ X B, X ⊆ E → IsBase B →
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
      obtain ⟨B', hB'⟩ := h_isBasis hI'.1.1 hBh

      have I'eq : I' = B' ∩ X :=
        subset_antisymm (subset_inter_iff.mpr ⟨hB'.2.1, hI'.1.2⟩)
          (hI'.2 ⟨h_subset hB'.1.1 inter_subset_left, inter_subset_right⟩
          (subset_inter_iff.mpr ⟨hB'.2.1, hI'.1.2⟩))
      rw [I'eq] at hI'
      have hB'c := (aux2 X B' hX hB'.1).mp hI'

      obtain ⟨B, hB⟩ := h_isBasis hI.1 hB'.1

      have h₁ : B ∩ (E \ X) ⊆ B' ∩ (E \ X) := by {
        have tmp := inter_subset_inter_left (E \ X) hB.2.2
        have : I ∩ (E \ X) ⊆ X ∩ (E \ X) := inter_subset_inter_left _ hI.2
        rw [inter_diff_self _ _, subset_empty_iff] at this
        rw [inter_distrib_right, this, empty_union] at tmp
        exact tmp
      }
      have h₂ : (E \ B') ∩ (E \ X) ⊆ (E \ B) ∩ (E \ X) :=
        compl_subset_inter h₁
      have h₃ : E \ B ∩ (E \ X) ∈ {I' | Indep' I' ∧ I' ⊆ E \ X} := by {
        refine' ⟨⟨E \ B, _, inter_subset_left⟩, inter_subset_right⟩
        have : IsBase (E \ (E \ B)) := by {
          rw [diff_diff_right_self, inter_eq_self_of_subset_right (h_support hB.1.1)]
          exact hB.1
        }
        exact ⟨diff_subset _ _, this⟩
      }
      have hBc := hB'c
      rw [subset_antisymm h₂ (hB'c.2 h₃ h₂), ← aux2 X B hX hB.1] at hBc
      refine' ⟨B ∩ X, hBc, subset_inter_iff.mpr ⟨hB.2.1, hI.2⟩, _⟩
      . calc
          B ∩ X ⊆ (I ∪ B') ∩ X    := inter_subset_inter_left X hB.2.2
          _ = (I ∩ X) ∪ (B' ∩ X)  := inter_distrib_right _ _ _
          _ = I ∪ (B' ∩ X)        := by rw [inter_eq_self_of_subset_left hI.2]
          _ = I ∪ I'              := by rw [← I'eq]

    simp_rw [ExistsMaximalSubsetProperty]
    rintro X hX I hI hIX
    obtain ⟨I', hI'⟩ := h_exists_maximal_indep_subset X hX
    obtain ⟨B, hB⟩ := aux3 X hX I I' ⟨⟨hI, hIX⟩, hI'⟩
    exact ⟨B, ⟨hB.1.1.1, hB.2.1, hB.1.1.2⟩, fun Y hY hBY ↦ hB.1.2 ⟨hY.1, hY.2.2⟩ hBY⟩
  })
  h_support



def directSum {ι : Type*} (Ms : ι → Matroid α)
  (hEs : Pairwise (Disjoint on (fun i ↦ (Ms i).E))) :=
  matroid_of_indep_of_forall_subset_isBase
    (⋃ i, (Ms i).E)
    (fun I ↦ (I ⊆ ⋃ i, (Ms i).E) ∧ ∀ i, (Ms i).Indep (I ∩ (Ms i).E))
    (by {
      rintro X hX
      sorry
    })
    (fun I J hJ hIJ ↦ ⟨hIJ.trans hJ.1,
      fun i ↦ (hJ.2 i).subset
      (subset_inter (inter_subset_left.trans hIJ) inter_subset_right)⟩)
    sorry
    (fun _ hI ↦ hI.1)
-/


/-
--- Def of dual goes here?

/-- If there is an absolute upper bound on the size of a set satisfying `P`, then the
  maximal subset property always holds. -/
theorem Matroid.existsMaximalSubsetProperty_of_bdd {P : Set α → Prop}
    (hP : ∃ (n : ℕ), ∀ Y, P Y → Y.encard ≤ n) (X : Set α) : ExistsMaximalSubsetProperty P X := by
  obtain ⟨n, hP⟩ := hP

  rintro I hI hIX
  have hfin : Set.Finite (ncard '' {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X})
  · rw [finite_iff_bddAbove, bddAbove_def]
    simp_rw [ENat.le_coe_iff] at hP
    use n
    rintro x ⟨Y, ⟨hY,-,-⟩, rfl⟩
    obtain ⟨n₀, heq, hle⟩ := hP Y hY
    rwa [ncard_def, heq, ENat.toNat_coe]
    -- have := (hP Y hY).2
  obtain ⟨Y, hY, hY'⟩ := Finite.exists_maximal_wrt' ncard _ hfin ⟨I, hI, rfl.subset, hIX⟩
  refine' ⟨Y, hY, fun J ⟨hJ, hIJ, hJX⟩ (hYJ : Y ⊆ J) ↦ (_ : J ⊆ Y)⟩
  have hJfin := finite_of_encard_le_coe (hP J hJ)
  refine' (eq_of_subset_of_ncard_le hYJ _ hJfin).symm.subset
  rw [hY' J ⟨hJ, hIJ, hJX⟩ (ncard_le_of_subset hYJ hJfin)]

/-- If there is an absolute upper bound on the size of an independent set, then the maximality axiom
  isn't needed to define a matroid by independent sets. -/
def matroid_of_indep_of_bdd (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n )
    (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_indep E Indep h_empty h_subset h_aug
    (fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd h_bdd X) h_support

@[simp] theorem matroid_of_indep_of_bdd_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n) (h_support : ∀ I, Indep I → I ⊆ E) :
    (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).Indep = Indep := by
  simp [matroid_of_indep_of_bdd]

/-- `matroid_of_indep_of_bdd` constructs a `RankFinite` matroid. -/
instance (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n )
    (h_support : ∀ I, Indep I → I ⊆ E) :
    Matroid.RankFinite (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support) := by

  refine' (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).exists_isBase.elim
    (fun B hB ↦ hB.rankFinite_of_finite _)
  obtain ⟨n, h_bdd⟩ := h_bdd
  refine' finite_of_encard_le_coe (h_bdd _ _)
  rw [← matroid_of_indep_of_bdd_apply E Indep, indep_iff_subset_isBase]
  exact ⟨_, hB, rfl.subset⟩

/-- If there is an absolute upper bound on the size of an independent set, then matroids
  can be defined using an 'augmentation' axiom similar to the standard definition of finite matroids
  for independent sets. -/
def matroid_of_indep_of_bdd_augment (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) :
    Matroid α :=
  matroid_of_indep_of_bdd E Indep h_empty h_subset
    (by
      simp_rw [mem_maximals_setOf_iff, not_and, not_forall, exists_prop, exists_and_left, mem_diff,
        and_imp, and_assoc]
      rintro I B hI hImax hB hBmax
      obtain ⟨J, hJ, hIJ, hne⟩ := hImax hI
      obtain ⟨n, h_bdd⟩ := h_bdd

      have hlt : I.encard < J.encard :=
        (finite_of_encard_le_coe (h_bdd J hJ)).encard_lt_encard (hIJ.ssubset_of_ne hne)
      have hle : J.encard ≤ B.encard
      · refine le_of_not_lt (fun hlt' ↦ ?_)
        obtain ⟨e, he⟩ := ind_aug hB hJ hlt'
        rw [hBmax he.2.2 (subset_insert _ _)] at he
        exact he.2.1 (mem_insert _ _)
      exact ind_aug hI hB (hlt.trans_le hle) )
    h_bdd h_support

@[simp] theorem matroid_of_indep_of_bdd_augment_apply (E : Set α) (Indep : Set α → Prop)
    (h_empty : Indep ∅) (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) :
    (matroid_of_indep_of_bdd_augment E Indep h_empty h_subset ind_aug h_bdd h_support).Indep
      = Indep := by
  simp [matroid_of_indep_of_bdd_augment]

/-- A collection of IsBases with the exchange property and at least one finite member is a matroid -/
def matroid_of_exists_finite_isBase {α : Type*} (E : Set α) (Base : Set α → Prop)
    (exists_finite_isBase : ∃ B, IsBase B ∧ B.Finite) (base_exchange : ExchangeProperty IsBase)
    (support : ∀ B, IsBase B → B ⊆ E) : Matroid α :=
  matroid_of_isBase E IsBase
    (by { obtain ⟨B,h⟩ := exists_finite_isBase; exact ⟨B,h.1⟩ }) base_exchange
    (by {
      obtain ⟨B, hB, hfin⟩ := exists_finite_isBase
      refine' fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd
        ⟨B.ncard, fun Y ⟨B', hB', hYB'⟩ ↦ _⟩ X
      rw [hfin.cast_ncard_eq, encard_isBase_eq_of_exch base_exchange hB hB']
      exact encard_mono hYB' })
    support

@[simp] theorem matroid_of_exists_finite_isBase_apply {α : Type*} (E : Set α) (Base : Set α → Prop)
    (exists_finite_isBase : ∃ B, IsBase B ∧ B.Finite) (base_exchange : ExchangeProperty IsBase)
    (support : ∀ B, IsBase B → B ⊆ E) :
    (matroid_of_exists_finite_isBase E IsBase exists_finite_isBase base_exchange support).IsBase = IsBase :=
  rfl

/-- A matroid constructed with a finite IsBase is `RankFinite` -/
instance {E : Set α} {Base : Set α → Prop} {exists_finite_isBase : ∃ B, IsBase B ∧ B.Finite}
    {base_exchange : ExchangeProperty IsBase} {support : ∀ B, IsBase B → B ⊆ E} :
    Matroid.RankFinite
      (matroid_of_exists_finite_isBase E IsBase exists_finite_isBase base_exchange support) :=
  ⟨exists_finite_isBase⟩

def matroid_of_isBase_of_finite {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_isBase : ∃ B, IsBase B) (base_exchange : ExchangeProperty IsBase)
    (support : ∀ B, IsBase B → B ⊆ E) : Matroid α :=
  matroid_of_exists_finite_isBase E IsBase
    (by { obtain ⟨B,hB⟩ := exists_isBase; exact ⟨B,hB, hE.subset (support _ hB)⟩ })
    base_exchange support

@[simp] theorem matroid_of_isBase_of_finite_apply {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_isBase : ∃ B, IsBase B) (base_exchange : ExchangeProperty IsBase)
    (support : ∀ B, IsBase B → B ⊆ E) :
    (matroid_of_isBase_of_finite hE IsBase exists_isBase base_exchange support).IsBase = IsBase := rfl

/-- A collection of subsets of a finite ground set satisfying the usual independence axioms
  determines a matroid -/
def matroid_of_indep_of_finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_indep_of_bdd_augment E Indep h_empty ind_mono
  ( fun I J hI hJ hlt ↦ ind_aug hI hJ ( by
      rwa [← Nat.cast_lt (α := ℕ∞), (hE.subset (h_support hJ)).cast_ncard_eq,
      (hE.subset (h_support hI)).cast_ncard_eq]) )
  (⟨E.ncard, fun I hI ↦ by { rw [hE.cast_ncard_eq]; exact encard_mono (h_support hI) }⟩ )
  h_support

instance matroid_of_indep_of_finite.Finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
    ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Finite :=
  ⟨hE⟩

instance matroid_of_indep_of_finite_apply {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
    ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Indep = Indep := by
  simp [matroid_of_indep_of_finite]
-/

end Matroid


/- Restrict a matroid to a set containing a known basis. This is a special case of restriction
  and only has auxiliary use -/
-- def bRestr (M : Matroid α) {B₀ R : Set α} (hB₀ : M.IsBase B₀) (hB₀R : B₀ ⊆ R) (hR : R ⊆ M.E) :
--     Matroid α where
--   ground := R
--   IsBase B := M.IsBase B ∧ B ⊆ R
--   exists_isBase' := ⟨B₀, ⟨hB₀, hB₀R⟩⟩
--   base_exchange' := by
--     rintro B B' ⟨hB, hBR⟩ ⟨hB', hB'R⟩ e he
--     obtain ⟨f, hf⟩ := hB.exchange hB' he
--     refine' ⟨f, hf.1, hf.2, insert_subset (hB'R hf.1.1) (diff_subset.trans hBR)⟩
--   maximality' := by
--     rintro X hXR Y ⟨B, ⟨hB, -⟩, hYB⟩ hYX
--     obtain ⟨J, ⟨⟨BJ, hBJ, hJBJ⟩, hJ⟩, hJmax⟩ := M.maximality' X (hXR.trans hR) Y ⟨B, hB, hYB⟩ hYX
--     simp only [mem_setOf_eq, and_imp, forall_exists_index] at hJmax
--     obtain ⟨BJ', hBJ', hJBJ'⟩ :=
--       (hBJ.indep.subset hJBJ).subset_isBasis_of_subset (subset_union_left _ B₀)
--         (union_subset (hJ.2.trans (hXR.trans hR)) (hB₀R.trans hR))
--     have' hBJ'b := hB₀.isBase_of_isBasis_superset subset_union_right hBJ'
--     refine' ⟨J, ⟨⟨BJ', ⟨hBJ'b, hBJ'.subset.trans (union_subset (hJ.2.trans hXR) hB₀R)⟩, hJBJ'⟩,hJ⟩,
--       fun K ⟨⟨BK, ⟨hBK, _⟩, hKBK⟩, hYK, hKX⟩ hKJ ↦ hJmax BK hBK hKBK hYK hKX hKJ⟩
--   subset_ground' := by tauto
