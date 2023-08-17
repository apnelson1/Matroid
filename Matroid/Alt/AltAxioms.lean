import Mathlib.Data.Set.Pairwise.Basic
import Matroid.Basic

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


/- dual matroid -/


/- definition of dual where the bases of the dual
   are definitionally the complements of the
   bases of the primal -/
def dual' (M : Matroid α) : Matroid α :=
  matroid_of_base
    M.E
    (fun B ↦ B ⊆ M.E ∧ M.Base (M.E \ B))
    (by {
      obtain ⟨B, hB⟩ := M.exists_base'
      refine' ⟨M.E \ B, _⟩
      simp_rw [sdiff_sdiff_right_self, ge_iff_le, le_eq_subset, inf_eq_inter,
        inter_eq_self_of_subset_right hB.subset_ground]
      exact ⟨diff_subset _ _, hB⟩
    })
    (by {
      rintro B₁ B₂ hB₁ hB₂ x hx

      obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB₂.2.indep.diff (B₁ \ { x })).exists_base_subset_union_base hB₁.2
      rw [←compl_subset_compl,
        ←(disjoint_of_subset_left (diff_subset B₁ {x}) disjoint_sdiff_self_right).sdiff_eq_right,
        ←union_diff_distrib, diff_eq, compl_inter, compl_compl, union_subset_iff,
        compl_subset_compl] at hB''₂

      have hI : ¬ M.Base (M.E \ (B₁ \ {x}))
      · intro g
        have : M.E \ B₁ ⊂ M.E \ (B₁ \ {x})
        · rw [diff_diff_right,
              inter_eq_self_of_subset_right (singleton_subset_iff.mpr (hB₁.1 hx.1)), union_comm,
              ←insert_eq]
          exact ssubset_insert (not_mem_diff_of_mem hx.1)
        exact g.not_base_of_ssubset this hB₁.2

      have hssu : B₁ \ {x} ⊂ B''ᶜ ∩ M.E :=
        (subset_inter (hB''₂.2) ((diff_subset B₁ {x}).trans hB₁.1)).ssubset_of_ne 
          (by { rintro g; apply hI; rw [g]; convert hB''; simp [hB''.subset_ground] })
      obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ :=
        exists_of_ssubset hssu
      refine' (em (x = e)).elim
        (by {rintro rfl; exfalso; exact heB'' (hB''₁ ⟨⟨hB₁.1 hx.1, hx.2⟩, heI⟩)}) (fun hxe ↦ ⟨e, _⟩)
      simp_rw [mem_diff, insert_subset_iff, and_iff_left heI, and_iff_right heE,
        and_iff_right ((diff_subset B₁ {x}).trans hB₁.1)]
      refine' ⟨by_contra (fun heX ↦ heB'' (hB''₁ ⟨_, heI⟩)), _⟩
      · rw [not_and_or, not_not] at heX
        refine' heX.elim (fun g ↦ ⟨heE, g⟩) (fun g ↦ _)
        · rw [mem_diff, not_and, not_not] at heI
          rw [←mem_singleton_iff.mp (heI g)] at hx
          exact ⟨heE, hx.2⟩
      · rw [insert_eq, diff_eq, compl_union, diff_eq, compl_inter, compl_compl,
            inter_distrib_left, inter_eq_self_of_subset_right (singleton_subset_iff.mpr
            (mem_compl_singleton_iff.mpr hxe)), inter_distrib_left,
            inter_eq_self_of_subset_right (singleton_subset_iff.mpr (hB₁.1 hx.1)), 
            inter_comm {e}ᶜ _, ←inter_assoc, ←diff_eq M.E _, ←diff_eq, union_comm, ←insert_eq]
        have : B'' ⊆ insert x ((M.E \ B₁) \ {e})
        · have : e ∈ B''ᶜ ∩ M.E := ⟨heB'', heE⟩
          have : {e} ∪ B₁ \ {x} ⊆ B''ᶜ ∩ M.E :=
            union_subset (singleton_subset_iff.mpr this) hssu.subset
          rw [inter_comm, ←diff_eq] at this
          have : M.E \ (M.E \ B'') ⊆ M.E \ ({e} ∪ B₁ \ {x}) :=
            diff_subset_diff_right this
          rw [diff_diff_cancel_left hB''.subset_ground, diff_eq, diff_eq, compl_union,
              compl_inter, compl_compl, inter_union_distrib_left, inter_comm _ B₁ᶜ,
              inter_eq_self_of_subset_right (singleton_subset_iff.mpr
              (mem_compl_singleton_iff.mpr hxe)), inter_union_distrib_left, ←inter_assoc,
              ←diff_eq, ←diff_eq,
              inter_eq_self_of_subset_right (singleton_subset_iff.mpr (hB₁.1 hx.1)), union_comm,
              ←insert_eq] at this
          exact this
        rw [diff_eq, mem_inter_iff, not_and', mem_compl_singleton_iff] at heI
        rwa [←hB₁.2.eq_exchange_of_subset hB'' ⟨heE, heI (Ne.symm hxe)⟩ this]
    })
    (by {
      rintro X hX I' ⟨Bt, ⟨hBt, hI'B⟩⟩ hI'X

      set B := M.E \ Bt
      have : Bt = M.E \ B :=
        (diff_diff_cancel_left hBt.1).symm
      rw [this] at hI'B; clear this
      
      obtain ⟨-, hB⟩ := hBt
      have hI'E := hI'B.trans (diff_subset M.E B)
      have hI'B : Disjoint I' B :=
        (subset_diff.mp hI'B).2  
      
      obtain ⟨I, hI⟩ :=  M.exists_basis (M.E \ X)
      obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB

      refine' ⟨(X \ B') ∩ M.E,
        ⟨⟨M.E \ B', ⟨⟨diff_subset _ _, by { rwa [diff_diff_cancel_left hB'.subset_ground] }⟩,
         (inter_subset_left (X \ B') M.E).trans (diff_subset_diff_left hX)⟩⟩,
         ⟨subset_inter_iff.mpr ⟨_, hI'X.trans hX⟩,
          (inter_subset_left (X \ B') M.E).trans (diff_subset X B')⟩⟩, _⟩
      · rw [subset_diff, and_iff_right hI'X]
        refine' disjoint_of_subset_right hB'IB _
        rw [disjoint_union_right, and_iff_left hI'B]
        exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right

      simp only [mem_setOf_eq, subset_inter_iff, and_imp, forall_exists_index]

      rintro J Bt h₁Bt hB'' hJBt _ hJX hssJ

      set B'' := M.E \ Bt
      have hJE := hJBt.trans h₁Bt
      have hdj : Disjoint J B''
      · have : J ⊆ M.E \ B''
        · rwa [diff_diff_cancel_left h₁Bt]
        exact (subset_diff.mp this).2
      clear h₁Bt; clear hJBt

      rw [and_iff_left hJE]
      rw [diff_eq, inter_right_comm, ←diff_eq, diff_subset_iff] at hssJ
  
      have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B'
      · rw [union_subset_iff, and_iff_left (diff_subset _ _),
        ←inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc]
        
        calc _ ⊆ _ := inter_subset_inter_right _ hssJ 
            _ ⊆ _ := by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty] 
            _ ⊆ _ := inter_subset_right _ _
      
      obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB''
      rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I

      have : B₁ = B'
      · refine' hB₁.eq_of_subset_indep hB'.indep (fun e he ↦ _)
        refine' (hB₁I he).elim (fun heB'' ↦ _) (fun h ↦ h.1)
        refine' (em (e ∈ X)).elim (fun heX ↦ hI' (Or.inl ⟨heB'', heX⟩)) (fun heX ↦ hIB' _)
        refine' hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ 
          (hB₁.indep.subset (insert_subset he _))
        refine' (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁
        refine' disjoint_of_subset_left hI.subset disjoint_sdiff_left 
      subst this 

      refine' subset_diff.mpr ⟨hJX, by_contra (fun hne ↦ _)⟩
      obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne
      obtain (heB'' | ⟨-,heX⟩ ) := hB₁I heB'
      · exact hdj.ne_of_mem heJ heB'' rfl
      exact heX (hJX heJ)
    })
    (fun B hB ↦ hB.1)

/- end of dual matroid -/

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
    rw [←subset_empty_iff.mp hI.2]
    exact hI.1
  })
  (fun I J hI hIJ ↦ h_subset hI hIJ)
  (by {
    rintro I B hI h'I hB
    obtain ⟨B', hB'⟩ := h_basis hI hB
    obtain ⟨x, hx⟩ : ∃ x, x ∈ B' \ I := by {
      simp_rw [mem_diff]
      by_contra' h
      rw [←subset_def] at h
      have : I = B' := subset_antisymm (hB'.2.1) (h)
      subst this
      exact h'I hB'.1
    }
    have hxB : x ∈ B := by
      have := hB'.2.2 hx.1 
      rw [mem_union] at this
      rcases this with g | g
      · { exfalso
          exact hx.2 g }
      · { exact g }
    have : insert x I ⊆ B' := by
      rw [insert_eq, union_subset_iff, singleton_subset_iff]
      exact ⟨hx.1, hB'.2.1⟩
    exact ⟨x, ⟨hxB, hx.2⟩, h_subset hB'.1.1 this⟩
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

lemma maximal_union_iff {ι : Type _} (Is : ι → Set α) (hIs : Pairwise (Disjoint on Is))
    (h_global : Set α → Prop) (h_local  : ι → Set α → Prop)
    (h : h_global (iUnion Is) ↔ ∀ i, h_local i (Is i)) :
    (iUnion Is) ∈ maximals (· ⊆ ·) { X | h_global X } ↔
      ∀ i, (Is i) ∈ maximals (· ⊆ ·) { X | h_local i X } :=
  sorry

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
          (fun i I ↦ (Ms i).Indep I)
          ⟨fun ⟨_, h⟩ ↦ (by {simp_rw [inter_union_disjoint hEs
            (fun i ↦ inter_subset_right I (Ms i).E)] at h; exact h}),
          fun h ↦ ⟨iUnion_mono fun i ↦ inter_subset_right _ _,
          (by { simp_rw [inter_union_disjoint hEs (fun i ↦ inter_subset_right I (Ms i).E)]; exact h })⟩⟩
        rw [←hI] at this
        refine' ⟨fun h i ↦
          (by { have := this.mp h i; rwa [←setOf_base_eq_maximals_setOf_indep] at this }),
          fun h ↦ _⟩
        · have g : ∀ (i : ι), I ∩ (Ms i).E ∈ maximals (· ⊆ ·) {X | (Ms i).Indep X} :=
            fun i ↦ (by { rw [←setOf_base_eq_maximals_setOf_indep]; exact h i })
          exact this.mpr g
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


/-

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

/-- `matroid_of_indep_of_bdd` constructs a `FiniteRk` matroid. -/
instance (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) → 
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) 
    (h_support : ∀ I, Indep I → I ⊆ E) : 
    Matroid.FiniteRk (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support) := by
  
  refine' (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).exists_base.elim 
    (fun B hB ↦ hB.finiteRk_of_finite _)
  obtain ⟨n, h_bdd⟩ := h_bdd
  refine' finite_of_encard_le_coe (h_bdd _ _)
  rw [←matroid_of_indep_of_bdd_apply E Indep, indep_iff_subset_base]
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

/-- A collection of Bases with the exchange property and at least one finite member is a matroid -/
def matroid_of_exists_finite_base {α : Type _} (E : Set α) (Base : Set α → Prop) 
    (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : ExchangeProperty Base) 
    (support : ∀ B, Base B → B ⊆ E) : Matroid α := 
  matroid_of_base E Base 
    (by { obtain ⟨B,h⟩ := exists_finite_base; exact ⟨B,h.1⟩ }) base_exchange 
    (by {
      obtain ⟨B, hB, hfin⟩ := exists_finite_base
      refine' fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd 
        ⟨B.ncard, fun Y ⟨B', hB', hYB'⟩ ↦ _⟩ X
      rw [hfin.cast_ncard_eq, encard_base_eq_of_exch base_exchange hB hB']
      exact encard_mono hYB' })
    support

@[simp] theorem matroid_of_exists_finite_base_apply {α : Type _} (E : Set α) (Base : Set α → Prop) 
    (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : ExchangeProperty Base) 
    (support : ∀ B, Base B → B ⊆ E) : 
    (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support).Base = Base := 
  rfl 

/-- A matroid constructed with a finite Base is `FiniteRk` -/
instance {E : Set α} {Base : Set α → Prop} {exists_finite_base : ∃ B, Base B ∧ B.Finite} 
    {base_exchange : ExchangeProperty Base} {support : ∀ B, Base B → B ⊆ E} : 
    Matroid.FiniteRk 
      (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support) := 
  ⟨exists_finite_base⟩  

def matroid_of_base_of_finite {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_base : ∃ B, Base B) (base_exchange : ExchangeProperty Base)
    (support : ∀ B, Base B → B ⊆ E) : Matroid α :=
  matroid_of_exists_finite_base E Base 
    (by { obtain ⟨B,hB⟩ := exists_base; exact ⟨B,hB, hE.subset (support _ hB)⟩ }) 
    base_exchange support

@[simp] theorem matroid_of_base_of_finite_apply {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_base : ∃ B, Base B) (base_exchange : ExchangeProperty Base)
    (support : ∀ B, Base B → B ⊆ E) : 
    (matroid_of_base_of_finite hE Base exists_base base_exchange support).Base = Base := rfl 

/-- A collection of subsets of a finite ground set satisfying the usual independence axioms 
  determines a matroid -/
def matroid_of_indep_of_finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α := 
  matroid_of_indep_of_bdd_augment E Indep h_empty ind_mono 
  ( fun I J hI hJ hlt ↦ ind_aug hI hJ ( by
      rwa [←Nat.cast_lt (α := ℕ∞), (hE.subset (h_support hJ)).cast_ncard_eq, 
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
-- def bRestr (M : Matroid α) {B₀ R : Set α} (hB₀ : M.Base B₀) (hB₀R : B₀ ⊆ R) (hR : R ⊆ M.E) : 
--     Matroid α where
--   ground := R
--   Base B := M.Base B ∧ B ⊆ R
--   exists_base' := ⟨B₀, ⟨hB₀, hB₀R⟩⟩ 
--   base_exchange' := by
--     rintro B B' ⟨hB, hBR⟩ ⟨hB', hB'R⟩ e he
--     obtain ⟨f, hf⟩ := hB.exchange hB' he
--     refine' ⟨f, hf.1, hf.2, insert_subset (hB'R hf.1.1) ((diff_subset _ _).trans hBR)⟩    
--   maximality' := by
--     rintro X hXR Y ⟨B, ⟨hB, -⟩, hYB⟩ hYX
--     obtain ⟨J, ⟨⟨BJ, hBJ, hJBJ⟩, hJ⟩, hJmax⟩ := M.maximality' X (hXR.trans hR) Y ⟨B, hB, hYB⟩ hYX 
--     simp only [mem_setOf_eq, and_imp, forall_exists_index] at hJmax 
--     obtain ⟨BJ', hBJ', hJBJ'⟩ :=
--       (hBJ.indep.subset hJBJ).subset_basis_of_subset (subset_union_left _ B₀) 
--         (union_subset (hJ.2.trans (hXR.trans hR)) (hB₀R.trans hR))
--     have' hBJ'b := hB₀.base_of_basis_supset (subset_union_right _ _) hBJ'
--     refine' ⟨J, ⟨⟨BJ', ⟨hBJ'b, hBJ'.subset.trans (union_subset (hJ.2.trans hXR) hB₀R)⟩, hJBJ'⟩,hJ⟩, 
--       fun K ⟨⟨BK, ⟨hBK, _⟩, hKBK⟩, hYK, hKX⟩ hKJ ↦ hJmax BK hBK hKBK hYK hKX hKJ⟩
--   subset_ground' := by tauto

