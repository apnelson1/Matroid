import Matroid.Basic
import Mathlib.Data.Set.Pairwise.Basic

open Set 

namespace Matroid

/- complement API -/

lemma compl_subset_inter {A B X E : Set α} (h : A ∩ X ⊆ B ∩ X) :
    (E \ B) ∩ X ⊆ (E \ A) ∩ X :=
  fun _ he ↦ ⟨⟨he.1.1, fun g ↦ he.1.2 (h ⟨g, he.2⟩).1⟩, he.2⟩

lemma compl_ssubset_inter {A B X E : Set α}
  (hA : A ⊆ E)
  (hB : B ⊆ E)
  (h : A ∩ X ⊂ B ∩ X) :
  (E \ B) ∩ X ⊂ (E \ A) ∩ X := by {
    refine' ⟨compl_subset_inter h.subset, fun g ↦ _⟩
    have := @compl_subset_inter α _ _ X E g
    rw [diff_diff_cancel_left hA, diff_diff_cancel_left hB] at this
    exact h.not_subset this
  }

lemma maximal_of_restriction {A B X} (P : Set α → Prop)
    (hP  : ∀ S T, P S → T ⊆ S → P T)
    (hA  : A ∈ maximals (· ⊆ ·) {I | P I ∧ I ⊆ X})
    (hB  : B ∈ maximals (· ⊆ ·) {I | P I})
    (hAB : A ⊆ B) :
    A = B ∩ X :=
  subset_antisymm (subset_inter_iff.mpr ⟨hAB, hA.1.2⟩)
    (hA.2 ⟨(hP (B) (B ∩ X) hB.1 (inter_subset_left _ _)), (inter_subset_right _ _)⟩
    (subset_inter_iff.mpr ⟨hAB, hA.1.2⟩))

lemma compl_ground {A B E : Set α} (h : A ⊆ E) : A \ B = A ∩ (E \ B) :=
  subset_antisymm (fun _ he ↦ ⟨he.1, h he.1, he.2⟩) (fun _ he ↦ ⟨he.1, he.2.2⟩)

lemma compl_subset {A B E : Set α}
    (h  : A ⊆ B) :
    E \ B ⊆ E \ A :=
  fun _ he ↦ ⟨he.1, fun he' ↦ he.2 (h he')⟩

lemma ground_compl_inter {A B E : Set α} :
    E \ (A ∩ B) = (E \ A) ∪ (E \ B) := by
  ext e
  refine' ⟨fun he ↦ _, fun he ↦ _⟩
  . have := he.2
    rw [mem_inter_iff] at this
    push_neg at this
    exact (em (e ∈ A)).elim (fun he' ↦ Or.inr ⟨he.1, this he'⟩) (fun he' ↦ Or.inl ⟨he.1, he'⟩)
  . refine' he.elim (fun he' ↦ ⟨he'.1, _⟩) (fun he' ↦ ⟨he'.1, _⟩)
    . rw [mem_inter_iff, not_and_or]
      exact Or.inl he'.2
    . rw [mem_inter_iff, not_and_or]
      exact Or.inr he'.2

lemma compl_ssubset {A B E : Set α}
    (hA : A ⊆ E)
    (hB : B ⊆ E)
    (hAB  : A ⊂ B) :
    E \ B ⊂ E \ A := by
  refine' ⟨compl_subset hAB.1, fun h ↦ _⟩
  have := @compl_subset α (E \ A) (E \ B) E h
  rw [diff_diff_cancel_left hB, diff_diff_cancel_left hA] at this
  exact hAB.not_subset this

lemma ssubset_of_subset_of_compl_ssubset {A B X E : Set α}
    (hA : A ⊆ E)
    (hB : B ⊆ E)
    (h₁ : A ∩ X ⊆ B ∩ X)
    (h₂ : A ∩ (E \ X) ⊂ B ∩ (E \ X)) :
    A ⊂ B := by
  rw [ssubset_iff_subset_ne]
  refine' ⟨fun e he ↦ (em (e ∈ X)).elim
    (fun g ↦ (h₁ ⟨he, g⟩).1) (fun g ↦ (h₂.subset ⟨he, ⟨hA he, g⟩⟩).1), _⟩
  rintro rfl
  exact h₂.not_subset (subset_refl _)

lemma ssubset_of_subset_of_compl_ssubset' {A B X E : Set α}
    (hA : A ⊆ E)
    (hB : B ⊆ E)
    (hX : X ⊆ E)
    (h₁ : A ∩ (E \ X) ⊆ B ∩ (E \ X))
    (h₂ : A ∩ X ⊂ B ∩ X) :
    A ⊂ B := by
  let Y := E \ X
  have g₂ : A ∩ (E \ Y) ⊂ B ∩ (E \ Y) := by
    rw [diff_diff_cancel_left hX]
    exact h₂
  exact ssubset_of_subset_of_compl_ssubset hA hB h₁ g₂ 

lemma ssubset_of_subset_of_compl_ssubset'' {A B : Set α}
    (h₁ : A ∩ X ⊂ B ∩ X)
    (h₂ : A \ X ⊆ B \ X) :
    A ⊂ B := by
  sorry


lemma ssubset_of_ssubset_of_compl_subset'' {A B X : Set α}
    (h₁ : A ∩ X ⊆ B ∩ X)
    (h₂ : A \ X ⊂ B \ X) :
    A ⊂ B := by
  sorry

lemma diff_ssubset_of_ssubset_of_subset_inter {A B X : Set α}
  (h₁ : A ⊂ B)
  (h₂ : A ∩ X ⊆ B ∩ X) :
  A \ X ⊂ B \ X := by
sorry

lemma disjoint_of_diff_subset {A B C : Set α}
    (h : A ⊆ B) :
    Disjoint A (C \ B) := by
  rw [←subset_compl_iff_disjoint_right, diff_eq, compl_inter, compl_compl]
  exact h.trans (subset_union_right _ _)

lemma compl_diff_compl_iff {x : α} (A B E : Set α) :
  x ∈ A \ B ↔ x ∈ (E \ B) \ (E \ A) :=
sorry


lemma compl_diff_compl' {x : α} (A B E : Set α)
  (h : x ∈ A \ B) :
  x ∈ (E \ B) \ (E \ A) :=
sorry

lemma aux {X A B : Set α} :
    X ∩ Aᶜ ⊂ X ∩ Bᶜ ↔ X ∩ B ⊂ X ∩ A := by
  sorry

/- end of complement API -/

/- singleton API -/
lemma inter_singleton_eq_self {a : α} {S : Set α} :
    S ∩ {a} = {a} ↔ a ∈ S :=
  sorry
/- end of singleton API -/

/- ExistsMaximalSubset reformulation -/
/- end of ExistsMaximalSubset reformulation-/


/- dual matroid -/

/- (B2)* from Oxley -/
theorem Base.exchange' {M : Matroid α} (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hx : e ∈ B₂ \ B₁) :
    ∃ y ∈ B₁ \ B₂, M.Base (insert e (B₁ \ {y})) :=
  sorry

/- Indep.exists_base_subset_union_base without relying on Indep -/
theorem exists_base_subset_union_base'
      {M : Matroid α}
      {Bi : Set α} (hBi : M.Base Bi) (hI : I ⊆ Bi)  -- I is indep
      (hB : M.Base B) :
    ∃ B', M.Base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B := by
  sorry

theorem not_base_of_ssubset
    {M : Matroid α} {I B : Set α} (hB : M.Base B) (hI : I ⊂ B) :
    ¬ M.Base I := by
  sorry

/- definition of dual where the bases of the dual
   are definitionally the complements of the
   bases of the primal -/
def dual' (M : Matroid α) : Matroid α :=
  matroid_of_base
    M.E
    (fun B ↦ B ⊆ M.E ∧ M.Base (M.E \ B))
    -- `B ⊆ M.E` is not needed often
    (by {
      obtain ⟨B, hB⟩ := M.exists_base'
      refine' ⟨M.E \ B, _⟩
      simp_rw [sdiff_sdiff_right_self, ge_iff_le, le_eq_subset, inf_eq_inter,
        inter_eq_self_of_subset_right hB.subset_ground]
      exact ⟨diff_subset _ _, hB⟩
    })
    (by {
      rintro B₁ B₂ hB₁ hB₂ x hx
      have hx := (compl_diff_compl_iff _ _ M.E).mp hx
      obtain ⟨y, ⟨hy, hB⟩⟩ := Base.exchange' hB₁.2 hB₂.2 hx
      have hy := (compl_diff_compl_iff _ _ M.E).mpr hy
      refine' ⟨y, hy, _⟩

      have : x ∈ {y}ᶜ := by {
        rw [mem_compl_singleton_iff]
        rintro rfl
        exact hx.1.2 hy.1
      }

      simp only [mem_diff, mem_singleton_iff]
      sorry
      -- rwa [insert_eq, diff_eq, compl_union, diff_eq, compl_inter, compl_compl, ←inter_assoc, inter_distrib_left, inter_assoc, inter_comm _ B₁ᶜ, ←inter_assoc, ←diff_eq, ←diff_eq, inter_assoc, inter_comm _ {x}, ←inter_assoc,
      --       inter_singleton_eq_self.mpr hx.1.1, inter_comm, inter_singleton_eq_self.mpr this, union_comm, ←insert_eq]
    })
    (by {
      rintro X hX Is ⟨Bs, ⟨hBs, hIsBs⟩⟩ hIsX
      let B := M.E \ Bs
      have hB : M.Base B :=
        hBs.2
      have hIsB : Disjoint Is B := by
        simp only [disjoint_iff, ge_iff_le, le_eq_subset, sdiff_le_iff,
          sup_eq_union, inf_eq_inter, bot_eq_empty, ←subset_empty_iff]
        calc
          Is ∩ (M.E \ Bs) ⊆ Bs ∩ (M.E \ Bs) :=
            inter_subset_inter_left _ hIsBs
          _ = (Bs ∩ M.E) \ Bs :=
            by rw [inter_diff_assoc]
          _ = Bs \ Bs :=
            by rw [inter_eq_self_of_subset_left hBs.1]
          _ = ∅ :=
            diff_self

      /- `M.E \ X` has a maximal independent subset `I` -/
      obtain ⟨I, hI⟩ := maximality' M (M.E \ X) (diff_subset _ _) ∅ ⟨B, ⟨hB, empty_subset _⟩⟩
        (empty_subset _)

      /- extend `I` into `B' ⊆ I ∪ B` -/
      obtain ⟨Bi, ⟨hBi, hIBi⟩⟩ := hI.1.1
      obtain ⟨B', hB'⟩ := exists_base_subset_union_base' hBi hIBi hB

      have hIBIs : I ∪ B ⊆ (M.E \ Is) := by
        rw [union_subset_iff]
        exact ⟨hI.1.2.2.trans (compl_subset hIsX), compl_subset hIsBs⟩

      -- membership
      refine' ⟨X \ B', ⟨⟨⟨M.E \ B', ⟨⟨diff_subset _ _,
        by { rw [diff_diff_cancel_left hB'.1.subset_ground]; exact hB'.1 }⟩,
        diff_subset_diff hX (Subset.refl _)⟩⟩, _, diff_subset _ _⟩, _⟩⟩
      . rw [diff_eq, subset_inter_iff]
        refine' ⟨hIsX, _⟩
        have := @compl_subset α B' (M.E \ Is) M.E (hB'.2.2.trans hIBIs)
        rw [diff_diff_cancel_left (hIsBs.trans hBs.1), diff_eq, subset_inter_iff] at this
        exact this.2
      
      -- maximality
      by_contra'
      obtain ⟨B'', hB'', hB''B'⟩ : ∃ B'', M.Base B'' ∧ (B'' ∩ X ⊂ B' ∩ X) := by {
        obtain ⟨J, ⟨⟨⟨Bt, ⟨hBt, hJBt⟩⟩, ⟨hIsJ, hJX⟩⟩, hJ⟩⟩ := this
        let B'' := M.E \ Bt
        have hBtB'' : Bt = M.E \ B'' := by
          rw [diff_diff_cancel_left hBt.1]
        refine' ⟨B'', hBt.2, _⟩
        have hXB'J : X \ B' ⊂ J := hJ
        have hJXB'' : J ⊆ X \ B'' := by
          rw [←inter_eq_self_of_subset_left hX, inter_diff_assoc]
          exact subset_inter_iff.mpr ⟨hJX, by { rw [←hBtB'']; exact hJBt }⟩
        rw [inter_comm , inter_comm _ X]
        exact aux.mp (ssubset_of_ssubset_of_subset hXB'J hJXB'')
      }

      let I' := (B'' ∩ X) ∪ (B' \ X)

      have hI'X : I' ∩ X = B'' ∩ X := by
        calc
          I' ∩ X = (B'' ∩ X ∪ B' \ X) ∩ X  := by rfl
            _ = B'' ∩ X := by rw [union_inter_distrib_right,
                                      inter_eq_self_of_subset_left (inter_subset_right _ _),
                                      inter_comm (B' \ X) X, inter_diff_self, union_empty]

      have g₁ : I' ∩ X ⊂ B' ∩ X := by
        calc
          I' ∩ X = B'' ∩ X := by rw [hI'X]
               _ ⊂ B' ∩ X := hB''B'
              
      have g₂ : I' \ X = B' \ X := by
        calc
          I' \ X = (B'' ∩ X ∪ B' \ X) \ X  := by rfl
            _ = B' \ X  := by rw [union_diff_distrib, diff_eq_empty.mpr (inter_subset_right _ _),
                            empty_union, diff_diff, union_eq_self_of_subset_left (Subset.refl _)]
      
      have hI' : I' ⊂ B' :=
        ssubset_of_subset_of_compl_ssubset'' g₁ g₂.subset
      
      obtain ⟨I'', hI''⟩ := exists_base_subset_union_base' hB'.1 hI'.subset hB''
      have hI'I'' : I' ⊂ I'' := by
        refine' ssubset_iff_subset_ne.mpr ⟨hI''.2.1, _⟩
        rintro rfl
        exact not_base_of_ssubset hB'.1 hI' hI''.1

      have h₁ : I' \ X ⊂ I'' \ X := by
        have : I' ∩ X = I'' ∩ X := by
          refine' subset_antisymm (inter_subset_inter_left X hI''.2.1) _
          have := inter_subset_inter_left X hI''.2.2
          rw [union_inter_distrib_right, ←hI'X, union_self] at this
          exact this
        exact diff_ssubset_of_ssubset_of_subset_inter hI'I'' this.subset
      
      have h₂ : I ⊆ I' \ X := by
        rw [g₂, diff_eq, subset_inter_iff]
        refine' ⟨hB'.2.1, _⟩
        have := hI.1.2.2
        rw [diff_eq, subset_inter_iff] at this
        exact this.2
      
      exact (ssubset_of_subset_of_ssubset h₂ h₁).not_subset (hI.2 ⟨⟨I'', hI''.1, diff_subset _ _⟩,
            ⟨empty_subset _, diff_subset_diff hI''.1.subset_ground (Subset.refl _)⟩⟩
                (ssubset_of_subset_of_ssubset h₂ h₁).subset)
    })
    (fun B hB ↦ hB.1)


/- end of dual matroid -/

/-
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
      . { exfalso
          exact hx.2 g }
      . { exact g }
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
      . by_contra' h
        have hX' : X ⊂ B := by
          rw [ssubset_iff_subset_ne]
          refine' ⟨hB.2, _⟩
          rintro rfl
          exact h hB.1
        exact hX'.not_subset (hX (dual_base_indep hB.1) hX'.subset)
      . rintro hX
        rw [maximals]
        by_contra' h
        dsimp at h
        push_neg at h
        obtain ⟨I, ⟨hI, hXI, hIX⟩⟩ := h ⟨X, hX, subset_refl X⟩
        obtain ⟨B, ⟨hB, hIB⟩⟩ := hI

        have hXc : Base (E \ X) := hX.2
        have hBc : Base (E \ B) := hB.2
        have hBcXc := (compl_ssubset hX.1 hB.1 (ssubset_of_ssubset_of_subset ⟨hXI, hIX⟩ hIB))

        exact hBcXc.not_subset (hBc.2 hXc.1 hBcXc.subset)


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
        have hI'B : Disjoint I' B :=
          disjoint_of_diff_subset hT.2

        rw [dual_indep_maximals_eq_dual_base] at hBt
        let B' := E \ Bt
        have hB' : Base B' := hBt.2
      
        obtain ⟨B'', hB''⟩ := @h_basis (B' \ I') B (h_subset hB'.1 (diff_subset _ _)) hB

        refine' ⟨E \ B'', _, _, _⟩
        . rw [dual_indep_maximals_eq_dual_base]
          exact dual_base_compl B'' hB''.1
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
          have : E \ B'' ⊆ E \ (B' \ I') := compl_subset hB''.2.1
          rw [compl_ground (diff_subset E Bt), ground_compl_inter,
              (diff_diff_cancel_left hBt.1), (diff_diff_cancel_left (hT.2.trans hT.1.1)),
              union_comm] at this
          exact this
        }
    
    have aux2' : ∀ X B, X ⊆ E → Base B →
        (B ∩ X ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X} →
        (E \ B) ∩ (E \ X) ∈ maximals (· ⊆ ·) {I' | Indep' I' ∧ I' ⊆ (E \ X)}) := by 
      rintro X B hX hB hBX
      refine' ⟨_, _⟩
      . refine' ⟨_, inter_subset_right _ _⟩
        . refine' ⟨(E \ B), _, inter_subset_left _ _⟩
          have : Base (E \ (E \ B)) := by
            rw [diff_diff_right_self, inter_eq_self_of_subset_right (h_support hB.1)]
            exact hB
          exact ⟨diff_subset _ _, this⟩
      . by_contra' g
        obtain ⟨B', hB'⟩ : ∃ B', Base B' ∧ (B' ∩ (E \ X) ⊂ B ∩ (E \ X)) := by
          obtain ⟨I, h⟩ := g
          obtain ⟨⟨Bt, hBt⟩, _⟩ := h.1
          have h₁ : (E \ B) ∩ (E \ X) ⊂ I :=
            ⟨h.2.1, h.2.2⟩
          rw [←inter_eq_self_of_subset_left h.1.2] at h₁
          have h₂ : (E \ I) ∩ (E \ X) ⊂ B ∩ (E \ X) := by {
            have := compl_ssubset_inter (diff_subset _ _) (hBt.2.trans hBt.1.1) h₁
            rw [diff_diff_cancel_left (h_support hB.1)] at this
            exact this
          }
          use E \ Bt
          use hBt.1.2
          exact ssubset_of_subset_of_ssubset (inter_subset_inter_left _ (compl_subset hBt.2)) h₂
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

        have hI'B : I' ⊂ B :=
          ssubset_of_subset_of_compl_ssubset (h_support hI'.1.1) (h_support hB.1) h₁I'B h₂I'B
        
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
          compl_ssubset_inter (h_support hB.1) (h_support h.1.1) h₁
        have h₃ : (E \ Bt) ∩ X ⊆ (E \ I) ∩ X :=
           inter_subset_inter_left _ (compl_subset hBt.2)
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
          ssubset_of_subset_of_compl_ssubset' (dual_support I' hI'.1.1) (diff_subset _ _) hX h₆ h₈

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
        compl_subset_inter h₁
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
      . calc
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

-- lemma maximals_subset_maximals_disjoint
--   {ι : Type _}
--   ()

def directSum {ι : Type _} (Ms : ι → Matroid α)
  (hEs : Pairwise (Disjoint on (fun i ↦ (Ms i).E))) :=
  matroid_of_indep_of_forall_subset_base
    (⋃ i, (Ms i).E)
    (fun I ↦ (I ⊆ ⋃ i, (Ms i).E) ∧ ∀ i, (Ms i).Indep (I ∩ (Ms i).E))
    (by {
      rintro X hX
      sorry
    })
    (fun I J hJ hIJ ↦ ⟨hIJ.trans hJ.1,
      fun i ↦ (hJ.2 i).subset
      (subset_inter ((inter_subset_left _ _).trans hIJ) (inter_subset_right _ _))⟩) 
    sorry
    (fun _ hI ↦ hI.1)
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

