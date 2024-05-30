import Mathlib.Data.Matroid.Basic
import Matroid.Closure
import Mathlib.Data.Matroid.IndepAxioms

open Set Matroid

variable {α : Type*} {I B X : Set α}

section ClMatroid

structure ClMatroid (α : Type*) where
  (E : Set α)
  (cl : Set α → Set α)
  (subset_cl_self : ∀ X ⊆ E, X ⊆ cl X)
  (cl_subset_cl : ∀ ⦃X Y : Set α⦄, X ⊆ Y → cl X ⊆ cl Y )
  (cl_cl_eq_cl : ∀ X, cl (cl X) = cl X)
  (cl_exchange : ∀ ⦃Z :Set α⦄ ⦃x y : α⦄, y ∈ cl (insert x Z) \ cl Z → x ∈ cl (insert y Z))
  (ClIndep : Set α → Prop)
  (clIndep_iff : ∀ ⦃I⦄, ClIndep I ↔ (∀ x ∈ I, x ∉ cl (I \ {x})))
  (clIndep_maximal : ∀ ⦃X⦄, ExistsMaximalSubsetProperty ClIndep X)
  (cl_inter_inter_ground : ∀ X, cl (X ∩ E) ∩ E = cl X)

namespace ClMatroid

lemma cl_subset_ground (M : ClMatroid α) (X : Set α) : M.cl X ⊆ M.E := by
  rw [← M.cl_inter_inter_ground]; apply inter_subset_right

lemma cl_inter_ground (M : ClMatroid α) (X : Set α) : M.cl (X ∩ M.E) = M.cl X := by
  rw [← inter_eq_self_of_subset_left (M.cl_subset_ground (X ∩ M.E)), M.cl_inter_inter_ground]

@[simps] protected def indepMatroidOnUniv (M : ClMatroid α) (hE : M.E = univ) : IndepMatroid α :=
  have h_indep_subset : ∀ ⦃I J⦄, M.ClIndep J → I ⊆ J → M.ClIndep I :=by
    intro I J Jindep Isubset
    rw [M.clIndep_iff]
    intro x xinI hx
    have hij : (I \ {x}) ⊆ (J \ {x}) := by
      rw [subset_def]
      intro y Iy
      rw [diff_eq]
      rw [diff_eq] at Iy
      apply inter_subset_inter_left
      apply Isubset
      exact Iy
    rw [subset_def] at Isubset
    have xj : x ∈ J := by
      apply Isubset
      exact xinI
    have clIsubsetclJ : M.cl (I \ {x}) ⊆ M.cl (J \ {x}) := by
      apply M.cl_subset_cl
      exact hij
    have xinclj : x ∈ M.cl (J \ {x}) := by
      rw [subset_def] at clIsubsetclJ
      apply clIsubsetclJ
      exact hx
    absurd xinclj
    rw [M.clIndep_iff] at Jindep
    apply Jindep
    exact xj

IndepMatroid.mk
  (E := univ)

  (Indep := M.ClIndep)

  (indep_empty := by
    rw [M.clIndep_iff]
    intro x xin
    exfalso
    exact xin)

  (indep_subset := h_indep_subset)

  (indep_aug := by
    intro I I' Iindep Inotmax I'max
    rw [maximals, mem_setOf_eq] at I'max
    rw [maximals] at Inotmax
    have hcl : ∀ Z, ∀ x,  M.ClIndep Z ∧ ¬M.ClIndep (insert x Z) → x ∈ M.cl Z := by
      intro Z x hand
      rcases hand with ⟨Zindep, Zxdep⟩
      rw [M.clIndep_iff] at Zxdep
      simp only [mem_insert_iff, forall_eq_or_imp, mem_singleton_iff,     insert_diff_of_mem, not_and,
        not_forall, Classical.not_imp, not_not] at Zxdep
      by_cases xinZ : x ∈ Z
      · apply M.subset_cl_self _ (by simp [hE])
        exact xinZ
      · contrapose! Zxdep
        refine ⟨?_, ?_⟩
        · contrapose! Zxdep
          apply M.cl_subset_cl
          apply diff_subset
          exact {x}
          exact Zxdep
        · intro y yinZ
          contrapose! Zxdep
          have hZ :Z = insert y (Z \ {y})  := by
            rw [insert_diff_singleton, insert_eq_self.mpr]
            exact yinZ
          rw [hZ]
          apply M.cl_exchange
          rw [mem_diff]
          refine ⟨?_, ?_⟩
          · rw [insert_diff_singleton_comm]
            exact Zxdep
            contrapose! xinZ
            rw [xinZ]
            exact yinZ
          · rw [M.clIndep_iff] at Zindep
            apply Zindep
            exact yinZ
    obtain ⟨B, Bmax'⟩ := M.clIndep_maximal I Iindep (subset_union_left I I')
    have hclI' :∀ y, y ∈ M.cl I'  := by
      intro y
      by_cases hyI' : y ∈ I'
      · apply M.subset_cl_self _ (by simp [hE])
        exact hyI'
      · apply hcl
        constructor
        · exact I'max.left
        · contrapose! I'max
          intro _
          use insert y I'
          constructor
          · exact I'max
          · constructor
            · simp
            · rw [subset_def]
              push_neg
              use y
              constructor
              · simp
              · exact hyI'
    have hclI'B: M.cl I' ⊆ M.cl B := by
      nth_rewrite 2 [← M.cl_cl_eq_cl]
      apply M.cl_subset_cl
      rw [subset_def]
      intro x xinI'
      by_cases xinB :x ∈ B
      · apply M.subset_cl_self _ (by simp [hE])
        exact xinB
      · apply hcl
        rw [maximals] at Bmax'
        simp only [mem_setOf_eq, and_imp] at Bmax'
        refine ⟨Bmax'.left.left, ?_⟩
        rw [M.clIndep_iff]
        push_neg
        use x
        refine ⟨?_, ?_⟩
        · simp only [mem_insert_iff, true_or]
        · apply hcl
          refine ⟨?_, ?_⟩
          · rw [insert_diff_of_mem, M.clIndep_iff]
            intro y hy
            have Bindep :=
              Bmax'.left.left
            contrapose! Bindep
            rw [M.clIndep_iff]
            push_neg
            use y
            refine ⟨diff_subset B {x}  hy, ?_⟩
            apply M.cl_subset_cl
            apply diff_subset
            exact {x}
            rw [diff_diff_comm]
            exact Bindep
            rw [mem_singleton_iff]
          . simp only [mem_singleton_iff, insert_diff_of_mem, insert_diff_singleton]
            contrapose! Bmax'
            intro hB
            use (insert x B)
            refine ⟨Bmax', subset_trans hB.right.left (subset_insert x B), ⟨?_, ?_, ?_⟩⟩
            apply insert_subset
            rw [mem_union]
            right
            exact xinI'
            exact hB.right.right
            simp only [subset_insert]
            contrapose! xinB
            rw [insert_subset_iff] at xinB
            exact xinB.left
    have cl_max (Z : Set α) :  (∀ x, x ∈ M.cl Z) ∧ M.ClIndep Z → Z ∈ maximals (fun x x_1 ↦ x ⊆ x_1) {I | M.ClIndep I}:= by
      intro ⟨xincl, Zindep⟩
      rw [maximals]
      simp only [mem_setOf_eq]
      refine ⟨Zindep, ?_⟩
      intro J Jindep ZsubJ
      contrapose! Jindep
      rw [subset_def, not_forall] at Jindep
      push_neg at Jindep
      rcases Jindep with ⟨ y, hyJ, hyZ⟩
      rw [M.clIndep_iff]
      push_neg
      use y
      refine ⟨hyJ, ?_⟩
      apply M.cl_subset_cl
      apply subset_diff.mpr
      refine ⟨ ZsubJ, disjoint_singleton_right.mpr hyZ⟩
      apply xincl
    have Bmax : B ∈ maximals (fun x x_1 ↦ x ⊆ x_1) {I | M.ClIndep I} := by
      apply cl_max
      rw [maximals] at Bmax'
      simp only [mem_setOf_eq, and_imp] at Bmax'
      refine ⟨?_, Bmax'.left.left⟩
      intro x
      apply hclI'B
      apply hclI'
    have : ∃ y ∈ B, y ∉ I:= by
      contrapose! Inotmax
      simp only [mem_setOf_eq]
      rw [maximals] at Bmax'
      simp only [mem_setOf_eq] at Bmax'
      rw [← subset_def] at Inotmax
      have : B = I := subset_antisymm Inotmax Bmax'.left.right.left
      refine ⟨ Iindep, ?_⟩
      rw [← this]
      exact Bmax.right
    rcases this with ⟨ y, yinB, ynotinI⟩
    use y
    refine ⟨?_, ?_⟩
    rw [mem_diff]
    refine ⟨?_,ynotinI⟩
    rw [maximals] at Bmax'
    simp only [mem_setOf_eq, and_imp] at Bmax'
    obtain ⟨ ⟨ _, _, BsubII'⟩,_⟩ := Bmax'
    have sub :B \ I ⊆ (I ∪ I') \ I:= by
      apply diff_subset_diff_left
      exact BsubII'
    simp only [union_diff_left] at sub
    have :y ∈ I' \ I := by
      have :y ∈ B \ I := by
        rw [mem_diff]
        refine ⟨ yinB, ynotinI⟩
      apply sub
      exact this
    apply diff_subset
    exact this
    apply h_indep_subset
    rw [maximals] at Bmax'
    simp only [mem_setOf_eq, and_imp] at Bmax'
    exact Bmax'.left.left
    rw [insert_eq, union_subset_iff]
    refine ⟨?_, Bmax'.left.right.left⟩
    rw [singleton_subset_iff]
    exact yinB)

  (indep_maximal := by
    refine fun X _ ↦ ?_
    apply M.clIndep_maximal)

  (subset_ground := by
    refine fun I _ ↦ subset_univ I)

@[simps!] def matroidOnUniv (M : ClMatroid α) (hM : M.E = univ) := (M.indepMatroidOnUniv hM).matroid

@[simp] lemma matroidOnUniv_indep_eq (M : ClMatroid α) (hM : M.E = univ) (I : Set α) : (M.matroidOnUniv hM).Indep I = M.ClIndep I := rfl

lemma matroidOnUniv_cl_eq (M : ClMatroid α) (hM : M.E = univ) (X : Set α) :
    (M.matroidOnUniv hM).cl X = M.cl X := by
  obtain ⟨I, hI⟩ := (M.matroidOnUniv hM).exists_basis X (by simp [hM])
  have hi := hI.indep
  simp [matroidOnUniv, M.clIndep_iff] at hi
  refine subset_antisymm ?_ ?_
  · simp_rw [← hI.cl_eq_cl, subset_def, hI.indep.mem_cl_iff']
    simp [M.clIndep_iff]
    refine fun e h ↦ by_contra fun heX ↦ ?_
    have heI : e ∉ I := not_mem_subset (hI.subset.trans (M.subset_cl_self X (by simp [hM]))) heX
    have heI' : e ∉ M.cl I := not_mem_subset (M.cl_subset_cl hI.subset) heX
    simp only [heI, not_false_eq_true, diff_singleton_eq_self, heI', imp_false, not_forall,
      Classical.not_imp, not_not, true_implies] at h
    obtain ⟨a, haI, ha⟩ := h
    rw [← insert_diff_singleton_comm (by rintro rfl; contradiction)] at ha
    exact heI' <| by simpa [haI] using M.cl_exchange ⟨ha, hi a haI⟩
  · simp_rw [← hI.cl_eq_cl, subset_def, hI.indep.mem_cl_iff']
    simp only [matroidOnUniv_E, mem_univ, matroidOnUniv_Indep, true_and]
    refine fun e h heI ↦ ?_
    rw [Matroid.Basis, maximals] at hI
    simp only [matroidOnUniv_Indep, mem_setOf_eq, and_imp, matroidOnUniv_E, subset_univ,
      and_true] at hI
    have hIX: M.cl X = M.cl I := by
      refine subset_antisymm ?_ (M.cl_subset_cl hI.left.right)
      nth_rw 2 [← M.cl_cl_eq_cl]
      apply cl_subset_cl
      obtain ⟨⟨hI', hIX⟩ ,  hImax⟩ := hI
      contrapose! hImax
      simp [subset_def, not_forall, Classical.not_imp] at hImax
      rcases hImax with ⟨a, haX, haI⟩
      use (insert a I)
      refine ⟨?_, insert_subset haX hIX, subset_insert a I, ?_⟩
      · rw [M.clIndep_iff]
        contrapose! haI
        obtain ⟨x, hx, hx'⟩ := haI
        by_cases hxa: x = a
        · simp [hxa, mem_singleton_iff, insert_diff_of_mem] at hx'
          apply cl_subset_cl
          apply diff_subset
          exact {a}
          exact hx'
        have: I = insert x (I \ {x}) := by
          rw [insert_diff_singleton, insert_eq_of_mem]
          rw [insert_def, mem_setOf] at hx
          rcases hx with h₁|h₂
          · absurd hxa h₁
            trivial
          · exact h₂
        rw [this]
        apply M.cl_exchange
        rw [mem_diff]
        refine ⟨ ?_,?_⟩
        · rw [insert_diff_singleton_comm]
          exact hx'
          rw [ne_eq, eq_comm]
          exact hxa
        . rw [clIndep_iff] at hI'
          apply hI'
          rw [insert_def, mem_setOf] at hx
          rcases hx with h₁|h₂
          · absurd hxa h₁
            trivial
          · exact h₂
      · simp [subset_def]
        contrapose! haI
        apply M.subset_cl_self
        simp [hM]
        exact haI
    rw [hIX] at h
    contrapose! h
    have: insert e I \ {e} = I := insert_diff_self_of_not_mem h
    rw [← this]
    rw [clIndep_iff] at heI
    apply heI
    simp [mem_insert_iff, true_or]





  -- apply hI.basis_cl_right.mem_of_insert_indep ?_ (by simpa [M.clIndep_iff, heI])
  -- rw [← hI.cl_eq_cl, hI.indep.mem_cl_iff']
  -- simp [M.clIndep_iff, heI]





end ClMatroid

-- structure ClMatroid (α : Type*) where
--   (E : Set α)
--   (cl : Set α → Set α)
--   (subset_cl_self : ∀ X ⊆ E, X ⊆ cl X)
--   (cl_subset : ∀ ⦃X Y : Set α⦄, X ⊆ Y → cl X ⊆ cl Y )
--   (cl_cl_eq_cl : ∀ X, cl (cl X) = cl X)
--   (cl_exchange : ∀ ⦃Z :Set α⦄ ⦃x y : α⦄, y ∈ cl (insert x Z) \ cl Z → x ∈ cl (insert y Z))
--   (ClIndep : Set α → Prop)
--   (clIndep_iff : ∀ ⦃I⦄, ClIndep I ↔ (∀ x ∈ I, x ∉ cl (I \ {x})))
--   (clIndep_maximal : ∀ ⦃X⦄, ExistsMaximalSubsetProperty ClIndep X)
--   (cl_inter_inter_ground : ∀ X, cl (X ∩ E) ∩ E = cl X)
