import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms

open Set Matroid

variable {α : Type*} {I B X : Set α}

section ClMatroid

structure ClMatroid (α : Type*) where
  (cl : Set α → Set α)
  (cl_contain_self : ∀ ⦃X :Set α⦄, X ⊆ cl X)
  (cl_subset : ∀ ⦃X Y : Set α⦄, X ⊆ Y → cl X ⊆ cl Y )
  (cl_cl_eq_cl : ∀ ⦃X :Set α⦄, cl (cl X) = cl X)
  (cl_exchange : ∀ ⦃Z :Set α⦄, ∀ ⦃x y : α⦄, y ∈ cl (insert x Z) \ cl Z → x ∈ cl (insert y Z))
  (ClIndep : Set α → Prop)
  (clIndep_iff : ∀ ⦃I :Set α⦄, ClIndep I ↔ (∀ x ∈ I, x ∉ cl (I \ {x})))
  (clIndep_maximal : ∀ ⦃X :Set α⦄, ExistsMaximalSubsetProperty ClIndep X)
namespace ClMatroid

@[simps] protected def matroid (M : ClMatroid α) : IndepMatroid α :=
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
      apply M.cl_subset
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
      · apply M.cl_contain_self
        exact xinZ
      · contrapose! Zxdep
        refine ⟨?_, ?_⟩
        · contrapose! Zxdep
          apply M.cl_subset
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
      · apply M.cl_contain_self
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
      apply M.cl_subset
      rw [subset_def]
      intro x xinI'
      by_cases xinB :x ∈ B
      · apply M.cl_contain_self
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
            apply M.cl_subset
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
      apply M.cl_subset
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
