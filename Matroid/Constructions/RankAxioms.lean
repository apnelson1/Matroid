import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms

/-- A matroid as defined by the (relative) rank axioms. The constructed
  `RankMatroid` can be then converted into a `Matroid` with `RankMatroid.matroid` -/
structure RankMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The (relative) rank function -/
  (relRank : Set α → Set α → ℕ∞)

  (relRank_le_encard_diff {A B : Set α} : A ⊆ E → B ⊆ A → relRank A B ≤ (A \ B).encard)
  (relRank_union_le_relRank_inter {A B : Set α} : A ⊆ E → B ⊆ E → relRank (A ∪ B) B ≤ relRank A (A ∩ B))
  (relRank_add_cancel {A B C : Set α} : A ⊆ E → B ⊆ A → C ⊆ B → (relRank A C) = (relRank A B) + (relRank B C))
  (relRank_sUnion_eq_zero {S : Set (Set α)} {B : Set α} :
      (∀ A ∈ S, B ⊆ A ∧ A ⊆ E ∧ relRank A B = 0) → relRank (⋃₀ S) B = 0)

  (RIndep : Set α → Prop)
  (rindep_maximal : ∀ X ⊆ E, Matroid.ExistsMaximalSubsetProperty RIndep X)
  (rindep_iff' : ∀ I, RIndep I ↔ I ⊆ E ∧ ∀ x ∈ I, relRank I (I \ {x}) > 0 )

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {M : RankMatroid α} {x : α}

theorem r_nonneg : M.relRank A B ≥ 0 := by
  exact zero_le (M.relRank A B)

theorem relRank_self_eq_zero (h : A ⊆ M.E) : M.relRank A A = 0 := by
  have := M.relRank_le_encard_diff h (subset_refl A)
  rw [Set.diff_eq_empty.mpr fun ⦃a⦄ a ↦ a, Set.encard_empty] at this
  exact nonpos_iff_eq_zero.mp this

theorem RIndep.subset_ground (h : M.RIndep I) : I ⊆ M.E := by
  rw [rindep_iff'] at h
  exact h.left

theorem RIndep.indep (h : M.RIndep I) :  ∀ x ∈ I, M.relRank I (I \ {x}) > 0  := by
  rw [rindep_iff'] at h
  exact h.right

theorem indep_subset (hJ : M.RIndep J) (rIJ : I ⊆ J) : M.RIndep I := by
    rw [M.rindep_iff']
    refine ⟨rIJ.trans hJ.subset_ground, λ x hx ↦ ?_⟩
    have hJ_indep := hJ.subset_ground
    have hJ := hJ.indep x (Set.mem_of_mem_of_subset hx rIJ)
    set A := I
    set B := J \ {x}
    have hAUB : J = A ∪ B := by
      refine (Set.union_diff_cancel' ?h₁ rIJ).symm
      exact Set.singleton_subset_iff.mpr hx
    have hAIB : A \ {x} = A ∩ B := by
      ext y;
      refine ⟨λ hY ↦ ?_, λ hY ↦ ?_⟩
      · refine ⟨Set.mem_of_mem_diff hY, Set.mem_diff_singleton.mpr ?_⟩
        refine ⟨rIJ (Set.mem_of_mem_diff hY), ?_⟩
        have h := Set.not_mem_of_mem_diff hY
        exact h
      have hyB : y ∈ J \ {x} := Set.mem_of_mem_inter_right hY
      have hynex : y ≠ x := by have := Set.not_mem_of_mem_diff hyB; exact this
      exact ⟨Set.mem_of_mem_inter_left hY, hynex⟩
    rw [hAUB] at hJ
    rw [hAIB]
    have hA : A ⊆ M.E := (rIJ.trans hJ_indep)
    have hB : B ⊆ M.E := ((Set.diff_subset J {x}).trans hJ_indep)
    exact hJ.trans_le (M.relRank_union_le_relRank_inter hA hB)

theorem r_le_r_subset_right (hX : X ⊆ M.E) (hAX : A ⊆ X) (hBA : B ⊆ A) : M.relRank X A ≤ M.relRank X B := by
  rw [M.relRank_add_cancel hX hAX hBA]; simp

theorem insert_indep_iff_r_insert_pos (hI_indep : M.RIndep I) (hx : x ∈ M.E \ I)
    : M.RIndep (Set.insert x I) ↔ M.relRank (Set.insert x I) I > 0 := by
  refine ⟨λ hIx_indep ↦ ?_, λ hr ↦ ?_⟩
  · have h := hIx_indep.indep x (Set.mem_insert x I)
    have : Set.insert x I \ {x} = I :=
      Set.insert_diff_self_of_not_mem (Set.not_mem_of_mem_diff hx)
    rwa [this] at h
  refine (M.rindep_iff' (Set.insert x I)).mpr ?_
  refine ⟨Set.insert_subset (Set.mem_of_mem_diff hx) hI_indep.subset_ground, ?_⟩
  contrapose! hr
  rcases hr with ⟨y, hy, hr⟩
  by_cases hxy : x = y
  · rw [hxy] at hr hx ⊢
    have := Set.not_mem_of_mem_diff hx
    have : Set.insert y I \ {y} = I := Set.insert_diff_self_of_not_mem this
    rwa [this] at hr
  have h : M.relRank (Set.insert x I) (I \ {y}) ≤ 1 := by
    set A := (Set.insert x I)
    set B := (Set.insert x I \ {y})
    set C := (I \ {y})
    have h₁ : A ⊆ M.E := Set.insert_subset (Set.mem_of_mem_diff hx) hI_indep.subset_ground
    have h₂ : B ⊆ A := Set.diff_subset (Set.insert x I) {y}
    have h₃ : C ⊆ B := by
      refine Set.diff_singleton_subset_iff.mpr ?_
      rw [Set.insert_diff_singleton]
      exact (Set.subset_insert x I).trans (Set.subset_insert y (Set.insert x I))
    have hrBC : M.relRank B C ≤ 1 := by
      have h := M.relRank_le_encard_diff (h₂.trans h₁) h₃
      rw [Set.diff_diff_right] at h
      have h := h.trans (Set.encard_union_le (B \ I) (B ∩ {y}))
      rw [Set.encard_eq_zero.mpr Set.diff_inter_self] at h
      simp only [add_zero] at h
      have : B \ I ⊆ {x} := by refine Set.diff_subset_iff.mpr ?_; simp; exact h₂
      rcases Set.subset_singleton_iff_eq.mp this with h' | h'
      · rw [h'] at h; rw [Set.encard_empty] at h; exact h.trans zero_le_one
      rw [h'] at h; rwa [Set.encard_singleton] at h;
    have h : M.relRank A B + M.relRank B C <= 1 := by
      exact add_le_add hr hrBC
    have := M.relRank_add_cancel h₁ h₂ h₃
    rwa [<-this] at h
  set A := (Set.insert x I)
  set B := (I)
  set C := (I \ {y})
  have h' : M.relRank A C = M.relRank A B + M.relRank B C := by
    have h₁ : A ⊆ M.E := Set.insert_subset (Set.mem_of_mem_diff hx) hI_indep.subset_ground
    have h₂ : B ⊆ A := Set.subset_insert x I
    have h₃ : C ⊆ B := Set.diff_subset I {y}
    exact M.relRank_add_cancel h₁ h₂ h₃
  have h'' : M.relRank B C ≥ 1 := by
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · contradiction
    have := hI_indep.indep y hy
    exact ENat.one_le_iff_pos.mpr this
  contrapose! h
  rw [h'];
  have h := ENat.add_one_le_of_lt h
  simp only [zero_add] at h
  have := add_le_add h h''
  rw [one_add_one_eq_two] at this
  refine (ENat.add_one_le_iff ?refine_2.intro.intro.hm).mp this
  exact ENat.coe_toNat_eq_self.mp rfl

theorem indep_subset_maximal_iff_relrank_zero (hX : X ⊆ M.E) (hI : I ⊆ X) (hI_indep : M.RIndep I) :
    (I ∈ (maximals (· ⊆ ·) {S | M.RIndep S ∧ S ⊆ X}) ↔ M.relRank X I = 0) := by
  refine ⟨λ hI_max ↦ ?_, λ hr ↦ ?_⟩
  · by_cases hXI : X = I
    · rw [hXI]; exact relRank_self_eq_zero hI_indep.subset_ground
    set S := {(insert x I) | x ∈ X \ I}
    have h : ∀ A ∈ S, I ⊆ A ∧ A ⊆ M.E ∧ M.relRank A I = 0 := by
      rintro A ⟨x, hx_mem, rfl⟩
      rcases (Set.mem_diff x).mpr hx_mem with ⟨hxX, hxI⟩
      refine ⟨Set.subset_insert x I, Set.insert_subset (hX hxX) hI_indep.subset_ground, ?_⟩
      contrapose! hI_max
      have hI_max : M.relRank (insert x I) I > 0 := by exact pos_iff_ne_zero.mpr hI_max
      suffices h : M.RIndep (insert x I) by
        have : (insert x I) ∈ {S | M.RIndep S ∧ S ⊆ X} := ⟨h, Set.insert_subset hxX hI⟩
        apply mem_maximals_iff.not.mpr
        push_neg; intro; use (insert x I)
        exact ⟨this, Set.subset_insert x I, by exact Set.ne_insert_of_not_mem I hxI⟩
      have hxEI : x ∈ M.E \ I := by exact (Set.mem_diff x).mpr ⟨hX hxX, hxI⟩
      exact (insert_indep_iff_r_insert_pos hI_indep hxEI).mpr hI_max
    have := M.relRank_sUnion_eq_zero h
    have hXU : X = S.sUnion := by
      apply Set.eq_of_subset_of_subset
      · intro x hx; simp only [Set.mem_sUnion]
        by_cases h : x ∈ I
        · have hXU_ssubset := Set.ssubset_iff_subset_ne.mpr ⟨hI, Ne.symm hXI⟩
          rcases Set.exists_of_ssubset hXU_ssubset with ⟨y, hy⟩
          have hy := (Set.mem_diff y).mpr hy
          set Ay := insert y I
          have : Ay ∈ S := by use y
          use Ay
          exact ⟨this, (Set.subset_insert y I) h⟩
        have hx := (Set.mem_diff x).mpr ⟨hx, h⟩
        use insert x I
        constructor
        · use x
        exact Set.mem_insert x I
      apply Set.sUnion_subset_iff.mpr; rintro Ax ⟨x, hx_mem, rfl⟩
      exact Set.insert_subset ((Set.mem_diff x).mpr hx_mem).left hI
    rwa [<-hXU] at this
  contrapose! hr
  unfold maximals at hr; simp at hr
  obtain ⟨I', hI'_indep, hI', hI'_ssubset⟩ := hr hI_indep hI
  rw [<-Set.ssubset_def] at hI'_ssubset
  obtain ⟨x, hxI', hxI⟩ := Set.exists_of_ssubset hI'_ssubset
  have : M.RIndep (Set.insert x I) := by
    exact indep_subset hI'_indep (Set.insert_subset hxI' hI'_ssubset.subset)
  rw [insert_indep_iff_r_insert_pos hI_indep ((Set.mem_diff x).mpr ⟨(hI'.trans hX) hxI', hxI⟩)] at this
  have : M.relRank X I > 0 := by
    rw [M.relRank_add_cancel hX (Set.insert_subset (hI' hxI') hI) (Set.subset_insert x I)]
    have this' : M.relRank X (Set.insert x I) ≥ 0 := by exact r_nonneg
    exact Right.add_pos_of_nonneg_of_pos this' this
  exact pos_iff_ne_zero.mp this

@[simps] protected def matroid (M : RankMatroid α) : IndepMatroid α where
  E := M.E
  Indep := M.RIndep

  indep_empty := by
    rw [M.rindep_iff'];
    refine ⟨Set.empty_subset M.E, λ x hx ↦ ?_⟩
    contradiction

  indep_subset := by
    intro I J hJ rIJ
    exact indep_subset hJ rIJ

  indep_aug := by
    have hiff : {S | M.RIndep S ∧ S ⊆ M.E} = {S | M.RIndep S} := by
      ext S; constructor
      · simp; tauto
      simp; exact λ h ↦ ⟨h, h.subset_ground⟩

    intro I B hI_indep hI_nmax hB_max
    have hB_indep := (mem_maximals_iff.mp hB_max).left
    have hrEI : M.relRank M.E I > 0 := by
      contrapose! hI_nmax
      norm_num at hI_nmax
      have := (indep_subset_maximal_iff_relrank_zero (subset_refl M.E) hI_indep.subset_ground hI_indep).mpr
      rw [hiff] at this
      exact this hI_nmax
    have hrEB : M.relRank M.E B = 0 := by
      have := (indep_subset_maximal_iff_relrank_zero (subset_refl M.E) hB_indep.subset_ground hB_indep).mp
      rw [hiff] at this
      exact this hB_max
    have hrIUB_I : M.relRank (I ∪ B) I > 0 := by
      have h₁ : I ⊆ (I ∪ B) := by exact Set.subset_union_left I B
      have h₂ : (I ∪ B) ⊆ M.E := by exact Set.union_subset hI_indep.subset_ground hB_indep.subset_ground
      have h₃ : M.E ⊆ M.E := by exact fun ⦃a⦄ a ↦ a
      calc
      0 < M.relRank M.E I := by assumption
      _ = M.relRank M.E (I ∪ B) + M.relRank (I ∪ B) I := by
        exact M.relRank_add_cancel h₃ h₂ h₁
      _ ≤ M.relRank M.E B + M.relRank (I ∪ B) I := by
        apply add_le_add_right
        exact r_le_r_subset_right h₃ h₂ (Set.subset_union_right I B)
      _ = M.relRank (I ∪ B) I := by
        rw [hrEB]
        simp
    have hIUB_subset := (Set.union_subset hI_indep.subset_ground hB_indep.subset_ground)
    have hI_nmax := (not_iff_not.mpr (indep_subset_maximal_iff_relrank_zero hIUB_subset (Set.subset_union_left I B) hI_indep)).mpr (Ne.symm (hrIUB_I.ne))
    have h_maximals_nonempty := M.rindep_maximal (I ∪ B) hIUB_subset I hI_indep  (Set.subset_union_left I B)
    rcases h_maximals_nonempty with ⟨I', ⟨hI'_indep, hI'_contains_I, hI'_in_IUB⟩, hI'_max⟩
    by_cases hII' : I = I'
    · rw [<-hII'] at hI'_max hI'_indep
      simp at hI'_max
      contrapose! hI_nmax
      rw [mem_maximals_iff]; simp
      refine ⟨by assumption, ?_⟩
      intro y hy_indep hy_in hy_within
      have := hI'_max hy_indep hy_within hy_in hy_within
      exact Set.Subset.antisymm hy_within (hI'_max hy_indep hy_within hy_in hy_within)
    have : I ⊂ I' := by exact HasSubset.Subset.ssubset_of_ne hI'_contains_I hII'
    rcases Set.exists_of_ssubset this with ⟨x, hx⟩
    use x
    have : x ∈ B \ I := by
      refine (Set.mem_diff x).mpr ⟨?_, hx.right⟩
      rcases (Set.mem_union x I B).mp (hI'_in_IUB hx.left) with h | h
      · exfalso; exact hx.right h
      assumption
    refine ⟨this, ?_⟩
    exact indep_subset hI'_indep (Set.insert_subset hx.left hI'_contains_I)

  indep_maximal := λ X hX ↦ M.rindep_maximal X hX
  subset_ground := λ I hI ↦ hI.subset_ground

end RankMatroid
