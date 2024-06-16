import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms
import Matroid.Minor.Rank

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
  (relRank_sUnion_eq_zero : ∀ ⦃S : Set (Set α)⦄, ∀ ⦃A : Set α⦄,
    (∀ B ∈ S, A ⊆ B ∧ relRank A B = 0) → relRank A (⋃₀ S) = 0)

  (relRank_compl_ground_eq : relRank ∅ Eᶜ = 0)
  (relRank_eq_union_right : ∀ A B, relRank A B = relRank A (B ∪ A))

  (Indep : Set α → Prop)
  (indep_maximal : ∀ ⦃X⦄, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  (indep_iff' : ∀ ⦃I⦄, Indep I ↔ I ⊆ E ∧ ∀ x ∈ I, relRank (I \ {x}) I > 0 )

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {x : α}

def indepSubsets (M : RankMatroid α) (A : Set α) : Set (Set α) :=
  {I | M.Indep I ∧ I ⊆ A}

def Basis' (M : RankMatroid α) (I A : Set α) : Prop :=
  I ∈ maximals (· ⊆ ·) (M.indepSubsets A)

lemma relRank_self_eq_zero {M : RankMatroid α} : M.relRank A A = 0 := by
  obtain h := M.relRank_le_encard_diff A A
  simpa only [sdiff_self, Set.bot_eq_empty, Set.encard_empty, nonpos_iff_eq_zero] using h

lemma Indep.subset_ground {M : RankMatroid α} (h : M.Indep I) : I ⊆ M.E :=
  (M.indep_iff'.mp h).left

lemma Indep.indep {M : RankMatroid α} (h : M.Indep I) : ∀ x ∈ I, M.relRank (I \ {x}) I > 0 :=
  (M.indep_iff'.mp h).right

lemma Indep.relRank_pos_of_sub_mem {M : RankMatroid α} (h : M.Indep I) (hx : x ∈ I) :
    M.relRank (I \ {x}) I > 0 :=
  h.indep x hx

lemma relRank_eq_diff_right {M : RankMatroid α} : M.relRank A B = M.relRank A (B \ A) := by
  rw [M.relRank_eq_union_right A (B \ A), Set.diff_union_self, relRank_eq_union_right]

lemma relRank_mono_right {M : RankMatroid α} (hAB : A ⊆ B) :
    M.relRank X A ≤ M.relRank X B := by
  rw [M.relRank_eq_union_right _ A, M.relRank_eq_union_right _ B,
    M.relRank_add_cancel Set.subset_union_right (Set.union_subset_union_left X hAB)]
  simp only [self_le_add_right]

lemma relRank_mono_left {M : RankMatroid α} (hAB : A ⊆ B) :
    M.relRank B X ≤ M.relRank A X := by
  calc
    M.relRank B X = M.relRank B (X ∪ B) := by rw [relRank_eq_union_right]
    _ ≤ M.relRank (A ∪ B) ((A ∪ B) ∪ (A ∪ X)) := by
      rw [Set.union_eq_right.mpr hAB, <-Set.union_assoc, Set.union_eq_left.mpr hAB, Set.union_comm]
    _ ≤ M.relRank ((A ∪ B) ∩ (A ∪ X)) (A ∪ X) := M.relRank_union_le_relRank_inter (A ∪ B) (A ∪ X)
    _ = M.relRank (A ∪ (B ∩ X)) (A ∪ X) := by rw [Set.union_inter_distrib_left]
    _ ≤ M.relRank A (A ∪ (B ∩ X)) + M.relRank (A ∪ (B ∩ X)) (A ∪ X) := le_add_self
    _ = M.relRank A (A ∪ X) := by
      have h : (A ∪ (B ∩ X)) ⊆ (A ∪ X) :=
        Set.union_subset_union (subset_refl A) Set.inter_subset_right
      rw [M.relRank_add_cancel Set.subset_union_left h]
    _ = M.relRank A X := by rw [Set.union_comm, <-relRank_eq_union_right]

lemma relRank_inter_ground {M : RankMatroid α} : M.relRank (A ∩ M.E) (B ∩ M.E) = M.relRank A B := by
  have relRank_inter_ground_self_left : ∀ ⦃A⦄, M.relRank (A ∩ M.E) A = 0 := fun A ↦ by
    rw [relRank_eq_diff_right, Set.diff_self_inter, Set.diff_eq_compl_inter, <-nonpos_iff_eq_zero]
    have h : M.relRank ∅ (M.Eᶜ ∩ A) ≤ 0 := by
      rw [<-M.relRank_compl_ground_eq]
      exact relRank_mono_right Set.inter_subset_left
    refine LE.le.trans ?_ h
    exact relRank_mono_left <| Set.empty_subset (A ∩ M.E)
  symm
  calc
    M.relRank A B = M.relRank A (B ∪ A) := by rw [relRank_eq_union_right]
    _ = M.relRank (A ∩ M.E) (B ∪ A) := by
      rw [M.relRank_add_cancel Set.inter_subset_left Set.subset_union_right,
        relRank_inter_ground_self_left, zero_add]
    _ = M.relRank (A ∩ M.E) ((B ∪ A) ∩ M.E) := by
      have h : A ∩ M.E ⊆ (B ∪ A) ∩ M.E :=
        Set.inter_subset_inter Set.subset_union_right <| subset_refl M.E
      rw [M.relRank_add_cancel h Set.inter_subset_left, relRank_inter_ground_self_left, add_zero]
    _ = M.relRank (A ∩ M.E) (B ∩ M.E) := by
      rw [Set.union_inter_distrib_right, <-relRank_eq_union_right]

lemma relRank_inter_ground_left {M : RankMatroid α} (A B : Set α) :
    M.relRank (A ∩ M.E) B = M.relRank A B := by
  rw [<-relRank_inter_ground, Set.inter_assoc, Set.inter_self, relRank_inter_ground]

lemma relRank_inter_ground_right {M : RankMatroid α} (A B : Set α) :
    M.relRank A (B ∩ M.E) = M.relRank A B := by
  rw [<-relRank_inter_ground, Set.inter_assoc, Set.inter_self, relRank_inter_ground]

lemma indep_subset {M : RankMatroid α} (hJ : M.Indep J) (rIJ : I ⊆ J) : M.Indep I := by
  refine M.indep_iff'.mpr ⟨rIJ.trans hJ.subset_ground, fun x hx ↦ ?_⟩
  have hJ := hJ.relRank_pos_of_sub_mem (rIJ hx)
  set A := I
  set B := J \ {x}
  have hAUB : J = I ∪ (J \ {x}) :=
    (Set.union_diff_cancel' (Set.singleton_subset_iff.mpr hx) rIJ).symm
  have hAIB : I \ {x} = I ∩ (J \ {x}) := by
    ext y;
    refine ⟨fun hY ↦ ?_, fun hY ↦ ?_⟩
    · refine ⟨Set.mem_of_mem_diff hY, Set.mem_diff_singleton.mpr ?_⟩
      refine ⟨rIJ (Set.mem_of_mem_diff hY), ?_⟩
      have h := Set.not_mem_of_mem_diff hY
      exact h
    have hyB : y ∈ J \ {x} := Set.mem_of_mem_inter_right hY
    have hynex : y ≠ x := by have := Set.not_mem_of_mem_diff hyB; exact this
    exact ⟨Set.mem_of_mem_inter_left hY, hynex⟩
  rw [hAUB] at hJ
  rw [hAIB]
  refine hJ.trans_le ?_
  rw [Set.union_comm, Set.inter_comm]
  exact M.relRank_union_le_relRank_inter B A

lemma insert_indep_iff_relRank_insert_pos {M : RankMatroid α} (hI_indep : M.Indep I)
    (hx : x ∈ M.E \ I) : M.Indep (Set.insert x I) ↔ M.relRank I (Set.insert x I) > 0 := by
  refine ⟨fun hIx_indep ↦ ?_, fun hr ↦ ?_⟩
  · have h := hIx_indep.indep x (Set.mem_insert x I)
    have : Set.insert x I \ {x} = I :=
      Set.insert_diff_self_of_not_mem (Set.not_mem_of_mem_diff hx)
    rwa [this] at h
  refine M.indep_iff'.mpr ?_
  refine ⟨Set.insert_subset (Set.mem_of_mem_diff hx) hI_indep.subset_ground, ?_⟩
  contrapose! hr
  rcases hr with ⟨y, hy, hr⟩
  by_cases hxy : x = y
  · rw [hxy] at hr hx ⊢
    have := Set.not_mem_of_mem_diff hx
    have : Set.insert y I \ {y} = I := Set.insert_diff_self_of_not_mem this
    rwa [this] at hr
  have h : M.relRank (I \ {y}) (Set.insert x I) ≤ 1 := by
    set C := (Set.insert x I)
    set B := (Set.insert x I \ {y})
    set A := (I \ {y})
    have h₂ : B ⊆ C := @Set.diff_subset α (insert x I) {y}
    have h₃ : A ⊆ B := by
      refine Set.diff_singleton_subset_iff.mpr ?_
      rw [Set.insert_diff_singleton]
      exact (Set.subset_insert x I).trans (Set.subset_insert y (Set.insert x I))
    have hrAB : M.relRank A B ≤ 1 := by
      have h := M.relRank_le_encard_diff A B
      rw [Set.diff_diff_right] at h
      have h := h.trans (Set.encard_union_le (B \ I) (B ∩ {y}))
      rw [Set.encard_eq_zero.mpr Set.diff_inter_self] at h
      simp only [add_zero] at h
      have : B \ I ⊆ {x} := by
        refine Set.diff_subset_iff.mpr ?_
        simp only [Set.union_singleton]
        exact h₂
      rcases Set.subset_singleton_iff_eq.mp this with h' | h'
      · rw [h'] at h; rw [Set.encard_empty] at h; exact h.trans zero_le_one
      rw [h'] at h; rwa [Set.encard_singleton] at h;
    have h : M.relRank A B + M.relRank B C <= 1 := by
      exact add_le_add hrAB hr
    have := M.relRank_add_cancel h₃ h₂
    rwa [<-this] at h
  set C := (Set.insert x I)
  set B := (I)
  set A := (I \ {y})
  have h' : M.relRank A C = M.relRank A B + M.relRank B C := by
    have h₂ : B ⊆ C := Set.subset_insert x I
    have h₃ : A ⊆ B := Set.diff_subset
    exact M.relRank_add_cancel h₃ h₂
  have h'' : M.relRank A B ≥ 1 := by
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · contradiction
    have := hI_indep.indep y hy
    exact ENat.one_le_iff_pos.mpr this
  contrapose! h
  rw [h'];
  have h := ENat.add_one_le_of_lt h
  simp only [zero_add] at h
  have := add_le_add h'' h
  rw [one_add_one_eq_two] at this
  refine (ENat.add_one_le_iff ?refine_2.intro.intro.hm).mp this
  exact ENat.coe_toNat_eq_self.mp rfl

lemma indep_subset_maximal_iff_relRank_zero {M : RankMatroid α} (hI : I ⊆ X) (hI_indep : M.Indep I)
    : (I ∈ (maximals (· ⊆ ·) {S | M.Indep S ∧ S ⊆ X}) ↔ M.relRank I X = 0) := by
  refine ⟨fun hI_max ↦ ?_, fun hr ↦ ?_⟩
  · by_cases hXI : X = I
    · rw [hXI]; exact relRank_self_eq_zero
    set S := {(insert x I) | x ∈ X \ I}
    have h : ∀ A ∈ S, I ⊆ A ∧ M.relRank I A = 0 := by
      rintro A ⟨x, hx_mem, rfl⟩
      refine ⟨Set.subset_insert x I, ?_⟩
      rcases (Set.mem_diff x).mpr hx_mem with ⟨hxX, hxI⟩
      by_cases hx : x ∉ M.E
      · rw [<-M.relRank_inter_ground, Set.insert_inter_of_not_mem hx, M.relRank_self_eq_zero]
      simp only [not_not] at hx
      contrapose! hI_max
      have hI_max : M.relRank I (insert x I) > 0 := by exact pos_iff_ne_zero.mpr hI_max
      suffices h : M.Indep (insert x I) by
        have : (insert x I) ∈ {S | M.Indep S ∧ S ⊆ X} := ⟨h, Set.insert_subset hxX hI⟩
        apply mem_maximals_iff.not.mpr
        push_neg; intro; use (insert x I)
        exact ⟨this, Set.subset_insert x I, by exact Set.ne_insert_of_not_mem I hxI⟩
      have hxEI : x ∈ M.E \ I := by exact (Set.mem_diff x).mpr ⟨hx, hxI⟩
      exact (insert_indep_iff_relRank_insert_pos hI_indep hxEI).mpr hI_max
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
  unfold maximals at hr;
  simp only [Set.mem_setOf_eq, and_imp, not_and, not_forall, Classical.not_imp,
    exists_prop, exists_and_left] at hr
  obtain ⟨I', hI'_indep, hI', hI'_ssubset⟩ := hr hI_indep hI
  rw [<-Set.ssubset_def] at hI'_ssubset
  obtain ⟨x, hxI', hxI⟩ := Set.exists_of_ssubset hI'_ssubset
  have : M.Indep (Set.insert x I) := by
    exact indep_subset hI'_indep (Set.insert_subset hxI' hI'_ssubset.subset)
  have hx : x ∈ M.E := hI'_indep.subset_ground hxI'
  rw [insert_indep_iff_relRank_insert_pos hI_indep ((Set.mem_diff x).mpr ⟨hx, hxI⟩)] at this
  have : M.relRank I X > 0 := by
    rw [M.relRank_add_cancel (Set.subset_insert x I) (Set.insert_subset (hI' hxI') hI)]
    exact Left.add_pos_of_pos_of_nonneg this (zero_le (M.relRank (Set.insert x I) X))
  exact pos_iff_ne_zero.mp this

@[simps!] protected def indepMatroid (M : RankMatroid α) : IndepMatroid α where
  E := M.E
  Indep := M.Indep

  indep_empty := by
    rw [M.indep_iff'];
    refine ⟨Set.empty_subset M.E, fun x hx ↦ ?_⟩
    contradiction

  indep_subset := by
    intro I J hJ rIJ
    exact indep_subset hJ rIJ

  indep_aug := by
    have hiff : {S | M.Indep S ∧ S ⊆ M.E} = {S | M.Indep S} := by
      ext S; constructor
      · simp only [Set.mem_setOf_eq, and_imp]; tauto
      simp only [Set.mem_setOf_eq]; exact fun h ↦ ⟨h, h.subset_ground⟩

    intro I B hI_indep hI_nmax hB_max
    have hB_indep := (mem_maximals_iff.mp hB_max).left
    have hrIE : M.relRank I M.E > 0 := by
      contrapose! hI_nmax
      norm_num at hI_nmax
      have := (indep_subset_maximal_iff_relRank_zero hI_indep.subset_ground hI_indep).mpr
      rw [hiff] at this
      exact this hI_nmax
    have hrBE : M.relRank B M.E = 0 := by
      have := (indep_subset_maximal_iff_relRank_zero hB_indep.subset_ground hB_indep).mp
      rw [hiff] at this
      exact this hB_max
    have hrI_IUB : M.relRank I (I ∪ B) > 0 := by
      have h₁ : I ⊆ (I ∪ B) := Set.subset_union_left
      have h₂ : (I ∪ B) ⊆ M.E := Set.union_subset hI_indep.subset_ground hB_indep.subset_ground
      calc
      0 < M.relRank I M.E := by assumption
      _ = M.relRank I (I ∪ B) + M.relRank (I ∪ B) M.E := by
        exact M.relRank_add_cancel h₁ h₂
      _ ≤ M.relRank I (I ∪ B) + M.relRank B M.E := by
        apply add_le_add_left
        exact relRank_mono_left Set.subset_union_right
      _ = M.relRank I (I ∪ B) := by
        rw [hrBE]
        simp only [add_zero]
    have hIUB_subset := (Set.union_subset hI_indep.subset_ground hB_indep.subset_ground)
    have hI_nmax :=
      (not_iff_not.mpr (indep_subset_maximal_iff_relRank_zero Set.subset_union_left hI_indep)).mpr
      (Ne.symm (hrI_IUB.ne))
    have h_maximals_nonempty :=
      M.indep_maximal hIUB_subset I hI_indep (Set.subset_union_left)
    rcases h_maximals_nonempty with ⟨I', ⟨hI'_indep, hI'_contains_I, hI'_in_IUB⟩, hI'_max⟩
    by_cases hII' : I = I'
    · rw [<-hII'] at hI'_max hI'_indep
      simp only [Set.mem_setOf_eq, and_imp] at hI'_max
      contrapose! hI_nmax
      clear hI_nmax
      rw [mem_maximals_iff]; simp only [Set.mem_setOf_eq, Set.subset_union_left, and_true, and_imp]
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

  indep_maximal := fun X hX ↦ M.indep_maximal hX
  subset_ground := fun I hI ↦ hI.subset_ground

@[simps!] protected def matroid (M : RankMatroid α) : Matroid α := M.indepMatroid.matroid

end RankMatroid

namespace Matroid

variable {α : Type*} {I : Set α}

lemma basis_of_maximal_extension (M : Matroid α) {I X J : Set α} (hX : X ⊆ M.E)
    (h : J ∈ maximals (· ⊆ ·) {I' | M.Indep I' ∧ I ⊆ I' ∧ I' ⊆ X}) : M.Basis J X := by
  unfold Basis; unfold maximals at h ⊢; simp only [Set.mem_setOf_eq, and_imp] at h ⊢
  obtain ⟨⟨hJ_indep, hIJ, hJX⟩, hJ_max⟩ := h
  refine ⟨⟨⟨hJ_indep, hJX⟩, ?_⟩, hX⟩
  intro J' hJ'_indep hJ'X hJJ'
  exact hJ_max hJ'_indep (hIJ.trans hJJ') hJ'X hJJ'

lemma relRank_intro (M : Matroid α) {A B : Set α} (hA : A ⊆ B) (hB : B ⊆ M.E) :
    ∃ I J : Set α, I ⊆ J ∧ M.Basis I A ∧ M.Basis J B ∧ M.relRank A B = (J \ I).encard := by
  obtain ⟨I, hI⟩ := M.maximality A (hA.trans hB) ∅ M.empty_indep (Set.empty_subset A)
  unfold maximals at hI; simp only [Set.empty_subset, true_and, Set.mem_setOf_eq, and_imp] at hI
  have ⟨⟨hI_indep, hI_subset_A⟩, _⟩ := hI
  obtain ⟨J, hJ⟩ := M.maximality B hB I hI_indep (hI_subset_A.trans hA)
  use I; use J
  unfold Basis
  have hIJ : I ⊆ J := hJ.1.2.1
  have hI_basis : M.Basis I A := by
    refine @basis_of_maximal_extension α M ∅ A I (hA.trans hB) ?_
    unfold maximals; simp only [Set.empty_subset, true_and, Set.mem_setOf_eq, and_imp]
    assumption
  have hJ_basis : M.Basis J B := by
    refine M.basis_of_maximal_extension hB hJ
  refine ⟨hIJ, hI_basis, hJ_basis, ?_⟩
  exact Basis.relRank_eq_encard_diff_of_subset_basis hI_basis hJ_basis hIJ

end Matroid

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {M : RankMatroid α} {x : α}

lemma relRank_indeps_eq_encard_diff (M : RankMatroid α) {A B : Set α} (hA : A ⊆ B) (hB : M.Indep B)
    : M.relRank A B = (B \ A).encard := by
  set P := fun n ↦ ∀ (A B : Set α), A ⊆ B → M.Indep B → (B \ A).encard = n → M.relRank A B = n
  have h_induc : ∀ n : ℕ∞, P n := by
    intro n
    refine (@ENat.nat_induction P n ?_ ?_ ?_)
    · intro A B _ _ h
      have := M.relRank_le_encard_diff A B
      rw [h] at this; simp only [nonpos_iff_eq_zero] at this; assumption
    · intro n hPn A B hA hB_indep h
      have : (n.succ : ℕ∞) > 0 := by exact NeZero.pos (n.succ : ℕ∞)
      rw [<-h] at this
      rcases (Set.encard_pos.mp this) with ⟨x, hx⟩
      set B' := B \ {x}
      have hxB : x ∈ B := Set.mem_of_mem_diff hx
      have hB'B : B' ⊆ B := by exact Set.diff_subset
      have hAB' : A ⊆ B' := Set.subset_diff_singleton hA (Set.not_mem_of_mem_diff hx)
      have hB'_indep : M.Indep B' := M.indep_subset hB_indep hB'B
      have hB'dA : B' \ A = (B \ A) \ {x} := by exact Set.diff_diff_comm
      have : (B' \ A).encard = n := by
        rw [hB'dA]
        rw [<-Set.encard_diff_singleton_add_one hx] at h
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h
        exact WithTop.add_right_cancel (ENat.coe_toNat_eq_self.mp (refl 1)) h
      have hrAB' : M.relRank A B' = n := hPn A B' hAB' hB'_indep this
      have hrB'B : M.relRank B' B = 1 := by
        have hle : M.relRank B' B <= 1 := by
          have := M.relRank_le_encard_diff (B \ {x}) B
          rw [Set.diff_diff_cancel_left (Set.singleton_subset_iff.mpr hxB)] at this
          simp only [Set.encard_singleton] at this; exact this
        have hgt : M.relRank B' B > 0 := by exact hB_indep.indep x hxB
        refine le_antisymm_iff.mpr ⟨hle, ENat.one_le_iff_pos.mpr hgt⟩
      rw [M.relRank_add_cancel hAB' hB'B, hrAB', hrB'B]
      have h11: (1 : ℕ) = (1 : ℕ∞) := rfl
      rw [<-h11, <-(ENat.coe_add n 1), Nat.succ_eq_add_one]
    intro hP A B hB hA_indep h
    by_contra! h_finite
    have : ∃ n, M.relRank A B = n := exists_eq'
    rcases this with ⟨c, hc⟩
    simp at h
    obtain ⟨D, hD_subset, hD_finite, hD_ncard⟩ :=
      Set.Infinite.exists_subset_ncard_eq h (ENat.toNat c + 1)
    have c_finite : c ≠ ⊤ := by rwa [hc] at h_finite
    have hcc : c + 1 = ↑(ENat.toNat c + 1) := by
      simp only [Nat.cast_add, Nat.cast_one, ENat.coe_toNat_eq_self.mpr c_finite]
    have hD_encard : D.encard = c + 1 := by
      have : D.encard = (D.ncard : ℕ∞) := by exact Eq.symm (Set.Finite.cast_ncard_eq hD_finite)
      rw [this, congrArg (Nat.cast) hD_ncard, hcc]
    clear hD_ncard hD_finite h_finite
    let A' := A ∪ D
    have hD_subset_B : D ⊆ B := hD_subset.trans (Set.diff_subset)
    have hA'_subset_B : A' ⊆ B := by exact (Set.union_subset hB hD_subset_B)
    have hA'_indep : M.Indep A' := by exact M.indep_subset hA_indep hA'_subset_B
    have hA'A : (A' \ A).encard = ↑(ENat.toNat c + 1) := by
      have : A ∩ D ⊆ ∅ := by
        have : Disjoint A (B \ A) := Set.disjoint_sdiff_right
        have : Disjoint A D := by exact Set.disjoint_of_subset (fun ⦃a⦄ a ↦ a) hD_subset this
        exact Set.disjoint_iff.mp this
      rw [Set.union_diff_cancel_left this, hD_encard, hcc]
    have hrAA' : M.relRank A A' = c + 1 := by
      rw [hP (ENat.toNat c + 1) A A' (Set.subset_union_left) hA'_indep hA'A, hcc]
    have hbad : M.relRank A B ≥ c + 1 := by
      rw [M.relRank_add_cancel Set.subset_union_left hA'_subset_B, hrAA']
      simp only [ge_iff_le, self_le_add_right]
    rw [hc] at hbad;
    exact (lt_irrefl c) ((ENat.add_one_le_iff c_finite).mp hbad)
  exact h_induc (B \ A).encard A B hA hB rfl

@[simp] theorem rankMatroid_relRank_eq_matroid_relRank (M : RankMatroid α)
    {A B : Set α} : M.relRank A B = M.matroid.relRank A B := by
  suffices h : ∀ {A B}, A ⊆ B → B ⊆ M.E → M.relRank A B = M.matroid.relRank A B by
    set A' := A ∩ M.E
    set B' := (B ∩ M.E) ∪ A'
    rw [<-relRank_inter_ground, relRank_eq_union_right, <-M.matroid.relRank_inter_ground_left,
        <-M.matroid.relRank_inter_ground_right, M.matroid.relRank_eq_union_right]
    simp only [matroid_E]
    refine h Set.subset_union_right ?_
    rw [<-Set.union_inter_distrib_right]
    exact Set.inter_subset_right
  intro A B hA hB
  obtain ⟨I, J, hI, ⟨hI_basis_A, _⟩, ⟨hJ_basis_B, _⟩, h⟩ := M.matroid.relRank_intro hA hB
  rw [h]; clear h;
  unfold maximals at hI_basis_A hJ_basis_B;
  simp only [matroid_Indep, Set.mem_setOf_eq, and_imp] at hI_basis_A hJ_basis_B
  obtain ⟨⟨hI_indep, hI_subset⟩, hI_max⟩ := hI_basis_A
  obtain ⟨⟨hJ_indep, hJ_subset⟩, hJ_max⟩ := hJ_basis_B
  rw [<-M.relRank_indeps_eq_encard_diff hI hJ_indep]
  have hIA : M.relRank I A = 0 := by
    rw [<-indep_subset_maximal_iff_relRank_zero hI_subset hI_indep]
    unfold maximals; simp only [Set.mem_setOf_eq, and_imp]
    exact ⟨⟨hI_indep, hI_subset⟩, hI_max⟩
  have hJB : M.relRank J B = 0 := by
    rw [<-indep_subset_maximal_iff_relRank_zero hJ_subset hJ_indep]
    unfold maximals; simp only [Set.mem_setOf_eq, and_imp]
    exact ⟨⟨hJ_indep, hJ_subset⟩, hJ_max⟩
  calc
    M.relRank A B = M.relRank I A + M.relRank A B := by
      rw [hIA]; simp only [zero_add]
    _ = M.relRank I B := by
      exact eq_comm.mp (M.relRank_add_cancel hI_subset hA)
    _ = M.relRank I J + M.relRank J B := by
      exact M.relRank_add_cancel hI hJ_subset
    _ = M.relRank I J := by
      rw [hJB]; simp only [add_zero]

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
    have h := rank_le_ncard Set.finite_empty;
    simp only [Set.encard_empty]
    simp only [Set.ncard_empty] at h
    exact congr_arg _ (Nat.eq_zero_of_le_zero h)
  have indep_empty_ncard : r ∅ = (∅ : Set α).ncard := by
    have h := rank_le_ncard Set.finite_empty;
    simp only [Set.ncard_empty] at h ⊢
    exact Nat.eq_zero_of_le_zero h
  have subset_ground : ∀ ⦃I : Set α⦄, Indep I → I ⊆ E := by
    intro I hI_indep
    have hIE_finite : (I ∩ E).Finite := (Set.Finite.subset hE Set.inter_subset_right)
    have hIE_indep : Indep (I ∩ E) := by
      refine LE.le.antisymm ?_ ?_
      · rw [<-Set.Finite.cast_ncard_eq hIE_finite, @Nat.cast_le ℕ∞]
        exact rank_le_ncard hIE_finite
      have := submodularity (I ∩ E) (I \ E)
      simp only [Set.inter_union_diff, rank_inter_ground (I \ E), Set.inter_assoc,
        Set.inter_diff_self, Set.diff_inter_self, Set.inter_empty, indep_empty_ncard,
        Set.ncard_empty, add_zero] at this
      rw [<-@Nat.cast_le ℕ∞] at this
      refine le_trans ?_ this
      rw [hI_indep]
      exact Set.encard_mono (Set.inter_subset_left)
    rw [h_indep] at hIE_indep hI_indep; rw [rank_inter_ground, hIE_indep] at hI_indep
    rw [<-Set.encard_diff_add_encard_inter I E] at hI_indep
    nth_rewrite 1 [<-zero_add (I ∩ E).encard] at hI_indep
    exact Set.diff_eq_empty.mp (Set.encard_eq_zero.mp (WithTop.add_right_cancel
        (Set.encard_ne_top_iff.mpr hIE_finite) hI_indep).symm)
  have indep_ncard : {I : Set α} → Indep I → r I = I.ncard := by
    intro I hI
    have hI_finite : I.Finite := Set.Finite.subset hE (subset_ground hI)
    rw [h_indep] at hI
    rw [<-Set.Finite.cast_ncard_eq hI_finite] at hI
    refine Nat.le_antisymm (rank_le_ncard hI_finite) ?_
    rw [<-@Nat.cast_le ℕ∞, hI]
  have indep_subset : ∀ ⦃I J : Set α⦄, Indep J → I ⊆ J → Indep I := by
    intro I J hJ_indep hI
    have hJ_finite : Set.Finite J := Set.Finite.subset hE (subset_ground hJ_indep)
    have hI_finite : Set.Finite I := Set.Finite.subset hJ_finite hI
    rw [h_indep]; dsimp only
    rw [<-Set.Finite.cast_ncard_eq hI_finite]
    apply congrArg Nat.cast
    refine LE.le.antisymm (rank_le_ncard hI_finite) ?_
    have := submodularity I (J \ I)
    rw [Set.union_diff_self, Set.inter_diff_self, indep_empty_ncard, Set.ncard_empty,
      add_zero, Set.union_eq_self_of_subset_left hI, indep_ncard hJ_indep] at this
    have := Nat.sub_le_of_le_add (this.trans (add_le_add (le_refl (r I))
      (rank_le_ncard (Set.Finite.subset hJ_finite Set.diff_subset))))
    simpa only [Set.ncard_diff hI hJ_finite,
      Nat.sub_sub_self (Set.ncard_le_ncard hI hJ_finite)] using this
  have indep_finite : ∀ ⦃I : Set α⦄, Indep I → Finite I :=
    fun I hI ↦ Set.Finite.subset hE (subset_ground hI)
  have indep_aug : ∀ ⦃I J : Set α⦄, Indep I → Indep J → I.ncard < J.ncard
      → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I) := by
    intro I J hI_indep hJ_indep hIJ
    by_contra!; rw [h_indep] at this; dsimp only at this
    have hI_finite : Finite I := indep_finite hI_indep
    have hJ_finite : Finite J := indep_finite hJ_indep
    have h : ∀ e ∈ J, e ∉ I → r (insert e I) = I.ncard := by
      intro e he he'
      have h' := this e he he'
      rw [<-Set.Finite.cast_ncard_eq (Set.Finite.insert e hI_finite)] at h'
      refine Nat.le_antisymm ?_ ?_
      · have h : r (insert e I) ≠ (insert e I).ncard := by
          contrapose! h'; exact congrArg _ h'
        have h_lt := Nat.lt_iff_le_and_ne.mpr ⟨(rank_le_ncard (Set.Finite.insert e hI_finite)), h⟩
        rw [Set.ncard_insert_of_not_mem he' hI_finite] at h_lt
        exact Nat.le_of_lt_succ h_lt
      rw [<-indep_ncard hI_indep]
      exact monotonicity (Set.subset_insert e I)
    have h_induc : ∀ n : ℕ, ∀ S ⊆ J \ I, S.ncard = n → r I = r (I ∪ S) := by
      intro n
      induction n with
      | zero =>
        intro S hS hS_ncard
        have hS_finite : Finite S := Set.Finite.subset hJ_finite (hS.trans Set.diff_subset)
        rw [(Set.ncard_eq_zero hS_finite).mp hS_ncard, Set.union_empty]
      | succ n hn =>
        intro S hS hS_ncard
        obtain ⟨y, T, hy, rfl, hT⟩ := Set.eq_insert_of_ncard_eq_succ hS_ncard
        refine LE.le.antisymm (monotonicity (Set.subset_union_left)) ?_
        rw [<-Set.singleton_union, Set.union_union_distrib_left]
        have := submodularity (I ∪ {y}) (I ∪ T)
        nth_rw 3 [Set.union_singleton] at this
        have hT_JI : T ⊆ J \ I := (Set.subset_insert y T).trans hS
        have hy_JI : y ∈ J \ I := hS (Set.mem_insert y T)
        rwa [<-hn T ((Set.subset_insert y T).trans hS) hT,
          h y (Set.mem_of_mem_diff hy_JI) (Set.not_mem_of_mem_diff hy_JI),
          <-Set.union_inter_distrib_left, Set.singleton_inter_eq_empty.mpr hy,
          Set.union_empty, add_le_add_iff_right, <-indep_ncard hI_indep] at this
    have hI_IJ := h_induc (J \ I).ncard (J \ I) subset_rfl rfl
    simp only [Set.union_diff_self] at hI_IJ
    have h_bad : r J ≤ r (I ∪ J) := monotonicity Set.subset_union_right
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
        rw [Set.encard_eq_zero.mp hX, rank_empty, Set.encard_empty]
        simp only [CharP.cast_eq_zero, le_refl]
      | hsuc n hn =>
        have hX_finite : Finite X := by
          have : (n.succ : ℕ∞) ≠ ⊤ := by exact ENat.coe_ne_top n.succ
          rw [<-hX, Set.encard_ne_top_iff] at this;
          assumption
        have h : X.ncard = n + 1 := by
          rw [<-Set.Finite.cast_ncard_eq hX_finite, Nat.succ_eq_add_one] at hX
          rwa [<-WithTop.coe_eq_coe]
        obtain ⟨x, Y, hx, rfl, hY⟩ := Set.eq_insert_of_ncard_eq_succ h
        have hY_finite := Set.Finite.subset hX_finite (Set.subset_insert x Y)
        have hY' : Y.encard = n := by
          rw [<-Set.Finite.cast_ncard_eq hY_finite, hY]
        rw [Set.encard_insert_of_not_mem hx, <-Set.union_singleton,
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
      exact h (A ∩ E) (B ∩ E) (Set.inter_subset_inter_left E hA) Set.inter_subset_right
    clear A B hA
    have h_induc : ∀ n : ℕ, ∀ {A B : Set α}, A ⊆ B → B ⊆ E → A.ncard + n = B.ncard → r A ≤ r B := by
      intro n A B hA hB
      have hB_finite := Set.Finite.subset hE hB
      have hA_finite := Set.Finite.subset hB_finite hA
      induction n generalizing A B with
      | zero =>
        intro h; simp [add_zero] at h
        rw [Set.eq_of_subset_of_ncard_le hA h.ge hB_finite]
      | succ n hn =>
        intro h;
        rw [<-Set.ncard_diff_add_ncard_of_subset hA hB_finite, add_comm] at h
        simp only [add_left_inj] at h
        obtain ⟨x, S, _, hxS, hS⟩ := Set.eq_insert_of_ncard_eq_succ h.symm
        have : B = (A ∪ S) ∪ {x} := by
          rw [Set.union_assoc, Set.union_singleton, hxS,
            Set.union_diff_self, Set.union_eq_self_of_subset_left hA]
        have hAS : (A ∪ S) ⊆ B := by rw [this]; exact Set.subset_union_left
        have hAS_disjoint : Disjoint A S := by
          have : S ⊆ B \ A := by rw [<-hxS]; exact Set.subset_insert x S
          exact (Set.subset_diff.mp this).right.symm
        have hAS_finite : (A ∪ S).Finite := Set.Finite.subset hB_finite hAS
        have hAS_encard : A.ncard + n = (A ∪ S).ncard := by
          rw [Set.ncard_union_eq hAS_disjoint hA_finite
            (Set.Finite.subset hAS_finite Set.subset_union_right), add_right_inj, hS]
        rw [this]
        exact le_trans (hn Set.subset_union_left (hAS.trans hB) hAS_finite hA_finite hAS_encard)
          (rank_step (A ∪ S) x).left
    intro A B hA hB
    have h_ncard : A.ncard + (B \ A).ncard = B.ncard := by
      rw [Set.ncard_diff hA (Set.Finite.subset hE hB),
          Nat.add_sub_cancel' (Set.ncard_le_ncard hA (Set.Finite.subset hE hB))]
    exact h_induc (B \ A).ncard hA hB h_ncard
  exact IndepMatroid.ofFiniteRankAxioms hE r
    rank_le_ncard monotonicity submodularity rank_inter_ground
