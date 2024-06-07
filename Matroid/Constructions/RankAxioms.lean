import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms

/-- A matroid as defined by the (relative) rank axioms. The constructed
  `RankMatroid` can be then converted into a `Matroid` with `RankMatroid.matroid` -/
structure RankMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The (relative) rank function -/
  (relRank : Set α → Set α → ℕ∞)

  (rel_rank_le_encard_diff {A B : Set α} : A ⊆ E → B ⊆ A → relRank A B ≤ (A \ B).encard)
  (rel_rank_union_le_relRank_inter {A B : Set α} : A ⊆ E → B ⊆ E →
    relRank (A ∪ B) B ≤ relRank A (A ∩ B))
  (rel_rank_add_cancel {A B C : Set α} : A ⊆ E → B ⊆ A → C ⊆ B → (relRank A C) = (relRank A B) + (relRank B C))
  (rel_rank_sUnion_eq_zero {S : Set (Set α)} {B : Set α} :
      (∀ A ∈ S, B ⊆ A ∧ A ⊆ E ∧ relRank A B = 0) → relRank (⋃₀ S) B = 0)

  (Indep : Set α → Prop)
  (indep_maximal : ∀ X ⊆ E, Matroid.ExistsMaximalSubsetProperty Indep X)
  (indep_iff' : ∀ I, Indep I ↔ I ⊆ E ∧ ∀ x ∈ I, relRank I (I \ {x}) > 0 )

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {M : RankMatroid α} {x : α}

def indepSubsets (M : RankMatroid α) (A : Set α) : Set (Set α) :=
  {I | M.Indep I ∧ I ⊆ A}

def Basis' (M : RankMatroid α) (I A : Set α) : Prop :=
  I ∈ maximals (· ⊆ ·) (M.indepSubsets A)

theorem r_nonneg : M.relRank A B ≥ 0 := by
  exact zero_le (M.relRank A B)

theorem relRank_self_eq_zero (h : A ⊆ M.E) : M.relRank A A = 0 := by
  have := M.rel_rank_le_encard_diff h (subset_refl A)
  rw [Set.diff_eq_empty.mpr fun ⦃a⦄ a ↦ a, Set.encard_empty] at this
  exact nonpos_iff_eq_zero.mp this

theorem Indep.subset_ground (h : M.Indep I) : I ⊆ M.E := by
  rw [indep_iff'] at h
  exact h.left

theorem Indep.indep (h : M.Indep I) :  ∀ x ∈ I, M.relRank I (I \ {x}) > 0  := by
  rw [indep_iff'] at h
  exact h.right

theorem indep_subset (hJ : M.Indep J) (rIJ : I ⊆ J) : M.Indep I := by
  rw [M.indep_iff']
  refine ⟨rIJ.trans hJ.subset_ground, fun x hx ↦ ?_⟩
  have hJ_indep := hJ.subset_ground
  have hJ := hJ.indep x (Set.mem_of_mem_of_subset hx rIJ)
  set A := I
  set B := J \ {x}
  have hAUB : J = A ∪ B := by
    refine (Set.union_diff_cancel' ?h₁ rIJ).symm
    exact Set.singleton_subset_iff.mpr hx
  have hAIB : A \ {x} = A ∩ B := by
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
  have hA : A ⊆ M.E := (rIJ.trans hJ_indep)
  have hB : B ⊆ M.E := ((Set.diff_subset).trans hJ_indep)
  exact hJ.trans_le (M.rel_rank_union_le_relRank_inter hA hB)

theorem r_le_r_subset_right (hX : X ⊆ M.E) (hAX : A ⊆ X) (hBA : B ⊆ A) : M.relRank X A ≤ M.relRank X B := by
  rw [M.rel_rank_add_cancel hX hAX hBA]; simp only [self_le_add_right]

theorem insert_indep_iff_r_insert_pos (hI_indep : M.Indep I) (hx : x ∈ M.E \ I)
    : M.Indep (Set.insert x I) ↔ M.relRank (Set.insert x I) I > 0 := by
  refine ⟨fun hIx_indep ↦ ?_, fun hr ↦ ?_⟩
  · have h := hIx_indep.indep x (Set.mem_insert x I)
    have : Set.insert x I \ {x} = I :=
      Set.insert_diff_self_of_not_mem (Set.not_mem_of_mem_diff hx)
    rwa [this] at h
  refine (M.indep_iff' (Set.insert x I)).mpr ?_
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
    have h₂ : B ⊆ A := @Set.diff_subset α (insert x I) {y}
    have h₃ : C ⊆ B := by
      refine Set.diff_singleton_subset_iff.mpr ?_
      rw [Set.insert_diff_singleton]
      exact (Set.subset_insert x I).trans (Set.subset_insert y (Set.insert x I))
    have hrBC : M.relRank B C ≤ 1 := by
      have h := M.rel_rank_le_encard_diff (h₂.trans h₁) h₃
      rw [Set.diff_diff_right] at h
      have h := h.trans (Set.encard_union_le (B \ I) (B ∩ {y}))
      rw [Set.encard_eq_zero.mpr Set.diff_inter_self] at h
      simp only [add_zero] at h
      have : B \ I ⊆ {x} := by refine Set.diff_subset_iff.mpr ?_; simp only [Set.union_singleton]; exact h₂
      rcases Set.subset_singleton_iff_eq.mp this with h' | h'
      · rw [h'] at h; rw [Set.encard_empty] at h; exact h.trans zero_le_one
      rw [h'] at h; rwa [Set.encard_singleton] at h;
    have h : M.relRank A B + M.relRank B C <= 1 := by
      exact add_le_add hr hrBC
    have := M.rel_rank_add_cancel h₁ h₂ h₃
    rwa [<-this] at h
  set A := (Set.insert x I)
  set B := (I)
  set C := (I \ {y})
  have h' : M.relRank A C = M.relRank A B + M.relRank B C := by
    have h₁ : A ⊆ M.E := Set.insert_subset (Set.mem_of_mem_diff hx) hI_indep.subset_ground
    have h₂ : B ⊆ A := Set.subset_insert x I
    have h₃ : C ⊆ B := Set.diff_subset
    exact M.rel_rank_add_cancel h₁ h₂ h₃
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

theorem indep_subset_maximal_iff_relrank_zero (hX : X ⊆ M.E) (hI : I ⊆ X) (hI_indep : M.Indep I) :
    (I ∈ (maximals (· ⊆ ·) {S | M.Indep S ∧ S ⊆ X}) ↔ M.relRank X I = 0) := by
  refine ⟨fun hI_max ↦ ?_, fun hr ↦ ?_⟩
  · by_cases hXI : X = I
    · rw [hXI]; exact relRank_self_eq_zero hI_indep.subset_ground
    set S := {(insert x I) | x ∈ X \ I}
    have h : ∀ A ∈ S, I ⊆ A ∧ A ⊆ M.E ∧ M.relRank A I = 0 := by
      rintro A ⟨x, hx_mem, rfl⟩
      rcases (Set.mem_diff x).mpr hx_mem with ⟨hxX, hxI⟩
      refine ⟨Set.subset_insert x I, Set.insert_subset (hX hxX) hI_indep.subset_ground, ?_⟩
      contrapose! hI_max
      have hI_max : M.relRank (insert x I) I > 0 := by exact pos_iff_ne_zero.mpr hI_max
      suffices h : M.Indep (insert x I) by
        have : (insert x I) ∈ {S | M.Indep S ∧ S ⊆ X} := ⟨h, Set.insert_subset hxX hI⟩
        apply mem_maximals_iff.not.mpr
        push_neg; intro; use (insert x I)
        exact ⟨this, Set.subset_insert x I, by exact Set.ne_insert_of_not_mem I hxI⟩
      have hxEI : x ∈ M.E \ I := by exact (Set.mem_diff x).mpr ⟨hX hxX, hxI⟩
      exact (insert_indep_iff_r_insert_pos hI_indep hxEI).mpr hI_max
    have := M.rel_rank_sUnion_eq_zero h
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
  simp only [Set.mem_setOf_eq, and_imp, not_and, not_forall, Classical.not_imp, exists_prop, exists_and_left] at hr
  obtain ⟨I', hI'_indep, hI', hI'_ssubset⟩ := hr hI_indep hI
  rw [<-Set.ssubset_def] at hI'_ssubset
  obtain ⟨x, hxI', hxI⟩ := Set.exists_of_ssubset hI'_ssubset
  have : M.Indep (Set.insert x I) := by
    exact indep_subset hI'_indep (Set.insert_subset hxI' hI'_ssubset.subset)
  rw [insert_indep_iff_r_insert_pos hI_indep ((Set.mem_diff x).mpr ⟨(hI'.trans hX) hxI', hxI⟩)] at this
  have : M.relRank X I > 0 := by
    rw [M.rel_rank_add_cancel hX (Set.insert_subset (hI' hxI') hI) (Set.subset_insert x I)]
    have this' : M.relRank X (Set.insert x I) ≥ 0 := by exact r_nonneg
    exact Right.add_pos_of_nonneg_of_pos this' this
  exact pos_iff_ne_zero.mp this

@[simps] protected def indepMatroid (M : RankMatroid α) : IndepMatroid α where
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
      have h₁ : I ⊆ (I ∪ B) := by exact Set.subset_union_left
      have h₂ : (I ∪ B) ⊆ M.E := by exact Set.union_subset hI_indep.subset_ground hB_indep.subset_ground
      have h₃ : M.E ⊆ M.E := by exact fun ⦃a⦄ a ↦ a
      calc
      0 < M.relRank M.E I := by assumption
      _ = M.relRank M.E (I ∪ B) + M.relRank (I ∪ B) I := by
        exact M.rel_rank_add_cancel h₃ h₂ h₁
      _ ≤ M.relRank M.E B + M.relRank (I ∪ B) I := by
        apply add_le_add_right
        exact r_le_r_subset_right h₃ h₂ (Set.subset_union_right)
      _ = M.relRank (I ∪ B) I := by
        rw [hrEB]
        simp only [zero_add]
    have hIUB_subset := (Set.union_subset hI_indep.subset_ground hB_indep.subset_ground)
    have hI_nmax := (not_iff_not.mpr (indep_subset_maximal_iff_relrank_zero hIUB_subset (Set.subset_union_left) hI_indep)).mpr (Ne.symm (hrIUB_I.ne))
    have h_maximals_nonempty := M.indep_maximal (I ∪ B) hIUB_subset I hI_indep  (Set.subset_union_left)
    rcases h_maximals_nonempty with ⟨I', ⟨hI'_indep, hI'_contains_I, hI'_in_IUB⟩, hI'_max⟩
    by_cases hII' : I = I'
    · rw [<-hII'] at hI'_max hI'_indep
      simp only [Set.mem_setOf_eq, and_imp] at hI'_max
      contrapose! hI_nmax
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

  indep_maximal := fun X hX ↦ M.indep_maximal X hX
  subset_ground := fun I hI ↦ hI.subset_ground

@[simps!] protected def matroid (M : RankMatroid α) : Matroid α := M.indepMatroid.matroid

end RankMatroid

namespace Matroid

variable {α : Type*} {I : Set α}

def indepSubsets (M : Matroid α) (A : Set α) : Set (Set α) :=
  {I | M.Indep I ∧ I ⊆ A}

noncomputable def relRank (M : Matroid α) (A B : Set α) : ℕ∞ :=
  sSup {x | ∃ I J : Set α, J ⊆ I ∧ I ∈ M.indepSubsets A ∧ M.Basis' J B ∧ x = (I \ J).encard}

theorem basis_of_maximal_extension (M : Matroid α) {I X J : Set α}
    (h : J ∈ maximals (· ⊆ ·) {I' | M.Indep I' ∧ I ⊆ I' ∧ I' ⊆ X}) : M.Basis' J X := by
  unfold Basis'; unfold maximals at h ⊢; simp only [Set.mem_setOf_eq, and_imp] at h ⊢
  obtain ⟨⟨hJ_indep, hIJ, hJX⟩, hJ_max⟩ := h
  refine ⟨⟨hJ_indep, hJX⟩, ?_⟩
  intro J' hJ'_indep hJ'X hJJ'
  exact hJ_max hJ'_indep (hIJ.trans hJJ') hJ'X hJJ'

theorem rel_rank_eq_any_choice (M : Matroid α) {A B : Set α} (hB : B ⊆ A) (hA : A ⊆ M.E) {I J : Set α}
    (h : J ⊆ I) (hI : M.Basis' I A) (hJ : M.Basis' J B) :
    M.relRank A B = (I \ J).encard := by
  unfold Basis' maximals at hJ; simp only [Set.mem_setOf_eq, and_imp] at hJ
  have ⟨⟨hJ_indep, hJ_subset_B⟩, hJ_max⟩ := hJ
  apply le_antisymm_iff.mpr; rw [and_comm]
  constructor
  · have : (I \ J).encard ∈ {x | ∃ I J : Set α, J ⊆ I ∧ I ∈ M.indepSubsets A ∧ J ∈ maximals (· ⊆ ·) (M.indepSubsets B) ∧ x = (I \ J).encard} := by
      use I, J; unfold maximals indepSubsets; simp only [Set.mem_setOf_eq, and_imp, and_true];
      unfold Basis' at hI
      exact ⟨h, (maximals_subset (fun a b ↦ a ⊆ b) (M.indepSubsets A)) hI, hJ.1, hJ.2⟩
    exact le_sSup this
  apply sSup_le; intro r; simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro I' J' h' hI' hJ' rfl
  sorry

theorem rel_rank_exists (M : Matroid α) {A B : Set α} (hB : B ⊆ A) (hA : A ⊆ M.E) :
    ∃ I J : Set α, J ⊆ I ∧ M.Basis' I A ∧ M.Basis' J B ∧ M.relRank A B = (I \ J).encard := by
  obtain ⟨J, hJ⟩ := M.maximality B (hB.trans hA) ∅ M.empty_indep (Set.empty_subset B)
  unfold maximals at hJ; simp only [Set.empty_subset, true_and, Set.mem_setOf_eq, and_imp] at hJ
  have ⟨⟨hJ_indep, hJ_subset_B⟩, hJ_max⟩ := hJ
  obtain ⟨I, hI⟩ := M.maximality A hA J hJ_indep (hJ_subset_B.trans hB)
  use I; use J
  unfold Basis'
  have hIJ : J ⊆ I := hI.1.2.1
  have hI_basis : M.Basis' I A := by
    refine M.basis_of_maximal_extension hA (hJ.1.2.trans hB) hJ.1.1 hI
  have hJ_basis : M.Basis' J B := by
    refine M.basis_of_maximal_extension (hB.trans hA) (Set.empty_subset B) M.empty_indep ?_
    unfold maximals; simp only [Set.empty_subset, true_and, Set.mem_setOf_eq, and_imp]
    assumption
  exact ⟨hIJ, hI_basis, hJ_basis, M.rel_rank_eq_any_choice hB hA hIJ hI_basis hJ_basis⟩

end Matroid

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {M : RankMatroid α} {x : α}

theorem relRank_indeps_eq_encard_diff (M : RankMatroid α) {A B : Set α} (hB : B ⊆ A)
    (hA : M.Indep A) : M.relRank A B = (A \ B).encard := by
  set P := fun n ↦ ∀ (A B : Set α), B ⊆ A → M.Indep A → (A \ B).encard = n → M.relRank A B = n
  have h_induc : ∀ n : ℕ∞, P n := by
    intro n
    refine (@ENat.nat_induction P n ?_ ?_ ?_)
    · intro A B hB hA_indep h
      have := M.rel_rank_le_encard_diff hA_indep.subset_ground hB
      rw [h] at this; simp only [nonpos_iff_eq_zero] at this; assumption
    · intro n hPn A B hB hA_indep h
      have : (n.succ : ℕ∞) > 0 := by exact NeZero.pos (n.succ : ℕ∞)
      rw [<-h] at this
      rcases (Set.encard_pos.mp this) with ⟨x, hx⟩
      set A' := A \ {x}
      have hxA : x ∈ A := Set.mem_of_mem_diff hx
      have hAA' : A' ⊆ A := by exact Set.diff_subset
      have hBA' : B ⊆ A' := Set.subset_diff_singleton hB (Set.not_mem_of_mem_diff hx)
      have hA'_indep : M.Indep A' := M.indep_subset hA_indep hAA'
      have hA'dB: A' \ B = (A \ B) \ {x} := by exact Set.diff_diff_comm
      have : (A' \ B).encard = n := by
        rw [hA'dB]
        rw [<-Set.encard_diff_singleton_add_one hx] at h
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h
        exact WithTop.add_right_cancel (ENat.coe_toNat_eq_self.mp (refl 1)) h
      have hrA'B : M.relRank A' B = n := hPn A' B hBA' hA'_indep this
      have hrAA' : M.relRank A A' = 1 := by
        have hle : M.relRank A A' <= 1 := by
          have := M.rel_rank_le_encard_diff hA_indep.subset_ground (@Set.diff_subset α A {x})
          rw [Set.diff_diff_cancel_left (Set.singleton_subset_iff.mpr hxA)] at this
          simp only [Set.encard_singleton] at this; exact this
        have hgt : M.relRank A A' > 0 := by exact hA_indep.indep x hxA
        refine le_antisymm_iff.mpr ⟨hle, ENat.one_le_iff_pos.mpr hgt⟩
      rw [M.rel_rank_add_cancel hA_indep.subset_ground hAA' hBA', hrA'B, hrAA']
      have h11: (1 : ℕ) = (1 : ℕ∞) := rfl
      rw [<-h11, <-(ENat.coe_add 1 n), add_comm, Nat.succ_eq_add_one];
    intro hP A B hB hA_indep h
    by_contra! h_finite
    have : ∃ n, M.relRank A B = n := by
      exact exists_eq'
    -- rcases Option.ne_none_iff_exists'.mp h_finite with ⟨c, hc⟩
    rcases this with ⟨c, hc⟩
    simp at h
    obtain ⟨D, hD_subset, hD_finite, hD_ncard⟩ := Set.Infinite.exists_subset_ncard_eq h (ENat.toNat c + 1)
    have c_finite : c ≠ ⊤ := by rwa [hc] at h_finite
    have hcc : c + 1 = ↑(ENat.toNat c + 1) := by
      simp only [Nat.cast_add, Nat.cast_one, ENat.coe_toNat_eq_self.mpr c_finite]
    have hD_encard : D.encard = c + 1 := by
      have : D.encard = (D.ncard : ℕ∞) := by exact Eq.symm (Set.Finite.cast_ncard_eq hD_finite)
      rw [this, congrArg (Nat.cast) hD_ncard, hcc]
    clear hD_ncard hD_finite h_finite
    let B' := B ∪ D
    have hD_subset_A : D ⊆ A := hD_subset.trans (Set.diff_subset)
    have hB'_subset_A : B' ⊆ A := by exact (Set.union_subset hB hD_subset_A)
    have hB'_indep : M.Indep B' := by exact M.indep_subset hA_indep hB'_subset_A
    have hB'B : (B' \ B).encard = ↑(ENat.toNat c + 1) := by
      have : B ∩ D ⊆ ∅ := by
        have : Disjoint B (A \ B) := Set.disjoint_sdiff_right
        have : Disjoint B D := by exact Set.disjoint_of_subset (fun ⦃a⦄ a ↦ a) hD_subset this
        exact Set.disjoint_iff.mp this
      rw [Set.union_diff_cancel_left this, hD_encard, hcc]
    have hrB'B : M.relRank B' B = c + 1 := by
      rw [hP (ENat.toNat c + 1) B' B (Set.subset_union_left) hB'_indep hB'B, hcc]
    have hbad : M.relRank A B ≥ c + 1 := by
      rw [M.rel_rank_add_cancel hA_indep.subset_ground hB'_subset_A (Set.subset_union_left), hrB'B]
      simp only [ge_iff_le, self_le_add_left]
    rw [hc] at hbad;
    exact (lt_irrefl c) ((ENat.add_one_le_iff c_finite).mp hbad)
  exact h_induc (A \ B).encard A B hB hA rfl

-- this should be simp, with reversed inequality
theorem rankMatroid_rel_rank_eq_matroid_rel_rank (M : RankMatroid α)
    {A B : Set α} (hB : B ⊆ A) (hA : A ⊆ M.E) : M.relRank A B = M.matroid.relRank A B := by
  obtain ⟨I, J, hJ, hI_basis_A, hJ_basis_B, h⟩ := M.matroid.rel_rank_exists hB hA
  rw [h]; clear h;
  unfold Matroid.Basis' maximals at hI_basis_A hJ_basis_B;
  simp only [matroid_Indep, Set.mem_setOf_eq, and_imp] at hI_basis_A hJ_basis_B
  obtain ⟨⟨hI_indep, hI_subset⟩, hI_max⟩ := hI_basis_A
  obtain ⟨⟨hJ_indep, hJ_subset⟩, hJ_max⟩ := hJ_basis_B
  rw [<-M.relRank_indeps_eq_encard_diff hJ hI_indep]
  have hAI : M.relRank A I = 0 := by
    rw [<-indep_subset_maximal_iff_relrank_zero hA hI_subset hI_indep]
    unfold maximals; simp only [Set.mem_setOf_eq, and_imp]
    exact ⟨⟨hI_indep, hI_subset⟩, hI_max⟩
  have hBJ : M.relRank B J = 0 := by
    rw [<-indep_subset_maximal_iff_relrank_zero (hB.trans hA) hJ_subset hJ_indep]
    unfold maximals; simp only [Set.mem_setOf_eq, and_imp]
    exact ⟨⟨hJ_indep, hJ_subset⟩, hJ_max⟩
  calc
    M.relRank A B = M.relRank A B + M.relRank B J := by
      rw [hBJ]; simp only [add_zero]
    _ = M.relRank A J := by
      exact eq_comm.mp (M.rel_rank_add_cancel hA hB hJ_subset)
    _ = M.relRank A I + M.relRank I J := by
      exact M.rel_rank_add_cancel hA hI_subset hJ
    _ = M.relRank I J := by
      rw [hAI]; simp only [zero_add]

theorem encard_to_ncard {n : ℕ} {S : Set α} (h : S.encard = n) : S.ncard = n := by
  have : S.Finite := by exact Set.finite_of_encard_eq_coe h
  rw [<-Set.Finite.cast_ncard_eq this] at h
  simp only [Nat.cast_inj] at h; assumption

def RankMatroid.ofFinite {E : Set α} (hE : E.Finite) (r : Set α → ℕ)
    (rank_le_encard : ∀ (X : Set α), r X ≤ X.encard)
    (monotonicity : {A B : Set α} → A ⊆ E → B ⊆ A → r B ≤ r A)
    (submodularity : {A B : Set α} → A ⊆ E → B ⊆ E → (r (A ∪ B)) + (r (A ∩ B)) ≤ r A + r B)
    : RankMatroid α where
  E := E
  relRank := fun A B ↦ r A - r B
  rel_rank_le_encard_diff := by
    intro A B hA hB; simp only [tsub_le_iff_right]
    have hr_empty : r ∅ = 0 := by
      have := rank_le_encard ∅
      simp only [Set.encard_empty, nonpos_iff_eq_zero, Nat.cast_eq_zero] at this
      assumption
    have h := submodularity ((@Set.diff_subset α A B).trans hA) (hB.trans hA)
    simp only [Set.diff_union_self, Set.diff_inter_self] at h
    rw [hr_empty, Set.union_eq_self_of_subset_right hB] at h; simp only [add_zero] at h
    have h' := rank_le_encard (A \ B)
    have : r A ≤ (r (A \ B) + r B : ℕ∞) := by
      rw [<-ENat.coe_add]; exact Nat.cast_le.mpr h
    exact le_add_of_le_add_right this (rank_le_encard (A \ B))
  rel_rank_union_le_relRank_inter := by
    dsimp only; intro A B hA hB
    apply Nat.mono_cast
    simp only [Nat.cast_id]
    apply Nat.le_sub_of_add_le
    have : Sub.sub (r (A ∪ B)) (r B) + (r (A ∩ B)) = (r (A ∪ B)) - (r B) + (r (A ∩ B)) := by
      exact rfl
    rw [this, <-@Nat.sub_add_comm (r (A ∪ B)) (r (A ∩ B)) (r B) (monotonicity (Set.union_subset hA hB) (Set.subset_union_right))]
    apply Nat.sub_le_iff_le_add.mpr
    exact submodularity hA hB
  rel_rank_add_cancel := by
    intro A B C hA hB hC; dsimp only
    refine Eq.symm (tsub_add_tsub_cancel ?hab ?hcb)
    · exact Nat.cast_le.mpr (monotonicity hA hB)
    exact Nat.cast_le.mpr (monotonicity (hB.trans hA) hC)
  rel_rank_sUnion_eq_zero := by
    dsimp only
    intro S B hS
    have hPE_finite : (𝒫 E).Finite := Set.Finite.finite_subsets hE
    have hS_subset_PE : S ⊆ 𝒫 E := by
      intro A hA; simp only [Set.mem_powerset_iff]; exact (hS A hA).2.1
    have hS_finite : S.Finite := Set.Finite.subset hPE_finite hS_subset_PE
    have h_induc : ∀ n : ℕ, ∀ S : Set (Set α), ∀ B, (∀ A ∈ S, B ⊆ A ∧ A ⊆ E ∧ (r A : ℕ∞) - (r B : ℕ∞) = 0) → S.encard = n → r (⋃₀ S) - r B = 0 := by
      intro n
      induction n with
      | zero =>
        intro S B hS hS_encard
        have : ⋃₀ S = ∅ := by
          rw [<-Set.sUnion_empty]
          refine congrArg Set.sUnion ?_
          exact Set.encard_eq_zero.mp hS_encard
        have h : r ∅ = 0 := by
          have := (rank_le_encard ∅)
          simp only [Set.encard_empty, nonpos_iff_eq_zero, Nat.cast_eq_zero] at this
          assumption
        rw [this, h]; simp only [ge_iff_le, zero_le, tsub_eq_zero_of_le]
      | succ n hn =>
        intro S B hS hS_encard
        have hS_rank : ∀ A ∈ S, r A = r B := by
          intro A hA
          have h₁ := (hS A hA).2.2
          have h₂ := monotonicity (hS A hA).2.1 (hS A hA).1
          rw [<-ENat.coe_sub] at h₁
          have : r A - r B = 0 := by exact WithTop.coe_eq_zero.mp h₁
          have := (Nat.sub_eq_iff_eq_add h₂).mp this
          simp only [zero_add] at this; assumption
        obtain ⟨A, S₀, ⟨h_nmem, h_ins, h_ncard⟩⟩ := Set.eq_insert_of_ncard_eq_succ (encard_to_ncard hS_encard)
        rw [<-h_ins] at hS_rank hS hS_encard ⊢
        rw [Set.sUnion_insert A S₀]
        have hS₀_subsetE : ⋃₀ S₀ ⊆ E := by
          apply Set.sUnion_subset_iff.mpr
          intro B hB; exact (hS B (Set.mem_insert_of_mem A hB)).2.1
        have hB_subsetS₀ : B ⊆ ⋃₀ S₀ := by
          sorry
        have h : r (A ∪ ⋃₀ S₀) + r (A ∩ ⋃₀ S₀) ≤ r A + r (⋃₀ S₀) := by
          exact submodularity (hS A (Set.mem_insert A S₀)).2.1 hS₀_subsetE
        have hS₀_encard : S₀.encard = n := by
          rw [Set.encard_insert_of_not_mem h_nmem] at hS_encard
          simp only [Nat.cast_add, Nat.cast_one] at hS_encard
          sorry
        simp only [Set.sUnion_insert] at hn
        have hS₀ : (∀ A ∈ S₀, B ⊆ A ∧ A ⊆ E ∧ (r A : ℕ∞) - r B = 0) := by
          intro A' hA'; exact hS A' (Set.mem_insert_of_mem A hA')
        have : r (⋃₀ S₀) = r B := by
          have := hn S₀ B hS₀ hS₀_encard
          rw [Nat.sub_eq_iff_eq_add (monotonicity hS₀_subsetE hB_subsetS₀)] at this
          simp only [zero_add] at this; assumption
        rw [this, hS_rank A (Set.mem_insert A S₀)] at h
        have : r (A ∩ ⋃₀ S₀) = r B := by
          apply le_antisymm_iff.mpr; constructor
          · rw [<-this]; exact monotonicity hS₀_subsetE (Set.inter_subset_right)
          exact monotonicity (Set.inter_subset_right.trans hS₀_subsetE) (Set.subset_inter (hS A (Set.mem_insert A S₀)).1 hB_subsetS₀)
        rw [this] at h; simp only [add_le_add_iff_right] at h
        exact Nat.sub_eq_zero_of_le h
    have := h_induc (ENat.toNat S.encard) S B hS (eq_comm.mp (ENat.coe_toNat_eq_self.mpr (Set.encard_ne_top_iff.mpr hS_finite)))
    exact @congrArg ℕ ℕ∞ (r (⋃₀ S) - r B) 0 Nat.cast this

  Indep := fun X ↦ X ⊆ E ∧ r X = X.encard
  indep_maximal := by
    intro X hX I hI hI'; dsimp only
    set S := {Y | (Y ⊆ E ∧ ↑(r Y) = Y.encard) ∧ I ⊆ Y ∧ Y ⊆ X}
    have : S ⊆ 𝒫 X := fun Y hY ↦ hY.2.2
    have : S.Finite := by
      exact Set.Finite.subset (Set.Finite.finite_subsets (Set.Finite.subset hE hX)) this
    unfold maximals Set.Nonempty
    have hS_nonempty : S.Nonempty := by
      unfold Set.Nonempty; use I
      exact ⟨⟨hI'.trans hX, hI.2⟩, subset_refl I, hI'⟩
    rcases Set.Finite.exists_maximal_wrt (fun A ↦ A) S this hS_nonempty with ⟨M, hMS, hM_max⟩
    use M; dsimp only [Set.sep_setOf, Set.mem_setOf_eq]
    refine ⟨hMS, ?_⟩
    intro M' hM'S hM'
    rw [hM_max M' hM'S hM']
  indep_iff' := by
    simp only [gt_iff_lt, tsub_pos_iff_lt, Nat.cast_lt]
    refine fun I ↦ ⟨fun ⟨hI_subset, hIr⟩ ↦ ⟨hI_subset, ?_⟩, fun ⟨hI_subset, hI⟩ ↦ ⟨hI_subset, ?_⟩⟩
    · intro x hx
      have hIr := encard_to_ncard (Eq.symm hIr)
      have hI_finite : I.Finite := by exact Set.Finite.subset hE hI_subset
      have : r (I \ {x}) ≤ r I - 1 := by
        rw [<-hIr, <-Set.ncard_diff_singleton_of_mem hx hI_finite]
        have := rank_le_encard (I \ {x})
        rw [<-Set.Finite.cast_ncard_eq (Set.Finite.subset hI_finite Set.diff_subset)] at this
        exact WithTop.coe_le_coe.mp this
      have hrI : r I > 0 := by
        rw [<-hIr]; exact Nat.zero_lt_of_ne_zero (Set.ncard_ne_zero_of_mem hx hI_finite)
      exact (Nat.lt_iff_le_pred hrI).mpr this
    sorry
end RankMatroid
