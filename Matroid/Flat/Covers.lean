import Matroid.Minor.Rank
import Matroid.Uniform
import Matroid.Simple
import Matroid.Minor.Iso
import Mathlib.Tactic.Linarith
import Matroid.Flat.LowRank
import Matroid.ForMathlib.Topology.ENat

set_option linter.style.longLine false

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {k : ℕ∞} {T : Set (Set α)}

open Set
namespace Matroid

@[mk_iff]
structure IsCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α)) : Prop where
  sUnion_eq : ⋃₀ T = M.E
  eRk_le : ∀ F ∈ T, M.eRk F ≤ k

lemma IsCover.subset_ground (h : M.IsCover k T) (hX : X ∈ T) : X ⊆ M.E := by
  grw [← h.sUnion_eq, ← subset_sUnion_of_mem hX]

lemma IsCover.isCover_closure (h : M.IsCover k T) : M.IsCover k (M.closure '' T) := by
  simp only [isCover_iff, sUnion_image, subset_antisymm_iff (b := M.E), iUnion_subset_iff,
    M.closure_subset_ground, implies_true, true_and, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, eRk_closure_eq]
  grw [h.sUnion_eq.symm.subset, sUnion_eq_biUnion]
  exact ⟨biUnion_mono rfl.subset fun X hX ↦ M.subset_closure X (h.subset_ground hX), h.2⟩

lemma IsCover.mono {k'} (h : M.IsCover k T) (hkk' : k ≤ k') : M.IsCover k' T :=
  ⟨h.1, fun F hF ↦ (h.2 F hF).trans hkk'⟩

lemma ground_isCover (M : Matroid α) : M.IsCover M.eRank {M.E} := by
  simp [isCover_iff]

lemma setOf_point_isCover (M : Matroid α) [M.RankPos] : M.IsCover 1 {P | M.IsPoint P} := by
  refine ⟨subset_antisymm (sUnion_subset fun _ ↦ IsPoint.subset_ground) fun e he ↦ ?_,
    by simp +contextual [mem_setOf_eq] ⟩
  simp only [mem_sUnion, mem_setOf_eq]
  obtain hl | hnl := M.isLoop_or_isNonloop e
  · obtain ⟨f, hf⟩ := M.exists_isNonloop
    exact ⟨_, hf.closure_isPoint, hl.mem_closure _⟩
  exact ⟨_, hnl.closure_isPoint, mem_closure_of_mem _ (by simp) (by simpa)⟩

lemma setOf_point_isCover' [hM : M.Loopless] : M.IsCover 1 {P | M.IsPoint P} := by
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · obtain rfl : E = ∅ := by simpa using hM
    constructor <;> simp
  exact M.setOf_point_isCover

lemma IsCover.nonempty [M.Nonempty] (h : M.IsCover k T) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [isCover_iff, eq_comm, M.ground_nonempty.ne_empty] at h

/-- The number of sets of rank at most `k` needed to cover a matroid `M`. -/
noncomputable def coverNumber (M : Matroid α) (k : ℕ∞) : ℕ∞ := sInf (encard '' {T | M.IsCover k T})

lemma IsCover.coverNumber_le (h : M.IsCover k T) : M.coverNumber k ≤ T.encard :=
  sInf_le <| by grind

@[simp]
lemma coverNumber_emptyOn (α : Type*) (k : ℕ∞) : (emptyOn α).coverNumber k = 0 := by
  simp [coverNumber, ENat.sInf_eq_zero, isCover_iff]

lemma coverNumber_pos (M : Matroid α) [M.Nonempty] (k : ℕ∞) : 0 < M.coverNumber k := by
  suffices ¬ M.IsCover k ∅ by simpa [pos_iff_ne_zero, coverNumber, ENat.sInf_eq_zero]
  exact fun h ↦ M.ground_nonempty.ne_empty <| by simpa using h.sUnion_eq.symm

@[simp]
lemma coverNumber_top (M : Matroid α) [M.Nonempty] : M.coverNumber ⊤ = 1 := by
  nth_grw 1 [le_antisymm_iff, ENat.one_le_iff_ne_zero,
    (M.ground_isCover.mono (by simp)).coverNumber_le, encard_singleton, and_iff_right rfl.le]
  exact (M.coverNumber_pos _).ne.symm

-- lemma foo (M : Matroid α) (C : Set α)



-- def coverNumber (M : Matroid α) (k : ℕ∞) : ℕ∞ :=
--   sInf {}

  -- refine ⟨subset_antisymm (sUnion_subset fun X hX ↦ ?_) ?_, ?_⟩
  -- ·

-- /-- A cover of the elements of `M` with sets of rank at most `k`. -/
-- structure Cover (M : Matroid α) (k : ℕ∞) where
--   toSet : Set (Set α)
--   sUnion_eq' : ⋃₀ toSet = M.E
--   eRk_le' : ∀ F ∈ toSet, M.eRk F ≤ k

-- -- `M.Cover k` behaves like a `Set` of `Set α`.
-- instance {k} : SetLike (M.Cover k) (Set α) where
--   coe := Cover.toSet
--   coe_injective' C C' _ := by cases C; cases C'; simpa

-- variable {T : M.Cover k}

-- @[simp]
-- lemma Cover.sUnion_eq (T : M.Cover k) : ⋃₀ T = M.E := T.sUnion_eq'
-- lemma Cover.eRk_le {T : M.Cover k} (h : F ∈ T) : M.eRk F ≤ k := T.eRk_le' F h
-- @[simp]
-- lemma Cover.toSet_eq_coe (T : M.Cover k) : T.toSet = T := rfl

-- lemma Cover.subset_ground_of_mem (hFC : F ∈ T) : F ⊆ M.E := by
--   grw [← T.sUnion_eq]
--   exact subset_sUnion_of_mem hFC

-- def Cover.closures (T : M.Cover k) : M.Cover k where
--   toSet := M.closure '' T
--   sUnion_eq' := by
--     refine subset
--   eRk_le' := _

@[simp]
lemma loopyOn.rank : M = loopyOn M.E ↔ M.eRank = 0 := by
  refine ⟨ ?_, ?_ ⟩
  · --exact fun h ↦ rank_eq_zero_iff.mpr h
    intro h
    rw[h]
    exact eRank_loopyOn M.E
  intro h
  apply eq_loopyOn_iff.2
  refine ⟨rfl, ?_ ⟩
  intro X hX hXI
  have : M.eRk X = 0 := by
    have : M.eRk X ≤ 0 := by
      grw [←h, eRk_le_eRank M X]
    exact nonpos_iff_eq_zero.mp this
  have h0 : X.encard = 0 := by
    rw[←this]
    exact (Indep.eRk_eq_encard hXI).symm
  exact encard_eq_zero.mp h0


-- lemma IsNonloop.contraction_points (he : M.IsNonloop e ) :
--         M.simplification.E.encard = (∑ M.IsLine L ∧ e ∈ L, L.encard) + 1

theorem kung_bound [RankFinite M]
    (hNoUnif : ∀ N : Matroid α, N ≤m M → N = (unifOn (N.E ) 2 ) → N.E.encard < l + 2) :
    --(hNoUnif : ¬ Nonempty ((unifOn (Set.univ : Set (Fin (l + 2))) 2) ≤i M)) :
    {P : Set α | M.IsPoint P}.encard ≤ (l ^ (M.rank ) - 1)/(l - 1) := by
    --M.simplification.E.encard ≤ (l ^ (M.rank ) - 1)/(l - 1) := by
  suffices hn : ∀ n : ℕ, M.rank = n → {P : Set α | M.IsPoint P}.encard ≤ (l ^ n - 1)/(l - 1)
  · exact hn M.rank rfl
  intro n hn
  induction n generalizing M with
  | zero =>
  -- We need a Thm that says that M has a non-loop element iff r(M)>0.
  -- Apparently the matroid of all loops is the called loopyOn. So I added the Lemma
  sorry
  | succ n ih =>
    have ⟨ e, he ⟩ : ∃ e, ¬ M.IsLoop e := by
      -- use loopyOn_isLoop_iff
      sorry
-- eq_unifOn_of_eRank_le_two will be useful
    --have hsum : {P : Set α | M.IsPoint P}.encard = (∑ L ∈ {L : Set α | M.IsLine L ∧ e ∈ L}, (L.encard)) + 1 := by sorry

    sorry


def IsUniform_minor_free (M : Matroid α) ( a b : ℕ ) :=
    ∀ N : Matroid α, N ≤m M → N = (unifOn (N.E ) (a + 1) ) → N.E.encard < b

def kung_infinite (hM : M.NoUniformMinor 2 (l + 2)) :
    M.simplification.E.encard ≤ ∑' i : {i : ℕ // i < M.eRank}, l ^ i.1 := by
  sorry
