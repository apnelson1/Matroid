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
    by simp +contextual [mem_setOf_eq, IsPoint] ⟩
  simp only [mem_sUnion, mem_setOf_eq]
  obtain hl | hnl := M.isLoop_or_isNonloop e
  · obtain ⟨f, hf⟩ := M.exists_isNonloop
    exact ⟨_, hf.closure_isPoint, hl.mem_closure _⟩
  exact ⟨_, hnl.closure_isPoint, mem_closure_of_mem _ (by simp) (by simpa)⟩

lemma setOf_point_isCover' [hM : M.Loopless] : M.IsCover 1 {P | M.IsPoint P} := by
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · obtain rfl : E = ∅ := by simpa using hM
    constructor <;> simp [IsPoint]
  exact M.setOf_point_isCover

lemma IsCover.nonempty [M.Nonempty] (h : M.IsCover k T) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [isCover_iff, eq_comm, M.ground_nonempty.ne_empty] at h


--Do we want ⋃₀ T = M.E or M.E ⊆ ⋃₀ T?
lemma IsCover.contract (h : (M／X).IsCover k T) (hX : X ⊆ M.E) (hXN : (M／ X).Nonempty) :
    M.IsCover (k + M.eRk X) ((· ∪ X) '' T) := by
  refine ⟨?_, ?_⟩
  · have := contract_ground M X
    have hrw : ⋃₀ ((fun x ↦ x ∪ X) '' T) = ⋃₀ T ∪ X := by
      simp only [sUnion_image]
      rw[sUnion_distrib_union h.nonempty ]
    rw[hrw]
    have hrw2 : M.E = (M ／ X).E ∪ X := by
      --diff_union_self
      simp only [contract_ground, diff_union_self]
      exact Eq.symm (union_eq_self_of_subset_right hX)
    rw[hrw2]
    apply union_eq_union_iff_right.2
    refine ⟨?_, ?_ ⟩
    · refine subset_union_of_subset_left ?_ X
      rw[h.sUnion_eq]
    rw[h.sUnion_eq]
    exact subset_union_left
  intro F hF
  simp only [mem_image] at hF
  obtain ⟨F', hF', hF'2⟩ := hF
  have h1 := h.eRk_le F' hF'
  rw[←eRelRk_eq_eRk_contract] at h1
  rw[←hF'2, ←M.eRelRk_add_eRk_eq  ]
  exact add_le_add_left h1 (M.eRk X)

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

lemma coverNumber_le {k k' : ℕ∞} (M : Matroid α) (hk : k ≤ k') : M.coverNumber k' ≤ M.coverNumber k
    := by
  refine ENat.forall_natCast_le_iff_le.mp ?_
  intro a hak
  unfold coverNumber at hak
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hak
  unfold coverNumber
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact fun T hT ↦ (hak T (hT.mono hk)  )

lemma coverNumber_contract_one {a : ℕ∞} (he : e ∈ M.E) (hel : M.IsNonloop e)
    (heN : (M／ {e}).Nonempty) :
    M.coverNumber (a + 1) ≤ (M ／ {e}).coverNumber a := by
  refine ENat.forall_natCast_le_iff_le.mp ?_
  intro b hb
  unfold coverNumber at hb
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hb
  unfold coverNumber
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro T hT
  have h1 := hT.contract (singleton_subset_iff.mpr he ) heN
  rw[IsNonloop.eRk_eq hel ] at h1
  have h2 := hb ((· ∪ {e}) '' T) h1
  grw[encard_image_le (fun x ↦ x ∪ {e}) T ] at h2
  exact h2

lemma coverNumber_contract {a : ℕ∞} (hX : X ⊆ M.E) :
    M.coverNumber (a + M.eRk X) ≤ (M ／ X).coverNumber a := by
  --Mathieu, do you want to do this one?
  sorry

-- lemma foo (M : Matroid α) [RankPos M] : M.coverNumber 1 = M.simplification.E.encard := by

--   rw [M.simplification_isSimplification.encard_ground_eq, le_antisymm_iff]
--   refine ⟨M.setOf_point_isCover.coverNumber_le, ?_⟩
--   rw [coverNumber, le_sInf_iff]
--   simp


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


-- lemma IsNonloop.contraction_points (he : M.IsNonloop e ) :
--         M.simplification.E.encard = (∑ M.IsLine L ∧ e ∈ L, L.encard) + 1

theorem kung_bound [RankFinite M]
    (hNoUnif : NoUniformMinor M (l + 2) 2) :
    --(hNoUnif : ∀ N : Matroid α, N ≤m M → N = (unifOn (N.E ) 2 ) → N.E.encard < l + 2) :
    --(hNoUnif : ¬ Nonempty ((unifOn (Set.univ : Set (Fin (l + 2))) 2) ≤i M)) :
    coverNumber M 1 ≤ ∑' i : {i : ℕ // i < M.eRank}, l^i.1  := by
    --M.simplification.E.encard ≤ (l ^ (M.rank ) - 1)/(l - 1) := by
  suffices hn : ∀ n : ℕ, M.rank = n → coverNumber M 1 ≤  ∑' i : {i : ℕ // i < n}, l^i.1
  ·
    sorry
  intro n hn
  sorry
  -- I think we just need to use coverNumber_contract_one






--   · exact hn M.rank rfl
--   intro n hn
--   induction n generalizing M with
--   | zero =>
--   -- We need a Thm that says that M has a non-loop element iff r(M)>0.
--   -- Apparently the matroid of all loops is the called loopyOn. So I added the Lemma
--   sorry
--   | succ n ih =>
--     have ⟨ e, he ⟩ : ∃ e, ¬ M.IsLoop e := by
--       -- use loopyOn_isLoop_iff
--       sorry
-- -- eq_unifOn_of_eRank_le_two will be useful
--     --have hsum : {P : Set α | M.IsPoint P}.encard = (∑ L ∈ {L : Set α | M.IsLine L ∧ e ∈ L}, (L.encard)) + 1 := by sorry



-- def IsUniform_minor_free (M : Matroid α) ( a b : ℕ ) :=
--     ∀ N : Matroid α, N ≤m M → N = (unifOn (N.E ) (a + 1) ) → N.E.encard < b

def kung_infinite (hM : M.NoUniformMinor 2 (l + 2)) :
    M.simplification.E.encard ≤ ∑' i : {i : ℕ // i < M.eRank}, l ^ i.1 := by
  sorry
