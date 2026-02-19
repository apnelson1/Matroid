import Matroid.Minor.Rank
import Matroid.Uniform
import Matroid.Simple
import Matroid.Minor.Iso
import Mathlib.Tactic.Linarith
import Matroid.Flat.LowRank
import Matroid.ForMathlib.Topology.ENat

set_option linter.style.longLine false

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}

open Set
namespace Matroid

section Indexed

variable {T : ι → Set α}

@[mk_iff]
structure IsIndexedCover (M : Matroid α) (k : ℕ∞) (T : ι → Set α) : Prop where
  iUnion_eq : ⋃ i, T i = M.E
  eRk_le : ∀ i, M.eRk (T i) ≤ k

lemma IsIndexedCover.subset_ground (h : M.IsIndexedCover k T) (i : ι) : T i ⊆ M.E := by
  grw [← h.iUnion_eq, ← subset_iUnion]

lemma IsIndexedCover.isIndexedCover_closure (h : M.IsIndexedCover k T) :
    M.IsIndexedCover k (fun i ↦ M.closure (T i)) := by
  refine ⟨(iUnion_subset (fun i ↦ M.closure_subset_ground ..)).antisymm ?_, fun i ↦ ?_⟩
  · grw [← h.iUnion_eq, iUnion_mono (fun i ↦ M.subset_closure (T i) (h.subset_ground i))]
  simpa using h.eRk_le i

lemma setOf_point_isIndexedCover (M : Matroid α) [M.RankPos] :
    M.IsIndexedCover 1 (fun x : {P // M.IsPoint P} ↦ x.1) := by
  refine ⟨(iUnion_subset fun P ↦ P.2.subset_ground).antisymm fun e he ↦ ?_, ?_⟩
  · obtain hl | hnl := M.isLoop_or_isNonloop e
    · obtain ⟨f, hf⟩ := M.exists_isNonloop
      exact mem_iUnion_of_mem (i := ⟨M.closure {f}, hf.closure_isPoint⟩) <| hl.mem_closure {f}
    exact mem_iUnion_of_mem (i := ⟨M.closure {e}, hnl.closure_isPoint⟩) <| M.mem_closure_self e
  simp +contextual [IsPoint.eRk]

lemma IsIndexedCover.cover_cover {η : ι → Type*} (h : M.IsIndexedCover k T)
    (T₀ : (i : ι) → (η i) → Set α) (hT₀ : ∀ i, (M ↾ (T i)).IsIndexedCover a (T₀ i)) :
    M.IsIndexedCover a (fun i : ((i : ι) × η i) ↦ T₀ i.1 i.2) := by
  refine ⟨?_, ?_⟩
  · rw [← h.iUnion_eq, iUnion_sigma]
    refine iUnion_congr fun i ↦ ?_
    rw [(hT₀ i).iUnion_eq, restrict_ground_eq]
  rintro ⟨i, j⟩
  have := (hT₀ i).eRk_le j
  rwa [restrict_eRk_eq', inter_eq_self_of_subset_left] at this
  grw [(hT₀ i).subset_ground, restrict_ground_eq]


-- noncomputable def coverNumber' (M : Matroid α) (k : ℕ∞) :=
--     ⨅ (T : Set (Set α)) (_ : M.IsIndexedCover k (fun x : T ↦ x)), T.encard

-- lemma IsIndexedCover.coverNumber'_le {T : Set (Set α)} (hT : M.IsIndexedCover k (fun x : T ↦ x)) :


-- lemma IsIndexedCover.coverNumber'_le (h : M.IsIndexedCover k T) : M.coverNumber' k ≤ ENat.card ι := by
--   grw [coverNumber', iInf₂_le _ (i := range T)]
--   · grw [← image_univ, encard_image_le, encard_le_card]





end Indexed

def IsCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α)) : Prop := M.IsIndexedCover k (fun X : T ↦ X.1)

lemma IsCover.isIndexedCover (h : M.IsCover k T) : M.IsIndexedCover k (fun X : T ↦ X.1) := h

lemma IsCover.sUnion_eq (h : M.IsCover k T) : ⋃₀ T = M.E := by
  rw [← IsIndexedCover.iUnion_eq h, sUnion_eq_iUnion]

lemma IsCover.eRk_le (h : M.IsCover k T) (hXT : X ∈ T) : M.eRk X ≤ k :=
  IsIndexedCover.eRk_le h ⟨X, hXT⟩

lemma isCover_iff : M.IsCover k T ↔ ⋃₀ T = M.E ∧ ∀ F ∈ T, M.eRk F ≤ k :=
  ⟨fun h ↦ ⟨h.sUnion_eq, fun _ ↦ h.eRk_le⟩,
    fun h ↦ ⟨by rw [← sUnion_eq_iUnion, h.1], by simpa using h.2⟩⟩



-- @[mk_iff]
-- structure IsCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α)) : Prop where
--   sUnion_eq : ⋃₀ T = M.E
--   eRk_le : ∀ F ∈ T, M.eRk F ≤ k

lemma IsCover.subset_ground (h : M.IsCover k T) (hX : X ∈ T) : X ⊆ M.E := by
  grw [← h.sUnion_eq, ← subset_sUnion_of_mem hX]

lemma IsCover.isCover_closure (h : M.IsCover k T) : M.IsCover k (M.closure '' T) := by
  simp only [isCover_iff, sUnion_image, subset_antisymm_iff (b := M.E), iUnion_subset_iff,
    M.closure_subset_ground, implies_true, true_and, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, eRk_closure_eq]
  grw [h.sUnion_eq.symm.subset, sUnion_eq_biUnion]
  exact ⟨biUnion_mono rfl.subset fun X hX ↦ M.subset_closure X (h.subset_ground hX),
    fun _ ↦ h.eRk_le⟩

lemma IsCover.mono {k'} (h : M.IsCover k T) (hkk' : k ≤ k') : M.IsCover k' T :=
  isCover_iff.2 ⟨h.sUnion_eq, fun _ hF ↦ (h.eRk_le hF).trans hkk'⟩

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

-- almost follows from `setOf_point_isCover` - handle the rank-zero case.
lemma setOf_cover_nonempty (M : Matroid α) (hk : 1 ≤ k) : {T | M.IsCover k T}.Nonempty := by
  obtain ⟨E, rfl⟩ | rp := M.exists_eq_loopyOn_or_rankPos
  · sorry
  exact ⟨_, M.setOf_point_isCover.mono hk⟩

--Do we want ⋃₀ T = M.E or M.E ⊆ ⋃₀ T?
lemma IsCover.contract (h : (M ／ X).IsCover k T) (hX : X ⊆ M.E) (hXN : (M ／ X).Nonempty) :
    M.IsCover (k + M.eRk X) ((· ∪ X) '' T) := by
  suffices ∀ F ∈ T, M.eRk (F ∪ X) ≤ k + M.eRk X by
    simpa [isCover_iff, ← biUnion_distrib_union _ h.nonempty, ← sUnion_eq_biUnion, h.sUnion_eq, hX]
  exact fun F hFT ↦ by grw [← h.eRk_le F hFT, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq]

/-- The number of sets of rank at most `k` needed to cover a matroid `M`. -/
noncomputable def coverNumber (M : Matroid α) (k : ℕ∞) : ℕ∞ := sInf (encard '' {T | M.IsCover k T})

lemma coverNumber_eq_iInf (M : Matroid α) (k : ℕ∞) :
    M.coverNumber k = ⨅ T ∈ {T | M.IsCover k T}, T.encard := by
  exact sInf_image

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

lemma exists_cover (M : Matroid α) {k : ℕ∞} (hk : 1 ≤ k) :
    ∃ T, M.IsCover k T ∧ T.encard = M.coverNumber k := by
  simpa using csInf_mem <| (M.setOf_cover_nonempty hk).image encard



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
