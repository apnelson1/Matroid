import Matroid.Minor.Rank
import Matroid.Uniform.Basic
import Matroid.Simple
import Matroid.Minor.Iso
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Powerset
import Matroid.Flat.LowRank
import Matroid.ForMathlib.Topology.ENat
import Matroid.ForMathlib.Minimal
import Mathlib.Data.Set.Card.Arithmetic

set_option linter.style.longLine false

variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' : Matroid α → Set α → Prop}

open Set

/-- `T.IsCover X P` means that `T` is a collection of sets with union `X`,
each satisfying property `P`.-/
@[mk_iff]
structure Set.IsCover (T : Set (Set α)) (X : Set α) (P : Set α → Prop) : Prop where
  sUnion_eq : ⋃₀ T = X
  pProp : ∀ F ∈ T, P F

noncomputable def Set.coverNumber (X : Set α) (P : Set α → Prop) : ℕ∞ :=
  ⨅ (T : Set (Set α)) (_ : T.IsCover X P), T.encard

lemma coverNumber_mono (X : Set α) {P Q : Set α → Prop} (hPQ : ∀ Y ⊆ X, P Y → Q Y) :
    X.coverNumber Q ≤ X.coverNumber P := by
  simp only [coverNumber, le_iInf_iff]
  refine fun T hT ↦ iInf₂_le T ⟨hT.1, fun F hF ↦ hPQ _ ?_ (hT.2 F hF)⟩




namespace Matroid

def IsRankCover (M : Matroid α) (T : Set (Set α)) (X : Set α) (k : ℕ∞) :=
    T.IsCover X (fun A ↦ M.eRk A ≤ k)



section General




@[mk_iff]
structure IsCover (M : Matroid α) (P : Matroid α → Set α → Prop) (T : Set (Set α)) : Prop where
  sUnion_eq : ⋃₀ T = M.E
  pProp : ∀ F ∈ T, P M F

lemma IsCover.subset_ground (h : M.IsCover P T) (hX : X ∈ T) : X ⊆ M.E := by
  grw [← h.sUnion_eq, ← subset_sUnion_of_mem hX]

-- monotone
-- PCover iff ∀ e, ∃ X ∈ T, e ∈ X

--Monotone under restriction
def IsMRProp (P : Matroid α → Set α → Prop) : Prop :=
    ∀ M : Matroid α, ∀ F : Set α, ∀ Y : Set α, Y ⊆ F → P (M ↾ F) Y → P M Y

--Monotone under subset
def IsMSProp (P : Matroid α → Set α → Prop) : Prop :=
    ∀ M : Matroid α, ∀ F : Set α, ∀ Y : Set α, Y ⊆ F → P M F → P M Y

-- --Minor union different prop. I think I want something different
-- def IsMUProp (P : Matroid α → Set α → Prop) (P' : Matroid α → Set α → Prop) : Prop :=
--     ∀ M : Matroid α, ∀ X : Set α, ∀ Y : Set α, P (M ／ X) Y → P' M (Y ∪ X)

--Minor monotono
def IsMMProp (P : Matroid α → Set α → Prop) (P' : Matroid α → Set α → Prop) : Prop :=
    --∀ M : Matroid α, ∀ X : Set α, ∀ Y : Set α, P (M ／ X) Y → P' M (Y ∪ X)
    ∀ N, N ≤m M → ∀ Y, Y ⊆ N.E → P N Y → P' M Y

-- M has a cover with respect to prop P
def hasCover_with (M : Matroid α) (P : Matroid α → Set α → Prop) : Prop :=
    ∃ T, M.IsCover P T

lemma Cover_Nonempt_iff :
    M.hasCover_with P ↔ {T | M.IsCover P T}.Nonempty := by
  refine ⟨ fun a ↦ Nonempty.mono (fun ⦃a⦄ a_1 ↦ a_1) a , fun a ↦ ((fun a_1 ↦ a) ∘ fun a ↦ α) α ⟩

lemma IsCover.nonempty [M.Nonempty] (h : M.IsCover P T) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [isCover_iff, eq_comm, M.ground_nonempty.ne_empty] at h

lemma IsCover.one_le [M.Nonempty] (h : M.IsCover P T) : 1 ≤ T.encard := by
  simp only [one_le_encard_iff_nonempty]
  exact nonempty h

noncomputable def coverNumber (M : Matroid α) (P : Matroid α → Set α → Prop) : ℕ∞ :=
    sInf (encard '' {T | M.IsCover P T})

lemma coverNumber_eq_iInf (M : Matroid α) (P : Matroid α → Set α → Prop) :
    M.coverNumber P = ⨅ T ∈ {T | M.IsCover P T}, T.encard := by
  exact sInf_image

lemma IsCover.coverNumber_le {T} (h : M.IsCover P T) : M.coverNumber P ≤ T.encard := by
  grw [coverNumber_eq_iInf]
  exact biInf_le encard h

lemma exists_mincover_NE {M : Matroid α} {P : Matroid α → Set α → Prop}
    (hn : {T | M.IsCover P T}.Nonempty) :
    ∃ T, M.IsCover P T ∧ T.encard = M.coverNumber P := by
  simpa using csInf_mem <| hn.image encard

lemma exists_min_cover {M : Matroid α} {P : Matroid α → Set α → Prop} (hP : M.hasCover_with P) :
    ∃ T, M.IsCover P T ∧ T.encard = M.coverNumber P := by
  simpa using csInf_mem <| (Cover_Nonempt_iff.1 hP ).image encard

lemma exists_cover (M : Matroid α) (P : Matroid α → Set α → Prop) :
    M.coverNumber P = ⊤ ∨ ∃ T, M.IsCover P T ∧ T.encard = M.coverNumber P := by
  obtain h0 | h := {T | M.IsCover P T}.eq_empty_or_nonempty
  · simp [coverNumber_eq_iInf, h0]
  right
  simpa using csInf_mem <| h.image encard

lemma coverNumer_positive [M.Nonempty] (P : Matroid α → Set α → Prop) :
    1 ≤ M.coverNumber P := by
  by_contra hc
  have h1 := ENat.lt_one_iff_eq_zero.mp (Std.not_le.mp hc)
  obtain ht | ⟨T, hT, hTe ⟩ := exists_cover M P
  · rw [h1] at ht
    simp only [ENat.zero_ne_top] at ht
  have := hT.nonempty
  grind

lemma IsCover.cover_fun {M : Matroid α} {P' : Matroid α → Set α → Prop} (hP' : IsMRProp P')
    (hcover : M.IsCover P T)
    (f : Set α → Set (Set α) )
    (hfun : ∀ X ∈ T, (M ↾ X).IsCover P' (f X)) :
    M.IsCover P' ( ⋃ X ∈ T, f X ):= by
  refine ⟨ ?_, ?_ ⟩
  · rw[←hcover.sUnion_eq]
    refine ext ?_
    intro e
    refine ⟨ ?_, ?_ ⟩
    · intro he
      simp only [ mem_sUnion, mem_iUnion] at he
      obtain ⟨T', ⟨ X, ⟨hX, hT'X ⟩ ⟩, hee ⟩ := he
      simp only [mem_sUnion]
      refine ⟨ X ,⟨ hX , mem_of_subset_of_mem ((hfun X hX).subset_ground hT'X ) hee  ⟩ ⟩
    intro he
    simp only [mem_sUnion] at he
    obtain ⟨X, hXT, heX⟩ := he
    simp only [mem_sUnion, mem_iUnion]
    have h1 : e ∈ (M ↾ ↑X).E := by exact mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) heX
    rw[←(hfun X hXT ).sUnion_eq] at h1
    simp only [mem_sUnion] at h1
    obtain ⟨X', hX', heX' ⟩ := h1
    refine ⟨ X', ⟨⟨X, ⟨hXT, hX'⟩ ⟩, heX'⟩ ⟩
  intro F hF
  simp only [ mem_iUnion] at hF
  obtain ⟨X, hXT, hF⟩ := hF
  exact hP' M X F (LE.le.subset ((hfun X hXT).subset_ground hF ) ) ((hfun X hXT).pProp F hF)


lemma IsCover.cover_typset {P' : Matroid α → Set α → Prop} (hP' : IsMRProp P' )
    (hcover : M.IsCover P T )
    (f : T → Set (Set α) )
    (hfun : ∀ X : T, (M ↾ X.1).IsCover P' (f X)) :
    M.IsCover P' (⋃ X : T, f X ):= by
  refine ⟨ ?_, ?_ ⟩
  · rw[←hcover.sUnion_eq]
    refine ext ?_
    intro e
    refine ⟨ ?_, ?_ ⟩
    · intro he
      simp only [iUnion_coe_set, mem_sUnion, mem_iUnion] at he
      obtain ⟨T', ⟨ X, ⟨hX, hT'X ⟩ ⟩, hee ⟩ := he
      simp only [mem_sUnion]
      refine ⟨X, ⟨hX, (mem_of_subset_of_mem (((hfun ⟨X, hX⟩ ).subset_ground hT'X)) hee ) ⟩⟩
    intro he
    simp only [mem_sUnion] at he
    obtain ⟨X, hXT, heX⟩ := he
    simp only [iUnion_coe_set, mem_sUnion, mem_iUnion]
    have h1 : e ∈ (M ↾ ↑X).E := by exact mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) heX
    rw[←(hfun ⟨X, hXT⟩ ).sUnion_eq] at h1
    simp only [mem_sUnion] at h1
    obtain ⟨X', hX', heX' ⟩ := h1
    refine ⟨ X', ⟨⟨X, ⟨hXT, hX'⟩ ⟩, heX'⟩ ⟩
  intro F hF
  simp only [iUnion_coe_set, mem_iUnion] at hF
  obtain ⟨X, hXT, hF⟩ := hF
  exact hP' M X F (LE.le.subset ((hfun ⟨X, hXT⟩).subset_ground hF ) ) ((hfun ⟨X, hXT⟩).pProp F hF)

lemma coverNumber_cover_of_covers {P' : Matroid α → Set α → Prop} (hcover : M.IsCover P T)
    (hP' : IsMRProp P') :
    M.coverNumber P' ≤ ∑' X : T, (M ↾ X.1).coverNumber P' := by
  obtain (h0 | h1) := exists_or_forall_not (fun X : T ↦ (M ↾ X).coverNumber P' = ⊤)
  · simp [ENat.tsum_eq_top_of_eq_top h0]
  have hf : ∀ X : T, ∃ XT, (M ↾ X.1).IsCover P' XT ∧
    XT.encard = (M ↾ X.1).coverNumber P' := by
    intro X
    obtain (h | ⟨XT, hXres, hencard⟩) := (M ↾ X).exists_cover P'
    · simp [h1 _ h]
    exact ⟨XT, hXres, hencard⟩
  choose f hfunco hfunca using hf
  have hcover := IsCover.cover_typset hP' hcover f hfunco
  grw [hcover.coverNumber_le, ENat.encard_iUnion_le_tsum_encard, tsum_congr hfunca]

lemma coverNumber_cover_of_covers_bound {P' : Matroid α → Set α → Prop} {k : ℕ∞}
    (hcover : M.IsCover P T) (hP' : IsMRProp P')
    (hflat : ∀ F, P M F → (M ↾ F).coverNumber P' ≤ k) :
    M.coverNumber P' ≤ (T.encard) * k := by
  grw [coverNumber_cover_of_covers hcover, ENat.tsum_le_tsum (g := fun _ ↦ k),
    ENat.tsum_subtype_const, mul_comm]
  intro F
  simp [hflat _ <| hcover.pProp F F.2 ]
  exact hP'


--P is minor preserved wrt f if
def MRProp (α) (P : Matroid α → Set α → Prop) (f : Set α → Matroid α → Set α → Prop ) : Prop :=
    ∀ M : Matroid α, ∀ Y X : Set α,
    ∃ (Q : Matroid α → Set α → Prop) , (P (M ／ Y) X → Q M X ∧ Q M X = f Y M X)

--Help
lemma RankIsMRProp (α) {k : ℕ∞} : MRProp (α)
    (fun M X ↦ M.eRk X ≤ k) (fun Y M X ↦ M.eRk (X ∪ Y) ≤ M.eRk Y + k ) := by
  intro M Y X
  use (fun N Z ↦ M.eRk (X ∪ Y) ≤ M.eRk Y + k )
  simp only [and_true]

  sorry

-- --Minor preserved under f
-- --(f : Set α → Matroid α → (Set α → Prop))
-- def IsMUProp (P : Matroid α → Set α → Prop) (X : Set α ) (P' : Matroid α → Set α → Prop): Prop :=
--     --∀ X : Set α,
--     --∃ P' : Matroid α → Set α → Prop,
--     ∀ M : Matroid α,
--     ∀ Y : Set α, P (M ／ X) Y → P' M Y

--P ' = k + M.eRk X for rank
lemma IsCover.contract (h : (M ／ X).IsCover P T)
    (hX : X ⊆ M.E) (hXN : (M ／ X).Nonempty)
    (hPP' : ∀ Y : Set α, P (M ／ X) Y → P' M ( Y ∪ X) ) :
    M.IsCover P' ((· ∪ X) '' T) := by
  suffices hi : ∀ F ∈ T, P (M ／ X) F by
    simp only [isCover_iff, sUnion_image, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, ← biUnion_distrib_union _ h.nonempty, ← sUnion_eq_biUnion,
      h.sUnion_eq, contract_ground, diff_union_self, union_eq_left, hX, true_and ]
    exact fun F hFT ↦ (((fun a ↦ (hPP' F (hi F hFT))) ∘ T) X )
  exact fun F hFT ↦ h.pProp F hFT


--Close under closure
def IsCCProp (α) (P : Matroid α → Set α → Prop) : Prop :=
    ∀ M : Matroid α, ∀ F : Set α, P M F → P M (M.closure F)

lemma IsCover.isCover_closure (h : M.IsCover P T) (hP : IsCCProp α P) :
    M.IsCover P (M.closure '' T) := by
  simp only [isCover_iff, sUnion_image, subset_antisymm_iff (b := M.E), iUnion_subset_iff,
    M.closure_subset_ground, implies_true, true_and, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  grw [h.sUnion_eq.symm.subset, sUnion_eq_biUnion]
  refine  ⟨biUnion_mono rfl.subset fun X hX ↦ M.subset_closure X (h.subset_ground hX),
  fun F hF ↦ (hP M F (h.pProp F hF)) ⟩

--Singleton section
-- noncomputable def SetsingletonEmbedding ( A : Set α ) : Function.Embedding
--     {X : Set α // ∃ e ∈ A, {e} = X} {e // e ∈ A} :=
-- { toFun := fun x => ⟨Classical.choose x.2, (Classical.choose_spec x.2).1 ⟩
--   inj' := by
--     intro x y hxy
--     simp only [Subtype.mk.injEq] at hxy
--     have heq : x.1 = y.1 := by
--       rw [←(Classical.choose_spec x.2).2, ←(Classical.choose_spec y.2).2]
--       exact singleton_eq_singleton_iff.mpr hxy
--     exact Subtype.ext heq
--     }

lemma IsCover_singleton_Prop (hP : ∀ e ∈ M.E, P M (singleton e)) :
    M.IsCover P (singleton '' M.E) := by
  refine ⟨ ?_, ?_ ⟩
  · refine Eq.symm (ext ?_)
    intro x
    refine ⟨ ?_, ?_ ⟩
    · intro hx
      refine mem_sUnion.mpr ⟨{x} , ⟨ ?_ , mem_singleton x ⟩ ⟩
      use x
    intro hc
    simp only [sUnion_image, biUnion_of_singleton] at hc
    exact mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hc
  intro F hF
  obtain ⟨e, heE, heF ⟩ := hF
  rw[←heF]
  exact hP e heE


lemma IsCover_singleton_le (hP : ∀ e ∈ M.E, P M (singleton e)) :
    M.coverNumber P ≤ M.E.encard := by
  grw [(IsCover_singleton_Prop hP).coverNumber_le ]
  set Sing : Set (Set α ) := { singleton e | e ∈ M.E} with hs
  exact encard_image_le singleton M.E


lemma IsCover.mono_prop (h : M.IsCover P T) (hPP' : ∀ X ∈ T, P M X → P' M X) : M.IsCover P' T :=
  (M.isCover_iff P' T).2 ⟨h.sUnion_eq, fun F hF ↦ hPP' F hF (h.pProp F hF)⟩

lemma IsCover_emptyset_iff (P : Matroid α → Set α → Prop) : M.IsCover P ∅ ↔ ¬M.Nonempty := by
  refine ⟨?_, ?_ ⟩
  · intro h
    rw [ ←Matroid.ground_nonempty_iff, not_nonempty_iff_eq_empty, ←sUnion_empty, h.sUnion_eq.symm ]
  intro h
  rw [ ←Matroid.ground_nonempty_iff, not_nonempty_iff_eq_empty, ←sUnion_empty] at h
  refine ⟨h.symm, by grind ⟩

lemma coverNumber_zero_iff (P : Matroid α → Set α → Prop) : M.coverNumber P = 0 ↔ M.IsCover P ∅ := by
  refine ⟨?_, ?_ ⟩
  · intro h
    obtain ht | ⟨T, hT, hTe ⟩ := exists_cover M P
    · by_contra
      rw[ht] at h
      simp only [ENat.top_ne_zero] at h
    rw [h] at hTe
    rwa [← encard_eq_zero.mp hTe  ]
  intro h
  have := h.coverNumber_le
  simp only [encard_empty, nonpos_iff_eq_zero] at this
  grind

lemma coverNumber_le_coverNumber (P Q : Matroid α → Set α → Prop) (M : Matroid α)
    (hPQ : ∀ X ⊆ M.E, P M X → Q M X) : M.coverNumber Q ≤ M.coverNumber P := by
  sorry

lemma coverNumber_congr (P Q : Matroid α → Set α → Prop)
    (hPQ : ∀ (M : Matroid α) (X : Set α), X ⊆ M.E → (P M X ↔ Q M X)) (M : Matroid α) :
    M.coverNumber P = M.coverNumber Q := by
  sorry

lemma coverNumber_mono_prop (P : Matroid α → Set α → Prop) {M N : Matroid α} (hMN : M.E = N.E)
    (hMP : ∀ X ⊆ M.E, P N X → P M X) : M.coverNumber P ≤ N.coverNumber P := by

--   simp only [coverNumber, le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂]
--   refine fun C hC ↦ sInf_le ?_
--   simp only [mem_image, mem_setOf_eq]
--   refine ⟨C, ?_, rfl⟩
--   have := hC.mono_prop (P' := P)


end General

section Rank

-- lemma RankPropIsMUProp {k : ℕ∞} : IsMUProp (RankProp α k) (fun M X Y ↦ (M.eRk Y ≤ k + M.eRk X)) := by
--     --use fun M X Y ↦ (M.eRk Y ≤ k + M.eRk X)
--     intro M X Y hXY
--     unfold RankProp at hXY
--     sorry

def IsRankCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α )) : Prop :=
    M.IsCover (fun M X ↦ M.eRk X ≤ k) T

lemma IsRankCover_iff_IsCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α )) :
    M.IsRankCover k T ↔ M.IsCover (fun M X ↦ M.eRk X ≤ k) T := Iff.rfl

lemma IsRankCover_iff (M : Matroid α) (k : ℕ∞) (T : Set (Set α )) :
    M.IsRankCover k T ↔ ⋃₀ T = M.E ∧ (∀ F ∈ T, M.eRk F ≤ k) := by
  sorry
  --Mathieu

lemma IsRankCover_isCover_closure (hcov : M.IsRankCover k T) :
    M.IsRankCover k (M.closure '' T) := by
  apply hcov.isCover_closure (fun M F hF ↦ ?_)
  rwa [(eRk_closure_eq M F) ]

lemma IsRankCover.mono_k {k' : ℕ∞} (hcov : M.IsRankCover k T) (hkk' : k ≤ k') :
    M.IsRankCover k' T := by
  refine ⟨ hcov.sUnion_eq, fun F hF ↦
    Std.IsPreorder.le_trans (M.eRk F) k k' (hcov.pProp F hF ) hkk' ⟩

lemma IsRankCover_RankPos : M.hasCover_with (fun M X ↦ M.eRk X ≤ 0) ↔ ¬ M.RankPos := by
  refine ⟨ ?_, ?_ ⟩
  · intro h
    refine M.not_rankPos_iff.2 (Matroid.eq_loopyOn_iff_loops.mpr
      ⟨Eq.symm (Subset.antisymm ?_ (loops_subset_ground M )) , by simp only ⟩   )
    intro e he
    obtain ⟨ T, hT ⟩ := h
    rw[←hT.sUnion_eq ] at he
    obtain ⟨ X, hXt, heX ⟩ := he
    exact isLoop_iff.mp (((Matroid.eRk_eq_zero_iff (IsCover.subset_ground hT hXt  )).1
      (nonpos_iff_eq_zero.mp (hT.pProp X hXt ))) heX)
  intro h
  refine ⟨ (singleton '' M.E), IsCover_singleton_Prop ?_ ⟩
  intro e he
  simp only [nonpos_iff_eq_zero]
  refine IsLoop.eRk_eq ?_
  rw [M.not_rankPos_iff.1 h]
  exact loopyOn_isLoop_iff.mpr he

lemma IsRankCover_two [M.Nonempty] (hcov : M.IsRankCover k T) (hk : k < M.eRank ) :
    2 ≤ T.encard := by
  by_contra hc
  simp only [not_le] at hc
  have hle : T.encard ≤ 1 := Order.le_of_lt_succ hc
  have h1 := ((IsRankCover_iff_IsCover M k T).1 hcov).one_le
  have h1 : T.encard = 1 := by grind
  obtain ⟨X, hX ⟩ := Set.encard_eq_one.1 h1
  have h2 := ((IsRankCover_iff_IsCover M k T).1 hcov).sUnion_eq
  rw [hX] at h2
  simp only [sUnion_singleton] at h2
  have hXT : X ∈ T := by
    rw[ hX ]
    exact mem_singleton X
  have hf := ((IsRankCover_iff_IsCover M k T).1 hcov).pProp X hXT
  rw[ h2, ←eRank_def M  ] at hf
  grind


lemma setOf_point_IsRankCover (M : Matroid α) [M.RankPos] : M.IsRankCover 1 {P | M.IsPoint P} := by
  refine ⟨subset_antisymm (sUnion_subset fun _ ↦ IsPoint.subset_ground) fun e he ↦ ?_,
    by simp +contextual [mem_setOf_eq, IsPoint] ⟩
  simp only [mem_sUnion, mem_setOf_eq]
  obtain hl | hnl := M.isLoop_or_isNonloop e
  · obtain ⟨f, hf⟩ := M.exists_isNonloop
    exact ⟨_, hf.closure_isPoint, hl.mem_closure _⟩
  exact ⟨_, hnl.closure_isPoint, mem_closure_of_mem _ (by simp) (by simpa)⟩

lemma setOf_point_IsCover [hM : M.Loopless] : M.IsRankCover 1 {P | M.IsPoint P} := by
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · obtain rfl : E = ∅ := by simpa using hM
    constructor <;> simp [IsPoint]
  exact M.setOf_point_IsRankCover

lemma IsRankCover_ground (M : Matroid α) : M.IsRankCover M.eRank ({M.E}) := by
  refine ⟨ by simp, fun F a ↦ eRk_le_eRank M F ⟩

lemma IsRankCover.nonempty [M.Nonempty] (h : M.IsRankCover k T) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [IsRankCover_iff, eq_comm, M.ground_nonempty.ne_empty] at h

lemma RankPropCover_exists (hk : 1 ≤ k) : M.hasCover_with (fun M X ↦ M.eRk X ≤ k) := by
  by_cases hRP : M.RankPos
  · refine ⟨{P | M.IsPoint P}, (setOf_point_IsRankCover M ).mono_k hk ⟩
  obtain ⟨ T, hT ⟩ := IsRankCover_RankPos.2 hRP
  refine ⟨ T, ((IsRankCover_iff_IsCover M 0 T).2 hT).mono_k (ENat.zero_le ) ⟩

lemma IsCover.delete (hT : M.IsCover (fun M X ↦ M.eRk X ≤ k) T) (D : Set α) :
    (M ＼ D).IsCover (fun M X ↦ M.eRk X ≤ k) ((fun s ↦ s \ D) '' T) := by
  refine ⟨ ?_, ?_ ⟩
  · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
    · intro hK
      obtain ⟨ X, hX, h ⟩ := hK
      rw[ ← h]
      exact diff_subset_diff_left (hT.subset_ground hX )
    simp only [delete_ground, mem_diff] at he
    rw [←hT.sUnion_eq] at he
    obtain ⟨X, hX, hXe ⟩ := he.1
    have : e ∈ X \ D := mem_diff_of_mem hXe (he.2 )
    grind
  intro F hF
  obtain ⟨ F' ,hF' ,hF2 ⟩ := hF
  rw [←hF2]
  simp only [delete_eRk_eq', sdiff_idem]
  grw [eRk_subset_le M (diff_subset)]
  exact hT.pProp F' hF'

--Help
lemma coverNumber_eRank [M.Nonempty] : M.coverNumber (fun M' X ↦ M'.eRk X ≤ M.eRank) = 1 := by
  have h2 : 1 ≤ M.coverNumber (fun M' X ↦ M'.eRk X ≤ M.eRank ) :=
    M.coverNumer_positive (fun M' X ↦ M'.eRk X ≤ M.eRank )
  refine h2.antisymm' ?_
  simpa using (IsRankCover_ground M).coverNumber_le

lemma coverNumber_delete_loop (hne : (M ＼ D).Nonempty) (hk : 1 ≤ k) (hD : D ⊆ M.loops ) :
    M.coverNumber (fun M X ↦ M.eRk X ≤ k) = (M ＼ D).coverNumber (fun M X ↦ M.eRk X ≤ k) := by
  obtain ⟨T, hT, hTen ⟩ := exists_min_cover (RankPropCover_exists (M := M) hk )
  have h1 := (hT.delete D ).coverNumber_le
  grw[encard_image_le (fun s ↦ s \ D) T, hTen ] at h1
  -- have hkD : (M ＼ D).RankPos := by
  --   have hh : (M ＼ M.loops).RankPos := Delete_loops_RankPos
  --   rw [Matroid.rankPos_iff ] at hh
  --   simp only [delete_isBase_iff] at hh
  --   refine { empty_not_isBase := ?_ }
  --   by_contra hc
  --   exact Ne.elim (fun a ↦ hh ((((Matroid.IsBasis.isBasis_subset (isBasis_ground_iff.mpr hc )
  --   (empty_subset (M.E \ D) ) (IsLoopEquiv.subset_ground rfl fun ⦃a⦄ a_1 ↦ a_1) ) ).isBasis_subset
  --     (empty_subset (M.E \ M.loops) ) (diff_subset_diff_right hD ) ).of_delete)) hTen
  --have : (M ＼ D).Nonempty := rankPos_nonempty
  obtain ⟨T', hT', hT'en ⟩ := exists_min_cover (RankPropCover_exists (M := (M ＼ D)) hk )
  have hcov : M.IsCover (fun M X ↦ M.eRk X ≤ k) (M.closure '' T' ) := by
    refine ⟨ ?_, ?_ ⟩
    · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
      · simp only [mem_image, forall_exists_index, and_imp]
        grind
      by_cases heD : e ∈ D
      · obtain ⟨ X, hX ⟩ := hT'.nonempty
        have := (IsLoop.mem_closure (hD heD) X )
        grind
      have h2 : e ∈ M.E \ D := mem_diff_of_mem he heD
      rw[←delete_ground,  ←hT'.sUnion_eq  ] at h2
      obtain ⟨ X, hX, heX ⟩ := h2
      have := (mem_closure_of_mem' M heX he )
      grind
    intro F hF
    obtain ⟨F' ,hF', hF2 ⟩ := hF
    rw[←hF2, eRk_closure_eq M F']
    have ha := hT'.pProp F' hF'
    simp only [delete_eRk_eq'] at ha
    have ha1 : F' \ D = F' := by
      have := hT'.subset_ground hF'
      grind
    rwa [ha1] at ha
  have h2 := hcov.coverNumber_le
  grw [encard_image_le M.closure T', hT'en] at h2
  grind

lemma coverNumber_contract_loop (hne : (M ＼ D).Nonempty) (hk : 1 ≤ k) (hD : D ⊆ M.loops ) :
    M.coverNumber (fun M X ↦ M.eRk X ≤ k) = (M ／ D).coverNumber (fun M X ↦ M.eRk X ≤ k) := by
  rw[contract_eq_delete_of_subset_loops hD]
  exact coverNumber_delete_loop hne hk hD

lemma IsRankCover.contract (h : (M ／ X).IsRankCover k T) (hX : X ⊆ M.E)
    (hXN : (M ／ X).Nonempty) :
    M.IsRankCover (k + M.eRk X) ((· ∪ X) '' T) := by
  suffices ∀ F ∈ T, M.eRk (F ∪ X) ≤ k + M.eRk X by
    simpa [IsRankCover_iff, ← biUnion_distrib_union _ h.nonempty, ← sUnion_eq_biUnion, h.sUnion_eq, hX]
  exact fun F hFT ↦ by grw [← h.pProp F hFT, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq]

lemma coverNumber_contract_one {a : ℕ∞} (he : e ∈ M.E) (hel : M.IsNonloop e)
    (heN : (M／ {e}).Nonempty) :
    M.coverNumber (fun M X ↦ M.eRk X ≤ (a + 1)) ≤ (M ／ {e}).coverNumber (fun M X ↦ M.eRk X ≤ a)
    := by
  refine ENat.forall_natCast_le_iff_le.mp ?_
  intro b hb
  unfold coverNumber at hb
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hb
  unfold coverNumber
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro T hT
  rw[←IsRankCover_iff_IsCover] at hT
  have h1 := hT.contract (singleton_subset_iff.mpr he ) heN
  rw[IsNonloop.eRk_eq hel ] at h1
  have h2 := hb ((· ∪ {e}) '' T) h1
  grw[encard_image_le (fun x ↦ x ∪ {e}) T ] at h2
  exact h2

-- lemma exists_cover (M : Matroid α) {k : ℕ∞} (hk : 1 ≤ k) :
--     ∃ T, M.IsCover k T ∧ T.encard = M.coverNumber k := by
--   simpa using csInf_mem <| (M.setOf_cover_nonempty hk).image encard



-- lemma coverNumber_contract {a : ℕ∞} (hX : X ⊆ M.E) :
--     M.coverNumber (a + M.eRk X) ≤ (M ／ X).coverNumber a := by
--   --Mathieu, do you want to do this one?
--   sorry

-- def closZ (a : ℕ) (hx : X.Finite ) (hX : X ⊆ M.E)
--     (Y : (M ↾ F).closure '' { Y | Y ⊆ X ∧ M.eRk Y = a} )
--     : ∃ Z :  { Y | Y ⊆ X ∧ M.eRk Y = a}, Y.1 = Z.1 := by
--   have := (mem_image ((M ↾ F).closure) ({ Y | Y ⊆ X ∧ M.eRk Y = a}) Y.1  ).1 Y.2
--   obtain ⟨Y, hY ⟩ := (mem_image ((M ↾ F).closure) ({ Y | Y ⊆ X ∧ M.eRk Y = a}) Y.1  ).1 Y.2
--   sorry

-- def IsFlat.restriction_clo (hF : M.IsFlat F) (hY : Y ⊆ F) : M.closure Y = (M ↾ F).closure Y :=
--     by
--   sorry



--Dont need
-- def closZ (a : ℕ)
--     (Z : (M ↾ F).closure '' { Y | Y ⊆ X ∧ M.eRk Y = a} )
--     : ∃ Y :  { Y | Y ⊆ X ∧ M.eRk Y = a}, (M ↾ F).closure Y.1 = Z.1 := by
--   --have := (mem_image ((M ↾ F).closure) ({ Y | Y ⊆ X ∧ M.eRk Y = a}) Y.1  ).1 Y.2
--   obtain ⟨Y, hY, h ⟩ := (mem_image ((M ↾ F).closure) ({ Y | Y ⊆ X ∧ M.eRk Y = a}) Z.1  ).1 Z.2
--   use ⟨Y, hY⟩

-- def getI (a : ℕ) (hX : X ⊆ M.E)
--     (Y : { Y | Y ⊆ X ∧ M.eRk Y = a} )
--     : ∃ I : {Y | Y ⊆ X ∧ Y.encard = a}, I.1 ⊆ X ∧ (M.IsBasis I Y.1) ∧ I.1.encard = a := by
--   --have : Y ⊆ M.E := by sorry
--   obtain ⟨I, hIB, hc ⟩ := (M.eq_eRk_iff.1 Y.2.2)
--   have h' :  I ∈ {Y | Y ⊆ X ∧ Y.encard = ↑a} := by
--     refine ⟨LE.le.subset fun ⦃a⦄ a_2 ↦ (Y.2.1 ) (IsBasis.subset hIB  a_2) , hc ⟩
--   use ⟨ I, h' ⟩
--   refine ⟨h'.1, hIB , hc ⟩

-- def ranksubsets_Map (a : ℕ) (b : ℕ) (hx : X.Finite ) (hX : X ⊆ M.E) (hF : M.IsFlat F) (hXF : X ⊆ F)
--     : Function.Embedding
--     ((M ↾ F).closure '' { Y | Y ⊆ X ∧ M.eRk Y = a}) {Y | Y ⊆ X ∧ Y.encard = a} :=
-- --have := LE.le.subset fun ⦃a⦄ a_1 ↦ hX (hY.1 a_1)
-- { toFun := fun Z =>
--     ⟨ (Classical.choose (getI a hX (Classical.choose (closZ a Z ))) ).1 ,
--     (Classical.choose (getI a hX (Classical.choose (closZ a Z ))) ).2 ⟩
--   inj' := by
--     intro x y hxy
--     simp only [Subtype.mk.injEq] at hxy
--     have heq : x.1 = y.1 := by
--       rw[ ←(Classical.choose_spec (closZ a x )), ←(Classical.choose_spec (closZ a y )) ]
--       --simp only [mem_setOf_eq, coe_setOf ]
--       rw[←hF.restriction_clo ?_, ←hF.restriction_clo ?_,
--       ←((Classical.choose_spec (getI a hX (Classical.choose (closZ a x ))) ).2.1).closure_eq_closure,
--       ←((Classical.choose_spec (getI a hX (Classical.choose (closZ a y ))) ).2.1).closure_eq_closure,
--       hxy ]
--       --simp only [restrict_closure_eq']
--       --have := (Classical.choose_spec (getI a hX (Classical.choose (closZ a x ))) ).1
--       have := (Classical.choose (closZ a x )).2.1
--       --exact LE.le.subset fun ⦃b⦄ b_2 ↦ hXF (this b_2)
--       --grw[hXF] at this
--       --intro Y hY

--       --simp only [mem_setOf_eq, coe_setOf] at this

--       sorry
--       · sorry
--     exact SetCoe.ext heq
--     --rw[ ] at hxy

--     }

lemma set_to_binom_number {a b : ℕ} (X : Set α) (hX : X.encard = b) :
    {Y | Y ⊆ X ∧ Y.encard = a}.encard = b.choose a := by
  have hXfin : X.Finite := by simp [← encard_lt_top_iff, hX]
  set X' := hXfin.toFinset with hX'
  have := (ENat.coe_inj).2 <| X'.card_powersetCard a
  convert (ENat.coe_inj).2 <| X'.card_powersetCard a
  · rw [← encard_coe_eq_coe_finsetCard, ← Finset.coe_injective.encard_image (β := Set α)]
    convert rfl
    ext S
    simp only [mem_image, SetLike.mem_coe, Finset.mem_powersetCard, mem_setOf_eq,
      hX', Finite.subset_toFinset]
    constructor
    · rintro ⟨T, ⟨hTX, rfl⟩, rfl⟩
      simpa
    intro ⟨hSX, hSa⟩
    refine ⟨Finite.toFinset (s := S) ?_, ?_⟩
    · simp [← encard_lt_top_iff, hSa]
    simp_rw [← ENat.coe_inj, ← hSa, ← Finite.encard_eq_coe_toFinset_card]
    simpa
  rw [← ENat.coe_inj, ← hX, eq_comm, hXfin.encard_eq_coe_toFinset_card]

-- lemma base_isCover {a : ℕ} (hr : M.eRank ≤ a + 1) (ha : 1 ≤ a) (hXfin : X.Finite)
--     --(h : Maximal (fun Y ↦ Y ⊆ M.E ∧ (M ↾ Y).IsFiniteRankUniform (a + 1) Y.encard) X) :
--     (h : MaximalFor (fun x ↦ x ∈ {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1) X.encard}) encard X) :
--     M.IsRankCover a (M.closure '' {K | K ⊆ X ∧ K.encard = a}) := by
--   refine ⟨?_, ?_⟩
--   · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
--     · simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
--       grind
--     obtain ⟨E, hEX, hEunif⟩ := h.prop.2.exists_eq_unifOn
--     obtain rfl : X = E := congr_arg Matroid.E hEunif
--     by_contra! hcon
--     simp only [sUnion_image, mem_setOf_eq, mem_iUnion, exists_prop, not_exists, not_and,
--       and_imp] at hcon
--     have hcon' (Z) (hZ : Z ⊆ X) (hZa : Z.encard ≤ a) : e ∉ M.closure Z := by
--       have haX : a ≤ X.encard := by
--         grw [← M.restrict_ground_eq (R := X), ← eRank_le_encard_ground, h.prop.2.eRank_eq]
--         simp
--       obtain ⟨W, hZW, hWZ, hW⟩ := exists_superset_subset_encard_eq hZ hZa haX
--       exact notMem_subset (M.closure_subset_closure hZW) (hcon W hWZ hW)
--     have heX : e ∉ X := by
--       by_contra hc
--       exact hcon' (singleton e) (singleton_subset_iff.mpr hc )
--         (by simp only [encard_singleton, ENat.one_le_coe, ha ]) (mem_closure_self M e he )
--     --have hwin := h.not_prop_of_ssuperset (t := insert e X) (by grind)
--     have hwin := h.not_prop_of_gt (j := insert e X)
--       (Finite.encard_lt_encard hXfin (ssubset_insert heX ))
--     simp only [mem_setOf_eq, not_and, insert_subset_iff.mpr ⟨he, h.prop.1 ⟩,forall_const ] at hwin
--     --rw [insert_subset_iff , and_iff_right he, and_iff_right h.prop.1] at hwin
--     apply hwin
--     suffices aux : (M ↾ insert e X) = unifOn (insert e X) (a + 1) by
--       rw [aux]
--       apply unifOn_isFiniteRank_uniform
--       grw [h.prop.2.le, ← subset_insert]
--     refine ext_indep rfl fun I (hI : I ⊆ insert e X) ↦ ?_
--     simp only [restrict_indep_iff, hI, and_true, unifOn_indep_iff, Nat.cast_add, Nat.cast_one]
--     refine ⟨fun hIi ↦ by grw [hIi.encard_le_eRank, hr], fun hcard ↦ ?_⟩
--     have hI₀ : M.Indep (I \ {e}) := by
--       have hrestr := (M.restrict_indep_iff (R := X) (I := I \ {e})).1
--       nth_grw 1 [hEunif, unifOn_indep_iff, diff_subset] at hrestr
--       grind
--     by_cases! heI : e ∉ I
--     · rwa [diff_singleton_eq_self heI] at hI₀
--     rw [← insert_diff_self_of_mem heI, hI₀.insert_indep_iff_of_notMem (by grind), mem_diff,
--       and_iff_right he]
--     refine hcon'  _ (by grind) ?_
--     grw [← ENat.add_one_le_add_one_iff, ← hcard, encard_diff_singleton_add_one heI]
--   simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
--   rintro F I hI hcard rfl
--   grw [eRk_closure_eq, eRk_le_encard, hcard]

lemma base_isCover {a : ℕ} (hr : M.eRank ≤ a + 1) (ha : 1 ≤ a) (hXfin : X.Finite)
    --(h : Maximal (fun Y ↦ Y ⊆ M.E ∧ (M ↾ Y).IsFiniteRankUniform (a + 1) Y.encard) X) :
    (h : MaximalFor (fun x ↦ x ∈ {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1) }) encard X) :
    M.IsRankCover a (M.closure '' {K | K ⊆ X ∧ K.encard = a}) := by
  refine ⟨?_, ?_⟩
  · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
    · simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
      grind
    obtain ⟨E, hEX, hEunif⟩ := h.prop.2.exists_eq_unifOn
    --obtain rfl : X = E := congr_arg Matroid.E hEunif
    by_contra! hcon
    simp only [sUnion_image, mem_setOf_eq, mem_iUnion, exists_prop, not_exists, not_and,
      and_imp] at hcon
    have hcon' (Z) (hZ : Z ⊆ X) (hZa : Z.encard ≤ a) : e ∉ M.closure Z := by
      have haX : a ≤ X.encard := by
        grw [← M.restrict_ground_eq (R := X), ← eRank_le_encard_ground, h.prop.2.eRank_eq]
        simp
      obtain ⟨W, hZW, hWZ, hW⟩ := exists_superset_subset_encard_eq hZ hZa haX
      exact notMem_subset (M.closure_subset_closure hZW) (hcon W hWZ hW)
    have heX : e ∉ X := by
      by_contra hc
      exact hcon' (singleton e) (singleton_subset_iff.mpr hc )
        (by simp only [encard_singleton, ENat.one_le_coe, ha ]) (mem_closure_self M e he )
    --have hwin := h.not_prop_of_ssuperset (t := insert e X) (by grind)
    have hwin := h.not_prop_of_gt (j := insert e X)
      (Finite.encard_lt_encard hXfin (ssubset_insert heX ))
    simp only [mem_setOf_eq, not_and, insert_subset_iff.mpr ⟨he, h.prop.1 ⟩,forall_const ] at hwin
    --rw [insert_subset_iff , and_iff_right he, and_iff_right h.prop.1] at hwin
    apply hwin
    suffices aux : (M ↾ insert e X) = unifOn (insert e X) (a + 1) by
      rw [aux]
      apply unifOn_isFiniteRankUniform
      grw [h.prop.2.le , ← subset_insert]
      exact encard_le_encard fun ⦃a⦄ a_1 ↦ a_1
    refine ext_indep rfl fun I (hI : I ⊆ insert e X) ↦ ?_
    simp only [restrict_indep_iff, hI, and_true, unifOn_indep_iff, Nat.cast_add, Nat.cast_one]
    refine ⟨fun hIi ↦ by grw [hIi.encard_le_eRank, hr], fun hcard ↦ ?_⟩
    have hI₀ : M.Indep (I \ {e}) := by
      have hrestr := (M.restrict_indep_iff (R := X) (I := I \ {e})).1
      have : I \ {e} ⊆ E  := by
        rw [ ←unifOn_ground_eq E (k := a + 1), ← hEX, restrict_ground_eq, diff_subset_iff, singleton_union]
        exact LE.le.subset hI
      nth_grw 1 [hEX, unifOn_indep_iff, diff_subset] at hrestr
      grind
    by_cases! heI : e ∉ I
    · rwa [diff_singleton_eq_self heI] at hI₀
    rw [← insert_diff_self_of_mem heI, hI₀.insert_indep_iff_of_notMem (by grind), mem_diff,
      and_iff_right he]
    refine hcon'  _ (by grind) ?_
    grw [← ENat.add_one_le_add_one_iff, ← hcard, encard_diff_singleton_add_one heI]
  simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
  rintro F I hI hcard rfl
  grw [eRk_closure_eq, eRk_le_encard, hcard]

lemma baseCase {a b : ℕ} (ha : 1 ≤ a) (hM : NoUniformMinor M (a + 1) (b + 1))
    (hr : M.eRank = a + 1) :
    M.coverNumber (fun M X ↦ M.eRk X ≤ a) ≤ Nat.choose b a := by
  have : M.RankFinite := M.eRank_ne_top_iff.mp (ENat.ne_top_iff_exists.2
      (Exists.intro ((fun x1 x2 ↦ x1 + x2) a 1) (hr.symm)))
  by_contra! hcon
  obtain ⟨B, hB⟩ := M.exists_isBase
  set Unif : Set (Set α) := {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1) } with h_UnifS
  have hne : Unif.Nonempty := by
    refine ⟨B, (IsBase.subset_ground hB), ?_, ?_,⟩
    · rwa [eRank_restrict, hB.eRk_eq_eRank]
    rw [hB.indep.restrict_eq_freeOn]
    exact freeOn_uniform B
  have hYbound : ∀ Y, Y ∈ Unif → Y.encard < b + 1 := by
    intro X hX
    by_contra hc
    simp only [not_lt] at hc
    --have : X ⊆ M.E := by exact hX.1
    have h2 : ((unifOn (M ↾ X).E (a + 1)).NoUniformMinor (a + 1) (b + 1)) := by
      rw[←hX.2.eq_unifOn ]
      exact hM.minor (IsRestriction.isMinor (restrict_isRestriction M X) )
    have h3 := unifOn_noUniformMinor_iff.1 h2
    grw [← restrict_ground_eq (M := M) (R := X)] at hc
    grind
    --simp only [mem_setOf_eq] at hX
    -- exact hc.not_gt <| hM.lt_of_isoMinor (N := M ↾ X) (b' := X.encard)
    --   (restrict_isRestriction _ _ hX.1).isMinor.isoMinor sorry
  have hcard : (encard '' Unif).Finite := by
    refine ENat.finite_of_sSup_lt_top ?_
    refine lt_of_le_of_lt ?_ <| WithTop.natCast_lt_top (b + 1)
    simp only [sSup_le_iff, mem_image, forall_exists_index, and_imp]
    intro k A hAE h
    rw[←h ]
    exact Std.le_of_lt (hYbound A ⟨hAE.1, hAE.2 ⟩ )
  obtain ⟨X, hX⟩ := Finite.exists_maximalFor' encard _ hcard hne
  have hXb : X.encard < b + 1 := hYbound X hX.prop
  set Subsets : Set (Set α) := { Y | Y ⊆ X ∧ Y.encard = a} with h_sub
  --(Set.encard_le_coe_iff.1 (ENat.lt_coe_add_one_iff.mp hXb )).1
  have hiC := base_isCover (Std.le_of_eq hr ) ha
      ((Set.encard_le_coe_iff.1 (ENat.lt_coe_add_one_iff.mp hXb )).1) hX
  --have hiC : M.IsCover (fun M X ↦ M.eRk X ≤ a) (M.closure '' Subsets) := by base_isCover
  obtain ⟨x, hx ⟩ := ENat.ne_top_iff_exists.1 (LT.lt.ne_top hXb )
  rw[←hx] at hXb
  grw [hiC.coverNumber_le, Set.encard_image_le, (set_to_binom_number) X hx.symm,
    (Nat.choose_le_choose a (Nat.le_of_lt_succ (ENat.coe_lt_coe.mp hXb )))] at hcon
  simp only [lt_self_iff_false] at hcon

lemma coverNumber_rank_Frombase {a b : ℕ} (ha : 1 ≤ a)
    (hM : NoUniformMinor M ( a + 1 ) (b + 1)) :
    M.coverNumber (fun M X ↦ M.eRk X ≤ a) ≤
    (Nat.choose b a) * M.coverNumber (fun M X ↦ M.eRk X ≤ (a + 1)) := by
  sorry

lemma coverNumber_Bound {M : Matroid α} [M.RankPos] {a b : ℕ} {n : ℕ∞} (ha : a ≠ 0) (hb : a ≤ b)
    (hM : NoUniformMinor M ( a + 1 ) (b + 1)) (hn : M.eRank = a + n) :
    M.coverNumber (fun M X ↦ M.eRk X ≤ a) ≤ (Nat.choose b a)^(M.eRank - a) := by
  obtain htop | hfin := eq_or_ne M.eRank ⊤
  · grw [htop, ENat.top_sub_coe, ENat.epow_top, ← le_top]
    obtain rfl | hlt := hb.eq_or_lt
    · simp [noUniformMinor_self_iff, htop] at hM
    rw [← ENat.coe_one, ENat.coe_lt_coe]
    suffices b.choose a ≠ 0 ∧ b.choose a ≠ 1 by lia
    exact ⟨(Nat.choose_pos hlt.le).ne.symm, by simp [Nat.choose_eq_one_iff, hlt.ne.symm, ha]⟩
  by_cases h0 : n = 0
  · -- When M.eRank = a, you can cover with (M.E). This is a lemma somewhere
    sorry
  --Now you can assume n ≠ 0 and n - 1 makes sense
  obtain ⟨e, heC⟩ : ∃ e, M.IsNonloop e := exists_isNonloop M
  have h' : (M ／ {e}).eRank < M.eRank := by sorry
  have hRP : ( M ／ {e}).RankPos := by sorry --I think here you need n ≠ 0
  have hM' : NoUniformMinor ( M ／ {e}) ( a + 1 ) (b + 1) := by sorry
  have hn' : (M ／ {e}).eRank = a + (n - 1) := by sorry
  have ih := coverNumber_Bound (M := M ／ {e}) (a := a) (b := b) ha hb hM' (n := n - 1)
  sorry
termination_by M.eRank

  -- suffices hn : ∀ n : ℕ, M.eRank = n + a + 1 →
  --     M.coverNumber (fun M X ↦ M.eRk X ≤ a) ≤ (Nat.choose b a)^(n + 1 )
  -- ·
  --   sorry
  -- intro n hn
  -- induction n generalizing M with
  -- | zero => sorry
  -- | succ n IH => sorry

-- -- change `ha` to `a ≠ 0`.
-- lemma coverNumber_Bound_contract [M.RankFinite] {a b : ℕ} (ha : 1 ≤ a)
--     (hM : NoUniformMinor M ( a + 1 ) (b + 1)) (hC : C ⊂ M.E)  :
--     M.coverNumber (fun M X ↦ M.eRk X ≤ a) ≤
--     (Nat.choose b a)^(M.eRk C ) * (M／C).coverNumber (fun M X ↦ M.eRk X ≤ a) := by
--   suffices hn : ∀ n : ℕ, n = M.eRk C →  M.coverNumber (fun M X ↦ M.eRk X ≤ a) ≤
--       (Nat.choose b a)^n * (M／C).coverNumber (fun M X ↦ M.eRk X ≤ a)
--   · obtain ⟨ n, hh ⟩ := ENat.ne_top_iff_exists.1 ( eRk_ne_top (M := M) (X := C))
--     rw[←hh]
--     exact le_of_eq_of_le rfl (hn n hh)
--   intro n hn
--   induction n generalizing M C with
--   | zero =>
--     simp only [pow_zero, one_mul]
--     rw [coverNumber_contract_loop ((ground_nonempty_iff (M ＼ C)).mp (nonempty_of_ssubset hC ) )
--       (ENat.one_le_coe.mpr ha ) ((eRk_eq_zero_iff (subset_of_ssubset hC)).1 hn.symm )]
--   | succ n IH =>
--   grw[coverNumber_rank_Frombase ha hM ]
--   have hresP : (M ↾ C).RankPos :=
--     (eRank_ne_zero_iff (M ↾ C)).mp <| by simp [eRank_restrict, ne_eq, ← hn]

--   obtain ⟨e, heC ⟩ := exists_isNonloop (M ↾ C)
--   obtain ⟨heC1, heC2 ⟩ := restrict_isNonloop_iff.1 heC
--   have heN : (M／ {e}).Nonempty := by
--     rw[←(M／ {e}).ground_nonempty_iff, contract_ground]
--     exact (Set.nonempty_of_ssubset (by grind ) )
--   grw[ coverNumber_contract_one (heC1.mem_ground ) heC1 heN]
--   have hn1 : (M／ {e}).eRk (C \ {e}) = n := by
--     have hrelrk := IsNonloop.eRelRk_add_one_eq heC1 (C \ {e})
--     simp only [insert_diff_singleton, insert_eq_of_mem heC2, ←hn, Nat.cast_add, Nat.cast_one,
--       ne_eq, ENat.one_ne_top, not_false_eq_true,
--       add_left_inj_of_ne_top] at hrelrk
--     rwa [eRelRk.eq_1] at hrelrk
--   have hsub1 : (C \ {e}) ⊂ (M／ {e}).E := by
--     simp only [contract_ground]
--     refine Set.ssubset_iff_subset_ne.mpr ⟨diff_subset_diff_left (subset_of_ssubset hC), ?_ ⟩
--     by_contra hc
--     have h : C = M.E := by
--       rw [←insert_diff_self_of_mem heC2, ←insert_diff_self_of_mem heC1.mem_ground, hc]
--     have hCE : C ≠ M.E := by exact Std.ne_of_lt hC
--     rw [h] at hCE
--     exact false_of_ne hCE
--   grw[ IH (hM.minor (contract_isMinor M {e} )) hsub1 hn1.symm ]
--   simp only [contract_contract, union_diff_self, singleton_union, ge_iff_le, insert_eq_of_mem heC2,
--     ←mul_assoc ]
--   nth_rw 1 [ ←ENat.epow_one (x := ↑(b.choose a)), ←ENat.epow_natCast,
--     ←ENat.epow_add (x :=  ↑(b.choose a)) (y := 1) (z := n ), ←ENat.coe_one, ←ENat.coe_add,
--     ENat.epow_natCast, add_comm ]


-- change `ha` to `a ≠ 0`.
lemma coverNumber_Bound_contract {M : Matroid α} {C : Set α} {a b : ℕ} (ha : a ≠ 0) (hb : a ≤ b)
    (hM : NoUniformMinor M (a + 1) (b + 1)) (hC : C ⊂ M.E)  :
    M.coverNumber (fun M X ↦ M.eRk X ≤ a) ≤
    (Nat.choose b a)^(M.eRk C) * (M ／ C).coverNumber (fun M X ↦ M.eRk X ≤ a) := by
  obtain htop | hlt := eq_or_ne (M.eRk C) ⊤
  · grw [htop, ENat.epow_top, ENat.top_mul, ← le_top ]
    · have heN : (M／ C).Nonempty := by
        rw[←(M／ C).ground_nonempty_iff, contract_ground]
        exact (Set.nonempty_of_ssubset (by grind ) )
      exact ENat.one_le_iff_ne_zero.mp (coverNumer_positive (fun M X ↦ M.eRk X ≤ a) )
    obtain rfl | hlt := hb.eq_or_lt
    · simp [noUniformMinor_self_iff] at hM
      grw [ ←eRk_le_eRank M C, htop ] at hM
      simp only [not_top_lt] at hM
    rw [← ENat.coe_one, ENat.coe_lt_coe]
    suffices b.choose a ≠ 0 ∧ b.choose a ≠ 1 by lia
    exact ⟨(Nat.choose_pos hlt.le).ne.symm, by simp [Nat.choose_eq_one_iff, hlt.ne.symm, ha] ⟩
  have hresP : (M ↾ C).RankPos := sorry
    -- (eRank_ne_zero_iff (M ↾ C)).mp <| by simp [eRank_restrict, ne_eq, ← hn]
  obtain ⟨e, heC⟩ : ∃ e, (M ↾ C).IsNonloop e := exists_isNonloop (M ↾ C)
  rw [restrict_isNonloop_iff] at heC
  -- have hrelrk := IsNonloop.eRelRk_add_one_eq heC.1 (C \ {e})
  -- simp only [insert_diff_singleton, insert_eq_of_mem heC.2] at hrelrk
  have h' : (M ／ {e}).eRk (C \ {e}) < M.eRk C := by
    have hrelrk := IsNonloop.eRelRk_add_one_eq heC.1 (C \ {e})
    simp only [insert_diff_singleton, insert_eq_of_mem heC.2] at hrelrk
    rw [ ←hrelrk, eRelRk.eq_1 ]
    simp only [ENat.lt_add_left_iff, ne_eq, eRk_eq_top_iff, IsRkFinite.diff_singleton_iff, not_not,
      one_ne_zero, not_false_eq_true, and_true]
    rw [ IsRkFinite ]
    refine eRank_lt_top_iff.mp ?_
    grw [eRank_restrict, eRk_contract_le_eRk M {e} C]
    exact Ne.lt_top' (id (Ne.symm hlt))
  have hsub1 : (C \ {e}) ⊂ (M／ {e}).E := by
    simp only [contract_ground]
    refine Set.ssubset_iff_subset_ne.mpr ⟨diff_subset_diff_left (subset_of_ssubset hC), ?_ ⟩
    by_contra hc
    have h : C = M.E := by
      rw [←insert_diff_self_of_mem heC.2, ←insert_diff_self_of_mem heC.1.mem_ground, hc]
    grind
  have heN : (M／ {e}).Nonempty := by
    rw[←(M／ {e}).ground_nonempty_iff, contract_ground]
    exact (Set.nonempty_of_ssubset (by grind ) )
  have : 1 ≤ a := by exact Nat.one_le_iff_ne_zero.mpr ha
  have ih := coverNumber_Bound_contract (M := M ／ {e}) (C := C \ {e}) (a := a) (b := b) ha
    hb (hM.minor (contract_isMinor M {e} )) hsub1
  grw [coverNumber_rank_Frombase (Nat.one_le_iff_ne_zero.mpr ha) hM, coverNumber_contract_one (heC.1.mem_ground ) heC.1 heN, ih ]
  simp only [contract_contract, union_diff_self, singleton_union, ge_iff_le, insert_eq_of_mem heC.2,
    ←mul_assoc]
  nth_rw 1 [←eRelRk.eq_1, ←ENat.epow_one (x := ↑(b.choose a)),
    ←ENat.epow_add (x :=  ↑(b.choose a)) (y := 1) (z := (M.eRelRk {e} (C \ {e})) ),
    ←add_comm (a := (M.eRelRk {e} (C \ {e}))) (b:= 1 ), (heC.1).eRelRk_add_one_eq, insert_diff_singleton, insert_eq_of_mem heC.2 ]

termination_by M.eRk C


end Rank

section NonSpanning

lemma NonSpanning_to_RankCover [M.RankFinite] (hM : 2 ≤ M.eRank) :
    M.IsCover Matroid.Nonspanning T ↔ M.IsRankCover (M.eRank - 1) T := by
  refine ⟨?_, ?_ ⟩
  · intro h
    refine ⟨ h.sUnion_eq, ?_ ⟩
    intro F hF
    by_contra hc
    simp only [not_le] at hc
    have : M.eRank ≤ M.eRk F := by
      have : M.eRank - 1 + 1 ≤  M.eRk F := by exact Order.add_one_le_of_lt hc
      sorry
    sorry
  sorry

lemma NonSpaning_le_two [M.Nonempty] (hle : M.eRank ≤ 1) :
    ⊤ ≤ M.coverNumber (Matroid.Nonspanning) := by
  obtain hT | ⟨T, hT1, hT2 ⟩  := M.exists_cover (Matroid.Nonspanning)
  · rw[ hT ]
  by_contra hc
  have : M.RankFinite := by
    refine eRank_lt_top_iff.mp ?_
    grw[hle]
    exact ENat.one_lt_top
  have hu := hT1.sUnion_eq
  have hl : ∀ T1 ∈ T, T1 ⊆ M.loops := by
    intro T1 hT'
    have h1 : M.eRk T1 < M.eRank := Nonspanning.eRk_lt (hT1.pProp T1 hT' )
    grw [hle] at h1
    simp only [ENat.lt_one_iff] at h1
    exact (M.eRk_eq_zero_iff (X := T1) (hX := by grind)).1 h1
  have hs : M.E ⊆ M.loops := by
    rw [←hT1.sUnion_eq]
    exact sUnion_subset hl
  obtain ⟨T', hT' ⟩ := hT1.nonempty
  have h2 : M.E ⊆ M.closure T' := by
    grw [hs]
    exact loops_subset_closure M T'
  exact Ne.elim (fun a ↦ ((hT1.pProp T' hT').not_spanning) ((spanning_iff_ground_subset_closure
    (hT1.subset_ground hT') ).2 h2)) hT2


lemma Non_spanning_singleton (he : e ∈ M.E) (hM : 2 ≤ M.eRank) : M.Nonspanning {e} := by
    by_contra hc
    have h1 : M.eRank ≤ 1 := by
      rw [not_nonspanning_iff] at hc
      rw [←hc.eRk_eq]
      simp only [eRk_singleton_le]
    grw [←hM] at h1
    simp only [ENat.not_ofNat_le_one] at h1

lemma IsCover_singleton_NonSpanning (hM : 2 ≤ M.eRank) :
    M.IsCover (Matroid.Nonspanning) (singleton '' M.E) := by
  exact IsCover_singleton_Prop (fun e he ↦ Non_spanning_singleton he hM)

lemma IsCover_singleton_le_NonSpanning (hM : 2 ≤ M.eRank) :
    M.coverNumber (Matroid.Nonspanning) ≤ M.E.encard := by
  exact IsCover_singleton_le (fun e he ↦ Non_spanning_singleton he hM)

lemma NonSpaning_cover_exists (hM : 2 ≤ M.eRank) : M.hasCover_with Matroid.Nonspanning := by
  refine ⟨(singleton '' M.E), IsCover_singleton_NonSpanning hM ⟩

lemma IsNonSpaningCover_contract (h : (M ／ X).IsCover (Matroid.Nonspanning) T)
    (hX : X ⊆ M.E) (hXN : (M ／ X).Nonempty) :
    M.IsCover (Matroid.Nonspanning) ((· ∪ X) '' T) := by
  apply h.contract hX hXN
  intro Y hC
  refine ⟨ ?_, union_subset (by have := hC.subset_ground; grind ) hX  ⟩
  · by_contra hc
    have hcc : (M ／ X).Spanning Y := by
      have h1 := hc.contract X
      simp only [union_diff_right] at h1
      exact h1.superset (diff_subset (s := Y) (t := X)) (hC.subset_ground)
    rw [←not_spanning_iff hcc.subset_ground ] at hC
    exact (iff_false_intro hC).mp hcc

lemma NonSpanningNumber_contract (hX : X ⊆ M.E) (hne : (M ／ X).Nonempty) :
    M.coverNumber Matroid.Nonspanning ≤ (M ／ X).coverNumber Matroid.Nonspanning := by
  obtain hT | ⟨T, hT, hTe ⟩ := (M ／ X).exists_cover (Matroid.Nonspanning)
  · rw [hT]
    exact OrderTop.le_top (M.coverNumber Nonspanning)
  rw [← hTe]
  exact
    Std.IsPreorder.le_trans (M.coverNumber Nonspanning) ((fun x ↦ x ∪ X) '' T).encard T.encard
      ((IsNonSpaningCover_contract hT hX hne).coverNumber_le)
      (encard_image_le (fun x ↦ x ∪ X) T )

lemma NonSpanningNumber_set_closure (hY : Y ⊆ M.closure X) (hX : X ⊆ M.E) :
    (M ↾ X).coverNumber Nonspanning  ≤ (M ↾ (X ∪ Y)).coverNumber Nonspanning := by
  obtain hT | ⟨T, hT, hTe ⟩ := (M ↾ (X ∪ Y)).exists_cover (Matroid.Nonspanning)
  · rw [hT]
    exact OrderTop.le_top ((M ↾ X).coverNumber Nonspanning)
  rw[←hTe]
  have hcov : (M ↾ X).IsCover (Matroid.Nonspanning) ((fun x ↦ x ∩ X) '' T) := by
    refine ⟨?_, ?_ ⟩
    · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
      · intro hK
        obtain ⟨K', hK'T, hK' ⟩ := hK
        rw [← hK']
        grind
      have h1 := hT.sUnion_eq
      simp only [restrict_ground_eq] at h1
      simp only [restrict_ground_eq] at he
      have : e ∈  ⋃₀ T := by grind
      obtain ⟨ T', hT', heT' ⟩ := this
      have : e ∈ T' ∩ X := by grind
      grind
    intro F hF
    obtain ⟨F', hF', hhF' ⟩ := hF
    simp only at hhF'
    rw [← hhF']
    by_contra hc
    rw [not_nonspanning_iff, restrict_spanning_iff (by grind)] at hc
    have hcc : X ∪ Y ⊆ M.closure F' := union_subset (LE.le.subset fun ⦃a⦄ a_1 ↦
      (closure_subset_closure M (inter_subset_left )) (hc a_1)) ( LE.le.subset fun ⦃a⦄ a_1 ↦
      (closure_subset_closure M (inter_subset_left )) ((LE.le.subset fun ⦃a⦄ a_1 ↦
      (closure_subset_closure_of_subset_closure hc ) (hY a_1) ) a_1))
    rw [←restrict_spanning_iff (hR := by grind), ←not_nonspanning_iff (by grind)  ] at hcc
    exact Ne.elim (fun a ↦ hcc (hT.pProp F' hF')) hTe
    exact LE.le.subset (hT.subset_ground hF')
  grw [hcov.coverNumber_le ]
  exact encard_image_le (fun x ↦ x ∩ X) T



-- lemma NonSpaningNumber_delete_loop (hne : (M ＼ D).Nonempty) (hk : 1 ≤ k) (hD : D ⊆ M.loops ) :
--     M.coverNumber (fun M X ↦ M.eRk X ≤ k) = (M ＼ D).coverNumber (fun M X ↦ M.eRk X ≤ k) := by

--   sorry
  -- obtain ⟨T, hT, hTen ⟩ := exists_min_cover (RankPropCover_exists (M := M) hk )
  -- have h1 := (hT.delete D ).coverNumber_le
  -- grw[encard_image_le (fun s ↦ s \ D) T, hTen ] at h1
  -- obtain ⟨T', hT', hT'en ⟩ := exists_min_cover (RankPropCover_exists (M := (M ＼ D)) hk )
  -- have hcov : M.IsCover (fun M X ↦ M.eRk X ≤ k) (M.closure '' T' ) := by
  --   refine ⟨ ?_, ?_ ⟩
  --   · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
  --     · simp only [mem_image, forall_exists_index, and_imp]
  --       grind
  --     by_cases heD : e ∈ D
  --     · obtain ⟨ X, hX ⟩ := hT'.nonempty
  --       have := (IsLoop.mem_closure (hD heD) X )
  --       grind
  --     have h2 : e ∈ M.E \ D := mem_diff_of_mem he heD
  --     rw[←delete_ground,  ←hT'.sUnion_eq  ] at h2
  --     obtain ⟨ X, hX, heX ⟩ := h2
  --     have := (mem_closure_of_mem' M heX he )
  --     grind
  --   intro F hF
  --   obtain ⟨F' ,hF', hF2 ⟩ := hF
  --   rw[←hF2, eRk_closure_eq M F']
  --   have ha := hT'.pProp F' hF'
  --   simp only [delete_eRk_eq'] at ha
  --   have ha1 : F' \ D = F' := by
  --     have := hT'.subset_ground hF'
  --     grind
  --   rwa [ha1] at ha
  -- have h2 := hcov.coverNumber_le
  -- grw [encard_image_le M.closure T', hT'en] at h2
  -- grind

-- lemma NonSpaningNumber_contract_loop (hne : (M ＼ D).Nonempty) (hk : 1 ≤ k) (hD : D ⊆ M.loops ) :
--     M.coverNumber (fun M X ↦ M.eRk X ≤ k) = (M ／ D).coverNumber (fun M X ↦ M.eRk X ≤ k) := by
--   rw[contract_eq_delete_of_subset_loops hD]
--   exact coverNumber_delete_loop hne hk hD




end NonSpanning












-- section Indexed

-- variable {T : ι → Set α}

-- @[mk_iff]
-- structure IsIndexedCover (M : Matroid α) (k : ℕ∞) (T : ι → Set α) : Prop where
--   iUnion_eq : ⋃ i, T i = M.E
--   eRk_le : ∀ i, M.eRk (T i) ≤ k

-- lemma IsIndexedCover.subset_ground (h : M.IsIndexedCover k T) (i : ι) : T i ⊆ M.E := by
--   grw [← h.iUnion_eq, ← subset_iUnion]

-- lemma IsIndexedCover.isIndexedCover_closure (h : M.IsIndexedCover k T) :
--     M.IsIndexedCover k (fun i ↦ M.closure (T i)) := by
--   refine ⟨(iUnion_subset (fun i ↦ M.closure_subset_ground ..)).antisymm ?_, fun i ↦ ?_⟩
--   · grw [← h.iUnion_eq, iUnion_mono (fun i ↦ M.subset_closure (T i) (h.subset_ground i))]
--   simpa using h.eRk_le i

-- lemma setOf_point_isIndexedCover (M : Matroid α) [M.RankPos] :
--     M.IsIndexedCover 1 (fun x : {P // M.IsPoint P} ↦ x.1) := by
--   refine ⟨(iUnion_subset fun P ↦ P.2.subset_ground).antisymm fun e he ↦ ?_, ?_⟩
--   · obtain hl | hnl := M.isLoop_or_isNonloop e
--     · obtain ⟨f, hf⟩ := M.exists_isNonloop
--       exact mem_iUnion_of_mem (i := ⟨M.closure {f}, hf.closure_isPoint⟩) <| hl.mem_closure {f}
--     exact mem_iUnion_of_mem (i := ⟨M.closure {e}, hnl.closure_isPoint⟩) <| M.mem_closure_self e
--   simp +contextual [IsPoint.eRk]

-- lemma IsIndexedCover.cover_cover {η : ι → Type*} (h : M.IsIndexedCover k T)
--     (T₀ : (i : ι) → (η i) → Set α) (hT₀ : ∀ i, (M ↾ (T i)).IsIndexedCover a (T₀ i)) :
--     M.IsIndexedCover a (fun i : ((i : ι) × η i) ↦ T₀ i.1 i.2) := by
--   refine ⟨?_, ?_⟩
--   · rw [← h.iUnion_eq, iUnion_sigma]
--     refine iUnion_congr fun i ↦ ?_
--     rw [(hT₀ i).iUnion_eq, restrict_ground_eq]
--   rintro ⟨i, j⟩
--   have := (hT₀ i).eRk_le j
--   rwa [restrict_eRk_eq', inter_eq_self_of_subset_left] at this
--   grw [(hT₀ i).subset_ground, restrict_ground_eq]




-- noncomputable def coverNumber' (M : Matroid α) (k : ℕ∞) :=
--     ⨅ (T : Set (Set α)) (_ : M.IsIndexedCover k (fun x : T ↦ x)), T.encard

-- lemma IsIndexedCover.coverNumber'_le {T : Set (Set α)} (hT : M.IsIndexedCover k (fun x : T ↦ x)) :


-- lemma IsIndexedCover.coverNumber'_le (h : M.IsIndexedCover k T) : M.coverNumber' k ≤ ENat.card ι := by
--   grw [coverNumber', iInf₂_le _ (i := range T)]
--   · grw [← image_univ, encard_image_le, encard_le_card]





-- end Indexed

-- def IsCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α)) : Prop := M.IsIndexedCover k (fun X : T ↦ X.1)

-- lemma IsCover.isIndexedCover (h : M.IsCover k T) : M.IsIndexedCover k (fun X : T ↦ X.1) := h

-- lemma IsCover.sUnion_eq (h : M.IsCover k T) : ⋃₀ T = M.E := by
--   rw [← IsIndexedCover.iUnion_eq h, sUnion_eq_iUnion]

-- lemma IsCover.eRk_le (h : M.IsCover k T) (hXT : X ∈ T) : M.eRk X ≤ k :=
--   IsIndexedCover.eRk_le h ⟨X, hXT⟩

-- lemma isCover_iff : M.IsCover k T ↔ ⋃₀ T = M.E ∧ ∀ F ∈ T, M.eRk F ≤ k :=
--   ⟨fun h ↦ ⟨h.sUnion_eq, fun _ ↦ h.eRk_le⟩,
--     fun h ↦ ⟨by rw [← sUnion_eq_iUnion, h.1], by simpa using h.2⟩⟩



-- -- @[mk_iff]
-- -- structure IsCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α)) : Prop where
-- --   sUnion_eq : ⋃₀ T = M.E
-- --   eRk_le : ∀ F ∈ T, M.eRk F ≤ k

-- lemma IsCover.subset_ground (h : M.IsCover k T) (hX : X ∈ T) : X ⊆ M.E := by
--   grw [← h.sUnion_eq, ← subset_sUnion_of_mem hX]

-- lemma IsCover.isCover_closure (h : M.IsCover k T) : M.IsCover k (M.closure '' T) := by
--   simp only [isCover_iff, sUnion_image, subset_antisymm_iff (b := M.E), iUnion_subset_iff,
--     M.closure_subset_ground, implies_true, true_and, mem_image, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂, eRk_closure_eq]
--   grw [h.sUnion_eq.symm.subset, sUnion_eq_biUnion]
--   exact ⟨biUnion_mono rfl.subset fun X hX ↦ M.subset_closure X (h.subset_ground hX),
--     fun _ ↦ h.eRk_le⟩

-- lemma IsCover.mono {k'} (h : M.IsCover k T) (hkk' : k ≤ k') : M.IsCover k' T :=
--   isCover_iff.2 ⟨h.sUnion_eq, fun _ hF ↦ (h.eRk_le hF).trans hkk'⟩

-- lemma ground_isCover (M : Matroid α) : M.IsCover M.eRank {M.E} := by
--   simp [isCover_iff]

-- -- lemma setOf_point_isCover (M : Matroid α) [M.RankPos] : M.IsCover 1 {P | M.IsPoint P} := by
-- --   refine ⟨subset_antisymm (sUnion_subset fun _ ↦ IsPoint.subset_ground) fun e he ↦ ?_,
-- --     by simp +contextual [mem_setOf_eq, IsPoint] ⟩
-- --   simp only [mem_sUnion, mem_setOf_eq]
-- --   obtain hl | hnl := M.isLoop_or_isNonloop e
-- --   · obtain ⟨f, hf⟩ := M.exists_isNonloop
-- --     exact ⟨_, hf.closure_isPoint, hl.mem_closure _⟩
-- --   exact ⟨_, hnl.closure_isPoint, mem_closure_of_mem _ (by simp) (by simpa)⟩

-- -- lemma setOf_point_IsCover [hM : M.Loopless] : M.IsCover 1 {P | M.IsPoint P} := by
-- --   obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
-- --   · obtain rfl : E = ∅ := by simpa using hM
-- --     constructor <;> simp [IsPoint]
-- --   exact M.setOf_point_isCover


-- -- lemma IsCover.contract (h : (M ／ X).IsCover k T) (hX : X ⊆ M.E) (hXN : (M ／ X).Nonempty) :
-- --     M.IsCover (k + M.eRk X) ((· ∪ X) '' T) := by
-- --   suffices ∀ F ∈ T, M.eRk (F ∪ X) ≤ k + M.eRk X by
-- --     simpa [isCover_iff, ← biUnion_distrib_union _ h.nonempty, ← sUnion_eq_biUnion, h.sUnion_eq, hX]
-- --   exact fun F hFT ↦ by grw [← h.eRk_le F hFT, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq]

-- /-- The number of sets of rank at most `k` needed to cover a matroid `M`. -/
-- noncomputable def coverNumber (M : Matroid α) (k : ℕ∞) : ℕ∞ := sInf (encard '' {T | M.IsCover k T})

-- lemma coverNumber_eq_iInf (M : Matroid α) (k : ℕ∞) :
--     M.coverNumber k = ⨅ T ∈ {T | M.IsCover k T}, T.encard := by
--   exact sInf_image

-- lemma IsCover.coverNumber_le (h : M.IsCover k T) : M.coverNumber k ≤ T.encard :=
--   sInf_le <| by grind

-- @[simp]
-- lemma coverNumber_emptyOn (α : Type*) (k : ℕ∞) : (emptyOn α).coverNumber k = 0 := by
--   simp [coverNumber, ENat.sInf_eq_zero, isCover_iff]

-- lemma coverNumber_pos (M : Matroid α) [M.Nonempty] (k : ℕ∞) : 0 < M.coverNumber k := by
--   suffices ¬ M.IsCover k ∅ by simpa [pos_iff_ne_zero, coverNumber, ENat.sInf_eq_zero]
--   exact fun h ↦ M.ground_nonempty.ne_empty <| by simpa using h.sUnion_eq.symm

-- @[simp]
-- lemma coverNumber_top (M : Matroid α) [M.Nonempty] : M.coverNumber ⊤ = 1 := by
--   nth_grw 1 [le_antisymm_iff, ENat.one_le_iff_ne_zero,
--     (M.ground_isCover.mono (by simp)).coverNumber_le, encard_singleton, and_iff_right rfl.le]
--   exact (M.coverNumber_pos _).ne.symm

-- lemma coverNumber_le {k k' : ℕ∞} (M : Matroid α) (hk : k ≤ k') : M.coverNumber k' ≤ M.coverNumber k
--     := by
--   refine ENat.forall_natCast_le_iff_le.mp ?_
--   intro a hak
--   unfold coverNumber at hak
--   simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂] at hak
--   unfold coverNumber
--   simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂]
--   exact fun T hT ↦ (hak T (hT.mono hk))

-- lemma coverNumber_contract_one {a : ℕ∞} (he : e ∈ M.E) (hel : M.IsNonloop e)
--     (heN : (M／ {e}).Nonempty) :
--     M.coverNumber (a + 1) ≤ (M ／ {e}).coverNumber a := by
--   refine ENat.forall_natCast_le_iff_le.mp ?_
--   intro b hb
--   unfold coverNumber at hb
--   simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂] at hb
--   unfold coverNumber
--   simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂]
--   intro T hT
--   have h1 := hT.contract (singleton_subset_iff.mpr he ) heN
--   rw[IsNonloop.eRk_eq hel ] at h1
--   have h2 := hb ((· ∪ {e}) '' T) h1
--   grw[encard_image_le (fun x ↦ x ∪ {e}) T ] at h2
--   exact h2

-- -- lemma exists_cover (M : Matroid α) {k : ℕ∞} (hk : 1 ≤ k) :
-- --     ∃ T, M.IsCover k T ∧ T.encard = M.coverNumber k := by
-- --   simpa using csInf_mem <| (M.setOf_cover_nonempty hk).image encard



-- lemma coverNumber_contract {a : ℕ∞} (hX : X ⊆ M.E) :
--     M.coverNumber (a + M.eRk X) ≤ (M ／ X).coverNumber a := by
--   --Mathieu, do you want to do this one?
--   sorry


-- lemma coverNumber_lt {k l : ℕ∞} (hlt : M.coverNumber k < l) : ∃ T, M.IsCover k T ∧ T.encard < l :=
--     by
-- obtain ⟨t, ⟨T, hT, hT1 ⟩, htl ⟩ := sInf_lt_iff.1 hlt
-- refine ⟨T, ⟨hT , (lt_of_eq_of_lt hT1 htl ) ⟩⟩


    --(hcovNum : M.coverNumber a ≤ )

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

-- theorem kung_bound [RankFinite M]
--     (hNoUnif : NoUniformMinor M (l + 2) 2) :
--     --(hNoUnif : ∀ N : Matroid α, N ≤m M → N = (unifOn (N.E ) 2 ) → N.E.encard < l + 2) :
--     --(hNoUnif : ¬ Nonempty ((unifOn (Set.univ : Set (Fin (l + 2))) 2) ≤i M)) :
--     coverNumber M 1 ≤ ∑' i : {i : ℕ // i < M.eRank}, l^i.1  := by
--     --M.simplification.E.encard ≤ (l ^ (M.rank ) - 1)/(l - 1) := by
--   suffices hn : ∀ n : ℕ, M.rank = n → coverNumber M 1 ≤  ∑' i : {i : ℕ // i < n}, l^i.1
--   ·
--     sorry
--   intro n hn
--   sorry
--   -- I think we just need to use coverNumber_contract_one


-- def kung_infinite (hM : M.NoUniformMinor 2 (l + 2)) :
--     M.simplification.E.encard ≤ ∑' i : {i : ℕ // i < M.eRank}, l ^ i.1 := by
--   sorry
