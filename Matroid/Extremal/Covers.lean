import Matroid.Minor.Rank
import Matroid.Uniform
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
namespace Matroid

section General

@[mk_iff]
structure IsCover' (M : Matroid α) (P : Matroid α → Set α → Prop) (T : Set (Set α)) : Prop where
  sUnion_eq : ⋃₀ T = M.E
  pProp : ∀ F ∈ T, P M F

lemma IsCover'.subset_ground (h : M.IsCover' P T) (hX : X ∈ T) : X ⊆ M.E := by
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
    ∃ T, M.IsCover' P T

lemma Cover_NE :
    M.hasCover_with P ↔ {T | M.IsCover' P T}.Nonempty := by
  refine ⟨ fun a ↦ Nonempty.mono (fun ⦃a⦄ a_1 ↦ a_1) a , fun a ↦ ((fun a_1 ↦ a) ∘ fun a ↦ α) α ⟩

-- lemma isCover'_iff : M.IsCover P T ↔ ⋃₀ T = M.E ∧ ∀ F ∈ T, P F :=
--   ⟨fun h ↦ ⟨h.sUnion_eq, fun _ ↦ h.eRk_le⟩,
--     fun h ↦ ⟨by rw [← sUnion_eq_iUnion, h.1], by simpa using h.2⟩⟩

lemma IsCover'.nonempty [M.Nonempty] (h : M.IsCover' P T) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [isCover'_iff, eq_comm, M.ground_nonempty.ne_empty] at h

-- -- almost follows from `setOf_point_isCover` - handle the rank-zero case.
-- lemma setOf_cover_nonempty (M : Matroid α) : {T | M.IsCover' P T}.Nonempty := by
--   obtain ⟨E, rfl⟩ | rp := M.exists_eq_loopyOn_or_rankPos
--   · sorry
--   exact ⟨_, M.setOf_point_isCover.mono hk⟩

noncomputable def coverNumber' (M : Matroid α) (P : Matroid α → Set α → Prop) : ℕ∞ :=
    sInf (encard '' {T | M.IsCover' P T})

lemma coverNumber'_eq_iInf (M : Matroid α) (P : Matroid α → Set α → Prop) :
    M.coverNumber' P = ⨅ T ∈ {T | M.IsCover' P T}, T.encard := by
  exact sInf_image

lemma IsCover'.coverNumber_le {T} (h : M.IsCover' P T) : M.coverNumber' P ≤ T.encard := by
  grw [coverNumber'_eq_iInf]
  exact biInf_le encard h

lemma exists_mincover'_NE {M : Matroid α} {P : Matroid α → Set α → Prop}
    (hn : {T | M.IsCover' P T}.Nonempty) :
    ∃ T, M.IsCover' P T ∧ T.encard = M.coverNumber' P := by
  simpa using csInf_mem <| hn.image encard

lemma exists_min_cover' {M : Matroid α} {P : Matroid α → Set α → Prop} (hP : M.hasCover_with P) :
    ∃ T, M.IsCover' P T ∧ T.encard = M.coverNumber' P := by
  simpa using csInf_mem <| (Cover_NE.1 hP ).image encard

lemma exists_cover (M : Matroid α) (P : Matroid α → Set α → Prop) :
    M.coverNumber' P = ⊤ ∨ ∃ T, M.IsCover' P T ∧ T.encard = M.coverNumber' P := by
  obtain h0 | h := {T | M.IsCover' P T}.eq_empty_or_nonempty
  · simp [coverNumber'_eq_iInf, h0]
  right
  simpa using csInf_mem <| h.image encard

lemma IsCover'.cover_fun {M : Matroid α} {P' : Matroid α → Set α → Prop} (hP' : IsMRProp P')
    (hcover : M.IsCover' P T)
    (f : Set α → Set (Set α) )
    (hfun : ∀ X ∈ T, (M ↾ X).IsCover' P' (f X)) :
    M.IsCover' P' ( ⋃ X ∈ T, f X ):= by
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


lemma IsCover'.cover_typset {P' : Matroid α → Set α → Prop} (hP' : IsMRProp P' )
    (hcover : M.IsCover' P T )
    (f : T → Set (Set α) )
    (hfun : ∀ X : T, (M ↾ X.1).IsCover' P' (f X)) :
    M.IsCover' P' (⋃ X : T, f X ):= by
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

lemma coverNumber_cover_of_covers' {P' : Matroid α → Set α → Prop} (hcover : M.IsCover' P T)
    (hP' : IsMRProp P') :
    M.coverNumber' P' ≤ ∑' X : T, (M ↾ X.1).coverNumber' P' := by
  obtain (h0 | h1) := exists_or_forall_not (fun X : T ↦ (M ↾ X).coverNumber' P' = ⊤)
  · simp [ENat.tsum_eq_top_of_eq_top h0]
  have hf : ∀ X : T, ∃ XT, (M ↾ X.1).IsCover' P' XT ∧
    XT.encard = (M ↾ X.1).coverNumber' P' := by
    intro X
    obtain (h | ⟨XT, hXres, hencard⟩) := (M ↾ X).exists_cover P'
    · simp [h1 _ h]
    exact ⟨XT, hXres, hencard⟩
  choose f hfunco hfunca using hf
  have hcover := IsCover'.cover_typset hP' hcover f hfunco
  grw [hcover.coverNumber_le, ENat.encard_iUnion_le_tsum_encard, tsum_congr hfunca]

lemma coverNumber_cover_of_covers_bound {P' : Matroid α → Set α → Prop} {k : ℕ∞}
    (hcover : M.IsCover' P T) (hP' : IsMRProp P')
    (hflat : ∀ F, P M F → (M ↾ F).coverNumber' P' ≤ k) :
    M.coverNumber' P' ≤ (T.encard) * k := by
  grw [coverNumber_cover_of_covers' hcover, ENat.tsum_le_tsum (g := fun _ ↦ k),
    ENat.tsum_subtype_const, mul_comm]
  intro F
  simp [hflat _ <| hcover.pProp F F.2 ]
  exact hP'
  --Ask about notation

--Minor preserved under f
--(f : Set α → Matroid α → (Set α → Prop))
def IsMUProp (P : Matroid α → Set α → Prop) (X : Set α ) (P' : Matroid α → Set α → Prop): Prop :=
    --∀ X : Set α,
    --∃ P' : Matroid α → Set α → Prop,
    ∀ M : Matroid α,
    ∀ Y : Set α, P (M ／ X) Y → P' M Y

--P ' = k + M.eRk X for rank
lemma IsCover'.contract (h : (M ／ X).IsCover' P T)
    (hX : X ⊆ M.E) (hXN : (M ／ X).Nonempty)
    (hPP' : ∀ Y : Set α, P (M ／ X) Y → P' M ( Y ∪ X) ) :
    M.IsCover' P' ((· ∪ X) '' T) := by
  suffices hi : ∀ F ∈ T, P (M ／ X) F by
    simp only [isCover'_iff, sUnion_image, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, ← biUnion_distrib_union _ h.nonempty, ← sUnion_eq_biUnion,
      h.sUnion_eq, contract_ground, diff_union_self, union_eq_left, hX, true_and ]
    exact fun F hFT ↦ (((fun a ↦ (hPP' F (hi F hFT))) ∘ T) X )
  exact fun F hFT ↦ h.pProp F hFT


--Close under closure
def IsCCProp (P : Matroid α → Set α → Prop) : Prop :=
    ∀ M : Matroid α, ∀ F : Set α, P M F → P M (M.closure F)

lemma IsCover'.isCover_closure (hP : IsCCProp P) (h : M.IsCover' P T) :
    M.IsCover' P (M.closure '' T) := by
  simp only [isCover'_iff, sUnion_image, subset_antisymm_iff (b := M.E), iUnion_subset_iff,
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
    M.coverNumber' P ≤ M.E.encard := by
  have hcover : M.IsCover' P (singleton '' M.E) := by
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
  grw [hcover.coverNumber_le ]
  set Sing : Set (Set α ) := { singleton e | e ∈ M.E} with hs
  exact encard_image_le singleton M.E


lemma IsCover'.mono_prop (h : M.IsCover' P T) (hPP' : ∀ X ∈ T, P M X → P' M X) : M.IsCover' P' T :=
  (M.isCover'_iff P' T).2 ⟨h.sUnion_eq, fun F hF ↦ hPP' F hF (h.pProp F hF)⟩


end General

section Rank

-- lemma RankProp_IsCCProp (α) (k : ℕ∞) : IsCCProp (RankProp α k) := by
--   intro M F hF
--   unfold RankProp
--   rw[(eRk_closure_eq M F)]
--   exact le_of_eq_of_le rfl hF
-- lemma RankPropIsMUProp {k : ℕ∞} : IsMUProp (RankProp α k) (fun M X Y ↦ (M.eRk Y ≤ k + M.eRk X)) := by
--     --use fun M X Y ↦ (M.eRk Y ≤ k + M.eRk X)
--     intro M X Y hXY
--     unfold RankProp at hXY
--     sorry

def IsRankCover (M : Matroid α) (k : ℕ∞) (T : Set (Set α )) : Prop :=
    M.IsCover' (fun M X ↦ M.eRk X ≤ k) T

lemma IsRankCover_iff_isCover' (M : Matroid α) (k : ℕ∞) (T : Set (Set α )) :
    M.IsRankCover k T ↔ M.IsCover' (fun M X ↦ M.eRk X ≤ k ) T := Iff.rfl

lemma IsRankCover_iff (M : Matroid α) (k : ℕ∞) (T : Set (Set α )) :
    M.IsRankCover k T ↔ ⋃₀ T = M.E ∧ (∀ F ∈ T, M.eRk F ≤ k) := by
  sorry
  --Mathieu

lemma setOf_point_IsRankCover (M : Matroid α) [M.RankPos] : M.IsRankCover 1 {P | M.IsPoint P} := by
  refine ⟨subset_antisymm (sUnion_subset fun _ ↦ IsPoint.subset_ground) fun e he ↦ ?_,
    by simp +contextual [mem_setOf_eq, IsPoint] ⟩
  simp only [mem_sUnion, mem_setOf_eq]
  obtain hl | hnl := M.isLoop_or_isNonloop e
  · obtain ⟨f, hf⟩ := M.exists_isNonloop
    exact ⟨_, hf.closure_isPoint, hl.mem_closure _⟩
  exact ⟨_, hnl.closure_isPoint, mem_closure_of_mem _ (by simp) (by simpa)⟩

lemma setOf_point_isCover' [hM : M.Loopless] : M.IsRankCover 1 {P | M.IsPoint P} := by
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · obtain rfl : E = ∅ := by simpa using hM
    constructor <;> simp [IsPoint]
  exact M.setOf_point_IsRankCover

lemma IsRankCover.nonempty [M.Nonempty] (h : M.IsRankCover k T) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [IsRankCover_iff, eq_comm, M.ground_nonempty.ne_empty] at h

-- almost follows from `setOf_point_isCover` - handle the rank-zero case.
-- lemma setOf_cover_nonempty (M : Matroid α) (hk : 1 ≤ k) : {T | M.IsCover k T}.Nonempty := by
--   obtain ⟨E, rfl⟩ | rp := M.exists_eq_loopyOn_or_rankPos
--   · sorry
--   exact ⟨_, M.setOf_point_isCover.mono hk⟩

--lemma coverNumber_toFlats

lemma IsRankCover.contract (h : (M ／ X).IsRankCover k T) (hX : X ⊆ M.E)
    (hXN : (M ／ X).Nonempty) :
    M.IsRankCover (k + M.eRk X) ((· ∪ X) '' T) := by
  suffices ∀ F ∈ T, M.eRk (F ∪ X) ≤ k + M.eRk X by
    simpa [IsRankCover_iff, ← biUnion_distrib_union _ h.nonempty, ← sUnion_eq_biUnion, h.sUnion_eq, hX]
  exact fun F hFT ↦ by grw [← h.pProp F hFT, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq]

lemma coverNumber_contract_one {a : ℕ∞} (he : e ∈ M.E) (hel : M.IsNonloop e)
    (heN : (M／ {e}).Nonempty) :
    M.coverNumber' (fun M X ↦ M.eRk X ≤ (a + 1)) ≤ (M ／ {e}).coverNumber' (fun M X ↦ M.eRk X ≤ a)
    := by
  refine ENat.forall_natCast_le_iff_le.mp ?_
  intro b hb
  unfold coverNumber' at hb
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hb
  unfold coverNumber'
  simp only [le_sInf_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro T hT
  rw[←IsRankCover_iff_isCover'] at hT
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
  have := (Nat.cast_inj (R := ℕ∞)).2 <| X'.card_powersetCard a
  convert (Nat.cast_inj (R := ℕ∞)).2 <| X'.card_powersetCard a
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
    simp_rw [← Nat.cast_inj (R := ℕ∞), ← hSa, ← Finite.encard_eq_coe_toFinset_card]
    simpa
  rw [← Nat.cast_inj (R := ℕ∞), ← hX, eq_comm, hXfin.encard_eq_coe_toFinset_card]

lemma cover_foo {a : ℕ} (hr : M.eRank ≤ a + 1)
    (h : Maximal (fun Y ↦ Y ⊆ M.E ∧ (M ↾ Y).IsFiniteRankUniform (a + 1) Y.encard) X) :
    M.IsRankCover a (M.closure '' {K | K ⊆ X ∧ K.encard = a}) := by
  refine ⟨?_, ?_⟩
  · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
    · simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp]
      grind
    obtain ⟨E, hEX, hEunif⟩ := h.prop.2.exists_eq_unifOn
    obtain rfl : X = E := congr_arg Matroid.E hEunif
    by_contra! hcon
    simp only [sUnion_image, mem_setOf_eq, mem_iUnion, exists_prop, not_exists, not_and,
      and_imp] at hcon
    have hcon' (Z) (hZ : Z ⊆ X) (hZa : Z.encard ≤ a) : e ∉ M.closure Z := by
      have haX : a ≤ X.encard := by
        grw [← M.restrict_ground_eq (R := X), ← eRank_le_encard_ground, h.prop.2.eRank_eq]
        simp
      obtain ⟨W, hZW, hWZ, hW⟩ := exists_superset_subset_encard_eq hZ hZa haX
      exact notMem_subset (M.closure_subset_closure hZW) (hcon W hWZ hW)
    have heX : e ∉ X := sorry
    have hwin := h.not_prop_of_ssuperset (t := insert e X) (by grind)
    rw [insert_subset_iff, and_iff_right he, and_iff_right h.prop.1] at hwin
    apply hwin
    suffices aux : (M ↾ insert e X) = unifOn (insert e X) (a + 1) by
      rw [aux]
      apply unifOn_isFiniteRank_uniform
      grw [h.prop.2.le, ← subset_insert]
    refine ext_indep rfl fun I (hI : I ⊆ insert e X) ↦ ?_
    simp only [restrict_indep_iff, hI, and_true, unifOn_indep_iff, Nat.cast_add, Nat.cast_one]
    refine ⟨fun hIi ↦ by grw [hIi.encard_le_eRank, hr], fun hcard ↦ ?_⟩
    have hI₀ : M.Indep (I \ {e}) := by
      have hrestr := (M.restrict_indep_iff (R := X) (I := I \ {e})).1
      nth_grw 1 [hEunif, unifOn_indep_iff, diff_subset] at hrestr
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

lemma baseCase {a b : ℕ} (ha : 1 ≤ a) (hM : NoUniformMinor M (a + 1) (b + 1)) (hr : M.eRank = a + 1) :
    M.coverNumber' (fun M X ↦ M.eRk X ≤ a) ≤ Nat.choose b a := by
  have : M.RankFinite := M.eRank_ne_top_iff.mp (ENat.ne_top_iff_exists.2
      (Exists.intro ((fun x1 x2 ↦ x1 + x2) a 1) (hr.symm)))
  by_contra! hcon
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hne : {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1) X.encard}.Nonempty := by
    refine ⟨B, (IsBase.subset_ground hB), rfl, ?_, ?_⟩
    · rwa [eRank_restrict, hB.eRk_eq_eRank]
    rw [hB.indep.restrict_eq_freeOn]
    exact freeOn_uniform B
  have hYbound : ∀ Y, Y ∈ {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1) X.encard}
      → Y.encard < b + 1 := by
    intro X hX
    by_contra hc
    simp only [not_lt] at hc
    simp only [mem_setOf_eq] at hX
    exact hc.not_gt <| hM.lt_of_isoMinor (N := M ↾ X) (b' := X.encard)
      (restrict_isRestriction _ _ hX.1).isMinor.isoMinor hX.2
    -- have := hM.lt_of_isoMinor
    -- have := hX.2.
    -- Mathieu, try this exact. I know it's solved but I think it's a fun one

  have hcard : (encard '' {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1) X.encard}).Finite := by
    refine ENat.finite_of_sSup_lt_top ?_
    refine lt_of_le_of_lt ?_ <| WithTop.natCast_lt_top (b + 1)
    simp only [sSup_le_iff, mem_image, mem_setOf_eq, forall_exists_index, and_imp]
    intro k A hAE h hen
    rw[←hen ]
    exact Std.le_of_lt (hYbound A ⟨hAE, h ⟩ )
  obtain ⟨X, hX⟩ := Finite.exists_maximalFor' encard _ hcard hne
  have hunif := hX.prop.2.isUniform
  have hXb : X.encard < b + 1 := hYbound X hX.prop
  have hXrank := hX.prop.2.2
  set Subsets : Set (Set α) := { Y | Y ⊆ X ∧ Y.encard = a} with h_sub
  have hiC : M.IsCover' (fun M X ↦ M.eRk X ≤ a) (M.closure '' Subsets) := by
    refine ⟨?_, ?_ ⟩
    · refine ext ?_
      intro e
      refine ⟨ ?_, ?_ ⟩
      · intro ⟨Y, ⟨Y', hY', h ⟩, heY ⟩
        rw[←h] at heY
        exact mem_of_subset_of_mem (LE.le.subset (closure_subset_ground M Y' ) ) heY
      intro heF
      by_contra hc
      have hMeq : (M ↾ (insert e X)).IsFiniteRankUniform (a + 1) (insert e X).encard := by
        have hindep : ∀ Y ⊆ X, Y.encard ≤ a → M.eRk Y = Y.encard := by
          intro Y hY hYr
          have hIndepR : (M ↾ X).Indep Y := by
            apply hunif.indep_of_nonspanning
            by_contra hc
            have h1 : (M ↾ X).eRank ≤ (M ↾ X).eRk Y :=
              (spanning_iff_eRk_le hY).mp ((not_nonspanning_iff hY).mp hc )
            grw[hXrank, eRk_le_encard (M ↾ X) Y , hYr ] at h1
            simp only [Nat.cast_add, Nat.cast_one, ENat.add_le_left_iff, ENat.coe_ne_top,
              one_ne_zero, or_self] at h1
          exact indep_iff_eRk_eq_encard.mp hIndepR.of_restrict
        have hRankin : (M ↾ insert e X).eRank = (a + 1) := by
          simp only [eRank_restrict]
          simp only [eRank_restrict, Nat.cast_add, Nat.cast_one] at hXrank
          have : M.eRk X ≤ M.eRk (insert e X) := eRk_subset_le M (subset_insert e X )
          rw[hXrank] at this
          have : M.eRk (insert e X) ≤ M.eRank := eRk_le_eRank M (insert e X)
          rw [hr] at this
          grind
        refine ⟨?_, hRankin, ?_⟩
        · simp only [restrict_ground_eq]
        intro I hI
        simp only [restrict_ground_eq] at hI
        obtain h0 | ⟨h11, h12⟩ := subset_insert_iff.1 hI
        · obtain h1 | h2 := (hunif.indep_or_spanning I )
          · exact Or.symm (Or.inr ((h1.of_restrict).indep_restrict_of_subset hI  ))
          right
          apply (spanning_iff_eRk_le hI).2
          rw [hRankin,restrict_eRk_eq _ hI, ←restrict_eRk_eq _ h0  ]
          exact le_of_eq_of_le (id (Eq.symm hXrank)) ((spanning_iff_eRk_le h0).mp h2 )
        obtain hlt | heq := lt_or_eq_of_le (le_of_le_of_eq (eRk_le_eRank (M ↾ X) (I \ {e}) ) hXrank)
        · left
          have hlea : (I \ {e}).encard ≤ a := by
            have hIeindep : (M ↾ X).Indep (I \ {e}) := by
              apply hunif.indep_of_nonspanning
              by_contra hc
              grw[←hXrank, ((spanning_iff_eRk_le h12).mp ((not_nonspanning_iff h12).mp hc ))] at hlt
              simp only [restrict_eRk_eq', lt_self_iff_false] at hlt
            rw[←indep_iff_eRk_eq_encard.1 hIeindep ]
            exact ENat.lt_coe_add_one_iff.mp hlt
          have ⟨J, hJI, hJX, hJen ⟩ : ∃ J, (I \ {e}) ⊆ J ∧ J ⊆ X ∧ J.encard = a := by
            have hh : a ≤ X.encard := by
              simp only [eRank_restrict, Nat.cast_add, Nat.cast_one] at hXrank
              grw[←eRk_le_encard M X, hXrank ]
              exact le_self_add
            exact exists_superset_subset_encard_eq h12 hlea hh
          simp only [sUnion_image, mem_iUnion, exists_prop, not_exists, not_and] at hc
          have hei : M.Indep ({e}) := by
            refine IsNonloop.indep ?_
            by_contra hcc
            exact (hc J ((mem_sep hJX hJen )) ) ((M.not_isNonloop_iff.1 hcc).mem_closure J)
          have hJeInd : M.Indep (J ∪ {e}) := by
            apply (Indep.union_indep_iff_forall_notMem_closure_right
              (Indep.of_restrict (Indep.indep_restrict_of_subset (indep_iff_eRk_eq_encard.mpr
              (hindep J hJX (ge_of_eq (id (Eq.symm hJen)))) ) hJX )) hei).2
            simp only [mem_diff, mem_singleton_iff, and_imp, forall_eq, sdiff_self, bot_eq_empty,
              union_empty]
            intro _
            exact hc J (mem_sep hJX hJen )
          have hIind : I ⊆ J ∪ {e} := by grind
          exact (Indep.subset hJeInd hIind ).indep_restrict_of_subset hI
        right
        apply (spanning_iff_eRk_le hI).2
        rw[hRankin, restrict_eRk_eq M hI]
        rw[restrict_eRk_eq M h12] at heq
        exact le_of_eq_of_le (Eq.symm heq) (eRk_subset_le M (diff_subset ) )
      --insert_subset heF ( hX.prop.1)
      --have hh : (insert e X) ∈ {X | (M ↾ X).IsFiniteRankUniform (a + 1) X.encard} := by exact mem_setOf.mpr hMeq
      --have := hX.eq_of_ge hh (encard_le_encard (subset_insert e X))
      have heX : e ∈ X := by
        by_contra hc
        have : X.encard < (insert e X).encard := Finite.encard_lt_encard
          (Set.encard_le_coe_iff.1 (ENat.lt_coe_add_one_iff.mp hXb )).1 (ssubset_insert hc )
        rw[hX.eq_of_ge (⟨insert_subset heF ( hX.prop.1), mem_setOf.mpr hMeq⟩ )
          (encard_le_encard (subset_insert e X))] at this
        exact (lt_self_iff_false X.encard).mp this
      have ⟨ J, hJ, hhJ1, hhJ2 ⟩ : ∃ J, e ∈ J ∧ J ⊆ X ∧ J.encard = a := by
        have hh : a ≤ X.encard := by
          simp only [eRank_restrict, Nat.cast_add, Nat.cast_one] at hXrank
          grw[←eRk_le_encard M X, hXrank ]
          exact le_self_add
        have ⟨ J, hJ, hhJ1, hhJ2 ⟩ := exists_superset_subset_encard_eq
          (singleton_subset_iff.mpr heX ) ?_ hh
        · refine ⟨J, (mem_of_subset_of_mem hJ rfl ), hhJ1, hhJ2 ⟩
        simp only [encard_singleton, Nat.one_le_cast, ha]
      have : e ∈ ⋃₀ (M.closure '' Subsets) := by
        simp only [sUnion_image, mem_iUnion, exists_prop]
        refine ⟨J, mem_sep hhJ1 hhJ2, mem_closure_of_mem' M hJ heF ⟩
      exact hc this
    intro F ⟨Y ,hY, h ⟩
    grw[←h, eRk_closure_eq M Y, eRk_le_encard M Y ]
    exact ge_of_eq (Eq.symm hY.2)
  obtain ⟨x, hx ⟩ := ENat.ne_top_iff_exists.1 (LT.lt.ne_top hXb )
  have hrw : (x).choose a ≤ (b.choose a) := by
    rw[←hx] at hXb
    exact Nat.choose_le_choose a (Nat.le_of_lt_succ (ENat.coe_lt_coe.mp hXb ))
  grw [hiC.coverNumber_le, Set.encard_image_le, h_sub, (set_to_binom_number) X hx.symm, hrw] at hcon
  simp only [lt_self_iff_false] at hcon



lemma coverNumber_Bound [M.RankFinite] {a b : ℕ} (ha : 1 ≤ a) (hb : a ≤ b)
    (hM : NoUniformMinor M ( a + 1 ) (b + 1)) :
    M.coverNumber' (fun M X ↦ M.eRk X ≤ a) ≤ (Nat.choose b a)^(M.eRank - a) := by

  suffices hn : ∀ n : ℕ, M.eRank = n + a + 1 →
      M.coverNumber' (fun M X ↦ M.eRk X ≤ a) ≤ (Nat.choose b a)^(n + 1 )
  ·
    sorry
  intro n hn
  induction n generalizing M with
  | zero => sorry
  | succ n IH => sorry


end Rank














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

-- lemma setOf_point_isCover (M : Matroid α) [M.RankPos] : M.IsCover 1 {P | M.IsPoint P} := by
--   refine ⟨subset_antisymm (sUnion_subset fun _ ↦ IsPoint.subset_ground) fun e he ↦ ?_,
--     by simp +contextual [mem_setOf_eq, IsPoint] ⟩
--   simp only [mem_sUnion, mem_setOf_eq]
--   obtain hl | hnl := M.isLoop_or_isNonloop e
--   · obtain ⟨f, hf⟩ := M.exists_isNonloop
--     exact ⟨_, hf.closure_isPoint, hl.mem_closure _⟩
--   exact ⟨_, hnl.closure_isPoint, mem_closure_of_mem _ (by simp) (by simpa)⟩

-- lemma setOf_point_isCover' [hM : M.Loopless] : M.IsCover 1 {P | M.IsPoint P} := by
--   obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
--   · obtain rfl : E = ∅ := by simpa using hM
--     constructor <;> simp [IsPoint]
--   exact M.setOf_point_isCover


-- lemma IsCover.contract (h : (M ／ X).IsCover k T) (hX : X ⊆ M.E) (hXN : (M ／ X).Nonempty) :
--     M.IsCover (k + M.eRk X) ((· ∪ X) '' T) := by
--   suffices ∀ F ∈ T, M.eRk (F ∪ X) ≤ k + M.eRk X by
--     simpa [isCover_iff, ← biUnion_distrib_union _ h.nonempty, ← sUnion_eq_biUnion, h.sUnion_eq, hX]
--   exact fun F hFT ↦ by grw [← h.eRk_le F hFT, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq]

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
  exact fun T hT ↦ (hak T (hT.mono hk))

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
