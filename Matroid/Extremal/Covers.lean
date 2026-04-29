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
import Matroid.Uniform.Basic
import Matroid.Uniform.Paving
import Matroid.Uniform.Finite
import Matroid.Uniform.Minor


variable {α : Type*} {M N M' : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C D K : Set α}
  {e f : α} {l r : ℕ} {a k : ℕ∞} {T : Set (Set α)} {ι : Type*} {i j : ι}
  {P P' Q : Set α → Prop}

open Set

section General

/-- `T.IsCover X P` means that `T` is a collection of sets with union `X`,
each satisfying property `P`.-/
@[mk_iff]
structure Set.IsCover (T : Set (Set α)) (X : Set α) (P : Set α → Prop) : Prop where
  sUnion_eq : ⋃₀ T = X
  pProp : ∀ F ∈ T, P F

lemma Set.IsCover.subset (h : T.IsCover X P) (hY : Y ∈ T) : Y ⊆ X := by
  grw [← h.sUnion_eq, ← subset_sUnion_of_mem hY]

def Set.HasCover (X : Set α) (P : Set α → Prop) : Prop :=
    ∃ T, IsCover T X P

lemma hasCover_iff {X : Set α} : X.HasCover P ↔ {T | IsCover T X P}.Nonempty := Iff.rfl

lemma Set.IsCover.nonempty (h : T.IsCover X P) (hX : X.Nonempty) : T.Nonempty := by
  rw [nonempty_iff_empty_ne]
  rintro rfl
  simp [isCover_iff, eq_comm] at h
  simp_all only [Set.not_nonempty_empty]

-- lemma IsCover.one_le (h : T.IsCover X P) (hX : X.Nonempty) : T.Nonempty := by
--   --simp only [one_le_encard_iff_nonempty]
--   exact h.nonempty hX

lemma isCover_iff_isCover_subset : T.IsCover X P ↔ T.IsCover X (fun A ↦ P A ∧ A ⊆ X) := by
  rw [isCover_iff, isCover_iff]
  refine and_congr_right fun hTX => ?_
  refine ⟨?_, ?_⟩
  · intro hAP F hF
    have hFX : F ⊆ X := by
      rw [← hTX]
      exact subset_sUnion_of_mem hF
    exact ⟨hAP F hF, hFX⟩
  · intro hAPsub F hF
    rcases hAPsub F hF with ⟨hPF, hFX⟩
    exact hPF

/-- The covers of each element of a cover define a cover.
In this case we use typesets to give the cover of covers-/
lemma Set.IsCover.biUnion' {E : Set α}
    (hcover : T.IsCover E P)
    (f : T → Set (Set α))
    (hfun : ∀ X : T, (f X).IsCover X.1 P') :
    (⋃ X : T, f X).IsCover E P' := by
  refine ⟨ ?_, ?_ ⟩
  · rw[←hcover.sUnion_eq]
    refine ext ?_
    intro e
    refine ⟨ ?_, ?_ ⟩
    · intro he
      simp only [iUnion_coe_set, mem_sUnion, mem_iUnion] at he
      obtain ⟨T', ⟨ X, ⟨hX, hT'X ⟩ ⟩, hee ⟩ := he
      simp only [mem_sUnion]
      refine ⟨X, ⟨hX, (mem_of_subset_of_mem (((hfun ⟨X, hX⟩).subset hT'X)) hee) ⟩⟩
    intro he
    simp only [mem_sUnion] at he
    obtain ⟨X, hXT, heX⟩ := he
    simp only [iUnion_coe_set, mem_sUnion, mem_iUnion]
    have h1 := (hfun ⟨X, hXT⟩).sUnion_eq
    simp only at h1
    rw[←h1] at heX
    simp only [mem_sUnion] at heX
    obtain ⟨X', hX', heX' ⟩ := heX
    refine ⟨ X', ⟨⟨X, ⟨hXT, hX'⟩ ⟩, heX'⟩ ⟩
  intro F hF
  simp only [iUnion_coe_set, mem_iUnion] at hF
  obtain ⟨X, hXT, hF⟩ := hF
  exact (hfun ⟨X, hXT⟩).pProp F hF

/-- The covers of each element of a cover define a cover. -/
lemma Set.IsCover.biUnion {P' :  Set α → Prop}
    (hcover : T.IsCover Y P)
    (f : Set α → Set (Set α))
    (hfun : ∀ X ∈ T, (f X).IsCover X P') :
    (⋃ X ∈ T, f X).IsCover Y P' := by
  refine ⟨ ?_, ?_ ⟩
  · rw[←hcover.sUnion_eq]
    refine ext ?_
    intro e
    refine ⟨ ?_, ?_ ⟩
    · intro he
      simp only [ mem_sUnion, mem_iUnion] at he
      obtain ⟨T', ⟨ X, ⟨hX, hT'X ⟩ ⟩, hee ⟩ := he
      simp only [mem_sUnion]
      refine ⟨ X ,⟨ hX , mem_of_subset_of_mem ((hfun X hX).subset hT'X) hee  ⟩ ⟩
    intro he
    simp only [mem_sUnion] at he
    obtain ⟨X, hXT, heX⟩ := he
    simp only [mem_sUnion, mem_iUnion]
    have h1 := (hfun X hXT).sUnion_eq
    rw[←(hfun X hXT).sUnion_eq] at heX
    simp only [mem_sUnion] at heX
    obtain ⟨X', hX', heX' ⟩ := heX
    refine ⟨ X', ⟨⟨X, ⟨hXT, hX'⟩ ⟩, heX'⟩ ⟩
  intro F hF
  simp only [ mem_iUnion] at hF
  obtain ⟨X, hXT, hF⟩ := hF
  exact (hfun X hXT).pProp F hF

lemma IsCover.mono_prop (h : T.IsCover Y P) (hPP' : ∀ X ∈ T, P X → P' X) : T.IsCover Y P' :=
  (T.isCover_iff Y P').2 ⟨h.sUnion_eq, fun F hF ↦ hPP' F hF (h.pProp F hF)⟩

lemma isCover_empty_iff (P : Set α → Prop) : IsCover ∅ Y P ↔ Y = ∅ := by
  refine ⟨?_, ?_ ⟩
  · intro h
    rw [ ←sUnion_empty, h.sUnion_eq.symm ]
  intro h
  rw [ ←sUnion_empty] at h
  refine ⟨h.symm, by grind ⟩

lemma Set.IsCover.image_union (h : T.IsCover Y P)
    (hXN : Y.Nonempty)
    (hPP' : ∀ F : Set α, P F → P' (F ∪ X)) :
    ((· ∪ X) '' T).IsCover (Y ∪ X) P' := by
  suffices hi : ∀ F ∈ T, P F by
    simp only [isCover_iff, sUnion_image, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, ← biUnion_distrib_union _ (h.nonempty hXN), ← sUnion_eq_biUnion,
      h.sUnion_eq, true_and  ]
    exact fun F hFT ↦ (((fun a ↦ (hPP' F (hi F hFT))) ∘ T) X)
  exact fun F hFT ↦ h.pProp F hFT

lemma Set.IsCover.mono_subset (h : T.IsCover X P) (hX : Y ⊆ X) (hPQ : ∀ Z, P Z → Q (Z ∩ Y)) :
    ((· ∩ Y) '' T).IsCover Y Q := by
  rw [isCover_iff, sUnion_image, ← iUnion₂_inter, ← sUnion_eq_biUnion, h.sUnion_eq,
      inter_eq_self_of_subset_right hX, and_iff_right rfl]
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun Z hZ ↦ hPQ Z <| h.pProp _ hZ

lemma Set.isCover_sUnion (T : Set (Set α)) (P : Set α → Prop) (hF : ∀ F ∈ T, P F) :
    T.IsCover (⋃₀ T) P :=
  ⟨rfl, hF⟩

end General

section Number

/-- This is the size of the smallest cover of `X` in which each set satisfies `P`. -/
noncomputable def Set.coverNumber (X : Set α) (P : Set α → Prop) : ℕ∞ :=
  ⨅ (T : Set (Set α)) (_ : T.IsCover X P), T.encard

lemma Set.IsCover.coverNumber_le {T : Set (Set α)} (h : T.IsCover X P) :
    X.coverNumber P ≤ T.encard := by
  simp only [coverNumber ]
  exact biInf_le encard h

lemma encard_eq_coverNumber_of_nonempty {P : Set α → Prop}
    (hn : {T | IsCover T X P}.Nonempty) :
    ∃ T, IsCover T X P ∧ T.encard = X.coverNumber P := by
  have := ENat.exists_eq_iInf
  simp only [coverNumber]
  simp_rw [iInf_subtype']
  have := hn.to_subtype
  obtain ⟨T, hT ⟩ :=
    ENat.exists_eq_iInf (f := fun (T : {T : Set (Set α) | T.IsCover X P}) ↦ T.1.encard)
  refine ⟨T.1, ⟨T.2, hT ⟩ ⟩
  -- have := ENat.exists_eq_iInf (f := fun (hT : T.IsCover X P) ↦ T.encard)

lemma exists_encard_eq_coverNumber (hP : X.HasCover P) :
    ∃ T, IsCover T X P ∧ T.encard = X.coverNumber P := encard_eq_coverNumber_of_nonempty hP

-- lemma iInf₂_empty_eq_top {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [CompleteLattice α]
--    {f : (i : ι) → κ i → α} : ⨅ (i : ι), ⨅ (j : κ i), f i j = ⊤ := by sorry

lemma coverNumber_empty_eq_top {P : Set α → Prop}
    (hem : {T | IsCover T X P} = ∅) : X.coverNumber P = ⊤ := by
  simp only [coverNumber, iInf₂_eq_top]
  intro T hT
  by_contra
  have : T ∈ {T | T.IsCover X P} := mem_setOf.mpr hT
  rw [hem] at this
  exact this


lemma coverNumber_eq_top_of_not_hasCover (hP : ¬ X.HasCover P) : X.coverNumber P = ⊤ := by
  simp only [coverNumber, iInf_eq_top, encard_eq_top_iff]
  exact fun C hC ↦ False.elim <| hP ⟨C, hC⟩

lemma Set.exists_cover (X : Set α) (P : Set α → Prop) :
    X.coverNumber P = ⊤ ∨ ∃ T, IsCover T X P ∧ T.encard = X.coverNumber P := by
  obtain h0 | h := {T | IsCover T X P}.eq_empty_or_nonempty
  · left
    simp only [coverNumber]
    simp_rw [iInf_subtype']
    simp only [iInf_eq_top, Subtype.forall]
    intro T hT
    by_contra
    exact Ne.elim (ne_of_mem_of_not_mem' hT fun a ↦ a) h0
  right
  exact exists_encard_eq_coverNumber h

lemma one_le_coverNumber (hX : X.Nonempty) (P : Set α → Prop) : 1 ≤ X.coverNumber P := by
  by_contra hc
  have h1 := ENat.lt_one_iff_eq_zero.mp (Std.not_le.mp hc)
  obtain ht | ⟨T, hT, hTe ⟩ := X.exists_cover P
  · rw [h1] at ht
    simp only [ENat.zero_ne_top] at ht
  have : T.Nonempty := hT.nonempty hX
  grind

/--
Given a cover we can bound the cover number with the cover number of each element of the cover.
See IsCover.biUnion'
-/
lemma coverNumber_le_tsum_coverNumber {P' : Set α → Prop} (hcover : T.IsCover Y P) :
    Y.coverNumber P' ≤ ∑' X : T, (X.1).coverNumber P' := by
  obtain (h0 | h1) := exists_or_forall_not (fun X : T ↦ coverNumber X P' = ⊤)
  · simp [ENat.tsum_eq_top_of_eq_top h0]
  have hf : ∀ X : T, ∃ XT : Set (Set α), XT.IsCover (X.1) P' ∧
    XT.encard = (X.1).coverNumber P' := by
    intro X
    obtain (h | ⟨XT, hXres, hencard⟩) := (X.1).exists_cover P'
    · simp [h1 _ h]
    exact ⟨XT, hXres, hencard⟩
  choose f hfunco hfunca using hf
  have hcover := IsCover.biUnion' hcover f hfunco
  grw [hcover.coverNumber_le, ENat.encard_iUnion_le_tsum_encard, tsum_congr hfunca]


lemma coverNumber_le_bound {P' : Set α → Prop} {k : ℕ∞}
    (hcover : T.IsCover Y P)
    (hflat : ∀ F, P F → F.coverNumber P' ≤ k) :
    Y.coverNumber P' ≤ (T.encard) * k := by
  grw [coverNumber_le_tsum_coverNumber hcover, ENat.tsum_le_tsum (g := fun _ ↦ k),
    ENat.tsum_subtype_const, mul_comm]
  intro F
  simp [hflat _ <| hcover.pProp F F.2 ]
  --exact hP'

lemma isCover_image_singleton (hP : ∀ e ∈ X, P {e}) : (singleton '' X).IsCover X P  := by
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

lemma isCover_singleton_le (hP : ∀ e ∈ X, P {e}) : X.coverNumber P ≤ X.encard := by
  grw [(isCover_image_singleton hP).coverNumber_le, encard_image_le singleton X ]

lemma coverNumber_eq_zero_iff (P : Set α → Prop) : X.coverNumber P = 0 ↔ IsCover ∅ X P := by
  refine ⟨?_, ?_ ⟩
  · intro h
    obtain ht | ⟨T, hT, hTe ⟩ := exists_cover X P
    · by_contra
      rw[ht] at h
      simp only [ENat.top_ne_zero] at h
    rw [h] at hTe
    rwa [← encard_eq_zero.mp hTe  ]
  intro h
  have := h.coverNumber_le
  simp only [encard_empty, nonpos_iff_eq_zero] at this
  grind

lemma coverNumber_le_coverNumber {P Q : Set α → Prop} {X : Set α} {Y : Set α} (f : Set α → Set α )
    (hcov : ∀ T, T.IsCover X P → ( f '' T).IsCover Y Q) : Y.coverNumber Q ≤ X.coverNumber P := by
  obtain ht | ⟨T, hT, hTe ⟩ := exists_cover X P
  · rw [ht]
    simp only [le_top]
  grw [←hTe, (hcov T hT).coverNumber_le, encard_image_le]

lemma coverNumber_le_prop (P Q : Set α → Prop) (X : Set α)
    (hPQ : ∀ Y ⊆ X, P Y → Q Y) : X.coverNumber Q ≤ X.coverNumber P := by
  obtain ht | ⟨T, hT, hTe ⟩ := exists_cover X P
  · rw [ht]
    simp only [le_top]
  rw [←hTe]
  exact IsCover.coverNumber_le ⟨hT.sUnion_eq, fun F hF ↦ hPQ F (hT.subset hF) (hT.pProp F hF)⟩

--Mathieu
lemma coverNumber_congr (P Q : Set α → Prop)
    (hPQ : ∀ (Y : Set α), Y ⊆ X → (P Y ↔ Q Y)) :
    X.coverNumber P = X.coverNumber Q := by
  sorry

lemma coverNumber_le_coverNumber_union {P Q : Set α → Prop} {X : Set α} {Y : Set α}
    (hX : X.Nonempty) (hP : ∀ F : Set α, P F → Q (F ∪ Y)) :
    (X ∪ Y).coverNumber Q ≤ X.coverNumber P :=
  coverNumber_le_coverNumber (· ∪ Y) (fun ?_ hT ↦ (hT.image_union hX hP))

lemma coverNumber_union_le :
    (X ∪ Y).coverNumber P ≤ X.coverNumber P + Y.coverNumber P := by
  obtain ht | ⟨T, hT, hTe ⟩ := exists_cover X P
  · rw [ht]
    simp only [top_add, le_top]
  obtain ht | ⟨T', hT', hT'e ⟩ := exists_cover Y P
  · rw [ht]
    simp only [add_top, le_top]
  grw [←hTe, ←hT'e, (hT.union_isCover hT').coverNumber_le ]
  exact encard_union_le T T'

lemma coverNumber_le_coverNumber_intersect {P Q : Set α → Prop} (X : Set α) (Y : Set α )
    (hP : ∀ F ⊆ X, P F → Q (F ∩ Y) ) : (X ∩ Y).coverNumber Q ≤ X.coverNumber P := by
  apply coverNumber_le_coverNumber (· ∩ Y)
  intro T hT
  refine ⟨?_, ?_ ⟩
  · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e ⟨he, heE⟩ ↦ ?_
    · intro ⟨F, hF, hF' ⟩
      simp only at hF'
      rw [←hF']
      have := hT.subset hF
      grind
    simp only [sUnion_image, mem_iUnion, mem_inter_iff, exists_and_left, exists_prop]
    rw [←hT.sUnion_eq ] at he
    obtain ⟨F, hF, hFe ⟩ := he
    refine ⟨F, ⟨hFe, hF, heE⟩⟩
  intro F hF
  obtain ⟨G, hG, hG2 ⟩ := hF
  simp only at hG2
  rw [←hG2]
  exact hP G (hT.subset hG) (hT.pProp G hG)

end Number

namespace Matroid
section Matroid

-- /-- Docstring here -/
-- def IsCCProp (P : Matroid α → Set α → Prop) : Prop :=
--     ∀ M : Matroid α, ∀ F : Set α, P M F → P M (M.closure F)

/-- If a property is closed under closure, you can also look at the closure of a cover. -/
lemma Set.IsCover.isCover_closure {P : Matroid α → Set α → Prop} {M : Matroid α}
    (h : T.IsCover X (P M)) (hP : ∀ F : Set α, P M F → P M (M.closure F))
    (hXc : M.IsFlat X) (hX : X ⊆ M.E) :
    (M.closure '' T).IsCover X (P M) := by
  simp only [isCover_iff, sUnion_image, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, subset_antisymm_iff (b := X), iUnion_subset_iff, mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  nth_rw 1 [←M.isFlat_iff_closure_self.1 hXc ]
  refine ⟨⟨fun T' hT' ↦ closure_subset_closure_of_subset_closure
    (by simp only [M.isFlat_iff_closure_self.1 hXc,IsCover.subset h hT' ]) , ?_ ⟩,
    fun F hF ↦ (hP F (h.pProp F hF)) ⟩
  · grw [h.sUnion_eq.symm.subset, sUnion_eq_biUnion]
    refine biUnion_mono rfl.subset fun Z hZ ↦ (subset_closure_iff_forall_subset_isFlat Z
      ((h.subset hZ).trans hX)).mpr fun F a a_1 ↦ a_1

end Matroid

section Rank
-- h.trans h'
-- Nonspanning

/-- Cover when the property is bounded rank. -/
def IsRankCover (M : Matroid α) (T : Set (Set α)) (X : Set α) (k : ℕ∞) : Prop :=
    T.IsCover X (fun A ↦ M.eRk A ≤ k)

/-- Cover number for Rank -/
noncomputable def rankCoverNumber (M : Matroid α) (X : Set α) (k : ℕ∞) : ℕ∞ :=
  X.coverNumber (fun A ↦ M.eRk A ≤ k)

lemma IsRankCover.contract (h : (M ／ X).IsRankCover T Y k) (hXN : Y.Nonempty) :
    M.IsRankCover ((· ∪ X) '' T) (Y ∪ X) (k + M.eRk X)  := by
  unfold IsRankCover
  unfold IsRankCover at h
  apply IsCover.image_union h hXN
  intro F hF
  rw [← eRelRk_add_eRk_eq, eRelRk_eq_eRk_contract]
  exact add_le_add_left hF (M.eRk X)

lemma IsRankCover_iff {M : Matroid α} {T : Set (Set α)} {X : Set α} {k : ℕ∞} :
    M.IsRankCover T X k ↔ T.IsCover X (fun A ↦ M.eRk A ≤ k) := Iff.rfl

lemma rankCoverNumber_eq {M : Matroid α} {X : Set α} {k : ℕ∞} :
    M.rankCoverNumber X k = X.coverNumber (fun A ↦ M.eRk A ≤ k) := by
  sorry

lemma IsRankCover_iff' (M : Matroid α) (T : Set (Set α)) (X : Set α) (k : ℕ∞) :
    M.IsRankCover T X k ↔ ⋃₀ T = X ∧ (∀ F ∈ T, M.eRk F ≤ k) := by
  rw [IsRankCover_iff, isCover_iff]

lemma IsRankCover_iff_restriction : M.IsRankCover T X k ↔ (M ↾ X).IsRankCover T (M ↾ X).E k := by
  rw [IsRankCover_iff', IsRankCover_iff', M.restrict_ground_eq]
  refine and_congr_right fun hU => ?_
  refine ⟨?_, ?_⟩
  · intro hRM F hFT
    have hFX : F ⊆ X := by
      rw [← hU]
      exact subset_sUnion_of_mem hFT
    simpa [M.restrict_eRk_eq hFX] using hRM F hFT
  · intro hRMX F hFT
    have hFX : F ⊆ X := by
      rw [← hU]
      exact subset_sUnion_of_mem hFT
    simpa [M.restrict_eRk_eq hFX] using hRMX F hFT

lemma IsRankCover.subset (h : M.IsRankCover T X k) (hY : Y ∈ T) : Y ⊆ X :=
  (IsRankCover_iff.1 h).subset hY

lemma IsRankCover.subset_ground (h : M.IsRankCover T X k) (hY : Y ∈ T)
    (hX : X ⊆ M.E := by aesop_mat) : Y ⊆ M.E := ((IsRankCover_iff.1 h).subset hY).trans hX

lemma IsRankCover.mono_subset (hcov : M.IsRankCover T X k) (hX : Y ⊆ X) :
    M.IsRankCover ((· ∩ Y) '' T) Y k := by
  rw [IsRankCover_iff]
  rw [IsRankCover_iff] at hcov
  apply hcov.mono_subset hX
  intro F hF
  grw [eRk_subset_le M inter_subset_left, hF]

lemma IsRankCover.subset_union_closure (hcov : M.IsRankCover T X k) (hne : X.Nonempty)
    (hX : X ⊆ M.E) : X ∪ M.closure ∅ ⊆ ⋃ F ∈ T, M.closure F := by
  refine union_subset ?_ ?_
  · grw [←iUnion₂_mono (fun F hF ↦ subset_closure M F (hcov.subset_ground hF)),
    ←sUnion_eq_biUnion, ←hcov.sUnion_eq ]
  obtain ⟨F', hF' ⟩ := hcov.nonempty hne
  have h1 : M.closure ∅ ⊆ M.closure F' := by
    rw [← M.closure_empty_union_closure_eq F']
    grind
  grw [h1]
  exact subset_biUnion_of_mem hF'

lemma IsRankCover.loops_union_of_closure (hcov : M.IsRankCover T X k) (hD : D ⊆ M.loops)
    (hne : X.Nonempty) (hX : X ⊆ M.E) :
    M.IsRankCover ((· ∩ (X ∪ D)) '' (M.closure '' T) ) (X ∪ D) k := by
  refine ⟨ ?_, ?_ ⟩
  · simp only [sUnion_image, mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
    rw [Eq.symm (iUnion₂_inter (fun i j ↦ M.closure i) (X ∪ D)) ]
    refine inter_eq_self_of_subset_right ?_
    grw [union_subset_union_right X hD ]
    apply hcov.subset_union_closure hne hX
  intro F hF
  simp only [mem_image, exists_exists_and_eq_and] at hF
  obtain ⟨F', hF', rfl ⟩ := hF
  grw [eRk_subset_le M (inter_subset_left)]
  simp only [eRk_closure_eq]
  exact hcov.pProp F' hF'

lemma IsRankCover.isCover_flat_closure (hcov : M.IsRankCover T X k) (hX : M.IsFlat X) :
    M.IsRankCover (M.closure '' T) X k := by
  rw [IsRankCover_iff]
  rw [IsRankCover_iff]  at hcov
  apply Set.IsCover.isCover_closure hcov (fun F hF ↦ ?_) hX (hX.subset_ground)
  rwa [(eRk_closure_eq M F) ]

lemma IsRankCover.mono_k {k' : ℕ∞} (hcov : M.IsRankCover T X k) (hkk' : k ≤ k') :
    M.IsRankCover T X k' := by
  refine ⟨ hcov.sUnion_eq, fun F hF ↦
    Std.IsPreorder.le_trans (M.eRk F) k k' (hcov.pProp F hF) hkk'⟩

lemma IsRankCover.nonempty_set (h : M.IsRankCover T X k) (hX : X.Nonempty) :
    T.Nonempty := h.nonempty hX

lemma IsRankCover_Zero (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X.HasCover (fun A ↦ M.eRk A ≤ 0) ↔ X ⊆ M.loops := by
  refine ⟨ ?_, ?_ ⟩
  · intro h e he
    obtain ⟨ T', hT' ⟩ := h
    rw[←hT'.sUnion_eq ] at he
    obtain ⟨ Y, hYt, heY ⟩ := he
    exact isLoop_iff.mp (isLoop_iff.mp (((Matroid.eRk_eq_zero_iff
    ((IsRankCover_iff.2 hT').subset_ground hYt )).1 (nonpos_iff_eq_zero.mp (hT'.pProp Y hYt))) heY))
  intro h
  refine ⟨(singleton '' X), isCover_image_singleton ?_⟩
  intro e he
  simp only [nonpos_iff_eq_zero]
  refine IsLoop.eRk_eq (isLoop_iff.mpr (h he))

lemma CoverNumberRank_subset_le (M : Matroid α) (k : ℕ∞) (hX : Y ⊆ X) :
    M.rankCoverNumber Y k ≤ M.rankCoverNumber X k := by
  rw [rankCoverNumber_eq, rankCoverNumber_eq]
  apply coverNumber_le_coverNumber (fun x ↦ x ∩ Y)
  intro T hT
  rw [←IsRankCover_iff] at hT
  rw [←IsRankCover_iff]
  exact hT.mono_subset hX

lemma IsRankCover_zero_or_exists' (X : Set α) (hne : X.Nonempty) (hX : X ⊆ M.E := by aesop_mat) :
    ⊤ = M.rankCoverNumber X 0 ∨ ∃ F, M.IsRankCover ({M.closure F ∩ X}) X 0 := by
  rw [rankCoverNumber_eq]
  obtain ht | ⟨T, hT, hT2 ⟩ := X.exists_cover (fun A ↦ M.eRk A ≤ 0)
  · left
    rw [ht]
  right
  rw [← IsRankCover_iff ] at hT
  obtain ⟨ F, hF ⟩:= hT.nonempty_set hne
  refine ⟨ F , ?_ ⟩
  have hsub := (IsRankCover_Zero X).1 ⟨T, hT⟩
  refine ⟨ ?_, ?_ ⟩
  · simp only [sUnion_singleton, inter_eq_right]
    grw [hsub ]
    exact loops_subset_closure M F
  simp only [mem_singleton_iff, nonpos_iff_eq_zero, forall_eq]
  apply nonpos_iff_eq_zero.mp
  grw [eRk_subset_le M (inter_subset_right), (eRk_eq_zero_iff hX).mpr hsub]

lemma IsRankCover_zero_or_exists (X : Set α) (hne : X.Nonempty) (hX : X ⊆ M.E := by aesop_mat) :
    M.rankCoverNumber X 0 = ⊤ ∨ M.rankCoverNumber X 0 = 1 := by
  rw [rankCoverNumber_eq]
  obtain htop | ⟨ F, hF ⟩ := IsRankCover_zero_or_exists' X hne
  · left
    exact htop.symm
  right
  have h1 := hF.coverNumber_le
  simp only [ encard_singleton] at h1
  have h2 := one_le_coverNumber hne (fun A ↦ M.eRk A ≤ 0)
  grind

lemma IsRankCover_zero_iff_not_rankPos :
    (M.E).HasCover (fun A ↦ M.eRk A ≤ 0) ↔ ¬ M.RankPos := by
  refine ⟨fun h ↦ (M.not_rankPos_iff.2 (Matroid.eq_loopyOn_iff_loops.mpr
    ⟨Eq.symm (Subset.antisymm ((IsRankCover_Zero M.E).1 h) (loops_subset_ground M)),
    by simp only ⟩)) , fun h ↦ (IsRankCover_Zero M.E fun ⦃a⦄ a_1 ↦ a_1).mpr
    (subset_of_subset_of_eq (fun ⦃a⦄ a_1 ↦ a_1) (Eq.symm (Matroid.eq_loopyOn_iff_loops.1
    (M.not_rankPos_iff.1 h)).1)) ⟩

lemma IsRankCover.nontrivial (hcov : M.IsRankCover T X k) (hk : k < M.eRk X) :
    T.Nontrivial := by
  by_contra! hc
  have hXne : X.Nonempty := by
    by_contra! hc
    subst hc
    simp at hk
  by_contra!
  have h1 := hcov.nonempty
  have h1 : T.encard = 1 := by grind
  obtain ⟨X', hX' ⟩ := Set.encard_eq_one.1 h1
  have h2 := ((IsRankCover_iff).1 hcov).sUnion_eq
  rw [hX'] at h2
  simp only [sUnion_singleton] at h2
  have hXT : X' ∈ T := by
    rw[ hX' ]
    exact mem_singleton X'
  have hf := ((IsRankCover_iff).1 hcov).pProp X' hXT
  rw[ h2] at hf
  grind

lemma setOf_point_isRankCover (M : Matroid α) (X : Set α) [(M ↾ X).RankPos] :
    M.IsRankCover {P | (M ↾ X).IsPoint P} X 1 := by
  refine ⟨subset_antisymm (sUnion_subset fun _ ↦ IsPoint.subset_ground) fun e he ↦ ?_, ?_ ⟩
  · simp only [mem_sUnion, mem_setOf_eq]
    obtain hl | hnl := (M ↾ X).isLoop_or_isNonloop e
    · obtain ⟨f, hf⟩ := (M ↾ X).exists_isNonloop
      exact ⟨_, hf.closure_isPoint, hl.mem_closure _⟩
    exact ⟨_, hnl.closure_isPoint, mem_closure_of_mem _ (by simp) (by simpa)⟩
  intro F hF
  simp only [mem_setOf_eq] at hF
  have hgs := hF.subset_ground
  simp only [restrict_ground_eq] at hgs
  grw [← inter_eq_left.2 (LE.le.subset hgs), ←restrict_eRk_eq', hF.eRk ]

lemma setOf_point_isRankCover' [hM : (M ↾ X).Loopless] :
    M.IsRankCover {P | (M ↾ X).IsPoint P} X 1 := by
  obtain ⟨E, hX⟩ | h := (M ↾ X).eq_loopyOn_or_rankPos'
  · rw [hX]
    rw [hX] at hM
    obtain rfl : E = ∅ := by simpa using hM
    constructor <;> simp [IsPoint]
    rw [ ←restrict_ground_eq (M := M) (R := X), hX ]
    simp only [loopyOn_empty, emptyOn_ground, sUnion_eq_empty, mem_setOf_eq, and_imp, forall_eq,
      eRk_empty, zero_ne_one, implies_true]
  exact M.setOf_point_isRankCover X

lemma setOf_point_isRankCover_ground (M : Matroid α) [M.RankPos] :
    M.IsRankCover {P | M.IsPoint P} M.E 1 := by
  sorry

--Need Help
lemma setOf_point_isminRankCover_ground (M : Matroid α) [M.RankPos] :
    M.rankCoverNumber M.E 1 = {P | M.IsPoint P}.encard := by
  have h1 := (setOf_point_isRankCover_ground M ).coverNumber_le
  rw [←rankCoverNumber] at h1
  sorry

lemma setOf_line_isRankCover [(M ／ {e}).RankPos] (he : M.IsNonloop e) :
    (M.E \ {e}).coverNumber (fun F ↦ ∃ L, M.IsLine L ∧ e ∈ L ∧ F = L \ {e}) ≤
    (M.E \ {e}).coverNumber (fun A ↦ (M ／ {e}).eRk A ≤ 1)
    := by
  rw [←rankCoverNumber, ←contract_ground M {e}, setOf_point_isminRankCover_ground]
  have hcov : ((· \ {e})''  (M.closure '' ((insert e · ) '' {P | (M ／ {e}).IsPoint P}))).IsCover
    (M.E \ {e}) (fun F ↦ ∃ L, M.IsLine L ∧ e ∈ L ∧ F = L \ {e}) := by
    refine ⟨?_, ?_ ⟩
    --rw [←hT.sUnion_eq ]
    · simp only [sUnion_image, mem_image, exists_exists_and_eq_and, iUnion_exists, biUnion_and',
      iUnion_iUnion_eq_right]
      refine subset_antisymm (iUnion_subset fun P ↦ ?_) fun f hf ↦ ?_
      · simp only [mem_setOf_eq, iUnion_subset_iff, diff_subset_iff, union_diff_self,
        singleton_union]
        intro h
        rw [insert_eq_of_mem he.mem_ground]
        exact closure_subset_ground M (insert e P)
      rw [←contract_ground M {e}, ←(setOf_point_isRankCover_ground (M ／ {e})).sUnion_eq] at hf
      obtain ⟨P, hP, hPf⟩ := hf
      simp only [mem_setOf_eq, mem_iUnion, mem_diff, mem_singleton_iff, exists_and_left,
        exists_prop]
      have hP' : P ⊆ M.E \ {e} := by
        rw [←contract_ground M {e}]
        exact IsPoint.subset_ground hP
      refine ⟨P, ⟨mem_of_subset_of_mem (subset_closure M (insert e P) (insert_subset_iff.mpr
          ⟨he.mem_ground, hP'.trans diff_subset⟩)) (by grind), hP, by grind ⟩⟩
    intro F hF
    simp only [mem_image, exists_exists_and_eq_and] at hF
    obtain ⟨P, hP, hPF ⟩ := hF
    use M.closure (insert e P)
    have hP' : P ⊆ M.E \ {e} := by
      rw [←contract_ground M {e}]
      exact IsPoint.subset_ground hP
    refine ⟨?_,mem_of_subset_of_mem (subset_closure M (insert e P) (insert_subset_iff.mpr
          ⟨he.mem_ground, hP'.trans diff_subset⟩)) (mem_insert e P), hPF.symm⟩
    refine ⟨isFlat_closure (insert e P), ?_⟩
    simp only [eRk_closure_eq]
    have hhelp := CovBy.eRk_eq ((isPoint_contract_iff (M := M) (C := {e}) (P := P)).1 hP).1
    simp only [singleton_union, eRk_closure_eq] at hhelp
    rw [hhelp, he.eRk_eq]
    exact one_add_one_eq_two
  grw [contract_ground M {e}, hcov.coverNumber_le, encard_image_le, encard_image_le,
    encard_image_le]



  --   have ⟨P, hP1, hP2⟩ : ∃ P, (M ／ {e}).IsPoint P ∧ A ⊆ P := by sorry
  -- -- obtain hlt | heq := lt_or_eq_of_le hP1
  -- -- · sorry
  -- use M.closure (insert e P)
  -- refine ⟨?_,?_,?_⟩
  -- · refine ⟨isFlat_closure (insert e P), ?_⟩
  --   simp only [eRk_closure_eq]
  --   have hhelp := CovBy.eRk_eq ((isPoint_contract_iff (M := M) (C := {e}) (P := P)).1 hP1).1
  --   simp only [singleton_union, eRk_closure_eq] at hhelp
  --   rw [hhelp, he.eRk_eq]
  --   exact one_add_one_eq_two
  -- have hP' : P ⊆ M.E \ {e} := by
  --     rw [←contract_ground M {e}]
  --     exact IsPoint.subset_ground hP1
  -- exact mem_of_subset_of_mem ((subset_closure M (insert e P) (insert_subset_iff.mpr
  --     ⟨he.mem_ground, hP'.trans diff_subset⟩)) ) (mem_insert e P)
  -- (subset_closure M (insert e P) (insert_subset_iff.mpr
  --     ⟨he.mem_ground, hP1.trans diff_subset⟩))


lemma setOf_line_isRankCover' [(M ／ {e}).RankPos] (he : M.IsNonloop e) :
    M.IsRankCover { F | ∃ L, M.IsLine L ∧ e ∈ L ∧ F = L \ {e}} (M.E \ {e}) 2 := by
  refine ⟨?_, ?_⟩
  · rw [←contract_ground M {e}, ←((M ／ {e}).setOf_point_isRankCover_ground).sUnion_eq]
    refine ext ?_
    intro x
    refine ⟨?_, ?_ ⟩
    · intro ⟨F, ⟨⟨L, ⟨hL, ⟨hLe, hL'⟩⟩⟩, hFx⟩⟩
      rw [hL'] at hFx
      have hP : (M ／ {e}).IsPoint (L \ {e}) := by
        refine (isPoint_contract_iff (singleton_subset_iff.mpr he.mem_ground)).mpr ?_
        simp only [union_diff_self, singleton_union, insert_eq_of_mem hLe]
        refine ⟨(IsLine.mem_iff_covBy hL he).mp hLe, disjoint_sdiff_left⟩
      refine ⟨L \ {e}, ⟨hP, hFx⟩⟩
    intro ⟨P, ⟨hP, hxP⟩⟩
    have hLin : M.IsLine (M.closure (insert e P)) := by
      refine ⟨isFlat_closure (insert e P), ?_⟩
      simp only [eRk_closure_eq]
      have hhelp := CovBy.eRk_eq ((isPoint_contract_iff (M := M) (C := {e}) (P := P)).1 hP).1
      simp only [singleton_union, eRk_closure_eq] at hhelp
      rw [hhelp, he.eRk_eq]
      exact one_add_one_eq_two
    have hP : P ⊆ M.E \ {e} := by
      rw [←contract_ground M {e}]
      exact IsPoint.subset_ground hP
    refine ⟨(M.closure (insert e P)) \ {e}, ⟨⟨M.closure (insert e P),
      ⟨hLin,mem_of_subset_of_mem (subset_closure M (insert e P) (insert_subset_iff.mpr
      ⟨he.mem_ground, hP.trans diff_subset⟩)) (mem_insert e P),
      diff_eq_diff_iff_inter_eq_inter.mpr rfl⟩ ⟩, ?_ ⟩⟩
    refine mem_diff_singleton.mpr ⟨mem_of_subset_of_mem (subset_closure_of_subset' M
      (subset_insert e P) (hP.trans diff_subset)) hxP, by grind⟩
  intro F ⟨L, ⟨hL, hL2, h3⟩⟩
  grw [h3, eRk_subset_le M diff_subset, hL.eRk]

--lemma setOf_line_isminRankCover [(M ／ {e}).RankPos] (he : M.IsNonloop e) :

lemma isRankCover_ground (M : Matroid α) : M.IsRankCover ({X}) X (M.eRk X) := by
  refine ⟨ by simp, ?_ ⟩
  intro F hF
  simp only [mem_singleton_iff] at hF
  rw [hF]

lemma rankCoverNumber_exists (M : Matroid α) (hk : 1 ≤ k) (hX : X ⊆ M.E) :
    X.HasCover (fun A ↦ M.eRk A ≤ k) := by
  by_cases hRP : (M ↾ X).RankPos
  · refine ⟨{P | (M ↾ X).IsPoint P}, IsRankCover_iff.1
      ((M.setOf_point_isRankCover X).mono_k hk) ⟩
  have hXl : X ⊆ M.loops := by
    rw [not_rankPos_iff, restrict_ground_eq] at hRP
    refine (eRk_eq_zero_iff hX).mp ?_
    rw [Eq.symm (eRank_restrict M X), hRP]
    exact eRank_loopyOn X
  obtain ⟨ T, hT ⟩ := (IsRankCover_Zero X).2 hXl
  refine ⟨ T, IsRankCover_iff.1 (IsRankCover.mono_k hT (ENat.zero_le))⟩

lemma rankCoverNumber_exists_cover (M : Matroid α) (X : Set α) (k : ℕ∞) :
    M.rankCoverNumber X k = ⊤ ∨ ∃ T, M.IsRankCover T X k ∧ T.encard = M.rankCoverNumber X k
    := exists_cover X (fun A ↦ M.eRk A ≤ k)

lemma RankPropCover_exists_encard_eq (M : Matroid α) (hk : 1 ≤ k) (hX : X ⊆ M.E) :
    ∃ T, M.IsRankCover T X k ∧ T.encard = M.rankCoverNumber X k := by
  simp only [IsRankCover_iff]
  exact exists_encard_eq_coverNumber (rankCoverNumber_exists M hk hX)

lemma rankCoverNumber_restriction_eq :
    M.rankCoverNumber X a = (M ↾ X).rankCoverNumber X a  := by
  refine coverNumber_congr (fun A ↦ M.eRk A ≤ a) (fun A ↦ (M ↾ X).eRk A ≤ a) ?_
  intro Y hY
  simp only [restrict_eRk_eq M hY]

lemma IsRankCover.rankCoverNumber_le {T : Set (Set α)} (h : M.IsRankCover T X k) :
    M.rankCoverNumber X k ≤ T.encard := by
  rw [rankCoverNumber_eq]
  rw [IsRankCover_iff] at h
  exact h.coverNumber_le


lemma IsRankCover.delete (hT : M.IsRankCover T X k) (D : Set α) :
    M.IsRankCover ((fun s ↦ s \ D) '' T) (X \ D) k := by
  refine ⟨ ?_, ?_ ⟩
  · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
    · intro hK
      obtain ⟨ X, hX, h ⟩ := hK
      rw[ ← h]
      exact diff_subset_diff_left (hT.subset hX)
    simp only [mem_diff] at he
    rw [←hT.sUnion_eq] at he
    obtain ⟨X, hX, hXe ⟩ := he.1
    have : e ∈ X \ D := mem_diff_of_mem hXe (he.2)
    grind
  intro F hF
  obtain ⟨ F' ,hF' ,hF2 ⟩ := hF
  rw [←hF2]
  grw [eRk_subset_le M (diff_subset)]
  exact hT.pProp F' hF'

lemma rankCoverNumber_eRk (hX : X.Nonempty) :
    M.rankCoverNumber X (M.eRk X) = 1 := by
  have h2 : 1 ≤ X.coverNumber (fun A ↦ M.eRk A ≤ (M.eRk X)) :=
    one_le_coverNumber hX (fun A ↦ M.eRk A ≤ (M.eRk X))
  refine h2.antisymm' ?_
  simpa using (isRankCover_ground M).coverNumber_le

lemma rankCoverNumber_spanning [M.Nonempty] (hY : M.Spanning Y) :
    M.rankCoverNumber M.E (M.eRk Y) = 1 := by
  have hcov : M.IsRankCover {M.closure Y} M.E (M.eRk Y) := by
    refine ⟨?_, ?_ ⟩
    · simp only [sUnion_singleton, hY.closure_eq]
    intro F hF
    rw [mem_singleton_iff.1 hF, eRk_closure_eq]
  have h1 := hcov.rankCoverNumber_le
  simp only [encard_singleton] at h1
  have h2 : 1 ≤ M.rankCoverNumber M.E (M.eRk Y) := by
    rw [rankCoverNumber]
    exact one_le_coverNumber (ground_nonempty M) (fun A ↦ M.eRk A ≤ M.eRk Y)
  grind

lemma rankCoverNumber_spanning' (hY : (M ↾ X).Spanning Y) (hX : X.Nonempty) :
    M.rankCoverNumber X ((M ↾ X).eRk Y) = 1 := by
  have hcov : M.IsRankCover {(M ↾ X).closure Y} X ((M ↾ X).eRk Y) := by
    refine ⟨?_, ?_ ⟩
    · simp only [sUnion_singleton, hY.closure_eq, restrict_ground_eq]
    intro F hF
    have hrw : (M ↾ X).closure Y = (M ↾ X).closure Y ∩ X := by refine left_eq_inter.mpr (by grind)
    rw [mem_singleton_iff.1 hF, hrw, ←eRk_restrict, eRk_closure_eq]
  have h1 := hcov.rankCoverNumber_le
  simp only [encard_singleton] at h1
  have h2 : 1 ≤ M.rankCoverNumber X ((M ↾ X).eRk Y) := by
    rw [rankCoverNumber]
    exact one_le_coverNumber hX (fun A ↦ M.eRk A ≤ (M ↾ X).eRk Y)
  grind

lemma rankCoverNumber_delete_loop (hD : D ⊆ M.loops) (hne : (X \ D).Nonempty)
    (hX : X ⊆ M.E) :
    M.rankCoverNumber X k = M.rankCoverNumber (X \ D) k := by
  have h1 := CoverNumberRank_subset_le M k (diff_subset (s := X) (t := D))
  have hh : X \ D ⊆ M.E := by
    simp only [diff_subset_iff, subset_union_of_subset_right hX D ]
  obtain ht | ⟨T', hT', hT'en ⟩ := (X \ D).exists_cover (fun A ↦ M.eRk A ≤ k)
  · rw [←rankCoverNumber_eq] at ht
    rw [ht] at h1
    rw [ht]
    grind
  rw [←IsRankCover_iff] at hT'
  have hcov := hT'.loops_union_of_closure (D := D ∩ X)
    (LE.le.subset fun ⦃a⦄ a_1 ↦ hD (inter_subset_left a_1)) hne hh
  have h2 := hcov.rankCoverNumber_le
  have : (X \ D) ∪ (D ∩ X) = X := by grind
  grw [this, encard_image_le (fun x ↦ x ∩ X) (M.closure '' T'),
    encard_image_le M.closure T', hT'en] at h2
  rw [←rankCoverNumber_eq] at h2
  grind

lemma rankCoverNumber_contract_one {a : ℕ∞} (hel : M.IsNonloop e) (heX : e ∈ X)
    (hne : (X \ {e}).Nonempty) :
    M.rankCoverNumber X (a + 1) ≤ (M ／ {e}).rankCoverNumber (X \ {e}) a
    := by
  apply coverNumber_le_coverNumber (fun x ↦ x ∪ {e})
  intro T hT
  have hrw : X = X \ {e} ∪ {e} := by grind
  nth_rw 1 [hrw]
  apply hT.image_union hne (P' := (fun A ↦ M.eRk A ≤ a + 1))
    (P := (fun A ↦ (M ／ {e}).eRk A ≤ a)) (X := {e})
  intro F hF
  rw [←eRelRk_eq_eRk_contract M {e} F] at hF
  grw [ ←eRelRk_add_eRk_eq M {e} F, IsNonloop.eRk_eq hel]
  simp only [ne_eq, ENat.one_ne_top, not_false_eq_true, add_le_add_iff_left_of_ne_top]
  exact hF


lemma rankCoverNumber_contract_one' {a : ℕ∞} (hel : M.IsNonloop e) :
    M.rankCoverNumber X (a + 1) ≤ (M ／ {e}).rankCoverNumber X a
    := by
  refine coverNumber_le_prop (fun A ↦ (M ／ {e}).eRk A ≤ a) (fun A ↦ M.eRk A ≤ a + 1) X ?_
  intro Y hY h
  rw [←eRelRk_eq_eRk_contract M {e} Y] at h
  grw [eRk_subset_le M (subset_union_left (t := {e})), ←eRelRk_add_eRk_eq M {e} Y,
    IsNonloop.eRk_eq hel ]
  simp only [ne_eq, ENat.one_ne_top, not_false_eq_true, add_le_add_iff_left_of_ne_top, h]

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

lemma base_isCover {a : ℕ} (hr : M.eRank ≤ a + 1) (ha : 1 ≤ a) (hXfin : X.Finite)
    --(h : Maximal (fun Y ↦ Y ⊆ M.E ∧ (M ↾ Y).IsFiniteRankUniform (a + 1) Y.encard) X) :
    (h : MaximalFor (fun x ↦ x ∈ {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1)}) encard X) :
    M.IsRankCover (M.closure '' {K | K ⊆ X ∧ K.encard = a}) M.E a := by
    --M.IsRankCover a (M.closure '' {K | K ⊆ X ∧ K.encard = a}) := by
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
      exact hcon' (singleton e) (singleton_subset_iff.mpr hc)
        (by simp only [encard_singleton, ENat.one_le_coe, ha ]) (mem_closure_self M e he)
    --have hwin := h.not_prop_of_ssuperset (t := insert e X) (by grind)
    have hwin := h.not_prop_of_gt (j := insert e X)
      (Finite.encard_lt_encard hXfin (ssubset_insert heX))
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
        rw [ ←unifOn_ground_eq E (k := a + 1), ← hEX, restrict_ground_eq, diff_subset_iff,
          singleton_union]
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
    M.rankCoverNumber M.E a ≤ Nat.choose b a := by
  have : M.RankFinite := M.eRank_ne_top_iff.mp (ENat.ne_top_iff_exists.2
      (Exists.intro ((fun x1 x2 ↦ x1 + x2) a 1) (hr.symm)))
  by_contra! hcon
  obtain ⟨B, hB⟩ := M.exists_isBase
  set Unif : Set (Set α) := {X | X ⊆ M.E ∧ (M ↾ X).IsFiniteRankUniform (a + 1)} with h_UnifS
  have hne : Unif.Nonempty := by
    refine ⟨B, (IsBase.subset_ground hB), ?_, ?_,⟩
    · rwa [eRank_restrict, hB.eRk_eq_eRank]
    rw [hB.indep.restrict_eq_freeOn]
    exact freeOn_uniform B
  have hYbound : ∀ Y, Y ∈ Unif → Y.encard < b + 1 := by
    intro X hX
    by_contra hc
    simp only [not_lt] at hc
    have h2 : ((unifOn (M ↾ X).E (a + 1)).NoUniformMinor (a + 1) (b + 1)) := by
      rw[←hX.2.eq_unifOn ]
      exact hM.minor (IsRestriction.isMinor (restrict_isRestriction M X))
    have h3 := unifOn_noUniformMinor_iff.1 h2
    grw [← restrict_ground_eq (M := M) (R := X)] at hc
    grind
  have hcard : (encard '' Unif).Finite := by
    refine ENat.finite_of_sSup_lt_top ?_
    refine lt_of_le_of_lt ?_ <| WithTop.natCast_lt_top (b + 1)
    simp only [sSup_le_iff, mem_image, forall_exists_index, and_imp]
    intro k A hAE h
    rw[←h ]
    exact Std.le_of_lt (hYbound A ⟨hAE.1, hAE.2 ⟩)
  obtain ⟨X, hX⟩ := Finite.exists_maximalFor' encard _ hcard hne
  have hXb : X.encard < b + 1 := hYbound X hX.prop
  set Subsets : Set (Set α) := {Y | Y ⊆ X ∧ Y.encard = a} with h_sub
  have hiC := base_isCover (Std.le_of_eq hr) ha
      ((Set.encard_le_coe_iff.1 (ENat.lt_coe_add_one_iff.mp hXb)).1) hX
  obtain ⟨x, hx ⟩ := ENat.ne_top_iff_exists.1 (LT.lt.ne_top hXb)
  rw[←hx] at hXb
  grw [hiC.rankCoverNumber_le, Set.encard_image_le, (set_to_binom_number) X hx.symm,
    (Nat.choose_le_choose a (Nat.le_of_lt_succ (ENat.coe_lt_coe.mp hXb)))] at hcon
  simp only [lt_self_iff_false] at hcon

lemma rankCoverNumber_from_base {a b : ℕ} (ha : 1 ≤ a)
    (hM : NoUniformMinor M (a + 1) (b + 1)) :
    M.rankCoverNumber M.E a ≤
    (Nat.choose b a) * M.rankCoverNumber M.E (a + 1) := by
    -- M.E.coverNumber (fun A ↦ M.eRk A ≤ a) ≤
    -- (Nat.choose b a) * (M.E).coverNumber (fun A ↦ M.eRk A ≤ a + 1) := by
  sorry

lemma rankCoverNumber_le_binomial {M : Matroid α} [M.RankPos] {a b : ℕ} {n : ℕ∞} (ha : a ≠ 0)
    (hb : a ≤ b)
    (hM : NoUniformMinor M (a + 1) (b + 1)) (hn : M.eRank = a + n) :
    M.rankCoverNumber M.E a ≤ (Nat.choose b a)^n := by
  obtain htop | hfin := eq_or_ne M.eRank ⊤
  · grw [htop] at hn
    have hrw : n = ⊤ := by
      exact ENat.map_eq_top_iff.mp (Eq.symm hn)
    grw [hrw, ENat.epow_top, ← le_top]
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
  have hRP : (M ／ {e}).RankPos := by sorry --I think here you need n ≠ 0
  have hM' : NoUniformMinor (M ／ {e}) (a + 1) (b + 1) := by sorry
  have hn' : (M ／ {e}).eRank = a + (n - 1) := by sorry
  have ih := rankCoverNumber_le_binomial (M := M ／ {e}) (a := a) (b := b) ha hb hM' (n := n - 1)
  sorry
termination_by M.eRank

-- `RankPos` hypothesis not needed, because of `a ≠ 0` and `hn`.
lemma rankCoverNumber_le_binomial_subset [(M ↾ Y).RankPos] {a b : ℕ} {n : ℕ∞}
    (ha : a ≠ 0) (hb : a ≤ b) (hM : (M ↾ Y).NoUniformMinor (a + 1) (b + 1)) (hn : M.eRk Y = a + n) :
    M.rankCoverNumber Y a ≤ (Nat.choose b a)^n := by
  rw [rankCoverNumber_restriction_eq ]
  exact rankCoverNumber_le_binomial ha hb hM hn

lemma rankCoverNumber_le_binomial_contract {M : Matroid α} {C : Set α} {a b : ℕ} (ha : a ≠ 0)
    (hb : a ≤ b) (hM : NoUniformMinor M (a + 1) (b + 1)) (hC : C ⊂ M.E) : M.rankCoverNumber M.E a ≤
    (Nat.choose b a)^(M.eRk C) * (M ／ C).rankCoverNumber (M ／ C).E a := by
  obtain htop | hlt := eq_or_ne (M.eRk C) ⊤
  · grw [htop, ENat.epow_top, ENat.top_mul, ← le_top ]
    · have heN : (M／ C).Nonempty := by
        rw[←(M／ C).ground_nonempty_iff, contract_ground]
        exact (Set.nonempty_of_ssubset (by grind))
      exact ENat.one_le_iff_ne_zero.mp (one_le_coverNumber
        ((ground_nonempty_iff (M ／ C)).mpr heN) (fun A ↦ (M ／ C).eRk A ≤ a))
    obtain rfl | hlt := hb.eq_or_lt
    · simp [noUniformMinor_self_iff] at hM
      grw [ ←eRk_le_eRank M C, htop ] at hM
      simp only [not_top_lt] at hM
    rw [← ENat.coe_one, ENat.coe_lt_coe]
    suffices b.choose a ≠ 0 ∧ b.choose a ≠ 1 by lia
    exact ⟨(Nat.choose_pos hlt.le).ne.symm, by simp [Nat.choose_eq_one_iff, hlt.ne.symm, ha] ⟩
  obtain h0 | hn := eq_or_ne (M.eRk C) 0
  · rw [h0]
    simp only [ENat.epow_zero, contract_ground, one_mul]
    rw [rankCoverNumber_delete_loop ((eRk_eq_zero_iff (subset_of_ssubset hC)).mp h0)
      (nonempty_of_ssubset hC) (by simp) ]
    suffices h : M.rankCoverNumber (M.E \ C) a = (M ／ C).rankCoverNumber (M.E \ C) ↑a
    · rw [h]
    refine coverNumber_congr (fun A ↦ M.eRk A ≤ ↑a) (fun A ↦ (M ／ C).eRk A ≤ ↑a) ?_
    intro Y hY
    simp only
    rw [contract_eq_delete_of_subset_loops ((eRk_eq_zero_iff (subset_of_ssubset hC)).1 h0)]
    have h : Disjoint Y C := by grind
    simp only [M.delete_eRk_eq h ]
  have hresP : (M ↾ C).RankPos := (eRank_ne_zero_iff (M ↾ C)).mp <|
    by simp [eRank_restrict, ne_eq, hn]
  obtain ⟨e, heC⟩ : ∃ e, (M ↾ C).IsNonloop e := exists_isNonloop (M ↾ C)
  rw [restrict_isNonloop_iff] at heC
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
    exact (Set.nonempty_of_ssubset (by grind))
  have ih := rankCoverNumber_le_binomial_contract (M := M ／ {e}) (C := C \ {e}) (a := a) (b := b) ha
    hb (hM.minor (contract_isMinor M {e})) hsub1
  nth_rw 1 [contract_ground M {e} ] at ih
  grw [rankCoverNumber_from_base (Nat.one_le_iff_ne_zero.mpr ha) hM,
    rankCoverNumber_contract_one heC.1 (mem_of_subset_of_mem (subset_of_ssubset hC) (heC.2))
    (nonempty_of_ssubset' hsub1), ih ]
  simp only [contract_contract, union_diff_self, singleton_union, ge_iff_le, insert_eq_of_mem heC.2,
    ←mul_assoc]
  nth_rw 1 [←eRelRk.eq_1, ←ENat.epow_one (x := ↑(b.choose a)),
    ←ENat.epow_add (x :=  ↑(b.choose a)) (y := 1) (z := (M.eRelRk {e} (C \ {e}))),
    ←add_comm (a := (M.eRelRk {e} (C \ {e}))) (b:= 1),
    (heC.1).eRelRk_add_one_eq, insert_diff_singleton, insert_eq_of_mem heC.2 ]

termination_by M.eRk C

lemma kung_bound  {M : Matroid α} {b : ℕ} [M.RankPos]
    (hM : NoUniformMinor M 2 (b + 2)) :
    M.rankCoverNumber M.E 1 ≤ ∑' (i : {i : ℕ // i < M.eRank}), b^(i.1) := by
  have fn : 1 < b := by sorry
  obtain htop | hfin := eq_or_ne M.eRank ⊤
  · rw [htop]
    have : (∑' (i : {i : ℕ // (i : ℕ∞) < ⊤}), b^(i.1) : ℕ∞) = ⊤ := by
      refine Eq.symm (ENat.eq_of_forall_natCast_le_iff ?_)
      intro n
      refine ⟨?_,?_⟩
      intro hn

      have h1 : (n : ℕ∞ ) ≤ b^ (n : ℕ∞) := by
        have : n < b ^ n := Nat.lt_pow_self fn
        have : n ≤ b ^ n := by exact Nat.le_of_succ_le this
        sorry
      grw [h1]
      sorry
      sorry
    sorry

  have : M.RankFinite := (eRank_ne_top_iff M).mp hfin
  have : Fintype {i : ℕ // (i : ℕ∞) < M.eRank} := by
    refine fintypeOfNotInfinite ?_
    simp only [not_infinite_iff_finite]
    obtain ⟨m, hm ⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [←hm]
    simp only [Nat.cast_lt]
    exact instFiniteSubtypeLtOfLocallyFiniteOrderBot
  rw [tsum_fintype]
  obtain ⟨e, heC⟩ : ∃ e, M.IsNonloop e := exists_isNonloop M
  by_cases hse : ¬M.Nonspanning {e}
  · rw [not_nonspanning_iff] at hse
    have := (ground_nonempty M)
    grw [←heC.eRk_eq, rankCoverNumber_spanning hse ]
    simp only [Nat.cast_sum, Nat.cast_pow, ge_iff_le]
    have h1 : (1 : ℕ∞) ≤ b ^ 0 := by
      simp only [pow_zero, Std.le_refl]
    set f : {i : ℕ // (i : ℕ∞) < M.eRank} → ℕ∞ := (fun x ↦ b^x.1 ) with hfun
    rw [hfun]
    have hh : f ⟨0, eRank_pos M ⟩ ≤ ∑ x : {i : ℕ // (i : ℕ∞) < M.eRank}, (b : ℕ∞)^x.1 := by
      apply Finset.single_le_sum
      · intro i hi
        rw [hfun]
        simp only [zero_le]
      simp only [Finset.mem_univ]
    rw [hfun ] at hh
    simp only at hh
    grw [h1]
    exact hh
  --Start hard case
  simp only [not_not] at hse
  have h' : (M ／ {e}).eRank < M.eRank := by
    rw [← heC.eRank_contractElem_add_one ]
    simp only [ENat.lt_add_left_iff, ne_eq, eRank_eq_top_iff, not_rankInfinite_iff, one_ne_zero,
      not_false_eq_true, and_true, contract_rankFinite]
  have : (M ／ {e}).RankPos := by
    refine (contract_rankPos_iff hse.subset_ground).mpr hse
  have ih := kung_bound (M := M ／ {e}) (hM.minor (contract_isMinor M {e}))
  have hlin : (M.E \ {e}).coverNumber (fun F ↦ ∃ L, M.IsLine L ∧ e ∈ L ∧ F = L \ {e}) ≤
      (M ／ {e}).rankCoverNumber (M ／ {e}).E 1 := by
    rw [rankCoverNumber]
    apply setOf_line_isRankCover heC
  grw [←hlin] at ih
  have h2 : M.rankCoverNumber (M.E \ {e}) 1 ≤
    (M.E \ {e}).coverNumber (fun F ↦ ∃ L, M.IsLine L ∧ e ∈ L ∧ F = L \ {e}) * b := by
    --Here I need the special cover of lines containig e and
    --to prove it has size M.rankCoverNumber (M.E \ {e}) 2
    obtain hT | ⟨T, hT1, hT2 ⟩ := (M.E \ {e}).exists_cover (fun F ↦ ∃ L, M.IsLine L ∧ e ∈ L ∧ F = L \ {e})
    · rw[ hT, ENat.top_mul ]
      simp only [le_top]
      rw [←ENat.coe_zero]
      simp only [Nat.cast_zero, ne_eq, Nat.cast_eq_zero]
      grind
    rw [←hT2, rankCoverNumber]
    apply coverNumber_le_bound hT1
    intro F ⟨L, ⟨hL1, hL2, hL3⟩⟩
    have heq := hL1.2
    rw [←one_add_one_eq_two] at heq
    rw [←rankCoverNumber, ←(Nat.choose_one_right b)]
    have hM' : (M ↾ F).NoUniformMinor (1 + 1) (b + 1) := by
      simp only [Nat.reduceAdd]

      sorry
    have : (M ↾ F).RankPos := by sorry
    have hlie : M.eRk F = 1 + 1 := by sorry
    have := rankCoverNumber_le_binomial_subset (a := 1) (b := b) (by grind) (by grind) hM' hlie
    simp only [Nat.cast_one, Nat.choose_one_right, ENat.epow_one] at this
    simp only [Nat.choose_one_right, ge_iff_le]
    sorry
  grw [ih] at h2
  -- Now just need to use new lemma for X = {w} and Y = M.E \ {e}
  have h3 : M.rankCoverNumber M.E 1 ≤ M.rankCoverNumber (M.E \ {e}) 1 + 1 := by
    sorry
  grw [h3, h2]
  simp only [Nat.cast_sum, Nat.cast_pow]
  have h : ∀ (i : ℕ), ((i : ℕ∞) < (M ／ {e}).eRank) ↔ ((i : ℕ∞) + 1 < M.eRank ):= by sorry
  set f : ℕ → ℕ := (fun x ↦ b^x ) with hfun
  set g : { i : ℕ // (i : ℕ∞) < (M ／ {e}).eRank } → ℕ := fun x ↦ f x.1  with h_g
  rw [h_g]
  rw [tsum_congr_subtype f h, hfun]
  have : Fintype {i : ℕ // (i : ℕ∞) + 1 < M.eRank} := by
    refine fintypeOfNotInfinite ?_
    simp only [not_infinite_iff_finite]
    obtain ⟨m, hm ⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [←hm]
    sorry
  --   --←ENat.coe_one
  --   sorry--simp only [Nat.cast_one]

  --   --simp only [ENat.coe_add, Nat.cast_lt]
  --   --exact instFiniteSubtypeLtOfLocallyFiniteOrderBot
  rw [tsum_fintype ]
  simp only [Nat.cast_sum, Nat.cast_pow]
  rw [ Finset.sum_mul] -- ←ENat.epow_one (x := b),   ENat.epow_natCast (x := (b : ℕ∞)),← ENat.coe_mul (n := b) ]
  nth_rw 2 [←ENat.epow_one (x := b)]


  --rw [(ENat.add_one_lt_add_one_iff (a := (i : ℕ∞)) (b := (M ／ {e}).eRank )).2 ]
  --rw [← heC.eRank_contractElem_add_one ]
  sorry
termination_by M.eRank


end Rank

section Nonspanning


/-- Docstring here -/
def NonspanningCover (M : Matroid α) (T : Set (Set α)) (X : Set α) :=
  T.IsCover X (M ↾ X).Nonspanning

lemma nonspanningCover_iff : NonspanningCover M T X ↔ T.IsCover X (M ↾ X).Nonspanning := Iff.rfl

-- This should be shorter
lemma nonspanningCover_iff_restriction :
    M.NonspanningCover T X ↔ (M ↾ X).NonspanningCover T (M ↾ X).E := by
  refine ⟨?_, ?_ ⟩
  · intro h
    rw [nonspanningCover_iff, restrict_ground_eq, restrict_idem]
    exact nonspanningCover_iff.mp h
  intro h
  rw [nonspanningCover_iff, restrict_ground_eq, restrict_idem] at h
  exact nonspanningCover_iff.mpr h

-- Need to move
lemma spanning_iff_intersection (hF : F ⊆ X) :
    (M ↾ X).Spanning F ↔ (M ↾ X ∩ M.E).Spanning (F ∩ M.E) := by
  rw [restrict_spanning_iff (hR := inter_subset_right) (inter_subset_inter hF fun ⦃a⦄ a_1 ↦ a_1),
  restrict_spanning_iff', ←closure_inter_ground]
  simp only [hF, and_true]

lemma nonspanning_iff_intersection (hF : F ⊆ X) :
    (M ↾ X).Nonspanning F ↔ (M ↾ X ∩ M.E).Nonspanning (F ∩ M.E) := by
  rw [←not_spanning_iff, ←not_spanning_iff (hXE := by grind)]
  refine not_congr (spanning_iff_intersection hF)

lemma nonspanning_empty_intersection (hXE : X ∩ M.E = ∅) (hX : X.Nonempty ) :
    X.coverNumber (M ↾ X).Nonspanning = ⊤ := by
  have hem : {T | IsCover T X (M ↾ X).Nonspanning} = ∅ := by
    by_contra! hc
    obtain ⟨T, hT⟩ := hc
    obtain ⟨F, hF⟩ := hT.nonempty hX
    have hcc : (M ↾ X).Spanning F := by
      rw [restrict_spanning_iff']
      refine ⟨?_, hT.subset hF ⟩
      rw [hXE]
      exact empty_subset (M.closure F)
    exact Ne.elim (fun a ↦ ((hT.pProp F hF).not_spanning) hcc) hXE
  exact coverNumber_empty_eq_top hem

lemma nonspanning_intersection_ground (hX : (X ∩ M.E).Nonempty)
    (hns : M.NonspanningCover T (X ∩ M.E)) : M.NonspanningCover ((· ∪ (X \ M.E)) '' T) X := by
  rw [nonspanningCover_iff]
  have : X = (X ∩ M.E) ∪ (X \ M.E) := by grind
  nth_rw 2 [this]
  rw [nonspanningCover_iff] at hns
  refine hns.image_union (Y := X ∩ M.E) (X := X \ M.E) hX ?_
  intro F hF
  by_contra hc
  have hrw : (F ∪ X \ M.E) ∩ M.E = F := by
    refine Subset.antisymm (by simp only [union_inter_distrib_right, diff_inter_self, union_empty,
      inter_subset_left] ) (by simp only [subset_inter_iff, subset_union_left, true_and,
      (hF.subset_ground.subset).trans (inter_subset_right)])
  rw [not_nonspanning_iff (hXE := ?_), restrict_spanning_iff', ←closure_inter_ground, hrw] at hc
  exact ((not_spanning_iff (hXE := by grind )).2 hF)
    ((restrict_spanning_iff (hR := by grind) (by grind)).2 hc.1 )
  simp only [restrict_ground_eq, union_subset_iff, diff_subset_iff, subset_union_right, and_true]
  exact (hF.subset_ground.subset).trans (inter_subset_left)

lemma nonspanning_le_rankCoverNumber {n : ℕ} (hr : M.eRk X = n + 1) :
    X.coverNumber (M ↾ X).Nonspanning ≤ M.rankCoverNumber X n := by
  apply coverNumber_le_coverNumber (fun X ↦ X)
  intro T hT
  simp only [image_id']
  refine ⟨hT.sUnion_eq, ?_⟩
  intro F hF
  have hcon := hT.pProp F hF
  apply nonspanning_of_eRk_ne (hXE := by simp only [restrict_ground_eq, hT.subset hF])
  simp only [restrict_eRk_eq M (hT.subset hF), eRank_restrict, ne_eq, hr]
  enat_to_nat!
  grind

lemma top_le_nonspanning (hX : X.Nonempty) (hle : M.eRk X ≤ 1) :
    ⊤ ≤ X.coverNumber (M ↾ X).Nonspanning := by
  obtain hT | ⟨T, hT1, hT2 ⟩  := X.exists_cover (M ↾ X).Nonspanning
  · rw[ hT ]
  by_contra hc
  have : (M ↾ X).RankFinite := by
    refine eRank_lt_top_iff.mp ?_
    simp only [eRank_restrict]
    grw[hle]
    exact ENat.one_lt_top
  have hu := hT1.sUnion_eq
  have hl : ∀ T1 ∈ T, T1 ⊆ (M ↾ X).loops := by
    intro T1 hT'
    have h1 := Nonspanning.eRk_lt (hT1.pProp T1 hT')
    rw [←eRank_restrict] at hle
    grw [hle] at h1
    simp only [ENat.lt_one_iff] at h1
    exact ((M ↾ X).eRk_eq_zero_iff (X := T1) (hT1.subset hT')).1 h1
  have hs : (M ↾ X).E ⊆ (M ↾ X).loops := by
    nth_rw 1 [←hT1.sUnion_eq]
    exact sUnion_subset hl
  obtain ⟨T', hT' ⟩ := hT1.nonempty hX
  have h2 : (M ↾ X).E ⊆ (M ↾ X).closure T' := by
    grw [hs]
    exact loops_subset_closure (M ↾ X) T'
  exact Ne.elim (fun a ↦ ((hT1.pProp T' hT').not_spanning) ((spanning_iff_ground_subset_closure
    (hT1.subset hT')).2 h2)) hT2

lemma nonspanning_singleton (he : e ∈ M.E) (hM : 2 ≤ M.eRank) : M.Nonspanning {e} := by
    by_contra hc
    have h1 : M.eRank ≤ 1 := by
      rw [not_nonspanning_iff] at hc
      rw [←hc.eRk_eq]
      simp only [eRk_singleton_le]
    grw [←hM] at h1
    simp only [ENat.not_ofNat_le_one] at h1

lemma isCover_singleton_nonspanning (hM : 2 ≤ M.eRk X) :
    NonspanningCover M (singleton '' X) X :=
  isCover_image_singleton (fun _ he ↦ nonspanning_singleton he hM)

lemma nonspanningNumber_le (hM : 2 ≤ M.eRk X) :
    X.coverNumber ((M ↾ X).Nonspanning) ≤ X.encard :=
  isCover_singleton_le (fun _ he ↦ nonspanning_singleton he hM)

lemma nonspanning_hasCover (hM : 2 ≤ M.eRk X) : X.HasCover ((M ↾ X).Nonspanning) :=
  ⟨(singleton '' X), isCover_singleton_nonspanning hM ⟩

lemma nonspanningNumber_intersection_ground (hX : (X ∩ M.E).Nonempty) :
    X.coverNumber (M ↾ X).Nonspanning = (X ∩ M.E).coverNumber (M ↾ X ∩ M.E).Nonspanning := by
  by_cases h2 : 2 ≤ M.eRk X
  · have h1 : (X ∩ M.E).coverNumber (M ↾ X ∩ M.E).Nonspanning ≤ X.coverNumber (M ↾ X).Nonspanning :=
    coverNumber_le_coverNumber_intersect X M.E
      (fun F hF hFns ↦ (nonspanning_iff_intersection hF).mp hFns)
    have h3 : X.coverNumber (M ↾ X).Nonspanning ≤ (X ∩ M.E).coverNumber (M ↾ X ∩ M.E).Nonspanning
        := by
      rw [←eRk_inter_ground M X] at h2
      obtain ⟨T, hT, hTen⟩ := exists_encard_eq_coverNumber (nonspanning_hasCover h2)
      have hcov := nonspanning_intersection_ground hX hT
      rw [nonspanningCover_iff] at hcov
      grw [←hTen, hcov.coverNumber_le]
      exact encard_image_le (fun x ↦ x ∪ X \ M.E) T
    grind
  have := top_le_nonspanning (Nonempty.left hX) (Order.le_of_lt_succ (not_le.1 h2))
  rw [←eRk_inter_ground M X] at h2
  have := top_le_nonspanning (hX) (Order.le_of_lt_succ (not_le.1 h2))
  grind

lemma nonspanning_image_union (h : NonspanningCover (M ／ C) T (M.E \ C)) (hX : C ⊆ M.E)
    (hXN : (M ／ C).Nonempty) : NonspanningCover M ((· ∪ C) '' T) M.E := by
  rw [nonspanningCover_iff] at h
  rw [nonspanningCover_iff]
  have : (M.E \ C ∪ C) = M.E := by grind
  nth_rw 1 [← this]
  rw [←Matroid.ground_nonempty_iff, contract_ground] at hXN
  apply h.image_union (X := C) hXN
  intro F hF
  have h3 :  (M ／ C ↾ M.E \ C) = M ／ C := by
    simp only [restrict_eq_self_iff, contract_ground]
  rw [h3] at hF
  simp only [restrict_ground_eq_self]
  by_contra hc
  have hcc : (M ／ C).Spanning F := by
    have hr : F ∪ C ⊆ M.E := by
      refine union_subset ?_ hX
      have := hF.subset_ground
      grind
    rw [not_nonspanning_iff hr] at hc
    refine (contract_spanning_iff hX).mpr ⟨hc, by grind⟩
  rw [←not_spanning_iff (hF.subset_ground)] at hF
  exact Ne.elim (fun a ↦ hF hcc) h3

lemma nonspanning_image_union_subset (h : NonspanningCover (M ／ C) T (Y \ C))
    (hX : C ⊆ Y) (hY : (Y \ C).Nonempty) : NonspanningCover M ((· ∪ C) '' T) Y := by
  have h1 : NonspanningCover ((M ↾ Y) ／ C) T (((M ↾ Y)).E \ C) := by
    simp only [restrict_ground_eq]
    refine ⟨h.sUnion_eq , ?_ ⟩
    intro F  hF
    rw [restrict_contract_eq_contract_restrict M hX, restrict_idem]
    exact h.pProp F hF
  rw [nonspanningCover_iff_restriction ]
  exact nonspanning_image_union h1 (IsLoopEquiv.subset_ground rfl hX)
    ((ground_nonempty_iff ((M ↾ Y) ／ C)).mp hY)

lemma nonspanningNumber_le_contract (hX : C ⊆ M.E) (hXN : (M ／ C).Nonempty) :
    M.E.coverNumber M.Nonspanning ≤ (M.E \ C).coverNumber (M ／ C).Nonspanning := by
  obtain hT | ⟨T, hT, hTe ⟩ := (M.E \ C).exists_cover (M ／ C).Nonspanning
  · rw [hT]
    exact OrderTop.le_top (M.E.coverNumber M.Nonspanning)
  rw [← hTe]
  rw [←(restrict_ground_eq_self (M ／ C)), contract_ground M C,
    ←nonspanningCover_iff (T := T) (X := M.E \ C) (M := M ／ C)] at hT
  have hrw2 := ((nonspanning_image_union hT hX hXN).coverNumber_le)
  simp only [restrict_ground_eq_self] at hrw2
  exact
    Std.IsPreorder.le_trans (M.E.coverNumber M.Nonspanning) ((fun x ↦ x ∪ C) '' T).encard T.encard
      hrw2 (encard_image_le (fun x ↦ x ∪ C) T)

lemma nonspanningNumber_le_contract_subset (hX : C ⊆ Y) (hYne : (Y \ C).Nonempty) :
    Y.coverNumber (M ↾ Y).Nonspanning ≤ (Y \ C).coverNumber ((M ／ C) ↾ (Y \ C)).Nonspanning := by
  obtain hT | ⟨T, hT, hTe ⟩ := (Y \ C).exists_cover ((M ／ C) ↾ (Y \ C)).Nonspanning
  · rw [hT]
    exact OrderTop.le_top (Y.coverNumber (M ↾ Y).Nonspanning)
  rw [← hTe]
  rw [←nonspanningCover_iff (T := T) (X := Y \ C) (M := M ／ C)] at hT
  exact
    Std.IsPreorder.le_trans (Y.coverNumber (M ↾ Y).Nonspanning)
      ((fun x ↦ x ∪ C) '' T).encard T.encard
      ((nonspanning_image_union_subset hT hX hYne).coverNumber_le)
      (encard_image_le (fun x ↦ x ∪ C) T)

lemma nonspanningNumber_set_closure (hY : Y ⊆ M.closure X) (hX : X ⊆ M.E) :
    X.coverNumber (M ↾ X).Nonspanning ≤ (X ∪ Y).coverNumber (M ↾ (X ∪ Y)).Nonspanning := by
  obtain hT | ⟨T, hT, hTe ⟩ := (X ∪ Y).exists_cover (M ↾ (X ∪ Y)).Nonspanning
  · rw [hT]
    exact OrderTop.le_top (X.coverNumber (M ↾ X).Nonspanning)
  rw [← hTe]

  have hcov : NonspanningCover M ((fun x ↦ x ∩ X) '' T) X := by
    refine ⟨?_, ?_ ⟩
    · refine subset_antisymm (sUnion_subset fun K ↦ ?_) fun e he ↦ ?_
      · intro hK
        obtain ⟨K', hK'T, hK' ⟩ := hK
        rw [← hK']
        grind
      have h1 := hT.sUnion_eq
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
      (closure_subset_closure M (inter_subset_left)) (hc a_1)) (LE.le.subset fun ⦃a⦄ a_1 ↦
      (closure_subset_closure M (inter_subset_left)) ((LE.le.subset fun ⦃a⦄ a_1 ↦
      (closure_subset_closure_of_subset_closure hc) (hY a_1)) a_1))
    rw [←restrict_spanning_iff (hR := by grind), ←not_nonspanning_iff (by grind)  ] at hcc
    have := (hT.pProp F' hF')
    exact Ne.elim (fun a ↦ hcc (hT.pProp F' hF')) hTe
    exact LE.le.subset (hT.subset hF')
  grw [hcov.coverNumber_le ]
  exact encard_image_le (fun x ↦ x ∩ X) T

end Nonspanning
