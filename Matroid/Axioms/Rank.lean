import Matroid.ForMathlib.Other
import Matroid.Minor.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Data.ENat.Basic

open Set

/-- A matroid as defined by the (relative) rank axioms. The constructed
  `RankMatroid` can be then converted into a `Matroid` with `RankMatroid.matroid` -/
structure RankMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The (relative) rank function -/
  (eRelRk : Set α → Set α → ℕ∞)

  (eRelRk_le_encard_diff : ∀ A B, eRelRk A B ≤ (B \ A).encard)
  (eRelRk_union_le_eRelRk_inter : ∀ A B, eRelRk A (A ∪ B) ≤ eRelRk (A ∩ B) B)
  (eRelRk_add_cancel : ∀ ⦃A B C⦄, A ⊆ B → B ⊆ C → eRelRk A C = eRelRk A B + eRelRk B C)
  (eRelRk_diff_eq_zero : ∀ ⦃A B : Set α⦄, A ⊆ B →
    (∀ e ∈ B \ A, eRelRk A (insert e A) = 0) → eRelRk A B = 0)

  (eRelRk_compl_ground_eq : eRelRk ∅ Eᶜ = 0)
  (eRelRk_eq_union_right : ∀ A B, eRelRk A B = eRelRk A (B ∪ A))

  (Indep : Set α → Prop)
  (indep_maximal : ∀ ⦃X⦄, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  (indep_iff : ∀ ⦃I⦄, Indep I ↔ ∀ x ∈ I, eRelRk (I \ {x}) I ≠ 0)

namespace RankMatroid

variable {α : Type*} {A B I J X : Set α} {x : α} {M : RankMatroid α}

@[simp] lemma eRelRk_self_eq_zero : M.eRelRk A A = 0 := by
  obtain h := M.eRelRk_le_encard_diff A A
  simpa only [sdiff_self, bot_eq_empty, encard_empty, nonpos_iff_eq_zero] using h

lemma eRelRk_insert_eq_one_of_ne (h : M.eRelRk A (insert x A) ≠ 0) :
    M.eRelRk A (insert x A) = 1 := by
  refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 h)
  refine (M.eRelRk_le_encard_diff _ _).trans ?_
  simp only [← singleton_union, union_diff_right]
  exact (encard_le_encard diff_subset).trans_eq <| by simp

lemma eRelRk_eq_diff_right : M.eRelRk A B = M.eRelRk A (B \ A) := by
  rw [M.eRelRk_eq_union_right A (B \ A), diff_union_self, eRelRk_eq_union_right]

lemma eRelRk_mono_right (M : RankMatroid α) (hAB : A ⊆ B) : M.eRelRk X A ≤ M.eRelRk X B := by
  rw [M.eRelRk_eq_union_right _ A, M.eRelRk_eq_union_right _ B,
    M.eRelRk_add_cancel subset_union_right (union_subset_union_left X hAB)]
  simp only [self_le_add_right]

lemma eRelRk_mono_left (M : RankMatroid α) (hAB : A ⊆ B) :
    M.eRelRk B X ≤ M.eRelRk A X := by
  calc
    M.eRelRk B X = M.eRelRk B (X ∪ B) := by rw [eRelRk_eq_union_right]
    _ ≤ M.eRelRk (A ∪ B) ((A ∪ B) ∪ (A ∪ X)) := by
      rw [← union_union_distrib_left, ← union_assoc, union_eq_self_of_subset_left hAB, union_comm]
    _ ≤ M.eRelRk ((A ∪ B) ∩ (A ∪ X)) (A ∪ X) := M.eRelRk_union_le_eRelRk_inter _ _
    _ = M.eRelRk (A ∪ (B ∩ X)) (A ∪ X) := by rw [union_inter_distrib_left]
    _ ≤ M.eRelRk A (A ∪ (B ∩ X)) + M.eRelRk (A ∪ (B ∩ X)) (A ∪ X) := le_add_self
    _ = M.eRelRk A (A ∪ X) := by rw [M.eRelRk_add_cancel subset_union_left <|
      show (A ∪ (B ∩ X)) ⊆ (A ∪ X) from union_subset_union (subset_refl A) inter_subset_right]
    _ = M.eRelRk A X := by rw [union_comm, ← eRelRk_eq_union_right]

lemma eRelRk_eq_zero_aux (M : RankMatroid α) (A B : Set α) : M.eRelRk A (A ∪ (B \ M.E)) = 0 := by
  rw [eRelRk_eq_diff_right, union_diff_left, le_antisymm_iff, and_iff_left (by simp),
    ← M.eRelRk_compl_ground_eq]
  refine (M.eRelRk_mono_left (empty_subset _)).trans (M.eRelRk_mono_right ?_)
  exact diff_subset.trans <| diff_subset_compl _ _

@[simp] lemma eRelRk_inter_ground_left {M : RankMatroid α} (A B : Set α) :
    M.eRelRk (A ∩ M.E) B = M.eRelRk A B := by
  have h0 : 0 = M.eRelRk (A ∩ M.E) A := by simp [← M.eRelRk_eq_zero_aux (A ∩ M.E) A]
  refine (M.eRelRk_mono_left inter_subset_left).antisymm' ?_
  rw [M.eRelRk_eq_union_right (A := A), ← zero_add (M.eRelRk A _), h0,
    ← M.eRelRk_add_cancel inter_subset_left subset_union_right]
  apply M.eRelRk_mono_right subset_union_left

@[simp] lemma eRelRk_inter_ground_right {M : RankMatroid α} (A B : Set α) :
    M.eRelRk A (B ∩ M.E) = M.eRelRk A B := by
  rw [M.eRelRk_eq_union_right (B := B ∩ M.E), ← add_zero (M.eRelRk _ (B ∩ M.E ∪ A)),
    ← M.eRelRk_eq_zero_aux (B ∩ M.E ∪ A) B, union_right_comm, inter_union_diff,
    ← M.eRelRk_add_cancel subset_union_right, eq_comm, eRelRk_eq_union_right]
  exact union_subset_union_left _ inter_subset_left

lemma eRelRk_inter_ground {M : RankMatroid α} : M.eRelRk (A ∩ M.E) (B ∩ M.E) = M.eRelRk A B := by
  simp

lemma Indep.subset_ground (h : M.Indep I) : I ⊆ M.E := by
  refine fun e heI ↦ by_contra fun heE ↦ ?_
  have h' := M.indep_iff.1 h e heI
  rw [← eRelRk_inter_ground, ← inter_diff_right_comm, inter_diff_assoc,
    diff_singleton_eq_self heE, eRelRk_self_eq_zero] at h'
  exact h' rfl

lemma Indep.eRelRk_diff_singleton {M : RankMatroid α} (h : M.Indep I) (hx : x ∈ I) :
    M.eRelRk (I \ {x}) I = 1 := by
  simpa [hx, M.indep_iff.1 h] using M.eRelRk_insert_eq_one_of_ne (A := I \ {x}) (x := x)

lemma Indep.subset {M : RankMatroid α} (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I := by
  refine M.indep_iff.2 fun x hxI ↦ Ne.symm <| LT.lt.ne ?_
  have hr := M.eRelRk_union_le_eRelRk_inter (J \ {x}) I
  rwa [diff_union_eq_union_of_subset _ (by simpa), union_eq_self_of_subset_right hIJ,
    hJ.eRelRk_diff_singleton (hIJ hxI), Order.one_le_iff_pos,
    ← inter_diff_right_comm, inter_eq_self_of_subset_right hIJ] at hr

lemma Indep.insert_indep_of_eRelRk_ne_zero (hI : M.Indep I) (hx : M.eRelRk I (insert x I) ≠ 0) :
    M.Indep (insert x I) := by
  suffices ∀ a ∈ I, ¬M.eRelRk (insert x I \ {a}) (insert x I) = 0 by
    simpa [M.indep_iff, M.eRelRk_add_cancel diff_subset (subset_insert _ _), hx]
  intro a haI hr
  have h' := M.eRelRk_union_le_eRelRk_inter I (insert x I \ {a})
  have hcon := M.eRelRk_add_cancel (show I \ {a} ⊆ I from diff_subset) (subset_insert x I)
  have hax : x ≠ a := by rintro rfl; simp [haI] at hx
  rw [eRelRk_insert_eq_one_of_ne hx, hI.eRelRk_diff_singleton haI, M.eRelRk_add_cancel
      (show I \ {a} ⊆ insert x I \ {a} from diff_subset_diff_left (subset_insert _ _)) diff_subset,
      hr, add_zero, ← insert_diff_singleton_comm hax,
      eRelRk_insert_eq_one_of_ne (by simp [hcon])] at hcon
  norm_num at hcon

lemma Indep.subset_maximal_iff_eRelRk_zero (hI : M.Indep I) (hIX : I ⊆ X) :
    Maximal (fun S ↦ M.Indep S ∧ S ⊆ X) I ↔ M.eRelRk I X = 0 := by
  refine ⟨fun h ↦ M.eRelRk_diff_eq_zero hIX fun e heX ↦ by_contra fun hne ↦ heX.2 ?_, fun h ↦ ?_⟩
  · exact h.mem_of_prop_insert
      ⟨hI.insert_indep_of_eRelRk_ne_zero hne, insert_subset heX.1 h.prop.2⟩
  rw [maximal_iff_forall_insert (fun I J hJ hIJ ↦ ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩),
    and_iff_right hI, and_iff_right hIX]
  intro e heI ⟨hi, hins⟩
  have hrr : ¬M.eRelRk I (insert e I) = 0 := by
    rw [indep_iff] at hi
    simpa [diff_singleton_eq_self heI] using hi e (mem_insert _ _)
  have hzero := M.eRelRk_add_cancel (subset_insert e I) hins
  rw [h, eq_comm, add_eq_zero] at hzero
  exact hrr hzero.1

lemma Indep.aug (hI : M.Indep I) (hInotmax : ¬ Maximal M.Indep I) (hBmax : Maximal M.Indep B) :
    ∃ e ∈ B \ I, M.Indep (insert e I) := by
  have hrw : M.Indep = fun J ↦ M.Indep J ∧ J ⊆ M.E := by
    simp +contextual [funext_iff, Indep.subset_ground]

  have hB : M.Indep B := hBmax.prop
  rw [hrw, hB.subset_maximal_iff_eRelRk_zero hB.subset_ground] at hBmax

  have h0 : M.eRelRk (I ∪ B) M.E = 0 := by
    simpa [hBmax, nonpos_iff_eq_zero]
      using M.eRelRk_mono_left (show B ⊆ I ∪ B from subset_union_right) (X := M.E)

  rw [hrw, hI.subset_maximal_iff_eRelRk_zero hI.subset_ground,
    M.eRelRk_add_cancel subset_union_left (union_subset hI.subset_ground hB.subset_ground),
    h0, add_zero, ← hI.subset_maximal_iff_eRelRk_zero subset_union_left] at hInotmax

  obtain ⟨e, heI, hi, hinx⟩ := exists_insert_of_not_maximal
    (fun I J hJ hIJ ↦ ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩) ⟨hI, subset_union_left⟩ hInotmax

  exact ⟨e, ⟨by simpa [insert_subset_iff, heI] using hinx, heI⟩, hi⟩

lemma Indep.eRelRk_subset (hJ : M.Indep J) (hIJ : I ⊆ J) : M.eRelRk I J = (J \ I).encard := by
  classical
  suffices aux : ∀ (D : Finset α), Disjoint I D → (D : Set α) ⊆ J → D.card ≤ M.eRelRk I (I ∪ D) by
    rw [le_antisymm_iff, and_iff_right (eRelRk_le_encard_diff _ _ _)]
    obtain hfin | hinf := (J \ I).finite_or_infinite
    · simpa [disjoint_sdiff_right, diff_subset, union_eq_self_of_subset_left hIJ,
        hfin.encard_eq_coe_toFinset_card] using aux hfin.toFinset
    rw [hinf.encard_eq, top_le_iff, ENat.eq_top_iff_forall_ge]
    refine fun m ↦ ?_
    obtain ⟨D, hDss, rfl⟩ := hinf.exists_subset_card_eq m
    refine (aux D (Disjoint.mono_right hDss disjoint_sdiff_right) (hDss.trans diff_subset)).trans ?_
    exact M.eRelRk_mono_right (union_subset hIJ (hDss.trans diff_subset))

  intro D
  induction' D using Finset.induction with e S heS IH
  · simp
  rw [Finset.coe_insert, insert_subset_iff, ← union_singleton, disjoint_union_right,
    disjoint_singleton_right, and_imp, and_imp, union_singleton, S.card_insert_of_notMem heS,
    Nat.cast_add, Nat.cast_one, union_insert,
    M.eRelRk_add_cancel subset_union_left (subset_insert _ _)]

  intro hdj heI heJ hSJ
  specialize IH hdj hSJ
  rwa [M.eRelRk_insert_eq_one_of_ne, WithTop.add_le_add_iff_right (by simp)]

  have hi : M.Indep (insert e (I ∪ S)) := hJ.subset (insert_subset heJ (union_subset hIJ hSJ))
  rw [indep_iff] at hi
  simpa [diff_singleton_eq_self (show e ∉ I ∪ S by simp [heI, heS])] using hi e

@[simps! E Indep] protected def matroid (M : RankMatroid α) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.mk
  (E := M.E)
  (Indep := M.Indep)
  (indep_empty := by simp [M.indep_iff])
  (indep_subset := fun _ _ ↦ Indep.subset)
  (indep_aug := fun _ _ ↦ Indep.aug)
  (indep_maximal := fun X hX ↦ M.indep_maximal hX)
  (subset_ground := fun I hI ↦ hI.subset_ground)

@[simp] lemma matroid_eRelRk_eq (M : RankMatroid α) (X Y : Set α) :
    M.matroid.eRelRk X Y = M.eRelRk X Y := by
  suffices h : ∀ {A B}, A ⊆ B → B ⊆ M.E → M.eRelRk A B = M.matroid.eRelRk A B by
    rw [← eRelRk_inter_ground, eRelRk_eq_union_right, ← Matroid.eRelRk_inter_ground_left,
      ← Matroid.eRelRk_inter_ground_right, matroid_E, Matroid.eRelRk_eq_union_right]
    apply (h _ _).symm <;> simp
  intro X Y hXY hY
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M.matroid.exists_isBasis_subset_isBasis hXY
  rw [hI.eRelRk_eq_encard_diff_of_subset_isBasis hJ hIJ, ← Indep.eRelRk_subset hJ.indep hIJ]
  have h1 := M.eRelRk_add_cancel hIJ hJ.subset
  have h2 := M.eRelRk_add_cancel hI.subset hXY
  rw [(Indep.subset_maximal_iff_eRelRk_zero hI.indep hI.subset).1 hI.1, zero_add] at h2
  rw [(Indep.subset_maximal_iff_eRelRk_zero hJ.indep hJ.subset).1 hJ.1, add_zero] at h1
  rw [← h1, h2]

end RankMatroid

/-- A `ℕ`-valued rank function with domain `Finset α`. Can be converted into a (finitary)
matroid using `FinsetRankMatroid.matroid`. -/
structure FinsetRankMatroid (α : Type*) [DecidableEq α] where
  E : Set α
  r : Finset α → ℕ
  rk_empty : r ∅ = 0
  rk_singleton : ∀ e, r {e} ≤ 1
  rk_insert_insert : ∀ X e f, r X + r (insert e (insert f X)) ≤ r (insert e X) + r (insert f X)
  rk_singleton_of_notMem_ground : ∀ e ∉ E, r {e} = 0

namespace FinsetRankMatroid

variable {α : Type*} {X Y I J : Finset α} {e f : α} [DecidableEq α] {M : FinsetRankMatroid α}

lemma rk_mono {X Y : Finset α} (h : X ⊆ Y) : M.r X ≤ M.r Y := by
  obtain rfl | hss := h.eq_or_ssubset; rfl
  obtain ⟨e, heX, heXY⟩ := Finset.ssubset_iff.1 hss
  have : (Y \ insert e X).card < (Y \ X).card := by
    refine Finset.card_lt_card <| Finset.ssubset_iff.2 ⟨e, ?_⟩
    simp [Finset.insert_subset_iff, heX, (Finset.insert_subset_iff.1 heXY).1]
    exact Finset.sdiff_subset_sdiff Subset.rfl (Finset.subset_insert _ _)
  exact le_trans (by simpa using M.rk_insert_insert X e e) <| FinsetRankMatroid.rk_mono heXY
termination_by (Y \ X).card

lemma rk_insert_le : M.r (insert e X) ≤ M.r X + M.r {e} := by
  induction' X using Finset.induction with f X _ hX
  · simp [rk_empty]
  linarith [M.rk_insert_insert X e f]

lemma rk_insert_le_add_one : M.r (insert e X) ≤ M.r X + 1 := by
  refine rk_insert_le.trans (add_le_add_left (M.rk_singleton e) _)

lemma rk_le_card : M.r X ≤ X.card := by
  induction' X using Finset.induction with e X heX hX
  · simp [rk_empty]
  rw [Finset.card_insert_of_notMem (by simpa)]
  exact rk_insert_le_add_one.trans (add_le_add_right hX 1)

lemma indep_empty : M.r ∅ = (∅ : Finset α).card :=
  le_antisymm M.rk_le_card <| by simp

lemma indep_subset (hJ : M.r J = J.card) (hIJ : I ⊆ J) : M.r I = I.card := by
  suffices h' : ∀ I D : Finset α, (I ∪ D).card ≤ M.r (I ∪ D) → M.r I = I.card from
    h' _ J <| by simpa [Finset.union_eq_right.2 hIJ] using hJ.symm.le
  intro I D
  induction' D using Finset.induction with e D heD hD
  · simp only [Finset.union_empty]
    exact fun h ↦ h.antisymm' M.rk_le_card
  rw [Finset.union_insert]
  by_cases heI : e ∈ I
  · rwa [Finset.insert_eq_of_mem (by simp [heI])]
  refine fun hle ↦ hD ?_
  replace hle := hle.trans rk_insert_le_add_one
  rwa [Finset.card_insert_of_notMem (by simp [heI, heD]), add_le_add_iff_right] at hle

lemma indep_aug' (hI : M.r I = I.card) (hlt : M.r I < M.r X) :
    ∃ e ∈ X, e ∉ I ∧ M.r (insert e I) = (insert e I).card := by
  by_contra! hcon
  have haux : ∀ S ⊆ X \ I, M.r (I ∪ S) = M.r I := fun S ↦ by
    induction' S using Finset.induction with e S heS ih
    · simp
    simp only [Finset.insert_subset_iff, Finset.mem_sdiff, Finset.union_insert, and_imp]
    intro heX heI hSJI
    induction' S using Finset.induction with f S _ ih'
    · rw [Finset.union_empty, le_antisymm_iff, ← Nat.lt_add_one_iff,
        hI, ← I.card_insert_of_notMem heI, lt_iff_le_and_ne, and_iff_right M.rk_le_card,
        and_iff_right (hcon e heX heI), ← hI, Finset.insert_eq, Finset.union_comm]
      apply M.rk_mono Finset.subset_union_left
    specialize ih hSJI
    have hsm := M.rk_insert_insert (I ∪ S) e f
    simp only [Finset.mem_insert, not_or] at heS
    have hIS : M.r (I ∪ S) = M.r I := by
      rw [← ih, Finset.union_insert, le_antisymm_iff, Finset.insert_eq, Finset.union_comm {f},
        and_iff_right (M.rk_mono Finset.subset_union_left), Finset.union_assoc, S.union_comm,
        ← S.insert_eq, ih]
      apply M.rk_mono I.subset_union_left
    rw [Finset.insert_subset_iff] at hSJI
    rw [ih' heS.2 (fun _ ↦ hIS) hSJI.2, ← Finset.union_insert, ih, hIS] at hsm
    exact le_antisymm (by linarith) <|
      M.rk_mono <| Finset.subset_union_left.trans (Finset.subset_insert _ _)
  have h' : M.r (X ∪ I) = M.r I := by simpa [X.union_comm] using haux _ Finset.Subset.rfl
  exact hlt.not_ge <| le_trans (M.rk_mono Finset.subset_union_left) h'.le

lemma indep_aug (hI : M.r I = I.card) (hJ : M.r J = J.card) (hlt : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ M.r (insert e I) = (insert e I).card :=
  indep_aug' hI (by rwa [hI, hJ])

lemma indep_support (hI : M.r I = I.card) : (I : Set α) ⊆ M.E := by
  refine fun e heI ↦ by_contra fun heE ↦ ?_
  have hle := (rk_insert_le (X := I.erase e) (e := e)).trans
    (add_le_add_right M.rk_le_card _)
  rw [Finset.insert_erase (by simpa using heI), M.rk_singleton_of_notMem_ground e heE,
    add_zero, hI, ← Finset.card_erase_add_one (by simpa using heI)] at hle
  simp at hle

/-- `FinsetRankMatroid α` gives an `Matroid α`; their rank functions agree on finsets.  -/
@[simps! E] protected def matroid (M : FinsetRankMatroid α) : Matroid α :=
   IndepMatroid.matroid <| IndepMatroid.ofFinset M.E (fun I ↦ M.r I = I.card)
    indep_empty (fun _ _ ↦ indep_subset) (fun _ _ ↦ indep_aug) (fun _ ↦ indep_support)

@[simp] protected lemma matroid_indep_iff {I : Finset α} : M.matroid.Indep I ↔ M.r I = I.card := by
  simp [FinsetRankMatroid.matroid]

instance : M.matroid.Finitary := by
  rw [FinsetRankMatroid.matroid, IndepMatroid.ofFinset]
  infer_instance

protected lemma matroid_indep_iff' {I : Set α} :
    M.matroid.Indep I ↔ ∀ J : Finset α, (J : Set α) ⊆ I → M.r J = J.card := by
  simp [FinsetRankMatroid.matroid, IndepMatroid.ofFinset_indep']

@[simp] protected lemma matroid_rk_eq (X : Finset α) : M.matroid.rk X = M.r X := by
  obtain ⟨I, hI⟩ := M.matroid.exists_isBasis' X
  obtain ⟨I, rfl⟩ := (X.finite_toSet.subset hI.subset).exists_finset_coe
  rw [← hI.card, ncard_coe_finset, ← FinsetRankMatroid.matroid_indep_iff.1 hI.indep]
  refine (M.rk_mono (by simpa using hI.subset)).antisymm <| le_of_not_gt fun hlt ↦ ?_
  obtain ⟨e, heX, heI, hr⟩ := M.indep_aug' (by simpa using hI.indep) hlt
  have hi : M.matroid.Indep (insert e I) := by
    rwa [← Finset.coe_insert, FinsetRankMatroid.matroid_indep_iff]
  exact heI <| by simpa using hI.mem_of_insert_indep (e := e) (by simpa) hi

@[simp] protected lemma matroid_eRk_eq (X : Finset α) : M.matroid.eRk X = M.r X := by
  rw [← Matroid.cast_rk_eq_eRk_of_finite _ (by simp), FinsetRankMatroid.matroid_rk_eq]

protected lemma matroid_eRk_eq_sup (X : Set α) :
    M.matroid.eRk X = ⨆ Y ∈ {Y : Finset α | (Y : Set α) ⊆ X}, (M.r Y : ℕ∞) := by
  refine le_antisymm ?_ ?_
  set S := {Y : Finset α | (Y : Set α) ⊆ X}
  · obtain ⟨I, hI⟩ := M.matroid.exists_isBasis' X
    obtain (hIfin | hIinf) := I.finite_or_infinite
    · obtain ⟨I, rfl⟩ := hIfin.exists_finset_coe
      rw [← hI.eRk_eq_eRk, FinsetRankMatroid.matroid_eRk_eq]
      exact le_biSup (f := fun X ↦ (M.r X : ℕ∞)) hI.subset
    suffices h : ⨆ Y ∈ S, (M.r Y : ℕ∞) = ⊤ by rw [h]; apply le_top
    rw [ENat.eq_top_iff_forall_ge]
    intro b
    obtain ⟨J, hJI, rfl⟩ := hIinf.exists_subset_card_eq b
    rw [← FinsetRankMatroid.matroid_indep_iff.1 (hI.indep.subset hJI)]
    apply le_biSup _ (show J ∈ S from hJI.trans hI.subset)
  simp only [mem_setOf_eq, ← FinsetRankMatroid.matroid_eRk_eq, iSup_le_iff]
  exact fun Y hYX ↦ M.matroid.eRk_mono hYX

/-- A rank function on `Finset`s that is bounded above by cardinality, monotone and submodular
gives rise to a `FinsetRankMatroid`. -/
def ofFinitaryRankAxioms [DecidableEq α]
    (E : Set α)
    (r : Finset α → ℕ)
    (rank_le_card : ∀ A, r A ≤ A.card)
    (monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B)
    (submodularity : ∀ (A B : Finset α), r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rk_singleton_of_notMem_ground : ∀ e ∉ E, r {e} = 0) :
    FinsetRankMatroid α :=
  { E := E
    r := r
    rk_empty := by simpa using rank_le_card ∅
    rk_singleton := fun e ↦ by simpa using rank_le_card {e}
    rk_insert_insert := fun X e f ↦ by
      obtain (rfl | hne) := eq_or_ne f e
      · simp [monotonicity (X.subset_insert f)]
      by_cases hfX : f ∈ X
      · rw [X.insert_eq_of_mem hfX, add_comm]
      refine le_of_eq_of_le ?_ (submodularity _ _)
      rw [Finset.inter_comm, X.insert_inter_of_notMem (by simp [hfX, hne]),
        Finset.inter_eq_left.2 (by simp), add_comm, Finset.insert_union,
        Finset.union_eq_right.2 (by simp)]
    rk_singleton_of_notMem_ground := rk_singleton_of_notMem_ground }

/-- A rank function on `Set`s that is bounded above by `encard` and is monotone and submodular
gives rise to a `FinsetRankMatroid`. -/
def ofFiniteRankAxioms
    (E : Set α)
    (r : Set α → ℕ)
    (rank_le_encard : ∀ A, r A ≤ A.encard)
    (monotonicity : ∀ ⦃A B⦄, A ⊆ B → r A ≤ r B)
    (submodularity : ∀ A B, r (A ∪ B) + r (A ∩ B) ≤ r A + r B)
    (rank_compl_ground : r Eᶜ = 0) :
    FinsetRankMatroid α :=
  ofFinitaryRankAxioms
  (E := E)
  (r := fun X ↦ r X)
  (rank_le_card := fun A ↦ by
    simpa [encard_coe_eq_coe_finsetCard, Nat.cast_le] using rank_le_encard A)
  (monotonicity := fun _ _ h ↦ monotonicity (by simpa))
  (submodularity := fun A B ↦ by simpa using submodularity A B)
  (rk_singleton_of_notMem_ground := fun e he ↦ by
    simpa using (monotonicity (show {e} ⊆ Eᶜ by simpa)).trans_eq rank_compl_ground )



end FinsetRankMatroid
