import Matroid.Rank.Finite

namespace Matroid

open Set ENat

variable {α : Type*} {M : Matroid α} {B I X Y : Set α} {e : α}

section Rank

/-- The `ℕ`-valued rank function, taking a junk value of zero for infinite-rank sets.
Intended to be used in a `FiniteRk` matroid,
or at the very least when the argument is known to be `rFin`; otherwise `Matroid.er` is better.-/
noncomputable def rk (M : Matroid α) (X : Set α) : ℕ :=
  ENat.toNat (M.eRk X)

/-- The `ℕ`-valued rank of the ground set of a matroid.
Has a junk value of `0` for infinite-rank matroids. -/
@[reducible] noncomputable def rank (M : Matroid α) : ℕ :=
  ENat.toNat M.eRank

lemma rank_def (M : Matroid α) : M.rank = M.rk M.E := by
  rw [rank,rk,eRk,restrict_ground_eq_self]

@[simp] lemma eRk_toNat_eq_rk (M : Matroid α) (X : Set α) : ENat.toNat (M.eRk X) = M.rk X :=
  rfl

lemma Base.ncard (hB : M.Base B) : B.ncard = M.rank := by
  rw [rank_def, ← eRk_toNat_eq_rk, ncard_def, hB.encard, eRank_def]

lemma rFin.cast_rk_eq (hX : M.rFin X) : (M.rk X : ℕ∞) = M.eRk X := by
  rw [rk, coe_toNat (by rwa [eRk_ne_top_iff])]

lemma cast_rk_eq_eRk_of_finite (M : Matroid α) (hX : X.Finite) : (M.rk X : ℕ∞) = M.eRk X :=
  (M.rFin_of_finite hX).cast_rk_eq

lemma Finset.cast_rk_eq (M : Matroid α) (X : Finset α) : (M.rk X : ℕ∞) = M.eRk X :=
  cast_rk_eq_eRk_of_finite _ (by simp)

@[simp] lemma cast_rk_eq (M : Matroid α) [FiniteRk M] (X : Set α) : (M.rk X : ℕ∞) = M.eRk X :=
  (M.to_rFin X).cast_rk_eq

@[simp] lemma coe_rank_eq (M : Matroid α) [FiniteRk M] : (M.rank : ℕ∞) = M.eRank := by
  rw [eRank_def, rank_def, cast_rk_eq]

lemma rk_eq_of_eRk_eq (h : M.eRk X = M.eRk Y) : M.rk X = M.rk Y := by
  rw [rk, rk, h]

lemma rFin.eRk_eq_eRk_iff (hX : M.rFin X) (hY : M.rFin Y) : M.eRk X = M.eRk Y ↔ M.rk X = M.rk Y := by
  rw [← hX.cast_rk_eq, ← hY.cast_rk_eq, Nat.cast_inj]

lemma rFin.eRk_le_eRk_iff (hX : M.rFin X) (hY : M.rFin Y) : M.eRk X ≤ M.eRk Y ↔ M.rk X ≤ M.rk Y := by
  rw [← hX.cast_rk_eq, ← hY.cast_rk_eq, Nat.cast_le]

@[simp] lemma eRk_eq_eRk_iff [FiniteRk M] : M.eRk X = M.eRk Y ↔ M.rk X = M.rk Y :=
  (M.to_rFin X).eRk_eq_eRk_iff (M.to_rFin Y)

@[simp] lemma eRk_le_eRk_iff [FiniteRk M] : M.eRk X ≤ M.eRk Y ↔ M.rk X ≤ M.rk Y := by
  rw [← cast_rk_eq, ← cast_rk_eq, Nat.cast_le]

@[simp] lemma eRk_eq_coe_iff [FiniteRk M] {n : ℕ} : M.eRk X = n ↔ M.rk X = n := by
  rw [← cast_rk_eq, Nat.cast_inj]

@[simp] lemma eRk_le_coe_iff [FiniteRk M] {n : ℕ} : M.eRk X ≤ n ↔ M.rk X ≤ n := by
  rw [← cast_rk_eq, Nat.cast_le]

@[simp] lemma coe_le_eRk_iff [FiniteRk M] {n : ℕ} : (n : ℕ∞) ≤ M.eRk X ↔ n ≤ M.rk X := by
  rw [← cast_rk_eq, Nat.cast_le]

lemma rFin.rk_le_rk_of_eRk_le_eRk (hY : M.rFin Y) (hle : M.eRk X ≤ M.eRk Y) : M.rk X ≤ M.rk Y := by
  rwa [← rFin.eRk_le_eRk_iff _ hY]; exact hle.trans_lt hY.lt

lemma rk_inter_ground (M : Matroid α) (X : Set α) : M.rk (X ∩ M.E) = M.rk X := by
  rw [← eRk_toNat_eq_rk, eRk_inter_ground, eRk_toNat_eq_rk]

lemma le_rk_iff [FiniteRk M] {n : ℕ} : n ≤ M.rk X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.ncard = n := by
  simp_rw [← coe_le_eRk_iff, le_eRk_iff,]
  refine ⟨fun ⟨I, hIX, hI, hc⟩ ↦ ⟨I, hIX, hI, by rw [ncard_def, hc, toNat_coe]⟩,
    fun ⟨I, hIX, hI, hc⟩ ↦ ⟨I, hIX, hI, ?_⟩⟩
  rw [hI.finite.encard_eq_coe, ← hc]; rfl

lemma rk_le_iff [FiniteRk M] {n : ℕ} : M.rk X ≤ n ↔ ∀ {I}, I ⊆ X → M.Indep I → I.ncard ≤ n := by
  simp_rw [← eRk_le_coe_iff, eRk_le_iff, encard_le_coe_iff]
  refine ⟨fun h I hIX hI ↦ ?_, fun h I hIX hI ↦ ⟨hI.finite, ⟨_, hI.finite.encard_eq_coe, h hIX hI⟩⟩⟩
  obtain ⟨-, m, hm, hmn⟩ := h hIX hI
  rwa [ncard_def, hm, toNat_coe]

lemma rk_mono (M : Matroid α) [FiniteRk M] : Monotone M.rk := by
  rintro X Y (hXY : X ⊆ Y);
  rw [← eRk_le_eRk_iff]
  exact M.eRk_mono hXY

lemma rFin.rk_le_of_subset (hY : M.rFin Y) (hXY : X ⊆ Y) : M.rk X ≤ M.rk Y := by
  rw [rk, rk, ← Nat.cast_le (α := ℕ∞), coe_toNat (hY.subset hXY).ne, coe_toNat hY.ne]
  exact M.eRk_mono hXY

lemma rk_le_of_subset (M : Matroid α) [FiniteRk M] (hXY : X ⊆ Y) : M.rk X ≤ M.rk Y :=
  M.rk_mono hXY

@[simp] lemma rk_empty (M : Matroid α) : M.rk ∅ = 0 := by
  rw [rk, eRk_empty]; rfl

@[simp] lemma rk_closure_eq (M : Matroid α) : M.rk (M.closure X) = M.rk X := by
  rw [rk, eRk_closure_eq, rk]

lemma rk_le_rank (M : Matroid α) [FiniteRk M] (X : Set α) : M.rk X ≤ M.rank := by
  rw [← rk_inter_ground, rank_def]; exact M.rk_mono inter_subset_right

lemma rk_eq_rank (hX : M.E ⊆ X) : M.rk X = M.rank := by
  rw [← rk_inter_ground, inter_eq_self_of_subset_right hX, rank_def]

lemma Indep.rk_eq_ncard (hI : M.Indep I) : M.rk I = I.ncard := by
  rw [← eRk_toNat_eq_rk, hI.er, ncard_def]

lemma Indep.rk_eq_card {I : Finset α} (hI : M.Indep I) : M.rk I = I.card := by
  rw [hI.rk_eq_ncard, ncard_coe_Finset]

lemma rk_le_card (M : Matroid α) [Matroid.Finite M] (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.rk X ≤ X.ncard :=
  rk_le_iff.2 <| fun {I} hI _ ↦ (ncard_le_ncard hI (M.set_finite X))

lemma Indep.ncard_le_rk_of_subset [FiniteRk M] (hI : M.Indep I) (h : I ⊆ X) : I.ncard ≤ M.rk X := by
  rw [← hI.rk_eq_ncard]
  exact M.rk_mono h

lemma Indep.ncard_le_rank [FiniteRk M] (hI : M.Indep I) : I.ncard ≤ M.rank :=
  hI.rk_eq_ncard.symm.trans_le (M.rk_le_rank I)

lemma Indep.base_of_ncard [FiniteRk M] (hI : M.Indep I) (hIcard : M.rank ≤ I.ncard) : M.Base I :=
  hI.base_of_encard hI.finite <| by rwa [← coe_rank_eq, ← hI.finite.cast_ncard_eq, Nat.cast_le]

lemma Indep.base_of_card [FiniteRk M] {I : Finset α} (hI : M.Indep I) (hIcard : M.rank ≤ I.card) :
    M.Base I :=
  hI.base_of_ncard (by simpa)

lemma Basis'.card (h : M.Basis' I X) : I.ncard = M.rk X := by
  rw [ncard_def, h.encard, ← eRk_toNat_eq_rk]

lemma Basis'.rk_eq_rk (h : M.Basis' I X) : M.rk I = M.rk X := by
  rw [← h.card, h.indep.rk_eq_ncard]

lemma Basis.ncard_eq_rk (h : M.Basis I X) : I.ncard = M.rk X :=
  h.basis'.card

lemma Basis.finset_card {I : Finset α} (hIX : M.Basis I X) : I.card = M.rk X := by
  simpa using hIX.ncard_eq_rk

lemma Basis'.finset_card {I : Finset α} (hIX : M.Basis' I X) : I.card = M.rk X := by
  simpa using hIX.card

lemma Base.finset_card {B : Finset α} (hB : M.Base B) : B.card = M.rank := by
  simpa [rank_def] using hB.basis_ground.ncard_eq_rk

lemma rk_le_toFinset_card (M : Matroid α) {X : Set α} (hX : X.Finite) :
    M.rk X ≤ hX.toFinset.card := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.card, ncard_eq_toFinset_card _ (hX.subset hI.subset)]
  exact Finset.card_mono (by simpa using hI.subset)

lemma rk_le_finset_card (M : Matroid α) (X : Finset α) : M.rk X ≤ X.card := by
  simpa using M.rk_le_toFinset_card X.finite_toSet

lemma Basis.rk_eq_rk (h : M.Basis I X) : M.rk I = M.rk X :=
  h.basis'.rk_eq_rk

lemma rk_eq_zero_iff [FiniteRk M] (hX : X ⊆ M.E) : M.rk X = 0 ↔ X ⊆ M.closure ∅ := by
  rw [← eRk_eq_coe_iff, coe_zero, eRk_eq_zero_iff]

@[simp] lemma rk_loops (M : Matroid α) : M.rk (M.closure ∅) = 0 := by
  simp [rk]

lemma Nonloop.rk_eq (he : M.Nonloop e) : M.rk {e} = 1 := by
  rw [rk, he.eRk_eq]; rfl

lemma Loop.rk_eq (he : M.Loop e) : M.rk {e} = 0 := by
  rw [rk, he.eRk_eq]; rfl

lemma Circuit.rk_add_one_eq {C : Finset α} (hC : M.Circuit C) : M.rk C + 1 = C.card := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, ← encard_coe_eq_coe_finsetCard,
    ← hC.eRk_add_one_eq, cast_rk_eq_eRk_of_finite _ (by simp), Nat.cast_one]

/-- The `ℕ`-valued rank function is submodular.
If the `X` is finite-rank and `Y` is not,
then this is true due to junk values, so we don't need `M.rFin Y`.  -/
lemma rFin.submod (hX : M.rFin X) (Y : Set α) : M.rk (X ∩ Y) + M.rk (X ∪ Y) ≤ M.rk X + M.rk Y := by
  by_cases hY : M.rFin Y
  · obtain ⟨c, h_eq⟩ := le_iff_exists_add.1 <| M.eRk_inter_add_eRk_union_le_eRk_add_eRk X Y
    obtain (rfl | hc) := eq_or_ne c ⊤
    · rw [add_top, WithTop.add_eq_top] at h_eq
      simp [hX.ne, hY.ne] at h_eq
    have hi : M.rFin (X ∩ Y) := hX.subset inter_subset_left
    have hu : M.rFin (X ∪ Y) := hX.union hY
    rw [← ge_iff_le, rk,rk, ge_iff_le, ← toNat_add hX.ne hY.ne, h_eq, toNat_add _ hc,
      toNat_add hi.ne hu.ne, ← rk, ← rk]
    · apply Nat.le_add_right
    rw [Ne, WithTop.add_eq_top, not_or]
    exact ⟨hi.ne, hu.ne⟩
  nth_rewrite 2 [rk]
  nth_rewrite 3 [rk]
  rw [eRk_eq_top_iff.2 (fun h ↦ hY <| h.subset subset_union_right), eRk_eq_top_iff.2 hY,
    toNat_top, add_zero, add_zero]
  refine hX.rk_le_of_subset inter_subset_left

lemma rFin.submod_right (hY : M.rFin Y) (X : Set α) :
    M.rk (X ∩ Y) + M.rk (X ∪ Y) ≤ M.rk X + M.rk Y := by
  rw [inter_comm, union_comm, add_comm (a := M.rk X)]
  apply hY.submod

lemma rk_submod (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.rk (X ∩ Y) + M.rk (X ∪ Y) ≤ M.rk X + M.rk Y :=
  rFin.submod (M.to_rFin X) Y

lemma Indep.exists_insert_of_ncard_lt [FiniteRk M] {J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.ncard < J.ncard) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  apply hI.exists_insert_of_encard_lt hJ
  rw [← hJ.finite.cast_ncard_eq, ← hI.finite.cast_ncard_eq]
  exact Nat.cast_lt.mpr hcard

@[simp] lemma rank_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).rank = M.rank := by
  simp [rank]

lemma rk_union_le_rk_add_rk (M : Matroid α) (X Y : Set α) : M.rk (X ∪ Y) ≤ M.rk X + M.rk Y := by
  by_cases hFin : M.rFin (X ∪ Y)
  · exact (Nat.le_add_left _ _).trans <| rFin.submod (hFin.subset subset_union_left) _
  rw [← eRk_ne_top_iff, not_not] at hFin
  rw [rk, hFin]
  simp

lemma ext_rank {M N : Matroid α} [FiniteRk M] [FiniteRk N] (hE : M.E = N.E)
    (h : ∀ X ⊆ M.E, M.rk X = N.rk X) : M = N := by
  simp_rw [ext_iff_indep, and_iff_right hE]
  refine fun I hIE ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · rw [indep_iff_eRk_eq_encard_of_finite hI.finite, ← cast_rk_eq_eRk_of_finite _ hI.finite, ← h _ hIE,
      hI.rk_eq_ncard, hI.finite.cast_ncard_eq]
  rw [indep_iff_eRk_eq_encard_of_finite hI.finite, ← cast_rk_eq_eRk_of_finite _ hI.finite, h _ hIE,
    hI.rk_eq_ncard, hI.finite.cast_ncard_eq]

end Rank
