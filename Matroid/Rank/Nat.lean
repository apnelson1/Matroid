import Matroid.Rank.Finite

namespace Matroid

open Set ENat

variable {α : Type*} {M : Matroid α} {B I X Y : Set α} {e : α}

section Rank

/-- The `ℕ`-valued rank function, taking a junk value of zero for infinite-rank sets.
Intended to be used in a `FiniteRk` matroid,
or at the very least when the argument is known to be `rFin`; otherwise `Matroid.er` is better.-/
noncomputable def r (M : Matroid α) (X : Set α) : ℕ :=
  ENat.toNat (M.er X)

/-- The `ℕ`-valued rank of the ground set of a matroid.
Has a junk value of `0` for infinite-rank matroids. -/
@[reducible] noncomputable def rk (M : Matroid α) : ℕ :=
  ENat.toNat M.erk

lemma rk_def (M : Matroid α) : M.rk = M.r M.E := by
  rw [rk,r,er,restrict_ground_eq_self]

@[simp] lemma er_toNat_eq_r (M : Matroid α) (X : Set α) : ENat.toNat (M.er X) = M.r X :=
  rfl

lemma Base.ncard (hB : M.Base B) : B.ncard = M.rk := by
  rw [rk_def, ← er_toNat_eq_r, ncard_def, hB.encard, erk_def]

lemma rFin.cast_r_eq (hX : M.rFin X) : (M.r X : ℕ∞) = M.er X := by
  rw [r, coe_toNat (by rwa [er_ne_top_iff])]

lemma cast_r_eq_er_of_finite (M : Matroid α) (hX : X.Finite) : (M.r X : ℕ∞) = M.er X :=
  (M.rFin_of_finite hX).cast_r_eq

lemma Finset.cast_r_eq (M : Matroid α) (X : Finset α) : (M.r X : ℕ∞) = M.er X :=
  cast_r_eq_er_of_finite _ (by simp)

@[simp] lemma cast_r_eq (M : Matroid α) [FiniteRk M] (X : Set α) : (M.r X : ℕ∞) = M.er X :=
  (M.to_rFin X).cast_r_eq

@[simp] lemma coe_rk_eq (M : Matroid α) [FiniteRk M] : (M.rk : ℕ∞) = M.erk := by
  rw [erk_def, rk_def, cast_r_eq]

lemma r_eq_of_er_eq (h : M.er X = M.er Y) : M.r X = M.r Y := by
  rw [r, r, h]

lemma rFin.er_eq_er_iff (hX : M.rFin X) (hY : M.rFin Y) : M.er X = M.er Y ↔ M.r X = M.r Y := by
  rw [← hX.cast_r_eq, ← hY.cast_r_eq, Nat.cast_inj]

lemma rFin.er_le_er_iff (hX : M.rFin X) (hY : M.rFin Y) : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := by
  rw [← hX.cast_r_eq, ← hY.cast_r_eq, Nat.cast_le]

@[simp] lemma er_eq_er_iff [FiniteRk M] : M.er X = M.er Y ↔ M.r X = M.r Y :=
  (M.to_rFin X).er_eq_er_iff (M.to_rFin Y)

@[simp] lemma er_le_er_iff [FiniteRk M] : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := by
  rw [← cast_r_eq, ← cast_r_eq, Nat.cast_le]

@[simp] lemma er_eq_coe_iff [FiniteRk M] {n : ℕ} : M.er X = n ↔ M.r X = n := by
  rw [← cast_r_eq, Nat.cast_inj]

@[simp] lemma er_le_coe_iff [FiniteRk M] {n : ℕ} : M.er X ≤ n ↔ M.r X ≤ n := by
  rw [← cast_r_eq, Nat.cast_le]

@[simp] lemma coe_le_er_iff [FiniteRk M] {n : ℕ} : (n : ℕ∞) ≤ M.er X ↔ n ≤ M.r X := by
  rw [← cast_r_eq, Nat.cast_le]

lemma rFin.r_le_r_of_er_le_er (hY : M.rFin Y) (hle : M.er X ≤ M.er Y) : M.r X ≤ M.r Y := by
  rwa [← rFin.er_le_er_iff _ hY]; exact hle.trans_lt hY.lt

lemma r_inter_ground (M : Matroid α) (X : Set α) : M.r (X ∩ M.E) = M.r X := by
  rw [← er_toNat_eq_r, er_inter_ground, er_toNat_eq_r]

lemma le_r_iff [FiniteRk M] {n : ℕ} : n ≤ M.r X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.ncard = n := by
  simp_rw [← coe_le_er_iff, le_er_iff,]
  refine ⟨fun ⟨I, hIX, hI, hc⟩ ↦ ⟨I, hIX, hI, by rw [ncard_def, hc, toNat_coe]⟩,
    fun ⟨I, hIX, hI, hc⟩ ↦ ⟨I, hIX, hI, ?_⟩⟩
  rw [hI.finite.encard_eq_coe, ← hc]; rfl

lemma r_le_iff [FiniteRk M] {n : ℕ} : M.r X ≤ n ↔ ∀ {I}, I ⊆ X → M.Indep I → I.ncard ≤ n := by
  simp_rw [← er_le_coe_iff, er_le_iff, encard_le_coe_iff]
  refine ⟨fun h I hIX hI ↦ ?_, fun h I hIX hI ↦ ⟨hI.finite, ⟨_, hI.finite.encard_eq_coe, h hIX hI⟩⟩⟩
  obtain ⟨-, m, hm, hmn⟩ := h hIX hI
  rwa [ncard_def, hm, toNat_coe]

lemma r_mono (M : Matroid α) [FiniteRk M] : Monotone M.r := by
  rintro X Y (hXY : X ⊆ Y);
  rw [← er_le_er_iff]
  exact M.er_mono hXY

lemma rFin.r_le_of_subset (hY : M.rFin Y) (hXY : X ⊆ Y) : M.r X ≤ M.r Y := by
  rw [r, r, ← Nat.cast_le (α := ℕ∞), coe_toNat (hY.subset hXY).ne, coe_toNat hY.ne]
  exact M.er_mono hXY

lemma r_le_of_subset (M : Matroid α) [FiniteRk M] (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
  M.r_mono hXY

@[simp] lemma r_empty (M : Matroid α) : M.r ∅ = 0 := by
  rw [r, er_empty]; rfl

@[simp] lemma r_closure_eq (M : Matroid α) : M.r (M.closure X) = M.r X := by
  rw [r, er_closure_eq, r]

lemma r_le_rk (M : Matroid α) [FiniteRk M] (X : Set α) : M.r X ≤ M.rk := by
  rw [← r_inter_ground, rk_def]; exact M.r_mono inter_subset_right

lemma r_eq_rk (hX : M.E ⊆ X) : M.r X = M.rk := by
  rw [← r_inter_ground, inter_eq_self_of_subset_right hX, rk_def]

lemma Indep.r_eq_ncard (hI : M.Indep I) : M.r I = I.ncard := by
  rw [← er_toNat_eq_r, hI.er, ncard_def]

lemma Indep.r_eq_card {I : Finset α} (hI : M.Indep I) : M.r I = I.card := by
  rw [hI.r_eq_ncard, ncard_coe_Finset]

lemma r_le_card (M : Matroid α) [Matroid.Finite M] (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.r X ≤ X.ncard :=
  r_le_iff.2 <| fun {I} hI _ ↦ (ncard_le_ncard hI (M.set_finite X))

lemma Indep.ncard_le_r_of_subset [FiniteRk M] (hI : M.Indep I) (h : I ⊆ X) : I.ncard ≤ M.r X := by
  rw [← hI.r_eq_ncard]
  exact M.r_mono h

lemma Indep.ncard_le_rk [FiniteRk M] (hI : M.Indep I) : I.ncard ≤ M.rk :=
  hI.r_eq_ncard.symm.trans_le (M.r_le_rk I)

lemma Indep.base_of_ncard [FiniteRk M] (hI : M.Indep I) (hIcard : M.rk ≤ I.ncard) : M.Base I :=
  hI.base_of_encard hI.finite <| by rwa [← coe_rk_eq, ← hI.finite.cast_ncard_eq, Nat.cast_le]

lemma Indep.base_of_card [FiniteRk M] {I : Finset α} (hI : M.Indep I) (hIcard : M.rk ≤ I.card) :
    M.Base I :=
  hI.base_of_ncard (by simpa)

lemma Basis'.card (h : M.Basis' I X) : I.ncard = M.r X := by
  rw [ncard_def, h.encard, ← er_toNat_eq_r]

lemma Basis'.r_eq_r (h : M.Basis' I X) : M.r I = M.r X := by
  rw [← h.card, h.indep.r_eq_ncard]

lemma Basis.ncard_eq_r (h : M.Basis I X) : I.ncard = M.r X :=
  h.basis'.card

lemma Basis.finset_card {I : Finset α} (hIX : M.Basis I X) : I.card = M.r X := by
  simpa using hIX.ncard_eq_r

lemma Basis'.finset_card {I : Finset α} (hIX : M.Basis' I X) : I.card = M.r X := by
  simpa using hIX.card

lemma Base.finset_card {B : Finset α} (hB : M.Base B) : B.card = M.rk := by
  simpa [rk_def] using hB.basis_ground.ncard_eq_r

lemma r_le_toFinset_card (M : Matroid α) {X : Set α} (hX : X.Finite) :
    M.r X ≤ hX.toFinset.card := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.card, ncard_eq_toFinset_card _ (hX.subset hI.subset)]
  exact Finset.card_mono (by simpa using hI.subset)

lemma r_le_finset_card (M : Matroid α) (X : Finset α) : M.r X ≤ X.card := by
  simpa using M.r_le_toFinset_card X.finite_toSet

lemma Basis.r_eq_r (h : M.Basis I X) : M.r I = M.r X :=
  h.basis'.r_eq_r

lemma r_eq_zero_iff [FiniteRk M] (hX : X ⊆ M.E) : M.r X = 0 ↔ X ⊆ M.closure ∅ := by
  rw [← er_eq_coe_iff, coe_zero, er_eq_zero_iff]

@[simp] lemma r_loops (M : Matroid α) : M.r (M.closure ∅) = 0 := by
  simp [r]

lemma Nonloop.r_eq (he : M.Nonloop e) : M.r {e} = 1 := by
  rw [r, he.er_eq]; rfl

lemma Loop.r_eq (he : M.Loop e) : M.r {e} = 0 := by
  rw [r, he.er_eq]; rfl

lemma Circuit.r_add_one_eq {C : Finset α} (hC : M.Circuit C) : M.r C + 1 = C.card := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, ← encard_coe_eq_coe_finsetCard,
    ← hC.er_add_one_eq, cast_r_eq_er_of_finite _ (by simp), Nat.cast_one]

/-- The `ℕ`-valued rank function is submodular.
If the `X` is finite-rank and `Y` is not,
then this is true due to junk values, so we don't need `M.rFin Y`.  -/
lemma rFin.submod (hX : M.rFin X) (Y : Set α) : M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y := by
  by_cases hY : M.rFin Y
  · obtain ⟨c, h_eq⟩ := le_iff_exists_add.1 <| M.er_inter_add_er_union_le_er_add_er X Y
    obtain (rfl | hc) := eq_or_ne c ⊤
    · rw [add_top, WithTop.add_eq_top] at h_eq
      simp [hX.ne, hY.ne] at h_eq
    have hi : M.rFin (X ∩ Y) := hX.subset inter_subset_left
    have hu : M.rFin (X ∪ Y) := hX.union hY
    rw [← ge_iff_le, r,r, ge_iff_le, ← toNat_add hX.ne hY.ne, h_eq, toNat_add _ hc,
      toNat_add hi.ne hu.ne, ← r, ← r]
    · apply Nat.le_add_right
    rw [Ne, WithTop.add_eq_top, not_or]
    exact ⟨hi.ne, hu.ne⟩
  nth_rewrite 2 [r]
  nth_rewrite 3 [r]
  rw [er_eq_top_iff.2 (fun h ↦ hY <| h.subset subset_union_right), er_eq_top_iff.2 hY,
    toNat_top, add_zero, add_zero]
  refine hX.r_le_of_subset inter_subset_left

lemma rFin.submod_right (hY : M.rFin Y) (X : Set α) :
    M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y := by
  rw [inter_comm, union_comm, add_comm (a := M.r X)]
  apply hY.submod

lemma r_submod (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
  rFin.submod (M.to_rFin X) Y

lemma Indep.exists_insert_of_ncard_lt [FiniteRk M] {J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.ncard < J.ncard) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  apply hI.exists_insert_of_encard_lt hJ
  rw [← hJ.finite.cast_ncard_eq, ← hI.finite.cast_ncard_eq]
  exact Nat.cast_lt.mpr hcard

@[simp] lemma rk_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).rk = M.rk := by
  simp [rk]

lemma r_union_le_r_add_r (M : Matroid α) (X Y : Set α) : M.r (X ∪ Y) ≤ M.r X + M.r Y := by
  by_cases hFin : M.rFin (X ∪ Y)
  · exact (Nat.le_add_left _ _).trans <| rFin.submod (hFin.subset subset_union_left) _
  rw [← er_ne_top_iff, not_not] at hFin
  rw [r, hFin]
  simp

lemma ext_rank {M N : Matroid α} [FiniteRk M] [FiniteRk N] (hE : M.E = N.E)
    (h : ∀ X ⊆ M.E, M.r X = N.r X) : M = N := by
  simp_rw [ext_iff_indep, and_iff_right hE]
  refine fun I hIE ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · rw [indep_iff_er_eq_encard_of_finite hI.finite, ← cast_r_eq_er_of_finite _ hI.finite, ← h _ hIE,
      hI.r_eq_ncard, hI.finite.cast_ncard_eq]
  rw [indep_iff_er_eq_encard_of_finite hI.finite, ← cast_r_eq_er_of_finite _ hI.finite, h _ hIE,
    hI.r_eq_ncard, hI.finite.cast_ncard_eq]

end Rank
