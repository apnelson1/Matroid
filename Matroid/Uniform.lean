import Matroid.Constructions.Truncate
import Matroid.ForMathlib.FinDiff
import Mathlib.Combinatorics.Matroid.Sum -- inefficient import
import Matroid.Simple
import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.Minor.Iso
import Matroid.ForMathlib.Card
import Matroid.ForMathlib.Set

variable {α : Type*} {M : Matroid α} {E I B X Y C : Set α} {k : ℕ} {e f : α}

universe u

open Set Set.Notation

@[simp] lemma pair_subsingleton_iff {x y : α} : ({x, y} : Set α).Subsingleton ↔ x = y := by
  aesop

namespace Matroid

section Uniform

/-- The uniform matroid with ground set `E`, whose independent sets are the finite sets of size
at most `k`. -/
def unifOn {α : Type*} (E : Set α) (k : ℕ) : Matroid α := (freeOn E).truncateTo k

@[simp] theorem unifOn_ground_eq (E : Set α) : (unifOn E k).E = E := rfl

@[simp] theorem unifOn_indep_iff : (unifOn E k).Indep I ↔ I.encard ≤ k ∧ I ⊆ E := by
  simp [unifOn, and_comm]

@[simp] theorem unifOn_zero (E : Set α) : unifOn E 0 = loopyOn E := by
  simp [unifOn]

@[simp] theorem unifOn_empty (α : Type*) (a : ℕ) : unifOn ∅ a = emptyOn α := by
  simp [unifOn]

theorem unifOn_eq_of_le (h : E.encard ≤ k) : unifOn E k = freeOn E := by
  rw [unifOn, truncate_eq_self_of_rank_le (by rwa [eRank_freeOn])]

theorem unifOn_isBase_iff (hk : k ≤ E.encard) (hBE : B ⊆ E) :
    (unifOn E k).IsBase B ↔ B.encard = k := by
  rw [unifOn, truncateTo_isBase_iff, freeOn_indep_iff, and_iff_right hBE]
  rwa [eRank_freeOn]

theorem unifOn_eRk_eq (E : Set α) (k : ℕ) (hX : X ⊆ E) : (unifOn E k).eRk X = min X.encard k := by
  rw [unifOn, truncateTo_eRk_eq, eRk_freeOn hX]

theorem unifOn_eRk_eq' (E : Set α) (k : ℕ) : (unifOn E k).eRk X = min (X ∩ E).encard k := by
  rw [← eRk_inter_ground, unifOn_eRk_eq _ _ (by rw [unifOn_ground_eq]; apply inter_subset_right),
    unifOn_ground_eq]

@[simp] theorem unifOn_eRank_eq (E : Set α) (k : ℕ) : (unifOn E k).eRank = min E.encard k := by
  rw [eRank_def, unifOn_ground_eq, unifOn_eRk_eq _ _ Subset.rfl]

theorem unifOn_eRank_eq' (hle : k ≤ E.encard) : (unifOn E k).eRank = k := by
  rw [unifOn_eRank_eq, min_eq_right hle]

theorem unifOn_rank_eq (hk : (k : ℕ∞) ≤ E.encard) : (unifOn E k).rank = k := by
  rw [rank, unifOn_eRank_eq, min_eq_right hk, ENat.toNat_coe]

instance {k : ℕ} {E : Set α} : RankFinite (unifOn E k) := by
  rw [← isRkFinite_ground_iff_rankFinite, ← eRk_lt_top_iff,
    unifOn_eRk_eq _ _ (by simp)]
  exact (min_le_right _ _).trans_lt (WithTop.coe_lt_top _)

theorem unifOn_dual_eq {k : ℕ} (hE : E.Finite) :
    (unifOn E k)✶ = unifOn E (hE.toFinset.card - k) := by
  classical
  obtain ⟨E, rfl⟩ := hE.exists_finset_coe
  obtain (hle | hlt) := le_or_gt E.card k
  · rw [unifOn_eq_of_le (by simpa), freeOn_dual_eq, tsub_eq_zero_of_le (by simpa), unifOn_zero]

  refine ext_isBase (by simp) (fun B hBE ↦ ?_)
  obtain ⟨B, rfl⟩ := (hE.subset hBE).exists_finset_coe
  simp only [dual_ground, unifOn_ground_eq] at hBE
  replace hlt := hlt.le

  rw [dual_isBase_iff, unifOn_isBase_iff (by simpa) (by simpa using diff_subset),
    unifOn_ground_eq, unifOn_isBase_iff (by simp) hBE, ← Finset.coe_sdiff,
    encard_coe_eq_coe_finsetCard, Nat.cast_inj, encard_coe_eq_coe_finsetCard, Nat.cast_inj,
    toFinite_toFinset, E.toFinset_coe, Finset.card_sdiff_of_subset (by simpa),
    tsub_eq_iff_eq_add_of_le (Finset.card_mono (by simpa)),
    eq_tsub_iff_add_eq_of_le (by simpa), add_comm, eq_comm]

lemma unifOn_dual_eq' {j k : ℕ} (hE : E.encard = k + j) : (unifOn E k)✶ = unifOn E j := by
  have hEfin : E.Finite := by rw [← encard_lt_top_iff]; enat_to_nat!
  rw [hEfin.encard_eq_coe_toFinset_card, ← Nat.cast_add, Nat.cast_inj] at hE
  rw [unifOn_dual_eq hEfin, hE, Nat.add_sub_cancel_left]

lemma unifOn_dual_eq_of_le {k : ℕ} (hEfin : E.Finite) (hle : k ≤ E.encard) :
    ∃ (j : ℕ), j ≤ E.encard ∧ k + j = E.encard ∧ (unifOn E k)✶ = unifOn E j := by
  obtain ⟨j, hj⟩ := exists_add_of_le hle
  rw [← encard_lt_top_iff] at hEfin
  generalize hn : E.encard = n at *
  enat_to_nat
  rw [hj, Nat.cast_add] at hn
  exact ⟨j, by omega, hj.symm, unifOn_dual_eq' hn⟩

theorem unifOn_spanning_iff' : (unifOn E k).Spanning X ↔ (k ≤ X.encard ∧ X ⊆ E) ∨ X = E := by
  rw [spanning_iff_eRk', eRank_def, unifOn_ground_eq, unifOn_eRk_eq', unifOn_eRk_eq',
    le_min_iff, min_le_iff, min_le_iff, iff_true_intro (le_refl _), or_true, and_true, inter_self]
  refine ⟨fun ⟨h, hXE⟩ ↦ h.elim (fun h ↦ ?_) (fun h ↦ Or.inl ⟨?_,hXE⟩),
    fun h ↦ h.elim (fun ⟨hle, hXE⟩ ↦ ⟨Or.inr (by rwa [inter_eq_self_of_subset_left hXE]), hXE⟩ ) ?_⟩
  · refine X.finite_or_infinite.elim (fun hfin ↦ .inr ?_) (fun hinf ↦ .inl ⟨?_, hXE⟩)
    · rw [← (hfin.inter_of_left E).eq_of_subset_of_encard_le inter_subset_right h,
        inter_eq_self_of_subset_left hXE]
    rw [hinf.encard_eq]
    apply le_top
  · exact h.trans (encard_mono inter_subset_left)
  rintro rfl
  rw [inter_self]
  exact ⟨Or.inl rfl.le, Subset.rfl⟩

theorem unifOn_spanning_iff {k : ℕ} (hk : k ≤ E.encard) (hX : X ⊆ E) :
    (unifOn E k).Spanning X ↔ k ≤ X.encard := by
  rw [unifOn_spanning_iff', and_iff_left hX, or_iff_left_iff_imp]
  rintro rfl
  assumption

theorem unifOn_spanning_iff'' {k : ℕ} (hk : k ≤ E.encard) :
    (unifOn E k).Spanning X ↔ k ≤ X.encard ∧ X ⊆ E := by
  rw [unifOn_spanning_iff', and_or_right, or_iff_left_of_imp (by rintro rfl; simpa),
    or_iff_left_of_imp (fun h ↦ h.le)]

theorem eq_unifOn_iff : M = unifOn E k ↔ M.E = E ∧ ∀ I, M.Indep I ↔ I.encard ≤ k ∧ I ⊆ E :=
  ⟨by rintro rfl; simp,
    fun ⟨hE, h⟩ ↦ ext_indep (by simpa) fun I _↦ by simpa using h I⟩

@[simp] theorem unifOn_delete_eq (E D : Set α) (k : ℕ) : (unifOn E k) ＼ D = unifOn (E \ D) k := by
  simp_rw [eq_unifOn_iff, delete_ground, unifOn_ground_eq, true_and, delete_indep_iff,
    unifOn_indep_iff, subset_diff, and_assoc, imp_true_iff]

theorem unifOn_contract_finset_eq {C : Finset α} (hCE : (C : Set α) ⊆ E) :
    ((unifOn E k) ／ (C : Set α)) = unifOn (E \ (C : Set α)) (k - C.card) := by
  obtain hle | hle := Nat.le_or_le k C.card
  · rw [tsub_eq_zero_of_le hle, unifOn_zero]
    exact contract_eq_loopyOn_of_spanning <| by simp [unifOn_spanning_iff', hle, hCE]
  have hC : (unifOn E k).Indep C
  · rw [unifOn_indep_iff, and_iff_left hCE]
    simpa using hle
  refine ext_indep rfl fun I (hIE : I ⊆ E \ C) ↦ ?_
  rw [subset_diff] at hIE
  simp [hC.contract_indep_iff, unifOn_indep_iff, hIE.1, hCE, subset_diff, hIE.2,
    encard_union_eq hIE.2]
  rw [← WithTop.add_le_add_iff_right (x := I.encard) (z := C.card) (by simp),
    tsub_add_cancel_of_le (by simpa)]

theorem unifOn_contractElem (heE : e ∈ E) : (unifOn E (k+1)) ／ {e} = unifOn (E \ {e}) k := by
  simpa using unifOn_contract_finset_eq (C := {e}) (E := E) (k := (k+1)) (by simpa)

theorem unifOn_insert_contractElem (he : e ∉ E) :
    (unifOn (insert e E) (k+1)) ／ {e} = unifOn E k := by
  rw [unifOn_contractElem (mem_insert ..), insert_diff_of_mem _ (by simp),
    diff_singleton_eq_self he]

-- @[simp] theorem unifOn_contract_eq {k : ℕ} :
--     ((unifOn E k) ／ C) = unifOn (E \ C) (k - (E ∩ C).encard) :=
--   unifOn_contract_eq' E C WithTop.coe_ne_top

instance unifOn_isLoopless (E : Set α) : Loopless (unifOn E (k+1)) := by
  simp_rw [loopless_iff_forall_isNonloop, ← indep_singleton, unifOn_indep_iff]
  simp

instance unifOn_simple (E : Set α) : Simple (unifOn E (k+2)) := by
  simp only [simple_iff_forall_pair_indep, unifOn_indep_iff, unifOn_ground_eq, pair_subset_iff]
  exact fun {e f} he hf ↦ ⟨(encard_pair_le e f).trans (by simp), he, hf⟩

@[simp] lemma circuitOn_dual (E : Set α) : (circuitOn E)✶ = unifOn E 1 := by
  obtain rfl | ⟨f, hf⟩ := E.eq_empty_or_nonempty
  · simp
  refine ext_indep rfl fun I (hIE : I ⊆ E) ↦ ?_
  rw [← coindep_def, coindep_iff_compl_spanning, circuitOn_spanning_iff ⟨f, hf⟩, unifOn_indep_iff,
    and_iff_left hIE, circuitOn_ground, Nat.cast_one, encard_le_one_iff_subsingleton]
  simp_rw [subset_antisymm_iff, insert_subset_iff, and_iff_left diff_subset,
    ← diff_singleton_subset_iff]
  refine ⟨fun ⟨e, heE, he⟩ ↦ subsingleton_of_subset_singleton (a := e) ?_, fun h ↦ ?_⟩
  · rwa [Set.diff_subset_diff_iff_subset (by simpa using heE) hIE] at he
  obtain rfl | ⟨e, rfl⟩ := h.eq_empty_or_singleton
  · exact ⟨f, hf, by simp⟩
  exact ⟨e, by simpa using hIE, rfl.subset⟩

@[simp] lemma unifOn_isCircuit_iff {n : ℕ} :
    (unifOn E n).IsCircuit C ↔ C.encard = n + 1 ∧ C ⊆ E := by
  obtain hCE | hCE := em' (C ⊆ E)
  · simp [hCE, show ¬ (unifOn E n).IsCircuit C from fun h ↦ hCE h.subset_ground]

  rw [isCircuit_iff_dep_forall_diff_singleton_indep, and_iff_left hCE, ← not_indep_iff,
    unifOn_indep_iff, and_iff_left hCE, not_le, ← ENat.add_one_le_iff (by simp)]

  obtain rfl | ⟨e, heC⟩ := C.eq_empty_or_nonempty
  · simp [eq_comm]

  simp_rw [unifOn_indep_iff]

  refine ⟨fun h ↦ (h.1.eq_of_not_lt fun hlt ↦ (h.2 e heC).1.not_gt ?_).symm,
    fun h ↦ ⟨h.symm.le, fun e heC ↦ ⟨Eq.le ?_, diff_subset.trans hCE⟩⟩⟩
  · rwa [← encard_diff_singleton_add_one heC, WithTop.add_lt_add_iff_right (by simp)] at hlt
  rwa [← encard_diff_singleton_add_one heC, WithTop.add_right_inj (by simp)] at h

lemma unifOn_coindep_iff' {n : ℕ} (hIE : I ⊆ E) :
    (unifOn E n).Coindep I ↔ (n ≤ (E \ I).encard ∨ I = ∅) := by
  rw [coindep_iff_compl_spanning, unifOn_spanning_iff', unifOn_ground_eq, and_iff_left diff_subset,
    sdiff_eq_left, disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_right hIE]

lemma unifOn_coindep_iff {n : ℕ} (hIE : I ⊆ E) (hnE : n ≤ E.encard) :
    (unifOn E n).Coindep I ↔ n ≤ (E \ I).encard := by
  simp +contextual [unifOn_coindep_iff' hIE, hnE]

lemma unifOn_coindep_iff'' {n : ℕ} (hnE : n ≤ E.encard) :
    (unifOn E n).Coindep I ↔ n ≤ (E \ I).encard ∧ I ⊆ E := by
  by_cases hIE : I ⊆ E
  · rw [unifOn_coindep_iff hIE hnE, and_iff_left hIE]
  exact iff_of_false (fun h ↦ hIE h.subset_ground) (by simp [hIE])

lemma unifOn_isHyperplane_iff {n : ℕ} {H : Set α} (hnE : n ≤ E.encard) :
    (unifOn E n).IsHyperplane H ↔ H.encard + 1 = n ∧ H ⊆ E := by
  wlog hHE : H ⊆ E with aux
  · exact iff_of_false (fun h ↦ hHE h.subset_ground) (by simp [hHE])
  rw [isHyperplane_iff_maximal_nonspanning, and_iff_left hHE]
  have h' : H.encard < n ↔ H.encard + 1 ≤ n := by generalize H.encard = a; enat_to_nat! <;> omega
  -- enat_to_nat! failure in the line above; doesn't generalize `H.encard` correctly.
  rw [maximal_iff_forall_insert (fun _ _ h hst ↦ h.subset hst), ← not_spanning_iff,
    unifOn_spanning_iff hnE hHE, not_le, h', le_antisymm_iff, and_congr_right_iff]
  refine fun hle ↦ ⟨fun hmax ↦ not_lt.1 fun hlt ↦ ?_, fun hle' x hxH hns ↦ hns.not_spanning ?_⟩
  · obtain rfl | hssu := hHE.eq_or_ssubset
    · enat_to_nat!; omega
    obtain ⟨e, heE, heH⟩ := exists_of_ssubset hssu
    have heHE : insert e H ⊆ E := insert_subset heE hHE
    specialize hmax e heH
    rw [not_nonspanning_iff heHE, unifOn_spanning_iff hnE heHE, encard_insert_of_notMem heH] at hmax
    exact hlt.not_ge hmax
  rwa [unifOn_spanning_iff hnE hns.subset_ground, encard_insert_of_notMem hxH]

lemma unifOn_isCocircuit_iff {n : ℕ} {K : Set α} (hnE : n ≤ E.encard) :
    (unifOn E n).IsCocircuit K ↔ (E \ K).encard + 1 = n ∧ K ⊆ E := by
  wlog hKE : K ⊆ E with aux
  · exact iff_of_false (fun h ↦ hKE h.subset_ground) (by simp [hKE])
  rw [← isHyperplane_compl_iff_isCocircuit, unifOn_isHyperplane_iff hnE]
  simp [hKE, diff_subset]

section unif

variable {a b a' b' : ℕ}

/-- The canonical finite uniform matroid on ground type `Fin b`,
whose independent sets are those of cardinality at most `a`. -/
def unif (a b : ℕ) : Matroid (Fin b) := unifOn univ a

@[simp] theorem unif_ground_eq (a b : ℕ) : (unif a b).E = univ := rfl

@[simp] theorem unif_indep_iff (I) : (unif a b).Indep I ↔ I.encard ≤ a := by
  rw [unif, unifOn_indep_iff, and_iff_left (subset_univ _)]

@[simp] theorem unif_eRk_eq (X) : (unif a b).eRk X = min X.encard a := by
  rw [unif, unifOn_eRk_eq _ _ (subset_univ _)]

@[simp] theorem unif_eRank_eq (a b : ℕ) : (unif a b).eRank = min a b := by
  rw [eRank_def, unif_eRk_eq]
  simp only [unif_ground_eq, min_comm, encard_univ_fin]; rfl

@[simp] theorem unif_rank_eq (a b : ℕ) : (unif a b).rank = min a b := by
  rw [rank, unif_eRank_eq, ENat.toNat_coe]

theorem unif_eRank_eq_of_le (hab : a ≤ b) : (unif a b).eRank = a := by
  simpa

theorem unif_isBase_iff (hab : a ≤ b) {B : Set (Fin b)} : (unif a b).IsBase B ↔ B.encard = a := by
  rw [unif, unifOn, truncateTo_isBase_iff, freeOn_indep_iff, and_iff_right (subset_univ _)]
  rwa [eRank_freeOn, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, Nat.cast_le]

@[simp] theorem unif_isBase_iff' {B : Set (Fin _)} : (unif a (a + b)).IsBase B ↔ B.encard = a := by
  rw [unif_isBase_iff (Nat.le_add_right _ _)]

@[simp] theorem unif_isCircuit_iff {C : Set (Fin b)} :
    (unif a b).IsCircuit C ↔ C.encard = a + 1 := by
  rw [unif, unifOn_isCircuit_iff, and_iff_left (subset_univ _)]

theorem unif_dual' {n : ℕ} (h : a + b = n) : (unif a n)✶ = unif b n := by
  subst h
  refine ext_isBase rfl (fun B _ ↦ ?_)
  rw [dual_isBase_iff, unif_ground_eq, unif_isBase_iff (Nat.le_add_right _ _),
    unif_isBase_iff (Nat.le_add_left _ _),
    ← WithTop.add_right_inj (encard_ne_top_iff.2 B.toFinite),
    encard_diff_add_encard_of_subset (subset_univ _), Iff.comm,
    ← WithTop.add_left_inj (WithTop.coe_ne_top (a := a)), eq_comm]
  convert Iff.rfl
  rw [encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.some_eq_coe, eq_comm,
    Nat.cast_add]

@[simp] theorem unif_add_left_dual (a b : ℕ) : (unif a (a + b))✶ = unif b (a+b) :=
  unif_dual' rfl

@[simp] theorem unif_add_right_dual (a b : ℕ) : (unif b (a + b))✶ = unif a (a+b) :=
  unif_dual' <| add_comm _ _

instance unif_isLoopless (a b : ℕ) : Loopless (unif (a + 1) b) := by
  rw [unif]
  infer_instance

instance unif_simple (a b : ℕ) : Simple (unif (a + 2) b) := by
  rw [unif]
  infer_instance

@[simp] theorem unif_zero (b : ℕ) : unif 0 b = loopyOn univ := by
  simp [eq_loopyOn_iff]

theorem unif_eq_freeOn (h : b ≤ a) : unif a b = freeOn univ := by
  simpa [eq_freeOn_iff]

/-- The expression for dual of a uniform matroid.
  The junk case where `b < a` still works because the subtraction truncates. -/
theorem unif_dual (a b : ℕ) : (unif a b)✶ = unif (b - a) b := by
  obtain (hab | hba) := le_or_gt a b
  · exact unif_dual' (Nat.add_sub_of_le hab)
  simp [unif_eq_freeOn hba.le, Nat.sub_eq_zero_of_le hba.le]

theorem unif_sub_dual (a b : ℕ) : (unif (b-a) b)✶ = unif a b := by
  rw [eq_comm, eq_dual_comm, unif_dual]

@[simp] theorem unif_self_dual (a : ℕ) : (unif a (2*a))✶ = unif a (2*a) :=
  unif_dual' (two_mul a).symm

theorem nonempty_iso_unif_iff :
    Nonempty (M ≂ (unif a b)) ↔ ∃ E, (M = unifOn E a ∧ E.encard = b) := by
  refine ⟨fun ⟨e⟩ ↦ ⟨M.E, ?_⟩, ?_⟩
  · rw [eq_unifOn_iff, and_iff_right rfl, and_iff_left <| by simpa using e.toEquiv.encard_eq]
    refine fun I ↦ ?_
    obtain (hIE | hIE) := em' <| I ⊆ M.E
    · exact iff_of_false (fun h ↦ hIE h.subset_ground) (by simp [hIE])
    rw [and_iff_left hIE]
    have hwin := e.indep_image_iff (I := M.E ↓∩ I)
    simp only [Subtype.image_preimage_coe, inter_eq_self_of_subset_right hIE, unif_ground_eq,
      unif_indep_iff] at hwin
    rwa [Subtype.val_injective.encard_image, (EmbeddingLike.injective' _).encard_image,
      encard_preimage_of_injective_subset_range Subtype.val_injective (by simpa)] at hwin
  rintro ⟨E, rfl, hE⟩
  obtain ⟨e⟩ := Fin.nonempty_equiv_iff_encard_eq.2 hE
  refine ⟨e.trans (Equiv.Set.univ (Fin b)).symm, fun I ↦ ?_⟩
  simp only [unifOn_indep_iff, Subtype.val_injective.encard_image, image_subset_iff, unif_ground_eq,
    Equiv.Set.univ, Equiv.trans_apply, Equiv.coe_fn_symm_mk, unif_indep_iff]
  rw [Function.Injective.encard_image (fun _ _ ↦ by simp), and_iff_left_iff_imp]
  exact fun _ ⟨_,hx⟩ _ ↦ hx

theorem nonempty_iso_unif_iff' :
    Nonempty (M ≂ (unif a b)) ↔ (M = unifOn M.E a ∧ M.E.encard = b) := by
  rw [nonempty_iso_unif_iff]
  exact ⟨by rintro ⟨E, rfl, h⟩; simp [h], fun h ↦ ⟨M.E, by simpa⟩⟩

noncomputable def unif_isoRestr_unif (a : ℕ) (hbb' : b ≤ b') : unif a b ≤ir unif a b' :=
  let R : Set (Fin b') := range (Fin.castLE hbb')
  have hM : Nonempty (((unif a b') ↾ R) ≂ unif a b) := by
    refine nonempty_iso_unif_iff.2 ⟨R, ?_⟩
    suffices R.encard = b by simpa [ext_iff_indep]
    rw [show R = range (Fin.castLE hbb') from rfl, ← image_univ, Function.Injective.encard_image,
      encard_univ_fin]
    exact (Fin.castLEEmb hbb').injective
  hM.some.symm.isoRestr.trans ((unif a b').restrict_isRestriction R).isoRestr

noncomputable def unif_isoMinor_contr (a b d : ℕ) : unif a b ≤i unif (a+d) (b+d) := by
  have e := (unif_isoRestr_unif (b-a) (Nat.le_add_right b d)).isoMinor.dual
  rwa [unif_sub_dual, ← Nat.add_sub_add_right b d a, unif_sub_dual] at e

theorem unif_isoMinor_unif_iff {a₁ a₂ d₁ d₂ : ℕ} :
    Nonempty (unif a₁ (a₁ + d₁) ≤i unif a₂ (a₂ + d₂)) ↔ a₁ ≤ a₂ ∧ d₁ ≤ d₂ := by
  refine ⟨fun ⟨e⟩ ↦ ⟨by simpa using e.rank_le, by simpa using IsoMinor.rank_le e.dual⟩, fun h ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h.1
  exact ⟨(unif_isoMinor_contr a₁ (a₁ + d₁) j).trans (unif_isoRestr_unif _ (by linarith)).isoMinor⟩

theorem unif_isoMinor_unif_iff' {a₁ a₂ b₁ b₂ : ℕ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    Nonempty (unif a₁ b₁ ≤i unif a₂ b₂) ↔ a₁ ≤ a₂ ∧ b₁ - a₁ ≤ b₂ - a₂ := by
  obtain ⟨d₁, rfl⟩ := Nat.exists_eq_add_of_le h₁
  obtain ⟨d₂, rfl⟩ := Nat.exists_eq_add_of_le h₂
  rw [add_tsub_cancel_left, add_tsub_cancel_left, unif_isoMinor_unif_iff]

section Infinite

variable {B B' : Set α}

/-- Uniformity as a predicate ; a matroid is uniform if every subset of the ground set
is independent or spanning.
This is mainly useful for infinite matroids, where uniformity is structurally nontrivial. -/
def IsUniform (M : Matroid α) := ∀ ⦃X⦄, X ⊆ M.E → M.Indep X ∨ M.Spanning X

lemma IsUniform.indep_or_spanning (hM : M.IsUniform) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.Indep X ∨ M.Spanning X :=
  hM hX

lemma isUniform_iff : M.IsUniform ↔ ∀ ⦃X⦄, X ⊆ M.E → M.Indep X ∨ M.Spanning X := Iff.rfl

lemma IsUniform.indep_of_nonspanning (hM : M.IsUniform) (h : M.Nonspanning X) : M.Indep X :=
  (or_iff_left h.not_spanning).1 <| hM h.subset_ground

lemma IsUniform.spanning_of_dep (hM : M.IsUniform) (h : M.Dep X) : M.Spanning X :=
  (or_iff_right h.not_indep).1 <| hM h.subset_ground

lemma IsUniform.inter_nonempty_of_dep_codep (hM : M.IsUniform) (hX : M.Dep X) (hcd : M.Codep Y) :
    (X ∩ Y).Nonempty := by
  refine not_disjoint_iff_nonempty_inter.1 fun hdj ↦ ?_
  refine (hcd.nonspanning_compl.subset (subset_diff.2 ⟨hX.subset_ground, hdj⟩)).not_spanning ?_
  exact hM.spanning_of_dep hX

/-- A matroid is uniform iff every circuit intersects every cocircuit. -/
lemma isUniform_iff_circuit_cocircuit :
    M.IsUniform ↔ ∀ ⦃C K⦄, M.IsCircuit C → M.IsCocircuit K → (C ∩ K).Nonempty := by
  refine ⟨fun h C K hC hK ↦ h.inter_nonempty_of_dep_codep hC.dep hK.codep, fun h X hXE ↦ ?_⟩
  rw [← not_dep_iff, ← not_nonspanning_iff, ← codep_compl_iff]
  by_contra! hcon
  obtain ⟨C, hCX, hC⟩ := hcon.1.exists_isCircuit_subset
  obtain ⟨K, hKX, hK⟩ := hcon.2.exists_isCocircuit_subset
  exact (h hC hK).not_disjoint (disjoint_sdiff_right.mono hCX hKX)

lemma IsUniform.dual (hM : M.IsUniform) : M✶.IsUniform := by
  intro X hX
  rw [← diff_diff_cancel_left hX, ← coindep_def, ← coindep_iff_compl_spanning,
    dual_ground, ← spanning_iff_compl_coindep, dual_coindep_iff, or_comm]
  exact hM diff_subset

@[simp] lemma uniform_dual_iff : M✶.IsUniform ↔ M.IsUniform :=
  ⟨fun h ↦ by simpa using h.dual, IsUniform.dual⟩

lemma IsUniform.exchange (hM : M.IsUniform) (hB : M.IsBase B) (he : e ∈ M.E \ B) (hf : f ∈ B) :
    M.IsBase (insert e (B \ {f})) := by
  have hef : e ≠ f := by rintro rfl; exact he.2 hf
  obtain (hi | hs) := hM (X := insert e (B \ {f}))
    (insert_subset he.1 (diff_subset.trans hB.subset_ground))
  · exact hB.exchange_isBase_of_indep he.2 hi

  have hss : insert e (B \ {f}) ⊆ M.E := insert_subset he.1 (diff_subset.trans hB.subset_ground)
  suffices M✶.IsBase (M.E \ insert e (B \ {f})) by rwa [base_iff_dual_isBase_compl]
  rw [spanning_iff_compl_coindep, coindep_def] at hs
  have hrw : insert f ((M.E \ B) \ {e}) = M.E \ insert e (B \ {f}) := by
    rw [eq_comm, ← union_singleton, ← diff_diff, diff_diff_right,
      inter_eq_self_of_subset_right (show {f} ⊆ M.E by simpa using hB.subset_ground hf),
      union_singleton, insert_diff_singleton_comm hef.symm]
  rw [← hrw]
  exact hB.compl_isBase_dual.exchange_isBase_of_indep (f := f) (e := e)
    (by simp [hf]) <| by rwa [hrw]

lemma uniform_iff_forall_exchange : M.IsUniform ↔
  ∀ ⦃B e f⦄, M.IsBase B → e ∈ M.E \ B → f ∈ B → M.IsBase (insert e (B \ {f})) := by
  refine ⟨fun h B e f hB he hf ↦ h.exchange hB he hf, fun h X hXE ↦ ?_⟩
  obtain ⟨I, hIX⟩ := M.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hIX.exists_isBase
  obtain h1 | h2 := hIX.subset.eq_or_ssubset
  · rw [← h1]
    exact .inl (hIX.indep)
  obtain ⟨e, heBX, heX⟩ := exists_of_ssubset h2
  obtain h1 | h2' := (show X ∩ B ⊆ B from inter_subset_right).eq_or_ssubset
  · rw [inter_eq_right] at h1
    exact .inr (hB.spanning.superset h1)
  exfalso
  obtain ⟨f, hfBX, hfB⟩ := exists_of_ssubset h2'
  rw [mem_inter_iff, and_iff_left (by simpa)] at heX hfB
  have hB' := h hB ⟨hXE heBX, heX⟩ hfBX
  refine (heX <| (hIX.mem_of_insert_indep heBX (hB'.indep.subset ?_)).1)
  refine insert_subset_insert ?_
  rwa [subset_diff_singleton_iff, and_iff_right inter_subset_left, mem_inter_iff,
    and_iff_right hfBX]

lemma IsUniform.contract (hM : M.IsUniform) (C : Set α) : (M ／ C).IsUniform := by
  suffices h : ∀ C ⊆ M.E, (M ／ C).IsUniform by convert h (C ∩ M.E) inter_subset_right using 1; simp
  clear C
  intro C hCE
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  suffices ∀ X ⊆ M.E, Disjoint C X → M.Indep (X ∪ I) ∨ M.Spanning (X ∪ C) by
    simpa +contextual [IsUniform, hI.contract_indep_iff, contract_spanning_iff hCE, subset_diff,
      disjoint_comm]
  exact fun X hXE hXC ↦ (hM.indep_or_spanning _ (union_subset hXE hI.indep.subset_ground)).elim .inl
    fun h ↦ .inr <| h.superset (union_subset_union_right X hI.subset)

lemma IsUniform.delete (hM : M.IsUniform) (D : Set α) : (M ＼ D).IsUniform := by
  rw [← uniform_dual_iff, dual_delete]
  exact hM.dual.contract D

lemma IsUniform.minor {N : Matroid α} (hM : M.IsUniform) (hNM : N ≤m M) : N.IsUniform := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact (hM.contract C).delete D

@[simp] lemma loopyOn_uniform (E : Set α) : (loopyOn E).IsUniform :=
  fun _ ↦ by simp +contextual [spanning_iff]

@[simp] lemma freeOn_uniform (E : Set α) : (freeOn E).IsUniform :=
  fun _ ↦ by simp +contextual

lemma IsUniform.truncate (hM : M.IsUniform) : M.truncate.IsUniform := by
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · simp
  intro X (hXE : X ⊆ M.E)
  rw [truncate_indep_iff, truncate_spanning_iff]
  obtain hX | hX := hM.indep_or_spanning X
  · rw [and_iff_right hX, ← imp_iff_not_or]
    intro hB
    obtain ⟨e, he⟩ := hB.nonempty
    exact ⟨e, hB.subset_ground he, by simpa [he] using hB.spanning⟩
  obtain ⟨B, hB, hBX⟩ := hX.exists_isBase_subset
  obtain ⟨e, he⟩ := hB.nonempty
  exact .inr ⟨e, hB.subset_ground he, hX.superset (subset_insert _ _)⟩

lemma IsUniform.closure_not_spanning (hM : M.IsUniform) (hIE : I ⊆ M.E) (hIs : ¬ M.Spanning I) :
    M.closure I = I := by
  refine subset_antisymm (fun e he ↦ by_contra fun heI ↦ ?_) (subset_closure _ _)
  rw [spanning_iff_closure_eq, ← closure_closure, ← insert_eq_of_mem he,
    closure_insert_closure_eq_closure_insert, ← spanning_iff_closure_eq] at hIs

  have hIe : M.Indep (insert e I) :=
    (hM.indep_or_spanning _ (by aesop_mat)).elim id fun h ↦ (hIs h).elim
  rw [(hIe.subset (subset_insert _ _)).mem_closure_iff_of_notMem heI] at he
  exact he.not_indep hIe

lemma IsUniform.isBase_of_isBase_of_finDiff {B B' : Set α} (hM : M.IsUniform) (hB : M.IsBase B)
    (h_fin : FinDiff B B') (hB' : B' ⊆ M.E) : M.IsBase B' := by
  obtain h | h := (B' \ B).eq_empty_or_nonempty
  · rw [diff_eq_empty] at h
    rwa [h_fin.symm.eq_of_subset h]
  obtain ⟨f, hfB, hfB'⟩ := h_fin.nonempty_of_nonempty h
  obtain ⟨e, heB', heB⟩ := h

  have hrw : (B' \ insert e (B \ {f})) = ((B' \ B) \ {e}) := by aesop
  have IH : (B' \ insert e (B \ {f})).encard < (B' \ B).encard := by
    rw [hrw, ← encard_diff_singleton_add_one (show e ∈ B' \ B from ⟨heB', heB⟩),
      ENat.lt_add_one_iff]
    simp_rw [encard_ne_top_iff]
    exact h_fin.diff_right_finite.diff

  apply hM.isBase_of_isBase_of_finDiff (hM.exchange hB ⟨hB' heB', heB⟩ hfB)
  rwa [finDiff_iff, insert_diff_of_mem _ heB', diff_diff_comm,
    and_iff_right h_fin.diff_left_finite.diff, ← singleton_union, union_comm, ← diff_diff,
    diff_diff_right, inter_singleton_eq_empty.2 hfB', union_empty,
    ← WithTop.add_right_inj (z := 1) (by simp),
    encard_diff_singleton_add_one (show f ∈ B \ B' from ⟨hfB, hfB'⟩),
    encard_diff_singleton_add_one (show e ∈ B' \ B from ⟨heB', heB⟩), h_fin.encard_diff_eq]
termination_by (B' \ B).encard

lemma maximal_right_of_forall_ge {α : Type*} {P Q : α → Prop} {a : α} [PartialOrder α]
    (hP : ∀ ⦃x y⦄, P x → x ≤ y → P y) (h : Maximal (fun x ↦ P x ∧ Q x) a) : Maximal Q a :=
  ⟨h.prop.2, fun _ hb hab ↦ h.le_of_ge ⟨hP h.prop.1 hab, hb⟩ hab⟩

/-- A finite-rank uniform matroid is one of the obvious ones. -/
lemma IsUniform.exists_eq_unifOn [M.RankFinite] (hM : M.IsUniform) :
    ∃ (E : Set α) (k : ℕ), k ≤ E.encard ∧ M = unifOn E k ∧ M.eRank = k := by
  refine ⟨M.E, M.rank, ?_, ext_isBase rfl fun B hBE ↦ ?_, by simp⟩
  · grw [cast_rank_eq, eRank_le_encard_ground]
  rw [unifOn_isBase_iff (M.cast_rank_eq ▸ M.eRank_le_encard_ground) hBE,
    cast_rank_eq, iff_def, and_iff_right IsBase.encard_eq_eRank]
  intro hB
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  refine hM.isBase_of_isBase_of_finDiff hB₀ ?_ hBE
  rw [finDiff_iff, and_iff_right hB₀.finite.diff,
    ← WithTop.add_right_inj (z := (B₀ ∩ B).encard), encard_diff_add_encard_inter,
    inter_comm, encard_diff_add_encard_inter, hB₀.encard_eq_eRank, hB]
  exact (hB₀.finite.inter_of_left B).encard_lt_top.ne

/-- A finitary non-free uniform matroid is one of the obvious ones. -/
lemma IsUniform.exists_eq_unifOn_of_finitary [M.Finitary] [M✶.RankPos] (hM : M.IsUniform) :
    ∃ (E : Set α) (k : ℕ), k ≤ E.encard ∧ M = unifOn E k ∧ M.eRank = k := by
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  obtain ⟨e, heC⟩ := hC.nonempty
  obtain hCi | hCs := hM.indep_or_spanning C
  · exact (hC.not_indep hCi).elim
  have := ((hC.diff_singleton_isBasis heC).isBase_of_spanning hCs).rankFinite_of_finite
    hC.finite.diff
  exact hM.exists_eq_unifOn

lemma IsUniform.exists_eq_freeOn_or_unifOn_of_finitary [M.Finitary] (hM : M.IsUniform) :
    ∃ (E : Set α), M = freeOn E ∨ ∃ (k : ℕ), k ≤ E.encard ∧ M = unifOn E k ∧ M.eRank = k := by
  obtain ⟨E, rfl⟩ | hr := M.exists_eq_freeOn_or_rankPos_dual
  · exact ⟨E, .inl rfl⟩
  obtain ⟨E, k, hle, rfl, hk⟩ := hM.exists_eq_unifOn_of_finitary
  exact ⟨E, .inr ⟨k, hle, rfl, hk⟩⟩

lemma unifOn_isUniform (E : Set α) (k : ℕ) : (unifOn E k).IsUniform := by
  intro X (hX : X ⊆ E)
  rw [unifOn_indep_iff, unifOn_spanning_iff']
  grind

lemma isUniform_of_eRank_add_one_le_girth [M.RankFinite] (hM : M.eRank + 1 ≤ M.girth) :
    M.IsUniform := by
  rw [isUniform_iff]
  intro X hXE
  rw [← not_dep_iff, ← imp_iff_not_or]
  intro hX
  grw [spanning_iff_eRk, ← ENat.add_one_le_add_one_iff, hM, hX.girth_le_eRk_add_one]

lemma isUniform_of_eRank_lt_girth (hM : M.eRank < M.girth) : M.IsUniform := by
  have _ : M.RankFinite := by rw [← eRank_lt_top_iff]; enat_to_nat!
  refine isUniform_of_eRank_add_one_le_girth <| Order.add_one_le_of_lt hM

@[simps!] def uniformMatroidOfBase (E : Set α) (IsBase : Set α → Prop)
    (exists_isBase : ∃ B, IsBase B)
    (antichain : IsAntichain (· ⊆ ·) (setOf IsBase))
    (exchange : ∀ ⦃B e f⦄, IsBase B → e ∈ B → f ∈ E \ B → IsBase (insert f (B \ {e})))
    (contain : ∀ ⦃I X⦄, I ⊆ X → X ⊆ E → (X \ I).Infinite →
      ∃ B, IsBase B ∧ ((B ⊆ I) ∨ (I ⊆ B ∧ B ⊆ X) ∨ (X ⊆ B)))
    (subset_ground : ∀ ⦃B⦄, IsBase B → B ⊆ E) :
    Matroid α :=
Matroid.ofBase E IsBase exists_isBase
  (by
    rintro B B' hB hB' e ⟨heB, heB'⟩
    contrapose! heB'
    rwa [antichain.eq hB' hB fun f hfB' ↦ by_contra fun hfB ↦ heB' f ⟨hfB', hfB⟩
      (exchange hB heB ⟨subset_ground hB' hfB', hfB⟩)])
  (by
    intro X hX I hI hIX
    obtain hfin | hinf := (X \ I).finite_or_infinite
    · set S := {A | I ⊆ A ∧ (∃ B, IsBase B ∧ A ⊆ B) ∧ A ⊆ X} with hS_def
      have hSfin : S.Finite := by
        refine Finite.of_finite_image (f := fun X ↦ X \ I) (hfin.finite_subsets.subset ?_) ?_
        · simp only [hS_def, image_subset_iff, preimage_setOf_eq, setOf_subset_setOf]
          exact fun J hIJ ↦ diff_subset_diff_left hIJ.2.2
        rintro A ⟨hIA, -, -⟩ B ⟨hIB, -, -⟩ (hAB : A \ I = B \ I)
        rw [← diff_union_of_subset hIA, hAB, diff_union_of_subset hIB]

      obtain ⟨J, hIJ : I ⊆ J, hJ⟩ := hSfin.exists_le_maximal (a := I) ⟨rfl.subset, hI, hIX⟩
      exact ⟨J, hIJ, maximal_right_of_forall_ge (fun x y hx hxy ↦ hx.trans hxy) hJ⟩
    simp only
    have aux : ∀ B, IsBase B → B ⊆ X → Maximal (fun K ↦ (∃ B', IsBase B' ∧ K ⊆ B') ∧ K ⊆ X) B := by
      simp only [maximal_subset_iff, and_imp, forall_exists_index]
      exact fun B hB hBX ↦ ⟨⟨⟨B, hB, rfl.subset⟩, hBX⟩, fun K B' hB' hKB' hB'X hBK ↦
        hBK.antisymm <| by rwa [ antichain.eq hB hB' (hBK.trans hKB')]⟩

    obtain ⟨B, hB, hIB⟩ := hI
    obtain ⟨B', hB', hB'I | ⟨hIB', hB'X⟩ | hXB'⟩ := contain hIX hX hinf
    ·
      obtain rfl : B' = B := antichain.eq hB' hB (hB'I.trans hIB)
      obtain rfl : I = B' := hIB.antisymm hB'I
      exact ⟨I, rfl.subset, aux _ hB hIX⟩
    · exact ⟨B', hIB', aux _ hB' hB'X⟩
    exact ⟨X, hIX, ⟨⟨B', hB', hXB'⟩, rfl.subset⟩, fun Y hY hXY ↦ hY.2⟩)
  subset_ground

lemma uniformMatroidOfBase_uniform (E : Set α) (IsBase : Set α → Prop)
    {exists_isBase} {ac} {exch} {contain} {subset_ground} :
    (uniformMatroidOfBase E IsBase exists_isBase ac exch contain subset_ground).IsUniform := by
  simp only [uniform_iff_forall_exchange, uniformMatroidOfBase_IsBase, uniformMatroidOfBase_E,
    mem_diff, and_imp]
  exact fun B e f hB heE he hf ↦ exch hB hf ⟨heE, he⟩

lemma IsBase.finDiff_of_finite_diff (hB : M.IsBase B) (hB' : M.IsBase B') (hBB' : (B \ B').Finite) :
    FinDiff B B' := by
  rw [finDiff_iff, and_iff_right hBB', hB.encard_diff_comm hB']

end Infinite

section Strong



end Strong

section LowRank

lemma eq_unifOn_of_eRank_le_one [M.Loopless] (hM : M.eRank ≤ 1) : ∃ E, M = unifOn E 1 := by
  simp +contextual only [ext_iff_indep, unifOn_ground_eq, unifOn_indep_iff, exists_eq_left',
    and_true]
  exact fun I hIE ↦ ⟨fun hI ↦ hI.encard_le_eRank.trans hM,
    fun hI ↦ subsingleton_indep (encard_le_one_iff_subsingleton.1 hI) hIE⟩

lemma eq_unifOn_of_eRank_le_two [M.Simple] (hM : M.eRank ≤ 2) : ∃ E, M = unifOn E 2 := by
  simp only [ext_iff_indep, unifOn_ground_eq, unifOn_indep_iff]
  exact ⟨_, rfl, fun I hIE ↦ ⟨fun hI ↦ ⟨hI.encard_le_eRank.trans hM, hIE⟩,
    fun ⟨hcard, _⟩ ↦ indep_of_encard_le_two hcard⟩⟩

theorem eq_unifOn_two_iff : M = unifOn E 2 ↔ M.E = E ∧ M.eRank ≤ 2 ∧ M.Simple := by
  refine ⟨?_, fun ⟨hE, hr, h⟩ ↦ ?_⟩
  · rintro rfl
    simpa [unifOn_eRank_eq] using unifOn_simple E
  obtain ⟨E', rfl⟩ := eq_unifOn_of_eRank_le_two hr
  rw [show E' = E from hE]

lemma unifOn_one_dual (E : Set α) : (unifOn E 1)✶ = circuitOn E := by
  rw [← circuitOn_dual, dual_dual]

theorem nonempty_iso_line_iff {n : ℕ} :
    Nonempty (M ≂ unif 2 n) ↔ M.Simple ∧ M.eRank ≤ 2 ∧ M.E.encard = n := by
  simp [nonempty_iso_unif_iff', ← and_assoc, eq_unifOn_two_iff, and_comm]

lemma eRank_le_one_iff : M.eRank ≤ 1 ↔ ∃ (E₀ E₁ : Set α) (h : Disjoint E₀ E₁),
    M = (loopyOn E₀).disjointSum (unifOn E₁ 1) h := by
  refine ⟨fun hr ↦ ⟨M.loops, M.E \ M.loops, disjoint_sdiff_right, ?_⟩, ?_⟩
  · refine ext_indep ?_ fun I hI ↦ ?_
    · simp [union_eq_self_of_subset_left M.loops_subset_ground]
    suffices M.Indep I ↔ Disjoint I (M.loops) ∧ (I ∩ (M.E \ M.loops)).Subsingleton ∧
      I ⊆ M.loops ∪ M.E by simpa [encard_le_one_iff_subsingleton, ← disjoint_iff_inter_eq_empty]
    refine ⟨fun h ↦ ?_, fun ⟨hcl, hss, _⟩ ↦ ?_⟩
    · rw [and_iff_right h.disjoint_loops, ← encard_le_one_iff_subsingleton,
        and_iff_left (h.subset_ground.trans subset_union_right)]
      exact (h.subset inter_subset_left).encard_le_eRank.trans hr
    have hI : I ∩ (M.E \ M.loops) = I := by rwa [inter_eq_left, subset_diff, and_iff_left hcl]
    rw [hI] at hss
    obtain rfl | ⟨e, rfl⟩ := hss.eq_empty_or_singleton
    · exact M.empty_indep
    rwa [indep_singleton, isNonloop_iff_notMem_loops, ← disjoint_singleton_left]
  rintro ⟨E₀, E₁, hdj, rfl⟩
  simp [unifOn_eRank_eq]

lemma unifOn_isLoopless_iff {n : ℕ} :
    (unifOn E n).Loopless ↔ (n = 0 → E = ∅) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro h rfl
    simpa using h
  obtain rfl | n := n
  · simpa using h rfl
  simp [loopless_iff_forall_isNonloop, ← indep_singleton]

lemma unifOn_simple_iff {n : ℕ} :
    (unifOn E n).Simple ↔ (n = 0 ∧ E = ∅) ∨ (n = 1 ∧ E.Subsingleton) ∨ 2 ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl | rfl | n := n
    · simp [unifOn_isLoopless_iff.1 h.loopless]
    · have h : ∀ ⦃e f : α⦄, e ∈ E → f ∈ E → e = f := by
        simpa +contextual [simple_iff_forall_pair_indep, pair_subset_iff,
          encard_le_one_iff_subsingleton] using h
      exact .inr (.inl ⟨rfl, fun x hxE y hyE ↦ h hxE hyE ⟩)
    exact .inr <| .inr <| by simp
  simp +contextual only [simple_iff_forall_pair_indep, unifOn_ground_eq, unifOn_indep_iff,
    pair_subset_iff, and_self, and_true]
  obtain ⟨rfl, rfl⟩ | ⟨rfl, h⟩ | h := h
  · simp
  · exact fun e f he hf ↦ by simpa [encard_le_one_iff_subsingleton] using h he hf
  exact fun e f he hf ↦ (encard_pair_le e f).trans (by simpa)

end LowRank

section IsoMinor

def NoUniformMinor (M : Matroid α) (a b : ℕ) : Prop := IsEmpty (unif a b ≤i M)

@[simp] lemma not_noUniformMinor_iff {a b : ℕ} :
    ¬ M.NoUniformMinor a b ↔ Nonempty (unif a b ≤i M) := by
  simp [NoUniformMinor]

lemma NoUniformMinor.minor {N a b} (hM : M.NoUniformMinor a b) (hNM : N ≤m M) :
    N.NoUniformMinor a b := by
  contrapose! hM
  simp only [not_noUniformMinor_iff] at hM ⊢
  exact ⟨hM.some.trans_isMinor hNM⟩

lemma nonempty_unif_isoRestr_unifOn (a : ℕ) {b : ℕ} {E : Set α} (h : b ≤ E.encard) :
    Nonempty (unif a b ≤ir unifOn E a) := by
  obtain ⟨f, hf⟩ : ∃ f : ↑(unif a b).E → ↑(unifOn E ↑a).E, f.Injective
  · obtain rfl | b := b
    · exact ⟨finZeroElim ∘ Subtype.val, Function.injective_of_subsingleton _⟩
    have : Nonempty E
    · rw [nonempty_coe_sort, nonempty_iff_ne_empty]
      rintro rfl
      simp at h
    obtain ⟨f, hf, hfi⟩ :=
      finite_univ.exists_injOn_of_encard_le (α := Fin (b+1)) (β := E) (t := univ) (by simpa using h)
    rw [injOn_univ] at hfi
    exact ⟨f ∘ Subtype.val, hfi.comp Subtype.val_injective⟩
  exact ⟨⟨f, hf, fun I ↦ by simp [Subtype.val_injective.encard_image, hf.encard_image]⟩⟩

@[simp] lemma unifOn_noUniformMinor_iff {a b : ℕ} :
    ((unifOn E a).NoUniformMinor a b) ↔ E.encard < b := by
  rw [← not_iff_not, not_noUniformMinor_iff, not_lt]
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ⟨(nonempty_unif_isoRestr_unifOn a h).some.isoMinor⟩⟩
  obtain ⟨f, hf, M₀, hm, hE, -⟩ := e
  refine le_trans ?_ <| encard_mono hm.subset
  rw [hE, Subtype.val_injective.encard_image, ← image_univ, hf.encard_image]
  simp

lemma no_line_minor_iff_of_eRank_le_two (hM : M.eRank ≤ 2) :
    M.NoUniformMinor 2 b ↔ M.simplification.E.encard < b := by
  obtain ⟨E, he⟩ := eq_unifOn_of_eRank_le_two (M := M.simplification) (by simpa)
  rw [← not_iff_not, not_noUniformMinor_iff, (unif_simple 0 b).isMinor_iff_isMinor_simplification,
      he, ← not_iff_not, ← not_noUniformMinor_iff, not_not, not_not,
    unifOn_noUniformMinor_iff, unifOn_ground_eq]


end IsoMinor





      /-
      theorem unif_isoMinor_unif_iff (hab : a ≤ b) (ha'b' : a' ≤ b') :
          unif a b ≤i unif a' b' ↔ a ≤ a' ∧ b - a ≤ b' - a' := by
        refine ⟨fun h ↦ ?_, fun ⟨hr, hr'⟩  ↦ ?_⟩
        · constructor
          · have hle := h.eRank_le_eRank
            simp only [unif_eRank_eq, ge_iff_le, Nat.cast_le, le_min_iff, min_le_iff] at hle
            obtain ⟨(haa'| hba'), (- | -)⟩ := hle <;> linarith
          have hle := h.dual.eRank_le_eRank
          rw [unif_dual, unif_dual, unif_eRank_eq_of_le (by simp),
          -- unif_eRank_eq_of_le (by simp)] at hle
          exact (WithTop.le_coe rfl).1 hle
        have hbb' := add_le_add hr hr'
        rw [Nat.add_sub_cancel' hab, Nat.add_sub_cancel' ha'b'] at hbb'

        obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hr
        obtain ⟨d',rfl⟩ := Nat.exists_eq_add_of_le ha'b'
        refine (unif_isoMinor_contr a b d).trans (unif_isoMinor_restr (a+d) ?_)
        have hb' : b ≤ d' + a
        · zify at hr'; simpa using hr'
        linarith

      @[simp] theorem isIso_line_iff {n : ℕ} : M ≂ unif 2 n ↔
      --M.Simple ∧ M.eRank ≤ 2 ∧ M.E.encard = n := by
        simp [isIso_unif_iff, ← and_assoc, and_congr_left_iff, eq_unifOn_two_iff, and_comm]

      theorem line_isoRestr_of_simple_eRk_le_two {n : ℕ} {L : Set α} (hL : (M ↾ L).Simple)
          (hcard : n ≤ L.encard) (hr : M.eRk L ≤ 2) : unif 2 n ≤ir M := by
        obtain ⟨Y, hYL, hY⟩ := exists_subset_encard_eq hcard
        have hYs := hL.subset hYL
        refine ⟨M ↾ Y, restrict_isRestriction _ Y hYs.subset_ground, ?_⟩
        rw [IsIso.comm, isIso_unif_iff, eq_unifOn_iff]
        simp only [restrict_ground_eq, restrict_indep_iff,
        --Nat.cast_ofNat, and_congr_left_iff, true_and,
          and_iff_left hY]
        refine fun I hIY ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
        · exact (hI.encard_le_eRk_of_subset (hIY.trans hYL)).trans hr
        exact (indep_of_encard_le_two (M := M ↾ Y) hI).of_restrict

      theorem no_line_isoRestr_iff {n : ℕ} {M : Matroid α} :
          ¬ (unif 2 n ≤ir M) ↔ ∀ L, (M ↾ L).Simple → M.eRk L ≤ 2 → L.encard < n := by
        refine ⟨fun h L hL hLr ↦ lt_of_not_ge fun hle ↦
          h <| line_isoRestr_of_simple_eRk_le_two hL hle hLr, fun h hR ↦ ?_⟩
        obtain ⟨N, hNM, hN⟩ := hR
        obtain ⟨L, -, rfl⟩ := hNM.exists_eq_restrict
        rw [IsIso.comm, isIso_unif_iff, eq_unifOn_iff] at hN
        simp only [restrict_ground_eq, restrict_indep_iff, Nat.cast_ofNat, and_congr_left_iff,
          true_and] at hN
        refine (h L ?_ ?_).ne hN.2
        · simp only [simple_iff_forall_pair_indep, restrict_ground_eq, mem_singleton_iff,
            restrict_indep_iff, pair_subset_iff]
          exact fun {e f} he hf ↦ ⟨by simp [hN.1 _ (pair_subset he hf)], he, hf⟩
        obtain ⟨I, hI⟩ := M.exists_isBasis' L
        rw [← hI.encard, ← hN.1 _ hI.subset]
        exact hI.indep

      end unif

      end Uniform
      -/

/-


@[simp] theorem isIso_line_iff {n : ℕ} : M ≂ unif 2 n ↔
  --M.Simple ∧ M.eRank ≤ 2 ∧ M.E.encard = n := by
  simp [isIso_unif_iff, ← and_assoc, and_congr_left_iff, eq_unifOn_two_iff, and_comm]

theorem line_isoRestr_of_simple_eRk_le_two {n : ℕ} {L : Set α} (hL : (M ↾ L).Simple)
    (hcard : n ≤ L.encard) (hr : M.eRk L ≤ 2) : unif 2 n ≤ir M := by
  obtain ⟨Y, hYL, hY⟩ := exists_subset_encard_eq hcard
  have hYs := hL.subset hYL
  refine ⟨M ↾ Y, restrict_isRestriction _ Y hYs.subset_ground, ?_⟩
  rw [IsIso.comm, isIso_unif_iff, eq_unifOn_iff]
  simp only [restrict_ground_eq, restrict_indep_iff, Nat.cast_ofNat, and_congr_left_iff, true_and,
    and_iff_left hY]
  refine fun I hIY ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · exact (hI.encard_le_eRk_of_subset (hIY.trans hYL)).trans hr
  exact (indep_of_encard_le_two (M := M ↾ Y) hI).of_restrict

theorem no_line_isoRestr_iff {n : ℕ} {M : Matroid α} :
    ¬ (unif 2 n ≤ir M) ↔ ∀ L, (M ↾ L).Simple → M.eRk L ≤ 2 → L.encard < n := by
  refine ⟨fun h L hL hLr ↦ lt_of_not_ge fun hle ↦
    h <| line_isoRestr_of_simple_eRk_le_two hL hle hLr, fun h hR ↦ ?_⟩
  obtain ⟨N, hNM, hN⟩ := hR
  obtain ⟨L, -, rfl⟩ := hNM.exists_eq_restrict
  rw [IsIso.comm, isIso_unif_iff, eq_unifOn_iff] at hN
  simp only [restrict_ground_eq, restrict_indep_iff, Nat.cast_ofNat, and_congr_left_iff,
    true_and] at hN
  refine (h L ?_ ?_).ne hN.2
  · simp only [simple_iff_forall_pair_indep, restrict_ground_eq, mem_singleton_iff,
      restrict_indep_iff, pair_subset_iff]
    exact fun {e f} he hf ↦ ⟨by simp [hN.1 _ (pair_subset he hf)], he, hf⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' L
  rw [← hI.encard, ← hN.1 _ hI.subset]
  exact hI.indep

end unif

end Uniform
-/
