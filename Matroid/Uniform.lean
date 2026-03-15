import Matroid.Constructions.Truncate
import Matroid.ForMathlib.FinDiff
import Mathlib.Combinatorics.Matroid.Sum -- inefficient import
import Matroid.Simple
import Matroid.Bool
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

lemma unifOn_truncate (E : Set α) (k : ℕ) (hk : k + 1 ≤ E.encard) :
    (unifOn E (k + 1)).truncate = unifOn E k := by
  rw [unifOn, truncateTo_truncate _ _ (by simpa), unifOn]

@[simp]
lemma unifOn_one_truncate (E : Set α) : (unifOn E 1).truncate = loopyOn E := by
  obtain rfl | hne := E.eq_empty_or_nonempty
  · simp
  rw [unifOn_truncate, unifOn_zero]
  exact one_le_encard_iff_nonempty.2 hne

@[simp]
lemma unifOn_freeLift (E : Set α) (k : ℕ) : (unifOn E k).freeLift = unifOn E (k + 1) := by
  refine ext_indep rfl fun I (hIE : I ⊆ E) ↦ ?_
  obtain rfl | hne := I.eq_empty_or_nonempty
  · simp
  simp only [freeLift_indep_iff, hne, unifOn_ground_eq, mem_inter_iff, unifOn_indep_iff,
    diff_singleton_subset_iff, forall_const, Nat.cast_add, Nat.cast_one]
  refine ⟨fun ⟨e, ⟨heI, heE⟩, hIe, hIE⟩ ↦ ?_, fun h ↦ ?_⟩
  · grw [← hIe, ← encard_le_encard_diff_singleton_add_one]
    grind
  obtain ⟨f, hf⟩ := hne
  refine ⟨f, by grind, ?_, by grind⟩
  grw [← ENat.add_one_le_add_one_iff, ← h.1, encard_diff_singleton_add_one hf]

theorem unifOn_eq_of_le (h : E.encard ≤ k) : unifOn E k = freeOn E := by
  rw [unifOn, truncate_eq_self_of_rank_le (by rwa [eRank_freeOn])]

lemma unifOn_pair : unifOn {e, f} 2 = freeOn {e, f} := by
  rw [unifOn_eq_of_le (encard_pair_le ..)]

lemma unifOn_pair_one (hef : e ≠ f) : unifOn {e, f} 1 = circuitOn {e, f} := by
  rw [circuitOn, ← unifOn_pair, unifOn_truncate]
  rw [encard_pair hef]
  rfl

lemma unifOn_triple {e f g : α} : unifOn {e, f, g} 3 = freeOn {e, f, g} := by
  rw [unifOn_eq_of_le]
  grw [encard_insert_le, encard_pair_le]
  rfl

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
-- set_option pp.all true

set_option backward.isDefEq.respectTransparency false in
theorem unifOn_eRank_eq' (hle : k ≤ E.encard) : (unifOn E k).eRank = k := by
  rw [unifOn_eRank_eq, min_eq_right hle]

theorem unifOn_rank_eq (hk : (k : ℕ∞) ≤ E.encard) : (unifOn E k).rank = k := by
  rw [rank, unifOn_eRank_eq, show min E.encard k = k from min_eq_right hk, ENat.toNat_coe]

@[simp]
theorem unifOn_rankPos_iff : (unifOn E k).RankPos ↔ 1 ≤ k ∧ E.Nonempty := by
  simp [← eRank_ne_zero_iff, unifOn_eRank_eq, ← ENat.one_le_iff_ne_zero, and_comm]


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

  rw [dual_isBase_iff, unifOn_isBase_iff (by simpa) (by simp),
    unifOn_ground_eq, unifOn_isBase_iff (by simp) hBE, ← Finset.coe_sdiff,
    encard_coe_eq_coe_finsetCard, ENat.coe_inj, encard_coe_eq_coe_finsetCard, ENat.coe_inj,
    toFinite_toFinset, E.toFinset_coe, Finset.card_sdiff_of_subset (by simpa),
    tsub_eq_iff_eq_add_of_le (Finset.card_mono (by simpa)),
    eq_tsub_iff_add_eq_of_le (by simpa), add_comm, eq_comm]

lemma unifOn_dual_eq' {j k : ℕ} (hE : E.encard = k + j) : (unifOn E k)✶ = unifOn E j := by
  have hEfin : E.Finite := by rw [← encard_lt_top_iff]; enat_to_nat!
  rw [hEfin.encard_eq_coe_toFinset_card, ← Nat.cast_add, ENat.coe_inj] at hE
  rw [unifOn_dual_eq hEfin, hE, Nat.add_sub_cancel_left]

lemma unifOn_dual_eq_of_le {k : ℕ} (hEfin : E.Finite) (hle : k ≤ E.encard) :
    ∃ (j : ℕ), j ≤ E.encard ∧ k + j = E.encard ∧ (unifOn E k)✶ = unifOn E j := by
  obtain ⟨j, hj⟩ := exists_add_of_le hle
  rw [← encard_lt_top_iff] at hEfin
  generalize hn : E.encard = n at *
  enat_to_nat
  rw [hj, Nat.cast_add] at hn
  exact ⟨j, by omega, hj.symm, unifOn_dual_eq' hn⟩

lemma unifOn_dual_eq_self {k : ℕ} {E : Set α} (hkE : E.encard = 2 * k) :
    (unifOn E k)✶ = unifOn E k :=
  unifOn_dual_eq' <| by enat_to_nat!; lia

lemma unifOn_bDual_eq_self {k : ℕ} {E : Set α} (hkE : E.encard = 2 * k) (d : Bool) :
    (unifOn E k).bDual d = unifOn E k := by
  cases d
  · rfl
  exact unifOn_dual_eq_self hkE

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
  enat_to_nat!; lia

theorem unifOn_contractElem (heE : e ∈ E) : (unifOn E (k+1)) ／ {e} = unifOn (E \ {e}) k := by
  simpa using unifOn_contract_finset_eq (C := {e}) (E := E) (k := (k+1)) (by simpa)

theorem unifOn_insert_contractElem (he : e ∉ E) :
    (unifOn (insert e E) (k+1)) ／ {e} = unifOn E k := by
  rw [unifOn_contractElem (mem_insert ..), insert_diff_of_mem _ (by simp),
    diff_singleton_eq_self he]

instance unifOn_loopless (E : Set α) : Loopless (unifOn E (k+1)) := by
  simp_rw [loopless_iff_forall_isNonloop, ← indep_singleton, unifOn_indep_iff]
  simp

instance unifOn_simple (E : Set α) : Simple (unifOn E (k+2)) := by
  simp only [simple_iff_forall_pair_indep, unifOn_indep_iff, unifOn_ground_eq, pair_subset_iff]
  exact fun {e f} he hf ↦ ⟨(encard_pair_le e f).trans (by simp), he, hf⟩

@[simp] lemma circuitOn_dual (E : Set α) : (circuitOn E)✶ = unifOn E 1 := by
  rw [← freeOn_truncate, truncate_dual, freeOn_dual_eq, ← unifOn_zero, unifOn_freeLift]

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
  · rwa [← encard_diff_singleton_add_one heC, ENat.add_one_lt_add_one_iff] at hlt
  rwa [← encard_diff_singleton_add_one heC, ENat.add_one_eq_add_one_iff] at h

lemma circuitOn_eq_unifOn {n : ℕ} (hn : n + 1 = C.encard) : circuitOn C = unifOn C n := by
  rw [← dual_inj, circuitOn_dual, unifOn_dual_eq' (j := 1)]
  simp [hn]

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
  simp [hKE]

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

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem unif_eRank_eq (a b : ℕ) : (unif a b).eRank = min a b := by
  rw [eRank_def, unif_eRk_eq]
  simp only [unif_ground_eq, min_comm, encard_univ_fin]; rfl

@[simp] theorem unif_rank_eq (a b : ℕ) : (unif a b).rank = min a b := by
  rw [rank, unif_eRank_eq, ENat.toNat_coe]

theorem unif_eRank_eq_of_le (hab : a ≤ b) : (unif a b).eRank = a := by
  simpa

theorem unif_isBase_iff (hab : a ≤ b) {B : Set (Fin b)} : (unif a b).IsBase B ↔ B.encard = a := by
  rw [unif, unifOn, truncateTo_isBase_iff, freeOn_indep_iff, and_iff_right (subset_univ _)]
  rwa [eRank_freeOn, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.coe_le_coe]

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
    ← add_left_inj_of_ne_top (encard_ne_top_iff.2 B.toFinite),
    encard_diff_add_encard_of_subset (subset_univ _), Iff.comm,
    ← add_right_inj_of_ne_top (ENat.coe_ne_top a), eq_comm]
  convert Iff.rfl
  rw [encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, Nat.cast_add]

@[simp] theorem unif_add_left_dual (a b : ℕ) : (unif a (a + b))✶ = unif b (a+b) :=
  unif_dual' rfl

@[simp] theorem unif_add_right_dual (a b : ℕ) : (unif b (a + b))✶ = unif a (a+b) :=
  unif_dual' <| add_comm _ _

instance unif_loopless (a b : ℕ) : Loopless (unif (a + 1) b) := by
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

set_option backward.isDefEq.respectTransparency false in
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

lemma unif_isoRestr_unifOn {a : ℕ} (hbb : b ≤ E.encard) :
    Nonempty (unif a b ≤ir (unifOn E a)) := by
  have hle : (unif a b).E.encard ≤ E.encard := by simpa
  obtain ⟨φ⟩ := (Finite.encard_le_iff_nonempty_embedding (by simp)).1 hle
  refine ⟨⟨φ, φ.injective, fun I ↦ ?_⟩⟩
  simp only [unif_ground_eq, unif_indep_iff, unifOn_ground_eq, unifOn_indep_iff, image_subset_iff,
    Subtype.coe_preimage_self, subset_univ, and_true, Subtype.val_injective.encard_image]
  rw [Function.Injective.encard_image (by exact φ.injective)]

section IsFreeBase

variable {B B' : Set α}

/-- A free base is one where exchanging any two elements gives a base. -/
@[mk_iff]
structure IsFreeBase (M : Matroid α) (B : Set α) : Prop where
  isBase : M.IsBase B
  isBase_of_exchange : ∀ B' ⊆ M.E, B'.IsExchange B → M.IsBase B'

lemma IsFreeBase.isBase_insert_diff_singleton (h : M.IsFreeBase B) (he : e ∈ B) (hf : f ∈ M.E \ B) :
    M.IsBase (insert f (B \ {e})) :=
  h.isBase_of_exchange _ (by grind [h.isBase.subset_ground]) (isExchange_diff_insert he hf.2).symm

lemma IsFreeBase.compl_dual (hB : M.IsFreeBase B) : M✶.IsFreeBase (M.E \ B) := by
  refine ⟨hB.isBase.compl_isBase_dual, fun B' hB' hB'ex ↦ ?_⟩
  have h1 := (isExchange_diff_right_comm hB' hB.isBase.subset_ground).1 hB'ex
  have h2 := (hB.isBase_of_exchange _ diff_subset h1).compl_isBase_dual
  rwa [diff_diff_cancel_left (by simpa)] at h2

lemma isFreeBase_dual_iff (hB : B ⊆ M.E) : M✶.IsFreeBase B ↔ M.IsFreeBase (M.E \ B) := by
  refine ⟨fun h ↦ by simpa using h.compl_dual, fun h ↦ ?_⟩
  rw [← diff_diff_cancel_left hB]
  exact h.compl_dual

lemma IsFreeBase.indep_of_ssubset_insert (hB : M.IsFreeBase B) (hI : I ⊂ insert e B)
    (he : e ∈ M.E := by aesop_mat) : M.Indep I := by
  by_cases! he : e ∉ (I \ B)
  · exact hB.isBase.indep.subset <| by grind
  obtain ⟨f, hf⟩ := exists_of_ssubset hI
  refine (hB.isBase_insert_diff_singleton (e := f) (f := e) ?_ ?_).indep.subset ?_ <;>
  grind

end IsFreeBase

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

lemma isUniform_iff_forall_isFreeBase : M.IsUniform ↔ ∀ B, M.IsBase B → M.IsFreeBase B := by
  refine ⟨fun h B hB ↦ ⟨hB, fun B' hB' hBB' ↦ ?_⟩, fun h X hXE ↦ ?_⟩
  · obtain hi | hs := h.indep_or_spanning B' hB'
    · exact hB.isBase_of_indep_of_finDiff hi hBB'.symm.finDiff
    exact hB.isBase_of_spanning_of_finDiff hs hBB'.symm.finDiff
  by_contra! hcon
  rw [not_indep_iff, not_spanning_iff] at hcon
  obtain ⟨C, hCX, hC⟩ := hcon.1.exists_isCircuit_subset
  obtain ⟨e, he⟩ := hC.nonempty
  obtain ⟨B, hB, hCeb⟩ := (hC.diff_singleton_indep he).exists_isBase_superset
  obtain rfl | hssu := (diff_singleton_subset_iff.1 hCeb).eq_or_ssubset
  · exact hcon.2.not_spanning (hB.spanning_of_superset (X := X) (by grind))
  exact ((h B hB).indep_of_ssubset_insert hssu).not_dep hC.dep

lemma IsUniform.isFreeBase (hM : M.IsUniform) (hB : M.IsBase B) : M.IsFreeBase B :=
  isUniform_iff_forall_isFreeBase.1 hM B hB

lemma IsUniform.isBase_insert_diff_singleton (hM : M.IsUniform) (hB : M.IsBase B) (he : e ∈ M.E \ B)
    (hf : f ∈ B) : M.IsBase (insert e (B \ {f})) :=
  (hM.isFreeBase hB).isBase_insert_diff_singleton hf he

lemma uniform_iff_forall_insert_diff_singleton : M.IsUniform ↔
    ∀ ⦃B e f⦄, M.IsBase B → e ∈ M.E \ B → f ∈ B → M.IsBase (insert e (B \ {f})) := by
  refine ⟨fun h B e f hB he hf ↦ h.isBase_insert_diff_singleton hB he hf,
    fun h ↦ isUniform_iff_forall_isFreeBase.2 fun B hB ↦ ⟨hB, fun B' hB' hBB' ↦ ?_⟩⟩
  obtain ⟨e, he, f, hf, rfl⟩ := hBB'.symm.exists
  grind

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

@[simp]
lemma isUniform_unifOn (E : Set α) (a : ℕ) : (unifOn E a).IsUniform := by
  intro I (hI : I ⊆ E)
  grind [unifOn_spanning_iff', unifOn_indep_iff]

lemma IsUniform.closure_not_spanning (hM : M.IsUniform) (hIE : I ⊆ M.E) (hIs : ¬ M.Spanning I) :
    M.closure I = I := by
  refine subset_antisymm (fun e he ↦ by_contra fun heI ↦ ?_) (subset_closure _ _)
  rw [spanning_iff_closure_eq, ← closure_closure, ← insert_eq_of_mem he,
    closure_insert_closure_eq_closure_insert, ← spanning_iff_closure_eq] at hIs

  have hIe : M.Indep (insert e I) :=
    (hM.indep_or_spanning _ (by aesop_mat)).elim id fun h ↦ (hIs h).elim
  rw [(hIe.subset (subset_insert _ _)).mem_closure_iff_of_notMem heI] at he
  exact he.not_indep hIe

-- lemma IsUniform.isBase_of_isBase_of_finDiff {B B' : Set α} (hM : M.IsUniform) (hB : M.IsBase B)
--     (h_fin : FinDiff B B') (hB' : B' ⊆ M.E) : M.IsBase B' := by
--   obtain h | h := (B' \ B).eq_empty_or_nonempty
--   · rw [diff_eq_empty] at h
--     rwa [h_fin.symm.eq_of_subset h]
--   obtain ⟨f, hfB, hfB'⟩ := h_fin.nonempty_of_nonempty h
--   obtain ⟨e, heB', heB⟩ := h

--   have hrw : (B' \ insert e (B \ {f})) = ((B' \ B) \ {e}) := by aesop
--   have IH : (B' \ insert e (B \ {f})).encard < (B' \ B).encard := by
--     rw [hrw, ← encard_diff_singleton_add_one (show e ∈ B' \ B from ⟨heB', heB⟩),
--       ENat.lt_add_one_iff]
--     simp_rw [encard_ne_top_iff]
--     exact h_fin.diff_right_finite.diff

--   apply hM.isBase_of_isBase_of_finDiff (hM.exchange hB ⟨hB' heB', heB⟩ hfB)
--   rwa [finDiff_iff, insert_diff_of_mem _ heB', diff_diff_comm,
--     and_iff_right h_fin.diff_left_finite.diff, ← singleton_union, union_comm, ← diff_diff,
--     diff_diff_right, inter_singleton_eq_empty.2 hfB', union_empty,
--     ← WithTop.add_right_inj (z := 1) (by simp),
--     encard_diff_singleton_add_one (show f ∈ B \ B' from ⟨hfB, hfB'⟩),
--     encard_diff_singleton_add_one (show e ∈ B' \ B from ⟨heB', heB⟩), h_fin.encard_diff_eq]
-- termination_by (B' \ B).encard

lemma maximal_right_of_forall_ge {α : Type*} {P Q : α → Prop} {a : α} [PartialOrder α]
    (hP : ∀ ⦃x y⦄, P x → x ≤ y → P y) (h : Maximal (fun x ↦ P x ∧ Q x) a) : Maximal Q a :=
  ⟨h.prop.2, fun _ hb hab ↦ h.le_of_ge ⟨hP h.prop.1 hab, hb⟩ hab⟩

end Infinite

section Finite

variable {a b n : ℕ}

/-- `M.IsFinRankUniform a` means that `M` is a uniform matroid of rank `a ∈ ℕ`. -/
@[mk_iff]
structure IsFinRankUniform (M : Matroid α) (a : ℕ) : Prop where
  eRank_eq : M.eRank = a
  isUniform : M.IsUniform

lemma IsFinRankUniform.le (h : M.IsFinRankUniform a) : a ≤ M.E.encard := by
  grw [← h.eRank_eq, M.eRank_le_encard_ground]

lemma IsFinRankUniform.rankFinite (h : M.IsFinRankUniform a) : M.RankFinite := by
  simp [← eRank_ne_top_iff, h.eRank_eq]

lemma IsFinRankUniform.eq_unifOn (h : M.IsFinRankUniform a) : M = unifOn M.E a := by
  refine ext_indep rfl fun I hIE ↦ ?_
  obtain hI | hI := M.indep_or_dep hIE
  · simp [hI.encard_le_eRank.trans h.eRank_eq.le, hI, hIE]
  obtain ⟨J, hJI⟩ := M.exists_isBasis I
  have hfin := h.rankFinite
  simp only [hI.not_indep, unifOn_indep_iff, hIE, and_true, false_iff, not_le, gt_iff_lt]
  rw [← h.eRank_eq, ← (hJI.isBase_of_spanning (h.isUniform.spanning_of_dep hI)).encard_eq_eRank]
  refine Finite.encard_lt_encard hJI.indep.finite <| hJI.subset.ssubset_of_ne ?_
  rintro rfl
  exact hI.not_indep hJI.indep

lemma IsFinRankUniform.exists_eq_unifOn (h : M.IsFinRankUniform a) :
    ∃ E, M = unifOn E a ∧ a ≤ E.encard :=
  ⟨M.E, h.eq_unifOn, by grw [← h.eRank_eq, ← M.eRank_le_encard_ground]⟩

lemma unifOn_isFinRankUniform (haE : a ≤ E.encard) : (unifOn E a).IsFinRankUniform a :=
  ⟨unifOn_eRank_eq' haE, by simp⟩

lemma isFinRankUniform_iff_eq_unifOn :
    M.IsFinRankUniform a ↔ M = unifOn M.E a ∧ a ≤ M.E.encard := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨E, rfl, haE⟩ := h.exists_eq_unifOn
    simpa
  rw [h.1]
  exact unifOn_isFinRankUniform h.2

lemma IsFinRankUniform.indep_iff (hM : M.IsFinRankUniform a) :
    M.Indep I ↔ I.encard ≤ a ∧ I ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  simp

lemma IsFinRankUniform.isCircuit_iff (hM : M.IsFinRankUniform a) :
    M.IsCircuit C ↔ C.encard = a + 1 ∧ C ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  rw [unifOn_isCircuit_iff, unifOn_ground_eq]

lemma IsFinRankUniform.dep_iff (hM : M.IsFinRankUniform a) : M.Dep X ↔ a < X.encard ∧ X ⊆ M.E := by
  grind [Dep, hM.indep_iff]

lemma IsFinRankUniform.isBase_iff (hM : M.IsFinRankUniform a) :
    M.IsBase B ↔ B.encard = a ∧ B ⊆ M.E := by
  by_cases hBE : B ⊆ M.E
  · obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
    rw [unifOn_isBase_iff _ (by simpa), and_iff_left hBE]
    assumption
  exact iff_of_false (fun h ↦ hBE h.subset_ground) <| by simp [hBE]

lemma IsFinRankUniform.isCocircuit_iff (hM : M.IsFinRankUniform a) :
    M.IsCocircuit C ↔ (M.E \ C).encard + 1 = a ∧ C ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  rwa [unifOn_ground_eq, unifOn_isCocircuit_iff]

lemma IsFinRankUniform.spanning_iff (hM : M.IsFinRankUniform a) :
    M.Spanning X ↔ a ≤ X.encard ∧ X ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  by_cases! hXE : ¬ X ⊆ E; grind [Spanning.subset_ground]
  rw [unifOn_spanning_iff hle hXE, unifOn_ground_eq, and_iff_left hXE]

/-- A uniform matroid whose rank is finite is one of the obvious ones. -/
lemma IsUniform.isFinRankUniform [M.RankFinite] (hM : M.IsUniform) :
    ∃ a, M.IsFinRankUniform a :=
  ⟨M.rank, M.cast_rank_eq.symm, hM⟩

/-- A finitary non-free uniform matroid is a finite-rank uniform matroid. -/
lemma IsUniform.isFinRankUniform_of_finitary [M.Finitary] [M✶.RankPos] (hM : M.IsUniform) :
    ∃ a, M.IsFinRankUniform a := by
  suffices M.RankFinite from hM.isFinRankUniform
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  grw [← eRank_ne_top_iff, ← (hM.spanning_of_dep hC.dep).eRk_eq, ← lt_top_iff_ne_top,
    eRk_le_encard, encard_lt_top_iff]
  exact hC.finite

lemma IsUniform.eq_freeOn_or_isFinRankUniform [M.Finitary] (hM : M.IsUniform) :
    ∃ (E : Set α), M = freeOn E ∨ ∃ a, M.IsFinRankUniform a := by
  obtain ⟨E, rfl⟩ | hr := M.exists_eq_freeOn_or_rankPos_dual
  · exact ⟨E, .inl rfl⟩
  simp [hM.isFinRankUniform_of_finitary]

/-- `M.IsFiniteUniform a b n` means that `M` is a finite uniform matroid of rank `a` and corank `b`,
with `n` elements.

We have `a + b = n` for every such matroid, but the redundancy helps with duality. -/
@[mk_iff]
structure IsFiniteUniform (M : Matroid α) (a b n : ℕ) : Prop extends M.IsFinRankUniform a where
  encard_eq : M.E.encard = n
  eRank_dual_eq : M✶.eRank = b

lemma IsFiniteUniform.finite (hM : M.IsFiniteUniform a b n) : M.Finite :=
  ⟨encard_lt_top_iff.1 <| by simp [hM.encard_eq]⟩

lemma IsFiniteUniform.add_eq {a b n : ℕ} (h : M.IsFiniteUniform a b n) : a + b = n := by
  rw [← ENat.coe_inj, ← h.encard_eq, ← eRank_add_eRank_dual, h.eRank_eq, h.eRank_dual_eq,
    ENat.coe_add]

@[simp]
lemma IsFiniteUniform.sub_eq_left (h : M.IsFiniteUniform a b n) : n - a = b := by
  simp [← h.add_eq]

@[simp]
lemma IsFiniteUniform.sub_eq_right (h : M.IsFiniteUniform a b n) : n - b = a := by
  simp [← h.add_eq]

lemma IsUniform.exists_isFiniteUniform_of_finite (hM : M.IsUniform) [M.Finite] :
    ∃ a b n, M.IsFiniteUniform a b n ∧ a = M.eRank ∧ b = M✶.eRank ∧ n = M.E.encard := by
  have hcard := M.ground_finite.encard_eq_coe_toFinset_card
  have hr := M.cast_rank_eq
  have hr' := M✶.cast_rank_eq
  exact ⟨M.rank, M✶.rank, _, ⟨⟨hr.symm, hM⟩, hcard, hr'.symm⟩, hr, hr', hcard.symm⟩

lemma IsFinRankUniform.exists_isFiniteUniform_of_finite (h : M.IsFinRankUniform a) [M.Finite] :
    ∃ b n, M.IsFiniteUniform a b n ∧ b = M✶.eRank ∧ n = M.E.encard := by
  obtain ⟨a', b, n, hM1, ha, hb, hn⟩ := h.isUniform.exists_isFiniteUniform_of_finite
  rw [h.eRank_eq, ENat.coe_inj] at ha
  exact ⟨b, n, ha ▸ hM1, hb, hn⟩

lemma isFiniteUniform_dual_iff : M✶.IsFiniteUniform a b n ↔ M.IsFiniteUniform b a n := by
  simp only [isFiniteUniform_iff, isFinRankUniform_iff, uniform_dual_iff, dual_ground, dual_dual]
  tauto

alias ⟨IsFiniteUniform.of_dual, IsFiniteUniform.dual⟩ := isFiniteUniform_dual_iff

lemma isFiniteUniform_unifOn {E : Set α} (hE : E.Finite) (a : ℕ) (haE : a ≤ E.encard) :
    ∃ b n, (unifOn E a).IsFiniteUniform a b n ∧ n = E.encard := by
  have : (unifOn E a).Finite := ⟨hE⟩
  obtain ⟨b, n, habc, hb, hn⟩ := (unifOn_isFinRankUniform haE).exists_isFiniteUniform_of_finite
  exact ⟨b, n, habc, hn⟩

lemma IsFiniteUniform.dual_eq_self (h : M.IsFiniteUniform a a b) : M✶ = M := by
  obtain ⟨E, rfl, ha⟩ := h.exists_eq_unifOn
  rw [unifOn_dual_eq']
  rw [← unifOn_ground_eq E, h.encard_eq, ← h.add_eq, Nat.cast_add]

/-- `M` is isomorphic to a rank-`a` uniform matroid on a ground set of size `b`.
Probably deprecated in favour of `IsFiniteUniform`. -/
@[mk_iff]
structure IsFiniteRankUniform (M : Matroid α) (a : ℕ) (b : ℕ∞) : Prop where
  encard_eq : M.E.encard = b
  eRank_eq : M.eRank = a
  isUniform : M.IsUniform

lemma IsFiniteRankUniform.le {a : ℕ} {b : ℕ∞} (h : M.IsFiniteRankUniform a b) : a ≤ b := by
  grw [← h.eRank_eq, M.eRank_le_encard_ground, h.encard_eq]

lemma IsFiniteRankUniform.finite (hM : M.IsFiniteRankUniform a b) : M.Finite :=
  ⟨encard_lt_top_iff.1 <| by simp [hM.encard_eq]⟩

lemma IsFiniteRankUniform.exists_eq_unifOn {b : ℕ∞} (hM : M.IsFiniteRankUniform a b) :
    ∃ (E : Set α), E.encard = b ∧ M = unifOn E a := by
  refine ⟨M.E, hM.encard_eq, ext_indep rfl fun I hI ↦ ?_⟩
  rw [unifOn_indep_iff, and_iff_left hI]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · grw [h.encard_le_eRank, ← hM.eRank_eq]
  obtain ⟨J, hJ⟩ := M.exists_isBasis I
  refine (hM.isUniform.indep_or_spanning I).elim id fun hI ↦ ?_
  refine Finite.eq_of_subset_of_encard_le' ?_ hJ.subset (h.trans ?_) ▸ hJ.indep
  · grw [← encard_lt_top_iff, h]
    simp
  grw [(hJ.isBase_of_spanning hI).encard_eq_eRank, hM.eRank_eq]

lemma IsFiniteRankUniform.indep_iff {b : ℕ∞} (hM : M.IsFiniteRankUniform a b) :
    M.Indep I ↔ I.encard ≤ a ∧ I ⊆ M.E := by
  obtain ⟨E, hE, rfl⟩ := hM.exists_eq_unifOn
  rw [unifOn_indep_iff, unifOn_ground_eq]

lemma IsFiniteRankUniform.isBase_iff {b : ℕ∞} (hM : M.IsFiniteRankUniform a b) :
    M.IsBase B ↔ B.encard = a ∧ B ⊆ M.E := by
  by_cases hBE : B ⊆ M.E
  · obtain ⟨E, hE, rfl⟩ := hM.exists_eq_unifOn
    rw [unifOn_isBase_iff _ (by simpa), and_iff_left hBE]
    grw [hE, hM.le]
  exact iff_of_false (fun h ↦ hBE h.subset_ground) <| by simp [hBE]

lemma IsFiniteRankUniform.isCocircuit_iff (hM : M.IsFiniteRankUniform a b) :
    M.IsCocircuit C ↔ C.encard + a = b + 1 ∧ C ⊆ M.E := by
  obtain ⟨E, hE, rfl⟩ := hM.exists_eq_unifOn
  wlog hCE : C ⊆ E with aux; grind [IsCocircuit.subset_ground]
  have hCt : C.encard ≠ ⊤ := by grw [← lt_top_iff_ne_top, hCE]; simp [hE]
  grw [unifOn_isCocircuit_iff (by simp [hE, hM.le]), ← hE, unifOn_ground_eq,
    ← encard_diff_add_encard_of_subset hCE, add_comm _ C.encard, add_assoc,
    ENat.add_eq_add_left_iff, or_iff_left hCt, eq_comm]

lemma IsFiniteRankUniform.spanning_iff {b : ℕ∞} (hM : M.IsFiniteRankUniform a b) :
    M.Spanning X ↔ a ≤ X.encard ∧ X ⊆ M.E := by
  wlog hXE : X ⊆ M.E; grind [Spanning.subset_ground]
  simp_rw [spanning_iff_exists_isBase_subset hXE, hM.isBase_iff, and_iff_left hXE]
  exact ⟨fun ⟨B, hB, hBX⟩ ↦ by grw [← hB.1, hBX], fun h ↦ by grind [exists_subset_encard_eq h]⟩

lemma IsFiniteRankUniform.unif_isoRestr {b : ℕ∞} (hM : M.IsFiniteRankUniform a b) (h : b' ≤ b) :
    Nonempty (unif a b' ≤ir M) := by
  obtain ⟨E, hEb, rfl⟩ := IsFiniteRankUniform.exists_eq_unifOn hM
  apply unif_isoRestr_unifOn
  grw [h, hEb]

/-- A finite-rank uniform matroid is one of the obvious ones. -/
lemma IsUniform.isFiniteRankUniform [M.RankFinite] (hM : M.IsUniform) :
    ∃ a b, M.IsFiniteRankUniform a b :=
  ⟨_, _, rfl, M.cast_rank_eq.symm, hM⟩


/-- A finitary non-free uniform matroid is one of the obvious ones. -/
lemma IsUniform.isFiniteRankUniform_of_finitary [M.Finitary] [M✶.RankPos] (hM : M.IsUniform) :
    ∃ a b, M.IsFiniteRankUniform a b := by
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  obtain ⟨e, heC⟩ := hC.nonempty
  obtain hCi | hCs := hM.indep_or_spanning C
  · exact (hC.not_indep hCi).elim
  have := ((hC.diff_singleton_isBasis heC).isBase_of_spanning hCs).rankFinite_of_finite
    hC.finite.diff
  exact hM.isFiniteRankUniform

/-- A finitary non-free uniform matroid is free or is one of the obvious ones. -/
lemma IsUniform.eq_freeOn_or_isFiniteRankUniform [M.Finitary] (hM : M.IsUniform) :
    ∃ (E : Set α), M = freeOn E ∨ ∃ a b, M.IsFiniteRankUniform a b := by
  obtain ⟨E, rfl⟩ | hr := M.exists_eq_freeOn_or_rankPos_dual
  · exact ⟨E, .inl rfl⟩
  simp [hM.isFiniteRankUniform_of_finitary]

/-- A finite-rank uniform matroid is one of the obvious ones - maybe use `IsFiniteRankUniform`
instead  -/
lemma IsUniform.exists_eq_unifOn [M.RankFinite] (hM : M.IsUniform) :
    ∃ (E : Set α) (k : ℕ), k ≤ E.encard ∧ M = unifOn E k ∧ M.eRank = k := by
  obtain ⟨E, hE, h_eq⟩ := IsFiniteRankUniform.exists_eq_unifOn ⟨rfl, M.cast_rank_eq.symm, hM⟩
  obtain rfl : E = M.E := by rw [h_eq, unifOn_ground_eq]
  exact ⟨M.E, M.rank, by grw [M.cast_rank_eq, M.eRank_le_encard_ground], h_eq, M.cast_rank_eq.symm⟩

lemma unifOn_isUniform (E : Set α) (k : ℕ) : (unifOn E k).IsUniform := by
  intro X (hX : X ⊆ E)
  rw [unifOn_indep_iff, unifOn_spanning_iff']
  grind

lemma unifOn_isFiniteRank_uniform (hab : a ≤ E.encard) :
    (unifOn E a).IsFiniteRankUniform a E.encard :=
  ⟨rfl, unifOn_eRank_eq' hab, unifOn_isUniform ..⟩

lemma IsFiniteRankUniform.dual {a b : ℕ} (hM : M.IsFiniteRankUniform a b) :
    M✶.IsFiniteRankUniform (b - a) b := by
  refine ⟨by simp [hM.encard_eq], ?_, hM.isUniform.dual⟩
  have h_eq := M.eRank_add_eRank_dual
  rw [hM.encard_eq, hM.eRank_eq] at h_eq
  enat_to_nat!; lia

lemma IsFiniteRankUniform.dual_of_add {a b : ℕ} (hM : M.IsFiniteRankUniform a (a + b)) :
    M✶.IsFiniteRankUniform b (a + b) := by
  simpa using hM.dual

lemma IsFiniteRankUniform.dual_eq_self {a : ℕ} (hM : M.IsFiniteRankUniform a (2 * a)) : M✶ = M := by
  obtain ⟨E, hE, rfl⟩ := hM.exists_eq_unifOn
  rw [unifOn_dual_eq_self hE]

lemma IsFiniteRankUniform.bDual_eq_self {a : ℕ} {d : Bool} (hM : M.IsFiniteRankUniform a (2 * a)) :
    M.bDual d = M := by
  cases d
  · rfl
  exact hM.dual_eq_self

lemma IsFiniteRankUniform.of_dual_self {a : ℕ} (hM : M✶.IsFiniteRankUniform a (2 * a)) :
    M.IsFiniteRankUniform a (2 * a) := by
  rwa [← M.dual_dual, hM.dual_eq_self]

lemma IsFiniteRankUniform.of_bDual_self {a : ℕ} {d : Bool}
    (hM : (M.bDual d).IsFiniteRankUniform a (2 * a)) : M.IsFiniteRankUniform a (2 * a) := by
  cases d
  · assumption
  exact hM.of_dual_self

lemma IsFiniteRankUniform.dual_eq_self₂₄ (hM : M.IsFiniteRankUniform 2 4) : M✶ = M :=
  hM.dual_eq_self

lemma isFiniteRankUniform_iff_nonempty_iso {a b : ℕ} (hab : a ≤ b) :
    M.IsFiniteRankUniform a b ↔ Nonempty (M ≂ unif a b) := by
  rw [nonempty_iso_unif_iff]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨E, hE, rfl⟩ := h.exists_eq_unifOn
    use E
  rintro ⟨E, rfl, hE⟩
  rw [← hE]
  exact unifOn_isFiniteRank_uniform <| by simpa [hE]

/-- A finitary non-free uniform matroid is one of the obvious ones.
maybe use `IsFiniteRankUniform` instead-/
lemma IsUniform.exists_eq_unifOn_of_finitary [M.Finitary] [M✶.RankPos] (hM : M.IsUniform) :
    ∃ (E : Set α) (k : ℕ), k ≤ E.encard ∧ M = unifOn E k ∧ M.eRank = k := by
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  obtain ⟨e, heC⟩ := hC.nonempty
  obtain hCi | hCs := hM.indep_or_spanning C
  · exact (hC.not_indep hCi).elim
  have := ((hC.diff_singleton_isBasis heC).isBase_of_spanning hCs).rankFinite_of_finite
    hC.finite.diff
  exact hM.exists_eq_unifOn

/-- Don't use. -/
lemma IsUniform.exists_eq_freeOn_or_unifOn_of_finitary [M.Finitary] (hM : M.IsUniform) :
    ∃ (E : Set α), M = freeOn E ∨ ∃ (k : ℕ), k ≤ E.encard ∧ M = unifOn E k ∧ M.eRank = k := by
  obtain ⟨E, rfl⟩ | hr := M.exists_eq_freeOn_or_rankPos_dual
  · exact ⟨E, .inl rfl⟩
  obtain ⟨E, k, hle, rfl, hk⟩ := hM.exists_eq_unifOn_of_finitary
  exact ⟨E, .inr ⟨k, hle, rfl, hk⟩⟩

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
  simp only [uniform_iff_forall_insert_diff_singleton, uniformMatroidOfBase_IsBase,
    uniformMatroidOfBase_E, mem_diff, and_imp]
  exact fun B e f hB heE he hf ↦ exch hB hf ⟨heE, he⟩

-- lemma IsBase.finDiff_of_finite_diff (hB : M.IsBase B) (hB' : M.IsBase B')
--  (hBB' : (B \ B').Finite) :
--     FinDiff B B' := by
--   rw [finDiff_iff, and_iff_right hBB', hB.encard_diff_comm hB']



section Strong



end Strong

section LowRank

lemma eq_unifOn_of_eRank_le_one [M.Loopless] (hM : M.eRank ≤ 1) : ∃ E, M = unifOn E 1 := by
  simp +contextual only [ext_iff_indep, unifOn_ground_eq, unifOn_indep_iff, exists_eq_left',
    and_true]
  exact fun I hIE ↦ ⟨fun hI ↦ hI.encard_le_eRank.trans hM,
    fun hI ↦ subsingleton_indep (encard_le_one_iff_subsingleton.1 hI) hIE⟩

lemma isFiniteRankUniform_of_eRank_le_one [M.Loopless] [M.Nonempty] (hM : M.eRank ≤ 1) :
    ∃ b, M.IsFiniteRankUniform 1 b := by
  obtain ⟨E, rfl⟩ := eq_unifOn_of_eRank_le_one hM
  refine ⟨E.encard, unifOn_isFiniteRank_uniform ?_⟩
  grw [Nat.cast_one, one_le_encard_iff_nonempty]
  exact (unifOn E 1).ground_nonempty

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

lemma isFiniteRankUniform_of_eRank_le_two [M.Simple] (hM : M.eRank ≤ 2) (hnt : M.E.Nontrivial) :
    ∃ b, M.IsFiniteRankUniform 2 b := by
  obtain ⟨E, rfl⟩ := eq_unifOn_of_eRank_le_two hM
  exact ⟨E.encard, unifOn_isFiniteRank_uniform <| two_le_encard_iff_nontrivial.2 hnt⟩

@[simp]
lemma unifOn_one_dual (E : Set α) : (unifOn E 1)✶ = circuitOn E := by
  rw [← circuitOn_dual, dual_dual]

theorem nonempty_iso_line_iff {n : ℕ} :
    Nonempty (M ≂ unif 2 n) ↔ M.Simple ∧ M.eRank ≤ 2 ∧ M.E.encard = n := by
  simp [nonempty_iso_unif_iff', ← and_assoc, eq_unifOn_two_iff, and_comm]


  -- simp [nonempty_iso_unif_iff', ← and_assoc, eq_unifOn_two_iff, and_comm]

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

lemma unifOn_loopless_iff {n : ℕ} :
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
    · simp [unifOn_loopless_iff.1 h.loopless]
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
  exact fun e f he hf ↦ (encard_pair_le e f).trans <| by simpa

@[simp]
lemma unifOn_map {β : Type*} (E : Set α) (f : α → β) (hf : InjOn f E) (a : ℕ) :
    (unifOn E a).map f hf = unifOn (f '' E) a := by
  refine ext_indep rfl fun I hI ↦ ?_
  simp only [map_ground, unifOn_ground_eq] at hI
  obtain ⟨I, hIE, rfl⟩ := subset_image_iff.1 hI
  rw [map_image_indep_iff hIE, unifOn_indep_iff, unifOn_indep_iff, (hf.mono hIE).encard_image,
    and_iff_left hIE, and_iff_left hI]

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

set_option backward.isDefEq.respectTransparency false in
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

lemma NoUniformMinor.le_minor {a b b' : ℕ} (hM : M.NoUniformMinor a b) (ha : a ≤ b) (hb' : b ≤ b') :
    M.NoUniformMinor a b' := by
  contrapose! hM
  simp only [not_noUniformMinor_iff] at hM ⊢
  exact ⟨((unif_isoMinor_unif_iff' ha (Nat.le_trans ha hb')).2 ⟨ Nat.le_refl a,
      Nat.sub_le_sub_right hb' a ⟩).some.trans hM.some⟩

lemma NoUniformMinor.lt_of_isoMinor {N : Matroid α} {a b : ℕ} {b' : ℕ∞} (h : M.NoUniformMinor a b)
    (hNM : N ≤i M) (hN : N.IsFiniteRankUniform a b') : b' < b := by
  by_contra! hle
  obtain ⟨E, rfl, rfl⟩ := hN.exists_eq_unifOn
  obtain ⟨φ⟩ := unif_isoRestr_unifOn (a := a) hle
  exact h.elim (IsoMinor.trans φ.isoMinor hNM)

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
