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

lemma IsUniform.not_isCircuitHyperplane (hM : M.IsUniform) (C : Set α) :
    ¬ M.IsCircuitHyperplane C :=
  fun ⟨h1, h2⟩ ↦ by simpa using (isUniform_iff_circuit_cocircuit.1 hM) h1 h2.compl_isCocircuit

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

lemma IsUniform.isBase_of_isBase_of_finDiff {B B' : Set α} (hM : M.IsUniform) (hB : M.IsBase B)
    (h_fin : FinDiff B B') (hB' : B' ⊆ M.E) : M.IsBase B' := by
  induction h_fin using FinDiff.induction with
  | refl B => assumption
  | exchange B X B' hBX hXB' _ _ ih =>
    exact (hM.isFreeBase (ih hB (by grind))).isBase_of_exchange _ hB' hXB'.symm

lemma IsUniform.insert_isCircuit_of_isBase (hM : M.IsUniform) (hB : M.IsBase B) (he : e ∈ M.E \ B) :
    M.IsCircuit (insert e B) := by
  rw [isCircuit_iff_dep_forall_diff_singleton_indep, and_iff_right (hB.insert_dep he)]
  refine fun f hef ↦ IsBase.indep ?_
  obtain rfl | hne := eq_or_ne e f
  · rwa [insert_diff_self_of_notMem he.2]
  rw [← insert_diff_singleton_comm hne]
  exact hM.isBase_insert_diff_singleton hB he <| by grind

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


lemma maximal_right_of_forall_ge {α : Type*} {P Q : α → Prop} {a : α} [PartialOrder α]
    (hP : ∀ ⦃x y⦄, P x → x ≤ y → P y) (h : Maximal (fun x ↦ P x ∧ Q x) a) : Maximal Q a :=
  ⟨h.prop.2, fun _ hb hab ↦ h.le_of_ge ⟨hP h.prop.1 hab, hb⟩ hab⟩

end Infinite


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


section LowRank


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
        simpa +contextual [simple_iff_forall_pair_indep, pair_subset_iff, eq_comm,
          encard_le_one_iff_subsingleton] using h
      exact .inr (.inl ⟨rfl, fun x hxE y hyE ↦ h hxE hyE ⟩)
    exact .inr <| .inr <| by simp
  simp +contextual only [simple_iff_forall_pair_indep, unifOn_ground_eq, unifOn_indep_iff,
    pair_subset_iff, and_self, and_true]
  obtain ⟨rfl, rfl⟩ | ⟨rfl, h⟩ | h := h
  · simp
  · exact fun e f he hf ↦ by simpa [encard_le_one_iff_subsingleton, eq_comm] using h he hf
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
