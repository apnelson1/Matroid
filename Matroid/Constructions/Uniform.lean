import Matroid.Constructions.Truncate
import Mathlib.Tactic.Linarith
import Matroid.Simple
import Matroid.ForMathlib.Card

variable {α : Type*} {M : Matroid α} {E I B X C : Set α} {k : ℕ∞}

namespace Matroid

open Set

section Uniform

/-- A uniform matroid with a given rank `k` and ground set `E`. If `k = ⊤`, then every set is
  independent. ` -/
def unifOn {α : Type*} (E : Set α) (k : ℕ∞) : Matroid α := (freeOn E).truncate k

@[simp] theorem unifOn_ground_eq (E : Set α) : (unifOn E k).E = E := by
  cases k <;> rfl

@[simp] theorem unifOn_indep_iff : (unifOn E k).Indep I ↔ I.encard ≤ k ∧ I ⊆ E := by
  simp [unifOn, and_comm]

@[simp] theorem unifOn_top (E : Set α) : unifOn E ⊤ = freeOn E := by
  rw [unifOn, truncate_top]

@[simp] theorem unifOn_zero (E : Set α) : unifOn E 0 = loopyOn E := by
  simp [unifOn]

@[simp] theorem unifOn_empty (α : Type*) (a : ℕ) : unifOn ∅ a = emptyOn α := by
  simp [unifOn]

theorem unifOn_eq_unifOn_min (E : Set α) (k : ℕ∞) : unifOn E k = unifOn E (min k E.encard) := by
  simp only [ge_iff_le, eq_iff_indep_iff_indep_forall, unifOn_ground_eq, unifOn_indep_iff,
    le_min_iff, and_congr_left_iff, iff_self_and, true_and]
  exact fun I hI _ _ ↦ encard_mono hI

@[simp] theorem unifOn_encard : unifOn E E.encard = freeOn E := by
  rw [unifOn, truncate_eq_self_of_rk_le (freeOn_erk_eq _).le]

theorem unifOn_eq_of_le (h : E.encard ≤ k) : unifOn E k = freeOn E := by
  rw [unifOn, truncate_eq_self_of_rk_le (by rwa [freeOn_erk_eq])]

theorem unifOn_base_iff {k : ℕ} (hk : k ≤ E.encard) (hBE : B ⊆ E) :
    (unifOn E k).Base B ↔ B.encard = k := by
  rw [unifOn, truncate_base_iff, freeOn_indep_iff, and_iff_right hBE]; rwa [freeOn_erk_eq]

theorem unifOn_base_iff' (hktop : k ≠ ⊤) (hk : k ≤ E.encard) (hBE : B ⊆ E) :
    (unifOn E k).Base B ↔ B.encard = k := by
  lift k to ℕ using hktop; rw [unifOn_base_iff hk hBE]

theorem unifOn_er_eq (E : Set α) (k : ℕ∞) (hX : X ⊆ E) : (unifOn E k).er X = min X.encard k := by
  rw [unifOn, truncate_er_eq, freeOn_er_eq hX]

theorem unifOn_er_eq' (E : Set α) (k : ℕ∞) : (unifOn E k).er X = min (X ∩ E).encard k := by
  rw [← er_inter_ground_eq, unifOn_er_eq _ _ (by rw [unifOn_ground_eq]; apply inter_subset_right),
    unifOn_ground_eq]

theorem unifOn_erk_eq (E : Set α) (k : ℕ∞) : (unifOn E k).erk = min E.encard k := by
  rw [erk_eq_er_ground, unifOn_ground_eq, unifOn_er_eq _ _ Subset.rfl]

instance {k : ℕ} {E : Set α} : FiniteRk (unifOn E k) := by
  rw [← rFin_ground_iff_finiteRk, rFin, unifOn_er_eq _ _ (by simp [rfl.subset])]
  exact (min_le_right _ _).trans_lt (WithTop.coe_lt_top _)

@[simp] theorem unifOn_spanning_iff' {k : ℕ∞} (hk : k ≠ ⊤) :
    (unifOn E k).Spanning X ↔ (k ≤ X.encard ∧ X ⊆ E) ∨ X = E  := by
  lift k to ℕ using hk
  rw [spanning_iff_er', erk_eq_er_ground, unifOn_ground_eq, unifOn_er_eq', unifOn_er_eq',
    le_min_iff, min_le_iff, min_le_iff, iff_true_intro (le_refl _), or_true, and_true, inter_self]
  refine' ⟨fun ⟨h, hXE⟩ ↦ h.elim (fun h ↦ _) (fun h ↦ Or.inl ⟨_,hXE⟩),
    fun h ↦ h.elim (fun ⟨hle, hXE⟩ ↦ ⟨Or.inr (by rwa [inter_eq_self_of_subset_left hXE]), hXE⟩ ) _⟩
  · refine' X.finite_or_infinite.elim (fun hfin ↦ Or.inr _) (fun hinf ↦ Or.inl ⟨_, hXE⟩)
    · rw [← (hfin.inter_of_left E).eq_of_subset_of_encard_le' (inter_subset_right _ _) h,
        inter_eq_self_of_subset_left hXE]
    rw [hinf.encard_eq]
    apply le_top
  · exact h.trans (encard_mono (inter_subset_left _ _))
  rintro rfl
  rw [inter_self]
  exact ⟨Or.inl rfl.le, Subset.rfl⟩

theorem unifOn_spanning_iff {k : ℕ} (hk : k ≤ E.encard) (hX : X ⊆ E) :
    (unifOn E k).Spanning X ↔ k ≤ X.encard := by
  rw [← ENat.some_eq_coe, unifOn_spanning_iff' (WithTop.coe_lt_top k).ne, and_iff_left hX,
    or_iff_left_iff_imp]
  rintro rfl
  assumption

theorem eq_unifOn_iff : M = unifOn E k ↔ M.E = E ∧ ∀ I, M.Indep I ↔ I.encard ≤ k ∧ I ⊆ E :=
  ⟨by rintro rfl; simp,
    fun ⟨hE, h⟩ ↦ eq_of_indep_iff_indep_forall (by simpa) fun I _↦ by simpa using h I⟩

theorem unifOn_dual_eq (hE : E.Finite) : (unifOn E k)﹡ = unifOn E (E.encard - k) := by
  obtain (rfl | hk) := eq_or_ne k ⊤; simp
  lift k to ℕ using hk
  obtain (hle | hlt) := le_or_lt E.encard k
  · rw [unifOn_eq_of_le hle, freeOn_dual_eq, tsub_eq_zero_of_le hle, unifOn_zero]
  refine eq_of_base_iff_base_forall (by simp) (fun B hBE ↦ ?_)
  simp only [dual_ground, unifOn_ground_eq] at hBE
  rw [dual_base_iff', unifOn_base_iff' ((tsub_le_self.trans_lt hE.encard_lt_top).ne) (by simp) hBE,
    unifOn_ground_eq, and_iff_left hBE, unifOn_base_iff hlt.le (diff_subset _ _),
    ← WithTop.add_right_cancel_iff (hE.subset hBE).encard_lt_top.ne,
    encard_diff_add_encard_of_subset hBE, Iff.comm, eq_comm, add_comm,
    ← WithTop.add_right_cancel_iff (hlt.trans_le le_top).ne, tsub_add_cancel_of_le hlt.le]

@[simp] theorem unifOn_delete_eq (E D : Set α) (k : ℕ∞) :
    (unifOn E k) ⧹ D = unifOn (E \ D) k := by
  simp_rw [eq_unifOn_iff, delete_ground, unifOn_ground_eq, true_and, delete_indep_iff,
    unifOn_indep_iff, subset_diff, and_assoc, imp_true_iff]

theorem unifOn_contract_eq' {α : Type*} (E C : Set α) {k : ℕ∞} (hk : k ≠ ⊤) :
    ((unifOn E k) ⧸ C) = unifOn (E \ C) (k - (E ∩ C).encard) := by
  lift k to ℕ using hk
  refine' eq_of_spanning_iff_spanning_forall (by simp) (fun S hS ↦ _)
  simp only [ge_iff_le, contract_ground, unifOn_ground_eq, diff_self_inter, subset_diff] at hS
  rw [← contract_inter_ground_eq, unifOn_ground_eq, inter_comm,
    contract_spanning_iff, unifOn_spanning_iff', unifOn_spanning_iff', tsub_le_iff_right,
    iff_true_intro (disjoint_of_subset_right (inter_subset_right _ _) hS.2), and_true,
     ← encard_union_eq (disjoint_of_subset_right (inter_subset_right _ _) hS.2), union_subset_iff,
    and_iff_left (inter_subset_left _ _), and_iff_left hS.1, subset_diff, union_distrib_left,
    and_iff_left hS, union_eq_self_of_subset_left hS.1, inter_eq_left,
    subset_antisymm_iff, subset_diff, and_iff_right hS, diff_subset_iff, union_comm C]
  · exact ((tsub_le_self).trans_lt (WithTop.coe_lt_top k)).ne
  exact WithTop.coe_ne_top

@[simp] theorem unifOn_contract_eq {k : ℕ} :
    ((unifOn E k) ⧸ C) = unifOn (E \ C) (k - (E ∩ C).encard) :=
  unifOn_contract_eq' E C WithTop.coe_ne_top

@[simp] theorem eq_unifOn_two_iff : M = unifOn E 2 ↔ M.E = E ∧ M.erk ≤ 2 ∧ M.Simple := by
  constructor
  · rintro rfl
    simp_rw [unifOn_ground_eq, unifOn_erk_eq, min_le_iff, iff_true_intro rfl.le,
      or_true, true_and, simple_iff_forall_pair_indep, unifOn_ground_eq, unifOn_indep_iff,
      and_iff_right (encard_pair_le _ _)]
    exact pair_subset
  rintro ⟨rfl, hr, hM⟩
  simp only [eq_iff_indep_iff_indep_forall, unifOn_ground_eq, unifOn_indep_iff, true_and]
  exact fun I hIE ↦ ⟨fun hI ↦ ⟨hI.encard_le_erk.trans hr, hIE⟩,
    fun ⟨hcard, _⟩ ↦ indep_of_encard_le_two hcard⟩

instance unifOn_loopless {k : ℕ∞} (E : Set α) : Loopless (unifOn E (k+1)) := by
  simp_rw [loopless_iff_forall_nonloop, ← indep_singleton, unifOn_indep_iff]
  simp

instance unifOn_simple {k : ℕ∞} (E : Set α) : Simple (unifOn E (k+2)) := by
  simp only [simple_iff_forall_pair_indep, unifOn_indep_iff, unifOn_ground_eq,
    mem_singleton_iff, pair_subset_iff]
  exact fun {e f} he hf ↦ ⟨(encard_pair_le e f).trans (self_le_add_left _ _), he, hf⟩

section unif

variable {a b a' b' : ℕ}

/-- A canonical uniform matroid, with rank `a` and ground type `Fin b`.
  (In the junk case where `b < a`, then the matroid is free, and the rank is `b` instead).  -/
def unif (a b : ℕ) := unifOn (univ : Set (Fin b)) a

@[simp] theorem unif_ground_eq (a b : ℕ) : (unif a b).E = univ := rfl

@[simp] theorem unif_indep_iff (I) : (unif a b).Indep I ↔ I.encard ≤ a := by
  rw [unif, unifOn_indep_iff, and_iff_left (subset_univ _)]

@[simp] theorem unif_er_eq (X) : (unif a b).er X = min X.encard a := by
  rw [unif, unifOn_er_eq _ _ (subset_univ _)]

@[simp] theorem unif_erk_eq (a b : ℕ) : (unif a b).erk = min a b := by
  rw [erk_eq_er_ground, unif_er_eq]
  simp only [unif_ground_eq, ge_iff_le, encard_univ_fin, min_comm]
  rfl

theorem unif_erk_eq_of_le (hab : a ≤ b) : (unif a b).erk = a := by
  simpa

theorem unif_base_iff (hab : a ≤ b) {B : Set (Fin b)} : (unif a b).Base B ↔ B.encard = a := by
  rw [unif, unifOn, truncate_base_iff, freeOn_indep_iff, and_iff_right (subset_univ _)]
  rwa [freeOn_erk_eq, encard_univ, PartENat.card_eq_coe_fintype_card, Fintype.card_fin,
    PartENat.withTopEquiv_natCast, Nat.cast_le]

@[simp] theorem unif_base_iff' {B : Set (Fin _)} : (unif a (a + b)).Base B ↔ B.encard = a := by
  rw [unif_base_iff (Nat.le_add_right _ _)]

theorem unif_dual' {n : ℕ} (h : a + b = n) : (unif a n)﹡ = unif b n := by
  subst h
  refine eq_of_base_iff_base_forall rfl (fun B _ ↦ ?_)
  rw [dual_base_iff, unif_ground_eq, unif_base_iff (Nat.le_add_right _ _),
    unif_base_iff (Nat.le_add_left _ _),
    ← WithTop.add_right_cancel_iff (encard_ne_top_iff.2 B.toFinite),
    encard_diff_add_encard_of_subset (subset_univ _), Iff.comm,
    ← WithTop.add_left_cancel_iff (WithTop.coe_ne_top (a := a)), eq_comm]
  convert Iff.rfl
  rw [encard_univ, PartENat.card_eq_coe_fintype_card, Fintype.card_fin,
    PartENat.withTopEquiv_natCast, ENat.some_eq_coe, eq_comm, Nat.cast_add]

instance unif_loopless (a b : ℕ) : Loopless (unif (a + 1) b) := by
  rw [unif, Nat.cast_add, Nat.cast_one]
  infer_instance

instance unif_simple (a b : ℕ) : Simple (unif (a + 2) b) := by
  rw [unif, Nat.cast_add, Nat.cast_two]
  infer_instance

/-- This needs a @[simp] tag even though the proof is `simp`, since the proof uses the RHS. -/
@[simp] theorem unif_eq_loopyOn (b : ℕ) : unif 0 b = loopyOn univ := by
  simp

theorem unif_eq_freeOn (h : b ≤ a) : unif a b = freeOn univ := by
  simpa

/-- The expression for dual of a uniform matroid.
  The junk case where `b < a` still works because the subtraction truncates. -/
@[simp] theorem unif_dual (a b : ℕ) : (unif a b)﹡ = unif (b - a) b := by
  obtain (hab | hba) := le_or_lt a b
  · exact unif_dual' (Nat.add_sub_of_le hab)
  simp [unif_eq_freeOn hba.le, Nat.sub_eq_zero_of_le hba.le]

theorem unif_self_dual (a : ℕ) : (unif a (2*a))﹡ = unif a (2*a) :=
  unif_dual' (two_mul a).symm

theorem isIso_unif_iff : M ≅ (unif a b) ↔ (M = unifOn M.E a ∧ M.E.encard = b) := by
  obtain (rfl | b) := b
  · rw []
    simp only [Nat.zero_eq, eq_emptyOn, isIso_emptyOn_iff, Nat.cast_zero, encard_eq_zero,
      ground_eq_empty_iff, iff_and_self]
    rintro rfl
    simp
  obtain (hα | hα) := isEmpty_or_nonempty α
  · simp only [eq_emptyOn, emptyOn_isIso_iff, emptyOn_ground, encard_empty, Nat.cast_succ,
      true_and]
    rw [← ground_eq_empty_iff, unif_ground_eq, univ_eq_empty_iff]
    simp [eq_comm (a := (0 : ℕ∞))]
  rw [eq_unifOn_iff, and_iff_right rfl]
  refine ⟨fun h ↦ ?_, fun ⟨hi,h⟩ ↦ ?_⟩
  · obtain (⟨rfl, -⟩ | ⟨-, -, ⟨e⟩⟩) := h.empty_or_nonempty_iso
    · simp [emptyOn_isIso_iff, ← ground_eq_empty_iff, unif_ground_eq] at h
    refine ⟨fun I ↦ ⟨fun hI ↦ ⟨?_, hI.subset_ground⟩, fun ⟨hIcard, hIE⟩ ↦ ?_⟩, ?_⟩
    · have hi := e.on_indep hI
      rwa [unif_indep_iff, (e.injOn_ground.mono hI.subset_ground).encard_image] at hi
    · rwa [e.on_indep_iff, unif_indep_iff, (e.injOn_ground.mono hIE).encard_image]
    rw [← e.injOn_ground.encard_image, e.image_ground, unif_ground_eq, encard_univ_fin]

  obtain ⟨f,hf⟩ := (finite_of_encard_eq_coe h).exists_bijOn_of_encard_eq
    ((encard_univ_fin _).symm ▸ h)
  refine (iso_of_forall_indep' hf.toPartialEquiv rfl (by simp) fun I hIE ↦ ?_).isIso
  simp [hi, hIE, (hf.injOn.mono hIE).encard_image]

/-- The forwards direction of `isIso_unif_iff`, stated existentially so that `M` and `b` can be
  substituted out of the context with `obtain ⟨_, rfl, rfl⟩ := h`.  -/
theorem exists_of_isIso_unif (h : M ≅ unif a b) : ∃ X, M = unifOn X a ∧ X.encard = b :=
  ⟨M.E, isIso_unif_iff.1 h⟩

theorem unif_isoMinor_restr (a : ℕ) (hbb' : b ≤ b') : unif a b ≤i unif a b' := by
  set R : Set (Fin b') := range (Fin.castLE hbb')
  have hM : ((unif a b') ↾ R) ≅ unif a b
  · rw [isIso_unif_iff, eq_iff_indep_iff_indep_forall]
    simp only [restrict_ground_eq, unifOn_ground_eq, restrict_indep_iff,
      unif_indep_iff, unifOn_indep_iff, implies_true, forall_const, and_self, true_and]
    rw [← image_univ, Function.Injective.encard_image, encard_univ_fin]
    exact (Fin.castLEEmb hbb').injective
  exact ⟨_, restrict_minor _ (by simp), hM.symm⟩

theorem unif_isoMinor_contr (a b d : ℕ) : unif a b ≤i unif (a+d) (b+d) := by
  rw [← isoMinor_dual_iff, unif_dual, unif_dual]
  have h_eq : b - a = b + d - (a + d)
  · rw [add_tsub_add_eq_tsub_right]
  rw [← h_eq]
  apply unif_isoMinor_restr _ (Nat.le_add_right b d)

theorem unif_isoMinor_unif_iff (hab : a ≤ b) (ha'b' : a' ≤ b') :
    unif a b ≤i unif a' b' ↔ a ≤ a' ∧ b - a ≤ b' - a' := by
  refine ⟨fun h ↦ ?_, fun ⟨hr, hr'⟩  ↦ ?_⟩
  · constructor
    · have hle := h.erk_le_erk
      simp only [unif_erk_eq, ge_iff_le, Nat.cast_le, le_min_iff, min_le_iff] at hle
      obtain ⟨(haa'| hba'), (- | -)⟩ := hle <;> linarith
    have hle := h.dual.erk_le_erk
    rw [unif_dual, unif_dual, unif_erk_eq_of_le (by simp), unif_erk_eq_of_le (by simp)] at hle
    exact (WithTop.le_coe rfl).1 hle
  have hbb' := add_le_add hr hr'
  rw [Nat.add_sub_cancel' hab, Nat.add_sub_cancel' ha'b'] at hbb'

  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨d',rfl⟩ := Nat.exists_eq_add_of_le ha'b'
  refine (unif_isoMinor_contr a b d).trans (unif_isoMinor_restr (a+d) ?_)
  have hb' : b ≤ d' + a
  · zify at hr'; simpa using hr'
  linarith

@[simp] theorem isIso_line_iff {n : ℕ} : M ≅ unif 2 n ↔ M.Simple ∧ M.erk ≤ 2 ∧ M.E.encard = n := by
  simp [isIso_unif_iff, ← and_assoc, and_congr_left_iff, eq_unifOn_two_iff, and_comm]

theorem line_isoRestr_of_simple_er_le_two {n : ℕ} {L : Set α} (hL : (M ↾ L).Simple)
    (hcard : n ≤ L.encard) (hr : M.er L ≤ 2) : unif 2 n ≤ir M := by
  obtain ⟨Y, hYL, hY⟩ := exists_subset_encard_eq hcard
  have hYs := hL.subset hYL
  refine ⟨M ↾ Y, restrict_restriction _ Y hYs.subset_ground, ?_⟩
  rw [IsIso.comm, isIso_unif_iff, eq_unifOn_iff]
  simp only [restrict_ground_eq, restrict_indep_iff, Nat.cast_ofNat, and_congr_left_iff, true_and,
    and_iff_left hY]
  refine fun I hIY ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · exact (hI.encard_le_er_of_subset (hIY.trans hYL)).trans hr
  exact (indep_of_encard_le_two (M := M ↾ Y) hI).of_restrict

theorem no_line_isoRestr_iff {n : ℕ} {M : Matroid α} :
    ¬ (unif 2 n ≤ir M) ↔ ∀ L, (M ↾ L).Simple → M.er L ≤ 2 → L.encard < n := by
  refine ⟨fun h L hL hLr ↦ lt_of_not_le fun hle ↦
    h <| line_isoRestr_of_simple_er_le_two hL hle hLr, fun h hR ↦ ?_⟩
  obtain ⟨N, hNM, hN⟩ := hR
  obtain ⟨L, -, rfl⟩ := hNM.exists_eq_restrict
  rw [IsIso.comm, isIso_unif_iff, eq_unifOn_iff] at hN
  simp only [restrict_ground_eq, restrict_indep_iff, Nat.cast_ofNat, and_congr_left_iff,
    true_and] at hN
  refine (h L ?_ ?_).ne hN.2
  · simp only [simple_iff_forall_pair_indep, restrict_ground_eq, mem_singleton_iff,
      restrict_indep_iff, pair_subset_iff]
    exact fun {e f} he hf ↦ ⟨by simp [hN.1 _ (pair_subset he hf)], he, hf⟩
  obtain ⟨I, hI⟩ := M.exists_basis' L
  rw [← hI.encard, ← hN.1 _ hI.subset]
  exact hI.indep

end unif

end Uniform
