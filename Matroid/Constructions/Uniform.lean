import Matroid.Constructions.Truncate
import Matroid.ForMathlib.FinDiff
import Mathlib.Tactic.Linarith
import Matroid.Simple
import Matroid.Minor.Iso
import Matroid.ForMathlib.Card
import Matroid.ForMathlib.Set

variable {α : Type*} {M : Matroid α} {E I B X Y C : Set α} {k : ℕ∞} {e f : α}

open Set Set.Notation


namespace Matroid



section Uniform

/-- A uniform matroid with a given rank `k` and ground set `E`.
  If `encard E ≤ k`, then every set is independent. ` -/
def unifOn {α : Type*} (E : Set α) (k : ℕ∞) : Matroid α := (freeOn E).truncateTo k

@[simp] theorem unifOn_ground_eq (E : Set α) : (unifOn E k).E = E := rfl

@[simp] theorem unifOn_indep_iff : (unifOn E k).Indep I ↔ I.encard ≤ k ∧ I ⊆ E := by
  simp [unifOn, and_comm]

@[simp] theorem unifOn_top (E : Set α) : unifOn E ⊤ = freeOn E := by
  rw [unifOn, truncateTo_top]

@[simp] theorem unifOn_zero (E : Set α) : unifOn E 0 = loopyOn E := by
  simp [unifOn]

@[simp] theorem unifOn_empty (α : Type*) (a : ℕ) : unifOn ∅ a = emptyOn α := by
  simp [unifOn]

theorem unifOn_eq_unifOn_min (E : Set α) (k : ℕ∞) : unifOn E k = unifOn E (min k E.encard) := by
  simp only [ge_iff_le, ext_iff_indep, unifOn_ground_eq, unifOn_indep_iff,
    le_min_iff, and_congr_left_iff, iff_self_and, true_and]
  exact fun I hI _ _ ↦ encard_mono hI

@[simp] theorem unifOn_encard : unifOn E E.encard = freeOn E := by
  rw [unifOn, truncate_eq_self_of_rk_le (freeOn_erk_eq _).le]

theorem unifOn_eq_of_le (h : E.encard ≤ k) : unifOn E k = freeOn E := by
  rw [unifOn, truncate_eq_self_of_rk_le (by rwa [freeOn_erk_eq])]

theorem unifOn_base_iff {k : ℕ} (hk : k ≤ E.encard) (hBE : B ⊆ E) :
    (unifOn E k).Base B ↔ B.encard = k := by
  rw [unifOn, truncateTo_base_iff, freeOn_indep_iff, and_iff_right hBE]; rwa [freeOn_erk_eq]

theorem unifOn_base_iff' (hktop : k ≠ ⊤) (hk : k ≤ E.encard) (hBE : B ⊆ E) :
    (unifOn E k).Base B ↔ B.encard = k := by
  lift k to ℕ using hktop; rw [unifOn_base_iff hk hBE]

theorem unifOn_er_eq (E : Set α) (k : ℕ∞) (hX : X ⊆ E) : (unifOn E k).er X = min X.encard k := by
  rw [unifOn, truncateTo_er_eq, freeOn_er_eq hX]

theorem unifOn_er_eq' (E : Set α) (k : ℕ∞) : (unifOn E k).er X = min (X ∩ E).encard k := by
  rw [← er_inter_ground, unifOn_er_eq _ _ (by rw [unifOn_ground_eq]; apply inter_subset_right),
    unifOn_ground_eq]

theorem unifOn_erk_eq (E : Set α) (k : ℕ∞) : (unifOn E k).erk = min E.encard k := by
  rw [erk_def, unifOn_ground_eq, unifOn_er_eq _ _ Subset.rfl]

instance {k : ℕ} {E : Set α} : FiniteRk (unifOn E k) := by
  rw [← rFin_ground_iff_finiteRk, rFin, unifOn_er_eq _ _ (by simp [rfl.subset])]
  exact (min_le_right _ _).trans_lt (WithTop.coe_lt_top _)

theorem unifOn_dual_eq {k : ℕ∞} (hE : E.Finite) : (unifOn E k)✶ = unifOn E (E.encard - k) := by
  obtain (rfl | hk) := eq_or_ne k ⊤
  · simp [ENat.sub_top]
  lift k to ℕ using hk
  obtain (hle | hlt) := le_or_lt E.encard k
  · rw [unifOn_eq_of_le hle, freeOn_dual_eq, tsub_eq_zero_of_le hle, unifOn_zero]
  refine ext_base (by simp) (fun B hBE ↦ ?_)
  simp only [dual_ground, unifOn_ground_eq] at hBE
  rw [dual_base_iff', unifOn_base_iff' ((tsub_le_self.trans_lt hE.encard_lt_top).ne) (by simp) hBE,
    unifOn_ground_eq, and_iff_left hBE, unifOn_base_iff hlt.le diff_subset,
    ← WithTop.add_right_cancel_iff (hE.subset hBE).encard_lt_top.ne,
    encard_diff_add_encard_of_subset hBE, Iff.comm, eq_comm, add_comm,
    ← WithTop.add_right_cancel_iff (hlt.trans_le le_top).ne, tsub_add_cancel_of_le hlt.le]

@[simp] theorem unifOn_spanning_iff' {k : ℕ∞} (hk : k ≠ ⊤) :
    (unifOn E k).Spanning X ↔ (k ≤ X.encard ∧ X ⊆ E) ∨ X = E  := by
  lift k to ℕ using hk
  rw [spanning_iff_er', erk_def, unifOn_ground_eq, unifOn_er_eq', unifOn_er_eq',
    le_min_iff, min_le_iff, min_le_iff, iff_true_intro (le_refl _), or_true, and_true, inter_self]
  refine ⟨fun ⟨h, hXE⟩ ↦ h.elim (fun h ↦ ?_) (fun h ↦ Or.inl ⟨?_,hXE⟩),
    fun h ↦ h.elim (fun ⟨hle, hXE⟩ ↦ ⟨Or.inr (by rwa [inter_eq_self_of_subset_left hXE]), hXE⟩ ) ?_⟩
  · refine X.finite_or_infinite.elim (fun hfin ↦ .inr ?_) (fun hinf ↦ .inl ⟨?_, hXE⟩)
    · rw [← (hfin.inter_of_left E).eq_of_subset_of_encard_le' inter_subset_right h,
        inter_eq_self_of_subset_left hXE]
    rw [hinf.encard_eq]
    apply le_top
  · exact h.trans (encard_mono inter_subset_left)
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
    fun ⟨hE, h⟩ ↦ ext_indep (by simpa) fun I _↦ by simpa using h I⟩

@[simp] theorem unifOn_delete_eq (E D : Set α) (k : ℕ∞) :
    (unifOn E k) ＼ D = unifOn (E \ D) k := by
  simp_rw [eq_unifOn_iff, delete_ground, unifOn_ground_eq, true_and, delete_indep_iff,
    unifOn_indep_iff, subset_diff, and_assoc, imp_true_iff]

theorem unifOn_contract_eq' {α : Type*} (E C : Set α) {k : ℕ∞} (hk : k ≠ ⊤) :
    ((unifOn E k) ／ C) = unifOn (E \ C) (k - (E ∩ C).encard) := by
  lift k to ℕ using hk
  refine ext_spanning (by simp) (fun S hS ↦ ?_)
  simp only [ge_iff_le, contract_ground, unifOn_ground_eq, diff_self_inter, subset_diff] at hS
  rw [← contract_inter_ground_eq, unifOn_ground_eq, inter_comm,
    contract_spanning_iff, unifOn_spanning_iff', unifOn_spanning_iff', tsub_le_iff_right,
    iff_true_intro (disjoint_of_subset_right inter_subset_right hS.2), and_true,
     ← encard_union_eq (disjoint_of_subset_right inter_subset_right hS.2), union_subset_iff,
    and_iff_left inter_subset_left, and_iff_left hS.1, subset_diff, union_inter_distrib_left,
    and_iff_left hS, union_eq_self_of_subset_left hS.1, inter_eq_left,
    subset_antisymm_iff, subset_diff, and_iff_right hS, diff_subset_iff, union_comm C]
  · exact ((tsub_le_self).trans_lt (WithTop.coe_lt_top k)).ne
  exact WithTop.coe_ne_top

@[simp] theorem unifOn_contract_eq {k : ℕ} :
    ((unifOn E k) ／ C) = unifOn (E \ C) (k - (E ∩ C).encard) :=
  unifOn_contract_eq' E C WithTop.coe_ne_top

@[simp] theorem eq_unifOn_two_iff : M = unifOn E 2 ↔ M.E = E ∧ M.erk ≤ 2 ∧ M.Simple := by
  constructor
  · rintro rfl
    simp_rw [unifOn_ground_eq, unifOn_erk_eq, min_le_iff, iff_true_intro rfl.le,
      or_true, true_and, simple_iff_forall_pair_indep, unifOn_ground_eq, unifOn_indep_iff,
      and_iff_right (encard_pair_le _ _)]
    exact fun e f ↦ pair_subset
  rintro ⟨rfl, hr, hM⟩
  simp only [ext_iff_indep, unifOn_ground_eq, unifOn_indep_iff, true_and]
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
  rw [erk_def, unif_er_eq]
  simp only [unif_ground_eq, ge_iff_le, min_comm, encard_univ_fin]; rfl

@[simp] theorem unif_rk_eq (a b : ℕ) : (unif a b).rk = min a b := by
  rw [rk, unif_erk_eq, ENat.toNat_coe]

theorem unif_erk_eq_of_le (hab : a ≤ b) : (unif a b).erk = a := by
  simpa

theorem unif_base_iff (hab : a ≤ b) {B : Set (Fin b)} : (unif a b).Base B ↔ B.encard = a := by
  rw [unif, unifOn, truncateTo_base_iff, freeOn_indep_iff, and_iff_right (subset_univ _)]
  rwa [freeOn_erk_eq, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, Nat.cast_le]

@[simp] theorem unif_base_iff' {B : Set (Fin _)} : (unif a (a + b)).Base B ↔ B.encard = a := by
  rw [unif_base_iff (Nat.le_add_right _ _)]

theorem unif_dual' {n : ℕ} (h : a + b = n) : (unif a n)✶ = unif b n := by
  subst h
  refine ext_base rfl (fun B _ ↦ ?_)
  rw [dual_base_iff, unif_ground_eq, unif_base_iff (Nat.le_add_right _ _),
    unif_base_iff (Nat.le_add_left _ _),
    ← WithTop.add_right_cancel_iff (encard_ne_top_iff.2 B.toFinite),
    encard_diff_add_encard_of_subset (subset_univ _), Iff.comm,
    ← WithTop.add_left_cancel_iff (WithTop.coe_ne_top (a := a)), eq_comm]
  convert Iff.rfl
  rw [encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.some_eq_coe, eq_comm,
    Nat.cast_add]

@[simp] theorem unif_add_left_dual (a b : ℕ) : (unif a (a + b))✶ = unif b (a+b) :=
  unif_dual' rfl

@[simp] theorem unif_add_right_dual (a b : ℕ) : (unif b (a + b))✶ = unif a (a+b) :=
  unif_dual' <| add_comm _ _

instance unif_loopless (a b : ℕ) : Loopless (unif (a + 1) b) := by
  rw [unif, Nat.cast_add, Nat.cast_one]
  infer_instance

instance unif_simple (a b : ℕ) : Simple (unif (a + 2) b) := by
  rw [unif, Nat.cast_add, Nat.cast_two]
  infer_instance

@[simp] theorem unif_zero (b : ℕ) : unif 0 b = loopyOn univ := by
  simp [eq_loopyOn_iff]

theorem unif_eq_freeOn (h : b ≤ a) : unif a b = freeOn univ := by
  simpa [eq_freeOn_iff]

/-- The expression for dual of a uniform matroid.
  The junk case where `b < a` still works because the subtraction truncates. -/
theorem unif_dual (a b : ℕ) : (unif a b)✶ = unif (b - a) b := by
  obtain (hab | hba) := le_or_lt a b
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

theorem nonempty_iso_line_iff {n : ℕ} :
    Nonempty (M ≂ unif 2 n) ↔ M.Simple ∧ M.erk ≤ 2 ∧ M.E.encard = n := by
  simp [nonempty_iso_unif_iff', ← and_assoc, and_congr_left_iff, eq_unifOn_two_iff, and_comm]

noncomputable def unif_isoRestr_unif (a : ℕ) (hbb' : b ≤ b') : unif a b ≤ir unif a b' :=
  let R : Set (Fin b') := range (Fin.castLE hbb')
  have hM : Nonempty (((unif a b') ↾ R) ≂ unif a b) := by
    refine nonempty_iso_unif_iff.2 ⟨R, ?_⟩
    suffices R.encard = b by simpa [ext_iff_indep]
    rw [show R = range (Fin.castLE hbb') from rfl, ← image_univ, Function.Injective.encard_image,
      encard_univ_fin]
    exact (Fin.castLEEmb hbb').injective
  hM.some.symm.isoRestr.trans ((unif a b').restrict_restriction R).isoRestr

noncomputable def unif_isoMinor_contr (a b d : ℕ) : unif a b ≤i unif (a+d) (b+d) := by
  have e := (unif_isoRestr_unif (b-a) (Nat.le_add_right b d)).isoMinor.dual
  rwa [unif_sub_dual, ← Nat.add_sub_add_right b d a, unif_sub_dual] at e

theorem unif_isoMinor_unif_iff {a₁ a₂ d₁ d₂ : ℕ} :
    Nonempty (unif a₁ (a₁ + d₁) ≤i unif a₂ (a₂ + d₂)) ↔ a₁ ≤ a₂ ∧ d₁ ≤ d₂ := by
  refine ⟨fun ⟨e⟩ ↦ ⟨by simpa using e.rk_le, by simpa using IsoMinor.rk_le e.dual⟩, fun h ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h.1
  exact ⟨(unif_isoMinor_contr a₁ (a₁ + d₁) j).trans (unif_isoRestr_unif _ (by linarith)).isoMinor⟩

theorem unif_isoMinor_unif_iff' {a₁ a₂ b₁ b₂ : ℕ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    Nonempty (unif a₁ b₁ ≤i unif a₂ b₂) ↔ a₁ ≤ a₂ ∧ b₁ - a₁ ≤ b₂ - a₂ := by
  obtain ⟨d₁, rfl⟩ := Nat.exists_eq_add_of_le h₁
  obtain ⟨d₂, rfl⟩ := Nat.exists_eq_add_of_le h₂
  rw [add_tsub_cancel_left, add_tsub_cancel_left, unif_isoMinor_unif_iff]

section Infinite

variable {B B' : Set α}

def Uniform (M : Matroid α) :=
  ∀ ⦃B e f⦄, M.Base B → e ∈ M.E \ B → f ∈ B → M.Base (insert e (B \ {f}))

lemma Uniform.dual (hM : M.Uniform) : M✶.Uniform := by
  intro B e f hB he hf
  have hne : e ≠ f := by rintro rfl; exact he.2 hf
  have hBE : B ⊆ M.E := hB.subset_ground
  convert (hM (hB.compl_base_of_dual) (by rwa [diff_diff_cancel_left hBE]) he).compl_base_dual
    using 1
  rw [← union_singleton, ← union_singleton, ← diff_diff, diff_diff_right,
    diff_diff_cancel_left hBE, inter_eq_self_of_subset_right (show {e} ⊆ M.E by simpa using he.1),
    union_diff_distrib, sdiff_eq_left.2 (show Disjoint ({e} : Set α) {f} by simp [hne])]

@[simp] lemma uniform_dual_iff : M✶.Uniform ↔ M.Uniform :=
  ⟨fun h ↦ by simpa using h.dual, Uniform.dual⟩

lemma uniform_iff_forall_indep_or_spanning : M.Uniform ↔ ∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X := by
  refine ⟨fun h X hXE ↦ ?_, fun h B e f hB he hf ↦ ?_⟩
  · obtain ⟨I, hIX⟩ := M.exists_basis X
    obtain ⟨B, hB, rfl⟩ := hIX.exists_base
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
  have hef : e ≠ f := by rintro rfl; exact he.2 hf
  obtain (hi | hs) := h (insert e (B \ {f}))
    (insert_subset he.1 (diff_subset.trans hB.subset_ground))
  · exact hB.exchange_base_of_indep he.2 hi

  have hss : insert e (B \ {f}) ⊆ M.E := insert_subset he.1 (diff_subset.trans hB.subset_ground)
  suffices M✶.Base (M.E \ insert e (B \ {f})) by rwa [base_iff_dual_base_compl]
  rw [spanning_iff_compl_coindep, coindep_def] at hs
  have hrw : insert f ((M.E \ B) \ {e}) = M.E \ insert e (B \ {f}) := by
    rw [eq_comm, ← union_singleton, ← diff_diff, diff_diff_right,
      inter_eq_self_of_subset_right (show {f} ⊆ M.E by simpa using hB.subset_ground hf),
      union_singleton, insert_diff_singleton_comm hef.symm]
  rw [← hrw]
  exact hB.compl_base_dual.exchange_base_of_indep (f := f) (e := e) (by simp [hf]) <| by rwa [hrw]

lemma Uniform.indep_or_spanning (hM : M.Uniform) (hX : X ⊆ M.E) : M.Indep X ∨ M.Spanning X := by
  rw [uniform_iff_forall_indep_or_spanning] at hM
  exact hM X hX

lemma Uniform.closure_not_spanning (hM : M.Uniform) (hIE : I ⊆ M.E) (hIs : ¬ M.Spanning I) :
    M.closure I = I := by
  refine subset_antisymm (fun e he ↦ by_contra fun heI ↦ ?_) (subset_closure _ _)
  rw [spanning_iff_closure_eq, ← closure_closure, ← insert_eq_of_mem he,
    closure_insert_closure_eq_closure_insert, ← spanning_iff_closure_eq] at hIs

  have hIe : M.Indep (insert e I) :=
    (hM.indep_or_spanning (by aesop_mat)).elim id fun h ↦ (hIs h).elim
  rw [(hIe.subset (subset_insert _ _)).mem_closure_iff_of_not_mem heI] at he
  exact he.not_indep hIe

lemma Uniform.base_of_base_of_finDiff {B B' : Set α} (h : M.Uniform) (hB : M.Base B)
    (h_fin : FinDiff B B') (hB' : B' ⊆ M.E) : M.Base B' := by
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
    exact h_fin.diff_right_finite.diff _

  apply h.base_of_base_of_finDiff (h hB ⟨hB' heB', heB⟩ hfB)
  rwa [finDiff_iff, insert_diff_of_mem _ heB', diff_diff_comm,
    and_iff_right (h_fin.diff_left_finite.diff _), ← singleton_union, union_comm, ← diff_diff,
    diff_diff_right, inter_singleton_eq_empty.2 hfB', union_empty,
    ← WithTop.add_right_cancel_iff (a := 1) (by simp),
    encard_diff_singleton_add_one (show f ∈ B \ B' from ⟨hfB, hfB'⟩),
    encard_diff_singleton_add_one (show e ∈ B' \ B from ⟨heB', heB⟩), h_fin.encard_diff_eq]
termination_by (B' \ B).encard

lemma maximal_right_of_forall_ge {α : Type*} {P Q : α → Prop} {a : α} [PartialOrder α]
    (hP : ∀ ⦃x y⦄, P x → x ≤ y → P y) (h : Maximal (fun x ↦ P x ∧ Q x) a) : Maximal Q a :=
  ⟨h.prop.2, fun _ hb hab ↦ h.le_of_ge ⟨hP h.prop.1 hab, hb⟩ hab⟩

@[simps!] def UniformMatroidOfBase (E : Set α) (Base : Set α → Prop)
    (exists_base : ∃ B, Base B)
    (antichain : IsAntichain (· ⊆ ·) (setOf Base))
    (exchange : ∀ ⦃B e f⦄, Base B → e ∈ B → f ∈ E \ B → Base (insert f (B \ {e})))
    (contain : ∀ ⦃I X⦄, I ⊆ X → X ⊆ E → (X \ I).Infinite →
      ∃ B, Base B ∧ ((B ⊆ I) ∨ (I ⊆ B ∧ B ⊆ X) ∨ (X ⊆ B)))
    (subset_ground : ∀ ⦃B⦄, Base B → B ⊆ E) :
    Matroid α :=
Matroid.ofBase E Base exists_base
  (by
    rintro B B' hB hB' e ⟨heB, heB'⟩
    contrapose! heB'
    rwa [antichain.eq hB' hB fun f hfB' ↦ by_contra fun hfB ↦ heB' f ⟨hfB', hfB⟩
      (exchange hB heB ⟨subset_ground hB' hfB', hfB⟩)])
  (by
    intro X hX I hI hIX
    obtain hfin | hinf := (X \ I).finite_or_infinite
    · set S := {A | I ⊆ A ∧ (∃ B, Base B ∧ A ⊆ B) ∧ A ⊆ X} with hS_def
      have hSfin : S.Finite := by
        refine Finite.of_finite_image (f := fun X ↦ X \ I) (hfin.finite_subsets.subset ?_) ?_
        · simp only [hS_def, image_subset_iff, preimage_setOf_eq, setOf_subset_setOf,
            forall_exists_index]
          exact fun J hIJ ↦ diff_subset_diff_left hIJ.2.2
        rintro A ⟨hIA, -, -⟩ B ⟨hIB, -, -⟩ (hAB : A \ I = B \ I)
        rw [← diff_union_of_subset hIA, hAB, diff_union_of_subset hIB]

      obtain ⟨J, hIJ : I ⊆ J, hJ⟩ := hSfin.exists_le_maximal (a := I) ⟨rfl.subset, hI, hIX⟩
      exact ⟨J, hIJ, maximal_right_of_forall_ge (fun x y hx hxy ↦ hx.trans hxy) hJ⟩
    simp only
    have aux : ∀ B, Base B → B ⊆ X → Maximal (fun K ↦ (∃ B', Base B' ∧ K ⊆ B') ∧ K ⊆ X) B := by
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

lemma uniformMatroidOfBase_uniform (E : Set α) (Base : Set α → Prop)
    {exists_base} {antichain} {exchange} {contain} {subset_ground} :
    (UniformMatroidOfBase E Base exists_base antichain exchange contain subset_ground).Uniform := by
  simp only [Uniform, UniformMatroidOfBase_Base, UniformMatroidOfBase_E, mem_diff, and_imp]
  exact fun B e f hB heE he hf ↦ exchange hB hf ⟨heE, he⟩

lemma Base.finDiff_of_finite_diff (hB : M.Base B) (hB' : M.Base B') (hBB' : (B \ B').Finite) :
    FinDiff B B' := by
  rw [finDiff_iff, and_iff_right hBB', hB.encard_diff_comm hB']


/-- Given a uniform matroid `M`, and a subset `Bs` of the bases of `M` that is closed under
exchanges, we can make a new uniform matroid by turning all the sets in `Bs` into circuits.
If `M` or its dual has finite rank, then `Bs` is necessarily the set of all bases of `M`,
and this is just truncation. But if `M` and `M✶` both have infinite rank, this gives
a quotient of `M` that is not just a truncation.
-/
@[simps! E Base] def Uniform.LocalTruncate (hM : M.Uniform) (hr : M.RkPos) (Bs : Set (Set α))
    (hBs_base : ∀ ⦃B⦄, B ∈ Bs → M.Base B)
    (hBs_finDiff : ∀ ⦃B B'⦄, B ∈ Bs → FinDiff B B' → B' ⊆ M.E → B' ∈ Bs) : Matroid α :=
  UniformMatroidOfBase M.E (fun B ↦ (M.Base B ∧ B ∉ Bs) ∨ (∃ e ∉ B, insert e B ∈ Bs))
  (by
    obtain ⟨B, hB⟩ := M.exists_base
    obtain ⟨e, he⟩ := hB.nonempty
    by_cases hBb : B ∈ Bs
    · exact ⟨B \ {e}, .inr ⟨e, by simpa [he]⟩⟩
    exact ⟨B, .inl ⟨hB, hBb⟩⟩)

  (by
    rintro B (hB | ⟨e, h₁, h₁'⟩) B' (hB' | ⟨e', h₂, h₂'⟩) hne hss
    · exact hne <| hB.1.eq_of_subset_base hB'.1 hss
    · rw [hB.1.eq_of_subset_base (hBs_base h₂') (hss.trans (subset_insert _ _))] at hB
      exact hB.2 h₂'
    · refine hB'.2 (hBs_finDiff h₁' ?_ hB'.1.subset_ground)
      refine ((hBs_base h₁').finDiff_of_finite_diff hB'.1 ((finite_singleton e).subset ?_))
      rw [diff_subset_iff, union_singleton]
      exact insert_subset_insert hss
    have he'B : e' ∉ B := not_mem_subset hss h₂
    have he'E : e' ∈ M.E := (hBs_base h₂').subset_ground (mem_insert _ _)
    have hBE : B ⊆ M.E := (subset_insert _ _).trans (hBs_base h₁').subset_ground
    have he'Bb := hBs_finDiff h₁' (finDiff_insert_insert h₁ he'B) (insert_subset he'E hBE)
    have hins := (hBs_base he'Bb).eq_of_subset_base (hBs_base h₂') (insert_subset_insert hss)
    apply_fun (fun X ↦ X \ {e'}) at hins
    obtain rfl : B = B' := by simpa [he'B, h₂] using hins
    contradiction)

  (by
    simp only [mem_insert_iff, mem_diff, mem_singleton_iff, not_or, not_and, not_not]
    rintro B e f (⟨hB, hBb⟩ | ⟨g, hgB, hgBb⟩) heB hfB
    · refine .inl ⟨hM hB hfB heB, fun hexch ↦ hBb <| hBs_finDiff hexch (FinDiff.symm ?_)
        hB.subset_ground⟩
      exact finDiff_exchange heB hfB.2

    refine .inr ⟨e, ?_⟩
    rw [insert_comm]
    simp only [heB, imp_self, and_true, insert_diff_singleton, insert_eq_of_mem]
    refine ⟨by rintro rfl; exact hfB.2 heB, ?_⟩
    refine hBs_finDiff hgBb (finDiff_insert_insert hgB hfB.2) (insert_subset hfB.1 ?_)
    exact (subset_insert _ _).trans (hBs_base hgBb).subset_ground )

  (by
    simp only
    rintro I X hIX hXE hinf

    by_cases hIb : I ∈ Bs
    · obtain ⟨e, he⟩ := (hBs_base hIb).nonempty
      exact ⟨I \ {e}, .inr ⟨e, by simp, by simpa [he]⟩, .inl diff_subset⟩
    obtain rfl | hssu := hIX.eq_or_ssubset
    · simp at hinf

    by_cases hXb : X ∈ Bs
    · obtain ⟨e, he⟩ := exists_of_ssubset hssu
      exact ⟨X \ {e}, .inr ⟨e, by simp, by simpa [he]⟩,
        .inr <| .inl ⟨subset_diff_singleton hssu.subset he.2, diff_subset⟩⟩

    obtain (hIi | hIs) := hM.indep_or_spanning (hIX.trans hXE)
    · obtain (hXi | hXs) := hM.indep_or_spanning hXE
      · obtain ⟨B, hB, hXB⟩ := hXi.exists_base_superset
        by_cases hBb : B ∈ Bs
        · obtain ⟨f, hf⟩ := exists_of_ssubset (hXB.ssubset_of_ne <| by rintro rfl; contradiction)
          exact ⟨B \ {f}, .inr ⟨f, by simpa [insert_eq_of_mem hf.1]⟩,
            .inr (.inr (subset_diff_singleton hXB hf.2))⟩
        exact ⟨B, .inl ⟨hB, hBb⟩, .inr (.inr hXB)⟩
      obtain ⟨B', hB'⟩ := hXs.exists_base_subset
      obtain ⟨B, hB, hIB, hBX⟩ := hIi.exists_base_subset_union_base hB'.1
      replace hBX := hBX.trans (union_subset hIX hB'.2)
      by_cases hBb : B ∈ Bs
      · obtain ⟨e, he⟩ := exists_of_ssubset (hIB.ssubset_of_ne <| by rintro rfl; contradiction)
        refine ⟨B \ {e}, .inr ⟨e, by simpa [he.1]⟩, .inr (.inl ?_)⟩
        exact ⟨subset_diff_singleton hIB he.2, diff_subset.trans hBX⟩
      exact ⟨B, .inl ⟨hB, hBb⟩, .inr (.inl ⟨hIB, hBX⟩)⟩
    obtain ⟨B, hB⟩ := hIs.exists_base_subset
    by_cases hBb : B ∈ Bs
    · obtain ⟨e, he⟩ := hB.1.nonempty
      exact ⟨B \ {e}, .inr ⟨e, by simpa [he]⟩, .inl <| diff_subset.trans hB.2⟩
    exact ⟨B, .inl ⟨hB.1, hBb⟩, .inl hB.2⟩)
  (by
    rintro B (hB | ⟨e, hB⟩)
    · exact hB.1.subset_ground
    exact (subset_insert _ _).trans (hBs_base hB.2).subset_ground)

@[simp] lemma localTruncate_indep_iff {hM : M.Uniform} {hr} {Bs} {hBs_base} {hBs_finDiff} :
    (hM.LocalTruncate hr Bs hBs_base hBs_finDiff).Indep I ↔ M.Indep I ∧ I ∉ Bs := by
  refine ⟨?_, fun ⟨hI, hIBs⟩ ↦ ?_⟩
  · rintro ⟨B, ⟨hB, hBb⟩ | ⟨e, heB, heBb⟩, hIB⟩
    · refine ⟨hB.indep.subset hIB, fun hIb ↦ hBb ?_⟩
      rwa [← (hBs_base hIb).eq_of_subset_base hB hIB]
    refine ⟨(hBs_base heBb).indep.subset (hIB.trans (subset_insert _ _)), fun hIb ↦ heB ?_⟩
    obtain rfl : I = insert e B :=
      (hBs_base hIb).eq_of_subset_base (hBs_base heBb) (hIB.trans (subset_insert _ _))
    exact hIB <| .inl rfl
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  by_cases hBb : B ∈ Bs
  · obtain ⟨e, he⟩ := exists_of_ssubset (hIB.ssubset_of_ne <| by rintro rfl; contradiction)
    exact ⟨B \ {e}, .inr ⟨e, by simpa [he.1]⟩, subset_diff_singleton hIB he.2⟩
  exact ⟨B, .inl ⟨hB, hBb⟩, hIB⟩

/-- This can be tidied up. -/
lemma LocalTruncate.closure_eq_of_not_mem (hM : M.Uniform) (hr) (Bs) (hBs_base) (hBs_finDiff)
    (hXE : X ⊆ M.E) (hX : ∀ e ∈ M.E \ X, insert e X ∉ Bs) :
    (hM.LocalTruncate hr Bs hBs_base hBs_finDiff).closure X = M.closure X := by
  set M' := (hM.LocalTruncate hr Bs hBs_base hBs_finDiff) with hM'_def
  obtain rfl | hssu := hXE.eq_or_ssubset
  · rw [show M.E = M'.E from rfl, closure_ground, show M'.E = M.E from rfl, closure_ground]
  by_cases hXs : M.Spanning X
  · rw [hXs.closure_eq, show M.E = M'.E from rfl, ← spanning_iff_closure_eq,
      spanning_iff_exists_base_subset', and_iff_left (show X ⊆ M'.E from hXE)]
    simp only [hM'_def, Uniform.LocalTruncate_Base]

    obtain ⟨B, hB, hBX⟩ := hXs.exists_base_subset
    by_cases hBs : B ∈ Bs
    · obtain ⟨e, he⟩ := hB.nonempty
      exact ⟨B \ {e}, .inr ⟨e, by simpa [he]⟩, diff_subset.trans hBX⟩
    exact ⟨B, .inl ⟨hB, hBs⟩, hBX⟩

  obtain ⟨I, hI'⟩ := M'.exists_basis X
  have hi := hI'.indep
  simp only [hM'_def, localTruncate_indep_iff] at hi
  have hI : M.Basis I X
  · rw [hi.1.basis_iff_forall_insert_dep hI'.subset]
    intro e he
    rw [Dep, and_iff_left (insert_subset (hXE he.1) hi.1.subset_ground)]
    intro hi
    have hni := (hI'.insert_dep he).not_indep
    simp only [localTruncate_indep_iff, hi, true_and, not_not, hM'_def] at hni
    exact hXs <| (hBs_base hni).spanning.superset (insert_subset he.1 hI'.subset)
  rw [← hI'.closure_eq_closure, ← hI.closure_eq_closure, Set.ext_iff]
  simp only [hM'_def, hI'.indep.mem_closure_iff', Uniform.LocalTruncate_E, localTruncate_indep_iff,
    and_imp, hI.indep.mem_closure_iff', and_congr_right_iff]

  refine fun e heE ↦ ⟨fun heI heIBs ↦ ?_, fun h1 h2 h3 ↦ h1 h2⟩
  by_contra heI'

  refine heI' <| heI heIBs fun hins ↦ ?_
  obtain rfl | hssu := hI.subset.eq_or_ssubset
  · exact hX e ⟨heE, heI'⟩ hins

  obtain ⟨f, hf⟩ := exists_of_ssubset hssu

  have hins' := hBs_finDiff hins (B' := insert f I) (finDiff_insert_insert heI' hf.2)
    (insert_subset (hXE hf.1) hi.1.subset_ground)
  exact hXs <| (hBs_base hins').spanning.superset (insert_subset hf.1 hssu.subset)

lemma LocalTruncate.closure_eq_of_mem (hM : M.Uniform) (hr) (Bs) (hBs_base) (hBs_finDiff)
    {X : Set α} (hXB : X ∈ Bs) (heX : e ∈ X) :
    (hM.LocalTruncate hr Bs hBs_base hBs_finDiff).closure (X \ {e}) = M.E := by
  rw [show M.E = (hM.LocalTruncate hr Bs hBs_base hBs_finDiff).E from rfl,
    ← spanning_iff_closure_eq _, spanning_iff_exists_base_subset']
  simp only [Uniform.LocalTruncate_Base, Uniform.LocalTruncate_E]
  refine ⟨⟨X \ {e}, .inr ⟨e, by simpa [heX]⟩, rfl.subset⟩, ?_⟩
  · exact diff_subset.trans (hBs_base hXB).subset_ground
  exact diff_subset.trans (hBs_base hXB).subset_ground

lemma LocalTruncate.closure_subset_closure (hM : M.Uniform) (hr) (Bs) (hBs_base) (hBs_finDiff)
    (X : Set α) (hXE : X ⊆ M.E) :
    M.closure X ⊆ (hM.LocalTruncate hr Bs hBs_base hBs_finDiff).closure X := by
  by_cases hX : ∃ e ∈ M.E \ X, insert e X ∈ Bs
  · obtain ⟨e, he, heX⟩ := hX
    have hcl := LocalTruncate.closure_eq_of_mem hM hr Bs hBs_base hBs_finDiff heX (mem_insert _ _)
    simp only [mem_singleton_iff, insert_diff_of_mem, diff_singleton_eq_self he.2] at hcl
    rw [hcl]
    exact M.closure_subset_ground X
  push_neg at hX
  rwa [LocalTruncate.closure_eq_of_not_mem _ _ _ _ _ hXE]

end Infinite

/-
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

@[simp] theorem isIso_line_iff {n : ℕ} : M ≂ unif 2 n ↔ M.Simple ∧ M.erk ≤ 2 ∧ M.E.encard = n := by
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
-/
