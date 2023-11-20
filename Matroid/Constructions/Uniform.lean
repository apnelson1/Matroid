import Matroid.Minor.Iso
import Matroid.Constructions.Truncate
import Mathlib.Tactic.Linarith

variable {α : Type*} {M : Matroid α} {E : Set α}

namespace Matroid

open Set

section Uniform

/-- A uniform matroid with a given rank `k` and ground set `E`. If `k = ⊤`, then every set is
  independent. ` -/
def unifOn (E : Set α) (k : ℕ∞) : Matroid α := (freeOn E).truncate k

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
  rw [←er_inter_ground_eq, unifOn_er_eq _ _ (by rw [unifOn_ground_eq]; apply inter_subset_right),
    unifOn_ground_eq]

instance {k : ℕ} {E : Set α} : FiniteRk (unifOn E k) := by
  rw [←rFin_ground_iff_finiteRk, rFin, unifOn_er_eq _ _ (by simp [rfl.subset])]
  exact (min_le_right _ _).trans_lt (WithTop.coe_lt_top _)

@[simp] theorem unifOn_spanning_iff' {k : ℕ∞} (hk : k ≠ ⊤) :
    (unifOn E k).Spanning X ↔ (k ≤ X.encard ∧ X ⊆ E) ∨ X = E  := by
  lift k to ℕ using hk
  rw [spanning_iff_er', erk_eq_er_ground, unifOn_ground_eq, unifOn_er_eq', unifOn_er_eq',
    le_min_iff, min_le_iff, min_le_iff, iff_true_intro (le_refl _), or_true, and_true, inter_self]
  refine' ⟨fun ⟨h, hXE⟩ ↦ h.elim (fun h ↦ _) (fun h ↦ Or.inl ⟨_,hXE⟩),
    fun h ↦ h.elim (fun ⟨hle, hXE⟩ ↦ ⟨Or.inr (by rwa [inter_eq_self_of_subset_left hXE]), hXE⟩ ) _⟩
  · refine' X.finite_or_infinite.elim (fun hfin ↦ Or.inr _) (fun hinf ↦ Or.inl ⟨_, hXE⟩)
    · rw [←(hfin.inter_of_left E).eq_of_subset_of_encard_le' (inter_subset_right _ _) h,
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
    ←WithTop.add_right_cancel_iff (hE.subset hBE).encard_lt_top.ne,
    encard_diff_add_encard_of_subset hBE, Iff.comm, eq_comm, add_comm,
    ←WithTop.add_right_cancel_iff (hlt.trans_le le_top).ne, tsub_add_cancel_of_le hlt.le]

@[simp] theorem unifOn_delete_eq (E D : Set α) (k : ℕ∞) :
    (unifOn E k) ⟍ D = unifOn (E \ D) k := by
  simp_rw [eq_unifOn_iff, delete_ground, unifOn_ground_eq, true_and, delete_indep_iff,
    unifOn_indep_iff, subset_diff, and_assoc, imp_true_iff]

theorem unifOn_contract_eq' (E C : Set α) {k : ℕ∞} (hk : k ≠ ⊤):
    (unifOn E k) ⟋ C = unifOn (E \ C) (k - (E ∩ C).encard) := by
  lift k to ℕ using hk
  refine' eq_of_spanning_iff_spanning_forall (by simp) (fun S hS ↦ _)
  simp only [ge_iff_le, contract_ground, unifOn_ground_eq, diff_self_inter, subset_diff] at hS
  rw [←contract_inter_ground_eq, unifOn_ground_eq, inter_comm,
    contract_spanning_iff, unifOn_spanning_iff', unifOn_spanning_iff', tsub_le_iff_right,
    iff_true_intro (disjoint_of_subset_right (inter_subset_right _ _) hS.2), and_true,
     ←encard_union_eq (disjoint_of_subset_right (inter_subset_right _ _) hS.2), union_subset_iff,
    and_iff_left (inter_subset_left _ _), and_iff_left hS.1, subset_diff, union_distrib_left,
    and_iff_left hS, union_eq_self_of_subset_left hS.1, inter_eq_left,
    subset_antisymm_iff, subset_diff, and_iff_right hS, diff_subset_iff, union_comm C]
  · exact ((tsub_le_self).trans_lt (WithTop.coe_lt_top k)).ne
  exact WithTop.coe_ne_top

@[simp] theorem unifOn_contract_eq {k : ℕ} :
    (unifOn E k) ⟋ C = unifOn (E \ C) (k - (E ∩ C).encard) :=
  unifOn_contract_eq' E C WithTop.coe_ne_top

section unif

variable {a b a' b' : ℕ}

/-- A canonical uniform matroid, with rank `a` and ground type `Fin b`. -/
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

theorem unif_base_iff (hab : a ≤ b) : (unif a b).Base B ↔ B.encard = a := by
  rw [unif, unifOn, truncate_base_iff, freeOn_indep_iff, and_iff_right (subset_univ _)]
  rwa [freeOn_erk_eq, encard_univ, PartENat.card_eq_coe_fintype_card, Fintype.card_fin,
    PartENat.withTopEquiv_natCast, Nat.cast_le]

@[simp] theorem unif_base_iff' : (unif a (a + b)).Base B ↔ B.encard = a := by
  rw [unif_base_iff (Nat.le_add_right _ _)]

theorem unif_dual' (h : a + b = n) : (unif a n)﹡ = unif b n := by
  subst h
  refine eq_of_base_iff_base_forall rfl (fun B _ ↦ ?_)
  rw [dual_base_iff, unif_ground_eq, unif_base_iff (Nat.le_add_right _ _),
    unif_base_iff (Nat.le_add_left _ _),
    ←WithTop.add_right_cancel_iff (encard_ne_top_iff.2 B.toFinite),
    encard_diff_add_encard_of_subset (subset_univ _), Iff.comm,
    ←WithTop.add_left_cancel_iff (WithTop.coe_ne_top (a := a)), eq_comm]
  convert Iff.rfl
  rw [encard_univ, PartENat.card_eq_coe_fintype_card, Fintype.card_fin,
    PartENat.withTopEquiv_natCast, ENat.some_eq_coe, eq_comm, Nat.cast_add]

theorem unif_eq_freeOn (h : b ≤ a) : unif a b = freeOn (univ : Set (Fin b)) := by
  apply eq_of_indep_iff_indep_forall (by simp)
  simp only [unif_ground_eq, subset_univ, unif_indep_iff, freeOn_indep_iff, iff_true,
    forall_true_left]
  intro I
  rw [I.toFinite.encard_eq_coe_toFinset_card, Nat.cast_le]
  refine le_trans ?_ h
  exact card_finset_fin_le (Finite.toFinset (toFinite I))

@[simp] theorem unif_eq_loopyOn (b : ℕ) : unif 0 b = loopyOn (univ : Set (Fin b)) := by
  simp [unif]

/-- The dual of a uniform matroid. This is true even if the subtraction truncates. -/
@[simp] theorem unif_dual (a b : ℕ): (unif a b)﹡ = unif (b - a) b := by
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
  refine (iso_of_forall_indep' hf.toLocalEquiv rfl (by simp) fun I hIE ↦ ?_).isIso
  simp [hi, hIE, (hf.injOn.mono hIE).encard_image]

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

end unif

end Uniform

-- /-- Horrible proof. Should be improved using `simple` api -/
-- theorem iso_line_iff {k : ℕ} (hk : 2 ≤ k) :
--   nonempty (M ≃i (unif 2 k)) ↔
--     (∀ e f ∈ M.E, M.indep {e,f}) ∧ M.rk = 2 ∧ M.E.finite ∧ M.E.ncard = k :=
-- begin
--   simp_rw [iso_unif_iff, encard_eq_coe_iff, ← and_assoc, and.congr_left_iff,
--     set.eq_unifOn_iff, and_iff_right rfl, nat.cast_bit0, enat.coe_one],
--   rintro rfl hfin,
--   have lem : ∀ x y, ({x,y} : Set α).encard ≤ 2,
--   { intros x y,
--     rw [(({x,y} : Set α).to_finite.encard_eq), ←nat.cast_two, nat.cast_le],
--     exact (ncard_insert_le _ _).trans (by simp) },
--   haveI : M.finite := ⟨hfin⟩,
--   refine ⟨λ h, ⟨λ e he f hf, (h _).mpr ⟨lem _ _,_⟩,_⟩, λ h I, _⟩,

--   { rintro x ((rfl : x = e)| (rfl : x = f)); assumption  },
--   { rw [rk],
--     rw [←one_add_one_eq_two, nat.add_one_le_iff, one_lt_ncard_iff hfin] at hk,
--     obtain ⟨a, b, ha, hb, hne⟩ := hk,
--     have hss : {a,b} ⊆ M.E, by {rintro x ((rfl : x = a) | (rfl : x = b)); assumption},
--     have hlb := M.r_mono hss,
--     rw [indep.r ((h _).mpr ⟨_, hss⟩), ncard_pair hne] at hlb,
--     { refine hlb.antisymm' _,
--       obtain ⟨B, hB⟩ := M.exists_base,
--       rw [←rk, ←hB.card],
--       have h' := ((h B).mp hB.indep).1,
--       rw [←nat.cast_two, encard_le_coe_iff] at h',
--       exact h'.2 },
--     apply lem },
--   rw [←nat.cast_two, encard_le_coe_iff],
--   refine ⟨λ h', ⟨⟨h'.finite, _⟩, h'.subset_ground⟩, _⟩,
--   { rw [←h'.r, ←h.2], exact r_le_rk _ _ },
--   rintro ⟨⟨hfin, hcard⟩, hss⟩,
--   rw [le_iff_eq_or_lt, nat.lt_iff_add_one_le, ncard_eq_two, ←one_add_one_eq_two,
--     nat.add_le_add_iff_right, ncard_le_one_iff_eq hfin] at hcard,
--   obtain (⟨x,y,-, rfl⟩ | rfl | ⟨e, rfl⟩ ) := hcard,
--   { exact h.1 _ (hss (by simp)) _ (hss (by simp)) },
--   { simp },
--   convert h.1 e (hss (by simp)) e (hss (by simp)),
--   simp,
-- end
