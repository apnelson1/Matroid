import Matroid.Uniform.Basic


namespace Matroid

open Set Set.Notation


variable {α : Type*} {M : Matroid α} {E I B X Y C : Set α} {k : ℕ} {e f : α} {a b n : ℕ}

/-- `M.IsFiniteRankUniform a` means that `M` is a uniform matroid of rank `a ∈ ℕ`. -/
@[mk_iff]
structure IsFiniteRankUniform (M : Matroid α) (a : ℕ) : Prop where
  eRank_eq : M.eRank = a
  isUniform : M.IsUniform

lemma IsFiniteRankUniform.le (h : M.IsFiniteRankUniform a) : a ≤ M.E.encard := by
  grw [← h.eRank_eq, M.eRank_le_encard_ground]

lemma IsFiniteRankUniform.rankFinite (h : M.IsFiniteRankUniform a) : M.RankFinite := by
  simp [← eRank_ne_top_iff, h.eRank_eq]

lemma IsFiniteRankUniform.eq_unifOn (h : M.IsFiniteRankUniform a) : M = unifOn M.E a := by
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

lemma IsFiniteRankUniform.exists_eq_unifOn (h : M.IsFiniteRankUniform a) :
    ∃ E, M = unifOn E a ∧ a ≤ E.encard :=
  ⟨M.E, h.eq_unifOn, by grw [← h.eRank_eq, ← M.eRank_le_encard_ground]⟩

lemma unifOn_isFiniteRankUniform (haE : a ≤ E.encard) : (unifOn E a).IsFiniteRankUniform a :=
  ⟨unifOn_eRank_eq' haE, by simp⟩

lemma isFiniteRankUniform_iff_eq_unifOn :
    M.IsFiniteRankUniform a ↔ M = unifOn M.E a ∧ a ≤ M.E.encard := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨E, rfl, haE⟩ := h.exists_eq_unifOn
    simpa
  rw [h.1]
  exact unifOn_isFiniteRankUniform h.2

lemma IsFiniteRankUniform.indep_iff (hM : M.IsFiniteRankUniform a) :
    M.Indep I ↔ I.encard ≤ a ∧ I ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  simp

lemma isFiniteRankUniform_iff_forall_indep_iff :
    M.IsFiniteRankUniform a ↔ a ≤ M.E.encard ∧ ∀ I ⊆ M.E, M.Indep I ↔ I.encard ≤ a := by
  refine ⟨fun h ↦ ⟨?_, fun I hIE ↦ ?_⟩, fun h ↦ ?_⟩
  · grw [← h.eRank_eq, eRank_le_encard_ground]
  · rw [h.indep_iff, and_iff_left hIE]
  rw [isFiniteRankUniform_iff_eq_unifOn, and_iff_left h.1, ext_iff_indep, and_iff_right (by simp)]
  simp +contextual [h.2]

lemma IsFiniteRankUniform.isCircuit_iff (hM : M.IsFiniteRankUniform a) :
    M.IsCircuit C ↔ C.encard = a + 1 ∧ C ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  rw [unifOn_isCircuit_iff, unifOn_ground_eq]

lemma IsFiniteRankUniform.dep_iff (hM : M.IsFiniteRankUniform a) :
    M.Dep X ↔ a < X.encard ∧ X ⊆ M.E := by
  grind [Dep, hM.indep_iff]

lemma IsFiniteRankUniform.isBase_iff (hM : M.IsFiniteRankUniform a) :
    M.IsBase B ↔ B.encard = a ∧ B ⊆ M.E := by
  by_cases hBE : B ⊆ M.E
  · obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
    rw [unifOn_isBase_iff _ (by simpa), and_iff_left hBE]
    assumption
  exact iff_of_false (fun h ↦ hBE h.subset_ground) <| by simp [hBE]

lemma IsFiniteRankUniform.isCocircuit_iff (hM : M.IsFiniteRankUniform a) :
    M.IsCocircuit C ↔ (M.E \ C).encard + 1 = a ∧ C ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  rwa [unifOn_ground_eq, unifOn_isCocircuit_iff]

lemma IsFiniteRankUniform.spanning_iff (hM : M.IsFiniteRankUniform a) :
    M.Spanning X ↔ a ≤ X.encard ∧ X ⊆ M.E := by
  obtain ⟨E, rfl, hle⟩ := hM.exists_eq_unifOn
  by_cases! hXE : ¬ X ⊆ E; grind
  rw [unifOn_spanning_iff hle hXE, unifOn_ground_eq, and_iff_left hXE]

lemma IsFiniteRankUniform.restrict (hM : M.IsFiniteRankUniform a) {R : Set α} (hRX : R ⊆ M.E)
    (haR : a ≤ R.encard) : (M ↾ R).IsFiniteRankUniform a := by
  refine ⟨?_, hM.isUniform.minor (restrict_isMinor _ hRX)⟩
  rw [eRank_restrict, hM.eq_unifOn, unifOn_eRk_eq _ _ hRX, min_eq_right haR]

lemma IsFiniteRankUniform.map (hM : M.IsFiniteRankUniform a) {β : Type*} {f : α → β}
    (hf : InjOn f M.E) : (M.map f hf).IsFiniteRankUniform a :=
  ⟨by simpa using hM.eRank_eq, hM.isUniform.map hf⟩

/-- A uniform matroid whose rank is finite is one of the obvious ones. -/
lemma IsUniform.isFiniteRankUniform [M.RankFinite] (hM : M.IsUniform) :
    ∃ a, M.IsFiniteRankUniform a :=
  ⟨M.rank, M.cast_rank_eq.symm, hM⟩

/-- A finitary non-free uniform matroid is a finite-rank uniform matroid. -/
lemma IsUniform.isFiniteRankUniform_of_finitary [M.Finitary] [M✶.RankPos] (hM : M.IsUniform) :
    ∃ a, M.IsFiniteRankUniform a := by
  suffices M.RankFinite from hM.isFiniteRankUniform
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  grw [← eRank_ne_top_iff, ← (hM.spanning_of_dep hC.dep).eRk_eq, ← lt_top_iff_ne_top,
    eRk_le_encard, encard_lt_top_iff]
  exact hC.finite

lemma IsUniform.eq_freeOn_or_isFiniteRankUniform [M.Finitary] (hM : M.IsUniform) :
    ∃ (E : Set α), M = freeOn E ∨ ∃ a, M.IsFiniteRankUniform a := by
  obtain ⟨E, rfl⟩ | hr := M.exists_eq_freeOn_or_rankPos_dual
  · exact ⟨E, .inl rfl⟩
  simp [hM.isFiniteRankUniform_of_finitary]

@[simp]
lemma isFiniteRankUniform_zero_iff : M.IsFiniteRankUniform 0 ↔ M.eRank = 0 := by
  refine ⟨fun h ↦ h.eRank_eq, fun h ↦ ⟨h, ?_⟩⟩
  rw [eRank_eq_zero_iff.1 h]
  simp

lemma IsFiniteRankUniform.of_iso (hM : M.IsFiniteRankUniform a) {β : Type*} {N : Matroid β}
    (e : M ≂ N) : N.IsFiniteRankUniform a :=
  ⟨by rw [← e.eRank_eq, hM.eRank_eq], hM.isUniform.of_iso e⟩

lemma Iso.isFiniteRankUniform_iff {β : Type*} {N : Matroid β} (e : M ≂ N) :
    M.IsFiniteRankUniform a ↔ N.IsFiniteRankUniform a :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

theorem nonempty_iso_unifOn_iff {β : Type*} {X : Set β} {a : ℕ} (haX : a ≤ X.encard) :
    Nonempty (M ≂ (unifOn X a)) ↔ M.IsFiniteRankUniform a ∧ Nonempty (X ≃ M.E) := by
  refine ⟨fun ⟨i⟩ ↦ ⟨⟨unifOn_eRank_eq' haX ▸ i.eRank_eq, ?_⟩, ⟨i.1.symm⟩⟩, fun ⟨h, ⟨i⟩⟩ ↦ ?_⟩
  · obtain rfl | hne := X.eq_empty_or_nonempty
    · obtain rfl : M = emptyOn α := by simpa [ground_eq_empty_iff] using i.1.encard_eq
      simp [isUniform_iff_forall_spanning_of_isCircuit]
    have aux : (unifOn X a).Nonempty := by rwa [← ground_nonempty_iff, unifOn_ground_eq]
    obtain ⟨f, hf, h⟩ := i.symm.exists_eq_map'
    rw [h]
    exact (isUniform_unifOn ..).map ..
  refine ⟨i.symm, fun I ↦ ?_⟩
  simp only [h.indep_iff, Subtype.val_injective.encard_image, image_subset_iff,
    Subtype.coe_preimage_self, subset_univ, and_true, unifOn_ground_eq, unifOn_indep_iff]
  rw [Function.Injective.encard_image (fun x ↦ by simp)]

/-- The restriction of `M` to `X` is a rank-`a` uniform matroid -/
@[mk_iff]
structure IsFiniteRankUniformOn (M : Matroid α) (a : ℕ) (X : Set α) : Prop where
  isFiniteRankUniform : (M ↾ X).IsFiniteRankUniform a
  subset_ground : X ⊆ M.E

attribute [grind →] IsFiniteRankUniformOn.subset_ground

lemma IsFiniteRankUniformOn.eRk (h : M.IsFiniteRankUniformOn a X) : M.eRk X = a := by
  rw [← M.eRank_restrict, h.isFiniteRankUniform.eRank_eq]

lemma IsFiniteRankUniform.isFiniteRankUniformOn_of_restrict'
    (h : (M ↾ X).IsFiniteRankUniform a) (ha : a ≠ 0) : M.IsFiniteRankUniformOn a X := by
  refine ⟨h, fun e heX ↦ (Indep.subset_ground ?_ (mem_singleton ..))⟩
  rw [isFiniteRankUniform_iff_forall_indep_iff] at h
  replace h := h.2 {e} (by simpa)
  rw [restrict_indep_iff, and_iff_left (by simpa), encard_singleton, ← Nat.cast_one,
    ENat.coe_le_coe] at h
  exact h.2 <| by lia

@[simp]
lemma isFiniteRankUniformOn_zero_iff : M.IsFiniteRankUniformOn 0 X ↔ X ⊆ M.loops := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · exact (eRk_eq_zero_iff h.subset_ground).1 h.isFiniteRankUniform.eRank_eq
  · grw [isFiniteRankUniform_zero_iff, eRank_restrict, eRk_eq_zero_iff', inter_subset_left, h]
  grw [← loops_subset_ground, h]

lemma IsFiniteRankUniform.isFiniteRankUniformOn_of_restrict (h : (M ↾ X).IsFiniteRankUniform a)
    (hXE : X ⊆ M.E := by aesop_mat) : M.IsFiniteRankUniformOn a X := by
  obtain rfl | hne := eq_or_ne a 0
  · simp only [isFiniteRankUniform_zero_iff, eRank_restrict] at h
    rwa [isFiniteRankUniformOn_zero_iff, ← eRk_eq_zero_iff]
  exact h.isFiniteRankUniformOn_of_restrict' hne

lemma isFiniteRankUniformOn_iff_indep (ha : a ≠ 0) :
    M.IsFiniteRankUniformOn a X ↔ a ≤ X.encard ∧ ∀ I ⊆ X, M.Indep I ↔ I.encard ≤ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, fun e heX ↦ (Indep.subset_ground ?_ (mem_singleton ..))⟩⟩
  · simpa +contextual using isFiniteRankUniform_iff_forall_indep_iff.1 h.isFiniteRankUniform
  · simpa +contextual [isFiniteRankUniform_iff_forall_indep_iff]
  simp only [h.2 {e} (by simpa), encard_singleton, Nat.one_le_cast]
  lia

lemma IsFiniteRankUniformOn.subset (h : M.IsFiniteRankUniformOn a X) (hYX : Y ⊆ X)
    (hY : a ≤ Y.encard) : M.IsFiniteRankUniformOn a Y := by
  obtain rfl | hne := eq_or_ne a 0
  · grind [isFiniteRankUniformOn_zero_iff]
  grind [isFiniteRankUniformOn_iff_indep hne]

lemma isFiniteRankUniform_restrict_iff :
    (M ↾ X).IsFiniteRankUniform a ↔ a ≤ X.encard ∧ ∀ I ⊆ X, M.Indep I ↔ I.encard ≤ a := by
  simp only [isFiniteRankUniform_iff_forall_indep_iff, restrict_ground_eq, restrict_indep_iff]
  grind

lemma IsFiniteRankUniform.restrict_insert_iff (h : (M ↾ X).IsFiniteRankUniform (a + 1))
    (heX : e ∉ X) (he : e ∈ M.closure X) :
    (M ↾ (insert e X)).IsFiniteRankUniform (a + 1) ↔ ∀ I ⊆ X, I.encard = a → e ∉ M.closure I := by
  have hX : M.eRk X = a + 1 := by simpa using h.eRank_eq
  simp only [isFiniteRankUniform_restrict_iff, encard_insert_of_notMem heX] at ⊢ h
  refine ⟨fun ⟨hcard, hI⟩ ↦ fun I hIX hIcard hIcl ↦ ?_, fun h' ↦ ⟨?_, fun I hIeX ↦ ?_⟩⟩
  · rw [Indep.mem_closure_iff_of_notMem _ (by grind)] at hIcl
    · refine (hI (insert e I) (by grind)).not.1 hIcl.not_indep ?_
      grw [encard_insert_le, hIcard, Nat.cast_add_one]
    grw [h.2 _ hIX, hIcard, ← le_self_add]
  · grw [h.1, ← le_self_add]
  by_cases! heI : e ∉ I
  · rw [h.2 _ (by grind)]
  replace h'' : ∀ J ⊆ X, J.encard ≤ a → e ∉ M.closure J := by
    refine fun J hJX hJ ↦ ?_
    obtain ⟨K, hJK, hKX, hK⟩ := exists_superset_subset_encard_eq hJX hJ
      (by grw [← h.1, Nat.cast_add_one, ← le_self_add])
    refine notMem_subset (M.closure_subset_closure hJK) <| h' _ hKX hK
  obtain hle | hgt := le_or_gt I.encard (a + 1)
  · refine iff_of_true ?_ hle
    rw [← insert_diff_self_of_mem heI, Indep.insert_indep_iff_of_notMem _ (by simp), mem_diff,
      and_iff_right (M.mem_ground_of_mem_closure he)]
    · refine h'' _ (by grind) ?_
      grw [← ENat.add_one_le_add_one_iff, ← hle, encard_diff_singleton_add_one heI]
    grw [h.2 _ (by grind), Nat.cast_add_one, ← hle, diff_subset]
  refine iff_of_false (fun hI ↦ ?_) hgt.not_ge
  replace hI := hI.encard_le_eRk_of_subset hIeX
  grw [← eRk_insert_closure_eq, insert_eq_of_mem he, eRk_closure_eq, hX] at hI
  exact hI.not_gt hgt

lemma IsFiniteRankUniform.contract (h : M.IsFiniteRankUniform a) (hC : C ⊆ M.E)
    (hab : a = b + C.encard) : (M ／ C).IsFiniteRankUniform b := by
  have hCi : M.Indep C := by
    grw [h.indep_iff, and_iff_left hC, hab, ← le_add_self]
  have hr : M.eRk C ≠ ⊤ := by rw [hCi.eRk_eq_encard]; enat_to_nat!
  rw [isFiniteRankUniform_iff, and_iff_left (h.isUniform.contract C),
    ← (ENat.add_left_injective_of_ne_top hr).eq_iff,
    eRank_contract_add_eRk, h.eRank_eq, hab, hCi.eRk_eq_encard]

lemma IsFiniteRankUniform.contractElem (h : M.IsFiniteRankUniform (a + 1)) (he : e ∈ M.E) :
    (M ／ {e}).IsFiniteRankUniform a :=
  h.contract (a := a + 1) (by simpa) <| by simp

/-- `M.IsFiniteUniform a b n` means that `M` is a finite uniform matroid of rank `a` and corank `b`,
with `n` elements.

We have `a + b = n` for every such matroid, but the redundancy helps with duality. -/
@[mk_iff]
structure IsFiniteUniform (M : Matroid α) (a b : ℕ) (n : ℕ := a + b) : Prop
    extends M.IsFiniteRankUniform a where
  encard_eq : M.E.encard = n
  eRank_dual_eq : M✶.eRank = b

lemma isFiniteUniform_iff' :
    M.IsFiniteUniform a b ↔ M.IsFiniteRankUniform a ∧ M.E.encard = a + b := by
  rw [isFiniteUniform_iff, ENat.coe_add, and_congr_right_iff, and_iff_left_iff_imp]
  refine fun h h' ↦ ?_
  rw [← M.eRank_add_eRank_dual, h.eRank_eq] at h'
  simpa using h'

lemma isFiniteUniform_iff_dual :
    M.IsFiniteUniform a b ↔ M.IsFiniteRankUniform a ∧ M✶.IsFiniteRankUniform b := by
  rw [isFiniteUniform_iff, and_congr_right_iff, M✶.isFiniteRankUniform_iff]
  refine fun h ↦ ⟨fun h' ↦ ⟨h'.2, h.isUniform.dual⟩, fun h' ↦ ⟨?_, h'.1⟩⟩
  rw [← eRank_add_eRank_dual, h'.1, h.eRank_eq, ENat.coe_add]

lemma IsFiniteUniform.finite (hM : M.IsFiniteUniform a b n) : M.Finite :=
  ⟨encard_lt_top_iff.1 <| by simp [hM.encard_eq]⟩

lemma IsFiniteUniform.add_eq {a b n : ℕ} (h : M.IsFiniteUniform a b n) : a + b = n := by
  rw [← ENat.coe_inj, ← h.encard_eq, ← eRank_add_eRank_dual, h.eRank_eq, h.eRank_dual_eq,
    ENat.coe_add]

lemma IsFiniteUniform.le_left (h : M.IsFiniteUniform a b n) : a ≤ n := by
  grw [← h.add_eq, ← le_self_add]

lemma IsFiniteUniform.le_right (h : M.IsFiniteUniform a b n) : b ≤ n := by
  grw [← h.add_eq, ← le_add_self]

lemma IsFiniteUniform.isFiniteUniform_add (h : M.IsFiniteUniform a b n) :
    M.IsFiniteUniform a b (a + b) := by
  rwa [h.add_eq]

lemma IsFiniteUniform.congr₃ (h : M.IsFiniteUniform a b n) {m : ℕ} (hm : m = a + b) :
    M.IsFiniteUniform a b m := by
  rwa [hm, h.add_eq]

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

lemma IsUniform.exists_isFiniteUniform_of_finite' (hM : M.IsUniform) [M.Finite] :
    ∃ a b, M.IsFiniteUniform a b ∧ a = M.eRank ∧ b = M✶.eRank := by
  obtain ⟨a, b, n, h, ha, hb, hn⟩ := hM.exists_isFiniteUniform_of_finite
  exact ⟨a, b, h.isFiniteUniform_add, ha, hb⟩

lemma IsFiniteRankUniform.exists_isFiniteUniform_of_finite (h : M.IsFiniteRankUniform a)
    [M.Finite] : ∃ b n, M.IsFiniteUniform a b n ∧ b = M✶.eRank ∧ n = M.E.encard := by
  obtain ⟨a', b, n, hM1, ha, hb, hn⟩ := h.isUniform.exists_isFiniteUniform_of_finite
  rw [h.eRank_eq, ENat.coe_inj] at ha
  exact ⟨b, n, ha ▸ hM1, hb, hn⟩

lemma isFiniteUniform_dual_iff : M✶.IsFiniteUniform a b n ↔ M.IsFiniteUniform b a n := by
  simp only [isFiniteUniform_iff, isFiniteRankUniform_iff, uniform_dual_iff, dual_ground, dual_dual]
  tauto

alias ⟨IsFiniteUniform.of_dual, IsFiniteUniform.dual⟩ := isFiniteUniform_dual_iff

lemma IsFiniteUniform.dual' (h : M.IsFiniteUniform a b) : M✶.IsFiniteUniform b a :=
  h.dual.isFiniteUniform_add

lemma isFiniteUniform_unifOn {E : Set α} (hE : E.Finite) (a : ℕ) (haE : a ≤ E.encard) :
    ∃ b n, (unifOn E a).IsFiniteUniform a b n ∧ n = E.encard := by
  have : (unifOn E a).Finite := ⟨hE⟩
  obtain ⟨b, n, habc, hb, hn⟩ := (unifOn_isFiniteRankUniform haE).exists_isFiniteUniform_of_finite
  exact ⟨b, n, habc, hn⟩

lemma IsFiniteUniform.dual_eq_self (h : M.IsFiniteUniform a a b) : M✶ = M := by
  obtain ⟨E, rfl, ha⟩ := h.exists_eq_unifOn
  rw [unifOn_dual_eq']
  rw [← unifOn_ground_eq E, h.encard_eq, ← h.add_eq, Nat.cast_add]

lemma IsFiniteUniform.bDual_eq_self (h : M.IsFiniteUniform a a b) (d : Bool) : M.bDual d = M := by
  cases d with
  | false => rfl
  | true => exact h.dual_eq_self

lemma IsFiniteUniform.contractElem (h : M.IsFiniteUniform (a + 1) b (n + 1)) (he : e ∈ M.E) :
    (M ／ {e}).IsFiniteUniform a b n := by
  have hcard : (M ／ {e}).E.encard = ↑n := by
    rw [contract_ground, ← ENat.add_one_inj, encard_diff_singleton_add_one he, h.encard_eq,
      ENat.coe_add, ENat.coe_one]
  refine ⟨h.toIsFiniteRankUniform.contractElem he, hcard, ?_⟩
  have hrd := (M ／ {e}).eRank_add_eRank_dual
  rw [hcard, (h.toIsFiniteRankUniform.contractElem he).eRank_eq] at hrd
  have ha := h.add_eq
  enat_to_nat!
  lia

lemma IsFiniteUniform.deleteElem (h : M.IsFiniteUniform a (b + 1) (n + 1)) (he : e ∈ M.E) :
    (M ＼ {e}).IsFiniteUniform a b n := by
  simpa using (h.dual.contractElem he).dual

lemma IsFiniteUniform.contractElem' (h : M.IsFiniteUniform (a + 1) b) (he : e ∈ M.E) :
    (M ／ {e}).IsFiniteUniform a b :=
  IsFiniteUniform.contractElem (h.congr₃ (add_right_comm ..)) he

lemma IsFiniteUniform.deleteElem' (h : M.IsFiniteUniform a (b + 1)) (he : e ∈ M.E) :
    (M ＼ {e}).IsFiniteUniform a b := by
  simpa using (h.dual'.contractElem' he).dual'

lemma IsFiniteUniform.nonempty_iso_unif (hM : M.IsFiniteUniform a b n) :
    Nonempty (M ≂ unif a n) := by
  rw [unif, nonempty_iso_unifOn_iff, and_iff_right hM.toIsFiniteRankUniform,
    ← Finite.encard_eq_iff_nonempty_equiv hM.finite.ground_finite,
    encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, hM.encard_eq]
  grw [encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, Nat.cast_le,
    ← hM.add_eq, ← le_self_add]

/-- Two finite uniform matroids with the same parameters are isomorphic. -/
lemma IsFiniteUniform.nonempty_iso (hM : M.IsFiniteUniform a b n) {β : Type*} {N : Matroid β}
    {m : ℕ} (hN : N.IsFiniteUniform a b m) : Nonempty (M ≂ N) := by
  obtain ⟨e⟩ := (hM.add_eq ▸ hM).nonempty_iso_unif
  obtain ⟨f⟩ := (hN.add_eq ▸ hN).nonempty_iso_unif
  exact ⟨e.trans f.symm⟩

lemma IsFiniteUniform.of_iso (hM : M.IsFiniteUniform a b n) {β : Type*} {N : Matroid β}
    (e : M ≂ N) : N.IsFiniteUniform a b n := by
  refine ⟨hM.toIsFiniteRankUniform.of_iso e, ?_, ?_⟩
  · rw [← e.toEquiv.encard_eq, hM.encard_eq]
  rw [← e.dual.eRank_eq, hM.eRank_dual_eq]

lemma Iso.isFiniteUniform_iff {β : Type*} {N : Matroid β} (e : M ≂ N) :
    M.IsFiniteUniform a b n ↔ N.IsFiniteUniform a b n :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- A finite-rank uniform matroid is one of the obvious ones - maybe use `IsFiniteRankUniform`
instead  -/
lemma IsUniform.exists_eq_unifOn [M.RankFinite] (hM : M.IsUniform) :
    ∃ (E : Set α) (k : ℕ), k ≤ E.encard ∧ M = unifOn E k ∧ M.eRank = k := by
  obtain ⟨k, hk⟩ := hM.isFiniteRankUniform
  obtain ⟨E, rfl, hkE⟩ := hk.exists_eq_unifOn
  exact ⟨E, k, hkE, rfl, by simpa⟩

lemma unifOn_isUniform (E : Set α) (k : ℕ) : (unifOn E k).IsUniform := by
  intro X (hX : X ⊆ E)
  rw [unifOn_indep_iff, unifOn_spanning_iff']
  grind

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

theorem nonempty_iso_unif_iff' :
    Nonempty (M ≂ (unif a (a + b))) ↔ M.IsFiniteUniform a b := by
  rw [unif, nonempty_iso_unifOn_iff (by simp), ← Finite.encard_eq_iff_nonempty_equiv' (by simp),
    encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, isFiniteUniform_iff, eq_comm]
  simp only [Nat.cast_add, and_congr_right_iff, iff_self_and]
  intro hr he
  rw [← eRank_add_eRank_dual, hr.eRank_eq] at he
  enat_to_nat!; lia

theorem nonempty_iso_unif_iff (hab : a ≤ b) :
    Nonempty (M ≂ (unif a b)) ↔ M.IsFiniteRankUniform a ∧ M.E.encard = b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [nonempty_iso_unif_iff']
  refine ⟨fun h ↦ ⟨h.toIsFiniteRankUniform, h.encard_eq⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
  rw [← eRank_add_eRank_dual, h.1.eRank_eq] at h
  enat_to_nat!; lia

theorem nonempty_iso_unif_iff'' :
    Nonempty (M ≂ (unif a b)) ↔ M.IsFiniteRankUniform (min a b) ∧ M.E.encard = b := by
  rw [unif_eq_unif_min, nonempty_iso_unif_iff (by simp)]

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_iso_unif_iff''' :
    Nonempty (M ≂ (unif a b)) ↔ ∃ E, (M = unifOn E a ∧ E.encard = b) := by
  rw [nonempty_iso_unif_iff'']
  refine ⟨fun h ↦ ⟨M.E, ?_, h.2⟩, ?_⟩
  · nth_rw 1 [h.1.eq_unifOn]
    refine ext_indep rfl fun I (hI : I ⊆ M.E) ↦ ?_
    simp only [unifOn_indep_iff, and_congr_left_iff]
    refine fun h' ↦ ⟨fun hle ↦ hle.trans (by simp),
      fun hle ↦ (le_min hle (encard_le_encard hI)).trans ?_⟩
    rw [h.2]
    simp only [inf_le_iff, Nat.cast_le, le_inf_iff, Std.le_refl, true_and, and_true]
    grind
  rintro ⟨E, rfl, hb⟩
  simp [hb, isFiniteRankUniform_iff, min_comm, le_antisymm_iff, show a ≤ b ∨ b ≤ a by lia]



-- theorem nonempty_iso_unif_iff' :
--     Nonempty (M ≂ (unif a b)) ↔ (M = unifOn M.E a ∧ M.E.encard = b) := by
--   rw [nonempty_iso_unif_iff]
--   exact ⟨by rintro ⟨E, rfl, h⟩; simp [h], fun h ↦ ⟨M.E, by simpa⟩⟩


lemma eq_unifOn_of_eRank_le_one [M.Loopless] (hM : M.eRank ≤ 1) : ∃ E, M = unifOn E 1 := by
  simp +contextual only [ext_iff_indep, unifOn_ground_eq, unifOn_indep_iff, exists_eq_left',
    and_true]
  exact fun I hIE ↦ ⟨fun hI ↦ hI.encard_le_eRank.trans hM,
    fun hI ↦ subsingleton_indep (encard_le_one_iff_subsingleton.1 hI) hIE⟩

lemma isFiniteRankUniform_of_eRank_le_one [M.Loopless] [M.Nonempty] (hM : M.eRank ≤ 1) :
    M.IsFiniteRankUniform 1 := by
  obtain ⟨E, rfl⟩ := eq_unifOn_of_eRank_le_one hM
  refine unifOn_isFiniteRankUniform ?_
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
    M.IsFiniteRankUniform 2 := by
  obtain ⟨E, rfl⟩ := eq_unifOn_of_eRank_le_two hM
  exact unifOn_isFiniteRankUniform <| two_le_encard_iff_nontrivial.2 hnt

@[simp]
lemma unifOn_one_dual (E : Set α) : (unifOn E 1)✶ = circuitOn E := by
  rw [← circuitOn_dual, dual_dual]

theorem nonempty_iso_line_iff {n : ℕ} :
    Nonempty (M ≂ unif 2 n) ↔ M.Simple ∧ M.eRank ≤ 2 ∧ M.E.encard = n := by
  simp [nonempty_iso_unif_iff''', ← and_assoc, eq_unifOn_two_iff, and_comm]

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
