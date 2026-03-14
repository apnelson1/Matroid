import Matroid.Extension.ProjectBy
import Matroid.ForMathlib.FinDiff

variable {α : Type*} {M : Matroid α} {E I B : Set α} {k : ℕ∞}

namespace Matroid

open Set

@[simp]
lemma ground_not_subset_loops [M.RankPos] : ¬ M.E ⊆ M.loops := by
  intro hE
  have hlt := M.eRank_pos
  grw [← eRk_ground, M.eRk_mono hE, eRk_loops] at hlt
  simp at hlt

section truncateTo

/-- The `IndepMatroid` whose independent sets are the `M`-independent sets of size at most `k`. -/
def truncateToNat (M : Matroid α) (k : ℕ) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofBddAugment
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ I.encard ≤ k)
  (indep_empty := by simp)
  (indep_subset := fun I J hI hIJ ↦ ⟨hI.1.subset hIJ, (encard_mono hIJ).trans hI.2⟩)
  (indep_aug := by
    rintro I J ⟨hI, _⟩ ⟨hJ, hJc⟩ hIJ
    obtain ⟨e, he, hi⟩ := hI.augment hJ hIJ
    exact ⟨e, he.1, he.2, hi,
      (encard_insert_of_notMem he.2).trans_le ((Order.add_one_le_of_lt hIJ).trans hJc)⟩)
  (indep_bdd := ⟨k, fun _ ↦ And.right⟩)
  (subset_ground := fun _ h ↦ h.1.subset_ground)

/-- The truncation of a matroid to rank `k`. The independent sets of the truncation
are the independent sets of the matroid of size at most `k`.  -/
def truncateTo (M : Matroid α) (k : ℕ∞) : Matroid α :=
  Matroid.ofExistsMatroid
    (E := M.E)
    (Indep := fun I ↦ M.Indep I ∧ I.encard ≤ k)
    (hM :=  k.recTopCoe ⟨M, rfl, by simp⟩
      (fun k ↦ ⟨M.truncateToNat k, rfl, fun _ ↦ by simp [truncateToNat]⟩))

@[simp] theorem truncateTo_top (M : Matroid α) : M.truncateTo ⊤ = M :=
  ext_indep rfl (by simp [truncateTo, Matroid.ofExistsMatroid])

@[simp] theorem truncateTo_indep_iff : (M.truncateTo k).Indep I ↔ (M.Indep I ∧ I.encard ≤ k) :=
    Iff.rfl

theorem truncateTo_indep_eq : (M.truncateTo k).Indep = fun I ↦ M.Indep I ∧ I.encard ≤ k := rfl

@[simp] theorem truncateTo_ground_eq : (M.truncateTo k).E = M.E := rfl

@[simp] theorem truncateTo_zero (M : Matroid α) : M.truncateTo 0 = loopyOn M.E := by
  refine ext_indep rfl ?_
  suffices ∀ I ⊆ M.E, I = ∅ → M.Indep I by simpa
  rintro I - rfl; exact M.empty_indep

@[simp] theorem truncateTo_emptyOn (α : Type*) (k : ℕ∞) : (emptyOn α).truncateTo k = emptyOn α := by
  rw [← ground_eq_empty_iff, truncateTo_ground_eq, emptyOn_ground]

@[simp] theorem truncate_loopyOn (E : Set α) (k : ℕ∞) : (loopyOn E).truncateTo k = loopyOn E := by
  apply ext_indep (by simp)
  suffices ∀ I ⊆ E, I = ∅ → encard I ≤ k by simpa
  rintro _ - rfl; simp

theorem truncate_eq_self_of_rank_le (h_rank : M.eRank ≤ k) : M.truncateTo k = M := by
  refine ext_indep truncateTo_ground_eq (fun I _ ↦ ?_)
  rw [truncateTo_indep_iff, and_iff_left_iff_imp]
  exact fun hi ↦ hi.encard_le_eRank.trans h_rank

theorem truncateTo_isBase_iff {k : ℕ} (h_rank : k ≤ M.eRank) :
    (M.truncateTo k).IsBase B ↔ M.Indep B ∧ B.encard = k := by
  simp_rw [isBase_iff_maximal_indep, truncateTo_indep_eq, maximal_subset_iff, and_assoc,
    and_congr_right_iff, and_imp]
  refine fun hi ↦ ⟨fun ⟨hle, hmax⟩ ↦ ?_, fun h ↦ ⟨h.le, fun J _ hcard hBJ ↦ ?_⟩⟩
  · obtain ⟨B', hB', hBB'⟩ := hi.exists_isBase_superset
    obtain ⟨J, hBJ, hJB', h'⟩ := exists_superset_subset_encard_eq hBB' hle
      (by rwa [hB'.encard_eq_eRank])
    rwa [hmax (hB'.indep.subset hJB') h'.le hBJ]
  exact (finite_of_encard_le_coe hcard).eq_of_subset_of_encard_le' hBJ <| hcard.trans_eq h.symm

theorem truncate_isBase_iff_of_rankFinite [RankFinite M] (h_rank : k ≤ M.eRank) :
    (M.truncateTo k).IsBase B ↔ M.Indep B ∧ B.encard = k := by
  lift k to ℕ using (h_rank.trans_lt M.eRank_lt_top).ne; rwa [truncateTo_isBase_iff]

instance truncateTo.finite [Matroid.Finite M] : Matroid.Finite (M.truncateTo k) :=
⟨ by simp [ground_finite M] ⟩

instance truncateTo.rankFinite {k : ℕ} : RankFinite (M.truncateTo k) := by
  obtain ⟨B, hB⟩ := (M.truncateTo k).exists_isBase
  refine ⟨B, hB, (le_or_gt M.eRank k).elim (fun h ↦ ?_) (fun h ↦ ?_)⟩
  · rw [truncate_eq_self_of_rank_le h] at hB
    rw [← encard_lt_top_iff, hB.encard_eq_eRank]
    exact h.trans_lt (WithTop.coe_lt_top _)
  rw [truncateTo_isBase_iff h.le] at hB
  rw [← encard_lt_top_iff, hB.2]
  apply WithTop.coe_lt_top

theorem Indep.of_truncateTo (h : (M.truncateTo k).Indep I) : M.Indep I := by
  rw [truncateTo_indep_iff] at h; exact h.1

theorem Indep.encard_le_of_truncateTo (h : (M.truncateTo k).Indep I) : I.encard ≤ k :=
  (truncateTo_indep_iff.mp h).2

theorem truncateTo_eRk_eq (M : Matroid α) (k : ℕ∞) (X : Set α) :
    (M.truncateTo k).eRk X = min (M.eRk X) k := by
  simp_rw [le_antisymm_iff, le_eRk_iff, eRk_le_iff, truncateTo_indep_iff]
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  refine ⟨?_, ?_⟩
  · intro J hJX hJi
    exact le_min (hJi.1.encard_le_eRk_of_subset hJX) hJi.2
  obtain ⟨I₀, hI₀, hI₀ss⟩ := exists_subset_encard_eq
    (min_le_of_left_le (b := k) hI.encard_eq_eRk.symm.le)
  exact ⟨_, hI₀.trans hI.subset, ⟨hI.indep.subset hI₀, hI₀ss.trans_le (min_le_right _ _)⟩, hI₀ss⟩


end truncateTo

section truncate

/-- The matroid on `M.E` whose independent sets are the independent nonbases of `M`. -/
def truncate (M : Matroid α) := Matroid.ofExistsMatroid
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ (M.IsBase I → I = ∅))
  (hM := by
    refine ⟨M.projectBy (ModularCut.principal M M.E), rfl, fun I ↦ ?_⟩
    obtain (hM | hM) := M.eq_loopyOn_or_rankPos
    · rw [hM]; simp [ModularCut.eq_top_iff, loops]
    suffices M.Indep I → (¬M.closure I = M.E ↔ M.IsBase I → I = ∅) by simpa
    refine fun hI ↦ ⟨fun h hIb ↦ by simp [hIb.closure_eq] at h, fun h hss ↦ ?_⟩
    have hIb := hI.isBase_of_ground_subset_closure hss.symm.subset
    exact hIb.nonempty.ne_empty (h hIb))

@[simp] lemma truncate_ground_eq : M.truncate.E = M.E := rfl

lemma truncate_indep_iff' : M.truncate.Indep I ↔ M.Indep I ∧ (M.IsBase I → I = ∅) := Iff.rfl

@[simp] lemma truncate_indep_iff [M.RankPos] : M.truncate.Indep I ↔ M.Indep I ∧ ¬ M.IsBase I := by
  simp only [truncate_indep_iff', and_congr_right_iff]
  exact fun _ ↦ ⟨fun h hB ↦ hB.nonempty.ne_empty (h hB), fun h hB ↦ by contradiction⟩

lemma truncate_dep_iff [M.RankPos] {D} :
    M.truncate.Dep D ↔ (M.Indep D → M.IsBase D) ∧ D ⊆ M.E := by
  rw [dep_iff, truncate_indep_iff, truncate_ground_eq, not_and, not_not]

@[simp] lemma truncate_loopyOn_eq {E : Set α} : (loopyOn E).truncate = loopyOn E := by
  simp +contextual [truncate, eq_loopyOn_iff, Matroid.ofExistsMatroid]

@[simp] lemma truncate_emptyOn_eq (α : Type*) : (emptyOn α).truncate = emptyOn α := by
  rw [← ground_eq_empty_iff]
  rfl

instance {M : Matroid α} [M.Nonempty] : M.truncate.Nonempty := ⟨M.ground_nonempty⟩

@[simp] lemma truncate_isBase_iff [M.RankPos] :
    M.truncate.IsBase B ↔ ∃ e ∉ B, M.IsBase (insert e B) := by
  refine ⟨fun h ↦ ?_, fun ⟨e, he, hBe⟩ ↦ ?_⟩
  · obtain ⟨hB, hBb⟩ := truncate_indep_iff.1 h.indep
    obtain ⟨B', hB', hBB'⟩ := hB.exists_isBase_superset
    obtain ⟨e, heB', heB⟩ := exists_of_ssubset (hBB'.ssubset_of_ne (by rintro rfl; contradiction))
    refine ⟨e, heB, ?_⟩
    rwa [h.eq_of_subset_indep ?_ (subset_diff_singleton hBB' heB), insert_diff_singleton,
      insert_eq_of_mem heB']
    rw [truncate_indep_iff]
    exact ⟨hB'.indep.subset diff_subset, hB'.not_isBase_of_ssubset <| diff_singleton_ssubset.2 heB'⟩
  refine Indep.isBase_of_forall_insert ?_ ?_
  · rw [truncate_indep_iff]
    exact ⟨hBe.indep.subset (subset_insert _ _), hBe.not_isBase_of_ssubset (ssubset_insert he)⟩
  simp only [truncate_ground_eq, mem_diff, truncate_indep_iff, not_and, not_not, and_imp]
  exact fun f _ hfB hfBi ↦ insert_isBase_of_insert_indep he hfB hBe hfBi

lemma IsBase.diff_singleton_truncate_isBase {e : α} (hB : M.IsBase B) (heB : e ∈ B) :
    M.truncate.IsBase (B \ {e}) := by
  have hpos : M.RankPos := hB.rankPos_of_nonempty ⟨e, heB⟩
  rw [truncate_isBase_iff]
  exact ⟨e, by simp, by simpa [heB]⟩

@[simp] lemma truncate_spanning_iff [M.RankPos] {S : Set α} :
    M.truncate.Spanning S ↔ ∃ e ∈ M.E, M.Spanning (insert e S) := by
  simp only [spanning_iff_exists_isBase_subset', truncate_isBase_iff, truncate_ground_eq,
    insert_subset_iff, ← and_assoc, exists_and_right, and_congr_left_iff]
  refine fun hSE ↦ ⟨fun ⟨B, ⟨e, he, heB⟩, hBS⟩ ↦ ?_, fun ⟨e, ⟨h, B, hB, hBS⟩, _⟩ ↦ ?_⟩
  · have heE : e ∈ M.E := heB.subset_ground (mem_insert _ _)
    exact ⟨e, ⟨heE, _, heB, insert_subset_insert hBS⟩, heE⟩
  by_cases heB : e ∈ B
  · exact ⟨B \ {e}, ⟨e, by simpa [heB]⟩, by simpa⟩
  rw [← diff_singleton_subset_iff, diff_singleton_eq_self heB] at hBS
  obtain ⟨f, hf⟩ := hB.nonempty
  exact ⟨B \ {f}, ⟨f, by simpa [hf]⟩, diff_subset.trans hBS⟩

lemma truncate_spanning_iff_of_ssubset {S : Set α} (hssu : S ⊂ M.E) :
    M.truncate.Spanning S ↔ ∃ e ∈ M.E \ S, M.Spanning (insert e S) := by
  obtain ⟨f, hf⟩ := exists_of_ssubset hssu
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · simp only [truncate_loopyOn_eq, loopyOn_spanning_iff, show S ⊆ E from hssu.subset,
      loopyOn_ground, mem_diff, insert_subset_iff, and_true, true_iff]
    exact ⟨f, hf, hf.1⟩
  rw [truncate_spanning_iff]
  refine ⟨fun ⟨e, heE, he⟩ ↦ ?_, fun ⟨e, heE, he⟩ ↦ ⟨e, heE.1, he⟩⟩
  by_cases heS : e ∈ S
  · exact ⟨f, hf, he.superset (insert_subset (mem_insert_of_mem _ heS) (subset_insert _ _))⟩
  exact ⟨e, ⟨heE, heS⟩, he⟩

lemma Spanning.truncate_spanning {S : Set α} (hS : M.Spanning S) : M.truncate.Spanning S := by
  obtain rfl | hssu := hS.subset_ground.eq_or_ssubset
  · exact M.truncate.ground_spanning
  rw [truncate_spanning_iff_of_ssubset hssu]
  obtain ⟨f, hf⟩ := exists_of_ssubset hssu
  exact ⟨f, hf, hS.superset (subset_insert _ _)⟩

lemma Coindep.truncate_delete {D : Set α} (hD : M.Coindep D) :
    (M ＼ D).truncate = M.truncate ＼ D := by
  refine ext_indep rfl fun I hI ↦ ?_
  rw [truncate_ground_eq, delete_ground, subset_diff] at hI
  rw [delete_indep_iff, truncate_indep_iff', hD.delete_isBase_iff, and_iff_left hI.2,
    truncate_indep_iff', delete_indep_iff, and_iff_left hI.2, and_iff_left hI.2]

lemma truncate_restrict_of_not_spanning {R : Set α} (hSE : R ⊆ M.E) (hS : ¬ M.Spanning R) :
    (M.truncate ↾ R) = M ↾ R := by
  refine ext_indep rfl fun I hI ↦ ?_
  simp only [restrict_indep_iff, truncate_indep_iff', and_congr_left_iff, and_iff_left_iff_imp]
  refine fun hIR _ hI ↦ (hS (hI.spanning.superset hIR)).elim

lemma truncate_contract (M : Matroid α) (C : Set α) : (M ／ C).truncate = M.truncate ／ C := by
  suffices aux : ∀ C ⊆ M.E, (M ／ C).truncate = M.truncate ／ C by
    convert aux (C ∩ M.E) inter_subset_right using 1
    simp
    rw [← contract_inter_ground_eq, truncate_ground_eq]
  clear C
  intro C hCE
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · simp
  by_cases hC : M.Spanning C
  · have hC' : M.truncate.Spanning C := by
      rw [truncate_spanning_iff]
      obtain ⟨B, hB⟩ := M.exists_isBase
      obtain ⟨e, he⟩ := hB.nonempty
      have heE := hB.subset_ground he
      exact ⟨e, hB.subset_ground he, hC.superset (subset_insert _ _)⟩
    simp [hC.contract_eq_loopyOn, hC'.contract_eq_loopyOn]

  have hpos : (M ／ C).RankPos
  · rwa [rankPos_iff_empty_not_spanning, contract_spanning_iff, empty_union,
      and_iff_left (empty_disjoint _)]

  refine ext_spanning rfl fun S hS ↦ ?_
  simp only [truncate_ground_eq, contract_ground, subset_diff] at hS
  simp only [truncate_spanning_iff, contract_ground, mem_diff, ← singleton_union,
    contract_spanning_iff hCE, disjoint_union_left, disjoint_singleton_left, hS.2, and_true,
    contract_spanning_iff (show C ⊆ M.truncate.E from hCE)]
  simp_rw [singleton_union, insert_union]
  refine ⟨fun ⟨e, he⟩ ↦ ⟨e, he.1.1, he.2.1⟩, fun ⟨e, he⟩ ↦ ?_⟩
  by_cases heC : e ∈ C
  · obtain ⟨B, hB⟩ := (M ／ C).exists_isBase
    obtain ⟨f, hf⟩ := hB.nonempty
    have hf' : f ∈ M.E \ C := ⟨(hB.subset_ground.trans diff_subset) hf, (hB.subset_ground hf).2⟩
    rw [insert_eq_of_mem (.inr heC)] at he
    exact ⟨f, ⟨hf'.1, hf'.2⟩, he.2.superset (subset_insert _ _), hf'.2⟩
  exact ⟨e, ⟨he.1, heC⟩, he.2, heC⟩

instance (M : Matroid α) [M.Nonempty] : M.truncate✶.RankPos := by
  have hE := M.ground_nonempty
  obtain ⟨E, rfl⟩ | hpos := M.eq_loopyOn_or_rankPos'
  · simpa [rankPos_iff, eq_comm] using hE.ne_empty
  rw [rankPos_iff]
  simp only [truncate_ground_eq, empty_subset, dual_isBase_iff, diff_empty, truncate_isBase_iff,
    not_exists, not_and]
  exact fun x hx hB ↦ hx <| hB.subset_ground (mem_insert ..)

lemma truncate_eRank_add_one [M.RankPos] : M.truncate.eRank + 1 = M.eRank := by
  obtain ⟨B, hB⟩ := M.truncate.exists_isBase
  rw [← hB.encard_eq_eRank]
  obtain ⟨e, heB, hB'⟩ := truncate_isBase_iff.1 hB
  rw [← hB'.encard_eq_eRank, encard_insert_of_notMem heB]

@[simp]
lemma truncate_rankPos_iff : M.truncate.RankPos ↔ 2 ≤ M.eRank := by
  obtain ⟨E, rfl⟩ | hM := M.exists_eq_loopyOn_or_rankPos
  · simp [← eRank_ne_zero_iff]
  rw [← eRank_ne_zero_iff, ← ENat.one_le_iff_ne_zero, ← M.truncate_eRank_add_one]
  simp [← one_add_one_eq_two]

lemma truncateTo_truncate (M : Matroid α) (k : ℕ) (hk : k + 1 ≤ M.eRank) :
    (M.truncateTo (k + 1 : ℕ)).truncate = M.truncateTo k := by
  refine ext_indep rfl fun I hI ↦ ?_
  simp only [truncate_indep_iff', truncateTo_indep_iff, truncateTo_isBase_iff hk]
  simp only [Nat.cast_add, Nat.cast_one, and_imp]
  refine ⟨fun h ↦ ⟨h.1.1, ?_⟩, fun h ↦ ?_⟩
  · obtain h_eq | hlt := h.1.2.eq_or_lt
    · simp [h.2 h.1.1 h_eq]
    exact Order.le_of_lt_add_one hlt
  refine ⟨⟨h.1, h.2.trans le_self_add⟩, fun hI hIk ↦ ?_⟩
  simp [hIk] at h

lemma truncate_isCircuit_iff {C} [M.RankPos] :
    M.truncate.IsCircuit C ↔ (M.IsCircuit C ∧ ¬ M.Spanning C) ∨ M.IsBase C := by
  by_cases! hCE : ¬(C ⊆ M.E); grind
  simp only [isCircuit_iff_forall_ssubset, truncate_dep_iff, hCE, and_true, truncate_indep_iff]
  obtain (hCi | hCd) := M.indep_or_dep hCE
  · suffices M.IsBase C → ∀ ⦃I : Set α⦄, I ⊂ C → M.Indep I ∧ ¬M.IsBase I by simpa [hCi.not_dep, hCi]
    exact fun hCb I hIC ↦ ⟨hCi.subset hIC.subset, hCb.not_isBase_of_ssubset hIC⟩
  suffices (∀ x ⊂ C, M.Indep x) → ((∀ x ⊂ C, ¬M.IsBase x) ↔ ¬M.Spanning C) by
    simpa [hCd.not_indep, IsEmpty.forall_iff, true_and, hCd,
      or_iff_left (show ¬M.IsBase C from fun h ↦ hCd.not_indep h.indep), forall_and]
  refine fun hCss ↦ ⟨fun h hsp ↦ ?_, fun h B hBC hB ↦ h <| hB.spanning_of_superset hBC.subset ⟩
  obtain ⟨B, hB, hBC⟩ := hsp.exists_isBase_subset
  obtain rfl | hssu := hBC.eq_or_ssubset
  · exact hCd.not_indep hB.indep
  exact h _ hssu hB

end truncate

def freeLift (M : Matroid α) : Matroid α := M✶.truncate✶

@[simp]
lemma freeLift_ground (M : Matroid α) : M.freeLift.E = M.E := rfl

@[simp]
lemma freeLift_freeOn (E : Set α) : (freeOn E).freeLift = freeOn E := by
  simp [freeLift]

@[simp]
lemma freeLift_emptyOn (α : Type*) : (emptyOn α).freeLift = emptyOn α := by
  simp [freeLift]

lemma freeLift_isBase_iff [M✶.RankPos] :
    M.freeLift.IsBase B ↔ (∃ e ∈ B, M.IsBase (B \ {e})) ∧ B ⊆ M.E := by
  wlog hBE : B ⊆ M.E; grind [freeLift_ground]
  rw [freeLift, dual_isBase_iff', truncate_ground_eq, dual_ground, truncate_isBase_iff]
  simp only [mem_diff, not_and, not_not, ← union_singleton, dual_isBase_iff', ← diff_diff,
    diff_diff_cancel_left hBE, union_subset_iff, singleton_subset_iff, hBE]
  grind

@[simp]
lemma freeLift_dual (M : Matroid α) : M.freeLift✶ = M✶.truncate := by
  simp [freeLift]

@[simp]
lemma truncate_dual (M : Matroid α) : M.truncate✶ = M✶.freeLift := by
  simp [freeLift]

instance [M.Nonempty] : (freeLift M).RankPos := by
  obtain ⟨E, rfl⟩ | h := M.exists_eq_freeOn_or_rankPos_dual
  · simp only [freeLift_freeOn, rankPos_iff, freeOn_isBase_iff]
    exact (freeOn E).ground_nonempty.ne_empty.symm
  simp [rankPos_iff, freeLift_isBase_iff]

@[simp]
lemma eRank_freeLift_eq [M✶.RankPos] : (freeLift M).eRank = M.eRank + 1 := by
  obtain ⟨B, hB⟩ := (freeLift M).exists_isBase
  rw [← hB.encard_eq_eRank]
  rw [freeLift_isBase_iff] at hB
  obtain ⟨⟨e, heB, hB⟩, hBE⟩ := hB
  rw [← encard_diff_singleton_add_one heB, hB.encard_eq_eRank]

lemma freeLift_indep_iff :
    M.freeLift.Indep I ↔ (I.Nonempty → ∃ e ∈ I ∩ M.E, M.Indep (I \ {e})) := by
  obtain rfl | hne := I.eq_empty_or_nonempty; simp
  obtain ⟨E, rfl⟩ | h := M.exists_eq_freeOn_or_rankPos_dual
  · simp only [freeLift_freeOn, freeOn_indep_iff, hne, freeOn_ground, mem_inter_iff,
      diff_singleton_subset_iff, forall_const]
    obtain ⟨f, hf⟩ := hne
    exact ⟨fun h ↦ ⟨f, by grind⟩, fun ⟨e, he⟩ ↦ by grind⟩
  simp only [indep_iff, freeLift_isBase_iff, hne, mem_inter_iff, diff_singleton_subset_iff,
    forall_const]
  refine ⟨fun ⟨B, ⟨⟨e, heB, hBe⟩, hBE⟩, hIB⟩ ↦ ?_,
    fun ⟨e, he, B, hB, hIB⟩ ↦ ?_⟩
  · by_cases heI : e ∈ I
    · exact ⟨e, by grind, _, hBe, by grind⟩
    obtain ⟨f, hf⟩ := hne
    exact ⟨f, by grind, _, hBe, by grind⟩
  by_cases heB : e ∈ B
  · obtain ⟨f, hfE, hfB⟩ := exists_of_ssubset hB.ssubset_ground
    refine ⟨insert f B, ⟨⟨f, by grind, ?_⟩, by grind⟩, by grind⟩
    rwa [insert_diff_self_of_notMem hfB]
  exact ⟨insert e B, ⟨⟨⟨e, by simp, by rwa [insert_diff_self_of_notMem heB]⟩, by grind⟩, hIB⟩⟩

instance : (freeLift M).Loopless := by
  simp [loopless_iff_forall_isNonloop, ← indep_singleton, freeLift_indep_iff]

instance [M.Loopless] : (freeLift M).Simple := by
  simp only [simple_iff_forall_pair_indep, freeLift_ground, freeLift_indep_iff, insert_nonempty,
    mem_inter_iff, mem_insert_iff, mem_singleton_iff, forall_const]
  refine fun e f he hf ↦ ⟨e, ⟨by simp, he⟩, (isNonloop_of_loopless hf).indep.subset <| by simp⟩

lemma freeLift_dep_iff {D} :
  M.freeLift.Dep D ↔ D.Nonempty ∧ (∀ e ∈ D, M.Dep (D \ {e})) ∧ D ⊆ M.E := by
  simp only [dep_iff, freeLift_indep_iff, mem_inter_iff, Classical.not_imp, not_exists, not_and,
    and_imp, freeLift_ground, diff_singleton_subset_iff, forall_mem_and]
  grind

lemma truncate_freeLift (M : Matroid α) [M.RankPos] [M✶.RankPos] :
    M.truncate.freeLift = M.freeLift.truncate := by
  refine ext_isBase rfl fun B hB ↦ ?_
  simp only [freeLift_isBase_iff, truncate_isBase_iff, mem_diff, mem_singleton_iff, not_and,
    not_not, truncate_ground_eq, show B ⊆ M.E from hB, and_true, mem_insert_iff, exists_eq_or_imp,
    insert_diff_of_mem, insert_subset_iff]
  refine ⟨fun ⟨f, hfB, e, he, hB⟩ ↦ ?_, ?_⟩
  · obtain rfl | hne := eq_or_ne e f
    · rw [insert_diff_self_of_mem hfB] at hB
      obtain ⟨x, hxE, hxB⟩ := exists_of_ssubset hB.ssubset_ground
      refine ⟨x, hxB, .inl ?_, hxE⟩
      rwa [diff_singleton_eq_self hxB]
    refine ⟨e, by grind, .inr ⟨f, hfB, ?_⟩, hB.subset_ground (by grind)⟩
    rwa [← insert_diff_singleton_comm hne]
  rintro ⟨e, heB, h | ⟨f, hfB, hB'⟩, heE⟩
  · rw [diff_singleton_eq_self heB] at h
    obtain ⟨f, hfB⟩ := h.nonempty
    exact ⟨f, hfB, f, by simp, by rwa [insert_diff_self_of_mem hfB]⟩
  refine ⟨f, hfB, e, by simp [heB], ?_⟩
  rwa [insert_diff_singleton_comm (by rintro rfl; contradiction)]

-- The lemma stated below is false. Circuits of the free lift are the minimal sets of nullity 2,
-- rather than the sets that are one removal away from being a circuit.
-- an example showing the difference is the directed sum of two triangles, which gets
-- free-lifted onto a circuit.

-- WRONG lemma freeLift_isCircuit_iff {C} :
--     M.freeLift.IsCircuit C ↔ (∃ e ∈ C, M.IsCircuit (C \ {e})) ∧ C ⊆ M.E := by

lemma freeLift_spanning_iff [M✶.RankPos] {X} :
    M.freeLift.Spanning X ↔ (∃ e ∈ X, M.Spanning (X \ {e})) ∧ X ⊆ M.E := by
  by_cases! hX : ¬ X ⊆ M.E; grind
  rw [freeLift, spanning_dual_iff (by simpa), truncate_ground_eq,
    truncate_indep_iff, dual_ground, dual_isBase_iff, diff_diff_cancel_left hX, ← Coindep,
    ← spanning_iff_compl_coindep, and_iff_left hX]
  refine ⟨fun ⟨hs, hb⟩ ↦ ?_, fun ⟨e, heX, hXs⟩ ↦ ?_⟩
  · obtain ⟨B, hB⟩ := hs.exists_isBase_subset
    obtain ⟨e, heX, heB⟩ := exists_of_ssubset (hB.2.ssubset_of_ne <| by grind)
    exact ⟨e, heX, hB.1.spanning.superset (by grind) (by grind)⟩
  refine ⟨hXs.superset diff_subset hX, fun hB ↦ ?_⟩
  grind [hB.eq_of_superset_spanning hXs diff_subset]

section circuitOn

variable {C : Set α}

/-- The matroid on `E` whose ground set is a circuit. Empty if `E = ∅`. -/
def circuitOn (C : Set α) := (freeOn C).truncate

@[simp]
lemma freeOn_truncate (C : Set α) : (freeOn C).truncate = circuitOn C := rfl

@[simp] lemma circuitOn_ground : (circuitOn C).E = C := rfl

@[simp] lemma circuitOn_empty (α : Type*) : circuitOn (∅ : Set α) = emptyOn α := by
  simp [circuitOn]

lemma circuitOn_indep_iff (hC : C.Nonempty) : (circuitOn C).Indep I ↔ I ⊂ C := by
  have := freeOn_rankPos hC
  rw [circuitOn, truncate_indep_iff, ssubset_iff_subset_ne]
  simp

lemma circuitOn_dep_iff (hC : C.Nonempty) {D : Set α} : (circuitOn C).Dep D ↔ D = C := by
  simp only [Dep, circuitOn_indep_iff hC, ssubset_iff_subset_ne, ne_eq, not_and, not_not,
    circuitOn_ground]
  exact ⟨fun h ↦ h.1 h.2, by rintro rfl; simp⟩

lemma circuitOn_isBase_iff (hC : C.Nonempty) :
    (circuitOn C).IsBase B ↔ ∃ e ∉ B, insert e B = C := by
  have _ := freeOn_rankPos hC; simp [circuitOn, -freeOn_truncate, truncate_isBase_iff]

lemma circuitOn_ground_isCircuit (hC : C.Nonempty) : (circuitOn C).IsCircuit C := by
  simp [isCircuit_iff_forall_ssubset, circuitOn_dep_iff hC, circuitOn_indep_iff hC]

lemma circuitOn_isCircuit_iff (hC : C.Nonempty) {C' : Set α} :
    (circuitOn C).IsCircuit C' ↔ C' = C := by
  refine ⟨fun h ↦ h.eq_of_subset_isCircuit (circuitOn_ground_isCircuit hC) h.subset_ground, ?_⟩
  rintro rfl
  exact circuitOn_ground_isCircuit hC

lemma circuitOn_spanning_iff (hC : C.Nonempty) {S : Set α} :
    (circuitOn C).Spanning S ↔ ∃ e, insert e S = C := by
  simp_rw [spanning_iff_exists_isBase_subset', circuitOn_ground, circuitOn_isBase_iff hC]
  constructor
  · rintro ⟨⟨B, ⟨e, heB, rfl⟩, hBS⟩, hSC⟩
    exact ⟨e, subset_antisymm (insert_subset (by simp) hSC) (insert_subset_insert hBS)⟩
  rintro ⟨e, rfl⟩
  exact ⟨⟨S \ {e}, ⟨e, by simp⟩, diff_subset⟩, subset_insert _ _⟩

lemma ground_isCircuit_iff [M.Nonempty] : M.IsCircuit M.E ↔ M = circuitOn M.E := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_isCircuit rfl <| fun C hC ↦ ?_
    rw [circuitOn_isCircuit_iff h.nonempty]
    exact ⟨fun h' ↦ h'.eq_of_subset_isCircuit h hC, by rintro rfl; assumption⟩
  rw [h]
  exact circuitOn_ground_isCircuit M.ground_nonempty

lemma eq_circuitOn_of_ground_isCircuit (h : M.IsCircuit M.E) : ∃ E, M = circuitOn E :=
  have : M.Nonempty := ⟨_, h.subset_ground h.nonempty.some_mem⟩
  ⟨M.E, ground_isCircuit_iff.1 h⟩

lemma isCircuit_iff_restr_eq_circuitOn (hCne : C.Nonempty) (hC : C ⊆ M.E := by aesop_mat) :
    M.IsCircuit C ↔ M ↾ C = circuitOn C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_isCircuit rfl fun C' hC' ↦ ?_
    rw [restrict_isCircuit_iff h.subset_ground, circuitOn_isCircuit_iff h.nonempty,
      and_iff_left (show C' ⊆ C from hC')]
    exact ⟨fun h' ↦ h'.eq_of_subset_isCircuit h hC', fun h' ↦ by rwa [h']⟩
  have h' := restrict_isCircuit_iff hC (C := C)
  rwa [and_iff_left Subset.rfl, h, iff_true_intro (circuitOn_ground_isCircuit hCne), true_iff] at h'

lemma IsCircuit.restrict_eq_circuitOn (hC : M.IsCircuit C) : M ↾ C = circuitOn C := by
  rwa [← isCircuit_iff_restr_eq_circuitOn hC.nonempty]

@[simp]
lemma circuitOn_freeLift (C : Set α) : (circuitOn C).freeLift = freeOn C := by
  obtain rfl | hne := C.eq_empty_or_nonempty; simp
  refine ext_indep rfl fun I (hIE : I ⊆ C) ↦ ?_
  obtain rfl | hIne := I.eq_empty_or_nonempty; simp
  simp only [freeLift_indep_iff, hIne, circuitOn_ground, mem_inter_iff, circuitOn_indep_iff hne,
    ssubset_iff_subset_ne, diff_singleton_subset_iff, ne_eq, forall_const, freeOn_indep_iff]
  refine ⟨by grind, fun h ↦ ?_⟩
  obtain ⟨f, hfI⟩ := hIne
  exact ⟨f, by grind⟩

@[simp]
lemma circuitOn_singleton (e : α) : circuitOn {e} = loopyOn {e} := by
  refine ext_indep rfl ?_
  suffices (circuitOn {e}).IsLoop e by simpa [-subset_singleton_iff, subset_singleton_iff_eq]
  rw [← singleton_isCircuit, circuitOn_isCircuit_iff]
  simp


end circuitOn

variable {I J B B' : Set α} {e f : α}

lemma IsBase.isBase_of_indep_of_finDiff (hB : M.IsBase B) (hI : M.Indep I) (hBI : FinDiff B I) :
    M.IsBase I := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hfin' : FinDiff B B' := by
    rw [finDiff_iff, hB'.encard_diff_comm hB, and_iff_left rfl]
    exact hBI.diff_finite.subset (diff_subset_diff_right hIB')
  rwa [(hBI.symm.trans hfin').eq_of_subset hIB']

lemma IsBase.isBase_of_spanning_of_finDiff {S : Set α} (hB : M.IsBase B) (hS : M.Spanning S)
    (hBS : FinDiff B S) : M.IsBase S := by
  rw [← M.dual_dual, dual_isBase_iff]
  exact hB.compl_isBase_dual.isBase_of_indep_of_finDiff hS.compl_coindep <|
    hBS.diff_right hB.subset_ground hS.subset_ground
/--
A `TruncateFamily` is a collection of nonempty bases of `M` such that,
for any two bases of `M` that both contain bases for a common hyperplane,
either both or neither belongs to the collection.
If `M` has finite rank or corank, the collection of all bases is the only `TruncateFamily`,
but in general there can be others.

Given such a collection `T`, we can form a new matroid by making all the sets in `T`
into spanning circuits instead of bases.
In the special case where `T` contains all the bases of `M`, this operation is just truncation.
-/
@[ext] structure TruncateFamily (M : Matroid α) where
  ToTruncate : Set α → Prop
  forall_nonempty : ∀ ⦃B⦄, ToTruncate B → B.Nonempty
  forall_isBase : ∀ ⦃B⦄, ToTruncate B → M.IsBase B
  toTruncate_of_toTruncate : ∀ ⦃B B' e e'⦄, ToTruncate B → e ∈ B → M.IsBase B' → e' ∈ B' →
      M.closure (B \ {e}) = M.closure (B' \ {e'}) → ToTruncate B'

namespace TruncateFamily

variable {T : M.TruncateFamily}

lemma ToTruncate.isBase (hB : T.ToTruncate B) : M.IsBase B :=
  T.forall_isBase hB

lemma ToTruncate.nonempty (hB : T.ToTruncate B) : B.Nonempty :=
  T.forall_nonempty hB

lemma ToTruncate.toTruncate_of_closure (hI : T.ToTruncate (insert e I)) (heI : e ∉ I) (hfJ : f ∉ J)
    (hJ : M.Indep (insert f J)) (hIJ : I ⊆ M.closure J) : T.ToTruncate (insert f J) := by
  have hhp : M.IsHyperplane (M.closure I) := by
    simpa [heI] using hI.isBase.isHyperplane_of_closure_diff_singleton (mem_insert _ _)
  replace hJ := show M.IsBase (insert f J) by
    refine hJ.isBase_of_ground_subset_closure ?_
    have hssu : M.closure I ⊂ M.closure (insert f J) := by
      refine (M.closure_subset_closure_of_subset_closure hIJ).trans_ssubset ?_
      exact hJ.closure_ssubset_closure (ssubset_insert hfJ)
    rw [← hhp.closure_eq_ground_of_ssuperset hssu, closure_closure]
  refine T.toTruncate_of_toTruncate hI (mem_insert _ _) hJ (mem_insert _ _) ?_

  suffices hJI : J ⊆ M.closure I by simp [(M.closure_subset_closure_of_subset_closure hIJ).antisymm
    (M.closure_subset_closure_of_subset_closure hJI), heI, hfJ]
  have hJE := (subset_insert _ _).trans hJ.subset_ground
  refine fun x hxJ ↦ by_contra fun hxI ↦ ?_
  have hcl := (hhp.closure_insert_eq_univ ⟨hJE hxJ, hxI⟩).symm.subset
  rw [closure_insert_closure_eq_closure_insert] at hcl
  replace hcl := hcl.trans (M.closure_subset_closure (insert_subset_insert hIJ))
  rw [closure_insert_closure_eq_closure_insert, insert_eq_of_mem hxJ] at hcl
  have hcl' := hJ.indep.closure_diff_singleton_ssubset (mem_insert _ _)
  simp only [mem_singleton_iff, insert_diff_of_mem, hfJ, not_false_eq_true,
    diff_singleton_eq_self, hJ.closure_eq] at hcl'
  exact hcl'.not_subset hcl

lemma ToTruncate.exchange (hB : T.ToTruncate B) (heB : e ∉ B) (hfB : f ∈ B)
    (h_indep : M.Indep (insert e (B \ {f}))) : T.ToTruncate (insert e (B \ {f})) := by
  have hef : e ≠ f := by rintro rfl; contradiction
  have h_isBase := hB.isBase.isBase_of_indep_of_finDiff h_indep
    (isExchange_diff_insert hfB heB).finDiff
  exact T.toTruncate_of_toTruncate hB hfB h_isBase (mem_insert _ _)
    <| by simp [diff_singleton_eq_self (show e ∉ B \ {f} by simp [heB, hef])]

lemma ToTruncate.of_exchange (hB' : T.ToTruncate (insert e (B \ {f})))
    (heB : e ∉ B) (hfB : f ∈ B) (hB : M.IsBase B) : T.ToTruncate B := by
  have hef : e ≠ f := by rintro rfl; contradiction
  have hrw : B = insert f (insert e (B \ {f}) \ {e}) := by
    simp [diff_singleton_eq_self (show e ∉ B \ {f} by simp [hef, heB]), insert_eq_of_mem hfB]
  rw [hrw]
  replace hB := hB.indep
  exact hB'.exchange (by simp [hef.symm]) (mem_insert _ _) <| (by rwa [← hrw])

lemma ToTruncate.finDiff {B B' : Set α} (hB : T.ToTruncate B) (hB' : M.IsBase B')
    (hdiff : FinDiff B B') : T.ToTruncate B' := by
  obtain h | h := (B \ B').eq_empty_or_nonempty
  · rw [diff_eq_empty] at h
    rwa [← hB.isBase.eq_of_subset_isBase hB' h]
  obtain ⟨f, hf⟩ := hdiff.symm.nonempty_of_nonempty h
  obtain ⟨e, he, heB⟩ := hB'.exchange hB.isBase hf
  have hlt : ((insert e (B' \ {f})) \ B).encard < (B' \ B).encard := by
    rw [insert_diff_of_mem _ he.1, diff_diff_comm, ← encard_diff_singleton_add_one hf,
      ENat.lt_add_one_iff]
    simpa using hdiff.symm.diff_finite.diff
  have hfd : FinDiff B (insert e (B' \ {f})) :=
    hdiff.trans_exchange <| isExchange_diff_insert hf.1 he.2
  exact (TruncateFamily.ToTruncate.finDiff hB heB hfd).of_exchange he.2 hf.1 hB'
termination_by (B' \ B).encard

def Indep (T : M.TruncateFamily) (I : Set α) : Prop := M.Indep I ∧ ¬ T.ToTruncate I

lemma indep_eq : T.Indep = fun I ↦ M.Indep I ∧ ¬ T.ToTruncate I := rfl

def IsBase (T : M.TruncateFamily) (B : Set α) : Prop :=
  (M.IsBase B ∧ ¬ T.ToTruncate B) ∨ (∃ e ∈ M.E \ B, T.ToTruncate (insert e B))

lemma isBase_eq :
    T.IsBase =
    fun B ↦ (M.IsBase B ∧ ¬ T.ToTruncate B) ∨ (∃ e ∈ M.E \ B, T.ToTruncate (insert e B)) :=
  rfl

lemma isBase_eq' :
    T.IsBase = fun B ↦ (M.IsBase B ∧ ¬ T.ToTruncate B) ∨ (∃ e ∉ B, T.ToTruncate (insert e B)) := by
  ext B
  refine or_congr_right ⟨fun ⟨e, he⟩ ↦ ⟨e, he.1.2, he.2⟩, fun ⟨e, he⟩ ↦ ⟨e, ⟨?_, he.1⟩, he.2⟩⟩
  exact he.2.isBase.subset_ground (mem_insert _ _)

lemma ToTruncate.isBase_diff_singleton (hBt : T.ToTruncate B) (heB : e ∈ B) : T.IsBase (B \ {e}) :=
  .inr ⟨e, by simpa [hBt.isBase.subset_ground heB, heB] ⟩

lemma ToTruncate.isBase_of_insert (hBt : T.ToTruncate (insert e B)) (heB : e ∉ B) : T.IsBase B := by
  simpa [heB] using hBt.isBase_diff_singleton (mem_insert _ _)

lemma IsBase.indep (hB : T.IsBase B) : T.Indep B := by
  obtain h | ⟨e, he, heB⟩ := hB
  · exact ⟨h.1.indep, h.2⟩
  refine ⟨heB.isBase.indep.subset <| subset_insert _ _, fun hBt ↦ ?_⟩
  rw [hBt.isBase.eq_of_subset_isBase heB.isBase (subset_insert _ _)] at he
  simp at he

lemma IsBase.exists_toTruncate_insert (hB : T.IsBase B) (hBM : ¬ M.IsBase B) :
    ∃ e ∈ M.E \ B, T.ToTruncate (insert e B) := by
  rwa [TruncateFamily.IsBase, iff_false_intro hBM, false_and, false_or] at hB

lemma Indep.indep (hI : T.Indep I) : M.Indep I :=
  hI.1

lemma _root_.Matroid.IsBase.partialTruncateBase_iff (hB : M.IsBase B) :
    T.IsBase B ↔ ¬ T.ToTruncate B :=
  ⟨fun h h' ↦ h.indep.2 h', fun h ↦ .inl ⟨hB, h⟩⟩

lemma _root_.Matroid.IsBase.partialTruncateBase (hB : M.IsBase B) (hBt : ¬ T.ToTruncate B) :
    T.IsBase B :=
  .inl ⟨hB, hBt⟩

lemma Indep.subset (hI : T.Indep I) (hJI : J ⊆ I) : T.Indep J :=
  ⟨hI.1.subset hJI, fun hT ↦ hI.2 <| by rwa [← hT.isBase.eq_of_subset_indep hI.indep hJI]⟩

lemma maximal_indep_eq : Maximal (T.Indep) = T.IsBase := by
  ext B
  rw [maximal_iff_forall_insert (fun _ _ ↦ TruncateFamily.Indep.subset)]
  by_cases hB : M.IsBase B
  · rw [hB.partialTruncateBase_iff, TruncateFamily.Indep, and_comm (a := M.Indep B),
      and_assoc, and_iff_left_iff_imp, and_iff_right hB.indep]
    intro h x hxB hi
    rw [hB.eq_of_subset_indep hi.1  (subset_insert _ _)] at hxB
    simp at hxB
  simp only [TruncateFamily.IsBase, hB, false_and, mem_diff, false_or]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨B₀, hB₀⟩ := M.exists_isBase
    obtain ⟨e, ⟨heB₀, heB⟩, heB'⟩ := h.1.1.exists_insert_of_not_isBase hB hB₀
    exact ⟨e, ⟨hB₀.subset_ground heB₀, heB⟩, by_contra fun ht ↦ h.2 e heB ⟨heB', ht⟩⟩
  rintro ⟨e, ⟨heE, heB⟩, ht⟩
  refine ⟨(ht.isBase_of_insert heB).indep, fun x hx hxB ↦ hxB.2 ?_⟩
  have hex : e ≠ x := by rintro rfl; exact hxB.2 ht
  simpa [heB] using ht.exchange (e := x) (f := e) (by simp [hx, hex.symm]) (by simp)
    (by simpa [heB] using hxB.1)

/-- The `Matroid` formed by truncating all the bases in `T`. -/
@[simps! E] protected def matroid (T : M.TruncateFamily) :
    Matroid α := IndepMatroid.matroid <| IndepMatroid.mk
  (E := M.E)
  (Indep := T.Indep)
  (indep_empty := ⟨M.empty_indep, fun h ↦ by simpa using h.nonempty⟩)
  (indep_subset := fun _ _ ↦ Indep.subset)
  (indep_aug := by
    simp_rw [maximal_indep_eq]
    intro I B ⟨hI, hIt⟩ hItb hB
    have hInotbase : ¬ M.IsBase I := fun hIb ↦ hItb (.inl ⟨hIb, hIt⟩)

    by_cases hBM : M.IsBase B
    · obtain ⟨e, heBI, heI⟩ := hI.exists_insert_of_not_isBase hInotbase hBM
      refine ⟨e, heBI, heI, fun heIt ↦ hItb ?_⟩
      simpa [heBI.2] using heIt.isBase_diff_singleton <| mem_insert _ _
    by_cases hcon : B ⊆ M.closure I
    · exfalso
      obtain ⟨e, he, heB⟩ := hB.exists_toTruncate_insert hBM
      obtain ⟨B₀, hB₀⟩ := M.exists_isBase
      obtain ⟨f, ⟨-, hf⟩, hfI⟩ := hI.exists_insert_of_not_isBase hInotbase hB₀
      exact hItb <| (heB.toTruncate_of_closure he.2 hf hfI hcon).isBase_of_insert hf
    simp only [subset_def, not_forall, exists_prop] at hcon
    obtain ⟨e, heB, he⟩ := hcon
    have heI : e ∉ I := notMem_subset (M.subset_closure _) he
    rw [hI.notMem_closure_iff_of_notMem heI (hB.indep.indep.subset_ground heB)] at he
    exact ⟨e, ⟨heB, heI⟩, he, fun hT ↦ hItb (hT.isBase_of_insert heI)⟩ )

  (indep_maximal := by
    intro X hX I hI hIX
    obtain ⟨J, hJX, hIJ⟩ := hI.indep.subset_isBasis_of_subset hIX
    have h_mono : ∀ ⦃s t : Set α⦄, T.Indep t ∧ t ⊆ X → s ⊆ t → T.Indep s ∧ s ⊆ X :=
      fun I J hI hIJ ↦ ⟨⟨hI.1.1.subset hIJ, fun hI' ↦ (hI.1.subset hIJ).2 hI'⟩, hIJ.trans hI.2⟩

    simp only [maximal_iff_forall_insert h_mono, insert_subset_iff, not_and]
    by_cases hJ : T.ToTruncate J
    · obtain ⟨e, he⟩ := exists_of_ssubset (hIJ.ssubset_of_ne <| by rintro rfl; exact hI.2 hJ)

      refine ⟨J \ {e}, subset_diff_singleton hIJ he.2, ?_⟩
      suffices ∀ (x : α), (x ∈ J → x = e) → T.Indep (insert x (J \ {e})) → x ∉ X by
        simpa [(hJ.isBase_diff_singleton he.1).indep, diff_singleton_subset_iff,
          show J ⊆ insert e X from hJX.subset.trans (subset_insert _ _)]
      refine fun x hxJ hxi hxX ↦ hxi.2 <| hJ.exchange (fun hxJ' ↦ hxi.2 ?_) he.1 hxi.1
      simpa [hxJ hxJ', he.1]

    suffices ∀ x ∉ J, T.Indep (insert x J) → x ∉ X from
      ⟨J, by simpa [hIJ, hJX.subset, show T.Indep J from ⟨hJX.indep, hJ⟩]⟩

    intro x hxJ hi hxX
    rw [hJX.eq_of_subset_indep hi.1 (subset_insert _ _) (insert_subset hxX hJX.subset)] at hxJ
    simp at hxJ )

  (subset_ground  := fun _ hI ↦ hI.1.subset_ground)

@[simp] lemma matroid_indep_eq : T.matroid.Indep = T.Indep := rfl

@[simp] lemma matroid_isBase_eq : T.matroid.IsBase = T.IsBase := by
  simp [funext_iff, ← maximal_indep_eq, isBase_iff_maximal_indep, Maximal]

lemma matroid_closure_eq_closure (X : Set α) (hX : X ⊆ M.E) (hX : ¬ T.matroid.Spanning X) :
    T.matroid.closure X = M.closure X := by
  obtain ⟨I, hI'⟩ := T.matroid.exists_isBasis X
  have hi := hI'.indep
  simp only [matroid_indep_eq, indep_eq] at hi

  have aux : ∀ x, ¬ T.ToTruncate (insert x I) := by
    refine fun x ht ↦ hX ?_
    by_cases hxI : x ∈ I
    · exact (hi.2 (by simpa [hxI] using ht)).elim
    have hb := ht.isBase_of_insert hxI
    rw [← T.matroid_isBase_eq] at hb
    exact hb.spanning.superset hI'.subset

  have hI : M.IsBasis I X
  · simp_rw [hi.1.isBasis_iff_forall_insert_dep hI'.subset, dep_iff, insert_subset_iff,
      and_iff_left hi.1.subset_ground]
    exact fun e he ↦ ⟨fun hi ↦ (hI'.insert_dep he).not_indep ⟨hi, aux _⟩,
      (hI'.subset_ground he.1)⟩

  rw [← hI'.closure_eq_closure, ← hI.closure_eq_closure, Set.ext_iff]
  simp [hI'.indep.mem_closure_iff', T.indep_eq, hI.indep.mem_closure_iff', aux]

/-- The `TruncateFamily` consisting of all bases of `M`. This corresponds to the truncation of `M`.
Empty if `M` has rank zero for technical reasons. -/
@[simps] def top (M : Matroid α) : M.TruncateFamily where
  ToTruncate B := M.IsBase B ∧ B.Nonempty
  forall_nonempty B h := h.2
  forall_isBase B h := h.1
  toTruncate_of_toTruncate := by tauto

@[simp] lemma matroid_top : (top M).matroid = M.truncate := by
  refine ext_isBase rfl ?_
  obtain h | h := M.eq_loopyOn_or_rankPos
  · rw [h]
    simp [(top _).isBase_eq', top_ToTruncate, nonempty_iff_ne_empty]

  suffices ∀ ⦃B : Set α⦄, B ⊆ M.E → M.IsBase B → ¬B.Nonempty → ∃ e ∉ B, M.IsBase (insert e B) by
    simpa +contextual [(top M).isBase_eq', top_ToTruncate, truncate_isBase_iff]

  exact fun B _ hB hne ↦ (hne hB.nonempty).elim

@[simps] def bot (M : Matroid α) : M.TruncateFamily where
  ToTruncate B := False
  forall_nonempty B h := h.elim
  forall_isBase B h := h.elim
  toTruncate_of_toTruncate := by tauto

@[simp] lemma matroid_bot : (bot M).matroid = M :=
  ext_isBase rfl <| by simp [(bot _).isBase_eq]

lemma eq_top_or_bot_of_rankFinite [RankFinite M] (T : M.TruncateFamily) :
    T = top M ∨ T = bot M := by
  obtain h | ⟨B₀, hB₀⟩ := em' (∃ B, T.ToTruncate B)
  · right
    push_neg at h
    ext
    simp [h]
  left
  ext B
  simp only [top_ToTruncate]
  refine ⟨fun h ↦ ⟨h.isBase, h.nonempty⟩, fun ⟨hB, hBne⟩ ↦ ?_⟩
  exact hB₀.finDiff hB <| finDiff_iff.2 ⟨hB₀.isBase.finite.diff, hB₀.isBase.encard_diff_comm hB⟩

lemma eq_top_or_bot_of_rankFinite_dual [RankFinite M✶] (T : M.TruncateFamily) :
    T = top M ∨ T = bot M := by
  obtain h | ⟨B₀, hB₀⟩ := em' (∃ B, T.ToTruncate B)
  · right
    push_neg at h
    ext
    simp [h]
  left
  ext B
  simp only [top_ToTruncate]
  refine ⟨fun h ↦ ⟨h.isBase, h.nonempty⟩, fun ⟨hB, hBne⟩ ↦ ?_⟩
  refine hB₀.finDiff hB <| finDiff_iff.2 ⟨?_, ?_⟩
  · exact hB.compl_isBase_dual.finite.subset <| diff_subset_diff_left hB₀.isBase.subset_ground
  convert hB.compl_isBase_dual.encard_diff_comm hB₀.isBase.compl_isBase_dual using 2
  · rw [diff_diff_right, diff_eq_empty.2 diff_subset, empty_union, inter_comm,
      inter_diff_distrib_left, inter_eq_self_of_subset_left hB₀.isBase.subset_ground,
      diff_self_inter]
  rw [diff_diff_right, diff_eq_empty.2 diff_subset, empty_union, inter_comm,
      inter_diff_distrib_left, inter_eq_self_of_subset_left hB.subset_ground, diff_self_inter]

end TruncateFamily

lemma truncate_closure_eq_of_not_spanning {X : Set α} (hXE : X ⊆ M.E := by aesop_mat)
    (hs : ¬ M.truncate.Spanning X) : M.truncate.closure X = M.closure X := by
  rw [← TruncateFamily.matroid_top] at hs ⊢
  rwa [TruncateFamily.matroid_closure_eq_closure _ hXE]
