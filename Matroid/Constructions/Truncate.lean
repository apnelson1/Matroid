import Matroid.Extension
import Matroid.ForMathlib.FinDiff

variable {α : Type*} {M : Matroid α} {E I B : Set α} {k : ℕ∞}

namespace Matroid

open Set

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
      (encard_insert_of_not_mem he.2).trans_le ((Order.add_one_le_of_lt hIJ).trans hJc)⟩)
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
  ext_indep rfl (by simp [truncateTo])

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

theorem truncate_eq_self_of_rk_le (h_rk : M.erk ≤ k) : M.truncateTo k = M := by
  refine ext_indep truncateTo_ground_eq (fun I _ ↦ ?_)
  rw [truncateTo_indep_iff, and_iff_left_iff_imp]
  exact fun hi ↦ hi.encard_le_erk.trans h_rk

theorem truncateTo_base_iff {k : ℕ} (h_rk : k ≤ M.erk) :
    (M.truncateTo k).Base B ↔ M.Indep B ∧ B.encard = k := by
  simp_rw [base_iff_maximal_indep, truncateTo_indep_eq, maximal_subset_iff, and_assoc,
    and_congr_right_iff, and_imp]
  refine fun hi ↦ ⟨fun ⟨hle, hmax⟩ ↦ ?_, fun h ↦ ⟨h.le, fun J _ hcard hBJ ↦ ?_⟩⟩
  · obtain ⟨B', hB', hBB'⟩ := hi.exists_base_superset
    obtain ⟨J, hBJ, hJB', h'⟩ := exists_superset_subset_encard_eq hBB' hle (by rwa [hB'.encard])
    rwa [hmax (hB'.indep.subset hJB') h'.le hBJ]
  exact (finite_of_encard_le_coe hcard).eq_of_subset_of_encard_le hBJ <| hcard.trans_eq h.symm

theorem truncate_base_iff_of_finiteRk [FiniteRk M] (h_rk : k ≤ M.erk) :
    (M.truncateTo k).Base B ↔ M.Indep B ∧ B.encard = k := by
  lift k to ℕ using (h_rk.trans_lt M.erk_lt_top).ne; rwa [truncateTo_base_iff]

instance truncateTo.finite [Matroid.Finite M] : Matroid.Finite (M.truncateTo k) :=
⟨ by simp [ground_finite M] ⟩

instance truncateTo.finiteRk {k : ℕ} : FiniteRk (M.truncateTo k) := by
  obtain ⟨B, hB⟩ := (M.truncateTo k).exists_base
  refine ⟨B, hB, (le_or_lt M.erk k).elim (fun h ↦ ?_) (fun h ↦ ?_)⟩
  · rw [truncate_eq_self_of_rk_le h] at hB
    rw [← encard_lt_top_iff, hB.encard]
    exact h.trans_lt (WithTop.coe_lt_top _)
  rw [truncateTo_base_iff h.le] at hB
  rw [← encard_lt_top_iff, hB.2]
  apply WithTop.coe_lt_top

theorem Indep.of_truncateTo (h : (M.truncateTo k).Indep I) : M.Indep I := by
  rw [truncateTo_indep_iff] at h; exact h.1

theorem Indep.encard_le_of_truncateTo (h : (M.truncateTo k).Indep I) : I.encard ≤ k :=
  (truncateTo_indep_iff.mp h).2

theorem truncateTo_er_eq (M : Matroid α) (k : ℕ∞) (X : Set α) :
    (M.truncateTo k).er X = min (M.er X) k := by
  simp_rw [le_antisymm_iff, le_er_iff, er_le_iff, truncateTo_indep_iff]
  obtain ⟨I, hI⟩ := M.exists_basis' X
  refine ⟨?_, ?_⟩
  · intro J hJX hJi
    exact le_min (hJi.1.encard_le_er_of_subset hJX) hJi.2
  obtain ⟨I₀, hI₀, hI₀ss⟩ := exists_subset_encard_eq (min_le_of_left_le (b := k) hI.encard.symm.le)
  exact ⟨_, hI₀.trans hI.subset, ⟨hI.indep.subset hI₀, hI₀ss.trans_le (min_le_right _ _)⟩, hI₀ss⟩

end truncateTo

section truncate

/-- The matroid on `M.E` whose independent sets are the independent nonbases of `M`. -/
def truncate (M : Matroid α) := Matroid.ofExistsMatroid
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ (M.Base I → I = ∅))
  (hM := by
    refine ⟨M.projectBy (ModularCut.principal M M.E), rfl, fun I ↦ ?_⟩
    obtain (hM | hM) := M.eq_loopyOn_or_rkPos
    · rw [hM]; simp [ModularCut.eq_top_iff, Subset.rfl]
    suffices M.Indep I → (¬M.E ⊆ M.closure I ↔ M.Base I → I = ∅) by simpa [M.principal_ground_ne_top]
    refine fun hI ↦ ⟨fun h hIb ↦ by simp [hIb.closure_eq, Subset.rfl] at h, fun h hss ↦ ?_⟩
    have hIb := hI.base_of_ground_subset_closure hss
    exact hIb.nonempty.ne_empty (h hIb))

@[simp] lemma truncate_ground_eq : M.truncate.E = M.E := rfl

lemma truncate_indep_iff' : M.truncate.Indep I ↔ M.Indep I ∧ (M.Base I → I = ∅) := Iff.rfl

@[simp] lemma truncate_indep_iff [M.RkPos] : M.truncate.Indep I ↔ M.Indep I ∧ ¬ M.Base I := by
  simp only [truncate_indep_iff', and_congr_right_iff]
  exact fun _ ↦ ⟨fun h hB ↦ hB.nonempty.ne_empty (h hB), fun h hB ↦ by contradiction⟩

@[simp] lemma truncate_loopyOn_eq {E : Set α} : (loopyOn E).truncate = loopyOn E := by
  simp (config := {contextual := true}) [truncate, ModularCut.principal, eq_loopyOn_iff]

lemma truncate_base_iff [M.RkPos] : M.truncate.Base B ↔ ∃ e ∉ B, M.Base (insert e B) := by
  refine ⟨fun h ↦ ?_, fun ⟨e, he, hBe⟩ ↦ ?_⟩
  · obtain ⟨hB, hBb⟩ := truncate_indep_iff.1 h.indep
    obtain ⟨B', hB', hBB'⟩ := hB.exists_base_superset
    obtain ⟨e, heB', heB⟩ := exists_of_ssubset (hBB'.ssubset_of_ne (by rintro rfl; contradiction))
    refine ⟨e, heB, ?_⟩
    rwa [h.eq_of_subset_indep ?_ (subset_diff_singleton hBB' heB), insert_diff_singleton,
      insert_eq_of_mem heB']
    rw [truncate_indep_iff]
    exact ⟨hB'.indep.subset diff_subset, hB'.not_base_of_ssubset <| diff_singleton_sSubset.mpr heB'⟩
  refine Indep.base_of_forall_insert ?_ ?_
  · rw [truncate_indep_iff]
    exact ⟨hBe.indep.subset (subset_insert _ _), hBe.not_base_of_ssubset (ssubset_insert he)⟩
  simp only [truncate_ground_eq, mem_diff, truncate_indep_iff, not_and, not_not, and_imp]
  exact fun f _ hfB hfBi ↦ insert_base_of_insert_indep he hfB hBe hfBi

end truncate

section circuitOn

variable {C : Set α}

/-- The matroid on `E` whose ground set is a circuit. Empty if `E = ∅`. -/
def circuitOn (C : Set α) := (freeOn C).truncate

@[simp] lemma circuitOn_ground : (circuitOn C).E = C := rfl

lemma circuitOn_indep_iff (hC : C.Nonempty) : (circuitOn C).Indep I ↔ I ⊂ C := by
  have := freeOn_rkPos hC
  simp [circuitOn, truncate_indep_iff, ssubset_iff_subset_ne]

lemma circuitOn_dep_iff (hC : C.Nonempty) {D : Set α} : (circuitOn C).Dep D ↔ D = C := by
  simp only [Dep, circuitOn_indep_iff hC, ssubset_iff_subset_ne, ne_eq, not_and, not_not,
    circuitOn_ground]
  exact ⟨fun h ↦ h.1 h.2, by rintro rfl; simp [Subset.rfl]⟩

lemma circuitOn_base_iff (hC : C.Nonempty) : (circuitOn C).Base B ↔ ∃ e ∉ B, insert e B = C := by
  have _ := freeOn_rkPos hC; simp [circuitOn, truncate_base_iff]

lemma circuitOn_ground_circuit (hC : C.Nonempty) : (circuitOn C).Circuit C := by
  simp [circuit_iff_forall_ssubset, circuitOn_dep_iff hC, circuitOn_indep_iff hC]

lemma circuitOn_circuit_iff (hC : C.Nonempty) {C' : Set α} : (circuitOn C).Circuit C' ↔ C' = C := by
  refine ⟨fun h ↦ h.eq_of_subset_circuit (circuitOn_ground_circuit hC) h.subset_ground, ?_⟩
  rintro rfl
  exact circuitOn_ground_circuit hC

lemma ground_circuit_iff [M.Nonempty] : M.Circuit M.E ↔ M = circuitOn M.E := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_circuit rfl <| fun C hC ↦ ?_
    rw [circuitOn_circuit_iff h.nonempty]
    exact ⟨fun h' ↦ h'.eq_of_subset_circuit h hC, by rintro rfl; assumption⟩
  rw [h]
  exact circuitOn_ground_circuit M.ground_nonempty

lemma circuit_iff_restr_eq_circuitOn (hCne : C.Nonempty) (hC : C ⊆ M.E := by aesop_mat) :
    M.Circuit C ↔ M ↾ C = circuitOn C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_circuit rfl fun C' hC' ↦ ?_
    rw [restrict_circuit_iff h.subset_ground, circuitOn_circuit_iff h.nonempty,
      and_iff_left (show C' ⊆ C from hC')]
    exact ⟨fun h' ↦ h'.eq_of_subset_circuit h hC', fun h' ↦ by rwa [h']⟩
  have h' := restrict_circuit_iff hC (C := C)
  rwa [and_iff_left Subset.rfl, h, iff_true_intro (circuitOn_ground_circuit hCne), true_iff] at h'

end circuitOn

section Partial

variable {I J B B' : Set α} {e f : α}

lemma Base.base_of_indep_of_finDiff (hB : M.Base B) (hI : M.Indep I) (hBI : FinDiff B I) :
    M.Base I := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_base_superset
  have hfin' : FinDiff B B' := by
    rw [finDiff_iff, hB'.encard_diff_comm hB, and_iff_left rfl]
    exact hBI.diff_left_finite.subset (diff_subset_diff_right hIB')
  rwa [(hBI.symm.trans hfin').eq_of_subset hIB']

@[ext] structure PartialTruncateCollection (M : Matroid α) where
  ToTruncate : Set α → Prop
  forall_nonempty : ∀ ⦃B⦄, ToTruncate B → B.Nonempty
  forall_base : ∀ ⦃B⦄, ToTruncate B → M.Base B
  toTruncate_of_toTruncate : ∀ ⦃B B' e e'⦄, ToTruncate B → e ∈ B → M.Base B' → e' ∈ B' →
      M.closure (B \ {e}) = M.closure (B' \ {e'}) → ToTruncate B'

variable {T : M.PartialTruncateCollection}

lemma PartialTruncateCollection.ToTruncate.base (hB : T.ToTruncate B) : M.Base B :=
  T.forall_base hB

lemma PartialTruncateCollection.ToTruncate.nonempty (hB : T.ToTruncate B) : B.Nonempty :=
  T.forall_nonempty hB


lemma PartialTruncateCollection.ToTruncate.toTruncate_of_closure (hI : T.ToTruncate (insert e I))
    (heI : e ∉ I) (hfJ : f ∉ J) (hJ : M.Indep (insert f J)) (hIJ : I ⊆ M.closure J) :
    T.ToTruncate (insert f J) := by
  have hhp : M.Hyperplane (M.closure I) := by
    simpa [heI] using hI.base.hyperplane_of_closure_diff_singleton (mem_insert _ _)
  replace hJ := show M.Base (insert f J) by
    refine hJ.base_of_ground_subset_closure ?_
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

lemma PartialTruncateCollection.ToTruncate.exchange (hB : T.ToTruncate B) (heB : e ∉ B)
    (hfB : f ∈ B) (h_base : M.Base (insert e (B \ {f}))) : T.ToTruncate (insert e (B \ {f})) := by
  have hef : e ≠ f := by rintro rfl; contradiction
  exact T.toTruncate_of_toTruncate hB hfB h_base (mem_insert _ _)
    <| by simp [diff_singleton_eq_self (show e ∉ B \ {f} by simp [heB, hef])]

lemma PartialTruncateCollection.ToTruncate.of_exchange (hB' : T.ToTruncate (insert e (B \ {f})))
    (heB : e ∉ B) (hfB : f ∈ B) (hB : M.Base B) : T.ToTruncate B := by
  have hef : e ≠ f := by rintro rfl; contradiction
  have hrw : B = insert f (insert e (B \ {f}) \ {e}) := by
    simp [diff_singleton_eq_self (show e ∉ B \ {f} by simp [hef, heB]), insert_eq_of_mem hfB]
  rw [hrw]
  exact hB'.exchange (by simp [hef.symm]) (mem_insert _ _) <| (by rwa [← hrw])

lemma PartialTruncateCollection.ToTruncate.finDiff {B B' : Set α} (hB : T.ToTruncate B)
    (hB' : M.Base B') (hdiff : FinDiff B B') : T.ToTruncate B' := by
  obtain h | h := (B \ B').eq_empty_or_nonempty
  · rw [diff_eq_empty] at h
    rwa [← hB.base.eq_of_subset_base hB' h]
  obtain ⟨f, hf⟩ := hdiff.symm.nonempty_of_nonempty h
  obtain ⟨e, he, heB⟩ := hB'.exchange hB.base hf
  have hlt : ((insert e (B' \ {f})) \ B).encard < (B' \ B).encard := by
    rw [insert_diff_of_mem _ he.1, diff_diff_comm, ← encard_diff_singleton_add_one hf,
      ENat.lt_add_one_iff]
    simpa using hdiff.diff_right_finite.diff {f}
  have hfd : FinDiff B (insert e (B' \ {f})) := hdiff.trans (finDiff_exchange hf.1 he.2)
  exact (PartialTruncateCollection.ToTruncate.finDiff hB heB hfd).of_exchange he.2 hf.1 hB'
termination_by (B' \ B).encard

def PartialTruncateCollection.Indep (T : M.PartialTruncateCollection) (I : Set α) : Prop :=
  M.Indep I ∧ ¬ T.ToTruncate I

def PartialTruncateCollection.Base (T : M.PartialTruncateCollection) (B : Set α) : Prop :=
  (M.Base B ∧ ¬ T.ToTruncate B) ∨ (∃ e ∈ M.E \ B, T.ToTruncate (insert e B))

lemma PartialTruncateCollection.ToTruncate.base_diff_singleton (hBt : T.ToTruncate B)
    (heB : e ∈ B) : T.Base (B \ {e}) :=
  .inr ⟨e, by simpa [hBt.base.subset_ground heB, heB] ⟩

lemma PartialTruncateCollection.ToTruncate.base_of_insert (hBt : T.ToTruncate (insert e B))
  (heB : e ∉ B) : T.Base B := sorry

lemma PartialTruncateCollection.ToTruncate.not_base (hBt : T.ToTruncate B) : ¬ T.Base B := by
  sorry

lemma PartialTruncateCollection.Base.indep (hB : T.Base B) : T.Indep B := by
  obtain h | ⟨e, he, heB⟩ := hB
  · exact ⟨h.1.indep, h.2⟩
  refine ⟨heB.base.indep.subset <| subset_insert _ _, fun hBt ↦ ?_⟩
  rw [hBt.base.eq_of_subset_base heB.base (subset_insert _ _)] at he
  simp at he

-- lemma PartialTruncateCollection.Base.base_insert (hB : T.Base B) (hBM : ¬ M.Base B)
--     (he : e ∈ M.E \ B) : M.Base (insert e B) := sorry

-- lemma PartialTruncateCollection.Base.exists_base_insert (hB : T.Base B) (hBM : ¬ M.Base B) :
--     ∃ e ∈ M.E \ B, T.ToTruncate (insert e B) := by
--   rw [PartialTruncateCollection.Base, iff_false_intro hBM] at hB

lemma PartialTruncateCollection.Base.exists_toTruncate_insert (hB : T.Base B) (hBM : ¬ M.Base B) :
    ∃ e ∈ M.E \ B, T.ToTruncate (insert e B) := sorry

lemma PartialTruncateCollection.Base.toTruncate_insert (hB : T.Base B) (hBM : ¬ M.Base B)
    (he : e ∈ M.E \ B) : T.ToTruncate (insert e B) := sorry



lemma PartialTruncateCollection.Indep.indep (hI : T.Indep I) : M.Indep I :=
  hI.1

lemma Base.partialTruncateBase_iff (hB : M.Base B) : T.Base B ↔ ¬ T.ToTruncate B := sorry

lemma Base.partialTruncateBase (hB : M.Base B) (hBt : ¬ T.ToTruncate B) : T.Base B :=
  .inl ⟨hB, hBt⟩

lemma PartialTruncateCollection.Indep.subset (hI : T.Indep I) (hJI : J ⊆ I) : T.Indep J :=
  ⟨hI.1.subset hJI, fun hT ↦ hI.2 <| by rwa [← hT.base.eq_of_subset_indep hI.indep hJI]⟩

lemma PartialTruncateCollection.indep_iff_subset_base : T.Indep I ↔ ∃ B, T.Base B ∧ I ⊆ B := by
  constructor
  · rintro ⟨hI, hIt⟩
    obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
    by_cases hBt : T.ToTruncate B
    · obtain ⟨e, he⟩ := exists_of_ssubset (hIB.ssubset_of_ne <| by rintro rfl; contradiction)
      exact ⟨B \ {e}, hBt.base_diff_singleton he.1, subset_diff_singleton hIB he.2⟩
    refine ⟨B, .inl ⟨hB, hBt⟩, hIB⟩
  rintro ⟨B, hB |⟨e, he, heB⟩, hIB⟩
  · exact ⟨hB.1.indep.subset hIB, fun hI ↦ hB.2 <| by rwa [← hI.base.eq_of_subset_base hB.1 hIB]⟩
  exact (heB.base_diff_singleton (mem_insert _ _)).indep.subset <|
    by simpa [diff_singleton_eq_self he.2]

lemma maximal_localTruncateIndep_eq : Maximal (T.Indep) = T.Base := by
  ext B
  sorry
  -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  -- ·

def PartialTruncateCollection.indepMatroid (T : M.PartialTruncateCollection) : IndepMatroid α where
  E := M.E
  Indep := T.Indep
  indep_empty := sorry
  indep_subset := sorry
  indep_aug := by
    simp_rw [maximal_localTruncateIndep_eq]
    intro I B ⟨hI, hIt⟩ hItb hB
    have hInotbase : ¬ M.Base I := fun hIb ↦ hItb (.inl ⟨hIb, hIt⟩)

    by_cases hBM : M.Base B
    · obtain ⟨e, heBI, heI⟩ := hI.exists_insert_of_not_base hInotbase hBM
      refine ⟨e, heBI, heI, fun heIt ↦ hItb ?_⟩
      simpa [heBI.2] using heIt.base_diff_singleton <| mem_insert _ _
    by_cases hcon : B ⊆ M.closure I
    · obtain ⟨e, he, heB⟩ := hB.exists_toTruncate_insert hBM
      have := heB.toTruncate_of_closure he.2 (J := I) (f := e)

    simp only [subset_def, not_forall, Classical.not_imp, exists_prop] at hcon
    obtain ⟨e, heB, he⟩ := hcon
    have heI : e ∉ I := not_mem_subset (M.subset_closure _) he
    rw [hI.not_mem_closure_iff_of_not_mem heI (hB.indep.indep.subset_ground heB)] at he
    exact ⟨e, ⟨heB, heI⟩, he, fun hT ↦ hItb (hT.base_of_insert heI)⟩


    -- obtain ⟨e, he, heB⟩ := hB.exists_toTruncate_insert hBM




      -- have := hI.exists_insert_of_not_base
  indep_maximal := sorry
  subset_ground := sorry


-- def PartialTruncateCollection.indepMatroid (T : M.PartialTruncateCollection) : Matroid α where
--   E := M.E
--   Base := T.Base
--   Indep := T.Indep
--   indep_iff' _ := indep_iff_subset_base
--   exists_base := by
--     obtain ⟨B, hB⟩ := M.exists_base
--     by_cases hBt : T.ToTruncate B
--     · obtain ⟨e, he⟩ := hBt.nonempty
--       exact ⟨_, hBt.base_diff_singleton he⟩
--     exact ⟨B, hB.partialTruncateBase hBt⟩
--   base_exchange := by
--     rintro B B' hB hB' e he
--     by_cases hBM : M.Base B

--     -- rw [Base.partialTruncateBase]
--     · by_cases hB'M : M.Base B'
--       · obtain ⟨f, hf, hfB⟩ := hBM.exchange hB'M he
--         exact ⟨f, hf, hfB.partialTruncateBase fun h ↦ (h.of_exchange hf.2 he.1 hBM).not_base hB⟩
--       by_contra! hcon

--       have hBeM := hB'.toTruncate_insert hB'M ⟨hBM.subset_ground he.1, he.2⟩

--       have hcon' := hBeM.toTruncate_of_closure (e := e) (f := e) (J := B \ {e}) he.2
--         (hBM.indep.subset diff_subset) ?_ (by simp)
--       · simp only [insert_diff_singleton, he.1, insert_eq_of_mem] at hcon'
--         exact hcon'.not_base hB
--       rw []


      -- rw [PartialTruncateCollection.Base, iff_false_intro hB'M, false_and, false_or] at hB'



    -- by_cases hBt : T.ToTruncate B
    -- · by_cases hBt' : T.ToTruncate B'
    --   ·
    --     -- obtain ⟨f, hf⟩ : (B' \ B).Nonempty := sorry
    --     obtain ⟨f, hf, hBf⟩ := hBt.base.exchange hBt'.base he

    --     refine ⟨f, hf, ?_⟩

        -- have := (hBt.base_diff_singleton he.1).exchange (hBt'.base_diff_singleton hf.1)



  --   sorry


  -- maximality := _
  -- subset_ground := _

lemma maximal_localTruncateIndep_eq : Maximal (T.Indep) = T.Base := by
  ext
  rw [maximal_subset_iff, LocalTruncateIndep]
  refine ⟨fun ⟨⟨hBi, hBb⟩, hmax⟩ ↦ ?_, ?_⟩
  · obtain ⟨B', hB', hBB'⟩ := hBi.exists_base_superset
    obtain rfl | hss := hBB'.eq_or_ssubset
    · exact .inl ⟨hB', hBb⟩
    right
    obtain ⟨e, heB', heB⟩ := exists_of_ssubset hss
    refine ⟨e, ⟨hB'.subset_ground heB', heB⟩, by_contra fun heBb ↦ ?_⟩
    rw [hmax ⟨(hB'.indep.subset (insert_subset heB' hBB')), heBb⟩ (subset_insert _ _)] at heB
    simp at heB
  rintro (⟨hB, hBb⟩ | ⟨e, heB, heBb⟩)
  · exact ⟨⟨hB.indep, hBb⟩, fun J hJ hBJ ↦ hB.eq_of_subset_indep hJ.1 hBJ⟩
  refine ⟨⟨?_, fun hT ↦ heB.2 ?_⟩, fun J hJ hBJ ↦ by_contra fun hne ↦ ?_⟩
  · exact (hT_base heBb).indep.subset (subset_insert _ _)
  · rw [(hT_base hT).eq_of_subset_base (hT_base heBb) (subset_insert _ _)]
    simp
  obtain ⟨f, hfJ, hfB⟩ := exists_of_ssubset (hBJ.ssubset_of_ne hne)

  have hfB_base : M.Base (insert f B) :=
    (hT_base heBb).base_of_indep_of_finDiff (hJ.1.subset (insert_subset hfJ hBJ))
    (finDiff_insert_insert heB hfB)
  obtain rfl : insert f B = J := hfB_base.eq_of_subset_indep hJ.1 (insert_subset hfJ hBJ)
  exact hJ.2 <| hT_finDiff heBb hfB_base (finDiff_insert_insert heB hfB)



/- Truncate a uniform matroid at a base `B₀`, by squashing every base at finite distance to `B₀`.
For finite uniform matroids, this just reduces the rank by one. For infinite ones,
This is weird, since it forms a proper quotient that still has a common base with `M` -/


-- def LocalTruncateIndepMatroid (M : Matroid α) (hr : M.RkPos) (T : Set (Set α))
--     (hT_base : ∀ ⦃B⦄, B ∈ T → M.Base B)
--     (hT_finDiff : ∀ ⦃B B'⦄, B ∈ T → M.Base B' → FinDiff B B' → B' ∈ T) : IndepMatroid α where
--   E := M.E
--   Indep := M.LocalTruncateIndep T
--   indep_empty := ⟨M.empty_indep, fun h ↦ M.empty_not_base (hT_base h)⟩

--   indep_subset I J hJ hIJ := hJ.subset hT_base hIJ
--   indep_aug := by
--     simp only [maximal_localTruncateIndep_iff hT_base hT_finDiff, not_or, not_and, not_not,
--       not_exists, mem_diff, and_imp]
--     rintro I B hI hInotbase hBmax
--     replace hInotbase := show ¬ M.Base I by simpa [hI.2] using hInotbase
--     rintro (⟨hB, hBb⟩ | ⟨e, heB, heBb⟩)
--     · obtain ⟨e, ⟨heB, heI⟩, heIi⟩ := hI.1.exists_insert_of_not_base hInotbase hB
--       exact ⟨e, ⟨heB, heI⟩, heIi, hBmax e heI⟩
--     -- have heI : e ∈ I := by
--     --   by_contra heI
--     --   have := hBmax _ heI
--     obtain ⟨f, ⟨(rfl | hf), hfI⟩, hfi⟩ := hI.1.exists_insert_of_not_base hInotbase (hT_base heBb)
--     ·
--       by_cases hbase : M.Base (insert f I)
--       · sorry
--       obtain ⟨g, hg, hgi⟩ := hfi.exists_insert_of_not_base hbase (hT_base heBb)
--       simp only [mem_insert_iff, true_or, insert_diff_of_mem, mem_diff, not_or] at hg
--       rw [insert_comm] at hgi
--       refine ⟨g, ⟨hg.1, hg.2.2⟩, hgi.subset (subset_insert _ _), fun hgI ↦ ?_⟩
--       obtain (rfl | hfI) : f ∈ insert g I :=
--         ((hT_base hgI).eq_of_subset_indep hgi (subset_insert _ _)).symm.subset (mem_insert f _)
--       · exact hg.2.1 rfl
--       contradiction
--       --   -- have := hbase.exchange (hT_base heBb) (e := f)

--       -- sorry
--     sorry
        -- have := hbase.exchange (hT_base heBb)






    -- have hInotbase : ¬ M.Base I := sorry
    -- by_cases hB : M.Base B
    -- · obtain ⟨e, heBI, heI⟩ := hI.1.exists_insert_of_not_base hInotbase hB
    --   obtain ⟨f, hfI, hins⟩ :=
    --     exists_insert_of_not_maximal (fun I J hJ hIJ ↦ hJ.subset hT_base hIJ) hI hInotmax
    --   refine ⟨e, heBI, heI, fun heIT ↦ hins.2 ?_⟩
    --   refine hT_finDiff heIT ?_ (finDiff_insert_insert heBI.2 hfI)
    --   exact (hT_base heIT).base_of_indep_of_finDiff hins.1 (finDiff_insert_insert heBI.2 hfI)

    -- obtain ⟨B₀, hB₀⟩ := M.exists_base
    -- obtain ⟨e, ⟨-, heB⟩, heBi⟩ := hBmax.prop.1.exists_insert_of_not_base hB hB₀
    -- have heBb : insert e B ∈ T :=
    --   by_contra fun h' ↦ hBmax.not_prop_of_ssuperset (ssubset_insert heB) ⟨heBi, h'⟩
    -- have :=

  -- indep_maximal := sorry
  -- subset_ground := sorry
-- def LocalTruncate (hM : M.Uniform) {B₀ : Set α} (hB₀ : M.Base B₀) (hne : B₀.Nonempty) : Matroid α :=
--   uniform_matroid_of_base M.E
--     (fun B ↦ (M.Base B ∧ ¬ FinDiff B B₀) ∨ (∃ e ∉ B, FinDiff (insert e B) B₀))
--     (by
--       obtain ⟨e, he⟩ := hne
--       exact ⟨B₀ \ {e}, .inr ⟨e, (by simp), by simp [he, finDiff_refl]⟩⟩)
--     (by

--       rintro B (⟨hB, hBB₀⟩ | ⟨e, heB, hBB₀⟩) B' (⟨hB', hB'B₀⟩ | ⟨e', he'B', hB'B₀⟩) hne hss
--       · obtain rfl : B = B' := hB.eq_of_subset_base hB' hss
--         contradiction
--       · have heB'ins := (hM.base_of_base_of_finDiff hB₀ hB'B₀.symm)
--         obtain rfl : B = insert e' B' :=
--           hB.eq_of_subset_base heB'ins <| hss.trans (subset_insert _ _)
--         exact he'B' (hss (mem_insert _ _))
--       · have heBins := (hM.base_of_base_of_finDiff hB₀ hBB₀.symm)
--         refine hB'B₀ (FinDiff.trans ?_ hBB₀)
--         obtain ⟨f, hfB', hfB⟩ := exists_of_ssubset (hss.ssubset_of_ne hne)
--         have hfBins : M.Base (insert f B) := insert_base_of_insert_indep heB hfB heBins
--           (hB'.indep.subset (insert_subset hfB' hss))
--         obtain rfl : insert f B = B' := hfBins.eq_of_subset_base hB' (insert_subset hfB' hss)
--         apply finDiff_insert_insert hfB heB

--       have heBins := hM.base_of_base_of_finDiff hB₀ hBB₀.symm
--       have he'B'ins := hM.base_of_base_of_finDiff hB₀ hB'B₀.symm

--       by_cases heB' : e ∈ B'
--       · have h_eq : insert e B = insert e' B' := heBins.eq_of_subset_base he'B'ins
--           (insert_subset (mem_insert_of_mem _ heB') (hss.trans (subset_insert _ _)))
--         obtain rfl | he'B := h_eq.symm.subset (mem_insert e' B')
--         · contradiction
--         exact he'B' (hss he'B)
--       have hb := hM.base_of_base_of_finDiff he'B'ins (finDiff_insert_insert he'B' heB')
--       have h_eq := heBins.eq_of_subset_base hb (insert_subset_insert hss)
--       apply_fun (fun X ↦ X \ {e}) at h_eq
--       obtain rfl : B = B' := by simpa [heB, heB'] using h_eq
--       contradiction )
--     (by
--       rintro B e f (⟨hB, hBB₀⟩ | ⟨g, hgB, hgBB₀⟩) heB hfB
--       · left
--         rw [finDiff_comm, ← finDiff_iff_exchange heB hfB, finDiff_comm, and_iff_left hBB₀]
--         exact hM.base_of_base_of_finDiff hB (finDiff_exchange heB hfB)

--       right
--       have hef : e ≠ f := by rintro rfl; contradiction
--       refine ⟨e, by simp [hef], FinDiff.trans ?_ hgBB₀⟩
--       rw [insert_diff_singleton_comm hef.symm, insert_diff_singleton,
--         insert_eq_of_mem (mem_insert_of_mem _ heB)]
--       exact finDiff_insert_insert hfB hgB )
--     (by
--       intro I X hIX hXE hinf
--       sorry
--     )
--     sorry




-- def tr (M : Matroid α) : Matroid α where
--   E := M.E
--   Base B := ∃ e ∉ B, M.Base (insert e B)
--   Indep I := M.Indep I ∧ ¬ M.Base I
--   indep_iff' I := by
--     refine ⟨fun ⟨hI, hIb⟩ ↦ ?_, fun ⟨B, ⟨e, heB, heB'⟩, hIB⟩ ↦ ?_⟩
--     · obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
--       obtain ⟨e, heB, heI⟩ := exists_of_ssubset (hIB.ssubset_of_ne (by rintro rfl; contradiction))
--       exact ⟨B \ {e}, ⟨e, by simp, by simpa [heB]⟩, subset_diff_singleton hIB heI⟩
--     have hIBe : I ⊆ insert e B := hIB.trans (subset_insert _ _)
--     refine ⟨heB'.indep.subset hIBe, fun hI ↦ heB (hIB ?_)⟩
--     simp [hI.eq_of_subset_base heB' hIBe]
--   exists_base := _
--   base_exchange := _
--   maximality := _
--   subset_ground := _

end Local
