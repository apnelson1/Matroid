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

namespace PartialTruncateCollection

@[simps] def top (M : Matroid α) [RkPos M] : M.PartialTruncateCollection where
  ToTruncate := M.Base
  forall_nonempty _ := Base.nonempty
  forall_base _ := id
  toTruncate_of_toTruncate := by tauto

variable {T : M.PartialTruncateCollection}

lemma ToTruncate.base (hB : T.ToTruncate B) : M.Base B :=
  T.forall_base hB

lemma ToTruncate.nonempty (hB : T.ToTruncate B) : B.Nonempty :=
  T.forall_nonempty hB

lemma ToTruncate.toTruncate_of_closure (hI : T.ToTruncate (insert e I)) (heI : e ∉ I) (hfJ : f ∉ J)
    (hJ : M.Indep (insert f J)) (hIJ : I ⊆ M.closure J) : T.ToTruncate (insert f J) := by
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

lemma ToTruncate.exchange (hB : T.ToTruncate B) (heB : e ∉ B) (hfB : f ∈ B)
    (h_indep : M.Indep (insert e (B \ {f}))) : T.ToTruncate (insert e (B \ {f})) := by
  have hef : e ≠ f := by rintro rfl; contradiction
  have h_base := hB.base.base_of_indep_of_finDiff h_indep (finDiff_exchange hfB heB)
  exact T.toTruncate_of_toTruncate hB hfB h_base (mem_insert _ _)
    <| by simp [diff_singleton_eq_self (show e ∉ B \ {f} by simp [heB, hef])]

lemma ToTruncate.of_exchange (hB' : T.ToTruncate (insert e (B \ {f})))
    (heB : e ∉ B) (hfB : f ∈ B) (hB : M.Base B) : T.ToTruncate B := by
  have hef : e ≠ f := by rintro rfl; contradiction
  have hrw : B = insert f (insert e (B \ {f}) \ {e}) := by
    simp [diff_singleton_eq_self (show e ∉ B \ {f} by simp [hef, heB]), insert_eq_of_mem hfB]
  rw [hrw]
  replace hB := hB.indep
  exact hB'.exchange (by simp [hef.symm]) (mem_insert _ _) <| (by rwa [← hrw])

lemma ToTruncate.finDiff {B B' : Set α} (hB : T.ToTruncate B) (hB' : M.Base B')
    (hdiff : FinDiff B B') : T.ToTruncate B' := by
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

def Indep (T : M.PartialTruncateCollection) (I : Set α) : Prop := M.Indep I ∧ ¬ T.ToTruncate I

lemma indep_eq : T.Indep = fun I ↦ M.Indep I ∧ ¬ T.ToTruncate I := rfl

def Below (T : M.PartialTruncateCollection) (B : Set α) : Prop :=
  ∃ e ∈ M.E \ B, T.ToTruncate (insert e B)

def Base (T : M.PartialTruncateCollection) (B : Set α) : Prop :=
  (M.Base B ∧ ¬ T.ToTruncate B) ∨ T.Below B

lemma ToTruncate.base_diff_singleton (hBt : T.ToTruncate B) (heB : e ∈ B) : T.Base (B \ {e}) :=
  .inr ⟨e, by simpa [hBt.base.subset_ground heB, heB] ⟩

lemma ToTruncate.base_of_insert (hBt : T.ToTruncate (insert e B)) (heB : e ∉ B) : T.Base B := by
  simpa [heB] using hBt.base_diff_singleton (mem_insert _ _)

lemma Base.indep (hB : T.Base B) : T.Indep B := by
  obtain h | ⟨e, he, heB⟩ := hB
  · exact ⟨h.1.indep, h.2⟩
  refine ⟨heB.base.indep.subset <| subset_insert _ _, fun hBt ↦ ?_⟩
  rw [hBt.base.eq_of_subset_base heB.base (subset_insert _ _)] at he
  simp at he

lemma Base.exists_toTruncate_insert (hB : T.Base B) (hBM : ¬ M.Base B) :
    ∃ e ∈ M.E \ B, T.ToTruncate (insert e B) := by
  rwa [PartialTruncateCollection.Base, iff_false_intro hBM, false_and, false_or] at hB

lemma Indep.indep (hI : T.Indep I) : M.Indep I :=
  hI.1

lemma _root_.Matroid.Base.partialTruncateBase_iff (hB : M.Base B) : T.Base B ↔ ¬ T.ToTruncate B :=
  ⟨fun h h' ↦ h.indep.2 h', fun h ↦ .inl ⟨hB, h⟩⟩

lemma _root_.Matroid.Base.partialTruncateBase (hB : M.Base B) (hBt : ¬ T.ToTruncate B) : T.Base B :=
  .inl ⟨hB, hBt⟩

lemma Indep.subset (hI : T.Indep I) (hJI : J ⊆ I) : T.Indep J :=
  ⟨hI.1.subset hJI, fun hT ↦ hI.2 <| by rwa [← hT.base.eq_of_subset_indep hI.indep hJI]⟩

lemma maximal_indep_eq : Maximal (T.Indep) = T.Base := by
  ext B
  rw [maximal_iff_forall_insert (fun _ _ ↦ PartialTruncateCollection.Indep.subset)]
  by_cases hB : M.Base B
  · rw [hB.partialTruncateBase_iff, PartialTruncateCollection.Indep, and_comm (a := M.Indep B),
      and_assoc, and_iff_left_iff_imp, and_iff_right hB.indep]
    intro h x hxB hi
    rw [hB.eq_of_subset_indep hi.1  (subset_insert _ _)] at hxB
    simp at hxB
  simp only [PartialTruncateCollection.Base, hB, false_and, mem_diff, false_or]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨B₀, hB₀⟩ := M.exists_base
    obtain ⟨e, ⟨heB₀, heB⟩, heB'⟩ := h.1.1.exists_insert_of_not_base hB hB₀
    exact ⟨e, ⟨hB₀.subset_ground heB₀, heB⟩, by_contra fun ht ↦ h.2 e heB ⟨heB', ht⟩⟩
  rintro ⟨e, ⟨heE, heB⟩, ht⟩
  refine ⟨(ht.base_of_insert heB).indep, fun x hx hxB ↦ hxB.2 ?_⟩
  have hex : e ≠ x := by rintro rfl; exact hxB.2 ht
  simpa [heB] using ht.exchange (e := x) (f := e) (by simp [hx, hex.symm]) (by simp)
    (by simpa [heB] using hxB.1)

@[simps! E] protected def matroid (T : M.PartialTruncateCollection) :
    Matroid α := IndepMatroid.matroid <| IndepMatroid.mk
  (E := M.E)
  (Indep := T.Indep)
  (indep_empty := ⟨M.empty_indep, fun h ↦ by simpa using h.nonempty⟩)
  (indep_subset := fun _ _ ↦ Indep.subset)
  (indep_aug := by
    simp_rw [maximal_indep_eq]
    intro I B ⟨hI, hIt⟩ hItb hB
    have hInotbase : ¬ M.Base I := fun hIb ↦ hItb (.inl ⟨hIb, hIt⟩)

    by_cases hBM : M.Base B
    · obtain ⟨e, heBI, heI⟩ := hI.exists_insert_of_not_base hInotbase hBM
      refine ⟨e, heBI, heI, fun heIt ↦ hItb ?_⟩
      simpa [heBI.2] using heIt.base_diff_singleton <| mem_insert _ _
    by_cases hcon : B ⊆ M.closure I
    · exfalso
      obtain ⟨e, he, heB⟩ := hB.exists_toTruncate_insert hBM
      obtain ⟨B₀, hB₀⟩ := M.exists_base
      obtain ⟨f, ⟨-, hf⟩, hfI⟩ := hI.exists_insert_of_not_base hInotbase hB₀
      exact hItb <| (heB.toTruncate_of_closure he.2 hf hfI hcon).base_of_insert hf
    simp only [subset_def, not_forall, Classical.not_imp, exists_prop] at hcon
    obtain ⟨e, heB, he⟩ := hcon
    have heI : e ∉ I := not_mem_subset (M.subset_closure _) he
    rw [hI.not_mem_closure_iff_of_not_mem heI (hB.indep.indep.subset_ground heB)] at he
    exact ⟨e, ⟨heB, heI⟩, he, fun hT ↦ hItb (hT.base_of_insert heI)⟩ )

  (indep_maximal := by
    intro X hX I hI hIX
    obtain ⟨J, hJX, hIJ⟩ := hI.indep.subset_basis_of_subset hIX
    have h_mono : ∀ ⦃s t : Set α⦄, T.Indep t ∧ t ⊆ X → s ⊆ t → T.Indep s ∧ s ⊆ X :=
      fun I J hI hIJ ↦ ⟨⟨hI.1.1.subset hIJ, fun hI' ↦ (hI.1.subset hIJ).2 hI'⟩, hIJ.trans hI.2⟩

    simp only [maximal_iff_forall_insert h_mono, insert_subset_iff, not_and]
    by_cases hJ : T.ToTruncate Jlb
    · obtain ⟨e, he⟩ := exists_of_ssubset (hIJ.ssubset_of_ne <| by rintro rfl; exact hI.2 hJ)

      refine ⟨J \ {e}, subset_diff_singleton hIJ he.2, ?_⟩
      suffices ∀ (x : α), (x ∈ J → x = e) → T.Indep (insert x (J \ {e})) → x ∉ X by
        simpa [(hJ.base_diff_singleton he.1).indep, diff_singleton_subset_iff,
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

@[simp] lemma matroid_base_eq : T.matroid.Base = T.Base := by
  simp [funext_iff, ← maximal_indep_eq, base_iff_maximal_indep, Maximal]

lemma matroid_closure_eq_closure (X : Set α) (hX : X ⊆ M.E) (hX : ¬ T.matroid.Spanning X) :
    T.matroid.closure X = M.closure X := by
  obtain ⟨I, hI'⟩ := T.matroid.exists_basis X
  have hi := hI'.indep
  simp only [matroid_indep_eq, indep_eq] at hi

  have aux : ∀ x, ¬ T.ToTruncate (insert x I) := by
    refine fun x ht ↦ hX ?_
    by_cases hxI : x ∈ I
    · exact (hi.2 (by simpa [hxI] using ht)).elim
    have hb := ht.base_of_insert hxI
    rw [← T.matroid_base_eq] at hb
    exact hb.spanning.superset hI'.subset

  have hI : M.Basis I X
  · simp_rw [hi.1.basis_iff_forall_insert_dep hI'.subset, dep_iff, insert_subset_iff,
      and_iff_left hi.1.subset_ground]
    exact fun e he ↦ ⟨fun hi ↦ (hI'.insert_dep he).not_indep ⟨hi, aux _⟩,
      (hI'.subset_ground he.1)⟩

  rw [← hI'.closure_eq_closure, ← hI.closure_eq_closure, Set.ext_iff]
  simp [hI'.indep.mem_closure_iff', T.indep_eq, hI.indep.mem_closure_iff', aux]









--   by_cases hXs : M.Spanning X
--   · rw [hXs.closure_eq, show M.E = T.matroid.E from rfl, ← spanning_iff_closure_eq,
--       spanning_iff_exists_base_subset', and_iff_left (show X ⊆ T.matroid.E from hX)]

--     simp only [matroid_base_eq]

--     obtain ⟨B, hB, hBX⟩ := hXs.exists_base_subset
--     by_cases hBt : T.Base B
--     · exact ⟨B, hBt, hBX⟩

--     rw [hB.partialTruncateBase_iff, not_not] at hBt
--     obtain ⟨e, he⟩ := hBt.nonempty
--     exact ⟨_, hBt.base_diff_singleton he, diff_subset.trans hBX⟩

--   obtain ⟨I, hI'⟩ := T.matroid.exists_basis X
--   have hi := hI'.indep
--   simp only [matroid_indep_eq, indep_eq] at hi
--   -- simp only [hM'_def, localTruncate_indep_iff] at hi
--   have hI : M.Basis I X
--   · simp_rw [hi.1.basis_iff_forall_insert_dep hI'.subset, dep_iff, insert_subset_iff,
--       and_iff_left hi.1.subset_ground]
--     refine fun e he ↦ ⟨fun hi ↦ (hI'.insert_dep he).not_indep ⟨hi, fun hIt ↦ hXs ?_⟩,
--       (hI'.subset_ground he.1)⟩
--     exact hIt.base.spanning.superset (insert_subset he.1 hI'.subset)




--   rw [← hI'.closure_eq_closure, ← hI.closure_eq_closure, Set.ext_iff]
--   simp only [hI'.indep.mem_closure_iff', matroid_E, matroid_indep_eq, T.indep_eq, and_imp,
--     hI.indep.mem_closure_iff', and_congr_right_iff]

--   refine fun e heE ↦ ⟨fun h hi ↦ by_contra fun heI ↦ heI <| h hi fun heIt ↦ ?_, fun h ↦ ?_⟩
--   · have := heIt.base_of_insert heI


  -- simp only [hM'_def, hI'.indep.mem_closure_iff', Uniform.LocalTruncate_E, localTruncate_indep_iff,
  --   and_imp, hI.indep.mem_closure_iff', and_congr_right_iff]

  -- refine fun e heE ↦ ⟨fun heI heIBs ↦ ?_, fun h1 h2 h3 ↦ h1 h2⟩
  -- by_contra heI'

  -- refine heI' <| heI heIBs fun hins ↦ ?_
  -- obtain rfl | hssu := hI.subset.eq_or_ssubset
  -- · exact hX e ⟨heE, heI'⟩ hins

  -- obtain ⟨f, hf⟩ := exists_of_ssubset hssu

  -- have hins' := hBs_finDiff hins (B' := insert f I) (finDiff_insert_insert heI' hf.2)
  --   (insert_subset (hXE hf.1) hi.1.subset_ground)
  -- exact hXs <| (hBs_base hins').spanning.superset (insert_subset hf.1 hssu.subset)

    -- obtain rfl | hssu := hBX.eq_or_ssubset
    -- · have := hBt.not_

    -- simp
    -- simp only [hM'_def, Uniform.LocalTruncate_Base]

    -- obtain ⟨B, hB, hBX⟩ := hXs.exists_base_subset
    -- by_cases hBs : B ∈ Bs
    -- · obtain ⟨e, he⟩ := hB.nonempty
    --   exact ⟨B \ {e}, .inr ⟨e, by simpa [he]⟩, diff_subset.trans hBX⟩
    -- exact ⟨B, .inl ⟨hB, hBs⟩, hBX⟩
  -- obtain ⟨I, hI⟩ := M.exists_basis X
  -- have : X ⊆ T.matroid.E := hX
  -- have hI' : T.matroid.Basis I X := by
  --   rw [basis_iff_maximal]
  --   simp_rw [T.matroid_indep_eq, T.indep_eq]



end PartialTruncateCollection
