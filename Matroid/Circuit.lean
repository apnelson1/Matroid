
import Matroid.Closure
import Matroid.Constructions.Basic
import Matroid.ForMathlib.Card

import Matroid.ForMathlib.Matroid.Basic

/-!
  A `Circuit` of a matroid is a minimal dependent set.
-/

variable {α : Type*} {M : Matroid α} {C C' I X K C₁ C₂ R E D : Set α} {e f x y : α}

open Set Set.Notation
namespace Matroid

/-- A Circuit is a minimal dependent set -/
def Circuit (M : Matroid α) (C : Set α) : Prop := Minimal M.Dep C

lemma circuit_def : M.Circuit C ↔ Minimal M.Dep C := Iff.rfl

lemma Circuit.dep (hC : M.Circuit C) : M.Dep C :=
  hC.prop

lemma Circuit.minimal (hC : M.Circuit C) : Minimal M.Dep C :=
  hC

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Circuit.subset_ground (hC : M.Circuit C) : C ⊆ M.E :=
  hC.dep.subset_ground

lemma circuit_iff : M.Circuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, M.Dep I → I ⊆ C → I = C := by
  simp_rw [circuit_def, minimal_subset_iff, eq_comm (a := C)]

lemma Circuit.ssubset_indep (hC : M.Circuit C) (hXC : X ⊂ C) : M.Indep X := by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h ↦ hXC.ne ((circuit_iff.1 hC).2 h hXC.subset)

lemma circuit_iff_forall_ssubset : M.Circuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, I ⊂ C → M.Indep I := by
  simp_rw [circuit_iff, dep_iff, and_congr_right_iff, ssubset_iff_subset_ne, and_imp]
  exact fun _ hC ↦ ⟨fun h I hIC hne ↦ by_contra fun hi ↦ hne (h hi (hIC.trans hC) hIC),
    fun h I hi _ hIC ↦ by_contra fun hne ↦ hi (h hIC hne)⟩

lemma Circuit.diff_singleton_indep (hC : M.Circuit C) (he : e ∈ C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (diff_singleton_sSubset.2 he)

lemma Circuit.diff_singleton_basis (hC : M.Circuit C) (he : e ∈ C) : M.Basis (C \ {e}) C := by
  nth_rw 2 [← insert_eq_of_mem he];
  rw [← insert_diff_singleton, (hC.diff_singleton_indep he).basis_insert_iff,
    insert_diff_singleton, insert_eq_of_mem he]
  exact Or.inl hC.dep

lemma Circuit.basis_iff_eq_diff_singleton (hC : M.Circuit C) :
    M.Basis I C ↔ ∃ e ∈ C, I = C \ {e} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.diff_singleton_indep he.1)
      (subset_diff_singleton h.subset he.2) diff_subset⟩
  rintro ⟨e, he, rfl⟩
  exact hC.diff_singleton_basis he

lemma Circuit.basis_iff_insert_eq (hC : M.Circuit C) :
    M.Basis I C ↔ ∃ e ∈ C \ I, C = insert e I := by
  rw [hC.basis_iff_eq_diff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ ↦ ⟨e, ⟨he, fun heI ↦ (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ ↦ ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_diff_singleton, insert_eq_of_mem he]
  rw [hC, insert_diff_self_of_not_mem he.2]

lemma Circuit.closure_diff_singleton_eq_closure (hC : M.Circuit C) (e : α) :
    M.closure (C \ {e}) = M.closure C :=
  (em (e ∈ C)).elim (fun he ↦ by rw [(hC.diff_singleton_basis he).closure_eq_closure])
    (fun he ↦ by rw [diff_singleton_eq_self he])

lemma Circuit.subset_closure_diff_singleton (hC : M.Circuit C) (e : α) :
    C ⊆ M.closure (C \ {e}) := by
  by_cases he : e ∈ C
  · rw [(hC.diff_singleton_basis he).closure_eq_closure]; exact M.subset_closure _
  rw [diff_singleton_eq_self he]; exact M.subset_closure _

lemma Circuit.subset_closure_diff_subsingleton (hC : M.Circuit C) {Z : Set α}
    (hZ : Z.Subsingleton) : C ⊆ M.closure (C \ Z) := by
  obtain (rfl | ⟨x, rfl⟩) := hZ.eq_empty_or_singleton
  · simpa using M.subset_closure _
  exact hC.subset_closure_diff_singleton _

lemma Circuit.closure_diff_subsingleton_eq_closure (hC : M.Circuit C) {Z : Set α}
    (hZ : Z.Subsingleton) : M.closure (C \ Z) = M.closure C := by
  obtain (rfl | ⟨x, rfl⟩) := hZ.eq_empty_or_singleton
  · simp
  rw [hC.closure_diff_singleton_eq_closure]

lemma Circuit.mem_closure_diff_singleton_of_mem (hC : M.Circuit C) (heC : e ∈ C) :
    e ∈ M.closure (C \ {e}) :=
  (hC.subset_closure_diff_singleton e) heC

lemma Circuit.eq_of_not_indep_subset (hC : M.Circuit C) (hX : ¬ M.Indep X) (hXC : X ⊆ C) :
    X = C :=
  eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

lemma Circuit.eq_of_dep_subset (hC : M.Circuit C) (hX : M.Dep X) (hXC : X ⊆ C) : X = C :=
  hC.eq_of_not_indep_subset hX.not_indep hXC

lemma Circuit.not_ssubset (hC : M.Circuit C) (hC' : M.Circuit C') : ¬C' ⊂ C :=
  fun h' ↦ h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

lemma Circuit.nonempty (hC : M.Circuit C) : C.Nonempty :=
  hC.dep.nonempty

lemma empty_not_circuit (M : Matroid α) : ¬M.Circuit ∅ :=
  fun h ↦ by simpa using h.nonempty

lemma Circuit.circuit_restrict_of_subset (hC : M.Circuit C) (hCR : C ⊆ R) :
    (M ↾ R).Circuit C := by
  simp_rw [circuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC ↦ hC.2 hI (hIC.trans hC.1.2) hIC⟩

lemma restrict_circuit_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Circuit C ↔ M.Circuit C ∧ C ⊆ R := by
  refine ⟨?_, fun h ↦ h.1.circuit_restrict_of_subset h.2⟩
  simp_rw [circuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h ↦ ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC ↦ h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

lemma circuit_iff_dep_forall_diff_singleton_indep :
    M.Circuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.Indep (C \ {e}) := by
  rw [circuit_iff_forall_ssubset, and_congr_right_iff]
  refine fun _ ↦ ⟨fun h e heC ↦ h (Iff.mpr diff_singleton_sSubset heC), fun h I hIC ↦ ?_⟩
  obtain ⟨e, he⟩ := exists_of_ssubset hIC
  exact (h e he.1).subset (subset_diff_singleton hIC.subset he.2)

lemma Circuit.eq_of_subset_circuit (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ⊆ C₂) :
    C₁ = C₂ :=
  hC₂.eq_of_dep_subset hC₁.dep h

lemma Indep.insert_circuit_of_forall (hI : M.Indep I) (heI : e ∉ I) (he : e ∈ M.closure I)
    (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.Circuit (insert e I) := by
  rw [circuit_iff_dep_forall_diff_singleton_indep, hI.insert_dep_iff,
    and_iff_right ⟨he, heI⟩]
  simp_rw [← insert_diff_singleton (s := I)]
  rintro f (rfl | ⟨hfI, hne : f ≠ e⟩)
  · simp [hI.diff]
  rw [insert_diff_singleton, ← insert_diff_singleton_comm hne.symm, (hI.diff _).insert_indep_iff,
    mem_diff, mem_diff, and_iff_right (mem_ground_of_mem_closure he)]
  exact .inl (h f hfI)

lemma Indep.insert_circuit_of_forall_of_nontrivial (hI : M.Indep I) (hInt : I.Nontrivial)
    (he : e ∈ M.closure I) (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.Circuit (insert e I) := by
  refine hI.insert_circuit_of_forall (fun heI ↦ ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))

section Cyclic

variable {A B : Set α}

/-- A cyclic set is a (possibly empty) union of circuits -/
def Cyclic (M : Matroid α) (A : Set α) := ∃ Cs : Set (Set α), A = ⋃₀ Cs ∧ ∀ C ∈ Cs, M.Circuit C

lemma Cyclic.exists (hA : M.Cyclic A) : ∃ Cs, A = ⋃₀ Cs ∧ ∀ C ∈ Cs, M.Circuit C := hA

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Cyclic.subset_ground (hA : M.Cyclic A) : A ⊆ M.E := by
  obtain ⟨Cs, rfl, h⟩ := hA.exists
  simpa using fun C hC ↦ (h C hC).subset_ground

@[simp] lemma empty_cyclic (M : Matroid α) : M.Cyclic ∅ :=
  ⟨∅, by simp⟩

lemma Circuit.cyclic (hC : M.Circuit C) : M.Cyclic C :=
  ⟨{C}, by simpa⟩

lemma Cyclic.exists_of_mem (hA : M.Cyclic A) (he : e ∈ A) : ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ A := by
  obtain ⟨Cs, rfl, h⟩ := hA.exists
  obtain ⟨C, hC, heC⟩ : ∃ t ∈ Cs, e ∈ t := by simpa only [mem_sUnion] using he
  exact ⟨C, h C hC, heC, subset_sUnion_of_subset Cs C (fun ⦃a⦄ ↦ id) hC⟩

lemma Cyclic.dep_of_nonempty (hA : M.Cyclic A) (hA : A.Nonempty) : M.Dep A := by
  obtain ⟨e, he⟩ := hA
  obtain ⟨C, hC, -, hCA⟩ := hA.exists_of_mem he
  exact hC.dep.superset hCA

lemma cyclic_iff_forall_exists : M.Cyclic A ↔ ∀ e ∈ A, ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ A := by
  refine ⟨fun h e he ↦ h.exists_of_mem he, fun h ↦ ?_⟩
  choose! Cs hCs using h
  simp only [forall_and] at hCs
  refine ⟨Cs '' A, ?_, by simpa using hCs.1⟩
  simp only [sUnion_image, subset_antisymm_iff, iUnion_subset_iff, subset_def (s := A),
    mem_iUnion, exists_prop, and_iff_left hCs.2.2]
  exact fun e he ↦ ⟨e, he, hCs.2.1 _ he⟩

lemma Cyclic.iUnion {ι : Type*} (As : ι → Set α) (hAs : ∀ i, M.Cyclic (As i)) :
    M.Cyclic (⋃ i, As i) := by
  choose f hf using fun i ↦ (hAs i).exists
  refine ⟨⋃ i, f i, by aesop, ?_⟩
  simp only [mem_iUnion, forall_exists_index]
  exact fun C i hC ↦ (hf i).2 _ hC

lemma Cyclic.sUnion (As : Set (Set α)) (hAs : ∀ A ∈ As, M.Cyclic A) : M.Cyclic (⋃₀ As) := by
  rw [sUnion_eq_iUnion]
  apply Cyclic.iUnion
  simpa

lemma Cyclic.biUnion {ι : Type*} {As : ι → Set α} {I : Set ι} (hAs : ∀ i ∈ I, M.Cyclic (As i)) :
    M.Cyclic (⋃ i ∈ I, As i) := by
  rw [biUnion_eq_iUnion]
  apply Cyclic.iUnion
  simpa

lemma Cyclic.union (hA : M.Cyclic A) (hB : M.Cyclic B) : M.Cyclic (A ∪ B) := by
  rw [union_eq_iUnion]
  apply Cyclic.iUnion
  simp [hA, hB]


end Cyclic

section Fundamental

/-- For an independent set `I` that spans a point `e ∉ I`, the unique circuit contained in
`I ∪ {e}`. Has the junk value `{e}` if `e ∈ I` and `insert e I` if `e ∉ M.closure I`. -/
def fundCct (M : Matroid α) (e : α) (I : Set α) :=
  insert e (I ∩ (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}))

lemma fundCct_eq_sInter (he : e ∈ M.closure I) :
    M.fundCct e I = insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}) := by
  rw [fundCct, inter_eq_self_of_subset_right]
  exact sInter_subset_of_mem ⟨Subset.rfl, he⟩

lemma fundCct_subset_insert (M : Matroid α) (e : α) (I : Set α) : M.fundCct e I ⊆ insert e I :=
  insert_subset_insert inter_subset_left

lemma fundCct_subset_ground (he : e ∈ M.E) (hI : I ⊆ M.E := by aesop_mat) : M.fundCct e I ⊆ M.E :=
  (M.fundCct_subset_insert e I).trans (insert_subset he hI)

lemma mem_fundCct (M : Matroid α) (e : α) (I : Set α) : e ∈ fundCct M e I :=
  mem_insert _ _

/-- The fundamental circuit of `e` and `I` has the junk value `{e}` if `e ∈ I` -/
lemma Indep.fundCct_eq_of_mem (hI : M.Indep I) (he : e ∈ I) : M.fundCct e I = {e} := by
  rw [fundCct, ← union_singleton, union_eq_right]
  refine inter_subset_right.trans (sInter_subset_of_mem ?_)
  simp only [mem_setOf, singleton_subset_iff, and_iff_right he]
  exact M.mem_closure_self _ (hI.subset_ground he)

lemma Indep.fundCct_circuit (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    M.Circuit (M.fundCct e I) := by
  apply (hI.inter_right _).insert_circuit_of_forall (by simp [heI])
  · rw [(hI.subset _).closure_inter_eq_inter_closure, mem_inter_iff, and_iff_right hecl,
      hI.closure_sInter_eq_biInter_closure_of_forall_subset _
      (by simp (config := {contextual := true}))]
    · simp
    · exact ⟨I, rfl.subset, hecl⟩
    exact union_subset rfl.subset (sInter_subset_of_mem ⟨rfl.subset, hecl⟩)
  simp only [mem_inter_iff, mem_sInter, mem_setOf_eq, and_imp]
  exact fun f hfI hf hecl ↦ (hf _ (diff_subset.trans inter_subset_left) hecl).2 rfl

lemma Indep.mem_fundCct_iff (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    x ∈ M.fundCct e I ↔ M.Indep (insert e I \ {x}) := by
  obtain (rfl | hne) := eq_or_ne x e
  · simp [hI.diff, mem_fundCct]
  suffices (∀ t ⊆ I, e ∈ M.closure t → x ∈ t) ↔ e ∉ M.closure (I \ {x}) by
    simpa [fundCct_eq_sInter hecl, hne, ← insert_diff_singleton_comm hne.symm,
      (hI.diff _).insert_indep_iff, mem_ground_of_mem_closure hecl, heI]
  refine ⟨fun h hecl ↦ (h _ diff_subset hecl).2 rfl, fun h J hJ heJ ↦ by_contra fun hxJ ↦ h ?_⟩
  exact M.closure_subset_closure (subset_diff_singleton hJ hxJ) heJ

lemma Base.fundCct_circuit {B : Set α} (hB : M.Base B) (hxE : x ∈ M.E) (hxB : x ∉ B) :
    M.Circuit (M.fundCct x B) :=
  hB.indep.fundCct_circuit (by rwa [hB.closure_eq]) hxB

end Fundamental

lemma Dep.exists_circuit_subset (hX : M.Dep X) : ∃ C, C ⊆ X ∧ M.Circuit C := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  exact ⟨M.fundCct e I, (M.fundCct_subset_insert e I).trans (insert_subset heX hI.subset),
    hI.indep.fundCct_circuit (hI.subset_closure heX) heI⟩

lemma dep_iff_superset_circuit (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X ↔ ∃ C, C ⊆ X ∧ M.Circuit C :=
  ⟨Dep.exists_circuit_subset, fun ⟨C, hCX, hC⟩ ↦ hC.dep.superset hCX⟩

lemma dep_iff_superset_circuit' : M.Dep X ↔ (∃ C, C ⊆ X ∧ M.Circuit C) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.exists_circuit_subset, h.subset_ground⟩, fun ⟨⟨C, hCX, hC⟩, h⟩ ↦ hC.dep.superset hCX⟩

lemma indep_iff_forall_subset_not_circuit' :
    M.Indep I ↔ (∀ C, C ⊆ I → ¬M.Circuit C) ∧ I ⊆ M.E := by
  simp_rw [indep_iff_not_dep, dep_iff_superset_circuit', not_and, imp_not_comm (b := _ ⊆ _)]; aesop

lemma indep_iff_forall_subset_not_circuit (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ C, C ⊆ I → ¬M.Circuit C := by
  rw [indep_iff_forall_subset_not_circuit', and_iff_left hI]

lemma mem_closure_iff_mem_or_exists_circuit (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ e ∈ X ∨ ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ insert e X := by
  refine (em (e ∈ X)).elim (fun he ↦ iff_of_true (M.mem_closure_of_mem he) (.inl he)) (fun he ↦ ?_)
  rw [or_iff_right he]
  refine ⟨fun h ↦ ?_, fun ⟨C, hC, heC, hCX⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [← hI.closure_eq_closure] at h
    exact ⟨M.fundCct e I, hI.indep.fundCct_circuit h (not_mem_subset hI.subset he),
      M.mem_fundCct e I, (M.fundCct_subset_insert _ _).trans (insert_subset_insert hI.subset)⟩
  refine ((hC.subset_closure_diff_singleton e).trans (M.closure_subset_closure ?_)) heC
  rwa [diff_subset_iff, singleton_union]

lemma mem_closure_iff_exists_circuit_of_not_mem (he : e ∉ X) :
    e ∈ M.closure X ↔ ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ insert e X := by
  rw [← closure_inter_ground, mem_closure_iff_mem_or_exists_circuit, mem_inter_iff,
    iff_false_intro he, false_and, false_or]
  refine ⟨
    fun ⟨C, hC, heC, h⟩ ↦ ⟨C, hC, heC, h.trans ((insert_subset_insert inter_subset_left))⟩,
    fun ⟨C, hC, heC, h⟩ ↦ ⟨C, hC, heC, (subset_inter h hC.subset_ground).trans ?_⟩⟩
  rw [insert_inter_of_mem (hC.subset_ground heC)]

section Elimination

/-- A generalization of the strong circuit elimination axiom. For finite matroids, this is
  equivalent to the case where `ι` is a singleton type, which is the usual two-circuit version.
  The stronger version is required for axiomatizing infinite matroids via circuits.

  TODO : The same fact should hold if there is no `z` chosen. This is not
    completely straightforward, since the proof really uses `z`, and the
    statement is not trivial if there is no choice available for `z`. The
    quickest proof probably uses closure.    -/
lemma Circuit.strong_multi_elimination {ι : Type*} (hC : M.Circuit C) (x : ι → α)
    (Cs : ι → Set α) (hCs : ∀ i, M.Circuit (Cs i)) (h_mem : ∀ i, x i ∈ C ∩ Cs i)
    (h_unique : ∀ i i', x i ∈ Cs i' → i = i') {z : α} (hz : z ∈ C \ ⋃ i, Cs i) :
    ∃ C', M.Circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ ⋃ i, Cs i) \ range x := by
  set Y := (C ∪ ⋃ x, Cs x) \ insert z (range x) with hY
  have hYE : Y ⊆ M.E := by
    refine diff_subset.trans (union_subset hC.subset_ground ?_)
    exact iUnion_subset fun i ↦ (hCs i).subset_ground
  have h₁ : range x ⊆ M.closure (⋃ i, (Cs i \ {x i}) \ insert z (range x)) := by
    rintro e ⟨i, rfl⟩
    have h' := (hCs i).subset_closure_diff_singleton (x i) (h_mem i).2
    refine mem_of_mem_of_subset h' (M.closure_subset_closure ?_)
    refine subset_iUnion_of_subset i (subset_diff.mpr ⟨rfl.subset, ?_⟩)
    rw [disjoint_iff_forall_ne]
    rintro y hy z (rfl | ⟨j, rfl⟩) rfl
    · exact hz.2 (mem_iUnion_of_mem i hy.1)
    refine hy.2 (mem_singleton_iff.mpr ?_)
    rw [h_unique _ _ hy.1]
  have h₂ : range x ⊆ M.closure Y := by
    refine h₁.trans (M.closure_subset_closure (iUnion_subset fun x ↦ ?_))
    refine diff_subset_diff_left (subset_union_of_subset_right ?_ _)
    exact subset_iUnion_of_subset x diff_subset
  have h₃ : C \ {z} ⊆ M.closure Y := by
    suffices C \ {z} ⊆ C \ insert z (range x) ∪ range x by
      rw [union_diff_distrib] at hY
      convert this.trans (union_subset_union (subset_union_left.trans_eq hY.symm) h₂) using 1
      rw [union_eq_right.mpr]
      exact M.subset_closure Y
    rw [← union_singleton, ← diff_diff, diff_subset_iff, singleton_union, ← insert_union,
      insert_diff_singleton, ← singleton_union, union_assoc, diff_union_self]
    exact subset_union_of_subset_right subset_union_left _
  rw [← M.closure_subset_closure_iff_subset_closure (diff_subset.trans hC.subset_ground)] at h₃
  have h₄ := h₃ (hC.subset_closure_diff_singleton z hz.1)
  obtain (hzY | ⟨C', hC', hzC', hCzY⟩) := (mem_closure_iff_mem_or_exists_circuit hYE).mp h₄
  · exact ((hY.subset hzY).2 (mem_insert z _)).elim
  refine ⟨C', hC', hzC', subset_diff.mpr ⟨?_, ?_⟩⟩
  · exact hCzY.trans (insert_subset (Or.inl hz.1) diff_subset)
  refine disjoint_of_subset_left hCzY ?_
  rw [← singleton_union, disjoint_union_left, disjoint_singleton_left]
  refine ⟨not_mem_subset ?_ hz.2, ?_⟩
  · rintro x' ⟨i, rfl⟩
    exact mem_iUnion_of_mem i (h_mem i).2
  exact disjoint_of_subset_right (subset_insert z _) disjoint_sdiff_left

/-- The strong circuit elimination axiom. For any two circuits `C₁,C₂` and all `e ∈ C₁ ∩ C₂` and
  `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma Circuit.strong_elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (he : e ∈ C₁ ∩ C₂)
    (hf : f ∈ C₁ \ C₂) : ∃ C, M.Circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e} ∧ f ∈ C := by
  obtain ⟨C, hC, hfC, hCss⟩ :=
    @Circuit.strong_multi_elimination _ M C₁ Unit hC₁ (fun _ ↦ e) (fun _ ↦ C₂) (by simpa)
      (by simpa) (by simp) f (by simpa)
  simp only [range_const, iUnion_const] at hCss
  exact ⟨C, hC, hCss, hfC⟩

/-- The circuit elimination axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some
  circuit is contained in `C₁ ∪ C₂ \ {e}`. Traditionally this is stated with the assumption that
  `e ∈ C₁ ∩ C₂`, but it is also true without it. --/
lemma Circuit.elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ C, M.Circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e} := by
  have hne : (C₁ \ C₂).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, diff_eq_empty]
    exact fun hss ↦ h (hC₁.eq_of_subset_circuit hC₂ hss)
  by_cases he₁ : e ∈ C₁
  · by_cases he₂ : e ∈ C₂
    · obtain ⟨C, h⟩ :=  hC₁.strong_elimination hC₂ ⟨he₁,he₂⟩ hne.some_mem
      exact ⟨C, h.1, h.2.1⟩
    exact ⟨C₂, hC₂, subset_diff_singleton subset_union_right he₂⟩
  exact ⟨C₁, hC₁, subset_diff_singleton subset_union_left he₁⟩

end Elimination

lemma Circuit.eq_fundCct_of_subset_insert_indep (hC : M.Circuit C) (hI : M.Indep I)
    (hCI : C ⊆ insert e I) : C = M.fundCct e I := by
  obtain (he | he) := em' <| e ∈ M.E
  · exact False.elim <| ((hI.diff {e}).subset
      (by simpa using subset_diff_singleton hCI (not_mem_subset hC.subset_ground he))).not_dep
      hC.dep
  by_contra! hne
  obtain ⟨hecl, heI⟩ := (hI.insert_dep_iff.1 <| hC.dep.superset hCI)
  obtain ⟨Cf, hCf, hCfss⟩ := hC.elimination (hI.fundCct_circuit hecl heI) hne e
  refine hCf.dep.not_indep (hI.subset (hCfss.trans ?_))
  rw [diff_subset_iff, singleton_union, union_subset_iff, and_iff_right hCI]
  apply fundCct_subset_insert

lemma ext_circuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ C, C ⊆ M₁.E → (M₁.Circuit C ↔ M₂.Circuit C)) : M₁ = M₂ := by
  have h' : ∀ C, M₁.Circuit C ↔ M₂.Circuit C := by
    exact fun C ↦ (em (C ⊆ M₁.E)).elim (h C)
      (fun hC ↦ iff_of_false (mt Circuit.subset_ground hC)
        (mt Circuit.subset_ground (fun hss ↦ hC (hss.trans_eq hE.symm))))
  refine ext_indep hE fun I hI ↦ ?_
  simp_rw [indep_iff_forall_subset_not_circuit hI, h',
    indep_iff_forall_subset_not_circuit (hI.trans_eq hE)]

lemma ext_circuit_not_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h₁ : ∀ ⦃C⦄, M₁.Circuit C → ¬ M₂.Indep C) (h₂ : ∀ ⦃C⦄, M₂.Circuit C → ¬ M₁.Indep C) :
    M₁ = M₂ := by
  refine ext_circuit hE fun C _ ↦ ⟨fun hC ↦ ?_, fun hC ↦ ?_⟩
  · have hC₂ : C ⊆ M₂.E := by rwa [← hE]
    specialize h₁ hC
    rw [not_indep_iff] at h₁
    obtain ⟨C', hC'C, hC'⟩ := h₁.exists_circuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ hC') hC'C]
  specialize h₂ hC
  rw [not_indep_iff] at h₂
  obtain ⟨C', hC'C, hC'⟩ := h₂.exists_circuit_subset
  rwa [← hC.eq_of_not_indep_subset (h₁ hC') hC'C]

lemma map_circuit_iff {β : Type*} {C : Set β} (f : α → β) (hf : M.E.InjOn f) :
    (M.map f hf).Circuit C ↔ ∃ C₀, M.Circuit C₀ ∧ C = f '' C₀ := by
  simp only [circuit_iff, map_dep_iff, forall_exists_index, and_imp]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, h⟩
    refine ⟨C, ⟨hC, fun D hD hDC ↦ ?_⟩, rfl⟩
    rw [← hf.image_eq_image_iff hD.subset_ground hC.subset_ground]
    exact h _ hD rfl (image_subset f hDC)
  rintro ⟨C₀, ⟨h,h'⟩, rfl⟩
  refine ⟨⟨C₀, h, rfl⟩, ?_⟩
  rintro _ D hD rfl hss
  rw [h' hD ((hf.image_subset_image_iff hD.subset_ground h.subset_ground).1 hss)]

lemma mapEquiv_circuit_iff {β : Type*} {C : Set β} (f : α ≃ β) :
    (M.mapEquiv f).Circuit C ↔ M.Circuit (f.symm '' C) := by
  rw [mapEquiv_eq_map, map_circuit_iff]
  exact ⟨by rintro ⟨C, hC, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩

@[simp] lemma uniqueBaseOn_dep_iff : (uniqueBaseOn I E).Dep D ↔ D.Nonempty ∧ ¬ (D ⊆ I) ∧ D ⊆ E := by
  by_cases hD : D ⊆ E
  · simp (config := {contextual := true}) [← not_indep_iff (M := uniqueBaseOn I E) hD, hD,
      nonempty_iff_ne_empty, not_imp_not]
  exact iff_of_false (fun h ↦ hD h.subset_ground) (by simp [hD])

@[simp] lemma loopyOn_dep_iff : (loopyOn E).Dep D ↔ D.Nonempty ∧ D ⊆ E := by
  simp [Dep, nonempty_iff_ne_empty]

@[simp] lemma uniqueBaseOn_circuit_iff : (uniqueBaseOn I E).Circuit C ↔ ∃ e ∈ E \ I, C = {e} := by
  simp only [circuit_iff_dep_forall_diff_singleton_indep, uniqueBaseOn_dep_iff,
    uniqueBaseOn_indep_iff', subset_inter_iff, diff_singleton_subset_iff, mem_diff]
  refine ⟨fun ⟨⟨⟨e,he⟩, hCI, hCE⟩, h2⟩ ↦ ⟨e, ⟨hCE he, fun heI ↦ hCI ?_⟩, ?_⟩, ?_⟩
  · exact (h2 e he).1.trans (insert_subset heI Subset.rfl)
  · suffices hsub : C.Subsingleton from hsub.eq_singleton_of_mem he
    refine fun f hf f' hf' ↦ by_contra fun hne ↦ hCI ?_
    convert subset_inter (h2 f hf).1 (h2 f' hf').1
    aesop
  rintro ⟨e, ⟨heI,heC⟩, rfl⟩
  simp [heI, heC]

@[simp] lemma freeOn_not_circuit {E : Set α} : ¬ (freeOn E).Circuit C := by
  simp [← uniqueBaseOn_self]

@[simp] lemma loopyOn_circuit_iff {E : Set α} : (loopyOn E).Circuit C ↔ ∃ e ∈ E, C = {e} := by
  simp [← uniqueBaseOn_empty]

@[simp] lemma emptyOn_not_circuit : ¬ (emptyOn α).Circuit C := by
  simp [← freeOn_empty]

section Dual

variable {B : Set α}

/-- A cocircuit is a circuit of the dual matroid, or equivalently the complement of a hyperplane -/
abbrev Cocircuit (M : Matroid α) (K : Set α) : Prop := M✶.Circuit K

lemma cocircuit_def : M.Cocircuit K ↔ M✶.Circuit K := Iff.rfl

lemma Cocircuit.circuit (hK : M.Cocircuit K) : M✶.Circuit K :=
  hK

lemma Circuit.cocircuit (hC : M.Circuit C) : M✶.Cocircuit C := by
  rwa [cocircuit_def, dual_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Cocircuit.subset_ground (hC : M.Cocircuit C) : C ⊆ M.E :=
  hC.circuit.subset_ground

@[simp] lemma dual_cocircuit_iff : M✶.Cocircuit C ↔ M.Circuit C := by
  rw [cocircuit_def, dual_dual]

lemma coindep_iff_forall_subset_not_cocircuit :
    M.Coindep X ↔ (∀ K, K ⊆ X → ¬M.Cocircuit K) ∧ X ⊆ M.E :=
  indep_iff_forall_subset_not_circuit'

lemma cocircuit_iff_minimal :
    M.Cocircuit K ↔ Minimal (fun X ↦ ∀ B, M.Base B → (X ∩ B).Nonempty) K := by
  have aux : M✶.Dep = fun X ↦ (∀ B, M.Base B → (X ∩ B).Nonempty) ∧ X ⊆ M.E := by
    ext; apply dual_dep_iff_forall
  rw [cocircuit_def, circuit_def, aux, iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1) fun X hX ↦
    ⟨X ∩ M.E, inter_subset_left, fun B hB ↦ ?_, inter_subset_right⟩
  rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground]
  exact hX B hB

lemma cocircuit_iff_minimal_compl_nonspanning :
    M.Cocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X)) K := by
  convert cocircuit_iff_minimal with K
  simp_rw [spanning_iff_exists_base_subset (S := M.E \ K), not_exists, subset_diff, not_and,
    not_disjoint_iff_nonempty_inter, ← and_imp, and_iff_left_of_imp Base.subset_ground,
      inter_comm K]

lemma cocircuit_iff_minimal_compl_nonspanning' :
    M.Cocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X) ∧ X ⊆ M.E) K := by
  rw [cocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1)
    (fun X hX ↦ ⟨X ∩ M.E, inter_subset_left, by rwa [diff_inter_self_eq_diff], inter_subset_right⟩)

lemma Circuit.cocircuit_disjoint_or_nontrivial_inter (hC : M.Circuit C) (hK : M.Cocircuit K) :
    Disjoint C K ∨ (C ∩ K).Nontrivial := by
  simp_rw [or_iff_not_imp_left, not_disjoint_iff]
  rintro ⟨e, heC, heK⟩
  simp_rw [nontrivial_iff_ne_singleton <| show e ∈ C ∩ K from ⟨heC, heK⟩]
  intro he
  simp_rw [cocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (diff_singleton_sSubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]; nth_rw 1 [← hKe.closure_eq, diff_diff_eq_sdiff_union]
  · refine (M.closure_subset_closure (subset_union_left (t := C))).trans ?_
    rw [union_assoc, singleton_union, insert_eq_of_mem heC, ← closure_union_congr_right
      (hC.closure_diff_singleton_eq_closure e), union_eq_self_of_subset_right]
    rw [← he, diff_self_inter]
    exact diff_subset_diff_left hC.subset_ground
  rw [← he]; exact inter_subset_left.trans hC.subset_ground

lemma Circuit.cocircuit_inter_nontrivial (hC : M.Circuit C) (hK : M.Cocircuit K)
    (hCK : (C ∩ K).Nonempty) : (C ∩ K).Nontrivial := by
  simpa [or_iff_not_imp_left, not_disjoint_iff_nonempty_inter, imp_iff_right hCK] using
    hC.cocircuit_disjoint_or_nontrivial_inter hK

lemma Circuit.inter_cocircuit_ne_singleton (hC : M.Circuit C) (hK : M.Cocircuit K) :
    C ∩ K ≠ {e} :=
  fun h ↦ by simpa [h] using hC.cocircuit_inter_nontrivial hK

lemma dual_rkPos_iff_exists_circuit : M✶.RkPos ↔ ∃ C, M.Circuit C := by
  rw [rkPos_iff_empty_not_base, dual_base_iff, diff_empty, not_iff_comm, not_exists,
    ← ground_indep_iff_base, indep_iff_forall_subset_not_circuit]
  exact ⟨fun h C _ ↦ h C, fun h C hC ↦ h C hC.subset_ground hC⟩

lemma Circuit.dual_rkPos (hC : M.Circuit C) : M✶.RkPos :=
  dual_rkPos_iff_exists_circuit.mpr ⟨C, hC⟩

lemma exists_circuit [RkPos M✶] : ∃ C, M.Circuit C :=
  dual_rkPos_iff_exists_circuit.1 (by assumption)

lemma rk_Pos_iff_exists_cocircuit : M.RkPos ↔ ∃ K, M.Cocircuit K := by
  rw [← dual_dual M, dual_rkPos_iff_exists_circuit, dual_dual M]

/-- The fundamental cocircuit for `B`. Should be used when `B` is a base and `e ∈ B`. -/
def fundCocct (e : α) (B : Set α) := M✶.fundCct e (M✶.E \ B)

lemma fundCocct_cocircuit (he : e ∈ B) (hB : M.Base B) : M.Cocircuit <| M.fundCocct e B := by
  apply hB.compl_base_dual.indep.fundCct_circuit _ (by simp [he])
  rw [hB.compl_base_dual.closure_eq, dual_ground]
  exact hB.subset_ground he

lemma mem_fundCocct (M : Matroid α) (e : α) (B : Set α) : e ∈ M.fundCocct e B :=
  mem_insert _ _

lemma fundCocct_subset_insert_compl (M : Matroid α) (e : α) (B : Set α) :
    M.fundCocct e B ⊆ insert e (M.E \ B) :=
  fundCct_subset_insert ..

lemma fundCocct_inter_eq (M : Matroid α) {B : Set α} (he : e ∈ B) :
    (M.fundCocct e B) ∩ B = {e} := by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocct _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocct_subset_insert_compl _ _)).trans ?_
  simp (config := {contextual := true})

lemma Indep.exists_cocircuit_inter_eq_mem (hI : M.Indep I) (heI : e ∈ I) :
    ∃ K, M.Cocircuit K ∧ K ∩ I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  refine ⟨M.fundCocct e B, fundCocct_cocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff, subset_inter_iff, singleton_subset_iff, and_iff_right
    (mem_fundCocct _ _ _), singleton_subset_iff, and_iff_left heI, ← M.fundCocct_inter_eq (hIB heI)]
  exact inter_subset_inter_right _ hIB


lemma Basis.switch_subset_of_basis_closure {I₀ J₀ : Set α} (hIX : M.Basis I X) (hI₀ : I₀ ⊆ I)
    (hJ₀X : J₀ ⊆ X) (hJ₀ : M.Basis J₀ (M.closure I₀)) : M.Basis ((I \ I₀) ∪ J₀) X := by
  have hdj : Disjoint (I \ I₀) J₀
  · rw [disjoint_iff_forall_ne]
    rintro e heII₀ _ heJ₀ rfl
    refine hIX.indep.not_mem_closure_diff_of_mem heII₀.1 ?_
    refine mem_of_mem_of_subset ?_ <| M.closure_subset_closure <|
      show I₀ ⊆ I \ {e} from subset_diff_singleton hI₀ heII₀.2
    exact hJ₀.subset heJ₀
  refine Indep.basis_of_subset_of_subset_closure ?_
    (union_subset (diff_subset.trans hIX.subset) hJ₀X) ?_

  · rw [indep_iff_forall_subset_not_circuit
      (union_subset (diff_subset.trans hIX.indep.subset_ground) (hJ₀.indep.subset_ground))]
    intro C hCss hC
    obtain ⟨e, heC, heI⟩ : ∃ e ∈ C, e ∈ I \ I₀
    · by_contra! hcon
      exact hC.dep.not_indep <| hJ₀.indep.subset
        fun e heC ↦ Or.elim (hCss heC) (fun h ↦ (hcon _ heC h).elim) id
    refine hIX.indep.not_mem_closure_diff_of_mem heI.1 ?_
    rw [← diff_union_of_subset hI₀, union_diff_distrib, diff_singleton_eq_self heI.2,
      ← closure_union_closure_right_eq, ← M.closure_closure I₀, ← hJ₀.closure_eq_closure,
      closure_union_closure_right_eq]
    refine mem_of_mem_of_subset (hC.mem_closure_diff_singleton_of_mem heC)
      (M.closure_subset_closure ?_)
    rwa [diff_subset_iff, ← union_assoc, union_diff_cancel (by simpa)]

  rw [closure_union_congr_right hJ₀.closure_eq_closure, closure_union_closure_right_eq,
    diff_union_of_subset hI₀]
  exact hIX.subset_closure

end Dual

section Finitary

lemma Circuit.finite [Finitary M] (hC : M.Circuit C) : C.Finite := by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push_neg at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

lemma finitary_iff_forall_circuit_finite : M.Finitary ↔ ∀ C, M.Circuit C → C.Finite := by
  refine ⟨fun _ _ ↦ Circuit.finite, fun h ↦
    ⟨fun I hI ↦ indep_iff_not_dep.2 ⟨fun hd ↦ ?_,fun x hx ↦ ?_⟩⟩ ⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_circuit_subset
    exact hC.dep.not_indep <| hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

lemma Cocircuit.finite [Finitary (M✶)] (hK : M.Cocircuit K) : K.Finite :=
  Circuit.finite hK

/-- In a finitary matroid, each finite set spanned by `X` is spanned by a finite independent
subset of `X`. -/
lemma exists_subset_finite_closure_of_subset_closure {Y : Set α} [M.Finitary]
    (hX : X.Finite) (hXY : X ⊆ M.closure Y) : ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ X ⊆ M.closure I := by

  obtain ⟨J, hJY⟩ := M.exists_basis' Y
  have h_choose : ∀ e ∈ X, ∃ Je, Je ⊆ J ∧ Je.Finite ∧ e ∈ M.closure Je
  · intro e he
    by_cases heY : e ∈ J
    · exact ⟨{e}, by simpa, by simp, M.mem_closure_of_mem' rfl⟩
    obtain ⟨C, hC, heC, hCss⟩ := (mem_closure_iff_exists_circuit_of_not_mem heY).1
      (by rw[hJY.closure_eq_closure]; exact hXY he)
    exact ⟨C \ {e}, by simpa, hC.finite.diff, hC.mem_closure_diff_singleton_of_mem heC⟩

  choose! Js hJs using h_choose

  have hu : ⋃ i ∈ X, Js i ⊆ J := by simpa [iUnion_subset_iff] using fun e heX ↦ (hJs e heX).1
  refine ⟨⋃ i ∈ X, Js i, hu.trans hJY.subset, ?_, hJY.indep.subset hu, fun e heX ↦ ?_⟩
  · exact hX.biUnion fun e he ↦ (hJs e he).2.1

  refine mem_of_mem_of_subset (hJs e heX).2.2 (M.closure_subset_closure ?_)
  exact subset_biUnion_of_mem heX

lemma exists_mem_finite_closure_of_mem_closure {Y : Set α} [M.Finitary]
    (he : e ∈ M.closure Y) : ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ e ∈ M.closure I := by
  simpa using M.exists_subset_finite_closure_of_subset_closure (X := {e}) (by simp [he]) (by simpa)

end Finitary
section Girth

variable {k : ℕ∞}

/-- The `girth` of `M` is the cardinality of the smallest circuit of `M`, or `⊤` if none exists.-/
noncomputable def girth (M : Matroid α) : ℕ∞ := ⨅ C ∈ {C | M.Circuit C}, C.encard

lemma one_le_girth (M : Matroid α) : 1 ≤ M.girth := by
  simp_rw [girth, le_iInf_iff, one_le_encard_iff_nonempty]
  exact fun _ ↦ Circuit.nonempty

lemma Circuit.girth_le_card (hC : M.Circuit C) : M.girth ≤ C.encard := by
  simp only [girth, mem_setOf_eq, iInf_le_iff, le_iInf_iff]
  exact fun b hb ↦ hb C hC

lemma girth_eq_top_iff : M.girth = ⊤ ↔ ∀ C, M.Circuit C → C.Infinite := by
  simp [girth, sInf_eq_top]

@[simp] lemma girth_eq_top_iff_ground_indep [Finitary M] : M.girth = ⊤ ↔ M = freeOn M.E := by
  rw [girth_eq_top_iff, eq_freeOn_iff, indep_iff_forall_subset_not_circuit, and_iff_right rfl]
  exact ⟨fun h C _ hC ↦ h C hC hC.finite, fun h C hC _ ↦ h C hC.subset_ground hC⟩

lemma le_girth_iff : k ≤ M.girth ↔ ∀ C, M.Circuit C → k ≤ C.encard := by
  simp [girth, le_sInf_iff]

lemma exists_circuit_girth (M : Matroid α) [RkPos M✶] :
    ∃ C, M.Circuit C ∧ C.encard = M.girth := by
  obtain ⟨⟨C,hC⟩, (hC' : C.encard = _)⟩ :=
    @ciInf_mem ℕ∞ (setOf M.Circuit) _ _ (nonempty_coe_sort.mpr M.exists_circuit)
      (fun C ↦ (C : Set α).encard)
  exact ⟨C, hC, by rw [hC', girth, iInf_subtype']⟩

@[simp] lemma girth_emptyOn : girth (emptyOn α) = ⊤ := by
  simp [girth]

@[simp] lemma girth_freeOn : girth (freeOn E) = ⊤ := by
  simp [Subset.rfl]

lemma girth_le_iff [RkPos M✶] : M.girth ≤ k ↔ ∃ C, M.Circuit C ∧ C.encard ≤ k :=
  let ⟨C, hC⟩ := M.exists_circuit_girth
  ⟨fun h ↦ ⟨C, hC.1, hC.2.le.trans h⟩, fun ⟨_, hC, hCc⟩ ↦ (hC.girth_le_card).trans hCc⟩

lemma girth_le_iff' {k : ℕ} : M.girth ≤ k ↔ ∃ C : Finset α, M.Circuit C ∧ C.card ≤ k := by
  by_cases h : RkPos M✶
  · simp_rw [girth_le_iff, encard_le_cast_iff]
    aesop
  rw [rkPos_iff_empty_not_base, not_not, empty_base_iff, ← dual_inj, dual_dual] at h
  rw [show M = freeOn M.E by simpa using h]
  simp

lemma girth_loopyOn (hE : E.Nonempty) : girth (loopyOn E) = 1 := by
  have _ : RkPos (loopyOn E)✶ := by rw [loopyOn_dual_eq]; exact freeOn_rkPos hE
  refine le_antisymm ?_ (one_le_girth _)
  simp only [girth_le_iff, loopyOn_circuit_iff]
  exact ⟨{hE.some}, ⟨_, hE.some_mem, rfl⟩, by simp⟩

lemma girth_lt_iff : M.girth < k ↔ ∃ C, M.Circuit C ∧ C.encard < k := by
  simp_rw [girth, iInf_lt_iff, mem_setOf_eq, bex_def]

lemma lt_girth_iff [RkPos M✶] : k < M.girth ↔ ∀ C, M.Circuit C → k < C.encard := by
  rw [lt_iff_not_le, girth_le_iff]
  simp

lemma lt_girth_iff' {k : ℕ} : k < M.girth ↔ ∀ C : Finset α, M.Circuit C → k < C.card := by
  rw [lt_iff_not_le, girth_le_iff']
  simp

lemma indep_of_card_lt_girth (hI : I.encard < M.girth) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  rw [indep_iff_forall_subset_not_circuit]
  exact fun C hCI hC ↦ ((hC.girth_le_card.trans (encard_mono hCI)).trans_lt hI).ne rfl

end Girth
section BasisExchange

variable {I₁ I₂ B₁ B₂ : Set α}

/- Given two bases `B₁,B₂` of `M` and an element `e` of `B₁ \ B₂`, we can find an `f ∈ B₂ \ B₁`
  so that swapping `e` for `f` in yields bases in both `B₁` and `B₂`.  -/
lemma Base.strong_exchange (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.Base (insert e B₂ \ {f}) ∧ M.Base (insert f B₁ \ {e}) := by
  suffices h1 : (∃ f, f ∈ B₂ \ B₁ ∧  M.Indep (insert e B₂ \ {f}) ∧ M.Indep (insert f B₁ \ {e})) by
    obtain ⟨f, hf, h₁, h₂⟩ := h1;
    exact ⟨f, hf, hB₂.exchange_base_of_indep' hf.1 he.2 h₁,
      hB₁.exchange_base_of_indep' he.1 hf.2 h₂⟩
  have he₁ : e ∈ M.closure B₂ \ B₂ := by
    rw [hB₂.closure_eq]; exact ⟨hB₁.subset_ground he.1, he.2⟩
  simp_rw [← hB₂.indep.mem_fundCct_iff he₁.1 he₁.2]
  by_contra! h

  have hC := hB₂.indep.fundCct_circuit he₁.1 he₁.2
  have hCss : M.fundCct e B₂ \ {e} ⊆ B₂ := by
    rw [diff_subset_iff, singleton_union]; exact fundCct_subset_insert ..

  have hclosure : M.fundCct e B₂ ⊆ M.closure (B₁ \ {e}) := by
    refine (hC.subset_closure_diff_singleton e).trans
      (closure_subset_closure_of_subset_closure (fun f hf ↦ ?_))
    have hef : f ≠ e := by rintro rfl; exact hf.2 rfl
    rw [(hB₁.indep.diff {e}).mem_closure_iff, dep_iff, insert_subset_iff,
      and_iff_left (diff_subset.trans hB₁.subset_ground), or_iff_not_imp_right, mem_diff,
      and_iff_left (hC.subset_ground hf.1), mem_singleton_iff,
      and_iff_left hef, insert_diff_singleton_comm hef]
    exact fun hfB₁ ↦ h _ ⟨hCss hf,hfB₁⟩ (diff_subset hf)

  exact hB₁.indep.not_mem_closure_diff_of_mem he.1 (hclosure (mem_fundCct _ _ _))

/- Given two bases `I₁,I₂` of `X` and an element `e` of `I₁ \ I₂`, we can find an `f ∈ I₂ \ I₁`
  so that swapping `e` for `f` in yields bases for `X` in both `I₁` and `I₂`.  -/
lemma Basis.strong_exchange (hI₁ : M.Basis I₁ X) (hI₂ : M.Basis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.Basis (insert e I₂ \ {f}) X ∧ M.Basis (insert f I₁ \ {e}) X := by
  obtain ⟨f, hf, h₁, h₂⟩ := hI₁.base_restrict.strong_exchange hI₂.base_restrict he
  rw [base_restrict_iff] at h₁ h₂
  exact ⟨f, hf, h₁, h₂⟩

lemma Base.rev_exchange (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.Base (insert e B₂ \ {f}) :=
  (hB₁.strong_exchange hB₂ he).imp fun _ ⟨hf, h, _⟩ ↦ ⟨hf, h⟩

lemma Basis.rev_exchange (hI₁ : M.Basis I₁ X) (hI₂ : M.Basis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.Basis (insert e I₂ \ {f}) X :=
  (hI₁.strong_exchange hI₂ he).imp
    (by simp only [mem_diff, mem_insert_iff, mem_singleton_iff]; tauto)

end BasisExchange


end Matroid
