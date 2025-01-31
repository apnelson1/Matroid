import Matroid.ForMathlib.Card
import Mathlib.Data.Matroid.Circuit
import Matroid.ForMathlib.Matroid.Basic

/-!
  A `Circuit` of a matroid is a minimal dependent set.
-/

variable {α : Type*} {M : Matroid α} {C C' I X K C₁ C₂ R E D : Set α} {e f x y : α}

open Set Set.Notation
namespace Matroid


lemma exists_circuit_of_mem_closure (he : e ∈ M.closure X) (heX : e ∉ X) :
    ∃ C ⊆ insert e X, M.Circuit C ∧ e ∈ C :=
  let ⟨I, hI⟩ := M.exists_basis' X
  ⟨_, (fundCircuit_subset_insert ..).trans (insert_subset_insert hI.subset),
    hI.indep.fundCircuit_circuit (by rwa [hI.closure_eq_closure]) (not_mem_subset
    hI.subset heX), M.mem_fundCircuit e I⟩

lemma mem_closure_iff_exists_circuit (he : e ∉ X) :
    e ∈ M.closure X ↔ ∃ C ⊆ insert e X, M.Circuit C ∧ e ∈ C :=
  ⟨fun h ↦ exists_circuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ ↦ mem_of_mem_of_subset
    (hC.mem_closure_diff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩

section Elimination

variable {ι : Type*} (x : ι → α) (Is Cs : ι → Set α) {z : α} {J : Set α}

/-- A version of `Matroid.Circuit.strong_multi_elimination` that is phrased using insertion. -/
lemma strong_multi_elimination_insert (h_not_mem : ∀ i, x i ∉ Is i)
    (hCs : ∀ i, M.Circuit (insert (x i) (Is i))) (hC : M.Circuit (J ∪ range x)) (hzJ : z ∈ J)
    (hzI : ∀ i, z ∉ Is i) : ∃ C', M.Circuit C' ∧ z ∈ C' ∧ C' ⊆ J ∪ ⋃ i, Is i := by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `Is` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simpa [range_eq_empty] using hC, hzJ, by simp⟩
  suffices hcl : z ∈ M.closure ((⋃ i, Is i) ∪ (J \ {z}))
  · rw [mem_closure_iff_exists_circuit (by simp [hzI])] at hcl
    obtain ⟨C', hC'ss, hC', hzC'⟩ := hcl
    refine ⟨C', hC', hzC', ?_⟩
    rwa [union_comm, ← insert_union, insert_diff_singleton, insert_eq_of_mem hzJ] at hC'ss
  replace hCs := show ∀ (i : ι), M.closure (Is i) = M.closure ({x i} ∪ (Is i))
    by simpa [diff_singleton_eq_self (h_not_mem _)] using
      fun i ↦ (hCs i).closure_diff_singleton_eq (x i)
  -- This is true because each `Is i` spans `x i` and `(range x) ∪ (J \ {z})` spans `z`.
  rw [closure_union_congr_left <| closure_iUnion_congr _ _ hCs, iUnion_union_distrib,
    iUnion_singleton_eq_range, union_right_comm]
  refine mem_of_mem_of_subset (hC.mem_closure_diff_singleton_of_mem (.inl hzJ))
    (M.closure_subset_closure (subset_trans ?_ subset_union_left))
  rw [union_diff_distrib, union_comm]
  exact union_subset_union_left _ diff_subset

/-- A generalization of the strong circuit elimination axiom `Matroid.Circuit.strong_elimination`
to an infinite collection of circuits.
This version is one of the axioms when defining infinite matroids via circuits.

TODO : A similar statement will hold even when all mentions of `z` are removed. -/
lemma Circuit.strong_multi_elimination (hC : M.Circuit C) (hCs : ∀ i, M.Circuit (Cs i))
    (h_mem_C : ∀ i, x i ∈ C) (h_mem : ∀ i, x i ∈ Cs i) (h_unique : ∀ ⦃i i'⦄, x i ∈ Cs i' → i = i')
    (hzC : z ∈ C) (hzCs : ∀ i, z ∉ Cs i) :
    ∃ C', M.Circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ ⋃ i, Cs i) \ range x := by
  have hwin := M.strong_multi_elimination_insert x (fun i ↦ (Cs i \ {x i}))
    (J := C \ range x) (z := z) (by simp) (fun i ↦ ?_) ?_ ⟨hzC, ?_⟩ ?_
  · obtain ⟨C', hC', hzC', hC'ss⟩ := hwin
    refine ⟨C', hC', hzC', hC'ss.trans ?_⟩
    refine union_subset (diff_subset_diff_left subset_union_left)
      (iUnion_subset fun i ↦ subset_diff.2
        ⟨diff_subset.trans (subset_union_of_subset_right (subset_iUnion ..) _), ?_⟩)
    rw [disjoint_iff_forall_ne]
    rintro _ he _ ⟨j, hj, rfl⟩ rfl
    obtain rfl : j = i := h_unique he.1
    simp at he
  · simpa [insert_eq_of_mem (h_mem i)] using hCs i
  · rwa [diff_union_self, union_eq_self_of_subset_right]
    rintro _ ⟨i, hi, rfl⟩
    exact h_mem_C i
  · rintro ⟨i, hi, rfl⟩
    exact hzCs _ (h_mem i)
  simp only [mem_diff, mem_singleton_iff, not_and, not_not]
  exact fun i hzi ↦ (hzCs i hzi).elim

/-- The strong circuit elimination axiom. For any two circuits `C₁,C₂` and all `e ∈ C₁ ∩ C₂` and
`f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma Circuit.strong_elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (heC₁ : e ∈ C₁)
    (heC₂ : e ∈ C₂) (hfC₁ : f ∈ C₁) (hfC₂ : f ∉ C₂) :
    ∃ C, M.Circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e} ∧ f ∈ C := by
  obtain ⟨C, hC, hfC, hCss⟩ := hC₁.strong_multi_elimination (fun i : Unit ↦ e) (fun _ ↦ C₂)
    (by simpa) (z := f) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hC, hCss.trans (diff_subset_diff (by simp) (by simp)), hfC⟩

/-- The circuit elimination lemma : for any pair of distinct circuits `C₁,C₂` and any `e`, some
circuit is contained in `(C₁ ∪ C₂) \ {e}`.

This is one of the axioms when definining finitary matroid via circuits;
as an axiom, it is usually stated with the extra assumption that `e ∈ C₁ ∩ C₂`. --/
lemma Circuit.elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ C, M.Circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e} := by
  obtain ⟨f, hf₁, hf₂⟩ : (C₁ \ C₂).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, diff_eq_empty]
    exact fun hss ↦ h (hC₁.eq_of_subset_circuit hC₂ hss)
  by_cases he₁ : e ∈ C₁
  · by_cases he₂ : e ∈ C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, hC₂, subset_diff_singleton subset_union_right he₂⟩
  exact ⟨C₁, hC₁, subset_diff_singleton subset_union_left he₁⟩

end Elimination

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

lemma exists_mem_finite_closure_of_mem_closure {Y : Set α} [M.Finitary] (he : e ∈ M.closure Y) :
    ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ e ∈ M.closure I := by
  by_cases heY : e ∈ Y
  · obtain ⟨J, hJ⟩ := M.exists_basis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCss, hC, heC⟩ := exists_circuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC.finite.diff, hC.diff_singleton_indep heC,
    hC.mem_closure_diff_singleton_of_mem heC⟩

/-- In a finitary matroid, each finite set spanned by `X` is spanned by a finite independent
subset of `X`. -/
lemma exists_subset_finite_closure_of_subset_closure {Y : Set α} [M.Finitary]
    (hX : X.Finite) (hXY : X ⊆ M.closure Y) : ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ X ⊆ M.closure I := by
  refine Set.Finite.induction_on_subset X hX ⟨∅, by simp⟩
    (@fun e Z heX hZX heZ ⟨J, hJY, hJfin, hJ, hJcl⟩ ↦ ?_)
  obtain ⟨K, hKY, hKfin, hK, heK⟩ := exists_mem_finite_closure_of_mem_closure (hXY heX)
  obtain ⟨I, hI⟩ := M.exists_basis (J ∪ K)
  refine ⟨I, hI.subset.trans (union_subset hJY hKY), (hJfin.union hKfin).subset hI.subset, hI.indep,
    (subset_trans (insert_subset ?_ ?_) hI.closure_eq_closure.symm.subset)⟩
  · exact mem_of_mem_of_subset heK (M.closure_subset_closure subset_union_right)
  exact hJcl.trans (M.closure_subset_closure subset_union_left)

end Finitary

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

lemma Cyclic.exists_of_mem (hA : M.Cyclic A) (he : e ∈ A) : ∃ C ⊆ A, M.Circuit C ∧ e ∈ C := by
  obtain ⟨Cs, rfl, h⟩ := hA.exists
  obtain ⟨C, hC, heC⟩ : ∃ t ∈ Cs, e ∈ t := by simpa only [mem_sUnion] using he
  exact ⟨C, subset_sUnion_of_subset Cs C (fun ⦃a⦄ ↦ id) hC, h C hC, heC⟩

lemma Cyclic.dep_of_nonempty (hA : M.Cyclic A) (hA : A.Nonempty) : M.Dep A := by
  obtain ⟨e, he⟩ := hA
  obtain ⟨C, hCA, hC, -⟩ := hA.exists_of_mem he
  exact hC.dep.superset hCA

lemma cyclic_iff_forall_exists : M.Cyclic A ↔ ∀ e ∈ A, ∃ C ⊆ A, M.Circuit C ∧ e ∈ C := by
  refine ⟨fun h e he ↦ h.exists_of_mem he, fun h ↦ ?_⟩
  choose! Cs hCs using h
  simp only [forall_and] at hCs
  refine ⟨Cs '' A, ?_, by simpa using hCs.2.1⟩
  simp only [sUnion_image, subset_antisymm_iff, subset_def (s := A), mem_iUnion, exists_prop,
    iUnion_subset_iff, and_iff_left hCs.1]
  exact fun e he ↦ ⟨e, he, hCs.2.2 _ he⟩

lemma cyclic_iff_forall_mem_closure_diff_singleton :
    M.Cyclic A ↔ ∀ e ∈ A, e ∈ M.closure (A \ {e}) := by
  simp_rw [cyclic_iff_forall_exists]
  refine ⟨fun h e heA ↦ ?_, fun h e heA ↦ ?_⟩
  · simp [heA, h, mem_closure_iff_exists_circuit (show e ∉ A \ {e} by simp)]
  obtain ⟨C, hCss, hC, heC⟩ := exists_circuit_of_mem_closure (h e heA) (by simp)
  exact ⟨C, by simpa [heA] using hCss, hC, heC⟩

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


lemma mem_closure_iff_mem_or_exists_circuit (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ e ∈ X ∨ ∃ C ⊆ insert e X, M.Circuit C ∧ e ∈ C :=
  (em (e ∈ X)).elim (fun heX ↦ by simp [heX, M.mem_closure_of_mem heX])
    fun heX ↦ by rw [mem_closure_iff_exists_circuit heX, or_iff_right heX]

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
  · simp +contextual [← not_indep_iff (M := uniqueBaseOn I E) hD, hD, nonempty_iff_ne_empty,
      not_imp_not]
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
      (hC.closure_diff_singleton_eq e), union_eq_self_of_subset_right]
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
  rw [rkPos_iff, dual_base_iff, diff_empty, not_iff_comm, not_exists,
    ← ground_indep_iff_base, indep_iff_forall_subset_not_circuit]
  exact ⟨fun h C _ ↦ h C, fun h C hC ↦ h C hC.subset_ground hC⟩

lemma Circuit.dual_rkPos (hC : M.Circuit C) : M✶.RkPos :=
  dual_rkPos_iff_exists_circuit.mpr ⟨C, hC⟩

lemma exists_circuit [RkPos M✶] : ∃ C, M.Circuit C :=
  dual_rkPos_iff_exists_circuit.1 (by assumption)

lemma rk_Pos_iff_exists_cocircuit : M.RkPos ↔ ∃ K, M.Cocircuit K := by
  rw [← dual_dual M, dual_rkPos_iff_exists_circuit, dual_dual M]

/-- The fundamental cocircuit for `B`. Should be used when `B` is a base and `e ∈ B`. -/
def fundCocircuit (M : Matroid α) (e : α) (B : Set α) := M✶.fundCircuit e (M✶.E \ B)

lemma fundCocircuit_cocircuit (he : e ∈ B) (hB : M.Base B) :
    M.Cocircuit <| M.fundCocircuit e B := by
  apply hB.compl_base_dual.indep.fundCircuit_circuit _ (by simp [he])
  rw [hB.compl_base_dual.closure_eq, dual_ground]
  exact hB.subset_ground he

lemma mem_fundCocircuit (M : Matroid α) (e : α) (B : Set α) : e ∈ M.fundCocircuit e B :=
  mem_insert _ _

lemma fundCocircuit_subset_insert_compl (M : Matroid α) (e : α) (B : Set α) :
    M.fundCocircuit e B ⊆ insert e (M.E \ B) :=
  fundCircuit_subset_insert ..

lemma fundCocircuit_inter_eq (M : Matroid α) {B : Set α} (he : e ∈ B) :
    (M.fundCocircuit e B) ∩ B = {e} := by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocircuit _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocircuit_subset_insert_compl _ _)).trans ?_
  simp +contextual

lemma Indep.exists_cocircuit_inter_eq_mem (hI : M.Indep I) (heI : e ∈ I) :
    ∃ K, M.Cocircuit K ∧ K ∩ I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  refine ⟨M.fundCocircuit e B, fundCocircuit_cocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff, subset_inter_iff, singleton_subset_iff, and_iff_right
    (mem_fundCocircuit _ _ _), singleton_subset_iff, and_iff_left heI, ← M.fundCocircuit_inter_eq (hIB heI)]
  exact inter_subset_inter_right _ hIB

lemma Base.mem_fundCocircuit_iff_mem_fundCircuit {e f : α} (hB : M.Base B) :
    e ∈ M.fundCocircuit f B ↔ f ∈ M.fundCircuit e B := by
  suffices aux : ∀ {N : Matroid α} {B' : Set α} (hB' : N.Base B') {e f},
      e ∈ N.fundCocircuit f B' → f ∈ N.fundCircuit e B' from
    ⟨fun h ↦ aux hB h , fun h ↦ aux hB.compl_base_dual <| by
      simpa [fundCocircuit, inter_eq_self_of_subset_right hB.subset_ground]⟩
  clear! B M e f
  intro M B hB e f he
  obtain rfl | hne := eq_or_ne e f
  · simp [mem_fundCircuit]
  have hB' : M✶.Base (M✶.E \ B) := hB.compl_base_dual
  obtain hfE | hfE := em' <| f ∈ M.E
  · rw [fundCocircuit, fundCircuit_eq_of_not_mem_ground (by simpa)] at he
    contradiction
  obtain hfB | hfB := em' <| f ∈ B
  · rw [fundCocircuit, fundCircuit_eq_of_mem (by simp [hfE, hfB])] at he
    contradiction
  obtain ⟨heE, heB⟩ : e ∈ M.E \ B :=
    by simpa [hne] using (M.fundCocircuit_subset_insert_compl f B) he
  rw [fundCocircuit, hB'.indep.mem_fundCircuit_iff (by rwa [hB'.closure_eq]) (by simp [hfB])] at he
  rw [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) heB]
  have hB' := (hB'.exchange_base_of_indep' ⟨heE, heB⟩ (by simp [hfE, hfB]) he).compl_base_of_dual
  refine hB'.indep.subset ?_
  simp only [dual_ground, diff_singleton_subset_iff]
  rw [diff_diff_right, inter_eq_self_of_subset_right (by simpa), union_singleton, insert_comm,
    ← union_singleton (s := M.E \ B), ← diff_diff, diff_diff_cancel_left hB.subset_ground]
  simp [hfB]

  -- · simp [mem_fundCircuit, mem_fundCocircuit]
  -- obtain heE | heE := em' <| e ∈ M.E
  -- · rw [fundCircuit_eq_of_not_mem_ground heE, mem_singleton_iff, iff_false_intro hne.symm,
  --     iff_false]
  --   exact fun hmem ↦ by simpa [hne, heE] using fundCocircuit_subset_insert_compl _ _ _ hmem
  --   -- refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, mem_fundCocircuit]⟩
  -- by_cases heB : e ∈ B
  -- · rw [fundCircuit_eq_of_mem heB, mem_singleton_iff]
  --   refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, mem_fundCocircuit]⟩
  --   obtain rfl | ⟨-, heB⟩ := M.fundCocircuit_subset_insert_compl f B h
  --   · rfl
  --   contradiction



  -- rw [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) heB, fundCocircuit,
  --   Indep.mem_fundCircuit_iff]

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


lemma Cocircuit.finite [Finitary (M✶)] (hK : M.Cocircuit K) : K.Finite :=
  Circuit.finite hK



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
  rw [rkPos_iff, not_not, empty_base_iff, ← dual_inj, dual_dual] at h
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
  simp_rw [← hB₂.indep.mem_fundCircuit_iff he₁.1 he₁.2]
  by_contra! h

  have hC := hB₂.indep.fundCircuit_circuit he₁.1 he₁.2
  have hCss : M.fundCircuit e B₂ \ {e} ⊆ B₂ := by
    rw [diff_subset_iff, singleton_union]; exact fundCircuit_subset_insert ..

  have hclosure : M.fundCircuit e B₂ ⊆ M.closure (B₁ \ {e}) := by
    refine (hC.subset_closure_diff_singleton e).trans
      (closure_subset_closure_of_subset_closure (fun f hf ↦ ?_))
    have hef : f ≠ e := by rintro rfl; exact hf.2 rfl
    rw [(hB₁.indep.diff {e}).mem_closure_iff, dep_iff, insert_subset_iff,
      and_iff_left (diff_subset.trans hB₁.subset_ground), or_iff_not_imp_right, mem_diff,
      and_iff_left (hC.subset_ground hf.1), mem_singleton_iff,
      and_iff_left hef, insert_diff_singleton_comm hef]
    exact fun hfB₁ ↦ h _ ⟨hCss hf,hfB₁⟩ (diff_subset hf)

  exact hB₁.indep.not_mem_closure_diff_of_mem he.1 (hclosure (mem_fundCircuit _ _ _))

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
