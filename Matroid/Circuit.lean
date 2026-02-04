import Matroid.ForMathlib.Card
import Mathlib.Combinatorics.Matroid.Circuit -- inefficient import
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Matroid.ForMathlib.Matroid.Basic
import Matroid.ForMathlib.Matroid.Sum
import Matroid.ForMathlib.Set
import Mathlib.Data.Set.Subset
import Batteries.CodeAction.Basic
import Batteries.CodeAction.Misc

/-!
  A `Circuit` of a matroid is a minimal dependent set.
-/

variable {α : Type*} {M : Matroid α} {C C' I X K C₁ C₂ R E D : Set α} {e f x y : α}

open Set Set.Notation Function
namespace Matroid

section Dual

variable {B : Set α}

lemma IsBasis.switch_subset_of_isBasis_closure {I₀ J₀ : Set α} (hIX : M.IsBasis I X) (hI₀ : I₀ ⊆ I)
    (hJ₀X : J₀ ⊆ X) (hJ₀ : M.IsBasis J₀ (M.closure I₀)) : M.IsBasis ((I \ I₀) ∪ J₀) X := by
  have hdj : Disjoint (I \ I₀) J₀ := by
    rw [disjoint_iff_forall_ne]
    rintro e heII₀ _ heJ₀ rfl
    refine hIX.indep.notMem_closure_diff_of_mem heII₀.1 ?_
    refine mem_of_mem_of_subset ?_ <| M.closure_subset_closure <|
      show I₀ ⊆ I \ {e} from subset_diff_singleton hI₀ heII₀.2
    exact hJ₀.subset heJ₀
  refine Indep.isBasis_of_subset_of_subset_closure ?_
    (union_subset (diff_subset.trans hIX.subset) hJ₀X) ?_

  · rw [indep_iff_forall_subset_not_isCircuit
      (union_subset (diff_subset.trans hIX.indep.subset_ground) (hJ₀.indep.subset_ground))]
    intro C hCss hC
    obtain ⟨e, heC, heI⟩ : ∃ e ∈ C, e ∈ I \ I₀
    · by_contra! hcon
      exact hC.dep.not_indep <| hJ₀.indep.subset
        fun e heC ↦ Or.elim (hCss heC) (fun h ↦ (hcon _ heC h).elim) id
    refine hIX.indep.notMem_closure_diff_of_mem heI.1 ?_
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

lemma IsCocircuit.finite [Finitary (M✶)] (hK : M.IsCocircuit K) : K.Finite :=
  IsCircuit.finite hK

section Cyclic

variable {A B : Set α}

lemma IsCircuit.exists_mem_of_mem_isCocircuit (hC : M.IsCircuit C) (hK : M.IsCocircuit K)
    (heC : e ∈ C) (heK : e ∈ K) : ∃ f, f ∈ C ∧ f ∈ K ∧ f ≠ e := by
  obtain ⟨f, hf, hfe⟩ := (hC.isCocircuit_inter_nontrivial hK ⟨e, heC, heK⟩).exists_ne e
  exact ⟨f, hf.1, hf.2, hfe⟩

/-- A cyclic set is a (possibly empty) union of circuits.
This is the same as a complement of a flat in the dual matroid,
and a number of other conditions; see `Matroid.cyclic_tfae`. -/
def Cyclic (M : Matroid α) (A : Set α) : Prop :=
  ∃ Cs : Set (Set α), A = ⋃₀ Cs ∧ ∀ C ∈ Cs, M.IsCircuit C

lemma Cyclic.exists (hA : M.Cyclic A) : ∃ Cs, A = ⋃₀ Cs ∧ ∀ C ∈ Cs, M.IsCircuit C := hA

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Cyclic.subset_ground (hA : M.Cyclic A) : A ⊆ M.E := by
  obtain ⟨Cs, rfl, h⟩ := hA.exists
  simpa using fun C hC ↦ (h C hC).subset_ground

@[simp] lemma empty_cyclic (M : Matroid α) : M.Cyclic ∅ :=
  ⟨∅, by simp⟩

lemma IsCircuit.cyclic (hC : M.IsCircuit C) : M.Cyclic C :=
  ⟨{C}, by simpa⟩

lemma Cyclic.exists_of_mem (hA : M.Cyclic A) (he : e ∈ A) : ∃ C ⊆ A, M.IsCircuit C ∧ e ∈ C := by
  obtain ⟨Cs, rfl, h⟩ := hA.exists
  obtain ⟨C, hC, heC⟩ : ∃ t ∈ Cs, e ∈ t := by simpa only [mem_sUnion] using he
  exact ⟨C, subset_sUnion_of_subset Cs C (fun ⦃a⦄ ↦ id) hC, h C hC, heC⟩

lemma Cyclic.dep_of_nonempty (hA : M.Cyclic A) (hA : A.Nonempty) : M.Dep A := by
  obtain ⟨e, he⟩ := hA
  obtain ⟨C, hCA, hC, -⟩ := hA.exists_of_mem he
  exact hC.dep.superset hCA

lemma cyclic_iff_forall_exists : M.Cyclic A ↔ ∀ e ∈ A, ∃ C ⊆ A, M.IsCircuit C ∧ e ∈ C := by
  refine ⟨fun h e he ↦ h.exists_of_mem he, fun h ↦ ?_⟩
  choose! Cs hCs using h
  simp only [forall_and] at hCs
  refine ⟨Cs '' A, ?_, by simpa using hCs.2.1⟩
  simp only [sUnion_image, subset_antisymm_iff, subset_def (s := A), mem_iUnion, exists_prop,
    iUnion_subset_iff, and_iff_left hCs.1]
  exact fun e he ↦ ⟨e, he, hCs.2.2 _ he⟩

lemma dual_cyclic_iff (hA : A ⊆ M.E := by aesop_mat) : M✶.Cyclic A ↔ M.IsFlat (M.E \ A) := by
  simp_rw [cyclic_iff_forall_exists, ← isCocircuit_def, isFlat_iff_closure_eq,
    subset_antisymm_iff, and_iff_left (M.subset_closure (M.E \ A)), subset_diff,
    and_iff_right (M.closure_subset_ground (M.E \ A)), disjoint_iff_forall_ne]
  simp only [ne_eq, imp_not_comm, forall_eq']
  refine ⟨fun h e heA hecl ↦ ?_, fun h e heA ↦ ?_⟩
  · obtain ⟨C, hCss, hC, heC⟩ := (mem_closure_iff_exists_isCircuit (by simp [heA])).1 hecl
    obtain ⟨K, hKA, hK, heK⟩ := h e heA
    obtain ⟨f, hfC, hfK, hfe⟩ := hC.exists_mem_of_mem_isCocircuit hK heC heK
    specialize hCss hfC
    rw [mem_insert_iff, or_iff_right hfe] at hCss
    exact hCss.2 <| hKA hfK
  obtain ⟨I, hI⟩ := M.exists_isBasis (M.E \ A)
  have heI : e ∉ M.closure I := fun heI ↦ h heA <| M.closure_subset_closure hI.subset heI
  have hi : M.Indep (insert e I) := by exact (hI.indep.notMem_closure_iff.1 heI).1
  obtain ⟨B, hB, hIB⟩ := hi.exists_isBase_superset
  refine ⟨_, ?_, hB.compl_closure_diff_singleton_isCocircuit <| hIB <| mem_insert .., ?_⟩
  · rw [diff_subset_comm]
    refine hI.subset_closure.trans (M.closure_subset_closure ?_)
    rw [subset_diff_singleton_iff, and_iff_left (notMem_subset (M.subset_closure ..) heI)]
    exact (subset_insert ..).trans hIB
  exact ⟨hA heA, hB.indep.notMem_closure_diff_of_mem (hIB (mem_insert ..))⟩

/-- A version of `Matroid.dual_cyclic_iff` where the supportedness assumption is part of the
equivalence rather than the hypothesis. -/
lemma dual_cyclic_iff' : M✶.Cyclic A ↔ M.IsFlat (M.E \ A) ∧ A ⊆ M.E := by
  by_cases hAE : A ⊆ M.E
  · simp [dual_cyclic_iff, hAE]
  exact iff_of_false (mt Cyclic.subset_ground hAE) <| fun h ↦ hAE h.2

lemma cyclic_iff_compl_isFlat_dual (hA : A ⊆ M.E := by aesop_mat) :
    M.Cyclic A ↔ M✶.IsFlat (M.E \ A) := by
  rw [← dual_ground, ← dual_cyclic_iff, dual_dual]

lemma Cyclic.compl_isFlat_dual (hA : M.Cyclic A) : M✶.IsFlat (M.E \ A) := by
  rwa [← dual_dual M, dual_cyclic_iff, dual_ground] at hA

lemma compl_cyclic_iff (hAE : A ⊆ M.E := by aesop_mat) : M.Cyclic (M.E \ A) ↔ M✶.IsFlat A := by
  rw [← dual_dual M, dual_cyclic_iff, dual_dual, dual_ground, diff_diff_cancel_left hAE]

lemma compl_cyclic_dual_iff {F : Set α} (hF : F ⊆ M.E := by aesop_mat) :
    M✶.Cyclic (M.E \ F) ↔ M.IsFlat F := by
  rw [dual_cyclic_iff, diff_diff_cancel_left hF]

lemma IsFlat.compl_cyclic_dual {F : Set α} (hF : M.IsFlat F) : M✶.Cyclic (M.E \ F) := by
  rwa [cyclic_iff_compl_isFlat_dual, dual_dual, dual_ground, diff_diff_cancel_left hF.subset_ground]

lemma isFlat_dual_iff_compl_cyclic {F : Set α} (hF : F ⊆ M.E := by aesop_mat) :
    M✶.IsFlat F ↔ M.Cyclic (M.E \ F) := by
  rw [cyclic_iff_compl_isFlat_dual, diff_diff_cancel_left hF]

lemma cyclic_tfae : List.TFAE [
    M.Cyclic A,
    ∃ Cs, A = ⋃₀ Cs ∧ ∀ C ∈ Cs, M.IsCircuit C,
    ∀ e ∈ A, ∃ C ⊆ A, M.IsCircuit C ∧ e ∈ C,
    ∀ e ∈ A, e ∈ M.closure (A \ {e}),
    (∀ K, M.IsCocircuit K → (A ∩ K).encard ≠ 1) ∧ A ⊆ M.E,
    M✶.IsFlat (M.E \ A) ∧ A ⊆ M.E] := by
  simp only [Ne, encard_eq_one, not_exists]
  tfae_have 1 <-> 2 := Iff.rfl
  tfae_have 1 <-> 3 := by rw [cyclic_iff_forall_exists]
  tfae_have 3 <-> 4 := by
    convert Iff.rfl with e heA
    simp_rw [mem_closure_iff_exists_isCircuit (show e ∉ A \ {e} by simp), insert_diff_singleton,
      insert_eq_of_mem heA]
  tfae_have 1 <-> 6 := by
    rw [← dual_dual M, dual_cyclic_iff', dual_dual, dual_dual, dual_ground]
  tfae_have 5 <-> 6 := by
    simp_rw [isCocircuit_def, and_congr_left_iff, isFlat_iff_closure_eq,
      subset_antisymm_iff (b := M.E \ A), and_iff_left (M✶.subset_closure (M.E \ A)), subset_diff,
      disjoint_right]
    set N := M✶
    refine fun hAE : A ⊆ N.E ↦ ⟨fun h ↦ ⟨N.closure_subset_ground .., fun e heA hcl ↦ ?_⟩,
      fun h C hC e hAKe ↦ ?_⟩
    · obtain ⟨C, hCss, hC, heC⟩ := exists_isCircuit_of_mem_closure hcl (by simp [heA])
      refine h C hC e <| subset_antisymm (fun f hf ↦ ?_) (by simp [heA, heC])
      obtain rfl | hf' := hCss hf.2
      · rfl
      exact (hf'.2 hf.1).elim
    obtain ⟨heA, heC⟩ := hAKe.symm.subset rfl
    refine h.2 heA <| mem_of_mem_of_subset (hC.mem_closure_diff_singleton_of_mem heC) ?_
    rw [← hAKe, diff_inter_self_eq_diff]
    exact N.closure_subset_closure <| diff_subset_diff_left hC.subset_ground
  tfae_finish

lemma cyclic_iff_forall_inter_isCocircuit_encard_ne (hAE : A ⊆ M.E := by aesop_mat) :
    M.Cyclic A ↔ ∀ K, M.IsCocircuit K → (A ∩ K).encard ≠ 1 := by
  rw [cyclic_tfae.out 0 4 rfl rfl, and_iff_left hAE]

lemma cyclic_iff_forall_mem_closure_diff_singleton :
    M.Cyclic A ↔ ∀ e ∈ A, e ∈ M.closure (A \ {e}) :=
  cyclic_tfae.out 0 3

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

lemma Cyclic.restrict (hA : M.Cyclic A) (hAR : A ⊆ R) : (M ↾ R).Cyclic A := by
  obtain ⟨Cs, rfl, hCs⟩ := hA
  exact ⟨Cs, rfl, fun C hC ↦ (hCs C hC).isCircuit_restrict_of_subset <|
    (subset_sUnion_of_mem hC).trans hAR⟩

lemma Cyclic.of_restrict {R : Set α} (hA : (M ↾ R).Cyclic A) (hR : R ⊆ M.E := by aesop_mat) :
    M.Cyclic A := by
  obtain ⟨Cs, rfl, hCs⟩ := hA
  exact ⟨Cs, rfl, fun C hC ↦ ((restrict_isCircuit_iff hR).1 (hCs C hC)).1⟩

lemma restrict_cyclic_iff (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Cyclic A ↔ M.Cyclic A ∧ A ⊆ R :=
  ⟨fun h ↦ ⟨h.of_restrict, h.subset_ground⟩, fun h ↦ h.1.restrict h.2⟩

/-- A cyclic set is the union of its fundamental circuits for some basis. -/
lemma Cyclic.eq_biUnion_fundCircuits (hA : M.Cyclic A) (hI : M.IsBasis I A) :
    A = ⋃ e ∈ (A \ I), M.fundCircuit e I := by
  -- By proving the lemma in the restriction to `A`, we may assume that `A = M.E`.
  wlog hAE : A = M.E generalizing M with aux
  · convert aux (hA.restrict rfl.subset) (hI.isBasis_restrict_of_subset rfl.subset) rfl using 4
      with e he
    rw [fundCircuit_restrict hI.subset he.1 hA.subset_ground]
  -- The only nontrivial thing to show is that each `e ∈ I` is in the union of the `fundCircuit`s.
  obtain rfl := hAE
  rw [isBasis_ground_iff] at hI
  simp only [mem_diff, subset_antisymm_iff, subset_def (s := M.E), mem_iUnion, exists_prop,
    iUnion_subset_iff, and_imp]
  refine ⟨fun e he ↦ ?_, fun e he _ ↦ M.fundCircuit_subset_ground he⟩
  obtain heI | heI := em' <| e ∈ I
  · exact ⟨e, ⟨he, heI⟩, mem_fundCircuit ..⟩
  -- Since `A` is cyclic, there exists `f ≠ e` in the fundamental cocircuit of `e` and `I`;
  -- this implies that `e` is in the fundamental circuit for `f`.
  obtain ⟨C, -, hC, heC⟩ := cyclic_iff_forall_exists.1 hA e he
  obtain ⟨f, ⟨hfC, hfK⟩, hfe⟩ :=
    (hC.isCocircuit_inter_nontrivial (M.fundCocircuit_isCocircuit heI hI)
    ⟨e, heC, mem_insert ..⟩).exists_ne e
  refine ⟨f, ⟨hC.subset_ground hfC, fun hfI ↦ hfe ?_⟩,
    hI.mem_fundCocircuit_iff_mem_fundCircuit.1 hfK⟩
  rwa [← mem_singleton_iff, ← M.fundCocircuit_inter_eq heI, mem_inter_iff, and_iff_left hfI]

/-- Every nonempty cyclic set is the union of a circuit and a smaller cyclic set.
This can be used for induction. -/
lemma Cyclic.exists_eq_union_isCircuit_cyclic_ssubset (hA : M.Cyclic A) (hne : A.Nonempty) :
    ∃ C A₀, C ⊆ A ∧ A₀ ⊂ A ∧ M.IsCircuit C ∧ M.Cyclic A₀ ∧ C ∪ A₀ = A := by
  -- Pick a basis `I`, so `A` is the union of fundamental circuits for `I`.
  -- Each element of `A \ I` is in exactly one of these circuits,
  -- so removing one such circuit `C` from the union makes `A` strictly smaller.
  obtain ⟨I, hI⟩ := M.exists_isBasis A
  have h_eq := hA.eq_biUnion_fundCircuits hI
  obtain h_empt | ⟨e, he⟩ := (A \ I).eq_empty_or_nonempty
  · simp_rw [h_empt, mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at h_eq
    exact (hne.ne_empty h_eq).elim
  have aux {x} : x ∈ A \ I → M.IsCircuit (M.fundCircuit x I) :=
    fun hx ↦ hI.indep.fundCircuit_isCircuit (hI.subset_closure hx.1) hx.2
  refine ⟨M.fundCircuit e I, ⋃ x ∈ ((A \ I) \ {e}), M.fundCircuit x I, ?_, ?_, aux he, ?_, ?_⟩
  · rw [h_eq]
    exact subset_iUnion₂_of_subset e he rfl.subset
  · refine ssubset_of_ssubset_of_eq
      ((biUnion_subset_biUnion_left diff_subset).ssubset_of_mem_notMem (a := e) ?_ ?_) h_eq.symm
    · exact mem_biUnion he <| mem_insert ..
    simp only [mem_diff, mem_singleton_iff, mem_iUnion, exists_prop, not_exists, not_and, and_imp,
      not_imp_not]
    refine fun x hxA hxE he' ↦ ?_
    obtain rfl | heI := (fundCircuit_subset_insert ..) he'
    · rfl
    exact (he.2 heI).elim
  · exact Cyclic.biUnion fun i hi ↦ (aux hi.1).cyclic
  rw [← biUnion_insert (t := fun x ↦ M.fundCircuit x I), insert_diff_singleton,
    insert_eq_of_mem he, ← h_eq]

/-- A minimal nonempty cyclic set is a circuit. -/
lemma minimal_nonempty_cyclic_iff_isCircuit :
    Minimal (fun A ↦ M.Cyclic A ∧ A.Nonempty) C ↔ M.IsCircuit C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨C', C₀, hC'C, hC₀C, hC', hC₀, rfl⟩ :=
      h.prop.1.exists_eq_union_isCircuit_cyclic_ssubset h.prop.2
    obtain rfl | hne := C₀.eq_empty_or_nonempty
    · simpa
    exact False.elim <| h.not_prop_of_ssubset hC₀C ⟨hC₀, hne⟩
  rw [minimal_iff_forall_ssubset, and_iff_right h.cyclic, and_iff_right h.nonempty]
  exact fun I hIC hI ↦ (hI.1.dep_of_nonempty hI.2).not_indep (h.ssubset_indep hIC)

end Cyclic

lemma mem_closure_iff_mem_or_exists_isCircuit (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ e ∈ X ∨ ∃ C ⊆ insert e X, M.IsCircuit C ∧ e ∈ C :=
  (em (e ∈ X)).elim (fun heX ↦ by simp [heX, M.mem_closure_of_mem heX])
    fun heX ↦ by rw [mem_closure_iff_exists_isCircuit heX, or_iff_right heX]

lemma map_isCircuit_iff {β : Type*} {C : Set β} (f : α → β) (hf : M.E.InjOn f) :
    (M.map f hf).IsCircuit C ↔ ∃ C₀, M.IsCircuit C₀ ∧ C = f '' C₀ := by
  simp only [isCircuit_iff, map_dep_iff, forall_exists_index, and_imp]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, h⟩
    refine ⟨C, ⟨hC, fun D hD hDC ↦ ?_⟩, rfl⟩
    rw [← hf.image_eq_image_iff hD.subset_ground hC.subset_ground]
    exact h _ hD rfl (image_mono hDC)
  rintro ⟨C₀, ⟨h,h'⟩, rfl⟩
  refine ⟨⟨C₀, h, rfl⟩, ?_⟩
  rintro _ D hD rfl hss
  rw [h' hD ((hf.image_subset_image_iff hD.subset_ground h.subset_ground).1 hss)]

lemma mapEquiv_isCircuit_iff {β : Type*} {C : Set β} (f : α ≃ β) :
    (M.mapEquiv f).IsCircuit C ↔ M.IsCircuit (f.symm '' C) := by
  rw [mapEquiv_eq_map, map_isCircuit_iff]
  exact ⟨by rintro ⟨C, hC, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩

@[simp]
lemma restrictSubtype_ground_isCircuit_iff {C : Set M.E} :
    (M.restrictSubtype M.E).IsCircuit C ↔ M.IsCircuit ((↑) '' C) := by
  rw [show M.IsCircuit ((↑) '' C) ↔ (M ↾ M.E).IsCircuit ((↑) '' C) by simp,
    ← M.map_val_restrictSubtype_eq M.E, map_isCircuit_iff]
  simp

@[simp] lemma uniqueBaseOn_dep_iff : (uniqueBaseOn I E).Dep D ↔ D.Nonempty ∧ ¬ (D ⊆ I) ∧ D ⊆ E := by
  by_cases hD : D ⊆ E
  · simp +contextual [← not_indep_iff (M := uniqueBaseOn I E) hD, hD, nonempty_iff_ne_empty,
      not_imp_not]
  exact iff_of_false (fun h ↦ hD h.subset_ground) (by simp [hD])

@[simp] lemma loopyOn_dep_iff : (loopyOn E).Dep D ↔ D.Nonempty ∧ D ⊆ E := by
  simp [Dep, nonempty_iff_ne_empty]

@[simp] lemma uniqueBaseOn_isCircuit_iff :
    (uniqueBaseOn I E).IsCircuit C ↔ ∃ e ∈ E \ I, C = {e} := by
  simp only [isCircuit_iff_dep_forall_diff_singleton_indep, uniqueBaseOn_dep_iff,
    uniqueBaseOn_indep_iff', subset_inter_iff, diff_singleton_subset_iff, mem_diff]
  refine ⟨fun ⟨⟨⟨e,he⟩, hCI, hCE⟩, h2⟩ ↦ ⟨e, ⟨hCE he, fun heI ↦ hCI ?_⟩, ?_⟩, ?_⟩
  · exact (h2 e he).1.trans (insert_subset heI Subset.rfl)
  · suffices hsub : C.Subsingleton from hsub.eq_singleton_of_mem he
    refine fun f hf f' hf' ↦ by_contra fun hne ↦ hCI ?_
    convert subset_inter (h2 f hf).1 (h2 f' hf').1
    aesop
  rintro ⟨e, ⟨heI,heC⟩, rfl⟩
  simp [heI, heC]

@[simp] lemma freeOn_not_isCircuit {E : Set α} : ¬ (freeOn E).IsCircuit C := by
  simp [← uniqueBaseOn_self]

@[simp] lemma loopyOn_isCircuit_iff {E : Set α} : (loopyOn E).IsCircuit C ↔ ∃ e ∈ E, C = {e} := by
  simp [← uniqueBaseOn_empty]

@[simp] lemma emptyOn_not_isCircuit : ¬ (emptyOn α).IsCircuit C := by
  simp [← freeOn_empty]

lemma IsCircuit.of_isRestriction {N : Matroid α} (hC : N.IsCircuit C) (hNM : N ≤r M) :
    M.IsCircuit C := by
  obtain ⟨R, hR, rfl⟩ := hNM
  rw [restrict_isCircuit_iff] at hC
  exact hC.1

section Girth

variable {k : ℕ∞}

/-- The `girth` of `M` is the cardinality of the smallest circuit of `M`, or `⊤` if none exists.-/
noncomputable def girth (M : Matroid α) : ℕ∞ := ⨅ C ∈ {C | M.IsCircuit C}, C.encard

lemma one_le_girth (M : Matroid α) : 1 ≤ M.girth := by
  simp_rw [girth, le_iInf_iff, one_le_encard_iff_nonempty]
  exact fun _ ↦ IsCircuit.nonempty

lemma IsCircuit.girth_le_card (hC : M.IsCircuit C) : M.girth ≤ C.encard := by
  simp only [girth, mem_setOf_eq, iInf_le_iff, le_iInf_iff]
  exact fun b hb ↦ hb C hC

lemma girth_eq_top_iff : M.girth = ⊤ ↔ ∀ C, M.IsCircuit C → C.Infinite := by
  simp [girth]

@[simp] lemma girth_eq_top_iff_ground_indep [Finitary M] : M.girth = ⊤ ↔ M = freeOn M.E := by
  rw [girth_eq_top_iff, eq_freeOn_iff, indep_iff_forall_subset_not_isCircuit, and_iff_right rfl]
  exact ⟨fun h C _ hC ↦ h C hC hC.finite, fun h C hC _ ↦ h C hC.subset_ground hC⟩

lemma le_girth_iff : k ≤ M.girth ↔ ∀ C, M.IsCircuit C → k ≤ C.encard := by
  simp [girth]

lemma exists_isCircuit_girth (M : Matroid α) [RankPos M✶] :
    ∃ C, M.IsCircuit C ∧ C.encard = M.girth := by
  obtain ⟨⟨C,hC⟩, (hC' : C.encard = _)⟩ :=
    @ciInf_mem ℕ∞ (setOf M.IsCircuit) _ _ (nonempty_coe_sort.mpr M.exists_isCircuit)
      (fun C ↦ (C : Set α).encard)
  exact ⟨C, hC, by rw [hC', girth, iInf_subtype']⟩

lemma girth_le_eRank_add_one (M : Matroid α) [RankPos M✶] :
    M.girth ≤ M.eRank + 1 := by
  obtain ⟨C, hC, hcard⟩ := M.exists_isCircuit_girth
  grw [← hcard, ← M.eRk_le_eRank C, hC.eRk_add_one_eq]

@[simp] lemma girth_emptyOn : girth (emptyOn α) = ⊤ := by
  simp [girth]

@[simp] lemma girth_freeOn : girth (freeOn E) = ⊤ := by
  simp

lemma girth_le_iff [RankPos M✶] : M.girth ≤ k ↔ ∃ C, M.IsCircuit C ∧ C.encard ≤ k :=
  let ⟨C, hC⟩ := M.exists_isCircuit_girth
  ⟨fun h ↦ ⟨C, hC.1, hC.2.le.trans h⟩, fun ⟨_, hC, hCc⟩ ↦ (hC.girth_le_card).trans hCc⟩

lemma girth_le_iff' {k : ℕ} : M.girth ≤ k ↔ ∃ C : Finset α, M.IsCircuit C ∧ C.card ≤ k := by
  by_cases h : RankPos M✶
  · simp_rw [girth_le_iff, encard_le_cast_iff]
    aesop
  rw [rankPos_iff, not_not, empty_isBase_iff, ← dual_inj, dual_dual] at h
  rw [show M = freeOn M.E by simpa using h]
  simp

lemma girth_loopyOn (hE : E.Nonempty) : girth (loopyOn E) = 1 := by
  have _ : RankPos (loopyOn E)✶ := by rw [loopyOn_dual_eq]; exact freeOn_rankPos hE
  refine le_antisymm ?_ (one_le_girth _)
  simp only [girth_le_iff, loopyOn_isCircuit_iff]
  exact ⟨{hE.some}, ⟨_, hE.some_mem, rfl⟩, by simp⟩

lemma girth_lt_iff : M.girth < k ↔ ∃ C, M.IsCircuit C ∧ C.encard < k := by
  simp_rw [girth, iInf_lt_iff, mem_setOf_eq, bex_def]

lemma lt_girth_iff [RankPos M✶] : k < M.girth ↔ ∀ C, M.IsCircuit C → k < C.encard := by
  rw [lt_iff_not_ge, girth_le_iff]
  simp

lemma lt_girth_iff' {k : ℕ} : k < M.girth ↔ ∀ C : Finset α, M.IsCircuit C → k < C.card := by
  rw [lt_iff_not_ge, girth_le_iff']
  simp

lemma indep_of_card_lt_girth (hI : I.encard < M.girth) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  rw [indep_iff_forall_subset_not_isCircuit]
  exact fun C hCI hC ↦ ((hC.girth_le_card.trans (encard_mono hCI)).trans_lt hI).ne rfl

lemma indep_of_eRk_add_one_lt_girth (hI : M.eRk I + 1 < M.girth) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  rw [indep_iff_forall_subset_not_isCircuit]
  refine fun C hCI hC ↦ ?_
  grw [hC.girth_le_card, ← hC.eRk_add_one_eq, M.eRk_mono hCI] at hI
  exact hI.ne rfl

lemma IsRestriction.girth_ge {N M : Matroid α} (h : N ≤r M) : M.girth ≤ N.girth :=
  le_girth_iff.2 fun _ hC ↦ IsCircuit.girth_le_card <| hC.of_isRestriction h

lemma girth_le_girth_restrict (M : Matroid α) (hR : R ⊆ M.E) : M.girth ≤ (M ↾ R).girth :=
  (restrict_isRestriction _ _ hR).girth_ge

lemma Dep.isCircuit_of_encard_le_girth (hX : M.Dep X) (hXfin : X.Finite)
    (hXcard : X.encard ≤ M.girth) : M.IsCircuit X := by
  obtain ⟨C, hCX, hC⟩ := hX.exists_isCircuit_subset
  rwa [← hXfin.eq_of_subset_of_encard_le' hCX (hXcard.trans hC.girth_le_card)]

lemma Dep.isCircuit_of_encard_lt_girth_add_one (hX : M.Dep X) (hXcard : X.encard < M.girth + 1) :
    M.IsCircuit X := by
  refine hX.isCircuit_of_encard_le_girth ?_ ?_
  · rw [← encard_lt_top_iff]
    exact hXcard.trans_le le_top
  exact Order.le_of_lt_add_one hXcard

lemma Dep.girth_le_card (hX : M.Dep X) : M.girth ≤ X.encard := by
  obtain ⟨C, hCX, hC⟩ := hX.exists_isCircuit_subset
  grw [← encard_le_encard hCX, hC.girth_le_card]

lemma Dep.girth_le_eRk_add_one (hX : M.Dep X) : M.girth ≤ M.eRk X + 1 := by
  obtain ⟨C, hCX, hC⟩ := hX.exists_isCircuit_subset
  grw [← M.eRk_mono hCX, hC.eRk_add_one_eq, hC.girth_le_card]

end Girth
section IsBasisExchange

variable {I₁ I₂ B₁ B₂ : Set α}

/- Given two bases `B₁,B₂` of `M` and an element `e` of `B₁ \ B₂`, we can find an `f ∈ B₂ \ B₁`
  so that swapping `e` for `f` in yields bases in both `B₁` and `B₂`.  -/
lemma IsBase.strong_exchange (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.IsBase (insert e B₂ \ {f}) ∧ M.IsBase (insert f B₁ \ {e}) := by
  suffices h1 : (∃ f, f ∈ B₂ \ B₁ ∧  M.Indep (insert e B₂ \ {f}) ∧ M.Indep (insert f B₁ \ {e})) by
    obtain ⟨f, hf, h₁, h₂⟩ := h1;
    exact ⟨f, hf, hB₂.exchange_isBase_of_indep' hf.1 he.2 h₁,
      hB₁.exchange_isBase_of_indep' he.1 hf.2 h₂⟩
  have he₁ : e ∈ M.closure B₂ \ B₂ := by
    rw [hB₂.closure_eq]; exact ⟨hB₁.subset_ground he.1, he.2⟩
  simp_rw [← hB₂.indep.mem_fundCircuit_iff he₁.1 he₁.2]
  by_contra! h

  have hC := hB₂.indep.fundCircuit_isCircuit he₁.1 he₁.2
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

  exact hB₁.indep.notMem_closure_diff_of_mem he.1 (hclosure (mem_fundCircuit _ _ _))

/- Given two bases `I₁,I₂` of `X` and an element `e` of `I₁ \ I₂`, we can find an `f ∈ I₂ \ I₁`
  so that swapping `e` for `f` in yields bases for `X` in both `I₁` and `I₂`.  -/
lemma IsBasis.strong_exchange (hI₁ : M.IsBasis I₁ X) (hI₂ : M.IsBasis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.IsBasis (insert e I₂ \ {f}) X ∧ M.IsBasis (insert f I₁ \ {e}) X := by
  obtain ⟨f, hf, h₁, h₂⟩ := hI₁.isBase_restrict.strong_exchange hI₂.isBase_restrict he
  rw [isBase_restrict_iff] at h₁ h₂
  exact ⟨f, hf, h₁, h₂⟩

lemma IsBase.rev_exchange (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.IsBase (insert e B₂ \ {f}) :=
  (hB₁.strong_exchange hB₂ he).imp fun _ ⟨hf, h, _⟩ ↦ ⟨hf, h⟩

lemma IsBasis.rev_exchange (hI₁ : M.IsBasis I₁ X) (hI₂ : M.IsBasis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.IsBasis (insert e I₂ \ {f}) X :=
  (hI₁.strong_exchange hI₂ he).imp
    (by simp only [mem_diff]; tauto)

end IsBasisExchange

section Sum

variable {ι : Type*} {α : ι → Type*} (M : (i : ι) → Matroid (α i))

lemma sigma_isCircuit_iff {C : Set ((i : ι) × α i)} :
    (Matroid.sigma M).IsCircuit C ↔ ∃ i C₀, (M i).IsCircuit C₀ ∧ C = Sigma.mk i '' C₀ := by
  wlog hC : C ⊆ (Matroid.sigma M).E
  · refine iff_of_false (fun h ↦ hC h.subset_ground) ?_
    rintro ⟨i, C₀, hC₀, rfl⟩
    simp [hC₀.subset_ground] at hC
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have aux : ∀ {e f}, e ∈ C → f ∈ C → e.1 = f.1 := by
      rintro ⟨i,e⟩ ⟨j,f⟩ he hf
      refine by_contra fun (hij : i ≠ j) ↦ h.not_indep ?_
      simp only [sigma_indep_iff]
      intro k
      obtain rfl | hne := eq_or_ne i k
      · refine ((sigma_indep_iff.1 (h.diff_singleton_indep hf)) i).subset ?_
        rw [preimage_diff, preimage_singleton_eq_empty.2 (by simpa using hij.symm), diff_empty]
      refine ((sigma_indep_iff.1 (h.diff_singleton_indep he)) k).subset ?_
      rw [preimage_diff, preimage_singleton_eq_empty.2 (by simpa using hne), diff_empty]
    obtain ⟨⟨i,e⟩, heC⟩ := h.nonempty
    have hss : C ⊆ range (Sigma.mk i) := by
      simp_rw [range_sigmaMk, subset_def, mem_preimage, mem_singleton_iff]
      exact fun y hy ↦ aux hy heC
    obtain ⟨C₀, rfl⟩ := subset_range_iff_exists_image_eq.1 hss
    simp_rw [isCircuit_iff_dep_forall_diff_singleton_indep]
    refine ⟨i, C₀, ⟨sigma_image_dep_iff.1 h.dep, fun e he ↦ ?_⟩, rfl⟩
    have hi := h.diff_singleton_indep (mem_image_of_mem _ he)
    rwa [← image_singleton, ← image_diff sigma_mk_injective, sigma_image_indep_iff] at hi
  obtain ⟨i, C₀, hC₀, rfl⟩ := h
  rw [isCircuit_iff_dep_forall_diff_singleton_indep, sigma_image_dep_iff, and_iff_right hC₀.dep]
  rintro _ ⟨e, he, rfl⟩
  rw [← image_singleton, ← image_diff sigma_mk_injective, sigma_image_indep_iff]
  exact hC₀.diff_singleton_indep he

lemma sigma_isCircuit_iff' {C : Set ((i : ι) × α i)} :
    (Matroid.sigma M).IsCircuit C ↔
    ∃ i, C ⊆ range (Sigma.mk i) ∧ (M i).IsCircuit ((Sigma.mk i) ⁻¹' C) := by
  rw [sigma_isCircuit_iff]
  refine ⟨?_, fun ⟨i, hCss, hC⟩ ↦ ⟨i, _, hC, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨i, C, hC, rfl⟩
  exact ⟨i, image_subset_range .., by simpa⟩

@[simp]
lemma disjointSigma_isCircuit_iff {α : Type*} {ι : Type*} {M : ι → Matroid α}
    (hdj : Pairwise (Disjoint on fun i ↦ (M i).E)) {C : Set α} :
    (Matroid.disjointSigma M hdj).IsCircuit C ↔ ∃ i, (M i).IsCircuit C := by
  simp only [Matroid.disjointSigma, mapEmbedding, map_isCircuit_iff, sigma_isCircuit_iff',
    range_sigmaMk, restrictSubtype_ground_isCircuit_iff, Embedding.sigmaSet_apply]
  refine ⟨?_, fun ⟨i, hCi⟩ ↦ ⟨Sigma.mk i '' ((M i).E ↓∩ C), ⟨i, ?_⟩, ?_⟩⟩
  · rintro ⟨C₀, ⟨i, hC₀i, hC₀⟩, rfl⟩
    refine ⟨i, ?_⟩
    convert hC₀
    ext e
    simp only [mem_image, Sigma.exists, Subtype.exists, exists_and_right, exists_eq_right,
      mem_preimage]
    refine ⟨fun ⟨a, haE, ha⟩ ↦ ?_, fun ⟨heE, heC⟩ ↦ ⟨_, heE, heC⟩ ⟩
    obtain rfl : a = i := by simpa using hC₀i ha
    exact ⟨haE, ha⟩
  · simpa [preimage_preimage, inter_eq_self_of_subset_right hCi.subset_ground]
  simp [image_image, hCi.subset_ground]

lemma sum_isCircuit_iff {α β : Type*} (M : Matroid α) (N : Matroid β) {C : Set (α ⊕ β)} :
    (M.sum N).IsCircuit C ↔
    (C ⊆ range .inl ∧ M.IsCircuit (.inl ⁻¹' C)) ∨ (C ⊆ range .inr ∧ N.IsCircuit (.inr ⁻¹' C)) := by
  simp only [Matroid.sum, cond_false, cond_true, Equiv.sumEquivSigmaBool, mapEquiv_isCircuit_iff,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Equiv.symm_symm, Equiv.coe_fn_mk,
    sigma_isCircuit_iff', range_sigmaMk, image_subset_iff, Bool.exists_bool, Equiv.ulift_apply]
  convert Iff.rfl <;> aesop

@[simp]
lemma disjointSum_isCircuit_iff {α : Type*} {M N : Matroid α} (hdj) {C : Set α} :
    (M.disjointSum N hdj).IsCircuit C ↔ M.IsCircuit C ∨ N.IsCircuit C := by
  simp only [disjointSum, mapEmbedding, map_isCircuit_iff, sum_isCircuit_iff,
    subset_range_iff_exists_image_eq, restrictSubtype_ground_isCircuit_iff,
    Function.Embedding.sumSet_apply]
  refine ⟨?_, fun h ↦ h.elim (fun hC ↦ ⟨.inl '' (M.E ↓∩ C), ?_⟩) fun hC ↦ ⟨.inr '' (N.E ↓∩ C), ?_⟩⟩
  · rintro ⟨_,(⟨⟨C, rfl⟩,hC⟩ | ⟨⟨C, rfl⟩,hC⟩),rfl⟩
    · rw [preimage_image_eq _ Sum.inl_injective] at hC
      simp [image_image, hC]
    rw [preimage_image_eq _ Sum.inr_injective] at hC
    simp [image_image, hC, image_image]
  all_goals simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective,
    inter_eq_self_of_subset_right hC.subset_ground, hC, image_image]



end Sum


end Matroid
