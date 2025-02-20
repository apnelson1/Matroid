import Matroid.ForMathlib.Card
import Mathlib.Data.Matroid.Circuit
import Matroid.ForMathlib.Matroid.Basic
import Matroid.ForMathlib.Set

/-!
  A `IsCircuit` of a matroid is a minimal dependent set.
-/

variable {α : Type*} {M : Matroid α} {C C' I X K C₁ C₂ R E D : Set α} {e f x y : α}

open Set Set.Notation
namespace Matroid


section Dual

variable {B : Set α}

/-- A cocircuit is a circuit of the dual matroid, or equivalently the complement of a hyperplane -/
abbrev Cocircuit (M : Matroid α) (K : Set α) : Prop := M✶.IsCircuit K

lemma isCocircuit_def : M.Cocircuit K ↔ M✶.IsCircuit K := Iff.rfl

lemma Cocircuit.isCircuit (hK : M.Cocircuit K) : M✶.IsCircuit K :=
  hK

lemma IsCircuit.isCocircuit (hC : M.IsCircuit C) : M✶.Cocircuit C := by
  rwa [isCocircuit_def, dual_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Cocircuit.subset_ground (hC : M.Cocircuit C) : C ⊆ M.E :=
  hC.isCircuit.subset_ground

@[simp] lemma dual_isCocircuit_iff : M✶.Cocircuit C ↔ M.IsCircuit C := by
  rw [isCocircuit_def, dual_dual]

lemma coindep_iff_forall_subset_not_isCocircuit :
    M.Coindep X ↔ (∀ K, K ⊆ X → ¬M.Cocircuit K) ∧ X ⊆ M.E :=
  indep_iff_forall_subset_not_isCircuit'

lemma isCocircuit_iff_minimal :
    M.Cocircuit K ↔ Minimal (fun X ↦ ∀ B, M.IsBase B → (X ∩ B).Nonempty) K := by
  have aux : M✶.Dep = fun X ↦ (∀ B, M.IsBase B → (X ∩ B).Nonempty) ∧ X ⊆ M.E := by
    ext; apply dual_dep_iff_forall
  rw [isCocircuit_def, isCircuit_def, aux, iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1) fun X hX ↦
    ⟨X ∩ M.E, inter_subset_left, fun B hB ↦ ?_, inter_subset_right⟩
  rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground]
  exact hX B hB

lemma isCocircuit_iff_minimal_compl_nonspanning :
    M.Cocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X)) K := by
  convert isCocircuit_iff_minimal with K
  simp_rw [spanning_iff_exists_isBase_subset (S := M.E \ K), not_exists, subset_diff, not_and,
    not_disjoint_iff_nonempty_inter, ← and_imp, and_iff_left_of_imp IsBase.subset_ground,
      inter_comm K]

lemma isCocircuit_iff_minimal_compl_nonspanning' :
    M.Cocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X) ∧ X ⊆ M.E) K := by
  rw [isCocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1)
    (fun X hX ↦ ⟨X ∩ M.E, inter_subset_left, by rwa [diff_inter_self_eq_diff], inter_subset_right⟩)

lemma IsCircuit.inter_isCocircuit_ne_singleton (hC : M.IsCircuit C) (hK : M.Cocircuit K) :
    C ∩ K ≠ {e} := by
  intro he
  have heC : e ∈ C := (he.symm.subset rfl).1
  simp_rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (diff_singleton_sSubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]
  nth_rw 1 [← hKe.closure_eq, diff_diff_eq_sdiff_union]
  · refine (M.closure_subset_closure (subset_union_left (t := C))).trans ?_
    rw [union_assoc, singleton_union, insert_eq_of_mem heC, ← closure_union_congr_right
      (hC.closure_diff_singleton_eq e), union_eq_self_of_subset_right]
    rw [← he, diff_self_inter]
    exact diff_subset_diff_left hC.subset_ground
  rw [← he]
  exact inter_subset_left.trans hC.subset_ground

lemma IsCircuit.isCocircuit_inter_nontrivial (hC : M.IsCircuit C) (hK : M.Cocircuit K)
    (hCK : (C ∩ K).Nonempty) : (C ∩ K).Nontrivial := by
  obtain ⟨e, heCK⟩ := hCK
  rw [nontrivial_iff_ne_singleton heCK]
  exact hC.inter_isCocircuit_ne_singleton hK

lemma IsCircuit.isCocircuit_disjoint_or_nontrivial_inter (hC : M.IsCircuit C) (hK : M.Cocircuit K) :
    Disjoint C K ∨ (C ∩ K).Nontrivial := by
  rw [or_iff_not_imp_left, disjoint_iff_inter_eq_empty, ← ne_eq, ← nonempty_iff_ne_empty]
  exact hC.isCocircuit_inter_nontrivial hK

lemma dual_rankPos_iff_exists_isCircuit : M✶.RankPos ↔ ∃ C, M.IsCircuit C := by
  rw [rankPos_iff, dual_isBase_iff, diff_empty, not_iff_comm, not_exists,
    ← ground_indep_iff_isBase, indep_iff_forall_subset_not_isCircuit]
  exact ⟨fun h C _ ↦ h C, fun h C hC ↦ h C hC.subset_ground hC⟩

lemma IsCircuit.dual_rankPos (hC : M.IsCircuit C) : M✶.RankPos :=
  dual_rankPos_iff_exists_isCircuit.mpr ⟨C, hC⟩

lemma exists_isCircuit [RankPos M✶] : ∃ C, M.IsCircuit C :=
  dual_rankPos_iff_exists_isCircuit.1 (by assumption)

lemma rk_Pos_iff_exists_isCocircuit : M.RankPos ↔ ∃ K, M.Cocircuit K := by
  rw [← dual_dual M, dual_rankPos_iff_exists_isCircuit, dual_dual M]

/-- The fundamental cocircuit for `B`. Should be used when `B` is a base and `e ∈ B`. -/
def fundCocircuit (M : Matroid α) (e : α) (B : Set α) := M✶.fundCircuit e (M✶.E \ B)

lemma fundCocircuit_isCocircuit (he : e ∈ B) (hB : M.IsBase B) :
    M.Cocircuit <| M.fundCocircuit e B := by
  apply hB.compl_isBase_dual.indep.fundCircuit_isCircuit _ (by simp [he])
  rw [hB.compl_isBase_dual.closure_eq, dual_ground]
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

lemma Indep.exists_isCocircuit_inter_eq_mem (hI : M.Indep I) (heI : e ∈ I) :
    ∃ K, M.Cocircuit K ∧ K ∩ I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  refine ⟨M.fundCocircuit e B, fundCocircuit_isCocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff, subset_inter_iff, singleton_subset_iff, and_iff_right
    (mem_fundCocircuit _ _ _), singleton_subset_iff, and_iff_left heI,
    ← M.fundCocircuit_inter_eq (hIB heI)]
  exact inter_subset_inter_right _ hIB

lemma IsBase.mem_fundCocircuit_iff_mem_fundCircuit {e f : α} (hB : M.IsBase B) :
    e ∈ M.fundCocircuit f B ↔ f ∈ M.fundCircuit e B := by
  suffices aux : ∀ {N : Matroid α} {B' : Set α} (hB' : N.IsBase B') {e f},
      e ∈ N.fundCocircuit f B' → f ∈ N.fundCircuit e B' from
    ⟨fun h ↦ aux hB h , fun h ↦ aux hB.compl_isBase_dual <| by
      simpa [fundCocircuit, inter_eq_self_of_subset_right hB.subset_ground]⟩
  clear! B M e f
  intro M B hB e f he
  obtain rfl | hne := eq_or_ne e f
  · simp [mem_fundCircuit]
  have hB' : M✶.IsBase (M✶.E \ B) := hB.compl_isBase_dual
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
  have hB' :=
    (hB'.exchange_isBase_of_indep' ⟨heE, heB⟩ (by simp [hfE, hfB]) he).compl_isBase_of_dual
  refine hB'.indep.subset ?_
  simp only [dual_ground, diff_singleton_subset_iff]
  rw [diff_diff_right, inter_eq_self_of_subset_right (by simpa), union_singleton, insert_comm,
    ← union_singleton (s := M.E \ B), ← diff_diff, diff_diff_cancel_left hB.subset_ground]
  simp [hfB]

lemma IsBasis.switch_subset_of_isBasis_closure {I₀ J₀ : Set α} (hIX : M.IsBasis I X) (hI₀ : I₀ ⊆ I)
    (hJ₀X : J₀ ⊆ X) (hJ₀ : M.IsBasis J₀ (M.closure I₀)) : M.IsBasis ((I \ I₀) ∪ J₀) X := by
  have hdj : Disjoint (I \ I₀) J₀
  · rw [disjoint_iff_forall_ne]
    rintro e heII₀ _ heJ₀ rfl
    refine hIX.indep.not_mem_closure_diff_of_mem heII₀.1 ?_
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
  IsCircuit.finite hK



section Cyclic

variable {A B : Set α}

/-- A cyclic set is a (possibly empty) union of circuits -/
def Cyclic (M : Matroid α) (A : Set α) := ∃ Cs : Set (Set α), A = ⋃₀ Cs ∧ ∀ C ∈ Cs, M.IsCircuit C

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

lemma cyclic_iff_forall_mem_closure_diff_singleton :
    M.Cyclic A ↔ ∀ e ∈ A, e ∈ M.closure (A \ {e}) := by
  simp_rw [cyclic_iff_forall_exists]
  refine ⟨fun h e heA ↦ ?_, fun h e heA ↦ ?_⟩
  · simp [heA, h, mem_closure_iff_exists_isCircuit (show e ∉ A \ {e} by simp)]
  obtain ⟨C, hCss, hC, heC⟩ := exists_isCircuit_of_mem_closure (h e heA) (by simp)
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
      ((biUnion_subset_biUnion_left diff_subset).ssubset_of_mem_not_mem (x := e) ?_ ?_) h_eq.symm
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
    exact h _ hD rfl (image_subset f hDC)
  rintro ⟨C₀, ⟨h,h'⟩, rfl⟩
  refine ⟨⟨C₀, h, rfl⟩, ?_⟩
  rintro _ D hD rfl hss
  rw [h' hD ((hf.image_subset_image_iff hD.subset_ground h.subset_ground).1 hss)]

lemma mapEquiv_isCircuit_iff {β : Type*} {C : Set β} (f : α ≃ β) :
    (M.mapEquiv f).IsCircuit C ↔ M.IsCircuit (f.symm '' C) := by
  rw [mapEquiv_eq_map, map_isCircuit_iff]
  exact ⟨by rintro ⟨C, hC, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩

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
  simp [girth, sInf_eq_top]

@[simp] lemma girth_eq_top_iff_ground_indep [Finitary M] : M.girth = ⊤ ↔ M = freeOn M.E := by
  rw [girth_eq_top_iff, eq_freeOn_iff, indep_iff_forall_subset_not_isCircuit, and_iff_right rfl]
  exact ⟨fun h C _ hC ↦ h C hC hC.finite, fun h C hC _ ↦ h C hC.subset_ground hC⟩

lemma le_girth_iff : k ≤ M.girth ↔ ∀ C, M.IsCircuit C → k ≤ C.encard := by
  simp [girth, le_sInf_iff]

lemma exists_isCircuit_girth (M : Matroid α) [RankPos M✶] :
    ∃ C, M.IsCircuit C ∧ C.encard = M.girth := by
  obtain ⟨⟨C,hC⟩, (hC' : C.encard = _)⟩ :=
    @ciInf_mem ℕ∞ (setOf M.IsCircuit) _ _ (nonempty_coe_sort.mpr M.exists_isCircuit)
      (fun C ↦ (C : Set α).encard)
  exact ⟨C, hC, by rw [hC', girth, iInf_subtype']⟩

@[simp] lemma girth_emptyOn : girth (emptyOn α) = ⊤ := by
  simp [girth]

@[simp] lemma girth_freeOn : girth (freeOn E) = ⊤ := by
  simp [Subset.rfl]

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
  rw [lt_iff_not_le, girth_le_iff]
  simp

lemma lt_girth_iff' {k : ℕ} : k < M.girth ↔ ∀ C : Finset α, M.IsCircuit C → k < C.card := by
  rw [lt_iff_not_le, girth_le_iff']
  simp

lemma indep_of_card_lt_girth (hI : I.encard < M.girth) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  rw [indep_iff_forall_subset_not_isCircuit]
  exact fun C hCI hC ↦ ((hC.girth_le_card.trans (encard_mono hCI)).trans_lt hI).ne rfl

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

  exact hB₁.indep.not_mem_closure_diff_of_mem he.1 (hclosure (mem_fundCircuit _ _ _))

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
    (by simp only [mem_diff, mem_insert_iff, mem_singleton_iff]; tauto)

end IsBasisExchange


end Matroid
