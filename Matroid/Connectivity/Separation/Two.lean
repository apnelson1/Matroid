import Matroid.Connectivity.Separation.Vertical
import Matroid.Extension.Guts

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A C X Y : Set α} {P : M.Separation}
  {b i : Bool} {e f x y : α}


open Set Matroid Matroid.Separation

namespace Matroid

/-# Independence and Bases -/

lemma IsBase.exists_isBase_contract_inter_of_eConn_le_one {B} (hB : M.IsBase B) (hP : P.eConn ≤ 1) :
    ∃ i, (M ／ P i).IsBase (B ∩ P (!i)) := by
  -- extend each `B ∩ P i` to a basis `J i` of `P i`.
  choose J hJ using fun j ↦ (hB.indep.inter_right (P j)).subset_isBasis_of_subset inter_subset_right
  have hb {j} : M.IsBasis (J j) (P j) := (hJ j).1
  have hss {j} : B ∩ P j ⊆ J j := (hJ j).2
  -- Using the definition of connectivity, we get that `∪ J` isn't much bigger than `B`.
  have hcard : (J false \ B).encard + (J true \ B).encard ≤ 1 := by
    rwa [← P.eConn_eq false, (hJ false).1.eConn_eq (J := J true) (by simpa using hb),
      nullity_eq_nullity_add_encard_diff (X := B), hB.indep.nullity_eq, zero_add,
      union_diff_distrib, encard_union_eq (by grind)] at hP
    · grind [P.union_inter_left B (i := false)]
    grind [hB.closure_eq]
  -- In fact, there is some `i` for which `J i` is no bigger than `B ∩ P i`.
  obtain ⟨i, hi⟩ : ∃ i, J i = B ∩ P i := by
    simp_rw [subset_antisymm_iff, and_iff_left hss, subset_inter_iff, and_iff_left hb.subset,
      ← diff_eq_empty, ← encard_eq_zero, Bool.exists_bool]
    enat_to_nat!; lia
  -- and this is the one that works
  use i
  grw [hb.contract_eq_contract_delete, delete_isBase_iff, contract_ground, diff_diff,
    union_diff_cancel hb.subset, P.compl_eq, isBasis_iff_indep_subset_closure,
    and_iff_right inter_subset_right, contract_closure_eq, hb.indep.contract_indep_iff,
    hi, union_comm, P.union_inter_left B]
  grind [hB.closure_eq, hB.indep]

lemma Indep.exists_indep_contract_inter_of_eConn_le_one {I} (hI : M.Indep I) (hP : P.eConn ≤ 1) :
    ∃ i, (M ／ P i).Indep (I ∩ P (!i)) := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  obtain ⟨i, hi⟩ := hB.exists_isBase_contract_inter_of_eConn_le_one hP
  exact ⟨i, hi.indep.subset <| by grind⟩

lemma Separation.indep_iff_of_eConn_le_one {I} (hP : P.eConn ≤ 1) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ((∀ i, M.Indep (I ∩ P i)) ∧ (∃ i, (M ／ P i).Indep (I ∩ P (!i)))) :=
  ⟨fun h ↦ ⟨fun _ ↦ h.inter_right _, h.exists_indep_contract_inter_of_eConn_le_one hP⟩,
    fun ⟨h, i, h'⟩ ↦ P.indep_of_contract hIE (h i) h'⟩

lemma Separation.indep_iff_of_eConn_le_one' {I} (hP : P.eConn ≤ 1) :
    M.Indep I ↔ ((∀ i, M.Indep (I ∩ P i)) ∧ (∃ i, (M ／ P i).Indep (I ∩ P (!i)))) ∧ I ⊆ M.E := by
  by_cases! hIE : ¬ I ⊆ M.E; grind
  rw [Separation.indep_iff_of_eConn_le_one hP, and_iff_left hIE]

lemma Separation.dep_iff_of_eConn_le_one {D} (hP : P.eConn ≤ 1) (hDE : D ⊆ M.E := by aesop_mat) :
    M.Dep D ↔ ((∀ i, M.Indep (D ∩ P i)) → (∀ i, (M ／ P i).Dep (D ∩ P (!i)))) := by
  rw [← not_indep_iff, Separation.indep_iff_of_eConn_le_one hP]
  simp

lemma Separation.dep_iff_of_eConn_le_one' {D} (hP : P.eConn ≤ 1) :
    M.Dep D ↔ ((∀ i, M.Indep (D ∩ P i)) → (∀ i, (M ／ P i).Dep (D ∩ P (!i)))) ∧ D ⊆ M.E := by
  by_cases! hDE : ¬ D ⊆ M.E; grind
  rw [Separation.dep_iff_of_eConn_le_one hP, and_iff_left hDE]

lemma IsMinor.indep_iff_indep {I : Set α} (hX : (M ／ (P i)).Indep X) (hY : (M ／ (P i)).Indep Y)
    (hI : I ⊆ P i) : (M ／ X).Indep I ↔ (M ／ Y).Indep I := by
  wlog hIi : (M ／ X).Indep I generalizing X Y with aux
  · exact iff_of_false hIi fun hIi' ↦ hIi <| (aux hY hX hIi').1 hIi'
  rw [iff_true_intro hIi, true_iff, hY.of_contract.contract_indep_iff, disjoint_comm,
    union_comm, ← hIi.of_contract.contract_indep_iff]
  exact hY.of_isMinor (contract_isMinor_of_subset _ hI)

lemma IsMinor.contract_insert_indep_iff (hPconn : P.eConn ≤ 1) {I : Set α} (hI : I ⊆ P i)
    (hX : (M ／ (P i)).IsBase X) (he : e ∈ (P !i)) (heX : e ∉ M.closure X)
    (hY : (M ／ (P i)).IsBase Y) (hf : f ∈ (P !i)) (hfY : f ∉ M.closure Y) :
    (M ／ X).Indep (insert e I) ↔ (M ／ Y).Indep (insert f I) := by
  wlog hi : (M ／ X).Indep (insert e I) generalizing X Y e f with aux
  · exact iff_of_false hi fun h ↦ hi <| (aux hY hf hfY hX he heX h).1 h
  refine iff_of_true hi ?_
  rw [hX.indep.of_contract.contract_indep_iff] at hi
  obtain ⟨j, hj⟩ := hi.2.exists_indep_contract_inter_of_eConn_le_one hPconn
  obtain rfl | rfl := j.eq_or_eq_not i
  · grind [hX.eq_of_subset_indep hj (by grind)]
  rw [hY.indep.of_contract.contract_indep_iff, disjoint_insert_left,
    and_iff_right (by grind [P.disjoint_bool i])]
  refine P.indep_of_contract (i := !i) (by grind [P.subset' i]) ?_ (hj.subset (by grind))
  suffices h : M.Indep (insert f Y) from h.subset <| by grind
  grind [hY.indep.of_contract.insert_indep_iff]

lemma IsMinor.eq_mapEquiv [DecidableEq α] (hPconn : P.eConn ≤ 1)
    (hX : (M ／ (P i)).IsBase X) (hx : x ∈ (P !i)) (hxX : x ∉ M.closure X)
    (hY : (M ／ (P i)).IsBase Y) (hy : y ∈ (P !i)) (hyY : y ∉ M.closure Y) :
    (M ／ Y) ↾ (insert y (P i)) = ((M ／ X) ↾ (insert x (P i))).mapEquiv (Equiv.swap x y) := by
  refine ext_indep ?_ fun I hI ↦ ?_
  · simp only [restrict_ground_eq, mapEquiv_ground_eq, image_insert_eq, Equiv.swap_apply_left]
    rw [Equiv.swap_image_eq_self]
    exact iff_of_false (by grind) (by grind)
  simp only [restrict_ground_eq] at hI
  rw [restrict_indep_iff, mapEquiv_indep_iff, restrict_indep_iff, Equiv.symm_swap, and_iff_left hI]
  -- if `x = y`, this implies the result.
  obtain rfl | hne := eq_or_ne x y
  · simp only [Equiv.swap_self, Equiv.refl_apply, image_id', hI, and_true]
    by_cases hxI : x ∈ I
    · rw [← insert_diff_self_of_mem hxI,
        IsMinor.contract_insert_indep_iff hPconn (by grind) hX hx hxX hY hy hyY]
    rw [IsMinor.indep_iff_indep hX.indep hY.indep (I := I) (by grind)]
  -- otherwise, the previous lemma does it.
  by_cases hyI : y ∈ I
  · rw [Equiv.swap_comm, Equiv.swap_image_eq_exchange hyI, and_iff_left (by grind),
      ← IsMinor.contract_insert_indep_iff (X := Y) (e := y) hPconn (by grind) hY hy hyY hX hx hxX,
      insert_diff_self_of_mem hyI]
    exact notMem_subset hI <| by grind
  have hxI : x ∉ I := by grind
  rw [Equiv.swap_image_eq_self (iff_of_false hxI hyI), and_iff_left (by grind),
    IsMinor.indep_iff_indep hX.indep hY.indep (by grind)]

lemma Separation.isCircuit_iUnion_inter_of_eConn_le_one {C : Bool → Set α}
    (hC : ∀ i, M.IsCircuit (C i)) (hP : P.eConn ≤ 1) (hCP : ∀ i j, (C i ∩ P j).Nonempty) :
    M.IsCircuit (⋃ i, (P i ∩ C i)) := by
  rw [isCircuit_iff_dep_forall_diff_singleton_indep,
    Separation.dep_iff_of_eConn_le_one hP (iUnion_subset (by grind))]
  simp_rw [Separation.indep_iff_of_eConn_le_one' (I := _ \ _) hP, diff_inter_right_comm]
  simp_rw [iUnion_inter_right_inter_eq_of_pairwise_disjoint P.pairwise_disjoint, mem_iUnion]
  have hdep (i j) : (M ／ P j).Dep ((P !j) ∩ C i) := by
    rw [inter_comm, ← P.diff_eq_inter_bool _ (by grind)]
    refine (hC i).contract_dep_of_not_subset ?_
    rw [← diff_eq_empty, P.diff_eq_inter_bool _ (by grind)]
    exact (hCP ..).ne_empty
  refine ⟨fun hCi i ↦ hdep .., fun e ⟨i, heP, heC⟩ ↦ ?_⟩
  refine ⟨⟨fun j ↦ Indep.diff ?_ _, !i, ?_⟩, diff_subset.trans (iUnion_subset <| by grind)⟩
  · refine (hC j).ssubset_indep ?_
    rw [inter_ssubset_right_iff, ← diff_eq_empty, P.diff_eq_inter_bool _ (by grind)]
    exact (hCP ..).ne_empty
  have hC' := (hC i).diff_singleton_indep heC
  rw [P.indep_iff_of_eConn_le_one hP (by grind)] at hC'
  simp_rw [diff_inter_right_comm, inter_comm (C i)] at hC'
  obtain ⟨j, hj⟩ := hC'.2
  obtain rfl | rfl := j.eq_or_eq_not !i
  · simpa using hj
  rw [← diff_inter_right_comm, diff_singleton_eq_self (by grind), i.not_not] at hj
  exact False.elim <| (hdep i i).not_indep hj

/-- If `C₁` and `C₂` are circuits intersecting both sides of a `2`-separation `P` of `M`,
then `(P b ∩ C₁) ∪ (P b ∩ C₂)` is a circuit of `M`. -/
lemma Separation.isCircuit_union_inter_of_eConn_le_one {C₁ C₂} (hC₁ : M.IsCircuit C₁)
    (hC₂ : M.IsCircuit C₂) (hP : P.eConn ≤ 1) (hC₁P : ∀ i, (C₁ ∩ P i).Nonempty)
    (hC₂P : ∀ i, (C₂ ∩ P i).Nonempty) (b : Bool) : M.IsCircuit ((C₁ ∩ P b) ∪ (C₂ ∩ P !b)) := by
  have hwin := P.isCircuit_iUnion_inter_of_eConn_le_one
    (C := fun i ↦ bif (b == i) then C₁ else C₂) (by grind) hP (by grind)
  simpa [Set.iUnion_bool' _ b, inter_comm (P _)] using hwin

/-- If `I` is an independent set of connectivity at most one, then all circuits that intersect `I`
intersect it in the same way. -/
lemma Indep.exists_forall_inter_circuit_eq {I : Set α} (hI : M.Indep I) (hIconn : M.eConn I ≤ 1) :
    ∃ J ⊆ I, ∀ C, M.IsCircuit C → (C ∩ I).Nonempty → C ∩ I = J := by
  by_cases! hC : ¬ ∃ C, M.IsCircuit C ∧ (C ∩ I).Nonempty
  · use ∅; grind
  obtain ⟨C, hC, hCne⟩ := hC
  refine ⟨C ∩ I, inter_subset_right, fun C' hC' hC'ne ↦ by_contra fun hne ↦ ?_⟩
  have hIconn : (M ／ (M.E \ I)).nullity I ≤ 1 := by
    grw [← nullity_project_eq_nullity_contract, project_nullity_eq_nullity_add_eLocalConn,
      hI.nullity_eq, ← eConn_eq_eLocalConn, hIconn, zero_add]
  have hrwC : C \ (M.E \ I) = C ∩ I := by grind
  have hrwC' : C' \ (M.E \ I) = C' ∩ I := by grind
  have h2 := (hC.cyclic.contract (M.E \ I)).two_le_nullity_union_of_ne (hrwC ▸ hCne)
    (hC'.cyclic.contract (M.E \ I)) (hrwC' ▸ hC'ne) <| by rwa [hrwC, hrwC', ne_comm]
  grw [hrwC, hrwC', inter_subset_right, inter_subset_right, union_self, hIconn] at h2
  simp at h2

/- Two-sum -/





-- /-# Parallel Connection -/

variable {β : Type*} {N : Matroid α} {e f : α}

/-- Given elements `e` and `f` in two matroids on different types, the matroid on the sum type
obtained by principally truncating the pair `{e, f}`.
If `e` and `f` are nonloops in their respective matroids,
then these two elements become parallel in the `parallelSum`. -/
def parallelSum (M : Matroid α) (N : Matroid β) (e : α) (f : β) : Matroid (α ⊕ β) :=
  (M.sum N).projectBy (ModularCut.principal _ {Sum.inl e, Sum.inr f})

lemma parallelSum_union_indep_iff_of_notMem_notMem {N : Matroid β} {f : β} (he : M.IsNonloop e)
    (hf : N.IsNonloop f) {I : Set α} {J : Set β} (heI : e ∉ I) (hfJ : f ∉ J) :
    (M.parallelSum N e f).Indep (.inl '' I ∪ .inr '' J) ↔
    (M.Indep (insert e I) ∧ N.Indep J) ∨ (M.Indep I ∧ N.Indep (insert f J)) := by
  have htop : ModularCut.principal (M.sum N) {Sum.inl e, Sum.inr f} ≠ ⊤ := by
    simp [ModularCut.principal_eq_top_iff', Set.subset_def, he.not_isLoop, he.mem_ground]
  suffices (M.Indep I ∧ N.Indep J) ∧ (e ∈ M.closure I → f ∉ N.closure J) ↔
      M.Indep (insert e I) ∧ N.Indep J ∨ M.Indep I ∧ N.Indep (insert f J) by
    simpa [parallelSum, ModularCut.projectBy_indep_iff_of_ne_top htop,
      ModularCut.mem_principal_iff', Set.subset_def, he.mem_ground, hf.mem_ground, htop]
  by_cases! hI : ¬ M.Indep I
  · simp [hI, show ¬ M.Indep (insert e I) from fun h ↦ hI (h.subset (subset_insert ..))]
  by_cases! hJ : ¬ N.Indep J
  · simp [hJ, show ¬ N.Indep (insert f J) from fun h ↦ hJ (h.subset (subset_insert ..))]
  grind [hI.insert_indep_iff_of_notMem heI, hJ.insert_indep_iff_of_notMem hfJ,
    he.mem_ground, hf.mem_ground]

lemma parallelSum_indep_iff_of_notMem_notMem {N : Matroid β} {f : β} (he : M.IsNonloop e)
    (hf : N.IsNonloop f) {I} (heI : .inl e ∉ I) (hfI : .inr f ∉ I) : (M.parallelSum N e f).Indep I ↔
    (M.Indep (.inl ⁻¹' I) ∧ N.Indep (insert f (.inr ⁻¹' I))) ∨
    (M.Indep (insert e (.inl ⁻¹' I)) ∧ N.Indep (.inr ⁻¹' I)) := by
  have hrw := image_preimage_inl_union_image_preimage_inr I
  nth_rw 1 [← hrw, parallelSum_union_indep_iff_of_notMem_notMem he hf (by simpa) (by simpa)]
  grind

/-- Given a separation `(P i, P !i)` and a label `f`, the matroid obtained by replacing
`P !i` with a single element `f` in the guts of `P`. Typically used when `f ∈ P !i`
and `P` is a `2`-separation, in which case this is one side of the `2`-sum corresponding to `P`.
If `P` is a `1`-separation, then `f` is a loop.  -/
def Separation.twoSummand (P : M.Separation) (i : Bool) (f : α) : Matroid α :=
  (M ↾ P i).extendBy f ((M.gutsModularCut P (by simp [iUnion_bool])).restrict (P i))

@[simp]
lemma Separation.twoSummand_ground (P : M.Separation) (i : Bool) (f : α) :
    (P.twoSummand i f).E = insert f (P i) := rfl

lemma Separation.twoSummand_deleteElem (hfP : f ∉ P i) : ((P.twoSummand i f) ＼ {f}) = M ↾ P i := by
  rw [twoSummand, ModularCut.extendBy_deleteElem _ hfP]

lemma Separation.gutsModularCut_eq_top_iff :
    (M.gutsModularCut P (by simp [iUnion_bool])) = ⊤ ↔ P.eConn = 0 := by
  rw [Matroid.gutsModularCut_eq_top_iff, isSkewFamily_bool_iff true, ← eConn_eq_zero_iff_skew]

lemma Separation.twoSummand_isNonloop (hP : P.eConn = 1) : (P.twoSummand i f).IsNonloop f := by
  rw [twoSummand, ModularCut.extendBy_isNonloop_iff, Ne, ModularCut.restrict_eq_top_iff,
    Separation.gutsModularCut_eq_top_iff, hP]
  simp

lemma Separation.twoSummand_isNonColoop (hfP : f ∉ P i) : (P.twoSummand i f).IsNonColoop f := by
  rw [twoSummand, isNonColoop_iff, ModularCut.extendBy_isColoop_iff _ (by simpa),
    ModularCut.restrict_eq_bot_iff, closure_mem_gutsModularCut_iff, not_not,
    isSkewFamily_bool_iff i, and_iff_right (skew_project_self ..)]
  simp

lemma Separation.twoSummand_contractElem (hP : P.eConn = 1) (hfP : f ∉ P i) :
    (P.twoSummand i f) ／ {f} = M ／ (P (!i)) := by
  rw [twoSummand, ModularCut.extendBy_contractElem _ hfP]
  have aux : (M.gutsModularCut P (by simp [iUnion_bool])).restrict (P i) ≠ ⊤ := by
    rw [Ne, ModularCut.restrict_eq_top_iff, P.gutsModularCut_eq_top_iff, hP]
    simp
  refine ext_indep (by simp) fun I hI ↦ ?_
  replace hI : I ⊆ P i := by simpa using hI
  let Q := P.induce (M.project (M.closure I ∩ P i))
  have hPQ (j : Bool) : P j = Q j := by simp [Q, induce_apply_subset]
  rw [ModularCut.projectBy_indep_iff_of_ne_top aux, restrict_indep_iff, and_iff_left hI,
    restrict_closure_eq _ hI, ModularCut.mem_restrict_iff, closure_mem_gutsModularCut_iff,
    and_iff_right ((M.closure_isFlat I).isFlat_restrict (P i)), isSkewFamily_bool_iff i,
    contract_indep_iff_indep_skew, and_congr_right_iff, ← eLocalConn_eq_zero]
  intro hI'
  have hP1 : P.eConn = 1 := hP
  rw [eConn_eq_eLocalConn _ i, ← M.eLocalConn_add_project_eLocalConn_of_subset
      (show M.closure I ∩ P i ⊆ P i from inter_subset_right) (P !i)] at hP1
  refine ⟨fun h ↦ ?_, fun h h0 ↦ ?_⟩
  · grw [← Ne, ← ENat.one_le_iff_ne_zero, ← hP1, ENat.add_le_right_iff, eLocalConn_eq_zero,
      or_iff_left (by enat_to_nat!)] at h
    exact h.mono_left (by grind)
  replace hP1 := hP1.ge
  grw [h0, add_zero, eLocalConn_mono_left _ inter_subset_left, eLocalConn_closure_left,
    h.eLocalConn] at hP1
  simp at hP1

lemma Separation.twoSummand_dual (hP : P.eConn = 1) (hfP : f ∉ P i) :
    (P.twoSummand i f)✶ = (P.induce M✶).twoSummand i f := by
  refine ext_contractElem_deleteElem (e := f) ?_ ?_ ?_ ?_
  · exact P.twoSummand_isNonColoop hfP
  · exact Separation.twoSummand_isNonloop <| by simpa
  · rw [← dual_inj, dual_contract_dual, twoSummand_deleteElem hfP,
      twoSummand_contractElem (by simpa) (by simpa)]
    simp
  rw [← dual_inj, dual_delete_dual, twoSummand_contractElem hP hfP,
    twoSummand_deleteElem (by simpa), induce_dual_apply, ← delete_compl, dual_ground,
    P.compl_eq, dual_delete_dual]

lemma Separation.twoSummand_mapEquiv [DecidableEq α] (heP : e ∉ P i) (hfP : f ∉ P i) :
    (P.twoSummand i f).mapEquiv (Equiv.swap f e) = P.twoSummand i e := by
  rw [twoSummand, ModularCut.mapEquiv_extendBy _ (by simpa) (by simpa), twoSummand]

/-- If we contract a spanning set in `M ／ P i` that is skew to `P i` and doesn't span `f` in `M`,
then restrict to `P i ∪ {f}`, then we get `P.twoSummand i f`. -/
lemma Separation.contract_restrict_insert_eq_twoSummand {X : Set α} (hP : P.eConn = 1)
    (hfP : f ∈ P !i) (hX : (M ／ P i).Spanning X) (hsk : M.Skew X (P i)) (hfB : f ∉ M.closure X) :
    (M ／ X) ↾ (insert f (P i)) = P.twoSummand i f := by
  have hf' : f ∉ P i := (P.disjoint_bool i).notMem_of_mem_right hfP
  refine ext_contractElem_deleteElem (e := f) ?_ ?_ ?_ ?_
  · simp [hfB, P.subset_ground hfP]
  · exact twoSummand_isNonloop hP
  · rw [twoSummand_contractElem hP hf', restrict_contract_eq_contract_restrict _ (by simp),
      insert_diff_self_of_notMem hf', contract_eq_contract_delete_of_subset_closure
      (show insert f X ⊆ P !i by grind), contract_contract, union_singleton,
      Matroid.delete_eq_restrict, contract_ground, diff_diff, union_diff_cancel (by grind),
      P.compl_not_eq]
    rw [← singleton_union, ← project_closure]
    refine IsNonloop.subset_closure_of_eRk_le_one ?_ ?_ hfP
    · rwa [project_isNonloop_iff, and_iff_left (P.subset_ground hfP)]
    have hXP : X ⊆ P !i := by grw [hX.subset_ground, contract_ground, P.compl_eq]
    rw [contract_spanning_iff] at hX
    grw [← (M.project X).eLocalConn_add_eRelRk_union_eq_eRk (P !i) (P i),
        eLocalConn_project_le_of_subset_left _ hXP,
        eLocalConn_comm, ← P.eConn_eq_eLocalConn, hP, P.union_bool_eq',
        eRelRk_eq_zero_iff'.2, add_zero]
    grw [project_ground, inter_self, project_closure, union_comm, hX.1.closure_eq]
  rw [twoSummand_deleteElem hf', Matroid.delete_eq_restrict, restrict_ground_eq,
    insert_diff_self_of_notMem hf', restrict_restrict_eq _ (subset_insert ..),
    hsk.contract_restrict_eq]

/-- If `N` is a minor of `M` that intersects one side of a two-separation in a unique element `f`,
which is not a loop or coloop of `N`, then `N` is a minor of the two-summand for the other side. -/
lemma Separation.isMinor_twoSummand (hP : P.eConn = 1) (hNM : N ≤m M) (hf : P (!i) ∩ N.E = {f})
    (hfnl : N.IsNonloop f) (hfncl : N.IsNonColoop f) : N ≤m P.twoSummand i f := by
  have ⟨hfj, hfN⟩ : f ∈ P (!i) ∧ f ∈ N.E := by simpa using hf.symm.subset
  have hle : 1 ≤ N.eConn {f} := by
    rw [ENat.one_le_iff_ne_zero, Ne, eConn_singleton_eq_zero_iff hfN]
    simp [hfnl.not_isLoop, hfncl.not_isColoop]
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  have hfC : f ∉ C := by grind
  have hfD : f ∉ D := by grind
  /- since `f` is neither a loop nor a coloop of the minor, we know that `P i` and `P !i`
    aren't skew after projecting `C ∩ P !i` -/
  grw [Matroid.eConn_eq_eLocalConn, eLocalConn_mono_left _ (singleton_subset_iff.2 hfj),
    eLocalConn_delete_le, ← hf, diff_inter_self_eq_diff, contract_delete_ground,
    diff_diff_comm, P.compl_not_eq, eLocalConn_mono_right _ _ diff_subset, eLocalConn_comm,
    ← contract_inter_ground_eq, ← P.union_bool_eq i, inter_union_distrib_left,
    ← eLocalConn_project_eq_eLocalConn_contract, union_comm, ← project_project,
    eLocalConn_project_le_of_subset_left _ (by simp)] at hle
  -- and this means that `P i` is skew to `C ∩ P !i` in `M`.
  have hsk := hP.le
  grw [P.eConn_eq_eLocalConn i, eLocalConn_eq_eLocalConn_project_add_eLocalConn_of_subset_right
    (C := C ∩ P !i) _ _ inter_subset_right, ← hle, ENat.add_le_left_iff, or_iff_right (by simp),
    eLocalConn_eq_zero] at hsk
  /- An easy computation. `grind` seems to fail. -/
  have hrw : (M.E \ insert f D) ⊆ C ∩ P (!i) ∪ P i := by
    grw [← singleton_union, ← hf, contract_delete_ground,
      diff_subset_iff, ← union_assoc, union_right_comm _ D, inter_comm,
      ← union_inter_distrib_right, union_comm C, ← diff_diff,
      diff_union_of_subset (by grind), inter_union_distrib_right,
      diff_union_of_subset (by grind), ← subset_union_left (t := D),
      inter_eq_self_of_subset_right P.subset_ground, P.union_bool_eq']
  /- `C ∩ P !i` is spanning, because of the fact that `D` is coindependent and `f` is not a
  coloop of `N`.-/
  have hsp : (M ／ P i).Spanning (C ∩ P !i) := by
    grw [contract_spanning_iff, and_iff_left (by grind)]
    refine (Coindep.compl_spanning ?_).superset hrw
    rw [Coindep, hD.insert_indep_iff_of_notMem (by grind), mem_diff, and_iff_right (by grind)]
    refine fun hfD' ↦ hfncl.not_isColoop ?_
    rwa [contract_delete_comm _ hCD, contract_isColoop_iff, IsColoop, dual_delete,
      contract_isLoop_iff_mem_closure, and_iff_right hfD', and_iff_left hfC]
  /- `C ∩ P !i` doesn't span `f`, since `f` is not a loop of `N`.  -/
  have hfcl : f ∉ M.closure (C ∩ P !i) := by
    grw [inter_subset_left]
    exact fun hfcl ↦ hfnl.not_isLoop <| by simp [hfcl, hfC, hfD]
  nth_rw 1 [← P.contract_restrict_insert_eq_twoSummand hP hfj hsp hsk.symm hfcl,
    contract_delete_comm _ hCD, ← inter_union_diff C (P !i), ← contract_contract]
  refine (contract_isMinor ..).trans ?_
  rw [← contract_delete_comm _ (hCD.mono_left inter_subset_left), Matroid.delete_eq_restrict]
  refine (IsRestriction.of_subset _ ?_).isMinor
  grw [contract_ground, diff_subset_iff, diff_subset_iff, union_insert, union_comm D,
    ← union_insert, ← union_assoc, union_comm, ← diff_subset_iff, hrw]

lemma Separation.eq_restrict_or_contract_of_ground_eq
    (hP : P.eConn ≤ 1) (hNM : N ≤m M) (hNE : N.E = P i) : N = M ↾ P i ∨ N = M ／ P !i := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
  rw [← P.eConn_eq (i := i), M.eConn_eq_eLocalConn_add_eLocalConn_dual (by grind) (by grind) hCD
    (by grind)] at hP
  have hCDu : C ∪ D = P !i := by
    rw [← P.compl_eq, ← hNE, contract_delete_ground, diff_diff_cancel_left (by grind)]
  by_cases hsk : M.Skew (P i) C
  · left
    rw [← hsk.symm.contract_restrict_eq, Matroid.delete_eq_restrict, contract_ground, diff_diff,
      ← contract_delete_ground, hNE]
  rw [← eLocalConn_eq_zero, ← Ne, ← ENat.one_le_iff_ne_zero] at hsk
  grw [← hsk, ENat.add_le_left_iff, or_iff_right (by simp), eLocalConn_eq_zero] at hP
  right
  rw [← dual_inj, dual_contract, M✶.delete_eq_restrict, dual_ground, P.compl_not_eq,
    ← hP.symm.contract_restrict_eq, dual_contract_delete, ← contract_delete_comm _ hCD.symm,
    Matroid.delete_eq_restrict, contract_ground, dual_ground, diff_diff, union_comm, hCDu,
    P.compl_not_eq]

lemma isMinor_twoSummand' (hP : P.eConn = 1) (hNM : N ≤m M) (hl : N.Loopless) (hl' : N.Coloopless)
  (hss : (P (!i) ∩ N.E).Subsingleton) : ∃ f ∈ P !i, N ≤m P.twoSummand i f := by
  obtain ⟨f, hf⟩ | hdj := hss.eq_empty_or_singleton.symm
  · have ⟨hfP, hfN⟩ : f ∈ P !i ∧ f ∈ N.E := by simpa using hf.symm.subset
    refine ⟨f, by simpa, isMinor_twoSummand hP hNM hf ?_ ?_⟩
    · exact hl.isNonloop_of_mem hfN
    exact hl'.dual_loopless.isNonloop_of_mem hfN
  rw [← disjoint_iff_inter_eq_empty] at hdj
  have hNi : N.E ⊆ P i := by
    rwa [← P.compl_not_eq, subset_diff, disjoint_comm, and_iff_right hNM.subset]
  obtain ⟨N', hNN', hN'M, hN'E⟩ := hNM.exists_isMinor_of_subset_subset hNi P.subset_ground
  obtain ⟨f, hfi⟩ : (P !i).Nonempty := by simpa [hP] using M.eConn_le_encard (P !i)
  refine ⟨f, hfi, ?_⟩
  obtain rfl | rfl := eq_restrict_or_contract_of_ground_eq (N := N') hP.le hN'M hN'E
  · refine hNN'.trans ?_
    rw [← twoSummand_deleteElem (show f ∉ P i by grind)]
    exact delete_isMinor ..
  refine hNN'.trans ?_
  rw [← twoSummand_contractElem hP (show f ∉ P i by grind)]
  exact contract_isMinor ..

/-- If `N` is a `3`-connected minor of a matroid `M` with a `2`-separation `P`,
then `N` is a minor of some two-summand of `M`. -/
lemma exists_isMinor_twoSummand (hP : P.eConn = 1) (hNM : N ≤m M) (hN : N.TutteConnected (2 + 1))
    (hnt : N.E.Nontrivial) : ∃ i f, f ∈ P !i ∧ N ≤m P.twoSummand i f := by
  have hss := hP.le
  grw [← eConn_induce_le_of_isMinor _ hNM] at hss
  obtain ⟨i, hi⟩ := hN.exists_subsingleton_of_isTutteSeparation hss
  rw [P.induce_apply_subset hNM.subset] at hi
  obtain ⟨f, hfP, hf⟩ := isMinor_twoSummand' hP hNM (i := !i)
    (hN.loopless (by simp) hnt) (by simpa using hN.dual.loopless (by simp) hnt) (by simpa)
  exact ⟨!i, f, hfP, hf⟩

/-- If `C` is skew to one side of a two-separation `P i`, then `M ／ C` has some two-summand of
the other side as a minor. -/
lemma exists_twoSummand_isMinor_contract (hP : P.eConn = 1) (hC : C ⊆ P !i) (hCP : M.Skew C (P i)) :
    ∃ f ∈ P !i, P.twoSummand i f ≤m M ／ C := by
  obtain ⟨I, hI⟩ := (M ／ P i ／ C).exists_isBase
  have hIP : I ∪ C ⊆ P !i := by grind
  have hIE : I ∪ C ⊆ M.E := hIP.trans P.subset_ground
  have hsk : M.Skew (P i) (I ∪ C) := by
    replace hI := hI.indep
    rw [contract_comm, contract_indep_iff_indep_skew _] at hI
    rw [skew_comm, skew_iff_contract_restrict_eq_restrict,
      union_comm, ← contract_contract, hI.2.contract_restrict_eq, hCP.contract_restrict_eq]
    grind [subset_diff]
  obtain ⟨f, hfP, hfcl⟩ : ∃ f ∈ P !i, f ∉ M.closure (I ∪ C) := by
    by_contra! hcon
    grw [← eLocalConn_eq_zero, ← le_zero_iff, ← eLocalConn_closure_right,
      ← show P (!i) ⊆ M.closure (I ∪ C) by grind, ← P.eConn_eq_eLocalConn, hP] at hsk
    simp at hsk
  have hsp : (M ／ P i).Spanning (I ∪ C) := by
    replace hI := hI.spanning
    rw [contract_contract, union_comm, contract_spanning_iff] at hI
    rw [contract_spanning_iff, union_assoc]
    grind
  refine ⟨f, hfP, ?_⟩
  rw [← contract_restrict_insert_eq_twoSummand hP hfP hsp (by rwa [skew_comm]) hfcl, union_comm,
    ← contract_contract]
  refine (restrict_isMinor _ ?_).trans <| contract_isMinor ..
  grw [← subset_closure _ _] at hfcl
  grw [contract_contract, union_comm, contract_ground, subset_diff, disjoint_insert_left,
    and_iff_right hfcl, hIP, insert_subset_iff]
  grind

lemma Separation.isoMinor_contract_of_notMem_closure (hP : P.eConn = 1) (hNM : N ≤m M)
    (hl : N.Loopless) (hl' : N.Coloopless) (hss : (P (!i) ∩ N.E).Subsingleton)
    (hecl : e ∉ M.closure (P i)) : Nonempty (N ≤i (M ／ {e})) := by
  classical
  by_cases! he : e ∉ P !i
  · rw [contractElem_eq_self]
    · exact ⟨hNM.isoMinor⟩
    grw [← subset_closure _ _ ] at hecl
    rw [← P.union_bool_eq' i, mem_union, not_or]
    exact ⟨he, hecl⟩
  obtain ⟨f, hfP, hf⟩ := exists_twoSummand_isMinor_contract hP (show {e} ⊆ P !i by simpa)
    (by rwa [(isNonloop_of_notMem_closure hecl).skew_left_iff])
  obtain ⟨g, hg, h2⟩ := isMinor_twoSummand' hP hNM hl hl' hss
  rw [← P.twoSummand_mapEquiv (e := f) (f := g) (i := i) (by grind) (by grind)] at hf
  let i' := (P.twoSummand i g).isoMapEquiv (Equiv.swap g f)
  exact ⟨(h2.isoMinor.trans_iso i').trans hf.isoMinor⟩

-- lemma IsTutteSeparation ((hP : P.eConn = 1) (hMs : M.Simple) (hMs : M✶.Simple) :
--     ∃
