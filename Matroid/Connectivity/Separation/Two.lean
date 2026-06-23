import Matroid.Connectivity.Separation.Vertical

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




-- lemma parallelSum_foo {N : Matroid β} {f : β} (he : M.IsNonloop e) (hf : N.IsNonloop f) :
--     Separation.



-- def parallelConnection (M N : Matroid α) (e : α) (_ : M.IsNonloop e) (_ : N.IsNonloop e)
--     (he : M.E ∩ N.E ⊆ {e}) : Matroid α :=
--     ((parallelSum M N e e) ＼ {Sum.inr e}).map (Sum.elim id id)
--     (by
--       suffices (∀ a ∈ M.E, ∀ b ∈ N.E, ¬b = e → ¬a = b) ∧ ∀ b ∈ N.E, ¬b = e → ∀ a ∈ M.E, ¬b = a by
--         simpa [InjOn, parallelSum]
--       simp only [subset_singleton_iff, mem_inter_iff, and_imp] at he
--       grind)

-- lemma parallelConnection_indep_iff_of_mem (heM : M.IsNonloop e) (heN : N.IsNonloop e)
--     (h : M.E ∩ N.E ⊆ {e}) {I} (hI : e ∈ I) :
--     (M.parallelConnection N e heM heN h).Indep I ↔ M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) := by
--   rw [parallelConnection, map_indep_iff, parallelSum]
--   simp only [delete_indep_iff, ModularCut.projectBy_indep_iff, sum_indep_iff, ne_eq,
--     ModularCut.principal_eq_top_iff, ModularCut.mem_principal_iff, isFlat_closure, true_and,
--     disjoint_singleton_right]
--   refine ⟨?_, fun h ↦ ?_⟩
--   · rintro ⟨I₀, ⟨⟨⟨hIM, hIN⟩, h'⟩, he⟩, rfl⟩
--     refine ⟨hIM.subset ?_, ?_⟩
--     · rintro x ⟨⟨y | y, hy, rfl⟩, hxE⟩
--       simpa

--       simp at hxE
--       simp
