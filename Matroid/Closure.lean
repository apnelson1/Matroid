import Mathlib.Data.Matroid.Closure
import Mathlib.Data.Matroid.Map

open Set
namespace Matroid

variable {α ι : Type*} {M : Matroid α} {F I J X Y B C R : Set α} {e f x y : α}

-- Independence and Bases

-- lemma Flat.insert_indep_of_not_mem (hF : M.Flat F) (hI : M.Indep I) (hIF : I ⊆ F)
--     (he : e ∈ M.E) (heF : e ∉ F) : M.Indep (insert e I) := by
--   obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF
--   obtain ⟨J', hJ', -⟩ := hJ.indep.subset_basis_of_subset (subset_insert e J)
--   have heJ := (mt <| hF.1 (X := insert e J) hJ) (by simp [insert_subset_iff, heF])
--   obtain ⟨f, hfJ', hfJ⟩ := hJ.indep.exists_insert_of_not_basis (subset_insert e J) heJ hJ'
--   refine hfJ.subset (insert_subset (.inl <| Eq.symm ?_) (hIJ.trans (subset_insert _ _)))
--   simpa [hfJ'.2] using mem_of_mem_of_subset hfJ' (diff_subset_diff_left hJ'.subset)

-- lemma flat_iff_forall_insert_indep :
--     M.Flat F ↔ (∀ ⦃I⦄, M.Indep I → I ⊆ F → ∀ e ∈ M.E, e ∉ F → M.Indep (insert e I)) ∧ F ⊆ M.E := by
--   refine ⟨fun h ↦ ⟨fun I hI h' e he heF ↦ h.insert_indep_of_not_mem hI h' he heF, h.subset_ground⟩,
--     fun ⟨h, hFE⟩ ↦ ⟨fun I X hIF hIX f hfX ↦ by_contra fun hfF ↦ ?_, hFE⟩⟩
--   exact hfF <| hIF.subset <| hIX.mem_of_insert_indep hfX <|
--     h hIX.indep hIF.subset f (hIX.subset_ground hfX) hfF

@[simp] theorem closure_flat (M : Matroid α) (X : Set α) : M.Flat (M.closure X) := by
  rw [flat_iff_isClosed, closure_eq_subtypeClosure]
  exact ⟨by simp [subtypeClosure], M.subtypeClosure.isClosed_closure ⟨X ∩ M.E, inter_subset_right⟩⟩

lemma Indep.closure_eq_setOf_basis_insert (hI : M.Indep I) :
    M.closure I = {x | M.Basis I (insert x I)} := by
  set F := {x | M.Basis I (insert x I)}
  have hIF : M.Basis I F := hI.basis_setOf_insert_basis

  have hF : M.Flat F := by
    refine ⟨fun J X hJF hJX e heX ↦ show M.Basis _ _ from ?_, hIF.subset_ground⟩
    exact (hIF.basis_of_basis_of_subset_of_subset (hJX.basis_union hJF) hJF.subset
      (hIF.subset.trans subset_union_right)).basis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans subset_union_right))

  rw [subset_antisymm_iff, closure_def, subset_sInter_iff, and_iff_right (sInter_subset_of_mem _)]
  · rintro F' ⟨hF', hIF'⟩ e (he : M.Basis I (insert e I))
    rw [inter_eq_left.mpr (hIF.subset.trans hIF.subset_ground)] at hIF'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2
    exact (hF'.1 hJ (he.basis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
  exact ⟨hF, inter_subset_left.trans hIF.subset⟩

lemma Indep.insert_basis_iff_mem_closure (hI : M.Indep I) :
    M.Basis I (insert e I) ↔ e ∈ M.closure I := by
  rw [hI.closure_eq_setOf_basis_insert, mem_setOf]

lemma Indep.basis_closure (hI : M.Indep I) : M.Basis I (M.closure I) := by
  rw [hI.closure_eq_setOf_basis_insert]; exact hI.basis_setOf_insert_basis

lemma Basis.closure_eq_closure (h : M.Basis I X) : M.closure I = M.closure X := by
  refine subset_antisymm (M.closure_subset_closure h.subset) ?_
  rw [← M.closure_closure I, h.indep.closure_eq_setOf_basis_insert]
  exact M.closure_subset_closure fun e he ↦ (h.basis_subset (subset_insert _ _)
    (insert_subset he h.subset))

lemma Basis.closure_eq_right (h : M.Basis I (M.closure X)) : M.closure I = M.closure X :=
  M.closure_closure X ▸ h.closure_eq_closure

lemma Basis'.closure_eq_closure (h : M.Basis' I X) : M.closure I = M.closure X := by
  rw [← closure_inter_ground _ X, h.basis_inter_ground.closure_eq_closure]

lemma Basis.subset_closure (h : M.Basis I X) : X ⊆ M.closure I := by
  rw [← closure_subset_closure_iff_subset_closure, h.closure_eq_closure]

lemma Basis'.basis_closure_right (h : M.Basis' I X) : M.Basis I (M.closure X) := by
  rw [← h.closure_eq_closure]; exact h.indep.basis_closure

lemma Basis.basis_closure_right (h : M.Basis I X) : M.Basis I (M.closure X) :=
  h.basis'.basis_closure_right

lemma Indep.mem_closure_iff (hI : M.Indep I) :
    x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I := by
  rwa [hI.closure_eq_setOf_basis_insert, mem_setOf, basis_insert_iff]

lemma Indep.mem_closure_iff' (hI : M.Indep I) :
    x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) → x ∈ I) := by
  rw [hI.mem_closure_iff, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground,
    imp_iff_not_or]
  have := hI.subset_ground
  aesop

lemma Indep.insert_dep_iff (hI : M.Indep I) : M.Dep (insert e I) ↔ e ∈ M.closure I \ I := by
  rw [mem_diff, hI.mem_closure_iff, or_and_right, and_not_self_iff, or_false,
    iff_self_and, imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep

lemma Indep.mem_closure_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) :
    e ∈ M.closure I ↔ M.Dep (insert e I) := by
  rw [hI.insert_dep_iff, mem_diff, and_iff_left heI]

lemma Indep.not_mem_closure_iff (hI : M.Indep I) (he : e ∈ M.E := by aesop_mat) :
    e ∉ M.closure I ↔ M.Indep (insert e I) ∧ e ∉ I := by
  rw [hI.mem_closure_iff, dep_iff, insert_subset_iff, and_iff_right he,
    and_iff_left hI.subset_ground]; tauto

lemma Indep.not_mem_closure_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I)
    (he : e ∈ M.E := by aesop_mat) : e ∉ M.closure I ↔ M.Indep (insert e I) := by
  rw [hI.not_mem_closure_iff, and_iff_left heI]

lemma Indep.insert_indep_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I := by
  rw [mem_diff, hI.mem_closure_iff_of_not_mem heI, dep_iff, not_and, not_imp_not, insert_subset_iff,
    and_iff_left hI.subset_ground]
  exact ⟨fun h ↦ ⟨h.subset_ground (mem_insert e I), fun _ ↦ h⟩, fun h ↦ h.2 h.1⟩

lemma Indep.insert_indep_iff (hI : M.Indep I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I := by
  obtain (h | h) := em (e ∈ I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_not_mem h, or_iff_left h]

lemma insert_indep_iff : M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I → e ∈ M.E \ M.closure I) := by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h ↦ hI <| h.subset <| subset_insert _ _]

/-- This can be used for rewriting if the LHS is inside a binder and whether `f = e` is unknown.-/
lemma Indep.insert_diff_indep_iff (hI : M.Indep (I \ {e})) (heI : e ∈ I) :
    M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.closure (I \ {e}) ∨ f ∈ I := by
  obtain rfl | hne := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_diff_singleton_comm hne.symm, hI.insert_indep_iff, mem_diff_singleton,
    and_iff_left hne.symm]

lemma Indep.basis_of_subset_of_subset_closure (hI : M.Indep I) (hIX : I ⊆ X)
    (hXI : X ⊆ M.closure I) : M.Basis I X :=
  hI.basis_closure.basis_subset hIX hXI

lemma basis_iff_indep_subset_closure : M.Basis I X ↔ M.Indep I ∧ I ⊆ X ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, h.subset, h.subset_closure⟩,
    fun h ↦ h.1.basis_of_subset_of_subset_closure h.2.1 h.2.2⟩

lemma Indep.base_of_ground_subset_closure (hI : M.Indep I) (h : M.E ⊆ M.closure I) : M.Base I := by
  rw [← basis_ground_iff]; exact hI.basis_of_subset_of_subset_closure hI.subset_ground h

lemma Base.closure_eq (hB : M.Base B) : M.closure B = M.E := by
  rw [← basis_ground_iff] at hB; rw [hB.closure_eq_closure, closure_ground]

lemma Base.mem_closure (hB : M.Base B) (e : α) (he : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure B := by
  rwa [hB.closure_eq]

lemma Base.closure_of_superset (hB : M.Base B) (hBX : B ⊆ X) : M.closure X = M.E :=
  subset_antisymm (M.closure_subset_ground _)
    (by rw [← hB.closure_eq]; exact M.closure_subset_closure hBX)

lemma base_iff_indep_closure_eq : M.Base B ↔ M.Indep B ∧ M.closure B = M.E := by
  rw [← basis_ground_iff, basis_iff_indep_subset_closure, and_congr_right_iff]
  exact fun hI ↦ ⟨fun h ↦ (M.closure_subset_ground _).antisymm h.2,
    fun h ↦ ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩

lemma Indep.base_iff_ground_subset_closure (hI : M.Indep I) : M.Base I ↔ M.E ⊆ M.closure I :=
  ⟨fun h ↦ by rw [h.closure_eq], hI.base_of_ground_subset_closure⟩

lemma Indep.closure_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J ⊆ I) :
    M.closure J ∩ I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff, and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.basis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

lemma closure_iInter_eq_iInter_closure_of_iUnion_indep {ι : Type*} [hι : Nonempty ι]
    (Is : ι → Set α) (h : M.Indep (⋃ i, Is i)) :
    M.closure (⋂ i, Is i) = (⋂ i, M.closure (Is i)) := by
  suffices hF : M.Flat (⋂ i, M.closure (Is i)) by
    refine subset_antisymm sorry ?_
  -- have hss : ∀ i, M.Indep (Is i) := sorry
  -- have hii : M.Indep (⋂ i, Is i) := sorry
  -- simp only [subset_antisymm_iff, subset_iInter_iff]
  -- refine ⟨fun h ↦ M.closure_subset_closure <| iInter_subset _ _, fun x hx ↦ ?_⟩
  -- have hxE : x ∈ M.E := sorry
  -- rw [hii.mem_closure_iff', and_iff_right hxE]
  -- · rintro hxI _ ⟨j, rfl⟩
  --   replace hx := mem_iInter.1 hx j
  --   rw [Indep.mem_closure_iff'] at hx
    -- refine fun hxI a ⟨b, rfl : Is b = a⟩ ↦ ?_

Yes, at least for many parts of graph theory. When dealing with simple graphs, especially
work within a fixed 'host graph' like Szemeredi stuff, it's less of a problem, because
`SimpleGraph.Subgraph` is basically a set lattice. But for multigraphs and minors,
all the issues that came up with matroids apply and will be even worse,
because there is an interplay between vertex and edge types.

The seemingly simple operation of contracting a single edge in a graph (i.e. identifying
its endpoints) is a type theory minefield.







  -- exact iInter_subset_of_subset h fun ⦃a⦄ a ↦ a


lemma Indep.closure_sInter_eq_biInter_closure_of_forall_subset {Js : Set (Set α)} (hI : M.Indep I)
    (hne : Js.Nonempty) (hIs : ∀ J ∈ Js, J ⊆ I) : M.closure (⋂₀ Js) = (⋂ J ∈ Js, M.closure J)  := by
  rw [subset_antisymm_iff, subset_iInter₂_iff]
  have hiX : ⋂₀ Js ⊆ I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine ⟨ fun X hX ↦ M.closure_subset_closure (sInter_subset_of_mem hX),
    fun e he ↦ by_contra fun he' ↦ ?_⟩
  rw [mem_iInter₂] at he
  have heEI : e ∈ M.E \ I := by
    refine ⟨M.closure_subset_ground _ (he _ hne.some_mem), fun heI ↦ he' ?_⟩
    refine mem_closure_of_mem _ (fun X hX' ↦ ?_) hiI.subset_ground
    rw [← hI.closure_inter_eq_self_of_subset (hIs X hX')]
    exact ⟨he X hX', heI⟩

  rw [hiI.not_mem_closure_iff_of_not_mem (not_mem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_basis_of_subset (insert_subset_insert hiX)
    (insert_subset heEI.1 hI.subset_ground)

  have hIb : M.Basis I (insert e I) := by
    rw [hI.insert_basis_iff_mem_closure]
    exact (M.closure_subset_closure (hIs _ hne.some_mem)) (he _ hne.some_mem)

  obtain ⟨f, hfIJ, hfb⟩ :=  hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩
  obtain rfl := hI.eq_of_basis (hfb.basis_subset (insert_subset hfIJ.1
    (by (rw [diff_subset_iff, singleton_union]; exact hJI.subset))) (subset_insert _ _))

  refine hfIJ.2 (heJ (mem_insert_of_mem _ fun X hX' ↦ by_contra fun hfX ↦ ?_))

  obtain (hd | heX) := ((hI.subset (hIs X hX')).mem_closure_iff).mp (he _ hX')
  · refine (hJI.indep.subset (insert_subset (heJ (mem_insert _ _)) ?_)).not_dep hd
    specialize hIs _ hX'
    rw [← singleton_union, ← diff_subset_iff, diff_singleton_eq_self hfX] at hIs
    exact hIs.trans diff_subset
  exact heEI.2 (hIs _ hX' heX)

lemma closure_iInter_eq_iInter_closure_of_iUnion_indep' {ι : Type*} [hι : Nonempty ι]
    (Is : ι → Set α) (h : M.Indep (⋃ i, Is i)) :
    M.closure (⋂ i, Is i) = (⋂ i, M.closure (Is i)) := by

  convert h.closure_sInter_eq_biInter_closure_of_forall_subset (range_nonempty Is)
    (by simp [subset_iUnion])
  simp

lemma closure_sInter_eq_biInter_closure_of_sUnion_indep (Is : Set (Set α)) (hIs : Is.Nonempty)
    (h : M.Indep (⋃₀ Is)) :  M.closure (⋂₀ Is) = (⋂ I ∈ Is, M.closure I) :=
  h.closure_sInter_eq_biInter_closure_of_forall_subset hIs (fun _ ↦ subset_sUnion_of_mem)

lemma closure_biInter_eq_biInter_closure_of_biUnion_indep {ι : Type*} {A : Set ι} (hA : A.Nonempty)
    {I : ι → Set α} (h : M.Indep (⋃ i ∈ A, I i)) :
    M.closure (⋂ i ∈ A, I i) = ⋂ i ∈ A, M.closure (I i) := by
  have := hA.coe_sort
  convert closure_iInter_eq_iInter_closure_of_iUnion_indep (ι := A) (Is := fun i ↦ I i)
    (by simpa) <;> simp

lemma Indep.closure_iInter_eq_biInter_closure_of_forall_subset {ι : Type*} [hι : Nonempty ι]
    {Js : ι → Set α} (hI : M.Indep I) (hJs : ∀ i, Js i ⊆ I) :
    M.closure (⋂ i, Js i) = ⋂ i, M.closure (Js i) :=
  closure_iInter_eq_iInter_closure_of_iUnion_indep _ (hI.subset <| by simpa)

lemma Indep.closure_inter_eq_inter_closure (h : M.Indep (I ∪ J)) :
    M.closure (I ∩ J) = M.closure I ∩ M.closure J := by
  rw [inter_eq_iInter, closure_iInter_eq_iInter_closure_of_iUnion_indep, inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]

lemma basis_iff_basis_closure_of_subset (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ M.Basis I (M.closure X) :=
  ⟨fun h ↦ h.basis_closure_right, fun h ↦ h.basis_subset hIX (M.subset_closure X hX)⟩

lemma basis_iff_basis_closure_of_subset' (hIX : I ⊆ X) :
    M.Basis I X ↔ X ⊆ M.E ∧ M.Basis I (M.closure X) :=
  ⟨fun h ↦ ⟨h.subset_ground, h.basis_closure_right⟩,
    fun h ↦ h.2.basis_subset hIX (M.subset_closure X h.1)⟩

lemma basis'_iff_basis_closure : M.Basis' I X ↔ M.Basis I (M.closure X) ∧ I ⊆ X := by
  rw [← closure_inter_ground, basis'_iff_basis_inter_ground]
  exact ⟨fun h ↦ ⟨h.basis_closure_right, h.subset.trans inter_subset_left⟩,
    fun h ↦ h.1.basis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_closure _)⟩

lemma exists_basis_inter_ground_basis_closure (M : Matroid α) (X : Set α) :
    ∃ I, M.Basis I (X ∩ M.E) ∧ M.Basis I (M.closure X) := by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  have hI' := hI.basis_closure_right; rw [closure_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩

lemma Basis.basis_of_closure_eq_closure (hI : M.Basis I X) (hY : I ⊆ Y)
    (h : M.closure X = M.closure Y) (hYE : Y ⊆ M.E := by aesop_mat) : M.Basis I Y := by
  refine hI.indep.basis_of_subset_of_subset_closure hY ?_
  rw [hI.closure_eq_closure, h]
  exact M.subset_closure Y

lemma basis_union_iff_indep_closure : M.Basis I (I ∪ X) ↔ M.Indep I ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ ↦
    hI.basis_closure.basis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩

lemma basis_iff_indep_closure : M.Basis I X ↔ M.Indep I ∧ X ⊆ M.closure I ∧ I ⊆ X :=
  ⟨fun h ↦ ⟨h.indep, h.subset_closure, h.subset⟩, fun h ↦
    (basis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).basis_subset h.2.2 subset_union_right⟩

lemma Basis.eq_of_closure_subset (hI : M.Basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.closure J) :
    J = I := by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI, inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

@[simp] lemma empty_basis_iff : M.Basis ∅ X ↔ X ⊆ M.closure ∅ := by
  rw [basis_iff_indep_closure, and_iff_right M.empty_indep, and_iff_left (empty_subset _)]

-- Sets

lemma mem_closure_insert (he : e ∉ M.closure X) (hef : e ∈ M.closure (insert f X)) :
    f ∈ M.closure (insert e X) := by
  rw [← closure_inter_ground] at *
  have hfE : f ∈ M.E := by
    by_contra! hfE; rw [insert_inter_of_not_mem hfE] at hef; exact he hef
  have heE : e ∈ M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]

  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.closure_eq_closure, hI.indep.not_mem_closure_iff] at he
  rw [← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
    closure_insert_closure_eq_closure_insert, he.1.mem_closure_iff] at *
  rw [or_iff_not_imp_left, dep_iff, insert_comm,
    and_iff_left (insert_subset heE (insert_subset hfE hI.indep.subset_ground)), not_not]
  intro h
  rw [(h.subset (subset_insert _ _)).mem_closure_iff, or_iff_right (h.not_dep), mem_insert_iff,
    or_iff_left he.2] at hef
  subst hef; apply mem_insert

lemma closure_exchange (he : e ∈ M.closure (insert f X) \ M.closure X) :
    f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨mem_closure_insert he.2 he.1, fun hf ↦ by
    rwa [closure_insert_eq_of_mem_closure hf, diff_self, iff_false_intro (not_mem_empty _)] at he⟩

lemma closure_exchange_iff :
    e ∈ M.closure (insert f X) \ M.closure X ↔ f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨closure_exchange, closure_exchange⟩

lemma closure_insert_eq_closure_insert_of_mem (he : e ∈ M.closure (insert f X) \ M.closure X) :
    M.closure (insert e X) = M.closure (insert f X) := by
  have hf := closure_exchange he
  rw [eq_comm, ← closure_closure, ← insert_eq_of_mem he.1, closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_closure, ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hf.1, closure_closure, closure_closure]

lemma closure_diff_singleton_eq_closure (h : e ∈ M.closure (X \ {e})) :
    M.closure (X \ {e}) = M.closure X := by
  refine (em (e ∈ X)).elim (fun h' ↦ ?_) (fun h' ↦ by rw [diff_singleton_eq_self h'])
  convert M.closure_insert_closure_eq_closure_insert e (X \ {e}) using 1
  · rw [insert_eq_of_mem h, closure_closure]
  rw [insert_diff_singleton, insert_eq_of_mem h']

lemma mem_closure_diff_singleton_iff_closure (he : e ∈ X) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure (X \ {e}) ↔ M.closure (X \ {e}) = M.closure X :=
  ⟨closure_diff_singleton_eq_closure, fun h ↦ by rw [h]; exact M.mem_closure_of_mem' he⟩

lemma indep_iff_not_mem_closure_diff_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ e ∈ I, e ∉ M.closure (I \ {e}) := by
  use fun h e heI he ↦ ((h.closure_inter_eq_self_of_subset diff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h _ he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M.closure_subset_closure (subset_diff_singleton hJ.subset heJ))

lemma indep_iff_not_mem_closure_diff_forall' :
    M.Indep I ↔ I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.closure (I \ {e}) :=
  ⟨fun h ↦ ⟨h.subset_ground, (indep_iff_not_mem_closure_diff_forall h.subset_ground).mp h⟩, fun h ↦
    (indep_iff_not_mem_closure_diff_forall h.1).mpr h.2⟩

lemma Indep.not_mem_closure_diff_of_mem (hI : M.Indep I) (he : e ∈ I) : e ∉ M.closure (I \ {e}) :=
  (indep_iff_not_mem_closure_diff_forall'.1 hI).2 e he

lemma indep_iff_closure_diff_ne_forall : M.Indep I ↔ ∀ e ∈ I,
    M.closure (I \ {e}) ≠ M.closure I := by
  rw [indep_iff_not_mem_closure_diff_forall']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq ↦ h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h ↦ ⟨fun e heI ↦ by_contra fun heE ↦ h e heI ?_,fun e heI hin ↦ h e heI
      (by rw [closure_diff_singleton_eq_closure hin])⟩⟩
  rw [← closure_inter_ground, inter_comm, inter_diff_distrib_left,
    inter_singleton_eq_empty.mpr heE, diff_empty, inter_comm, closure_inter_ground]

lemma Indep.closure_diff_singleton_ssubset (hI : M.Indep I) (he : e ∈ I) :
    M.closure (I \ {e}) ⊂ M.closure I :=
  ssubset_of_subset_of_ne (M.closure_mono diff_subset) (indep_iff_closure_diff_ne_forall.mp hI _ he)

lemma indep_iff_closure_ssubset_ssubset_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ (∀ J, J ⊂ I → M.closure J ⊂ M.closure I) := by
  rw [indep_iff_not_mem_closure_diff_forall]
  refine ⟨fun h J hJI ↦ (M.closure_subset_closure hJI.subset).ssubset_of_ne (fun h_eq ↦ ?_),
    fun h e heI hin ↦ ?_⟩
  · obtain ⟨e,heJ,h'⟩ := ssubset_iff_insert.1 hJI
    apply h e (h' (mem_insert _ _))
    have heI := M.mem_closure_of_mem (h' (mem_insert e J))
    rw [← h_eq] at heI
    refine mem_of_mem_of_subset heI (M.closure_subset_closure ?_)
    rw [subset_diff, disjoint_singleton_right, and_iff_left heJ]
    exact (subset_insert _ _).trans h'
  refine (h (I \ {e}) (diff_singleton_sSubset.2 heI)).ne ?_
  rw [← closure_closure, ← insert_eq_of_mem hin, closure_insert_closure_eq_closure_insert,
    insert_diff_singleton, insert_eq_of_mem heI]

lemma ext_closure {M₁ M₂ : Matroid α} (h : ∀ X, M₁.closure X = M₂.closure X) : M₁ = M₂ :=
  eq_of_indep_iff_indep_forall (by simpa using h univ)
    (fun _ _ ↦ by simp_rw [indep_iff_closure_diff_ne_forall, h])

@[simp] lemma restrict_closure_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).closure X = (M.closure (X ∩ R) ∩ R) ∪ (R \ M.E) := by
  rw [← closure_inter_ground, restrict_ground_eq]
  ext e
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis (X ∩ R)
  have hI' := (basis_restrict_iff'.mp hI).1
  rw [← hI.closure_eq_closure, ← M.closure_inter_ground (X ∩ R), ← hI'.closure_eq_closure,
    mem_union, mem_inter_iff, hI'.indep.mem_closure_iff, hI.indep.mem_closure_iff, restrict_dep_iff,
    insert_subset_iff, dep_iff, insert_subset_iff, and_iff_left hI'.indep.subset_ground, mem_diff,
    and_iff_left (show I ⊆ R from hI.indep.subset_ground)]
  have hIR : I ⊆ R := hI.indep.subset_ground
  by_cases he : e ∈ M.E; aesop
  simp only [iff_false_intro he, and_false, false_or, and_true, ← mem_inter_iff, ← mem_union,
    inter_eq_self_of_subset_left hIR, union_comm I, and_iff_right
      (show ¬M.Indep (insert e I) from fun hi ↦ he (hi.subset_ground (mem_insert _ _))),
    not_false_iff]

lemma restrict_closure_eq (M : Matroid α) (hXR : X ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).closure X = M.closure X ∩ R := by
  rw [restrict_closure_eq', diff_eq_empty.mpr hR, union_empty, inter_eq_self_of_subset_left hXR]

@[simp] lemma comap_closure_eq {β : Type*} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).closure X = f ⁻¹' M.closure (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_basis' X
  obtain ⟨hI', hIinj, -⟩ := comap_basis'_iff.1 hI
  rw [← hI.closure_eq_closure]
  ext x
  obtain (hxE | hxE) := em' (f x ∈ M.E)
  · apply iff_of_false <;> exact (fun h ↦ hxE (by simpa using mem_ground_of_mem_closure h))

  by_cases hxI : x ∈ I
  · exact iff_of_true (mem_closure_of_mem _ hxI hI.indep.subset_ground)
      (mem_closure_of_mem' _ (mem_image_of_mem f (hI.subset hxI))
        (hI'.indep.subset_ground (mem_image_of_mem f hxI)))
  have hss : insert x I ⊆ (M.comap f).E := insert_subset hxE hI.indep.subset_ground
  rw [hI.indep.mem_closure_iff_of_not_mem hxI, ← not_indep_iff hss, comap_indep_iff,
    injOn_insert hxI, not_and, not_and, not_not, iff_true_intro hIinj, true_imp_iff]

  by_cases hxI' : f x ∈ f '' I
  · simp [hxI', hxE, mem_closure_of_mem' _ (hI'.subset hxI') hxE]

  rw [iff_false_intro hxI', imp_false, mem_preimage, image_insert_eq,
    hI'.indep.insert_indep_iff_of_not_mem hxI', mem_diff, and_iff_right hxE, not_not,
    hI'.closure_eq_closure]

@[simp] lemma map_closure_eq {β : Type*} (M : Matroid α) (f : α → β) (hf) (X : Set β) :
    (M.map f hf).closure X = f '' M.closure (f ⁻¹' X) := by
  suffices h' : ∀ X ⊆ f '' M.E, (M.map f hf).closure X = f '' (M.closure (f ⁻¹' X)) by
    convert h' (X ∩ f '' M.E) inter_subset_right using 1
    · rw [← closure_inter_ground]; rfl
    rw [preimage_inter, eq_comm, ← closure_inter_ground, inter_assoc,
      hf.preimage_image_inter Subset.rfl, closure_inter_ground]
  clear X
  intro X hX
  obtain ⟨I, hI⟩ := (M.map f hf).exists_basis X

  obtain ⟨I, X, hI', rfl, rfl⟩ := (map_basis_iff').1 hI

  rw [eq_comm, ← closure_inter_ground, hf.preimage_image_inter hI'.subset_ground,
    ← hI.closure_eq_closure, ← hI'.closure_eq_closure]
  ext e
  simp only [mem_image, hI.indep.mem_closure_iff', map_ground, map_indep_iff, forall_exists_index,
    and_imp, hI'.indep.mem_closure_iff']

  refine ⟨?_, ?_⟩
  . rintro ⟨e, ⟨heE, hind⟩, rfl⟩
    refine ⟨⟨e, heE, rfl⟩, fun J hJ hins ↦ ⟨e, hind ?_, rfl⟩⟩
    rw [← image_insert_eq,
      hf.image_eq_image_iff (insert_subset heE hI'.indep.subset_ground) hJ.subset_ground] at hins
    rwa [hins]
  rintro ⟨⟨x, hx, rfl⟩, h⟩
  refine ⟨x, ⟨hx, fun hind ↦ ?_⟩, rfl⟩
  obtain ⟨x', hx', h_eq⟩ := h _ hind (by rw [image_insert_eq])
  rwa [← hf (hI'.indep.subset_ground hx') hx h_eq]

section Spanning

variable {S T : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
  a base of `M`. -/
def Spanning (M : Matroid α) (S : Set α) := M.closure S = M.E ∧ S ⊆ M.E

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Spanning.subset_ground (hS : M.Spanning S) : S ⊆ M.E :=
  hS.2

lemma Spanning.closure_eq (hS : M.Spanning S) : M.closure S = M.E :=
  hS.1

lemma spanning_iff_closure (hS : S ⊆ M.E := by aesop_mat) : M.Spanning S ↔ M.closure S = M.E :=
  ⟨And.left, fun h ↦ ⟨h, hS⟩⟩

lemma closure_spanning_iff (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning (M.closure S) ↔ M.Spanning S := by
  rw [spanning_iff_closure, closure_closure, ← spanning_iff_closure]

lemma spanning_iff_ground_subset_closure (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.E ⊆ M.closure S := by
  rw [spanning_iff_closure, subset_antisymm_iff, and_iff_right (closure_subset_ground _ _)]

lemma not_spanning_iff_closure (hS : S ⊆ M.E := by aesop_mat) :
    ¬M.Spanning S ↔ M.closure S ⊂ M.E := by
  rw [spanning_iff_closure, ssubset_iff_subset_ne, iff_and_self,
    iff_true_intro (M.closure_subset_ground _)]
  exact fun _ ↦ trivial

lemma Spanning.superset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩

lemma Spanning.closure_superset_eq (hS : M.Spanning S) (hST : S ⊆ T) : M.closure T = M.E := by
  rw [← closure_inter_ground, ← spanning_iff_closure]
  exact hS.superset (subset_inter hST hS.subset_ground)

lemma Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (S ∪ X) :=
  hS.superset subset_union_left

lemma Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.superset subset_union_right

lemma Base.spanning (hB : M.Base B) : M.Spanning B :=
  ⟨hB.closure_eq, hB.subset_ground⟩

lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.closure_ground, rfl.subset⟩

lemma Base.superset_spanning (hB : M.Base B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

lemma spanning_iff_superset_base' : M.Spanning S ↔ (∃ B, M.Base B ∧ B ⊆ S) ∧ S ⊆ M.E := by
  refine ⟨fun h ↦ ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_basis S
  have hB' := hB.basis_closure_right
  rw [h.closure_eq, basis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

lemma spanning_iff_superset_base (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ ∃ B, M.Base B ∧ B ⊆ S := by
  rw [spanning_iff_superset_base', and_iff_left hS]

lemma Spanning.exists_base_subset (hS : M.Spanning S) : ∃ B, M.Base B ∧ B ⊆ S := by
  rwa [spanning_iff_superset_base] at hS

lemma coindep_iff_compl_spanning (hI : I ⊆ M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [coindep_iff_exists, spanning_iff_superset_base]

lemma spanning_iff_compl_coindep (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.Coindep (M.E \ S) := by
  rw [coindep_iff_compl_spanning, diff_diff_cancel_left hS]

lemma Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
  (coindep_iff_compl_spanning hI.subset_ground).mp hI

lemma coindep_iff_closure_compl_eq_ground (hK : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ M.closure (M.E \ X) = M.E := by
  rw [coindep_iff_compl_spanning, spanning_iff_closure]

lemma Coindep.closure_compl (hX : M.Coindep X) : M.closure (M.E \ X) = M.E :=
  (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX

lemma Indep.base_of_spanning (hI : M.Indep I) (hIs : M.Spanning I) : M.Base I := by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_base_subset; rwa [← hB.eq_of_subset_indep hI hBI]

lemma Spanning.base_of_indep (hIs : M.Spanning I) (hI : M.Indep I) : M.Base I :=
  hI.base_of_spanning hIs

lemma eq_of_spanning_iff_spanning_forall {M M' : Matroid α} (h : M.E = M'.E)
    (hsp : ∀ S, S ⊆ M.E → (M.Spanning S ↔ M'.Spanning S )) : M = M' := by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S ⊆ M.E)).elim (fun hSE ↦ by rw [hsp _ hSE] )
      (fun hSE ↦ iff_of_false (fun h ↦ hSE h.subset_ground)
      (fun h' ↦ hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj, eq_iff_indep_iff_indep_forall, dual_ground, dual_ground, and_iff_right h]
  intro I hIE
  rw [← coindep_def, ← coindep_def, coindep_iff_compl_spanning, coindep_iff_compl_spanning, hsp', h]

end Spanning

section Constructions

@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = ∅ := by
  rw [← subset_empty_iff, ← emptyOn_ground]; apply closure_subset_ground

@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E :=
  (closure_subset_ground _ _).antisymm
    (subset_trans (by rw [(loopyOn_base_iff.2 rfl).closure_eq])
      (closure_subset_closure _ (empty_subset _)))

lemma closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ ext_closure ?_, fun h ↦ by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq, ← h]
  exact M.closure_mono (empty_subset _)

@[simp] lemma uniqueBaseOn_closure_eq (I E X : Set α) :
    (uniqueBaseOn I E).closure X = (X ∩ I ∩ E) ∪ (E \ I) := by
  have hb : (uniqueBaseOn (I ∩ E) E).Basis (X ∩ E ∩ (I ∩ E)) (X ∩ E) :=
    (uniqueBaseOn_basis_iff inter_subset_right inter_subset_right).2 rfl
  ext e
  rw [← uniqueBaseOn_inter_ground_eq I E, ← closure_inter_ground _ X, uniqueBaseOn_ground,
    ← hb.closure_eq_closure, hb.indep.mem_closure_iff, dep_iff, uniqueBaseOn_indep_iff',
    insert_subset_iff, uniqueBaseOn_ground, inter_assoc, inter_self,
    and_iff_left inter_subset_right, ← inter_inter_distrib_right, inter_assoc,
    inter_union_distrib_right, inter_comm I, inter_union_diff, insert_subset_iff, inter_comm X,
    inter_assoc, and_iff_left inter_subset_left, mem_inter_iff]
  simp only [not_and, mem_inter_iff, mem_union, mem_diff]
  tauto

end Constructions

variable {Xs Ys : Set (Set α)} {ι : Type*}

lemma Indep.inter_basis_closure_iff_subset_closure_inter {X : Set α} (hI : M.Indep I) :
    M.Basis (X ∩ I) X ↔ X ⊆ M.closure (X ∩ I) :=
  ⟨Basis.subset_closure,
    fun h ↦ (hI.inter_left X).basis_of_subset_of_subset_closure inter_subset_left h⟩

lemma Indep.interBasis_biInter (hI : M.Indep I) {X : ι → Set α} {A : Set ι} (hA : A.Nonempty)
    (h : ∀ i ∈ A, M.Basis ((X i) ∩ I) (X i)) : M.Basis ((⋂ i ∈ A, X i) ∩ I) (⋂ i ∈ A, X i) := by
  refine (hI.inter_left _).basis_of_subset_of_subset_closure inter_subset_left ?_
  have := biInter_inter hA X I
  simp_rw [← biInter_inter hA,
    closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i ↦ (X i) ∩ I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA ↦ (biInter_subset_of_mem hiA).trans (h i hiA).subset_closure

lemma Indep.interBasis_iInter [Nonempty ι] {X : ι → Set α} (hI : M.Indep I)
    (h : ∀ i, M.Basis ((X i) ∩ I) (X i)) : M.Basis ((⋂ i, X i) ∩ I) (⋂ i, X i) := by
  rw [← biInter_univ]
  exact hI.interBasis_biInter (by simp) (by simpa)

lemma Indep.interBasis_sInter (hI : M.Indep I) (hXs : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.Basis (X ∩ I) X) : M.Basis (⋂₀ Xs ∩ I) (⋂₀ Xs) := by
  rw [sInter_eq_biInter]
  exact hI.interBasis_biInter hXs h

lemma Basis.closure_inter_basis_closure (h : M.Basis (X ∩ I) X) (hI : M.Indep I) :
    M.Basis (M.closure X ∩ I) (M.closure X) := by
  rw [hI.inter_basis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))

end Matroid





-- -- section from_axioms
-- -- lemma closure_diff_singleton_eq_cl' (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ X Y, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- {x : α} {I : set α} (h : x ∈ closure (I \ {x})) :
-- --   closure (I \ {x}) = closure I :=
-- -- begin
-- --   refine (closure_mono _ _ diff_subset).antisymm _,
-- --   have h' := closure_mono _ _ (insert_subset.mpr ⟨h, (M.subset_closure _ )⟩),
-- --   rw [insert_diff_singleton, closure_idem] at h',
-- --   exact (closure_mono _ _ (subset_insert _ _)).trans h',
-- -- end
-- -- /-- A set is independent relative to a closure function if none of its elements are contained in
-- --   the closure of their removal -/
-- -- def closure_indep (closure : set α → set α) (I : set α) : Prop := ∀ e ∈ I, e ∉ closure (I \ {e})
-- -- lemma closure_indep_mono {closure : set α → set α} (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) {I J : set α}
-- -- (hJ : closure_indep closure J) (hIJ : I ⊆ J) :
-- --   closure_indep closure I :=
-- -- (λ e heI heclosure, hJ e (hIJ heI) (closure_mono (diff_subset_diff_left hIJ) heclosure))
-- -- lemma closure_indep_aux {e : α} {I : set α} {closure : set α → set α}
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (h : closure_indep closure I) (heI : ¬closure_indep closure (insert e I)) :
-- -- e ∈ closure I :=
-- -- begin
-- --   have he : α ∉ I, by { intro he, rw [insert_eq_of_mem he] at heI, exact heI h },
-- --   rw [closure_indep] at heI, push_neg at heI,
-- --   obtain ⟨f, ⟨(rfl | hfI), hfclosure⟩⟩ := heI,
-- --   { rwa [insert_diff_self_of_not_mem he] at hfclosure },
-- --   have hne : α ≠ f, by { rintro rfl, exact he hfI },
-- --   rw [← insert_diff_singleton_comm hne] at hfclosure,
-- --   convert (closure_exchange (I \ {f}) e f ⟨hfclosure,h f hfI⟩).1,
-- --   rw [insert_diff_singleton, insert_eq_of_mem hfI],
-- -- end
-- -- /-- If the closure axioms hold, then `cl`-independence gives rise to a matroid -/
-- -- def matroid_of_closure (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X  →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- -- matroid_in α :=
-- -- matroid_of_indep (closure_indep closure)
-- -- (λ e he _, not_mem_empty _ he) (λ I J hJ hIJ, closure_indep_mono closure_mono hJ hIJ)
-- -- (begin
-- --   refine λ I I' hI hIn hI'm, _,
-- --   obtain ⟨B, hB⟩ := closure_indep_maximal hI (subset_union_left I I'),
-- --   have hB' : B ∈ maximals (⊆) {J | closure_indep closure J},
-- --   { refine ⟨hB.1.1,(λ B' hB' hBB' e heB', by_contra (λ heB, _) )⟩,
-- --     have he' : α ∈ closure I',
-- --     { refine (em (e ∈ I')).elim (λ heI', (M.subset_closure I') heI')
-- --         (λ heI', closure_indep_aux closure_exchange hI'm.1 (λ hi, _)),
-- --       exact heI' (hI'm.2 hi (subset_insert e _) (mem_insert e _)) },
-- --       have hI'B : I' ⊆ closure B,
-- --     { refine λ f hf, (em (f ∈ B)).elim (λ h', M.subset_closure B h')
-- --         (λ hfB', closure_indep_aux closure_exchange hB.1.1 (λ hi, hfB' _)),
-- --       refine hB.2 ⟨hi,hB.1.2.1.trans (subset_insert _ _),_⟩ (subset_insert _ _) (mem_insert _ _),
-- --       exact insert_subset.mpr ⟨or.inr hf,hB.1.2.2⟩ },
-- --     have heBclosure := (closure_idem B).subset ((closure_mono hI'B) he'),
-- --     refine closure_indep_mono closure_mono hB' (insert_subset.mpr ⟨heB', hBB'⟩) e (mem_insert _ _) _,
-- --     rwa [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heB] },
-- --   obtain ⟨f,hfB,hfI⟩ := exists_of_ssubset
-- --     (hB.1.2.1.ssubset_of_ne (by { rintro rfl, exact hIn hB' })),
-- --   refine ⟨f, ⟨_, hfI⟩, closure_indep_mono closure_mono hB.1.1 (insert_subset.mpr ⟨hfB,hB.1.2.1⟩)⟩,
-- --   exact or.elim (hB.1.2.2 hfB) (false.elim ∘ hfI) id,
-- -- end)
-- -- (λ I X hI hIX, closure_indep_maximal hI hIX)
-- -- lemma closure_indep_closure_eq {closure : set α → set α }
-- --   (M.subset_closure : ∀ X, X ⊆ closure X )
-- --   (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y )
-- --   (closure_idem : ∀ X, closure (closure X) = closure X )
-- --   (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- --   (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty ) (X : set α) :
-- -- closure X = X ∪ {e | ∃ I ⊆ X, closure_indep closure I ∧ ¬closure_indep closure (insert e I) }  :=
-- -- begin
-- --   ext f,
-- --   refine ⟨λ h, (em (f ∈ X)).elim or.inl (λ hf, or.inr _),
-- --     λ h, or.elim h (λ g, M.subset_closure X g) _⟩,
-- --   { have hd : ¬ (closure_indep closure (insert f X)),
-- --     { refine λ hi, hi f (mem_insert _ _) _, convert h,
-- --       rw [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self hf] },
-- --     obtain ⟨I, hI⟩ := closure_indep_maximal (λ e he h', not_mem_empty _ he) (empty_subset X),
-- --     have hXI : X ⊆ closure I,
-- --     { refine λ x hx, (em (x ∈ I)).elim (λ h', M.subset_closure _ h') (λ hxI, _),
-- --       refine closure_indep_aux closure_exchange hI.1.1 (λ hi, hxI _),
-- --       refine hI.2 ⟨hi, empty_subset (insert x I), _⟩ (subset_insert x _) (mem_insert _ _),
-- --       exact insert_subset.mpr ⟨hx, hI.1.2.2⟩ },
-- --     have hfI : f ∈ closure I, from (closure_mono (hXI)).trans_eq (closure_idem I) h,
-- --     refine ⟨I, hI.1.2.2, hI.1.1, λ hi, hf (hi f (mem_insert f _) _).elim⟩,
-- --     rwa [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self],
-- --     exact not_mem_subset hI.1.2.2 hf },
-- --   rintro ⟨I, hIX, hI, hfI⟩,
-- --   exact (closure_mono hIX) (closure_indep_aux closure_exchange hI hfI),
-- -- end
-- -- @[simp] lemma matroid_of_closure_apply {closure : set α → set α} (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X)
-- -- (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- -- (matroid_of_closure closure M.subset_closure closure_mono closure_idem closure_exchange closure_indep_maximal).closure = closure :=
-- -- begin
-- --   ext1 X,
-- --   rw [(closure_indep_closure_eq M.subset_closure closure_mono closure_idem closure_exchange closure_indep_maximal X : closure X = _),
-- --     matroid_of_closure, matroid.closure_eq_set_of_indep_not_indep],
-- --   simp,
-- -- end
-- -- @[simp] lemma matroid_of_closure_indep_iff {closure : set α → set α} (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X)
-- -- (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) {I : set α}:
-- -- (matroid_of_closure closure M.subset_closure closure_mono closure_idem closure_exchange closure_indep_maximal).indep I ↔ closure_indep closure I :=
-- -- by rw [matroid_of_closure, matroid_of_indep_apply]
-- -- /-- The maximality axiom isn't needed if all independent sets are at most some fixed size. -/
-- -- def matroid_of_closure_of_indep_bounded (closure : set α → set α)
-- --   (M.subset_closure : ∀ X, X ⊆ closure X )
-- --   (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y )
-- --   (closure_idem : ∀ X, closure (closure X) = closure X )
-- --   (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- --   (n : ℕ) (hn : ∀ I, closure_indep closure I → I.finite ∧ I.ncard ≤ n) :
-- -- matroid_in α := matroid_of_closure closure M.subset_closure closure_mono closure_idem closure_exchange
-- -- (exists_maximal_subset_property_of_bounded ⟨n, hn⟩)
-- -- @[simp] lemma matroid_of_closure_of_indep_bounded_apply (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (n : ℕ) (hn : ∀ I, closure_indep closure I → I.finite ∧ I.ncard ≤ n) :
-- -- (matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange n hn).closure = closure :=
-- -- by simp [matroid_of_closure_of_indep_bounded]
-- -- instance (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (n : ℕ) (hn : ∀ I, closure_indep closure I → I.finite ∧ I.ncard ≤ n) :
-- -- matroid.finite_rk (matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange n hn)
-- -- :=
-- -- begin
-- --   obtain ⟨B, h⟩ :=
-- --     (matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange n hn).exists_base,
-- --   refine h.finite_rk_of_finite (hn _ _).1,
-- --   simp_rw [matroid_of_closure_of_indep_bounded, matroid_of_closure, matroid.base_iff_maximal_indep,
-- --     matroid_of_indep_apply] at h,
-- --   exact h.1,
-- -- end
-- -- /-- A finite matroid as defined by the closure axioms. -/
-- -- def matroid_of_closure_of_finite [finite E] (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X) :
-- -- matroid_in α   :=
-- -- matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange (nat.card E)
-- -- (λ I hI, ⟨to_finite _, by { rw [← ncard_univ], exact ncard_le_of_subset (subset_univ _) }⟩)
-- -- @[simp] lemma matroid_of_closure_of_finite_apply [finite E] (closure : set α → set α)
-- -- (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X) :
-- -- (matroid_of_closure_of_finite closure M.subset_closure closure_mono closure_idem closure_exchange).closure = closure :=
-- -- by simp [matroid_of_closure_of_finite]
-- -- end from_axioms
-- end Matroid
