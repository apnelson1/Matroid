import Mathlib.Data.Matroid.Map
import Mathlib.Order.Closure
import Matroid.Constructions.DirectSum
import Matroid.Constructions.Coexpand

open Set
namespace Matroid

variable {α ι : Type*} {M : Matroid α} {F I J X Y B C R : Set α} {e f x y : α}

section Flat

/-- A flat is a maximal set having a given basis  -/
@[mk_iff]
structure Flat (M : Matroid α) (F : Set α) : Prop where
  insert_indep_of_not_mem : ∀ ⦃I e⦄, I ⊆ F → M.Indep I → e ∈ M.E → e ∉ F → M.Indep (insert e I)
  subset_ground : F ⊆ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] Flat.subset_ground

@[simp] lemma ground_flat (M : Matroid α) : M.Flat M.E :=
  ⟨by tauto, Subset.rfl⟩

lemma flat_iff_forall_basis : M.Flat F ↔ (∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F) ∧ F ⊆ M.E := by
  rw [flat_iff, and_congr_left_iff, iff_comm]
  refine fun hF ↦ ⟨fun h I e hIF hI he heF↦ ?_, fun h I X hIF hIX e he ↦ by_contra fun heF ↦ ?_⟩
  · obtain ⟨J, hJF, hIJ⟩ := hI.subset_basis_of_subset hIF
    by_contra hcon
    rw [not_indep_iff] at hcon
    refine False.elim <| heF <| (h (X := insert e J) hJF
      (hJF.indep.basis_of_forall_insert (subset_insert _ _) ?_)) (mem_insert e _)
    simp (config := {contextual := true}) [hcon.superset (insert_subset_insert hIJ)]
  by_cases heI : e ∈ I
  · exact heF <| hIF.subset heI
  apply (hIX.insert_dep ⟨he, heI⟩).not_indep
  exact h hIF.subset hIF.indep (hIX.subset_ground he) heF

lemma Flat.subset_of_basis_of_basis (hF : M.Flat F) (hIF : M.Basis I F) (hIX : M.Basis I X) :
    X ⊆ F := by
  rw [flat_iff_forall_basis] at hF
  exact hF.1 hIF hIX

lemma Flat.iInter {ι : Type*} [Nonempty ι] {Fs : ι → Set α}
    (hFs : ∀ i, M.Flat (Fs i)) : M.Flat (⋂ i, Fs i) := by
  simp only [flat_iff, subset_iInter_iff, mem_iInter, not_forall, forall_exists_index]
  exact ⟨fun I e hIF hI he i hei ↦ (hFs i).insert_indep_of_not_mem (hIF i) hI he hei,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground ⟩

lemma coexpand_flat_iff {F : Set α} : M.coexpand.Flat F ↔ M.Flat (F ∩ M.E) := by
  simp only [flat_iff, coexpand_indep_iff, coexpand_ground_eq, mem_univ, true_implies, subset_univ,
    and_true, subset_inter_iff, mem_inter_iff, not_and, and_imp, inter_subset_right]
  refine ⟨fun h I e hIF hIE hI he heF ↦ ?_, fun h I e hIF hI heF ↦ ?_⟩
  · specialize h hIF (by rwa [inter_eq_self_of_subset_left hIE]) (fun heF' ↦ heF heF' he)
    rwa [insert_inter_of_mem he, inter_eq_self_of_subset_left hIE] at h
  by_cases he : e ∈ M.E
  · rw [insert_inter_of_mem he]
    exact h (inter_subset_left.trans hIF) inter_subset_right hI he (by simp [heF])
  rwa [insert_inter_of_not_mem he]

def closure (M : Matroid α) : ClosureOperator (Set α) := by
  refine ClosureOperator.ofCompletePred (fun X ↦ M.Flat (X ∩ M.E)) fun s hs ↦ ?_
  obtain (rfl | hne) := s.eq_empty_or_nonempty
  · simp
  have _ := hne.coe_sort
  simpa [biInter_inter hne, ← sInter_eq_biInter] using
    Flat.iInter (M := M) (Fs := fun (F : s) ↦ F ∩ M.E) (by simpa)

lemma flat_iff_isClosed : M.Flat F ↔ M.closure.IsClosed F ∧ F ⊆ M.E := by
  simp only [closure, ClosureOperator.ofCompletePred_isClosed]
  exact ⟨fun h ↦ by simpa [inter_eq_self_of_subset_left h.subset_ground, h.subset_ground],
    fun ⟨h,h'⟩ ↦ by rwa [← inter_eq_self_of_subset_left h']⟩

lemma flat_iff_isClosed' (hF : F ⊆ M.E := by aesop_mat) : M.Flat F ↔ M.closure.IsClosed F := by
  rw [flat_iff_isClosed, and_iff_left hF]

lemma Flat.isClosed (hF : M.Flat F) : M.closure.IsClosed F := by
  rwa [← flat_iff_isClosed']

@[simp] lemma coexpand_closure_eq (M : Matroid α) : M.coexpand.closure = M.closure :=
  ClosureOperator.ext _ _ fun X ↦ by simp [closure, iInter_subtype, coexpand_flat_iff]

end Flat

lemma closure_eq_union_sInter (M : Matroid α) (X : Set α) :
    M.closure X = X ∪ ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F} := by
  simp only [closure, ClosureOperator.ofCompletePred_apply, le_eq_subset, iInf_subtype,
    iInf_eq_iInter, subset_antisymm_iff, subset_def (t := X ∪ _), mem_iInter, and_imp, mem_union,
    mem_sInter, mem_setOf_eq, or_iff_not_imp_left, subset_iInter_iff, union_subset_iff]
  refine ⟨fun e h heX F hF hXF ↦ ?_, fun F hXF hF ↦ ⟨hXF, ?_⟩⟩
  · specialize h (X ∪ F) subset_union_left
    rwa [mem_union, or_iff_right heX, union_inter_distrib_right,
      inter_eq_self_of_subset_left hF.subset_ground, union_eq_self_of_subset_left hXF,
      imp_iff_right hF] at h
  refine (sInter_subset_of_mem ?_).trans (show F ∩ M.E ⊆ F from inter_subset_left)
  simp [hF, inter_subset_left.trans hXF]

lemma closure_eq_sInter (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = ⋂₀ {F | M.Flat F ∧ X ⊆ F} := by
  simp [closure_eq_union_sInter, inter_eq_self_of_subset_left hX, union_eq_self_of_subset_left]

/-- The closure of a subset of the ground set is the intersection of the flats containing it.
A set `X` that doesn't satisfy `X ⊆ M.E` has a junk value such that
`M.closure X := M.closure (X ∩ M.E)`. -/
-- def closure (M : Matroid α) (X : Set α) := ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F}

-- lemma closure_eq_subtypeCl (M : Matroid α) (X : Set α) :
--     M.closure X = M.subtypeCl ⟨X ∩ M.E, inter_subset_right⟩  := by
--   suffices ∀ (x : α), (∀ (t : Set α), M.Flat t → X ∩ M.E ⊆ t → x ∈ t) ↔
--     (x ∈ M.E ∧ ∀ a ⊆ M.E, X ∩ M.E ⊆ a → M.Flat a → x ∈ a) by
--     simpa [closure, subtypeCl, Set.ext_iff]
--   exact fun x ↦ ⟨fun h ↦ ⟨h _ M.ground_flat inter_subset_right, fun F _ hXF hF ↦ h F hF hXF⟩,
--     fun ⟨_, h⟩ F hF hXF ↦ h F hF.subset_ground hXF hF⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma closure_subset_ground (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X ⊆ M.E := by
  rw [M.closure_eq_sInter X]
  exact sInter_subset_of_mem ⟨M.ground_flat, hX⟩

lemma closure_flat (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.Flat (M.closure X) := by
  rw [flat_iff_isClosed, and_iff_left (M.closure_subset_ground X)]
  exact M.closure.isClosed_closure X

@[simp] lemma closure_empty_flat (M : Matroid α) : M.Flat <| M.closure ∅ :=
  M.closure_flat ∅

@[simp] lemma ground_subset_closure_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.E ⊆ M.closure X ↔ M.closure X = M.E := by
  simp [M.closure_subset_ground X, subset_antisymm_iff]

lemma closure_eq_union_closure_inter_ground_self (M : Matroid α) (X : Set α) :
    M.closure X = M.closure (X ∩ M.E) ∪ X := by
  rw [closure_eq_union_sInter, closure_eq_union_sInter, union_right_comm,
    union_eq_self_of_subset_left inter_subset_left, inter_assoc, inter_self]

lemma closure_subset_ground_union (M : Matroid α) (X : Set α) : M.closure X ⊆ M.E ∪ X := by
  rw [closure_eq_union_closure_inter_ground_self]
  exact union_subset_union_left _ (closure_subset_ground _ _)

lemma closure_eq_closure_inter_ground_union_diff (M : Matroid α) (X : Set α) :
    M.closure X = M.closure (X ∩ M.E) ∪ (X \ M.E) := by
  rw [closure_eq_union_sInter, closure_eq_union_sInter, inter_assoc, inter_self]
  nth_rw 1 [← inter_union_diff X M.E, union_right_comm]

lemma closure_inter_ground_subset_ground (M : Matroid α) (X : Set α) :
    M.closure (X ∩ M.E) ⊆ M.E := by
  aesop_mat

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma closure_diff_self_subset_ground (M : Matroid α) (X : Set α) : M.closure X \ X ⊆ M.E := by
  rw [diff_subset_iff, union_comm]
  apply closure_subset_ground_union

lemma closure_diff_self_eq_closure_inter_ground_diff (M : Matroid α) (X : Set α) :
    M.closure X \ X = M.closure (X ∩ M.E) \ (X ∩ M.E) := by
  rw [closure_eq_union_closure_inter_ground_self, union_diff_right, sdiff_eq_sdiff_iff_inf_eq_inf]
  simp_rw [inf_eq_inter, ← inter_assoc, left_eq_inter]
  exact inter_subset_left.trans <| M.closure_subset_ground _

@[simp] lemma subset_closure (M : Matroid α) (X : Set α) : X ⊆ M.closure X :=
  M.closure.le_closure X

@[simp] lemma closure_subset_ground_iff : M.closure X ⊆ M.E ↔ X ⊆ M.E :=
  ⟨fun h ↦ (M.subset_closure X).trans h, fun h ↦ M.closure_subset_ground X h⟩

lemma mem_closure_iff_forall_mem_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ ∀ F, M.Flat F → X ⊆ F → e ∈ F := by
  simp [M.closure_eq_sInter X]

lemma subset_closure_iff_forall_subset_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    Y ⊆ M.closure X ↔ ∀ F, M.Flat F → X ⊆ F → Y ⊆ F := by
  simp [M.closure_eq_sInter X]

lemma Flat.closure (hF : M.Flat F) : M.closure F = F := by
  simp_rw [M.closure_eq_sInter F, subset_antisymm_iff, subset_sInter_iff, mem_setOf,
    and_imp, imp_self, implies_true, and_true]
  refine sInter_subset_of_mem (by simpa [Subset.rfl])

@[simp] lemma closure_ground (M : Matroid α) : M.closure M.E = M.E :=
  (M.closure_subset_ground M.E).antisymm (M.subset_closure M.E)

@[simp] lemma closure_univ (M : Matroid α) : M.closure univ = univ := by
  simp [closure]

lemma closure_subset_closure (M : Matroid α) (h : X ⊆ Y) : M.closure X ⊆ M.closure Y :=
  M.closure.monotone' h

lemma closure_mono (M : Matroid α) : Monotone M.closure :=
  fun _ _ ↦ M.closure_subset_closure

lemma closure_closure (M : Matroid α) (X : Set α) : M.closure (M.closure X) = M.closure X :=
  M.closure.idempotent X

lemma closure_subset_closure_iff_subset_closure : M.closure X ⊆ M.closure Y ↔ X ⊆ M.closure Y :=
  (M.closure.le_closure_iff (x := X) (y := Y)).symm

lemma closure_subset_closure_of_subset_closure (hXY : X ⊆ M.closure Y) :
    M.closure X ⊆ M.closure Y :=
  closure_subset_closure_iff_subset_closure.2 hXY

lemma closure_self_inter_ground_eq  (M : Matroid α) (X : Set α) :
    M.closure X ∩ M.E = M.closure (X ∩ M.E) := by
  refine (subset_inter (M.closure_mono inter_subset_left) (M.closure_subset_ground _)).antisymm' ?_
  rw [closure_eq_union_closure_inter_ground_self, union_inter_distrib_right, union_subset_iff]
  exact ⟨inter_subset_left, M.subset_closure _⟩

lemma subset_closure_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    X ⊆ M.closure Y :=
  hXY.trans (M.subset_closure Y)

lemma exists_of_closure_ssubset (hXY : M.closure X ⊂ M.closure Y) : ∃ e ∈ Y, e ∉ M.closure X := by
  by_contra! hcon
  exact hXY.not_subset (M.closure_subset_closure_of_subset_closure hcon)

lemma mem_closure_of_mem (M : Matroid α) (h : e ∈ X) : e ∈ M.closure X :=
  (M.subset_closure X) h

lemma not_mem_of_mem_diff_closure (he : e ∈ M.E \ M.closure X) : e ∉ X :=
  fun heX ↦ he.2 <| M.mem_closure_of_mem heX

lemma closure_iUnion_closure_eq_closure_iUnion (M : Matroid α) (Xs : ι → Set α) :
    M.closure (⋃ i, M.closure (Xs i)) = M.closure (⋃ i, Xs i) :=
  M.closure.closure_iSup_closure Xs

lemma closure_iUnion_congr {ι : Type*} (Xs Ys : ι → Set α)
    (h : ∀ i, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i, Xs i) = M.closure (⋃ i, Ys i) := by
  rw [← M.closure_iUnion_closure_eq_closure_iUnion]
  simp [h, M.closure_iUnion_closure_eq_closure_iUnion]

lemma closure_biUnion_closure_eq_closure_sUnion (M : Matroid α) (Xs : Set (Set α)) :
    M.closure (⋃ X ∈ Xs, M.closure X) = M.closure (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion, biUnion_eq_iUnion, closure_iUnion_closure_eq_closure_iUnion]

lemma closure_biUnion_closure_eq_closure_biUnion (M : Matroid α) (Xs : ι → Set α) (A : Set ι) :
    M.closure (⋃ i ∈ A, M.closure (Xs i)) = M.closure (⋃ i ∈ A, Xs i) := by
  rw [biUnion_eq_iUnion, M.closure_iUnion_closure_eq_closure_iUnion, biUnion_eq_iUnion]

lemma closure_biUnion_congr (M : Matroid α) (Xs Ys : ι → Set α) (A : Set ι)
    (h : ∀ i ∈ A, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i ∈ A, Xs i) = M.closure (⋃ i ∈ A, Ys i) := by
  rw [← closure_biUnion_closure_eq_closure_biUnion, iUnion₂_congr h,
    closure_biUnion_closure_eq_closure_biUnion]

@[simp] lemma closure_closure_union_closure_eq_closure_union (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X ∪ M.closure Y) = M.closure (X ∪ Y) := by
  rw [eq_comm, union_eq_iUnion, ← closure_iUnion_closure_eq_closure_iUnion, union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]

@[simp] lemma closure_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y) := by
  rw [← closure_closure_union_closure_eq_closure_union, closure_closure,
    closure_closure_union_closure_eq_closure_union]

@[simp] lemma closure_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y) := by
  rw [← closure_closure_union_closure_eq_closure_union, closure_closure,
    closure_closure_union_closure_eq_closure_union]

@[simp] lemma closure_insert_closure_eq_closure_insert (M : Matroid α) (e : α) (X : Set α) :
    M.closure (insert e (M.closure X)) = M.closure (insert e X) := by
  simp_rw [← singleton_union, closure_union_closure_right_eq]

@[simp] lemma closure_union_closure_empty_eq (M : Matroid α) (X : Set α) :
    M.closure X ∪ M.closure ∅ = M.closure X :=
  union_eq_self_of_subset_right (M.closure_subset_closure (empty_subset _))

@[simp] lemma closure_empty_union_closure_eq (M : Matroid α) (X : Set α) :
    M.closure ∅ ∪ M.closure X = M.closure X :=
  union_eq_self_of_subset_left (M.closure_subset_closure (empty_subset _))

lemma closure_insert_eq_of_mem_closure (he : e ∈ M.closure X) :
    M.closure (insert e X) = M.closure X := by
  rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem he, closure_closure]

lemma mem_closure_self (M : Matroid α) (e : α) : e ∈ M.closure {e} :=
  mem_closure_of_mem _ rfl

lemma mem_closure_iff_mem_of_not_mem_ground (he : e ∉ M.E) : e ∈ M.closure X ↔ e ∈ X := by
  rw [closure_eq_union_closure_inter_ground_self, mem_union, or_iff_right_iff_imp]
  exact fun hecl ↦ False.elim <| he <| M.closure_subset_ground (X ∩ M.E) (by aesop_mat) hecl

-- Independence and Bases

lemma Indep.closure_eq_setOf_basis_insert (hI : M.Indep I) :
    M.closure I = {x | M.Basis I (insert x I)} := by
  set F := {x | M.Basis I (insert x I)}
  have hIF : M.Basis I F := hI.basis_setOf_insert_basis

  have hF : M.Flat F := by
    rw [flat_iff_forall_basis]
    refine ⟨fun J X hJF hJX e heX ↦ (?_ : M.Basis _ _), hIF.subset_ground⟩
    exact (hIF.basis_of_basis_of_subset_of_subset (hJX.basis_union hJF) hJF.subset
      (hIF.subset.trans subset_union_right)).basis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans subset_union_right))

  rw [subset_antisymm_iff, M.closure_eq_sInter I, subset_sInter_iff,
    and_iff_right (sInter_subset_of_mem (by simp [hF, hIF.subset]))]

  rintro F' ⟨hF', hIF'⟩ e (he : M.Basis I (insert e I))
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2
  exact (hF'.subset_of_basis_of_basis hJ (he.basis_union_of_subset hJ.indep hIJ))
    (Or.inr (mem_insert _ _))

lemma Indep.insert_basis_iff_mem_closure (hI : M.Indep I) :
    M.Basis I (insert e I) ↔ e ∈ M.closure I := by
  rw [hI.closure_eq_setOf_basis_insert, mem_setOf]

lemma Indep.basis_closure (hI : M.Indep I) : M.Basis I (M.closure I) := by
  rw [hI.closure_eq_setOf_basis_insert]; exact hI.basis_setOf_insert_basis

lemma Basis.closure_eq_closure (h : M.Basis I X) : M.closure X = M.closure I := by
  apply (M.closure_subset_closure h.subset).antisymm'
  rw [← M.closure_closure I, h.indep.closure_eq_setOf_basis_insert]
  exact M.closure_subset_closure fun e he ↦
    (h.basis_subset (subset_insert _ _) (insert_subset he h.subset))

lemma Basis.closure_eq_right (h : M.Basis I (M.closure X)) : M.closure I = M.closure X :=
  M.closure_closure X ▸ h.closure_eq_closure.symm

lemma Basis.subset_closure (h : M.Basis I X) : X ⊆ M.closure I := by
  rw [← closure_subset_closure_iff_subset_closure, h.closure_eq_closure]

lemma Basis'.closure_eq_closure (h : M.Basis' I X) : M.closure I = M.closure (X ∩ M.E) := by
  rw [h.basis_inter_ground.closure_eq_closure]

lemma Basis.basis_closure_right (h : M.Basis I X) : M.Basis I (M.closure X) := by
  rw [h.closure_eq_closure]
  exact h.indep.basis_closure

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

/-- This can be used for rewriting if the LHS is inside a quantifier where `f = e` is not known.-/
lemma Indep.insert_diff_indep_iff (hI : M.Indep (I \ {e})) (heI : e ∈ I) :
    M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.closure (I \ {e}) ∨ f ∈ I := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_diff_singleton_comm hne.symm, hI.insert_indep_iff, mem_diff_singleton,
    and_iff_left hne.symm]

lemma Indep.basis_of_subset_of_subset_closure (hI : M.Indep I) (hIX : I ⊆ X) (hXI : X ⊆ M.closure I) :
    M.Basis I X :=
  hI.basis_closure.basis_subset hIX hXI

lemma basis_iff_indep_subset_closure : M.Basis I X ↔ M.Indep I ∧ I ⊆ X ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, h.subset, h.subset_closure⟩, fun h ↦ h.1.basis_of_subset_of_subset_closure h.2.1 h.2.2⟩

lemma Indep.base_of_ground_subset_closure (hI : M.Indep I) (h : M.E ⊆ M.closure I) : M.Base I := by
  rw [← basis_ground_iff]; exact hI.basis_of_subset_of_subset_closure hI.subset_ground h

lemma Base.closure_eq (hB : M.Base B) : M.closure B = M.E := by
  rw [← basis_ground_iff] at hB; rw [← hB.closure_eq_closure, closure_ground]

lemma Base.mem_closure (hB : M.Base B) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.closure B := by
  rwa [hB.closure_eq]

lemma Base.closure_of_superset (hB : M.Base B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = M.E :=
  (M.closure_subset_ground _).antisymm (hB.closure_eq ▸ M.closure_subset_closure hBX)

lemma base_iff_indep_closure_eq : M.Base B ↔ M.Indep B ∧ M.closure B = M.E := by
  rw [← basis_ground_iff, basis_iff_indep_subset_closure, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h ↦ (M.closure_subset_ground _).antisymm h.2,
    fun h ↦ ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩

lemma Indep.base_iff_ground_subset_closure (hI : M.Indep I) : M.Base I ↔ M.E ⊆ M.closure I :=
  ⟨fun h ↦ by rw [h.closure_eq], hI.base_of_ground_subset_closure⟩

lemma Indep.closure_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J ⊆ I) : M.closure J ∩ I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff, and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.basis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

lemma Indep.closure_sInter_eq_biInter_closure_of_forall_subset {Js : Set (Set α)} (hI : M.Indep I)
    (hne : Js.Nonempty) (hIs : ∀ J ∈ Js, J ⊆ I) : M.closure (⋂₀ Js) = (⋂ J ∈ Js, M.closure J)  := by
  rw [subset_antisymm_iff, subset_iInter₂_iff]
  have hiX : ⋂₀ Js ⊆ I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine ⟨ fun X hX ↦ M.closure_subset_closure (sInter_subset_of_mem hX),
    fun e he ↦ by_contra fun he' ↦ ?_⟩
  rw [mem_iInter₂] at he
  have heEI : e ∈ M.E \ I := by
    obtain ⟨J, hJ⟩ := hne
    have hJE := (hIs _ hJ).trans hI.subset_ground
    refine ⟨M.closure_subset_ground J hJE (he _ hJ), fun heI ↦ he' ?_⟩
    refine mem_closure_of_mem _ (fun X hX ↦ ?_)
    rw [← hI.closure_inter_eq_self_of_subset (hIs X hX)]
    exact ⟨he X hX, heI⟩

  rw [hiI.not_mem_closure_iff_of_not_mem (not_mem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_basis_of_subset (insert_subset_insert hiX)
    (insert_subset heEI.1 hI.subset_ground)

  have hIb : M.Basis I (insert e I) := by
    rw [hI.insert_basis_iff_mem_closure]; exact (M.closure_subset_closure (hIs _ hne.some_mem)) (he _ hne.some_mem)

  obtain ⟨f, hfIJ, hfb⟩ :=  hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩
  obtain rfl := hI.eq_of_basis (hfb.basis_subset (insert_subset hfIJ.1
    (by (rw [diff_subset_iff, singleton_union]; exact hJI.subset))) (subset_insert _ _))

  refine' hfIJ.2 (heJ (mem_insert_of_mem _ fun X hX' ↦ by_contra fun hfX ↦ _))

  obtain (hd | heX) := ((hI.subset (hIs X hX')).mem_closure_iff).mp (he _ hX')
  · refine' (hJI.indep.subset (insert_subset (heJ (mem_insert _ _)) _)).not_dep hd
    specialize hIs _ hX'
    rw [← singleton_union, ← diff_subset_iff, diff_singleton_eq_self hfX] at hIs
    exact hIs.trans diff_subset
  exact heEI.2 (hIs _ hX' heX)

lemma closure_iInter_eq_iInter_closure_of_iUnion_indep {ι : Type*} [hι : Nonempty ι]
    (Is : ι → Set α) (h : M.Indep (⋃ i, Is i)) :  M.closure (⋂ i, Is i) = (⋂ i, M.closure (Is i)) := by
  convert h.closure_sInter_eq_biInter_closure_of_forall_subset (range_nonempty Is) (by simp [subset_iUnion])
  simp

lemma closure_sInter_eq_biInter_closure_of_sUnion_indep (Is : Set (Set α)) (hIs : Is.Nonempty)
    (h : M.Indep (⋃₀ Is)) :  M.closure (⋂₀ Is) = (⋂ I ∈ Is, M.closure I) :=
  h.closure_sInter_eq_biInter_closure_of_forall_subset hIs (fun _ ↦ subset_sUnion_of_mem)

lemma closure_biInter_eq_biInter_closure_of_biUnion_indep {ι : Type*} {A : Set ι} (hA : A.Nonempty)
    {I : ι → Set α} (h : M.Indep (⋃ i ∈ A, I i)) : M.closure (⋂ i ∈ A, I i) = ⋂ i ∈ A, M.closure (I i) := by
  have := hA.coe_sort
  convert closure_iInter_eq_iInter_closure_of_iUnion_indep (ι := A) (Is := fun i ↦ I i) (by simpa) <;> simp

lemma Indep.closure_iInter_eq_biInter_closure_of_forall_subset {ι : Type*} [hι : Nonempty ι] {Js : ι → Set α}
    (hI : M.Indep I) (hJs : ∀ i, Js i ⊆ I) : M.closure (⋂ i, Js i) = ⋂ i, M.closure (Js i) :=
  closure_iInter_eq_iInter_closure_of_iUnion_indep _ (hI.subset <| by simpa)

lemma Indep.closure_inter_eq_inter_closure (h : M.Indep (I ∪ J)) : M.closure (I ∩ J) = M.closure I ∩ M.closure J := by
  rw [inter_eq_iInter, closure_iInter_eq_iInter_closure_of_iUnion_indep, inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]

lemma basis_iff_basis_closure_of_subset (hIX : I ⊆ X) :
    M.Basis I X ↔ M.Basis I (M.closure X) :=
  ⟨fun h ↦ h.basis_closure_right, fun h ↦ h.basis_subset hIX (M.subset_closure X)⟩

lemma Basis.basis_of_closure_eq_closure (hI : M.Basis I X) (hY : I ⊆ Y)
    (h : M.closure X = M.closure Y) : M.Basis I Y := by
  refine hI.indep.basis_of_subset_of_subset_closure hY ?_
  rw [← hI.closure_eq_closure, h]
  exact M.subset_closure Y

lemma basis_union_iff_indep_closure : M.Basis I (I ∪ X) ↔ M.Indep I ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ ↦
    hI.basis_closure.basis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩

lemma basis_iff_indep_closure : M.Basis I X ↔ M.Indep I ∧ X ⊆ M.closure I ∧ I ⊆ X :=
  ⟨fun h ↦ ⟨h.indep, h.subset_closure, h.subset⟩, fun h ↦
    (basis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).basis_subset h.2.2 subset_union_right⟩

lemma Basis.eq_of_closure_subset (hI : M.Basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.closure J) : J = I := by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI, inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

@[simp] lemma empty_basis_iff : M.Basis ∅ X ↔ X ⊆ M.closure ∅ := by
  rw [basis_iff_indep_closure, and_iff_right M.empty_indep, and_iff_left (empty_subset _)]



-- Sets

lemma closure_insert_of_not_mem_ground (he : e ∉ M.E) (X : Set α) :
    M.closure (insert e X) = insert e (M.closure X) := by
  rw [closure_eq_union_closure_inter_ground_self, insert_inter_of_not_mem he,
    M.closure_eq_union_closure_inter_ground_self X, ← union_singleton, ← union_singleton,
    union_assoc]

lemma mem_closure_insert (he : e ∉ M.closure X) (hef : e ∈ M.closure (insert f X)) :
    f ∈ M.closure (insert e X) := by
  rw [← coexpand_closure_eq] at *
  set M' := M.coexpand

  obtain ⟨I, hI⟩ := M'.exists_basis X
  rw [hI.closure_eq_closure, hI.indep.not_mem_closure_iff] at he
  rw [← closure_insert_closure_eq_closure_insert, hI.closure_eq_closure,
    closure_insert_closure_eq_closure_insert, he.1.mem_closure_iff] at *
  rw [or_iff_not_imp_left, not_dep_iff, insert_comm]
  intro hi
  rw [(hi.subset (subset_insert _ _)).mem_closure_iff, or_iff_not_imp_left, not_dep_iff,
    imp_iff_right hi, mem_insert_iff, or_iff_left he.2] at hef
  simp [hef]

lemma closure_exchange (he : e ∈ M.closure (insert f X) \ M.closure X) :
    f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨mem_closure_insert he.2 he.1, fun hf ↦ by simp [closure_insert_eq_of_mem_closure hf] at he⟩

lemma closure_exchange_iff :
    e ∈ M.closure (insert f X) \ M.closure X ↔ f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨closure_exchange, closure_exchange⟩

lemma mem_closure_insert_comm (h : e ∈ M.closure X ↔ f ∈ M.closure X) :
    e ∈ M.closure (insert f X) ↔ f ∈ M.closure (insert e X) := by
  by_cases he : e ∈ M.closure X
  · exact iff_of_true (M.closure_subset_closure (subset_insert _ _) he)
      (M.closure_subset_closure (subset_insert _ _) (by rwa [← h]))
  simpa [he, mt h.2 he] using closure_exchange_iff (e := e) (f := f) (M := M) (X := X)

lemma closure_insert_eq_closure_insert_of_mem (he : e ∈ M.closure (insert f X) \ M.closure X) :
    M.closure (insert e X) = M.closure (insert f X) := by
  rw [eq_comm, ← closure_closure, ← insert_eq_of_mem he.1, closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_closure, ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem (closure_exchange he).1, closure_closure, closure_closure]

lemma closure_diff_singleton_eq_closure (h : e ∈ M.closure (X \ {e})) :
    M.closure (X \ {e}) = M.closure X := by
  refine' (em (e ∈ X)).elim (fun h' ↦ _) (fun h' ↦ by rw [diff_singleton_eq_self h'])
  convert M.closure_insert_closure_eq_closure_insert e (X \ {e}) using 1
  · rw [insert_eq_of_mem h, closure_closure]
  rw [insert_diff_singleton, insert_eq_of_mem h']

lemma mem_closure_diff_singleton_iff_closure (he : e ∈ X) :
    e ∈ M.closure (X \ {e}) ↔ M.closure (X \ {e}) = M.closure X :=
  ⟨closure_diff_singleton_eq_closure, fun h ↦ by rw [h]; exact M.mem_closure_of_mem he⟩

lemma indep_iff_not_mem_closure_diff_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ e ∈ I, e ∉ M.closure (I \ {e}) := by
  use fun h e heI he ↦ ((h.closure_inter_eq_self_of_subset diff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine' hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h _ he _)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M.closure_subset_closure (subset_diff_singleton hJ.subset heJ))

lemma indep_iff_not_mem_closure_diff_forall' :
    M.Indep I ↔ (∀ e ∈ I, e ∉ M.closure (I \ {e})) ∧ I ⊆ M.E :=
  ⟨fun h ↦ ⟨(indep_iff_not_mem_closure_diff_forall h.subset_ground).mp h, h.subset_ground⟩, fun h ↦
    (indep_iff_not_mem_closure_diff_forall h.2).mpr h.1⟩

lemma Indep.not_mem_closure_diff_of_mem (hI : M.Indep I) (he : e ∈ I) : e ∉ M.closure (I \ {e}) :=
  (indep_iff_not_mem_closure_diff_forall'.1 hI).1 e he

lemma indep_iff_closure_diff_ne_forall :
    M.Indep I ↔ (∀ e ∈ I, M.closure (I \ {e}) ≠ M.closure I) ∧ I ⊆ M.E := by
  rw [indep_iff_not_mem_closure_diff_forall', and_congr_left_iff]
  exact fun _ ↦ ⟨fun h e heI h_eq ↦ h e heI <| h_eq ▸ M.subset_closure I heI,
    fun h e heI hmem ↦ h e heI <| by rwa [mem_closure_diff_singleton_iff_closure heI] at hmem⟩

lemma Indep.closure_diff_singleton_ssubset (hI : M.Indep I) (he : e ∈ I) :
    M.closure (I \ {e}) ⊂ M.closure I :=
  (M.closure_subset_closure diff_subset).ssubset_of_ne <|
    (indep_iff_closure_diff_ne_forall.1 hI).1 e he

lemma indep_iff_closure_ssubset_ssubset_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ (∀ J, J ⊂ I → M.closure J ⊂ M.closure I) := by
  refine ⟨fun hI J hJI ↦ ?_,
    fun h ↦ indep_iff_closure_diff_ne_forall.2 ⟨fun e heI ↦ (h _ (by simpa)).ne, hI⟩⟩
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
  exact ssubset_of_subset_of_ssubset
    (M.closure_subset_closure (subset_diff_singleton hJI.subset heJ)) <|
    hI.closure_diff_singleton_ssubset heI

lemma insert_not_indep_of_mem_closure_not_mem (he : e ∈ M.closure X) (heX : e ∉ X) :
    ¬ M.Indep (insert e X) :=
  fun hi ↦ by simp [(hi.subset (subset_insert _ _)).insert_indep_iff, he, heX] at hi

lemma insert_dep_of_mem_closure_not_mem (he : e ∈ M.closure X) (heX : e ∉ X)
    (hX : X ⊆ M.E := by aesop_mat) : M.Dep (insert e X) := by
  rw [dep_iff, insert_subset_iff, and_iff_left hX,
    and_iff_left (M.closure_diff_self_subset_ground X ⟨he, heX⟩)]
  exact insert_not_indep_of_mem_closure_not_mem he heX

lemma ext_closure {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h : ∀ X, M₁.closure X = M₂.closure X) :
    M₁ = M₂ :=
  eq_of_indep_iff_indep_forall hE fun I _ ↦ by simp_rw [indep_iff_closure_diff_ne_forall, h, hE]

@[simp] lemma restrict_closure_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).closure X = (M.closure (X ∩ R) ∩ R) ∪ X ∪ (R \ M.E) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis (X ∩ R)
  have hI' := (basis_restrict_iff'.mp hI).1
  ext e
  by_cases heX : e ∈ X
  · exact iff_of_true (subset_closure _ _ heX) (by simp [heX])

  obtain ⟨⟨-, hIR⟩, hIE⟩ : (I ⊆ X ∧ I ⊆ R) ∧ I ⊆ M.E := by simpa [subset_inter_iff] using hI'.subset
  have h' : M.Indep (insert e I) → e ∈ M.E := fun h ↦ h.subset_ground <| .inl rfl
  have heI : e ∉ I := not_mem_subset (subset_inter_iff.1 hI.subset).1 heX

  suffices e ∈ R → (M.Indep (insert e I) → e ∉ R ↔ ¬M.Indep (insert e I) ∧ e ∈ M.E ∨ e ∉ M.E) by
    simpa [closure_eq_union_closure_inter_ground_self _ X, and_comm (a := e ∈ R), ← or_and_right,
      hI.closure_eq_closure, hI.indep.mem_closure_iff_of_not_mem heI, dep_iff,
      insert_subset_iff, hIR, heX, closure_eq_union_closure_inter_ground_self _ (X ∩ R),
      hI'.closure_eq_closure, hI'.indep.mem_closure_iff_of_not_mem heI, hIE]

  tauto

lemma restrict_closure_eq (M : Matroid α) (hXR : X ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).closure X = M.closure X ∩ R := by
  rw [restrict_closure_eq', diff_eq_empty.2 hR, union_empty, inter_eq_self_of_subset_left hXR,
    union_eq_left, subset_inter_iff]
  simpa

@[simp] lemma comap_closure_eq {β : Type*} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).closure X = f ⁻¹' M.closure (f '' (X ∩ f ⁻¹' M.E)) ∪ X := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_basis (X ∩ f ⁻¹' M.E)
  obtain ⟨hI', hIinj, -⟩ := comap_basis_iff.1 hI
  obtain ⟨hIX, hIE⟩ := subset_inter_iff.1 hI.subset
  ext x
  by_cases hxX : x ∈ X
  · exact iff_of_true (subset_closure _ _ hxX) (.inr hxX)
  have hxI : x ∉ I := not_mem_subset hIX hxX
  have h' : f x ∉ M.E → ∀ y ∈ I, ¬ (f y = f x) := fun hxE y hyI hyx ↦ (hyx ▸ hxE) (hIE hyI)
  simp only [closure_eq_union_closure_inter_ground_self _ X, comap_ground_eq,
    hI.closure_eq_closure, mem_union, hI.indep.mem_closure_iff_of_not_mem hxI, dep_iff,
    comap_indep_iff, image_insert_eq, injOn_insert hxI, hIinj, mem_image, not_exists, not_and,
    not_forall, insert_subset_iff, mem_preimage, hxX,
    or_false, hI'.closure_eq_closure, hI'.indep.mem_closure_iff, image_subset_iff]
  tauto

@[simp] lemma map_closure_eq {β : Type*} (M : Matroid α) (f : α → β) (hf) (X : Set β) :
    (M.map f hf).closure X = f '' M.closure (f ⁻¹' (X ∩ f '' M.E) ∩ M.E) ∪ X := by
  obtain ⟨I, hI⟩ := (M.map f hf).exists_basis (X ∩ f '' M.E)
  obtain ⟨I, X', h, rfl, hX'⟩ := map_basis_iff'.1 hI
  ext e
  rw [closure_eq_union_closure_inter_ground_self]
  by_cases heX : e ∈ X
  · simp [heX]
  simp only [map_ground, mem_union, heX, or_false]
  obtain (he | ⟨e, he, rfl⟩) := em' <| e ∈ f '' M.E
  · exact iff_of_false (not_mem_subset (closure_subset_ground _ _ inter_subset_right) he)
      (not_mem_subset (image_subset _ (closure_subset_ground _ _)) he)
  have heI : insert e I ⊆ M.E := insert_subset he h.indep.subset_ground
  rw [hf.mem_image_iff (closure_subset_ground _ _) he]
  simp_rw [hI.closure_eq_closure, hX', hf.preimage_image_inter h.subset_ground,
    h.closure_eq_closure, h.indep.mem_closure_iff, hI.indep.mem_closure_iff]
  rw [hf.mem_image_iff h.indep.subset_ground he, ← image_insert_eq, dep_iff,
    map_image_indep_iff (insert_subset he h.indep.subset_ground), map_ground,
    and_iff_left (image_subset _ heI), not_indep_iff]


section Spanning

variable {S T : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
  a base of `M`. -/
def Spanning (M : Matroid α) (S : Set α) := M.closure S = M.E

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Spanning.subset_ground (hS : M.Spanning S) : S ⊆ M.E :=
  (M.subset_closure S).trans_eq hS

lemma Spanning.closure_eq (hS : M.Spanning S) : M.closure S = M.E :=
  hS

lemma spanning_def : M.Spanning S ↔ M.closure S = M.E := Iff.rfl

@[simp] lemma closure_spanning_iff : M.Spanning (M.closure S) ↔ M.Spanning S := by
  rw [spanning_def, spanning_def, closure_closure]

lemma ground_subset_closure_iff_spanning (hS : S ⊆ M.E := by aesop_mat) :
    M.E ⊆ M.closure S ↔ M.Spanning S := by
  rw [spanning_def, subset_antisymm_iff, and_iff_right (closure_subset_ground _ _)]

lemma not_spanning_iff_closure (hS : S ⊆ M.E := by aesop_mat) :
    ¬M.Spanning S ↔ M.closure S ⊂ M.E := by
  rw [spanning_def, ssubset_iff_subset_ne, iff_and_self,
    iff_true_intro (M.closure_subset_ground _)]
  exact fun _ ↦ trivial

lemma Spanning.superset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T := by
  rw [← ground_subset_closure_iff_spanning, ← hS.closure_eq]
  exact closure_subset_closure _ hST

lemma Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (S ∪ X) :=
  hS.superset subset_union_left

lemma Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.superset subset_union_right

lemma Base.spanning (hB : M.Base B) : M.Spanning B :=
  hB.closure_eq

lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  M.closure_ground

lemma Base.superset_spanning (hB : M.Base B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

lemma spanning_iff_superset_base' : M.Spanning S ↔ (∃ B, M.Base B ∧ B ⊆ S) ∧ S ⊆ M.E := by
  refine' ⟨fun h ↦ ⟨_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.superset hBS⟩
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
  rw [coindep_iff_compl_spanning, spanning_def]

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

@[simp] lemma uniqueBaseOn_closure_eq (I E X : Set α) :
    (uniqueBaseOn I E).closure X = (E \ I) ∪ X := by
  have hb : (uniqueBaseOn (I ∩ E) E).Basis (X ∩ E ∩ (I ∩ E)) (X ∩ E) :=
    (uniqueBaseOn_basis_iff inter_subset_right inter_subset_right).2 rfl
  rw [← uniqueBaseOn_inter_ground_eq I E, closure_eq_union_closure_inter_ground_self,
    uniqueBaseOn_ground, hb.closure_eq_closure]
  ext e
  rw [mem_union, Indep.mem_closure_iff (by simp [subset_def]), dep_iff]
  simp only [uniqueBaseOn_indep_iff', subset_def, mem_insert_iff, mem_inter_iff, and_self_right,
    forall_eq_or_imp, and_imp, imp_self, implies_true, and_true, not_and, uniqueBaseOn_ground,
    mem_union, mem_diff, not_forall, Classical.not_imp, not_and]
  tauto

lemma freeOn_closure_eq (E X : Set α) : (freeOn E).closure X = X := by
  simp [← uniqueBaseOn_self]

@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = X := by
  rw [← freeOn_empty, freeOn_closure_eq]

@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E ∪ X := by
  rw [← uniqueBaseOn_empty, uniqueBaseOn_closure_eq, diff_empty]

lemma closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ ext_closure rfl fun X ↦ ?_, fun hM ↦ by rw [hM]; simp⟩
  rw [loopyOn_closure_eq, subset_antisymm_iff, union_subset_iff, ← h,  and_iff_left
    (subset_closure _ _), and_iff_left (closure_subset_closure _ (empty_subset _)), h]
  apply closure_subset_ground_union

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
  simp_rw [← biInter_inter hA, closure_biInter_eq_biInter_closure_of_biUnion_indep hA
    (I := fun i ↦ (X i) ∩ I) (hI.subset (by simp)), subset_iInter_iff]
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
-- -- (λ e heI heclosure, hJ e (hIJ heI) (closure_mono (diff_subset_diff_left hIJ) hecl))
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
-- -- matroid_of_indep (closure_indep cl)
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
