import Matroid.Simple
import Matroid.Closure
import Matroid.ForMathlib.Other
import Matroid.Minor.Basic

namespace Matroid
open Set BigOperators

variable {α : Type*} {M : Matroid α} {I B : Set α} {Ys Xs : (Set (Set α))}

--- predicate (functions to `Prop`) should be in upper camel case, without underscores
@[pp_dot] def ModularFamily (M : Matroid α) (Xs : Set (Set α)) := ∃ B, M.Modular Xs B

theorem ModularFamily.subset (hXs : M.ModularFamily Xs) (hYs : Ys ⊆ Xs) : M.ModularFamily Ys := by
  obtain ⟨B, hB⟩ := hXs
  exact ⟨B, hB.subset hYs⟩

@[pp_dot] def ModularPair (M : Matroid α) (X Y : Set α) : Prop := M.ModularFamily {X,Y}

theorem modularPair_iff : M.ModularPair X Y ↔
    ∃ I, M.Basis I (X ∪ Y) ∧ M.Basis (X ∩ I) X
      ∧ M.Basis (Y ∩ I) Y ∧ M.Basis (X ∩ Y ∩ I) (X ∩ Y):= by
  refine ⟨fun ⟨B, hB⟩ ↦ ?_, fun ⟨I, hu, hIX, hIY, hi⟩ ↦ ?_⟩
  · refine ⟨(X ∪ Y) ∩ B, by simpa using hB.basis_sUnion, ?_, ?_, ?_⟩
    · rw [←inter_assoc, inter_eq_self_of_subset_left (subset_union_left _ _)]
      exact hB.inter_basis_of_mem <| mem_insert X {Y}
    · rw [← inter_assoc, inter_eq_self_of_subset_left (subset_union_right _ _)]
      exact hB.inter_basis_of_mem <| mem_insert_of_mem X rfl
    rw [← inter_assoc, inter_eq_self_of_subset_left
      ((inter_subset_left _ _).trans (subset_union_left _ _))]
    simpa using hB.2 Subset.rfl (by simp)
  obtain ⟨B, hB, hIB⟩ := hu.indep
  refine ⟨B, hB, fun Ys hYs hne ↦ ?_⟩
  obtain (rfl | rfl | rfl) := (Nonempty.subset_pair_iff hne).1 hYs
  <;> simp only [sInter_singleton, sInter_pair]
  · rwa [← hIX.inter_eq_of_subset_indep (inter_subset_inter_right _ hIB) (hB.indep.inter_left _),
      inter_right_comm, inter_self] at hIX
  · rwa [← hIY.inter_eq_of_subset_indep (inter_subset_inter_right _ hIB) (hB.indep.inter_left _),
      inter_right_comm, inter_self] at hIY
  rwa [← hi.inter_eq_of_subset_indep (inter_subset_inter_right _ hIB) (hB.indep.inter_left _),
      inter_right_comm, inter_self] at hi

theorem ModularPair.symm (h : M.ModularPair X Y) : M.ModularPair Y X := by
  rw [ModularPair] at h ⊢; rwa [pair_comm]

theorem ModularPair.comm : M.ModularPair X Y ↔ M.ModularPair Y X :=
  ⟨ModularPair.symm, ModularPair.symm⟩

@[pp_dot] def ModularSet (M : Matroid α) (X : Set α) : Prop :=
    ∀ {F}, M.Flat F → M.ModularPair X F

@[pp_dot] def ModularMatroid (M : Matroid α) : Prop :=
    ∀ {F}, M.Flat F → M.ModularSet F

theorem modular_ground (M : Matroid α) : M.ModularSet M.E := by
  intro F hF
  obtain ⟨I, hI⟩ := M.exists_basis F
  obtain ⟨B, hB, hIB⟩ := hI.indep
  obtain rfl := hI.inter_eq_of_subset_indep hIB hB.indep
  refine modularPair_iff.2 ⟨B, ?_⟩
  rw [union_eq_self_of_subset_right hF.subset_ground,
    inter_eq_self_of_subset_right hB.subset_ground, basis_ground_iff,
    inter_eq_self_of_subset_right hF.subset_ground, inter_comm F]
  exact ⟨hB, hB, hI, hI⟩

theorem modular_loops (M : Matroid α) : M.ModularSet (M.cl ∅) := by
  intro F hF
  obtain ⟨I, hI⟩ := M.exists_basis F
  refine modularPair_iff.2 ⟨I, ?_⟩
  rwa [basis_loops_iff,inter_right_comm, inter_comm _ I,  hI.indep.disjoint_loops.inter_eq,
    and_iff_right rfl, empty_inter, empty_basis_iff,
    inter_eq_self_of_subset_left hF.loops_subset, union_eq_self_of_subset_left hF.loops_subset,
    and_iff_right hI, and_iff_left Subset.rfl, inter_eq_self_of_subset_right hI.subset]

/-- It is probably best for a modular cut to be a structure - it is easier to reason about
  different ways of getting them, equivalences, etc. -/
@[ext] structure ModularCut (M : Matroid α) where
  (Fs : Set (Set α))
  (forall_flat : ∀ {F}, F ∈ Fs → M.Flat F)
  (up_closed : ∀ {F F'}, F ∈ Fs → F ⊆ F' → M.Flat F' → F' ∈ Fs)
  (modular : ∀ Xs ⊆ Fs, Xs.Nonempty → M.ModularFamily Xs → ⋂₀ Xs ∈ Fs)

/-- Instance so `M.ModularCut` can be treated like a set via coercion. -/
instance {M : Matroid α} : SetLike (M.ModularCut) (Set α) where
  coe := ModularCut.Fs
  coe_injective' := by rintro ⟨C, -, -, -⟩ ⟨C', -, -, -⟩; simp

@[simp] theorem ModularCut.mem_Fs_iff {C : M.ModularCut} : I ∈ C.Fs ↔ I ∈ C := Iff.rfl

theorem ModularCut.superset (C : M.ModularCut) (hF : F ∈ C) (hFF' : F ⊆ F') (hF' : M.Flat F') :
    F' ∈ C :=
  C.up_closed hF hFF' hF'

theorem ModularCut.flat (C : M.ModularCut) (hF : F ∈ C) : M.Flat F :=
    C.forall_flat hF

theorem ModularCut.sInter (C : M.ModularCut) (hXs : Xs ⊆ C) (hXsmod : M.ModularFamily Xs)
    (hne : Xs.Nonempty) : ⋂₀ Xs ∈ C :=
  C.modular _ hXs hne hXsmod

theorem ModularCut.inter (C : M.ModularCut) (hF : F ∈ C) (hF' : F' ∈ C)
    (hFF' : M.ModularPair F F') : F ∩ F' ∈ C := by
  simpa using C.sInter (pair_subset hF hF') hFF' (by simp)


lemma modular_finite_intersection {M : Matroid α} {X : Set (Set α)} {Fs : Set (Set α)}
    (forall_flat : ∀ {F}, F ∈ Fs → M.Flat F)
    (pair_modular : ∀ {F F'}, F ∈ Fs → F' ∈ Fs → M.ModularFamily {F, F'} → F ∩ F' ∈ Fs)
    (hfin : X.Finite) (hsub : X ⊆ Fs) (hmod : M.ModularFamily X) (hnone : X.Nonempty) :
    sInter X ∈ Fs := by
  obtain (⟨x, rfl⟩ | X_nt) := hnone.exists_eq_singleton_or_nontrivial
  · rwa [sInter_singleton, ←singleton_subset_iff]
  obtain ⟨x, y, xy_ne, xy_sub⟩ := nontrivial_iff_pair_subset.1 X_nt
  have x_eq_insert : X = insert x (X \ {x})
  · simp [pair_subset_iff.1 xy_sub]
  rw [x_eq_insert, sInter_insert]
  obtain ⟨B, B_mod⟩ := hmod
  apply pair_modular (hsub (xy_sub (mem_insert _ _))) _
  · refine' ⟨B, B_mod.1, fun Ys Ys_sub Ys_none ↦ _⟩
    obtain (rfl | rfl | rfl) := (Nonempty.subset_pair_iff Ys_none).1 Ys_sub
    · apply B_mod.2 (singleton_subset_iff.2 (xy_sub (mem_insert _ _))) (singleton_nonempty _)
    · rw [sInter_singleton]
      apply B_mod.2 (diff_subset _ _) ⟨y, ⟨(pair_subset_iff.1 xy_sub).2, _⟩⟩
      exact xy_ne.symm
    rw [sInter_pair, ←sInter_insert, ←x_eq_insert]
    exact B_mod.2 (rfl.subset) hnone
  have encard_lt : (X \ {x}).encard < X.encard
  · apply hfin.encard_lt_encard ⟨diff_subset _ _, (not_subset.2 ⟨x, (xy_sub (mem_insert _ _)), _⟩)⟩
    exact fun x_mem ↦ absurd rfl x_mem.2
  have:= encard_lt
  apply modular_finite_intersection forall_flat pair_modular (hfin.subset (diff_subset _ _)) ((diff_subset _ _).trans
   hsub) ⟨B, (B_mod.subset (diff_subset _ _))⟩ ⟨y, ⟨(pair_subset_iff.1 xy_sub).2, _⟩⟩
  exact xy_ne.symm
termination_by _ => X.encard

/-- In a finite matroid, the 'pair property' is enough to construct a modular cut .
  The @[simps] will autogenerate simp lemmas. -/
@[simps] def ModularCut.ofForallPair {M : Matroid α} [M.Finite] {Fs : Set (Set α)}
    (forall_flat : ∀ {F}, F ∈ Fs → M.Flat F)
    (up_closed : ∀ {F F'}, F ∈ Fs → F ⊆ F' → M.Flat F' → F' ∈ Fs)
    (pair_modular : ∀ {F F'}, F ∈ Fs → F' ∈ Fs → M.ModularFamily {F, F'} → F ∩ F' ∈ Fs) :
    M.ModularCut where
  Fs := Fs
  forall_flat := forall_flat
  up_closed := up_closed
  -- Use the stuff in `modular_cut_iff_modular_cut'_finite` to prove this.
  modular := by
    intro Xs hsub hnone hXs
    have hfin : Xs.Finite
    · have flat_fin : {F | M.Flat F}.Finite
      · apply Finite.subset M.ground_finite.finite_subsets (fun F F_Flat ↦ F_Flat.subset_ground)
      apply Finite.subset (Finite.subset (flat_fin) (fun F F_C ↦ forall_flat F_C)) hsub
    exact modular_finite_intersection forall_flat pair_modular hfin hsub hXs hnone


/-- A modular cut will determine an extension. -/
@[simps] def ModularCut.extensionIndepMatroid (C : M.ModularCut) (e : α) :
    IndepMatroid α where
  E := insert e M.E
  -- this definition of independence is equivalent to yours, but doesn't use `ite` and
  -- so doesn't need decidability. It also means that the hypothesis that `e ∉ M.E`
  -- isn't needed as part of the definition; you just get the original matroid back
  -- as the extension if `e ∈ M.E`. (Theorems about the extension can have `e ∉ M.E`
  -- as part of the hypothesis if needed).
  Indep I := M.Indep I ∨ (e ∈ I \ M.E ∧ M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ C)
  indep_empty := Or.inl M.empty_indep
  indep_subset I J := by
    -- tricks like the line below are good for deconstructing `Or`s without `by_cases, if_pos`, etc.
    rintro (hJ | ⟨⟨heJ, heE⟩, hJ, hJC⟩) hIJ
    · exact Or.inl <| hJ.subset hIJ
    by_cases heI : e ∈ I
    · refine Or.inr ⟨⟨heI, heE⟩, hJ.subset (diff_subset_diff_left hIJ), fun hIC ↦ hJC ?_⟩
      exact C.superset hIC (M.cl_subset_cl (diff_subset_diff_left hIJ)) (M.cl_flat _)
    refine Or.inl (hJ.subset <| subset_diff_singleton hIJ heI)
  indep_aug := by
    -- hard work here
    sorry
  indep_maximal := by
    -- more hard work here
    sorry
  subset_ground := by
    rintro I (hI | ⟨-, hI, -⟩)
    · exact hI.subset_ground.trans <| subset_insert _ _
    simpa using diff_subset_iff.1 hI.subset_ground

def ModularCut.extension (C : M.ModularCut) (e : α) := (C.extensionIndepMatroid e).matroid

@[simp] theorem ModularCut.extension_ground (C : M.ModularCut) (e : α) :
    (C.extension e).E = insert e M.E := rfl

@[simp] theorem ModularCut.extension_indep (C : M.ModularCut) (e : α) {I : Set α} :
    (C.extension e).Indep I ↔
      M.Indep I ∨ (e ∈ I \ M.E ∧ M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ C) := by
  simp [extension]

/-- If `e ∈ M.E`, then the extension is just the matroid itself -/
theorem ModularCut.extension_eq_self (C : M.ModularCut) (he : e ∈ M.E) :
    C.extension e = M :=
  eq_of_indep_iff_indep_forall (by simpa) (fun _ _ ↦ by simp [he])

theorem ModularCut.extension_delete (C : M.ModularCut) {e : α} (he : e ∉ M.E) :
    (C.extension e) ⟍ e = M :=
  eq_of_indep_iff_indep_forall (by simpa)
    (fun I hI ↦ by simp [show e ∉ I from fun heI ↦ by simpa using hI heI])

theorem ModularCut.extension_cl_eq_of_mem (C : M.ModularCut) (he : e ∉ M.E) (hX : M.cl X ∈ C) :
    (C.extension e).cl X = insert e (M.cl X) := by
  sorry

theorem ModularCut.extension_cl_eq_of_not_mem (C : M.ModularCut) (he : e ∉ M.E) (hX : M.cl X ∉ C) :
    (C.extension e).cl X = M.cl X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  have hI' : (extension C e).Basis' I X
  sorry
  -- · rw [← C.extension_delete he, delete_elem, delete_basis'_iff] at hI
  --   have := hI.indep.basis_insert_iff (e := e)



theorem ModularCut.extension_flat_iff (C : M.ModularCut) (e : α) (he : e ∉ M.E) :
    (C.extension e).Flat F ↔ (M.Flat F ∧ F ∉ C) ∨ (e ∈ F ∧ F \ {e} ∈ C) := by
  sorry


/-- Type-theory nonsense. -/
@[simps] def ModularCut.congr {M N : Matroid α} (C : M.ModularCut) (hMN : M = N) :
    N.ModularCut where
  Fs := C.Fs
  forall_flat := by subst hMN; exact C.forall_flat
  up_closed := by subst hMN; exact C.up_closed
  modular := by subst hMN; exact C.modular

@[simp] theorem ModularCut.mem_congr {M N : Matroid α} (C : M.ModularCut) (hMN : M = N) :
    F ∈ C.congr hMN ↔ F ∈ C := Iff.rfl

/-- The modular cut corresponding to a deletion. (This is the empty cut if `e ∉ M.E`) -/
@[simps] def ModularCut.ofDelete (M : Matroid α) (e : α) : (M ⟍ e).ModularCut where
  Fs := {F | (M ⟍ e).Flat F ∧ e ∈ M.cl F}
  forall_flat := by simp only [delete_elem, mem_setOf_eq, and_imp]; tauto
  up_closed := by
    simp only [delete_elem, mem_setOf_eq, and_imp]
    exact fun {F F'} hF heF hFF' hF' ↦ ⟨hF', M.cl_subset_cl hFF' heF⟩
  modular := by
    sorry

@[simp] theorem ModularCut.mem_ofDelete_iff (M : Matroid α) (e : α) {F : Set α} :
  F ∈ ModularCut.ofDelete M e ↔ (M ⟍ e).Flat F ∧ e ∈ M.cl F := Iff.rfl

def ModularCut.extensionEquiv (M : Matroid α) (e : α) (he : e ∉ M.E) :
    M.ModularCut ≃ {N : Matroid α | e ∈ N.E ∧ N ⟍ e = M} where
  toFun Fs := ⟨Fs.extension e, mem_insert _ _, Fs.extension_delete he⟩
  invFun N := (ModularCut.ofDelete N e).congr N.prop.2
  left_inv := by
    rintro C
    -- I think the `ext` here might have been the trick you were missing. If you have
    -- `structure = structure` with a bunch of junk as a goal, then `ext` will
    -- reduce it to goals of the form `structure field = structure field`,
    -- which often makes the simplifier a lot happier.
    ext F
    simp only [delete_elem, mem_setOf_eq, extension_ground, congr_Fs, SetLike.mem_coe,
      mem_ofDelete_iff, mem_Fs_iff]

    -- some matroidy goal left
    sorry

  right_inv := by
    rintro ⟨N, hN, rfl⟩
    simp only [delete_elem, coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
    apply eq_of_indep_iff_indep_forall (by simpa) (fun I hI ↦ ?_)
    by_cases heI : e ∈ I
    · simp only [delete_elem, mem_setOf_eq, extension_indep, delete_indep_iff,
        disjoint_singleton_right, heI, not_true_eq_false, and_false, delete_ground, mem_diff,
        mem_singleton_iff, not_false_eq_true, and_self, and_true, delete_cl_eq, sdiff_idem,
        mem_congr, mem_ofDelete_iff, not_and, true_and, false_or]
      -- matroidy goals. Should be able to reduce to the case where `I \ {e}` is independent.

      sorry
    simp [heI]


    -- some matroidy goal left
