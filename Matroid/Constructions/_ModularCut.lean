import Matroid.Simple
import Matroid.Closure
import Matroid.ForMathlib.Other
import Matroid.Minor.Basic
import Matroid.Modular
import Matroid.Modular

namespace Matroid
open Set BigOperators

variable {α : Type*} {M : Matroid α} {I B : Set α} {Ys Xs : (Set (Set α))}

--- predicate (functions to `Prop`) should be in upper camel case, without underscores
-- @[pp_dot] def ModularFamily (M : Matroid α) (Xs : Set (Set α)) := ∃ B, M.Modular Xs B

-- theorem ModularFamily.subset (hXs : M.ModularFamily Xs) (hYs : Ys ⊆ Xs) : M.ModularFamily Ys := by
--   obtain ⟨B, hB⟩ := hXs
--   exact ⟨B, hB.subset hYs⟩

-- @[pp_dot] def ModularPair (M : Matroid α) (X Y : Set α) : Prop := M.ModularFamily {X,Y}

-- theorem modularPair_iff : M.ModularPair X Y ↔
--     ∃ I, M.Basis I (X ∪ Y) ∧ M.Basis (X ∩ I) X
--       ∧ M.Basis (Y ∩ I) Y ∧ M.Basis (X ∩ Y ∩ I) (X ∩ Y):= by
--   refine ⟨fun ⟨B, hB⟩ ↦ ?_, fun ⟨I, hu, hIX, hIY, hi⟩ ↦ ?_⟩
--   · refine ⟨(X ∪ Y) ∩ B, by simpa using hB.basis_sUnion, ?_, ?_, ?_⟩
--     · rw [←inter_assoc, inter_eq_self_of_subset_left (subset_union_left _ _)]
--       exact hB.inter_basis_of_mem <| mem_insert X {Y}
--     · rw [← inter_assoc, inter_eq_self_of_subset_left (subset_union_right _ _)]
--       exact hB.inter_basis_of_mem <| mem_insert_of_mem X rfl
--     rw [← inter_assoc, inter_eq_self_of_subset_left
--       ((inter_subset_left _ _).trans (subset_union_left _ _))]
--     simpa using hB.2 Subset.rfl (by simp)
--   obtain ⟨B, hB, hIB⟩ := hu.indep
--   refine ⟨B, hB, fun Ys hYs hne ↦ ?_⟩
--   obtain (rfl | rfl | rfl) := (Nonempty.subset_pair_iff hne).1 hYs
--   <;> simp only [sInter_singleton, sInter_pair]
--   · rwa [← hIX.inter_eq_of_subset_indep (inter_subset_inter_right _ hIB) (hB.indep.inter_left _),
--       inter_right_comm, inter_self] at hIX
--   · rwa [← hIY.inter_eq_of_subset_indep (inter_subset_inter_right _ hIB) (hB.indep.inter_left _),
--       inter_right_comm, inter_self] at hIY
--   rwa [← hi.inter_eq_of_subset_indep (inter_subset_inter_right _ hIB) (hB.indep.inter_left _),
--       inter_right_comm, inter_self] at hi

-- theorem ModularPair.symm (h : M.ModularPair X Y) : M.ModularPair Y X := by
--   rw [ModularPair] at h ⊢; rwa [pair_comm]

-- theorem ModularPair.comm : M.ModularPair X Y ↔ M.ModularPair Y X :=
--   ⟨ModularPair.symm, ModularPair.symm⟩

-- @[pp_dot] def ModularSet (M : Matroid α) (X : Set α) : Prop :=
--     ∀ {F}, M.Flat F → M.ModularPair X F

-- @[pp_dot] def ModularMatroid (M : Matroid α) : Prop :=
--     ∀ {F}, M.Flat F → M.ModularSet F

-- theorem modular_ground (M : Matroid α) : M.ModularSet M.E := by
--   intro F hF
--   obtain ⟨I, hI⟩ := M.exists_basis F
--   obtain ⟨B, hB, hIB⟩ := hI.indep
--   obtain rfl := hI.inter_eq_of_subset_indep hIB hB.indep
--   refine modularPair_iff.2 ⟨B, ?_⟩
--   rw [union_eq_self_of_subset_right hF.subset_ground,
--     inter_eq_self_of_subset_right hB.subset_ground, basis_ground_iff,
--     inter_eq_self_of_subset_right hF.subset_ground, inter_comm F]
--   exact ⟨hB, hB, hI, hI⟩

-- theorem modular_loops (M : Matroid α) : M.ModularSet (M.cl ∅) := by
--   intro F hF
--   obtain ⟨I, hI⟩ := M.exists_basis F
--   refine modularPair_iff.2 ⟨I, ?_⟩
--   rwa [basis_loops_iff,inter_right_comm, inter_comm _ I,  hI.indep.disjoint_loops.inter_eq,
--     and_iff_right rfl, empty_inter, empty_basis_iff,
--     inter_eq_self_of_subset_left hF.loops_subset, union_eq_self_of_subset_left hF.loops_subset,
--     and_iff_right hI, and_iff_left Subset.rfl, inter_eq_self_of_subset_right hI.subset]

/-- It is probably best for a modular cut to be a structure - it is easier to reason about
  different ways of getting them, equivalences, etc. -/
@[ext] structure ModularCut (M : Matroid α) where
  (Fs : Set (Set α))
  (forall_flat : ∀ {F}, F ∈ Fs → M.Flat F)
  (up_closed : ∀ {F F'}, F ∈ Fs → F ⊆ F' → M.Flat F' → F' ∈ Fs)
  (modular : ∀ Xs ⊆ Fs, Xs.Nonempty → M.ModularFamily (fun X : Xs ↦ X) → ⋂₀ Xs ∈ Fs)

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

theorem ModularCut.sInter (C : M.ModularCut) (hXs : Xs ⊆ C)
    (hXsmod : M.ModularFamily (fun X : Xs ↦ X)) (hne : Xs.Nonempty) : ⋂₀ Xs ∈ C :=
  C.modular _ hXs hne hXsmod

theorem ModularCut.inter (C : M.ModularCut) (hF : F ∈ C) (hF' : F' ∈ C)
    (hFF' : M.ModularPair F F') : F ∩ F' ∈ C := by
  rw [←sInter_pair]
  apply C.sInter (pair_subset hF hF') _ (by simp)
  let ⟨B, hB⟩ := hFF'
  refine' ⟨B, hB.1, fun i ↦ _⟩
  dsimp
  obtain (eq | ne) := mem_insert_iff.2 (Subtype.mem i)
  · rw [eq]
    exact hB.2 true
  rw [mem_singleton_iff.1 ne]
  exact hB.2 false

#check Indep.cl_inter_eq_self_of_subset

lemma ModularCut.insert_cl (C : M.ModularCut) (hI : M.Indep (insert a (insert b X)))
    (ha : M.cl (insert a X) ∈ C) (hb : M.cl (insert b X) ∈ C) (hne : a ≠ b) : M.cl X ∈ C := by
  rw [←(@inter_insert_eq _ X _ _ hne), Indep.cl_inter_eq_inter_cl]
  · apply C.inter ha hb (modularPair_iff.2 ⟨(insert a (insert b X)), hI, _⟩)
    rw [hI.cl_inter_eq_self_of_subset (subset_insert _ _), hI.cl_inter_eq_self_of_subset]
    · refine' ⟨Indep.basis_cl (hI.subset _), Indep.basis_cl (hI.subset (subset_insert _ _))⟩
      rw [insert_comm]
      exact subset_insert _ _
    rw [insert_comm]
    exact subset_insert _ _
  rwa [union_insert_eq, insert_comm]





lemma ModularBase.subset {M : Matroid α} {X Y : Set (Set α)} {B : Set α}
    (hmod : M.ModularBase B (fun x : X ↦ x)) (hsub : Y ⊆ X) : M.ModularBase B (fun y : Y ↦ y) :=
  ⟨hmod.1, fun i ↦ hmod.2 ⟨i.1, hsub i.2⟩⟩


lemma ModularFamily.subset {M : Matroid α} {X Y : Set (Set α)}
    (hmod : M.ModularFamily (fun x : X ↦ x)) (hsub : Y ⊆ X) : M.ModularFamily (fun y : Y ↦ y) := by
  obtain ⟨B, hB⟩ := hmod
  refine' ⟨B, hB.subset hsub⟩


lemma modular_finite_intersection {M : Matroid α} {X : Set (Set α)} {Fs : Set (Set α)}
    (forall_flat : ∀ {F}, F ∈ Fs → M.Flat F)
    (pair_modular : ∀ {F F'}, F ∈ Fs → F' ∈ Fs → M.ModularPair F F' → F ∩ F' ∈ Fs)
    (hfin : X.Finite) (hsub : X ⊆ Fs) (hmod : M.ModularFamily (fun x : X ↦ x)) (hnone : X.Nonempty) :
    sInter X ∈ Fs := by
  obtain (⟨x, rfl⟩ | X_nt) := hnone.exists_eq_singleton_or_nontrivial
  · rwa [sInter_singleton, ←singleton_subset_iff]
  obtain ⟨x, y, xy_ne, xy_sub⟩ := nontrivial_iff_pair_subset.1 X_nt
  have x_eq_insert : X = insert x (X \ {x})
  · simp [pair_subset_iff.1 xy_sub]
  rw [x_eq_insert, sInter_insert]
  obtain ⟨B, B_mod⟩ := hmod
  apply pair_modular (hsub (xy_sub (mem_insert _ _))) _
  · refine' ⟨B, B_mod.1, Bool.forall_bool.2 ⟨_, _⟩⟩
    · dsimp
      rw [sInter_eq_biInter]
      apply B_mod.1.indep.interBasis_biInter ⟨y, _⟩ (fun i i_mem ↦ B_mod.2 ⟨i, i_mem.1⟩)
      exact ⟨(pair_subset_iff.1 xy_sub).2, xy_ne.symm⟩
    apply (B_mod.2 ⟨x, xy_sub (mem_insert _ _)⟩)
  have encard_lt : (X \ {x}).encard < X.encard
  · apply hfin.encard_lt_encard ⟨diff_subset _ _, (not_subset.2 ⟨x, (xy_sub (mem_insert _ _)), _⟩)⟩
    exact fun x_mem ↦ absurd rfl x_mem.2
  have:= encard_lt
  apply modular_finite_intersection forall_flat pair_modular (hfin.subset (diff_subset _ _)) ((diff_subset _ _).trans
   hsub) (ModularFamily.subset ⟨B, B_mod⟩ (diff_subset _ _)) ⟨y, ⟨(pair_subset_iff.1 xy_sub).2, _⟩⟩
  exact xy_ne.symm
termination_by _ => X.encard

/-- In a finite matroid, the 'pair property' is enough to construct a modular cut .
  The @[simps] will autogenerate simp lemmas. -/
@[simps] def ModularCut.ofForallPair {M : Matroid α} [M.Finite] {Fs : Set (Set α)}
    (forall_flat : ∀ {F}, F ∈ Fs → M.Flat F)
    (up_closed : ∀ {F F'}, F ∈ Fs → F ⊆ F' → M.Flat F' → F' ∈ Fs)
    (pair_modular : ∀ {F F'}, F ∈ Fs → F' ∈ Fs → M.ModularPair F F' → F ∩ F' ∈ Fs) :
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
    rintro I J I_ind I_nmax ⟨J_ind, J_max⟩
    have J_base_of_ind : M.Indep J → M.Base J
    · intro J_ind
      rw [base_iff_maximal_indep]
      refine' ⟨J_ind, fun X X_ind X_sub ↦ _⟩
      apply subset_antisymm X_sub (J_max _ X_sub)
      exact Or.inl X_ind
    rw [mem_maximals_iff] at I_nmax
    push_neg at I_nmax
    obtain ⟨Y, Y_ind, I_sub_Y, I_ne_Y⟩ := I_nmax I_ind
    dsimp at Y_ind J_ind
    obtain (I_ind | ⟨e_in_I, I_ind, I_cl_not_mem⟩) := I_ind
    · --rw [if_pos (I_sub_Y e_in_I)] at Y_ind
      obtain (J_ind | ⟨e_in_J, J_ind, J_cl_not_mem⟩) := J_ind
      ·  --e in neither case
        have I_not_base : ¬ M.Base I
        · intro h_f
          obtain (Y_ind | ⟨e_in_Y, Y_ind, Y_cl_not_mem⟩) := Y_ind
          · apply (h_f.dep_of_ssubset (I_ne_Y.ssubset_of_subset I_sub_Y)
            Y_ind.subset_ground).not_indep Y_ind
          have e_in_J := not_mem_subset J_ind.subset_ground e_in_Y.2
          rw [Spanning.cl_eq _] at Y_cl_not_mem
          · apply (ne_insert_of_not_mem J e_in_J (subset_antisymm (subset_insert e J) (J_max _ (subset_insert e J))))
            refine' Or.inr ⟨⟨mem_insert _ _, e_in_Y.2⟩, by simp [J_ind, e_in_J], _⟩
            rwa [insert_diff_self_of_not_mem e_in_J, (J_base_of_ind J_ind).cl_eq]
          rw [spanning_iff_superset_base (Y_ind.subset_ground)]
          refine' ⟨I, h_f, subset_diff_singleton I_sub_Y (not_mem_subset I_ind.subset_ground e_in_Y.2)⟩
        obtain ⟨x, x_mem, x_ind⟩ := I_ind.exists_insert_of_not_base I_not_base
         (J_base_of_ind J_ind)
        refine' ⟨x, x_mem, Or.inl x_ind⟩
      -- e in J only case
      have e_notin_I:= not_mem_subset I_ind.subset_ground e_in_J.2
      by_cases cl_I_mem : M.cl I ∈ C
      · by_contra' h_f
        have J_diff_sub_cl_I : J \ {e} ⊆ M.cl I
        · rintro j ⟨j_J, (j_ne : j ≠ e)⟩
          rw [I_ind.mem_cl_iff, or_comm, or_iff_not_imp_left, dep_iff]
          intro j_nI
          refine' ⟨(not_or.1 (h_f j ⟨j_J, j_nI⟩)).1, insert_subset (J_ind.subset_ground ⟨j_J, j_ne⟩) I_ind.subset_ground⟩
        have I_J_exch : ∃ i ∈ I \ (J \ {e}), M.Indep (insert i (J \ {e}))
        · apply J_ind.exists_insert_of_not_basis (subset_union_left _ I)
          · intro h_f
            apply J_cl_not_mem (C.superset cl_I_mem _ (M.cl_flat _))
            rw [h_f.cl_eq_cl]
            apply M.cl_subset_cl (subset_union_right _ _)
          rw [basis_iff_indep_subset_cl]
          refine' ⟨I_ind, subset_union_right _ _, fun x ↦ _⟩
          rintro (x_J | x_I)
          · exact J_diff_sub_cl_I x_J
          · exact M.mem_cl_of_mem x_I
        obtain ⟨i, i_mem, i_ind⟩ := I_J_exch
        obtain (Y_ind | ⟨e_in_Y, Y_ind, Y_cl_not_mem⟩) := Y_ind
        · obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
          obtain (mem_c | y_in_I) := I_ind.insert_indep_iff.1 (Y_ind.subset
           (insert_subset hy.1 I_sub_Y))
          · have y_insert_indep : M.Indep (insert y (insert i (J \ {e})))
            · rw [i_ind.insert_indep_iff_of_not_mem, mem_diff]
              · refine' ⟨Y_ind.subset_ground hy.1, fun y_cl ↦ _⟩
                apply mem_c.2 (cl_subset_cl_of_subset_cl (insert_subset (M.mem_cl_of_mem i_mem.1
                 I_ind.subset_ground) J_diff_sub_cl_I) y_cl)
              rintro (rfl | y_in_J)
              · exact hy.2 i_mem.1
              exact mem_c.2 (J_diff_sub_cl_I y_in_J)
            apply J_cl_not_mem (C.insert_cl y_insert_indep _ _ _)
            · by_contra insert_not_mem
              apply (J \ {e}).ne_insert_of_not_mem (J \ {e}) _ (subset_antisymm (subset_insert y _) _)
              · exact fun y_mem ↦ mem_c.2 (J_diff_sub_cl_I y_mem)
              rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem mem_c.1 e_in_J.2)]
              apply diff_subset_diff_left (J_max (Or.inr _) (subset_insert _ _))
              rw [←insert_diff_singleton_comm (ne_of_mem_of_not_mem mem_c.1 e_in_J.2)]
              refine' ⟨⟨mem_insert_of_mem _ e_in_J.1, e_in_J.2⟩, y_insert_indep.subset _, insert_not_mem⟩
              rw [insert_comm]
              exact subset_insert _ _
            · by_contra insert_not_mem
              apply (J \ {e}).ne_insert_of_not_mem (J \ {e}) i_mem.2 (subset_antisymm (subset_insert i _) _)
              rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem (I_ind.subset_ground i_mem.1) e_in_J.2)]
              · apply diff_subset_diff_left (J_max (Or.inr _) (subset_insert _ _))
                rw [←insert_diff_singleton_comm (ne_of_mem_of_not_mem (I_ind.subset_ground i_mem.1) e_in_J.2)]
                refine' ⟨⟨mem_insert_of_mem _ e_in_J.1, e_in_J.2⟩, y_insert_indep.subset (subset_insert _ _), insert_not_mem⟩
            exact fun (rfl) ↦ hy.2 i_mem.1
          exact hy.2 y_in_I
        apply Y_cl_not_mem (C.superset cl_I_mem (M.cl_subset_cl (subset_diff_singleton I_sub_Y e_notin_I)) (M.cl_flat _))
      refine' ⟨e, ⟨e_in_J.1, e_notin_I⟩, Or.inr ⟨⟨mem_insert _ _, e_in_J.2⟩, _, _⟩⟩
      · rwa [insert_diff_self_of_not_mem e_notin_I]
      rwa [insert_diff_self_of_not_mem e_notin_I]
    obtain (J_ind | ⟨e_in_J, J_ind, J_cl_not_mem⟩) := J_ind
    --case involving finding 2 to add from J to I where e is in I only
    · obtain (Y_ind | ⟨e_in_Y, Y_ind, Y_cl_not_mem⟩) := Y_ind
      · exact absurd (Y_ind.subset_ground (I_sub_Y e_in_I.1)) e_in_I.2
      have I_nb : ¬ M.Base (I \ {e})
      · intro I_Base
        apply (I_Base.dep_of_ssubset _ Y_ind.subset_ground).not_indep Y_ind
        rw [ssubset_iff_subset_ne]
        refine' ⟨diff_subset_diff_left I_sub_Y, fun diff_eq ↦ _⟩
        apply I_ne_Y (subset_antisymm I_sub_Y _)
        intro y y_in_Y
        obtain (rfl | hne) := eq_or_ne y e
        · exact e_in_I.1
        apply diff_subset I {e}
        rw [diff_eq]
        exact ⟨y_in_Y, hne⟩
      obtain ⟨j₂, hj₂⟩ := I_ind.exists_insert_of_not_base I_nb (J_base_of_ind J_ind)
      rw [diff_diff_right, Disjoint.inter_eq (disjoint_singleton_right.2 (not_mem_subset J_ind.subset_ground e_in_Y.2)),
       union_empty] at hj₂
      by_cases j₂I_b : M.Base (insert j₂ (I \ {e}))
      · refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [←insert_diff_singleton_comm (ne_of_mem_of_not_mem (J_ind.subset_ground hj₂.1.1)
         e_in_Y.2), and_iff_right hj₂.2]
        obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
        obtain (rfl | ne) := eq_or_ne j₂ y
        · exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, fun cl_mem ↦ Y_cl_not_mem
           (C.superset cl_mem (M.cl_subset_cl (insert_subset ⟨hy.1,
           (ne_of_mem_of_not_mem e_in_I.1 hj₂.1.2).symm⟩ (diff_subset_diff_left I_sub_Y)))
           (M.cl_flat _))⟩
        have y_notin : y ∉ insert j₂ (I \ {e})
        · rw [mem_insert_iff, not_or, mem_diff, not_and_or]
          exact ⟨ne.symm, Or.inl hy.2⟩
        have base_insert:= @Matroid.Base.exchange_base_of_indep _ _ _ _ j₂ j₂I_b y_notin
        rw [insert_diff_self_of_not_mem (not_mem_subset (diff_subset _ _) hj₂.1.2)] at base_insert
        rw [j₂I_b.cl_eq]
        rw [Spanning.cl_eq _] at Y_cl_not_mem
        · refine Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, Y_cl_not_mem⟩
        have insert_y_subset_Y : insert y (I \ {e}) ⊆ Y \ {e}
        · rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem e_in_I (not_mem_subset (diff_subset _ _) hy.2)).symm]
          exact diff_subset_diff_left (insert_subset hy.1 I_sub_Y)
        apply Base.superset_spanning (base_insert (Y_ind.subset insert_y_subset_Y))
         insert_y_subset_Y Y_ind.subset_ground
      obtain ⟨j₁, j₁_mem, j₁_ind⟩:=hj₂.2.exists_insert_of_not_base j₂I_b
       (J_base_of_ind J_ind)
      have hne : j₁ ≠ j₂:= fun (rfl) ↦ j₁_mem.2 (mem_insert _ _)
      by_cases j₁_cl_mem_c : M.cl (insert j₁ (I \ {e})) ∈ C
      · by_cases j₂_cl_mem_c : M.cl (insert j₂ (I \ {e})) ∈ C
        · exact absurd (C.insert_cl j₁_ind j₁_cl_mem_c j₂_cl_mem_c hne) I_cl_not_mem
        refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [←insert_diff_singleton_comm
         (ne_of_mem_of_not_mem (J_ind.subset_ground hj₂.1.1) e_in_I.2) _]
        exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, j₁_ind.subset (subset_insert _ _),
         j₂_cl_mem_c⟩
      refine' ⟨j₁, ⟨j₁_mem.1, fun hf ↦ j₁_mem.2 (mem_insert_of_mem _ ⟨hf, ne_of_mem_of_not_mem
       j₁_mem.1 (not_mem_subset J_ind.subset_ground e_in_I.2)⟩)⟩, _⟩
      dsimp
      rw [ ←insert_diff_singleton_comm (ne_of_mem_of_not_mem j₁_mem.1 (not_mem_subset J_ind.subset_ground e_in_I.2)) _]
      exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, j₁_ind.subset (insert_subset_insert (subset_insert _ _)), j₁_cl_mem_c⟩
    --hard case, e in both
    by_contra' h_f
    obtain (Y_ind | ⟨e_in_Y, Y_ind, Y_cl_not_mem⟩) := Y_ind
    · exact e_in_I.2 (Y_ind.subset_ground (I_sub_Y e_in_I.1))
    have J_insert_mem_C : ∀ x ∉ J, M.Indep (insert x (J \ {e})) → M.cl (insert x (J \ {e})) ∈ C
    · intro x x_notin_J x_ind
      by_contra not_mem_C
      apply (ne_insert_of_not_mem _ x_notin_J) (subset_antisymm (subset_insert _ _) (J_max _
        (subset_insert _ _)))
      dsimp
      rw [←insert_diff_singleton_comm (ne_of_mem_of_not_mem
        e_in_J.1 x_notin_J).symm]
      exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_J.1, e_in_J.2⟩, x_ind, not_mem_C⟩
    obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
    have y_ind : M.Indep ((insert y I) \ {e}) ∧ M.cl ((insert y I) \ {e}) ∉ C
    · refine' ⟨Y_ind.subset (diff_subset_diff_left (insert_subset hy.1 I_sub_Y)),
        fun cl_mem_C ↦ _⟩
      exact Y_cl_not_mem (C.superset cl_mem_C (M.cl_subset_cl (diff_subset_diff_left (insert_subset
        hy.1 I_sub_Y))) (M.cl_flat _))
    have y_notin_J : y ∉ J
    · intro y_in_J
      apply h_f y ⟨y_in_J, hy.2⟩ _
      exact Or.inr ⟨⟨mem_insert_of_mem y e_in_I.1, e_in_I.2⟩, y_ind⟩
    have y_ground := (Y_ind.subset_ground (mem_diff_of_mem hy.1 (ne_of_mem_of_not_mem e_in_J
      (not_mem_subset (diff_subset _ _) y_notin_J)).symm))
    have x := I_ind.subset_basis_of_subset (diff_subset_diff_left (subset_union_left I J)) ?_
    · obtain ⟨I', I'_basis, I_sub_I'⟩ := x
      have : (I \ {e} ⊂ I')
      · have hne:= (ne_of_mem_of_not_mem e_in_J (not_mem_subset (diff_subset _ M.E) y_notin_J)).symm
        apply Ne.ssubset_of_subset _ I_sub_I'
        rintro rfl
        apply insert_ne_self.2 y_notin_J (subset_antisymm (J_max _ (subset_insert _ _))
          (subset_insert _ _))
        dsimp
        rw [←insert_diff_singleton_comm
          hne, ←J_ind.not_mem_cl_iff_of_not_mem _]
        refine' Or.inr ⟨⟨(mem_insert_of_mem _ e_in_J.1), e_in_J.2⟩, not_mem_subset (M.cl_subset_cl (diff_subset_diff_left
          (subset_union_right I J))) _, _⟩
        · rw [←I'_basis.cl_eq_cl, I_ind.not_mem_cl_iff_of_not_mem (not_mem_subset
          (diff_subset _ _) hy.2),
          insert_diff_singleton_comm hne]
          exact y_ind.1
        rw [insert_diff_singleton_comm hne]
        intro cl_mem_C
        apply y_ind.2 (C.superset cl_mem_C _ (M.cl_flat _))
        rw [←insert_diff_singleton_comm hne I,
          ←cl_insert_cl_eq_cl_insert, I'_basis.cl_eq_cl, cl_insert_cl_eq_cl_insert,
          ←insert_diff_singleton_comm hne]
        · apply M.cl_subset_cl (insert_subset_insert (diff_subset_diff_left
          (subset_union_right _ _)))
        exact not_mem_subset (diff_subset _ _) y_notin_J
      obtain ⟨a, a_not_mem, a_insert_sub⟩ := ssubset_iff_insert.1 this
      have a_mem_JI : a ∈ J \ I
      · obtain ⟨(aI | aJ), a_ne_e⟩:= I'_basis.subset (a_insert_sub (mem_insert a _))
        apply absurd (⟨aI, a_ne_e⟩ : (a ∈ I \ {e})) a_not_mem
        apply (mem_diff _).2 ⟨aJ, _⟩
        intro aI
        apply a_not_mem ⟨aI, a_ne_e⟩
      obtain (ssubset | rfl) := ssubset_or_eq_of_subset a_insert_sub
      · obtain ⟨b, b_not_mem, b_insert_sub⟩ := ssubset_iff_insert.1 ssubset
        apply I_cl_not_mem (C.insert_cl (I'_basis.indep.subset b_insert_sub) _ _ (ne_of_mem_of_not_mem (mem_insert _ _) b_not_mem).symm)
        · rw [insert_comm] at b_insert_sub
          have:= h_f b ?_
          · rw [not_or, not_and, not_and, not_not,
              ←insert_diff_singleton_comm (ne_of_mem_of_not_mem ((I'_basis.indep.subset
              b_insert_sub).subset_ground (mem_insert_of_mem _ (mem_insert _ _))) e_in_I.2)] at this
            exact this.2 ⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩ (I'_basis.indep.subset ((subset_insert _ _).trans b_insert_sub))
          rw [insert_comm] at b_insert_sub
          obtain ⟨(bI | bJ), b_ne_e⟩:= I'_basis.subset (b_insert_sub (mem_insert b _))
          · apply absurd (⟨bI, b_ne_e⟩ : (b ∈ I \ {e})) _
            apply not_mem_subset (subset_insert _ _) b_not_mem
          apply (mem_diff _).2 ⟨bJ, _⟩
          intro bI
          apply b_not_mem (mem_insert_of_mem _ ⟨bI, b_ne_e⟩)
        have:= h_f a a_mem_JI
        rw [not_or, not_and, not_and, not_not,
          ←insert_diff_singleton_comm] at this
        · exact this.2 ⟨(mem_insert_of_mem _ e_in_I.1), e_in_I.2⟩ (I'_basis.indep.subset a_insert_sub)
        exact ne_of_mem_of_not_mem ((I'_basis.indep.subset a_insert_sub).subset_ground
          (mem_insert _ _)) e_in_I.2
      have J_not_basis : ¬ M.Basis (J \ {e}) ((I ∪ J) \ {e})
      · intro J_basis
        apply h_f a a_mem_JI
        rw [←insert_diff_singleton_comm, I'_basis.cl_eq_cl, ←J_basis.cl_eq_cl]
        exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, I'_basis.indep, J_cl_not_mem⟩
        exact (ne_of_mem_of_not_mem e_in_I.1 a_mem_JI.2).symm
      obtain ⟨i, hi⟩ := J_ind.exists_insert_of_not_basis (diff_subset_diff_left
       (subset_union_right _ _)) J_not_basis I'_basis
      have I'_base : M.Base (insert a (I \ {e}))
      · by_contra I'_not_base
        obtain ⟨B, hB⟩ := M.exists_base
        obtain ⟨b, hb⟩ := I'_basis.indep.exists_insert_of_not_base I'_not_base hB
        have b_notin_union : b ∉ I ∪ J
        · intro b_mem_union
          have : b ∈ (I ∪ J) \ {e}
          · rwa [mem_diff_singleton, and_iff_left (ne_of_mem_of_not_mem
            (hB.subset_ground hb.1.1) e_in_I.2)]
          apply ((I'_basis.indep.insert_indep_iff_of_not_mem hb.1.2).1 hb.2).2
          rw [I'_basis.cl_eq_cl]
          apply M.mem_cl_of_mem this I'_basis.subset_ground
        have bi_J_indep : M.Indep (insert b (insert i (J \ {e})))
        · rw [hi.2.insert_indep_iff, mem_diff _, and_iff_right (hB.subset_ground hb.1.1)]
          rw [I'_basis.indep.insert_indep_iff_of_not_mem hb.1.2, I'_basis.cl_eq_cl] at hb
          apply Or.inl (not_mem_subset (M.cl_subset_cl _) hb.2.2)
          rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem (hi.2.subset_ground
            (mem_insert _ _)) e_in_I.2)]
          apply diff_subset_diff_left (insert_subset _ (subset_union_right _ _))
          obtain (rfl | i_Jd) := hi.1.1
          · apply (Or.inr a_mem_JI.1)
          apply (Or.inl i_Jd.1)
        apply J_cl_not_mem (C.insert_cl bi_J_indep _ _ (ne_of_mem_of_not_mem hi.1.1 hb.1.2).symm)
        · apply J_insert_mem_C b (not_mem_subset (subset_union_right _ _) b_notin_union) _
          rw [insert_comm] at bi_J_indep
          exact bi_J_indep.subset (subset_insert _ _)
        apply J_insert_mem_C i _ hi.2
        intro i_J
        apply hi.1.2 ⟨i_J, ne_of_mem_of_not_mem (hi.2.subset_ground (mem_insert _ _)) e_in_I.2⟩
      have yI_base : M.Base (insert y (I \ {e}))
      · have base_insert:= @Matroid.Base.exchange_base_of_indep _ _ _ y a I'_base
        rw [insert_diff_self_of_not_mem a_not_mem] at base_insert
        apply base_insert
        · rintro (rfl | y_mem)
          · exact y_notin_J a_mem_JI.1
          exact hy.2 y_mem.1
        rw [insert_diff_singleton_comm (ne_of_mem_of_not_mem y_ground e_in_I.2)]
        exact y_ind.1
      apply h_f a a_mem_JI
      rw [←insert_diff_singleton_comm
        (ne_of_mem_of_not_mem e_in_I (not_mem_subset (diff_subset _ _) a_mem_JI.2)).symm,
        I'_base.cl_eq, ←yI_base.cl_eq, insert_diff_singleton_comm (ne_of_mem_of_not_mem y_ground e_in_I.2)]
      exact Or.inr ⟨⟨(mem_insert_of_mem _ e_in_I.1), (not_mem_subset (M.cl_subset_ground _) e_in_I.2)⟩, I'_base.indep, y_ind.2⟩
    rintro x ⟨(x_I | x_J), (hne : x ≠ e)⟩
    · exact I_ind.subset_ground ⟨x_I, hne⟩
    exact J_ind.subset_ground ⟨x_J, hne⟩



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
    (C.extension e) ⧹ e = M :=
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
  -- · rw [← C.extension_delete he, deleteElem, delete_basis'_iff] at hI
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
@[simps] def ModularCut.ofDelete (M : Matroid α) (e : α) : (M ⧹ e).ModularCut where
  Fs := {F | (M ⧹ e).Flat F ∧ e ∈ M.cl F}
  forall_flat := by simp only [deleteElem, mem_setOf_eq, and_imp]; tauto
  up_closed := by
    simp only [deleteElem, mem_setOf_eq, and_imp]
    exact fun {F F'} hF heF hFF' hF' ↦ ⟨hF', M.cl_subset_cl hFF' heF⟩
  modular := by
    sorry

@[simp] theorem ModularCut.mem_ofDelete_iff (M : Matroid α) (e : α) {F : Set α} :
  F ∈ ModularCut.ofDelete M e ↔ (M ⧹ e).Flat F ∧ e ∈ M.cl F := Iff.rfl

def ModularCut.extensionEquiv (M : Matroid α) (e : α) (he : e ∉ M.E) :
    M.ModularCut ≃ {N : Matroid α | e ∈ N.E ∧ N ⧹ e = M} where
  toFun Fs := ⟨Fs.extension e, mem_insert _ _, Fs.extension_delete he⟩
  invFun N := (ModularCut.ofDelete N e).congr N.prop.2
  left_inv := by
    rintro C
    -- I think the `ext` here might have been the trick you were missing. If you have
    -- `structure = structure` with a bunch of junk as a goal, then `ext` will
    -- reduce it to goals of the form `structure field = structure field`,
    -- which often makes the simplifier a lot happier.
    ext F
    simp only [deleteElem, mem_setOf_eq, extension_ground, congr_Fs, SetLike.mem_coe,
      mem_ofDelete_iff, mem_Fs_iff]

    -- some matroidy goal left
    sorry

  right_inv := by
    rintro ⟨N, hN, rfl⟩
    simp only [deleteElem, coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
    apply eq_of_indep_iff_indep_forall (by simpa) (fun I hI ↦ ?_)
    by_cases heI : e ∈ I
    · simp only [deleteElem, mem_setOf_eq, extension_indep, delete_indep_iff,
        disjoint_singleton_right, heI, not_true_eq_false, and_false, delete_ground, mem_diff,
        mem_singleton_iff, not_false_eq_true, and_self, and_true, delete_cl_eq, sdiff_idem,
        mem_congr, mem_ofDelete_iff, not_and, true_and, false_or]
      -- matroidy goals. Should be able to reduce to the case where `I \ {e}` is independent.

      sorry
    simp [heI]


    -- some matroidy goal left
