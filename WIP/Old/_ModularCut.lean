import Matroid.Simple
import Matroid.ForMathlib.Other
import Matroid.Minor.Basic
import Matroid.Modular.Basic

namespace Matroid
open Set BigOperators

variable {α : Type*} {M : Matroid α} {I B : Set α} {Ys Xs : (Set (Set α))}

--- predicate (functions to `Prop`) should be in upper camel case, without underscores
-- def IsModularFamily (M : Matroid α) (Xs : Set (Set α)) := ∃ B, M.Modular Xs B

-- theorem IsModularFamily.subset (hXs : M.IsModularFamily Xs) (hYs : Ys ⊆ Xs) : M.IsModularFamily Ys := by
--   obtain ⟨B, hB⟩ := hXs
--   exact ⟨B, hB.subset hYs⟩

-- def IsModularPair (M : Matroid α) (X Y : Set α) : Prop := M.IsModularFamily {X,Y}

-- theorem isModularPair_iff : M.IsModularPair X Y ↔
--     ∃ I, M.IsBasis I (X ∪ Y) ∧ M.IsBasis (X ∩ I) X
--       ∧ M.IsBasis (Y ∩ I) Y ∧ M.IsBasis (X ∩ Y ∩ I) (X ∩ Y):= by
--   refine ⟨fun ⟨B, hB⟩ ↦ ?_, fun ⟨I, hu, hIX, hIY, hi⟩ ↦ ?_⟩
--   · refine ⟨(X ∪ Y) ∩ B, by simpa using hB.isBasis_sUnion, ?_, ?_, ?_⟩
--     · rw [← inter_assoc, inter_eq_self_of_subset_left subset_union_left]
--       exact hB.inter_isBasis_of_mem <| mem_insert X {Y}
--     · rw [← inter_assoc, inter_eq_self_of_subset_left subset_union_right]
--       exact hB.inter_isBasis_of_mem <| mem_insert_of_mem X rfl
--     rw [← inter_assoc, inter_eq_self_of_subset_left
--       (inter_subset_left.trans subset_union_left)]
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

-- theorem IsModularPair.symm (h : M.IsModularPair X Y) : M.IsModularPair Y X := by
--   rw [IsModularPair] at h ⊢; rwa [pair_comm]

-- theorem IsModularPair.comm : M.IsModularPair X Y ↔ M.IsModularPair Y X :=
--   ⟨IsModularPair.symm, IsModularPair.symm⟩

-- def ModularSet (M : Matroid α) (X : Set α) : Prop :=
--     ∀ {F}, M.IsFlat F → M.IsModularPair X F

-- def ModularMatroid (M : Matroid α) : Prop :=
--     ∀ {F}, M.IsFlat F → M.ModularSet F

-- theorem modular_ground (M : Matroid α) : M.ModularSet M.E := by
--   intro F hF
--   obtain ⟨I, hI⟩ := M.exists_isBasis F
--   obtain ⟨B, hB, hIB⟩ := hI.indep
--   obtain rfl := hI.inter_eq_of_subset_indep hIB hB.indep
--   refine isModularPair_iff.2 ⟨B, ?_⟩
--   rw [union_eq_self_of_subset_right hF.subset_ground,
--     inter_eq_self_of_subset_right hB.subset_ground, basis_ground_iff,
--     inter_eq_self_of_subset_right hF.subset_ground, inter_comm F]
--   exact ⟨hB, hB, hI, hI⟩

-- theorem modular_loops (M : Matroid α) : M.ModularSet (M.loops) := by
--   intro F hF
--   obtain ⟨I, hI⟩ := M.exists_isBasis F
--   refine isModularPair_iff.2 ⟨I, ?_⟩
--   rwa [isBasis_loops_iff,inter_right_comm, inter_comm _ I,  hI.indep.disjoint_loops.inter_eq,
--     and_iff_right rfl, empty_inter, empty_isBasis_iff,
--     inter_eq_self_of_subset_left hF.loops_subset, union_eq_self_of_subset_left hF.loops_subset,
--     and_iff_right hI, and_iff_left Subset.rfl, inter_eq_self_of_subset_right hI.subset]

/-- It is probably best for a modular cut to be a structure - it is easier to reason about
  different ways of getting them, equivalences, etc. -/
@[ext] structure ModularCut (M : Matroid α) where
  (Fs : Set (Set α))
  (forall_isFlat : ∀ {F}, F ∈ Fs → M.IsFlat F)
  (up_closed : ∀ {F F'}, F ∈ Fs → F ⊆ F' → M.IsFlat F' → F' ∈ Fs)
  (modular : ∀ Xs ⊆ Fs, Xs.Nonempty → M.IsModularFamily (fun X : Xs ↦ X) → ⋂₀ Xs ∈ Fs)

/-- Instance so `M.ModularCut` can be treated like a set via coercion. -/
instance {M : Matroid α} : SetLike (M.ModularCut) (Set α) where
  coe := ModularCut.Fs
  coe_injective' := by rintro ⟨C, -, -, -⟩ ⟨C', -, -, -⟩; simp

def ModularCut.empty (M : Matroid α) : M.ModularCut where
  Fs := ∅
  forall_isFlat := fun F_mem ↦ absurd F_mem (notMem_empty _)
  up_closed := fun F_mem ↦ absurd F_mem (notMem_empty _)
  modular := fun _ Xs_sub Xs_none ↦ absurd (subset_empty_iff.1 Xs_sub).symm (ne_of_ssubset Xs_none.empty_ssubset)

def ModularCut.Nonempty {M : Matroid α} (C : M.ModularCut) : Prop := C.Fs.Nonempty

@[simp] theorem ModularCut.mem_Fs_iff {C : M.ModularCut} : I ∈ C.Fs ↔ I ∈ C := Iff.rfl

theorem ModularCut.superset {F F' : Set α} (C : M.ModularCut) (hF : F ∈ C) (hFF' : F ⊆ F') (hF' : M.IsFlat F') :
    F' ∈ C :=
  C.up_closed hF hFF' hF'

theorem ModularCut.isFlat {F : Set α} (C : M.ModularCut) (hF : F ∈ C) : M.IsFlat F :=
    C.forall_isFlat hF

theorem ModularCut.sInter (C : M.ModularCut) (hXs : Xs ⊆ C)
    (hXsmod : M.IsModularFamily (fun X : Xs ↦ X)) (hne : Xs.Nonempty) : ⋂₀ Xs ∈ C :=
  C.modular _ hXs hne hXsmod

theorem ModularCut.inter {F F' : Set α} (C : M.ModularCut) (hF : F ∈ C) (hF' : F' ∈ C)
    (hFF' : M.IsModularPair F F') : F ∩ F' ∈ C := by
  rw [← sInter_pair]
  apply C.sInter (pair_subset hF hF') _ (by simp)
  let ⟨B, hB⟩ := hFF'
  refine' ⟨B, hB.1, fun i ↦ _⟩
  dsimp
  obtain (eq | ne) := mem_insert_iff.2 (Subtype.mem i)
  · rw [eq]
    exact hB.2 true
  rw [mem_singleton_iff.1 ne]
  exact hB.2 false

lemma ModularCut.insert_closure {a b : α} {X : Set α} (C : M.ModularCut) (hI : M.Indep (insert a (insert b X)))
    (ha : M.closure (insert a X) ∈ C) (hb : M.closure (insert b X) ∈ C) (hne : a ≠ b) : M.closure X ∈ C := by
  rw [← (@inter_insert_eq _ X _ _ hne), Indep.closure_inter_eq_inter_closure]
  · apply C.inter ha hb (isModularPair_iff.2 ⟨(insert a (insert b X)), hI, _⟩)
    rw [hI.closure_inter_eq_self_of_subset (subset_insert _ _), hI.closure_inter_eq_self_of_subset]
    · refine' ⟨Indep.isBasis_closure (hI.subset _), Indep.isBasis_closure (hI.subset (subset_insert _ _))⟩
      rw [insert_comm]
      exact subset_insert _ _
    rw [insert_comm]
    exact subset_insert _ _
  rwa [union_insert_eq, insert_comm]

theorem IsBasis.exchange_isBase_of_indep {M : Matroid α} {f e : α} {X : Set α} (hB : M.IsBasis B X) (hf : f ∈ X \ B)
    (hI : M.Indep (insert f (B \ {e}))) : M.IsBasis (insert f (B \ {e})) X := by
  have X_sub := hB.subset_ground
  rw [← base_restrict_iff] at hB ⊢
  · apply hB.exchange_isBase_of_indep hf.2 (hI.indep_restrict_of_subset (insert_subset hf.1
    (diff_subset.trans hB.subset_ground)))



lemma IsModularBase.subset {M : Matroid α} {X Y : Set (Set α)} {B : Set α}
    (hmod : M.IsModularBase B (fun x : X ↦ x)) (hsub : Y ⊆ X) : M.IsModularBase B (fun y : Y ↦ y) :=
  ⟨hmod.1, fun i ↦ hmod.2 ⟨i.1, hsub i.2⟩⟩


lemma IsModularFamily.subset {M : Matroid α} {X Y : Set (Set α)}
    (hmod : M.IsModularFamily (fun x : X ↦ x)) (hsub : Y ⊆ X) : M.IsModularFamily (fun y : Y ↦ y) := by
  obtain ⟨B, hB⟩ := hmod
  refine' ⟨B, hB.subset hsub⟩


lemma modular_finite_intersection {M : Matroid α} {X : Set (Set α)} {Fs : Set (Set α)}
    (forall_isFlat : ∀ {F}, F ∈ Fs → M.IsFlat F)
    (pair_modular : ∀ {F F'}, F ∈ Fs → F' ∈ Fs → M.IsModularPair F F' → F ∩ F' ∈ Fs)
    (hfin : X.Finite) (hsub : X ⊆ Fs) (hmod : M.IsModularFamily (fun x : X ↦ x)) (hnone : X.Nonempty) :
    sInter X ∈ Fs := by
  obtain (⟨x, rfl⟩ | X_nt) := hnone.exists_eq_singleton_or_nontrivial
  · rwa [sInter_singleton, ← singleton_subset_iff]
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
  apply modular_finite_intersection forall_isFlat pair_modular (hfin.subset diff_subset) (diff_subset.trans
   hsub) (IsModularFamily.subset ⟨B, B_mod⟩ diff_subset) ⟨y, ⟨(pair_subset_iff.1 xy_sub).2, _⟩⟩
  exact xy_ne.symm
termination_by _ => X.encard

/-- In a finite matroid, the 'pair property' is enough to construct a modular cut .
  The @[simps] will autogenerate simp lemmas. -/
@[simps] def ModularCut.ofForallPair {M : Matroid α} [M.Finite] {Fs : Set (Set α)}
    (forall_isFlat : ∀ {F}, F ∈ Fs → M.IsFlat F)
    (up_closed : ∀ {F F'}, F ∈ Fs → F ⊆ F' → M.IsFlat F' → F' ∈ Fs)
    (pair_modular : ∀ {F F'}, F ∈ Fs → F' ∈ Fs → M.IsModularPair F F' → F ∩ F' ∈ Fs) :
    M.ModularCut where
  Fs := Fs
  forall_isFlat := forall_isFlat
  up_closed := up_closed
  -- Use the stuff in `modular_cut_iff_modular_cut'_finite` to prove this.
  modular := by
    intro Xs hsub hnone hXs
    have hfin : Xs.Finite
    · have isFlat_fin : {F | M.IsFlat F}.Finite
      · apply Finite.subset M.ground_finite.finite_subsets (fun F F_IsFlat ↦ F_IsFlat.subset_ground)
      apply Finite.subset (Finite.subset (flat_fin) (fun F F_C ↦ forall_isFlat F_C)) hsub
    exact modular_finite_intersection forall_isFlat pair_modular hfin hsub hXs hnone

theorem ModularCut.remove {M : Matroid α} (C : M.ModularCut) {B Y : Set α}
    (hB₁ : M.Indep B) (hB₂ : Y ⊆ B) (h_remove : ∀ b ∈ B \ Y, M.closure (B \ {b}) ∈ C) (h_B : M.closure B ∈ C)
    : M.closure Y ∈ C := by
  set Js := {M.closure (B \ {b}) | b ∈ B \ Y}
  set Js₁ := {(B \ {b}) | b ∈ B \ Y}
  obtain (rfl | h_ne) := eq_or_ne Y B
  · assumption
  have Js₁_none : Js₁.Nonempty
  · obtain ⟨b, hb⟩ := exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨hB₂, h_ne⟩)
    refine' ⟨B \ {b}, ⟨b, ⟨hb.1, hb.2⟩, rfl⟩⟩
  have Js₁_sInter_sub_B : ⋂₀ Js₁ ⊆ B
  · intro j j_mem
    rw [mem_sInter] at j_mem
    obtain ⟨t, ht⟩ := Js₁_none
    apply ((_ : t ⊆ B) (j_mem t ht))
    obtain ⟨b, _, rfl⟩ := ht
    exact diff_subset _ _
  have Js_biInter_eq : ⋂ J ∈ Js, J = ⋂ J₁ ∈ Js₁, M.closure J₁ := (by simp)
  have Js_inter_eq : ⋂₀ Js = M.closure Y
  · rw [sInter_eq_biInter, Js_biInter_eq, ← hB₁.closure_sInter_eq_biInter_closure_of_forall_subset Js₁_none]
    · congr!
      ext x
      refine' ⟨fun x_mem ↦ _, fun x_mem I I_mem ↦ _⟩
      · by_contra x_notin_Y
        have xBY : x ∈ B \ Y := ⟨Js₁_sInter_sub_B x_mem, x_notin_Y⟩
        rw [mem_sInter] at x_mem
        exact absurd rfl (x_mem (B \ {x}) ⟨x, xBY, rfl⟩).2
      obtain ⟨b, hb, rfl⟩ := I_mem
      exact ⟨hB₂ x_mem, ne_of_mem_of_notMem x_mem hb.2⟩
    rintro J ⟨b, _, rfl⟩
    exact diff_subset _ _
  rw [← Js_inter_eq]
  apply C.modular
  · rintro J ⟨b, hb, rfl⟩
    exact h_remove b hb
  · obtain ⟨A, a, ha⟩ := Js₁_none
    refine' ⟨M.closure (B \ {a}), _⟩
    refine' ⟨a, ha.1, rfl⟩
  have:= hB₁
  obtain ⟨B', B'_isBase, B_sub_B'⟩ := this
  refine' ⟨B', B'_isBase, fun x ↦ _⟩
  obtain ⟨y, ⟨y', y'_mem, rfl⟩⟩ := x
  dsimp
  rw [B'_isBase.indep.closure_inter_eq_self_of_subset (diff_subset.trans B_sub_B')]
  apply (hB₁.subset (diff_subset _ {y'})).isBasis_closure

/-- A modular cut will determine an extension. -/
@[simps] def ModularCut.extensionIndepMatroid (C : M.ModularCut) (e : α) :
    IndepMatroid α where
  E := insert e M.E
  -- this definition of independence is equivalent to yours, but doesn't use `ite` and
  -- so doesn't need decidability. It also means that the hypothesis that `e ∉ M.E`
  -- isn't needed as part of the definition; you just get the original matroid back
  -- as the extension if `e ∈ M.E`. (Theorems about the extension can have `e ∉ M.E`
  -- as part of the hypothesis if needed).
  Indep I := M.Indep I ∨ (e ∈ I \ M.E ∧ M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ C)
  indep_empty := Or.inl M.empty_indep
  indep_subset I J := by
    -- tricks like the line below are good for deconstructing `Or`s without `by_cases, if_pos`, etc.
    rintro (hJ | ⟨⟨_, heE⟩, hJ, hJC⟩) hIJ
    · exact Or.inl <| hJ.subset hIJ
    by_cases heI : e ∈ I
    · refine Or.inr ⟨⟨heI, heE⟩, hJ.subset (diff_subset_diff_left hIJ), fun hIC ↦ hJC ?_⟩
      exact C.superset hIC (M.closure_subset_closure (diff_subset_diff_left hIJ)) (M.closure_isFlat _)
    refine Or.inl (hJ.subset <| subset_diff_singleton hIJ heI)
  indep_aug := by
    -- hard work here
    rintro I J I_ind I_nmax ⟨J_ind, J_max⟩
    have J_isBase_of_ind : M.Indep J → M.IsBase J
    · intro J_ind
      rw [isBase_iff_maximal_indep]
      refine' ⟨J_ind, fun X X_ind X_sub ↦ _⟩
      apply subset_antisymm X_sub (J_max _ X_sub)
      exact Or.inl X_ind
    rw [mem_maximals_iff] at I_nmax
    push_neg at I_nmax
    obtain ⟨Y, Y_ind, I_sub_Y, I_ne_Y⟩ := I_nmax I_ind
    dsimp at Y_ind J_ind
    obtain (I_ind | ⟨e_in_I, I_ind, I_closure_notMem⟩) := I_ind
    · --rw [if_pos (I_sub_Y e_in_I)] at Y_ind
      obtain (J_ind | ⟨e_in_J, J_ind, J_closure_notMem⟩) := J_ind
      ·  --e in neither case
        have I_not_isBase : ¬ M.IsBase I
        · intro h_f
          obtain (Y_ind | ⟨e_in_Y, Y_ind, Y_closure_notMem⟩) := Y_ind
          · apply (h_f.dep_of_ssubset (I_ne_Y.ssubset_of_subset I_sub_Y)
            Y_ind.subset_ground).not_indep Y_ind
          have e_in_J := notMem_subset J_ind.subset_ground e_in_Y.2
          rw [Spanning.closure_eq _] at Y_closure_notMem
          · apply (ne_insert_of_notMem J e_in_J (subset_antisymm (subset_insert e J) (J_max _ (subset_insert e J))))
            refine' Or.inr ⟨⟨mem_insert _ _, e_in_Y.2⟩, by simp [J_ind, e_in_J], _⟩
            rwa [insert_diff_self_of_notMem e_in_J, (J_isBase_of_ind J_ind).closure_eq]
          rw [spanning_iff_superset_isBase (Y_ind.subset_ground)]
          refine' ⟨I, h_f, subset_diff_singleton I_sub_Y (notMem_subset I_ind.subset_ground e_in_Y.2)⟩
        obtain ⟨x, x_mem, x_ind⟩ := I_ind.exists_insert_of_not_isBase I_not_isBase
         (J_isBase_of_ind J_ind)
        refine' ⟨x, x_mem, Or.inl x_ind⟩
      -- e in J only case
      have e_notin_I:= notMem_subset I_ind.subset_ground e_in_J.2
      by_cases closure_I_mem : M.closure I ∈ C
      · by_contra! h_f
        have J_diff_sub_closure_I : J \ {e} ⊆ M.closure I
        · rintro j ⟨j_J, (j_ne : j ≠ e)⟩
          rw [I_ind.mem_closure_iff, or_comm, or_iff_not_imp_left, dep_iff]
          intro j_nI
          refine' ⟨(not_or.1 (h_f j ⟨j_J, j_nI⟩)).1, insert_subset (J_ind.subset_ground ⟨j_J, j_ne⟩) I_ind.subset_ground⟩
        have I_J_exch : ∃ i ∈ I \ (J \ {e}), M.Indep (insert i (J \ {e}))
        · apply J_ind.exists_insert_of_not_isBasis (subset_union_left _ I)
          · intro h_f
            apply J_closure_notMem (C.superset closure_I_mem _ (M.closure_isFlat _))
            rw [h_f.closure_eq_closure]
            apply M.closure_subset_closure subset_union_right
          rw [isBasis_iff_indep_subset_closure]
          refine' ⟨I_ind, subset_union_right, fun x ↦ _⟩
          rintro (x_J | x_I)
          · exact J_diff_sub_closure_I x_J
          · exact M.mem_closure_of_mem x_I
        obtain ⟨i, i_mem, i_ind⟩ := I_J_exch
        obtain (Y_ind | ⟨_, _, Y_closure_notMem⟩) := Y_ind
        · obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
          obtain (mem_c | y_in_I) := I_ind.insert_indep_iff.1 (Y_ind.subset
           (insert_subset hy.1 I_sub_Y))
          · have y_insert_indep : M.Indep (insert y (insert i (J \ {e})))
            · rw [i_ind.insert_indep_iff_of_notMem, mem_diff]
              · refine' ⟨Y_ind.subset_ground hy.1, fun y_closure ↦ _⟩
                apply mem_c.2 (closure_subset_closure_of_subset_closure (insert_subset (M.mem_closure_of_mem i_mem.1
                 I_ind.subset_ground) J_diff_sub_closure_I) y_closure)
              rintro (rfl | y_in_J)
              · exact hy.2 i_mem.1
              exact mem_c.2 (J_diff_sub_closure_I y_in_J)
            apply J_closure_notMem (C.insert_closure y_insert_indep _ _ _)
            · by_contra insert_notMem
              apply (J \ {e}).ne_insert_of_notMem (J \ {e}) _ (subset_antisymm (subset_insert y _) _)
              · exact fun y_mem ↦ mem_c.2 (J_diff_sub_closure_I y_mem)
              rw [insert_diff_singleton_comm (ne_of_mem_of_notMem mem_c.1 e_in_J.2)]
              apply diff_subset_diff_left (J_max (Or.inr _) (subset_insert _ _))
              rw [← insert_diff_singleton_comm (ne_of_mem_of_notMem mem_c.1 e_in_J.2)]
              refine' ⟨⟨mem_insert_of_mem _ e_in_J.1, e_in_J.2⟩, y_insert_indep.subset _, insert_notMem⟩
              rw [insert_comm]
              exact subset_insert _ _
            · by_contra insert_notMem
              apply (J \ {e}).ne_insert_of_notMem (J \ {e}) i_mem.2 (subset_antisymm (subset_insert i _) _)
              rw [insert_diff_singleton_comm (ne_of_mem_of_notMem (I_ind.subset_ground i_mem.1) e_in_J.2)]
              · apply diff_subset_diff_left (J_max (Or.inr _) (subset_insert _ _))
                rw [← insert_diff_singleton_comm (ne_of_mem_of_notMem (I_ind.subset_ground i_mem.1) e_in_J.2)]
                refine' ⟨⟨mem_insert_of_mem _ e_in_J.1, e_in_J.2⟩, y_insert_indep.subset (subset_insert _ _), insert_notMem⟩
            exact fun (rfl) ↦ hy.2 i_mem.1
          exact hy.2 y_in_I
        apply Y_closure_notMem (C.superset closure_I_mem (M.closure_subset_closure (subset_diff_singleton I_sub_Y e_notin_I)) (M.closure_isFlat _))
      refine' ⟨e, ⟨e_in_J.1, e_notin_I⟩, Or.inr ⟨⟨mem_insert _ _, e_in_J.2⟩, _, _⟩⟩
      · rwa [insert_diff_self_of_notMem e_notin_I]
      rwa [insert_diff_self_of_notMem e_notin_I]
    obtain (J_ind | ⟨e_in_J, J_ind, J_closure_notMem⟩) := J_ind
    --case involving finding 2 to add from J to I where e is in I only
    · obtain (Y_ind | ⟨e_in_Y, Y_ind, Y_closure_notMem⟩) := Y_ind
      · exact absurd (Y_ind.subset_ground (I_sub_Y e_in_I.1)) e_in_I.2
      have I_nb : ¬ M.IsBase (I \ {e})
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
      obtain ⟨j₂, hj₂⟩ := I_ind.exists_insert_of_not_isBase I_nb (J_isBase_of_ind J_ind)
      rw [diff_diff_right, Disjoint.inter_eq (disjoint_singleton_right.2 (notMem_subset J_ind.subset_ground e_in_Y.2)),
       union_empty] at hj₂
      by_cases j₂I_b : M.IsBase (insert j₂ (I \ {e}))
      · refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [← insert_diff_singleton_comm (ne_of_mem_of_notMem (J_ind.subset_ground hj₂.1.1)
         e_in_Y.2), and_iff_right hj₂.2]
        obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
        obtain (rfl | ne) := eq_or_ne j₂ y
        · exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, fun closure_mem ↦ Y_closure_notMem
           (C.superset closure_mem (M.closure_subset_closure (insert_subset ⟨hy.1,
           (ne_of_mem_of_notMem e_in_I.1 hj₂.1.2).symm⟩ (diff_subset_diff_left I_sub_Y)))
           (M.closure_isFlat _))⟩
        have y_notin : y ∉ insert j₂ (I \ {e})
        · rw [mem_insert_iff, not_or, mem_diff, not_and_or]
          exact ⟨ne.symm, Or.inl hy.2⟩
        have base_insert:= @Matroid.IsBase.exchange_isBase_of_indep _ _ _ _ j₂ j₂I_b y_notin
        rw [insert_diff_self_of_notMem (notMem_subset diff_subset hj₂.1.2)] at base_insert
        rw [j₂I_b.closure_eq]
        rw [Spanning.closure_eq _] at Y_closure_notMem
        · refine Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, Y_closure_notMem⟩
        have insert_y_subset_Y : insert y (I \ {e}) ⊆ Y \ {e}
        · rw [insert_diff_singleton_comm (ne_of_mem_of_notMem e_in_I (notMem_subset diff_subset hy.2)).symm]
          exact diff_subset_diff_left (insert_subset hy.1 I_sub_Y)
        apply IsBase.superset_spanning (base_insert (Y_ind.subset insert_y_subset_Y))
         insert_y_subset_Y Y_ind.subset_ground
      obtain ⟨j₁, j₁_mem, j₁_ind⟩:=hj₂.2.exists_insert_of_not_isBase j₂I_b
       (J_isBase_of_ind J_ind)
      have hne : j₁ ≠ j₂:= fun (rfl) ↦ j₁_mem.2 (mem_insert _ _)
      by_cases j₁_closure_mem_c : M.closure (insert j₁ (I \ {e})) ∈ C
      · by_cases j₂_closure_mem_c : M.closure (insert j₂ (I \ {e})) ∈ C
        · exact absurd (C.insert_closure j₁_ind j₁_closure_mem_c j₂_closure_mem_c hne) I_closure_notMem
        refine' ⟨j₂, hj₂.1, _⟩
        dsimp
        rw [← insert_diff_singleton_comm
         (ne_of_mem_of_notMem (J_ind.subset_ground hj₂.1.1) e_in_I.2) _]
        exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, j₁_ind.subset (subset_insert _ _),
         j₂_closure_mem_c⟩
      refine' ⟨j₁, ⟨j₁_mem.1, fun hf ↦ j₁_mem.2 (mem_insert_of_mem _ ⟨hf, ne_of_mem_of_notMem
       j₁_mem.1 (notMem_subset J_ind.subset_ground e_in_I.2)⟩)⟩, _⟩
      dsimp
      rw [ ← insert_diff_singleton_comm (ne_of_mem_of_notMem j₁_mem.1 (notMem_subset J_ind.subset_ground e_in_I.2)) _]
      exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, j₁_ind.subset (insert_subset_insert (subset_insert _ _)), j₁_closure_mem_c⟩
    --hard case, e in both
    by_contra! h_f
    obtain (Y_ind | ⟨_, Y_ind, Y_closure_notMem⟩) := Y_ind
    · exact e_in_I.2 (Y_ind.subset_ground (I_sub_Y e_in_I.1))
    have J_insert_mem_C : ∀ x ∉ J, M.Indep (insert x (J \ {e})) → M.closure (insert x (J \ {e})) ∈ C
    · intro x x_notin_J x_ind
      by_contra notMem_C
      apply (ne_insert_of_notMem _ x_notin_J) (subset_antisymm (subset_insert _ _) (J_max _
        (subset_insert _ _)))
      dsimp
      rw [← insert_diff_singleton_comm (ne_of_mem_of_notMem
        e_in_J.1 x_notin_J).symm]
      exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_J.1, e_in_J.2⟩, x_ind, notMem_C⟩
    obtain ⟨y, hy⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.2 ⟨I_sub_Y, I_ne_Y⟩)
    have y_ind : M.Indep ((insert y I) \ {e}) ∧ M.closure ((insert y I) \ {e}) ∉ C
    · refine' ⟨Y_ind.subset (diff_subset_diff_left (insert_subset hy.1 I_sub_Y)),
        fun closure_mem_C ↦ _⟩
      exact Y_closure_notMem (C.superset closure_mem_C (M.closure_subset_closure (diff_subset_diff_left (insert_subset
        hy.1 I_sub_Y))) (M.closure_isFlat _))
    have y_notin_J : y ∉ J
    · intro y_in_J
      apply h_f y ⟨y_in_J, hy.2⟩ _
      exact Or.inr ⟨⟨mem_insert_of_mem y e_in_I.1, e_in_I.2⟩, y_ind⟩
    have y_ground := (Y_ind.subset_ground (mem_diff_of_mem hy.1 (ne_of_mem_of_notMem e_in_J
      (notMem_subset diff_subset y_notin_J)).symm))
    have x := I_ind.subset_isBasis_of_subset (diff_subset_diff_left (subset_union_left I J)) ?_
    · obtain ⟨I', I'_isBasis, I_sub_I'⟩ := x
      have : (I \ {e} ⊂ I')
      · have hne:= (ne_of_mem_of_notMem e_in_J (notMem_subset (diff_subset _ M.E) y_notin_J)).symm
        apply Ne.ssubset_of_subset _ I_sub_I'
        rintro rfl
        apply insert_ne_self.2 y_notin_J (subset_antisymm (J_max _ (subset_insert _ _))
          (subset_insert _ _))
        dsimp
        rw [← insert_diff_singleton_comm
          hne, ← J_ind.notMem_closure_iff_of_notMem _]
        refine' Or.inr ⟨⟨(mem_insert_of_mem _ e_in_J.1), e_in_J.2⟩, notMem_subset (M.closure_subset_closure (diff_subset_diff_left
          (subset_union_right I J))) _, _⟩
        · rw [← I'_isBasis.closure_eq_closure, I_ind.notMem_closure_iff_of_notMem (notMem_subset
          diff_subset hy.2),
          insert_diff_singleton_comm hne]
          exact y_ind.1
        rw [insert_diff_singleton_comm hne]
        intro closure_mem_C
        apply y_ind.2 (C.superset closure_mem_C _ (M.closure_isFlat _))
        rw [← insert_diff_singleton_comm hne I,
          ← closure_insert_closure_eq_closure_insert, I'_isBasis.closure_eq_closure, closure_insert_closure_eq_closure_insert,
          ← insert_diff_singleton_comm hne]
        · apply M.closure_subset_closure (insert_subset_insert (diff_subset_diff_left
          subset_union_right))
        exact notMem_subset diff_subset y_notin_J
      obtain ⟨a, a_notMem, a_insert_sub⟩ := ssubset_iff_insert.1 this
      have a_mem_JI : a ∈ J \ I
      · obtain ⟨(aI | aJ), a_ne_e⟩:= I'_isBasis.subset (a_insert_sub (mem_insert a _))
        apply absurd (⟨aI, a_ne_e⟩ : (a ∈ I \ {e})) a_notMem
        apply (mem_diff _).2 ⟨aJ, _⟩
        intro aI
        apply a_notMem ⟨aI, a_ne_e⟩
      obtain (ssubset | rfl) := ssubset_or_eq_of_subset a_insert_sub
      · obtain ⟨b, b_notMem, b_insert_sub⟩ := ssubset_iff_insert.1 ssubset
        apply I_closure_notMem (C.insert_closure (I'_isBasis.indep.subset b_insert_sub) _ _ (ne_of_mem_of_notMem (mem_insert _ _) b_notMem).symm)
        · rw [insert_comm] at b_insert_sub
          have:= h_f b ?_
          · rw [not_or, not_and, not_and, not_not,
              ← insert_diff_singleton_comm (ne_of_mem_of_notMem ((I'_isBasis.indep.subset
              b_insert_sub).subset_ground (mem_insert_of_mem _ (mem_insert _ _))) e_in_I.2)] at this
            exact this.2 ⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩ (I'_isBasis.indep.subset ((subset_insert _ _).trans b_insert_sub))
          rw [insert_comm] at b_insert_sub
          obtain ⟨(bI | bJ), b_ne_e⟩:= I'_isBasis.subset (b_insert_sub (mem_insert b _))
          · apply absurd (⟨bI, b_ne_e⟩ : (b ∈ I \ {e})) _
            apply notMem_subset (subset_insert _ _) b_notMem
          apply (mem_diff _).2 ⟨bJ, _⟩
          intro bI
          apply b_notMem (mem_insert_of_mem _ ⟨bI, b_ne_e⟩)
        have:= h_f a a_mem_JI
        rw [not_or, not_and, not_and, not_not,
          ← insert_diff_singleton_comm] at this
        · exact this.2 ⟨(mem_insert_of_mem _ e_in_I.1), e_in_I.2⟩ (I'_isBasis.indep.subset a_insert_sub)
        exact ne_of_mem_of_notMem ((I'_isBasis.indep.subset a_insert_sub).subset_ground
          (mem_insert _ _)) e_in_I.2
      have J_not_isBasis : ¬ M.IsBasis (J \ {e}) ((I ∪ J) \ {e})
      · intro J_isBasis
        apply h_f a a_mem_JI
        rw [← insert_diff_singleton_comm, I'_isBasis.closure_eq_closure, ← J_isBasis.closure_eq_closure]
        exact Or.inr ⟨⟨mem_insert_of_mem _ e_in_I.1, e_in_I.2⟩, I'_isBasis.indep, J_closure_notMem⟩
        exact (ne_of_mem_of_notMem e_in_I.1 a_mem_JI.2).symm
      obtain ⟨i, hi⟩ := J_ind.exists_insert_of_not_isBasis (diff_subset_diff_left
       subset_union_right) J_not_isBasis I'_isBasis
      have I'_isBase : M.IsBase (insert a (I \ {e}))
      · by_contra I'_not_isBase
        obtain ⟨B, hB⟩ := M.exists_isBase
        obtain ⟨b, hb⟩ := I'_isBasis.indep.exists_insert_of_not_isBase I'_not_isBase hB
        have b_notin_union : b ∉ I ∪ J
        · intro b_mem_union
          have : b ∈ (I ∪ J) \ {e}
          · rwa [mem_diff_singleton, and_iff_left (ne_of_mem_of_notMem
            (hB.subset_ground hb.1.1) e_in_I.2)]
          apply ((I'_isBasis.indep.insert_indep_iff_of_notMem hb.1.2).1 hb.2).2
          rw [I'_isBasis.closure_eq_closure]
          apply M.mem_closure_of_mem this I'_isBasis.subset_ground
        have bi_J_indep : M.Indep (insert b (insert i (J \ {e})))
        · rw [hi.2.insert_indep_iff, mem_diff _, and_iff_right (hB.subset_ground hb.1.1)]
          rw [I'_isBasis.indep.insert_indep_iff_of_notMem hb.1.2, I'_isBasis.closure_eq_closure] at hb
          apply Or.inl (notMem_subset (M.closure_subset_closure _) hb.2.2)
          rw [insert_diff_singleton_comm (ne_of_mem_of_notMem (hi.2.subset_ground
            (mem_insert _ _)) e_in_I.2)]
          apply diff_subset_diff_left (insert_subset _ subset_union_right)
          obtain (rfl | i_Jd) := hi.1.1
          · apply (Or.inr a_mem_JI.1)
          apply (Or.inl i_Jd.1)
        apply J_closure_notMem (C.insert_closure bi_J_indep _ _ (ne_of_mem_of_notMem hi.1.1 hb.1.2).symm)
        · apply J_insert_mem_C b (notMem_subset subset_union_right b_notin_union) _
          rw [insert_comm] at bi_J_indep
          exact bi_J_indep.subset (subset_insert _ _)
        apply J_insert_mem_C i _ hi.2
        intro i_J
        apply hi.1.2 ⟨i_J, ne_of_mem_of_notMem (hi.2.subset_ground (mem_insert _ _)) e_in_I.2⟩
      have yI_isBase : M.IsBase (insert y (I \ {e}))
      · have base_insert:= @Matroid.IsBase.exchange_isBase_of_indep _ _ _ y a I'_isBase
        rw [insert_diff_self_of_notMem a_notMem] at base_insert
        apply base_insert
        · rintro (rfl | y_mem)
          · exact y_notin_J a_mem_JI.1
          exact hy.2 y_mem.1
        rw [insert_diff_singleton_comm (ne_of_mem_of_notMem y_ground e_in_I.2)]
        exact y_ind.1
      apply h_f a a_mem_JI
      rw [← insert_diff_singleton_comm
        (ne_of_mem_of_notMem e_in_I (notMem_subset diff_subset a_mem_JI.2)).symm,
        I'_isBase.closure_eq, ← yI_isBase.closure_eq, insert_diff_singleton_comm (ne_of_mem_of_notMem y_ground e_in_I.2)]
      exact Or.inr ⟨⟨(mem_insert_of_mem _ e_in_I.1), (notMem_subset (M.closure_subset_ground _) e_in_I.2)⟩, I'_isBase.indep, y_ind.2⟩
    rintro x ⟨(x_I | x_J), (hne : x ≠ e)⟩
    · exact I_ind.subset_ground ⟨x_I, hne⟩
    exact J_ind.subset_ground ⟨x_J, hne⟩

  indep_maximal := by
    -- more hard work here
    intro X X_sub Y Y_ind Y_sub_X
    obtain (Y_ind | ⟨e_in_Y, Y_ind, Y_closure_notMem⟩) := Y_ind
    · by_cases e_in_Y : e ∈ Y
      · obtain ⟨B, B_Basis, Y_sub_B⟩ := Y_ind.subset_isBasis_of_subset Y_sub_X (X_sub.trans
          (insert_subset (Y_ind.subset_ground e_in_Y) subset_rfl))
        refine' ⟨B, _⟩
        rw [mem_maximals_iff]
        refine' ⟨⟨Or.inl B_Basis.indep, Y_sub_B, B_Basis.subset⟩, fun I I_ind I_sub ↦ _⟩
        obtain ⟨(I_ind | ⟨e_in_I, _, _⟩), Y_sub_I, I_sub_X⟩ := I_ind
        · obtain (rfl | ssub) := eq_or_ssubset_of_subset I_sub
          · rfl
          exact absurd I_ind (B_Basis.dep_of_ssubset ssub I_sub_X).not_indep
        apply absurd (Y_ind.subset_ground e_in_Y) e_in_I.2
      by_cases e_in_X : e ∈ X
      · obtain (X_ground | ⟨e_mem, Xdiff_sub⟩) := subset_insert_iff.1 X_sub
        · obtain ⟨B, B_Basis, Y_sub_B⟩ := Y_ind.subset_isBasis_of_subset Y_sub_X X_ground
          refine' ⟨B, mem_maximals_iff.2 _⟩
          refine' ⟨⟨Or.inl B_Basis.indep, Y_sub_B, B_Basis.subset⟩, fun I I_ind I_sub ↦ _⟩
          obtain ⟨(I_ind | ⟨e_in_I, _, _⟩), Y_sub_I, I_sub_X⟩ := I_ind
          · obtain (rfl | ssub) := eq_or_ssubset_of_subset I_sub
            · rfl
            exact absurd I_ind (B_Basis.dep_of_ssubset ssub I_sub_X).not_indep
          apply absurd (X_ground e_in_X) e_in_I.2
        obtain ⟨B, B_Basis, Y_sub_B⟩ := Y_ind.subset_isBasis_of_subset (subset_diff_singleton Y_sub_X e_in_Y) Xdiff_sub
        by_cases eB_ind : M.Indep (insert e B)
        · refine' ⟨insert e B, mem_maximals_iff.2 ⟨⟨Or.inl eB_ind, Y_sub_B.trans (subset_insert _ _)
            , insert_subset e_in_X (B_Basis.subset.trans diff_subset)⟩, fun I I_ind I_sub ↦ _⟩⟩
          obtain ⟨(I_ind | ⟨e_in_I, _, _⟩), Y_sub_I, I_sub_X⟩ := I_ind
          · obtain (rfl | ssub) := eq_or_ssubset_of_subset I_sub
            · rfl
            obtain ⟨i, hi⟩ := exists_of_ssubset ssub
            apply absurd (I_ind.subset (insert_subset hi.1 ((subset_insert _ _).trans I_sub))) (Dep.not_indep _)
            refine' B_Basis.dep_of_ssubset (ssubset_insert (notMem_subset (subset_insert _ _) hi.2))
              (insert_subset ⟨I_sub_X hi.1, fun (rfl) ↦ hi.2 (mem_insert _ _)⟩ B_Basis.subset)
          apply absurd (eB_ind.subset_ground (mem_insert _ _)) e_in_I.2
        by_cases closure_mem_C : M.closure B ∈ C ∨ e ∈ M.E
        · refine' ⟨B, mem_maximals_iff.2 ⟨⟨Or.inl B_Basis.indep, Y_sub_B, (B_Basis.subset.trans diff_subset)⟩, fun I I_ind I_sub ↦ _⟩⟩
          obtain ⟨(I_ind | ⟨e_in_I, _, closure_notMem⟩), Y_sub_I, I_sub_X⟩ := I_ind
          · obtain (rfl | ssub) := eq_or_ssubset_of_subset I_sub
            · rfl
            have I_sub_Xd := subset_diff_singleton I_sub_X (fun (e_mem : e ∈ I) ↦ (eB_ind (I_ind.subset (insert_subset e_mem I_sub))))
            apply absurd I_ind (B_Basis.dep_of_ssubset ssub I_sub_Xd).not_indep
          obtain (closure_mem_C | e_mem) := closure_mem_C
          · apply absurd (C.superset closure_mem_C (M.closure_subset_closure (subset_diff_singleton I_sub
             (notMem_subset B_Basis.left_subset_ground e_in_I.2))) (M.closure_isFlat _)) closure_notMem
          exact absurd e_mem e_in_I.2
        push_neg at closure_mem_C
        have e_nB := notMem_subset B_Basis.left_subset_ground closure_mem_C.2
        refine' ⟨insert e B, mem_maximals_iff.2 ⟨⟨Or.inr ⟨⟨mem_insert _ _, closure_mem_C.2⟩, by simp
         [B_Basis.indep, e_nB], by simp [closure_mem_C, e_nB]⟩, Y_sub_B.trans (subset_insert _ _),
         insert_subset e_in_X (B_Basis.subset.trans diff_subset)⟩, fun I I_ind sub_I ↦ _⟩⟩
        obtain ⟨(I_ind | ⟨e_in_I, I_ind, closure_notMem⟩), Y_sub_I, I_sub_X⟩ := I_ind
        · exact absurd (I_ind.subset_ground (sub_I (mem_insert _ _))) closure_mem_C.2
        obtain (rfl | ssub) := eq_or_ssubset_of_subset sub_I
        · rfl
        obtain ⟨i, hi⟩ := exists_of_ssubset ssub
        have e_niB: e ∉ insert i B
        · rintro (rfl | e_B)
          · exact hi.2 (mem_insert _ _)
          exact e_nB e_B
        have iB_sub_Xd : insert i B ⊆ X \ {e}:= subset_diff_singleton (insert_subset (I_sub_X hi.1) ((B_Basis.subset).trans diff_subset)) e_niB
        apply absurd (I_ind.subset _) (B_Basis.dep_of_ssubset (ssubset_insert (notMem_subset (subset_insert _ _) hi.2)) iB_sub_Xd).not_indep
        exact subset_diff_singleton (insert_subset hi.1 ((subset_insert _ _).trans sub_I)) e_niB
      rw [← diff_singleton_subset_iff, diff_singleton_eq_self e_in_X] at X_sub
      obtain ⟨B, B_Basis, Y_sub_B⟩ := Y_ind.subset_isBasis_of_subset Y_sub_X
      refine' ⟨B, mem_maximals_iff.2 ⟨⟨Or.inl B_Basis.indep, Y_sub_B, B_Basis.subset⟩, fun I I_ind sub_I ↦ _⟩⟩
      obtain ⟨(I_ind | ⟨e_in_I, _, _⟩), Y_sub_I, I_sub_X⟩ := I_ind
      · obtain (rfl | ssub) := eq_or_ssubset_of_subset sub_I
        · rfl
        apply absurd I_ind (B_Basis.dep_of_ssubset ssub I_sub_X).not_indep
      apply absurd (I_sub_X e_in_I.1) e_in_X
    rw [← diff_singleton_subset_iff] at X_sub
    obtain ⟨B, B_Basis, Y_sub_B⟩ := Y_ind.subset_isBasis_of_subset (diff_subset_diff_left Y_sub_X) X_sub
    have e_nB : e ∉ B
    · exact notMem_subset B_Basis.left_subset_ground e_in_Y.2
    obtain (closure_B_mem_C | closure_B_mem_C) := em (M.closure B ∉ C)
    · refine' ⟨insert e B, mem_maximals_iff.2 ⟨⟨Or.inr ⟨⟨mem_insert _ _, e_in_Y.2⟩, by simp
       [B_Basis.indep, e_nB], by simp [closure_B_mem_C, e_nB]⟩, diff_singleton_subset_iff.1 Y_sub_B,
       insert_subset (Y_sub_X e_in_Y.1) (B_Basis.subset.trans diff_subset)⟩, fun I I_ind sub_I ↦ _⟩⟩
      obtain ⟨(I_ind | ⟨e_in_I, I_ind, _⟩), _, I_sub_X⟩ := I_ind
      · exact absurd (I_ind.subset_ground (sub_I (mem_insert _ _))) e_in_Y.2
      obtain (rfl | ssub) := eq_or_ssubset_of_subset (subset_diff_singleton ((subset_insert _ _).trans sub_I) e_nB)
      · simp [e_in_I.1]
      apply absurd I_ind (B_Basis.dep_of_ssubset ssub (diff_subset_diff_left I_sub_X)).not_indep
    rw [not_not] at closure_B_mem_C
    obtain (h_remove | h_remove) := em (∀ b ∈ B \ (Y \ {e}), M.closure (B \ {b}) ∈ C)
    · exact absurd (C.remove B_Basis.indep Y_sub_B h_remove closure_B_mem_C) Y_closure_notMem
    push_neg at h_remove
    obtain ⟨b, b_mem, b_closure_mem⟩ := h_remove
    refine' ⟨(insert e (B \ {b})), mem_maximals_iff.2 ⟨⟨Or.inr ⟨⟨mem_insert _ _, e_in_Y.2⟩, by simp
     [e_nB, B_Basis.indep.subset (diff_subset B {b})], by simp [e_nB, b_closure_mem]⟩,
     ⟨diff_singleton_subset_iff.1 (subset_diff_singleton Y_sub_B b_mem.2), insert_subset (Y_sub_X
     e_in_Y.1) ((diff_subset.trans B_Basis.subset).trans diff_subset)⟩⟩,
     fun I I_ind sub_I ↦ _⟩⟩
    obtain ⟨(I_ind | ⟨e_in_I, I_ind, I_closure_notMem⟩), Y_sub_I, I_sub_X⟩ := I_ind
    · exact absurd (I_ind.subset_ground (sub_I (mem_insert _ _))) e_in_Y.2
    obtain (rfl | ssub) := eq_or_ssubset_of_subset sub_I
    · rfl
    obtain ⟨i, hi⟩ := exists_of_ssubset ssub
    exfalso
    apply I_closure_notMem
    have bsub : insert i (B \ {b}) ⊆ I \ {e}
    · apply insert_subset _ _
      · exact ⟨hi.1, fun (rfl) ↦ hi.2 (mem_insert _ _)⟩
      apply subset_diff_singleton ((subset_insert _ _).trans sub_I) (notMem_subset
       (diff_subset.trans (B_Basis.left_subset_ground)) e_in_Y.2)
    have iBb_C : M.closure (insert i (B \ {b})) ∈ C
    · obtain (rfl | i_ne_b) := eq_or_ne i b
      · simp only [b_mem.1, not_true_eq_false, mem_diff, mem_singleton_iff, and_false,
        insert_diff_singleton, insert_eq_of_mem, closure_B_mem_C]
      rwa [@Basis.closure_eq_closure _ M _ (X \ {e}) _, ← B_Basis.closure_eq_closure]
      apply B_Basis.exchange_isBase_of_indep
      rw [mem_diff, mem_diff, mem_singleton_iff]
      · refine' ⟨⟨I_sub_X hi.1, fun (rfl) ↦ hi.2 (mem_insert _ _)⟩, fun i_B ↦ hi.2 (mem_insert_of_mem _ ⟨i_B, i_ne_b⟩)⟩
      refine' I_ind.subset (insert_subset ⟨hi.1, fun (rfl) ↦ hi.2 (mem_insert _ _)⟩ ((subset_insert _ _).trans bsub))
    apply @ModularCut.superset _ M (M.closure (insert i (B \ {b}))) _ C iBb_C _ (M.closure_isFlat _)
    apply M.closure_subset_closure bsub

  subset_ground := by
    rintro I (hI | ⟨-, hI, -⟩)
    · exact hI.subset_ground.trans <| subset_insert _ _
    simpa using diff_subset_iff.1 hI.subset_ground


def ModularCut.extension (C : M.ModularCut) (e : α) := (C.extensionIndepMatroid e).matroid

@[simp] theorem ModularCut.extension_ground (C : M.ModularCut) (e : α) :
    (C.extension e).E = insert e M.E := rfl

@[simp] theorem ModularCut.extension_indep (C : M.ModularCut) (e : α) {I : Set α} :
    (C.extension e).Indep I ↔
      M.Indep I ∨ (e ∈ I \ M.E ∧ M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ C) := by
  simp [extension]

/-- If `e ∈ M.E`, then the extension is just the matroid itself -/
theorem ModularCut.extension_eq_self {e : α} (C : M.ModularCut) (he : e ∈ M.E) :
    C.extension e = M :=
  ext_indep (by simpa) (fun _ _ ↦ by simp [he])

theorem ModularCut.extension_delete (C : M.ModularCut) {e : α} (he : e ∉ M.E) :
    (C.extension e) ＼ e = M :=
  ext_indep (by simpa)
    (fun I hI ↦ by simp [show e ∉ I from fun heI ↦ by simpa using hI heI])

theorem ModularCut.extension_closure_eq_of_mem {e : α} {X : Set α} (C : M.ModularCut) (he : e ∉ M.E) (hX : M.closure X ∈ C) :
    (C.extension e).closure X = insert e (M.closure X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have ex_isBasis : (extension C e).IsBasis' I X
  · rw [isBasis'_iff_isBasis_inter_ground, C.extension_ground, basis_iff, C.extension_indep,
    and_iff_right (Or.inl hI.indep)]
    have sub_inter:= subset_inter_iff.1 hI.isBasis_inter_ground.subset
    refine' ⟨subset_inter_iff.2 ⟨sub_inter.1, sub_inter.2.trans (subset_insert _ _)⟩,
     fun J J_ind I_sub_J J_sub_X ↦ _⟩
    rw [←hI.closure_eq_closure] at hX
    rw [isBasis'_iff_isBasis_inter_ground, basis_iff] at hI
    obtain (M_ind | ⟨e_mem, _, closure_notMem⟩) := (C.extension_indep e).1 J_ind
    · apply hI.2.2 _ M_ind I_sub_J
      exact fun j j_mem ↦ ⟨(J_sub_X j_mem).1, M_ind.subset_ground j_mem⟩
    exact absurd hX (fun I_closure_mem ↦ closure_notMem (C.superset I_closure_mem (M.closure_subset_closure
     (subset_diff_singleton I_sub_J (notMem_subset hI.1.subset_ground e_mem.2))) (M.closure_isFlat _)))
  rw [←hI.closure_eq_closure, ←ex_isBasis.closure_eq_closure, ext_iff]
  refine' fun x ↦ ⟨fun x_mem ↦ _, fun (x_mem) ↦ _⟩
  · obtain (x_dep | x_mem) := ex_isBasis.indep.mem_closure_iff.1 x_mem
    · have x_ground:= x_dep.subset_ground
      obtain (rfl | ne) := eq_or_ne x e
      · exact mem_insert _ _
      rw [←not_indep_iff, (C.extension_indep e), not_or, not_indep_iff _] at x_dep
      · apply Or.inr (hI.indep.mem_closure_iff.2 (Or.inl x_dep.1))
      rw [C.extension_ground e, ←diff_singleton_subset_iff, diff_singleton_eq_self _] at x_ground
      · assumption
      rintro (rfl | e_I)
      · exact ne rfl
      exact he (hI.indep.subset_ground e_I)
    exact Or.inr ((M.subset_closure _ hI.indep.subset_ground) x_mem)
  obtain (rfl | x_mem) := x_mem
  · have xnI := (notMem_subset hI.indep.subset_ground he)
    rw [ex_isBasis.indep.mem_closure_iff, or_iff_left xnI, dep_iff,
     C.extension_ground, insert_subset_insert_iff xnI, (C.extension_indep x), not_or,
     and_iff_left (hI.indep.subset_ground)]
    refine' ⟨fun hf ↦ he (hf.subset_ground (mem_insert _ _)), fun hf ↦ hf.2.2 _⟩
    rwa [insert_diff_self_of_notMem xnI, hI.closure_eq_closure]
  rw [ex_isBasis.indep.mem_closure_iff]
  obtain (x_dep | x_mem) := hI.indep.mem_closure_iff.1 x_mem
  · refine' Or.inl (dep_iff.2 ⟨fun ind ↦ _, _⟩)
    · obtain (M_ind | ⟨e_mem, _⟩) := (C.extension_indep e).1 ind
      · exact x_dep.not_indep M_ind
      exact he (x_dep.subset_ground e_mem.1)
    rw [C.extension_ground]
    exact (x_dep.subset_ground).trans (subset_insert _ _)
  exact Or.inr x_mem


theorem ModularCut.extension_closure_eq_of_notMem {e : α} {X : Set α} (C : M.ModularCut) (he : e ∉ M.E)
    (hX : M.closure X ∉ C) (heX : e ∉ X) : (C.extension e).closure X = M.closure X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have ex_isBasis : (extension C e).IsBasis' I X
  · rw [isBasis'_iff_isBasis_inter_ground, C.extension_ground, basis_iff, C.extension_indep,
    and_iff_right (Or.inl hI.indep)]
    have sub_inter:= subset_inter_iff.1 hI.isBasis_inter_ground.subset
    refine' ⟨subset_inter_iff.2 ⟨sub_inter.1, sub_inter.2.trans (subset_insert _ _)⟩,
     fun J J_ind I_sub_J J_sub_X ↦ _⟩
    rw [←hI.closure_eq_closure] at hX
    rw [isBasis'_iff_isBasis_inter_ground, basis_iff] at hI
    obtain (M_ind | ⟨e_mem, _, _⟩) := (C.extension_indep e).1 J_ind
    · apply hI.2.2 _ M_ind I_sub_J
      exact fun j j_mem ↦ ⟨(J_sub_X j_mem).1, M_ind.subset_ground j_mem⟩
    exact absurd (J_sub_X.trans inter_subset_left e_mem.1) heX
  rw [←hI.closure_eq_closure, ←ex_isBasis.closure_eq_closure, ext_iff]
  refine' fun x ↦ ⟨fun x_mem ↦ _, fun (x_mem) ↦ _⟩
  · obtain (x_dep | x_mem) := ex_isBasis.indep.mem_closure_iff.1 x_mem
    · have x_ground:= x_dep.subset_ground
      obtain (rfl | ne) := eq_or_ne x e
      · rw [dep_iff, (C.extension_indep x), not_or] at x_dep
        apply absurd _ x_dep.1.2
        rw [insert_diff_self_of_notMem (notMem_subset hI.indep.subset_ground he), hI.closure_eq_closure]
        refine' ⟨⟨mem_insert _ _, he⟩, hI.indep, hX⟩
      rw [hI.indep.mem_closure_iff, ←(@ModularCut.extension_delete _ M C e he), deleteElem,
      delete_dep_iff, disjoint_singleton_right]
      refine' Or.inl ⟨x_dep, fun e_mem ↦ heX (hI.subset (mem_of_mem_insert_of_ne e_mem ne.symm))⟩
    exact (M.subset_closure _ hI.indep.subset_ground x_mem)
  rw [ex_isBasis.indep.mem_closure_iff]
  obtain (x_dep | x_mem) := hI.indep.mem_closure_iff.1 x_mem
  · have del_dep : ((C.extension e) ＼ e).Dep (insert x I)
    · rwa [C.extension_delete he]
    exact Or.inl (delete_dep_iff.1 del_dep).1
  exact Or.inr x_mem





    --C.extension_delete heX]


  -- · rw [← C.extension_delete he, deleteElem, delete_isBasis'_iff] at hI
  --   have := hI.indep.isBasis_insert_iff (e := e)



theorem ModularCut.extension_isFlat_iff {F : Set α} {C : M.ModularCut} (hC : C.Nonempty) (e : α) (he : e ∉ M.E) :
    (C.extension e).IsFlat F ↔ (M.IsFlat F ∧ F ∉ C) ∨ (e ∈ F ∧ F \ {e} ∈ C) := by
  rw [isFlat_iff_closure_self]
  refine' ⟨fun closure_eq_self ↦ _, fun closure_eq_self ↦ _⟩
  · obtain (e_mem | e_notMem) := em (e ∈ F ∧ F \ {e} ∈ C)
    · exact Or.inr e_mem
    have M_eq : (C.extension e) ↾ M.E = M
    · have ground_eq : M.E = (C.extension e).E \ {e}
      · rw [(C.extension_ground), insert_diff_self_of_notMem he]
      rw [ground_eq, ←delete]
      exact C.extension_delete he
    obtain (e_notMem | f_notMem) := not_and_or.1 e_notMem
    · have Fsub : F ⊆ M.E
      · rw [←diff_singleton_eq_self e_notMem, diff_singleton_subset_iff, ←closure_eq_self, ←(C.extension_ground)]
        exact closure_subset_ground _ _
      obtain ⟨I, hI⟩ := (C.extension e).exists_isBasis F (Fsub.trans (subset_insert _ _))
      have hI' : M.IsBasis I F
      · sorry
      have F_isFlat : M.IsFlat F
      · rw [isFlat_iff_closure_self, ←M_eq, restrict_closure_eq _ Fsub (by simp)]
        · rw [closure_eq_self, inter_eq_self_of_subset_left Fsub]
      refine' Or.inl ⟨F_isFlat, fun F_mem ↦ e_notMem _⟩
      have e_nI := notMem_subset hI.subset e_notMem
      rw [←(IsFlat.closure_eq_iff_isBasis_of_indep _ hI.indep).2 hI, hI.indep.mem_closure_iff, dep_iff,
      (C.extension_indep e), not_or, insert_diff_self_of_notMem e_nI, hI'.closure_eq_closure,
      C.extension_ground, insert_subset_insert_iff e_nI, not_and_or]
      · refine' Or.inl ⟨⟨fun eI_ind ↦ he (eI_ind.subset_ground (mem_insert _ _)), _⟩,
        hI'.left_subset_ground⟩
        rw [isFlat_iff_closure_self.1 F_isFlat, not_and_or, not_not]
        exact Or.inr (Or.inr F_mem)
      rwa [isFlat_iff_closure_self]
    have e_nF : e ∉ F
    · intro e_F



  sorry


/-- Type-theory nonsense. -/
@[simps] def ModularCut.congr {M N : Matroid α} (C : M.ModularCut) (hMN : M = N) :
    N.ModularCut where
  Fs := C.Fs
  forall_isFlat := by subst hMN; exact C.forall_isFlat
  up_closed := by subst hMN; exact C.up_closed
  modular := by subst hMN; exact C.modular

@[simp] theorem ModularCut.mem_congr {F : Set α} {M N : Matroid α} (C : M.ModularCut) (hMN : M = N) :
    F ∈ C.congr hMN ↔ F ∈ C := Iff.rfl




/-- The modular cut corresponding to a deletion. (This is the empty cut if `e ∉ M.E`) -/
@[simps] def ModularCut.ofDelete (M : Matroid α) (e : α) : (M ＼ e).ModularCut where
  Fs := {F | (M ＼ e).IsFlat F ∧ e ∈ M.closure F}
  forall_isFlat := by simp only [deleteElem, mem_setOf_eq, and_imp]; tauto
  up_closed := by
    simp only [deleteElem, mem_setOf_eq, and_imp]
    exact fun {F F'} hF heF hFF' hF' ↦ ⟨hF', M.closure_subset_closure hFF' heF⟩
  modular := by
    intro Xs Xs_sub Xs_none mod
    refine' ⟨IsFlat.sInter Xs_none (fun F F_mem ↦ (Xs_sub F_mem).1), _⟩
    have mod': IsModularFamily M (fun X : Xs ↦ X) := mod.ofRestrict diff_subset
    haveI Xsne : _root_.Nonempty ↑Xs := nonempty_coe_sort.2 Xs_none
    rw [sInter_eq_iInter, ←IsModularFamily.iInter_closure_eq_closure_iInter mod', mem_iInter]
    exact fun X ↦ (Xs_sub X.2).2



@[simp] theorem ModularCut.mem_ofDelete_iff (M : Matroid α) (e : α) {F : Set α} :
  F ∈ ModularCut.ofDelete M e ↔ (M ＼ e).IsFlat F ∧ e ∈ M.closure F := Iff.rfl

def ModularCut.extensionEquiv (M : Matroid α) (e : α) (he : e ∉ M.E) :
    M.ModularCut ≃ {N : Matroid α | e ∈ N.E ∧ N ＼ e = M} where
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
    rw [←deleteElem, C.extension_delete he]
    refine' ⟨fun F_IsFlat ↦ _, fun F_C ↦ _⟩
    · obtain ⟨B, hB⟩ := M.exists_isBasis F F_IsFlat.1.subset_ground
      have hB' : (C.extension e).IsBasis B F
      · rw [←(@extension_delete _ M C e he)] at hB
        exact ((basis_restrict_iff diff_subset).1 hB).1
      have e_not_B : e ∉ B := fun e_in_B ↦ he (hB.left_subset_ground e_in_B)
      rw [←hB'.closure_eq_closure, hB'.indep.mem_closure_iff, or_iff_left e_not_B, dep_iff,
      (C.extension_indep), not_or, not_and_or, not_and_or, or_iff_right,
      insert_diff_self_of_notMem e_not_B, or_iff_right (not_not.2 hB.indep),
      not_not, hB.closure_eq_closure, F_IsFlat.1.closure] at F_IsFlat
      · exact F_IsFlat.2.1.2
      exact not_not.2 ⟨(mem_insert _ _), he⟩
    obtain ⟨B, hB⟩ := M.exists_isBasis F (C.isFlat F_C).subset_ground
    have hB' : (C.extension e).IsBasis B F
    · rw [←(@extension_delete _ M C e he)] at hB
      exact ((basis_restrict_iff diff_subset).1 hB).1
    have e_not_B : e ∉ B := fun e_in_B ↦ he (hB.left_subset_ground e_in_B)
    rw [←hB'.closure_eq_closure, hB'.indep.mem_closure_iff, or_iff_left e_not_B, dep_iff, C.extension_indep,
    not_or, not_and_or, not_and_or, insert_diff_self_of_notMem e_not_B, not_not, hB.closure_eq_closure,
    (C.isFlat F_C).closure]
    exact ⟨(C.isFlat F_C), ⟨(fun ind ↦ he (ind.subset_ground (mem_insert _ _))), Or.inr (Or.inr F_C)⟩, (insert_subset_insert hB.left_subset_ground)⟩
  right_inv := by
    rintro ⟨N, hN, rfl⟩
    simp only [deleteElem, coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
    apply ext_indep (by simpa) (fun I hI ↦ ?_)
    by_cases heI : e ∈ I
    · simp only [deleteElem, mem_setOf_eq, extension_indep, delete_indep_iff,
        disjoint_singleton_right, heI, not_true_eq_false, and_false, delete_ground, mem_diff,
        mem_singleton_iff, not_false_eq_true, and_self, and_true, delete_closure_eq, sdiff_idem,
        mem_congr, mem_ofDelete_iff, not_and, true_and, false_or]
      -- matroidy goals. Should be able to reduce to the case where `I \ {e}` is independent.
      refine' ⟨_, fun ind ↦ ⟨ind.subset diff_subset, _⟩⟩
      · rintro ⟨ind, isFlat⟩
        have Ie_isBasis : N.IsBasis (I \ {e}) (N.closure (I \ {e}) \ {e})
        · exact (ind.isBasis_closure).isBasis_subset (subset_diff_singleton (N.subset_closure _) (fun e_mem ↦ absurd rfl e_mem.2)) diff_subset
        obtain (closure_isFlat | closure_not_isFlat) := em ((N ＼ e).IsFlat (N.closure (I \ {e}) \ {e}))
        · have e_notMem:= isFlat closure_isFlat
          rw [←Ie_isBasis.closure_eq_closure, ind.mem_closure_iff, not_or, not_dep_iff] at e_notMem
          convert e_notMem.1
          simp [heI]
        obtain ⟨a, a_mem, a_notMem⟩ := exists_mem_closure_notMem_of_not_isFlat closure_not_isFlat
        have basis_restrict : (N ＼ e).IsBasis (I \ {e}) (N.closure (I \ {e}) \ {e})
        · exact (basis_restrict_iff diff_subset).2 ⟨Ie_isBasis, (diff_subset_diff_left (N.closure_subset_ground _))⟩
        rw [←basis_restrict.closure_eq_closure] at a_mem
        apply absurd ⟨_, (_ : a ≠ e)⟩ a_notMem
        · rw [ind.mem_closure_iff, dep_iff]
          rw [deleteElem, delete_eq_restrict, (ind.indep_restrict_of_subset _).mem_closure_iff,
          restrict_dep_iff] at a_mem
          · obtain (a_dep | a_mem) := a_mem
            · exact Or.inl ⟨a_dep.1, a_dep.2.trans diff_subset⟩
            exact Or.inr a_mem
          exact subset_diff_singleton ind.subset_ground (fun e_mem ↦ e_mem.2 rfl)
        apply ne_of_mem_of_notMem a_mem (notMem_subset (closure_subset_ground _ _) he)

      sorry
    simp [heI]


    -- some matroidy goal left
