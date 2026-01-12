-- Tutte's Triangle Lemma says that if T is a triangle of M,  a 3-connected matroid,
-- with at least 4 elements, and e and f are distinct elements of T such that M\e
-- and M\f both fail to be 3-connected, then then there is a triad T* of M such that
-- T* contains e and the intersection of T and T* has cardinality two.
-- This file contains the proof that the lemma holds in the case that
-- M\e,f is not connected (when M has at least 5 elements).
import Mathlib.Combinatorics.Matroid.Minor.Order
import Matroid.Connectivity.Vertical
import Matroid.Connectivity.Minor

open Set Matroid Function Separation

set_option linter.style.longLine false

-- for mathlib
lemma Set.exists_eq_of_encard_eq_three_of_mem {α : Type*} {s : Set α} {x : α}
    (hs : s.encard = 3) (hxs : x ∈ s) : ∃ y z, y ≠ x ∧ z ≠ x ∧ y ≠ z ∧ s = {x,y,z} := by
  obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := encard_eq_three.1 hs
  obtain rfl | rfl | rfl := by simpa using hxs
  · use b, c; grind
  · use a, c; grind
  use a, b; grind

-- for mathlib
lemma Set.exists_eq_of_encard_eq_three_of_mem_of_mem {α : Type*} {s : Set α} {x y : α}
    (hs : s.encard = 3) (hxs : x ∈ s) (hys : y ∈ s) (hxy : x ≠ y) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ s = {x,y,z} := by
  obtain ⟨a, b, hax, hbc, hab, rfl⟩ := s.exists_eq_of_encard_eq_three_of_mem hs hxs
  obtain rfl | rfl : y = a ∨ y = b := by simpa [hxy.symm] using hys
  · use b, hbc, hab.symm
  use a, hax, hab, by grind

namespace Matroid

variable {i : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P Q: M.Separation}

@[mk_iff]
structure IsTriangle (M : Matroid α) (T : Set α) : Prop where
  isCircuit : M.IsCircuit T
  three_elements : T.encard = 3

@[mk_iff]
structure IsTriad (M : Matroid α) (T : Set α) : Prop where
  isCocircuit : M.IsCocircuit T
  three_elements : T.encard = 3

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriangle.subset_ground (hT : M.IsTriangle T) : T ⊆ M.E := hT.isCircuit.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsTriad.subset_ground (hT : M.IsTriad T) : T ⊆ M.E := hT.isCocircuit.subset_ground

lemma IsTriangle.dual_isTriad (h : M.IsTriangle T) : M✶.IsTriad T := by
  simpa [isTriad_iff, isTriangle_iff] using h

lemma IsTriad.dual_isTriangle (h : M.IsTriad T) : M✶.IsTriangle T := by
  simpa [isTriad_iff, isTriangle_iff] using h

@[simp]
lemma dual_isTriad_iff : M✶.IsTriad T ↔ M.IsTriangle T := by
  simp [isTriad_iff, isTriangle_iff]

@[simp]
lemma dual_isTriangle_iff : M✶.IsTriangle T ↔ M.IsTriad T := by
  simp [isTriad_iff, isTriangle_iff]

/- Golfed. The hypothesis `hef` is only actually needed to handle the case where `M.E = T`.
We could also change the conclusion to the more concise and descriptive
`∃ x, x ∉ T ∧ M.IsTriad {e,f,x}`, but maybe this doesn't really matter for the wider lemma.

The first main optimization was considering the side of `P` containing `g` as opposed to using
`wlog` to make `g` on the `false` side.

The second was using the existing definition `Separation.ofDelete`,
which extends a separation of `M ＼ D` to a separation of `M`. This meant all the work defining
`Q` and proving it was a valid separation wasn't needed. -/
lemma tutte_triangle_disconnected_case (hM : M.TutteConnected 3) (hT : M.IsTriangle T) (he : e ∈ T)
    (hf : f ∈ T) (hef : e ≠ f) (hdef : ¬(M ＼ {e,f}).Connected) :
    ∃ K, (M.IsTriad K ∧ e ∈ K ∧ (K ∩ T).encard = 2) := by
  obtain ⟨g, hge : g ≠ e, hgf : g ≠ f, rfl : T = {e,f,g}⟩ :=
    T.exists_eq_of_encard_eq_three_of_mem_of_mem hT.three_elements he hf hef
  obtain ⟨heE : e ∈ M.E, hfE : f ∈ M.E, hgE : g ∈ M.E⟩ :=
    by simpa [insert_subset_iff] using hT.subset_ground
  have hgE' : g ∈ (M ＼ {e,f}).E := ⟨(hT.subset_ground (by simp)), (by simp [hge, hgf])⟩
  have hne : (M ＼ {e,f}).Nonempty := by rw [← ground_nonempty_iff]; use g
  obtain ⟨P, hP0, hPnt⟩ := exists_partition_of_not_connected hdef
  rw [P.not_trivial_iff] at hPnt
  -- let `j` be the side of `P` containing `g`.
  obtain ⟨j, hgj⟩ : ∃ j, g ∈ P j := by rwa [← P.iUnion_eq, mem_iUnion] at hgE'
  -- the separation `Q` obtained by adding `{e,f}` to side `j` of `P` has connectivity at most `1`.
  -- This is because `P` itself has connectivity zero, and we get from `P` to `Q` by
  -- adding a single element `e` to side `j`, and then an element `f` which is already spanned
  -- by `e` and side `j`.
  have hconn : (P.ofDelete j).eConn ≤ 1 := by
    grw [Separation.eConn_eq_eLocalConn _ j, ofDelete_apply_self, ofDelete_apply_not,
      show P j ∪ {e,f} = insert f (insert e (P j)) by grind, ← eLocalConn_closure_left,
      closure_insert_eq_of_mem_closure, eLocalConn_closure_left, eLocalConn_insert_left_le,
      ← P.eConn_eq_eLocalConn_of_isRestriction (by simp), hP0, zero_add]
    exact mem_of_mem_of_subset (hT.isCircuit.mem_closure_diff_singleton_of_mem hf)
      <| M.closure_subset_closure <| by grind
  -- Since `Q` is not a Tutte separation, and has at least three elements on the `j`
  -- side, it follows that `Q !j = P !j` is a singleton `{x}`.
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at hM
  have hnotsep : ¬ (P.ofDelete j).IsTutteSeparation :=
    hM.not_isTutteSeparation (P := P.ofDelete j) (by grw [hconn])
  rw [isTutteSeparation_iff_lt_encard (by enat_to_nat!), not_forall] at hnotsep
  -- rw [isTutteSeparation_iff_add_one_le_encard (by enat_to_nat!), not_forall] at hnotsep
  obtain ⟨i, hi⟩ := hnotsep
  grw [hconn, not_lt] at hi
  obtain rfl | rfl := (i.eq_or_eq_not j)
  · grw [ofDelete_apply_self, ← encard_le_encard subset_union_right, encard_pair hef] at hi
    simp at hi
  rw [ENat.le_one_iff_eq_zero_or_eq_one, ofDelete_apply_not, encard_eq_zero,
    ← not_nonempty_iff_eq_empty, ← imp_iff_not_or, imp_iff_right (hPnt _), encard_eq_one] at hi
  obtain ⟨x, hPx⟩ := hi
  have hxE : x ∈ (M ＼ {e, f}).E := by grw [← singleton_subset_iff, ← hPx, P.subset_ground]
  obtain ⟨hxE' : x ∈ M.E, hxe : x ≠ e, hxf : x ≠ f⟩ := by simpa using hxE
  -- Now we have that `x` is a loop or coloop of `M ＼ {e,f}`.
  have hxT : x ∉ ({e, f, g} : Set α) := by
    simp only [mem_insert_iff, hxe, hxf, mem_singleton_iff, false_or]
    rintro rfl
    exact (P.disjoint_bool j).notMem_of_mem_left hgj <| by simp [hPx]
  have hcard : 4 ≤ M.E.encard := by
    grw [show (4 : ℕ∞) = 2 + 1 + 1 from rfl, ← encard_le_encard (s := {x, e, f, g}) (by grind),
      encard_insert_of_notMem hxT, encard_insert_of_notMem, encard_pair hgf.symm]
    simp [hef, hge.symm]
  rw [← P.eConn_eq !j, hPx, eConn_singleton_eq_zero_iff hxE] at hP0
  obtain hxl | hxcl := hP0
  · -- the loop case doesn't happen, because this would mean that `x` is a loop of the
    -- three-connected matroid `M`.
    exfalso
    refine (hxl.of_isRestriction (delete_isRestriction ..)).not_tutteConnected ?_ (by simp) hM
    grw [← two_le_encard_iff_nontrivial, ← hcard]
    norm_num
  -- in the coloop case, we get that `K = {e,f,x}` is codependent in `M`.
  -- Therefore it contains a cocircuit. But `M` is `3`-connected, so in fact `K` is a cocircuit
  -- satisfying the lemma.
  rw [delete_isColoop_iff, diff_diff, union_singleton] at hxcl
  have hcard : encard {x,e,f} = 3 := by
    rw [encard_insert_of_notMem (by simp [hxe, hxf]), encard_pair hef, two_add_one_eq_three]
  refine ⟨{x,e,f}, ⟨?_, hcard⟩, by simp, ?_⟩
  · refine Dep.isCircuit_of_encard_lt_girth_add_one ?_ ?_
    · rw [dep_dual_iff, ← nonspanning_compl_iff, nonspanning_iff, and_iff_left diff_subset]
      refine fun hsp ↦ hxcl.1 <| by simpa [hsp.closure_eq] using hxcl.2.1
    grw [← hM.dual.girth_ge (by simpa), hcard]
    norm_num
  rwa [insert_inter_of_notMem, inter_eq_self_of_subset_left (by grind), encard_pair hef]










-- lemma tutte_triangle_disconnected_case (hG : 4 < M.E.encard) (hM : M.TutteConnected 3)
--     (hT : M.IsTriangle T) (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f) (hdef : ¬(M ＼ {e,f}).Connected) :
--     ∃ K, (M.IsTriad K ∧ e ∈ K ∧ (K ∩ T).encard = 2) := by
--   -- the hypothesis `hef` shouldn't be needed, since
--   have heM : e ∈ M.E := by
--     apply hT.isCircuit.subset_ground
--     exact he
--   have hfM : f ∈ M.E := by
--     apply hT.isCircuit.subset_ground
--     exact hf

-- -- There is an element g in T such that T = {e,f,g}.

--   have hTcard : T.encard = 3 := hT.three_elements

--   have h₁ : ∃ g ∈ T, g ≠ e ∧ g ≠ f ∧ T = {e,f,g} := by
--     apply Set.third_mem at hTcard
--     apply hTcard at he
--     apply he at hf
--     apply hf at hef
--     exact hef
--   obtain ⟨g, hg⟩ := h₁

--   have hgM : g ∈ M.E := by
--     apply mem_of_mem_of_subset
--     refine hg.1
--     refine hT.isCircuit.subset_ground

--   have hgMdef : g ∈ (M ＼ {e,f}).E := by simp [hgM, hg.2]

-- -- M\ e, f is nonempty and disconnected, so it contains a separation P.

--   have h₂ : (M＼{e,f}).Nonempty := by
--     simp only [← ground_nonempty_iff, delete_ground, diff_nonempty,
--       not_subset_iff_exists_mem_notMem]
--     use g
--     simp only [hgM, true_and, mem_insert_iff, not_or, mem_singleton_iff]
--     tauto
--   apply tutteConnected_two_iff at h₂
--   rw [← h₂, ← one_add_one_eq_two, not_tutteConnected_iff_exists] at hdef

--   obtain ⟨P, hP⟩ := hdef

--   have hPfalse : P false ⊆ (M ＼ {e,f}).E := P.subset_ground
--   have hPtrue : P true ⊆ (M ＼ {e,f}).E := P.subset_ground
--   have hPefalse : e ∉ P false := by
--     by_contra hc
--     apply mem_of_mem_of_subset at hc
--     apply hc at hPfalse
--     simp at hPfalse
--   have hPetrue : e ∉ P true := by
--     by_contra hc
--     apply mem_of_mem_of_subset at hc
--     apply hc at hPtrue
--     simp at hPtrue
--   have hPffalse : f ∉ P false := by
--     by_contra hc
--     apply mem_of_mem_of_subset at hc
--     apply hc at hPfalse
--     simp at hPfalse
--   have hPftrue : f ∉ P true := by
--     by_contra hc
--     apply mem_of_mem_of_subset at hc
--     apply hc at hPtrue
--     simp at hPtrue

-- -- Without loss of generality, g is in (P false).

--   wlog hgtrue : g ∈ P false generalizing P
--   apply this P.symm
--   simp only [eConn_symm, isTutteSeparation_symm_iff]
--   exact hP
--   simp only [Separation.symm_false]
--   exact hPtrue
--   simp only [Separation.symm_true]
--   exact hPfalse
--   simp only [Separation.symm_false]
--   exact hPetrue
--   simp only [Separation.symm_true]
--   exact hPefalse
--   simp only [Separation.symm_false]
--   exact hPftrue
--   simp only [Separation.symm_true]
--   exact hPffalse
--   simp only [Separation.symm_false]
--   have hgtrue₁ : g ∈ (M ＼ {e,f}).E \ (P false) := by
--     simp only [delete_ground, diff_diff, mem_diff, hgM, mem_union, not_or,
--       hgtrue, not_false_eq_true, and_true, mem_insert_iff, hg.2.1, mem_singleton_iff, hg.2.2]
--   rw [Separation.compl_eq] at hgtrue₁
--   exact hgtrue₁

-- -- We consider the partition Q = (P true, P false ∪ {e,f}) of M.

--   let QtoFun : Bool → Set α := fun i ↦ bif i then (P true) else ((P false) ∪ ({e,f} : Set α))

--   have hQpartition₁ : Disjoint (P true) ((P false) ∪ {e,f}) := by
--     have hQpartition₃ : Disjoint (P false) (P true) := P.disjoint_false_true
--     have hQpartition₄ : (P true) ⊆ (M ＼ {e,f}).E := P.subset_ground
--     have hQpartition₅ : Disjoint (P true) {e,f} := by
--       by_contra hc
--       simp only [disjoint_insert_right, not_and_or, hPetrue, not_not, false_or,
--         disjoint_singleton_right] at hc
--       tauto
--     apply Disjoint.union_right
--     exact P.disjoint_true_false
--     exact hQpartition₅

--   have hQpartitiondis : Pairwise (Disjoint on QtoFun) := by
--     rw [pairwise_disjoint_on_bool]
--     exact hQpartition₁

--   have hQpartition₂ : (P true) ∪ ((P false) ∪ {e,f}) = M.E := by
--     rw [subset_antisymm_iff]
--     have hQpartition₆ : (P false) ⊆ M.E := by
--       apply subset_trans
--       refine P.subset_ground
--       simp only [delete_ground, diff_subset]
--     have hQpartition₇ : (P true) ⊆ M.E := by
--       apply subset_trans
--       refine P.subset_ground
--       simp only [delete_ground, diff_subset]
--     have hQpartition₈ : (P true) ∪ ((P false) ∪ {e,f}) ⊆ M.E := by
--       simp [heM, hfM, insert_subset_iff, diff_subset]
--     have hQpartition₉ : (M ＼ {e,f}).E ⊆ ((P false) ∪ {e,f}) ∪ (P true) := by
--       rw [← P.union_eq]
--       simp only [union_subset_iff, subset_union_right]
--       grw [← subset_union_left]
--       simp only [subset_union_left, and_true]
--     have hQpartition₁₀ : M.E = (M ＼ {e,f}).E ∪ {e,f} := by
--       simp only [delete_ground, diff_union_self]
--       rw [union_eq_self_of_subset_right]
--       simp only [insert_subset_iff, heM, singleton_subset_iff, hfM, true_and]
--     have hQpartition₁₁ : (P false) ∪ {e,f} ∪ (P true) = ((P false) ∪ (P true)) ∪ {e,f} := by
--       simp only [union_assoc]
--       nth_rewrite 2 [union_comm]
--       rfl
--     have hQpartition₁₂ : M.E ⊆ (P true) ∪ ((P false) ∪ {e,f}) := by
--       rw [hQpartition₁₀, delete_ground, diff_union_self, union_insert, union_singleton,
--         insert_eq_of_mem, insert_eq_of_mem, ← union_assoc]
--       have hQpartition₁₃ : ⋃ i, P i = (M ＼ {e,f}).E := by
--         simp only [P.iUnion_eq]
--       have hQpartition₁₄ : ⋃ i, P i = (P true) ∪ (P false) := by
--         simp only [iUnion_bool, Separation.union_eq]
--       rw [← hQpartition₁₄, hQpartition₁₃, delete_ground]
--       simp only [subset_diff_union]
--       exact hfM
--       simp only [mem_insert_iff, heM, or_true]
--     apply And.intro hQpartition₈ hQpartition₁₂

--   have hQpartitioniunion : ⋃ i, QtoFun i = M.E := by
--     simp_all only [iUnion_bool, cond_true, cond_false, QtoFun]

--   let Q : M.Separation := (Separation.mk QtoFun hQpartitiondis hQpartitioniunion)

--   have hQtrue : Q true = P true := by rfl
--   have hQleft : Q false = P false ∪ {e,f} := by rfl

-- -- Q is a 2-separation of M.

--   have hQ2sep : Q.eConn + 1 ≤ 2 := by
--     have hQ2sep₆ : M.eLocalConn (Q true) (M.closure (Q false \ {f})) + 1 ≤ 2 := by
--       have hQ2sep₆₁ : M.eLocalConn (Q true) (Q false \ {f}) + 1 ≤ 2 := by
--         have hQ2sep₆₂ : (M ＼ {f}).eLocalConn (Q true) (Q false \ {f}) + 1 ≤ 2 := by
--           have hQ2sep₆₄ : (M ＼ {f}).eConn (Q true) + 1 ≤ 2 := by
--             have hQ2sep₆₁₃ : (M ＼ {f} ＼ {e}).eConn (Q true) + 1 ≤ 1 := by
--               simp only [delete_delete, union_singleton, hQtrue]
--               simp only [eConn_eq]
--               exact hP.1
--             grw [eConn_le_eConn_delete_singleton_add_one]
--             rw [← one_add_one_eq_two]
--             simp only [ENat.add_one_le_add_one_iff]
--             exact hQ2sep₆₁₃
--           rw [eConn_eq_eLocalConn] at hQ2sep₆₄
--           have hQ2sep₆₅ : ((M ＼ {f}).E \ Q true) = Q false \ {f} := by
--             rw [hQleft, hQtrue, delete_ground]
--             have hQ2sep₆₆ : P true  = (M.E \ {e,f}) \ (P false) := by
--               rw [← delete_ground]
--               rw [Separation.compl_eq]
--               tauto
--             rw [hQ2sep₆₆]
--             simp only [diff_diff]
--             have hQ2sep₆₇ : ({f} ∪ M.E \ ({e, f} ∪ P false)) = M.E \ (P false ∪ {e}) := by
--               simp [union_singleton, ← diff_diff]
--               rw [← delete_ground]
--               simp only [Separation.compl_eq]
--               have hQ2sep₆₁₁ : insert e (P false) = (Q false) \ {f} := by
--                 rw [hQleft]
--                 simp only [union_insert, union_singleton]
--                 rw [insert_comm]
--                 have hQ2sep₆₁₂ : f ∉ insert e (P false) := by
--                   simp only [mem_insert_iff, not_or, hPffalse, not_false_eq_true, and_true]
--                   tauto
--                 apply insert_diff_self_of_notMem at hQ2sep₆₁₂
--                 rw [hQ2sep₆₁₂]
--               rw [hQ2sep₆₁₁]
--               rw [diff_diff_eq_sdiff_union]
--               nth_rewrite 1 [Separation.compl_eq]
--               simp only [union_singleton]
--               tauto
--               simp only [singleton_subset_iff, hfM]
--             rw [hQ2sep₆₇]
--             rw [diff_diff_right_self]
--             have hQ2sep₆₈ : (P false ∪ {e}) ⊆ M.E := by
--               simp only [union_subset_iff, singleton_subset_iff, heM, and_true]
--               apply subset_trans at hPfalse
--               have hQ2sep₆₉ : (M ＼ {e,f}).E ⊆ M.E := by
--                 simp only [delete_ground, diff_subset]
--               apply hPfalse at hQ2sep₆₉
--               exact hQ2sep₆₉
--             apply inter_eq_self_of_subset_right at hQ2sep₆₈
--             rw [hQ2sep₆₈]
--             simp only [union_singleton, union_insert]
--             rw [insert_comm]
--             have hQ2sep₆₁₀ : f ∉ insert e (P false) := by
--               simp only [mem_insert_iff, hPffalse, or_false]
--               rw [← not_ne_iff, not_not]
--               tauto
--             apply insert_diff_self_of_notMem at hQ2sep₆₁₀
--             rw [hQ2sep₆₁₀]
--           rw [← hQ2sep₆₅]
--           exact hQ2sep₆₄
--         rw [eLocalConn_delete_eq] at hQ2sep₆₂
--         simp only [diff_diff, union_singleton, pair_eq_singleton] at hQ2sep₆₂
--         have hQ2sep₆₃ : Q true = Q true \ {f} := by
--           rw [diff_singleton_eq_self]
--           rw [hQtrue]
--           exact hPftrue
--         rw [hQ2sep₆₃]
--         exact hQ2sep₆₂
--       rw [eLocalConn_closure_right]
--       exact hQ2sep₆₁
--     have hQ2sep₅ : Q false ⊆ M.closure (Q false \ {f}) := by
--       have hQ2sep₅₁ : f ∈  M.closure (Q false \ {f}) := by
--         rw [mem_closure_iff_mem_or_exists_isCircuit, mem_diff_singleton, hQleft]
--         simp_all only [mem_union, mem_insert_iff, mem_singleton_iff, or_true, true_and]
--         simp
--         use T
--         simp only [subset_insert_iff, mem_diff_singleton]
--         rw [hg.2.2.2]
--         simp only [diff_singleton_subset_iff, insert_subset_iff, mem_insert_iff, true_or, true_and,
--         or_true, singleton_subset_iff, hgtrue, and_true]
--         symm at hef
--         simp_all only [ne_eq, not_false_eq_true, or_true]
--         rw [← hg.2.2.2]
--         simp_all only [hT.isCircuit, true_and]
--       have hQ2sep₅₂ : Q false = (Q false \ {f}) ∪ {f} := by
--         simp only [union_singleton, insert_diff_singleton]
--         rw [hQleft]
--         simp_all only [union_insert, union_singleton, insert_comm]
--         simp only [mem_insert_iff, true_or, insert_eq_of_mem]
--       nth_rewrite 1 [hQ2sep₅₂]
--       simp only [union_subset_iff, singleton_subset_iff, hQ2sep₅₁, and_true]
--       have hQ2sep₅₃ : Q false \ {f} ⊆ M.E := by
--         simp only [diff_subset_iff, singleton_union]
--         rw [insert_eq_of_mem]
--         simp only [Separation.subset_ground]
--         exact hfM
--       apply subset_closure at hQ2sep₅₃
--       exact hQ2sep₅₃
--     have hQ2sep₄ : M.eLocalConn (Q true) (Q false) ≤
--       M.eLocalConn (Q true) (M.closure (Q false \ {f})) := by
--       apply eLocalConn_mono_right at hQ2sep₅
--       exact hQ2sep₅
--     have hQ2sep₃ : M.eLocalConn (Q true) (Q false) + 1 ≤
--       M.eLocalConn (Q true) (M.closure (Q false \ {f})) + 1:= by
--       grw [hQ2sep₄]
--     have hQ2sep₂ : M.eLocalConn (Q true) (Q false) + 1 ≤ 2 := by
--       grw [← hQ2sep₆]
--       exact hQ2sep₃
--     have hQ2sep₁ : M.eConn (Q true) + 1 ≤ 2 := by
--       simp only [eConn_eq_eLocalConn]
--       rw [Separation.compl_eq]
--       exact hQ2sep₂
--     rw [← eConn_eq]
--     exact hQ2sep₁

-- -- Now Q true must contain a single element.

--   have hQtruesing : (Q true).encard ≤ 1 := by
--     have hQtruesing₁ : ¬Q.IsTutteSeparation := by
--       by_contra hc
--       have hQtruesing₂ : ∃ R : M.Separation, R.eConn + 1 ≤ 2 ∧ R.IsTutteSeparation := by
--         use Q
--       rw [← not_tutteConnected_iff_exists] at hQtruesing₂
--       simp only [two_add_one_eq_three] at hQtruesing₂
--       tauto
--     rw [isTutteSeparation_iff true] at hQtruesing₁
--     simp only [not_and_or] at hQtruesing₁
--     have hQtruesing₃ : ∃ C ⊆ Q false, M.IsCircuit C := by
--       use T
--       simp only [hT.isCircuit, and_true]
--       rw [hQleft, hg.2.2.2]
--       simp only [insert_subset_iff, mem_union, mem_insert_iff, true_or, or_true, true_and,
--         mem_singleton_iff, singleton_subset_iff, hgtrue]
--     have hQtruesing₄ : M.Dep (Q false) := by
--       rw [dep_iff_superset_isCircuit]
--       use T
--       simp only [hT.isCircuit, and_true]
--       rw [hg.2.2.2]
--       simp only [insert_subset_iff, hQleft, union_insert, mem_insert_iff, true_or, true_and,
--         union_singleton, or_true, singleton_subset_iff, hgtrue]
--     have hQtruesing₅ : (M.Dep (Q false) ∨ M.Codep (Q false)) := Or.inl hQtruesing₄
--     have hQtruesing₆ : ¬(M.Dep (Q true) ∨ M.Codep (Q true)) := by
--       tauto
--     rw [not_or, not_dep_iff, not_codep_iff] at hQtruesing₆
--     rw [← eConn_eq_encard_iff'] at hQtruesing₆
--     rw [← one_add_one_eq_two, ENat.add_one_le_add_one_iff] at hQ2sep
--     rw [← hQtruesing₆]
--     rw [eConn_eq]
--     exact hQ2sep
--     simp only [eConn_eq]
--     have hQtruesing₇ : Q.eConn ≤ 1 := by
--       rw [← one_add_one_eq_two, ENat.add_one_le_add_one_iff] at hQ2sep
--       exact hQ2sep
--     apply ne_top_of_le_ne_top at hQtruesing₇
--     exact hQtruesing₇
--     symm
--     apply ENat.top_ne_one
--   have hQtruesing₈ : (Q true).encard = 1 := by
--     rw [ENat.le_one_iff_eq_zero_or_eq_one] at hQtruesing
--     have hQtruesing₉ : ¬(Q true).encard = 0 := by
--       by_contra hc
--       rw [encard_eq_zero, hQtrue] at hc
--       have hQtruesing₁₀ : P.IsTutteSeparation := hP.2
--       exact (hQtruesing₁₀.nonempty true).ne_empty hc
--     apply Or.resolve_left at hQtruesing
--     apply hQtruesing at hQtruesing₉
--     exact hQtruesing₉

--   -- (P true) is a circuit or a cocircuit of M \ e, f.

--   have hPtutte : P.IsTutteSeparation := hP.2

--   have hPtruecocorcir : (M ＼ {e,f}).IsCircuit (P true) ∨ (M ＼ {e,f}).IsCocircuit (P true) := by
--     apply IsTutteSeparation.singleton_is_circuit_or_cocircuit at hPtutte
--     rw [hQtrue] at hQtruesing₈
--     apply hPtutte at hQtruesing₈
--     exact hQtruesing₈

--   -- (P true) must be a cocircuit of M \ e,f.

--   have hPtruecoc₇ : (M ＼ {e,f}).IsCircuit (P true) → (M ＼ {e,f}).IsCocircuit (P true) := by
--     have hPtruecoc₁ : M.Nonempty := by
--       simp only [← ground_nonempty_iff, nonempty_def]
--       use g
--     have hPtruecoc₂ : M.E.Nontrivial := by
--       rw [Set.nontrivial_iff_exists_ne heM]
--       use g
--       simp only [hgM, true_and]
--       exact hg.2.1
--     intro h
--     by_contra hc
--     rw [← circuit_iff_delete_of_disjoint] at h
--     have hPtruecoc₃ : M.Connected := by
--       have hPtruecoc₄ : 2 ≤ 3 := by simp
--       have hPtruecoc₅ : (2 : ENat) ≤ (3 : ENat) := by
--         rw [← ENat.coe_le_coe] at hPtruecoc₄
--         exact hPtruecoc₄
--       have hPtruecoc₆ : M.TutteConnected 2 := by
--         apply TutteConnected.mono at hM
--         apply hM at hPtruecoc₅
--         exact hPtruecoc₅
--       rw [tutteConnected_two_iff] at hPtruecoc₆
--       exact hPtruecoc₆
--     apply IsConnected.nontrivial_of_loopless at hPtruecoc₂
--     simp only [loopless_iff_forall_isCircuit] at hPtruecoc₂
--     apply hPtruecoc₂ at h
--     rw [← one_lt_encard_iff_nontrivial] at h
--     rw [← hQtrue, hQtruesing₈] at h
--     tauto
--     exact hPtruecoc₃
--     simp only [disjoint_insert_right, hPetrue, not_false_eq_true, true_and,
--       disjoint_singleton_right, hPftrue]

--   have hPtruecoc : (M ＼ {e,f}).IsCocircuit (P true) := Or.elim hPtruecocorcir hPtruecoc₇ (by simp)

--   -- Now (P true) ∪ {e,f} is the triad we are seeking.

--   apply IsCocircuit.exists_subset_isCocircuit_of_delete at hPtruecoc
--   obtain ⟨C', hC'⟩ := hPtruecoc

--   have h₃ : Disjoint (P true) {e,f} := by
--     simp only [disjoint_insert_right, disjoint_singleton_right, hPetrue, hPftrue]
--     tauto
--   have h₄ : ((P true) ∪ {e,f}).encard = 3 := by
--     rw [encard_union_eq]
--     rw [← hQtrue, hQtruesing₈, encard_insert_of_notMem, encard_singleton]
--     rw [← add_assoc, one_add_one_eq_two, two_add_one_eq_three]
--     simp only [mem_singleton_iff]
--     exact hef
--     exact h₃
--   have h₅ : C' ⊆ (P true) ∪ {e,f} := hC'.2.2
--   have h₆ : C'.encard ≤ 3 := by
--     apply encard_mono at h₅
--     rw [h₄] at h₅
--     exact h₅
--   have h₇ : 3 ≤ M✶.girth := by
--     have h₈ : M✶.TutteConnected (2 + 1) := by
--       simp [tutteConnected_dual_iff]
--       rw [two_add_one_eq_three]
--       exact hM
--     have h₉ : 2 * 2 ≤ M✶.E.encard := by
--       rw [dual_ground]
--       grw [← hG]
--       rw [two_mul, two_add_two_eq_four]
--     apply TutteConnected.girth_ge at h₈
--     apply h₈ at h₉
--     tauto
--   have h₁₀ : M✶.IsCircuit C' := by
--     rw [← IsCocircuit]
--     exact hC'.1
--   have h₁₁ : 3 ≤ C'.encard := by
--     apply IsCircuit.girth_le_card at h₁₀
--     grw [h₇]
--     exact h₁₀
--   have h₁₂ : C'.encard = 3 := by
--     apply le_antisymm
--     exact h₆
--     exact h₁₁
--   have h₁₃ : C' = (P true) ∪ {e,f} := by
--     by_contra hc
--     have h₁₄ : ¬((P true) ∪ {e,f}) ⊆ C' := by
--       by_contra hc₂
--       apply subset_antisymm at h₅
--       apply h₅ at hc₂
--       tauto
--     have h₁₅ : C' ⊂ (P true) ∪ {e,f} := by
--       simp only [ssubset_def, h₅, h₁₄, not_false_eq_true, true_and]
--     apply Finite.encard_lt_encard at h₁₅
--     rw [h₁₂, h₄] at h₁₅
--     tauto
--     rw [← encard_ne_top_iff, h₁₂]
--     simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true]
--   use C'
--   rw [h₁₃, mem_union, mem_insert_iff, eq_self_iff_true, true_or, or_true, true_and]
--   rw [← h₁₃]
--   have h₁₆ : M.IsTriad C' := by
--     rw [isTriad_iff]
--     simp only [hC'.1, true_and]
--     exact h₁₂
--   simp only [h₁₆, true_and]
--   have h₁₇ : C' ∩ T = {e,f} := by
--     have h₁₈ : {e,f} ⊆ C' ∩ T := by
--       simp only [insert_subset_iff, h₁₃, mem_inter_iff, he, mem_union, mem_insert_iff, true_or,
--         or_true, and_true, singleton_subset_iff, mem_singleton_iff, hf]
--     apply subset_antisymm
--     rw [h₁₃, hg.2.2.2]
--     simp only [union_inter_distrib_right]
--     have h₁₉ : (P true) ∩ {e,f,g} = ∅ := by
--       rw [inter_insert_of_notMem, inter_insert_of_notMem, inter_singleton_eq_empty]
--       have h₂₀ : g ∈ (M ＼ {e,f}).E \ (P true) := by
--         rw [Separation.compl_true]
--         exact hgtrue
--       rw [mem_diff] at h₂₀
--       simp only [hgMdef, true_and] at h₂₀
--       exact h₂₀
--       exact hPftrue
--       exact hPetrue
--     rw [h₁₉]
--     simp only [empty_union, inter_subset_left]
--     exact h₁₈
--   rw [h₁₇]
--   rw [encard_insert_of_notMem, encard_singleton]
--   rw [one_add_one_eq_two]
--   simp only [mem_singleton_iff, hef, not_false_eq_true]
