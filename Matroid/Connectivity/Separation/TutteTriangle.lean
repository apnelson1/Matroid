import Mathlib.Combinatorics.Matroid.Minor.Order
import Matroid.Triangle
import Matroid.Connectivity.Separation.Vertical

open Set Matroid Function Separation

set_option linter.style.longLine false

lemma Bool.range_bool {α : Type*} (f : Bool → α) (b : Bool) : range f = {f b, f !b} := by
  cases b <;> simp [pair_comm]

@[simp]
lemma Bool.apply_eq_or_eq {α : Type*} (f : Bool → α) (b : Bool) : f b = f false ∨ f b = f true := by
  cases b <;> simp

@[simp]
lemma Bool.apply_eq_or_eq_bool {α : Type*} (f : Bool → α) (b c : Bool) : f b = f c ∨ f b = f !c := by
  cases b <;> cases c <;> simp


namespace Matroid

variable {i : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P : M.Separation}

lemma Separation.union_apply_eq_diff_inter (P Q : M.Separation) (b c : Bool) :
    P b ∪ Q c = M.E \ (P (!b) ∩ Q (!c)) := sorry

structure TriangleDeletePair (M : Matroid α) where
  card_ge : 4 ≤ M.E.encard
  three_connected : M.TutteConnected (1 + 1 + 1)
  x : Bool → α
  g : α
  P : (i : Bool) → (M ＼ {x i}).Separation
  sep : ∀ {b}, (P b).IsTutteSeparation
  conn_le : ∀ {b}, (P b).eConn ≤ 1
  mem : ∀ {b}, x (!b) ∈ P b true
  true_false_triangle : M.IsTriangle {g, x true, x false}

lemma TriangleDeletePair.mem' (Δ : M.TriangleDeletePair) {b} : Δ.x b ∈ Δ.P (!b) true := by
  simpa using Δ.mem (b := !b)

lemma TriangleDeletePair.triangle (Δ : M.TriangleDeletePair) {b} :
    M.IsTriangle {Δ.g, Δ.x b, Δ.x (!b)} := by
  cases b
  · exact pair_comm _ _ ▸ Δ.true_false_triangle
  exact Δ.true_false_triangle

@[simp]
lemma TriangleDeletePair.notMem (Δ : M.TriangleDeletePair) {b c} : Δ.x b ∉ Δ.P b c :=
  notMem_subset (Δ.P b).subset <| by simp

lemma TriangleDeletePair.notMem_closure (Δ : M.TriangleDeletePair) (b c) :
    Δ.x b ∉ M.closure (Δ.P b c) :=
  Δ.three_connected.notMem_closure_of_separation_deleteElem (by simpa using Δ.conn_le) Δ.sep c

lemma TriangleDeletePair.g_mem_ground (Δ : M.TriangleDeletePair) : Δ.g ∈ M.E :=
  Δ.true_false_triangle.mem_ground₁

lemma TriangleDeletePair.g_mem_false (Δ : M.TriangleDeletePair) {b} : Δ.g ∈ Δ.P b false := by
  rw [← Separation.compl_true, delete_ground, mem_diff, mem_diff, mem_singleton_iff,
    and_iff_right Δ.g_mem_ground, and_iff_right Δ.triangle.ne₁₂]
  exact fun hmem ↦ Δ.notMem_closure b true <| mem_of_mem_of_subset Δ.triangle.mem_closure₂ <|
    M.closure_subset_closure <| pair_subset hmem Δ.mem

lemma TriangleDeletePair.delete_tutteConnected (Δ : M.TriangleDeletePair) {b} :
    (M ＼ {Δ.x b}).TutteConnected (1 + 1) :=
  Δ.three_connected.deleteElem (by grw [← Δ.card_ge]; norm_num) (Δ.x b)

@[simp]
lemma TriangleDeletePair.range_subset_ground (Δ : M.TriangleDeletePair) : range Δ.x ⊆ M.E := by
  grw [← Δ.true_false_triangle.subset_ground, ← subset_insert, Bool.range_eq, pair_comm]

lemma TriangleDeletePair.coindep_range (Δ : M.TriangleDeletePair) : M.Coindep (range Δ.x) := by
  refine M✶.indep_of_card_lt_girth ?_ Δ.range_subset_ground
  grw [← image_univ, encard_image_le, Bool.univ_eq, encard_pair_le,
    ← three_le_girth_iff.2 <| Δ.three_connected.dual.simple Δ.card_ge]
  norm_num

lemma TriangleDeletePair.delete_connected (Δ : M.TriangleDeletePair) {b} :
    (M ＼ {Δ.x b}).Connected := by
  have hne : (M ＼ {Δ.x b}).Nonempty := ⟨⟨Δ.g, Δ.g_mem_ground, by simpa using Δ.triangle.ne₁₂⟩⟩
  rw [← tutteConnected_two_iff]
  exact Δ.delete_tutteConnected

lemma TriangleDeletePair.delete_delete_eq (Δ : M.TriangleDeletePair) {b} :
    (M ＼ {Δ.x b} ＼ {Δ.x !b}) = M ＼ range Δ.x := by
  rw [Bool.range_bool _ b, delete_delete, singleton_union]

def TriangleDeletePair.Q (Δ : M.TriangleDeletePair) (b : Bool) : (M ＼ range Δ.x).Separation :=
  (Δ.P b).induce _

lemma TriangleDeletePair.Q_apply' (Δ : M.TriangleDeletePair) {b i} :
    Δ.Q b i = Δ.P b i \ range Δ.x := by
  rw [TriangleDeletePair.Q, induce_apply_delete_of_delete _ (by simp)]

lemma TriangleDeletePair.Q_apply (Δ : M.TriangleDeletePair) {b i} :
    Δ.Q b i = Δ.P b i \ {Δ.x (!b)} := by
  rw [Δ.Q_apply', Bool.range_bool _ b, ← union_singleton, ← diff_diff, sdiff_eq_left.2 (by simp)]

lemma TriangleDeletePair.g_mem_false_Q (Δ : M.TriangleDeletePair) {b} : Δ.g ∈ Δ.Q b false := by
  rw [Q_apply, mem_diff_singleton, and_iff_right Δ.g_mem_false]
  exact Δ.triangle.ne₁₃

lemma TriangleDeletePair.P_nontrivial (Δ : M.TriangleDeletePair) {b} : (Δ.P b).Nontrivial := by
  simp_rw [Separation.nontrivial_iff_forall, Bool.forall_bool]
  exact ⟨⟨Δ.g, Δ.g_mem_false⟩, ⟨Δ.x !b, Δ.mem⟩⟩

@[simp]
lemma TriangleDeletePair.eConn_eq (Δ : M.TriangleDeletePair) {b} : (Δ.P b).eConn = 1 :=
  Δ.conn_le.antisymm <| ENat.one_le_iff_ne_zero.2 fun h0 ↦
    (Δ.delete_connected.trivial_of_eConn_eq_zero h0).not_nontrivial Δ.P_nontrivial

lemma TriangleDeletePair.P_apply_nontrivial (Δ : M.TriangleDeletePair) {b i} :
    (Δ.P b i).Nontrivial :=
  (Δ.sep.nontrivial (P := Δ.P b) (by simp) i)

lemma TriangleDeletePair.Q_nontrivial (Δ : M.TriangleDeletePair) {b} : (Δ.Q b).Nontrivial := by
  simp_rw [Separation.nontrivial_iff_forall, Δ.Q_apply]
  exact fun i ↦ Δ.P_apply_nontrivial.diff_singleton_nonempty _

lemma TriangleDeletePair.faithful_delete (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) {b} : (Δ.P b).Faithful (M ＼ range Δ.x) := by
  rw [← Δ.delete_delete_eq (b := b)]
  refine (Δ.delete_connected.tutteConnected_one_add_one).faithful_of_tutteConnected_delete
    (by rwa [delete_delete_eq]) (Δ.P b) (by simp) fun i ↦ ?_
  rw [one_lt_encard_iff_nontrivial]
  exact Δ.P_apply_nontrivial

lemma TriangleDeletePair.mem_closure (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) {b} : Δ.x b ∈ M.closure (Δ.Q (!b) true) := by
  rw [Q_apply']
  exact (Δ.faithful_delete hc).mem_closure_delete_of_delete (by simp) Δ.mem' Δ.coindep_range

lemma TriangleDeletePair.not_subset (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) {b} : (¬ Δ.Q b true ⊆ Δ.Q (!b) false) := by
  refine fun hss ↦ Δ.notMem_closure (b := !b) (c := false) <|
    mem_of_mem_of_subset (Δ.mem_closure hc) ?_
  grw [b.not_not, hss, Q_apply, diff_subset]

lemma TriangleDeletePair.cross_induce_faithful (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) (b c : Bool) (hbc : (b && c) = false) {d} :
    (((Δ.Q true).cross (Δ.Q false) b c d).induce M (!d)).Faithful (M ＼ range Δ.x) := by
  refine faithful_of_subset_closure_of_delete _ <| range_subset_iff.2 ?_
  have aux (d i) : Δ.x i ∈ M.closure (insert Δ.g (Δ.Q d true)) := by
    have hd : Δ.x (!d) ∈ M.closure (insert Δ.g (Δ.Q d true)) := by
      grw [← subset_insert]
      simpa using Δ.mem_closure hc (b := !d)
    revert i
    grw [Bool.forall_bool' d, and_iff_left hd, ← closure_insert_eq_of_mem_closure hd,
      ← empty_subset ((Δ.Q d true)), insert_empty_eq, pair_comm]
    exact Δ.triangle.mem_closure₂
  cases b
  · cases c
    · exact fun i ↦ mem_of_mem_of_subset (Δ.mem_closure hc) <| M.closure_subset_closure
        <| by cases i with simp
    refine fun i ↦ mem_of_mem_of_subset (aux true i) <| M.closure_subset_closure ?_
    simp [insert_subset_iff, Δ.g_mem_false_Q]
  obtain rfl : c = false := by grind
  refine fun i ↦ mem_of_mem_of_subset (aux false i) <| M.closure_subset_closure ?_
  simp [insert_subset_iff, Δ.g_mem_false_Q]


lemma TriangleDeletePair.R_faithful (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) : Δ.R.Faithful (M ＼ range Δ.x) := by
  _


lemma TriangleDeletePair.eConn_Q_eq (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) {b} : (Δ.Q b).eConn = 1 := by
  convert (Δ.faithful_delete hc (b := b)).eConn_induce_eq using 1
  simp

lemma TriangleDeletePair.cross_nontrivial (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) :
    ((Δ.Q true).cross (Δ.Q false) true true true).Nontrivial := by
  rw [← Separation.not_trivial_iff, Δ.Q_nontrivial.cross_trivial_iff, not_or]
  exact ⟨Δ.not_subset hc, Δ.not_subset hc⟩

lemma TriangleDeletePair.Q_inter_eq (Δ : M.TriangleDeletePair) (i j) :
    Δ.Q true i ∩ Δ.Q false j = Δ.P true i ∩ Δ.P false j := by
  rw [Q_apply', Q_apply', diff_inter_diff_right, sdiff_eq_left.2 (by simp)]

def TriangleDeletePair.R (Δ : M.TriangleDeletePair) (b : Bool) : M.Separation :=
  (((Δ.Q true).cross (Δ.Q false) b (!b) b).induce (M ＼ {Δ.x b}) b).induce M (!b)

lemma foo (Δ : M.TriangleDeletePair) (b : Bool) :
    Δ.R b b = insert (Δ.x (!b)) (Δ.P true b ∩ Δ.P false (!b)) := by
  simp [TriangleDeletePair.R]
  rw [induce_apply_self, cross_apply_not, Bool.not_not, Separation.union_apply_eq_diff_inter,
    diff_diff_right, delete_ground, delete_ground, diff_diff_right, diff_eq_empty.2 diff_subset,
      empty_union, diff_inter_right_comm, inter_eq_self_of_subset_right Δ.range_subset_ground,
      Bool.not_not, ← Δ.Q_inter_eq, inter_eq_self_of_subset_right, ← singleton_union]
  · convert rfl
    rw [Bool.range_bool _ b, insert_diff_self_of_notMem (by simp [Δ.triangle.ne₂₃])]
  grw [inter_subset_left, Separation.subset, delete_ground, diff_subset_diff_right]
  simp




lemma TriangleDeletePair.inter_subsingleton (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) (b c : Bool) (hbc : b || c)
    (hcc' : (Δ.P true b ∩ Δ.P false c).Nonempty) :
    ((Δ.P true (!b)) ∩ (Δ.P false (!c))).Subsingleton := by
  have hsm := (Δ.Q true).submod_cross (Δ.Q false) (!b) (!c) false true
  grw [Δ.eConn_Q_eq hc, Δ.eConn_Q_eq hc, add_comm, ← Nontrivial.one_le_eConn_of_tutteConnected _ hc,
    add_comm, ENat.add_one_le_add_one_iff] at hsm
  · rw [← (Δ.cross_induce_faithful hc (!b) (!c) (by grind)).eConn_eq_of_delete] at hsm
    obtain ⟨(rfl | rfl), hss⟩ := Δ.three_connected.exists_subsingleton_of_isTutteSeparation hsm
    · rwa [Bool.not_false, induce_true_false, apply_inter_ground_of_delete, cross_apply_self,
        Δ.Q_inter_eq] at hss
    simp [induce_apply_of_delete_self _ _ Δ.range_subset_ground, Δ.true_false_triangle.ne₂₃] at hss
  grw [Separation.nontrivial_iff_forall, Bool.forall_bool, cross_apply_true_false, Bool.not_not,
    Bool.not_not, cross_apply_self, Bool.not_not, Bool.not_not, Δ.Q_inter_eq, and_iff_left hcc']
  exact (Δ.Q_nontrivial.nonempty _).mono subset_union_left

lemma TriangleDeletePair.inter_false_eq (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) : Δ.P true false ∩ Δ.P false false = {Δ.g} := by
  refine Subsingleton.eq_singleton_of_mem ?_ ⟨Δ.g_mem_false, Δ.g_mem_false⟩
  refine Δ.inter_subsingleton hc true true (by simp) <| ?_
  grw [← Δ.Q_inter_eq, ← (Δ.Q false).compl_false, ← inter_diff_assoc, Separation.inter_ground_eq,
    diff_nonempty]
  exact Δ.not_subset hc

lemma TriangleDeletePair.foo (Δ : M.TriangleDeletePair) (hc : (M ＼ range Δ.x).TutteConnected 2) :
    ∃ i, (Δ.P true i).encard ≤ 2 := by
  -- simp_rw [show (2 : ℕ∞) = 1 + 1 from rfl, ENat.add_one_le_iff (m := 1) (by simp),
  --   ← not_le, encard_le_one_iff_subsingleton]
  by_contra! hcon
  have hcon1 := hcon false
  rw [← encard_diff_add_encard_inter (t := Δ.P false false), Δ.inter_false_eq hc,
    encard_singleton, (Δ.P false).diff_eq_inter_bool _ _] at hcon1
  ·
    replace hcon1 := Order.add_one_le_of_lt hcon1
    rw [ENat.add_one_le_add_one_iff, two_le_encard_iff_nontrivial, Bool.not_false] at hcon1
    have hss := Δ.inter_subsingleton hc _ _ (by decide) hcon1.nonempty
    obtain h_emp | ⟨y, hy⟩ := hss.eq_empty_or_singleton
    ·

  nth_grw 1 [delete_ground, subset_diff_singleton_iff, (Δ.P true).subset, delete_ground,
    and_iff_right diff_subset]
  exact (Δ.P true).disjoint_false_true.notMem_of_mem_right <| Δ.mem



  -- obtain rfl | rfl := b.eq_or_eq_not c
  -- · obtain rfl : b = false := by simpa using hbc
  --   simp [Δ.inter_false_eq hc]
  -- nth_rw 2 [← c.not_not]
  -- refine Δ.inter_subsingleton hc _ _ (by simp) ?_
  -- have := (Δ.sep (b := c)).nontrivial (by simp) false
  -- rw [← Separation.inter_ground_eq] at this
  -- -- have := (Δ.faithful_delete hc (b := c)).isTutteSeparation_of_induce

  -- #exit
  -- have aux {X} (hX : X ⊆ (M ＼ range Δ.x).E) (b) : X = (X ∩ (Δ.Q b true)) ∪ (X ∩ Δ.Q b false) := sorry
  -- rw [← Δ.Q_inter_eq]
  -- cases c
  -- ·
  -- cases c
  -- · rw [← Δ.Q_inter_eq, Bool.not_false]
  -- rw [← Δ.Q_inter_eq, ← (Δ.Q false).inter_ground_left, ← inter_assoc]
  -- simp_rw [← (Δ.Q true).union_bool_eq c]


  -- suffices aux : (((Δ.P true) !b) ∩ (Δ.P false) !c).Nonempty by
  --   simpa using Δ.inter_subsingleton hc (!b) (!c) (by simpa using hbc) aux
  -- -- rw [← Δ.Q_inter_eq, ← (Δ.Q false).diff_eq_inter_bool _ (Δ.Q true).subset, ← diff_inter_self_eq_diff,
  -- --   diff_nonempty]
  -- -- rw [nonempty_iff_ne_empty]
  -- -- rintro he
  -- cases b
  -- · cases c
  --   · simp
  --   rw [← Δ.Q_inter_eq, Bool.not_false]

  --   refine ((((Δ.sep (b := false)).nontrivial (by simp)) (!c)).diff_singleton_nonempty Δ.g).mono ?_




  -- have hsm := (Δ.Q true).submod_cross (Δ.Q false) false false true true
  -- grw [Bool.not_false, Δ.eConn_Q_eq hc, Δ.eConn_Q_eq hc,
  --   ← (Δ.cross_nontrivial hc).one_le_eConn_of_tutteConnected hc, ENat.add_one_le_add_one_iff,
  --   ← (Δ.cross_induce_faithful hc).eConn_eq_of_delete] at hsm
  -- obtain ⟨rfl | rfl, hss⟩ := Δ.three_connected.exists_subsingleton_of_isTutteSeparation hsm
  -- · simp [induce_apply_of_delete_self _ _ Δ.range_subset_ground, Δ.true_false_triangle.ne₂₃] at hss
  -- rwa [induce_false_true, apply_inter_ground_of_delete, cross_apply_self, Q_apply',
  --   Q_apply', ← diff_inter_distrib_right, sdiff_eq_left.2 (by simp)] at hss






#exit


    -- (by rwa [Δ.delete_delete_eq])  ?_ ?_





-- lemma TriangleDeletePair.nontrivial (T : M.TriangleDeletePair) {b} : (T.P b).Nontrivial := by









-- set_option trace.profiler.useHeartbeats true
-- set_option trace.profiler true in
lemma baz (hM : M.TutteConnected (1 + 1 + 1)) {x : Bool → α}
    (hT : M.IsTriangle {x true, x false, g}) (hcard : 4 ≤ M.E.encard)
    (P : ∀ i, (M ＼ {x i}).Separation) (hPconn : ∀ {b}, (P b).eConn = 1)
    (hmem : ∀ {b}, x (!b) ∈ P b true) (hPsep : ∀ {b}, (P b).IsTutteSeparation)
    (hdd : (M ＼ range x).TutteConnected (1 + 1)) : ∃ K, M.IsTriad K ∧ x true ∈ K := by
  have hTx {b} : M.IsTriangle {x b, x !b, g} := sorry
    -- convert hT using 1
    -- cases b <;> grind
  have hdnt {b} : (M ＼ {x b}).E.Nontrivial := by
    sorry
    -- grw [← (P b).union_eq, ← two_le_encard_iff_nontrivial, encard_union_eq (P b).disjoint_true_false,
    --   ← one_le_encard_iff_nonempty.2 (hPsep.nonempty _),
    --   ← one_le_encard_iff_nonempty.2 (hPsep.nonempty _), one_add_one_eq_two]
  have hxdel {b} : (M ＼ {x b}).TutteConnected (1 + 1) := sorry
    -- hM.deleteElem (by grw [← hcard]; norm_num) (x b)
  have hxncl (b c) : x b ∉ M.closure (P b c) :=
    hM.notMem_closure_of_separation_deleteElem (by simp [hPconn]) hPsep _
  have hPg {b} : g ∈ P b false := by
    rw [← (P b).compl_true, delete_ground, mem_diff, mem_diff_singleton,
      and_iff_right hT.mem_ground₃, and_iff_right hTx.ne₁₃.symm]
    exact fun hg ↦ hxncl b true <| mem_of_mem_of_subset hTx.mem_closure₁ <|
      M.closure_subset_closure <| pair_subset hmem hg
  have hrw {b} : (M ＼ {x b}) ＼ {x !b} = M ＼ range x := sorry
  /- Since `M ＼ {x b}` and `M ＼ {x b, x !b}` are both `2`-connected, and `P b` has connectivity 1,
  `P b` is faithful for the deletion. -/
  have hQP {b} : (P b).Faithful (M ＼ range x) := sorry
  -- by
  --   rw [← hrw (b := b)]
  --   refine (hxdel).faithful_of_tutteConnected_delete (hrw ▸ hdd) _ hPconn.le fun i ↦ ?_
  --   grw [← two_le_encard_iff_nontrivial.2 ((hPsep (b := b)).nontrivial hPconn.symm.le i)]
  --   norm_num
  have hd {b i} : P b i \ range x = P b i \ {x !b} := by
    rw [Bool.range_bool _ b]
    grind [show x b ∉ P b i from notMem_subset (P b).subset (by simp)]

  set Q : Bool → (M ＼ range x).Separation := fun b ↦ (P b).induce _ with hQdef
  have hQi {b i} : Q b i = P b i \ {x !b} := sorry

  have hcl (b) : x b ∈ M.closure (Q (!b) true) := by
    rw [induce_apply_delete_of_delete _ (by simp)]
    refine hQP.mem_closure_delete_of_delete (by simp) (by simpa using @hmem !b) ?_
    refine indep_of_card_lt_girth ?_
    grw [← image_univ, encard_image_le, Bool.univ_eq, encard_pair_le,
      ← three_le_girth_iff.2 (hM.dual.simple hcard)]
    norm_num

  have hQnt {b} : (Q b).Nontrivial := by
    simp_rw [Separation.nontrivial_iff_forall, hQi]
    exact fun i ↦ (hPsep.nontrivial (by grw [hPconn]) i).diff_singleton_nonempty (x !b)

  have hnss (b) : ¬ (Q b true ⊆ P (!b) false) :=

    fun hss ↦ hxncl _ _ <| M.closure_subset_closure hss (hcl _)


  have h_faith : (((Q true).cross (Q false) false false true).induce M).Faithful (M ＼ range x) := by
    refine faithful_of_subset_closure_of_delete _ <| range_subset_iff.2 fun i ↦ ?_
    grw [cross_apply_true_false, Bool.not_false, ← iUnion_bool (s := fun j ↦ Q j true),
      ← subset_iUnion _ (!i)]
    exact hcl i
  sorry
  -- have hntc (b c) : ((Q true).cross (Q false) b c true).Nontrivial := by


#exit


/- the proof for the disconnected case with named elements of the triangle. Prevents some faff.
We also prove a weaker conclusion that implies the stronger one anyway. -/
lemma tutte_triangle_disconnected_case (hM : M.TutteConnected 3) (hT : M.IsTriangle {e,f,g})
    (hdisc : ¬(M ＼ {e,f}).Connected) : ∃ K, M.IsTriad K ∧ e ∈ K := by
  sorry
  -- have hgE' : g ∈ (M ＼ {e,f}).E := ⟨hT.mem_ground₃, by simp [hT.ne₁₃.symm, hT.ne₂₃.symm]⟩
  -- have hne : (M ＼ {e,f}).Nonempty := by rw [← ground_nonempty_iff]; use g
  -- obtain ⟨P, hP0, hPnt⟩ := exists_separation_of_not_connected hdisc
  -- -- let `j` be the side of `P` containing `g`.
  -- obtain ⟨j, hgj⟩ : ∃ j, g ∈ P j := by rwa [← P.iUnion_eq, mem_iUnion] at hgE'
  -- have hconn : (P.induce M j).eConn ≤ 1 := by
  --   grw [Separation.eConn_eq_eLocalConn _ j, induce_apply_of_delete_not,
  --     induce_apply_of_delete_self, eLocalConn_union_left_le,
  --     ← P.eConn_eq_eLocalConn_of_isRestriction (by simp), hP0, zero_add,
  --     show P j ∪ {e,f} = insert f (insert e (P j)) by grind, ← eRelRk_closure_right,
  --     closure_insert_eq_of_mem_closure, eRelRk_closure_right, eRelRk_insert_le]
  --   exact mem_of_mem_of_subset hT.mem_closure₂ <| M.closure_subset_closure <| by grind
  -- rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at hM
  -- have hnotsep : ¬ (P.induce M j).IsTutteSeparation :=
  --   hM.not_isTutteSeparation (P := P.induce M j) (by grw [hconn])
  -- rw [isTutteSeparation_iff_lt_encard (by enat_to_nat!), not_forall] at hnotsep
  -- -- rw [isTutteSeparation_iff_add_one_le_encard (by enat_to_nat!), not_forall] at hnotsep
  -- obtain ⟨i, hi⟩ := hnotsep
  -- grw [hconn, not_lt] at hi
  -- obtain rfl | rfl := (i.eq_or_eq_not j)
  -- · grw [induce_apply_of_delete_self, ← subset_union_right, encard_pair hT.ne₁₂] at hi
  --   simp at hi
  -- rw [induce_apply_of_delete_not, encard_le_one_iff_subsingleton] at hi
  -- obtain ⟨x, hPx⟩ := hi.exists_eq_of_singleton_of_nonempty <| hPnt.nonempty _
  -- have hxE : x ∈ (M ＼ {e, f}).E := by grw [← singleton_subset_iff, ← hPx, P.subset_ground]
  -- obtain ⟨hxE' : x ∈ M.E, hxe : x ≠ e, hxf : x ≠ f⟩ := by simpa using hxE
  -- -- Now we have that `x` is a loop or coloop of `M ＼ {e,f}`.
  -- have hxT : x ∉ ({e, f, g} : Set α) := by
  --   simp only [mem_insert_iff, hxe, hxf, mem_singleton_iff, false_or]
  --   rintro rfl
  --   exact (P.disjoint_bool j).notMem_of_mem_left hgj <| by simp [hPx]
  -- have hcard : 4 ≤ M.E.encard := by
  --   grw [show (4 : ℕ∞) = 3 + 1 from rfl, ← insert_subset hxE' hT.subset_ground,
  --     encard_insert_of_notMem hxT, hT.three_elements]
  -- have hlp : M.Simple := hM.simple hcard
  -- rw [← P.eConn_eq !j, hPx, eConn_singleton_eq_zero_iff hxE,
  --   delete_isLoop_iff, iff_false_intro (M.not_isLoop _), false_and, false_or,
  --   delete_isColoop_iff, diff_diff, union_singleton] at hP0
  -- have hcard : encard {x,e,f} = 3 := by
  --   rw [encard_insert_of_notMem (by simp [hxe, hxf]), encard_pair hT.ne₁₂, two_add_one_eq_three]
  -- refine ⟨{x,e,f}, ⟨?_, hcard⟩, by simp⟩
  -- refine Dep.isCircuit_of_encard_lt_girth_add_one ?_ ?_
  -- · rw [dep_dual_iff, ← nonspanning_compl_iff, nonspanning_iff, and_iff_left diff_subset]
  --   exact fun hsp ↦ hP0.1 <| by simpa [hsp.closure_eq] using hP0.2.1
  -- grw [← hM.dual.girth_ge (by simpa), hcard]
  -- norm_num

lemma tutte_triangle_weak (hM : M.TutteConnected 3) (hT : M.IsTriangle {e,f,g})
    (hcard : 4 ≤ M.E.encard) (he : ¬ (M ＼ {e}).TutteConnected 3)
    (hf : ¬ (M ＼ {f}).TutteConnected 3) : ∃ K, M.IsTriad K ∧ e ∈ K := by
  obtain hdisc | hcon := em' <| (M ＼ {e,f}).Connected
  · exact tutte_triangle_disconnected_case hM hT hdisc
  -- wlog `(M ＼ {e,f})` is connected.
  sorry

/-- The familiar, stronger, form of Tutte's triangle lemma follows from the above. -/
lemma tutte_triangle (hM : M.TutteConnected 3) (hT : M.IsTriangle {e,f,g}) (hcard : 4 ≤ M.E.encard)
    (he : ¬ (M ＼ {e}).TutteConnected 3) (hf : ¬ (M ＼ {f}).TutteConnected 3) :
    ∃ K, M.IsTriad K ∧ e ∈ K ∧ ((f ∈ K ∧ g ∉ K) ∨ (f ∉ K ∧ g ∈ K)) := by
  sorry
  -- obtain ⟨K, hK, heK⟩ := tutte_triangle_weak hM hT hcard he hf
  -- -- If `K = {e,f,g}`, then `M` is `U₂,₄`, and we have some easy bookkeeping to do.
  -- obtain rfl | hne := eq_or_ne {e,f,g} K
  -- · obtain ⟨E, hE4, rfl⟩ := hT.eq_unifOn_two_four_of_isTriad_of_tutteConnected hK hM
  --   obtain ⟨x, hxE : x ∈ E, hxT⟩ : ∃ x ∈ (unifOn E 2).E, x ∉ ({e, f, g} : Set α)
  --   · refine exists_of_ssubset (hT.subset_ground.ssubset_of_ne ?_)
  --     rintro (rfl : {e,f,g} = E)
  --     replace hE4 := hE4.symm.le
  --     grw [encard_insert_le, encard_pair_le] at hE4
  --     norm_num at hE4
  --   have hef := hT.ne₁₂
  --   have heg := hT.ne₁₃
  --   have hfg := hT.ne₂₃
  --   obtain ⟨hxe : x ≠ e, hxf : x ≠ f, hxg : x ≠ g⟩ := by simpa using hxT
  --   refine ⟨{e, f, x}, ?_, by grind⟩
  --   rw [isTriad_iff, encard_insert_of_notMem (by grind), encard_pair hxf.symm,
  --     and_iff_left (by rfl), isCocircuit_def, unifOn_dual_eq' (j := 2) (by enat_to_nat! <;> lia), unifOn_isCircuit_iff, encard_insert_of_notMem (by grind), encard_pair hxf.symm]
  --   grind [hT.mem_ground₁, hT.mem_ground₂]
  -- refine ⟨K, hK, heK, ?_⟩
  -- have hnt := hT.isCircuit.isCocircuit_inter_nontrivial hK.isCocircuit (by use e; simp_all)
  -- obtain ⟨x, ⟨hxT, hxK⟩, hxe⟩ := hnt.exists_ne e
  -- have aux : ¬ (f ∈ K ∧ g ∈ K) :=
  --   fun ⟨hf, hg⟩ ↦ hne <| Finite.eq_of_subset_of_encard_le (by simp) (by grind)
  --   (by rw [hK.three_elements, hT.three_elements])
  -- grind
-- #count_heartbeast! in


  --   sorry

  -- set Q₀ : Bool → Bool → (M ＼ range x).Separation := (Q true).cross (Q false)

  #exit
  /- Because of this faithfulness, we know that `x !b` is spanned by the rest of `P b true`. -/
  have hcl (b) : x (!b) ∈ M.closure ((P b).delete {x !b} true) := by
    refine mem_of_mem_of_subset ((hrw ▸ hQP).mem_closure_of_deleteElem hmem ?_) ?_
    · grw [delete_apply, (delete_isRestriction ..).closure_subset_closure]
    refine fun hcl ↦ hcl.not_connected hdnt <| hxdel.connected' ?_ rfl.le
    exact (ground_nonempty_iff ..).1 hdnt.nonempty
  set Q : Bool → (M ＼ range x).Separation := fun b ↦ ((P b).delete {x !b}).copy hrw
  have hle {b} : Q b ≼ P b := fun i ↦ by simp [Q]
  have hQnt {b} : (Q b).Nontrivial := by
    simp only [Q, Separation.nontrivial_iff_forall, copy_apply, ↓delete_apply]
    exact fun i ↦ (hPsep.nontrivial (by grw [hPconn]) i).diff_singleton_nonempty (x !b)
  have hQdef {b i} : Q b i = ((P b).delete {x !b}) i := rfl
  /- something here -/
  have hnss (b) : ¬ (Q b true ⊆ P (!b) false) :=
    fun hss ↦ hxncl _ _ <| M.closure_subset_closure hss (hcl _)
  have hnss' (b) : ¬ (Q b true ⊆ Q (!b) false) := sorry
    -- fun hss ↦ hxncl _ _ <| M.closure_subset_closure hss (hcl _)

  set Q₀ : (M ＼ range x).Separation := (Q true).cross (Q false) false false true with hQ₀
  set Q₁ : (M ＼ range x).Separation := (Q true).cross (Q false) true true true with hQ₁
  have hsm : Q₀.eConn + Q₁.eConn ≤ (Q true).eConn + (Q false).eConn := submod_cross ..

  /- the union (false) side of `Q₀` spans both `e` and `f`. -/
  have hQcl (b) : x b ∈ M.closure (Q₀ false)
  · rw [← b.not_not]
    refine mem_of_mem_of_subset (hcl _) <| M.closure_subset_closure ?_
    simp only [↓delete_apply, Bool.not_not, hQ₀, cross_apply_true_false, Bool.not_false,
      diff_singleton_subset_iff, Q, copy_apply, ↓delete_apply]
    cases b <;> grind

  /- And therefore adding them back to the false side gives a faithful separation of `M`. -/
  have hQ' : (Q₀.ofDelete false).Faithful (M ＼ range x) :=
    faithful_ofDelete_of_subset_closure Q₀ <| by simpa [pair_subset_iff] using hQcl

  have hQ₁conn : 1 ≤ Q₁.eConn := by
    refine Nontrivial.one_le_eConn_of_connected ?_ ?_
    · grw [← Separation.not_trivial_iff, hQnt.cross_trivial_iff, not_or]
      exact ⟨hnss' true, hnss' false⟩
    refine hdd.connected' ?_ rfl.le
    grw [← ground_nonempty_iff, ← one_le_encard_iff_nonempty]
    sorry

  grw [← hQ₁conn, hQP.eConn_eq_of_le (delete_isRestriction_of_subset _ (by simp)).isMinor hle,
    hQP.eConn_eq_of_le (delete_isRestriction_of_subset _ (by simp)).isMinor hle, hPconn, hPconn,
    ENat.add_one_le_add_one_iff] at hsm


  have hg : P true false ∩ P false false = {g} := by
    obtain ⟨rfl | rfl, hss⟩ := hM.exists_subsingleton_of_isTutteSeparation (P := Q₀.ofDelete false)
      (by grw [hQ'.eConn_ofDelete_eq, hsm])
    · have := hss.anti (s := range x)
      -- simp [hQ₀, ofDelete] at hss


      -- (by grw [hQ'.eConn_ofRemove_eq, ])



-- #exit

-- lemma bar (hM : M.TutteConnected (2 + 1)) {x : Bool → α} (hT : M.IsTriangle {x true, x false, g})
--     (hcard : 4 ≤ M.E.encard) (hd : ∀ i, ¬ (M ＼ {x i}).TutteConnected (2 + 1))
--     (hdd : (M ＼ range x).TutteConnected 2) : ∃ K, M.IsTriad K ∧ x true ∈ K := by
--   -- rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
--   -- define `x` to abstract the common properties of `e` and `f`.
--   -- set x := fun b ↦ bif b then e else f with hx_def
--   have hTx {b} : M.IsTriangle {x b, x !b, g} := by
--     convert hT using 1
--     cases b <;> grind
--   -- have hxsep {b} : ¬ (M ＼ {x b}).TutteConnected (1 + 1 + 1) := by grind
--   -- clear he hf
--   have hxE {b} : x b ∈ M.E := hTx.mem_ground₁
--   have hxne {b} : x b ≠ x !b := hTx.ne₁₂
--   have hxdel {b} : (M ＼ {x b}).TutteConnected (1 + 1) :=
--     hM.deleteElem (by grw [← hcard]; norm_num) (x b)
--   -- have hdel {b} : (M ＼ {x b}) ＼ {x !b} = M ＼ {e,f} := by
--   --   rw [delete_delete, singleton_union]; grind [pair_comm]
--   have hgx {b} : x b ≠ g := hTx.ne₁₃
--   have hclx {b} : x b ∈ M.closure {x !b, g} := hTx.mem_closure₁
--   -- For each `b`, there is an exact `2`-separation of `M ＼ {x b}` with `x !b` on the `true` side.
--   have hdnt {b} : (M ＼ {x b}).E.Nontrivial := by
--     grw [← two_le_encard_iff_nontrivial, delete_ground, ← ENat.add_one_le_add_one_iff,
--       encard_diff_singleton_add_one hxE, ← hcard]
--     norm_num

--   have aux (b : Bool) : ∃ (P : (M ＼ {x b}).Separation), P.eConn = 1 ∧ P.IsTutteSeparation
--       ∧ x (!b) ∈ P true := by
--     obtain ⟨P', hP'conn, hP'⟩ := (hxdel (b := b)).exists_of_not_tutteConnected_add_one (hd b)
--     obtain ht | hf := P'.mem_or_mem (a := x !b) ⟨hxE, hxne.symm⟩
--     · exact ⟨P', by simpa using hP'conn, hP', ht⟩
--     exact ⟨P'.symm, by simpa using hP'conn, by simpa, hf⟩
--   choose P hP using aux
--   have hPconn {b} : (P b).eConn = 1 := (hP b).1
--   have hPsep {b} : (P b).IsTutteSeparation := (hP b).2.1
--   have hPmem {b} : x (!b) ∈ P b true := (hP b).2.2
--   clear hP
--   -- neither side of `P b` spans `x b` in `M`.
--   have hxncl (b c) : x b ∉ M.closure (P b c) :=
--     hM.notMem_closure_of_separation_deleteElem (by simp [hPconn]) hPsep _
--   -- `g` is on the `false` side, since otherwise the `true` side would span `x b`.
--   have hPg {b} : g ∈ P b false := by
--     rw [← (P b).compl_true, delete_ground, mem_diff, mem_diff_singleton,
--       and_iff_right hT.mem_ground₃, and_iff_right hgx.symm]
--     exact fun hg ↦ hxncl b true <| mem_of_mem_of_subset hTx.mem_closure₁ <|
--       M.closure_subset_closure <| pair_subset hPmem hg
--   /- Since `M ＼ {x b}` and `M ＼ {x b, x !b}` are both `2`-connected, and `P b` has connectivity 1,
--   `P b` is faithful for the deletion. -/
--   have hQP {b} : (P b).Faithful (M ＼ {x b} ＼ {x !b}) := by
--     refine hxdel.faithful_of_tutteConnected_delete
--       (by simp [hdel, hconn.tutteConnected_one_add_one]) _ (by simp [hPconn]) fun i ↦ ?_
--     grw [← two_le_encard_iff_nontrivial.2 ((hPsep (b := b)).nontrivial hPconn.symm.le i)]
--     norm_num
--   /- Because of this faithfulness, we know that `x !b` is spanned by the rest of `P b true`. -/
--   have hcl (b) : x (!b) ∈ M.closure ((P b).delete {x !b} true) := by
--     refine mem_of_mem_of_subset (hQP.mem_closure_of_deleteElem hPmem ?_) ?_
--     · refine fun hcl ↦ hcl.not_connected hdnt <| hxdel.connected' ?_ rfl.le
--       exact (ground_nonempty_iff ..).1 hdnt.nonempty
--     grw [delete_apply, (delete_isRestriction ..).closure_subset_closure]
--   /- something here -/
--   have hnss (b) : ¬ (((P b).delete {x !b}) true ⊆ P (!b) false) := by
--     exact fun hss ↦ hxncl _ _ <| M.closure_subset_closure hss (hcl _)

--   set Q : (M ＼ {e, f}).Separation :=
--     (((P false).delete _).copy hdel).cross (((P true).delete _).copy hdel) false false true with hQ

--   /- the union (false) side of `Q` spans both `e` and `f`. -/
--   have hQcl (b) : x b ∈ M.closure (Q false)
--   · rw [← b.not_not]
--     refine mem_of_mem_of_subset (hcl _) <| M.closure_subset_closure ?_
--     simp only [↓delete_apply, hQ, cross_apply_true_false, copy_apply, diff_singleton_subset_iff]
--     cases b <;> grind

--   /- And therefore adding them back to the false side gives a faithful separation of `M`. -/
--   have hQ' : (Q.ofDelete false).Faithful (M ＼ {e, f}) :=
--     faithful_ofDelete_of_subset_closure Q <| pair_subset (hQcl true) (hQcl false)

--   have hg : P true false ∩ P false false = {g} := by
--     have := hM.exists_subsingleton_of_isTutteSeparation (P := Q.ofDelete false)
--       (by grw [hQ'.eConn_ofRemove_eq, ])



-- lemma foo (hM : M.TutteConnected 3) (hT : M.IsTriangle {e,f,g}) (hcard : 4 ≤ M.E.encard)
--     (he : ¬ (M ＼ {e}).TutteConnected 3) (hf : ¬ (M ＼ {f}).TutteConnected 3)
--     (hconn : (M ＼ {e,f}).Connected) : ∃ K, M.IsTriad K ∧ e ∈ K := by
--   rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
--   -- define `x` to abstract the common properties of `e` and `f`.
--   set x := fun b ↦ bif b then e else f with hx_def
--   have hTx {b} : M.IsTriangle {x b, x !b, g} := by convert hT using 1; grind
--   have hxsep {b} : ¬ (M ＼ {x b}).TutteConnected (1 + 1 + 1) := by grind
--   clear he hf
--   have hxE {b} : x b ∈ M.E := by grind [hT.mem_ground₁, hT.mem_ground₂]
--   have hxne {b} : x b ≠ x !b := by grind [hT.ne₁₂]
--   have hxdel {b} : (M ＼ {x b}).TutteConnected (1 + 1) :=
--     hM.deleteElem (by grw [← hcard]; norm_num) (x b)
--   have hdel {b} : (M ＼ {x b}) ＼ {x !b} = M ＼ {e,f} := by
--     rw [delete_delete, singleton_union]; grind [pair_comm]
--   have hgx {b} : x b ≠ g := by grind [hT.ne₁₃, hT.ne₂₃]
--   have hclx {b} : x b ∈ M.closure {x !b, g} := by grind [hT.mem_closure₁, hT.mem_closure₂]
--   -- For each `b`, there is an exact `2`-separation of `M ＼ {x b}` with `x !b` on the `true` side.
--   have hdnt {b} : (M ＼ {x b}).E.Nontrivial := by
--     grw [← two_le_encard_iff_nontrivial, delete_ground, ← ENat.add_one_le_add_one_iff,
--       encard_diff_singleton_add_one hxE, ← hcard]
--     norm_num

--   have aux (b : Bool) : ∃ (P : (M ＼ {x b}).Separation), P.eConn = 1 ∧ P.IsTutteSeparation
--       ∧ x (!b) ∈ P true := by
--     obtain ⟨P', hP'conn, hP'⟩ := (hxdel (b := b)).exists_of_not_tutteConnected_add_one hxsep
--     obtain ht | hf := P'.mem_or_mem (a := x !b) ⟨hxE, hxne.symm⟩
--     · exact ⟨P', by simpa using hP'conn, hP', ht⟩
--     exact ⟨P'.symm, by simpa using hP'conn, by simpa, hf⟩
--   choose P hP using aux
--   have hPconn {b} : (P b).eConn = 1 := (hP b).1
--   have hPsep {b} : (P b).IsTutteSeparation := (hP b).2.1
--   have hPmem {b} : x (!b) ∈ P b true := (hP b).2.2
--   clear hP
--   -- neither side of `P b` spans `x b` in `M`.
--   have hxncl (b c) : x b ∉ M.closure (P b c) :=
--     hM.notMem_closure_of_separation_deleteElem (by simp [hPconn]) hPsep _
--   -- `g` is on the `false` side, since otherwise the `true` side would span `x b`.
--   have hPg {b} : g ∈ P b false := by
--     rw [← (P b).compl_true, delete_ground, mem_diff, mem_diff_singleton,
--       and_iff_right hT.mem_ground₃, and_iff_right hgx.symm]
--     exact fun hg ↦ hxncl b true <| mem_of_mem_of_subset hTx.mem_closure₁ <|
--       M.closure_subset_closure <| pair_subset hPmem hg
--   /- Since `M ＼ {x b}` and `M ＼ {x b, x !b}` are both `2`-connected, and `P b` has connectivity 1,
--   `P b` is faithful for the deletion. -/
--   have hQP {b} : (P b).Faithful (M ＼ {x b} ＼ {x !b}) := by
--     refine hxdel.faithful_of_tutteConnected_delete
--       (by simp [hdel, hconn.tutteConnected_one_add_one]) _ (by simp [hPconn]) fun i ↦ ?_
--     grw [← two_le_encard_iff_nontrivial.2 ((hPsep (b := b)).nontrivial hPconn.symm.le i)]
--     norm_num
--   /- Because of this faithfulness, we know that `x !b` is spanned by the rest of `P b true`. -/
--   have hcl (b) : x (!b) ∈ M.closure ((P b).delete {x !b} true) := by
--     refine mem_of_mem_of_subset (hQP.mem_closure_of_deleteElem hPmem ?_) ?_
--     · refine fun hcl ↦ hcl.not_connected hdnt <| hxdel.connected' ?_ rfl.le
--       exact (ground_nonempty_iff ..).1 hdnt.nonempty
--     grw [delete_apply, (delete_isRestriction ..).closure_subset_closure]
--   /- something here -/
--   have hnss (b) : ¬ (((P b).delete {x !b}) true ⊆ P (!b) false) := by
--     exact fun hss ↦ hxncl _ _ <| M.closure_subset_closure hss (hcl _)

--   set Q : (M ＼ {e, f}).Separation :=
--     (((P false).delete _).copy hdel).cross (((P true).delete _).copy hdel) false false true with hQ

--   /- the union (false) side of `Q` spans both `e` and `f`. -/
--   have hQcl (b) : x b ∈ M.closure (Q false)
--   · rw [← b.not_not]
--     refine mem_of_mem_of_subset (hcl _) <| M.closure_subset_closure ?_
--     simp only [↓delete_apply, hQ, cross_apply_true_false, copy_apply, diff_singleton_subset_iff]
--     cases b <;> grind

--   /- And therefore adding them back to the false side gives a faithful separation of `M`. -/
--   have hQ' : (Q.ofDelete false).Faithful (M ＼ {e, f}) :=
--     faithful_ofDelete_of_subset_closure Q <| pair_subset (hQcl true) (hQcl false)

--   have hg : P true false ∩ P false false = {g} := by
--     have := hM.exists_subsingleton_of_isTutteSeparation (P := Q.ofDelete false)
--       (by grw [hQ'.eConn_ofRemove_eq, ])


--   #exit

--     -- intro hss
--     -- have := M.closure_subset_closure hss (hcl _)
--     -- grind

--     -- grw [((hPsep (b := b)).nontrivial hPconn.symm.le i)]


--     -- rw [← hdel (b := b)]
--     -- refine faithful_of_eConn_induce_ge (by simp [hPconn]) (delete_isMinor ..) ?_
--     -- grw [hPconn, ← Nontrivial.one_le_eConn_of_connected _ (by simpa [hdel])]
--     -- simp_rw [Separation.nontrivial_iff_forall, induce_eq_delete, delete_apply]
--     -- exact fun i ↦ (hPsep.nontrivial (by grw [hPconn]) i).diff_singleton_nonempty (x !b)



--   -- let `Q b` be the separation of `M ＼ {e,f}` obtained by deleting `x !b` from `P b`.
--   set Q := fun b ↦ ((P b).delete {x !b}).copy hdel with hQ_def
--   have hQf {b} : Q b false = P b false := by
--     suffices (x !b) ∉ (P b) false by simpa [Q]
--     exact (P b).disjoint_true_false.notMem_of_mem_left hPmem
--   have hQt {b} : Q b true = P b true \ {x !b} := by simp [hQ_def]
--   have hQnt {b} : (Q b).Nontrivial := by
--     simp only [hQ_def, Separation.nontrivial_iff_forall, copy_apply, ↓delete_apply]
--     exact fun i ↦ (hPsep.nontrivial (by grw [hPconn]) i).diff_singleton_nonempty (x !b)
--   have hQg {b} : g ∈ Q b false := by simp [hQf, hPg]
--   -- `Q b` has connectivity `1` by the connectedness of `M ＼ {e,f}`.
--   have hQconn {b} : (Q b).eConn = 1 := by
--     refine (hQnt.one_le_eConn_of_connected hconn).antisymm' ?_
--     grw [hQ_def, eConn_copy, (P b).eConn_delete_le, hPconn]
--   -- Since `Q b` and `P b` have the same connectivity, the `true` side of `Q b` spans `x !b`.


--   #exit

--   have hcl (b): x (!b) ∈ M.closure (Q b true) := by
--     specialize hQconn (b := b)
--     rw [← hPconn (b := b), hQ_def, eConn_copy,
--       eConn_delete_eq_eConn_iff_of_coindep (by simp [hPconn]) sorry] at hQconn
--     specialize hQconn true
--     rw [inter_eq_self_of_subset_left (by simpa using hPmem)] at hQconn
--     nth_grw 1 [hQt, ← singleton_subset_iff, hQconn,
--       (delete_isRestriction ..).closure_subset_closure]
--   have hnss (b) : ¬ Q b true ⊆ P (!b) false := by
--     intro hss
--     have := M.closure_subset_closure hss (hcl _)
--     grind
--   -- let `Q₀` be the separation with `true` side equal to `Q false ∩ Q false`.
--   -- This has connectivity at most `1` by a submodularity argument.
--   set Q₀ := (Q true).cross (Q false) false false true with hQ₀_def
--   have hQ₀conn : Q₀.eConn ≤ 1 := by
--     have hQu : 1 ≤ ((Q true).cross (Q false) true true false).eConn := by
--       refine Nontrivial.one_le_eConn_of_connected ?_ hconn
--       rw [← Separation.not_trivial_iff, hQnt.cross_trivial_iff, Bool.not_true, not_or, hQf, hQf]
--       exact ⟨hnss true, hnss false⟩
--     have hsm := (Q true).submod_cross (Q false) false false true false
--     grw [Bool.not_false, ← hQu, hQconn, hQconn, ← hQ₀_def, ENat.add_one_le_add_one_iff] at hsm
--     assumption
--   -- `Q₀` also has connectivity equal to `Q₀.ofDelete false`, since its large side spans `{e,f}`.
--   have hQ₀P : (Q₀.ofDelete false).eConn = Q₀.eConn := by
--     refine eConn_ofDelete_eq_of_subset_closure _ _ ?_
--     rw [hQ₀_def, cross_apply_, Bool.not_false, pair_subset_iff]
--     nth_grw 1 [← subset_union_right, ← subset_union_left]
--     exact ⟨hcl false, hcl true⟩
--   -- Since `M` is `3`-connected, this means that the small side of `Q₀` is just `{g}`.
--   have hQg : Q true false ∩ Q false false = {g} := by
--     obtain ⟨rfl | rfl, hi⟩ := hM.exists_subsingleton_of_isTutteSeparation (hQ₀P.trans_le hQ₀conn)
--     · grw [ofDelete_apply_self, ← encard_le_one_iff_subsingleton, ← subset_union_right,
--         encard_pair hT.ne₁₂] at hi
--       simp at hi
--     rw [Q₀.ofDelete_apply, Bool.cond_eq_ite, if_neg (by simp), hQ₀_def,
--       Separation.inter_apply_true] at hi
--     exact hi.eq_singleton_of_mem <| by grind

--   have hsm' := (Q true).eConn_union_add_eConn_union_le (Q false) true false

--   grw [hQconn, hQconn, Bool.not_true, Bool.not_false, ← eConn_ofDelete_eq_of_subset_closure _ true,
--     ← eConn_ofDelete_eq_of_subset_closure _ true] at hsm'
--   · sorry
--   rw [Separation.union_apply_true, pair_subset_iff]

--   -- simp [hQt, hQf]
--   -- have foo (b) : x b ∈ M.closure (P !b)



--   -- set Q₁ := (Q true).inter (Q false) true false with hQ₁_def
--   -- set Q₂ := (Q true).union (Q false) true false with hQ₁_def
--   -- have hQconn' : Q₁.eConn
--   sorry
