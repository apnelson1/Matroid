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

/-- An auxiliary structure containing the data in the setting of the triangle lemma,
namely a proof that `M` is a nontrivial three-connected matroid, a triangle `{e, f, g}`,
and `2`-separations of both `M ＼ {e}` and `M ＼ {f}`, whose true sides contain `f` and `e`
respectively.

To preserve the symmetry between `e` and `f`, we encode these elements using a
function `x` from `Bool`, which will have `x true = e` and `x false = f`. -/
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

namespace TriangleDeletePair

protected lemma mem' (Δ : M.TriangleDeletePair) {b} : Δ.x b ∈ Δ.P (!b) true := by
  simpa using Δ.mem (b := !b)

protected lemma triangle (Δ : M.TriangleDeletePair) {b} : M.IsTriangle {Δ.g, Δ.x b, Δ.x (!b)} := by
  cases b
  · exact pair_comm _ _ ▸ Δ.true_false_triangle
  exact Δ.true_false_triangle

@[simp]
protected lemma mem_ground (Δ : M.TriangleDeletePair) {b} : Δ.x b ∈ M.E :=
  Δ.triangle.mem_ground₂

@[simp]
protected lemma notMem (Δ : M.TriangleDeletePair) {b c} : Δ.x b ∉ Δ.P b c :=
  notMem_subset (Δ.P b).subset <| by simp

protected lemma notMem_closure (Δ : M.TriangleDeletePair) (b c) :
    Δ.x b ∉ M.closure (Δ.P b c) :=
  Δ.three_connected.notMem_closure_of_separation_deleteElem (by simpa using Δ.conn_le) Δ.sep c

protected lemma g_mem_ground (Δ : M.TriangleDeletePair) : Δ.g ∈ M.E :=
  Δ.true_false_triangle.mem_ground₁

/-- `g` must be on the `false` side of each separation of `Δ`, since otherwise the `true`
side would span the triangle and we would have a `2`-separation of `M`. -/
protected lemma g_mem_false (Δ : M.TriangleDeletePair) {b} : Δ.g ∈ Δ.P b false := by
  rw [← Separation.compl_true, delete_ground, mem_diff, mem_diff, mem_singleton_iff,
    and_iff_right Δ.g_mem_ground, and_iff_right Δ.triangle.ne₁₂]
  exact fun hmem ↦ Δ.notMem_closure b true <| mem_of_mem_of_subset Δ.triangle.mem_closure₂ <|
    M.closure_subset_closure <| pair_subset hmem Δ.mem

@[simp]
protected lemma encard_range (Δ : M.TriangleDeletePair) : (range Δ.x).encard = 2 := by
  rw [Bool.range_eq, encard_pair Δ.true_false_triangle.ne₂₃.symm]

protected lemma delete_tutteConnected (Δ : M.TriangleDeletePair) {b} :
    (M ＼ {Δ.x b}).TutteConnected (1 + 1) :=
  Δ.three_connected.deleteElem (by grw [← Δ.card_ge]; norm_num) (Δ.x b)

@[simp]
protected lemma range_subset_ground (Δ : M.TriangleDeletePair) : range Δ.x ⊆ M.E := by
  grw [← Δ.true_false_triangle.subset_ground, ← subset_insert, Bool.range_eq, pair_comm]

protected lemma coindep_range (Δ : M.TriangleDeletePair) : M.Coindep (range Δ.x) := by
  refine M✶.indep_of_card_lt_girth ?_ Δ.range_subset_ground
  grw [Δ.encard_range, ← three_le_girth_iff.2 <| Δ.three_connected.dual.simple Δ.card_ge]
  norm_num

protected lemma delete_connected (Δ : M.TriangleDeletePair) {b} : (M ＼ {Δ.x b}).Connected := by
  have hne : (M ＼ {Δ.x b}).Nonempty := ⟨⟨Δ.g, Δ.g_mem_ground, by simpa using Δ.triangle.ne₁₂⟩⟩
  rw [← tutteConnected_two_iff]
  exact Δ.delete_tutteConnected

protected lemma delete_delete_eq (Δ : M.TriangleDeletePair) {b} :
    (M ＼ {Δ.x b} ＼ {Δ.x !b}) = M ＼ range Δ.x := by
  rw [Bool.range_bool _ b, delete_delete, singleton_union]

/-- `Q b` is the separation of `M ＼ {e, f}` induced by `P b`. -/
protected def Q (Δ : M.TriangleDeletePair) (b : Bool) : (M ＼ range Δ.x).Separation :=
  (Δ.P b).induce _

protected lemma Q_apply' (Δ : M.TriangleDeletePair) {b i} : Δ.Q b i = Δ.P b i \ range Δ.x := by
  rw [TriangleDeletePair.Q, induce_apply_delete_of_delete _ (by simp)]

protected lemma Q_apply (Δ : M.TriangleDeletePair) {b i} : Δ.Q b i = Δ.P b i \ {Δ.x (!b)} := by
  rw [Δ.Q_apply', Bool.range_bool _ b, ← union_singleton, ← diff_diff, sdiff_eq_left.2 (by simp)]

protected lemma g_mem_false_Q (Δ : M.TriangleDeletePair) {b} : Δ.g ∈ Δ.Q b false := by
  rw [Δ.Q_apply, mem_diff_singleton, and_iff_right Δ.g_mem_false]
  exact Δ.triangle.ne₁₃

protected lemma P_nontrivial (Δ : M.TriangleDeletePair) {b} : (Δ.P b).Nontrivial := by
  simp_rw [Separation.nontrivial_iff_forall, Bool.forall_bool]
  exact ⟨⟨Δ.g, Δ.g_mem_false⟩, ⟨Δ.x !b, Δ.mem⟩⟩

@[simp]
protected lemma eConn_eq (Δ : M.TriangleDeletePair) {b} : (Δ.P b).eConn = 1 :=
  Δ.conn_le.antisymm <| ENat.one_le_iff_ne_zero.2 fun h0 ↦
    (Δ.delete_connected.trivial_of_eConn_eq_zero h0).not_nontrivial Δ.P_nontrivial

protected lemma P_apply_nontrivial (Δ : M.TriangleDeletePair) {b i} : (Δ.P b i).Nontrivial :=
  (Δ.sep.nontrivial (P := Δ.P b) (by simp) i)

protected lemma Q_nontrivial (Δ : M.TriangleDeletePair) {b} : (Δ.Q b).Nontrivial := by
  simp_rw [Separation.nontrivial_iff_forall, Δ.Q_apply]
  exact fun i ↦ Δ.P_apply_nontrivial.diff_singleton_nonempty _

protected lemma Q_inter_eq (Δ : M.TriangleDeletePair) (i j) :
    Δ.Q true i ∩ Δ.Q false j = Δ.P true i ∩ Δ.P false j := by
  rw [Δ.Q_apply', Δ.Q_apply', diff_inter_diff_right, sdiff_eq_left.2 (by simp)]

/-- For the next few lemmas, we assume that `M ＼ {e,f}` is connected.
We first show that each `P b` is faithful to `M ＼ {e,f}`, since otherwise its connectivity
would drop from `1` to `0` on deletion, contradicting connectedness of `M ＼ {e,f}`. -/
protected lemma faithful_delete (Δ : M.TriangleDeletePair) (hc : (M ＼ range Δ.x).TutteConnected 2)
    {b} : (Δ.P b).Faithful (M ＼ range Δ.x) := by
  rw [← Δ.delete_delete_eq (b := b)]
  refine (Δ.delete_connected.tutteConnected_one_add_one).faithful_of_tutteConnected_delete
    (by rwa [Δ.delete_delete_eq]) (Δ.P b) (by simp) fun i ↦ ?_
  rw [one_lt_encard_iff_nontrivial]
  exact Δ.P_apply_nontrivial

/-- Therefore `x b` is spanned by the `true` side of `Q !b`. -/
protected lemma mem_closure (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) {b} : Δ.x b ∈ M.closure (Δ.Q (!b) true) := by
  rw [Δ.Q_apply']
  exact (Δ.faithful_delete hc).mem_closure_delete_of_delete (by simp) Δ.mem' Δ.coindep_range

/-- Since `Q true false` does not span `x true`, but `Q false true` does,
the set `Q true true ∩ Q false true` is nonempty.  -/
protected lemma inter_true_true_nonempty (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) : (Δ.P true true ∩ Δ.P false true).Nonempty := by
  rw [← Δ.Q_inter_eq]
  by_contra! hcon
  have hss : Δ.Q false true ⊆ Δ.Q true false := by
    grind [(Δ.Q true).union_inter_right (Δ.Q false true) (Δ.Q false).subset true]
  have h1 := Δ.mem_closure hc (b := true)
  grw [Bool.not_true, hss, Δ.Q_apply, diff_subset] at h1
  exact Δ.notMem_closure true false h1

/-- Using the fact that `Q b false` always contains `g`, and `Q b true` always spans `x !b`,
we can conclude that `Q true b ∪ Q false c` always spans both `x true` and `x false`,
unless `b` and `c` are both true.

This implies that the separation of `M ＼ {e,f}` with one side `Q true b ∪ Q false c`
induces a separation of `M` with the same connectivity that it has in `M ＼ {e,f}`. -/
protected lemma cross_induce_faithful (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) {b c : Bool} (hbc : (b && c) = false) {d} :
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

protected lemma eConn_Q_eq (Δ : M.TriangleDeletePair) (hc : (M ＼ range Δ.x).TutteConnected 2) {b} :
    (Δ.Q b).eConn = 1 := by
  convert (Δ.faithful_delete hc (b := b)).eConn_induce_eq using 1
  simp

/-- By an uncrossing argument with submodularity, it follows that if `b` or `c` is `true`
and `P true b ∩ P false c` is nonempty, then the opposite intersection `P true !b ∩ P false !b`
is small. -/
protected lemma inter_subsingleton (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) (b c : Bool) (hbc : b || c)
    (hcc' : (Δ.P true b ∩ Δ.P false c).Nonempty) :
    ((Δ.P true (!b)) ∩ (Δ.P false (!c))).Subsingleton := by
  have hsm := (Δ.Q true).submod_cross (Δ.Q false) (!b) (!c) false true
  grw [Δ.eConn_Q_eq hc, Δ.eConn_Q_eq hc, add_comm, ← Nontrivial.one_le_eConn_of_tutteConnected _ hc,
    add_comm, ENat.add_one_le_add_one_iff] at hsm
  · rw [← (Δ.cross_induce_faithful hc (by grind)).eConn_eq_of_delete] at hsm
    obtain ⟨(rfl | rfl), hss⟩ := Δ.three_connected.exists_subsingleton_of_isTutteSeparation hsm
    · rwa [Bool.not_false, induce_true_false, apply_inter_ground_of_delete, cross_apply_self,
        Δ.Q_inter_eq] at hss
    simp [induce_apply_of_delete_self _ _ Δ.range_subset_ground, Δ.true_false_triangle.ne₂₃] at hss
  grw [Separation.nontrivial_iff_forall, Bool.forall_bool, cross_apply_true_false, Bool.not_not,
    Bool.not_not, cross_apply_self, Bool.not_not, Bool.not_not, Δ.Q_inter_eq, and_iff_left hcc']
  exact (Δ.Q_nontrivial.nonempty _).mono subset_union_left

/-- Now by reasoning about cardinalities, we can prove that `Δ P true` has a side with at most
two elements. -/
protected lemma exists_encard_le_two (Δ : M.TriangleDeletePair)
    (hc : (M ＼ range Δ.x).TutteConnected 2) : ∃ i, (Δ.P true i).encard ≤ 2 := by
  have hss0 := Δ.inter_subsingleton hc _ _ (by decide) (Δ.inter_true_true_nonempty hc)
  simp only [Bool.not_true] at hss0
  by_contra! hcon
  have hcon1 := hcon false
  grw [← encard_diff_add_encard_inter (t := Δ.P false false),
    encard_le_one_iff_subsingleton.2 hss0, (Δ.P false).diff_eq_inter_bool _ _] at hcon1
  · replace hcon1 := Order.add_one_le_of_lt hcon1
    rw [ENat.add_one_le_add_one_iff, two_le_encard_iff_nontrivial, Bool.not_false] at hcon1
    obtain h_emp : (Δ.P true true ∩ Δ.P false false) = ∅ := by
      by_contra! hcon
      exact (Δ.inter_subsingleton hc _ _ (by decide) hcon).not_nontrivial <| by simpa
    have h' := (Δ.Q true).union_inter_right (X := Δ.Q false false) (Separation.subset _) false
    rw [Bool.not_false, Δ.Q_inter_eq, Δ.Q_inter_eq, h_emp, union_empty, Δ.Q_apply,
      sdiff_eq_left.2] at h'
    · exact Δ.P_apply_nontrivial.not_subsingleton <| h' ▸ hss0
    simp [← Separation.compl_true, show Δ.x true ∈ Δ.P false true from Δ.mem' (b := true)]
  nth_grw 1 [delete_ground, subset_diff_singleton_iff, (Δ.P true).subset, delete_ground,
    and_iff_right diff_subset]
  exact (Δ.P true).disjoint_false_true.notMem_of_mem_right <| Δ.mem

/-- Meanwhile, if `M ＼ {e, f}` is disconnected with a separation `R`, then adding `e` and `f`
to the side containing `g` gives a separation with connectivity at most `1` in `M`.  -/
protected lemma eConn_le_one (Δ : M.TriangleDeletePair) (R : (M ＼ range Δ.x).Separation)
    (hR : R.eConn = 0) (hgR : Δ.g ∈ R false) : (R.induce M).eConn ≤ 1 := by
  grw [Separation.eConn_eq_eLocalConn _ false, induce_apply_of_delete_self,
    induce_apply_not, apply_inter_ground_of_delete, Bool.not_false,
    eLocalConn_union_left_le, ← Bool.not_false, ← R.eConn_eq_eLocalConn_of_isRestriction (by simp),
    hR, zero_add, union_comm, ← eRelRk_eq_union_right,
    M.eRelRk_mono_left (X := {Δ.g}) (Y := range Δ.x) (by simpa),
    eRelRk_eq_eRelRk_union, IsTriangle.eRelRk _ (by simp)]
  rw [union_comm, Bool.range_eq, singleton_union]
  exact Δ.triangle

/-- Since this is not a Tutte separation of `M`, the side not containing `g` is tiny.  -/
protected lemma subsingleton_true (Δ : M.TriangleDeletePair) (R : (M ＼ range Δ.x).Separation)
    (hR : R.eConn = 0) (hgR : Δ.g ∈ R false) : (R true).Subsingleton := by
  have hconn := Δ.eConn_le_one R hR hgR
  have hnt := Δ.three_connected.not_isTutteSeparation (by simpa using hconn)
  grw [isTutteSeparation_iff_lt_encard (by enat_to_nat!), not_forall, Bool.exists_bool,
    not_lt, not_lt, induce_false_true, induce_apply_of_delete_self, hconn,
    apply_inter_ground_of_delete, ← subset_union_right, Δ.encard_range,
    or_iff_right (by simp), encard_le_one_iff_subsingleton] at hnt
  assumption

/-- In both cases, we have a set `D` equal to `{e}` or `{e,f}`,
and a Tutte separation `R` of `M ＼ D` with a very small side `R i` (that is, `|R i| + |D| ≤ 3`).
This gives that `R i ∪ D` is a triad containing `e`. -/
protected lemma exists_triad_mem (Δ : M.TriangleDeletePair) : ∃ K, M.IsTriad K ∧ Δ.x true ∈ K := by
  by_cases hc : (M ＼ range Δ.x).TutteConnected (1 + 1)
  · obtain ⟨i, hi⟩ := Δ.exists_encard_le_two hc
    have ht := Δ.three_connected.union_isTriad_of_separation_delete (P := Δ.P true) Δ.card_ge Δ.sep
      (i := i) (by simp) (by simp) (by simpa [show (3 : ℕ∞) = 2 + 1 from rfl])
    exact ⟨_, ht, by simp⟩
  rw [not_tutteConnected_iff_exists_mem (e := Δ.g) (i := false)
    (by simp [Δ.g_mem_ground, Δ.true_false_triangle.ne₁₂, Δ.true_false_triangle.ne₁₃])] at hc
  obtain ⟨R, hR, hRsep, hgR⟩ := hc
  have hss := Δ.subsingleton_true R (by simpa using hR) hgR
  obtain ⟨y, hy⟩ := hss.exists_eq_of_singleton_of_nonempty (hRsep.nonempty _)
  refine ⟨{y} ∪ (range Δ.x), ?_, by simp⟩
  refine hy ▸ Δ.three_connected.union_isTriad_of_separation_delete Δ.card_ge hRsep
    Δ.range_subset_ground (by simp) ?_
  grw [encard_le_one_iff_subsingleton.2 hss, Δ.encard_range, show (1 : ℕ∞) + 2 = 3 from rfl]

end TriangleDeletePair

lemma tutte_triangle_weak (hM : M.TutteConnected 3) (hT : M.IsTriangle {e,f,g})
    (hcard : 4 ≤ M.E.encard) (he : ¬ (M ＼ {e}).TutteConnected 3)
    (hf : ¬ (M ＼ {f}).TutteConnected 3) : ∃ K, M.IsTriad K ∧ e ∈ K := by
  suffices aux : ∃ Δ : M.TriangleDeletePair, Δ.x true = e
  · obtain ⟨Δ, rfl⟩ := aux
    exact Δ.exists_triad_mem
  let x := fun i ↦ bif i then e else f
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  have hsep (i) : ∃ (P : (M ＼ {x i}).Separation),
       P.eConn ≤ 1 ∧ P.IsTutteSeparation ∧ x (!i) ∈ P true := by
    cases i
    · rw [not_tutteConnected_iff_exists_mem (e := e) (by simp [hT.ne₁₂, hT.mem_ground₁]) true] at hf
      simpa using hf
    rw [not_tutteConnected_iff_exists_mem (e := f)
      (by simp [hT.ne₁₂.symm, hT.mem_ground₂]) true] at he
    simpa using he
  choose P hP using hsep
  exact ⟨⟨hcard, hM, fun i ↦ bif i then e else f, g, P, @fun _ ↦ (hP _).2.1, @fun _ ↦ (hP _).1,
    @fun _ ↦ (hP _).2.2, by convert hT using 1; grind⟩, rfl⟩

/-- If `{e, f, g}` is a triangle in a `3`-connected matroid `M` with at least four elements,
and neither `M ＼ {e}` nor `M ＼ {f}` is connected, then `M` has a triad containing `e` and
exactly one of `f` and `g`. -/
theorem tutte_triangle (hM : M.TutteConnected 3) (hT : M.IsTriangle {e, f, g})
    (hcard : 4 ≤ M.E.encard) (he : ¬ (M ＼ {e}).TutteConnected 3)
    (hf : ¬ (M ＼ {f}).TutteConnected 3) :
    ∃ K, M.IsTriad K ∧ e ∈ K ∧ ((f ∈ K ∧ g ∉ K) ∨ (f ∉ K ∧ g ∈ K)) := by
  obtain ⟨K, hK, heK⟩ := tutte_triangle_weak hM hT hcard he hf
  -- If `K = {e,f,g}`, then `M` is `U₂,₄`, and we have some easy bookkeeping to do.
  obtain rfl | hne := eq_or_ne {e, f, g} K
  · have hfin := hT.isFiniteUniform_two_four_of_isTriad hK hM
    simp only [IsTriad, hfin.dual_eq_self, isTriangle_iff, hfin.isCircuit_iff,
      show (2 : ℕ) + (1 : ℕ∞) = 3 from rfl, encard_eq_three]
    obtain ⟨x, hxE, hxe, hxf, hxg⟩ : ∃ x ∈ M.E, x ≠ e ∧ x ≠ f ∧ x ≠ g := by
      suffices M.E ≠ {e, f, g} by grind [hK.subset_ground]
      apply_fun encard
      simp [hK.three_elements, hfin.encard_eq]
    use ({e, f, x} : Set α)
    grind
  refine ⟨K, hK, heK, ?_⟩
  have hnt := hT.isCircuit.isCocircuit_inter_nontrivial hK.isCocircuit (by use e; simp_all)
  obtain ⟨x, ⟨hxT, hxK⟩, hxe⟩ := hnt.exists_ne e
  have aux : ¬ (f ∈ K ∧ g ∈ K) :=
    fun ⟨hf, hg⟩ ↦ hne <| Finite.eq_of_subset_of_encard_le (by simp) (by grind)
    (by rw [hK.three_elements, hT.three_elements])
  grind
