import Mathlib.Combinatorics.Matroid.Minor.Order
import Matroid.Connectivity.Triangle

open Set Matroid Function Separation

set_option linter.style.longLine false


namespace Matroid

variable {i : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P Q: M.Separation}

/- the proof for the disconnected case with named elements of the triangle. Prevents some faff.
We also prove a weaker conclusion that implies the stronger one anyway. -/
lemma tutte_triangle_disconnected_case (hM : M.TutteConnected 3) (hT : M.IsTriangle {e,f,g})
    (hdisc : ¬(M ＼ {e,f}).Connected) : ∃ K, M.IsTriad K ∧ e ∈ K := by
  have hgE' : g ∈ (M ＼ {e,f}).E := ⟨hT.mem_ground₃, by simp [hT.ne₁₃.symm, hT.ne₂₃.symm]⟩
  have hne : (M ＼ {e,f}).Nonempty := by rw [← ground_nonempty_iff]; use g
  obtain ⟨P, hP0, hPnt⟩ := exists_separation_of_not_connected hdisc
  -- rw [P.not_trivial_iff] at hPnt
  -- let `j` be the side of `P` containing `g`.
  obtain ⟨j, hgj⟩ : ∃ j, g ∈ P j := by rwa [← P.iUnion_eq, mem_iUnion] at hgE'
  have hconn : (P.ofDelete j).eConn ≤ 1 := by
    grw [Separation.eConn_eq_eLocalConn _ j, ofDelete_apply_self, ofDelete_apply_not,
      show P j ∪ {e,f} = insert f (insert e (P j)) by grind, ← eLocalConn_closure_left,
      closure_insert_eq_of_mem_closure, eLocalConn_closure_left, eLocalConn_insert_left_le,
      ← P.eConn_eq_eLocalConn_of_isRestriction (by simp), hP0, zero_add]
    exact mem_of_mem_of_subset (hT.isCircuit.mem_closure_diff_singleton_of_mem (by simp))
      <| M.closure_subset_closure <| by grind
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at hM
  have hnotsep : ¬ (P.ofDelete j).IsTutteSeparation :=
    hM.not_isTutteSeparation (P := P.ofDelete j) (by grw [hconn])
  rw [isTutteSeparation_iff_lt_encard (by enat_to_nat!), not_forall] at hnotsep
  -- rw [isTutteSeparation_iff_add_one_le_encard (by enat_to_nat!), not_forall] at hnotsep
  obtain ⟨i, hi⟩ := hnotsep
  grw [hconn, not_lt] at hi
  obtain rfl | rfl := (i.eq_or_eq_not j)
  · grw [ofDelete_apply_self, ← encard_le_encard subset_union_right, encard_pair hT.ne₁₂] at hi
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
    grw [show (4 : ℕ∞) = 2 + 1 + 1 from rfl, ← encard_le_encard (s := {x, e, f, g}) (by aesop_mat),
      encard_insert_of_notMem hxT, encard_insert_of_notMem, encard_pair hT.ne₂₃]
    simp [hT.ne₁₂, hT.ne₁₃]
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
    rw [encard_insert_of_notMem (by simp [hxe, hxf]), encard_pair hT.ne₁₂, two_add_one_eq_three]
  refine ⟨{x,e,f}, ⟨?_, hcard⟩, by simp⟩
  refine Dep.isCircuit_of_encard_lt_girth_add_one ?_ ?_
  · rw [dep_dual_iff, ← nonspanning_compl_iff, nonspanning_iff, and_iff_left diff_subset]
    refine fun hsp ↦ hxcl.1 <| by simpa [hsp.closure_eq] using hxcl.2.1
  grw [← hM.dual.girth_ge (by simpa), hcard]
  norm_num

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
  obtain ⟨K, hK, heK⟩ := tutte_triangle_weak hM hT hcard he hf
  -- If `K = {e,f,g}`, then `M` is `U₂,₄`, and we have some easy bookkeeping to do.
  obtain rfl | hne := eq_or_ne {e,f,g} K
  · obtain ⟨E, hE4, rfl⟩ := hT.eq_unifOn_two_four_of_isTriad_of_tutteConnected hK hM
    obtain ⟨x, hxE : x ∈ E, hxT⟩ : ∃ x ∈ (unifOn E 2).E, x ∉ ({e, f, g} : Set α)
    · refine exists_of_ssubset (hT.subset_ground.ssubset_of_ne ?_)
      rintro (rfl : {e,f,g} = E)
      replace hE4 := hE4.symm.le
      grw [encard_insert_le, encard_pair_le] at hE4
      norm_num at hE4
    have hef := hT.ne₁₂
    have heg := hT.ne₁₃
    have hfg := hT.ne₂₃
    obtain ⟨hxe : x ≠ e, hxf : x ≠ f, hxg : x ≠ g⟩ := by simpa using hxT
    refine ⟨{e, f, x}, ?_, by grind⟩
    rw [isTriad_iff, encard_insert_of_notMem (by grind), encard_pair hxf.symm,
      and_iff_left (by rfl), isCocircuit_def, unifOn_dual_eq' (j := 2) (by enat_to_nat! <;> lia), unifOn_isCircuit_iff, encard_insert_of_notMem (by grind), encard_pair hxf.symm]
    grind [hT.mem_ground₁, hT.mem_ground₂]
  refine ⟨K, hK, heK, ?_⟩
  have hnt := hT.isCircuit.isCocircuit_inter_nontrivial hK.isCocircuit (by use e; simp_all)
  obtain ⟨x, ⟨hxT, hxK⟩, hxe⟩ := hnt.exists_ne e
  have aux : ¬ (f ∈ K ∧ g ∈ K) :=
    fun ⟨hf, hg⟩ ↦ hne <| Finite.eq_of_subset_of_encard_le (by simp) (by grind)
    (by rw [hK.three_elements, hT.three_elements])
  grind













lemma foo (hM : M.TutteConnected 3) (hT : M.IsTriangle {e,f,g}) (hcard : 4 ≤ M.E.encard)
    (he : ¬ (M ＼ {e}).TutteConnected 3) (hf : ¬ (M ＼ {f}).TutteConnected 3)
    (hconn : (M ＼ {e,f}).Connected) : ∃ K, M.IsTriad K ∧ e ∈ K := by
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  -- define `x` to abstract the common properties of `e` and `f`.
  set x := fun b ↦ bif b then e else f with hx_def
  have hxsep {b} : ¬ (M ＼ {x b}).TutteConnected (1 + 1 + 1) := by grind
  clear he hf
  have hxE {b} : x b ∈ M.E := by grind [hT.mem_ground₁, hT.mem_ground₂]
  have hxne {b} : x b ≠ x !b := by grind [hT.ne₁₂]
  have hxdel {b} : (M ＼ {x b}).TutteConnected (1 + 1) :=
    hM.deleteElem (by grw [← hcard]; norm_num) (x b)
  have hdel {b} : (M ＼ {x b}) ＼ {x !b} = M ＼ {e,f} := by
    rw [delete_delete, singleton_union]; grind [pair_comm]
  have hgx {b} : x b ≠ g := by grind [hT.ne₁₃, hT.ne₂₃]
  have hclx {b} : x b ∈ M.closure {x !b, g} := by grind [hT.mem_closure₁, hT.mem_closure₂]
  -- For each `b`, there is an exact `2`-separation of `M ＼ {x b}` with `x !b` on the `true` side.
  have aux (b : Bool) : ∃ (P : (M ＼ {x b}).Separation), P.eConn = 1 ∧ P.IsTutteSeparation
      ∧ x (!b) ∈ P true := by
    obtain ⟨P', hP'conn, hP'⟩ :=
      exists_of_tutteConnected_of_not_tutteConnected_add_one (hxdel (b := b)) hxsep
    obtain ht | hf := P'.mem_or_mem (a := x !b) ⟨hxE, hxne.symm⟩
    · exact ⟨P', by simpa using hP'conn, hP', ht⟩
    exact ⟨P'.symm, by simpa using hP'conn, by simpa, hf⟩
  choose P hP using aux
  have hPconn {b} : (P b).eConn = 1 := (hP b).1
  have hPsep {b} : (P b).IsTutteSeparation := (hP b).2.1
  have hPmem {b} : x (!b) ∈ P b true := (hP b).2.2
  clear hP
  -- Neither side of `P b` spans `x b`, since otherwise `P b` would induce a `2`-separation of `M`.
  have hxncl (b c) : x b ∉ M.closure (P b c) := by
    intro hx
    have hConn' : ((P b).ofDelete c).eConn = 1 := by
      rw [eConn_ofDelete_eq_of_subset_closure (P b) c (by simpa), hPconn]
    refine hM.not_isTutteSeparation (P := (P b).ofDelete c) (by simp [hConn']) ?_
    refine isTutteSeparation_of_lt_encard fun i ↦ ?_
    grw [hConn', ← ofDelete_apply_superset, ← hPsep.eConn_add_one_le, hPconn]
    norm_num
  -- and therefore `g` is on the `false` side of `P b`.
  have hPg {b} : g ∈ P b false := by
    obtain ht | hf := (P b).mem_or_mem ⟨hT.mem_ground₃, hgx.symm⟩
    · exfalso
      exact hxncl b true <| mem_of_mem_of_subset hclx <| M.closure_subset_closure <| by grind
    exact hf
  -- let `Q b` be the separation of `M ＼ {e,f}` obtained by deleting `x !b` from `P b`.
  set Q := fun b ↦ ((P b).delete {x !b}).copy hdel with hQ_def
  have hQf {b} : Q b false = P b false := by
    suffices (x !b) ∉ (P b) false by simpa [Q]
    exact (P b).disjoint_true_false.notMem_of_mem_left hPmem
  have hQt {b} : Q b true = P b true \ {x !b} := by simp [hQ_def]
  have hQnt {b} : (Q b).Nontrivial := by
    simp only [hQ_def, Separation.nontrivial_iff_forall, copy_apply, ↓delete_apply]
    exact fun i ↦ (hPsep.nontrivial (by grw [hPconn]) i).diff_singleton_nonempty (x !b)
  have hQg {b} : g ∈ Q b false := by simp [hQf, hPg]
  -- `Q b` has connectivity `1` by the connectedness of `M ＼ {e,f}`.
  have hQconn {b} : (Q b).eConn = 1 := by
    refine (hQnt.one_le_eConn_of_connected hconn).antisymm' ?_
    grw [hQ_def, eConn_copy, (P b).eConn_delete_le, hPconn]
  -- Since `Q b` and `P b` have the same connectivity, the `true` side of `Q b` spans `x !b`.
  have hcl (b): x (!b) ∈ M.closure (Q b true) := by
    specialize hQconn (b := b)
    rw [← hPconn (b := b), hQ_def, eConn_copy,
      eConn_delete_eq_eConn_iff_of_coindep (by simp [hPconn]) sorry] at hQconn
    specialize hQconn true
    rw [inter_eq_self_of_subset_left (by simpa using hPmem)] at hQconn
    nth_grw 1 [hQt, ← singleton_subset_iff, hQconn,
      (delete_isRestriction ..).closure_subset_closure]
  have hnss (b) : ¬ Q b true ⊆ P (!b) false := by
    intro hss
    have := M.closure_subset_closure hss (hcl _)
    grind
  -- let `Q₀` be the separation with `true` side equal to `Q false ∩ Q false`.
  -- This has connectivity at most `1` by a submodularity argument.
  set Q₀ := (Q true).inter (Q false) false false with hQ₀_def
  have hQ₀conn : Q₀.eConn ≤ 1 := by
    have hQu : 1 ≤ ((Q true).union (Q false) false false).eConn := by
      refine Nontrivial.one_le_eConn_of_connected ?_ hconn
      rw [← Separation.not_trivial_iff, hQnt.union_trivial_iff, Bool.not_false, not_or,
        hQf, hQf]
      exact ⟨hnss true, hnss false⟩
    have hsm := (Q true).eConn_inter_add_eConn_union_le (Q false) false false
    grw [← hQu, hQconn, hQconn, ← hQ₀_def, ENat.add_one_le_add_one_iff] at hsm
    assumption
  -- `Q₀` also has connectivity equal to `Q₀.ofDelete false`, since its large side spans `{e,f}`.
  have hQ₀P : (Q₀.ofDelete false).eConn = Q₀.eConn := by
    refine eConn_ofDelete_eq_of_subset_closure _ _ ?_
    rw [hQ₀_def, Separation.inter_apply_false, Bool.not_false, pair_subset_iff]
    nth_grw 1 [← subset_union_right, ← subset_union_left]
    exact ⟨hcl false, hcl true⟩
  -- Since `M` is `3`-connected, this means that the small side of `Q₀` is just `{g}`.
  have hQg : Q true false ∩ Q false false = {g} := by
    obtain ⟨rfl | rfl, hi⟩ := hM.exists_subsingleton_of_isTutteSeparation (hQ₀P.trans_le hQ₀conn)
    · grw [ofDelete_apply_self, ← encard_le_one_iff_subsingleton, ← subset_union_right,
        encard_pair hT.ne₁₂] at hi
      simp at hi
    rw [Q₀.ofDelete_apply, Bool.cond_eq_ite, if_neg (by simp), hQ₀_def,
      Separation.inter_apply_true] at hi
    exact hi.eq_singleton_of_mem <| by grind

  have hsm' := (Q true).eConn_union_add_eConn_union_le (Q false) true false

  grw [hQconn, hQconn, Bool.not_true, Bool.not_false, ← eConn_ofDelete_eq_of_subset_closure _ true,
    ← eConn_ofDelete_eq_of_subset_closure _ true] at hsm'
  · sorry
  rw [Separation.union_apply_true, pair_subset_iff]

  -- simp [hQt, hQf]
  -- have foo (b) : x b ∈ M.closure (P !b)



  -- set Q₁ := (Q true).inter (Q false) true false with hQ₁_def
  -- set Q₂ := (Q true).union (Q false) true false with hQ₁_def
  -- have hQconn' : Q₁.eConn
  sorry
