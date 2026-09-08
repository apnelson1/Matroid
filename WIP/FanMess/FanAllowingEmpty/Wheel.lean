module

public import Matroid.Graphic
public import Matroid.Graph.Constructions.Sum
public import Matroid.Graph.Constructions.Cycle
public import Matroid.Graph.Connected.Ear
public import Matroid.Connectivity.Fan.Cyclic


@[expose] public section

variable {α β : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α} {G : Graph α β}



open Set Option WList Function

namespace Graph

/-- The wheel graph, with rim edges of the form `(i, true)` and spoke edges of the form
`(i : false)`, for `i : Fin n`.  -/
def wheel (n : ℕ) : Graph (Option (Fin n)) (Fin n × Bool) :=
  (Graph.cycle n).apex.edgeMap (fun x ↦ ⟨x.elim id id, x.isLeft⟩)

@[simp]
lemma wheel_vertexSet (n : ℕ) : V(wheel n) = univ := by simp [wheel]

@[simp]
lemma wheel_edgeSet (n : ℕ) : E(wheel n) = univ := by
  ext ⟨x, i⟩
  simp [wheel]

lemma wheel_connGE (n : ℕ) : (wheel n).ConnGE (min n 3) := by
  obtain rfl | rfl | n := n
  · simp
  · simp [wheel, apex_connected]
  rw [show min (n + 1 + 1) 3 = (min (n + 1) 2) + 1 by lia, wheel, connGE_edgeMap_iff]
  refine ConnGE.apex ?_ ⟨0, by simp, 1, by simp, by simp⟩
  obtain rfl | n := n
  · simp [(cycle_isCycle ..).connected]
  simp only [le_add_iff_nonneg_left, zero_le, inf_of_le_right]
  exact (cycle_isCycle ..).connGE_two <| by simp [add_assoc]

lemma wheel_isCyclicWalk_triangle [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (wheel n).IsCyclicWalk <| WList.zip
    [none, some i, some (i + 1), none] ([(i, false), (i, true), (i + 1, false)]) := by
  have hnz := i.neZero
  have hnz' : NeZero (List.finRange n).length := by simpa
  have hC : (cycle n).IsPath (cons i i (nil (i + 1))) := by simp [show n ≠ 1 by lia]
  simpa [wheel] using (hC.isCyclicWalk_apex (by simp)).edgeMap
    (fun (x : Fin n ⊕ Fin n) ↦ ((x.elim id id, x.isLeft) : Fin n × Bool)) (by simp [InjOn])

lemma wheel_isCycleSet [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (wheel n).IsCycleSet {(i, false), (i, true), (i + 1, false)} := by
  simpa using (wheel_isCyclicWalk_triangle hn i).isCycleSet_edgeSet

lemma wheel_isBond_triple {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (wheel n).IsBond {(i, true), (i + 1, false), (i + 1, true)} := by
  rw! [wheel, isBond_edgeMap_iff' (by simp [Injective]) (by simp [insert_subset_iff])]
  convert (cycle n).apex_isBond_setLinkEdges_singleton (x := i + 1) (by simp)
  have : (cycle n).apex.Loopless := by
    simpa [apex_loopless_iff, cycle_eq_circuitOn, circuitOn_loopless_iff, List.nodup_finRange]
  rw [setLinkEdges_singleton_compl_eq_incEdges]
  ext (x | x)
  · simp [apex_inc_eq_match, or_comm]
  simp [apex_inc_eq_match, eq_comm]

lemma wheel_isCycleSet_true {n : ℕ} [NeZero n] : (wheel n).IsCycleSet {e | e.2 = true} := by
  obtain ⟨C, hC, hC_eq⟩ := (cycle_isCycle n).exists_isCyclicWalk_eq
  replace hC := hC.isCyclicWalk_apex.edgeMap
    (fun (x : Fin n ⊕ Fin n) ↦ ((x.elim id id, x.isLeft) : Fin n × Bool)) (by simp [InjOn])
  convert hC.isCycleSet_edgeSet
  · rfl
  simp only [edgeedgeSet_map, WList.edgeSet_map,
    show E(C) = univ by simpa using congr_arg Graph.edgeSet hC_eq, image_univ]
  ext ⟨x, b⟩
  simp

lemma wheel_isBond_false {n : ℕ} [NeZero n] : (wheel n).IsBond {e | e.2 = false} := by
  rw [wheel, isBond_edgeMap_iff' (by simp [Injective]) (by simp [Set.subset_def]),
    preimage_ofPred_eq]
  convert PreconnGE.isBond_setLinkEdges_singleton (v := none) ?_ ?_ ?_
  · simp [Set.ext_iff, Option.exists, mem_setLinkEdges_iff]
  · exact PreconnGE.apex <| by simpa using (cycle_isCycle n).connected.pre
  · simp
  simp [show _root_.Nontrivial (Option (Fin n)) by infer_instance]

end Graph

namespace Matroid

/-- The wheel matroid with ground set `Fin n × Bool`. -/
protected def wheel (n : ℕ) : Matroid (Fin n × Bool) := (Graph.wheel n).cycleMatroid

lemma wheel_isTriangle [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (Matroid.wheel n).IsTriangle {(i, false), (i, true), (i + 1, false)} := by
  rw [isTriangle_iff, Matroid.wheel, Graph.cycleMatroid_isCircuit,
    and_iff_right (Graph.wheel_isCycleSet hn i),
    encard_insert_of_notMem (by simp [show n ≠ 1 by lia]), encard_pair (by simp),
    show (2 : ℕ∞) + 1 = 3 from rfl]

lemma wheel_isTriad [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (Matroid.wheel n).IsTriad {(i, true), (i + 1, false), (i + 1, true)} := by
  rw [Matroid.wheel, isTriad_iff, Graph.cycleMatroid_cocircuit, and_iff_right
    (Graph.wheel_isBond_triple hn i),
    encard_insert_of_notMem (by simp [show n ≠ 1 by lia]), encard_pair (by simp),
    show (2 : ℕ∞) + 1 = 3 from rfl]

def wheelFanEquiv : Fin n × Bool ≃ Fin (n * 2) :=
    ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm)).trans finProdFinEquiv

@[simp]
lemma wheelFanEquiv_apply_val (x : Fin n × Bool) : (wheelFanEquiv x).val = 2 * x.1 + x.2.toNat := by
  obtain ⟨x, rfl | rfl⟩ := x <;>
  simp [wheelFanEquiv, finTwoEquiv, add_comm]

@[simp]
lemma wheelFanEquiv_symm_apply_left (x : Fin (n * 2)) : (wheelFanEquiv.symm x).1.1 = x.1.div2 := by
  simp [wheelFanEquiv, Nat.div2]

@[simp]
lemma wheelFanEquiv_symm_apply_right (x : Fin (n * 2)) : (wheelFanEquiv.symm x).2 = x.1.bodd := by
  simp [wheelFanEquiv, Nat.mod_bodd]

lemma wheelFanEquiv_symm_apply (x : Fin (n * 2)) :
    wheelFanEquiv.symm x = ⟨⟨x.1.div2, by grind⟩, x.1.bodd⟩ := by
  ext <;> simp

open Fin.NatCast in
lemma wheelFanEquiv_add_one (x : Fin n × Bool) [NeZero n] :
    wheelFanEquiv x + 1 = wheelFanEquiv (x.1 + (x.2.toNat : Fin n), !x.2) := by
  obtain ⟨⟨x, hx⟩, rfl | rfl⟩ := x
  · simp [← Fin.val_inj, Fin.val_add, Nat.mod_eq_of_lt (show 2 * x + 1 < n * 2 by lia)]
  simp [← Fin.val_inj, Fin.val_add, show 2 * x + 1 + 1 = (x + 1) * 2 by lia,
    Nat.mul_mod_mul_right, mul_comm ((x + 1) % n)]

lemma wheelFanEquiv_add_two (x : Fin n × Bool) [NeZero n] :
    wheelFanEquiv x + 2 = wheelFanEquiv (x.1 + 1, x.2) := by
  rw [← Fin.one_add_one, ← add_assoc, wheelFanEquiv_add_one, wheelFanEquiv_add_one]
  obtain ⟨x, rfl | rfl⟩ := x <;>
  simp [← Fin.val_inj]

lemma wheelFanEquiv_image_eq {n : ℕ} {b : Bool} :
    wheelFanEquiv (n := n) '' {e | e.2 = b} = Fin.val ⁻¹' {i | i.bodd = b} := by
  ext ⟨x, hx⟩
  simp only [mem_image_equiv, mem_ofPred_eq, preimage_ofPred_eq]
  convert Iff.rfl
  simp [wheelFanEquiv, Nat.mod_bodd]

open Fin.NatCast in
lemma wheel_isCyclicFan' (hn : n ≠ 0) :
    (Matroid.wheel n).IsCyclicFan ((List.finRange (n * 2)).map wheelFanEquiv.symm) false := by
  obtain rfl | hne := eq_or_ne n 1
  · have hbond : (Graph.wheel 1).IsBond {(0, false)} := by
      convert Graph.wheel_isBond_false (n := 1); simp [Set.ext_iff]
    have hcyc : (Graph.wheel 1).IsCycleSet {(0, true)} := by
      convert Graph.wheel_isCycleSet_true (n := 1); simp [Set.ext_iff]
    suffices (Matroid.wheel 1).IsCyclicFan [(0, false), (0, true)] false by
      simpa [wheelFanEquiv_symm_apply 0, wheelFanEquiv_symm_apply 1]
    rw [isCyclicFan_two_iff rfl, and_iff_right (by simp)]
    simp [← singleton_isCircuit, ← isCocircuit_def, Matroid.wheel, hbond, hcyc]
  have hnzn : Fact (1 < n) := ⟨by lia⟩
  refine isCyclicFan_of_forall_get (by grind) ?_ fun i ↦ ?_
  · rw [List.nodup_map_iff_of_injOn (by simp)]
    exact List.nodup_finRange ..
  simp_rw [finRotate_apply, add_assoc, Fin.one_add_one, Bool.false_bne]
  set p := wheelFanEquiv.symm <| i.cast (show _ = n * 2 by simp)
  have hip : i.1.bodd = p.2 := by simp [p]
  have hip' : i = (wheelFanEquiv p).cast (by simp) := by simp [p]
  simp_rw [List.get_map, List.get_finRange, Fin.cast_add,  hip', Fin.cast_cast, Fin.cast_refl,
    id_eq, Fin.cast_one, Fin.cast_ofNat, wheelFanEquiv_add_one, wheelFanEquiv_add_two,
    Equiv.symm_apply_apply]
  obtain ht | hf := p.2.eq_false_or_eq_true
  · convert (wheel_isTriad (by lia) p.1).isCircuit using 3 <;>
    simp [ht]
  convert (wheel_isTriangle (by lia) p.1).isCircuit using 3 <;>
  simp [hf]

lemma wheel_isCyclicFan (hn : n ≠ 0) : ∃ (F : List (Fin n × Bool)) (hF : F.length = 2 * n),
    (Matroid.wheel n).IsCyclicFan F false ∧ {e | e ∈ F} = univ ∧
      (∀ (i : Fin n) (b : Bool), F[2 * i + b.toNat] = (i, b)) ∧
      (∀ i (hi : i < F.length), F[i] = (⟨i.div2, by grind⟩, i.bodd)) := by
  have hF := wheel_isCyclicFan' hn
  refine ⟨_, by simp [mul_comm], hF, by simp [Equiv.symm_apply_eq], fun i b ↦ ?_, fun i hi ↦ ?_⟩
  · ext <;> cases b with simp
  lift i to Fin (n * 2) using (by simpa using hi)
  simp [Prod.ext_iff, ← Fin.val_inj]

lemma wheel_connected (hn : 2 ≤ n) : (Matroid.wheel n).Connected := by
  obtain ⟨F, -, hF, hfU, -, -⟩ := wheel_isCyclicFan (show n ≠ 0 by lia)
  rw [← hF.setOf_eq_ground_iff, hfU]
  · simp [Matroid.wheel]
  intro h2
  have hcon : 2 = (n : ℕ∞) * 2 := by
    simpa [hF.isFan.nodup.encard_toSet_eq, h2] using congr_arg encard hfU
  enat_to_nat
  lia

/-- This statement is designed to exactly fit the API for cyclic fans. -/
lemma wheel_tutteConnected (hn : 2 < (Matroid.wheel n).E.encard) :
    (Matroid.wheel n).TutteConnected 2 := by
  have h2 : 2 < (n : ℕ∞) * 2 := by simpa [Matroid.wheel] using hn
  exact (wheel_connected (by enat_to_nat! <;> lia)).tutteConnected_two

lemma wheel_isCircuitHyperplane (hn : n ≠ 0) :
    (Matroid.wheel n).IsCircuitHyperplane {e | e.2 = true} := by
  have hwin := @Graph.wheel_isCycleSet_true (n := n) ⟨hn⟩
  obtain hlt | hn2 := lt_or_ge n 2
  · obtain rfl : n = 1 := by lia
    refine ⟨?_, ?_⟩
    · rwa [Matroid.wheel, Graph.cycleMatroid_isCircuit]
    rw [Matroid.wheel, ← isCocircuit_compl_iff_isHyperplane (by simp),
       Graph.cycleMatroid_cocircuit, Graph.cycleMatroid_E, Graph.wheel_edgeSet,
       show (univ : Set (Fin 1 × Bool)) \ {e | e.2 = true} = {(0, false)} by
       (ext ⟨e, i⟩; simp [e.fin_one_eq_zero])]
    rw [Graph.wheel, Graph.isBond_edgeMap_iff' (by simp [Injective]) (by simp [subset_def])]
    convert (Graph.cycle 1).apex_isBond_setLinkEdges_singleton (x := 0) (by simp)
    ext (x | x) <;>
    simp [Graph.mem_setLinkEdges_iff]
  obtain ⟨F, hFn, hF, hFuniv, hFi, hFinv⟩ := (wheel_isCyclicFan (n := n) (by simpa))
  have hrw :  (F.get '' {i | i.1.bodd = !false}) = {e | e.2 = true} := by
    ext ⟨i, b⟩
    grind [hF.isFan.getElem_inj_iff, Fin.exists_iff]
  obtain hch | hb := hF.isCircuitHyperplane_or_isBase_cojoints wheel_tutteConnected
  · rwa [← hrw]
  refine False.elim <| hb.indep.not_dep <| IsCircuit.dep ?_
  have hwin := @Graph.wheel_isCycleSet_true (n := n) ⟨hn⟩
  rwa [hrw, Matroid.wheel, Graph.cycleMatroid_isCircuit]

/-- A whirl is obtained from a wheel by relaxing the circuit of rim elements.
(A zero-whirl is defined to be an empty matroid.) -/
def whirl (n : ℕ) := (Matroid.wheel n).relax (T := if n = 0 then ∅ else {{e | e.2 = true}})
   (by
    cases n with
    | zero => simp [IsLawfulRelaxation]
    | succ n => simpa using (IsLawfulRelaxation.single (wheel_isCircuitHyperplane (by simp))))

/-- Every connected matroid with a cyclic fan is isomorphic to a wheel or a whirl. -/
lemma IsCyclicFan.exists_eq_map_wheel_or_whirl (hF : M.IsCyclicFan F false)
    (h : 2 < M.E.encard → M.TutteConnected 2) : ∃ (n : ℕ) (φ : Fin n × Bool → α) (hφ : Injective φ),
    M = (Matroid.wheel n).map φ hφ.injOn ∨ M = (Matroid.whirl n).map φ hφ.injOn := by
  set n := F.length.div2 with hn
  have hFn : F.length = n * 2 := mul_comm 2 _ ▸ hF.two_mul_div2.symm
  set φ : Fin n × Bool → α := F.get ∘ ((Fin.cast hFn.symm) ∘ wheelFanEquiv) with hφ
  have hinj : Injective φ :=
    hF.isFan.nodup.injective_get.comp <| (Fin.cast_injective _).comp wheelFanEquiv.injective
  refine ⟨n, φ, hinj, or_iff_not_imp_left.2 fun hMw ↦ ?_⟩
  have hF' : ((Matroid.wheel n).map φ hinj.injOn).IsCyclicFan F false := by
    convert (wheel_isCyclicFan' (by grind)).map hinj.injOn
    simpa [List.map_map, hφ, List.ext_get_iff]
  have hni : ¬ ((Matroid.wheel n).map φ hinj.injOn).Indep
      (F.get '' Fin.val ⁻¹' {i | i.bodd = !false}) := by
    refine fun h ↦ False.elim <| h.not_dep <| IsCircuit.dep ?_
    convert (InvariantFun.map_set (P := IsCircuitHyperplane) (Q := IsCircuitHyperplane)
      (wheel_isCircuitHyperplane (n := n) (by grind)) hinj.injOn).isCircuit
    rw [hφ, image_comp, image_comp,  wheelFanEquiv_image_eq]
    simp
  obtain ⟨hch, hM_eq⟩ := hF.eq_relax hF' h
    (by simpa [hinj.encard_image] using wheel_tutteConnected (n := n))
    hMw (fun h ↦ (hni h).elim)
  rw! [whirl, ite_eq_right (by grind)]
  rw! [relax_map _ hinj.injOn, hφ, image_singleton, image_comp, image_comp,
    wheelFanEquiv_image_eq, ← map_map _ (by simp) hF.isFan.nodup.injective_get.injOn,
    hM_eq, hφ, ← map_map _ (by simp) hF.isFan.nodup.injective_get.injOn]
  simp

lemma IsCyclicFan.nonempty_iso_wheel_or_whirl (hF : M.IsCyclicFan F false)
    (hc : 2 < M.E.encard → M.TutteConnected 2) :
    ∃ (n : ℕ), Nonempty (M ≂ Matroid.wheel n) ∨ Nonempty (M ≂ Matroid.whirl n) := by
  obtain ⟨n, φ, hφ, h⟩ := hF.exists_eq_map_wheel_or_whirl hc
  refine ⟨n , Or.imp ?_ ?_ h⟩
  · rintro rfl
    exact ⟨(isoMap ..).symm⟩
  rintro rfl
  exact ⟨(isoMap ..).symm⟩
