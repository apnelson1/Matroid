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

lemma wheel_isCyclicFan (hn : 2 ≤ n) : (Matroid.wheel n).IsCyclicFan
    ((List.finRange (2 * n)).map (finMulTwoEquiv n)) false := by
  have : NeZero n := ⟨by lia⟩
  have : NeZero (2 * n) := ⟨by lia⟩
  have hnz : NeZero <| List.length <| (List.finRange (2 * n)).map (finMulTwoEquiv n) := by simpa
  refine isCyclicFan_of_forall _ _ _ (by grind) ?_ ?_
  · simp_rw [List.nodup_map_iff_inj_on (List.nodup_finRange _),
      (finMulTwoEquiv n).injective.eq_iff]
    simp
  simp only [Bool.false_bne, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
    Fin.forall_iff, List.length_map, List.length_finRange]
  intro i hi
  lift i to Fin (2 * n) using hi
  cases hib : i.1.bodd with
  | false =>
    convert wheel_isTriangle hn (finMulTwoEquiv n i).1 using 2
    · rfl
    · simpa
    convert rfl using 2
    · simp [Fin.val_add, (show (2 * n).bodd = false by simp), div2_mod, hib,
        Nat.mod_bodd, Nat.mod_eq_of_lt, show i.1.div2 < n by grind]
    simp [Fin.val_add, (show (2 * n).bodd = false by simp), div2_mod, hib, Nat.mod_bodd,
      ← Fin.val_inj]
  | true =>
    convert wheel_isTriad hn (finMulTwoEquiv n i).1 using 2
    · simp
    · simpa
    convert rfl using 2 <;>
    simp [Fin.val_add, (show (2 * n).bodd = false by simp), div2_mod, hib, Nat.mod_bodd,
      ← Fin.val_inj]

lemma wheel_isCircuitHyperplane (hn : n ≠ 0) :
    (Matroid.wheel n).IsCircuitHyperplane {e | e.2 = false} := by
  obtain rfl | rfl | n := n
  · lia
  · sorry
  have := (wheel_isCyclicFan (n := n + 1 + 1) (by simp)).isCircuitHyperplane_or_isBase_cojoints
    (Connected.tutteConnected_two ?_)
  · sorry
  simp [Matroid.wheel]





  -- | true => sorry
  -- · rw [List.nodup_map_iff_inj_on]
  --   simp




  --   ((List.range (2 * n)).pmap (P := fun i ↦ i < 2 * n)
  --   (f := fun i hi ↦ (⟨i.div2, by grind [i.bodd_add_div2]⟩, true)) (by simp)) false := by
  -- _
