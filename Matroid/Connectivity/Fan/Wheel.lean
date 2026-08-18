module

public import Matroid.Graphic
public import Matroid.Graph.Constructions.Sum
public import Matroid.Graph.Constructions.Cycle
public import Matroid.Graph.Connected.Ear


@[expose] public section

variable {α β : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α} {G : Graph α β}



open Set Option WList Function

namespace Graph

/-- The wheel graph, with rim edges of the form `(i, true)` and spoke edges of the form
`(i : false)`, for `i : Fin n`.  -/
def wheel (n : ℕ) : Graph (Option (Fin n)) (Fin n × Bool) :=
  (Graph.cycle n).apex.edgeMap (fun x ↦ ⟨x.elim id id, x.isRight⟩)



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

lemma wheel_triangle [NeZero n] (hn : 2 ≤ n) (i : Fin n) : (wheel n).IsCyclicWalk <| WList.zip
    [none, some i, some (i + 1), none] ([(i, true), (i, false), (i + 1, true)]) := by
  have hnz := i.neZero
  have hC := (cyclePath_isPath i (i + 1) (by simp [show n ≠ 1 by lia])).isCyclicWalk_apex
    (cyclePath_nonempty ..)
  replace hC := hC.edgeMap (fun (x : Fin n ⊕ Fin n) ↦ ((x.elim id id, x.isRight) : Fin n × Bool))
    (by simp)
  simp only [cyclePath_add_one_self, first_cons, map_cons, map_nil, edgeMap_cons, edgeMap_nil,
    last_cons, nil_last, cons_concat, nil_concat, Sum.elim_inr, id_eq, Sum.isRight_inr,
    Sum.elim_inl, Sum.isRight_inl] at hC
  exact hC

lemma wheel_bond {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (wheel n).IsBond {(i, false), (i + 1, true), (i + 1, false)} := by
  rw! [wheel, isBond_edgeMap_iff' (by simp [Injective]) (by simp [insert_subset_iff])]
  convert (cycle n).apex_isBond_setLinkEdges_singleton (x := i + 1) (by simp)
  have : (cycle n).apex.Loopless := by
    simp only [apex_loopless_iff]
    rw [IsCycle]
    _
  rw [setLinkEdges_singleton_compl_eq_incEdges]

  ext (x | x)
  · simp [apex_inc_eq_match, or_comm]
  simp [apex_inc_eq_match, eq_comm]





  -- rw! [wheel, apex, copy_eq, isBond_edgeMap_iff' (by simp [Injective])
  --   (by simp [insert_subset_iff]), isBond_edgeMap_iff' (by simp [Injective])
  --   (by simp [preimage_subset_iff]), isBond_map_iff,
  --   ]



  sorry


end Graph

namespace Matroid

/-- The wheel matroid with ground set `Fin n × Bool`. -/
-- protected def wheel (n : ℕ) : Matroid (Fin n × Bool) := (Graph.wheel n).cycleMatroid
