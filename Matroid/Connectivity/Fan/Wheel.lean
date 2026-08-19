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

lemma wheel_isCyclicFan (hn : 2 ≤ n) : ∃ (F : List (Fin n × Bool)) (hF : F.length = 2 * n),
    (Matroid.wheel n).IsCyclicFan F false ∧ {e | e ∈ F} = univ ∧
      (∀ (i : Fin n) (b : Bool), F[2 * i + b.toNat] = (i, b)) ∧
      (∀ i (hi : i < F.length), F[i] = (⟨i.div2, by grind⟩, i.bodd)) := by
  set φ := (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)) with hφ
  have hφ' (i : ℕ) (hi : i < n * 2) : φ ⟨i, hi⟩ = (⟨i.div2, by grind⟩, i.bodd) := by
    simp [φ, Nat.mod_bodd, Nat.div2, Fin.divNat]
  set F := (List.finRange (n * 2)).map φ with hF
  have hnzn : NeZero n := ⟨by lia⟩
  have hnz : NeZero F.length := ⟨by simp [F]⟩
  have hφ'' (i : Fin F.length) : (φ (i.cast (by simp [F]))).1 = i.1.div2 := by
    simp [φ, Nat.mod_bodd, Nat.div2, Fin.divNat]
  refine ⟨F, by simp [hF, mul_comm], ?_, ?_, ?_, ?_⟩
  · refine isCyclicFan_of_forall _ _ _ (by simp [F, show 4 ≤ n * 2 by lia]) ?_ ?_
    · simp [F, List.nodup_map_iff_inj_on (List.nodup_finRange _)]
    simp only [Bool.false_bne, List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.forall_iff,
      List.length_map, List.length_finRange, F]
    intro i hi
    cases hib : i.bodd
    · convert wheel_isTriangle hn (φ ⟨i, hi⟩).1 using 3
      · simp
      · simpa [hφ']
      · simp [hφ', Fin.val_add, Nat.mod_bodd, hib, div2_mod, mul_comm n 2,
          Nat.mod_eq_of_lt (show i.div2 < n by grind)]
      simp [hφ', Fin.val_add, Nat.mod_bodd, hib, div2_mod, mul_comm n 2, ← Fin.val_inj]
    convert wheel_isTriad hn (φ ⟨i, hi⟩).1 using 3
    · simp
    · simpa [hφ']
    · simp [hφ', Fin.val_add, Nat.mod_bodd, hib, div2_mod, mul_comm n 2, ← Fin.val_inj]
    simp [hφ', Fin.val_add, Nat.mod_bodd, hib, div2_mod, mul_comm n 2, ← Fin.val_inj]
  · simp [F, show ∀ x, ∃ a, φ a = x from fun x ↦ ⟨φ.symm x, by simp⟩]
  · suffices ∀ (i : Fin n), ⟨(2 * ↑i + 1) / 2, by grind⟩ = i by simpa [F, φ, Fin.divNat]
    grind
  simp [F, φ, Fin.divNat, Nat.div2, Nat.mod_bodd]

lemma wheel_connected (hn : 2 ≤ n) : (Matroid.wheel n).Connected := by
  obtain ⟨F, -, hF, hfU, -, -⟩ := wheel_isCyclicFan hn
  rw [← hF.setOf_eq_ground_iff, hfU]
  simp [Matroid.wheel]

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
  have hMc : (Matroid.wheel n).Connected := by
    simp_rw [← hF.setOf_eq_ground_iff, hFuniv, Matroid.wheel, Graph.cycleMatroid_E,
      Graph.wheel_edgeSet]
  have hrw :  ((fun x ↦ F[x.1]) '' Fin.val ⁻¹' {i | i.bodd = !false}) = {e | e.2 = true} := by
    ext ⟨i, b⟩
    grind [hF.isFan.getElem_inj_iff, Fin.exists_iff]
  obtain hch | hb := hF.isCircuitHyperplane_or_isBase_cojoints hMc.tutteConnected_two
  · rwa [← hrw]
  refine False.elim <| hb.indep.not_dep <| IsCircuit.dep ?_
  have hwin := @Graph.wheel_isCycleSet_true (n := n) ⟨hn⟩
  rwa [hrw, Matroid.wheel, Graph.cycleMatroid_isCircuit]

def whirl (n : ℕ) := (Matroid.wheel n).relax (T := if n = 0 then ∅ else {{e | e.2 = true}})
   (by
    cases n with
    | zero => simp [IsLawfulRelaxation]
    | succ n => simpa using (IsLawfulRelaxation.single (wheel_isCircuitHyperplane (by simp))))

/- Need better API for `map` with connected, relax, etc.  -/
-- lemma IsCyclicFan.exists_eq_map_wheel_or_whirl (hF : M.IsCyclicFan F false)
--     (hc : M.TutteConnected 2) : ∃ (n : ℕ) (φ : Fin n × Bool → α) (hφ : Injective φ),
--     M = (Matroid.wheel n).map φ hφ.injOn ∨ M = (Matroid.whirl n).map φ hφ.injOn := by
--   set n := F.length.div2 with hn
--   have h2n : 2 ≤ n := by grind
--   let ψ : Fin n × Bool ≃ Fin (n * 2) :=
--     (((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm)).trans (finProdFinEquiv))
--   have hinj : Injective fun i ↦ F[(ψ i).1] := by
--     simp [Injective, hF.isFan.nodup.getElem_inj_iff, Fin.val_inj]
--   refine ⟨n, fun i ↦ F[(ψ i).1], hinj, ?_⟩
--   obtain ⟨F₀, hF₀n, hF₀, hF₀u, hF₀1, hF₀2⟩ := wheel_isCyclicFan h2n
--   have hrw : F = F₀.map (fun i ↦ F[(ψ i).1]) := sorry
--   have hM' := hF₀.map hinj.injOn
--   rw [← hrw] at hM'
--   rw [or_iff_not_imp_left]
--   intro hMM'
--   have := hF.eq_relax hM' hc ?_ hMM' ?_
--   · obtain ⟨hch, rfl⟩ := this
--     simp [whirl, ite_eq_right (show n ≠ 0 by lia)]
--   have := hM'.eq_relax hF (Connected.tutteConnected_two ?_) hc (Ne.symm hMM')
--   sorry
