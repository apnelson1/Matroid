module

public import Matroid.Graph.Walk.Cycle
public import Matroid.Graph.Forest
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Matroid.ForMathlib.Fin

@[expose] public section

open List

section Cycle

attribute [simp] NeZero.ne Nat.pos_of_neZero

namespace WList

variable {α β : Type*} {a : List α} {b : List β}

/-- Given two lists of equal length, the closed `WList` obtained by zipping them together and
adding the first element at the end. -/
def cycleZip (a : List α) (b : List β) (hab : a.length = b.length) (ha : a ≠ []) (_ : b.Nodup) :
    WList α β :=
  WList.zip (a.concat (a.head ha)) b (by simpa using hab.symm)

@[simp]
lemma cycleZip_vertex (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).vertex = a ++ [a.head ha] := by
  simp [cycleZip]

@[simp]
lemma cycleZip_vertexSet (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).vertexSet = {x | x ∈ a} := by
  simp only [cycleZip, List.concat_eq_append, zip_vertexSet, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  grind

@[simp]
lemma cycleZip_edge (a : List α) (b : List β) {hab ha hb} : (cycleZip a b hab ha hb).edge = b := by
  simp [cycleZip]

@[simp]
lemma cycleZip_edgeSet (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).edgeSet = {e | e ∈ b} := by
  simp [cycleZip]

@[simp]
lemma cycleZip_wellFormed (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).WellFormed :=
  WList.wellFormed_of_nodup <| by simpa

@[simp]
lemma cycleZip_nonempty (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).Nonempty := by
  rwa [← edge_ne_nil_iff, cycleZip_edge, b.ne_nil_iff_length_pos, ← hab, ← a.ne_nil_iff_length_pos]

@[simp]
lemma cycleZip_isClosed (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).IsClosed := by
  cases a with
  | nil => simp at ha
  | cons x a => simp [IsClosed, ← vertex_head, ← vertex_getLast]

@[simp]
lemma cycleZip_length (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).length = a.length := by
  simp [← length_edge, hab]

@[simp]
lemma cycleZip_tail_vertex_nodup_iff (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b ha hb hab).tail.vertex.Nodup ↔ a.Nodup := by
  cases a with | nil => simp at hb | cons => rw [← List.nodup_reverse]; simp

lemma cycleZip_dInc_iff (a : List α) (b : List β) {hab ha hb} {x y : α} {e : β} :
    (cycleZip a b hab ha hb).DInc e x y ↔ ∃ (i : Fin a.length),
      a[i.1] = x ∧ a[(finRotate _ i).1] = y ∧ b[i.1] = e := by
  simp only [cycleZip, List.concat_eq_append, dinc_iff_get, zip_edge, zip_length, exists_and_left,
    finRotate_apply]
  have aux (i : Fin a.length) : a[(finRotate _ i).1] = (a ++ [a.head ha])[i.1 + 1] := by
    have := i.neZero
    simp only [finRotate_apply]
    obtain rfl | hne := eq_or_ne i ⊤
    · rw! [Fin.top_add_one, Fin.val_zero, Fin.val_top, Nat.sub_add_cancel (by grind),
        List.getElem_append_right rfl.le, Nat.sub_self, List.getElem_cons_zero]
      rw [← List.getElem_zero]
    rw! [Fin.val_add_one_of_ne_top hne, List.getElem_append_left (by grind)]
    rfl
  constructor
  · rintro ⟨i, rfl, rfl, ⟨hi, rfl⟩⟩
    lift i to Fin a.length using hi.trans_eq hab.symm
    exact ⟨i, by simpa [WList.zip_get_eq_getD] using aux i⟩
  rintro ⟨i, rfl, rfl, rfl⟩
  exact ⟨i, by simpa [WList.zip_get_eq_getD, show i.1 < b.length by grind] using (aux i).symm⟩

end WList

namespace Graph

variable {n : ℕ} {α β : Type*}

def circuitOn' {n : ℕ} [NeZero n] (a : Fin n → α) (b : Fin n → β) (hb : b.Injective) : Graph α β :=
  WList.toGraph <| WList.cycleZip ((List.finRange n).map a) ((List.finRange n).map b) (by simp)
    (by simp) ((List.nodup_map_iff hb).2 (List.nodup_finRange n))

/-- The cycle graph determined by two nonempty lists of equal length,
where the edge list has no repeats.
This graph is Eulerian, and is a cycle if the vertices do not repeat. -/
def circuitOn (a : List α) (b : List β) (hab : a.length = b.length) (ha : a ≠ []) (hb : b.Nodup) :
  Graph α β := (WList.cycleZip a b hab ha hb).toGraph

@[simp]
lemma circuitOn_isTour (a : List α) (b : List β) {hab ha hb} :
    (circuitOn a b hab ha hb).IsTour (WList.cycleZip a b hab ha hb) :=
  ⟨⟨WList.WellFormed.isWalk_toGraph (by simp), by simpa⟩, by simp, by simp⟩

lemma circuitOn_isCyclicWalk (a : List α) (b : List β) {hab ha hb} (ha' : a.Nodup) :
    (circuitOn a b hab ha hb).IsCyclicWalk (WList.cycleZip a b hab ha hb) := by
  rwa [isCyclicWalk_iff, and_iff_right (by simp), WList.cycleZip_tail_vertex_nodup_iff]

lemma circuitOn_isCycle (a : List α) (b : List β) {hab ha hb} (ha' : a.Nodup) :
    (circuitOn a b hab ha hb).IsCycle :=
  (circuitOn_isCyclicWalk a b ha').toGraph_isCycle

variable {n : ℕ}

/-- A canonical cycle graph on `Fin n`, where edge `i : Fin n` joins vertices `i, i + 1`. -/
@[simps]
def cycle (n : ℕ) : Graph (Fin n) (Fin n) where
  vertexSet := Set.univ
  IsLink e i j := have := i.neZero
    (e = i ∧ j = i + 1) ∨ (e = j ∧ i = j + 1)
  isLink_symm := by grind [Std.Symm]
  eq_or_eq_of_isLink_of_isLink := by grind
  edge_mem_iff_exists_isLink := by grind
  left_mem_of_isLink := by simp

lemma cycle_adj_add [NeZero n] (i : Fin n) : (cycle n).Adj i (i + 1) := by
  simp [cycle, Adj]

lemma cycle_adj_sub [NeZero n] (i : Fin n) : (cycle n).Adj i (i - 1) := by
  simp [cycle, Adj]

@[simp]
lemma cycle_inc_iff [NeZero n] {e x} : (cycle n).Inc e x ↔ e = x ∨ e = x - 1 := by
  obtain rfl | hne := eq_or_ne e x
  · simp [Inc, cycle_isLink]
  simp [Inc, hne, eq_sub_iff_add_eq, eq_comm]

lemma cycle_isLink_add_one [NeZero n] (i : Fin n) : (cycle n).IsLink i i (i + 1) := by
  simp [cycle]


def cFun (a d : Fin n) (x : Fin ((-d).rev + 1)) := a + x.castLE (by grind)

@[simp]
lemma cFun_zero [NeZero n] (a : Fin n) : cFun a 0 = fun x ↦ a + x.cast
  (by cases n with | zero => simpa using a.2 | succ => simp) := rfl

@[simp]
lemma cFun_fin_one (a d : Fin 1) : cFun a d = fun x ↦ x.cast (by grind) := by
  rw [a.fin_one_eq_zero, d.fin_one_eq_zero]
  simp

@[simp]
lemma cFun_one [hn : Fact (1 < n)] (a : Fin n) : cFun a 1 = fun _ ↦ a := by
  obtain rfl | rfl | n := n
  · simpa using hn.elim
  · simpa using hn.elim
  ext x
  obtain rfl : x = 0 := by simpa using x.2
  simp [cFun]

/-- The `WList` in a cycle of the form `a, a, a + 1, a + 1, ..., b - 1, b`.
If `a = b`, this is the whole cycle.  -/
def cyclePath (a b : Fin n) : WList (Fin n) (Fin n) :=
  let L := (finRange _).map (cFun a (b - a))
  WList.zip (L.concat b) L (by simp)

@[simp]
lemma cyclePath_first (a b : Fin n) : (cyclePath a b).first = a := by
  have := a.neZero
  simp [cyclePath, cFun, finRange, Fin.castLE]

@[simp]
lemma cyclePath_last (a b : Fin n) : (cyclePath a b).last = b := by
  have := a.neZero
  simp [cyclePath, cFun, finRange, Fin.castLE]

lemma cyclePath_length (a b : Fin n) :
    (cyclePath a b).length = if a = b then n else (b - a).1 := by
  obtain rfl | rfl | n := n
  · simpa using a.2
  · simp [a.fin_one_eq_zero, b.fin_one_eq_zero, cyclePath]
  split_ifs with hab
  · simp [cyclePath, hab]
  simp only [cyclePath, Fin.val_rev, concat_eq_append, WList.zip_length, length_map,
    length_finRange, Nat.reduceSubDiff]
  have hba : (b - a).1 ≠ 0 := by simp [sub_eq_zero, Ne.symm hab]
  have hblt := (b - a).2
  rw [Fin.val_neg, ite_eq_right (by grind)]
  lia

lemma cyclePath_nonempty (a b : Fin n) : (cyclePath a b).Nonempty := by
  have hnz := a.neZero
  rw [← WList.length_ne_zero_iff, cyclePath_length]
  split_ifs with hab
  · exact hnz.1
  simp [sub_eq_zero, Ne.symm hab]

open Fin.NatCast in
lemma cyclePath_get [NeZero n] {a b : Fin n} (i : ℕ) (hi : i ≤ (cyclePath a b).length) :
    (cyclePath a b).get i = (a + i : Fin n) := by
  rw [cyclePath, WList.get_eq_getElem_vertex _ (by simpa [cyclePath] using hi)]
  simp only [Fin.val_rev, concat_eq_append, WList.zip_vertex]
  obtain rfl | hlt := hi.eq_or_lt
  · rw [List.getElem_concat_length (by simp [cyclePath])]
    simp only [cyclePath_length, Nat.cast_ite, Fin.natCast_self, Fin.cast_val_eq_self]
    grind
  rw [List.getElem_append_left (by simpa [cyclePath] using hlt)]
  suffices i = i % n by simpa [cFun, ← Fin.val_inj]
  have hle' : i ≤ n - (↑(a - b) + 1) := by simpa [cyclePath] using hlt
  rw [Nat.mod_eq_of_lt (by lia)]

open Fin.NatCast in
lemma cyclePath_getElem_edge [NeZero n] {a b : Fin n} (i : ℕ)
    (hi : i < (cyclePath a b).edge.length) : (cyclePath a b).edge[i] = (a + i : Fin n) := by
  rw [← cyclePath_get (b := b) i (by simpa using hi.le)]
  rw! [cyclePath, WList.zip_edge, WList.get_eq_getElem_vertex _ (by simpa [cyclePath] using hi.le),
    concat_eq_append, WList.zip_vertex, getElem_append_left]
  rfl

open Fin.NatCast in
lemma cyclePath_isTrail (a b : Fin n) : (cycle n).IsTrail (cyclePath a b) := by
  obtain rfl | n := n
  · simpa using a.2
  refine ⟨?_, ?_⟩
  · rw [isWalk_iff_forall_isLink_get_of_nonempty (cyclePath_nonempty ..)]
    intro i hi
    rw [cyclePath_get _ hi.le, cyclePath_getElem_edge, cyclePath_get _ (by lia),
      Nat.cast_add, ← add_assoc, Nat.cast_one]
    exact cycle_isLink_add_one ..
  simp only [cyclePath, Fin.val_rev, concat_eq_append, WList.zip_edge]
  rw [nodup_map_iff_inj_on]
  · simp [cFun]
  exact nodup_finRange ..

lemma cyclePath_isPath (a b : Fin n) (hab : a ≠ b) : (cycle n).IsPath (cyclePath a b) := by
  refine ⟨(cyclePath_isTrail ..).isWalk, ?_⟩
  simp only [cyclePath, Fin.val_rev, concat_eq_append, WList.zip_vertex, nodup_append, nodup_cons,
    not_mem_nil, not_false_eq_true, nodup_nil, and_self, mem_map, mem_finRange, cFun, true_and,
    mem_cons, or_false, ne_eq, forall_eq, forall_exists_index, forall_apply_eq_imp_iff]
  rw [List.nodup_map_iff_inj_on]
  · simp only [mem_finRange, cFun, Fin.val_rev, add_right_inj, Fin.castLE_inj, imp_self,
      implies_true, true_and]
    have := a.neZero
    rintro ⟨rfl | x, hlt⟩ heq
    · simp [← heq, Fin.castLE] at hab
    simp only [← heq, Fin.castLE_mk, add_sub_cancel_left, Fin.val_neg, Fin.mk_eq_zero,
       NeZero.ne, ↓reduceIte, Order.lt_add_one_iff, Order.add_one_le_iff] at hlt
    grind
  exact nodup_finRange ..

lemma cyclePath_isCyclicWalk (a : Fin n) : (cycle n).IsCyclicWalk (cyclePath a a) := by
  refine IsTour.isCyclicWalk_of_dropLast_nodup ?_ ?_
  · simp [isTour_iff, cyclePath_isTrail, cyclePath_nonempty, WList.IsClosed]
  simp only [cyclePath, Fin.val_rev, concat_eq_append, ne_eq, map_eq_nil_iff, finRange_eq_nil_iff,
    NeZero.ne, not_false_eq_true, WList.zip_dropLast, cons_ne_self,
    dropLast_append_of_ne_nil, dropLast_singleton, append_nil, WList.zip_vertex]
  rw [List.nodup_map_iff_inj_on]
  · simp [cFun]
  exact nodup_finRange ..

lemma cyclePath_add_one_self [NeZero n] (a : Fin n) :
    (cyclePath a (a + 1)) = (WList.nil (a + 1)).cons a a := by
  obtain rfl | rfl | n := n
  · simpa using a.2
  · simp [cyclePath, finRange, a.fin_one_eq_zero]
  have : Fact (1 < n + 1 + 1) := ⟨by lia⟩
  simp only [cyclePath, Fin.val_rev, concat_eq_append]
  rw! [add_sub_cancel_left, cFun_one]
  simp

lemma cycle_eq_circuitOn (n : ℕ) [NeZero n] :
    cycle n = Graph.circuitOn (List.finRange n) (List.finRange n)
      rfl (by simp) (List.nodup_finRange n) := by
  refine ext_inc (by simp [circuitOn]) ?_
  simp only [cycle_inc_iff, circuitOn, WList.cycleZip_wellFormed, WList.WellFormed.toGraph_inc,
    WList.Inc, WList.isLink_iff_dInc, WList.cycleZip_dInc_iff, List.getElem_finRange, Fin.eta,
    finRotate_apply, Fin.cast_add_one]
  refine fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl | rfl := h
    · exact ⟨e + 1, .inl ⟨e.cast (by simp), by simp⟩⟩
    exact ⟨x - 1, .inr ⟨(x - 1).cast (by simp), by simp⟩⟩
  obtain ⟨y, ⟨z, rfl, rfl, rfl⟩ | ⟨z, rfl, rfl, rfl⟩⟩ := h <;>
  simp

lemma cycle_isCyclicWalk (n : ℕ) [NeZero n] : (cycle n).IsCyclicWalk
    (WList.cycleZip (finRange n) (finRange n) rfl (by simp) (List.nodup_finRange n)) := by
  rw [isCyclicWalk_iff, isTour_iff, isTrail_iff]
  simp only [WList.cycleZip_edge, nodup_finRange, and_true, WList.cycleZip_nonempty,
    WList.cycleZip_isClosed, and_self, WList.Nonempty.vertex_tail, WList.cycleZip_vertex, ne_eq,
    finRange_eq_nil_iff, NeZero.ne, not_false_eq_true, tail_append_of_ne_nil, nodup_append,
    Nodup.tail, nodup_cons, not_mem_nil, nodup_nil, mem_cons, or_false, forall_eq, true_and]
  refine ⟨?_, ?_⟩
  · rw [cycle_eq_circuitOn, circuitOn]
    exact WList.WellFormed.isWalk_toGraph (by simp)
  rintro a ha rfl
  exact (nodup_finRange n).head_notMem_tail (hne := by simp) ha

lemma cycle_isCycle (n : ℕ) [NeZero n] : (cycle n).IsCycle := by
  rw [cycle_eq_circuitOn]
  exact (cycle_isCyclicWalk n).toGraph_isCycle

lemma cycle_regular_two (n : ℕ) [NeZero n] : (cycle n).Regular 2 :=
  (cycle_isCycle n).regular_two

@[simp]
lemma cycle_vertexSet (n : ℕ) : V(cycle n) = Set.univ := rfl

@[simp]
lemma cycle_edgeSet (n : ℕ) : V(cycle n) = Set.univ := rfl

@[simp]
lemma cycle_degree (n : ℕ) [NeZero n] (x : Fin n) : (cycle n).degree x = 2 :=
  (cycle_regular_two n).degree <| by simp

@[simp]
lemma cycle_eDegree (n : ℕ) [NeZero n] (x : Fin n) : (cycle n).eDegree x = 2 :=
  cycle_regular_two n <| by simp

end Graph
