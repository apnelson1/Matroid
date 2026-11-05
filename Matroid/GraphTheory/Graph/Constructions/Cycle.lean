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

variable {α β : Type*} {a : List α} {b : List β}

namespace WList

/-- Given two lists of equal length, the closed `WList` obtained by zipping them together and
adding the first element at the end. Maybe this definition is overkill. -/
def cycleZip (a : List α) (b : List β) (hab : a.length = b.length) (ha : a ≠ []) : WList α β :=
  WList.zip (a.concat (a.head ha)) b (by simpa using hab.symm)

@[simp]
lemma cycleZip_vertex (a : List α) (b : List β) {hab ha} :
    (cycleZip a b hab ha).vertex = a ++ [a.head ha] := by
  simp [cycleZip]

@[simp]
lemma cycleZip_vertexSet (a : List α) (b : List β) {hab ha} :
    (cycleZip a b hab ha).vertexSet = {x | x ∈ a} := by
  simp only [cycleZip, List.concat_eq_append, zip_vertexSet, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  grind

@[simp]
lemma cycleZip_edge (a : List α) (b : List β) {hab ha} : (cycleZip a b hab ha).edge = b := by
  simp [cycleZip]

@[simp]
lemma cycleZip_edgeSet (a : List α) (b : List β) {hab ha} :
    (cycleZip a b hab ha).edgeSet = {e | e ∈ b} := by
  simp [cycleZip]

@[simp]
lemma cycleZip_wellFormed_of_nodup (a : List α) (b : List β) {hab ha} (hb : b.Nodup) :
    (cycleZip a b hab ha).WellFormed :=
  WList.wellFormed_of_nodup <| by simpa

@[simp]
lemma cycleZip_nonempty (a : List α) (b : List β) {hab ha} :
    (cycleZip a b hab ha).Nonempty := by
  rwa [← edge_ne_nil_iff, cycleZip_edge, b.ne_nil_iff_length_pos, ← hab, ← a.ne_nil_iff_length_pos]

@[simp]
lemma cycleZip_isClosed (a : List α) (b : List β) {hab ha} :
    (cycleZip a b hab ha).IsClosed := by
  cases a with
  | nil => simp at ha
  | cons x a => simp [IsClosed, ← vertex_head, ← vertex_getLast]

@[simp]
lemma cycleZip_length (a : List α) (b : List β) {hab ha} :
    (cycleZip a b hab ha).length = a.length := by
  simp [← length_edge, hab]

@[simp]
lemma cycleZip_tail_vertex_nodup_iff (a : List α) (b : List β) {hab ha} :
    (cycleZip a b hab ha).tail.vertex.Nodup ↔ a.Nodup := by
  cases a with | nil => simp at ha | cons => rw [← List.nodup_reverse]; simp

lemma cycleZip_dInc_iff (a : List α) (b : List β) {hab ha} {x y : α} {e : β} :
    (cycleZip a b hab ha).DInc e x y ↔ ∃ (i : Fin a.length),
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

def circuitOn' {n : ℕ} [NeZero n] (a : Fin n → α) (b : Fin n → β) : Graph α β :=
  WList.toGraph <| WList.cycleZip ((List.finRange n).map a) ((List.finRange n).map b) (by simp)
    (by simp)

/-- The cycle graph determined by two nonempty lists of equal length,
where the edge list has no repeats.
This graph is Eulerian, and is a cycle if the vertices do not repeat. -/
def circuitOn (a : List α) (b : List β) (hab : a.length = b.length) (ha : a ≠ [])  :
  Graph α β := (WList.cycleZip a b hab ha).toGraph

@[simp]
lemma circuitOn_isTour (a : List α) (b : List β) {hab ha} (hb : b.Nodup) :
    (circuitOn a b hab ha).IsTour (WList.cycleZip a b hab ha) :=
  ⟨⟨WList.WellFormed.isWalk_toGraph (WList.cycleZip_wellFormed_of_nodup _ _ hb), by simpa⟩,
    by simp, by simp⟩

lemma circuitOn_isCyclicWalk {hab ha} (ha' : a.Nodup) (hb : b.Nodup) :
    (circuitOn a b hab ha).IsCyclicWalk (WList.cycleZip a b hab ha) := by
  rwa [isCyclicWalk_iff, and_iff_right (circuitOn_isTour _ _ hb),
    WList.cycleZip_tail_vertex_nodup_iff]

lemma circuitOn_isCycle {hab ha} (ha' : a.Nodup) (hb : b.Nodup) : (circuitOn a b hab ha).IsCycle :=
  (circuitOn_isCyclicWalk ha' hb).toGraph_isCycle

lemma circuitOn_loopless_iff {hab ha} (ha' : a.Nodup) (hb : b.Nodup) :
    (circuitOn a b hab ha).Loopless ↔ 2 ≤ a.length := by
  simp only [circuitOn, (circuitOn_isCyclicWalk ha' hb).toGraph_loopless_iff, WList.cycleZip_length]
  grind [cases List]

lemma circuitOn_simple_iff {hab ha} (ha' : a.Nodup) (hb : b.Nodup) :
    (circuitOn a b hab ha).Simple ↔ 3 ≤ a.length := by
  simp [circuitOn, (circuitOn_isCyclicWalk ha' hb).toGraph_simple_iff]

variable {n : ℕ}

open Fin.NatCast in
/-- A walk around the cycle arising from lists `a` and `b`, starting at position `i`
and proceeding `d` steps clockwise. -/
def cycleWalk (a : List α) (b : List β) (hlen : a.length = b.length) (x : Fin a.length) (d : ℕ) :
    WList α β :=
  have := x.neZero
  have := (x.cast hlen).neZero
  WList.zip ((range (d + 1)).map fun (i : ℕ) ↦ a.get (x + (i)))
    ((range d).map fun (i : ℕ) ↦ b.get (x.cast hlen + i)) (by simp)

@[simp]
lemma cycleWalk_length (a : List α) (b : List β) (hlen) (x : Fin a.length) (d : ℕ) :
    (cycleWalk a b hlen x d).length = d := by
  simp [cycleWalk]

@[simp]
lemma cycleWalk_zero (a : List α) (b : List β) {hlen} (x : Fin a.length) :
    (cycleWalk a b hlen x 0) = WList.nil a[x] := by
  simp [cycleWalk]

open Fin.NatCast in
lemma cycleWalk_one (a : List α) [NeZero a.length] (b : List β) {hlen} (x : Fin a.length) :
    (cycleWalk a b hlen x 1) = WList.cons a[x] b[x] (WList.nil (a[x + 1])) := by
  simp [cycleWalk, show range 2 = [0, 1] from rfl, Nat.cast_one]

open Fin.NatCast in
lemma cycleWalk_get (a : List α) (b : List β) (hlen) (x : Fin a.length) {d i : ℕ} (hid : i ≤ d) :
    have := x.neZero
    (cycleWalk a b hlen x d).get i = a.get (x + (i : Fin a.length)) := by
  rw [WList.get_eq_getElem_vertex _ (by simpa)]
  simp [cycleWalk]

lemma cycleWalk_zero_length (a : List α) [ha : NeZero a.length] (b : List β) (hlen) :
    cycleWalk a b hlen 0 a.length = WList.cycleZip a b hlen (by rintro rfl; simpa using ha.1) := by
  rw [cycleWalk, WList.cycleZip]
  convert rfl
  · rw! [range_add_one, List.map_append, map_cons, map_nil, zero_add, get_eq_getElem]
    simp [getElem_zero_eq_head]
    exact List.ext_getElem (by simp) (by simp +contextual [Nat.mod_eq_of_lt])
  rw [hlen] at ha
  exact List.ext_getElem (by simp [hlen]) <| by simp +contextual [Fin.cast_zero, Nat.mod_eq_of_lt]

open Fin.NatCast in
@[simp]
lemma cycleWalk_tail (a : List α) [NeZero a.length] (b : List β) (hlen) (x : Fin a.length) {d : ℕ} :
    (cycleWalk a b hlen x (d + 1)).tail = cycleWalk a b hlen (x + 1) d := by
  rw [cycleWalk, cycleWalk, WList.zip_tail _ (by simp)]
  convert rfl
  · rw! [← List.map_tail, List.tail_range, range'_eq_map_range, List.map_map]
    simp [Nat.cast_add, add_assoc]
  rw! [← List.map_tail, List.tail_range, range'_eq_map_range, List.map_map]
  have := (x.cast hlen).neZero
  simp [Nat.cast_add, Fin.cast_add, add_assoc]

@[simp]
lemma cycleWalk_dropLast (a : List α) (b : List β) (hlen) (x : Fin a.length) {d : ℕ} :
    (cycleWalk a b hlen x (d + 1)).dropLast = cycleWalk a b hlen x d := by
  rw! [cycleWalk, cycleWalk, WList.zip_dropLast _ (by simp)]
  simp [List.range_add_one]

@[simp]
lemma cycleWalk_first (a : List α) (b : List β) (hlen) (x : Fin a.length) (d : ℕ) :
    (cycleWalk a b hlen x d).first = a[x] := by
  simp [cycleWalk]

open Fin.NatCast in
@[simp]
lemma cycleWalk_last (a : List α) [NeZero a.length] (b : List β) (hlen) (x : Fin a.length) (d : ℕ) :
    (cycleWalk a b hlen x d).last = a[(x + d).1] := by
  simp [cycleWalk]

open Fin.NatCast in
lemma cycleWalk_isWalk {a : List α} {b : List β} {hlen} (hb : b.Nodup) (x : Fin a.length) (d : ℕ) :
    (circuitOn a b hlen (by rintro rfl; simpa using x.2)).IsWalk (cycleWalk a b hlen x d) := by
  rw [cycleWalk, isWalk_zip_iff]
  simp only [circuitOn, WList.toGraph_vertexSet, WList.cycleZip_vertexSet, get_eq_getElem,
    getElem_map, getElem_range, Fin.natCast_zero, Fin.add_zero, Set.mem_ofPred_eq, getElem_mem,
    length_map, length_range, Order.lt_add_one_iff, Order.add_one_le_iff, true_and]
  intro i hid
  rw [(WList.cycleZip_wellFormed_of_nodup _ _ hb).toGraph_isLink, WList.cycleZip,
    WList.zip_isLink_iff]
  have hnz := x.neZero
  have hxa := x.2
  refine ⟨(x + i).1, by simp, by simp [Fin.val_add, hlen], ?_⟩
  convert rfl using 2
  · simp_rw [Fin.val_add, hlen, concat_eq_append, Fin.val_natCast, ← hlen, Nat.add_mod_mod]
    rw [getElem_append_left]
  obtain htop | hne := eq_or_ne (x + i) ⊤
  · rw! [htop, Fin.val_top, Nat.sub_add_cancel (by lia), Nat.cast_add, ← add_assoc, htop,
      Nat.cast_one, Fin.top_add_one, Fin.val_zero]
    simp [getElem_zero_eq_head]
  rw! [List.concat_eq_append, getElem_append_left, Nat.cast_add, ← add_assoc, Nat.cast_one,
    Fin.val_add_one_of_ne_top hne]
  rfl

lemma cycleWalk_isTrail {a : List α} {b : List β} {hlen} (hb : b.Nodup) (x : Fin a.length)
    {d : ℕ} (hd : d ≤ a.length) :
    (circuitOn a b hlen (by rintro rfl; simpa using x.2)).IsTrail (cycleWalk a b hlen x d) := by
  refine ⟨cycleWalk_isWalk hb x d, ?_⟩
  simp only [cycleWalk, get_eq_getElem, WList.zip_edge]
  rw [nodup_map_iff_inj_on (nodup_range ..)]
  simp only [mem_range, hb.getElem_inj_iff, Fin.val_inj, add_right_inj]
  intro x hx y hy hxy
  rwa [← Fin.val_inj, Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by lia),
    Nat.mod_eq_of_lt (by lia)] at hxy

lemma cycleWalk_isPath {a : List α} {b : List β} {hlen} (ha : a.Nodup) (hb : b.Nodup)
    (x : Fin a.length) {d : ℕ} (hd : d < a.length) :
    (circuitOn a b hlen (by rintro rfl; simpa using x.2)).IsPath (cycleWalk a b hlen x d) := by
  refine ⟨cycleWalk_isWalk hb x d, ?_⟩
  simp only [cycleWalk, get_eq_getElem, WList.zip_vertex]
  rw [nodup_map_iff_inj_on (nodup_range ..)]
  simp only [mem_range, Order.lt_add_one_iff, ha.getElem_inj_iff, Fin.val_inj, add_right_inj]
  intro x hx y hy hxy
  rwa [← Fin.val_inj, Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by lia),
    Nat.mod_eq_of_lt (by lia)] at hxy

lemma cycleWalk_isCyclicWalk {a : List α} {b : List β} {hlen} (ha : a.Nodup) (hb : b.Nodup)
    (x : Fin a.length) : (circuitOn a b hlen (by rintro rfl; simpa using x.2)).IsCyclicWalk
    (cycleWalk a b hlen x a.length) := by
  have hnz := x.neZero
  refine IsTour.isCyclicWalk_of_dropLast_nodup ⟨cycleWalk_isTrail hb x rfl.le, ?_, ?_⟩ ?_
  · cases a with | nil => simpa using x.2 | cons => simp [cycleWalk]
  · simp [WList.IsClosed]
  cases h : a.length with
  | zero => simp [hnz.1 h]
  | succ n =>
    rw [cycleWalk_dropLast]
    exact ((cycleWalk_isPath ha hb x (d := n)) (by lia)).nodup

/-- A canonical cycle graph on `Fin n`, where edge `i : Fin n` joins vertices `i, i + 1`. -/
@[simps]
def cycle (n : ℕ) : Graph (Fin n) (Fin n) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e i j := have := i.neZero
    (e = i ∧ j = i + 1) ∨ (e = j ∧ i = j + 1)
  isLink_symm := by grind [Std.Symm]
  eq_or_eq_of_isLink_of_isLink := by grind
  edge_mem_iff_exists_isLink := by grind
  left_mem_of_isLink := by simp

lemma cycle_eq_circuitOn (n : ℕ) [NeZero n] :
    cycle n = circuitOn (List.finRange n) (List.finRange n) rfl (by simp) := by
  refine Graph.ext (by simp [circuitOn]) fun e x y ↦ ?_
  rw [circuitOn, WList.WellFormed.toGraph_isLink, WList.isLink_iff_dInc, WList.cycleZip_dInc_iff,
    WList.cycleZip_dInc_iff, cycle_isLink]
  · simp only [getElem_finRange, Fin.eta, finRotate_apply, Fin.cast_add, Fin.cast_one]
    refine ⟨Or.imp ?_ ?_, Or.imp ?_ ?_⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨e.cast (by simp), by simp⟩
    · rintro ⟨rfl, hx⟩
      exact ⟨e.cast (by simp), by simp [hx]⟩
    · rintro ⟨i, rfl, rfl, rfl⟩
      simp
    rintro ⟨i, rfl, rfl, rfl⟩
    simp
  exact WList.cycleZip_wellFormed_of_nodup _ _ <| nodup_finRange n

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

lemma cycle_isCycle (n : ℕ) [NeZero n] : (cycle n).IsCycle := by
  rw [cycle_eq_circuitOn]
  exact circuitOn_isCycle (nodup_finRange n) (nodup_finRange n)

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

@[simp]
lemma cycle_one : cycle 1 = Graph.singleEdge 0 0 0 := by
  ext e x y
  · simp [e.fin_one_eq_zero]
  simp [e.fin_one_eq_zero, Fin.isValue, x.fin_one_eq_zero, y.fin_one_eq_zero,
    - isLink_self_iff]

-- @[simp]
-- lemma cycle_two : cycle 2 = Graph.banana 0 1 {0, 1} := by
--   _

end Graph
