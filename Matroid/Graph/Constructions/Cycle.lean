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


end Graph
