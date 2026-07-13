import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Forest
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.ZMod.Basic

section Cycle

variable {α β : Type*}

namespace WList

variable {n : ℕ} [NeZero n] {a : List.Vector α n} {b : List.Vector β n}

def circuitZip {n : ℕ} [NeZero n] (a : List.Vector α n) (b : List.Vector β n) (_ : b.toList.Nodup) :
    WList α β := WList.zip (a.toList ++ [a.toList.head (by
      rw [← List.length_pos_iff, a.toList_length, ne_zero_iff_pos]
    )]) b.toList (by simp)

@[simp]
lemma circuitZip_vertex {hb} : (circuitZip a b hb).vertex = a.toList ++ [a.head] := by
  simp [circuitZip]

@[simp]
lemma circuitZip_edge {hb} : (circuitZip a b hb).edge = b.toList := by
  simp [circuitZip]

@[simp]
lemma circuitZip_wellFormed {hb} : (circuitZip a b hb).WellFormed :=
  WList.wellFormed_of_nodup <| by simpa

@[simp]
lemma circuitZip_vertex_getElem {hb} {i : ℕ} (hi : i + 1 < (circuitZip a b hb).vertex.length) :
    (circuitZip a b hb).vertex[i] = a[i]'(by simpa using hi) := by
  cases a using vector_in

variable {n : ℕ} {a : ZMod n → α} {b : ZMod n → β}

-- lemma foo [NeZero n] : ((List.range n).map (fun (i : ℕ) ↦ a i)).Nodup ↔ a.Injective := by
--   obtain rfl | n := n
--   · exact False.elim <| NeZero.ne 0 rfl
--   simp only [List.nodup_iff_injective_getElem, List.getElem_map, List.getElem_range]
--   simp +contextual [Function.Injective, ZMod]
--   refine ⟨?_, fun h ↦ ?_⟩
--   ·
--     have := h (a₁ := i.cast (by simp)) (a₂ := j.cast (by simp))
--     simp at this





def cycleZip' {n : ℕ} (a : ZMod n → α) (b : ZMod n → β) (_ : b.Injective) : WList α β :=
    WList.zip
      ((List.range n).map (fun (i : ℕ) ↦ a i) ++ [a 0])
      ((List.range n).map (fun (i : ℕ) ↦ b i)) (by simp)

@[simp]
lemma cycleZip'_vertex {hb} :
    (cycleZip' a b hb).vertex = (List.range n).map (fun (i : ℕ) ↦ a i) ++ [a 0] := by
  simp [cycleZip']

@[simp]
lemma cycleZip'_edge {hb} : (cycleZip' a b hb).edge = (List.range n).map (fun (i : ℕ) ↦ b i) := by
  simp [cycleZip']

@[simp]
lemma cycleZip'_wellFormed {hb} : (cycleZip' a b hb).WellFormed := by
  refine WList.wellFormed_of_nodup ?_
  rw [cycleZip'_edge]
  refine List.nodup_range.map_on <|
    by simp +contextual [hb.eq_iff, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt]

@[simp]
lemma cycleZip'_length {hb} : (cycleZip' a b hb).length = n := by
  simp [← WList.length_edge]

@[simp]
lemma cycleZip'_nonempty [NeZero n] {hb} : (cycleZip' a b hb).Nonempty := by
  simp [← WList.length_ne_zero_iff, NeZero.ne n]

@[simp]
lemma cycleZip_first {hb} : (cycleZip' a b hb).first = a 0 := by
  cases n with simp [← vertex_head]

@[simp]
lemma cycleZip_vertex_getElem {hb} {i : ℕ} (hi : i < (cycleZip' a b hb).vertex.length) :
    (cycleZip' a b hb).vertex[i] = a i := by
  obtain rfl | hlt := (show i ≤ n by simpa using hi).eq_or_lt
  · simp
  simp only [cycleZip'_vertex]
  rw [List.getElem_append_left (by simpa)]
  simp

@[simp]
lemma cycleZip_last {hb} : (cycleZip' a b hb).last = a 0 := by
  cases n with simp [← vertex_getLast]

lemma cycleZip_edge_getElem {hb} {i : ℕ} (hi : i < (cycleZip' a b hb).edge.length) :
    (cycleZip' a b hb).edge[i] = b i := by
  simp

@[simp]
lemma cycleZip'_isClosed {hb} : (cycleZip' a b hb).IsClosed := by
  simp [IsClosed]


@[simp]
lemma cycleZip_tail_vertex_rotate {hb} [NeZero n] :
    (cycleZip' a b hb).tail.vertex.rotate 1 = := by


@[simp]
lemma cycleZip_tail_vertex_nodup_iff {hb} [NeZero n] :
    (cycleZip' a b hb).tail.vertex.Nodup ↔ a.Injective := by
  cases n with
  | zero => exact False.elim <| NeZero.ne 0 rfl
  | succ n =>
    rw [← List.nodup_reverse]
    simp


variable {a : List α} {b : List β}

def cycleZip (a : List α) (b : List β) (hab : a.length = b.length) (ha : a ≠ []) (_ : b.Nodup) :
    WList α β :=
  WList.zip (a.concat (a.head ha)) b (by simpa using hab.symm)

@[simp]
lemma cycleZip_vertex (a : List α) (b : List β) {hab ha hb} :
    (cycleZip a b hab ha hb).vertex = a ++ [a.head ha] := by
  simp [cycleZip]

@[simp]
lemma cycleZip_edge (a : List α) (b : List β) {hab ha hb} : (cycleZip a b hab ha hb).edge = b := by
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

end WList

namespace Graph

variable {n : ℕ}

def circuitOn' {n : ℕ} (a : ZMod n → α) (b : ZMod n → β) (hb : b.Injective) : Graph α β :=
  match n with
  | 0 => ⊥
  | n + 1 => WList.toGraph <| (WList.cycleZip
    ((List.range (n + 1)).map fun (i : ℕ) ↦ a i) ((List.range (n + 1)).map fun (i : ℕ) ↦ b i)
    (by simp) (by simp) (List.nodup_range.map_on <| by
      simp +contextual [hb.eq_iff, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt]))



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

-- lemma circuitOn_isLink_iff_getElem {a b hab ha hb} {e : β} {x y : α} :
--     (circuitOn a b hab ha hb).IsLink e x y ↔
--       (e = b.getLast (by grind) ∧ s(x,y) = s(a.getLast ha, a.head ha)) ∨
--       (∃ (i : ℕ) (hi : i + 1 < a.length), e = b[i] ∧ s(x,y) = s(a[i], a[i + 1])) := by
--   cases a with
--   | nil => simp at ha
--   | cons u a => cases b with
--     | nil => simp at hab
--     | cons f b =>

--     rw [circuitOn, WList.WellFormed.toGraph_isLink (by simp), WList.cycleZip,
--       WList.isLink_iff_vertex_get]
--     refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--     ·
    -- simp only [List.head_cons, List.concat_eq_append, List.cons_append, WList.zip_cons_cons,
    --   WList.cons_edge, WList.zip_edge, WList.cons_vertex, WList.zip_vertex, List.getElem_cons_succ,
    --   Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, WList.cons_length, WList.zip_length,
    --   Order.lt_add_one_iff, List.length_cons, Order.add_one_le_iff]
    -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩

variable {n : ℕ}

/-- A canonical cycle graph on `ZMod n`, where edge `i : ZMod n` joins vertices `i, i + 1`. -/
@[simps]
def cycle (n : ℕ) : Graph (ZMod n) (ZMod n) where
  vertexSet := Set.univ
  IsLink e i j := (e = i ∧ j = i + 1) ∨ (e = j ∧ i = j + 1)
  isLink_symm := by grind [Symmetric]
  eq_or_eq_of_isLink_of_isLink := by grind
  edge_mem_iff_exists_isLink := by grind
  left_mem_of_isLink := by simp

lemma cycle_adj_add (i : ZMod n) : (cycle n).Adj i (i + 1) := by
  simp [cycle, Adj]

lemma cycle_adj_sub (i : ZMod n) : (cycle n).Adj i (i - 1) := by
  simp [cycle, Adj]

@[simp]
lemma cycle_inc_iff {e x} : (cycle n).Inc e x ↔ e = x ∨ e = x - 1 := by
  obtain rfl | hne := eq_or_ne e x
  · simp [Inc, cycle_isLink]
  simp [Inc, hne, eq_sub_iff_add_eq, eq_comm]

lemma cycle_eq_circuitOn (n : ℕ) [NeZero n] :
    cycle n = Graph.circuitOn ((List.range n).map Nat.cast) ((List.range n).map Nat.cast)
      rfl (by simp [NeZero.ne n])
      (List.nodup_range.map_on <| by
        simp +contextual [List.mem_range, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt]) := by
  _



end Graph

#exit

-- /-- The `WList α α` corresponding to a cycle
-- whose vertices and edges are both the terms in the list.
-- So `cycleWList [1,2,3] = [1,1,2,2,3,3,1] -/
-- def cycleWList {α : Type*} (a : List α) (ha : a ≠ []) : WList α α :=
--   WList.zip (a.concat (a.head ha)) a (by simp)

-- lemma cycleWList_wellFormed {ha : a ≠ []} (hnd : a.Nodup) : (cycleWList a ha).WellFormed :=
--   WList.wellFormed_of_nodup <| by simpa [cycleWList]

-- @[simp]
-- lemma cycleWList_vertex {α : Type*} (a : List α) (ha : a ≠ []) :
--     (cycleWList a ha).vertex = a ++ [a.head ha] := by
--   simp [cycleWList]

-- @[simp]
-- lemma cycleWList_edge {α : Type*} (a : List α) (ha : a ≠ []) :
--     (cycleWList a ha).edge = a := by
--   simp [cycleWList]

-- @[simp]
-- lemma cycleWList_isClosed (ha : a ≠ []) : (cycleWList a ha).IsClosed := by
--   cases a with
--   | nil => simp at ha
--   | cons x a => simp [WList.IsClosed, cycleWList]

-- @[simp]
-- lemma cycleWList_nonempty (ha : a ≠ []) : (cycleWList a ha).Nonempty := by
--   simp [cycleWList, WList.nonempty_iff_exists_edge, List.exists_mem_of_ne_nil _ ha]

-- @[simp]
-- lemma cycleWList_length (ha : a ≠ []) : (cycleWList a ha).length = a.length := by
--   rw [← WList.length_edge]
--   simp

-- lemma cycleWList_tail_vertex_nodup (ha : a ≠ []) (hnd : a.Nodup) :
--     (cycleWList a ha).tail.vertex.Nodup := by
--   cases a with
--   | nil => simp at ha
--   | cons x a =>
--     rw [← List.nodup_reverse]
--     simpa using hnd



namespace Graph

variable {α β : Type*} {n : ℕ} {i j : ZMod n}

def cycleWListNat (n : ℕ) [NeZero n] : WList (ZMod n) (ZMod n) :=
  cycleWList ((List.range n).map Nat.cast) (by simp [NeZero.ne])

@[simp]
lemma cycleWListNat_nodup [NeZero n] : (cycleWListNat n).edge.Nodup := by
  simp only [cycleWListNat, cycleWList_edge]
  refine List.nodup_range.map_on ?_
  simp only [List.mem_range]
  refine fun x hx y hy hxy ↦ ?_
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hxy

@[simp]
lemma cycleWListNat_length (n : ℕ) [NeZero n] :(cycleWListNat n).length = n := by
  simp [cycleWListNat]

@[simp]
lemma cycleWListNat_wellFormed [NeZero n] : (cycleWListNat n).WellFormed :=
  WList.wellFormed_of_nodup (by simp)

@[simp]
lemma cycleWListNat_edge_getElem {n i : ℕ} [NeZero n] {hi : i < (cycleWListNat n).edge.length} :
    (cycleWListNat n).edge[i] = i := by
  simp [cycleWListNat]

@[simp]
lemma cycleWListNat_vertex_getElem {n i : ℕ} [NeZero n] {hi : i < (cycleWListNat n).vertex.length} :
    (cycleWListNat n).vertex[i] = i := by
  simp only [cycleWListNat, cycleWList_vertex, List.head_map, List.head_range, Nat.cast_zero]
  obtain rfl | hlt := (show i ≤ n by simpa [cycleWListNat] using hi).eq_or_lt
  · simp
  rw [List.getElem_append_left (by simpa)]
  simp

/-- A canonical cycle graph on `ZMod n`, where edge `i : ZMod n` joins vertices `i, i + 1`. -/
@[simps]
def cycle (n : ℕ) : Graph (ZMod n) (ZMod n) where
  vertexSet := Set.univ
  IsLink e i j := (e = i ∧ j = i + 1) ∨ (e = j ∧ i = j + 1)
  isLink_symm := by grind [Symmetric]
  eq_or_eq_of_isLink_of_isLink := by grind
  edge_mem_iff_exists_isLink := by grind
  left_mem_of_isLink := by simp

lemma cycle_adj_add (i : ZMod n) : (cycle n).Adj i (i + 1) := by
  simp [cycle, Adj]

lemma cycle_adj_sub (i : ZMod n) : (cycle n).Adj i (i - 1) := by
  simp [cycle, Adj]

@[simp]
lemma cycle_inc_iff {e x} : (cycle n).Inc e x ↔ e = x ∨ e = x - 1 := by
  obtain rfl | hne := eq_or_ne e x
  · simp [Inc, cycle_isLink]
  simp [Inc, hne, eq_sub_iff_add_eq, eq_comm]

lemma cycle_eq_toGraph (n : ℕ) [NeZero n] : cycle n = WList.toGraph (cycleWListNat n) := by
  refine Graph.ext ?_ ?_
  · suffices ∀ (x : ZMod n), (∃ a < n, ↑a = x) ∨ x = 0 by
      simpa [Set.ext_iff, cycle, cycleWListNat, cycleWList]
    exact fun x ↦ .inl ⟨x.val, by simp [x.val_lt]⟩
  intro e x y
  rw [WList.WellFormed.toGraph_isLink (by simp), WList.isLink_iff_vertex_get]
  simp only [cycle_isLink, cycleWListNat_edge_getElem, cycleWListNat_vertex_getElem, Nat.cast_add,
    Nat.cast_one, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, cycleWListNat_length,
    exists_and_left, exists_prop]
  refine ⟨fun h ↦ ⟨e.val, ?_⟩, fun ⟨i, h⟩ ↦ by grind⟩
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, true_and]
  grind

lemma cycle_isCyclicWalk (n : ℕ) [NeZero n] : (cycle n).IsCyclicWalk (cycleWListNat n) := by
  rw [isCyclicWalk_iff, isTour_iff, isTrail_iff, and_iff_left cycleWListNat_nodup]
  refine ⟨⟨?_, by simp [cycleWListNat], by simp [cycleWListNat]⟩, ?_⟩
  · rw [cycle_eq_toGraph]
    exact WList.WellFormed.isWalk_toGraph (by simp)
  refine cycleWList_tail_vertex_nodup _ ?_
  convert cycleWListNat_nodup (n := n)
  simp [cycleWListNat]

lemma cycle_isCycle (n : ℕ) [NeZero n] : (cycle n).IsCycle := by
  rw [cycle_eq_toGraph]
  exact (cycle_isCyclicWalk n).toGraph_isCycle

lemma cycle_regular_two (n : ℕ) [NeZero n] : (cycle n).Regular 2 :=
  (cycle_isCycle n).regular_two

@[simp]
lemma cycle_vertexSet (n : ℕ) : V(cycle n) = Set.univ := rfl

@[simp]
lemma cycle_edgeSet (n : ℕ) : V(cycle n) = Set.univ := rfl

@[simp]
lemma cycle_degree (n : ℕ) [NeZero n] (x : ZMod n) : (cycle n).degree x = 2 :=
  (cycle_regular_two n).degree <| by simp






  -- sorry

  -- set L := (List.range n).map (Nat.cast : ℕ → ZMod n) ++ [0] with hL
  -- have aux (i : ZMod n) (d : ℕ) (hlt : i.val + d < n + 1) :
  --     L[i.val + d]'(by simpa [hL] using hlt) = i + d := by
  --   obtain (h_eq | hlt) := (show i.val + d ≤ n by lia).eq_or_lt
  --   · suffices 0 = i + d by simpa [hL, h_eq]
  --     simpa using congr_arg ((Nat.cast : ℕ → ZMod n)) h_eq.symm
  --   rw [List.getElem_append_left (by simpa)]
  --   simp
  -- have aux0 (i : ZMod n) (h : i.val < n + 1) :
  --   (List.map Nat.cast (List.range n) ++ [0])[i.val]'(by grind) = i :=
  --   by
  --   have := aux i 0 (by grind)
  --   sim p
  --   -- simp at this
  -- simp at aux0
  -- refine ⟨fun h ↦ ⟨e.val, by simp, e.val_lt, ?_⟩, fun h ↦ ?_⟩
  -- ·
  --   rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  --   · refine ⟨e.val, by simp, e.val_lt, .inl ⟨?_, ?_⟩⟩
  --     · convert aux e 0 (by grind)
  --       simp
  --     convert aux e 1 (by grind)
  --     simp
  --   refine ⟨e.val, ?_⟩
  -- rw [List.getElem_append_left (by simpa using e.val_lt), and_iff_right (by simp)]
  -- obtain rfl | hne := eq_or_ne e (-1)
  -- · obtain rfl | n := n; contradiction
  --   simp [ZMod.val_neg_one]
  -- rw [List.getElem_append_left, List.getElem_map]
  -- · simp
  -- simp only [List.length_map, List.length_range]
  -- obtain hlt | heq := (show e.val + 1 ≤ n by grind).lt_or_eq
  -- · assumption













-- lemma cycle_adj_iff : (cycle n).Adj i j ↔



/- Given a list `[a₁, a₂, a₃, .., a_k]`, the `WList -/



  -- WList.zip (((List.range n).map Nat.cast).concat 0) ((List.range n).map Nat.cast) (by simp)

-- lemma cycle_isCyclicWalk_WList (n : ℕ) [NeZero n] : (cycle n).IsCyclicWalk (cycleWList n) := by
--   rw [isCyclicWalk_iff, isTour_iff, isTrail_iff, nil_isWalk_iff
