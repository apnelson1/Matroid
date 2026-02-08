import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Card

open Set Function List Nat

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S S' T T' U V : Set α} {F F' R R': Set β}

/-- A `WList α β` is an alternating list `[v₀, e₁, v₁, ... , eₙ, vₙ]` where the `vᵢ` have type `α`
and the `eᵢ` have type `β`. The first and last terms always have type `α`.

The definition does not depend on `Graph`, but the intended use case is where `α` and `β` are the
vertex and edge types of some `G : Graph α β`, and the `WList` is though of as a walk of `G`.
The abstract definition allows us to easily express the idea that a particular
list of vertices and edges is a walk in more than one graph.

(Note that a `WList α β` may not correspond to an actual walk in any `Graph α β`.
For instance, if all `eᵢ` are equal, and there are at least three different `vᵢ`,
then such a graph would have to have an edge with more than two ends. )
 -/
inductive WList (α β : Type*) where
| nil (u : α) : WList α β
| cons (u : α) (e : β) (w : WList α β) : WList α β

namespace WList

def repr_aux [Repr α] [Repr β] (w : WList α β) (n : Nat) : Std.Format := match w with
| nil x => reprPrec x n
| cons x e w => reprPrec x n ++ " --" ++ reprPrec e n ++ "-> " ++ repr_aux w n

instance [Repr α] [Repr β] : Repr (WList α β) where
  reprPrec w n := "W[" ++ repr_aux w n ++ "]"

variable {w w₁ w₂ : WList α β}

@[simp, grind =]
lemma nil_inj_iff : (nil x : WList α β) = nil y ↔ x = y := by
  rw [nil.injEq]

@[simp, grind =]
lemma cons_inj_iff : cons x e w₁ = cons y f w₂ ↔ x = y ∧ e = f ∧ w₁ = w₂ := by
  induction w₁ with simp

/-! ## First and Last -/

/-- The first element of a `WList` -/
def first : WList α β → α
  | nil x => x
  | cons x _ _ => x

@[simp, grind =]
lemma nil_first : (nil x : WList α β).first = x := rfl

@[simp, grind =]
lemma first_cons : (cons x e w).first = x := rfl

def second : WList α β → α
| nil x => x
| cons _ _ w => w.first

@[simp, grind =] lemma second_nil : (nil x : WList α β).second = x := rfl
@[simp, grind =] lemma second_cons : (cons x e w).second = w.first := rfl
@[simp, grind =] lemma second_cons_cons : (cons x e (cons y f w)).second = y := rfl

def last : WList α β → α
  | nil x => x
  | cons _ _ w => w.last

@[simp, grind =] lemma last_cons : (cons x e w).last = w.last := rfl

@[simp, grind =] lemma nil_last : (nil x : WList α β).last = x := rfl

/-! ## Vertex/Edge Lists -/

/-- The list of vertices of a `WList` -/
def vertex : WList α β → List α
  | nil x => [x]
  | cons x _e w => x :: w.vertex

@[simp, grind .]
lemma vertex_ne_nil : w.vertex ≠ [] := by
  cases w with simp [vertex]

@[simp, grind =] lemma cons_vertex : (cons x e w).vertex = x :: w.vertex := rfl

@[simp, grind =] lemma nil_vertex : (nil x : WList α β).vertex = [x] := rfl

@[simp, grind =]
lemma vertex_head : w.vertex.head vertex_ne_nil = w.first := by
  cases w with rfl

@[simp, grind =]
lemma vertex_getLast {w : WList α β} : w.vertex.getLast vertex_ne_nil = w.last := by
  induction w with simp_all

@[simp, grind .]
lemma vertex_length_pos (w : WList α β) : 0 < w.vertex.length :=
  length_pos_of_ne_nil vertex_ne_nil

@[simp, grind =]
lemma vertex_getElem_zero (w : WList α β) : w.vertex[0] = w.first := by
  cases w with simp

/-- The list of edges of a `WList` -/
def edge : WList α β → List β
  | nil _ => []
  | cons _ e w => e :: w.edge

@[simp, grind =]
lemma nil_edge (x : α) : (nil x : WList α β).edge = [] := rfl

@[simp, grind =]
lemma cons_edge (x e) (w : WList α β) : (cons x e w).edge = e :: w.edge := rfl

/-- Two `WLists` with the same vertex and edge lists arae equal. -/
@[ext]
lemma ext_vertex_edge {w₁ w₂ : WList α β} (h_vertex : w₁.vertex = w₂.vertex)
    (h_edge : w₁.edge = w₂.edge) : w₁ = w₂ := by
  match w₁ with
  | nil u => cases w₂ with | _ => simp_all
  | cons u e w₁ => match w₂ with
    | nil u => simp_all
    | cons v f w₂ =>
    simp_all only [cons_vertex, List.cons.injEq, cons_edge, cons.injEq, true_and]
    exact ext_vertex_edge h_vertex.2 h_edge.2

/-! ### Membership -/

-- /-- `w.mem x` means that `x` is a vertex of `w`. Defined inductively for cleaner proofs. -/
-- protected inductive Mem : WList α β → α → Prop
--   | nil x : (nil x).Mem x
--   | cons_eq x e w : (cons x e w).Mem x
--   | cons u e {w x} (h : w.Mem x) : (cons u e w).Mem x


instance : Membership α (WList α β) where
  mem w x := x ∈ w.vertex

@[simp, grind =]
lemma mem_vertex : (x ∈ w.vertex) = (x ∈ w) := rfl

@[simp, grind =]
lemma mem_nil_iff : x ∈ (nil u : WList α β) ↔ x = u := by
  simp [← mem_vertex]

@[simp, grind =]
lemma mem_cons_iff : x ∈ (cons u e w) ↔ x = u ∨ x ∈ w := by
  simp [← mem_vertex]

lemma eq_or_ne_mem_of_mem_cons (h : x ∈ cons u e w) : x = u ∨ (x ≠ u ∧ x ∈ w) := by
  obtain rfl | hne := eq_or_ne x u
  · simp
  exact .inr ⟨hne, by simpa [hne] using h⟩

instance [DecidableEq α] : Decidable (x ∈ w) :=
  inferInstanceAs <| Decidable (x ∈ w.vertex)

@[simp, grind .] lemma first_mem : w.first ∈ w := by
  cases w with simp

@[simp, grind .] lemma second_mem : w.second ∈ w := by
  cases w with simp

@[simp, grind .] lemma last_mem {w : WList α β} : w.last ∈ w := by
  induction w with simp_all

/-- `w.UniqueMem x` means that `x : α` appears in `w` exactly once. -/
protected inductive UniqueMem : WList α β → α → Prop
  | nil x : (nil x).UniqueMem x
  | cons_eq {x} e w (h : x ∉ w) : (cons x e w).UniqueMem x
  | cons_ne {x u} (h : u ≠ x) e w (hw : w.UniqueMem x) : (cons u e w).UniqueMem x

/-! ### Vertex/Edge Sets -/

protected def vertexSet (w : WList α β) : Set α := {x | x ∈ w}

scoped notation "V(" w ")" => WList.vertexSet w

protected def edgeSet (w : WList α β) : Set β := {e | e ∈ w.edge}

scoped notation "E(" w ")" => WList.edgeSet w

@[simp, grind =]
lemma mem_vertexSet_iff : x ∈ V(w) ↔ x ∈ w := Iff.rfl

@[simp, grind =]
lemma mem_edgeSet_iff : e ∈ E(w) ↔ e ∈ w.edge := Iff.rfl

@[simp, grind =]
lemma nil_vertexSet : V((nil x : WList α β)) = {x} := by
  simp [WList.vertexSet]

@[simp, grind =]
lemma nil_edgeSet : E((nil x : WList α β)) = ∅ := by
  simp [WList.edgeSet]

@[simp, grind =] lemma cons_vertexSet : V(cons x e w) = insert x V(w) := by
  simp [WList.vertexSet, mem_cons_iff, Set.ext_iff]

@[simp, grind =] lemma cons_edgeSet : E(cons x e w) = insert e E(w) := by
  simp only [WList.edgeSet, cons_edge, mem_cons]
  rfl

@[simp]
lemma edgeSet_finite (w : WList α β) : E(w).Finite := by
  induction w with simp_all

@[simp]
lemma vertexSet_nonempty (w : WList α β) : V(w).Nonempty := by
  cases w with simp

@[simp]
lemma vertexSet_finite (w : WList α β) : V(w).Finite := by
  induction w with simp_all

lemma vertexSet_disjoint_iff : _root_.Disjoint V(w₁) V(w₂) ↔ w₁.vertex.Disjoint w₂.vertex := by
  simp [Set.disjoint_left, List.disjoint_left]

lemma edgeSet_disjoint_iff : _root_.Disjoint E(w₁) E(w₂) ↔ w₁.edge.Disjoint w₂.edge := by
  simp [Set.disjoint_left, List.disjoint_left]

@[simp]
lemma vertex_toFinset_toSet [DecidableEq α] (w : WList α β) :
    (w.vertex.toFinset : Set α) = V(w) := by
  induction w with
  | nil u => simp
  | cons u e W ih =>
    ext
    simp [← ih]

@[simp]
lemma vertex_disjoint_iff : w₁.vertex.Disjoint w₂.vertex ↔ Disjoint V(w₁) V(w₂) := by
  rw [disjoint_iff_forall_ne]
  refine ⟨fun h x hx₁ y hy₂ heq => ?_, fun h x hx₁ hx₂ => h hx₁ hx₂ rfl⟩
  subst y
  exact h hx₁ hy₂

@[simp]
lemma edge_disjoint_iff : w₁.edge.Disjoint w₂.edge ↔ Disjoint E(w₁) E(w₂) := by
  rw [disjoint_iff_forall_ne]
  refine ⟨fun h x hx₁ y hy₂ heq => ?_, fun h x hx₁ hx₂ => h hx₁ hx₂ rfl⟩
  subst y
  exact h hx₁ hy₂

/-! ## Emptiness -/

/-- `Nil w` means that `w : WList α β` has no edges -/
inductive Nil : WList α β → Prop
  | nil (x : α) : Nil (nil x)

@[simp, grind .]
lemma nil_nil : Nil (nil x (β := β)) :=
  Nil.nil ..

@[simp, grind .]
lemma not_nil_cons (w : WList α β) (x) (e) : ¬ Nil (w.cons x e) := by
  rintro ⟨_⟩

lemma Nil.eq_nil_of_mem (h : w.Nil) (hxw : x ∈ w) : w = .nil x := by
  induction w with simp_all

lemma Nil.eq_nil_first (h : w.Nil) : w = .nil w.first :=
  h.eq_nil_of_mem <| by simp

lemma Nil.eq_nil_last (h : w.Nil) : w = .nil w.last :=
  h.eq_nil_of_mem <| by simp

lemma Nil.first_eq_last (h : w.Nil) : w.first = w.last := by
  cases h with rfl

lemma nil_iff_eq_nil : Nil w ↔ ∃ x, w = nil x := by
  induction w with simp

lemma first_eq_last_iff (hnodup : w.vertex.Nodup) : w.first = w.last ↔ w.Nil :=
  ⟨fun h ↦ by cases w with simp_all, Nil.first_eq_last⟩

/-- `Nonempty w` means that `w : WList α β` has at least one edge -/
protected inductive Nonempty : WList α β → Prop
  | cons (x e) (w : WList α β) : WList.Nonempty (cons x e w)

@[simp, grind .]
lemma cons_nonempty (x e) (w : WList α β) : (cons x e w).Nonempty := by
  apply Nonempty.cons

@[simp, grind .]
lemma nil_not_nonempty : ¬ (nil x : WList α β).Nonempty := by
  rintro ⟨_, _, _⟩

lemma nil_injective : Injective (nil : α → WList α β) := by
  rintro x y h
  rwa [nil.injEq] at h

@[simp, push, grind =] protected lemma not_nonempty_iff : ¬ w.Nonempty ↔ w.Nil := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
  simp only [cons_nonempty, not_true_eq_false, false_iff]
  rintro ⟨_⟩
alias ⟨_, Nil.not_nonempty⟩ := not_nonempty_iff

@[simp, push, grind =] lemma not_nil_iff : ¬ w.Nil ↔ w.Nonempty := by
  rw [← WList.not_nonempty_iff, not_not]
alias ⟨_, Nonempty.not_nil⟩ := not_nil_iff

lemma Nonempty.exists_cons (hw : w.Nonempty) : ∃ x e w', w = .cons x e w' := by
  cases hw with simp

lemma nonempty_iff_exists_cons : w.Nonempty ↔ ∃ x e w', w = cons x e w' := by
  induction w with simp_all

lemma first_ne_last_iff (hnodup : w.vertex.Nodup) : w.first ≠ w.last ↔ w.Nonempty := by
  simp [first_eq_last_iff hnodup]

lemma nil_or_nonempty (w : WList α β) : w.Nil ∨ w.Nonempty := by
  induction w with simp

lemma exists_eq_nil_or_nonempty (w : WList α β) : (∃ x, w = nil x) ∨ w.Nonempty := by
  induction w with simp

instance DecidableNonempty (w : WList α β) : Decidable w.Nonempty := by
  match w with
  | nil _ =>
    simp only [nil_not_nonempty]
    exact instDecidableFalse
  | cons v e w =>
    simp only [cons_nonempty]
    exact instDecidableTrue

/-- The first edge of a nonempty `WList` -/
def Nonempty.firstEdge : (w : WList α β) → (hw : w.Nonempty) → β
  | nil x, hw => by simp at hw
  | .cons x e w, hw => e

@[simp, grind =]
lemma Nonempty.firstEdge_cons (x e) (w : WList α β) : (cons_nonempty x e w).firstEdge = e := rfl

@[simp]
lemma Nonempty.firstEdge_mem (hw : w.Nonempty) : hw.firstEdge w ∈ w.edge := by
  induction w with | nil => simp at hw | cons => simp

lemma Nonempty.edge_ne_nil (hw : w.Nonempty) : w.edge ≠ [] := by
  cases hw with simp

lemma Nonempty.firstEdge_eq_head (hw : w.Nonempty) :
    hw.firstEdge = w.edge.head hw.edge_ne_nil := by
  cases hw with simp

@[simp, grind .]
lemma Nonempty.edgeSet_nonempty (h : w.Nonempty) : E(w).Nonempty := by
  cases h with simp

lemma nonempty_iff_exists_edge : w.Nonempty ↔ ∃ e, e ∈ w.edge := by
  induction w with simp_all
alias ⟨Nonempty.exists_edge, _⟩:= nonempty_iff_exists_edge

lemma nil_iff_edge_nil : w.Nil ↔ w.edge = [] := by
  match w with
  | .nil u => simp
  | .cons u e w => simp

lemma Nonempty.first_ne_last_of_nodup (hne : w.Nonempty) (hv : w.vertex.Nodup) :
    w.first ≠ w.last := by
  obtain ⟨x, e, w, rfl⟩ := hne.exists_cons
  obtain ⟨hxw, hh⟩ := by simpa using hv
  simp only [first_cons, last_cons, ne_eq]
  contrapose! hxw
  exact hxw ▸ last_mem

/-! ### Nontriviality -/

/-- a `WList` is nontrivial if it has at least two edges. -/
inductive Nontrivial : WList α β → Prop
| cons_cons (u e v f) (w : WList α β) : Nontrivial (cons u e (cons v f w))

attribute [simp] Nontrivial.cons_cons

lemma Nontrivial.nonempty (hw : w.Nontrivial) : w.Nonempty := by
  cases hw with | cons_cons  => exact Nonempty.cons ..

@[simp]
lemma not_nontrivial_nil : ¬ (nil x : WList α β).Nontrivial := by
  rintro ⟨_⟩

@[simp]
lemma not_nontrivial_cons_nil : ¬ (cons x e (nil y)).Nontrivial := by
  rintro ⟨_⟩

@[simp]
lemma cons_nontrivial_iff : (cons u e w).Nontrivial ↔ w.Nonempty := by
  induction w with simp_all

lemma Nontrivial.first_ne_second_of_nodup (hnt : w.Nontrivial) (hv : w.vertex.Nodup) :
    w.first ≠ w.second := by
  obtain ⟨u, e, v, f, w⟩ := hnt
  simp_all

lemma Nontrivial.second_ne_last_of_nodup (hnt : w.Nontrivial) (hv : w.vertex.Nodup) :
    w.second ≠ w.last := by
  obtain ⟨u, e, v, f, w⟩ := hnt
  obtain ⟨hxw, hh⟩ := by simpa using hv
  simp only [second_cons, first_cons, last_cons, ne_eq]
  rintro rfl
  exact hh.1 last_mem

instance : Decidable w.Nontrivial := by
  match w with
  | nil _ =>
    simp only [not_nontrivial_nil]
    infer_instance
  | cons _ _ w =>
    simp only [cons_nontrivial_iff]
    infer_instance

/-! ### Length -/

/-- The number of edges in a `WList`. Change this to `length w.edge` ?? -/
def length : WList α β → ℕ
| nil _ => 0
| cons _ _ w => w.length + 1

@[simp]
lemma length_edge (w : WList α β) : w.edge.length = w.length := by
  induction w with simp_all [length, edge]

@[simp]
lemma length_vertex (w : WList α β) : w.vertex.length = w.length + 1 := by
  induction w with simp_all [length, vertex]

@[simp] lemma cons_length : (cons x e w).length = w.length + 1 := rfl

@[simp] lemma nil_length : (nil x : WList α β).length = 0 := rfl

@[simp]
lemma length_eq_zero : w.length = 0 ↔ w.Nil := by
  induction w with simp

lemma length_ne_zero_iff : w.length ≠ 0 ↔ w.Nonempty := by
  simp

@[simp]
lemma length_pos_iff : 0 < w.length ↔ w.Nonempty := by
  simp [Nat.pos_iff_ne_zero]

@[simp]
lemma one_le_length_iff : 1 ≤ w.length ↔ w.Nonempty := by
  rw [Nat.one_le_iff_ne_zero, Nat.ne_zero_iff_zero_lt, length_pos_iff]

lemma Nonempty.length_pos (hw : w.Nonempty) : 0 < w.length :=
  length_pos_iff.2 hw

lemma encard_vxSet_of_nodup (h : w.vertex.Nodup) : V(w).encard = w.length + 1 := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
  · simp only [cons_vertex, nodup_cons, mem_vertex] at h
    simp only [cons_vertexSet, cons_length, cast_add, cast_one]
    rw [encard_insert_of_notMem (by simpa using h.1), ih h.2]

@[simp]
lemma one_lt_length_iff : 1 < w.length ↔ w.Nontrivial := by
  cases w with | nil => simp | cons _ _ w => cases w with simp

@[simp]
lemma two_le_length_iff : 2 ≤ w.length ↔ w.Nontrivial := by
  cases w with | nil => simp | cons _ _ w => cases w with simp

lemma Nontrivial.one_lt_length (hw : w.Nontrivial) : 1 < w.length := by
  simpa

lemma Nontrivial.two_le_length (hw : w.Nontrivial) : 2 ≤ w.length := by
  rw [two_le_length_iff]
  exact hw

lemma Nonempty.nontrivial_of_length_ne_one (hw : w.Nonempty) (hne : w.length ≠ 1) :
    w.Nontrivial := by
  match w with
  | nil x => simp at hw
  | .cons u e (nil v) => simp at hne
  | .cons u e (.cons v f w) => simp_all

protected lemma length_eq_one_iff : w.length = 1 ↔ ∃ u e v, w = cons u e (nil v) := by
  match w with
  | .nil u => simp
  | .cons u e w => simp [nil_iff_eq_nil]

protected lemma length_eq_two_iff :
    w.length = 2 ↔ ∃ a e b f c, w = cons a e (cons b f (nil c)) := by
  match w with
  | .nil u => simp
  | .cons u e w => simp_all [w.length_eq_one_iff]

lemma vertex_toFinset_card_le [DecidableEq α] (w : WList α β) :
    w.vertex.toFinset.card ≤ w.length + 1 := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [cons_vertex, toFinset_cons, cons_length]
    grw [Finset.card_insert_le]
    simpa

lemma edge_toFinset_card_le [DecidableEq β] (w : WList α β) :
    w.edge.toFinset.card ≤ w.length := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [cons_edge, toFinset_cons, cons_length]
    grw [Finset.card_insert_le, Nat.add_le_add_iff_right]
    assumption

/-- `w.DInc e x y` means that `w` contains `[x,e,y]` as a contiguous sublist.
(`DInc` stands for 'directed incidence')` -/
protected inductive DInc : WList α β → β → α → α → Prop
  | cons_left (x e w) : (cons x e w).DInc e x w.first
  | cons (u f) {w e x y} (hw : w.DInc e x y) : (cons u f w).DInc e x y

@[simp]
lemma not_nil_dInc (u : α) (e : β) x y : ¬ (WList.nil u).DInc e x y := by
  rintro ⟨_⟩

@[simp]
lemma dInc_cons_iff : (cons u f w).DInc e x y ↔ (u = x ∧ f = e ∧ w.first = y) ∨ w.DInc e x y := by
  refine ⟨fun h ↦ by cases h with simp_all, ?_⟩
  rintro (⟨rfl, rfl, rfl⟩ | h)
  · apply DInc.cons_left
  apply h.cons

lemma DInc.left_mem (h : w.DInc e x y) : x ∈ w.vertex := by
  induction h with simp_all

lemma DInc.right_mem (h : w.DInc e x y) : y ∈ w.vertex := by
  induction h with simp_all

lemma DInc.edge_mem (h : w.DInc e x y) : e ∈ w.edge := by
  induction h with simp_all

lemma exists_dInc_of_mem_edge (he : e ∈ w.edge) : ∃ x y, w.DInc e x y := by
  induction w with
  | nil => simp at he
  | cons u f w ih =>
    obtain (rfl : e = f) | (hew : e ∈ w.edge) := by simpa using he
    · exact ⟨u, w.first, DInc.cons_left ..⟩
    obtain ⟨x, y, h⟩ := ih hew
    exact ⟨x, y, h.cons ..⟩

lemma mem_edge_iff_exists_dInc : e ∈ w.edge ↔ ∃ x y, w.DInc e x y :=
  ⟨exists_dInc_of_mem_edge, fun ⟨_, _, h⟩ ↦ h.edge_mem⟩

lemma DInc.sublist (h : w.DInc e x y) : [x,y] <+ w.vertex := by
  induction h with simp_all

lemma DInc.ne_first (h : w.DInc e x y) (hnd : w.vertex.Nodup) : y ≠ w.first := by
  cases h with
  | cons_left x e w =>
    rintro rfl
    simp at hnd
  | @cons u f w e x y hw =>
    rintro rfl
    simp only [cons_vertex, nodup_cons, mem_vertex] at hnd
    exact hnd.1 hw.right_mem

lemma DInc.ne_last (h : w.DInc e x y) (hnd : w.vertex.Nodup) : x ≠ w.last := by
  induction h with
  | cons_left x e w =>
    simp_all only [cons_vertex, nodup_cons, mem_vertex, last_cons, ne_eq]
    rintro rfl
    simp at hnd
  | cons => rintro rfl; simp_all

lemma DInc.nonempty (h : w.DInc e x y) : w.Nonempty := by
  cases h with simp

-- in a WList with no repeated edges, each edge is part of exactly one DInc triplet
lemma dInc_iff_eq_of_dInc_of_edge_nodup (hw : w.edge.Nodup) (he : w.DInc e u v) :
    w.DInc e x y ↔ x = u ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil => simp_all
  | cons z f w IH =>
    simp only [cons_edge, nodup_cons, dInc_cons_iff] at hw h he
    obtain ⟨rfl, rfl, rfl⟩ | h := h <;> obtain ⟨rfl, he, rfl⟩ | he := he
    · tauto
    · exact hw.1 he.edge_mem |>.elim
    · subst f
      exact hw.1 h.edge_mem |>.elim
    apply IH <;> first | assumption | tauto

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_left (hw : w.vertex.Nodup) (hu : w.DInc e u v) :
    w.DInc f u y ↔ f = e ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with | nil => simp_all | cons u' f' w IH =>
  simp_all only [cons_vertex, List.nodup_cons, mem_vertex, dInc_cons_iff, forall_const]
  obtain ⟨rfl, rfl, rfl⟩ | h := h <;> obtain ⟨hu, rfl, rfl⟩ | hu := hu
  · tauto
  · exact hw.1 hu.left_mem |>.elim
  · exact hw.1 (hu ▸ h.left_mem) |>.elim
  exact IH hu h

lemma exists_left_edge (hyw : y ∈ w) (hy : y ≠ w.first) : ∃ e x, w.DInc e x y := by
  induction w generalizing y with | nil u => simp_all | cons u e w IH =>
  obtain (rfl | hne) := eq_or_ne y w.first
  · use e, u
    tauto
  · simp_all only [ne_eq, mem_cons_iff, first_cons, dInc_cons_iff, false_or]
    obtain ⟨f, x, h⟩ := IH hyw hne
    use f, x, Or.inr h

lemma exists_right_edge (hxw : x ∈ w) (hx : x ≠ w.last) : ∃ e y, w.DInc e x y := by
  induction w generalizing x with simp_all only [ne_eq, mem_cons_iff, last_cons, dInc_cons_iff,
  mem_nil_iff, nil_last, ne_eq, not_true_eq_false]
  | cons u e w IH =>
    obtain (rfl | hxw) := hxw
    · use e, w.first
      tauto
    · obtain ⟨f, x, h⟩ := IH hxw hx
      use f, x, Or.inr h

instance {w : WList α β} {e : β} {x y : α} [DecidableEq α] [DecidableEq β] :
    Decidable (w.DInc e x y) := by
  match w with
  | nil _ =>
    simp only [not_nil_dInc]
    infer_instance
  | cons v f w =>
    simp only [dInc_cons_iff]
    have := instDecidableDIncOfDecidableEq (w := w) (e := e) (x := x) (y := y)
    infer_instance

/-- `w.IsLink e x y` means that `w` contains `[x,e,y]` or `[y,e,x]` as a contiguous sublist. -/
protected inductive IsLink : WList α β → β → α → α → Prop
  | cons_left (x e w) : (cons x e w).IsLink e x w.first
  | cons_right (x e w) : (cons x e w).IsLink e w.first x
  | cons (u f) {w e x y} (hw : w.IsLink e x y) : (cons u f w).IsLink e x y

@[simp]
protected lemma IsLink.not_nil : ¬ (nil u (β := β)).IsLink e x y := by
  rintro (_ | _ | _)

lemma DInc.isLink (h : w.DInc e x y) : w.IsLink e x y := by
  induction h with
  | cons_left x e w => exact IsLink.cons_left x e w
  | cons u f hw ih => exact IsLink.cons u f ih

protected lemma IsLink.symm (h : w.IsLink e x y) : w.IsLink e y x := by
  induction h with
  | cons_left => apply cons_right
  | cons_right => apply cons_left
  | cons _ _ _ ih => apply ih.cons

lemma isLink_iff_dInc : w.IsLink e x y ↔ w.DInc e x y ∨ w.DInc e y x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim DInc.isLink fun h' ↦ h'.isLink.symm⟩
  induction h with
  | cons_left x e w => exact .inl <| DInc.cons_left ..
  | cons_right x e w => exact .inr <| DInc.cons_left ..
  | cons u f hw ih => exact ih.elim (.inl ∘ DInc.cons _ _) (.inr ∘ DInc.cons _ _)

protected lemma IsLink.of_cons (hw : (WList.cons u f w).IsLink e x y) (hef : e ≠ f) :
    w.IsLink e x y := by
  cases hw with | cons_left => contradiction | cons_right => contradiction | cons => assumption

lemma isLink_cons_iff' : (cons u f w).IsLink e x y ↔
    (f = e ∧ (x = u ∧ y = w.first ∨ x = w.first ∧ y = u)) ∨ w.IsLink e x y := by
  refine ⟨fun h ↦ by cases h with simp_all, ?_⟩
  rintro (⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | h)
  · apply IsLink.cons_left
  · apply IsLink.cons_right
  apply h.cons

lemma isLink_cons_iff : (cons u f w).IsLink e x y ↔
    (f = e ∧ (s(x,y) = s(u,w.first))) ∨ w.IsLink e x y := by
  rw [isLink_cons_iff', Sym2.eq_iff]

lemma IsLink.left_mem (h : w.IsLink e x y) : x ∈ w := by
  induction h with simp_all

lemma IsLink.right_mem (h : w.IsLink e x y) : y ∈ w :=
  h.symm.left_mem

lemma IsLink.edge_mem (h : w.IsLink e x y) : e ∈ w.edge := by
  induction h with simp_all

lemma IsLink.nonempty (h : w.IsLink e x y) : w.Nonempty := by
  cases h with simp

lemma exists_isLink_of_mem_edge (he : e ∈ w.edge) : ∃ x y, w.IsLink e x y := by
  obtain ⟨x, y, h⟩ := exists_dInc_of_mem_edge he
  exact ⟨x, y, h.isLink⟩

lemma IsLink.eq_firstEdge_of_isLink_first (he : w.IsLink e w.first x) (hnd : w.vertex.Nodup) :
    e = he.nonempty.firstEdge := by
  cases w with
  | nil u => simp at he
  | cons u f w =>
    simp only [Nonempty.firstEdge_cons]
    simp only [cons_vertex, nodup_cons, mem_vertex] at hnd
    cases he with
    | cons_left => rfl
    | cons_right => rfl
    | cons u f hw =>
      simp only [first_cons] at hw
      exact (hnd.1 hw.left_mem).elim

lemma Nonempty.mem_iff_exists_isLink (hw : w.Nonempty) : x ∈ w ↔ ∃ y e, w.IsLink e x y := by
  refine ⟨fun h ↦ ?_, fun ⟨y, e, h⟩ ↦ h.left_mem⟩
  induction w with
  | nil => simp at hw
  | cons u e w ih =>
    obtain (rfl : x = u) | (hxw : x ∈ w) := by simpa using h
    · exact ⟨w.first, e, IsLink.cons_left x e w⟩
    cases w with
    | nil v =>
      refine ⟨u, e, ?_⟩
      obtain rfl : x = v := by simpa using hxw
      apply IsLink.cons_right
    | cons v f w =>
      obtain ⟨y, e', h⟩ := ih (by simp) hxw
      exact ⟨y, e', IsLink.cons _ _ h⟩

instance {w : WList α β} {e : β} {x y : α} [DecidableEq α] [DecidableEq β] :
    Decidable (w.IsLink e x y) := by
  match w with
  | nil _ =>
    simp only [IsLink.not_nil]
    infer_instance
  | cons v f w =>
    rw [isLink_cons_iff']
    have := instDecidableIsLinkOfDecidableEq (w := w) (e := e) (x := x) (y := y)
    infer_instance

/-- A `WList` is `WellFormed` if each edge appears only with the same ends. -/
def WellFormed (w : WList α β) : Prop :=
  ∀ ⦃e x₁ x₂ y₁ y₂⦄, w.IsLink e x₁ x₂ → w.IsLink e y₁ y₂ → s(x₁, x₂) = s(y₁, y₂)

@[simp]
lemma nil_wellFormed : (nil x (β := β)).WellFormed := by
  intro e x₁ x₂ y₁ y₂ h₁ h₂
  simp at h₁

lemma WellFormed.of_cons (hw : (cons u f w).WellFormed) : w.WellFormed := by
  intro e x₁ x₂ y₁ y₂ h₁ h₂
  have := @hw e x₁ x₂ y₁ y₂
  simpa [isLink_cons_iff', h₁, h₂] using this

/-- The set of ends of `e` in `w` -/
def endsOf (w : WList α β) (e : β) : Set α := {x | ∃ y, w.IsLink e x y}

section indices

/-! ### Indices -/

/-- The `n`th vertex of `w`, or the last vertex if `n > w.length`. -/
protected def get : WList α β → ℕ → α
  | nil x, _ => x
  | cons x _ _, 0 => x
  | cons _ _ w, n+1 => w.get n

@[simp]
lemma get_nil (x : α) (n : ℕ) : (nil x (β := β)).get n = x := rfl

@[simp]
lemma get_zero (w : WList α β) : w.get 0 = w.first := by
  cases w with rfl

@[simp]
lemma get_cons_add (x e) (w : WList α β) (n : ℕ) : (cons x e w).get (n+1) = w.get n := rfl

@[simp]
lemma get_length (w : WList α β) : w.get w.length = w.last := by
  induction w with simp_all

@[simp]
lemma get_mem (w : WList α β) (n : ℕ) : w.get n ∈ w := by
  induction n generalizing w with
  | zero => simp
  | succ n IH => cases w with simp [IH]

lemma get_of_length_le {n} (hn : w.length ≤ n) : w.get n = w.last := by
  induction w generalizing n with | nil => simp | cons => induction n with simp_all

lemma get_eq_getD_vertex (w : WList α β) (n) : w.get n = w.vertex.getD n w.last := by
  induction n generalizing w with
  | zero => simp
  | succ n IH => cases w with simp [IH]

lemma DInc_get_get_succ {n : ℕ} (hn : n < w.length) :
    have hw : n < w.edge.length := by simpa using hn
    w.DInc (w.edge[n]) (w.get n) (w.get (n+1)) := by
  simp only
  induction w generalizing n with
  | nil => simp at hn
  | cons u e w ih =>
  · cases n with
  | zero => simp
  | succ n => apply (@ih n (by simpa using hn)).cons

lemma exists_dInc_get_get_succ {n : ℕ} (hn : n < w.length) :
    ∃ e, w.DInc e (w.get n) (w.get (n+1)) :=
  ⟨_, DInc_get_get_succ hn⟩

variable [DecidableEq α]

/-- The index of a vertex in a `WList`. Equal to `w.length + 1` if the vertex doesn't appear. -/
protected def idxOf : WList α β → α → ℕ
  | nil u, x => if u = x then 0 else 1
  | cons u _ w, x => if u = x then 0 else w.idxOf x + 1

@[simp]
lemma idxOf_nil (u x : α) : ((nil u (β := β)).idxOf x) = if u = x then 0 else 1 := rfl

lemma idxOf_cons (u e) (w : WList α β) :
  (cons u e w).idxOf x = if u = x then 0 else w.idxOf x + 1 := rfl

@[simp]
lemma idxOf_cons_self (u e) (w : WList α β) : (cons u e w).idxOf u = 0 := by
  simp [idxOf_cons]

@[simp]
lemma idxOf_cons_eq_zero (w) : (cons u e w).idxOf x = 0 ↔ u = x := by
  simp [idxOf_cons]

@[simp]
lemma idxOf_cons_ne (hne : u ≠ x) (e) (w : WList α β) :
    (cons u e w).idxOf x = w.idxOf x + 1 := by
  simp [idxOf_cons, hne]

lemma idxOf_notMem (hx : x ∉ w) : w.idxOf x = w.length + 1 := by
  induction w with
  | nil => simp_all [Ne.symm]
  | cons u e w ih =>
    simp_all only [mem_cons_iff, not_or, cons_length, not_false_eq_true, forall_const]
    rw [← ih, idxOf_cons_ne (Ne.symm hx.1)]

lemma idxOf_mem_le (hx : x ∈ w) : w.idxOf x ≤ w.length := by
  induction w with
  | nil => simp_all
  | cons u e w ih =>
      obtain rfl | ⟨hne, hxw⟩ := eq_or_ne_mem_of_mem_cons hx
      · simp
      rw [idxOf_cons_ne hne.symm, cons_length, Nat.add_le_add_iff_right]
      exact ih hxw

@[simp]
lemma idxOf_le_length_iff_mem : w.idxOf x ≤ w.length ↔ x ∈ w := by
  refine ⟨fun h ↦ by_contra fun hxw ↦ ?_, idxOf_mem_le⟩
  rw [idxOf_notMem hxw] at h
  omega

@[simp]
lemma idxOf_first (w : WList α β) : w.idxOf w.first = 0 := by
  induction w with simp_all

lemma idxOf_eq_idxOf_vertex (w : WList α β) (x : α) : w.idxOf x = w.vertex.idxOf x := by
  induction w with
  | nil => simp [List.idxOf_cons]
  | cons u e w ih =>
    obtain rfl | hne := eq_or_ne x u
    · simp
    simp [idxOf_cons_ne hne.symm, ← ih, List.idxOf_cons_ne _ hne.symm]

lemma get_idxOf (w : WList α β) (hxw : x ∈ w) : w.get (w.idxOf x) = x := by
  rw [get_eq_getD_vertex, idxOf_eq_idxOf_vertex, getD_eq_getElem?_getD, getElem?_idxOf (by simpa),
    Option.getD_some]

lemma idxOf_get (hw : w.vertex.Nodup) {n} (hn : n ≤ w.length) : w.idxOf (w.get n) = n := by
  rw [get_eq_getD_vertex, idxOf_eq_idxOf_vertex, ← vertex_getLast, getD_eq_getElem?_getD,
    ← hw.idxOf_getElem n (by simpa [Nat.lt_add_one_iff])]
  simp

lemma idxOf_last (w : WList α β) (hw : w.vertex.Nodup) : w.idxOf w.last = w.length := by
  induction w with
  | nil => simp
  | cons u e w ih =>
  simp
  have hfl : u ≠ w.last := by
    unfold Nodup at hw
    simp_all only [ne_eq, cons_vertex, pairwise_cons, mem_vertex, last_mem, not_false_eq_true]
  rw [idxOf_cons_ne hfl ]
  simp
  exact ih (Nodup.of_cons hw)

@[simp]
lemma range_get (w : WList α β) : Set.range w.get = V(w) := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [cons_vertexSet, Set.ext_iff, Set.mem_range, Set.mem_insert_iff, mem_vertexSet_iff]
    refine fun x ↦ ⟨by rintro ⟨(rfl | y), rfl⟩ <;> simp , ?_⟩
    rintro (rfl | hx)
    · exact ⟨0, by simp⟩
    exact ⟨w.idxOf x + 1, by simp [get_idxOf _ hx]⟩

-- idxOf is injective if either element is in the list
lemma idxOf_inj_of_left_mem (hx : x ∈ w) (heq : w.idxOf x = w.idxOf y) : x = y := by
  have hy : y ∈ w := idxOf_le_length_iff_mem.mp (heq ▸ idxOf_le_length_iff_mem.mpr hx)
  rw [← get_idxOf w hx, ← get_idxOf w hy, heq]

lemma idxOf_inj_of_right_mem (hy : y ∈ w) (heq : w.idxOf x = w.idxOf y) : x = y := by
  symm at heq ⊢
  exact idxOf_inj_of_left_mem hy heq

lemma idxOf_inj (hmem : x ∈ w ∨ y ∈ w) : w.idxOf x = w.idxOf y ↔ x = y :=
  ⟨hmem.elim idxOf_inj_of_left_mem idxOf_inj_of_right_mem, by tauto⟩

@[simp]
lemma idxOf_le (w : WList α β) (x : α) : w.idxOf x ≤ w.length + 1 := by
  fun_induction w.idxOf x with simp_all

@[simp]
lemma idxOf_le_of_mem (hx : x ∈ w) : w.idxOf x ≤ w.length := by
  fun_induction w.idxOf x with simp_all [eq_comm]

@[simp]
lemma idxOf_get_le (w : WList α β) (n : ℕ) : w.idxOf (w.get n) ≤ n := by
  fun_induction w.get n with simp_all | case3 u e w n IH =>
  simp [w.idxOf_cons u e]
  obtain rfl | hne := em (u = w.get n) <;> simp_all

-- idxOf is the first occurence of a value; all values before it must not be equal
lemma get_ne_of_lt_idxOf {n} (hlt : n < w.idxOf x) : w.get n ≠ x := by
  rintro rfl
  have := w.idxOf_get_le n
  omega

@[simp]
lemma idxOf_eq_zero_iff : w.idxOf x = 0 ↔ x = w.first := by
  fun_induction WList.idxOf with simp_all [Ne.symm]

lemma idxOf_cons_eq_one_iff : (cons u e w).idxOf x = 1 ↔ u ≠ x ∧ x = w.first := by
  generalize w'_def : cons u e w = w'
  fun_induction WList.idxOf with simp_all [idxOf_eq_zero_iff]

@[simp]
lemma idxOf_eq_succ_length_iff : w.idxOf x = w.length + 1 ↔ x ∉ w := by
  fun_induction WList.idxOf with simp_all [Ne.symm]

lemma idxOf_eq_length (h : w.idxOf x = w.length) : x = w.last := by
  fun_induction WList.idxOf with simp_all

@[simp]
lemma idxOf_eq_length_iff (h : w.vertex.Nodup) : w.idxOf x = w.length ↔ x = w.last := by
  fun_induction WList.idxOf with simp_all [Ne.symm] | case3 e w u =>
  rintro rfl
  exact h.1 w.last_mem

end indices

end WList


-- /-- `w.AllIncIn e x y` means that whenever `e` appears in `w`, its ends are `x` and `y`. -/
-- inductive AllIncIn : WList α β → β → α → α → Prop
--   | nil (u e x y) : AllIncIn (nil u) e x y
--   | cons_ne (u f) {w e x y} (hef : e ≠ f) (hw : w.AllIncIn e x y) : AllIncIn (cons u f w) e x y
--   | cons_left {x e w} (hw : w.AllIncIn e x w.first) : AllIncIn (cons x e w) e x w.first
--   | cons_right {x e w} (hw : w.AllIncIn e w.first x) : AllIncIn (cons x e w) e w.first x

-- @[simp]
-- lemma allIncIn_nil (e : β) {x y u : α} :
--   AllIncIn (WList.nil u) e x y := AllIncIn.nil u e x y

-- lemma allIncIn_cons_iff : AllIncIn (cons u f w) e x y ↔
--     AllIncIn w e x y ∧ (e = f → ((x = u ∧ y = w.first) ∨ (x = w.first ∧ y = u))) := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · cases h with
--     | cons_ne u f hef hw => simp [hw, hef]
--     | cons_left hw => simpa
--     | cons_right hw => simpa
--   obtain rfl | hne := eq_or_ne e f
--   · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.2 rfl
--     · exact AllIncIn.cons_left h.1
--     exact AllIncIn.cons_right h.1
--   exact AllIncIn.cons_ne _ _ hne h.1



/- Properties between the basic properties of a wList -/









-- /-- Given a graph adjacency, we can create a wList of length 1 -/
-- lemma Adj.exist_wList (h : G.Adj u v) : ∃ (W : WList α β), G.IsWList w ∧ W.length = 1 ∧
-- W.first = u ∧
--     W.last = v := by
--   obtain ⟨e, he⟩ := h
--   use he.wList, he.wList_isWList
--   simp only [IsLink.wList_length, IsLink.wList_first, IsLink.wList_last, and_self]

-- /-- Given a reflexive adjacency, we can create a wList of length at most 1 -/
-- lemma reflAdj.exist_wList (h : G.reflAdj u v) : ∃ (W : WList α β), G.IsWList w ∧ W.length ≤ 1 ∧
-- --     W.first = u ∧ W.last = v := by
-- --   obtain hadj | ⟨rfl, hx⟩ := h
-- --   · obtain ⟨W, hW, hlength, hfirst, hlast⟩ := hadj.exist_wList
-- --     use W, hW
-- --     simp only [hlength, le_refl, hfirst, hlast, and_self]
-- --   · use nil u
-- --     constructor
-- --     · simp [hx]
-- --     · simp

-- namespace WList.ValidIn

-- lemma connected (h : G.IsWList w) : G.Connected w.first w.last := by
--   induction w with
--   | nil x => simpa only [nil_first, nil_last, Connected.refl_iff]
--   | cons x e w ih =>
--     obtain ⟨H1, H2⟩ := h
--     simp only [first_cons, last_cons]
--     exact H1.connected.trans (ih H2)

-- lemma connected_last_of_mem (h : G.IsWList w) (hx : u ∈ w) : G.Connected u w.last := by
--   induction w generalizing u with
--   | nil x =>
--     rw [mem_nil_iff] at hx
--     subst u
--     simp only [nil_last, Connected.refl_iff]
--     exact h
--   | cons x e w ih =>
--     rw [mem_cons_iff] at hx
--     obtain rfl | hx := hx
--     · exact Connected.trans h.1.connected (ih h.2 (first_mem))
--     · exact ih h.2 hx

-- lemma connected_of_mem (h : G.IsWList w) (hx : x ∈ w) (hy : y ∈ w) :
--     G.Connected x y := by
--   have hx' := connected_last_of_mem h hx
--   have hy' := connected_last_of_mem h hy
--   exact Connected.trans hx' hy'.symm

-- lemma connected_first_of_mem (h : G.IsWList w) (hx : x ∈ w) : G.Connected w.first x :=
--   h.connected_of_mem first_mem hx

-- lemma eq_nil_of_mem_isolated {w : WList α β} {x : α} (hisol : G.Isolated x) (hmem : x ∈ w)
--     (h : G.IsWList w) : w = nil x := by
--   match w with
--   | .nil y => simp_all only [mem_nil_iff, nil_isWList]
--   | .cons y e w =>
--     exfalso
--     obtain ⟨hbtw, hVd⟩ := h
--     rw [mem_cons_iff] at hmem
--     obtain rfl | h := hmem
--     · exact hisol e hbtw.inc_left
--     · have := eq_nil_of_mem_isolated hisol h hVd
--       subst w
--       rw [nil_first] at hbtw
--       exact hisol e hbtw.inc_right

-- end WList.ValidIn

-- namespace IsWListFrom

-- lemma setConnected (hWF : G.IsWListFrom S T w) : G.SetConnected S T := by
--   obtain ⟨hVd, hfirst, hlast⟩ := hWF
--   use w.first, hfirst, w.last, hlast, hVd.connected

-- lemma left_subset (hWF : G.IsWListFrom S T w)
  -- (hsubset : S ∩ V(G) ⊆ S') : G.IsWListFrom S' T w where
--   isWList := hWF.isWList
--   first_mem := hsubset ⟨hWF.first_mem, hWF.isWList.vertex_mem_of_mem WList.first_mem⟩
--   last_mem := hWF.last_mem

-- lemma left_subset' (hWF : G.IsWListFrom S T w) (hsubset : S ⊆ S') : G.IsWListFrom S' T w where
--   isWList := hWF.isWList
--   first_mem := hsubset hWF.first_mem
--   last_mem := hWF.last_mem

-- lemma right_subset (hWF : G.IsWListFrom S T w) (hsubset : T ∩ V(G) ⊆ T') :
    -- G.IsWListFrom S T' w where
--   isWList := hWF.isWList
--   first_mem := hWF.first_mem
--   last_mem := hsubset ⟨hWF.last_mem, hWF.isWList.vertex_mem_of_mem WList.last_mem⟩

-- lemma right_subset' (hWF : G.IsWListFrom S T w) (hsubset : T ⊆ T') : G.IsWListFrom S T' w where
--   isWList := hWF.isWList
--   first_mem := hWF.first_mem
--   last_mem := hsubset hWF.last_mem

-- lemma left_right_subset (hWF : G.IsWListFrom S T w) (hS : S ∩ V(G) ⊆ S') (hT : T ∩ V(G) ⊆ T') :
--     G.IsWListFrom S' T' w := hWF.left_subset hS |>.right_subset hT

-- lemma left_right_subset' (hWF : G.IsWListFrom S T w) (hS : S ⊆ S') (hT : T ⊆ T') :
--     G.IsWListFrom S' T' w := hWF.left_subset' hS |>.right_subset' hT


-- end IsWListFrom
