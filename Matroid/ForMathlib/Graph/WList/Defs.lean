import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Sym.Sym2

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

variable {w w₁ w₂ : WList α β}

@[simp]
lemma nil_inj_iff : (nil x : WList α β) = nil y ↔ x = y := by
  rw [nil.injEq]

@[simp]
lemma cons_inj_iff : cons x e w₁ = cons y f w₂ ↔ x = y ∧ e = f ∧ w₁ = w₂ := by
  induction w₁ with simp

/-! ## First and Last -/

/-- The first element of a `WList` -/
def first : WList α β → α
  | nil x => x
  | cons x _ _ => x

@[simp]
lemma nil_first : (nil x : WList α β).first = x := rfl

@[simp]
lemma first_cons : (cons x e w).first = x := rfl

def last : WList α β → α
  | nil x => x
  | cons _ _ w => w.last

@[simp]
lemma last_cons : (cons x e w).last = w.last := rfl

@[simp]
lemma nil_last : (nil x : WList α β).last = x := rfl

/-! ## Vertex/Edge Lists -/

/-- The list of vertices of a `WList` -/
def vx : WList α β → List α
  | nil x => [x]
  | cons x _e w => x :: w.vx

@[simp]
lemma vx_ne_nil : w.vx ≠ [] := by
  cases w with simp [vx]

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

@[simp] lemma nil_vx : (nil x : WList α β).vx = [x] := rfl

@[simp]
lemma vx_head : w.vx.head vx_ne_nil = w.first := by
  cases w with rfl

@[simp]
lemma vx_getLast {w : WList α β} : w.vx.getLast vx_ne_nil = w.last := by
  induction w with simp_all

@[simp]
lemma vx_length_pos (w : WList α β) : 0 < w.vx.length :=
  length_pos_of_ne_nil vx_ne_nil

@[simp]
lemma vx_getElem_zero (w : WList α β) : w.vx[0] = w.first := by
  cases w with simp

/-- The list of edges of a `WList` -/
def edge : WList α β → List β
  | nil _ => []
  | cons _ e w => e :: w.edge

@[simp]
lemma nil_edge (x : α) : (nil x : WList α β).edge = [] := rfl

@[simp]
lemma cons_edge (x e) (w : WList α β) : (cons x e w).edge = e :: w.edge := rfl

/-- Two `WLists` with the same vertex and edge lists arae equal. -/
@[ext]
lemma ext_vx_edge {w₁ w₂ : WList α β} (h_vx : w₁.vx = w₂.vx) (h_edge : w₁.edge = w₂.edge) :
    w₁ = w₂ := by
  match w₁ with
  | nil u => cases w₂ with | _ => simp_all
  | cons u e w₁ => match w₂ with
    | nil u => simp_all
    | cons v f w₂ =>
    simp_all only [cons_vx, List.cons.injEq, cons_edge, cons.injEq, true_and]
    exact ext_vx_edge h_vx.2 h_edge.2

/-! ### Membership -/

-- /-- `w.mem x` means that `x` is a vertex of `w`. Defined inductively for cleaner proofs. -/
-- protected inductive Mem : WList α β → α → Prop
--   | nil x : (nil x).Mem x
--   | cons_eq x e w : (cons x e w).Mem x
--   | cons u e {w x} (h : w.Mem x) : (cons u e w).Mem x



instance : Membership α (WList α β) where
  mem w x := x ∈ w.vx


@[simp]
lemma mem_vx : (x ∈ w.vx) = (x ∈ w) := rfl

@[simp]
lemma mem_nil_iff : x ∈ (nil u : WList α β) ↔ x = u := by
  simp [← mem_vx]

@[simp]
lemma mem_cons_iff : x ∈ (cons u e w) ↔ x = u ∨ x ∈ w := by
  simp [← mem_vx]

lemma eq_or_ne_mem_of_mem_cons (h : x ∈ cons u e w) : x = u ∨ (x ≠ u ∧ x ∈ w) := by
  obtain rfl | hne := eq_or_ne x u
  · simp
  exact .inr ⟨hne, by simpa [hne] using h⟩

instance [DecidableEq α] : Decidable (x ∈ w) :=
  inferInstanceAs <| Decidable (x ∈ w.vx)

@[simp] lemma first_mem : w.first ∈ w := by
  cases w with simp

@[simp]
lemma last_mem {w : WList α β} : w.last ∈ w := by
  induction w with simp_all

/-- `w.UniqueMem x` means that `x : α` appears in `w` exactly once. -/
protected inductive UniqueMem : WList α β → α → Prop
  | nil x : (nil x).UniqueMem x
  | cons_eq {x} e w (h : x ∉ w) : (cons x e w).UniqueMem x
  | cons_ne {x u} (h : u ≠ x) e w (hw : w.UniqueMem x) : (cons u e w).UniqueMem x

/-! ### Vertex/Edge Sets -/

def vxSet (w : WList α β) : Set α := {x | x ∈ w}

def edgeSet (w : WList α β) : Set β := {e | e ∈ w.edge}

@[simp]
lemma mem_vxSet_iff : x ∈ w.vxSet ↔ x ∈ w := Iff.rfl

@[simp]
lemma mem_edgeSet_iff : e ∈ w.edgeSet ↔ e ∈ w.edge := Iff.rfl

@[simp]
lemma nil_vxSet : (nil x : WList α β).vxSet = {x} := by
  simp [vxSet]

@[simp]
lemma nil_edgeSet : (nil x : WList α β).edgeSet = ∅ := by
  simp [edgeSet]

@[simp] lemma cons_vxSet : (cons x e w).vxSet = insert x w.vxSet := by
  simp [vxSet, mem_cons_iff, Set.ext_iff]

@[simp] lemma cons_edgeSet : (cons x e w).edgeSet = {e} ∪ w.edgeSet := by
  simp only [edgeSet, cons_edge, mem_cons, singleton_union]
  rfl

@[simp]
lemma vxSet_nonempty (w : WList α β) : w.vxSet.Nonempty := by
  cases w with simp

@[simp]
lemma vx_toFinset_toSet [DecidableEq α] (w : WList α β) : (w.vx.toFinset : Set α) = w.vxSet := by
  induction w with
  | nil u => simp
  | cons u e W ih =>
    ext
    simp [← ih]

/-! ## Emptiness -/

/-- `Nil w` means that `w : WList α β` has no edges -/
inductive Nil : WList α β → Prop
  | nil (x : α) : Nil (nil x)

@[simp]
lemma nil_nil : Nil (nil x (β := β)) :=
  Nil.nil ..

@[simp]
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

lemma first_eq_last_iff (hnodup : w.vx.Nodup) : w.first = w.last ↔ w.Nil :=
  ⟨fun h ↦ by cases w with simp_all, Nil.first_eq_last⟩

/-- `Nonempty w` means that `w : WList α β` has at least one edge -/
inductive Nonempty : WList α β → Prop
  | cons (x e) (w : WList α β) : Nonempty (cons x e w)

@[simp]
lemma cons_nonempty : (cons x e w).Nonempty := by
  apply Nonempty.cons

@[simp]
lemma nil_not_nonempty : ¬ (nil x : WList α β).Nonempty := by
  rintro ⟨_, _, _⟩

lemma nil_injective : Injective (nil : α → WList α β) := by
  rintro x y h
  rwa [nil.injEq] at h

@[simp] lemma not_nonempty_iff : ¬ w.Nonempty ↔ w.Nil := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
  simp only [cons_nonempty, not_true_eq_false, false_iff]
  rintro ⟨_⟩

@[simp] lemma not_nil_iff : ¬ w.Nil ↔ w.Nonempty := by
  rw [← not_nonempty_iff, not_not]

lemma Nonempty.exists_cons (hw : w.Nonempty) : ∃ x e w', w = .cons x e w' := by
  cases hw with simp

lemma nonempty_iff_exists_cons : w.Nonempty ↔ ∃ x e w', w = cons x e w' := by
  induction w with simp_all

lemma first_ne_last_iff (hnodup : w.vx.Nodup) : w.first ≠ w.last ↔ w.Nonempty := by
  simp [first_eq_last_iff hnodup]

lemma nonempty_or_exists_eq_nil (w : WList α β) : w.Nonempty ∨ ∃ x, w = nil x := by
  induction w with simp

/-- The first edge of a nonempty `WList` -/
def firstEdge : (w : WList α β) → (hw : w.Nonempty) → β
  | .nil x, hw => by simp at hw
  | .cons x e w, hw => e

/-! ### Length -/

/-- The number of edges in a `WList`. Change this to `length w.edge` ?? -/
def length : WList α β → ℕ
| nil _ => 0
| cons _ _ w => w.length + 1

@[simp]
lemma length_edge (w : WList α β) : w.edge.length = w.length := by
  induction w with simp_all [length, edge]

@[simp]
lemma length_vx (w : WList α β) : w.vx.length = w.length + 1 := by
  induction w with simp_all [length, vx]

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

lemma DInc.vx_mem_left (h : w.DInc e x y) : x ∈ w.vx := by
  induction h with simp_all

lemma DInc.vx_mem_right (h : w.DInc e x y) : y ∈ w.vx := by
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

/-- `w.Inc₂ e x y` means that `w` contains `[x,e,y]` or `[y,e,x]` as a contiguous sublist. -/
protected inductive Inc₂ : WList α β → β → α → α → Prop
  | cons_left (x e w) : (cons x e w).Inc₂ e x w.first
  | cons_right (x e w) : (cons x e w).Inc₂ e w.first x
  | cons (u f) {w e x y} (hw : w.Inc₂ e x y) : (cons u f w).Inc₂ e x y

@[simp]
protected lemma Inc₂.not_nil : ¬ (nil u (β := β)).Inc₂ e x y := by
  rintro (_ | _ | _)

lemma DInc.inc₂ (h : w.DInc e x y) : w.Inc₂ e x y := by
  induction h with
  | cons_left x e w => exact Inc₂.cons_left x e w
  | cons u f hw ih => exact Inc₂.cons u f ih

protected lemma Inc₂.symm (h : w.Inc₂ e x y) : w.Inc₂ e y x := by
  induction h with
  | cons_left => apply cons_right
  | cons_right => apply cons_left
  | cons _ _ _ ih => apply ih.cons

lemma inc₂_iff_dInc : w.Inc₂ e x y ↔ w.DInc e x y ∨ w.DInc e y x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim DInc.inc₂ fun h' ↦ h'.inc₂.symm⟩
  induction h with
  | cons_left x e w => exact .inl <| DInc.cons_left ..
  | cons_right x e w => exact .inr <| DInc.cons_left ..
  | cons u f hw ih => exact ih.elim (.inl ∘ DInc.cons _ _) (.inr ∘ DInc.cons _ _)

protected lemma Inc₂.of_cons (hw : (WList.cons u f w).Inc₂ e x y) (hef : e ≠ f) : w.Inc₂ e x y := by
  cases hw with | cons_left => contradiction | cons_right => contradiction | cons => assumption

lemma inc₂_cons_iff' : (cons u f w).Inc₂ e x y ↔
    (f = e ∧ (x = u ∧ y = w.first ∨ x = w.first ∧ y = u)) ∨ w.Inc₂ e x y := by
  refine ⟨fun h ↦ by cases h with simp_all, ?_⟩
  rintro (⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | h)
  · apply Inc₂.cons_left
  · apply Inc₂.cons_right
  apply h.cons

lemma inc₂_cons_iff : (cons u f w).Inc₂ e x y ↔
    (f = e ∧ (s(x,y) = s(u,w.first))) ∨ w.Inc₂ e x y := by
  rw [inc₂_cons_iff', Sym2.eq_iff]

lemma Inc₂.vx_mem_left (h : w.Inc₂ e x y) : x ∈ w.vx := by
  induction h with simp_all

lemma Inc₂.vx_mem_right (h : w.Inc₂ e x y) : y ∈ w.vx :=
  h.symm.vx_mem_left

lemma Inc₂.edge_mem (h : w.Inc₂ e x y) : e ∈ w.edge := by
  induction h with simp_all

lemma exists_inc₂_of_mem_edge (he : e ∈ w.edge) : ∃ x y, w.Inc₂ e x y := by
  obtain ⟨x, y, h⟩ := exists_dInc_of_mem_edge he
  exact ⟨x, y, h.inc₂⟩

/-- A `WList` is `WellFormed` if each edge appears only with the same ends. -/
def WellFormed (w : WList α β) : Prop :=
  ∀ ⦃e x₁ x₂ y₁ y₂⦄, w.Inc₂ e x₁ x₂ → w.Inc₂ e y₁ y₂ → s(x₁, x₂) = s(y₁, y₂)

/-- The set of ends of `e` in `w` -/
def endsOf (w : WList α β) (e : β) : Set α := {x | ∃ y, w.Inc₂ e x y}

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

lemma get_eq_getD_vx (w : WList α β) (n) : w.get n = w.vx.getD n w.last := by
  induction n generalizing w with
  | zero => simp
  | succ n IH => cases w with simp [IH]

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

lemma idxOf_cons_ne (hne : u ≠ x) (e) (w : WList α β) :
    (cons u e w).idxOf x = w.idxOf x + 1 := by
  simp [idxOf_cons, hne]

lemma idxOf_not_mem (hx : x ∉ w) : w.idxOf x = w.length + 1 := by
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
  rw [idxOf_not_mem hxw] at h
  omega

@[simp]
lemma idxOf_first (w : WList α β) : w.idxOf w.first = 0 := by
  induction w with simp_all [idxOf_cons]

lemma idxOf_eq_idxOf_vx (w : WList α β) (x : α) : w.idxOf x = w.vx.idxOf x := by
  induction w with
  | nil => simp [List.idxOf_cons]
  | cons u e w ih =>
    obtain rfl | hne := eq_or_ne x u
    · simp
    simp [idxOf_cons_ne hne.symm, ← ih, List.idxOf_cons_ne _ hne.symm]

lemma get_idxOf (w : WList α β) (hxw : x ∈ w) : w.get (w.idxOf x) = x := by
  rw [get_eq_getD_vx, idxOf_eq_idxOf_vx, getD_eq_getElem?_getD, getElem?_idxOf (by simpa),
    Option.getD_some]

lemma idxOf_get (hw : w.vx.Nodup) {n} (hn : n ≤ w.length) : w.idxOf (w.get n) = n := by
  rw [get_eq_getD_vx, idxOf_eq_idxOf_vx, ← vx_getLast, getD_eq_getElem?_getD,
    ← List.idxOf_getElem hw n (by simpa [Nat.lt_add_one_iff])]
  simp

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
--   simp only [Inc₂.wList_length, Inc₂.wList_first, Inc₂.wList_last, and_self]

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
  -- (hsubset : S ∩ G.V ⊆ S') : G.IsWListFrom S' T w where
--   isWList := hWF.isWList
--   first_mem := hsubset ⟨hWF.first_mem, hWF.isWList.vx_mem_of_mem WList.first_mem⟩
--   last_mem := hWF.last_mem

-- lemma left_subset' (hWF : G.IsWListFrom S T w) (hsubset : S ⊆ S') : G.IsWListFrom S' T w where
--   isWList := hWF.isWList
--   first_mem := hsubset hWF.first_mem
--   last_mem := hWF.last_mem

-- lemma right_subset (hWF : G.IsWListFrom S T w) (hsubset : T ∩ G.V ⊆ T') :
    -- G.IsWListFrom S T' w where
--   isWList := hWF.isWList
--   first_mem := hWF.first_mem
--   last_mem := hsubset ⟨hWF.last_mem, hWF.isWList.vx_mem_of_mem WList.last_mem⟩

-- lemma right_subset' (hWF : G.IsWListFrom S T w) (hsubset : T ⊆ T') : G.IsWListFrom S T' w where
--   isWList := hWF.isWList
--   first_mem := hWF.first_mem
--   last_mem := hsubset hWF.last_mem

-- lemma left_right_subset (hWF : G.IsWListFrom S T w) (hS : S ∩ G.V ⊆ S') (hT : T ∩ G.V ⊆ T') :
--     G.IsWListFrom S' T' w := hWF.left_subset hS |>.right_subset hT

-- lemma left_right_subset' (hWF : G.IsWListFrom S T w) (hS : S ⊆ S') (hT : T ⊆ T') :
--     G.IsWListFrom S' T' w := hWF.left_subset' hS |>.right_subset' hT


-- end IsWListFrom
