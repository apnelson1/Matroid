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

variable {w w₁ w₂ : WList α β}

namespace WList

/-! ## Empty WLists -/

inductive Nil : WList α β → Prop
  | nil (x : α) : Nil (nil x)

inductive Nonempty : WList α β → Prop
  | cons (x e) (w : WList α β) : Nonempty (cons x e w)

def first : WList α β → α
| nil x => x
| cons x _ _ => x

def last : WList α β → α
| nil x => x
| cons _ _ w => w.last

def vx : WList α β → List α
| nil x => [x]
| cons x _e w => x :: w.vx

instance : Membership α (WList α β) where
  mem w x := x ∈ w.vx

instance [DecidableEq α] : Decidable (x ∈ w) :=
  inferInstanceAs <| Decidable (x ∈ w.vx)

@[simp]
lemma mem_vx : (x ∈ w.vx) = (x ∈ w) := rfl

def vxSet : WList α β → Set α := fun w => {x | x ∈ w}

def edge : WList α β → List β
| nil _ => []
| cons _ e w => e :: w.edge

def edgeSet : WList α β → Set β := fun w => {e | e ∈ w.edge}

/-- Change this to `length w.edge`-/
def length : WList α β → ℕ
| nil _ => 0
| cons _ _ w => w.length + 1

@[simp]
lemma length_edge (w : WList α β) : w.edge.length = w.length := by
  induction w with simp_all [length, edge]

@[simp]
lemma length_vx (w : WList α β) : w.vx.length = w.length + 1 := by
  induction w with simp_all [length, vx]

@[simp]
lemma vx_ne_nil : w.vx ≠ [] := by
  cases w with simp [vx]

/-! ### Properties of `cons` -/

@[simp] lemma cons_first : (cons x e w).first = x := rfl

@[simp] lemma cons_last : (cons x e w).last = w.last := rfl

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

@[simp] lemma mem_cons_iff : x ∈ (cons u e w) ↔ x = u ∨ x ∈ w := by simp [← mem_vx]

@[simp] lemma cons_vxSet : (cons x e w).vxSet = insert x w.vxSet := by
  simp [vxSet, mem_cons_iff, Set.ext_iff]

@[simp↓] lemma cons_vxSet_subset : (cons x e w).vxSet ⊆ U ↔ x ∈ U ∧ w.vxSet ⊆ U := by
  simp [insert_subset_iff]

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

@[simp] lemma cons_edgeSet : (cons x e w).edgeSet = {e} ∪ w.edgeSet := by
  simp only [edgeSet, cons_edge, mem_cons, singleton_union]
  rfl

@[simp] lemma cons_length : (cons x e w).length = w.length + 1 := rfl


/-! # Properties of `mem` -/

@[simp] lemma mem_vxSet_iff : x ∈ w.vxSet ↔ x ∈ w := by
  simp [vxSet]

@[simp] lemma mem_edgeSet_iff : e ∈ w.edgeSet ↔ e ∈ w.edge := by
  simp [edgeSet]

@[simp] lemma first_mem : w.first ∈ w := by
  match w with
  | nil x => simp [first, ← mem_vx, vx]
  | cons x e w => simp

@[simp]
lemma last_mem {w : WList α β} : w.last ∈ w := by
  match w with
  | nil x => simp [last, ← mem_vx, vx]
  | cons x e w => simp [last_mem]

lemma first_eq_vx_head : w.first = w.vx.head vx_ne_nil := by
  cases w with rfl

@[simp]
lemma last_mem_vxSet : w.last ∈ w.vxSet := by simp

/-! # Properties of `nil`. -/

@[simp] lemma nil_inj : (nil x : WList α β) = nil y ↔ x = y := by
  rw [nil.injEq]

@[simp] lemma cons_nonempty : (cons x e w).Nonempty := by
  apply Nonempty.cons

@[simp] lemma nil_not_nonempty : ¬ (nil x : WList α β).Nonempty := by
  rintro ⟨_, _, _⟩

@[simp] lemma nil_first : (nil x : WList α β).first = x := rfl

@[simp] lemma nil_last : (nil x : WList α β).last = x := rfl

@[simp] lemma nil_vx : (nil x : WList α β).vx = [x] := rfl

@[simp] lemma mem_nil_iff : x ∈ (nil u : WList α β) ↔ x = u := by simp [← mem_vx]

@[simp] lemma nil_vxSet : (nil x : WList α β).vxSet = {x} := by simp [vxSet]

@[simp] lemma nil_edge : (nil x : WList α β).edge = [] := rfl

@[simp] lemma nil_edgeSet : (nil x : WList α β).edgeSet = ∅ := by simp [edgeSet]

@[simp] lemma nil_length : (nil x : WList α β).length = 0 := rfl

@[simp] lemma nil_injective : Injective (nil : α → WList α β) := by
  rintro x y h
  rwa [nil.injEq] at h

@[simp]
lemma nil_nil : Nil (nil x (β := β)) :=
  Nil.nil ..

@[simp] lemma not_nonempty_iff : ¬ w.Nonempty ↔ w.Nil := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
  simp only [cons_nonempty, not_true_eq_false, false_iff]
  rintro ⟨_⟩

@[simp] lemma not_nil_iff : ¬ w.Nil ↔ w.Nonempty := by
  rw [← not_nonempty_iff, not_not]

lemma nil_iff_eq_nil : Nil w ↔ ∃ x, w = nil x := by
  induction w with simp


@[simp]
lemma not_nil_cons (w : WList α β) (x) (e) : ¬ Nil (w.cons x e) := by
  simp

lemma Nil.eq_nil_of_mem (h : w.Nil) (hxw : x ∈ w) : w = .nil x := by
  induction w with simp_all

lemma Nil.eq_nil_first (h : w.Nil) : w = .nil w.first :=
  h.eq_nil_of_mem <| by simp

lemma Nil.eq_nil_last (h : w.Nil) : w = .nil w.last :=
  h.eq_nil_of_mem <| by simp

lemma Nil.first_eq_last (h : w.Nil) : w.first = w.last := by
  cases h with rfl

/- Properties of Nonempty -/

lemma Nonempty.exists_cons (hw : w.Nonempty) : ∃ x e w', w = .cons x e w' := by
  cases hw with simp

lemma nonempty_iff_exists_cons : w.Nonempty ↔ ∃ x e w', w = cons x e w' := by
  induction w with simp_all

@[simp]
lemma length_eq_zero : w.length = 0 ↔ w.Nil := by
  induction w with simp

lemma length_ne_zero_iff : w.length ≠ 0 ↔ w.Nonempty := by
  simp

@[simp]
lemma length_pos_iff : 0 < w.length ↔ w.Nonempty := by
  simp [Nat.pos_iff_ne_zero]

lemma first_eq_last_iff (hnodup : w.vx.Nodup) : w.first = w.last ↔ w.Nil :=
  ⟨fun h ↦ by cases w with simp_all, Nil.first_eq_last⟩

lemma first_ne_last_iff (hnodup : w.vx.Nodup) : w.first ≠ w.last ↔ w.Nonempty := by
  simp [first_eq_last_iff hnodup]

@[ext]
lemma ext_vx_edge {w₁ w₂ : WList α β} (h_vx : w₁.vx = w₂.vx) (h_edge : w₁.edge = w₂.edge) :
    w₁ = w₂ := by
  match w₁ with
  | nil u => cases w₂ with | _ => simp_all
  | cons u e w₁ =>
  match w₂ with
  | nil u => simp_all
  | cons v f w₂ =>
  simp_all only [cons_vx, List.cons.injEq, cons_edge, cons.injEq, true_and]
  exact ext_vx_edge h_vx.2 h_edge.2

lemma last_eq_vx_getLast {w : WList α β} : w.last = w.vx.getLast vx_ne_nil := by
  cases w with
  | nil => rfl
  | cons =>
    simp only [cons_last, cons_vx, ne_eq, vx_ne_nil, not_false_eq_true, getLast_cons]
    apply last_eq_vx_getLast


/-- The first edge of a nonempty `WList` -/
def firstEdge : (w : WList α β) → (hw : w.Nonempty) → β
  | .nil x, hw => by simp at hw
  | .cons x e w, hw => e

@[simp]
lemma vx_nodup_of_cons (h : (WList.cons x e w).vx.Nodup) : w.vx.Nodup := by
  simp_all

@[simp]
lemma vx_toFinset_toSet [DecidableEq α] (w : WList α β) : (w.vx.toFinset : Set α) = w.vxSet := by
  induction w with
  | nil u => simp
  | cons u e W ih =>
    ext
    simp [← ih]

/-- `w.Inc₂ e x y` means that `w` contains `[x,e,y]` as a contiguous sublist. -/
protected inductive Inc₂ : WList α β → β → α → α → Prop
  | cons_left (x e w) : (cons x e w).Inc₂ e x w.first
  | cons_right (x e w) : (cons x e w).Inc₂ e w.first x
  | cons (u f) {w e x y} (hw : w.Inc₂ e x y) : (cons u f w).Inc₂ e x y

@[simp]
protected lemma Inc₂.not_nil : ¬ (nil u (β := β)).Inc₂ e x y := by
  rintro (_ | _ | _)

protected lemma Inc₂.symm (h : w.Inc₂ e x y) : w.Inc₂ e y x := by
  induction h with
  | cons_left => apply cons_right
  | cons_right => apply cons_left
  | cons _ _ _ ih => apply ih.cons

protected lemma Inc₂.of_cons (hw : (WList.cons u f w).Inc₂ e x y) (hef : e ≠ f) : w.Inc₂ e x y := by
  cases hw with | cons_left => contradiction | cons_right => contradiction | cons => assumption

protected lemma inc₂_cons_iff : (cons u f w).Inc₂ e x y ↔
    (f = e ∧ (x = u ∧ y = w.first ∨ x = w.first ∧ y = u)) ∨ w.Inc₂ e x y := by
  refine ⟨fun h ↦ by cases h with simp_all, ?_⟩
  rintro (⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | h)
  · apply Inc₂.cons_left
  · apply Inc₂.cons_right
  apply h.cons

/-- A `WList` is well-formed if each edge appears only with the same ends.  -/
def WellFormed (w : WList α β) : Prop := ∀ ⦃e x y₁ y₂⦄, w.Inc₂ e x y₁ → w.Inc₂ e x y₂ → y₁ = y₂

/-- The set of ends of -/
def endsOf (w : WList α β) (e : β) : Set α := {x | ∃ y, w.Inc₂ e x y}

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


end WList


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
--     simp only [cons_first, cons_last]
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
