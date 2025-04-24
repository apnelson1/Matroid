import Matroid.ForMathlib.Graph.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Dedup

open Set Function List Nat

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S S' T T' U V : Set α}
  {F F' R R': Set β}

namespace Graph


inductive Walk (α β : Type*) where
| nil (u : α) : Walk α β
| cons (u : α) (e : β) (w : Walk α β) : Walk α β

variable {w w₁ w₂ : Walk α β}
namespace Walk

def Nonempty : Walk α β → Prop
| nil _ => False
| cons _ _ _ => True

def first : Walk α β → α
| nil x => x
| cons x _ _ => x

def last : Walk α β → α
| nil x => x
| cons _ _ w => w.last

def vx : Walk α β → List α
| nil x => [x]
| cons x _e w => x :: w.vx

instance : Membership α (Walk α β) where
  mem w x := x ∈ w.vx

instance [DecidableEq α] : Decidable (x ∈ w) := by
  change Decidable (x ∈ w.vx)
  infer_instance

@[simp]
lemma mem_notation : (x ∈ w.vx) = (x ∈ w) := rfl

def vxSet : Walk α β → Set α := fun w => {x | x ∈ w}

def edge : Walk α β → List β
| nil _ => []
| cons _ e w => e :: w.edge

def edgeSet : Walk α β → Set β := fun w => {e | e ∈ w.edge}

/-- Change this to `length w.edge`-/
def length : Walk α β → ℕ
| nil _ => 0
| cons _ _ w => w.length + 1

@[simp]
lemma length_edge (w : Walk α β) : w.edge.length = w.length := by
  induction w with simp_all [length, edge]

@[simp]
lemma length_vx (w : Walk α β) : w.vx.length = w.length + 1 := by
  induction w with simp_all [length, vx]

def ValidIn (w : Walk α β) (G : Graph α β) : Prop :=
  match w with
  | nil x => x ∈ G.V
  | cons x e w => G.Inc₂ e x w.first ∧ w.ValidIn G

end Walk

@[mk_iff]
structure IsTrail (G : Graph α β) (W : Walk α β) : Prop where
  validIn : W.ValidIn G
  edge_nodup : W.edge.Nodup

@[simp] lemma IsTrail.validIn_simp (h : G.IsTrail w) : w.ValidIn G := h.validIn
@[simp] lemma IsTrail.edge_nodup_simp (h : G.IsTrail w) : w.edge.Nodup := h.edge_nodup
@[simp] lemma isTrail_simp (hVd : w.ValidIn G) (hed : w.edge.Nodup) :
    G.IsTrail w := IsTrail.mk hVd hed

@[mk_iff]
structure IsPath (G : Graph α β) (W : Walk α β) : Prop where
  validIn : W.ValidIn G
  nodup : W.vx.Nodup

@[simp] lemma IsPath.validIn_simp (h : G.IsPath w) : w.ValidIn G := h.validIn
@[simp] lemma IsPath.nodup_simp (h : G.IsPath w) : w.vx.Nodup := h.nodup
@[simp] lemma isPath_simp (hVd : w.ValidIn G) (hnodup : w.vx.Nodup) :
    G.IsPath w := IsPath.mk hVd hnodup

@[mk_iff]
structure IsWalkFrom (G : Graph α β) (S T : Set α) (W : Walk α β) : Prop where
  validIn : W.ValidIn G
  first_mem : W.first ∈ S
  last_mem : W.last ∈ T

@[simp] lemma IsWalkFrom.validIn_simp (h : G.IsWalkFrom S T w) : w.ValidIn G := h.validIn
@[simp] lemma IsWalkFrom.first_mem_simp (h : G.IsWalkFrom S T w) : w.first ∈ S := h.first_mem
@[simp] lemma IsWalkFrom.last_mem_simp (h : G.IsWalkFrom S T w) : w.last ∈ T := h.last_mem
@[simp] lemma isWalkFrom_simp (hVd : w.ValidIn G) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsWalkFrom S T w := IsWalkFrom.mk hVd hfirst hlast

@[mk_iff]
structure IsTrailFrom (G : Graph α β) (S T : Set α) (W : Walk α β) : Prop extends
  G.IsTrail W, G.IsWalkFrom S T W

@[mk_iff]
structure IsPathFrom (G : Graph α β) (S T : Set α) (W : Walk α β) : Prop extends
  G.IsPath W, G.IsWalkFrom S T W







/- Properties between IsWalkFrom, IsTrail, IsPath, IsTrailFrom, IsPathFrom -/

-- lemma IsPath.isTrail (h : G.IsPath w) : G.IsTrail w where
--   validIn := h.validIn
--   edge_nodup := by
--     _

-- lemma IsCycle.isTrail (h : G.IsCycle w) : G.IsTrail w where
--   validIn := h.validIn
--   edge_nodup := sorry

lemma IsTrailFrom.isTrail (h : G.IsTrailFrom S T w) : G.IsTrail w where
  validIn := h.validIn
  edge_nodup := h.edge_nodup

lemma IsTrailFrom.isWalkFrom (h : G.IsTrailFrom S T w) : G.IsWalkFrom S T w where
  validIn := h.validIn
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.isPath (h : G.IsPathFrom S T w) : G.IsPath w where
  validIn := h.validIn
  nodup := h.nodup

lemma IsPathFrom.isWalkFrom (h : G.IsPathFrom S T w) : G.IsWalkFrom S T w where
  validIn := h.validIn
  first_mem := h.first_mem
  last_mem := h.last_mem

-- lemma IsPathFrom.isTrailFrom (h : G.IsPathFrom S T w) : G.IsTrailFrom S T w where
--   validIn := h.validIn
--   edge_nodup := h.isPath.isTrail.edge_nodup
--   first_mem := h.first_mem
--   last_mem := h.last_mem

lemma Walk.ValidIn.isTrail (hVd : w.ValidIn G) (hedge : w.edge.Nodup) : G.IsTrail w := ⟨hVd, hedge⟩

lemma Walk.ValidIn.isPath (hVd : w.ValidIn G) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hVd, hvx⟩

lemma Walk.ValidIn.isWalkFrom (hVd : w.ValidIn G) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsWalkFrom S T w := ⟨hVd, hfirst, hlast⟩


lemma Walk.ValidIn.isTrailFrom (hVd : w.ValidIn G) (hedge : w.edge.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsTrailFrom S T w := ⟨⟨hVd, hedge⟩, hfirst, hlast⟩

lemma Walk.ValidIn.isPathFrom (hVd : w.ValidIn G) (hvx : w.vx.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsPathFrom S T w := ⟨⟨hVd, hvx⟩, hfirst, hlast⟩

lemma IsTrail.isPath (hT : G.IsTrail w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hT.validIn, hvx⟩

lemma IsTrail.isTrailFrom (hT : G.IsTrail w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsTrailFrom S T w := ⟨hT, hfirst, hlast⟩

lemma IsTrail.isPathFrom (hT : G.IsTrail w) (hvx : w.vx.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsPathFrom S T w := ⟨⟨hT.validIn, hvx⟩, hfirst, hlast⟩

lemma IsPath.isPathFrom (hP : G.IsPath w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsPathFrom S T w := ⟨hP, hfirst, hlast⟩

namespace Walk

/- Properties of nil -/

@[simp] lemma nil_not_nonempty : ¬ (nil x : Walk α β).Nonempty := by simp [Nonempty]

@[simp] lemma nil_first : (nil x : Walk α β).first = x := rfl

@[simp] lemma nil_last : (nil x : Walk α β).last = x := rfl

@[simp] lemma nil_vx : (nil x : Walk α β).vx = [x] := rfl

@[simp] lemma mem_nil_iff : x ∈ (nil u : Walk α β) ↔ x = u := by simp [← mem_notation]

@[simp] lemma nil_vxSet : (nil x : Walk α β).vxSet = {x} := by simp [vxSet]

@[simp] lemma nil_edge : (nil x : Walk α β).edge = [] := rfl

@[simp] lemma nil_edgeSet : (nil x : Walk α β).edgeSet = ∅ := by simp [edgeSet]

@[simp] lemma nil_length : (nil x : Walk α β).length = 0 := rfl

@[simp] lemma nil_injective : Injective (nil : α → Walk α β) := by
  rintro x y h
  rwa [nil.injEq] at h

-- @[simp] lemma nil_inj : (nil x : Walk α β) = nil y ↔ x = y := by
--   rw [nil.injEq]

@[simp] lemma nil_validIn : (nil x : Walk α β).ValidIn G ↔ x ∈ G.V := by
  simp only [ValidIn]

@[simp] lemma nil_isWalkFrom : G.IsWalkFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  refine ⟨fun ⟨h, hS, hT⟩ ↦ ?_, fun ⟨hV, hS, hT⟩ ↦ ⟨?_, ?_, ?_⟩⟩ <;> simp_all only [and_self,
  nil_validIn, nil_first, nil_last]

@[simp] lemma nil_isTrail : G.IsTrail (nil x) ↔ x ∈ G.V := by
  refine ⟨fun ⟨H1, H2⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩ <;> simp_all only [nil_validIn,
    nil_edge, nodup_nil]

@[simp] lemma nil_isPath : G.IsPath (nil x) ↔ x ∈ G.V := by
  refine ⟨fun ⟨H1, H2⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩ <;> simp_all only [nil_vx,
    nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil, and_self, nil_validIn]

@[simp] lemma nil_isTrailFrom : G.IsTrailFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  constructor
  · rintro ⟨hT, hfirst, hlast⟩
    simp_all only [nil_isTrail, nil_first, nil_last, and_self]
  · rintro ⟨hV, hS, hT⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp_all only [nil_isTrail, IsTrail.validIn_simp, nil_edge,
      nodup_nil, isTrail_simp, nil_first, nil_last]

@[simp] lemma nil_isPathFrom : G.IsPathFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  constructor
  · rintro ⟨hP, hfirst, hlast⟩
    simp_all only [nil_isPath, nil_first, nil_last, and_self]
  · rintro ⟨hV, hS, hT⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp_all only [nil_isPath, IsPath.validIn_simp, nil_edge,
      nodup_nil, isPath_simp, nil_first, nil_last]

/- Properties of cons -/

@[simp] lemma cons_nonempty : (cons x e w).Nonempty := by simp [Nonempty]

@[simp] lemma cons_first : (cons x e w).first = x := rfl

@[simp] lemma cons_last : (cons x e w).last = w.last := rfl

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

@[simp] lemma mem_cons_iff : x ∈ (cons u e w) ↔ x = u ∨ x ∈ w := by simp [← mem_notation]

@[simp] lemma cons_vxSet : (cons x e w).vxSet = {x} ∪ w.vxSet := by
  simp only [vxSet, mem_cons_iff, singleton_union]
  rfl

@[simp↓] lemma cons_vxSet_subset : (cons x e w).vxSet ⊆ U ↔ x ∈ U ∧ w.vxSet ⊆ U := by
  simp [insert_subset_iff]

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

@[simp] lemma cons_edgeSet : (cons x e w).edgeSet = {e} ∪ w.edgeSet := by
  simp only [edgeSet, cons_edge, mem_cons, singleton_union]
  rfl

@[simp] lemma cons_length : (cons x e w).length = w.length + 1 := rfl

@[simp] lemma cons_validIn : (cons x e w).ValidIn G ↔ G.Inc₂ e x w.first ∧ w.ValidIn G :=
  ⟨id, id⟩

@[simp]
lemma ValidIn.cons (hw : (cons x e w).ValidIn G) : w.ValidIn G := by
  rw [cons_validIn] at hw
  exact hw.2

@[simp] lemma cons_isWalkFrom : G.IsWalkFrom S T (cons x e w) ↔
    w.ValidIn G ∧ G.Inc₂ e x w.first ∧ x ∈ S ∧ w.last ∈ T := by
  refine ⟨fun ⟨h, hS, hT⟩ ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hV, hS, hVd, hT⟩ ↦ ⟨?_, ?_, ?_⟩⟩
  <;> simp_all only [cons_validIn, cons_first, cons_last, and_self]

@[simp]
lemma cons_vx_nodup (h : (cons x e w).vx.Nodup) : w.vx.Nodup := by
  simp only [cons_vx, nodup_cons] at h
  exact h.2

@[simp] lemma cons_isTrail : G.IsTrail (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge := by
  refine ⟨fun ⟨H1, H2⟩ ↦ ⟨⟨?_, ?_⟩, ?_, ?_⟩, fun ⟨hT, h₂, hnin⟩ ↦ ⟨?_, ?_⟩⟩
  · rw [cons_validIn] at H1
    exact H1.2
  · simp only [cons_edge, nodup_cons] at H2
    exact H2.2
  · rw [cons_validIn] at H1
    exact H1.1
  · simp only [cons_edge, nodup_cons] at H2
    exact H2.1
  · simp [h₂, hT]
  · simp [hT.edge_nodup, hnin]

@[simp] lemma cons_isPath : G.IsPath (cons x e w) ↔ G.IsPath w ∧ G.Inc₂ e x w.first ∧ x ∉ w := by
  constructor
  · refine fun ⟨hVd, hnodup⟩ ↦ ⟨?_, ?_, ?_⟩ <;> simp_all only [cons_validIn, cons_vx,
    nodup_cons, mem_notation, not_false_eq_true, isPath_simp]
  · refine fun ⟨hP, h₂, hnin⟩ ↦ ⟨?_, ?_⟩ <;> simp_all only [not_false_eq_true,
    and_self, cons_vx, nodup_cons, mem_notation, true_and, hP.validIn, hP.nodup, cons_validIn]

@[simp]
lemma cons_isTrailFrom : G.IsTrailFrom S T (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge ∧ x ∈ S ∧ w.last ∈ T := by
  constructor
  · refine fun ⟨⟨hVd, hnodup⟩, hfirst, hlast⟩ ↦ ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all only [cons_validIn,
    cons_edge, nodup_cons, cons_first, cons_last, isTrail_simp, not_false_eq_true]
  · refine fun ⟨hV, hS, hVd, hT⟩ ↦ ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp_all only [IsTrail.validIn_simp,
    not_false_eq_true, and_self, cons_edge, nodup_cons, true_and, cons_isTrail, cons_first,
    cons_last, hV.edge_nodup]

@[simp]
lemma cons_isPathFrom : G.IsPathFrom S T (cons x e w) ↔
    G.IsPath w ∧ G.Inc₂ e x w.first ∧ x ∉ w ∧ x ∈ S ∧ w.last ∈ T := by
  refine ⟨fun ⟨⟨hVd, hnodup⟩, hfirst, hlast⟩ ↦ ⟨?_, ?_, ?_, ?_, ?_⟩,
    fun ⟨hV, hS, hVd, hT⟩ ↦ ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  <;> simp_all only [not_false_eq_true, and_self, cons_edge, nodup_cons, cons_validIn, cons_first,
  cons_last, mem_notation, cons_vx, isPath_simp, cons_isPath, true_and, IsPath.validIn]
  exact hV.nodup

end Walk
open Walk

@[simp]
lemma IsTrail.cons (h : G.IsTrail (cons x e w)) : G.IsTrail w := by
  rw [cons_isTrail] at h
  exact h.1

@[simp]
lemma IsPath.cons (h : G.IsPath (cons x e w)) : G.IsPath w := by
  rw [cons_isPath] at h
  exact h.1

namespace Walk


@[simp]
lemma vx_toFinset_toSet [DecidableEq α] (w : Walk α β) : (w.vx.toFinset : Set α) = w.vxSet := by
  induction w with
  | nil u => simp
  | cons u e W ih =>
  ext
  simp [← ih]

/- Properties between the basic properties of a walk -/

@[simp]
lemma vx_ne_nil : w.vx ≠ [] := by
  match w with
  | nil x => simp
  | cons x e w => simp

@[simp] lemma mem_vxSet_iff : x ∈ w.vxSet ↔ x ∈ w := by simp [vxSet]

@[simp] lemma mem_edgeSet_iff : e ∈ w.edgeSet ↔ e ∈ w.edge := by simp [edgeSet]

@[simp] lemma first_mem : w.first ∈ w := by
  match w with
  | nil x => simp
  | cons x e w => simp

@[simp] lemma first_mem_vxSet : w.first ∈ w.vxSet := by simp

lemma first_eq_vx_head : w.first = w.vx.head vx_ne_nil := by
  match w with
  | nil x => rfl
  | cons x e w => rfl

@[simp]
lemma last_mem {w : Walk α β} : w.last ∈ w := by
  match w with
  | nil x => simp
  | cons x e w => simp [last_mem]

@[simp]
lemma last_mem_vxSet : w.last ∈ w.vxSet := by simp

@[ext]
lemma ext_vx_edge {w₁ w₂ : Walk α β} (h_vx : w₁.vx = w₂.vx) (h_edge : w₁.edge = w₂.edge) :
    w₁ = w₂ := by
  match w₁ with
  | nil u => cases w₂ with | nil v => simp_all | cons v f W => simp_all
  | cons u e w₁ =>
  match w₂ with
  | nil u => simp_all
  | cons v f w₂ =>
  simp_all only [cons_vx, List.cons.injEq, cons_edge, cons.injEq, true_and]
  exact ext_vx_edge h_vx.2 h_edge.2

lemma last_eq_vx_getLast {w : Walk α β} : w.last = w.vx.getLast vx_ne_nil := by
  match w with
  | nil x => rfl
  | cons x e w =>
    simp only [cons_last, cons_vx, ne_eq, vx_ne_nil, not_false_eq_true, getLast_cons]
    apply last_eq_vx_getLast

lemma ValidIn.vx_mem_of_mem {w : Walk α β} (h : w.ValidIn G) (hmem : x ∈ w) : x ∈ G.V := by
  match w with
  | .nil y =>
    rw [mem_nil_iff] at hmem
    exact mem_of_eq_of_mem hmem h
  | .cons y e w =>
    obtain ⟨hbtw, hVd⟩ := h
    obtain rfl | h : x = y ∨ x ∈ w := by simpa using hmem
    · exact hbtw.vx_mem_left
    · exact hVd.vx_mem_of_mem h

lemma ValidIn.vxSet_subset (hVd : w.ValidIn G) : w.vxSet ⊆ G.V := fun _ ↦ hVd.vx_mem_of_mem

lemma ValidIn.edge_mem_of_mem {w : Walk α β} (h : w.ValidIn G) (hmem : e ∈ w.edge) : e ∈ G.E := by
  match w with
  | .nil x => simp at hmem
  | .cons x e' w =>
    obtain ⟨hbtw, hVd⟩ := h
    obtain rfl | h : e = e' ∨ e ∈ w.edge := by simpa using hmem
    · exact hbtw.edge_mem
    · exact hVd.edge_mem_of_mem h

lemma ValidIn.edgeSet_subset (h : w.ValidIn G) : w.edgeSet ⊆ G.E := fun _ ↦ h.edge_mem_of_mem

/- Properties of Nonempty -/

lemma Nonempty.exists_cons (hw : w.Nonempty) : ∃ x e w', w = cons x e w' := by
  induction w with simp_all

lemma nonempty_iff_exists_cons : w.Nonempty ↔ ∃ x e w', w = cons x e w' := by
  induction w with simp

@[simp]
lemma Nonempty.not_nil : ¬ (nil x : Walk α β).Nonempty := by
  simp only [Nonempty, not_false_eq_true]

@[simp]
lemma Nonempty.cons_true : (cons x e w).Nonempty := by
  simp only [Nonempty]

@[simp]
lemma Nonempty.not_iff : ¬ w.Nonempty ↔ ∃ x, w = nil x := by
  match w with
  | nil x => simp only [not_nil, not_false_eq_true, nil.injEq, exists_eq']
  | cons x e w => simp only [Nonempty, not_true_eq_false, reduceCtorEq, exists_false]

@[simp]
lemma length_pos_iff : 0 < w.length ↔ w.Nonempty := by
  induction w with simp

lemma length_ne_zero_iff : w.length ≠ 0 ↔ w.Nonempty := by
  induction w with simp

lemma first_eq_last_of_not_nonempty (h : ¬ w.Nonempty) : w.first = w.last := by
  match w with
  | nil x => simp only [nil_first, nil_last]
  | cons x e w => simp only [Nonempty.cons_true, not_true_eq_false] at h

@[simp]
lemma first_eq_last_iff (hnodup : w.vx.Nodup) : w.first = w.last ↔ ¬ w.Nonempty := by
  match w with
  | .nil x => simp only [nil_first, nil_last, Nonempty.not_nil, not_false_eq_true]
  | .cons x e w =>
    simp only [cons_vx, nodup_cons, cons_first, cons_last, Nonempty.cons_true, not_true_eq_false,
      iff_false, ne_eq] at hnodup ⊢
    exact fun h => hnodup.1 (h ▸ last_mem)

@[simp]
lemma first_ne_last_iff (hnodup : w.vx.Nodup) : w.first ≠ w.last ↔ w.Nonempty :=
  (first_eq_last_iff hnodup).not_left

/-- A walk is `Nil` if it has just one vertex -/
def Nil (W : Walk α β) : Prop := ¬ W.Nonempty

@[simp] lemma not_nonempty_iff : ¬ w.Nonempty ↔ w.Nil := Iff.rfl

@[simp] lemma not_nil_iff : ¬ w.Nil ↔ w.Nonempty := by
  rw [← not_nonempty_iff, not_not]

@[simp]
lemma length_eq_zero : w.length = 0 ↔ w.Nil := by
  rw [← not_iff_not, ← Ne, length_ne_zero_iff, not_nil_iff]

lemma nil_iff_eq_nil : Nil w ↔ ∃ x, w = nil x := by
  induction w with simp [Nil]

@[simp]
lemma nil_nil (x : α) (β : Type*) : Nil (nil x (β := β)) := by
  simp [Nil]

@[simp]
lemma not_nil_cons (w : Walk α β) (x) (e) : ¬ Nil (w.cons x e) := by
  simp

lemma Nil.eq_nil_of_mem (h : w.Nil) (hxw : x ∈ w) : w = nil x := by
  induction w with simp_all

lemma Nil.eq_nil_first (h : w.Nil) : w = nil w.first :=
  h.eq_nil_of_mem <| by simp

lemma Nil.eq_nil_last (h : w.Nil) : w = nil w.last :=
  h.eq_nil_of_mem <| by simp

end Walk
open Walk

def Inc₂.walk (_h : G.Inc₂ e u v) : Walk α β := cons u e (nil v)


lemma Walk.ValidIn.mem_of_mem_edge_of_inc (hVd : w.ValidIn G) (he : e ∈ w.edge) (h : G.Inc e u) :
    u ∈ w := by
  induction w with
  | nil x => simp at he
  | cons x e' w ih =>
  simp only [mem_cons_iff, or_iff_not_imp_left]
  simp only [cons_validIn] at hVd
  intro hux
  obtain rfl | h' : e = e' ∨ _ := by simpa using he
  · simp [h.eq_of_inc₂_of_ne_left hVd.1 hux]
  exact ih hVd.2 h'



namespace Inc₂

@[simp] lemma walk_first (h : G.Inc₂ e u v): h.walk.first = u := rfl

@[simp] lemma walk_last (h : G.Inc₂ e u v): h.walk.last = v := rfl

@[simp] lemma walk_vx (h : G.Inc₂ e u v): h.walk.vx = [u, v] := rfl

@[simp] lemma mem_walk_iff (h : G.Inc₂ e u v) (x : α) : x ∈ h.walk ↔ x = u ∨ x = v := by
  simp [walk]

@[simp] lemma walk_vxSet (h : G.Inc₂ e u v): h.walk.vxSet = {u, v} := by
  simp only [vxSet, mem_walk_iff]
  rfl

@[simp] lemma walk_edge (h : G.Inc₂ e u v): h.walk.edge = [e] := rfl

@[simp] lemma walk_edgeSet (h : G.Inc₂ e u v): h.walk.edgeSet = {e} := by simp [edgeSet]

@[simp] lemma walk_length (h : G.Inc₂ e u v): h.walk.length = 1 := rfl

@[simp]
lemma walk_validIn (h : G.Inc₂ e u v) : h.walk.ValidIn G := by
  simp [walk, h, h.vx_mem_right]

lemma walk_isPath (h : G.Inc₂ e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_validIn, by simp [hne]⟩

end Inc₂





-- /-- Given a graph adjacency, we can create a walk of length 1 -/
-- lemma Adj.exist_walk (h : G.Adj u v) : ∃ (W : Walk α β), W.ValidIn G ∧ W.length = 1 ∧
-- W.first = u ∧
--     W.last = v := by
--   obtain ⟨e, he⟩ := h
--   use he.walk, he.walk_validIn
--   simp only [Inc₂.walk_length, Inc₂.walk_first, Inc₂.walk_last, and_self]

-- /-- Given a reflexive adjacency, we can create a walk of length at most 1 -/
-- -- lemma reflAdj.exist_walk (h : G.reflAdj u v) : ∃ (W : Walk α β), W.ValidIn G ∧ W.length ≤ 1 ∧
-- --     W.first = u ∧ W.last = v := by
-- --   obtain hadj | ⟨rfl, hx⟩ := h
-- --   · obtain ⟨W, hW, hlength, hfirst, hlast⟩ := hadj.exist_walk
-- --     use W, hW
-- --     simp only [hlength, le_refl, hfirst, hlast, and_self]
-- --   · use nil u
-- --     constructor
-- --     · simp [hx]
-- --     · simp

-- namespace Walk.ValidIn

-- lemma connected (h : w.ValidIn G) : G.Connected w.first w.last := by
--   induction w with
--   | nil x => simpa only [nil_first, nil_last, Connected.refl_iff]
--   | cons x e w ih =>
--     obtain ⟨H1, H2⟩ := h
--     simp only [cons_first, cons_last]
--     exact H1.connected.trans (ih H2)

-- lemma connected_last_of_mem (h : w.ValidIn G) (hx : u ∈ w) : G.Connected u w.last := by
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

-- lemma connected_of_mem (h : w.ValidIn G) (hx : x ∈ w) (hy : y ∈ w) :
--     G.Connected x y := by
--   have hx' := connected_last_of_mem h hx
--   have hy' := connected_last_of_mem h hy
--   exact Connected.trans hx' hy'.symm

-- lemma connected_first_of_mem (h : w.ValidIn G) (hx : x ∈ w) : G.Connected w.first x :=
--   h.connected_of_mem first_mem hx

-- lemma eq_nil_of_mem_isolated {w : Walk α β} {x : α} (hisol : G.Isolated x) (hmem : x ∈ w)
--     (h : w.ValidIn G) : w = nil x := by
--   match w with
--   | .nil y => simp_all only [mem_nil_iff, nil_validIn]
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

-- end Walk.ValidIn

-- namespace IsWalkFrom

-- lemma setConnected (hWF : G.IsWalkFrom S T w) : G.SetConnected S T := by
--   obtain ⟨hVd, hfirst, hlast⟩ := hWF
--   use w.first, hfirst, w.last, hlast, hVd.connected

-- lemma left_subset (hWF : G.IsWalkFrom S T w) (hsubset : S ∩ G.V ⊆ S') : G.IsWalkFrom S' T w where
--   validIn := hWF.validIn
--   first_mem := hsubset ⟨hWF.first_mem, hWF.validIn.vx_mem_of_mem Walk.first_mem⟩
--   last_mem := hWF.last_mem

-- lemma left_subset' (hWF : G.IsWalkFrom S T w) (hsubset : S ⊆ S') : G.IsWalkFrom S' T w where
--   validIn := hWF.validIn
--   first_mem := hsubset hWF.first_mem
--   last_mem := hWF.last_mem

-- lemma right_subset (hWF : G.IsWalkFrom S T w) (hsubset : T ∩ G.V ⊆ T') :
    -- G.IsWalkFrom S T' w where
--   validIn := hWF.validIn
--   first_mem := hWF.first_mem
--   last_mem := hsubset ⟨hWF.last_mem, hWF.validIn.vx_mem_of_mem Walk.last_mem⟩

-- lemma right_subset' (hWF : G.IsWalkFrom S T w) (hsubset : T ⊆ T') : G.IsWalkFrom S T' w where
--   validIn := hWF.validIn
--   first_mem := hWF.first_mem
--   last_mem := hsubset hWF.last_mem

-- lemma left_right_subset (hWF : G.IsWalkFrom S T w) (hS : S ∩ G.V ⊆ S') (hT : T ∩ G.V ⊆ T') :
--     G.IsWalkFrom S' T' w := hWF.left_subset hS |>.right_subset hT

-- lemma left_right_subset' (hWF : G.IsWalkFrom S T w) (hS : S ⊆ S') (hT : T ⊆ T') :
--     G.IsWalkFrom S' T' w := hWF.left_subset' hS |>.right_subset' hT


-- end IsWalkFrom

end Graph
