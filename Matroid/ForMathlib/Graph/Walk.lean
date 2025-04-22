import Matroid.ForMathlib.Graph.Basic
import Mathlib.Data.List.Basic

open Function Set List

variable {α β : Type*} {e e' f : β} {x y z u v : α} {G : Graph α β}

inductive Walk (α β : Type*) where
| nil (u : α) : Walk α β
| cons (u : α) (e : β) (W : Walk α β) : Walk α β

namespace Walk
variable {w w₁ w₂ : Walk α β}

def Nonempty : Walk α β → Prop
| nil _ => False
| cons _ _ _ => True

def start : Walk α β → α
| nil x => x
| cons x _ _ => x

def finish : Walk α β → α
| nil x => x
| cons _ _ w => w.finish

def ValidIn (w : Walk α β) (G : Graph α β) : Prop :=
  match w with
  | nil x => x ∈ G.V
  | cons x e w => G.Inc₂ e x w.start ∧ w.ValidIn G

def vx : Walk α β → List α
| nil x => [x]
| cons x _e w => x :: w.vx

instance : Membership α (Walk α β) where
  mem w x := x ∈ w.vx

instance [DecidableEq α] : Decidable (x ∈ w) := by
  change Decidable (x ∈ w.vx)
  infer_instance

@[simp]
lemma mem_iff : (x ∈ w) = (x ∈ w.vx) := rfl

def edge : Walk α β → List β
| nil _ => []
| cons _ e w => e :: w.edge

def length : Walk α β → ℕ
| nil _ => 0
| cons _ _ w => w.length + 1

def concat : Walk α β → β → α → Walk α β
| nil x, e, y => cons x e (nil y)
| cons x e w, f, y => cons x e (w.concat f y)

def dropLast : Walk α β → Walk α β
| nil x => nil x
| cons x _ (nil _) => nil x
| cons x e (cons y e' w) => cons x e ((cons y e' w).dropLast)

/-- Append one walk `w` to another walk `w'` by replacing the last vertex of `w` with the walk `w'`.
(Intended for the case where `w.last = w'.first`; the last vertex of `w` is ignored)  -/
def append : Walk α β → Walk α β → Walk α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

instance instAppend : Append (Walk α β) where
  append := append

def IsPrefix : Walk α β → Walk α β → Prop :=
  fun W w => ∃ w', W = w ++ w'

def IsSuffix : Walk α β → Walk α β → Prop :=
  fun W w => ∃ w', W = w' ++ w

def reverse : Walk α β → Walk α β
| nil x => nil x
| cons x e w => w.reverse.concat e x

def startAt [DecidableEq α] (w : Walk α β) (u : α) (h : u ∈ w) : Walk α β :=
  match w with
  | nil x => nil x
  | cons x e w =>
    if hin : u ∈ w
    then startAt w u hin
    else cons x e w

@[simp]
lemma cons_length : (cons x e w).length = w.length + 1 := rfl

lemma startAt_length_le [DecidableEq α] {w : Walk α β} (h : u ∈ w) :
    (startAt w u h).length ≤ w.length := by
  match w with
  | nil x => simp [startAt]
  | cons x e w =>
    simp only [startAt, cons_length]
    split_ifs with hin
    · have := startAt_length_le hin
      omega
    · simp

def dedup [DecidableEq α] : Walk α β → Walk α β
| nil x => nil x
| cons x e w =>
  if h : x ∈ w
  then by
    have := startAt_length_le h
    exact (startAt w x h).dedup
  else cons x e (dedup w)
termination_by w => w.length

@[simp] lemma cons_vx : (cons x e w).vx = x :: w.vx := rfl

@[simp] lemma nil_vx : (nil x : Walk α β).vx = [x] := rfl

@[simp] lemma nil_edge : (nil x : Walk α β).edge = [] := rfl

@[simp] lemma nil_length : (nil x : Walk α β).length = 0 := rfl

@[simp] lemma nil_start : (nil x : Walk α β).start = x := rfl

@[simp] lemma nil_finish : (nil x : Walk α β).finish = x := rfl

@[simp] lemma nil_ValidIn_iff : (nil x : Walk α β).ValidIn G ↔ x ∈ G.V := by
  simp only [ValidIn]

@[simp] lemma nil_injective : Injective (nil : α → Walk α β) := by
  rintro x y h
  rwa [nil.injEq] at h

-- @[simp] lemma nil_inj : (nil x : Walk α β) = nil y ↔ x = y := by
--   rw [nil.injEq]

@[simp] lemma cons_edge : (cons x e w).edge = e :: w.edge := rfl

@[simp] lemma cons_start : (cons x e w).start = x := rfl

@[simp] lemma cons_finish : (cons x e w).finish = w.finish := rfl

@[simp] lemma cons_ValidIn (hw : w.ValidIn G) (he : G.Inc₂ e x w.start) :
  (cons x e w).ValidIn G := ⟨he, hw⟩

@[simp] lemma cons_ValidIn_iff : (cons x e w).ValidIn G ↔ G.Inc₂ e x w.start ∧ w.ValidIn G :=
  ⟨fun h => h, fun h => h⟩

lemma ValidIn.of_cons (hw : (cons x e w).ValidIn G) : w.ValidIn G := by
  rw [cons_ValidIn_iff] at hw
  exact hw.2

lemma cons_vx_nodup (h : (cons x e w).vx.Nodup) : w.vx.Nodup := by
  simp only [cons_vx, nodup_cons] at h
  exact h.2

lemma vx_ne_nil : w.vx ≠ [] := by
  match w with
  | nil x => simp
  | cons x e w => simp

@[simp]
lemma mem_vx_nil_iff : x ∈ (nil u : Walk α β) ↔ x = u := by
  simp only [mem_iff, nil_vx, mem_cons, not_mem_nil, or_false]

@[simp]
lemma mem_vx_cons_iff : x ∈ (cons u e w) ↔ x = u ∨ x ∈ w := by
  simp only [mem_iff, cons_vx, mem_cons]

@[simp]
lemma mem_edge_nil_iff : e ∈ (nil u : Walk α β).edge ↔ False := by
  simp only [nil_edge, mem_nil_iff]

@[simp]
lemma mem_edge_cons_iff : e ∈ (cons u e' w).edge ↔ e = e' ∨ e ∈ w.edge := by
  simp only [cons_edge, mem_cons]

@[simp]
lemma start_vx_mem : w.start ∈ w.vx := by
  match w with
  | nil x => simp only [nil_vx, nil_start, mem_cons, not_mem_nil, or_false]
  | cons x e w => simp only [cons_vx, cons_start, mem_cons, true_or]

lemma start_eq_vx_head {w : Walk α β} : w.start = w.vx.head vx_ne_nil := by
  match w with
  | nil x => rfl
  | cons x e w => rfl

@[simp]
lemma finish_vx_mem {w : Walk α β} : w.finish ∈ w.vx := by
  match w with
  | nil x => simp
  | cons x e w =>
    simp only [cons_vx, cons_finish, mem_cons]
    right
    exact finish_vx_mem

lemma finish_eq_vx_getLast {w : Walk α β} : w.finish = w.vx.getLast vx_ne_nil := by
  match w with
  | nil x => rfl
  | cons x e w =>
    simp only [cons_finish, cons_vx, ne_eq, vx_ne_nil, not_false_eq_true, getLast_cons]
    apply finish_eq_vx_getLast

lemma ValidIn.mem_of_mem_vx {w : Walk α β} (h : w.ValidIn G) (hmem : x ∈ w.vx) :
    x ∈ G.V := by
  match w with
  | nil y =>
    simp only [nil_vx, mem_cons, not_mem_nil, or_false] at hmem
    subst x
    exact h
  | cons y e w =>
    obtain ⟨hbtw, hVd⟩ := h
    obtain rfl | h : x = y ∨ x ∈ w.vx := by simpa using hmem
    · exact hbtw.vx_mem_left
    · exact hVd.mem_of_mem_vx h

lemma ValidIn.mem_of_mem_edge {w : Walk α β} (h : w.ValidIn G) (hmem : e ∈ w.edge) :
    e ∈ G.E := by
  match w with
  | nil x => simp at hmem
  | cons x e' w =>
    obtain ⟨hbtw, hVd⟩ := h
    obtain rfl | h : e = e' ∨ e ∈ w.edge := by simpa using hmem
    · exact hbtw.edge_mem
    · exact hVd.mem_of_mem_edge h


lemma Nonempty.exists_cons : w.Nonempty → ∃ x e w', w = cons x e w' := by
  induction w with
  | nil x => simp only [Nonempty, reduceCtorEq, exists_false, imp_self]
  | cons x e w ih => simp only [cons.injEq, exists_and_left, exists_eq', and_true, implies_true]

lemma Nonempty.iff_exists_cons : w.Nonempty ↔ ∃ x e w', w = cons x e w' := by
  constructor
  · apply Nonempty.exists_cons
  · rintro ⟨x, e, w', rfl⟩
    simp only [Nonempty, cons.injEq, exists_and_left, exists_eq', and_true, implies_true]

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

lemma start_eq_finish_of_not_nonempty (h : ¬ w.Nonempty) : w.start = w.finish := by
  match w with
  | nil x => simp only [nil_start, nil_finish]
  | cons x e w => simp only [Nonempty.cons_true, not_true_eq_false] at h

@[simp]
lemma start_eq_finish_iff (hnodup : w.vx.Nodup) : w.start = w.finish ↔ ¬ w.Nonempty := by
  match w with
  | .nil x => simp only [nil_start, nil_finish, Nonempty.not_nil, not_false_eq_true]
  | .cons x e w =>
    simp only [cons_vx, nodup_cons, cons_start, cons_finish, Nonempty.cons_true, not_true_eq_false,
      iff_false, ne_eq] at hnodup ⊢
    exact fun h => hnodup.1 (h ▸ finish_vx_mem)

@[simp]
lemma start_ne_finish_iff (hnodup : w.vx.Nodup) : w.start ≠ w.finish ↔ w.Nonempty :=
  (start_eq_finish_iff hnodup).not_left

/- Properties of append operation -/
@[simp]
lemma append_notation : append w₁ w₂ = w₁ ++ w₂ := rfl

@[simp]
lemma nil_append : nil x ++ w₂ = w₂ := by
  simp only [← append_notation, append]

@[simp]
lemma cons_append : cons x e w₁ ++ w₂ = cons x e (w₁ ++ w₂) := by
  simp only [← append_notation, append]

@[simp]
lemma append_vx : (w₁ ++ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil x => simp
  | cons x e w ih =>
    simp only [append_notation, append, cons_vx]
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil, List.cons_append]
    simpa

lemma append_vx' {w₁ w₂ : Walk α β} (heq : w₁.finish = w₂.start) :
    (w₁ ++ w₂).vx = w₁.vx ++ w₂.vx.tail := by
  match w₁ with
  | .nil x =>
    simp_all only [nil_finish, append_vx, nil_vx, dropLast_single, nil_append, cons_append]
    rw [start_eq_vx_head]
    exact (head_cons_tail w₂.vx vx_ne_nil).symm
  | .cons x e w =>
    simp only [cons_finish, cons_append, cons_vx, List.cons_append, List.cons.injEq,
      true_and] at heq ⊢
    exact append_vx' heq

@[simp]
lemma append_edge {w₁ w₂ : Walk α β} : (w₁ ++ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil x => simp only [nil_append, nil_edge, List.nil_append]
  | cons x e w ih => simp only [cons_append, cons_edge, ih, List.cons_append]

@[simp]
lemma append_length : (w₁ ++ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil x => simp
  | cons x e w ih => simp [ih, Nat.add_right_comm]

@[simp]
lemma append_nil (h : w.finish = x) : w ++ (nil x) = w := by
  induction w with
  | nil u => aesop
  | cons u e W ih =>
    rw [cons_finish] at h
    rw [cons_append, ih h]

@[simp]
lemma append_start_of_eq (h : w₁.finish = w₂.start):
  (w₁ ++ w₂).start = w₁.start := by
  induction w₁ with
  | nil x => simp only [nil_append, ← h, nil_finish, nil_start]
  | cons x e w ih => simp only [cons_append, cons_start]

@[simp]
lemma append_start_of_nonempty (h : w₁.Nonempty) :
  (w₁ ++ w₂).start = w₁.start := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at h
  | cons x e w ih => simp only [cons_append, cons_start]

@[simp]
lemma append_finish :
  (w₁ ++ w₂).finish = w₂.finish := by
  induction w₁ with
  | nil x => simp only [nil_append]
  | cons x e w ih => simp only [cons_append, cons_finish, ih]

lemma append_assoc (w1 w2 w3 : Walk α β) : (w1 ++ w2) ++ w3 = w1 ++ (w2 ++ w3) := by
  induction w1 with
  | nil x => simp only [nil_append]
  | cons x e w ih => simp only [cons_append, ih]

lemma append_right_injective : Injective (w ++ ·) := by
  rintro w₁ w₂ h
  induction w with
  | nil x => simpa only [nil_append] using h
  | cons x e w ih =>
    simp only [cons_append, cons.injEq, true_and] at h
    exact ih h

@[simp]
lemma append_right_inj : w ++ w₁ = w ++ w₂ ↔ w₁ = w₂ := by
  constructor
  · apply append_right_injective
  · rintro rfl
    rfl

@[simp]
lemma append_right_eq_self : w ++ w₁ = w ↔ w₁ = nil w.finish := by
  induction w with
  | nil x => simp only [nil_append, nil_finish]
  | cons x e w ih => simpa only [cons_append, cons.injEq, true_and, cons_finish]

@[simp]
lemma append_left_eq_self : w₁ ++ w = w ↔ ¬ w₁.Nonempty := by
  refine ⟨fun h ↦ by simpa [← length_pos_iff] using congr_arg length h, fun h ↦ ?_⟩
  obtain ⟨x, rfl⟩ := by simpa using h
  rfl

@[simp]
lemma append_eq_nil_iff : w₁ ++ w₂ = nil x ↔ (∃ y, w₁ = nil y) ∧ w₂ = nil x := by
  induction w₁ with
  | nil y => simp only [nil_append, nil.injEq, exists_eq', true_and]
  | cons y e w ih => simp only [cons_append, reduceCtorEq, exists_false, false_and]

lemma append_ValidIn (h : w₁.finish = w₂.start) (h₁ : w₁.ValidIn G) (h₂ : w₂.ValidIn G) :
  (w₁ ++ w₂).ValidIn G := by
  induction w₁ with
  | nil x => simpa
  | cons x e w₁ ih =>
    simp only [cons_finish] at h
    refine ⟨?_, by simp [ih h h₁.2]⟩
    convert h₁.1 using 1
    exact append_start_of_eq h

lemma ValidIn.append_left_ValidIn (h : w₁.finish = w₂.start) (hw₁ : w₁.Nonempty)
    (hVd : (w₁ ++ w₂).ValidIn G) : w₁.ValidIn G := by
  induction w₁ with
  | nil x => simp only [Nonempty.not_nil] at hw₁
  | cons x e w ih =>
    simp only [cons_append, cons_ValidIn_iff] at hVd
    by_cases hNonempty : w.Nonempty
    · refine ⟨?_, ih h hNonempty hVd.2⟩
      convert hVd.1 using 1
      simp only [hNonempty, append_start_of_nonempty]
    · simp only [Nonempty.not_iff] at hNonempty
      obtain ⟨y, rfl⟩ := hNonempty
      simp only [cons_finish, nil_finish, nil_append, cons_ValidIn_iff, nil_start,
        nil_ValidIn_iff] at h hVd ⊢
      subst y
      refine ⟨hVd.1, hVd.2.mem_of_mem_vx start_vx_mem⟩

lemma ValidIn.append_right_ValidIn (hVd : (w₁ ++ w₂).ValidIn G) : w₂.ValidIn G := by
  induction w₁ with
  | nil x => simpa only [nil_append] using hVd
  | cons x e w ih =>
    simp only [cons_append, cons_ValidIn_iff] at hVd
    exact ih hVd.2

lemma ValidIn.finish_eq_start (hw₁ : w₁.Nonempty) (hVd₁ : w₁.ValidIn G) (hVd : (w₁ ++ w₂).ValidIn G) :
  w₁.finish = w₂.start := by


  match w₁ with
  | nil x => simp at hw₁
  | cons x e w₁ =>
  induction w₁ with
  | nil u =>
  simp_all only [Nonempty.cons_true, cons_ValidIn_iff, nil_start, nil_ValidIn_iff, cons_append,
    nil_append, cons_finish, nil_finish]
  exact hVd₁.1.eq_of_inc₂ hVd.1
  | cons u f w₁ ih =>
  simp_all only [Nonempty.cons_true, cons_ValidIn_iff, cons_append, cons_finish, and_imp,
    forall_const, cons_start, true_and, implies_true]

  rw [append_start_of_nonempty] at hVd


  -- simp only [cons_append, cons_ValidIn_iff] at hVd
  -- rw [append_start_of_nonempty] at hVd

    -- simp_all only [Nonempty.cons_true, cons_append, cons_ValidIn_iff, cons_finish, forall_const]
    -- by_cases hNonempty : w.Nonempty
    -- · simp_all only [forall_const, append_start_of_eq, true_and]
    -- · simp only [Nonempty.not_iff] at hNonempty
    --   obtain ⟨y, rfl⟩ := hNonempty
    --   simp_all only [Nonempty.not_nil, nil_finish, IsEmpty.forall_iff, nil_start, nil_ValidIn_iff,
    --     nil_append]
    --   exact hVd₁.1.eq_of_Inc₂ hVd.1
