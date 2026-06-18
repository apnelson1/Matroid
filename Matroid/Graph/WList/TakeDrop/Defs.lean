import Matroid.Graph.WList.Sublist

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

/-! # Cutting wLists Off -/

variable {P : α → Prop} [DecidablePred P]

/-- Take the prefix ending at the first vertex satisfying a predicate `P`
(or the entire wList if nothing satisfies `P`). -/
def prefixUntil (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  match w with
  | nil x => nil x
  | cons x e w => if P x then nil x else cons x e (prefixUntil w P)

@[simp] lemma prefixUntil_nil : (nil u (β := β)).prefixUntil P = nil u := rfl

@[simp, grind =]
lemma prefixUntil_cons (w) :
    (cons x e w).prefixUntil P = if P x then nil x else cons x e (w.prefixUntil P) := rfl

/-- The prefix of `w` ending at a vertex `x`. Equal to `w` if `x ∉ w`. -/
def prefixUntilVertex [DecidableEq α] (w : WList α β) (x : α) : WList α β := w.prefixUntil (· = x)

@[simp]
lemma prefixUntilVertex_nil [DecidableEq α] : (nil (β := β) u).prefixUntilVertex x = nil u := by
  simp [prefixUntilVertex]

@[simp]
lemma prefixUntilVertex_cons_eq_nil [DecidableEq α] (u e) (w : WList α β) :
    (cons u e w).prefixUntilVertex u = nil u := by
  simp [prefixUntilVertex, prefixUntil_cons]

lemma prefixUntilVertex_cons [DecidableEq α] (u e) (w : WList α β) :
    (cons u e w).prefixUntilVertex x = if u = x then nil u else
    cons u e (w.prefixUntilVertex x) := by
  simp [prefixUntilVertex, prefixUntil]

/-- Take the suffix starting at the first vertex satisfying a predicate `P`,
(or the `Nil` wList on the last vertex if nothing satisfies `P`) -/
def suffixFrom (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  match w with
  | nil x => nil x
  | cons x e w => if P x then cons x e w else suffixFrom w P

@[simp] lemma suffixFrom_nil : (nil u (β := β)).suffixFrom P = nil u := rfl

@[simp, grind =]
lemma suffixFrom_cons (w) :
    (cons x e w).suffixFrom P = if P x then cons x e w else w.suffixFrom P := rfl

lemma suffixFrom_isSuffix (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.suffixFrom P).IsSuffix w := by
  induction w with
  | nil u => simp
  | cons u e W ih =>
    simp only [suffixFrom_cons]
    split_ifs
    · simp
    exact ih.trans (by simp)

/-- The suffix of `w` starting at the first occurence of a vertex `x`.
Equal to `[w.last]` if `x ∉ w`. -/
def suffixFromVertex [DecidableEq α] (w : WList α β) (x : α) : WList α β := w.suffixFrom (· = x)

@[simp]
lemma suffixFromVertex_nil [DecidableEq α] : (nil (β := β) u).suffixFromVertex x = nil u := by
  simp [suffixFromVertex]

lemma suffixFromVertex_isSuffix [DecidableEq α] (w : WList α β) (x : α) :
    (w.suffixFromVertex x).IsSuffix w := suffixFrom_isSuffix ..

/-- Take the prefix of `w` ending at the last occurence of `x` in `w`.
Equal to `w` if `x ∉ w`. -/
def prefixUntilLast (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  (w.reverse.suffixFrom P).reverse

/-- Take the suffix of `w` starting at the last occurence of `P` in `w`.
If `P` never occurs, this is all of `w`. -/
def suffixFromLast (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  (w.reverse.prefixUntil P).reverse

section drop

/-- Remove the first vertex and edge from a wList -/
def tail : WList α β → WList α β
  | nil x => nil x
  | cons _ _ w => w

@[simp, grind =]
lemma tail_nil (x : α) : (nil x (β := β)).tail = nil x := rfl

@[simp, grind =]
lemma tail_cons (x e) (w : WList α β) : (cons x e w).tail = w := rfl

/-- Remove the last edge and vertex from a wList. This is the reverse of the reversed tail. -/
def dropLast : WList α β → WList α β
| nil x => nil x
| cons x _ (nil _) => nil x
| cons x e (cons y e' w) => cons x e ((cons y e' w).dropLast)

@[simp]
lemma dropLast_nil : (nil x : WList α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_nil : (cons x e (nil y) : WList α β).dropLast = nil x := rfl

@[simp]
lemma dropLast_cons_cons :
  (cons x e (cons y e' w) : WList α β).dropLast = cons x e ((cons y e' w).dropLast) := rfl

variable {n m : ℕ}

/-- Take the first `n` vertices from a `WList`. Returns the entire list if `n ≥ w.length + 1`. -/
def take : WList α β → ℕ → WList α β
  | nil x, _ => nil x
  | cons x _ _, 0 => nil x
  | cons x e w, n+1 => cons x e (w.take n)

@[simp]
lemma take_nil (x : α) (n : ℕ) : (nil x (β := β)).take n = nil x := rfl

@[simp]
lemma take_zero (w : WList α β) : w.take 0 = nil w.first := by
  cases w with simp [take]

@[simp]
lemma take_cons_succ (x e) (w : WList α β) (n : ℕ) :
  (cons x e w).take (n+1) = cons x e (w.take n) := rfl

/-- Drop the first `n` vertices from a `WList`. Returns `nil w.last` if `n ≥ w.length + 1`. -/
def drop : WList α β → ℕ → WList α β
  | w, 0 => w
  | nil x, _ => nil x
  | cons _ _ w, n+1 => w.drop n

@[simp]
lemma drop_zero (w : WList α β) : w.drop 0 = w := by
  match w with
  | .nil u => rfl
  | .cons u e w => rfl

@[simp]
lemma drop_nil (x : α) (n : ℕ) : (nil x (β := β)).drop n = nil x := by
  match n with
  | 0 => rfl
  | n + 1 => rfl

@[simp]
lemma drop_cons_succ (x e) (w : WList α β) (n : ℕ) :
  (cons x e w).drop (n+1) = w.drop n := rfl

end drop

section dedup

variable [DecidableEq α]

/-- Remove duplicate vertices from a `WList` to give a duplicate-free sublist. -/
def dedup : WList α β → WList α β
  | nil x => nil x
  | cons x e w =>
    have := (w.suffixFromVertex_isSuffix x).length_le
    if x ∈ w then dedup (w.suffixFromVertex x) else cons x e (dedup w)
  termination_by w => w.length

@[simp]
lemma dedup_nil (x : α) : (nil x (β := β)).dedup = nil x := by
  simp [dedup]

end dedup

section deloop

variable [DecidableEq α]

/-- Remove loops from a `WList` by removing edges where the source equals the target. -/
def deloop : WList α β → WList α β
| nil x => nil x
| cons x e w =>
  if x = w.first then deloop w else cons x e (deloop w)

@[simp]
lemma deloop_nil (x : α) : (nil x (β := β)).deloop = nil x := by
  simp [deloop]

@[grind =]
lemma deloop_cons_eq_ite (x : α) (e : β) (w : WList α β) :
    (cons x e w).deloop = if x = w.first then deloop w else cons x e w.deloop := by
  simp [deloop]

end deloop

section noLoop

/-- A `WList` has no loops if no edge connects a vertex to the next vertex being itself. -/
def NoLoop : WList α β → Prop
  | nil _ => True
  | cons x _ w => x ≠ w.first ∧ w.NoLoop

@[simp]
lemma noLoop_nil (x : α) : (nil x (β := β)).NoLoop := by
  simp [NoLoop]

@[simp]
lemma noLoop_cons (x : α) (e : β) (w : WList α β) :
    (cons x e w).NoLoop ↔ x ≠ w.first ∧ w.NoLoop := by
  simp [NoLoop]

end noLoop

section edgeRemove

variable [DecidablePred (· ∈ F)]

/-- Remove edges from a `WList` that belong to a given edge set `F`. -/
def edgeRemove (F : Set β) [DecidablePred (· ∈ F)] : WList α β → WList α β
  | nil x => nil x
  | cons x e w => if e ∈ F then edgeRemove F w else cons x e (edgeRemove F w)

@[simp]
lemma edgeRemove_nil : (nil x (β := β)).edgeRemove F = nil x := rfl

@[grind =]
lemma edgeRemove_cons (x : α) (e : β) (w : WList α β) :
    (cons x e w).edgeRemove F = if e ∈ F then edgeRemove F w else cons x e (w.edgeRemove F) :=
  rfl

end edgeRemove

end WList
