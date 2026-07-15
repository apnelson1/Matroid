import Matroid.Graph.WList.Sublist

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w' w₀ w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

/-! # Cutting wLists Off -/

section pred

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

variable {Q : β → Prop} [DecidablePred Q]

/-- Take the prefix ending at the tail of the first edge satisfying `Q`.
Equal to `w` if no edge satisfies `Q`. -/
def prefixUntilEdge (w : WList α β) (Q : β → Prop) [DecidablePred Q] : WList α β :=
  match w with
  | nil x => nil x
  | cons x e w => if Q e then nil x else cons x e (prefixUntilEdge w Q)

@[simp] lemma prefixUntilEdge_nil : (nil u (β := β)).prefixUntilEdge Q = nil u := rfl

@[grind =]
lemma prefixUntilEdge_cons (w) :
    (cons x e w).prefixUntilEdge Q = if Q e then nil x else cons x e (w.prefixUntilEdge Q) :=
  rfl

@[simp]
lemma prefixUntilEdge_cons_true (he : Q e) : (cons x e w).prefixUntilEdge Q = nil x := by
  grind

@[simp]
lemma prefixUntilEdge_cons_false (he : ¬ Q e) :
    (cons x e w).prefixUntilEdge Q = cons x e (w.prefixUntilEdge Q) := by
  grind

lemma prefixUntilEdge_isPrefix (w : WList α β) (Q : β → Prop) [DecidablePred Q] :
    (w.prefixUntilEdge Q).IsPrefix w := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [prefixUntilEdge_cons]
    split_ifs
    · simp
    exact ih.cons ..

lemma prefixUntilEdge_length_lt (hQ : ∃ e ∈ E(w), Q e) :
    (w.prefixUntilEdge Q).length < w.length := by
  induction w with
  | nil u => simp at hQ
  | cons u e w ih =>
    simp only [cons_edgeSet, Set.mem_insert_iff, mem_edgeSet_iff, exists_eq_or_imp] at hQ
    grind

/-- Take the suffix starting at the head of the first edge satisfying `Q`.
Equal to `nil w.last` if no edge satisfies `Q`. -/
def suffixFromEdge (w : WList α β) (Q : β → Prop) [DecidablePred Q] : WList α β :=
  match w with
  | nil x => nil x
  | cons _ e w => if Q e then w else suffixFromEdge w Q

@[simp] lemma suffixFromEdge_nil : (nil u (β := β)).suffixFromEdge Q = nil u := rfl

@[grind =]
lemma suffixFromEdge_cons (w) :
    (cons x e w).suffixFromEdge Q = if Q e then w else w.suffixFromEdge Q := rfl

@[simp]
lemma suffixFromEdge_cons_true (he : Q e) : (cons x e w).suffixFromEdge Q = w := by
  grind [suffixFromEdge]

@[simp]
lemma suffixFromEdge_cons_false (he : ¬ Q e) :
    (cons x e w).suffixFromEdge Q = (w.suffixFromEdge Q) := by
  grind

lemma suffixFromEdge_isSuffix (w : WList α β) (Q : β → Prop) [DecidablePred Q] :
    (w.suffixFromEdge Q).IsSuffix w := by
  induction w with
  | nil u => simp
  | cons u e w ih =>
    simp only [suffixFromEdge_cons]
    split_ifs
    · simp
    exact ih.trans (by simp)

lemma suffixFromEdge_length_lt (hQ : ∃ e ∈ E(w), Q e) : (w.suffixFromEdge Q).length < w.length := by
  induction w with
  | nil u => simp at hQ
  | cons u e w ih =>
    simp only [cons_edgeSet, Set.mem_insert_iff, mem_edgeSet_iff, exists_eq_or_imp] at hQ
    grind

/-- The prefix of `w` ending just before the first occurrence of edge `e`.
Equal to `w` if `e ∉ w.edge`. -/
def prefixUntilEdgeLabel [DecidableEq β] (w : WList α β) (e : β) : WList α β :=
  w.prefixUntilEdge (· = e)

/-- The suffix of `w` starting just after the first occurrence of edge `e`.
Equal to `nil w.last` if `e ∉ w.edge`. -/
def suffixFromEdgeLabel [DecidableEq β] (w : WList α β) (e : β) : WList α β :=
  w.suffixFromEdge (· = e)

/-- Take the prefix of `w` ending at the last occurence of `x` in `w`.
Equal to `w` if `x ∉ w`. -/
def prefixUntilLast (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  (w.reverse.suffixFrom P).reverse

/-- Take the suffix of `w` starting at the last occurence of `P` in `w`.
If `P` never occurs, this is all of `w`. -/
def suffixFromLast (w : WList α β) (P : α → Prop) [DecidablePred P] : WList α β :=
  (w.reverse.prefixUntil P).reverse

end pred

section index

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

end index

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

end WList
