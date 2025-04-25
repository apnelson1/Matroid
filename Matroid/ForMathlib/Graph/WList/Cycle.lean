import Matroid.ForMathlib.Graph.WList.Sublist
import Mathlib.Data.List.Rotate

variable {α β : Type*} {x y z u v : α} {e f : β} {w : WList α β} (m n : ℕ)

open Set WList



namespace WList

/-- A `WList` is closed if its first and last entries are equal. -/
def IsClosed (w : WList α β) : Prop := w.first = w.last

@[simp]
lemma nil_isClosed (x : α) : (nil x (β := β)).IsClosed := rfl

@[simp]
lemma cons_isClosed_iff : (cons x e w).IsClosed ↔ x = w.last := by
  simp [IsClosed]

@[simp]
lemma concat_isClosed_iff : (w.concat e x).IsClosed ↔ x = w.first := by
  simp [IsClosed, eq_comm]

lemma IsClosed.vxSet_tail (h : w.IsClosed) : w.tail.vxSet = w.vxSet := by
  induction w with simp_all

lemma IsClosed.reverse (h : w.IsClosed) : w.reverse.IsClosed := by
  simp_all [IsClosed]

@[simp]
lemma reverse_isClosed_iff : w.reverse.IsClosed ↔ w.IsClosed := by
  simp [IsClosed, eq_comm]

/-- Rotate a WList `n` vertices to the left.
This behaves badly (forgets the first vertex) if the list isn't closed. -/
protected def rotate : WList α β → ℕ → WList α β
  | w, 0 => w
  | nil x, _ => nil x
  | cons _ e w, n + 1 => (w.concat e w.first).rotate n

@[simp]
lemma cons_rotate_one : (cons x e w).rotate 1 = w.concat e w.first := by
  simp [WList.rotate]

@[simp]
lemma rotate_cons_succ (w : WList α β) (x e) (n : ℕ) :
  (cons x e w).rotate (n+1) = (w.concat e w.first).rotate n := rfl

@[simp]
lemma rotate_nil (x : α) (n : ℕ) : (nil x (β := β)).rotate n = nil x := by
  unfold WList.rotate
  aesop

@[simp]
lemma rotate_zero (w : WList α β) : w.rotate 0 = w := by
  simp [WList.rotate]

@[simp]
lemma rotate_rotate : ∀ (w : WList α β) (m n : ℕ), (w.rotate m).rotate n = w.rotate (m + n)
  | nil x, _, _=> by simp
  | cons x e w, 0, n => by simp
  | cons x e w, m+1, n => by
    rw [rotate_cons_succ, rotate_rotate, Nat.add_right_comm, ← rotate_cons_succ]

lemma rotate_induction {motive : WList α β → Prop} (h0 : motive w)
    (rotate : ∀ ⦃w⦄, motive w → motive (w.rotate 1)) (n : ℕ) : motive (w.rotate n) := by
  induction n with | zero => simpa | succ n IH => rw [← rotate_rotate]; exact rotate IH

lemma IsClosed.rotate (hw : w.IsClosed) (n : ℕ) : (w.rotate n).IsClosed :=
  rotate_induction hw (by rintro (x | ⟨u, e, w⟩) hw <;> simp) n

@[simp]
lemma rotate_edge (w : WList α β) (n : ℕ) : (w.rotate n).edge = w.edge.rotate n := by
  suffices aux : ∀ (w : WList α β), (w.rotate 1).edge = w.edge.rotate 1 by induction n with
    | zero => simp | succ n IH => rw [← rotate_rotate, aux, ← List.rotate_rotate, IH]
  rintro (w | ⟨x, e, w⟩) <;> simp

@[simp]
lemma rotate_vx_tail (w : WList α β) (n : ℕ) : (w.rotate n).tail.vx = w.tail.vx.rotate n := by
  suffices aux : ∀ (w : WList α β), (w.rotate 1).tail.vx = w.tail.vx.rotate 1 by induction n with
    | zero => simp | succ n IH => rw [← rotate_rotate, aux, ← List.rotate_rotate, IH]
  rintro (w | ⟨x, e, (w | ⟨y, f, w⟩)⟩) <;> simp

-- @[simp]
-- lemma rotate_edgeSet (w : WList α β) (n) : (w.rotate n).vxSet = w.vxSet := by
--   induction n generalizing w with
--   | zero => simp
--   | succ n IH =>
--     rw [Nat.add_comm, ← rotate_rotate, IH]
--     cases w with
--     | nil u => simp
--     | cons u e w =>
--       simp

end WList

-- @[mk_iff]
-- structure IsCycleIn (G : Graph α β) (W : Walk α β) : Prop where
--   validIn : W.ValidIn G
--   nodup' : W.vx.dropLast.Nodup
--   closed : W.first = W.last

-- lemma IsPath.not_isCycle (hP : G.IsPath w) (hnonempty : w.Nonempty) : ¬ w.IsCycleIn G := by
--   suffices heq : w.first ≠ w.last by
--     rintro ⟨hVd, hnodup, hclosed⟩
--     exact heq hclosed
--   rwa [first_ne_last_iff hP.nodup]

-- lemma ValidIn.isCycleIn (hVd : w.ValidIn G) (hvx : w.vx.dropLast.Nodup)
--     (hclosed : w.first = w.last) : w.IsCycleIn G := ⟨hVd, hvx, hclosed⟩

-- lemma IsCycle.exist_paths_of_mem_of_mem {C : Walk α β} (hC : C.IsCycleIn G)
--     (hx : x ∈ C.vx) (hy : y ∈ C.vx) (hne : x ≠ y) :
--     ∃ P Q, G.IsPath P ∧ G.IsPath Q ∧ P.first = x ∧ Q.first = x ∧ P.first = y ∧ Q.first = y ∧
--     P.toGraph ∪ Q.toGraph = C.toGraph := sorry
