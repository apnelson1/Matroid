import Matroid.ForMathlib.Graph.Walk.Subwalk
import Matroid.ForMathlib.Graph.Subgraph
import Mathlib.Data.List.Rotate

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {w : Graph.Walk α β}

open Set

namespace Graph

namespace Walk

/-
x₀ e₁ [x₁ e₂ x₂ e₃ x₃ e₄ x₀] ->  [x₁ e₂ x₂ e₃ x₃ e₄ x₀] e₁ x₁
-/

/-- Rotate a walk `n` vertices to the left. This behaves badly if the walk isn't closed. -/
protected def rotate : Walk α β → ℕ → Walk α β
  | w, 0 => w
  | nil x, _ => nil x
  | cons _ e w, n + 1 => (w.concat e w.first).rotate n

def IsClosed (w : Walk α β) : Prop := w.first = w.last

@[simp]
lemma cons_rotate_one : (cons x e w).rotate 1 = w.concat e w.first := by
  simp [Walk.rotate]

@[simp]
lemma rotate_cons_succ (w : Walk α β) (x e) (n : ℕ) :
  (cons x e w).rotate (n+1) = (w.concat e w.first).rotate n := rfl

@[simp]
lemma rotate_nil (x : α) (n : ℕ) : (nil x (β := β)).rotate n = nil x := by
  unfold Walk.rotate
  aesop

@[simp]
lemma rotate_zero (w : Walk α β) : w.rotate 0 = w := by
  simp [Walk.rotate]

@[simp]
lemma rotate_rotate : ∀ (w : Walk α β) (m n : ℕ), (w.rotate m).rotate n = w.rotate (m + n)
  | nil x, _, _=> by simp
  | cons x e w, 0, n => by simp
  | cons x e w, m+1, n => by
    rw [rotate_cons_succ, rotate_rotate, Nat.add_right_comm, ← rotate_cons_succ]

lemma IsClosed.rotate (hw : w.IsClosed) (n : ℕ) : (w.rotate n).IsClosed := by
  suffices aux : ∀ {w : Walk α β} (h : w.IsClosed), (w.rotate 1).IsClosed by
    induction n with | zero => simpa | succ n IH => simpa using aux IH
  rintro (x | ⟨u, e, w⟩) hw
  · simpa
  simp [IsClosed]

@[simp]
lemma rotate_edge (w : Walk α β) (n : ℕ) : (w.rotate n).edge = w.edge.rotate n := by
  suffices aux : ∀ (w : Walk α β), (w.rotate 1).edge = w.edge.rotate 1 by induction n with
    | zero => simp | succ n IH => rw [← rotate_rotate, aux, ← List.rotate_rotate, IH]
  rintro (w | ⟨x, e, w⟩) <;> simp

@[mk_iff]
structure IsCycleIn (G : Graph α β) (W : Walk α β) : Prop where
  validIn : W.ValidIn G
  nodup' : W.vx.dropLast.Nodup
  closed : W.first = W.last

lemma IsPath.not_isCycle (hP : G.IsPath w) (hnonempty : w.Nonempty) : ¬ w.IsCycleIn G := by
  suffices heq : w.first ≠ w.last by
    rintro ⟨hVd, hnodup, hclosed⟩
    exact heq hclosed
  rwa [first_ne_last_iff hP.nodup]

lemma ValidIn.isCycleIn (hVd : w.ValidIn G) (hvx : w.vx.dropLast.Nodup)
    (hclosed : w.first = w.last) : w.IsCycleIn G := ⟨hVd, hvx, hclosed⟩

lemma IsCycle.exist_paths_of_mem_of_mem {C : Walk α β} (hC : C.IsCycleIn G)
    (hx : x ∈ C.vx) (hy : y ∈ C.vx) (hne : x ≠ y) :
    ∃ P Q, G.IsPath P ∧ G.IsPath Q ∧ P.first = x ∧ Q.first = x ∧ P.first = y ∧ Q.first = y ∧
    P.toGraph ∪ Q.toGraph = C.toGraph := sorry
