import Matroid.ForMathlib.Graph.WList.Sublist
import Mathlib.Algebra.Order.Group.Nat
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

lemma IsClosed.vxSet_tail (h : w.IsClosed) : w.tail.V = w.V := by
  induction w with simp_all

lemma IsClosed.reverse (h : w.IsClosed) : w.reverse.IsClosed := by
  simp_all [IsClosed]

@[simp]
lemma reverse_isClosed_iff : w.reverse.IsClosed ↔ w.IsClosed := by
  simp [IsClosed, eq_comm]

lemma IsClosed.tail_dropLast (hw : w.IsClosed) : w.tail.dropLast = w.dropLast.tail := by
  refine (eq_or_ne w.length 1).elim (fun h1 ↦ ?_) WList.tail_dropLast
  cases w with
  | nil => simp
  | cons u e w => cases w with | nil => simpa [eq_comm, IsClosed] using hw | cons => simp at h1

lemma IsClosed.length_eq_one_iff (hw : w.IsClosed) :
    w.length = 1 ↔ ∃ x e, w = cons x e (nil x) := by
  cases w with
  | nil => simp
  | cons u e w => cases w with simp_all

/-! ### Rotations -/

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

lemma rotate_succ (w : WList α β) (n : ℕ) : w.rotate (n+1) = (w.rotate 1).rotate n := by
  rw [rotate_rotate, Nat.add_comm]

@[simp]
lemma length_rotate (w : WList α β) (n : ℕ) : (w.rotate n).length = w.length := by
  induction n generalizing w with
  | zero => simp
  | succ n IH =>
    rw [rotate_succ, IH]
    cases w with simp

@[simp] lemma rotate_nonempty_iff : (w.rotate n).Nonempty ↔ w.Nonempty := by
  induction n generalizing w with
  | zero => simp
  | succ n IH =>
    rw [rotate_succ, IH]
    cases w with simp

lemma rotate_first (w : WList α β) (n : ℕ) (hn : n ≤ w.length) : (w.rotate n).first = w.get n := by
  induction n generalizing w with
  | zero => simp
  | succ n IH => cases w with
    | nil => simp
    | cons u e w =>
      simp only [cons_length, Nat.add_le_add_iff_right] at hn
      rwa [rotate_cons_succ, get_cons_add, IH _ (hn.trans (by simp)), get_concat]

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

lemma IsClosed.rotate_vxSet (hw : w.IsClosed) (n) : (w.rotate n).V = w.V := by
  simp_rw [← (hw.rotate _).vxSet_tail, WList.V, ← mem_vx, rotate_vx_tail, List.mem_rotate, mem_vx]
  rw [← WList.V, hw.vxSet_tail, WList.V]

lemma IsClosed.mem_rotate (hw : w.IsClosed) {n} : x ∈ w.rotate n ↔ x ∈ w := by
  rw [← mem_vxSet_iff, hw.rotate_vxSet, mem_vxSet_iff]

@[simp]
lemma rotate_edgeSet (w : WList α β) (n) : (w.rotate n).E = w.E := by
  simp [WList.E, rotate_edge]

lemma IsClosed.rotate_length (hw : w.IsClosed) : w.rotate w.length = w := by
  refine ext_vx_edge ?_ (by rw [rotate_edge, ← length_edge, List.rotate_length])
  cases w with
  | nil => simp
  | cons u e w =>
    rw [cons_length, rotate_cons_succ, cons_vx,
      ← ((w.concat e w.first).rotate w.length).vx.head_cons_tail (by simp),
      ← tail_vx (by simp), rotate_vx_tail, vx_head, rotate_first _ _ (by simp),
      get_concat _ _ _ rfl.le, get_length, eq_comm, show u = w.last from hw]
    convert rfl
    cases w with
    | nil => simp
    | cons y f w =>
      rw [first_cons, cons_concat, tail_cons, concat_vx, cons_length, cons_vx,
        ← w.length_vx, List.rotate_append_length_eq]
      simp

lemma IsClosed.rotate_eq_mod (hw : w.IsClosed) (n) : w.rotate n = w.rotate (n % w.length) := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp
  obtain hlt | hle := lt_or_le n w.length
  · rw [Nat.mod_eq_of_lt hlt]
  obtain ⟨c, hc⟩ := exists_add_of_le hle
  have hc' : c < n := by
    have := hne.length_pos
    omega
  rw [hc, Nat.add_mod_left, ← rotate_rotate, hw.rotate_length, hw.rotate_eq_mod]

lemma exists_rotate_first_eq (hx : x ∈ w) : ∃ n ≤ w.length, (w.rotate n).first = x := by
  classical
  exact ⟨w.idxOf x, by simpa, by rw [rotate_first _ _ (by simpa), get_idxOf _ hx]⟩

lemma IsClosed.rotate_one_dropLast (hw : w.IsClosed) : (w.rotate 1).dropLast = w.tail := by
  cases w with simp

/-- Rotate by an integer amount. -/
def intRotate (w : WList α β) (n : ℤ) : WList α β :=
  w.rotate (n.natMod w.length)

@[simp]
lemma length_intRotate (w : WList α β) (m : ℤ) : (w.intRotate m).length = w.length :=
  length_rotate ..

@[simp]
lemma intRotate_zero : w.intRotate 0 = w := by
  cases w with simp [intRotate, Int.natMod]

@[simp]
lemma nil_intRotate (x : α) (n) : (nil x : WList α β).intRotate n = nil x := by
  simp [intRotate]

lemma IsClosed.intRotate_eq_rotate (hw : w.IsClosed) (n : ℕ) : w.intRotate n = w.rotate n := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp [intRotate]
  rw [intRotate, hw.rotate_eq_mod, Int.natMod, eq_comm, hw.rotate_eq_mod, Int.ofNat_mod_ofNat,
    Int.toNat_natCast, Nat.mod_mod]

/-- Nasty proof. -/
lemma IsClosed.intRotate_intRotate (hw : w.IsClosed) (m n : ℤ) :
    (w.intRotate m).intRotate n = w.intRotate (m + n) := by
  obtain ⟨x, rfl⟩ | hne := w.exists_eq_nil_or_nonempty
  · simp [intRotate]
  simp only [intRotate, length_rotate, rotate_rotate, Int.natMod]
  rw [hw.rotate_eq_mod, Int.add_emod]
  generalize hm' : m % w.length = m'
  generalize hn' : n % w.length = n'
  lift m' to ℕ using by simpa [← hm'] using Int.emod_nonneg _ (by simpa)
  lift n' to ℕ using by simpa [← hn'] using Int.emod_nonneg _ (by simpa)
  norm_cast




end WList
