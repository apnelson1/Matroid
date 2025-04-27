import Matroid.ForMathlib.Graph.Walk.Path
-- import Matroid.ForMathlib.Graph.Connected
import Matroid.ForMathlib.Graph.WList.Cycle

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ C C₁ C₂ : WList α β} {S T : Set α}

open WList

namespace Graph


lemma IsWalk.rotate (hw : G.IsWalk w) (hc : w.IsClosed) (n) : G.IsWalk (w.rotate n) := by
  have aux {w'} (hw' : G.IsWalk w') (hc' : w'.IsClosed) : G.IsWalk (w'.rotate 1) := by
    induction hw' with
    | nil => simpa
    | @cons x e w hw h ih =>
      simp only [rotate_cons_succ, rotate_zero]
      obtain rfl : x = w.last := by simpa using hc'
      exact hw.concat h
  induction n with
  | zero => simpa
  | succ n IH => simpa [← rotate_rotate] using aux IH (hc.rotate n)

lemma IsWalk.intRotate (hw : G.IsWalk w) (hc : w.IsClosed) (n) : G.IsWalk (w.intRotate n) :=
  hw.rotate hc _

@[simp]
lemma IsClosed.isWalk_rotate_iff (hc : w.IsClosed) {n} : G.IsWalk (w.rotate n) ↔ G.IsWalk w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.rotate hc _⟩
  have h' := h.intRotate (hc.rotate _) (-n)
  rwa [← hc.intRotate_eq_rotate, hc.intRotate_intRotate, add_neg_cancel, intRotate_zero] at h'

/-- `G.IsCycle C` means that `C` is a nonempty closed walk with no repeated vertices or edges. -/
@[mk_iff]
structure IsCycle (G : Graph α β) (C : WList α β) : Prop extends G.IsTrail C where
  nonempty : C.Nonempty
  /-- The start and end vertex are the same -/
  isClosed : C.IsClosed
  /-- There are no repeated vertices except for the first and last. -/
  nodup : C.tail.vx.Nodup

lemma IsCycle.rotate (hC : G.IsCycle C) (n : ℕ) : G.IsCycle (C.rotate n) where
  nonempty := by simpa using hC.nonempty
  isWalk := hC.isWalk.rotate hC.isClosed n
  edge_nodup := by simpa using hC.edge_nodup
  isClosed := hC.isClosed.rotate n
  nodup := by simpa [rotate_vx_tail, List.nodup_rotate] using hC.nodup

@[simp]
lemma not_isCycle_nil (x : α) : ¬ G.IsCycle (nil x : WList α β) :=
  fun h ↦ by simpa using h.nonempty

lemma IsCycle.intRotate (hC : G.IsCycle C) (n : ℤ) : G.IsCycle (C.intRotate n) :=
  hC.rotate ..

lemma IsCycle.tail_isPath (hC : G.IsCycle C) : G.IsPath C.tail where
  isWalk := hC.isWalk.suffix <| tail_isSuffix C
  nodup := hC.nodup

lemma IsCycle.dropLast_isPath (hC : G.IsCycle C) : G.IsPath C.dropLast := by
  have h := (hC.intRotate (-1)).isClosed.rotate_one_dropLast
  rw [← IsClosed.intRotate_eq_rotate, hC.isClosed.intRotate_intRotate] at h
  · simp only [Int.reduceNeg, Int.cast_ofNat_Int, neg_add_cancel, intRotate_zero] at h
    rw [h]
    exact (hC.intRotate (-1)).tail_isPath
  exact (hC.intRotate _).isClosed

lemma IsCycle.reverse (hC : G.IsCycle C) : G.IsCycle C.reverse where
  isWalk := hC.isWalk.reverse
  edge_nodup := by simpa using hC.edge_nodup
  nonempty := by simp [hC.nonempty]
  isClosed := by simp [hC.isClosed]
  nodup := by simp [hC.dropLast_isPath.nodup]

lemma IsCycle.mem_tail_dropLast_of_ne_first (hC : G.IsCycle C) (hxC : x ∈ C) (hx : x ≠ C.first) :
    x ∈ C.tail.dropLast := by
  rwa [mem_iff_eq_first_or_mem_tail, or_iff_right hx, mem_iff_eq_mem_dropLast_or_eq_last,
    tail_last, ← hC.isClosed, or_iff_left hx] at hxC


  -- rw [IsClosed.rotate_one_dropLast]
  -- cases C with
  -- | nil u => simp at hC
  -- | cons u e C =>
  --   cases C with
  --   | nil v => simpa using hC.isWalk.vx_mem_of_mem (by simp)
  --   | cons v f w =>

  --     rw [dropLast_cons_cons, isPath_iff]
  --     refine hC.tail_isPath.prefix ?_
  --     simp

    -- sorry
    -- have hnd : C.vx.Nodup := by simpa using hC.tail_isPath.nodup
    -- refine ⟨hC.isWalk.dropLast, ?_⟩
    -- rw [← List.nodup_reverse, ← reverse_vx, ← reverse_tail, reverse_cons, tail_concat,
    --   concat_vx, List.nodup_append]
    -- simp
    -- simp only [cons_nonempty, dropLast_vx, cons_vx]

    -- cases C with
    -- | nil => simp
    -- | cons v f C =>
    --   simp
    -- rw [← List.nodup_reverse]
    -- cases C with
    -- | nil u => sorry
    -- | cons u e w => sorry
    -- simp only [tail_cons] at this


-- lemma IsCycle.rotate (hC : G.IsCycle C) (n : ℕ) : G.IsCycle (C.rotate n) where
--   isClosed := hC.isClosed.rotate n
--   isTrail := {
--     isWalk := hC.isTrail.isWalk.rotate
--     edge_nodup := _
--   }
--   nodup := _





end Graph
