import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Matroid.ForMathlib.ENat

variable {α : Type*} {X Y : Set α} {e f : α}

set_option linter.style.longLine false

open Set Insert Set.Notation

@[mk_iff]
structure FinDiff (X Y : Set α) : Prop where
  diff_left_finite : (X \ Y).Finite
  encard_diff_eq : (X \ Y).encard = (Y \ X).encard

lemma FinDiff.diff_right_finite (h : FinDiff X Y) : (Y \ X).Finite := by
  rw [← encard_lt_top_iff, ← h.encard_diff_eq, encard_lt_top_iff]
  exact h.diff_left_finite

lemma FinDiff.symm (h : FinDiff X Y) : FinDiff Y X where
  diff_left_finite := h.diff_right_finite
  encard_diff_eq := h.encard_diff_eq.symm

lemma finDiff_comm : FinDiff X Y ↔ FinDiff Y X :=
  ⟨FinDiff.symm, FinDiff.symm⟩

lemma finDiff_refl (X : Set α) : FinDiff X X := by
  simp [finDiff_iff]

lemma FinDiff.eq_of_subset (h : FinDiff X Y) (hXY : X ⊆ Y) : X = Y := by
  have h' := h.encard_diff_eq
  rw [diff_eq_empty.2 hXY, encard_empty, eq_comm, encard_eq_zero, diff_eq_empty] at h'
  exact hXY.antisymm h'

lemma FinDiff.nonempty_of_nonempty (h : FinDiff X Y) (hXY : (Y \ X).Nonempty) :
    (X \ Y).Nonempty := by
  rwa [← encard_pos, h.encard_diff_eq, encard_pos]

lemma finDiff_exchange {e f : α} (he : e ∈ X) (hf : f ∉ X) : FinDiff X (insert f (X \ {e})) := by
  rw [finDiff_iff, show X \ insert f (X \ {e}) = {e} by aesop,
    show insert f (X \ {e}) \ X = {f} by aesop]
  simp

lemma finDiff_insert_insert {e f : α} (he : e ∉ X) (hf : f ∉ X) :
    FinDiff (insert e X) (insert f X) := by
  rw [finDiff_iff, show insert e X \ insert f X = {e} \ {f} by aesop,
    show insert f X \ insert e X = {f} \ {e} by aesop]
  obtain rfl | hne := eq_or_ne e f
  · simp
  rw [sdiff_eq_left.2 (by simpa), sdiff_eq_left.2 (by simpa using hne.symm)]
  simp

lemma FinDiff.insert {e f : α} (hXY : FinDiff X Y) (heX : e ∉ X) (heY : e ∉ Y)
    (hfX : f ∉ X) (hfY : f ∉ Y) : FinDiff (insert e X) (insert f Y) := by
  obtain rfl | hne := eq_or_ne e f
  . rw [finDiff_iff, insert_diff_of_mem _ (by simp),
      and_iff_right (hXY.diff_left_finite.subset (by grind)), diff_insert_of_notMem heX,
      insert_diff_of_mem _ (by simp), diff_insert_of_notMem heY, hXY.encard_diff_eq]
  rwa [finDiff_iff, insert_diff_of_notMem _ (by grind), insert_diff_of_notMem _ (by grind),
    diff_insert_of_notMem hfX, diff_insert_of_notMem heY, encard_insert_of_notMem (by grind),
      encard_insert_of_notMem (by grind), ENat.add_one_eq_add_one_iff, finite_insert,
      ← finDiff_iff]

lemma finDiff_singleton_singleton (e f : α) : FinDiff {e} {f} := by
  convert finDiff_insert_insert (X := ∅) (e := e) (f := f) (by simp) (by simp) <;> simp

@[elab_as_elim]
protected lemma FinDiff.induction {motive : (X : Set α) → (Y : Set α) → FinDiff X Y → Prop}
    -- the base case; the required proposition holds for a set and itself
    (h0 : ∀ X, motive X X (finDiff_refl X))
    -- induction; if the proposition holds for `X, Y`, it should hold for `X + e, Y + f`
    -- for distinct new elements `e, f`.
    (h_int : ∀ (X Y : Set α) (hXY : FinDiff X Y) (a b : α) (haX : a ∉ X) (haY : a ∉ Y)
      (hbX : b ∉ X) (hbY : b ∉ Y) (_hab : a ≠ b) (_ih : motive X Y hXY),
      motive (Insert.insert a X) (Insert.insert b Y) (hXY.insert haX haY hbX hbY))
      {X Y : Set α} (hXY : FinDiff X Y) : motive X Y hXY := by
  obtain hXYe | ⟨e, hXYe⟩ := (X \ Y).eq_empty_or_nonempty
  · simp_rw [← hXY.eq_of_subset <| diff_eq_empty.1 hXYe]
    apply h0
  obtain ⟨f, hf⟩ := hXY.symm.nonempty_of_nonempty ⟨e, hXYe⟩
  have hcard : ((X \ {e}) \ (Y \ {f})).encard + 1 = (X \ Y).encard := by
    rw [diff_diff_right, inter_singleton_eq_empty.2 (by grind), union_empty, diff_diff_comm,
      ← encard_diff_singleton_add_one hXYe]
  have hcard' : ((Y \ {f}) \ (X \ {e})).encard + 1 = (Y \ X).encard := by
    rw [diff_diff_right, inter_singleton_eq_empty.2 (by grind), union_empty, diff_diff_comm,
      ← encard_diff_singleton_add_one hf]
  have hlt : ((X \ {e}) \ (Y \ {f})).encard < (X \ Y).encard := by
    rw [← ENat.add_one_lt_add_one_iff, hcard, ENat.lt_add_one_iff]
    exact encard_ne_top_iff.2 hXY.diff_left_finite
  have hfd : FinDiff (X \ {e}) (Y \ {f}) := by
    refine ⟨hXY.diff_left_finite.subset (by grind), ?_⟩
    rw [← ENat.add_one_eq_add_one_iff, hcard, hcard', hXY.encard_diff_eq]
  have m := FinDiff.induction (motive := motive) h0 h_int hfd
  specialize h_int _ _ hfd e f (by simp) (by grind) (by grind) (by simp) (by grind) m
  simp_rw [insert_diff_self_of_mem hXYe.1, insert_diff_self_of_mem hf.1] at h_int
  assumption
termination_by (X \ Y).encard


  -- induction hd : (X \ Y).encard generalizing X Y with
  -- | zero =>
  --   have hXY0 : (X \ Y).encard = 0 := by simpa using hd
  --   have hYX0 := hXY.encard_diff_eq ▸ hXY0
  --   simp only [encard_eq_zero, diff_eq_empty] at hXY0 hYX0
  --   obtain rfl : X = Y := hXY0.antisymm hYX0
  --   apply h0 X
  -- | succ n ih =>
  --   have hYX : hXY.diff_right_finite.toFinset.card = n + 1:=

-- lemma FinDiff.exists (h : FinDiff X Y) : ∃ (Z P Q : Set α), P.Finite ∧ Q.Finite ∧
--     Disjoint Z P ∧ Disjoint Z Q ∧ Disjoint P Q ∧ P.encard = Q.encard ∧ X = Z ∪ P ∧ Y = Z ∪ Q := by
--   sorry

-- lemma FinDiff.finDiff_union_union_iff' {P Q : Set α} (hPQ : FinDiff P Q) (hPX : Disjoint P X)
--     (hQY : Disjoint Q Y)  : FinDiff X Y ↔ FinDiff (X ∪ P) (Y ∪ Q) := by
--   obtain ⟨R, P, Q, hP, hQ, hRP, hRQ, hPQ, hPQcard, rfl, rfl⟩ := hPQ.exists




lemma FinDiff.finDiff_union_union_iff {P Q : Set α} (hPQ : FinDiff P Q) (hPX : Disjoint P X)
    (hQY : Disjoint Q Y) : FinDiff X Y ↔ FinDiff (X ∪ P) (Y ∪ Q) := by

  have hrw' : ∀ {A B C D : Set α}, Disjoint A C → Disjoint B D → (A \ B) ∩ D = (D \ C) ∩ A := by
    intro A B C D h1 h2
    rw [subset_antisymm_iff, subset_inter_iff, and_iff_left (inter_subset_left.trans diff_subset),
      subset_diff, and_iff_right inter_subset_right, subset_inter_iff,
      and_iff_left (inter_subset_left.trans diff_subset), subset_diff,
      and_iff_right inter_subset_right]
    exact ⟨h1.mono_left (inter_subset_left.trans diff_subset),
      h2.symm.mono_left (inter_subset_left.trans diff_subset)⟩

  have hrw1 : X \ Y ∩ Q = (Q \ P) ∩ X := hrw' hPX.symm hQY.symm
  have hrw2 : Y \ X ∩ P = (P \ Q) ∩ Y := hrw' hQY.symm hPX.symm

  have hfin1 := hPQ.diff_left_finite.inter_of_left Y
  have hfin2 := hPQ.diff_right_finite.inter_of_left X
  have hfin3 : ((Q \ P) \ X).Finite := hPQ.diff_right_finite.diff
  have hfin4 : ((P \ Q) \ Y).Finite := hPQ.diff_left_finite.diff

  rw [finDiff_iff, ← diff_union_inter (X \ Y) Q, finDiff_iff, union_diff_distrib, ← diff_diff,
    union_comm Y, ← diff_diff, union_diff_distrib, ← diff_diff (s := Y), union_comm X,
← diff_diff,
    finite_union, finite_union, encard_union_eq disjoint_sdiff_inter, hrw1,
    and_iff_left hfin2, and_iff_left hfin4, and_congr_right_iff,
    encard_union_eq, encard_union_eq, ← diff_union_inter (Y \ X) P,
    encard_union_eq disjoint_sdiff_inter, diff_union_inter, add_comm (a := ((Q \ P) \ X).encard),
    hrw2]
  rotate_left
  · exact hQY.mono (diff_subset.trans diff_subset) (diff_subset.trans diff_subset)
  · exact hPX.symm.mono (diff_subset.trans diff_subset) (diff_subset.trans diff_subset)

  obtain hinf | hfin5 := ((Y \ X) \ P).finite_or_infinite.symm
  · simp only [hinf.encard_eq, top_add]
    simp
    -- rw [ENat.add_eq, WithTop.add_eq_top, encard_eq_top_iff, encard_eq_top_iff,
    --   encard_eq_top_iff]
    simp [hfin2, hfin4]
  intro hfin6

  have h' := hPQ.encard_diff_eq
  rw [← encard_diff_add_encard_inter (P \ Q) Y, ← encard_diff_add_encard_inter (Q \ P) X] at h'

  rw [hfin1.encard_eq_coe, hfin2.encard_eq_coe, hfin3.encard_eq_coe, hfin4.encard_eq_coe] at h' ⊢
  rw [hfin5.encard_eq_coe, hfin6.encard_eq_coe]
  simp_rw [← Nat.cast_add, ENat.coe_inj] at h' ⊢
  exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

lemma finDiff_insert_insert_iff (heX : e ∉ X) (hfY : f ∉ Y) :
    FinDiff X Y ↔ FinDiff (insert e X) (insert f Y) := by
  rw [← union_singleton, ← union_singleton,
    ← (finDiff_singleton_singleton e f).finDiff_union_union_iff (by simpa) (by simpa)]

lemma FinDiff.union_union {P Q : Set α} (hXY : FinDiff X Y) (hPQ : FinDiff P Q)
    (hPX : Disjoint P X) (hQY : Disjoint Q Y) : FinDiff (X ∪ P) (Y ∪ Q) := by
  rwa [← hPQ.finDiff_union_union_iff hPX hQY]

lemma FinDiff.insert_insert (hXY : FinDiff X Y) (heX : e ∉ X) (hfY : f ∉ Y) :
    FinDiff (Insert.insert e X) (Insert.insert f Y) := by
  rwa [← finDiff_insert_insert_iff heX hfY]

lemma FinDiff.exchange_right (hXY : FinDiff X Y) {e f : α} (heY : e ∈ Y) (hfY : f ∉ Y) :
    FinDiff X (Insert.insert f (Y \ {e})) := by
  by_cases heX : e ∈ X
  · have hrw := finDiff_insert_insert_iff (X := X \ {e}) (Y := Y \ {e}) (e := e) (f := e)
      (by simp) (by simp)
    simp only [insert_diff_singleton, insert_eq_of_mem heX, insert_eq_of_mem heY] at hrw
    rw [← hrw] at hXY
    convert hXY.insert_insert (e := e) (f := f) (by simp) (by simp [hfY])
    simp [heX]
  have hef : e ≠ f := by rintro rfl; contradiction
  rwa [finDiff_insert_insert_iff heX (f := e) (by simp [hef]), insert_comm, insert_diff_singleton,
    insert_eq_of_mem heY, ← finDiff_insert_insert_iff heX hfY]

lemma FinDiff.trans {X Y Z : Set α} (hXY : FinDiff X Y) (hYZ : FinDiff Y Z) : FinDiff X Z := by
  obtain h | h := eq_empty_or_nonempty (Z \ Y)
  · rw [diff_eq_empty] at h
    rwa [hYZ.symm.eq_of_subset h]
  obtain ⟨f, hfY, hfZ⟩ := hYZ.nonempty_of_nonempty h
  obtain ⟨e, heZ, heY⟩ := h
  have decr : (Insert.insert f (Z \ {e}) \ Y).encard < (Z \ Y).encard := by
    rw [insert_diff_of_mem _ hfY, diff_diff_comm,
      ← encard_diff_singleton_add_one (show e ∈ Z \ Y by simp [heZ, heY]), ENat.lt_add_one_iff]
    simp [hYZ.diff_right_finite.diff]
  have IH : FinDiff Y (Insert.insert f (Z \ {e})) := hYZ.exchange_right heZ hfZ
  have hd := FinDiff.trans hXY IH
  have hne : e ≠ f := by rintro rfl; contradiction
  convert hd.exchange_right (e := f) (f := e) (by simp) (by simp [heZ, hne])
  simp only [mem_singleton_iff, insert_diff_of_mem]
  rw [← insert_diff_of_notMem _ (by simpa), insert_diff_singleton, insert_eq_of_mem heZ,
    diff_singleton_eq_self hfZ]
termination_by (Z \ Y).encard

lemma finDiff_iff_exchange (heY : e ∈ Y) (hfY : f ∉ Y) :
    FinDiff X Y ↔ FinDiff X (insert f (Y \ {e})) := by
  refine ⟨fun h ↦ h.exchange_right heY hfY, fun h ↦ ?_⟩
  convert h.exchange_right (e := f) (f := e) (by simp) (by aesop)
  simp [mem_singleton_iff, insert_diff_of_mem,
    insert_diff_singleton_comm (show e ≠ f by rintro rfl; contradiction),
    insert_eq_of_mem heY, diff_singleton_eq_self hfY]
