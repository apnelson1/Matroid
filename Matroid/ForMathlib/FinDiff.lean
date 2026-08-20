module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Linarith
public import Matroid.ForMathlib.ENat
public import Matroid.ForMathlib.Set
public import Matroid.ForMathlib.Tactic.ENatToNat

@[expose] public section

variable {α : Type*} {X Y Z P Q : Set α} {e f : α}

set_option linter.style.longLine false

open Set Insert Set.Notation

namespace Set

/-- `X.IsExchange Y` means that `Y` is obtained from `X` by adding an element of `Y \ X`
and then removing an element of `X \ Y`. -/
inductive IsExchange : Set α → Set α → Prop
  | insert_insert' X e f (heX : e ∉ X) (hfX : f ∉ X) (hef : e ≠ f) :
    IsExchange (insert e X) (insert f X)

lemma isExchange_insert_insert (heX : e ∉ X) (hfX : f ∉ X) (hef : e ≠ f) :
    (insert e X).IsExchange (insert f X) :=
  IsExchange.insert_insert' X e f heX hfX hef

lemma IsExchange.symm (hXY : X.IsExchange Y) : Y.IsExchange X := by
  cases hXY with | insert_insert' X e f heX hfX hef => exact insert_insert' X f e hfX heX hef.symm

lemma isExchange_comm : X.IsExchange Y ↔ Y.IsExchange X :=
  ⟨IsExchange.symm, IsExchange.symm⟩

lemma IsExchange.ne (hXY : X.IsExchange Y) : X ≠ Y := by
  cases hXY with | insert_insert' X e f heX hfX hef => apply_fun (e ∈ ·); simp [hef, heX]

lemma IsExchange.exists (hXY : X.IsExchange Y) :
    ∃ e ∈ X \ Y, ∃ f ∈ Y \ X, Y = insert f (X \ {e}) := by
  cases hXY with | insert_insert' X e f heX hfX hef => exact
    ⟨e, by simp [heX, hef], f, by simp [hfX, hef.symm], by rw [insert_sdiff_self_of_notMem heX]⟩

lemma IsExchange.exists_sdiff_singleton_of_mem (h : X.IsExchange Y) (heX : e ∈ X) (heY : e ∉ Y) :
    ∃ f ∈ Y, f ∉ X ∧ X = insert e (Y \ {f}) := by
  obtain ⟨e', he', f, hf, rfl⟩ := h.exists
  exact ⟨f, by simp, hf.2, by grind⟩

lemma IsExchange.exists_insert_of_notMem (h : X.IsExchange Y) (heX : e ∉ X) (heY : e ∈ Y) :
    ∃ f ∈ X, f ∉ Y ∧ X = insert f (Y \ {e}) := by
  obtain ⟨e', he', f, hf, rfl⟩ := h.exists
  exact ⟨e', he'.1, he'.2, by grind⟩

lemma isExchange_sdiff_insert (heX : e ∈ X) (hfX : f ∉ X) : IsExchange X (insert f (X \ {e})) := by
  convert IsExchange.insert_insert' (X \ {e}) e f (by simp) (by simp [hfX]) (by grind)
  rw [insert_sdiff_self_of_mem heX]

lemma isExchange_insert_sdiff (heX : e ∈ X) (hfX : f ∉ X) : IsExchange X ((insert f X) \ {e}):= by
  rw [← insert_sdiff_singleton_comm (by grind)]
  exact isExchange_sdiff_insert heX hfX

lemma isExchange_diff_singleton_diff_singleton (heX : e ∈ X) (hfX : f ∈ X) (hef : e ≠ f) :
    (X \ {e}).IsExchange (X \ {f}) := by
  convert isExchange_insert_insert (X := X \ {e, f}) (by simp) (by simp) hef.symm using 1 <;> grind

lemma IsExchange.diff_eq_singleton (h : X.IsExchange Y) : ∃ e, X \ Y = {e} := by
  cases h with | insert_insert' X e => exact ⟨e, by grind⟩

lemma IsExchange.union_union {P} (hXY : X.IsExchange Y) (hPX : Disjoint P X) (hPY : Disjoint P Y) :
    (X ∪ P).IsExchange (Y ∪ P) := by
  cases hXY with
  | insert_insert' Z e f heZ hfZ hef =>
    rw [insert_union, insert_union]
    exact isExchange_insert_insert (by grind) (by grind) (by grind)

lemma IsExchange.insert_insert (hXY : X.IsExchange Y) (heX : e ∉ X) (heY : e ∉ Y) :
    (insert e X).IsExchange (insert e Y) := by
  simpa using hXY.union_union (P := {e}) (by simpa) (by simpa)

lemma IsExchange.sdiff_sdiff {P} (hXY : X.IsExchange Y) (hPX : P ⊆ X) (hPY : P ⊆ Y) :
    (X \ P).IsExchange (Y \ P) := by
  cases hXY with
  | insert_insert' Z e f heZ hfZ hef =>
    rw [insert_sdiff_of_notMem _ (by grind), insert_sdiff_of_notMem _ (by grind)]
    exact isExchange_insert_insert (by grind) (by grind) (by grind)

lemma IsExchange.nonempty_left (h : IsExchange X Y) : X.Nonempty := by
  cases h with simp

lemma IsExchange.nonempty_right (h : IsExchange X Y) : Y.Nonempty := by
  cases h with simp

@[simp]
lemma not_empty_isExchange (X : Set α) : ¬ IsExchange ∅ X :=
  fun h ↦ by simpa using h.nonempty_left

@[simp]
lemma not_isExchange_empty (X : Set α) : ¬ IsExchange X ∅ :=
  fun h ↦ by simpa using h.nonempty_right

lemma IsExchange.sdiff_right {S : Set α} (h : X.IsExchange Y) (hXS : X ⊆ S) (hYS : Y ⊆ S) :
    (S \ X).IsExchange (S \ Y) := by
  cases h with
  | insert_insert' A e f heA hfA hef =>
    convert (isExchange_insert_insert (X := (S \ A) \ {e,f}) (by simp) (by simp) hef).symm using 1
    <;> grind

lemma isExchange_sdiff_right_iff {S : Set α} (hXS : X ⊆ S) (hYS : Y ⊆ S) :
    (S \ X).IsExchange (S \ Y) ↔ X.IsExchange Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.sdiff_right hXS hYS⟩
  rw [← sdiff_sdiff_cancel_left hXS, ← sdiff_sdiff_cancel_left hYS]
  exact h.sdiff_right sdiff_subset sdiff_subset

lemma isExchange_sdiff_right_comm {S} (hXS : X ⊆ S) (hYS : Y ⊆ S) :
    X.IsExchange (S \ Y) ↔ (S \ X).IsExchange Y := by
  rw [← isExchange_sdiff_right_iff hXS sdiff_subset, sdiff_sdiff_cancel_left hYS]

lemma isExchange_insert_insert_iff (heX : e ∉ X) (heY : e ∉ Y) :
    IsExchange (insert e X) (insert e Y) ↔ IsExchange X Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hwin := h.sdiff_sdiff (P := {e}) (by simp) (by simp)
    rwa [insert_sdiff_self_of_notMem heX, insert_sdiff_self_of_notMem heY] at hwin
  exact h.insert_insert heX heY

@[simp]
lemma singleton_isExchange_iff {a : α} : IsExchange {a} X ↔ ∃ b ≠ a, X = {b} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · generalize haY : ({a} : Set α) = Y at h
    cases h with
    | insert_insert' P e f heP hfP hef =>
      obtain rfl : e = a := haY.symm.subset <| .inl rfl
      exact ⟨f, hef.symm, by grind⟩
  rintro ⟨b, hba, rfl⟩
  rw [← insert_empty_eq a, ← insert_empty_eq b]
  exact isExchange_insert_insert (notMem_empty _) (notMem_empty _) hba.symm

@[simp]
lemma isExchange_singleton_iff {a : α} : IsExchange X {a} ↔ ∃ b ≠ a, X = {b} := by
  rw [isExchange_comm]
  simp

lemma isExchange_singleton_singleton {a b : α} : IsExchange {a} {b} ↔ a ≠ b := by
  simp [eq_comm]

@[simp]
lemma isExchange_pair_iff_right {a b c : α} : IsExchange {a, b} {a, c} ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain rfl | hab := eq_or_ne a b
  · simp [eq_comm]
  obtain rfl | hac := eq_or_ne a c
  · simp [eq_comm]
  rw [isExchange_insert_insert_iff (by simpa) (by simpa), isExchange_singleton_singleton]
  simp [hab, hac]

@[simp]
lemma isExchange_pair_iff_left {a b c : α} : IsExchange {a, c} {b, c} ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rw [pair_comm, pair_comm b, isExchange_pair_iff_right]
  tauto

lemma isExchange_image_iff_of_injOn {β : Type*} {f : α → β} {S : Set α} (hS : InjOn f S)
    (hX : X ⊆ S) (hY : Y ⊆ S) : IsExchange (f '' X) (f '' Y) ↔ IsExchange X Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, ⟨⟨x, hx, rfl⟩, hx'⟩, _, ⟨⟨y, hy, rfl⟩, hy'⟩, heq⟩ := h.exists
    rw [← image_singleton, ← image_sdiff_of_injOn (hS.mono hX) (by simpa), ← image_insert_eq,
      hS.image_eq_image_iff hY (by grind)] at heq
    rw [hS.mem_image_iff hX (hY hy)] at hy'
    rw [heq]
    refine isExchange_sdiff_insert hx hy'
  obtain ⟨x, ⟨hx, hx'⟩, y, ⟨hy, hy'⟩, rfl⟩ := h.exists
  rw [image_insert_eq, image_sdiff_of_injOn (hS.mono hX) (by simpa), image_singleton]
  refine isExchange_sdiff_insert ?_ ?_
  · rwa [hS.mem_image_iff hX (hX hx)]
  rwa [hS.mem_image_iff hX (by grind)]

/-- `X.FinDiff Y` means that `Y` is obtained from `X` by inserting and then removing `k` elements,
for some finite `k`. -/
def FinDiff : Set α → Set α → Prop := Relation.ReflTransGen IsExchange

lemma FinDiff.symm (h : FinDiff X Y) : FinDiff Y X := by
  rw [FinDiff]
  convert Relation.ReflTransGen.swap _ _ h using 4 with X Y
  exact isExchange_comm

lemma finDiff_comm : FinDiff X Y ↔ FinDiff Y X :=
  ⟨FinDiff.symm, FinDiff.symm⟩

@[simp]
lemma finDiff_refl (X : Set α) : FinDiff X X := Relation.ReflTransGen.refl

lemma FinDiff.encard_sdiff_comm (h : FinDiff X Y) : (X \ Y).encard = (Y \ X).encard := by
  have aux {x P} (hxP : x ∉ P) : (X \ insert x P).encard = (insert x P \ X).encard ↔
      (X \ P).encard = (P \ X).encard + 1 := by
    by_cases hxX : x ∈ X
    · rw [insert_sdiff_of_mem _ hxX, ← ENat.add_one_inj, ← union_singleton, ← sdiff_sdiff,
        encard_sdiff_singleton_add_one (by grind)]
    rw [insert_sdiff_of_notMem _ hxX, encard_insert_of_notMem (by grind), ← union_singleton,
      ← sdiff_sdiff, sdiff_singleton_eq_self (by grind)]
  induction h with
  | refl => simp
  | @tail Y Z c hab => cases hab with grind

lemma FinDiff.eq_of_subset (h : FinDiff X Y) (hXY : X ⊆ Y) : X = Y := by
  refine hXY.antisymm <| sdiff_eq_empty.1 ?_
  rw [← encard_eq_zero, ← h.encard_sdiff_comm, sdiff_eq_empty.2 hXY, encard_empty]

lemma FinDiff.sdiff_nonempty_of_ne (h : FinDiff X Y) (hne : X ≠ Y) : (X \ Y).Nonempty := by
  rw [sdiff_nonempty]
  contrapose hne
  exact h.eq_of_subset hne

lemma IsExchange.finDiff (h : X.IsExchange Y) : FinDiff X Y :=
  Relation.ReflTransGen.single h

lemma FinDiff.trans (hXY : X.FinDiff Y) (hYZ : Y.FinDiff Z) : X.FinDiff Z :=
  Relation.ReflTransGen.trans hXY hYZ

lemma FinDiff.trans_exchange (hXY : X.FinDiff Y) (hYZ : Y.IsExchange Z) : X.FinDiff Z :=
  Relation.ReflTransGen.trans hXY hYZ.finDiff

lemma IsExchange.trans_finDiff (hXY : X.IsExchange Y) (hYZ : Y.FinDiff Z) : X.FinDiff Z :=
  hXY.finDiff.trans hYZ

lemma FinDiff.sdiff_finite (h : FinDiff X Y) : (X \ Y).Finite := by
  induction h with
  | refl => simp
  | @tail P Q Z hfin ih =>
    cases hfin with | insert_insert' Q a b haZ hbZ hab => exact (ih.insert a).subset <| by grind

@[elab_as_elim]
lemma FinDiff.induction {motive : (X : Set α) → (Y : Set α) → (hXY : FinDiff X Y) → Prop}
    (refl : ∀ X, motive X X Relation.ReflTransGen.refl)
    (exchange : ∀ (X Y Z : Set α) (hXY : FinDiff X Y) (hYZ : Y.IsExchange Z) (_hu : Y ⊆ X ∪ Z)
      (_hi : X ∩ Z ⊆ Y) (_ih : motive X Y hXY), motive X Z (Relation.ReflTransGen.tail hXY hYZ))
      {X Y : Set α} (hXY : FinDiff X Y) : motive X Y hXY := by
  obtain rfl | hne := eq_or_ne X Y
  · apply refl
  obtain ⟨e, he⟩ := hXY.sdiff_nonempty_of_ne hne
  obtain ⟨f, hf⟩ := hXY.symm.sdiff_nonempty_of_ne hne.symm
  have hex := isExchange_sdiff_insert hf.1 he.2
  have h' : FinDiff X (insert e (Y \ {f})) := hXY.trans <| IsExchange.finDiff hex
  have hlt' : (X \ (insert e (Y \ {f}))).encard < (X \ Y).encard := by
    rw [← union_singleton, ← sdiff_sdiff, sdiff_sdiff_right, inter_singleton_eq_empty.2 hf.2,
      union_empty]
    exact hXY.sdiff_finite.sdiff.encard_lt_encard (by grind)
  exact exchange _ _ Y h' hex.symm (by grind) (by grind) <| FinDiff.induction refl exchange h'
termination_by (X \ Y).encard

@[elab_as_elim]
lemma FinDiff.induction_head {motive : (X : Set α) → (Y : Set α) → (hXY : FinDiff X Y) → Prop}
    (refl : ∀ X, motive X X Relation.ReflTransGen.refl)
    (exchange : ∀ (X Y Z : Set α) (hXY : X.IsExchange Y) (hYZ : Y.FinDiff Z)
      (_hu : Y ⊆ X ∪ Z) (_hi : X ∩ Z ⊆ Y) (_ih : motive Y Z hYZ),
      motive X Z (Relation.ReflTransGen.head hXY hYZ)) {X Y : Set α}
      (hXY : FinDiff X Y) : motive X Y hXY := by
  rw [finDiff_comm] at hXY
  induction hXY using FinDiff.induction with
  | refl X => exact refl X
  | exchange X Y Z hXY' hYZ _ _ ih =>
      exact exchange _ Y _ hYZ.symm hXY'.symm (by rwa [union_comm]) (by rwa [inter_comm]) <|
      ih hXY'.symm

lemma finDiff_insert_insert (heX : e ∉ X) (hfX : f ∉ X) : FinDiff (insert e X) (insert f X) := by
  obtain rfl | hne := eq_or_ne e f
  · exact finDiff_refl _
  exact (isExchange_insert_insert heX hfX hne).finDiff

lemma FinDiff.union_union_disjoint {P} (hXY : FinDiff X Y) (hPX : Disjoint P X)
    (hPY : Disjoint P Y) : FinDiff (X ∪ P) (Y ∪ P) := by
  induction hXY using FinDiff.induction with
  | refl X => simp
  | exchange X Y Z hXY hYZ hu hi ih =>
    exact (ih hPX (by grind)).trans_exchange <| hYZ.union_union (by grind) hPY

lemma FinDiff.sdiff_sdiff {P} (hXY : FinDiff X Y) (hPX : P ⊆ X) (hPY : P ⊆ Y) :
    FinDiff (X \ P) (Y \ P) := by
  induction hXY using FinDiff.induction with
  | refl X => simp
  | exchange X Y Z hXY hYZ hu hi ih =>
    exact (ih hPX (by grind)).trans_exchange <| hYZ.sdiff_sdiff (by grind) hPY

lemma finDiff_union_union_disjoint_iff {P} (hPX : Disjoint P X) (hPY : Disjoint P Y) :
    FinDiff (X ∪ P) (Y ∪ P) ↔ FinDiff X Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.union_union_disjoint hPX hPY⟩
  rw [← union_sdiff_cancel_left hPX.inter_eq.subset, union_comm P,
  ← union_sdiff_cancel_left hPY.inter_eq.subset, union_comm P]
  exact h.sdiff_sdiff (by simp) (by simp)

lemma finDiff_iff {X Y : Set α} :
    X.FinDiff Y ↔ (X \ Y).Finite ∧ (X \ Y).encard = (Y \ X).encard := by
  refine ⟨fun h ↦ ⟨h.sdiff_finite, h.encard_sdiff_comm⟩, fun ⟨hfin, hXY⟩ ↦ ?_⟩
  obtain he | hne := (X \ Y).eq_empty_or_nonempty
  · obtain rfl : X = Y := (sdiff_eq_empty.1 he).antisymm <| sdiff_eq_empty.1 <|
      by rwa [← encard_eq_zero, ← hXY, encard_eq_zero]
    simp
  obtain ⟨f, hf⟩ : (Y \ X).Nonempty := by rwa [← encard_pos, ← hXY, encard_pos]
  obtain ⟨e, he⟩ := hne
  have hlt : ((insert f (X \ {e})) \ Y).encard < (X \ Y).encard := by
    rw [insert_sdiff_of_mem _ hf.1, sdiff_sdiff_comm, ← encard_sdiff_singleton_add_one he]
    simpa using hfin.sdiff
  refine (isExchange_sdiff_insert he.1 hf.2).trans_finDiff ?_
  refine finDiff_iff.2 ⟨(hfin.insert f).subset (by grind), ?_⟩
  rw [insert_sdiff_of_mem _ hf.1, sdiff_sdiff_comm, ← ENat.add_one_inj,
    encard_sdiff_singleton_add_one he, ← union_singleton, ← sdiff_sdiff, sdiff_sdiff_right,
    inter_singleton_eq_empty.2 he.2, union_empty, encard_sdiff_singleton_add_one hf, hXY]
termination_by (X \ Y).encard

lemma FinDiff.encard_eq_encard (h : FinDiff X Y) : X.encard = Y.encard := by
  rw [← encard_sdiff_add_encard_inter X Y, ← encard_sdiff_add_encard_inter Y X, h.encard_sdiff_comm,
    inter_comm]

lemma FinDiff.sdiff_nonempty_of_nonempty (h : FinDiff X Y) (hXY : (Y \ X).Nonempty) :
    (X \ Y).Nonempty := by
  rwa [← encard_pos, h.encard_sdiff_comm, encard_pos]

lemma FinDiff.nonempty_of_nonempty (h : FinDiff X Y) (hX : X.Nonempty) : Y.Nonempty := by
  rwa [← encard_pos, ← h.encard_eq_encard, encard_pos]

@[simp]
lemma finDiff_singleton_singleton (e f : α) : FinDiff {e} {f} := by
  convert finDiff_insert_insert (X := ∅) (e := e) (f := f) (by simp) (by simp) <;> simp

lemma FinDiff.union_union_right {P : Set α} (hXY : FinDiff X Y) (hPX : Disjoint P X)
    (hPY : Disjoint P Y) : FinDiff (X ∪ P) (Y ∪ P) := by
  induction hXY using FinDiff.induction with
  | refl X => simp
  | exchange X Y Z hXY hYZ hu hi ih =>
    exact (ih hPX (by grind)).trans_exchange <| hYZ.union_union (by grind) hPY

lemma FinDiff.sdiff_sdiff_right {P : Set α} (hXY : FinDiff X Y) (hPX : P ⊆ X) (hPY : P ⊆ Y) :
    FinDiff (X \ P) (Y \ P) := by
  induction hXY using FinDiff.induction with
  | refl X => simp
  | exchange X Y Z hXY hYZ hu hi ih =>
    exact (ih hPX (by grind)).trans_exchange <| hYZ.sdiff_sdiff (by grind) hPY

lemma FinDiff.finDiff_union_union_iff {P Q : Set α} (hPQ : FinDiff P Q) (hPX : Disjoint P X)
    (hQY : Disjoint Q Y) : FinDiff (X ∪ P) (Y ∪ Q) ↔ FinDiff X Y := by
  have hle1 : (P ∩ Y).encard ≤ (P \ Q).encard := encard_le_encard (by grind)
  have hle2 : (Q ∩ X).encard ≤ (Q \ P).encard := encard_le_encard (by grind)
  have h1 : (X \ Y) ∪ (P \ Q) = ((X ∪ P) \ (Y ∪ Q)) ∪ (P ∩ Y) ∪ (Q ∩ X) := by grind
  have h2 : (Y \ X) ∪ (Q \ P) = ((Y ∪ Q) \ (X ∪ P)) ∪ (P ∩ Y) ∪ (Q ∩ X) := by grind
  apply_fun encard at h1 h2
  rw [encard_union_eq (by grind), encard_union_eq (by grind), encard_union_eq (by grind)] at h1 h2
  have hPQ1 := hPQ.encard_sdiff_comm
  have hPQfin := encard_lt_top_iff.2 hPQ.sdiff_finite
  simp_rw [finDiff_iff, ← encard_lt_top_iff]
  enat_to_nat!
  lia

lemma FinDiff.finDiff_sdiff_sdiff_iff {P Q : Set α} (hPQ : FinDiff P Q) (hPX : P ⊆ X)
    (hQY : Q ⊆ Y) : FinDiff (X \ P) (Y \ Q) ↔ FinDiff X Y := by
  rw [← hPQ.finDiff_union_union_iff disjoint_sdiff_right disjoint_sdiff_right,
    sdiff_union_of_subset hPX, sdiff_union_of_subset hQY]

lemma finDiff_sdiff_sdiff_singleton_iff (heX : e ∈ X) (hfY : f ∈ Y) :
    FinDiff (X \ {e}) (Y \ {f}) ↔ FinDiff X Y :=
  FinDiff.finDiff_sdiff_sdiff_iff (by simp) (by simpa) (by simpa)

lemma FinDiff.finDiff_sdiff_sdiff_singleton (hXY : FinDiff X Y) (heX : e ∈ X) (hfY : f ∈ Y) :
    FinDiff (X \ {e}) (Y \ {f}) :=
  (finDiff_sdiff_sdiff_singleton_iff heX hfY).2 hXY

lemma finDiff_insert_insert_iff (heX : e ∉ X) (hfY : f ∉ Y) :
    FinDiff (insert e X) (insert f Y) ↔ FinDiff X Y := by
  rw [← union_singleton, ← union_singleton,
    (finDiff_singleton_singleton e f).finDiff_union_union_iff (by simpa) (by simpa)]

lemma FinDiff.union_union {P Q : Set α} (hXY : FinDiff X Y) (hPQ : FinDiff P Q)
    (hPX : Disjoint P X) (hQY : Disjoint Q Y) : FinDiff (X ∪ P) (Y ∪ Q) := by
  rwa [hPQ.finDiff_union_union_iff hPX hQY]

lemma FinDiff.insert_insert (hXY : FinDiff X Y) (heX : e ∉ X) (hfY : f ∉ Y) :
    FinDiff (Insert.insert e X) (Insert.insert f Y) := by
  rwa [finDiff_insert_insert_iff heX hfY]

lemma FinDiff.exchange_right (hXY : FinDiff X Y) {e f : α} (heY : e ∈ Y) (hfY : f ∉ Y) :
    FinDiff X (Insert.insert f (Y \ {e})) := by
  by_cases heX : e ∈ X
  · have hrw := finDiff_insert_insert_iff (X := X \ {e}) (Y := Y \ {e}) (e := e) (f := e)
      (by simp) (by simp)
    simp only [insert_sdiff_singleton, insert_eq_of_mem heX, insert_eq_of_mem heY] at hrw
    rw [hrw] at hXY
    convert hXY.insert_insert (e := e) (f := f) (by simp) (by simp [hfY])
    simp [heX]
  have hef : e ≠ f := by rintro rfl; contradiction
  rwa [← finDiff_insert_insert_iff heX (f := e) (by simp [hef]), insert_comm, insert_sdiff_singleton,
    insert_eq_of_mem heY, finDiff_insert_insert_iff heX hfY]

lemma finDiff_iff_exchange (heY : e ∈ Y) (hfY : f ∉ Y) :
    FinDiff X Y ↔ FinDiff X (insert f (Y \ {e})) := by
  refine ⟨fun h ↦ h.exchange_right heY hfY, fun h ↦ ?_⟩
  convert h.exchange_right (e := f) (f := e) (by simp) (by aesop)
  simp [mem_singleton_iff, insert_sdiff_of_mem,
    insert_sdiff_singleton_comm (show e ≠ f by rintro rfl; contradiction),
    insert_eq_of_mem heY, sdiff_singleton_eq_self hfY]

lemma FinDiff.sdiff_right {S} (h : FinDiff X Y) (hXS : X ⊆ S) (hYS : Y ⊆ S) :
    FinDiff (S \ X) (S \ Y) := by
  induction h using FinDiff.induction with
  | refl => simp
  | exchange X Y Z hXY hYZ hu hi ih =>
      exact (ih hXS (by grind)).trans_exchange (hYZ.sdiff_right (by grind) hYS)

lemma finDiff_sdiff_right_iff {S : Set α} (hXS : X ⊆ S) (hYS : Y ⊆ S) :
    (S \ X).FinDiff (S \ Y) ↔ X.FinDiff Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.sdiff_right hXS hYS⟩
  rw [← sdiff_sdiff_cancel_left hXS, ← sdiff_sdiff_cancel_left hYS]
  exact h.sdiff_right sdiff_subset sdiff_subset

lemma finDiff_sdiff_right_comm {S} (hXS : X ⊆ S) (hYS : Y ⊆ S) :
    X.FinDiff (S \ Y) ↔ (S \ X).FinDiff Y := by
  rw [← finDiff_sdiff_right_iff hXS sdiff_subset, sdiff_sdiff_cancel_left hYS]

lemma Finite.finDiff_iff_encard_eq (hX : X.Finite) : X.FinDiff Y ↔ X.encard = Y.encard := by
  refine ⟨fun h ↦ h.encard_eq_encard, fun h ↦ finDiff_iff.2 ⟨hX.sdiff, ?_⟩⟩
  rwa [← encard_sdiff_add_encard_inter X Y, ← encard_sdiff_add_encard_inter Y X, inter_comm,
    add_left_inj_of_ne_top (by simpa using hX.inter_of_right Y)] at h
