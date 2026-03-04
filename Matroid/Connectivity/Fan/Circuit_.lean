import Matroid.Connectivity.Fan.Basic
import Matroid.Connectivity.Separation.Vertical
import Mathlib.Tactic.DepRewrite


open Set List



set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {F J : List α} {b c : Bool} {L : List ℕ}

variable {P Q : Set (Fin n)}


/-- `L.unique f` means that `L` has exactly one elements satisfying `f`. -/
def List.unique : List α → (α → Bool) → Bool
  | [], _ => false
  | a :: L, f => (f a && !L.any f) || (!f a && L.unique f)

-- lemma unique_cons_eq_cond {L : List α} {f : α → Bool} {a : α} :
--     (a :: L).unique f = bif f a then !L.any f else L.unique f := by
--   rfl

@[simp, grind .]
lemma unique_cons {L : List α} {f : α → Bool} {a : α} :
    (a :: L).unique f = ((f a && !L.any f) ||  (!f a && L.unique f)) := rfl

@[simp, grind .]
lemma unique_nil (f : α → Bool) : [].unique f = false := rfl

@[simp]
lemma unique_singleton (f : α → Bool) (a : α) : [a].unique f = f a := by
  simp

@[simp]
lemma unique_pair (f : α → Bool) (a b : α) :
    ([a,b].unique f) = ((f a && (!f b)) || (!(f a) && f b)) := by
  grind [unique]

@[simp]
lemma unique_map {β : Type*} (f : α → β) (g : β → Bool) (L : List α) :
    (L.map f).unique g = L.unique (g ∘ f) := by
  induction L with simp_all

-- lemma unique_map {β : Type*} (f : α → Bool) (g : α → β) (h : Function.LeftInverse) (L : List α) :
--     L.unique f = (L.map g)unique (g ∘ f) := by

lemma List.get_preimage_cons_of_mem (F : List α) (heX : e ∈ X) :
    (e :: F).get ⁻¹' X = insert 0 (Fin.succ '' (F.get ⁻¹' X)) := by
  simp only [length_cons, Set.ext_iff, mem_preimage, get_eq_getElem, Set.mem_insert_iff, mem_image]
  intro x
  grind [x.eq_zero_or_eq_succ]

lemma List.get_preimage_cons_of_notMem (F : List α) (heX : e ∉ X) :
    (e :: F).get ⁻¹' X = Fin.succ '' (F.get ⁻¹' X) := by
  simp only [length_cons, Set.ext_iff, mem_preimage, get_eq_getElem, mem_image]
  intro x
  grind [x.eq_zero_or_eq_succ]

@[simp]
lemma finRange_preimage_get (X : Set (Fin n)) :
    (List.finRange n).get ⁻¹' X = Fin.cast (by simp) ⁻¹' X := by
  ext; simp

@[simp]
lemma Fin.bodd_succ (i : Fin n) : (i.succ : ℕ).bodd = !(i : ℕ).bodd := by
  cases i; simp

@[simp]
lemma Fin.bodd_castSucc (i : Fin n) : (i.castSucc : ℕ).bodd = (i : ℕ).bodd := by
  cases i; simp

lemma Fin.bodd_rev (i : Fin n) : (i.rev : ℕ).bodd = ((i : ℕ).bodd == n.bodd) := by
  have := congr_arg Nat.bodd <| add_tsub_cancel_of_le (show i.1 + 1 ≤ n by grind)
  rw [← this, Nat.bodd_add, val_rev, Nat.bodd_succ]
  grind

@[simp]
lemma Fin.bodd_rev' (i : Fin n) : (n - (i.1 + 1)).bodd = ((i : ℕ).bodd == n.bodd) := by
  rw [← val_rev, Fin.bodd_rev]

@[simp, grind =]
lemma Fin.succ_eq_one_iff {x : Fin (n + 1)} : x.succ = 1 ↔ x = 0 := by
  rw [← Fin.succ_zero_eq_one, Fin.succ_inj]

@[simp, grind =]
lemma Fin.succ_eq_two_iff {x : Fin (n + 2)} : x.succ = 2 ↔ x = 1 := by
  rw [← Fin.succ_one_eq_two, Fin.succ_inj]

@[simp, grind =]
lemma Fin.castSucc_eq_one_iff {x : Fin (n + 2)} : x.castSucc = 1 ↔ x = 1 := by
  rw [← Fin.castSucc_one, Fin.castSucc_inj]

@[simp]
lemma Fin.last_succ_castSucc (n : ℕ) :
    (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ := by
  rfl


namespace Matroid.Fan


/-- A subset of indices of a fan is `Orthogonal` if it does not intersect any triad
in exactly one element. The set of indices of a matroid circuit must have this property. -/
inductive Orthogonal : {n : ℕ} → Bool → Set (Fin n) → Prop
  | zero (b) (P : Set (Fin 0)) : Orthogonal b P
  | one (b) (P : Set (Fin 1)) : Orthogonal b P
  | two (b) (P : Set (Fin 2)) : Orthogonal b P
  | succ_of_not' (n b) (P : Set (Fin (n + 2))) (h : Orthogonal (!b) P)
      (hb : b = true → (0 ∈ P ↔ 1 ∈ P)) : Orthogonal b (Fin.succ '' P)
  | insert_succ_of_not' (n b) (P : Set (Fin (n + 2))) (h : Orthogonal (!b) P)
      (hb : b = true → (0 ∈ P ∨ 1 ∈ P)) : Orthogonal b (insert 0 (Fin.succ '' P))

attribute [simp] Orthogonal.zero Orthogonal.one Orthogonal.two

-- lemma Orthogonal.ge_two (h : Orthogonal b P) : 2 ≤ n := by
--   cases h with simp_all

lemma Orthogonal.succ_of_not [n.AtLeastTwo] {P : Set (Fin n)} (h : Orthogonal (!b) P)
    (hb : b = true → (0 ∈ P ↔ 1 ∈ P)) : Orthogonal b (Fin.succ '' P) := by
  obtain rfl | rfl | n := n; simp; simp;
  exact h.succ_of_not' _ _ _ <| hb

lemma Orthogonal.insert_succ_of_not [n.AtLeastTwo] (h : Orthogonal (!b) P)
    (hb : b = true → (0 ∈ P ∨ 1 ∈ P)) : Orthogonal b (insert 0 (Fin.succ '' P)) := by
  obtain rfl | rfl | n := n; simp; simp
  exact h.insert_succ_of_not' _ _ _ <| hb

lemma Orthogonal.succ [n.AtLeastTwo] (h : Orthogonal b P)
    (hb : b = false → (0 ∈ P ↔ 1 ∈ P)) : Orthogonal (!b) (Fin.succ '' P) :=
  (b.not_not ▸ h).succ_of_not (by simpa)

lemma Orthogonal.insert_succ [n.AtLeastTwo] (h : Orthogonal b P)
    (hb : b = false → (0 ∈ P ∨ 1 ∈ P)) : Orthogonal (!b) (insert 0 (Fin.succ '' P)) :=
  (b.not_not ▸ h).insert_succ_of_not (by simpa)

-- maybe these next four are redundant
lemma Orthogonal.succ_of_not_of_ge {P : Set (Fin n)} (h : Orthogonal (!b) P)
    (hb : ∀ (h : 2 ≤ n), b = true → (⟨0, by lia⟩ ∈ P ↔ ⟨1, by lia⟩ ∈ P)) :
    Orthogonal b (Fin.succ '' P) := by
  obtain rfl | rfl | n := n; simp; simp;
  exact h.succ_of_not' _ _ _ <| hb (by simp)

lemma Orthogonal.insert_succ_of_not_of_ge {P : Set (Fin n)} (h : Orthogonal (!b) P)
    (hb : ∀ (h : 2 ≤ n), b = true → (⟨0, by lia⟩ ∈ P ∨ ⟨1, by lia⟩ ∈ P)) :
    Orthogonal b (insert 0 (Fin.succ '' P)) := by
  obtain rfl | rfl | n := n; simp; simp;
  exact h.insert_succ_of_not' _ _ _ <| hb (by simp)

lemma Orthogonal.succ_of_ge (h : Orthogonal b P)
    (hb : ∀ (h : 2 ≤ n), b = false → (⟨0, by lia⟩ ∈ P ↔ ⟨1, by lia⟩ ∈ P)) :
      Orthogonal (!b) (Fin.succ '' P) :=
  (b.not_not ▸ h).succ_of_not_of_ge <| by simpa

lemma Orthogonal.insert_succ_of_ge (h : Orthogonal b P)
    (hb : ∀ (h : 2 ≤ n), b = false → (⟨0, by lia⟩ ∈ P ∨ ⟨1, by lia⟩ ∈ P)) :
    Orthogonal (!b) <| insert 0 (Fin.succ '' P) :=
  (b.not_not ▸ h).insert_succ_of_not_of_ge <| by simpa

@[simp]
lemma orthogonal_empty : Orthogonal b (∅ : Set (Fin n)) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih => simpa using (@ih (!b)).succ_of_ge (by simp)

lemma orthogonal_three (P : Set (Fin 3)) (hbL : b = true → P.Nonempty → P.Nontrivial) :
    Orthogonal b P := by
  by_cases hP : 0 ∈ P
  · rw [← insert_diff_self_of_mem hP, diff_eq, ← Fin.range_succ, ← image_preimage_eq_inter_range]
    refine Orthogonal.insert_succ_of_not (by simp) fun hb ↦ ?_
    grind [(hbL hb ⟨_, hP⟩).exists_ne 0]
  rw [← P.image_preimage_eq_of_subset (f := Fin.succ) (by grind [Fin.range_succ])]
  refine (Orthogonal.two ..).succ_of_not fun hb ↦ ?_
  suffices 1 ∈ P ↔ 2 ∈ P by simpa
  obtain (rfl | ⟨x, hxP⟩) := P.eq_empty_or_nonempty
  · simp
  grind [(hbL hb ⟨x, hxP⟩).exists_ne x]

lemma orthogonal_three' (P : Set (Fin 3)) (hbL : b = true → P.Subsingleton → P = ∅) :
    Orthogonal b P :=
  orthogonal_three P fun hb hne ↦ Set.not_subsingleton_iff.1 fun hss ↦ hne.ne_empty <| hbL hb hss

@[simp]
lemma orthogonal_three_false (P : Set (Fin 3)) : Orthogonal false P :=
  orthogonal_three P (by simp)

@[simp]
lemma orthogonal_cast_iff {m : ℕ} (hnm : n = m) :
    Orthogonal b (Fin.cast hnm '' P) ↔ Orthogonal b P := by
  subst hnm
  simp

alias ⟨_, Orthogonal.image_cast⟩ := orthogonal_cast_iff

@[simp]
lemma orthogonal_preimage_cast_iff {m : ℕ} (hmn : m = n) :
    Orthogonal b (Fin.cast hmn ⁻¹' P) ↔ Orthogonal b P := by
  subst hmn
  simp

alias ⟨_, Orthogonal.preimage_cast⟩ := orthogonal_preimage_cast_iff

@[elab_as_elim]
lemma Orthogonal.induction₁
    {motive : {n : ℕ} → (b : Bool) → (P : Set (Fin (n + 1))) → Orthogonal b P → Prop}
    (one : ∀ (b : Bool) (P : Set (Fin 1)), motive b P (Orthogonal.one ..))
    (two : ∀ (b : Bool) (P : Set (Fin 2)), motive b P (Orthogonal.two ..))
    (succ_of_not : ∀ (n b) (P : Set (Fin (n + 2))) (h : Orthogonal (!b) P)
      (hb : b = true → (0 ∈ P ↔ 1 ∈ P)) (_ih : motive (!b) P h),
      motive b (Fin.succ '' P) (h.succ_of_not hb))
    (insert_succ_of_not : ∀ (n b) (P : Set (Fin (n + 2))) (h : Orthogonal (!b) P)
      (hb : b = true → (0 ∈ P ∨ 1 ∈ P)) (_ih : motive (!b) P h),
      motive b (insert 0 (Fin.succ '' P)) (h.insert_succ_of_not hb))
    {P : Set (Fin (n + 1))} (h : Orthogonal b P) : motive b P h := by
  suffices aux : ∀ (n : ℕ) (b : Bool) (hn : 1 ≤ n) (Q : Set (Fin n)) (hQ : Orthogonal b Q),
      motive (n := n - 1) b (Fin.cast (tsub_add_cancel_of_le hn).symm '' Q) (hQ.image_cast _) by
    simpa using aux _ b (by simp) P h
  intro n b hn Q hQ
  induction hQ with
  | succ_of_not' n b P h hb ih => simpa using succ_of_not _ b P h hb (by simpa using ih)
  | insert_succ_of_not' n b P h hb ih =>
      simpa using insert_succ_of_not _ b P h hb (by simpa using ih)
  | _ => grind

@[elab_as_elim]
lemma Orthogonal.induction₂
    {motive : {n : ℕ} → (b : Bool) → (P : Set (Fin (n + 2))) → Orthogonal b P → Prop}
    (two : ∀ (b : Bool) (P : Set (Fin 2)), motive b P (Orthogonal.two ..))
    (succ_of_not : ∀ (n b) (P : Set (Fin (n + 2))) (h : Orthogonal (!b) P)
      (hb : b = true → (0 ∈ P ↔ 1 ∈ P)) (_ih : motive (!b) P h),
      motive b (Fin.succ '' P) (h.succ_of_not hb))
    (insert_succ_of_not : ∀ (n b) (P : Set (Fin (n + 2))) (h : Orthogonal (!b) P)
      (hb : b = true → (0 ∈ P ∨ 1 ∈ P)) (_ih : motive (!b) P h),
      motive b (insert 0 (Fin.succ '' P)) (h.insert_succ_of_not hb))
    {P : Set (Fin (n + 2))} (h : Orthogonal b P) : motive b P h := by
  suffices aux : ∀ (n : ℕ) (b : Bool) (hn : 2 ≤ n) (Q : Set (Fin n)) (hQ : Orthogonal b Q),
      motive (n := n - 2) b (Fin.cast (tsub_add_cancel_of_le hn).symm '' Q) (hQ.image_cast _) by
    simpa using aux _ b (by simp) P h
  intro n b hn Q hQ
  induction hQ with
  | succ_of_not' n b P h hb ih => simpa using succ_of_not _ b P h hb (by simpa using ih)
  | insert_succ_of_not' n b P h hb ih =>
      simpa using insert_succ_of_not _ b P h hb (by simpa using ih)
  | _ => grind

lemma Orthogonal.succ_or_succ_succ_mem {P : Set (Fin (n + 2))} (h : Orthogonal b P) {i : Fin n}
    (hi : i.castSucc.castSucc ∈ P) (hib : (!(i : ℕ).bodd) = b) :
    i.castSucc.succ ∈ P ∨ i.succ.succ ∈ P := by
  induction h using Orthogonal.induction₂ with
  | two => grind
  | succ_of_not n b P h hb ih =>
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · simp at hi
    simpa using ih (by simpa using hi) (by simpa using hib)
  | insert_succ_of_not n b P h hb ih =>
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · simpa [two_ne_zero] using hb (by simpa using hib)
    simpa using ih (by simpa using hi) (by simpa using hib)

lemma Orthogonal.succ_iff_succ_succ_mem {P : Set (Fin (n + 2))} (h : Orthogonal b P) {i : Fin n}
    (hi : i.castSucc.castSucc ∉ P) (hib : (!(i : ℕ).bodd) = b) :
    i.castSucc.succ ∈ P ↔ i.succ.succ ∈ P := by
  induction h using Orthogonal.induction₂ with
  | two => grind
  | succ_of_not n b P h hb ih =>
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · simpa using hb (by simpa using hib)
    simpa using ih (by simpa using hi) (by simpa using hib)
  | insert_succ_of_not n b P h hb ih =>
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · simp at hi
    simpa using ih (by simpa using hi) (by simpa using hib)

lemma Orthogonal.mem_or_succ_succ_mem {P : Set (Fin (n + 2))} (h : Orthogonal b P) {i : Fin n}
    (hi : i.succ.castSucc ∈ P) (hib : (!(i : ℕ).bodd) = b) :
    i.castSucc.castSucc ∈ P ∨ i.succ.succ ∈ P := by
  grind [h.succ_iff_succ_succ_mem, h.succ_or_succ_succ_mem]

lemma Orthogonal.mem_iff_succ_succ_mem {P : Set (Fin (n + 2))} (h : Orthogonal b P) {i : Fin n}
    (hi : i.succ.castSucc ∉ P) (hib : (!(i : ℕ).bodd) = b) :
    i.castSucc.castSucc ∈ P ↔ i.succ.succ ∈ P := by
  grind [h.succ_iff_succ_succ_mem, h.succ_or_succ_succ_mem]

lemma Orthogonal.mem_or_succ_mem {P : Set (Fin (n + 2))} (h : Orthogonal b P) {i : Fin n}
    (hi : i.succ.succ ∈ P) (hib : (!(i : ℕ).bodd) = b) :
    i.castSucc.castSucc ∈ P ∨ i.succ.castSucc ∈ P := by
  grind [h.succ_iff_succ_succ_mem, h.succ_or_succ_succ_mem]

lemma Orthogonal.mem_iff_succ_mem {P : Set (Fin (n + 2))} (h : Orthogonal b P) {i : Fin n}
    (hi : i.succ.succ ∉ P) (hib : (!(i : ℕ).bodd) = b) :
    i.castSucc.castSucc ∈ P ↔ i.succ.castSucc ∈ P := by
  grind [h.succ_iff_succ_succ_mem, h.succ_or_succ_succ_mem]

lemma Orthogonal.not_unique {P : Set (Fin (n + 2))} (h : Orthogonal b P) (i : Fin n)
    [DecidablePred (· ∈ P)] (hib : (!(i : ℕ).bodd) = b) :
    [i.castSucc.castSucc, i.succ.castSucc, i.succ.succ].unique (· ∈ P) = false := by
  by_cases hi : i.castSucc.castSucc ∈ P
  · simpa [hi, ← or_iff_not_imp_left] using h.succ_or_succ_succ_mem hi (by simpa using hib)
  grind [h.succ_iff_succ_succ_mem hi (by simpa using hib)]

lemma Orthogonal.mem_one_or_two (h : Orthogonal true P) (hn : 3 ≤ n) (h0 : ⟨0, by lia⟩ ∈ P) :
    ⟨1, by lia⟩ ∈ P ∨ ⟨2, by lia⟩ ∈ P := by
  obtain rfl | rfl | rfl | n := n; lia; lia; lia
  exact h.succ_or_succ_succ_mem (i := 0) h0 rfl

lemma Orthogonal.mem_one_iff_two (h : Orthogonal true P) (hn : 3 ≤ n) (h0 : ⟨0, by lia⟩ ∉ P) :
    ⟨1, by lia⟩ ∈ P ↔ ⟨2, by lia⟩ ∈ P := by
  obtain rfl | rfl | rfl | n := n; lia; lia; lia
  exact h.succ_iff_succ_succ_mem (i := 0) h0 rfl

lemma Orthogonal.castSucc {P : Set (Fin (n + 2))} (h : Orthogonal b P)
    (hnb : b = !n.bodd → (Fin.last (n + 1) ∈ P ↔ (Fin.last n).castSucc ∈ P)) :
    Orthogonal b (Fin.castSucc '' P) := by
  induction h using Orthogonal.induction₂ with
  | two b P =>
    suffices b = true → P.Nonempty → P.Nontrivial from orthogonal_three _ <| by simpa
    rintro rfl ⟨i, hi⟩
    exact nontrivial_of_exists_ne hi <| by grind [Nat.bodd_zero]
  | succ_of_not n b P h hb ih => simpa [image_image] using (ih (by simpa using hnb)).succ (by simpa)
  | insert_succ_of_not n b P h hb ih =>
    simpa [image_image, image_insert_eq] using (ih (by simpa using hnb)).insert_succ (by simpa)

lemma Orthogonal.castSucc_insert {P : Set (Fin (n + 2))} (h : Orthogonal b P)
    (hnb : b = !n.bodd → (Fin.last (n + 1) ∈ P ∨ (Fin.last n).castSucc ∈ P)) :
    Orthogonal b (insert (Fin.last _) (Fin.castSucc '' P)) := by
  induction h using Orthogonal.induction₂ with
  | two b P =>
    refine orthogonal_three' _ fun hb ↦ ?_
    simpa [(insert_nonempty ..).ne_empty, or_and_right, exists_or, or_comm] using hnb hb
  | succ_of_not n b P h hb ih =>
    simpa [image_insert_eq, image_image] using (ih (by simpa using hnb)).succ_of_not
      (by simpa [Fin.last])
  | insert_succ_of_not n b P h hb ih =>
    simpa [image_insert_eq, image_image, insert_comm] using
      (ih (by simpa using hnb)).insert_succ_of_not (by simpa [Fin.last])

lemma orthogonal_iff_forall (P : Set (Fin (n + 2))) [DecidablePred (· ∈ P)] :
    Orthogonal b P ↔ ∀ (i : Fin n), (!(i : ℕ).bodd) = b →
        ([i.castSucc.castSucc, i.succ.castSucc, i.succ.succ].unique (· ∈ P)) = false := by
  classical
  refine ⟨fun h i hib ↦ h.not_unique i hib, fun h ↦ ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    specialize ih (Fin.castSucc ⁻¹' P) fun i hb ↦ by simpa using h i.castSucc hb
    by_cases hn : Fin.last _ ∈ P
    · convert ih.castSucc_insert <| by grind [h (Fin.last _)]
      grind [image_preimage_eq_inter_range, Fin.range_castSucc]
    convert ih.castSucc <| by grind [h (Fin.last _)]
    grind [image_preimage_eq_inter_range, Fin.range_castSucc]

lemma Orthogonal.iUnion {ι : Sort*} (X : ι → Set (Fin n)) (hX : ∀ i, Orthogonal b (X i)) :
    Orthogonal b (⋃ i, X i) := by
  obtain rfl | rfl | n := n; simp; simp
  classical
  simp_rw [orthogonal_iff_forall] at *
  rintro k rfl
  simp only [Fin.castSucc_succ, unique_cons, mem_iUnion,] at *
  grind

lemma Orthogonal.iUnion₂ {ι : Type*} {η : ι → Sort*} (X : ∀ i, η i → Set (Fin n))
    (hX : ∀ (i : ι) (j : η i), Orthogonal b (X i j)) :
    Orthogonal b (⋃ (i : ι) (j : η i), X i j) :=
  Orthogonal.iUnion _ fun i ↦ Orthogonal.iUnion _ <| hX i

lemma Orthogonal.biUnion (Xs : Set (Set (Fin n))) (hX : ∀ X ∈ Xs, Orthogonal b X) :
    Orthogonal b (⋃ X ∈ Xs, X) :=
  Orthogonal.iUnion₂ _ (by simpa)


def Closed (b : Bool) (P : Set (Fin n)) : Prop := Orthogonal (!b) Pᶜ

lemma Closed.succ (h : Closed b P) (hb : ∀ (hn : 2 ≤ n), b = true → ⟨0, by lia⟩ ∈ P ↔ ⟨1, hn⟩ ∉ P) :
    Closed (!b) (Fin.succ '' P) := by
  rw [Closed]
  convert Orthogonal.insert_succ_of_ge h <| by grind using 1
  rw [image_compl_eq_range_diff_image (Fin.succ_injective n), Fin.range_succ]
  grind

lemma Closed.succ_insert (h : Closed b P)
    (hb : ∀ (hn : 2 ≤ n), b = true → ⟨0, by lia⟩ ∈ P ∧ ⟨1, hn⟩ ∈ P) :
    Closed (!b) (insert 0 (Fin.succ '' P)) := by
  rw [Closed]
  convert Orthogonal.succ_of_ge h <| by grind using 1
  rw [image_compl_eq_range_diff_image (Fin.succ_injective n), Fin.range_succ]
  grind

def Spans (b : Bool) (P : Set (Fin n)) (i : Fin n) : Prop := ∀ Q, Closed b Q → P ⊆ Q → i ∈ P

end Fan

open Fan

/-- The index-intersection of a circuit with a fan is orthogonal. -/
lemma IsFan.inter_circuit_orthogonal (h : M.IsFan F b c) (hC : M.IsCircuit C) :
    Fan.Orthogonal b (F.get ⁻¹' C) := by
  induction h with
  | of_pair => simp
  | cons_triangle e x y F b c h heF hT ih =>
    by_cases heC : e ∈ C
    · rw [get_preimage_cons_of_mem _ heC]
      exact ih.insert_succ_of_ge fun _ hb ↦ hT.mem_or_mem_of_isCircuit_bDual (by simpa [hb]) heC
    rw [get_preimage_cons_of_notMem _ heC]
    exact ih.succ_of_ge fun _ hb ↦ hT.mem_iff_mem_of_isCircuit_bDual (by simpa [hb]) heC

lemma IsFan.get_preimage_compl (hF : M.IsFan F b c) (X : Set α) :
    (F.get ⁻¹' X)ᶜ = F.get ⁻¹' (M.E \ X) := by
  grind [hF.subset_ground]

lemma IsFan.inter_flat_closed (hF : M.IsFan F b c) (hX : M.IsFlat X) : Closed b (F.get ⁻¹' X) := by
  by_cases hXE : X = M.E
  · simp [Closed, hF.get_preimage_compl, hXE]
  obtain ⟨Hs, hHs, hXh, rfl⟩ := hX.eq_sInter_isHyperplanes_of_ne_ground hXE
  simp_rw [preimage_sInter, Closed, compl_iInter₂, hF.get_preimage_compl]
  exact Orthogonal.iUnion₂ _ fun H hH ↦
    hF.dual.inter_circuit_orthogonal (hXh H hH).compl_isCocircuit





-- #exit
--     -- (hNF : N.IsFan (List.finRange (n + 4)) false true)


-- lemma Orthogonal.mem_or_mem_right (h : Orthogonal n b P) (hin : i + 2 < n)
--     (hi : i.bodd = !b) (hiP : i ∈ P) : i + 1 ∈ P ∨ i + 2 ∈ P := by
--   induction h generalizing i with
--   | small => lia
--   | succ_of_not' n b P h hle hb ih =>
--     cases i with
--     | zero => simp at hiP
--     | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)
--   | insert_succ_of_not' n b P h hle hb ih =>
--     cases i with
--     | zero => simpa using hb (by simpa using hi)
--     | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)

-- lemma Orthogonal.mem_iff_mem_right (h : Orthogonal n b P) (hin : i + 2 < n)
--     (hi : i.bodd = !b) (hiP : i ∉ P) : i + 1 ∈ P ↔ i + 2 ∈ P := by
--   induction h generalizing i with
--   | small => lia
--     | succ_of_not' n b P h hle hb ih =>
--     cases i with
--     | zero => simpa using hb (by simpa using hi)
--     | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)
--   | insert_succ_of_not' n b P h hle hb ih =>
--     cases i with
--     | zero => simp at hiP
--     | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)

-- lemma Orthogonal.mem_or_mem_left_right (h : Orthogonal n b P) (hin : i + 2 < n)
--     (hi : i.bodd = !b) (hiP : i + 1 ∈ P) : i ∈ P ∨ i + 2 ∈ P := by
--   grind [h.mem_iff_mem_right hin hi]

-- lemma Orthogonal.mem_iff_mem_left_right (h : Orthogonal n b P) (hin : i + 2 < n)
--     (hi : i.bodd = !b) (hiP : i + 1 ∉ P) : i ∈ P ↔ i + 2 ∈ P := by
--   grind [h.mem_or_mem_right hin hi, h.mem_iff_mem_right hin hi]

-- lemma Orthogonal.mem_or_mem_left (h : Orthogonal n b P) (hi : i.bodd = !b)
--     (hiP : i + 2 ∈ P) : i ∈ P ∨ i + 1 ∈ P := by
--   grind [h.mem_iff_mem_right (by simpa using Finset.mem_of_subset h.subset_range hiP) hi]

-- lemma Orthogonal.mem_iff_mem_left (h : Orthogonal n b P) (hin : i + 2 < n)
--     (hi : i.bodd = !b) (hiP : i + 2 ∉ P) : i ∈ P ↔ i + 1 ∈ P := by
--   grind [h.mem_iff_mem_right hin hi, h.mem_or_mem_right hin hi]

-- lemma Orthogonal.card_inter_triad_ne_one (h : Orthogonal n b P) (hin : i + 2 < n)
--     (hi : i.bodd = !b) : ({i, i + 1, i + 2} ∩ P).card ≠ 1 := by
--   grind [h.mem_or_mem_left hi, h.mem_iff_mem_left]

-- lemma Orthogonal.succ_right (h : Orthogonal (n + 2) b P)
--     (hnb : b = !n.bodd → (n ∈ P ↔ n + 1 ∈ P)) : Orthogonal (n + 3) b P := by
--   generalize hm : n + 2 = m at h
--   induction h generalizing n with
--   | small => grind [orthogonal_three, Finset.subset_range_two, Nat.bodd_zero]
--   | succ_of_not' m b P h hle hb ih =>
--     refine Orthogonal.succ_of_not ?_ hb
--     cases n with
--     | zero => exact Orthogonal.small rfl.le <| h.subset_range.trans <| by grind
--     | succ => exact ih (by simpa using hnb) <| by lia
--   | insert_succ_of_not' m b P h hle hb ih =>
--     refine Orthogonal.insert_succ_of_not ?_ hb
--     cases n with
--     | zero => exact Orthogonal.small rfl.le <| h.subset_range.trans <| by grind
--     | succ n => exact ih (by simpa using hnb) <| by lia

-- lemma Orthogonal.cons_succ_right (h : Orthogonal (n + 2) b P)
--     (hnb : b = !n.bodd → (n ∈ P ∨ n + 1 ∈ P)) :
--     Orthogonal (n + 3) b (P.cons (n + 2) (by grind [h.subset_range])) := by
--   generalize_proofs hnP
--   rw [Finset.cons_eq_insert]
--   generalize hm : n + 2 = m at h
--   induction h generalizing n with
--   | small => grind [orthogonal_three, Finset.subset_range_two, Nat.bodd_zero]
--   | succ_of_not' m b P h hle hb ih =>
--     cases n with
--     | zero => exact orthogonal_three (by grind [h.subset_range]) <| by grind [Nat.bodd_zero]
--     | succ n => simpa [add_right_comm] using
--         (ih (by simpa using hnb) (by grind) (by lia)).succ_of_not (by grind)
--   | insert_succ_of_not' m b P h hle hb ih =>
--     cases n with
--     | zero => exact orthogonal_three (by grind [h.subset_range]) <| by grind
--     | succ n => simpa [Finset.insert_comm, add_right_comm] using
--         (ih (by simpa using hnb) (by grind) (by lia)).insert_succ_of_not (by grind)

-- lemma Orthogonal.erase_of_succ (h : Orthogonal (n + 1) b P) :
--     Orthogonal n b (P.erase n) := by
--   generalize hmn : n + 1 = m at h
--   induction h generalizing n with
--   | small => exact Orthogonal.small (by lia) <| by grind
--   | succ_of_not' m b P h hle hb ih =>
--     obtain rfl : n = m := by lia
--     obtain rfl | rfl | rfl | n := n; lia; lia; grind [orthogonal_of_le_two hle, h.subset_range]
--     rw [show n + 3 = addRightEmbedding 1 (n + 2) from rfl, ← Finset.map_erase]
--     exact (ih (n := n + 2) (by lia)).succ_of_not <| by simpa
--   | insert_succ_of_not' m b P h hn hb ih =>
--     obtain rfl : n = m := by lia
--     obtain rfl | rfl | rfl | n := n; lia; lia; grind [orthogonal_two, h.subset_range]
--     rw [show n + 3 = addRightEmbedding 1 (n + 2) from rfl, Finset.erase_insert_of_ne (by grind),
--       ← Finset.map_erase]
--     exact (ih (by lia)).insert_succ_of_not <| by simpa

-- lemma Orthogonal.of_succ (h : Orthogonal (n + 1) b P) (hP : n ∉ P) :
--     Orthogonal n b P := by
--   rw [← Finset.erase_eq_of_notMem hP]
--   exact h.erase_of_succ

-- lemma Orthogonal.of_succ_insert (h : Orthogonal (n + 1) b (insert n P)) (hP : n ∉ P) :
--     Orthogonal n b P := by
--   rw [← Finset.erase_insert hP]
--   exact h.erase_of_succ

-- @[elab_as_elim]
-- lemma Orthogonal.induction_right
--     {motive : (n : ℕ) → (b : Bool) → (P : Finset ℕ) → Orthogonal n b P → Prop}
--     (small : ∀ (n b P) (hn : n ≤ 2) (hP : P ⊆ Finset.range n),
--       motive n b P (Orthogonal.small hn hP))
--     (succ : ∀ (n b P) (h : Orthogonal (n + 2) b P) (hb : b = !n.bodd → (n ∈ P ↔ (n + 1) ∈ P))
--       (_ih : motive _ _ _ h), motive (n + 3) b P (h.succ_right hb))
--     (succ_cons : ∀ (n b P) (h : Orthogonal (n + 2) b P)
--       (hb : b = !n.bodd → (n ∈ P ∨ (n + 1) ∈ P))
--       (_ih : motive _ _ _ h), motive (n + 3) b (P.cons (n + 2) (by grind [h.subset_range]))
--       (h.cons_succ_right hb))
--     (h : Orthogonal n b P) : motive n b P h := by
--   obtain hle | (hlt : 3 ≤ n) := le_or_gt n 2
--   · grind [h.subset_range]
--   obtain ⟨m, rfl⟩ := show ∃ m, n = m + 3 by obtain rfl | rfl | rfl | n := n <;> grind
--   induction m generalizing P with
--   | zero =>
--     by_cases hmP : 2 ∈ P
--     · convert succ_cons _ _ _ h.erase_of_succ ?_ (small _ _ _ rfl.le (by grind [h.subset_range]))
--       · simp_rw [zero_add, Finset.cons_eq_insert, Finset.insert_erase hmP]
--       rintro rfl
--       grind [h.mem_one_iff_two (by lia)]
--     convert succ _ _ _ h.erase_of_succ ?_ (small _ _ _ rfl.le (by grind [h.subset_range]))
--     · rw [Finset.erase_eq_of_notMem hmP]
--     rintro rfl
--     grind [h.mem_one_iff_two (by lia), h.mem_one_or_two (by lia)]
--   | succ m ih =>
--     specialize ih h.erase_of_succ (by lia)
--     by_cases hmP : m + 3 ∈ P
--     · convert succ_cons _ _ _ h.erase_of_succ ?_ ih
--       · simp [Finset.insert_erase hmP]
--       rintro rfl
--       simpa using h.mem_or_mem_left (by simp) hmP
--     convert succ _ _ _ h.erase_of_succ ?_ ih
--     · rw [Finset.erase_eq_of_notMem hmP]
--     rintro rfl
--     simpa using h.mem_iff_mem_left (by lia) (by simp) hmP

-- lemma orthogonal_triangle (hin : i + 2 < n) (hib : i.bodd = b) :
--     Orthogonal n b {i, i + 1, i + 2} := by
--   induction n generalizing i b with
--   | zero => simp at hin
--   | succ n ih =>
--     obtain hlt | rfl := Nat.lt_add_one_iff_lt_or_eq.1 hin
--     · obtain rfl | rfl | rfl | n := n; lia; lia; lia
--       apply (ih hlt hib).succ_right
--       rintro rfl
--       grind [Nat.bodd_succ]
--     obtain rfl | i := i
--     · grind [orthogonal_three]
--     simpa using (@ih i (!b) (by lia) (by simpa using hib)).succ <| by grind [Nat.bodd_eq_ite]

-- lemma orthogonal_of_forall_triad (hP : P ⊆ Finset.range n)
--     (hib : ∀ i, i.bodd = !b → i + 2 < n → ({i, i + 1, i + 2} ∩ P).card ≠ 1) :
--     Orthogonal n b P := by
--   induction n generalizing P with
--   | zero => grind [orthogonal_zero]
--   | succ n ih =>
--     obtain rfl | rfl | n := n; grind [orthogonal_one]; grind [orthogonal_two]
--     obtain hn | hn := em' <| (n + 2) ∈ P
--     · exact (@ih P (by grind) (by grind)).succ_right <| by rintro rfl; grind
--     specialize @ih (P.erase (n + 2)) (by grind) (by grind)
--     simpa [Finset.insert_erase hn] using ih.cons_succ_right (by grind)

-- @[mk_iff]
-- structure IsClosed (n : ℕ) (b : Bool) (P : Finset ℕ) : Prop where
--   subset_range : P ⊆ Finset.range n
--   orthogonal : Orthogonal n (!b) (Finset.range n \ P)

-- lemma range_isClosed (n : ℕ) (b : Bool) : IsClosed n b (Finset.range n) :=
--   ⟨rfl.subset, by simp⟩

-- lemma isClosed_of_forall_triangle (hP : P ⊆ Finset.range n)
--     (hib : ∀ i, i.bodd = b → i + 2 < n → ({i, i + 1, i + 2} ∩ P).card ≠ 2) : IsClosed n b P := by
--   rw [isClosed_iff, and_iff_right hP]
--   refine orthogonal_of_forall_triad (by simp) fun i hi hin hcard ↦ ?_
--   rw [← Finset.inter_sdiff_left_comm, Finset.inter_eq_right.2 (by grind)] at hcard
--   grind

-- structure Spans (n : ℕ) (b : Bool) (P : Finset ℕ) (i : ℕ) : Prop where
--   subset_range : P ⊆ Finset.range n
--   forall_isClosed : ∀ Q, IsClosed n b Q → P ⊆ Q → i ∈ P

-- lemma Spans.superset (h : Spans n b P i) (hPQ : P ⊆ Q) (hQ : Q ⊆ Finset.range n) :
--     Spans n b Q i :=
--   ⟨hQ, fun F hF hQF ↦ Finset.mem_of_subset hPQ <| (h.forall_isClosed F hF (hPQ.trans hQF))⟩

-- lemma Spans.of_mem (hP : P ⊆ Finset.range n) (hiP : i ∈ P) : Spans n b P i :=
--   ⟨hP, fun _ _ _ ↦ hiP⟩

-- lemma Spans.lt (h : Spans n b P i) : i < n := by
--   simpa using Finset.mem_of_subset h.subset_range
--     <| h.forall_isClosed _ (range_isClosed n b) h.subset_range

-- -- lemma aux {s t : Finset ℕ} {a : ℕ} {hs : s.card = 3} (h : (s ∩ t).card = a) :
-- --     ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ∈ s ∧ x ∈ t ∧ y ∈ s ∧ y ∈ t ∧ z ∈ s ∧ z ∉ t := by
-- --   _
-- example (s : Set (Fin 5)) : Finset ℕ := by
--   classical
--   have := s.toFinset

-- lemma bar {b c : Bool} (hF : M.IsFan F b c) [DecidablePred (· ∈ X)] (hX : M.IsFlat X) :

--     IsClosed F.length b <| (F.get ⁻¹' X).toFinite.toFinset.map Fin.valEmbedding := by
--   refine isClosed_of_forall_triangle ?_ fun i hi hin ↦ ?_
--   · grw [Finset.subset_univ]
--     -- grw [(findIdxs_sublist_range ..).subset.toFinset_subset, toFinset_range]

-- lemma bar {b c : Bool} (hF : M.IsFan F b c) [DecidablePred (· ∈ X)] (hX : M.IsFlat X) :
--     IsClosed F.length b (F.findIdxs (· ∈ X)).toFinset := by
--   classical
--   refine isClosed_of_forall_triangle ?_ fun i hi hin ↦ ?_
--   · grw [(findIdxs_sublist_range ..).subset.toFinset_subset, toFinset_range]
--   intro h2
--   set T : Finset ℕ := {i, i + 1, i + 2} with hT
--   set U := (findIdxs (· ∈ X) F).toFinset with hU
--   have hcard := Finset.card_sdiff_add_card_inter T U
--   rw [h2, show Finset.card T = 1 + 2 by simp [hT], add_right_cancel_iff,
--     Finset.card_eq_one] at hcard
--   obtain ⟨a, ha⟩ := hcard
--   have han : a < F.length := by grind [show a ∈ T \ U by grind]
--   have ⟨haT, haU⟩ : a ∈ T ∧ a ∉ U := by simpa using Finset.subset_of_eq ha.symm
--   suffices ha : F[a] ∈ X by simp [hU, han, ha] at haU
--   have h1 := (hF.isTriangle_get _ hin).isCircuit.subset_closure_diff_singleton (F[a])
--   simp only [hi, bne_self_eq_false, bDual_false] at h1
--   refine mem_of_mem_of_subset (by grind) (h1.trans <| hX.closure_subset_of_subset ?_)




--   -- simp [Finset.inter_insert, show i < F.length by lia, show i + 1 < F.length by lia,
--   --   Finset.singleton_inter, hin]
--   -- rw [Finset.card_insert_eq_ite]
--   -- intro hcard
--   -- by_cases hi : F[i] ∈ X
--   -- · rw [Finset.insert_inter_of_mem (by simp [hi, show i < F.length by lia])] at hcard
--   --   by_cases hi' : F[i+1] ∈ X
--   --   · rw [Finset.insert_inter_of_mem (by simp [hi, show i + 1 < F.length by lia])] at hcard
--   --     have hi2 : F[i+2] ∉ X := by
--   --       simpa [← Finset.disjoint_iff_inter_eq_empty, hin] using hcard



--   -- simp only [Finset.card_eq_two, ne_eq, Finset.ext_iff, Finset.mem_inter, Finset.mem_insert,
--   --   Finset.mem_singleton, List.mem_toFinset, mem_findIdxs_iff_getElem_sub_pos, zero_le, tsub_zero,
--   --   decide_eq_true_eq, true_and] at hcard
--   -- by_cases hi : F[i] ∈ X
--   -- · sorry
--   -- simp [iff_def, or_imp, forall_and, hi] at hcard
--   -- rw [Finset.card_eq_two] at hcard
--   -- simp only [ne_eq, Finset.ext_iff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
--   --   List.mem_toFinset, mem_findIdxs_iff_getElem_sub_pos, zero_le, tsub_zero, decide_eq_true_eq,
--   --   true_and, iff_def, and_imp, forall_exists_index, or_imp, forall_and, forall_eq,
--   --   show i < F.length by lia, forall_true_left, show i + 1 < F.length by lia,
--   --   show i + 2 < F.length by lia] at hcard

--   -- obtain ⟨x, y, hxy, h_eq⟩ := hcard

--   -- obtain ⟨z, hz, hzx, hzy⟩ : ∃ z, z ∈ ({i, i + 1, i + 2} : Finset ℕ) ∧ z ≠ x ∧ z ≠ y := by
--   --   simp only [Finset.mem_insert, exists_eq_or_imp, Finset.mem_singleton]
--   --   grind

--   -- simp only [Finset.mem_insert, Finset.mem_singleton] at hz
--   -- have h1 := (hF.isTriangle_get i hin).isCircuit.subset_closure_diff_singleton (e := F[z])
--   -- simp only [← hi, bne_self_eq_false, bDual_false] at h1
--   -- have h2 := hX.closure_subset_of_subset (X := {F[i], F[i+1], F[i+2]} \ {F[z]}) ?_
--   -- · have h3 := mem_of_mem_of_subset (x := F[z]) (by grind) (h1.trans h2)
--   --   have := Finset.mem_of_subset (Finset.subset_of_eq h_eq) (a := z)
--   --   grind [List.mem_toFinset]
--   -- simp [Set.subset_def]
--   -- sorry













-- -- lemma foo {b c : Bool} (hF : M.IsFan F b c) [DecidablePred (· ∈ X)] (hXE : X ⊆ M.E)
-- --     (h : Spans F.length b (F.findIdxs (· ∈ X)).toFinset i) : F[i]'(h.lt) ∈ M.closure X := by
-- --   -- `hXE` not actually needed
