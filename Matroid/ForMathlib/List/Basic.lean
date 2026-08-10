module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace List

open Set

variable {α : Type*} {l : List α}

lemma getElem_mem_dropLast {i} (hi : i < l.length - 1) : l[i] ∈ l.dropLast := by
  rw [← l.getElem_dropLast (by simpa using hi)]
  exact getElem_mem ..

lemma Nodup.countP_eq_card {α} {l : List α} {P : α → Prop} [DecidableEq α] [DecidablePred P]
    (h : l.Nodup) : countP P l = (l.toFinset.filter P).card := by
  rw [countP_eq_length_filter, ← toFinset_card_of_nodup (h.filter ..)]
  simp

lemma Nodup.eq_singleton_iff_head_getLast {α} {l : List α} (hnd : l.Nodup) (hne : l ≠ []) :
    l.head hne = l.getLast hne ↔ ∃ x, l = [x] :=
  ⟨fun h => by cases l <;> grind, fun ⟨x, hx⟩ => by grind⟩

lemma eq_of_length_eq_zero {α} {l : List α} (h : l.length = 0) : l = [] := by
  match l with
  | [] => rfl
  | head :: tail => simp at h

lemma eq_of_length_eq_one {α} {l : List α} (h : l.length = 1) : l = [l[0]] := by
  match l with
  | [] => simp at h
  | head :: tail => simpa using h

lemma eq_of_length_eq_two {α} {l : List α} (h : l.length = 2) : l = [l[0], l[1]] := by
  match l with
  | [] => simp at h
  | head :: [tail] => simp
  | head :: tail :: tail' => simpa using h

lemma eq_of_length_eq_three {α} {l : List α} (h : l.length = 3) : l = [l[0], l[1], l[2]] := by
  match l with
  | [] => simp at h
  | head :: [tail] => simp at h
  | head :: tail :: [tail'] => simp
  | head :: tail :: tail' :: tail'' => simpa using h

lemma eq_of_map_eq_map {β : Type*} {l l' : List α} {f : α → β} (h : l.map f = l'.map f)
    (hinj : Set.InjOn f {x | x ∈ l ∨ x ∈ l'}) : l = l' := by
  induction l generalizing l' with
  | nil => simpa using h
  | cons x l ih =>
    cases l' with
    | nil => simp at h
    | cons y l' =>
      simp only [map_cons, cons.injEq] at h
      rw [hinj (by simp) (by simp) h.1, ih h.2 (hinj.mono (by grind))]

lemma mem_dropLast_iff {ι} {x : ι} {l : List ι} (hnd : l.Nodup) (hne : l ≠ []) :
    x ∈ l.dropLast ↔ x ∈ l ∧ x ≠ l.getLast hne := by
  obtain rfl | ⟨l', y, rfl⟩ := l.eq_nil_or_concat <;> grind

lemma mem_dropLast_of_mem_ne {ι} {x : ι} {l : List ι} (hne : l ≠ []) (hmem : x ∈ l)
    (hxne : x ≠ l.getLast hne) : x ∈ l.dropLast := by
  obtain rfl | ⟨l', y, rfl⟩ := l.eq_nil_or_concat <;> grind

lemma mem_iff_eq_head_or_mem_tail {α} {x : α} {l : List α} (hne : l ≠ []) :
    x ∈ l ↔ x = l.head hne ∨ x ∈ l.tail := by
  match l with
  | [] => simp at hne
  | head :: tail => simp

lemma mem_iff_mem_dropLast_or_eq_getLast {α} {x : α} {l : List α} (hne : l ≠ []) :
    x ∈ l ↔ x ∈ l.dropLast ∨ x = l.getLast hne := by
  induction l using List.reverseRec with
  | nil => simp at hne
  | append_singleton l a _ => simp

lemma Nodup.eq_head_or_mem_tail_ne {α} {x : α} {l : List α} (hnd : l.Nodup) (hx : x ∈ l) :
    x = l.head (ne_nil_of_mem hx) ∨ x ≠ l.head (ne_nil_of_mem hx) ∧ x ∈ l.tail := by
  match l with | [] => simp at hx | a :: as => grind

@[grind =]
lemma Nodup.mem_iff_eq_head_or_mem_tail {α} {x : α} {l : List α} (hnd : l.Nodup) (hne : l ≠ []) :
    x ∈ l ↔ x = l.head hne ∨ x ≠ l.head hne ∧ x ∈ l.tail := by
  match l with | [] => simp at hne | a :: as => grind

lemma Nodup.eq_getLast_or_mem_dropLast_ne {α} {x : α} {l : List α} (hnd : l.Nodup) (hx : x ∈ l) :
    x = l.getLast (ne_nil_of_mem hx) ∨ x ≠ l.getLast (ne_nil_of_mem hx) ∧ x ∈ l.dropLast := by
  induction l using List.reverseRec with | nil => simp at hx | append_singleton l a _ => grind

@[grind =]
lemma Nodup.mem_iff_eq_getLast_or_mem_dropLast {α} {x : α} {l : List α} (hnd : l.Nodup)
    (hne : l ≠ []) : x ∈ l ↔ x = l.getLast hne ∨ x ≠ l.getLast hne ∧ x ∈ l.dropLast := by
  induction l using List.reverseRec with | nil => simp at hne | append_singleton l a _ => grind

lemma IsSuffix.eq_of_first_mem {α} {l₁ l₂ : List α} (h : l₁.IsSuffix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.head hne ∈ l₁) : l₁ = l₂ := by
  match h with
  | .intro w h => grind

lemma IsPrefix.eq_of_last_mem {α} {l₁ l₂ : List α} (h : l₁.IsPrefix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.getLast hne ∈ l₁) : l₁ = l₂ := by
  simpa using h.reverse.eq_of_first_mem (by simpa) (by simpa) (by simpa)

@[gcongr] lemma IsPrefix.tail {α} {l₁ l₂ : List α} (h : l₁ <+: l₂) : l₁.tail <+: l₂.tail := by
  convert h.drop 1 using 1 <;> exact drop_one.symm

@[gcongr] lemma IsPrefix.dropLast {α} {l₁ l₂ : List α} (h : l₁ <+: l₂) :
    l₁.dropLast <+: l₂.dropLast := by
  obtain heq | hlt := h.length_le.eq_or_lt
  · exact eq_of_length h heq ▸ refl _
  rw [prefix_iff_eq_take.mp h, dropLast_take hlt, dropLast_eq_take]
  exact take_prefix_take_left (by grind)

@[gcongr] lemma IsSuffix.dropLast {α} {l₁ l₂ : List α} (h : l₁ <:+ l₂) :
    l₁.dropLast <:+ l₂.dropLast := by
  rw [← reverse_prefix, ← tail_reverse, ← tail_reverse]
  exact h.reverse.tail

@[gcongr] lemma IsSuffix.drop {α} {l₁ l₂ : List α} (h : l₁ <:+ l₂) (n : ℕ) :
    l₁.drop n <:+ l₂.drop n := by
  rw [suffix_iff_eq_drop.mp h, drop_drop]
  exact drop_suffix_drop_left l₂ (by omega)

@[gcongr] lemma IsSuffix.tail {α} {l₁ l₂ : List α} (h : l₁ <:+ l₂) : l₁.tail <:+ l₂.tail := by
  convert h.drop 1 using 1 <;> exact drop_one.symm

lemma isChain_iff_all_zip_tail {α} (r : α → α → Prop) (l : List α) :
    l.IsChain r ↔ ∀ x ∈ l.zip l.tail, r x.1 x.2 := by
  induction l with | nil => simp | cons a l ih => cases l <;> simp [ih]

@[simp]
lemma isChain_and_iff {α} (r s : α → α → Prop) (l : List α) :
    l.IsChain (fun x y ↦ r x y ∧ s x y) ↔ l.IsChain r ∧ l.IsChain s := by
  match l with | [] => simp | [a] => simp | a :: b :: as => _
  simp_rw [isChain_cons_cons, isChain_and_iff]
  tauto


variable {e f x : α} {b c d : Bool} {L : List α}

lemma findIdxs_sublist_range (xs : List α) (p : α → Bool) :
    findIdxs p xs <+ range xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    suffices aux : 0 :: map (fun x ↦ x + 1) (findIdxs p xs) <+ range ((xs).length + 1) by
      rw [findIdxs_cons, zero_add, findIdxs_start]
      split_ifs
      · assumption
      exact Sublist.trans (by simp) aux
    exact ((ih.map _).cons_cons 0 ).trans <| by rw [range_succ_eq_map]

@[simp]
lemma findIxs_length (xs : List α) (p : α → Bool) :
    (findIdxs p xs).length = (xs.filter p).length := by
  have hz := unzip_findIdxsValues (p := p) (xs := xs) (s := 0)
  simp only [unzip_eq_map, Prod.mk.injEq] at hz
  rw [← congr_arg length hz.1, ← congr_arg length hz.2, length_map, length_map]

lemma range_three : List.range 3 = [0, 1, 2] := rfl

lemma range_add_one {n : ℕ} : range (n + 1) = range n ++ [n] := range_succ

lemma range'_suffix_add (a b : ℕ) : List.range' a b <:+ range (a + b) := by
  rw [range_add, range'_eq_map_range]
  apply suffix_append

lemma range'_suffix (a b : ℕ) : List.range' a (b - a) <:+ range b := by
  obtain hlt | hle := lt_or_ge b a
  · grind
  have := add_tsub_cancel_of_le hle ▸ range'_suffix_add a (b - a)
  assumption

lemma range_prefix {a b} (hab : a ≤ b) : range a <+: range b := by
  obtain ⟨d, hd, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [range_add]
  apply prefix_append

lemma range'_sub_infix (a : ℕ) {b n : ℕ} (hbn : b ≤ n) : range' a (b - a) <:+: range n :=
  (range'_suffix a b).isInfix.trans (range_prefix hbn).isInfix

lemma range'_infix {a b n} (h : a + b ≤ n) : range' a b <:+: range n :=
  (range'_suffix_add ..).isInfix.trans (range_prefix h).isInfix

-- lemma map_add_range'_sub (a b d : ℕ) : (range' a (b - a)).map (· + d) =
--     range' (a + d) (b + d - a) := by
--   sorry

@[simp]
lemma map_toFinset {α β : Type*} [DecidableEq α] [DecidableEq β] (L : List α) (f : α → β) :
    (L.map f).toFinset = L.toFinset.image f := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma map_toFinset_embedding {α β : Type*} [DecidableEq α] [DecidableEq β]
    (L : List α) (f : α ↪ β) : (L.map f).toFinset = L.toFinset.map f := by
  induction L with simp_all

-- lemma range'_sub_infix_range'_sub {a a' b b' : ℕ} (ha : a ≤ a') (hb : b' ≤ b) :
--     range' a' (b' - a') <:+: range' a (b - a) := by

  -- (range'_suffix a b).isInfix.trans (range_prefix hbn).isInfix

lemma cons_range'_add_one (a b : ℕ) : a :: range' (a + 1) b = range' a (b + 1) := rfl

lemma cons_range'_sub_add_one {a b : ℕ} (hab : a < b) :
    a :: range' (a + 1) (b - (a + 1)) = range' a (b - a) := by
  grind [cons_range'_add_one]

lemma range'_sub_add_one {a b : ℕ} (hab : a ≤ b) :
    range' a (b + 1 - a) = range' a (b - a) ++ [b] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [show a + d + 1 - a = d + 1 by grind, show a + d - a = d by grind]
  simp [← range'_append_1]

lemma prefix_suffix_sublist {A B L : List α} (hA : A <+: L) (hB : B <:+ L)
    (hAB : A.length + B.length ≤ L.length) : A ++ B <+ L := by
  induction A generalizing L with
  | nil => simpa using hB.sublist
  | cons x A ih =>
    obtain ⟨L, rfl, hAL⟩ := cons_prefix_iff.1 hA
    rw [cons_append]
    obtain rfl | hBL := suffix_cons_iff.1 hB
    · simp at hAB
    exact (ih hAL hBL (by grind)).cons_cons x

lemma exists_eq_or_eq_concat_of_sublist_range_add_one {L : List ℕ} {n : ℕ}
    (h : L <+ range (n + 1)) : ∃ L₀, L₀ <+ range n ∧ (L = L₀ ∨ L = L₀ ++ [n]) := by
  rw [range_add_one, sublist_append_iff] at h
  obtain ⟨L₁, L₂, h1, h2, h3⟩ := h
  refine ⟨L₁, h2, ?_⟩
  obtain rfl | rfl := by simpa using h3
  · simp [h1]
  simp[ h1]

lemma zipIdx_take (L : List α) (k i : ℕ) : (L.zipIdx i).take k = (L.take k).zipIdx i := by
  induction k generalizing L i with
  | zero => simp
  | succ k ih => cases L with simp_all


lemma Subset.toFinset_subset [DecidableEq α] {a b : List α} (hab : a ⊆ b) :
    a.toFinset ⊆ b.toFinset :=
  fun i hi ↦ by simpa using hab <| by simpa using hi

@[simp]
lemma toFinset_range (n : ℕ) : (range n).toFinset = Finset.range n := by
  ext
  simp

lemma setOf_two {a b : α} : {x | x ∈ [a, b]} = {a, b} := by
  ext; simp

lemma setOf_three {a b c : α} : {x | x ∈ [a, b, c]} = {a, b, c} := by
  ext; simp

lemma setOf_four {a b c d : α} : {x | x ∈ [a, b, c, d]} = {a, b, c, d} := by
  ext; simp

theorem getElem_reverse' {l : List α} {i j : ℕ} (hij : i + j + 1 = l.length) :
    l.reverse[i]'(by rw [length_reverse]; lia) = l[j] := by
  simp_rw [getElem_reverse, ← hij]
  convert rfl
  lia

-- Variant of getElem?_reverse with a hypothesis giving the linear relation between the indices.
