import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.SplitBy
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.Induction

namespace List

variable {α : Type*}

lemma Nodup.countP_eq_card {α} {l : List α} {P : α → Prop} [DecidableEq α] [DecidablePred P]
    (h : l.Nodup) : countP P l = (l.toFinset.filter P).card := by
  rw [countP_eq_length_filter, ← toFinset_card_of_nodup (h.filter ..)]
  simp

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

lemma mem_dropLast_iff {ι} {x : ι} {l : List ι} (hnd : l.Nodup) (hne : l ≠ []) :
    x ∈ l.dropLast ↔ x ∈ l ∧ x ≠ l.getLast hne := by
  obtain rfl | ⟨l', y, rfl⟩ := l.eq_nil_or_concat
  · simp at hne
  simp only [concat_eq_append, nodup_append, nodup_cons, not_mem_nil, not_false_eq_true, nodup_nil,
    and_self, mem_cons, or_false, ne_eq, forall_eq, true_and] at hnd
  simp only [concat_eq_append, ne_eq, cons_ne_self, not_false_eq_true, dropLast_append_of_ne_nil,
    dropLast_singleton, append_nil, mem_append, mem_cons, not_mem_nil, or_false,
    getLast_append_of_ne_nil, getLast_singleton]
  refine ⟨fun h => ?_, fun h => h.1.elim id (h.2 · |>.elim)⟩
  simp [h, hnd.2 x h]

lemma mem_dropLast_of_mem_ne {ι} {x : ι} {l : List ι} (hne : l ≠ []) (hmem : x ∈ l)
    (hxne : x ≠ l.getLast hne) : x ∈ l.dropLast := by
  obtain rfl | ⟨l', y, rfl⟩ := l.eq_nil_or_concat
  · simp at hne
  simp_all

lemma op_foldl_eq_foldl_op_of_assoc {α} {f : α → α → α} [Std.Associative f] :
    ∀ a b l, (foldl f (f a b) l) = f a (foldl f b l)
  | _, _, nil => rfl
  | a, b, c :: l => by
    simp only [foldl_cons]
    simp_rw [Std.Associative.assoc a b c]
    rw [op_foldl_eq_foldl_op_of_assoc ..]

lemma Nodup.eq_singleton_iff_head_getLast {α} {l : List α} (hnd : l.Nodup) (hne : l ≠ []) :
    l.head hne = l.getLast hne ↔ ∃ x, l = [x] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · match l with
  | [] => simp at hne
  | head :: tail =>
    simp only [head_cons, nodup_cons, cons.injEq] at h hnd ⊢
    by_contra! htail
    simp_all
  obtain ⟨x, rfl⟩ := h
  simp

lemma IsSuffix.eq_of_first_mem {α} {l₁ l₂ : List α} (h : l₁.IsSuffix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.head hne ∈ l₁) : l₁ = l₂ := by
  match h with | .intro w h => ?_
  subst l₂
  rw [self_eq_append_left]
  match w with
  | [] => rfl
  | a :: as => simp_all

lemma IsPrefix.eq_of_last_mem {α} {l₁ l₂ : List α} (h : l₁.IsPrefix l₂) (hnd : l₂.Nodup)
    (hne : l₂ ≠ []) (hl : l₂.getLast hne ∈ l₁) : l₁ = l₂ := by
  simpa using h.reverse.eq_of_first_mem (by simpa) (by simpa) (by simpa)

lemma isChain_iff_all_zip_tail {α} (r : α → α → Prop) (l : List α) :
    l.IsChain r ↔ ∀ x ∈ l.zip l.tail, r x.1 x.2 := by
  induction l with | nil => simp | cons a l ih => cases l with | nil => simp | cons b t => simp [ih]

@[simp]
lemma isChain_and_iff {α} (r s : α → α → Prop) (l : List α) :
    l.IsChain (fun x y ↦ r x y ∧ s x y) ↔ l.IsChain r ∧ l.IsChain s := by
  match l with
  | [] => simp
  | [a] => simp
  | a :: b :: as =>
    simp only [isChain_cons_cons]
    rw [isChain_and_iff]
    tauto

@[simp]
theorem splitBy_singleton (r : α → α → Bool) (a : α) : splitBy r [a] = [[a]] :=
  rfl

private theorem splitByLoop_eq_append {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (gs : List (List α)) : splitBy.loop r l a g gs = gs.reverse ++ splitBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    simp_rw [splitBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp

@[simp]
theorem splitBy_eq_nil_iff (r : α → α → Bool) (l : List α) : l.splitBy r = [] ↔ l = [] := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  simpa using congrArg flatten h

private theorem splitByLoop_ne_nil {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    splitBy.loop r l a g [] ≠ [] := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    unfold splitBy.loop
    split
    · simp [IH]
    rw [splitByLoop_eq_append]
    simp

private theorem nil_notMem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    [] ∉ splitBy.loop r l a g [] := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · exact IH
    · rw [splitByLoop_eq_append, mem_append]
      simpa using IH

@[simp]
theorem splitBy_cons_cons_of_not_rel {r : α → α → Bool} {a b : α} (l : List α) (h : ¬r a b) :
    (a :: b :: l).splitBy r = [a] :: (b :: l).splitBy r := by
  unfold splitBy
  conv_lhs => simp [splitBy.loop, h]
  rw [splitByLoop_eq_append]
  rfl

private theorem splitByLoop_eq_cons {r : α → α → Bool} {l : List α} {a b : α} {g : List α} :
    splitBy.loop r l b (g ++ [a]) [] = (a :: (splitBy.loop r l b g []).head splitByLoop_ne_nil) ::
    ((splitBy.loop r l b g []).tail) := by
  induction l generalizing b g with
  | nil => simp [splitBy.loop]
  | cons c l IH =>
    conv_lhs => unfold splitBy.loop
    split <;> rename_i hbc <;> conv_rhs => simp only [splitBy.loop, hbc, reverse_cons]
    · rw [← cons_append, IH]
    rw [splitByLoop_eq_append]
    simp only [reverse_cons, reverse_append, reverse_nil, nil_append, cons_append, cons.injEq,
      true_and]
    constructor
    · change ([g.reverse ++ [b]].reverse ++ (splitBy.loop r l c [] [])).head (by simp) = _
      congr 1
      exact (splitByLoop_eq_append _).symm
    rw [splitByLoop_eq_append [g.reverse ++ [b]]]
    simp

private theorem splitByLoop_eq_reverse_append {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    splitBy.loop r l a g [] = (g.reverse ++ (splitBy.loop r l a [] []).head splitByLoop_ne_nil) ::
    ((splitBy.loop r l a [] [])).tail := by
  set g' := g.reverse with hg'
  rw [(show g = g'.reverse from reverse_eq_iff.mp hg')]
  induction g' with
  | nil => simp
  | cons b g IH => simp [splitByLoop_eq_cons, IH]

@[simp]
theorem splitBy_cons_cons_of_rel {r : α → α → Bool} {a b : α} (l : List α) (h : r a b) :
    (a :: b :: l).splitBy r = match (b :: l).splitBy r with
      | [] => []
      | m :: ms => (a :: m) :: ms := by
  match hs : (b :: l).splitBy r with
  | nil => simp at hs
  | cons m ms =>
    simp only [splitBy, splitBy.loop, h] at hs ⊢
    simp [splitByLoop_eq_reverse_append, hs]

theorem foo {r : α → α → Bool} {a b : α} {l m : List α} {ms : List (List α)}
    (h : r a b) (heq : (b :: l).splitBy r = m :: ms) :
    (a :: b :: l).splitBy r = (a :: m) :: ms := by
  simpa [heq] using splitBy_cons_cons_of_rel l h

theorem bar (r : α → α → Bool) (a : α) (l : List α) :
    ∃ m ms, (a :: l).splitBy r = (a :: m) :: ms := by
  induction l generalizing a with
  | nil =>
    use [], []
    simp
  | cons b l IH =>
    obtain ⟨m, ms, h⟩ := IH b
    by_cases hab : r a b
    · use b :: m, ms
      rw [splitBy_cons_cons_of_rel _ hab, h]
    · use [], (b :: m) :: ms
      rw [splitBy_cons_cons_of_not_rel _ hab, h]

@[simp]
theorem splitBy_append_of_not_rel {r : α → α → Bool} {l₁ l₂ : List α} (hl₁ : l₁ ≠ [])
    (hl₂ : l₂ ≠ []) (h : ¬r (l₁.getLast hl₁) (l₂.head hl₂)) :
    (l₁ ++ l₂).splitBy r = (l₁.splitBy r) ++ (l₂.splitBy r) := by
  match l₁ with
  | [] => simp
  | [a] =>
    simp only [getLast_singleton, Bool.not_eq_true, cons_append, nil_append] at h ⊢
    conv_lhs => rw [← cons_head_tail hl₂]
    rw [splitBy_cons_cons_of_not_rel _ (by simpa)]
    simp
  | a :: b :: as =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, Bool.not_eq_true,
      cons_append] at h ⊢
    by_cases hab : r a b
    · match hs : (b :: as).splitBy r with
      | nil => simpa using (splitBy_eq_nil_iff r (b :: as)).1 (by simp [hs])
      | cons m ms =>
        rw [splitBy_cons_cons_of_rel (as ++ l₂) hab, splitBy_cons_cons_of_rel as hab]
        have IH : ((b :: as) ++ l₂).splitBy r = (b :: as).splitBy r ++ l₂.splitBy r :=
          splitBy_append_of_not_rel (by simp) hl₂ (by simpa using h)
        simp only [cons_append, hs] at IH
        simp [hs, IH]
    · rw [splitBy_cons_cons_of_not_rel _ hab, splitBy_cons_cons_of_not_rel _ hab, ← cons_append,
        splitBy_append_of_not_rel (by simp) hl₂ (by simpa), cons_append]

-- theorem splitBy_of_isChain {r : α → α → Bool} {l : List α} (hc : l.IsChain (r · ·))
-- (hne : l ≠ []) :
--     splitBy r l = [l] := by
--   match l, hne with
--   | [a], _ => simp
--   | a :: b :: as, _ =>
--     rw [isChain_cons_cons] at hc
--     obtain ⟨m, ms, hm⟩ := bar r b as
--     obtain ⟨rfl, rfl⟩ : as = m ∧ ms = [] := by simpa [splitBy_of_isChain hc.2] using hm
--     rw [foo hc.1 hm]

-- theorem splitBy_of_mem_splitBy {r : α → α → Bool} {l l' : List α} (h : l ∈ splitBy r l') :
--     splitBy r l = [l] :=
--   splitBy_of_isChain (isChain_of_mem_splitBy h) (ne_nil_of_mem_splitBy h)

-- theorem splitBy_flatten_of_cons {r : α → α → Bool} {l l' : List α} {L : List (List α)}
--     (h : splitBy r l = l' :: L) : L.flatten.splitBy r = L := by
--   match l with
--   | nil => simp at h
--   | [a] =>
--     obtain rfl | rfl := (by simpa only [splitBy_singleton, infix_singleton_iff] using h)
--     simp
--   | a :: b :: as =>
--     obtain ⟨m, ms, hm⟩ := bar r b as
--     by_cases hab : r a b
--     · obtain ⟨rfl, rfl⟩ : _ = l' ∧ ms = L := by simpa [foo hab hm] using h
--       exact splitBy_flatten_of_cons hm
--     · obtain ⟨rfl, rfl⟩ : [a] = l' ∧ _ = L := by simpa [splitBy_cons_cons_of_not_rel _ hab]
-- using h
--       rw [flatten_splitBy]

-- theorem splitBy_flatten_of_prefix {r : α → α → Bool} {l : List α} {L : List (List α)}
--     (h : L <+: splitBy r l) : L.flatten.splitBy r = L := by
--   match l with
--   | nil =>
--     obtain rfl := by simpa using h
--     simp
--   | [a] =>
--     obtain rfl | rfl := (by simpa only [splitBy_singleton, infix_singleton_iff] using h.isInfix)
--     <;> simp
--   | a :: b :: as =>
--     obtain ⟨m, ms, hm⟩ := bar r b as
--     by_cases hab : r a b
--     · have habms := foo hab hm
--       rw [habms, prefix_cons_iff] at h
--       obtain rfl | ⟨L', rfl, hl'⟩ := h
--       · simp
--       have hbm := splitBy_of_mem_splitBy  <| hm ▸ (by simp : (b :: m) ∈ ((b :: m) :: ms))
--       obtain rfl | hneL' := eq_or_ne L' []
--       · simp only [flatten_cons, flatten_nil, append_nil]
--         exact foo hab hbm
--       have hrec := splitBy_flatten_of_prefix <| (splitBy_flatten_of_cons hm) ▸ hl'
--       have hne_flat : L'.flatten ≠ [] := by
--         intro hflat
--         simp [hflat, hneL'] at hrec
--       have hboundary : ¬ r ((a :: b :: m).getLast (by simp)) ((L'.flatten).head hne_flat) := by
--         have := isChain_getLast_head_splitBy r (a :: b :: as)
--         rw [habms, ← cons_head_tail (by grind : ms ≠ [])] at this
--         obtain ⟨_, hmsh, hf⟩ := this.rel_head
--         simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, Bool.not_eq_true]
--         simp_rw [head_flatten_eq_head_head hne_flat (hl'.head hneL' ▸ hmsh), hl'.head hneL']
--         exact hf
--       rw [flatten_cons, splitBy_append_of_not_rel (by simp) hne_flat hboundary, hrec]
--       simp [foo hab hbm]
--     · rw [splitBy_cons_cons_of_not_rel _ hab, prefix_cons_iff] at h
--       obtain rfl | ⟨L', rfl, hl'⟩ := h
--       · simp
--       obtain rfl | hneL' := eq_or_ne L' []
--       · simp
--       have := splitBy_flatten_of_prefix hl'
--       have hne_flat : L'.flatten ≠ [] := by
--         intro hflat
--         simp [hflat, hneL'] at this
--       -- The head of `L'.flatten` is `b`, since `L'`
-- is a nonempty prefix of `(b :: as).splitBy r`.
--       have hboundary : ¬ r ([a].getLast (by simp)) ((L'.flatten).head hne_flat) := by
--         have := isChain_getLast_head_splitBy r (a :: b :: as)
--         rw [splitBy_cons_cons_of_not_rel _ hab, hm] at this
--         obtain ⟨_, hmsh, hf⟩ := this.rel_head
--         simp only [getLast_singleton, Bool.not_eq_true]
--         simp_rw [head_flatten_eq_head_head hne_flat (by simp [hl'.head hneL', hm]),
-- hl'.head hneL',
--           hm]
--         exact hf
--       rw [flatten_cons, splitBy_append_of_not_rel (by simp) hne_flat hboundary, this]
--       simp

-- theorem splitBy_flatten_of_infix {r : α → α → Bool} {l : List α} {L : List (List α)}
--     (h : L <:+: splitBy r l) : L.flatten.splitBy r = L := by
--   induction hl : splitBy r l generalizing l with
--   | nil =>
--     obtain rfl := by simpa [hl] using h
--     simp
--   | cons head tail IH =>
--     rw [hl, infix_cons_iff] at h
--     obtain hnil | htl := h
--     · exact splitBy_flatten_of_prefix <| hl ▸ hnil
--     · have htlf := splitBy_flatten_of_cons hl
--       exact IH (htlf.symm ▸ htl) htlf

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

/-- Take every other element of a list `L`,
with the `Bool` indicating whether to take the first element.-/
def alt : List α → Bool → List α
  | [], _ => []
  | x :: L, true => x :: alt L false
  | _ :: L, false => alt L true

@[simp]
lemma alt_empty (b) : List.alt ([] : List α) b = [] := rfl

@[simp]
lemma alt_cons_true (L : List α) (x : α) : (x :: L).alt true = x :: L.alt false := rfl

@[simp]
lemma alt_cons_false (L : List α) (x : α) : (x :: L).alt false = L.alt true := rfl

lemma alt_cons (L : List α) (x : α) (b : Bool) :
    (x :: L).alt b = bif b then x :: L.alt (!b) else L.alt (!b) := by
  cases b <;> simp

lemma alt_length_add (L : List α) : (L.alt true).length + (L.alt false).length = L.length := by
  induction L with
  | nil => simp
  | cons a L ih => grind [alt_cons_true, alt_cons_false, ih.symm]

lemma alt_true_length_eq (L : List α) :
    (L.alt true).length = (L.alt false).length + (if Odd L.length then 1 else 0) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [alt_cons_true, length_cons, alt_cons_false, ih, Nat.odd_add_one]
    grind

lemma length_alt (L : List α) :
    L.length = 2 * (L.alt false).length + (if (Odd L.length) then 1 else 0) := by
  grind [L.alt_length_add, L.alt_true_length_eq]

@[simp]
lemma alt_getElem (L : List α) (b : Bool) (i : ℕ) (hi : i < (L.alt b).length) :
    (L.alt b)[i] = L[2 * i + (bif b then 0 else 1)]'
      (by cases b <;> grind [L.alt_true_length_eq, L.length_alt]) := by
  induction L generalizing b i with
  | nil => simp at hi
  | cons => cases b with cases i with simp_all [Nat.mul_add]

@[simp]
lemma alt_head_cons_cons (L : List α) : ((e :: f :: L).alt d).head (by cases d <;> simp) =
    bif d then e else f := by
  cases d <;> simp

lemma alt_head_cons (L : List α) {h : ((e :: L).alt d) ≠ []} : ((e :: L).alt d).head h =
    d.dcond (fun _ ↦ e) (fun hd ↦ L.head (fun hF ↦ by simp [hF, hd] at h)) := by
  cases L with | _ => cases d <;> simp_all [Bool.dcond]

lemma alt_head {L : List α} {hF : L.alt d ≠ []} :
    (L.alt d).head hF = d.dcond (fun _ ↦ L.head (by rintro rfl; simp at hF))
      (fun hd ↦ L[1]'(by
        subst hd
        match L with
        | [] => simp at hF
        | [x] => simp at hF
        | _ :: _ :: F => simp)) := by
  match L with
  | [] => simp at hF
  | e :: F =>
    rw [F.alt_head_cons]
    cases d <;>
    simp [Bool.dcond, getElem_zero]

lemma mem_iff_exists_mem_alt (L : List α) : x ∈ L ↔ ∃ i, x ∈ L.alt i := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [mem_cons, ih, Bool.exists_bool, alt_cons_false, alt_cons_true]
    grind

lemma alt_sublist (L : List α) (b : Bool) : (L.alt b) <+ L := by
  induction L generalizing b with
  | nil => simp
  | cons a L ih =>
    cases b
    · exact (ih true).trans <| sublist_cons_self ..
    simpa using ih false

lemma Nodup.alt_disjoint (hF : L.Nodup) : Disjoint (L.alt false) (L.alt true) := by
  induction hF with
  | nil => simp
  | @cons a L h1 h2 hdj =>
    simp [show a ∉ L.alt true from fun hmem ↦ h1 a ((L.alt_sublist true).mem hmem) rfl, hdj.symm]

lemma alt_concat (L : List α) (x : α) (b : Bool) :
    (L.concat x).alt b = bif L.length.bodd == b then L.alt b else (L.alt b).concat x := by
  induction L generalizing b with cases b <;> simp_all [Bool.apply_cond]

lemma alt_reverse (L : List α) (b : Bool) :
    (L.alt b).reverse = L.reverse.alt (b == L.length.bodd) := by
  induction L generalizing b with cases b <;> simp_all [← List.concat_eq_append, List.alt_concat]

lemma reverse_alt (L : List α) (b : Bool) :
    L.reverse.alt b = (L.alt (bif L.length.bodd then b else !b)).reverse := by
  cases b <;> simp [L.alt_reverse]

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

-- #check List.idx

variable [DecidableEq α] {P : ℕ → Bool}

/-- Given a list `L`, and a predicate on the indices.
returns the finset of elements of `L` whose indices satisfy the predicate.
Indices out of bounds are ignored. -/
def getFinset (L : List α) (P : ℕ → Bool) : Finset α :=
  ((L.zipIdx.filter (fun x ↦ P x.2)).map Prod.fst).toFinset

@[simp]
lemma getFinset_nil : ([] : List α).getFinset P = {} := by
  simp [getFinset]

lemma getFinset_cons_pos {a : α} (h0 : P 0) :
    (a :: L).getFinset P = insert a (L.getFinset (fun i ↦ P (i + 1))) := by
  simp only [getFinset, zipIdx_cons', h0, filter_cons_of_pos, map_cons, toFinset_cons,
    map_toFinset, toFinset_filter]
  ext x
  simp

lemma getFinset_cons_neg {a : α} (h0 : ¬ P 0) :
    (a :: L).getFinset P = L.getFinset (fun i ↦ P (i + 1)) := by
  simp only [getFinset, zipIdx_cons',  toFinset_cons,
    map_toFinset, toFinset_filter, Finset.filter_insert, h0, Bool.false_eq_true, ↓reduceIte]
  ext
  simp

@[simp]
lemma getFinset_cons {a : α} : (a :: L).getFinset P = bif P 0 then
    insert a (L.getFinset (fun i ↦ P (i + 1))) else (L.getFinset (fun i ↦ P (i + 1))) := by
  by_cases h0 : P 0
  · rw [getFinset_cons_pos h0]
    simp [h0]
  rw [getFinset_cons_neg h0]
  simp [h0]

lemma getFinset_concat_pos {a : α} (hP : P L.length) :
    (L ++ [a]).getFinset P = insert a (L.getFinset P) := by
  induction L generalizing P with
  | nil => simp [show P 0 by simpa using hP]
  | cons b L ih => rw [getFinset_cons, cons_append, getFinset_cons, ih (by simpa),
      Finset.insert_comm, ← Bool.apply_cond]

lemma getFinset_concat_neg {a : α} (hP : ¬P L.length) :
    (L ++ [a]).getFinset P = L.getFinset P := by
  induction L generalizing P with
  | nil => simp [show ¬ P 0 by simpa using hP]
  | cons b L ih => rw [getFinset_cons, cons_append, getFinset_cons, ih (by simpa using hP)]

lemma getFinset_concat {a : α} :
    (L ++ [a]).getFinset P = bif P L.length then insert a (L.getFinset P) else L.getFinset P := by
  by_cases h : P L.length
  · rw [getFinset_concat_pos h]
    simp [h]
  rw [getFinset_concat_neg h]
  simp [h]

@[simp]
lemma getFinset_singleton_eq_cond {a : α} : [a].getFinset P = bif P 0 then {a} else {} := by
  simp [getFinset_cons]

lemma getFinset_subset (L : List α) (P : ℕ → Bool) : L.getFinset P ⊆ L.toFinset := by
  induction L generalizing P with
  | nil => simp
  | cons a L ih =>
    by_cases h0 : P 0
    · grw [getFinset_cons_pos h0, toFinset_cons, ih]
    grw [getFinset_cons_neg h0, ih, toFinset_cons, ← Finset.subset_insert]

@[simp]
lemma mem_getFinset_iff {a} :
    a ∈ L.getFinset P ↔ ∃ (i : ℕ) (hi : i < L.length), P i ∧ L[i] = a := by
  induction L using List.reverseRecOn generalizing P with
  | nil => simp
  | append_singleton L b ih =>
    by_cases h : P L.length
    · rw [getFinset_concat_pos h, Finset.mem_insert, ih]
      grind
    rw [getFinset_concat_neg h]
    grind

lemma getFinset_mono (L : List α) {P Q : ℕ → Bool} (hPQ : ∀ i, P i → Q i) :
    L.getFinset P ⊆ L.getFinset Q := by
  simp only [Finset.subset_iff, mem_getFinset_iff, exists_and_left, forall_exists_index, and_imp]
  rintro a i ha hi rfl
  exact ⟨i, hPQ i ha, hi, rfl⟩

@[simp]
lemma getFinset_finset_insert {i : ℕ} (F : Finset ℕ) (hi : i < L.length) :
    (L.getFinset (· ∈ insert i F)) = insert (L[i]) (L.getFinset (· ∈ F)) := by
  induction L using List.reverseRecOn generalizing F with
  | nil => simp at hi
  | append_singleton L b IH => grind [mem_getFinset_iff]

lemma getFinset_false (hP : ∀ i < L.length, P i = false) : L.getFinset P = {} := by
  induction L generalizing P with
  | nil => simp
  | cons a L ih => rw [getFinset_cons_neg (by grind), ih (by grind)]

lemma getFinset_finset_mono (L : List α) {F G : Finset ℕ} (hFG : F ⊆ G) :
    L.getFinset (· ∈ F) ⊆ L.getFinset (· ∈ G) :=
  getFinset_mono _ <| by simpa using Finset.subset_iff.1 hFG

lemma Nodup.getFinset_card (hnd : L.Nodup) {F : Finset ℕ}
    (hF : F ⊆ Finset.range L.length) : (L.getFinset (· ∈ F)).card = F.card := by
  induction F using Finset.induction with
  | empty => rw [getFinset_false (by simp), Finset.card_empty, Finset.card_empty]
  | insert a s has ih =>
    rw [Finset.insert_subset_iff, Finset.mem_range] at hF
    rw [getFinset_finset_insert _ hF.1, Finset.card_insert_of_notMem has,
      Finset.card_insert_of_notMem, ih hF.2]
    grind [hnd.getElem_inj_iff, mem_getFinset_iff]


-- @[simp]
-- lemma Nodup.getFinset_inter (hL : L.Nodup) (F G : Finset ℕ) :
--     L.getFinset (· ∈ F ∩ G) = L.getFinset (· ∈ F) ∩ L.getFinset (· ∈ G) := by
--   ext a
--   simp only [Finset.mem_inter, Bool.decide_and, mem_getFinset_iff, Bool.and_eq_true,
--     decide_eq_true_eq, exists_and_left]
--   constructor
--   · rintro ⟨i, ⟨hiF, hiG⟩, hi, rfl⟩
--     exact ⟨⟨i, hiF, hi, rfl⟩, i, hiG, hi, rfl⟩
--   rintro ⟨⟨i, hiF, hi, rfl⟩, j, hjG, hj, h'⟩
--   have := hL.injective_get
--   #check List.get
