import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.SplitBy
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Bits
import Mathlib.Data.List.Induction
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.Interval
import Mathlib.Algebra.Order.Interval.Set.SuccPred

namespace List

open Set

variable {α : Type*} {l : List α}

lemma toSet_cons_eq {a : α} : {x | x ∈ a :: l} = insert a {x | x ∈ l} := by
  simp [Set.ext_iff]

lemma toSet_concat_eq {a : α} : {x | x ∈ l ++ [a]} = insert a {x | x ∈ l} := by
  simp [Set.ext_iff, or_comm]

lemma toSet_append_eq {l' : List α} : {x | x ∈ l ++ l'} = {x | x ∈ l} ∪ {x | x ∈ l'} := by
  simp [Set.ext_iff]

lemma Nodup.toSet_tail_eq (hl : l.Nodup) (h0 : l ≠ []) :
    {x | x ∈ l.tail} = {x | x ∈ l} \ {l.head h0} := by
  nth_rw 2 [← cons_head_tail h0]
  rw [toSet_cons_eq, Set.insert_sdiff_self_of_notMem]
  cases hl with grind

lemma Nodup.toSet_dropLast_eq (hl : l.Nodup) (h0 : l ≠ []) :
    {x | x ∈ l.dropLast} = {x | x ∈ l} \ {l.getLast h0} := by
  have := (nodup_reverse.2 hl).toSet_tail_eq (by simpa)
  simp only [tail_reverse, mem_reverse, head_reverse] at this
  assumption

lemma getElem_mem_dropLast {i} (hi : i < l.length - 1) : l[i] ∈ l.dropLast := by
  rw [← l.getElem_dropLast (by simpa using hi)]
  exact getElem_mem ..

lemma subset_of_subset_setOf_of_forall {s t : Set α} (hs : s ⊆ {x | x ∈ l})
    (hst : ∀ i (hi : i < l.length), l[i] ∈ s → l[i] ∈ t) : s ⊆ t := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem <| hs hx
  exact hst i hi hx

lemma eq_of_subset_setOf_of_forall {s t : Set α} (hs : s ⊆ {x | x ∈ l}) (ht : t ⊆ {x | x ∈ l})
    (hst : ∀ i (hi : i < l.length), l[i] ∈ s ↔ l[i] ∈ t) : s = t :=
  (subset_of_subset_setOf_of_forall hs (by grind)).antisymm <|
    (subset_of_subset_setOf_of_forall ht (by grind))

@[simp]
lemma toSet_nonempty_iff : {x | x ∈ l}.Nonempty ↔ l ≠ [] := by
  cases l with
  | nil => simp
  | cons head tail =>
    rw [toSet_cons_eq]
    simp

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

@[simp] theorem splitBy_singleton (r : α → α → Bool) (a : α) : splitBy r [a] = [[a]] := rfl

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
--         obtain ⟨_, hmsh, hf⟩ := this.rel
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
--         obtain ⟨_, hmsh, hf⟩ := this.rel
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

lemma extract_zero (L : List α) (stop : ℕ) : L.extract 0 stop = L.take stop := by
  simp

lemma extract_zero_right (L : List α) (a : ℕ) : L.extract a 0 = [] := by
  simp

lemma extract_of_length_le (L : List α) (start : ℕ) {stop : ℕ} (h : L.length ≤ stop) :
    L.extract start stop = L.drop start := by
  obtain hle | hgt := le_or_gt start stop
  · simpa [Nat.sub_add_cancel hle]
  simp only [extract_eq_take_drop, take_eq_self_iff, length_drop, tsub_le_iff_right]
  grw [Nat.sub_eq_zero_of_le hgt.le, zero_add, ← hgt, h]

lemma extract_eq_nil (L : List α) {start stop : ℕ} (hlt : stop ≤ start) :
    L.extract start stop = [] := by
  grind [extract_eq_take_drop, take_eq_nil_iff, drop_eq_nil_iff]

lemma extract_succ_cons (L : List α) (x : α) (a b : ℕ) :
    (x :: L).extract (a + 1) (b + 1) = L.extract a b := by
  rw [extract_eq_drop_take', take_succ_cons, drop_succ_cons, extract_eq_drop_take']

lemma map_extract {β : Type*} (L : List α) (f : α → β) (a b : ℕ) :
    (L.extract a b).map f = (L.map f).extract a b := by
  simp

lemma mem_extract_iff_getElem {L : List α} {p q : ℕ} :
    x ∈ L.extract p q ↔ ∃ (i : ℕ) (hi : i < L.length), p ≤ i ∧ i < q ∧ L[i] = x := by
  simp only [extract_eq_take_drop, mem_take_iff_getElem, getElem_drop, length_drop, lt_inf_iff,
    exists_and_left]
  refine ⟨by grind, ?_⟩
  rintro ⟨i, hpi, hiq, hi, rfl⟩
  obtain ⟨d, rfl⟩ := exists_add_of_le hpi
  grind

@[simp]
lemma Nodup.getElem_mem_extract_iff (hL : L.Nodup) {i p q : ℕ} {hi : i < L.length} :
    L[i] ∈ L.extract p q ↔ p ≤ i ∧ i < q := by
  simp [mem_extract_iff_getElem, hL.getElem_inj_iff, hi]

lemma extract_min_right (L : List α) (p q : ℕ) :
    L.extract p (min q L.length) = L.extract p q := by
  obtain hq | hq := le_or_gt q L.length
  · rw [min_eq_left hq]
  rw [extract_eq_drop_take', take_of_length_le (by lia), extract_eq_drop_take',
    take_of_length_le (by lia)]

lemma extract_min_left (L : List α) (p q : ℕ) :
    L.extract (min p L.length) q = L.extract p q := by
  obtain hp | hp := le_or_gt p L.length
  · rw [min_eq_left hp]
  rw [← extract_min_right, extract_eq_nil _ (by lia), ← extract_min_right,
    extract_eq_nil _ (by lia)]

lemma extract_min_min (L : List α) (p q : ℕ) :
    L.extract (min p L.length) (min q L.length) = L.extract p q := by
  rw [extract_min_left, extract_min_right]

lemma extract_reverse (L : List α) (p q : ℕ) :
    L.reverse.extract p q = (L.extract (L.length - q) (L.length - p)).reverse := by
  wlog hq : p ≤ L.length ∧ q ≤ L.length generalizing p q with aux
  · rw [← extract_min_min, aux _ _ (by simp), length_reverse]
    convert rfl using 3 <;> lia
  rw [eq_comm, extract_eq_drop_take', reverse_drop, length_take, min_eq_left (by simp),
    show L.length - p - (L.length - q) = q - p by lia, reverse_take, Nat.sub_sub_self (by lia)]

lemma reverse_extract (L : List α) (p q : ℕ) :
    (L.extract p q).reverse = L.reverse.extract (L.length - q) (L.length - p) := by
  rw [eq_comm, extract_reverse, Nat.sub_sub_eq_min, Nat.sub_sub_eq_min, min_comm, min_comm _ q,
    extract_min_min]

lemma extract_add_one_right (L : List α) {p q : ℕ} (hpq : p ≤ q) (hq : q < L.length) :
    L.extract p (q + 1) = (L.extract p q) ++ [L[q]] := by
  induction L generalizing p q with
  | nil => simp at hq
  | cons x L ih =>
    obtain rfl | q := q
    · simp [show p = 0 by simpa using hpq]
    obtain rfl | p := p
    · simp
    rw [extract_succ_cons, extract_succ_cons, getElem_cons_succ, ih (by lia) (by grind)]

lemma cons_extract_add_one_left (L : List α) {p q : ℕ} (hpq : p < q) (hq : q ≤ L.length) :
    L[p] :: L.extract (p + 1) q = L.extract p q := by
  induction L generalizing p q with
  | nil => grind
  | cons x L ih =>
    obtain rfl | q := q
    · simp at hpq
    obtain rfl | p := p
    · simp
    rw [extract_succ_cons, extract_succ_cons, getElem_cons_succ, ih (by lia) (by grind)]

lemma zipIdx_take (L : List α) (k i : ℕ) : (L.zipIdx i).take k = (L.take k).zipIdx i := by
  induction k generalizing L i with
  | zero => simp
  | succ k ih => cases L with simp_all

/-- Take the elements of a list whose indices satisfy a certain predicate and (optionally)
belong to a certain subrange. -/
def filterIdx (L : List α) (p : ℕ → Bool) (start : ℕ := 0) (stop : ℕ := L.length) : List α :=
  ((L.zipIdx.extract start stop).filter fun x ↦ p x.2).map Prod.fst

@[simp]
lemma filterIdx_nil (p : ℕ → Bool) {start stop : ℕ} :
    ([] : List α).filterIdx p start stop = [] := by
  simp [filterIdx]

lemma filterIdx_eq (L : List α) (p : ℕ → Bool) :
    L.filterIdx p = (L.zipIdx.filter fun x ↦ p x.2).map Prod.fst := by
  simp [filterIdx, take_of_length_le]

lemma filterIdx_eq_nil (L : List α) (p : ℕ → Bool) {start stop : ℕ} (hle : stop ≤ start) :
    L.filterIdx p start stop = [] := by
  simp [filterIdx, extract_eq_nil _ hle]

lemma filterIdx_zero_left (L : List α) (p : ℕ → Bool) (stop : ℕ) :
    L.filterIdx p 0 stop = (L.take stop).filterIdx p := by
  rw [filterIdx, filterIdx_eq, List.extract_zero, zipIdx_take]

@[simp]
lemma filterIdx_zero_right (L : List α) (p : ℕ → Bool) (start : ℕ) :
    L.filterIdx p start 0 = [] := by
  simp [filterIdx]

@[simp]
lemma filterIdx_false (L : List α) (start stop : ℕ) :
    L.filterIdx (fun _ ↦ false) start stop = [] := by
  simp [filterIdx]

@[simp]
lemma filterIdx_true (L : List α) : L.filterIdx (fun _ ↦ true) = L := by
  simp [filterIdx]

lemma filterIdx_cons_pos (L : List α) (a : α) {p : ℕ → Bool} (hp : p 0 = true):
    (a :: L).filterIdx p = a :: (L.filterIdx (fun x ↦ p (x + 1))) := by
  rw [filterIdx_eq, filterIdx_eq]
  simp only [zipIdx_cons, zero_add, zipIdx_succ, hp, filter_cons_of_pos, filter_map, map_cons,
    map_map, cons.injEq, true_and]
  convert rfl <;> rfl

lemma filterIdx_cons_neg (L : List α) (a : α) {p : ℕ → Bool} (hp : p 0 = false):
    (a :: L).filterIdx p = L.filterIdx (fun x ↦ p (x + 1)) := by
  rw [filterIdx_eq, filterIdx_eq]
  simp only [zipIdx_cons, zero_add, zipIdx_succ, hp, Bool.false_eq_true, not_false_eq_true,
    filter_cons_of_neg, filter_map, map_map]
  convert rfl <;> rfl

lemma filterIdx_cons (L : List α) (a : α) (p : ℕ → Bool) :
    (a :: L).filterIdx p = bif p 0 then a :: (L.filterIdx (fun x ↦ p (x + 1)))
      else (L.filterIdx (fun x ↦ p (x + 1))) := by
  cases h : p 0 with
  | false => rw [filterIdx_cons_neg _ _ h, cond_false]
  | true => rw [filterIdx_cons_pos _ _ h, cond_true]

lemma filterIdx_cons_succ_succ (L : List α) (x : α) (p : ℕ → Bool) (a b : ℕ) :
    (x :: L).filterIdx p (a + 1) (b + 1) = L.filterIdx (fun x ↦ p (x + 1)) a b := by
  rw [filterIdx, zipIdx_cons', extract_succ_cons, filterIdx, ← map_extract, filter_map, map_map]
  convert rfl <;>
  simp [funext_iff]

lemma take_eq_filterIdx (L : List α) (b : ℕ) : L.take b = L.filterIdx (fun i ↦ i < b) := by
  induction b generalizing L with
  | zero => simp
  | succ b ih =>
    cases L with
    | nil => simp
    | cons a L =>
      rw [take_succ_cons, ih, length_cons, eq_comm, filterIdx_zero_left,
        take_of_length_le (by simp), filterIdx_cons_pos _ _ (by simp)]
      simp

lemma drop_eq_filterIdx (L : List α) (b : ℕ) : L.drop b = L.filterIdx (fun i ↦ b ≤ i) := by
  induction b generalizing L with
  | zero => simp
  | succ b ih =>
    cases L with
    | nil => simp
    | cons x L =>
      rw [drop_succ_cons, length_cons, filterIdx_zero_left, take_of_length_le (by simp),
        filterIdx_cons_neg _ _ (by simp), ih]
      simp

lemma extract_eq_filterIdx (L : List α) (a b : ℕ) :
    L.extract a b = L.filterIdx (fun i ↦ a ≤ i && i < b) := by
  induction b generalizing a L with
  | zero => simp
  | succ b ih =>
    cases L with
    | nil => simp
    | cons x L =>
      obtain rfl | a := a
      · simp only [extract_zero, take_succ_cons, zero_le, decide_true, Bool.true_and, length_cons]
        rw [filterIdx_zero_left, eq_comm, take_of_length_le (by simp),
          filterIdx_cons_pos _ _ (by simp), take_eq_filterIdx]
        simp
      rw [extract_eq_drop_take', take_succ_cons, drop_succ_cons, ← extract_eq_drop_take', ih,
        filterIdx_cons_neg _ _ (by simp)]
      simp

lemma filterIdx_length (L : List α) (p : ℕ → Bool) :
    (L.filterIdx p).length = ((range L.length).filter p).length := by
  rw [filterIdx_eq, length_map, range_eq_range', ← zipIdx_map_snd 0 L, ← length_map Prod.snd,
    filter_map]
  rfl

lemma filterIdx_congr (L : List α) {p q : ℕ → Bool} (start stop : ℕ)
    (h : ∀ i, start ≤ i → i < stop → p i = q i) :
    L.filterIdx p start stop = L.filterIdx q start stop := by
  rw [filterIdx, filterIdx, filter_congr]
  refine fun ⟨x, i⟩ hx ↦ ?_
  simp only [extract_eq_take_drop, mem_take_iff_getElem, getElem_drop, getElem_zipIdx, zero_add,
    Prod.mk.injEq, length_drop, length_zipIdx, lt_inf_iff, exists_and_right] at hx
  obtain ⟨j, ⟨⟨hj, hj'⟩, rfl⟩, rfl⟩ := hx
  grind

lemma filterIdx_map {β : Type*} (L : List α) (p : ℕ → Bool) (f : α → β) {a b : ℕ} :
    (L.filterIdx p a b).map f = (L.map f).filterIdx p a b := by
  induction L generalizing p a b with
  | nil => rw [filterIdx_nil, map_nil, filterIdx_nil]
  | cons x L ih =>
    obtain rfl | b := b
    · simp
    obtain rfl | a := a
    · specialize ih (fun i ↦ p (i + 1)) (a := 0) (b := b)
      rw [filterIdx_zero_left, eq_comm, filterIdx_zero_left] at ih
      rw [filterIdx_zero_left, take_succ_cons, map_cons, eq_comm, filterIdx_zero_left,
        take_succ_cons, filterIdx_cons, ih, filterIdx_cons]
      cases h : p 0 with simp
    rw [filterIdx_cons_succ_succ, ih, map_cons, filterIdx_cons_succ_succ]

lemma filterIdx_start_stop_eq (L : List α) (p : ℕ → Bool) (a b : ℕ) :
    L.filterIdx p a b = L.filterIdx (fun i ↦ p i && (a ≤ i && i < b)) := by
  induction L generalizing a b p with
  | nil =>
    simp
  | cons x L ih =>
    obtain rfl | b := b
    · simp
    obtain rfl | a := a
    · rw [filterIdx_zero_left, take_succ_cons, filterIdx_cons, ← filterIdx_zero_left, ih,
        filterIdx_cons]
      cases h : p 0 with simp
    rw [filterIdx_cons_succ_succ, ih, filterIdx_cons]
    simp



def getElems (L : List α) (s : Set ℕ) : Set α :=
  {x | ∃ (i : ℕ) (hi : i < L.length), i ∈ s ∧ L[i] = x}

@[simp]
lemma getElems_finite (L : List α) (s : Set ℕ) : (L.getElems s).Finite :=
  L.finite_toSet.subset <| by grind [getElems]

@[simp]
lemma nil_getElems (s : Set ℕ) : ([] : List α).getElems s = ∅ := by
  simp [getElems]

@[simp]
lemma getElems_empty (L : List α) : L.getElems ∅ = ∅ := by
  simp [getElems]

@[gcongr]
lemma getElems_mono (L : List α) {s t : Set ℕ} (hst : s ⊆ t) :
    L.getElems s ⊆ L.getElems t := by
  grind [getElems]

lemma mem_getElems {i : ℕ} {s : Set ℕ} (hi : i ∈ s) (hlt : i < L.length) : L[i] ∈ L.getElems s :=
  ⟨i, hlt, hi, rfl⟩

lemma getElems_union (L : List α) (s t : Set ℕ) :
    L.getElems (s ∪ t) = L.getElems s ∪ L.getElems t := by
  refine (Set.union_subset (getElems_mono _ (by simp)) (getElems_mono _ (by simp))).antisymm' ?_
  rintro _ ⟨i, hi, hi', rfl⟩
  exact Or.elim hi' (fun h ↦ .inl (mem_getElems h hi)) fun h ↦ .inr (mem_getElems h hi)

lemma getElems_singleton {i : ℕ} (hi : i < L.length) : L.getElems {i} = {L[i]} := by
  grind [getElems]

lemma getElems_insert (L : List α) (s : Set ℕ) {i : ℕ} (hi : i < L.length) :
    L.getElems (insert i s) = insert L[i] (L.getElems s) := by
  rw [← union_singleton, getElems_union, getElems_singleton hi, union_singleton]

lemma getElems_insert_eq_self (L : List α) (s : Set ℕ) {i : ℕ} (hi : L.length ≤ i) :
    L.getElems (insert i s) = L.getElems s := by
  rw [← union_singleton, getElems_union]
  simp [getElems, hi]

lemma getElems_insert_eq_dite (L : List α) (s : Set ℕ) (i : ℕ) :
    L.getElems (insert i s) = if hi : i < L.length then insert L[i] (L.getElems s) else
      L.getElems s := by
  split_ifs with h
  · exact getElems_insert L s h
  exact getElems_insert_eq_self L s (by lia)

lemma getElems_singleton_subsingleton {i : ℕ} : (L.getElems {i}).Subsingleton := by
  by_cases hi : i < L.length
  · simp [getElems_singleton hi]
  simp [getElems, hi]

lemma getElems_cons_of_mem (L : List α) (a : α) {s : Set ℕ} (h0 : 0 ∈ s) :
    (a :: L).getElems s = insert a (L.getElems {x | x + 1 ∈ s}) := by
  refine Set.ext fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨rfl | i, hi, his, rfl⟩ <;> simp [mem_getElems, his]
  rintro (rfl | ⟨i, hi, his, rfl⟩)
  · exact mem_getElems h0 (L := x :: L) (by simp)
  exact mem_getElems (show i + 1 ∈ s from his) (L := a :: L) (by grind)

lemma getElems_cons_of_notMem (L : List α) (a : α) {s : Set ℕ} (h0 : 0 ∉ s) :
    (a :: L).getElems s = L.getElems {x | x + 1 ∈ s} := by
  refine Set.ext fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨rfl | i, hi, his, rfl⟩
    · contradiction
    simp [mem_getElems, his]
  rintro ⟨i, hi, his, rfl⟩
  exact mem_getElems (show i + 1 ∈ s from his) (L := a :: L) (by grind)

lemma getElems_encard_le (L : List α) (s : Set ℕ) : (L.getElems s).encard ≤ s.encard := by
  obtain hs | hs := s.finite_or_infinite.symm
  · simp [hs.encard_eq]
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a s has hs ih =>
    grw [← Set.singleton_union, getElems_union, Set.encard_union_le,
      Set.encard_le_one_iff_subsingleton.2 (getElems_singleton_subsingleton ..), ih,
      Set.singleton_union, Set.encard_insert_of_notMem has, add_comm]

@[simp]
lemma getElems_univ (L : List α) : L.getElems Set.univ = {x | x ∈ L} := by
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨i, hi, -, rfl⟩
    simp
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem h
  exact ⟨i, hi, by simp, rfl⟩

@[grind! .]
lemma getElems_subset_toSet (L : List α) (s : Set ℕ) : L.getElems s ⊆ {x | x ∈ L} := by
  grw [s.subset_univ, getElems_univ]

lemma getElems_congr (L : List α) {s t : Set ℕ} (hst : ∀ i < L.length, i ∈ s ↔ i ∈ t) :
    L.getElems s = L.getElems t := by
  grind [getElems]

lemma getElems_inter_Iio (L : List α) (s : Set ℕ) :
    L.getElems (s ∩ Set.Iio L.length) = L.getElems s :=
  getElems_congr _ <| by grind

lemma getElems_append (L L' : List α) (s : Set ℕ) :
    (L ++ L').getElems s = L.getElems s ∪ L'.getElems {i | i + L.length ∈ s} := by
  induction L generalizing s with
  | nil => simp
  | cons x L ih =>
    by_cases h0s : 0 ∈ s
    · simp [getElems_cons_of_mem _ _ h0s, ih, add_assoc, insert_union]
    simp [getElems_cons_of_notMem _ _  h0s, ih, add_assoc]

lemma getElems_tail (L : List α) (s : Set ℕ) : L.tail.getElems s = L.getElems ((· + 1) '' s) := by
  match L with
  | [] => simp
  | a :: L =>
    rw [tail_cons, getElems_cons_of_notMem _ _ (by simp)]
    simp

lemma getElems_dropLast (hL : L.Nodup) (hL0 : L ≠ []) (s : Set ℕ) :
    L.dropLast.getElems s = L.getElems s \ {L.getLast hL0} := by
  nth_rw 2 [← L.dropLast_concat_getLast hL0]
  grw [getElems_append, union_sdiff_distrib, sdiff_singleton_eq_self, eq_comm, union_eq_left,
    getElems_subset_toSet]
  · simp
  grw [getElems_subset_toSet, mem_ofPred_eq, getLast_eq_getElem]
  rw [← L.dropLast_concat_getLast hL0, nodup_append] at hL
  grind

@[simp]
lemma Nodup.getElem_mem_getElems_iff (hL : L.Nodup) {s i} {hi : i < L.length} :
    L[i] ∈ L.getElems s ↔ i ∈ s := by
  simp [getElems, hL.getElem_inj_iff, hi]

lemma Nodup.subset_getElems_iff (hL : L.Nodup) {s : Set ℕ} {t : Set α} :
    t ⊆ L.getElems s ↔ t ⊆ {x | x ∈ L} ∧ ∀ i (hi : i < L.length), L[i] ∈ t → i ∈ s := by
  refine ⟨fun h ↦ ⟨h.trans (getElems_subset_toSet ..), fun i hi hit ↦ ?_⟩, fun h x hxt ↦ ?_⟩
  · exact hL.getElem_mem_getElems_iff.1 <| h hit
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem (h.1 hxt)
  exact mem_getElems (h.2 i hi hxt) hi

lemma getElems_subset_iff {s : Set ℕ} {t : Set α} :
    L.getElems s ⊆ t ↔ ∀ i (hi : i < L.length), i ∈ s → L[i] ∈ t := by
  refine ⟨fun h i hi his ↦ h ⟨i, hi, his, rfl⟩, fun h ↦ ?_⟩
  rintro _ ⟨i, hi, his, rfl⟩
  exact h i hi his

lemma Nodup.getElems_eq_iff (hL : L.Nodup) {s : Set ℕ} {t : Set α} :
    t = L.getElems s ↔ t ⊆ {x | x ∈ L} ∧ ∀ i (hi : i < L.length), L[i] ∈ t ↔ i ∈ s := by
  refine ⟨fun h ↦ ⟨h.subset.trans (getElems_subset_toSet ..), fun i hi ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [h, hL.getElem_mem_getElems_iff]
  refine subset_antisymm ?_ ?_
  · grind [subset_getElems_iff]
  grind [getElems_subset_iff]

lemma Nodup.getElems_inter (hL : L.Nodup) (s t : Set ℕ) :
    L.getElems (s ∩ t) = L.getElems s ∩ L.getElems t := by
  suffices L.getElems s ∩ L.getElems t ⊆ {x | x ∈ L} by
    simpa [eq_comm, hL.getElems_eq_iff, hL.getElem_mem_getElems_iff]
  grw [getElems_subset_toSet, Set.inter_subset_left]

lemma Nodup.getElems_ofPred_and (hL : L.Nodup) (s : Set ℕ) (p : ℕ → Prop) :
    L.getElems {i ∈ s | p i} = L.getElems s ∩ L.getElems {i | p i} := by
  rw [ofPred_and, hL.getElems_inter, ofPred_mem_eq]

lemma getElems_Ico_eq_singleton (L : List α) (p : ℕ) (hp : p < L.length) :
    L.getElems (Set.Ico p (p + 1)) = {L[p]} := by
  simp [getElems, ← le_antisymm_iff, eq_comm (a := L[p]), hp]

lemma getElems_Ico_eq_pair (L : List α) (p : ℕ) (hp : p + 1 < L.length) :
    L.getElems (Set.Ico p (p + 2)) = {L[p], L[p + 1]} := by
  rw [show p + 2 = (p + 1) + 1 by simp, ← insert_Ico_right_eq_Ico_add_one (by lia),
    getElems_insert _ _ hp, getElems_Ico_eq_singleton _ _ (by lia), pair_comm]

lemma getElems_Ico_eq_triple (L : List α) (p : ℕ) (hp : p + 2 < L.length) :
    L.getElems (Set.Ico p (p + 3)) = {L[p], L[p + 1], L[p + 2]} := by
  rw [show p + 3 = (p + 2) + 1 by simp, ← insert_Ico_right_eq_Ico_add_one (by lia),
    getElems_insert _ _ hp, getElems_Ico_eq_pair _ _ (by lia), insert_comm, pair_comm]

lemma getElems_reverse_bodd (L : List α) (b : Bool) :
    L.reverse.getElems {i | i.bodd = b} = L.getElems {i | i.bodd = (b == L.length.bodd)} := by
  suffices aux : ∀ (L : List α) b,
      L.reverse.getElems {i | i.bodd = b} ⊆ L.getElems {i | i.bodd = (b == L.length.bodd)} by
    refine (aux ..).antisymm ?_
    nth_grw 1 [← L.reverse_reverse, aux, length_reverse]
    simp
  rintro L b _ ⟨i, hi, rfl, rfl⟩
  refine ⟨L.length - 1 - i, by grind, ?_, by simp⟩
  simp only [mem_ofPred_eq]
  obtain ⟨d, hd⟩ := exists_add_of_le (show i + 1 ≤ L.length by grind)
  rw [hd, ← Nat.sub_add_eq, add_comm 1, Nat.add_sub_cancel_left]
  cases h : i.bodd with simp [h]

lemma getElems_bodd_eq_reverse (L : List α) (b : Bool) :
    L.getElems {i | i.bodd = b} = L.reverse.getElems {i | i.bodd = (b == L.length.bodd)} := by
  simp [getElems_reverse_bodd]

lemma Nodup.getElems_bodd_encard (hL : L.Nodup) (b : Bool) :
    2 * (L.getElems {i | i.bodd = b}).encard + (b && L.length.bodd).toNat =
      L.length + (!b && L.length.bodd).toNat := by
  induction L using List.twoStepInduction with
  | nil => simp
  | singleton x => cases b with | _ => simp [getElems, one_add_one_eq_two]
  | cons_cons x y xs h1 _ =>
      simp only [length_cons, Nat.bodd_succ, Bool.not_not, Nat.cast_add, Nat.cast_one]
      rw [add_assoc _ 1 1, ← two_mul, add_right_comm, ← h1 (by grind), add_comm,
        add_comm (2 * _), add_assoc, ← mul_add]
      obtain rfl | rfl := b
      · rw [getElems_cons_of_mem _ _ (by simp), getElems_cons_of_notMem _ _ (by simp),
          encard_insert_of_notMem (by grind)]
        simp
      rw [getElems_cons_of_notMem _ _ (by simp), getElems_cons_of_mem _ _ (by simp),
        encard_insert_of_notMem (by grind)]
      simp

@[simp]
lemma getElems_Iio_length (L : List α) : L.getElems (Set.Iio L.length) = {x | x ∈ L} := by
  rw [← Set.univ_inter (Set.Iio L.length), getElems_inter_Iio, getElems_univ]

lemma getElems_Iio (L : List α) (p : ℕ) : L.getElems (Set.Iio p) = {x | x ∈ L.take p} := by
  obtain hle | hlt := le_or_gt L.length p
  · rw [take_of_length_le (by lia), ← getElems_inter_Iio, inter_eq_self_of_subset_right (by simpa),
      getElems_Iio_length]
  induction L generalizing p with
  | nil => simp
  | cons x L ih =>
    obtain rfl | p := p
    · simp
    rw [getElems_cons_of_mem L x (by simp), take_succ_cons]
    simp [mem_Iio, Order.lt_add_one_iff, Order.add_one_le_iff, mem_cons, ofPred_or, ← ih p
      (by simpa using hlt), Set.Iio_def]

lemma getElems_Ici (L : List α) (p : ℕ) : L.getElems (Set.Ici p) = {x | x ∈ L.drop p} := by
  induction L generalizing p with
  | nil => simp
  | cons x L ih =>
    obtain rfl | p := p
    · simp
    rw [getElems_cons_of_notMem _ _ (by simp), drop_succ_cons, ← ih _]
    simp [Ici]

lemma getElems_Ico (L : List α) (p q : ℕ) : L.getElems (Set.Ico p q) = {x | x ∈ L.extract p q} := by
  induction L generalizing p q with
  | nil => simp
  | cons x L ih =>
    obtain rfl | p := p
    · rw [extract_zero, ← getElems_Iio, Ico_zero]
    obtain rfl | q := q
    · simp
    rw [getElems_cons_of_notMem _ _ (by simp)]
    simp_rw [mem_Ico, add_le_add_iff_right, add_lt_add_iff_right, ← mem_Ico, ofPred_mem_eq, ih,
      extract_succ_cons]

-- /-- Take every other element of a list `L`,
-- with the `Bool` indicating whether to take the first element.-/
-- def alt : List α → Bool → List α
--   | [], _ => []
--   | x :: L, true => x :: alt L false
--   | _ :: L, false => alt L true

-- @[simp]
-- lemma alt_empty (b) : List.alt ([] : List α) b = [] := rfl

-- @[simp]
-- lemma alt_cons_true (L : List α) (x : α) : (x :: L).alt true = x :: L.alt false := rfl

-- @[simp]
-- lemma alt_cons_false (L : List α) (x : α) : (x :: L).alt false = L.alt true := rfl

-- lemma alt_cons (L : List α) (x : α) (b : Bool) :
--     (x :: L).alt b = bif b then x :: L.alt (!b) else L.alt (!b) := by
--   cases b <;> simp

-- lemma alt_length_add (L : List α) : (L.alt true).length + (L.alt false).length = L.length := by
--   induction L with
--   | nil => simp
--   | cons a L ih => grind [alt_cons_true, alt_cons_false, ih.symm]

-- lemma alt_true_length_eq (L : List α) :
--     (L.alt true).length = (L.alt false).length + (if Odd L.length then 1 else 0) := by
--   induction L with
--   | nil => simp
--   | cons a L ih =>
--     simp only [alt_cons_true, length_cons, alt_cons_false, ih, Nat.odd_add_one]
--     grind

-- lemma length_alt (L : List α) :
--     L.length = 2 * (L.alt false).length + (if (Odd L.length) then 1 else 0) := by
--   grind [L.alt_length_add, L.alt_true_length_eq]

-- @[simp]
-- lemma alt_getElem (L : List α) (b : Bool) (i : ℕ) (hi : i < (L.alt b).length) :
--     (L.alt b)[i] = L[2 * i + (bif b then 0 else 1)]'
--       (by cases b <;> grind [L.alt_true_length_eq, L.length_alt]) := by
--   induction L generalizing b i with
--   | nil => simp at hi
--   | cons => cases b with cases i with simp_all [Nat.mul_add]

-- @[simp]
-- lemma alt_head_cons_cons (L : List α) : ((e :: f :: L).alt d).head (by cases d <;> simp) =
--     bif d then e else f := by
--   cases d <;> simp

-- lemma alt_head_cons (L : List α) {h : ((e :: L).alt d) ≠ []} : ((e :: L).alt d).head h =
--     d.dcond (fun _ ↦ e) (fun hd ↦ L.head (fun hF ↦ by simp [hF, hd] at h)) := by
--   cases L with | _ => cases d <;> simp_all [Bool.dcond]

-- lemma alt_head {L : List α} {hF : L.alt d ≠ []} :
--     (L.alt d).head hF = d.dcond (fun _ ↦ L.head (by rintro rfl; simp at hF))
--       (fun hd ↦ L[1]'(by
--         subst hd
--         match L with
--         | [] => simp at hF
--         | [x] => simp at hF
--         | _ :: _ :: F => simp)) := by
--   match L with
--   | [] => simp at hF
--   | e :: F =>
--     rw [F.alt_head_cons]
--     cases d <;>
--     simp [Bool.dcond, getElem_zero]

-- lemma mem_iff_exists_mem_alt (L : List α) : x ∈ L ↔ ∃ i, x ∈ L.alt i := by
--   induction L with
--   | nil => simp
--   | cons a L ih =>
--     simp only [mem_cons, ih, Bool.exists_bool, alt_cons_false, alt_cons_true]
--     grind

-- lemma alt_sublist (L : List α) (b : Bool) : (L.alt b) <+ L := by
--   induction L generalizing b with
--   | nil => simp
--   | cons a L ih =>
--     cases b
--     · exact (ih true).trans <| sublist_cons_self ..
--     simpa using ih false

-- lemma Nodup.alt_disjoint (hF : L.Nodup) : Disjoint (L.alt false) (L.alt true) := by
--   induction hF with
--   | nil => simp
--   | @cons a L h1 h2 hdj =>
--     simp [show a ∉ L.alt true from fun hmem ↦ h1 a ((L.alt_sublist true).mem hmem) rfl, hdj.symm]

-- lemma alt_concat (L : List α) (x : α) (b : Bool) :
--     (L.concat x).alt b = bif L.length.bodd == b then L.alt b else (L.alt b).concat x := by
--   induction L generalizing b with cases b <;> simp_all [Bool.apply_cond]

-- lemma alt_reverse (L : List α) (b : Bool) :
--     (L.alt b).reverse = L.reverse.alt (b == L.length.bodd) := by
--   induction L generalizing b with cases b <;> simp_all [← List.concat_eq_append, List.alt_concat]

-- lemma reverse_alt (L : List α) (b : Bool) :
--     L.reverse.alt b = (L.alt (bif L.length.bodd then b else !b)).reverse := by
--   cases b <;> simp [L.alt_reverse]

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

-- variable [DecidableEq α] {P : ℕ → Bool}

-- /-- Given a list `L`, and a predicate on the indices.
-- returns the finset of elements of `L` whose indices satisfy the predicate.
-- Indices out of bounds are ignored. -/
-- def getFinset (L : List α) (P : ℕ → Bool) : Finset α :=
--   ((L.zipIdx.filter (fun x ↦ P x.2)).map Prod.fst).toFinset

-- @[simp]
-- lemma getFinset_nil : ([] : List α).getFinset P = {} := by
--   simp [getFinset]

-- lemma getFinset_cons_pos {a : α} (h0 : P 0) :
--     (a :: L).getFinset P = insert a (L.getFinset (fun i ↦ P (i + 1))) := by
--   simp only [getFinset, zipIdx_cons', h0, filter_cons_of_pos, map_cons, toFinset_cons,
--     map_toFinset, toFinset_filter]
--   ext x
--   simp

-- lemma getFinset_cons_neg {a : α} (h0 : ¬ P 0) :
--     (a :: L).getFinset P = L.getFinset (fun i ↦ P (i + 1)) := by
--   simp only [getFinset, zipIdx_cons',  toFinset_cons,
--     map_toFinset, toFinset_filter, Finset.filter_insert, h0, Bool.false_eq_true, ↓reduceIte]
--   ext
--   simp

-- @[simp]
-- lemma getFinset_cons {a : α} : (a :: L).getFinset P = bif P 0 then
--     insert a (L.getFinset (fun i ↦ P (i + 1))) else (L.getFinset (fun i ↦ P (i + 1))) := by
--   by_cases h0 : P 0
--   · rw [getFinset_cons_pos h0]
--     simp [h0]
--   rw [getFinset_cons_neg h0]
--   simp [h0]

-- lemma getFinset_concat_pos {a : α} (hP : P L.length) :
--     (L ++ [a]).getFinset P = insert a (L.getFinset P) := by
--   induction L generalizing P with
--   | nil => simp [show P 0 by simpa using hP]
--   | cons b L ih => rw [getFinset_cons, cons_append, getFinset_cons, ih (by simpa),
--       Finset.insert_comm, ← Bool.apply_cond]

-- lemma getFinset_concat_neg {a : α} (hP : ¬P L.length) :
--     (L ++ [a]).getFinset P = L.getFinset P := by
--   induction L generalizing P with
--   | nil => simp [show ¬ P 0 by simpa using hP]
--   | cons b L ih => rw [getFinset_cons, cons_append, getFinset_cons, ih (by simpa using hP)]

-- lemma getFinset_concat {a : α} :
--     (L ++ [a]).getFinset P = bif P L.length then insert a (L.getFinset P) else L.getFinset P :=
--   by_cases h : P L.length
--   · rw [getFinset_concat_pos h]
--     simp [h]
--   rw [getFinset_concat_neg h]
--   simp [h]

-- @[simp]
-- lemma getFinset_singleton_eq_cond {a : α} : [a].getFinset P = bif P 0 then {a} else {} := by
--   simp [getFinset_cons]

-- lemma getFinset_subset (L : List α) (P : ℕ → Bool) : L.getFinset P ⊆ L.toFinset := by
--   induction L generalizing P with
--   | nil => simp
--   | cons a L ih =>
--     by_cases h0 : P 0
--     · grw [getFinset_cons_pos h0, toFinset_cons, ih]
--     grw [getFinset_cons_neg h0, ih, toFinset_cons, ← Finset.subset_insert]

-- @[simp]
-- lemma mem_getFinset_iff {a} :
--     a ∈ L.getFinset P ↔ ∃ (i : ℕ) (hi : i < L.length), P i ∧ L[i] = a := by
--   induction L using List.reverseRecOn generalizing P with
--   | nil => simp
--   | append_singleton L b ih =>
--     by_cases h : P L.length
--     · rw [getFinset_concat_pos h, Finset.mem_insert, ih]
--       grind
--     rw [getFinset_concat_neg h]
--     grind

-- lemma getFinset_mono (L : List α) {P Q : ℕ → Bool} (hPQ : ∀ i, P i → Q i) :
--     L.getFinset P ⊆ L.getFinset Q := by
--   simp only [Finset.subset_iff, mem_getFinset_iff, exists_and_left, forall_exists_index, and_imp]
--   rintro a i ha hi rfl
--   exact ⟨i, hPQ i ha, hi, rfl⟩

-- @[simp]
-- lemma getFinset_finset_insert {i : ℕ} (F : Finset ℕ) (hi : i < L.length) :
--     (L.getFinset (· ∈ insert i F)) = insert (L[i]) (L.getFinset (· ∈ F)) := by
--   induction L using List.reverseRecOn generalizing F with
--   | nil => simp at hi
--   | append_singleton L b IH => grind [mem_getFinset_iff]

-- lemma getFinset_false (hP : ∀ i < L.length, P i = false) : L.getFinset P = {} := by
--   induction L generalizing P with
--   | nil => simp
--   | cons a L ih => rw [getFinset_cons_neg (by grind), ih (by grind)]

-- lemma getFinset_finset_mono (L : List α) {F G : Finset ℕ} (hFG : F ⊆ G) :
--     L.getFinset (· ∈ F) ⊆ L.getFinset (· ∈ G) :=
--   getFinset_mono _ <| by simpa using Finset.subset_iff.1 hFG

-- lemma Nodup.getFinset_card (hnd : L.Nodup) {F : Finset ℕ}
--     (hF : F ⊆ Finset.range L.length) : (L.getFinset (· ∈ F)).card = F.card := by
--   induction F using Finset.induction with
--   | empty => rw [getFinset_false (by simp), Finset.card_empty, Finset.card_empty]
--   | insert a s has ih =>
--     rw [Finset.insert_subset_iff, Finset.mem_range] at hF
--     rw [getFinset_finset_insert _ hF.1, Finset.card_insert_of_notMem has,
--       Finset.card_insert_of_notMem, ih hF.2]
--     grind [hnd.getElem_inj_iff, mem_getFinset_iff]



-- -- @[simp]
-- -- lemma Nodup.getFinset_inter (hL : L.Nodup) (F G : Finset ℕ) :
-- --     L.getFinset (· ∈ F ∩ G) = L.getFinset (· ∈ F) ∩ L.getFinset (· ∈ G) := by
-- --   ext a
-- --   simp only [Finset.mem_inter, Bool.decide_and, mem_getFinset_iff, Bool.and_eq_true,
-- --     decide_eq_true_eq, exists_and_left]
-- --   constructor
-- --   · rintro ⟨i, ⟨hiF, hiG⟩, hi, rfl⟩
-- --     exact ⟨⟨i, hiF, hi, rfl⟩, i, hiG, hi, rfl⟩
-- --   rintro ⟨⟨i, hiF, hi, rfl⟩, j, hjG, hj, h'⟩
-- --   have := hL.injective_get
-- --   #check List.get
