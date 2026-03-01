import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.SplitBy

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

theorem splitBy_of_isChain {r : α → α → Bool} {l : List α} (hc : l.IsChain (r · ·)) (hne : l ≠ []) :
    splitBy r l = [l] := by
  match l, hne with
  | [a], _ => simp
  | a :: b :: as, _ =>
    rw [isChain_cons_cons] at hc
    obtain ⟨m, ms, hm⟩ := bar r b as
    obtain ⟨rfl, rfl⟩ : as = m ∧ ms = [] := by simpa [splitBy_of_isChain hc.2] using hm
    rw [foo hc.1 hm]

theorem splitBy_of_mem_splitBy {r : α → α → Bool} {l l' : List α} (h : l ∈ splitBy r l') :
    splitBy r l = [l] :=
  splitBy_of_isChain (isChain_of_mem_splitBy h) (ne_nil_of_mem_splitBy h)

theorem splitBy_flatten_of_cons {r : α → α → Bool} {l l' : List α} {L : List (List α)}
    (h : splitBy r l = l' :: L) : L.flatten.splitBy r = L := by
  match l with
  | nil => simp at h
  | [a] =>
    obtain rfl | rfl := (by simpa only [splitBy_singleton, infix_singleton_iff] using h)
    simp
  | a :: b :: as =>
    obtain ⟨m, ms, hm⟩ := bar r b as
    by_cases hab : r a b
    · obtain ⟨rfl, rfl⟩ : _ = l' ∧ ms = L := by simpa [foo hab hm] using h
      exact splitBy_flatten_of_cons hm
    · obtain ⟨rfl, rfl⟩ : [a] = l' ∧ _ = L := by simpa [splitBy_cons_cons_of_not_rel _ hab] using h
      rw [flatten_splitBy]

theorem splitBy_flatten_of_prefix {r : α → α → Bool} {l : List α} {L : List (List α)}
    (h : L <+: splitBy r l) : L.flatten.splitBy r = L := by
  match l with
  | nil =>
    obtain rfl := by simpa using h
    simp
  | [a] =>
    obtain rfl | rfl := (by simpa only [splitBy_singleton, infix_singleton_iff] using h.isInfix)
    <;> simp
  | a :: b :: as =>
    obtain ⟨m, ms, hm⟩ := bar r b as
    by_cases hab : r a b
    · have habms := foo hab hm
      rw [habms, prefix_cons_iff] at h
      obtain rfl | ⟨L', rfl, hl'⟩ := h
      · simp
      have hbm := splitBy_of_mem_splitBy  <| hm ▸ (by simp : (b :: m) ∈ ((b :: m) :: ms))
      obtain rfl | hneL' := eq_or_ne L' []
      · simp only [flatten_cons, flatten_nil, append_nil]
        exact foo hab hbm
      have hrec := splitBy_flatten_of_prefix <| (splitBy_flatten_of_cons hm) ▸ hl'
      have hne_flat : L'.flatten ≠ [] := by
        intro hflat
        simp [hflat, hneL'] at hrec
      have hboundary : ¬ r ((a :: b :: m).getLast (by simp)) ((L'.flatten).head hne_flat) := by
        have := isChain_getLast_head_splitBy r (a :: b :: as)
        rw [habms, ← cons_head_tail (by grind : ms ≠ [])] at this
        obtain ⟨_, hmsh, hf⟩ := this.rel_head
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, Bool.not_eq_true]
        simp_rw [head_flatten_eq_head_head hne_flat (hl'.head hneL' ▸ hmsh), hl'.head hneL']
        exact hf
      rw [flatten_cons, splitBy_append_of_not_rel (by simp) hne_flat hboundary, hrec]
      simp [foo hab hbm]
    · rw [splitBy_cons_cons_of_not_rel _ hab, prefix_cons_iff] at h
      obtain rfl | ⟨L', rfl, hl'⟩ := h
      · simp
      obtain rfl | hneL' := eq_or_ne L' []
      · simp
      have := splitBy_flatten_of_prefix hl'
      have hne_flat : L'.flatten ≠ [] := by
        intro hflat
        simp [hflat, hneL'] at this
      -- The head of `L'.flatten` is `b`, since `L'` is a nonempty prefix of `(b :: as).splitBy r`.
      have hboundary : ¬ r ([a].getLast (by simp)) ((L'.flatten).head hne_flat) := by
        have := isChain_getLast_head_splitBy r (a :: b :: as)
        rw [splitBy_cons_cons_of_not_rel _ hab, hm] at this
        obtain ⟨_, hmsh, hf⟩ := this.rel_head
        simp only [getLast_singleton, Bool.not_eq_true]
        simp_rw [head_flatten_eq_head_head hne_flat (by simp [hl'.head hneL', hm]), hl'.head hneL',
          hm]
        exact hf
      rw [flatten_cons, splitBy_append_of_not_rel (by simp) hne_flat hboundary, this]
      simp

theorem splitBy_flatten_of_infix {r : α → α → Bool} {l : List α} {L : List (List α)}
    (h : L <:+: splitBy r l) : L.flatten.splitBy r = L := by
  induction hl : splitBy r l generalizing l with
  | nil =>
    obtain rfl := by simpa [hl] using h
    simp
  | cons head tail IH =>
    rw [hl, infix_cons_iff] at h
    obtain hnil | htl := h
    · exact splitBy_flatten_of_prefix <| hl ▸ hnil
    · have htlf := splitBy_flatten_of_cons hl
      exact IH (htlf.symm ▸ htl) htlf
