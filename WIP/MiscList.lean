
-- /-- Take the elements of a list whose indices satisfy a certain predicate and (optionally)
-- belong to a certain subrange. -/
-- def filterIdx (L : List α) (p : ℕ → Bool) (start : ℕ := 0) (stop : ℕ := L.length) : List α :=
--   ((L.zipIdx.extract start stop).filter fun x ↦ p x.2).map Prod.fst

-- @[simp]
-- lemma filterIdx_nil (p : ℕ → Bool) {start stop : ℕ} :
--     ([] : List α).filterIdx p start stop = [] := by
--   simp [filterIdx]

-- lemma filterIdx_eq (L : List α) (p : ℕ → Bool) :
--     L.filterIdx p = (L.zipIdx.filter fun x ↦ p x.2).map Prod.fst := by
--   simp [filterIdx, take_of_length_le]

-- lemma filterIdx_eq_nil (L : List α) (p : ℕ → Bool) {start stop : ℕ} (hle : stop ≤ start) :
--     L.filterIdx p start stop = [] := by
--   simp [filterIdx, extract_eq_nil _ hle]

-- lemma filterIdx_zero_left (L : List α) (p : ℕ → Bool) (stop : ℕ) :
--     L.filterIdx p 0 stop = (L.take stop).filterIdx p := by
--   rw [filterIdx, filterIdx_eq, List.extract_zero, zipIdx_take]

-- @[simp]
-- lemma filterIdx_zero_right (L : List α) (p : ℕ → Bool) (start : ℕ) :
--     L.filterIdx p start 0 = [] := by
--   simp [filterIdx]

-- @[simp]
-- lemma filterIdx_false (L : List α) (start stop : ℕ) :
--     L.filterIdx (fun _ ↦ false) start stop = [] := by
--   simp [filterIdx]

-- @[simp]
-- lemma filterIdx_true (L : List α) : L.filterIdx (fun _ ↦ true) = L := by
--   simp [filterIdx]

-- lemma filterIdx_cons_pos (L : List α) (a : α) {p : ℕ → Bool} (hp : p 0 = true):
--     (a :: L).filterIdx p = a :: (L.filterIdx (fun x ↦ p (x + 1))) := by
--   rw [filterIdx_eq, filterIdx_eq]
--   simp only [zipIdx_cons, zero_add, zipIdx_succ, hp, filter_cons_of_pos, filter_map, map_cons,
--     map_map, cons.injEq, true_and]
--   convert rfl <;> rfl

-- lemma filterIdx_cons_neg (L : List α) (a : α) {p : ℕ → Bool} (hp : p 0 = false):
--     (a :: L).filterIdx p = L.filterIdx (fun x ↦ p (x + 1)) := by
--   rw [filterIdx_eq, filterIdx_eq]
--   simp only [zipIdx_cons, zero_add, zipIdx_succ, hp, Bool.false_eq_true, not_false_eq_true,
--     filter_cons_of_neg, filter_map, map_map]
--   convert rfl <;> rfl

-- lemma filterIdx_cons (L : List α) (a : α) (p : ℕ → Bool) :
--     (a :: L).filterIdx p = bif p 0 then a :: (L.filterIdx (fun x ↦ p (x + 1)))
--       else (L.filterIdx (fun x ↦ p (x + 1))) := by
--   cases h : p 0 with
--   | false => rw [filterIdx_cons_neg _ _ h, cond_false]
--   | true => rw [filterIdx_cons_pos _ _ h, cond_true]

-- lemma filterIdx_cons_succ_succ (L : List α) (x : α) (p : ℕ → Bool) (a b : ℕ) :
--     (x :: L).filterIdx p (a + 1) (b + 1) = L.filterIdx (fun x ↦ p (x + 1)) a b := by
--   rw [filterIdx, zipIdx_cons', extract_succ_cons, filterIdx, ← map_extract, filter_map, map_map]
--   convert rfl <;>
--   simp [funext_iff]

-- lemma take_eq_filterIdx (L : List α) (b : ℕ) : L.take b = L.filterIdx (fun i ↦ i < b) := by
--   induction b generalizing L with
--   | zero => simp
--   | succ b ih =>
--     cases L with
--     | nil => simp
--     | cons a L =>
--       rw [take_succ_cons, ih, length_cons, eq_comm, filterIdx_zero_left,
--         take_of_length_le (by simp), filterIdx_cons_pos _ _ (by simp)]
--       simp

-- lemma drop_eq_filterIdx (L : List α) (b : ℕ) : L.drop b = L.filterIdx (fun i ↦ b ≤ i) := by
--   induction b generalizing L with
--   | zero => simp
--   | succ b ih =>
--     cases L with
--     | nil => simp
--     | cons x L =>
--       rw [drop_succ_cons, length_cons, filterIdx_zero_left, take_of_length_le (by simp),
--         filterIdx_cons_neg _ _ (by simp), ih]
--       simp

-- lemma extract_eq_filterIdx (L : List α) (a b : ℕ) :
--     L.extract a b = L.filterIdx (fun i ↦ a ≤ i && i < b) := by
--   induction b generalizing a L with
--   | zero => simp
--   | succ b ih =>
--     cases L with
--     | nil => simp
--     | cons x L =>
--       obtain rfl | a := a
--       · simp only [extract_zero, take_succ_cons, zero_le, decide_true, Bool.true_and, length_cons]
--         rw [filterIdx_zero_left, eq_comm, take_of_length_le (by simp),
--           filterIdx_cons_pos _ _ (by simp), take_eq_filterIdx]
--         simp
--       rw [extract_eq_drop_take', take_succ_cons, drop_succ_cons, ← extract_eq_drop_take', ih,
--         filterIdx_cons_neg _ _ (by simp)]
--       simp

-- lemma filterIdx_length (L : List α) (p : ℕ → Bool) :
--     (L.filterIdx p).length = ((range L.length).filter p).length := by
--   rw [filterIdx_eq, length_map, range_eq_range', ← zipIdx_map_snd 0 L, ← length_map Prod.snd,
--     filter_map]
--   rfl

-- lemma filterIdx_congr (L : List α) {p q : ℕ → Bool} (start stop : ℕ)
--     (h : ∀ i, start ≤ i → i < stop → p i = q i) :
--     L.filterIdx p start stop = L.filterIdx q start stop := by
--   rw [filterIdx, filterIdx, filter_congr]
--   refine fun ⟨x, i⟩ hx ↦ ?_
--   simp only [extract_eq_take_drop, mem_take_iff_getElem, getElem_drop, getElem_zipIdx, zero_add,
--     Prod.mk.injEq, length_drop, length_zipIdx, lt_inf_iff, exists_and_right] at hx
--   obtain ⟨j, ⟨⟨hj, hj'⟩, rfl⟩, rfl⟩ := hx
--   grind

-- lemma filterIdx_map {β : Type*} (L : List α) (p : ℕ → Bool) (f : α → β) {a b : ℕ} :
--     (L.filterIdx p a b).map f = (L.map f).filterIdx p a b := by
--   induction L generalizing p a b with
--   | nil => rw [filterIdx_nil, map_nil, filterIdx_nil]
--   | cons x L ih =>
--     obtain rfl | b := b
--     · simp
--     obtain rfl | a := a
--     · specialize ih (fun i ↦ p (i + 1)) (a := 0) (b := b)
--       rw [filterIdx_zero_left, eq_comm, filterIdx_zero_left] at ih
--       rw [filterIdx_zero_left, take_succ_cons, map_cons, eq_comm, filterIdx_zero_left,
--         take_succ_cons, filterIdx_cons, ih, filterIdx_cons]
--       cases h : p 0 with simp
--     rw [filterIdx_cons_succ_succ, ih, map_cons, filterIdx_cons_succ_succ]

-- lemma filterIdx_start_stop_eq (L : List α) (p : ℕ → Bool) (a b : ℕ) :
--     L.filterIdx p a b = L.filterIdx (fun i ↦ p i && (a ≤ i && i < b)) := by
--   induction L generalizing a b p with
--   | nil =>
--     simp
--   | cons x L ih =>
--     obtain rfl | b := b
--     · simp
--     obtain rfl | a := a
--     · rw [filterIdx_zero_left, take_succ_cons, filterIdx_cons, ← filterIdx_zero_left, ih,
--         filterIdx_cons]
--       cases h : p 0 with simp
--     rw [filterIdx_cons_succ_succ, ih, filterIdx_cons]
--     simp




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



-- /-- Take all the elements `L[i]` where `p ≤ i < q`, and `i` has a given parity. -/
-- def List.altBetween (L : List α) (p q : ℕ) (b : Bool) : Set α :=
--     {x | ∃ (i : ℕ) (hi : i < L.length), p ≤ i ∧ i < q ∧ i.bodd = b ∧ L[i] = x}

-- lemma List.altBetween_subset_iff : L.altBetween p q b ⊆ X ↔
--     ∀ i (hi : i < L.length), p ≤ i → i < q → i.bodd = b → L[i] ∈ X := by
--   grind [List.altBetween]

-- lemma List.altBetween_subset (L : List α) p q b : L.altBetween p q b ⊆ {e | e ∈ L} := by
--   grind [List.altBetween]

-- @[simp]
-- lemma List.altBetween_self : L.altBetween p p b = ∅ := by
--   grind [List.altBetween]

-- lemma List.altBetween_eq_empty_of_ge (hji : j ≤ i) : L.altBetween i j b = ∅ := by
--   grind [List.altBetween]

-- lemma altBetween_mono {p q p' q'} (L : List α) (hpp' : p ≤ p') (hqq' : q' ≤ q) (b : Bool) :
--     L.altBetween p' q' b ⊆ L.altBetween p q b := by
--   grind [altBetween]

-- lemma altBetween_eq_of_length_le (L : List α) (hj : L.length ≤ j) :
--     L.altBetween i j b = L.altBetween i L.length b := by
--   refine subset_antisymm ?_ (altBetween_mono _ rfl.le hj _)
--   rintro e ⟨x, hx, hix, hxj, rfl, rfl⟩
--   use x, hx, hix, hx

-- lemma altBetween_add_one_eq_self (p : ℕ) (hq : q.bodd = !b) :
--     L.altBetween p (q + 1) b = L.altBetween p q b := by
--   refine (altBetween_mono _ rfl.le (by lia) _).antisymm' ?_
--   rintro x ⟨i, hi, hpi, hiq, rfl, rfl⟩
--   refine ⟨i, hi, hpi, ?_, rfl, rfl⟩
--   suffices i ≠ q by grind
--   grind

-- lemma altBetween_add_one_left_eq_self (hqb : p.bodd = !b) (q : ℕ) :
--     L.altBetween (p + 1) q b = L.altBetween p q b := by
--   refine (altBetween_mono _ (by lia) rfl.le _).antisymm ?_
--   rintro x ⟨i, hi, hpi, hiq, rfl, rfl⟩
--   refine ⟨i, hi, ?_, hiq, rfl, rfl⟩
--   suffices i ≠ p by grind
--   grind

-- lemma altBetween_eq_insert_altBetween_add_one_left (hpq : p < q) (hp : p < L.length)
--     (hqb : p.bodd = b) : L.altBetween p q b = insert L[p] (L.altBetween (p + 1) q b) := by
--   refine subset_antisymm ?_ <| insert_subset ⟨p, by grind⟩ <| altBetween_mono _ (by lia) rfl.le _
--   rintro _ ⟨i, hi, hpi, hiq, rfl, rfl⟩
--   obtain rfl | hlt := hpi.eq_or_lt
--   · simp
--   exact .inr ⟨i, by grind⟩

-- lemma altBetween_add_one_eq_insert (hpq : p ≤ q) (hqlt : q < L.length) (hqb : q.bodd = b) :
--     L.altBetween p (q + 1) b = insert L[q] (L.altBetween p q b) := by
--   refine (insert_subset ?_ (altBetween_mono _ rfl.le (by lia) _)).antisymm' ?_
--   · exact ⟨q, hqlt, hpq, by lia, hqb, rfl⟩
--   rintro x ⟨i, hi, hpi, hiq, rfl, rfl⟩
--   obtain rfl | hne := eq_or_ne i q
--   · simp
--   exact .inr ⟨i, hi, hpi, by grind, rfl, rfl⟩

-- lemma altBetween_union (L : List α) (hpq : p ≤ q) (hqr : q ≤ r) :
--     L.altBetween p q b ∪ L.altBetween q r b = L.altBetween p r b := by
--   apply (union_subset (altBetween_mono _ rfl.le hqr _) (altBetween_mono _ hpq rfl.le _)).antisymm
--   rw [altBetween_subset_iff]
--   rintro i hi hpi hir rfl
--   obtain hle | hlt := lt_or_ge i q
--   · exact .inl <| by use i, hi
--   exact .inr <| by grind [altBetween]

-- lemma altBetween_add_two (hpq : p ≤ q) (hq : q.bodd = !b) (hqn : q + 1 < L.length) :
--     L.altBetween p (q + 2) b = insert L[q + 1] (L.altBetween p q b) := by
--   rw [altBetween_add_one_eq_insert (by lia) hqn (by simpa), altBetween_add_one_eq_self _ hq]

-- lemma altBetween_add_two' (hpq : p ≤ q) (hq : q.bodd = b) (hqn : q + 1 < L.length) :
--     L.altBetween p (q + 2) b = insert L[q] (L.altBetween p q b) := by
--   rw [altBetween_add_one_eq_self _ (by simp [hq]), altBetween_add_one_eq_insert hpq _ hq]

-- lemma altBetween_add_two'' (hpq : p ≤ q) (hqn : q + 1 < L.length) :
--     L.altBetween p (q + 2) b = insert L[q + (q.bodd != b).toNat] (L.altBetween p q b) := by
--   obtain rfl | rfl := b.eq_or_eq_not q.bodd
--   · rw [altBetween_add_two' hpq rfl hqn]
--     simp
--   rw [altBetween_add_two hpq (by simp) hqn]
--   simp

-- lemma List.Nodup.getElem_mem_altBetween_iff (hL : L.Nodup) {hi : i < L.length} :
--     L[i] ∈ L.altBetween p q b ↔ p ≤ i ∧ i < q ∧ i.bodd = b := by
--   simp only [altBetween, exists_and_left, mem_ofPred_eq]
--   grind [hL.getElem_inj_iff]

-- lemma getElem_mem_altBetween {hi : i < L.length} (hpi : p ≤ i) (hiq : i < q) (hib : i.bodd = b) :
--     L[i] ∈ L.altBetween p q b := by
--   grind [altBetween]

-- lemma altBetween_pair_eq_middle (hp : p + 1 < L.length) (hpb : p.bodd = !b) :
--     L.altBetween p (p + 2) b = {L[p + 1]} := by
--   rw [altBetween_add_two rfl.le hpb hp, altBetween_self, insert_empty_eq]

-- lemma altBetween_pair_eq_left (hp : p < L.length) (hpb : p.bodd = b) :
--     L.altBetween p (p + 2) b = {L[p]} := by
--   rw [altBetween_add_one_eq_self _ (by simpa), altBetween_add_one_eq_insert rfl.le hp hpb,
--     altBetween_self, insert_empty_eq]

-- lemma altBetween_insert_drop_two {L : List α} {p q : ℕ} (hpq : p ≤ q)
--     (hplt : p + 1 < L.length) (hp : p.bodd = !b) :
--     insert L[p + 1] ((L.drop 2).altBetween p q b) = L.altBetween p (q + 2) b := by
--   simp only [altBetween, getElem_drop, length_drop, exists_and_left, Set.ext_iff,
--     Set.mem_insert_iff, mem_ofPred_eq, iff_def, forall_exists_index, and_imp]
--   refine fun i ↦ ⟨?_, ?_⟩
--   · rintro (rfl | ⟨i, hpi, hiq, rfl, hilt, rfl⟩)
--     · exact ⟨p + 1, by lia, by lia, by simpa, by lia, rfl⟩
--     exact ⟨2 + i, by lia, by lia, by simp, by lia, rfl⟩
--   rintro i hpi hiq rfl hlt rfl
--   by_contra! hcon
--   obtain rfl | rfl | i := i; grind; grind
--   exact hcon.2 i (by grind) (by lia) (by simp) (by lia) (by grind)

-- -- lemma mem_extract_iff_getElem {L : List α} : x ∈ L.extract p q ↔ ∃ (i : ℕ) (hi : i < L.length),
-- --     p ≤ i ∧ i < q ∧ L[i] = x := by
-- --   simp only [extract_eq_take_drop, mem_take_iff_getElem, getElem_drop, length_drop, lt_inf_iff,
-- --     exists_and_left]
-- --   refine ⟨by grind, ?_⟩
-- --   rintro ⟨i, hpi, hiq, hi, rfl⟩
-- --   obtain ⟨d, rfl⟩ := exists_add_of_le hpi
-- --   grind


-- lemma altBetween_subset_extract (L : List α) (p q : ℕ) (b : Bool) :
--     L.altBetween p q b ⊆ {x | x ∈ L.extract p q} := by
--   grind [altBetween, mem_extract_iff_getElem]

-- lemma List.Nodup.altBetween_encard_add_eq {L : List α} (hL : L.Nodup) {p q : ℕ} (hpq : p ≤ q)
--     (hq : q ≤ L.length) (b : Bool) :
--     2 * (L.altBetween p q b).encard + p + (p.bodd != b && q.bodd == b).toNat =
--       q + (p.bodd == b && q.bodd != b).toNat := by
--   obtain ⟨rfl | rfl | d, hd⟩ := exists_add_of_le hpq
--   · obtain rfl := hd
--     cases b with simp
--   · subst hd
--     obtain rfl | rfl := b.eq_or_eq_not p.bodd
--     · rw [altBetween_add_one_eq_insert rfl.le (by lia) rfl]
--       simp [add_assoc (p: ℕ∞) 1 1, add_comm (2 : ℕ∞), one_add_one_eq_two]
--     simp [altBetween_add_one_eq_self]
--   rw [hd, add_assoc, add_assoc, one_add_one_eq_two, ← add_assoc, ← add_assoc,
--     altBetween_add_two'' (by lia) (by lia), encard_insert_of_notMem
--     (by simp [hL.getElem_mem_altBetween_iff])]
--   simp only [Nat.bodd_add, show Nat.bodd 2 = false from rfl, Bool.bne_false, Nat.cast_add,
--     Nat.cast_ofNat, Bool.bne_assoc, mul_add, mul_one]
--   have hwin := altBetween_encard_add_eq hL (show p ≤ p + d by simp) (by lia) b
--   apply_fun (· + 2) at hwin
--   simp_rw [add_assoc, add_comm (2 : ℕ∞)] at *
--   convert hwin using 1
--   · simp [add_assoc]
--   simp [add_assoc]

-- @[simp]
-- lemma altBetween_cons_false (L : List α) (q : ℕ) :
--     (e :: L).altBetween 0 (q + 1) false = insert e (L.altBetween 0 q true) := by
--   simp only [altBetween, zero_le, Order.lt_add_one_iff, true_and, length_cons, exists_and_left,
--     Set.ext_iff, mem_ofPred_eq, Set.mem_insert_iff]
--   refine fun x ↦ ⟨?_, ?_⟩
--   · rintro ⟨rfl | i, hiq, hi, hiL, rfl⟩
--     · simp
--     exact .inr ⟨i, by lia, by simpa using hi, hiL, rfl⟩
--   rintro (rfl | ⟨i, hiq, hi, hiL, rfl⟩)
--   · use 0
--     simp
--   exact ⟨i + 1, by lia, by simpa using hi, by lia, by simp⟩

-- @[simp]
-- lemma altBetween_cons_true (L : List α) (q : ℕ) :
--     (e :: L).altBetween 0 (q + 1) true = L.altBetween 0 q false := by
--   simp only [altBetween, zero_le, Order.lt_add_one_iff, true_and, length_cons, exists_and_left]
--   simp only [Set.ext_iff, mem_ofPred_eq, iff_def, forall_exists_index, and_imp]
--   refine fun x ↦ ⟨?_, ?_⟩
--   · rintro (rfl | i) hiq hi hiL rfl
--     · simp at hi
--     exact ⟨i, by lia, by simpa using hi, by grind⟩
--   rintro i hiq hi hiL rfl
--   exact ⟨i + 1, by lia, by simpa, by grind⟩

-- @[simp]
-- lemma altBetween_cons (L : List α) (q : ℕ) :
--     (e :: L).altBetween (p + 1) (q + 1) b = L.altBetween p q (!b) := by
--   refine subset_antisymm ?_ ?_
--   · rintro _ ⟨rfl | i, hi, hpi, hiq, rfl, rfl⟩
--     · lia
--     simp only [Nat.bodd_succ, Bool.not_not, getElem_cons_succ]
--     use i; grind
--   rintro _ ⟨i, hi, hpi, hiq, hi', rfl⟩
--   exact ⟨i + 1, by grind [Nat.bodd_succ, length_cons]⟩
