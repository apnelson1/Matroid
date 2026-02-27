import Matroid.Triangle

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α}



open Set List

@[simp]
lemma Bool.cond_self_left {α : Sort*} {i : Bool} {a b c : α} :
    (bif i then (bif i then a else b) else c : α) = bif i then a else c := by
  grind

@[simp]
lemma Bool.cond_self_right {α : Sort*} {i : Bool} {a b c : α} :
    (bif i then a else (bif i then b else c) : α) = bif i then a else c := by
  grind

#check Bool.dcond

@[simp]
lemma Bool.dcond_true {α : Sort*} (x : true = true → α) (y : true = false → α) :
    Bool.dcond true x y = x rfl := rfl

@[simp]
lemma Bool.dcond_false {α : Sort*} (x : false = true → α) (y : false = false → α) :
    Bool.dcond false x y = y rfl := rfl

/-- Take every other element of a list `L`,
with the `Bool` indicating whether to take the first element.-/
def List.alt : List α → Bool → List α
  | [], _ => []
  | x :: L, true => x :: alt L false
  | _ :: L, false => alt L true

@[simp]
lemma List.alt_empty (b) : List.alt ([] : List α) b = [] := rfl

@[simp]
lemma List.alt_cons_true (L : List α) (x : α) : (x :: L).alt true = x :: L.alt false := rfl

@[simp]
lemma List.alt_cons_false (L : List α) (x : α) : (x :: L).alt false = L.alt true := rfl

lemma List.alt_cons (L : List α) (x : α) (b : Bool) :
    (x :: F).alt b = bif b then x :: L.alt (!b) else L.alt (!b) := by
  cases b <;> simp

lemma List.alt_length_add (L : List α) : (L.alt true).length + (L.alt false).length = L.length := by
  induction L with
  | nil => simp
  | cons a L ih => grind [alt_cons_true, alt_cons_false, ih.symm]

lemma List.alt_true_length_eq (L : List α) :
    (L.alt true).length = (L.alt false).length + (if Odd L.length then 1 else 0) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [alt_cons_true, length_cons, alt_cons_false, ih, Nat.odd_add_one]
    grind

lemma List.length_alt (L : List α) :
    L.length = 2 * (L.alt false).length + (if (Odd L.length) then 1 else 0) := by
  grind [L.alt_length_add, L.alt_true_length_eq]

@[simp]
lemma List.alt_getElem (L : List α) (b : Bool) (i : ℕ) (hi : i < (L.alt b).length) :
    (L.alt b)[i] = L[2 * i + (bif b then 0 else 1)]'
      (by cases b <;> grind [L.alt_true_length_eq, L.length_alt]) := by
  induction L generalizing b i with
  | nil => simp at hi
  | cons => cases b with cases i with simp_all [Nat.mul_add]

@[simp]
lemma List.alt_head_cons_cons (L : List α) : ((e :: f :: L).alt d).head (by cases d <;> simp) =
    bif d then e else f := by
  cases d <;> simp

lemma List.alt_head_cons (L : List α) {h : ((e :: L).alt d) ≠ []} : ((e :: L).alt d).head h =
    d.dcond (fun _ ↦ e) (fun hd ↦ L.head (fun hF ↦ by simp [hF, hd] at h)) := by
  cases L with | _ => cases d <;> simp_all [Bool.dcond]

lemma List.alt_head {L : List α} {hF : L.alt d ≠ []} :
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

lemma List.alt_sublist (L : List α) (b : Bool) : (L.alt b) <+ L := by
  induction L generalizing b with
  | nil => simp
  | cons a L ih =>
    cases b
    · exact (ih true).trans <| sublist_cons_self ..
    simpa using ih false

lemma List.Nodup.alt_disjoint (hF : L.Nodup) : Disjoint (L.alt false) (L.alt true) := by
  induction hF with
  | nil => simp
  | @cons a L h1 h2 hdj =>
    simp [show a ∉ L.alt true from fun hmem ↦ h1 a ((L.alt_sublist true).mem hmem) rfl, hdj.symm]

lemma List.alt_concat (L : List α) (x : α) (b : Bool) :
    (L.concat x).alt b = bif L.length.bodd == b then L.alt b else (L.alt b).concat x := by
  induction L generalizing b with cases b <;> simp_all [Bool.apply_cond]

lemma List.alt_reverse (L : List α) (b : Bool) :
    (L.alt b).reverse = L.reverse.alt (b == L.length.bodd) := by
  induction L generalizing b with cases b <;> simp_all [← List.concat_eq_append, List.alt_concat]

lemma List.reverse_alt (L : List α) (b : Bool) :
    L.reverse.alt b = (L.alt (bif L.length.bodd then b else !b)).reverse := by
  cases b <;> simp [L.alt_reverse]

namespace Matroid

-- variable {J : Bool → List α}


variable {F J L : List α} {b c : Bool}

/-- A fan of a matroid `M` is a sequence `[e₀, f₀, e₁, f₁, ...]` of at least three
distinct elements of `M`, where consecutive triples alternate between being triangles and triads.
The fan may start and end with either triangles or triads;
if each pair of consecutive `eᵢ` belongs to a common triangle,
then the `eᵢ` are the 'joints' of the fan, and the `fᵢ` are 'cojoints'.

Formally, the predicate `M.IsFan J b c` means that `J` is the list of elements, and `b c` are
boolean variables indicating whether the fan respectively starts and ends with a triangle.
We have `b = c` if and only if `J` had odd length.

For example, if `{e,f,g}` is a triangle of `M`, then the fan `e, f, g` corresponds to the
statement `M.IsFan [e, f, g] false false`.
(The `false false` means that the fan begins and ends on joints.)

If, additionally, `{f,g,h}` is a triad of `M`, then the fan `e, f, g, h` corresponds to the
statement `M.IsFan [e, f, g, h] false true`. -/
inductive IsFan : Matroid α → List α → Bool → Bool → Prop
  | of_isTriangle (M b e f g) (h : (M.bDual b).IsTriangle {e, f, g}) : IsFan M [e, f, g] b b
  | cons_triangle (M e x y F b c) (h : IsFan M (x :: y :: F) b c) (heF : e ∉ F)
      (hT : (M.bDual (!b)).IsTriangle {e, x, y}) : IsFan M (e :: x :: y :: F) (!b) c

lemma IsTriangle.isFan_of_bDual (h : (M.bDual b).IsTriangle {e, f, g}) : M.IsFan [e, f, g] b b :=
  IsFan.of_isTriangle M b e f g h

lemma IsTriangle.isFan (h : M.IsTriangle {e, f, g}) : M.IsFan [e, f, g] false false :=
  IsFan.of_isTriangle M false e f g h

lemma IsFan.cons (h : M.IsFan (x :: y :: F) b c) (heF : e ∉ F)
    (hT : (M.bDual (!b)).IsTriangle {e, x, y}) : M.IsFan (e :: x :: y :: F) (!b) c := by
  apply IsFan.cons_triangle <;> assumption

lemma IsFan.cons_not (h : M.IsFan (x :: y :: F) (!b) c) (heF : e ∉ F)
    (hT : (M.bDual b).IsTriangle {e, x, y}) : M.IsFan (e :: x :: y :: F) b c := by
  simpa using h.cons heF (by simpa)

lemma IsFan.dual (h : M.IsFan F b c) : M✶.IsFan F (!b) (!c) := by
  induction h with
  | of_isTriangle b e f g h => exact IsTriangle.isFan_of_bDual <| by simpa
  | cons_triangle e x y F b c h heF hT ih => exact ih.cons heF <| by simpa

lemma IsFan.of_dual (h : M✶.IsFan F b c) : M.IsFan F (!b) (!c) := by
  simpa using h.dual

@[simp]
lemma isFan_dual_iff : M✶.IsFan F b c ↔ M.IsFan F (!b) (!c) :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

lemma isFan_dual_bnot_iff : M✶.IsFan F (!b) (!c) ↔ M.IsFan F b c := by
  simp

@[simp]
lemma isFan_bDual_iff : (M.bDual d).IsFan F b c ↔ M.IsFan F (b != d) (c != d) := by
  cases d with simp

alias ⟨IsFan.of_bDual, _⟩ := isFan_bDual_iff

lemma IsFan.three_le_length (h : M.IsFan F b c) : 3 ≤ F.length := by
  induction h with simp_all

lemma IsFan.ne_nil (h : M.IsFan F b c) : F ≠ [] := by
  grind [h.three_le_length]

lemma IsFan.alt_ne_nil (h : M.IsFan F b c) {d} : F.alt d ≠ [] := by
  cases d <;> grind [F.alt_true_length_eq, h.three_le_length, F.alt_length_add]

/-- An induction principle for fans that involves verifying a primal case and self-duality. -/
@[elab_as_elim]
def IsFan.recTriangle
    {motive : (M : Matroid α) → (F : List α) → (b c : Bool) → M.IsFan F b c → Prop}
    (of_isTriangle : ∀ (M : Matroid α) (e f g : α)
      (h : M.IsTriangle {e, f, g}), motive M [e, f, g] false false h.isFan)
    (of_dual : ∀ M F b h, motive M✶ F false (!b) h → motive M F true b (by simpa using h.dual))
    (cons_triangle : ∀ M e x y F b (h : M.IsFan (x :: y :: F) true b) (heF : e ∉ F)
      (hT : M.IsTriangle {e, x, y}), motive M (x :: y :: F) true b h →
        motive M (e :: x :: y :: F) false b (h.cons heF hT)) (h : M.IsFan F b c) :
    motive M F b c h := by
  induction h with
  | of_isTriangle b e f g h =>
    cases b
    · exact of_isTriangle _ _ _ _ h
    exact of_dual M [e, f, g] true (by simpa using h.isFan) (of_isTriangle _ _ _ _ h)
  | cons_triangle e x y F b c h heF hT ih =>
    cases b
    · refine of_dual M (e :: x :: y :: F) c (h.cons heF hT).dual ?_
      refine cons_triangle M✶ e x y F (!c) h.dual heF hT ?_
      exact of_dual M✶ (x :: y :: F) (!c) (by simpa) (by simpa)
    exact cons_triangle _ _ _ _ _ _ _ heF hT ih

lemma IsFan.cons' (h : M.IsFan F b c) (heF : e ∉ F)  (hT : (M.bDual !b).IsTriangle
    {e, F.head h.ne_nil, F.tail.head (by grind [length_tail, h.three_le_length])}) :
    M.IsFan (e :: F) (!b) c := by
  cases h with
  | of_isTriangle b e' f g h => exact h.isFan_of_bDual.cons (by grind) hT
  | cons_triangle e' x y F' b c h he'F hT' =>
    simpa using (h.cons he'F hT').cons (by grind) (by simpa using hT)

lemma IsFan.concat (h : M.IsFan F b c) (hT : (M.bDual (!c)).IsTriangle
    {F.dropLast.getLast (by grind [length_dropLast, h.three_le_length]), (F.getLast h.ne_nil), e})
    (heL : e ∉ F) : M.IsFan (F.concat e) b !c := by
  induction h with
  | of_isTriangle b e' f g h => simpa using hT.isFan.cons (by grind) (by simpa)
  | cons_triangle => grind [IsFan.cons]

lemma IsFan.nodup (h : M.IsFan F b c) : F.Nodup := by
  induction h with grind

lemma IsFan.reverse (h : M.IsFan F b c) : M.IsFan F.reverse c b := by
  induction h with
  | of_isTriangle b e f g h => exact h.reverse.isFan_of_bDual
  | cons_triangle e x y F b c h heF hT ih =>
      simpa using ih.concat (by simpa using hT.reverse) (by grind)

@[simp]
lemma isFan_reverse_iff : M.IsFan F.reverse b c ↔ M.IsFan F c b :=
  ⟨fun h ↦ by simpa using h.reverse, IsFan.reverse⟩

lemma IsFan.tail (h : M.IsFan F b c) (hle : 4 ≤ F.length) : M.IsFan F.tail (!b) c := by
  induction h with
  | of_isTriangle => simp at hle
  | cons_triangle => simpa

lemma IsFan.dropLast (h : M.IsFan F b c) (hle : 4 ≤ F.length) : M.IsFan F.dropLast b (!c) := by
  simpa using (h.reverse.tail (by simpa)).reverse

lemma IsFan.drop {k} (h : M.IsFan F b c) (hk : k + 3 ≤ F.length) :
    M.IsFan (F.drop k) (if Even k then b else !b) c := by
  induction k with
  | zero => simpa
  | succ k ih =>
    convert (ih (by grind)).tail (by grind) using 1
    · simp
    grind

lemma IsFan.right_eq (h : M.IsFan F b c) : c = (if Odd F.length then b else !b) := by
  induction h with grind

lemma IsFan.take {k} (h : M.IsFan F b c) (hk : 3 ≤ k) (hkle : k ≤ F.length) :
    M.IsFan (F.take k) b (if Odd k then b else !b) := by
  convert (h.reverse.drop (k := F.length - k) (by grind)).reverse using 1
  · grind [List.drop_reverse]
  obtain ⟨d, h_eq⟩ := exists_add_of_le hkle
  simp only [h_eq, add_tsub_cancel_left, h.right_eq, Nat.odd_add]
  split_ifs <;> grind

lemma IsFan.isNonloop_bDual (h : M.IsFan F b c) (heF : e ∈ F) (d : Bool) :
    (M.bDual d).IsNonloop e := by
  induction h with
  | of_isTriangle b a f g h =>
      simpa using h.isNonloop_bDual_of_mem (by simpa using heF) (b := b != d)
  | cons_triangle a x y F b c h haF hT ih =>
      obtain rfl | hne := mem_cons.1 heF
      · simpa using hT.isNonloop_bDual₁ (b := !(b != d))
      exact ih (by grind)

lemma IsFan.isNonloop (h : M.IsFan F b c) (heF : e ∈ F) : M.IsNonloop e :=
  h.isNonloop_bDual heF false

lemma IsFan.length_bodd_eq (h : M.IsFan F b c) : F.length.bodd = (b == c) := by
  induction h with
  | of_isTriangle => simp
  | cons_triangle e x y F b => cases b with simp_all

lemma IsFan.isTriangle_bDual (h : M.IsFan F b c) : (M.bDual b).IsTriangle
    {F[0]'(by grind [h.three_le_length]), F[1]'(by grind [h.three_le_length]),
    F[2]'(by grind [h.three_le_length])} := by
  induction h with simpa

lemma isFan_cons_iff : M.IsFan (x :: F) b c ↔
    ∃ e f F₀, F = e :: f :: F₀ ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ∉ F₀ ∧
    ((F₀ = [] ∧ b = c) ∨ M.IsFan F (!b) c) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases h with
    | of_isTriangle => simpa
    | cons_triangle e x y F b c h heF hT => simp [hT, heF, h]
  rintro ⟨e, f, F₀, rfl, hT, hx, ⟨rfl, rfl⟩ | hF⟩
  · exact hT.isFan_of_bDual
  simpa using hF.cons hx (by simpa)

lemma IsFan.of_cons (hF : M.IsFan (x :: F) b c) (h : 2 ≤ F.length) : M.IsFan F (!b) c := by
  rw [isFan_cons_iff] at hF


lemma IsFan.isTriangle_get (h : M.IsFan F b c) (i) (hi : i + 2 < F.length) :
    (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  induction h generalizing i with
  | of_isTriangle => simpa [show i = 0 by grind]
  | cons_triangle e x y F b c h heF hT ih =>
    obtain rfl | i := i
    · simpa
    simpa using ih (i := i) (by simpa using hi)

lemma IsFan.recBool₂ {motive : (M : Matroid α) → (F : List α) → (b c : Bool) → M.IsFan F b c → Prop}
    (of_isTriangle : ∀ M e f g d (h : (M.bDual d).IsTriangle {e, f, g}),
      motive M [e, f, g] d d h.isFan_of_bDual)
    (of_quad : ∀ M e f g x d (hT : (M.bDual (!d)).IsTriangle {f, g, x})
      (hT' : (M.bDual d).IsTriangle {e, f, g}) (hex : e ≠ x),
      motive M [e, f, g, x] d (!d)
      (by simpa using hT.isFan.of_bDual.cons (by simpa) (by simpa)))
    (cons_cons : ∀ M e f x y F c d (h : M.IsFan (x :: y :: F) c d)
      (hT : (M.bDual (!c)).IsTriangle {f, x, y}) (hf : f ∉ F)
      (hT' : (M.bDual c).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
      motive M _ _ _ h → motive M _ c d ((h.cons hf hT).cons_not (by grind) hT'))
    (h : M.IsFan F b c) : motive M F b c h := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h.three_le_length
  induction k using Nat.twoStepInduction generalizing F b with
  | zero =>
      obtain ⟨e, f, g, rfl⟩ := length_eq_three.1 <| (add_zero (M := ℕ) _ ▸ hk)
      convert of_isTriangle M e f g b h.isTriangle_bDual
      simp [h.right_eq, show Odd 3 by decide]
  | one =>
      obtain ⟨x, e, f, g, rfl⟩ := length_eq_four.1 <| (add_zero (M := ℕ) _ ▸ hk)
      convert of_quad M x e f g b ?_ h.isTriangle_bDual (by grind [h.nodup])
      · simp [h.right_eq, show Even 4 by decide]
      simpa using h.isTriangle_get 1 (by simp)
  | more n ih _ =>
      obtain ⟨e, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)
      obtain ⟨f, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)

      have hF : M.IsFan F := by simpa using (h.tail (by simp)).tail (by simp)
      -- have hF : F.length = 3 + n := by grind

      -- have aux : F.tail.tail.length = 3 + n := by rw [length_tail, length_tail]; lia
      -- have := cons_cons M (ih ((h.tail (by lia)).tail (by grind)) aux)
      -- rw [← length_tail_add_one, ← length_tail_add_one] at hk
      -- ·
  -- induction hF : F.length using Nat.strong_induction_on generalizing F with
  -- | h n ih =>
  --   _
  -- | of_isTriangle b e f g h => exact of_isTriangle _ _ _ _ _ h
  -- | cons_triangle e x y F b c h heF hT ih =>
  --   induction

#exit


/-- Induct by stripping two layers off the front of a fan to get a fan of the same type. -/
lemma IsFan.recBool₂ {motive : (M : Matroid α) → (L : List α) → (b c : Bool) → M.IsFan F b c → Prop}
    (of_isTriangle : ∀ M e f g d (h : (M.bDual d).IsTriangle {e, f, g}),
      motive M [e, f, g] d d (by simpa using h.isFan))
    (of_quad : ∀ M e f g x d (hT : (M.bDual (!d)).IsTriangle {f, g, x})
      (hT' : (M.bDual d).IsTriangle {e, f, g}) (hex : e ≠ x),
      motive M [e, f, g, x] d (!d)
      (by simpa using hT.isFan.of_bDual.cons (by simpa using hT') (by simpa)))
    (cons_cons : ∀ M e f x y L c d (h : M.IsFan (x :: y :: F) c d)
      (hT : (M.bDual (!c)).IsTriangle {f, x, y}) (hf : f ∉ L)
      (hT' : (M.bDual c).IsTriangle {e, f, x}) (he : e ∉ L) (hey : e ≠ y),
      motive M _ _ _ h → motive M (e :: f :: x :: y :: F) c d
        (by simpa using (h.cons hT hf).cons (by simpa) (by grind)))
    (h : M.IsFan F b c) : motive M L b c h := by
  induction hF : F.length using Nat.strong_induction_on generalizing L with
  | h n ih =>
  match L with
  | [] => grind [h.three_le_length]
  | [e] => grind [h.three_le_length]
  | [e, f] => grind [h.three_le_length]
  | [e, f, g] =>
    obtain rfl : b = c := by simpa using h.length_bodd_eq
    exact of_isTriangle _ _ _ _ _ <| by simpa using h.isTriangle_bDual
  | [e, f, g, x] =>
    obtain rfl : c = !b := by cases b <;> simpa using h.length_bodd_eq
    refine of_quad _ _ _ _ _ _ ?_ h.isTriangle_bDual (by grind [h.nodup])
    simpa using h.isTriangle_get 1 (by simp)
  | e :: f :: x :: y :: z :: F =>
  have hF' : M.IsFan (x :: y :: z :: F) b c := by simpa using (h.tail (by simp)).tail (by simp)
  refine cons_cons _ _ _ _ _ _ _ _ hF' ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using h.isTriangle_get 1 (by simp)
  · grind [h.nodup]
  · exact h.isTriangle_bDual
  · grind [h.nodup]
  · grind [h.nodup]
  exact ih _ (by grind) hF' rfl

lemma IsFan.eq_of_parallel_of_bnot (h : M.IsFan F b (!b)) (hF : 5 ≤ F.length) (he : e ∈ L)
    (hf : f ∈ L) (hef : (M.bDual d).Parallel e f) : e = f := by
  wlog hd : d = false generalizing d b M with aux
  · obtain rfl : d = true := by simpa using hd
    exact aux (M := M✶) (b := !b) (by simpa using h.dual) (by simpa) rfl
  wlog hb : b = true generalizing b L with aux
  · grind [h.reverse]
  subst hb hd
  rw [mem_iff_getElem] at he hf
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hf
  wlog hij : i < j generalizing i j with aux
  · grind [aux j hj i hi hef.symm]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  by_contra hne
  sorry

#exit

  obtain rfl | i := i
  · have h_eq :=
      (h.isTriangle_bDual).mem_or_mem_of_isCircuit_bDual (hef.isCircuit_of_ne hne) (by simp)
    obtain (rfl | rfl) : k = 0 ∨ k = 1 := by simpa [h.nodup.getElem_inj_iff] using h_eq
    · have := h.isTriangle_bDual.in
    -- simp only [zero_add, Set.mem_insert_iff, mem_singleton_iff] at h_eq
    -- simp [h.nodup.getElem_inj_iff] at h_eq
    -- simp at hne











lemma IsFan.indep_alt (h : M.IsFan F b c) (d : Bool)
    (h_ind : (M.bDual d).Indep {(F.alt d).head h.alt_ne_nil, (F.alt d).getLast h.alt_ne_nil}) :
    (M.bDual d).Indep {x | x ∈ F.alt d} := by
  wlog hd : d = false generalizing d M b c with aux
  · obtain rfl : d = true := by grind
    simp at h_ind
    specialize aux h.dual false
    simp at aux
  induction h using IsFan.recBool₂ with
  | of_isTriangle M e f g b h =>
    cases d
    · simp [h.isNonloop_of_bDual₂]
    simpa using h_ind
  | of_quad M e f g x b hT hT' hex => cases d <;> simpa [alt_head] using h_ind
  | cons_cons M e f x y L b c h hT hf hT' he hey ih =>
    cases d with
    | false =>
      simp_all [setOf_or]
    | true =>
      simp_all

structure Fan (M : Matroid α) where
  b₀ : Bool
  b₁ : Bool
  toList : List α
  isFan : M.IsFan toList b₀ b₁

namespace Fan

instance {M : Matroid α} : CoeOut M.Fan (List α) where
  coe := Fan.toList

attribute [coe] Fan.toList

@[ext]
protected lemma ext {F₁ F₂ : M.Fan} (h : (F₁ : List α) = F₂) (hb₀ : F₁.b₀ = F₂.b₀) :
    F₁ = F₂ := by
  obtain ⟨b₀, b₁, L, hF⟩ := F₁
  obtain ⟨b₀', b₁', L', hF'⟩ := F₂
  obtain rfl : L' = L := h.symm
  obtain rfl : b₀' = b₀ := hb₀.symm
  simp [hF.right_eq, hF'.right_eq]

@[simp]
lemma toList_eq_coe (F : M.Fan) : F.toList = F := rfl

protected def fst (F : M.Fan) := (F : List α).head F.isFan.ne_nil

@[simp] lemma fst_mk (L b) (h : M.IsFan F b c) :
  (Fan.mk b c L h).fst = F.head h.ne_nil := rfl

protected def snd (F : M.Fan) := (F : List α)[1]'(by grind [F.isFan.three_le_length])

@[simp] lemma snd_mk (L b) (h : M.IsFan F b c) :
    (Fan.mk b c L h).snd = L[1]'(by grind [h.three_le_length]) := rfl

protected def thd (F : M.Fan) := (F : List α)[2]'(by grind [F.isFan.three_le_length])

@[simp] lemma thd_mk (L b) (h : M.IsFan F b c) :
    (Fan.mk b c L h).thd = L[2]'(by grind [h.three_le_length]) := rfl

protected def last (F : M.Fan) := (F : List α).getLast F.isFan.ne_nil

/-- `F.joints false` are the joints of `F`, and `F.joints true` are the cojoints.  -/
protected def joints (F : M.Fan) (b : Bool) := (F : List α).alt (b == F.b₀)

@[simp]
lemma mk_joints (h : M.IsFan F b c) : (Fan.mk b c L h).joints = fun d ↦ F.alt (d == b) := rfl

lemma fst_mem_joints (F : M.Fan) : F.fst ∈ F.joints F.b₀ := by
  obtain ⟨b₀, -, L, h⟩ := F
  cases L with simp

@[simps]
def _root_.Matroid.IsTriangle.toFan (h : M.IsTriangle {e, f, g}) : M.Fan where
  b₀ := false
  b₁ := false
  toList := [e, f, g]
  isFan := IsFan.of_isTriangle M e f g h

@[simps]
protected def dual (F : M.Fan) : M✶.Fan where
  b₀ := !F.b₀
  b₁ := !F.b₁
  toList := F.toList
  isFan := by simpa using F.isFan

@[simp]
lemma mk_dual (h : M.IsFan F b c) : (Fan.mk b c L h).dual = (Fan.mk _ _ L h.dual) := rfl

@[simps]
protected def copy {N : Matroid α} (F : M.Fan) (hMN : M = N) : N.Fan where
  b₀ := F.b₀
  b₁ := F.b₁
  toList := F.toList
  isFan := hMN ▸ F.isFan

@[simp]
lemma dual_copy {N : Matroid α} (F : M.Fan) (h : M = N) :
    (F.copy h).dual = F.dual.copy (show M✶ = N✶ by rw [h]) := by
  ext <;> rfl

@[simp]
lemma dual_joints (F : M.Fan) : F.dual.joints = fun b ↦ F.joints (!b) := by
  obtain ⟨b₀, b₁, L, h⟩ := F
  simp only [mk_dual, mk_joints]
  convert rfl using 2 with i
  cases i <;> simp

@[simps!]
protected def ofDual (F : M✶.Fan) : M.Fan := F.dual.copy M.dual_dual

@[simp]
lemma ofDual_copy {N : Matroid α} (F : M✶.Fan) (h : M✶ = N✶) :
    (F.copy h).ofDual = F.ofDual.copy (show M = N from dual_inj.1 h) := by
  ext <;> rfl

def ofBDual (F : (M.bDual b).Fan) : M.Fan :=
  Bool.dcond b (fun hb ↦ (F.copy (by simp [hb])).ofDual) (fun hb ↦ F.copy (by simp [hb]))

@[simp]
lemma ofBDual_toList (F : (M.bDual b).Fan) : F.ofBDual.toList = F.toList := by
  cases b <;> simp [ofBDual, Bool.dcond]

@[simp]
lemma ofBDual_b₀ (F : (M.bDual b).Fan) : F.ofBDual.b₀ = (F.b₀ != b) := by
  cases b <;> simp [ofBDual, Bool.dcond]

@[simp]
lemma ofBDual_b₁ (F : (M.bDual b).Fan) : F.ofBDual.b₁ = (F.b₁ != b) := by
  cases b <;> simp [ofBDual, Bool.dcond]

@[simps]
protected def cons (F : M.Fan) (h : (M.bDual !F.b₀).IsTriangle {e, F.fst, F.snd})
    (heF : e ∉ F.toList) : M.Fan where
  b₀ := !F.b₀
  b₁ := F.b₁
  toList := e :: F.toList
  isFan := F.isFan.cons' (by simpa using h) heF

@[simps b₁]
protected def tail (F : M.Fan) : M.Fan where
  b₀ := if 4 ≤ (F : List α).length then !F.b₀ else F.b₀
  b₁ := F.b₁
  toList := if 4 ≤ (F : List α).length then (F : List α).tail else F
  isFan := by
    split_ifs with h
    · exact F.isFan.tail h
    exact F.isFan

lemma tail_left_eq {F : M.Fan} (h : 4 ≤ (F : List α).length) : F.tail.b₀ = !F.b₀ := by
  simpa [Fan.tail]

lemma tail_toList_eq {F : M.Fan} (h : 4 ≤ (F : List α).length) : F.tail.toList = F.toList.tail := by
  simp [Fan.tail, h]

lemma tail_tail_toList_eq {F : M.Fan} (h : 5 ≤ (F : List α).length) :
    F.tail.tail.toList = F.toList.tail.tail := by
  grind [tail_toList_eq]

@[simps]
def reverse (F : M.Fan) : M.Fan where
  b₀ := F.b₁
  b₁ := F.b₀
  toList := F.toList.reverse
  isFan := F.isFan.reverse

@[simp]
lemma reverse_dual (F : M.Fan) : F.reverse.dual = F.dual.reverse := by
  ext <;> simp

@[simp]
lemma length_bodd_eq (F : M.Fan) : F.toList.length.bodd = (F.b₀ == F.b₁) :=
  F.isFan.length_bodd_eq

@[simp]
lemma reverse_joints (F : M.Fan) (d : Bool) : F.reverse.joints d = (F.joints d).reverse := by
  obtain ⟨b, c, F, h⟩ := F
  cases b with cases d <;> simp [reverse, mk_joints, h.length_bodd_eq, alt_reverse]

lemma joints_ne_nil (F : M.Fan) {d : Bool} : F.joints d ≠ [] := by
  obtain ⟨b₀, b₁, F, h⟩ := F
  induction h generalizing d with cases d <;> simp_all

def firstJoint (F : M.Fan) (d : Bool) : α := (F.joints d).head <| F.joints_ne_nil

def lastJoint (F : M.Fan) (d : Bool) : α := (F.joints d).getLast <| F.joints_ne_nil

lemma joints_sublist (F : M.Fan) {d : Bool} : F.joints d <+ F.toList :=
  F.toList.alt_sublist _

lemma isTriangle_bDual (F : M.Fan) {k : ℕ} (hk : k + 2 < F.toList.length) :
    (M.bDual (F.b₀ != k.bodd)).IsTriangle {F.toList[k], F.toList[k + 1], F.toList[k + 2]} := by
  obtain ⟨b₀, b₁, F, h⟩ := F
  induction h generalizing k with
  | of_isTriangle => simpa [show k = 0 by grind]
  | of_dual' M L b h ih => simp_all
  | cons_triangle M e x y J b h heJ hT ih =>
    obtain rfl | k := k
    · simpa
    simpa using ih (k := k) (by simpa using hk)

def IsJoint (F : M.Fan) (e : α) (d : Bool) : Prop := e ∈ F.joints d

/-- The list beginning and ending with the `d`-joints in positions `p` and `q` respectively,
having all the `!d`-joints between them in the fan between them in the list.
This is a circuit of `M.bDual d`. -/
def circuitSublist (F : M.Fan) (d : Bool) {p q : ℕ} (hpq : p < q) (hq : q < (F.joints d).length) :
    List α :=
  ((F.joints d)[p] :: (F.joints (!d)).extract (p + bif (F.b₀ == d) then 0 else 1)
    (q + bif (F.b₀ == d) then 0 else 1)).concat (F.joints d)[q]

/-- Every circuit intersects every nontrivial fan in an interval of cojoints,
and possibly one or two joints at the ends of the interval. -/
lemma foo (F : M.Fan) (hlen : 4 ≤ (F : List α).length) {C : Set α} (hC : (M.bDual d).IsCircuit C) :
    ∃ (p q : ℕ), ∀ (i : ℕ) (hi : i < (F : List α).length),
      (i.bodd = !d → ((F : List α)[i] ∈ C ↔ p ≤ i ∧ i < q))
    ∧ (q ≤ p → (q = 0) ∧ (p + 1 = (F : List α).length))
    ∧ (i.bodd = d → (F : List α)[i] ∈ C → i = p ∨ i = q)
    ∧ (∃ (_ : p ≤ q) (_ : q < (F : List α).length),
      (F : List α)[p] ∈ C → (F : List α)[q] ∈ C → C ⊆ {x | x ∈ (F : List α)}) := by
  sorry
  --   (∃ p, p.bodd = d ∧ ∀ i (hi : i < F.toList.length) (lt : Bool),
  --     F.toList[i] ∈ C ↔ i = p ∨ (i.bodd = !d ∧ lt = (i < p))

  --   ∨ (∃ (p q : ℕ) (hpq : p < q) (hq : q < (F.joints d).length),
  --     C = {x | x ∈ F.circuitSublist d hpq hq}) ∨ C = {x | x ∈ F.joints !d} := by
  -- obtain ⟨b, c, L, hF⟩ := F
  -- simp only [fst_mk, mk_joints]
  -- induction hlen' : F.toList.length using
  -- induction hF using IsFan.recBool with
  -- | of_isTriangle => simp at hlen
  -- | cons M e x' y' L d' c hF hT hne _ =>
  --   simp_all
  -- induction hF with
  -- | of_isTriangle M e f g h => sorry
  -- | of_dual' M L b h ih => sorry
  -- | cons_triangle M e x y J b h heJ hT ih => sorry



-- lemma IsFan.indep_bDual (h : M.IsFan J b c) (d : Bool) (hd : ¬ (b = c ∧ c = d)) :
--     (M.bDual d).Indep {x | x ∈ J d} := by



-- lemma Fan.indep_joints_of_not_parallel  (F : M.Fan) (d : Bool)
--     (hd : ¬ (M.bDual d).Parallel (F.firstJoint d) (F.lastJoint d)) :
--     (M.bDual d).Indep {x | x ∈ F.joints d} := by
--   rw [indep_iff_forall_subset_not_isCircuit']
--   -- have := F.joints_sub


#exit
lemma Fan.indep_bDual  (F : M.Fan) (d : Bool) (hd : ¬ (F.b₀ = F.b₁ ∧ F.b₁ = d)) :
    (M.bDual d).Indep {x | x ∈ F.joints d} := by
  obtain ⟨b, c, F, h⟩ := F
  simp_all only [not_and, mk_joints]
  wlog hcd : d = !c generalizing F b c d with aux
  · obtain rfl : d = c := by simpa using hcd
    obtain rfl : b = !d := by cases b <;> grind
    convert aux d _ _ _ h.reverse (by grind) (by grind) using 1
    simp [reverse_alt, h.length_bodd_eq]
  subst hcd
  clear hd
  induction h with
  | of_isTriangle M e f g h =>
    sorry
  | of_dual' M L b h ih => simp_all
  | cons_triangle M e x y J b h heJ hT ih =>
    simp_all
    cases b
    · simp_all
    simp_all
    have := h.isTriangle_bDual
    simp at this
    -- rw [isFan_cons_cons_iff] at h









          -- simpa using aux F.dual false (by grind) rfl




      --   toList := F.toList.tail
      --   toFanAux := by
      --     obtain ⟨b, L, hF⟩ := F
      --     simp only
      --     induction hF with
      --     | of_isTriangle M e f g h =>
      --       simp at h
      --     | of_dual' M L h ih =>
      --       simp
      --     | cons_triangle M e x y J h heJ hT ih => sorry


  -- simp only [mk_joints] at hd ⊢
  -- wlog hdf : d = false generalizing M b c d F with aux
  -- · obtain rfl : d = true := by simpa using hdf
  --   simpa using aux (M := M✶) false _ _ _ h.dual (by grind) rfl
  -- subst hdf
  -- wlog ht : b = true generalizing F b c with aux
  -- · obtain rfl : b = false := by simpa using ht
  --   obtain rfl : c = true := by simpa using hd
  --   simpa [List.reverse_alt, h.length_bodd_eq] using aux _ _ _ h.reverse (by simp) rfl
  -- subst ht
  -- clear hd
  -- simp only [bDual_false, beq_true]
  -- induction h with
  -- | of_isTriangle M e f g h => sorry
  -- | of_dual' M L b h ih => sorry
  -- | cons_triangle M e x y J b h heJ hT ih => sorry
    -- convert aux false _ _  h.reverse (by grind) rfl (by grind) using 1








--     · simpa using this
--     · sorry
--     sorry





    -- simpa using aux F.dual false (by grind) rfl




--   toList := F.toList.tail
--   toFanAux := by
--     obtain ⟨b, L, hF⟩ := F
--     simp only
--     induction hF with
--     | of_isTriangle M e f g h =>
--       simp at h
--     | of_dual' M L h ih =>
--       simp
--     | cons_triangle M e x y J h heJ hT ih => sorry
