import Matroid.Connectivity.Triangle

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
    (x :: L).alt b = bif b then x :: L.alt (!b) else L.alt (!b) := by
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
    d.dcond (fun _ ↦ e) (fun hd ↦ L.head (fun hL ↦ by simp [hL, hd] at h)) := by
  cases L with | _ => cases d <;> simp_all [Bool.dcond]

lemma List.alt_head {L : List α} {hL : L.alt d ≠ []} :
    (L.alt d).head hL = d.dcond (fun _ ↦ L.head (by rintro rfl; simp at hL))
      (fun hd ↦ L[1]'(by
        subst hd
        match L with
        | [] => simp at hL
        | [x] => simp at hL
        | _ :: _ :: L => simp)) := by
  match L with
  | [] => simp at hL
  | e :: L =>
    rw [L.alt_head_cons]
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

lemma List.Nodup.alt_disjoint (hL : L.Nodup) : Disjoint (L.alt false) (L.alt true) := by
  induction hL with
  | nil => simp
  | @cons a L h1 h2 hdj =>
    simp [show a ∉ L.alt true from fun hmem ↦ h1 a ((L.alt_sublist true).mem hmem) rfl, hdj.symm]

lemma List.alt_concat (L : List α) (x : α) (b : Bool) :
    (L.concat x).alt b = bif L.length.bodd == b then L.alt b else (L.alt b).concat x := by
  induction L generalizing b with cases b <;> simp_all [Bool.apply_cond]

lemma List.alt_reverse (L : List α) (b : Bool) :
    (L.alt b).reverse = L.reverse.alt (bif L.length.bodd then b else !b) := by
  induction L generalizing b with cases b <;> simp_all [← List.concat_eq_append, List.alt_concat]

lemma List.reverse_alt (L : List α) (b : Bool) :
    L.reverse.alt b = (L.alt (bif L.length.bodd then b else !b)).reverse := by
  cases b <;> simp [L.alt_reverse]

namespace Matroid

variable {J : Bool → List α}


variable {L : List α} {b c : Bool}

/-- A fan of a matroid `M` is a sequence `[e₀, f₀, e₁, f₁, ...]` of distinct elements of `M`,
where consecutive triples alternate between being triangles and being triads.
The fan may start and end with either triangles or triads;
if each pair of consecutive `eᵢ` belongs to a common triangle,
then the `eᵢ` are the 'joints' of the fan, and the `fᵢ` are 'cojoints'.

Formally, if `J : Bool → List α` and `b c : Bool`, the predicate `M.IsFan J b c` means that
`J false` is the list of joints, `J true` is the list of cojoints, and `b c` indicate respectively
whether the first element is a cojoint, and whether the last element is a cojoint.

For example, if `{e,f,g}` is a triangle of `M`, then the fan `e, f, g` corresponds to the
statement `M.IsFan J false false`, with `J false = [e, g]` and `J true = [g]`.
(The `false false` means that the fan begins and ends on joints.)

If, additionally, `{f,g,h}` is a triad of `M`, then the fan `e, f, g, h` corresponds to the
statement `M.IsFan J false true`, with `J false = [e,g]` and `J true = [h,f]`. -/
inductive IsFan : Matroid α → List α → Bool → Bool → Prop
  | of_isTriangle (M e f g) (h : M.IsTriangle {e, f, g}) : IsFan M [e, f, g] false false
  | of_dual' (M L b) (h : IsFan M✶ L false (!b)) : IsFan M L true b
  | cons_triangle (M e x y J b) (h : IsFan M (x :: y :: J) true b) (heJ : e ∉ J)
      (hT : M.IsTriangle {e, x, y}) : IsFan M (e :: x :: y :: J) false b

lemma IsFan.dual (h : M.IsFan L b c) : M✶.IsFan L (!b) !c := by
  induction h with
  | of_isTriangle M e f g h => exact IsFan.of_dual' _ _ _ <| by simpa using of_isTriangle _ _ _ _ h
  | of_dual' => simpa
  | cons_triangle M e x y J b h heJ hT ih =>
    exact IsFan.of_dual' _ _ _
      <| by simpa using IsFan.cons_triangle M e x y J _ (IsFan.of_dual' _ _ _ ih) heJ hT

lemma IsTriangle.isFan (h : M.IsTriangle {e, f, g}) : M.IsFan [e, f, g] false false :=
    IsFan.of_isTriangle  _ _ _ _ h

@[simp]
lemma isFan_dual_iff : M✶.IsFan L b c ↔ M.IsFan L (!b) !c :=
  ⟨fun h ↦ M.dual_dual ▸ h.dual, fun h ↦ b.not_not ▸ c.not_not ▸ h.dual⟩

lemma isFan_dual_bnot_iff : M✶.IsFan L (!b) (!c) ↔ M.IsFan L b c := by
  simp

lemma IsFan.of_dual (h : M✶.IsFan L b c) : M.IsFan L (!b) (!c) :=
  isFan_dual_iff.1 h

@[simp]
lemma isFan_bDual_iff : (M.bDual d).IsFan L b c ↔ M.IsFan L (b != d) (c != d) := by
  cases d with simp

alias ⟨IsFan.of_bDual, _⟩ := isFan_bDual_iff

lemma IsFan.three_le_length (h : M.IsFan L b c) : 3 ≤ L.length := by
  induction h with simp_all

lemma IsFan.ne_nil (h : M.IsFan L b c) : L ≠ [] := by
  grind [h.three_le_length]

lemma IsFan.alt_ne_nil (h : M.IsFan L b c) {d} : L.alt d ≠ [] := by
  cases d <;> grind [L.alt_true_length_eq, h.three_le_length, L.alt_length_add]

lemma IsFan.cons {x y : α} (h : M.IsFan (x :: y :: L) b c) (hT : (M.bDual !b).IsTriangle {e, x, y})
    (heL : e ∉ L) : M.IsFan (e :: x :: y :: L) (!b) c := by
  cases b
  · simpa using (IsFan.cons_triangle _ _ _ _ _ _ h.dual heL (by simpa using hT)).dual
  exact IsFan.cons_triangle _ _ _ _ _ _ h heL (by simpa using hT)

lemma IsFan.cons' (h : M.IsFan L b c) (hT : (M.bDual !b).IsTriangle
    {e, L.head h.ne_nil, L.tail.head (by grind [length_tail, h.three_le_length])}) (heL : e ∉ L) :
    M.IsFan (e :: L) (!b) c := by
  match L with
  | nil => simpa using h.ne_nil
  | [x] => simpa using h.three_le_length
  | x :: y :: L => exact h.cons hT (by grind)

lemma IsFan.concat (h : M.IsFan L b c) (hT : (M.bDual (!c)).IsTriangle
    {L.dropLast.getLast (by grind [length_dropLast, h.three_le_length]), (L.getLast h.ne_nil), e})
    (heL : e ∉ L) : M.IsFan (L.concat e) b !c := by
  induction h with
  | of_isTriangle M e' f g h =>
    simpa using ((IsFan.of_isTriangle _ _ _ _ hT).cons (by simpa) (by grind)).dual
  | of_dual' => simp_all
  | cons_triangle M e' x y J b h heJ hT' ih => exact (ih hT (by grind)).cons hT' (by grind)

lemma IsFan.nodup (h : M.IsFan L b c) : L.Nodup := by
  induction h with
  | of_isTriangle M e f g h => simp [h.ne₁₂, h.ne₁₃, h.ne₂₃]
  | of_dual' => assumption
  | cons_triangle M e x y J c h heJ hT ih => simp_all [hT.ne₁₂, hT.ne₁₃, hT.ne₂₃]

lemma IsFan.reverse (h : M.IsFan L b c) : M.IsFan L.reverse c b := by
  induction h with
  | of_isTriangle M e f g h => exact h.reverse.isFan
  | of_dual' M L b h ih => simpa using ih.of_dual
  | cons_triangle M e x y J b h heJ hT ih =>
    convert ih.concat (e := e) (by simpa using hT.reverse) (by simp [heJ, hT.ne₁₃, hT.ne₁₂])
    simp

lemma IsFan.tail (h : M.IsFan L b c) (hle : 4 ≤ L.length) : M.IsFan L.tail (!b) c := by
  induction h with
  | of_isTriangle => simp at hle
  | of_dual' M L b h ih => simpa using (ih hle).of_dual
  | cons_triangle => simpa

lemma IsFan.dropLast (h : M.IsFan L b c) (hle : 4 ≤ L.length) : M.IsFan L.dropLast b (!c) := by
  simpa using (h.reverse.tail (by simpa)).reverse

lemma IsFan.drop {k} (h : M.IsFan L b c) (hk : k + 3 ≤ L.length) :
    M.IsFan (L.drop k) (if Even k then b else !b) c := by
  induction k with
  | zero => simpa
  | succ k ih =>
    convert (ih (by grind)).tail (by grind) using 1
    · simp
    grind

lemma IsFan.right_eq (h : M.IsFan L b c) : c = (if Odd L.length then b else !b) := by
  induction h with grind

lemma IsFan.take {k} (h : M.IsFan L b c) (hk : 3 ≤ k) (hkle : k ≤ L.length) :
    M.IsFan (L.take k) b (if Odd k then b else !b) := by
  convert (h.reverse.drop (k := L.length - k) (by grind)).reverse using 1
  · grind [List.drop_reverse]
  obtain ⟨d, h_eq⟩ := exists_add_of_le hkle
  simp only [h_eq, add_tsub_cancel_left, h.right_eq, Nat.odd_add]
  split_ifs <;> grind

lemma IsFan.isNonloop_bDual (h : M.IsFan L b c) (heL : e ∈ L) (d : Bool) :
    (M.bDual d).IsNonloop e := by
  induction h generalizing d with
  | of_isTriangle M x f g h => exact h.isNonloop_bDual_of_mem <| by simpa using heL
  | of_dual' M L b h ih => simpa using ih heL (!d)
  | cons_triangle M e' x y J b h heJ hT' ih =>
    obtain rfl | heL := mem_cons.1 heL
    · exact hT'.isNonloop_bDual_of_mem <| by simp
    exact ih heL d

lemma IsFan.isNonloop (h : M.IsFan L b c) (heL : e ∈ L) : M.IsNonloop e :=
  h.isNonloop_bDual heL false

lemma IsFan.length_bodd_eq (h : M.IsFan L b c) : L.length.bodd = (b == c) := by
  induction h with simp_all

lemma IsFan.isTriangle_bDual (h : M.IsFan L b c) : (M.bDual b).IsTriangle
    {L[0]'(by grind [h.three_le_length]), L[1]'(by grind [h.three_le_length]),
    L[2]'(by grind [h.three_le_length])} := by
  induction h with
  | of_dual' M L b h ih => simpa using ih
  | _ => simpa

lemma isFan_cons_iff : M.IsFan (x :: L) b c ↔
    ∃ e f L₀, L = e :: f :: L₀ ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ∉ L₀ ∧
    ((L₀ = [] ∧ b = c) ∨ M.IsFan L (!b) c) := by
  match L with
  | [] => exact iff_of_false (fun h ↦ by grind [h.three_le_length]) <| by grind
  | [_] => exact iff_of_false (fun h ↦ by grind [h.three_le_length]) <| by grind
  | e :: f :: L₀ =>
  simp only [cons.injEq, ↓existsAndEq, and_true, exists_eq_left']
  refine ⟨fun h ↦ ⟨by simpa using h.isTriangle_bDual, by grind [h.nodup], ?_⟩, fun h ↦ ?_⟩
  · cases L₀ with
    | nil => simp [show b = c by simpa using h.length_bodd_eq]
    | cons g L₀ => simpa using h.tail (by grind)
  obtain ⟨hT, hx, ⟨rfl, rfl⟩ | hf⟩ := h
  · simpa using hT.isFan
  simpa using hf.cons (e := x) (by simpa) hx

lemma IsFan.recBool {motive : (M : Matroid α) → (L : List α) → (b c : Bool) → M.IsFan L b c → Prop}
    (of_isTriangle : ∀ M e f g d (h : (M.bDual d).IsTriangle {e, f, g}),
      motive M [e, f, g] d d (by simpa using h.isFan))
    (cons : ∀ M e x y L d c (hL : M.IsFan (x :: y :: L) (!d) c)
      (hT : (M.bDual d).IsTriangle {e, x, y}) (hne : e ∉ L), motive M (x :: y :: L) _ _ hL →
      motive M (e :: x :: y :: L) d c (by simpa using hL.cons (by simpa using hT) hne))
    (h : M.IsFan L b c) : motive M L b c h := by
  induction hL : L.length generalizing b L with
  | zero => grind [h.three_le_length]
  | succ n ih =>
    cases L with
    | nil => simp at hL
    | cons x L =>
      obtain ⟨e, f, L₀, rfl, hT, hX, ⟨rfl, rfl⟩ | h'⟩ := isFan_cons_iff.1 h
      · apply of_isTriangle
        simpa using h.isTriangle_bDual
      apply cons _ _ _ _ _ _ _ h' (by simpa) hX
      cases L₀ with
      | nil => grind [h'.three_le_length]
      | cons g L₀ => apply ih; simp_all

lemma IsFan.isTriangle_get (h : M.IsFan L b c) (i) (hi : i + 2 < L.length) :
    (M.bDual (b != i.bodd)).IsTriangle {L[i], L[i + 1], L[i + 2]} := by
  induction h using IsFan.recBool generalizing i with
  | of_isTriangle => simpa [show i = 0 by grind]
  | cons M e x y L d c hL hT hne ih =>
    obtain rfl | i := i
    · simpa
    simpa using ih (i := i) (by simpa using hi)

/-- Induct by stripping two layers off the front of a fan to get a fan of the same type. -/
lemma IsFan.recBool₂ {motive : (M : Matroid α) → (L : List α) → (b c : Bool) → M.IsFan L b c → Prop}
    (of_isTriangle : ∀ M e f g d (h : (M.bDual d).IsTriangle {e, f, g}),
      motive M [e, f, g] d d (by simpa using h.isFan))
    (of_quad : ∀ M e f g x d (hT : (M.bDual (!d)).IsTriangle {f, g, x})
      (hT' : (M.bDual d).IsTriangle {e, f, g}) (hex : e ≠ x),
      motive M [e, f, g, x] d (!d)
      (by simpa using hT.isFan.of_bDual.cons (by simpa using hT') (by simpa)))
    (cons_cons : ∀ M e f x y L c d (h : M.IsFan (x :: y :: L) c d)
      (hT : (M.bDual (!c)).IsTriangle {f, x, y}) (hf : f ∉ L)
      (hT' : (M.bDual c).IsTriangle {e, f, x}) (he : e ∉ L) (hey : e ≠ y),
      motive M _ _ _ h → motive M (e :: f :: x :: y :: L) c d
        (by simpa using (h.cons hT hf).cons (by simpa) (by grind)))
    (h : M.IsFan L b c) : motive M L b c h := by
  induction hL : L.length using Nat.strong_induction_on generalizing L with
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
  | e :: f :: x :: y :: z :: L =>
  have hL' : M.IsFan (x :: y :: z :: L) b c := by simpa using (h.tail (by simp)).tail (by simp)
  refine cons_cons _ _ _ _ _ _ _ _ hL' ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using h.isTriangle_get 1 (by simp)
  · grind [h.nodup]
  · exact h.isTriangle_bDual
  · grind [h.nodup]
  · grind [h.nodup]
  exact ih _ (by grind) hL' rfl

lemma IsFan.eq_of_parallel_of_bnot (h : M.IsFan L b (!b)) (hL : 5 ≤ L.length) (he : e ∈ L)
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

  obtain rfl | i := i
  · have h_eq :=
      (h.isTriangle_bDual).mem_or_mem_of_isCircuit_bDual (hef.isCircuit_of_ne hne) (by simp)
    obtain (rfl | rfl) : k = 0 ∨ k = 1 := by simpa [h.nodup.getElem_inj_iff] using h_eq
    · have := h.isTriangle_bDual.in
    -- simp only [zero_add, Set.mem_insert_iff, mem_singleton_iff] at h_eq
    -- simp [h.nodup.getElem_inj_iff] at h_eq
    -- simp at hne











lemma IsFan.indep_alt (h : M.IsFan L b c) (d : Bool)
    (h_ind : (M.bDual d).Indep {(L.alt d).head h.alt_ne_nil, (L.alt d).getLast h.alt_ne_nil}) :
    (M.bDual d).Indep {x | x ∈ L.alt d} := by
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
  obtain ⟨b₀, b₁, L, hL⟩ := F₁
  obtain ⟨b₀', b₁', L', hL'⟩ := F₂
  obtain rfl : L' = L := h.symm
  obtain rfl : b₀' = b₀ := hb₀.symm
  simp [hL.right_eq, hL'.right_eq]

@[simp]
lemma toList_eq_coe (F : M.Fan) : F.toList = F := rfl

protected def fst (F : M.Fan) := (F : List α).head F.isFan.ne_nil

@[simp] lemma fst_mk (L b) (h : M.IsFan L b c) :
  (Fan.mk b c L h).fst = L.head h.ne_nil := rfl

protected def snd (F : M.Fan) := (F : List α)[1]'(by grind [F.isFan.three_le_length])

@[simp] lemma snd_mk (L b) (h : M.IsFan L b c) :
    (Fan.mk b c L h).snd = L[1]'(by grind [h.three_le_length]) := rfl

protected def thd (F : M.Fan) := (F : List α)[2]'(by grind [F.isFan.three_le_length])

@[simp] lemma thd_mk (L b) (h : M.IsFan L b c) :
    (Fan.mk b c L h).thd = L[2]'(by grind [h.three_le_length]) := rfl

protected def last (F : M.Fan) := (F : List α).getLast F.isFan.ne_nil

/-- `F.joints false` are the joints of `F`, and `F.joints true` are the cojoints.  -/
protected def joints (F : M.Fan) (b : Bool) := (F : List α).alt (b == F.b₀)

@[simp]
lemma mk_joints (h : M.IsFan L b c) : (Fan.mk b c L h).joints = fun d ↦ L.alt (d == b) := rfl

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
lemma mk_dual (h : M.IsFan L b c) : (Fan.mk b c L h).dual = (Fan.mk _ _ L h.dual) := rfl

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
  -- obtain ⟨b, c, L, hL⟩ := F
  -- simp only [fst_mk, mk_joints]
  -- induction hlen' : F.toList.length using
  -- induction hL using IsFan.recBool with
  -- | of_isTriangle => simp at hlen
  -- | cons M e x' y' L d' c hL hT hne _ =>
  --   simp_all
  -- induction hL with
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
      --     obtain ⟨b, L, hL⟩ := F
      --     simp only
      --     induction hL with
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
--     obtain ⟨b, L, hL⟩ := F
--     simp only
--     induction hL with
--     | of_isTriangle M e f g h =>
--       simp at h
--     | of_dual' M L h ih =>
--       simp
--     | cons_triangle M e x y J h heJ hT ih => sorry
