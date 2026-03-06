import Matroid.Connectivity.Separation.Tutte
import Matroid.ForMathlib.List
import Matroid.ForMathlib.Parity

set_option linter.style.longLine false

open Set List

namespace Matroid

-- variable {J : Bool → List α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {F J : List α} {b c : Bool} {L : List ℕ}

/-- A fan of a matroid `M` is a sequence `[e₀, f₀, e₁, f₁, ...]` of at least two
distinct elements of `M`, where consecutive triples alternate between being triangles and triads.
We allow fans to have length two for technical reasons; in a fan of length `2`, we
insist that neither element is a loop or coloop.

The fan may start and end with either triangles or triads;
if each pair of consecutive `eᵢ` belongs to a common triangle,
then the `eᵢ` are the 'joints' of the fan, and the `fᵢ` are 'cojoints'.

Formally, the predicate `M.IsFan J b c` means that `J` is the list of elements, and `b c` are
boolean variables indicating whether the fan respectively starts and ends with a triangle.
We have `b = c` if and only if `J` had odd length.

For example, if `{e,f,g}` is a triangle of `M`, then the fan `e, f, g` corresponds to the
statement `M.IsFan [e, f, g] false false`.
(The `false false` means that the fan begins and ends on joints.)

If, additionally, `{f, g, h}` is a triad of `M`, then the fan `e, f, g, h` corresponds to the
statement `M.IsFan [e, f, g, h] false true`. -/
inductive IsFan : Matroid α → List α → Bool → Bool → Prop
  | of_pair (M b e f) (he : ∀ i, (M.bDual i).IsNonloop e)
      (hf : ∀ i, (M.bDual i).IsNonloop f) (hne : e ≠ f) : IsFan M [e, f] b (!b)
  | cons_triangle (M e x y F b c) (h : IsFan M (x :: y :: F) b c) (heF : e ∉ F)
      (hT : (M.bDual (!b)).IsTriangle {e, x, y}) : IsFan M (e :: x :: y :: F) (!b) c

lemma IsFan.cons (h : M.IsFan (x :: y :: F) b c) (heF : e ∉ F)
    (hT : (M.bDual (!b)).IsTriangle {e, x, y}) : M.IsFan (e :: x :: y :: F) (!b) c := by
  apply IsFan.cons_triangle <;> assumption

lemma IsFan.cons_not (h : M.IsFan (x :: y :: F) (!b) c) (heF : e ∉ F)
    (hT : (M.bDual b).IsTriangle {e, x, y}) : M.IsFan (e :: x :: y :: F) b c := by
  simpa using h.cons heF (by simpa)

lemma isFan_pair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) {b} : M.IsFan [e, f] b (!b) :=
  IsFan.of_pair _ _ _ _ he hf hef

lemma isFan_pair_not (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) {b} : M.IsFan [e, f] (!b) b :=
  by simpa using isFan_pair he hf hef (b := !b)

lemma IsTriangle.isFan_of_bDual (h : (M.bDual b).IsTriangle {e, f, g}) : M.IsFan [e, f, g] b b := by
  refine (isFan_pair_not ?_ ?_ h.ne₂₃).cons_not (by simp) h
  · exact fun i ↦ by simpa using h.isNonloop_bDual₂ (b := b != i)
  exact fun i ↦ by simpa using h.isNonloop_bDual₃ (b := b != i)

lemma IsTriangle.isFan (h : M.IsTriangle {e, f, g}) : M.IsFan [e, f, g] false false :=
  IsTriangle.isFan_of_bDual (b := false) h

lemma IsFan.dual (h : M.IsFan F b c) : M✶.IsFan F (!b) (!c) := by
  induction h with
  | of_pair b e f he hf hef =>
      exact isFan_pair (by simpa [and_comm] using he) (by simpa [and_comm] using hf) hef
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

lemma IsFan.bDual (h : M.IsFan F b c) (d : Bool) : (M.bDual d).IsFan F (b != d) (c != d) := by
  simpa

lemma IsFan.two_le_length (h : M.IsFan F b c) : 2 ≤ F.length := by
  induction h with simp_all

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind[IsFan.two_le_length])

lemma IsFan.ne_nil (h : M.IsFan F b c) : F ≠ [] := by
  grind [h.two_le_length]

lemma IsFan.alt_ne_nil (h : M.IsFan F b c) {d} : F.alt d ≠ [] := by
  cases d <;> grind [F.alt_true_length_eq, h.two_le_length, F.alt_length_add]

lemma IsFan.cons' (h : M.IsFan F b c) (heF : e ∉ F)  (hT : (M.bDual !b).IsTriangle
    {e, F.head h.ne_nil, F.tail.head (by grind [length_tail, h.two_le_length])}) :
    M.IsFan (e :: F) (!b) c := by
  cases h with
  | of_pair => simpa using hT.isFan_of_bDual
  | cons_triangle e x y F b c h he'F hT' =>
    simpa using (h.cons he'F hT').cons (by grind) (by simpa using hT)

lemma IsFan.concat (h : M.IsFan F b c) (hT : (M.bDual (!c)).IsTriangle
    {F.dropLast.getLast (by grind [length_dropLast, h.two_le_length]), (F.getLast h.ne_nil), e})
    (heL : e ∉ F) : M.IsFan (F.concat e) b !c := by
  induction h with
  | of_pair => simpa using hT.isFan_of_bDual
  | cons_triangle => grind [IsFan.cons]

lemma IsFan.nodup (h : M.IsFan F b c) : F.Nodup := by
  induction h with grind

lemma IsFan.reverse (h : M.IsFan F b c) : M.IsFan F.reverse c b := by
  induction h with
  | of_pair b e f he hf hef => exact isFan_pair_not hf he hef.symm
  | cons_triangle e x y F b c h heF hT ih =>
      simpa using ih.concat (by simpa using hT.reverse) (by grind)

@[simp]
lemma isFan_reverse_iff : M.IsFan F.reverse b c ↔ M.IsFan F c b :=
  ⟨fun h ↦ by simpa using h.reverse, IsFan.reverse⟩

lemma IsFan.tail (h : M.IsFan F b c) (hle : 3 ≤ F.length) : M.IsFan F.tail (!b) c := by
  induction h with
  | of_pair => simp at hle
  | cons_triangle => simpa

lemma IsFan.dropLast (h : M.IsFan F b c) (hle : 3 ≤ F.length) : M.IsFan F.dropLast b (!c) := by
  simpa using (h.reverse.tail (by simpa)).reverse

@[simp]
lemma IsFan.dropLast_ne_nil (h : M.IsFan F b c) : F.dropLast ≠ [] := by
  cases h with grind

lemma IsFan.drop {k} (h : M.IsFan F b c) (hk : k + 2 ≤ F.length) :
    M.IsFan (F.drop k) (if Even k then b else !b) c := by
  induction k with
  | zero => simpa
  | succ k ih =>
    convert (ih (by grind)).tail (by grind) using 1
    · simp
    grind

lemma IsFan.right_eq (h : M.IsFan F b c) : c = (if Odd F.length then b else !b) := by
  induction h with grind

lemma IsFan.take {k} (h : M.IsFan F b c) (hk : 2 ≤ k) (hkle : k ≤ F.length) :
    M.IsFan (F.take k) b (if Odd k then b else !b) := by
  convert (h.reverse.drop (k := F.length - k) (by grind)).reverse using 1
  · grind [List.drop_reverse]
  obtain ⟨d, h_eq⟩ := exists_add_of_le hkle
  simp only [h_eq, add_tsub_cancel_left, h.right_eq, Nat.odd_add]
  split_ifs <;> grind

lemma IsFan.isNonloop_bDual (h : M.IsFan F b c) (heF : e ∈ F) (d : Bool) :
    (M.bDual d).IsNonloop e := by
  induction h with
  | of_pair => grind
  | cons_triangle a x y F b c h haF hT ih =>
      obtain rfl | hne := mem_cons.1 heF
      · simpa using hT.isNonloop_bDual₁ (b := !(b != d))
      exact ih (by grind)

lemma IsFan.isNonloop (h : M.IsFan F b c) (heF : e ∈ F) : M.IsNonloop e :=
  h.isNonloop_bDual heF false

lemma IsFan.subset_ground (h : M.IsFan F b c) : {x | x ∈ F} ⊆ M.E :=
  fun _ heF ↦ IsNonloop.mem_ground <| h.isNonloop heF

lemma IsFan.range_get_subset_ground (h : M.IsFan F b c) : range F.get ⊆ M.E := by
  grind [h.subset_ground]

@[simp, grind →]
lemma IsFan.get_mem_ground (h : M.IsFan F b c) {hi : i < F.length} : F[i] ∈ M.E :=
  h.subset_ground (by simp)

@[grind →]
lemma IsFan.getElem_inj_iff (h : M.IsFan F b c) {hi : i < F.length} {hj : j < F.length} :
    F[i] = F[j] ↔ i = j :=
  h.nodup.getElem_inj_iff

lemma IsFan.length_bodd_eq (h : M.IsFan F b c) : F.length.bodd = (b == c) := by
  induction h with
  | of_pair => simp
  | cons_triangle e x y F b => cases b with simp_all

lemma IsFan.bool_right_eq (h : M.IsFan F b c) : c = (b == F.length.bodd) := by
  simp [h.length_bodd_eq]

lemma IsFan.bool_left_eq (h : M.IsFan F b c) : b = (c == F.length.bodd) := by
  cases b with simp [h.length_bodd_eq]

lemma IsFan.length_even (h : M.IsFan F b !b) : Even F.length := by
  have := h.length_bodd_eq
  simp [Nat.bodd_eq_ite] at this
  simpa [Nat.bodd_eq_ite] using h.length_bodd_eq

lemma IsFan.isTriangle_bDual (h : M.IsFan F b c) (hF : 3 ≤ F.length) :
    (M.bDual b).IsTriangle {F[0], F[1], F[2]} := by
  induction h with
  | of_pair => simp at hF
  | cons_triangle => simpa

lemma isFan_cons_iff (hF : 3 ≤ F.length) : M.IsFan (x :: F) b c ↔
    ∃ e f F₀, F = e :: f :: F₀ ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ∉ F ∧ M.IsFan F (!b) c := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | of_pair => simp at hF
    | cons_triangle e z y F b c h heF hT => exact ⟨z, y, F, rfl, hT, by grind, by simpa⟩
  obtain ⟨e, f, F, rfl, hT, hxF, hF'⟩ := h
  refine hF'.cons_not (by grind) hT

lemma IsFan.of_cons (hF : M.IsFan (x :: F) b c) (h : 2 ≤ F.length) : M.IsFan F (!b) c := by
  cases hF with | of_pair => simp at h | cons_triangle => simpa

lemma IsFan.exists_cons (hF : M.IsFan F b c) (h : 3 ≤ F.length) :
    ∃ e F₀, F = e :: F₀ ∧ M.IsFan F₀ (!b) c := by
  cases hF with grind

lemma IsFan.isTriangle_getElem (h : M.IsFan F b c) (i) (hi : i + 2 < F.length) :
    (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  induction h generalizing i with
  | of_pair => grind
  | cons_triangle e x y F b c h heF hT ih =>
    obtain rfl | i := i
    · simpa
    simpa using ih i <| by simpa using hi

lemma IsFan.isTriangle_getElem_of_eq (h : M.IsFan F b c) (i) (hi : i + 2 < F.length)
    (hib : i.bodd = b) : M.IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  simpa [hib.symm] using h.isTriangle_getElem i hi

lemma IsFan.isTriad_getElem_of_eq (h : M.IsFan F b c) (i) (hi : i + 2 < F.length)
    (hib : i.bodd = !b) : M.IsTriad {F[i], F[i + 1], F[i + 2]} := by
  simpa [hib] using h.isTriangle_getElem i hi

lemma IsFan.isTriangle_image_get (h : M.IsFan F b c) (hF : F.length = n + 2) (i : Fin n) :
    (M.bDual (b != (i : ℕ).bodd)).IsTriangle
      <| (fun j ↦ F.get (Fin.cast hF.symm j)) ''
        {i.castSucc.castSucc, i.succ.castSucc, i.succ.succ} := by
  convert h.isTriangle_getElem i.1 (by grind)
  simp [image_insert_eq]

lemma isFan_of_forall_triangle (hF : 3 ≤ F.length) (hnd : F.Nodup)
    (hT : ∀ i (hi : i + 2 < F.length),
    (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]}) :
    M.IsFan F b (b == F.length.bodd) := by
  match F with
  | [] => simp at hF
  | [_] => simp at hF
  | [_, _] => simp at hF
  | e :: f :: g :: F =>
    induction F generalizing e f g b with
    | nil => simpa using (hT 0 (by simp)).isFan_of_bDual
    | cons a F ih =>
      have hwin := (ih f g a (b := !b) (by simp) (by grind) ?_).cons_not (e := e) (by grind) ?_
      · cases b with simpa using hwin
      · exact fun i hi ↦ by simpa using hT (i + 1) (by grind)
      simpa using hT 0 (by simp)

lemma isFan_of_eq_of_forall_triangle (hF : 3 ≤ F.length) (hnd : F.Nodup)
    (hbc : (b == c) = F.length.bodd) (hT : ∀ i (hi : i + 2 < F.length),
      (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]}) : M.IsFan F b c := by
  convert isFan_of_forall_triangle hF hnd (b := b) hT
  cases b with cases c with grind

lemma isFan_iff_forall (hF : 3 ≤ F.length) :
    M.IsFan F b c ↔ (b == c) = F.length.bodd ∧ F.Nodup ∧ ∀ i (hi : i + 2 < F.length),
    (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  refine ⟨fun h ↦ ⟨h.length_bodd_eq.symm, h.nodup, h.isTriangle_getElem⟩, fun ⟨hbc, hnd, h⟩ ↦ ?_⟩
  convert isFan_of_forall_triangle hF hnd h
  cases b with cases c with grind

@[simp]
lemma isFan_three_iff : M.IsFan [e, f, g] b c ↔ b = c ∧ (M.bDual b).IsTriangle {e, f, g} := by
  refine ⟨fun h ↦ ⟨by simpa using h.length_bodd_eq, h.isTriangle_bDual rfl.le⟩, fun h ↦ ?_⟩
  rw [← h.1]
  exact h.2.isFan_of_bDual

lemma isFan_four_iff : M.IsFan [x, e, f, g] b c ↔ c = !b ∧
    (M.bDual (!b)).IsTriangle {e, f, g} ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ≠ g := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hcb, hT, hT', hxg⟩ ↦ ?_⟩
  · cases b with simpa using h.length_bodd_eq
  · simpa using h.isTriangle_getElem 1 (by simp)
  · exact h.isTriangle_bDual (by simp)
  · grind [h.nodup]
  simpa [hcb] using hT.isFan.cons (by simpa using hxg) (by simpa)

/-- Induct by stripping two layers off the front of a fan to get a fan of the same type. -/
@[elab_as_elim]
lemma IsFan.induction₂
    {motive : (M : Matroid α) → (F : List α) → (b c : Bool) → M.IsFan F b c → Prop}
    (of_pair : ∀ M e f (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
      (hef : e ≠ f) d, motive M [e, f] d (!d) (isFan_pair he hf hef))
    (of_isTriangle : ∀ M e f g d (h : (M.bDual d).IsTriangle {e, f, g}),
      motive M [e, f, g] d d h.isFan_of_bDual)
    (cons_cons : ∀ M e f x y F c d (h : M.IsFan (x :: y :: F) c d)
      (hT : (M.bDual (!c)).IsTriangle {f, x, y}) (hf : f ∉ F)
      (hT' : (M.bDual c).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
      motive M _ _ _ h → motive M _ c d ((h.cons hf hT).cons_not (by grind) hT'))
    (h : M.IsFan F b c) : motive M F b c h := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h.two_le_length
  induction k using Nat.twoStepInduction generalizing F b with
  | zero =>
    obtain ⟨e, f, rfl⟩ := length_eq_two.1 <| (add_zero (M := ℕ) _ ▸ hk)
    obtain rfl | rfl := c.eq_or_eq_not b
    · simpa using h.length_bodd_eq
    apply of_pair _ _ _ (h.isNonloop_bDual (by simp)) (h.isNonloop_bDual (by simp))
      (by simpa using h.nodup)
  | one =>
    obtain ⟨e, f, g, rfl⟩ := length_eq_three.1 <| (add_zero (M := ℕ) _ ▸ hk)
    convert of_isTriangle M e f g b <| h.isTriangle_bDual (by simp)
    simp [h.right_eq, show Odd 3 by decide]
  | more n ih _ =>
    obtain ⟨e, F, rfl, h1⟩ := h.exists_cons (by grind)
    obtain ⟨f, F, rfl, h2⟩ := h1.exists_cons (by grind)
    obtain ⟨x, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)
    obtain ⟨y, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)
    have hnd := h.nodup
    exact cons_cons M e f x y F _ _ (by simpa using h2) (h1.isTriangle_bDual (by grind)) (by grind)
      (h.isTriangle_bDual (by grind)) (by grind) (by grind) <| ih (by simpa using h2) (by grind)

/-- An induction principle about fans of even length. -/
@[elab_as_elim]
lemma IsFan.induction₂_even
   {motive : (M : Matroid α) → (F : List α) → (b : Bool) → M.IsFan F b (!b) → Prop}
    (of_pair : ∀ M e f (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
      (hef : e ≠ f) d, motive M [e, f] d (isFan_pair he hf hef))
    (cons_cons : ∀ M e f x y F b (h : M.IsFan (x :: y :: F) b !b)
      (hT : (M.bDual (!b)).IsTriangle {f, x, y}) (hf : f ∉ F)
      (hT' : (M.bDual b).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
      motive M _ _ h → motive M _ b ((h.cons hf hT).cons_not (by grind) hT'))
    (h : M.IsFan F b !b) : motive M F b h := by
  generalize hbc : (!b) = c
  have h' : M.IsFan F b c := by rwa [← hbc]
  induction h' using IsFan.induction₂ with
  | of_pair => apply of_pair <;> assumption
  | of_isTriangle => simpa using h.length_bodd_eq
  | cons_cons => grind

@[elab_as_elim]
lemma IsFan.induction₂_odd
   {motive : (M : Matroid α) → (F : List α) → (b : Bool) → M.IsFan F b b → Prop}
    (of_triangle : ∀ M e f g b (hT : (M.bDual b).IsTriangle {e, f, g}),
      motive M [e, f, g] b hT.isFan_of_bDual)
    (cons_cons : ∀ M e f x y F b (h : M.IsFan (x :: y :: F) b b)
      (hT : (M.bDual (!b)).IsTriangle {f, x, y}) (hf : f ∉ F)
      (hT' : (M.bDual b).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
      motive M _ _ h → motive M _ b ((h.cons hf hT).cons_not (by grind) hT'))
    (h : M.IsFan F b b) : motive M F b h := by
  obtain ⟨c, hcb, h'⟩ : ∃ c, c = b ∧ M.IsFan F b c := ⟨b, rfl, h⟩
  induction h' using IsFan.induction₂ with grind

lemma IsFan.eRk_le (h : M.IsFan F b c) (hlen : 3 ≤ F.length) :
    2 * M.eRk {e | e ∈ F} ≤ F.length + 1 + b.toNat + c.toNat := by
  induction h with
  | of_pair => simp at hlen
  | cons_triangle e x y F b c h heF hT ih =>
    cases F with
    | nil =>
      cases b
      · grw [eRk_le_encard, setOf_three, hT.three_elements, h.bool_right_eq]
        rfl
      grw [setOf_three, IsTriangle.eRk (by simpa using hT), h.bool_right_eq]
      rfl
    | cons p F =>
      simp_rw [List.mem_cons (b := e), setOf_or, setOf_eq_eq_singleton, singleton_union]
      cases b
      · grw [eRk_insert_le_add_one, mul_add, ih (by grind)]
        simp [h.bool_right_eq]
        enat_to_nat! <;> lia
      grw [← eRk_closure_eq, closure_insert_eq_of_mem_closure, eRk_closure_eq, ih (by grind)]
      · simp [h.bool_right_eq]
      exact mem_of_mem_of_subset hT.mem_closure₁ <| M.closure_subset_closure <| by grind

lemma IsFiniteRankUniform.exists_isFan (h : M.IsFiniteRankUniform 2 4) (b : Bool) :
    ∃ F, M.IsFan F b (!b) ∧ {e | e ∈ F} = M.E := by
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hE⟩ := encard_eq_four.1 h.encard_eq
  refine ⟨[x, y, z, w], ?_, by simp [hE, Set.ext_iff]⟩
  grind [encard_eq_three, isFan_four_iff, h.bDual_eq_self, h.isTriangle_iff]

lemma IsFan.contract_disjoint_aux (hF : M.IsFan F false c) (h4 : 4 ≤ F.length)
    (hX : Disjoint {e | e ∈ F} X) (hb : F[0] ∉ M.closure X) (hXE : X ⊆ M.E):
    (M ／ X).IsTriangle {F[0], F[1], F[2]} := by
  have hT := hF.isTriangle_getElem_of_eq 0 (by lia) rfl
  have hdj : Disjoint {F[0], F[1], F[2]} X := hX.mono_left <| (show _ ⊆ {e | e ∈ F} by grind)
  rw [isTriangle_iff, and_iff_left hT.three_elements]
  refine Skew.isCircuit_contract (by_contra fun hsk ↦ hb ?_) hT.isCircuit hdj.symm
  rw [skew_comm] at hsk
  obtain ⟨C, hC, hCss, h0C, hCX⟩ :=
    hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew hdj hsk (e := F[0]) (by simp)
  have hT' := hF.isTriad_getElem_of_eq 1 (by lia) (by simp)
  have h21 := hT'.reverse.mem_iff_mem_of_isCocircuit (K := C) (by simpa) (by grind)
  by_cases h1 : F[1] ∈ C
  · simp [← hT.isCircuit.eq_of_subset_isCircuit hC (by grind), hdj.inter_eq] at hCX
  grw [← diff_subset_iff.2 hCss, ← union_singleton, ← diff_diff, Disjoint.sdiff_eq_left (a := C)
    (by grind), hC.closure_diff_singleton_eq]
  exact M.mem_closure_of_mem h0C

/- Contractions preserve the property of being a fan, unless one of the ends is a joint
spanned by the contract-set. -/
lemma IsFan.contract_disjoint (hF : M.IsFan F b c) (h4 : 4 ≤ F.length) (hX : Disjoint {e | e ∈ F} X)
    (hb : b = false → F[0] ∉ M.closure X) (hc : c = false → F[F.length - 1] ∉ M.closure X) :
    (M ／ X).IsFan F b c := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · grind [M.closure_inter_ground X, M.contract_inter_ground_eq X]
  rw [isFan_iff_forall (by lia), hF.length_bodd_eq, and_iff_right rfl, and_iff_right hF.nodup]
  rintro i hi
  rw [isTriangle_iff, and_iff_left (hF.isTriangle_getElem i hi).three_elements]
  obtain rfl | rfl := b.eq_or_eq_not !i.bodd
  · simp only [Bool.not_bne, bne_self_eq_false, Bool.not_false, bDual_true, dual_contract,
      delete_isCircuit_iff, disjoint_insert_left, disjoint_singleton_left,
      (hF.isTriad_getElem_of_eq i hi (by simp)).isCircuit]
    grind
  obtain rfl | i := i
  · simp only [Nat.bodd_zero, Bool.not_false, Bool.not_true, forall_const] at hb
    simpa using (hF.contract_disjoint_aux h4 hX hb hXE).isCircuit
  obtain heq | hlt := (show i + 4 ≤ F.length from hi).eq_or_lt
  · obtain rfl : c = false := by simpa [← heq] using hF.bool_right_eq
    have hT := (hF.reverse.contract_disjoint_aux (by simpa) (by simpa)
      (by simpa using hc) hXE).reverse
    simpa [← heq] using hT.isCircuit
  simp only [Nat.bodd_succ, Bool.not_not, bne_self_eq_false, bDual_false]
  have hT := hF.isTriangle_getElem_of_eq (i + 1) (by lia) (by simp)
  have hTdj : Disjoint {F[i + 1], F[i + 1 + 1], F[i + 1 + 2]} X := by grind
  refine Skew.isCircuit_contract (by_contra fun hsk ↦ ?_) hT.isCircuit hTdj.symm
  rw [skew_comm] at hsk
  obtain ⟨C, hC, hCss, hCi, hCX⟩ := hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew hTdj
    (e := F[i + 2]) hsk (by simp) hXE
  have hi1C : F[i + 1] ∈ C:= (hF.isTriad_getElem_of_eq i (by lia)
    (by simp)).reverse.swap_right.mem_of_mem_of_notMem_of_is_Cocircuit (by simpa) hCi
    (by grind [hF.nodup.getElem_inj_iff])
  have hi3C : F[i + 3] ∈ C := (hF.isTriad_getElem_of_eq (i + 2) (by lia)
    (by simp)).swap_right.mem_of_mem_of_notMem_of_is_Cocircuit (by simpa) hCi
    (by grind [hF.nodup.getElem_inj_iff])
  simp [← hT.isCircuit.eq_of_subset_isCircuit hC (by grind), hTdj.inter_eq] at hCX

/-- If `N` is a minor of `M`, and `F` is a fan of `M` contained in `E(N)`, whose (co)joint ends are
are not (co)loops of `N`, then `F` is also a fan of `N`.  -/
lemma IsFan.minor {N : Matroid α} (hF : M.IsFan F b c) (h4 : 4 ≤ F.length) (hNM : N ≤m M)
    (hFN : {e | e ∈ F} ⊆ N.E) (h_first : (N.bDual b).IsNonloop F[0])
    (h_last : (N.bDual c).IsNonloop F[F.length - 1]) : N.IsFan F b c := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  have hCF := hF.contract_disjoint h4 (X := C) (by grind) ?_ ?_
  · have hwin := (hCF.dual.contract_disjoint (X := D) h4 (by grind) ?_ ?_).dual
    · simpa using hwin
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_false, dual_contract, delete_closure_eq, mem_diff,
        not_and, not_not, hCD.sdiff_eq_right]
      rintro rfl hcl
      refine False.elim <| h_first.not_isLoop ?_
      grind [bDual_true, dual_delete, dual_contract, contract_isLoop_iff_mem_closure,
        delete_closure_eq, hCD.sdiff_eq_right]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, dual_contract, delete_closure_eq, mem_diff]
    rintro rfl hcl
    refine h_last.not_isLoop ?_
    grind [bDual_true, dual_delete, dual_contract, contract_isLoop_iff_mem_closure,
      delete_closure_eq]
  · rintro rfl hcl
    grind [bDual_false, delete_isLoop_iff, contract_isLoop_iff_mem_closure, h_first.not_isLoop]
  rintro rfl hcl
  grind [h_last.not_isLoop, bDual_false, delete_isLoop_iff, contract_isLoop_iff_mem_closure]




-- (hX : Disjoint {e | e ∈ F} X)
--     (hb : b = false → F[0] ∉ M.closure X) (hc : c = false → F[F.length - 1] ∉ M.closure X) :

    -- by_cases h1 : F[1] ∈ C; grind

  -- have h_or' : F[i+1] ∈ C ∨ F[i+2] ∈ C := by
  --   contra


  -- -- rw [skew_iff_forall_isCircuit (by grind) hXE (by grind [hF.get_mem_ground])]
  -- intro C hC hCXu


    -- by_cases h1 : F[1] ∈ C
    -- · by_cases h0C : F[0] ∈ C
    --   . rw [← hT.isCircuit.eq_of_subset_isCircuit hC (by grind)]
    --     simp
    --   obtain ⟨C', hC'ss, hC', h0C'⟩ :=
    --     hT.isCircuit.strong_elimination hC (f := F[0]) (by simp) h1 (by simp) h0C







  --   sorry






-- lemma Triassic.exists_fan (hM : M.Triassic) (hfin : M.Finite) (hne : M.Nonempty)
--     (hconn : M.TutteConnected 3) : ∃ F c, M.IsFan F false c ∧ {e | e ∈ F} = M.E := by
--   by_cases hU : M.IsFiniteRankUniform 2 4
--   · grind [hU.exists_isFan false]
--   suffices aux : ∀ (n : ℕ), n ≤ M.E.encard → ∃ F b, M.IsFan F b false ∧ n ≤ F.length
--   · have hcard := hfin.ground_finite.encard_eq_coe_toFinset_card
--     obtain ⟨F, b, hF, hle⟩ := aux _ hcard.symm.le
--     refine ⟨F.reverse, b, hF.reverse, ?_⟩
--     refine Finite.eq_of_subset_of_encard_le (by simp) hF.reverse.subset_ground ?_
--     simp only [mem_reverse]
--     rwa [hF.nodup.encard_toSet_eq, hcard, Nat.cast_le]
--   intro n hle
--   induction n with
--   | zero =>
--     obtain ⟨e, he⟩ := hne.ground_nonempty
--     obtain ⟨f, g, hefg⟩ := hM.exists_triangle_bDual he false
--     refine ⟨[e, f, g], false, hefg.isFan, by simp⟩
--   | succ n ih =>
--     obtain ⟨F, b, hF, hnF⟩ := ih (by grw [← hle]; simp)
--     generalize hc : false = c at hF
--     cases hF with
--     | of_pair b e f he hf hne =>
--       obtain ⟨x, y, hexy⟩ := hM.exists_triangle_bDual (he false).mem_ground (!b)
--       exact ⟨[e, x, y], (!b), hexy.isFan_of_bDual, by grind⟩
--     | cons_triangle e x y F b c h heF hT =>
--       subst hc
--       obtain ⟨p, q, hepq⟩ := hM.exists_triangle_bDual (by simpa using hT.mem_ground₁) b
--       have hmem := hepq.mem_or_mem_of_isCircuit_bDual hT.isCircuit (by simp)
--       wlog hp : p = x ∨ p = y generalizing p q with aux
--       · exact aux q p hepq.swap_right (by grind [hepq.ne₁₂]) (by grind [hepq.ne₁₂])
--       by_cases hq : q = x ∨ q = y
--       · have h_eq : ({e, p, q} : Set α) = {e, x, y} := by grind [hepq.ne₂₃]
--         contrapose! hU
--         exact (hepq.isFiniteRankUniform_two_four_of_isTriad (by simpa [h_eq])
--           (by simpa)).of_bDual_self
--       have := h.cons heF hT
--       obtain rfl | rfl := hp
--       · by_cases hqF : q ∈ F
--         · sorry
--         have hF' := (h.cons heF hT).cons (e := q) (by grind) <|
--           by simpa using hepq.reverse.swap_right
--         exact ⟨_, _, hF', by grind⟩
--       sorry


--       _












--           -- obtain ⟨E, hE4, hME⟩ := hepq.swap_right.eq_unifOn_two_four_of_isTriad_of_tutteConnected
--         obtain rfl | rfl := hp
--         · sorry
--         cases F with
--         | nil =>
--           obtain rfl | hne := eq_or_ne x q
--           · obtain ⟨E, hE4, hME⟩ := hepq.swap_right.eq_unifOn_two_four_of_isTriad_of_tutteConnected
--               (by simpa [IsTriad] using hT) (by simpa)
--             obtain ⟨F, hF, hFE⟩ := unifOn_two_four_isFan hE4 b
--             have hF : F.length = 4 := by
--               rw [← Nat.cast_inj (R := ℕ∞), ← hF.nodup.encard_toSet_eq, hFE, hE4, Nat.cast_ofNat]
--             apply_fun (Matroid.bDual · b) at hME
--             simp only [bDual_bDual, bne_self_eq_false, bDual_false] at hME
--             exact ⟨F.reverse, true, by simpa [hME], by grind⟩
--           have hF : M.IsFan [x, e, p, q] (!b) b := by simpa using
--             (hepq.isFan.cons (e := x) (by grind) (by simpa using hT.swap_left)).bDual b
--           cases b
--           · exact ⟨_, _, hF, by grind⟩
--           exact ⟨_, _, hF.reverse, by grind⟩
--         | cons z F =>
--           have := h.isTriangle_bDual sorry
--           simp at this


--     -- have := hM.exists_triangle_bDual

--     --  hfin.ground_finite.toFinset.card
--     --   (by simp [hfin.ground_finite.encard_eq_coe_toFinset_card])
