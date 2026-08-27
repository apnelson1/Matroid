module

public import Matroid.Connectivity.Separation.Tutte
public import Matroid.ForMathlib.List.Basic
public import Mathlib.Data.Vector.Snoc
public import Matroid.ForMathlib.Parity

@[expose] public section
attribute [-grind] Disjoint.mono_left List.Nodup.getElem_inj List.eq_or_mem_of_mem_cons
  List.Nodup.mem_iff_eq_getLast_or_mem_dropLast

set_option linter.style.longLine false

open Set List.Vector

namespace Matroid

-- variable {J : Bool → List α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {L : List α} {n i j : ℕ} {F J : List.Vector α n} {b c : Bool} {L : List ℕ}

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
inductive IsFan : Matroid α → (n : ℕ) → List.Vector α n → Bool → Bool → Prop
  | of_pair (M : Matroid α) (b e f) (he : (M.bDual b).IsNonloop e)
      (hf : (M.bDual !b).IsNonloop f) (hne : e ≠ f) : IsFan M 2 (e ::ᵥ f ::ᵥ nil) b (!b)
  | cons_triangle (M : Matroid α) (n : ℕ) (hn : 2 ≤ n) e (F : List.Vector α n) b c
      (h : IsFan M n F b c) (heF : e ∉ F.toList)
      (hT : (M.bDual (!b)).IsTriangle {e, F[0], F[1]}) : IsFan M (n + 1) (e ::ᵥ F) (!b) c

lemma IsFan.cons (h : M.IsFan n F b c) (heF : e ∉ F.toList) (hn : 2 ≤ n)
    (hT : (M.bDual (!b)).IsTriangle {e, F[0], F[1]}) : M.IsFan (n + 1) (e ::ᵥ F) (!b) c := by
  apply IsFan.cons_triangle <;> assumption

lemma IsFan.cons' {F} (h : M.IsFan (n + 2) F b c) (heF : e ∉ F.toList)
    (hT : (M.bDual (!b)).IsTriangle {e, F[0], F[1]}) : M.IsFan (n + 3) (e ::ᵥ F) (!b) c :=
  h.cons heF (by simp) hT

lemma IsFan.cons_not (h : M.IsFan n F (!b) c) (heF : e ∉ F.toList) (hn : 2 ≤ n)
    (hT : (M.bDual b).IsTriangle {e, F[0], F[1]}) : M.IsFan (n + 1) (e ::ᵥ F) b c := by
  simpa using h.cons heF hn (by simpa)

lemma isFan_pair {b} (he : (M.bDual b).IsNonloop e) (hf : (M.bDual (!b)).IsNonloop f)
    (hef : e ≠ f) : M.IsFan 2 (e ::ᵥ f ::ᵥ nil) b (!b) :=
  IsFan.of_pair _ _ _ _ he hf hef

lemma isFan_pair_not {b} (he : (M.bDual !b).IsNonloop e) (hf : (M.bDual b).IsNonloop f)
    (hef : e ≠ f) : M.IsFan 2 (e ::ᵥ f ::ᵥ nil) (!b) b :=
  by simpa using isFan_pair he (by simpa using hf) hef (b := !b)

lemma IsFan.dual (h : M.IsFan n F b c) : M✶.IsFan n F (!b) (!c) := by
  induction h with
  | of_pair b e f he hf hef =>
      exact isFan_pair (by simpa [and_comm] using he) (by simpa [and_comm] using hf) hef
  | cons_triangle n hn e F b c h heF hT ih => exact ih.cons heF hn (by simpa)

lemma IsTriangle.isFan_of_bDual (h : (M.bDual b).IsTriangle {e, f, g}) :
    M.IsFan 3 (e ::ᵥ f ::ᵥ g ::ᵥ nil) b b :=
  (isFan_pair_not (by simpa [IsNonColoop] using h.isNonColoop₂) h.isNonloop₃ h.ne₂₃).cons_not
    (by simp [h.ne₁₂, h.ne₁₃]) rfl.le (by simpa)

lemma IsTriangle.isFan (h : M.IsTriangle {e, f, g}) : M.IsFan 3 ⟨[e, f, g], rfl⟩ false false :=
  IsTriangle.isFan_of_bDual (b := false) h

lemma IsFan.congr {m : ℕ} {b' c' : Bool} (h : M.IsFan n F b c) {F' : List.Vector α m}
    (hmn : m = n) (hF : F.1 = F'.1) (hb : b = b') (hc : c = c') : M.IsFan m F' b' c' := by
  subst hmn hb hc
  rwa [List.Vector.eq _ _ hF.symm]

lemma IsFan.of_dual (h : M✶.IsFan n F b c) : M.IsFan n F (!b) (!c) := by
  simpa using h.dual

@[simp]
lemma isFan_dual_iff : M✶.IsFan n F b c ↔ M.IsFan n F (!b) (!c) :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

lemma isFan_dual_bnot_iff : M✶.IsFan n F (!b) (!c) ↔ M.IsFan n F b c := by
  simp

@[simp]
lemma isFan_bDual_iff : (M.bDual d).IsFan n F b c ↔ M.IsFan n F (b != d) (c != d) := by
  cases d with simp

alias ⟨IsFan.of_bDual, _⟩ := isFan_bDual_iff

lemma IsFan.bDual (h : M.IsFan n F b c) (d : Bool) : (M.bDual d).IsFan n F (b != d) (c != d) := by
  simpa

lemma IsFan.length_bodd_eq (h : M.IsFan n F b c) : n.bodd = (b == c) := by
  induction h with
  | of_pair => simp
  | cons_triangle e x y F b => cases b with simp_all

lemma IsFan.bool_right_eq (h : M.IsFan n F b c) : c = (b == n.bodd) := by
  simp [h.length_bodd_eq]

lemma IsFan.bool_left_eq (h : M.IsFan n F b c) : b = (c == n.bodd) := by
  cases b with simp [h.length_bodd_eq]

@[grind →]
lemma IsFan.two_le_length (h : M.IsFan n F b c) : 2 ≤ n := by
  induction h with lia

lemma IsFan.neZero (h : M.IsFan n F b c) : NeZero n := ⟨by grind⟩

lemma IsFan.fact_one_lt_length (h : M.IsFan n F b c) : Fact (1 < n) := ⟨by grind⟩

lemma IsFan.length_sub_one_bodd_eq (h : M.IsFan n F b c) : (n - 1).bodd = (b != c) := by
  rw [Nat.bodd_sub (by grind)]
  simp [h.length_bodd_eq]

@[grind →]
lemma IsFan.three_le_length (h : M.IsFan n F b b) : 3 ≤ n := by
  obtain rfl | h3 := h.two_le_length.eq_or_lt
  · simpa using h.length_bodd_eq
  lia

lemma IsFan.mod_lt_length (h : M.IsFan n F b c) (i : ℕ) : i % n < n :=
  Nat.mod_lt i (by grind)

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| grind[IsFan.two_le_length, IsFan.three_le_length, IsFan.mod_lt_length,
      List.length_rotate, Nat.add_one_lt_of_bodd_eq])

-- lemma IsFan.ne_nil (h : M.IsFan n F b c) : F ≠ ⟨[], rfl⟩ := by
--   grind [h.two_le_length]

@[simp]
lemma not_isFan_nil : ¬ M.IsFan 0 ⟨[], rfl⟩ b c :=
  fun h ↦ by simpa using h.two_le_length

@[simp]
lemma not_isFan_single : ¬ M.IsFan 1 ⟨[e], rfl⟩ b c :=
  fun h ↦ by simpa using h.two_le_length

-- lemma IsFan.cons' (h : M.IsFan n F b c) (heF : e ∉ F)  (hT : (M.bDual !b).IsTriangle
--     {e, F.head h.ne_nil, F.tail.head (by grind [length_tail, h.two_le_length])}) :
--     M.IsFan (e :: F) (!b) c := by
--   cases h with
--   | of_pair => simpa using hT.isFan_of_bDual
--   | cons_triangle e x y F b c h he'F hT' =>
--     simpa using (h.cons he'F hT').cons (by grind) (by simpa using hT)

lemma IsFan.concat (h : M.IsFan n F b c) (heL : e ∉ F.toList)
    (hT : (M.bDual (!c)).IsTriangle {F[n - 2], F[n - 1], e}) : M.IsFan (n + 1) (F.snoc e) b !c := by
  obtain rfl | rfl | n := n
  · simpa using h.two_le_length
  · simpa using h.two_le_length
  induction h with
  | of_pair b x y hx hy hne =>
    exact hT.isFan_of_bDual.congr rfl (by simp [List.Vector.getElem_def]) (by simp) rfl


  | cons_triangle n hn x F b c h hxF hT ih =>
    simp only [toList_cons, List.mem_cons, not_or] at heL
    simp at hT
    _
    -- {F.dropLast.getLast (by grind [length_dropLast, h.two_le_length]), (F.getLast h.ne_nil), e})

  -- induction h with
  -- | of_pair => simpa using hT.isFan_of_bDual
  -- | cons_triangle => grind [IsFan.cons]

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
    M.IsFan (F.drop k) (b != k.bodd) c := by
  induction k with
  | zero => simpa
  | succ k ih => convert (ih (by grind)).tail (by grind) using 1 <;> simp

lemma IsFan.right_eq (h : M.IsFan F b c) : c = (if Odd F.length then b else !b) := by
  induction h with grind

lemma IsFan.take {k} (h : M.IsFan F b c) (hk : 2 ≤ k) (hkle : k ≤ F.length) :
    M.IsFan (F.take k) b (b == k.bodd) := by
  convert (h.reverse.drop (k := F.length - k) (by grind)).reverse using 1
  · grind [List.drop_reverse]
  obtain ⟨d, h_eq⟩ := exists_add_of_le hkle
  simp only [h.bool_left_eq, h_eq, Nat.bodd_add, add_tsub_cancel_left]
  cases c with cases hd : d.bodd with simp

lemma IsFan.isNonloop_left (h : M.IsFan [x,y] b c) : (M.bDual b).IsNonloop x := by
  cases h with | of_pair => assumption

lemma IsFan.isNonloop_right (h : M.IsFan [x,y] b c) : (M.bDual !b).IsNonloop y := by
  cases h with | of_pair => assumption

lemma isFan_pair_iff : M.IsFan [e, f] b c ↔
    (c = !b) ∧ e ≠ f ∧ (M.bDual b).IsNonloop e ∧ (M.bDual !b).IsNonloop f := by
  refine ⟨fun h ↦ ⟨by simpa using h.bool_right_eq, by simpa using h.nodup,
    h.isNonloop_left, h.isNonloop_right⟩, ?_⟩
  rintro ⟨rfl, hef, he, hf⟩
  exact IsFan.of_pair _ _ _ _ he hf hef

lemma IsFan.isNonloop_bDual (h : M.IsFan F b c) (heF : e ∈ F) (d : Bool)
    (h2 : F.length = 2 → e = F[(b != d).toNat] := by lia) : (M.bDual d).IsNonloop e := by
  induction h with
  | of_pair b e' f' he hf hne =>
    obtain rfl | rfl := b.eq_or_eq_not d
    · rwa [show e = e' by simpa using h2]
    simpa [show e = f' by simpa using h2] using hf
  | cons_triangle e' x y F b c h heF hT ih =>
    by_cases heT : e ∈ ({e', x, y} : Set α)
    · simpa using hT.isNonloop_bDual_of_mem heT (b := !(b != d))
    cases F with
    | nil => grind
    | cons z F => exact ih (by grind) (by simp)

lemma IsFan.isNonloop (h : M.IsFan F b c) (heF : e ∈ F)
    (h2 : F.length = 2 → e = F[b.toNat] := by lia) : M.IsNonloop e :=
  h.isNonloop_bDual (d := false) heF <| by simpa

lemma IsFan.isNonloop_getElem_fin (h : M.IsFan F b c) {i : Fin F.length}
    (h2 : F.length = 2 → i.1.bodd = b := by lia) : M.IsNonloop F[i.1] := by
  refine h.isNonloop (by simp) fun h2' ↦ ?_
  rw! [← h2 h2', Nat.bodd_toNat_eq_self (by grind)]
  rfl

lemma IsFan.isNonloop_getElem (h : M.IsFan F b c) (i : ℕ) (hi : i < F.length)
    (h2 : F.length = 2 → i.bodd = b := by lia) : M.IsNonloop F[i] := by
  refine h.isNonloop (by simp) fun h2' ↦ ?_
  rw! [← h2 h2', Nat.bodd_toNat_eq_self (by grind)]
  rfl

lemma IsFan.subset_ground (h : M.IsFan F b c) : {x | x ∈ F} ⊆ M.E := by
  induction h with
  | of_pair b e f he hf hne =>
    simp [show e ∈ M.E by simpa using he.mem_ground, show f ∈ M.E by simpa using hf.mem_ground,
      Set.subset_def]
  | cons_triangle e x y F b c h heF hT ih =>
    rwa [toSet_cons_eq, insert_subset_iff, and_iff_right (by simpa using hT.mem_ground₁)]

lemma IsFan.ground_nontrivial (h : M.IsFan F b c) : M.E.Nontrivial := by
  grw [← two_le_encard_iff_nontrivial, ← h.subset_ground, h.nodup.encard_toSet_eq,
    ← h.two_le_length]
  rfl

lemma IsFan.range_get_subset_ground (h : M.IsFan F b c) : range F.get ⊆ M.E := by
  grind [h.subset_ground]

@[simp, grind →]
lemma IsFan.getElem_mem_ground (h : M.IsFan F b c) {hi : i < F.length} : F[i] ∈ M.E :=
  h.subset_ground (by simp)

@[simp, grind .]
lemma IsFan.get_mem_ground (h : M.IsFan F b c) (i : Fin F.length) : F.get i ∈ M.E :=
  h.subset_ground (by simp)

@[grind →]
lemma IsFan.getElem_inj_iff (h : M.IsFan F b c) {hi : i < F.length} {hj : j < F.length} :
    F[i] = F[j] ↔ i = j :=
  h.nodup.getElem_inj_iff

lemma IsFan.getElem_zero_ne_last (h : M.IsFan F b c) : F[0] ≠ F[F.length - 1] := by
  rw [Ne, h.getElem_inj_iff]
  grind

lemma IsFan.length_even (h : M.IsFan F b !b) : Even F.length := by
  have := h.length_bodd_eq
  simp [Nat.bodd_eq_ite] at this
  simpa [Nat.bodd_eq_ite] using h.length_bodd_eq

lemma IsFan.isTriangle_bDual (h : M.IsFan F b c) (hF : 3 ≤ F.length := by lia) :
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

lemma IsFan.isTriangle_getElem (h : M.IsFan F b c) (i) (hi : i + 2 < F.length := by lia) :
    (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  induction h generalizing i with
  | of_pair => grind
  | cons_triangle e x y F b c h heF hT ih =>
    obtain rfl | i := i
    · simpa
    specialize ih i (by simpa using hi)
    simpa

lemma IsFan.isTriangle_getElem_of_eq (h : M.IsFan F b c) (i) (hib : i.bodd = b)
    (hi : i + 2 < F.length := by lia) : M.IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  simpa [hib.symm] using h.isTriangle_getElem i hi

lemma IsFan.isTriad_getElem_of_eq (h : M.IsFan F b c) (i) (hib : i.bodd = !b)
    (hi : i + 2 < F.length := by lia) : M.IsTriad {F[i], F[i + 1], F[i + 2]} := by
  simpa [hib] using h.isTriangle_getElem i hi

lemma IsFan.isTriangle_image_get (h : M.IsFan F b c) (hF : F.length = n + 2) (i : Fin n) :
    (M.bDual (b != (i : ℕ).bodd)).IsTriangle
      <| (fun j ↦ F.get (Fin.cast hF.symm j)) ''
        {i.castSucc.castSucc, i.succ.castSucc, i.succ.succ} := by
  convert h.isTriangle_getElem i.1 (by grind)
  simp [image_insert_eq]

lemma isFan_of_forall_isCircuit (h2 : 2 ≤ F.length) (hnd : F.Nodup)
    (hnl : F.length = 2 → ∀ i (hi : i < F.length), (M.bDual (b != i.bodd)).IsNonloop F[i])
    (hT : ∀ i (hi : i + 2 < F.length),
      (M.bDual (b != i.bodd)).IsCircuit {F[i], F[i + 1], F[i + 2]}) :
    M.IsFan F b (b == F.length.bodd) := by
  replace hT : ∀ i (hi : i + 2 < F.length), (M.bDual (b != i.bodd)).IsTriangle
      {F[i], F[i + 1], F[i + 2]} := by
    refine fun i hi ↦ ⟨hT i hi, ?_⟩
    rw [encard_insert_of_notMem, encard_pair, show (2 : ℕ∞) + 1 = 3 from rfl]
    · simp [hnd.getElem_inj_iff]
    simp [hnd.getElem_inj_iff]
  induction F generalizing b with
  | nil => simp at h2
  | cons e F ih =>
    cases F with | nil => simp at h2 | cons f F =>
    cases F with
    | nil =>
      rw [show (b == [e, f].length.bodd) = !b by simp]
      exact IsFan.of_pair M b e f (by simpa using hnl rfl 0 (by simp))
        (by simpa using hnl rfl 1 (by simp)) (by simpa using hnd)
    | cons g F =>
    cases F with | nil => simpa using (hT 0 (by simp)).isFan_of_bDual | cons g' F =>
    specialize ih (b := !b) (by grind) (by simpa using hnd.tail) (by simp) fun i hi ↦
      by simpa [add_assoc] using hT (i + 1) (by grind)
    cases b with simpa using ih.cons_not (e := e) (by grind) (by simpa using hT 0 (by simp))

lemma isFan_of_eq_of_forall_isCircuit (h2 : 2 ≤ F.length) (hnd : F.Nodup)
    (hbc : (b == c) = F.length.bodd)
    (hnl : F.length = 2 → ∀ i (hi : i < F.length), (M.bDual (b != i.bodd)).IsNonloop F[i])
    (hT : ∀ i (hi : i + 2 < F.length),
      (M.bDual (b != i.bodd)).IsCircuit {F[i], F[i + 1], F[i + 2]}) :
    M.IsFan F b c := by
  convert isFan_of_forall_isCircuit h2 hnd hnl hT
  cases c with grind

lemma isFan_of_eq_of_forall_triangle_get [NeZero F.length] (h2 : 2 ≤ F.length) (hnd : F.Nodup)
    (hbc : (b == c) = F.length.bodd)
    (hnl : F.length = 2 → ∀ i (hi : i < F.length), (M.bDual (b != i.bodd)).IsNonloop F[i])
    (hT : ∀ (i : Fin F.length), i ≠ 0 → i ≠ ⊤ →
      (M.bDual (b == i.1.bodd)).IsCircuit {F[i - 1], F[i], F[i + 1]}) :
    M.IsFan F b c := by
  refine isFan_of_eq_of_forall_isCircuit h2 hnd hbc hnl fun i hi ↦ ?_
  convert hT ⟨i + 1, by lia⟩ (by simp) (by simp [← Fin.val_inj, show i + 1 ≠ F.length - 1 by lia])
  · cases b with simp
  · simp [Fin.val_sub_one_of_ne_zero (show (⟨i + 1, by lia⟩ : Fin F.length) ≠ 0 by simp)]
  · rfl
  rw! [Fin.getElem_fin, Fin.val_add_one_of_lt' (by simpa [add_assoc])]
  rfl

lemma isFan_iff_forall (hF : 3 ≤ F.length) :
    M.IsFan F b c ↔ (b == c) = F.length.bodd ∧ F.Nodup ∧ ∀ i (hi : i + 2 < F.length),
    (M.bDual (b != i.bodd)).IsCircuit {F[i], F[i + 1], F[i + 2]} :=
  ⟨fun h ↦ ⟨h.length_bodd_eq.symm, h.nodup, fun _ _ ↦ (h.isTriangle_getElem ..).isCircuit⟩,
    fun ⟨hbc, hnd, h⟩ ↦
    isFan_of_eq_of_forall_isCircuit (by lia) hnd hbc (by lia) h⟩

lemma isFan_iff_forall' : M.IsFan F b c ↔ (b == c) = F.length.bodd ∧ 2 ≤ F.length ∧ F.Nodup ∧
    (F.length = 2 → ∀ i (hi : i < F.length), (M.bDual (b != i.bodd)).IsNonloop F[i]) ∧
    ∀ i (hi : i + 2 < F.length), (M.bDual (b != i.bodd)).IsCircuit {F[i], F[i + 1], F[i + 2]} := by
  obtain hle | hgt := le_or_gt 3 F.length
  · simp [isFan_iff_forall hle, and_iff_right (show 2 ≤ F.length by lia), show F.length ≠ 2 by lia]
  match F with
  | [] => simp
  | [_] => simp
  | [x, y] =>
    refine ⟨fun h ↦ ⟨h.length_bodd_eq.symm, by simp, h.nodup, ?_, by simp⟩,
      fun ⟨hbc, _, hnd, h, _⟩ ↦ ?_⟩
    · rintro - (rfl | rfl | i) hi
      · simpa using h.isNonloop_left
      · simpa using h.isNonloop_right
      simp at hi
    obtain rfl | rfl := c.eq_or_eq_not b
    · simp at hbc
    exact IsFan.of_pair _ _ _ _ (by simpa using h rfl 0 (by lia))
      (by simpa using h rfl 1 (by lia)) (by simpa using hnd)

instance InvariantFun.isFan {b c : Bool} :
  InvariantFun (fun M L ↦ Matroid.IsFan M L b c) (fun M L ↦ Matroid.IsFan M L b c) where
  of_empty α β hβ x := by simp +contextual [← eq_nil_iff_forall_not_mem]
  map_eq α β M f hf F hF := by
    simp only [SupportClass.list_supported] at hF
    rw! [isFan_iff_forall', TransferClass.pure_transfer, TransferClass.list_transfer,
      isFan_iff_forall', List.nodup_map_iff_of_injOn (by grind [hf.eq_iff]), length_map, eq_iff_iff]
    convert Iff.rfl with a b _ i
    · rw [getElem_map, bDual_map, isNonloop_map_iff _ (by grind)]
    rw [getElem_map, getElem_map, getElem_map, ← image_pair, ← image_insert_eq, bDual_map,
      InvariantFun.map_set_image_iff (X := {F[i], F[i + 1], F[i + 2]}) (P := IsCircuit)
        (Q := IsCircuit) (by simp [insert_subset_iff, hF])]

lemma isFan_map_iff {β : Type*} {f : α → β} {b c : Bool} {hf : InjOn f M.E}
    (hF : {e | e ∈ F} ⊆ M.E) : (M.map f hf).IsFan (F.map f) b c ↔ M.IsFan F b c := by
  apply InvariantFun.map_iff (P := fun M L ↦ Matroid.IsFan M L b c)
    (Q := fun M L ↦ Matroid.IsFan M L b c)
  simpa

lemma IsFan.map (hF : M.IsFan F b c) {β : Type*} {f : α → β} (hf : InjOn f M.E) :
    (M.map f hf).IsFan (F.map f) b c := by
  rwa [isFan_map_iff hF.subset_ground]

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

lemma IsFan.swap_middle (h : M.IsFan F b c) (h4 : F.length = 4) :
    M.IsFan [F[0], F[2], F[1], F[3]] b c := by
  obtain ⟨p, q, r, s, rfl⟩ := length_eq_four.1 h4
  simp only [isFan_four_iff, ne_eq, getElem_cons_zero, getElem_cons_succ] at *
  exact ⟨h.1, h.2.1.swap_left, h.2.2.1.swap_right, h.2.2.2⟩

-- /-- Induct by stripping two layers off the front of a fan to get a fan of the same type. -/
-- @[elab_as_elim]
-- lemma IsFan.induction₂
--     {motive : (M : Matroid α) → (F : List α) → (b c : Bool) → M.IsFan F b c → Prop}
--     (of_pair : ∀ M e f (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
--       (hef : e ≠ f) d, motive M [e, f] d (!d) (isFan_pair he hf hef))
--     (of_isTriangle : ∀ M e f g d (h : (M.bDual d).IsTriangle {e, f, g}),
--       motive M [e, f, g] d d h.isFan_of_bDual)
--     (cons_cons : ∀ M e f x y F c d (h : M.IsFan (x :: y :: F) c d)
--       (hT : (M.bDual (!c)).IsTriangle {f, x, y}) (hf : f ∉ F)
--       (hT' : (M.bDual c).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
--       motive M _ _ _ h → motive M _ c d ((h.cons hf hT).cons_not (by grind) hT'))
--     (h : M.IsFan F b c) : motive M F b c h := by
--   obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h.two_le_length
--   induction k using Nat.twoStepInduction generalizing F b with
--   | zero =>
--     obtain ⟨e, f, rfl⟩ := length_eq_two.1 <| (add_zero (M := ℕ) _ ▸ hk)
--     obtain rfl | rfl := c.eq_or_eq_not b
--     · simpa using h.length_bodd_eq
--     apply of_pair _ _ _ (h.isNonloop_bDual (by simp)) (h.isNonloop_bDual (by simp))
--       (by simpa using h.nodup)
--   | one =>
--     obtain ⟨e, f, g, rfl⟩ := length_eq_three.1 <| (add_zero (M := ℕ) _ ▸ hk)
--     convert of_isTriangle M e f g b <| h.isTriangle_bDual (by simp)
--     simp [h.right_eq, show Odd 3 by decide]
--   | more n ih _ =>
--     obtain ⟨e, F, rfl, h1⟩ := h.exists_cons (by grind)
--     obtain ⟨f, F, rfl, h2⟩ := h1.exists_cons (by grind)
--     obtain ⟨x, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)
--     obtain ⟨y, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)
--     have hnd := h.nodup
--     exact cons_cons M e f x y F _ _ (by simpa using h2) (h1.isTriangle_bDual (by grind)) (by grind)
--       (h.isTriangle_bDual (by grind)) (by grind) (by grind) <| ih (by simpa using h2) (by grind)

-- /-- An induction principle about fans of even length. -/
-- @[elab_as_elim]
-- lemma IsFan.induction₂_even
--    {motive : (M : Matroid α) → (F : List α) → (b : Bool) → M.IsFan F b (!b) → Prop}
--     (of_pair : ∀ M e f (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
--       (hef : e ≠ f) d, motive M [e, f] d (isFan_pair he hf hef))
--     (cons_cons : ∀ M e f x y F b (h : M.IsFan (x :: y :: F) b !b)
--       (hT : (M.bDual (!b)).IsTriangle {f, x, y}) (hf : f ∉ F)
--       (hT' : (M.bDual b).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
--       motive M _ _ h → motive M _ b ((h.cons hf hT).cons_not (by grind) hT'))
--     (h : M.IsFan F b !b) : motive M F b h := by
--   generalize hbc : (!b) = c
--   have h' : M.IsFan F b c := by rwa [← hbc]
--   induction h' using IsFan.induction₂ with
--   | of_pair => apply of_pair <;> assumption
--   | of_isTriangle => simpa using h.length_bodd_eq
--   | cons_cons => grind

-- @[elab_as_elim]
-- lemma IsFan.induction₂_odd
--    {motive : (M : Matroid α) → (F : List α) → (b : Bool) → M.IsFan F b b → Prop}
--     (of_triangle : ∀ M e f g b (hT : (M.bDual b).IsTriangle {e, f, g}),
--       motive M [e, f, g] b hT.isFan_of_bDual)
--     (cons_cons : ∀ M e f x y F b (h : M.IsFan (x :: y :: F) b b)
--       (hT : (M.bDual (!b)).IsTriangle {f, x, y}) (hf : f ∉ F)
--       (hT' : (M.bDual b).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
--       motive M _ _ h → motive M _ b ((h.cons hf hT).cons_not (by grind) hT'))
--     (h : M.IsFan F b b) : motive M F b h := by
--   obtain ⟨c, hcb, h'⟩ : ∃ c, c = b ∧ M.IsFan F b c := ⟨b, rfl, h⟩
-- induction h' using IsFan.induction₂ with grind

lemma IsFan.eRk_le (h : M.IsFan F b c) (hlen : 3 ≤ F.length) :
    2 * M.eRk {e | e ∈ F} ≤ F.length + 1 + b.toNat + c.toNat := by
  induction h with
  | of_pair => simp at hlen
  | cons_triangle e x y F b c h heF hT ih =>
    cases F with
    | nil =>
      cases b
      · grw [eRk_le_encard, setOf_three, hT.three_elements, h.bool_right_eq,
          show (2 : ℕ∞) * 3 ≤ 3 + 1 + 1 + 1 from rfl.le]
        simp
      grw [setOf_three, IsTriangle.eRk (by simpa using hT), h.bool_right_eq,
        show (2 : ℕ∞) * 2 ≤ 3 + 1 from rfl.le]
      simp
    | cons p F =>
      simp_rw [List.mem_cons (b := e), ofPred_or, ofPred_eq_eq_singleton, singleton_union]
      cases b
      · grw [eRk_insert_le_add_one, mul_add, ih (by grind)]
        simp [h.bool_right_eq]
        enat_to_nat! <;> lia
      grw [← eRk_closure_eq, closure_insert_eq_of_mem_closure, eRk_closure_eq, ih (by grind)]
      · simp [h.bool_right_eq]
      exact mem_of_mem_of_subset hT.mem_closure₁ <| M.closure_subset_closure <| by grind

lemma IsFiniteRankUniform.exists_isFan (h : M.IsFiniteUniform 2 2) (b : Bool) :
    ∃ F, M.IsFan F b (!b) ∧ {e | e ∈ F} = M.E := by
  obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hE⟩ := encard_eq_four.1 h.encard_eq
  refine ⟨[x, y, z, w], ?_, by simp [hE, Set.ext_iff]⟩
  grind [isFan_four_iff, encard_eq_three, h.isTriangle_iff, h.bDual_eq_self]

lemma IsFan.contract_disjoint_aux (hF : M.IsFan F false c) (h4 : 4 ≤ F.length)
    (hX : Disjoint {e | e ∈ F} X) (hb : F[0] ∉ M.closure X) (hXE : X ⊆ M.E):
    (M ／ X).IsTriangle {F[0], F[1], F[2]} := by
  have hT := hF.isTriangle_getElem_of_eq 0 rfl
  have hdj : Disjoint {F[0], F[1], F[2]} X := hX.mono_left <| (show _ ⊆ {e | e ∈ F} by grind)
  rw [isTriangle_iff, and_iff_left hT.three_elements]
  refine Skew.isCircuit_contract (by_contra fun hsk ↦ hb ?_) hT.isCircuit hdj.symm
  rw [skew_comm] at hsk
  obtain ⟨C, hC, hCss, h0C, hCX⟩ :=
    hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew hdj hsk (e := F[0]) (by simp) hXE
  have hT' := hF.isTriad_getElem_of_eq 1 (by simp)
  have h21 := hT'.reverse.mem_iff_mem_of_isCocircuit (K := C) (by simpa)
    (by grind [hF.nodup.getElem_inj_iff])
  by_cases h1 : F[1] ∈ C
  · simp [← hT.isCircuit.eq_of_subset_isCircuit hC
      (by grind), hdj.inter_eq] at hCX
  grw [← sdiff_subset_iff.2 hCss, ← union_singleton, ← sdiff_sdiff, Disjoint.sdiff_eq_left (a := C)
    (by grind), hC.closure_sdiff_singleton_eq]
  exact M.mem_closure_of_mem h0C


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
--               rw [← ENat.natCast_inj, ← hF.nodup.encard_toSet_eq, hFE, hE4, Nat.cast_ofNat]
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
