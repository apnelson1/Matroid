module

public import Matroid.Connectivity.Separation.Tutte
public import Matroid.ForMathlib.List.Basic
public import Matroid.ForMathlib.Parity

@[expose] public section
attribute [-grind] Disjoint.mono_left List.Nodup.getElem_inj List.eq_or_mem_of_mem_cons
  List.Nodup.mem_iff_eq_getLast_or_mem_dropLast

set_option linter.style.longLine false

open Set List

namespace Matroid

-- variable {J : Bool → List α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {L : List α} {n i j : ℕ} {F J : List α} {b c : Bool} {L : List ℕ}

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
  | nil M b : IsFan M [] b (!b)
  | cons' M b c e F (hF : IsFan M F b c) (he : (M.bDual (!b)).IsNonloop e) (heF : e ∉ F)
      (hT : ∀ (hF : 2 ≤ F.length), (M.bDual (!b)).IsTriangle {e, F[0], F[1]}) :
      IsFan M (e :: F) (!b) c

@[simp, grind =]
lemma isFan_nil_iff : M.IsFan [] b c ↔ c = !b :=
  ⟨fun h ↦ by cases h with rfl, fun h ↦ h ▸ IsFan.nil M b ⟩

lemma IsFan.cons (hF : M.IsFan F b c) (he : F.length ≤ 1 → (M.bDual (!b)).IsNonloop e)
    (heF : e ∉ F) (hT : ∀ (hF : 2 ≤ F.length), (M.bDual (!b)).IsTriangle {e, F[0], F[1]}) :
    M.IsFan (e :: F) (!b) c :=
  IsFan.cons' _ _ _ _ _ hF (by grind [IsTriangle.isNonloop₁]) heF hT

lemma IsFan.cons_not (hF : M.IsFan F (!b) c) (he : F.length ≤ 1 → (M.bDual b).IsNonloop e)
    (heF : e ∉ F) (hT : ∀ (hF : 2 ≤ F.length), (M.bDual b).IsTriangle {e, F[0], F[1]}) :
    M.IsFan (e :: F) b c := by
  simpa using hF.cons (by simpa) heF (by simpa)

lemma IsFan.cons_triangle {b c : Bool} (h : M.IsFan (x :: y :: F) b c) (heF : e ∉ F)
    (hT : (M.bDual (!b)).IsTriangle {e, x, y}) : M.IsFan (e :: x :: y :: F) (!b) c :=
  h.cons (fun _ ↦ hT.isNonloop₁) (by simpa [hT.ne₁₂, hT.ne₁₃]) (by simp [hT])

lemma IsFan.cons_triangle_not (h : M.IsFan (x :: y :: F) (!b) c) (heF : e ∉ F)
    (hT : (M.bDual b).IsTriangle {e, x, y}) : M.IsFan (e :: x :: y :: F) b c := by
  simpa using h.cons_triangle heF (by simpa)

lemma IsNonloop.isFan_of_bDual (he : (M.bDual b).IsNonloop e) : M.IsFan [e] b b := by
  simpa using (IsFan.nil M !b).cons_not (by simpa) (by simp) (by simp)

@[simp, grind =]
lemma isFan_single_iff : M.IsFan [e] b c ↔ (M.bDual b).IsNonloop e ∧ b = c := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.2 ▸ h.1.isFan_of_bDual⟩
  cases h with | cons' b c e F hF he heF hT =>
  obtain rfl : c = !b := by simpa using hF
  exact ⟨he, rfl⟩

lemma IsFan.length_bodd_eq (h : M.IsFan F b c) : F.length.bodd = (b == c) := by
  induction h with
  | nil b => simp
  | cons' b c e F hF he heF hT ih => cases b with simpa using ih

lemma IsFan.bool_right_eq (h : M.IsFan F b c) : c = (b == F.length.bodd) := by
  simp [h.length_bodd_eq]

lemma IsFan.bool_left_eq (h : M.IsFan F b c) : b = (c == F.length.bodd) := by
  cases b with simp [h.length_bodd_eq]

lemma IsFan.nodup (h : M.IsFan F b c) : F.Nodup := by
  induction h with grind

lemma isFan_pair {b} (he : (M.bDual b).IsNonloop e) (hf : (M.bDual (!b)).IsNonloop f)
    (hef : e ≠ f) : M.IsFan [e, f] b (!b) := by
  simpa using IsFan.cons' _ _ _ e _  hf.isFan_of_bDual (by simpa) (by simpa) (by simp)

lemma isFan_pair_not {b} (he : (M.bDual !b).IsNonloop e) (hf : (M.bDual b).IsNonloop f)
    (hef : e ≠ f) : M.IsFan [e, f] (!b) b :=
  by simpa using isFan_pair he (by simpa using hf) hef (b := !b)

lemma IsFan.isNonloop_left (h : M.IsFan [x,y] b c) : (M.bDual b).IsNonloop x := by
  cases h with assumption

lemma IsFan.isNonloop_right (h : M.IsFan [x,y] b c) : (M.bDual !b).IsNonloop y := by
  cases h with grind

lemma isFan_pair_iff : M.IsFan [e, f] b c ↔
    (c = !b) ∧ e ≠ f ∧ (M.bDual b).IsNonloop e ∧ (M.bDual !b).IsNonloop f := by
  refine ⟨fun h ↦ ⟨by simpa using h.bool_right_eq, by simpa using h.nodup,
    h.isNonloop_left, h.isNonloop_right⟩, ?_⟩
  rintro ⟨rfl, hef, he, hf⟩
  exact isFan_pair he hf hef

lemma IsFan.dual (h : M.IsFan F b c) : M✶.IsFan F (!b) (!c) := by
  induction h with
  | nil b => simp
  | cons' b c e F hF he heF hT ih => exact IsFan.cons' _ _ _ _ _ ih (by simpa) heF <| by simpa

lemma IsTriangle.isFan_of_bDual (h : (M.bDual b).IsTriangle {e, f, g}) : M.IsFan [e, f, g] b b :=
  (isFan_pair_not (by simpa [IsNonColoop] using h.isNonColoop₂) h.isNonloop₃
    h.ne₂₃).cons_triangle_not (by simp) h

lemma IsTriangle.isFan (h : M.IsTriangle {e, f, g}) : M.IsFan [e, f, g] false false :=
  IsTriangle.isFan_of_bDual (b := false) h

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

-- @[grind →]
-- lemma IsFan.two_le_length (h : M.IsFan F b c) : 2 ≤ F.length := by
--   induction h with simp_all

-- lemma IsFan.neZero (h : M.IsFan F b c) : NeZero F.length := ⟨by grind⟩

-- lemma IsFan.fact_one_lt_length (h : M.IsFan F b c) : Fact (1 < F.length) := ⟨by grind⟩

lemma IsFan.length_sub_one_bodd_eq (h : M.IsFan F b c) (h0 : F.length ≠ 0) :
    (F.length - 1).bodd = (b != c) := by
  rw [Nat.bodd_sub (by grind)]
  simp [h.length_bodd_eq]

-- lemma IsFan.val_one (h : M.IsFan F b c) (hF : NeZero F.length := h.neZero) :
--     (1 : Fin F.length).1 = 1 := by
--   simp [Nat.mod_eq_of_lt h.fact_one_lt_length.elim]

-- lemma IsFan.val_two (h : M.IsFan F b c) (hF : 3 ≤ F.length) (hF : NeZero F.length := h.neZero) :
--     (2 : Fin F.length).1 = 2 := by
--   simp only [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show 2 < F.length by lia)]

@[grind →]
lemma IsFan.one_le_length (h : M.IsFan F b b) : 1 ≤ F.length := by
  cases F with simp_all

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| grind[IsFan.one_le_length, List.length_rotate, Nat.add_one_lt_of_bodd_eq])

-- lemma IsFan.cons' (h : M.IsFan F b c) (heF : e ∉ F)  (hT : (M.bDual !b).IsTriangle
--     {e, F.head h.ne_nil, F.tail.head (by grind [length_tail, h.two_le_length])}) :
--     M.IsFan (e :: F) (!b) c := by
--   cases h with
--   | of_pair => simpa using hT.isFan_of_bDual
--   | cons_triangle e x y F b c h he'F hT' =>
--     simpa using (h.cons he'F hT').cons (by grind) (by simpa using hT)
lemma isFan_of_forall_isCircuit (hnd : F.Nodup) (hc : c = (b == F.length.bodd))
    (hnl : F.length ≤ 2 → ∀ i (hi : i < F.length), (M.bDual (b != i.bodd)).IsNonloop F[i])
    (hT : ∀ i (hi : i + 2 < F.length), (M.bDual (b != i.bodd)).IsCircuit
      {F[i], F[i + 1], F[i + 2]}) : M.IsFan F b c := by
  subst hc
  replace hT : ∀ i (hi : i + 2 < F.length), (M.bDual (b != i.bodd)).IsTriangle
      {F[i], F[i + 1], F[i + 2]} := by
    refine fun i hi ↦ ⟨hT i hi, ?_⟩
    rw [encard_insert_of_notMem, encard_pair, show (2 : ℕ∞) + 1 = 3 from rfl]
    · simp [hnd.getElem_inj_iff]
    simp [hnd.getElem_inj_iff]
  induction F using List.twoStepInduction generalizing b with
  | nil => simp
  | singleton x => simpa using hnl (by simp) 0 (by simp)
  | cons_cons x y F ih ih' =>
    cases F with
    | nil =>
      simpa using isFan_pair (by simpa using hnl rfl.le 0 (by simp))
        (by simpa using hnl rfl.le 1 (by simp)) (by simpa using hnd)
    | cons z F =>
    have hT0 : (M.bDual b).IsTriangle {x, y, z} := by simpa using hT 0 (by simp)
    refine IsFan.cons_not ?_ (fun _ ↦ hT0.isNonloop₁) (by grind) fun _ ↦ hT0
    cases F with
    | nil =>
      simpa using isFan_pair (M := M) (b := !b) (by simpa using hT0.isNonloop_bDual₂ (b := true))
        (by simpa using hT0.isNonloop₃) (by grind)
    | cons w F =>
    specialize ih' y (b := !b) (by simpa using hnd.tail) (by simp) fun i hi ↦ ?_
    · simpa [add_assoc] using hT (i + 1) (by grind)
    cases b with simpa using ih'

lemma isFan_of_forall_isCircuit_getElem_fin [NeZero F.length] (hnd : F.Nodup)
    (hc : c = (b == F.length.bodd))
    (hnl : F.length ≤ 2 → ∀ i : Fin F.length, (M.bDual (b != i.1.bodd)).IsNonloop (F[i.1]))
    (hT : ∀ i : Fin F.length, i ≠ ⊤ → i + 1 ≠ ⊤ →
      (M.bDual (b != i.1.bodd)).IsCircuit {F[i.1], F[(i + 1).1], F[(i + 2).1]}) :
    M.IsFan F b c := by
  refine isFan_of_forall_isCircuit hnd hc (by simpa [Fin.forall_iff] using hnl) fun i hi ↦ ?_
  simp only [ne_eq, ← Fin.val_inj, Fin.val_top, Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod,
    Fin.forall_iff] at hT
  specialize hT i
  rw! [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt hi] at hT
  exact hT (by lia) (by lia) (by lia)

lemma IsFan.isTriangle_getElem (h : M.IsFan F b c) (i) (hi : i + 2 < F.length := by lia) :
    (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  induction h generalizing i with
  | nil => simp at hi
  | cons' b c e F hF he heF hT ih =>
    match F with
    | [] => simp at hi
    | [_] => simp at hi
    | f :: g :: F =>
      obtain rfl | i := i
      · simpa using hT
      specialize ih i (by grind)
      cases b with simpa [add_assoc] using ih

lemma IsFan.isNonloop_bDual_getElem (h : M.IsFan F b c) (i : ℕ) (hi : i < F.length) (d : Bool)
    (h2 : F.length ≤ 2 → d = (i.bodd != b) := by lia) : (M.bDual d).IsNonloop F[i] := by
  match F with
  | [] => simp at hi
  | [e] => simpa [h2, show i = 0 by grind] using (isFan_single_iff.1 h).1
  | [e, f] =>
    obtain rfl | rfl | i := i
    · simp [h2, h.isNonloop_left]
    · simp [h2, h.isNonloop_right]
    simp at hi
  | e :: f :: g :: F =>
    obtain rfl | rfl | i := i
    · simpa using (h.isTriangle_getElem 0 (by grind)).isNonloop_bDual₁ (b := (b != d))
    · simpa using (h.isTriangle_getElem 0 (by grind)).isNonloop_bDual₂ (b := (b != d))
    have hT := (h.isTriangle_getElem i (by grind)).isNonloop_bDual₃ (b := ((i.bodd != b) != d))
    simpa using hT

lemma IsFan.isNonloop_bDual_of_mem (h : M.IsFan F b c) (heF : e ∈ F) (d : Bool)
    (h0 : ∀ (_ : F.length ≤ 2), e = F[0] → d = b := by lia)
    (h0' : ∀ (_ : F.length = 2), e = F[1] → d = !b := by lia) : (M.bDual d).IsNonloop e := by
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem heF
  refine h.isNonloop_bDual_getElem i hi _ fun h2 ↦ ?_
  obtain rfl | ⟨rfl, h2⟩ : i = 0 ∨ (i = 1 ∧ F.length = 2) := by grind
  · simp [h0 h2]
  simp [h0' h2]

lemma IsFan.isNonloop_getElem (h : M.IsFan F b c) (i : ℕ) (hi : i < F.length)
    (h2 : F.length ≤ 2 → i.bodd = b := by lia) : M.IsNonloop F[i] :=
  h.isNonloop_bDual_getElem i hi false <| by simpa

lemma IsFan.isNonloop_of_mem (h : M.IsFan F b c) (heF : e ∈ F)
    (h0 : ∀ (_ : F.length ≤ 2), e = F[0] → b = false := by lia)
    (h0' : ∀ (_ : F.length = 2), e = F[1] → b = true := by lia) :
    M.IsNonloop e :=
  h.isNonloop_bDual_of_mem heF false (by grind) (by grind)

lemma IsFan.concat (h : M.IsFan F b c) (he : F.length ≤ 1 → (M.bDual !c).IsNonloop e)
    (hT : ∀ (h2 : 2 ≤ F.length), (M.bDual (!c)).IsTriangle {F[F.length - 2], F[F.length - 1], e})
    (heF : e ∉ F) : M.IsFan (F.concat e) b !c := by
  refine isFan_of_forall_isCircuit (by grind [nodup_append, h.nodup])
    (by cases b with simp [h.bool_right_eq]) (fun hF1 i hi ↦ ?_) fun i hi ↦ ?_
  · obtain (⟨rfl, h1⟩ | rfl) : (i = 0 ∧ F.length = 1) ∨ i = F.length := by grind
    · cases h with
      | nil b => simp at h1
      | cons' b c f F hF hf heF hT => simpa using hf
    cases c with simpa [h.bool_left_eq] using he (by grind)
  obtain heq | hlt := (show i + 2 ≤ F.length by grind).eq_or_lt
  · rw! [concat_eq_append, getElem_append_left (by lia), getElem_append_left (by lia), heq]
    cases b with simpa [h.bool_right_eq, heq.symm] using (hT (by lia)).isCircuit
  rw! [concat_eq_append, getElem_append_left (by lia), getElem_append_left (by lia),
    getElem_append_left (by lia)]
  exact (h.isTriangle_getElem i).isCircuit

lemma IsFan.concat_triangle (h : M.IsFan F b c) (h2F : 2 ≤ F.length) (hT : (M.bDual (!c)).IsTriangle
    {F[F.length - 2], F[F.length - 1], e}) (heF : e ∉ F) : M.IsFan (F.concat e) b !c :=
  h.concat (by lia) (fun _ ↦ hT) heF

lemma IsFan.reverse (h : M.IsFan F b c) : M.IsFan F.reverse c b := by
  induction h with
  | nil => simp
  | cons' b c e F hF he heF hT ih =>
    replace ih := ih.concat (e := e) (by simp [he]) (fun h2 ↦ ?_) (by simpa)
    · simpa using ih
    simpa [show F.length - 1 - (F.length - 2) = 1 by grind] using (hT (by grind)).reverse

@[simp]
lemma isFan_reverse_iff : M.IsFan F.reverse b c ↔ M.IsFan F c b :=
  ⟨fun h ↦ by simpa using h.reverse, IsFan.reverse⟩

lemma IsFan.tail (h : M.IsFan F b c) (hne : F ≠ []) : M.IsFan F.tail (!b) c := by
  induction h with
  | nil => simp at hne
  | cons' => simpa

lemma IsFan.dropLast (h : M.IsFan F b c) (hne : F ≠ []) : M.IsFan F.dropLast b (!c) := by
  simpa using (h.reverse.tail (by simpa)).reverse

lemma IsFan.drop {k} (h : M.IsFan F b c) (hk : k ≤ F.length) :
    M.IsFan (F.drop k) (b != k.bodd) c := by
  induction k with
  | zero => simpa
  | succ k ih => simpa using (ih (by grind)).tail (by rw [← length_pos_iff, length_drop]; lia)

lemma IsFan.right_eq (h : M.IsFan F b c) : c = (if Odd F.length then b else !b) := by
  induction h with grind

lemma IsFan.take {k} (h : M.IsFan F b c) (hk : 2 ≤ k) (hkle : k ≤ F.length) :
    M.IsFan (F.take k) b (b == k.bodd) := by
  convert (h.reverse.drop (k := F.length - k) (by grind)).reverse using 1
  · grind [List.drop_reverse]
  obtain ⟨d, h_eq⟩ := exists_add_of_le hkle
  simp only [h.bool_left_eq, h_eq, Nat.bodd_add, add_tsub_cancel_left]
  cases c with cases hd : d.bodd with simp



-- lemma IsFan.isNonloop_getElem_fin (h : M.IsFan F b c) {i : Fin F.length}
--     (h2 : F.length = 2 → i.1.bodd = b := by lia) : M.IsNonloop F[i.1] := by
--   refine h.isNonloop (by simp) fun h2' ↦ ?_
--   rw! [← h2 h2', Nat.bodd_toNat_eq_self (by grind)]
--   rfl

-- lemma IsFan.isNonloop_getElem (h : M.IsFan F b c) (i : ℕ) (hi : i < F.length)
--     (h2 : F.length = 2 → i.bodd = b := by lia) : M.IsNonloop F[i] := by
--   refine h.isNonloop (by simp) fun h2' ↦ ?_
--   rw! [← h2 h2', Nat.bodd_toNat_eq_self (by grind)]
--   rfl

lemma IsFan.subset_ground (h : M.IsFan F b c) : {x | x ∈ F} ⊆ M.E := by
  induction h with
  | nil => simp
  | cons' b c e F hF he =>
    simpa [ofPred_or, insert_subset_iff, and_iff_right (by simpa using he.mem_ground)]


lemma IsFan.ground_nontrivial (h : M.IsFan F b c) (h2 : 2 ≤ F.length) : M.E.Nontrivial := by
  grw [← two_le_encard_iff_nontrivial, ← h.subset_ground, h.nodup.encard_toSet_eq, ← h2]
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

lemma IsFan.length_even (h : M.IsFan F b !b) : Even F.length := by
  have := h.length_bodd_eq
  simp [Nat.bodd_eq_ite] at this
  simpa [Nat.bodd_eq_ite] using h.length_bodd_eq

lemma isFan_cons_iff (hF : 3 ≤ F.length) : M.IsFan (x :: F) b c ↔
    ∃ e f F₀, F = e :: f :: F₀ ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ∉ F ∧ M.IsFan F (!b) c := by
  refine ⟨fun h ↦ ⟨F[0], F[1], F.tail.tail, ?_, by simpa using h.isTriangle_getElem 0 (by grind),
    by grind [h.nodup], by simpa using h.tail (by grind)⟩, ?_⟩
  · rw [← head_tail (by grind [length_tail]), cons_head_tail, getElem_zero_eq_head,
        cons_head_tail]
  rintro ⟨e, f, F₀, rfl, hT, hxF, hF⟩
  exact hF.cons_triangle_not (by grind) hT

lemma IsFan.of_cons (hF : M.IsFan (x :: F) b c) : M.IsFan F (!b) c := by
  simpa using hF.tail (by simp)

lemma IsFan.exists_cons (hF : M.IsFan F b c) (h : 3 ≤ F.length) :
    ∃ e F₀, F = e :: F₀ ∧ M.IsFan F₀ (!b) c := by
  cases hF with grind

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

lemma isFan_iff_forall (hF : 3 ≤ F.length) :
    M.IsFan F b c ↔ (b == c) = F.length.bodd ∧ F.Nodup ∧ ∀ i (hi : i + 2 < F.length),
    (M.bDual (b != i.bodd)).IsCircuit {F[i], F[i + 1], F[i + 2]} :=
  ⟨fun h ↦ ⟨h.length_bodd_eq.symm, h.nodup, fun _ _ ↦ (h.isTriangle_getElem ..).isCircuit⟩,
    fun ⟨hbc, hnd, h⟩ ↦ isFan_of_forall_isCircuit hnd (by cases b with simpa using hbc) (by lia) h⟩

lemma isFan_iff_forall' : M.IsFan F b c ↔ (b == c) = F.length.bodd ∧ F.Nodup ∧
    (F.length ≤ 2 → ∀ i (hi : i < F.length), (M.bDual (b != i.bodd)).IsNonloop F[i]) ∧
    ∀ i (hi : i + 2 < F.length), (M.bDual (b != i.bodd)).IsCircuit {F[i], F[i + 1], F[i + 2]} := by
  match F with
  | [] => cases b with | _ => simp
  | [e] => simp [and_comm]
  | [e, f] => cases b with | _ => simp [isFan_pair_iff, ← Nat.and_forall_add_one]
  | e :: f :: g :: F => simp [isFan_iff_forall]


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
  refine ⟨fun h ↦ ⟨by simpa using h.length_bodd_eq,
    by simpa using h.isTriangle_getElem 0 (by grind)⟩, fun h ↦ ?_⟩
  rw [← h.1]
  exact h.2.isFan_of_bDual

lemma isFan_four_iff : M.IsFan [x, e, f, g] b c ↔ c = !b ∧
    (M.bDual (!b)).IsTriangle {e, f, g} ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ≠ g := by
  grind [isFan_three_iff, isFan_cons_iff]

lemma IsFan.swap_middle (h : M.IsFan F b c) (h4 : F.length = 4) :
    M.IsFan [F[0], F[2], F[1], F[3]] b c := by
  obtain ⟨p, q, r, s, rfl⟩ := length_eq_four.1 h4
  simp only [isFan_four_iff, ne_eq, getElem_cons_zero, getElem_cons_succ] at *
  exact ⟨h.1, h.2.1.swap_left, h.2.2.1.swap_right, h.2.2.2⟩

lemma IsFan.eRk_le (h : M.IsFan F b c) :
    2 * M.eRk {e | e ∈ F} ≤ F.length + 1 + b.toNat + c.toNat := by
  induction h with
  | nil => simp
  | cons' b c e F hF he heF hT ih =>
    simp only [mem_cons, ofPred_or, ofPred_eq_eq_singleton, singleton_union, length_cons,
      Nat.cast_add, Nat.cast_one]
    obtain rfl | rfl := b
    · grw [eRk_insert_le_add_one, mul_add, ih, Bool.toNat_false, Bool.not_false, Bool.toNat_true]
      simp only [Nat.cast_zero, add_zero, mul_one, Nat.cast_one]
      enat_to_nat! <;> lia
    match F with
    | [] =>
      grw [eRk_le_encard]
      simp [one_add_one_eq_two]
    | [f] =>
      grw [eRk_le_encard, show c = true by simpa using hF.bool_right_eq,
        encard_insert_of_notMem (by simpa using heF)]
      simp [two_mul, one_add_one_eq_two, add_assoc]
    | f :: g :: F =>
      grw [eRk_insert_of_mem_closure, ih]
      · simp
      exact mem_of_mem_of_subset (hT (by simp)).mem_closure₁ <| closure_subset_closure _ <|
        by simp [insert_subset_iff]

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
