/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.Walk.Defs

/-!
# Operations on walks

Cuts compute their common endpoint from the walk, so `take` and `drop` concatenate without an
endpoint equality proof. Reversal swaps the two incidence labels at each step. These operations
concern the labels of a walk and carry no graph-validity conditions.
-/

@[expose] public section

namespace Walk

variable {V I E : Type*} {u v w x u' v' : V} {i j : I} {e : E}

/-- The vertex at position `n`, with the terminal vertex repeated beyond the end. -/
def getVert {u v : V} : Walk I E u v → ℕ → V
  | .nil _ _ u, _ => u
  | .cons u _ _ _ _, 0 => u
  | .cons _ _ _ _ p, n + 1 => p.getVert n

@[simp] lemma getVert_zero (p : Walk I E u v) : p.getVert 0 = u := by cases p <;> rfl

@[simp] lemma getVert_nil (n : ℕ) : (nil I E u).getVert n = u := rfl

@[simp] lemma getVert_cons_succ (p : Walk I E v w) (n : ℕ) :
    (cons u i e j p).getVert (n + 1) = p.getVert n := rfl

lemma getVert_mem_support (p : Walk I E u v) (n : ℕ) : p.getVert n ∈ p.support := by
  induction p generalizing n with
  | nil => simp
  | cons u i e j p ih => cases n <;> simp [ih]

lemma getVert_of_length_le (p : Walk I E u v) {n : ℕ} (hn : p.length ≤ n) : p.getVert n = v := by
  induction p generalizing n with
  | nil => rfl
  | cons u i e j p ih =>
    cases n with
    | zero => simp at hn
    | succ n => exact ih (Nat.le_of_succ_le_succ hn)

@[simp] lemma getVert_length (p : Walk I E u v) : p.getVert p.length = v :=
  p.getVert_of_length_le le_rfl

/-- Regard a walk as having propositionally equal endpoints. -/
def copy (p : Walk I E u v) (hu : u = u') (hv : v = v') : Walk I E u' v' := hu ▸ hv ▸ p

/-- The first `n` steps, or the whole walk if `n` exceeds its length.
The cut endpoint is computed once and shared by the output constructors. -/
def take (p : Walk I E u v) (n : ℕ) : Walk I E u (p.getVert n) :=
  go p n (p.getVert n) rfl
where
  /-- Construct a prefix while carrying its terminal vertex explicitly. -/
  go : {u v : V} → (p : Walk I E u v) → (n : ℕ) →
      (t : V) → p.getVert n = t → Walk I E u t
    | _, _, .nil _ _ u, _, _, h => (Walk.nil I E u).copy rfl h
    | _, _, .cons u _ _ _ _, 0, _, h => (Walk.nil I E u).copy rfl h
    | _, _, .cons u i e j p, n + 1, t, h => .cons u i e j (go p n t h)

/-- Delete the first `n` steps, ending with an empty walk if `n` exceeds the length. -/
def drop {u v : V} : (p : Walk I E u v) → (n : ℕ) → Walk I E (p.getVert n) v
  | .nil _ _ u, _ => .nil I E u
  | .cons u i e j p, 0 => .cons u i e j p
  | .cons _ _ _ _ p, n + 1 => p.drop n

@[simp] lemma take_nil (n : ℕ) : (nil I E u).take n = nil I E u := rfl

@[simp] lemma drop_nil (n : ℕ) : (nil I E u).drop n = nil I E u := rfl

@[simp] lemma take_cons_zero (p : Walk I E v w) :
    (cons u i e j p).take 0 = nil I E u := rfl

@[simp] lemma drop_cons_zero (p : Walk I E v w) :
    (cons u i e j p).drop 0 = cons u i e j p := rfl

@[simp] lemma take_cons_succ (p : Walk I E v w) (n : ℕ) :
    (cons u i e j p).take (n + 1) = cons u i e j (p.take n) := rfl

@[simp] lemma drop_cons_succ (p : Walk I E v w) (n : ℕ) :
    (cons u i e j p).drop (n + 1) = p.drop n := rfl

@[simp] lemma take_append_drop (p : Walk I E u v) (n : ℕ) : (p.take n).append (p.drop n) = p := by
  induction p generalizing n with
  | nil => simp
  | cons u i e j p ih =>
    cases n with
    | zero => rfl
    | succ n => simp [ih]

@[simp] lemma length_take (p : Walk I E u v) (n : ℕ) : (p.take n).length = min n p.length := by
  induction p generalizing n with
  | nil => simp
  | cons u i e j p ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (p.take n).length + 1 = min (n + 1) (p.length + 1)
      rw [ih]
      exact (Nat.succ_min_succ n p.length).symm

@[simp] lemma length_drop (p : Walk I E u v) (n : ℕ) : (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil => simp
  | cons u i e j p ih =>
    cases n with
    | zero => rfl
    | succ n => simp [ih]

@[simp] lemma edges_take (p : Walk I E u v) (n : ℕ) : (p.take n).edges = p.edges.take n := by
  induction p generalizing n with
  | nil => simp
  | cons u i e j p ih =>
    cases n with
    | zero => rfl
    | succ n => simp [ih]

@[simp] lemma edges_drop (p : Walk I E u v) (n : ℕ) : (p.drop n).edges = p.edges.drop n := by
  induction p generalizing n with
  | nil => simp
  | cons u i e j p ih =>
    cases n with
    | zero => rfl
    | succ n => simp [ih]

lemma support_take_subset (p : Walk I E u v) (n : ℕ) : (p.take n).support ⊆ p.support := by
  intro x hx
  rw [← p.take_append_drop n]
  exact (mem_support_append _ _).mpr (.inl hx)

lemma support_drop_subset (p : Walk I E u v) (n : ℕ) : (p.drop n).support ⊆ p.support := by
  intro x hx
  rw [← p.take_append_drop n]
  exact (mem_support_append _ _).mpr (.inr hx)

lemma support_append_single (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) :
    (p.append (single v i e j w)).support = p.support ++ [w] := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih]

/-- Reverse onto an accumulator, using one recursive call per traversal. -/
def reverseAux : {u v : V} → Walk I E u v → Walk I E u w → Walk I E v w
  | _, _, .nil _ _ _, q => q
  | _, _, .cons u i e j p, q => p.reverseAux (.cons _ j e i q)

@[simp] lemma reverseAux_nil (q : Walk I E u v) : (nil I E u).reverseAux q = q := rfl

@[simp] lemma reverseAux_cons (p : Walk I E v w) (q : Walk I E u x) :
    (cons u i e j p).reverseAux q = p.reverseAux (cons v j e i q) := rfl

lemma reverseAux_append (p : Walk I E u v) (q : Walk I E u w) (r : Walk I E w x) :
    (p.reverseAux q).append r = p.reverseAux (q.append r) := by
  induction p with
  | nil => rfl
  | cons u i e j p ih =>
    simpa only [reverseAux_cons, cons_append] using ih (cons _ j e i q)

/-- Reverse a walk using an accumulator, swapping the incidence pair at each step. -/
def reverse (p : Walk I E u v) : Walk I E v u := p.reverseAux (.nil I E u)

lemma reverseAux_eq (p : Walk I E u v) (q : Walk I E u w) :
    p.reverseAux q = p.reverse.append q := by
  simp [reverse, reverseAux_append]

@[simp] lemma reverse_nil : (nil I E u).reverse = nil I E u := rfl

lemma reverse_cons (p : Walk I E v w) :
    (cons u i e j p).reverse = p.reverse.append (single v j e i u) := by
  exact reverseAux_eq p (single v j e i u)

@[simp] lemma reverse_single : (single u i e j v).reverse = single v j e i u := rfl

@[simp] lemma reverse_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  induction p with
  | nil => simp
  | cons u i e j p ih => simp [reverse_cons, ih, append_assoc]

@[simp] lemma reverse_reverse (p : Walk I E u v) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [reverse_cons, ih, single]

/-- Reversal is a bijection between the two endpoint-indexed walk types. -/
def reverseEquiv (u v : V) : Walk I E u v ≃ Walk I E v u where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

lemma reverse_injective : Function.Injective (reverse : Walk I E u v → Walk I E v u) :=
  (reverseEquiv u v).injective

@[simp] lemma length_reverse (p : Walk I E u v) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [reverse_cons, single, ih]

@[simp] lemma edges_reverse (p : Walk I E u v) : p.reverse.edges = p.edges.reverse := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [reverse_cons, single, ih]

@[simp] lemma support_reverse (p : Walk I E u v) : p.reverse.support = p.support.reverse := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [reverse_cons, support_append_single, ih]

@[simp] lemma incidences_reverse (p : Walk I E u v) :
    p.reverse.incidences = p.incidences.reverse := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [reverse_cons, single, ih, List.append_assoc]

@[simp] lemma mem_support_reverse (p : Walk I E u v) {x : V} :
    x ∈ p.reverse.support ↔ x ∈ p.support := by simp

@[simp] lemma copy_rfl (p : Walk I E u v) : p.copy rfl rfl = p := rfl

@[simp] lemma length_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by subst_vars; rfl

@[simp] lemma support_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).support = p.support := by subst_vars; rfl

@[simp] lemma edges_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edges = p.edges := by subst_vars; rfl

@[simp] lemma incidences_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).incidences = p.incidences := by subst_vars; rfl

@[simp] lemma getVert_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') (n : ℕ) :
    (p.copy hu hv).getVert n = p.getVert n := by subst_vars; rfl

lemma copy_copy (p : Walk I E u v) (hu : u = u') (hv : v = v')
    (hu' : u' = w) (hv' : v' = x) :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars; rfl

lemma append_copy (p : Walk I E u v) (q : Walk I E v w)
    (hu : u = u') (hv : v = v') (hw : w = x) :
    (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by
  subst_vars; rfl

@[simp] lemma take_zero (p : Walk I E u v) :
    (p.take 0).copy rfl p.getVert_zero = nil I E u := by cases p <;> rfl

@[simp] lemma drop_zero (p : Walk I E u v) :
    (p.drop 0).copy p.getVert_zero rfl = p := by cases p <;> rfl

@[simp] lemma drop_of_length_le (p : Walk I E u v) {n : ℕ} (hn : p.length ≤ n) :
    (p.drop n).copy (p.getVert_of_length_le hn) rfl = nil I E v := by
  apply Nil.eq_nil
  apply length_eq_zero_iff.mp
  simpa only [length_copy, length_drop] using Nat.sub_eq_zero_of_le hn

@[simp] lemma take_of_length_le (p : Walk I E u v) {n : ℕ} (hn : p.length ≤ n) :
    (p.take n).copy rfl (p.getVert_of_length_le hn) = p := by
  simpa only [drop_of_length_le p hn, append_nil, take_append_drop, copy_rfl] using
    append_copy (p.take n) (p.drop n) rfl (p.getVert_of_length_le hn) rfl

@[simp] lemma take_length (p : Walk I E u v) :
    (p.take p.length).copy rfl p.getVert_length = p := by simp

@[simp] lemma drop_length (p : Walk I E u v) :
    (p.drop p.length).copy p.getVert_length rfl = nil I E v := by simp

lemma append_right_injective (p : Walk I E u v) :
    Function.Injective (p.append : Walk I E v w → Walk I E u w) := by
  intro q r h
  induction p with
  | nil => exact h
  | cons u i e j p ih => exact ih (eq_of_heq (cons.inj h).2.2.2.2)

lemma append_left_injective (q : Walk I E v w) :
    Function.Injective (fun p : Walk I E u v => p.append q) := by
  intro p r h
  apply reverse_injective
  apply append_right_injective q.reverse
  simpa using congrArg reverse h

@[simp] lemma append_right_inj (p : Walk I E u v) (q r : Walk I E v w) :
    p.append q = p.append r ↔ q = r := (append_right_injective p).eq_iff

@[simp] lemma append_left_inj (p q : Walk I E u v) (r : Walk I E v w) :
    p.append r = q.append r ↔ p = q := (append_left_injective r).eq_iff

/-- Ordered pairs of incidence labels, one pair per traversal. -/
def incidencePairs {u v : V} : Walk I E u v → List (I × I)
  | .nil _ _ _ => []
  | .cons _ i _ j p => (i, j) :: p.incidencePairs

/-- Incidences used at the departures of the traversals. -/
def sourceIncs {u v : V} : Walk I E u v → List I
  | .nil _ _ _ => []
  | .cons _ i _ _ p => i :: p.sourceIncs

/-- Incidences used at the arrivals of the traversals. -/
def targetIncs {u v : V} : Walk I E u v → List I
  | .nil _ _ _ => []
  | .cons _ _ _ j p => j :: p.targetIncs

@[simp] lemma incidencePairs_nil : (nil I E u).incidencePairs = [] := rfl

@[simp] lemma incidencePairs_cons (p : Walk I E v w) :
    (cons u i e j p).incidencePairs = (i, j) :: p.incidencePairs := rfl

@[simp] lemma sourceIncs_nil : (nil I E u).sourceIncs = [] := rfl

@[simp] lemma sourceIncs_cons (p : Walk I E v w) :
    (cons u i e j p).sourceIncs = i :: p.sourceIncs := rfl

@[simp] lemma targetIncs_nil : (nil I E u).targetIncs = [] := rfl

@[simp] lemma targetIncs_cons (p : Walk I E v w) :
    (cons u i e j p).targetIncs = j :: p.targetIncs := rfl

lemma sourceIncs_eq_map (p : Walk I E u v) :
    p.sourceIncs = p.incidencePairs.map Prod.fst := by
  induction p <;> simp_all

lemma targetIncs_eq_map (p : Walk I E u v) :
    p.targetIncs = p.incidencePairs.map Prod.snd := by
  induction p <;> simp_all

@[simp] lemma incidencePairs_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).incidencePairs = p.incidencePairs := by subst_vars; rfl

@[simp] lemma sourceIncs_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).sourceIncs = p.sourceIncs := by subst_vars; rfl

@[simp] lemma targetIncs_copy (p : Walk I E u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).targetIncs = p.targetIncs := by subst_vars; rfl

@[simp] lemma length_incidencePairs (p : Walk I E u v) : p.incidencePairs.length = p.length := by
  induction p <;> simp_all

@[simp] lemma length_sourceIncs (p : Walk I E u v) : p.sourceIncs.length = p.length := by
  simp [sourceIncs_eq_map]

@[simp] lemma length_targetIncs (p : Walk I E u v) : p.targetIncs.length = p.length := by
  simp [targetIncs_eq_map]

@[simp] lemma incidencePairs_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).incidencePairs = p.incidencePairs ++ q.incidencePairs := by
  induction p <;> simp_all

@[simp] lemma sourceIncs_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).sourceIncs = p.sourceIncs ++ q.sourceIncs := by simp [sourceIncs_eq_map]

@[simp] lemma targetIncs_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).targetIncs = p.targetIncs ++ q.targetIncs := by simp [targetIncs_eq_map]

lemma incidences_eq_flatMap (p : Walk I E u v) :
    p.incidences = p.incidencePairs.flatMap (fun ij => [ij.1, ij.2]) := by
  induction p <;> simp_all

/-- Append one traversal to a walk. -/
def concat (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) : Walk I E u w :=
  p.append (single v i e j w)

@[simp] lemma concat_nil :
    (nil I E u).concat i e j v = single u i e j v := rfl

@[simp] lemma concat_cons {i' j' : I} {f : E} (p : Walk I E v w) :
    (cons u i e j p).concat i' f j' x = cons u i e j (p.concat i' f j' x) := rfl

@[simp] lemma length_concat (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) :
    (p.concat i e j w).length = p.length + 1 := by simp [concat, single]

@[simp] lemma support_concat (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) :
    (p.concat i e j w).support = p.support ++ [w] := support_append_single p i e j w

@[simp] lemma edges_concat (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) :
    (p.concat i e j w).edges = p.edges ++ [e] := by simp [concat, single]

@[simp] lemma incidencePairs_concat (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) :
    (p.concat i e j w).incidencePairs = p.incidencePairs ++ [(i, j)] := by simp [concat, single]

lemma append_concat (p : Walk I E u v) (q : Walk I E v w) (i : I) (e : E) (j : I) (x : V) :
    (p.append q).concat i e j x = p.append (q.concat i e j x) := append_assoc ..

lemma concat_append (p : Walk I E u v) (i : I) (e : E) (j : I) (q : Walk I E w x) :
    (p.concat i e j w).append q = p.append (cons v i e j q) := by
  simp [concat, append_assoc, single]

section ConcatRec

variable {motive : ∀ {u v : V}, Walk I E u v → Sort*}
  (Hnil : ∀ (u : V), motive (.nil I E u))
  (Hconcat : ∀ {u v : V} (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V),
    motive p → motive (p.concat i e j w))

/-- Accumulate the concat recursion along a suffix of a walk. -/
def concatRecAux {v w : V} (q : Walk I E v w) :
    ∀ {u : V} (p : Walk I E u v), motive p → motive (p.append q) :=
  match q with
  | .nil _ _ _ => fun p hp => p.append_nil.symm ▸ hp
  | .cons v i e j q => fun p hp =>
    concat_append p i e j q ▸ concatRecAux q (p.concat i e j _) (Hconcat p i e j _ hp)

/-- Recursion by adjoining the last traversal, with values in any sort. -/
@[elab_as_elim]
def concatRec {u v : V} (p : Walk I E u v) : motive p :=
  concatRecAux Hconcat p (.nil I E u) (Hnil u)

@[simp] lemma concatRec_nil (u : V) :
    concatRec (motive := motive) Hnil Hconcat (.nil I E u) = Hnil u := rfl

lemma concatRecAux_concat {a b c : V} (p : Walk I E a b) (q : Walk I E b c)
    (i : I) (e : E) (j : I) (d : V) (hp : motive p) :
    HEq (concatRecAux Hconcat (q.concat i e j d) p hp)
      (Hconcat (p.append q) i e j d (concatRecAux Hconcat q p hp)) := by
  have hcongr {a b : V} (p q : Walk I E a b) (i : I) (e : E) (j : I) (d : V)
      (h : p = q) (hp : motive p) (hq : motive q) (hh : HEq hp hq) :
      HEq (Hconcat p i e j d hp) (Hconcat q i e j d hq) := by
    subst q
    cases hh
    rfl
  induction q generalizing a with
  | nil v =>
    simp only [concat_nil, single, concatRecAux, eqRec_heq_iff]
    exact hcongr p (p.append (.nil I E v)) i e j d p.append_nil.symm hp
      (p.append_nil.symm ▸ hp) (by simp)
  | cons v i' f j' q ih =>
    simp only [concat_cons, concatRecAux, eqRec_heq_iff]
    exact (ih (p.concat i' f j' _) (Hconcat p i' f j' _ hp)).trans
      (hcongr _ _ i e j d (concat_append p i' f j' q) _ _ (by simp))

@[simp] lemma concatRec_concat (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) :
    concatRec (motive := motive) Hnil Hconcat (p.concat i e j w) =
      Hconcat p i e j w (concatRec (motive := motive) Hnil Hconcat p) := by
  exact eq_of_heq (concatRecAux_concat Hconcat (.nil I E u) p i e j w (Hnil u))

end ConcatRec

/-- Induction by adjoining the last traversal. -/
@[elab_as_elim] theorem reverse_induction {motive : ∀ {u v : V}, Walk I E u v → Prop}
    (nil : ∀ (u : V), motive (.nil I E u))
    (concat : ∀ {u v : V} (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V),
      motive p → motive (p.concat i e j w)) {u v : V} (p : Walk I E u v) : motive p :=
  concatRec nil concat p

lemma exists_concat (p : Walk I E u v) (hp : p.length ≠ 0) :
    ∃ (w : V) (i : I) (e : E) (j : I) (q : Walk I E u w), p = q.concat i e j v := by
  induction p using reverse_induction with
  | nil u => exact (hp rfl).elim
  | concat q i e j v ih => exact ⟨_, i, e, j, q, rfl⟩

/-- Drop the first traversal, repeating the endpoint for an empty walk. -/
def tail (p : Walk I E u v) : Walk I E (p.getVert 1) v := p.drop 1

/-- Drop the last traversal, repeating the endpoint for an empty walk. -/
def dropLast (p : Walk I E u v) : Walk I E u (p.getVert (p.length - 1)) :=
  p.take (p.length - 1)

@[simp] lemma tail_nil : (nil I E u).tail = nil I E u := rfl

@[simp] lemma tail_cons (p : Walk I E v w) :
    (cons u i e j p).tail.copy (by simp) rfl = p := by cases p <;> rfl

@[simp] lemma dropLast_nil : (nil I E u).dropLast = nil I E u := rfl

@[simp] lemma length_tail (p : Walk I E u v) : p.tail.length = p.length - 1 := length_drop ..

@[simp] lemma length_dropLast (p : Walk I E u v) : p.dropLast.length = p.length - 1 := by
  simp [dropLast]

@[simp] lemma incidencePairs_reverse (p : Walk I E u v) :
    p.reverse.incidencePairs = p.incidencePairs.reverse.map Prod.swap := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [reverse_cons, single, ih]

@[simp] lemma sourceIncs_reverse (p : Walk I E u v) :
    p.reverse.sourceIncs = p.targetIncs.reverse := by
  simp [sourceIncs_eq_map, targetIncs_eq_map, List.map_reverse, List.map_map, Function.comp_def]

@[simp] lemma targetIncs_reverse (p : Walk I E u v) :
    p.reverse.targetIncs = p.sourceIncs.reverse := by
  simp [sourceIncs_eq_map, targetIncs_eq_map, List.map_reverse, List.map_map, Function.comp_def]

end Walk
