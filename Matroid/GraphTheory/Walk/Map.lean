/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.GraphTheory.Walk.Operations
public import Mathlib.Data.List.Basic

/-!
# Relabeling walks

`Walk.map` applies separate functions to vertex, incidence, and edge labels. The same function
maps both incidence labels of each step, so relabeling commutes with reversal.
-/

@[expose] public section

namespace Walk

variable {V I E V' I' E' V'' I'' E'' : Type*} {u v w : V} {i j : I} {e : E} {p q : Walk I E u v}
  {f : V → V'} {g : I → I'} {h : E → E'} {f' : V' → V''} {g' : I' → I''} {h' : E' → E''}

/-- Apply functions to the vertex, incidence, and edge labels of a walk. -/
def map (f : V → V') (g : I → I') (h : E → E') : {u v : V} → Walk I E u v → Walk I' E' (f u) (f v)
  | _, _, .nil _ _ u => .nil I' E' (f u)
  | _, _, .cons u i e j p => .cons (f u) (g i) (h e) (g j) (p.map f g h)

@[simp] lemma map_nil : (nil I E u).map f g h = nil I' E' (f u) := rfl

@[simp] lemma map_cons (p : Walk I E v w) :
    (cons u i e j p).map f g h = cons (f u) (g i) (h e) (g j) (p.map f g h) := rfl

@[simp] lemma length_map : (p.map f g h).length = p.length := by
  induction p <;> simp_all

@[simp] lemma support_map : (p.map f g h).support = p.support.map f := by
  induction p <;> simp_all

@[simp] lemma edges_map : (p.map f g h).edges = p.edges.map h := by
  induction p <;> simp_all

@[simp] lemma incidences_map : (p.map f g h).incidences = p.incidences.map g := by
  induction p <;> simp_all

@[simp] lemma incidencePairs_map :
    (p.map f g h).incidencePairs = p.incidencePairs.map (Prod.map g g) := by
  induction p <;> simp_all

@[simp] lemma sourceIncs_map : (p.map f g h).sourceIncs = p.sourceIncs.map g := by
  induction p <;> simp_all

@[simp] lemma targetIncs_map : (p.map f g h).targetIncs = p.targetIncs.map g := by
  induction p <;> simp_all

@[simp] lemma getVert_map (p : Walk I E u v) (n : ℕ) :
    (p.map f g h).getVert n = f (p.getVert n) := by
  induction p generalizing n with
  | nil => rfl
  | cons u i e j p ih => cases n <;> simp [ih]

@[simp] lemma map_id : p.map id id id = p := by
  induction p <;> simp_all

@[simp] lemma map_map : (p.map f g h).map f' g' h' = p.map (f' ∘ f) (g' ∘ g) (h' ∘ h) := by
  induction p <;> simp_all

/-- Injective label maps give an injective map on walks. -/
lemma map_injective (hf : Function.Injective f) (hg : Function.Injective g)
    (hh : Function.Injective h) : Function.Injective (map f g h : Walk I E u v → _) := by
  intro p q hpq
  apply ext
  · exact (List.map_injective_iff.mpr hf) (by simpa using congrArg support hpq)
  · exact (List.map_injective_iff.mpr hh) (by simpa using congrArg edges hpq)
  exact (List.map_injective_iff.mpr hg) (by simpa using congrArg incidences hpq)

lemma map_inj (hf : Function.Injective f) (hg : Function.Injective g) (hh : Function.Injective h) :
    p.map f g h = q.map f g h ↔ p = q := (map_injective hf hg hh).eq_iff

@[simp] lemma map_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).map f g h = (p.map f g h).append (q.map f g h) := by
  induction p <;> simp_all

@[simp] lemma map_concat (p : Walk I E u v) (i : I) (e : E) (j : I) (w : V) :
    (p.concat i e j w).map f g h = (p.map f g h).concat (g i) (h e) (g j) (f w) := by
  simp [concat, single]

@[simp] lemma map_reverse (p : Walk I E u v) : p.reverse.map f g h = (p.map f g h).reverse := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [reverse_cons, single, ih]

@[simp] lemma map_take (p : Walk I E u v) (n : ℕ) :
    (p.take n).map f g h = ((p.map f g h).take n).copy rfl (getVert_map p n) := by
  refine ext ?_ (by simp) ?_
  · simp only [support_copy, support_map]
    induction p generalizing n with | nil => simp | cons u i e j p ih => _
    cases n with
    | zero => rfl
    | succ n => simp [ih]
  simp only [incidences_copy, incidences_map]
  induction p generalizing n with | nil => simp | cons u i e j p ih => _
  cases n with
  | zero => rfl
  | succ n => simp [ih]

@[simp] lemma map_drop (p : Walk I E u v) (n : ℕ) :
    (p.drop n).map f g h = ((p.map f g h).drop n).copy (getVert_map p n) rfl := by
  refine ext ?_ (by simp) ?_
  · simp only [support_copy, support_map]
    induction p generalizing n with | nil => simp | cons u i e j p ih => _
    cases n with
    | zero => exact (cons u i e j p).support_map.symm
    | succ n => simp [ih]
  simp only [incidences_copy, incidences_map]
  induction p generalizing n with | nil => simp | cons u i e j p ih => _
  cases n with
  | zero => exact (cons u i e j p).incidences_map.symm
  | succ n => simp [ih]

@[simp] lemma map_tail (p : Walk I E u v) :
    p.tail.map f g h = (p.map f g h).tail.copy (getVert_map p 1) rfl := by
  simp [tail]

@[simp] lemma map_dropLast (p : Walk I E u v) :
    p.dropLast.map f g h = (p.map f g h).dropLast.copy rfl
      (by simp only [length_map, getVert_map]) := by
  refine ext ?_ ?_ ?_
  · simpa only [dropLast, map_take, support_copy] using
      congrArg (fun n => ((p.map f g h).take n).support) (congrArg (· - 1) p.length_map).symm
  · simpa only [dropLast, map_take, edges_copy] using
      congrArg (fun n => ((p.map f g h).take n).edges) (congrArg (· - 1) p.length_map).symm
  simpa only [dropLast, map_take, incidences_copy] using
    congrArg (fun n => ((p.map f g h).take n).incidences) (congrArg (· - 1) p.length_map).symm

end Walk
