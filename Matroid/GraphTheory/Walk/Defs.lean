/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Set.Card
public import Matroid.GraphTheory.HypergraphLike.Subgraph
public import Matroid.GraphTheory.HypergraphLike.Hierarchy.Directed

/-!
# Walks in a graph

`Walk I E u v` is an endpoint-indexed sequence of vertex labels, with an edge label and
an ordered pair of incidence labels at each step. It carries no graph-validity conditions.
This file defines its length, vertex support, edge and incidence lists, emptiness, and append.
-/

@[expose] public section

open Set Function Nat

inductive Walk {V : Type*} : Type _ → Type _ → V → V → Type _ where
| nil (I E : Type*) (v : V) : Walk I E v v
| cons {I E : Type _} (u : V) (i : I) (e : E) (j : I) {v w : V} (W : Walk I E v w) : Walk I E u w

namespace Walk

variable {V I E : Type*} {u v w x : V} {i j : I} {e : E}

instance : HypergraphLike V I E (Walk.nil I E v) where
  verts := {v}
  incs := ∅
  edges := ∅
  edgeMap' i := i.prop.elim
  attach' i := i.prop.elim
  IsSource i := false
  IsTarget i := false
  mem_incs_iff i := by grind

instance {v : V} : HypergraphLike.Directed (Walk.nil I E v) where
  not_isTarget_of_isSource _ _ hi := (Bool.eq_not_self false).mp hi

/-- The one-step walk with the specified vertex, incidence, and edge labels. -/
@[match_pattern, reducible]
def single (u : V) (i : I) (e : E) (j : I) (v : V) : Walk I E u v :=
  .cons u i e j (.nil I E v)

instance [DecidableEq I]: HypergraphLike V I E (single u i e j v) where
  verts := {u, v}
  incs := {i, j}
  edges := {e}
  edgeMap' k := ⟨e, rfl⟩
  attach' k := if k = i then ⟨u, by grind⟩ else ⟨v, by grind⟩
  IsSource k := if k = i then true else false
  IsTarget k := if k = j then true else false
  mem_incs_iff k := by grind

/-- The number of edge traversals, with repetitions counted. -/
def length {u v : V} : Walk I E u v → ℕ
  | .nil _ _ _ => 0
  | .cons _ _ _ _ p => p.length + 1

/-- The visited vertex labels in order, including both endpoints. -/
def support {u v : V} : Walk I E u v → List V
  | .nil _ _ u => [u]
  | .cons u _ _ _ p => u :: p.support

/-- The traversed edge labels in order, retaining repetitions. -/
def edges {u v : V} : Walk I E u v → List E
  | .nil _ _ _ => []
  | .cons _ _ e _ p => e :: p.edges

/-- The incidence labels in traversal order, retaining repetitions. -/
def incidences {u v : V} : Walk I E u v → List I
  | .nil _ _ _ => []
  | .cons _ i _ j p => i :: j :: p.incidences

@[simp] lemma length_nil : (nil I E u).length = 0 := rfl

@[simp] lemma length_cons (p : Walk I E v w) : (cons u i e j p).length = p.length + 1 := rfl

@[simp] lemma support_nil : (nil I E u).support = [u] := rfl

@[simp, grind =]
lemma support_cons (p : Walk I E v w) : (cons u i e j p).support = u :: p.support := rfl

@[simp] lemma edges_nil : (nil I E u).edges = [] := rfl

@[simp] lemma edges_cons (p : Walk I E v w) : (cons u i e j p).edges = e :: p.edges := rfl

@[simp] lemma incidences_nil : (nil I E u).incidences = [] := rfl

@[simp] lemma incidences_cons (p : Walk I E v w) :
    (cons u i e j p).incidences = i :: j :: p.incidences := rfl

@[simp, grind =]
lemma length_support (p : Walk I E u v) : p.support.length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih]

@[simp, grind =] lemma length_edges (p : Walk I E u v) : p.edges.length = p.length := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih]

@[simp, grind =] lemma length_incidences (p : Walk I E u v) :
    p.incidences.length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih, Nat.mul_add, Nat.add_assoc]

@[simp] lemma start_mem_support (p : Walk I E u v) : u ∈ p.support := by
  cases p <;> simp

@[simp] lemma end_mem_support (p : Walk I E u v) : v ∈ p.support := by
  induction p with
  | nil => simp
  | cons u i e j p ih => simp [ih]

/-- An empty walk has equal endpoints. -/
lemma eq_of_length_eq_zero (p : Walk I E u v) (h : p.length = 0) : u = v := by
  cases p with
  | nil => rfl
  | cons => simp at h

@[simp] lemma support_ne_nil (p : Walk I E u v) : p.support ≠ [] := by cases p <;> simp

instance : Inhabited (Walk I E u u) := ⟨nil I E u⟩

@[simp] lemma default_eq_nil : (default : Walk I E u u) = nil I E u := rfl

/-- Prepending a step with explicit vertex indices. -/
@[match_pattern]
abbrev cons' (u v w : V) (i : I) (e : E) (j : I) (p : Walk I E v w) : Walk I E u w :=
  cons u i e j p

/-- Emptiness for walks whose endpoint indices need not be definitionally equal. -/
inductive Nil : {u v : V} → Walk I E u v → Prop
  | nil (u : V) : Nil (.nil I E u)

@[simp, grind .] lemma nil_nil : (nil I E u).Nil := .nil u

@[simp] lemma not_nil_cons {p : Walk I E v w} : ¬ (cons u i e j p).Nil := nofun

instance (p : Walk I E u v) : Decidable p.Nil :=
  match p with
  | .nil _ _ u => isTrue (.nil u)
  | .cons _ _ _ _ _ => isFalse nofun

@[grind .]
protected lemma Nil.eq {p : Walk I E u v} : p.Nil → u = v
  | .nil _ => rfl

lemma not_nil_of_ne {p : Walk I E u v} : u ≠ v → ¬ p.Nil := mt Nil.eq

@[simp, grind .] lemma length_eq_zero_iff {p : Walk I E u v} : p.length = 0 ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.length_eq_zero⟩ := length_eq_zero_iff

@[simp] lemma eq_nil_iff_nil {p : Walk I E u u} : p = nil I E u ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.eq_nil⟩ := eq_nil_iff_nil

lemma nil_iff_support_eq {p : Walk I E u v} : p.Nil ↔ p.support = [u] := by
  cases p <;> simp

@[simp] lemma edges_eq_nil {p : Walk I E u v} : p.edges = [] ↔ p.Nil := by
  cases p <;> simp

@[simp] lemma incidences_eq_nil {p : Walk I E u v} : p.incidences = [] ↔ p.Nil := by
  cases p <;> simp

lemma not_nil_iff_lt_length {p : Walk I E u v} : ¬ p.Nil ↔ 0 < p.length := by
  simp [← length_eq_zero_iff, Nat.pos_iff_ne_zero]

lemma not_nil_iff {p : Walk I E u v} :
    ¬ p.Nil ↔ ∃ (w : V) (i : I) (e : E) (j : I) (q : Walk I E w v), p = cons u i e j q := by
  cases p <;> simp

lemma exists_eq_cons_of_ne (hne : u ≠ v) (p : Walk I E u v) :
    ∃ (w : V) (i : I) (e : E) (j : I) (q : Walk I E w v), p = cons u i e j q :=
  not_nil_iff.mp (not_nil_of_ne hne)

@[simp] lemma exists_nil_iff : (∃ p : Walk I E u v, p.Nil) ↔ u = v := by
  refine ⟨fun ⟨_, hp⟩ => hp.eq, ?_⟩
  rintro rfl
  exact ⟨nil I E u, .nil u⟩

@[simp] lemma exists_length_eq_zero_iff : (∃ p : Walk I E u v, p.length = 0) ↔ u = v := by
  simp

/-- Eliminate a nonempty walk by exposing its first step and tail. -/
@[elab_as_elim]
def notNilRec {motive : {u w : V} → (p : Walk I E u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : V} → (i : I) → (e : E) → (j : I) → (q : Walk I E v w) →
      motive (cons u i e j q) not_nil_cons) (p : Walk I E u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil _ _ u => fun hp => absurd (.nil u) hp
  | .cons _ i e j q => fun _ => cons i e j q

@[simp]
lemma notNilRec_cons {motive : {u w : V} → (p : Walk I E u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : V} → (i : I) → (e : E) → (j : I) → (q : Walk I E v w) →
      motive (Walk.cons u i e j q) not_nil_cons) (q : Walk I E v w) :
    notNilRec cons (.cons u i e j q) not_nil_cons = cons i e j q := rfl

@[simp] lemma length_single : (single u i e j v).length = 1 := rfl

@[simp] lemma support_single : (single u i e j v).support = [u, v] := rfl

@[simp] lemma edges_single : (single u i e j v).edges = [e] := rfl

@[simp] lemma incidences_single : (single u i e j v).incidences = [i, j] := rfl

lemma exists_eq_single_of_length_eq_one {p : Walk I E u v} (hp : p.length = 1) :
    ∃ (i : I) (e : E) (j : I), p = single u i e j v := by
  cases p with
  | nil => simp at hp
  | cons u i e j p =>
    cases p with
    | nil => exact ⟨i, e, j, rfl⟩
    | cons => simp at hp

@[simp]
lemma exists_length_eq_one_iff : (∃ p : Walk I E u v, p.length = 1) ↔ Nonempty I ∧ Nonempty E := by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨⟨i⟩, ⟨e⟩⟩ ↦ ⟨single u i e i v, rfl⟩⟩
  obtain ⟨i, e, j, rfl⟩ := exists_eq_single_of_length_eq_one hp
  exact ⟨⟨i⟩, ⟨e⟩⟩

@[simp] lemma head_support (p : Walk I E u v) : p.support.head p.support_ne_nil = u := by
  cases p <;> rfl

@[simp] lemma head?_support (p : Walk I E u v) : p.support.head? = some u := by
  cases p <;> rfl

@[simp] lemma getLast_support (p : Walk I E u v) : p.support.getLast p.support_ne_nil = v := by
  induction p <;> simp_all

@[simp] lemma cons_tail_support (p : Walk I E u v) : u :: p.support.tail = p.support := by
  cases p <;> rfl

@[simp] lemma support_nonempty (p : Walk I E u v) : {x | x ∈ p.support}.Nonempty :=
  ⟨u, p.start_mem_support⟩

lemma mem_support_iff (p : Walk I E u v) : x ∈ p.support ↔ x = u ∨ x ∈ p.support.tail := by
  cases p <;> simp

lemma mem_support_nil_iff : x ∈ (nil I E u).support ↔ x = u := by simp

lemma end_mem_tail_support {p : Walk I E u v} (hp : ¬ p.Nil) : v ∈ p.support.tail :=
  p.notNilRec (by simp) hp

lemma end_mem_tail_support_of_ne (hne : u ≠ v) (p : Walk I E u v) : v ∈ p.support.tail :=
  end_mem_tail_support (not_nil_of_ne hne)

lemma support_suffix_support_cons (p : Walk I E v w) : p.support <:+ (cons u i e j p).support := by
  simp

lemma support_subset_support_cons (p : Walk I E v w) : p.support ⊆ (cons u i e j p).support := by
  simp

lemma coe_support (p : Walk I E u v) : (p.support : Multiset V) = {u} + p.support.tail := by
  cases p <;> rfl

@[simp] lemma support_getElem_zero (p : Walk I E u v) : p.support[0]'(by simp) = u := by
  cases p <;> rfl

@[simp] lemma support_getElem_length (p : Walk I E u v) : p.support[p.length]'(by simp) = v := by
  induction p <;> simp_all

/-- The vertex, edge, and incidence lists together determine a walk. -/
@[ext]
lemma ext {p q : Walk I E u v} (hV : p.support = q.support) (hE : p.edges = q.edges)
    (hI : p.incidences = q.incidences) : p = q := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons => simp at hE
  | cons u i e j p ih =>
    cases q with
    | nil => simp at hE
    | cons u i' e' j' q =>
      simp only [support_cons, List.cons.injEq, true_and] at hV
      obtain ⟨rfl, hE⟩ := List.cons.inj hE
      obtain ⟨rfl, rfl, hI⟩ := by simpa only [incidences_cons, List.cons.injEq] using hI
      have hv := congrArg List.head? hV
      simp only [head?_support, Option.some.injEq] at hv
      subst_vars
      exact congrArg (cons u i e j) (ih hV (by simpa using hE) (by simpa using hI))

instance [DecidableEq V] [DecidableEq I] [DecidableEq E] : DecidableEq (Walk I E u v) :=
  fun p q => decidable_of_iff
    (p.support = q.support ∧ p.edges = q.edges ∧ p.incidences = q.incidences)
    ⟨fun h => ext h.1 h.2.1 h.2.2, fun h => by subst q; exact ⟨rfl, rfl, rfl⟩⟩

/-- Concatenation of walks with matching endpoints. -/
def append {u v w : V} : Walk I E u v → Walk I E v w → Walk I E u w
  | .nil _ _ _, q => q
  | .cons u i e j p, q => .cons u i e j (p.append q)

@[simp] lemma nil_append (p : Walk I E u v) : (nil I E u).append p = p := rfl

@[simp] lemma cons_append (p : Walk I E v w) (q : Walk I E w x) :
    (cons u i e j p).append q = cons u i e j (p.append q) := rfl

@[simp] lemma append_nil (p : Walk I E u v) : p.append (nil I E v) = p := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih]

lemma append_assoc (p : Walk I E u v) (q : Walk I E v w) (r : Walk I E w x) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih]

@[simp] lemma length_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp
  | cons u i e j p ih => simp [ih, Nat.add_right_comm]

@[simp] lemma edges_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih]

@[simp] lemma incidences_append (p : Walk I E u v) (q : Walk I E v w) :
    (p.append q).incidences = p.incidences ++ q.incidences := by
  induction p with
  | nil => rfl
  | cons u i e j p ih => simp [ih]

lemma mem_support_append (p : Walk I E u v) (q : Walk I E v w) {x : V} :
    x ∈ (p.append q).support ↔ x ∈ p.support ∨ x ∈ q.support := by
  induction p with
  | nil =>
    simp only [nil_append, support_nil, List.mem_singleton]
    exact ⟨Or.inr, fun h => h.elim (fun h => h ▸ q.start_mem_support) id⟩
  | cons u i e j p ih => simp [ih, or_assoc]

@[simp]
lemma nil_append_iff (p : Walk I E u v) (q : Walk I E v w) : (p.append q).Nil ↔ p.Nil ∧ q.Nil := by
  simp [← length_eq_zero_iff]

@[simp] lemma single_append (p : Walk I E v w) : (single u i e j v).append p = cons u i e j p := rfl

end Walk
