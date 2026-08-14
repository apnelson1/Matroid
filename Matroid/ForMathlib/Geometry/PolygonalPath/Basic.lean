module

public import Mathlib.Topology.Separation.Connected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Matroid.ForMathlib.Analysis.Convex.Segment
public import Matroid.ForMathlib.List.Basic
public import Matroid.ForMathlib.Topology.Path
public import Matroid.ForMathlib.Topology.MetricSpace

/-!
# Polygonal paths

A `PolygonalPath x y` is a finite sequence of points starting at `x` and ending at `y`, thought of
as the piecewise-linear path that visits them in order. It carries strictly more information than
the set it traces out (`toSet`) or the path that traverses it (`toPath`): the list of vertices is
part of the data.

This file contains only the operations that make sense for a path with *arbitrary* endpoints.
Operations that only make sense for closed paths — rotating the base point, and the notion of a
simple *closed* curve — belong to `Polygon`; see
`Matroid.ForMathlib.Geometry.Polygon.PolygonalPath` for the dictionary between the two.

## Main definitions

* `PolygonalPath x y` : the type of polygonal paths from `x` to `y`. The base case `nil x` has no
  segments at all, and `direct x y` is the single segment from `x` to `y`.
* `vertices`, `edges`, `internal`, `length` : the combinatorial data.
* `ofList` : build a path with at least one segment from its list of internal vertices.
* `append`, `snoc`, `reverse`, `drop` : concatenation, reversal, and suffixes.
* `cast` : transport along equalities of the endpoints.
* `toSet` : the set of points covered, defined by recursion; `toSet_eq_range_toPath` identifies it
  with the range of the parametrization.
* `toPath` : the topological path traversing `P`, used only to interface with topology.
* `breakAt`, `subdivide` : cut at, resp. insert, a point of `toSet` as a vertex.
* `IsSimple` : distinct vertices, and distinct segments meeting only in shared endpoints.
* `IsTrivial`, `HasNondegenerateEdges` : all vertices equal, resp. no segment is a point.

## Main statements

The characterization to work from is `isSimple_append_iff`:
```
(A.append B).IsSimple ↔ A.IsSimple ∧ B.IsSimple ∧ A.toSet ∩ B.toSet ⊆ {y}
```
i.e. a concatenation is simple exactly when the two pieces meet only at the point they share.
`isSimple_cons_iff` is the case `A = direct x y`, and the closed analogue (with the *two* shared
endpoints on the right) is the bridge to `Polygon.IsSimple`.

`injective_toPath_iff` connects `IsSimple` to the parametrization, and
`exists_isSimple_toSet_subset` is arc extraction: any polygonal path contains a simple path with
the same endpoints.

## Design notes

* The base case is `nil x : PolygonalPath x x`, with no segments, rather than a single segment.
  This makes `nil` a two-sided identity for `append`, makes splitting at *any* vertex total
  (`exists_append_eq_of_mem_vertices`, with no interiority hypothesis), and makes arc extraction
  hypothesis-free (`M = nil x` when `x = y`).
* Consequently `IsSimple` cannot be `Injective P.toPath`: since `toPath (cons a b as)` is
  `(Path.segment a b).trans as.toPath` and `toPath (nil x)` is constant, injectivity of the
  parametrization would fail for every path. `IsSimple` is therefore combinatorial, in exact
  parallel with `Polygon.IsSimple`, and `injective_toPath_iff` records the relationship. For the
  same reason `toPath` special-cases a final segment, so its `cons` equation has a nondegeneracy
  side condition (`toPath_cons`).
* `toSet` is likewise defined by recursion rather than as `range toPath`, so that `toSet_nil`,
  `toSet_cons` and `toSet_append` are cheap. `toSet_eq_range_toPath` is the interface to topology.
* `ofList` only produces paths with at least one segment, so `PolygonalPath x y` is no longer
  equivalent to `List α`; `equivList` is stated for `{P // 0 < P.length}`.

The earlier one-segment-base-case development in `WIP/Jun/Planarity/PolygonalPath.lean` informed
some of these proofs, but the `nil` cases and the combinatorial `IsSimple` API require separate
arguments.
-/

@[expose] public section

universe u

open Set Function List

variable {α : Type u} {a b c x y z : α} {L : List α}

/-- A polygonal path from `x` to `y` : a finite sequence of points beginning at `x` and ending at
`y`, to be joined consecutively by line segments. -/
inductive PolygonalPath : α → α → Type u where
  /-- The path that stays at `x`, with no segments. -/
  | nil (x : α) : PolygonalPath x x
  /-- Prepend the segment from `a` to `b` to a path starting at `b`. -/
  | cons (a b : α) {c : α} (as : PolygonalPath b c) : PolygonalPath a c

namespace PolygonalPath

/-- The path consisting of the single segment from `x` to `y`. -/
def direct (x y : α) : PolygonalPath x y := cons x y (nil y)

/-- Transport a path along equalities of its endpoints. Needed whenever a `Polygon` operation moves
the base point, since the endpoints then agree only propositionally. -/
def cast (P : PolygonalPath x y) {x' y' : α} (hx : x = x') (hy : y = y') : PolygonalPath x' y' :=
  hx ▸ hy ▸ P

@[simp] lemma cast_rfl (P : PolygonalPath x y) : P.cast rfl rfl = P := rfl

/-! ### Vertices, edges, length -/

/-- All the vertices of `P`, in order; a nonempty list beginning with `x` and ending with `y`. -/
def vertices : ∀ {x y : α}, PolygonalPath x y → List α
  | _, _, nil x => [x]
  | _, _, cons a _ as => a :: as.vertices

@[simp] lemma vertices_nil (x : α) : (nil x).vertices = [x] := rfl

@[simp] lemma vertices_cons (a b : α) (P : PolygonalPath b c) :
    (cons a b P).vertices = a :: P.vertices := rfl

@[simp] lemma vertices_direct (x y : α) : (direct x y).vertices = [x, y] := rfl

/-- The edges of `P`, as the list of ordered pairs of consecutive vertices. (Compare
`SimpleGraph.Walk.darts`, which is the same construction for walks in a graph; `Polygon.edgeSet`
is the corresponding *set* of points.) -/
def edges : ∀ {x y : α}, PolygonalPath x y → List (α × α)
  | _, _, nil _ => []
  | _, _, cons a b as => (a, b) :: as.edges

@[simp] lemma edges_nil (x : α) : (nil x).edges = [] := rfl

@[simp] lemma edges_cons (a b : α) (P : PolygonalPath b c) :
    (cons a b P).edges = (a, b) :: P.edges := rfl

@[simp] lemma edges_direct (x y : α) : (direct x y).edges = [(x, y)] := rfl
/-- The number of segments of `P`. -/
def length : ∀ {x y : α}, PolygonalPath x y → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ _ as => as.length + 1

@[simp] lemma length_nil (x : α) : (nil x).length = 0 := rfl

@[simp] lemma length_cons (a b : α) (P : PolygonalPath b c) :
    (cons a b P).length = P.length + 1 := rfl

@[simp] lemma length_direct (x y : α) : (direct x y).length = 1 := rfl

/-- The vertices of `P` other than its two endpoints. Junk (namely `[]`) when `P = nil x`. -/
def internal (P : PolygonalPath x y) : List α := P.vertices.tail.dropLast

variable (P : PolygonalPath x y)

@[simp] lemma internal_nil (x : α) : (nil x).internal = [] := rfl

@[simp] lemma internal_direct (x y : α) : (direct x y).internal = [] := rfl

/-- Note the nondegeneracy hypothesis: `(cons a b (nil b)).internal` is `[]`, not `[b]`. -/
lemma internal_cons {P : PolygonalPath b c} (h : 0 < P.length) :
    (cons a b P).internal = b :: P.internal := by
  cases P with
  | nil => simp at h
  | cons _ _ P =>
    simp only [internal, vertices_cons, List.tail_cons]
    rw [List.dropLast_cons_of_ne_nil (by cases P <;> simp)]

@[simp] lemma cast_vertices {x' y' : α} (hx : x = x') (hy : y = y') :
    (P.cast hx hy).vertices = P.vertices := by
  subst x'
  subst y'
  rfl

@[simp] lemma cast_length {x' y' : α} (hx : x = x') (hy : y = y') :
    (P.cast hx hy).length = P.length := by
  subst x'
  subst y'
  rfl

@[simp] lemma vertices_length : P.vertices.length = P.length + 1 := by
  induction P with
  | nil => rfl
  | cons _ _ P ih => simp [ih, Nat.add_comm]

@[simp] lemma edges_length : P.edges.length = P.length := by
  induction P <;> simp_all

@[simp] lemma internal_length : P.internal.length = P.length - 1 := by
  simp [internal, List.length_dropLast]

@[simp] lemma vertices_ne_nil : P.vertices ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

@[simp] lemma vertices_head? : P.vertices.head? = some x := by
  cases P <;> rfl

@[simp] lemma vertices_getLast? : P.vertices.getLast? = some y := by
  induction P with
  | nil => rfl
  | cons _ _ P ih => simp [List.getLast?_cons, ih]

lemma first_mem_vertices : x ∈ P.vertices := by
  cases P <;> simp

lemma last_mem_vertices : y ∈ P.vertices := by
  induction P with
  | nil => simp
  | cons _ _ P ih => simp [ih]

lemma vertices_eq_cons : P.vertices = x :: P.vertices.tail := by
  exact (List.cons_head?_tail P.vertices_head?).symm

lemma vertices_eq_concat : P.vertices = P.vertices.dropLast ++ [y] := by
  exact (List.dropLast_append_getLast? y P.vertices_getLast?).symm

@[simp] lemma cons_internal_concat (h : 0 < P.length) :
    x :: (P.internal ++ [y]) = P.vertices := by
  have ht : P.vertices.tail ≠ [] := by
    cases P with
    | nil => simp at h
    | cons => simp
  rw [internal, ← List.cons_append, ← List.dropLast_cons_of_ne_nil ht,
    ← P.vertices_eq_cons, ← P.vertices_eq_concat]

@[simp] lemma cons_internal (h : 0 < P.length) : x :: P.internal = P.vertices.dropLast := by
  have ht : P.vertices.tail ≠ [] := by
    cases P with
    | nil => simp at h
    | cons => simp
  rw [internal, ← List.dropLast_cons_of_ne_nil ht, ← P.vertices_eq_cons]

@[simp] lemma internal_concat (h : 0 < P.length) : P.internal ++ [y] = P.vertices.tail := by
  have hEq := P.cons_internal_concat h
  rw [P.vertices_eq_cons] at hEq
  exact (List.cons.inj hEq).2

lemma edges_eq_zip : P.edges = P.vertices.zip P.vertices.tail := by
  induction P with
  | nil => simp
  | cons a b P ih =>
    rw [vertices_cons, edges_cons, List.tail_cons, ih]
    rw [P.vertices_eq_cons]
    simp only [List.tail_cons, List.zip_cons_cons]

lemma mem_edges_iff {s : α × α} :
    s ∈ P.edges ↔ ∃ i, ∃ h : i + 1 < P.vertices.length,
      s = (P.vertices[i], P.vertices[i + 1]) := by
  rw [P.edges_eq_zip, List.mem_iff_getElem]
  have hzip : (P.vertices.zip P.vertices.tail).length = P.length := by
    rw [← P.edges_eq_zip, P.edges_length]
  refine ⟨?_, ?_⟩
  · grind
  rintro ⟨i, hi, rfl⟩
  refine ⟨i, ?_, ?_⟩
  · grind
  rw [List.getElem_zip, List.getElem_tail]

lemma fst_mem_vertices {s : α × α} (hs : s ∈ P.edges) : s.1 ∈ P.vertices := by
  rw [P.edges_eq_zip] at hs
  exact List.of_mem_zip hs |>.1

lemma snd_mem_vertices {s : α × α} (hs : s ∈ P.edges) : s.2 ∈ P.vertices := by
  rw [P.edges_eq_zip] at hs
  exact List.mem_of_mem_tail (List.of_mem_zip hs |>.2)

/-- A path with no segments is `nil`. Stated for a closed path, which is the only case in which the
hypothesis can hold. -/
lemma eq_nil_of_length_eq_zero (P : PolygonalPath x x) (h : P.length = 0) : P = nil x := by
  cases P with
  | nil => rfl
  | cons => simp at h

lemma length_pos_of_ne (h : x ≠ y) : 0 < P.length := by
  cases P with
  | nil => exact (h rfl).elim
  | cons => simp

lemma length_pos_iff : 0 < P.length ↔ P.vertices.tail ≠ [] := by
  cases P <;> simp

/-! ### Paths from lists -/

/-- The polygonal path from `x` to `y` whose internal vertices are the entries of `L`. Never `nil`:
`ofList x [] y` is `direct x y`. -/
def ofList (x : α) (L : List α) (y : α) : PolygonalPath x y :=
  match L with
  | [] => direct x y
  | a :: as => cons x a (ofList a as y)

@[simp] lemma ofList_vertices (x : α) (L : List α) (y : α) :
    (ofList x L y).vertices = x :: L ++ [y] := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih => simp [ofList, ih]

@[simp] lemma ofList_internal (x : α) (L : List α) (y : α) :
    (ofList x L y).internal = L := by
  rw [internal, ofList_vertices]
  simp

@[simp] lemma ofList_length (x : α) (L : List α) (y : α) :
    (ofList x L y).length = L.length + 1 := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih => simp [ofList, ih, Nat.add_comm]

/-- The `eta` rule for polygonal paths with at least one segment. -/
lemma ofList_internal_self (h : 0 < P.length) : ofList x P.internal y = P := by
  induction P with
  | nil => simp at h
  | @cons a b c P ih =>
    obtain hP | hP := em (0 < P.length)
    · grind [internal_cons hP, ofList]
    have hP0 : P.length = 0 := Nat.eq_zero_of_not_pos hP
    cases P with
    | nil => rfl
    | cons => simp at hP0

/-- Paths with at least one segment are equivalent to lists of internal vertices. -/
def equivList (x y : α) : {P : PolygonalPath x y // 0 < P.length} ≃ List α where
  toFun P := P.1.internal
  invFun L := ⟨ofList x L y, by simp⟩
  left_inv P := Subtype.ext (ofList_internal_self P.1 P.2)
  right_inv L := ofList_internal x L y

/-- Induction on the list of internal vertices, for paths with at least one segment. -/
lemma list_induction {motive : PolygonalPath x y → Prop} (P : PolygonalPath x y)
    (h : ∀ L, motive (ofList x L y)) (hP : 0 < P.length) : motive P := by
  rw [← P.ofList_internal_self hP]
  exact h _

/-- Strong induction on the number of segments. -/
lemma length_induction {motive : ∀ {x y : α}, PolygonalPath x y → Prop}
    (ih : ∀ {x y : α} (P : PolygonalPath x y),
      (∀ {u v : α} (Q : PolygonalPath u v), Q.length < P.length → motive Q) → motive P)
    (P : PolygonalPath x y) : motive P := by
  generalize hn : P.length = n
  induction n using Nat.strong_induction_on generalizing x y with
  | h n hrec =>
    apply ih P
    intro u v Q hQ
    exact hrec Q.length (hn ▸ hQ) (P := Q) rfl

/-! ### Concatenation, reversal, suffixes -/

/-- Concatenate two polygonal paths, identifying the end of the first with the start of the
second. `nil` is a two-sided identity. -/
def append : ∀ {x y z : α}, PolygonalPath x y → PolygonalPath y z → PolygonalPath x z
  | _, _, _, nil _, q => q
  | _, _, _, cons a b as, q => cons a b (as.append q)

@[simp] lemma nil_append (Q : PolygonalPath x z) : (nil x).append Q = Q := rfl

@[simp] lemma cons_append (a b : α) (P : PolygonalPath b y) (Q : PolygonalPath y z) :
    (cons a b P).append Q = cons a b (P.append Q) := rfl

@[simp] lemma direct_append (x y : α) (Q : PolygonalPath y z) :
    (direct x y).append Q = cons x y Q := rfl

/-- Append a single segment at the end of `P`. -/
def snoc (P : PolygonalPath x y) (z : α) : PolygonalPath x z := P.append (direct y z)

/-- Traverse `P` backwards. -/
def reverse : ∀ {x y : α}, PolygonalPath x y → PolygonalPath y x
  | _, _, nil x => nil x
  | _, _, cons a b as => as.reverse.append (direct b a)

/-- The subpath of `P` from its `i`-th vertex to `y`, with the `i`-th vertex named `u`. The lemmas
about it assume `u` is indeed the `i`-th vertex and that `i < P.length`; outside that range it is
junk. -/
def drop (P : PolygonalPath x y) (u : α) (i : ℕ) : PolygonalPath u y :=
  ofList u ((P.vertices.drop (i + 1)).dropLast) y

variable (Q : PolygonalPath y z)

@[simp] lemma append_nil : P.append (nil y) = P := by
  induction P <;> simp_all

@[simp] lemma append_vertices : (P.append Q).vertices = P.vertices ++ Q.vertices.tail := by
  induction P with
  | nil => simpa using Q.vertices_eq_cons
  | cons _ _ P ih => simp [ih]

@[simp] lemma append_edges : (P.append Q).edges = P.edges ++ Q.edges := by
  induction P <;> simp_all

@[simp] lemma append_length : (P.append Q).length = P.length + Q.length := by
  induction P <;> simp_all [Nat.add_assoc, Nat.add_comm]

lemma append_assoc {w : α} (R : PolygonalPath z w) :
    (P.append Q).append R = P.append (Q.append R) := by
  induction P <;> simp_all

@[simp] lemma snoc_vertices : (P.snoc z).vertices = P.vertices ++ [z] := by
  simp [snoc]

@[simp] lemma snoc_length : (P.snoc z).length = P.length + 1 := by
  simp [snoc]

@[simp] lemma reverse_nil (x : α) : (nil x).reverse = nil x := rfl

@[simp] lemma reverse_vertices : P.reverse.vertices = P.vertices.reverse := by
  induction P with
  | nil => rfl
  | cons a b P ih =>
    simp only [reverse, append_vertices, ih, vertices_direct, List.tail_cons,
      vertices_cons, List.reverse_cons]

@[simp] lemma reverse_edges : P.reverse.edges = (P.edges.map Prod.swap).reverse := by
  induction P with
  | nil => rfl
  | cons a b P ih => simp [reverse, ih]

@[simp] lemma reverse_length : P.reverse.length = P.length := by
  induction P <;> simp_all [reverse]

private lemma reverse_append_aux {P : PolygonalPath x y} {Q : PolygonalPath y z} :
    (P.append Q).reverse = Q.reverse.append P.reverse := by
  induction P with
  | nil => simp
  | cons a b P ih => simp [reverse, ih, append_assoc]

@[simp] lemma reverse_reverse : P.reverse.reverse = P := by
  induction P with
  | nil => rfl
  | cons a b P ih => simp [reverse, reverse_append_aux, ih, direct]

@[simp] lemma reverse_append : (P.append Q).reverse = Q.reverse.append P.reverse := by
  exact reverse_append_aux

@[simp] lemma reverse_snoc : (P.snoc z).reverse = cons z y P.reverse := by
  simp [snoc, reverse, direct]

/-- Induction peeling off the *last* segment. -/
lemma snoc_induction {motive : ∀ {x y : α}, PolygonalPath x y → Prop}
    (nil : ∀ x, motive (nil x))
    (snoc : ∀ {x y : α} (P : PolygonalPath x y) (z : α), motive P → motive (P.snoc z))
    (P : PolygonalPath x y) : motive P := by
  have aux : ∀ {x y : α} (Q : PolygonalPath x y), motive Q.reverse := by
    intro x y Q
    induction Q with
    | nil x => simpa using nil x
    | cons a b Q ih =>
      rw [reverse]
      exact snoc Q.reverse a ih
  simpa using aux P.reverse

/-- Splitting at a vertex, exactly: no new vertices are created and nothing is dropped. Unlike with
a one-segment base case, this needs no hypothesis beyond `a` being a vertex — at an endpoint one of
the two pieces is `nil`. -/
lemma exists_append_eq_of_mem_vertices (ha : a ∈ P.vertices) :
    ∃ (A : PolygonalPath x a) (B : PolygonalPath a y), P = A.append B := by
  induction P generalizing a with
  | nil x =>
    simp only [vertices_nil, List.mem_singleton] at ha
    cases ha
    exact ⟨nil x, nil x, rfl⟩
  | @cons x b y P ih =>
    simp only [vertices_cons, List.mem_cons] at ha
    obtain rfl | ha := ha
    · exact ⟨nil a, cons a b P, rfl⟩
    obtain ⟨A, B, rfl⟩ := ih ha
    exact ⟨cons x b A, B, rfl⟩

@[simp] lemma drop_zero (h : 0 < P.length) : P.drop x 0 = P := by
  simpa [drop, internal] using P.ofList_internal_self h

@[simp] lemma drop_length (i : ℕ) (u : α) (hi : i < P.length) :
    (P.drop u i).length = P.length - i := by
  simp [drop, List.length_dropLast]
  omega

lemma drop_vertices (u : α) (i : ℕ) (hu : P.vertices[i]? = some u) (hi : i < P.length) :
    (P.drop u i).vertices = P.vertices.drop i := by
  induction P generalizing i u with
  | nil => simp at hi
  | @cons a b y P ih =>
    cases i with
    | zero =>
      simp only [vertices_cons, List.getElem?_cons_zero, Option.some.injEq] at hu
      subst u
      simpa using congrArg vertices (drop_zero (cons a b P) (by simp))
    | succ i =>
      simpa [drop, Nat.add_assoc] using ih u i (by simpa using hu) (by simpa using hi)

/-! ### Degenerate and nondegenerate paths -/

/-- A path all of whose vertices are equal; equivalently, a path whose image is a single point. -/
def IsTrivial (P : PolygonalPath x y) : Prop := ∀ z ∈ P.vertices, z = x

@[simp] lemma isTrivial_nil (x : α) : (nil x).IsTrivial := by simp [IsTrivial]

lemma IsTrivial.first_eq_last (h : P.IsTrivial) : x = y := (h y P.last_mem_vertices).symm

lemma IsTrivial.of_cons {P : PolygonalPath x y} (h : (cons a x P).IsTrivial) : P.IsTrivial := by
  intro z hz
  calc
    z = a := h z (by simp [hz])
    _ = x := (h x (by
      rw [vertices_cons]
      exact List.mem_cons_of_mem a P.first_mem_vertices)).symm

lemma isTrivial_iff_vertices_eq_replicate :
    P.IsTrivial ↔ P.vertices = List.replicate (P.length + 1) x := by
  refine ⟨?_, ?_⟩
  · intro h
    exact List.eq_replicate_iff.mpr ⟨by simp, fun z hz => h z hz⟩
  intro h z hz
  rw [h] at hz
  simpa using hz

/-- No segment of `P` is degenerate, i.e. consecutive vertices are distinct. This is what a
"normalised" walk is; compare `Polygon.HasNondegenerateEdges`. -/
def HasNondegenerateEdges (P : PolygonalPath x y) : Prop := ∀ s ∈ P.edges, s.1 ≠ s.2

@[simp] lemma hasNondegenerateEdges_nil (x : α) : (nil x).HasNondegenerateEdges := by
  simp [HasNondegenerateEdges]

@[simp] lemma hasNondegenerateEdges_direct :
    (direct x y).HasNondegenerateEdges ↔ x ≠ y := by
  simp [HasNondegenerateEdges]

@[simp] lemma hasNondegenerateEdges_cons {P : PolygonalPath b y} :
    (cons a b P).HasNondegenerateEdges ↔ a ≠ b ∧ P.HasNondegenerateEdges := by
  simp [HasNondegenerateEdges]

@[simp] lemma hasNondegenerateEdges_append :
    (P.append Q).HasNondegenerateEdges ↔
      P.HasNondegenerateEdges ∧ Q.HasNondegenerateEdges := by
  simp only [HasNondegenerateEdges, append_edges, List.forall_mem_append]

@[simp] lemma hasNondegenerateEdges_reverse :
    P.reverse.HasNondegenerateEdges ↔ P.HasNondegenerateEdges := by
  simp only [HasNondegenerateEdges, reverse_edges, List.mem_reverse, List.mem_map, Prod.exists]
  refine ⟨?_, ?_⟩
  · intro h s hs
    exact fun hEq => h (s.2, s.1) ⟨s.1, s.2, hs, rfl⟩ hEq.symm
  rintro h s ⟨u, v, huv, rfl⟩
  exact fun hEq => h (u, v) huv hEq.symm

/-! ### The set of points covered -/

section Segments

variable [AddCommGroup α] [Module ℝ α] {P : PolygonalPath x y}

/-- The set of points covered by `P`. For `nil x` this is `{x}`, not `∅`. -/
def toSet : ∀ {x y : α}, PolygonalPath x y → Set α
  | _, _, nil x => {x}
  | _, _, cons a b as => segment ℝ a b ∪ as.toSet

@[simp] lemma toSet_nil (x : α) : (nil x).toSet = ({x} : Set α) := rfl

@[simp] lemma toSet_cons (a b : α) (P : PolygonalPath b c) :
    (cons a b P).toSet = segment ℝ a b ∪ P.toSet := rfl

@[simp] lemma toSet_direct (x y : α) : (direct x y).toSet = segment ℝ x y := by
  simp [direct, right_mem_segment]

variable (P : PolygonalPath x y) (Q : PolygonalPath y z)

@[simp] lemma toSet_append : (P.append Q).toSet = P.toSet ∪ Q.toSet := by
  induction P with
  | nil => cases Q <;> simp [left_mem_segment]
  | cons a b P ih => simp [ih, union_assoc]

@[simp] lemma toSet_snoc : (P.snoc z).toSet = P.toSet ∪ segment ℝ y z := by
  simp [snoc]

@[simp] lemma toSet_reverse : P.reverse.toSet = P.toSet := by
  induction P with
  | nil => rfl
  | cons a b P ih => simp [reverse, ih, segment_symm, union_comm]

@[simp] lemma toSet_cast {x' y' : α} (hx : x = x') (hy : y = y') :
    (P.cast hx hy).toSet = P.toSet := by
  subst x'
  subst y'
  rfl

lemma toSet_eq_insert_biUnion :
    P.toSet = insert y (⋃ s ∈ P.edges, segment ℝ s.1 s.2) := by
  induction P with
  | nil => simp
  | cons a b P ih =>
    rw [toSet_cons, ih]
    ext u
    simp only [edges_cons, List.mem_cons, mem_union, mem_insert_iff,
      mem_iUnion]
    aesop

lemma toSet_eq_biUnion (h : 0 < P.length) :
    P.toSet = ⋃ s ∈ P.edges, segment ℝ s.1 s.2 := by
  induction P with
  | nil => simp at h
  | @cons a b y P ih =>
    obtain hP | hP := em (0 < P.length)
    · rw [toSet_cons, ih hP]
      simp
    have hP0 : P.length = 0 := Nat.eq_zero_of_not_pos hP
    cases P with
    | nil => simp [right_mem_segment]
    | cons => simp at hP0

lemma mem_toSet_iff (h : 0 < P.length) {u : α} :
    u ∈ P.toSet ↔ ∃ s ∈ P.edges, u ∈ segment ℝ s.1 s.2 := by
  rw [P.toSet_eq_biUnion h]
  simp

lemma mem_toSet_of_mem_vertices {u : α} (hu : u ∈ P.vertices) : u ∈ P.toSet := by
  induction P with
  | nil => simpa using hu
  | cons a b P ih =>
    simp only [vertices_cons, List.mem_cons] at hu
    obtain rfl | hu := hu
    · exact mem_union_left _ (left_mem_segment ℝ _ b)
    exact mem_union_right _ (ih hu)

lemma vertices_subset_toSet : {u | u ∈ P.vertices} ⊆ P.toSet := fun _ => P.mem_toSet_of_mem_vertices

lemma segment_subset_toSet {s : α × α} (hs : s ∈ P.edges) : segment ℝ s.1 s.2 ⊆ P.toSet := by
  have hP : 0 < P.length := by
    rw [← P.edges_length]
    exact List.length_pos_of_ne_nil (ne_nil_of_mem hs)
  rw [P.toSet_eq_biUnion hP]
  exact subset_iUnion_of_subset s (subset_iUnion_of_subset hs le_rfl)

lemma toSet_nonempty : P.toSet.Nonempty := ⟨x, P.mem_toSet_of_mem_vertices P.first_mem_vertices⟩

lemma toSet_mono_drop (u : α) (i : ℕ) (hu : P.vertices[i]? = some u) (hi : i < P.length) :
    (P.drop u i).toSet ⊆ P.toSet := by
  induction P generalizing i u with
  | nil => simp at hi
  | @cons a b y P ih =>
    cases i with
    | zero =>
      simp only [vertices_cons, List.getElem?_cons_zero, Option.some.injEq] at hu
      subst u
      rw [drop_zero (cons a b P) (by simp)]
    | succ i =>
      have hi' : i < P.length := by simpa using hi
      simpa [drop, Nat.add_assoc] using (ih u i (by simpa using hu) hi').trans (subset_union_right)

/-! ### Simple paths -/

/-- `P.IsSimple` says that `P` has distinct vertices and that two distinct segments of `P` meet only
in endpoints common to both. Exactly parallel to `Polygon.IsSimple`; `nil x` is simple, and
`direct x x` is not. See `injective_toPath_iff` for the relation to the parametrization. -/
def IsSimple (P : PolygonalPath x y) : Prop :=
  P.vertices.Nodup ∧ P.edges.Pairwise fun s t =>
    segment ℝ s.1 s.2 ∩ segment ℝ t.1 t.2 ⊆ ({s.1, s.2} ∩ {t.1, t.2} : Set α)

@[simp] lemma isSimple_nil (x : α) : (nil x).IsSimple := by simp [IsSimple]

@[simp] lemma isSimple_direct : (direct x y).IsSimple ↔ x ≠ y := by
  simp [IsSimple, direct]

private lemma IsSimple.first_mem_segment {P : PolygonalPath x y} (h : P.IsSimple)
    {s : α × α} (hs : s ∈ P.edges) (hx : x ∈ segment ℝ s.1 s.2) :
    x = s.1 ∨ x = s.2 := by
  cases P with
  | nil => simp at hs
  | cons x b P =>
    simp only [edges_cons, List.mem_cons] at hs
    obtain rfl | hs := hs
    · simp
    have := ((List.pairwise_cons.mp h.2).1 (s.1, s.2) hs) ⟨left_mem_segment ℝ x b, hx⟩
    simpa only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, true_or, true_and] using this

/-- The basic recursion for simplicity: prepending a segment keeps a path simple exactly when the
new segment meets the old path only at the vertex they share. -/
lemma isSimple_cons_iff {P : PolygonalPath b y} :
    (cons a b P).IsSimple ↔ a ≠ b ∧ P.IsSimple ∧ segment ℝ a b ∩ P.toSet ⊆ {b} := by
  cases P with
  | nil => simp [IsSimple, right_mem_segment]
  | @cons b c y P =>
    let Q : PolygonalPath b y := cons b c P
    change (cons a b Q).IsSimple ↔ _
    refine ⟨?_, ?_⟩
    · intro h
      have hv := List.nodup_cons.mp h.1
      have he := List.pairwise_cons.mp h.2
      refine ⟨fun hab => hv.1 (hab ▸ Q.first_mem_vertices), ⟨hv.2, he.2⟩, fun u ⟨huS, huQ⟩ ↦ ?_⟩
      obtain ⟨s, hs, hus⟩ := Q.mem_toSet_iff (by simp [Q]) |>.mp huQ
      have huends := he.1 s hs ⟨huS, hus⟩
      obtain (rfl | rfl) := huends.1
      · apply (hv.1 ?_).elim
        obtain h | h := huends.2
        · rw [h]
          exact Q.fst_mem_vertices hs
        · rw [h]
          exact Q.snd_mem_vertices hs
      · rfl
    refine fun ⟨hab, hQ, hSQ⟩ ↦ ⟨?_, ?_⟩
    · change (a :: Q.vertices).Nodup
      rw [List.nodup_cons]
      exact ⟨fun haQ ↦ (hab (hSQ ⟨left_mem_segment ℝ a b, Q.mem_toSet_of_mem_vertices haQ⟩)), hQ.1⟩
    change List.Pairwise _ ((a, b) :: Q.edges)
    rw [List.pairwise_cons]
    refine ⟨fun s hs u hu ↦ ?_, hQ.2⟩
    obtain rfl : u = b := hSQ ⟨hu.1, Q.segment_subset_toSet hs hu.2⟩
    simp [hQ.first_mem_segment hs hu.2]

/-- The characterization to work from: a concatenation is simple exactly when both pieces are
simple and they meet only at the point they share. The closed analogue allows the two pieces to
meet at *both* shared endpoints; see `PolygonalPath.isSimpleLoop_append_iff`. -/
lemma isSimple_append_iff {A : PolygonalPath x y} {B : PolygonalPath y z} :
    (A.append B).IsSimple ↔ A.IsSimple ∧ B.IsSimple ∧ A.toSet ∩ B.toSet ⊆ {y} := by
  induction A with
  | nil x =>
    refine ⟨?_, ?_⟩
    · intro h
      exact ⟨isSimple_nil x, h, fun u hu => by simpa using hu.1⟩
    exact fun h => h.2.1
  | @cons a b y A ih =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨hab, hAB, hSAB⟩ := isSimple_cons_iff.mp h
      obtain ⟨hA, hB, hAB'⟩ := ih.mp hAB
      refine ⟨isSimple_cons_iff.mpr ⟨hab, hA, fun u hu ↦ ?_⟩, hB, fun u hu ↦ ?_⟩
      · exact hSAB ⟨hu.1, by simpa using mem_union_left B.toSet hu.2⟩
      · obtain huS | huA := hu.1
        · have hub : u = b := hSAB ⟨huS, by simpa using mem_union_right A.toSet hu.2⟩
          have hby : b = y := hAB' ⟨A.mem_toSet_of_mem_vertices A.first_mem_vertices,
            hub ▸ hu.2⟩
          exact hub.trans hby
        · exact hAB' ⟨huA, hu.2⟩
    rintro ⟨hA, hB, hAB⟩
    obtain ⟨hab, hA', hSA⟩ := isSimple_cons_iff.mp hA
    apply isSimple_cons_iff.mpr
    refine ⟨hab, ih.mpr ⟨hA', hB, fun u hu => hAB ⟨mem_union_right _ hu.1, hu.2⟩⟩, fun u hu ↦ ?_⟩
    rw [toSet_append] at hu
    obtain huA | huB := hu.2
    · exact hSA ⟨hu.1, huA⟩
    have huy : u = y := hAB ⟨mem_union_left A.toSet hu.1, huB⟩
    have hyb : y = b := hSA ⟨huy ▸ hu.1,
      A.mem_toSet_of_mem_vertices A.last_mem_vertices⟩
    exact huy.trans hyb

lemma isSimple_append_iff' {A : PolygonalPath x y} {B : PolygonalPath y z} :
    (A.append B).IsSimple ↔ A.IsSimple ∧ B.IsSimple ∧ A.toSet ∩ B.toSet = {y} := by
  rw [isSimple_append_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨hA, hB, hsub⟩
    refine ⟨hA, hB, hsub.antisymm fun u hu ↦ ?_⟩
    obtain rfl : u = y := by simpa using hu
    exact ⟨A.mem_toSet_of_mem_vertices A.last_mem_vertices,
      B.mem_toSet_of_mem_vertices B.first_mem_vertices⟩
  exact fun ⟨hA, hB, hEq⟩ ↦ ⟨hA, hB, hEq.le⟩

variable {P : PolygonalPath x y}

lemma IsSimple.of_cons {P : PolygonalPath b y} (h : (cons a b P).IsSimple) : P.IsSimple :=
  isSimple_cons_iff.mp h |>.2.1

lemma IsSimple.of_append_left {A : PolygonalPath x y} {B : PolygonalPath y z}
    (h : (A.append B).IsSimple) : A.IsSimple := isSimple_append_iff.mp h |>.1

lemma IsSimple.of_append_right {A : PolygonalPath x y} {B : PolygonalPath y z}
    (h : (A.append B).IsSimple) : B.IsSimple := isSimple_append_iff.mp h |>.2.1

@[simp] lemma isSimple_reverse : P.reverse.IsSimple ↔ P.IsSimple := by
  induction P with
  | nil => simp
  | cons a b P ih =>
    rw [reverse, isSimple_append_iff, ih, isSimple_direct, isSimple_cons_iff]
    simp only [toSet_reverse, toSet_direct, ne_eq]
    simp [segment_symm, inter_comm, ne_comm, and_left_comm]

@[simp] lemma isSimple_cast {x' y' : α} (hx : x = x') (hy : y = y') :
    (P.cast hx hy).IsSimple ↔ P.IsSimple := by
  subst x'
  subst y'
  rfl

lemma IsSimple.vertices_nodup (h : P.IsSimple) : P.vertices.Nodup := h.1

lemma IsSimple.edges_nodup (h : P.IsSimple) : P.edges.Nodup := by
  induction P with
  | nil => simp
  | cons a b P ih =>
    rw [edges_cons, List.nodup_cons]
    refine ⟨fun hab ↦ ?_, ih h.of_cons⟩
    exact (List.nodup_cons.mp h.1).1 (P.fst_mem_vertices hab)

lemma IsSimple.hasNondegenerateEdges (h : P.IsSimple) : P.HasNondegenerateEdges := by
  induction P with
  | nil => simp
  | cons a b P ih =>
    rw [hasNondegenerateEdges_cons]
    exact ⟨isSimple_cons_iff.mp h |>.1, ih h.of_cons⟩

/-- A simple path with distinct endpoints has at least one segment, and a simple path with equal
endpoints is `nil`. -/
lemma IsSimple.ne (h : P.IsSimple) (hP : 0 < P.length) : x ≠ y := by
  intro hxy
  have hxnot : x ∉ P.vertices.tail := by
    have hv := h.1
    rw [P.vertices_eq_cons] at hv
    exact (List.nodup_cons.mp hv).1
  apply hxnot
  have hy : y ∈ P.vertices.tail := by
    rw [← P.internal_concat hP]
    simp
  exact hxy.symm ▸ hy

lemma IsSimple.isTrivial_iff (h : P.IsSimple) : P.IsTrivial ↔ P.length = 0 := by
  refine ⟨fun htriv ↦ ?_, ?_⟩
  · by_contra hne
    exact h.ne (Nat.pos_of_ne_zero hne) htriv.first_eq_last
  intro hzero
  cases P with
  | nil => simp
  | cons => simp at hzero

private lemma IsSimple.mem_segment_iff_of_mem_vertices_aux (h : P.IsSimple) {u : α}
    (hu : u ∈ P.vertices) {s : α × α} (hs : s ∈ P.edges) :
    u ∈ segment ℝ s.1 s.2 ↔ u = s.1 ∨ u = s.2 := by
  refine ⟨?_, fun hends => hends.elim (fun e => e ▸ left_mem_segment ℝ _ _)
    (fun e => e ▸ right_mem_segment ℝ _ _)⟩
  intro hus
  obtain ⟨A, B, rfl⟩ := P.exists_append_eq_of_mem_vertices hu
  obtain hs | hs := (by simpa using hs)
  · have hs' : (s.2, s.1) ∈ A.reverse.edges := by
      rw [reverse_edges]
      simp only [List.mem_reverse, List.mem_map, Prod.exists]
      exact ⟨s.1, s.2, hs, rfl⟩
    have hu' : u ∈ segment ℝ s.2 s.1 := by simpa [segment_symm] using hus
    have hArev : A.reverse.IsSimple := isSimple_reverse.mpr (isSimple_append_iff.mp h).1
    rcases hArev.first_mem_segment hs' hu' with hsu | hsu
    · exact Or.inr hsu
    · exact Or.inl hsu
  exact (isSimple_append_iff.mp h).2.1.first_mem_segment hs hus

/-- A point of a simple path which is not a vertex lies on a unique segment. -/
lemma IsSimple.existsUnique_edge (h : P.IsSimple) {u : α} (hu : u ∈ P.toSet)
    (huv : u ∉ P.vertices) : ∃! s ∈ P.edges, u ∈ segment ℝ s.1 s.2 := by
  have hP : 0 < P.length := by
    by_contra hP
    have hzero : P.length = 0 := Nat.eq_zero_of_not_pos hP
    cases P with
    | nil => exact huv (by simpa using hu)
    | cons => simp at hzero
  obtain ⟨s, hs, hus⟩ := P.mem_toSet_iff hP |>.mp hu
  refine ⟨s, ⟨hs, hus⟩, fun t ⟨ht, hut⟩ ↦ by_contra fun hst ↦ ?_⟩
  have hsymm : Std.Symm fun s t : α × α =>
      segment ℝ s.1 s.2 ∩ segment ℝ t.1 t.2 ⊆ ({s.1, s.2} ∩ {t.1, t.2} : Set α) :=
    ⟨fun p q hpq v hv ↦ inter_comm .. ▸ hpq ⟨hv.2, hv.1⟩⟩
  exact huv (((h.2.forall hs ht (fun e => hst e.symm)) ⟨hus, hut⟩).1.elim
    (· ▸ P.fst_mem_vertices hs) (· ▸ P.snd_mem_vertices hs))

/-- A vertex of a simple path lies on the one or two segments incident to it, and no others. -/
lemma IsSimple.mem_segment_iff_of_mem_vertices (h : P.IsSimple) {u : α} (hu : u ∈ P.vertices)
    {s : α × α} (hs : s ∈ P.edges) : u ∈ segment ℝ s.1 s.2 ↔ u = s.1 ∨ u = s.2 :=
  h.mem_segment_iff_of_mem_vertices_aux hu hs

/-- Normalisation: a path covers the same set as a path with no degenerate segments. -/
lemma exists_hasNondegenerateEdges (P : PolygonalPath x y) :
    ∃ Q : PolygonalPath x y, Q.HasNondegenerateEdges ∧ Q.toSet = P.toSet ∧
      Q.length ≤ P.length := by
  induction P with
  | nil x => exact ⟨nil x, by simp⟩
  | @cons a b y P ih =>
    obtain ⟨Q, hQ, hset, hlen⟩ := ih
    by_cases hab : a = b
    · subst b
      refine ⟨Q, hQ, ?_, by simp; omega⟩
      rw [hset, toSet_cons, segment_same]
      exact (union_eq_right.mpr fun u hu => hu ▸
        P.mem_toSet_of_mem_vertices P.first_mem_vertices).symm
    refine ⟨cons a b Q, hasNondegenerateEdges_cons.mpr ⟨hab, hQ⟩, ?_, ?_⟩
    · simp [hset]
    simp
    omega

private lemma exists_first_inter_toSet {a b : α} (Q : PolygonalPath x y) (hQ : 0 < Q.length)
    (hne : (segment ℝ a b ∩ Q.toSet).Nonempty) :
    ∃ q ∈ segment ℝ a b ∩ Q.toSet, segment ℝ b q ∩ Q.toSet ⊆ {q} := by
  let U : α × α → Set ℝ := fun e =>
    {t | t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ segment ℝ e.1 e.2}
  let T : Set ℝ := ⋃ e ∈ {e | e ∈ Q.edges}, U e
  have hfinite : {e | e ∈ Q.edges}.Finite := Q.edges.finite_toSet
  have hcompactT : IsCompact T :=
    hfinite.isCompact_biUnion fun e _ => isCompact_setOf_lineMap_mem_segment a b e.1 e.2
  have hmemT (t : ℝ) : t ∈ T ↔ t ∈ Icc 0 1 ∧ AffineMap.lineMap a b t ∈ Q.toSet := by
    simp only [T, U, mem_iUnion, mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨e, he, ht, hte⟩
      exact ⟨ht, Q.segment_subset_toSet he hte⟩
    rintro ⟨ht, htQ⟩
    obtain ⟨e, he, hte⟩ := (Q.mem_toSet_iff hQ).mp htQ
    exact ⟨e, he, ht, hte⟩
  have hTne : T.Nonempty := by
    obtain ⟨w, hwab, hwQ⟩ := hne
    rw [segment_eq_image_lineMap] at hwab
    obtain ⟨t, ht, rfl⟩ := hwab
    exact ⟨t, (hmemT t).mpr ⟨ht, hwQ⟩⟩
  obtain ⟨m, hmT, hm⟩ := hcompactT.exists_isMaxOn hTne continuousOn_id
  have hmIcc : m ∈ Icc (0 : ℝ) 1 := (hmemT m).mp hmT |>.1
  refine ⟨AffineMap.lineMap a b m,
    ⟨lineMap_mem_segment ℝ a b hmIcc, (hmemT m).mp hmT |>.2⟩, ?_⟩
  intro w hw
  have himage : segment ℝ b (AffineMap.lineMap a b m) =
      AffineMap.lineMap a b '' Icc m 1 := by
    calc
      segment ℝ b (AffineMap.lineMap a b m) =
          segment ℝ (AffineMap.lineMap a b 1) (AffineMap.lineMap a b m) := by simp
      _ = AffineMap.lineMap a b '' segment ℝ 1 m :=
        (image_segment ℝ (AffineMap.lineMap a b) 1 m).symm
      _ = AffineMap.lineMap a b '' Icc m 1 := by
        rw [segment_symm ℝ 1 m, segment_eq_Icc hmIcc.2]
  rw [himage] at hw
  obtain ⟨t, ht, rfl⟩ := hw.1
  obtain rfl : t = m := le_antisymm (hm ((hmemT t).mpr ⟨⟨hmIcc.1.trans ht.1, ht.2⟩, hw.2⟩)) ht.1
  simp

private noncomputable def suffixAt {x y : α} (P : PolygonalPath x y) {a : α}
    (ha : a ∈ P.toSet) : PolygonalPath a y :=
  match P with
  | .nil x => by
    have hax : a = x := by simpa using ha
    subst a
    exact nil x
  | .cons u v vs => by
    classical
    if hau : a = u then
      subst a
      exact cons u v vs
    else if hauv : a ∈ openSegment ℝ u v then
      exact cons a v vs
    else
      have ha' : a ∈ vs.toSet := by
        simp only [toSet_cons, mem_union] at ha
        rcases ha with ha | ha
        · by_cases hav : a = v
          · subst a
            exact vs.mem_toSet_of_mem_vertices vs.first_mem_vertices
          · exact (hauv (mem_openSegment_of_ne_left_right
              (fun h => hau h.symm) (fun h => hav h.symm) ha)).elim
        · exact ha
      exact suffixAt vs ha'

@[simp] private lemma suffixAt_nil {a : α} (x : α) (ha : a ∈ (nil x).toSet) :
    (nil x).suffixAt ha = (nil x).cast (show a = x by simpa using ha).symm rfl := by
  obtain rfl : a = x := by simpa using ha
  rfl

private lemma suffixAt_toSet_subset {P : PolygonalPath x y} {a : α} (ha : a ∈ P.toSet) :
    (P.suffixAt ha).toSet ⊆ P.toSet := by
  induction P with
  | nil x => simp
  | @cons u v y P ih =>
    rw [PolygonalPath.suffixAt]
    split_ifs with hau hau
    · subst a
      exact subset_rfl
    · grind [toSet_cons, segment_union_eq_segment (openSegment_subset_segment ℝ u v hau)]
    exact (ih _).trans subset_union_right

private lemma IsSimple.suffixAt {P : PolygonalPath x y} (h : P.IsSimple) {a : α}
    (ha : a ∈ P.toSet) : (P.suffixAt ha).IsSimple := by
  induction P with
  | nil x => simp
  | @cons u v y P ih =>
    rw [PolygonalPath.suffixAt]
    split_ifs with hau hau
    · subst a; exact h
    · grind [isSimple_cons_iff, segment_union_eq_segment (openSegment_subset_segment ℝ u v hau)]
    exact ih h.of_cons _

/-- **Arc extraction.** Every polygonal path contains a simple polygonal path with the same
endpoints. No hypothesis is needed: when `x = y` the extracted path is `nil x`.

Proof sketch, by strong induction on `P.length` (`length_induction`) and avoiding all reference to
the parametrization. If `P.length = 0` take `M := nil x`. Otherwise write `P = cons x v₁ P'` and
`S := segment ℝ x v₁`.
* Let `k` be the largest index whose segment meets `S` (it exists, `k = 1` works), and let `q` be
  the last point of that segment's intersection with `S`, along that segment
  (`exists_first_inter_toSet`); for `k = 1` this gives `q = v₁`.
* Recurse on `cons q v_k (P.drop v_k k)` when `q ≠ v_k`, and on `P.drop v_k k` when `q = v_k`;
  either way the length drops. Maximality of `k` and the choice of `q` give
  `tail.toSet ∩ S = {q}`, hence `M'.toSet ∩ S ⊆ {q}`.
* Glue: `M := (direct x q).append M'` if `q ≠ x`, else `M := M'`, using `isSimple_append_iff` and
  `[x, q] ⊆ S` by convexity. -/
lemma exists_isSimple_toSet_subset (P : PolygonalPath x y) :
    ∃ M : PolygonalPath x y, M.IsSimple ∧ M.toSet ⊆ P.toSet := by
  induction P with
  | nil x => exact ⟨nil x, isSimple_nil x, subset_rfl⟩
  | @cons a b y P ih =>
    obtain ⟨Q, hQ, hQP⟩ := ih
    obtain rfl | hab := eq_or_ne a b
    · exact ⟨Q, hQ, hQP.trans subset_union_right⟩
    cases Q with
    | nil =>
      refine ⟨direct a b, isSimple_direct.mpr hab, ?_⟩
      rw [toSet_direct, toSet_cons]
      exact subset_union_left
    | @cons b c y Q =>
      let R : PolygonalPath b y := cons b c Q
      have hne : (segment ℝ b a ∩ R.toSet).Nonempty :=
        ⟨b, left_mem_segment ℝ b a, R.mem_toSet_of_mem_vertices R.first_mem_vertices⟩
      obtain ⟨q, hq, hfirst⟩ := exists_first_inter_toSet R (by simp [R]) hne
      let B : PolygonalPath q y := R.suffixAt hq.2
      have hB : B.IsSimple := hQ.suffixAt hq.2
      have hBR : B.toSet ⊆ R.toSet := suffixAt_toSet_subset hq.2
      obtain rfl | hqa := eq_or_ne q a
      · exact ⟨B, hB, hBR.trans (hQP.trans subset_union_right)⟩
      refine ⟨(direct a q).append B, isSimple_append_iff.mpr ?_, ?_⟩
      · exact ⟨isSimple_direct.mpr (fun haq => hqa haq.symm), hB,
          fun w hw ↦ hfirst ⟨by simpa [toSet_direct] using hw.1, hBR hw.2⟩⟩
      rw [toSet_append, toSet_direct, toSet_cons]
      apply union_subset
      · have hqS : q ∈ segment ℝ a b := by simpa [segment_symm] using hq.1
        rw [← segment_union_eq_segment hqS]
        exact subset_union_left.trans subset_union_left
      exact hBR.trans (hQP.trans subset_union_right)

end Segments

/-! ### The parametrization -/

section Path

-- `IsTopologicalAddGroup α` below subsumes `ContinuousAdd α`, which is needed for `toPath`.
set_option linter.overlappingInstances false

variable [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α] [ContinuousAdd α]

/-- The path traversing the segments of `P` in order. A final segment is traversed on all of
`[0,1]`, so that the parametrization of a path with at least one segment is never eventually
constant. The parametrization is an implementation detail: only the topological interface below
should depend on it. -/
noncomputable def toPath : ∀ {x y : α}, PolygonalPath x y → Path x y
  | _, _, nil x => Path.refl x
  | _, _, cons x w (nil _) => Path.segment x w
  | _, _, cons x w as => (Path.segment x w).trans as.toPath

@[simp] lemma toPath_nil (x : α) : (nil x).toPath = Path.refl x := rfl

@[simp] lemma toPath_direct (x y : α) : (direct x y).toPath = Path.segment x y := rfl

lemma toPath_cons {P : PolygonalPath b c} (h : 0 < P.length) :
    (cons a b P).toPath = (Path.segment a b).trans P.toPath := by
  cases P with
  | nil => simp at h
  | cons => rfl

variable (P : PolygonalPath x y) (Q : PolygonalPath y z)

/-- The interface between the combinatorial `toSet` and the parametrization. -/
@[simp] lemma toSet_eq_range_toPath : P.toSet = range P.toPath := by
  induction P with
  | nil => simp [toPath, Path.refl_range]
  | cons a b P ih =>
    cases P with
    | nil => simp [toPath, Path.range_segment, right_mem_segment]
    | cons b c P =>
      simp only [toSet_cons, toPath, Path.trans_range, Path.range_segment]
      conv_rhs => rw [← ih]
      rw [toSet_cons]

lemma isConnected_toSet : IsConnected P.toSet := by
  rw [P.toSet_eq_range_toPath]
  exact isConnected_range P.toPath.continuous

lemma isCompact_toSet [IsTopologicalAddGroup α] : IsCompact P.toSet := by
  rw [P.toSet_eq_range_toPath]
  exact isCompact_range P.toPath.continuous

lemma isClosed_toSet [IsTopologicalAddGroup α] [T2Space α] : IsClosed P.toSet :=
  P.isCompact_toSet.isClosed

lemma toSet_infinite_of_nontrivial [T1Space α] (h : P.toSet.Nontrivial) : P.toSet.Infinite :=
  P.isConnected_toSet.isPreconnected.infinite_of_nontrivial h

lemma isTrivial_iff_toSet_eq_singleton [T1Space α] : P.IsTrivial ↔ P.toSet = {x} := by
  refine ⟨?_, ?_⟩
  · intro h
    induction P with
    | nil => simp
    | cons a b P ih =>
      obtain rfl : b = a := h b (by simp [P.first_mem_vertices])
      rw [toSet_cons, segment_same, ih h.of_cons]
      simp
  intro h z hz
  have hz' := P.mem_toSet_of_mem_vertices hz
  rw [h] at hz'
  simpa using hz'

open unitInterval

/-- Simplicity is injectivity of the parametrization, except that `nil` is simple while its
parametrization is constant. -/
lemma injective_toPath_iff : Injective P.toPath ↔ P.IsSimple ∧ 0 < P.length := by
  induction P with
  | nil x =>
    simp only [toPath_nil, isSimple_nil, length_nil, lt_self_iff_false, and_false, iff_false]
    intro h
    have := h (a₁ := (0 : I)) (a₂ := 1)
    simp at this
  | @cons a b y P ih =>
    cases P with
    | nil =>
      change Injective (Path.segment a b) ↔ (direct a b).IsSimple ∧ 0 < (direct a b).length
      rw [isSimple_direct]
      simp only [length_direct, Nat.lt_one_iff, and_true]
      exact ⟨fun h hab => by
        subst b
        exact zero_ne_one (h (a₁ := (0 : I)) (a₂ := 1) (by simp)),
        Path.segment_injective_of_ne⟩
    | @cons b c y P =>
      let Q : PolygonalPath b y := cons b c P
      change Injective ((Path.segment a b).trans Q.toPath) ↔
        (cons a b Q).IsSimple ∧ 0 < (cons a b Q).length
      rw [Path.trans_injective_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨hseg, hQinj, hdj⟩
        obtain ⟨hQ, hQlen⟩ := ih.mp hQinj
        refine ⟨isSimple_cons_iff.mpr ⟨fun hab ↦ ?_, hQ, fun u hu ↦ ?_⟩, by simp⟩
        · subst b
          exact zero_ne_one (hseg (a₁ := (0 : I)) (a₂ := 1) (by simp))
        · by_contra hub
          have huS : u ∈ range (Path.segment a b) := by
            rw [Path.range_segment]
            exact hu.1
          have huQ : u ∈ range Q.toPath := by
            rw [← Q.toSet_eq_range_toPath]
            exact hu.2
          exact hdj.notMem_of_mem_left ⟨huS, hub⟩ huQ
      rintro ⟨hsimple, hlen⟩
      obtain ⟨hab, hQ, hinter⟩ := isSimple_cons_iff.mp hsimple
      have hQlen : 0 < Q.length := by simp [Q]
      refine ⟨Path.segment_injective_of_ne hab, ih.mpr ⟨hQ, hQlen⟩, ?_⟩
      rw [Set.disjoint_left]
      rintro u ⟨huS, hub⟩ huQ
      have huS' : u ∈ segment ℝ a b := by
        rw [← Path.range_segment]
        exact huS
      have huQ' : u ∈ Q.toSet := by
        rw [Q.toSet_eq_range_toPath]
        exact huQ
      exact hub (hinter ⟨huS', huQ'⟩)

/-! ### Cutting at, and inserting, a point of the image -/

/-- Split `P` at an arbitrary point `a` of its image, inserting `a` as a vertex of both halves.
Unlike `exists_append_eq_of_mem_vertices` this creates a new vertex, so
`(P.breakAt ha).1.append (P.breakAt ha).2` is `P.subdivide ha`, not `P`. -/
noncomputable def breakAt {x y : α} (P : PolygonalPath x y) {a} (ha : a ∈ P.toSet) :
    PolygonalPath x a × PolygonalPath a y :=
  match P with
  | .nil x => by
    obtain rfl : a = x := ha
    exact (nil _, nil _)
  | .cons u v vs => by
    classical
    if hau : a = u then
      subst a
      exact (nil u, cons u v vs)
    else if hauv : a ∈ openSegment ℝ u v then
      exact (direct u a, cons a v vs)
    else
      have ha' : a ∈ vs.toSet := by
        simp only [toSet_cons, mem_union] at ha
        rcases ha with ha | ha
        · by_cases hav : a = v
          · subst a
            exact vs.mem_toSet_of_mem_vertices vs.first_mem_vertices
          · exact (hauv (mem_openSegment_of_ne_left_right
              (fun h => hau h.symm) (fun h => hav h.symm) ha)).elim
        · exact ha
      let P' := vs.breakAt ha'
      exact (cons u v P'.1, P'.2)

/-- `P` with the point `a` of its image inserted as a vertex. -/
noncomputable def subdivide {x y : α} (P : PolygonalPath x y) {a} (ha : a ∈ P.toSet) :
    PolygonalPath x y := (P.breakAt ha).1.append (P.breakAt ha).2

variable {P : PolygonalPath x y} {a : α} (ha : a ∈ P.toSet)

@[simp] lemma breakAt_toSet_union : (P.breakAt ha).1.toSet ∪ (P.breakAt ha).2.toSet = P.toSet := by
  induction P with
  | nil x =>
    simp only [toSet_nil, mem_singleton_iff] at ha
    subst a
    simp [breakAt]
  | @cons u v y P ih =>
    rw [breakAt]
    split
    next hau =>
      subst a
      simp
    next hau =>
      split
      next hauv =>
        simp only [toSet_direct, toSet_cons]
        rw [← union_assoc, segment_union_eq_segment
          (openSegment_subset_segment ℝ u v hauv)]
      next hauv =>
        simp only [toSet_cons]
        rw [union_assoc, ih]

@[simp] lemma toSet_subdivide : (P.subdivide ha).toSet = P.toSet := by
  rw [subdivide, toSet_append, breakAt_toSet_union]

lemma mem_vertices_subdivide : a ∈ (P.subdivide ha).vertices := by
  rw [subdivide, append_vertices]
  exact List.mem_append_left _ (P.breakAt ha).1.last_mem_vertices

private lemma breakAt_length_sum_le {P : PolygonalPath x y} {a : α} (ha : a ∈ P.toSet) :
    (P.breakAt ha).1.length + (P.breakAt ha).2.length ≤ P.length + 1 := by
  induction P with
  | nil x =>
    simp only [toSet_nil, mem_singleton_iff] at ha
    subst a
    simp [breakAt]
  | @cons u v y P ih =>
    rw [breakAt]
    split
    next hau => subst a; simp
    next hau =>
      split
      next hauv => simp; omega
      next hauv =>
        have ha' : a ∈ P.toSet := by
          simp only [toSet_cons, mem_union] at ha
          rcases ha with ha | ha
          · by_cases hav : a = v
            · subst a
              exact P.mem_toSet_of_mem_vertices P.first_mem_vertices
            · exact (hauv (mem_openSegment_of_ne_left_right
                (fun h => hau h.symm) (fun h => hav h.symm) ha)).elim
          · exact ha
        have hle := ih ha'
        simp only [length_cons]
        omega

lemma subdivide_length_le : (P.subdivide ha).length ≤ P.length + 1 := by
  simpa [subdivide] using breakAt_length_sum_le ha

lemma vertices_subset_vertices_subdivide :
    {u | u ∈ P.vertices} ⊆ {u | u ∈ (P.subdivide ha).vertices} := by
  intro w hw
  induction P with
  | nil x =>
    simp only [toSet_nil, mem_singleton_iff] at ha
    subst a
    simpa [subdivide, breakAt] using hw
  | @cons u v y P ih =>
    rw [subdivide, breakAt]
    split
    next hau =>
      subst a
      simpa using hw
    next hau =>
      split
      next hauv =>
        simp only [vertices_cons, mem_cons, append_vertices, vertices_direct, tail_cons,
          mem_append] at hw ⊢
        obtain hw | hw := hw
        · exact Or.inl (Or.inl hw)
        exact Or.inr hw
      next hauv =>
        have ha' : a ∈ P.toSet := by
          simp only [toSet_cons, mem_union] at ha
          rcases ha with ha | ha
          · by_cases hav : a = v
            · subst a
              exact P.mem_toSet_of_mem_vertices P.first_mem_vertices
            · exact (hauv (mem_openSegment_of_ne_left_right
                (fun h => hau h.symm) (fun h => hav h.symm) ha)).elim
          · exact ha
        simp only [vertices_cons, mem_cons, append_vertices] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · apply List.mem_cons_of_mem
          simpa [subdivide] using ih ha' hw

/-- Subdividing does not change simplicity. -/
@[simp] lemma isSimple_subdivide_iff : (P.subdivide ha).IsSimple ↔ P.IsSimple := by
  induction P with
  | nil x =>
    simp only [toSet_nil, mem_singleton_iff] at ha
    subst a
    simp [subdivide, breakAt]
  | @cons u v y P ih =>
    rw [subdivide, breakAt]
    split
    next hau =>
      subst a
      simp
    next hau =>
      split
      next hauv =>
        have hua : u ≠ a := fun h => hau h.symm
        have huv : u ≠ v := by
          rintro rfl
          rw [openSegment_same] at hauv
          exact hua (mem_singleton_iff.mp hauv).symm
        have hav : a ≠ v := by
          rintro rfl
          exact huv (right_mem_openSegment_iff.mp hauv)
        have hinter : segment ℝ u a ∩ segment ℝ a v = {a} :=
          segment_inter_subsegments_eq_singleton huv hauv
        have hsplit := segment_union_eq_segment (openSegment_subset_segment ℝ u v hauv)
        have hsub₁ : segment ℝ u a ⊆ segment ℝ u v := by
          rw [← hsplit]
          exact subset_union_left
        have hsub₂ : segment ℝ a v ⊆ segment ℝ u v := by
          rw [← hsplit]
          exact subset_union_right
        simp only [direct_append, isSimple_cons_iff, toSet_cons]
        constructor
        · rintro ⟨_, ⟨_, hP, haP⟩, huaP⟩
          refine ⟨huv, hP, ?_⟩
          rintro w ⟨hwuv, hwP⟩
          rw [← hsplit] at hwuv
          rcases hwuv with hwa | hwv
          · have hwa' : w = a := huaP ⟨hwa, mem_union_right _ hwP⟩
            subst w
            exact haP ⟨left_mem_segment ℝ a v, hwP⟩
          · exact haP ⟨hwv, hwP⟩
        · rintro ⟨_, hP, huvP⟩
          refine ⟨hua, ⟨hav, hP, fun w hw => huvP ⟨hsub₂ hw.1, hw.2⟩⟩, ?_⟩
          rintro w ⟨hwu, hwrest⟩
          rcases hwrest with hwa | hwP
          · exact (Set.ext_iff.mp hinter w).mp ⟨hwu, hwa⟩
          · have hwv : w = v := huvP ⟨hsub₁ hwu, hwP⟩
            subst w
            have hva : v = a := by
              simpa using (Set.ext_iff.mp hinter v).mp ⟨hwu, right_mem_segment ℝ a v⟩
            exact (hav hva.symm).elim
      next hauv =>
        have ha' : a ∈ P.toSet := by
          simp only [toSet_cons, mem_union] at ha
          obtain ha | ha := ha
          · by_cases hav : a = v
            · subst a
              exact P.mem_toSet_of_mem_vertices P.first_mem_vertices
            · exact (hauv (mem_openSegment_of_ne_left_right
                (fun h => hau h.symm) (fun h => hav h.symm) ha)).elim
          exact ha
        change (cons u v (P.subdivide ha')).IsSimple ↔ (cons u v P).IsSimple
        rw [isSimple_cons_iff, ih ha', toSet_subdivide]
        exact (isSimple_cons_iff (a := u) (b := v) (P := P)).symm

/-- Cutting a simple path at a point of its image gives two simple paths meeting only at that
point. This is the open version of the "two arcs" decomposition of a simple closed curve. -/
lemma IsSimple.breakAt (h : P.IsSimple) (ha : a ∈ P.toSet) :
    (P.breakAt ha).1.IsSimple ∧ (P.breakAt ha).2.IsSimple ∧
      (P.breakAt ha).1.toSet ∩ (P.breakAt ha).2.toSet = {a} := by
  simpa only [subdivide, isSimple_append_iff'] using ((isSimple_subdivide_iff ha).mpr h)

/-- The two pieces of `IsSimple.breakAt` are the two *parameter* halves of `P.toPath`.

`IsSimple.breakAt` identifies the pieces combinatorially, as polygonal paths; this identifies them
analytically. An embedded arc has an injective `toPath`, so each piece is a connected subset of the
image whose parameter preimage is an interval, and the two intervals meet only at `t₀`
(`Path.image_Icc_subset_of_isConnected`). Callers cutting a cell twice — once at each end — need
this to compose the two cuts, since the second cut is taken in the *first piece's* parametrisation
while the conclusion has to be stated in `P`'s. -/
@[grind →]
lemma IsSimple.toSet_breakAt_eq [T2Space α] (hP : P.IsSimple) (hlen : 0 < P.length)
    (ha : a ∈ P.toSet) {t₀ : I} (ht₀ : P.toPath t₀ = a) :
    (P.breakAt ha).1.toSet = P.toPath '' Set.Icc (0 : I) t₀ ∧
    (P.breakAt ha).2.toSet = P.toPath '' Set.Icc t₀ (1 : I) := by
  have hinj : Function.Injective P.toPath := (injective_toPath_iff P).mpr ⟨hP, hlen⟩
  obtain ⟨_, _, hAB⟩ := hP.breakAt ha
  have hunion := P.breakAt_toSet_union (ha := ha)
  have hAsub : (P.breakAt ha).1.toSet ⊆ Set.range P.toPath := by
    rw [← P.toSet_eq_range_toPath, ← hunion]; exact Set.subset_union_left
  have hBsub : (P.breakAt ha).2.toSet ⊆ Set.range P.toPath := by
    rw [← P.toSet_eq_range_toPath, ← hunion]; exact Set.subset_union_right
  have hA : P.toPath '' Set.Icc (0 : I) t₀ ⊆ (P.breakAt ha).1.toSet :=
    Path.image_Icc_subset_of_isConnected hinj (P.breakAt ha).1.isConnected_toSet hAsub
      (by simp [Path.source]) (by simp [ht₀])
  have hB : P.toPath '' Set.Icc t₀ (1 : I) ⊆ (P.breakAt ha).2.toSet :=
    Path.image_Icc_subset_of_isConnected hinj (P.breakAt ha).2.isConnected_toSet hBsub
      (by simp [ht₀]) (by simp [Path.target])
  refine ⟨subset_antisymm ?_ hA, subset_antisymm ?_ hB⟩
  · intro w hw
    obtain ⟨t, rfl⟩ : w ∈ Set.range P.toPath := by
      have : w ∈ P.toSet := hunion ▸ Or.inl hw
      rwa [P.toSet_eq_range_toPath] at this
    refine ⟨t, ⟨bot_le, ?_⟩, rfl⟩
    by_contra ht
    have ht' : t₀ < t := lt_of_not_ge ht
    have hinter : P.toPath t ∈ (P.breakAt ha).1.toSet ∩ (P.breakAt ha).2.toSet :=
      ⟨hw, hB ⟨t, ⟨ht'.le, le_top⟩, rfl⟩⟩
    rw [hAB, Set.mem_singleton_iff] at hinter
    exact ht'.ne' (hinj (hinter.trans ht₀.symm))
  intro w hw
  obtain ⟨t, rfl⟩ : w ∈ Set.range P.toPath := by
    have : w ∈ P.toSet := hunion ▸ Or.inr hw
    rwa [P.toSet_eq_range_toPath] at this
  refine ⟨t, ⟨?_, le_top⟩, rfl⟩
  by_contra ht
  have ht' : t < t₀ := lt_of_not_ge ht
  have hinter : P.toPath t ∈ (P.breakAt ha).1.toSet ∩ (P.breakAt ha).2.toSet :=
    ⟨hA ⟨t, ⟨bot_le, ht'.le⟩, rfl⟩, hw⟩
  rw [hAB, Set.mem_singleton_iff] at hinter
  exact ht'.ne (hinj (hinter.trans ht₀.symm))

/-- Regression test for the `@[grind →]` above; it fails if the tag is removed.

The forward form is forced. `@[grind =]` is rejected twice over: the conclusion is a conjunction,
not an equality, and even after splitting it the left-hand side `(P.breakAt ha).1.toSet` does not
mention `t₀`, so the pattern could not instantiate it. The antecedent `P.toPath t₀ = a` is the only
place every variable appears together, and it is specific — headed by `toPath` — so keying there
costs nothing outside this API. -/
example [T2Space α] (hP : P.IsSimple) (hlen : 0 < P.length) (ha : a ∈ P.toSet) {t₀ : I}
    (ht₀ : P.toPath t₀ = a) : (P.breakAt ha).1.toSet = P.toPath '' Set.Icc (0 : I) t₀ := by grind

omit [ContinuousAdd α] in
/-- Locally, a simple path looks like the unique segment through the given point. This is the local
structure lemma the Jordan curve argument runs on; only the uniqueness of the segment is used, so it
is stated for that hypothesis. -/
lemma exists_nhds_inter_toSet_eq [IsTopologicalAddGroup α] [T2Space α] {s : α × α}
    (h : ∃! s ∈ P.edges, a ∈ segment ℝ s.1 s.2) (hs : s ∈ P.edges)
    (has : a ∈ segment ℝ s.1 s.2) :
    ∃ U ∈ nhds a, U ∩ P.toSet = U ∩ segment ℝ s.1 s.2 := by
  let T : Set (α × α) := {t | t ∈ P.edges ∧ t ≠ s}
  let K : Set α := ⋃ t ∈ T, segment ℝ t.1 t.2
  have hT : T.Finite := P.edges.finite_toSet.subset fun t ht => ht.1
  have hK : IsClosed K := by
    apply (hT.isCompact_biUnion fun t _ => isCompact_segment t.1 t.2).isClosed
  have haK : a ∉ K := by
    intro haK
    simp only [K, mem_iUnion] at haK
    obtain ⟨t, ht, hat⟩ := haK
    have hts : t = s := h.unique ⟨ht.1, hat⟩ ⟨hs, has⟩
    exact ht.2 hts
  refine ⟨Kᶜ, hK.isOpen_compl.mem_nhds haK, ?_⟩
  refine Set.ext (fun w ↦ ⟨?_, ?_⟩)
  · rintro ⟨hwK, hwP⟩
    have hPpos : 0 < P.length := by
      rw [← P.edges_length]
      exact List.length_pos_of_ne_nil (ne_nil_of_mem hs)
    obtain ⟨t, ht, hwt⟩ := (P.mem_toSet_iff hPpos).mp hwP
    refine ⟨hwK, ?_⟩
    by_cases hts : t = s
    · simpa [hts] using hwt
    · exfalso
      exact hwK (by
        simp only [K, mem_iUnion]
        exact ⟨t, ⟨ht, hts⟩, hwt⟩)
  exact fun ⟨hwK, hws⟩ ↦ ⟨hwK, P.segment_subset_toSet hs hws⟩

end Path

/-! ### First and last edges of a path -/

section Edges

variable {x y : α}

/-- A path of positive length has an edge ending at its last vertex. -/
@[grind →]
lemma exists_edge_ending_at_last {x y : α} {P : PolygonalPath x y} (h : 0 < P.length) :
    ∃ a, (a, y) ∈ P.edges := by
  have hrev : 0 < P.reverse.length := by simpa using h
  cases hP : P.reverse with
  | nil => simp [hP] at hrev
  | cons _ a Q =>
    refine ⟨a, ?_⟩
    have : (y, a) ∈ P.reverse.edges := by simp [hP]
    simpa [reverse_edges] using this

/-- A path of positive length has an edge starting at its first vertex. -/
@[grind →]
lemma exists_edge_starting_at_first {x y : α} {P : PolygonalPath x y} (h : 0 < P.length) :
    ∃ b, (x, b) ∈ P.edges := by
  cases P with
  | nil => simp at h
  | cons _ b Q => exact ⟨b, by simp⟩

@[simp, grind =]
lemma edges_cast {x y x' y' : α} (P : PolygonalPath x y) (hx : x = x') (hy : y = y') :
    (P.cast hx hy).edges = P.edges := by
  subst hx; subst hy; rfl

/-- Casting the right factor of an append agrees with casting the append. -/
@[grind =]
lemma append_cast_right {x p y : α} (A : PolygonalPath x p) (B : PolygonalPath p y)
    (heq : y = x) :
    (A.append B).cast rfl heq = A.append (B.cast rfl heq) := by
  induction heq
  rfl

end Edges

/-! ### The edge of a simple path through one of its endpoints -/

section SimpleEdge

variable [AddCommGroup α] [Module ℝ α]

/-- In a simple path, the only edge whose segment contains the last vertex is the last edge. -/
@[grind →]
lemma eq_last_edge_of_mem_segment {x p : α} {A : PolygonalPath x p} (hA : A.IsSimple)
    {a : α} (ha : (a, p) ∈ A.edges) {s : α × α} (hs : s ∈ A.edges)
    (hps : p ∈ segment ℝ s.1 s.2) : s = (a, p) := by
  have ha' : (p, a) ∈ A.reverse.edges := by simpa [reverse_edges] using ha
  have hs' : (s.2, s.1) ∈ A.reverse.edges := by simpa [reverse_edges] using hs
  have hps' : p ∈ segment ℝ s.2 s.1 := by rwa [segment_symm]
  cases hArev : A.reverse with
  | nil =>
    have hlen : A.reverse.length = 0 := by rw [hArev]; rfl
    have : A.length = 0 := by simpa using hlen
    cases A with
    | nil => simp at ha
    | cons => simp at this
  | cons _ b Q =>
    have hAr' : (cons p b Q).IsSimple := hArev ▸ (isSimple_reverse.mpr hA)
    obtain ⟨hpb, hQ, hmeet⟩ := isSimple_cons_iff.mp hAr'
    have ha_mem : (p, a) ∈ (p, b) :: Q.edges := by
      simpa [hArev, edges_cons] using ha'
    have hb_eq : a = b := by
      obtain heq | haQ := List.mem_cons.mp ha_mem
      · exact (Prod.mk.inj heq).2
      exact ((List.nodup_cons.mp hAr'.1).1 (Q.fst_mem_vertices haQ)).elim
    subst b
    have hs_mem : (s.2, s.1) ∈ (p, a) :: Q.edges := by
      simpa [hArev, edges_cons] using hs'
    rcases List.mem_cons.mp hs_mem with heq | hsQ
    · grind
    have hpQ : p ∈ Q.toSet := Q.segment_subset_toSet hsQ hps'
    have : p = a := mem_singleton_iff.mp (hmeet ⟨left_mem_segment ℝ p a, hpQ⟩)
    exact (hpb this).elim

/-- In a simple path, the only edge whose segment contains the first vertex is the first
edge. -/
@[grind →]
lemma eq_first_edge_of_mem_segment {p y : α} {B : PolygonalPath p y} (hB : B.IsSimple)
    {b : α} (hb : (p, b) ∈ B.edges) {s : α × α} (hs : s ∈ B.edges)
    (hps : p ∈ segment ℝ s.1 s.2) : s = (p, b) := by
  cases hBcases : B with
  | nil => simp [hBcases] at hb
  | cons _ c Q =>
    have hBsimp : (cons p c Q).IsSimple := hBcases ▸ hB
    obtain ⟨hpc, hQ, hmeet⟩ := isSimple_cons_iff.mp hBsimp
    have hb_mem : (p, b) ∈ (p, c) :: Q.edges := by
      simpa [hBcases, edges_cons] using hb
    have hc_eq : b = c := by
      rcases List.mem_cons.mp hb_mem with heq | hbQ
      · exact (Prod.mk.inj heq).2
      exact ((List.nodup_cons.mp hBsimp.1).1 (Q.fst_mem_vertices hbQ)).elim
    subst c
    have hs_mem : s ∈ (p, b) :: Q.edges := by
      simpa [hBcases, edges_cons] using hs
    rcases List.mem_cons.mp hs_mem with heq | hsQ
    · exact heq
    have hpQ : p ∈ Q.toSet := Q.segment_subset_toSet hsQ hps
    have : p = b := mem_singleton_iff.mp (hmeet ⟨left_mem_segment ℝ p b, hpQ⟩)
    exact (hpc this).elim

end SimpleEdge

section Metric

variable [NormedAddCommGroup α] [NormedSpace ℝ α]

open Metric

/-- A simple polygonal path meets a small enough ball around its start in its first segment only.

**The radius has to be chosen after the path.** A path may perfectly well leave a *fixed* ball
around its start and come back into it; what simplicity rules out is only that it returns to `x`
itself. So the statement produces a `ρ`, and any consumer needing a bound of this shape at a radius
it also gets from elsewhere must take the minimum of the two.

Route: `toSet_eq_insert_biUnion` writes `P.toSet` as `{y}` together with finitely many segments.
The tail `Q.toSet` is compact (`isCompact_segment`, `Set.Finite.isCompact_biUnion`) and misses `x`
by simplicity, so `exists_pos_le_dist_of_notMem` (`ForMathlib/Topology/MetricSpace.lean`) bounds `ρ`
away from it; half that bound is small enough. -/
theorem exists_ball_inter_subset_firstSegment {x y : α} {P : PolygonalPath x y}
    (hP : P.IsSimple) (hxy : x ≠ y) :
    ∃ ρ > 0, ∃ z ≠ x, P.toSet ∩ closedBall x ρ ⊆ segment ℝ x z ∧ segment ℝ x z ⊆ P.toSet := by
  classical
  cases P with
  | nil => exact (hxy rfl).elim
  | @cons _ b _ Q =>
    obtain ⟨hab, -, hinter⟩ := isSimple_cons_iff.mp hP
    have hxQ : x ∉ Q.toSet := by
      intro hx
      have : x ∈ segment ℝ x b ∩ Q.toSet := ⟨left_mem_segment _ _ _, hx⟩
      exact hab (by simpa using hinter this)
    have hKcompact : IsCompact Q.toSet := by
      rw [toSet_eq_insert_biUnion]
      exact isCompact_singleton.union
        (Q.edges.finite_toSet.isCompact_biUnion fun _ _ ↦ isCompact_segment _ _)
    obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_dist_of_notMem hKcompact.isClosed hxQ
    refine ⟨δ / 2, half_pos hδpos, b, hab.symm, fun u ⟨huP, huball⟩ ↦ ?_, ?_⟩
    · rw [toSet_cons] at huP
      obtain huseg | huQ := huP
      · exact huseg
      · linarith [mem_closedBall'.mp huball, hδle u huQ, hδpos]
    have hedge : (x, b) ∈ (cons x b Q).edges := by
      simp [edges_cons]
    exact (cons x b Q).segment_subset_toSet hedge

end Metric

end PolygonalPath
