module

import Matroid.GraphLike.Assembly

/-! Assembly tests use actual links: a circle, parallel arcs, and infinitely many loops. -/

open Set Function Topology Set.Notation
open scoped GraphLike

namespace GraphLikeAssemblyTests

private lemma circleLink : IsPrimitiveLink (univ : Set Circle) 1 1 :=
  isPrimitiveLink_iff_isCircuit.mpr ⟨circle_isCircuit, mem_univ _⟩

private lemma circle_neg_one_ne_one : (-1 : Circle) ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  simp only [Circle.coe_neg_one] at this
  exact absurd this (by norm_num)

-- A single loop is assembled with its singleton boundary, not discarded as degenerate.
example : ∃ G : GraphLike Circle,
    G.Finite ∧ G.carrier = univ ∧ univ ∈ E(G) ∧ G.edgeBoundary univ = {1} := by
  let Z : Set Circle := {1}
  let a (_ : Unit) : Z := ⟨1, rfl⟩
  have hv (i : Unit) : (univ : Set Circle) ∩ Z = {(a i).1, (a i).1} := by simp [Z, a]
  have hd : Pairwise fun i j : Unit ↦ Disjoint (univ \ Z) (univ \ Z) :=
    fun i j hij ↦ False.elim (hij (Subsingleton.elim _ _))
  let G := GraphLike.ofFiniteLinks Z (finite_singleton _) a a (fun _ ↦ univ)
    (fun _ ↦ circleLink) hv hd
  refine ⟨G, GraphLike.ofFiniteLinks_finite .., ?_,
    GraphLike.ofFiniteLinks_mem_edgeSet Z (finite_singleton _) a a (fun _ ↦ univ)
      (fun _ ↦ circleLink) hv hd (), ?_⟩
  · exact eq_univ_of_forall fun x ↦ Or.inr (mem_iUnion.mpr ⟨(), mem_univ x⟩)
  · change univ ∩ Z = {1}
    simp [Z]

-- Splitting a real circle provides two different arcs with the same two boundary vertices.
example : ∃ (G : GraphLike Circle) (e f : Set Circle),
    G.Finite ∧ e ∈ E(G) ∧ f ∈ E(G) ∧ e ≠ f ∧
      G.edgeBoundary e = G.edgeBoundary f ∧ e ∪ f = univ := by
  let m : Circle := -1
  let A := circleLink.splitLeft m
  let B := circleLink.splitRight m
  have hA : IsPrimitiveLink A 1 m :=
    circleLink.isPrimitiveLink_splitLeft (mem_univ _) circle_neg_one_ne_one
  have hB : IsPrimitiveLink B m 1 :=
    circleLink.isPrimitiveLink_splitRight (mem_univ _) circle_neg_one_ne_one
  have hcover : A ∪ B = univ := circleLink.splitLeft_union_splitRight m
  have hinter : A ∩ B = {m} ∪ ({1} ∩ {1}) :=
    circleLink.splitLeft_inter_splitRight (mem_univ _)
  let Z : Set Circle := {1, m}
  let a (_ : Bool) : Z := ⟨1, by simp [Z]⟩
  let b (_ : Bool) : Z := ⟨m, by simp [Z]⟩
  let L : Bool → Set Circle := fun i ↦ cond i A B
  have hl (i) : IsPrimitiveLink (L i) (a i).1 (b i).1 := by
    cases i
    · exact hB.symm
    · exact hA
  have hv (i) : L i ∩ Z = {(a i).1, (b i).1} := by
    change L i ∩ Z = Z
    exact inter_eq_right.mpr (pair_subset (hl i).left_mem (hl i).right_mem)
  have hab : A ∩ B ⊆ Z := by
    rw [hinter]
    simp [Z]
  have hdAB : Disjoint (A \ Z) (B \ Z) :=
    disjoint_left.mpr fun _ ha hb ↦ ha.2 (hab ⟨ha.1, hb.1⟩)
  have hd : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z) := by
    intro i j hij
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact hdAB.symm
    · exact hdAB
    · exact False.elim (hij rfl)
  let G := GraphLike.ofFiniteLinks Z ((finite_singleton m).insert 1) a b L hl hv hd
  let q := GraphLike.ofFiniteLinksEdgeEquiv Z ((finite_singleton m).insert 1) a b L hl hv hd
  refine ⟨G, B, A, GraphLike.ofFiniteLinks_finite ..,
    GraphLike.ofFiniteLinks_mem_edgeSet Z _ a b L hl hv hd false,
    GraphLike.ofFiniteLinks_mem_edgeSet Z _ a b L hl hv hd true, ?_, ?_, ?_⟩
  · intro h
    apply Bool.false_ne_true (q.injective (Subtype.ext ?_))
    simpa only [q, GraphLike.ofFiniteLinksEdgeEquiv_coe, L,
      Bool.cond_false, Bool.cond_true] using h
  · exact (hv false).trans (hv true).symm
  · simpa only [union_comm] using hcover

-- The empty family retains all supplied isolated vertices.
example : ∃ G : GraphLike ℝ, G.Finite ∧ G.carrier = {0, 1} ∧
    V(G) = {0, 1} ∧ E(G) = ∅ := by
  let Z : Set ℝ := {0, 1}
  let a : Empty → Z := Empty.elim
  let L : Empty → Set ℝ := Empty.elim
  have hl (i : Empty) : IsPrimitiveLink (L i) (a i).1 (a i).1 := i.elim
  have hv (i : Empty) : L i ∩ Z = {(a i).1, (a i).1} := i.elim
  have hd : Pairwise fun i j ↦ Disjoint (L i \ Z) (L j \ Z) := fun i ↦ i.elim
  let G := GraphLike.ofFiniteLinks Z ((finite_singleton 1).insert 0) a a L hl hv hd
  exact ⟨G, GraphLike.ofFiniteLinks_finite .., by simp [G, Z], rfl,
    by rw [GraphLike.ofFiniteLinks_edgeSet]; exact range_eq_empty L⟩

private def loopVertices : Set (ℕ × Circle) := {p | p.2 = 1}
private noncomputable def loopSource (n : ℕ) : loopVertices := ⟨(n, 1), rfl⟩
private def loopRange (n : ℕ) : Set (ℕ × Circle) := {p | p.1 = n}

private lemma loop_link (n : ℕ) :
    IsPrimitiveLink (loopRange n) (loopSource n).1 (loopSource n).1 := by
  change IsPrimitiveLink (loopRange n) (n, 1) (n, 1)
  have h := circleLink.image (f := fun z ↦ (n, z))
    (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ _ _ h ↦ congrArg Prod.snd h)
  convert h using 1
  ext p
  simp [loopRange, Prod.ext_iff, eq_comm]

private lemma loop_vertices (n : ℕ) :
    loopRange n ∩ loopVertices = {(loopSource n).1, (loopSource n).1} := by
  ext p
  simp [loopRange, loopVertices, loopSource, Prod.ext_iff]

private lemma loop_disjoint :
    Pairwise fun i j ↦ Disjoint (loopRange i \ loopVertices) (loopRange j \ loopVertices) := by
  intro i j hij
  exact disjoint_left.mpr fun _ hi hj ↦ hij (hi.1.symm.trans hj.1)

private lemma loop_vertices_closed :
    IsClosed ((loopVertices ∪ ⋃ i, loopRange i) ↓∩ loopVertices) :=
  (isClosed_singleton.preimage continuous_snd).preimage continuous_subtype_val

private lemma loop_vertices_separated :
    IsTotallySeparated ((loopVertices ∪ ⋃ i, loopRange i) ↓∩ loopVertices) := by
  intro x hx y hy hxy
  change x.1.2 = 1 at hx
  change y.1.2 = 1 at hy
  let U : Set ↥(loopVertices ∪ ⋃ i, loopRange i) := {p | p.1.1 = x.1.1}
  have hU : IsClopen U :=
    ⟨isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val),
      (isOpen_discrete {x.1.1}).preimage (continuous_fst.comp continuous_subtype_val)⟩
  have hne : y.1.1 ≠ x.1.1 := by
    intro he
    exact hxy (Subtype.ext (Prod.ext he.symm (hx.trans hy.symm)))
  exact ⟨U, Uᶜ, hU.2, hU.1.isOpen_compl, rfl, hne,
    fun p _ ↦ em (p ∈ U), disjoint_compl_right⟩

private lemma loop_interior_open (n : ℕ) :
    IsOpen ((loopVertices ∪ ⋃ i, loopRange i) ↓∩ (loopRange n \ loopVertices)) :=
  (((isOpen_discrete {n}).preimage continuous_fst).inter
    (isClosed_singleton.isOpen_compl.preimage continuous_snd)).preimage continuous_subtype_val

-- A genuine infinite edge family: countably many disjoint circles, one vertex per circle.
private noncomputable def infiniteLoops : GraphLike (ℕ × Circle) :=
  GraphLike.ofLinks loopVertices loopSource loopSource loopRange loop_link loop_vertices
    loop_disjoint loop_vertices_closed loop_vertices_separated loop_interior_open

private noncomputable def infiniteLoopEquiv : ℕ ≃ ↥E(infiniteLoops) :=
  GraphLike.ofLinksEdgeEquiv loopVertices loopSource loopSource loopRange loop_link loop_vertices
    loop_disjoint loop_vertices_closed loop_vertices_separated loop_interior_open

example : E(infiniteLoops).Infinite := by
  have : Infinite ↥E(infiniteLoops) :=
    Infinite.of_injective infiniteLoopEquiv infiniteLoopEquiv.injective
  exact Set.infinite_coe_iff.mp this

example (n : ℕ) : loopRange n ∈ E(infiniteLoops) := GraphLike.ofLinks_mem_edgeSet ..

example (n : ℕ) : infiniteLoops.edgeBoundary (loopRange n) = {(n, (1 : Circle))} := by
  exact (loop_vertices n).trans (by simp [loopSource])

-- `splitLeft` and `splitRight` are available at a chosen point, and both union orders simplify.
example {X : Type*} [TopologicalSpace X] {L : Set X} {x y m : X} (hL : IsPrimitiveLink L x y) :
    hL.splitLeft m ∪ hL.splitRight m = L ∧ hL.splitRight m ∪ hL.splitLeft m = L := by
  simp

example : circleLink.splitLeft (-1) ∪ circleLink.splitRight (-1) = univ := by
  simp

example : circleLink.splitLeft (-1) ∩ circleLink.splitRight (-1) = {(1 : Circle), -1} := by
  rw [circleLink.splitLeft_inter_splitRight (mem_univ _)]
  ext z
  simp

example : IsPrimitiveLink (circleLink.splitLeft (-1)) (1 : Circle) (-1) :=
  circleLink.isPrimitiveLink_splitLeft (mem_univ _) circle_neg_one_ne_one

example : IsPrimitiveLink (circleLink.splitRight (-1)) (-1 : Circle) (1 : Circle) :=
  circleLink.isPrimitiveLink_splitRight (mem_univ _) circle_neg_one_ne_one

example : (1 : Circle) ∈ circleLink.splitLeft (-1) ∧
    (-1 : Circle) ∈ circleLink.splitLeft (-1) ∧
    (1 : Circle) ∈ circleLink.splitRight (-1) ∧
    (-1 : Circle) ∈ circleLink.splitRight (-1) :=
  ⟨circleLink.left_mem_splitLeft _, circleLink.mem_splitLeft (mem_univ _),
    circleLink.right_mem_splitRight _, circleLink.mem_splitRight (mem_univ _)⟩

example {X : Type*} [TopologicalSpace X] {L A B : Set X} {x y m : X} [T2Space L]
    (hL : IsPrimitiveLink L x y) (hxy : x ≠ y) (hA : IsPrimitiveLink A x m) (hAL : A ⊆ L)
    (hB : IsPrimitiveLink B m y) (hBL : B ⊆ L) :
    A = hL.splitLeft m ∧ B = hL.splitRight m :=
  ⟨hL.eq_splitLeft hxy hA hAL, hL.eq_splitRight hxy hB hBL⟩

-- An arc contains no loop, and its sublinks are determined by their endpoints.
example {X : Type*} [TopologicalSpace X] {L M : Set X} {x a b : X} [T2Space M]
    (hL : IsPrimitiveLink L x x) (hM : IsPrimitiveLink M a b) (hab : a ≠ b) (hLM : L ⊆ M) :
    False :=
  hL.endpoints_ne_of_subset hM hab hLM rfl

example {X : Type*} [TopologicalSpace X] {M A B : Set X} {a b u v : X} [T2Space M]
    (hM : IsPrimitiveLink M a b) (hab : a ≠ b) (hA : IsPrimitiveLink A u v)
    (hB : IsPrimitiveLink B v u) (hAM : A ⊆ M) (hBM : B ⊆ M) : A = B :=
  hM.eq_of_subset hab hA hB.symm hAM hBM

end GraphLikeAssemblyTests

/-- info: 'GraphLike.ofLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.ofLinks
/-- info: 'GraphLike.ofLinksEdgeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.ofLinksEdgeEquiv
/-- info: 'GraphLike.ofFiniteLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.ofFiniteLinks
/-- info: 'GraphLike.ofLinks_finite_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.ofLinks_finite_iff
