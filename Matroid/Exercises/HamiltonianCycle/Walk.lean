import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic
import Matroid.Graph.Connected.Basic
import Matroid.Graph.Walk.Index
import Matroid.Graph.Walk.Cycle
import Matroid.ForMathlib.Tactic.ENatToNat

import Matroid.Exercises.HamiltonianCycle.MinimalMaximal
import Matroid.Exercises.HamiltonianCycle.NeBot
import Matroid.Exercises.HamiltonianCycle.Degree

-- This file contains all relevant lemmas on walks/paths/cycles.
-- All three are included together for convenience.

open WList Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {w p q P Q C : WList α β}

-- In a simple graph, walks are completely dictated by their vertices
lemma IsWalk.eq_of_vertex_eq
    {G : Graph α β} [G.Simple]
    {p q} (hp : G.IsWalk p) (hq : G.IsWalk q) (heq : p.vertex = q.vertex) :
    p = q := by
  induction q generalizing p with
  | nil x =>
      cases p <;> simp_all
  | cons x e w IH =>
      induction p <;> simp_all
      case cons x' e' w' =>
        exact IsLink.unique_edge (G := G) hp hq.1

lemma IsPath.vertex_length_eq_vertexSet_ncard {p} (hp : G.IsPath p) :
    p.vertex.length = V(p).ncard := by
  induction p with simp_all

lemma IsPath.vertex_length_eq_vertexSet_encard {p} (hp : G.IsPath p) :
    p.vertex.length = V(p).encard := by
  have vx_finite : V(p).Finite := p.vertexSet_finite
  rw [← vx_finite.cast_ncard_eq]
  enat_to_nat
  exact hp.vertex_length_eq_vertexSet_ncard

lemma IsCycle.length_eq_tail_vertex_length {C} (hC : G.IsCycle C) :
    C.length = C.tail.vertex.length := by
  induction C with simp_all

lemma IsCycle.length_eq_vertexSet_encard {C : WList α β} (hC : G.IsCycle C ) :
    C.length = V(C).encard := by
  rw [hC.length_eq_tail_vertex_length, ← hC.isClosed.vertexSet_tail]
  have : G.IsPath C.tail := hC.tail_isPath
  exact this.vertex_length_eq_vertexSet_encard

lemma IsCycle.length_eq_vertexSet_ncard {G : Graph α β} {C : WList α β} (hC : G.IsCycle C ) :
    C.length = V(C).ncard := by
  have vx_finite : V(C).Finite := C.vertexSet_finite
  have := hC.length_eq_vertexSet_encard
  rw [←vx_finite.cast_ncard_eq] at this
  enat_to_nat; assumption


private
lemma IsWalk.vertex_mem_of_mem' {p} (hp : G.IsWalk p) (x) (hx : x ∈ p.vertex) : x ∈ V(G) :=
  hp.vertex_mem_of_mem hx

--------- vertex_coe

-- Important def: for any graph G, we have an embedding {p // G.IsWalk p} ↪ List V(G)
def IsWalk.vertex_coe {p} (hp : G.IsWalk p) : List ↑V(G) :=
  p.vertex.attachWith V(G) (vertex_mem_of_mem' hp)

lemma IsWalk.vertex_coe_inj [G.Simple]
    {p q} (hp : G.IsWalk p) (hq : G.IsWalk q) (heq : hp.vertex_coe = hq.vertex_coe) :
    p = q := by
  apply congr_arg (List.map Subtype.val) at heq
  replace heq : p.vertex = q.vertex := by
    simp [vertex_coe] at heq
    have rw1 := p.vertex.unattach_attachWith (p := V(G)) (H := hp.vertex_mem_of_mem')
    have rw2 := q.vertex.unattach_attachWith (p := V(G)) (H := hq.vertex_mem_of_mem')
    simp [rw1, rw2] at heq
    assumption
  exact IsWalk.eq_of_vertex_eq hp hq heq

lemma IsPath.vertex_coe_nodup {p} (hp : G.IsPath p) :
    hp.isWalk.vertex_coe.Nodup := by
  simp [IsWalk.vertex_coe]
  exact hp.nodup

lemma IsWalk.vertex_coe_length_eq {p} (hp : G.IsWalk p) :
    hp.vertex_coe.length = p.vertex.length := by
  simp [vertex_coe]

lemma IsPath.vertex_length_le_encard {G : Graph α β} {p} (hp : G.IsPath p) :
    p.vertex.length ≤ V(G).encard := by
  obtain (eqTop|neTop) := Classical.em $ V(G).encard = ⊤
  · simp_all
  simp at neTop
  rw [←hp.isWalk.vertex_coe_length_eq]
  have hfintype : Fintype V(G) := neTop.fintype
  rw [← Set.coe_fintypeCard]
  enat_to_nat
  exact hp.vertex_coe_nodup.length_le_card

lemma IsPath.vertex_length_le_ncard [G.Finite] {p} (hp : G.IsPath p) :
    p.vertex.length ≤ V(G).ncard := by
  have vx_finite := ‹G.Finite›.vertexSet_finite
  have := hp.vertex_length_le_encard
  rw [←vx_finite.cast_ncard_eq] at this
  enat_to_nat; assumption

-- every path in a graph has at most V(G) - 1 edges
lemma IsPath.length_le_encard
    {p} (hp : G.IsPath p) :
    p.length + 1 ≤ V(G).encard := by
  have := hp.vertex_length_le_encard
  simp at this
  assumption

lemma IsPath.length_le_ncard
    [G.Finite] {p} (hp : G.IsPath p) :
    p.length + 1 ≤ V(G).ncard := by
  have vx_finite := ‹G.Finite›.vertexSet_finite
  have := hp.length_le_encard
  rw [←vx_finite.cast_ncard_eq] at this
  enat_to_nat; assumption

lemma IsTrail.edge_encard_eq_length
    [DecidableEq β] {p} (hp : G.IsTrail p) :
    E(p).encard = p.length := by
  rw [←p.length_edge]
  have edge_nodup : p.edge.Nodup := hp.edge_nodup
  rw [←p.edgeSet_finite.cast_ncard_eq]
  enat_to_nat
  change {e | e ∈ p.edge}.ncard = p.edge.length
  rw [←p.edge.toFinset_card_of_nodup edge_nodup, ←p.edge.coe_toFinset, ncard_coe_finset]

lemma IsTrail.edge_ncard_eq_length
    [DecidableEq β] {p} (hp : G.IsTrail p) :
    E(p).ncard = p.length := by
  have := hp.edge_encard_eq_length
  rw [←p.edgeSet_finite.cast_ncard_eq] at this
  enat_to_nat; assumption

----- PathSet

def PathSet (G : Graph α β) := {p | IsPath G p}

lemma pathSet_finite (G : Graph α β) [G.Simple] [G.Finite] :
    G.PathSet.Finite := by
  -- the number of G-paths IN A SIMPLE GRAPH is directly upper-bounded by the number of
  -- nodup lists with elements in V(G).
  -- Note that in a non-simple graph, we could have infinitely many edges between just two vertices,
  -- hence infinitely many paths.
  have isInG {p} (hp : G.IsPath p) (x) (h : x ∈ p.vertex) : x ∈ V(G) := by
    exact hp.isWalk.vertex_mem_of_mem h
  let inj : G.PathSet → List V(G) := fun ⟨_, hp⟩ ↦ hp.isWalk.vertex_coe
  have inj_injective : Function.Injective inj := by
    intro ⟨p, hp⟩ ⟨q, hq⟩ heq
    simp [inj] at heq ⊢
    exact IsWalk.vertex_coe_inj hp.isWalk hq.isWalk heq
  -- refine ‹G.Finite›.vertexSet_finite.finite_of_encard_le ?_
  have vx_finite : Finite V(G) := vertexSet_finite
  have ⟨n, hn⟩ := G.vertexSet_finite.exists_encard_eq_coe
  have h_subset : range inj ⊆ {l : List V(G) | l.length ≤ n} := by
    intro l hl
    simp [inj] at hl ⊢
    obtain ⟨p, hp, rfl⟩ := hl
    have := hp.vertex_length_le_encard
    rw [hp.isWalk.vertex_coe_length_eq]
    enat_to_nat!; omega
  change Finite G.PathSet
  rw [←Set.finite_range_iff inj_injective]
  refine Set.Finite.subset (List.finite_length_le V(G) n) h_subset

lemma pathSet_nonempty (G : Graph α β) (hNeBot : G.NeBot) :
    G.PathSet.Nonempty := by
  have hnonempty : V(G).Nonempty := by rwa [←NeBot_iff_vertexSet_nonempty]
  obtain ⟨x, hx⟩ := hnonempty
  use nil x
  simpa [PathSet]

--------- IsLongestPath

def IsLongestPath (G : Graph α β) (p : WList (α) β) :=
  MaximalFor G.IsPath (fun w => w.length) p

@[simp]
lemma IsLongestPath.isPath {p} (h : G.IsLongestPath p) : G.IsPath p := h.1

lemma exists_longest_path
    (G : Graph α β) [G.Simple] [G.Finite] (hNeBot : G.NeBot) :
    ∃ p, G.IsLongestPath p :=
  Set.Finite.exists_maximalFor _ _ (G.pathSet_finite) (G.pathSet_nonempty hNeBot)

@[simp]
lemma IsLongestPath.reverse (hp : G.IsLongestPath p) : G.IsLongestPath p.reverse := by
  simp only [IsLongestPath, MaximalFor, reverse_isPath_iff, reverse_length]
  exact hp

-- TODO: this already exists in library.
-- by maximality, each neighbour of is on the path
lemma first_neighbors_mem_path
    (G : Graph α β) [G.Simple]
    {P : WList (α) β} (hP : G.IsLongestPath P)
    (x : α) (hx : G.Adj P.first x) :
    x ∈ P := by
  -- suppose not.
  -- then, we will try constructing a longer path by prepending this neighbour
  by_contra! hyp
  obtain ⟨e, he⟩ := hx
  generalize Q_def : cons x e P = Q
  symm at Q_def
  symm at he
  have hQ : G.IsPath Q := by simp_all
  have hQ_len : Q.length = P.length + 1 := by simp_all
  have hQ_path : Q ∈ G.PathSet := hQ
  have maximality := maximalFor_is_upper_bound _ hP _ hQ_path
  linarith

-- similarly, the same statement but reverse in direction
lemma last_neighbors_mem_path
    (G : Graph α β) [G.Simple]
    {P : WList (α) β} (hP : G.IsLongestPath P)
    (x : α) (hx : G.Adj P.last x) :
    x ∈ P := by
  -- just reverse `first_neighbors_mem_path`
  set P' := P.reverse with P'_def
  have hx' : G.Adj P'.first x := by simp_all only [reverse_first]
  have hP' : G.IsLongestPath P' := hP.reverse
  have := first_neighbors_mem_path G hP' x hx'
  simp_all only [mem_reverse]

------- Lemmas on cycles in simple graphs?

-- cycles in simple graphs are nontrivial
lemma IsCycle.nontrivial_of_simple
    [G.Simple]
    {P} (hP : G.IsCycle P) : P.Nontrivial := by
  obtain (h|h) := hP.loop_or_nontrivial
  swap; assumption
  exfalso
  obtain ⟨x,e,rfl⟩ := h
  replace hP := hP.isTrail
  rw [cons_isTrail_iff] at hP
  apply hP.2.1.ne; simp

-- cycles in simple graphs are of length at least 3
lemma IsCycle.three_le_length_of_simple
    [G.Simple]
    {P} (hP : G.IsCycle P) :
    3 ≤ P.length := by
  by_contra! hyp_contra
  replace hyp_contra : P.length = 2 := by
    suffices 2 ≤ P.length by linarith
    have P_nontrivial := hP.nontrivial_of_simple
    linarith [P_nontrivial.one_lt_length]
  rw [hP.length_eq_two_iff] at hyp_contra
  obtain ⟨x,y,e,f,_, hne, rfl⟩ := hyp_contra
  have h_e_link : G.IsLink e x y := by
    replace hP := hP.isTrail
    simp_all
  have h_f_link : G.IsLink f y x := by
    replace hP := hP.isTrail
    simp_all
  symm at h_f_link
  apply hne
  have := IsLink.unique_edge h_e_link h_f_link
  assumption


-------- prefixUntilVertex / suffixFromVertex lemmas

lemma IsPath.suffixFromVertex_idempotent
    [DecidableEq α]
    {p} (hp : G.IsPath p) (x) :
    (p.suffixFromVertex x).suffixFromVertex x = p.suffixFromVertex x := by
  induction p generalizing x with
  | nil u =>
    simp_all [suffixFromVertex]
  | cons x' e p IH =>
      simp_all
      obtain (rfl|hne) := Classical.em (x = x')
      · simp_all [suffixFromVertex]
      replace hne : ¬ x' = x := fun a ↦ hne a.symm
      simp_all [suffixFromVertex]

lemma IsPath.dInc_suffixFromVertex
    [DecidableEq α]
    {p} (hp : G.IsPath p) (h : p.DInc e x y) :
    p.suffixFromVertex x = cons x e (p.suffixFromVertex y) := by
  induction p generalizing e x y with
  | nil =>
      simp_all
  | cons x' e' p IH =>
      rw [dInc_cons_iff] at h
      have x'_nin : x' ∉ p := by simp at hp; tauto
      obtain (h|h) := h
      · obtain ⟨rfl, rfl, rfl⟩ := h
        have x'_first : x' = (cons x' e' p).first := by simp
        conv => left; right; rw [x'_first]
        rw [WList.suffixFromVertex_from_first_eq (cons x' e' p)]
        rw [WList.suffixFromVertex_from_second_eq]
        intro rfl
        have := p.first_mem
        contradiction
      specialize IH hp.of_cons h
      have x'_ne_y : ¬ x' = y := by
        intro rfl
        have := h.right_mem
        contradiction
      have x'_ne_x : ¬ x' = x := by
        intro rfl
        have := h.left_mem
        contradiction
      simp_all [suffixFromVertex]

lemma IsPath.prefixUntilVertex_dInc_suffixFromVertex
    [DecidableEq α]
    {p} (hp : G.IsPath p) (h : p.DInc e x y) :
    (p.prefixUntilVertex x) ++ cons x e (p.suffixFromVertex y) = p := by
  rw [← hp.dInc_suffixFromVertex h]
  exact prefixUntilVertex_append_suffixFromVertex p x

lemma IsPath.first_in_suffixFromVertex_iff
    [DecidableEq α]
    {p} (hp : G.IsPath p) {x} (hx : x ∈ p) :
    p.first ∈ p.suffixFromVertex x ↔ p.first = x := by
  refine ⟨?_, ?_⟩
  swap
  · rintro rfl
    simp [WList.suffixFromVertex_from_first_eq p]
  induction p generalizing x with simp_all
  | cons u e w IH =>
      obtain (rfl|hx) := hx
      · simp_all [suffixFromVertex]
      obtain (h|h) := WList.suffixFromVertex_cons_or u e w x
      · obtain ⟨rfl, h⟩ := h
        tauto
      rw [h.2]
      intro bad
      exfalso
      apply hp.2.2
      exact (w.suffixFromVertex_isSuffix x).mem bad
