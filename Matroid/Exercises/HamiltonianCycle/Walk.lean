import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic
import Matroid.Graph.Connected.Basic
import Matroid.Graph.Walk.Cycle
import Matroid.ForMathlib.Tactic.ENatToNat

import Matroid.Exercises.HamiltonianCycle.MinimalMaximal
import Matroid.Exercises.HamiltonianCycle.Degree
import Matroid.Exercises.HamiltonianCycle.WList

-- This file contains all relevant lemmas on walks/paths/cycles.
-- All three are included together for convenience.

open WList Set

namespace Graph

variable {α β ι : Type*} {x y z u v a b : α} {e f : β} {G H : Graph α β} {w p q P Q C : WList α β}
         {m n : ℕ}

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

lemma pathSet_nonempty (G : Graph α β) (hnonempty : V(G).Nonempty) : G.PathSet.Nonempty := by
  obtain ⟨x, hx⟩ := hnonempty
  use nil x
  simpa [PathSet]

--------- IsLongestPath

def IsLongestPath (G : Graph α β) (p : WList (α) β) :=
  MaximalFor G.IsPath (fun w => w.length) p

@[simp]
lemma IsLongestPath.isPath {p} (h : G.IsLongestPath p) : G.IsPath p := h.1

lemma exists_longest_path [G.Simple] [G.Finite] (hNeBot : V(G).Nonempty) :
    ∃ p, G.IsLongestPath p :=
  G.pathSet_finite.exists_maximalFor _ _ (G.pathSet_nonempty hNeBot)

@[simp]
lemma IsLongestPath.reverse (hp : G.IsLongestPath p) : G.IsLongestPath p.reverse := by
  simp only [IsLongestPath, MaximalFor, reverse_isPath_iff, reverse_length]
  exact hp

-- TODO: this already exists in library.
-- by maximality, each neighbour of is on the path
lemma first_neighbors_mem_path [G.Simple] (hP : G.IsLongestPath P) (hx : G.Adj P.first x) :
    x ∈ P := by
  -- suppose not.
  -- then, we will try constructing a longer path by prepending this neighbour
  by_contra! hyp
  obtain ⟨e, he⟩ := hx
  have hQ : G.IsPath (cons x e P) := by simp_all [he.symm]
  have hQ_len : (cons x e P).length = P.length + 1 := by simp_all
  have maximality := maximalFor_is_upper_bound _ hP _ hQ
  linarith

-- similarly, the same statement but reverse in direction
lemma last_neighbors_mem_path [G.Simple] (hP : G.IsLongestPath P) (hx : G.Adj P.last x) :x ∈ P := by
  -- just reverse `first_neighbors_mem_path`
  set P' := P.reverse with P'_def
  have hx' : G.Adj P'.first x := by simp_all only [reverse_first]
  have hP' : G.IsLongestPath P' := hP.reverse
  have := first_neighbors_mem_path hP' hx'
  simp_all only [mem_reverse]

------- Lemmas on cycles in simple graphs?

-- cycles in simple graphs are nontrivial
lemma IsCycle.nontrivial_of_simple [G.Simple] (hP : G.IsCycle P) : P.Nontrivial := by
  apply hP.loop_or_nontrivial.elim (fun h ↦ ?_) id
  exfalso
  obtain ⟨x, e, rfl⟩ := h
  simpa using cons_isTrail_iff.1 hP.isTrail

-- cycles in simple graphs are of length at least 3
lemma IsCycle.three_le_length_of_simple [G.Simple] (hP : G.IsCycle P) : 3 ≤ P.length := by
  by_contra! hyp_contra
  replace hyp_contra : P.length = 2 := by
    suffices 2 ≤ P.length by linarith
    have P_nontrivial := hP.nontrivial_of_simple
    linarith [P_nontrivial.one_lt_length]
  rw [hP.length_eq_two_iff] at hyp_contra
  obtain ⟨x, y, e, f,_ , hne, rfl⟩ := hyp_contra
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

lemma Prefix_Suffix_int [DecidableEq α] (hP : G.IsPath P) (hp : b ∈ P.prefixUntilVertex x)
    (hs : b ∈ P.suffixFromVertex x) (hx : x ∈ P) : x = b := by
  rw [← prefixUntilVertex_append_suffixFromVertex P x] at hP
  have hPf : x = (P.suffixFromVertex x).first := (suffixFromVertex_first hx).symm
  nth_rw 1 [(prefixUntilVertex_last hx).symm] at hPf
  have hint : b ∈ V(P.prefixUntilVertex x) ∩ V(P.suffixFromVertex x) := mem_inter hp hs
  rw [hP.inter_eq_singleton_of_append hPf] at hint
  simp only [prefixUntilVertex_last hx, mem_singleton_iff] at hint
  exact hint.symm


--- ROTATE

lemma IsCycle.rotate_one (hC : G.IsCycle C) :
    ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) :=
  hC.nonempty.rotate_one

lemma IsCycle.idxOf_rotate_one [DecidableEq α] (hC : G.IsCycle C) (h1 : C.first ≠ a) (ha : a ∈ C) :
    (C.rotate 1).idxOf a + 1 = C.idxOf a :=
  hC.nonempty.idxOf_rotate_one h1 ha

lemma IsCycle.idxOf_rotate_first [DecidableEq α] (_ : G.IsCycle C) (hlt : n < C.idxOf a) :
    (C.rotate n).first ≠ a :=
  WList.idxOf_rotate_first_ne_of_lt hlt

lemma IsCycle.idxOf_rotate_n_le [DecidableEq α] (_ : G.IsCycle C) (ha : a ∈ C)
    (hle : n ≤ C.idxOf a) : (C.rotate n).idxOf a + n = C.idxOf a :=
  C.idxOf_rotate_n_of_n_le_idxOf ha hle

lemma IsCycle.idxOf_rotate_one_first' [DecidableEq α] (hC : G.IsCycle C) :
    (C.rotate 1).idxOf C.first + 1 = C.length := by
  obtain ⟨e, hrC⟩ := hC.rotate_one
  rw [hrC, idxOf_concat_of_mem, hC.isClosed.eq, ← tail_last, idxOf_last _ hC.nodup, tail_length,
    Nat.sub_add_cancel hC.nonempty.length_pos]
  rw [hC.isClosed.mem_tail_iff]
  exact first_mem

lemma IsCycle.idxOf_rotate_one_first [DecidableEq α] (hC : G.IsCycle C) (h1 : C.first = a)
    (ha : a ∈ C) : (C.rotate 1).idxOf a + 1 = C.length := by
  obtain ⟨e, hrC⟩ := hC.rotate_one
  have hft := h1 ▸ hC.isClosed.eq
  rw [hrC, idxOf_concat_of_mem (hC.isClosed.mem_tail_iff.2 ha), hft, (tail_last C).symm,
    idxOf_last C.tail (hC.nodup), tail_length]
  have := hC.nonempty.length_pos
  omega

lemma IsCycle.idxOf_rotate_untilfirst [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) :
    (C.rotate (C.idxOf a + 1)).idxOf a + 1 = C.length := by
  rw [← rotate_rotate C (C.idxOf a) 1, (hC.rotate (C.idxOf a)).idxOf_rotate_one_first
    (rotate_idxOf_first ha) (hC.isClosed.mem_rotate.mpr ha), length_rotate]

--@[simp]
lemma IsCycle.idxOf_rotate_idxOf [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) :
    (C.rotate (C.idxOf a)).idxOf a = 0 := by
  simpa using hC.idxOf_rotate_n_le ha le_rfl

lemma IsCycle.idxOf_rotate_n [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) (hn : n < C.length)
    (hle : C.idxOf a < n) : (C.rotate n).idxOf a + n = C.length + C.idxOf a := by
  obtain ⟨x, rfl⟩ | hnt := exists_eq_nil_or_nonempty C
  · simp_all
  induction n with | zero => simp_all | succ n hi =>
  obtain han | hu := eq_or_ne (C.idxOf a) n
  · rw [← han]
    have hle' : C.idxOf a < C.length := by
      rw [han]
      exact Nat.lt_of_succ_lt hn
    have := hC.idxOf_rotate_untilfirst ha
    linarith
  rw [← C.rotate_rotate n 1]
  have hg : n < C.length := Nat.lt_of_succ_lt hn
  have hii := hi hg (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hle) hu)
  have hnf : (C.rotate n).first ≠ a := by
    by_contra hc
    have hia : (C.rotate n).idxOf a = 0 := by
      rw [← hc]
      exact idxOf_first (C.rotate n)
    rw [hia, zero_add] at hii
    rw [hii] at hg
    linarith
  have ha' : a ∈ C.rotate n := (IsClosed.mem_rotate (hC.isClosed)).mpr ha
  have hf := ((rotate_nonempty_iff n).mpr hnt).idxOf_rotate_one hnf ha'
  linarith

lemma IsTrail.idxOf_Adj [DecidableEq α] (hw : G.IsTrail w) (ha : a ∈ w) (hb : b ∈ w)
    (he : w.idxOf b = w.idxOf a + 1) : G.Adj a b := by
  induction w with | nil w => simp_all | cons u e w ih =>
  simp_all only [cons_isTrail_iff, mem_cons_iff, forall_const]
  obtain rfl | hu := eq_or_ne a u
  · simp_all only [true_or, idxOf_cons_self, zero_add]
    obtain rfl | hbb := eq_or_ne a b
    · simp at he
    simp [idxOf_cons a e w, hbb] at he
    simp [hbb.symm] at hb
    have : b = w.first := by
      have h1 := w.get_idxOf hb
      rw[he ] at h1
      --have : w.first ∈ w := by exact first_mem
      have h2 := w.get_idxOf first_mem
      rw [idxOf_first w, h1] at h2
      exact h2
    rw [this]
    use e
    exact hw.2.1
  simp only [hu, false_or] at ha
  obtain rfl | hau := eq_or_ne b u
  simp_all
  simp [hau] at hb
  simp [idxOf_cons_ne hu.symm, idxOf_cons_ne hau.symm ] at he
  exact ih ha hb he

lemma IsCycle.idxOf_Adj [DecidableEq α] {a b : α} {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) (hb : b ∈ C) (he : C.idxOf b = C.idxOf a + 1) : G.Adj a b :=
  (hC.toIsTrail).idxOf_Adj ha hb he

-- lemma IsCycle.idxOf_Adj_first [DecidableEq α] {a b : α} {C : WList α β} (hC : G.IsCycle C)
--     (hab : a ≠ b)
--     (ha : C.idxOf a = 0 ) (hb : C.idxOf b = C.length - 1): G.Adj a b := by

lemma IsCycle.idxOf_Adj_first [DecidableEq α] (hC : G.IsCycle C) (hab : a ≠ b) (ha : C.idxOf a = 0)
    (hb : C.idxOf b = C.length - 1) : G.Adj a b := by
  have haC : a ∈ C := by
    have hlea : C.idxOf a ≤ C.length := by
      rw [ha]
      exact Nat.zero_le C.length
    exact idxOf_le_length_iff_mem.mp hlea
  have hbC : b ∈ C := by
    have hle : C.idxOf b ≤ C.length := by
      rw [hb]
      omega
    exact idxOf_le_length_iff_mem.mp hle
  obtain h0 | hnt := DecidableNonempty C
  · simp only [WList.not_nonempty_iff] at h0
    rw [length_eq_zero.2 h0, zero_tsub, ← ha] at hb
    exact hab (C.idxOf_inj_of_left_mem haC hb.symm) |>.elim
  obtain h1 | hle := le_or_gt C.length 1
  · rw [h1.antisymm (one_le_length_iff.mpr hnt), tsub_self, ← ha] at hb
    exact hab (C.idxOf_inj_of_left_mem haC hb.symm) |>.elim
  have hn : C.idxOf b < C.length := by
    rw [hb]
    omega
  have hab : C.idxOf a < C.idxOf b := by
    rw [ha, hb]
    exact Nat.zero_lt_sub_of_lt hle
  have := hC.idxOf_rotate_idxOf hbC
  have hf := hC.idxOf_rotate_n haC hn hab
  rw [ha, ←this] at hf
  nth_rw 2 [hb] at hf
  have hlast : (C.rotate (C.idxOf b)).idxOf a  = (C.rotate (C.idxOf b)).idxOf b + 1 := by omega
  exact (idxOf_Adj (rotate hC (C.idxOf b)) (hC.isClosed.mem_rotate.2 hbC)
    (hC.isClosed.mem_rotate.2 haC) hlast).symm

lemma IsCycle.idxOf_rotate [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) (hn : n < C.length) :
    ((C.rotate n).idxOf a + n) % C.length = C.idxOf a := by
  obtain ⟨x, rfl⟩ | hne := exists_eq_nil_or_nonempty C
  · simp_all
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  · rw [hC.idxOf_rotate_n_le ha hle]
    exact Nat.mod_eq_of_lt (hC.isClosed.idxOf_lt_length ha hne)
  rw [hC.idxOf_rotate_n ha hn hlt]
  simp only [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (hC.isClosed.idxOf_lt_length ha hne)

lemma IsCycle.idxOf_Adj_rotate [DecidableEq α] (hC : G.IsCycle C) (ha : a ∈ C) (hb : b ∈ C)
    (hn : n < C.length) : C.idxOf b = C.idxOf a + 1 ∨ (C.idxOf b = 0 ∧ C.idxOf a = C.length - 1)
    ↔ (C.rotate n).idxOf b = (C.rotate n).idxOf a + 1 ∨
    ((C.rotate n).idxOf b = 0 ∧ (C.rotate n).idxOf a = C.length - 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  have := hC.idxOf_rotate_n_le ha hle
  · obtain hleb | hltb := le_or_gt n (C.idxOf b)
    · have := hC.idxOf_rotate_n_le hb hleb
      omega
    have := hC.idxOf_rotate_n hb hn hltb
    omega
  obtain hleb | hltb := le_or_gt n (C.idxOf b)
  · have := hC.idxOf_rotate_n ha hn hlt
    have := hC.idxOf_rotate_n_le hb hleb
    omega
  have := hC.idxOf_rotate_n ha hn hlt
  have := hC.idxOf_rotate_n hb hn hltb
  omega

  have hne := hC.nonempty
  have hh : (C.rotate n).idxOf b + n = (C.rotate n).idxOf a + n + 1
      ∨ (C.rotate n).idxOf b + n = n ∧ (C.rotate n).idxOf a + n = C.length - 1 + n := by
    omega
  obtain hle | hlt := le_or_gt n (C.idxOf a)
  rw [hC.idxOf_rotate_n_le ha hle] at hh
  · obtain hleb | hltb := le_or_gt n (C.idxOf b)
    · rw [hC.idxOf_rotate_n_le hb hleb] at hh
      obtain hgood | hf := hh
      · omega
      have := (hC.isClosed).idxOf_lt_length ha hne
      rw[hf.2] at this
      by_contra
      omega
    rw [hC.idxOf_rotate_n hb hn hltb] at hh
    have := (hC.isClosed).idxOf_lt_length ha hne
    have : C.length ≤ C.length + C.idxOf b := Nat.le_add_right C.length (C.idxOf b)
    obtain haa | haaa : C.length + C.idxOf b = C.length ∨ C.length + C.idxOf b = C.length + 1 := by
      omega
    · simp only [Nat.add_eq_left] at haa
      rw [haa] at hh
      omega
    simp only [Nat.add_left_cancel_iff] at haaa
    simp only [haaa, Nat.add_right_cancel_iff] at hh
    omega
  obtain hleb | hltb := le_or_gt n (C.idxOf b)
  rw [hC.idxOf_rotate_n_le hb hleb] at hh
  · rw [hC.idxOf_rotate_n ha hn hlt] at hh
    have := (hC.isClosed).idxOf_lt_length hb hne
    omega
  rw [hC.idxOf_rotate_n ha hn hlt, hC.idxOf_rotate_n hb hn hltb] at hh
  omega

-- lemma rotate_pre_suf [DecidableEq α] (w : WList α β) {a : ℕ} :
--     (w.rotate a).suffixFromVertex (w.get a) = w.suffixFromVertex (w.get a) := by sorry

-- lemma IsCycle.rotate_pre_suff [DecidableEq α] {C : WList α β} (hC : G.IsCycle C) {a : ℕ }
--   (hnt : C.Nonempty) (hla : a ≤ C.length) (ha : 1 ≤ a ) :
--   (C.rotate a).prefixUntilVertex (C.last ) = C.suffixFromVertex (C.get a) := by
-- induction a with
-- | zero =>
-- simp
-- by_contra
-- exact Nat.not_succ_le_zero 0 ha
-- | succ n IH =>
-- have hwnt : (C.rotate n).Nonempty := by sorry
-- rw[←rotate_rotate C n 1] --SuffixFromVertex_get C hnt hla hw ]
-- -- obtain ⟨e, hC ⟩ := rotate_one hwnt
-- -- rw[hC]
-- -- set w' := (w.rotate n) with h_w'
-- -- have : ((w.rotate n).tail.concat e (w.rotate n).tail.first).prefixUntilVertex w.last
-- --     = ((w.rotate n).prefixUntilVertex w.last).tail := by
-- --   rw[←h_w']
-- --   have hlin : w.last ∈ w'.tail := by sorry
-- --   rw[prefixUntilVertex_concat_of_exists w'.tail hlin, prefixUntilVertex_tail w']
-- --   rw[h_w']
-- --   sorry
-- --   sorry
-- --   exact hwnd
-- sorry
