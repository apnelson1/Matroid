module

public import Matroid.Graph.Connected.Basic
public import Matroid.Graph.Walk.Cycle
public import Matroid.ForMathlib.Tactic.ENatToNat
public import Matroid.ForMathlib.Minimal

public import Matroid.Exercises.HamiltonianCycle.Degree
public import Matroid.Exercises.HamiltonianCycle.WList

-- This file contains all relevant lemmas on walks/paths/cycles.
-- All three are included together for convenience.

open WList Set

namespace Graph

variable {α β ι : Type*} {x y z u v a b : α} {e f : β} {G H : Graph α β} {w p q P Q C : WList α β}
         {m n : ℕ}

-- In a simple graph, walks are completely dictated by their vertices
lemma IsWalk.eq_of_vertex_eq [G.Simple] (hp : G.IsWalk p) (hq : G.IsWalk q)
    (heq : p.vertex = q.vertex) : p = q := by
  induction q generalizing p with
  | nil x => cases p <;> simp_all
  | cons x e w IH =>
    induction p with | nil u => simp_all | cons u e w ih =>
    simp_all only [cons_isWalk_iff, and_self, cons_vertex, List.cons.injEq, cons.injEq, and_true,
      true_and, forall_const, List.ne_cons_self, IsEmpty.forall_iff]
    exact hp.unique_edge hq.1

private lemma IsWalk.vertex_mem_of_mem' (hp : G.IsWalk p) (x) (hx : x ∈ p.vertex) : x ∈ V(G) :=
  hp.vertex_mem_of_mem hx

--------- vertexAttach

-- Important def: for any graph G, we have an embedding {p // G.IsWalk p} ↪ List V(G)
def IsWalk.vertexAttach (hp : G.IsWalk p) : List ↑V(G) :=
  p.vertex.attachWith V(G) hp.vertex_mem_of_mem'

lemma IsWalk.vertexAttach_inj [G.Simple] (hp : G.IsWalk p) (hq : G.IsWalk q)
    (heq : hp.vertexAttach = hq.vertexAttach) : p = q := by
  apply congr_arg (List.map Subtype.val) at heq
  replace heq : p.vertex = q.vertex := by
    simp only [vertexAttach, List.map_subtype, List.map_id_fun', id_eq] at heq
    have rw1 := p.vertex.unattach_attachWith (p := V(G)) (H := hp.vertex_mem_of_mem')
    have rw2 := q.vertex.unattach_attachWith (p := V(G)) (H := hq.vertex_mem_of_mem')
    simp [rw1, rw2] at heq
    assumption
  exact hp.eq_of_vertex_eq hq heq

lemma IsPath.vertexAttach_nodup (hp : G.IsPath p) : hp.isWalk.vertexAttach.Nodup :=
  List.nodup_attachWith .. |>.mpr hp.nodup

@[simp]
lemma IsWalk.vertexAttach_length (hp : G.IsWalk p) : hp.vertexAttach.length = p.vertex.length :=
  List.length_attachWith

@[simp]
lemma IsWalk.vertexAttach_map_val (hp : G.IsWalk p) : hp.vertexAttach.map Subtype.val = p.vertex :=
  List.unattach_attachWith

--------- edgeAttach

private lemma IsWalk.edge_mem_of_mem' (hp : G.IsWalk p) (e) (he : e ∈ p.edge) : e ∈ E(G) :=
  hp.edge_mem_of_mem he

-- Important def: for any graph `G`, we can attach the edges of a walk as elements of `E(G)`.
def IsWalk.edgeAttach (hp : G.IsWalk p) : List ↑E(G) :=
  p.edge.attachWith E(G) hp.edge_mem_of_mem'

lemma IsTrail.edgeAttach_nodup (hp : G.IsTrail p) : hp.isWalk.edgeAttach.Nodup :=
  List.nodup_attachWith .. |>.mpr hp.edge_nodup

@[simp]
lemma IsWalk.edgeAttach_length (hp : G.IsWalk p) : hp.edgeAttach.length = p.length :=
  List.length_attachWith.trans p.length_edge

lemma IsWalk.eq_of_edgeAttach_eq_first_eq (hp : G.IsWalk p) (hq : G.IsWalk q)
    (hfirst : p.first = q.first) (heq : hp.edgeAttach = hq.edgeAttach) : p = q := by
  apply congr_arg (List.map Subtype.val) at heq
  have hedge : p.edge = q.edge := by
    simp only [IsWalk.edgeAttach, List.map_subtype, List.map_id_fun', id_eq] at heq
    have rw1 := p.edge.unattach_attachWith (p := E(G)) (H := hp.edge_mem_of_mem')
    have rw2 := q.edge.unattach_attachWith (p := E(G)) (H := hq.edge_mem_of_mem')
    simpa [rw1, rw2] using heq
  exact hp.eq_of_edge_eq_first_eq hq hfirst hedge

lemma IsTrail.length_le_encard (hp : G.IsTrail p) : p.length ≤ E(G).encard := by
  obtain eqTop | neTop := em $ E(G).encard = ⊤
  · simp_all
  simp only [encard_eq_top_iff, not_infinite] at neTop
  rw [← hp.isWalk.edgeAttach_length]
  have : Fintype E(G) := neTop.fintype
  rw [← Set.coe_fintypeCard]
  enat_to_nat
  exact hp.edgeAttach_nodup.length_le_card

lemma IsTrail.length_le_ncard [G.Finite] (hp : G.IsTrail p) : p.length ≤ E(G).ncard := by
  have := hp.length_le_encard
  rw [← G.edgeSet_finite.cast_ncard_eq] at this
  norm_cast at this

lemma IsTrail.edge_encard_eq_length (hp : G.IsTrail p) : E(p).encard = p.length := by
  classical
  rw [← p.length_edge, ← p.edgeSet_finite.cast_ncard_eq]
  enat_to_nat
  change {e | e ∈ p.edge}.ncard = p.edge.length
  rw [← p.edge.toFinset_card_of_nodup hp.edge_nodup, ←p.edge.coe_toFinset, ncard_coe_finset]

lemma IsTrail.edge_ncard_eq_length (hp : G.IsTrail p) : E(p).ncard = p.length := by
  have := hp.edge_encard_eq_length
  rw [← p.edgeSet_finite.cast_ncard_eq] at this
  norm_cast at this

----- PathSet

def PathSet (G : Graph α β) := {p | IsPath G p}

lemma pathSet_finite (G : Graph α β) [G.Finite] : G.PathSet.Finite := by
  let f : G.PathSet →
    {l : List V(G) // l.length ≤ V(G).ncard} × {l : List E(G) // l.length ≤ E(G).ncard} := fun P ↦
    (⟨P.prop.isWalk.vertexAttach, by
      simp only [IsWalk.vertexAttach_length, length_vertex]
      exact P.prop.length_le_ncard⟩,
    ⟨P.prop.isWalk.edgeAttach, by
      rw [IsWalk.edgeAttach_length]
      exact P.prop.isTrail.length_le_ncard⟩)
  have f_inj : Function.Injective f := by
    intro ⟨P, hp⟩ ⟨Q, hq⟩ heq
    simp only [PathSet, mem_ofPred_eq] at hp hq
    obtain ⟨hV, hE⟩ := by
      simpa [Prod.mk.injEq, Subtype.mk.injEq, f, IsWalk.vertexAttach, IsWalk.edgeAttach] using heq
    apply_fun List.unattach at hV hE
    replace hV := List.unattach_attachWith ..|>.symm.trans hV |>.trans (List.unattach_attachWith ..)
    replace hE := List.unattach_attachWith ..|>.symm.trans hE |>.trans (List.unattach_attachWith ..)
    ext1
    exact ext_vertex_edge hV hE
  have : Finite {l : List V(G) // l.length ≤ V(G).ncard} :=
    @List.finite_length_le _ G.vertexSet_finite _
  have : Finite {l : List E(G) // l.length ≤ E(G).ncard} :=
    @List.finite_length_le _ G.edgeSet_finite _
  exact Finite.of_injective f f_inj

lemma pathSet_nonempty (G : Graph α β) (hnonempty : V(G).Nonempty) : G.PathSet.Nonempty := by
  obtain ⟨x, hx⟩ := hnonempty
  use nil x
  simpa [PathSet]

--------- IsLongestPath

def IsLongestPath (G : Graph α β) (p : WList (α) β) :=
  MaximalFor G.IsPath (fun w => w.length) p

@[simp]
lemma IsLongestPath.isPath {p} (h : G.IsLongestPath p) : G.IsPath p := h.1

lemma exists_longest_path [G.Finite] (hNeBot : V(G).Nonempty) :
    ∃ p, G.IsLongestPath p :=
  G.pathSet_finite.exists_maximalFor _ _ (G.pathSet_nonempty hNeBot)

@[simp]
lemma IsLongestPath.reverse (hp : G.IsLongestPath p) : G.IsLongestPath p.reverse := by
  simp only [IsLongestPath, MaximalFor, reverse_isPath_iff, reverse_length]
  exact hp

-- TODO: this already exists in library.
-- by maximality, each neighbour of is on the path
lemma first_neighbors_mem_path (hP : G.IsLongestPath P) (hx : G.Adj P.first x) : x ∈ P := by
  by_contra! hyp
  obtain ⟨e, he⟩ := hx
  have hQ : G.IsPath (cons x e P) := by simp_all [he.symm]
  simpa using hP.le hQ

-- similarly, the same statement but reverse in direction
lemma last_neighbors_mem_path (hP : G.IsLongestPath P) (hx : G.Adj P.last x) :x ∈ P := by
  simpa using first_neighbors_mem_path hP.reverse (by simpa)

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
