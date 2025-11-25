import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

import Qq
-- TODO: remember to remove this Loogle import at the end of the project
import Loogle.Find

import Matroid.ForMathlib.Tactic.ENatToNat
import Matroid.Graph.Connected.Basic
import Matroid.Graph.Connected.Component
import Matroid.Graph.Connected.Separating
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Basic
import Matroid.Graph.Independent
import Matroid.Graph.Subgraph.Basic
import Matroid.Graph.Tree
import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Walk.Path
import Matroid.Graph.WList.Defs
import Matroid.Graph.WList.Cycle

open Qq Lean Meta Elab Tactic
open WList Set

section NonGraphThings

variable {α β : Type*} {P₀ P₁ : WList α β} {e f : β}

lemma finite_of_ncard_nonzero {s : Set α} (h : s.ncard ≠ 0) : s.Finite := by
  by_contra hyp
  replace hyp : s.Infinite := hyp
  apply h
  exact Infinite.ncard hyp

lemma finite_of_ncard_positive {s : Set α} (h : 0 < s.ncard) : s.Finite := by
  apply finite_of_ncard_nonzero ; linarith

lemma minimal_is_lower_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Minimal P x) :
    ∀ y, P y → x ≤ y := by
  intro y hy
  simp [Minimal] at h
  obtain (_|_) := le_total x y
  · assumption
  · tauto

lemma minimalFor_is_lower_bound
    {ι} [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι} (h : MinimalFor P f i) :
    ∀ j, P j → f i ≤ f j := by
  intro j hj
  simp [MinimalFor] at h
  obtain (_|_) := le_total (f i) (f j)
  · assumption
  · tauto

lemma maximal_is_upper_bound [LinearOrder α] {P : α → Prop} {x : α} (h : Maximal P x) :
    ∀ y, P y → y ≤ x := by
  intro y hy
  simp [Maximal] at h
  obtain (_|_) := le_total y x
  · assumption
  · tauto

lemma maximalFor_is_upper_bound
    {ι} [LinearOrder α] {P : ι → Prop} (f : ι → α) {i : ι} (h : MaximalFor P f i) :
    ∀ j, P j → f j ≤ f i := by
  intro j hj
  simp [MaximalFor] at h
  obtain (_|_) := le_total (f j) (f i)
  · assumption
  · tauto

end NonGraphThings

namespace WList

variable {α β : Type*} {P₀ P₁ w p : WList α β} {x y u v : α} {e f : β}

lemma suffixFromVertex_from_first_eq
    [DecidableEq α]
    (w : WList α β) :
    w.suffixFromVertex w.first = w := by
  induction w with (simp_all [suffixFromVertex])

lemma suffixFromVertex_from_second_eq
    [DecidableEq α]
    (w : WList α β) (e) (hx : x ≠ w.first) :
    (cons x e w).suffixFromVertex w.first = w := by
  simp_all [suffixFromVertex]
  exact suffixFromVertex_from_first_eq w

lemma suffixFromVertex_nil
    [DecidableEq α]
    {u x : α} : (nil (β := β) u).suffixFromVertex x = nil u := by
  simp [suffixFromVertex]

lemma suffixFromVertex_cons_or
    [DecidableEq α]
    (u e) (w : WList α β) (x) :
    (u = x ∧ (cons u e w).suffixFromVertex x = cons u e w) ∨
    (u ≠ x ∧ (cons u e w).suffixFromVertex x = w.suffixFromVertex x) := by
  obtain (h|h) := Classical.em (u = x) <;>
    simp_all [suffixFromVertex]

lemma IsSublist.mem_edge
    {w₁ w₂ : WList α β}
    (h : w₁.IsSublist w₂) (he : e ∈ w₁.edge) :
    e ∈ w₂.edge := by
  have := h.edgeSet_subset
  exact this he

lemma IsSuffix.mem_edge
    {w₁ w₂ : WList α β}
    (h : w₁.IsSuffix w₂) (he : e ∈ w₁.edge) :
    e ∈ w₂.edge := by
  refine IsSublist.mem_edge ?_ he
  exact h.isSublist

lemma IsPrefix.mem_edge
    {w₁ w₂ : WList α β}
    (h : w₁.IsPrefix w₂) (he : e ∈ w₁.edge) :
    e ∈ w₂.edge := by
  refine IsSublist.mem_edge ?_ he
  exact h.isSublist

-- in a WList with no repeated edges, each edge is part of exactly one DInc triplet
lemma dInc_iff_eq_of_dInc_of_edge_nodup {w : WList α β} (hw : w.edge.Nodup) (he : w.DInc e u v) :
    w.DInc e x y ↔ x = u ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil => simp_all
  | cons z f w IH =>
    simp at hw h he
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨rfl, he, rfl⟩ | he := he; try tauto
      exfalso; apply hw.1; apply he.edge_mem
    obtain ⟨rfl, rfl, rfl⟩ | he := he
    · exfalso; apply hw.1; apply h.edge_mem
    apply IH <;> first | assumption | tauto

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_left
    {w : WList α β} (hw : w.vertex.Nodup) (hu : w.DInc e u v) :
    w.DInc f u y ↔ f = e ∧ y = v := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; assumption⟩
  induction w with
  | nil _ => simp_all
  | cons u' f' w IH =>
    simp_all
    obtain ⟨rfl, rfl, rfl⟩ | h := h
    · obtain ⟨hu, rfl, rfl⟩ | hu := hu; try tauto
      exfalso; apply hw.1; apply hu.left_mem
    obtain ⟨rfl, rfl, rfl⟩ | hu := hu
    · exfalso; apply hw.1; apply h.left_mem
    apply IH <;> assumption

lemma dInc_iff_eq_of_dInc_of_vertex_nodup_right
    {w : WList α β} (hw : w.vertex.Nodup) (hv : w.DInc e u v) :
    w.DInc f x v ↔ f = e ∧ x = u := by
  generalize hw_def' : w.reverse = w'
  have hw' : w'.vertex.Nodup := by rwa [← hw_def', reverse_vertex, List.nodup_reverse]
  have hv' : w'.DInc e v u := by simpa [← hw_def']
  have := dInc_iff_eq_of_dInc_of_vertex_nodup_left (f := f) (v := u) (y := x) hw' hv'
  rwa [← hw_def', dInc_reverse_iff] at this

lemma exists_left_edge
    (w : WList α β) {y : α} (hyw : y ∈ w) (hy : y ≠ w.first) :
    ∃ e x, w.DInc e x y := by
  induction w generalizing y with simp_all
  | cons u e w IH =>
    obtain (hne|heq) := Classical.decEq _ y w.first
    · obtain ⟨f, x, h⟩ := IH hyw hne
      use f, x
      right; assumption
    use e, u
    left; tauto

lemma exists_right_edge
    (w : WList α β) {x : α} (hxw : x ∈ w) (hx : x ≠ w.last) :
    ∃ e y, w.DInc e x y := by
  generalize hw'_def : w.reverse = w'; symm at hw'_def
  have hx' : x ≠ w'.first := by simp_all
  have hxw' : x ∈ w' := by simp_all
  obtain ⟨e, y, h⟩ := exists_left_edge w' hxw' hx'
  use e, y
  simp_all


lemma Cycle_conc_index
    [DecidableEq α]
    (huv : v ≠ u) {P : WList α β} (hCP : v ∈ cons u e (P.concat f u))
    : v ∈ P ∧ (cons u e (P.concat f u)).idxOf v = P.idxOf v + 1 := by
  simp at hCP
  obtain (rfl | h2 | rfl) := hCP
  · exact False.elim (huv rfl)
  · refine ⟨ h2, ?_ ⟩
    rw [idxOf_cons_ne huv.symm e (P.concat f u) ]
    simp
    rwa [idxOf_concat_ne P f ]
  · exact False.elim (huv rfl)


lemma prefixUntilVertex_index [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w)
    (hle : w.idxOf y ≤ w.idxOf x ) :
    w.idxOf y = (w.prefixUntilVertex x).idxOf y := by
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  simp at hx
  obtain rfl | hu := eq_or_ne x u
  · obtain rfl | hxy := eq_or_ne x y
    simp
    have h1 : (cons x e w).first = x := by exact rfl
    rw [←prefixUntilVertex_first (cons x e w) x] at h1
    have h := idxOf_first ((cons x e w).prefixUntilVertex x)
    nth_rw 3 [←h1]
    exact id (Eq.symm h)
    · simp at hle
      rw [hle]
      rw [idxOf_cons_ne hxy] at hle
      by_contra!
      have hcon : 0 ≤ w.idxOf y := by exact Nat.zero_le (w.idxOf y)
      rw [←hle ] at hcon
      linarith
  simp_all [prefixUntilVertex, hu.symm, idxOf_cons_ne hu.symm]
  obtain rfl | huy := eq_or_ne y u
  · simp
  simp_all [ idxOf_cons_ne huy.symm]

lemma prefixUntilVertex_Nil [DecidableEq α] (w : WList α β) (x : α) :
    Nil ((cons x e w).prefixUntilVertex x) := by
  refine length_eq_zero.mp ?_
  rw [prefixUntilVertex_length (w := cons x e w)]
  exact idxOf_cons_self x e w
  simp

lemma prefixUntilVertex_nil [DecidableEq α] (w : WList α β) (x : α) :
    (cons x e w).prefixUntilVertex x = .nil x := by
  refine Nil.eq_nil_of_mem (prefixUntilVertex_Nil w x) ?_
  have h1 : x = ((cons x e w).prefixUntilVertex x).first := by
    rw [prefixUntilVertex_first (cons x e w) x]
    exact rfl
  have h2 : ((cons x e w).prefixUntilVertex x).first ∈ (cons x e w).prefixUntilVertex x := by
    exact first_mem
  rwa [←h1 ] at h2

lemma prefixUntilVertex_index_iff [DecidableEq α] (w : WList α β) (x : α) (hx : x ∈ w) (hy : y ∈ w)
    : y ∈ (w.prefixUntilVertex x) ↔  w.idxOf y ≤ w.idxOf x := by
refine ⟨ ?_, ?_ ⟩
· intro hyP
  induction w with | nil => simp_all [prefixUntilVertex] | cons u e w ih =>
  obtain rfl | hu := eq_or_ne x u
  · simp
    rw [prefixUntilVertex_nil w x] at hyP
    simp at hyP
    rw[hyP]
    simp
  simp [hu] at hx
  obtain rfl | huy := eq_or_ne y u
  · simp
  simp [huy] at hy
  simp [idxOf_cons u e w, huy.symm, hu.symm]
  rw [prefixUntilVertex_cons_of_ne w hu.symm] at hyP
  simp only [mem_cons_iff, huy, false_or] at hyP
  exact ih hx hy hyP
intro hle
by_contra hc
have h1 := idxOf_notMem hc
rw [prefixUntilVertex_length hx, ←prefixUntilVertex_index w x hx hle] at h1
linarith

lemma idx_Of_tail [DecidableEq α] {w : WList α β} {a : α} (hw : w.Nonempty) (haf : w.first ≠ a)
    (ha : a ∈ w) :
    (w.tail).idxOf a + 1 = w.idxOf a := by
  induction w with
  | nil w =>
  simp
  rw [nil_first] at haf
  exact haf (mem_nil_iff.1 ha).symm
  | cons u e w ih =>
  simp
  obtain rfl | hu := eq_or_ne a u
  simp
  exact haf rfl
  simp [hu.symm]

lemma idx_Of_dropLast [DecidableEq α] {w : WList α β} {a : α} (hw : w.Nonempty) (ha : a ∈ w) :
    (w.dropLast).idxOf a = w.idxOf a := by
  induction w with
  | nil w => rfl
  | cons u e w ih =>
  obtain he | hwN := exists_eq_nil_or_nonempty w
  obtain ⟨x, hx ⟩ := he
  rw [hx]
  obtain rfl | hu := eq_or_ne a u
  simp
  simp [hu.symm]
  simp [hu, hx] at ha
  exact id (Eq.symm ha)
  rw [hwN.dropLast_cons]
  obtain rfl | hu := eq_or_ne a u
  simp_all
  simp [hu.symm ]
  simp_all

end WList

namespace Graph

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}

/- Theorem 10.1.1 (Dirac 1952)
Every graph with n >= 3 vertices and minimum degree at least n/2 has a Hamiltonian cycle.
-/

-- INITIAL DEFINITIONS

def NeBot (G : Graph α β) : Prop :=
  G ≠ ⊥

@[simp]
lemma NeBot_iff_vertexSet_nonempty {G : Graph α β} :
    G.NeBot ↔ V(G).Nonempty := by
  simp [NeBot]

lemma vertexSet_nonempty_of_NeBot {G : Graph α β} (h : G.NeBot) :
    V(G).Nonempty := by
  rwa [←NeBot_iff_vertexSet_nonempty]

lemma NeBot_iff_encard_positive {G : Graph α β} :
    G.NeBot ↔ 0 < V(G).encard := by
  simp

lemma NeBot_of_ncard_positive {G : Graph α β} (h : 0 < V(G).ncard) : G.NeBot := by
  rw [NeBot, ne_eq, ←vertexSet_eq_empty_iff, ←ne_eq, ←Set.nonempty_iff_ne_empty]
  apply nonempty_of_ncard_ne_zero
  linarith

@[simp]
lemma eDegree_eq_top (hx : G.eDegree x = ⊤) : ¬ G.LocallyFinite :=
  fun _ ↦ eDegree_ne_top hx

lemma locallyFinite_of_eDegree_ne_top (hG : ∀ x, G.eDegree x ≠ ⊤) : G.LocallyFinite := by
  by_contra! hcon
  simp [locallyFinite_iff] at hcon
  obtain ⟨x, hx⟩ := hcon
  refine hG x ?_
  rw [eq_top_iff]
  suffices {e | G.Inc e x}.encard = ⊤ by
   rw [←this]
   exact G.encard_setOf_inc_le_eDegree x
  simpa

lemma forall_eDegree_ne_top_iff : (∀ x, G.eDegree x ≠ ⊤) ↔ G.LocallyFinite :=
  ⟨locallyFinite_of_eDegree_ne_top, fun _ _ ↦ eDegree_ne_top⟩

lemma exists_eDegree_eq_top_of_not_locallyFinite (hG : ¬ G.LocallyFinite) :
    ∃ x, G.eDegree x = ⊤ := by
  simp [←forall_eDegree_ne_top_iff] at hG
  assumption

lemma exists_eDegree_eq_top_iff : (∃ x, G.eDegree x = ⊤) ↔ ¬ G.LocallyFinite := by
  refine ⟨fun ⟨_, hx⟩ ↦ eDegree_eq_top hx, exists_eDegree_eq_top_of_not_locallyFinite⟩

noncomputable def minEDegree (G : Graph α β) : ℕ∞ :=
  ⨅ x ∈ V(G), G.eDegree x

-- G.minDegree returns the minimum degree of its vertices if G is finite, else it returns 0
noncomputable def minDegree (G : Graph α β) : ℕ :=
  G.minEDegree.toNat

-- if G is Nonempty and LocallyFinite, then the two definitions agree
lemma natCast_minDegree_eq (G : Graph α β) [G.LocallyFinite] (hG : G.NeBot) :
    (G.minDegree : ℕ∞) = G.minEDegree := by
  simp [minDegree, minEDegree]
  rw [NeBot_iff_vertexSet_nonempty] at hG
  exact hG

lemma minEDegree_eq_top_of_empty (hG : G = ⊥) :
    G.minEDegree = ⊤ := by
  simp only [minEDegree]
  have : V(G) = ∅ := by simpa
  simp [this]

lemma minEDegree_eq_top (hG : G.minEDegree = ⊤) :
    G = ⊥ ∨ ¬ G.LocallyFinite := by
  by_contra! hcon
  obtain ⟨hcon₁, hcon₂⟩ := hcon
  have ⟨x, hx⟩ : V(G).Nonempty := by
    rw [←NeBot_iff_vertexSet_nonempty]
    exact hcon₁
  simp [minEDegree] at hG
  specialize hG _ hx
  assumption

lemma minDegree_eq_zero_of_empty (hG : G = ⊥) :
    G.minDegree = 0 := by
  unfold minDegree
  simp [minEDegree_eq_top_of_empty hG]

-- minEDegree is minimal among all degrees
lemma minEDegree_le_eDegree (hx : x ∈ V(G)) :
    G.minEDegree ≤ G.eDegree x := by
  exact biInf_le G.eDegree hx

lemma minDegree_le_degree [G.LocallyFinite] (hx : x ∈ V(G)) :
    G.minDegree ≤ G.degree x := by
  simp [minDegree,  minEDegree, degree]
  refine ENat.toNat_le_toNat (minEDegree_le_eDegree hx) eDegree_ne_top

-- TODO: shuffle into ENat
lemma ENat.exists_eq_biInf {ι} {S : Set ι} (hS : S.Nonempty) (f : ι → ℕ∞) :
    ∃ a ∈ S, f a = ⨅ x ∈ S, f x := by
  rw [←sInf_image]
  exact csInf_mem (hS.image f)

lemma exists_vertex_minEDegree (hG : G ≠ ⊥) : ∃ x ∈ V(G), G.eDegree x = G.minEDegree := by
  unfold minEDegree
  apply ENat.exists_eq_biInf
  simpa

lemma exists_vertex_minDegree (hG : G ≠ ⊥) : ∃ x ∈ V(G), G.degree x = G.minDegree := by
  obtain ⟨x, hxG, hx⟩ := exists_vertex_minEDegree hG
  refine ⟨x, hxG, ?_⟩
  simp [degree, minDegree]
  tauto

-- MORE THINGS

lemma setOf_adj_subset {G : Graph α β} (x : α) : {y | G.Adj x y} ⊆ V(G) := by
  intro y hy
  simp at hy
  exact hy.right_mem

-- maybe this should be `Neighbor`?
lemma encard_setOf_adj_le {G : Graph α β} [G.Simple] {x : α} (h : x ∈ V(G)) :
    {y | G.Adj x y}.encard + 1 ≤ V(G).encard := by
  have : ({x} : Set α).encard = 1 := by simp
  rw [← this]; clear this
  rw [←Set.encard_union_eq]
  swap
  · simp; apply not_adj_self
  apply encard_le_encard
  simp
  refine insert_subset h ?_
  exact setOf_adj_subset _

-- by incAdjEquiv
lemma eDegree_le_encard {G : Graph α β} [G.Simple] {x : α} (h : x ∈ V(G)) :
    G.eDegree x + 1 ≤ V(G).encard := by
  have solver := G.incAdjEquiv x
  simp [eDegree_eq_encard_inc]
  change {e // e ∈ {e | G.Inc e x}} ≃ {y // y ∈ {y | G.Adj x y}} at solver
  repeat rw [←coe_eq_subtype] at solver
  rw [solver.encard_eq]
  exact encard_setOf_adj_le h

lemma degree_le_ncard {G : Graph α β} [G.Simple] [G.Finite] {x : α} (h : x ∈ V(G)) :
    G.degree x + 1 ≤ V(G).ncard := by
  suffices hyp : G.eDegree x + 1 ≤ V(G).encard
  · rw [←natCast_degree_eq, ←Set.Finite.cast_ncard_eq vertexSet_finite] at hyp
    enat_to_nat!; assumption
  exact eDegree_le_encard h

lemma degree_lt_ncard {G : Graph α β} [G.Simple] [G.Finite] {x : α} (h : x ∈ V(G)) :
    G.degree x < V(G).ncard := by
  linarith [degree_le_ncard h]

lemma minDegree_lt_ncard {G : Graph α β} [G.Simple] [G.Finite] (hNeBot : G.NeBot) :
    G.minDegree < V(G).ncard := by
  have ⟨v,hvG, vspec⟩ := G.exists_vertex_minDegree hNeBot
  rw [←vspec]
  apply degree_lt_ncard
  tauto

--The exercises start here
--I added this lemma. Seems important. Do we need to prove it or already exists but is not working?
lemma isCompOf_subset (G H : Graph α β) (hHG : H.IsCompOf G) : V(H) ⊆ V(G) := by
  have hclo : H ≤c G := by
      --Richard already has a lemma for this
      exact IsCompOf.isClosedSubgraph hHG
  exact IsClosedSubgraph.vertexSet_mono hclo
  -- Use IsClosedSubgraph.vertexSet_mono to finsih


lemma minDegree_le_minDegree_of_isCompOf (G H : Graph α β) [G.Finite] (hHG : H.IsCompOf G) :
    G.minDegree ≤ H.minDegree := by
    obtain ⟨v, hv, hveq⟩ := H.exists_vertex_minDegree
      (NeBot_iff_vertexSet_nonempty.2 hHG.nonempty)
    rw [←hveq]
    have hvG : v ∈ V(G) := by
      --I cheated and added the lemma above
      have hcheat : V(H) ⊆ V(G) := isCompOf_subset G H hHG
      -- Have should follow now
      exact hcheat hv
    have hclo : H ≤c G := by
      --Richard already has a lemma for this
      exact IsCompOf.isClosedSubgraph hHG
    have heq : H.degree v = G.degree v := by
      --Use IsClosedSubgraph.degree_eq
      exact IsClosedSubgraph.degree_eq hHG.isClosedSubgraph hv
    rw [heq]
    exact minDegree_le_degree hvG

  --Somhow I did this exercise instead
lemma minDegree_le_minDegree_of_Subgraph (G H : Graph α β) [G.Finite] (hHG : H ≤s G) :
    H.minDegree ≤ G.minDegree := by
    --The following two haves are used in the obtain.
    --First one follows from H being a component of a finite graph
  have Hfin: H.Finite := finite_of_le hHG.le
  obtain (hne | hni) := Classical.em (H.NeBot)
  · have gne : G.NeBot := by
      rw [NeBot_iff_vertexSet_nonempty]
      rw [NeBot_iff_vertexSet_nonempty] at hne
      have VHseVG : V(H) ⊆ V(G) := hHG.le.vertex_subset
      exact Nonempty.mono VHseVG hne
    obtain ⟨v, hv, hveq⟩ := H.exists_vertex_minDegree hne
    rw [←hveq]
    have hvG: v ∈ V(G) := hHG.le.vertex_subset hv
    obtain ⟨w, gw, gweq⟩ := G.exists_vertex_minDegree gne
    have wvH: w ∈ V(H) := by
      rw [hHG.vertexSet_eq]
      exact gw
    have h1 : H.degree w ≤ G.degree w := degree_mono hHG.le w
    rw [← gweq, hveq]
    have h2 : H.minDegree ≤ H.degree w := minDegree_le_degree wvH
    linarith


  --This is the case the graph is empty. Richard has a nice lemma that if the graph is
  --empty or infinite then the min degree is 0. We just need to rw that
  rw [H.minDegree_eq_zero_of_empty (by simp at hni; assumption)]
  exact Nat.zero_le G.minDegree

lemma ge_two_components_of_not_connected {G : Graph α β} (hNeBot : G.NeBot) (h : ¬ G.Connected) :
    2 ≤ G.Components.encard := by
  -- G has a vertex
  obtain ⟨ v, hv ⟩ := vertexSet_nonempty_of_NeBot hNeBot
  -- I cheated here, but this lemma is missing and I'm guessing it should be in connected
  obtain ⟨ H, hH, hvH ⟩ := G.exists_IsCompOf_vertex_mem hv
  have hbig : ∃ w ∈ V(G), w ∉ V(H) := by
    by_contra! hw
    --Our contradiction is that G is connected. The following have is the hardest.
    have hcon : G = H := by
    -- I think I went overboard on this refine, try refine ext_inc ?_ ?_ and see what happens
      refine ext_inc (Subset.antisymm_iff.mpr ⟨hw, isCompOf_subset G H hH ⟩  ) ?_
      intro e x
      -- Here is a one line proof, try to write this in steps.
      refine ⟨ fun hh ↦ (Inc.of_isClosedSubgraph_of_mem hh (IsCompOf.isClosedSubgraph hH)
          (hw x (Inc.vertex_mem hh))), fun hh ↦ (Inc.of_le hh (IsCompOf.le hH)) ⟩
    rw [ hcon ] at hH
    -- Just state the contradiction
    sorry
  obtain ⟨ w, hw, hwH ⟩ := hbig
  obtain ⟨ H₁, hH1, hvH1 ⟩ := G.exists_IsCompOf_vertex_mem hw
  have : H ≠ H₁ := by sorry
  sorry
  -- Set.Nontrivial, Set.Subsingleton


def ConnectivityGE (G : Graph α β) (k : ℕ∞) : Prop :=
  ∀ S, S.encard < k → (G - S).Connected

lemma minEDegree_ge_one_of_connected_nontrivial
    {G : Graph α β} (hConn : G.Connected) (hNontrivial : 1 < V(G).encard) :
    ∀ x ∈ V(G), 1 ≤ G.eDegree x := by
  by_contra! hyp; obtain ⟨x, hxG, hx⟩ := hyp
  rw [ENat.lt_one_iff_eq_zero] at hx
  rw [connected_iff_forall_exists_adj] at hConn
    <;> [skip; use x]
  specialize hConn {x}
  have : {x} ⊂ V(G) := by
    refine ⟨by simp; tauto, ?_⟩
    intro bad
    have := Set.encard_le_encard bad
    have := hNontrivial.trans_le this
    simp at this
  simp at hConn
  specialize hConn this; clear this
  obtain ⟨y, ⟨hyG, hne⟩, hadj⟩ := hConn
  rw [eDegree_eq_zero_iff_adj] at hx
  exact hx y hadj

lemma unique_neighbor_of_eDegree_eq_one
    {G : Graph α β} {x : α} (hx : G.eDegree x = 1)
    {y z : α} (hxy : G.Adj x y) (hxz : G.Adj x z) :
    y = z := by
  have heq := G.eDegree_eq_encard_add_encard x
  rw [hx] at heq
  have no_loops : {e | G.IsLoopAt e x}.encard = 0 := by
    by_contra! hyp
    rw [←ENat.one_le_iff_ne_zero] at hyp
    replace hyp : 2 ≤ 2 * {e | G.IsLoopAt e x}.encard :=
      le_mul_of_one_le_right' hyp
    have hle : 2 * {e | G.IsLoopAt e x}.encard ≤ 1 := by
      simp [heq]
    have := hyp.trans hle
    simp at this
  rw [no_loops] at heq; simp at heq; symm at heq
  rw [Set.encard_eq_one] at heq
  obtain ⟨e, he⟩ := heq
  have setOf_inc_le : {e | G.Inc e x} ⊆ {e} := by
    simp [inc_iff_isLoopAt_or_isNonloopAt]
    rintro f (h|h) <;> [exfalso; skip]
    · suffices f ∈ {e | G.IsLoopAt e x} by simp_all
      exact h
    suffices f ∈ {e | G.IsNonloopAt e x} by simp_all
    exact h
  simp at setOf_inc_le
  obtain ⟨xy, hxy⟩ := hxy
  obtain ⟨xz, hxz⟩ := hxz
  suffices xy = xz by
    subst this; exact IsLink.right_unique hxy hxz
  have hxy' : xy = e := setOf_inc_le _ hxy.inc_left
  have hxz' : xz = e := setOf_inc_le _ hxz.inc_left
  simp_all

lemma IsTree.exists_vertex_eDegree_ge_two
    {T : Graph α β} (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ x ∈ V(T), 2 ≤ T.eDegree x := by
  have hMinDeg : ∀ x ∈ V(T), 1 ≤ T.eDegree x := by
    refine minEDegree_ge_one_of_connected_nontrivial hT.connected ?_
    suffices (1 : ℕ∞) < 3 by
      exact this.trans_le hV
    simp
  by_contra! hyp
  replace hyp : ∀ x ∈ V(T), T.eDegree x = 1 := by
    intro x hxT
    specialize hyp _ hxT
    specialize hMinDeg _ hxT
    enat_to_nat! <;> omega
  clear hMinDeg
  have hT_nonempty : V(T).Nonempty := by
    simp only [←Set.encard_pos]
    enat_to_nat!; omega
  have ⟨x, hxT⟩ := hT_nonempty
  have hx_ssub : {x} ⊂ V(T) := by
    refine ⟨by simp; tauto, ?_⟩
    intro bad
    have := Set.encard_le_encard bad
    simp at this; enat_to_nat!; omega
  have hconn := hT.connected
  rw [connected_iff_forall_exists_adj hT_nonempty] at hconn
  have hy := hconn _ hx_ssub (by simp)
  simp at hy
  obtain ⟨y, ⟨hyT, hne⟩, hadj⟩ := hy
  have hxy_ssub : {x,y} ⊂ V(T) := by
    refine ⟨?_, ?_⟩
    · simp [pair_subset_iff]; tauto
    intro bad
    have := Set.encard_le_encard bad
    have := hV.trans this
    replace hne : x ≠ y := fun a ↦ hne (id (Eq.symm a))
    simp [Set.encard_pair hne] at this
    norm_num at this
  have hz := hconn _ hxy_ssub (by simp)
  obtain ⟨x', hx', z, hz⟩ := hz
  apply hz.1.2
  simp at hx'; obtain (hx'|hx') := hx'
    <;> symm at hx'
    <;> subst hx'
    <;> [(right; simp); (left; symm at hadj)]
    <;> exact unique_neighbor_of_eDegree_eq_one (hyp _ ‹_›) hz.2 ‹_›

lemma IsTree.exists_length_two_path
    {T : Graph α β} (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ P, T.IsPath P ∧ P.length = 2 := by
  have T_simple := hT.isForest.simple
  have ⟨x, hxT, hx⟩ : ∃ x ∈ V(T), 2 ≤ T.eDegree x :=
    hT.exists_vertex_eDegree_ge_two hV
  rw [eDegree_eq_encard_adj] at hx
  have ⟨N, hN_sub, hN_encard⟩ := Set.exists_subset_encard_eq hx
  rw [Set.encard_eq_two] at hN_encard
  obtain ⟨y,z,hne,rfl⟩ := hN_encard
  -- pick a path between y and z which does not go through x
  obtain ⟨hy, hz⟩ : T.Adj x y ∧ T.Adj x z := by
    refine ⟨hN_sub ?_, hN_sub ?_⟩ <;> simp
  have ⟨hyT, hzT⟩ : y ∈ V(T) ∧ z ∈ V(T) := by
    have := T.setOf_adj_subset x
    refine ⟨?_, ?_⟩  <;>
      apply this <;> assumption
  obtain ⟨ey, hey⟩ := hy
  obtain ⟨ez, hez⟩ := hz
  refine ⟨cons y ey (cons x ez (nil z)), ?_, by simp⟩
  simp
  have hne_xy : x ≠ y := hey.adj.ne
  have hne_xz : x ≠ z := hez.adj.ne
  tauto

-- the same as previous lemma, just reworded
lemma IsTree.exists_nontrivial_path
    {T : Graph α β} (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ P, T.IsPath P ∧ P.Nontrivial := by
  obtain ⟨P, P_isPath, P_length⟩ := hT.exists_length_two_path hV
  refine ⟨P, P_isPath, ?_⟩
  rw [←WList.two_le_length_iff]
  omega

lemma IsTree.exists_isSepSet
    {T : Graph α β} (hT : T.IsTree) (hV : 3 ≤ V(T).encard) :
    ∃ S, IsSepSet T S ∧ S.encard = 1 := by
  -- we show there exists a vertex x of degree at least 2, in which case
  -- the singleton {x} is exactly our sepset
  have ⟨x, hxT, hx⟩ : ∃ x ∈ V(T), 2 ≤ T.eDegree x :=
    hT.exists_vertex_eDegree_ge_two hV

  -- now we have our vertex x of degree ≥ 2
  use {x}
  refine ⟨?_, by simp⟩
  simp [IsSepSet]
  refine ⟨by assumption, ?_⟩
  -- choose any two neighbors of x; they must be separated by x
  intro bad
  have T_simple := hT.isForest.simple
  rw [eDegree_eq_encard_adj] at hx
  have ⟨N, hN_sub, hN_encard⟩ := Set.exists_subset_encard_eq hx
  rw [Set.encard_eq_two] at hN_encard
  obtain ⟨y,z,hne,rfl⟩ := hN_encard
  -- pick a path between y and z which does not go through x
  obtain ⟨hy, hz⟩ : T.Adj x y ∧ T.Adj x z := by
    refine ⟨hN_sub ?_, hN_sub ?_⟩ <;> simp
  have ⟨hyT', hzT'⟩ : y ∈ V(T - {x}) ∧ z ∈ V(T - {x}) := by
    simp
    have := hT.isForest.loopless
    refine ⟨⟨hy.right_mem, ?_⟩, ⟨hz.right_mem, ?_⟩⟩
      <;> rintro rfl <;> apply T.not_adj_self <;> assumption
  obtain ⟨P, hP, hP_first, hP_last⟩ := (bad.connectedBetween hyT' hzT').exists_isPath
  obtain ⟨xy, hxy⟩ := hy
  obtain ⟨xz, hxz⟩ := hz
  let Q' := cons x xy P
  have hQ'_isPath : T.IsPath Q' := by
    simp [Q']
    refine ⟨hP.of_le vertexDelete_le, by rwa [hP_first], ?_⟩
    intro bad
    replace hP := hP.vertexSet_subset
    apply hP at bad
    rw [vertexDelete_vertexSet] at bad
    apply bad.2
    simp
  let Q := cons z xz Q'
  have hQ_isCycle : T.IsCycle Q := by
    simp [Q]
    have := hQ'_isPath.cons_isCycle_of_nontrivial (G := T) (P := Q') (e := xz)
    simp [Q', hP_last, hxz] at this
    apply this
    by_contra! bad
    simp at bad
    apply hne
    rw [←hP_first, ←hP_last]
    exact Nil.first_eq_last bad
  exact hT.isForest _ hQ_isCycle

section WalkLemmas

def PathSet (G : Graph α β) := {p | IsPath G p}

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

private
lemma IsWalk.vertex_mem_of_mem' {p} (hp : G.IsWalk p) (x) (hx : x ∈ p.vertex) : x ∈ V(G) :=
  hp.vertex_mem_of_mem hx

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

def IsLongestPath (G : Graph α β) (p : WList (α) β) :=
  MaximalFor G.IsPath (fun w => w.length) p

@[simp]
lemma IsLongestPath.isPath {p} (h : G.IsLongestPath p) : G.IsPath p := h.1

lemma exists_longest_path
    (G : Graph α β) [G.Simple] [G.Finite] (hNeBot : G.NeBot) :
    ∃ p, G.IsLongestPath p :=
  Set.Finite.exists_maximalFor _ _ (G.pathSet_finite) (G.pathSet_nonempty hNeBot)

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
  sorry

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
lemma IsCycle.cycle_length_ge_3_of_simple
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

lemma IsPath.existsUnique_left_edge
    {w : WList α β} (hw : G.IsPath w) {y : α} (hyw : y ∈ w) (hy : y ≠ w.first) :
    ∃! e, ∃ x, w.DInc e x y := by
  obtain ⟨e, x, h⟩ := exists_left_edge w hyw hy
  refine ⟨e, ⟨x, h⟩, ?_⟩
  simp
  intro e' x' h'
  simp [dInc_iff_eq_of_dInc_of_vertex_nodup_right hw.nodup h] at h'
  tauto

lemma IsPath.existsUnique_right_edge
    {w : WList α β} (hw : G.IsPath w) {x : α} (hxw : x ∈ w) (hx : x ≠ w.last) :
    ∃! e, ∃ y, w.DInc e x y := by
  generalize hw'_def : w.reverse = w'; symm at hw'_def
  have hw' : G.IsPath w' := by simp_all
  have hx' : x ≠ w'.first := by simp_all
  have hxw' : x ∈ w' := by simp_all
  obtain ⟨e, he⟩ := IsPath.existsUnique_left_edge hw' hxw' hx'
  simp_all
  refine ⟨e, he.1, ?_⟩
  simp
  exact he.2

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

lemma IsLongestPath.nontrivial_of_connected_of_encard_ge_three
    {P} (hP : G.IsLongestPath P)
    (hConn : G.Connected)
    (hNontrivial : 3 ≤ V(G).encard) :
    P.Nontrivial := by
  -- we will just leverage our result on trees
  obtain ⟨T, hT, hles⟩ := hConn.exists_isTree_spanningSubgraph
  have hT_encard : 3 ≤ V(T).encard := by
    simpa [hles.vertexSet_eq]
  have ⟨Q, hQ, hQ_length⟩ := hT.exists_length_two_path hT_encard
  replace hQ : G.IsPath Q := hQ.of_le hles.le
  rw [← WList.two_le_length_iff]
  have solver := maximalFor_is_upper_bound WList.length hP _ hQ
  omega

lemma IsPath.exists_isPath_vertex
    [DecidableEq α]
    (P : WList α β) (hP : G.IsPath P) (hu : u ∈ P) :
    ∃ P₀ P₁, G.IsPath P₀ ∧ G.IsPath P₁ ∧ u = P₀.last ∧ u = P₁.first ∧
    P₀.length + P₁.length = P.length ∧ P = (P₀ ++ P₁) := by
  set Pre : WList α β := prefixUntilVertex P u with h_pre
  set Suf : WList α β := suffixFromVertex P u with h_suf
  use Pre
  use Suf
  rw [h_pre,h_suf]
  refine ⟨ IsPath.prefix hP (prefixUntilVertex_isPrefix P u),
  (IsPath.suffix hP (suffixFromVertex_isSuffix P u)),
  Eq.symm (prefixUntilVertex_last hu) , Eq.symm (suffixFromVertex_first hu),
  prefixUntilVertex_suffixFromVertex_length P u hu,
  Eq.symm (prefixUntilVertex_append_suffixFromVertex P u) ⟩

lemma IsCycle.rotate_one [DecidableEq α] {C : WList α β} (hC : G.IsCycle C)
    : ∃ e, (C.rotate 1) = (C.tail).concat e (C.tail.first) := by
  set e := hC.nonempty.firstEdge
  use e
  have hCn : C = cons C.first e C.tail := by
    exact Eq.symm (Nonempty.cons_tail hC.nonempty)
  nth_rw 1 [hCn]
  rw [cons_rotate_one ]

lemma IsCycle.idxOf_rotate_one [DecidableEq α] {a : α} {C : WList α β} (hC : G.IsCycle C)
    (hnt : C.Nonempty) (h1 : C.first ≠ a ) (ha : a ∈ C) :
    (C.rotate 1).idxOf a + 1 = C.idxOf a := by
  obtain ⟨e, h ⟩ :=  hC.rotate_one
  have hat : a ∈ C.tail := by
    obtain hfirst | h1 := eq_first_or_mem_tail ha
    · by_contra
      exact h1 (id (Eq.symm hfirst))
    exact h1
  have := idx_Of_tail hnt h1 ha
  rwa [h, idxOf_concat_ne C.tail e hat]

lemma IsCycle.idxOf_rotate_first [DecidableEq α] {a  : α} {n : ℕ} {C : WList α β} (hC : G.IsCycle C)
    (hn : n < C.length) (hle : n + 1 ≤ C.idxOf a ) : (C.rotate n).first ≠ a := by
  rw [rotate_first C n (Nat.le_of_succ_le hn) ]
  by_contra hc
  rw[←hc] at hle
  rw [idxOf_get hC hn ] at hle
  linarith

lemma IsCycle.idxOf_rotate_n_le [DecidableEq α] {a : α} {n : ℕ} {C : WList α β} (hC : G.IsCycle C)
    (ha : a ∈ C) (hn : n < C.length)
    (hnt : C.Nonempty) (hle : n ≤ C.idxOf a ) :
    (C.rotate n).idxOf a + n  = C.idxOf a := by
  induction n with
  | zero =>
  simp_all
  | succ n hi =>
  rw[←rotate_rotate C n 1]
  have hlen : n ≤ C.length := by
    linarith
  have hle' : n ≤ C.idxOf a := by
    linarith
  have han : (C.rotate n).first ≠ a := by
    rw [rotate_first C n hlen ]
    by_contra hc
    rw[←hc, idxOf_get hC (Nat.lt_of_succ_lt hn) ] at hle
    linarith
  have hf := (rotate hC n ).idxOf_rotate_one ((rotate_nonempty_iff n).mpr hnt )
      han (((hC.isClosed).mem_rotate).2 ha)
  have := hi (Nat.lt_of_succ_lt hn) hle'
  linarith

lemma IsCycle.idxOf_rotate_one_first [DecidableEq α] {a : α} {C : WList α β} (hC : G.IsCycle C)
    (h1 : C.first = a ) (ha : a ∈ C) :
    (C.rotate 1).idxOf a + 1 = C.length := by
  obtain ⟨e, hrC ⟩ := hC.rotate_one
  have hft : C.first = C.last := (hC.isClosed).eq
  rw [h1] at hft
  rw [hrC, idxOf_concat_ne C.tail e ((hC.isClosed).mem_tail_iff.2 ha ), hft, (tail_last C).symm ,
  idxOf_last C.tail (hC.nodup), tail_length]
  sorry

lemma IsCycle.idxOf_rotate_untilfirst
    [DecidableEq α] {a : α} {C : WList α β} (hC : G.IsCycle C) (ha : a ∈ C) :
    (C.rotate (C.idxOf a + 1)).idxOf a + 1 = C.length := by
  have hfirst : a = (C.rotate (C.idxOf a)).first := by
    exact Eq.symm (rotate_idxOf_first ha)
  have ha' : a ∈ (C.rotate (C.idxOf a)) := by
    refine (IsClosed.mem_rotate (hC.isClosed)).mpr ha
  rw[←rotate_rotate C (C.idxOf a) 1, (rotate hC (C.idxOf a)).idxOf_rotate_one_first
    (Eq.symm (rotate_idxOf_first ha)).symm ha' ]
  simp

lemma IsCycle.idxOf_rotate_n [DecidableEq α] {a : α} {n : ℕ} (C : WList α β) (hC : G.IsCycle C)
    (hnt : C.Nonempty) (ha : a ∈ C) (hn : n < C.length)
    (hle : C.idxOf a < n ) : (C.rotate n).idxOf a + n = C.length + C.idxOf a := by
  induction n with
  | zero =>
  simp_all
  | succ n hi =>
  obtain han | hu := eq_or_ne (C.idxOf a) n
  · rw [←han]
    have hle' : C.idxOf a < C.length := by
      rw[han]
      exact Nat.lt_of_succ_lt hn
    have := hC.idxOf_rotate_untilfirst ha
    linarith
  rw[←rotate_rotate C n 1]
  have hg : n < C.length := by exact Nat.lt_of_succ_lt hn
  have hii := hi hg (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hle ) hu )
  have hnf : (C.rotate n).first ≠ a := by
    by_contra hc
    have hia : (C.rotate n).idxOf a = 0 := by
      rw[←hc]
      exact idxOf_first (C.rotate n)
    rw [hia] at hii
    simp at hii
    rw [hii] at hg
    linarith
  have ha' : a ∈ C.rotate n := by
    refine (IsClosed.mem_rotate (hC.isClosed)).mpr ha
  have hf := (rotate hC n ).idxOf_rotate_one ((rotate_nonempty_iff n).mpr hnt) hnf ha'
  linarith

--I think this lemma is important and useful for us

lemma IsCycle.length_eq_tail_vertex_length {C} (hC : G.IsCycle C) :
    C.length = C.tail.vertex.length := by
  induction C with simp_all

lemma IsCycle_length_to_vertex {G : Graph α β} {C : WList α β} (hC : G.IsCycle C ) :
    C.length = V(C).encard := by
  rw [hC.length_eq_tail_vertex_length]
  sorry

lemma IsCycle_length_bound {G : Graph α β} {C : WList α β} (hC : G.IsCycle C ) :
    C.length ≤ V(G).encard := by

  have hsubs := hC.isWalk.vertexSet_subset
  have : C.length = V(C).encard := by
    sorry
  sorry

def IsHamiltonianCycle (G : Graph α β) (C : WList α β) : Prop :=
  G.IsCycle C ∧ C.length = V(G).ncard

lemma IsHamiltonianCycle.vertexSet_encard_eq (G : Graph α β) (C : WList α β) (hC : G.IsCycle C )
    (hen : C.vertexSet.encard = V(G).encard ) : IsHamiltonianCycle G C := by sorry

end WalkLemmas

lemma Bound_on_indepSet {G : Graph α β} [G.Simple] [G.Finite]
    (S : Set (α)) (hS : IsSepSet G S)
    (H : Graph α β ) (hH : IsCompOf H (G-S) )
    (A : Set (α)) (hA : IsMaxIndependent G A) ( v : α ) (hx : v ∈ V(H) ∩ A )
    : G.degree v + (A ∩ V(H)).ncard ≤ (V(H)).ncard + S.ncard := by
    -- Need degree_eq_ncard_adj, will work after update
  let Inc := {w | G.Adj v w}
  let IncW := {w | G.Adj v w} ∩ V(H)

  have disjoint : Inc ∩ (A ∩ V(H)) = ∅ := by
    by_contra hcon
    have ⟨ w, hw ⟩ : ∃ e, e ∈ Inc ∩ (A ∩ V(H)) := by
      refine nonempty_def.mp (nonempty_iff_ne_empty.mpr hcon)
    have hwvAdj: G.Adj v w := by
      have h1 : w ∈ Inc := mem_of_mem_inter_left hw
      exact h1
    have hco : ¬ G.Adj v w := by
      have hAindep : IsIndependent G A := by exact hA.1
      have hvA : v ∈ A := mem_of_mem_inter_right hx
      have hwA := mem_of_mem_inter_left ( mem_of_mem_inter_right hw)
      apply hAindep.2 hvA hwA
      by_contra hc
      rw [hc] at hwvAdj
      exact (not_adj_self G w) hwvAdj
    exact hco hwvAdj

  --For the following you need that the sets are disjoint
  have hf1 : (Inc ∪ (A ∩ V(H))).ncard = Inc.ncard + (A ∩ V(H)).ncard := by
    -- have hfin2 : (A ∩ V(H)).Finite := by
    --   have : (A ∩ V(H)) ⊆ V(G) := by
    --     exact fun ⦃a⦄ a_1 ↦ (hA.1.1) (inter_subset_left a_1)
    --   have : V(G).Finite := by exact vertexSet_finite
    --   exact Finite.subset vertexSet_finite (fun ⦃a⦄ a_1 ↦ (hA.1.1) (inter_subset_left a_1))
    apply ncard_union_eq
    exact disjoint_iff_inter_eq_empty.mpr disjoint
    exact finite_setOf_adj G
    exact Finite.subset vertexSet_finite (fun ⦃a⦄ a_1 ↦ (hA.1.1) (inter_subset_left a_1))
  have hf2 : (V(H) ∪ S).ncard = V(H).ncard + S.ncard := sorry
  --Use degree_eq_ncard_adj
  have hdeg : G.degree v = Inc.ncard := sorry
  --This one should be straight forward
  have h1 : Inc ∪ (A ∩ V(H)) = (IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) := by
    have hinc : Inc = IncW ∪ (Inc\IncW) := by
      refine Eq.symm (union_diff_cancel' (fun ⦃a⦄ a_1 ↦ a_1) inter_subset_left)
    --conv => lhs ; rhs
    nth_rewrite 1 [hinc]
    exact union_right_comm IncW (Inc \ IncW) (A ∩ V(H))
  --Again, disjoint sets
  have hf3 : ((IncW ∪ (A ∩ V(H))) ∪ (Inc\IncW) ).ncard =
      (IncW ∪ (A ∩ V(H))).ncard + (Inc\IncW).ncard
    := by
      sorry
  --Very important
  rw [←hf2,hdeg,←hf1,h1, hf3 ]

  --Inequalities to finish
  have hH : (IncW ∪ (A ∩ V(H))).ncard ≤ V(H).ncard := by
    have hH1 : (IncW ∪ (A ∩ V(H))) ⊆ V(H) := by
      exact union_subset (inter_subset_right) (inter_subset_right)
    refine ncard_le_ncard hH1 ?_
    have hP : V(G-S) ⊆ V(G) := by
      simp [vertexDelete_vertexSet]
      exact diff_subset
    exact Finite.subset (vertexSet_finite) (fun ⦃a⦄ a_1 ↦ hP ((isCompOf_subset (G - S) H hH ) a_1))

  have hS : (Inc\IncW).ncard ≤ S.ncard := by
    have hH1 :(Inc\IncW) ⊆ S := by
      intro w hwsub
      have hAdj : G.Adj v w := by
        have h : w ∈ Inc := mem_of_mem_inter_left hwsub
        exact h
      sorry
    sorry
  linarith

--Again, is missing when G is complete but whatever
lemma indep_to_Dirac {G : Graph α β} [G.Simple] [G.Finite] (h3 : 3 ≤ V(G).ncard)
    (S : Set (α)) (HS : IsMinSepSet G S )
    (A : Set (α)) (hA : IsMaxIndependent G A)
    (hDirac : V(G).ncard ≤ 2 * G.minDegree ) : A.ncard ≤ S.ncard := by
  --Trivial case: Independent set is completely contained in the separator
  obtain ( HAS| he ) := Classical.em (A ⊆ S)
  · have : S.Finite := Set.Finite.subset vertexSet_finite HS.1.1
    exact ncard_le_ncard HAS this
  have ⟨x, hxA, hvS ⟩ : ∃ x ∈ A, x ∉ S := by exact not_subset.mp he
  -- Add hDirac applyed to x. You won't need it immediatly but will need it in all cases

  --We want to use ge_two_components_of_not_connected with G-S so we need:
  have hxS: x ∈ V(G - S) := by
    simp
    have := hA.1.1
    tauto

  have hNeBotS : (G - S).NeBot := by
    apply NeBot_iff_vertexSet_nonempty.2
    tauto

  have hcomp := ge_two_components_of_not_connected hNeBotS sorry
  have ⟨ H1, hccH1, hcH1 ⟩ : ∃ H, IsCompOf H (G-S) ∧ x ∈ V(H) := by
    exact exists_IsCompOf_vertex_mem hxS

  --Here are two options to finish the proof, either define H2 as follows, but it won't be conencted
  --let H2 := G - (V(H1) ∪ S)
  --In this case use hcomp to get V(H2)≠ ∅

  --Second option is to use and prove this
  -- have ⟨ H2, hccH2, h12 ⟩  : ∃ H, IsCompOf H (G-S) ∧ H ≠ H1 := by
  --   sorry
  --see Richards proof using hcomp
  --In this case you will need (V(H2)).ncard ≤ (V(G)\ (V(H1) ∪ S) ).ncard + S.ncard (or something)

  have ⟨H2, ⟨H2comp, H2ne⟩⟩ :
    ∃ H, H.IsCompOf (G - S) ∧ H ≠ H1 := by
    have components_nonempty : (G - S).Components.Nonempty := by
      apply nonempty_of_encard_ne_zero
      intro h; rw [h] at hcomp; clear h
      norm_num at hcomp
    by_contra! hyp_contra
    have is_singleton : (G - S).Components = {H1} := by
      exact (Nonempty.subset_singleton_iff (components_nonempty)).mp hyp_contra
    have : (G - S).Components.encard = 1 := by
      simp [is_singleton]
    rw [this] at hcomp; clear this
    have : (2 : ℕ) ≤ (1 : ℕ) := by exact ENat.coe_le_coe.mp hcomp
    linarith

  -- Second annoying case
  obtain ( Hemp| hAH1 ) := Classical.em ( A ∩ V(H2) = ∅)
  · have ⟨y, hy ⟩ : ∃ y, y ∈ V(H2) \ A := by
      -- Managed to simplify this part a lot - Noah
      rw [← Set.diff_self_inter, Set.inter_comm, Hemp, Set.diff_empty]
      exact H2comp.1.2
    --Apply Bound_on_indepSet with modifications since H2 is not a connected component
    -- You will nee hDirac applied to y
    have := Bound_on_indepSet S HS.1 H1 hccH1 A hA x (by tauto)

    sorry

  --Easy case
  obtain ⟨y, yA2 ⟩ := nonempty_iff_ne_empty.mpr hAH1

  --Use Bound_on_indepSet twice and linarith to conclude. You'll also need
  have h1 : (V(H1)).ncard + S.ncard + (V(H2)).ncard + S.ncard = V(G).ncard + S.ncard := by sorry
  -- Add hDirac applied to y
  sorry


def neighbour_of_Set (G : Graph α β) (H : Set α) (v : α ) : Prop :=
    ∃ w, w ∈ H ∧  Adj G v w

lemma Adj_exists_edge (G : Graph α β) (x y : α) (hA : G.Adj x y) : ∃ e, G.IsLink e x y := hA

--Noah, here is the lemma thats not liking me
lemma Complete_to_cycle {G : Graph α β} [G.Finite] (n : ℕ) (hn : n + 3 ≤ V(G).encard)
    (hcomplete : ∀ v w, v ∈ V(G) → w ∈ V(G) → v ≠ w → G.Adj v w)
    : ∃ C : WList α β, G.IsCycle C ∧ V(C).encard = n + 3 := by
  induction n with
  | zero =>
    simp
    have ⟨ T, hT, hT3 ⟩ := V(G).exists_subset_encard_eq hn
    have ⟨ v, u, w, hvu, hvw, huw, hTel ⟩ := (T.encard_eq_three).1 hT3
    have hv : v ∈ V(G) := by sorry
    have hu : u ∈ V(G) := by sorry
    have hw : w ∈ V(G) := by sorry
    have ⟨ euv, heuv ⟩ := Adj_exists_edge G v u (hcomplete v u hv hu hvu )
    have ⟨ euw, heuw ⟩ := Adj_exists_edge G u w (hcomplete u w hu hw huw )
    have ⟨ ewv, hewv ⟩ := Adj_exists_edge G w v (hcomplete w v hw hv hvw.symm )
    --have : G.IsWalk [ v ] := by sorry
    · have hv : v ∈ V(G) := by
        have : v ∈ T := by
          rw[hTel]
          exact mem_insert v {u, w}
        exact hT this
      have hu : u ∈ V(G) := by
        have : u ∈ T := by
          rw[hTel]
          refine mem_insert_of_mem v (mem_insert u {w})
        exact hT this
      have hw : w ∈ V(G) := by
        have : w ∈ T := by
          rw[hTel]
          refine mem_insert_of_mem v (mem_insert_of_mem u rfl)
        exact hT this
      --have ⟨euv, hh ⟩ : ∃ evu, G.IsLink evu v u := hcomplete v u hv hu hvu
      --use [u v w]
      sorry

  | succ n IH =>

    sorry

lemma Hamiltonian_alpha_kappa {G : Graph α β} [G.Simple] [G.Finite] (h3 : 3 ≤ V(G).encard)
    (S : Set α) (HS : IsMinSepSet G S )
    (A : Set α) (hA : IsMaxIndependent G A)
    (hAS : A.encard ≤ S.encard ) : ∃ C : WList α β, IsHamiltonianCycle G C := by
--grw
  have decEq_α : DecidableEq α := Classical.decEq α

  -- To find a longest cycle, we first need to show the existence of some cycle C'
  have ⟨ C', hC'⟩ : ∃ C, G.IsCycle C := by
    by_contra! hCon
    -- if there is no cycle, then since G is a forest,
    -- any vertex v of degree >= 2 is a separating set
    obtain (h1 | h2) := Classical.em (∃ v, v ∈ V(G) ∧ G.degree v ≥ 2)
    · -- So, S.encard = 1, and thus A.encard <= 1
      have ⟨v, ⟨hvG, hv⟩⟩ := h1
      -- since v has degree at least 2, we can obtain two neighbours
      have hn2 : 1 < {x | G.Adj v x}.ncard := by
        rw [← G.degree_eq_ncard_adj]
        assumption
      have nsFinite : {x | G.Adj v x}.Finite :=
        G.finite_setOf_adj
      rw [one_lt_ncard_iff nsFinite] at hn2
      have ⟨a, b, ha, hb, hab⟩ := hn2
      simp_all
      -- Show that {v} is a separating set
      have vSep : G.IsSepSet {v} := by
        refine ⟨singleton_subset_iff.mpr hvG, ?_⟩
        -- those two neighbours a and b are not connected in G - {v},
        -- because otherwise there would be a cycle
        -- for a contradiction, let's construct the cycle
        by_contra! hCon
        have aVGv : a ∈ V(G - {v}) := by
          have := Adj.right_mem ha
          simp_all only [ne_eq, vertexDelete_vertexSet, mem_diff, mem_singleton_iff, true_and]
          exact fun a_1 ↦ (Adj.ne ha) (id (Eq.symm a_1))
        have bVGv : b ∈ V(G - {v}) := by
          have := Adj.right_mem hb
          simp_all only [ne_eq, vertexDelete_vertexSet, mem_diff, mem_singleton_iff, true_and]
          exact fun a_1 ↦ (Adj.ne hb) (id (Eq.symm a_1))
        have abCon : (G - {v}).ConnectedBetween a b := Connected.connectedBetween hCon aVGv bVGv
        have ⟨abPath, habPath⟩ := ConnectedBetween.exists_isPath abCon
        have ⟨abPathG, vnP⟩ := (isPath_vertexDelete_iff.1 habPath.1)
        -- need to first add v to the ab path
        rw [Adj.eq_1 G] at ha
        have ⟨e, eLink⟩ := ha
        have ⟨e2, e2Link⟩ := hb
        have e2LinkOrig := e2Link
        have enee2 : e ≠ e2 := by
          by_contra!
          rw [← this] at e2Link
          rw [IsLink.isLink_iff eLink] at e2Link
          cases e2Link
          · simp_all only [not_true_eq_false]
          simp_all only [isLink_self_iff, not_isLoopAt, exists_false]
        have vnP : v ∉ abPath := by simp_all
        rw [← habPath.2.1] at eLink
        have vbPath := cons_isPath_iff.2 ⟨abPathG, eLink, vnP⟩
        rw [Adj.eq_1 G] at hb
        have vfirst : v = (cons v e abPath).first := rfl
        have blast : b = (cons v e abPath).last := by tauto
        rw [vfirst, blast] at e2Link
        have e2npe : e2 ∉ (cons v e abPath).edge := by
          simp
          refine ⟨by tauto, ?_⟩
          by_contra!
          have := IsWalk.edge_mem_of_mem habPath.1.isWalk this
          have := (IsLink.mem_vertexDelete_iff e2LinkOrig).1 this
          tauto
        -- then link it up to a cycle, contradicting that G doesn't have any cycle
        have := IsPath.cons_isCycle vbPath e2Link e2npe
        tauto
      -- finally, we have that {v} is a separating set in G
      have hS1 : S.encard ≤ 1 := by
        have := HS.2 {v} vSep
        simp_all only [encard_singleton]
      -- But then the two neighbours of v cannot be adjacent,
      -- because otherwise there would be a cycle
      -- So, A.encard >= 2, contradiction
      have anev : ¬a = v := by
        have := loopless_iff_forall_ne_of_adj.1 (IsForest.loopless hCon) v a ha
        rw [ne_comm, ne_eq] at this
        assumption
      have bnev : ¬b = v := by
        have := loopless_iff_forall_ne_of_adj.1 (IsForest.loopless hCon) v b hb
        rw [ne_comm, ne_eq] at this
        assumption
      obtain (h3 | h4) := Classical.em (G.Adj a b)
      · -- First, the case where a and b are adjacent
        -- Need to construct the cycle a-b-v
        have ⟨e, eLink⟩ := ha
        have ⟨e2, e2Link⟩ := hb
        have ⟨e3, e3Link⟩ := h3
        have avPath := cons_isPath_iff.2 ⟨nil_isPath hvG, ⟨IsLink.symm eLink, by
          rw [mem_nil_iff]
          assumption⟩⟩
        have bavPath := cons_isPath_iff.2 ⟨avPath, ⟨IsLink.symm e3Link, by
          simp_all [mem_cons_iff]
          tauto⟩⟩
        let bav := (cons b e3 (cons a e (nil v)))
        have flLink : G.IsLink e2 bav.first bav.last := by
          simp_all
          exact id (IsLink.symm e2Link)
        have eDis : e2 ∉ (cons b e3 (cons a e (nil v))).edge := by
          simp_all
          refine ⟨?_, ?_⟩
          · by_contra!
            simp_all
            have := G.eq_or_eq_of_isLink_of_isLink e2Link e3Link
            tauto
          by_contra!
          simp_all
          have := IsLink.eq_and_eq_or_eq_and_eq eLink e2Link
          tauto
        have := IsPath.cons_isCycle bavPath flLink eDis
        tauto
      -- Now, a and b are not adjacent
      -- We show {a, b} is independent for a contradiction
      have hI : G.IsIndependent {a, b} := by
        refine ⟨?_, ?_⟩
        · have : a ∈ V(G) := ha.right_mem
          have : b ∈ V(G) := hb.right_mem
          grind only [= subset_def, usr subset_insert, = singleton_subset_iff, = mem_insert_iff,
            = setOf_true, = mem_singleton_iff, = setOf_false, cases Or]
        intro x hx y hy hxy
        simp_all only [mem_insert_iff, mem_singleton_iff, ne_eq]
        have : ¬G.Adj b a := by exact fun a_1 ↦ h4 (id (Adj.symm a_1))
        grind only [= setOf_true, = setOf_false, cases Or]
      have Age2 : 2 ≤ A.encard := by
        have hA2 := hA.2 {a, b} hI
        have : ({a, b} : Set α).encard = 2 := encard_pair hab
        rw [this] at hA2
        exact hA2
      have Ale1 : A.encard ≤ 1 := Std.IsPreorder.le_trans A.encard S.encard 1 hAS hS1
      have : 2 ≤ (1 : ℕ∞) := Std.IsPreorder.le_trans 2 A.encard 1 Age2 Ale1
      simp_all only [Nat.not_ofNat_le_one]

    -- If every vertex has degree <= 1, then S.encard = 0, so we are done
    have Vnz : V(G).Nonempty := by
      rw [←encard_pos]
      suffices (0 : ℕ∞) < 3 by exact this.trans_le h3
      simp
    obtain ⟨v, hv⟩ : ∃ v, v ∈ V(G) := Vnz
    have : ¬G.Connected := by
      -- We know there are ≥ 3 vertices
      -- But all have degree ≤ 1
      have : G.degree v ≤ 1 := by grind only
      sorry
    have Sempty : S.encard = 0 := by
      have esSep : IsSepSet G ∅ := by
        refine ⟨empty_subset V(G), ?_⟩
        rw [vertexDelete_empty]
        assumption
      have : S.encard = (∅ : Set α).encard := by
        have := HS.2 ∅ esSep
        simp_all
      simp_all
    have hGI : G.IsIndependent {v} := ⟨by simp_all, by simp_all⟩
    have := hA.2 {v} hGI
    simp_all

  let S := {C : WList α β | G.IsCycle C }
  have hsne : S.Nonempty := by
    exact nonempty_of_mem hC'
  have hsfin : ((length ) '' S).Finite := by sorry

  --The following obtains a cycle of G that is maximal in length
  obtain ⟨C, hCs⟩ := hsfin.exists_maximalFor' _ _ hsne
  --Now that we got a max cycle, we have two cases
  obtain ( hn| hlen ) := Classical.em (V(C).encard = V(G).encard  )
  · use C
    apply IsHamiltonianCycle.vertexSet_encard_eq G C (hCs.prop) hn
  --There should be an obvious bound on the size of a cycle
  have hCle : V(C).encard < V(G).encard := by
    have hVCG : V(C) ⊆ V(G) := by sorry
    refine Finite.encard_lt_encard ?_ ?_
    --have := hlen (congrArg encard a)
      --simp [hlen]
    exact WList.vertexSet_finite C
    exact HasSubset.Subset.ssubset_of_ne hVCG fun a ↦ hlen (congrArg encard a)
--VC = V(C)
  --have ⟨v, hvV ⟩ : ∃ v, v ∉ C.vertex := sorry
  have hG : V(G-V(C)).Nonempty := by
    by_contra hc
    have hg1 : V(C) ⊆ V(G) := by sorry
    rw[vertexDelete_vertexSet] at hc
    have hconcl : V(G) ⊆ V(C) := by
      intro v hv
      obtain h1 | h2 := Classical.em (v ∈ V(C))
      · exact h1
      by_contra
      have hh : v ∈ V(G)\V(C) := by exact mem_diff_of_mem hv h2
      have hhh : (V(G)\ V(C)).Nonempty := by
        use v
      exact hc hhh
      --rw [←NeBot_iff_vertexSet_nonempty ] at hc
    have hconclusion : V(G) = V(C)  := by exact hconcl.antisymm hg1
    rw[ hconclusion ] at hCle
    exact hlen (congrArg encard (id (Eq.symm hconclusion)))
    --obtain ⟨v, hv ⟩ := hc
    -- have hg : V(G) \ VC = ∅ := by sorry
    -- have hg1 : VC ⊆ V(G) := by sorry
    -- have hconcl : V(G) ⊆ VC  := by exact diff_eq_empty.mp hg
    -- have hconclusion : V(G) = VC  := by exact Subset.antisymm hconcl hg1
  have ⟨D, hD ⟩ := exists_IsCompOf hG
  set Neig : Set α := {v : α | v ∈ C ∧ (neighbour_of_Set G V(D) v) } with h_neig
  --This is the second worst sorry
  have hDadj : ∀ v, v ∈ Neig → ∀ u, u ∈ Neig
      → C.idxOf v ≠ C.idxOf u + 1 := by
    intro v hvN u huN
    by_contra hcon
    obtain ⟨ w, hwD, hwad ⟩ := hvN.2
    obtain ⟨ w', huD, huad ⟩ := huN.2
    --Need to take path in D from w to w' and extend cycle
    sorry
  set NextNeigh : Set α := {v ∈ C | ∃ w ∈ Neig, C.idxOf v + 1 = C.idxOf w  } with h_NN
  have hNNV : NextNeigh ⊆ V(G) :=
    fun ⦃a⦄ b ↦ ((IsCycle.isTrail hCs.prop ).vertexSet_subset)
        ((sep_subset (fun x ↦ List.Mem x C.vertex)
        fun x ↦ ∃ w ∈ Neig, C.idxOf x + 1 = C.idxOf w) b)

    --sep_subset V(G) fun x ↦ ∃ w ∈ Neig, C.idxOf x = C.idxOf w + 1
  have ⟨ v, hvD ⟩ : ∃ v, v ∈ V(D) := IsCompOf.nonempty hD

  have hCNT : C.Nontrivial := by sorry
  --Worst sorry, I will take this one
  have hNNI : IsIndependent G NextNeigh := by
    by_contra hc
    obtain ⟨a, b, ha, hb, hab⟩ := IsIndepndent_nee hNNV hc
    --rw[h_NN] at ha
    obtain ⟨P,e,f, hPath, haP, heP, hfP, hef, hC ⟩ :=
        IsCycle.exists_isPath_vertex hCs.prop hCNT ha.1
    have hbP : b ∈ P := by
      have hhh : b ∈ C.rotate (C.idxOf a)  := by
        refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb.1
      rw [hC] at hhh
      exact (Cycle_conc_index (hab.ne).symm hhh).1

    obtain ⟨ b₁, hb1N, hbind ⟩ := hb.2
    obtain ⟨ a₁, ha1N, haind ⟩ := ha.2
    have hab₁ : b₁ ≠ a := by sorry
    --Basically if b₁ = a then a ∈ Neigh and a,a₁ are adj
    --obtain ⟨P₀,P₁,hP₁,hP₂,hP₀last,hP₀first,hP01d,hP01 ⟩ := IsPath.exists_isPath_vertex P hPath hbP
    set P₀ : WList α β := prefixUntilVertex P b with h_pre
    set P₁ : WList α β := suffixFromVertex P b with h_suf
    have hP₀ := IsPath.prefix hPath (prefixUntilVertex_isPrefix P b)
    have hP₁ := IsPath.suffix hPath (suffixFromVertex_isSuffix P b)
    --have hP₀P₁ := Eq.symm (prefixUntilVertex_append_suffixFromVertex P b)
    rw [←h_pre] at hP₀
    rw [←h_suf] at hP₁
    --rw [←h_pre, ←h_suf] at hP₀P₁
    have hb1P' : b₁ ∈ P := by
        have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
          refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
        rw [hC] at hhh
        exact (Cycle_conc_index hab₁ hhh).1
    have hb1P1 : b₁ ∈ P₁ := by
      have hb1P : b₁ ∈ P := by
        have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
          refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
        rw [hC] at hhh
        exact (Cycle_conc_index hab₁ hhh).1
      rw [Eq.symm (prefixUntilVertex_append_suffixFromVertex P b),←h_pre, ←h_suf] at hb1P
      obtain (hf | hg ):= mem_of_mem_append hb1P
      · rw [h_pre] at hf
        --rw [←Eq.symm (prefixUntilVertex_append_suffixFromVertex P b)] at hb1P
        have hcon := (prefixUntilVertex_index_iff P b hbP hb1P').1 hf
        have hbindP : P.idxOf b + 1 = P.idxOf b₁ := by
          have hhh : b ∈ C.rotate (C.idxOf a)  := by
            refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb.1
          rw[hC] at hhh
          have hg1 := (Cycle_conc_index (hab.ne).symm hhh).2
          have hhh : b₁ ∈ C.rotate (C.idxOf a)  := by
            refine (IsClosed.mem_rotate ((hCs.prop).isClosed )).mpr hb1N.1
          rw[hC] at hhh
          have hg2 := (Cycle_conc_index (hab₁) hhh).2
          rw [←hC] at hg1
          rw [←hC] at hg2
          -- Use lemmas I added by cases on idxOf a ≤ idxOf b along with hg2, hg1 and haind
          sorry
        rw [←hbindP ] at hcon
        linarith
      exact hg
    set P₂ : WList α β := prefixUntilVertex P₁ b₁ with h_pre2
    set P₃ : WList α β := suffixFromVertex P₁ b₁ with h_suf2
    have hP₂ := IsPath.prefix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
        (prefixUntilVertex_isPrefix P₁ b₁)
    have hP₃ := IsPath.suffix (IsPath.suffix hPath (suffixFromVertex_isSuffix P b))
        (suffixFromVertex_isSuffix P₁ b₁)
    --have hP₂P₃ := Eq.symm (prefixUntilVertex_append_suffixFromVertex P₁ b₁)
    rw [←h_pre2] at hP₂
    rw [←h_suf2] at hP₃
    sorry
  have hNNIv : IsIndependent G ( insert v NextNeigh) := by
    --Should not be too bad doing cases
    sorry
  --Finish
  sorry





lemma components_encard_le (G : Graph α β)
    : G.Components.encard ≤ V(G).encard := by
  have h_disj := G.components_pairwise_stronglyDisjoint
  have h_eq := G.eq_sUnion_components
  replace h_eq : V(G) = ⋃ H ∈ G.Components, V(H) := by
    apply congr_arg (fun H : Graph α β ↦ V(H)) at h_eq
    simp_all
  let surj : V(G) → G.Components := by
    rintro ⟨x, hx⟩
    refine ⟨G.walkable x, walkable_isCompOf hx⟩
  have surj_surjective : Function.Surjective surj := by
    rintro ⟨H, H_spec⟩
    have H_nonempty := H_spec.1.2
    have ⟨x, hxH⟩ := H_nonempty
    have hxG : x ∈ V(G) := H_spec.1.1.le.vertex_subset hxH
    use ⟨x, hxG⟩
    simp [surj]
    simp [H_spec.eq_walkable_of_mem_walkable hxH]
  have inj_spec := Function.injective_surjInv surj_surjective
  set inj := Function.surjInv surj_surjective
  exact Function.Embedding.encard_le ⟨inj, inj_spec⟩

lemma finite_components_of_finite {G : Graph α β} (hFinite : G.Finite) :
    G.Components.Finite := by
  refine hFinite.vertexSet_finite.finite_of_encard_le ?_
  exact G.components_encard_le

/- Step 1: WTS G is connected.
Proof: Suppose not. Then the degree of any vertex in the smallest component C of G
would be less than |C| ≤ n/2.
-/

lemma dirac_connected {G : Graph α β} [G.Simple] [hFinite : G.Finite]
  (hV : 3 ≤ V(G).encard) (hDegree : V(G).encard ≤ 2 * G.minEDegree) :
  G.Connected := by
  have encard_eq_ncard : V(G).encard = ↑V(G).ncard := by
    rw [Set.Finite.cast_ncard_eq]
    exact vertexSet_finite
  have hNeBot : G.NeBot := by
    rw [NeBot_iff_encard_positive]
    enat_to_nat! <;> omega
  simp [← G.natCast_minDegree_eq hNeBot] at hDegree
  rw [encard_eq_ncard] at hV hDegree
  enat_to_nat

  -- Suppose not.
  by_contra! hyp_contra

  -- There thus must be at least two components.
  have num_components_ge_2 : 2 ≤ G.Components.encard :=
    ge_two_components_of_not_connected hNeBot hyp_contra

  have components_nonempty : G.Components.Nonempty := by
    apply nonempty_of_encard_ne_zero
    intro h; rw [h] at num_components_ge_2; clear h
    norm_num at num_components_ge_2

  -- Choose the smallest component.
  obtain ⟨min_comp, min_comp_spec⟩ :=
    Set.Finite.exists_minimalFor
      (fun H => H.vertexSet.ncard)
      G.Components
      (finite_components_of_finite hFinite)
      components_nonempty

  -- There must be at least one other component.
  have ⟨other_comp, other_comp_spec⟩ :
    ∃ H, H.IsCompOf G ∧ H ≠ min_comp := by
    by_contra! hyp_contra
    have is_singleton : G.Components = {min_comp} := by
      exact (Nonempty.subset_singleton_iff components_nonempty).mp hyp_contra
    have : G.Components.encard = 1 := by
      simp [is_singleton]
    rw [this] at num_components_ge_2; clear this
    enat_to_nat; omega

  -- G, min_comp, other_comp have finite vertexSets
  have G_finite_vertexSet : V(G).Finite := vertexSet_finite
  have min_comp_finite : min_comp.Finite := hFinite.mono min_comp_spec.1.le
  have min_comp_finite_vertexSet : V(min_comp).Finite :=
    vertexSet_finite
  have other_comp_finite : other_comp.Finite := hFinite.mono other_comp_spec.1.le
  have other_comp_finite_vertexSet : V(other_comp).Finite :=
    vertexSet_finite

  -- other_comp has at least as many vertices as min_comp
  have other_comp_larger : V(min_comp).ncard ≤ V(other_comp).ncard := by
    refine minimalFor_is_lower_bound (fun H : Graph α β => H.vertexSet.ncard) min_comp_spec ?_ ?_
    simp
    exact other_comp_spec.1
  -- min_comp and other_comp have disjoint vertex sets
  have disjoint_vx_sets : Disjoint V(min_comp) V(other_comp) := by
    suffices StronglyDisjoint min_comp other_comp by
      exact this.vertex
    apply G.components_pairwise_stronglyDisjoint <;> try tauto
    exact min_comp_spec.1

  have G_vertexSet_is_superset : V(min_comp) ∪ V(other_comp) ⊆ V(G) := by
    rw [union_subset_iff]; constructor <;> apply vertexSet_mono
    -- This works: it does exactly what the two following bulleted lines do:
    /-
     · exact min_comp_spec.1.le
     · exact other_comp_spec.1.le
    -/
    -- But it does so without referring to names explicitly.
    run_tacq
      for ldecl in ← getLCtx do
        let hyp := mkIdent ldecl.userName
        let some ty := ← checkTypeQ (← whnf ldecl.type) q(Prop) | continue
        if let ~q($p ∧ $q) := ty then
          evalTactic (← `(tactic| try exact $hyp.1.le))
    -- The type-checking is completely unnecessary, the following code would suffice as well:
    /-
    run_tacq
      for ldecl in ← getLCtx do
        let hyp := mkIdent ldecl.userName
        evalTactic (← `(tactic| try exact $hyp.1.le))
    -/
    -- But the longer example above just shows how one might match on types in
    -- more elaborate scenarios.

  have G_ncard_ge_sum : V(min_comp).ncard + V(other_comp).ncard ≤ V(G).ncard := by
    have : V(min_comp).ncard + V(other_comp).ncard = (V(min_comp) ∪ V(other_comp)).ncard := by
      exact Eq.symm
        (ncard_union_eq disjoint_vx_sets min_comp_finite_vertexSet other_comp_finite_vertexSet)
    rw [this]; clear this
    refine ncard_le_ncard ?_ ?_ <;> assumption

  -- so |min_comp| ≤ n/2
  replace G_ncard_ge_sum : 2 * V(min_comp).ncard ≤ V(G).ncard := by
    linarith

  -- some manipulations left over
  have hle : V(min_comp).ncard ≤ G.minDegree := by linarith
  have hle2 : G.minDegree ≤ min_comp.minDegree := by
    apply minDegree_le_minDegree_of_isCompOf
    rw [←mem_components_iff_isCompOf]
    exact min_comp_spec.1
  replace hle : V(min_comp).ncard ≤ min_comp.minDegree := by linarith
  have hlt : min_comp.minDegree < V(min_comp).ncard := by
    have min_comp_simple : min_comp.Simple := ‹G.Simple›.mono min_comp_spec.1.le
    refine minDegree_lt_ncard ?_
    rw [NeBot_iff_vertexSet_nonempty]
    exact min_comp_spec.1.nonempty

  linarith

/- gist of the proof of the next part:
Goal: there's a cycle which contains the vertices of the longest path (which we will call P)
Proof:
- first, note that each neighbour of P.first must be on P by maximality of P
- symmetrically, each neighbour of P.last must be on P as well
- each neighbour of P.first has an edge of P to its left,
  each neighbour of P.last has an edge of P to its right
- since min degree >= n/2, there are n/2 edges of P with a neighbour of
  of P.first on its right and n/2 edges of P with a neighbour of P.last on its left
- P can only have at most n - 1 edges, so by pigeonhole, there must be at least
  one edge of P with a neighbour of P.last on its left and a neighbour of P.first on
  its right, say x - e - y with (G.Adj P.first x), (G.Adj P.last y)
- so if we let:
  * u := P.first
  * v := P.last
  * P₁ be the prefix u ... x,
  * P₂ be the suffix y ... v,
  then P₁ + xv - P₂ + yu is a cycle containing all of V(P)
-/

lemma dirac_exists_cycle
    [G.Simple] [G.Finite] {P} (hP : G.IsLongestPath P)
    (hNontrivial : 3 ≤ V(G).encard)
    (hDegree : V(G).encard ≤ 2 * G.minEDegree) :
    ∃ C, G.IsCycle C ∧ V(C) = V(P) := by

  -- every max-length path in G must be of length at least 2
  have P_nontrivial : P.Nontrivial :=
    hP.nontrivial_of_connected_of_encard_ge_three
      (dirac_connected hNontrivial hDegree)
      hNontrivial

  -- enat_to_nat away encard → ncard
  have G_nonempty : V(G).Nonempty := by
    rw [←encard_ne_zero]
    enat_to_nat! <;> omega
  have G_nebot : G.NeBot := by
    rwa [NeBot_iff_vertexSet_nonempty]
  have vx_finite : V(G).Finite := vertexSet_finite
  simp [←vx_finite.cast_ncard_eq] at hDegree hNontrivial
  simp [← G.natCast_minDegree_eq G_nebot] at hDegree
  enat_to_nat



  have first_edge (y : {y // G.Adj P.first y}) :
      ∃! e, ∃ x, P.DInc e x y := by
    obtain ⟨y, hy⟩ := y
    have ne_first : y ≠ P.first := hy.ne.symm
    refine IsPath.existsUnique_left_edge hP.isPath ?_ ne_first
    exact G.first_neighbors_mem_path hP _ hy
  have last_edge (x : {x // G.Adj P.last x}) :
      ∃! e, ∃ y, P.DInc e x y := by
    obtain ⟨x, hx⟩ := x
    have ne_last : x ≠ P.last := hx.ne.symm
    refine IsPath.existsUnique_right_edge hP.isPath ?_ ne_last
    exact G.last_neighbors_mem_path hP _ hx
  rw [forall_existsUnique_iff] at first_edge last_edge
  obtain ⟨left_edge, left_edge_spec⟩ := first_edge
  obtain ⟨right_edge, right_edge_spec⟩ := last_edge
  have left_edge_inj : Function.Injective left_edge := by
    intro ⟨y, hy⟩ ⟨y', hy'⟩ heq
    simp
    generalize e_def : left_edge ⟨y, hy⟩ = e
    generalize e'_def : left_edge ⟨y', hy'⟩ = e'
    replace heq : e = e' := (e_def.symm.trans heq).trans e'_def
    rw [←left_edge_spec] at e_def
    obtain ⟨x, hx⟩ := e_def
    rw [← heq, ←left_edge_spec] at e'_def
    obtain ⟨x', hx'⟩ := e'_def
    rw [hP.isPath.isTrail.dInc_iff_eq_of_dInc hx (x := x') (y := y')] at hx'
    tauto
  have right_edge_inj : Function.Injective right_edge := by
    intro ⟨x, hx⟩ ⟨x', hx'⟩ heq
    simp
    generalize e_def : right_edge ⟨x, hx⟩ = e
    generalize e'_def : right_edge ⟨x', hx'⟩ = e'
    replace heq : e = e' := (e_def.symm.trans heq).trans e'_def
    rw [←right_edge_spec] at e_def
    obtain ⟨y, hy⟩ := e_def
    rw [← heq, ←right_edge_spec] at e'_def
    obtain ⟨y', hy'⟩ := e'_def
    rw [hP.isPath.isTrail.dInc_iff_eq_of_dInc hy (x := x') (y := y')] at hy'
    tauto
  have left_edge_range_le : Set.range left_edge ⊆ E(P) := by
    intro e ⟨y, hy⟩
    rw [←left_edge_spec] at hy
    obtain ⟨x, h⟩ := hy
    exact h.edge_mem
  have right_edge_range_le : Set.range right_edge ⊆ E(P) := by
    intro e ⟨x, hx⟩
    rw [←right_edge_spec] at hx
    obtain ⟨y, h⟩ := hx
    exact h.edge_mem
  let equiv_first := G.incAdjEquiv P.first
  let equiv_last := G.incAdjEquiv P.last

  -- there exists some edge which is both a left edge and a right edge
  have ⟨e, he⟩ : (range left_edge ∩ range right_edge).Nonempty := by
    rw [←not_disjoint_iff_nonempty_inter]
    intro h_disj
    have P_edge_finite : E(P).Finite := by
      refine ‹G.Finite›.edgeSet_finite.subset ?_
      exact hP.isPath.isWalk.edgeSet_subset
    have left_edge_range_finite : (range left_edge).Finite :=
      P_edge_finite.subset left_edge_range_le
    have right_edge_range_finite : (range right_edge).Finite :=
      P_edge_finite.subset right_edge_range_le
    have left_edge_range_card : (range left_edge).ncard = G.degree P.first := by
      rw [←Nat.card_coe_set_eq, Nat.card_range_of_injective, Nat.card_congr equiv_first.symm]
        <;> [skip ; assumption]
      change Nat.card {e | G.Inc e P.first} = G.degree P.first
      rw [Nat.card_coe_set_eq]
      exact degree_eq_ncard_inc.symm
    have right_edge_range_card : (range right_edge).ncard = G.degree P.last := by
      rw [←Nat.card_coe_set_eq, Nat.card_range_of_injective, Nat.card_congr equiv_last.symm]
        <;> [skip ; assumption]
      change Nat.card {e | G.Inc e P.last} = G.degree P.last
      rw [Nat.card_coe_set_eq]
      exact degree_eq_ncard_inc.symm
    have sum :
        ((range left_edge) ∪ (range right_edge)).ncard = G.degree P.first + G.degree P.last := by
      rw [ncard_union_eq h_disj left_edge_range_finite right_edge_range_finite]
      rw [left_edge_range_card, right_edge_range_card]
    replace sum : V(G).ncard ≤ (range left_edge ∪ range right_edge).ncard := by
      have le₁ : G.minDegree ≤ G.degree P.first :=
        minDegree_le_degree hP.isPath.isWalk.first_mem
      have le₂ : G.minDegree ≤ G.degree P.last :=
        minDegree_le_degree hP.isPath.isWalk.last_mem
      omega
    have killer₁ : E(P).ncard + 1 ≤ V(G).ncard := by
      have : DecidableEq β := Classical.decEq β
      rw [hP.isPath.isTrail.edge_ncard_eq_length]
      exact hP.isPath.length_le_ncard
    have killer₂ : (range left_edge ∪ range right_edge).ncard ≤ E(P).ncard := by
      refine ncard_le_ncard ?_ P_edge_finite
      simp
      tauto
    omega

  obtain ⟨⟨y, he_left⟩, ⟨x, he_right⟩⟩ := he
  have h_dinc : P.DInc e x y := by
    rw [←left_edge_spec] at he_left
    rw [←right_edge_spec] at he_right
    obtain ⟨x', hx'⟩ := he_left
    obtain ⟨y', hy'⟩ := he_right
    rw [hP.isPath.isTrail.dInc_iff_eq_of_dInc hy' (x := x') (y := y)] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    assumption
  obtain ⟨y, ey, hy⟩ := y
  obtain ⟨x, ex, hx⟩ := x
  simp at h_dinc
  have decEqα := Classical.decEq α
  clear left_edge_spec left_edge_inj left_edge_range_le he_left left_edge
  clear right_edge_spec right_edge_inj right_edge_range_le he_right right_edge
  clear equiv_first equiv_last

  -- Two trivial cases: when ex ∈ P.edge or when ey ∈ P.edge.
  -- In either case, we can directly close the path up.
  obtain (hey|ey_notMem) := Classical.em (ey ∈ P.edge)
  · -- In this case, we must have P.DInc ey P.first y.
    -- But we already know P.DInc e x y, so we must have x = P.first.
    -- Thus, we can directly close up the loop with ex.
    have h_dinc' : P.DInc ey P.first y := by
      have h_isLink' : P.IsLink ey P.first y := by
        simpa [hP.isPath.isWalk.isLink_iff_isLink_of_mem hey]
      rw [isLink_iff_dInc] at h_isLink'
      obtain (h|h) := h_isLink'
        <;> [assumption; exfalso]
      -- this is impossible, can't have P.first as RHS of DInc.
      have := h.ne_first hP.isPath.nodup
      contradiction
    rw [dInc_iff_eq_of_dInc_of_vertex_nodup_right hP.isPath.nodup h_dinc (f := ey) (x := P.first)]
      at h_dinc'
    obtain ⟨rfl, rfl⟩ := h_dinc'
    have hC : G.IsCycle (cons P.last ex P) :=
      hP.isPath.cons_isCycle_of_nontrivial hx.symm P_nontrivial
    refine ⟨cons P.last ex P, hC, ?_⟩
    simp [←hC.isClosed.vertexSet_tail]
  -- ditto for ex ∈ P.edge
  obtain (hex|ex_notMem) := Classical.em (ex ∈ P.edge)
  · have h_dinc' : P.DInc ex x P.last := by
      have h_isLink' : P.IsLink ex P.last x := by
        simpa [hP.isPath.isWalk.isLink_iff_isLink_of_mem hex]
      rw [isLink_iff_dInc] at h_isLink'
      obtain (h|h) := h_isLink'
        <;> [exfalso; assumption]
      have := h.ne_last hP.isPath.nodup
      contradiction
    rw [dInc_iff_eq_of_dInc_of_vertex_nodup_left hP.isPath.nodup h_dinc (f := ex) (y := P.last)]
      at h_dinc'
    obtain ⟨rfl, rfl⟩ := h_dinc'
    have hC : G.IsCycle (cons P.last ey P) :=
      hP.isPath.cons_isCycle_of_nontrivial hy P_nontrivial
    refine ⟨cons P.last ey P, hC, ?_⟩
    simp [←hC.isClosed.vertexSet_tail]

  -- we now do surgery on a grape
  let pref := P.prefixUntilVertex x
  let suff := P.suffixFromVertex y
  have pref_dinc_suff_eq : pref ++ cons x e suff = P := by
    simp only [pref, suff, IsPath.prefixUntilVertex_dInc_suffixFromVertex hP.isPath h_dinc]
  have x_notMem_suff : x ∉ suff := by
    have h_isPath := hP.isPath
    have h_isSuff : (cons x e suff).IsSuffix P := by
      rw [← pref_dinc_suff_eq]
      exact WList.isSuffix_append_left _ _
    apply h_isPath.suffix at h_isSuff
    simp at h_isSuff; tauto

  have h_disj : Disjoint V(pref) V(suff) := by
    by_contra! hcon
    rw [not_disjoint_iff_nonempty_inter] at hcon
    obtain ⟨u, hu_pref, hu_suff⟩ := hcon
    have h_isPath := hP.isPath.reverse
    rw [← pref_dinc_suff_eq, WList.reverse_append] at h_isPath
      <;> [skip ; exact P.prefixUntilVertex_last h_dinc.left_mem]
    rw [reverse_cons] at h_isPath
    have disj := h_isPath.diff_Last_disjoint_of_append
    simp [x_notMem_suff] at disj
    exact disj.notMem_of_mem_right hu_pref hu_suff

  have y_notMem_pref : y ∉ pref := by
    intro h_y_pref
    have h_y_suff : y ∈ suff := by
      simp [suff]; nth_rewrite 2 [←P.suffixFromVertex_first h_dinc.right_mem]
      exact WList.first_mem
    exact h_disj.notMem_of_mem_left h_y_pref h_y_suff
  have notMem_pref_edge_of_notMem_edge {e} (h : e ∉ P.edge) : e ∉ pref.edge := by
    intro bad
    simp [pref] at bad
    have := WList.IsPrefix.mem_edge (P.prefixUntilVertex_isPrefix x) bad
    contradiction
  have notMem_suff_edge_of_notMem_edge {e} (h : e ∉ P.edge) : e ∉ suff.edge := by
    intro bad
    simp [suff] at bad
    have := WList.IsSuffix.mem_edge (P.suffixFromVertex_isSuffix y) bad
    contradiction

  have h₁ : G.IsPath (cons P.first ey suff) := by
    simp
    refine ⟨?_, ?_, ?_⟩
    · refine hP.isPath.suffix (P.suffixFromVertex_isSuffix y)
    · suffices suff.first = y by simpa [this]
      refine suffixFromVertex_first h_dinc.right_mem
    intro bad
    have := IsPath.first_in_suffixFromVertex_iff hP.isPath h_dinc.right_mem
    simp [suff, this] at bad
    exact hy.ne bad
  have h₂ : G.IsPath (pref.reverse ++ (cons P.first ey suff)) := by
    have pref'_isPath : G.IsPath pref.reverse := by
      refine IsPath.reverse ?_
      refine hP.isPath.prefix (P.prefixUntilVertex_isPrefix x)
    refine IsPath.append pref'_isPath h₁ (by simp [pref, suff]) ?_
    intro u hu_pref' hu_cons
    simp at hu_cons
    obtain (h|h) := hu_cons
    · simpa [pref]
    change u ∈ V(suff) at h
    replace hu_pref' : u ∈ V(pref) := by
      rw [WList.mem_reverse] at hu_pref'
      exact hu_pref'
    exfalso
    exact h_disj.notMem_of_mem_left hu_pref' h
  have h₃ : G.IsCycle (cons P.last ex (pref.reverse ++ (cons P.first ey suff))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
      refine ⟨h₂.isTrail, ?_, ?_⟩
      · simpa [pref, P.prefixUntilVertex_last h_dinc.left_mem]
      refine ⟨by tauto, ?_, by tauto⟩
      intro rfl
      suffices : P.first = P.last
      · rw [WList.first_eq_last_iff hP.isPath.nodup] at this
        rw [←WList.length_eq_zero] at this
        rw [←WList.two_le_length_iff] at P_nontrivial
        omega
      obtain (h|h) := hx.eq_and_eq_or_eq_and_eq hy
        <;> [exact h.1.symm; exfalso]
      apply ex_notMem
      rw [←h.2] at hy
      have e_isLink : G.IsLink e x y :=
        hP.isPath.isWalk.isLink_of_isLink h_dinc.isLink
      rw [hy.unique_edge e_isLink]
      exact h_dinc.edge_mem
    · simp
    · simp
      show P.last = suff.last
      simp [suff]
    simp only [tail_cons]
    exact h₂.nodup
  refine ⟨cons P.last ex (pref.reverse ++ cons P.first ey suff), h₃, ?_⟩
  simp [←h₃.isClosed.vertexSet_tail]
  rw [WList.append_vertexSet_of_eq (by simp [pref]),
      WList.reverse_vertexSet]
  nth_rewrite 2 [← pref_dinc_suff_eq]
  rw [WList.append_vertexSet_of_eq]
  swap
  · simp [pref]
    exact P.prefixUntilVertex_last h_dinc.left_mem
  simp
  ext u
  refine ⟨?_, ?_⟩
  · rintro (rfl|hu)
    · right; left
      rw [← P.prefixUntilVertex_first x]
      exact WList.first_mem
    right; assumption
  rintro (hu|hu)
  · symm at hu; obtain rfl := hu
    right; left
    rw [← P.prefixUntilVertex_last h_dinc.left_mem]
    exact WList.last_mem
  right; assumption

lemma dirac_isHamiltonianCycle
    [G.Simple] [G.Finite] {P} (hP : G.IsLongestPath P)
    (hNontrivial : 3 ≤ V(G).encard)
    (hDegree : V(G).encard ≤ 2 * G.minEDegree)
    {C} (hC : G.IsCycle C ∧ V(C) = V(P)) :
    G.IsHamiltonianCycle C := by
  by_contra! hcon
  obtain ⟨hC, hCP⟩ := hC
  simp [IsHamiltonianCycle] at hcon
  simp_all
  have hCG : V(C) ⊆ V(G) := hC.isWalk.vertexSet_subset
  -- replace hcon : C.length < V(G).ncard :
  sorry
