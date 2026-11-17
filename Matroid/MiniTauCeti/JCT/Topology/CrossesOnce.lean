module

public import Matroid.MiniTauCeti.JCT.Topology.Crossing

/-!
# A single crossing between two sets

`Set.StraddlesAt T S p` expresses a local crossing of `S` by `T` at `p`.
`Set.CrossesOnce T S` additionally requires exactly one intersection.
The local region is existential, so neither an orientation nor a global side is selected.
-/

@[expose] public section

open Set Topology

variable {X : Type*} [TopologicalSpace X] {S T C : Set X} {p : X}

namespace Set

/-- `T` straddles `S` at `p`: near `p`, `S` is the frontier of a set whose interior and exterior
both contain points of `T` arbitrarily close to `p`. -/
def StraddlesAt (T S : Set X) (p : X) : Prop :=
  ∃ U, frontier U =ᶠ[𝓝 p] S ∧ p ∈ boundaryCrossings T U

namespace StraddlesAt

lemma mem_inter (h : StraddlesAt T S p) : p ∈ T ∩ S := by
  obtain ⟨U, hU, hp⟩ := h
  exact ⟨hp.1.1, hU.self_of_nhds.mp hp.1.2⟩

lemma mem_left (h : StraddlesAt T S p) : p ∈ T := h.mem_inter.1

lemma mem_right (h : StraddlesAt T S p) : p ∈ S := h.mem_inter.2

lemma of_mem_boundaryCrossings {U : Set X} (hfront : frontier U =ᶠ[𝓝 p] S)
    (hp : p ∈ boundaryCrossings T U) : StraddlesAt T S p :=
  ⟨U, hfront, hp⟩

/-- Straddling depends only on the germs of the crossing set and the frontier-like set. -/
lemma congr (h : StraddlesAt T S p) {T' S' : Set X}
    (hT : T =ᶠ[𝓝 p] T') (hS : S =ᶠ[𝓝 p] S') : StraddlesAt T' S' p := by
  obtain ⟨U, hU, hp⟩ := h
  exact of_mem_boundaryCrossings (hU.trans hS)
    ((mem_boundaryCrossings_congr_germs hT Filter.EventuallyEqSet.rfl).mp hp)

/-- A region with the same frontier germ and preconnected local sides detects the straddling. -/
lemma mem_boundaryCrossings (h : StraddlesAt T S p) {V : Set X}
    (hfront : frontier V =ᶠ[𝓝 p] S) (hlocal : PreconnectedSidesAt V p) :
    p ∈ boundaryCrossings T V := by
  obtain ⟨U, hU, hp⟩ := h
  exact mem_boundaryCrossings_of_frontier_eventuallyEq hp (hU.trans hfront.symm) hlocal

end StraddlesAt

/-- `T` meets `S` at exactly one point, where it straddles `S`. Symmetry requires geometric
assumptions on the sets. The crossing point is existential because no point is selected. -/
def CrossesOnce (T S : Set X) : Prop :=
  ∃ p, T ∩ S = {p} ∧ StraddlesAt T S p

lemma crossesOnce_iff : CrossesOnce T S ↔ ∃ p, T ∩ S = {p} ∧ StraddlesAt T S p :=
  Iff.rfl

/-- A single crossing is unique contact together with straddling at every contact point.
The singleton witness records uniqueness without selecting a crossing point. -/
lemma crossesOnce_iff_forall : CrossesOnce T S ↔
    (∃ p, T ∩ S = {p}) ∧ ∀ p ∈ T ∩ S, StraddlesAt T S p := by
  constructor
  · rintro h
    obtain ⟨p, hp, hstr⟩ := crossesOnce_iff.mp h
    refine ⟨⟨p, hp⟩, fun q hq ↦ ?_⟩
    have : q = p := mem_singleton_iff.mp (hp ▸ hq)
    exact this ▸ hstr
  · rintro ⟨⟨p, hp⟩, hstr⟩
    exact crossesOnce_iff.mpr ⟨p, hp, hstr p (hp.symm ▸ mem_singleton p)⟩

namespace CrossesOnce

lemma inter_nonempty (h : CrossesOnce T S) : (T ∩ S).Nonempty := by
  obtain ⟨p, hp⟩ := (crossesOnce_iff_forall.mp h).1
  rw [hp]
  exact singleton_nonempty p

lemma not_disjoint (h : CrossesOnce T S) : ¬ Disjoint T S :=
  not_disjoint_iff_nonempty_inter.mpr h.inter_nonempty

lemma inter_subsingleton (h : CrossesOnce T S) : (T ∩ S).Subsingleton := by
  obtain ⟨p, hp⟩ := (crossesOnce_iff_forall.mp h).1
  rw [hp]
  exact subsingleton_singleton

/-- A specified intersection point straddles the frontier-like set. -/
lemma straddlesAt (h : CrossesOnce T S) (hp : p ∈ T ∩ S) : StraddlesAt T S p :=
  (crossesOnce_iff_forall.mp h).2 p hp

/-- Replacing the second set preserves a single crossing when its intersection and its germ at
that intersection are unchanged. This permits replacing an edge by a containing circuit. -/
lemma congr_right (h : CrossesOnce T S) (hinter : T ∩ C = T ∩ S)
    (hgerm : ∀ p ∈ T ∩ S, S =ᶠ[𝓝 p] C) : CrossesOnce T C := by
  obtain ⟨⟨p, hp⟩, hstr⟩ := crossesOnce_iff_forall.mp h
  apply crossesOnce_iff_forall.mpr
  refine ⟨⟨p, hinter.trans hp⟩, fun q hq ↦ ?_⟩
  have hq' : q ∈ T ∩ S := hinter ▸ hq
  exact (hstr q hq').congr Filter.EventuallyEqSet.rfl (hgerm q hq')

/-- A global region with locally preconnected sides detects exactly the unique intersection
as a crossing. This replaces the arbitrary local region in `CrossesOnce`. -/
lemma boundaryCrossings_eq_inter (h : CrossesOnce T S) {V : Set X}
    (hfront : frontier V = S) (hlocal : ∀ p ∈ T ∩ S, PreconnectedSidesAt V p) :
    boundaryCrossings T V = T ∩ S := by
  apply Subset.antisymm
  · exact fun q hq ↦ ⟨hq.1.1, hfront ▸ hq.1.2⟩
  · intro p hp
    exact (h.straddlesAt hp).mem_boundaryCrossings
      (by rw [hfront]) (hlocal p hp)

end CrossesOnce

end Set
