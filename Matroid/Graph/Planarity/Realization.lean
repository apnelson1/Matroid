import Matroid.Graph.Finite
import Matroid.Graph.GraphLike.ArbRel
import Matroid.Graph.Connected.Defs
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected

namespace Graph

variable {α β : Type*} {G : Graph α β}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path WList
open scoped unitInterval

/-!
# Topological realization of a multigraph

The *geometric realization* `Graph.Realization G` is a 1-dimensional space: the discrete 0-skeleton
on `V(G)`, a closed 1-cell `I = Icc 0 1` per edge, and the quotient identifying `0`/`1` with chosen
endpoints of each edge (via `Classical.choice` among the two `IsLink` orientations).

This matches `sk₁` of a relative CW complex with stationary higher skeleta.  Concretely it is the
quotient of `V(G) ⊔ ⨆_{e ∈ E(G)} I`, i.e. (up to canonical homeomorphism) the pushout in `Top` of
`Fin 2 × E(G)` against the disjoint union of 1-disks.

`DiscreteVtx G` is used so the 0-skeleton carries the discrete topology `⊥`, not the subspace
topology from `α`.

If `G` is finite (finitely many vertices and edges), then `PreRealization G` is a finite disjoint
union of compact pieces (finite discrete spaces and copies of `I`), hence compact, and so is the
quotient `Realization G` (`Quotient.compactSpace`).
-/

/-- Vertices of `G` as a type, equipped with the discrete topology (the 0-skeleton). -/
def DiscreteVtx (G : Graph α β) := V(G)

/-- Discrete uniformity (hence discrete topology) on vertices. -/
instance instUniformSpaceDiscreteVtx (G : Graph α β) : UniformSpace (DiscreteVtx G) := ⊥

instance : DiscreteTopology (DiscreteVtx G) := discreteTopology_bot _

def DiscreteEdge (G : Graph α β) := E(G)

instance instUniformSpaceDiscreteEdge (G : Graph α β) : UniformSpace (DiscreteEdge G) := ⊥

instance : DiscreteTopology (DiscreteEdge G) := discreteTopology_bot _

instance instFiniteDiscreteVtx [G.Finite] : Finite (DiscreteVtx G) :=
  Finite.to_subtype G.vertexSet_finite

instance instFiniteDiscreteEdge [G.Finite] : Finite (DiscreteEdge G) :=
  Finite.to_subtype G.edgeSet_finite

noncomputable def DiscreteEdge.src (e : DiscreteEdge G) : DiscreteVtx G :=
  ⟨G.src e.prop, G.src_mem e.prop⟩

noncomputable def DiscreteEdge.tgt (e : DiscreteEdge G) : DiscreteVtx G :=
  ⟨G.tgt e.prop, G.tgt_mem e.prop⟩

/-- Disjoint union of the discrete 0-skeleton and one copy of `EdgeDisk` per edge. -/
def PreRealization (G : Graph α β) : Type _ :=
  DiscreteVtx G ⊕ (DiscreteEdge G × I)

instance instUniformSpacePreRealization (G : Graph α β) : UniformSpace (PreRealization G) :=
  Sum.instUniformSpace

-- /-- The topology induced by the sum uniformity agrees with the disjoint-union topology. -/
-- theorem preRealization_topology_eq_sum (G : Graph α β) :
--     @UniformSpace.toTopologicalSpace (PreRealization G) (instUniformSpacePreRealization G) =
--       @instTopologicalSpaceSum (DiscreteVtx G) (DiscreteEdge G × I) _ _ :=
--   rfl

theorem uniformContinuous_preRealization_inl (G : Graph α β) :
    UniformContinuous (Sum.inl : DiscreteVtx G → PreRealization G) :=
  uniformContinuous_inl

theorem uniformContinuous_preRealization_inr (G : Graph α β) :
    UniformContinuous (Sum.inr : DiscreteEdge G × I → PreRealization G) :=
  uniformContinuous_inr

/-- Gluing relation for a single attachment: each endpoint of `EdgeDisk` is identified with the
corresponding vertex of `G`. -/
def glueRel (G : Graph α β) (x y : PreRealization G) : Prop :=
  (∃ e : E(G), x = Sum.inl (DiscreteEdge.src e) ∧ y = Sum.inr ⟨e, 0⟩) ∨
  (∃ e : E(G), x = Sum.inl (DiscreteEdge.tgt e) ∧ y = Sum.inr ⟨e, 1⟩)

/-- Topological realization: quotient of `PreRealization G` by the equivalence closure of
`glueRel`. -/
def Realization (G : Graph α β) : Type _ :=
  Quotient (EqvGen.setoid (glueRel G))

/-- Inclusion of a vertex into the realization. -/
def vertexMk (v : DiscreteVtx G) : Realization G :=
  Quotient.mk' (s := EqvGen.setoid (glueRel G)) (Sum.inl v)

/-- Inclusion of a point of the `e`-th edge interval into the realization. -/
def edgeMk (e : E(G)) (t : I) : Realization G :=
  Quotient.mk' (s := EqvGen.setoid (glueRel G)) (Sum.inr ⟨e, t⟩)

theorem glueRel_vertex_zero (e : E(G)) :
    EqvGen (glueRel G) (Sum.inl (DiscreteEdge.src e)) (Sum.inr ⟨e, 0⟩) :=
  EqvGen.rel _ _ <| Or.inl ⟨e, rfl, rfl⟩

theorem glueRel_vertex_one (e : E(G)) :
    EqvGen (glueRel G) (Sum.inl (DiscreteEdge.tgt e)) (Sum.inr ⟨e, 1⟩) :=
  EqvGen.rel _ _ <| Or.inr ⟨e, rfl, rfl⟩

theorem realization_eq_edgeMk_zero (e : E(G)) : vertexMk (DiscreteEdge.src e) = edgeMk e 0 :=
  Quotient.sound (glueRel_vertex_zero e)

theorem realization_eq_edgeMk_one (e : E(G)) : vertexMk (DiscreteEdge.tgt e) = edgeMk e 1 :=
  Quotient.sound (glueRel_vertex_one e)

instance : TopologicalSpace (Realization G) :=
  instTopologicalSpaceQuotient

theorem continuous_vertexMk : Continuous (vertexMk (G := G)) :=
  continuous_quotient_mk'.comp continuous_inl

theorem continuous_edgeMk (e : E(G)) : Continuous (fun t : I ↦ edgeMk e t) :=
  continuous_quotient_mk'.comp <| continuous_inr.comp
  <| continuous_prodMk.mpr ⟨continuous_const, continuous_inclusion subset_rfl⟩

/-- The pre-realization is compact when `G` is finite: finite disjoint union of compact spaces.

TC synthesis does not match `def PreRealization` to the `CompactSpace` instance for binary `Sum`;
we spell the disjoint union and reuse `inferInstance` there. -/
instance instCompactSpacePreRealization [G.Finite] : CompactSpace (PreRealization G) :=
  (inferInstance : CompactSpace (DiscreteVtx G ⊕ (DiscreteEdge G × I)))

/-- The topological realization of a finite multigraph is compact (quotient of a compact space). -/
instance instCompactSpaceRealization [G.Finite] : CompactSpace (Realization G) :=
  (inferInstance : CompactSpace (Quotient (EqvGen.setoid (glueRel G))))

theorem realization_isCompact_univ [G.Finite] : IsCompact (univ : Set (Realization G)) :=
  CompactSpace.isCompact_univ

lemma continuous_mul_left_I (t : I) : Continuous (fun s : I => t * s) :=
  Continuous.codRestrict (s := I) ((continuous_const_mul (t : ℝ)).comp continuous_subtype_val)
    fun (s : I) => by
      obtain ⟨t, ht1, ht2⟩ := t
      obtain ⟨s, hs1, hs2⟩ := s
      simp [mul_le_one₀ ht2 hs1 hs2, Left.mul_nonneg ht1 hs1]

/-- Quotient map from the disjoint union `PreRealization G`. -/
def realMk (a : PreRealization G) : Realization G :=
  Quotient.mk' (s := EqvGen.setoid (glueRel G)) a

/-- The canonical path along an edge `e` in the realization, from `src e` to `tgt e`. -/
noncomputable def pathAlongEdge (e : E(G)) :
    Path (vertexMk (DiscreteEdge.src e)) (vertexMk (DiscreteEdge.tgt e)) where
  toContinuousMap := ⟨fun t : I ↦ edgeMk e t, continuous_edgeMk e⟩
  source' := (realization_eq_edgeMk_zero e).symm
  target' := (realization_eq_edgeMk_one e).symm

theorem joined_vertexMk_of_isLink {e : β} {x y : α} (h : G.IsLink e x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  let he := h.edge_mem
  let ed : E(G) := ⟨e, he⟩
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h.eq_and_eq_or_eq_and_eq <| G.isLink_src_tgt he
  · simpa [h1, h2, DiscreteEdge.src, DiscreteEdge.tgt, ed] using
      (show Joined (vertexMk (DiscreteEdge.src ed)) (vertexMk (DiscreteEdge.tgt ed)) from
        ⟨pathAlongEdge ed⟩)
  simpa [h1, h2, DiscreteEdge.src, DiscreteEdge.tgt, ed] using
    (show Joined (vertexMk (DiscreteEdge.tgt ed)) (vertexMk (DiscreteEdge.src ed)) from
      ⟨pathAlongEdge ed |>.symm⟩)

theorem joined_vertexMk_of_isWalk {w : WList α β} (hw : G.IsWalk w) :
    Joined (vertexMk ⟨w.first, hw.first_mem⟩) (vertexMk ⟨w.last, hw.last_mem⟩) := by
  induction hw with
  | @nil x hx => exact Joined.refl _
  | @cons x e w hw' hlink ih => simpa [last_cons] using (joined_vertexMk_of_isLink hlink).trans ih

theorem joined_vertexMk_of_connBetween {x y : α} (h : G.ConnBetween x y) :
    Joined (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact joined_vertexMk_of_isWalk hw

/-- From `src e`, follow the edge only up to parameter `t`. -/
lemma mul_one_I (t : I) : t * (1 : I) = t :=
  Subtype.ext (by simp [mul_one])

noncomputable def pathAlongEdgeTo (e : E(G)) (t : I) :
    Path (vertexMk (DiscreteEdge.src e)) (edgeMk e t) where
  toContinuousMap :=
    ⟨fun s : I ↦ edgeMk e (t * s), (continuous_edgeMk e).comp (continuous_mul_left_I t)⟩
  source' := by simp [realization_eq_edgeMk_zero]
  target' := by simp [mul_one_I t]

theorem joined_vertexMk_edgeMk (e : E(G)) (t : I) :
    Joined (vertexMk (DiscreteEdge.src e)) (edgeMk e t) :=
  ⟨pathAlongEdgeTo e t⟩

theorem joined_vertexMk_realMk_of_preconnected {v0 : α} (hv0 : v0 ∈ V(G)) (hG : G.Preconnected)
    (a : PreRealization G) : Joined (vertexMk ⟨v0, hv0⟩) (realMk a) := by
  cases a with
  | inl v =>
    simpa [realMk] using joined_vertexMk_of_connBetween (hG v0 v hv0 v.prop)
  | inr p =>
    obtain ⟨e, t⟩ := p
    refine (joined_vertexMk_of_connBetween (hG v0 (G.src e.prop) hv0 ?_)).trans ?_
    · exact (G.isLink_src_tgt e.prop).left_mem
    · simpa [realMk, DiscreteEdge.src] using joined_vertexMk_edgeMk e t

theorem pathConnectedSpace_of_connected (h : G.Connected) : PathConnectedSpace (Realization G) := by
  obtain ⟨v0, hv0⟩ := h.nonempty
  refine ⟨⟨vertexMk ⟨v0, hv0⟩⟩, fun x y ↦ ?_⟩
  refine Quotient.inductionOn₂ x y fun a b ↦ ?_
  exact (joined_vertexMk_realMk_of_preconnected hv0 h.pre a).symm.trans
    (joined_vertexMk_realMk_of_preconnected hv0 h.pre b)



end Graph
