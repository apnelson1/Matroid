import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.CWComplex.Classical.Graph
import Matroid.Graph.Planarity.Realization.CWComplex
import Matroid.Graph.Planarity.Topology.Circuit
import Matroid.Graphic
import Matroid.ForMathlib.Analysis.Normed.Module.Connected


open Metric Set Graph Topology.RelCWComplex Topology.CWComplex Function Set.Notation

namespace Graph

variable {α β : Type*} {G : Graph α β}

structure Embedding (G : Graph α β) (E : Type*) [TopologicalSpace E] : Type _ where
  toFun : G.Realization → E
  embedding : Topology.IsEmbedding toFun

namespace Embedding

variable {E : Type*} [TopologicalSpace E] {φ : Embedding G E}

instance : FunLike (Embedding G E) G.Realization E where
  coe := Embedding.toFun
  coe_injective' φ₁ φ₂ h := by cases φ₁; cases φ₂; simpa

@[reducible]
def Faces (φ : Embedding G E) := ConnectedComponents ↑((range φ.toFun)ᶜ)

def FaceMk (f : Faces φ) : Set E := Subtype.val '' ConnectedComponents.mk ⁻¹' {f}

lemma faceMk_nonempty (f : Faces φ) : (FaceMk f).Nonempty := by
  simp only [FaceMk, ConnectedComponents.mk, image_nonempty]
  exact Quotient.mk''_surjective.nonempty_preimage.mpr <| singleton_nonempty f

lemma faceMk_disjoint_range (f : Faces φ) : Disjoint (FaceMk f) (range φ.toFun) := by
  simp only [FaceMk, ConnectedComponents.mk]
  rw [disjoint_iff_forall_notMem]
  rintro _ ⟨x, _, rfl⟩
  exact x.prop

lemma faceMk_eq_connectedComponentIn (f : Faces φ) (x : E)
    (hx : x ∈ FaceMk f) : FaceMk f = connectedComponentIn (range φ.toFun)ᶜ x := by
  have hxran : x ∉ range φ.toFun := (φ.faceMk_disjoint_range f).subset_compl_right hx
  simp only [FaceMk, mem_image, mem_preimage, mem_singleton_iff, Subtype.exists, mem_compl_iff,
    mem_range, not_exists, exists_and_right, exists_eq_right] at hx ⊢
  obtain ⟨_, rfl⟩ := hx
  ext y
  rw [connectedComponentIn_eq_image hxran]
  simp [← connectedComponent_eq_iff_mem, ConnectedComponents.coe_eq_coe]

-- lemma homeomorphism_faceMk (f : Faces φ) : Nonempty (FaceMk f ≃ₜ ball (0 : ℂ) 1) := by
--   obtain ⟨x, hx⟩ := φ.faceMk_nonempty f
--   obtain h := φ.cellular x <| (φ.faceMk_disjoint_range f).subset_compl_right hx
--   rwa [← φ.faceMk_eq_connectedComponentIn f x hx] at h

def drawing (φ : Embedding G E) : Set E := range φ.toFun

lemma vertexMK_mem_drawing (v : V(G)) : φ (vertexMk v) ∈ drawing φ := by
  use vertexMk v
  rfl

lemma edge_subset_drawing (e : E(G)) : range (φ ∘ edgePath e) ⊆ drawing φ := by
  rintro x ⟨t, ht, rfl⟩
  use (edgePath e) t
  rfl

end Embedding

/- Plan: no K3,3 or K5 minor ↔ combinatorial map & euler's formula ↔ integer embedding.
  Let `Minor` be the proposition that a graph has no K3,3 or K5 minor.
  Let `Comb` be the proposition that a graph has a combinatorial map satisfying the euler's formula.
  Let `Int` be the proposition that a graph has an integer embedding.
i) Operations that preserve `Comb`
  - Adding a chord edge to a face
  - Contraction (glue two vertex permutations together)
  - Deletion of an edge (dual operation)
  - Deletion of a vertex (delete darts and skip them)
ii) Dual graph given a combinatorial map satisfying the euler's formula
  - Euler's formula + handshake lemma + faceshake lemma → K3,3 & K5 does not have `Comb`.
iii) If a graph G is 3-connected, `Minor` → `Comb`.
  1. If G is 3-connected, there is an edge, e, that can be contracted to a 3-connected graph.
  2. By IH, G / e has a combinatorial map satisfying the euler's formula.
  3. `Minor` → the facial cycle bounding supervertex {u, v} in (G / e - {u, v}) can
    be divded to two halves, one half containing all neighbors of u in G and the other half
    containing all neighbors of v in G.
  4. extend the map s.t. permutations on u and v are given by the cyclic order of the facial cycle
    and face orbits that used to include the supervertex {u, v} now contain u and v via dart between
    them.
  5. The extended map satisfies the euler's formula as we added one edge and one vertex. Hence, G
    has a combinatorial map satisfying the euler's formula XOR G has K33 or K5 minor.
iv) In general, `Minor` → `Comb`.
  1.
v) Schnyder Wood
  - Choose an arbitrary ordering of the vertices of the graph.
  -
-/

-- /- TODO:
-- 1. Adding a chord edge on a non-outer face of a convex embedding is a convex embedding.
-- 2. Subdividing an edge of a convex embedding is a convex embedding.
-- 3. Apexing a face of a convex embedding is a convex embedding.
-- 3. If simplification of a graph has a convex embedding, then the original graph has an embedding.
--   - Adding a loop to a vertex of an embedding is an embedding.
--   - Adding a parallel edge to an embedding is an embedding.

-- Goal: If a simple graph G has no K3,3 or K5 minor, then there is a convex embedding of G.
-- 1. If G has no K3,3 or K5 minor, then the simplification of G has no K3,3 or K5 minor.
-- 2. Edge maxmal simple graph s.t. it has no K3,3 or K5 minor is 3-connected.
-- 3. 3-connected graph has an edge, e, that can be contracted to a 3-connected graph. (done)
-- 4. By IH, G / e has a convex embedding.
-- 5. The facial cycle bounding supervertex {u, v} in (G / e - {u, v}) can be divded to two halves,
--   one half containing all neighbors of u in G and the other half containing all neighbors of v in
--   G.
-- 6. All neighbors of u in G are in the same facial cycle in G - u.
-- 7. Add u back in by apexing the face containing u. -/
