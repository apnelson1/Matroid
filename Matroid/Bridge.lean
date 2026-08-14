module

public import Matroid.ForMathlib.Partition.Constructor
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Matroid.Connectivity.Connected
public import Matroid.Parallel

@[expose] public section

/-
# C-Bridge and overlapping graph

Let M be a matroid and C be a cycle in M. Then `C-Bridge` is the connected component of `M/C`.
Each `C-Bridge`, B, paritions `C` into series classes of `M ↾ (B ∪ C)`. Let them be `B-segments`.
Two `C-Bridge`s, B1 and B2, `overlap` if there is `B1-segment` and `B2-segment` that covers `C`.
The graph with `C-Bridges` as vertices and adjacency relation of `overlapping` is called
`overlap graph`.

This generalises the notion of `C-Bridge` in graph theory that is used for arguing planarity of
a graph.
-/

namespace Matroid

variable {α : Type*}

instance {M : Matroid α} : Std.Symm M.ConnectedTo where
  symm _ _ := M.connectedTo_comm.mp

instance {M : Matroid α} : IsTrans α M.ConnectedTo where
  trans _ _ _ h1 h2 := ConnectedTo.trans h1 h2

/-- The connected components of a matroid, defined as a partition of its ground set. -/
def components (M : Matroid α) : Partition (Set α) :=
  Partition.ofRel M.ConnectedTo

/-- `B` is a `C`-bridge in `M` if it is a connected component of `M ／ C`. -/
def IsBridge (M : Matroid α) (C B : Set α) : Prop :=
  B ∈ (M ／ C).components

/-- The series classes of `M`. -/
def seriesClasses (M : Matroid α) : Partition (Set α) :=
  M✶.parallelClasses

/-- The `B`-segments of `C` in `M`. Defined as the series classes of `M ↾ (B ∪ C)`
restricted to `C`. -/
def segments (M : Matroid α) (C B : Set α) : Partition (Set α) :=
  (M ↾ (B ∪ C)).seriesClasses.induce C

/-- Two `C`-bridges `B₁` and `B₂` overlap in `M` if there are no `B₁`-segment `S₁`
and `B₂`-segment `S₂` that cover `C`.
(They "avoid" each other if such segments exist; they overlap otherwise). -/
def BridgesOverlap (M : Matroid α) (C B₁ B₂ : Set α) : Prop :=
  ¬ ∃ (S₁ S₂ : Set α), S₁ ∈ M.segments C B₁ ∧ S₂ ∈ M.segments C B₂ ∧ S₁ ∪ S₂ = C

variable {M : Matroid α} {C B B₁ B₂ : Set α}

@[simp] lemma components_supp : M.components.supp = M.E := by
  ext x
  simp only [components, Partition.ofRel_supp, Relation.mem_domain_iff]
  exact ⟨fun ⟨y, hy⟩ ↦ hy.mem_ground_left, fun hx ↦ ⟨x, M.connectedTo_self hx⟩⟩

lemma IsBridge.subset_ground (h : M.IsBridge C B) : B ⊆ (M ／ C).E :=
  Partition.subset_of_mem h |>.trans (by simp)

@[simp] lemma seriesClasses_supp : M.seriesClasses.supp = {e | M✶.IsNonloop e} := by
  change M✶.parallelClasses.supp = _
  rw [parallelClasses_supp]

lemma segments_supp : (M.segments C B).supp ⊆ C := by
  rw [segments, Partition.induce_supp']
  exact Set.inter_subset_left

lemma BridgesOverlap.symm (h : M.BridgesOverlap C B₁ B₂) : M.BridgesOverlap C B₂ B₁ := by
  intro ⟨S₂, S₁, h2, h1, hU⟩
  exact h ⟨S₁, S₂, h1, h2, Set.union_comm S₂ S₁ ▸ hU⟩

/-- The overlap graph of `C`-bridges in `M`. -/
def overlapGraph (M : Matroid α) (C : Set α) : SimpleGraph {B // M.IsBridge C B} where
  Adj B₁ B₂ := M.BridgesOverlap C B₁.val B₂.val ∧ B₁ ≠ B₂
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h ↦ h.2 rfl⟩

end Matroid
