# Graph Theory Formalization

This folder (`Matroid/Graph/`) contains a substantial formalization of graph theory in Lean,
developed as part of the Matroid project. It builds on `Mathlib.Combinatorics.Graph` with
definitions and results tailored for matroid-theoretic applications, though many are
self-contained graph theory contributions.

The overarching goal is to formalize the connection between graphs and matroids (graphic
matroids, gammoids, etc.) and to provide the graph-theoretic infrastructure needed for
advanced matroid theory, including planarity, connectivity, and matching theory.

> **A note on file structure.** Many concepts here are split across multiple files. This
> is a deliberate trade-off: a wide, shallow import tree improves parallel compilation
> and gives a more responsive coding experience in Lean. As a consequence, conceptually
> related material (e.g. vertex-connectivity vs. set-connectivity) often lives in
> different files. The main body of this document is therefore organized **concept-first**,
> with file:line references for each entry. A short directory map at the bottom orients
> readers by file.

---

## Walks, trails, paths, cycles

The walk machinery is built on a custom inductive type `WList α β` (lists of vertices
alternating with edges) that is more convenient than `Mathlib`'s walk structure for
the proofs in this project.

### `WList` (underlying walk-with-edges list)

**Definition:** `WList` — inductive type of vertex/edge lists
(`Matroid/Graph/WList/Defs.lean:20`).

**Core accessors:** `first`, `second`, `last`, `vertex`, `edge`, `length`
(`WList/Defs.lean`).

**Predicates:** `Nil` (inductive), `Nonempty`, `Nontrivial`, `Inc`, `WellFormed`
(`WList/Defs.lean`); `IsClosed` (`WList/Cycle.lean:11`), `NoLoop`
(`WList/TakeDrop.lean:1806`).

**Operations on lists:**
- `append`, `concat`, `reverse`, `map`, `edgeMap`
  (`WList/Ops.lean`).
- `prefixUntil` / `prefixUntilVertex` / `prefixUntilLast`
  (`WList/TakeDrop.lean`).
- `suffixFrom` / `suffixFromVertex` / `suffixFromLast`
  (`WList/TakeDrop.lean`).
- `tail`, `dropLast`, `take`, `drop`
  (`WList/TakeDrop.lean`).
- `dedup`, `deloop`
  (`WList/TakeDrop.lean`).
- `breakAt`, `breakAt_aux`, `betweenSets`
  (`WList/Decompose.lean`).
- `edgeRemove`
  (`WList/TakeDrop.lean:1895`).
- `intRotate`
  (`WList/Cycle.lean:460`).

**Sublist/prefix/suffix relations:** `IsSublist`, `IsPrefix`, `IsSuffix`, `IsInfix`,
`appendList`, `DecomposeTo` (`WList/Sublist.lean`).

**Alternative representation:** `TsiLw` with `TsiLw_equiv : TsiLw α β ≃ WList α β`
(`WList/Ops.lean:50`).

**Dart-related accessors:** `dIncFirst`, `dIncLast`, `endsOf` (`WList/Defs.lean`,
`WList/Ops.lean`).

### Walk predicates (on `Graph`)

- `IsWalk` — inductive predicate that a `WList` is a valid walk
  (`Walk/Basic.lean:16`).
- `IsWalkFrom` — a walk from set `S` to set `T` (`Walk/Basic.lean:392`).
- `IsTrail` — a walk with no repeated edge (`Walk/Path.lean:15`).
- `IsTour` — a closed trail (`Walk/Cycle.lean:41`).
- `IsCyclicWalk` — a closed trail with no repeated vertex (i.e. a "cycle walk")
  (`Walk/Cycle.lean:49`).
- `IsPath` — a walk with no repeated vertex (`Walk/Path.lean:131`).
- `IsTrailFrom`, `IsPathFrom` — versions between sets
  (`Walk/Path.lean:366`, `:370`).
- `IsCycle` (defined in `Forest.lean`) — a graph whose `IsCyclicWalk` structure is minimal.

**Key walk lemmas:**
- `IsWalk.connBetween_first_last` — first/last vertices are connected.
- `IsWalk.dedup_isPath` — `dedup` of a walk is a path.
- `IsPath.toGraph_simple` (`Simple.lean`) — the underlying graph of a path is simple.
- `IsCyclicWalk.exists_isPath_toGraph_eq_delete_vertex` and `_delete_edge`
  (`Walk/Cycle.lean`) — every cyclic walk has an underlying cycle.

---

## Connectivity

A key design choice is to separate vertex-, edge-, and set-level connectivity into
distinct (parallelizable) files.

### Core predicates (graph-level)

- `Preconnected` — every pair of vertices is joined by a walk (`Connected/Defs.lean`).
- `Connected` — preconnected with nonempty vertex set (`Connected/Defs.lean`).

**Core equivalences:** `connected_iff`, `preconnected_iff` (`Connected/Defs.lean`).

### Components and partitions

- `IsCompOf` — a connected component of `G` (`Subgraph/Basic.lean:304`).
- `walkable` — the connected component containing a vertex (`Connected/Component.lean`).
- `Components` — the family of all components (`Connected/Component.lean`).
- `compPartition`, `connPartition` — partitions of vertex/edge sets by components
  (`Connected/Component.lean`, `Lattice.lean`).
- `NumberOfComponents` (`c(G)`) — cardinality of the components
  (`Connected/Component.lean`, `Lattice.lean`).

**Key lemmas:**
- `walkable_isCompOf` — every walkable component is a connected component.
- `isCompOf_iff_exists_walkable` — components are exactly the walkables.
- `components_pairwise_stronglyDisjoint`, `eq_sUnion_components` — components partition `G`.
- `IsCompOf.stronglyDisjoint_of_ne` (`Lattice.lean`) — distinct components are strongly disjoint.

### Connectivity between vertices

- `ConnBetween` — `u` is connected to `v` (`Connected/Vertex/Defs.lean`).
- `IsSepBetween` — a set separating `u` from `v` (`Connected/Vertex/Defs.lean`).
- `IsEdgeCutBetween` — an edge set separating `u` from `v` (`Connected/Vertex/Defs.lean`).
- `ConnBetweenGE`, `EdgeConnBetweenGE` — at least `n` internally disjoint / edge-disjoint
  `u`–`v` paths (`Connected/Vertex/Defs.lean`).
- `connectivityBetween`, `edgeConnectivityBetween` — the maximum `n`
  (`Connected/Vertex/Defs.lean`).

**Path ensembles:**
- `PathEnsemble` (`Connected/Vertex/Defs.lean`).
- `VertexEnsemble` (`Connected/Vertex/Defs.lean`).
- `EdgePathEnsemble` (`Connected/Vertex/Defs.lean`).
- `VertexEnsemble.ofSetEnsemble`, `VertexEnsemble.extend_singleEdge`
  (`Connected/Vertex/VertexEnsemble.lean`).

**Key lemma:** `ConnBetween.exists_isPath` — connection implies a path.

### Set connectivity

- `SetConnected` — `S` is connected to `T` (`Connected/Set/Defs.lean`).
- `IsSetCut`, `IsEdgeSetCut` — set-level separators (`Connected/Set/Defs.lean`).
- `SetEnsemble` — a family of `S`–`T` paths (`Connected/Set/Defs.lean`).
- `SetConnGE`, `EdgeSetConnGE` — at least `n` disjoint paths/sets
  (`Connected/Set/Defs.lean`).
- `setConnectivity`, `edgeSetConnectivity` (`Connected/Set/Defs.lean`).

**Auxiliary:** `IsRightLeg`, `shorten` (`Connected/Set/Leg.lean`);
`path_insert`, `path_remove`, `extend_right`, `extend_right_two`,
`extend_right_le_two` (`Connected/Set/SetEnsemble.lean`).

### Graph-level connectivity functions

- `connectivity`, `preconnectivity`, `edgeConnectivity` — global minimum connectivity
  (`Connected/Defs.lean`).
- `sepConnectivity` (`Connected/Basic.lean`).
- `ConnGE`, `PreconnGE`, `EdgeConnGE` — `n`-connected / `n`-edge-connected
  (`Connected/Defs.lean`).
- `PreconnGE.contract_isLink` (`Connected/Minor.lean`).

**Boundary lemmas:**
- `connGE_one_iff` (↔ Connected), `preconnGE_one_iff` (↔ Preconnected)
  (`Connected/Defs.lean`).
- `connBetweenGE_one_iff` (↔ ConnBetween), `setConnGE_one_iff` (↔ SetConnected).

### Bridges, bonds, edge cuts

- `IsBridge` (`Connected/Bond.lean`) — an edge whose deletion disconnects its endpoints.
- `IsEdgeCut` (`Connected/Bond.lean`) — a set of edges separating two sides.
- `IsBond` (`Connected/Bond.lean`) — a minimal nonempty edge cut.

**Key lemmas:**
- `IsLink.isBridge_iff_not_connBetween` — `e` is a bridge iff its endpoints are not
  connected after deleting `e`.
- `IsPath.isBridge_of_mem` — an edge of a path (not a cycle) is a bridge.
- `IsCyclicWalk.not_isBridge_of_mem` — an edge of a cycle is not a bridge.
- `exists_isCyclicWalk_of_not_isBridge` — if `e` is not a bridge, some cycle contains it.
- `IsBond.exists_minimal_not_connBetween` — bonds detect disconnection.
- `EdgeConnGE.minDegreeGE` — edge-connectivity ≤ min degree.

### Connectivity under minors and contractions

- `ConnBetween.map`, `Connected.map` (`Connected/Minor.lean`).
- `IsSep.of_map`, `IsSep.of_contract` (`Connected/Minor.lean`).
- `contract_connBetween_iff`, `contract_connected_iff`, `contract_preconnected_iff`,
  `contract_isBridge_iff` (`Minor/Conn.lean`).
- `exists_contract_connGE_three` — 3-connected graphs admit an edge whose contraction
  stays 3-connected (`Connected/Minor.lean`).

### Named connectivity theorems

- **`Menger'sTheorem_set`** — set-connectivity ≥ `n` ⟺ `n` disjoint `S`–`T` paths
  (`Connected/Menger.lean:204`).
- **`Menger'sTheorem_vertex`** — vertex-connectivity ≥ `n` ⟺ `n` internally disjoint
  `s`–`t` paths (`Connected/Menger.lean:232`).
- **`Menger'sTheorem_edge`** — edge-connectivity ≥ `n` ⟺ `n` edge-disjoint `s`–`t` paths
  (`Connected/Menger.lean:428`).
- **`Menger'sTheorem_mixed`** — mixed vertex/edge version via the mixed line graph
  (`Connected/Menger.lean:345`).
- **`Menger'sTheoremPre`**, **`Menger'sTheorem_aux`** — auxiliary statements
  (`Connected/Menger.lean`).

**Menger infrastructure:**
- `mixedLineGraph_walkMap`, `WalkOfMixedLineGraph`, `mixedLineEnsembleMap`,
  `mixedLineOfEnsembleMap` (`Connected/MixedLineGraph.lean`).
- `EdgePathEnsemble.ofLineGraphSetEnsemblePaths` (`Connected/Menger.lean`).
- `lineGraph_setConnected_incEdges_iff`, `isEdgeCutBetween_iff_lineGraph_isSetCut`,
  `edgeConnBetweenGE_iff_lineGraph_setConnGE` (`Connected/LineGraph.lean`).

### Vertex-cut lemmas (walks and closed subgraphs)

- `IsWalk.isWalk_or_isWalk_compl_of_closedSubgraph` — a walk in `G` splits into walks in
  a closed subgraph and its complement (`Connected/Vertex/Basic.lean`).
- `IsWalk.prefixUntil_isWalk_subgraph` — prefix of a walk in a subgraph stays there.
- `IsSep.prefixUntil_isWalk_deleteVerts` (`Connected/Set/Defs.lean`).

---

## Trees, forests, cycles

- `IsAcyclicSet` — a set of edges containing no cycle (`AcyclicSet.lean`).
- `IsCycleSet` — the edge set of a cycle (`AcyclicSet.lean`).
- `IsMaximalAcyclicSet` (`AcyclicSet.lean`).
- `IsForest` — a graph whose edge set is acyclic (`Forest.lean`).
- `IsCycle` — a connected 2-regular graph with a cyclic walk
  (defined in `Forest.lean`; walks `IsCyclicWalk` are in `Walk/Cycle.lean`).
- `IsTree` — a connected forest (`Forest.lean`).

**Key properties:**
- `IsCycle.regular_two` — every cycle is 2-regular (`Forest.lean:226`).
- `IsCycle.connected` — every cycle is connected (`Forest.lean`).
- `IsForest.anti` — subgraph of a forest is a forest.
- `IsForest.exists_isPendant` — a finite forest with an edge has a pendant vertex.
- `IsForest.bipartite` — forests are bipartite (`Forest.lean` and `Bipartite.lean`).
- `IsTree.encard_vertexSet` (|V| = |E| + 1), `IsForest.encard_vertexSet`
  (`Forest.lean`).
- `Connected.exists_isTree_spanningSubgraph` — every connected graph has a spanning tree
  (`Tree.lean:31`).
- `Connected.encard_vertexSet_le` — |V| ≤ |E| + 1 when connected (`Tree.lean`).

**Named theorem:**
- **`twoPaths`** — two distinct paths with the same ends contain a cycle
  (`Forest.lean:12`). (Also used in the graphic matroid's circuit elimination,
  `Matroid/Graphic.lean`.)

**Auxiliary AcyclicSet lemmas:**
- `isCycleSet_singleton_iff` — a singleton is a cycle set iff it is a parallel pair (or empty).
- `isCycleSet_pair_iff_parallel` — a pair is a cycle set iff the two edges are parallel.
- `restrict_isForest_iff` — restricting to an edge set gives a forest iff it is acyclic.
- `IsAcyclicSet.isBridge` — in an acyclic set every edge is a bridge.
- `IsMaximalAcyclicSet.connBetween_iff` — endpoints are connected iff the edge is in a
  maximal acyclic set.

---

## Cycles and bridges — `Degree/Max.lean`

**Named result:** `Connected.isPathGraph_or_isCycle_of_maxDegreeLE` — a finite connected
graph with max degree ≤ 2 is either a path or a cycle (`Degree/Max.lean:106`).

Other entries:
- `IsPathGraph` (`Degree/Max.lean`).
- `Connected.isCycle_of_regular` — 2-regular connected graphs are cycles.
- `Connected.exists_isPath_of_leaves` — connected max-degree-≤-2 graphs have a
  leaf-to-leaf path.

---

## Degree

- `incFun` — incidence function as a `Finsupp` (`Degree/Basic.lean`).
- `eDegree` (ℕ∞) and `degree` (ℕ) — extended/natural degree (`Degree/Basic.lean`).
- `DegreePos`, `MaxDegreeLE`, `MinDegreeGE`, `Regular`
  (`Degree/Defs.lean`).
- `eDegree_eq_encard_inc` (loopless case) and `eDegree_eq_encard_adj` (simple case)
  (`Degree/Basic.lean`).
- `Regular.encard_edgeSet`, `Regular.ncard_edgeSet` (`Degree/Defs.lean`).

**Named theorem:**
- **`handshake_eDegree`** — ∑ eDegree(v) = 2 · |E(G)| (`Degree/Basic.lean:281`).
- **`handshake_degree_subtype`** — finite version (`Degree/Basic.lean`).

**Other key lemmas:**
- `degree_mono`, `eDegree_addEdge_left`/`_right` (`Degree/Basic.lean`, `Degree/Constructions.lean`).
- `IsNonloopAt.eDegree_delete_add_one`, `IsLoopAt.eDegree_delete_add_two`.
- `IsPath.eDegree_toGraph_eq_two`, `IsCyclicWalk.toGraph_regular`.

### Leaves and isolated vertices

- `Isolated` (structure), `IsolatedSet` (`Basic.lean`).
- `IsPendant`, `IsLeaf`, `IsLeafEdge` (`Basic.lean`, `Degree/Leaf.lean`).
- `isolated_iff_eDegree`, `isolated_iff_degree` (`Degree/Leaf.lean`).
- `eDegree_eq_one_iff` (↔ IsLeaf), `degree_eq_one_iff` (↔ IsLeaf) (`Degree/Leaf.lean`).
- `Inc.isPendant_of_eDegree_le_one` (`Degree/Leaf.lean`).
- `IsTrail.eq_first_or_last_of_degree_eq_one`, `IsTrail.disjoint_of_degree_le_one`.

---

## Subgraphs

### Operations and basic notions

- `restrict`, `deleteEdges`, `induce`, `deleteVerts` (`Subgraph/Defs.lean`).
- `union`, `inter`, `iUnion`, `sUnion` on graphs (`Subgraph/Defs.lean`).
- `IsInducedSubgraph`, `IsSpanningSubgraph`, `IsClosedSubgraph`, `IsEdgeSep`
  (`Subgraph/Basic.lean`).

**Compatibility:**
- `Compatible` (relation) and its compatibility with `union`/`inter`/`iUnion`
  (`Subgraph/Compatible.lean`).
- `Compatible.union_isLink_iff`, `Compatible.union_inc_iff`.

**Key lemmas:**
- `IsClosedSubgraph.isLink_congr`, `IsClosedSubgraph.adj_of_adj_of_mem`.
- `IsSpanningSubgraph.edgeSet_eq`.
- `sInter_isClosedSubgraph` — `sInter` of closed subgraphs is closed.

### Lattice of subgraphs

- `Subgraph` — the type of all subgraphs of `G` (`Lattice.lean`).
- `ClosedSubgraph` (`Lattice.lean`).
- `NumberOfComponents` `c(G)` (`Lattice.lean`).

**Algebraic structure:** subgraphs form a `CompleteLattice` and
`CompletelyDistribLattice`; closed subgraphs form a `CompleteBooleanAlgebra` and
`CompleteAtomicBooleanAlgebra` (`Lattice.lean`).

**Key characterizations:**
- `ClosedSubgraph.isAtom_iff_isCompOf` — atoms of closed-subgraph lattice are the
  connected components.
- `ClosedSubgraph.compl_vertexSet`, `ClosedSubgraph.compl_edgeSet`,
  `ClosedSubgraph.inf_compl_eq_bot_iff`.

---

## Minors

### Definitions

- `contract` (edge-set contraction with merging map) (`Minor/Defs.lean:70`).
- `IsLink.contract` (single-edge contraction) (`Minor/Defs.lean:308`).
- `minorMap` (structure for `G ≤_m H` via partition/identification)
  (`Minor/Defs.lean:459`).
- `IsMinor` (`Minor/Defs.lean`).
- `sContract` (`Minor/Defs.lean:439`).
- `IsPartitionGraph` (class) (`Minor/Defs.lean:414`).

**Also in `GraphLike/Contract.lean`:** an abstract `contract` operation for
`GraphLike` structures, and `Partition.IsRepFun.isContractClosed`.

### Key lemmas

- `contract_eq_map_of_disjoint`, `IsLink.contract_eq_map_deleteEdges`.
- `IsLink.isRepFun` (`Minor/Defs.lean:236`).
- `minorMap.vertexSet_intermediate`, `minorMap.edgeSet_intermediate`,
  `minorMap.eq_contract_of_intermediate`.
- `nonempty_minorMap_iff_exists_le_contract` — `G ≤_m H` iff `H` dominates some
  contraction of `G`.
- `IsMinor.refl`, `isMinor_of_contract`, `IsMinor.trans`.
- `contract_contract`, `contract_restrict_comm`, `contract_deleteEdges_comm`.
- `IsWalk.edgeRemove_contract`, `IsTrail.edgeRemove_contract`,
  `IsTour.edgeRemove_contract` (`GraphLike/Contract.lean`).
- `IsWalk.uncontract`, `IsPath.uncontract_isPath`, `IsCyclicWalk.exists_isCyclicWalk_of_contract`
  (`Minor/Conn.lean`).

---

## Matching

### Definitions

- `IsMatching` — a set of vertex-disjoint edges (`Matching/Defs.lean`).
- `IsMaxMatching` — no matching strictly contains it (`Matching/Defs.lean`).
- `matchingNumber` (ν(G)) — size of a maximum matching (`Matching/Defs.lean`).
- `IsCover`, `IsMinCover`, `coverNumber` (τ(G)) — vertex covers
  (`Matching/Defs.lean`).
- `IsMatchable` — a set of vertices covered by some matching (`Matching/Defs.lean`).
- `IsPathGraph` — finite connected max-degree-≤-2 graph (`Matching/Defs.lean`,
  `Degree/Max.lean`).
- `Inessential`, `IsOddCompOf`, `oddComponents` — odd-component machinery for
  Tutte-Berge (`Matching/Defs.lean`).
- `IsAugmenter`, `IsNonleafEdge` — augmenting-path machinery for Berge
  (`Matching/Berge.lean`).

**Auxiliary for König:** `pathCover`, `pathMatching` (`Matching/Konigs.lean`).

**For the matching matroid:** `matchingIndepMatroid`, `matchingMatroid`
(`Matching/TutteBerge.lean`).

### Named theorems

- **`berge`** — `¬ IsMaxMatching M ↔ ∃ P, IsAugmenter M P` (Berge's theorem,
  `Matching/Berge.lean:552`).
- **`Konig'sTheorem`** — for `[H.Simple] [H.Finite] (hB : H.Bipartite)`:
  `τ(H) = ν(H)` (König's theorem, `Matching/Konigs.lean:455`). Also proven for path
  graphs and cycles: `IsPathGraph.konig`, `IsCycle.konig`.
- **`tutte_berge`** — `ν(G) = (|V| - max_{Z ⊆ V} (odd(G - Z) - |Z|)) / 2` (Tutte-Berge
  formula, `Matching/TutteBerge.lean:218`, currently a sketch).
- **`tutte_berge_le`**, **`tutte_berge_of_maximal_deleteVerts`** — bounding statements.

### Key supporting lemmas

- `matchingNumber_le_coverNumber` — ν(G) ≤ τ(G) (always).
- `IsMatching.existsUnique_covering_edge`.
- `IsMatching.union`, `IsCover.union`, `IsMaxMatching.union`.
- `matchingNumber_union`, `coverNumber_union`.
- `IsPathGraph.setOf_isLeaf_eq`, `IsPathGraph.eDegree_eq_one_or_two`.
- `IsAugmenter.symmDiff_matching_isMatching` — augmentation enlarges the matching.
- `IsMaxMatching.not_isAugmenter` — max matchings admit no augmenting path.
- `exists_isAugmenter_of_matching_encard_lt`.

---

## Planarity

### Top-level definitions and Euler

- `matroidalDual` — `G.cycleMatroid* = H.cycleMatroid` (planar dual definition,
  `Planarity/Defs.lean`).

**Named theorems:**
- **`euler_formula`** — |V(G)| + |V(H)| = |E(G)| + c(G) + c(H) for dual pairs
  (`Planarity/Defs.lean:67`).
- **`euler_formula_of_connected`** — |V(G)| + |V(H)| = |E(G)| + 2 for connected dual
  pairs.

### K₃,₃ non-planarity

- `Sym2Set`, `CompletePartite`, `IsPartite`, `IsCompletePartite` (`Planarity/K33.lean`)
  — the setup for showing that K₃,₃ is non-planar.

### Drawings, combinatorial maps, and topological realization

- `Drawing.lean` — plane drawings.
- `CombinatorialMap`, `faceCycles` (`Planarity/CombMap/Basic.lean`).
- `finiteOrbit`, `skip`, `keep` on permutations (`Planarity/CombMap/Equiv.lean`).
- `CycleList/Basic.lean` — cycle lists.
- `GraphContinuum/Basic.lean` — graph-as-continuum representation.
- `Realization/` — topological realization of graphs in the plane
  (`Basic`, `Celluar`, `CWComplex`, `Metric`, `Subgraph`).
- `CWComplex/DualGraph.lean` — dual graph of a CW complex.

### Topology

- `Topology/Curve.lean` — curves in the plane.
- `Topology/Circle.lean` — the Jordan circle.
- `Topology/Plane.lean` — plane topology basics.
- `Topology/Path.lean` — paths in the plane.
- `Topology/PolygonalPath.lean` — polygonal approximations.
- `Topology/Circuit.lean` — circuits in the plane.
- `Topology/ConnPartition.lean` — connectedness partitions of the plane.
- `Topology/JCT.lean` — Jordan Curve Theorem (in the formalization).

---

## Constructions

Standard named graphs as definitions:

- `noEdge`, `singleEdge` (`Constructions/Basic.lean`).
- `banana`, `bouquet` (`Constructions/Basic.lean`).
- `CompleteGraph`, `CompleteBipartiteGraph` (`Constructions/Basic.lean`).
- `StarGraph` (`Constructions/Basic.lean`).
- `LineGraph` (`L(G)`), `mixedLineGraph` (`L'(G)`) (`Constructions/Basic.lean`).
- `OfSimpleGraph`, `fromList` (`Constructions/Basic.lean`).
- `randomGraph` (`Constructions/Random.lean`) — random simple graph on ℕ; instance
  `Simple`.

**Predicates on constructions:**
- `IsComplete` (`Constructions/Basic.lean`).
- `Regular` (`d-regular`, `Constructions/Basic.lean`).

**Key lemmas:**
- `CompleteGraph_isComplete`, `bouquet_isComplete`, `banana_isComplete`,
  `lineGraph_bouquet_isComplete`.
- `IsComplete.VertexEnsemble`, `IsComplete.edgeConnGE`, `completeGraph_edgeConnGE_iff`.
- `noEdge_connBetweenGE_iff`, `singleEdge_connGE`, `banana_connGE_iff`.
- `randomGraph` is `Simple`.

---

## Maps, homomorphisms, isomorphisms

### Vertex/edge relabeling

- `Graph.map` (vertex relabeling), `Graph.edgeMap` (edge relabeling) (`Map.lean`).
- `Graph.ofPFun`, `edgePreimg` (`Map.lean`).
- `IsContractClosed` (`Map.lean`).

**Key lemmas:**
- `map_union`, `map_restrict_comm`, `map_deleteEdges_comm`.
- `IsWalk.map`, `IsCyclicWalk.map`.
- `exists_map_eq_of_le_map`.

### Homomorphisms

- `Hom`, `Emb`, `Iso` (structures with `vertMap`, `edgeMap`) (`Hom.lean`).
- `TopologicalMinor` (subdivision structure) (`TopologicalMinor.lean`).
- `TopologicalMinor.of_le` — if `H ≤ G`, then `H` is a topological minor of `G`.

**Key lemmas:** composition `comp` for each of `Hom`/`Emb`/`Iso`; `Iso.id`;
`Hom.anti_left`, `Hom.mono_right`.

---

## Dart / `GraphLike` abstraction

This is a typeclass-based abstraction of "graph-like" structures (darts, adjacency)
generalizing the concrete `Graph`.

- `Dart`, `Dart.edge`, `Dart.fst`, `Dart.snd` (inductive: `dir`/`fwd`/`bck`)
  (`GraphLike/Graph.lean`).
- `DartLike`, `GraphLike` (classes) (`GraphLike/Basic.lean`).
- `GraphLike.verts`, `GraphLike.darts`, `GraphLike.Adj`, `GraphLike.step`,
  `GraphLike.DartAdj` (`GraphLike/Basic.lean`).
- `SymmDartLike`, `SymmGraphLike` (`GraphLike/Symm.lean`).
- `dartSym2`, `dartSymm` (`GraphLike/Symm.lean`).
- `Walk` (inductive: `nil`/`cons`), `Walk.length`, `Walk.support`, `Walk.darts`,
  `Walk.Nil` (`GraphLike/Walk.lean`).
- `ArbRel` (a total order extending equality), `source`, `target`
  (`GraphLike/ArbRel.lean`).
- `IsLink.source`, `IsLink.target`.

**Key lemmas:**
- `inv_mem_darts_iff`, `dartSym2_symm`, `dartSym2_eq_iff`.
- `exists_boundary_dart`, `head_support`, `getLast_support`, `length_support`,
  `isChain_adj_support`, `darts_injective`.

`Graph α β` is made an instance of `DartLike` and `GraphLike` in
`GraphLike/Graph.lean`.

---

## Bipartite graphs

- `Bipartition` — structure with `left`, `right` vertex sets (`Bipartite.lean`).
- `Bipartition.Same` / `Bipartition.Opp` — relations.
- `Bipartite` — a graph admitting a bipartition (`Bipartite.lean`).
- `CompleteBipartiteGraph.bipartition` (`Bipartite.lean`).

**Key theorems:**
- `bipartite_iff_forall_cycle_even` — A graph is bipartite iff every cycle has even
  length.
- `Bipartition.same_iff_even_dist`, `Bipartition.opp_iff_odd_dist` — same/opposite side
  iff walk distance parity.
- `Bipartite.length_even_of_isWalk_isClosed` — closed walks in bipartite graphs are
  even-length.
- `bipartite_of_forall_parity_adj_swap` — alternative characterization.

---

## Distance and shortest paths

- `eDist` (extended natural distance), `dist` (natural distance) (`Distance.lean`).
- `IsShortestPath` (`Distance.lean`).

**Key lemmas:**
- `eDist_comm`, `eDist_triangle` — distance is a pseudometric.
- `ConnBetween.exists_isPath_length_eq_eDist` — every connection has a path of length
  equal to the distance.
- `Adj.eDist_le_one`, `ConnBetween.exists_adj_eDist_eq_add_one`.
- `IsShortestPath.prefix`, `IsShortestPath.suffix`, `IsShortestPath.sublist`.

---

## Independent sets

- `IsIndependent` — a set of vertices with no edges between any two (`Independent.lean`).
- `IndepNumLE` — bound on independent number (`Independent.lean`).
- `IsMaxIndependent` (`Independent.lean`).

**Key lemmas:** `isIndependent_pair_iff_of_ne`, `IsIndependent.mono`,
`isIndependent_empty`, `isIndependent_singleton`, `IsMaxIndependent.bot_iff`.

---

## Edge coloring

- `EdgeColoring` — a function assigning a "color" to each edge (`EdgeColoring.lean`).
- `EdgeColorable` (`EdgeColoring.lean`).
- `chromaticIndex` (`EdgeColoring.lean`).

**Key lemmas:** `EdgeColoring.injOn_incidenceSet`, `EdgeColoring.map`,
`EdgeColorable_mono`.

---

## Simplicity, loops, simplification

- `Loopless` (class), `Simple` (class) (`Simple.lean`).
- `loopRemove`, `simplify` (`Simple.lean`).
- `incAdjEquiv` — bijection between edges incident to `v` and neighbors of `v` in
  loopless graphs (`Simple.lean`).

**Key lemmas:** `loopless_iff_forall_ne_of_adj`, `Simple.ends_injective`,
`loopRemove_isSpanningSubgraph`, `IsPath.toGraph_simple`.

---

## Basic definitions (vertices, edges, neighborhoods)

In `Basic.lean`:

- `endSet` — set of endpoints of an edge (`V(G, e)`).
- `incVertexSet` — vertices incident to an edge set (`V(G, F)`).
- `parallel` — two edges with the same endpoints (and `parallelClasses`,
  `parallel_refl`, `parallel.symm`, `parallel.trans`).
- `Neighbor` (open neighborhood, `N(G, x)`), `SetNeighbor` (external neighborhood,
  `N(G, S)`).
- `IncEdges` (edges at a vertex, `E(G, v)`), `SetIncEdges` (edges at a set of vertices,
  `E(G, S)`).
- `LinkEdges` (edges linking two vertices, `E(G, u, v)`),
  `SetLinkEdges` (edges between two sets, `E(G, S, T)`).
- `δ(G, S)` — edge boundary (cut) of `S`.
- `Isolated`, `IsolatedSet` (`Isol(G)`), `IsPendant`, `IsLeaf`, `IsLeafEdge`.

**Notable lemmas:** `endSet_encard_le_two`, `incVertexSet_encard_le`,
`Isolated.not_adj`, `IsLeaf.exists_unique_inc`, `setLinkEdges_singleton_eq_setOf_isNonloopAt`.

---

## Matrix viewpoint (incidence matrix)

- `orientation` (structure) (`Matrix.lean`).
- `signedIncMatrix` — signed incidence matrix of an oriented graph (`Matrix.lean`).
- `coeff_walk` — coefficient extraction along a walk (`Matrix.lean`).

**Key lemmas:**
- `signedIncMatrix_isTrail` — sum of signed columns along a trail equals last − first.
- `signedIncMatrix_isCyclicWalk` — sum is 0 for cyclic walks.
- `signedIncMatrix_pendent_col_support`.

---

## Finiteness conditions

Classes (in `Finite.lean`):
- `EdgeFinite` — every vertex set has finitely many incident edges.
- `Finite` — both vertex and edge sets finite.
- `LocallyFinite` — each vertex has finitely many incident edges.

**Key lemmas:**
- `finite_list_nodup`, `isTrail_finite`, `isPath_finite`, `isCyclicWalk_finite`.
- `exists_le_maximal_isTrail` / `isPath` / `isCyclicWalk` — Zorn-style existence of
  maximal walks.
- `finite_setOf_le` — finitely many subgraphs.
- `encard_delete_vertex_lt`, `encard_delete_edge_lt` — well-founded induction
  principles.

---

## Gammoids

- `GammoidIndep` — a set is gammoid-independent with respect to a base set
  (`Connected/Gammoid.lean`).
- `gammoidIndepMatroid`, `gammoid` — the resulting matroid.

**Key lemmas:** `GammoidIndep.exists_setEnsemble`, `setConnGE_of_exists_setEnsemble`.

---

## Graphic matroid (in `Matroid/Graphic.lean`)

The bridge from graphs to matroids.

- `cycleMatroid` — the graphic matroid `M(G)` (`Matroid/Graphic.lean`).
- `eRank` — extended rank (`Matroid/Graphic.lean`).

**Key lemmas:**
- `cycleMatroid_indep` — independence ↔ acyclic ↔ forest.
- `cycleMatroid_circuit` — circuits ↔ cycle sets.
- `cycleMatroid_isBase` — bases ↔ spanning forests ↔ maximal acyclic sets.
- `eRank_cycleMatroid_eq` — rank formula.
- `eRank_cycleMatroid_add_numberOfComponents` — `r(M(G)) = |V| - c(G)`.
- `twoPaths` — used in circuit elimination.

---

## Summary of named theorems

| Theorem | File:line | Statement |
|---|---|---|
| **twoPaths** | `Forest.lean:12` | Two distinct paths with same ends contain a cycle |
| **Handshake (ℕ∞)** | `Degree/Basic.lean:281` | ∑ eDegree(v) = 2·\|E(G)\| |
| **Handshake (ℕ)** | `Degree/Basic.lean` | ∑ degree(v) = 2·\|E(G)\| (subtype) |
| **Menger (set)** | `Connected/Menger.lean:204` | Set-connectivity ≥ n ⟺ n disjoint S–T paths |
| **Menger (vertex)** | `Connected/Menger.lean:232` | Vertex-connectivity ≥ n ⟺ n internally disjoint s–t paths |
| **Menger (edge)** | `Connected/Menger.lean:428` | Edge-connectivity ≥ n ⟺ n edge-disjoint s–t paths |
| **Menger (mixed)** | `Connected/Menger.lean:345` | Mixed vertex/edge version via mixed line graph |
| **Berge** | `Matching/Berge.lean:552` | Matching is maximum ⟺ no augmenting path |
| **König** | `Matching/Konigs.lean:455` | In bipartite graphs: ν(G) = τ(G) |
| **Tutte-Berge** | `Matching/TutteBerge.lean:218` | ν(G) = (\|V\| − max_Z (odd(G−Z) − \|Z\|)) / 2 |
| **Euler's formula** | `Planarity/Defs.lean:67` | \|V(G)\| + \|V(H)\| = \|E(G)\| + c(G) + c(H) for dual pairs |
| **Path-or-cycle** | `Degree/Max.lean:106` | Finite connected max-degree ≤ 2 graph is path or cycle |
| **Spanning tree** | `Tree.lean:31` | Every connected graph has a spanning tree |

---

## Directory map (one-line summaries)

For orientation, here is what each file is *primarily* about.

```
Matroid/Graph/
├── Basic.lean                     – Multigraph extensions: endSet, neighborhoods, parallel, isolated, leaves.
├── AcyclicSet.lean                – IsAcyclicSet, IsCycleSet, IsMaximalAcyclicSet.
├── Bipartite.lean                 – Bipartition, Bipartite, bipartite iff cycles even.
├── Distance.lean                  – eDist, dist, IsShortestPath.
├── EdgeColoring.lean              – EdgeColoring, chromaticIndex.
├── Finite.lean                    – EdgeFinite, Finite, LocallyFinite; maximal-walk existence.
├── Forest.lean                    – IsForest, IsTree, IsCycle, twoPaths.
├── Hom.lean                       – Hom, Emb, Iso (with vertMap, edgeMap).
├── Independent.lean               – IsIndependent, IsMaxIndependent.
├── Lattice.lean                   – Subgraph/ClosedSubgraph lattices, NumberOfComponents.
├── Map.lean                       – Vertex/edge relabeling, IsContractClosed.
├── Matrix.lean                    – Signed incidence matrix of an oriented graph.
├── Simple.lean                    – Loopless, Simple, loopRemove, simplify, incAdjEquiv.
├── TopologicalMinor.lean          – TopologicalMinor structure.
├── Tree.lean                      – Spanning tree existence, |V| ≤ |E| + 1.
├── Connected/                     – Connectivity (parallelized by topic)
│   ├── Defs.lean                  – Core predicates: Preconnected, Connected, connectivity, ConnGE.
│   ├── Basic.lean                 – IsSep, IsMinSep, IsEdgeSep, IsMixedSep, preconnectivity, sepConnectivity.
│   ├── Bond.lean                  – IsBridge, IsEdgeCut, IsBond.
│   ├── Component.lean             – walkable, Components, compPartition, connPartition.
│   ├── Construction.lean          – Connectivity of named constructions.
│   ├── Gammoid.lean               – GammoidIndep, gammoid (graph → matroid).
│   ├── LineGraph.lean             – Edge-connectivity via the line graph.
│   ├── Menger.lean                – Menger's theorems (set, vertex, edge, mixed).
│   ├── Minor.lean                 – Connectivity under maps and contractions.
│   ├── MixedLineGraph.lean        – L'(G) for mixed Menger.
│   ├── Subgraph.lean              – Deleting leaves from trails stays connected.
│   ├── Set/Defs.lean              – SetConnected, IsSetCut, SetConnGE, SetEnsemble.
│   ├── Set/Leg.lean               – "Right leg" decomposition for Menger.
│   ├── Set/SetEnsemble.lean       – Ensemble operations (path_insert, extend_right, ...).
│   ├── Vertex/Defs.lean           – ConnBetween, IsSepBetween, PathEnsemble, VertexEnsemble.
│   ├── Vertex/Basic.lean          – Walks in closed-subgraph complements.
│   └── Vertex/VertexEnsemble.lean – VertexEnsemble.ofSetEnsemble, extend_singleEdge.
├── Constructions/
│   ├── Basic.lean                 – noEdge, singleEdge, banana, bouquet, Complete(K_n, K_{m,n}), StarGraph, LineGraph, mixedLineGraph.
│   └── Random.lean                – randomGraph (instance Simple).
├── Degree/                        – Degree machinery
│   ├── Defs.lean                  – DegreePos, MaxDegreeLE, MinDegreeGE, Regular.
│   ├── Basic.lean                 – incFun, eDegree, degree, handshake.
│   ├── Constructions.lean         – Degree under operations.
│   ├── Leaf.lean                  – isolated iff eDegree 0; leaf iff eDegree 1.
│   └── Max.lean                   – Path-or-cycle classification.
├── GraphLike/                     – Typeclass abstraction (DartLike, GraphLike, SymmGraphLike, Walk)
│   ├── Basic.lean                 – DartLike, GraphLike, GraphLike.Adj, GraphLike.step.
│   ├── Graph.lean                 – Graph α β as instance; Dart inductive.
│   ├── Symm.lean                  – SymmDartLike, SymmGraphLike, dartSym2.
│   ├── Walk.lean                  – Walk (generalized).
│   ├── ArbRel.lean                – Arbitrary total order for orienting edges.
│   └── Contract.lean              – Abstract contract operation.
├── Matching/
│   ├── Defs.lean                  – IsMatching, IsMaxMatching, ν, IsCover, τ, IsMatchable, oddComponents.
│   ├── Berge.lean                 – IsAugmenter, berge.
│   ├── Konigs.lean                – Konig'sTheorem (bipartite).
│   └── TutteBerge.lean            – matchingIndepMatroid, tutte_berge (sketch).
├── Minor/
│   ├── Defs.lean                  – contract, IsLink.contract, minorMap, IsMinor, sContract, IsPartitionGraph.
│   └── Conn.lean                  – Connectivity under contraction; uncontracting walks.
├── Planarity/                     – Planarity framework
│   ├── Defs.lean                  – matroidalDual, euler_formula.
│   ├── K33.lean                   – K₃,₃ non-planarity.
│   ├── Drawing.lean               – Plane drawings.
│   ├── CombMap/                   – Combinatorial maps (Basic, Equiv).
│   ├── CWComplex/DualGraph.lean   – Dual graph of a CW complex.
│   ├── CycleList/Basic.lean       – Cycle lists.
│   ├── GraphContinuum/Basic.lean  – Graph-as-continuum.
│   ├── Realization/               – Topological realization (Basic, Celluar, CWComplex, Metric, Subgraph).
│   └── Topology/                  – Plane topology (Circle, Circuit, ConnPartition, Curve, JCT, Path, Plane, PolygonalPath).
├── Subgraph/
│   ├── Defs.lean                  – restrict, deleteEdges, induce, deleteVerts, union, inter.
│   ├── Basic.lean                 – IsInducedSubgraph, IsSpanningSubgraph, IsClosedSubgraph.
│   ├── Compatible.lean            – Compatible relation and its closure properties.
│   ├── Delete.lean                – Lemmas about edge/vertex deletion.
│   ├── Inter.lean                 – Intersection lemmas.
│   ├── Lemma.lean                 – Misc subgraph lemmas.
│   └── Union.lean                 – Union lemmas.
├── Walk/                          – Walk predicates on Graph
│   ├── Basic.lean                 – IsWalk, IsWalkFrom.
│   ├── Cycle.lean                 – IsTour, IsCyclicWalk.
│   ├── Dart.lean                  – DartStructure, dartFiber, IncidenceType.
│   ├── OrientationWalk.lean       – Walk orientation.
│   └── Path.lean                  – IsTrail, IsPath, IsTrailFrom, IsPathFrom.
└── WList/                         – Underlying WList α β type
    ├── Defs.lean                  – WList, first/last/vertex/edge/length, Nil, Nonempty, WellFormed, Inc.
    ├── Ops.lean                   – append, concat, reverse, map, edgeMap, TsiLw equivalence.
    ├── TakeDrop.lean              – prefixUntil, suffixFrom, tail, dropLast, take, drop, dedup.
    ├── Sublist.lean               – IsSublist, IsPrefix, IsSuffix, IsInfix, DecomposeTo.
    ├── Decompose.lean             – breakAt, betweenSets.
    └── Cycle.lean                 – IsClosed, intRotate.
```

Related (in `Matroid/`):
- `Matroid/Graphic.lean` — graphic matroid, `cycleMatroid`, `eRank`, `twoPaths` usage.
