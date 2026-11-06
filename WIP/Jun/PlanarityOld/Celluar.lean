

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

/- TODO:
1. Adding a chord edge on a non-outer face of a convex embedding is a convex embedding.
2. Subdividing an edge of a convex embedding is a convex embedding.
3. Apexing a face of a convex embedding is a convex embedding.
3. If simplification of a graph has a convex embedding, then the original graph has an embedding.
  - Adding a loop to a vertex of an embedding is an embedding.
  - Adding a parallel edge to an embedding is an embedding.

Goal: If a simple graph G has no K3,3 or K5 minor, then there is a convex embedding of G.
1. If G has no K3,3 or K5 minor, then the simplification of G has no K3,3 or K5 minor.
2. Edge maxmal simple graph s.t. it has no K3,3 or K5 minor is 3-connected.
3. 3-connected graph has an edge, e, that can be contracted to a 3-connected graph. (done)
4. By IH, G / e has a convex embedding.
5. The facial cycle bounding supervertex {u, v} in (G / e - {u, v}) can be divded to two halves,
  one half containing all neighbors of u in G and the other half containing all neighbors of v in
  G.
6. All neighbors of u in G are in the same facial cycle in G - u.
7. Add u back in by apexing the face containing u. -/
