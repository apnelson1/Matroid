From Flat
- flat iff cycle almost included is included
- take a compOf G \upr F
- this is clearly a subgraph so why is it induced?
- induced is defined as any edge, e, between x and y s.t. x and y are in the subgraph then e must also be in the subgraph.
- Suppose there is an edge e that is not in F and between x and y belonging to some connected component of G \upr F. Then, since connected, there is some path between x and y inside F.
- Together with e, we have a cycle which is almost included in F, so e is in F. contradiction

To Flat
- Take a cycle that is almost included in F.
- Every vertex of this cycle must be in some connected component of G \upr F.
- So the only edge possibly not included in F, e, is between two vertices in the component.
- This component is an induced subgraph so e is included in F.
