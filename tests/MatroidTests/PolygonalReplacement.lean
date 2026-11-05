module

public import Matroid.ForMathlib.Geometry.PrimitiveLinkReplacement
public import Matroid.Graph.Planarity.PLReduction

open Set Metric PolygonalPath

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]

-- Individual tolerances and obstacles, with loops preserved alongside arcs.
example {Z : Set V} [Finite Z] {a b : ι → Z} {L : ι → Set V}
    (hL : ∀ i, IsPrimitiveLink (L i) (a i).1 (b i).1)
    (hLV : ∀ i, L i ∩ Z ⊆ {(a i).1, (b i).1})
    (hLL : Pairwise fun i j ↦ L i ∩ L j ⊆ Z)
    (K : ι → Set V) (hK : ∀ i, IsClosed (K i))
    (hLK : ∀ i, Disjoint (L i) (K i)) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ M : ι → Set V, (∀ i, IsSegmentFigure (M i)) ∧
      (∀ i, a i = b i → IsCircuit (M i)) ∧
      (∀ i, M i ∩ Z = {(a i).1, (b i).1}) ∧
      (Pairwise fun i j ↦ M i ∩ M j ⊆ Z) ∧
      ∀ i, Disjoint (M i) (K i) ∧ M i ⊆ thickening (ε i) (L i) := by
  obtain ⟨M, hM, hp, hV, hd, hU⟩ := exists_polygonal_primitiveLink_family hL hLV hLL
    (fun i ↦ (K i)ᶜ ∩ thickening (ε i) (L i))
    (fun i ↦ (hK i).isOpen_compl.inter isOpen_thickening)
    (fun i ↦ subset_inter (hLK i).subset_compl_right (self_subset_thickening (hε i) _))
  refine ⟨M, hp, fun i hi ↦ ?_, hV, hd, fun i ↦
    ⟨disjoint_left.mpr fun x hx ↦ (hU i hx).1, fun x hx ↦ (hU i hx).2⟩⟩
  exact (isPrimitiveLink_iff_isCircuit.mp (hi ▸ hM i)).1

-- Reversing the endpoint labels requires only symmetry of the link and endpoint set.
example {Z : Set V} [Finite Z] {a b : ι → Z} {L : ι → Set V}
    (hL : ∀ i, IsPrimitiveLink (L i) (a i).1 (b i).1)
    (hLV : ∀ i, L i ∩ Z ⊆ {(a i).1, (b i).1})
    (hLL : Pairwise fun i j ↦ L i ∩ L j ⊆ Z) :
    ∃ M : ι → Set V, (∀ i, IsPrimitiveLink (M i) (b i).1 (a i).1) ∧
      (∀ i, IsSegmentFigure (M i)) ∧
      (∀ i, M i ∩ Z = {(b i).1, (a i).1}) ∧
      (Pairwise fun i j ↦ M i ∩ M j ⊆ Z) := by
  obtain ⟨M, hM, hp, hV, hd, -⟩ := exists_polygonal_primitiveLink_family
    (fun i ↦ (hL i).symm) (fun i ↦ by simpa only [pair_comm] using hLV i) hLL
    (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ subset_univ _)
  exact ⟨M, hM, hp, hV, hd⟩

-- The containing segment figure need not itself be a primitive link.
example {S T L : Set V} {a b : V} (hS : IsSegmentFigure S) (hT : IsSegmentFigure T)
    (hL : IsPrimitiveLink L a b) (hsub : L ⊆ S ∪ T) :
    ∃ P : PolygonalPath a b, P.toPath.IsPrimitive ∧ P.toSet = L :=
  hL.exists_polygonalPath ((hS.union hT).of_isPrimitiveLink_subset hL hsub)

-- Finite graph drawing replacement no longer needs a loopless hypothesis.
example {α β : Type*} {G : Graph α β} [G.Finite] (D : Graph.Drawing G V) :
    ∃ P : Graph.PLDrawing G V, ∀ x, P.vertex x = D.vertex x := D.exists_plDrawing

/-- info: 'exists_polygonal_primitiveLink_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_polygonal_primitiveLink_family

/-- info: 'IsPrimitiveLink.exists_radial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsPrimitiveLink.exists_radial

/-- info: 'IsPrimitiveLink.exists_polygonalPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsPrimitiveLink.exists_polygonalPath

/-- info: 'Graph.Drawing.exists_plDrawing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.exists_plDrawing
