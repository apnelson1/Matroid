module

public import Matroid.GraphTheory.HypergraphLike.Hom
public import Matroid.GraphTheory.HypergraphLike.Hierarchy.GraphLike

/-! # Pairing preservation for maps of graphs -/

@[expose] public section

open Set Function

namespace HypergraphLike

variable {V I E Gr W J F Hr : Type*} {G : Gr} {H : Hr}
  [HypergraphLike V I E G] [HypergraphLike W J F H] [GraphLike G] [GraphLike H]

/-- An incidence embedding between graphs preserves the paired incidence. -/
lemma IncEmb.map_other' (f : IncEmb G H) (i : I(G)) :
    f.incMap' (GraphLike.other' i) = GraphLike.other' (f.incMap' i) := by
  have he : edgeMap' (f.incMap' i) = edgeMap' (f.incMap' (GraphLike.other' i)) := by
    rw [f.map_edgeMap', f.map_edgeMap', GraphLike.edgeMap'_other']
  exact (GraphLike.edgeMap'_eq (f.incMap' i) _ he).resolve_left
    (fun h ↦ GraphLike.other'_ne i (f.incMap'_injective h))

/-- For graphs, an incidence embedding reaches the whole fibre of every mapped edge. -/
lemma IncEmb.isLocallySurjective (f : IncEmb G H) : f.toIncHom.IsLocallySurjective := by
  intro e j hj
  obtain ⟨i, hi, _⟩ := GraphLike.exists_isSource_of_mem_edgeSet' (G := G) e.property
  have hi' : edgeMap' i = e := Subtype.ext hi
  have he : edgeMap' (f.incMap' i) = edgeMap' j := by rw [f.map_edgeMap', hi', hj]
  obtain rfl | rfl := GraphLike.edgeMap'_eq (f.incMap' i) j he
  · exact ⟨i, hi', rfl⟩
  exact ⟨GraphLike.other' i, (GraphLike.edgeMap'_other' i).trans hi', f.map_other' i⟩

/-- A graph homomorphism preserves the paired incidence because it reaches each two-element fibre. -/
lemma Hom.map_other' (f : Hom G H) (i : I(G)) :
    f.incMap' (GraphLike.other' i) = GraphLike.other' (f.incMap' i) := by
  have he : edgeMap' (f.incMap' i) = edgeMap' (f.incMap' (GraphLike.other' i)) := by
    rw [f.map_edgeMap', f.map_edgeMap', GraphLike.edgeMap'_other']
  refine (GraphLike.edgeMap'_eq (f.incMap' i) _ he).resolve_left ?_
  intro h
  obtain ⟨j, hj, hfj⟩ := f.isLocallySurjective (edgeMap' i) (a := GraphLike.other' (f.incMap' i))
    ((GraphLike.edgeMap'_other' _).trans (f.map_edgeMap' i))
  obtain hj | hj := GraphLike.edgeMap'_eq i j hj.symm
  · rw [hj] at hfj
    exact GraphLike.other'_ne (f.incMap' i) hfj.symm
  rw [hj] at hfj
  exact GraphLike.other'_ne (f.incMap' i) (hfj.symm.trans h)

end HypergraphLike
