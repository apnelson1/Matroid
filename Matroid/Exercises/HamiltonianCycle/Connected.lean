import Matroid.Graph.Connected.Basic

open Set

namespace Graph

variable {α β : Type*} {G H K : Graph α β} {S : Set α}

/-! ### Deprecated aliases (prefer the named replacements) -/

@[deprecated numberOfComponents_eq_one_iff (since := "2026-08-14")]
lemma components_encard_eq_one_iff : G.Components.encard = 1 ↔ G.Connected := by
  rw [← numberOfComponents_eq_one_iff, NumberOfComponents]

@[deprecated empty_isSep_iff (since := "2026-08-14")]
lemma isSep_empty_iff_not_connected : G.IsSep ∅ ↔ ¬ G.Connected :=
  empty_isSep_iff

@[deprecated empty_isMinSep_iff (since := "2026-08-14")]
lemma isMinSep_empty_iff_not_connected : G.IsMinSep ∅ ↔ ¬ G.Connected :=
  empty_isMinSep_iff

@[deprecated IsClosedSubgraph.components_subset_components (since := "2026-08-14")]
lemma IsClosedSubgraph.components_subset (hH : H ≤c G) : H.Components ⊆ G.Components :=
  hH.components_subset_components

@[deprecated IsCompOf.of_isClosedSubgraph (since := "2026-08-14")]
lemma IsClosedSubgraph.isCompOf_of_isCompOf (hH : H ≤c G) (hK : K.IsCompOf H) : K.IsCompOf G :=
  hK.of_isClosedSubgraph hH

@[deprecated IsCompOf.of_deleteVerts (since := "2026-08-14")]
lemma IsCompOf.isCompOf_compl_of_disjoint
    (hH : H.IsCompOf G) (hdisj : Disjoint V(H) S) : H.IsCompOf (G - S) :=
  hH.of_deleteVerts hdisj

end Graph
