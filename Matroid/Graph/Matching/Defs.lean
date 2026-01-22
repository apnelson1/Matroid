import Matroid.Graph.Degree.Max
import Matroid.Graph.Bipartite
import Matroid.Parallel

namespace Graph

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}

open Set symmDiff WList

/-! ### Matching -/

/-- A matching is a set of edges where no two edges share a vertex.
  Note: This does not exclude loops. Consider assuming `[Loopless G]` to exclude loops. -/
@[mk_iff]
structure IsMatching (G : Graph α β) (M : Set β) : Prop where
  subset : M ⊆ E(G)
  disjoint : ∀ ⦃e f⦄, e ∈ M → f ∈ M → e ≠ f → Disjoint V(G, e) V(G, f)

@[mk_iff]
structure IsMaxMatching (G : Graph α β) (M : Set β) : Prop extends G.IsMatching M where
  max : ∀ M', G.IsMatching M' → M'.encard ≤ M.encard

noncomputable def matchingNumber (G : Graph α β) : ℕ∞ :=
  sSup {n | ∃ M, G.IsMatching M ∧ n = M.encard}

scoped notation "ν(" G ")" => matchingNumber G

def IsMatchable (G : Graph α β) (S : Set α) : Prop := ∃ M, G.IsMatching M ∧ V(G, M) = S


lemma IsMatching.subsingleton_inc (h : G.IsMatching M) (v : α) : (M ∩ E(G, v)).Subsingleton := by
  intro e he f hf
  by_contra hne
  exact (h.disjoint he.1 hf.1 hne).le_bot ⟨he.2, hf.2⟩

lemma IsMatching.degree_le_one (h : G.IsMatching M) (v : α) : (M ∩ E(G, v)).encard ≤ 1 := by
  rw [encard_le_one_iff_subsingleton]
  exact h.subsingleton_inc v

lemma IsMatching.maxDegree_le_one [G.Loopless] (h : G.IsMatching M) : (G ↾ M).MaxDegreeLE 1 := by
  have : ∀ v : α, E(G ↾ M, v).encard ≤ ↑1 := by
    intro v
    refine (encard_le_encard ?_).trans (h.degree_le_one v)
    rintro e ⟨w, hw⟩
    exact ⟨hw.1, w, hw.2⟩
  rw [maxDegreeLE_iff']
  intro v hv
  rw [eDegree_eq_encard_inc]
  exact this v

lemma IsMatching.of_le (hle : G ≤ H) (h : G.IsMatching M) : H.IsMatching M where
  subset := h.subset.trans (edgeSet_mono hle)
  disjoint e f heM hfM hne := by
    -- Consider `disjoint_iff_forall_notMem` and`inc_eq_of_le`
    sorry

lemma IsMatching.encard_le (hM : G.IsMatching M) : M.encard ≤ ν(G) := by
  sorry

lemma IsMaxMatching.encard (h : G.IsMaxMatching M) : M.encard = ν(G) := by
  sorry

lemma IsMatching.isMaxMatching_of_encard_eq (hM : G.IsMatching M) (h : M.encard = ν(G)) :
    G.IsMaxMatching M where
  toIsMatching := hM
  max M' hM' := by
    sorry

lemma IsMatching.isMaxMatching_of_vertex_subset (hM : G.IsMatching M) (hsu : V(G) ⊆ V(G, M)) :
    G.IsMaxMatching M where
  toIsMatching := hM
  max M' hM' := by
    sorry

def IsMatching.restrict₂ (hM : G.IsMatching M) (hM' : G.IsMatching M') : Graph α β :=
  G ↾ (M ∆ M') |>.loopRemove

instance IsMatching.restrict₂.edgeFinite (hM : G.IsMatching M) (hM' : G.IsMatching M')
    [G.EdgeFinite] : (hM.restrict₂ hM').EdgeFinite := by
  sorry

lemma IsMatching.symmDiff_maxDegree_le_two (hM : G.IsMatching M) (hM' : G.IsMatching M') :
    (hM.restrict₂ hM').MaxDegreeLE 2 := by
  sorry

lemma IsMatching.disjoint_inter_of_isCycleGraph_symmDiff (hM : G.IsMatching M)
    (hM' : G.IsMatching M') (hC : C.IsCycleGraph) (hCG : C ≤ hM.restrict₂ hM') :
    Disjoint (E(C) ∩ M) (E(C) ∩ M') := by
  sorry

lemma IsMatching.inter_encard_eq_of_isCycleGraph_isCompOf_symmDiff (hM : G.IsMatching M)
    (hM' : G.IsMatching M') (hC : C.IsCycleGraph) (hCG : C.IsCompOf (hM.restrict₂ hM')) :
    (E(C) ∩ M).encard = (E(C) ∩ M').encard := by
  sorry

-- lemma IsMatching.exists_isPathGraph_isCompOf_symmDiff (hM : G.IsMatching M)
--     (hM' : G.IsMatching M')
--     (hcd : M.encard < M'.encard) [G.EdgeFinite] :
--     ∃ G' : Graph α β, G'.IsCompOf (hM.restrict₂ hM') ∧ G'.IsPathGraph := by
--   contrapose! hcd
--   have hmax := hM.symmDiff_maxDegree_le_two hM'
--   have hcd' : ∀ (G' : Graph α β), G'.IsCompOf (hM.restrict₂ hM') → G'.IsCycleGraph :=
--     fun G' hG' ↦ hG'.isPathGraph_or_isCycleGraph_of_maxDegreeLE hmax |>.resolve_left
--     <| hcd G' hG'
--   clear hcd hmax
--   sorry -- component partition

lemma isMaxMatching_iff_maximalFor : G.IsMaxMatching M ↔ MaximalFor G.IsMatching Set.encard M :=
  ⟨fun h => ⟨h.toIsMatching, fun T hT _ ↦ h.2 T hT⟩,
    fun h => ⟨h.1, fun T hT ↦ (le_total T.encard M.encard).elim id <| h.2 hT⟩⟩

lemma matchingNumber_mono (hle : G ≤ H) : ν(G) ≤ ν(H) := by
  sorry



/-! ### Augmenting paths -/

@[mk_iff]
structure IsAltPath (G : Graph α β) (hM : G.IsMatching M) (P : WList α β) : Prop
  extends G.IsPath P where
  mem_matching : P.edge.IsChain (fun e f ↦ e ∈ M ∨ f ∈ M)

@[mk_iff]
structure IsSemiAugPath (G : Graph α β) (hM : G.IsMatching M) (P : WList α β) : Prop
  extends G.IsAltPath hM P where
  nonempty : P.Nonempty
  last_not_in : P.last ∉ V(G, M)

@[mk_iff]
structure IsAugPath (G : Graph α β) (hM : G.IsMatching M) (P : WList α β) : Prop
  extends G.IsSemiAugPath hM P where
  first_not_in : P.first ∉ V(G, M)

/-! ### Structure of graph from maximal matching -/

def Inessential (G : Graph α β) (x : α) : Prop :=
  ∃ M, G.IsMaxMatching M ∧ x ∉ V(G, M)

structure IsOddCompOf (H G : Graph α β) extends H.IsCompOf G where
  finite : V(H).Finite
  odd : Odd V(H).encard

def oddComponents (G : Graph α β) : Set (Graph α β) :=
  {H | H.IsOddCompOf G}

/-! ### Cover -/

structure IsCover (G : Graph α β) (S : Set α) : Prop where
  subset : S ⊆ V(G)
  cover : E(G) ⊆ E(G, S)

structure IsMinCover (G : Graph α β) (S : Set α) : Prop extends IsCover G S where
  min : ∀ T, IsCover G T → S.encard ≤ T.encard

noncomputable def coverNumber (G : Graph α β) : ℕ∞ :=
  sInf {n | ∃ S, G.IsCover S ∧ n = S.encard}

scoped notation "τ(" G ")" => coverNumber G
