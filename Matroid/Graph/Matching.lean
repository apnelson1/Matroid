import Matroid.Graph.Degree.Max
import Matroid.Graph.Bipartite
import Matroid.Parallel

namespace Graph

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}

open Set symmDiff WList

/-- A matching is a set of edges where no two edges share a vertex.
  Note: This does not exclude loops. Consider assuming `[Loopless G]` to exclude loops. -/
@[mk_iff]
structure IsMatching (G : Graph α β) (M : Set β) : Prop where
  subset : M ⊆ E(G)
  disjoint : ∀ ⦃e f⦄, e ∈ M → f ∈ M → e ≠ f → Disjoint V(G, e) V(G, f)

@[mk_iff]
structure IsMaxMatching (G : Graph α β) (M : Set β) : Prop extends G.IsMatching M where
  max : ∀ M', G.IsMatching M' → M'.encard ≤ M.encard

noncomputable def MatchingNumber (G : Graph α β) : ℕ∞ :=
  sSup {n | ∃ M, G.IsMatching M ∧ n = M.encard}

scoped notation "ν(" G ")" => MatchingNumber G

def IsMatchable (G : Graph α β) (S : Set α) : Prop := ∃ M, G.IsMatching M ∧ V(G, M) = S

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

def inessential (G : Graph α β) (x : α) : Prop :=
  ∃ M, G.IsMaxMatching M ∧ x ∉ V(G, M)

structure IsOddCompOf (H G : Graph α β) extends H.IsCompOf G where
  finite : V(H).Finite
  odd : Odd V(H).encard

def OddComponents (G : Graph α β) : Set (Graph α β) :=
  {H | H.IsOddCompOf G}

structure IsCover (G : Graph α β) (S : Set α) : Prop where
  subset : S ⊆ V(G)
  cover : E(G) ⊆ E(G, S)

structure IsMinCover (G : Graph α β) (S : Set α) : Prop extends IsCover G S where
  minimal : ∀ T, IsCover G T → S.encard ≤ T.encard

noncomputable def CoverNumber (G : Graph α β) : ℕ∞ :=
  sInf {n | ∃ S, G.IsCover S ∧ n = S.encard}

scoped notation "τ(" G ")" => CoverNumber G

variable {P P' : WList α β} {hM : G.IsMatching M}

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
  disjoint e f he hf hne := by
    sorry

lemma IsMatching.isMaxMatching_of_vertex_subset (hM : G.IsMatching M) (hsu : V(G) ⊆ V(G, M)) :
    G.IsMaxMatching M where
  toIsMatching := hM
  max M' hM' := by
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

@[simp]
lemma nil_isAltPath (hM : G.IsMatching M) (x : α) : G.IsAltPath hM (.nil x) ↔ x ∈ V(G) := by
  simp [isAltPath_iff]

lemma IsAltPath.of_cons (h : G.IsAltPath hM (.cons x e P)) : G.IsAltPath hM P := by
  simp only [isAltPath_iff, cons_isPath_iff, WList.cons_edge] at h ⊢
  obtain ⟨⟨hP, hl, hx⟩, he⟩ := h
  exact ⟨hP, he.of_cons⟩

@[simp]
lemma IsAltPath.tail (h : G.IsAltPath hM P) : G.IsAltPath hM P.tail := by
  match P with
  | .nil u => simp_all
  | .cons u e w => simp [h.of_cons]

lemma IsAltPath.suffix (h : G.IsAltPath hM P) (h' : P'.IsSuffix P) : G.IsAltPath hM P' :=
  h'.recOfTail (fun _ h ↦ h.tail) h

lemma IsAltPath.of_concat (h : G.IsAltPath hM (P.concat e x)) : G.IsAltPath hM P := by
  simp only [isAltPath_iff, concat_isPath_iff, WList.concat_edge, List.isChain_append,
    List.IsChain.singleton, Option.mem_def, List.head?_cons, Option.some.injEq, forall_eq',
    true_and] at h ⊢
  obtain ⟨⟨hP, hl, hx⟩, he, hlast⟩ := h
  refine ⟨hP, he⟩

lemma IsAltPath.dropLast (h : G.IsAltPath hM P) : G.IsAltPath hM P.dropLast := by
  obtain ⟨v, rfl⟩ | hne := P.exists_eq_nil_or_nonempty
  · rwa [WList.dropLast_nil]
  obtain ⟨w', f, y, rfl⟩ := hne.exists_concat
  rw [WList.dropLast_concat]
  exact h.of_concat

lemma IsAltPath.prefix (h : G.IsAltPath hM P) (h' : P'.IsPrefix P) : G.IsAltPath hM P' :=
  h'.recOfDropLast (fun _ h ↦ h.dropLast) h

lemma IsAltPath.mem_matching_iff {P : WList α β} (h : G.IsAltPath hM P) :
    P.edge.IsChain (fun e f ↦ e ∈ M ↔ f ∉ M) := by
  match P with
  | .nil u => simp
  | .cons u e (.nil v) => simp
  | .cons u e (.cons v f w) =>
    simp only [WList.cons_edge, List.isChain_cons_cons]
    obtain ⟨hor, -⟩ := by simpa using h.mem_matching
    obtain ⟨⟨hef, -⟩, -, -⟩ := by simpa using h.isTrail.edge_nodup
    obtain ⟨⟨-, hfvwf, -⟩, heuv, -, -⟩ := by simpa using h.toIsPath
    use ⟨fun heM hfM ↦ ?_, hor.resolve_right⟩, by simpa using h.of_cons.mem_matching_iff
    exact hM.disjoint heM hfM hef |>.notMem_of_mem_left heuv.inc_right hfvwf.inc_left

lemma IsAltPath.mem_matching_iff' {P : WList α β} (h : G.IsAltPath hM P) :
    P.edge.IsChain (fun e f ↦ e ∉ M ↔ f ∈ M) := by
  convert h.mem_matching_iff using 3
  rw [iff_not_comm, iff_comm (a := _ ∈ M)]

lemma isAugPath_of_singleEdge (hl : G.IsLink e u v) (hu : u ∉ V(G, M)) (hv : v ∉ V(G, M))
    (huv : u ≠ v) : G.IsAugPath hM (.cons u e (.nil v)) := by
  simp [hu, hv, isAugPath_iff, isSemiAugPath_iff, isAltPath_iff, hl.right_mem, huv, hl]

@[simp]
lemma nil_not_isAugPath : ¬ G.IsAugPath hM (.nil x) := by
  rintro h
  simpa using h.nonempty

@[simp]
lemma IsAugPath.vertex_notMem_of_cons (h : G.IsAugPath hM (cons u e P)) : u ∉ V(G, M) :=
  h.first_not_in

@[simp]
lemma IsAugPath.edge_notMem_of_cons (h : G.IsAugPath hM (cons u e P)) : e ∉ M := by
  rintro heM
  have := by simpa using h.first_not_in
  obtain ⟨h1, h2⟩ := cons_isWalk_iff.mp h.isWalk
  exact this e heM h1.inc_left

@[simp]
lemma IsAugPath.firstEdge_notMem (h : G.IsAugPath hM P) : h.nonempty.firstEdge ∉ M := by
  obtain ⟨u, e, P, rfl⟩ := h.nonempty.exists_cons
  rw [Nonempty.firstEdge_cons]
  exact h.edge_notMem_of_cons

@[simp]
lemma IsAugPath.vertex_notMem_of_concat (h : G.IsAugPath hM (concat P e v)) : v ∉ V(G, M) := by
  simpa using h.last_not_in

@[simp]
lemma IsAugPath.edge_notMem_of_concat (h : G.IsAugPath hM (concat P e v)) : e ∉ M := by
  rintro heM
  have := by simpa using h.last_not_in
  obtain ⟨h1, h2⟩ := concat_isWalk_iff.mp h.isWalk
  exact this e heM h2.inc_right

@[simp]
lemma IsAugPath.lastEdge_notMem (h : G.IsAugPath hM P) : h.nonempty.lastEdge ∉ M := by
  obtain ⟨u, e, P, rfl⟩ := h.nonempty.exists_concat
  simp only [lastEdge_concat]
  rintro heM
  have := by simpa using h.last_not_in
  obtain ⟨h1, h2⟩ := concat_isWalk_iff.mp h.isWalk
  exact this e heM h2.inc_right

@[simp]
lemma IsAugPath.mem_of_cons_cons (h : G.IsAugPath hM (cons u e (cons v f P))) : f ∈ M := by
  have := by simpa [h.edge_notMem_of_cons] using h.toIsAltPath.mem_matching
  exact this.1

@[simp]
lemma IsAugPath.mem_of_concat_concat (h : G.IsAugPath hM ((concat P e u).concat f v)) : e ∈ M := by
  have := by simpa [h.edge_notMem_of_concat] using h.toIsAltPath.mem_matching
  exact this.2

lemma not_isAugPath_of_length_two (h : P.length = 2) : ¬ G.IsAugPath hM P := by
  rintro hP
  obtain ⟨a, e, b, f, c, rfl⟩ := P.length_eq_two_iff.mp h; clear h
  have heM := hP.edge_notMem_of_cons
  have heq : cons a e (cons b f (nil c)) = (cons a e (nil b)).concat f c := rfl
  have hfM := (heq ▸ hP).edge_notMem_of_concat
  simpa [heM, hfM] using hP.toIsAltPath.mem_matching

-- lemma IsAugPath.trivial_or_cons_cons (h : G.IsAugPath hM P) : (∃ u e v, P = cons u e (nil v)) ∨
--     (∃ u e v f P', P = cons u e (cons v f P') ∧ G.IsAugPath hM P') := by
--   match P with
--   | .nil u => simpa using h.nonempty
--   | .cons u' e' (.nil v') => simp
--   | .cons u e (.cons v f P') =>
--     simp only [cons.injEq, reduceCtorEq, and_false, exists_false, ↓existsAndEq, and_true,
--       exists_and_right, true_and, false_or]
--     refine ⟨h.toIsAltPath.of_cons.of_cons, ?_, ?_, ?_⟩
--     · by_contra! h
--       match h with
--       | .nil x => exact (not_isAugPath_of_length_two <| by simp) h
--     ·
--       sorry
--     simpa using h.last_not_in

-- lemma IsAugPath.length_odd (h : G.IsAugPath hM P) : Odd P.length := by
--   induction P with
--   | nil _ => simp at h
--   | cons u e P ih =>
--     simp only [length]
--     exact ih.add_one
--   sorry

lemma IsAugPath.augment (h : G.IsAugPath hM P) : G.IsMatching (M ∆ E(P)) where
  subset := symmDiff_subset_union.trans <| union_subset hM.subset h.isWalk.edgeSet_subset
  disjoint e f he hf hne := by
    by_cases heM : e ∈ M <;> by_cases hfM : f ∈ M <;> simp [mem_symmDiff, heM, hfM] at he hf
    · exact hM.disjoint heM hfM hne
    · sorry
    · sorry

    sorry

lemma IsAugPath.augment_vertex_subset (h : G.IsAugPath hM P) : V(G, M) ⊆ V(G, M ∆ E(P)) := by
  sorry

lemma IsAugPath.augment_encard [G.EdgeFinite] (h : G.IsAugPath hM P) :
    (M ∆ E(P)).encard = M.encard + 1 := by
  sorry

lemma IsMatching.exists_isAugPath_not_max (hM : G.IsMatching M) (hnotmax : ¬ G.IsMaxMatching M)
    [G.EdgeFinite] : ∃ P, G.IsAugPath hM P := by
  obtain ⟨M', hM', hM'cd⟩ := by
    simpa only [isMaxMatching_iff, hM, true_and, not_forall, not_le] using hnotmax
  sorry


-- Konig's & Hall's theorem Section

lemma IsCover.mem_or_mem_or_isLink (h : G.IsCover S) (he : G.IsLink e u v) : u ∈ S ∨ v ∈ S := by
  sorry

lemma IsCover.le_encard (h : G.IsCover S) : τ(G) ≤ S.encard := by
  sorry

lemma IsMinCover.encard (h : G.IsMinCover S) : S.encard = τ(G) := by
  sorry

lemma isMinCover_iff_minimalFor : G.IsMinCover S ↔ MinimalFor G.IsCover Set.encard S :=
  ⟨fun h => ⟨h.toIsCover, fun T hT _ ↦ h.minimal T hT⟩,
    fun h => ⟨h.1, fun T hT ↦ (le_total T.encard S.encard).elim (h.2 hT) id⟩⟩

lemma IsCover.of_vertexDelete (h : (G - X).IsCover S) : G.IsCover ((V(G) ∩ X) ∪ S) where
  subset := sorry
  cover e he := sorry

lemma IsCover.isMinCover_of_encard_eq (hC : G.IsCover S) (h : S.encard = τ(G)) :
    G.IsMinCover S where
  toIsCover := hC
  minimal T hT := by
    sorry

def IsMatching.mapToCover (hM : G.IsMatching M) (hC : G.IsCover S) : M → S := by
  sorry

lemma IsMatching.mapToCover_inj (hM : G.IsMatching M) (hC : G.IsCover S) :
    Function.Injective (hM.mapToCover hC) := by
  sorry

lemma IsMatching.mapToCover_inc (hM : G.IsMatching M) (hC : G.IsCover S) (he : e ∈ M) :
    G.Inc e (hM.mapToCover hC ⟨e, he⟩) := by
  sorry

lemma matchingNumber_le_coverNumber : ν(G) ≤ τ(G) := by
  sorry

lemma IsMatching.mapToCover_range_eq_of_encard_eq (hC : G.IsCover S) (hM : G.IsMatching M)
    (h : S.encard = M.encard) : range (hM.mapToCover hC) = ⊤ := by
  sorry

lemma coverNumber_mono (hle : G ≤ H) : τ(G) ≤ τ(H) := by
  sorry

lemma IsPathGraph.konig (h : G.IsPathGraph) : τ(G) = ν(G) := by
  sorry

lemma IsCycleGraph.konig (hB : G.Bipartite) (h : G.IsCycleGraph) : τ(G) = ν(G) := by
  sorry

/-!
### König's Matching Theorem
Source: Romeo Rizzi (2000) [cite: 2]

Theorem: Let G be a bipartite graph. Then ν(G) = τ(G).

Proof:
Let G be a minimal counterexample. Then G is connected, is not a circuit, nor a path. [cite: 14]
So, G has a node of degree at least 3. Let u be such a node and v one of its neighbors. [cite: 15]

Case 1: If ν(G \ v) < ν(G). [cite: 16]
By minimality, G \ v has a cover W' with |W'| < ν(G). [cite: 16]
Hence, W' ∪ {v} is a cover of G with cardinality ν(G) at most. [cite: 17]

Case 2: Assume there exists a maximum matching M of G having no edge incident at v. [cite: 18]
Let f be an edge of G \ M incident at u but not at v. [cite: 18]
Let W' be a cover of G \ f with |W'| = ν(G). [cite: 22]
Since no edge of M is incident at v, it follows that W' does not contain v. [cite: 22]
So W' contains u and is a cover of G. [cite: 22]
-/
theorem Konig'sTheorem [H.Finite] (hB : H.Bipartite) : τ(H) = ν(H) := by
  have hloopless := hB.loopless
  by_contra! hne
  let P := fun (G : H.Subgraph) ↦ G.val.Bipartite ∧ τ(G.val) ≠ ν(G.val)
  obtain ⟨⟨G, hle⟩, ⟨hB, hne⟩, hMin⟩ := exists_minimal_of_wellFoundedLT P ⟨⟨H, le_refl _⟩, hB, hne⟩
  simp only [Subgraph.le_mk_iff, Subgraph.mk_le_iff, and_imp, Subtype.forall, P] at hB hMin hne
  have : G.Finite := finite_of_le hle
  have hcon : G.Connected := by
    /- Otherwise, by def of `Connected`, there is a strictly smaller component of `G`.
    `τ` and `ν` are additive over the components so at least one component must have `τ` or `ν`
    different.
    That component is a smaller counterexample to the theorem, contradicting minimality.-/
    sorry
  obtain ⟨u, hu, hdegu⟩ : ∃ u ∈ V(G), 3 ≤ G.degree u := by
    /- Otherwise, by `isPathGraph_or_isCycleGraph_of_maxDegreeLE`, `G` would be a path or cycle,
    By lemmas above, any path graph or cycle graph has `τ = ν`, contradicting `τ ≠ ν` assumption.-/
    sorry
  obtain ⟨v, hv⟩ := G.degree_ne_zero_iff_inc (v := u) |>.mp (by omega)
  -- have hlt := G.coverNumber_le_matchingNumber.lt_of_ne hne
  sorry

theorem Hall'sTheorem (B : G.Bipartition) :
    (∃ M, G.IsMatching M ∧ B.left ⊆ V(G, M)) ↔ ∀ D ⊆ B.left, D.encard ≤ N(G, D).encard := by
  sorry

-- Matroid exercise 4 Q2

/-
\subsection{Part (a)}
Show that, if $S \subseteq E(M)$ is a set of size at least $2$ whose two-element subsets are
all series pairs of $M$, then $r_M(E(M) - S) = r(M) - |S| + 1$.

\begin{proof}
  Consider $r_{M^*}(S)$. In $M^*$, $S$ is subset of a parallel class so $r_{M^*}(S) = 1$.
  Simultaneously, $r_{M^*}(S) = r_M(E(M) - S) + |S| - r(M)$.
  By rearranging and substituting, we have $r_M(E(M) - S) = r(M) - |S| + 1$.
\end{proof}-/
lemma _root_.Matroid.eRk_pos_of_mem_nonloop {M : Matroid α} {e : α} (heX : e ∈ X)
    (he : M.IsNonloop e) : 0 < M.eRk X := by
  refine Order.one_le_iff_pos.mp ?_
  rw [← he.eRk_eq]
  apply M.eRk_mono
  simpa

lemma _root_.Matroid.fooA {M : Matroid α} (hS : S ⊆ M.E) (hnt : S.Nontrivial)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → M.Series a b) : M.eRk (M.E \ S) + S.encard = M.eRank + 1 := by
  obtain ⟨s, hs, t, ht, hne⟩ := hnt
  have hnls := (h s hs t ht hne).isNonloop_left
  suffices M.dual.eRk S = 1 by
    rw [← this, add_comm M.eRank, M.eRk_dual_add_eRank S hS]
  refine le_antisymm ?_ (Order.one_le_iff_pos.mpr <| M✶.eRk_pos_of_mem_nonloop hs hnls)
  rw [← hnls.eRk_eq, ← M✶.eRk_closure_eq {s}]
  apply M✶.eRk_mono
  intro x hxS
  obtain rfl | hxs := eq_or_ne x s
  · exact M✶.subset_closure _ (by simpa using hnls.mem_ground) (by rfl)
  exact (h x hxS s hs hxs).mem_closure

/-
\subsection{Part (b)}
Let $G$ be a graph with vertex set $V$. We say that a set $X \subseteq V$ is matchable in $G$
if there is a matching of $G$ whose vertex set contains $X$. Show (using augmenting paths)
that the matchable sets of $G$ are the independent sets of a matroid on $V$. (We call this the
matchable sets matroid of $G$; note that this matroid has rank $2\nu(G)$).

\begin{proof}
\begin{itemize}
  \item[(I1)] $\emptyset$ is trivially matchable.
  \item[(I2)] Let $I$ is matchable. Then, for $J \subseteq I$, WTS $J$ is matchable using the
  exactly same matching.
  \item[(I3)] Let $I$ and $J$ be matchable s.t. $|I| < |J|$.
  Let $M_I$ and $M_J$ be the matchings of $G$ containing $I$ and $J$ respectively.
  Consider the symmetric difference $M_I \operatorname{\Delta} M_J$.
  Let $G' := (V(G), M_I \operatorname{\Delta} M_J)$.
  Since the max degree of $G'$ is at most $2$, $G'$ consists of alternating paths and cycles.
  Every vertex in $J \setminus I$ and $I \setminus J$ is an endpoint of an alternating path in $G'$.
  By $|I| < |J|$, $|I \setminus J| < |J \setminus I|$.
  If for every vertex in $J \setminus I$, the other endpoint is in $I \setminus J$, then
  we have a bijection between $J \setminus I$ and $I \setminus J$ which is a contradiction.
  Therefore, there exists some vertex $v \in J \setminus I$ in an alternating path in $G'$ s.t.
  the other endpoint is not in $I \setminus J$.
  If the other endpoint is matched by $M_J$, then the path is augmenting.
  Otherwise, the other endpoint is matched by $M_I$ but not in $I$, then the path is alternating.
  Regardless, we can create a new matching $M_I' := M_I \operatorname{\Delta} P$ where $P$ is the
  path in $G'$ containing $v$.
  This new matching matches all $I$ and also $v \in J$.
  Therefore, $I \cup \{v\}$ is matchable.
\end{itemize}
\end{proof}-/
def matchingIndepMatroid (G : Graph α β) : IndepMatroid α where
  E := V(G)
  Indep := fun S ↦ ∃ M, G.IsMatching M ∧ S ⊆ V(G, M)
  indep_empty := by
    sorry
  indep_subset := by
    sorry
  indep_aug := by
    sorry
  indep_maximal := by
    sorry
  subset_ground := by
    sorry

def matchingMatroid (G : Graph α β) : Matroid α := G.matchingIndepMatroid.matroid

/-
\subsection{Part (c)}
Let $G$ be a graph such that, for every vertex $v$ of $G$, there is a matching of $G$ of
size $\nu(G)$ whose vertex set does not include $v$.
\begin{enumerate}
    \item[i.] Show that the matchable sets matroid of $G$ has no coloop, and that every
    pair of adjacent vertices of $G$ is a series pair in this matroid.
    \item[ii.] Show that $G$ has a matching avoiding exactly one vertex from each of its
    components (and hence that each component of $G$ has an odd number of vertices).
\end{enumerate}

\begin{proof}
  \begin{enumerate}
    \item[i.] For every vertex $v$, there is a matching $M$ of $G$ of size $\nu(G)$ s.t. $v$ is not
    matched by $M$.
    Let $V(M)$ be the set of vertices matched by $M$.
    Then, $|V(M)| = 2 \nu(G)$ so $V(M)$ is a basis of the matchable sets matroid of $G$.
    Therefore, $v$ is not a coloop in the matchable sets matroid of $G$.
    $v$ was arbitrary, so every vertex is not a coloop in the matchable sets matroid of $G$.

    Let $u$ and $v$ be adjacent vertices of $G$.
    WTS: $\{u, v\}$ is a cocircuit or $E(G) \setminus \{u, v\}$ is a hyperplane.
    Since for every vertex $v$, there is a matching $M$ of $G$ of size $\nu(G)$ s.t. $v$ is not
    matched by $M$, the rank of $E(G) \setminus \{u\}$ is $2 \nu(G)$ and the rank of $E(G) \setminus \{v\}$
    is also $2 \nu(G)$.
    If $M$ does not match $v$, then we can extend $M$ to a bigger matching by adding the edge $uv$.
    so $v$ must be matched by $M$.
    Therefore, $E(G) \setminus \{u, v\}$ has rank $2 \nu(G) - 1$.
    As adding another element to $E(G) \setminus \{u, v\}$ increases the rank,
    $E(G) \setminus \{u, v\}$ is a closure.
    Since it has the rank $2 \nu(G) - 1$, it is a hyperplane.
    Therefore, $\{u, v\}$ is a cocircuit.
    $u$ and $v$ were arbitrary, so every pair of adjacent vertices is a series pair in the matchable sets matroid of $G$.
    \item[ii.] Consider a component $C$ of $G$.
    Then, by part i and the transitivity of series and parallel, $V(C)$ is a set whose two-element subsets
    are all series pairs.
    Therefore, the rank of $E(M) \setminus V(C)$ is $2 \nu(C) - |V(C)| + 1$.
    By diminishing return,
    \[|V(C)| - 1 = r(M) - r_M(E(M) \setminus V(C)) \leq r_M(V(C)) - r_M(\emptyset) = r_M(V(C))\]
    At the same time, $r_M(V(C)) < |V(C)|$ because a matching of $G$ is a disjoint union of matchings
    of each component and for each vertex, there is a matching of $G$ of size $\nu(G)$ that does
    not contain the vertex so the entire $V(C)$ is not matchable simultaneously.
    Therefore, $r_M(V(C)) = |V(C)| - 1$.
    Since $C$ was arbitrary, this is true for all components of $G$.
    Therefore, $G$ has a matching avoiding exactly one vertex from each of its components.
  \end{enumerate}
\end{proof}-/

lemma inessential_of_not_mem (hx : x ∉ V(G)) : G.inessential x := by
  sorry

lemma matchingMatroid.noColoop (h : ∀ x, G.inessential x) (hx : x ∈ V(G)) :
    ¬ G.matchingMatroid.IsColoop x := by
  sorry

lemma matchingMatroid.seriesPair_of_adj (h : ∀ x, G.inessential x) (h : G.Adj x y) :
    G.matchingMatroid.Series x y := by
  sorry

lemma foo_of_forall_inessential (h : ∀ x, G.inessential x) :
    ∃ M, G.IsMatching M ∧ ∀ H : Graph α β, H.IsCompOf G → ∃! x, x ∈ V(H) ∧ x ∉ V(G, M) := by
  sorry

/-
\subsection{Part (d)}
Let $G$ be a graph with vertex set $V$.
\begin{enumerate}
    \item[i.] Let $X \subseteq V$ be maximal such that $\nu(G - X) = \nu(G) - |X|$. Show
    using (d) that $\nu(G - X) = \frac{1}{2}(|V - X| - \text{odd}(G - X))$, where `odd'
    denotes the number of components with an odd number of vertices. Hence determine
    $\nu(G)$ in terms of $X$.
    \item[ii.] Show that $\nu(G) \leq \frac{1}{2}(|V| + |Y| - \text{odd}(G - Y))$ for all
    $Y \subseteq V$.
    \item[iii.] Conclude that $\nu(G) = \min_{Z \subseteq V} \frac{1}{2}(|V| + |Z| -
    \text{odd}(G - Z))$. This is the Tutte-Berge formula for the size of a maximum matching
    in an arbitrary graph.
\end{enumerate}

\begin{proof}
  \begin{enumerate}
    \item[i.] Let $X$ be maximal with $\nu(G-X)=\nu(G)-|X|$ and put $H := G-X$.
    WTS: $\nu(H-v)=\nu(H)$ for every $v\in V(H)$. Let $v\in V(H)$. Removing a vertex
    decreases the matching number by at most one, so
    $\nu(G-(X\cup\{v\})) \ge \nu(G) - |X| - 1$. If equality held, then
    $\nu(G-(X\cup\{v\})) = \nu(G) - (|X|+1)$, contradicting the maximality of $X$.
    Therefore $\nu(G-(X\cup\{v\})) \ge \nu(G)-|X| = \nu(H)$. Also
    $\nu(G-(X\cup\{v\})) \le \nu(H)$. Hence $\nu(H-v)=\nu(H)$.

    Let $C$ be any component of $H$ and $v\in V(C)$. Since $\nu(H-v)=\nu(H)$ and matching
    number is additive over components, we have $\nu(C-v)=\nu(C)$. If $|C|$ were even, then
    $|C-v|$ is odd and $\nu(C-v) \le \lfloor(|C|-1)/2\rfloor < |C|/2 \le \nu(C)$, a
    contradiction. Thus $|C|$ is odd and necessarily $\nu(C)=(|C|-1)/2$, with $C-v$ having a
    perfect matching for every $v\in V(C)$. Therefore each component of $H$ is
    of odd order. Therefore $H$ has a matching that leaves exactly one vertex unmatched in
    each component, and hence
    \[
      \nu(G-X)=\nu(H)=\frac12\big(|V(H)| - \text{odd}(H)\big) = \frac12\big(|V-X| - \text{odd}(G-X)\big).
    \]
    Using $\nu(G)=\nu(G-X)+|X|$, we obtain
    \[
      \nu(G) = |X| + \frac12\big(|V-X| - \text{odd}(G-X)\big)
      = \frac12\big(|V| + |X| - \text{odd}(G-X)\big).
    \]

    \item[ii.] For any $Y\subseteq V$, in $G-Y$ every odd component contributes at least one
    unmatched vertex to any matching, so
    \[
      \nu(G-Y) \le \frac12\big(|V-Y| - \text{odd}(G-Y)\big).
    \]
    Also, removing $Y$ can destroy at most $|Y|$ edges of a matching, so
    $\nu(G) \le \nu(G-Y) + |Y|$. Combining,
    \[
      \nu(G) \le \frac12\big(|V-Y| - \text{odd}(G-Y)\big) + |Y|
      = \frac12\big(|V| + |Y| - \text{odd}(G-Y)\big).
    \]

    \item[iii.] Let $X$ be as in (i). Then
    $\nu(G) = \frac12\big(|V| + |X| - \text{odd}(G-X)\big)$. By (ii), for every
    $Z\subseteq V$ we have $\nu(G) \le \frac12\big(|V| + |Z| - \text{odd}(G-Z)\big)$.
    Therefore
    \[
      \nu(G) = \min_{Z\subseteq V} \frac12\big(|V| + |Z| - \text{odd}(G-Z)\big),
    \]
    which is the Tutte--Berge formula.
  \end{enumerate}
\end{proof}
-/
lemma tutte_berge_of_maximal_vertexDelete (hX : Maximal (fun X ↦ ν(G - X) = ν(G) - X.encard) X) :
    2 * ν(G - X) = (V(G) \ X).encard - (G - X).OddComponents.encard := by
  sorry

lemma tutte_berge_le [G.Finite] :
    2 * ν(G) ≤ (V(G).encard + Y.encard) - (G - Y).OddComponents.encard := by

  sorry

lemma tutte_berge [G.Finite] :
    2 * ν(G) = ⨅ Z ⊆ V(G), (V(G).encard + Z.encard) - (G - Z).OddComponents.encard := by
  sorry

-- def HasPerfectMatching (G : Graph α β) : Prop :=
--   ∃ M, G.IsMatching M ∧ V(G, M) = V(G)

-- def IsFactorCritical (G : Graph α β) : Prop :=
--   ∀ v ∈ V(G), (G - {v}).HasPerfectMatching

-- lemma HasPerfectMatching.encard_even [G.Finite] (h : G.HasPerfectMatching) :
--     Even V(G).encard := by
--   -- Proof: A perfect matching partitions vertices into pairs, so |V| = 2 * |M|.
--   sorry

-- lemma IsFactorCritical.encard_odd [G.Finite] (h : G.IsFactorCritical) :
--     Odd V(G).encard := by
--   -- Proof: For any v, G-v has a perfect matching, so |V|-1 is even, implying |V| is odd.
--   sorry

-- lemma IsFactorCritical.hasPerfectMatching_of_vertexDelete [G.Finite] (h : G.IsFactorCritical)
--     (v : α) (hv : v ∈ V(G)) : (G - {v}).HasPerfectMatching := by
--   -- Proof: Follows directly from the definition.
--   sorry

-- def OddComponents (G : Graph α β) : Set (Graph α β) :=
--   {H | H.IsOddCompOf G}

-- noncomputable def maxMatchingSize (G : Graph α β) : ℕ∞ :=
--   sSup {n | ∃ M, G.IsMatching M ∧ n = M.encard}

-- def gallai_D (G : Graph α β) : Set α :=
--   {v | ∃ M, G.IsMaxMatching M ∧ v ∉ V(G, M)}

-- noncomputable def gallai_A (G : Graph α β) : Set α :=
--   N(G, G.gallai_D) \ G.gallai_D

-- noncomputable def gallai_C (G : Graph α β) : Set α :=
--   V(G) \ (G.gallai_D ∪ G.gallai_A)

-- lemma IsMatching.encard_le_div_two [G.Finite] (hM : G.IsMatching M) :
--     2 * M.encard ≤ V(G).encard := by
--   -- Proof: Each edge covers 2 vertices, and edges are disjoint. So 2|M| ≤ |V|.
--   sorry

-- lemma IsMatching.odd_comp_deficiency (hM : G.IsMatching M) {H : Graph α β} (hH : H.IsOddCompOf G) :
--     V(H).encard - 2 * (M ∩ E(H)).encard ≥ 1 := by
--   -- Proof: M restricted to H is a matching. 2|M_H| ≤ |V(H)|. Since |V(H)| is odd, strict inequality holds.
--   sorry

-- lemma sum_matching_in_components_eq (hM : G.IsMatching M) (U : Set α) :
--     (∑ᶠ H ∈ (G - U).OddComponents, (M ∩ E(H)).encard) + (M ∩ E(G[U])).encard + (M ∩ E(G, U)).encard = M.encard := by
--   -- Proof: Edges of M are disjoint. They are either in G[U], between U and G-U, or inside components of G-U.
--   -- No edge can connect two different components of G-U.
--   sorry

-- theorem tutte_berge_weak_duality [G.Finite] {M : Set β} (hM : G.IsMatching M)
--     {U : Set α} (hU : U ⊆ V(G)) :
--     (G - U).OddComponents.encard + 2 * M.encard ≤ V(G).encard + U.encard := by
--   -- Proof:
--   -- |V(G)| = |U| + sum(|V(K)| for K in G-U)
--   -- |M| = |M_U| + |M_cross| + sum(|M_K|)
--   -- Use |V(K)| ≥ 2|M_K| + 1 for odd K, and |V(K)| ≥ 2|M_K| for even K.
--   -- Rearrange terms to show the inequality.
--   sorry

-- lemma gallai_D_mem_iff (v : α) :
--     v ∈ G.gallai_D ↔ ∃ M, G.IsMaxMatching M ∧ v ∉ V(G, M) := by
--   -- Proof: Definition.
--   sorry

-- lemma gallai_D_component_factor_critical (C : Graph α β) (hC : C.IsCompOf G[G.gallai_D]) :
--     C.IsFactorCritical := by
--   -- Proof: Let v ∈ C. v ∈ D implies some max matching M misses v.
--   -- M must match C-{v} perfectly, otherwise we could augment M or find a larger deficiency.
--   sorry

-- lemma gallai_A_matched_to_D_explicit (hM : G.IsMaxMatching M) (v : α) (hv : v ∈ G.gallai_A) :
--     ∃ u ∈ G.gallai_D, ∃ e ∈ M, G.IsLink e v u := by
--   -- Proof: v ∈ A means v ∈ N(D) \ D. v cannot be unmatched (else v ∈ D).
--   -- v cannot be matched to A or C (structural properties of Gallai-Edmonds).
--   -- So v is matched to D.
--   sorry

-- lemma gallai_C_perfect_matching_explicit (hM : G.IsMaxMatching M) :
--     G[G.gallai_C].HasPerfectMatching := by
--   -- Proof: If not, C would contain an unmatched vertex in some max matching, putting it in D.
--   sorry

-- lemma maxMatchingSize_eq_gallai_formula [G.Finite] :
--     let H := G - G.gallai_A
--     2 * G.maxMatchingSize + H.OddComponents.encard = V(G).encard + G.gallai_A.encard := by
--   -- Proof: Construct M by:
--   -- 1. Perfect matchings in C.
--   -- 2. Matching each v ∈ A to a distinct component of D.
--   -- 3. Near-perfect matchings in components of D (leaving one root per component).
--   -- Count the size and show it meets the bound.
--   sorry

-- theorem tutte_berge [G.Finite] :
--     ∃ U ⊆ V(G),
--     (G - U).OddComponents.encard + 2 * G.maxMatchingSize = V(G).encard + U.encard := by
--   -- Proof: Use U = G.gallai_A and the previous formula.
--   sorry

end Graph
