import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Matroid.Graph.Degree.Max
import Matroid.Graph.Minor.Conn
import Matroid.Graph.Hom
import Matroid.Graph.TopologicalMinor
import Matroid.ForMathlib.Data.Set.IndexedPartition
import Matroid.Graph.Planarity.CombMap.Basic


variable {α β E ι : Type*} {G C : Graph α β} {S T : Set α} {u v : α}

open Set Function WList IndexedPartition

namespace Graph

def Sym2Set (S : Sym2 (Set α)) : Set (Sym2 α) := by
  refine Sym2.lift ⟨fun A B ↦ (Function.uncurry Sym2.mk) '' (A ×ˢ B), fun A B ↦ ?_⟩ S
  ext s
  induction s with | h x y => _
  simp only [mem_image, mem_prod]
  grind

@[simps (attr := grind =)]
def CompletePartite (P : S.IndexedPartition ι) : Graph α (Sym2 α) where
  vertexSet := ⋃ i, P i
  edgeSet := ⋃ i, ⋃ j ≠ i, Sym2Set (s(P i, P j))
  IsLink e u v := e = s(u, v) ∧ ∃ i j, i ≠ j ∧ u ∈ P i ∧ v ∈ P j
  isLink_symm e he u v := by
    simp only [and_imp, forall_exists_index]
    rintro rfl i j hne hui hvj
    use Sym2.eq_swap, j, i, hne.symm, hvj, hui
  eq_or_eq_of_isLink_of_isLink e u v w z huv hwz := by grind
  edge_mem_iff_exists_isLink e := by
    simp only [ne_eq, Sym2Set, image_uncurry_prod, image2_curry, Sym2.lift_mk, mem_iUnion,
      mem_image, mem_prod]
    grind
  left_mem_of_isLink e u v he := by grind [mem_iUnion]

def IsPartite (G : Graph α β) (ι : Type*) : Prop :=
  ∃ P : V(G).IndexedPartition ι, ∀ i, (P i).Pairwise (¬ G.Adj · ·)

def IsCompletePartite (G : Graph α β) (ι : Type*) : Prop :=
  ∃ P : V(G).IndexedPartition ι, (∀ i, (P i).Pairwise (¬ G.Adj · ·)) ∧
    Pairwise ((fun A B ↦ ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) on P)

variable {ι : Type*} {P : S.IndexedPartition ι} {i j : ι}

lemma IsCompletePartite.isPartite (h : IsCompletePartite G ι) : IsPartite G ι := by
  obtain ⟨P, hP, hPp⟩ := h
  exact ⟨P, hP⟩

lemma completePartite_isCompletePartite (P : S.IndexedPartition ι) :
    (CompletePartite P).IsCompletePartite ι :=
  ⟨P.induce (by simp), fun i u ↦ by grind [Adj], fun i j hne u hui v hvj ↦ ⟨s(u, v), by grind⟩⟩

-- #exit

lemma K33_K5_lemma_aux1 (hCG : C ≤ G) (hC : C.IsCycle) (hu : u ∉ V(C)) (hv : v ∉ V(C)) (huv : u ≠ v)
    (hadj : G.Adj u v) (hu2 : (N(G, u) ∩ V(C)).Nontrivial) (hv2 : (N(G, v) ∩ V(C)).Nontrivial)
    (h : ∃ P, C.IsPath P ∧ (∀ x ∈ P, G.Adj u x ↔ x = P.first) ∧ (∀ x ∈ P, G.Adj v x ↔ x = P.last) ∧
      P.Nonempty) :
    (∃ P₁ P₂ : WList α β, C.IsPath P₁ ∧ C.IsPath P₂ ∧ (∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x) ∧
    (∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x) ∧ C.IsCyclicWalk (P₁ ++ P₂)) ∨ (∃ (K : _),
    Nonempty (Iso (CompleteBipartiteGraph 3 3) K) ∧ Nonempty (K.TopologicalMinor G)) := by
  classical
  obtain ⟨P, hPC, hpPtl, hpPdl, hPne⟩ := h
  have hPfv : ¬ G.Adj v P.first := by
    rw [hpPdl _ first_mem]
    exact hPne.first_ne_last_of_nodup hPC.nodup
  have hPlu : ¬ G.Adj u P.last := by
    rw [hpPtl _ last_mem]
    exact hPne.first_ne_last_of_nodup hPC.nodup |>.symm
  obtain ⟨Q, hQ, hQne, hQf, hQl, hPQ⟩ := hC.exists_compl_path hPC hPne
  obtain rfl := hC.toGraph_of_isCyclicWalk hPQ
  have hinPQ : ∀ x ∈ P ++ Q, x ∈ P ∨ x ∈ Q.vertex.tail.dropLast := by
    intro x hx
    rw [mem_append_iff_of_eq hQf, ← Q.mem_vertex, List.mem_iff_eq_head_or_mem_tail Q.vertex_ne_nil,
      Q.vertex_head, List.mem_iff_mem_dropLast_or_eq_getLast, List.getLast_tail, Q.vertex_getLast,
      ← hQf, ← hQl] at hx
    grind
    rw [← hQne.cons_tail]
    simp
  obtain huQ : ∃ u' ∈ Q.vertex.tail.dropLast, G.Adj u u' := by
    obtain ⟨u1, ⟨hu1u, hu1C⟩, u2, ⟨hu2u, hu2C⟩, hu12⟩ := hu2
    grind
  obtain hvQ : ∃ v' ∈ Q.vertex.tail.dropLast, G.Adj v v' := by
    obtain ⟨v1, ⟨hv1v, hv1C⟩, v2, ⟨hv2v, hv2C⟩, hv12⟩ := hv2
    grind
  have hQnt : Q.Nontrivial := by
    obtain ⟨u1, ⟨hu1u, hu1C⟩, u2, ⟨hu2u, hu2C⟩, hu12⟩ := hu2
    obtain ⟨q, hq, -⟩ : ∃ u' ∈ Q.vertex.tail.dropLast, G.Adj u u' := by grind
    match Q with
    | nil x => simp at hq
    | cons x e (nil y) => simp at hq
    | cons x e  (cons y f Q) => simp
  simp only [← hQne.vertex_tail, ← hQnt.tail_nonempty.vertex_dropLast, mem_vertex] at huQ hvQ

  let UQ := (Q.tail.dropLast.prefixUntil (G.Adj u)).cons Q.first hQne.firstEdge
  let VQ := (Q.tail.dropLast.suffixFromLast (G.Adj v)).concat hQne.lastEdge Q.last
  let uf := UQ.last
  let vl := VQ.first
  have huf : G.Adj u uf := ((Q.tail.dropLast.prefixUntil_last_eq_iff_prop huQ).mpr rfl).1
  have hvl : G.Adj v vl := by
    simpa [vl, VQ] using ((Q.tail.dropLast.suffixFromLast_first_eq_iff_prop hvQ).mpr rfl).1
  have hUQ_prefix : UQ.IsPrefix Q.dropLast := by
    rw [← hQne.cons_tail, hQnt.tail_nonempty.dropLast_cons]
    unfold UQ
    gcongr
    exact (Q.tail.dropLast.prefixUntil_isPrefix (G.Adj u))
  have hUQ_prefix' : UQ.IsPrefix Q := hUQ_prefix.trans Q.dropLast_isPrefix
  have hVQ_suffix : VQ.IsSuffix Q.tail := by
    rw [← hQne.concat_dropLast, hQnt.dropLast_nonempty.tail_concat, ← hQnt.tail_dropLast]
    unfold VQ
    gcongr
    exact Q.tail.dropLast.suffixFromLast_isSuffix (G.Adj v)
  have hVQ_suffix' : VQ.IsSuffix Q := hVQ_suffix.trans Q.tail_isSuffix
  have hUQ'_path : (P ++ Q).toGraph.IsPath UQ := by
    rw [← hPQ.ne_iff_isPath_of_isSublist <| hUQ_prefix'.isSublist.trans
      (isSuffix_append_left ..).isSublist, ← hQne.cons_tail]
    apply_fun WList.length
    grind [Q.tail.dropLast.suffixFromLast_isSuffix (G.Adj v) |>.isSublist.length_le]
  have hVQ'_path : (P ++ Q).toGraph.IsPath VQ := by
    rw [← hPQ.ne_iff_isPath_of_isSublist ((hVQ_suffix.trans Q.tail_isSuffix).trans
      (isSuffix_append_left ..)).isSublist]
    apply_fun WList.length
    grind [Q.tail.dropLast.suffixFromLast_isSuffix (G.Adj v) |>.isSublist.length_le]
  obtain hT | hF := em (uf ∈ VQ)
  · refine Or.inl ⟨P ++ UQ, VQ.suffixFromVertex uf, ?_, hVQ'_path.suffix
      (VQ.suffixFromVertex_isSuffix uf), ?_, ?_, ?_⟩
    · rw [← hPQ.ne_iff_isPath_of_isSublist (hUQ_prefix'.append_left P).isSublist, ← hQne.cons_tail]
      simp only [ne_eq, append_right_inj_iff, cons.injEq, true_and, UQ]
      intro heq
      have := (heq ▸ (prefixUntil_isPrefix ..)).antisymm Q.tail.dropLast_isPrefix
      exact hQnt.tail_nonempty.not_nil (dropLast_eq_self_iff _ |>.mp this.symm)
    · rintro x hx hux
      rw [append_vertex, cons_vertex, List.tail_append_of_ne_nil] at hx
      simp only [List.mem_append, List.mem_cons, List.dropLast_append_cons,
        List.dropLast_cons_of_ne_nil vertex_ne_nil] at hx
      obtain hxP | rfl | hxUQ := hx
      · obtain rfl := hpPtl x (List.mem_of_mem_dropLast <| List.mem_of_mem_tail hxP) |>.mp hux
        have := List.nodup_cons.mp <| List.cons_head_tail P.vertex_ne_nil ▸ hPC.nodup
        exact (P.vertex_head ▸ this).1 (List.mem_of_mem_dropLast <| List.tail_dropLast ▸ hxP)
      · exact hPne.not_nil <|
          hPC.first_eq_last_iff.mp (hpPtl P.last last_mem |>.mp (hQf ▸ hux)).symm
      · exact prefixUntil_vertex_dropLast_not_prop hxUQ hux
      · apply_fun List.length
        grind
    · rintro x hx hvx
      replace hx : x ∈ VQ.vertex.tail.dropLast :=
        (suffixFromVertex_isSuffix VQ uf).suffix.tail.dropLast.mem hx
      simp only [concat_vertex, ne_eq, vertex_ne_nil, not_false_eq_true, List.tail_append_of_ne_nil,
      List.cons_ne_self, List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil,
      VQ] at hx
      exact suffixFromLast_vertex_tail_not_prop hx hvx
    have hUQ_eq : UQ = Q.prefixUntilVertex uf := by
      have hufeqlast : (Q.tail.prefixUntil (G.Adj u)).last = uf :=
        congr_arg WList.last (Q.tail.dropLast_isPrefix.prefixUntil_eq_prefixUntil_of_exists huQ)
        |>.symm
      rw [← hQne.cons_tail, prefixUntilVertex_cons_of_ne _ (by grind)]
      unfold UQ
      rw [Q.tail.dropLast_isPrefix.prefixUntil_eq_prefixUntil_of_exists huQ, ← hufeqlast,
        Q.tail.prefixUntil_eq_prefixUntilVertex_last_of_nodup
          (hQ.nodup.sublist Q.tail_isSuffix.isSublist.sublist)]
    have hVQ_suf_eq : VQ.suffixFromVertex uf = Q.suffixFromVertex uf :=
      hVQ_suffix'.suffixFrom_eq_suffixFrom_of_forall (by grind) hQ.nodup
    rwa [append_assoc, hUQ_eq, hVQ_suf_eq, prefixUntilVertex_append_suffixFromVertex]
  right

  sorry
  /- Find the first neighbor of u in Q.tail, uf, and the last neighbor of v in Q.dropLast, vl.
  Such vertices exist because u and v have at least two neighbors in C, yet P contains only one
  neighbor each, P.first and P.last.
  If uf appears strictly before vl in Q, we have neighbor of u and v appearing alternatingly:
  P.first -- P.last -- uf -- vl -- P.first. Moreover, these four vertices are distinct, because
  1. P is nonempty so P.first ≠ P.last,
  2. uf is taken from Q.tail, so uf ≠ P.last = Q.first,
  3. uf appears strictly before vl so uf ≠ vl,
  4. vl is taken from Q.dropLast, so vl ≠ P.first = Q.last.
  We construct K3,3 by contracting all but one edge between P.first -- P.last, P.last -- uf,
  uf -- vl, and vl -- P.first.
  P.first, uf, and v forms one part of K3,3, and the other part is P.last, vl, and u.

  Otherwise, either uf = vl or uf appears after vl in Q. Then, traversing C from P.first, the first
  neighbor of u is uf so take the path between them as P₁ and the rest of C as P₂. By construction,
  P₁ is internally disjoint from N(G, u). P₂ is internally disjoint from N(G, v) because vl is the
  last neighbor of v in Q.dropLast so after vl, no neighbor of v appears and all of P₂ is after vl.
  -/

lemma K33_K5_lemma_aux2 (hCG : C ≤ G) (hC : C.IsCycle) (hu : u ∉ V(C)) (hv : v ∉ V(C)) (huv : u ≠ v)
    (hadj : G.Adj u v) (hu2 : (N(G, u) ∩ V(C)).Nontrivial) (hv2 : (N(G, v) ∩ V(C)).Nontrivial)
    (h : ∀ P, C.IsPath P → (∀ x ∈ P, G.Adj u x ↔ x = P.first) → (∀ x ∈ P, G.Adj v x ↔ x = P.last) →
      P.Nil) :
    (∃ P₁ P₂ : WList α β, C.IsPath P₁ ∧ C.IsPath P₂ ∧ (∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x) ∧
    (∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x) ∧ C.IsCyclicWalk (P₁ ++ P₂)) ∨
    (∃ (K : _), Nonempty (Iso (CompleteBipartiteGraph 3 3) K) ∧ Nonempty (K.TopologicalMinor G)) ∨
    (∃ (K : _), Nonempty (Iso (CompleteGraph 5) K) ∧ Nonempty (K.TopologicalMinor G)) := by
  have h1 : ∀ x ∈ V(C), ∃ y ∈ V(C), x ≠ y ∧ G.Adj u y ∧ G.Adj v y := by
    intro x hxC
    obtain ⟨P, hP, hPeq⟩ := hC.deleteVerts_singleton_isPathGraph (hu2.mono inter_subset_right) hxC
    have := congr_arg vertexSet hPeq
    simp only [vertexSet_deleteVerts, toGraph_vertexSet, Set.ext_iff, mem_diff, mem_singleton_iff,
      mem_vertexSet_iff] at this
    obtain ⟨P', hP'in, ⟨huf, hvl, hP'tl, hP'dl⟩ | ⟨hvl, huf, hP'tl, hP'dl⟩⟩ :=
      P.exists_infix_of_exists_prop (p := G.Adj u) (q := G.Adj v) (by grind [hu2.exists_ne x])
      (by grind [hv2.exists_ne x])
    · have hP'path := hP.infix hP'in |>.of_le deleteVerts_le
      specialize h P' hP'path (fun x hx ↦ ?_) fun x hx ↦ ?_
      · obtain heq | ⟨hne, htl⟩ := hP'path.nodup.eq_head_or_mem_tail_ne hx <;> grind
      · obtain heq | ⟨hne, hdl⟩ := hP'path.nodup.eq_getLast_or_mem_dropLast_ne hx <;> grind
      exact ⟨P'.first, hP'path.vertexSet_subset first_mem, Ne.symm (hP.infix hP'in
        |>.vertexSet_subset first_mem |>.2), huf, h.first_eq_last ▸ hvl⟩
    have hP'path := hP.infix hP'in |>.of_le deleteVerts_le
    specialize h P'.reverse hP'path.reverse (fun x hx ↦ ?_) fun x hx ↦ ?_
    · obtain heq | ⟨hne, htl⟩ := hP'path.nodup.eq_getLast_or_mem_dropLast_ne (by simpa using hx)
      <;> grind
    · obtain heq | ⟨hne, hdl⟩ := hP'path.nodup.eq_head_or_mem_tail_ne (by simpa using hx) <;> grind
    simp only [reverse_nil_iff] at h
    exact ⟨P'.first, hP'path.vertexSet_subset first_mem, Ne.symm (hP.infix hP'in
      |>.vertexSet_subset first_mem |>.2), h.first_eq_last ▸ huf, hvl⟩
  obtain ⟨x, hxC, -, hux, hvx⟩ := h1 hu2.nonempty.some hu2.nonempty.some_mem.2
  obtain ⟨y, hyC, hxy, huy, hvy⟩ := h1 x hxC
  clear h1 hu2 hv2
  obtain ⟨Pxy, Pyx, hPxy, hPyx, rfl, rfl, hPxytl, hPyxdl, hC⟩ := hC.exists_two_paths_of_ne hxC hyC
    hxy
  let P : α → WList α β → Prop := fun a p ↦ ∃ x ∈ p.vertex.tail.dropLast, G.Adj a x
  have : ((¬ P u Pxy ∧ ¬ P v Pyx) ∨ (¬ P v Pxy ∧ ¬ P u Pyx)) ∨ ((P u Pxy ∧ P u Pyx) ∨
    (P v Pxy ∧ P v Pyx)) ∨ ((P u Pxy ∧ P v Pxy) ∨ (P u Pyx ∧ P v Pyx)) := by
    grind
  refine this.imp3 ?_ ?_ ?_
  · simp only [not_exists, not_and, P]
    rintro (⟨huxy, hvyx⟩ | ⟨hvxy, huyx⟩)
    · use Pxy, Pyx, hPxy, hPyx, huxy, hvyx
    · use Pyx, Pxy, hPyx, hPxy, huyx, hvxy
      exact (rotate_eq_append hPyxdl.symm hPxytl.symm) ▸ hC.rotate Pxy.length
  · rintro (⟨huxy, huyx⟩ | ⟨hvxy, hvyx⟩)
    · sorry
    · sorry
  rintro (⟨huxy, hvxy⟩ | ⟨huyx, hvyx⟩)
  · sorry
  · sorry


  /- Let a path satisfying the condition of `h` be path of change.
  First, we show that there are at least two paths of change.
  Take some neighbor of u in C, u₁ and some neighbor of v in C, v₁. Then, C is partitioned into two
  trails, one from u₁ to v₁ and v₁ to u₁. From `exists_infix_of_prop` we get that each of these
  trails has a path of change.
  By assumption, both of these paths are a single vertex path. Let those vertices be x and y.
  Then, C is partitioned into two paths, one from x to y and one from y to x.
  If both paths internally have a neighbor of u, then we can construct a K3,3 similar to the
  construction in `K33_K5_lemma_aux1`.
  WLOG, assume that all neighbors of u appear in x-y path leaving y-x path internally disjoint with
  neighbors of u.
  If any neighbor of v appears in x-y path, then `exists_infix_of_exists_prop` gives us another
  path of change, nil z. Then, x, y and z form a K5 together with u and v.
  Otherwise, all neighbors of v must appear in y-x path leaving x-y path internally disjoint with
  neighbors of v.
  Therefore, x-y path and y-x path is the two paths as desired.-/

lemma K33_K5_lemma (hCG : C ≤ G) (hC : IsCycle C) (hu : u ∉ V(C)) (hv : v ∉ V(C)) (huv : u ≠ v)
    (hadj : G.Adj u v) (hu2 : (N(G, u) ∩ V(C)).Nontrivial) (hv2 : (N(G, v) ∩ V(C)).Nontrivial) :
    (∃ P₁ P₂ : WList α β, C.IsPath P₁ ∧ C.IsPath P₂ ∧ (∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x) ∧
    (∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x) ∧ C.IsCyclicWalk (P₁ ++ P₂)) ∨
    (∃ (K : _), Nonempty (Iso (CompleteBipartiteGraph 3 3) K) ∧ Nonempty (K.TopologicalMinor G)) ∨
    (∃ (K : _), Nonempty (Iso (CompleteGraph 5) K) ∧ Nonempty (K.TopologicalMinor G)) := by
  by_cases h : ∃ P, C.IsPath P ∧ (∀ x ∈ P, G.Adj u x ↔ x = P.first) ∧
    (∀ x ∈ P, G.Adj v x ↔ x = P.last) ∧ P.Nonempty
  · rw [← or_assoc]
    left
    exact K33_K5_lemma_aux1 hCG hC hu hv huv hadj hu2 hv2 h
  push Not at h
  exact K33_K5_lemma_aux2 hCG hC hu hv huv hadj hu2 hv2 h

-- lemma Kuratowski_aux_1 {G : Graph α β} [G.Finite] (hK5 : ∀ K, Nonempty (Iso (CompleteGraph 5) K) →
--     IsEmpty (K.TopologicalMinor G)) (hK33 : ∀ K, Nonempty (Iso (CompleteBipartiteGraph 3 3) K) →
--     IsEmpty (K.TopologicalMinor G)) : ∃ M : CombinatorialMap G (IncidenceType α β),
--     M.EulerCharacteristic = 1 := by
--   refine Finite.inductionOn_edgeSet G ?_ (P := fun H hH ↦ ∃ M : CombinatorialMap H (IncidenceType α β),
--     M.EulerCharacteristic = 1)
--   rintro H _ hH
--   wlog h3 : 3 < V(H).encard
--   · simp only [not_lt] at h3
--     sorry
--   wlog hconn3 : H.ConnGE 3
--   · obtain ⟨C, hHC, hC3⟩ := exists_isSepSet_encard_lt_of_not_connGE (by norm_cast) hconn3

--     sorry


  -- sorry


-- theorem K33_not_planar (f : (CompleteBipartiteGraph 3 3).Realization → E)
--     (hf : Topology.IsEmbedding f) : ∃ C : Set E, IsCircuit C ∧ C ⊆ range f ∧ IsConnected Cᶜ := by
--   sorry
