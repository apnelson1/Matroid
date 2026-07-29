import Matroid.Graph.Degree.Max
import Matroid.Graph.Planarity.Obstructions

variable {α β : Type*} {G C : Graph α β} {u v : α}

open Set WList

namespace Graph

lemma prefixUntilLast_append_suffixFromLast (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.prefixUntilLast P ++ w.suffixFromLast P = w := by
  have hends : (w.prefixUntilLast P).last = (w.suffixFromLast P).first := by
    simp only [prefixUntilLast, suffixFromLast, reverse_last, reverse_first]
    exact (w.reverse.prefixUntil_last_eq_suffixFrom_first P).symm
  rw [← reverse_inj_iff, reverse_append hends, prefixUntilLast, suffixFromLast, reverse_reverse,
    reverse_reverse, prefixUntil_append_suffixFrom]

lemma K33_K5_lemma_aux1 (hCG : C ≤ G) (hC : C.IsCycle) (hu : u ∉ V(C)) (hv : v ∉ V(C)) (huv : u ≠ v)
    (hadj : G.Adj u v) (hu2 : (N(G, u) ∩ V(C)).Nontrivial) (hv2 : (N(G, v) ∩ V(C)).Nontrivial)
    (h : ∃ P, C.IsPath P ∧ (∀ x ∈ P, G.Adj u x ↔ x = P.first) ∧ (∀ x ∈ P, G.Adj v x ↔ x = P.last) ∧
      P.Nonempty) :
    (∃ P₁ P₂ : WList α β, C.IsPath P₁ ∧ C.IsPath P₂ ∧ (∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x) ∧
    (∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x) ∧ C.IsCyclicWalk (P₁ ++ P₂)) ∨
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G := by
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
  have hUQ_path : (P ++ Q).toGraph.IsPath UQ := by
    rw [← hPQ.ne_iff_isPath_of_isSublist <| hUQ_prefix'.isSublist.trans
      (isSuffix_append_left ..).isSublist, ← hQne.cons_tail]
    apply_fun WList.length
    grind [Q.tail.dropLast.suffixFromLast_isSuffix (G.Adj v) |>.isSublist.length_le]
  have hVQ_path : (P ++ Q).toGraph.IsPath VQ := by
    rw [← hPQ.ne_iff_isPath_of_isSublist ((hVQ_suffix.trans Q.tail_isSuffix).trans
      (isSuffix_append_left ..)).isSublist]
    apply_fun WList.length
    grind [Q.tail.dropLast.suffixFromLast_isSuffix (G.Adj v) |>.isSublist.length_le]
  -- In one cyclic order the two required clean paths are already visible. In the other, the four
  -- alternating arcs are exactly the input expected by the one-off `K₃,₃` constructor.
  obtain hT | hF := em (uf ∈ VQ)
  · refine Or.inl ⟨P ++ UQ, VQ.suffixFromVertex uf, ?_, hVQ_path.suffix
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
  -- Middle arc of Q from the first u-neighbor uf to the last v-neighbor vl.
  let R := (Q.tail.dropLast.prefixUntilLast (G.Adj v)).suffixFrom (G.Adj u)
  have hPluf : P.last ≠ uf := fun h ↦ hPlu (h ▸ huf)
  have hufvl : uf ≠ vl := fun h ↦ hF (h ▸ first_mem)
  have hUQne : UQ.Nonempty := by simp [UQ]
  have hVQne : VQ.Nonempty := by simp [VQ]
  have hR_path : (P ++ Q).toGraph.IsPath R :=
    hQ.sublist <|
      (((Q.tail.dropLast.prefixUntilLast (G.Adj v)).suffixFrom_isSuffix (G.Adj u)).isSublist.trans
        (Q.tail.dropLast.prefixUntilLast_isPrefix (G.Adj v)).isSublist).trans
      (Q.tail.dropLast_isPrefix.isSublist.trans Q.tail_isSuffix.isSublist)
  let Wmid := Q.tail.dropLast
  have hufmid : uf ∈ Wmid := by
    have hufQdl : uf ∈ Q.dropLast := hUQ_prefix.mem last_mem
    rw [← hQne.cons_tail, hQnt.tail_nonempty.dropLast_cons] at hufQdl
    obtain heq | huf := mem_cons_iff.mp hufQdl
    · exact (hPluf (hQf.trans heq.symm)).elim
    exact huf
  have huf_not_suf : uf ∉ Wmid.suffixFromLast (G.Adj v) := fun huf ↦
    hF (by simpa [VQ, mem_concat] using Or.inl huf)
  have hufpre : uf ∈ Wmid.prefixUntilLast (G.Adj v) := by
    rw [← prefixUntilLast_append_suffixFromLast Wmid (G.Adj v)] at hufmid
    exact (mem_of_mem_append hufmid).resolve_right huf_not_suf
  have hpre_eq : (Wmid.prefixUntilLast (G.Adj v)).prefixUntil (G.Adj u) =
      Wmid.prefixUntil (G.Adj u) :=
    Wmid.prefixUntilLast_isPrefix (G.Adj v) |>.prefixUntil_eq_prefixUntil_of_exists
      ⟨uf, hufpre, huf⟩
  have hpre : Wmid.prefixUntilLast (G.Adj v) = Wmid.prefixUntil (G.Adj u) ++ R := by
    unfold R
    rw [← hpre_eq, prefixUntil_append_suffixFrom]
  have hmid : Wmid = Wmid.prefixUntil (G.Adj u) ++ R ++ Wmid.suffixFromLast (G.Adj v) := by
    rw [← hpre]
    exact (prefixUntilLast_append_suffixFromLast Wmid (G.Adj v)).symm
  have hRfirst : R.first = uf := by
    change ((Wmid.prefixUntilLast (G.Adj v)).suffixFrom (G.Adj u)).first = uf
    rw [← prefixUntil_last_eq_suffixFrom_first, hpre_eq]
    rfl
  have hRlast : R.last = vl := by
    change ((Wmid.prefixUntilLast (G.Adj v)).suffixFrom (G.Adj u)).last = vl
    rw [suffixFrom_last]
    have : (Wmid.prefixUntilLast (G.Adj v)).last = (Wmid.suffixFromLast (G.Adj v)).first := by
      simp only [prefixUntilLast, suffixFromLast, reverse_last, reverse_first]
      exact (Wmid.reverse.prefixUntil_last_eq_suffixFrom_first (G.Adj v)).symm
    simpa [vl, VQ, Wmid] using this
  have hRne : R.Nonempty := (first_ne_last_iff hR_path.nodup).mp (hRfirst ▸ hRlast ▸ hufvl)
  have hUQ_first : UQ.first = P.last := by simp [UQ, hQf]
  have hUQlast : UQ.last = R.first := hRfirst.symm
  have hR_VQ : R.last = VQ.first := hRlast
  have hQeq : Q = UQ ++ R ++ VQ := by
    change Q = cons Q.first hQne.firstEdge (Wmid.prefixUntil (G.Adj u)) ++ R ++
      (Wmid.suffixFromLast (G.Adj v)).concat hQne.lastEdge Q.last
    refine hQne.concat_dropLast.symm.trans ?_
    have hdrop : Q.dropLast = cons Q.first hQne.firstEdge Wmid :=
      (congr_arg WList.dropLast hQne.cons_tail).symm.trans
        (hQnt.tail_nonempty.dropLast_cons Q.first hQne.firstEdge)
    rw [hdrop]
    conv_lhs => rw [hmid]
    rw [cons_concat, cons_append, ← WList.append_concat, ← cons_append]
  letI : Inhabited α := ⟨P.first⟩
  have hdec_RVQ : (R ++ VQ).DecomposeTo [R, VQ] :=
    (DecomposeTo.append_cons_iff hR_VQ (by simp)).mpr ⟨by simp, by simp [appendList], by simp⟩
  have hdec_UQRVQ : (UQ ++ (R ++ VQ)).DecomposeTo [UQ, R, VQ] :=
    (DecomposeTo.append_cons_iff (by simpa [append_first_of_eq hR_VQ] using hUQlast)
      (by simp)).mpr hdec_RVQ
  have hdec : (P ++ Q).DecomposeTo [P, UQ, R, VQ] := by
    rw [hQeq, append_assoc]
    exact (DecomposeTo.append_cons_iff (by simpa [append_first_of_nonempty hUQne] using
      hUQ_first.symm) (by simp)).mpr hdec_UQRVQ
  exact isTopologicalMinor_completeBipartiteGraph_of_alternating_cycle
    (hPQ.of_le hCG) hdec hPne hUQne hRne hVQne
    (by simpa using hu) (by simpa using hv) huv
    (hpPtl P.first first_mem |>.mpr rfl) huf
    (hpPdl P.last last_mem |>.mpr rfl) (by simpa [hRlast] using hvl) hadj

lemma K33_K5_lemma_aux2 (hCG : C ≤ G) (hC : C.IsCycle) (hu : u ∉ V(C)) (hv : v ∉ V(C)) (huv : u ≠ v)
    (hadj : G.Adj u v) (hu2 : (N(G, u) ∩ V(C)).Nontrivial) (hv2 : (N(G, v) ∩ V(C)).Nontrivial)
    (h : ∀ P, C.IsPath P → (∀ x ∈ P, G.Adj u x ↔ x = P.first) → (∀ x ∈ P, G.Adj v x ↔ x = P.last) →
      P.Nil) :
    (∃ P₁ P₂ : WList α β, C.IsPath P₁ ∧ C.IsPath P₂ ∧ (∀ x ∈ P₁.vertex.tail.dropLast, ¬ G.Adj u x) ∧
    (∀ x ∈ P₂.vertex.tail.dropLast, ¬ G.Adj v x) ∧ C.IsCyclicWalk (P₁ ++ P₂)) ∨
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G ∨
    (CompleteGraph 5).IsTopologicalMinor G := by
  have h1 : ∀ x ∈ V(C), ∃ y ∈ V(C), x ≠ y ∧ G.Adj u y ∧ G.Adj v y := by
    intro x hxC
    obtain ⟨P, hP, hPeq⟩ := hC.deleteVerts_singleton_isPathGraph (hu2.mono inter_subset_right) hxC
    have := congr_arg vertexSet hPeq
    simp only [vertexSet_deleteVerts, toGraph_vertexSet, Set.ext_iff, mem_sdiff, mem_singleton_iff,
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
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G ∨
    (CompleteGraph 5).IsTopologicalMinor G := by
  by_cases h : ∃ P, C.IsPath P ∧ (∀ x ∈ P, G.Adj u x ↔ x = P.first) ∧
    (∀ x ∈ P, G.Adj v x ↔ x = P.last) ∧ P.Nonempty
  · rw [← or_assoc]
    left
    exact K33_K5_lemma_aux1 hCG hC hu hv huv hadj hu2 hv2 h
  push Not at h
  exact K33_K5_lemma_aux2 hCG hC hu hv huv hadj hu2 hv2 h

/- The intended conclusion of this unfinished theorem has not yet been specified.
lemma Kuratowski_aux_1 [G.Finite] (hcon : G.Connected) (hK5 : ∀ K, Nonempty
    (Iso (CompleteGraph 5) K) → IsEmpty (K.TopologicalMinor G)) (hK33 : ∀ K, Nonempty
    (Iso (CompleteBipartiteGraph 3 3) K) → IsEmpty (K.TopologicalMinor G)) :
     := by
  generalize hm : E(G).ncard = m
  induction m using Nat.strong_induction_on with | h m ih => _
  subst m
  wlog h3 : 3 < V(G).ncard
  · simp only [not_lt] at h3

    sorry
  wlog hconn3 : G.ConnGE 3
  · obtain ⟨C, hHC, hC3⟩ := exists_isSepSet_encard_lt_of_not_connGE (by norm_cast) hconn3

    sorry


  -- sorry
-/


-- theorem K33_not_planar (f : (CompleteBipartiteGraph 3 3).Realization → E)
--     (hf : Topology.IsEmbedding f) : ∃ C : Set E, IsCircuit C ∧ C ⊆ range f ∧ IsConnected Cᶜ := by
--   sorry
