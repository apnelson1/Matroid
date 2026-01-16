import Matroid.Graph.Matching.Defs

namespace Graph

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}
  {hM : G.IsMatching M} {P P' : WList α β}

open Set symmDiff WList

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

end Graph
