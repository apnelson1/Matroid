import Matroid.Graph.Connected.Set.SetEnsemble

open Set Graph.SetEnsemble

variable {α β : Type*} {G : Graph α β} {A : G.SetEnsemble} {S T : Set α} {P : WList α β}

namespace WList

/-! ### Legs -/

structure IsRightLeg (P : WList α β) (A : G.SetEnsemble) (S T : Set α)
  extends G.IsPathFrom A.vertexSet T P where
  between : A.between S T
  inter_left : V(P) ∩ S ⊆ {P.first}

namespace IsRightLeg

noncomputable def Q (h : P.IsRightLeg A S T) : WList α β := A.of_vertex P.first h.first_mem

@[simp]
lemma Q_mem (h : P.IsRightLeg A S T) : h.Q ∈ A.paths :=
  A.of_vertex_mem_setEnsemble h.first_mem

@[simp]
lemma first_mem_path (h : P.IsRightLeg A S T) : P.first ∈ h.Q := by
  exact mem_of_vertex ..

def ofIsPathFrom (hAST : A.between S T) (hP : G.IsPathFrom S T P) (hex : ∃ u ∈ P, u ∈ A.vertexSet)
    [DecidablePred (· ∈ A.vertexSet)] : IsRightLeg (P.suffixFromLast (· ∈ A.vertexSet)) A S T where
  toIsPathFrom := hP.suffixFromLast hex
  between := hAST
  inter_left := by
    rintro x ⟨hxP, hxS⟩
    have hsf := P.suffixFromLast_isSuffix (· ∈ A.vertexSet)
    obtain rfl := hP.eq_first_of_mem (hsf.subset hxP) hxS
    have heq := hsf.eq_of_first_mem hP.nodup hxP
    rw [heq]
    rfl

noncomputable def Q1 (h : P.IsRightLeg A S T) : WList α β := by
  classical
  exact h.Q.prefixUntilVertex P.first

@[simp]
lemma first_mem_Q1 (h : P.IsRightLeg A S T) : P.first ∈ h.Q1 := by
  classical
  exact (h.Q.prefixUntilVertex_last h.first_mem_path) ▸ last_mem

@[simp]
lemma Q1_isPrefix (h : P.IsRightLeg A S T) : h.Q1.IsPrefix h.Q := by
  classical
  exact prefixUntilVertex_isPrefix ..

@[simp]
lemma Q1_isPath (h : P.IsRightLeg A S T) : G.IsPath h.Q1 :=
  h.between h.Q_mem |>.isPath.prefix h.Q1_isPrefix

@[simp]
lemma Q1_first (h : P.IsRightLeg A S T) : h.Q1.first = h.Q.first := by
  classical
  exact prefixUntilVertex_first ..

@[simp]
lemma Q1_last (h : P.IsRightLeg A S T) : h.Q1.last = P.first := by
  classical
  unfold Q1
  have := h.Q.prefixUntil_prop_last (P := (· == P.first)) <| by simp
  simpa only [beq_iff_eq] using this

@[simp]
lemma Q1_subset_vertexSet (h : P.IsRightLeg A S T) : V(h.Q1) ⊆ A.vertexSet :=
  h.Q1_isPrefix.subset.trans <| A.subset_vertexSet_of_mem
  <| A.of_vertex_mem_setEnsemble h.first_mem

lemma P_inter_Q1 (h : P.IsRightLeg A S T) : V(P) ∩ V(h.Q1) = {P.first} := by
  rw [eq_singleton_iff_unique_mem]
  simp only [mem_inter_iff, mem_vertexSet_iff, first_mem, h.Q1_last ▸ last_mem, and_self, and_imp,
    true_and]
  exact fun x hxP hxQ1 ↦ h.eq_first_of_mem hxP (h.Q1_subset_vertexSet hxQ1)

lemma Q1_inter_right (h : P.IsRightLeg A S T) : V(h.Q1) ∩ T ⊆ {P.first} := by
  rintro x ⟨hxQ1, hxT⟩
  obtain rfl := (h.between h.Q_mem).eq_last_of_mem (h.Q1_isPrefix.subset hxQ1) hxT
  simp [← h.Q1_isPrefix.eq_of_last_mem (h.between h.Q_mem).nodup hxQ1]

lemma Q1_disjoint_right_of_nonempty (h : P.IsRightLeg A S T) (hP : P.Nonempty) :
    Disjoint V(h.Q1) T := by
  rw [disjoint_iff_forall_notMem]
  rintro x hxQ1 hxT
  obtain rfl := h.Q1_inter_right ⟨hxQ1, hxT⟩
  exact (first_ne_last_iff h.nodup).mpr hP <| h.eq_last_of_mem first_mem hxT

noncomputable def Q2 (h : P.IsRightLeg A S T) : WList α β := by
  classical
  exact h.Q.suffixFromVertex P.first

@[simp]
lemma first_mem_Q2 (h : P.IsRightLeg A S T) : P.first ∈ h.Q2 := by
  classical
  exact (h.Q.suffixFromVertex_first h.first_mem_path) ▸ first_mem

@[simp]
lemma Q2_isSuffix (h : P.IsRightLeg A S T) : h.Q2.IsSuffix h.Q := by
  classical
  exact suffixFromVertex_isSuffix ..

@[simp]
lemma Q2_isPath (h : P.IsRightLeg A S T) : G.IsPath h.Q2 := by
  classical
  exact h.between h.Q_mem |>.isPath.suffix h.Q2_isSuffix

@[simp]
lemma Q2_first (h : P.IsRightLeg A S T) : h.Q2.first = P.first := by
  classical
  unfold Q2
  have := h.Q.suffixFrom_prop_first (P := (· == P.first)) <| by simp
  simpa only [beq_iff_eq] using this

@[simp]
lemma Q2_last (h : P.IsRightLeg A S T) : h.Q2.last = h.Q.last := by
  classical
  exact suffixFromVertex_last ..

@[simp]
lemma Q2_subset_vertexSet (h : P.IsRightLeg A S T) : V(h.Q2) ⊆ A.vertexSet :=
  h.Q2_isSuffix.subset.trans <| A.subset_vertexSet_of_mem
  <| A.of_vertex_mem_setEnsemble h.first_mem

@[simp]
lemma Q1_append_Q2 (h : P.IsRightLeg A S T) : h.Q1 ++ h.Q2 = h.Q := by
  classical
  exact prefixUntil_append_suffixFrom ..

lemma P_inter_Q2 (h : P.IsRightLeg A S T) : V(P) ∩ V(h.Q2) = {P.first} := by
  rw [eq_singleton_iff_unique_mem]
  simp only [mem_inter_iff, mem_vertexSet_iff, first_mem, h.Q2_first ▸ first_mem, and_self, and_imp,
    true_and]
  exact fun x hxP hxQ2 ↦ h.eq_first_of_mem hxP (h.Q2_subset_vertexSet hxQ2)

lemma Q1_inter_Q2 (h : P.IsRightLeg A S T) : V(h.Q1) ∩ V(h.Q2) = {P.first} := by
  convert (h.Q1_append_Q2 ▸ (h.between h.Q_mem).isPath).inter_eq_singleton_of_append
    (by simp) using 2
  exact (Q1_last h).symm

lemma Q2_inter_left (h : P.IsRightLeg A S T) : V(h.Q2) ∩ S ⊆ {P.first} := by
  rintro x ⟨hxQ2, hxS⟩
  obtain rfl := (h.between h.Q_mem).eq_first_of_mem (h.Q2_isSuffix.subset hxQ2) hxS
  simp [← h.Q2_isSuffix.eq_of_first_mem (h.between h.Q_mem).nodup hxQ2]

lemma Q2_inter_right (h : P.IsRightLeg A S T) : V(h.Q2) ∩ T = {h.Q.last} := by
  rw [eq_singleton_iff_unique_mem]
  simp only [mem_inter_iff, mem_vertexSet_iff, h.Q2_last ▸ last_mem, (h.between h.Q_mem).last_mem,
    and_self, and_imp, true_and]
  exact fun x hxQ2 ↦ (h.between h.Q_mem).eq_last_of_mem (h.Q2_isSuffix.subset hxQ2)

noncomputable def bQ2 (h : P.IsRightLeg A S T) : WList α β := by
  classical
  exact P.reverse ++ h.Q2

@[simp]
lemma bQ2_isPath (h : P.IsRightLeg A S T) : G.IsPath h.bQ2 := by
  classical
  unfold bQ2
  refine h.isPath.reverse.append h.Q2_isPath (by simp) ?_
  simp only [mem_reverse, reverse_last]
  exact fun x hP hQ2 ↦ h.eq_first_of_mem hP <| h.Q2_subset_vertexSet hQ2

@[simp]
lemma bQ2_first (h : P.IsRightLeg A S T) : h.bQ2.first = P.last := by
  simp [bQ2]

@[simp]
lemma bQ2_last (h : P.IsRightLeg A S T) : h.bQ2.last = h.Q.last := by
  simp [bQ2]

@[simp]
lemma bQ2_vertexSet (h : P.IsRightLeg A S T) : V(h.bQ2) = V(P) ∪ V(h.Q2) := by
  simp [bQ2]

@[simp]
lemma first_mem_bQ2 (h : P.IsRightLeg A S T) : P.first ∈ h.bQ2 := by
  rw [← mem_vertexSet_iff]
  simp

lemma bQ2_inter_left (h : P.IsRightLeg A S T) : V(h.bQ2) ∩ S ⊆ {P.first} := by
  rw [bQ2_vertexSet, union_inter_distrib_right, union_subset_iff]
  use h.inter_left, h.Q2_inter_left

lemma bQ2_inter_right (h : P.IsRightLeg A S T) : V(h.bQ2) ∩ T = {h.bQ2.first, h.bQ2.last} := by
  rw [bQ2_vertexSet, union_inter_distrib_right]
  simp [h.vertexSet_inter_right, h.Q2_inter_right, pair_comm]

lemma bQ2_inter_vertexSet (h : P.IsRightLeg A S T) : V(h.bQ2) ∩ A.vertexSet = V(h.Q2) := by
  rw [bQ2_vertexSet, union_inter_distrib_right, h.vertexSet_inter_left, inter_eq_left.mpr (by simp)]
  simp

lemma Q1_isPathFrom (h : P.IsRightLeg A S T) : G.IsPathFrom S (T ∪ V(h.bQ2)) h.Q1 where
  toIsPath := h.Q1_isPath
  first_mem := by
    simp only [Q1_first]
    exact h.between h.Q_mem |>.first_mem
  last_mem := by simp
  eq_first_of_mem := by
    simp only [Q1_first]
    exact fun x hxQ1 hxS ↦ h.between h.Q_mem |>.eq_first_of_mem (h.Q1_isPrefix.subset hxQ1) hxS
  eq_last_of_mem := by
    simp only [bQ2_vertexSet, mem_union, mem_vertexSet_iff, Q1_last]
    rintro x hxQ1 (hxT | hxP | hxQ2)
    · exact h.Q1_inter_right ⟨hxQ1, hxT⟩
    · exact h.eq_first_of_mem hxP <| h.Q1_subset_vertexSet hxQ1
    exact h.Q1_inter_Q2.subset ⟨hxQ1, hxQ2⟩

lemma path_remove_Q_disjoint_bQ2 (h : P.IsRightLeg A S T) :
    Disjoint (A.path_remove h.Q).vertexSet V(h.bQ2) := by
  rw [h.bQ2_vertexSet, disjoint_union_right]
  have hdj := A.path_remove_vertexSet_disjoint h.Q_mem
  refine ⟨?_, hdj.mono_right h.Q2_isSuffix.subset⟩
  rw [disjoint_iff_forall_notMem] at hdj ⊢
  rintro x hxQ hxP
  obtain rfl := h.eq_first_of_mem hxP <| by simp_all
  exact hdj hxQ (A.mem_of_vertex h.first_mem)

@[simp]
noncomputable def shorten (h : P.IsRightLeg A S T) : G.SetEnsemble := by
  classical
  exact A.shorten h.Q (Q := h.Q1) (h.Q.prefixUntilVertex_isPrefix P.first).isSublist h.Q_mem

lemma shorten_between (h : P.IsRightLeg A S T) : h.shorten.between S (T ∪ V(h.bQ2)) := by
  rintro Q (rfl | hQ)
  · exact h.Q1_isPathFrom
  suffices (A.path_remove h.Q).between S (T ∪ V(h.bQ2)) by
    exact this hQ
  refine h.between.path_remove h.Q |>.right ?_
  rw [symmDiff_of_le subset_union_left, union_diff_left]
  exact (h.path_remove_Q_disjoint_bQ2).mono_right diff_subset

@[simp]
lemma shorten_last (h : P.IsRightLeg A S T) :
    last '' h.shorten.paths = insert P.first ((last '' A.paths) \ {h.Q.last}) := by
  simp only [shorten, shorten_paths, image_insert_eq, Q1_last, A.last_injOn.image_diff]
  congr
  rw [inter_eq_right.mpr (by simp)]
  simp

end IsRightLeg
end WList
