import Matroid.Graph.Connected.Set.Leg
import Matroid.Graph.Connected.Vertex.VertexEnsemble
import Matroid.Graph.Connected.MixedLineGraph
import Matroid.Graph.Finite
import Mathlib.Data.Finite.Card

open Set Function Nat WList symmDiff Graph.SetEnsemble

variable {α β ι : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z s t : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β} {n m : ℕ}

namespace Graph

lemma Menger'sTheorem_aux [G.Finite] {S T : Set α} (hS : S ⊆ V(G)) (hT : T ⊆ V(G))
    (hconn : G.SetConnGE S T n) {A : G.SetEnsemble} (hA : A.between S T)
    (hAFin : A.paths.Finite) (hAcard : A.paths.encard < n) :
    ∃ B : G.SetEnsemble, B.between S T ∧
    ∃ x ∉ last '' A.paths, insert x (last '' A.paths) = last '' B.paths := by
  classical
  have hTfin : T.Finite := G.vertexSet_finite.subset hT
  have : (V(G) \ T).Finite := G.vertexSet_finite.subset diff_subset

  /- Since we have less paths than the connectivity, the last ends of the paths is not an ST cut.
    Therefore, there is an S-(T \ last '' A.paths) path. -/
  have h1 : (G - (last '' A.paths)).SetConnGE S (T \ last '' A.paths) 1 := by
    have hlast : last '' A.paths ⊆ V(G) := by
      rintro _ ⟨P, hP, rfl⟩
      exact hT <| hA hP |>.last_mem
    apply hconn.vertexDelete' (last '' A.paths) |>.subset diff_subset subset_rfl |>.anti_right
    rw [inter_eq_left.mpr hlast, A.last_injOn.encard_image]
    rw [← ENat.add_one_le_iff (by simpa)] at hAcard
    refine one_le_iff_ne_zero.mpr ?_
    simp only [ne_eq, ENat.toNat_eq_zero, ENat.sub_eq_top_iff, ENat.coe_ne_top, encard_eq_top_iff,
      not_infinite, false_and, or_false]
    exact ENat.one_le_iff_ne_zero.mp <| ENat.le_sub_of_add_le_left (by simpa) hAcard
  obtain ⟨P, hP⟩ := h1.exists_isPathFrom (by simp); clear h1
  have hPlA : Disjoint V(P) (last '' A.paths) := by
    have := hP.isPath.vertexSet_subset
    simp only [vertexDelete_vertexSet, subset_diff] at this
    exact this.2

  by_cases hdj : Disjoint V(P) A.vertexSet
  · let A' := A.path_insert P (hP.of_vertexDelete.subset subset_union_left (by simp) hP.first_mem
      hP.last_mem.1).isPath hdj.symm
    refine ⟨A', hA.path_insert (hP.of_vertexDelete.subset subset_union_left (by simp) hP.first_mem
        hP.last_mem.1) hdj.symm, P.last, ?_, by simp [A', image_insert_eq]⟩
    by_contra! hdj'
    absurd hdj
    rw [not_disjoint_iff]
    exact ⟨P.last, last_mem, A.image_last_subset hdj'⟩
  rw [not_disjoint_iff] at hdj

  have hGP : G.IsPathFrom S T P := by
    refine hP.of_vertexDelete'.right_of_symmdiff_disjoint ?_
    simpa [inter_eq_right.mpr (hA.image_last_eq_inter ▸ inter_subset_left),
      symmDiff_of_le diff_subset]
  let P' := P.suffixFromLast (· ∈ A.vertexSet)
  have hP'P : P'.IsSuffix P := by
    exact suffixFromLast_isSuffix ..
  have hP' : (G - (last '' A.paths)).IsPath P' := hP.suffix hP'P
  let R : P'.IsRightLeg A S T := IsRightLeg.ofIsPathFrom hA hGP hdj
  let R' := R.shorten
  have hR' : R'.between S (T ∪ V(R.bQ2)) := R.shorten_between
  have hR'Fin : R'.paths.Finite := by
    simp only [R', IsRightLeg.shorten, shorten_paths, finite_insert]
    exact hAFin.diff
  have hR'card : R'.paths.encard < n := by
    unfold R' IsRightLeg.shorten shorten
    rw [path_insert_paths_encard, path_remove_paths, Set.encard_diff_singleton_of_mem R.Q_mem]
    obtain ⟨n', hn'⟩ := ENat.ne_top_iff_exists.mp <| Set.encard_ne_top_iff.mpr hAFin
    rw [← hn']
    norm_cast
    have : 0 < n' := by
      rw [← ENat.coe_lt_coe, hn']
      simp only [cast_zero, encard_pos]
      use R.Q, R.Q_mem
    rwa [Nat.sub_add_cancel (by omega), ← ENat.coe_lt_coe, hn']
  have hT' : T ∪ V(R.bQ2) ⊆ V(G) := by
    rw [R.bQ2_vertexSet]
    exact union_subset hT <| union_subset (hP'P.subset.trans hGP.vertexSet_subset)
    <| R.Q2_subset_vertexSet.trans A.vertexSet_subset
  have hP'T : P'.first ∉ T := fun hxT ↦ hP'.vertexSet_subset first_mem |>.2 <| by
    rw [mem_image]
    use R.Q, R.Q_mem, (hA R.Q_mem |>.eq_last_of_mem R.first_mem_path hxT).symm
  have hA'lW : last '' R.shorten.paths \ V(R.bQ2) = last '' A.paths \ {R.Q.last} := by
    rw [R.shorten_last, insert_diff_of_mem _ (by simp)]
    apply Disjoint.sdiff_eq_left
    rw [disjoint_diff_iff, hA.image_last_eq_inter, inter_assoc, inter_comm _ V(R.bQ2),
      R.bQ2_inter_vertexSet, ← hA R.Q_mem|>.vertexSet_inter_right, inter_comm]
    exact inter_subset_inter_left _ R.Q2_isSuffix.subset

  obtain ⟨B, hB, y, hy, hexcd⟩ := Menger'sTheorem_aux hS hT' (hconn.subset subset_rfl
    subset_union_left) hR' hR'Fin hR'card

  rw [R.shorten_last] at hy
  obtain ⟨hyP'f, hyA⟩ := by simpa only [mem_insert_iff, mem_diff, mem_image, mem_singleton_iff,
    not_or, not_and, Decidable.not_not, forall_exists_index, and_imp] using hy
  have hif : if y ∈ R.bQ2.vertex then List.countP (fun x ↦ decide (x ∈ B.vertexSet)) R.bQ2.vertex
      = 2 else List.countP (fun x ↦ decide (x ∈ B.vertexSet)) R.bQ2.vertex = 1 := by
    have h1 : ∀ x, x ∈ R.bQ2 ∧ x ∈ B.vertexSet ↔ x ∈ R.bQ2 ∧ x ∈ last '' B.paths := by
      simp_rw [hB.image_last_eq_inter, mem_inter_iff, mem_union]
      tauto
    have h2 : ∀ x, x ∈ R.bQ2 → ¬ (x ∈ last '' A.paths ∧ x ≠ R.Q.last) := by
      rintro x hxbQ2 h
      have hxlA : x ∈ last '' (A.path_remove R.Q).paths := by rwa [A.path_remove_last R.Q_mem]
      exact R.path_remove_Q_disjoint_bQ2.notMem_of_mem_left (image_last_subset _ hxlA) hxbQ2
    split_ifs with hyW
    · rw [R.bQ2_isPath.nodup.countP_eq_card, Finset.card_eq_two]
      use y, P'.first, hyP'f
      ext x
      simp only [Finset.mem_filter, List.mem_toFinset, mem_vertex, Finset.mem_insert,
        Finset.mem_singleton]
      rw [h1, ← hexcd, R.shorten_last, mem_insert_iff, mem_insert_iff, mem_diff, ← or_assoc]
      simp +contextual only [mem_singleton_iff, iff_def, and_imp, h2, or_false, implies_true,
        true_or, and_true, true_and]
      rintro (rfl | rfl)
      · exact hyW
      simp
    rw [R.bQ2_isPath.nodup.countP_eq_card, Finset.card_eq_one]
    use P'.first
    ext x
    simp only [Finset.mem_filter, List.mem_toFinset, mem_vertex, Finset.mem_singleton]
    rw [h1, ← hexcd, R.shorten_last]
    simp +contextual only [mem_insert_iff, mem_diff, mem_singleton_iff, iff_def, and_imp,
      IsRightLeg.first_mem_bQ2, true_or, or_true, and_self, implies_true, and_true]
    rintro hxbQ2 (rfl | rfl | hxlA)
    · exact (hyW hxbQ2).elim
    · rfl
    exact (h2 x hxbQ2 hxlA).elim

  have hle : List.countP (fun x ↦ decide (x ∈ B.vertexSet)) R.bQ2.vertex ≤ 2 := by
    split_ifs at hif <;> omega
  have hSW : V(R.bQ2) ∩ S ⊆ B.vertexSet := by
    refine R.bQ2_inter_left.trans (subset_trans ?_ B.image_last_subset)
    rw [singleton_subset_iff, ← hexcd, R.shorten_last]
    simp
  have hWT : (T \ V(R.bQ2) ∪ {R.bQ2.first, R.bQ2.last}) = T := by
    rw [← R.bQ2_inter_right, inter_comm, diff_union_inter]
  let B' := B.extend_right_le_two hB R.bQ2_isPath hle
  use B'
  split_ifs at hif with hybQ2
  · have := hB.extend_right_le_two R.bQ2_isPath hle hSW
    rw [hWT] at this
    refine ⟨this, P.last, hP.last_mem.2, ?_⟩
    rw [SetEnsemble.extend_right_le_two_last_of_two hB R.bQ2_isPath hif, ← hexcd,
      insert_diff_of_mem _ (by exact hybQ2), hA'lW, R.bQ2_first, R.bQ2_last]
    simp only [union_insert, union_singleton, insert_diff_singleton]
    rw [insert_eq_of_mem (a := R.Q.last) (by use R.Q, R.Q_mem),
      P.suffixFromLast_last (· ∈ A.vertexSet)]
  have hP'lB : R.bQ2.first ∉ B.vertexSet := by
    intro hPlB
    have hPlBl : R.bQ2.first ∈ last '' B.paths := by
      rw [hB.image_last_eq_inter, mem_inter_iff]
      use subset_union_right first_mem
    rw [← hexcd, R.shorten_last] at hPlBl
    simp only [mem_insert_iff, mem_diff, mem_image, mem_singleton_iff] at hPlBl
    obtain rfl | (h | ⟨h, hnQl⟩) := hPlBl
    · exact hybQ2 first_mem
    · exact hP'T <| (R.bQ2_first ▸ h) ▸ (hP'P.last_eq ▸ hP.last_mem.1)
    rw [← mem_image, R.bQ2_first] at h
    exact (hP'P.last_eq ▸ hP.last_mem.2) h
  have := hB.extend_right_le_two R.bQ2_isPath hle hSW
  rw [hWT] at this
  refine ⟨this, y, fun hylA ↦ ?_, ?_⟩
  · simp only [mem_insert_iff, mem_diff, mem_singleton_iff, not_or, not_and,
    Decidable.not_not] at hy
    obtain rfl := hy.2 hylA
    exact ((R.bQ2_last ▸ hybQ2) last_mem).elim
  rw [SetEnsemble.extend_right_le_two_last_of_one hB R.bQ2_isPath hif hP'lB, ← hexcd,
    insert_diff_of_notMem _ (by exact hybQ2), hA'lW, insert_comm, R.bQ2_last,
    insert_diff_self_of_mem (by use R.Q, R.Q_mem)]
termination_by (V(G) \ T).ncard
decreasing_by
  refine ncard_lt_ncard ?_ (by assumption)
  rw [diff_ssubset_diff_iff, ssubset_iff_exists]
  use inter_subset_inter subset_rfl subset_union_left
  use P'.first, ?_, by simp [hP'T]
  simp only [SetEnsemble.mem_vertexSet_iff, mem_inter_iff, mem_union, WList.mem_vertexSet_iff]
  use (hP'P.subset.trans hGP.vertexSet_subset) first_mem, Or.inr (R.first_mem_bQ2)

lemma Menger'sTheorem_aux' [G.Finite] (hS : S ⊆ V(G)) (hT : T ⊆ V(G)) {n : ℕ}
    (hconn : G.SetConnGE S T n) :
    ∀ m ≤ n, ∃ A : G.SetEnsemble, A.between S T ∧ A.paths.encard = m := by
  rintro m hn
  match m with
  | 0 => exact ⟨SetEnsemble.empty G, by simp⟩
  | 1 =>
    obtain ⟨P, hP⟩ := hconn.exists_isPathFrom (by simp only [ne_eq]; omega)
    exact ⟨SetEnsemble.single hP.isPath, single_between hP, by simp⟩
  | m + 2 =>
  obtain ⟨A, hA, hAcard⟩ := Menger'sTheorem_aux' hS hT hconn (m+1) (by omega)
  obtain ⟨B, hB, b, hb, hB⟩ := Menger'sTheorem_aux hS hT hconn (A := A)
    hA (finite_of_encard_eq_coe hAcard) (hAcard ▸ (by norm_cast))
  use B
  apply_fun Set.encard (α := α) at hB
  rw [← B.last_injOn.encard_image, ← hB, encard_insert_of_notMem hb, A.last_injOn.encard_image,
    hAcard]
  norm_cast

/-- ## Menger's Theorem
  For vertex sets `S` and `T`, if every `S`-`T` cut has at least `n` vertices, then there are `n`
  disjoint paths from `S` to `T`. -/
theorem Menger'sTheorem_set [G.Finite] (hS : S ⊆ V(G)) (hT : T ⊆ V(G)) (n : ℕ) :
    G.SetConnGE S T n ↔ ∃ A : G.SetEnsemble, A.between S T ∧ A.paths.encard = n := by
  refine ⟨(Menger'sTheorem_aux' hS hT · n le_rfl), fun ⟨A, hA, hAcard⟩ C hC => ?_⟩
  match n with
  | 0 => exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a_1 ↦ a_1) rfl _
  | n + 1 =>
  rw [← hAcard]
  by_contra! hC'
  obtain ⟨P, hP, hdj⟩ : ∃ P ∈ A.paths, Disjoint V(P) C := by
    contrapose! hC'
    simp_rw [not_disjoint_iff] at hC'
    have hAFin : A.paths.Finite := finite_of_encard_eq_coe hAcard
    let f : A.paths → C := fun P ↦ ⟨(hC' P P.prop).choose, (hC' P P.prop).choose_spec.2⟩
    have hf : Injective f := by
      rintro P Q hPQ
      rw [← Subtype.val_inj] at hPQ ⊢
      exact A.disjoint.eq P.prop Q.prop <| not_disjoint_iff.mpr
        ⟨(f P).val, (hC' P P.prop).choose_spec.1, hPQ ▸ (hC' Q Q.prop).choose_spec.1⟩
    exact Embedding.encard_le ⟨f, hf⟩

  apply hC.ST_disconnects
  simp only [SetConnected]
  use P.first, (hA hP).first_mem, P.last, (hA hP).last_mem, P, by simpa [A.valid hP |>.isWalk]

-- #print axioms Menger'sTheorem

/-- For two vertices `s` and `t`, if every `s`-`t` cut has at least `n` vertices,
    then there are `n` internally disjoint paths from `s` to `t`. -/
theorem Menger'sTheorem_vertex [G.Finite] (hs : s ∈ V(G)) (ht : t ∈ V(G)) (hι : ENat.card ι = n) :
    G.ConnBetweenGE s t n ↔ Nonempty (G.VertexEnsemble s t ι) := by
  classical
  have hιFin : Finite ι := ENat.card_lt_top.mp <| hι ▸ ENat.coe_lt_top n
  obtain hne | hne := eq_or_ne s t
  · subst t
    simp only [hs, connBetweenGE_self, true_iff]
    exact ⟨G.vertexEnsemble_nil hs ι⟩
  by_cases hadj : G.Adj s t
  · obtain ⟨e, he⟩ := hadj
    simp only [he.connBetweenGE, true_iff]
    exact ⟨he.vertexEnsemble ι hne⟩
  refine ⟨fun h => ?_, fun ⟨A⟩ C hC => ?_⟩
  · rw [connBetweenGE_iff_setConnGE hne hadj, Menger'sTheorem_set
    (by simpa [subset_diff, hadj] using (G.neighbor_subset s).trans <| subset_insert ..)
    (by simpa [subset_diff, not_symm_not hadj] using (G.neighbor_subset t).trans
    <| subset_insert ..)] at h
    obtain ⟨A, hA, hAcard⟩ := h
    have hAdj := A.of_vertexDelete
    replace hA := hA.left (S₀ := N(G, s)) <| by
      rw [diff_symmDiff]
      exact (hAdj.mono_right (by simp)).mono_right inter_subset_right
    replace hA := hA.right (T₀ := N(G, t)) <| by
      rw [diff_symmDiff]
      exact (hAdj.mono_right (by simp)).mono_right inter_subset_right
    refine ⟨VertexEnsemble.ofSetEnsemble s t hne A hA |>.comp (ι' := ι) ?_⟩
    rw [ENat.card_eq_coe_natCard, ENat.coe_inj] at hι
    rw [← A.first_injOn.encard_image] at hAcard
    have hAcardFin : (first '' A.paths).Finite := finite_of_encard_eq_coe hAcard
    rw [← hAcardFin.cast_ncard_eq, ENat.coe_inj] at hAcard
    exact (Finite.equivFinOfCardEq hι).trans (hAcardFin.equivFinOfCardEq hAcard).symm |>.toEmbedding
  have hmeet : ∀ i, ∃ x ∈ V(A.f i), x ∈ C := by
    intro i
    have hC' : G.IsSepBetween (A.f i).first (A.f i).last C := by
      simpa [A.first_eq i, A.last_eq i] using hC
    exact (A.isPath i).isWalk.exists_mem_isSepBetween (X := C) hC'
  choose v hvV hvC using hmeet
  let f : ι → C := fun i ↦ ⟨v i, hvC i⟩
  have hf : Injective f := by
    intro i j hij
    have hv : v i = v j := congrArg Subtype.val hij
    by_contra hne
    have hsne : v i ≠ s := by
      exact ne_of_mem_of_not_mem (hvC i) hC.left_not_mem
    have htne : v i ≠ t := by
      exact ne_of_mem_of_not_mem (hvC i) hC.right_not_mem
    have hst : v i = s ∨ v i = t :=
      A.eq_or_eq_of_mem (hxi := hvV i) (hxj := by simpa [hv] using hvV j) hne
    cases hst with
    | inl hs' => exact hsne hs'
    | inr ht' => exact htne ht'
  have hcard : ENat.card ι ≤ C.encard := by
    simpa [ENat.card_coe_set_eq] using (ENat.card_le_card_of_injective hf)
  simpa [hι] using hcard

theorem Menger'sTheoremPre [G.Finite] (hι : ENat.card ι = n) :
    G.PreconnGE n ↔ ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → Nonempty (G.VertexEnsemble s t ι) :=
  forall₄_congr fun _ _ hs ht ↦ Menger'sTheorem_vertex hs ht hι

theorem Menger'sTheorem [G.Finite] (hι : ENat.card ι = n) (hnt : V(G).Nontrivial) :
    G.ConnGE n ↔ ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → ∃ A : G.VertexEnsemble s t ι,
    Set.Subsingleton {i | (A.f i).length = 1} := by
  classical
  refine iff_comm.mp ⟨fun h => ?_, fun h s t hs ht => ?_⟩
  · by_cases hC : G.IsComplete
    · rw [hC.connGE_iff n]
      simp only [hnt.not_subsingleton, false_and, false_or]
      obtain ⟨s, hs, t, ht, hne⟩ := hnt
      obtain ⟨A, hA⟩ := h hs ht
      exact A.vertexSet_encard_of_length_one_subsingleton hι hs hne hA
    rw [← G.preconnGE_iff_connGE_of_not_isComplete hC n]
    intro s t hs ht
    rw [Menger'sTheorem_vertex hs ht hι]
    exact ⟨(h hs ht).choose⟩
  obtain rfl | hne := eq_or_ne s t
  · use G.vertexEnsemble_nil hs ι, by simp
  obtain hem | ⟨e, he⟩ := E(G, s, t).eq_empty_or_nonempty
  · obtain ⟨A⟩ := Menger'sTheoremPre hι |>.mp h.pre hs ht
    use A
    convert subsingleton_empty
    simp only [WList.length_eq_one_iff, mem_setOf_eq, mem_empty_iff_false, iff_false,
      not_exists, Set.ext_iff]
    intro i u e v hi
    obtain rfl := by simpa using hi ▸ (A.first_eq i)
    obtain rfl := by simpa using hi ▸ (A.last_eq i)
    obtain ⟨huv, -, -⟩ := cons_isPath_iff.mp <| hi ▸ (A.isPath i)
    simp only [first_cons, last_cons, nil_last, Set.ext_iff, mem_linkEdges_iff,
      mem_empty_iff_false, iff_false] at hem
    exact hem e huv
  match n with
  | 0 =>
    simp only [cast_zero, ENat.card_eq_zero_iff_empty] at hι
    use G.vertexEnsemble_empty s t ι, by simp
  | n + 1 =>
    have hιn : Nonempty ι := by simp [← ENat.one_le_card_iff_nonempty, hι]
    have hι' : ENat.card ({hιn.some}ᶜ : Set ι) = n := by
      have := by simpa [hι] using encard_add_encard_compl ({hιn.some} : Set ι)
      simp only [ENat.card_coe_set_eq]
      enat_to_nat!
      omega
    obtain ⟨A⟩ := (G ＼ E(G, s, t)).Menger'sTheoremPre hι' |>.mp
      (h.edgeDelete_linkEdges s t |>.pre) (by simpa : s ∈ _) (by simpa : t ∈ _)
    have hP : G.IsPath <| cons s e (nil t) := by simpa [hne, ht]
    use A.of_le edgeDelete_le |>.extend_singleEdge hιn.some hP
    intro i hAi j hAj
    obtain rfl | hnei := eq_or_ne i hιn.some <;> obtain rfl | hnej := eq_or_ne j hιn.some
    <;> simp_all only [mem_linkEdges_iff, cast_add, cast_one, ENat.card_coe_set_eq,
      mem_setOf_eq, VertexEnsemble.extend_singleEdge_of_eq, cons_length, nil_length, zero_add]
    · simp [(A.of_le _).extend_singleEdge_of_ne hP hnej, A.of_linkEdges_edgeDelete] at hAj
    · simp [(A.of_le _).extend_singleEdge_of_ne hP hnei, A.of_linkEdges_edgeDelete] at hAi
    simp [(A.of_le _).extend_singleEdge_of_ne hP hnei, A.of_linkEdges_edgeDelete] at hAi

theorem Menger'sTheorem_mixed [G.Finite] (hs : s ∈ V(G)) (ht : t ∈ V(G)) (hι : ENat.card ι = n) :
    (∀ X ⊆ V(G), s ∉ X ∧ t ∉ X → ∀ F ⊆ E(G), ¬ ((G - X) ＼ F).ConnBetween s t →
    n ≤ X.encard + F.encard) ↔ ∃ A : G.VertexEnsemble s t ι, A.edgeDisjoint := by
  convert (L'(G)).Menger'sTheorem_vertex (by simpa : Sum.inl s ∈ _) (by simpa : Sum.inl t ∈ _) hι
  · refine ⟨fun h C hC ↦ ?_, fun h X hX ⟨hsX, htX⟩ F hF hXF ↦ ?_⟩
    · change n ≤ C.encard
      rw [← image_preimage_inl_union_image_preimage_inr C, encard_union_eq (by simp),
      Sum.inl_injective.encard_image, Sum.inr_injective.encard_image]
      refine h (Sum.inl ⁻¹' C) ?_ ?_ (Sum.inr ⁻¹' C) ?_ ?_
      · exact preimage_subset_iff.mpr fun x hxC ↦ by simpa using hC.subset hxC
      · exact ⟨hC.left_not_mem, hC.right_not_mem⟩
      · exact preimage_subset_iff.mpr fun e heC ↦ by simpa using hC.subset heC
      rw [← connBetween_mixedLineGraph_del_iff, image_preimage_inl_union_image_preimage_inr]
      exact hC.not_connBetween
    have hSep : (L'(G)).IsSepBetween (Sum.inl s) (Sum.inl t) (Sum.inl '' X ∪ Sum.inr '' F) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      on_goal 4 =>
        contrapose! hXF
        rwa [← connBetween_mixedLineGraph_del_iff]
      all_goals simp [Sum.inl_injective.preimage_image, Sum.inr_injective.preimage_image, hX, hF,
      hsX, htX]
    have h' := h (C := (Sum.inl '' X ∪ Sum.inr '' F)) hSep
    change n ≤ (Sum.inl '' X ∪ Sum.inr '' F).encard at h'
    rwa [encard_union_eq (by simp), Sum.inl_injective.encard_image,
      Sum.inr_injective.encard_image] at h'
  refine ⟨fun ⟨A, hA⟩ ↦ ⟨mixedLineEnsembleMap A hA⟩, fun ⟨A⟩ ↦ ?_⟩
  classical
  use mixedLineOfEnsembleMap A, mixedLineOfEnsembleMap_edgeDisjoint A

end Graph
