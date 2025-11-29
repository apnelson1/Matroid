import Matroid.Graph.Connected.Set.Leg
import Matroid.Graph.Connected.Vertex.VertexEnsemble
import Matroid.Graph.Connected.Defs
import Matroid.Graph.Finite
import Mathlib.Data.Finite.Card

open Set Function Nat WList symmDiff Graph.SetEnsemble

variable {α β ι : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z s t : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β} {n m : ℕ}

namespace Graph

lemma Menger'sTheorem_aux [G.Finite] {S T : Set α} (hS : S ⊆ V(G)) (hT : T ⊆ V(G))
    (hconn : G.SetConnGe S T n) {A : G.SetEnsemble} (hA : A.between S T)
    (hAFin : A.paths.Finite) (hAcard : A.paths.encard < n) :
    ∃ B : G.SetEnsemble, B.between S T ∧
    ∃ x ∉ last '' A.paths, insert x (last '' A.paths) = (last '' B.paths) := by
  classical
  have hTfin : T.Finite := G.vertexSet_finite.subset hT
  have : (V(G) \ T).Finite := G.vertexSet_finite.subset diff_subset

  /- Since we have less paths than the connectivity, the last ends of the paths is not an ST cut.
    Therefore, there is an S-(T \ last '' A.paths) path. -/
  have h1 : (G - (last '' A.paths)).SetConnGe S (T \ last '' A.paths) 1 := by
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
    (hconn : G.SetConnGe S T n) :
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
    G.SetConnGe S T n ↔ ∃ A : G.SetEnsemble, A.between S T ∧ A.paths.encard = n := by
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
    G.ConnBetweenGe s t n ↔ Nonempty (G.VertexEnsemble s t ι) := by
  have hιFin : Finite ι := ENat.card_lt_top.mp <| hι ▸ ENat.coe_lt_top n
  obtain hne | hne := eq_or_ne s t
  · subst t
    simp only [hs, connBetweenGe_self, true_iff]
    exact ⟨G.vertexEnsemble_nil hs ι⟩
  by_cases hadj : G.Adj s t
  · obtain ⟨e, he⟩ := hadj
    simp only [he.connBetweenGe, true_iff]
    exact ⟨he.vertexEnsemble ι hne⟩
  refine ⟨fun h => ?_, fun ⟨A⟩ => ?_⟩
  · rw [connBetweenGe_iff_setConnGe hne hadj, Menger'sTheorem_set
    (by simp [subset_diff, hadj]) (by simp [subset_diff, not_symm_not hadj])] at h
    obtain ⟨A, hA, hAcard⟩ := h
    refine ⟨VertexEnsemble.ofSetEnsemble s t hne A hA |>.comp (ι' := ι) ?_⟩
    rw [ENat.card_eq_coe_natCard, ENat.coe_inj] at hι
    rw [← A.first_injOn.encard_image] at hAcard
    have hAcardFin : (first '' A.paths).Finite := finite_of_encard_eq_coe hAcard
    rw [← hAcardFin.cast_ncard_eq, ENat.coe_inj] at hAcard
    exact (Finite.equivFinOfCardEq hι).trans (hAcardFin.equivFinOfCardEq hAcard).symm |>.toEmbedding
  unfold ConnBetweenGe
  by_contra! hC
  obtain ⟨C, hC⟩ := hC
  obtain ⟨i, hdj⟩ : ∃ i, Disjoint V(A.f i) C := by
    contrapose! hC
    simp_rw [not_disjoint_iff] at hC
    let f : ι → C := fun i ↦ ⟨(hC i).choose, (hC i).choose_spec.2⟩
    have hf : Injective f := by
      rintro i j hij
      apply A.internallyDisjoint.eq fun h ↦ ?_
      have his : (f i).val ≠ s := ne_of_mem_of_not_mem (hC i).choose_spec.2 C.left_not_mem
      have hit : (f i).val ≠ t := ne_of_mem_of_not_mem (hC i).choose_spec.2 C.right_not_mem
      have : (f i).val ∈ V(A.f i) ∩ V(A.f j) := ⟨(hC i).choose_spec.1, hij ▸ (hC j).choose_spec.1⟩
      simp [h, his, hit] at this
    exact hι ▸ ENat.card_le_card_of_injective hf
  apply C.not_connectedBetween
  use A.f i, by simpa [(A.isPath i).isWalk], A.first_eq i, A.last_eq i

-- #print axioms Menger'sTheorem_vertex

theorem Menger'sTheorem [G.Finite] (hι : ENat.card ι = n) :
    G.PreconnGe n ↔ ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → Nonempty (G.VertexEnsemble s t ι) :=
  forall₄_congr fun _ _ hs ht ↦ Menger'sTheorem_vertex hs ht hι



def Walk (G : Graph α β) := {w // G.IsWalk w}

lemma mixedLineGraph_edgeDelete : L'(G ＼ F) = L'(G) - (Sum.inr '' F) := by
  ext a b c
  · simp only [mixedLineGraph_vertexSet, edgeDelete_vertexSet, edgeDelete_edgeSet,
      vertexDelete_vertexSet, image_diff Sum.inr_injective, union_diff_distrib]
    convert Iff.rfl
    apply Disjoint.sdiff_eq_left
    simp
  cases b <;> cases c <;> simp only [mixedLineGraph_isLink, edgeDelete_inc_iff, Sym2.eq,
    Sym2.rel_iff', Prod.mk.injEq, Sum.inl.injEq, reduceCtorEq, and_false, Prod.swap_prod_mk,
    or_self, vertexDelete_isLink_iff, mem_image, exists_false, not_false_eq_true, and_self,
    and_true, Sum.inr.injEq, false_and, or_self, and_false, exists_eq_right] <;> aesop

lemma mixedLineGraph_vertexDelete : L'(G - X) = L'(G) - (Sum.inl '' X ∪ Sum.inr '' E(G, X)) := by
  ext a b c
  · simp only [mixedLineGraph_vertexSet, vertexDelete_vertexSet, vertexDelete_edgeSet_diff]
    rw [image_diff Sum.inl_injective, union_diff_distrib, ← diff_diff, ← diff_diff]
    convert Iff.rfl using 3
    · apply Disjoint.sdiff_eq_left
      rw [← image_diff Sum.inl_injective]
      simp
    rw [disjoint_image_inl_image_inr.symm.sdiff_eq_left, ← image_diff Sum.inr_injective]
  cases b <;> cases c <;> simp only [mixedLineGraph_isLink, vertexDelete_inc_iff,
    mem_setIncidentEdges_iff, not_exists, not_and, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Sum.inl.injEq, reduceCtorEq, and_false, Prod.swap_prod_mk, or_self, vertexDelete_isLink_iff,
    mem_union, mem_image, exists_eq_right, exists_false, or_false, false_and, Sum.inr.injEq,
    exists_eq_right, false_or, not_exists, not_and]
  · refine ⟨?_, ?_⟩
    · rintro ⟨⟨hav, ha2⟩, rfl, rfl⟩
      simpa [hav, and_self, true_and, mt (ha2 a.1) (not_not_intro hav)]
    rintro ⟨⟨hinc, rfl, rfl⟩, ha1, hX⟩
    simpa [hinc]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨hinc, hX⟩, rfl, rfl⟩
    simpa [hinc, mt (hX a.1)]
  rintro ⟨⟨hinc, rfl, rfl⟩, hX, ha1⟩
  simpa [hinc]

@[simp]
def mixedLineGraph_walkMap : WList α β → WList (α ⊕ β) (α × β)
| nil x => nil (Sum.inl x)
| cons x e w => cons (Sum.inl x) (x, e) (cons (Sum.inr e) (w.first, e) (mixedLineGraph_walkMap w))

@[simp]
lemma mixedLineGraph_walkMap_first : (mixedLineGraph_walkMap W).first = Sum.inl W.first := by
  induction W with
  | nil x => simp
  | cons x e w ih => simp

@[simp]
lemma mixedLineGraph_walkMap_last : (mixedLineGraph_walkMap W).last = Sum.inl W.last := by
  induction W with
  | nil x => simp
  | cons x e w ih => simpa

@[simp]
lemma mixedLineGraph_walkMap_isWalk (hW : G.IsWalk W) :L'(G).IsWalk (mixedLineGraph_walkMap W) := by
  induction hW with
  | nil hx => simpa
  | cons hw h ih => simp [ih, h.inc_left, h.inc_right]

@[simp]
lemma mixedLineGraph_walkMap_vertexSet :
    V(mixedLineGraph_walkMap W) = Sum.inl '' V(W) ∪ Sum.inr '' E(W) := by
  induction W with
  | nil x => simp
  | cons x e w ih => simp [ih, image_insert_eq, insert_union, insert_comm]

@[simp]
lemma mem_mixedLineGraph_walkMap_iff {x} : x ∈ mixedLineGraph_walkMap W ↔ (∃ v ∈ W, Sum.inl v = x) ∨
    (∃ e ∈ E(W), Sum.inr e = x) := by
  rw [← WList.mem_vertexSet_iff]
  simp

-- If e is not a loop, then we could even get a path rather than a walk.
lemma Preconnected.exists_isWalk_first_lastEdge (h : G.Preconnected) (hx : x ∈ V(G))
    (he : e ∈ E(G)) : ∃ (P : WList α β) (hP : P.Nonempty), G.IsWalk P ∧ P.first = x ∧
    hP.lastEdge = e := by
  have ⟨a, b, he⟩ := G.exists_isLink_of_mem_edgeSet he
  obtain ⟨P, hP, rfl, rfl⟩ := h x a hx he.left_mem
  use P.concat e b
  simp [hP, he]

lemma Preconnected.exists_isWalk_firstEdge_lastEdge (h : G.Preconnected) (he : e ∈ E(G))
    (hf : f ∈ E(G)) : ∃ (W : WList α β) (hW : W.Nonempty), G.IsWalk W ∧ hW.firstEdge = e ∧
    hW.lastEdge = f := by
  have ⟨a, b, he⟩ := G.exists_isLink_of_mem_edgeSet he
  have ⟨c, d, hf⟩ := G.exists_isLink_of_mem_edgeSet hf
  obtain ⟨P, hP, rfl, rfl⟩ := h b c he.right_mem hf.left_mem
  use (P.cons a e).concat f d
  simp [hP, he, hf, Nonempty.lastEdge_cons]

-- def sublist_of_mixedLineGraph_walkMap {W' : WList (α ⊕ β) (α × β)}
--     (hW' : G.mixedLineGraph.IsWalk W') :
--     ∃ W : WList α β, W'.IsSublist (mixedLineGraph_walkMap W) := by
--   induction hW' with
--   | nil hx =>
--     expose_names
--     obtain ⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩ := (by
--       simpa [mixedLineGraph_vertexSet, mem_union, mem_image] using hx)
--     <;> simp only [nil_isSublist_iff, mem_mixedLineGraph_walkMap_iff, reduceCtorEq, and_false,
--       exists_false, mem_edgeSet_iff, Sum.inr.injEq, exists_eq_right, false_or, Sum.inl.injEq,
--     or_false]
--     · use nil v, by simp
--     obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
--     use huv.walk, by simp
--   | cons hw h ih =>
--     simp only [mixedLineGraph_isLink, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
--Prod.swap_prod_mk] at h
--     obtain ⟨he, ⟨rfl, hwf⟩ | ⟨hwf, rfl⟩⟩ := h
--     ·
--     sorry

lemma notMem_iff_forall_mem_ne (S : Set α) (x : α) : (∀ y ∈ S, y ≠ x) ↔ x ∉ S := by
  aesop

-- lemma mixedLineGraph_vertexDelete_preconnected_of_preconnected (h : (G - X ＼ F).Preconnected) :
--     (G.mixedLineGraph - (Sum.inl '' X ∪ Sum.inr '' F)).Preconnected := by
--   intro s t hs ht
--   simp only [vertexDelete_vertexSet, mixedLineGraph_vertexSet, mem_diff, mem_union, mem_image,
--     not_or, not_exists, not_and, ne_eq] at hs ht
--   obtain ⟨(⟨u, hu, rfl⟩ | ⟨f, hf, rfl⟩), hsX, hsF⟩ := hs
--   obtain ⟨(⟨v, hv, rfl⟩ | ⟨g, hg, rfl⟩), htX, htF⟩ := ht
--   · simp_all only [Sum.inl.injEq, reduceCtorEq, not_false_eq_true, implies_true, ← ne_eq]
--     rw [notMem_iff_forall_mem_ne X _] at htX hsX
--     obtain hconn := h u v (by simp [hu, hsX]) (by simp [hv, htX])

--     sorry


-- lemma mixedLineGraph_vertexDelete_connected_of_connected (h : (G - X ＼ F).Connected) :
--     (G.mixedLineGraph - (Sum.inl '' X ∪ Sum.inr '' F)).Connected := by
--   obtain ⟨W, hW, rfl, rfl⟩ := h.connectedBetween (by simp) (by simp)

-- ¬(G.mixedLineGraph - (Sum.inl '' C.vertexSet ∪ Sum.inr '' C.edgeSet)).Connected
-- this : ¬(G - C.vertexSet ＼ C.edgeSet).Connected

-- def MixedCut.toCutMixedLineGraph (C : G.MixedCut) : G.mixedLineGraph.Cut where
--   carrier := Sum.inl '' C.vertexSet ∪ Sum.inr '' C.edgeSet
--   carrier_subset := by
--     simp only [mixedLineGraph_vertexSet, union_subset_iff]
--     exact ⟨(image_mono C.vertexSet_subset).trans subset_union_left,
--       (image_mono C.edgeSet_subset).trans subset_union_right⟩
--   not_connected' := by
--     have := C.not_conn'
--     simp
--     sorry


-- theorem Menger'sTheorem_mixed [G.Finite] (hι : ENat.card ι = n) :
--     G.ConnGe n ↔ ∀ ⦃s t⦄, s ∈ V(G) → t ∈ V(G) → ∃ A : G.VertexEnsemble s t ι,
--A.edgeDisjoint := by
--   sorry

variable {α' β' : Type*} {H H' : Graph α' β'}

-- def Walk.IsPrefix (w w' : G.Walk) : Prop := w.val.IsPrefix w'.val

-- def Walk.reverse (w : G.Walk) : G.Walk := ⟨w.val.reverse, w.prop.reverse⟩

-- structure WalkHom (G : Graph α β) (H : Graph α' β') where
--   walkMap : G.Walk → H.Walk
--   IsPrefix' ⦃w w' : G.Walk⦄ : w.IsPrefix w' → (walkMap w).IsPrefix (walkMap w')
--   reverse' ⦃w⦄ : walkMap w.reverse = (walkMap w).reverse

-- def vxMap (F : G.WalkHom H) : α → α'

end Graph
