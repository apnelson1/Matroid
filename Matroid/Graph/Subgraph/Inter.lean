import Matroid.Graph.Subgraph.Compatible

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

namespace Graph

/-! ### Indexed Intersections -/

/-- The intersection of a nonempty family of pairwise compatible graphs.
  Remove any disagreeing edges. -/
@[simps dup isLink edgeSet]
protected def iInter [Nonempty ι] (G : ι → Graph α β) : Graph α β where
  Dup := ⨅ i, (G i).Dup
  IsLink e x y :=
    let j := Classical.arbitrary ι
    ∀ i, (G i).Dup x = (G j).Dup x ∧ (G i).Dup y = (G j).Dup y ∧ (G i).IsLink e x y
  isLink_symm e he a b hl i := by
    obtain ⟨ha, hb, h⟩ := hl i
    exact ⟨hb, ha, h.symm⟩
  dup_or_dup_of_isLink_of_isLink e a b c d hlab' hlcd' := by
    let j := Classical.arbitrary ι
    simp_all only [Partition.iInf_rel, iInf_apply, ciInf_const]
    obtain ⟨ha, hb, hlab⟩ := hlab' j
    obtain ⟨hc, hd, hlcd⟩ := hlcd' j
    exact (G j).dup_or_dup_of_isLink_of_isLink hlab hlcd
  mem_vertexSet_of_isLink e a b hl := by
    simp only [Partition.iInf_supp, vertexSet_def, mem_iInter] at hl ⊢
    exact fun i ↦ (hl i).2.2.left_mem
  isLink_of_dup e a b c hdab hlbc i := by
    let j := Classical.arbitrary ι
    simp_all only [Partition.iInf_rel, iInf_apply, iInf_Prop_eq, true_and]
    obtain ⟨hc, hd, h⟩ := hlbc i
    use ?_, trans' (hdab i) h
    ext d
    rw [(G i).dup_left_rw (hdab i), hc, (G j).dup_left_rw (hdab j)]

variable {G : ι → Graph α β} [Nonempty ι]

@[simp]
lemma iInter_vertexSet (G : ι → Graph α β) : V(Graph.iInter G) = ⋂ i, V(G i) := by
  rw [vertexSet_eq]
  simp

@[simp↓]
lemma iInter_isLink_of_agree (hG : Pairwise (Dup_agree on G)) :
    (Graph.iInter G).IsLink e = ⨅ j, (G j).IsLink e := by
  ext x y
  simp +contextual only [iInter_isLink, iInf_apply, iInf_Prop_eq, iff_def, IsLink.symm,
    implies_true, and_true, true_and]
  refine fun h i ↦ ⟨?_, ?_⟩ <;> ext z
  · exact (Partition.agree_iff_rel.mp <| hG.of_refl i (Classical.arbitrary ι)) _ z
      (h i).left_mem_supp (h _).left_mem_supp
  · exact (Partition.agree_iff_rel.mp <| hG.of_refl i (Classical.arbitrary ι)) _ z
      (h i).right_mem_supp (h _).right_mem_supp

@[simp↓]
lemma iInter_edgeSet_of_agree (hG : Pairwise (Dup_agree on G)) (hG' : Pairwise (Compatible on G)) :
    E(Graph.iInter G) = ⋂ i, E(G i) := by
  simp_rw [edgeSet_eq_setOf_exists_isLink, iInter_isLink_of_agree hG]
  ext e
  simp only [iInf_apply, iInf_Prop_eq, mem_setOf_eq, mem_iInter]
  refine ⟨fun ⟨x, y, h⟩ i ↦ ⟨x, y, h i⟩, fun h ↦ ?_⟩
  obtain ⟨x, y, hj⟩ := h (Classical.arbitrary ι)
  use x, y, fun i ↦ ?_
  obtain ⟨_, _, hi⟩ := h i
  exact hG'.of_refl _ i |>.isLink_eq hj.edge_mem hi.edge_mem |>.mp hj

lemma iInter_dup_le (G : ι → Graph α β) (i : ι) :
    (Graph.iInter G).Dup ≤ (G i).Dup := iInf_le _ i

protected lemma iInter_le (hG : Pairwise (Dup_agree on G)) (i : ι) : Graph.iInter G ≤ G i where
  dup_subset := by
    rw [iInter_dup]
    exact Partition.iInf_subset_of_agree hG i
  isLink_of_isLink _ _ _ h := (h i).2.2

@[simp]
lemma le_iInter_iff (hG : Pairwise (Dup_agree on G)) :
    H ≤ Graph.iInter G ↔ ∀ i, H ≤ G i := by
  let j := Classical.arbitrary ι
  refine ⟨fun h i ↦ h.trans <| Graph.iInter_le hG i,
    fun h ↦ le_of_le_isLabelSubgraph_subset_subset (h j)
    (isLabelSubgraph_of_le (Graph.iInter_le hG j)) ?_ fun e he ↦ ?_⟩ <;>
    simp only [iInter_vertexSet, subset_iInter_iff, iInter_edgeSet, mem_setOf_eq]
  · exact fun i ↦ vertexSet_mono (h i)
  obtain ⟨x, y, hHxy⟩ := exists_isLink_of_mem_edgeSet he
  use x, y, fun i ↦ ?_
  have hi := hHxy.of_le (h i)
  have hj := hHxy.of_le (h j)
  exact ⟨(hG.of_refl i j).eq_of_mem hi.left_mem hj.left_mem,
    (hG.of_refl i j).eq_of_mem hi.right_mem hj.right_mem, hi⟩

@[simp]
protected lemma iInter_const (G : Graph α β) : Graph.iInter (fun (_ : ι) ↦ G) = G := by
  apply le_antisymm (Graph.iInter_le (Pairwise.const_of_refl G) (Classical.arbitrary ι))
  rw [le_iInter_iff (Pairwise.const_of_refl G)]
  exact fun i ↦ le_refl G

-- lemma iInter_le_iUnion (hG : Pairwise (Compatible on G)) :
--     Graph.iInter G ≤ Graph.iUnion G hG :=
--   (Graph.iInter_le (Classical.arbitrary ι)).trans <| Graph.le_iUnion ..

protected lemma iInter_comp_le [Nonempty ι'] {f : ι' → ι} (hG : Pairwise (Dup_agree on G)) :
    Graph.iInter G ≤ Graph.iInter (fun i ↦ G (f i)) := by
  rw [Graph.le_iInter_iff (by exact hG.onFun_comp_of_refl f)]
  exact fun i ↦ Graph.iInter_le hG (f i)

lemma iInter_comp_eq_of_surj (hG : Pairwise (Dup_agree on G)) [Nonempty ι'] {f : ι' → ι}
    (hf : Function.Surjective f) : Graph.iInter G = Graph.iInter (fun i ↦ G (f i)) :=
  le_antisymm (Graph.iInter_comp_le hG) <| by
  rw [Graph.le_iInter_iff hG]
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.iInter_le (hG.onFun_comp_of_refl f) i'

omit [Nonempty ι] in
lemma iInter_range [Nonempty ι'] {f : ι' → ι} {G : (Set.range f) → Graph α β}
    (hG : Pairwise (Dup_agree on G)) :
    Graph.iInter G = Graph.iInter (fun i ↦ G (Set.rangeFactorization f i)) :=
  iInter_comp_eq_of_surj hG surjective_onto_range

@[simp]
lemma iInter_inc (hG : Pairwise (Dup_agree on G)) :
    (Graph.iInter G).Inc e x ↔ ∃ y, ∀ i, (G i).IsLink e x y := by
  rw [Inc, iInter_isLink_of_agree hG]
  simp

@[simp↓]
lemma iInter_inc_of_compatible (hG : Pairwise (Dup_agree on G)) (hG' : Pairwise (Compatible on G)) :
    (Graph.iInter G).Inc e x ↔ ∀ i, (G i).Inc e x := by
  rw [iInter_inc hG]
  let j := Classical.arbitrary ι
  refine ⟨fun ⟨y, h⟩ i ↦ ⟨y, h i⟩, fun h ↦ ?_⟩
  obtain ⟨y, hy⟩ := h j
  use y, fun i ↦ hy.of_compatible (hG'.of_refl j i) (h i).edge_mem

@[simp]
lemma iInter_isLoopAt_iff (hG : Pairwise (Dup_agree on G)) :
    (Graph.iInter G).IsLoopAt e x ↔ ∀ i, (G i).IsLoopAt e x := by
  simp_rw [IsLoopAt, iInter_isLink_of_agree hG]
  simp

@[simp]
lemma iInter_isNonloopAt_iff (hG : Pairwise (Dup_agree on G)) :
    (Graph.iInter G).IsNonloopAt e x ↔
    ∃ y, ¬ (Graph.iInter G).Dup x y ∧ ∀ i, (G i).IsLink e x y := by
  simp_rw [IsNonloopAt, iInter_isLink_of_agree hG, iInter_dup]
  simp

-- @[simp]
-- lemma induce_iInter [Nonempty ι] {G : ι → Graph α β} (X : Set α) :
--     (Graph.iInter G)[X] = .iInter (fun i ↦ (G i)[X]) :=
--   Graph.ext (iInter_const X).symm fun e x y ↦ by
--   simp [forall_and_right]

@[simp]
lemma vertexDelete_iInter (hG : Pairwise (Dup_agree on G)) (X : Set α) :
    (Graph.iInter G) - X = .iInter (fun i ↦ (G i) - X) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp [hG, hG.vertexDelete_dup_agree X, forall_and_right]

@[simp]
lemma edgeDelete_iInter (hG : Pairwise (Dup_agree on G)) (F : Set β) :
    (Graph.iInter G) ＼ F = .iInter (fun i ↦ (G i) ＼ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp [hG, hG.edgeDelete_dup_agree F, forall_and_right]

@[simp]
lemma edgeRestrict_iInter (hG : Pairwise (Dup_agree on G)) (F : Set β) :
    (Graph.iInter G) ↾ F = .iInter (fun i ↦ (G i) ↾ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp [hG, hG.edgeRestrict_dup_agree F, forall_and_left]

/-! ### Set Intersections -/

/-- The intersection of a nonempty set of pairwise compatible graphs. -/
@[simps! vertexSet isLink edgeSet]
protected def sInter (s : Set (Graph α β)) (hne : s.Nonempty) : Graph α β :=
  @Graph.iInter _ _ _ hne.to_subtype (fun G : s ↦ G.1)

variable {s t : Set (Graph α β)} {G H : Graph α β}

@[simp]
lemma sInter_dup (hne : s.Nonempty) : (Graph.sInter s hne).Dup = ⨅ G ∈ s, G.Dup := by
  let _ : Nonempty s := hne.to_subtype
  rw [Graph.sInter, iInter_dup, iInf_subtype]

@[simp↓]
lemma sInter_isLink_of_agree (hne : s.Nonempty) (hG : s.Pairwise Dup_agree) :
    (Graph.sInter s hne).IsLink e = ⨅ G ∈ s, G.IsLink e := by
  let _ : Nonempty s := hne.to_subtype
  rw [Graph.sInter, iInter_isLink_of_agree hG.subtype, iInf_subtype]

@[simp↓]
lemma sInter_edgeSet_of_agree (hne : s.Nonempty) (hG : s.Pairwise Dup_agree)
    (hG' : s.Pairwise Compatible) : E(Graph.sInter s hne) = ⋂ G ∈ s, E(G) := by
  let _ : Nonempty s := hne.to_subtype
  rw [Graph.sInter, iInter_edgeSet_of_agree hG.subtype hG'.subtype, iInter_subtype]

protected lemma sInter_le (hG : s.Pairwise Dup_agree) (hGs : G ∈ s) :
    Graph.sInter s ⟨G, hGs⟩ ≤ G :=
  let _ : Nonempty s := by use G
  Graph.iInter_le hG.subtype ⟨G, hGs⟩

@[simp]
protected lemma le_sInter_iff (hne : s.Nonempty) (hG : s.Pairwise Dup_agree) :
    H ≤ Graph.sInter s hne ↔ ∀ G ∈ s, H ≤ G := by
  let _ : Nonempty s := hne.to_subtype
  simp [Graph.sInter, hG.subtype]

protected lemma sInter_anti (hnes : s.Nonempty) (hs : s.Pairwise Dup_agree) (hnet : t.Nonempty)
    (ht : t.Pairwise Dup_agree) (hle : s ⊆ t) : Graph.sInter t hnet ≤ Graph.sInter s hnes := by
  rw [Graph.le_sInter_iff hnes hs]
  exact fun G hGs ↦ Graph.sInter_le ht (hle hGs)

def Equiv.insert_option {s : Set α} [DecidablePred fun (x : α) => x ∈ s] {a : α} (has : a ∉ s) :
    Option s ≃ (insert a s : Set α) :=
  (Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm

protected lemma sInter_insert_eq_iInter (hs : (insert G s).Pairwise Dup_agree) (hGs : G ∉ s)
    [DecidablePred (· ∈ s)] : Graph.sInter (insert G s) (by simp) = Graph.iInter
    ((fun G : (insert G s : Set _) ↦ G.1) ∘ (Equiv.insert_option hGs)) :=
  Graph.iInter_comp_eq_of_surj hs.subtype <| Equiv.surjective (Equiv.insert_option hGs)

omit [Nonempty ι] in
protected lemma sInter_image {s : Set ι} (hne : s.Nonempty) (f : ι → Graph α β)
    (hfs : s.Pairwise (Dup_agree on f)) :
    Graph.sInter (f '' s) (by simpa) = @Graph.iInter _ _ _ hne.to_subtype (f · : s → _) := by
  rw [Graph.sInter]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  have := hne.to_subtype
  exact Graph.iInter_comp_eq_of_surj (f := f') hfs.image.subtype
    fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩

protected lemma sInter_range {f : ι → Graph α β} (hfs : Pairwise (Dup_agree on f)) :
    Graph.sInter (Set.range f) (range_nonempty f) = .iInter f :=
  Graph.iInter_comp_eq_of_surj (f := Set.rangeFactorization f) hfs.range_pairwise.subtype
    surjective_onto_range

@[simp]
protected lemma sInter_singleton (G : Graph α β) : Graph.sInter {G} (by simp) = G := by
  apply le_antisymm (Graph.sInter_le (by simp) (by simp))
  rw [Graph.le_sInter_iff (by simp) (by simp)]
  exact fun G_2 a ↦ Eq.ge a

@[simp]
lemma sInter_inc (hs : s.Nonempty) (hG : s.Pairwise Dup_agree) :
    (Graph.sInter s hs).Inc e x ↔ ∃ y, ∀ G ∈ s, G.IsLink e x y := by
  unfold Inc
  simp [hG]

@[simp↓]
lemma sInter_inc_of_compatible (hs : s.Nonempty) (hG : s.Pairwise Dup_agree)
    (hG' : s.Pairwise Compatible) :
    (Graph.sInter s hs).Inc e x ↔ ∀ G ∈ s, G.Inc e x := by
  let _ : Nonempty s := hs.to_subtype
  rw [Graph.sInter, iInter_inc_of_compatible hG.subtype hG'.subtype]
  simp

@[simp]
lemma sInter_isLoopAt_iff (hs : s.Nonempty) (hG : s.Pairwise Dup_agree) :
    (Graph.sInter s hs).IsLoopAt e x ↔ ∀ G ∈ s, G.IsLoopAt e x := by
  rw [IsLoopAt, sInter_isLink_of_agree hs hG]
  simp

@[simp]
lemma sInter_isNonloopAt_iff (hs : s.Nonempty) (hG : s.Pairwise Dup_agree) :
    (Graph.sInter s hs).IsNonloopAt e x ↔
    ∃ y, ¬ (Graph.sInter s hs).Dup x y ∧ ∀ G ∈ s, G.IsLink e x y := by
  rw [IsNonloopAt, sInter_isLink_of_agree hs hG]
  simp

-- @[simp]
-- lemma induce_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (X : Set α) :
--     (Graph.sInter s hs)[X] = .sInter ((·[X]) '' s) (by simpa) := by
--   refine Graph.ext (by simp; exact (biInter_const hs X).symm) fun e x y ↦ ?_
--   simp +contextual only [induce_isLink_iff, sInter_isLink, mem_image, forall_exists_index,
--     and_imp, forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, true_and]
--   exact fun h ↦ (h _ hs.some_mem).right

-- @[simp]
-- lemma vertexDelete_sInter (hs : s.Nonempty) (hG : s.Pairwise Dup_agree) (X : Set α) :
--     (Graph.sInter s hs) - X = .sInter ((· - X) '' s) (by simpa) := by
--   let _ : Nonempty s := hs.to_subtype
--   unfold Graph.sInter
--   rw [vertexDelete_iInter hG.subtype]
--   sorry

-- @[simp]
-- lemma edgeDelete_sInter (hs : s.Nonempty) (hG : s.Pairwise Dup_agree) (F : Set β) :
--     (Graph.sInter s hs) ＼ F = .sInter ((· ＼ F) '' s) (by simpa) := by
--   let _ : Nonempty s := hs.to_subtype
--   unfold Graph.sInter
--   rw [edgeDelete_iInter hG.subtype]
--   sorry

-- @[simp]
-- lemma edgeRestrict_sInter (hs : s.Nonempty) (hG : s.Pairwise Dup_agree) (F : Set β) :
--     (Graph.sInter s hs) ↾ F = .sInter ((· ↾ F) '' s) (by simpa) := by
--   let _ : Nonempty s := hs.to_subtype
--   unfold Graph.sInter
--   rw [edgeRestrict_iInter hG.subtype]
--   sorry

/-! ### Intersections -/

/-- The intersection of two graphs `G` and `H`. There seems to be no good way to
defined junk values so that this has the right edge and vertex set, so the
edges are precisely those on which `G` and `H` agree, and the edge set is a subset
of `E(G) ∩ E(H)`,
with equality if `G` and `H` are compatible.   -/
protected def inter (G H : Graph α β) : Graph α β :=
  Graph.sInter {G, H} (by simp)

instance : Inter (Graph α β) where inter := Graph.inter

@[simp]
protected lemma sInter_pair (G H : Graph α β) : Graph.sInter {G, H} (by simp) = G ∩ H := rfl

@[simp]
lemma inter_dup : (G ∩ H).Dup = G.Dup ⊓ H.Dup := by
  ext x y
  rw [← Graph.sInter_pair, sInter_dup (by simp), iInf_pair]

@[simp]
lemma inter_vertexSet : V(G ∩ H) = V(G) ∩ V(H) := by
  rw [← Graph.sInter_pair, sInter_vertexSet, biInter_pair]

@[simp]
lemma inter_isLink : (G ∩ H).IsLink e x y ↔ G.Dup x = H.Dup x ∧ G.Dup y = H.Dup y ∧
    G.IsLink e x y ∧ H.IsLink e x y := by
  let G' := Classical.arbitrary (Set.Elem {G, H})
  simp only [← Graph.sInter_pair, sInter_isLink, mem_insert_iff, mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  change (_ = G'.val.Dup x ∧ _ = G'.val.Dup y ∧ _) ∧ _ = G'.val.Dup x ∧ _ = G'.val.Dup y ∧ _ ↔ _
  obtain hG' | hG' : G' = G ∨ G' = H := G'.prop <;>
  · simp_rw [hG']
    simp +contextual [iff_def]

@[simp]
lemma inter_edgeSet : E(G ∩ H) = {e | ∃ x y, (G ∩ H).IsLink e x y} := by
  rw [edgeSet_eq_setOf_exists_isLink]

@[simp↓]
lemma inter_isLink_of_agree (hG : G.Dup_agree H) :
    (G ∩ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := by
  rw [← Graph.sInter_pair, sInter_isLink_of_agree (by simp) (pairwise_pair_of_symm hG)]
  simp

@[simp↓]
lemma inter_edgeSet_of_agree (hG : G.Dup_agree H) (hG' : G.Compatible H) :
    E(G ∩ H) = E(G) ∩ E(H) := by
  rw [← Graph.sInter_pair, sInter_edgeSet_of_agree (by simp) (pairwise_pair_of_symm hG)
    (pairwise_pair_of_symm hG')]
  simp

protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G := by
  rw [← Graph.sInter_pair, ← Graph.sInter_pair]
  congr 1
  exact pair_comm G H

lemma inter_edgeSet_subset : E(G ∩ H) ⊆ E(G) ∩ E(H) := by
  simp +contextual only [inter_edgeSet, inter_isLink, exists_and_left, subset_def, mem_setOf_eq,
    mem_inter_iff, forall_exists_index, and_imp]
  exact fun e x _ y _ hG hH ↦ ⟨hG.edge_mem, hH.edge_mem⟩

@[simp]
lemma inter_inc : (G ∩ H).Inc e x ↔ G.Dup x = H.Dup x ∧
    ∃ x_1, G.Dup x_1 = H.Dup x_1 ∧ G.IsLink e x x_1 ∧ H.IsLink e x x_1 := by
  simp [Inc]

@[simp↓]
lemma Dup_agree.inter_inc (hG : G.Dup_agree H) :
    (G ∩ H).Inc e x ↔ ∃ y, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [Inc, hG]

@[simp]
lemma inter_isLoopAt_iff (hG : G.Dup_agree H) :
    (G ∩ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x := by
  rw [← Graph.sInter_pair, sInter_isLoopAt_iff (by simp) (pairwise_pair_of_symm hG)]
  simp

@[simp]
lemma inter_isNonloopAt_iff (hG : G.Dup_agree H) :
    (G ∩ H).IsNonloopAt e x ↔ ∃ y, ¬ (G ∩ H).Dup x y ∧ G.IsLink e x y ∧ H.IsLink e x y := by
  rw [← Graph.sInter_pair, sInter_isNonloopAt_iff (by simp) (pairwise_pair_of_symm hG)]
  simp

@[simp]
protected lemma inter_le_left (hG : G.Dup_agree H) : G ∩ H ≤ G := by
  rw [← Graph.sInter_pair]
  exact Graph.sInter_le (pairwise_pair_of_symm hG) (by simp)

@[simp]
protected lemma inter_le_right (hG : G.Dup_agree H) : G ∩ H ≤ H := by
  rw [← Graph.sInter_pair]
  exact Graph.sInter_le (pairwise_pair_of_symm hG) (by simp)

protected lemma le_inter (hG : G₁.Dup_agree G₂) (h₁ : H ≤ G₁) (h₂ : H ≤ G₂) : H ≤ G₁ ∩ G₂ := by
  rw [← Graph.sInter_pair, Graph.le_sInter_iff (by simp) (pairwise_pair_of_symm hG)]
  simp [h₁, h₂]

lemma Compatible.inter_edgeSet (h : G.Compatible H) (hG : G.Dup_agree H) :
    E(G ∩ H) = E(G) ∩ E(H) := by
  rw [← Graph.sInter_pair, sInter_edgeSet_of_agree (by simp) (pairwise_pair_of_symm hG)
    (pairwise_pair_of_symm h)]
  simp

@[simp↓]
lemma Compatible.inter_inc (hG : G.Dup_agree H) (hG' : G.Compatible H) :
    (G ∩ H).Inc e x ↔ G.Inc e x ∧ H.Inc e x := by
  simp [← Graph.sInter_pair, sInter_inc_of_compatible (by simp) (pairwise_pair_of_symm hG)
    (pairwise_pair_of_symm hG')]

lemma inter_eq_iInter (hG : G.Dup_agree H) : G ∩ H = Graph.iInter (fun b ↦ bif b then G else H) :=
  let h : Pairwise (Dup_agree on (fun b ↦ bif b then G else H)) :=
    (pairwise_on_bool IsSymm.symm).mpr hG
  Graph.ext (by
    rw [← Graph.sInter_pair, ← Graph.sInter_range h]
    simp [Graph.inter_comm]) (by simp [hG, h, and_comm])

lemma le_inter_iff (hG : G₁.Dup_agree G₂) : H ≤ G₁ ∩ G₂ ↔ H ≤ G₁ ∧ H ≤ G₂ := by
  simp [← Graph.sInter_pair, Graph.le_sInter_iff (by simp) (pairwise_pair_of_symm hG)]

lemma inter_eq_self_of_le (hle : G ≤ H) : G ∩ H = G :=
  le_antisymm (Graph.inter_le_left (dup_agree_of_le hle)) <| by
    simpa [le_inter_iff (dup_agree_of_le hle)]

-- lemma le_of_inter_eq_self (h : G ∩ H = G) : G ≤ H := by
--   rw [← h]
--   exact Graph.inter_le_right

lemma inter_mono_left (hG : G₂.Dup_agree H) (hle : G₁ ≤ G₂) : G₁ ∩ H ≤ G₂ ∩ H := by
  rw [le_inter_iff hG]
  exact ⟨(Graph.inter_le_left (hG.mono_left hle)).trans hle,
    Graph.inter_le_right (hG.mono_left hle)⟩

lemma inter_mono_right (hG : G.Dup_agree H₂) (hle : H₁ ≤ H₂) : G ∩ H₁ ≤ G ∩ H₂ := by
  rw [le_inter_iff hG]
  exact ⟨Graph.inter_le_left (hG.mono_right hle),
    (Graph.inter_le_right (hG.mono_right hle)).trans hle⟩

lemma inter_mono (hG : G₂.Dup_agree H₂) (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) : G₁ ∩ H₁ ≤ G₂ ∩ H₂ :=
  (inter_mono_right (hG.mono_left hleG) hleH).trans (inter_mono_left hG hleG)

-- lemma edgeSet_induce_inter_eq_edgeSet_induce_of_le (h : G ≤ H) : E(G) ∩ E(H[X]) = E(G[X]) :=
--   Set.ext fun _ ↦ ⟨fun ⟨he, x, y, hl, hx, hy⟩ => ⟨x, y, hl.of_le_of_mem h he, hx, hy⟩,
--     fun ⟨x, y, hl, hx, hy⟩ => ⟨hl.edge_mem, x, y, hl.of_le h, hx, hy⟩⟩

-- lemma induce_inter (X Y : Set α) : G[X ∩ Y] = G[X] ∩ G[Y] :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [induce_isLink_iff, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
--     implies_true]

-- lemma induce_inter_distrib (X : Set α) : (G ∩ H)[X] = G[X] ∩ H[X] :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [induce_isLink_iff, inter_isLink_iff, iff_def, and_self, implies_true]

-- lemma vertexDelete_union (X Y : Set α) : G - (X ∪ Y) = (G - X) ∩ (G - Y) := by
--   refine Graph.ext (by simp) fun e x y ↦ by
--     rw [inter_isLink_of_agree sorry]
--     simp +contextual [iff_def]

-- lemma vertexDelete_inter_distrib (X : Set α) : (G ∩ H) - X = (G - X) ∩ (H - X) :=
--   Graph.ext (by simp [diff_inter_distrib_right]) fun e x y ↦ by
--   simp +contextual only [vertexDelete_isLink_iff, inter_isLink_iff, iff_def, not_false_eq_true,
--     and_self, implies_true]

-- lemma edgeDelete_union (F₁ F₂ : Set β) : G ＼ (F₁ ∪ F₂) = (G ＼ F₁) ∩ (G ＼ F₂) :=
--   Graph.ext (by simp [diff_inter_diff]) fun e x y ↦ by
--   simp +contextual only [edgeDelete_isLink, mem_union, not_or, inter_isLink_iff, iff_def,
--     not_false_eq_true, and_self, implies_true]

-- lemma edgeDelete_inter_distrib (F : Set β) : (G ∩ H) ＼ F = (G ＼ F) ∩ (H ＼ F) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeDelete_isLink, inter_isLink_iff, iff_def, not_false_eq_true,
--     and_self, implies_true]

-- lemma edgeRestrict_inter (F₁ F₂ : Set β) : (G ↾ (F₁ ∩ F₂)) = (G ↾ F₁) ∩ (G ↾ F₂) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeRestrict_isLink, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
--     implies_true]

-- lemma edgeRestrict_inter_distrib (F : Set β) : (G ∩ H) ↾ F = (G ↾ F) ∩ (H ↾ F) :=
--   Graph.ext (by simp) fun e x y ↦ by
--   simp +contextual only [edgeRestrict_isLink, inter_isLink_iff, iff_def, and_self, implies_true]

-- protected lemma inter_distrib_iInter [Nonempty ι] {H : ι → Graph α β} :
--     G ∩ (Graph.iInter H) = Graph.iInter (fun i ↦ G ∩ (H i)) :=
--   Graph.ext (by simp [inter_iInter]) (by
--     simp only [inter_isLink_iff, iInter_isLink]
--     rintro i x y
--     rw [forall_and_left])

-- protected lemma inter_distrib_sInter [Nonempty ι] {s : Set (Graph α β)} (hne : s.Nonempty) :
--     G ∩ (Graph.sInter s hne) = Graph.sInter ((G ∩ ·) '' s) (by simpa) := by
--   rw [Graph.sInter_image hne]
--   unfold Graph.sInter
--   have := hne.to_subtype
--   rw [Graph.inter_distrib_iInter]

-- protected lemma inter_distrib_iUnion {H : ι → Graph α β} (hH : Pairwise (Compatible on H)) :
--     G ∩ (Graph.iUnion H hH) = Graph.iUnion (fun i ↦ G ∩ (H i))
--       (fun _ _ hne ↦ (hH hne).mono Graph.inter_le_right Graph.inter_le_right) :=
--   Graph.ext (by simp [inter_iUnion]) (by simp)

-- protected lemma inter_distrib_sUnion (hs : s.Pairwise Compatible) :
--     G ∩ (Graph.sUnion s hs) = Graph.sUnion ((fun K ↦ G ∩ K) '' s) (by
--       rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
--       exact (hs.of_refl hK₁ hK₂).mono Graph.inter_le_right Graph.inter_le_right) := by
--   ext <;> aesop

-- lemma Pairwise.union_compatible {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
--     (Graph.sUnion s (hst.mono subset_union_left)).Compatible
--     (Graph.sUnion t (hst.mono subset_union_right)) := by
--   refine compatible_of_le_le (G := Graph.sUnion (s ∪ t) hst) ?_ ?_ <;> rw [Graph.sUnion_le_iff]
--   <;> exact fun G hG ↦ Graph.le_sUnion hst (by simp [hG])

-- lemma sUnion_union_sUnion {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
--     Graph.sUnion s (hst.mono subset_union_left) ∪ Graph.sUnion t (hst.mono subset_union_right) =
--     Graph.sUnion (s ∪ t) hst := by
--   have hs : s.Pairwise Compatible := hst.mono subset_union_left
--   have ht : t.Pairwise Compatible := hst.mono subset_union_right
--   refine Graph.ext (by aesop) fun e x y ↦ ?_
--   rw [(Pairwise.union_compatible hst).union_isLink_iff]
--   aesop

-- protected lemma sInter_inter_sInter {s t : Set (Graph α β)} (hs : s.Nonempty) (ht : t.Nonempty) :
--     Graph.sInter s hs ∩ .sInter t ht = .sInter (s ∪ t) (by simp [hs]) := by
--   ext <;> aesop

-- lemma Compatible.sum_compatible {G : ι → Graph α β} {H : ι' → Graph α β}
--     (hGH : Pairwise (Compatible on (Sum.elim G H))) :
--     (Graph.iUnion G (hGH.sum_left)).Compatible (Graph.iUnion H (hGH.sum_right)) :=
--   compatible_of_le_le (iUnion_left_le_iUnion_sum hGH) <| iUnion_right_le_iUnion_sum hGH

-- protected lemma iUnion_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
--     {H : ι' → Graph α β} (hGH : Pairwise (Compatible on (Sum.elim G H))) :
--     Graph.iUnion (Sum.elim G H) hGH = (.iUnion G hGH.sum_left) ∪ (.iUnion H hGH.sum_right) := by
--   refine le_antisymm ?_ <| Graph.union_le (iUnion_left_le_iUnion_sum hGH)
--     (iUnion_right_le_iUnion_sum hGH)
--   rw [Graph.iUnion_le_iff]
--   rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
--   · exact le_trans (Graph.le_iUnion hGH.sum_left i) (Graph.left_le_union _ _)
--   · exact le_trans (Graph.le_iUnion hGH.sum_right i)
--       (Compatible.right_le_union (Compatible.sum_compatible hGH))

-- protected lemma iInter_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
--     {H : ι' → Graph α β} : Graph.iInter (Sum.elim G H) = .iInter G ∩ .iInter H := by
--   ext <;> aesop

-- protected lemma iInter_option [Nonempty ι] {G₁ : Graph α β} {G : ι → Graph α β} :
--     Graph.iInter (Option.elim · G₁ G) = G₁ ∩ Graph.iInter G :=
--   Graph.ext (by simp [Set.iInter_option]) (by simp [Option.forall])

-- protected lemma sInter_insert {s : Set (Graph α β)} (G : Graph α β) (hne : s.Nonempty) :
--     Graph.sInter (insert G s) (by simp) = G ∩ Graph.sInter s hne := by
--   ext v <;> simp

-- lemma iInter_option_eq_sInter_insert {G₁ : Graph α β} {G : ι → Graph α β} :
--     Graph.iInter (Option.elim · G₁ G) = Graph.sInter (insert G₁ (range G)) (by simp) := by
--   obtain hι | hι := isEmpty_or_nonempty ι
--   · simp [range_eq_empty G]
--   rw [Graph.sInter_insert _ (range_nonempty _), Graph.sInter_range, Graph.iInter_option]

-- -- protected lemma union_iInter [Nonempty ι] {H : ι → Graph α β} (hc : ∀ i, G.Compatible (H i))
-- --     (hH : Pairwise (Compatible on H)) :
-- --     G ∪ (Graph.iInter H hH) = Graph.iInter (fun i ↦ G ∪ (H i))
-- --     (by
-- --       refine fun i j hij ↦ (h)
-- --     )

-- --     := by
-- --   _

--   -- rw [Graph.sUnion, Graph.sUnion]
--   -- generalize_proofs h₁ h₂
--   -- rw [Graph.inter_distrib_iUnion _]
