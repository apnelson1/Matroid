import Matroid.Graph.Subgraph.Agree

variable {α β ι ι' : Type*} [CompleteLattice α] {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β}
  {X Y : Set α} {P Q : Partition α} {Gs Gs' Hs : Set (Graph α β)}
  {G G' G₁ G₂ H H' H₁ H₂ : Graph α β} {Gι Hι : ι → Graph α β} {Gι' Hι' : ι' → Graph α β}

open Set Function Partition

namespace Graph

/-- The union of a set of graphs. In the case where there does not exist a suitable common
  supergraph, it returns `⊥`. -/
protected noncomputable def sUnion (Gs : Set (Graph α β)) : Graph α β :=
  (⨆ G ∈ Gs, WithTop.some G).get!

@[simp]
lemma sUnion_eq_sUnion' (hs' : Agree Gs) :
    Graph.sUnion Gs = sUnion' Gs hs'.choose hs'.choose_spec := by
  unfold Graph.sUnion
  rw [hs'.biSup_some_eq]
  rfl

@[simp]
lemma sUnion_of_not_agree (hs : ¬ Agree Gs) : Graph.sUnion Gs = ⊥ := by
  unfold Graph.sUnion
  rw [Agree.biSup_some_eq_top_iff.mpr hs]
  rfl

@[simp]
lemma sUnion_vertexSet (hs' : Agree Gs) : V(Graph.sUnion Gs) = ⋃ G ∈ Gs, V(G) := by
  simp [sUnion_eq_sUnion' hs']

@[simp]
lemma sUnion_edgeSet (hs' : Agree Gs) : E(Graph.sUnion Gs) = ⋃ G ∈ Gs, E(G) := by
  simp [sUnion_eq_sUnion' hs']

@[simp]
lemma sUnion_isLink (hs' : Agree Gs) :
    (Graph.sUnion Gs).IsLink e x y ↔ ∃ G ∈ Gs, G.IsLink e x y := by
  simp [sUnion_eq_sUnion' hs']

@[simp]
lemma sUnion_le_iff (hs' : Agree Gs) : Graph.sUnion Gs ≤ H ↔ ∀ G ∈ Gs, G ≤ H := by
  simp [hs']

lemma le_sUnion (hs' : Agree Gs) (h : G ∈ Gs) : G ≤ Graph.sUnion Gs := by
  rw [sUnion_eq_sUnion' hs']
  exact le_sUnion' hs'.choose_spec h

lemma sUnion_induce (hs' : Agree Gs) (X : Set α) :
    (Graph.sUnion Gs)[X] = Graph.sUnion ((·[X]) '' Gs) := by
  rw [sUnion_eq_sUnion' hs', sUnion_eq_sUnion' (hs'.induce X)]
  refine Graph.ext (by simp [iUnion_inter]) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sUnion'_isLink,
      exists_exists_and_eq_and, induce_isLink]
  tauto

lemma sUnion_vertexDelete (hs' : Agree Gs) (X : Set α) :
    (Graph.sUnion Gs) - X = Graph.sUnion ((·-X) '' Gs) := by
  rw [sUnion_eq_sUnion' hs', sUnion_eq_sUnion' (hs'.vertexDelete X)]
  refine Graph.ext (by simp [iUnion_diff]) ?_
  simp only [vertexDelete_isLink_iff, sUnion'_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, exists_exists_and_eq_and]
  tauto

lemma sUnion_edgeRestrict (hs' : Agree Gs) (F : Set β) :
    (Graph.sUnion Gs) ↾ F = Graph.sUnion ((·↾F) '' Gs) := by
  rw [sUnion_eq_sUnion' hs', sUnion_eq_sUnion' (hs'.edgeRestrict F)]
  refine Graph.ext (by simp) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sUnion'_isLink,
      exists_exists_and_eq_and, edgeRestrict_isLink]
  tauto

lemma sUnion_edgeDelete (hs' : Agree Gs) (F : Set β) :
    (Graph.sUnion Gs) ＼ F = Graph.sUnion ((·＼F) '' Gs) := by
  rw [sUnion_eq_sUnion' hs', sUnion_eq_sUnion' (hs'.edgeDelete F)]
  refine Graph.ext (by simp) ?_
  simp only [edgeDelete_isLink, sUnion'_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, exists_exists_and_eq_and]
  tauto

lemma subset_le_sUnion (hs' : Agree Gs) : Gs ⊆ {H | H ≤ Graph.sUnion Gs} := by
  rintro G hG
  simp only [hs', sUnion_eq_sUnion', mem_setOf_eq]
  exact le_sUnion' _ hG

lemma agree_le_sUnion : Agree {H | H ≤ Graph.sUnion Gs} := by
  use Graph.sUnion Gs, fun _ hle ↦ hle

lemma agree_sUnion_image_iff {GS : Set (Set (Graph α β))} (hagree : ∀ Gs ∈ GS, Agree Gs) :
    Agree (Graph.sUnion '' GS) ↔ Agree (⋃₀ GS) := by
  refine ⟨fun h => h.mono fun G hG ↦ ?_, fun h => ?_⟩
  · simp_all only [sUnion_eq_sUnion', mem_sUnion, mem_image, exists_exists_and_eq_and]
    obtain ⟨Gs, hGs, hGGs⟩ := hG
    exact ⟨Gs, hGs, le_sUnion (hagree Gs hGs) hGGs⟩
  obtain ⟨H, hH⟩ := h
  use H
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rintro Gs hGs
  rw [Graph.sUnion_le_iff (hagree Gs hGs)]
  exact fun G hG ↦ hH G <| mem_sUnion_of_mem hG hGs

lemma sUnion_sUnion_image {GS : Set (Set (Graph α β))} (hagree : ∀ Gs ∈ GS, Agree Gs) :
    Graph.sUnion (Graph.sUnion '' GS) = Graph.sUnion (⋃₀ GS) := by
  by_cases h : Agree (Graph.sUnion '' GS) <;> have h' := (by
    rwa [agree_sUnion_image_iff hagree] at h) <;> apply Graph.ext ?_ fun e x y ↦ ?_
  · have : ⋃ y ∈ GS, V(Graph.sUnion y) = ⋃ y ∈ GS, ⋃ x ∈ y, V(x) :=
      iUnion₂_congr fun Gs hGs ↦ by simp [hagree Gs hGs]
    simp [h, h', this]
  · have : (∃ a ∈ GS, (Graph.sUnion a).IsLink e x y) ↔ ∃ G, (∃ t ∈ GS, G ∈ t) ∧ G.IsLink e x y := by
      refine ⟨fun ⟨Gs, hGs, h⟩ => ?_, fun ⟨G, ⟨Gs, hGs, hGGs⟩, hG⟩ => ?_⟩
      · obtain ⟨G, hGGs, hG⟩ := by simpa [hagree Gs hGs] using h
        use G, (by use Gs)
      use Gs, hGs
      simp only [hagree Gs hGs, sUnion_eq_sUnion', sUnion'_isLink]
      use G
    simp [h, h', this]
  all_goals simp [h, h']

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} = G := by
  rw [sUnion_eq_sUnion' (by simp)]
  exact sUnion'_singleton G _

/-! ### Indexed unions -/

/-- The union of an indexed family of pairwise compatible graphs. -/
protected noncomputable def iUnion (Gι : ι → Graph α β) : Graph α β :=
  (⨆ i, WithTop.some (Gι i)).get!

@[simp]
lemma iUnion_eq_sUnion' (hs' : Agree (range Gι)) :
    Graph.iUnion Gι = sUnion' (Set.range Gι) hs'.choose hs'.choose_spec := by
  unfold Graph.iUnion
  rw [hs'.iSup_some_eq]
  rfl

@[simp]
lemma iUnion_of_not_agree (hs : ¬ Agree (range Gι)) : Graph.iUnion Gι = ⊥ := by
  unfold Graph.iUnion
  rw [Agree.iSup_some_eq_top_iff.mpr hs]
  rfl

lemma iUnion_eq_sUnion : Graph.iUnion Gι = Graph.sUnion (range Gι) := by
  by_cases h : Agree (range Gι) <;> simp [h]

@[simp]
lemma iUnion_vertexSet (hs' : Agree (range Gι)) : V(Graph.iUnion Gι) = ⋃ i, V(Gι i) := by
  simp [hs']

@[simp]
lemma iUnion_edgeSet (hs' : Agree (range Gι)) : E(Graph.iUnion Gι) = ⋃ i, E(Gι i) := by
  simp [hs']

@[simp]
lemma iUnion_isLink (hs' : Agree (range Gι)) :
    (Graph.iUnion Gι).IsLink e x y ↔ ∃ i, (Gι i).IsLink e x y := by
  simp [hs']

protected lemma le_iUnion (hs' : Agree (range Gι)) (i : ι) : Gι i ≤ Graph.iUnion Gι := by
  rw [iUnion_eq_sUnion' hs']
  exact le_sUnion' _ (by use i)

@[simp]
protected lemma iUnion_le_iff (hs' : Agree (range Gι)) : Graph.iUnion Gι ≤ H ↔ ∀ i, Gι i ≤ H := by
  simp [hs']

@[simp]
protected lemma iUnion_const [Nonempty ι] (G : Graph α β) : Graph.iUnion (fun (_ : ι)↦ G) = G := by
  simp

@[simp]
lemma iUnion_inc (hs' : Agree (range Gι)) :(Graph.iUnion Gι).Inc e x ↔ ∃ i, (Gι i).Inc e x := by
  simp [hs']

@[simp]
lemma iUnion_isLoopAt (hs' : Agree (range Gι)) :
    (Graph.iUnion Gι).IsLoopAt e x ↔ ∃ i, (Gι i).IsLoopAt e x := by
  simp [← isLink_self_iff, hs']

@[simp]
lemma iUnion_isNonloopAt (hs' : Agree (range Gι)) :
    (Graph.iUnion Gι).IsNonloopAt e x ↔ ∃ i, (Gι i).IsNonloopAt e x := by
  simp [hs']

lemma iUnion_map_le_iUnion (hs' : Agree (range Gι)) (f : ι' → ι) :
    (Graph.iUnion (Gι ∘ f)) ≤ Graph.iUnion Gι := by
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion' (hs'.subset <| range_comp_subset_range f Gι)]
  exact sUnion'_mono _ _ <| range_comp_subset_range f Gι

lemma iUnion_left_le_iUnion_sum (hs' : Agree (range (Sum.elim Gι Gι'))) :
    Graph.iUnion Gι ≤ Graph.iUnion (Sum.elim Gι Gι') := by
  have h : range Gι ⊆ range (Sum.elim Gι Gι') := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion' <| hs'.subset h]
  exact sUnion'_mono _ _ h

lemma iUnion_right_le_iUnion_sum (hs' : Agree (range (Sum.elim Gι Gι'))) :
    Graph.iUnion Gι' ≤ Graph.iUnion (Sum.elim Gι Gι') := by
  have h : range Gι' ⊆ range (Sum.elim Gι Gι') := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inr i, rfl⟩
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion' <| hs'.subset h]
  exact sUnion'_mono _ _ h

@[simp]
lemma induce_iUnion [Nonempty ι] (hs' : Agree (range Gι)) (X : Set α) :
    (Graph.iUnion Gι)[X] = Graph.iUnion (fun i ↦ (Gι i)[X]) := by
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion' ?_]
  exact Graph.ext (by simp [iUnion_inter]) (by simp)
  · convert hs'.induce X
    rw [← range_comp]
    rfl

@[simp]
lemma vertexDelete_iUnion (hs' : Agree (range Gι)) (X : Set α) :
    (Graph.iUnion Gι) - X = Graph.iUnion (fun i ↦ (Gι i) - X) := by
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion' ?_]
  exact Graph.ext (by simp [iUnion_diff]) (by simp)
  · convert hs'.vertexDelete X
    rw [← range_comp]
    rfl

@[simp]
lemma edgeDelete_iUnion (hs' : Agree (range Gι)) (F : Set β) :
    (Graph.iUnion Gι) ＼ F = Graph.iUnion (fun i ↦ (Gι i) ＼ F) := by
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion' ?_]
  exact Graph.ext (by simp) (by simp)
  · convert hs'.edgeDelete F
    rw [← range_comp]
    rfl

@[simp]
lemma edgeRestrict_iUnion (hs' : Agree (range Gι)) (F : Set β) :
    (Graph.iUnion Gι) ↾ F = Graph.iUnion (fun i ↦ (Gι i) ↾ F) := by
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion' ?_]
  exact Graph.ext (by simp) (by simp)
  · convert hs'.edgeRestrict F
    rw [← range_comp]
    rfl

protected lemma iUnion_comp_le {f : ι' → ι} (hs' : Agree <| range Gι) :
    Graph.iUnion (fun i ↦ Gι (f i)) ≤ Graph.iUnion Gι := by
  rw [iUnion_eq_sUnion' hs', iUnion_eq_sUnion']
  · exact sUnion'_mono _ _ (range_comp_subset_range f Gι)
  exact hs'.subset (range_comp_subset_range f Gι)

lemma iUnion_comp_eq_of_surj {f : ι' → ι} (hs' : Agree <| range Gι) (hf : Function.Surjective f) :
    Graph.iUnion Gι = Graph.iUnion (fun i ↦ Gι (f i)) := by
  refine le_antisymm ?_ (Graph.iUnion_comp_le hs')
  rw [Graph.iUnion_le_iff hs']
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.le_iUnion (hs'.subset <| range_comp_subset_range f Gι) i'

lemma iUnion_range {f : ι' → ι} {Gf : (Set.range f) → Graph α β} (hs' : Agree <| range Gf) :
    Graph.iUnion Gf = Graph.iUnion (Gf <| Set.rangeFactorization f ·) :=
  iUnion_comp_eq_of_surj hs' rangeFactorization_surjective


/-! ### Unions of pairs -/

/-- The union of two graphs `G` and `H`. Unlike `WithTop (Graph α β)`, as the error value is `⊥`
  rather than `⊤`, this is not associative in general. -/
protected noncomputable def union (G H : Graph α β) := (WithTop.some G ⊔ WithTop.some H).get!

noncomputable instance : Union (Graph α β) where union := Graph.union

variable {G H H₁ H₂ : Graph α β}

@[simp]
lemma union_eq_sUnion' (h : Agree {G, H}) :
    G ∪ H = Graph.sUnion' {G, H} h.choose h.choose_spec := by
  change (WithTop.some G ⊔ WithTop.some H).get! = _
  rw [h.sup_some_eq]
  rfl

lemma union_eq_bot_of_not_agree (h : ¬ Agree {G, H}) : G ∪ H = ⊥ := by
  change (WithTop.some G ⊔ WithTop.some H).get! = ⊥
  rw [Agree.sup_some_eq_top_iff.mpr h]
  rfl

@[simp]
lemma union_vertexSet (h : Agree {G, H}) : V(G ∪ H) = V(G) ∪ V(H) := by
  simp [h]

@[simp]
lemma union_vertexSet_of_not_agree (h : ¬ Agree {G, H}) : V(G ∪ H) = ∅ := by
  simp [union_eq_bot_of_not_agree h]

@[simp]
lemma union_isLink (h : Agree {G, H}) : (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  simp [h]

@[simp]
lemma union_isLink_of_not_agree (h : ¬ Agree {G, H}) : ¬ (G ∪ H).IsLink e x y := by
  simp [union_eq_bot_of_not_agree h]

@[simp]
lemma union_edgeSet (h : Agree {G, H}) : E(G ∪ H) = E(G) ∪ E(H) := by
  simp [h]

@[simp]
lemma union_edgeSet_of_not_agree (h : ¬ Agree {G, H}) : E(G ∪ H) = ∅ := by
  simp [union_eq_bot_of_not_agree h]

protected lemma sUnion_pair : Graph.sUnion {G, H} = G ∪ H := by
  change (⨆ G ∈ _, WithTop.some G).get! = (WithTop.some G ⊔ WithTop.some H).get!
  rw [iSup_pair]

protected lemma union_comm : G ∪ H = H ∪ G := by
  rw [← Graph.sUnion_pair, ← Graph.sUnion_pair, pair_comm]

lemma sUnion_union_sUnion (hGs : Agree Gs) (hHs : Agree Hs) :
    Graph.sUnion Gs ∪ Graph.sUnion Hs = Graph.sUnion (Gs ∪ Hs) := by
  rw [← Graph.sUnion_pair, ← image_pair, sUnion_sUnion_image (by simp [hGs, hHs]), sUnion_pair]

protected lemma sUnion_insert (hGs : Agree Gs) : .sUnion (insert G Gs) = G ∪ Graph.sUnion Gs := by
  nth_rw 2 [← Graph.sUnion_singleton G]
  rw [sUnion_union_sUnion (by simp) hGs]
  exact Graph.ext (by simp) <| by simp

protected lemma union_assoc {J : Graph α β} (hGH : Agree {G, H}) (hHJ : Agree {H, J}) :
    (G ∪ H) ∪ J = G ∪ (H ∪ J) := by
  rw [← Graph.sUnion_pair (G := H), ← Graph.sUnion_insert hHJ, ← Graph.sUnion_pair (G := G),
    Graph.union_comm, ← Graph.sUnion_insert hGH]
  congr 1
  aesop

lemma union_assoc' {J : Graph α β} (h : Agree {G, H, J}) : (G ∪ H) ∪ J = G ∪ (H ∪ J) :=
  Graph.union_assoc (h.subset <| by simp [pair_subset]) <| h.subset <| by simp

@[simp]
protected lemma left_le_union (hGH : Agree {G, H}) : G ≤ G ∪ H := by
  rw [union_eq_sUnion' hGH]
  exact le_sUnion' _ (by simp)

lemma right_le_union (hGH : Agree {G, H}) : H ≤ G ∪ H := by
  rw [union_eq_sUnion' hGH]
  exact le_sUnion' _ (by simp)

protected lemma union_le (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  have hGH : Agree {H₁, H₂} := by use G, (by simp [h₁, h₂])
  rw [union_eq_sUnion' hGH]
  exact sUnion'_le _ (by simp [h₁, h₂])

lemma union_le_iff (h' : Agree {H₁, H₂}) : H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G :=
  ⟨fun h => ⟨(Graph.left_le_union h').trans h, (Graph.right_le_union h').trans h⟩,
    fun ⟨h₁, h₂⟩ => Graph.union_le h₁ h₂⟩

@[simp]
protected lemma union_self (G : Graph α β) : G ∪ G = G :=
  (Graph.union_le le_rfl le_rfl).antisymm <| Graph.left_le_union (by simp) ..

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  rw [union_eq_sUnion' (by use G, (by simp))]
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [edgeRestrict_isLink, mem_union, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
    forall_eq, sUnion'_isLink, exists_eq_or_imp, ↓existsAndEq, true_and]
  tauto

lemma union_edgeRestrict_distrib (G H : Graph α β) (hGH : Agree {G, H}) (F : Set β) :
    (G ∪ H) ↾ F = G ↾ F ∪ (H ↾ F) := by
  rw [union_eq_sUnion' hGH, union_eq_sUnion' <| by simpa only [image_pair] using hGH.edgeRestrict F]
  exact Graph.ext (by simp) fun e x y ↦ by simp [and_or_left]

@[simp]
lemma union_inc (hGH : Agree {G, H}) : (G ∪ H).Inc e x ↔ G.Inc e x ∨ H.Inc e x := by
  simp [hGH]

@[simp]
lemma union_isLoopAt (hGH : Agree {G, H}) :
    (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ H.IsLoopAt e x := by
  simp [← isLink_self_iff, hGH]

@[simp]
lemma union_isNonloopAt (hGH : Agree {G, H}) :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ H.IsNonloopAt e x := by
  simp only [IsNonloopAt, ne_eq, hGH, union_eq_sUnion', mem_insert_iff, mem_singleton_iff,
    forall_eq_or_imp, forall_eq, sUnion'_isLink, exists_eq_or_imp, ↓existsAndEq, true_and]
  refine ⟨fun ⟨y, hne, hy⟩ => hy.imp (⟨y, hne, ·⟩) (⟨y, hne, ·⟩), ?_⟩
  rintro (⟨y, hne, hy⟩ | ⟨y, hne, hy⟩)
  · use y, hne, Or.inl hy
  · use y, hne, Or.inr hy

lemma union_adj (hGH : Agree {G, H}) : (G ∪ H).Adj x y ↔ G.Adj x y ∨ H.Adj x y := by
  simp [Adj, hGH, exists_or]

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (Graph.union_le hle rfl.le).antisymm <| right_le_union <|
    agree_of_le hle

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (Graph.union_le rfl.le hle).antisymm <| Graph.left_le_union (agree_of_le hle).symm ..

lemma union_mono_right (hGH : Agree {G, H₂}) (h : H₁ ≤ H₂) : G ∪ H₁ ≤ G ∪ H₂ := by
  rw [union_eq_sUnion' hGH, union_eq_sUnion' (hGH.mono (by simp [h]))]
  simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, sUnion'_le_iff]
  exact ⟨le_sUnion' _ (by simp), h.trans <| le_sUnion' _ (by simp)⟩

lemma union_mono_left (hGH : Agree {G, H₂}) (hle : H₁ ≤ H₂) : H₁ ∪ G ≤ H₂ ∪ G := by
  rw [Graph.union_comm, Graph.union_comm (G := H₂)]
  exact union_mono_right hGH hle

lemma union_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) (h : Agree {G₂, H₂}) : G₁ ∪ H₁ ≤ G₂ ∪ H₂ := by
  refine le_trans (union_mono_left ?_ hleG) (union_mono_right h hleH)
  rw [Set.pair_comm]
  exact h.mono (by simp [hleH])

lemma edgeRestrict_union_edgeDelete (G : Graph α β) (F : Set β) : (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α β) (F : Set β) : (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Graph.union_comm]

lemma induce_union_edgeDelete (G : Graph α β) : G[X] ∪ (G ＼ E(G[X])) = G := by
  refine Graph.ext ?_ fun e x y ↦ ?_ <;> rw [union_eq_sUnion' (by use G, (by simp))]
  · simp
  simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, sUnion'_isLink,
    exists_eq_or_imp, ↓existsAndEq, edgeDelete_isLink, true_and]
  by_cases he : e ∈ E(G[X])
  · simp only [induce_isLink, he, not_true_eq_false, and_false, or_false, and_iff_left_iff_imp]
    exact (·.mem_induce_iff.mp he)
  simp [he]

lemma edgeDelete_union_induce (G : Graph α β) : (G ＼ E(G[X])) ∪ G[X] = G := by
  rw [Graph.union_comm, induce_union_edgeDelete G]

lemma union_eq_iUnion : G ∪ H = Graph.iUnion (fun b ↦ bif b then G else H) := by
  have h' : {G, H} = range fun b ↦ bif b then G else H := by simp [pair_comm]
  by_cases h : Agree {G, H}
  · rw [union_eq_sUnion' h, iUnion_eq_sUnion' (by rwa [← h'])]
    simp [h']
  rw [union_eq_bot_of_not_agree h, iUnion_of_not_agree (by rwa [← h'])]

lemma union_induce (hGH : Agree {G, H}) (X : Set α) : (G ∪ H)[X] = G[X] ∪ H[X] := by
  rw [← Graph.sUnion_pair, sUnion_induce hGH, image_pair, Graph.sUnion_pair]

lemma union_vertexDelete (h : Agree {G, H}) (X : Set α) : (G ∪ H) - X = (G - X) ∪ (H - X) := by
  rw [← Graph.sUnion_pair, sUnion_vertexDelete h, image_pair, Graph.sUnion_pair]

-- protected lemma sUnion_image {s : Set ι} {f : ι → Graph α β}
--     (hs : s.Pairwise (Graph.Compatible on f)) :
--     Graph.sUnion (f '' s) hs.image = .iUnion (f · : s → _) (Pairwise.restrict.mpr hs) := by
--   rw [Graph.sUnion]
--   let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
--   exact Graph.iUnion_comp_eq_of_surj (f := f') _ (fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩)

-- protected lemma sUnion_range {f : ι → Graph α β} (h : Pairwise (Graph.Compatible on f)) :
--     Graph.sUnion (Set.range f) h.range_pairwise = .iUnion f h := by
--   unfold Graph.sUnion
--   exact Graph.iUnion_comp_eq_of_surj (f := Set.rangeFactorization f) _ surjective_onto_range

-- @[simp]
-- lemma noEdge_union_eq_self : Graph.noEdge P β ∪ G = G ↔ P ≤ P(G) := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · rw [← h]
--     convert left_vertexPartition_le_union
--     rfl
--   refine vertexPartition_ext (by simpa) fun e x y ↦ ?_
--   simp only [union_isLink_not_agree, noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
--     not_isLink_of_notMem_edgeSet, and_true, false_or, union_vertexPartition,
--noEdge_vertexPartition,
--     h, sup_of_le_right]
--   refine ⟨?_, fun h => ⟨x, y, h, foo_eq_self_of_mem h.left_mem',
--     foo_eq_self_of_mem h.right_mem'⟩⟩
--   rintro ⟨u, v, h, rfl, rfl⟩
--   rwa [foo_eq_self_of_mem h.left_mem', foo_eq_self_of_mem h.right_mem']

-- @[simp]
-- lemma union_noEdge_eq_self : G ∪ Graph.noEdge P β = G ↔ P ≤ P(G) := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · rw [← h]
--     convert right_vertexPartition_le_union
--     rfl
--   refine vertexPartition_ext (by simpa) fun e x y ↦ ?_
--   simp only [union_isLink_not_agree, noEdge_edgeSet, mem_empty_iff_false, not_false_eq_true,
--     not_isLink_of_notMem_edgeSet, false_and, or_false, union_vertexPartition,
--     noEdge_vertexPartition, h, sup_of_le_left]
--   refine ⟨?_, fun h => ⟨x, y, h, foo_eq_self_of_mem h.left_mem',
--     foo_eq_self_of_mem h.right_mem'⟩⟩
--   rintro ⟨u, v, h, rfl, rfl⟩
--   rwa [foo_eq_self_of_mem h.left_mem', foo_eq_self_of_mem h.right_mem']

end Graph
