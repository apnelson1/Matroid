import Matroid.Graph.Subgraph.Compatible
import Matroid.Graph.Subgraph.Inter

variable {α β ι ι' : Type*} [CompleteLattice α] {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β}
  {X Y : Set α} {P Q : Partition α} {Gs Gs' Hs : Set (Graph α β)}
  {G G' G₁ G₂ H H' H₁ H₂ : Graph α β} {Gι Hι : ι → Graph α β} {Gι' Hι' : ι' → Graph α β}

open Set Function Partition

namespace Graph

section Agree

def Agree (Gs : Set (Graph α β)) : Prop := ∃ H : Graph α β, ∀ G ∈ Gs, G ≤ H

lemma agree_of_le (h : G ≤ H) : Agree {G, H} := by
  use H
  rintro _ (rfl | rfl) <;> aesop

@[simp]
lemma agree_empty : Agree (∅ : Set (Graph α β)) := by
  use ⊥
  simp

@[simp]
lemma agree_singleton (G : Graph α β) : Agree {G} := by
  use G
  simp

lemma Agree.symm (hs : Agree {G, H}) : Agree {H, G} := by
  rwa [Set.pair_comm]

lemma Agree.subset (hs : Agree Gs') (h : Gs ⊆ Gs') : Agree Gs := by
  obtain ⟨H, hH⟩ := hs
  use H, fun G hG ↦ hH G (h hG)

lemma Agree.mono (hs : Agree Gs') (h : ∀ G ∈ Gs, ∃ G' ∈ Gs', G ≤ G') : Agree Gs := by
  obtain ⟨H, hH⟩ := hs
  use H, fun G hG ↦ ?_
  obtain ⟨G', hG', hle⟩ := h G hG
  exact hle.trans (hH G' hG')

lemma Agree.induce (hs' : Agree Gs) (X : Set α) : Agree ((Graph.induce · X) '' Gs) := by
  obtain ⟨H, hH⟩ := hs'
  use H[X]
  rintro _ ⟨G, hG, rfl⟩
  exact induce_mono_left (hH G hG) X

lemma Agree.vertexDelete (hs' : Agree Gs) (X : Set α) : Agree ((Graph.vertexDelete · X) '' Gs) := by
  obtain ⟨H, hH⟩ := hs'
  use H - X
  rintro _ ⟨G, hG, rfl⟩
  exact vertexDelete_mono_left (hH G hG) X

lemma Agree.edgeRestrict (hs' : Agree Gs) (F : Set β) : Agree ((Graph.edgeRestrict · F) '' Gs) := by
  obtain ⟨H, hH⟩ := hs'
  use H ↾ F
  rintro _ ⟨G, hG, rfl⟩
  exact edgeRestrict_mono_left (hH G hG) F

lemma Agree.edgeDelete (hs' : Agree Gs) (F : Set β) : Agree ((Graph.edgeDelete · F) '' Gs) := by
  obtain ⟨H, hH⟩ := hs'
  use H ＼ F
  rintro _ ⟨G, hG, rfl⟩
  exact edgeDelete_mono_left (hH G hG) F

lemma Agree.subgraph (hs' : Agree Gs) : Agree {H | ∃ G ∈ Gs, H ≤ G} := by
  obtain ⟨G', hG'⟩ := hs'
  use G'
  rintro _ ⟨G, hG, hle⟩
  exact hle.trans (hG' G hG)

lemma agree_pair_iff : Agree {G, H} ↔ Compatible G H ∧ G.Dup_agree H := by
  refine ⟨fun ⟨G', hG'⟩ => ⟨?_, ?_⟩, fun ⟨hc, hd⟩ => ?_⟩
  · exact compatible_of_le_le (hG' G (by simp)) (hG' H (by simp))
  · exact dup_agree_of_le_le (hG' G (by simp)) (hG' H (by simp))
  let G' : Graph α β := {
    vertexPartition := hd.choose
    IsLink e x y := G.IsLink e x y ∨ H.IsLink e x y
    isLink_symm e he x y := by simp [isLink_comm]
    eq_or_eq_of_isLink_of_isLink e a b c d h h' := by
      obtain (hG | hH) := h <;> obtain (hG' | hH') := h'
      · exact G.eq_or_eq_of_isLink_of_isLink hG hG'
      · have hG' := hc.isLink_eq hG.edge_mem hH'.edge_mem ▸ hH'
        exact G.eq_or_eq_of_isLink_of_isLink hG hG'
      · have hG := hc.isLink_eq hG'.edge_mem hH.edge_mem ▸ hH
        exact G.eq_or_eq_of_isLink_of_isLink hG hG'
      · exact H.eq_or_eq_of_isLink_of_isLink hH hH'
    left_mem_of_isLink e u v he :=
      he.elim (hd.choose_spec.1 ·.left_mem') (hd.choose_spec.2 ·.left_mem')}
  use G'
  simp +contextual only [mem_insert_iff, mem_singleton_iff, le_iff, forall_eq_or_imp, true_or,
    implies_true, and_true, or_true, forall_eq, G']
  exact hd.choose_spec.imp (fun hsu x hx ↦ hsu <| G.vertexSet_eq_parts ▸ hx)
    (fun hsu x hx ↦ hsu <| H.vertexSet_eq_parts ▸ hx)

lemma pairwise_compatible_of_subgraph (h : ∀ i, Hι i ≤ G) : Pairwise (Compatible on Hι) :=
  fun i j _ ↦ compatible_of_le_le (h i) (h j)

lemma set_pairwise_compatible_of_subgraph (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) : Gs.Pairwise Compatible :=
  fun _ hi _ hj _ ↦ compatible_of_le_le (h hi) (h hj)

lemma pairwise_dup_agree_of_subgraph (h : ∀ i, Hι i ≤ G) : Pairwise (Dup_agree on Hι) :=
  fun i j _ ↦ dup_agree_of_le_le (h i) (h j)

lemma set_pairwise_dup_agree_of_subgraph (h : ∀ ⦃H⦄, H ∈ Gs → H ≤ G) : Gs.Pairwise Dup_agree :=
  fun _ hi _ hj _ ↦ dup_agree_of_le_le (h hi) (h hj)

/-- a version of sUnion specifically for a set of subgraphs of some ambient graph.
  The crucial difference other than the additional hypothesis is that this function is defined with
  `[CompleteLattice α]` instance rather than `[Order.Frame α]` instance. -/
@[simps]
def sUnion' (Gs : Set (Graph α β)) (H : Graph α β) (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) : Graph α β where
  vertexPartition := P(H).restrict (⋃ G ∈ Gs, V(G)) (by
    simp only [vertexPartition_parts, iUnion_subset_iff]
    exact fun G hG ↦ (h hG).vertexSet_subset)
  vertexSet := ⋃ G ∈ Gs, V(G)
  IsLink e x y := ∃ G ∈ Gs, G.IsLink e x y
  isLink_symm e he x y := by simp [isLink_comm]
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' := by
    obtain ⟨G₁, hG₁s, hG₁e⟩ := h
    obtain ⟨G₂, hG₂s, hG₂e⟩ := h'
    rw [(set_pairwise_compatible_of_subgraph h).of_refl hG₁s hG₂s
      ⟨hG₁e.edge_mem, hG₂e.edge_mem⟩] at hG₁e
    exact G₂.eq_or_eq_of_isLink_of_isLink hG₁e hG₂e
  left_mem_of_isLink e x y h := by
    obtain ⟨G, hG, hGxy⟩ := h
    simp only [mem_iUnion, exists_prop]
    exact ⟨G, hG, hGxy.left_mem⟩
  edgeSet := ⋃ G ∈ Gs, E(G)
  edge_mem_iff_exists_isLink e := by
    simp only [mem_iUnion, edge_mem_iff_exists_isLink, exists_prop]
    tauto

lemma le_sUnion' (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) (hG : G ∈ Gs) : G ≤ sUnion' Gs H h := by
  simp only [le_iff, sUnion'_vertexSet, sUnion'_isLink]
  exact ⟨subset_biUnion_of_mem hG, fun e u v he ↦ by use G⟩

lemma sUnion'_le (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) (hH' : ∀ ⦃G⦄, G ∈ Gs → G ≤ H') :
    sUnion' Gs H h ≤ H' := by
  simp only [le_iff, sUnion'_vertexSet, iUnion_subset_iff, sUnion'_isLink, forall_exists_index,
    and_imp]
  exact ⟨fun G hG ↦ vertexSet_mono (hH' hG), fun e u v G hG hGuv ↦ hGuv.of_le (hH' hG)⟩

@[simp]
lemma sUnion'_le_iff (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) : sUnion' Gs H h ≤ H' ↔ ∀ G ∈ Gs, G ≤ H' :=
  ⟨fun h' _ hG => (le_sUnion' h hG).trans h', sUnion'_le h⟩

lemma sUnion'_eq_sUnion' (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) (h' : ∀ ⦃G⦄, G ∈ Gs → G ≤ H') :
    sUnion' Gs H h = sUnion' Gs H' h' :=
  (sUnion'_le h' fun _ ↦ le_sUnion' h').antisymm (sUnion'_le h fun _ ↦ le_sUnion' h')

@[simp]
lemma sUnion'_inc (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) :
    (sUnion' Gs H h).Inc e x ↔ ∃ G ∈ Gs, G.Inc e x := by
  simp only [Inc, sUnion'_isLink]
  tauto

@[simp]
lemma sUnion'_isLoopAt (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) :
    (sUnion' Gs H h).IsLoopAt e x ↔ ∃ G ∈ Gs, G.IsLoopAt e x := by
  simp only [IsLoopAt, sUnion'_isLink]

@[simp]
lemma sUnion'_isNonloopAt (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) :
    (sUnion' Gs H h).IsNonloopAt e x ↔ ∃ G ∈ Gs, G.IsNonloopAt e x := by
  simp only [IsNonloopAt, sUnion'_isLink]
  tauto

@[simp]
lemma sUnion'_singleton (G : Graph α β) (h : ∀ ⦃G_1⦄, G_1 ∈ ({G} : Set (Graph α β)) → G_1 ≤ H) :
    sUnion' {G} H h = G := by
  apply Graph.ext <;> simp

lemma sUnion'_mono (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) (h' : ∀ ⦃G⦄, G ∈ Gs' → G ≤ H') (hGs : Gs ⊆ Gs') :
    sUnion' Gs H h ≤ sUnion' Gs' H' h' := by
  rw [sUnion'_le_iff]
  exact fun G hG ↦ le_sUnion' h' (hGs hG)

end Agree

namespace WithTop

lemma eq_top_or_eq_some {α : Type*} (a' : WithTop α) : a' = ⊤ ∨ ∃ a : α, a' = WithTop.some a :=
  Option.eq_none_or_eq_some a'

noncomputable instance : CompleteLattice (WithTop <| Graph α β) where
  sInf s := by
    by_cases hs : ∃ G : Graph α β, WithTop.some G ∈ s
    · exact WithTop.some (Graph.sInter (WithTop.some ⁻¹' s) (by tauto))
    · exact ⊤
  sInf_le s G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · exact le_top
    have : ∃ G : Graph α β, WithTop.some G ∈ s := by use G
    simp only [this, ↓reduceDIte, ge_iff_le]
    exact WithTop.coe_le_coe.mpr <| Graph.sInter_le hG
  le_sInf s G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · suffices ∀ G : Graph α β, WithTop.some G ∉ s by simp [this]
      exact fun _ hHs => Option.some_ne_none _ <| top_le_iff.mp <| hG _ hHs
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <|
        (Graph.le_sInter_iff h).mpr fun _ hHs => WithTop.coe_le_coe.mp (hG _ hHs)
    · exact le_top
  sup G H := by
    classical
    exact G.bind (fun G ↦ H.bind (fun H ↦
      if h : ∃ G', ∀ ⦃H'⦄, H' ∈ ({G, H} : Set (Graph α β)) → H' ≤ G'
      then WithTop.some <| sUnion' ({G, H} : Set (Graph α β)) h.choose h.choose_spec else none))
  le_sup_left G H := by
    obtain rfl | ⟨G, rfl⟩ := Option.eq_none_or_eq_some G
    · simp
    obtain rfl | ⟨H, rfl⟩ := Option.eq_none_or_eq_some H
    · simp only [Option.bind_none, Option.bind_fun_none]
      exact le_top
    simp only [Option.bind_some]
    split_ifs with h
    · refine WithTop.coe_le_coe.mpr <| le_sUnion' _ (by simp)
    · exact le_top
  le_sup_right G H := by
    obtain rfl | ⟨G, rfl⟩ := Option.eq_none_or_eq_some G
    · exact le_top
    obtain rfl | ⟨H, rfl⟩ := Option.eq_none_or_eq_some H
    · simp
    simp only [Option.bind_some]
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <| le_sUnion' _ (by simp)
    · exact le_top
  sup_le G H K hGK hHK := by
    obtain rfl | ⟨G, rfl⟩ := Option.eq_none_or_eq_some G
    · simpa
    obtain rfl | ⟨H, rfl⟩ := Option.eq_none_or_eq_some H
    · simpa
    obtain rfl | ⟨K, rfl⟩ := Option.eq_none_or_eq_some K
    · exact le_top
    have hle : ∀ ⦃G'⦄, G' ∈ ({G, H} : Set (Graph α β)) → G' ≤ K := by
      rintro G' hG'
      obtain (rfl | rfl) := hG' <;> rwa [← WithTop.coe_le_coe]
    have h : ∃ G', ∀ ⦃H' : Graph α β⦄, H' ∈ ({G, H} : Set (Graph α β)) → H' ≤ G' := ⟨K, hle⟩
    simp only [Option.bind_some, h]
    simp only [↓reduceDIte, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact WithTop.coe_le_coe.mpr <| sUnion'_le hle hle
  sSup Gs := by
    classical
    exact if h : ⊤ ∉ Gs ∧ ∃ G', ∀ ⦃H'⦄, H' ∈ WithTop.some ⁻¹' Gs → H' ≤ G'
      then WithTop.some (sUnion' (WithTop.some ⁻¹' Gs) h.2.choose h.2.choose_spec) else ⊤
  le_sSup Gs G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · simp +contextual [hG]
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <| le_sUnion' _ (by simpa)
    · exact le_top
  sSup_le Gs G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · simp
    have hG' : ∀ H ∈ WithTop.some ⁻¹' Gs, H ≤ G := fun _ hH => WithTop.coe_le_coe.mp (hG _ hH)
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <| sUnion'_le hG' hG'
    · rw [and_comm, not_and, not_not] at h
      specialize h ⟨G, hG'⟩
      simpa using hG ⊤ h

instance : Nontrivial (WithTop <| Graph α β) where
  exists_pair_ne := ⟨⊥, ⊤, WithTop.coe_ne_top⟩

end WithTop

lemma Agree.sup_some_eq_top_iff : WithTop.some G ⊔ WithTop.some H = ⊤ ↔ ¬ Agree {G, H} := by
  classical
  change (if h : _ then _ else ⊤) = (⊤ : WithTop <| Graph α β) ↔ _
  refine ⟨fun h => ?_, fun h => by simp_all [Agree]⟩
  split_ifs at h with h'
  · simp at h
  contrapose! h'
  simp_all [Agree]

lemma Agree.biSup_some_eq_top_iff : (⨆ G ∈ Gs, WithTop.some G) = ⊤ ↔ ¬ Agree Gs := by
  classical
  rw [← sSup_image]
  change (if h : _ then _ else ⊤) = (⊤ : WithTop <| Graph α β) ↔ _
  refine ⟨fun h => ?_, fun h => by simp_all [Agree]⟩
  split_ifs at h with h'
  · simp at h
  contrapose! h'
  exact ⟨by simp, by simpa⟩

lemma Agree.iSup_some_eq_top_iff : (⨆ i, WithTop.some (Gι i)) = ⊤ ↔ ¬ Agree (range Gι) := by
  classical
  rw [← sSup_range]
  change (if h : _ then _ else ⊤) = (⊤ : WithTop <| Graph α β) ↔ _
  refine ⟨fun h => ?_, fun h => by simp_all [Agree]⟩
  split_ifs at h with h'
  · simp at h
  contrapose! h'
  exact ⟨by simp, by simp_all [Agree]⟩

lemma Agree.biSup_some_ne_top_iff : (⨆ G ∈ Gs, WithTop.some G) ≠ ⊤ ↔ Agree Gs := by
  convert Agree.biSup_some_eq_top_iff.not
  rw [not_not]

lemma Agree.sup_some_eq (hs : Agree {G, H}) :
    WithTop.some G ⊔ WithTop.some H = WithTop.some (sUnion' {G, H} hs.choose hs.choose_spec) := by
  classical
  change (if h : _ then _ else ⊤) = WithTop.some (sUnion' {G, H} hs.choose hs.choose_spec)
  split_ifs with h
  · simp
  absurd h
  simp_all [Agree]

lemma Agree.iSup_some_eq (hs' : Agree (range Gι)) : (⨆ i, WithTop.some (Gι i)) =
    WithTop.some (sUnion' (Set.range Gι) hs'.choose hs'.choose_spec) := by
  classical
  change (if h : _ then _ else ⊤) = WithTop.some (sUnion' (Set.range Gι) hs'.choose hs'.choose_spec)
  have h : ∃ G', ∀ (a : ι), Gι a ≤ G' := by simpa [Agree] using hs'
  have h' : (WithTop.some ⁻¹' range fun i ↦ ↑(Gι i)) = range Gι := by
    ext G
    simp
  simp [h, h']

lemma Agree.biSup_some_eq (hs : Agree Gs) :
    (⨆ G ∈ Gs, WithTop.some G) = WithTop.some (sUnion' Gs hs.choose hs.choose_spec) := by
  classical
  rw [← sSup_image]
  change (if h : _ then _ else ⊤) = WithTop.some (sUnion' Gs hs.choose hs.choose_spec)
  have hpi : WithTop.some ⁻¹' (WithTop.some '' Gs) = Gs := by
    ext G
    simp
  split_ifs with h
  · simp [hpi]
  absurd h
  simpa

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
lemma iUnion_inc_iff (hs' : Agree (range Gι)) :(Graph.iUnion Gι).Inc e x ↔ ∃ i, (Gι i).Inc e x := by
  simp [hs']

@[simp]
lemma iUnion_isLoopAt_iff (hs' : Agree (range Gι)) :
    (Graph.iUnion Gι).IsLoopAt e x ↔ ∃ i, (Gι i).IsLoopAt e x := by
  simp [← isLink_self_iff, hs']

@[simp]
lemma iUnion_isNonloopAt_iff (hs' : Agree (range Gι)) :
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
