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

@[simp]
lemma IsLink.isLink_of_agree_of_edge_mem (h : G.IsLink e x y) (hs : Agree Gs) (hG : G ∈ Gs)
    (hH : H ∈ Gs) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨G', hG'⟩ := hs
  exact (h.of_le <| hG' G hG).of_le_of_mem (hG' H hH) he

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
