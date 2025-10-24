import Matroid.Graph.Subgraph.Lemma

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {F F₁ F₂ : Set β} {X Y : Set α}
  [CompleteLattice α] {G G₁ G₂ G' H H₁ H₂ H' : Graph α β} {Gs Hs : Set (Graph α β)}
  {Gι Hι : ι → Graph α β}

open Set Function

open scoped Sym2

namespace Graph

section Lattice

@[reducible] def Subgraph (G : Graph α β) := {H // H ≤ G}

namespace Subgraph

instance {G : Graph α β} : CoeOut G.Subgraph (Graph α β) where
  coe H := H.1

@[simp]
lemma le (H : G.Subgraph) : H.1 ≤ G :=
  H.2

instance : PartialOrder G.Subgraph := inferInstanceAs (PartialOrder {H // H ≤ G})

@[simp]
lemma mk_le_iff {hH₁ : H₁ ≤ G} {H : G.Subgraph} : (⟨H₁, hH₁⟩ : G.Subgraph) ≤ H ↔ H₁ ≤ H.1 := Iff.rfl

@[simp]
lemma le_mk_iff {hH₁ : H₁ ≤ G} {H : G.Subgraph} : H ≤ (⟨H₁, hH₁⟩ : G.Subgraph) ↔ H.1 ≤ H₁ := Iff.rfl

@[simp]
lemma compatible (H₁ H₂ : G.Subgraph) : H₁.val.Compatible H₂.val :=
  compatible_of_le_le H₁.prop H₂.prop

@[simp]
lemma pairwise_compatible (H : ι → G.Subgraph) :
    Pairwise (Compatible on (fun i ↦ (H i : Graph α β))) :=
  G.pairwise_compatible_of_subgraph (fun i ↦ (H i).2)

@[simp]
lemma set_pairwise_compatible (s : Set G.Subgraph) :
    ((Subtype.val '' s).Pairwise Compatible) :=
  G.set_pairwise_compatible_of_subgraph (by rintro _ ⟨H, -, rfl⟩; exact H.2)

@[simp]
lemma dup_agree (H₁ H₂ : G.Subgraph) : H₁.val.Dup_agree H₂.val :=
  dup_agree_of_le_le H₁.prop H₂.prop

@[simp]
lemma pairwise_dup_agree (H : ι → G.Subgraph) :
    Pairwise (Dup_agree on (fun i ↦ (H i : Graph α β))) :=
  G.pairwise_dup_agree_of_subgraph (fun i ↦ (H i).2)

@[simp]
lemma set_pairwise_dup_agree (s : Set G.Subgraph) :
    ((Subtype.val '' s).Pairwise Dup_agree) :=
  G.set_pairwise_dup_agree_of_subgraph (by rintro _ ⟨H, -, rfl⟩; exact H.2)

instance : SemilatticeInf G.Subgraph where
  inf H₁ H₂ := ⟨H₁ ∩ H₂, Graph.inter_le_left.trans H₁.2⟩
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter

instance : OrderBot G.Subgraph where
  bot := ⟨⊥, by simp⟩
  bot_le := by simp

instance : OrderTop G.Subgraph where
  top := ⟨G, le_rfl⟩
  le_top H := H.2

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

lemma sUnion'_le (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) (hH' : ∀ ⦃G⦄, G ∈ Gs → G ≤ H') :
    sUnion' Gs H h ≤ H' := by
  simp only [le_iff, sUnion'_vertexSet, iUnion_subset_iff, sUnion'_isLink, forall_exists_index,
    and_imp]
  exact ⟨fun G hG ↦ vertexSet_mono (hH' hG), fun e u v G hG hGuv ↦ hGuv.of_le (hH' hG)⟩

lemma le_sUnion' (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) (hG : G ∈ Gs) : G ≤ sUnion' Gs H h := by
  simp only [le_iff, sUnion'_vertexSet, sUnion'_isLink]
  exact ⟨subset_biUnion_of_mem hG, fun e u v he ↦ by use G⟩

/-- Under the `Order.Frame α` instance, `sUnion'` is equal to `Graph.sUnion`. -/
lemma sUnion_eq_sUnion' {α : Type*} [Order.Frame α] {Gs : Set (Graph α β)} {H : Graph α β}
    (h : ∀ ⦃G⦄, G ∈ Gs → G ≤ H) : Graph.sUnion Gs = sUnion' Gs H h :=
  le_antisymm (Graph.sUnion_le_of_forall_le fun _ ↦ le_sUnion' h)
  <| sUnion'_le h fun _ ↦ Graph.le_sUnion (compatible_of_forall_mem_le h)
  <| dup_agree_of_forall_mem_le h

instance : Lattice G.Subgraph where
  sup H₁ H₂ := ⟨sUnion' {H₁.val, H₂.val} G (by simp), sUnion'_le (by simp) (by simp)⟩
  le_sup_left H₁ H₂ := by
    rw [Subgraph.le_mk_iff]
    generalize_proofs hG
    exact le_sUnion' hG (by simp)
  le_sup_right H₁ H₂ := by
    rw [Subgraph.le_mk_iff]
    generalize_proofs hG
    exact le_sUnion' hG (by simp)
  sup_le H₁ H₂ K hHK hHK' := by
    rw [Subgraph.le_mk_iff]
    generalize_proofs hG hG'
    exact sUnion'_le hG (by simp [hHK, hHK'])

instance : CompleteLattice G.Subgraph where
  sSup Gs := ⟨sUnion' (Subtype.val '' Gs) G (by
    rintro _ ⟨G', hG', rfl⟩
    exact G'.prop), sUnion'_le _ (by
    rintro _ ⟨G', hG', rfl⟩
    exact G'.prop)⟩
  le_sSup Gs H hHs := by
    rw [Subgraph.le_mk_iff]
    generalize_proofs hG
    exact le_sUnion' hG (by simp [hHs])
  sSup_le Gs H h := by
    rw [Subgraph.le_mk_iff]
    generalize_proofs hG
    apply sUnion'_le hG
    rintro _ ⟨G', hG', rfl⟩
    exact h G' hG'
  sInf s := ⟨Graph.sInter (insert G (((↑) : G.Subgraph → Graph α β) '' s)) (by simp),
    Graph.sInter_le (by simp)⟩
  sInf_le s H h := Graph.sInter_le <| by simp [h]
  le_sInf s H h := by simpa using fun K h' hK ↦ h _ hK

@[simp]
lemma coe_top : ((⊤ : G.Subgraph) : Graph α β) = G := rfl

@[simp]
lemma coe_bot : ((⊥ : G.Subgraph) : Graph α β) = ⊥ := rfl

lemma coe_iInf (H : ι → G.Subgraph) :
    (⨅ i, H i : G.Subgraph) = Graph.iInter (Option.elim · G (H ·)) := by
  change Graph.sInter _ (by simp) = _
  rw [← range_comp', iInter_option_eq_sInter_insert]

@[simp]
lemma iInf_of_isEmpty [IsEmpty ι] (H : ι → G.Subgraph) : (⨅ i, H i : G.Subgraph) = G := by
  simp [_root_.iInf_of_isEmpty ..]

@[simp]
lemma coe_iInf_of_nonempty [Nonempty ι] (H : ι → G.Subgraph) :
    (⨅ i, H i : G.Subgraph) = Graph.iInter (fun i ↦ (H i : Graph α β)) := by
  simp only [le_antisymm_iff, le_iInter_iff, Subtype.coe_le_coe, iInf_le, implies_true, true_and]
  refine (Graph.le_sInter_iff (by simp)).2 ?_
  simp only [mem_insert_iff, mem_image, mem_range, exists_exists_eq_and, forall_eq_or_imp,
    forall_exists_index, forall_apply_eq_imp_iff]
  exact ⟨(Graph.iInter_le (Classical.arbitrary ι)).trans (by simp), fun i ↦ Graph.iInter_le i⟩

lemma coe_sInf (s : Set G.Subgraph) :
    ((sInf s : G.Subgraph) : Graph α β) = Graph.sInter (insert G <| (↑) '' s) (by simp) := rfl

lemma coe_sInf_of_nonempty (s : Set G.Subgraph) (hs : s.Nonempty) :
    ((sInf s : G.Subgraph) : Graph α β) = Graph.sInter ((↑) '' s) (by simpa) := by
  change Graph.sInter _ (by simp) = _
  rw [le_antisymm_iff]
  simp only [Graph.le_sInter_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    forall_exists_index, mem_insert_iff, forall_eq_or_imp]
  obtain ⟨⟨K, hKG⟩, hK⟩ := hs
  exact ⟨fun H hHG hHs ↦ Graph.sInter_le (by simp [hHG, hHs]),
    (Graph.sInter_le (by simp [hKG, hK])).trans hKG,
    fun H hHG hHs ↦ Graph.sInter_le (by simp [hHs, hHG])⟩

lemma coe_sInf_of_empty : ((sInf ∅ : G.Subgraph) : Graph α β) = G := by simp

@[simp]
lemma coe_iSup (H : ι → G.Subgraph) :
    (⨆ i, H i : G.Subgraph) = sUnion' (range <| Subtype.val ∘ H) G (by simp) := by
  change (⟨sUnion' _ _ _, _⟩ : G.Subgraph).val = _
  simp_rw [range_comp]

@[simp]
lemma coe_sSup (s : Set G.Subgraph) : ((sSup s : G.Subgraph) : Graph α β) =
    sUnion' (Subtype.val '' s) G (by rintro _ ⟨G', _, rfl⟩; exact G'.prop) := rfl

@[simp↓]
lemma coe_biSup (s : Set ι) (H : ι → G.Subgraph) :
    (⨆ i ∈ s, H i : G.Subgraph) = sUnion' (Subtype.val ∘ H '' s) G (by simp) := by
  simp_rw [← sSup_image, coe_sSup, image_comp]

@[simp]
lemma coe_sup (H₁ H₂ : G.Subgraph) : ((H₁ ⊔ H₂ : G.Subgraph) : Graph α β) =
    sUnion' {H₁.val, H₂.val} G (by simp) := rfl

lemma coe_sup_eq_union {α : Type*} [Order.Frame α] {G : Graph α β} (H₁ H₂ : G.Subgraph) :
    ((H₁ ⊔ H₂ : G.Subgraph) : Graph α β) = H₁.1 ∪ H₂.1 := by
  rw [coe_sup, ← sUnion_eq_sUnion', (compatible H₁ H₂).union_eq_sUnion (dup_agree H₁ H₂)]

@[simp]
lemma coe_inf (H₁ H₂ : G.Subgraph) : ((H₁ ⊓ H₂ : G.Subgraph) : Graph α β) = H₁.1 ∩ H₂.1 :=
  rfl

@[simp]
lemma range_iSup (f : ι' → ι) (H : ι → G.Subgraph) :
    (⨆ (i : Set.range f), H i : G.Subgraph) = ⨆ i, H (f i) := by
  apply_fun Subtype.val using Subtype.val_injective
  simp only [coe_iSup]
  congr
  ext G
  simp

@[simp]
lemma range_iInf (f : ι' → ι) (H : ι → G.Subgraph) :
    (⨅ (i : Set.range f), H i : G.Subgraph) = ⨅ i, H (f i) := by
  apply_fun Subtype.val using Subtype.val_injective
  obtain hι | hι := isEmpty_or_nonempty ι'
  · have : IsEmpty ↑(range f) := by simpa
    simp
  · simp [Graph.iInter_range]

lemma disjoint_iff (H₁ H₂ : G.Subgraph) : Disjoint H₁ H₂ ↔ H₁.val.StronglyDisjoint H₂.val := by
  rw [_root_.disjoint_iff, ← Subtype.coe_inj, coe_inf, coe_bot, ← disjoint_iff_inter_eq_bot,
    stronglyDisjoint_iff_disjoint_of_compatible (H₁.compatible H₂)]

def of_le {H : Graph α β} (H' : H.Subgraph) (hle : H ≤ G) : G.Subgraph :=
  ⟨H', H'.le.trans hle⟩

@[simp]
lemma coe_of_le {H : Graph α β} (H' : H.Subgraph) (hle : H ≤ G) :
    (H'.of_le hle : Graph α β) = H' := rfl

/-- The proof that the subgraphs of a graph `G` form a completely distributive lattice. -/
def minAx : CompletelyDistribLattice.MinimalAxioms G.Subgraph where
  iInf_iSup_eq {ι κ} f := by
    rw [Subtype.ext_iff]
    obtain (hι | hι) := isEmpty_or_nonempty ι
    · rw [iInf_of_isEmpty]
      simp
    ext a b c <;> simp only [iInter_vertexSet, sUnion'_vertexSet, mem_range, comp_apply,
      iUnion_exists, iUnion_iUnion_eq', mem_iInter, mem_iUnion, coe_iInf_of_nonempty, iInter_isLink,
      sUnion'_isLink, mem_range, comp_apply, exists_exists_eq_and, coe_iInf_of_nonempty, coe_iSup,
      coe_iInf_of_nonempty] <;> exact ⟨fun h => ⟨fun i ↦ (h i).choose, fun i ↦ (h i).choose_spec⟩,
        fun h i => ⟨h.choose i, h.choose_spec i⟩⟩

/-- The subgraphs of a graph `G` form a completely distributive lattice.-/
instance : CompletelyDistribLattice G.Subgraph :=
  CompletelyDistribLattice.ofMinimalAxioms Subgraph.minAx

end Subgraph

@[reducible] def ClosedSubgraph (G : Graph α β) := {H // H ≤c G}

namespace ClosedSubgraph
variable {G : Graph α β} {H H₁ H₂ : G.ClosedSubgraph} {s : Set G.ClosedSubgraph}

instance : PartialOrder G.ClosedSubgraph := inferInstanceAs (PartialOrder {H // H ≤c G})

/-- The order embedding from closed subgraphs to subgraphs -/
def toSubgraph : G.ClosedSubgraph ↪o G.Subgraph :=
  Subtype.orderEmbedding fun _ ↦ IsClosedSubgraph.le

@[simp]
lemma toSubgraph_val_eq_val : (·.toSubgraph.val : G.ClosedSubgraph → _) = (↑) := rfl

@[simp]
lemma coe_toSubgraph (H : G.ClosedSubgraph) : (H.toSubgraph : Graph α β) = H := rfl

@[simp]
lemma coe_comp_toSubgraph : (Subtype.val ∘ toSubgraph : G.ClosedSubgraph → _) = (↑) := rfl

instance {G : Graph α β} : CoeOut G.ClosedSubgraph (Graph α β) where
  coe H := H.1

@[simp]
lemma mk_le_iff {H₁ : Graph α β} {hH₁ : H₁ ≤c G} {H : G.ClosedSubgraph} :
    (⟨H₁, hH₁⟩ : G.ClosedSubgraph) ≤ H ↔ H₁ ≤ H.1 := Iff.rfl

@[simp]
lemma le_mk_iff {H₁ : Graph α β} {hH₁ : H₁ ≤c G} {H : G.ClosedSubgraph} :
    H ≤ (⟨H₁, hH₁⟩ : G.ClosedSubgraph) ↔ H.1 ≤ H₁ := Iff.rfl

instance : Lattice G.ClosedSubgraph where
  sup H₁ H₂ := ⟨(H₁.toSubgraph ⊔ H₂.toSubgraph).val, (H₁.toSubgraph ⊔ H₂.toSubgraph).prop, by
    simp only [Subgraph.coe_sup, Subgraph.sUnion'_vertexSet, mem_insert_iff, mem_singleton_iff,
      iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left, mem_union, Subgraph.sUnion'_edgeSet]
    exact fun e v he hv ↦ hv.imp (H₁.prop.closed he) (H₂.prop.closed he)⟩
  le_sup_left H₁ H₂ := by
    rw [le_mk_iff, ← toSubgraph_val_eq_val, Subtype.coe_le_coe]
    exact le_sup_left
  le_sup_right H H' := by
    rw [le_mk_iff, ← toSubgraph_val_eq_val, Subtype.coe_le_coe]
    exact le_sup_right
  sup_le a b c hac hbc := by
    rw [mk_le_iff (H := c), ← toSubgraph_val_eq_val, Subtype.coe_le_coe]
    exact sup_le hac hbc
  inf H₁ H₂ := ⟨H₁ ∩ H₂, H₁.2.inter H₂.2⟩
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter

instance : OrderBot G.ClosedSubgraph where
  bot := ⟨⊥, by simp⟩
  bot_le := by simp

instance : OrderTop G.ClosedSubgraph where
  top := ⟨G, isClosedSubgraph_self⟩
  le_top H := H.2.le

@[simp]
lemma coe_top : ((⊤ : G.ClosedSubgraph) : Graph α β) = G := rfl

@[simp]
lemma coe_bot : ((⊥ : G.ClosedSubgraph) : Graph α β) = ⊥ := rfl

@[simp]
lemma eq_bot_iff (H : G.ClosedSubgraph) : H = ⊥ ↔ H.val = ⊥ := by
  simp only [Subtype.ext_iff, coe_bot]

instance : CompleteLattice G.ClosedSubgraph where
  sSup s := ⟨(⨆ H ∈ s, H.toSubgraph).val, (⨆ H ∈ s, H.toSubgraph).prop, by
    simp only [Subgraph.coe_biSup, comp_apply, Subgraph.sUnion'_vertexSet, mem_image,
      Subtype.exists, iUnion_exists, mem_iUnion, exists_prop, exists_and_right, ↓existsAndEq,
      and_true, Subgraph.sUnion'_edgeSet, forall_exists_index, and_imp]
    intro e u v H hHc hs hu
    use H, hHc, hs, (hHc.edge_mem_iff_vertex_mem_of_inc v).mpr hu⟩
  le_sSup s H hHs := by
    simp only [↓Subgraph.coe_biSup, comp_apply, le_mk_iff]
    apply Subgraph.le_sUnion'
    rw [toSubgraph_val_eq_val]
    use H
  sSup_le s H hHs := by
    simp only [↓Subgraph.coe_biSup, comp_apply, toSubgraph_val_eq_val, mk_le_iff]
    apply Subgraph.sUnion'_le
    rintro A ⟨a, has, rfl⟩
    exact hHs a has
  sInf s := ⟨((⨅ (H : s), ClosedSubgraph.toSubgraph H.1 : G.Subgraph) : Graph α β), by
    obtain hs | hs := isEmpty_or_nonempty s; simp
    simp only [Subgraph.coe_iInf_of_nonempty, ClosedSubgraph.coe_toSubgraph]
    exact iInter_isClosedSubgraph (by simp +contextual)⟩
  sInf_le s H hHs := by
    have hne : Nonempty s := ⟨H, hHs⟩
    simp only [Subgraph.coe_iInf_of_nonempty, ClosedSubgraph.coe_toSubgraph]
    exact Graph.iInter_le (G := fun i : s ↦ (i.1.toSubgraph : Graph α β)) ⟨H, hHs⟩
  le_sInf s := by
    obtain rfl | hne := s.eq_empty_or_nonempty
    · simp +contextual [IsClosedSubgraph.le]
    simp [hne.to_subtype]

lemma coe_le_coe {H₀ H : G.ClosedSubgraph} : H₀.1 ≤ H.1 ↔ H₀ ≤ H := Iff.rfl

lemma coe_lt_coe {H₀ H : G.ClosedSubgraph} : H₀.1 < H.1 ↔ H₀ < H := Iff.rfl

lemma toSubgraph_le_toSubgraph {H₁ H₂ : G.ClosedSubgraph} :
    H₁.toSubgraph ≤ H₂.toSubgraph ↔ H₁ ≤ H₂ := Iff.rfl

lemma toSubgraph_lt_toSubgraph {H₁ H₂ : G.ClosedSubgraph} :
    H₁.toSubgraph < H₂.toSubgraph ↔ H₁ < H₂ := Iff.rfl

@[simp]
lemma coe_sup (H₁ H₂ : G.ClosedSubgraph) : (H₁ ⊔ H₂ : G.ClosedSubgraph).val =
    Subgraph.sUnion' {H₁.1, H₂.1} G (by simp [H₁.2.le, H₂.2.le]) := rfl

@[simp]
lemma coe_inf (H₁ H₂ : G.ClosedSubgraph) : (H₁ ⊓ H₂ : G.ClosedSubgraph).val = H₁.1 ∩ H₂.1 :=
  rfl

@[simp]
lemma compatible (H₁ H₂ : G.ClosedSubgraph) : H₁.val.Compatible H₂.val :=
  compatible_of_le_le H₁.2.le H₂.2.le

@[simp]
lemma pairwise_compatible (H : ι → G.ClosedSubgraph) :
    Pairwise (Compatible on (fun i ↦ (H i : Graph α β))) :=
  G.pairwise_compatible_of_subgraph (fun i ↦ (H i).2.le)

@[simp]
lemma set_pairwise_compatible (s : Set G.ClosedSubgraph) :
    ((((↑) : _ → Graph α β) '' s).Pairwise Compatible) :=
  G.set_pairwise_compatible_of_subgraph (by rintro _ ⟨H, -, rfl⟩; exact H.2.le)

@[simp]
lemma dup_agree (H₁ H₂ : G.ClosedSubgraph) : H₁.val.Dup_agree H₂.val :=
  dup_agree_of_le_le H₁.2.le H₂.2.le

@[simp]
lemma pairwise_dup_agree (H : ι → G.ClosedSubgraph) :
    Pairwise (Dup_agree on (fun i ↦ (H i : Graph α β))) :=
  G.pairwise_dup_agree_of_subgraph (fun i ↦ (H i).2.le)

@[simp]
lemma set_pairwise_dup_agree (s : Set G.ClosedSubgraph) :
    ((((↑) : _ → Graph α β) '' s).Pairwise Dup_agree) :=
  G.set_pairwise_dup_agree_of_subgraph (by rintro _ ⟨H, -, rfl⟩; exact H.2.le)

@[simp]
lemma sup_vertexSet (H₁ H₂ : G.ClosedSubgraph) : V((H₁ ⊔ H₂).val) = V(H₁.val) ∪ V(H₂.val) := by
  simp

@[simp]
lemma sup_edgeSet (H₁ H₂ : G.ClosedSubgraph) : E((H₁ ⊔ H₂).val) = E(H₁.val) ∪ E(H₂.val) := by
  simp

@[simp]
lemma sup_isLink (H₁ H₂ : G.ClosedSubgraph) :
    (H₁ ⊔ H₂).val.IsLink e = H₁.val.IsLink e ⊔ H₂.val.IsLink e := by
  ext u v
  simp

@[simp]
lemma inf_vertexSet (H₁ H₂ : G.ClosedSubgraph) : V((H₁ ⊓ H₂).val) = V(H₁.val) ∩ V(H₂.val) := by
  simp

@[simp]
lemma inf_edgeSet (H₁ H₂ : G.ClosedSubgraph) : E((H₁ ⊓ H₂).val) = E(H₁.val) ∩ E(H₂.val) := by
  simp

@[simps]
def compl' (H : G.ClosedSubgraph) : Graph α β where
  vertexPartition := P(G).delete P(H.val).parts
  vertexSet := V(G) \ V(H.val)
  vertexSet_eq_parts := by simp
  IsLink e x y := G.IsLink e x y ∧ e ∉ E(H.val)
  isLink_symm e he x y h := by simp_all [IsLink.symm]
  edgeSet := E(G) \ E(H.val)
  edge_mem_iff_exists_isLink e := by simp [edge_mem_iff_exists_isLink]
  eq_or_eq_of_isLink_of_isLink e x y z w := by
    rintro ⟨he, hne⟩ ⟨he', -⟩
    exact G.eq_or_eq_of_isLink_of_isLink he he'
  left_mem_of_isLink e x y := by
    rintro ⟨he, hne⟩
    simp only [mem_diff, he.left_mem, true_and]
    contrapose! hne
    exact H.prop.closed ⟨y, he⟩ hne

lemma compl'_isClosedSubgraph (H : G.ClosedSubgraph) : H.compl' ≤c G where
  vertexSet_subset := by simp [diff_subset]
  isLink_of_isLink e u v h := h.1
  closed e u he := by
    rintro ⟨huG, huH⟩
    simp_all [he.edge_mem, H.prop.edge_mem_iff_vertex_mem_of_inc he]

instance : CompleteBooleanAlgebra G.ClosedSubgraph where
  le_sup_inf H₁ H₂ H₃ := by
    refine ClosedSubgraph.coe_le_coe.mp ⟨by simp [← union_inter_distrib_left], fun e x y ↦ ?_⟩
    simp only [coe_inf, coe_sup, inter_isLink, Pi.inf_apply, Subgraph.sUnion'_isLink,
      mem_insert_iff, mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq, true_and, inf_Prop_eq,
      and_imp]
    tauto
  compl H := ⟨H.compl', H.compl'_isClosedSubgraph⟩
  sdiff H₁ H₂ := _
  himp H₁ H₂ := _
  inf_compl_le_bot := by simp [← vertexSet_eq_empty_iff]
  top_le_sup_compl := by
    refine fun H ↦ ⟨?_, fun e x y he ↦ ?_⟩
    · rw [ClosedSubgraph.sup_vertexSet, ClosedSubgraph.compl'_vertexSet]
      simp
    rw [ClosedSubgraph.sup_isLink]
    simp only [Pi.sup_apply, ClosedSubgraph.compl'_isLink, sup_Prop_eq] at he ⊢
    by_cases heH : e ∈ E(H.val)
    · exact .inl <| he.of_le_of_mem H.prop.le heH
    tauto
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

@[simp]
lemma toSubgraph_sSup (s : Set G.ClosedSubgraph) :
    toSubgraph (sSup s) = ⨆ (H : s), toSubgraph H.1 := rfl

@[simp]
lemma coe_sSup (s : Set G.ClosedSubgraph) :
    ((sSup s : G.ClosedSubgraph) : Graph α β) = Graph.sUnion (Subtype.val '' s) := by
  change Graph.sUnion _ = _
  congr 1
  simp_rw [← range_comp', coe_toSubgraph]
  exact (image_eq_range Subtype.val s).symm

@[simp]
lemma toSubgraph_iSup (f : ι → G.ClosedSubgraph) :
    toSubgraph (⨆ i, f i) = ⨆ i, toSubgraph (f i) :=
  Subgraph.range_iSup (fun i ↦ f i) ⇑toSubgraph

-- @[simp]
-- lemma coe_iSup (f : ι → G.ClosedSubgraph)
--     (hf : Pairwise (Compatible on fun i ↦ (f i : Graph α β))) :
--     (⨆ i, f i : G.ClosedSubgraph) = Graph.iUnion (fun i ↦ (f i : Graph α β)) := by
--   simp only [iSup, coe_sSup, ← range_comp']
--   rw [Graph.sUnion_range]

@[simp]
lemma vertexSet_sSup (s : Set G.ClosedSubgraph) :
    V((sSup s).val) = ⋃ a ∈ s, V(a.val) := by
  rw [coe_sSup, sUnion_vertexSet (ClosedSubgraph.set_pairwise_dup_agree s), biUnion_image]

@[simp]
lemma edgeSet_sSup (s : Set G.ClosedSubgraph) :
    E((sSup s).val) = ⋃ a ∈ s, E(a.val) := by
  rw [coe_sSup, sUnion_edgeSet (ClosedSubgraph.set_pairwise_compatible s), biUnion_image]

@[simp]
lemma toSubgraph_iInf (f : ι → G.ClosedSubgraph) :
    toSubgraph (⨅ i, f i) = ⨅ i, toSubgraph (f i) :=
  Subgraph.range_iInf (fun i ↦ f i) ⇑toSubgraph

@[simp]
lemma coe_iInf_of_nonempty [Nonempty ι] (f : ι → G.ClosedSubgraph) :
    (⨅ i, f i : G.ClosedSubgraph) = Graph.iInter (fun i ↦ (f i : Graph α β)) := by
  simp only [le_antisymm_iff, le_iInter_iff, Subtype.coe_le_coe, iInf_le, implies_true, true_and]
  refine (Graph.le_sInter_iff (by simp)).2 ?_
  simp only [mem_insert_iff, mem_image, mem_range, exists_exists_eq_and, forall_eq_or_imp,
    forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨(Graph.iInter_le (Classical.arbitrary ι)).trans ((f _).prop.le), fun i ↦ ?_⟩
  obtain ⟨_, i, rfl⟩ := i
  exact Graph.iInter_le i

@[simp]
lemma coe_iInf_of_empty [IsEmpty ι] (f : ι → G.ClosedSubgraph) :
    ((⨅ i, f i : G.ClosedSubgraph) : Graph α β) = G := by
  simp [_root_.iInf_of_isEmpty ..]

@[simp]
lemma toSubgraph_sInf (s : Set G.ClosedSubgraph) :
    toSubgraph (sInf s) = sInf (toSubgraph '' s) := by
  change iInf _ = _
  rw [sInf_image]
  exact iInf_subtype'' s ⇑toSubgraph

@[simp]
lemma coe_sInf (s : Set G.ClosedSubgraph) :
    ((sInf s : G.ClosedSubgraph) : Graph α β) =
    Graph.sInter (insert G (Subtype.val '' s)) (by simp) := by
  change Graph.sInter _ (by simp) = _
  congr 2
  simp_rw [← range_comp', coe_toSubgraph]
  exact (image_eq_range Subtype.val s).symm

@[simp]
lemma coe_sInf_of_nonempty (hs : s.Nonempty):
    ((sInf s : G.ClosedSubgraph) : Graph α β) = Graph.sInter (Subtype.val '' s) (by simpa) := by
  rw [← coe_toSubgraph, toSubgraph_sInf, Subgraph.coe_sInf_of_nonempty _ (by simpa)]
  congr 1
  rw [← image_comp, coe_comp_toSubgraph]

@[simp]
lemma coe_sInf_of_empty : ((sInf ∅ : G.ClosedSubgraph) : Graph α β) = G := by simp

lemma vertexSet_sInf_comm (s : Set G.ClosedSubgraph) :
    V((sInf s).val) = V(G) ∩ ⋂ a ∈ s, V(a.val) := by
  simp only [coe_sInf, sInter_vertexSet, mem_insert_iff, iInter_iInter_eq_or_left, biInter_image]

@[simp]
lemma vertexSet_sInf_comm_of_nonempty (hs : s.Nonempty) :
    V((sInf s).val) = ⋂ a ∈ s, V(a.val) := by
  simp only [coe_sInf_of_nonempty hs, sInter_vertexSet, biInter_image]

instance : CompleteAtomicBooleanAlgebra G.ClosedSubgraph where
  iInf_iSup_eq {ι κ} f := by
    apply_fun ClosedSubgraph.toSubgraph using ClosedSubgraph.toSubgraph.injective
    simp only [ClosedSubgraph.toSubgraph_iInf, ClosedSubgraph.toSubgraph_iSup]
    exact CompletelyDistribLattice.iInf_iSup_eq (fun a b ↦ ClosedSubgraph.toSubgraph (f a b))

@[simp]
lemma coe_eq_induce (H : G.ClosedSubgraph) :
    G[P(H.val)] = H.val := vertexPartition_ext rfl fun e x y =>
  ⟨fun ⟨hl, hx, hy⟩ => by rwa [H.prop.isLink_iff_of_mem (H.val.vertexSet_eq_parts ▸ hx)],
  fun h => ⟨h.of_le H.prop.le, H.val.vertexSet_eq_parts ▸ h.left_mem,
    H.val.vertexSet_eq_parts ▸ h.right_mem⟩⟩

lemma IsClosedSubgraph.eq_induce {H₁ : Graph α β} (hcl : H₁ ≤c G) : H₁ = G[P(H₁)] := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl⟩
  change H₁' = G[P(H₁'.val)]
  exact H₁'.coe_eq_induce.symm

lemma ext_vertexSet (h : V(H₁.val) = V(H₂.val)) : H₁ = H₂ := by
  rw [← Subtype.coe_inj, ← H₁.coe_eq_induce, ← H₂.coe_eq_induce, vertexPartition_eq_iff.mpr h]

lemma vertexSet_inj : H₁ = H₂ ↔ V(H₁.val) = V(H₂.val) :=
  ⟨(· ▸ rfl), ClosedSubgraph.ext_vertexSet⟩

lemma IsClosedSubgraph.vertexSet_inj {H₁ H₂ : Graph α β} (hcl₁ : H₁ ≤c G) (hcl₂ : H₂ ≤c G) :
    H₁ = H₂ ↔ V(H₁) = V(H₂) := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl₁⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hcl₂⟩
  change H₁' = H₂'.val ↔ V(H₁'.val) = V(H₂'.val)
  rw [Subtype.coe_inj]
  exact H₁'.vertexSet_inj

lemma vertexSet_injective : Injective (V(·.val) : G.ClosedSubgraph → Set α) :=
  fun _ _ => vertexSet_inj.mpr

lemma vertexSet_strictMono (G : Graph α β) :
    StrictMono (V(·.val) : G.ClosedSubgraph → Set α) := fun H₁ H₂ hlt => by
  rw [lt_iff_le_and_ne, ← vertexSet_inj.ne]
  exact ⟨vertexSet_mono hlt.le, hlt.ne⟩

lemma disjoint_iff (H₁ H₂ : G.ClosedSubgraph) :
    Disjoint H₁ H₂ ↔ H₁.val.StronglyDisjoint H₂.val := by
  rw [_root_.disjoint_iff, ← Subtype.coe_inj, coe_inf, coe_bot, ← disjoint_iff_inter_eq_bot,
    stronglyDisjoint_iff_disjoint_of_compatible (H₁.compatible H₂)]

lemma disjoint_iff_vertexSet_disjoint :
    Disjoint H₁ H₂ ↔ Disjoint V(H₁.val) V(H₂.val) := by
  rw [ClosedSubgraph.disjoint_iff, (H₁.compatible H₂).disjoint_iff_vertexSet_disjoint]

lemma disjoint_iff_val_disjoint (H₁ H₂ : G.ClosedSubgraph) :
    Disjoint H₁ H₂ ↔ Disjoint H₁.val H₂.val := by
  rw [H₁.disjoint_iff_vertexSet_disjoint, Graph.disjoint_iff_vertexSet_disjoint]

@[simp]
lemma eq_ambient_of_subset_vertexSet (h : V(G) ⊆ V(H.val)) : H = ⊤ := by
  have hV : V(G) = V(H.val) := subset_antisymm h (vertexSet_mono H.prop.le)
  refine le_antisymm le_top ?_
  rw [← Subtype.coe_le_coe, ← H.coe_eq_induce, ← vertexPartition_eq_iff.mpr hV,
    induce_vertexSet_self]
  rfl

lemma IsClosedSubgraph.eq_ambient_of_subset_vertexSet {H : Graph α β} (hcl : H ≤c G)
    (h : V(G) ⊆ V(H)) : H = G := by
  let H' : G.ClosedSubgraph := ⟨H, hcl⟩
  change H'.val = (⊤ : G.ClosedSubgraph).val
  rw [Subtype.coe_inj]
  exact H'.eq_ambient_of_subset_vertexSet h

lemma le_iff_vertexSet_subset : H₁ ≤ H₂ ↔ V(H₁.val) ⊆ V(H₂.val) := by
  rw [← Subtype.coe_le_coe, ← H₁.coe_eq_induce, ← H₂.coe_eq_induce]
  exact induce_mono_right_iff G

lemma lt_iff_vertexSet_ssubset : H₁ < H₂ ↔ V(H₁.val) ⊂ V(H₂.val) := by
  refine ⟨(vertexSet_strictMono G ·), fun h => ?_⟩
  simp [lt_iff_le_and_ne, le_iff_vertexSet_subset.mpr h.subset, vertexSet_inj, h.ne]

lemma IsClosedSubgraph.le_iff_vertexSet_subset {H₁ H₂ : Graph α β} (hcl₁ : H₁ ≤c G)
    (hcl₂ : H₂ ≤c G) : H₁ ≤ H₂ ↔ V(H₁) ⊆ V(H₂) := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl₁⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hcl₂⟩
  change H₁' ≤ H₂' ↔ V(H₁'.val) ⊆ V(H₂'.val)
  exact H₁'.le_iff_vertexSet_subset

lemma IsClosedSubgraph.lt_iff_vertexSet_ssubset {H₁ H₂ : Graph α β} (hcl₁ : H₁ ≤c G)
    (hcl₂ : H₂ ≤c G) : H₁ < H₂ ↔ V(H₁) ⊂ V(H₂) := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl₁⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hcl₂⟩
  change H₁' < H₂' ↔ V(H₁'.val) ⊂ V(H₂'.val)
  exact H₁'.lt_iff_vertexSet_ssubset

@[simp]
lemma compl_vertexSet (H : G.ClosedSubgraph) :
    V((Hᶜ : G.ClosedSubgraph).val) = V(G) \ V(H.val) := by
  change V(compl' H) = _
  rw [compl'_vertexSet]

@[simp]
lemma compl_edgeSet (H : G.ClosedSubgraph) :
    E((Hᶜ : G.ClosedSubgraph).val) = E(G) \ E(H.val) := by
  change E(compl' H) = E(G) \ E(H.val)
  rw [compl'_edgeSet]

@[simp]
lemma compl_isLink (H : G.ClosedSubgraph) :
    Hᶜ.val.IsLink e x y ↔ G.IsLink e x y ∧ e ∉ E(H.val) := by
  change (compl' H).IsLink e x y ↔ _
  rw [compl'_isLink]

-- lemma compl_eq_of_stronglyDisjoint_union {H₁ H₂ : Graph α β}
--     (hdisj : H₁.StronglyDisjoint H₂) :
--     (⟨H₁, hdisj.isClosedSubgraph_union_left⟩ : (H₁ ∪ H₂).ClosedSubgraph)ᶜ =
--     ⟨H₂, hdisj.isClosedSubgraph_union_right⟩ := by
--   rw [vertexSet_inj]
--   simp only [compl_vertexSet, union_vertexSet, union_diff_left, sdiff_eq_left]
--   exact hdisj.vertex.symm

lemma isAtom_iff_isCompOf (H : G.ClosedSubgraph) :
    IsAtom H ↔ H.val.IsCompOf G := by
  simp only [IsAtom, ne_eq, Subtype.forall, bot_isClosedSubgraph, Subtype.mk_eq_bot_iff, IsCompOf,
    Minimal, vertexSet_nonempty_iff, Subtype.coe_eq_bot_iff, ge_iff_le, and_imp]
  apply and_congr (not_iff_not.mp ?_) <| forall₂_congr fun H' hH'cl => ?_
  · simp [H.prop]
  rw [lt_iff_le_and_ne, ← and_imp, and_comm (a := ¬H' = ⊥), and_imp, and_imp]
  refine imp_congr_right fun hle => ?_
  convert not_imp_not
  · tauto
  simp [le_antisymm_iff, hle]

/-- Distinct components are vertex-disjoint. -/
lemma IsCompOf.stronglyDisjoint_of_ne {H₁ H₂ : Graph α β} (hco₁ : H₁.IsCompOf G)
    (hco₂ : H₂.IsCompOf G) (hne : H₁ ≠ H₂) : StronglyDisjoint H₁ H₂ := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hco₁.isClosedSubgraph⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hco₂.isClosedSubgraph⟩
  have := (H₁'.isAtom_iff_isCompOf.mpr hco₁).disjoint_of_ne (H₂'.isAtom_iff_isCompOf.mpr hco₂)
  rw [← Subtype.coe_ne_coe, H₁'.disjoint_iff] at this
  exact this hne

lemma IsCompOf.eq_of_mem_mem {H₁ H₂ : Graph α β} (hH₁ : H₁.IsCompOf G)
    (hH₂ : H₂.IsCompOf G) (hx₁ : x ∈ V(H₁)) (hx₂ : x ∈ V(H₂)) : H₁ = H₂ :=
  by_contra fun hne ↦ (hH₁.stronglyDisjoint_of_ne hH₂ hne).vertex.notMem_of_mem_left hx₁ hx₂

end ClosedSubgraph

end Lattice
