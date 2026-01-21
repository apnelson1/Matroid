import Matroid.Graph.Subgraph.Lemma
import Mathlib.Order.Atoms

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α}

open Set Function

open scoped Sym2

namespace Graph

namespace WithTop

lemma eq_top_or_eq_some {α : Type*} (a' : WithTop α) : a' = ⊤ ∨ ∃ a : α, a' = WithTop.some a :=
  Option.eq_none_or_eq_some a'

noncomputable def sInter (s : Set (WithTop <| Graph α β)) : WithTop <| Graph α β := by
  by_cases hs : ∃ G : Graph α β, WithTop.some G ∈ s
  · exact WithTop.some (Graph.sInter (WithTop.some ⁻¹' s) (by tauto))
  · exact ⊤

noncomputable instance : CompleteSemilatticeInf (WithTop <| Graph α β) where
  sInf := sInter
  sInf_le s G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · exact le_top
    have : ∃ G : Graph α β, WithTop.some G ∈ s := by use G
    simp only [sInter, this, ↓reduceDIte, ge_iff_le]
    exact WithTop.coe_le_coe.mpr <| Graph.sInter_le hG
  le_sInf s G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · suffices ∀ G : Graph α β, WithTop.some G ∉ s by simp [this, sInter]
      exact fun _ hHs => Option.some_ne_none _ (top_le_iff.mp <| hG _ hHs)
    unfold sInter
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <|
        (Graph.le_sInter_iff h).mpr fun _ hHs => WithTop.coe_le_coe.mp (hG _ hHs)
    · exact le_top

noncomputable instance : CompleteLattice (WithTop <| Graph α β) where
  sup G H := by
    classical
    exact G.bind (fun G ↦ H.bind (fun H ↦ if Compatible G H then WithTop.some <| G ∪ H else none))
  le_sup_left G H := by
    obtain rfl | ⟨G, rfl⟩ := Option.eq_none_or_eq_some G
    · simp
    obtain rfl | ⟨H, rfl⟩ := Option.eq_none_or_eq_some H
    · simp only [Option.bind_none, Option.bind_fun_none]
      exact le_top
    simp only [Option.bind_some]
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <| Graph.left_le_union G H
    · exact le_top
  le_sup_right G H := by
    obtain rfl | ⟨G, rfl⟩ := Option.eq_none_or_eq_some G
    · exact le_top
    obtain rfl | ⟨H, rfl⟩ := Option.eq_none_or_eq_some H
    · simp
    simp only [Option.bind_some]
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <| Compatible.right_le_union h
    · exact le_top
  sup_le G H K hGK hHK := by
    obtain rfl | ⟨G, rfl⟩ := Option.eq_none_or_eq_some G
    · simpa
    obtain rfl | ⟨H, rfl⟩ := Option.eq_none_or_eq_some H
    · simpa
    obtain rfl | ⟨K, rfl⟩ := Option.eq_none_or_eq_some K
    · exact le_top
    have hGK : G ≤ K := WithTop.coe_le_coe.mp hGK
    have hHK : H ≤ K := WithTop.coe_le_coe.mp hHK
    simp only [Option.bind_some, compatible_of_le_le hGK hHK, ↓reduceIte, ge_iff_le]
    exact WithTop.coe_le_coe.mpr <| Graph.union_le hGK hHK
  sSup s := by
    classical
    exact if h : (WithTop.some ⁻¹' s).Pairwise Compatible ∧ ⊤ ∉ s
      then WithTop.some (Graph.sUnion (WithTop.some ⁻¹' s) h.1) else ⊤
  le_sSup s G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · simp [hG]
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <| G.le_sUnion h.1 hG
    · exact le_top
  sSup_le s G hG := by
    obtain rfl | ⟨G, rfl⟩ := eq_top_or_eq_some G
    · simp
    have hG' : ∀ H ∈ WithTop.some ⁻¹' s, H ≤ G := fun _ hH => WithTop.coe_le_coe.mp (hG _ hH)
    split_ifs with h
    · exact WithTop.coe_le_coe.mpr <| by rwa [Graph.sUnion_le_iff]
    · simp only [set_pairwise_compatible_of_subgraph hG', true_and, not_not] at h
      exact hG ⊤ h
  __ := completeLatticeOfCompleteSemilatticeInf _

-- lemma disjoint_iff_disjoint : Disjoint (WithTop.some G) (WithTop.some H) ↔ G.Disjoint H := by
--   rw [disjoint_iff_inf_le, le_bot_iff]
--   sorry

-- lemma IsClosedSubgraph_of_mem_partition {G H : Graph α β} (P : Partition (WithTop.some G))
--     (hH : WithTop.some H ∈ P) : H ≤c G where
--   le := by simpa using P.le_of_mem hH
--   closed {e x} hxy hx := by
--     have := P.indep hH
--     sorry





end WithTop

section Lattice

variable {H : ι → Graph α β} {H₀ : Graph α β}

-- protected def iInterAux (H : ι → Graph α β) (hf : ∀ i, H i ≤ G) : Graph α β :=
--   Graph.iInter (Option.elim · G H) (G.pairwise_compatible_of_subgraph
--     (by rintro (rfl | i) <;> simp [hf]))

-- @[simp]
-- lemma iInterAux_eq_iInter [Nonempty ι] (H : ι → Graph α β) (hf : ∀ i, H i ≤ G) :
--     Graph.iInterAux H hf = Graph.iInter H (G.pairwise_compatible_of_subgraph hf) := by
--   unfold Graph.iInterAux
--   sorry

-- lemma iInterAux_empty [IsEmpty ι] (H : ι → Graph α β) :
--     G.iInterAux H (by simp) = G := sorry

-- lemma iInterAux_le (hf : ∀ i, H i ≤ G) : Graph.iInterAux H hf ≤ G := sorry

-- @[simp]
-- lemma le_iInterAux_iff (hf : ∀ i, H i ≤ G) : H₀ ≤ G.iInterAux H hf ↔ ∀ i, H₀ ≤ H i := by
--   sorry

-- lemma le_iInterAux (hf : ∀ i, H i ≤ G) (h₀ : ∀ i, H₀ ≤ H i) : H₀ ≤ Graph.iInterAux H hf := sorry

-- lemma iInterAux_le_mem (hf : ∀ i, H i ≤ G) (i : ι) :
--     Graph.iInterAux H hf ≤ H i := sorry

-- -- lemma iInterAux_le_mem (hf : ∀ i, H i ≤ G) (i : ι) :

-- -- @[simp]
-- -- lemma le_iInterAux_iff (hf : ∀ i, H i ≤ G) : H₀ ≤ G.iInterAux H hf ↔ ∀ i, H₀ ≤ H i := by
-- --   sorry

-- -- @[simp]
-- -- lemma iInterAux_eq_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
-- --     Graph.sInter s (G.set_pairwise_compatible_of_subgraph h) =
-- --     -- Graph.iInterAux H hf = Graph.iInter H (G.pairwise_compatible_of_subgraph hf) := by
-- --   sorry

@[reducible] def Subgraph (G : Graph α β) := {H // H ≤ G}

namespace Subgraph
variable {H H₁ H₂ : G.Subgraph}

instance : CoeOut G.Subgraph (Graph α β) where
  coe H := H.1

@[simp]
lemma le (H : G.Subgraph) : H.1 ≤ G := H.2

instance : PartialOrder G.Subgraph := inferInstanceAs (PartialOrder {H // H ≤ G})

@[simp]
lemma mk_le_iff {H₁} {hH₁ : H₁ ≤ G} : (⟨H₁, hH₁⟩ : G.Subgraph) ≤ H ↔ H₁ ≤ H.1 := Iff.rfl

@[simp]
lemma le_mk_iff {H₁} {hH₁ : H₁ ≤ G} : H ≤ (⟨H₁, hH₁⟩ : G.Subgraph) ↔ H.1 ≤ H₁ := Iff.rfl

lemma le_iff_subset : H₁ ≤ H₂ ↔ V(H₁.val) ⊆ V(H₂.val) ∧ E(H₁.val) ⊆ E(H₂.val) := by
  refine ⟨fun h => ⟨by grw [h], by grw [h]⟩, fun ⟨H1, H2⟩ => ?_⟩
  exact Subtype.coe_le_coe.mp <| le_of_le_le_subset_subset H₁.prop H₂.prop H1 H2

@[ext]
lemma ext (hV : V(H₁.val) = V(H₂.val)) (hE : E(H₁.val) = E(H₂.val)) : H₁ = H₂ :=
  Subtype.ext <| Graph.ext_of_le_le H₁.prop H₂.prop hV hE

lemma _root_.Graph.IsLink.of_mem (hxy : H₁.val.IsLink e x y) (he : e ∈ E(H₂.val)) :
    H₂.val.IsLink e x y := hxy.of_le H₁.prop |>.of_le_of_mem H₂.prop he

lemma _root_.Graph.IsLink.isLink_iff_mem (hxy : H₁.val.IsLink e x y) :
    H₂.val.IsLink e x y ↔ e ∈ E(H₂.val) :=
  ⟨fun h => h.edge_mem, fun h => hxy.of_mem h⟩

lemma _root_.Graph.Inc.of_mem (h : H₁.val.Inc e x) (he : e ∈ E(H₂.val)) : H₂.val.Inc e x :=
  h.of_le H₁.prop |>.of_le_of_mem H₂.prop he

lemma _root_.Graph.Inc.isInc_iff_mem (hx : H₁.val.Inc e x) :
    H₂.val.Inc e x ↔ e ∈ E(H₂.val) :=
  ⟨fun h => h.edge_mem, fun h => hx.of_mem h⟩

lemma endSetSet_subset_of_le_subset (H₁ : G.Subgraph) (hF : F ⊆ E(H₂.val)) :
    V(H₁.val, F) ⊆ V(H₂.val, F) := by
  rintro x ⟨e, he, hx⟩
  exact ⟨e, he, hx.of_mem (hF he)⟩

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

/-- The proof that the subgraphs of a graph `G` form a completely distributive lattice. -/
instance : CompleteLattice G.Subgraph where
  sup H₁ H₂ := ⟨H₁ ∪ H₂, Graph.union_le H₁.2 H₂.2⟩
  le_sup_left _ _ := Graph.left_le_union ..
  le_sup_right H H' := (compatible_of_le_le H.2 H'.2).right_le_union
  sup_le _ _ _ := Graph.union_le
  inf H₁ H₂ := ⟨H₁ ∩ H₂, Graph.inter_le_left.trans H₁.2⟩
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter
  sSup s := ⟨Graph.sUnion (((↑) : G.Subgraph → Graph α β) '' s)
    (G.set_pairwise_compatible_of_subgraph (by simp +contextual)), (by simp +contextual)⟩
  le_sSup s H hHs := by
    generalize_proofs h₁ h₂
    exact Graph.le_sUnion h₁ <| by simpa [H.2]
  sSup_le s H h := by
    simp only [Subgraph.mk_le_iff, Graph.sUnion_le_iff, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    aesop
  sInf s := ⟨Graph.sInter (insert G (((↑) : G.Subgraph → Graph α β) '' s)) (by simp),
    Graph.sInter_le (by simp) ..⟩
  sInf_le s H h := by
    generalize_proofs h₁
    exact Graph.sInter_le <| by simp [h]
  le_sInf s H h := by simpa using fun K h' hK ↦ h _ hK
  top := ⟨G, le_rfl⟩
  le_top H := H.2
  bot := ⟨⊥, by simp⟩
  bot_le := by simp

@[simp]
lemma coe_top : ((⊤ : G.Subgraph) : Graph α β) = G := rfl

@[simp]
lemma coe_bot : ((⊥ : G.Subgraph) : Graph α β) = ⊥ := rfl

@[simp, push]
lemma ne_bot_iff : H ≠ ⊥ ↔ V(H.val).Nonempty := by
  rw [← Graph.ne_bot_iff]
  simp

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
    (⨆ i, H i : G.Subgraph) = Graph.iUnion (fun i ↦ (H i : Graph α β)) (by simp) := by
  change Graph.sUnion _ (by simp) = _
  rw [le_antisymm_iff]
  simp only [Graph.sUnion_le_iff, mem_image, mem_range, exists_exists_eq_and, forall_exists_index,
    forall_apply_eq_imp_iff, Graph.iUnion_le_iff]
  exact ⟨Graph.le_iUnion (G := fun i ↦ (H i).1) (by simp), fun h ↦ Graph.le_sUnion _ (by simp)⟩

@[simp]
lemma coe_sSup (s : Set G.Subgraph) :
    ((sSup s : G.Subgraph) : Graph α β) = Graph.sUnion ((↑) '' s) (by simp) := rfl

-- @[simp↓]
-- lemma coe_biSup (s : Set ι) (H : ι → G.Subgraph) :
--     (⨆ i ∈ s, H i : G.Subgraph) = sUnion' (Subtype.val ∘ H '' s) G (by simp) := by
--   simp_rw [← sSup_image, coe_sSup, image_comp]

@[simp]
lemma coe_sup (H₁ H₂ : G.Subgraph) : ((H₁ ⊔ H₂ : G.Subgraph) : Graph α β) = H₁.1 ∪ H₂.1 :=
  rfl

@[simp]
lemma coe_sup_eq_union (H₁ H₂ : G.Subgraph) : (H₁ ⊔ H₂ : G.Subgraph).val = H₁.1 ∪ H₂.1 := by
  rfl

@[simp]
lemma coe_inf (H₁ H₂ : G.Subgraph) : ((H₁ ⊓ H₂ : G.Subgraph) : Graph α β) = H₁.1 ∩ H₂.1 :=
  rfl

@[simp]
lemma range_iSup (f : ι' → ι) (H : ι → G.Subgraph) :
    (⨆ (i : Set.range f), H i : G.Subgraph) = ⨆ i, H (f i) := by
  apply_fun Subtype.val using Subtype.val_injective
  simp only [coe_iSup]
  exact Graph.iUnion_range _

@[simp]
lemma range_iInf (f : ι' → ι) (H : ι → G.Subgraph) :
    (⨅ (i : Set.range f), H i : G.Subgraph) = ⨅ i, H (f i) := by
  apply_fun Subtype.val using Subtype.val_injective
  obtain hι | hι := isEmpty_or_nonempty ι'
  · have : IsEmpty ↑(range f) := by simpa
    simp
  · simp [Graph.iInter_range]

lemma disjoint_iff_stronglyDisjoint (H₁ H₂ : G.Subgraph) :
    Disjoint H₁ H₂ ↔ H₁.val.StronglyDisjoint H₂.val := by
  rw [_root_.disjoint_iff, ← Subtype.coe_inj, coe_inf, coe_bot, ← disjoint_iff_inter_eq_bot,
    stronglyDisjoint_iff_disjoint_of_compatible (H₁.compatible H₂)]

@[simp]
lemma disjoint_iff (H₁ H₂ : G.Subgraph) : Disjoint H₁ H₂ ↔ Disjoint V(H₁.val) V(H₂.val) := by
  rw [_root_.disjoint_iff, ← Subtype.coe_inj, coe_inf, coe_bot, ← disjoint_iff_inter_eq_bot,
    disjoint_iff_vertexSet_disjoint]

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
    ext a b c <;> simp only [coe_iInf_of_nonempty, coe_iSup, iInter_vertexSet, iUnion_vertexSet,
      mem_iInter, mem_iUnion] <;> exact ⟨fun h => ⟨fun i ↦ (h i).choose, fun i ↦ (h i).choose_spec⟩,
        fun h i => ⟨h.choose i, h.choose_spec i⟩⟩

/-- The subgraphs of a graph `G` form a completely distributive lattice.-/
instance : CompletelyDistribLattice G.Subgraph :=
  CompletelyDistribLattice.ofMinimalAxioms Subgraph.minAx

/-- The minimal subgraph of `G` that contains the edges in `F`. -/
def ofEdge (G : Graph α β) (F : Set β) : G.Subgraph where
  val := G[V(G, F)] ↾ F
  property := edgeRestrict_le.trans <| induce_le (by simp)

@[simp]
lemma induce_endSetSet_inter_eq (F : Set β) : E(G[V(G, F)]) ∩ F = E(G) ∩ F := by
  ext e
  simp only [induce_edgeSet, mem_endSetSet_iff, mem_inter_iff, mem_setOf_eq, and_congr_left_iff]
  refine fun he ↦ ⟨fun ⟨_, _, he, _⟩ => he.edge_mem, fun h => ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, ⟨e, he, h.inc_left⟩, ⟨e, he, h.inc_right⟩⟩

@[simp]
lemma ofEdge_vertexSet (F : Set β) : V((ofEdge G F).val) = V(G, F) := by
  simp [ofEdge]

@[simp]
lemma ofEdge_edgeSet (F : Set β) : E((ofEdge G F).val) = E(G) ∩ F := by
  simp [ofEdge, edgeRestrict_edgeSet]

@[simp]
lemma ofEdge_isLink (F : Set β) : (ofEdge G F).val.IsLink e x y ↔ e ∈ F ∧ G.IsLink e x y := by
  simp only [ofEdge, edgeRestrict_isLink, induce_isLink, mem_endSetSet_iff, and_congr_right_iff,
    and_iff_left_iff_imp]
  exact fun heF he ↦ ⟨⟨e, heF, he.inc_left⟩, e, heF, he.inc_right⟩

/-- The complement of a subgraph of `G` is the minimal subgraph of `G` that contains
  the edges and vertices that are not in the subgraph. See `compl_le_iff`.
  This complement is not well behaved in general order theoretically. See `inf_compl_eq_bot_iff`.
  However, it is useful for other purposes.-/
instance : Compl G.Subgraph where
  compl H := by
    use G[V(G) \ V(H.val) ∪ V(G, E(G) \ E(H.val))] ＼ E(H.val)
    grw [edgeDelete_le, induce_le]
    rw [union_subset_iff]
    refine ⟨?_, endSetSet_subset G _⟩
    grw [← vertexDelete_vertexSet, vertexSet_mono (vertexDelete_le)]

lemma compl_vertexSet (H : G.Subgraph) : V(Hᶜ.val) = V(G) \ V(H.val) ∪ V(G, E(G) \ E(H.val)) := rfl

@[simp]
lemma compl_edgeSet (H : G.Subgraph) : E(Hᶜ.val) = E(G) \ E(H.val) := by
  change E(G[V(G) \ V(H.val) ∪ V(G, E(G) \ E(H.val))] ＼ E(H.val)) = _
  ext e
  simp only [edgeDelete_edgeSet, induce_edgeSet, mem_union, mem_diff, mem_endSetSet_iff,
    mem_setOf_eq, and_congr_left_iff]
  refine fun heH ↦ ⟨fun ⟨x, y, hxy, h⟩ => hxy.edge_mem, fun h => ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
  use x, y, hxy, ?_, ?_ <;> right <;> use e, ⟨h, heH⟩
  · exact hxy.inc_left
  · exact hxy.inc_right

lemma disjoint_compl_edgeSet (H : G.Subgraph) : Disjoint E(H.val) E(Hᶜ.val) := by
  simp only [compl_edgeSet]
  exact disjoint_sdiff_right

lemma mem_edgeSet_or_compl_edgeSet (H : G.Subgraph) (he : e ∈ E(G)) :
    e ∈ E(H.val) ∨ e ∈ E(Hᶜ.val) := by
  simp only [compl_edgeSet, mem_diff, he, true_and]
  exact em _

@[simp]
lemma compl_isLink (H : G.Subgraph) : Hᶜ.val.IsLink e x y ↔ G.IsLink e x y ∧ e ∉ E(H.val) := by
  rw [isLink_iff_isLink_and_mem_of_le Hᶜ.prop, compl_edgeSet, mem_diff, ← and_assoc]
  simp only [and_congr_left_iff, and_iff_left_iff_imp]
  exact fun a a_1 ↦ a_1.edge_mem

lemma vertexSet_compl_subset_compl_vertexSet (H : G.Subgraph) : V(G) \ V(H.val) ⊆ V(Hᶜ.val) := by
  simp only [compl_vertexSet, subset_union_left]

@[simp]
lemma compl_le_iff : H₁ᶜ ≤ H₂ ↔ V(G) \ V(H₁.val) ⊆ V(H₂.val) ∧ E(G) \ E(H₁.val) ⊆ E(H₂.val) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨H1, H2⟩ => ?_⟩
  · grw [← h, vertexSet_compl_subset_compl_vertexSet]
  · grw [← h, compl_edgeSet]
  grw [le_iff_subset, compl_edgeSet, compl_vertexSet, union_subset_iff]
  use ⟨H1, ?_⟩, H2
  have := coe_top ▸ endSetSet_subset_of_le_subset ⊤ H2
  grw [this, endSetSet_subset]

lemma ofEdge_diff_le_compl (H : G.Subgraph) : ofEdge G (E(G) \ E(H.val)) ≤ Hᶜ := by
  refine le_iff_subset.mpr ⟨?_, ?_⟩
  · simp [ofEdge_vertexSet, compl_vertexSet]
  simp

-- @[simp]
-- lemma compl_compl (H : G.Subgraph) : Hᶜᶜ = H := by
--   rw [Subgraph.ext_iff]
--   have hE : E(Hᶜᶜ.val) = E(H.val) := by
--     simp [edgeSet_mono H.prop]
--   refine ⟨?_, hE⟩
--   ext x
--   simp +contextual only [compl_vertexSet, compl_edgeSet, sdiff_sdiff_right_self,
-- Set.inf_eq_inter,
--     mem_union, mem_diff, mem_endSetSet_iff, not_or, not_and, not_not, not_exists, and_imp,
--     mem_inter_iff, iff_def, implies_true, true_and]
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · obtain ⟨h, h', h''⟩ | ⟨e, h, h'⟩ := h
--     · exact h' h
--     exact h'.of_le_of_mem H.prop h.2 |>.vertex_mem
--   by_cases he : ∃ e, H.val.Inc e x
--   · obtain ⟨e, he⟩ := he
--     exact Or.inr ⟨e, ⟨edgeSet_mono H.prop he.edge_mem, he.edge_mem⟩, he.of_le H.prop⟩
--   left
--   use vertexSet_mono H.prop h
--   rintro e heG heH hex
--   have := he

def sep (H : G.Subgraph) : Set α := V(H.val) ∩ V(G, E(G) \ E(H.val))

@[simp]
lemma mem_sep_iff (H : G.Subgraph) (x : α) :
    x ∈ H.sep ↔ x ∈ V(H.val) ∧ ∃ e ∈ E(G) \ E(H.val), G.Inc e x := Iff.rfl

@[simp]
lemma sep_subset (H : G.Subgraph) : H.sep ⊆ V(H.val) := by
  rintro x ⟨hx, _⟩
  exact hx

lemma sep_eq_vertexSet_inter_compl : H₁.sep = V(H₁.val) ∩ V(H₁ᶜ.val) := by
  ext x
  rw [compl_vertexSet, inter_union_distrib_left, mem_union]
  simp only [mem_sep_iff, mem_diff, inter_diff_self, mem_empty_iff_false, mem_inter_iff,
    mem_endSetSet_iff, false_or]

@[simp]
lemma sep_subset_compl (H : G.Subgraph) : H.sep ⊆ V(Hᶜ.val) := by
  simp [sep_eq_vertexSet_inter_compl]

lemma inf_compl_eq_bot_iff : H₁ ⊓ H₁ᶜ = ⊥ ↔ H₁.val ≤c G := by
  refine ⟨fun h => ⟨H₁.prop, fun e x hex hxH ↦ ?_⟩, fun h => ?_⟩
  · by_contra! he
    apply_fun Graph.vertexSet ∘ Subtype.val at h
    simp only [comp_apply, coe_inf, inter_vertexSet, ← sep_eq_vertexSet_inter_compl, coe_bot,
      bot_vertexSet, eq_empty_iff_forall_notMem] at h
    exact h x ⟨hxH, by use e, ⟨hex.edge_mem, he⟩⟩
  refine Subtype.ext ?_
  simp only [coe_inf, coe_bot, inter_eq_bot_iff, compl_vertexSet]
  ext x
  simp +contextual only [mem_inter_iff, mem_union, mem_diff, mem_endSetSet_iff, mem_empty_iff_false,
    iff_false, not_and, not_true_eq_false, and_false, false_or, not_exists, and_imp]
  rintro hxH e he heH hex
  exact heH <| h.closed hex hxH

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
  sup H₁ H₂ := ⟨H₁ ∪ H₂, H₁.2.union H₂.2⟩
  le_sup_left _ _ := Graph.left_le_union ..
  le_sup_right H H' := (compatible_of_le_le H.2.le H'.2.le).right_le_union
  sup_le _ _ _ := Graph.union_le
  inf H₁ H₂ := ⟨H₁ ∩ H₂, H₁.2.inter H₂.2⟩
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter



lemma coe_le_coe {H₀ H : G.ClosedSubgraph} : H₀.1 ≤ H.1 ↔ H₀ ≤ H := Iff.rfl

lemma coe_lt_coe {H₀ H : G.ClosedSubgraph} : H₀.1 < H.1 ↔ H₀ < H := Iff.rfl

lemma toSubgraph_le_toSubgraph {H₁ H₂ : G.ClosedSubgraph} :
    H₁.toSubgraph ≤ H₂.toSubgraph ↔ H₁ ≤ H₂ := Iff.rfl

lemma toSubgraph_lt_toSubgraph {H₁ H₂ : G.ClosedSubgraph} :
    H₁.toSubgraph < H₂.toSubgraph ↔ H₁ < H₂ := Iff.rfl

@[simp]
lemma coe_sup (H₁ H₂ : G.ClosedSubgraph) :
    ((H₁ ⊔ H₂ : G.ClosedSubgraph) : Graph α β) = H₁.1 ∪ H₂.1 := rfl

@[simp]
lemma coe_inf (H₁ H₂ : G.ClosedSubgraph) : (H₁ ⊓ H₂ : G.ClosedSubgraph).val = H₁.1 ∩ H₂.1 :=
  rfl

@[simp]
lemma pairwise_compatible (H : ι → G.ClosedSubgraph) :
    Pairwise (Compatible on (fun i ↦ (H i : Graph α β))) :=
  G.pairwise_compatible_of_subgraph (fun i ↦ (H i).2.le)

@[simp]
lemma set_pairwise_compatible (s : Set G.ClosedSubgraph) :
    ((((↑) : _ → Graph α β) '' s).Pairwise Compatible) :=
  G.set_pairwise_compatible_of_subgraph (by rintro _ ⟨H, -, rfl⟩; exact H.2.le)

@[simp]
lemma sup_vertexSet (H₁ H₂ : G.ClosedSubgraph) : V((H₁ ⊔ H₂).val) = V(H₁.val) ∪ V(H₂.val) := by
  simp

@[simp]
lemma sup_edgeSet (H₁ H₂ : G.ClosedSubgraph) : E((H₁ ⊔ H₂).val) = E(H₁.val) ∪ E(H₂.val) := by
  simp

-- @[simp]
-- lemma sup_isLink (H₁ H₂ : G.ClosedSubgraph) :
--     (H₁ ⊔ H₂).val.IsLink e = H₁.val.IsLink e ⊔ H₂.val.IsLink e := by
--   ext u v
--   simp

@[simp]
lemma inf_vertexSet (H₁ H₂ : G.ClosedSubgraph) : V((H₁ ⊓ H₂).val) = V(H₁.val) ∩ V(H₂.val) := by
  simp

-- @[simp]
-- lemma inf_edgeSet (H₁ H₂ : G.ClosedSubgraph) : E((H₁ ⊓ H₂).val) = E(H₁.val) ∩ E(H₂.val) := by
--   simp

-- @[simp]
-- lemma compl'_vertexSet (H : G.ClosedSubgraph) : V(G - V(H.val)) = V(G) \ V(H.val) := by
--   simp

-- @[simp↓]
-- lemma compl'_isLink (H : G.ClosedSubgraph) :
--     (G - V(H.val)).IsLink e x y ↔ G.IsLink e x y ∧ e ∉ E(H.val) := by
--   simp only [vertexDelete_isLink_iff, and_congr_right_iff, ← not_or, not_iff_not]
--   exact fun he ↦ ⟨fun h ↦ h.elim (H.prop.closed ⟨y, he⟩) (H.prop.closed ⟨x, he.symm⟩),
--     fun h ↦ Or.inl <| he.of_le_of_mem (H.prop.le) h |>.left_mem⟩

-- @[simp]
-- lemma compl'_edgeSet (H : G.ClosedSubgraph) : E(G - V(H.val)) = E(G) \ E(H.val) := by
--   rw [edgeSet_eq_setOf_exists_isLink, edgeSet_eq_setOf_exists_isLink]
--   simp only [↓compl'_isLink, exists_and_right]
--   rfl

-- lemma compl'_isClosedSubgraph (H : G.ClosedSubgraph) : G - V(H.val) ≤c G where
--   vertexSet_subset := by simp [diff_subset]
--   isLink_of_isLink e u v h := h.1
--   closed e u he := by
--     rintro ⟨huG, _, huH⟩
--     rw [compl'_edgeSet]
--     simp_all [he.edge_mem, H.prop.edge_mem_iff_vertex_mem_of_inc he]

-- lemma _root_.Graph.IsClosedSubgraph.compl {H : Graph α β} (hcl : H ≤c G) : G - V(H) ≤c G :=
--   let H' : G.ClosedSubgraph := ⟨H, hcl⟩
--   H'.compl'_isClosedSubgraph


instance : CompleteBooleanAlgebra G.ClosedSubgraph where
  sSup s := ⟨((⨆ (H : s), ClosedSubgraph.toSubgraph H.1 : G.Subgraph) : Graph α β),
    by simpa only [Subgraph.coe_iSup] using iUnion_isClosedSubgraph fun H ↦ H.1.2⟩
  le_sSup s H hHs := by
    simp only [Subgraph.coe_iSup, ClosedSubgraph.coe_toSubgraph]
    exact Graph.le_iUnion (G := fun i : s ↦ (i.1.toSubgraph : Graph α β))
      (G.pairwise_compatible_of_subgraph (by simp +contextual [IsClosedSubgraph.le])) ⟨H, hHs⟩
  sSup_le := by simp
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
  bot := ⟨⊥, by simp⟩
  top := ⟨G, isClosedSubgraph_self⟩
  le_top := by simp +contextual [IsClosedSubgraph.le]
  bot_le := by simp
  le_sup_inf := by
    refine fun ⟨H₁, h₁⟩ ⟨H₂, h₂⟩ ⟨H₃, h₃⟩ ↦ ClosedSubgraph.coe_le_coe.1 ?_
    refine ⟨by simp [← union_inter_distrib_left], fun e x y ↦ ?_⟩
    simp only [ClosedSubgraph.coe_inf, ClosedSubgraph.coe_sup, inter_isLink_iff, and_imp,
      inter_isLink_iff, (compatible_of_le_le h₁.le h₂.le).union_isLink_iff,
      (compatible_of_le_le h₁.le h₃.le).union_isLink_iff,
      (G.compatible_of_le_le h₁.le (Graph.inter_le_left.trans h₂.le)).union_isLink_iff]
    tauto
  compl H := ⟨_, H.2.compl⟩
  sdiff H₁ H₂ := _
  himp H₁ H₂ := _
  inf_compl_le_bot := by simp [← vertexSet_eq_empty_iff]
  top_le_sup_compl := by
    simp only [ClosedSubgraph.mk_le_iff, ClosedSubgraph.coe_sup, Subtype.forall]
    refine fun H hc ↦ ⟨by simp, fun e x y he ↦ ?_⟩
    rw [(G.compatible_of_le_le hc.le (by simp)).union_isLink_iff]
    by_cases hx : x ∈ V(H)
    · exact .inl <| he.of_isClosedSubgraph_of_mem hc hx
    exact .inr <| he.of_isClosedSubgraph_of_mem hc.compl (by simp [hx, he.left_mem])
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

@[simp]
lemma coe_top : ((⊤ : G.ClosedSubgraph) : Graph α β) = G := rfl

@[simp]
lemma coe_bot : ((⊥ : G.ClosedSubgraph) : Graph α β) = ⊥ := rfl

@[simp]
lemma toSubgraph_sSup (s : Set G.ClosedSubgraph) :
    toSubgraph (sSup s) = ⨆ (H : s), toSubgraph H.1 := rfl

@[simp]
lemma coe_sSup (s : Set G.ClosedSubgraph) :
    ((sSup s : G.ClosedSubgraph) : Graph α β) =
    Graph.sUnion (Subtype.val '' s) (by simp) := by
  change Graph.sUnion _ (by simp) = _
  congr 1
  simp_rw [← range_comp', coe_toSubgraph]
  exact (image_eq_range Subtype.val s).symm

@[simp]
lemma toSubgraph_iSup (f : ι → G.ClosedSubgraph) :
    toSubgraph (⨆ i, f i) = ⨆ i, toSubgraph (f i) :=
  Subgraph.range_iSup (fun i ↦ f i) ⇑toSubgraph

@[simp]
lemma coe_iSup (f : ι → G.ClosedSubgraph)
    (hf : Pairwise (Compatible on fun i ↦ (f i : Graph α β))) :
    (⨆ i, f i : G.ClosedSubgraph) = Graph.iUnion (fun i ↦ (f i : Graph α β)) hf := by
  simp only [iSup, coe_sSup, ← range_comp']
  rw [Graph.sUnion_range]

@[simp]
lemma vertexSet_sSup (s : Set G.ClosedSubgraph) : V((sSup s).val) = ⋃ a ∈ s, V(a.val) := by
  rw [coe_sSup, sUnion_vertexSet, biUnion_image]

@[simp]
lemma edgeSet_sSup (s : Set G.ClosedSubgraph) : E((sSup s).val) = ⋃ a ∈ s, E(a.val) := by
  rw [coe_sSup, sUnion_edgeSet, biUnion_image]

@[simp]
lemma toSubgraph_iInf (f : ι → G.ClosedSubgraph) : toSubgraph (⨅ i, f i) = ⨅ i, toSubgraph (f i) :=
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

lemma compatible (H₁ H₂ : G.ClosedSubgraph) : H₁.val.Compatible H₂.val :=
  compatible_of_le_le H₁.prop.le H₂.prop.le

@[simp]
lemma coe_eq_induce (H : G.ClosedSubgraph) :
    G[V(H.val)] = H.val := Graph.ext rfl fun e x y =>
  ⟨fun ⟨hl, hx, hy⟩ => by rwa [H.prop.isLink_iff_of_mem hx],
  fun h => ⟨h.of_le H.prop.le, h.left_mem, h.right_mem⟩⟩

lemma ext_vertexSet (h : V(H₁.val) = V(H₂.val)) : H₁ = H₂ := by
  rw [← Subtype.coe_inj, ← H₁.coe_eq_induce, ← H₂.coe_eq_induce, h]

lemma vertexSet_inj : H₁ = H₂ ↔ V(H₁.val) = V(H₂.val) :=
  ⟨(· ▸ rfl), ClosedSubgraph.ext_vertexSet⟩

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
  rw [← Subtype.coe_le_coe, ← H.coe_eq_induce, ← hV, induce_vertexSet_self]
  rfl

@[simp, push]
lemma ne_bot_iff : H ≠ ⊥ ↔ V(H.val).Nonempty := by
  rw [← Graph.ne_bot_iff]
  simp

lemma le_iff_vertexSet_subset : H₁ ≤ H₂ ↔ V(H₁.val) ⊆ V(H₂.val) := by
  rw [← Subtype.coe_le_coe, ← H₁.coe_eq_induce, ← H₂.coe_eq_induce]
  exact induce_mono_right_iff G

lemma lt_iff_vertexSet_ssubset : H₁ < H₂ ↔ V(H₁.val) ⊂ V(H₂.val) := by
  refine ⟨(vertexSet_strictMono G ·), fun h => ?_⟩
  simp [lt_iff_le_and_ne, le_iff_vertexSet_subset.mpr h.subset, vertexSet_inj, h.ne]


@[simp]
lemma compl_vertexSet (H : G.ClosedSubgraph) :
    V((Hᶜ : G.ClosedSubgraph).val) = V(G) \ V(H.val) :=
  vertexDelete_vertexSet G V(H.val)

@[simp]
lemma compl_edgeSet (H : G.ClosedSubgraph) :
    E((Hᶜ : G.ClosedSubgraph).val) = E(G) \ E(H.val) := by
  change E(G - V(H.val)) = E(G) \ E(H.val)
  ext e
  simp only [vertexDelete_edgeSet, mem_setOf_eq, mem_diff, iff_def, forall_exists_index, and_imp]
  refine ⟨fun u v huv hunin hvnin => ⟨huv.edge_mem, ?_⟩, fun he heH => ?_⟩
  · exact fun he => hunin <| huv.of_le_of_mem H.prop.le he |>.left_mem
  · obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    use x, y, hxy
    have hx := H.prop.mem_tfae_of_isLink hxy |>.not.out 0 2
    have hy := H.prop.mem_tfae_of_isLink hxy |>.not.out 1 2
    tauto

@[simp]
lemma compl_isLink (H : G.ClosedSubgraph) :
    Hᶜ.val.IsLink e x y ↔ G.IsLink e x y ∧ e ∉ E(H.val) := by
  change (G - V(H.val)).IsLink e x y ↔ _
  simp only [vertexDelete_isLink_iff, and_congr_right_iff]
  rintro he
  have hx := H.prop.mem_tfae_of_isLink he |>.not.out 0 2
  have hy := H.prop.mem_tfae_of_isLink he |>.not.out 1 2
  tauto

lemma compl_eq_of_stronglyDisjoint_union {H₁ H₂ : Graph α β}
    (hdisj : H₁.StronglyDisjoint H₂) :
    (⟨H₁, hdisj.isClosedSubgraph_union_left⟩ : (H₁ ∪ H₂).ClosedSubgraph)ᶜ =
    ⟨H₂, hdisj.isClosedSubgraph_union_right⟩ := by
  rw [vertexSet_inj]
  simp only [compl_vertexSet, union_vertexSet, union_diff_left, sdiff_eq_left]
  exact hdisj.vertex.symm

lemma isAtom_iff_isCompOf (H : G.ClosedSubgraph) : IsAtom H ↔ H.val.IsCompOf G := by
  simp only [IsAtom, ne_eq, Subtype.forall, bot_isClosedSubgraph, Subtype.mk_eq_bot_iff, IsCompOf,
    Minimal, ← Graph.ne_bot_iff, Subtype.coe_eq_bot_iff, ge_iff_le, and_imp]
  apply and_congr (not_iff_not.mp ?_) <| forall₂_congr fun H' hH'cl => ?_
  · simp [H.prop]
  rw [lt_iff_le_and_ne, ← and_imp, and_comm (a := ¬H' = ⊥), and_imp, and_imp]
  refine imp_congr_right fun hle => ?_
  convert not_imp_not
  · tauto
  simp [le_antisymm_iff, hle]

end ClosedSubgraph

lemma IsClosedSubgraph.eq_induce {H₁ : Graph α β} (hcl : H₁ ≤c G) : H₁ = G[V(H₁)] := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl⟩
  change H₁' = G[V(H₁'.val)]
  exact H₁'.coe_eq_induce.symm

lemma IsClosedSubgraph.vertexSet_inj {H₁ H₂ : Graph α β} (hcl₁ : H₁ ≤c G) (hcl₂ : H₂ ≤c G) :
    H₁ = H₂ ↔ V(H₁) = V(H₂) := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl₁⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hcl₂⟩
  change H₁' = H₂'.val ↔ V(H₁'.val) = V(H₂'.val)
  rw [Subtype.coe_inj]
  exact H₁'.vertexSet_inj

lemma IsClosedSubgraph.eq_ambient_of_subset_vertexSet {H : Graph α β} (hcl : H ≤c G)
    (h : V(G) ⊆ V(H)) : H = G := by
  let H' : G.ClosedSubgraph := ⟨H, hcl⟩
  change H'.val = (⊤ : G.ClosedSubgraph).val
  rw [Subtype.coe_inj]
  exact H'.eq_ambient_of_subset_vertexSet h

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

end Lattice
