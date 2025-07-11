import Matroid.Graph.Operations.Union
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic

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
    · simp [hG]
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

instance {G : Graph α β} : CoeOut G.Subgraph (Graph α β) where
  coe H := H.1

@[simp]
lemma Subgraph.le (H : G.Subgraph) : H.1 ≤ G :=
  H.2

instance : PartialOrder G.Subgraph := inferInstanceAs (PartialOrder {H // H ≤ G})

@[simp]
lemma Subgraph.mk_le_iff {H₀ : Graph α β} {hH₀ : H₀ ≤ G} {H : G.Subgraph} :
    (⟨H₀, hH₀⟩ : G.Subgraph) ≤ H ↔ H₀ ≤ H.1 := Iff.rfl

@[simp]
lemma Subgraph.le_mk_iff {H₀ : Graph α β} {hH₀ : H₀ ≤ G} {H : G.Subgraph} :
    H ≤ (⟨H₀, hH₀⟩ : G.Subgraph) ↔ H.1 ≤ H₀ := Iff.rfl

@[simp]
lemma Subgraph.pairwise_compatible (H : ι → G.Subgraph) :
    Pairwise (Compatible on (fun i ↦ (H i : Graph α β))) :=
  G.pairwise_compatible_of_subgraph (fun i ↦ (H i).2)

@[simp]
lemma Subgraph.set_pairwise_compatible (s : Set G.Subgraph) :
    ((((↑) : _ → Graph α β) '' s).Pairwise Compatible) :=
  G.set_pairwise_compatible_of_subgraph (by rintro _ ⟨H, -, rfl⟩; exact H.2)

/-- The proof that the subgraphs of a graph `G` form a completely distributive lattice. -/
def Subgraph.minAx : CompletelyDistribLattice.MinimalAxioms G.Subgraph where
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
    Graph.sInter_le ..⟩
  sInf_le s H h := by
    generalize_proofs h₁
    exact Graph.sInter_le <| by simp [h]
  le_sInf s H h := by simpa using fun K h' hK ↦ h _ hK
  top := ⟨G, le_rfl⟩
  bot := ⟨Graph.noEdge ∅ β, by simp⟩
  le_top H := H.2
  bot_le := by simp
  iInf_iSup_eq {ι κ} f := by
    simp_rw [iInf, iSup]
    rw [Subtype.mk_eq_mk]; swap; simp
    refine le_antisymm ?_ ?_
    · refine ⟨fun x hx ↦ ?_, fun e x y ↦ ?_⟩
      · suffices x ∈ V(G) ∧ ∃ (g : (a : ι) → κ a), ∀ (i : ι), x ∈ V((f i (g i)).1) by simpa
        have hx' : x ∈ V(G) ∧ ∀ (i : ι), ∃ (j : κ i), x ∈ V((f i j).1) := by simpa using hx
        choose g hg using hx'.2
        exact ⟨hx'.1, g, hg⟩
      suffices G.IsLink e x y → (∀ (i : ι), ∃ (j : κ i), ((f i j).1.IsLink e x y)) →
        ∃ (g : (i : ι) → κ i), ∀ (i : ι), (f i (g i)).1.IsLink e x y by simpa +contextual
      intro hexy h
      choose g hg using h
      exact ⟨_, hg⟩
    simp only [Graph.le_sInter_iff, mem_insert_iff, mem_image, mem_range, exists_exists_eq_and,
      Graph.sUnion_le_iff, forall_exists_index, forall_apply_eq_imp_iff, forall_eq_or_imp]
    refine ⟨fun _ ↦ Graph.sInter_le (by simp), fun i g ↦ ?_⟩
    exact (Graph.sInter_le (G := (f i (g i)).1) (by simp)).trans (Graph.le_sUnion _ (by simp))

/-- The subgraphs of a graph `G` form a completely distributive lattice.-/
instance : CompletelyDistribLattice G.Subgraph :=
  CompletelyDistribLattice.ofMinimalAxioms Subgraph.minAx

@[simp]
lemma Subgraph.coe_top : ((⊤ : G.Subgraph) : Graph α β) = G := rfl

@[simp]
lemma Subgraph.coe_bot : ((⊥ : G.Subgraph) : Graph α β) = ⊥ := rfl

lemma Subgraph.coe_iInf (H : ι → G.Subgraph) :
    (⨅ i, H i : G.Subgraph) = Graph.iInter (Option.elim · G (H ·)) := by
  change Graph.sInter _ (by simp) = _
  rw [← range_comp', iInter_option_eq_sInter_insert]

@[simp]
lemma Subgraph.iInf_of_isEmpty [IsEmpty ι] (H : ι → G.Subgraph) :
    (⨅ i, H i : G.Subgraph) = G := by
  simp [_root_.iInf_of_isEmpty ..]

@[simp]
lemma Subgraph.coe_iInf_of_nonempty [Nonempty ι] (H : ι → G.Subgraph) :
    (⨅ i, H i : G.Subgraph) = Graph.iInter (fun i ↦ (H i : Graph α β)) := by
  simp only [le_antisymm_iff, le_iInter_iff, Subtype.coe_le_coe, iInf_le, implies_true, true_and]
  refine (Graph.le_sInter_iff (by simp)).2 ?_
  simp only [mem_insert_iff, mem_image, mem_range, exists_exists_eq_and, forall_eq_or_imp,
    forall_exists_index, forall_apply_eq_imp_iff]
  exact ⟨(Graph.iInter_le (Classical.arbitrary ι)).trans (by simp), fun i ↦ Graph.iInter_le i⟩

lemma Subgraph.coe_sInf (s : Set G.Subgraph) :
    ((sInf s : G.Subgraph) : Graph α β) = Graph.sInter (insert G <| (↑) '' s) (by simp) := rfl

lemma Subgraph.coe_sInf_of_nonempty (s : Set G.Subgraph) (hs : s.Nonempty) :
    ((sInf s : G.Subgraph) : Graph α β) = Graph.sInter ((↑) '' s) (by simpa) := by
  change Graph.sInter _ (by simp) = _
  rw [le_antisymm_iff]
  simp only [Graph.le_sInter_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    forall_exists_index, mem_insert_iff, forall_eq_or_imp]
  obtain ⟨⟨K, hKG⟩, hK⟩ := hs
  exact ⟨fun H hHG hHs ↦ Graph.sInter_le (by simp [hHG, hHs]),
    (Graph.sInter_le (by simp [hKG, hK])).trans hKG,
    fun H hHG hHs ↦ Graph.sInter_le (by simp [hHs, hHG])⟩

lemma Subgraph.coe_sInf_of_empty : ((sInf ∅ : G.Subgraph) : Graph α β) = G := by simp

@[simp]
lemma Subgraph.coe_iSup (H : ι → G.Subgraph) :
    (⨆ i, H i : G.Subgraph) = Graph.iUnion (fun i ↦ (H i : Graph α β)) (by simp) := by
  change Graph.sUnion _ (by simp) = _
  rw [le_antisymm_iff]
  simp only [Graph.sUnion_le_iff, mem_image, mem_range, exists_exists_eq_and, forall_exists_index,
    forall_apply_eq_imp_iff, Graph.iUnion_le_iff]
  exact ⟨Graph.le_iUnion (G := fun i ↦ (H i).1) (by simp), fun h ↦ Graph.le_sUnion _ (by simp)⟩

@[simp]
lemma Subgraph.coe_sSup (s : Set G.Subgraph) :
    ((sSup s : G.Subgraph) : Graph α β) = Graph.sUnion ((↑) '' s) (by simp) := rfl

@[simp]
lemma Subgraph.coe_sup (H₁ H₂ : G.Subgraph) : ((H₁ ⊔ H₂ : G.Subgraph) : Graph α β) = H₁.1 ∪ H₂.1 :=
  rfl

@[simp]
lemma Subgraph.coe_inf (H₁ H₂ : G.Subgraph) : ((H₁ ⊓ H₂ : G.Subgraph) : Graph α β) = H₁.1 ∩ H₂.1 :=
  rfl

@[simp]
lemma Subgraph.range_iSup (f : ι' → ι) (H : ι → G.Subgraph) :
    (⨆ (i : Set.range f), H i : G.Subgraph) = ⨆ i, H (f i) := by
  apply_fun Subtype.val using Subtype.val_injective
  simp only [coe_iSup]
  exact Graph.iUnion_range _

@[simp]
lemma Subgraph.range_iInf (f : ι' → ι) (H : ι → G.Subgraph) :
    (⨅ (i : Set.range f), H i : G.Subgraph) = ⨅ i, H (f i) := by
  apply_fun Subtype.val using Subtype.val_injective
  obtain hι | hι := isEmpty_or_nonempty ι'
  · have : IsEmpty ↑(range f) := by simpa
    simp
  · simp [Graph.iInter_range]

@[simp]
lemma Subgraph.compatible (H₁ H₂ : G.Subgraph) : H₁.val.Compatible H₂.val :=
  compatible_of_le_le H₁.prop H₂.prop

lemma Subgraph.disjoint_iff (H₁ H₂ : G.Subgraph) :
    Disjoint H₁ H₂ ↔ H₁.val.StronglyDisjoint H₂.val := by
  rw [_root_.disjoint_iff, ← Subtype.coe_inj, coe_inf, coe_bot, ← disjoint_iff_inter_eq_bot,
    stronglyDisjoint_iff_disjoint_of_compatible (H₁.compatible H₂)]

def Subgraph.of_le {H : Graph α β} (H' : H.Subgraph) (hle : H ≤ G) : G.Subgraph :=
  ⟨H', H'.le.trans hle⟩

@[simp]
lemma Subgraph.coe_of_le {H : Graph α β} (H' : H.Subgraph) (hle : H ≤ G) :
    (H'.of_le hle : Graph α β) = H' := rfl


@[reducible] def ClosedSubgraph (G : Graph α β) := {H // H ≤c G}

variable {G : Graph α β} {H H₁ H₂ : G.ClosedSubgraph} {s : Set G.ClosedSubgraph}

instance : PartialOrder G.ClosedSubgraph := inferInstanceAs (PartialOrder {H // H ≤c G})

/-- The order embedding from closed subgraphs to subgraphs -/
def ClosedSubgraph.toSubgraph : G.ClosedSubgraph ↪o G.Subgraph :=
  Subtype.orderEmbedding fun _ ↦ IsClosedSubgraph.le

instance {G : Graph α β} : CoeOut G.ClosedSubgraph (Graph α β) where
  coe H := H.1

instance : Lattice G.ClosedSubgraph where
  sup H₁ H₂ := ⟨H₁ ∪ H₂, H₁.2.union H₂.2⟩
  le_sup_left _ _ := Graph.left_le_union ..
  le_sup_right H H' := (compatible_of_le_le H.2.le H'.2.le).right_le_union
  sup_le _ _ _ := Graph.union_le
  inf H₁ H₂ := ⟨H₁ ∩ H₂, H₁.2.inter H₂.2⟩
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter

@[simp]
lemma ClosedSubgraph.mk_le_iff {H₀ : Graph α β} {hH₀ : H₀ ≤c G} {H : G.ClosedSubgraph} :
    (⟨H₀, hH₀⟩ : G.ClosedSubgraph) ≤ H ↔ H₀ ≤ H.1 := Iff.rfl

@[simp]
lemma ClosedSubgraph.le_mk_iff {H₀ : Graph α β} {hH₀ : H₀ ≤c G} {H : G.ClosedSubgraph} :
    H ≤ (⟨H₀, hH₀⟩ : G.ClosedSubgraph) ↔ H.1 ≤ H₀ := Iff.rfl

lemma ClosedSubgraph.coe_le_coe {H₀ H : G.ClosedSubgraph} : H₀.1 ≤ H.1 ↔ H₀ ≤ H := Iff.rfl

lemma ClosedSubgraph.coe_lt_coe {H₀ H : G.ClosedSubgraph} : H₀.1 < H.1 ↔ H₀ < H := Iff.rfl

lemma ClosedSubgraph.toSubgraph_le_toSubgraph {H₁ H₂ : G.ClosedSubgraph} :
    H₁.toSubgraph ≤ H₂.toSubgraph ↔ H₁ ≤ H₂ := Iff.rfl

lemma ClosedSubgraph.toSubgraph_lt_toSubgraph {H₁ H₂ : G.ClosedSubgraph} :
    H₁.toSubgraph < H₂.toSubgraph ↔ H₁ < H₂ := Iff.rfl

@[simp]
lemma ClosedSubgraph.coe_sup (H₁ H₂ : G.ClosedSubgraph) :
    ((H₁ ⊔ H₂ : G.ClosedSubgraph) : Graph α β) = H₁.1 ∪ H₂.1 := rfl

@[simp]
lemma ClosedSubgraph.coe_inf (H₁ H₂ : G.ClosedSubgraph) :
    ((H₁ ⊓ H₂ : G.ClosedSubgraph) : Graph α β) = H₁.1 ∩ H₂.1 :=
  rfl

@[simp]
lemma ClosedSubgraph.pairwise_compatible (H : ι → G.ClosedSubgraph) :
    Pairwise (Compatible on (fun i ↦ (H i : Graph α β))) :=
  G.pairwise_compatible_of_subgraph (fun i ↦ (H i).2.le)

@[simp]
lemma ClosedSubgraph.set_pairwise_compatible (s : Set G.ClosedSubgraph) :
    ((((↑) : _ → Graph α β) '' s).Pairwise Compatible) :=
  G.set_pairwise_compatible_of_subgraph (by rintro _ ⟨H, -, rfl⟩; exact H.2.le)

@[simp]
lemma ClosedSubgraph.coe_toSubgraph (H : G.ClosedSubgraph) : (H.toSubgraph : Graph α β) = H := rfl

@[simp]
lemma ClosedSubgraph.coe_comp_toSubgraph : (Subtype.val ∘ toSubgraph : G.ClosedSubgraph → _) =
    (↑) := rfl

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
    exact iInter_isClosedSubgraph (by simp +contextual [IsClosedSubgraph.le])⟩
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
lemma ClosedSubgraph.coe_top : ((⊤ : G.ClosedSubgraph) : Graph α β) = G := rfl

@[simp]
lemma ClosedSubgraph.coe_bot : ((⊥ : G.ClosedSubgraph) : Graph α β) = ⊥ := rfl

@[simp]
lemma ClosedSubgraph.toSubgraph_sSup (s : Set G.ClosedSubgraph) :
    toSubgraph (sSup s) = ⨆ (H : s), toSubgraph H.1 := rfl

@[simp]
lemma ClosedSubgraph.coe_sSup (s : Set G.ClosedSubgraph) :
    ((sSup s : G.ClosedSubgraph) : Graph α β) =
    Graph.sUnion (Subtype.val '' s) (by simp) := by
  change Graph.sUnion _ (by simp) = _
  congr
  simp_rw [← range_comp', coe_toSubgraph]
  exact (image_eq_range Subtype.val s).symm

@[simp]
lemma ClosedSubgraph.toSubgraph_iSup (f : ι → G.ClosedSubgraph) :
    toSubgraph (⨆ i, f i) = ⨆ i, toSubgraph (f i) :=
  Subgraph.range_iSup (fun i ↦ f i) ⇑toSubgraph

@[simp]
lemma ClosedSubgraph.coe_iSup (f : ι → G.ClosedSubgraph)
    (hf : Pairwise (Compatible on fun i ↦ (f i : Graph α β))) :
    (⨆ i, f i : G.ClosedSubgraph) = Graph.iUnion (fun i ↦ (f i : Graph α β)) hf := by
  simp only [iSup, coe_sSup, ← range_comp']
  rw [Graph.sUnion_range]

@[simp]
lemma ClosedSubgraph.vertexSet_sSup (s : Set G.ClosedSubgraph) :
    V((sSup s).val) = ⋃ a ∈ s, V(a.val) := by
  simp only [coe_sSup, sUnion_vertexSet, mem_insert_iff, iUnion_iUnion_eq_or_left, biUnion_image]

@[simp]
lemma ClosedSubgraph.edgeSet_sSup (s : Set G.ClosedSubgraph) :
    E((sSup s).val) = ⋃ a ∈ s, E(a.val) := by
  simp only [coe_sSup, sUnion_edgeSet, mem_insert_iff, iUnion_iUnion_eq_or_left, biUnion_image]

@[simp]
lemma ClosedSubgraph.toSubgraph_iInf (f : ι → G.ClosedSubgraph) :
    toSubgraph (⨅ i, f i) = ⨅ i, toSubgraph (f i) :=
  Subgraph.range_iInf (fun i ↦ f i) ⇑toSubgraph

@[simp]
lemma ClosedSubgraph.coe_iInf_of_nonempty [Nonempty ι] (f : ι → G.ClosedSubgraph) :
    (⨅ i, f i : G.ClosedSubgraph) = Graph.iInter (fun i ↦ (f i : Graph α β)) := by
  simp only [le_antisymm_iff, le_iInter_iff, Subtype.coe_le_coe, iInf_le, implies_true, true_and]
  refine (Graph.le_sInter_iff (by simp)).2 ?_
  simp only [mem_insert_iff, mem_image, mem_range, exists_exists_eq_and, forall_eq_or_imp,
    forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨(Graph.iInter_le (Classical.arbitrary ι)).trans ((f _).prop.le), fun i ↦ ?_⟩
  obtain ⟨_, i, rfl⟩ := i
  exact Graph.iInter_le i

@[simp]
lemma ClosedSubgraph.coe_iInf_of_empty [IsEmpty ι] (f : ι → G.ClosedSubgraph) :
    ((⨅ i, f i : G.ClosedSubgraph) : Graph α β) = G := by
  simp [_root_.iInf_of_isEmpty ..]

@[simp]
lemma ClosedSubgraph.toSubgraph_sInf (s : Set G.ClosedSubgraph) :
    toSubgraph (sInf s) = sInf (toSubgraph '' s) := by
  change iInf _ = _
  rw [sInf_image]
  exact iInf_subtype'' s ⇑toSubgraph

@[simp]
lemma ClosedSubgraph.coe_sInf (s : Set G.ClosedSubgraph) :
    ((sInf s : G.ClosedSubgraph) : Graph α β) =
    Graph.sInter (insert G (Subtype.val '' s)) (by simp) := by
  change Graph.sInter _ (by simp) = _
  congr
  simp_rw [← range_comp', coe_toSubgraph]
  exact (image_eq_range Subtype.val s).symm

@[simp]
lemma ClosedSubgraph.coe_sInf_of_nonempty (hs : s.Nonempty):
    ((sInf s : G.ClosedSubgraph) : Graph α β) = Graph.sInter (Subtype.val '' s) (by simpa) := by
  rw [← coe_toSubgraph, toSubgraph_sInf, Subgraph.coe_sInf_of_nonempty _ (by simpa)]
  congr
  rw [← image_comp, coe_comp_toSubgraph]

@[simp]
lemma ClosedSubgraph.coe_sInf_of_empty : ((sInf ∅ : G.ClosedSubgraph) : Graph α β) = G := by simp

lemma ClosedSubgraph.vertexSet_sInf_comm (s : Set G.ClosedSubgraph) :
    V((sInf s).val) = V(G) ∩ ⋂ a ∈ s, V(a.val) := by
  simp only [coe_sInf, sInter_vertexSet, mem_insert_iff, iInter_iInter_eq_or_left, biInter_image]

@[simp]
lemma ClosedSubgraph.vertexSet_sInf_comm_of_nonempty (hs : s.Nonempty) :
    V((sInf s).val) = ⋂ a ∈ s, V(a.val) := by
  simp only [coe_sInf_of_nonempty hs, sInter_vertexSet, biInter_image]

instance : CompleteAtomicBooleanAlgebra G.ClosedSubgraph where
  iInf_iSup_eq {ι κ} f := by
    apply_fun ClosedSubgraph.toSubgraph using ClosedSubgraph.toSubgraph.injective
    simp only [ClosedSubgraph.toSubgraph_iInf, ClosedSubgraph.toSubgraph_iSup]
    exact CompletelyDistribLattice.iInf_iSup_eq (fun a b ↦ ClosedSubgraph.toSubgraph (f a b))

lemma ClosedSubgraph.compatible (H₁ H₂ : G.ClosedSubgraph) : H₁.val.Compatible H₂.val :=
  compatible_of_le_le H₁.prop.le H₂.prop.le

@[simp]
lemma ClosedSubgraph.coe_eq_induce (H : G.ClosedSubgraph) :
    G[V(H.val)] = H.val := Graph.ext rfl fun e x y =>
  ⟨fun ⟨hl, hx, hy⟩ => by rwa [H.prop.isLink_iff_of_mem hx],
  fun h => ⟨h.of_le H.prop.le, h.left_mem, h.right_mem⟩⟩

lemma IsClosedSubgraph.eq_induce {H₁ : Graph α β} (hcl : H₁ ≤c G) : H₁ = G[V(H₁)] := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl⟩
  change H₁' = G[V(H₁'.val)]
  exact H₁'.coe_eq_induce.symm

lemma ClosedSubgraph.ext_vertexSet (h : V(H₁.val) = V(H₂.val)) : H₁ = H₂ := by
  rw [← Subtype.coe_inj, ← H₁.coe_eq_induce, ← H₂.coe_eq_induce, h]

lemma ClosedSubgraph.vertexSet_inj : H₁ = H₂ ↔ V(H₁.val) = V(H₂.val) :=
  ⟨(· ▸ rfl), ClosedSubgraph.ext_vertexSet⟩

lemma IsClosedSubgraph.vertexSet_inj {H₁ H₂ : Graph α β} (hcl₁ : H₁ ≤c G) (hcl₂ : H₂ ≤c G) :
    H₁ = H₂ ↔ V(H₁) = V(H₂) := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hcl₁⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hcl₂⟩
  change H₁' = H₂'.val ↔ V(H₁'.val) = V(H₂'.val)
  rw [Subtype.coe_inj]
  exact H₁'.vertexSet_inj

lemma ClosedSubgraph.vertexSet_injective : Injective (V(·.val) : G.ClosedSubgraph → Set α) :=
  fun _ _ => vertexSet_inj.mpr

lemma ClosedSubgraph.vertexSet_strictMono (G : Graph α β) :
    StrictMono (V(·.val) : G.ClosedSubgraph → Set α) := fun H₁ H₂ hlt => by
  rw [lt_iff_le_and_ne, ← vertexSet_inj.ne]
  exact ⟨vertexSet_mono hlt.le, hlt.ne⟩

lemma ClosedSubgraph.disjoint_iff (H₁ H₂ : G.ClosedSubgraph) :
    Disjoint H₁ H₂ ↔ H₁.val.StronglyDisjoint H₂.val := by
  rw [_root_.disjoint_iff, ← Subtype.coe_inj, coe_inf, coe_bot, ← disjoint_iff_inter_eq_bot,
    stronglyDisjoint_iff_disjoint_of_compatible (H₁.compatible H₂)]

lemma ClosedSubgraph.disjoint_iff_vertexSet_disjoint :
    Disjoint H₁ H₂ ↔ Disjoint V(H₁.val) V(H₂.val) := by
  rw [ClosedSubgraph.disjoint_iff, (H₁.compatible H₂).disjoint_iff_vertexSet_disjoint]

lemma ClosedSubgraph.disjoint_iff_val_disjoint (H₁ H₂ : G.ClosedSubgraph) :
    Disjoint H₁ H₂ ↔ Disjoint H₁.val H₂.val := by
  rw [H₁.disjoint_iff_vertexSet_disjoint, Graph.disjoint_iff_vertexSet_disjoint]

@[simp]
lemma ClosedSubgraph.eq_ambient_of_subset_vertexSet (h : V(G) ⊆ V(H.val)) : H = ⊤ := by
  have hV : V(G) = V(H.val) := subset_antisymm h (vertexSet_mono H.prop.le)
  refine le_antisymm le_top ?_
  rw [← Subtype.coe_le_coe, ← H.coe_eq_induce, ← hV, induce_vertexSet_self]
  rfl

lemma IsClosedSubgraph.eq_ambient_of_subset_vertexSet {H : Graph α β} (hcl : H ≤c G)
    (h : V(G) ⊆ V(H)) : H = G := by
  let H' : G.ClosedSubgraph := ⟨H, hcl⟩
  change H'.val = (⊤ : G.ClosedSubgraph).val
  rw [Subtype.coe_inj]
  exact H'.eq_ambient_of_subset_vertexSet h

lemma ClosedSubgraph.le_iff_vertexSet_subset : H₁ ≤ H₂ ↔ V(H₁.val) ⊆ V(H₂.val) := by
  rw [← Subtype.coe_le_coe, ← H₁.coe_eq_induce, ← H₂.coe_eq_induce]
  exact induce_mono_right_iff G

lemma ClosedSubgraph.lt_iff_vertexSet_ssubset : H₁ < H₂ ↔ V(H₁.val) ⊂ V(H₂.val) := by
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
lemma ClosedSubgraph.compl_vertexSet (H : G.ClosedSubgraph) :
    V((Hᶜ : G.ClosedSubgraph).val) = V(G) \ V(H.val) :=
  vertexDelete_vertexSet G V(H.val)

@[simp]
lemma ClosedSubgraph.compl_edgeSet (H : G.ClosedSubgraph) :
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
lemma ClosedSubgraph.compl_isLink (H : G.ClosedSubgraph) :
    Hᶜ.val.IsLink e x y ↔ G.IsLink e x y ∧ e ∉ E(H.val) := by
  change (G - V(H.val)).IsLink e x y ↔ _
  simp only [vertexDelete_isLink_iff, and_congr_right_iff]
  rintro he
  have hx := H.prop.mem_tfae_of_isLink he |>.not.out 0 2
  have hy := H.prop.mem_tfae_of_isLink he |>.not.out 1 2
  tauto

lemma ClosedSubgraph.compl_eq_of_stronglyDisjoint_union {H₁ H₂ : Graph α β}
    (hdisj : H₁.StronglyDisjoint H₂) :
    (⟨H₁, hdisj.isClosedSubgraph_union_left⟩ : (H₁ ∪ H₂).ClosedSubgraph)ᶜ =
    ⟨H₂, hdisj.isClosedSubgraph_union_right⟩ := by
  rw [vertexSet_inj]
  simp only [compl_vertexSet, union_vertexSet, union_diff_left, sdiff_eq_left]
  exact hdisj.vertex.symm

lemma ClosedSubgraph.isAtom_iff_isCompOf (H : G.ClosedSubgraph) :
    IsAtom H ↔ H.val.IsCompOf G := by
  simp only [IsAtom, ne_eq, Subtype.forall, bot_isClosedSubgraph, Subtype.mk_eq_bot_iff, IsCompOf,
    Minimal, vertexSet_nonempty_iff, Subtype.coe_eq_bot_iff, ge_iff_le, and_imp]
  apply and_congr (not_iff_not.mp ?_) <| forall₂_congr fun H' hH'cl => ?_
  · simp [not_nonempty_iff_eq_empty, H.prop]
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
