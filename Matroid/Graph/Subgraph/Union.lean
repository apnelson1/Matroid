import Matroid.Graph.Subgraph.Compatible

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function Partition

namespace Graph

/-! ### Indexed unions -/

/-- The union of an indexed family of pairwise compatible graphs. -/
@[simps! vertexSet]
protected def iUnion (G : ι → Graph α β) (hG : Pairwise (Graph.Compatible on G)) : Graph α β :=
  mk_of_domp (⨆ i, (G i).Dup) (fun e => (⨆ i, (G i).IsLink e)) <| fun hab hcd => by
    obtain ⟨i, hab⟩ := by simpa using hab
    obtain ⟨j, hcd⟩ := by simpa using hcd
    have := hab.of_compatible (hG.of_refl i j) hcd.edge_mem
    apply ((G j).dup_or_dup_of_isLink_of_isLink this hcd).imp <;> rw [iSup_rel] <;>
    refine fun _ => Relation.TransGen.single ?_ <;> simp only [iSup_apply, iSup_Prop_eq] <;>
    use j

variable {G H : ι → Graph α β} {i j : ι}

instance (hG : Pairwise (Graph.Compatible on G)) [∀ i, Nodup (G i)] :
    Nodup (Graph.iUnion G hG) where
  atomic_dup := by simp

@[simp]
lemma iUnion_vertexSet (hG : Pairwise (Graph.Compatible on G)) :
    V(Graph.iUnion G hG) = ⋃ i, V(G i) := by
  rw [vertexSet_eq, iUnion_dup]
  ext x
  simp [mem_iUnion]

@[simp↓]
lemma iUnion_dup_of_dup_agree (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G hG).Dup x y ↔ ∃ i, (G i).Dup x y := by
  simp only [iUnion_dup, iSup_rel]
  refine ⟨fun h => ?_, fun h =>  Relation.TransGen.single <| by simpa⟩
  induction h with
  | single hxb => simpa using hxb
  | tail h1 h2 IH =>
    simp only [iSup_apply, iSup_Prop_eq] at h2
    obtain ⟨i, h2⟩ := h2
    obtain ⟨j, ih⟩ := IH
    exact ⟨i, (hG'.of_refl j i).trans_right ih h2⟩

lemma dup_le_iUnion (hG : Pairwise (Graph.Compatible on G)) (i : ι) :
    (G i).Dup ≤ (Graph.iUnion G hG).Dup := by
  rw [← rel_le_iff_le]
  intro x y hxy
  simp only [iUnion_dup, iSup_rel]
  apply Relation.TransGen.single
  simp only [iSup_apply, iSup_Prop_eq]
  use i

@[simp]
lemma iUnion_isLink (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).IsLink e x y ↔
    Relation.Domp ((Graph.iUnion G hG).Dup) (⨆ i, (G i).IsLink e) x y := by
  conv_lhs => rw [Graph.iUnion, mk_of_domp_isLink]
  rfl

lemma isLink_le_iUnion (hG : Pairwise (Graph.Compatible on G))
    (hxy : (G i).IsLink e x y) : (Graph.iUnion G hG).IsLink e x y := by
  refine ⟨x, ?_, y, ?_, ?_⟩ <;> simp only [iSup_rel,
    Relation.transClosure_self_iff, iSup_apply, iSup_Prop_eq, Relation.flip_apply] <;> use i
  · exact hxy.left_refl
  · exact symm hxy
  · exact hxy.right_refl

@[simp↓]
lemma iUnion_isLink_of_dup_agree (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G hG).IsLink e x y ↔ ∃ i, (G i).IsLink e x y := by
  refine ⟨fun ⟨a, hxa, b, hlba, hby⟩ => ?_, fun ⟨i, hlxy⟩ => isLink_le_iUnion hG hlxy⟩
  obtain ⟨i, hlba⟩ := by simpa using hlba
  rw [iSup_rel_of_agree_of_mem hG' (vertexSet_eq _ ▸ hlba.left_mem)] at hby
  rw [comm_of ⇑(⨆ i, (G i).Dup),
    iSup_rel_of_agree_of_mem hG' (vertexSet_eq _ ▸ hlba.right_mem)] at hxa
  exact ⟨i, trans' (trans' (symm hxa) hlba.symm) hby⟩

@[simp]
lemma iUnion_edgeSet (hG : Pairwise (Graph.Compatible on G)) :
    E(Graph.iUnion G hG) = ⋃ i, E(G i) := by
  rw [Graph.iUnion, mk_of_domp_edgeSet]
  ext e
  simp +contextual only [Relation.Domp, Relation.Comp, iSup_rel, Relation.flip_apply,
    iSup_apply, iSup_Prop_eq, mem_setOf_eq, mem_iUnion, iff_def, forall_exists_index, and_imp]
  refine ⟨fun a b c hac d i hldc hdb => ⟨i, hldc.edge_mem⟩, fun i hei => ?_⟩
  obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hei
  use y, x, y, ?_, x, ⟨i, hl⟩ <;> simp [Relation.transClosure_self_iff]
  · exact ⟨i, hl.left_refl⟩
  · exact ⟨i, hl.right_refl⟩

protected lemma le_iUnion (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) (i : ι) : G i ≤ Graph.iUnion G hG :=
  le_of (subset_iSup_of_agree hG' i) (fun _ _ _ ↦ isLink_le_iUnion hG)

@[simp]
protected lemma iUnion_le_iff (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) : Graph.iUnion G hG ≤ G₁ ↔ ∀ i, G i ≤ G₁ := by
  refine ⟨fun h i ↦ (Graph.le_iUnion hG hG' i).trans h,
    fun h' ↦ ⟨fun s hs ↦ ?_, fun e x y hl ↦ ?_⟩⟩
  · simp only [iUnion_dup, mem_parts, SetLike.mem_coe] at hs
    obtain ⟨i, hs⟩ := (mem_iSup_iff_of_agree hG').mp hs
    exact h' i |>.dup_subset hs
  obtain ⟨i, hl⟩ := (iUnion_isLink_of_dup_agree hG hG').mp hl
  exact hl.of_le (h' i)

@[simp]
protected lemma iUnion_const [Nonempty ι] (G : Graph α β) :
    Graph.iUnion (fun (_ : ι) ↦ G) (Pairwise.const_of_refl G) = G := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [iUnion_isLink, iUnion_dup, ciSup_const]
  rw [Relation.domp_eq G.Dup (G.IsLink e)]

@[simp]
lemma iUnion_inc_iff (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).Inc e x ↔ ∃ i, (Relation.Comp (G i).Inc (Graph.iUnion G hG).Dup) e x := by
  refine ⟨fun ⟨y, a, hxa, b, hl, hby⟩ => ?_, fun ⟨i, y, ⟨z, hlyz⟩, hyx⟩ => ?_⟩
  · simp only [Relation.flip_apply, iSup_apply, iSup_Prop_eq] at hl
    obtain ⟨i, hl⟩ := hl
    exact ⟨i, a, ⟨b, hl.symm⟩, hxa.symm⟩
  refine ⟨z, y, hyx.symm, z, ?_, (isLink_le_iUnion hG hlyz).right_refl⟩
  simp only [Relation.flip_apply, iSup_apply, iSup_Prop_eq]
  use i, hlyz.symm

@[simp↓]
lemma iUnion_inc_iff_of_dup_agree (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G hG).Inc e x ↔ ∃ i, (G i).Inc e x := by
  simpa [Inc, hG'] using exists_comm

@[simp]
lemma iUnion_isLoopAt_iff (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G hG).IsLoopAt e x ↔ ∃ i, (G i).IsLoopAt e x := by
  simp [← isLink_self_iff, hG']

@[simp]
lemma iUnion_isNonloopAt_iff (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion G hG).IsNonloopAt e x ↔ ∃ i, (G i).IsNonloopAt e x := by
  simp only [IsNonloopAt, hG', ↓iUnion_dup_of_dup_agree, not_exists, ↓iUnion_isLink_of_dup_agree]
  refine ⟨fun ⟨z, hnd, i, hil⟩ => ⟨i, z, hnd i, hil⟩, fun ⟨i, z, hnd, hil⟩ => ⟨z, ?_, i, hil⟩⟩
  exact fun j hj ↦ hnd <| (hG'.of_refl i j).rel_of_right_of_mem (by simpa using hil.left_mem) hj

lemma iUnion_map_le_iUnion (hG : Pairwise (Graph.Compatible on G)) (f : ι' → ι)
    (hG' : Pairwise (Dup_agree on G)) :
    (Graph.iUnion (G ∘ f) (hG.onFun_comp_of_refl f)) ≤ Graph.iUnion G hG := by
  rw [Graph.iUnion_le_iff]
  · exact fun i ↦ Graph.le_iUnion hG hG' (f i)
  apply Pairwise.onFun_of_refl hG'

lemma iUnion_left_le_iUnion_sum {H : ι' → Graph α β}
    (hGH : Pairwise (Graph.Compatible on Sum.elim G H))
    (hGH' : Pairwise (Dup_agree on Sum.elim G H)) :
    Graph.iUnion G hGH.sum_left ≤ Graph.iUnion (Sum.elim G H) hGH := by
  rw [Graph.iUnion_le_iff _ hGH'.sum_left]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH hGH' (Sum.inl i))

lemma iUnion_left_le_iUnion_sum_of_nodup {H : ι' → Graph α β} [∀ i, Nodup (G i)]
    [∀ i, Nodup (H i)] (hGH : Pairwise (Graph.Compatible on Sum.elim G H)) :
    Graph.iUnion G hGH.sum_left ≤ Graph.iUnion (Sum.elim G H) hGH :=
  iUnion_left_le_iUnion_sum hGH (by
    refine @pairwise_dup_agree_of_nodup _ _ _ _ ?_
    rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance)

lemma iUnion_right_le_iUnion_sum {H : ι' → Graph α β}
    (hGH : Pairwise (Graph.Compatible on Sum.elim G H))
    (hGH' : Pairwise (Dup_agree on Sum.elim G H)) :
    Graph.iUnion H hGH.sum_right ≤ Graph.iUnion (Sum.elim G H) hGH := by
  rw [Graph.iUnion_le_iff _ hGH'.sum_right]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH hGH' (Sum.inr i))

-- @[simp]
-- lemma induce_iUnion [Nonempty ι] (hG : Pairwise (Graph.Compatible on G)) (X : Set α) :
--     (Graph.iUnion G hG)[X] = .iUnion (fun i ↦ (G i)[X]) (fun _ _ hij ↦ (hG hij).induce ..) :=
--   Graph.ext (by ext; simp [iUnion_const]) (by simp)

@[simp]
lemma Compatible.vertexDelete_iUnion (hG : Pairwise (Graph.Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) (X : Set α) : (Graph.iUnion G hG) - X =
    .iUnion (fun i ↦ (G i) - X) (fun _ _ hij ↦ (hG hij).vertexDelete) := by
  refine Graph.ext ?_ ?_ <;> simp [iSup_induce_of_agree hG' Xᶜ, hG',
    hG'.mono (fun _ _ ↦ Dup_agree.vertexDelete X)]

@[simp]
lemma Compatible.edgeDelete_iUnion (hG : Pairwise (Graph.Compatible on G))
    (F : Set β) :
    (Graph.iUnion G hG) ＼ F = .iUnion (fun i ↦ (G i) ＼ F) (fun _ _ hij ↦ (hG hij).edgeDelete) := by
  ext <;> simp only [edgeDelete_isLink, iUnion_isLink, Relation.Domp, Relation.Comp, iUnion_dup,
    iSup_rel, Relation.flip_apply, iSup_apply, iSup_Prop_eq, edgeDelete_dup,
    exists_and_right]
  tauto

@[simp]
lemma Compatible.edgeRestrict_iUnion (hG : Pairwise (Graph.Compatible on G))
    (F : Set β) : (Graph.iUnion G hG) ↾ F =
    .iUnion (fun i ↦ (G i) ↾ F) (fun _ _ hij ↦ (hG hij).edgeRestrict) := by
  ext <;> simp only [edgeRestrict_isLink, iUnion_isLink, Relation.Domp, Relation.Comp, iUnion_dup,
    iSup_rel, Relation.flip_apply, iSup_apply, iSup_Prop_eq, edgeRestrict_dup,
    exists_and_left]
  tauto

protected lemma iUnion_comp_le {f : ι' → ι} (hG : Pairwise (Compatible on G))
    (hG' : Pairwise (Dup_agree on G)) :
    Graph.iUnion (fun i ↦ G (f i)) (hG.onFun_comp_of_refl f) ≤ Graph.iUnion G hG := by
  rw [Graph.iUnion_le_iff]
  · exact fun i ↦ Graph.le_iUnion hG hG' (f i)
  exact hG'.onFun_comp_of_refl f

lemma iUnion_comp_eq_of_surj (hG : Pairwise (Compatible on G)) (hG' : Pairwise (Dup_agree on G))
    {f : ι' → ι} (hf : Function.Surjective f) :
    Graph.iUnion G hG = Graph.iUnion (fun i ↦ G (f i)) (hG.onFun_comp_of_refl f) := by
  refine le_antisymm ?_ (Graph.iUnion_comp_le hG hG')
  rw [Graph.iUnion_le_iff hG hG']
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.le_iUnion (hG.onFun_comp_of_refl f) (hG'.onFun_comp_of_refl f) i'

lemma iUnion_range {f : ι' → ι} {G : (Set.range f) → Graph α β}
    (hG : Pairwise (Graph.Compatible on G)) (hG' : Pairwise (Dup_agree on G)) :
    Graph.iUnion G hG = Graph.iUnion (G <| Set.rangeFactorization f ·)
    (hG.onFun_comp_of_refl <| rangeFactorization f) :=
  iUnion_comp_eq_of_surj hG hG' surjective_onto_range

-- nodup lemmas

@[simp]
lemma iUnion_dup_of_nodup (hG : Pairwise (Graph.Compatible on G)) [∀ i, Nodup (G i)] :
    (Graph.iUnion G hG).Dup = Partition.discrete (⋃ i, V(G i)) := by
  simp only [dup_eq_discrete, iUnion_vertexSet]

@[simp↓]
lemma iUnion_isLink_of_nodup (hG : Pairwise (Graph.Compatible on G)) [∀ i, Nodup (G i)] :
    (Graph.iUnion G hG).IsLink e x y ↔ ∃ i, (G i).IsLink e x y :=
  iUnion_isLink_of_dup_agree hG pairwise_dup_agree_of_nodup

protected lemma le_iUnion_of_nodup (hG : Pairwise (Graph.Compatible on G)) [hN : ∀ i, Nodup (G i)]
    (i : ι) : G i ≤ Graph.iUnion G hG := Graph.le_iUnion hG pairwise_dup_agree_of_nodup i

@[simp]
protected lemma iUnion_le_iff_of_nodup (hG : Pairwise (Graph.Compatible on G))
    [hN : ∀ i, Nodup (G i)] : Graph.iUnion G hG ≤ G₁ ↔ ∀ i, G i ≤ G₁ :=
  Graph.iUnion_le_iff hG pairwise_dup_agree_of_nodup

@[simp↓]
lemma iUnion_inc_iff_of_nodup (hG : Pairwise (Graph.Compatible on G)) [hN : ∀ i, Nodup (G i)] :
    (Graph.iUnion G hG).Inc e x ↔ ∃ i, (G i).Inc e x := by simp

@[simp]
lemma iUnion_isLoopAt_iff_of_nodup (hG : Pairwise (Graph.Compatible on G)) [hN : ∀ i, Nodup (G i)] :
    (Graph.iUnion G hG).IsLoopAt e x ↔ ∃ i, (G i).IsLoopAt e x := by simp

@[simp]
lemma iUnion_isNonloopAt_iff_of_nodup (hG : Pairwise (Graph.Compatible on G))
    [hN : ∀ i, Nodup (G i)] :
    (Graph.iUnion G hG).IsNonloopAt e x ↔ ∃ i, (G i).IsNonloopAt e x := by simp

lemma iUnion_map_le_iUnion_of_nodup (hG : Pairwise (Graph.Compatible on G)) (f : ι' → ι)
    [hN : ∀ i, Nodup (G i)] :
    (Graph.iUnion (G ∘ f) (hG.onFun_comp_of_refl f)) ≤ Graph.iUnion G hG :=
  iUnion_map_le_iUnion hG f pairwise_dup_agree_of_nodup

lemma iUnion_right_le_iUnion_sum_of_nodup {H : ι' → Graph α β} [∀ i, Nodup (G i)]
    [∀ i, Nodup (H i)] (hGH : Pairwise (Graph.Compatible on Sum.elim G H)) :
    Graph.iUnion G hGH.sum_left ≤ Graph.iUnion (Sum.elim G H) hGH :=
  iUnion_left_le_iUnion_sum hGH (by
    refine @pairwise_dup_agree_of_nodup _ _ _ _ ?_
    rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> infer_instance)

@[simp]
lemma Compatible.vertexDelete_iUnion_of_nodup (hG : Pairwise (Graph.Compatible on G))
    (X : Set α) [hN : ∀ i, Nodup (G i)] :
    (Graph.iUnion G hG) - X = .iUnion (fun i ↦ (G i) - X) (fun _ _ hij ↦ (hG hij).vertexDelete) :=
  Compatible.vertexDelete_iUnion hG pairwise_dup_agree_of_nodup X

protected lemma iUnion_comp_le_of_nodup {f : ι' → ι} (hG : Pairwise (Compatible on G))
    [hN : ∀ i, Nodup (G i)] :
    Graph.iUnion (fun i ↦ G (f i)) (hG.onFun_comp_of_refl f) ≤ Graph.iUnion G hG :=
  Graph.iUnion_comp_le hG pairwise_dup_agree_of_nodup

lemma iUnion_comp_eq_of_surj_of_nodup {f : ι' → ι} (hG : Pairwise (Compatible on G))
    (hf : Function.Surjective f) [hN : ∀ i, Nodup (G i)] :
    Graph.iUnion G hG = Graph.iUnion (fun i ↦ G (f i)) (hG.onFun_comp_of_refl f) :=
  iUnion_comp_eq_of_surj hG pairwise_dup_agree_of_nodup hf

lemma iUnion_range_of_nodup {f : ι' → ι} {G : (Set.range f) → Graph α β}
    (hG : Pairwise (Graph.Compatible on G)) [hN : ∀ i, Nodup (G i)] :
    Graph.iUnion G hG = Graph.iUnion (G <| Set.rangeFactorization f ·)
    (hG.onFun_comp_of_refl <| rangeFactorization f) :=
  iUnion_comp_eq_of_surj_of_nodup hG surjective_onto_range

/-! ### Set unions -/

variable {s : Set (Graph α β)} {G : Graph α β}

/-- The union of a set of pairwise compatible graphs. -/
@[simps! vertexSet]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β :=
  .iUnion (fun G : s ↦ G.1) hs.subtype

instance (hs : s.Pairwise Compatible) [hN : ∀ (i : s), Nodup i.val] :
    Nodup (Graph.sUnion s hs) := by
  unfold Graph.sUnion
  infer_instance

@[simp]
lemma sUnion_dup (hs : s.Pairwise Compatible) : (Graph.sUnion s hs).Dup = ⨆ i ∈ s, i.Dup := by
  rw [Graph.sUnion, iUnion_dup, iSup_subtype]

@[simp↓]
lemma sUnion_dup_of_dup_agree (hs : s.Pairwise Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s hs).Dup x y ↔ ∃ G ∈ s, G.Dup x y := by
  rw [Graph.sUnion, iUnion_dup_of_dup_agree _ hs'.subtype]
  simp

lemma dup_le_sUnion (hs : s.Pairwise Compatible) (hG : G ∈ s) :
    G.Dup ≤ (Graph.sUnion s hs).Dup := by
  convert dup_le_iUnion _ (⟨G, hG⟩ : s)
  simp

@[simp]
lemma sUnion_isLink (hs : s.Pairwise Graph.Compatible) : (Graph.sUnion s hs).IsLink e x y ↔
    Relation.Domp (Graph.sUnion s hs).Dup (⨆ i ∈ s, i.IsLink e) x y := by
  change Relation.Domp (Graph.sUnion s hs).Dup (⨆ i : s, i.val.IsLink e) x y ↔ _
  rw [iSup_subtype]

lemma isLink_le_sUnion (hs : s.Pairwise Graph.Compatible) (hG : G ∈ s) (hxy : G.IsLink e x y) :
    (Graph.sUnion s hs).IsLink e x y := by
  convert isLink_le_iUnion hs.subtype _
  exact ⟨G, hG⟩
  exact hxy

@[simp↓]
lemma sUnion_isLink_of_dup_agree (hs : s.Pairwise Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s hs).IsLink e x y ↔ ∃ G ∈ s, G.IsLink e x y := by
  rw [Graph.sUnion, iUnion_isLink_of_dup_agree _ hs'.subtype]
  simp

@[simp↓]
lemma sUnion_isLink_of_nodup (hs : s.Pairwise Graph.Compatible) [hN : ∀ (i : s), Nodup i.val] :
    (Graph.sUnion s hs).IsLink e x y ↔ ∃ G ∈ s, G.IsLink e x y := by
  rw [Graph.sUnion, iUnion_isLink_of_nodup]
  simp

@[simp]
lemma sUnion_edgeSet (hs : s.Pairwise Graph.Compatible) :
    E(Graph.sUnion s hs) = ⋃ i : s, E(i.val) := by
  rw [Graph.sUnion, iUnion_edgeSet]

protected lemma le_sUnion (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree)
    (hG : G ∈ s) : G ≤ Graph.sUnion s hs :=
  Graph.le_iUnion (ι := s) _ hs'.subtype ⟨G, hG⟩

@[simp]
protected lemma sUnion_le_iff {H : Graph α β} (hs : s.Pairwise Graph.Compatible)
    (hs' : s.Pairwise Dup_agree) : Graph.sUnion s hs ≤ H ↔ ∀ G ∈ s, G ≤ H := by
  simp [Graph.sUnion, Graph.iUnion_le_iff _ hs'.subtype]

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} (by simp) = G := by
  unfold Graph.sUnion
  convert G.iUnion_const
  · expose_names
    exact x.prop
  infer_instance

@[simp]
lemma sUnion_inc_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).Inc e x ↔ ∃ G ∈ s, (Relation.Comp G.Inc (Graph.sUnion s hs).Dup) e x := by
  simp [Graph.sUnion, iUnion_inc_iff]

@[simp↓]
lemma sUnion_inc_iff_of_dup_agree (hs : s.Pairwise Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s hs).Inc e x ↔ ∃ G ∈ s, G.Inc e x := by
  rw [Graph.sUnion, iUnion_inc_iff_of_dup_agree _ hs'.subtype]
  simp

@[simp]
lemma sUnion_isLoopAt_iff (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s hs).IsLoopAt e x ↔ ∃ G ∈ s, G.IsLoopAt e x := by
  simp [Graph.sUnion, iUnion_isLoopAt_iff _ hs'.subtype]

@[simp]
lemma sUnion_isNonloopAt_iff (hs : s.Pairwise Graph.Compatible) (hs' : s.Pairwise Dup_agree) :
    (Graph.sUnion s hs).IsNonloopAt e x ↔ ∃ G ∈ s, G.IsNonloopAt e x := by
  simp [Graph.sUnion, iUnion_isNonloopAt_iff _ hs'.subtype]

protected lemma sUnion_image {s : Set ι} {f : ι → Graph α β}
    (hs : s.Pairwise (Graph.Compatible on f)) (hs' : s.Pairwise (Dup_agree on f)) :
    Graph.sUnion (f '' s) hs.image = .iUnion (f · : s → _) (Pairwise.restrict.mpr hs) := by
  rw [Graph.sUnion]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  convert Graph.iUnion_comp_eq_of_surj (f := f') _ _ (fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩)
  rintro ⟨_, i, hi, rfl⟩ ⟨_, j, hj, rfl⟩ _
  exact hs'.of_refl hi hj

protected lemma sUnion_range {f : ι → Graph α β} (h : Pairwise (Graph.Compatible on f))
    (h' : Pairwise (Dup_agree on f)) :
    Graph.sUnion (Set.range f) h.range_pairwise = .iUnion f h := by
  unfold Graph.sUnion
  convert Graph.iUnion_comp_eq_of_surj (f := Set.rangeFactorization f) _ _ surjective_onto_range
  rintro ⟨_, i, _, rfl⟩ ⟨_, j, _, rfl⟩ _
  exact h'.of_refl i j

-- vertexDelete? edgeDelete? edgeRestrict?

/-! ### Unions of pairs -/

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.
If `G` and `H` are `Compatible`, this doesn't occur.
We define this in terms of `sUnion` and `Graph.copy` so the vertex and edge sets are
definitionally unions. -/
protected def union (G H : Graph α β) : Graph α β :=
  Graph.sUnion {G, H ＼ E(G)} pairwise_compatible_edgeDelete

instance : Union (Graph α β) where union := Graph.union

variable {G H : Graph α β}

instance [Nodup G] [Nodup H] : ∀ (i : Set.Elem {G, H ＼ E(G)}), i.val.Nodup := by
  rintro ⟨G', rfl | rfl⟩ <;> infer_instance

instance [Nodup G] [Nodup H] : Nodup (G ∪ H) := by
  change Nodup (Graph.sUnion {G, H ＼ E(G)} pairwise_compatible_edgeDelete)
  convert instNodupSUnionOfValMemSet _
  rintro ⟨G', (rfl | rfl)⟩ <;> infer_instance

lemma union_eq_sUnion (G H : Graph α β) :
    G ∪ H = Graph.sUnion {G, H ＼ E(G)} pairwise_compatible_edgeDelete := rfl

@[simp]
lemma union_vertexSet (G H : Graph α β) : V(G ∪ H) = V(G) ∪ V(H) := by
  simp [union_eq_sUnion]

@[simp]
lemma union_dup : (G ∪ H).Dup = G.Dup ⊔ H.Dup := by
  rw [← H.edgeDelete_dup E(G), union_eq_sUnion, ← iSup_pair, sUnion_dup]

@[simp] lemma left_le_union_dup : ⇑G.Dup ≤ (G ∪ H).Dup := by
  rw [rel_le_iff_le]
  simp

@[simp]
lemma right_edgeDelete_le_union_dup : ⇑(H ＼ E(G)).Dup ≤ (G ∪ H).Dup := by
  rw [rel_le_iff_le]
  simp

@[simp]
lemma Dup_agree.union_dup (hG' : G.Dup_agree H) :
    (G ∪ H).Dup x y ↔ G.Dup x y ∨ H.Dup x y := by
  rw [union_eq_sUnion, sUnion_dup_of_dup_agree _ (by simp [hG'])]
  simp

@[simp]
lemma union_isLink : (G ∪ H).IsLink e x y ↔
    Relation.Domp (G ∪ H).Dup (fun x y => G.IsLink e x y ∨ H.IsLink e x y ∧ e ∉ E(G)) x y := by
  have : (⨆ i ∈ ({G, H ＼ E(G)} : Set (Graph α β)), i.IsLink e) =
      fun x y => G.IsLink e x y ∨ H.IsLink e x y ∧ e ∉ E(G) := by
    ext x y
    simp
  rw [union_eq_sUnion, sUnion_isLink, this]

lemma IsLink.le_union_left (hxy : G.IsLink e x y) : (G ∪ H).IsLink e x y :=
  G.isLink_le_sUnion pairwise_compatible_edgeDelete (mem_insert G {H ＼ E(G)}) hxy

@[simp↓]
lemma Dup_agree.union_isLink (hG' : G.Dup_agree H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y ∧ e ∉ E(G) := by
  rw [union_eq_sUnion, sUnion_isLink_of_dup_agree _ (by simp [hG'])]
  simp

lemma Dup_agree.isLink_or_isLink_of_union (hG' : G.Dup_agree H) (h : (G ∪ H).IsLink e x y) :
    G.IsLink e x y ∨ H.IsLink e x y := by
  rw [hG'.union_isLink] at h
  tauto

@[simp]
lemma Dup_agree.union_isLink_of_mem_left (hG' : G.Dup_agree H)
    (he : e ∈ E(G)) : (G ∪ H).IsLink e x y ↔ G.IsLink e x y := by
  simp [hG', he]

@[simp]
lemma union_edgeSet : E(G ∪ H) = E(G) ∪ E(H) := by
  simp [union_eq_sUnion]

@[simp]
protected lemma Dup_agree.left_le_union (hG' : G.Dup_agree H) : G ≤ G ∪ H :=
  Graph.le_sUnion pairwise_compatible_edgeDelete (pairwise_dup_agree_edgeDelete hG')
    (mem_insert G {H ＼ E(G)})

@[simp]
lemma Dup_agree.right_edgeDelete_le_union (hG' : G.Dup_agree H) : H ＼ E(G) ≤ G ∪ H :=
  Graph.le_sUnion pairwise_compatible_edgeDelete (pairwise_dup_agree_edgeDelete hG')
    (mem_insert_of_mem _ (mem_singleton_iff.2 rfl))

@[simp]
lemma union_inc_iff : (G ∪ H).Inc e x ↔ ∃ u, (G.Inc e u ∨ (H.Inc e u ∧ e ∉ E(G))) ∧
    (G.Dup ⊔ H.Dup) x u := by
  rw [union_eq_sUnion, sUnion_inc_iff, ← union_eq_sUnion, union_dup]
  constructor
  · rintro ⟨G', (rfl | rfl), y, hiy, hyx⟩
    · exact ⟨y, Or.inl hiy, hyx.symm⟩
    rw [edgeDelete_inc_iff] at hiy
    exact ⟨y, Or.inr hiy, hyx.symm⟩
  rintro ⟨y, (hi | hi), hxy⟩
  · exact ⟨G, by simp, y, hi, hxy.symm⟩
  refine ⟨H ＼ E(G), by simp, y, ?_, hxy.symm⟩
  rwa [edgeDelete_inc_iff]

@[simp↓]
lemma Dup_agree.union_inc_iff (hG' : G.Dup_agree H) :
    (G ∪ H).Inc e x ↔ G.Inc e x ∨ (H.Inc e x ∧ e ∉ E(G)) := by
  rw [union_eq_sUnion, sUnion_inc_iff_of_dup_agree _ <| pairwise_dup_agree_edgeDelete hG']
  simp

lemma Dup_agree.union_isLoopAt_iff (hG' : G.Dup_agree H) :
    (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ (H.IsLoopAt e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion, sUnion_isLoopAt_iff _ (pairwise_dup_agree_edgeDelete hG')]

lemma Dup_agree.union_isNonloopAt_iff (hG' : G.Dup_agree H) :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ (H.IsNonloopAt e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion, sUnion_isNonloopAt_iff _ (pairwise_dup_agree_edgeDelete hG')]

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) := by
  simp [union_eq_sUnion, union_eq_sUnion]

protected lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  rw [union_eq_sUnion, Graph.sUnion_le_iff]
  · simp [h₁, edgeDelete_le.trans h₂]
  exact pairwise_dup_agree_edgeDelete <| dup_agree_of_le_le h₁ h₂

lemma Dup_agree.union_le_iff {H₁ H₂ : Graph α β} (h : H₁.Dup_agree H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ＼ E(H₁) ≤ G := by
  simp [union_eq_sUnion, Graph.sUnion_le_iff _ (pairwise_dup_agree_edgeDelete h)]

lemma Dup_agree.union_mono_right (h : G.Dup_agree H₂) (hle : H₁ ≤ H₂) : G ∪ H₁ ≤ G ∪ H₂ := by
  rw [union_eq_sUnion, Graph.sUnion_le_iff]
  · simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, h.left_le_union,
    forall_eq, true_and]
    exact le_trans (edgeDelete_mono_left hle) h.right_edgeDelete_le_union
  exact pairwise_dup_agree_edgeDelete <| h.mono_right hle

@[simp]
protected lemma union_self (G : Graph α β) : G ∪ G = G :=
  (Graph.union_le le_rfl le_rfl).antisymm <| dup_agree_rfl.left_le_union

-- protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
--   have dup_assoc : (G₁ ∪ G₂ ∪ G₃).Dup = (G₁ ∪ (G₂ ∪ G₃)).Dup := by simp [sup_assoc]
--   refine Graph.ext dup_assoc fun e x y ↦ ?_
--   simp_rw [union_isLink, dup_assoc]
--   refine ⟨fun ⟨a, hxa, b, h, hby⟩ => ?_, fun ⟨a, hxa, b, h, hby⟩ => ?_⟩
--   · obtain ⟨c, hbc, d, hdc, hda⟩ := h
--     refine ⟨d, ?_, c, ?_, ?_⟩
--     · rw [← dup_assoc]
--       exact trans_of (G₁ ∪ G₂ ∪ G₃).Dup (dup_assoc ▸ hxa) <| symm <| left_le_union_dup _ _ hda
--     swap
--     · rw [← dup_assoc]
--       exact trans_of (G₁ ∪ G₂ ∪ G₃).Dup (symm <| left_le_union_dup _ _ hbc) (dup_assoc ▸ hby)
--     simp only [Relation.flip_apply, union_dup, sup_rel] at hdc ⊢
--     refine hdc.imp IsLink.symm (fun ⟨hl₂dc, he⟩ => ⟨?_, he⟩)
--     · use b
--       sorry
--     sorry

--   sorry

lemma Compatible.union_isLink (h : G.Compatible H) :
    (G ∪ H).IsLink e x y ↔ Relation.Domp (G ∪ H).Dup (G.IsLink e ⊔ H.IsLink e) x y := by
  by_cases heG : e ∈ E(G)
  · have hl : G.IsLink e ⊔ H.IsLink e = G.IsLink e := by
      ext x y
      simp only [Pi.sup_apply, sup_Prop_eq, or_iff_left_iff_imp]
      exact (·.of_compatible h.symm heG)
    simp [heG, hl]
  have hl : G.IsLink e ⊔ H.IsLink e = H.IsLink e := by
    ext x y
    simp only [Pi.sup_apply, sup_Prop_eq, or_iff_right_iff_imp]
    exact fun hl => (heG hl.edge_mem).elim
  simp [hl, heG]

lemma Compatible.isLink_le_union_right (h : G.Compatible H) (hxy : H.IsLink e x y) :
    (G ∪ H).IsLink e x y := by
  simp only [h.union_isLink, union_dup, sup_rel]
  use x, Relation.TransGen.single ?_, y, ?_, Relation.TransGen.single ?_
  · simp [hxy.left_refl]
  swap
  · simp [hxy.right_refl]
  simp [hxy]

@[simp↓]
lemma Compatible.union_isLink_of_mem_right (hG : G.Compatible H) (hG' : G.Dup_agree H)
    (he : e ∈ E(H)) : (G ∪ H).IsLink e x y ↔ H.IsLink e x y := by
  simp only [hG', ↓Dup_agree.union_isLink]
  by_cases heG : e ∈ E(G)
  · simp +contextual [hG.isLink_eq heG he]
  simp [heG]

@[simp↓]
lemma Compatible.union_isLink_of_agree (hG : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).IsLink e = (G.IsLink e ⊔ H.IsLink e) := by
  ext x y
  simp only [hG', ↓Dup_agree.union_isLink, Pi.sup_apply, sup_Prop_eq]
  by_cases heG : e ∈ E(G)
  · simp +contextual [heG, (IsLink.of_compatible · hG.symm heG)]
  simp [heG]

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_isLink]
  simp only [edgeRestrict_isLink, mem_union, union_dup, edgeRestrict_dup, le_refl, sup_of_le_left]
  refine ⟨fun ⟨he, hl⟩ => ?_, fun ⟨a, hxa, b, hl, hby⟩ => ?_⟩
  · refine ⟨x, hl.left_refl, y, ?_, hl.right_refl⟩
    simpa [hl.symm]
  simp only [Relation.flip_apply, Pi.sup_apply, edgeRestrict_isLink, sup_Prop_eq] at hl
  obtain ⟨he, hl⟩ | ⟨he, hl⟩ := hl
  · use Or.inl he, (hl.symm.dup_left hxa.symm).dup_right hby
  · use Or.inr he, (hl.symm.dup_left hxa.symm).dup_right hby

@[simp↓]
lemma Compatible.union_eq_sUnion (h : G.Compatible H) :
    G ∪ H = Graph.sUnion {G, H} (by simp [Set.pairwise_iff_of_refl, h, h.symm]) :=
  have : (G ∪ H).Dup =
    (Graph.sUnion {G, H} (by simp [Set.pairwise_iff_of_refl, h, h.symm])).Dup := by
    rw [union_dup, sUnion_dup, ← iSup_pair]
  Graph.ext this fun e x y ↦ by rw [h.union_isLink, sUnion_isLink, this, iSup_pair]

@[simp↓]
lemma Compatible.union_inc_iff (h : G.Compatible H) :
    (G ∪ H).Inc e x ↔ ∃ u, (G.Inc e u ∨ H.Inc e u) ∧ (G.Dup ⊔ H.Dup) x u := by
  rw [Graph.union_inc_iff]
  refine exists_congr fun u ↦ and_congr_left fun _ ↦ ?_
  by_cases heG : e ∈ E(G)
  · simp only [heG, not_true_eq_false, and_false, or_false, iff_self_or]
    exact (·.of_compatible h.symm heG)
  simp [heG]

@[simp↓]
lemma Compatible.union_inc_iff_of_agree (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).Inc e x ↔ G.Inc e x ∨ H.Inc e x := by
  simp only [hG', ↓Dup_agree.union_inc_iff]
  by_cases heG : e ∈ E(G)
  · simp only [heG, not_true_eq_false, and_false, or_false, iff_self_or]
    exact (·.of_compatible h.symm heG)
  simp [heG]

@[simp↓]
lemma Compatible.union_isLoopAt_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ H.IsLoopAt e x := by
  simp only [hG', ↓Dup_agree.union_isLoopAt_iff]
  by_cases heG : e ∈ E(G)
  · simp only [heG, not_true_eq_false, and_false, or_false, iff_self_or]
    exact (·.of_compatible h.symm heG)
  simp [heG]

@[simp↓]
lemma Compatible.union_isNonloopAt_iff (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ H.IsNonloopAt e x := by
  simp only [hG', ↓Dup_agree.union_isNonloopAt_iff]
  by_cases heG : e ∈ E(G)
  · simp only [heG, not_true_eq_false, and_false, or_false, iff_self_or]
    refine fun ⟨y, hxy, hl⟩ ↦ ⟨y, ?_, hl.of_compatible h.symm heG⟩
    contrapose! hxy
    exact hG'.rel_of_left_of_mem (vertexSet_eq _ ▸ hl.left_mem) hxy
  simp [heG]

@[simp↓]
lemma Compatible.union_adj_iff (h : G.Compatible H) :
    (G ∪ H).Adj = (Relation.Domp (G ∪ H).Dup G.Adj) ⊔ (Relation.Domp (G ∪ H).Dup H.Adj) := by
  unfold Adj
  ext x y
  simp only [h.union_isLink, union_dup, Pi.sup_apply, sup_Prop_eq]
  refine ⟨fun ⟨e, a, hxa, b, hl, hby⟩ =>
    hl.imp (⟨a, hxa, b, ⟨e, ·⟩, hby⟩) (⟨a, hxa, b, ⟨e, ·⟩, hby⟩), ?_⟩
  rintro (⟨a, hxa, b, ⟨e, hl⟩, hby⟩ | ⟨a, hxa, b, ⟨e, hl⟩, hby⟩)
  · exact ⟨e, a, hxa, b, Or.inl hl, hby⟩
  · exact ⟨e, a, hxa, b, Or.inr hl, hby⟩

@[simp↓]
lemma Compatible.union_adj_iff_of_agree (h : G.Compatible H) (hG' : G.Dup_agree H) :
    (G ∪ H).Adj x y ↔ G.Adj x y ∨ H.Adj x y := by
  unfold Adj
  simp_rw [h.union_isLink_of_agree hG']
  refine ⟨fun ⟨e, h⟩ => h.imp (⟨e, ·⟩) (⟨e, ·⟩), ?_⟩
  rintro (⟨e, hl⟩ | ⟨e, hl⟩)
  · exact ⟨e, Or.inl hl⟩
  · exact ⟨e, Or.inr hl⟩

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G := by
  simp_rw [h.union_eq_sUnion, h.symm.union_eq_sUnion, Set.pair_comm]

@[simp↓]
lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂)
    (hG' : H₁.Dup_agree H₂) : H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G := by
  rw [h_compat.union_eq_sUnion, Graph.sUnion_le_iff]; swap
  · rintro G' (rfl | rfl) H' (rfl | rfl) _ <;> simp [hG', hG'.symm]
  simp

@[simp]
lemma Compatible.right_le_union (hG : G.Compatible H) (hG' : G.Dup_agree H) : H ≤ G ∪ H := by
  simp [hG.union_comm, hG'.symm.left_le_union]

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (Graph.union_le hle rfl.le).antisymm <| compatible_of_le hle |>.right_le_union
    <| dup_agree_of_le hle

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (compatible_of_le hle).union_comm ▸ union_eq_self_of_le_left hle

lemma Compatible.union_mono_left (h : G.Compatible H₂) (h' : G.Dup_agree H₂) (hle : H₁ ≤ H₂) :
    H₁ ∪ G ≤ H₂ ∪ G := by
  rw [← h.union_comm, ← (h.mono_right hle).union_comm]
  exact h'.union_mono_right hle

lemma Compatible.union_mono (h : G₂.Compatible H₁) (h' : G₂.Dup_agree H₂) (hleG : G₁ ≤ G₂)
    (hleH : H₁ ≤ H₂) : G₁ ∪ H₁ ≤ G₂ ∪ H₂ :=
  (h.symm.union_mono_left (h'.mono_right hleH).symm hleG).trans <| h'.union_mono_right hleH

lemma edgeRestrict_union_edgeDelete (G : Graph α β) (F : Set β) :
    (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α β) (F : Set β) :
    (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Compatible.union_comm]
  apply G.compatible_of_le_le (by simp) (by simp)

-- lemma induce_union_edgeDelete (G : Graph α β) (hX : X ⊆ V(G)) : G[X] ∪ (G ＼ E(G[X])) = G := by
--   rw [← union_eq_union_edgeDelete, union_eq_self_of_le_left (induce_le hX)]

-- lemma edgeDelete_union_induce (G : Graph α β) (hX : X ⊆ V(G)) : (G ＼ E(G[X])) ∪ G[X] = G := by
--   rw [(Compatible.of_disjoint_edgeSet _).union_comm, induce_union_edgeDelete _ hX]
--   simp [disjoint_sdiff_left]

-- lemma Compatible.union_eq_iUnion (h : G.Compatible H) :
--     G ∪ H = Graph.iUnion (fun b ↦ bif b then G else H) (by simpa [pairwise_on_bool]) := by
--   generalize_proofs h'
--   simp only [le_antisymm_iff, h.union_le_iff, Graph.iUnion_le_iff, Bool.forall_bool, cond_false,
--     h.right_le_union, cond_true, Graph.left_le_union, and_self, and_true]
--   exact ⟨Graph.le_iUnion h' true, Graph.le_iUnion h' false⟩

-- lemma Compatible.induce_union (h : G.Compatible H) (X : Set α) : (G ∪ H)[X] = G[X] ∪ H[X] := by
--   refine Graph.ext (by simp) fun e x y ↦ ?_
--   simp only [induce_isLink_iff, h.union_isLink_iff, h.induce.union_isLink_iff]
--   tauto

-- lemma Compatible.vertexDelete_union (h : G.Compatible H) (X : Set α) :
--     (G ∪ H) - X = (G - X) ∪ (H - X) := by
--   simp only [h.union_eq_iUnion, vertexDelete_iUnion, Bool.apply_cond (f := fun G ↦ G - X),
--     ← h.vertexDelete.union_eq_iUnion]

-- lemma induce_union (G : Graph α β) (X Y : Set α) (hX : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
--     G [X ∪ Y] = G [X] ∪ G [Y] := by
--   refine Graph.ext rfl fun e x y ↦ ?_
--   simp only [induce_isLink_iff, mem_union, Compatible.induce_induce.union_isLink_iff]
--   by_cases hxy : G.IsLink e x y
--   · by_cases hx : x ∈ X
--     · simp [hx, show y ∉ Y from fun hy ↦ hX x hx y hy hxy.adj]
--     by_cases hy : y ∈ X
--     · simp [hy, show x ∉ Y from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
--     simp [hx, hy]
--   simp [hxy]
