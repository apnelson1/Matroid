import Matroid.Graph.Subgraph.Defs

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)} {Gι Hι : ι → Graph α β}

open Set Function

/- For Mathlib -/

@[simp]
lemma Option.elim_eq_const_of_isEmpty {α : Type*} [hα : IsEmpty α] (f : α → β) (b : β) :
    (Option.elim · b f) = fun _ ↦ b :=
  funext fun a ↦ match a with
  | none => rfl
  | some a => hα.elim a

instance {ι : Type*} {r : α → α → Prop} [Std.Refl r] {f : ι → α} : Std.Refl (r on f) where
  refl i := refl (f i)

open scoped Sym2

namespace Graph

/-! ### Compatibility -/
section CompatibleAt

-- This is not transitive.

lemma compatibleAt_symmetric : Symmetric (CompatibleAt e (α := α)) := fun _ _ ↦ CompatibleAt.symm

lemma CompatibleAt.isLink_iff (h : CompatibleAt e G H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y := by
  rw [h heG heH]

lemma compatibleAt_of_notMem_left (he : e ∉ E(G)) : CompatibleAt e G H := by
  simp [CompatibleAt, he]

lemma compatibleAt_of_notMem_right (he : e ∉ E(H)) : CompatibleAt e G H := by
  simp [CompatibleAt, he]

lemma CompatibleAt.induce_left (h : CompatibleAt e G H) (X : Set α) : CompatibleAt e G[X] H := by
  rintro ⟨x, y, ⟨he, hx, hy⟩⟩ heH
  ext z w
  rw [← h he.edge_mem heH, induce_isLink, he.isLink_iff]
  aesop

lemma CompatibleAt.induce_right (h : CompatibleAt e G H) (X : Set α) : CompatibleAt e G H[X] :=
  (h.symm.induce_left X).symm

@[gcongr]
lemma CompatibleAt.induce (h : CompatibleAt e G H) (X : Set α) : CompatibleAt e G[X] H[X] :=
  (h.induce_left X).induce_right X

end CompatibleAt

section Compatible

@[simp]
lemma compatible_symmetric : Symmetric (@Compatible α β) :=
  fun _ _ ↦ Compatible.symm

lemma compatible_comm : G.Compatible H ↔ H.Compatible G :=
  ⟨Compatible.symm, Compatible.symm⟩

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ :=
  ((isLink_eqOn_of_le h₁).mono inter_subset_left).trans <|
    (isLink_eqOn_of_le h₂).symm.mono inter_subset_right

lemma compatible_of_forall_map_le (h : ∀ i, Gι i ≤ G) : Pairwise (Compatible on Gι) := by
  rintro i j -
  exact compatible_of_le_le (h i) (h j)

lemma compatible_of_forall_mem_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) : s.Pairwise Compatible := by
  rintro _ hi _ hj _
  exact compatible_of_le_le (h hi) (h hj)

lemma compatible_of_le (h : H ≤ G) : H.Compatible G := compatible_of_le_le h le_rfl

lemma Inc.of_compatible (h : G.Inc e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

lemma IsLoopAt.of_compatible (h : G.IsLoopAt e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLoopAt e x := IsLink.of_compatible h hGH heH

lemma IsNonloopAt.of_compatible (h : G.IsNonloopAt e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsNonloopAt e x := by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

lemma Compatible.pair (h : G.Compatible H) : ({G, H} : Set (Graph α β)).Pairwise Compatible := by
  rw [pairwise_pair]
  exact fun _ ↦ ⟨h, h.symm⟩

lemma Compatible.mono_left {G₀ : Graph α β} (h : Compatible G H) (hG₀ : G₀ ≤ G) :
    Compatible G₀ H :=
  ((isLink_eqOn_of_le hG₀).mono inter_subset_left).trans
    (h.mono (inter_subset_inter_left _ (edgeSet_mono hG₀)))

lemma Compatible.mono_right {H₀ : Graph α β} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α β} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ :=
  (h.mono_left hG).mono_right hH

lemma Compatible.induce_left (h : Compatible G H) (X : Set α) : G[X].Compatible H := by
  intro e ⟨heG, heX⟩
  ext x y
  obtain ⟨u, v, heuv : G.IsLink e u v, hu, hv⟩ := heG
  simp only [induce_isLink, ← h ⟨heuv.edge_mem, heX⟩, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (X : Set α) : G.Compatible H[X] :=
  (h.symm.induce_left X).symm

@[gcongr]
lemma Compatible.induce (h : Compatible G H) : G[X].Compatible H[X] :=
  (h.induce_left X).induce_right X

@[gcongr]
lemma Compatible.vertexDelete (h : Compatible G H) : (G - X).Compatible (H - X) :=
  h.mono vertexDelete_le vertexDelete_le

@[gcongr]
lemma Compatible.edgeDelete (h : Compatible G H) : (G ＼ F).Compatible (H ＼ F) :=
  h.mono edgeDelete_le edgeDelete_le

@[gcongr]
lemma Compatible.edgeRestrict (h : Compatible G H) : (G ↾ F).Compatible (H ↾ F) :=
  h.mono edgeRestrict_le edgeRestrict_le

@[simp, gcongr]
lemma Compatible.induce_induce : G[X].Compatible G[Y] :=
  Compatible.induce_left (Compatible.induce_right G.compatible_self _) _

lemma Compatible.stronglyDisjoint_of_vertexSet_disjoint (h : G.Compatible H)
    (hV : Disjoint V(G) V(H)) : G.StronglyDisjoint H := by
  refine ⟨hV, disjoint_left.2 fun e he he' ↦ ?_⟩
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet he
  exact hV.notMem_of_mem_left hexy.left_mem (h ⟨he, he'⟩ ▸ hexy).left_mem

lemma Compatible.disjoint_iff_vertexSet_disjoint (h : G.Compatible H) :
    G.StronglyDisjoint H ↔ Disjoint V(G) V(H) :=
  ⟨(·.vertex), h.stronglyDisjoint_of_vertexSet_disjoint⟩

lemma StronglyDisjoint.compatible (h : G.StronglyDisjoint H) : G.Compatible H :=
  Compatible.of_disjoint_edgeSet h.edge

lemma Compatible.edgeSet_disjoint_of_vertexSet_disjoint (h : G.Compatible H)
    (hV : Disjoint V(G) V(H)) : Disjoint E(G) E(H) := by
  by_contra he
  obtain ⟨e, heG, heH⟩ := not_disjoint_iff.mp he
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet heG
  exact hV.notMem_of_mem_left hexy.left_mem <| hexy.of_compatible h heH |>.left_mem

lemma stronglyDisjoint_iff_vertexSet_disjoint_compatible :
    G.StronglyDisjoint H ↔ Disjoint V(G) V(H) ∧ G.Compatible H :=
  ⟨fun h => ⟨h.vertex, h.compatible⟩,
    fun ⟨hdisj, hco⟩ => ⟨hdisj, hco.edgeSet_disjoint_of_vertexSet_disjoint hdisj⟩⟩

@[deprecated "Pairwise.const_of_refl" (since := "2025-07-30")]
lemma pairwise_compatible_const (G : Graph α β) : Pairwise (Compatible on fun (_ : ι) ↦ G) := by
  simp [Pairwise]

@[deprecated "Pairwise.onFun_comp_of_refl" (since := "2025-07-30")]
lemma pairwise_compatible_comp {ι ι' : Type*} {G : ι → Graph α β} (hG : Pairwise (Compatible on G))
    (f : ι' → ι): Pairwise (Compatible on (G ∘ f)) := by
  rw [onFun_comp]
  exact Pairwise.onFun_of_refl hG _

/-- useful with `Pairwise` and `Set.Pairwise`.-/
@[simp]
lemma stronglyDisjoint_le_compatible : @StronglyDisjoint α β ≤ Compatible :=
  fun _ _ ↦ StronglyDisjoint.compatible

end Compatible
end Graph
