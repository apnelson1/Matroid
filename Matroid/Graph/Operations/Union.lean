import Matroid.Graph.Constructions.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function

/- For Mathlib -/

@[simp]
lemma Option.elim_eq_const_of_isEmpty {α : Type*} [hα : IsEmpty α] (f : α → β) (b : β) :
    (Option.elim · b f) = fun _ ↦ b :=
  funext fun a ↦ match a with
  | none => rfl
  | some a => hα.elim a

@[simp]
lemma Set.iInter_diff_distrib {ι α : Type*} [Nonempty ι] {G : ι → Set α} {X : Set α} :
    (⋂ i, G i) \ X = ⋂ i, (G i) \ X := by
  ext x
  simp +contextual only [mem_diff, mem_iInter, iff_def, not_false_eq_true, and_self, implies_true,
    true_and]
  exact fun a ↦ notMem_of_mem_diff (a <| Classical.arbitrary ι)

@[simp]
lemma Set.biInter_diff_distrib {ι α : Type*} {s : Set ι} (hs : s.Nonempty) {G : ι → Set α}
    {X : Set α} : (⋂ i ∈ s, G i) \ X = ⋂ i ∈ s, G i \ X := by
  ext x
  simp +contextual only [mem_diff, mem_iInter, iff_def, not_false_eq_true, and_self, implies_true,
    true_and]
  exact fun h ↦ (h _ hs.some_mem).2

@[simp]
lemma Set.sInter_diff_distrib {α : Type*} {s : Set (Set α)} (hs : s.Nonempty) {X : Set α} :
    ⋂₀ s \ X = ⋂₀ ((· \ X) '' s) := by
  ext x
  simp +contextual only [mem_diff, mem_sInter, sInter_image, mem_iInter, iff_def, not_false_eq_true,
    and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).2

lemma Pairwise.of_refl {ι α : Type*} {r : α → α → Prop} [IsRefl α r] {f : ι → α}
    (h : Pairwise (r on f)) (i j : ι) : r (f i) (f j) :=
  (eq_or_ne i j).elim (fun hij ↦ hij ▸ refl (f i)) fun hne ↦ h hne

lemma Pairwise.true_of_refl {r : α → α → Prop} {x y : α} [IsRefl α r] (hr : Pairwise r) :
    r x y := by
  by_cases hf : x = y
  · exact hf ▸ refl x
  · exact hr hf

lemma true_pairwise : Pairwise (⊤ : α → α → _) := by tauto

lemma Pairwise.iff_top_of_refl {r : α → α → Prop} [IsRefl α r] : Pairwise r ↔ r = ⊤ := by
  refine ⟨fun hr ↦ ?_, ?_⟩
  · ext x y
    simp [hr.true_of_refl]
  · rintro rfl
    exact fun ⦃i j⦄ a ↦ trivial

lemma Pairwise.iff_true_of_refl {r : α → α → Prop} [IsRefl α r] : Pairwise r ↔ ∀ x y, r x y := by
  rw [iff_top_of_refl]
  aesop

lemma Function.onFun_comp {α β γ : Type*} {r : α → α → Prop} {f : β → α} {g : γ → β} :
    (r on f ∘ g) = ((r on f) on g) := rfl

-- lemma Function.onFun_top {α β : Type*} {f : β → α} : ((⊤ : α → α → Prop) on f) = ⊤ := rfl

lemma Pairwise.onFun_of_refl {ι α : Type*} {r : α → α → Prop} [IsRefl α r] {f : ι → α}
    (hr : Pairwise r) : Pairwise (r on f) := by
  rintro i j hne
  rw [Pairwise.iff_top_of_refl] at hr
  subst r
  trivial

lemma Set.Pairwise.range_of_injective {ι α : Type*} {r : α → α → Prop} {f : ι → α}
    (hf : Function.Injective f) : Pairwise (r on f) ↔ (range f).Pairwise r := by
  refine ⟨fun h ↦ ?_, fun h i j hne ↦ @h (f i) ⟨i, rfl⟩ (f j) ⟨j, rfl⟩ <| fun a ↦ hne (hf a)⟩
  rintro _ ⟨i, _, rfl⟩ _ ⟨j, _, rfl⟩ hne
  exact h fun a ↦ hne (congrArg f a)

lemma Pairwise.restrict {ι α : Type*} {r : α → α → Prop} {f : ι → α} {s : Set ι} :
    Pairwise (r on (f · : s → α)) ↔ s.Pairwise (r on f) :=
  ⟨fun h i his j hjs hne ↦ @h ⟨i, his⟩ ⟨j, hjs⟩ (by simpa),
  fun h i j hne ↦ h i.prop j.prop (by rwa [Subtype.coe_ne_coe])⟩

lemma Pairwise.sum_left {ι ι' γ : Type*} {G : ι → γ} {H : ι' → γ} {r : γ → γ → Prop}
    (h : Pairwise (r on Sum.elim G H)) : Pairwise (r on G) := by
  rw [← Sum.elim_comp_inl G H, onFun_comp]
  exact h.comp_of_injective Sum.inl_injective

lemma Pairwise.sum_right {ι ι' γ : Type*} {G : ι → γ} {H : ι' → γ} {r : γ → γ → Prop}
    (h : Pairwise (r on Sum.elim G H)) : Pairwise (r on H) := by
  rw [← Sum.elim_comp_inr G H, onFun_comp]
  exact h.comp_of_injective Sum.inr_injective

instance {ι α : Type*} {r : α → α → Prop} [IsRefl α r] {f : ι → α} : IsRefl ι (r on f) where
  refl i := refl (f i)

open scoped Sym2

namespace Graph

/-! ### Strongly disjointness -/

/-- Two graphs are strongly disjoint if their edge sets and vertex sets are disjoint.
    This is a stronger notion of disjointness than `Disjoint`,
    see `disjoint_iff_vertexSet_disjoint`. -/
@[mk_iff]
structure StronglyDisjoint (G H : Graph α β) : Prop where
  vertex : Disjoint V(G) V(H)
  edge : Disjoint E(G) E(H)

lemma StronglyDisjoint.symm (h : G.StronglyDisjoint H) : H.StronglyDisjoint G :=
  ⟨h.1.symm, h.2.symm⟩

lemma StronglyDisjoint_iff_of_le_le (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) :
    StronglyDisjoint H₁ H₂ ↔ Disjoint V(H₁) V(H₂) := by
  refine ⟨StronglyDisjoint.vertex, fun h ↦ ⟨h, disjoint_left.2 fun e he₁ he₂ ↦ ?_⟩⟩
  obtain ⟨x, y, he₁⟩ := exists_isLink_of_mem_edgeSet he₁
  exact h.notMem_of_mem_left he₁.left_mem ((he₁.of_le h₁).of_le_of_mem h₂ he₂).left_mem

lemma StronglyDisjoint.disjoint (h : G.StronglyDisjoint H) : Disjoint G H := by
  rintro H' hH'G hH'H
  rw [le_bot_iff, ← vertexSet_eq_empty_iff]
  have := le_inf (vertexSet_mono hH'G) <| vertexSet_mono hH'H
  rwa [h.vertex.eq_bot, le_bot_iff] at this

/-! ### Compatibility -/

def CompatibleAt (e : β) (G H : Graph α β) : Prop := e ∈ E(G) → e ∈ E(H) → G.IsLink e = H.IsLink e

lemma compatibleAt_def :
    CompatibleAt e G H ↔ (e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y) := by
  simp [CompatibleAt, funext_iff]

lemma CompatibleAt.symm (h : CompatibleAt e G H) : CompatibleAt e H G :=
  fun he1 he2 ↦ (h he2 he1).symm

lemma CompatibleAt.comm : CompatibleAt e G H ↔ CompatibleAt e H G :=
  ⟨CompatibleAt.symm, CompatibleAt.symm⟩

lemma compatibleAt_self : CompatibleAt e G G := fun _ _ ↦ rfl

instance {e : β} : IsRefl (Graph α β) (CompatibleAt e) := ⟨fun _ _ _ ↦ rfl⟩

instance {e : β} : IsSymm (Graph α β) (CompatibleAt e) := ⟨fun _ _ ↦ CompatibleAt.symm⟩

-- This is not transitive.

lemma compatibleAt_symmetric : Symmetric (CompatibleAt e (α := α)) := fun _ _ ↦ CompatibleAt.symm

lemma CompatibleAt.isLink_iff (h : CompatibleAt e G H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y := by
  rw [h heG heH]

lemma compatibleAt_of_notMem_left (he : e ∉ E(G)) : CompatibleAt e G H := by
  simp [CompatibleAt, he]

lemma compatibleAt_of_notMem_right (he : e ∉ E(H)) : CompatibleAt e G H := by
  simp [CompatibleAt, he]

lemma IsLink.compatibleAt_iff_left (hIsLink : G.IsLink e x y) :
    CompatibleAt e G H ↔ (e ∈ E(H) → H.IsLink e x y) :=
  ⟨fun h heH ↦ by rwa [← CompatibleAt.isLink_iff h hIsLink.edge_mem heH], fun h heG heH ↦
  (isLink_eq_isLink_iff_exists_isLink_of_mem_edgeSet heG).mpr ⟨x, y, hIsLink, h heH⟩⟩

lemma IsLink.compatibleAt_iff_right (h : H.IsLink e x y) :
    CompatibleAt e G H ↔ (e ∈ E(G) → G.IsLink e x y) := by
  rw [CompatibleAt.comm]
  exact compatibleAt_iff_left h

lemma IsLink.of_compatibleAt (he : G.IsLink e x y) (h : CompatibleAt e G H) (heH : e ∈ E(H)) :
    H.IsLink e x y := (he.compatibleAt_iff_left).mp h heH

lemma CompatibleAt.mono_left {G₀ : Graph α β} (h : CompatibleAt e G H) (hle : G₀ ≤ G) :
    CompatibleAt e G₀ H :=
  compatibleAt_def.2 fun heG₀ heH _ _ ↦ ⟨fun h' ↦ (h'.of_le hle).of_compatibleAt h heH,
    fun h' ↦ (h'.of_compatibleAt h.symm (edgeSet_mono hle heG₀)).of_le_of_mem hle heG₀⟩

lemma CompatibleAt.mono_right {H₀ : Graph α β} (h : CompatibleAt e G H) (hH₀ : H₀ ≤ H) :
    CompatibleAt e G H₀ :=
  (h.symm.mono_left hH₀).symm

lemma CompatibleAt.mono {G₀ H₀ : Graph α β} (h : CompatibleAt e G H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    CompatibleAt e G₀ H₀ :=
  (h.mono_left hG).mono_right hH

lemma CompatibleAt.induce_left (h : CompatibleAt e G H) (X : Set α) : CompatibleAt e G[X] H := by
  rintro ⟨x, y, ⟨he, hx, hy⟩⟩ heH
  ext z w
  rw [← h he.edge_mem heH, induce_isLink_iff, he.isLink_iff]
  aesop

lemma CompatibleAt.induce_right (h : CompatibleAt e G H) (X : Set α) :
    CompatibleAt e G H[X] :=
  (h.symm.induce_left X).symm

lemma CompatibleAt.induce (h : CompatibleAt e G H) {X : Set α} : CompatibleAt e G[X] H[X] :=
  (h.induce_left X).induce_right X

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := EqOn G.IsLink H.IsLink (E(G) ∩ E(H))

lemma Compatible.isLink_eq (h : G.Compatible H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e = H.IsLink e :=
  h ⟨heG, heH⟩

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G := by
  rwa [Compatible, inter_comm, eqOn_comm]

instance : IsSymm (Graph α β) Compatible where
  symm _ _ := Compatible.symm

@[simp]
lemma compatible_symmetric : Symmetric (@Compatible α β) :=
  fun _ _ ↦ Compatible.symm

lemma compatible_comm : G.Compatible H ↔ H.Compatible G :=
  ⟨Compatible.symm, Compatible.symm⟩

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ :=
  ((isLink_eqOn_of_le h₁).mono inter_subset_left).trans <|
    (isLink_eqOn_of_le h₂).symm.mono inter_subset_right

lemma compatible_of_le (h : H ≤ G) : H.Compatible G := compatible_of_le_le h le_rfl

lemma IsLink.of_compatible (h : G.IsLink e x y) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLink e x y := by
  rwa [← hGH ⟨h.edge_mem, heH⟩]

@[simp]
lemma compatible_self (G : Graph α β) : G.Compatible G :=
  eqOn_refl ..

instance : IsRefl (Graph α β) Compatible where
  refl G := G.compatible_self

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H := by
  simp [Compatible, h.inter_eq]

@[simp]
lemma compatible_edgeDelete_right : G.Compatible (H ＼ E(G)) :=
  Compatible.of_disjoint_edgeSet disjoint_sdiff_right

/-- Used to simplify the definition of the union of a pair. -/
@[simp]
lemma pairwise_compatible_edgeDelete : ({G, H ＼ E(G)} : Set (Graph α β)).Pairwise Compatible := by
  simp [pairwise_iff_of_refl, compatible_edgeDelete_right.symm]

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
  simp only [induce_isLink_iff, ← h ⟨heuv.edge_mem, heX⟩, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.dup_and_dup_or_dup_and_dup heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (X : Set α) :
    G.Compatible H[X] :=
  (h.symm.induce_left X).symm

lemma Compatible.induce (h : Compatible G H) {X : Set α} : G[X].Compatible H[X] :=
  (h.induce_left X).induce_right X

lemma Compatible.vertexDelete (h : Compatible G H) {X : Set α} : (G - X).Compatible (H - X) :=
  h.mono vertexDelete_le vertexDelete_le

lemma Compatible.edgeDelete (h : Compatible G H) {F : Set β} : (G ＼ F).Compatible (H ＼ F) :=
  h.mono edgeDelete_le edgeDelete_le

lemma Compatible.edgeRestrict (h : Compatible G H) {F : Set β} : (G ↾ F).Compatible (H ↾ F) :=
  h.mono edgeRestrict_le edgeRestrict_le

@[simp]
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

lemma pairwise_compatible_const (G : Graph α β) : Pairwise (Compatible on fun (_ : ι) ↦ G) := by
  simp [Pairwise]

lemma pairwise_compatible_comp {ι ι' : Type*} {G : ι → Graph α β} (hG : Pairwise (Compatible on G))
    (f : ι' → ι): Pairwise (Compatible on (G ∘ f)) := by
  rw [onFun_comp]
  exact Pairwise.onFun_of_refl hG

/-- useful with `Pairwise` and `Set.Pairwise`.-/
@[simp]
lemma stronglyDisjoint_le_compatible : @StronglyDisjoint α β ≤ Compatible :=
  fun _ _ ↦ StronglyDisjoint.compatible

/-! ### Indexed unions -/

protected def iUnion' (G : ι → Graph α β) : Graph α β where
  vertexSet := ⋃ i, V(G i)
  IsLink e x y := (∃ i, (G i).IsLink e x y) ∧ Pairwise ((CompatibleAt e) on G)
  isLink_symm := fun e he x y ⟨⟨i, hi⟩, h'⟩ ↦ ⟨⟨i, hi.symm⟩, h'⟩
  dup_or_dup_of_isLink_of_isLink := by
    refine fun e x y v w ⟨⟨i, hi⟩, h⟩ ⟨⟨j, hj⟩, _⟩ ↦ ?_
    rw [← h.of_refl i j hi.edge_mem hj.edge_mem] at hj
    exact hi.left_eq_or_eq hj
  left_mem_of_isLink := fun e x y ⟨⟨i, hi⟩,h⟩ ↦ mem_iUnion.2 ⟨i, hi.left_mem⟩

/-- The union of an indexed family of pairwise compatible graphs. -/
@[simps]
protected def iUnion (G : ι → Graph α β) (hG : Pairwise (Graph.Compatible on G)) : Graph α β where
  vertexSet := ⋃ i, V(G i)
  edgeSet := ⋃ i, E(G i)
  IsLink e x y := ∃ i, (G i).IsLink e x y
  isLink_symm := by simp +contextual [Symmetric, isLink_comm]
  dup_or_dup_of_isLink_of_isLink :=
    fun e x y v w ⟨i, hi⟩ ⟨j, hj⟩ ↦ (hi.of_compatible (hG.of_refl i j) hj.edge_mem).left_eq_or_eq hj
  edge_mem_iff_exists_isLink := by
    simp only [mem_iUnion, edge_mem_iff_exists_isLink]
    aesop
  left_mem_of_isLink := fun e x y ⟨i, hi⟩ ↦ mem_iUnion.2 ⟨i, hi.left_mem⟩

protected lemma le_iUnion {G : ι → Graph α β}  (hG : Pairwise (Graph.Compatible on G)) (i : ι) :
    G i ≤ Graph.iUnion G hG where
  vertex_subset := subset_iUnion (fun i ↦ V(G i)) i
  isLink_of_isLink := fun _ _ _ he ↦ ⟨i, he⟩

@[simp]
protected lemma iUnion_le_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    Graph.iUnion G hG ≤ H ↔ ∀ i, G i ≤ H :=
  ⟨fun h i ↦ (Graph.le_iUnion hG i).trans h,
    fun h' ↦ ⟨by simp [fun i ↦ vertexSet_mono (h' i)], fun e x y ⟨i, h⟩ ↦ h.of_le (h' i)⟩⟩

@[simp]
protected lemma iUnion_const [Nonempty ι] (G : Graph α β) :
    Graph.iUnion (fun (_ : ι) ↦ G) (pairwise_compatible_const G) = G := by
  apply le_antisymm ?_ (Graph.le_iUnion (pairwise_compatible_const G) (Classical.arbitrary ι))
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ le_refl G

@[simp]
lemma iUnion_inc_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).Inc e x ↔ ∃ i, (G i).Inc e x := by
  simpa [Inc] using exists_comm

@[simp]
lemma iUnion_isLoopAt_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).IsLoopAt e x ↔ ∃ i, (G i).IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma iUnion_isNonloopAt_iff {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) :
    (Graph.iUnion G hG).IsNonloopAt e x ↔ ∃ i, (G i).IsNonloopAt e x := by
  simp only [IsNonloopAt, ne_eq, iUnion_isLink]
  aesop

lemma iUnion_map_le_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G)) (f : ι' → ι):
    (Graph.iUnion (G ∘ f) (pairwise_compatible_comp hG f)) ≤ Graph.iUnion G hG := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ Graph.le_iUnion hG (f i)

lemma iUnion_left_le_iUnion_sum {G : ι → Graph α β} {H : ι' → Graph α β}
    (hGH : Pairwise (Graph.Compatible on Sum.elim G H)) :
    Graph.iUnion G hGH.sum_left ≤ Graph.iUnion (Sum.elim G H) hGH := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH (Sum.inl i))

lemma iUnion_right_le_iUnion_sum {G : ι → Graph α β} {H : ι' → Graph α β}
    (hGH : Pairwise (Graph.Compatible on Sum.elim G H)) :
    Graph.iUnion H hGH.sum_right ≤ Graph.iUnion (Sum.elim G H) hGH := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ le_trans (by simp) (Graph.le_iUnion hGH (Sum.inr i))

@[simp]
lemma induce_iUnion [Nonempty ι] {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (X : Set α) :
    (Graph.iUnion G hG)[X] = .iUnion (fun i ↦ (G i)[X]) (fun _ _ hij ↦ (hG hij).induce ..) :=
  Graph.ext (by simp [iUnion_const]) (by simp)

@[simp]
lemma Compatible.vertexDelete_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (X : Set α) :
    (Graph.iUnion G hG) - X = .iUnion (fun i ↦ (G i) - X) (fun _ _ hij ↦ (hG hij).vertexDelete) :=
  Graph.ext (by simp [iUnion_diff]) (by simp)

@[simp]
lemma Compatible.edgeDelete_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (F : Set β) :
    (Graph.iUnion G hG) ＼ F = .iUnion (fun i ↦ (G i) ＼ F) (fun _ _ hij ↦ (hG hij).edgeDelete) := by
  ext <;> simp

@[simp]
lemma Compatible.edgeRestrict_iUnion {G : ι → Graph α β} (hG : Pairwise (Graph.Compatible on G))
    (F : Set β) : (Graph.iUnion G hG) ↾ F =
    .iUnion (fun i ↦ (G i) ↾ F) (fun _ _ hij ↦ (hG hij).edgeRestrict) := by
  ext <;> simp

protected lemma iUnion_comp_le {f : ι' → ι} {G : ι → Graph α β} (hG : Pairwise (Compatible on G)) :
    Graph.iUnion (fun i ↦ G (f i)) (pairwise_compatible_comp hG f) ≤ Graph.iUnion G hG := by
  rw [Graph.iUnion_le_iff]
  exact fun i ↦ Graph.le_iUnion hG (f i)

lemma iUnion_comp_eq_of_surj {f : ι' → ι} {G : ι → Graph α β} (hG : Pairwise (Compatible on G))
    (hf : Function.Surjective f) :
    Graph.iUnion G hG = Graph.iUnion (fun i ↦ G (f i)) (pairwise_compatible_comp hG f) := by
  refine le_antisymm ?_ (Graph.iUnion_comp_le hG)
  rw [Graph.iUnion_le_iff]
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.le_iUnion (pairwise_compatible_comp hG f) i'

lemma iUnion_range {f : ι' → ι} {G : (Set.range f) → Graph α β}
    (hG : Pairwise (Graph.Compatible on G)) :
    Graph.iUnion G hG = Graph.iUnion (G <| Set.rangeFactorization f ·)
    (pairwise_compatible_comp hG <| rangeFactorization f) :=
  iUnion_comp_eq_of_surj hG surjective_onto_range

/-! ### Set unions -/

/-- The union of a set of pairwise compatible graphs. -/
@[simps!]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β :=
  .iUnion (fun G : s ↦ G.1) <| (pairwise_subtype_iff_pairwise_set s Compatible).2 hs

protected lemma le_sUnion (hs : s.Pairwise Graph.Compatible) (hG : G ∈ s) :
    G ≤ Graph.sUnion s hs := by
  convert Graph.le_iUnion (ι := s) _ ⟨G, hG⟩
  rfl

@[simp]
protected lemma sUnion_le_iff (hs : s.Pairwise Graph.Compatible) :
    Graph.sUnion s hs ≤ H ↔ ∀ G ∈ s, G ≤ H := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_inc_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).Inc e x ↔ ∃ G ∈ s, G.Inc e x := by
  simp [Graph.sUnion]

@[simp]
lemma sUnion_isLoopAt_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).IsLoopAt e x ↔ ∃ G ∈ s, G.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma sUnion_isNonloopAt_iff (hs : s.Pairwise Graph.Compatible) :
    (Graph.sUnion s hs).IsNonloopAt e x ↔ ∃ G ∈ s, G.IsNonloopAt e x := by
  simp [Graph.sUnion]

@[simp]
protected lemma sUnion_singleton (G : Graph α β) : Graph.sUnion {G} (by simp) = G := by
  ext <;> simp

protected lemma sUnion_image {s : Set ι} {f : ι → Graph α β}
    (hs : s.Pairwise (Graph.Compatible on f)) :
    Graph.sUnion (f '' s) hs.image = .iUnion (f · : s → _) (Pairwise.restrict.mpr hs) := by
  rw [Graph.sUnion]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  exact Graph.iUnion_comp_eq_of_surj (f := f') _ (fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩)

protected lemma sUnion_range {f : ι → Graph α β} (h : Pairwise (Graph.Compatible on f)) :
    Graph.sUnion (Set.range f) h.range_pairwise = .iUnion f h := by
  unfold Graph.sUnion
  exact Graph.iUnion_comp_eq_of_surj (f := Set.rangeFactorization f) _ surjective_onto_range

/-! ### Unions of pairs -/

/-- The union of two graphs `G` and `H`. If there is an edge `e` whose `G`-ends differ from
its `H`-ends, then `G` is favoured, so this is not commutative in general.
If `G` and `H` are `Compatible`, this doesn't occur.
We define this in terms of `sUnion` and `Graph.copy` so the vertex and edge sets are
definitionally unions. -/
protected def union (G H : Graph α β) := Graph.copy (V := V(G) ∪ V(H)) (E := E(G) ∪ E(H))
  (Graph.sUnion {G, H ＼ E(G)} (by simp)) (by simp) (by simp) (fun _ _ _ ↦ Iff.rfl)

instance : Union (Graph α β) where union := Graph.union

@[simp]
lemma union_vertexSet (G H : Graph α β) : V(G ∪ H) = V(G) ∪ V(H) := rfl

@[simp]
lemma union_edgeSet (G H : Graph α β) : E(G ∪ H) = E(G) ∪ E(H) := rfl

lemma union_eq_sUnion (G H : Graph α β) : G ∪ H = Graph.sUnion {G, H ＼ E(G)} (by simp) := by
  simp_rw [Union.union, Graph.union, Graph.copy]
  ext <;> simp

lemma union_isLink_iff :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ (H.IsLink e x y ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion]

lemma union_inc_iff : (G ∪ H).Inc e x ↔ G.Inc e x ∨ (H.Inc e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion]

lemma union_isLoopAt_iff : (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ (H.IsLoopAt e x ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion]

lemma union_isNonloopAt_iff :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ (H.IsNonloopAt e x ∧ e ∉ E(G)) := by
  simp only [IsNonloopAt, ne_eq, union_isLink_iff]
  aesop

lemma union_eq_union_edgeDelete (G H : Graph α β) : G ∪ H = G ∪ (H ＼ E(G)) := by
  simp [union_eq_sUnion, union_eq_sUnion]

@[simp]
protected lemma left_le_union (G H : Graph α β) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_isLink_iff]
  tauto

protected lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  simp [union_eq_sUnion, h₁, edgeDelete_le.trans h₂]

lemma union_le_iff {H₁ H₂ : Graph α β} : H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ＼ E(H₁) ≤ G := by
  simp [union_eq_sUnion]

lemma union_mono_right (h : H₁ ≤ H₂) : G ∪ H₁ ≤ G ∪ H₂ := by
  simp only [union_eq_sUnion, Graph.sUnion_le_iff, mem_insert_iff, mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  exact ⟨Graph.le_sUnion _ (by simp), le_trans (edgeDelete_mono_left h) <|
    Graph.le_sUnion _ (by simp : H₂ ＼ E(G) ∈ _)⟩

@[simp]
protected lemma union_self (G : Graph α β) : G ∪ G = G :=
  (Graph.union_le le_rfl le_rfl).antisymm <| Graph.left_le_union ..

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_isLink_iff]
  tauto

lemma isLink_or_isLink_of_union (h : (G ∪ H).IsLink e x y) : G.IsLink e x y ∨ H.IsLink e x y :=
  (union_isLink_iff.1 h).elim .inl fun h' ↦ .inr h'.1

lemma Compatible.union_isLink_iff (h : G.Compatible H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.union_isLink_iff, heG, not_true_eq_false, and_false, or_false, iff_self_or]
    exact fun he ↦ by rwa [h.isLink_eq heG he.edge_mem]
  simp [heG, Graph.union_isLink_iff]

lemma edgeRestrict_union (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ (F₁ ∪ F₂)) = G ↾ F₁ ∪ (G ↾ F₂) := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  rw [(G.compatible_self.mono (by simp) (by simp)).union_isLink_iff]
  simp only [edgeRestrict_isLink, mem_union]
  tauto

lemma Compatible.union_eq_sUnion (h : G.Compatible H) :
    G ∪ H = Graph.sUnion {G, H} (by simp [Set.pairwise_iff_of_refl, h, h.symm]) :=
  Graph.ext (by simp) fun e x y ↦ by simp [h.union_isLink_iff]

lemma Compatible.union_inc_iff (h : G.Compatible H) : (G ∪ H).Inc e x ↔ G.Inc e x ∨ H.Inc e x := by
  simp_rw [Inc, h.union_isLink_iff]
  aesop

lemma Compatible.union_isLoopAt_iff (h : G.Compatible H) :
    (G ∪ H).IsLoopAt e x ↔ G.IsLoopAt e x ∨ H.IsLoopAt e x := by
  simp_rw [← isLink_self_iff, h.union_isLink_iff]

lemma Compatible.union_isNonloopAt_iff (h : G.Compatible H) :
    (G ∪ H).IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ H.IsNonloopAt e x := by
  simp_rw [IsNonloopAt, h.union_isLink_iff]
  aesop

lemma Compatible.union_adj_iff (h : G.Compatible H) : (G ∪ H).Adj x y ↔ G.Adj x y ∨ H.Adj x y := by
  simp [Adj, h.union_isLink_iff, exists_or]

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G :=
  Graph.ext (Set.union_comm ..)
    fun _ _ _ ↦ by rw [h.union_isLink_iff, h.symm.union_isLink_iff, or_comm]

lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G := by
  simp [h_compat.union_eq_sUnion]

lemma Compatible.right_le_union (h : G.Compatible H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma union_eq_self_of_le_left (hle : G ≤ H) : G ∪ H = H :=
  (Graph.union_le hle rfl.le).antisymm (H.compatible_self.mono_left hle).right_le_union

lemma union_eq_self_of_le_right (hle : G ≤ H) : H ∪ G = H :=
  (Graph.union_le rfl.le hle).antisymm <| Graph.left_le_union ..

lemma Compatible.union_mono_left (h : H₂.Compatible G) (hle : H₁ ≤ H₂) : H₁ ∪ G ≤ H₂ ∪ G := by
  rw [h.union_comm, (h.mono_left hle).union_comm]
  exact union_mono_right hle

lemma Compatible.union_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) (h : G₂.Compatible H₁) :
    G₁ ∪ H₁ ≤ G₂ ∪ H₂ := le_trans (h.union_mono_left hleG) (union_mono_right hleH)

lemma edgeRestrict_union_edgeDelete (G : Graph α β) (F : Set β) : (G ↾ F) ∪ (G ＼ F) = G := by
  rw [edgeDelete_eq_edgeRestrict, ← edgeRestrict_union, ← edgeRestrict_inter_edgeSet]
  simp only [union_diff_self, edgeRestrict_inter_edgeSet, edgeRestrict_union, edgeRestrict_self]
  exact union_eq_self_of_le_left (by simp)

lemma edgeDelete_union_edgeRestrict (G : Graph α β) (F : Set β) : (G ＼ F) ∪ (G ↾ F) = G := by
  convert G.edgeRestrict_union_edgeDelete F using 1
  rw [Compatible.union_comm]
  apply G.compatible_of_le_le (by simp) (by simp)

lemma induce_union_edgeDelete (G : Graph α β) (hX : X ⊆ V(G)) : G[X] ∪ (G ＼ E(G[X])) = G := by
  rw [← union_eq_union_edgeDelete, union_eq_self_of_le_left (induce_le hX)]

lemma edgeDelete_union_induce (G : Graph α β) (hX : X ⊆ V(G)) : (G ＼ E(G[X])) ∪ G[X] = G := by
  rw [(Compatible.of_disjoint_edgeSet _).union_comm, induce_union_edgeDelete _ hX]
  simp [disjoint_sdiff_left]

lemma Compatible.union_eq_iUnion (h : G.Compatible H) :
    G ∪ H = Graph.iUnion (fun b ↦ bif b then G else H) (by simpa [pairwise_on_bool]) := by
  generalize_proofs h'
  simp only [le_antisymm_iff, h.union_le_iff, Graph.iUnion_le_iff, Bool.forall_bool, cond_false,
    h.right_le_union, cond_true, Graph.left_le_union, and_self, and_true]
  exact ⟨Graph.le_iUnion h' true, Graph.le_iUnion h' false⟩

lemma Compatible.induce_union (h : G.Compatible H) (X : Set α) : (G ∪ H)[X] = G[X] ∪ H[X] := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink_iff, h.union_isLink_iff, h.induce.union_isLink_iff]
  tauto

lemma Compatible.vertexDelete_union (h : G.Compatible H) (X : Set α) :
    (G ∪ H) - X = (G - X) ∪ (H - X) := by
  simp only [h.union_eq_iUnion, vertexDelete_iUnion, Bool.apply_cond (f := fun G ↦ G - X),
    ← h.vertexDelete.union_eq_iUnion]

lemma induce_union (G : Graph α β) (X Y : Set α) (hX : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    G [X ∪ Y] = G [X] ∪ G [Y] := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink_iff, mem_union, Compatible.induce_induce.union_isLink_iff]
  by_cases hxy : G.IsLink e x y
  · by_cases hx : x ∈ X
    · simp [hx, show y ∉ Y from fun hy ↦ hX x hx y hy hxy.adj]
    by_cases hy : y ∈ X
    · simp [hy, show x ∉ Y from fun hx ↦ hX _ hy _ hx hxy.symm.adj, hxy]
    simp [hx, hy]
  simp [hxy]

/-! ### Indexed Intersections -/

/-- The intersection of a nonempty family of pairwise compatible graphs.
  Remove any disagreeing edges. -/
@[simps]
protected def iInter [Nonempty ι] (G : ι → Graph α β) : Graph α β where
  vertexSet := ⋂ i, V(G i)
  edgeSet := {e | ∃ x y, ∀ i, (G i).IsLink e x y}
  IsLink e x y := ∀ i, (G i).IsLink e x y
  isLink_symm e he x y := by simp [isLink_comm]
  dup_or_dup_of_isLink_of_isLink e _ _ _ _ h h' :=
    (h (Classical.arbitrary ι)).left_eq_or_eq (h' (Classical.arbitrary ι))
  edge_mem_iff_exists_isLink e := by simp
  left_mem_of_isLink e x y h := mem_iInter.2 fun i ↦ (h i).left_mem

protected lemma iInter_le {G : ι → Graph α β} [Nonempty ι] (i : ι) : Graph.iInter G ≤ G i where
  vertex_subset := iInter_subset (fun i ↦ V(G i)) i
  isLink_of_isLink _ _ _ h := h i

@[simp]
lemma le_iInter_iff [Nonempty ι] {G : ι → Graph α β} :
    H ≤ Graph.iInter G ↔ ∀ i, H ≤ G i := by
  let j := Classical.arbitrary ι
  refine ⟨fun h i ↦ h.trans <| Graph.iInter_le .., fun h ↦ ?_⟩
  apply le_of_le_le_subset_subset (h j) (Graph.iInter_le ..) ?_ fun e he ↦ ?_
  · simp [fun i ↦ vertexSet_mono (h i)]
  simp only [iInter_edgeSet, mem_setOf_eq]
  obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet he
  use x, y, fun i ↦ hbtw.of_le (h i)

@[simp]
protected lemma iInter_const [Nonempty ι] (G : Graph α β) :
    Graph.iInter (fun (_ : ι) ↦ G) = G := by
  apply le_antisymm (Graph.iInter_le (Classical.arbitrary ι))
  rw [le_iInter_iff]
  exact fun i ↦ le_refl G

lemma iInter_le_iUnion [Nonempty ι] {G : ι → Graph α β} (hG : Pairwise (Compatible on G)) :
    Graph.iInter G ≤ Graph.iUnion G hG :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| Graph.le_iUnion ..

protected lemma iInter_comp_le [Nonempty ι] [Nonempty ι'] {f : ι' → ι}
    {G : ι → Graph α β} : Graph.iInter G ≤ Graph.iInter (fun i ↦ G (f i)) := by
  rw [Graph.le_iInter_iff]
  exact fun i ↦ Graph.iInter_le (f i)

lemma iInter_comp_eq_of_surj [Nonempty ι] [Nonempty ι'] {f : ι' → ι}
    {G : ι → Graph α β} (hf : Function.Surjective f) :
    Graph.iInter G = Graph.iInter (fun i ↦ G (f i)) :=
  le_antisymm (Graph.iInter_comp_le) <| by
  rw [Graph.le_iInter_iff]
  rintro i
  obtain ⟨i', rfl⟩ := hf i
  exact Graph.iInter_le i'

lemma iInter_range [Nonempty ι'] {f : ι' → ι} {G : (Set.range f) → Graph α β} :
    Graph.iInter G = Graph.iInter (fun i ↦ G (Set.rangeFactorization f i)) :=
  iInter_comp_eq_of_surj surjective_onto_range

@[simp]
lemma iInter_inc_iff [Nonempty ι] {G : ι → Graph α β} :
    (Graph.iInter G).Inc e x ↔ ∃ y, ∀ i, (G i).IsLink e x y := by
  simp only [Inc, iInter_isLink]

@[simp]
lemma iInter_isLoopAt_iff [Nonempty ι] {G : ι → Graph α β} :
    (Graph.iInter G).IsLoopAt e x ↔ ∀ i, (G i).IsLoopAt e x := by
  simp only [IsLoopAt, iInter_isLink]

@[simp]
lemma iInter_isNonloopAt_iff [Nonempty ι] {G : ι → Graph α β} :
    (Graph.iInter G).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ i, (G i).IsLink e x y := by
  simp only [IsNonloopAt, iInter_isLink]

@[simp]
lemma induce_iInter [Nonempty ι] {G : ι → Graph α β} (X : Set α) :
    (Graph.iInter G)[X] = .iInter (fun i ↦ (G i)[X]) :=
  Graph.ext (iInter_const X).symm fun e x y ↦ by
  simp [forall_and_right]

@[simp]
lemma vertexDelete_iInter [Nonempty ι] {G : ι → Graph α β} (X : Set α) :
    (Graph.iInter G) - X = .iInter (fun i ↦ (G i) - X) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, iInter_isLink, iff_def, not_false_eq_true,
    and_self, implies_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).right

@[simp]
lemma edgeDelete_iInter [Nonempty ι] {G : ι → Graph α β} (F : Set β) :
    (Graph.iInter G) ＼ F = .iInter (fun i ↦ (G i) ＼ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, iInter_isLink, iff_def, not_false_eq_true, and_self,
    implies_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).right

@[simp]
lemma edgeRestrict_iInter [Nonempty ι] {G : ι → Graph α β} (F : Set β) :
    (Graph.iInter G) ↾ F = .iInter (fun i ↦ (G i) ↾ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, iInter_isLink, iff_def, and_self, implies_true,
    and_true, true_and]
  exact fun h ↦ (h <| Classical.arbitrary ι).left

/-! ### Set Intersections -/

/-- The intersection of a nonempty set of pairwise compatible graphs. -/
@[simps!]
protected def sInter (s : Set (Graph α β)) (hne : s.Nonempty) :
    Graph α β :=
  @Graph.iInter _ _ _ hne.to_subtype (fun G : s ↦ G.1)

protected lemma sInter_le {s : Set (Graph α β)} (hG : G ∈ s) :
    Graph.sInter s ⟨G, hG⟩ ≤ G := by
  rw [Graph.sInter]
  generalize_proofs h
  exact Graph.iInter_le (⟨G, hG⟩ : s)

@[simp]
protected lemma le_sInter_iff {s} (hne : s.Nonempty) :
    H ≤ Graph.sInter s hne ↔ ∀ G ∈ s, H ≤ G := by
  simp [Graph.sInter]

protected lemma sInter_anti {s t : Set (Graph α β)} (hne : s.Nonempty) (hne' : t.Nonempty)
    (hle : s ⊆ t) : Graph.sInter t hne' ≤ Graph.sInter s hne := by
  rw [Graph.le_sInter_iff hne]
  exact fun G hGs ↦ Graph.sInter_le (hle hGs)

def Equiv.insert_option {s : Set α} [DecidablePred fun (x : α) => x ∈ s] (a : α) (has : a ∉ s) :
    Option s ≃ (insert a s : Set α) :=
  (Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm

protected lemma sInter_insert_eq_iInter {s : Set (Graph α β)} [DecidablePred (· ∈ s)]
    (hGs : G ∉ s) : Graph.sInter (insert G s) (by simp) = Graph.iInter
    ((fun G : (insert G s : Set _) ↦ G.1) ∘ (Equiv.insert_option G hGs)) :=
  Graph.iInter_comp_eq_of_surj <| Equiv.surjective (Equiv.insert_option G hGs)

protected lemma sInter_image {s : Set ι} (hne : s.Nonempty) (f : ι → Graph α β) :
    Graph.sInter (f '' s) (by simpa) = @Graph.iInter _ _ _ hne.to_subtype (f · : s → _) := by
  rw [Graph.sInter]
  let f' : s → ↑(f '' s) := fun i ↦ ⟨f i, ⟨i, i.2, rfl⟩⟩
  have := hne.to_subtype
  exact Graph.iInter_comp_eq_of_surj (f := f') fun ⟨_, i, hGs, rfl⟩ ↦ ⟨⟨i, hGs⟩, rfl⟩

protected lemma sInter_range [Nonempty ι] {f : ι → Graph α β} :
    Graph.sInter (Set.range f) (range_nonempty f) = .iInter f := by
  rw [Graph.sInter]
  exact Graph.iInter_comp_eq_of_surj (f := Set.rangeFactorization f) surjective_onto_range

@[simp]
protected lemma sInter_singleton (G : Graph α β) : Graph.sInter {G} (by simp) = G := by
  apply le_antisymm (Graph.sInter_le (by simp))
  rw [Graph.le_sInter_iff (by simp)]
  exact fun G_2 a ↦ Eq.ge a

@[simp]
lemma sInter_inc_iff {s : Set (Graph α β)} (hs : s.Nonempty) :
    (Graph.sInter s hs).Inc e x ↔ ∃ y, ∀ G ∈ s, G.IsLink e x y := by
  simp only [Inc, sInter_isLink]

@[simp]
lemma sInter_isLoopAt_iff {s : Set (Graph α β)} (hs : s.Nonempty) :
    (Graph.sInter s hs).IsLoopAt e x ↔ ∀ G ∈ s, G.IsLoopAt e x := by
  simp only [IsLoopAt, sInter_isLink]

@[simp]
lemma sInter_isNonloopAt_iff {s : Set (Graph α β)} (hs : s.Nonempty) :
    (Graph.sInter s hs).IsNonloopAt e x ↔ ∃ y ≠ x, ∀ G ∈ s, G.IsLink e x y := by
  simp only [IsNonloopAt, sInter_isLink]

@[simp]
lemma induce_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (X : Set α) :
    (Graph.sInter s hs)[X] = .sInter ((·[X]) '' s) (by simpa) := by
  refine Graph.ext (by simp; exact (biInter_const hs X).symm) fun e x y ↦ ?_
  simp +contextual only [induce_isLink_iff, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma vertexDelete_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (X : Set α) :
    (Graph.sInter s hs) - X = .sInter ((· - X) '' s) (by simpa) := by
  refine Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ ?_
  simp +contextual only [vertexDelete_isLink_iff, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeDelete_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (F : Set β) :
    (Graph.sInter s hs) ＼ F = .sInter ((· ＼ F) '' s) (by simpa) :=
  Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, sInter_isLink, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, iff_def, not_false_eq_true, and_self, implies_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).right

@[simp]
lemma edgeRestrict_sInter {s : Set (Graph α β)} (hs : s.Nonempty) (F : Set β) :
    (Graph.sInter s hs) ↾ F = .sInter ((· ↾ F) '' s) (by simpa) :=
  Graph.ext (by simp [biInter_diff_distrib hs]) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, sInter_isLink, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, and_true, true_and]
  exact fun h ↦ (h _ hs.some_mem).left

/-! ### Intersections -/

/-- The intersection of two graphs `G` and `H`. There seems to be no good way to
defined junk values so that this has the right edge and vertex set, so the
edges are precisely those on which `G` and `H` agree, and the edge set is a subset
of `E(G) ∩ E(H)`,
with equality if `G` and `H` are compatible.   -/
protected def inter (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∩ V(H)
  IsLink e x y := G.IsLink e x y ∧ H.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1.symm, h.2.symm⟩
  dup_or_dup_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  edge_mem_iff_exists_isLink e := by simp
  left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩

instance : Inter (Graph α β) where inter := Graph.inter

@[simp]
lemma inter_vertexSet (G H : Graph α β) : V(G ∩ H) = V(G) ∩ V(H) := rfl

@[simp]
lemma inter_isLink_iff : (G ∩ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G :=
  Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

lemma inter_edgeSet (G H : Graph α β) :
    E(G ∩ H) = {e ∈ E(G) ∩ E(H) | G.IsLink e = H.IsLink e} := by
  simp only [edgeSet_eq_setOf_exists_isLink, inter_isLink_iff, mem_inter_iff, mem_setOf_eq,
    funext_iff, eq_iff_iff, Set.ext_iff]
  exact fun e ↦ ⟨fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
    fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩,
    fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩⟩

lemma inter_edgeSet_subset : E(G ∩ H) ⊆ E(G) ∩ E(H) := by
  simp +contextual [inter_edgeSet, subset_def]

@[simp]
lemma inter_inc_iff : (G ∩ H).Inc e x ↔ ∃ y, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [Inc]

@[simp]
lemma inter_isLoopAt_iff : (G ∩ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma inter_isNonloopAt_iff :
    (G ∩ H).IsNonloopAt e x ↔ ∃ y ≠ x, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [IsNonloopAt]

@[simp]
protected lemma inter_le_left : G ∩ H ≤ G where
  vertex_subset := inter_subset_left
  isLink_of_isLink := by simp +contextual

@[simp]
protected lemma inter_le_right : G ∩ H ≤ H :=
  Graph.inter_comm _ _ ▸ Graph.inter_le_left

protected lemma le_inter (h₁ : H ≤ G₁) (h₂ : H ≤ G₂) : H ≤ G₁ ∩ G₂ where
  vertex_subset := subset_inter (vertexSet_mono h₁) (vertexSet_mono h₂)
  isLink_of_isLink e x y h := by simp [h.of_le h₁, h.of_le h₂]

instance : SemilatticeInf (Graph α β) where
  inf := Graph.inter
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter

@[simp]
lemma inf_eq_inter : H₁ ⊓ H₂ = H₁ ∩ H₂ := rfl

@[simp]
lemma inter_eq_bot_iff : H₁ ∩ H₂ = ⊥ ↔ V(H₁) ∩ V(H₂) = ∅ := by
  rw [← vertexSet_eq_empty_iff, inter_vertexSet]

lemma disjoint_iff_inter_eq_bot : Disjoint H₁ H₂ ↔ H₁ ∩ H₂ = ⊥ := by
  rw [disjoint_iff, inf_eq_inter]

@[simp]
lemma disjoint_iff_vertexSet_inter_eq_empty : Disjoint H₁ H₂ ↔ V(H₁) ∩ V(H₂) = ∅ := by
  rw [disjoint_iff_inter_eq_bot, inter_eq_bot_iff]

lemma disjoint_iff_vertexSet_disjoint : Disjoint H₁ H₂ ↔ Disjoint V(H₁) V(H₂) := by
  rw [disjoint_iff_inter_eq_bot, inter_eq_bot_iff, Set.disjoint_iff_inter_eq_empty]

alias ⟨Disjoint.vertex_disjoint, _⟩ := disjoint_iff_vertexSet_disjoint

lemma Compatible.inter_edgeSet (h : G.Compatible H) : E(G ∩ H) = E(G) ∩ E(H) := by
  rw [Graph.inter_edgeSet]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, h he⟩

lemma inter_eq_iInter : G ∩ H = Graph.iInter (fun b ↦ bif b then G else H) :=
  Graph.ext (by simp [Set.inter_eq_iInter, Bool.apply_cond]) (by simp [and_comm])

lemma le_inter_iff : H ≤ G₁ ∩ G₂ ↔ H ≤ G₁ ∧ H ≤ G₂ := by
  simp [inter_eq_iInter, and_comm]

lemma inter_eq_self_of_le (hle : G ≤ H) : G ∩ H = G :=
  le_antisymm Graph.inter_le_left <| by simpa [le_inter_iff]

lemma le_of_inter_eq_self (h : G ∩ H = G) : G ≤ H := by
  rw [← h]
  exact Graph.inter_le_right

lemma inter_mono_left (hle : G₁ ≤ G₂) : G₁ ∩ H ≤ G₂ ∩ H := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left.trans hle, Graph.inter_le_right⟩

lemma inter_mono_right (hle : H₁ ≤ H₂) : G ∩ H₁ ≤ G ∩ H₂ := by
  rw [le_inter_iff]
  exact ⟨Graph.inter_le_left, Graph.inter_le_right.trans hle⟩

lemma inter_mono (hleG : G₁ ≤ G₂) (hleH : H₁ ≤ H₂) : G₁ ∩ H₁ ≤ G₂ ∩ H₂ :=
  (inter_mono_right hleH).trans (inter_mono_left hleG)

lemma stronglyDisjoint_iff_disjoint_of_compatible (h : H₁.Compatible H₂) :
    StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ := by
  rw [stronglyDisjoint_iff_vertexSet_disjoint_compatible, Set.disjoint_iff_inter_eq_empty,
    disjoint_iff, ← vertexSet_eq_empty_iff]
  simp [h]

lemma edgeSet_induce_inter_eq_edgeSet_induce_of_le (h : G ≤ H) : E(G) ∩ E(H[X]) = E(G[X]) :=
  Set.ext fun _ ↦ ⟨fun ⟨he, x, y, hl, hx, hy⟩ => ⟨x, y, hl.of_le_of_mem h he, hx, hy⟩,
    fun ⟨x, y, hl, hx, hy⟩ => ⟨hl.edge_mem, x, y, hl.of_le h, hx, hy⟩⟩

lemma induce_inter (X Y : Set α) : G[X ∩ Y] = G[X] ∩ G[Y] :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [induce_isLink_iff, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
    implies_true]

lemma induce_inter_distrib (X : Set α) : (G ∩ H)[X] = G[X] ∩ H[X] :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [induce_isLink_iff, inter_isLink_iff, iff_def, and_self, implies_true]

lemma vertexDelete_union (X Y : Set α) : G - (X ∪ Y) = (G - X) ∩ (G - Y) :=
  Graph.ext (by simp [diff_inter_diff]) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, mem_union, not_or, inter_isLink_iff, iff_def,
    not_false_eq_true, and_self, implies_true]

lemma vertexDelete_inter_distrib (X : Set α) : (G ∩ H) - X = (G - X) ∩ (H - X) :=
  Graph.ext (by simp [diff_inter_distrib_right]) fun e x y ↦ by
  simp +contextual only [vertexDelete_isLink_iff, inter_isLink_iff, iff_def, not_false_eq_true,
    and_self, implies_true]

lemma edgeDelete_union (F₁ F₂ : Set β) : G ＼ (F₁ ∪ F₂) = (G ＼ F₁) ∩ (G ＼ F₂) :=
  Graph.ext (by simp [diff_inter_diff]) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, mem_union, not_or, inter_isLink_iff, iff_def,
    not_false_eq_true, and_self, implies_true]

lemma edgeDelete_inter_distrib (F : Set β) : (G ∩ H) ＼ F = (G ＼ F) ∩ (H ＼ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeDelete_isLink, inter_isLink_iff, iff_def, not_false_eq_true, and_self,
    implies_true]

lemma edgeRestrict_inter (F₁ F₂ : Set β) : (G ↾ (F₁ ∩ F₂)) = (G ↾ F₁) ∩ (G ↾ F₂) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, mem_inter_iff, inter_isLink_iff, iff_def, and_self,
    implies_true]

lemma edgeRestrict_inter_distrib (F : Set β) : (G ∩ H) ↾ F = (G ↾ F) ∩ (H ↾ F) :=
  Graph.ext (by simp) fun e x y ↦ by
  simp +contextual only [edgeRestrict_isLink, inter_isLink_iff, iff_def, and_self, implies_true]

protected lemma inter_distrib_iInter [Nonempty ι] {H : ι → Graph α β} :
    G ∩ (Graph.iInter H) = Graph.iInter (fun i ↦ G ∩ (H i)) :=
  Graph.ext (by simp [inter_iInter]) (by
    simp only [inter_isLink_iff, iInter_isLink]
    rintro i x y
    rw [forall_and_left])

protected lemma inter_distrib_sInter [Nonempty ι] {s : Set (Graph α β)} (hne : s.Nonempty) :
    G ∩ (Graph.sInter s hne) = Graph.sInter ((G ∩ ·) '' s) (by simpa) := by
  rw [Graph.sInter_image hne]
  unfold Graph.sInter
  have := hne.to_subtype
  rw [Graph.inter_distrib_iInter]

protected lemma inter_distrib_iUnion {H : ι → Graph α β} (hH : Pairwise (Compatible on H)) :
    G ∩ (Graph.iUnion H hH) = Graph.iUnion (fun i ↦ G ∩ (H i))
      (fun _ _ hne ↦ (hH hne).mono Graph.inter_le_right Graph.inter_le_right) :=
  Graph.ext (by simp [inter_iUnion]) (by simp)

protected lemma inter_distrib_sUnion (hs : s.Pairwise Compatible) :
    G ∩ (Graph.sUnion s hs) = Graph.sUnion ((fun K ↦ G ∩ K) '' s) (by
      rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ -
      exact (hs.of_refl hK₁ hK₂).mono Graph.inter_le_right Graph.inter_le_right) := by
  ext <;> aesop

lemma Pairwise.union_compatible {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
    (Graph.sUnion s (hst.mono subset_union_left)).Compatible
    (Graph.sUnion t (hst.mono subset_union_right)) := by
  refine compatible_of_le_le (G := Graph.sUnion (s ∪ t) hst) ?_ ?_ <;> rw [Graph.sUnion_le_iff]
  <;> exact fun G hG ↦ Graph.le_sUnion hst (by simp [hG])

lemma sUnion_union_sUnion {s t : Set (Graph α β)} (hst : (s ∪ t).Pairwise Compatible) :
    Graph.sUnion s (hst.mono subset_union_left) ∪ Graph.sUnion t (hst.mono subset_union_right) =
    Graph.sUnion (s ∪ t) hst := by
  have hs : s.Pairwise Compatible := hst.mono subset_union_left
  have ht : t.Pairwise Compatible := hst.mono subset_union_right
  refine Graph.ext (by aesop) fun e x y ↦ ?_
  rw [(Pairwise.union_compatible hst).union_isLink_iff]
  aesop

protected lemma sInter_inter_sInter {s t : Set (Graph α β)} (hs : s.Nonempty) (ht : t.Nonempty) :
    Graph.sInter s hs ∩ .sInter t ht = .sInter (s ∪ t) (by simp [hs]) := by
  ext <;> aesop

lemma Compatible.sum_compatible {G : ι → Graph α β} {H : ι' → Graph α β}
    (hGH : Pairwise (Compatible on (Sum.elim G H))) :
    (Graph.iUnion G (hGH.sum_left)).Compatible (Graph.iUnion H (hGH.sum_right)) :=
  compatible_of_le_le (iUnion_left_le_iUnion_sum hGH) <| iUnion_right_le_iUnion_sum hGH

protected lemma iUnion_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
    {H : ι' → Graph α β} (hGH : Pairwise (Compatible on (Sum.elim G H))) :
    Graph.iUnion (Sum.elim G H) hGH = (.iUnion G hGH.sum_left) ∪ (.iUnion H hGH.sum_right) := by
  refine le_antisymm ?_ <| Graph.union_le (iUnion_left_le_iUnion_sum hGH)
    (iUnion_right_le_iUnion_sum hGH)
  rw [Graph.iUnion_le_iff]
  rintro (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · exact le_trans (Graph.le_iUnion hGH.sum_left i) (Graph.left_le_union _ _)
  · exact le_trans (Graph.le_iUnion hGH.sum_right i)
      (Compatible.right_le_union (Compatible.sum_compatible hGH))

protected lemma iInter_sum [Nonempty ι] [Nonempty ι'] {G : ι → Graph α β}
    {H : ι' → Graph α β} : Graph.iInter (Sum.elim G H) = .iInter G ∩ .iInter H := by
  ext <;> aesop

protected lemma iInter_option [Nonempty ι] {G₁ : Graph α β} {G : ι → Graph α β} :
    Graph.iInter (Option.elim · G₁ G) = G₁ ∩ Graph.iInter G :=
  Graph.ext (by simp [Set.iInter_option]) (by simp [Option.forall])

protected lemma sInter_insert {s : Set (Graph α β)} (G : Graph α β) (hne : s.Nonempty) :
    Graph.sInter (insert G s) (by simp) = G ∩ Graph.sInter s hne := by
  ext v <;> simp

lemma iInter_option_eq_sInter_insert {G₁ : Graph α β} {G : ι → Graph α β} :
    Graph.iInter (Option.elim · G₁ G) = Graph.sInter (insert G₁ (range G)) (by simp) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [range_eq_empty G]
  rw [Graph.sInter_insert _ (range_nonempty _), Graph.sInter_range, Graph.iInter_option]

-- protected lemma union_iInter [Nonempty ι] {H : ι → Graph α β} (hc : ∀ i, G.Compatible (H i))
--     (hH : Pairwise (Compatible on H)) :
--     G ∪ (Graph.iInter H hH) = Graph.iInter (fun i ↦ G ∪ (H i))
--     (by
--       refine fun i j hij ↦ (h)
--     )

--     := by
--   _

  -- rw [Graph.sUnion, Graph.sUnion]
  -- generalize_proofs h₁ h₂
  -- rw [Graph.inter_distrib_iUnion _]





section Subgraph

/-! ### Subgraphs -/

variable {H : ι → Graph α β} {H₁ H₂ : Graph α β}

lemma pairwise_compatible_of_subgraph {H : ι → Graph α β} (h : ∀ i, H i ≤ G) :
    Pairwise (Compatible on H) :=
  fun i j _ ↦ compatible_of_le_le (h i) (h j)

lemma set_pairwise_compatible_of_subgraph (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
    s.Pairwise Compatible :=
  fun _ hi _ hj _ ↦ compatible_of_le_le (h hi) (h hj)

protected lemma iUnion_le_of_forall_le (h : ∀ i, H i ≤ G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤ G := by
  simpa

protected lemma sUnion_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) :
    Graph.sUnion s (set_pairwise_compatible_of_subgraph h) ≤ G := by
  simpa

protected lemma iInter_le_of_forall_le [Nonempty ι] (h : ∀ i, H i ≤ G) :
    Graph.iInter H ≤ G :=
  (Graph.iInter_le (Classical.arbitrary ι)).trans <| h _

protected lemma sInter_le_of_forall_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) (hne : s.Nonempty) :
    Graph.sInter s hne ≤ G :=
  have := hne.to_subtype
  Graph.iInter_le_of_forall_le (by simpa)

/-- A union of closed subgraphs of `G` is a closed subgraph of `G`. -/
lemma iUnion_isClosedSubgraph (h : ∀ i, H i ≤c G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤c G where
  le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
  closed e x he := by
    simp only [iUnion_vertexSet, mem_iUnion, iUnion_edgeSet, forall_exists_index]
    exact fun i hxi ↦ ⟨_, (he.of_isClosedSubgraph_of_mem (h i) hxi).edge_mem⟩

/-- A nonempty union of spanning subgraphs of `G` is a spanning subgraph of `G`. -/
lemma iUnion_isSpanningSubgraph [Nonempty ι] (h : ∀ i, H i ≤s G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph (fun i ↦ (h i).le)) ≤s G where
  le := Graph.iUnion_le_of_forall_le fun i ↦ (h i).le
  vertexSet_eq := by simp [(h _).vertexSet_eq, iUnion_const]

-- A weakening of the previous lemma.
lemma iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le [Nonempty ι]
    (h : ∀ i, H i ≤ G) (hH : ∃ i, H i ≤s G) :
    Graph.iUnion H (pairwise_compatible_of_subgraph h) ≤s G where
  le := Graph.iUnion_le_of_forall_le h
  vertexSet_eq := by
    apply le_antisymm
    · simp only [iUnion_vertexSet, le_eq_subset, iUnion_subset_iff]
      exact fun i ↦ (h i).vertex_subset
    obtain ⟨i, hi⟩ := hH
    rw [← hi.vertexSet_eq]
    exact subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a

/-- A nonempty intersection of induced subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isInducedSubgraph [Nonempty ι] (h : ∀ i, H i ≤i G) :
    Graph.iInter H ≤i G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  isLink_of_mem_mem := by
    simp only [iInter_vertexSet, mem_iInter, iInter_isLink]
    exact fun e x y he hx hy i ↦ (h i).isLink_of_mem_mem he (hx i) (hy i)

/-- A nonempty intersection of spanning subgraphs of `G` is a spanning subgraph of `G`.-/
lemma iInter_isSpanningSubgraph [Nonempty ι] (h : ∀ i, H i ≤s G) :
    Graph.iInter H ≤s G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  vertexSet_eq := iInter_eq_const fun i ↦ (h i).vertexSet_eq

/-- A nonempty intersection of closed subgraphs `G` is an induced subgraph of `G`-/
lemma iInter_isClosedSubgraph [Nonempty ι] (h : ∀ i, H i ≤c G) :
    Graph.iInter H ≤c G where
  le := Graph.iInter_le_of_forall_le fun i ↦ (h i).le
  closed e x he := by
    simp only [iInter_vertexSet, mem_iInter, iInter_edgeSet, mem_setOf_eq]
    rintro hx
    obtain ⟨y, hy⟩ := he
    use x, y, fun i ↦ by rwa [(h i).isLink_iff_of_mem (hx i)]

lemma sUnion_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) :
    Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤c G :=
  iUnion_isClosedSubgraph <| by simpa

lemma sUnion_isSpanningSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤s G) (hne : s.Nonempty) :
    Graph.sUnion s (set_pairwise_compatible_of_subgraph (fun _ h ↦ (hs h).le)) ≤s G :=
  have := hne.to_subtype
  iUnion_isSpanningSubgraph <| by simpa

lemma sInter_isInducedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤i G) (hne : s.Nonempty) :
    Graph.sInter s hne ≤i G :=
  have := hne.to_subtype
  iInter_isInducedSubgraph <| by simpa

lemma sInter_isClosedSubgraph (hs : ∀ ⦃H⦄, H ∈ s → H ≤c G) (hne : s.Nonempty) :
    Graph.sInter s hne ≤c G :=
  have := hne.to_subtype
  iInter_isClosedSubgraph <| by simpa

lemma isClosedSubgraph_iUnion_of_stronglyDisjoint (h : Pairwise (StronglyDisjoint on H)) (i : ι) :
    H i ≤c Graph.iUnion H (h.mono fun _ _ ↦ StronglyDisjoint.compatible) where
  le := Graph.le_iUnion ..
  closed e x he hx := by
    obtain ⟨j, hj : (H j).Inc e x⟩ := (iUnion_inc_iff ..).1 he
    obtain rfl | hne := eq_or_ne i j
    · exact hj.edge_mem
    exact False.elim <| (h hne).vertex.notMem_of_mem_left hx hj.vertex_mem

lemma isClosedSubgraph_sUnion_of_stronglyDisjoint (s : Set (Graph α β))
    (hs : s.Pairwise StronglyDisjoint) (hG : G ∈ s) : G ≤c Graph.sUnion s (hs.mono' (by simp)) :=
  isClosedSubgraph_iUnion_of_stronglyDisjoint ((pairwise_subtype_iff_pairwise_set ..).2 hs) ⟨G, hG⟩

lemma isClosedSubgraph_union_left_of_vertexSet_disjoint (h : Disjoint V(H₁) V(H₂)) :
    H₁ ≤c H₁ ∪ H₂ := by
  refine ⟨Graph.left_le_union H₁ H₂, fun e x hinc hx₁ => ?_⟩
  have hninc : ¬ H₂.Inc e x := fun hinc ↦ h.notMem_of_mem_left hx₁ hinc.vertex_mem
  simp only [union_inc_iff, hninc, false_and, or_false] at hinc
  exact hinc.edge_mem

lemma Disjoint.isClosedSubgraph_union_left (h : Disjoint H₁ H₂) : H₁ ≤c H₁ ∪ H₂ :=
  isClosedSubgraph_union_left_of_vertexSet_disjoint <| Disjoint.vertex_disjoint h

lemma StronglyDisjoint.isClosedSubgraph_union_left (h : StronglyDisjoint H₁ H₂) :
    H₁ ≤c H₁ ∪ H₂ := by
  rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
  exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

lemma StronglyDisjoint.isClosedSubgraph_union_right (h : StronglyDisjoint H₁ H₂) :
    H₂ ≤c H₁ ∪ H₂ := by
  rw [(stronglyDisjoint_le_compatible _ _ h).union_eq_sUnion]
  exact isClosedSubgraph_sUnion_of_stronglyDisjoint _ (by simp [Set.Pairwise, h, h.symm]) (by simp)

lemma IsClosedSubgraph.union (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∪ H₂ ≤c G := by
  rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
  exact iUnion_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsSpanningSubgraph.union (h₁ : H₁ ≤s G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
  rw [(compatible_of_le_le h₁.le h₂.le).union_eq_iUnion]
  exact iUnion_isSpanningSubgraph <| by simp [h₁,h₂]

lemma IsSpanningSubgraph.union_left (h₁ : H₁ ≤s G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤s G := by
  rw [(compatible_of_le_le h₁.le h₂).union_eq_iUnion]
  exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁.le, h₂])
    ⟨True, h₁⟩

lemma IsSpanningSubgraph.union_right (h₁ : H₁ ≤ G) (h₂ : H₂ ≤s G) : H₁ ∪ H₂ ≤s G := by
  rw [(compatible_of_le_le h₁ h₂.le).union_eq_iUnion]
  exact iUnion_isSpanningSubgraph_of_exists_isSpanningSubgraph_of_forall_le (by simp [h₁, h₂.le])
    ⟨False, h₂⟩

lemma IsInducedSubgraph.inter (h₁ : H₁ ≤i G) (h₂ : H₂ ≤i G) : H₁ ∩ H₂ ≤i G := by
  rw [inter_eq_iInter]
  exact iInter_isInducedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) : H₁ ∩ H₂ ≤c G := by
  rw [inter_eq_iInter]
  exact iInter_isClosedSubgraph <| by simp [h₁,h₂]

lemma IsClosedSubgraph.inter_le {K G H : Graph α β} (hKG : K ≤c G) (hle : H ≤ G) : K ∩ H ≤c H where
  le := Graph.inter_le_right
  closed e x hex hx := by
    rw [inter_vertexSet] at hx
    have heK := ((hex.of_le hle).of_isClosedSubgraph_of_mem hKG hx.1).edge_mem
    rw [(compatible_of_le_le hKG.le hle).inter_edgeSet]
    exact ⟨heK, hex.edge_mem⟩

@[simp]
lemma le_bot_iff : G ≤ ⊥ ↔ G = ⊥ := _root_.le_bot_iff

@[simp]
lemma isClosedSubgraph_bot_iff : G ≤c ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isClosedSubgraph ⊥⟩

@[simp]
lemma isSpanningSubgraph_bot_iff : G ≤s ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ ⟨le_rfl, rfl⟩⟩

@[simp]
lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ bot_isInducedSubgraph ⊥⟩

@[simp]
lemma induce_empty : G[∅] = ⊥ := by
  rw [← vertexSet_eq_empty_iff, induce_vertexSet]

end Subgraph

/-! ### Adding one edge -/

@[simp]
lemma singleEdge_compatible_iff :
    Compatible (Graph.singleEdge u v e) G ↔ (e ∈ E(G) → G.IsLink e u v) := by
  refine ⟨fun h he ↦ by simp [← h ⟨by simp, he⟩], fun h f ⟨hfe, hf⟩ ↦ ?_⟩
  obtain rfl : f = e := by simpa using hfe
  ext x y
  simp only [singleEdge_isLink, (h hf).isLink_iff]
  tauto

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
@[simps! edgeSet vertexSet]
protected def addEdge (G : Graph α β) (e : β) (a b : α) : Graph α β :=
  Graph.singleEdge a b e ∪ G

lemma addEdge_isLink (G : Graph α β) (e : β) (a b : α) : (G.addEdge e a b).IsLink e a b := by
  simp [Graph.addEdge, union_isLink_iff]

lemma addEdge_isLink_of_ne (hf : G.IsLink f x y) (hne : f ≠ e) (a b : α) :
    (G.addEdge e a b).IsLink f x y := by
  simpa [Graph.addEdge, union_isLink_iff, hne]

lemma addEdge_isLink_iff {a b : α} (he : e ∉ E(G)) :
    (G.addEdge e a b).IsLink f x y ↔ (f = e ∧ s(a,b) = s(x,y)) ∨ G.IsLink f x y := by
  have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
  simp only [Graph.addEdge, union_isLink_iff, singleEdge_isLink, singleEdge_edgeSet,
    mem_singleton_iff, edgeDelete_isLink, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  obtain rfl | hne := eq_or_ne e f
  · have hl : ¬ G.IsLink e x y := fun h ↦ he h.edge_mem
    simp only [true_and, not_true_eq_false, hl, and_self, or_false]
    tauto
  simp [hne.symm]

lemma addEdge_deleteEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (G.addEdge e x y) ＼ {e} = G := by
  have hc : Compatible (Graph.singleEdge x y e) G := by simp [he]
  simp only [Graph.addEdge, Graph.ext_iff, edgeDelete_vertexSet, union_vertexSet,
    singleEdge_vertexSet, union_eq_right, insert_subset_iff, hx, singleton_subset_iff, hy, and_self,
    edgeDelete_isLink, hc.union_isLink_iff, singleEdge_isLink, mem_singleton_iff, true_and]
  intro f p q
  obtain rfl | hne := eq_or_ne f e
  · suffices ¬ G.IsLink f p q by simpa
    exact fun hf ↦ he hf.edge_mem
  simp [hne]

lemma addEdge_le (hle : H ≤ G) (he : G.IsLink e x y) : H.addEdge e x y ≤ G :=
  Graph.union_le (by simpa) hle

lemma le_addEdge (he : e ∉ E(G)) : G ≤ G.addEdge e x y :=
  Compatible.right_le_union <| by simp [he]

lemma addEdge_mono (hle : H ≤ G) : H.addEdge e x y ≤ G.addEdge e x y :=
  union_mono_right hle

lemma deleteEdge_le_addEdge : G ＼ {e} ≤ G.addEdge e x y := by
  rw [Graph.addEdge, union_eq_union_edgeDelete]
  simp only [singleEdge_edgeSet]
  exact Compatible.right_le_union <| by simp

lemma deleteEdge_addEdge : (G ＼ {e}).addEdge e x y = G.addEdge e x y := by
  refine le_antisymm (addEdge_mono edgeDelete_le) ?_
  unfold Graph.addEdge
  rw [union_le_iff]
  refine ⟨Graph.left_le_union (Graph.singleEdge x y e) (G ＼ {e}), Compatible.right_le_union ?_⟩
  simp

lemma addEdge_eq_self (hbtw : G.IsLink e x y) : G.addEdge e x y = G :=
  le_antisymm (addEdge_le (by simp) hbtw) <| Compatible.right_le_union <| by simp [hbtw]

lemma addEdge_idem : (G.addEdge e x y).addEdge e x y = G.addEdge e x y :=
  addEdge_eq_self <| addEdge_isLink G e x y

lemma isSpanningSubgraph_addEdge (he : e ∉ E(G)) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G ≤s G.addEdge e x y := by
  nth_rw 1 [← addEdge_deleteEdge he hx hy]
  exact edgeDelete_isSpanningSubgraph

lemma IsLink.deleteEdge_addEdge (h : G.IsLink e x y) : (G ＼ {e}).addEdge e x y = G :=
  ext_of_le_le (addEdge_le (by simp) h) le_rfl (by simp [pair_subset_iff, h.left_mem, h.right_mem])
    <| by simp [h.edge_mem]
