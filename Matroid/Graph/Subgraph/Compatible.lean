import Matroid.Graph.Subgraph.Delete
import Matroid.ForMathlib.Partition.Lattice

variable {α β ι ι' : Type*} [CompleteLattice α] {x y z u v w : α} {e f : β}
  {G G₁ G₂ H H₁ H₂ : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}
  {P Q : Partition α} {Gι Hι : ι → Graph α β}

open Set Function

/- For Mathlib -/

@[simp]
lemma Option.elim_eq_const_of_isEmpty {α : Type*} [hα : IsEmpty α] (f : α → β) (b : β) :
    (Option.elim · b f) = fun _ ↦ b :=
  funext fun a ↦ match a with
  | none => rfl
  | some a => hα.elim a

open scoped Sym2 Graph

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
section CompatibleAt

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
  rw [← h he.edge_mem heH, induce_isLink, he.isLink_iff]
  aesop

lemma CompatibleAt.induce_right (h : CompatibleAt e G H) (X : Set α) : CompatibleAt e G H[X] :=
  (h.symm.induce_left X).symm

lemma CompatibleAt.induce (h : CompatibleAt e G H) (X : Set α) : CompatibleAt e G[X] H[X] :=
  (h.induce_left X).induce_right X

end CompatibleAt

section Compatible

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := EqOn G.IsLink H.IsLink (E(G) ∩ E(H))

@[simp]
lemma Compatible.compatibleAt (h : G.Compatible H) (e : β) : CompatibleAt e G H :=
  fun heG heH ↦ h ⟨heG, heH⟩

@[simp]
lemma pairwise_compatibleAt_of_compatible (h : Pairwise (Compatible on Gι)) (e : β) :
    Pairwise (CompatibleAt e on Gι) := fun _ _ hne ↦ (h hne).compatibleAt e

@[simp]
lemma set_pairwise_compatibleAt_of_compatible (h : s.Pairwise Compatible) (e : β) :
    s.Pairwise (CompatibleAt e) := fun _ hi _ hj hne ↦ (h hi hj hne).compatibleAt e

lemma Compatible.isLink_eq (h : G.Compatible H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e = H.IsLink e :=
  h ⟨heG, heH⟩

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G := by
  rwa [Compatible, inter_comm, eqOn_comm]

instance : IsSymm (Graph α β) Compatible where
  symm _ _ := Compatible.symm

@[simp]
lemma compatible_symmetric : Symmetric (@Compatible α β _) :=
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

lemma IsLink.of_compatible (h : G.IsLink e x y) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLink e x y := by
  rwa [← hGH ⟨h.edge_mem, heH⟩]

lemma Inc.of_compatible (h : G.Inc e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

lemma IsLoopAt.of_compatible (h : G.IsLoopAt e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLoopAt e x := IsLink.of_compatible h hGH heH

lemma IsNonloopAt.of_compatible (h : G.IsNonloopAt e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsNonloopAt e x := by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

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

lemma Compatible.pair (h : G.Compatible H) : ({G, H} : Set (Graph α β)).Pairwise Compatible := by
  rw [pairwise_pair]
  exact fun _ ↦ ⟨h, h.symm⟩

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
  simp only [induce_isLink, ← h ⟨heuv.edge_mem, heX⟩, and_iff_left_iff_imp]
  intro h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq heuv <;> simp_all

lemma Compatible.induce_right (h : Compatible G H) (X : Set α) : G.Compatible H[X] :=
  (h.symm.induce_left X).symm

lemma Compatible.induce (h : Compatible G H) : G[X].Compatible H[X] :=
  (h.induce_left X).induce_right X

lemma Compatible.vertexDelete (h : Compatible G H) : (G - X).Compatible (H - X) :=
  h.mono vertexDelete_le vertexDelete_le

lemma Compatible.edgeDelete (h : Compatible G H) : (G ＼ F).Compatible (H ＼ F) :=
  h.mono edgeDelete_le edgeDelete_le

lemma Compatible.edgeRestrict (h : Compatible G H) : (G ↾ F).Compatible (H ↾ F) :=
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
lemma stronglyDisjoint_le_compatible : @StronglyDisjoint α β _ ≤ @Compatible α β _ :=
  fun _ _ ↦ StronglyDisjoint.compatible

end Compatible

section Dup_agree

def Dup_agree (G H : Graph α β) : Prop := (Partition.Agree on Graph.vertexPartition) G H

lemma Dup_agree.mem_iff_subset (h : G.Dup_agree H) (hxG : x ∈ V(G)) :
    x ∈ V(H) ↔ ¬ Disjoint P(H).supp x := by
  refine ⟨fun hxH h => ?_, fun hdisj => ?_⟩ <;> rw [← mem_vertexPartition_iff] at *
  · exact P(H).ne_bot_of_mem hxH <| h.symm.eq_bot_of_le <| P(H).le_supp_of_mem hxH
  · exact h.mem_of_mem hxG hdisj

@[simp]
lemma dup_agree_rfl : G.Dup_agree G := by
  simp [Dup_agree]

instance : IsRefl (Graph α β) Dup_agree where
  refl _ := dup_agree_rfl

lemma Dup_agree.symm (h : G.Dup_agree H) : H.Dup_agree G := by
  unfold Dup_agree
  exact _root_.symm h

instance : IsSymm (Graph α β) Dup_agree where
  symm _ _ := Dup_agree.symm

@[simp]
lemma dup_agree_symmetric : Symmetric (@Dup_agree α β _) :=
  fun _ _ ↦ Dup_agree.symm

lemma Dup_agree_comm : G.Dup_agree H ↔ H.Dup_agree G :=
  ⟨Dup_agree.symm, Dup_agree.symm⟩

@[deprecated "Pairwise.onFun_comp_of_refl" (since := "2025-07-30")]
lemma pairwise_dup_agree_comp {ι ι' : Type*} {G : ι → Graph α β} (hG : Pairwise (Dup_agree on G))
    (f : ι' → ι): Pairwise (Dup_agree on (G ∘ f)) := by
  rw [onFun_comp]
  exact Pairwise.onFun_of_refl hG f

lemma Dup_agree.mono_left {G₀ : Graph α β} (h : G.Dup_agree H) (hG₀ : G₀ ≤ G) :
    G₀.Dup_agree H := Partition.Agree.mono_left h (vertexPartition_mono hG₀)

lemma Dup_agree.mono_right {H₀ : Graph α β} (h : G.Dup_agree H) (hH₀ : H₀ ≤ H) :
    G.Dup_agree H₀ := Partition.Agree.mono_right h (vertexPartition_mono hH₀)

lemma Dup_agree.mono {G₀ H₀ : Graph α β} (h : G.Dup_agree H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Dup_agree H₀ := Partition.Agree.mono h (vertexPartition_mono hG) (vertexPartition_mono hH)

lemma dup_agree_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Dup_agree H₂ :=
  Partition.agree_of_subset_subset (vertexPartition_mono h₁) (vertexPartition_mono h₂)

lemma dup_agree_of_forall_map_le (h : ∀ i, Gι i ≤ G) : Pairwise (Dup_agree on Gι) := by
  rintro i j -
  exact dup_agree_of_le_le (h i) (h j)

lemma dup_agree_of_forall_mem_le (h : ∀ ⦃H⦄, H ∈ s → H ≤ G) : s.Pairwise Dup_agree := by
  rintro _ hi _ hj _
  exact dup_agree_of_le_le (h hi) (h hj)

lemma dup_agree_of_le (h : H ≤ G) : H.Dup_agree G := dup_agree_of_le_le h le_rfl

lemma Dup_agree.pair (h : G.Dup_agree H) : ({G, H} : Set (Graph α β)).Pairwise Dup_agree := by
  rw [pairwise_pair]
  exact fun _ ↦ ⟨h, h.symm⟩

/-- Used to simplify the definition of the union of a pair. -/
lemma Dup_agree.pair_edgeDelete (h : G.Dup_agree H) :
    ({G, H ＼ E(G)} : Set (Graph α β)).Pairwise Dup_agree := by
  rw [pairwise_pair]
  exact fun _ ↦ ⟨h, h.symm⟩

@[simp]
lemma Dup_agree.induce (X : Set α) (h : G.Dup_agree H) : G[X].Dup_agree H[X] := by
  simp [Dup_agree, Function.onFun]
  exact Partition.Agree.mono h (P(G).restrict_subset _) (P(H).restrict_subset _)

lemma Dup_agree.vertexDelete (X : Set α) (h : G.Dup_agree H) : (G - X).Dup_agree (H - X) :=
  Partition.Agree.mono h (vertexPartition_mono vertexDelete_le)
    (vertexPartition_mono (vertexDelete_le))

lemma Dup_agree.edgeDelete (F : Set β) (h : G.Dup_agree H) : (G ＼ F).Dup_agree (H ＼ F) := by
  simpa only [Dup_agree, edgeDelete_vertexSet, Partition.agree_iff_rel] using h

lemma Dup_agree.edgeRestrict (F : Set β) (h : G.Dup_agree H) : (G ↾ F).Dup_agree (H ↾ F) := by
  simpa only [Dup_agree, edgeRestrict_vertexSet, Partition.agree_iff_rel] using h

lemma pairwise_dup_agree_eq_pairwise_image {S : Set (Graph α β)} :
    S.Pairwise Dup_agree ↔ (vertexPartition '' S).Pairwise Partition.Agree := by
  rw [Set.pairwise_image_of_refl]
  rfl

@[simp]
lemma pairwise_dup_agree_edgeDelete (hG' : G.Dup_agree H) :
    ({G, H ＼ E(G)} : Set _).Pairwise Dup_agree := by
  rw [pairwise_pair]
  exact fun _ ↦ ⟨hG', hG'.symm⟩

lemma Pairwise.induce_dup_agree {G : ι → Graph α β} (h : Pairwise (Dup_agree on G))
    (P : Set α) : Pairwise (Dup_agree on fun i ↦ (G i)[P]) :=
  h.mono (fun _ _ ↦ Dup_agree.induce P)

lemma Pairwise.vertexDelete_dup_agree {G : ι → Graph α β} (h : Pairwise (Dup_agree on G))
    (X : Set α) : Pairwise (Dup_agree on fun i ↦ (G i) - X) :=
  h.mono (fun _ _ ↦ Dup_agree.vertexDelete X)

lemma Pairwise.edgeDelete_dup_agree {G : ι → Graph α β} (h : Pairwise (Dup_agree on G))
    (F : Set β) : Pairwise (Dup_agree on fun i ↦ (G i) ＼ F) :=
  h.mono (fun _ _ ↦ Dup_agree.edgeDelete F)

lemma Pairwise.edgeRestrict_dup_agree {G : ι → Graph α β} (h : Pairwise (Dup_agree on G))
    (F : Set β) : Pairwise (Dup_agree on fun i ↦ (G i) ↾ F) :=
  h.mono (fun _ _ ↦ Dup_agree.edgeRestrict F)

lemma Set.Pairwise.induce_dup_agree {S : Set (Graph α β)} (h : S.Pairwise Dup_agree)
    (P : Set α) : ((·[P]) '' S).Pairwise Dup_agree :=
  fun _ ⟨_, hGS, hi⟩ _ ⟨_, hHS, hj⟩ _ ↦ hi ▸ hj ▸ (h.of_refl hGS hHS).induce P

lemma Set.Pairwise.vertexDelete_dup_agree {S : Set (Graph α β)} (h : S.Pairwise Dup_agree)
    (X : Set α) : ((· - X) '' S).Pairwise Dup_agree :=
  fun _ ⟨_, hGS, hi⟩ _ ⟨_, hHS, hj⟩ _ ↦ hi ▸ hj ▸ (h.of_refl hGS hHS).vertexDelete X

lemma Set.Pairwise.edgeDelete_dup_agree {S : Set (Graph α β)} (h : S.Pairwise Dup_agree)
    (F : Set β) : ((· ＼ F) '' S).Pairwise Dup_agree :=
  fun _ ⟨_, hGS, hi⟩ _ ⟨_, hHS, hj⟩ _ ↦ hi ▸ hj ▸ (h.of_refl hGS hHS).edgeDelete F

lemma Set.Pairwise.edgeRestrict_dup_agree {S : Set (Graph α β)} (h : S.Pairwise Dup_agree)
    (F : Set β) : ((· ↾ F) '' S).Pairwise Dup_agree :=
  fun _ ⟨_, hGS, hi⟩ _ ⟨_, hHS, hj⟩ _ ↦ hi ▸ hj ▸ (h.of_refl hGS hHS).edgeRestrict F

end Dup_agree

--  This needs Order.Frame as supposed to the others.
lemma dup_agree_iff_union_pairwiseDisjoint {α : Type*} [Order.Frame α] (G H : Graph α β) :
    G.Dup_agree H ↔ (V(G) ∪ V(H)).PairwiseDisjoint id := by
  simp [Dup_agree, onFun, Partition.agree_iff_union_pairwiseDisjoint]

end Graph
