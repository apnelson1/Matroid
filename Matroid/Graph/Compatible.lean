import Matroid.Graph.Operations.Delete
import Matroid.ForMathlib.Partition.Lattice

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

open scoped Sym2 Graph

namespace Graph

-- /-! ### Strongly disjointness -/

-- /-- Two graphs are strongly disjoint if their edge sets and vertex sets are disjoint.
--     This is a stronger notion of disjointness than `Disjoint` derived from `≤` relation,
--     see `disjoint_iff_vertexSet_disjoint`. -/
-- @[mk_iff]
-- structure StronglyDisjoint (G H : Graph α β) : Prop where
--   vertex : Disjoint V(G) V(H)
--   edge : Disjoint E(G) E(H)

-- lemma StronglyDisjoint.symm (h : G.StronglyDisjoint H) : H.StronglyDisjoint G :=
--   ⟨h.1.symm, h.2.symm⟩

-- lemma stronglyDisjoint_comm : G.StronglyDisjoint H ↔ H.StronglyDisjoint G :=
--   ⟨StronglyDisjoint.symm, StronglyDisjoint.symm⟩

-- lemma stronglyDisjoint_iff_of_le_isLabelSubgraph (h₁ : H₁ ≤ G) (h₂ : H₂ ≤l G) :
--     StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ := by
--   refine ⟨(disjoint_iff_vertexSet_disjoint.mp <| StronglyDisjoint.vertex ·),
--     fun h ↦ ⟨h.vertexSet_disjoint, disjoint_left.2 fun e he₁ he₂ ↦ ?_⟩⟩
--   obtain ⟨x, y, he₁⟩ := exists_isLink_of_mem_edgeSet he₁
--   exact h.vertexSet_disjoint.notMem_of_mem_left he₁.left_mem <|
--     (he₁.of_le h₁).of_isLabelSubgraph_of_mem h₂ he₂ |>.left_mem

-- lemma stronglyDisjoint_iff_of_isLabelSubgraph_le (h₁ : H₁ ≤l G) (h₂ : H₂ ≤ G) :
--     StronglyDisjoint H₁ H₂ ↔ Disjoint H₁ H₂ :=
--   stronglyDisjoint_comm.trans <|
--     (stronglyDisjoint_iff_of_le_isLabelSubgraph h₂ h₁).trans disjoint_comm

-- lemma StronglyDisjoint.disjoint (h : G.StronglyDisjoint H) : Disjoint G H :=
--   disjoint_iff_vertexSet_disjoint.mp h.vertex

/-! ### Compatibility -/

def CompatibleAt (e : β) (G H : Graph α β) : Prop :=
  e ∈ E(G) → e ∈ E(H) → ∀ ⦃x y⦄, G.IsLink e x y ↔ H.IsLink e x y

lemma CompatibleAt.symm (h : CompatibleAt e G H) : CompatibleAt e H G :=
  fun he1 he2 _ _ ↦ (@h he2 he1 _ _).symm

lemma CompatibleAt.comm : CompatibleAt e G H ↔ CompatibleAt e H G :=
  ⟨CompatibleAt.symm, CompatibleAt.symm⟩

lemma compatibleAt_self : CompatibleAt e G G := fun _ _ _ _ ↦ Iff.rfl

instance {e : β} : IsRefl (Graph α β) (CompatibleAt e) := ⟨fun _ _ _ _ _ ↦ Iff.rfl⟩

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

-- lemma IsLink.compatibleAt_iff_left (hIsLink : G.IsLink e x y) :
--     CompatibleAt e G H ↔ (e ∈ E(H) → H.IsLink e x y) :=
--   ⟨fun h heH ↦ by rwa [← CompatibleAt.isLink_iff h hIsLink.edge_mem heH], fun h heG heH ↦
--   (isLink_eq_isLink_iff_exists_isLink_of_mem_edgeSet heG).mpr ⟨x, y, hIsLink, h heH⟩⟩

-- lemma IsLink.compatibleAt_iff_right (h : H.IsLink e x y) :
--     CompatibleAt e G H ↔ (e ∈ E(G) → G.IsLink e x y) := by
--   rw [CompatibleAt.comm]
--   exact compatibleAt_iff_left h

lemma IsLink.of_compatibleAt (he : G.IsLink e x y) (h : CompatibleAt e G H) (heH : e ∈ E(H)) :
    H.IsLink e x y := (h he.edge_mem heH).mp he

lemma CompatibleAt.mono_left {G₀ : Graph α β} (h : CompatibleAt e G H) (hle : G₀ ≤ G) :
    CompatibleAt e G₀ H := by
  rintro heG₀ heH - -
  rw [← h (edgeSet_mono hle heG₀) heH, isLink_iff_isLink_of_le_of_mem hle heG₀]

lemma CompatibleAt.mono_right {H₀ : Graph α β} (h : CompatibleAt e G H) (hH₀ : H₀ ≤ H) :
    CompatibleAt e G H₀ := (h.symm.mono_left hH₀).symm

lemma CompatibleAt.mono {G₀ H₀ : Graph α β} (h : CompatibleAt e G H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    CompatibleAt e G₀ H₀ := (h.mono_left hG).mono_right hH

-- lemma CompatibleAt.induce_left (h : CompatibleAt e G H) (X : Set α) : CompatibleAt e G[X] H := by
--   rintro ⟨x, y, ⟨hl, hxX, hyX⟩⟩ heH u v huX huH hvX hvH
--   rw [← h hl.edge_mem heH, induce_isLink_iff, hl.isLink_iff]
--   aesop

-- lemma CompatibleAt.induce_right (h : CompatibleAt e G H) (X : Set α) :
--     CompatibleAt e G H[X] :=
--   (h.symm.induce_left X).symm

-- lemma CompatibleAt.induce (h : CompatibleAt e G H) {X : Set α} : CompatibleAt e G[X] H[X] :=
--   (h.induce_left X).induce_right X

/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop :=
  ∀ ⦃e x y⦄, e ∈ E(G) ∩ E(H) → (G.IsLink e x y ↔ H.IsLink e x y)

lemma Compatible.isLink_eq (h : G.Compatible H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y := h ⟨heG, heH⟩

lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ _ _ ⟨heG, heH⟩ ↦ h ⟨heH, heG⟩ |>.symm

instance : IsSymm (Graph α β) Compatible where
  symm _ _ := Compatible.symm

@[simp]
lemma compatible_symmetric : Symmetric (@Compatible α β) :=
  fun _ _ ↦ Compatible.symm

lemma compatible_comm : G.Compatible H ↔ H.Compatible G :=
  ⟨Compatible.symm, Compatible.symm⟩

/-- Two subgraphs of the same graph are compatible. -/
lemma compatible_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁.Compatible H₂ :=
  fun _ _ _ ⟨he₁, he₂⟩ ↦ by
    rw [← isLink_iff_isLink_of_le_of_mem h₁ he₁, ← isLink_iff_isLink_of_le_of_mem h₂ he₂]

lemma compatible_of_le (h : H ≤ G) : H.Compatible G := compatible_of_le_le h le_rfl

lemma IsLink.of_compatible (h : G.IsLink e x y) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLink e x y := by rwa [← hGH ⟨h.edge_mem, heH⟩]

lemma Inc.of_compatible (h : G.Inc e x) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

@[simp]
lemma compatible_self (G : Graph α β) : G.Compatible G :=
  fun _ _ _ _ ↦ Iff.rfl

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
    Compatible G₀ H :=  fun _ _ _ ⟨he₀, heH⟩ ↦ by
    rw [← h ⟨edgeSet_mono hG₀ he₀, heH⟩, isLink_iff_isLink_of_le_of_mem hG₀ he₀]

lemma Compatible.mono_right {H₀ : Graph α β} (h : Compatible G H) (hH₀ : H₀ ≤ H) :
    Compatible G H₀ := (h.symm.mono_left hH₀).symm

lemma Compatible.mono {G₀ H₀ : Graph α β} (h : G.Compatible H) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    G₀.Compatible H₀ := (h.mono_left hG).mono_right hH

-- lemma Compatible.induce_left (h : Compatible G H) (X : Set α) : G[X].Compatible H := by
--   intro e x y ⟨heG, heX⟩ ⟨hxG, hxH⟩ ⟨hyG, hyH⟩
--   obtain ⟨u, v, heuv : G.IsLink e u v, hu, hv⟩ := heG
--   simp only [induce_isLink_iff]
--   intro h
--   obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.dup_and_dup_or_dup_and_dup heuv <;> simp_all

-- lemma Compatible.induce_right (h : Compatible G H) (X : Set α) :
--     G.Compatible H[X] :=
--   (h.symm.induce_left X).symm

-- lemma Compatible.induce (h : Compatible G H) {X : Set α} : G[X].Compatible H[X] :=
--   (h.induce_left X).induce_right X

lemma Compatible.vertexDelete (h : Compatible G H) {X : Set α} : (G - X).Compatible (H - X) :=
  fun _ _ _ ⟨heG, heH⟩ ↦ by
    simp only [vertexDelete_isLink, and_congr_left_iff, and_imp]
    exact fun _ _ => h ⟨vertexDelete_isLabelSubgraph.edgeSet heG,
      vertexDelete_isLabelSubgraph.edgeSet heH⟩

lemma Compatible.edgeDelete (h : Compatible G H) {F : Set β} : (G ＼ F).Compatible (H ＼ F) :=
  h.mono edgeDelete_le edgeDelete_le

lemma Compatible.edgeRestrict (h : Compatible G H) {F : Set β} : (G ↾ F).Compatible (H ↾ F) :=
  h.mono edgeRestrict_le edgeRestrict_le

-- @[simp]
-- lemma Compatible.induce_induce : G[X].Compatible G[Y] :=
--   Compatible.induce_left (Compatible.induce_right G.compatible_self _) _

-- lemma Compatible.stronglyDisjoint_of_vertexSet_disjoint (h : G.Compatible H)
--     (hV : Disjoint V(G) V(H)) : G.StronglyDisjoint H := by
--   refine ⟨hV, disjoint_left.2 fun e he he' ↦ ?_⟩
--   obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet he
--   exact hV.notMem_of_mem_left hexy.left_mem (h ⟨he, he'⟩ ▸ hexy).left_mem

-- lemma Compatible.disjoint_iff_vertexSet_disjoint (h : G.Compatible H) :
--     G.StronglyDisjoint H ↔ Disjoint V(G) V(H) :=
--   ⟨(·.vertex), h.stronglyDisjoint_of_vertexSet_disjoint⟩

-- lemma StronglyDisjoint.compatible (h : G.StronglyDisjoint H) : G.Compatible H :=
--   Compatible.of_disjoint_edgeSet h.edge

lemma Compatible.edgeSet_disjoint_of_vertexSet_disjoint (h : G.Compatible H)
    (hV : Disjoint V(G) V(H)) : Disjoint E(G) E(H) := by
  by_contra he
  obtain ⟨e, heG, heH⟩ := not_disjoint_iff.mp he
  obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet heG
  exact hV.notMem_of_mem_left hexy.left_mem <| hexy.of_compatible h heH |>.left_mem

-- lemma stronglyDisjoint_iff_vertexSet_disjoint_compatible :
--     G.StronglyDisjoint H ↔ Disjoint V(G) V(H) ∧ G.Compatible H :=
--   ⟨fun h => ⟨h.vertex, h.compatible⟩,
--     fun ⟨hdisj, hco⟩ => ⟨hdisj, hco.edgeSet_disjoint_of_vertexSet_disjoint hdisj⟩⟩

lemma pairwise_compatible_const (G : Graph α β) : Pairwise (Compatible on fun (_ : ι) ↦ G) := by
  simp [Pairwise]

lemma pairwise_compatible_comp {ι ι' : Type*} {G : ι → Graph α β} (hG : Pairwise (Compatible on G))
    (f : ι' → ι): Pairwise (Compatible on (G ∘ f)) := by
  rw [onFun_comp]
  exact Pairwise.onFun_of_refl hG

-- /-- useful with `Pairwise` and `Set.Pairwise`.-/
-- @[simp]
-- lemma stronglyDisjoint_le_compatible : @StronglyDisjoint α β ≤ Compatible :=
--   fun _ _ ↦ StronglyDisjoint.compatible

-- def dup_compatible (G H : Graph α β) : Prop :=
--   ∀ ⦃x y⦄, x ∈ V(G) ∩ V(H) → G.Dup x y ↔ H.Dup x y

-- lemma exists_subsetSup_of_dup_compatible (h : dup_compatible G H) :
--     ∃ P : Partition (Set α), G.Dup ⊆ P ∧ H.Dup ⊆ P := by
--   use G.Dup ⊔ H.Dup, ?_, ?_
--   · rw [Partition.subset_iff_rel]
--     intro x y hx


-- def Unionable (G H : Graph α β) : Prop :=
--   ∃ G' : Graph α β, G ≤ G' ∧ H ≤ G'

-- lemma Unionable.dup_agree (h : G.Unionable H) : G.Dup.Agree H.Dup := by
--   obtain ⟨G', hG, hH⟩ := h
--   exact ⟨G'.Dup, hG.dup_subset, hH.dup_subset⟩

-- lemma unionable_rfl : G.Unionable G := ⟨G, le_rfl, le_rfl⟩

-- instance : IsRefl (Graph α β) Unionable where
--   refl _ := unionable_rfl

-- lemma Unionable.symm (h : G.Unionable H) : H.Unionable G := by
--   obtain ⟨G', hG, hH⟩ := h
--   exact ⟨G', hH, hG⟩

-- lemma unionable_comm : G.Unionable H ↔ H.Unionable G := ⟨Unionable.symm, Unionable.symm⟩

-- instance : IsSymm (Graph α β) Unionable := ⟨fun _ _ ↦ Unionable.symm⟩

-- lemma Unionable.trans_left {a b c : α} (h : G.Unionable H) (hab : G.Dup a b) (hbc : H.Dup b c) :
--     G.Dup a c :=
--   trans' hab <| Partition.Agree_iff_rel.mp h.dup_agree b c hab.right_mem hbc.left_mem |>.mpr hbc

-- lemma Unionable.trans_right {a b c : α} (h : G.Unionable H) (hab : G.Dup a b) (hbc : H.Dup b c) :
--     H.Dup a c := trans' (Partition.Agree_iff_rel.mp h.dup_agree b a hab.right_mem hbc.left_mem
--     |>.mp hab.symm).symm hbc

-- instance (h : G.Unionable H) : Trans G.Dup H.Dup G.Dup where
--   trans := h.trans_left

-- instance (h : G.Unionable H) : Trans G.Dup H.Dup H.Dup where
--   trans := h.trans_right

-- lemma compatible_of_unionable

def Dup_agree (G H : Graph α β) : Prop := G.Dup.Agree H.Dup

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

lemma Dup_agree_comm : G.Dup_agree H ↔ H.Dup_agree G :=
  ⟨Dup_agree.symm, Dup_agree.symm⟩

-- lemma Dup_agree.trans_left {a b c : α} (h : G.Dup_agree H) (hab : G.Dup a b) (hbc : H.Dup b c) :
--     G.Dup a c :=
--   Partition.Agree.trans_left h hab hbc

-- lemma Dup_agree.trans_right {a b c : α} (h : G.Dup_agree H) (hab : G.Dup a b) (hbc : H.Dup b c) :
--     H.Dup a c :=
--   trans' (Partition.agree_iff_rel.mp h _ _ hab.right_mem hbc.left_mem |>.mp hab.symm).symm hbc

@[simp]
lemma dup_agree_of_nodup [Nodup G] [Nodup H] : G.Dup_agree H := by
  simp [Dup_agree]

@[simp]
lemma pairwise_dup_agree_of_nodup {G : ι → Graph α β} [∀ i, Nodup (G i)] :
    Pairwise (Dup_agree on G) := by
  simp [Pairwise, dup_agree_of_nodup]

@[simp]
lemma dup_of_pairwise_dup_agree_of_mem {G : ι → Graph α β} (h : Pairwise (Dup_agree on G))
    {i : ι} (hi : x ∈ V(G i)) : (⨆ j, (G j).Dup) x y ↔ (G i).Dup x y := by
  rw [Partition.iSup_rel, iff_comm]
  refine ⟨fun h => Relation.TransGen.single ?_, fun h => ?_⟩
  · simp only [iSup_apply, iSup_Prop_eq]
    use i
  induction h with
  | single hxy =>
    simp only [iSup_apply, iSup_Prop_eq] at hxy
    obtain ⟨j, hxy⟩ := hxy
    exact (h.of_refl i j).trans_left (dup_refl_iff.mpr hi) hxy
  | tail h1 h2 IH =>
    obtain ⟨j, h2⟩ := by simpa using h2
    exact (h.of_refl i j).trans_left IH h2



end Graph
