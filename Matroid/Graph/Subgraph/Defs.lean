import Matroid.Graph.Constructions.Basic
import Matroid.ForMathlib.Set
import Matroid.ForMathlib.Function

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {Gs Hs : Set (Graph α β)} {Gι Hι : ι → Graph α β}

open Set Function

namespace Graph

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps (attr := grind =)]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E(G) ∩ E₀
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm e he x y h := ⟨h.1, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [G.exists_isLink_of_mem_edgeSet h.1, h.2],
    fun ⟨x, y, h⟩ ↦ ⟨h.2.edge_mem, h.1⟩⟩
  left_mem_of_isLink _ _ _ h := h.2.left_mem

attribute [grind =] edgeRestrict_vertexSet edgeRestrict_edgeSet edgeRestrict_isLink

/-- `G ↾ F` is the subgraph of `G` restricted to the edges in `F`. Vertices are not changed. -/
scoped infixl:65 " ↾ "  => Graph.edgeRestrict

@[simp, grind .]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  vertex_subset := rfl.le
  isLink_of_isLink := by simp

@[simp]
lemma edgeRestrict_eq_iff (G : Graph α β) (E₀ : Set β) : G ↾ E₀ = G ↔ E(G) ⊆ E₀ :=
  ⟨fun h ↦ by simpa using edgeSet_mono h.ge,
    fun h ↦ ext_of_le_le edgeRestrict_le le_rfl (by simp) (by simpa)⟩

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  ext_of_le_le (G := G) (by simp) (by simp) rfl (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F :=
  ext_of_le_le (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F := by
  rw [inter_comm, edgeRestrict_edgeSet_inter]

@[gcongr]
lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F := by
  refine G.le_of_le_le_subset_subset (edgeRestrict_le.trans h) (by simp)
    (by simpa using vertexSet_mono h) ?_
  simp [inter_subset_left.trans (edgeSet_mono h)]

@[gcongr]
lemma edgeRestrict_mono_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  vertex_subset := rfl.subset
  isLink_of_isLink _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

@[simp]
lemma edgeRestrict_inc_iff : (G ↾ F).Inc e x ↔ G.Inc e x ∧ e ∈ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeRestrict_isLoopAt_iff : (G ↾ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∈ F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_le_le ?_ (by simp) (by simp) ?_
  · exact edgeRestrict_le.trans (by simp)
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm _ F₂]

/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[simps! (attr := grind =)]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (E := E(G) \ F)
  (IsLink := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl
  (by simp [diff_subset])
  (fun e x y ↦ by
    simp only [edgeRestrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

attribute [grind =] edgeDelete_vertexSet edgeDelete_edgeSet edgeDelete_isLink

/-- `G ＼ F` is the subgraph of `G` with the edges in `F` deleted. Vertices are not changed. -/
scoped infixl:75 " ＼ "  => Graph.edgeDelete

lemma edgeDelete_eq_edgeRestrict (G : Graph α β) (F : Set β) :
    G ＼ F = G ↾ (E(G) \ F) := copy_eq ..

@[simp]
lemma edgeDelete_le : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

@[simp]
lemma edgeDelete_empty : G ＼ ∅ = G := by
  simp [edgeDelete_eq_edgeRestrict]

@[gcongr]
lemma edgeDelete_mono_left (h : H ≤ G) (F : Set β) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (E(H) \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left (edgeSet_mono h)

@[simp]
lemma edgeDelete_inc_iff : (G ＼ F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeDelete_isLoopAt_iff : (G ＼ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isLoopAt_iff, mem_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma edgeDelete_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ＼ F₂ = G ＼ (F₁ ∪ F₂) := by
  simp only [edgeDelete_eq_edgeRestrict, diff_eq_compl_inter, edgeRestrict_inter_edgeSet,
    edgeRestrict_edgeSet, edgeRestrict_edgeRestrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, edgeRestrict_inter_edgeSet, inter_comm]


/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[simps! (attr := grind =) vertexSet isLink]
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm _ _ x := by simp +contextual [G.isLink_comm (x := x)]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  left_mem_of_isLink := by simp +contextual

/-- `G[X]` is the subgraph of `G` induced by the set `X` of vertices. -/
notation:max G:1000 "[" S "]" => Graph.induce G S

lemma induce_le (hX : X ⊆ V(G)) : G[X] ≤ G :=
  ⟨hX, fun _ _ _ h ↦ h.1⟩

@[simp]
lemma induce_le_iff : G[X] ≤ G ↔ X ⊆ V(G) :=
  ⟨vertexSet_mono, induce_le⟩

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α β) (X : Set α) :
    E(G[X]) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp]
lemma induce_empty (G : Graph α β) : G[∅] = ⊥ := by
  apply Graph.ext <;> simp

@[simp]
lemma induce_vertexSet_self (G : Graph α β) : G[V(G)] = G := by
  refine G.ext_of_le_le (by simp) (by simp) rfl <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

/-- The graph obtained from `G` by deleting a set of vertices. -/
protected def vertexDelete (G : Graph α β) (X : Set α) : Graph α β := G[V(G) \ X]

/-- `G - X` is the graph obtained from `G` by deleting the set `X` of vertices. -/
instance : HSub (Graph α β) (Set α) (Graph α β) where
  hSub G X := G[V(G) \ X]

instance : HSub (Graph α β) α (Graph α β) where
  hSub G x := G - ({x} : Set α)
-- scoped notation:51 G:100 " - " S:100 => Graph.vertexDelete G S

lemma vertexDelete_def (G : Graph α β) (X : Set α) : G - X = G [V(G) \ X] := rfl

@[simp]
lemma vertexDelete_singleton (G : Graph α β) (x : α) : G - x = G - ({x} : Set α) := rfl

@[simp]
lemma vertexDelete_vertexSet (G : Graph α β) (X : Set α) : V(G - X) = V(G) \ X := rfl

@[simp]
lemma vertexDelete_isLink_iff (G : Graph α β) (X : Set α) :
    (G - X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [vertexDelete_def, induce_isLink, mem_diff, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
lemma vertexDelete_edgeSet (G : Graph α β) (X : Set α) :
    E(G - X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOf_exists_isLink]

lemma vertexDelete_edgeSet_diff (G : Graph α β) (X : Set α) : E(G - X) = E(G) \ E(G, X) := by
  ext e
  simp only [vertexDelete_edgeSet, mem_setOf_eq, mem_diff, edge_mem_iff_exists_isLink,
    mem_setIncEdges_iff, not_exists, not_and]
  refine ⟨fun ⟨x, y, hexy, hx, hy⟩ ↦ ⟨?_, fun z hz hez ↦ ?_⟩, fun ⟨⟨x, y, h⟩, h2⟩ ↦ ?_⟩
  · use x, y
  · obtain rfl | rfl := hez.eq_or_eq_of_isLink hexy <;> tauto
  have hxX := mt (h2 x) (not_not.mpr h.inc_left)
  have hyX := mt (h2 y) (not_not.mpr h.inc_right)
  use x, y

@[simp]
lemma vertexDelete_empty (G : Graph α β) : G - (∅ : Set α) = G := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_vertexSet_self (G : Graph α β) : G - V(G) = ⊥ := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_le : G - X ≤ G := G.induce_le diff_subset

lemma vertexDelete_isLink_iff' (G : Graph α β) (X : Set α) :
    (G - X).IsLink e x y ↔ G.IsLink e x y ∧ e ∉ E(G, X) := by
  refine ⟨fun h ↦ ⟨h.of_le vertexDelete_le, (G.vertexDelete_edgeSet_diff X ▸ h.edge_mem).2⟩,
    fun ⟨h, he⟩ ↦ h.of_le_of_mem vertexDelete_le ?_⟩
  rw [vertexDelete_edgeSet_diff]
  use h.edge_mem

/-! ### Strongly disjointness -/

/-- Two graphs are strongly disjoint if their edge sets and vertex sets are disjoint.
    This is a stronger notion of disjointness than `Disjoint`,
    see `disjoint_iff_vertexSet_disjoint`. -/
@[mk_iff]
structure StronglyDisjoint (G H : Graph α β) : Prop where
  vertex : Disjoint V(G) V(H)
  edge : Disjoint E(G) E(H)

@[symm]
lemma StronglyDisjoint.symm (h : G.StronglyDisjoint H) : H.StronglyDisjoint G :=
  ⟨h.1.symm, h.2.symm⟩

instance : Std.Symm (StronglyDisjoint : Graph α β → Graph α β → Prop) where
  symm _ _ := StronglyDisjoint.symm

lemma StronglyDisjoint.anti_left (h : G.StronglyDisjoint H) (h₁ : H₁ ≤ G) :
    H₁.StronglyDisjoint H where
  vertex := h.vertex.mono_left (vertexSet_mono h₁)
  edge := h.edge.mono_left (edgeSet_mono h₁)

lemma StronglyDisjoint.anti_right (h : G.StronglyDisjoint H) (h₂ : H₂ ≤ H) :
    G.StronglyDisjoint H₂ where
  vertex := h.vertex.mono_right (vertexSet_mono h₂)
  edge := h.edge.mono_right (edgeSet_mono h₂)

lemma StronglyDisjoint.anti (h : G.StronglyDisjoint H) (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ H) :
    H₁.StronglyDisjoint H₂ where
  vertex := h.vertex.mono (vertexSet_mono h₁) (vertexSet_mono h₂)
  edge := h.edge.mono (edgeSet_mono h₁) (edgeSet_mono h₂)

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

def CompatibleAt (e : β) (G H : Graph α β) : Prop := e ∈ E(G) → e ∈ E(H) → G.IsLink e = H.IsLink e

lemma compatibleAt_def :
    CompatibleAt e G H ↔ (e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y) := by
  simp [CompatibleAt, funext_iff]

@[symm]
lemma CompatibleAt.symm (h : CompatibleAt e G H) : CompatibleAt e H G :=
  fun he1 he2 ↦ (h he2 he1).symm

lemma CompatibleAt.comm : CompatibleAt e G H ↔ CompatibleAt e H G :=
  ⟨CompatibleAt.symm, CompatibleAt.symm⟩

lemma compatibleAt_self : CompatibleAt e G G := fun _ _ ↦ rfl

instance {e : β} : Std.Refl (CompatibleAt e : Graph α β → Graph α β → Prop) where
  refl _ _ _ := rfl

instance {e : β} : Std.Symm (CompatibleAt e : Graph α β → Graph α β → Prop) where
  symm _ _ := CompatibleAt.symm


/-- Two graphs are `Compatible` if the edges in their intersection agree on their ends -/
def Compatible (G H : Graph α β) : Prop := EqOn G.IsLink H.IsLink (E(G) ∩ E(H))

@[simp]
lemma Compatible.compatibleAt (h : G.Compatible H) (e : β) : CompatibleAt e G H :=
  fun heG heH ↦ h ⟨heG, heH⟩

@[simp]
lemma pairwise_compatibleAt_of_compatible (h : Pairwise (Compatible on Gι)) (e : β) :
    Pairwise (CompatibleAt e on Gι) := fun _ _ hne ↦ (h hne).compatibleAt e

@[simp]
lemma set_pairwise_compatibleAt_of_compatible (h : Gs.Pairwise Compatible) (e : β) :
    Gs.Pairwise (CompatibleAt e) := fun _ hi _ hj hne ↦ (h hi hj hne).compatibleAt e

lemma Compatible.isLink_eq (h : G.Compatible H) (heG : e ∈ E(G)) (heH : e ∈ E(H)) :
    G.IsLink e = H.IsLink e :=
  h ⟨heG, heH⟩

@[simp]
lemma compatible_self (G : Graph α β) : G.Compatible G :=
  eqOn_refl ..

instance : Std.Refl (Compatible : Graph α β → Graph α β → Prop) where
  refl G := G.compatible_self

@[symm]
lemma Compatible.symm (h : G.Compatible H) : H.Compatible G := by
  rwa [Compatible, inter_comm, eqOn_comm]

instance : Std.Symm (Compatible : Graph α β → Graph α β → Prop) where
  symm _ _ := Compatible.symm

lemma IsLink.of_compatible (h : G.IsLink e x y) (hGH : G.Compatible H) (heH : e ∈ E(H)) :
    H.IsLink e x y := by
  rwa [← hGH ⟨h.edge_mem, heH⟩]

lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H := by
  simp [Compatible, h.inter_eq]

@[simp]
lemma compatible_edgeDelete_right : G.Compatible (H ＼ E(G)) :=
  Compatible.of_disjoint_edgeSet disjoint_sdiff_right

/-- Used to simplify the definition of the union of a pair. -/
@[simp]
lemma pairwise_compatible_edgeDelete : ({G, H ＼ E(G)} : Set (Graph α β)).Pairwise Compatible := by
  simp [pairwise_iff_of_refl, compatible_edgeDelete_right.symm]

@[simp]
lemma singleEdge_compatible_iff :
    Compatible (Graph.singleEdge u v e) G ↔ (e ∈ E(G) → G.IsLink e u v) := by
  refine ⟨fun h he ↦ by simp [← h ⟨by simp, he⟩], fun h f ⟨hfe, hf⟩ ↦ ?_⟩
  obtain rfl : f = e := by simpa using hfe
  ext x y
  simp only [singleEdge_isLink, (h hf).isLink_iff]
  tauto

/-- The intersection of a nonempty family of pairwise compatible graphs.
  Remove any disagreeing edges. -/
@[simps (attr := grind =)]
protected def iInter [Nonempty ι] (G : ι → Graph α β) : Graph α β where
  vertexSet := ⋂ i, V(G i)
  edgeSet := {e | ∃ x y, ∀ i, (G i).IsLink e x y}
  IsLink e x y := ∀ i, (G i).IsLink e x y
  isLink_symm e he x y := by simp [isLink_comm]
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' :=
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

/-- The intersection of a nonempty set of pairwise compatible graphs. -/
@[simps! (attr := grind =)]
protected def sInter (s : Set (Graph α β)) (hne : s.Nonempty) : Graph α β :=
  @Graph.iInter _ _ _ hne.to_subtype (fun G : s ↦ G.1)

protected lemma sInter_le (hG : G ∈ Gs) : Graph.sInter Gs ⟨G, hG⟩ ≤ G := by
  rw [Graph.sInter]
  generalize_proofs h
  exact Graph.iInter_le (⟨G, hG⟩ : Gs)

@[simp]
protected lemma le_sInter_iff (hne : Gs.Nonempty) : H ≤ Graph.sInter Gs hne ↔ ∀ G ∈ Gs, H ≤ G := by
  simp [Graph.sInter]

/-- The intersection of two graphs `G` and `H`. There seems to be no good way to
defined junk values so that this has the right edge and vertex set, so the
edges are precisely those on which `G` and `H` agree, and the edge set is a subset
of `E(G) ∩ E(H)`,
with equality if `G` and `H` are compatible.   -/
protected def inter (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∩ V(H)
  edgeSet := {e ∈ E(G) ∩ E(H) | G.IsLink e = H.IsLink e}
  IsLink e x y := G.IsLink e x y ∧ H.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1.symm, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  edge_mem_iff_exists_isLink e := by
    simp only [edgeSet_eq_setOf_exists_isLink, mem_inter_iff, mem_setOf_eq, funext_iff, eq_iff_iff]
    exact ⟨fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩,
      fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
      fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩⟩
  left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩

instance : Inter (Graph α β) where inter := Graph.inter

@[simp]
lemma inter_vertexSet (G H : Graph α β) : V(G ∩ H) = V(G) ∩ V(H) := rfl

@[simp]
lemma inter_isLink_iff : (G ∩ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

lemma inter_edgeSet (G H : Graph α β) : E(G ∩ H) = {e ∈ E(G) ∩ E(H) | G.IsLink e = H.IsLink e} :=
  rfl

protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G :=
  Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

instance : Std.Commutative (α := Graph α β) (· ∩ ·) where
  comm G H := Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

protected lemma inter_assoc (G H I : Graph α β) : (G ∩ H) ∩ I = G ∩ (H ∩ I) :=
  Graph.ext (Set.inter_assoc ..) <| by simp [and_assoc]

instance : Std.Associative (α := Graph α β) (· ∩ ·) where
  assoc _ _ _ := Graph.ext (Set.inter_assoc ..) <| by simp [and_assoc]

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

-- protected def iUnion' (G : ι → Graph α β) : Graph α β where
--   vertexSet := ⋃ i, V(G i)
--   IsLink e x y := (∃ i, (G i).IsLink e x y) ∧ Pairwise ((CompatibleAt e) on G)
--   isLink_symm := fun e he x y ⟨⟨i, hi⟩, h'⟩ ↦ ⟨⟨i, hi.symm⟩, h'⟩
--   eq_or_eq_of_isLink_of_isLink := by
--     refine fun e x y v w ⟨⟨i, hi⟩, h⟩ ⟨⟨j, hj⟩, _⟩ ↦ ?_
--     rw [← h.of_refl i j hi.edge_mem hj.edge_mem] at hj
--     exact hi.left_eq_or_eq hj
--   left_mem_of_isLink := fun e x y ⟨⟨i, hi⟩,h⟩ ↦ mem_iUnion.2 ⟨i, hi.left_mem⟩

/-- The union of an indexed family of pairwise compatible graphs. -/
@[simps (attr := grind =)]
protected def iUnion (G : ι → Graph α β) (hG : Pairwise (Graph.Compatible on G)) : Graph α β where
  vertexSet := ⋃ i, V(G i)
  edgeSet := ⋃ i, E(G i)
  IsLink e x y := ∃ i, (G i).IsLink e x y
  isLink_symm := by simp +contextual [Symmetric, isLink_comm]
  eq_or_eq_of_isLink_of_isLink :=
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

/-- The union of a set of pairwise compatible graphs. -/
@[simps! (attr := grind =)]
protected def sUnion (s : Set (Graph α β)) (hs : s.Pairwise Compatible) : Graph α β :=
  .iUnion (fun G : s ↦ G.1) <| (pairwise_subtype_iff_pairwise_set s Compatible).2 hs

protected lemma le_sUnion (hGs : Gs.Pairwise Graph.Compatible) (hG : G ∈ Gs) :
    G ≤ Graph.sUnion Gs hGs := by
  convert Graph.le_iUnion (ι := Gs) _ ⟨G, hG⟩
  rfl

@[simp]
protected lemma sUnion_le_iff (hGs : Gs.Pairwise Graph.Compatible) :
    Graph.sUnion Gs hGs ≤ H ↔ ∀ G ∈ Gs, G ≤ H := by
  simp [Graph.sUnion]

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

lemma union_isLink_iff : (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ (H.IsLink e x y ∧ e ∉ E(G)) := by
  simp [union_eq_sUnion]

@[simp]
protected lemma left_le_union (G H : Graph α β) : G ≤ G ∪ H := by
  simp_rw [le_iff, union_isLink_iff]
  tauto

protected lemma union_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) : H₁ ∪ H₂ ≤ G := by
  simp [union_eq_sUnion, h₁, edgeDelete_le.trans h₂]

lemma union_le_iff {H₁ H₂ : Graph α β} : H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ＼ E(H₁) ≤ G := by
  simp [union_eq_sUnion]

@[simp]
protected lemma union_self (G : Graph α β) : G ∪ G = G :=
  (Graph.union_le le_rfl le_rfl).antisymm <| Graph.left_le_union ..

protected lemma union_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ∪ G₂) ∪ G₃ = G₁ ∪ (G₂ ∪ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [union_isLink_iff]
  tauto

instance : Std.Associative (α := Graph α β) (· ∪ ·) where
  assoc := Graph.union_assoc

lemma Compatible.union_isLink_iff (h : G.Compatible H) :
    (G ∪ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.union_isLink_iff, heG, not_true_eq_false, and_false, or_false, iff_self_or]
    exact fun he ↦ by rwa [h.isLink_eq heG he.edge_mem]
  simp [heG, Graph.union_isLink_iff]

lemma Compatible.union_comm (h : Compatible G H) : G ∪ H = H ∪ G :=
  Graph.ext (Set.union_comm ..)
    fun _ _ _ ↦ by rw [h.union_isLink_iff, h.symm.union_isLink_iff, or_comm]

lemma Compatible.right_le_union (h : G.Compatible H) : H ≤ G ∪ H := by
  simp [h.union_comm]

lemma Compatible.union_eq_sUnion (h : G.Compatible H) :
    G ∪ H = Graph.sUnion {G, H} (by simp [Set.pairwise_iff_of_refl, h, h.symm]) :=
  Graph.ext (by simp) fun e x y ↦ by simp [h.union_isLink_iff]

lemma Compatible.union_le_iff {H₁ H₂ : Graph α β} (h_compat : H₁.Compatible H₂) :
    H₁ ∪ H₂ ≤ G ↔ H₁ ≤ G ∧ H₂ ≤ G := by
  simp [h_compat.union_eq_sUnion]

/-- Add a new edge `e` between vertices `a` and `b`. If `e` is already in the graph,
its ends change to `a` and `b`. -/
@[simps! (attr := grind =) edgeSet vertexSet]
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
    mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  obtain rfl | hne := eq_or_ne e f
  · have hl : ¬ G.IsLink e x y := fun h ↦ he h.edge_mem
    simp only [true_and, not_true_eq_false, hl, and_self, or_false]
    tauto
  simp [hne.symm]

lemma addEdge_le (hle : H ≤ G) (he : G.IsLink e x y) : H.addEdge e x y ≤ G :=
  Graph.union_le (by simpa) hle

lemma le_addEdge (he : e ∉ E(G)) : G ≤ G.addEdge e x y :=
  Compatible.right_le_union <| by simp [he]

lemma addEdge_eq_self (hbtw : G.IsLink e x y) : G.addEdge e x y = G :=
  le_antisymm (addEdge_le (by simp) hbtw) <| Compatible.right_le_union <| by simp [hbtw]

lemma addEdge_idem : (G.addEdge e x y).addEdge e x y = G.addEdge e x y :=
  addEdge_eq_self <| addEdge_isLink G e x y

end Graph
