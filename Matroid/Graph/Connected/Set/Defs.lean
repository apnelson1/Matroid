import Matroid.Graph.Connected.Vertex.Defs
import Matroid.ForMathlib.Partition.Set

open Set Function Nat WList

variable {α β ι : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {C U V S S' T T' X Y : Set α} {F F' R R': Set β} {W P Q : WList α β}

namespace Graph

/-! ### Connectivity between two sets -/

def SetConnected (G : Graph α β) (S T : Set α) : Prop :=
  ∃ s ∈ S, ∃ t ∈ T, G.ConnBetween s t

@[simp]
lemma SetConnected_singleton (G : Graph α β) (s t : α) :
    G.SetConnected {s} {t} ↔ G.ConnBetween s t := by
  refine ⟨?_, fun h => ⟨s, rfl, t, rfl, h⟩⟩
  rintro ⟨s, rfl, t, rfl, hst⟩
  exact hst

lemma SetConnected.of_le (h : G.SetConnected S T) (hle : G ≤ H) : H.SetConnected S T := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hs, t, ht, hst.of_le hle⟩

lemma SetConnected.subset_left (h : G.SetConnected S T) (hS : S ⊆ S') : G.SetConnected S' T := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hS hs, t, ht, hst.of_le (by simp)⟩

lemma SetConnected.subset_right (h : G.SetConnected S T) (hT : T ⊆ T') : G.SetConnected S T' := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hs, t, hT ht, hst.of_le (by simp)⟩

lemma SetConnected.subset (h : G.SetConnected S T) (hS : S ⊆ S') (hT : T ⊆ T') :
    G.SetConnected S' T' :=
  h.subset_left hS |>.subset_right hT

lemma SetConnected.vertexSet_inter_left (h : G.SetConnected S T) : G.SetConnected (V(G) ∩ S) T := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, ⟨hst.left_mem, hs⟩, t, ht, hst.of_le (by simp)⟩

lemma SetConnected.vertexSet_inter_right (h : G.SetConnected S T) :
    G.SetConnected S (V(G) ∩ T) := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hs, t, ⟨hst.right_mem, ht⟩, hst.of_le (by simp)⟩

lemma SetConnected.vertexSet_inter (h : G.SetConnected S T) :
    G.SetConnected (V(G) ∩ S) (V(G) ∩ T) :=
  h.vertexSet_inter_left.vertexSet_inter_right

lemma IsWalkFrom.SetConnected (hW : G.IsWalkFrom S T W) : G.SetConnected S T := by
  use W.first, hW.first_mem, W.last, hW.last_mem, W, hW.isWalk

lemma setConnected_iff_exists_isWalkFrom (S T : Set α) :
    G.SetConnected S T ↔ ∃ W, G.IsWalkFrom S T W := by
  refine ⟨?_, fun ⟨W, hW⟩ => ?_⟩
  · rintro ⟨_, _, _, _, w, hw, rfl, rfl⟩
    use w, hw
  · use W.first, hW.first_mem, W.last, hW.last_mem, W, hW.isWalk

lemma setConnected_iff_exists_isPathFrom (S T : Set α) :
    G.SetConnected S T ↔ ∃ P, G.IsPathFrom S T P := by
  classical
  refine ⟨?_, fun ⟨P, hP⟩ => hP.isWalkFrom.SetConnected⟩
  rintro ⟨s, hs, t, ht, h⟩
  obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
  exact ⟨P.extractPathFrom S T, hP.extractPathFrom_isPathFrom hs ht⟩

lemma ConnBetween.neighbor_setConnected (h : G.ConnBetween s t) (hne : s ≠ t)
    (hadj : ¬ G.Adj s t) : (G - {s, t}).SetConnected (N(G, s) \ {s}) (N(G, t) \ {t}) := by
  obtain ⟨w, hw, rfl, rfl⟩ := h.exists_isPath
  obtain ⟨x, e, w', f, y, rfl⟩ := (hw.isWalk.nontrivial_of_ne_not_adj hne hadj).exists_cons_concat
  obtain ⟨⟨hw', hf, hyw'⟩, he, hxw', hxy⟩ := by simpa using hw
  simp only [first_cons, last_cons, concat_last]
  use w'.first, ⟨⟨e, he⟩, (hxw' <| · ▸ first_mem)⟩, w'.last, ⟨⟨f, hf.symm⟩, (hyw' <| · ▸ last_mem)⟩,
    w', by simp [hw'.isWalk, hxw', hyw']

/-! ### Cut between two sets -/

structure IsSetCut (G : Graph α β) (S T : Set α) (C : Set α) where
  subset_vertexSet : C ⊆ V(G)
  ST_disconnects : ¬ (G - C).SetConnected S T

lemma isSetCut_empty (h : ¬ G.SetConnected S T) : G.IsSetCut S T ∅ := by
  use empty_subset _
  simpa using h

lemma left_isSetCut (G : Graph α β) (S T : Set α) : G.IsSetCut S T (V(G) ∩ S) where
  subset_vertexSet := inter_subset_left
  ST_disconnects := by
    simp only [SetConnected, vertexDelete_vertexSet_inter, not_exists, not_and]
    rintro s hs t ht h
    have := by simpa using h.left_mem
    exact this.2 hs

lemma right_isSetCut (G : Graph α β) (S T : Set α) : G.IsSetCut S T (V(G) ∩ T) where
  subset_vertexSet := inter_subset_left
  ST_disconnects := by
    simp only [SetConnected, vertexDelete_vertexSet_inter, not_exists, not_and]
    rintro s hs t ht h
    have := by simpa using h.right_mem
    exact this.2 ht

lemma IsSetCut.of_le (h : G.IsSetCut S T C) (hle : H ≤ G) : H.IsSetCut S T (V(H) ∩ C) where
  subset_vertexSet := inter_subset_left
  ST_disconnects hH := by
    rw [vertexDelete_vertexSet_inter] at hH
    exact h.ST_disconnects <| hH.of_le (vertexDelete_mono_left hle C)

lemma IsSetCut.subset_left (h : G.IsSetCut S T C) (hS : S' ⊆ S) : G.IsSetCut S' T C where
  subset_vertexSet := h.subset_vertexSet.trans (by simp)
  ST_disconnects hH := h.ST_disconnects <| hH.subset_left hS

lemma IsSetCut.subset_right (h : G.IsSetCut S T C) (hT : T' ⊆ T) : G.IsSetCut S T' C where
  subset_vertexSet := h.subset_vertexSet.trans (by simp)
  ST_disconnects hH := h.ST_disconnects <| hH.subset_right hT

lemma IsSetCut.subset (h : G.IsSetCut S T C) (hS : S' ⊆ S) (hT : T' ⊆ T) : G.IsSetCut S' T' C :=
  h.subset_left hS |>.subset_right hT

lemma IsSetCut.of_vertexDelete (h : (G - X).IsSetCut S T C) : G.IsSetCut S T ((X ∩ V(G)) ∪ C) where
  subset_vertexSet := by
    simp only [union_subset_iff, inter_subset_right, true_and]
    exact h.subset_vertexSet.trans (by simp [diff_subset])
  ST_disconnects h1 := by
    refine h.ST_disconnects ?_
    convert h1 using 1
    rw [vertexDelete_vertexDelete, ← vertexDelete_vertexSet_inter, inter_comm,
      union_inter_distrib_right]
    congr
    exact inter_eq_left.mpr <| h.subset_vertexSet.trans (by simp [diff_subset])

@[simps]
lemma IsSetCut.of_vertexDelete' (hC : (G - X).IsSetCut S T C) :
    G.IsSetCut (S ∪ X) (T ∪ X) ((X ∩ V(G)) ∪ C) where
  subset_vertexSet := by
    simp only [union_subset_iff, inter_subset_right, true_and]
    exact hC.subset_vertexSet.trans <| (G.vertexDelete_vertexSet X) ▸ diff_subset
  ST_disconnects := by
    rintro ⟨s, hs, t, ht, h⟩
    have hl := h.left_mem
    have hr := h.right_mem
    simp only [vertexDelete_vertexSet, mem_diff, mem_union, mem_inter_iff, not_or, not_and] at hl hr
    obtain hs | hs := hs.symm
    · tauto
    obtain ht | ht := ht.symm
    · tauto
    exact hC.of_vertexDelete.ST_disconnects ⟨s, hs, t, ht, h⟩

lemma IsWalkFrom.not_disjoint_isSetCut (hW : G.IsWalkFrom S T W) (hC : G.IsSetCut S T C) :
    ¬ Disjoint V(W) C := by
  refine fun hdisj ↦ hC.ST_disconnects ⟨W.first, hW.first_mem, W.last, hW.last_mem, ?_⟩
  use W, hW.isWalk.vertexDelete hdisj

lemma IsWalkFrom.exists_mem_isSetCut (hW : G.IsWalkFrom S T W) (hC : G.IsSetCut S T C) :
    ∃ v ∈ V(W), v ∈ C := by
  have := hW.not_disjoint_isSetCut hC
  rwa [not_disjoint_iff] at this

lemma IsSetCut.inter_subset (hC : G.IsSetCut S T C) : V(G) ∩ S ∩ T ⊆ C := by
  rintro x ⟨⟨hx, hxS⟩, hxT⟩
  have hw : G.IsWalkFrom S T (nil x) := ⟨by simpa, hxS, hxT⟩
  obtain ⟨v, hv, hvC⟩ := hw.exists_mem_isSetCut hC
  simp_all

lemma CutBetween.isSetCut (C : G.CutBetween s t) : G.IsSetCut (insert s C) (insert t C) C where
  subset_vertexSet x hxC := C.coe_subset hxC
  ST_disconnects h := by
    have hs : (V(G - C) ∩ insert s ↑C) ⊆ {s} := by
      rintro x
      simp +contextual
    have ht : (V(G - C) ∩ insert t ↑C) ⊆ {t} := by
      rintro x
      simp +contextual
    have := h.vertexSet_inter.subset hs ht
    rw [SetConnected_singleton] at this
    exact C.not_connBetween this

structure IsEdgeSetCut (G : Graph α β) (S T : Set α) (C : Set β) where
  subset_edgeSet : C ⊆ E(G)
  ST_disconnects : ¬ (G ＼ C).SetConnected S T

lemma isEdgeSetCut_empty (h : ¬ G.SetConnected S T) : G.IsEdgeSetCut S T ∅ where
  subset_edgeSet := empty_subset _
  ST_disconnects := by simpa using h

lemma IsWalkFrom.not_disjoint_isEdgeSetCut (hW : G.IsWalkFrom S T W) (hC : G.IsEdgeSetCut S T F) :
    ¬ Disjoint E(W) F := by
  intro hdisj
  apply hC.ST_disconnects ⟨W.first, hW.first_mem, W.last, hW.last_mem, ?_⟩
  use W, hW.isWalk.edgeDelete hdisj

lemma IsWalkFrom.exists_mem_isEdgeSetCut (hW : G.IsWalkFrom S T W) (hC : G.IsEdgeSetCut S T F) :
    ∃ e ∈ E(W), e ∈ F := by
  have := hW.not_disjoint_isEdgeSetCut hC
  rwa [not_disjoint_iff] at this

lemma IsEdgeSetCut.disjoint (hF : G.IsEdgeSetCut S T F) : Disjoint V(G) (S ∩ T) := by
  by_contra! h
  rw [not_disjoint_iff] at h
  obtain ⟨x, hx, hxS, hxT⟩ := h
  exact hF.ST_disconnects ⟨x, hxS, x, hxT, by simpa⟩

lemma not_isEdgeSetCut_of_not_disjoint (hdj : ¬ Disjoint V(G) (S ∩ T)) : ¬ G.IsEdgeSetCut S T F :=
  mt IsEdgeSetCut.disjoint hdj

open Notation in
private lemma inc_vert_foo : ∀ e ∈ E(G) ∩ F, ∃ x ∈ inc_vert '' (E(G) ↓∩ F), G.Inc e x := by
  rintro e ⟨he, heF⟩
  use inc_vert ⟨e, he⟩
  simp only [mem_image, mem_preimage, Subtype.exists, exists_and_left, inc_vert_inc ⟨e, he⟩,
    and_true]
  use e, heF, he

open Notation in
noncomputable def IsEdgeSetCut.isSetCut (hF : G.IsEdgeSetCut S T F) :
    G.IsSetCut S T (inc_vert '' (E(G) ↓∩ F)) where
  subset_vertexSet := by
    rintro x ⟨e, he, rfl⟩
    exact inc_vert_mem e
  ST_disconnects h := hF.ST_disconnects <| h.of_le <| G.vertexDelete_le_edgeDelete inc_vert_foo

/-! ### Ensemble of paths between two sets -/

structure SetEnsemble (G : Graph α β) where
  paths : Set (WList α β)
  disjoint : paths.Pairwise (Disjoint on WList.vertexSet)
  valid : ∀ ⦃P⦄, P ∈ paths → G.IsPath P

namespace SetEnsemble
variable {A : G.SetEnsemble}

def between (A : G.SetEnsemble) (S T : Set α) :=
    ∀ ⦃P⦄, P ∈ A.paths → G.IsPathFrom S T P

def vertexPartition (A : G.SetEnsemble) : Partition (Set α) :=
  Partition.ofPairwiseDisjoint' (parts := WList.vertexSet '' A.paths) (by
    rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hPQ
    refine A.disjoint hP hQ (hPQ <| · ▸ rfl)) (by
    rintro _ ⟨P, hP, rfl⟩
    rw [bot_eq_empty, ← Set.nonempty_iff_ne_empty]
    exact ⟨P.first, P.first_mem⟩)

@[simp]
lemma vertexSet_mem_vertexPartition (A : G.SetEnsemble) (hP : P ∈ A.paths) :
    V(P) ∈ A.vertexPartition := by
  use P

def vertexSet (A : G.SetEnsemble) : Set α :=
  A.vertexPartition.supp

@[simp]
lemma mem_vertexSet_iff (A : G.SetEnsemble) :
    v ∈ A.vertexSet ↔ ∃ P ∈ A.paths, v ∈ P := by
  refine ⟨fun ⟨V, hV, hv⟩ ↦ ?_, fun ⟨P, hP, hvP⟩ ↦ ⟨V(P), (by use P), hvP⟩⟩
  obtain ⟨P, hP, rfl⟩ := by simpa [vertexPartition] using hV
  use P, hP, hv

@[simp]
lemma subset_vertexSet_of_mem (hP : P ∈ A.paths) :
    V(P) ⊆ A.vertexSet :=
  fun _ hvP ↦ A.mem_vertexSet_iff.mpr ⟨P, hP, hvP⟩

lemma vertexSet_subset (A : G.SetEnsemble) : A.vertexSet ⊆ V(G) := by
  rintro v
  simp only [mem_vertexSet_iff, forall_exists_index, and_imp]
  exact fun _ hP hvP ↦ (A.valid hP).vertexSet_subset hvP

lemma vertexSet_eq_biUnion (A : G.SetEnsemble) : A.vertexSet = ⋃ P ∈ A.paths, V(P) := by
  ext v
  simp

lemma image_first_subset (A : G.SetEnsemble) : first '' A.paths ⊆ A.vertexSet := by
  rintro _ ⟨P, hP, rfl⟩
  simp only [mem_vertexSet_iff]
  use P, hP, first_mem

lemma image_last_subset (A : G.SetEnsemble) : last '' A.paths ⊆ A.vertexSet := by
  rintro _ ⟨P, hP, rfl⟩
  simp only [mem_vertexSet_iff]
  use P, hP, last_mem

@[simps]
def empty (G : Graph α β) : G.SetEnsemble where
  paths := ∅
  disjoint := by simp
  valid := by simp

@[simp]
lemma empty_between (S T : Set α) : (empty G).between S T := by
  simp [between]

@[simp]
def single (hP : G.IsPath P) : G.SetEnsemble where
  paths := {P}
  disjoint := by simp
  valid := by simp [hP]

@[simp]
lemma single_between (hP : G.IsPathFrom S T P) :
    (single hP.isPath).between S T := by
  simpa [between]

noncomputable def of_vertex (A : G.SetEnsemble) (v : α) (hv : v ∈ A.vertexSet) :
    WList α β :=
  (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.1.choose

@[simp]
lemma of_vertex_mem_setEnsemble (hv : v ∈ A.vertexSet) : A.of_vertex v hv ∈ A.paths :=
  (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.1.choose_spec.1

@[simp]
lemma mem_of_vertex (hv : v ∈ A.vertexSet) : v ∈ A.of_vertex v hv := by
  have := (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.1.choose_spec.2
  have := this ▸ (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.2
  rwa [← WList.mem_vertexSet_iff]

lemma eq_of_vertex_mem (hv : v ∈ A.vertexSet) (hP : P ∈ A.paths) (hvP : v ∈ P) :
    P = A.of_vertex v hv := by
  refine A.disjoint.eq hP (A.of_vertex_mem_setEnsemble hv) ?_
  rw [not_disjoint_iff]
  use P.first, P.first_mem
  let S := (A.vertexPartition.exists_unique_of_mem_supp hv).choose
  have : V(A.of_vertex v hv) = S :=
    (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.1.choose_spec.2
  have hS : V(P) = S := (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.2 V(P)
    (by simp [hvP, hP])
  rw [this, ← hS]
  exact P.first_mem

lemma of_vertex_injOn_first (hu : u ∈ first '' A.paths) (hv : v ∈ first '' A.paths) :
    A.of_vertex u (A.image_first_subset hu) = A.of_vertex v (image_first_subset A hv) ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨P, hP, rfl⟩ := by exact hu
  obtain ⟨Q, hQ, rfl⟩ := by exact hv
  rw [← A.eq_of_vertex_mem (A.image_first_subset hu) hP first_mem,
    ← A.eq_of_vertex_mem (image_first_subset A hv) hQ first_mem] at h
  exact h ▸ rfl

lemma of_vertex_injOn_last (hu : u ∈ last '' A.paths) (hv : v ∈ last '' A.paths) :
    A.of_vertex u (A.image_last_subset hu) = A.of_vertex v (image_last_subset A hv) ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  obtain ⟨P, hP, rfl⟩ := by exact hu
  obtain ⟨Q, hQ, rfl⟩ := by exact hv
  rw [← A.eq_of_vertex_mem (A.image_last_subset hu) hP last_mem,
    ← A.eq_of_vertex_mem (image_last_subset A hv) hQ last_mem] at h
  exact h ▸ rfl

lemma between.image_last_eq_inter (hAST : A.between S T) :
    last '' A.paths = T ∩ A.vertexSet := by
  ext x
  simp only [mem_image, mem_inter_iff, mem_vertexSet_iff]
  refine ⟨fun ⟨P, hPA, hx⟩ => ?_, fun ⟨hxT, P, hPA, hxP⟩ => by use P, hPA,
    (hAST hPA |>.eq_last_of_mem hxP hxT).symm⟩
  subst x
  use hAST hPA |>.last_mem, P, hPA, last_mem

lemma between.image_first_eq_inter (hAST : A.between S T) :
    first '' A.paths = S ∩ A.vertexSet := by
  ext x
  simp only [mem_image, mem_inter_iff, mem_vertexSet_iff]
  refine ⟨fun ⟨P, hPA, hx⟩ => ?_, fun ⟨hxS, P, hPA, hxP⟩ => by use P, hPA,
    (hAST hPA |>.eq_first_of_mem hxP hxS).symm⟩
  subst x
  use hAST hPA |>.first_mem, P, hPA, first_mem

end SetEnsemble

/-! ### k-connectivity between two sets -/

def SetConnGe (G : Graph α β) (S T : Set α) (n : ℕ) : Prop :=
  ∀ ⦃C : Set α⦄, G.IsSetCut S T C → n ≤ C.encard

@[simp]
lemma SetConnGe_zero (G : Graph α β) (S T : Set α) : G.SetConnGe S T 0 := by
  simp [SetConnGe]

lemma SetConnGe.anti_right (hle : n ≤ m) (h : G.SetConnGe S T m) :
    G.SetConnGe S T n :=
  fun _ hC ↦ le_trans (by norm_cast) (h hC)

@[simp]
lemma setConnGe_one_iff : G.SetConnGe S T 1 ↔ G.SetConnected S T := by
  refine ⟨fun h => ?_, fun h C hC => ?_⟩
  · by_contra hc
    simpa using h <| isSetCut_empty hc
  obtain ⟨s, hs, t, ht, w, hw, rfl, rfl⟩ := h
  have hwF : G.IsWalkFrom S T w := ⟨hw, hs, ht⟩
  obtain ⟨x, hxw, hxC⟩ := hwF.exists_mem_isSetCut hC
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxC

lemma SetConnGe.SetConnected (h : G.SetConnGe S T n) (hn : n ≠ 0) :
    G.SetConnected S T := by
  unfold SetConnGe at h
  contrapose! h
  use ∅, isSetCut_empty h
  change (∅ : Set α).encard < n
  rw [encard_empty]
  norm_cast
  exact pos_of_ne_zero hn

lemma SetConnGe.exists_isPathFrom (h : G.SetConnGe S T n) (hn : n ≠ 0) :
    ∃ P, G.IsPathFrom S T P := by
  classical
  obtain ⟨s, hs, t, ht, hst⟩ := h.SetConnected hn
  obtain ⟨P, hP, rfl, rfl⟩ := hst.exists_isPath
  exact ⟨P.extractPathFrom S T, hP.extractPathFrom_isPathFrom hs ht⟩

lemma SetConnGe.vertexDelete (h : G.SetConnGe S T n) (X : Set α) :
    (G - X).SetConnGe S T (n - (X ∩ V(G)).encard).toNat := by
  intro C hC
  have := by simpa using h (hC.of_vertexDelete)
  exact (ENat.coe_toNat_le_self _).trans <| tsub_le_iff_left.mpr <| this.trans <| encard_union_le ..

lemma SetConnGe.vertexDelete' (h : G.SetConnGe S T n) (X : Set α) :
    (G - X).SetConnGe (S \ X) (T \ X) (n - (X ∩ V(G)).encard).toNat := by
  intro C hC
  have := by simpa using h ((hC.of_vertexDelete').subset (by simp) (by simp))
  exact (ENat.coe_toNat_le_self _).trans <| tsub_le_iff_left.mpr <| this.trans <| encard_union_le ..

lemma SetConnGe.subset (h : G.SetConnGe S T n) (hS : S ⊆ S') (hT : T ⊆ T') :
    G.SetConnGe S' T' n :=
  fun _ hC ↦ h (hC.subset hS hT)

lemma setConnGe_inter_ncard (hFin : (V(G) ∩ S ∩ T).Finite) :
    G.SetConnGe S T (V(G) ∩ S ∩ T).ncard := by
  intro C hC
  rw [Set.ncard_def, ENat.coe_toNat (by simpa)]
  exact encard_le_encard (hC.inter_subset)

lemma SetConnGe.left_encard_le (h : G.SetConnGe S T n) : n ≤ (V(G) ∩ S).encard :=
  h (left_isSetCut G S T)

lemma SetConnGe.right_encard_le (h : G.SetConnGe S T n) : n ≤ (V(G) ∩ T).encard :=
  h (right_isSetCut G S T)

def EdgeSetConnGe (G : Graph α β) (S T : Set α) (n : ℕ) : Prop :=
  ∀ ⦃F : Set β⦄, G.IsEdgeSetCut S T F → n ≤ F.encard

@[simp]
lemma EdgeSetConnGe_zero (G : Graph α β) (S T : Set α) : G.EdgeSetConnGe S T 0 := by
  simp [EdgeSetConnGe]

lemma EdgeSetConnGe.anti_right (hle : n ≤ m) (h : G.EdgeSetConnGe S T m) :
    G.EdgeSetConnGe S T n :=
  fun _ hF ↦ le_trans (by norm_cast) (h hF)

@[simp]
lemma EdgeSetConnGe_one_iff : G.EdgeSetConnGe S T 1 ↔ G.SetConnected S T := by
  refine ⟨fun h => ?_, fun h F hF => ?_⟩
  · by_contra! hc
    simpa using h <| isEdgeSetCut_empty hc
  obtain ⟨s, hs, t, ht, w, hw, rfl, rfl⟩ := h
  have hwF : G.IsWalkFrom S T w := ⟨hw, hs, ht⟩
  obtain ⟨x, hxw, hxF⟩ := hwF.exists_mem_isEdgeSetCut hF
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxF

lemma EdgeSetConnGe.of_not_disjoint (hdj : ¬ Disjoint V(G) (S ∩ T)) :
    G.EdgeSetConnGe S T n :=
  fun _ hF ↦ (hdj hF.disjoint).elim

lemma SetConnGe.edgeSetConnGe (h : G.SetConnGe S T n) :
    G.EdgeSetConnGe S T n :=
  fun _ hF ↦ h hF.isSetCut |>.trans (encard_image_le _ _)
  |>.trans (encard_preimage_val_le_encard_right _ _)
