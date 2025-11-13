import Matroid.Graph.Connected.Vertex.Defs

open Set Function Nat WList

variable {α β ι : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {C U V S S' T T' X Y : Set α} {F F' R R': Set β} {W P Q : WList α β}

namespace Graph

/-! ### Connectivity between two sets -/

def SetConnected (G : Graph α β) (S T : Set α) : Prop :=
  ∃ s ∈ S, ∃ t ∈ T, G.ConnectedBetween s t

lemma SetConnected.of_le (h : G.SetConnected S T) (hle : G ≤ H) : H.SetConnected S T := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hs, t, ht, hst.of_le hle⟩

lemma SetConnected.subset_left (h : G.SetConnected S T) (hS : S ⊆ S') : G.SetConnected S' T := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hS hs, t, ht, hst.of_le (by simp)⟩

lemma SetConnected.subset_right (h : G.SetConnected S T) (hT : T ⊆ T') : G.SetConnected S T' := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hs, t, hT ht, hst.of_le (by simp)⟩

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

lemma ConnectedBetween.neighbor_setConnected (h : G.ConnectedBetween s t) (hne : s ≠ t)
    (hadj : ¬ G.Adj s t) : (G - {s, t}).SetConnected (N(G, s)) (N(G, t)) := by
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
    exact h.ST_disconnects <| hH.of_le (vertexDelete_mono_left hle)

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

end SetEnsemble

/-! ### k-connectivity between two sets -/

def SetConnectivityGe (G : Graph α β) (S T : Set α) (n : ℕ) : Prop :=
  ∀ ⦃C : Set α⦄, G.IsSetCut S T C → n ≤ C.encard

@[simp]
lemma SetConnectivityGe_zero (G : Graph α β) (S T : Set α) : G.SetConnectivityGe S T 0 := by
  simp [SetConnectivityGe]

lemma SetConnectivityGe.anti_right (hle : n ≤ m) (h : G.SetConnectivityGe S T m) :
    G.SetConnectivityGe S T n :=
  fun _ hC ↦ le_trans (by norm_cast) (h hC)

@[simp]
lemma setConnectivityGe_one_iff : G.SetConnectivityGe S T 1 ↔ G.SetConnected S T := by
  refine ⟨fun h => ?_, fun h C hC => ?_⟩
  · by_contra hc
    simpa using h <| isSetCut_empty hc
  obtain ⟨s, hs, t, ht, w, hw, rfl, rfl⟩ := h
  have hwF : G.IsWalkFrom S T w := ⟨hw, hs, ht⟩
  obtain ⟨x, hxw, hxC⟩ := hwF.exists_mem_isSetCut hC
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxC

lemma SetConnectivityGe.SetConnected (h : G.SetConnectivityGe S T n) (hn : n ≠ 0) :
    G.SetConnected S T := by
  unfold SetConnectivityGe at h
  contrapose! h
  use ∅, isSetCut_empty h
  change (∅ : Set α).encard < n
  rw [encard_empty]
  norm_cast
  exact pos_of_ne_zero hn

lemma SetConnectivityGe.exists_isPathFrom (h : G.SetConnectivityGe S T n) (hn : n ≠ 0) :
    ∃ P, G.IsPathFrom S T P := by
  classical
  obtain ⟨s, hs, t, ht, hst⟩ := h.SetConnected hn
  obtain ⟨P, hP, rfl, rfl⟩ := hst.exists_isPath
  exact ⟨P.extractPathFrom S T, hP.extractPathFrom_isPathFrom hs ht⟩

lemma SetConnectivityGe.vertexDelete (h : G.SetConnectivityGe S T n) (X : Set α) :
    (G - X).SetConnectivityGe S T (n - (X ∩ V(G)).encard).toNat := by
  intro C hC
  have := by simpa using h (hC.of_vertexDelete)
  exact (ENat.coe_toNat_le_self _).trans <| tsub_le_iff_left.mpr <| this.trans <| encard_union_le ..

lemma SetConnectivityGe.vertexDelete' (h : G.SetConnectivityGe S T n) (X : Set α) :
    (G - X).SetConnectivityGe (S \ X) (T \ X) (n - (X ∩ V(G)).encard).toNat := by
  intro C hC
  have := by simpa using h ((hC.of_vertexDelete').subset (by simp) (by simp))
  exact (ENat.coe_toNat_le_self _).trans <| tsub_le_iff_left.mpr <| this.trans <| encard_union_le ..

lemma SetConnectivityGe.subset (h : G.SetConnectivityGe S T n) (hS : S ⊆ S') (hT : T ⊆ T') :
    G.SetConnectivityGe S' T' n :=
  fun _ hC ↦ h (hC.subset hS hT)

lemma setConnectivityGe_inter_ncard (hFin : (V(G) ∩ S ∩ T).Finite) :
    G.SetConnectivityGe S T (V(G) ∩ S ∩ T).ncard := by
  intro C hC
  rw [Set.ncard_def, ENat.coe_toNat (by simpa)]
  exact encard_le_encard (hC.inter_subset)

def EdgeSetConnectivityGe (G : Graph α β) (S T : Set α) (n : ℕ) : Prop :=
  ∀ ⦃C : Set β⦄, G.IsEdgeSetCut S T C → n ≤ C.encard

@[simp]
lemma EdgeSetConnectivityGe_zero (G : Graph α β) (S T : Set α) : G.EdgeSetConnectivityGe S T 0 := by
  simp [EdgeSetConnectivityGe]

lemma EdgeSetConnectivityGe.anti_right (hle : n ≤ m) (h : G.EdgeSetConnectivityGe S T m) :
    G.EdgeSetConnectivityGe S T n :=
  fun _ hC ↦ le_trans (by norm_cast) (h hC)

@[simp]
lemma EdgeSetConnectivityGe_one_iff : G.EdgeSetConnectivityGe S T 1 ↔ G.SetConnected S T := by
  refine ⟨fun h => ?_, fun h C hC => ?_⟩
  · by_contra! hc
    simpa using h <| isEdgeSetCut_empty hc
  obtain ⟨s, hs, t, ht, w, hw, rfl, rfl⟩ := h
  have hwF : G.IsWalkFrom S T w := ⟨hw, hs, ht⟩
  obtain ⟨x, hxw, hxC⟩ := hwF.exists_mem_isEdgeSetCut hC
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxC
