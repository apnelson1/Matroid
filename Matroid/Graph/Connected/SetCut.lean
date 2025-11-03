import Matroid.Graph.Connected.Defs

open Set Function Nat WList symmDiff

variable {α β ι : Type*} [CompleteLattice α] {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z s t : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β} {n m : ℕ∞}


lemma Set.diff_symmDiff_diff (A B C : Set α) : (A \ B) ∆ (A \ C) = A ∩ (B ∆ C) := by
  simp only [symmDiff_def, sup_eq_union]
  aesop

lemma Set.symmDiff_diff_distrib (A B C : Set α) : (A ∆ B) \ C = (A \ C) ∆ (B \ C) := by
  simp [symmDiff_def]
  aesop

lemma Set.disjoint_diff_iff (A B C : Set α) : Disjoint (A \ B) C ↔ A ∩ C ⊆ B := by
  rw [disjoint_iff_inter_eq_empty, diff_inter_right_comm]
  exact diff_eq_empty

namespace Graph


/-! ### ST-Connectivity -/

variable {S S' T T' : Set α}

structure SetCut (G : Graph α β) (S T : Set α) where
  carrier : Set α
  carrier_subset : carrier ⊆ V(G)
  ST_disconnects : ∀ s ∈ S, ∀ t ∈ T, ¬ (G - carrier).VertexConnected s t

instance : SetLike (G.SetCut S T) α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [SetCut.mk.injEq]

@[simp]
lemma SetCut.coe_subset (C : G.SetCut S T) : ↑C ⊆ V(G) := C.carrier_subset

@[simps]
def setCut_of_left (G : Graph α β) (S T : Set α) : G.SetCut S T where
  carrier := V(G) ∩ S
  carrier_subset := Set.inter_subset_left
  ST_disconnects s hs t ht h := by simpa [hs] using h.left_mem

@[simps]
def setCut_of_right (G : Graph α β) (S T : Set α) : G.SetCut S T where
  carrier := V(G) ∩ T
  carrier_subset := Set.inter_subset_left
  ST_disconnects s hs t ht h := by simpa [ht] using h.right_mem

@[simps]
def SetCut.vertexDelete (C : G.SetCut S T) (X : Set α) : (G - X).SetCut S T where
  carrier := C \ X
  carrier_subset := by
    rw [vertexDelete_vertexSet]
    exact diff_subset_diff_left C.coe_subset
  ST_disconnects s hs t ht h := by
    apply C.ST_disconnects s hs t ht
    simp only [vertexDelete_vertexDelete, union_diff_self] at h
    apply h.of_le
    rw [union_comm, ← vertexDelete_vertexDelete]
    exact vertexDelete_le

@[simps]
def SetCut.subset (C : G.SetCut S T) (hS : S' ⊆ S) (hT : T' ⊆ T) : G.SetCut S' T' where
  carrier := C
  carrier_subset := C.coe_subset
  ST_disconnects := fun s hs t ht h ↦ C.ST_disconnects s (hS hs) t (hT ht) h

@[simps]
def SetCut.of_vertexDelete (C : (G - X).SetCut S T) : G.SetCut S T where
  carrier := (X ∩ V(G)) ∪ C
  carrier_subset := by
    simp only [union_subset_iff, inter_subset_right, true_and]
    exact C.coe_subset.trans <| (G.vertexDelete_vertexSet X) ▸ diff_subset
  ST_disconnects s hs t ht h := by
    apply C.ST_disconnects s hs t ht
    rw [vertexDelete_vertexDelete]
    convert h using 1
    rw [← vertexDelete_vertexSet_inter, inter_comm, union_inter_distrib_right]
    congr
    exact inter_eq_left.mpr <| C.coe_subset.trans <| (G.vertexDelete_vertexSet X) ▸ diff_subset

@[simps]
def SetCut.of_vertexDelete' (C : (G - X).SetCut S T) : G.SetCut (S ∪ X) (T ∪ X) where
  carrier := (X ∩ V(G)) ∪ C
  carrier_subset := by
    simp only [union_subset_iff, inter_subset_right, true_and]
    exact C.coe_subset.trans <| (G.vertexDelete_vertexSet X) ▸ diff_subset
  ST_disconnects s hs t ht h := by
    obtain hs | hs := hs.symm
    · have := h.left_mem
      simp only [vertexDelete_vertexSet, mem_diff, mem_union, mem_inter_iff, hs, true_and,
        SetLike.mem_coe, not_or] at this
      tauto
    obtain ht | ht := ht.symm
    · have := h.right_mem
      simp only [vertexDelete_vertexSet, mem_diff, mem_union, mem_inter_iff, ht, true_and,
        SetLike.mem_coe, not_or] at this
      tauto
    exact C.of_vertexDelete.ST_disconnects s hs t ht h

def SetPreconnectivityGe (G : Graph α β) (S T : Set α) (n : ℕ∞) : Prop :=
  ∀ C : G.SetCut S T, n ≤ (↑C : Set α).encard

lemma SetPreconnectivityGe_zero (G : Graph α β) (S T : Set α) : G.SetPreconnectivityGe S T 0 := by
  simp [SetPreconnectivityGe]

lemma SetPreconnectivityGe.exists_vertexConnected (h : G.SetPreconnectivityGe S T n) (hn : n ≠ 0) :
    ∃ s ∈ S, ∃ t ∈ T, G.VertexConnected s t := by
  unfold SetPreconnectivityGe at h
  contrapose! h
  use ⟨∅, empty_subset _, by simpa⟩
  change (∅ : Set α).encard < n
  rw [encard_empty]
  exact pos_of_ne_zero hn

lemma SetPreconnectivityGe.exists_isPathFrom (h : G.SetPreconnectivityGe S T n) (hn : n ≠ 0) :
    ∃ P, G.IsPathFrom S T P := by
  classical
  obtain ⟨s, hs, t, ht, hst⟩ := h.exists_vertexConnected hn
  obtain ⟨P, hP, rfl, rfl⟩ := hst.exists_isPath
  exact ⟨P.extractPathFrom S T, hP.extractPathFrom_isPathFrom hs ht⟩

lemma SetPreconnectivityGe.vertexDelete (h : G.SetPreconnectivityGe S T n) (X : Set α) :
    (G - X).SetPreconnectivityGe S T (n - (X ∩ V(G)).encard) := by
  intro C
  have := by simpa using h C.of_vertexDelete
  have := this.trans <| encard_union_le _ _
  exact tsub_le_iff_left.mpr this

lemma SetPreconnectivityGe.vertexDelete' (h : G.SetPreconnectivityGe S T n) (X : Set α) :
    (G - X).SetPreconnectivityGe (S \ X) (T \ X) (n - (X ∩ V(G)).encard) := by
  intro C
  have := by simpa using h ((C.of_vertexDelete').subset (by simp) (by simp))
  have := this.trans <| encard_union_le _ _
  exact tsub_le_iff_left.mpr this

lemma SetPreconnectivityGe.downwards_closed (h : G.SetPreconnectivityGe S T n) (hle : m ≤ n) :
    G.SetPreconnectivityGe S T m :=
  fun C ↦ hle.trans (h C)

lemma SetPreconnectivityGe.subset (h : G.SetPreconnectivityGe S T n) (hS : S ⊆ S') (hT : T ⊆ T') :
    G.SetPreconnectivityGe S' T' n :=
  fun C ↦ h (C.subset hS hT)

structure SetEnsemble (G : Graph α β) (S T : Set α) where
  paths : Set (WList α β)
  disjoint : paths.Pairwise (Disjoint on WList.vertexSet)
  valid : ∀ ⦃P⦄, P ∈ paths → G.IsPathFrom S T P

@[simps]
def SetEnsemble.empty (G : Graph α β) (S T : Set α) : G.SetEnsemble S T where
  paths := ∅
  disjoint := by simp
  valid := by simp

@[simp]
def SetEnsemble.single (G : Graph α β) (S T : Set α) (P : WList α β) (hP : G.IsPathFrom S T P) :
    G.SetEnsemble S T where
  paths := {P}
  disjoint := by simp
  valid := by simp [hP]

lemma SetEnsemble.injOn_iff (f : WList α β → ι) :
    (∀ P Q, G.IsPathFrom S T P → G.IsPathFrom S T Q → f P = f Q → ∃ x ∈ V(P), x ∈ V(Q)) ↔
    ∀ A : G.SetEnsemble S T, A.paths.InjOn f := by
  refine ⟨fun h A P hP Q hQ hPQ => A.disjoint.eq hP hQ ?_, fun h P Q hP hQ hPQ => ?_⟩
  · rw [not_disjoint_iff]
    exact h P Q (A.valid hP) (A.valid hQ) hPQ
  rw [← not_disjoint_iff]
  rintro hdj
  suffices P = Q by
    subst P
    absurd hdj
    simp only [disjoint_self, bot_eq_empty]
    exact ne_of_mem_of_not_mem' Q.first_mem id
  refine h {paths := {P, Q}, disjoint := ?_, valid := by simp [hP, hQ]} (by simp) (by simp) hPQ
  simp [Set.pairwise_pair, onFun, disjoint_comm, hdj]

lemma SetEnsemble.injOn_of_isSublist (A : G.SetEnsemble S T) (f : WList α β → WList α β)
    (hf : ∀ w, (f w).IsSublist w) : A.paths.InjOn f :=
  (SetEnsemble.injOn_iff f).mp (fun P Q _ _ hPQ ↦
    ⟨(f P).first, (hf P).vertex_subset first_mem, (hf Q).vertex_subset (hPQ ▸ first_mem)⟩) A

lemma SetEnsemble.first_injOn (A : G.SetEnsemble S T) : A.paths.InjOn WList.first := by
  intro P hP Q hQ h
  refine not_imp_comm.mp (A.disjoint hP hQ) ?_
  rw [not_disjoint_iff]
  use P.first, P.first_mem, h ▸ Q.first_mem

lemma SetEnsemble.last_injOn (A : G.SetEnsemble S T) : A.paths.InjOn WList.last := by
  intro P hP Q hQ h
  refine not_imp_comm.mp (A.disjoint hP hQ) ?_
  rw [not_disjoint_iff]
  use P.last, P.last_mem, h ▸ Q.last_mem

def SetEnsemble.vertexPartition (A : G.SetEnsemble S T) : Partition (Set α) :=
  Partition.ofPairwiseDisjoint' (parts := WList.vertexSet '' A.paths) (by
    rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hPQ
    refine A.disjoint hP hQ (hPQ <| · ▸ rfl)) (by
    rintro _ ⟨P, hP, rfl⟩
    rw [bot_eq_empty, ← Set.nonempty_iff_ne_empty]
    exact ⟨P.first, P.first_mem⟩)

@[simp]
lemma SetEnsemble.vertexSet_mem_vertexPartition (A : G.SetEnsemble S T) (hP : P ∈ A.paths) :
    V(P) ∈ A.vertexPartition := by
  use P

def SetEnsemble.vertexSet (A : G.SetEnsemble S T) : Set α :=
  A.vertexPartition.supp

@[simp]
lemma SetEnsemble.mem_vertexSet_iff (A : G.SetEnsemble S T) :
    v ∈ A.vertexSet ↔ ∃ P ∈ A.paths, v ∈ P := by
  refine ⟨fun ⟨V, hV, hv⟩ ↦ ?_, fun ⟨P, hP, hvP⟩ ↦ ⟨V(P), (by use P), hvP⟩⟩
  obtain ⟨P, hP, rfl⟩ := by simpa [vertexPartition] using hV
  use P, hP, hv

@[simp]
lemma SetEnsemble.subset_vertexSet_of_mem (A : G.SetEnsemble S T) (hP : P ∈ A.paths) :
    V(P) ⊆ A.vertexSet :=
  fun _ hvP ↦ A.mem_vertexSet_iff.mpr ⟨P, hP, hvP⟩

lemma SetEnsemble.vertexSet_subset (A : G.SetEnsemble S T) : A.vertexSet ⊆ V(G) := by
  rintro v
  simp only [mem_vertexSet_iff, forall_exists_index, and_imp]
  exact fun _ hP hvP ↦ (A.valid hP).vertexSet_subset hvP

lemma SetEnsemble.vertexSet_eq_biUnion (A : G.SetEnsemble S T) :
    A.vertexSet = ⋃ P ∈ A.paths, V(P) := by
  ext v
  simp

lemma SetEnsemble.image_first_subset (A : G.SetEnsemble S T) : first '' A.paths ⊆ A.vertexSet := by
  rintro _ ⟨P, hP, rfl⟩
  simp only [mem_vertexSet_iff]
  use P, hP, first_mem

lemma SetEnsemble.image_last_subset (A : G.SetEnsemble S T) : last '' A.paths ⊆ A.vertexSet := by
  rintro _ ⟨P, hP, rfl⟩
  simp only [mem_vertexSet_iff]
  use P, hP, last_mem

noncomputable def SetEnsemble.of_vertex (A : G.SetEnsemble S T) (v : α) (hv : v ∈ A.vertexSet) :
    WList α β :=
  (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.1.choose

lemma SetEnsemble.of_vertex_mem_setEnsemble (A : G.SetEnsemble S T) (hv : v ∈ A.vertexSet) :
    A.of_vertex v hv ∈ A.paths :=
  (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.1.choose_spec.1

lemma SetEnsemble.of_vertex_mem (A : G.SetEnsemble S T) (hv : v ∈ A.vertexSet) :
    v ∈ A.of_vertex v hv := by
  have := (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.1.choose_spec.2
  have := this ▸ (A.vertexPartition.exists_unique_of_mem_supp hv).choose_spec.1.2
  rwa [← WList.mem_vertexSet_iff]

lemma SetEnsemble.eq_of_vertex_mem (A : G.SetEnsemble S T) (hv : v ∈ A.vertexSet)
    (hP : P ∈ A.paths) (hvP : v ∈ P) : P = A.of_vertex v hv := by
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

/-! ### Operations on SetEnsembles -/

@[simps]
def SetEnsemble.congr (A : G.SetEnsemble S T) (hG : G = H) (hS : S = S') (hT : T = T') :
    H.SetEnsemble S' T' where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := hG ▸ hS ▸ hT ▸ A.valid hP

@[simp]
lemma SetEnsemble.congr_vertexSet (A : G.SetEnsemble S T) (hG : G = H) (hS : S = S') (hT : T = T') :
    (A.congr hG hS hT).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, congr_paths, ← vertexSet_eq_biUnion]

/-- Attaches the same set of paths to a larger graph. -/
@[simps]
def SetEnsemble.of_le (A : G.SetEnsemble S T) (hle : G ≤ H) : H.SetEnsemble S T where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := (A.valid hP).of_le hle

@[simp]
lemma SetEnsemble.of_le_vertexSet (A : G.SetEnsemble S T) (hle : G ≤ H) :
    (A.of_le hle).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, of_le_paths, ← vertexSet_eq_biUnion]

@[simps]
def SetEnsemble.left_of_symmdiff_disjoint {S₀ : Set α} (A : G.SetEnsemble S T)
    (hA : Disjoint A.vertexSet (S ∆ S₀)) : G.SetEnsemble S₀ T where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := (A.valid hP).left_of_symmdiff_disjoint (hA.mono_left (A.subset_vertexSet_of_mem hP))

@[simp]
lemma SetEnsemble.left_of_symmdiff_disjoint_vertexSet {S₀ : Set α} (A : G.SetEnsemble S T)
    (hA : Disjoint A.vertexSet (S ∆ S₀)) :
    (A.left_of_symmdiff_disjoint hA).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, left_of_symmdiff_disjoint_paths, ← vertexSet_eq_biUnion]

@[simps]
def SetEnsemble.right_of_symmdiff_disjoint {T₀ : Set α} (A : G.SetEnsemble S T)
    (hA : Disjoint A.vertexSet (T ∆ T₀)) : G.SetEnsemble S T₀ where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP :=
    (A.valid hP).right_of_symmdiff_disjoint (hA.mono_left (A.subset_vertexSet_of_mem hP))

@[simp]
lemma SetEnsemble.right_of_symmdiff_disjoint_vertexSet {T₀ : Set α} (A : G.SetEnsemble S T)
    (hA : Disjoint A.vertexSet (T ∆ T₀)) :
    (A.right_of_symmdiff_disjoint hA).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, right_of_symmdiff_disjoint_paths, ← vertexSet_eq_biUnion]

/-- Takes the suitable suffixes of the paths to get a SetEnsemble for larger `S`. -/
@[simps]
def SetEnsemble.subset_left (A : G.SetEnsemble S T) (hS : S ⊆ S') [DecidablePred (· ∈ S')] :
    G.SetEnsemble S' T where
  paths := (suffixFromLast · (· ∈ S')) '' A.paths
  disjoint P hP Q hQ hPQ := by
    obtain ⟨P', hP', rfl, rfl⟩ := hP
    obtain ⟨Q', hQ', rfl, rfl⟩ := hQ
    simp only at hPQ ⊢
    apply (A.disjoint hP' hQ' ?_).mono
    · exact (P'.suffixFromLast_isSuffix (· ∈ S')).subset
    · exact (Q'.suffixFromLast_isSuffix (· ∈ S')).subset
    rintro rfl
    simp at hPQ
  valid := by
    rintro _ ⟨P', hP', rfl, rfl⟩
    simp only
    refine ⟨(A.valid hP').isPath.suffix (P'.suffixFromLast_isSuffix (· ∈ S')),
      suffixFromLast_prop_first (by use P'.first, P'.first_mem, hS (A.valid hP').first_mem),
      (P'.suffixFromLast_isSuffix (· ∈ S')).last_eq ▸ (A.valid hP').last_mem,
      fun s hs hsS' ↦ (suffixFromLast_first_eq_of_prop hs hsS').symm, fun t ht htT ↦ ?_⟩
    rw [(P'.suffixFromLast_isSuffix (· ∈ S')).last_eq]
    exact (A.valid hP').eq_last_of_mem ((P'.suffixFromLast_isSuffix (· ∈ S')).mem ht) htT

@[simp]
lemma SetEnsemble.subset_left_paths_encard [DecidablePred (· ∈ S')] (A : G.SetEnsemble S T)
    (hS : S ⊆ S') : (A.subset_left hS).paths.encard = A.paths.encard := by
  simp only [subset_left_paths]
  exact (A.injOn_of_isSublist _ (·.suffixFromLast_isSuffix (· ∈ S') |>.isSublist)).encard_image

/-- Takes the suitable prefixes of the paths to get a SetEnsemble for larger `T`. -/
@[simps]
def SetEnsemble.subset_right (A : G.SetEnsemble S T) (hT : T ⊆ T') [DecidablePred (· ∈ T')] :
    G.SetEnsemble S T' where
  paths := (prefixUntil · (· ∈ T')) '' A.paths
  disjoint P hP Q hQ hPQ := by
    obtain ⟨P', hP', rfl, rfl⟩ := hP
    obtain ⟨Q', hQ', rfl, rfl⟩ := hQ
    simp only at hPQ
    apply (A.disjoint hP' hQ' ?_).mono
    · exact (P'.prefixUntil_isPrefix (· ∈ T')).subset
    · exact (Q'.prefixUntil_isPrefix (· ∈ T')).subset
    rintro rfl
    simp at hPQ
  valid := by
    rintro _ ⟨P', hP', rfl, rfl⟩
    simp only
    refine ⟨(A.valid hP').isPath.prefix (P'.prefixUntil_isPrefix (· ∈ T')),
      (P'.prefixUntil_first (· ∈ T')) ▸ (A.valid hP').first_mem,
      prefixUntil_prop_last (by use P'.last, P'.last_mem, hT (A.valid hP').last_mem), ?_,
      fun t ht htT' ↦ (prefixUntil_last_eq_of_prop ht htT').symm⟩
    simp only [prefixUntil_first]
    rintro s hs hsS'
    exact (A.valid hP').eq_first_of_mem ((P'.prefixUntil_isPrefix (· ∈ T')).mem hs) hsS'

@[simp]
lemma SetEnsemble.subset_right_paths_encard [DecidablePred (· ∈ T')] (A : G.SetEnsemble S T)
    (hT : T ⊆ T') : (A.subset_right hT).paths.encard = A.paths.encard := by
  simp only [subset_right_paths]
  exact InjOn.encard_image <| A.injOn_of_isSublist _ (·.prefixUntil_isPrefix (· ∈ T') |>.isSublist)

/-- Takes the suitable infixes of the paths to get a SetEnsemble for larger `S` and `T`. -/
@[simps!]
def SetEnsemble.subset (A : G.SetEnsemble S T) (hS : S ⊆ S') (hT : T ⊆ T') [DecidablePred (· ∈ S')]
    [DecidablePred (· ∈ T')] : G.SetEnsemble S' T' :=
  A.subset_left hS |>.subset_right hT

/-- Given a vertex set disjoint from a SetEnsemble, the same set of paths form a valid SetEnsmeble
  for `G - X`. -/
@[simps!]
def SetEnsemble.vertexDelete_of_disjoint (A : G.SetEnsemble S T) (hA : Disjoint A.vertexSet X) :
    (G - X).SetEnsemble S T where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := (A.valid hP).vertexDelete_of_disjoint (hA.mono_left (A.subset_vertexSet_of_mem hP))

@[simp]
lemma SetEnsemble.vertexDelete_of_disjoint_vertexSet (A : G.SetEnsemble S T)
    (hA : Disjoint A.vertexSet X) : (A.vertexDelete_of_disjoint hA).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, vertexDelete_of_disjoint_paths, ← vertexSet_eq_biUnion]

/-- Given a vertex set disjoint from a SetEnsemble, the same set of paths form a valid SetEnsmeble
  for `S \ X`. -/
@[simps!]
def SetEnsemble.diff_left_of_disjoint (A : G.SetEnsemble S T) (hA : Disjoint A.vertexSet X) :
    G.SetEnsemble (S \ X) T where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := (A.valid hP).subset_left diff_subset <| ⟨(A.valid hP).first_mem,
    ((hA.mono_left (A.subset_vertexSet_of_mem hP))).notMem_of_mem_left first_mem⟩

@[simp]
lemma SetEnsemble.diff_left_of_disjoint_vertexSet (A : G.SetEnsemble S T)
    (hA : Disjoint A.vertexSet X) : (A.diff_left_of_disjoint hA).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, diff_left_of_disjoint_paths, ← vertexSet_eq_biUnion]

/-- Given a vertex set disjoint from a SetEnsemble, the same set of paths form a valid SetEnsmeble
  for `T \ X`. -/
@[simps!]
def SetEnsemble.diff_right_of_disjoint (A : G.SetEnsemble S T) (hA : Disjoint A.vertexSet X) :
    G.SetEnsemble S (T \ X) where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := (A.valid hP).subset_right diff_subset <| ⟨(A.valid hP).last_mem,
    ((hA.mono_left (A.subset_vertexSet_of_mem hP))).notMem_of_mem_left last_mem⟩

@[simp]
lemma SetEnsemble.diff_right_of_disjoint_vertexSet (A : G.SetEnsemble S T)
    (hA : Disjoint A.vertexSet X) : (A.diff_right_of_disjoint hA).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, diff_right_of_disjoint_paths, ← vertexSet_eq_biUnion]

/-- Inserts a new disjoint path into a SetEnsemble. -/
@[simps]
def SetEnsemble.insert_path (A : G.SetEnsemble S T) (P : WList α β) (hP : G.IsPathFrom S T P)
    (hdj : Disjoint V(P) A.vertexSet) : G.SetEnsemble S T where
  paths := insert P A.paths
  disjoint := by
    refine A.disjoint.insert fun Q hQ hne ↦ ?_
    simp only [onFun, disjoint_comm, and_self]
    exact hdj.mono_right (A.subset_vertexSet_of_mem hQ)
  valid := by
    rintro Q (rfl | hQ)
    · exact hP
    exact A.valid hQ

@[simp]
lemma SetEnsemble.insert_path_paths_encard (A : G.SetEnsemble S T) (hP : G.IsPathFrom S T P)
    (hdj : Disjoint V(P) A.vertexSet) :
    (A.insert_path P hP hdj).paths.encard = A.paths.encard + 1 := by
  rw [insert_path_paths, Set.encard_insert_of_notMem ?_]
  contrapose! hdj
  rw [not_disjoint_iff]
  exact ⟨P.last, P.last_mem, A.mem_vertexSet_iff.mpr ⟨P, hdj, P.last_mem⟩⟩

/-- Takes a subset of the paths of a SetEnsemble. -/
@[simps]
def SetEnsemble.path_subset (A : G.SetEnsemble S T) (P : Set (WList α β)) (hP : P ⊆ A.paths) :
    G.SetEnsemble S T where
  paths := P
  disjoint := A.disjoint.mono hP
  valid _ hQ := A.valid (hP hQ)

/-! ### Extending a SetEnsemble by a path in `T` -/

/-- `pathr` refers to the path `P` in `T`. -/
lemma SetEnsemble.pathr_first_mem (A : G.SetEnsemble S T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) : P.first ∈ A.vertexSet :=
  singleton_subset_iff.mp <| hPfirst ▸ inter_subset_left

lemma SetEnsemble.pathr_first_eq_of_vertex_last (A : G.SetEnsemble S T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hPT : V(P) ⊆ T) :
    (A.of_vertex P.first <| A.pathr_first_mem hPfirst).last = P.first :=
  let hfirst := A.pathr_first_mem hPfirst
  A.valid (A.of_vertex_mem_setEnsemble <| A.pathr_first_mem hPfirst)
  |>.eq_last_of_mem (A.of_vertex_mem hfirst) (hPT P.first_mem) |>.symm

lemma SetEnsemble.disjoint_pathr_of_ne_of_vertex (A : G.SetEnsemble S T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hPT : V(P) ⊆ T) (hQ : Q ∈ A.paths)
    (hQne : Q ≠ A.of_vertex P.first (A.pathr_first_mem hPfirst)) : Disjoint V(P) V(Q) := by
  contrapose! hQne
  apply A.disjoint.eq hQ (A.of_vertex_mem_setEnsemble (A.pathr_first_mem hPfirst))
  rw [not_disjoint_iff] at hQne ⊢
  use P.first, ?_, A.of_vertex_mem (A.pathr_first_mem hPfirst)
  obtain ⟨v, hvP, hvQ⟩ := hQne
  obtain rfl := A.valid hQ |>.eq_last_of_mem hvQ (hPT hvP)
  convert hvQ using 1
  rw [eq_comm, ← mem_singleton_iff, ← hPfirst, mem_inter_iff, A.mem_vertexSet_iff]
  use ⟨Q, hQ, last_mem⟩, hvP

@[simps]
def SetEnsemble.extend_right (A : G.SetEnsemble S T) (P : WList α β) (hP : V(P) ⊆ T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hPP : G.IsPath P) :
    G.SetEnsemble (S \ (V(P) \ {P.first})) (T \ (V(P) \ {P.last})) where
  paths :=
    let Q := A.of_vertex P.first (singleton_subset_iff.mp <| hPfirst ▸ inter_subset_left)
    insert (Q ++ P) (A.paths \ {Q})
  disjoint := by
    refine (A.disjoint.mono diff_subset).insert fun Q hQ hne ↦ ?_
    simp only [onFun, A.pathr_first_eq_of_vertex_last hPfirst hP, append_vertexSet_of_eq,
      disjoint_comm, disjoint_union_right, and_self]
    exact ⟨(A.disjoint hQ.1 (A.of_vertex_mem_setEnsemble <| A.pathr_first_mem hPfirst) hQ.2),
      A.disjoint_pathr_of_ne_of_vertex hPfirst hP hQ.1 hQ.2⟩
  valid := by
    have hfirst : P.first ∈ A.vertexSet := singleton_subset_iff.mp <| hPfirst ▸ inter_subset_left
    rintro Q (rfl | hQ)
    · exact (A.valid <| A.of_vertex_mem_setEnsemble <| A.pathr_first_mem hPfirst).append_right hPP
        hP <| A.pathr_first_eq_of_vertex_last hPfirst hP
    have hdj := A.disjoint_pathr_of_ne_of_vertex hPfirst hP hQ.1 hQ.2 |>.symm
    exact (A.valid hQ.1).diff_left_of_disjoint (hdj.mono_right diff_subset)
    |>.diff_right_of_disjoint <| hdj.mono_right diff_subset

@[simp]
lemma SetEnsemble.extend_right_paths_encard (A : G.SetEnsemble S T) (hAFin : A.paths.Finite)
    (hP : V(P) ⊆ T) (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hPP : G.IsPath P) :
    (A.extend_right P hP hPfirst hPP).paths.encard = A.paths.encard := by
  have hf := singleton_subset_iff.mp <| hPfirst ▸ inter_subset_left
  have : Finite ↑A.paths := hAFin
  have : Finite ↑(A.paths \ {A.of_vertex P.first hf}) :=
    Finite.Set.finite_diff A.paths {A.of_vertex P.first hf}
  have hAcard : 0 < A.paths.encard := by
    obtain ⟨Q, hQ, -⟩ := by simpa using hf
    exact Nonempty.encard_pos ⟨Q, hQ⟩
  have hPfirstQ : A.of_vertex P.first hf ++ P ∉ A.paths \ {A.of_vertex P.first hf} := by
    simp only [mem_diff, mem_singleton_iff, not_and, not_not]
    rintro haA
    apply A.disjoint.eq haA (A.of_vertex_mem_setEnsemble (A.pathr_first_mem hPfirst)) ?_
    rw [not_disjoint_iff]
    exact ⟨(A.of_vertex P.first hf).first, by simp [A.pathr_first_eq_of_vertex_last hPfirst hP],
      first_mem⟩
  rw [extend_right_paths, encard_insert_of_notMem hPfirstQ, encard_diff_singleton_of_mem
  <| A.of_vertex_mem_setEnsemble (A.pathr_first_mem hPfirst)]
  refine tsub_add_cancel_of_le ?_
  exact Order.one_le_iff_pos.mpr hAcard

@[simp]
lemma SetEnsemble.extend_right_vertexSet (A : G.SetEnsemble S T) (hP : V(P) ⊆ T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hPP : G.IsPath P) :
    (A.extend_right P hP hPfirst hPP).vertexSet = A.vertexSet ∪ V(P) := by
  simp_rw [Set.ext_iff, mem_vertexSet_iff, extend_right_paths, mem_insert_iff, mem_diff,
    mem_singleton_iff, exists_eq_or_imp, mem_union, mem_append_iff_of_eq
    (A.pathr_first_eq_of_vertex_last hPfirst hP), or_comm, or_assoc]
  apply fun v ↦ or_congr_right ?_
  by_cases hv : v ∈ A.of_vertex P.first (A.pathr_first_mem hPfirst)
  · simp only [hv, ne_eq, true_or, mem_vertexSet_iff, true_iff]
    use A.of_vertex P.first (A.pathr_first_mem hPfirst),
      (A.of_vertex_mem_setEnsemble (A.pathr_first_mem hPfirst)), hv
  simp only [hv, ne_eq, false_or, mem_vertexSet_iff]
  apply exists_congr fun Q ↦ and_congr_left fun hvQ ↦ ?_
  simp only [and_iff_left_iff_imp]
  exact fun _ heq ↦ hv <| heq ▸ hvQ

/-- Extends a SetEnsemble by a path in `P` when exactly two paths end somewhere in `P`.
  Send help. -/
@[simps!]
def SetEnsemble.extend_right_two (A : G.SetEnsemble S T) (P : WList α β) (hPT : V(P) ⊆ T)
    [DecidablePred (· ∈ A.vertexSet)] (htwo : P.vertex.countP (· ∈ A.vertexSet) = 2)
    (hPP : G.IsPath P) :
    G.SetEnsemble (S \ (V(P) \ A.vertexSet)) (T \ (V(P) \ {P.first, P.last})) := by
  have hPslen : (P.breakAt (· ∈ A.vertexSet)).length = 3 := by rw [breakAt_length, htwo]
  let P₀ := P.prefixUntil (· ∈ A.vertexSet)
  let P₂ := P.suffixFromLast (· ∈ A.vertexSet)
  have hP : (P.breakAt fun x ↦ x ∈ A.vertexSet) = [P₀, (P.breakAt (· ∈ A.vertexSet))[1], P₂] := by
    obtain ⟨P₀', P₁', P₂', hP'⟩ := List.length_eq_three.mp hPslen
    obtain rfl : P₀ = P₀' := by simp [P₀, ← P.breakAt_head (· ∈ A.vertexSet), hP']
    obtain rfl : P₂ = P₂' := by simp [P₂, ← P.breakAt_getLast (· ∈ A.vertexSet), hP']
    simp [hP']
  have hap : P = P₀ ++ (P.breakAt (· ∈ A.vertexSet))[1] ++ P₂ :=
    hP ▸ P.breakAt_foldl_append_cancel (· ∈ A.vertexSet) (x := P.first) |>.symm
  have hdj : Disjoint V(P₀) V(P₂) := by
    obtain ⟨hP₀leq, hP₂feq⟩ := by
      have := hP ▸ P.breakAt_isChain_eq (· ∈ A.vertexSet)
      simpa using this
    exact (hap ▸ hPP).disjoint_of_append_append hP₀leq
    <| P.nonempty_of_mem_breakAt_dropLast_tail (· ∈ A.vertexSet) <| by (conv_lhs => rw [hP]); simp
  have hPf : P₀.first = P.first := P.prefixUntil_first _
  have hPl : P₂.last = P.last := P.suffixFromLast_last _
  have hex : ∃ u ∈ P, u ∈ A.vertexSet := by
    obtain ⟨u, hup, huA⟩ := (P.vertex.countP_pos_iff (p := (· ∈ A.vertexSet))).mp (by omega)
    exact ⟨u, hup, by simpa using huA⟩
  have hP₀f : V(P₀) \ {P₀.first} = V(P₀) \ {P.first, P.last} := by
    rw [← hPf, ← hPl, pair_comm, diff_insert_of_notMem]
    exact hdj.notMem_of_mem_right last_mem
  have hP₀l : V(P₀) \ {P₀.last} = V(P₀) \ A.vertexSet := by
    rw [diff_eq_diff_iff_inter_eq_inter, P.prefixUntil_inter_eq_last A.vertexSet hex, inter_eq_left]
    simp
  have hP₂f : V(P₂) \ {P₂.first} = V(P₂) \ A.vertexSet := by
    rw [diff_eq_diff_iff_inter_eq_inter, P.suffixFromLast_inter_eq_first A.vertexSet hex,
      inter_eq_left]
    simp
  have hP₂l : V(P₂) \ {P₂.last} = V(P₂) \ {P.first, P.last} := by
    rw [← hPf, ← hPl, diff_insert_of_notMem]
    exact hdj.notMem_of_mem_left first_mem
  have h : V(P) ∩ A.vertexSet ⊆ V(P₀) ∪ V(P₂) := by
    rintro x ⟨hxP, hxA⟩
    rw [WList.mem_vertexSet_iff] at hxP
    have : x ∈ List.map (fun x ↦ x.first) (P.breakAt fun x ↦ x ∈ A.vertexSet).tail :=
      P.breakAt_tail_map_first_eq_vertex_filter (· ∈ A.vertexSet) ▸
      List.mem_filter.mpr (by simp [hxP, hxA] : x ∈ P.vertex ∧ _)
    obtain rfl | rfl := by
      obtain ⟨hP₀leq, hP₂feq⟩ := by
        have := hP ▸ P.breakAt_isChain_eq (· ∈ A.vertexSet)
        simpa using this
      rw [hP] at this
      simpa [← hP₀leq] using this
    · exact mem_union_left _ last_mem
    exact mem_union_right _ first_mem

  refine A.extend_right P₀.reverse (P₀.reverse_vertexSet ▸ (P.prefixUntil_isPrefix _).subset.trans
    hPT) ?_ (hPP.reverse.suffix (P.prefixUntil_isPrefix _).reverse_isSuffix_reverse)
    |>.extend_right P₂ ?_ ?_ (hPP.suffix <| P.suffixFromLast_isSuffix _)
    |>.left_of_symmdiff_disjoint ?_ |>.right_of_symmdiff_disjoint ?_
  · simp only [reverse_vertexSet, reverse_first]
    exact P.prefixUntil_inter_eq_last A.vertexSet hex
  · simp only [reverse_vertexSet, reverse_last]
    rw [subset_diff]
    use (P.suffixFromLast_isSuffix _).subset.trans hPT, hdj.symm.mono_right diff_subset
  · simp only [extend_right_vertexSet, reverse_vertexSet, union_inter_distrib_right]
    rw [disjoint_iff_inter_eq_empty.mp hdj, union_empty]
    exact P.suffixFromLast_inter_eq_first A.vertexSet hex
  · conv in (_ ∆ _) =>
      rw [diff_diff, Set.diff_symmDiff_diff, reverse_vertexSet, reverse_first, hP₀l, hP₂f,
        ← union_diff_distrib, ← symmDiff_diff_distrib, symmDiff_of_le
        (by simp; exact ⟨(P.prefixUntil_isPrefix _).subset, (P.suffixFromLast_isSuffix _).subset⟩),
        ← diff_diff]
    simp only [extend_right_vertexSet, reverse_vertexSet, disjoint_union_left, and_assoc]
    exact ⟨(disjoint_sdiff_right).mono_right inter_subset_right,
      disjoint_sdiff_right.mono_right <| (inter_subset_right.trans diff_subset).trans diff_subset,
      disjoint_sdiff_right.mono_right <| inter_subset_right.trans diff_subset⟩
  conv in (_ ∆ _) =>
    rw [diff_diff, Set.diff_symmDiff_diff, reverse_vertexSet, reverse_last, hP₀f, hP₂l,
      ← union_diff_distrib, ← symmDiff_diff_distrib, symmDiff_of_le
      (by simp; exact ⟨(P.prefixUntil_isPrefix _).subset, (P.suffixFromLast_isSuffix _).subset⟩),
      inter_eq_right.mpr ((diff_subset.trans diff_subset).trans hPT), ← diff_diff]
  refine Disjoint.mono_right diff_subset ?_
  simp only [left_of_symmdiff_disjoint_vertexSet, extend_right_vertexSet, reverse_vertexSet,
    disjoint_union_left, and_assoc]
  refine ⟨?_, disjoint_sdiff_right.mono_right diff_subset, disjoint_sdiff_right⟩
  rwa [diff_diff, disjoint_comm, disjoint_diff_iff]

@[simp]
lemma SetEnsemble.extend_right_two_vertexSet (A : G.SetEnsemble S T) (P : WList α β)
    (hPT : V(P) ⊆ T) [DecidablePred (· ∈ A.vertexSet)]
    (htwo : P.vertex.countP (· ∈ A.vertexSet) = 2) (hPP : G.IsPath P) :
    (A.extend_right_two P hPT htwo hPP).vertexSet =
    A.vertexSet ∪ V(P.prefixUntil (· ∈ A.vertexSet)) ∪ V(P.suffixFromLast (· ∈ A.vertexSet)) := by
  simp [extend_right_two, extend_right_vertexSet]
