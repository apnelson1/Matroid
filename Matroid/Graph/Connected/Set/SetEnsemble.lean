import Matroid.Graph.Connected.Set.Defs


open Set Function Nat WList symmDiff

variable {α β ι : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z s t : α}
  {e e' f g : β} {U V S T X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β} {n m : ℕ∞}

namespace Graph


/-! ### ST-Connectivity -/

namespace SetEnsemble
variable {A : G.SetEnsemble}

lemma injOn_iff (f : WList α β → ι) :
    (∀ P Q, G.IsPath P → G.IsPath Q → f P = f Q → ∃ x ∈ V(P), x ∈ V(Q)) ↔
    ∀ A : G.SetEnsemble, A.paths.InjOn f := by
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

lemma injOn_of_isSublist (A : G.SetEnsemble) {f : WList α β → WList α β}
    (hf : ∀ w, (f w).IsSublist w) : A.paths.InjOn f :=
  (injOn_iff f).mp (fun P Q _ _ hPQ ↦
    ⟨(f P).first, (hf P).subset first_mem, (hf Q).subset (hPQ ▸ first_mem)⟩) A

lemma first_injOn (A : G.SetEnsemble) : A.paths.InjOn WList.first := by
  intro P hP Q hQ h
  refine not_imp_comm.mp (A.disjoint hP hQ) ?_
  rw [not_disjoint_iff]
  use P.first, P.first_mem, h ▸ Q.first_mem

lemma last_injOn (A : G.SetEnsemble) : A.paths.InjOn WList.last := by
  intro P hP Q hQ h
  refine not_imp_comm.mp (A.disjoint hP hQ) ?_
  rw [not_disjoint_iff]
  use P.last, P.last_mem, h ▸ Q.last_mem

/-! ### Operations on SetEnsembles -/

@[simps (attr := grind =)]
def congr (A : G.SetEnsemble) (hG : G = H) : H.SetEnsemble where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := hG ▸ A.valid hP

@[simp]
lemma congr_vertexSet (A : G.SetEnsemble) (hG : G = H) :
    (A.congr hG).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, congr_paths, ← vertexSet_eq_biUnion]

/-- Attaches the same set of paths to a larger graph. -/
@[simps (attr := grind =)]
def of_le (A : G.SetEnsemble) (hle : G ≤ H) : H.SetEnsemble where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := (A.valid hP).of_le hle

@[simp]
lemma of_le_vertexSet (A : G.SetEnsemble) (hle : G ≤ H) :
    (A.of_le hle).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, of_le_paths, ← vertexSet_eq_biUnion]

@[simp]
lemma between.left {S₀ : Set α} (hAST : A.between S T)
    (hA : Disjoint A.vertexSet (S ∆ S₀)) : A.between S₀ T :=
  fun _ hP ↦ (hAST hP).left_of_symmdiff_disjoint (hA.mono_left (A.subset_vertexSet_of_mem hP))

@[simp]
lemma between.right {T₀ : Set α} (hAST : A.between S T)
    (hA : Disjoint A.vertexSet (T ∆ T₀)) : A.between S T₀ :=
  fun _ hP ↦ (hAST hP).right_of_symmdiff_disjoint (hA.mono_left (A.subset_vertexSet_of_mem hP))

lemma between_vertexSet_inter_left_iff : A.between (V(G) ∩ S) T ↔ A.between S T :=
  ⟨fun h _ hC => isPathFrom_vertexSet_inter_left_iff.mp <| h hC,
    fun h _ hC => isPathFrom_vertexSet_inter_left_iff.mpr <| h hC⟩

lemma between_vertexSet_inter_right_iff : A.between S (V(G) ∩ T) ↔ A.between S T :=
  ⟨fun h _ hC => isPathFrom_vertexSet_inter_right_iff.mp <| h hC,
    fun h _ hC => isPathFrom_vertexSet_inter_right_iff.mpr <| h hC⟩

/-- Given a vertex set disjoint from a SetEnsemble, the same set of paths form a valid SetEnsmeble
  for `G - X`. -/
@[simps (attr := grind =)]
def vertexDelete (A : G.SetEnsemble) (hA : Disjoint A.vertexSet X) : (G - X).SetEnsemble where
  paths := A.paths
  disjoint := A.disjoint
  valid _ hP := by
    rw [isPath_vertexDelete_iff]
    use A.valid hP, hA.mono_left (A.subset_vertexSet_of_mem hP)

@[simp]
lemma vertexDelete_vertexSet (A : G.SetEnsemble)
    (hA : Disjoint A.vertexSet X) : (A.vertexDelete hA).vertexSet = A.vertexSet := by
  rw [vertexSet_eq_biUnion, vertexDelete_paths, ← vertexSet_eq_biUnion]

lemma of_vertexDelete (A : (G - X).SetEnsemble) : Disjoint A.vertexSet X := by
  have := by simpa [subset_diff] using A.vertexSet_subset
  exact this.2

/-- Given a vertex set disjoint from a SetEnsemble, the same set of paths form a valid SetEnsmeble
  for `S \ X`. -/
@[simp]
def between.diff_left (hAST : A.between S T) (hA : Disjoint A.vertexSet X) :
    A.between (S \ X) T := fun _ hP ↦ (hAST hP).subset_left diff_subset <| ⟨(hAST hP).first_mem,
    ((hA.mono_left (A.subset_vertexSet_of_mem hP))).notMem_of_mem_left first_mem⟩

/-- Given a vertex set disjoint from a SetEnsemble, the same set of paths form a valid SetEnsmeble
  for `T \ X`. -/
@[simp]
def between.diff_right (hAST : A.between S T) (hA : Disjoint A.vertexSet X):
    A.between S (T \ X) := fun _ hP ↦ (hAST hP).subset_right diff_subset <| ⟨(hAST hP).last_mem,
    ((hA.mono_left (A.subset_vertexSet_of_mem hP))).notMem_of_mem_left last_mem⟩

/-- Inserts a new disjoint path into a  -/
@[simps (attr := grind =)]
def path_insert (A : G.SetEnsemble) (P : WList α β) (hP : G.IsPath P)
    (hdj : Disjoint A.vertexSet V(P)) : G.SetEnsemble where
  paths := insert P A.paths
  disjoint := by
    refine A.disjoint.insert fun Q hQ hne ↦ ?_
    simp only [onFun, disjoint_comm, and_self]
    exact hdj.symm.mono_right (A.subset_vertexSet_of_mem hQ)
  valid := by
    rintro Q (rfl | hQ)
    · exact hP
    exact A.valid hQ

@[simp]
lemma path_insert_paths_encard (hP : G.IsPath P) (hdj : Disjoint A.vertexSet V(P)) :
    (A.path_insert P hP hdj).paths.encard = A.paths.encard + 1 := by
  rw [path_insert_paths, Set.encard_insert_of_notMem ?_]
  contrapose! hdj
  rw [disjoint_comm, not_disjoint_iff]
  exact ⟨P.last, P.last_mem, A.mem_vertexSet_iff.mpr ⟨P, hdj, P.last_mem⟩⟩

lemma between.path_insert (hAST : A.between S T) (hP : G.IsPathFrom S T P)
    (hdj : Disjoint A.vertexSet V(P)) : (A.path_insert P hP.isPath hdj).between S T := by
  rintro Q hQ
  obtain rfl | hQ := (by simpa using hQ)
  · exact hP
  exact hAST hQ |>.left_of_symmdiff_disjoint <| by simp

@[simps (attr := grind =)]
def path_remove (A : G.SetEnsemble) (P : WList α β) : G.SetEnsemble where
  paths := A.paths \ {P}
  disjoint := A.disjoint.mono diff_subset
  valid _ hQ := A.valid (by simp_all)

@[simp]
lemma path_remove_vertexSet_disjoint (hP : P ∈ A.paths) :
    Disjoint (A.path_remove P).vertexSet V(P) := by
  simp only [vertexSet_eq_biUnion, disjoint_iUnion_left, path_remove_paths, mem_diff,
    mem_singleton_iff, and_imp]
  simp_rw [eq_comm, disjoint_comm]
  exact A.disjoint hP

@[simp]
lemma path_remove_vertexSet (hP : P ∈ A.paths) :
    (A.path_remove P).vertexSet = A.vertexSet \ V(P) := by
  rw [vertexSet_eq_biUnion, path_remove_paths, vertexSet_eq_biUnion]
  conv_rhs => rw [← insert_eq_of_mem hP , ← insert_diff_singleton, biUnion_insert,
    union_diff_cancel_left (by
    rw [subset_empty_iff, ← disjoint_iff_inter_eq_empty, ← path_remove_paths, ←vertexSet_eq_biUnion]
    exact (A.path_remove_vertexSet_disjoint hP).symm)]

@[simp]
lemma path_remove_last (hP : P ∈ A.paths) :
    last '' (A.path_remove P).paths = (last '' A.paths) \ {P.last} := by
  rw [path_remove_paths, A.last_injOn.image_diff, inter_eq_right.mpr (by simpa), image_singleton]

lemma between.path_remove (hAST : A.between S T) (P) : (A.path_remove P).between S T :=
  fun _ hQ ↦ hAST hQ.1

@[simps! (attr := grind =)]
def shorten (A : G.SetEnsemble) (P : WList α β) (hQ : Q.IsSublist P) (hP : P ∈ A.paths) :
    G.SetEnsemble :=
  A.path_remove P |>.path_insert Q (A.valid hP |>.sublist hQ)
  <| (path_remove_vertexSet_disjoint hP).mono_right hQ.subset

lemma shorten_last (hQ : Q.IsSublist P) (hP : P ∈ A.paths) :
    last '' (A.shorten P hQ hP).paths = insert Q.last ((last '' A.paths) \ {P.last}) := by
  rw [shorten_paths, image_insert_eq, A.last_injOn.image_diff, inter_eq_right.mpr (by simpa),
    image_singleton]

/-! ### Extending a SetEnsemble by a path in `T` -/

/-- `pathr` refers to the path `P` in `T`. -/
private lemma pathr_mem (A : G.SetEnsemble) (hPfirst : A.vertexSet ∩ V(P) = {P.first}) :
    P.first ∈ A.vertexSet := singleton_subset_iff.mp <| hPfirst ▸ inter_subset_left

lemma pathr_first_eq_of_vertex_last (hAST : A.between S T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hPT : V(P) ⊆ T) :
    (A.of_vertex P.first <| A.pathr_mem hPfirst).last = P.first :=
  let hfirst := A.pathr_mem hPfirst
  hAST (A.of_vertex_mem_setEnsemble <| A.pathr_mem hPfirst)
  |>.eq_last_of_mem (A.mem_of_vertex hfirst) (hPT P.first_mem) |>.symm

lemma disjoint_pathr_of_ne_of_vertex (hAST : A.between S T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hPT : V(P) ⊆ T) (hQ : Q ∈ A.paths)
    (hQne : Q ≠ A.of_vertex P.first (A.pathr_mem hPfirst)) : Disjoint V(P) V(Q) := by
  contrapose! hQne
  apply A.disjoint.eq hQ (A.of_vertex_mem_setEnsemble (A.pathr_mem hPfirst))
  rw [not_disjoint_iff] at hQne ⊢
  use P.first, ?_, A.mem_of_vertex (A.pathr_mem hPfirst)
  obtain ⟨v, hvP, hvQ⟩ := hQne
  obtain rfl := hAST hQ |>.eq_last_of_mem hvQ (hPT hvP)
  convert hvQ using 1
  rw [eq_comm, ← mem_singleton_iff, ← hPfirst, mem_inter_iff, A.mem_vertexSet_iff]
  use ⟨Q, hQ, last_mem⟩, hvP

lemma vertexSet_inter_pathr_eq_last_inter_pathr (hAST : A.between S T) (hPT : V(P) ⊆ T) :
    A.vertexSet ∩ V(P) = (last '' A.paths) ∩ V(P) := by
  ext x
  simp only [mem_inter_iff, mem_vertexSet_iff, WList.mem_vertexSet_iff, mem_image,
    and_congr_left_iff]
  refine fun hx ↦ exists_congr fun P ↦ and_congr_right fun hP ↦ ?_
  simpa [eq_comm, hPT hx] using hAST hP |>.eq_last_iff_mem x |>.symm

@[simps! (attr := grind =)]
def extend_right (A : G.SetEnsemble) (hAST : A.between S T) (P : WList α β)
   (hPT : V(P) ⊆ T) (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hP : G.IsPath P) :
   G.SetEnsemble := by
  let Q := A.of_vertex P.first (A.pathr_mem hPfirst)
  refine A.path_remove Q |>.path_insert (Q ++ P) ?_ ?_
  · exact ((hAST <| A.of_vertex_mem_setEnsemble <| A.pathr_mem hPfirst).append_right hP
      hPT <| A.pathr_first_eq_of_vertex_last hAST hPfirst hPT).isPath
  simp only [vertexSet_eq_biUnion, path_remove_paths, mem_diff, mem_singleton_iff, ← ne_eq,
    disjoint_iUnion_left, and_imp]
  rintro R hR hne
  rw [append_vertexSet_of_eq <| A.pathr_first_eq_of_vertex_last hAST hPfirst hPT,
    disjoint_comm, disjoint_union_left]
  exact ⟨A.disjoint (A.of_vertex_mem_setEnsemble <| A.pathr_mem hPfirst) hR hne.symm,
    A.disjoint_pathr_of_ne_of_vertex hAST hPfirst hPT hR hne⟩

@[simp]
lemma between.extend_right (hAST : A.between S T) (hPT : V(P) ⊆ T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hP : G.IsPath P) :
    (A.extend_right hAST P hPT hPfirst hP).between (S \ (V(P) \ {P.first}))
    (T \ (V(P) \ {P.last})) := by
  rintro Q hQ
  obtain rfl | ⟨hQ, hQne⟩ := (by simpa using hQ) ; clear hQ
  · exact ((hAST <| A.of_vertex_mem_setEnsemble <| A.pathr_mem hPfirst).append_right hP
      hPT <| A.pathr_first_eq_of_vertex_last hAST hPfirst hPT)
  refine hAST hQ |>.diff_left_of_disjoint ?_ |>.diff_right_of_disjoint ?_
  · refine Disjoint.mono_left (A.subset_vertexSet_of_mem hQ) ?_
    rw [disjoint_comm, disjoint_diff_iff, inter_comm]
    exact hPfirst.subset
  exact (A.disjoint_pathr_of_ne_of_vertex hAST hPfirst hPT hQ hQne).symm.mono_right diff_subset

@[simp]
lemma extend_right_paths_encard (A : G.SetEnsemble) (hAST : A.between S T)
    (hAFin : A.paths.Finite) (hPT : V(P) ⊆ T) (hPfirst : A.vertexSet ∩ V(P) = {P.first})
    (hP : G.IsPath P) : (A.extend_right hAST P hPT hPfirst hP).paths.encard = A.paths.encard := by
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
    apply A.disjoint.eq haA (A.of_vertex_mem_setEnsemble (A.pathr_mem hPfirst)) ?_
    rw [not_disjoint_iff]
    exact ⟨(A.of_vertex P.first hf).first, by
      simp [A.pathr_first_eq_of_vertex_last hAST hPfirst hPT], first_mem⟩
  rw [extend_right_paths, encard_insert_of_notMem hPfirstQ, encard_diff_singleton_of_mem
  <| A.of_vertex_mem_setEnsemble (A.pathr_mem hPfirst)]
  refine tsub_add_cancel_of_le ?_
  exact Order.one_le_iff_pos.mpr hAcard

@[simp]
lemma extend_right_vertexSet (hAST : A.between S T) (hPT : V(P) ⊆ T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hP : G.IsPath P) :
    (A.extend_right hAST P hPT hPfirst hP).vertexSet = A.vertexSet ∪ V(P) := by
  simp_rw [Set.ext_iff, mem_vertexSet_iff, extend_right_paths, mem_insert_iff, mem_diff,
    mem_singleton_iff, exists_eq_or_imp, mem_union, mem_append_iff_of_eq
    (A.pathr_first_eq_of_vertex_last hAST hPfirst hPT), or_comm, or_assoc]
  apply fun v ↦ or_congr_right ?_
  by_cases hv : v ∈ A.of_vertex P.first (A.pathr_mem hPfirst)
  · simp only [hv, ne_eq, true_or, mem_vertexSet_iff, true_iff]
    use A.of_vertex P.first (A.pathr_mem hPfirst),
      (A.of_vertex_mem_setEnsemble (A.pathr_mem hPfirst)), hv
  simp only [hv, ne_eq, false_or, mem_vertexSet_iff]
  apply exists_congr fun Q ↦ and_congr_left fun hvQ ↦ ?_
  simp only [and_iff_left_iff_imp]
  exact fun _ heq ↦ hv <| heq ▸ hvQ

@[simp]
lemma extend_right_last (A : G.SetEnsemble) (hAST : A.between S T) (hPT : V(P) ⊆ T)
    (hPfirst : A.vertexSet ∩ V(P) = {P.first}) (hP : G.IsPath P) :
    last '' (A.extend_right hAST P hPT hPfirst hP).paths =
    insert P.last ((last '' A.paths) \ V(P)) := by
  simp only [extend_right_paths, image_insert_eq, append_last, A.last_injOn.image_diff,
    of_vertex_mem_setEnsemble, inter_singleton_of_mem, image_singleton]
  congr 1
  have hl : last '' A.paths ∩ V(P) = {P.first} := by
    apply subset_antisymm (hPfirst ▸ Set.inter_subset_inter_left _ A.image_last_subset)
    simp only [subset_inter_iff, singleton_subset_iff, mem_image, WList.mem_vertexSet_iff,
      P.first_mem, and_true]
    exact ⟨_, by simp, A.pathr_first_eq_of_vertex_last hAST hPfirst hPT⟩
  rw [diff_eq_diff_iff_inter_eq_inter, V(P).inter_comm, hl, ← image_singleton,
    ← A.last_injOn.image_inter (by simp) subset_rfl, inter_eq_left.mpr (by simp)]
  simp only [image_singleton, singleton_eq_singleton_iff]
  exact pathr_first_eq_of_vertex_last hAST hPfirst hPT

/-- Extends a SetEnsemble by a path in `P` when exactly two paths end somewhere in `P`.
  Send help. -/
@[simps! (attr := grind =)]
def extend_right_two (A : G.SetEnsemble) (hAST : A.between S T) (P : WList α β) (hPT : V(P) ⊆ T)
    [DecidablePred (· ∈ A.vertexSet)] (htwo : P.vertex.countP (· ∈ A.vertexSet) = 2)
    (hPP : G.IsPath P) : G.SetEnsemble := by
  have hPslen : (P.breakAt (· ∈ A.vertexSet)).length = 3 := by rw [breakAt_length, htwo]
  let P₀ := P.prefixUntil (· ∈ A.vertexSet)
  let P₂ := P.suffixFromLast (· ∈ A.vertexSet)
  have hex : ∃ u ∈ P, u ∈ A.vertexSet := by
    obtain ⟨u, hup, huA⟩ := (P.vertex.countP_pos_iff (p := (· ∈ A.vertexSet))).mp (by omega)
    exact ⟨u, hup, by simpa using huA⟩
  have hinter : A.vertexSet ∩ V(P₀.reverse) = {P₀.reverse.first} := by
    simp only [reverse_vertexSet, reverse_first]
    refine P.prefixUntil_inter_eq_last ?_
    obtain ⟨u, hup, huA⟩ := (P.vertex.countP_pos_iff (p := (· ∈ A.vertexSet))).mp (by omega)
    exact ⟨u, hup, by simpa using huA⟩
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
  refine A.extend_right hAST P₀.reverse (P₀.reverse_vertexSet ▸
    (P.prefixUntil_isPrefix _).subset.trans hPT) hinter
    (hPP.reverse.suffix (P.prefixUntil_isPrefix _).reverse_isSuffix_reverse)
    |>.extend_right (hAST.extend_right ?_ hinter ?_) P₂ ?_ ?_
    (hPP.suffix <| P.suffixFromLast_isSuffix _)
  · rw [reverse_vertexSet]
    exact (P.prefixUntil_isPrefix (· ∈ A.vertexSet)).subset.trans hPT
  · rw [reverse_isPath_iff]
    exact hPP.prefix (P.prefixUntil_isPrefix (· ∈ A.vertexSet))
  · simp only [reverse_vertexSet, reverse_last]
    rw [subset_diff]
    use (P.suffixFromLast_isSuffix _).subset.trans hPT, hdj.symm.mono_right diff_subset
  · simp only [extend_right_vertexSet, reverse_vertexSet, union_inter_distrib_right]
    rw [disjoint_iff_inter_eq_empty.mp hdj, union_empty]
    exact P.suffixFromLast_inter_eq_first hex

lemma between.extend_right_two (hAST : A.between S T) (hPT : V(P) ⊆ T)
    [DecidablePred (· ∈ A.vertexSet)] (htwo : P.vertex.countP (· ∈ A.vertexSet) = 2)
    (hPP : G.IsPath P) : (A.extend_right_two hAST P hPT htwo hPP).between (S \ (V(P) \ A.vertexSet))
    (T \ (V(P) \ {P.first, P.last})) := by
  simp only [SetEnsemble.extend_right_two]
  generalize_proofs hP₀T hP₀inter hP₀ hbtw hP₂T hP₂inter hP₂
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
  have hex : ∃ u ∈ P, u ∈ A.vertexSet := by
    obtain ⟨u, hup, huA⟩ := (P.vertex.countP_pos_iff (p := (· ∈ A.vertexSet))).mp (by omega)
    exact ⟨u, hup, by simpa using huA⟩
  have hPf : P₀.first = P.first := P.prefixUntil_first _
  have hPl : P₂.last = P.last := P.suffixFromLast_last _
  have hP₀f : V(P₀) \ {P₀.first} = V(P₀) \ {P.first, P.last} := by
    rw [← hPf, ← hPl, pair_comm, diff_insert_of_notMem]
    exact hdj.notMem_of_mem_right last_mem
  have hP₀l : V(P₀) \ {P₀.last} = V(P₀) \ A.vertexSet := by
    rw [diff_eq_diff_iff_inter_eq_inter, P.prefixUntil_inter_eq_last hex, inter_eq_left]
    simp
  have hP₂f : V(P₂) \ {P₂.first} = V(P₂) \ A.vertexSet := by
    rw [diff_eq_diff_iff_inter_eq_inter, P.suffixFromLast_inter_eq_first hex,
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
      List.mem_filter.mpr (by simp [hxP, hxA] : x ∈ P.vertex ∧ decide (x ∈ A.vertexSet) = true)
    obtain rfl | rfl := by
      obtain ⟨hP₀leq, hP₂feq⟩ := by
        have := hP ▸ P.breakAt_isChain_eq (· ∈ A.vertexSet)
        simpa using this
      rw [hP] at this
      simpa [← hP₀leq] using this
    · exact mem_union_left _ last_mem
    exact mem_union_right _ first_mem
  refine (hbtw.extend_right hP₂T hP₂inter hP₂).left ?_ |>.right ?_
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
  simp only [extend_right_vertexSet, reverse_vertexSet, disjoint_union_left, and_assoc]
  refine ⟨?_, disjoint_sdiff_right.mono_right diff_subset, disjoint_sdiff_right⟩
  rwa [diff_diff, disjoint_comm, disjoint_diff_iff]

@[simp]
lemma extend_right_two_vertexSet (hAST : A.between S T) (hPT : V(P) ⊆ T)
    [DecidablePred (· ∈ A.vertexSet)] (htwo : P.vertex.countP (· ∈ A.vertexSet) = 2)
    (hPP : G.IsPath P) :
    (A.extend_right_two hAST P hPT htwo hPP).vertexSet =
    A.vertexSet ∪ V(P.prefixUntil (· ∈ A.vertexSet)) ∪ V(P.suffixFromLast (· ∈ A.vertexSet)) := by
  simp [extend_right_two, extend_right_vertexSet]

@[simp]
lemma extend_right_two_paths_encard (hAST : A.between S T) (hAFin : A.paths.Finite)
    (hPT : V(P) ⊆ T) [DecidablePred (· ∈ A.vertexSet)]
    (htwo : P.vertex.countP (· ∈ A.vertexSet) = 2) (hPP : G.IsPath P) :
    (A.extend_right_two hAST P hPT htwo hPP).paths.encard = A.paths.encard := by
  rw [extend_right_two, extend_right_paths_encard, extend_right_paths_encard _ hAST hAFin]
  simp only [extend_right_paths, mem_vertexSet_iff, reverse_first,
    prefixUntil_last_eq_suffixFrom_first, finite_insert]
  exact hAFin.diff

@[simp]
lemma extend_right_two_last (hAST : A.between S T) (hPT : V(P) ⊆ T)
    [DecidablePred (· ∈ A.vertexSet)] (htwo : P.vertex.countP (· ∈ A.vertexSet) = 2)
    (hPP : G.IsPath P) :
    last '' (A.extend_right_two hAST P hPT htwo hPP).paths =
    (last '' A.paths) \ V(P) ∪ {P.first, P.last} := by
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
  have hlast : V(P) ∩ (last '' A.paths) = V(P) ∩ A.vertexSet := by
    ext x
    simp only [mem_inter_iff, mem_image, WList.mem_vertexSet_iff, mem_vertexSet_iff,
      and_congr_right_iff]
    refine fun hx ↦ exists_congr fun Q ↦ and_congr_right fun hQ ↦ ?_
    simpa [eq_comm, hPT hx] using hAST hQ |>.eq_last_iff_mem x
  have hex : ∃ u ∈ P, u ∈ A.vertexSet := by
    obtain ⟨u, hup, huA⟩ := (P.vertex.countP_pos_iff (p := (· ∈ A.vertexSet))).mp (by omega)
    exact ⟨u, hup, by simpa using huA⟩

  have := P.breakAt_tail_map_first_eq_vertex_filter (· ∈ A.vertexSet)
  simp only [SetEnsemble.extend_right_two]
  rw [extend_right_last, extend_right_last, pair_comm]
  simp only [mem_vertexSet_iff, suffixFromLast_last, reverse_last, prefixUntil_first,
    reverse_vertexSet, union_insert, union_singleton]
  rw [insert_diff_of_notMem, diff_diff]
  congr 2
  rw [diff_eq_diff_iff_inter_eq_inter]
  ext x
  simp only [mem_vertexSet_iff, mem_inter_iff, mem_union, WList.mem_vertexSet_iff, mem_image,
    and_congr_left_iff, forall_exists_index, and_imp]
  rintro Q hQ rfl
  have hQlast : Q.last ∈ A.vertexSet := by simp; use Q, hQ, last_mem
  have := (Set.ext_iff.mp <| P.breakAt_tail_map_first_eq_inter A.vertexSet) Q.last
  simp only [mem_vertexSet_iff, List.map_tail, mem_setOf_eq, mem_inter_iff, WList.mem_vertexSet_iff,
    hQlast, and_true] at this
  convert this
  rw [hP]
  obtain ⟨hP₀leq, hP₂feq⟩ := by
    have := hP ▸ P.breakAt_isChain_eq (· ∈ A.vertexSet)
    simpa using this
  simp only [mem_vertexSet_iff, List.map_cons, ← hP₀leq, List.map_nil, List.tail_cons,
    List.mem_cons, List.not_mem_nil, or_false]
  apply or_congr
  · refine ⟨fun h => ?_, fun h => h ▸ last_mem⟩
    rw [eq_comm, ← P.prefixUntil_last_eq_iff_prop hex]
    simp [hQlast, h]
  refine ⟨fun h => ?_, fun h => h ▸ first_mem⟩
  rw [eq_comm, ← P.suffixFromLast_first_eq_iff_prop hex]
  simp [hQlast, h]

  have hPf : P₀.first = P.first := P.prefixUntil_first _
  simp only [mem_vertexSet_iff, WList.mem_vertexSet_iff]
  exact hdj.notMem_of_mem_left <| hPf ▸ first_mem

@[simp]
def extend_right_le_two (A : G.SetEnsemble) (hAST : A.between S (T ∪ V(P))) (hP : G.IsPath P)
    [DecidablePred (· ∈ A.vertexSet)] (hAP : P.vertex.countP (· ∈ A.vertexSet) ≤ 2) :
    G.SetEnsemble := by
  by_cases h0 : P.vertex.countP (· ∈ A.vertexSet) = 0
  · exact A

  by_cases h1 : P.vertex.countP (· ∈ A.vertexSet) = 1
  · by_cases hPf : P.first ∈ A.vertexSet
    · exact A
    let P' := P.suffixFromLast (· ∈ A.vertexSet)
    refine A.extend_right hAST (P := P') ((P.suffixFromLast_isSuffix _).subset.trans
      subset_union_right) ?_ (hP.suffix <| P.suffixFromLast_isSuffix _)
    ext x
    simp only [mem_inter_iff, WList.mem_vertexSet_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxA, hxP⟩ => (suffixFromLast_first_eq_of_prop hxP hxA).symm,
      fun h => ⟨?_, h ▸ first_mem⟩⟩
    subst x
    apply suffixFromLast_prop_first
    rw [List.countP_eq_length_filter, List.length_eq_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    have ⟨hyP, hyA⟩ := List.mem_filter.mp <| hy ▸ (show y ∈ [y] from by simp)
    exact ⟨y, hyP, by simpa using hyA⟩

  have h2 : P.vertex.countP (· ∈ A.vertexSet) = 2 := by omega
  exact A.extend_right_two hAST P subset_union_right h2 hP

lemma extend_right_le_two_last_of_one (hAST : A.between S (T ∪ V(P))) (hP : G.IsPath P)
    [DecidablePred (· ∈ A.vertexSet)] (hAP : P.vertex.countP (· ∈ A.vertexSet) = 1)
    (hPf : P.first ∉ A.vertexSet) : last '' (A.extend_right_le_two hAST hP (by omega)).paths =
    insert P.last ((last '' A.paths) \ V(P)) := by
  simp only [extend_right_le_two, mem_vertexSet_iff, hAP, one_ne_zero, ↓reduceDIte, hPf,
    extend_right_paths, image_insert_eq, append_last, suffixFromLast_last, A.last_injOn.image_diff]
  rw [inter_eq_right.mpr (by simp), image_singleton]
  congr 1
  rw [diff_eq_diff_iff_inter_eq_inter]
  let P' := P.suffixFromLast (· ∈ A.vertexSet)
  generalize_proofs hP'f
  have heq := hAST (A.of_vertex_mem_setEnsemble hP'f) |>.eq_last_of_mem (A.mem_of_vertex hP'f) <|
    (subset_union_right <| (P.suffixFromLast_isSuffix _).subset first_mem)
  rw [← heq]
  ext x
  refine ⟨fun ⟨h1, h2⟩ => mem_inter ?_ h2, fun ⟨h1, h2⟩ => mem_inter ?_ h2⟩
  · simp only [mem_vertexSet_iff, mem_singleton_iff] at h1
    subst x
    exact (P.suffixFromLast_isSuffix _).subset first_mem
  simp only [mem_vertexSet_iff, mem_singleton_iff]
  rw [List.countP_eq_length_filter, List.length_eq_one_iff] at hAP
  obtain ⟨y, hy⟩ := hAP
  have hy' : ∀ x, x ∈ P.vertex.filter (· ∈ A.vertexSet) ↔ x = y := by simp [hy]
  simp only [List.mem_filter, mem_vertex, decide_eq_true_eq] at hy'; clear hy
  obtain rfl := (hy' P'.first).mp ⟨(P.suffixFromLast_isSuffix _).subset first_mem, hP'f⟩
  refine (hy' x).mp ⟨h1, ?_⟩
  simp only [mem_image, mem_vertexSet_iff] at h2 ⊢
  obtain ⟨Q, hQ, rfl⟩ := h2
  use Q, hQ, last_mem

lemma extend_right_le_two_last_of_two (hAST : A.between S (T ∪ V(P))) (hP : G.IsPath P)
    [DecidablePred (· ∈ A.vertexSet)] (hAP : P.vertex.countP (· ∈ A.vertexSet) = 2) :
    last '' (A.extend_right_le_two hAST hP (by omega)).paths =
    ((last '' A.paths) \ V(P)) ∪ {P.first, P.last} := by
  simp only [extend_right_le_two, hAP, OfNat.ofNat_ne_zero, ↓reduceDIte, OfNat.ofNat_ne_one]
  rw [extend_right_two_last]

lemma between.extend_right_le_two (hAST : A.between S (T ∪ V(P))) (hP : G.IsPath P)
    [DecidablePred (· ∈ A.vertexSet)] (hAP : P.vertex.countP (· ∈ A.vertexSet) ≤ 2)
    (hST : V(P) ∩ S ⊆ A.vertexSet) :
    (A.extend_right_le_two hAST hP hAP).between S ((T \ V(P)) ∪ {P.first, P.last}) := by
  simp only [SetEnsemble.extend_right_le_two]
  by_cases h0 : P.vertex.countP (· ∈ A.vertexSet) = 0
  · simp only [mem_vertexSet_iff, h0, ↓reduceDIte]
    apply hAST.right
    rw [symmDiff_of_ge (union_subset_union diff_subset (by simp [pair_subset])), ← diff_diff,
      union_diff_diff]
    apply Disjoint.mono_right <| diff_subset
    rw [disjoint_comm, disjoint_iff_forall_notMem]
    simp only [List.countP_eq_zero, mem_vertex, decide_eq_true_eq] at h0
    exact h0

  by_cases h1 : P.vertex.countP (· ∈ A.vertexSet) = 1
  · simp only [mem_vertexSet_iff, h1, one_ne_zero, ↓reduceDIte]
    rw [List.countP_eq_length_filter, List.length_eq_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    have hy' : ∀ x, x ∈ P.vertex.filter (· ∈ A.vertexSet) ↔ x = y := by simp [hy]
    simp only [List.mem_filter, mem_vertex, decide_eq_true_eq] at hy'; clear hy h0
    have hex : ∃ u ∈ P, u ∈ A.vertexSet := ⟨y, (hy' y).mpr rfl⟩
    split_ifs with h
    · obtain rfl := (hy' P.first).mp ⟨first_mem, h⟩
      apply hAST.right
      rw [symmDiff_of_ge (union_subset_union diff_subset (by simp [pair_subset]))]
      apply Disjoint.mono_right <| (?_ : _ ⊆ V(P) \ {P.first, P.last})
      rw [disjoint_comm, disjoint_diff_iff]
      rintro x
      rw [mem_inter_iff, WList.mem_vertexSet_iff, hy']
      rintro rfl
      simp
      · rw [← diff_diff]
        apply diff_subset_diff_left
        rw [union_diff_diff]
    let P' := P.suffixFromLast (· ∈ A.vertexSet)
    have hP'sf := P.suffixFromLast_isSuffix (· ∈ A.vertexSet)
    generalize_proofs hP'su heq hP'
    refine hAST.extend_right hP'su heq hP' |>.left ?_ |>.right ?_
    · convert disjoint_empty _
      change ((S \ (V(P') \ {P'.first})) ∆ S) = _
      rw [diff_symmDiff, ← inter_diff_assoc, diff_eq_empty, ← heq, inter_comm]
      exact subset_inter ((inter_subset_inter hP'sf.subset subset_rfl).trans hST) inter_subset_left
    rw [extend_right_vertexSet]
    change Disjoint (A.vertexSet ∪ V(P')) (((T ∪ V(P)) \ (V(P') \ {P'.last})) ∆
      (T \ V(P) ∪ {P.first, P.last}))
    have hr : (((T ∪ V(P)) \ (V(P') \ {P'.last})) ∆ (T \ V(P) ∪ {P.first, P.last})) =
      ((V(P) \ V(P')) \ {P.first}) := by
      rw [suffixFromLast_last]
      ext x
      simp +contextual only [union_insert, union_singleton, symmDiff_def, sup_eq_union, mem_union,
        mem_diff, WList.mem_vertexSet_iff, mem_singleton_iff, not_and, not_not, mem_insert_iff,
        not_or, Classical.not_imp, iff_def, or_true, IsEmpty.forall_iff, and_self,
        not_false_eq_true, implies_true, and_true, true_and, not_true_eq_false, and_false, or_false,
        false_or, false_and, imp_false, and_imp]
      refine ⟨?_, ?_⟩
      · rintro (⟨⟨hTP, hxP'⟩, hxf, hxl, hxTP⟩ | ⟨(rfl | rfl | hxT), himp⟩)
        · use (by use hTP.elim hxTP id, fun h => hxl (hxP' h)), hxf
        · rw [← hP'sf.eq_of_first_mem hP.nodup
            (himp <| Or.inr first_mem).1] at h
          exact (h <| P.suffixFromLast_prop_first hex).elim
        · exact ((himp <| Or.inr last_mem).2 rfl).elim
        exact (hxT.2 <| hP'sf.subset (himp <| Or.inl hxT.1).1).elim
      rintro _ h _ rfl
      rw [← P.suffixFromLast_last (· ∈ A.vertexSet)] at h
      exact h last_mem
    rw [hr, disjoint_iff_inter_eq_empty]
    ext x
    simp only [mem_inter_iff, mem_union, WList.mem_vertexSet_iff, mem_diff, mem_singleton_iff,
      mem_empty_iff_false, iff_false, not_and, not_not, and_imp]
    rintro (hxA | hxP'1) hxP hxP'
    · obtain rfl := (hy' P'.first).mp ⟨hP'sf.subset first_mem, P.suffixFromLast_prop_first hex⟩
      obtain rfl := (hy' x).mp ⟨hxP, hxA⟩
      exact (hxP' first_mem).elim
    exact (hxP' hxP'1).elim

  have h2 : P.vertex.countP (· ∈ A.vertexSet) = 2 := by omega
  simp only [mem_vertexSet_iff, h2, OfNat.ofNat_ne_zero, ↓reduceDIte, OfNat.ofNat_ne_one]
  generalize_proofs hP'su
  refine hAST.extend_right_two hP'su h2 hP |>.left ?_ |>.right ?_
  · convert disjoint_empty _
    rwa [diff_symmDiff, ← inter_diff_assoc, diff_eq_empty, inter_comm]
  convert disjoint_empty _
  ext x
  simp +contextual only [union_insert, union_singleton, symmDiff_def, mem_diff, mem_union,
    WList.mem_vertexSet_iff, first_mem, or_true, mem_insert_iff, mem_singleton_iff, true_or,
    not_true_eq_false, and_false, not_false_eq_true, and_self, insert_diff_of_mem, last_mem,
    sup_eq_union, not_or, not_and, not_not, Classical.not_imp, mem_empty_iff_false, iff_def,
    imp_false, and_imp, or_false, false_and, implies_true, and_true, IsEmpty.forall_iff]
  rintro (hxT | hxP) himp hxf hxl
  · use hxT
    exact fun a ↦ hxl (himp a hxf)
  exact (hxl (himp hxP hxf)).elim

end SetEnsemble
end Graph
