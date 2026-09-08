module

public import Matroid.Parallel.Basic
public import Matroid.Simple

@[expose] public section

open Set

namespace Matroid

variable {α : Type*} {M N : Matroid α} {e f g : α} {I F X Y D : Set α} {P : Set α → Prop}
    {cl : Set α → Set α}

@[mk_iff]
structure IsClosedBy (M : Matroid α) (P : Set α → Prop) (cl : Set α → Set α) (X : Set α) :
    Prop where
  subset_ground : X ⊆ M.E
  closed : ∀ S ⊆ X, P S → cl S ⊆ X

lemma IsClosedBy.eq_iUnion₂ (hX : M.IsClosedBy P cl X) (hXcl : ∀ e ∈ M.E, e ∈ X → e ∈ cl {e})
    (hP : ∀ e ∈ M.E, e ∈ X → P {e}) : X = ⋃ (S : Set α) (_ : S ⊆ X ∧ P S), cl S :=
  (iUnion₂_subset fun S ⟨hS, hS'⟩ ↦ hX.closed S hS hS').antisymm' fun e heX ↦ mem_iUnion₂.2
    ⟨{e}, by simpa [hP e (hX.subset_ground heX) heX], hXcl e (hX.subset_ground heX) heX⟩

lemma isClosedBy_ground (M : Matroid α) {P : Set α → Prop} {cl : Set α → Set α}
    (h : ∀ X ⊆ M.E, P X → cl X ⊆ M.E) : M.IsClosedBy P cl M.E :=
  ⟨subset_rfl, h⟩

def closureBy (M : Matroid α) (P : Set α → Prop) (cl : Set α → Set α) (X : Set α) : Set α :=
  sInf {S | M.IsClosedBy P cl S ∧ X ∩ M.E ⊆ S}

lemma closureBy_subset_ground (M : Matroid α) (h : ∀ X ⊆ M.E, P X → cl X ⊆ M.E) :
    M.closureBy P cl X ⊆ M.E :=
  sInf_le ⟨isClosedBy_ground _ h, inter_subset_right⟩

@[simp]
lemma closureBy_inter_ground (M : Matroid α) :
    M.closureBy P cl (X ∩ M.E) = M.closureBy P cl X := by
  simp [closureBy, inter_assoc]

@[gcongr]
lemma closureBy_subset (M : Matroid α) (hXY : X ⊆ Y) :
    M.closureBy P cl X ⊆ M.closureBy P cl Y := by
  refine le_sInf fun S hS ↦ sInf_le ⟨hS.1, by grw [hXY, hS.2]⟩

lemma subset_closureBy (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.closureBy P cl X :=
  le_sInf fun F hF ↦ by grw [← inter_eq_self_of_subset_left hX, hF.2]

lemma isClosedBy_closureBy (M : Matroid α) (h : ∀ X ⊆ M.E, P X → cl X ⊆ M.E) (X : Set α) :
    M.IsClosedBy P cl (M.closureBy P cl X) := by
  refine ⟨closureBy_subset_ground _ h, fun S hS hPS ↦ le_sInf fun Y hY ↦ ?_⟩
  simp only [closureBy, sInf_eq_sInter, subset_sInter_iff, mem_ofPred_eq, and_imp] at hS
  exact hY.1.closed _ (hS Y hY.1 hY.2) hPS

lemma IsClosedBy.closureBy_eq_self (h : M.IsClosedBy P cl X) : M.closureBy P cl X = X :=
  (subset_closureBy M X h.subset_ground).antisymm' <| sInf_le ⟨h, inter_subset_left⟩

lemma closureBy_closureBy (h : ∀ X ⊆ M.E, P X → cl X ⊆ M.E) :
    M.closureBy P cl (M.closureBy P cl X) = M.closureBy P cl X :=
  (isClosedBy_closureBy M h X).closureBy_eq_self

def IsParallelClosed (M : Matroid α) (X : Set α) : Prop := M.IsClosedBy Set.Subsingleton M.closure X

lemma IsParallelClosed.subset_ground (h : M.IsParallelClosed X) : X ⊆ M.E :=
  IsClosedBy.subset_ground h

lemma IsFlat.isParallelClosed (hF : M.IsFlat F) : M.IsParallelClosed F :=
  ⟨hF.subset_ground, fun _ hPF _ ↦ hF.closure_subset_of_subset hPF⟩

@[simp]
lemma isParallelClosed_ground (M : Matroid α) : M.IsParallelClosed M.E :=
  M.ground_isFlat.isParallelClosed

def parallelClosure (M : Matroid α) := M.closureBy Set.Subsingleton M.closure

lemma parallelClosure_subset_ground (M : Matroid α) (X : Set α) : M.parallelClosure X ⊆ M.E :=
  closureBy_subset_ground _ (by simp [closure_subset_ground])

lemma subset_parallelClosure (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.parallelClosure X :=
  le_sInf fun Y ⟨_, hXY⟩ ↦ by grw [← hXY, inter_eq_self_of_subset_left hX]

lemma parallelClosure_eq_biUnion (M : Matroid α) (X : Set α) :
    M.parallelClosure X = M.loops ∪ ⋃ e ∈ X, M.closure {e} := by
  rw [parallelClosure]
  refine subset_antisymm ?_ <| union_subset (le_sInf ?_) <| iUnion₂_subset ?_
  · refine sInf_le ⟨⟨by aesop_mat, fun P hP hPss ↦ ?_⟩, fun e ⟨heX, heE⟩ ↦ ?_⟩
    · rw [← closure_inter_ground]
      obtain hempt | ⟨e, he⟩ := (hPss.anti (show P ∩ M.E ⊆ P by simp)).eq_empty_or_singleton
      · simp [hempt, loops]
      obtain hl | hnl :=
        M.isLoop_or_isNonloop e (by simpa using he.superset.trans inter_subset_right)
      · simp [he, hl.closure]
      grw [← show P ∩ M.E ⊆ P by simp, he, singleton_subset_iff, mem_union,
        or_iff_right (by simpa using hnl.not_isLoop), mem_iUnion₂] at hP
      simp_rw [exists_prop, ← hnl.parallel_iff_mem_closure] at hP
      obtain ⟨f, hfX, hef⟩ := hP
      grw [he, ← subset_union_right, hef.closure_eq_closure]
      exact subset_biUnion_of_mem (u := fun x ↦ M.closure {x}) hfX
    exact .inr <| mem_iUnion₂_of_mem heX <| mem_closure_self M e heE
  · exact fun Y ⟨hY, hXY⟩ ↦ hY.closed ∅ (by simp) (by simp)
  simp_rw [← M.closure_inter_ground {_}]
  exact fun e heX ↦ le_sInf fun Y hY ↦ hY.1.closed _ (by grind) <|
    subsingleton_singleton.anti inter_subset_left

@[simp]
lemma parallelClosure_empty (M : Matroid α) : M.parallelClosure ∅ = M.loops := by
  simp [parallelClosure_eq_biUnion]

lemma parallelClosure_eq_biUnion_of_nonempty (M : Matroid α) (hX : X.Nonempty) :
    M.parallelClosure X = ⋃ e ∈ X, M.closure {e} := by
  grw [parallelClosure_eq_biUnion, union_eq_right, ← subset_biUnion_of_mem hX.choose_spec,
    loops_subset_closure]

lemma mem_parallelClosure_iff : e ∈ M.parallelClosure X ↔ M.IsLoop e ∨ ∃ f ∈ X, M.Parallel e f := by
  simp only [parallelClosure_eq_biUnion, mem_union, mem_loops_iff, mem_iUnion, exists_prop]
  refine ⟨fun h ↦ Or.elim h Or.inl (fun ⟨f, hfX, hef⟩ ↦ ?_),
    Or.imp id fun ⟨f, hfX, he⟩ ↦ ⟨f, hfX, he.mem_closure⟩ ⟩
  obtain hel | henl := M.isLoop_or_isNonloop e
  · exact .inl hel
  simp_rw [henl.parallel_iff_mem_closure]
  exact .inr ⟨f, hfX, hef⟩

lemma parallelClosure_union (M : Matroid α) (X Y : Set α) :
    M.parallelClosure (X ∪ Y) = M.parallelClosure X ∪ M.parallelClosure Y := by
  simp_rw [parallelClosure_eq_biUnion, ← union_union_distrib_left, ← biUnion_union]

@[gcongr]
lemma parallelClosure_subset {Y : Set α} (M : Matroid α) (hXY : X ⊆ Y) :
    M.parallelClosure X ⊆ M.parallelClosure Y := by
  grw [parallelClosure_eq_biUnion, parallelClosure_eq_biUnion, ← biUnion_subset_biUnion_left hXY]

def SPclosure (M : Matroid α) (U : Set α) : Set α :=
    {x | ∃ (N : Matroid α) (b : Bool), (N.bDual b) ≤si (M.bDual b) ∧
      ∃ e ∈ U, (N.bDual !b).Parallel e x}


/-- A set `IsSeriesParallelClosed` if it contains or is disjoint from every parallel pair and
every series pair. -/
def IsSeriesParallelClosed (M : Matroid α) (X : Set α) : Prop :=
  M.IsClosedBy Set.Subsingleton (fun S ↦ M.closure S ∪ M✶.closure S) X

/-- The `seriesParallelClosure` of `X` is the closure of `X` under series and parallel
extensions. -/
def seriesParallelClosure (M : Matroid α) (X : Set α) : Set α :=
  M.closureBy Set.Subsingleton (fun S ↦ M.closure S ∪ M✶.closure S) X

@[simp]
lemma isSeriesParallelClosed_dual_iff :
    M✶.IsSeriesParallelClosed X ↔ M.IsSeriesParallelClosed X := by
  simp [IsSeriesParallelClosed, isClosedBy_iff, and_comm]

alias ⟨IsSeriesParallelClosed.of_dual, IsSeriesParallelClosed.dual⟩ :=
  isSeriesParallelClosed_dual_iff

@[simp]
lemma seriesParallelClosure_dual (M : Matroid α) (X : Set α) :
    M✶.seriesParallelClosure X = M.seriesParallelClosure X := by
  simp [seriesParallelClosure, closureBy, isClosedBy_iff, and_comm]

@[simp]
lemma closure_dual_subset_ground (M : Matroid α) (X : Set α) : M✶.closure X ⊆ M.E :=
  M✶.closure_subset_ground X

@[simp]
lemma isSeriesParallelClosed_seriesParallelClosure (M : Matroid α) (X : Set α) :
    M.IsSeriesParallelClosed (M.seriesParallelClosure X) :=
  isClosedBy_closureBy _ (by simp [M.closure_dual_subset_ground, M.closure_subset_ground]) _

lemma subset_seriesParallelClosure (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.seriesParallelClosure X :=
  subset_closureBy _ _ hX

@[simp]
lemma seriesParallelClosure_seriesParallelClosure (M : Matroid α) (X : Set α) :
    M.seriesParallelClosure (M.seriesParallelClosure X) = M.seriesParallelClosure X :=
  closureBy_closureBy (by simp [M.closure_dual_subset_ground, M.closure_subset_ground])

@[gcongr]
lemma seriesParallelClosure_subset (M : Matroid α) (hXY : X ⊆ Y) :
    M.seriesParallelClosure X ⊆ M.seriesParallelClosure Y :=
  M.closureBy_subset hXY

lemma seriesParallelClosure_subset_of_subset (M : Matroid α) (hXY : X ⊆ M.seriesParallelClosure Y) :
    M.seriesParallelClosure X ⊆ M.seriesParallelClosure Y := by
  simpa using M.seriesParallelClosure_subset hXY
