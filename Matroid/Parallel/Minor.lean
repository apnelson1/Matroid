module

public import Matroid.Parallel.Basic

@[expose] public section

open Set

namespace Matroid

variable {α : Type*} {M N : Matroid α} {e f g : α} {I F X D : Set α} {P : Set α → Prop}
    {cl : Set α → Set α}

structure IsClosedBy (M : Matroid α) (P : Set α → Prop) (cl : Set α → Set α) (X : Set α) :
    Prop where
  subset_ground : X ⊆ M.E
  closed : ∀ S ⊆ X, P S → cl S ⊆ X

lemma IsClosedBy.eq_iUnion₂ (hX : M.IsClosedBy P cl X)
    (hXcl : ∀ e ∈ X, e ∈ cl {e}) (hP : ∀ e ∈ X, P {e}) :
    X = ⋃ (S : Set α) (_ : S ⊆ X ∧ P S), cl S :=
  (iUnion₂_subset fun S ⟨hS, hS'⟩ ↦ hX.closed S hS hS').antisymm' fun e heX ↦
    mem_iUnion₂.2 ⟨{e}, ⟨by simpa, hP e heX⟩, hXcl e heX⟩

lemma isClosedBy_ground (M : Matroid α) {P : Set α → Prop} {cl : Set α → Set α}
    (h : ∀ X ⊆ M.E, P X → cl X ⊆ M.E) : M.IsClosedBy P cl M.E :=
  ⟨subset_rfl, h⟩

def relClosure (M : Matroid α) (P : Set α → Prop) (cl : Set α → Set α) (X : Set α) : Set α :=
  sInf {S | M.IsClosedBy P cl S ∧ X ∩ M.E ⊆ S}

lemma relClosure_subset_ground (M : Matroid α) (h : ∀ X ⊆ M.E, P X → cl X ⊆ M.E) :
    M.relClosure P cl X ⊆ M.E :=
  sInf_le ⟨isClosedBy_ground _ h, inter_subset_right⟩

def IsParallelClosed (M : Matroid α) (X : Set α) : Prop := M.IsClosedBy Set.Subsingleton M.closure X

lemma IsParallelClosed.subset_ground (h : M.IsParallelClosed X) : X ⊆ M.E :=
  IsClosedBy.subset_ground h

lemma IsFlat.isParallelClosed (hF : M.IsFlat F) : M.IsParallelClosed F :=
  ⟨hF.subset_ground, fun _ hPF _ ↦ hF.closure_subset_of_subset hPF⟩

@[simp]
lemma isParallelClosed_ground (M : Matroid α) : M.IsParallelClosed M.E :=
  M.ground_isFlat.isParallelClosed

def parallelClosure (M : Matroid α) := M.relClosure Set.Subsingleton M.closure

lemma parallelClosure_subset_ground (M : Matroid α) (X : Set α) : M.parallelClosure X ⊆ M.E :=
  relClosure_subset_ground _ (by simp [closure_subset_ground])

lemma subset_parallelClosure (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.parallelClosure X :=
  le_sInf fun Y ⟨_, hXY⟩ ↦ by grw [← hXY, inter_eq_self_of_subset_left hX]

lemma parallelClosure_eq_biUnion (M : Matroid α) (X : Set α) :
    M.parallelClosure X = M.loops ∪ ⋃ e ∈ X, M.closure {e} := by
  rw [parallelClosure, ]
  -- refine subset_antisymm ?_ <| union_subset (le_sInf ?_) <| iUnion₂_subset ?_
  -- · refine sInf_le ⟨⟨by aesop_mat, fun P hP hPss ↦ ?_⟩, fun e ⟨heX, heE⟩ ↦ ?_⟩
  --   · rw [← closure_inter_ground]
  --     obtain hempt | ⟨e, he⟩ := (hPss.anti (show P ∩ M.E ⊆ P by simp)).eq_empty_or_singleton
  --     · simp [hempt, loops]
  --     obtain hl | hnl :=
  --       M.isLoop_or_isNonloop e (by simpa using he.superset.trans inter_subset_right)
  --     · simp [he, hl.closure]
  --     grw [← show P ∩ M.E ⊆ P by simp, he, singleton_subset_iff, mem_union,
  --       or_iff_right (by simpa using hnl.not_isLoop), mem_iUnion₂] at hP
  --     simp_rw [exists_prop, ← hnl.parallel_iff_mem_closure] at hP
  --     obtain ⟨f, hfX, hef⟩ := hP
  --     grw [he, ← subset_union_right, hef.closure_eq_closure]
  --     exact subset_biUnion_of_mem (u := fun x ↦ M.closure {x}) hfX
  --   exact .inr <| mem_iUnion₂_of_mem heX <| mem_closure_self M e heE
  -- · exact fun Y ⟨hY, hXY⟩ ↦ hY.closed ∅ (by simp) (by simp)
  -- simp_rw [← M.closure_inter_ground {_}]
  -- exact fun e heX ↦ le_sInf fun Y hY ↦ hY.1.closed _ (by grind) <|
  --   subsingleton_singleton.anti inter_subset_left

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
