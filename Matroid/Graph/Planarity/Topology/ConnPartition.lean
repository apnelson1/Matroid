import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
-- import Matroid.ForMathlib.Partition.Set
import Matroid.Graph.Basic

open Set Function Partition
variable {α : Type*} [TopologicalSpace α] {S T T₁ T₂ : Set α} {u v w : α}

section ComponentPartition

def ComponentPartition (S : Set α) : Partition (Set α) :=
  Partition.ofRel (Eq on connectedComponentIn S)



end ComponentPartition

section PathComponentPartition

instance : IsTrans α (JoinedIn S) where
  trans _ _ _ := JoinedIn.trans

instance : Std.Symm (JoinedIn S) where
  symm _ _ := JoinedIn.symm

def PathComponentPartition (S : Set α) : Partition (Set α) := Partition.ofRel (JoinedIn S)

@[simp]
lemma pathComponentPartition_supp (S : Set α) : (PathComponentPartition S).supp = S := by
  ext v
  simp only [PathComponentPartition, ofRel_supp, Relation.mem_domain_iff]
  exact ⟨fun ⟨x, hx⟩ => hx.source_mem, fun hv => ⟨v, JoinedIn.refl hv⟩⟩

@[simp]
lemma pathComponentPartition_partOf (S : Set α) :
    (PathComponentPartition S).partOf v = pathComponentIn S v := by
  simp [PathComponentPartition, partOf, Relation.fiber, pathComponentIn, comm_of]

lemma mem_pathComponentPartition_iff (S T : Set α) :
    T ∈ PathComponentPartition S ↔ ∃ v ∈ S, pathComponentIn S v = T := by
  refine ⟨fun hT => ?_, fun ⟨v, hv, h⟩ => h ▸ pathComponentPartition_partOf S ▸ partOf_mem
    <| by simpa⟩
  obtain ⟨v, hv⟩ := (PathComponentPartition S).nonempty_of_mem hT
  exact ⟨v, pathComponentPartition_supp S ▸ (PathComponentPartition S).subset_of_mem hT hv,
    pathComponentPartition_partOf S ▸ (PathComponentPartition S).eq_partOf_of_mem hT hv |>.symm⟩

lemma pathComponentPartition_parts (S : Set α) :
    (PathComponentPartition S).parts = (pathComponentIn S) '' S := by
  ext T
  rw [mem_parts, mem_pathComponentPartition_iff, mem_image]

lemma IsOpen.pathComponentPartition_isOpen [LocPathConnectedSpace α]
    (hT : T ∈ PathComponentPartition S) (h : IsOpen S) : IsOpen T := by
  obtain ⟨v, hv, rfl⟩ := mem_pathComponentPartition_iff S T |>.mp hT
  exact h.pathComponentIn v

lemma frontier_subset_of_mem_pathComponentPartition [LocPathConnectedSpace α]
    (hT : T ∈ PathComponentPartition S) (h : IsOpen S) : frontier T ⊆ Sᶜ := by
  rintro u ⟨huc, hui⟩
  rw [(h.pathComponentPartition_isOpen hT).interior_eq] at hui
  obtain ⟨v, -, rfl⟩ := mem_pathComponentPartition_iff S T |>.mp hT
  by_contra! huS
  simp only [mem_compl_iff, not_not] at huS
  have hUopen : IsOpen (pathComponentIn S u) := h.pathComponentIn u
  have huU : u ∈ pathComponentIn S u := mem_pathComponentIn_self huS
  obtain ⟨z, hzU, hzT⟩ := mem_closure_iff_nhds.1 huc _ (hUopen.mem_nhds huU)
  exact hui ((pathComponentIn_congr hzU).symm.trans (pathComponentIn_congr hzT) ▸ huU)

lemma IsPathConnected.exists_part_pathComponentPartition (h : T ⊆ S) (hT : IsPathConnected T) :
    ∃ U ∈ PathComponentPartition S, T ⊆ U := by
  obtain ⟨x, hx⟩ := hT.nonempty
  use (PathComponentPartition S).partOf x, ?_, fun y hyT ↦ ?_
  · exact (PathComponentPartition S).partOf_mem <| by simp [h hx]
  simp only [pathComponentPartition_partOf, pathComponentIn, mem_setOf_eq]
  exact hT.joinedIn _ hx _ hyT |>.mono h

structure AdjRegion (S T₁ T₂ : Set α) : Prop where
  hT₁ : T₁ ∈ PathComponentPartition S
  hT₂ : T₂ ∈ PathComponentPartition S
  h : (frontier T₁) ∩ (frontier T₂) |>.Nonempty

end PathComponentPartition
