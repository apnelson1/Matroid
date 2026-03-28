import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
import Mathlib.Topology.UniformSpace.Path -- inefficient import
import Mathlib.Topology.Separation.Connected -- inefficient import
import Mathlib.Topology.LocallyConstant.Basic -- inefficient import
import Matroid.ForMathlib.Partition.Set
import Matroid.Graph.Basic

open Set Function Partition
variable {α : Type*} [TopologicalSpace α] {S T T₁ T₂ : Set α} {u v w : α}

instance : IsTrans α (JoinedIn S) where
  trans _ _ _ := JoinedIn.trans

instance : Std.Symm (JoinedIn S) where
  symm _ _ := JoinedIn.symm

def ComponentPartition (S : Set α) : Partition (Set α) := Partition.ofRel (JoinedIn Sᶜ)

@[simp]
lemma componentPartition_supp (S : Set α) : (ComponentPartition S).supp = Sᶜ := by
  ext v
  simp only [ComponentPartition, ofRel_supp, Relation.mem_domain_iff, mem_compl_iff]
  exact ⟨fun ⟨x, hx⟩ => hx.source_mem, fun hv => ⟨v, JoinedIn.refl hv⟩⟩

@[simp]
lemma componentPartition_partOf (S : Set α) :
    (ComponentPartition S).partOf v = pathComponentIn Sᶜ v := by
  simp [ComponentPartition, partOf, Relation.fiber, pathComponentIn, comm_of]

lemma mem_componentPartition_iff (S T : Set α) :
    T ∈ ComponentPartition S ↔ ∃ v ∈ Sᶜ, pathComponentIn Sᶜ v = T := by
  refine ⟨fun hT => ?_, fun ⟨v, hv, h⟩ => h ▸ componentPartition_partOf S ▸ partOf_mem <| by simpa⟩
  obtain ⟨v, hv⟩ := (ComponentPartition S).nonempty_of_mem hT
  exact ⟨v, componentPartition_supp S ▸ (ComponentPartition S).subset_of_mem hT hv,
    componentPartition_partOf S ▸ (ComponentPartition S).eq_partOf_of_mem hT hv |>.symm⟩

lemma componentPartition_parts (S : Set α) :
    (ComponentPartition S).parts = (pathComponentIn Sᶜ) '' Sᶜ := by
  ext T
  rw [mem_parts, mem_componentPartition_iff, mem_image]

lemma IsClosed.componentPartition_isOpen [LocPathConnectedSpace α] (hT : T ∈ ComponentPartition S)
    (h : IsClosed S) : IsOpen T := by
  obtain ⟨v, hv, rfl⟩ := mem_componentPartition_iff S T |>.mp hT
  exact h.isOpen_compl.pathComponentIn v

lemma frontier_subset_of_mem_componentPartition [LocPathConnectedSpace α]
    (hT : T ∈ ComponentPartition S) (h : IsClosed S) : frontier T ⊆ S := by
  rintro u ⟨huc, hui⟩
  rw [(h.componentPartition_isOpen hT).interior_eq] at hui
  obtain ⟨v, -, rfl⟩ := mem_componentPartition_iff S T |>.mp hT
  by_contra huS
  have hUopen : IsOpen (pathComponentIn Sᶜ u) := h.isOpen_compl.pathComponentIn u
  have huU : u ∈ pathComponentIn Sᶜ u := mem_pathComponentIn_self huS
  obtain ⟨z, hzU, hzT⟩ := mem_closure_iff_nhds.1 huc _ (hUopen.mem_nhds huU)
  exact hui ((pathComponentIn_congr hzU).symm.trans (pathComponentIn_congr hzT) ▸ huU)

structure AdjRegion (S T₁ T₂ : Set α) : Prop where
  hT₁ : T₁ ∈ ComponentPartition S
  hT₂ : T₂ ∈ ComponentPartition S
  h : (frontier T₁) ∩ (frontier T₂) |>.Nonempty
