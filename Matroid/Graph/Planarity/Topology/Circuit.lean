import Matroid.Graph.Planarity.Topology.Circle

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a b c u v w x y z : α}
  {C X Y : Set α}

open Set Function TopologicalSpace Topology Metric Nat unitInterval

def IsCircuit {α} [TopologicalSpace α] (C : Set α) : Prop :=
  ∃ f : Circle → α, Topology.IsEmbedding f ∧ range f = C

lemma IsCircuit.isPathConnected (hC : IsCircuit C) : IsPathConnected C := by
  obtain ⟨f, hf, rfl⟩ := hC
  exact isPathConnected_range hf.continuous

lemma circle_isCircuit : IsCircuit (univ : Set Circle) := ⟨id, IsEmbedding.id, by simp⟩

-- lemma isCircuit_of_exists_paths (P : Path x x) (hP : InjOn P (Ioc 0 1)) :
--     IsCircuit (range P) := by
--   let f :=(AddCircle.homeoIccQuot 1 0).symm.trans (AddCircle.homeomorphCircle (zero_ne_one' ℝ).symm)
--   have hII : (I → I → Prop) = ((Icc 0 (0 + 1 : ℝ)) → (Icc 0 (0 + 1 : ℝ)) → Prop) := by simp
--   let f' := Quot.lift (α := I) (r := by convert AddCircle.EndpointIdent (1 : ℝ) 0) P
--     (fun i j hij ↦ ?_)

--   sorry

lemma IsCircuit.twoConnected (hC : IsCircuit C) : ∀ x, IsPathConnected (C \ {x}) := by
  rintro x
  obtain ⟨f, hf, rfl⟩ := hC
  by_cases hx : x ∈ range f
  · obtain ⟨i, rfl⟩ := hx
    convert Circle.singleton_compl_isPathConnected i |>.image hf.continuous
    rw [image_compl_eq_range_diff_image hf.injective, image_singleton]
  simp only [hx, not_false_eq_true, diff_singleton_eq_self]
  exact isPathConnected_range hf.continuous

def IsCircuit.isEmbedding (hC : IsCircuit C) (f : α → β) (hf : Topology.IsEmbedding f) :
    IsCircuit (f '' C) := by
  obtain ⟨f', hf', rfl⟩ := hC
  exact ⟨f ∘ f', hf.comp hf', by simp [range_comp]⟩

-- lemma not_isCircuit_real (S : Set ℝ) : ¬ IsCircuit S := by
--   sorry
