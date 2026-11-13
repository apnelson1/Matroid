module

public import Matroid.MiniTauCeti.JCT.Geometry.PrimitiveLinkReplacement
public import Matroid.MiniTauCeti.JCT.Geometry.ThetaRegions
public import Matroid.MiniTauCeti.JCT.Topology.Crossing

public section

open Set Topology Function

namespace K33

attribute [local instance] Complex.finrank_real_complex_fact

private lemma polygonal_obstruction (v : Fin 3 ⊕ Fin 3 → ℂ)
    (L : Fin 3 × Fin 3 → Set ℂ) (hv : Injective v)
    (hL : ∀ e, IsPrimitiveLink (L e) (v (.inl e.1)) (v (.inr e.2)))
    (hpoly : ∀ e, IsSegmentFigure (L e))
    (hLV : ∀ e, L e ∩ range v ⊆ {v (.inl e.1), v (.inr e.2)})
    (hLL : Pairwise fun e f ↦ L e ∩ L f ⊆ range v) : False := by
  have hmem (x : Fin 3 ⊕ Fin 3) (e : Fin 3 × Fin 3) :
      v x ∈ L e ↔ x = .inl e.1 ∨ x = .inr e.2 := by
    constructor
    · intro hx
      simpa only [mem_insert_iff, mem_singleton_iff, hv.eq_iff] using
        hLV e ⟨hx, mem_range_self x⟩
    · rintro (rfl | rfl)
      · exact (hL e).left_mem
      · exact (hL e).right_mem
  have hinter {e f : Fin 3 × Fin 3} (hef : e ≠ f) :
      L e ∩ L f ⊆ {v (.inl e.1), v (.inr e.2)} :=
    fun _ hz ↦ hLV e ⟨hz.1, hLL hef hz⟩
  let A : Fin 3 → Set ℂ := fun j ↦ L (0, j) ∪ L (1, j)
  have hA (j) : IsPrimitiveLink (A j) (v (.inl 0)) (v (.inl 1)) := by
    apply (hL (0, j)).union (hL (1, j)).symm
      (hv.ne (by simp)) (hv.ne (by simp))
    intro z hz
    rcases hinter (e := (0, j)) (f := (1, j)) (by simp) hz with rfl | h
    · simpa [hmem] using hz.2
    · exact h
  have hmeet : Pairwise fun i j ↦ A i ∩ A j = {v (.inl 0), v (.inl 1)} := by
    intro i j hij
    apply Subset.antisymm
    · rintro z ⟨hi | hi, hj | hj⟩
      all_goals
        rcases hinter (by simp [hij]) ⟨hi, hj⟩ with rfl | rfl
        · simp
        · simp [hmem, hij] at hj
    · rintro z (rfl | rfl)
      · exact ⟨(hA i).left_mem, (hA j).left_mem⟩
      · exact ⟨(hA i).right_mem, (hA j).right_mem⟩
  obtain ⟨W, hWopen, _, _, hcover, hfront⟩ := IsPrimitiveLink.regions A
    (hv.ne (by decide)) hA (fun j ↦ (hpoly (0, j)).union (hpoly (1, j))) hmeet
  have hp : v (.inl 2) ∈ (⋃ j, A j)ᶜ := by
    simp [A, hmem]
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
  have havoid : Disjoint (L (2, i) \ {v (.inl 2), v (.inr i)}) (⋃ j, A j) := by
    apply disjoint_left.mpr
    rintro z ⟨hz, hzi⟩ hzA
    obtain ⟨j, hj | hj⟩ := mem_iUnion.mp hzA
    all_goals exact hzi (hinter (by simp) ⟨hz, hj⟩)
  have hclosure : L (2, i) ⊆ closure (W i) := by
    have hd : Disjoint (L (2, i) \ {v (.inl 2), v (.inr i)}) (frontier (W i)) := by
      apply havoid.mono_right
      rw [hfront]
      exact iUnion₂_subset fun j _ ↦ subset_iUnion A j
    have hpfront : v (.inl 2) ∉ frontier (W i) := by
      rw [(hWopen i).frontier_eq]
      exact fun h ↦ h.2 hi
    have hconn := (hL (2, i)).isConnected_diff_endpoints.isPreconnected
    have hsub := (hconn.subset_interior_iff_of_mem_closure hd
        ((hL (2, i)).subset_closure_diff_endpoints (hL (2, i)).left_mem) hpfront).mpr hi
    exact (hL (2, i)).subset_closure_diff_endpoints.trans
      (closure_mono (hsub.trans interior_subset))
  have hqA : v (.inr i) ∈ ⋃ j, A j :=
    mem_iUnion.mpr ⟨i, Or.inl (hL (0, i)).right_mem⟩
  have hqW : v (.inr i) ∉ W i := fun h ↦
    (hcover ▸ mem_iUnion.mpr ⟨i, h⟩) hqA
  have hqfront : v (.inr i) ∈ frontier (W i) := by
    rw [(hWopen i).frontier_eq]
    exact ⟨hclosure (hL (2, i)).right_mem, hqW⟩
  rw [hfront] at hqfront
  simp [A, hmem, eq_comm] at hqfront

/-- Six distinct plane vertices cannot support nine links with the incidences of `K₃,₃`. -/
theorem obstruction (v : Fin 3 ⊕ Fin 3 → ℂ) (L : Fin 3 × Fin 3 → Set ℂ)
    (hv : Injective v)
    (hL : ∀ e, IsPrimitiveLink (L e) (v (.inl e.1)) (v (.inr e.2)))
    (hLV : ∀ e, L e ∩ range v ⊆ {v (.inl e.1), v (.inr e.2)})
    (hLL : Pairwise fun e f ↦ L e ∩ L f ⊆ range v) : False := by
  let : Finite (range v) := (finite_range v).to_subtype
  obtain ⟨M, hM, hpoly, hMV, hMM, _⟩ := exists_polygonal_primitiveLink_family
    (a := fun e : Fin 3 × Fin 3 ↦ ⟨v (.inl e.1), mem_range_self _⟩)
    (b := fun e : Fin 3 × Fin 3 ↦ ⟨v (.inr e.2), mem_range_self _⟩)
    hL hLV hLL (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ subset_univ _)
  exact polygonal_obstruction v M hv hM hpoly (fun e ↦ (hMV e).subset) hMM

end K33
