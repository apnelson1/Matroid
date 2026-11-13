module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Constructions

@[expose] public section

open Set Topology Set.Notation

/-- Adjoining a closed set along finitely many points preserves relative total separation. -/
lemma isTotallySeparated_preimage_union_of_finite_inter
    {X : Type*} [TopologicalSpace X] [T2Space X] {S K Z : Set X}
    (hS : IsClosed S) (hK : IsClosed K) (hSK : (S ∩ K).Finite) (hZ : Z ⊆ S)
    (hsep : IsTotallySeparated (S ↓∩ Z)) :
    IsTotallySeparated ((S ∪ K) ↓∩ Z) := by
  intro x hx y hy hxy
  let x' : S := ⟨x.1, hZ hx⟩
  let y' : S := ⟨y.1, hZ hy⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hcover, hdisj⟩ :=
    hsep (x := x') (y := y') hx hy (fun h ↦ hxy (Subtype.ext (congrArg (fun z : S ↦ z.1) h)))
  let A := Subtype.val '' U ∩ K
  let B := Subtype.val '' V ∩ K
  have hA : A.Finite := hSK.subset (by rintro z ⟨⟨w, hw, rfl⟩, hz⟩; exact ⟨w.2, hz⟩)
  have hB : B.Finite := hSK.subset (by rintro z ⟨⟨w, hw, rfl⟩, hz⟩; exact ⟨w.2, hz⟩)
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    rintro z ⟨⟨a, ha, rfl⟩, -⟩ ⟨⟨b, hb, hab⟩, -⟩
    exact hdisj.notMem_of_mem_left ha (Subtype.ext hab ▸ hb)
  obtain ⟨O, P, hO, hP, hAO, hBP, hOP⟩ := SeparatedNhds.of_finite hA hB hAB
  let U' : Set X := (Subtype.val '' Uᶜ)ᶜ ∩ (K \ O)ᶜ
  let V' : Set X := (Subtype.val '' Vᶜ)ᶜ ∩ (K \ P)ᶜ
  have hU' : IsOpen U' :=
    (hS.isClosedMap_subtype_val _ hU.isClosed_compl).isOpen_compl.inter
      (hK.sdiff hO).isOpen_compl
  have hV' : IsOpen V' :=
    (hS.isClosedMap_subtype_val _ hV.isClosed_compl).isOpen_compl.inter
      (hK.sdiff hP).isOpen_compl
  have memU {z : S} (hz : z ∈ U) : z.1 ∈ U' := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact hw (Subtype.ext hwz ▸ hz)
    · rintro ⟨hzK, hzO⟩
      exact hzO (hAO ⟨⟨z, hz, rfl⟩, hzK⟩)
  have memV {z : S} (hz : z ∈ V) : z.1 ∈ V' := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact hw (Subtype.ext hwz ▸ hz)
    · rintro ⟨hzK, hzP⟩
      exact hzP (hBP ⟨⟨z, hz, rfl⟩, hzK⟩)
  refine ⟨Subtype.val ⁻¹' U', Subtype.val ⁻¹' V', hU'.preimage continuous_subtype_val,
    hV'.preimage continuous_subtype_val, memU hxU, memV hyV, ?_, ?_⟩
  · intro z hz
    obtain hzU | hzV := hcover (show (⟨z.1, hZ hz⟩ : S) ∈ S ↓∩ Z from hz)
    · exact Or.inl (memU hzU)
    · exact Or.inr (memV hzV)
  · rw [disjoint_left]
    intro z hzU hzV
    obtain hzS | hzK := z.2
    · have hu : (⟨z.1, hzS⟩ : S) ∈ U := by
        by_contra h
        exact hzU.1 ⟨⟨z.1, hzS⟩, h, rfl⟩
      have hv : (⟨z.1, hzS⟩ : S) ∈ V := by
        by_contra h
        exact hzV.1 ⟨⟨z.1, hzS⟩, h, rfl⟩
      exact hdisj.notMem_of_mem_left hu hv
    · exact hOP.notMem_of_mem_left (not_not.mp fun h ↦ hzU.2 ⟨hzK, h⟩)
        (not_not.mp fun h ↦ hzV.2 ⟨hzK, h⟩)

/-- In a totally separated set, a point can be separated from any compact subset avoiding it by
disjoint open sets covering the whole set. -/
lemma IsTotallySeparated.exists_separation_of_isCompact {Y : Type*} [TopologicalSpace Y]
    {V F : Set Y} (hV : IsTotallySeparated V) (hF : IsCompact F) (hFV : F ⊆ V) {p : Y}
    (hpV : p ∈ V) (hpF : p ∉ F) :
    ∃ U W : Set Y, IsOpen U ∧ IsOpen W ∧ p ∈ U ∧ F ⊆ W ∧ V ⊆ U ∪ W ∧ Disjoint U W := by
  apply hF.induction_on
    (p := fun A ↦ ∃ U W : Set Y, IsOpen U ∧ IsOpen W ∧ p ∈ U ∧
      A ⊆ W ∧ V ⊆ U ∪ W ∧ Disjoint U W)
  · exact ⟨univ, ∅, isOpen_univ, isOpen_empty, trivial, empty_subset _, by simp,
      disjoint_empty _⟩
  · rintro A B hAB ⟨U, W, hU, hW, hpU, hBW, hcover, hd⟩
    exact ⟨U, W, hU, hW, hpU, hAB.trans hBW, hcover, hd⟩
  · rintro A B ⟨U, W, hU, hW, hpU, hAW, hcover, hd⟩
      ⟨U', W', hU', hW', hpU', hBW', hcover', hd'⟩
    refine ⟨U ∩ U', W ∪ W', hU.inter hU', hW.union hW', ⟨hpU, hpU'⟩,
      union_subset (hAW.trans subset_union_left) (hBW'.trans subset_union_right), ?_, ?_⟩
    · intro x hx
      rcases hcover hx with hu | hw
      · exact (hcover' hx).elim (fun hu' ↦ Or.inl ⟨hu, hu'⟩) (fun hw' ↦ Or.inr (Or.inr hw'))
      exact Or.inr (Or.inl hw)
    exact disjoint_left.mpr fun _ hu hw ↦
      hw.elim (hd.notMem_of_mem_left hu.1) (hd'.notMem_of_mem_left hu.2)
  intro q hq
  obtain ⟨U, W, hU, hW, hpU, hqW, hcover, hd⟩ :=
    hV hpV (hFV hq) (fun h ↦ hpF (h ▸ hq))
  exact ⟨W, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hqW), U, W, hU, hW, hpU, Subset.rfl,
    hcover, hd⟩
