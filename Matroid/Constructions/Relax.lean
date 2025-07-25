
import Matroid.Flat.Hyperplane

variable {α : Type*} {M : Matroid α} {E I H B X : Set α} {e f : α}

namespace Matroid

open Set

section Relax

lemma IsHyperplane.exchange_isBase_of_isCircuit (hH : M.IsHyperplane H) (hHc : M.IsCircuit H)
    (he : e ∈ H) (hf : f ∈ M.E \ H) : M.IsBase (insert f (H \ {e})) := by
  have hclosure := hH.closure_insert_eq hf.2 hf.1
  rw [← closure_insert_closure_eq_closure_insert, ← hHc.closure_diff_singleton_eq e,
    closure_insert_closure_eq_closure_insert,
    ← spanning_iff_closure_eq (insert_subset hf.1 (diff_subset.trans hH.subset_ground))] at hclosure
  apply hclosure.isBase_of_indep
  rw [← (hHc.diff_singleton_indep he).notMem_closure_iff_of_notMem (fun hf' ↦ hf.2 hf'.1),
    hHc.closure_diff_singleton_eq e, hH.isFlat.closure]
  exact hf.2

lemma IsBase.exists_exchange_of_isCircuit_of_isHyperplane (hB : M.IsBase B) (hH : M.IsHyperplane H)
    (hHc : M.IsCircuit H) (he : e ∈ B) :
    ∃ f, f ∈ H \ B ∧ (M.IsBase (insert f (B \ {e})) ∨ insert f (B \ {e}) = H) := by
  by_contra! h

  have h1 : H \ {e} ⊆ M.closure (B \ {e}) := by
    refine fun x hx ↦ by_contra fun hclosure ↦ ?_
    have hxB : x ∉ B := by
      exact fun hxB' ↦ hclosure (M.mem_closure_of_mem' ⟨hxB', hx.2⟩ (hH.subset_ground hx.1))

    refine (h x ⟨hx.1, hxB⟩).1 (hB.exchange_isBase_of_indep hxB ?_)
    rwa [← (hB.indep.diff {e}).notMem_closure_iff_of_notMem (notMem_subset diff_subset hxB)
      (hH.subset_ground hx.1)]

  rw [← closure_subset_closure_iff_subset_closure (diff_subset.trans hH.subset_ground),
    hHc.closure_diff_singleton_eq, hH.isFlat.closure] at h1
  obtain hBH := hH.eq_of_subset (hB.isHyperplane_of_closure_diff_singleton he) h1

  have hb : M.IsBasis (B \ {e}) H := by
    exact (hB.indep.diff _).isBasis_of_subset_of_subset_closure
      ((M.subset_closure (B \ {e}) (diff_subset.trans hB.subset_ground)).trans hBH.symm.subset) h1
  obtain ⟨f, ⟨hfH, hfBe⟩, hfB⟩ := hHc.isBasis_iff_insert_eq.1 hb
  refine (h _ ⟨hfH, fun hfB ↦ hfBe ⟨hfB, fun (hfe : f = e) ↦ ?_⟩⟩).2 hfB.symm
  apply hB.indep.notMem_closure_diff_of_mem he
  rwa [← hBH, ← hfe]

lemma antichain_of_isCircuit_isHyperplane (M : Matroid α) :
    IsAntichain (· ⊆ ·) ({ B | M.IsBase B } ∪ { H | M.IsCircuit H ∧ M.IsHyperplane H }) := by
  rintro X ((hX : M.IsBase X) | ⟨hXc, -⟩) Y ((hY : M.IsBase Y) | ⟨hYc, hYh⟩) hne hss
  · exact hne (hX.eq_of_subset_isBase hY hss)
  · exact hYh.not_spanning (hX.spanning.superset hss)
  · exact (hY.indep.subset hss).not_dep hXc.dep
  exact hne (hXc.eq_of_subset_isCircuit hYc hss)

/-- Relax a collection `Hs` of circuit-hyperplanes of a matroid `M` to obtain a new matroid whose
  bases are the old bases together with the sets in `Hs`.
  (If `Hs` contains sets that are not circuit hyperplanes, they do not become bases.) -/
def relaxSet (M : Matroid α) (Hs : Set (Set α)) : Matroid α :=
  Matroid.ofBase M.E
    (fun B ↦ M.IsBase B ∨ (B ∈ Hs ∧ M.IsCircuit B ∧ M.IsHyperplane B) )
    (M.exists_isBase.imp fun _ ↦ Or.inl )
    (by
        rintro B B' (hB | ⟨-, hBc, hBcc⟩) hB' e he
        · obtain (hB' | ⟨hB'h, hB'c, hB'cc⟩) := hB'
          · obtain ⟨f, hf⟩:= hB.exchange hB' he
            exact ⟨f, hf.1, Or.inl hf.2⟩
          · obtain ⟨f, hf, hf'⟩ := hB.exists_exchange_of_isCircuit_of_isHyperplane hB'cc hB'c he.1
            refine ⟨f, hf, hf'.elim Or.inl (Or.inr ∘ ?_)⟩
            rintro rfl
            exact ⟨hB'h, hB'c, hB'cc⟩
        · have hB'B : (B' \ B).Nonempty := by
            rw [nonempty_iff_ne_empty, ne_eq, diff_eq_empty]; intro hB'B
            obtain (hB' | hB') := hB'
            · exact hBcc.not_spanning (hB'.spanning.superset hB'B)
            rw [hB'.2.1.eq_of_subset_isCircuit hBc hB'B, diff_self] at he
            exact notMem_empty e he
          obtain ⟨f, hf⟩ := hB'B
          refine ⟨f, hf, Or.inl (hBcc.exchange_isBase_of_isCircuit hBc he.1 ⟨?_, hf.2⟩)⟩
          exact hB'.elim (fun h ↦ h.subset_ground hf.1) (fun h ↦ h.2.1.subset_ground hf.1) )

    (by
        intro X hXE I ⟨B, hB, hIB⟩ hIX

        simp_rw [maximal_subset_iff, and_imp, forall_exists_index, and_imp]
        -- Split into cases depending on whether there is a base or circuit-hyperplane between
        -- `I` and `Z`.
        obtain (⟨Z, hZ, hIZ, hZX⟩ | hsmall) :=
          em (∃ Z, (M.IsBase Z ∨ Z ∈ Hs ∧ M.IsCircuit Z ∧ M.IsHyperplane Z) ∧ I ⊆ Z ∧ Z ⊆ X)
        · refine ⟨Z, hIZ, ⟨⟨Z,hZ, rfl.subset⟩, hZX⟩, fun J BJ hBJ hJBJ _ hZJ ↦ ?_⟩
          obtain rfl := M.antichain_of_isCircuit_isHyperplane.eq
            (hZ.elim Or.inl (Or.inr ∘ And.right)) (hBJ.elim .inl (.inr ∘ And.right))
            (hZJ.trans hJBJ)
          exact hZJ.antisymm hJBJ

        -- `I` is independent, since it is a proper subset of a circuit or base.
        have hI : M.Indep I := hB.elim (fun h ↦ h.indep.subset hIB) (fun h ↦ h.2.1.ssubset_indep
          (hIB.ssubset_of_ne fun h_eq ↦ hsmall ⟨I, .inr (h_eq ▸ h), h_eq ▸ hIB, hIX⟩))

        obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIX
        obtain ⟨BJ, hBJ, hJBJ⟩ := hJ.indep.exists_isBase_superset
        refine ⟨J, hIJ, ⟨⟨BJ, .inl hBJ, hJBJ⟩, hJ.subset⟩, fun K BK hBK hKBK hKX hJK ↦ ?_⟩
        by_cases hK : M.Indep K
        · exact hJ.eq_of_subset_indep hK hJK hKX

        refine False.elim <| hsmall ⟨BK, hBK, ?_⟩
        obtain hBK | hBK := hBK
        · exact False.elim <| hK <| hBK.indep.subset hKBK
        obtain rfl := hBK.2.1.eq_of_not_indep_subset hK hKBK
        exact ⟨hIJ.trans hJK, hKX⟩)
    (by rintro B (hB | ⟨-, hB, -⟩) <;> aesop_mat )

lemma relaxSet_isBase_iff {Hs : Set (Set α)} (h : ∀ H ∈ Hs, M.IsCircuit H ∧ M.IsHyperplane H) :
    (M.relaxSet Hs).IsBase B ↔ M.IsBase B ∨ B ∈ Hs := by
  simp only [relaxSet, Matroid.ofBase]
  exact ⟨fun h' ↦ h'.elim Or.inl (Or.inr ∘ And.left),
    fun h' ↦ h'.elim Or.inl (fun hBs ↦ Or.inr ⟨hBs, h B hBs⟩)⟩

lemma relaxSet_indep_iff {Hs : Set (Set α)} (h : ∀ H ∈ Hs, M.IsCircuit H ∧ M.IsHyperplane H) :
    (M.relaxSet Hs).Indep I ↔ M.Indep I ∨ I ∈ Hs := by
  simp_rw [indep_iff, relaxSet_isBase_iff h]
  refine ⟨fun ⟨B, hB, hIB⟩ ↦ hB.elim (fun hB' ↦ Or.inl ⟨B, hB', hIB⟩) (fun hB' ↦ ?_),
    fun h ↦ h.elim (fun ⟨B, hB, hIB⟩ ↦ ⟨B, Or.inl hB, hIB⟩) fun hI ↦ ⟨I, Or.inr hI, rfl.subset⟩⟩
  refine hIB.eq_or_ssubset.elim (fun h ↦ Or.inr (by rwa [h])) (fun hss ↦ Or.inl ?_)
  apply Indep.exists_isBase_superset (hB.elim (fun h' ↦ h'.indep.subset hIB)
    (fun h' ↦ (h _ h').1.ssubset_indep hss))

/-- Change a single nonbase `H` of `M` to a base, provided `H` is a circuit-hyperplane -/
def relax (M : Matroid α) (H : Set α) : Matroid α := M.relaxSet {H}

lemma relax_isBase_iff (hH : M.IsHyperplane X) (hC : M.IsCircuit X) :
    (M.relax X).IsBase B ↔ (M.IsBase B ∨ B = X) := by
  rw [relax, relaxSet_isBase_iff, mem_singleton_iff]; simp [hH, hC]

lemma relax_indep_iff (hH : M.IsHyperplane X) (hC : M.IsCircuit X) :
    (M.relax X).Indep I ↔ (M.Indep I ∨ I = X) := by
  rw [relax, relaxSet_indep_iff, mem_singleton_iff]; simp [hH, hC]

end Relax


section Tighten

structure IsFreeBase (M : Matroid α) (B : Set α) : Prop where
  isBase : M.IsBase B
  fundCircuit_eq_insert : ∀ ⦃e⦄, e ∈ M.E → e ∉ B → M.fundCircuit e B = insert e B

structure IsTightenSet (M : Matroid α) (Bs : Set (Set α)) : Prop where
  isFreeBase_of_mem : ∀ ⦃B⦄, B ∈ Bs → M.IsFreeBase B
  eq_of_eq_exchange : ∀ ⦃B⦄ ⦃e f : α⦄, B ∈ Bs → insert e (B \ {f}) ∈ Bs → e = f

-- def IsTightenSet.matroid (M : Matroid α) {Bs : Set (Set α)} (hBs : M.IsTightenSet Bs) :
--     Matroid α := Matroid.ofBase
--     (E := M.E)
--     (IsBase := fun B ↦ M.IsBase B ∧ B ∉ Bs)
--     (exists_isBase := sorry)
--     (isBase_exchange := sorry)
--     (maximality := sorry)
--     (subset_ground := sorry)

end Tighten
