
import Matroid.Flat

variable {α : Type*} {M : Matroid α} {E I H B X : Set α} {e f : α}

namespace Matroid

open Set

section Relax

lemma Hyperplane.exchange_base_of_circuit (hH : M.Hyperplane H) (hHc : M.Circuit H) (he : e ∈ H)
    (hf : f ∈ M.E \ H) : M.Base (insert f (H \ {e})) := by
  have hcl := hH.cl_insert_eq hf.2 hf.1
  rw [← cl_insert_cl_eq_cl_insert, ← hHc.cl_diff_singleton_eq_cl e, cl_insert_cl_eq_cl_insert,
    ← spanning_iff_cl (insert_subset hf.1 (diff_subset.trans hH.subset_ground))] at hcl
  refine' hcl.base_of_indep _
  rw [← (hHc.diff_singleton_indep he).not_mem_cl_iff_of_not_mem (fun hf' ↦ hf.2 hf'.1),
    hHc.cl_diff_singleton_eq_cl e, hH.flat.cl]
  exact hf.2

lemma Base.exists_exchange_of_circuit_of_hyperplane (hB : M.Base B) (hH : M.Hyperplane H)
    (hHc : M.Circuit H) (he : e ∈ B) :
    ∃ f, f ∈ H \ B ∧ (M.Base (insert f (B \ {e})) ∨ insert f (B \ {e}) = H) := by
  by_contra! h

  have h1 : H \ {e} ⊆ M.cl (B \ {e}) := by
    refine fun x hx ↦ by_contra fun hcl ↦ ?_
    have hxB : x ∉ B := by
      exact fun hxB' ↦ hcl (M.mem_cl_of_mem' ⟨hxB', hx.2⟩ (hH.subset_ground hx.1))

    refine (h x ⟨hx.1, hxB⟩).1 (hB.exchange_base_of_indep hxB ?_)
    rwa [← (hB.indep.diff {e}).not_mem_cl_iff_of_not_mem (not_mem_subset diff_subset hxB)
      (hH.subset_ground hx.1)]

  rw [← cl_subset_cl_iff_subset_cl (diff_subset.trans hH.subset_ground),
    hHc.cl_diff_singleton_eq_cl, hH.flat.cl] at h1
  obtain hBH := hH.eq_of_subset (hB.hyperplane_of_cl_diff_singleton he) h1

  have hb : M.Basis (B \ {e}) H := by
    exact (hB.indep.diff _).basis_of_subset_of_subset_cl
      ((M.subset_cl (B \ {e}) (diff_subset.trans hB.subset_ground)).trans hBH.symm.subset) h1
  obtain ⟨f, ⟨hfH, hfBe⟩, hfB⟩ := hHc.basis_iff_insert_eq.1 hb
  refine (h _ ⟨hfH, fun hfB ↦ hfBe ⟨hfB, fun (hfe : f = e) ↦ ?_⟩⟩).2 hfB.symm
  apply hB.indep.not_mem_cl_diff_of_mem he
  rwa [← hBH, ← hfe]

lemma antichain_of_circuit_hyperplane (M : Matroid α) :
    IsAntichain (· ⊆ ·) ({ B | M.Base B } ∪ { H | M.Circuit H ∧ M.Hyperplane H }) := by
  rintro X ((hX : M.Base X) | ⟨hXc, -⟩) Y ((hY : M.Base Y) | ⟨hYc, hYh⟩) hne hss
  · exact hne (hX.eq_of_subset_base hY hss)
  · exact hYh.not_spanning (hX.spanning.superset hss)
  · exact (hY.indep.subset hss).not_dep hXc.dep
  exact hne (hXc.eq_of_subset_circuit hYc hss)

/-- Relax a collection `Hs` of circuit-hyperplanes of a matroid `M` to obtain a new matroid whose
  bases are the old bases together with the sets in `Hs`.
  (If `Hs` contains sets that are not circuit hyperplanes, they do not become bases.) -/
def relaxSet (M : Matroid α) (Hs : Set (Set α)) : Matroid α :=
  Matroid.ofBase M.E
    ( fun B ↦ M.Base B ∨ (B ∈ Hs ∧ M.Circuit B ∧ M.Hyperplane B) )
    ( M.exists_base.imp fun _ ↦ Or.inl )
    ( by
        rintro B B' (hB | ⟨-, hBc, hBcc⟩) hB' e he
        · obtain (hB' | ⟨hB'h, hB'c, hB'cc⟩) := hB'
          · obtain ⟨f, hf⟩:= hB.exchange hB' he
            exact ⟨f, hf.1, Or.inl hf.2⟩
          · obtain ⟨f, hf, hf'⟩ := hB.exists_exchange_of_circuit_of_hyperplane hB'cc hB'c he.1
            refine ⟨f, hf, hf'.elim Or.inl (Or.inr ∘ ?_)⟩
            rintro rfl
            exact ⟨hB'h, hB'c, hB'cc⟩
        · have hB'B : (B' \ B).Nonempty := by
            rw [nonempty_iff_ne_empty, ne_eq, diff_eq_empty]; intro hB'B
            obtain (hB' | hB') := hB'
            · exact hBcc.not_spanning (hB'.spanning.superset hB'B)
            rw [hB'.2.1.eq_of_subset_circuit hBc hB'B, diff_self] at he
            exact not_mem_empty e he
          obtain ⟨f, hf⟩ := hB'B
          refine ⟨f, hf, Or.inl (hBcc.exchange_base_of_circuit hBc he.1 ⟨?_, hf.2⟩)⟩
          exact hB'.elim (fun h ↦ h.subset_ground hf.1) (fun h ↦ h.2.1.subset_ground hf.1) )

    ( by
        intro X hXE I ⟨B, hB, hIB⟩ hIX

        obtain (⟨Z, hZ, hIZ, hZX⟩ | hsmall) :=
          em (∃ Z, (M.Base Z ∨ Z ∈ Hs ∧ M.Circuit Z ∧ M.Hyperplane Z) ∧ I ⊆ Z ∧ Z ⊆ X)
        · refine ⟨Z, ⟨⟨Z, hZ, rfl.subset⟩, hIZ, hZX⟩,
            fun J ⟨⟨BJ, (hBJ : _ ∨ _), hJBJ⟩, _, _⟩ (hZJ : Z ⊆ J) ↦ ?_⟩
          rwa [M.antichain_of_circuit_hyperplane.eq (hZ.elim Or.inl (Or.inr ∘ And.right))
            (hBJ.elim Or.inl (Or.inr ∘ And.right)) (hZJ.trans hJBJ)]

        have hI : M.Indep I := by
          refine hB.elim (fun h ↦ h.indep.subset hIB)
            (fun h ↦ h.2.1.ssubset_indep (hIB.ssubset_of_ne ?_))
          rintro rfl
          exact hsmall ⟨I, Or.inr h, hIB, hIX⟩

        obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIX
        obtain ⟨BJ, hBJ, hJBJ⟩ := hJ.indep.exists_base_superset
        refine ⟨J, ⟨⟨BJ, Or.inl hBJ, hJBJ⟩,hIJ,hJ.subset⟩,
          fun K ⟨⟨BK, hBK, hKBK⟩, hIK, hKX⟩ (hJK : J ⊆ K) ↦ (?_ : K ⊆ J)⟩
        rw [hJ.eq_of_subset_indep _ hJK hKX]
        obtain (hBK | ⟨hBK,hBKc,hBKh⟩) := hBK
        · exact hBK.indep.subset hKBK
        refine hBKc.ssubset_indep (hKBK.ssubset_of_ne ?_)
        rintro rfl
        exact hsmall ⟨K, Or.inr ⟨hBK, hBKc, hBKh⟩, hIK, hKX⟩ )
    ( by rintro B (hB | ⟨-, hB, -⟩) <;> aesop_mat )

lemma relaxSet_base_iff {Hs : Set (Set α)} (h : ∀ H ∈ Hs, M.Circuit H ∧ M.Hyperplane H) :
    (M.relaxSet Hs).Base B ↔ M.Base B ∨ B ∈ Hs := by
  simp only [relaxSet, Matroid.ofBase]
  exact ⟨fun h' ↦ h'.elim Or.inl (Or.inr ∘ And.left),
    fun h' ↦ h'.elim Or.inl (fun hBs ↦ Or.inr ⟨hBs, h B hBs⟩)⟩

lemma relaxSet_indep_iff {Hs : Set (Set α)} (h : ∀ H ∈ Hs, M.Circuit H ∧ M.Hyperplane H) :
    (M.relaxSet Hs).Indep I ↔ M.Indep I ∨ I ∈ Hs := by
  simp_rw [indep_iff, relaxSet_base_iff h]
  refine' ⟨fun ⟨B, hB, hIB⟩ ↦ hB.elim (fun hB' ↦ Or.inl ⟨B, hB', hIB⟩) (fun hB' ↦ _),
    fun h ↦ h.elim (fun ⟨B, hB, hIB⟩ ↦ ⟨B, Or.inl hB, hIB⟩) fun hI ↦ ⟨I, Or.inr hI, rfl.subset⟩⟩
  refine hIB.eq_or_ssubset.elim (fun h ↦ Or.inr (by rwa [h])) (fun hss ↦ Or.inl ?_)
  apply Indep.exists_base_superset (hB.elim (fun h' ↦ h'.indep.subset hIB)
    (fun h' ↦ (h _ h').1.ssubset_indep hss))

/-- Change a single nonbase `H` of `M` to a base, provided `H` is a circuit-hyperplane -/
def relax (M : Matroid α) (H : Set α) : Matroid α := M.relaxSet ({H} : Set (Set α))

lemma relax_base_iff (hH : M.Hyperplane X) (hC : M.Circuit X) :
    (M.relax X).Base B ↔ (M.Base B ∨ B = X) := by
  rw [relax, relaxSet_base_iff, mem_singleton_iff]; simp [hH, hC]

lemma relax_indep_iff (hH : M.Hyperplane X) (hC : M.Circuit X) :
    (M.relax X).Indep I ↔ (M.Indep I ∨ I = X) := by
  rw [relax, relaxSet_indep_iff, mem_singleton_iff]; simp [hH, hC]



end Relax
