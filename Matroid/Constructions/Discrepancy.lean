import Matroid.Constructions.Quotient

open Set

namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {I X Y B B' : Set α} {e f : α}


lemma Quotient.truncate (h : M₂ ≤q M₁) : M₂.truncate ≤q M₁.truncate := by
  refine quotient_of_forall_closure_subset_closure h.ground_eq.symm fun X (hXE : X ⊆ M₁.E) ↦ ?_
  obtain rfl | hssu := hXE.eq_or_ssubset
  · rw [← truncate_ground_eq, closure_ground, truncate_ground_eq, ← h.ground_eq,
      ← M₂.truncate_ground_eq, closure_ground]
  by_cases hX : M₁.truncate.Spanning X
  · suffices hsp : M₂.truncate.Spanning X
    · rw [hsp.closure_eq, truncate_ground_eq, h.ground_eq, ← truncate_ground_eq]
      apply closure_subset_ground
    rw [truncate_spanning_iff_of_ssubset (hssu.trans_eq h.ground_eq.symm)]
    rw [truncate_spanning_iff_of_ssubset hssu] at hX
    obtain ⟨e, ⟨heE, heX⟩, hS⟩ := hX
    exact ⟨e, ⟨h.ground_eq.symm.subset heE, heX⟩, h.spanning_of_spanning hS⟩
  rw [M₁.truncate_closure_eq_of_not_spanning hXE hX]
  exact (h.closure_subset_closure X).trans <| M₂.truncate_quotient.closure_subset_closure X

lemma Quotient.encard_diff_le_encard_diff
    {I₀ B₀ : Set α} (h : M₂ ≤q M₁) (hIfin : I.Finite) (hI₀I : M₂.Basis I₀ I)
    (hI : M₁.Indep I) (hB₀ : M₂.Base B₀) (hB : M₁.Base B) (hB₀B : B₀ ⊆ B) :
    (I \ I₀).encard ≤ (B \ B₀).encard := by
  obtain ⟨B', hB', hIB', hB'IB⟩ := hI.exists_base_subset_union_base hB
  obtain ⟨B'', hB'', hI₀B''⟩ := hI₀I.indep.subset_basis_of_subset (hI₀I.subset.trans hIB')
    (hB'.subset_ground.trans_eq h.ground_eq.symm)
  have hB''B' := hB''.subset

  replace hB'' := hB''.base_of_spanning (h.spanning_of_spanning hB'.spanning)

  have hrw1 : B' \ B = I \ B
  · rwa [subset_antisymm_iff, and_iff_left (diff_subset_diff_left hIB'), diff_subset_iff,
      union_diff_self, union_comm]

  have hfin : (B \ B').encard ≠ ⊤
  · rw [hB.encard_diff_comm hB', hrw1, encard_ne_top_iff]
    apply hIfin.diff _

  have hrw2 : B'' ∩ I = I₀
  · exact Eq.symm <| hI₀I.eq_of_subset_indep (hB''.indep.inter_right I)
      (subset_inter hI₀B'' hI₀I.subset) inter_subset_right

  have hrw3 : (B \ B'').encard = (B \ B').encard + (B ∩ (B' \ B'')).encard
  · rw [← diff_inter_self_eq_diff,
      ← diff_union_diff_cancel inter_subset_right (inter_subset_inter_left _ hB''B'),
      encard_union_eq (disjoint_sdiff_left.mono_right diff_subset), diff_inter_self_eq_diff]
    convert rfl using 3
    rw [← inter_diff_assoc, inter_comm, diff_eq_diff_inter_of_subset inter_subset_right]

  have hB''ss' : B'' ⊆ B ∪ I₀
  · rw [← diff_union_inter B'' I, hrw2, union_subset_iff, diff_subset_iff,
      and_iff_left subset_union_right, union_comm, union_assoc, union_comm, union_assoc]
    refine hB''B'.trans (hB'IB.trans subset_union_right)

  have hi2 : I₀ \ B = B'' \ B
  · rwa [subset_antisymm_iff, and_iff_right (diff_subset_diff_left hI₀B''), diff_subset_iff,
      union_diff_self]

  have hcalc1 : (B \ B'').encard = (B \ B₀).encard + (I₀ \ B).encard := by
    calc
      (B \ B'').encard = (B₀ \ B'').encard + ((B \ B₀) \ B'').encard := ?_
      _                = (B'' \ B₀).encard + ((B \ B₀) \ B'').encard := by
        rw [hB''.encard_diff_comm hB₀]
      _                = (B'' \ B₀ ∪ (B \ B₀) \ B'').encard          := ?_
      _                = ((B'' ∪ B) \ B₀).encard := ?_
    · rw [← encard_union_eq (disjoint_sdiff_right.mono diff_subset diff_subset),
        ← union_diff_distrib, union_diff_cancel hB₀B]
    · rw [encard_union_eq <| disjoint_sdiff_right.mono_left diff_subset]
    · rw [diff_diff_comm, ← union_diff_distrib, union_diff_self]
    · rw [union_comm, ← union_diff_self, union_diff_distrib,
        diff_diff, union_eq_self_of_subset_right hB₀B,
        encard_union_eq (disjoint_sdiff_right.mono_left diff_subset), ← hi2]

  apply_fun (· + ((I \ I₀) \ B).encard) at hcalc1
  rw [add_assoc, ← encard_union_eq (disjoint_sdiff_right.mono diff_subset diff_subset),
    ← union_diff_distrib, union_diff_cancel hI₀I.subset, ← hrw1,
    hB'.encard_diff_comm hB, hrw3, add_assoc, add_comm, WithTop.add_right_cancel_iff hfin] at hcalc1

  rw [← hcalc1, ← encard_diff_add_encard_inter (t := B), add_comm, inter_comm, ← hrw2,
    diff_inter_self_eq_diff]
  refine add_le_add_right (encard_le_card ?_) _
  exact inter_subset_inter_right _ (diff_subset_diff_left hIB')

lemma Quotient.eq_of_base_indep' [Finitary M₂] (hQ : M₂ ≤q M₁) {B : Set α} (hB₁ : M₁.Base B)
    (hB₂ : M₂.Indep B) : M₂ = M₁ := by
  replace hB₂ := show M₂.Base B from
    hB₂.base_of_maximal fun J hJ hBJ ↦ hB₁.eq_of_subset_indep (hQ.weakLE.indep_of_indep hJ) hBJ
  refine ext_circuit_not_indep hQ.ground_eq (fun C hC hCi ↦ ?_)
    (fun C hC ↦ ((hQ.cyclic_of_circuit hC).dep_of_nonempty hC.nonempty).not_indep)

  obtain ⟨e, he⟩ := hC.nonempty
  simpa [he] using
    hQ.encard_diff_le_encard_diff hC.finite (hC.diff_singleton_basis he) hCi hB₂ hB₁ rfl.subset

def Quotient.exists_basis_subset_pair (hQ : M₂ ≤q M₁) (X : Set α) :
    ∃ Is : Set α × Set α, Is.2 ⊆ Is.1 ∧ M₁.Basis' Is.1 X ∧ M₂.Basis' Is.2 X := by
  obtain ⟨I, hI⟩ := M₂.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := (hQ.weakLE.indep_of_indep hI.indep).subset_basis'_of_subset hI.subset
  exact ⟨⟨J,I⟩, hIJ, hJ, hI⟩

noncomputable def Quotient.discrepancy (hQ : M₂ ≤q M₁) (X : Set α) :=
  ((hQ.exists_basis_subset_pair X).choose.1 \ (hQ.exists_basis_subset_pair X).choose.2).encard

lemma Quotient.exists_finite_witness {J₀ J : Set α} [M₂.Finitary] (hQ : M₂ ≤q M₁)
    (hJ₀X : M₂.Basis J₀ X) (hJX : M₁.Basis J X) (hss : J₀ ⊆ J) (hfin : (J \ J₀).Finite) :
    ∃ I₀ I, I.Finite ∧ M₁.Indep I ∧ M₂.Basis I₀ I ∧ I ⊆ X ∧ I \ I₀ = J \ J₀ := by
  have hJE' : J ⊆ M₂.E := hJX.indep.subset_ground.trans_eq hQ.ground_eq.symm
  have hcl := M₂.exists_subset_finite_closure_of_subset_closure hfin (Y := J₀)
  rw [hJ₀X.closure_eq_closure] at hcl
  obtain ⟨I₀, hI₀J₀, hI₀fin, hI₀i, hI₀ss⟩ :=
    hcl (M₂.subset_closure_of_subset' (diff_subset.trans hJX.subset) (diff_subset.trans hJE'))

  refine ⟨I₀, I₀ ∪ (J \ J₀), hI₀fin.union hfin,
    hJX.indep.subset (union_subset (hI₀J₀.trans hss) diff_subset),
      hI₀i.basis_of_subset_of_subset_closure subset_union_left (union_subset ?_ hI₀ss),
      union_subset (hI₀J₀.trans hJ₀X.subset) (diff_subset.trans hJX.subset), ?_⟩
  · exact M₂.subset_closure I₀ hI₀i.subset_ground
  simp only [union_diff_left, sdiff_eq_left]
  exact disjoint_sdiff_left.mono_right hI₀J₀

lemma Quotient.encard_diff_eq_encard_diff_of_bases [M₂.Finitary] {B₁ B₂ B₁' B₂' : Set α}
    (hQ : M₂ ≤q M₁) (hB₂ : M₂.Base B₂) (hB₂' : M₂.Base B₂') (hB₁ : M₁.Base B₁) (hB₁' : M₁.Base B₁')
    (hss : B₂ ⊆ B₁) (hss' : B₂' ⊆ B₁') : (B₁ \ B₂).encard = (B₁' \ B₂').encard := by
  wlog hle : (B₁ \ B₂).encard ≤ (B₁' \ B₂').encard with h
  · rw [not_le] at hle
    rw [h hQ hB₂' hB₂ hB₁' hB₁ hss' hss hle.le]

  refine hle.antisymm ?_
  obtain hinf | hfin := (B₁ \ B₂).finite_or_infinite.symm
  · simp [hinf.encard_eq]

  suffices aux : ∀ (J : Finset α), (J : Set α) ⊆ B₁' \ B₂' → (J.card : ℕ∞) ≤ (B₁ \ B₂).encard
  ·
    obtain hinf' | hfin' := (B₁' \ B₂').finite_or_infinite.symm
    · obtain ⟨D,hD, hDcard⟩ := hinf'.exists_subset_card_eq (hfin.toFinset.card + 1)
      specialize aux D hD
      rw [hDcard, ENat.coe_add, ← encard_coe_eq_coe_finsetCard, Finite.coe_toFinset, Nat.cast_one,
        ENat.add_one_le_iff (by simpa)] at aux
      simp at aux
    simpa [← encard_coe_eq_coe_finsetCard] using aux hfin'.toFinset (by simp)

  intro J hJss
  have hJcl : (J : Set α) ⊆ M₂.closure B₂'
  · rw [hB₂'.closure_eq]
    exact (hJss.trans diff_subset).trans (hB₁'.subset_ground.trans_eq hQ.ground_eq.symm)

  obtain ⟨I₀, I, hIfin, hIi, hI₀I, hIss, hdiff⟩ :=
    hQ.exists_finite_witness (X := B₂' ∪ J) (J₀ := B₂') (J := B₂' ∪ J)
    (hB₂'.indep.basis_of_subset_of_subset_closure subset_union_left
      (union_subset (subset_closure _ _) hJcl))
    (hB₁'.indep.subset (union_subset hss' (hJss.trans diff_subset))).basis_self
    subset_union_left (by simp [J.finite_toSet.diff _])

  rw [union_diff_left, sdiff_eq_left.2 (subset_diff.1 hJss).2] at hdiff
  rw [← encard_coe_eq_coe_finsetCard, ← hdiff]

  exact hQ.encard_diff_le_encard_diff hIfin hI₀I hIi hB₂ hB₁ hss

lemma Quotient.encard_base_diff_eq_discrepancy [M₂.Finitary] {B₁ B₂ : Set α}
    (hQ : M₂ ≤q M₁) (hB₂ : M₂.Base B₂) (hB₁ : M₁.Base B₁) (hss : B₂ ⊆ B₁) :
    (B₁ \ B₂).encard = hQ.discrepancy M₁.E := by
  set Ps := hQ.exists_basis_subset_pair M₁.E

  refine hQ.encard_diff_eq_encard_diff_of_bases hB₂ ?_ hB₁ ?_ hss Ps.choose_spec.1
  · rw [← basis_ground_iff, ← basis'_iff_basis, hQ.ground_eq]
    exact Ps.choose_spec.2.2

  rw [← basis_ground_iff, ← basis'_iff_basis]
  exact Ps.choose_spec.2.1
