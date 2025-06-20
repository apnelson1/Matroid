import Matroid.Order.Quotient

open Set

namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {I J I₁ I₂ J₁ J₂ B B' B₁ B₂ B₁' B₂' X Y : Set α}
    {e f : α}

lemma encard_diff_le_encard_diff {I₀ B₀ : Set α} (h : M₁✶ ≤w M₂✶) (hIfin : I.Finite)
    (hI₀I : M₂.IsBasis I₀ I) (hI : M₁.Indep I) (hB₀ : M₂.IsBase B₀) (hB : M₁.IsBase B)
    (hB₀B : B₀ ⊆ B) : (I \ I₀).encard ≤ (B \ B₀).encard := by
  obtain ⟨B', hB', hIB', hB'IB⟩ := hI.exists_isBase_subset_union_isBase hB
  obtain ⟨B'', hB'', hI₀B''⟩ := hI₀I.indep.subset_isBasis_of_subset (hI₀I.subset.trans hIB')
    (hB'.subset_ground.trans_eq h.ground_eq)
  have hB''B' := hB''.subset

  replace hB'' := hB''.isBase_of_spanning (h.spanning_of_spanning_of_dual hB'.spanning)

  have hrw1 : B' \ B = I \ B
  · rwa [subset_antisymm_iff, and_iff_left (diff_subset_diff_left hIB'), diff_subset_iff,
      union_diff_self, union_comm]

  have hfin : (B \ B').encard ≠ ⊤
  · rw [hB.encard_diff_comm hB', hrw1, encard_ne_top_iff]
    apply hIfin.diff

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
    hB'.encard_diff_comm hB, hrw3, add_assoc, add_comm, WithTop.add_right_inj hfin] at hcalc1

  rw [← hcalc1, ← encard_diff_add_encard_inter (t := B), add_comm, inter_comm, ← hrw2,
    diff_inter_self_eq_diff]
  refine add_le_add_right (encard_le_encard ?_) _
  exact inter_subset_inter_right _ (diff_subset_diff_left hIB')

namespace Quotient

lemma eq_of_isBase_indep' [Finitary M₂] (hQ : M₂ ≤q M₁) {B : Set α} (hB₁ : M₁.IsBase B)
    (hB₂ : M₂.Indep B) : M₂ = M₁ := by
  replace hB₂ := show M₂.IsBase B from
    hB₂.isBase_of_maximal fun J hJ hBJ ↦ hB₁.eq_of_subset_indep (hQ.weakLE.indep_of_indep hJ) hBJ
  refine ext_isCircuit_not_indep hQ.ground_eq (fun C hC hCi ↦ ?_)
    (fun C hC ↦ ((hQ.cyclic_of_isCircuit hC).dep_of_nonempty hC.nonempty).not_indep)

  obtain ⟨e, he⟩ := hC.nonempty
  simpa [he] using encard_diff_le_encard_diff hQ.dual.weakLE hC.finite
    (hC.diff_singleton_isBasis he) hCi hB₂ hB₁ rfl.subset

def exists_isBasis_subset_pair (hQ : M₂ ≤q M₁) (X : Set α) :
    ∃ Is : Set α × Set α, Is.2 ⊆ Is.1 ∧ M₁.IsBasis' Is.1 X ∧ M₂.IsBasis' Is.2 X := by
  obtain ⟨I, hI⟩ := M₂.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := (hQ.weakLE.indep_of_indep hI.indep).subset_isBasis'_of_subset hI.subset
  exact ⟨⟨J,I⟩, hIJ, hJ, hI⟩

/-- The `discrepancy` of a set `X` relative to a quotient `hQ : M₂ ≤q M₁` is (informally)
the difference between the ranks of `X` in the two matroids, except it is also meaningful
when both ranks are infinite.
It is defined by noncomputably choosing a nested basis pair `I₂ ⊆ I₁` for `X` in the two matroids,
and taking the cardinality of `I₁ \ I₂`.

This quantity is only sensible if `M₂` is finitary (even when `X` is the ground set),
as otherwise it can depend on the choice of `I₁` and `I₂`; see `Matroid.TruncateFamily`. -/
noncomputable def discrepancy {M₂ : Matroid α} (hQ : M₂ ≤q M₁) (X : Set α) :=
  let h_ex := hQ.exists_isBasis_subset_pair X
  (h_ex.choose.1 \ h_ex.choose.2).encard

lemma exists_finite_witness {J₀ J : Set α} [M₂.Finitary] (hQ : M₂ ≤q M₁)
    (hJ₀X : M₂.IsBasis J₀ X) (hJX : M₁.IsBasis J X) (hss : J₀ ⊆ J) (hfin : (J \ J₀).Finite) :
    ∃ I₀ I, I.Finite ∧ M₁.Indep I ∧ M₂.IsBasis I₀ I ∧ I ⊆ X ∧ I \ I₀ = J \ J₀ := by
  have hJE' : J ⊆ M₂.E := hJX.indep.subset_ground.trans_eq hQ.ground_eq.symm
  have hcl := M₂.exists_subset_finite_closure_of_subset_closure hfin (Y := J₀)
  rw [hJ₀X.closure_eq_closure] at hcl
  obtain ⟨I₀, hI₀J₀, hI₀fin, hI₀i, hI₀ss⟩ :=
    hcl (M₂.subset_closure_of_subset' (diff_subset.trans hJX.subset) (diff_subset.trans hJE'))

  refine ⟨I₀, I₀ ∪ (J \ J₀), hI₀fin.union hfin,
    hJX.indep.subset (union_subset (hI₀J₀.trans hss) diff_subset),
      hI₀i.isBasis_of_subset_of_subset_closure subset_union_left (union_subset ?_ hI₀ss),
      union_subset (hI₀J₀.trans hJ₀X.subset) (diff_subset.trans hJX.subset), ?_⟩
  · exact M₂.subset_closure I₀ hI₀i.subset_ground
  simp only [union_diff_left, sdiff_eq_left]
  exact disjoint_sdiff_left.mono_right hI₀J₀

lemma encard_isBasis'_diff_isBasis'_mono [M₂.Finitary] (hQ : M₂ ≤q M₁)
    (hI₂ : M₂.IsBasis' I₂ X) (hI₁ : M₁.IsBasis' I₁ X) (hJ₂ : M₂.IsBasis' J₂ Y)
    (hJ₁ : M₁.IsBasis' J₁ Y) (hIss : I₂ ⊆ I₁) (hJss : J₂ ⊆ J₁) (hXY : X ⊆ Y) :
    (I₁ \ I₂).encard ≤ (J₁ \ J₂).encard := by
  obtain hinf | hfin := (J₁ \ J₂).finite_or_infinite.symm
  · simp [hinf.encard_eq]

  suffices aux : ∀ (K : Finset α), (K : Set α) ⊆ I₁ \ I₂ → (K.card : ℕ∞) ≤ (J₁ \ J₂).encard
  · obtain hinf' | hfin' := (I₁ \ I₂).finite_or_infinite.symm
    · obtain ⟨D,hD, hDcard⟩ := hinf'.exists_subset_card_eq (hfin.toFinset.card + 1)
      specialize aux D hD
      rw [hDcard, ENat.coe_add, ← encard_coe_eq_coe_finsetCard, Finite.coe_toFinset, Nat.cast_one,
        ENat.add_one_le_iff (by simpa)] at aux
      simp at aux
    simpa [← encard_coe_eq_coe_finsetCard] using aux hfin'.toFinset (by simp)

  intro K hKss
  rw [subset_diff] at hKss
  have hKE : (K : Set α) ⊆ M₂.E
  · exact hKss.1.trans (hI₁.indep.subset_ground.trans_eq hQ.ground_eq.symm)
  have hK : (K : Set α) ⊆ M₂.closure I₂
  · rw [hI₂.closure_eq_closure]
    exact M₂.subset_closure_of_subset' (hKss.1.trans hI₁.subset) hKE

  obtain ⟨L₀, L, hLfin, hLi, hL₀L, hLss, hdiff⟩ :=
    hQ.exists_finite_witness (X := I₂ ∪ K) (J₀ := I₂) (J := I₂ ∪ K)
    (hI₂.indep.isBasis_of_subset_of_subset_closure subset_union_left
      (union_subset (M₂.subset_closure I₂ hI₂.indep.subset_ground) hK))
    (hI₁.indep.subset (union_subset hIss hKss.1)).isBasis_self
    subset_union_left (by simp [K.finite_toSet.diff])

  rw [union_diff_left, sdiff_eq_left.2 hKss.2] at hdiff
  rw [← encard_coe_eq_coe_finsetCard, ← hdiff]

  have hL : L ⊆ X := hLss.trans (union_subset hI₂.subset (hKss.1.trans hI₁.subset))

  exact encard_diff_le_encard_diff (hQ.restrict Y).dual.weakLE hLfin
    (hL₀L.isBasis_restrict_of_subset (hL.trans hXY))
    (hLi.indep_restrict_of_subset (hL.trans hXY))
    (by rwa [isBase_restrict_iff']) (by rwa [isBase_restrict_iff']) hJss

lemma encard_diff_eq_encard_diff_of_isBasis' [M₂.Finitary] (hQ : M₂ ≤q M₁)
    (hI₂ : M₂.IsBasis' I₂ X) (hI₁ : M₁.IsBasis' I₁ X) (hJ₂ : M₂.IsBasis' J₂ X)
    (hJ₁ : M₁.IsBasis' J₁ X) (hIss : I₂ ⊆ I₁) (hJss : J₂ ⊆ J₁) :
    (I₁ \ I₂).encard = (J₁ \ J₂).encard := by
  refine le_antisymm ?_ ?_
  · exact hQ.encard_isBasis'_diff_isBasis'_mono hI₂ hI₁ hJ₂ hJ₁ hIss hJss rfl.subset
  exact hQ.encard_isBasis'_diff_isBasis'_mono hJ₂ hJ₁ hI₂ hI₁ hJss hIss rfl.subset

lemma encard_diff_eq_encard_diff_of_isBase [M₂.Finitary] {B₁ B₂ B₁' B₂' : Set α} (hQ : M₂ ≤q M₁)
    (hB₂ : M₂.IsBase B₂) (hB₂' : M₂.IsBase B₂') (hB₁ : M₁.IsBase B₁) (hB₁' : M₁.IsBase B₁')
    (hss : B₂ ⊆ B₁) (hss' : B₂' ⊆ B₁') : (B₁ \ B₂).encard = (B₁' \ B₂').encard := by
  refine hQ.encard_diff_eq_encard_diff_of_isBasis' (hB₂.isBasis_ground.isBasis') ?_
    (hB₂'.isBasis_ground.isBasis') ?_ hss hss' <;>
  rwa [hQ.ground_eq, isBasis'_iff_isBasis, isBasis_ground_iff]

lemma encard_isBasis'_diff_eq_discrepancy [M₂.Finitary] (hQ : M₂ ≤q M₁)
    (hI₂ : M₂.IsBasis' I₂ X) (hI₁ : M₁.IsBasis' I₁ X) (hss : I₂ ⊆ I₁) :
    (I₁ \ I₂).encard = hQ.discrepancy X :=
  have Ps := hQ.exists_isBasis_subset_pair X
  hQ.encard_diff_eq_encard_diff_of_isBasis' hI₂ hI₁ Ps.choose_spec.2.2 Ps.choose_spec.2.1 hss
    Ps.choose_spec.1

lemma encard_isBasis_diff_eq_discrepancy [M₂.Finitary] (hQ : M₂ ≤q M₁)
    (hI₂ : M₂.IsBasis I₂ X) (hI₁ : M₁.IsBasis I₁ X) (hss : I₂ ⊆ I₁) :
    (I₁ \ I₂).encard = hQ.discrepancy X :=
  hQ.encard_isBasis'_diff_eq_discrepancy hI₂.isBasis' hI₁.isBasis' hss

lemma encard_isBase_diff_eq_discrepancy_ground [M₂.Finitary] (hQ : M₂ ≤q M₁) (hB₂ : M₂.IsBase B₂)
    (hB₁ : M₁.IsBase B₁) (hss : B₂ ⊆ B₁) : (B₁ \ B₂).encard = hQ.discrepancy M₁.E :=
  hQ.encard_isBasis_diff_eq_discrepancy (by rwa [← hQ.ground_eq, isBasis_ground_iff])
    hB₁.isBasis_ground hss

lemma eRk_left_add_discrepancy_eq [M₂.Finitary] (hQ : M₂ ≤q M₁) (X : Set α) :
    M₂.eRk X + hQ.discrepancy X = M₁.eRk X := by
  obtain ⟨I, hI⟩ := M₂.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := (hQ.weakLE.indep_of_indep hI.indep).subset_isBasis'_of_subset hI.subset
  rw [← hI.encard_eq_eRk, ← hJ.encard_eq_eRk, ← hQ.encard_isBasis'_diff_eq_discrepancy hI hJ hIJ,
    add_comm, encard_diff_add_encard_of_subset hIJ]

lemma discrepancy_mono [M₂.Finitary] (hQ : M₂ ≤q M₁) (hXY : X ⊆ Y) :
    hQ.discrepancy X ≤ hQ.discrepancy Y := by
  obtain ⟨I₂, hI₂⟩ := M₂.exists_isBasis' X
  obtain ⟨I₁, hI₁, hssI⟩ :=
    (hQ.weakLE.indep_of_indep hI₂.indep).subset_isBasis'_of_subset hI₂.subset
  obtain ⟨J₂, hJ₂⟩ := M₂.exists_isBasis' Y
  obtain ⟨J₁, hJ₁, hssJ⟩ :=
    (hQ.weakLE.indep_of_indep hJ₂.indep).subset_isBasis'_of_subset hJ₂.subset
  rw [← hQ.encard_isBasis'_diff_eq_discrepancy hI₂ hI₁ hssI,
    ← hQ.encard_isBasis'_diff_eq_discrepancy hJ₂ hJ₁ hssJ]
  exact hQ.encard_isBasis'_diff_isBasis'_mono hI₂ hI₁ hJ₂ hJ₁ hssI hssJ hXY

lemma restrict_eq_restrict_of_discrepancy_le_zero [M₂.Finitary] (hQ : M₂ ≤q M₁)
    (h : hQ.discrepancy X ≤ 0) : M₂ ↾ X = M₁ ↾ X := by
  simp only [restrict_eq_restrict_iff]
  refine fun I hIX ↦ ⟨hQ.weakLE.indep_of_indep, fun hI ↦ ?_⟩
  obtain ⟨J, hJ⟩ := M₂.exists_isBasis' I
  replace h := (hQ.discrepancy_mono hIX).trans h
  rw [← hQ.encard_isBasis'_diff_eq_discrepancy hJ hI.isBasis_self.isBasis' hJ.subset,
    nonpos_iff_eq_zero, encard_eq_zero, diff_eq_empty] at h
  rw [← h.antisymm hJ.subset] at hJ
  exact hJ.indep

lemma eq_of_discrepancy_le_zero [M₂.Finitary] (hQ : M₂ ≤q M₁) (h : hQ.discrepancy M₁.E ≤ 0) :
    M₂ = M₁ := by
  rw [← M₁.restrict_ground_eq_self, ← M₂.restrict_ground_eq_self, hQ.ground_eq]
  exact hQ.restrict_eq_restrict_of_discrepancy_le_zero h

lemma discrepancy_inter_ground [M₂.Finitary] (hQ : M₂ ≤q M₁) (X : Set α) :
    hQ.discrepancy (X ∩ M₁.E) = hQ.discrepancy X := by
  obtain ⟨I, hI⟩ := M₂.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := ((hQ.weakLE).indep_of_indep hI.indep).subset_isBasis'_of_subset hI.subset
  have hI' := hI.isBasis_inter_ground
  rw [hQ.ground_eq] at hI'
  rw [← hQ.encard_isBasis_diff_eq_discrepancy hI' hJ.isBasis_inter_ground hIJ,
    ← hQ.encard_isBasis'_diff_eq_discrepancy hI hJ hIJ]

lemma discrepancy_ne_top [M₁.RankFinite] (hQ : M₂ ≤q M₁) (X : Set α) : hQ.discrepancy X ≠ ⊤ := by
  have := hQ.rankFinite
  intro htop
  have hdis := hQ.eRk_left_add_discrepancy_eq X
  rw [htop] at hdis
  simp [eq_comm, eRk_eq_top_iff, M₁.isRkFinite_set X] at hdis

@[simp]
lemma discrepancy_empty [M₂.Finitary] (hQ : M₂ ≤q M₁) : hQ.discrepancy ∅ = 0 := by
  simpa using hQ.eRk_left_add_discrepancy_eq ∅

noncomputable abbrev nDiscrepancy (hQ : M₂ ≤q M₁) (X : Set α) : ℕ := (hQ.discrepancy X).toNat

lemma rk_left_add_nDiscrepancy_eq [M₁.RankFinite] (hQ : M₂ ≤q M₁) (X : Set α) :
    M₂.rk X + hQ.nDiscrepancy X = M₁.rk X := by
  have := hQ.rankFinite
  have hdis := hQ.eRk_left_add_discrepancy_eq X
  rw [rk, rk, ← hdis, ENat.toNat_add (by simp only [ne_eq, eRk_ne_top_iff, M₂.isRkFinite_set X])
    (hQ.discrepancy_ne_top _)]

lemma cast_nDiscrepancy_eq [M₁.RankFinite] (hQ : M₂ ≤q M₁) (X : Set α) :
    (hQ.nDiscrepancy X : ℕ∞) = hQ.discrepancy X := by
  simp [nDiscrepancy, hQ.discrepancy_ne_top]

lemma nDiscrepancy_mono [M₁.RankFinite] (hQ : M₂ ≤q M₁) : Monotone hQ.nDiscrepancy :=
  have := hQ.rankFinite
  fun X Y (hXY : X ⊆ Y) ↦ ENat.toNat_le_toNat (hQ.discrepancy_mono hXY) (hQ.discrepancy_ne_top _)

lemma nDiscrepancy_le_of_subset [M₁.RankFinite] (hQ : M₂ ≤q M₁) {X Y : Set α} (hXY : X ⊆ Y) :
    hQ.nDiscrepancy X ≤ hQ.nDiscrepancy Y :=
  hQ.nDiscrepancy_mono hXY

lemma intCast_rk_sub_rk_eq_nDiscrepancy [M₁.RankFinite] (hQ : M₂ ≤q M₁) (X : Set α) :
    (M₁.rk X : ℤ) - (M₂.rk X : ℤ) = hQ.nDiscrepancy X := by
  simp [← hQ.rk_left_add_nDiscrepancy_eq X]

lemma intCast_rank_sub_rank_eq_nDiscrepancy [M₁.RankFinite] (hQ : M₂ ≤q M₁) :
    (M₁.rank : ℤ) - M₂.rank  = hQ.nDiscrepancy M₁.E := by
  rw [rank_def, rank_def, hQ.ground_eq, intCast_rk_sub_rk_eq_nDiscrepancy]

def foo [M₁.RankFinite] (hQ : M₂ ≤q M₁) {X : Set α} :
    hQ.nDiscrepancy X = hQ.nDiscrepancy M₁.E ↔ M₁ ／ X = M₂ ／ X := by
  have := hQ.rankFinite
  refine ⟨fun h ↦ ext_rk (by simp [hQ.ground_eq]) (fun Y hY ↦ ?_), fun h_eq ↦ ?_⟩
  · zify
    simp only [contract_rk_cast_int_eq]

    have h1 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy X

    have h2 := hQ.intCast_rk_sub_rk_eq_nDiscrepancy (Y ∪ X)
    have h3 : hQ.nDiscrepancy (Y ∪ X) ≤ hQ.nDiscrepancy M₁.E := by
      rw [nDiscrepancy, ← discrepancy_inter_ground, ← nDiscrepancy]
      exact hQ.nDiscrepancy_mono inter_subset_right
    have h4 := hQ.nDiscrepancy_le_of_subset (X := X) (Y := Y ∪ X) subset_union_right
    linarith
  apply_fun fun X ↦ (rank X : ℤ) at h_eq
  simp only [contract_rank_cast_int_eq] at h_eq
  linarith [hQ.intCast_rank_sub_rank_eq_nDiscrepancy, hQ.intCast_rk_sub_rk_eq_nDiscrepancy X]

@[simp]
lemma nDiscrepancy_empty [M₂.Finitary] (hQ : M₂ ≤q M₁) : hQ.nDiscrepancy ∅ = 0 := by
  simp [nDiscrepancy]


-- lemma nDiscrepancy_covers {F : Set α} (hF : M₁.IsFlat F) (hQ : M₂ ≤q M₁)
-- (hdis : hQ.nDiscrepancy F < hQ.nDiscrepancy M₁.E) : ∃ F₁, (F ⋖[M₁] F₁) := by
--   have he : ∃ e, e ∈ M₁.E \ F := by
--     by_contra! hnot
--     have hFE : F ⊆ M₁.E := hF.subset_ground
--     --I'm pretty sure the following proof can be shorten, no idea how
--     have hEF : M₁.E = F := by
--       refine ext ?_
--       intro c
--       refine⟨ ?_ , (fun a ↦ hFE a)⟩
--       intro hs
--       by_contra hcg
--       exact hnot c (mem_diff_of_mem hs hcg)
--     rw [hEF ] at hdis
--     exact (lt_self_iff_false (hQ.nDiscrepancy F)).mp hdis
--   obtain ⟨e, he ⟩ := he
--   use M₁.closure (insert e F)
--   exact hF.covBy_closure_insert (notMem_of_mem_diff he)




  -- refine ⟨fun h ↦ ext_indep (by simp [hQ.ground_eq]) fun I hI ↦ ?_, fun h ↦ ?_⟩
  -- · obtain ⟨J, D, h₂, h₁, hJD, hcard⟩ := hQ.exists_isBasis'_diff_isBasis' X
  --   rw [h₁.contract_indep_iff, h₂.contract_indep_iff, and_congr_left_iff, ← union_assoc]
  --   rw [nDiscrepancy, ← hcard] at h
  --   refine fun hdj ↦ ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  -- sorry
