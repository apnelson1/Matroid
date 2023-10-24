import Matroid.Basic

open Set

namespace Matroid

-- ### Various alternative ways to construct a matroid from axioms.

/-- A constructor for matroids via the base axioms.
  (In fact, just a wrapper for the definition of a matroid) -/
def matroid_of_base (E : Set α) (Base : Set α → Prop) (exists_base : ∃ B, Base B)
    (base_exchange : ExchangeProperty Base)
    (maximality : ∀ X, X ⊆ E → ExistsMaximalSubsetProperty (∃ B, Base B ∧ · ⊆ B) X)
    (support : ∀ B, Base B → B ⊆ E) : Matroid α :=
  ⟨E, Base, exists_base, base_exchange, maximality, support⟩

@[simp] theorem matroid_of_base_apply (E : Set α) (Base : Set α → Prop) (exists_base : ∃ B, Base B)
    (base_exchange : ExchangeProperty Base)
    (maximality : ∀ X, X ⊆ E → ExistsMaximalSubsetProperty (∃ B, Base B ∧ · ⊆ B) X)
    (support : ∀ B, Base B → B ⊆ E) :
    (matroid_of_base E Base exists_base base_exchange maximality support).Base = Base := rfl

/-- A constructor for a matroid using the independence axioms for infinite matroids. -/
def matroid_of_indep (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_maximal : ∀ X, X ⊆ E → ExistsMaximalSubsetProperty Indep X)
    (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_base E (· ∈ maximals (· ⊆ ·) (setOf Indep))
  ( by
      obtain ⟨B, ⟨hB,-,-⟩, hB₁⟩ := h_maximal E rfl.subset ∅ h_empty (empty_subset _)
      exact ⟨B, ⟨hB, fun B' hB' hBB' ↦ hB₁ ⟨hB', empty_subset _,h_support B' hB'⟩ hBB'⟩⟩ )
  ( by
      rintro B B' ⟨hB, hBmax⟩ ⟨hB',hB'max⟩ e he
      have hnotmax : B \ {e} ∉ maximals (· ⊆ ·) (setOf Indep)
      { simp only [mem_maximals_setOf_iff, diff_singleton_subset_iff, not_and, not_forall,
          exists_prop, exists_and_left]
        exact fun _ ↦ ⟨B, hB, subset_insert _ _, by simpa using he.1⟩ }

      obtain ⟨f,hf,hfB⟩ := h_aug (h_subset hB (diff_subset B {e})) hnotmax ⟨hB',hB'max⟩
      simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf

      have hfB' : f ∉ B := by (intro hfB; obtain rfl := hf.2 hfB; exact he.2 hf.1)

      refine' ⟨f, ⟨hf.1, hfB'⟩, by_contra (fun hnot ↦ _)⟩
      obtain ⟨x,hxB, hind⟩ :=  h_aug hfB hnot ⟨hB, hBmax⟩
      simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or, not_and, not_not] at hxB
      obtain rfl := hxB.2.2 hxB.1
      rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind
      exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _) )
  ( by
      rintro X hXE I ⟨hB, hB, hIB⟩ hIX
      obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal X hXE I (h_subset hB.1 hIB) hIX
      obtain ⟨BJ, hBJ⟩ := h_maximal E rfl.subset J hJ (h_support J hJ)
      refine' ⟨J, ⟨⟨BJ,_, hBJ.1.2.1⟩ ,hIJ,hJX⟩, _⟩
      · exact ⟨hBJ.1.1, fun B' hB' hBJB' ↦ hBJ.2 ⟨hB',hBJ.1.2.1.trans hBJB', h_support _ hB'⟩ hBJB'⟩
      simp only [maximals, mem_setOf_eq, and_imp, forall_exists_index]
      rintro A B' (hBi' : Indep _) - hB'' hIA hAX hJA
      simp only [mem_setOf_eq, and_imp] at hJmax
      exact hJmax (h_subset hBi' hB'') hIA hAX hJA )
  ( fun B hB ↦ h_support B hB.1 )

@[simp] theorem matroid_of_indep_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_maximal : ∀ X, X ⊆ E → ExistsMaximalSubsetProperty Indep X)
    (h_support : ∀ I, Indep I → I ⊆ E) :
    (matroid_of_indep E Indep h_empty h_subset h_aug h_maximal h_support).Indep = Indep := by
  ext I
  simp_rw [indep_iff_subset_base, matroid_of_indep, matroid_of_base_apply, mem_maximals_setOf_iff]
  refine' ⟨fun ⟨B, ⟨hBi, _⟩, hIB⟩ ↦ h_subset hBi hIB, fun h ↦ _⟩
  obtain ⟨B, hB⟩ := h_maximal E rfl.subset I h (h_support I h)
  simp_rw [mem_maximals_setOf_iff, and_imp] at hB
  exact ⟨B, ⟨hB.1.1, fun J hJ hBJ ↦ hB.2 hJ (hB.1.2.1.trans hBJ) (h_support J hJ) hBJ⟩, hB.1.2.1⟩


/-- An independence predicate satisfying the finite matroid axioms determines a matroid,
  provided independence is compact (i.e. determined by its behaviour on finite sets). 
  Uses the axiom of choice.  -/
def matroid_of_indep_of_compact (E : Set α) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → I.Finite → Indep J → J.Finite → I.ncard < J.ncard →
    ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_compact : ∀ I, (∀ J, J ⊆ I → J.Finite → Indep J) → Indep I)
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α :=

  have htofin : ∀ I e, Indep I → ¬ Indep (insert e I) →
    ∃ I₀, I₀ ⊆ I ∧ I₀.Finite ∧ ¬ Indep (insert e I₀) := by
      by_contra h; push_neg at h
      obtain ⟨I, e, -, hIe, h⟩ := h
      refine hIe <| h_compact _ fun J hJss hJfin ↦ ?_
      exact ind_mono (h (J \ {e}) (by rwa [diff_subset_iff]) (hJfin.diff _)) (by simp)

  matroid_of_indep E Indep h_empty ind_mono
  ( by
    intro I B hI hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, not_and, not_forall, exists_prop,
      exists_and_left, iff_true_intro hI, true_imp_iff] at hImax hBmax
    obtain ⟨I', hI', hII', hne⟩ := hImax
    obtain ⟨e, heI', heI⟩ := exists_of_ssubset (hII'.ssubset_of_ne hne)
    have hins : Indep (insert e I) := ind_mono hI' (insert_subset heI' hII')
    obtain (heB | heB) := em (e ∈ B)
    · exact ⟨e, ⟨heB, heI⟩, hins⟩
    by_contra hcon; push_neg at hcon

    have heBdep : ¬Indep (insert e B) :=
      fun hi ↦ heB <| insert_eq_self.1 (hBmax.2 hi (subset_insert _ _)).symm

    /- There is a finite subset `B₀` of `B` so that `B₀ + e` is dependent-/
    obtain ⟨B₀, hB₀B, hB₀fin, hB₀e⟩ := htofin B e hBmax.1  heBdep
    have hB₀ := ind_mono hBmax.1 hB₀B

    /- There is a finite subset `I₀` of `I` so that `I₀` doesn't extend into `B₀` -/
    have hexI₀ : ∃ I₀, I₀ ⊆ I ∧ I₀.Finite ∧ ∀ x, x ∈ B₀ \ I₀ → ¬Indep (insert x I₀)
    · have hchoose : ∀ (b : ↑(B₀ \ I)), ∃ Ib, Ib ⊆ I ∧ Ib.Finite ∧ ¬Indep (insert (b : α) Ib)
      · rintro ⟨b, hb⟩; exact htofin I b hI (hcon b ⟨hB₀B hb.1, hb.2⟩)
      choose! f hf using hchoose
      have _ := finite_coe_iff.2 (hB₀fin.diff I)
      refine ⟨iUnion f ∪ (B₀ ∩ I),
        union_subset (iUnion_subset (fun i ↦ (hf i).1)) (inter_subset_right _ _),
        (finite_iUnion <| fun i ↦ (hf i).2.1).union (hB₀fin.subset (inter_subset_left _ _)),
        fun x ⟨hxB₀, hxn⟩ hi ↦ ?_⟩
      have hxI : x ∉ I := fun hxI ↦ hxn <| Or.inr ⟨hxB₀, hxI⟩
      refine (hf ⟨x, ⟨hxB₀, hxI⟩⟩).2.2 (ind_mono hi <| insert_subset_insert ?_)
      apply subset_union_of_subset_left
      apply subset_iUnion

    obtain ⟨I₀, hI₀I, hI₀fin, hI₀⟩ := hexI₀

    set E₀ := insert e (I₀ ∪ B₀)
    have hE₀fin : E₀.Finite := (hI₀fin.union hB₀fin).insert e

    /- Extend `B₀` to a maximal independent subset of `I₀ ∪ B₀ + e` -/
    obtain ⟨J, ⟨hB₀J, hJ, hJss⟩, hJmax⟩ := Finite.exists_maximal_wrt (f := id)
      (s := {J | B₀ ⊆ J ∧ Indep J ∧ J ⊆ E₀})
      (hE₀fin.finite_subsets.subset (by simp))
      ⟨B₀, Subset.rfl, hB₀, (subset_union_right _ _).trans (subset_insert _ _)⟩

    have heI₀ : e ∉ I₀ := not_mem_subset hI₀I heI
    have heI₀i : Indep (insert e I₀) := ind_mono hins (insert_subset_insert hI₀I)

    have heJ : e ∉ J := fun heJ ↦ hB₀e (ind_mono hJ <| insert_subset heJ hB₀J)

    have hJfin := hE₀fin.subset hJss

    /- We have `|I₀ + e| ≤ |J|`, since otherwise we could extend the maximal set `J`  -/
    have hcard : (insert e I₀).ncard ≤ J.ncard
    · refine not_lt.1 fun hlt ↦ ?_
      obtain ⟨f, hfI, hfJ, hfi⟩ := ind_aug hJ hJfin heI₀i (hI₀fin.insert e) hlt
      have hfE₀ : f ∈ E₀ := mem_of_mem_of_subset hfI (insert_subset_insert (subset_union_left _ _))
      refine hfJ (insert_eq_self.1 <| Eq.symm (hJmax _
        ⟨hB₀J.trans <| subset_insert _ _,hfi,insert_subset hfE₀ hJss⟩ (subset_insert _ _)))


    /- But this means `|I₀| < |J|`, and extending `I₀` into `J` gives a contradiction -/
    rw [ncard_insert_of_not_mem heI₀ hI₀fin, ←Nat.lt_iff_add_one_le] at hcard

    obtain ⟨f, hfJ, hfI₀, hfi⟩ := ind_aug (ind_mono hI hI₀I) hI₀fin hJ hJfin hcard
    exact hI₀ f ⟨Or.elim (hJss hfJ) (fun hfe ↦ (heJ <| hfe ▸ hfJ).elim) (by aesop), hfI₀⟩ hfi )

    ( by
      rintro X - I hI hIX
      have hzorn := zorn_subset_nonempty {Y | Indep Y ∧ I ⊆ Y ∧ Y ⊆ X} ?_ I ⟨hI, Subset.rfl, hIX⟩
      · obtain ⟨J, hJ, -, hJmax⟩ := hzorn
        exact ⟨J, hJ, fun K hK hJK ↦ (hJmax K hK hJK).subset⟩

      refine fun Is hIs hchain ⟨K, hK⟩ ↦ ⟨⋃₀ Is, ⟨?_,?_,?_⟩, fun _ ↦ subset_sUnion_of_mem ⟩
      · refine h_compact _ fun J hJ hJfin ↦ ?_
        have hchoose : ∀ e, e ∈ J → ∃ I, I ∈ Is ∧ (e : α) ∈ I
        · exact fun _ he ↦ mem_sUnion.1 <| hJ he
        choose! f hf using hchoose
        refine J.eq_empty_or_nonempty.elim (fun hJ ↦ hJ ▸ h_empty) (fun hne ↦ ?_)
        obtain ⟨x, hxJ, hxmax⟩ := Finite.exists_maximal_wrt f _ hJfin hne
        refine ind_mono (hIs (hf x hxJ).1).1 fun y hyJ ↦ ?_
        obtain (hle | hle) := hchain.total (hf _ hxJ).1 (hf _ hyJ).1
        · rw [hxmax _ hyJ hle]; exact (hf _ hyJ).2
        exact hle (hf _ hyJ).2

      · exact subset_sUnion_of_subset _ K (hIs hK).2.1 hK
      exact sUnion_subset fun X hX ↦ (hIs hX).2.2 )
    h_support


/-- If there is an absolute upper bound on the size of a set satisfying `P`, then the
  maximal subset property always holds. -/
theorem existsMaximalSubsetProperty_of_bdd {P : Set α → Prop}
    (hP : ∃ (n : ℕ), ∀ Y, P Y → Y.encard ≤ n) (X : Set α) : ExistsMaximalSubsetProperty P X := by
  obtain ⟨n, hP⟩ := hP

  rintro I hI hIX
  have hfin : Set.Finite (ncard '' {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X})
  · rw [finite_iff_bddAbove, bddAbove_def]
    simp_rw [ENat.le_coe_iff] at hP
    use n
    rintro x ⟨Y, ⟨hY,-,-⟩, rfl⟩
    obtain ⟨n₀, heq, hle⟩ := hP Y hY
    rwa [ncard_def, heq, ENat.toNat_coe]
    -- have := (hP Y hY).2
  obtain ⟨Y, hY, hY'⟩ := Finite.exists_maximal_wrt' ncard _ hfin ⟨I, hI, rfl.subset, hIX⟩
  refine' ⟨Y, hY, fun J ⟨hJ, hIJ, hJX⟩ (hYJ : Y ⊆ J) ↦ (_ : J ⊆ Y)⟩
  have hJfin := finite_of_encard_le_coe (hP J hJ)
  refine' (eq_of_subset_of_ncard_le hYJ _ hJfin).symm.subset
  rw [hY' J ⟨hJ, hIJ, hJX⟩ (ncard_le_of_subset hYJ hJfin)]

/-- If there is an absolute upper bound on the size of an independent set, then the maximality axiom
  isn't needed to define a matroid by independent sets. -/
def matroid_of_indep_of_bdd (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n )
    (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_indep E Indep h_empty h_subset h_aug
    (fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd h_bdd X) h_support

@[simp] theorem matroid_of_indep_of_bdd_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n) (h_support : ∀ I, Indep I → I ⊆ E) :
    (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).Indep = Indep := by
  simp [matroid_of_indep_of_bdd]

/-- `matroid_of_indep_of_bdd` constructs a `FiniteRk` matroid. -/
instance (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) →
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n )
    (h_support : ∀ I, Indep I → I ⊆ E) :
    Matroid.FiniteRk (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support) := by

  refine' (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).exists_base.elim
    (fun B hB ↦ hB.finiteRk_of_finite _)
  obtain ⟨n, h_bdd⟩ := h_bdd
  refine' finite_of_encard_le_coe (h_bdd _ _)
  rw [←matroid_of_indep_of_bdd_apply E Indep, indep_iff_subset_base]
  exact ⟨_, hB, rfl.subset⟩

/-- If there is an absolute upper bound on the size of an independent set, then matroids
  can be defined using an 'augmentation' axiom similar to the standard definition of
  finite matroids for independent sets. -/
def matroid_of_indep_of_bdd_augment (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) :
    Matroid α :=
  matroid_of_indep_of_bdd E Indep h_empty h_subset
    (by
      simp_rw [mem_maximals_setOf_iff, not_and, not_forall, exists_prop,  mem_diff,
        and_imp, and_assoc]
      rintro I B hI hImax hB hBmax
      obtain ⟨J, hJ, hIJ, hne⟩ := hImax hI
      obtain ⟨n, h_bdd⟩ := h_bdd

      have hlt : I.encard < J.encard :=
        (finite_of_encard_le_coe (h_bdd J hJ)).encard_lt_encard (hIJ.ssubset_of_ne hne)
      have hle : J.encard ≤ B.encard
      · refine le_of_not_lt (fun hlt' ↦ ?_)
        obtain ⟨e, he⟩ := ind_aug hB hJ hlt'
        rw [hBmax he.2.2 (subset_insert _ _)] at he
        exact he.2.1 (mem_insert _ _)
      exact ind_aug hI hB (hlt.trans_le hle) )
    h_bdd h_support

@[simp] theorem matroid_of_indep_of_bdd_augment_apply (E : Set α) (Indep : Set α → Prop)
    (h_empty : Indep ∅) (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) :
    (matroid_of_indep_of_bdd_augment E Indep h_empty h_subset ind_aug h_bdd h_support).Indep
      = Indep := by
  simp [matroid_of_indep_of_bdd_augment]

instance (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅)
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.encard < J.encard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_supp : ∀ I, Indep I → I ⊆ E) :
    (matroid_of_indep_of_bdd_augment E Indep h_empty h_subset ind_aug h_bdd h_supp).FiniteRk := by
  rw [matroid_of_indep_of_bdd_augment]; infer_instance

/-- A collection of bases with the exchange property and at least one finite member is a matroid -/
def matroid_of_exists_finite_base {α : Type _} (E : Set α) (Base : Set α → Prop)
    (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : ExchangeProperty Base)
    (support : ∀ B, Base B → B ⊆ E) : Matroid α :=
    matroid_of_base E Base
    (by { obtain ⟨B,h⟩ := exists_finite_base; exact ⟨B,h.1⟩ }) base_exchange
    (by {
      obtain ⟨B, hB, hfin⟩ := exists_finite_base
      refine' fun X _ ↦ Matroid.existsMaximalSubsetProperty_of_bdd
        ⟨B.ncard, fun Y ⟨B', hB', hYB'⟩ ↦ _⟩ X
      rw [hfin.cast_ncard_eq, encard_base_eq_of_exch base_exchange hB hB']
      exact encard_mono hYB' })
    support

@[simp] theorem matroid_of_exists_finite_base_apply {α : Type _} (E : Set α) (Base : Set α → Prop)
    (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : ExchangeProperty Base)
    (support : ∀ B, Base B → B ⊆ E) :
    (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support).Base = Base :=
  rfl

/-- A matroid constructed with a finite Base is `FiniteRk` -/
instance finiteRk_of_exists_finite_base {E : Set α} {Base : Set α → Prop}
    {exists_finite_base : ∃ B, Base B ∧ B.Finite} {base_exchange : ExchangeProperty Base}
    {support : ∀ B, Base B → B ⊆ E} :
    Matroid.FiniteRk
      (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support) :=
  ⟨exists_finite_base⟩

/-- If `E` is finite, then any nonempty collection of its subsets
  with the exchange property is the collection of bases of a matroid on `E`. -/
def matroid_of_base_of_finite {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_base : ∃ B, Base B) (base_exchange : ExchangeProperty Base)
    (support : ∀ B, Base B → B ⊆ E) : Matroid α :=
  matroid_of_exists_finite_base E Base
    (by { obtain ⟨B,hB⟩ := exists_base; exact ⟨B,hB, hE.subset (support _ hB)⟩ })
    base_exchange support

@[simp] theorem matroid_of_base_of_finite_apply {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_base : ∃ B, Base B) (base_exchange : ExchangeProperty Base)
    (support : ∀ B, Base B → B ⊆ E) :
    (matroid_of_base_of_finite hE Base exists_base base_exchange support).Base = Base := rfl

/-- If `E` is finite, then any collection of subsets of `E` satisfying
  the usual independence axioms determines a matroid -/
def matroid_of_indep_of_finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_indep_of_bdd_augment E Indep h_empty ind_mono
  ( fun I J hI hJ hlt ↦ ind_aug hI hJ ( by
      rwa [←Nat.cast_lt (α := ℕ∞), (hE.subset (h_support hJ)).cast_ncard_eq,
      (hE.subset (h_support hI)).cast_ncard_eq]) )
  (⟨E.ncard, fun I hI ↦ by { rw [hE.cast_ncard_eq]; exact encard_mono (h_support hI) }⟩ )
  h_support

instance matroid_of_indep_of_finite.Finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
    ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Finite :=
  ⟨hE⟩

instance matroid_of_indep_of_finite_apply {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
    ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Indep = Indep := by
  simp [matroid_of_indep_of_finite]


@[simp] theorem matroid_of_indep_of_compact_apply (E : Set α) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → I.Finite → Indep J → J.Finite → I.ncard < J.ncard →
    ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_compact : ∀ I, (∀ J, J ⊆ I → J.Finite → Indep J) → Indep I)
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
  (matroid_of_indep_of_compact E Indep h_empty ind_mono ind_aug h_compact h_support).Indep
    = Indep := by simp [matroid_of_indep_of_compact]

instance matroid_of_indep_of_compact_finitary (E : Set α) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → I.Finite → Indep J → J.Finite → I.ncard < J.ncard →
    ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_compact : ∀ I, (∀ J, J ⊆ I → J.Finite → Indep J) → Indep I)
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
    (matroid_of_indep_of_compact E Indep h_empty ind_mono ind_aug h_compact h_support).Finitary :=
  ⟨ by simpa ⟩

/-- An independence predicate on `Finset α` that obeys the finite matroid axioms determines a
  finitary matroid on `α`.
  TODO : Simp lemmas -/
def matroid_of_indep_finset [DecidableEq α] (E : Set α) (Indep : Finset α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.card < J.card →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I))
    (h_support : ∀ ⦃I⦄, Indep I → (I : Set α) ⊆ E) : Matroid α :=
  matroid_of_indep_of_compact E (fun I ↦ (∀ (J : Finset α), (J : Set α) ⊆ I → Indep J))
    ( by simpa [subset_empty_iff] )
    ( fun I J hJ hIJ K hKI ↦ hJ _ (hKI.trans hIJ) )
    ( by
      intro I J hI hIfin hJ hJfin hIJ
      rw [ncard_eq_toFinset_card _ hIfin, ncard_eq_toFinset_card _ hJfin] at hIJ
      have aug := ind_aug (hI _ (by simp [Subset.rfl])) (hJ _ (by simp [Subset.rfl])) hIJ
      simp only [Finite.mem_toFinset] at aug
      obtain ⟨e, heJ, heI, hi⟩ := aug
      exact ⟨e, heJ, heI, fun K hK ↦ ind_mono hi <| Finset.coe_subset.1 (by simpa)⟩ )
    ( fun I h J hJ ↦ h _ hJ J.finite_toSet _ Subset.rfl )
    ( fun I hI x hxI ↦ by simpa using h_support <| hI {x} (by simpa) )

/-- Construct a matroid from an independence predicate that agrees with that of some matroid `M'`.
  Computable even when `M'` is not known constructively. -/
def matroid_of_indep_of_exists_matroid (E : Set α) (Indep : Set α → Prop)
    (hM : ∃ (M : Matroid α), E = M.E ∧ ∀ I, M.Indep I ↔ Indep I) : Matroid α :=
  have hex : ∃ (M : Matroid α), E = M.E ∧ M.Indep = Indep := by
    obtain ⟨M, rfl, h⟩ := hM; refine ⟨_, rfl, funext (by simp [h])⟩
  matroid_of_indep E Indep
  ( by obtain ⟨M, -, rfl⟩ := hex; exact M.empty_indep )
  ( by obtain ⟨M, -, rfl⟩ := hex; exact fun I J hJ hIJ ↦ hJ.subset hIJ )
  ( by obtain ⟨M, -, rfl⟩ := hex; exact M.aug_property )
  ( by obtain ⟨M, rfl, rfl⟩ := hex; exact M.existsMaximalSubsetProperty_indep )
  ( by obtain ⟨M, rfl, rfl⟩ := hex; exact fun I ↦ Indep.subset_ground )

@[simp] theorem matroid_of_indep_of_exists_matroid_indep (E : Set α) (Indep : Set α → Prop)
    (hM : ∃ (M : Matroid α), E = M.E ∧ ∀ I, M.Indep I ↔ Indep I) :
    (matroid_of_indep_of_exists_matroid E Indep hM).Indep = Indep := by
  simp [matroid_of_indep_of_exists_matroid]

@[simp] theorem matroid_of_indep_of_exists_matroid_ground (E : Set α) (Indep : Set α → Prop)
    (hM : ∃ (M : Matroid α), E = M.E ∧ ∀ I, M.Indep I ↔ Indep I) :
    (matroid_of_indep_of_exists_matroid E Indep hM).E = E := rfl

end Matroid