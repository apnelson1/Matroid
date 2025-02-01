import Matroid.Representation.StandardRep
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Matroid.Uniform

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix


namespace Matroid

section Minor

/-- Contracting a set preserves representability. -/
@[simps!] def Rep.contract (v : M.Rep 𝔽 W) (C : Set α) :
    (M ／ C).Rep 𝔽 (W ⧸ (span 𝔽 (v '' C))) where
  to_fun := Submodule.mkQ _ ∘ v
  valid' := by
    intro J
    obtain ⟨I,hI⟩ := M.exists_basis' C
    by_cases hCJ : Disjoint C J
    · rw [hI.contract_indep_iff, and_iff_left hCJ, ← v.span_closure_congr hI.closure_eq_closure,
        (v.onIndep hI.indep).quotient_iff_union (hCJ.mono_left hI.subset), ← v.indep_iff_restrict,
        union_comm]
    refine iff_of_false (fun hi ↦ hCJ (subset_diff.1 hi.subset_ground).2.symm) fun hli ↦ ?_
    obtain ⟨e, heC, heJ⟩ := not_disjoint_iff.1 hCJ
    exact hli.ne_zero ⟨e, heJ⟩ <| by simpa using subset_span (mem_image_of_mem v heC)

@[simps!] noncomputable def Rep.delete (v : M.Rep 𝔽 W) (D : Set α) : (M ＼ D).Rep 𝔽 W :=
  v.restrict (M.E \ D)

lemma Representable.contract (hM : M.Representable 𝔽) {C : Set α} : (M ／ C).Representable 𝔽 :=
  (hM.some.contract C).representable

lemma Representable.delete (hM : M.Representable 𝔽) {D : Set α} : (M ＼ D).Representable 𝔽 :=
  (hM.some.delete D).representable

lemma Representable.restrict (hM : M.Representable 𝔽) {R : Set α} : (M ↾ R).Representable 𝔽 :=
  (hM.some.restrict R).representable

lemma Representable.minor {M N : Matroid α} (hM : M.Representable 𝔽) (hNM : N ≤m M) :
    N.Representable 𝔽 := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact hM.contract.delete

lemma Representable.isoMinor {M : Matroid α} {N : Matroid β} (hM : M.Representable 𝔽)
    (hNM : N ≤i M) : N.Representable 𝔽 :=
  let ⟨_, hM₀, i, _⟩  := hNM.exists_iso
  (hM.minor hM₀).iso i.symm

end Minor

variable {𝔽 : Type*} [Field 𝔽]

lemma Representable.encard_le_of_simple [FiniteRk M] [Simple M] (h : M.Representable 𝔽) :
    M.E.encard ≤ ∑ i ∈ Finset.range (M.rank), (ENat.card 𝔽)^i := by
  classical
  -- If `M` has rank at most `1`, this is trivial.
  obtain hle | hlt := le_or_lt M.eRank 1
  · obtain ⟨E, rfl⟩ := M.eq_unifOn_of_eRank_le_one hle
    have hE := unifOn_simple_iff.1 (by assumption)
    replace hE := show E.Subsingleton by simpa using hE
    obtain rfl | ⟨e, rfl⟩ := hE.eq_empty_or_singleton <;>
    simp [rank]
  have hr : 1 < M.rank := by rwa [← Nat.cast_lt (α := ℕ∞), cast_rank_eq]
  -- If `𝔽` is infinite, this is trivial, because the RHS is infinite.
  obtain hinf | hfin := (finite_or_infinite 𝔽).symm
  · refine le_trans ?_ (CanonicallyOrderedAddCommMonoid.single_le_sum (i := 1) (by simpa))
    simp [ENat.card_eq_top_of_infinite (α := 𝔽)]
  /- Otherwise `v` gives an injection from `M.E` to a finite projective space with
  known cardinality, giving the upper bound on `M.E.encard`. -/

  have : Nonempty (Fin M.rank) := ⟨1, hr⟩
  obtain ⟨v, -⟩ := h.exists_fin_rep
  rw [← v.projectivization_injOn.encard_image]
  refine (encard_le_card (subset_univ _)).trans ?_
  simp_rw [encard_univ, ENat.card_eq_coe_natCard]
  norm_cast
  rw [Projectivization.card_of_finrank]
  simp

section Uniform

lemma Representable.encard_le_of_unifOn_two (h : (unifOn E 2).Representable 𝔽) :
    E.encard ≤ ENat.card 𝔽 + 1 := by
  obtain hlt | hle := lt_or_le E.encard (2 : ℕ)
  · exact (show E.encard ≤ 1 from Order.le_of_lt_add_one hlt).trans (by simp)
  convert h.encard_le_of_simple
  simp [unifOn_rank_eq hle]

lemma Representable.encard_le_of_unif_two {a : ℕ} (h : (unif 2 a).Representable 𝔽) :
    a ≤ ENat.card 𝔽 + 1 :=  by
  simpa using h.encard_le_of_unifOn_two

@[simp] lemma removeLoops_representable_iff :
    M.removeLoops.Representable 𝔽 ↔ M.Representable 𝔽 := by
  refine ⟨fun ⟨v⟩ ↦ ?_, fun ⟨v⟩ ↦ ?_⟩
  · rw [M.eq_restrict_removeLoops]
    exact (v.restrict M.E).representable
  rw [removeLoops_eq_restr]
  exact (v.restrict _).representable

lemma Representable.noUniformMinor [Fintype 𝔽] (h : M.Representable 𝔽) :
    M.NoUniformMinor 2 (Fintype.card 𝔽 + 2) := by
  by_contra hcon
  obtain ⟨hm⟩ := not_noUniformMinor_iff.1 hcon
  have hcon := (h.isoMinor hm).encard_le_of_unif_two
  simp only [Nat.cast_add, Nat.cast_ofNat, ENat.card_eq_coe_fintype_card] at hcon
  rw [show (2 :ℕ∞) = 1 + 1 from rfl, ← add_assoc, ENat.add_one_le_iff] at hcon
  · simp at hcon
  simp only [WithTop.add_ne_top, ne_eq, WithTop.one_ne_top, not_false_eq_true, and_true]
  exact ne_of_beq_false rfl




/- A uniform matroid on at most `|𝔽|+1` elements is `𝔽`-representable -/
-- lemma uniform_rep_of_le {a b : ℕ} {𝔽 : Type*} [Field 𝔽] (hb : b ≤ encard (univ : Set 𝔽) + 1) :
--     Representable (unif a b) 𝔽 := by
--   have hinj : Nonempty (Fin b ↪ (Option 𝔽))
--   · refine ⟨Embedding.trans (Nonempty.some ?_) (Equiv.Set.univ (Option 𝔽)).toEmbedding⟩
--     rw [Fin.nonempty_embedding_iff_le_encard]
--     convert hb
--     rw [encard_univ, PartENat.card_option, encard_univ]
--     convert PartENat.withTopAddEquiv.map_add (PartENat.card 𝔽) 1
--     exact (PartENat.withTopEquiv_natCast 1).symm
--   obtain ⟨i,hi⟩ := hinj
--   set A := Matrix.rectProjVandermonde i a
--   exact IsRep.representable
--     (fun I ↦ by rw [Matrix.rectProjVandermonde_rowSet_linearIndependent_iff hi, unif_indep_iff])

end Uniform

/-
classical
    intro J
    obtain ⟨I,hI⟩ := M.exists_basis' C
    convert linearIndependent_comp_subtype.symm
    simp_rw [← LinearMap.map_finsupp_linearCombination, mkQ_apply, Quotient.mk_eq_zero,
      hI.contract_indep_iff, ← v.span_closure_congr hI.closure_eq_closure,
      Finsupp.mem_span_image_iff_linearCombination, v.indep_iff, linearIndependent_comp_subtype]
    refine ⟨fun ⟨h, hdj⟩ c hc ⟨c', hc'I, hc'c⟩ ↦ ?_, fun h ↦ ?_⟩
    · have hsupp : c + (-c') ∈ Finsupp.supported 𝔽 𝔽 (J ∪ I) := sorry
      obtain rfl : c = c' := by
        simpa [add_eq_zero_iff_eq_neg] using h (c + (-c')) hsupp (by simp [hc'c])
      simpa [(hdj.symm.mono_right hI.subset).inter_eq] using subset_inter hc hc'I
    · have hdj :
      let cI := ((Finsupp.restrictDom _ 𝔽 I) c)
      let cJ := ((Finsupp.restrictDom _ 𝔽 J) c)
      specialize h cJ.1 cJ.2 ⟨- cI.1, by simp, ?_⟩
      -- · rw [map_neg, eq_comm, ← add_eq_zero_iff_eq_neg, ← LinearMap.map_add]
      --   convert hc0
      --   sorry








      -- rw [← LinearMap.map_finsupp_linearCombination, mkQ_apply, Quotient.mk_eq_zero,
      --   Finsupp.mem_span_image_iff_linearCombination] at hc0
      -- obtain ⟨c', hc'supp, hc'⟩ := hc0
      -- rw [v.indep_iff, linearIndependent_comp_subtype] at h
      -- have hsupp : c - c' ∈ Finsupp.supported 𝔽 𝔽 (J ∪ I)
      -- · rw [Finsupp.mem_supported'] at hc'supp hc ⊢
      --   simp only [mem_union, not_or, Finsupp.coe_sub, Pi.sub_apply, and_imp]
      --   exact fun x hxI hxJ ↦ by simp [hc'supp x hxJ, hc x hxI]

      -- obtain rfl : c = c' := by simpa [sub_eq_zero] using h.1 (c - c') hsupp (by simp [hc'])
      -- simpa [(h.2.symm.mono_right hI.subset).inter_eq] using subset_inter hc hc'supp





      -- rw [Finsupp.linearCombination_comp] at hc0

-/
