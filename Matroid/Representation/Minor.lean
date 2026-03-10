import Matroid.Representation.StandardRep
import Matroid.Uniform

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Submodule


namespace Matroid

section Minor

set_option backward.isDefEq.respectTransparency false in
/-- Contracting a set preserves representability. -/
@[simps!] def Rep.contract (v : M.Rep 𝔽 W) (C : Set α) :
    (M ／ C).Rep 𝔽 (W ⧸ (span 𝔽 (v '' C))) where
  to_fun := mkQ _ ∘ v
  indep_iff' J := by
    obtain ⟨I,hI⟩ := M.exists_isBasis' C
    by_cases hCJ : Disjoint C J
    · rw [hI.contract_indep_iff, and_iff_left hCJ, ← v.span_closure_congr hI.closure_eq_closure,
        (v.onIndep hI.indep).quotient_iff_union (hCJ.mono_left hI.subset), v.indep_iff, union_comm]
    obtain ⟨e, heC, heJ⟩ := not_disjoint_iff.1 hCJ
    refine iff_of_false (fun hi ↦ hCJ (subset_diff.1 hi.subset_ground).2.symm)
      fun hli ↦ hli.ne_zero heJ <| by simpa using subset_span (mem_image_of_mem v heC)

@[simps!] noncomputable def Rep.delete (v : M.Rep 𝔽 W) (D : Set α) : (M ＼ D).Rep 𝔽 W :=
  v.restrict (M.E \ D)

lemma Representable.contract (hM : M.Representable 𝔽) {C : Set α} : (M ／ C).Representable 𝔽 :=
  (hM.some.contract C).representable

lemma Representable.delete (hM : M.Representable 𝔽) {D : Set α} : (M ＼ D).Representable 𝔽 :=
  (hM.some.delete D).representable

lemma Representable.restrict (hM : M.Representable 𝔽) {R : Set α} : (M ↾ R).Representable 𝔽 :=
  (hM.some.restrict R).representable

lemma Representable.of_isMinor {M N : Matroid α} (hM : M.Representable 𝔽) (hNM : N ≤m M) :
    N.Representable 𝔽 := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact hM.contract.delete

lemma Representable.isoMinor {M : Matroid α} {N : Matroid β} (hM : M.Representable 𝔽)
    (hNM : N ≤i M) : N.Representable 𝔽 :=
  let ⟨_, hM₀, i, _⟩  := hNM.exists_iso
  (hM.of_isMinor hM₀).iso i.symm

end Minor

variable {𝔽 : Type*} [Field 𝔽]






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



/-
classical
    intro J
    obtain ⟨I,hI⟩ := M.exists_isBasis' C
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
