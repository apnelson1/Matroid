import Matroid.Representation.StandardRep
import Matroid.Uniform

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [Field 𝔽]
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

lemma Representable.minor {M N : Matroid α} (hM : M.Representable 𝔽) (hNM : N ≤m M) :
    N.Representable 𝔽 := by
  rw [minor_iff_exists_contract_delete] at hNM
  obtain ⟨C, D, rfl⟩ := hNM
  exact ((hM.some.contract C).delete D).representable

end Minor

section Simple

lemma Rep.eq_zero_iff (v : M.Rep 𝔽 W) (e : α) (he : e ∈ M.E := by aesop_mat) :
    v e = 0 ↔ M.Loop e := by
  rw [← singleton_not_indep he, v.indep_iff, linearIndependent_unique_iff]
  simp

lemma Rep.eq_zero_of_loop (v : M.Rep 𝔽 W) (h : M.Loop e) : v e = 0 :=
  (v.eq_zero_iff e).2 h

lemma Rep.ne_zero_of_nonloop (v : M.Rep 𝔽 W) (h : M.Nonloop e) : v e ≠ 0 := by
  rw [Ne, v.eq_zero_iff e]; exact h.not_loop

lemma Rep.ne_zero_iff_nonloop (v : M.Rep 𝔽 W) (e : α) (he : e ∈ M.E := by aesop_mat) :
    v e ≠ 0 ↔ M.Nonloop e :=
  ⟨fun h ↦ by rwa [← not_loop_iff, ← v.eq_zero_iff e], v.ne_zero_of_nonloop⟩

lemma Rep.loopless_iff (v : M.Rep 𝔽 W) : M.Loopless ↔ ∀ e ∈ M.E, v e ≠ 0 := by
  rw [loopless_iff_forall_nonloop]
  exact ⟨fun h e he ↦ (v.ne_zero_iff_nonloop e he).2 (h e he),
    fun h e he ↦ (v.ne_zero_iff_nonloop e he).1 (h e he)⟩

@[simp] lemma removeLoops_representable_iff :
    M.removeLoops.Representable 𝔽 ↔ M.Representable 𝔽 := by
  refine ⟨fun ⟨v⟩ ↦ ?_, fun ⟨v⟩ ↦ ?_⟩
  · rw [M.eq_restrict_removeLoops]
    exact (v.restrict M.E).representable
  rw [removeLoops_eq_restr]
  exact (v.restrict _).representable

lemma Rep.parallel_iff (v : M.Rep 𝔽 W) (he : M.Nonloop e) :
    M.Parallel e f ↔ ∃ (c : 𝔽), c ≠ 0 ∧ v e = c • v f := by
  obtain (hfE | hfE) := em' (f ∈ M.E)
  · refine iff_of_false (fun h ↦ hfE h.mem_ground_right) ?_
    simp [v.eq_zero_of_not_mem_ground hfE, iff_true_intro (v.ne_zero_of_nonloop he)]
  obtain (hf | hf) := M.loop_or_nonloop f
  · refine iff_of_false (fun h ↦ h.nonloop_right.not_loop hf) ?_
    simp [v.eq_zero_of_loop hf, iff_true_intro (v.ne_zero_of_nonloop he)]

  obtain (rfl | hef) := eq_or_ne e f
  · exact iff_of_true hf.parallel_self ⟨1, one_ne_zero, (one_smul _ _).symm⟩

  rw [he.parallel_iff_dep hf hef, ← not_indep_iff, v.indep_iff_restrict, not_iff_comm,
    linearIndependent_restrict_pair_iff _ hef (v.ne_zero_of_nonloop he)]
  simp only [ne_eq, not_exists, not_and]
  refine ⟨fun h c h' ↦ ?_, fun h c hc h_eq ↦
    h c⁻¹ (by rw [h_eq, smul_smul, inv_mul_cancel₀ hc, one_smul])⟩
  have hc : c ≠ 0 := by rintro rfl; exact v.ne_zero_of_nonloop hf (by simp [← h'])
  exact h c⁻¹ (by simpa) <| by rw [← h', smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma Rep.simple_iff [RkPos M] (v : M.Rep 𝔽 W) :
    M.Simple ↔ ∀ {e f} (_ : e ∈ M.E) (_ : f ∈ M.E) (c : 𝔽), v e = c • (v f) → e = f := by
  simp_rw [simple_iff_loopless_eq_of_parallel_forall, v.loopless_iff]
  refine ⟨fun ⟨h0,h1⟩ e f he _ c h_eq ↦ h1 e f ?_, fun h ↦ ⟨fun e he h0 ↦ ?_, fun e f hef ↦ ?_⟩⟩
  · refine (v.parallel_iff ?_).2 ⟨c, ?_, h_eq⟩
    · rw [← v.ne_zero_iff_nonloop e]; exact h0 _ he
    rintro rfl
    exact h0 e he <| by simp [h_eq]
  · obtain ⟨f, hf⟩ := M.exists_nonloop
    obtain rfl := h he hf.mem_ground 0 (by simp [h0])
    exact v.ne_zero_of_nonloop hf h0
  obtain ⟨c,-,h_eq⟩ := (v.parallel_iff hef.symm.nonloop_right).1 hef
  exact h (by aesop_mat) (by aesop_mat) c h_eq

lemma Rep.injOn_of_simple (v : M.Rep 𝔽 W) (h : M.Simple) : InjOn v M.E := by
  obtain (hl | hpos) := M.eq_loopyOn_or_rkPos
  · rw [simple_iff_loopless_eq_of_parallel_forall, hl, loopyOn_loopless_iff] at h
    simp [h.1]
  exact fun e he f hf h_eq ↦ (v.simple_iff.1 h) he hf 1 <| by rwa [one_smul]

-- @[simp] lemma simplification_representable_iff :
--     M.simplification.Representable 𝔽 ↔ M.Representable 𝔽 := by
--   obtain ⟨c, hc, hM⟩ := M.exists_simplification_eq_wrt
--   rw [hM]
--   refine ⟨fun ⟨v⟩ ↦ ?_, fun h ↦ h.minor (simplificationWrt_restriction hc).minor⟩
--   rw [← removeLoops_representable_iff, ← preimage_simplificationWrt M hc]
--   exact (v.preimage _).representable

end Simple
section Uniform

lemma Representable.encard_le_of_line (h : (unifOn E 2).Representable 𝔽) :
    E.encard ≤ ENat.card 𝔽 + 1 := by
  obtain ⟨B, hB⟩ := (unifOn E 2).exists_base
  obtain hlt | hle := lt_or_le E.encard 2
  · rw [← ENat.add_one_le_iff (hlt.trans_le le_top).ne, ← one_add_one_eq_two,
      WithTop.add_le_add_iff_right (by simp)] at hlt
    exact hlt.trans (by simp)
  have h_ex := h.exists_fin_rep_of_eq (n := 2)
  rw [rank, unifOn_eRank_eq, min_eq_right (by simpa using hle), Nat.cast_ofNat, ENat.toNat_ofNat,
    imp_iff_right rfl] at h_ex
  obtain ⟨v, hb⟩ := h_ex
  have hsimp := unifOn_simple E (k := 0)
  have : (unifOn E 2).RkPos  := sorry
  rw [zero_add, v.simple_iff] at hsimp
  simp at hsimp




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
