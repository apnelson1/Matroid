import Matroid.Uniform
import Matroid.Connectivity.Skew



open Set

@[simp] lemma Set.diff_ssubset_left_iff {α : Type*} {s t : Set α} :
    s \ t ⊂ s ↔ (s ∩ t).Nonempty := by
  rw [ssubset_iff_subset_ne, and_iff_right diff_subset, Ne, sdiff_eq_left,
    disjoint_iff_inter_eq_empty, nonempty_iff_ne_empty]

@[simp] lemma Set.inter_ssubset_right_iff {α : Type*} {s t : Set α} :
    s ∩ t ⊂ t ↔ ¬ (t ⊆ s) := by
  rw [ssubset_iff_subset_ne, and_iff_right inter_subset_right, Ne, inter_eq_right]

@[simp] lemma Set.inter_ssubset_left_iff {α : Type*} {s t : Set α} :
    s ∩ t ⊂ s ↔ ¬ (s ⊆ t) := by
  rw [ssubset_iff_subset_ne, and_iff_right inter_subset_left, Ne, inter_eq_left]

lemma Set.Finite.encard_lt_encard' {α : Type*} {s t : Set α} (hs : s.Finite) (hst : s ⊂ t) :
    s.encard < t.encard := by
  obtain hfin | hinf := t.finite_or_infinite
  · exact hfin.encard_lt_encard hst
  rwa [hinf.encard_eq, encard_lt_top_iff]


@[simp] lemma ENat.natCast_odd_iff (n : ℕ) : Odd (n : ℕ∞) ↔ Odd n := by
  refine ⟨fun ⟨k, h⟩ ↦ ?_, fun ⟨k, h⟩ ↦ ⟨k, by simp [h]⟩⟩
  lift k to ℕ using (by rintro rfl; simp at h)
  exact ⟨k, by norm_cast at h⟩

@[simp] lemma ENat.natCast_even_iff (n : ℕ) : Even (n : ℕ∞) ↔ Even n := by
  refine ⟨fun ⟨k, h⟩ ↦ ?_, fun ⟨k, h⟩ ↦ ⟨k, by simp [h]⟩⟩
  lift k to ℕ using (by rintro rfl; simp at h)
  exact ⟨k, by norm_cast at h⟩


namespace Matroid



variable {α : Type*} {M : Matroid α} {C K X Y B I J : Set α}

def Binary (M : Matroid α) := ∀ C K, M.Circuit C → M.Cocircuit K → ∀ (h : (C ∩ K).Finite),
  Even h.toFinset.card

lemma exists_of_not_binary (hM : ¬ M.Binary) : ∃ (C : Finset α) (X Y : Set α),
    (C : Set α) ⊆ M.E ∧ X ⊆ M.E ∧ Y ⊆ M.E ∧
    M.Circuit (C ∪ X) ∧ M.Cocircuit (C ∪ Y) ∧ Disjoint X C ∧ Disjoint Y C ∧ Disjoint X Y ∧
    Odd C.card ∧ 3 ≤ C.card ∧ Finset.Nonempty C := by
  simp only [Binary, not_forall, Classical.not_imp, Nat.not_even_iff_odd, exists_and_left] at hM
  obtain ⟨Cc, Ck, hCc, hCk, hfin, h_odd⟩ := hM
  refine ⟨hfin.toFinset, Cc \ Ck, Ck \ Cc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [inter_subset_left.trans hCc.subset_ground]
  · simp [diff_subset.trans hCc.subset_ground]
  · simp [diff_subset.trans hCk.subset_ground]
  · simpa
  · simpa [inter_comm Cc]
  · simp [disjoint_sdiff_left.mono_right inter_subset_right]
  · simp [disjoint_sdiff_left.mono_right inter_subset_left]
  · exact disjoint_sdiff_sdiff
  refine ⟨h_odd, ?_⟩
  obtain ⟨rfl | k, h : hfin.toFinset.card = _⟩ := h_odd
  · exfalso
    obtain ⟨a, ha⟩ : ∃ a, hfin.toFinset = {a} := by simpa [Finset.card_eq_one] using h
    apply_fun Finset.toSet at ha
    exact (hCc.inter_cocircuit_ne_singleton hCk (by simpa using ha))
  rw [← Finset.one_le_card, h]
  constructor <;> linarith

lemma Binary.dual (hM : M.Binary) : M✶.Binary := by
  intro C K hC hK h
  rw [inter_comm] at h
  convert hM K C (by simpa using hK.circuit) (by simpa using hC.cocircuit) h using 3
  rw [inter_comm]


lemma Binary.minor {N M : Matroid α} (hM : M.Binary) (hNM : N ≤m M) : N.Binary := by
  suffices aux : ∀ ⦃M : Matroid α⦄ ⦃S : Set α⦄, M.Spanning S → M.Binary → (M ↾ S).Binary
  · obtain ⟨I, R, hI, hIR, hR, rfl⟩ := hNM.exists_eq_contract_spanning_restrict
    apply aux hR
    rw [← dual_delete_dual_eq_contract]
    apply (aux _ hM.dual).dual
    rwa [← coindep_iff_compl_spanning, dual_coindep_iff]

  clear! N M
  intro M S hS hM C D hC hD h
  rw [restrict_circuit_iff] at hC
  have hh := hD.compl_hyperplane
  rw [restrict_ground_eq, hS.hyperplane_restrict_iff] at hh

  suffices h_eq : C ∩ D = C ∩ (M.E \ M.closure (S \ D))
  · convert hM C _ hC.1 hh.1.compl_cocircuit (by rwa [← h_eq]) using 3

  rw [diff_eq, ← inter_assoc, inter_eq_self_of_subset_left hC.1.subset_ground,
    ← inter_eq_self_of_subset_left hC.2, inter_assoc, inter_assoc, ← diff_eq,
    ← diff_self_inter, inter_comm S (M.closure _), ← hh.2]
  simp



  -- have  := hD.compl_hyperplane

  -- suffices ∀ (M : Matroid α) X, M.Coindep X → M.Binary → (M ＼ X).Binary
  -- · sorry
  -- sorry


-- theorem odd_circuit_cocircuit_foo {C : Finset α} (hCc : M.Circuit C) (hCk : M.Cocircuit C)
--     (hsp : M.Spanning C) (h_odd : Odd C.card) (h_minor : IsEmpty (unif 2 4 ≤i M)) :
--     ∃ (e : α) (C₀ : Finset α), (e ∈ M.E \ C) ∧ C₀ ⊆ C ∧ (M ／ e).Circuit C₀ := by

--   classical

--   have hfin : FiniteRk M
--   · rw [finiteRk_iff, ← hsp.er_eq, Ne, ← WithTop.add_right_cancel_iff (a := 1) (by simp),
--       hCc.er_add_one_eq, top_add, encard_eq_top_iff, not_infinite]
--     exact C.finite_toSet

--   have hcard : 3 ≤ C.card
--   · obtain ⟨(rfl | k), hk⟩ := h_odd
--     · obtain ⟨a, rfl⟩ : ∃ a, C = {a} := by simpa [Finset.card_eq_one, mul_zero, zero_add] using hk
--       simpa using hCc.inter_cocircuit_ne_singleton hCk (e := a)
--     linarith

--   have hr : 2 ≤ M.r C
--   · rw [← hCc.r_add_one_eq] at hcard
--     linarith

--   obtain ⟨e, he, heC⟩ : ∃ e, M.Nonloop e ∧ e ∉ C := by
--     by_contra! hcon'
--     have hr' : M.r (M.E \ C) = 0 := by
--       rw [r_eq_zero_iff diff_subset]
--       intro e he
--       rw [← loop_iff_mem_closure_empty, ← not_nonloop_iff]
--       exact fun hne ↦ he.2 (by simpa using hcon' e hne)
--     have hr0 := hCk.compl_hyperplane.covBy.er_eq
--     rw [← cast_r_eq, ← cast_r_eq] at hr0
--     norm_cast at hr0
--     rw [hr', zero_add] at hr0
--     simpa using hr.trans <| (M.r_mono hCc.subset_ground).trans_eq hr0

--   have heE := he.mem_ground
--   set N := M ↾ (insert e C) with hN_def

--   have hNdel : N ＼ e = circuitOn C
--   · rw [hN_def, deleteElem, delete_eq_restrict, restrict_ground_eq,
--       restrict_restrict_eq _ diff_subset, insert_diff_of_mem _ (mem_singleton e),
--       diff_singleton_eq_self (by simpa), hCc.restrict_eq_circuitOn]

--   have hNcon : N✶ ／ e = unifOn C 1
--   · rw [contract_elem, ← delete_dual_eq_dual_contract, ← deleteElem, hNdel, circuitOn_dual]

--   have heN : N✶.Nonloop e
--   · rw [← not_loop_iff (mem_insert _ _), dual_loop_iff_coloop, coloop_iff_not_mem_closure_compl]
--     suffices e ∈ M.closure (↑C \ {e} ∩ insert e ↑C) by simpa [hN_def, heE]
--     rwa [inter_eq_self_of_subset_left (diff_subset.trans (subset_insert _ _)),
--       hCc.closure_diff_singleton_eq_closure, hsp.closure_eq]

--   have heNcl : N✶.closure {e} = {e}
--   · rw [subset_antisymm_iff, subset_def,
--       and_iff_left (N✶.subset_closure (X := {e}) (by simpa using heN.mem_ground))]
--     refine fun x hx ↦ by_contra fun (hne : x ≠ e) ↦ ?_
--     have hloop : (N✶ ／ e).Loop x
--     · rw [loop_iff_mem_closure_empty, contract_elem, contract_closure_eq]
--       simpa [hne]
--     have hxC : x ∈ C := by simpa [hN_def, hne] using hloop.mem_ground
--     exact hloop.not_nonloop <| by simpa [hNcon, ← indep_singleton, unifOn_indep_iff]

--   have hNer : N✶.erk = 2
--   · rw [← heN.erk_contract_add_one, hNcon, unifOn_erk_eq,
--       min_eq_right (by simpa using hCc.nonempty), show (1 : ℕ∞) + 1 = 2 from rfl]

--   have hNr : N✶.rk = 2
--   · rw [rk, hNer, ENat.toNat_ofNat]

--   have hfin' : FiniteRk N✶ := by simp [finiteRk_iff, hNer]

--   obtain ⟨_, hI⟩ := (N✶ ＼ e).exists_base
--   obtain ⟨I, rfl⟩ := hI.indep.finite.exists_finset_coe



--   have hIcard : I.card = 1 ∨ I.card = 2
--   · suffices 1 ≤ I.card ∧ I.card ≤ 2 by omega
--     rw [← ncard_coe_Finset, hI.ncard, deleteElem]
--     refine ⟨?_, (N✶.delete_rk_le {e}).trans_eq hNr⟩
--     linarith [N✶.delete_rk_add_r_ge_rk {e}, (N✶.r_le_finset_card {e}), Finset.card_singleton e]

--   rw [Finset.card_eq_one, Finset.card_eq_two] at hIcard
--   sorry
--   -- obtain ⟨a, rfl⟩ | ⟨a,b, hne, rfl⟩ := hIcard
--   -- · refine ⟨e, C, ⟨heE, heC⟩, rfl.subset, ?_⟩
  --   have h' : (N ／ e).Circuit C
  --   · rw [← dual_dual (N ／ e), ← cocircuit_def, contract_elem, contract_dual_eq_dual_delete]


  --   -- have := Finite.r_le_card N✶ {e}

    -- refine ⟨?_, ?_⟩
    -- · have := relRank_delete_eq
    -- sorry
  --   have := hI.ncard
  --   simp only [ncard_coe_Finset, deleteElem] at this
  -- -- · rw [hI.encard, deleteElem, ← contract_dual_eq_dual_delete]



lemma rank_two_foo {e : α} (hr : M.erk = 2) (hel : ¬ M.Coloop e) (he : M.Point {e})
    (hU : M.NoUniformMinor 2 4) :
    ∃ C₁ C₂, (M ＼ e).Cocircuit C₁ ∧ (M ＼ e).Cocircuit C₂ ∧ Disjoint C₁ C₂ ∧ C₁ ∪ C₂ = M.E \ {e} := by
  obtain ⟨I, hI⟩ := M.exists_basis (M.E \ {e})
  have hI' : M.Base I
  · refine hI.indep.base_of_spanning ?_
    rwa [hI.spanning_iff_spanning, ← not_not (a := M.Spanning _), ← coloop_iff_diff_nonspanning]
  have hIE := hI'.subset_ground

  -- obtain ⟨hI', -⟩ : M.Indep I ∧ _ := by simpa using hI.indep
  have hl := he.loopless_of_singleton
  have heE : e ∈ M.E := by simpa using he.subset_ground
  --   exact M.closure_subset_closure <| empty_subset _

  have hU : ∀ x ∈ (M ＼ e).E, ∃ y ∈ I, x ∈ M.closure {y}
  · by_contra! hcon
    obtain ⟨x, ⟨hxE, hne : x ≠ e⟩, hx⟩ := hcon
    have hx' : ∀ y ∈ I, M.Indep {x,y}
    · refine fun y hyI ↦ ?_
      rw [(M.toNonloop).indep.insert_indep_iff]
      exact .inl ⟨hxE, hx y hyI⟩

    set N := M ↾ (I ∪ {e, x}) with hN
    have hNM : N ≤m M := M.restrict_minor (union_subset hI'.subset_ground (pair_subset heE hxE))

    have h_unif : N = unifOn (I ∪ {e, x}) 2
    · rw [eq_unifOn_two_iff, hN, restrict_ground_eq, and_iff_right rfl, erk_restrict, ← hr,
        and_iff_right (er_le_erk _ _), simple_iff_forall_pair_indep]
      simp only [union_insert, union_singleton, restrict_ground_eq, mem_insert_iff,
        restrict_indep_iff, pair_subset_iff]
      rintro a b (rfl | rfl | haI)

      · suffices b ∈ I → M.Indep {a, b} by
          simpa (config := {contextual := true}) [or_imp, he.nonloop, he.insert_indep x hxE]
        exact fun hbI ↦ he.insert_indep b
      · simp (config := {contextual := true}) [or_imp, M.toNonloop, pair_comm _ e,
          he.insert_indep _ hxE, M.toNonloop hxE, hx' b]
      simp (config := { contextual := true }) only [haI, or_true, and_self, and_true, pair_comm a]

      rintro (rfl | rfl | hbI)
      · exact he.insert_indep a
      · exact hx' _ haI
      exact hI'.indep.subset (pair_subset hbI haI)

    have hcard : encard (I ∪ {e, x}) = 4
    · rw [encard_union_eq, hI'.encard, hr, encard_pair hne.symm]
      · rfl
      rw [← singleton_union, disjoint_union_right, and_iff_right (subset_diff.1 hI.subset).2,
        disjoint_singleton_right]
      exact fun hxI ↦ hx x hxI <| M.mem_closure_self _ hxE

    replace hU := hU.minor hNM
    rw [h_unif, show (2 : ℕ∞) = (2 : ℕ) from rfl, unifOn_noUniformMinor_iff, hcard] at hU
    simp at hU





  have foo : ∀ x ∈ I, (M ＼ e).Cocircuit (M.closure {x})
  · intro x hxI


  rw [← hI.ncard, ncard_eq_two] at hr

  obtain ⟨a, b, hab, rfl⟩ := hr


lemma foo {C : Finset α} (hCc : M.Circuit C) (hCs : M.Spanning C) (hCh : M.Hyperplane (M.E \ C))
    (hCi : M.Indep (M.E \ C)) (h_card : 3 ≤ C.card) (h_bin : M.NoUniformMinor 2 4) :
    ∃ (N : Matroid α) (C' K' : Set α) (h : C' ∩ K' ⊂ C), N ≤m M ∧ N.Circuit C' ∧ N.Cocircuit K' ∧
      ∃ (hfin' : (C' ∩ K').Finite), Odd hfin'.toFinset.card := by



  obtain ⟨f, hf⟩ : (M.E \ C).Nonempty
  · rw [nonempty_iff_ne_empty]
    intro hss
    have hle := (M.er_le_erk C).trans_eq hCh.er_add_one_eq.symm
    rw [hss, er_empty, zero_add, ← WithTop.add_le_add_iff_right (show 1 ≠ ⊤ by simp),
      hCc.er_add_one_eq] at hle
    norm_cast at hle
    linarith

  set N := M ／ ((M.E \ ↑C) \ {f}) with hN
  have hfl : ¬ N.Coloop f := sorry

  have hNr : (N ＼ f).rk = 2
  · rw [rk, deleteElem_erk_eq hfl, ← rk]
    obtain ⟨e, he, hbas⟩ := hCh.exists_insert_base_of_basis (hCi.basis_self)
    have hb' : N.Base {e, f}
    simp only [sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff, Finset.mem_coe] at he
    · rw [hN, (hCi.diff _).contract_base_iff, ← singleton_union, union_assoc, disjoint_union_left]
      simpa [hf, he.1, he.2]

    rw [← hb'.ncard, ncard_pair (by rintro rfl; exact he.2 hf)]

  have hNf : N.Flat {f}
  · rw [flat_iff_closure_self, hN, contract_closure_eq, union_diff_cancel (by simpa)]
    simpa [hCh.flat.closure]

  have hNl : N.Loopless
  · rw [loopless_iff_closure_empty, hN, contract_closure_eq, empty_union, diff_eq_empty,
      subset_diff_singleton_iff]
    nth_rw 2 [← hCh.flat.closure]
    exact ⟨M.closure_mono diff_subset, hCi.not_mem_closure_diff_of_mem hf⟩


  have hfoo := rank_two_foo (e := f) hNr hNf (h_bin.minor (contract_minor _ _))






  -- rw [spanning_iff_compl_coindep, dual_ground, dual_coindep_iff] at hCMds
  -- simp only [encard_coe_eq_coe_finsetCard] at hr

  have := hCM.cocircuit_inter_nontrivial hCMd (by simpa using hCM.nonempty)


lemma middle_foo {C : Finset α} (hCc : M.Circuit C) (hCk : M.Cocircuit C) (h_odd : Odd C.card)
    (h_binary : ¬ Nonempty (unif 2 4 ≤i M)) : ∃ (N : Matroid α) (C' K' : Set α) (h : C' ∩ K' ⊂ C),
    N ≤m M ∧ N.Circuit C' ∧ N.Cocircuit K' ∧
      ∃ (hfin' : (C' ∩ K').Finite), Odd hfin'.toFinset.card := by
  by_contra! hcon
  have hh := hCk.compl_hyperplane

  obtain ⟨I, hI⟩ := M.exists_basis (M.E \ C) diff_subset

  have hIC : Disjoint I C := (subset_diff.1 hI.subset).2
  have hICE : I ∪ C ⊆ M.E := union_subset hI.indep.subset_ground hCc.subset_ground

  set N := M ↾ (I ∪ C) with hN_def

  have hNM : N ≤m M := restrict_minor _ hICE

  have hIi : N.Indep I := by simp [hN_def, hI.indep]

  have hIs : M.Spanning (I ∪ C)
  · rw [spanning_iff_closure_eq, ← closure_union_closure_left_eq, hI.closure_eq_closure,
      closure_union_closure_left_eq, diff_union_of_subset hCc.subset_ground, closure_ground]

  have hIhp : N.Hyperplane I
  · rw [hN_def, hIs.hyperplane_restrict_iff, hI.closure_eq_closure,
      hh.flat.closure, and_iff_right hh, diff_eq, inter_right_comm,
      inter_eq_self_of_subset_right hICE, ← diff_eq, union_diff_right, hIC.sdiff_eq_left]

  have hNCk : N.Cocircuit C
  · convert hIhp.compl_cocircuit
    simp [hN_def, hIC.sdiff_eq_right]

  have hNCc : N.Circuit C
  · rwa [hN_def, restrict_circuit_iff, and_iff_left subset_union_right]

  obtain ⟨f, hfI, hf⟩ : ∃ f ∈ I, ¬ N.Coloop f
  · sorry

  obtain ⟨e, heC⟩ := hCc.nonempty
  have heI : e ∉ I := fun heI ↦ (hI.subset heI).2 heC

  have := rank_two_foo (M := N ／ (I \ {f})) (e := f) ?_ ?_ ?_ ?_
  · sorry
  · have hb' : (N ／ (I \ {f})).Base {e,f}
    · rw [(hIi.diff _).contract_base_iff, ← singleton_union, union_assoc, disjoint_union_left]
      simpa [heI, hfI] using hIhp.insert_base_of_basis hIi.basis_self <|
        by simp [heI, hNCc.subset_ground heC]
    rw [rk, ← hb'.encard, encard_pair (by rintro rfl; contradiction)]
    rfl
  · rw [loopless_iff_closure_empty, contract_closure_eq, empty_union, diff_eq_empty,
      subset_diff_singleton_iff, and_iff_left (hIi.not_mem_closure_diff_of_mem hfI)]
    exact (N.closure_subset_closure diff_subset).trans hIhp.flat.closure.subset
  · rw [flat_iff_closure_self, contract_closure_eq]
    simp [hfI, hIhp.flat.closure]
  contrapose! h_binary
  exact ⟨h_binary.some.trans_minor ((contract_minor _ _).trans hNM)⟩
  -- refine isEmpty_iff.2 fun e ↦ ⟨







--   set N₁ := N ↾ (I ∪ C) with hN₁_def

--   have hN₁M : N₁ ≤m M := (N.restrict_minor hsp.subset_ground).trans hNM

--   have hhp : N₁.Hyperplane I
--   · have h1 := hCk.compl_hyperplane.inter_hyperplane_spanning_restrict hsp
--     rwa [diff_eq, inter_right_comm, inter_eq_self_of_subset_right
--       (union_subset hI.indep.subset_ground hCc.subset_ground), union_inter_distrib_right,
--       inter_compl_self, union_empty, ← diff_eq, ← diff_eq, hIC.sdiff_eq_left,
--       hI.closure_eq_closure, imp_iff_right (N.subset_closure _ diff_subset)] at h1




lemma top_foo {M : Matroid α} {C K : Set α} (hC : M.Circuit C) (hK : M.Cocircuit K)
    (hfin : (C ∩ K).Finite) (h_odd : Odd hfin.toFinset.card) : Nonempty (unif 2 4 ≤i M) := by
  have hne : (C ∩ K).Nonempty
  · rw [nonempty_iff_ne_empty, Ne, ← encard_eq_zero, hfin.encard_eq_coe_toFinset_card,
      Nat.cast_eq_zero]
    intro h
    simp [h] at h_odd

  by_contra hcon
  set N := M ／ (C \ K) ＼ (K \ C) with hN_def
  have hNM : N ≤m M := contract_delete_minor _ _ _
  have hN : IsEmpty (unif 2 4 ≤i N) := isEmpty_iff.2 fun e ↦ hcon ⟨e.trans_minor hNM⟩

  have hNC : N.Circuit (C ∩ K)
  · rw [hN_def, delete_circuit_iff, and_iff_left (disjoint_sdiff_right.mono_left inter_subset_left)]
    simpa using hC.contract_circuit (C := C \ K) (by simpa)

  have hNK : N.Cocircuit (C ∩ K)
  · rw [inter_comm, cocircuit_def, hN_def, delete_dual_eq_dual_contract,
      contract_dual_eq_dual_delete, ← contract_delete_comm _ disjoint_sdiff_sdiff,
      delete_circuit_iff, and_iff_left (disjoint_sdiff_right.mono_left inter_subset_left)]
    simpa using hK.contract_circuit (C := K \ C) (by simpa [inter_comm])

  obtain ⟨M', C', K', hssu, hM', hC', hK', hfin', h_odd'⟩ :=
    middle_foo (C := hfin.toFinset) (by simpa) (by simpa) (by simpa) hN

  have hlt : (C' ∩ K').encard < (C ∩ K).encard := hfin.encard_lt_encard <| by simpa using hssu

  exact hcon <| ⟨(top_foo hC' hK' hfin' h_odd').some.trans_minor (hM'.trans hNM)⟩
termination_by (C ∩ K).encard



  -- rwa [show C ∩ K = hfin.toFinset by simp, encard_coe_eq_coe_finsetCard,
  --   ENat.natCast_odd_iff] at h_odd





-- noncomputable def inductionSig (A B : Set α) : ℕ∞ × ℕ∞ × ℕ∞ :=
--   ⟨(A ∩ B).encard, A.encard, B.encard⟩



-- lemma foo_one {M : Matroid α} {C K : Set α} (hC : M.Circuit C) (hK : M.Cocircuit K)
--     (hfin : (C ∩ K).Finite) (h_odd : Odd hfin.toFinset.card) : Nonempty (unif 2 4 ≤i M) := by

--   have hnonempty : (C ∩ K).Nonempty := sorry

--   by_contra hcon

--   have hCK : C ⊆ K
--   · contrapose! hcon
--     have hlt : inductionSig (C ∩ K) K < inductionSig C K
--     · simp [inductionSig, inter_assoc, hfin.encard_lt_encard' (t := C) <| by simpa,
--         encard_mono diff_subset]

--     have h_minor := foo_one (M := M ／ (C \ K)) (C := C ∩ K) (K := K) ?_ ?_ ?_ ?_
--     · exact ⟨h_minor.some.trans_minor (contract_minor _ _)⟩
--     · simpa using hC.contract_circuit (C := C \ K) (by simpa)
--     · rwa [cocircuit_def, contract_dual_eq_dual_delete, delete_circuit_iff,
--         and_iff_left disjoint_sdiff_right]
--     · simpa [inter_assoc]
--     convert h_odd using 3
--     simp [inter_assoc]

--   have hKC : K ⊆ C
--   · contrapose! hcon
--     have hlt : inductionSig (M ＼ (K \ C)) C (C ∩ K) < inductionSig M C K
--     · simp [inductionSig, ← inter_assoc, hfin.encard_lt_encard' (t := K) <| by simpa,
--         encard_mono diff_subset]
--     have h_minor := foo_one (M := M ＼ (K \ C)) (C := C) (K := C ∩ K) ?_ ?_ ?_ ?_
--     · exact ⟨h_minor.some.trans_minor (delete_minor _ _)⟩
--     · rwa [delete_circuit_iff, and_iff_left disjoint_sdiff_right]
--     · rw [inter_comm, cocircuit_def, delete_dual_eq_dual_contract]
--       simpa using hK.circuit.contract_circuit (C := (K \ C)) (by simpa [inter_comm])
--     · simpa [← inter_assoc]
--     convert h_odd using 3
--     simp [← inter_assoc]

--   obtain rfl := hCK.antisymm hKC
--   rw [inter_self] at hfin
--   set C₀ := (show C.Finite by simpa using hfin).toFinset
--   rw [show C = (C₀ : Set α) by simp [C₀]] at *

--   have hcard : Odd C₀.card := by convert h_odd; simp

--   clear hnonempty hCK hKC




--   sorry


-- termination_by M.inductionSig C K



--   by_contra hcon
--   have IH : ∀ M₀, M₀ ≤m M → M₀✶.erk < M.erk → M₀.Binary
--   · refine fun M₀ hm hr' ↦ by_contra fun hnonbin ↦ hcon ?_
--     obtain ⟨e⟩ := foo_one (M := M₀) hnonbin
--     exact ⟨e.trans_minor hm⟩

--   obtain ⟨C, X, Y, hCE, hXE, hYE, hX, hY, hXC, hYC, hXY, h_odd, h3, hne⟩ := exists_of_not_binary hM
--   set N := M ／ X ＼ Y with hN_def
--   have hNM : N ≤m M := contract_delete_minor _ _ _

--   have hssu : ∀ {Z : Set α}, Disjoint Z C → Z ⊂ C ∪ Z
--   · refine fun {Z} hZC ↦ subset_union_right.ssubset_of_ne ?_
--     rwa [Ne, eq_comm, union_eq_right, ← diff_eq_empty, hZC.sdiff_eq_right, ← Ne,
--       ← nonempty_iff_ne_empty, Finset.coe_nonempty]

--   have hCc : N.Circuit C
--   · rw [hN_def, ← circuit_iff_delete_of_disjoint hYC.symm]
--     simpa [hXC.sdiff_eq_right] using hX.contract_circuit (hssu hXC)

--   have hCk : N.Cocircuit C
--   · rw [hN_def, cocircuit_def, delete_dual_eq_dual_contract, contract_dual_eq_dual_delete,
--       ← contract_delete_comm _ hXY.symm, ← circuit_iff_delete_of_disjoint hXC.symm]
--     simpa [hYC.sdiff_eq_right] using hY.circuit.contract_circuit (hssu hYC)

--   obtain ⟨I, hI⟩ := N.exists_basis (N.E \ C) diff_subset

--   have hIC : Disjoint I C := (subset_diff.1 hI.subset).2

--   have hsp : N.Spanning (I ∪ C)
--   · obtain ⟨e, he, heB⟩ := hCk.compl_hyperplane.exists_insert_base_of_basis hI
--     simp only [sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff, Finset.mem_coe] at he
--     exact heB.spanning.superset (insert_subset (.inr he.2) subset_union_left)
--       (union_subset hI.indep.subset_ground hCc.subset_ground)

--   set N₁ := N ↾ (I ∪ C) with hN₁_def

--   have hN₁M : N₁ ≤m M := (N.restrict_minor hsp.subset_ground).trans hNM

--   have hhp : N₁.Hyperplane I
--   · have h1 := hCk.compl_hyperplane.inter_hyperplane_spanning_restrict hsp
--     rwa [diff_eq, inter_right_comm, inter_eq_self_of_subset_right
--       (union_subset hI.indep.subset_ground hCc.subset_ground), union_inter_distrib_right,
--       inter_compl_self, union_empty, ← diff_eq, ← diff_eq, hIC.sdiff_eq_left,
--       hI.closure_eq_closure, imp_iff_right (N.subset_closure _ diff_subset)] at h1

--   have hN₁Cc : N₁.Circuit C := hCc.circuit_restrict_of_subset subset_union_right
--   have hN₁Ck : N₁.Cocircuit C
--   · rw [← hIC.sdiff_eq_right]
--     simpa [hN₁_def] using hhp.compl_cocircuit

--   have hIN₁ : N₁.Indep I
--   · rw [hN₁_def, restrict_indep_iff, and_iff_left subset_union_left]
--     exact hI.indep



--   have hI' : ∃ f ∈ I, ¬ N₁.Coloop f
--   · by_contra! h_cl
--     have hss : I ⊆ N₁✶.closure ∅ := h_cl
--     have hC₁ : (N₁ ／ I).Cocircuit C
--     · rwa [cocircuit_def, contract_dual_eq_dual_delete, ← circuit_iff_delete_of_disjoint hIC.symm,
--         ← cocircuit_def]
--     have hrw : N₁ ／ I = unifOn C 1
--     · rw [← dual_inj, unifOn_one_dual, ←  hC₁.circuit.restrict_eq_circuitOn, eq_comm,
--         restrict_eq_self_iff, hN₁_def]
--       simp [hIC.sdiff_eq_right]
--     have h' : (N₁ ／ I).Circuit C
--     · rwa [contract_eq_delete_of_subset_coloops hss, ← circuit_iff_delete_of_disjoint hIC.symm]
--     rw [hrw, ← Nat.cast_one, unifOn_circuit_iff, ← Nat.cast_one (R := ℕ∞),
--       encard_coe_eq_coe_finsetCard, ← Nat.cast_add, Nat.cast_inj] at h'
--     linarith [h'.1]

--   obtain ⟨f, hfI, hf⟩ := hI'

--   set N' := N₁ ／ (I \ {f}) with hN'_def
--   have hN'M : N' ≤m M := (contract_minor _ _).trans hN₁M

--   have hN'r : N'.rk = 2
--   · obtain ⟨e, he⟩ := hne
--     have heI : e ∉ I := fun heI ↦ (hI.subset heI).2 <| by simpa
--     have hne : e ≠ f := by rintro rfl; contradiction
--     have hIe : N₁.Base (insert e I) :=
--       hhp.insert_base_of_basis hIN₁.basis_self ⟨hN₁Cc.subset_ground he, heI⟩

--     suffices hbas : N'.Base {e,f}
--     · simp [rk, ← hbas.encard, encard_pair hne]

--     rwa [hN'_def, (hIN₁.diff _).contract_base_iff, ← union_singleton, disjoint_union_left,
--       and_iff_right disjoint_sdiff_right, disjoint_singleton_left,
--       and_iff_left (by simp [heI, hne]), union_right_comm, union_diff_self, singleton_union,
--       insert_eq_of_mem hfI, union_singleton]

--   have hfN' : N'.Flat {f}
--   · simp [flat_iff_closure_self, hN'_def, hfI, hhp.flat.closure]

--   have hloop : N'.Loopless
--   · rw [hN'_def, loopless_iff_closure_empty, contract_closure_eq, empty_union, diff_eq_empty,
--       subset_diff_singleton_iff, and_iff_left <| hIN₁.not_mem_closure_diff_of_mem hfI]
--     nth_rewrite 2 [← hhp.flat.closure]
--     exact N₁.closure_subset_closure diff_subset

--   have hU : IsEmpty (unif 2 4 ≤ir N')
--   · rw [isEmpty_iff]
--     exact fun e ↦ hcon ⟨e.isoMinor.trans_minor hN'M⟩

--   obtain ⟨C₁, C₂, hC₁, hC₂, hdj, hu⟩ := rank_two_foo hN'r hloop hfN' hU

--   replace hu := show C₁ ∪ C₂ = C by
--     simpa [hN'_def, hN₁_def, diff_diff, hfI, hIC.sdiff_eq_right] using hu

--   rw [hN'_def, cocircuit_def, deleteElem, delete_dual_eq_dual_contract,
--       contract_dual_eq_dual_delete, ← contract_delete_comm _ (by simp), delete_circuit_iff,
--       ← delete_dual_eq_dual_contract, ← cocircuit_def, ← deleteElem] at hC₁ hC₂

--   have hlt : (N₁ ＼ f)✶.erk < M✶.erk
--   · refine lt_of_lt_of_le ?_ hN₁M.dual.erk_le
--     rw [← dual_loop_iff_coloop, ← singleton_not_indep, not_not] at hf
--     rw [deleteElem, delete_dual_eq_dual_contract, ← N₁✶.erk_contract_add_er {f}, hf.er]


-- termination_by M✶.erk


    -- deleteElem, contract_delete_comm _ (by simp), ← deleteElem,
    --   cocircuit_def, contract] at hC₁





    -- have hr := hCk.compl_hyperplane.relRank_eq_one
    -- apply_fun (N.relRank ∅ (N.E \ C) + ·) at hr
    -- rw [relRank_add_cancel _ (empty_subset _) (diff_subset), relRank_empty_left, relRank_empty_left,
    --   ← hI.encard, encard_empty, zero_add] at hr
    -- have := hCc.er_add_one_eq
    -- -- rw [← WithTop.add_right_cancel_iff (a := N.relRank ∅ C)] at hr







theorem odd_circuit_cocircuit {C : Finset α} (hCc : M.Circuit C) (hCk : M.Cocircuit C)
    (hsp : M.Spanning C) (h_odd : Odd C.card) : Nonempty (unif 2 4 ≤i M) := by
  by_contra hcon

  have hcard : 3 ≤ C.card
  · obtain ⟨(rfl | k), hk⟩ := h_odd
    · obtain ⟨a, rfl⟩ : ∃ a, C = {a} := by simpa [Finset.card_eq_one, mul_zero, zero_add] using hk
      simpa using hCc.inter_cocircuit_ne_singleton hCk (e := a)
    linarith

  have hr : 2 ≤ M.er C := by
    rwa [← Nat.cast_le (α := ℕ∞), ← encard_coe_eq_coe_finsetCard, ← hCc.er_add_one_eq,
      Nat.cast_ofNat, show (3 : ℕ∞) = 2 + 1 from rfl, WithTop.add_le_add_iff_right (by simp)]
        at hcard

  obtain ⟨e, he, heC⟩ : ∃ e, M.Nonloop e ∧ e ∉ C := by
    by_contra! hcon'
    have hr' : M.er (M.E \ C) = 0 := by
      rw [er_eq_zero_iff]
      intro e he
      rw [← loop_iff_mem_closure_empty, ← not_nonloop_iff]
      exact fun hne ↦ he.2 (by simpa using hcon' e hne)
    have hr0 := hCk.compl_hyperplane.covBy.er_eq
    rw [hr', zero_add] at hr0
    simpa using hr.trans <| (M.er_mono hCc.subset_ground).trans_eq hr0


  -- obtain ⟨e, heE, heC⟩ : (M.E \ C).Nonempty := by
  --   rw [nonempty_iff_ne_empty]
  --   intro h_empty
  --   have hr' := hCk.compl_hyperplane.covBy.er_eq
  --   rw [h_empty, er_empty, zero_add] at hr'


  set N := M ↾ (insert e C) with hN_def

  have hNr : N✶.erk = 2
  · obtain ⟨f, hf⟩ := hCc.nonempty
    have hB : N.Base (C \ {f})
    · rw [base_restrict_iff]
      refine (hCc.diff_singleton_indep hf).basis_of_subset_of_subset_closure
        (diff_subset.trans (subset_insert _ _)) ?_
      rw [hCc.closure_diff_singleton_eq_closure, hsp.closure_eq, insert_subset_iff,
        and_iff_left hCc.subset_ground]
      exact he.mem_ground
    rw [← hB.compl_base_dual.encard, hN_def, restrict_ground_eq,
      insert_diff_of_not_mem _ (by simp [heC]), diff_diff_cancel_left (by simpa),
      encard_pair (by rintro rfl; contradiction)]

  have hNr' : (N✶ ＼ e).erk = 2
  · rwa [deleteElem, Coindep.delete_erk_eq]
    simp only [dual_coindep_iff, indep_singleton]
    simpa [hN_def]



  _



  have := hCc.inter_cocircuit_ne_singleton hCk

theorem foo [M.Finite] (hM : ¬ M.Binary) : Nonempty (unif 2 4 ≤i M) := by

  simp only [Binary, not_forall, Classical.not_imp, Nat.not_even_iff_odd, exists_and_left] at hM
  obtain ⟨C, K, hC, hK, hfin, h_odd : Odd hfin.toFinset.card⟩ := hM
  have nonempty : (C ∩ K).Nonempty := by
    rw [← encard_ne_zero, hfin.encard_eq_coe_toFinset_card, ← ENat.coe_zero, Ne, ENat.coe_inj]
    exact Nat.ne_of_odd_add h_odd
  have hssu1 : C \ K ⊂ C := by
    refine diff_subset.ssubset_of_ne fun h_eq ↦ ?_
    rw [sdiff_eq_left] at h_eq
    simp [h_eq.inter_eq] at nonempty
  have hssu2 : K \ C ⊂ K := by
    refine diff_subset.ssubset_of_ne fun h_eq ↦ ?_
    rw [sdiff_eq_left] at h_eq
    simp [h_eq.symm.inter_eq] at nonempty
  have hdj1 : Disjoint (C ∩ K) (K \ C) := disjoint_sdiff_right.mono_left inter_subset_left
  have hdj2 : Disjoint (C ∩ K) (C \ K) := disjoint_sdiff_right.mono_left inter_subset_right

  set N₁ := M ／ (C \ K) ＼ (K \ C) with hN₁_def

  have hCN : N₁.Circuit (C ∩ K) := by
    rw [← circuit_iff_delete_of_disjoint hdj1]
    simpa using hC.contract_circuit hssu1

  have hE := hCN.subset_ground
  obtain ⟨I, hI⟩ := N₁.exists_basis (C ∩ K) hCN.subset_ground
  obtain ⟨B, hB, rfl⟩ := hI.exists_base

  set N₂ := N₁ ／ (B \ (C ∩ K)) with hN₂_def

  have hsk : N₁.Skew (C ∩ K) (B \ (C ∩ K))
  · rw [skew_iff_closure_skew_left hCN.subset_ground, ← hI.closure_eq_closure,
      ← skew_iff_closure_skew_left (inter_subset_right.trans hE)]
    simpa using hB.indep.subset_skew_diff (inter_subset_left (t := C ∩ K))

  have hN₂c : N₂.Circuit (C ∩ K)
  · rwa [hN₂_def, circuit_iff_restr_eq_circuitOn hCN.nonempty _, hsk.symm.contract_restrict_eq,
      ← circuit_iff_restr_eq_circuitOn hCN.nonempty]
    rwa [contract_ground, subset_diff, and_iff_left disjoint_sdiff_right]

  have hN₂k : N₂.Cocircuit (C ∩ K)
  · rw [hN₂_def, hN₁_def, cocircuit_def]
    simp only [contract_dual_eq_dual_delete, delete_dual_eq_dual_contract, delete_circuit_iff]
    rw [← contract_delete_comm _ disjoint_sdiff_sdiff, delete_circuit_iff,
      and_iff_left disjoint_sdiff_right, and_iff_left hdj2, inter_comm]
    simpa using hK.circuit.contract_circuit hssu2

  have hN₂sp : N₂.Spanning (C ∩ K)
  · rw [hN₂_def, contract_spanning_iff', and_iff_left disjoint_sdiff_right,
      inter_eq_self_of_subset_left (diff_subset.trans hB.subset_ground), union_diff_self]
    exact hB.spanning.superset subset_union_right (union_subset hE hB.subset_ground)

  obtain ⟨e⟩ := odd_circuit_cocircuit (M := N₂) (C := hfin.toFinset) (by simpa) (by simpa)
    (by simpa) h_odd

  exact ⟨e.trans_minor ((contract_minor _ _).trans (contract_delete_minor _ _ _))⟩
