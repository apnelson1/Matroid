import Matroid.Connectivity.Separation.Infinite
import Matroid.Connectivity.Fan.Cyclic
import Matroid.Connectivity.Splitter.Cretaceous
import Matroid.Connectivity.Splitter.Basic
import Matroid.Connectivity.Splitter.TutteTriangle

open Set Function

namespace Matroid

variable {α β : Type*} {M : Matroid α} {N : Matroid β} {X Y C K T : Set α} {e f g x y : α}
    {b c d : Bool} {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

lemma Simple.nonempty_isoMinor_deleteElem_of_parallel (hN : N.Simple) (hNM : N ≤i M)
    (hef : M.Parallel e f) (hne : e ≠ f) : Nonempty (N ≤i M ＼ {e}) := by
  classical
  obtain ⟨M₀, hM₀, i, -⟩ := hNM.exists_iso
  have hsi := hN.of_iso i
  wlog hefM₀ : e ∈ M₀.E → f ∈ M₀.E generalizing e f with aux
  · obtain ⟨i⟩ := aux hef.symm hne.symm (by grind)
    rw [hef.parallel'.deleteElem_eq_mapEquiv]
    exact ⟨i.trans_iso <| isoMapEquiv ..⟩
  suffices aux : M₀ ≤m M ＼ {e} ∨ M₀ ≤m M ＼ {f}
  · obtain h | h := aux
    · exact ⟨i.transIsMinor h⟩
    rw [hef.parallel'.deleteElem_eq_mapEquiv]
    exact ⟨i.isoMinor.trans (h.isoMinor.trans_iso (isoMapEquiv ..))⟩
  by_contra! hcon
  by_cases hec : M₀ ≤m M ／ {e}
  · by_cases hfN : f ∈ M₀.E
    · exact ((hN.of_iso i).loopless.isNonloop_of_mem hfN).not_isLoop <|
        (hef.isLoop_contractElem hne).of_isMinor hfN hec
    obtain ⟨rfl | rfl, hf⟩ := hec.exists_isMinor_removeElem hfN
    · refine hcon.2 <| hf.trans <| contract_delete_isMinor_delete _ <| by simpa
    rw [remove_true, contract_contract, union_singleton, hef.parallel'.symm.contract_pair_eq] at hf
    exact hcon.1 <| hf.trans <| contract_delete_isMinor_delete _ (by simpa using hne.symm)
  by_cases heE : e ∈ M₀.E
  · exact hne (hef.parallel'.of_isMinor hM₀ heE (hefM₀ heE)).eq
  simpa [hcon.1, hec] using hM₀.exists_isMinor_removeElem heE

/-- If `M ／ {e}` has an `N`-minor for some simple `N`, then `M ＼ {f}` has an `N`-minor for
any `f` in a triangle with `e`. -/
lemma IsTriangle.nonempty_isMinor_delete_of_isMinor_contract (h : M.IsTriangle {e, f, g})
    (hNM : N ≤i M ／ {e}) (hN : N.Simple) : Nonempty (N ≤i M ＼ {f}) := by
  obtain ⟨i⟩ := hN.nonempty_isoMinor_deleteElem_of_parallel hNM h.parallel_contract₁ h.ne₂₃
  exact ⟨i.trans_isMinor <| contract_delete_isMinor_delete _ <| by simpa using h.ne₁₂⟩

/-- A version of `IsTriangle.nonempty_isMinor_delete_of_isMinor_contract` where instead of assuming
that `N` is simple, we assume that `M` and `N` are both `3`-connected and that `|M| ≥ 5`.
This is what we need for the splitter theorem - it follows from the simple version unless `N`
is very small. -/
lemma IsTriangle.nonempty_isMinor_delete_of_isMinor_contract' (h : M.IsTriangle {e, f, g})
    (hM : M.TutteConnected 3) (h5 : 5 ≤ M.E.encard) (hNM : N ≤i M ／ {e})
    (hN : N.TutteConnected 3) : Nonempty (N ≤i M ＼ {f}) := by
  by_cases hsi : N.Simple
  · exact h.nonempty_isMinor_delete_of_isMinor_contract hNM hsi
  obtain h4 | h3 := lt_or_ge 3 N.E.encard
  · exact False.elim <| hsi <| hN.simple <| Order.add_one_le_of_lt h4
  rw [show (3 : ℕ∞) = 2 + 1 from rfl] at hN hM
  obtain ⟨a, rfl | rfl | b, n, hNab, hab, hba, -⟩ :=
    hN.isFiniteUniform_of_encard_le (by enat_to_nat! <;> lia) (by simp)
  · simp [hNab.simple_iff] at hsi
  · have ha : a ≤ 1 := by simpa [hNab.simple_iff] using hsi
    rw [zero_add] at hNab
    obtain ⟨C, hCn, hCfin, rfl⟩ := hNab.exists_eq_circuitOn
    rw [nonempty_circuitOn_isoMinor_iff_of_finite hCn hCfin]
    obtain ⟨C', hC'⟩ := (hM.connected_deleteElem (by enat_to_nat!; lia) f).exists_isCircuit_of_ne
      (by grind) (by grind) h.ne₁₃
    refine ⟨C', hC'.1, ?_⟩
    grw [← show ({e, g} : Set α) ⊆ C' by grind, encard_pair h.ne₁₃, ← circuitOn_ground (C := C),
      hNab.encard_eq, ← hNab.add_eq]
    enat_to_nat; lia
  obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 0 := by grind [hNab.tutteConnected_iff, hNab.simple_iff]
  rw [← isFiniteUniform_dual_iff, zero_add, one_add_one_eq_two] at hNab
  obtain ⟨K, hKne, hKfin, hKN⟩ := hNab.exists_eq_circuitOn
  rw [← nonempty_isoMinor_dual_iff, hKN, nonempty_circuitOn_isoMinor_iff_of_finite hKne hKfin]
  simp_rw [show K.encard = (circuitOn K).E.encard from rfl, ← hKN, hNab.encard_eq, ← hNab.add_eq]
  refine exists_isCircuit_encard_ge_three ?_ ?_
  · have hne : (M ＼ {f})✶.Nonempty := ⟨e, h.mem_ground₁, h.ne₁₂⟩
    exact (hM.deleteElem (by enat_to_nat!; lia) f).dual.connected rfl.le
  by_contra! hlt
  rw [dual_delete, ← ENat.add_one_lt_add_one_iff,
   h.isNonColoop₂.isNonloop_dual.eRank_contractElem_add_one, ENat.lt_add_one_iff (by simp)] at hlt
  have hc1 : M.eConn {e, f, g} ≤ 1 := by
    have hc := (M.eRk_add_eRk_dual_eq {e, f, g}).symm.le
    grw [h.three_elements, h.eRk, eRk_le_eRank] at hc
    enat_to_nat! <;> lia
  obtain h2 | h3 := hM.encard_eq_or_encard_compl_eq (X := {e, f, g}) (by enat_to_nat! <;> lia)
  · simp [← h2, h.three_elements] at hc1
  rw [← encard_diff_add_encard_of_subset h.subset_ground, h.three_elements] at h5
  enat_to_nat! <;> lia


lemma TutteConnected.splitterTheoremHoldsFor_of_fan_on_ground (hM : M.TutteConnected 3)
    (hlen : 4 ≤ M.E.encard) (hF : M.IsFan F b c)
    (hFE : {x | x ∈ F} = M.E) (N : Matroid α) : SplitterTheoremHoldsFor M N := by
  obtain ⟨n, J, h2n, hnF, hJ, hJE⟩ :=
    hF.exists_isCyclicFan_of_ground_eq (hM.simple hlen) (hM.dual.simple hlen) hFE
  exact .inl ⟨n, by lia, J, hJ, hJE⟩

/-- `M.IsFlexibleFan N F b c` means that `F` is a `b,c`-fan of `M`, and that deleting any joint
or contracting any cojoint of `F` preserves the property of having an `N`-minor. -/
structure IsFlexibleFan (M : Matroid α) (N : Matroid β) (F : List α) (b c : Bool) : Prop where
  isFan : M.IsFan F b c
  nonempty_isoMinor : ∀ (i : ℕ) (hi : i < F.length), Nonempty (N ≤i M.remove (i.bodd != b) {F[i]})


lemma foo (hM : M.TutteConnected 3) (hN : N.TutteConnected 3) {F : List α} (hMfin : M.Finite)
    (hF : M.IsFlexibleFan N F b c) (hlen : 5 ≤ F.length) : SplitterTheoremHoldsFor M N := by
  have hM5 : 5 ≤ M.E.encard := by
    grw [← ENat.coe_le_coe, ← hF.isFan.nodup.encard_toSet_eq, hF.isFan.subset_ground] at hlen
    assumption
  have hM4 : 4 ≤ M.E.encard := by enat_to_nat!; lia

  -- have hms : M.Simple := hM.simple (by enat_to_nat!; lia)
  -- have hmcs : M✶.Simple := hM.dual.simple (by rw [dual_ground]; enat_to_nat!; lia)

  -- obtain heq | hssu := hF.isFan.subset_ground.eq_or_ssubset
  -- · obtain ⟨n, J, hn, hn2, hJ, hnF⟩ := hF.isFan.exists_isCyclicFan_of_ground_eq hms hmcs heq
  --   exact .inl ⟨n, by lia, J, hJ, hnF⟩

  by_contra! hcon
  have aux {d : Bool} {i : ℕ} (hi : i < F.length) (hi0 : i.bodd = d) :
      ¬ ((M.bDual b).remove d {F[i]}).TutteConnected 3 := by
    contrapose! hcon
    refine .inr ⟨d != b, F[i], hF.isFan.get_mem_ground, hi0 ▸ hF.nonempty_isoMinor i hi  , ?_⟩
    rw [← tutteConnected_bDual_iff (b := b), bDual_remove]
    cases b with simpa using hcon
  have auxd {i : ℕ} (hi : i < F.length) (hi0 : i.bodd = false) :
      ¬ ((M.bDual b) ＼ {F[i]}).TutteConnected 3 := aux hi hi0
  have := hF.nonempty_isoMinor 0 (by lia)
  simp at this

  obtain ⟨K, hK, h0K, ⟨h2K, h1K⟩ | ⟨h1K, h2K⟩⟩ :=
    tutte_triangle (hM.bDual b) (hF.isFan.isTriangle_bDual (by lia)).swap_right (by simpa)
     (auxd (by lia) rfl) (auxd (by lia) rfl)
  · have := hF.isFan.mem_or_mem₁₂ 2 K (by lia)
      (by simpa using hK.isCocircuit.isCircuit) h2K




  -- have := (hM.bDual b).tutte_tri (hF.isFan.isTriangle_bDual (by lia))









--
