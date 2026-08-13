import Matroid.Connectivity.Fan.ThreeConnected
import Matroid.Connectivity.Splitter.Cretaceous

open Set Function

namespace Matroid

variable {α β : Type*} {M : Matroid α} {N : Matroid β} {X Y C K T : Set α} {e f g x y : α}
    {b c d : Bool} {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

/-- If `N` is a simple minor of a matroid `M`, and `{e, f}` is a parallel pair of `M`,
then `M ＼ {e}` has an `N`-minor. -/
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
    (hM : M.TutteConnected 3) (h5 : 5 ≤ M.E.encard) (hNM : Nonempty (N ≤i M ／ {e}))
    (hN : N.TutteConnected 3) : Nonempty (N ≤i M ＼ {f}) := by
  by_cases hsi : N.Simple
  · exact h.nonempty_isMinor_delete_of_isMinor_contract hNM.some hsi
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
  rw [← encard_sdiff_add_encard_of_subset h.subset_ground, h.three_elements] at h5
  enat_to_nat! <;> lia

lemma IsTriangle.nonempty_isMinor_remove_of_isMinor_remove (h : (M.bDual b).IsTriangle {e, f, g})
    (hM : M.TutteConnected 3) (h5 : 5 ≤ M.E.encard) (hNM : Nonempty (N ≤i M.remove (!b) {e}))
    (hN : N.TutteConnected 3) : Nonempty (N ≤i M.remove b {f}) := by
  have := h.nonempty_isMinor_delete_of_isMinor_contract' (N := N.bDual b)
    (by simpa) (by simpa) (Nonempty.some ?_) (by simpa)
  · cases b
    · simpa using this
    simpa [← nonempty_isoMinor_dual_iff (N := N✶)] using this
  rw [← nonempty_isoMinor_bDual_iff (b := b), bDual_bDual_self, bDual_contract, bDual_bDual_self]
  exact ⟨hNM⟩

lemma IsTriangle.nonempty_isMinor_remove_of_isMinor_remove' {T : Set α} (hM : M.TutteConnected 3)
    (h5 : 5 ≤ M.E.encard) (h : (M.bDual b).IsTriangle T) (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f)
    (hN : N.TutteConnected 3) (hNM : Nonempty (N ≤i M.remove (!b) {e})) :
    Nonempty (N ≤i M.remove b {f}) := by
  obtain ⟨g, ge, hgf, rfl⟩ := exists_eq_of_encard_eq_three_of_mem_of_mem h.three_elements he hf hef
  exact h.nonempty_isMinor_remove_of_isMinor_remove hM (N := N) h5 hNM hN

/-- A fan is good for a minor `N` if its joints are deletable for `N` and its cojoints are
contractible for `N`. -/
structure IsGoodFan (M : Matroid α) (N : Matroid β) (F : List α) (b c : Bool) : Prop where
  isFan : M.IsFan F b c
  nonempty_isoMinor : ∀ i (hi : i < F.length), Nonempty (N ≤i M.remove (i.bodd != b) {F[i]})

/-- Any fan on at least five elements with a removable internal element is good. -/
lemma IsFan.isGoodFan_of_single (hF : M.IsFan F b c) (h5 : 5 ≤ F.length)
    (hM : M.TutteConnected 3) (hN : N.TutteConnected 3)
    {s : ℕ} {d : Bool} (hs : s + 1 < F.length) (hs0 : s ≠ 0)
    (hne : Nonempty (N ≤i M.remove d {F[s]})) : M.IsGoodFan N F b c := by
  have hM5 : 5 ≤ M.E.encard := by
    grw [← hF.subset_ground, hF.nodup.encard_toSet_eq, ← h5, ENat.coe_eq_ofNat]
  suffices aux : ∃ (t : ℕ) (ht : t + 1 < F.length), t ≠ 0 ∧
      Nonempty (N ≤i M.remove (t.bodd != b) {F[t]}) by
    clear! s
    obtain ⟨s, hlt, hs0, hs⟩ := aux
    refine ⟨hF, fun i hiF ↦ ?_⟩
    wlog hsi : s ≤ i generalizing F b c i s with aux
    · specialize aux hF.reverse (by simpa) (i := F.length - 1 - i) (s := F.length - 1 - s)
        (by grind) (by lia) ?_ (by grind) (by lia)
      · rw [Nat.bodd_sub (by lia), hF.length_sub_one_bodd_eq, F.getElem_reverse' (j := s) (by lia)]
        cases b with cases c with simpa using hs
      rw [Nat.bodd_sub (by lia), hF.length_sub_one_bodd_eq, F.getElem_reverse' (j := i) (by lia)]
        at aux
      cases b with cases c with simpa using aux
    induction i using Nat.strong_induction_on with | h n ih =>
    obtain rfl | hslt := hsi.eq_or_lt
    · assumption
    obtain rfl | rfl | n := n
    · simp at hslt
    · lia
    cases b with simpa using IsTriangle.nonempty_isMinor_remove_of_isMinor_remove
      (hF.isTriangle_getElem n).rotate_left hM hM5
      (by simpa using ih (n + 1) (by lia) (by lia) (by lia)) hN
  obtain rfl | rfl := d.eq_or_eq_not (s.bodd != b)
  · exact ⟨s, hs, hs0, hne⟩
  obtain rfl | rfl | rfl | s := s
  · simp at hs0
  · exact ⟨3, by lia, by simp, by
      simpa using (hF.isTriangle_getElem 1).swap_right.nonempty_isMinor_remove_of_isMinor_remove hM
        hM5 (by simpa using hne) hN⟩
  · refine ⟨3, by lia, by simp, ?_⟩
    have h1 := (hF.isTriangle_getElem 0).reverse.nonempty_isMinor_remove_of_isMinor_remove hM hM5
      (by simpa using hne) hN
    simpa using (hF.isTriangle_getElem 1).swap_right.nonempty_isMinor_remove_of_isMinor_remove
      hM hM5 (by simpa using h1) hN
  exact ⟨s + 1, by lia, by
    cases b with simpa using IsTriangle.nonempty_isMinor_remove_of_isMinor_remove
       (hF.isTriangle_getElem (s + 1)).rotate hM hM5 (by simpa using hne) hN⟩

/-- The splitter theorem holds if `M` has at most five elements. This is true because any such
  `M` must be a uniform matroid. -/
private lemma splitter_small {N : Matroid α} (hM : M.TutteConnected 3) (h5 : M.E.encard ≤ 5)
    (hNM : N <m M) (hN : N.TutteConnected 3) :
    ∃ e b, e ∈ M.E ∧ Nonempty (N ≤i M.remove b {e}) ∧ (M.remove b {e}).TutteConnected 3 := by
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  obtain ⟨b, hb⟩ := hM.exists_forall_remove_of_isUniform (hM.isUniform_of_encard_le h5)
    (by grw [finite_iff, ← encard_lt_top_iff, h5, ENat.ofNat_lt_top])
  wlog hb' : b = true generalizing M N b with aux
  · obtain rfl : b = false := by grind
    obtain ⟨e, b, he, hne, htc⟩ :=
      aux hM.dual h5 hNM.dual hN.dual true (by simpa using fun e ↦ (hb e).dual) rfl
    exact ⟨e, !b, he, by simpa [← nonempty_isoMinor_dual_iff (N := N✶)] using hne,
      by simpa using htc.dual⟩
  subst hb'
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.isMinor.exists_contract_indep_delete_coindep
  obtain ⟨e, heC⟩ | rfl := C.eq_empty_or_nonempty.symm
  · refine ⟨e, true, hC.subset_ground heC, ⟨IsMinor.isoMinor ?_⟩, hb e⟩
    exact (delete_isMinor ..).trans <| contract_isMinor_of_subset _ <| by simpa
  obtain rfl | ⟨e, heD⟩ := D.eq_empty_or_nonempty
  · simp [isStrictMinor_irrefl] at hNM
  simp_rw [contract_empty] at *
  have hmin : M ＼ D ≤m M.remove false {e}:= (delete_isRestriction_of_subset _ (by simpa)).isMinor
  refine ⟨e, false, hD.subset_ground heD, ⟨hmin.isoMinor⟩, ?_⟩
  apply TutteConnected.tutteConnected_of_tutteConnected_isSpanningRestriction hN hM
    hD.delete_isSpanningRestriction hmin (remove_isMinor ..)

/- ## Seymour's splitter theorem -/
/-- If `N` is a `3`-connected proper minor of a `3`-connected matroid `M`,
then either `M` is a wheel or whirl,
or there is an element `e` such that `M ／ e` or `M ＼ e` is `3`-connected with an `N`-minor. -/
theorem splitterTheorem [M.Finite] {N : Matroid α} (hM : M.TutteConnected 3) (hNM : N <m M)
    (hN : N.TutteConnected 3) (not_whorl : ¬ ∃ F b, M.IsCyclicFan F b) :
    ∃ e b, e ∈ M.E ∧ Nonempty (N ≤i M.remove b {e}) ∧ (M.remove b {e}).TutteConnected 3 := by
  obtain h5 | h5 := lt_or_ge M.E.encard 5
  · exact splitter_small hM h5.le hNM hN
  by_cases! hex :
      ∀ e b, e ∈ M.E → Nonempty (N ≤i M.remove b {e}) → ∀ T, (M.bDual !b).IsTriangle T → e ∉ T
  · exact splitter_no_triangle_minor hM (by enat_to_nat!; lia) hNM hN hex
  have h4 : 4 ≤ M.E.encard := le_trans (by simp) h5
  by_contra! hcon
  -- find a length-four fan `F₀` whose first element is removable in the right way for `N`.
  obtain ⟨F₀, b, c, hF₀, hF₀4, hF₀ne⟩ : ∃ (F₀ : List α) (b c : Bool) (hF₀ : M.IsFan F₀ b c)
      (hF₀4 : F₀.length = 4), Nonempty (N ≤i M.remove b {F₀[0]}) := by
    obtain ⟨x, d₀, hx, hNx, T, hT, hxT⟩ := hex
    obtain ⟨y, z, -, -, -, rfl⟩ := exists_eq_of_encard_eq_three_of_mem hT.three_elements hxT
    have hNy := hT.nonempty_isMinor_remove_of_isMinor_remove hM h5 (by simpa) hN
    have hNz := hT.swap_right.nonempty_isMinor_remove_of_isMinor_remove hM h5 (by simpa) hN
    have hyr := hcon y _ (by simpa using hT.mem_ground₂) hNy
    have hzr := hcon z _ (by simpa using hT.mem_ground₃) hNz
    obtain ⟨w, hw⟩ := tutte_triangle' (by simpa) hT.reverse (by simpa)
      (by simpa only [bDual_delete, tutteConnected_bDual_iff])
      (by simpa only [bDual_delete, tutteConnected_bDual_iff])
    simp only [bDual_isTriad_iff, Bool.not_not, ne_comm (a := w)] at hw
    obtain ⟨hxw, hw⟩ | ⟨hyw, hw⟩ := hw
    · have hNw := hw.swap_right.nonempty_isMinor_remove_of_isMinor_remove hM h5 hNz hN
      use [x, y, z, w]
      refine ⟨_, _, (hw.swap_left.isFan.cons (by simpa) (by simpa)).of_bDual, rfl, ?_⟩
      simp
      have hNy' := hw.nonempty_isMinor_remove_of_isMinor_remove hM h5 hNz hN
      exact hT.swap_left.nonempty_isMinor_remove_of_isMinor_remove hM h5 (by simpa) hN
    have hNw := hw.swap_right.nonempty_isMinor_remove_of_isMinor_remove hM h5 hNz hN
    use [y, x, z, w]
    exact ⟨_, _, (hw.swap_left.isFan.cons (by simpa) (by simpa using hT.swap_left)).of_bDual,
      rfl, by simpa⟩
  -- extend `F₀` (after possibly switching the middle two elements to get `F₁`)
  -- to a fan `F` that is either cyclic, or whose first element is removable
  -- in the right way for connectivity.
  obtain ⟨F, F₁, hF₁, hF₁F, hcyc | ⟨d, hF, hFr⟩⟩ := hF₀.exists_suffix_removable hF₀4.ge hM
  -- If `F` it is cyclic, we win.
  · exact not_whorl ⟨_, _, hcyc⟩
  -- If the extension is trivial, then the first element is removable for both `N` and connectivity
  have hlen : F₀.length = F₁.length := by grind
  suffices hFgood : M.IsGoodFan N F d c from
    hcon _ _ hF.getElem_mem_ground (hFgood.2 0 (by grind)) <| by simpa
  -- otherwise, the fan `F` contains an internal `N`-removable element and has length at least `5`,
  -- so its first element is removable for `N` as well.
  obtain h4 | h5' := hF₁F.length_le.eq_or_lt
  · obtain rfl : F₁ = F := hF₁F.eq_of_length_le h4.ge
    obtain rfl : b = d := by simp [hF₀.bool_left_eq, hlen, ← hF.bool_left_eq]
    exact False.elim <| hcon F₀[0] b hF₀.getElem_mem_ground hF₀ne <| by cases hF₁ with grind
  obtain ⟨L, rfl⟩ := List.suffix_iff_exists_eq_append.1 hF₁F
  refine hF.isGoodFan_of_single (s := L.length) (d := b) (by grind) hM hN (by grind) (by grind) ?_
  simpa [show F₁[0] = F₀[0] by grind]

/- ## Tutte's Wheels and Whirls Theorem -/
/-- Every nonempty `3`-connected matroid that is not a wheel
or whirl has an element whose removal keeps `3`-connectivity. -/
theorem wheelsAndWhirls [M.Finite] (hM : M.TutteConnected 3) (hne : M.Nonempty)
    (hF : ¬ ∃ F b, M.IsCyclicFan F b) :
    ∃ e ∈ M.E, (M ／ {e}).TutteConnected 3 ∨ (M ＼ {e}).TutteConnected 3 := by
  have he : emptyOn α <m M := by
    rw [isStrictMinor_iff_isMinor_ne, and_iff_right M.emptyOn_isMinor]
    rintro rfl
    simp [← Matroid.ground_nonempty_iff] at hne
  obtain ⟨e, rfl | rfl, he, -, htc⟩ := splitterTheorem hM (N := emptyOn α) he (by simp) hF
  · exact ⟨e, he, .inr htc⟩
  exact ⟨e, he, .inl htc⟩
