import Matroid.Connectivity.Separation.Infinite
import Matroid.Connectivity.Fan.ThreeConnected
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

lemma bar (P : Bool → ℕ → Prop) {a : ℕ} (h : P false 0)
    (h : ∀ s i j b, s + 2 < a → s.bodd = b → s ≤ i → i ≤ s + 2 → s ≤ j → j ≤ s + 2 → i ≠ j →
      P b i → P (!b) j) (d : Bool) {j : ℕ} (hj : j + 2 < a) : P d (j + 1) := by
  sorry

lemma splitter [M.Finite] {N : Matroid α} (hM : M.TutteConnected 3) (h5 : 5 ≤ M.E.encard)
    (hNM : N <m M) (hN : N.TutteConnected 3) (not_whorl : ¬ ∃ F b, M.IsCyclicFan F b) :
    ∃ e b, e ∈ M.E ∧ Nonempty (N ≤i M.remove b {e}) ∧ (M.remove b {e}).TutteConnected 3 := by
  by_cases! hex :
      ∀ e b, e ∈ M.E → Nonempty (N ≤i M.remove b {e}) → ∀ T, (M.bDual !b).IsTriangle T → e ∉ T
  · exact splitter_no_triangle_minor hM (by enat_to_nat!; lia) hNM hN hex

  have h4 : 4 ≤ M.E.encard := le_trans (by simp) h5
  by_contra! hcon
  -- find a good fan.
  obtain ⟨F₀, b, c, hF₀, hF₀4, hF₀ne⟩ : ∃ (F₀ : List α) (b c : Bool) (hF₀ : M.IsFan F₀ b c)
      (hF₀4 : F₀.length = 4), ∀ e ∈ F₀, ∃ d, Nonempty (N ≤i M.remove d {e}) := by
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
      refine ⟨[x, y, z, w], _, _, (hw.swap_left.isFan.cons (by simpa) (by simpa)).of_bDual, rfl, ?_⟩
      obtain rfl | rfl := d₀ <;>
      · simp only [remove_false, Bool.not_false, Bool.not_true, remove_true] at hNx hNy hNz hNw
        simp [hNx, hNy, hNz, hNw]
    have hNw := hw.swap_right.nonempty_isMinor_remove_of_isMinor_remove hM h5 hNz hN
    refine ⟨[y, x, z, w], _, _,
      (hw.swap_left.isFan.cons (by simpa) (by simpa using hT.swap_left)).of_bDual, rfl, ?_⟩
    obtain rfl | rfl := d₀ <;>
    · simp only [remove_false, Bool.not_false, Bool.not_true, remove_true] at hNx hNy hNz hNw
      simp [hNx, hNy, hNz, hNw]
  -- extend it to a maximal fan
  obtain ⟨F, d, hF₀F, h | ⟨hF, hF3⟩⟩ :=
    hM.exists_subset_isFan_remove_tutteConnected_three hF₀ hF₀4.ge
  · exact not_whorl ⟨_, _, h⟩








    -- · simpa only [bDual_delete, tutteConnected_bDual_iff]

    -- have hNy := hT.nonempty_isMinor_delete_of_isMinor_contract' hM h5 hNx.some hN
    -- have hNz := hT.swap_right.nonempty_isMinor_delete_of_isMinor_contract' hM h5 hNx.some hN
    -- obtain ⟨w, hwx, hw⟩ | ⟨w, hwy, hw⟩ := tutte_triangle' hM hT.reverse
    --   (by enat_to_nat!; lia) (hcon z false hT.mem_ground₃ hNz) (hcon y false hT.mem_ground₂ hNy)

#exit

  wlog hd₀ : d₀ = true generalizing d₀ M N with aux
  · obtain rfl : d₀ = false := by grind
    specialize aux hM.dual (by simpa) hNM.dual hN.dual ?_ true hx ?_ (by simpa) rfl
    · exact fun ⟨F, b, hF'⟩ ↦ not_whorl ⟨F, !b, by simpa using hF'⟩
    · simpa using nonempty_isoMinor_dual_iff.2 hNx
    obtain ⟨e, b, he, hNM', h3⟩ := aux
    refine ⟨e, !b, he, ?_, by simpa using h3.dual ⟩
    simpa [← nonempty_isoMinor_dual_iff (N := N)]
  subst hd₀
  simp only [Bool.not_true, bDual_false, remove_true] at hT hNx
  by_contra! hcon
  -- `M` has a `4`-fan `F₀` containing two deletable elements.
  obtain ⟨F₀, b, c, hF₀, hF₀4, hF₀ne⟩ : ∃ (F₀ : List α) (b c : Bool) (hF₀ : M.IsFan F₀ b c)
    (hF₀4 : F₀.length = 4), ∀ e ∈ F₀, ∃ d, Nonempty (N ≤i M.remove d {e}) := by
    obtain ⟨y, z, -, -, -, rfl⟩ := exists_eq_of_encard_eq_three_of_mem hT.three_elements hxT
    have hNy := hT.nonempty_isMinor_delete_of_isMinor_contract' hM h5 hNx.some hN
    have hNz := hT.swap_right.nonempty_isMinor_delete_of_isMinor_contract' hM h5 hNx.some hN
    obtain ⟨w, hwx, hw⟩ | ⟨w, hwy, hw⟩ := tutte_triangle' hM hT.reverse
      (by enat_to_nat!; lia) (hcon z false hT.mem_ground₃ hNz) (hcon y false hT.mem_ground₂ hNy)
    · have := hw.non
      have hF := hw.reverse.isFan.cons (e := x) hT.ne₁₃ (by simpa)


    obtain ⟨K, hK, hzK, ⟨hyK, hxK⟩ | ⟨hyK, hxK⟩⟩ := tutte_triangle hM hT.reverse
      (by enat_to_nat!; lia) (hcon z false hT.mem_ground₃ hNz) (hcon y false hT.mem_ground₂ hNy)
    ·
      obtain ⟨w, -, -, rfl⟩ :=
        exists_eq_of_encard_eq_three_of_mem_of_mem hK.three_elements hyK hzK hT.ne₂₃
      refine ⟨_, _, _, (hK.isFan.cons (e := x) (by grind) (by simpa)).of_dual, rfl, ?_⟩
      -- simp [Set.Nontrivial]
      exact ⟨y, ⟨by simp, hNy⟩, z, ⟨by simp, hNz⟩, hT.ne₂₃⟩
    obtain ⟨w, -, -, rfl⟩ :=
      exists_eq_of_encard_eq_three_of_mem_of_mem hK.three_elements hxK hzK hT.ne₁₃
    exact ⟨_, _, _, (hK.isFan.cons (e := y) (by grind) (by simpa using hT.swap_left)).of_dual,
      rfl, ⟨y, ⟨by simp, hNy⟩, z, ⟨by simp, hNz⟩, hT.ne₂₃⟩⟩
  clear! x


  obtain ⟨F, d, hF₀F, h | ⟨hF, hF3⟩⟩ :=
    hM.exists_subset_isFan_remove_tutteConnected_three hF₀ hF₀4.ge
  · exact not_whorl ⟨_, _, h⟩
  have h4F := hF₀4.symm.trans_le <| hF₀.nodup.length_le_of_subset hF₀F

  have hnd := bar (P := fun b i ↦ ∃ (hi : i < F.length), IsEmpty (N ≤i M.remove (b != d) {F[i]}))
    (a := F.length) ?_ ?_
  · obtain ⟨x, ⟨hxF₀, hxd⟩, hxne⟩ := hF₀ne.diff_singleton_nonempty (F[F.length - 1])
    obtain ⟨rfl | j, hj, rfl⟩ := List.getElem_of_mem (hF₀F hxF₀)
    · have := hcon _ false hF.getElem_mem_ground hxd
    have hlt : j + 1 < F.length := by grind
    have := hnd false

    sorry

  · by_contra! hcon'
    exact hcon _ _ hF.getElem_mem_ground (by simpa using hcon' (by lia)) hF3
  intro s i j b hs hsb hsi his hsj hjs hij ⟨hiF, hemp⟩
  contrapose! hemp
  obtain ⟨hFj⟩ := hemp (by lia)
  have hwin := (hF.isTriangle_getElem s).nonempty_isMinor_remove_of_isMinor_remove' (e := F[j])
    (f := F[i]) (N := N) hM h5 (by grind [hF.nodup.getElem_inj_iff])
    (by grind [hF.nodup.getElem_inj_iff]) (by grind [hF.nodup.getElem_inj_iff]) hN
    (by cases d with simpa [hsb] using hFj)
  cases d with simpa [hsb] using hwin

  -- simp [hF.nodup.getElem_inj_iff, show j = s ∨ j = s + 1 ∨ j = s + 2 by grind] at this


  -- · sorry
  -- · by_contra! hcon'
  --   exact hcon _ _ hF.getElem_mem_ground (by simpa using hcon' (by lia)) hF3

  -- have aux : ∀ i b (hi : i + 2 < F.length), IsEmpty (N ≤i M.remove b {F[i + 1]}) := by
  --   intro i b hi
  --   induction i with
  --   | zero =>
  --     by_contra! hne
  --     simp only [zero_add] at hne
  --     have hT : (M.bDual d).IsTriangle {F[0], F[1], F[2]} := by simpa using hF.isTriangle_getElem 0
  --     suffices hne' : Nonempty (N ≤i M.remove (!d) {F[1]}) by
  --       have hwin := hT.swap_left.nonempty_isMinor_remove_of_isMinor_remove hM h5 hne'.some hN
  --       exact hcon _ _ hF.getElem_mem_ground hwin hF3
  --     obtain rfl | rfl := b.eq_or_eq_not !d
  --     · exact hne
  --     have hT' : (M.bDual !d).IsTriangle {F[1], F[2], F[3]} := by
  --       simpa using hF.isTriangle_getElem 1
  --     have hne' := hT'.nonempty_isMinor_remove_of_isMinor_remove (N := N) hM h5 hne.some hN
  --     have := hT.reverse.nonempty_isMinor_remove_of_isMinor_remove hM h5 hne'.some hN


  --   | succ n _ => sorry

  --   _
  -- obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem (hF₀F hxF₀)

  -- obtain ⟨F, d, hFc | ⟨hF, hF4, hFc⟩⟩ :=
  --   hM.exists_subset_isFan_remove_tutteConnected_three
  --   --  ⟨F₀, _, _, hF₀, hF₀4.ge⟩
  -- · exact not_whorl ⟨F, _, hFc⟩




  -- have hne : Nonempty ((N.bDual !d₀) ≤i (M.bDual !d₀) ／ {x}) := by
  --   rwa [← nonempty_isoMinor_bDual_iff (b := !d₀), bDual_contract, bDual_bDual_self,
  --     bDual_bDual_self, Bool.not_not]
  -- have hney := hT.nonempty_isMinor_delete_of_isMinor_contract' (hM.bDual _)
  --   (by simpa) hne.some (hN.bDual !d₀)
  -- have hnex := hT.swap_right.nonempty_isMinor_delete_of_isMinor_contract' (hM.bDual _)
  --   (by simpa) hne.some (hN.bDual !d₀)
  -- have := tutte_triangle (hM.bDual _) hT (by simpa)


  -- by_contra! hcon
  -- have h₀ := hcon x d₀ hx hNx

  -- have := hT.nonempty_isMinor_delete_of_isMinor_contract'
  -- wlog hd₀ : d₀ = false generalizing M N d₀ with aux
  -- · obtain rfl : d₀ = true := by grind
  --   have := aux hM.dual (by simpa) hNM.dual hN.dual ?_ false he₀ ?_ (by simpa)

  --
  -- by_cases h3c : (M.drmo)

-- lemma foo (hM : M.TutteConnected 3) {T T'} (hT : M.IsTriangle T) (hT' : M.IsTriad T')
--     (hne : (T ∩ T').Nonempty)
