import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Support
import Matroid.Graph.Walk.Dart

open Set PFun Part Equiv Function Equiv.Perm

namespace Equiv

variable {α : Type*} {S s t : Set α} {e f : Equiv.Perm α} {x y z : α} {k n : ℕ}

lemma apply_symm_commute (e : Equiv.Perm α) : Function.Commute e e.symm := by
  rintro x
  simp

@[simp]
lemma apply_pow_symm_pow_comm (e : Equiv.Perm α) (k n : ℕ) (x : α) :
    (e ^ n) ((e.symm ^ k) x) = (e.symm ^ k) ((e ^ n) x) := by
  simpa using e.apply_symm_commute.iterate_iterate n k x

@[simp]
lemma symm_pow_apply_pow_of_le (e : Equiv.Perm α) (h : k ≤ n) (x : α) :
    (e.symm ^ k) ((e ^ n) x) = (e ^ (n - k)) x := by
  induction k generalizing x n with
  | zero => simp
  | succ k ih =>
    rcases n with _ | n
    · exact (Nat.not_succ_le_zero k h).elim
    rw [pow_succ', Perm.mul_apply, ih (Nat.le_of_succ_le h)]
    have : n + 1 - k = Nat.succ (n - k) := by omega
    rw [this, pow_succ', Perm.mul_apply, symm_apply_apply]
    congr 1
    simp [Nat.succ_sub_succ]

@[simp]
lemma symm_pow_apply_pow_of_ge (e : Equiv.Perm α) (h : n ≤ k) (x : α) :
    (e.symm ^ k) ((e ^ n) x) = (e.symm ^ (k - n)) x := by
  induction n generalizing x k with
  | zero => simp
  | succ k ih =>
    rcases k with _ | k'
    · simp at h
    rw [pow_succ, pow_succ']
    simp [ih (by omega : k ≤ k')]

lemma Perm.IsCycleOn.eq_of_mem_mem (hs : e.IsCycleOn s) (ht : e.IsCycleOn t) (hxs : x ∈ s)
    (hxt : x ∈ t) : s = t := by
  ext y
  refine ⟨fun hys ↦ ?_, fun hyt ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := hs.2 hxs hys
    exact (ht.1.perm_zpow i).mapsTo hxt
  obtain ⟨i, rfl⟩ := ht.2 hxt hyt
  exact (hs.1.perm_zpow i).mapsTo hxs

lemma Perm.IsCycleOn.eq_or_disjoint (hs : e.IsCycleOn s) (ht : e.IsCycleOn t) :
    s = t ∨ _root_.Disjoint s t := by
  rw [or_iff_not_imp_right]
  intro hst
  obtain ⟨x, hxs, hxt⟩ := Set.not_disjoint_iff.mp hst
  exact hs.eq_of_mem_mem ht hxs hxt

lemma Perm.isCycleOn_range (e : Equiv.Perm α) (x : α) :
    e.IsCycleOn (Set.range fun i : ℤ ↦ (e ^ i) x) := by
  refine ⟨?_, ?_⟩
  · refine e.bijOn' ?_ ?_ <;> rintro y ⟨i, rfl⟩
    · use i + 1
      rw [add_comm]
      simp [zpow_add]
    use i - 1
    rw [← neg_add_eq_sub]
    simp [zpow_add]
  rintro y ⟨i, rfl⟩ z ⟨j, rfl⟩
  simpa using SameCycle.refl e x

def finiteOrbit (e : Equiv.Perm α) := periodicPts e = univ

lemma finiteOrbit_iff (e : Equiv.Perm α) :
    e.finiteOrbit ↔ ∀ x, ∃ n, 0 < n ∧ IsPeriodicPt e n x := by
  simp [finiteOrbit, Set.ext_iff, mem_periodicPts]

lemma finiteOrbit.isPeriodicPt (he : e.finiteOrbit) (x : α) :
    ∃ n, 0 < n ∧ IsPeriodicPt e n x := by
  have := he ▸ mem_univ x
  exact this

lemma finiteOrbit.symm (he : e.finiteOrbit) : e.symm.finiteOrbit := by
  rw [finiteOrbit_iff] at he ⊢
  intro x
  obtain ⟨n, hn, h⟩ := he x
  use n, hn
  unfold IsPeriodicPt IsFixedPt at h ⊢
  nth_rewrite 1 [← h]
  simp

lemma finiteOrbit.exists_pow_eq_of_sameCycle (he : e.finiteOrbit) (hxy : SameCycle e x y) :
    ∃ n, (e ^ n) x = y := by
  obtain ⟨n, hn, h⟩ := he.isPeriodicPt x
  obtain ⟨i, rfl⟩ := hxy
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn.ne'
  refine ⟨(i % n).toNat, ?_⟩
  simp only [IsPeriodicPt, IsFixedPt, Perm.iterate_eq_pow] at h
  rw [← zpow_natCast, Int.toNat_of_nonneg (i.emod_nonneg hn')]
  conv_rhs => rw [← i.emod_add_mul_ediv n, zpow_add, zpow_mul, zpow_natCast, Equiv.Perm.mul_apply,
    zpow_apply_eq_self_of_apply_eq_self h (i / (n : ℤ))]

lemma finiteOrbit_iff_finite_of_isCycleOn (e : Equiv.Perm α) :
    e.finiteOrbit ↔ ∀ t, e.IsCycleOn t → t.Finite := by
  refine ⟨fun he t ht ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl | ⟨a, ha⟩ := t.eq_empty_or_nonempty
    · simp
    obtain ⟨n, hn, hper⟩ := he.isPeriodicPt a
    refine (Set.finite_range (fun k : Fin n ↦ (e ^ (k : ℕ)) a)).subset fun y hy ↦ ?_
    obtain ⟨m, rfl⟩ := he.exists_pow_eq_of_sameCycle (ht.2 ha hy)
    exact ⟨⟨m % n, Nat.mod_lt m hn⟩, by simpa [Perm.iterate_eq_pow] using hper.iterate_mod_apply m⟩
  refine finiteOrbit_iff e |>.mpr fun x ↦ ?_
  obtain ⟨m, n, hmn, hpow⟩ := (h _ (e.isCycleOn_range x)).exists_lt_map_eq_of_forall_mem
      (t := Set.range _) (f := fun k : ℕ ↦ (e ^ k) x) (fun k ↦ ⟨(k : ℤ), by simp⟩)
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  simpa [IsPeriodicPt, IsFixedPt, Perm.iterate_eq_pow,
    symm_pow_apply_pow_of_le e hmn.le] using congrArg (fun y ↦ (e.symm ^ m) y) hpow.symm

lemma finiteOrbit.finite_of_isCycleOn (ht : e.IsCycleOn t) (he : e.finiteOrbit) : t.Finite :=
  (finiteOrbit_iff_finite_of_isCycleOn e).mp he t ht

def skip (e : Equiv.Perm α) (s : Set α) [DecidablePred (· ∈ s)] (he : e.finiteOrbit) :
    Equiv.Perm α where
  toFun x := if hx : x ∈ s then x else
    let n := Nat.find (p := fun n ↦ 0 < n ∧ e^[n] x ∉ s) <| by
      obtain ⟨n, hn, h⟩ := he.isPeriodicPt x
      exact ⟨n, hn, by rwa [h]⟩
    (e^n) x
  invFun x := if hx : x ∈ s then x else
    let n := Nat.find (p := fun n ↦ 0 < n ∧ e.symm^[n] x ∉ s) <| by
      obtain ⟨n, hn, h⟩ := he.symm.isPeriodicPt x
      exact ⟨n, hn, by rwa [h]⟩
    (e.symm^n) x
  left_inv x := by
    simp only [Perm.iterate_eq_pow]
    split_ifs with hx hx'
    · rfl
    · generalize_proofs hn at hx'
      exact (Nat.find_spec hn |>.2 hx').elim
    generalize_proofs hex hex'
    have hmn : Nat.find hex' = Nat.find hex := by
      rw [Nat.find_eq_iff hex']
      refine ⟨⟨(Nat.find_spec hex).1, by simp [hx]⟩, fun m hm ⟨hmpos, hmout⟩ ↦ ?_⟩
      set n := Nat.find hex
      have hmout' : e^[n - m] x ∉ s := by simpa [hm.le] using hmout
      exact (Nat.find_min hex <| by omega) ⟨by omega, hmout'⟩
    rw [symm_pow_apply_pow_of_le e hmn.le, hmn]
    simp
  right_inv x := by
    simp only [Perm.iterate_eq_pow]
    split_ifs with hx hx'
    · rfl
    · generalize_proofs hn at hx'
      exact (Nat.find_spec hn |>.2 hx').elim
    generalize_proofs hex hex'
    have hmn : Nat.find hex' = Nat.find hex := by
      rw [Nat.find_eq_iff hex']
      refine ⟨⟨(Nat.find_spec hex).1, by simp [hx]⟩, fun m hm ⟨hmpos, hmout⟩ ↦ ?_⟩
      set n := Nat.find hex
      have hmout' : e.symm^[n - m] x ∉ s := by simpa [hm.le] using hmout
      exact (Nat.find_min hex <| by omega) ⟨by omega, hmout'⟩
    rw [apply_pow_symm_pow_comm, symm_pow_apply_pow_of_ge e hmn.le, hmn]
    simp

variable [DecidablePred (· ∈ s)]

@[simp]
lemma skip_apply_of_mem (he : e.finiteOrbit) (hx : x ∈ s) : e.skip s he x = x := by
  simp [skip, hx]

lemma skip_apply_not_mem (he : e.finiteOrbit) (hx : x ∉ s) :
    ∃ n > 0, e.skip s he x = (e ^ n) x ∧ (e ^ n) x ∉ s ∧ ∀ m, 0 < m → m < n → (e ^ m) x ∈ s := by
  let hex : ∃ k, 0 < k ∧ e^[k] x ∉ s := by
    obtain ⟨n, hn, h⟩ := he.isPeriodicPt x
    exact ⟨n, hn, by rwa [h]⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_, fun m hm hm' ↦ ?_⟩
  · simp only [skip, Perm.iterate_eq_pow, coe_fn_mk, hx, ↓reduceDIte]
  · simpa [Perm.iterate_eq_pow] using (Nat.find_spec hex).2
  have hmem : e^[m] x ∈ s := by
    by_contra hout
    exact (Nat.find_min hex hm') ⟨hm, hout⟩
  simpa [Perm.iterate_eq_pow] using hmem

lemma skip_apply_of_fixed (he : e.finiteOrbit) (hf : IsFixedPt e x) : e.skip s he x = x := by
  by_cases hx : x ∈ s
  · exact Equiv.skip_apply_of_mem he hx
  obtain ⟨n, -, hskip_eq, -, -⟩ := skip_apply_not_mem he hx
  exact hskip_eq ▸ pow_apply_eq_self_of_apply_eq_self hf n

lemma skip_mapsTo (he : e.finiteOrbit) (ht : e.IsCycleOn t) :
    Set.MapsTo (e.skip s he) (t \ s) (t \ s) := by
  intro x ⟨hxt, hxs⟩
  by_cases hx' : x ∈ s
  · exact absurd hx' hxs
  obtain ⟨n, -, hskip, hnout, -⟩ := skip_apply_not_mem he hx'
  simpa [hskip] using ⟨ht.1.mapsTo.perm_pow n hxt, hnout⟩

private lemma mem_of_pow_mem (ht : e.IsCycleOn t) (n : ℕ) (hx : (e ^ n) x ∈ t) : x ∈ t := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply] at hx
    exact ih (ht.apply_mem_iff.1 hx)

lemma skip_symm_mapsTo (he : e.finiteOrbit) (ht : e.IsCycleOn t) :
    Set.MapsTo (e.skip s he).symm (t \ s) (t \ s) := by
  intro x hx
  replace hx : e.skip s he ((Equiv.symm (skip e s he)) x) ∈ t \ s := by simp [hx]
  by_cases hz : (Equiv.symm (skip e s he)) x ∈ s
  · simp only [Equiv.skip_apply_of_mem he hz, mem_diff] at hx
    exact absurd hz hx.2
  obtain ⟨n, -, hskip, -, -⟩ := skip_apply_not_mem he hz
  refine ⟨mem_of_pow_mem ht n ?_, hz⟩
  simpa [hskip] using hx.1

lemma skip_bijOn (he : e.finiteOrbit) (ht : e.IsCycleOn t) :
    Set.BijOn (e.skip s he) (t \ s) (t \ s) :=
  ⟨skip_mapsTo he ht, (e.skip s he).injective.injOn, fun y hy =>
    ⟨(e.skip s he).symm y, skip_symm_mapsTo he ht hy, by simp⟩⟩

private lemma skip_sameCycle_pow (he : e.finiteOrbit) (ht : e.IsCycleOn t) (hx : x ∈ t \ s)
    (hy : (e ^ n) x ∈ t \ s) : SameCycle (e.skip s he) x ((e ^ n) x) := by
  revert x
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x hx hy
    obtain rfl | hnpos := n.eq_zero_or_pos
    · exact SameCycle.refl _ _
    obtain ⟨m₀, hmpos, hskip, hnout, hinter⟩ := skip_apply_not_mem he hx.2
    have hpow' : (e ^ (n - m₀)) ((e ^ m₀) x) = (e ^ n) x := by
      rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by grind)]
    have hstep : SameCycle (e.skip s he) x ((e ^ m₀) x) := ⟨(1 : ℤ), by simp [hskip]⟩
    exact hstep.trans (hpow' ▸ ih (n - m₀) (by omega) ⟨ht.1.mapsTo.perm_pow m₀ hx.1, hnout⟩
      (hpow' ▸ hy))

lemma skip_sameCycle (he : e.finiteOrbit) (ht : e.IsCycleOn t) (hx : x ∈ t \ s) (hy : y ∈ t \ s) :
    SameCycle (e.skip s he) x y := by
  obtain ⟨n, hn⟩ := ht.2 hx.1 hy.1
  obtain ⟨n, hn⟩ := ht.exists_pow_eq' (he.finite_of_isCycleOn ht) hx.1 hy.1
  exact hn ▸ skip_sameCycle_pow he ht hx (hn ▸ hy)

def keep (e : Equiv.Perm α) (s : Set α) [DecidablePred (· ∈ s)] (he : e.finiteOrbit) :
    Equiv.Perm α :=
  e.skip sᶜ he

@[simp]
lemma keep_apply_of_not_mem (he : e.finiteOrbit) (hx : x ∉ s) : e.keep s he x = x := by
  simpa [keep] using Equiv.skip_apply_of_mem (e := e) (s := sᶜ) he hx

lemma keep_apply_mem (he : e.finiteOrbit) (hx : x ∈ s) :
    ∃ n > 0, e.keep s he x = (e ^ n) x ∧ (e ^ n) x ∈ s ∧ ∀ m, 0 < m → m < n → (e ^ m) x ∉ s := by
  have hx' : x ∉ sᶜ := by simpa
  simpa [keep] using Equiv.skip_apply_not_mem (e := e) (s := sᶜ) he hx'

lemma keep_apply_of_fixed (he : e.finiteOrbit) (hf : IsFixedPt e x) : e.keep s he x = x := by
  exact skip_apply_of_fixed (s := sᶜ) he hf

lemma keep_mapsTo (he : e.finiteOrbit) (ht : e.IsCycleOn t) :
    Set.MapsTo (e.keep s he) (t ∩ s) (t ∩ s) := by
  convert skip_mapsTo (e := e) (s := sᶜ) he ht using 1 <;> ext x <;> simp

lemma keep_symm_mapsTo (he : e.finiteOrbit) (ht : e.IsCycleOn t) :
    Set.MapsTo (e.keep s he).symm (t ∩ s) (t ∩ s) := by
  convert skip_symm_mapsTo (e := e) (s := sᶜ) he ht using 1 <;> ext x <;> simp

lemma keep_bijOn (he : e.finiteOrbit) (ht : e.IsCycleOn t) :
    Set.BijOn (e.keep s he) (t ∩ s) (t ∩ s) := by
  convert skip_bijOn (e := e) (s := sᶜ) he ht using 1 <;> ext x <;> simp

lemma keep_sameCycle (he : e.finiteOrbit) (ht : e.IsCycleOn t) (hx : x ∈ t ∩ s) (hy : y ∈ t ∩ s) :
    SameCycle (e.keep s he) x y := by
  exact skip_sameCycle (e := e) (s := sᶜ) he ht (by simpa using hx) (by simpa using hy)

namespace Perm.IsCycleOn

lemma exists_pow_eq_of_finiteOrbit (he : e.finiteOrbit) (ht : IsCycleOn e t)
    (hx : x ∈ t) (hy : y ∈ t) : ∃ n, (e ^ n) x = y := he.exists_pow_eq_of_sameCycle (ht.2 hx hy)

theorem skip (he : e.finiteOrbit) (ht : IsCycleOn e t) (s : Set α) [DecidablePred (· ∈ s)] :
    IsCycleOn (e.skip s he) (t \ s) :=
  ⟨skip_bijOn he ht, fun _ hx _ hy ↦ skip_sameCycle he ht hx hy⟩

theorem keep (he : e.finiteOrbit) (ht : IsCycleOn e t) (s : Set α) [DecidablePred (· ∈ s)] :
    IsCycleOn (e.keep s he) (t ∩ s) :=
  ⟨keep_bijOn he ht, fun _ hx _ hy ↦ keep_sameCycle he ht hx hy⟩

end Perm.IsCycleOn

lemma finiteOrbit.skip (he : e.finiteOrbit) (s : Set α) [DecidablePred (· ∈ s)] :
    (e.skip s he).finiteOrbit := by
  rw [finiteOrbit_iff]
  intro x
  by_cases hx : x ∈ s
  · refine ⟨1, one_pos, ?_⟩
    simp [IsPeriodicPt, IsFixedPt, Equiv.skip_apply_of_mem he hx]
  let t := Set.range fun i : ℤ ↦ (e ^ i) x
  have ht : e.IsCycleOn t := e.isCycleOn_range x
  have hxt : x ∈ t \ s := ⟨⟨0, by simp⟩, hx⟩
  have hfin : (t \ s).Finite := (he.finite_of_isCycleOn ht).diff
  let u := hfin.toFinset
  have hu : (u : Set α) = t \ s := hfin.coe_toFinset
  have hcycle : (e.skip s he).IsCycleOn u := by
    simpa [hu] using ht.skip he s
  have hxu : x ∈ u := by
    rw [← Finset.mem_coe, hu]
    exact hxt
  refine ⟨u.card, Finset.card_pos.mpr ⟨x, hxu⟩, ?_⟩
  simp only [IsPeriodicPt, IsFixedPt, Perm.iterate_eq_pow]
  exact hcycle.pow_card_apply hxu

lemma finiteOrbit.keep (he : e.finiteOrbit) (s : Set α) [DecidablePred (· ∈ s)] :
    (e.keep s he).finiteOrbit := by
  simpa [Equiv.keep] using finiteOrbit.skip (e := e) he sᶜ

set_option linter.unusedSectionVars false in
lemma keep_finite_support (he : e.finiteOrbit) (hs : s.Finite) [DecidablePred (· ∈ s)] :
    {x | e.keep s he x ≠ x}.Finite :=
  hs.subset fun x hx ↦ by
    by_contra hxs
    exact hx (Equiv.keep_apply_of_not_mem he hxs)

lemma finiteOrbit.mul_of_finite_support_right (he : e.finiteOrbit) (hf : {x | f x ≠ x}.Finite) :
    (e * f).finiteOrbit := by
  rw [finiteOrbit_iff]
  intro x
  let supp : Set α := {y | f y ≠ y}
  let base : Set α := insert x supp
  let orbit : α → Set α := fun y ↦ Set.range fun i : ℤ ↦ (e ^ i) y
  let T : Set α := ⋃ y ∈ base, orbit y
  have hbase_fin : base.Finite := hf.insert x
  have hTfin : T.Finite := by
    exact hbase_fin.biUnion fun y _ ↦ he.finite_of_isCycleOn (e.isCycleOn_range y)
  have hxT : x ∈ T := by
    exact Set.mem_biUnion (mem_insert x supp) ⟨0, by simp⟩
  have hstep : ∀ {y}, y ∈ T → (e * f) y ∈ T := by
    intro y hy
    simp only [T, orbit, mem_iUnion, exists_prop, mem_range] at hy ⊢
    obtain ⟨a, ha, i, rfl⟩ := hy
    by_cases hfix : f ((e ^ i) a) = (e ^ i) a
    · refine ⟨a, ha, i + 1, ?_⟩
      rw [mul_apply, hfix, add_comm]
      simp [zpow_add]
    have hmem : f ((e ^ i) a) ∈ base := by
      refine mem_insert_iff.mpr (Or.inr ?_)
      intro hfix'
      exact hfix (f.injective hfix')
    refine ⟨f ((e ^ i) a), hmem, 1, ?_⟩
    simp
  have hpowT : ∀ n, ((e * f) ^ n) x ∈ T := by
    intro n
    induction n with
    | zero => simpa using hxT
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact hstep ih
  obtain ⟨m, n, hmn, hpow⟩ := hTfin.exists_lt_map_eq_of_forall_mem
    (t := T) (f := fun k : ℕ ↦ ((e * f) ^ k) x) hpowT
  refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  simpa [IsPeriodicPt, IsFixedPt, Perm.iterate_eq_pow,
    symm_pow_apply_pow_of_le (e * f) hmn.le] using
    congrArg (fun y ↦ ((e * f).symm ^ m) y) hpow.symm

lemma finiteOrbit.mul_of_finite_support_left (he : e.finiteOrbit) (hf : {x | f x ≠ x}.Finite) :
    (f * e).finiteOrbit := by
  have hf' : {x | f.symm x ≠ x}.Finite := by
    simpa [Perm.set_support_symm_eq] using hf
  simpa using (finiteOrbit.mul_of_finite_support_right (e := e.symm) (f := f.symm) he.symm hf').symm

end Equiv
