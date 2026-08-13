import Matroid.Connectivity.WIP.Basic

open Set Function

namespace Matroid.Fan

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {n i j : ℕ} {b b' c : Bool} {F : M.Fan}

/- Contractions preserve the property of being a fan, unless one of the ends is a joint
spanned by the contract-set. -/
@[simps!]
protected def contract (F : M.Fan) (X : Set α) (h4 : 4 ≤ F.length)
    (hX : _root_.Disjoint (F : Set α) X) (h0 : F.b = false → F[0] ∉ M.closure X)
    (hlast : F.c = false → F.getLast ∉ M.closure X) : (M ／ X).Fan :=
  have aux : ∀ i (hi : i + 2 < F.length), ((M ／ X).bDual (F.b != i.bodd)).IsTriangle
      {F[i], F[i + 1], F[i + 2]} := by
    intro i hi
    wlog hi' : i + 3 < F.length generalizing i F with aux
    · specialize aux F.reverse (by simpa) (by simpa) (by simpa) (by simpa) 0 (by grind) (by grind)
      simpa only [reverse_left, F.right_eq, show F.length = i + 3 by lia, Nat.bodd_succ,
        Bool.not_not, Nat.bodd_zero, Bool.bne_false, reverse_getElem, Nat.add_one_sub_one,
        tsub_zero, zero_add, add_tsub_cancel_right, Bool.beq_not] using aux.reverse
    have hFX (j) (hj : j < F.length) : F[j] ∉ X := hX.notMem_of_mem_left (by simp)
    obtain hb | hb := (F.b.eq_or_eq_not i.bodd).symm
    · simp [hb, show M.IsTriad _ from F.isTriangle_bDual_of_eq i (d := true) hi (by simp [hb]), hFX]
    suffices (M ／ X).IsTriangle {F[i], F[i + 1], F[i + 2]} by simpa [hb]
    wlog hXE : X ⊆ M.E generalizing X with aux
    · rw [← contract_inter_ground_eq]
      exact aux _ (by grind) (by simpa) (by simpa) (by grind) inter_subset_right
    have hT : M.IsTriangle {F[i], F[i + 1], F[i + 2]} := F.isTriangle_of_eq i hi (by simp [hb])
    refine hT.contract_isTriangle <| Skew.symm <| by_contra fun hcon ↦ ?_
    obtain ⟨C, hC, hCss, hiC, hCX⟩ :=
      hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew (e := F[i])
      ((hX.mono_left (by simp [insert_subset_iff]))) hcon (by simp)
    have h2 : F[i + 1 + 2] ∉ C := fun h2 ↦ (hCss h2).elim (by simp [add_assoc]) <| hFX _ _
    have hiff := (F.isTriangle_bDual_of_eq (i + 1) (d := true) (by lia)
      (by simp [hb])).reverse.mem_iff_mem_of_isCircuit_bDual hC h2
    by_cases h1c : F[i + 1] ∈ C
    · obtain rfl : C = {F[i], F[i + 1], F[i + 2]} :=
        hC.eq_of_superset_isCircuit hT.isCircuit (by simp [insert_subset_iff, hiff, h1c, hiC])
      exact hCX.not_disjoint <| hX.mono_left <| by simp [insert_subset_iff]
    rw [iff_false_intro h1c, iff_false] at hiff
    obtain rfl | i := i
    · grw [insert_comm, insert_union, subset_insert_iff_of_notMem h1c, pair_comm,
          insert_union, subset_insert_iff_of_notMem hiff, ← sdiff_subset_iff] at hCss
      refine h0 hb ?_
      grw [← hCss]
      exact hC.mem_closure_sdiff_singleton_of_mem hiC
    refine h1c ?_
    rwa [← (F.isTriangle_bDual_of_eq i (d := true) (by lia)
      (by simp [hb])).mem_iff_mem_of_isCircuit_bDual hC]
    exact fun hiC' ↦ (hCss hiC').elim (by simp [add_assoc]) <| hX.notMem_of_mem_left <| by simp
  Fan.mk (F : List α) F.b F.c F.nodup (by lia) F.length_bodd (by lia) aux

@[simp, grind! .] lemma contract_length (F : M.Fan) {X h4 hX h0 hlast} :
    (F.contract X h4 hX h0 hlast).length = F.length := rfl

@[simp] lemma contract_toSet (F : M.Fan) {X h4 hX h0 hlast} :
    (F.contract X h4 hX h0 hlast : Set α) = F := rfl

@[simp] lemma contract_getElem (F : M.Fan) {X h4 hX h0 hlast} {i hi} :
    (F.contract X h4 hX h0 hlast)[i]'hi = F[i]'(show i < F.length from hi) := rfl

@[simps!]
protected def delete (F : M.Fan) (X : Set α) (h4 : 4 ≤ F.length)
    (hX : _root_.Disjoint (F : Set α) X) (h0 : F.b = true → F[0] ∉ M✶.closure X)
    (hlast : F.c = true → F.getLast ∉ M✶.closure X) : (M ＼ X).Fan :=
  (F.dual.contract X (by simpa) (by simpa) (by simpa) (by simpa)).dual.copy _ <| by simp

@[simp, grind! .] lemma delete_length (F : M.Fan) {X h4 hX h0 hlast} :
    (F.delete X h4 hX h0 hlast).length = F.length := rfl

@[simp] lemma delete_toSet (F : M.Fan) {X h4 hX h0 hlast} :
    (F.delete X h4 hX h0 hlast : Set α) = F := rfl

@[simp] lemma delete_getElem (F : M.Fan) {X h4 hX h0 hlast} {i hi} :
    (F.delete X h4 hX h0 hlast)[i]'hi = F[i]'(show i < F.length from hi) := rfl

@[simps!]
protected def restrict (F : M.Fan) (R : Set α) (h4 : 4 ≤ F.length) (hX : (F : Set α) ⊆ R)
    (h0 : F.b = true → F[0] ∉ M✶.closure (M.E \ R))
    (hlast : F.c = true → F.getLast ∉ M✶.closure (M.E \ R)) : (M ↾ R).Fan :=
  have aux : ∀ (i : ℕ) (hi : i + 2 < F.length),
      ((M ↾ R).bDual (F.b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
    intro i hi
    obtain hb | hb := F.b.eq_or_eq_not i.bodd
    · simp only [hb, bne_self_eq_false, Matroid.bDual_false]
      grw [isTriangle_restrict_iff, ← hX, and_iff_left (by simp [insert_subset_iff])]
      exact F.isTriangle_of_eq i hi hb.symm
    simp only [hb, Bool.not_bne, bne_self_eq_false, Bool.not_false, Matroid.bDual_true,
      dual_isTriangle_iff]
    have hT' := (F.delete (M.E \ R) h4 (by grind) (by simpa) (by simpa)).isTriangle_bDual_of_eq i
      (d := true) (by simpa) (by simp [hb])
    simp only [Matroid.bDual_true, dual_delete, delete_getElem] at hT'
    refine ⟨?_, hT'.2⟩
    rw [restrict_eq_delete_disjointSum_loopyOn]
    generalize_proofs h
    simp [disjointSum_dual, dual_delete, disjointSum_isCircuit_iff, hT'.isCircuit]
  Fan.mk (F : List α) F.b F.c F.nodup (by lia) F.length_bodd (by lia) aux

@[simp, grind! .] lemma restrict_length (F : M.Fan) {X h4 hX h0 hlast} :
    (F.restrict X h4 hX h0 hlast).length = F.length := rfl

@[simp] lemma restrict_toSet (F : M.Fan) {X h4 hX h0 hlast} :
    (F.restrict X h4 hX h0 hlast : Set α) = F := rfl

@[simp] lemma restrict_getElem (F : M.Fan) {X h4 hX h0 hlast} {i hi} :
    (F.restrict X h4 hX h0 hlast)[i]'hi = F[i]'(show i < F.length from hi) := rfl

/-- Contract the head of a fan to get a smaller fan, provided various side-conditions hold.
The side conditions for length-`3` and length-`4` fans are automatically discharged by `lia`
in cases where `F` is known to be longer than that. -/
@[simps!]
def contractHead (F : M.Fan) (hl : 3 ≤ F.length) (h_init : F.b = true → ¬ M.Parallel F[0] F[1])
    (h_pair : F.b = false → F.c = false → ¬ M.Parallel F[0] F.getLast)
    (h4 : F.length = 4 → F.b = true → ¬ F[0] ∈ M.closure {F[1], F[2]} := by lia)
    (h3 : F.length = 3 → F.b = true → ¬ M.Parallel F[0] F[2] := by lia) :
    (M ／ {F[0]}).Fan where
  toList := (F : List α).tail
  b := !F.b
  c := F.c
  toList_nodup := F.nodup.tail
  toList_length_ge := by grind
  toList_length_bodd := by simp [F.length_sub_one_bodd_eq]
  isNonloop' hl i hi d := by
    simp only [List.length_tail, length_toList, Nat.pred_eq_succ_iff, Nat.reduceAdd] at hl
    have hi : i = 0 ∨ i = 1 := by simpa [hl, Nat.le_one_iff_eq_zero_or_eq_one] using hi
    cases d with
    | false =>
      suffices ¬ M.Parallel F[i + 1] F[0] by simpa [← F.isNonloop.parallel_iff_mem_closure]
      intro hp
      cases h : F.b
      · simpa [hi] using (F.isTriangle_of_eq 0 (by lia) h.symm).eq_of_parallel_mem_mem hp.symm
      obtain rfl | rfl := hi
      · exact h_init h hp.symm
      exact h3 hl h hp.symm
    | true => simp [show M.IsNonColoop F[i + 1] from F.isNonloop_bDual (d := true)]
  isTriangle' i hi := by
    by_cases hF4 : F.length = 4
    · obtain rfl : i = 0 := by grind
      cases h : F.b
      · simp [show M.IsTriad _ from F.isTriangle_bDual_of_eq 1 true (by lia) (by simpa)]
      suffices (M ／ {F[0]}).IsTriangle {F[1], F[2], F[3]} by simpa
      have hT := F.isTriangle_of_eq 1 (by lia) h.symm
      refine hT.contract_isTriangle <| ?_
      rw [F.isNonloop.skew_left_iff, pair_comm, insert_comm, closure_insert_eq_of_mem_closure
        hT.mem_closure₃]
      exact h4 hF4 h
    have hlt : i + 3 < F.length := by grind
    set F' := (F.tail (by grind)).contract {F[0]} (by grind) (by simp)
      (by simpa [← F.isNonloop.parallel_iff_mem_closure, parallel_comm (e := F[1])])
      (by
        suffices aux : F.c = false → ¬M.Parallel F[0] F[F.length - 1] by
          simpa [F.getLast_eq_getElem, ← F.isNonloop.parallel_iff_mem_closure, parallel_comm]
        intro hc hpara
        cases hb : F.b
        · exact h_pair hb hc <| F.getLast_eq_getElem ▸ hpara
        obtain hlen : F.length - 1 = 0 ∨ F.length = 2 ∨ F.length = 3 := by
          simpa using (F.isTriangle_bDual_of_eq 0 true (by lia)
          (by simpa)).isCircuit.mem_iff_mem_of_parallel_bDual hpara
        lia)
    have hwin := F'.isTriangle i (by grind)
    simpa [F'] using hwin

@[simp, grind! .] lemma contractHead_length (F : M.Fan) {h₁ h₂ h₃ h₄ h₅} :
    (F.contractHead h₁ h₂ h₃ h₄ h₅).length = (F.tail h₁).length := rfl

@[simp]
lemma contractHead_toSet (F : M.Fan) {h₁ h₂ h₃ h₄ h₅} :
    (F.contractHead h₁ h₂ h₃ h₄ h₅ : Set α) = (F : Set α) \ {F[0]} := by
  change {e | e ∈ F.tail h₁} = _
  simp

@[simp]
lemma contractHead_getElem (F : M.Fan) {h₁ h₂ h₃ h₄ h₅} {i hi} :
    (F.contractHead h₁ h₂ h₃ h₄ h₅)[i]'hi = F[i + 1]'(show i + 1 < F.length by grind) :=
  F.getElem_tail h₁ _

@[simp]
lemma contractHead_getLast (F : M.Fan) {h₁ h₂ h₃ h₄ h₅} :
    (F.contractHead h₁ h₂ h₃ h₄ h₅).getLast = F.getLast :=
  F.getLast_tail h₁

@[simp]
lemma contractHead_getPenult (F : M.Fan) {h₁ h₂ h₃ h₄ h₅} :
    (F.contractHead h₁ h₂ h₃ h₄ h₅).getPenult = F.getPenult :=
  F.getPenult_tail h₁

/-- If `N` is a minor of `M`, and `F` is a fan of `M` contained in `E(N)`, whose (co)joint ends are
are not (co)loops of `N`, then `F` is also a fan of `N`.  -/
@[simps!]
protected def toMinor {N : Matroid α} (F : M.Fan) (h4 : 4 ≤ F.length) (hNM : N ≤m M)
    (hFN : (F : Set α) ⊆ N.E) (h_first : (N.bDual F.b).IsNonloop F[0])
    (h_last : (N.bDual F.c).IsNonloop F.getLast) : N.Fan :=
  have aux : ∀ (i : ℕ) (hi : i + 2 < F.length),
      (N.bDual (F.b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
    intro i hi
    obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_contract_indep_delete_coindep
    simp only [delete_ground, contract_ground, subset_sdiff] at hFN
    set F₁ := F.contract C h4 hFN.1.2 (fun hb h0C ↦ by simp [hb, h0C] at h_first)
      (fun hc h0C ↦ by simp [hc, h0C] at h_last)
    set F₂ := F₁.delete D (show 4 ≤ F₁.length by simpa) (by simpa [F₁] using hFN.2)
      (by
        intro (hb : F.b = true) (hcl : F[0] ∈ (M ／ C)✶.closure D)
        simp only [dual_contract, delete_closure_eq, mem_sdiff] at hcl
        simp [hb, hcl] at h_first)
      (by
        intro (hc : F.c = true) (hcl : F.getLast ∈ _)
        simp only [dual_contract, delete_closure_eq, mem_sdiff] at hcl
        simp [hc, hcl.1, hcl.2] at h_last)
    simpa [F₁, F₂] using! F₂.isTriangle i (by simpa [F₂, F₁])
  Fan.mk (F : List α) F.b F.c F.nodup (by lia) F.length_bodd (by lia) aux
