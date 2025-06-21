
import Mathlib.Data.Matroid.Minor.Restrict
import Mathlib.Data.Fintype.Basic
import Matroid.ForMathlib.Finset
import Matroid.ForMathlib.Function
import Matroid.ForMathlib.Matroid.Basic
import Matroid.Rank.Nat

open Set Function

namespace Matroid

variable {α β : Type*} {M : Matroid α} {Adj : α → β → Prop} {f : β → α} {v : β} {I J : Finset β}

def IsMatching (Adj : α → β → Prop) (f : β → α) (I : Set α) (J : Set β) :=
  BijOn f J I ∧ (∀ v ∈ J, Adj (f v) v)

lemma IsMatching.adj {I₀ : Set α} {I : Set β} (h : IsMatching Adj f I₀ I) (hv : v ∈ I) :
    Adj (f v) v :=
  h.2 v hv

lemma IsMatching.bijOn {I₀ : Set α} {I : Set β} (h : IsMatching Adj f I₀ I) : BijOn f I I₀ :=
  h.1

lemma IsMatching.card_eq {I₀ : Finset α} {I : Finset β} (h : IsMatching Adj f I₀ I) :
    I₀.card = I.card := by
  classical
  rw [← Finset.card_image_of_injOn h.bijOn.injOn]
  congr
  simp [← Finset.coe_inj, h.bijOn.image_eq]

/-- `I : Finset β` is `AdjIndep` relative to `M : Matroid α` and `Adj : α → β → Prop`
if `I` is matchable to an `M`-independent set using edges in `Adj`. -/
def AdjIndep (M : Matroid α) (Adj : α → β → Prop) (I : Finset β) :=
  I = ∅ ∨ ∃ (I₀ : Finset α) (f : β → α), M.Indep I₀ ∧ IsMatching Adj f I₀ I

lemma AdjIndep.exists [Nonempty α] {I : Finset β} (h : M.AdjIndep Adj I) :
    ∃ (I₀ : Finset α) (f : β → α), M.Indep I₀ ∧ IsMatching Adj f I₀ I := by
  obtain (rfl | h) := h
  · exact ⟨∅, Classical.arbitrary _, by simp [IsMatching]⟩
  exact h

lemma AdjIndep.subset (hI : M.AdjIndep Adj I) (hJI : J ⊆ I) : M.AdjIndep Adj J := by
  classical
  obtain (rfl | ⟨I₀, f, h₀, hf⟩) := hI
  · exact .inl (Finset.subset_empty.1 hJI)
  refine .inr ⟨I₀ ∩ J.image f, f, h₀.subset <| by simp, ?_,
    fun v hv ↦ hf.adj (mem_of_mem_of_subset hv (by simpa))⟩
  convert hf.bijOn.subset_right (r := I₀ ∩ J.image f) (by simp)
  · rw [Finset.coe_image, preimage_inter, ← hf.bijOn.image_eq, ← inter_assoc,
      inter_comm (a := (I : Set β)), hf.bijOn.injOn.preimage_image_inter Subset.rfl,
      inter_comm, hf.bijOn.injOn.preimage_image_inter (by simpa)]
  simp

lemma AdjIndep.augment [DecidableEq β] (hI : M.AdjIndep Adj I) (hJ : M.AdjIndep Adj J)
  (hIJ : I.card < J.card) : ∃ e ∈ J, e ∉ I ∧ M.AdjIndep Adj (insert e I) := by
  obtain (hα | hα) := isEmpty_or_nonempty α
  · simp only [AdjIndep, show J ≠ ∅ by rintro rfl; simp at hIJ, exists_and_left, false_or] at hJ
    obtain ⟨J₀, -, f, hf⟩ := hJ
    simp [← hf.card_eq, J₀.eq_empty_of_isEmpty] at hIJ
  classical
  let T := (β → α) × Finset α
  set S := {w : T × T | M.Indep w.1.2 ∧ IsMatching Adj w.1.1 w.1.2 I ∧
    M.Indep w.2.2 ∧ IsMatching Adj w.2.1 w.2.2 J}
  have hSne : S.Nonempty := by
    obtain ⟨I₀, f, h⟩ := hI.exists
    obtain ⟨J₀, g, h'⟩ := hJ.exists
    exact ⟨⟨⟨f, I₀⟩, ⟨g, J₀⟩⟩, by simp [h.1, h'.1, S, h'.2, h.2]⟩
  set φ : T × T → Finset β := fun w ↦ ((I ∩ J).filter (fun x ↦ w.1.1 x = w.2.1 x))
  have him : (φ '' S).Finite := by
    refine (I ∩ J).powerset.finite_toSet.subset ?_
    rintro _ ⟨⟨P,Q⟩,-,rfl⟩
    simp +contextual [φ, subset_def]

  obtain ⟨⟨⟨f, I₀⟩,⟨g, J₀⟩⟩, ⟨hI₀, hf, hJ₀, hg⟩, hmax⟩ :=
    Set.Finite.exists_maximalFor' φ S him hSne

  simp only at hf hg hI₀ hJ₀

  rw [← hf.card_eq, ← hg.card_eq] at hIJ
  obtain ⟨x, hxJ₀, hxI₀, hxI⟩ := hI₀.augment_finset hJ₀ hIJ

  obtain ⟨y, hyJ, hyI, rfl⟩ : ∃ y, y ∈ J ∧ y ∉ I ∧ g y = x := by
    obtain ⟨y, hy : y ∈ J, rfl⟩ := hg.bijOn.image_eq.symm.subset hxJ₀
    refine ⟨y, hy, fun hyI ↦ ?_, rfl⟩
    set I₀' := insert (g y) (I₀ \ {f y}) with hI₀'
    set f' := update f y (g y) with hf'

    specialize @hmax ⟨⟨f', I₀'⟩, ⟨g, J₀⟩⟩ ⟨hxI.subset ?_, ?_, hJ₀, hg⟩
    · simp only [hI₀', Finset.coe_insert, Finset.coe_sdiff, Finset.coe_singleton]
      exact insert_subset_insert diff_subset
    · simp only [hI₀', Finset.coe_insert, Finset.coe_sdiff, Finset.coe_singleton, f']
      refine ⟨hf.bijOn.bijOn_update hyI hxI₀, fun v hvs ↦ ?_⟩
      obtain (rfl | hne) := eq_or_ne v y
      · simp [hg.adj hy]
      rw [update_of_ne hne]
      exact hf.adj hvs

    simp only [Finset.le_eq_subset, Finset.subset_iff, Finset.mem_filter, Finset.mem_inter, and_imp,
      Finset.ext_iff, and_congr_right_iff, φ, f'] at hmax

    specialize hmax (fun a haI haJ ha ↦ ⟨⟨haI, haJ⟩, ?_⟩) hyI hy
    · simp_rw [update_apply, ← ha, ite_eq_right_iff, ha, eq_comm]
      apply congr_arg
    simp only [update_self, forall_const, S, f', φ, T] at hmax
    rw [← hmax.2] at hxI₀
    exact hxI₀ <| hf.bijOn.image_eq.subset (mem_image_of_mem _ hyI)

  refine ⟨y, hyJ, hyI, .inr ⟨insert (g y) I₀, update f y (g y), by simpa, ?_, ?_⟩⟩
  · nth_rw 2 [show g y = update f y (g y) y by simp]
    simp only [Finset.coe_insert]
    apply BijOn.insert_notMem ?_ (by simpa) (by simpa)
    exact hf.bijOn.congr fun a haI ↦ by rw [update_of_ne (by rintro rfl; contradiction)]

  simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, forall_eq_or_imp, update_self,
    hg.adj hyJ, true_and]
  intro a haI
  rw [update_of_ne (by rintro rfl; contradiction)]
  exact hf.adj haI

/-- Given `M : Matroid α` and a graph `H` with bipartition `(α, β)` described by an
adjacency predicate `Adj : α → β → Prop`,
`M.adjMap Adj E` is the finitary matroid on `β` with ground set `E`
whose finite independent sets are those `H`-matchable to an independent set of `M`.
This doesn't require `M` to be finitary to be well-defined,
but only depends on the collection of finite independent sets of `M`.
This construction fails to be a matroid if we try to allow infinite sets to be independent;
see the docstring of `Data.Matroid.Map`. -/
def adjMap [DecidableEq β] (M : Matroid α) (Adj : α → β → Prop) (E : Set β) : Matroid β :=
  (IndepMatroid.matroid <| IndepMatroid.ofFinset univ (M.AdjIndep Adj) (.inl rfl)
    (fun _ _ ↦ Matroid.AdjIndep.subset) (fun _ _ ↦ Matroid.AdjIndep.augment) (by simp)) ↾ E

@[simp] lemma adjMap_indep_iff [DecidableEq β] (M : Matroid α) (Adj : α → β → Prop) (E : Set β)
    {I : Finset β} : (M.adjMap Adj E).Indep I ↔ M.AdjIndep Adj I ∧ (I : Set β) ⊆ E := by
  simp [adjMap]

@[simp] lemma adjMap_ground_eq [DecidableEq β] (M : Matroid α) (Adj : α → β → Prop) (E : Set β) :
  (M.adjMap Adj E).E = E := rfl

/-- `M.adjMap Adj E` is finitary. -/
instance [DecidableEq β] (M : Matroid α) (Adj : α → β → Prop) (E : Set β) :
    Finitary (M.adjMap Adj E) := by
  rw [adjMap, IndepMatroid.ofFinset]
  infer_instance
