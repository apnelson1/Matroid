-- import Mathlib.Data.Set.Finite.Basic -- inefficient import
module

public import Mathlib.Data.Finset.Powerset -- inefficient import
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section
-- import Mathlib.Data.Fintype.Lattice
-- import Mathlib.Data.Int.Cast.Basic
-- import Mathlib.Algebra.Group.Int
-- import Mathlib.Algebra.Ring.Int

variable {α β : Type*} {s t r : Finset α} {a b : α}

namespace Finset

variable [DecidableEq α]

lemma sdiff_erase_notMem (h : a ∉ s) : s \ t.erase a = s \ t := by
  rw [sdiff_eq_sdiff_iff_inter_eq_inter, inter_erase, erase_eq_of_notMem (by simp [h])]

lemma sdiff_subset_iff : s \ t ⊆ r ↔ s ⊆ t ∪ r := by
  simp [← coe_subset, Set.sdiff_subset_iff]

lemma pair_sdiff_left (hne : a ≠ b) : ({a, b} : Finset α) \ ({a} : Finset α) = {b} := by
  aesop

lemma pair_sdiff_right (hne : a ≠ b) : ({a, b} : Finset α) \ ({b} : Finset α) = {a} :=
  Finset.pair_comm a b ▸ Finset.pair_sdiff_left hne.symm

lemma erase_eq_empty_of_mem {s : Finset α} {a : α} (h : a ∈ s) :
    Finset.erase s a = ∅ ↔ s = {a} := by
  rw [Finset.erase_eq_empty_iff, or_iff_right_iff_imp]
  aesop

lemma coe_card_inter (s : Finset α) (t : Finset α) :
    (s ∩ t).card = (s.card : ℤ) + t.card - (s ∪ t).card := by
  rw [Finset.card_inter, Int.natCast_sub, Int.natCast_add]
  exact card_union_le s t

lemma singleton_subset_inter_and_union_subset_singleton {s t : Finset α} {e : α}
    (h : {e} ⊆ s ∩ t) (h' : s ∪ t ⊆ {e}) : s = {e} ∧ t = {e} := by
  refine ⟨?_, ?_⟩
  · exact Subset.antisymm (Finset.union_subset_left h') (h.trans Finset.inter_subset_left)
  · exact Subset.antisymm (Finset.union_subset_right h') (h.trans Finset.inter_subset_right)

omit [DecidableEq α] in
lemma singleton_of_mem_card_le_one {e : α} {s : Finset α} (hs : s.card ≤ 1)
    (he : e ∈ s) : s = {e} := by
  ext x; refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [(card_le_one_iff.mp hs) he h, mem_singleton]
  rwa [mem_singleton.mp h]

lemma inter_ssubset_of_not_subset_left {s t : Finset α} (h : ¬s ⊆ t) : s ∩ t ⊂ s := by
  refine ssubset_iff_subset_ne.mpr ⟨inter_subset_left, ?_⟩
  contrapose! h
  rwa [inter_eq_left] at h

lemma inter_ssubset_of_not_subset_right {s t : Finset α} (h : ¬t ⊆ s) : s ∩ t ⊂ t := by
  rw [inter_comm]; exact inter_ssubset_of_not_subset_left h

-- lemma exists_minimal_satisfying_subset (P : Finset α → Prop) {s : Finset α}
--     {e : Finset α} (he : e ⊆ s) (hP : P e) : ∃ a ⊆ s, P a ∧ ∀ ⦃a'⦄, P a' → a' ⊆ a → a ⊆ a' := by
--   set S := {a | a ⊆ s ∧ P a}
--   have h_fin : Set.Finite S := s.powerset.finite_toSet.subset (by
--     intro a ha; simp only [mem_coe, mem_powerset]; exact ha.1)
--   have : Set.Nonempty S := by use e; exact ⟨he, hP⟩
--   obtain ⟨a, h₁, h₂⟩ := h_fin.toFinset.exists_minimal (h_fin.toFinset_nonempty.mpr this)
--   simp only [Set.Finite.mem_toFinset, lt_eq_subset, S, Set.mem_ofPred_eq, and_imp] at h₁ h₂
--   use a
--   refine ⟨h₁.1, h₁.2, fun a' h ha' ↦ ?_⟩
--   specialize h₂ a' (ha'.trans h₁.1) h
--   rw [Finset.ssubset_def] at h₂
--   push_neg at h₂
--   exact h₂ ha'

lemma finset_biUnion_union (s t : Finset α) (u : α → Finset β) [DecidableEq β]:
    (s ∪ t).biUnion u = s.biUnion u ∪ t.biUnion u := by
  aesop

lemma finset_biUnion_inter (s t : Finset α) (u : α → Finset β) [DecidableEq β]:
    (s ∩ t).biUnion u ⊆ s.biUnion u ∩ t.biUnion u := by
  simp only [biUnion_subset_iff_forall_subset]
  intro x h
  obtain ⟨hs, ht⟩ := mem_inter.mp h
  refine subset_inter ?_ ?_ <;> intro a ha <;> aesop

lemma erase_inter_distrib (s : Finset α) (t : Finset α) (a : α) :
    (s ∩ t).erase a = s.erase a ∩ t.erase a := by
  aesop

@[simp] lemma coe_nontrivial {α : Type*} {s : Finset α} :
    (s : Set α).Nontrivial ↔ s.Nontrivial := by
  rfl

lemma subset_range_two {P : Finset ℕ} (hP : P ⊆ Finset.range 2) :
    P = ∅ ∨ P = {0} ∨ P = {1} ∨ P = {0, 1} := by
  rw [Finset.range_add_one, Finset.range_one] at hP
  grind

end Finset

lemma List.toFinset_subset [DecidableEq α] {a b : List α} (hab : a ⊆ b) :
    a.toFinset ⊆ b.toFinset :=
  fun i hi ↦ by simpa using hab <| by simpa using hi

/-- A relation that joins adjacent intervals holds across an interval if it holds on each
successive gap of a finite set of cut points. The gaps are the subintervals whose endpoints lie in
`{a, b} ∪ F` and whose interiors avoid `F`. -/
theorem Finset.interval_induction [LinearOrder α] {F : Finset α} {R : α → α → Prop}
    (hjoin : ∀ a c b, a < c → c < b → R a c → R c b → R a b) (hab : a < b)
    (hgap : ∀ s t, a ≤ s → s < t → t ≤ b → (s = a ∨ s ∈ F) → (t = b ∨ t ∈ F) →
      (∀ u ∈ F, u ∉ Set.Ioo s t) → R s t) : R a b := by
  induction F using Finset.induction_on generalizing a b with
  | empty => exact hgap a b le_rfl hab le_rfl (Or.inl rfl) (Or.inl rfl) (by simp)
  | @insert c F hc ih =>
    by_cases hcI : c ∈ Set.Ioo a b
    · refine hjoin a c b hcI.left hcI.right
        (ih hcI.left fun s t has hst htc hs ht hcut ↦ hgap s t has hst (htc.trans hcI.right.le)
          (hs.imp_right Finset.mem_insert_of_mem)
          (Or.inr <| ht.elim (fun h => h ▸ Finset.mem_insert_self c F) Finset.mem_insert_of_mem) ?_)
        (ih hcI.right fun s t hcs hst htb hs ht hcut ↦ hgap s t (hcI.left.le.trans hcs) hst htb
          (Or.inr <| hs.elim (fun h => h ▸ Finset.mem_insert_self c F) Finset.mem_insert_of_mem)
          (ht.imp_right Finset.mem_insert_of_mem) ?_)
        <;> intro u hu <;> rcases Finset.mem_insert.mp hu with rfl | hu <;> grind
    refine ih hab fun s t has hst htb hs ht hcut ↦ hgap s t has hst htb
      (hs.imp_right Finset.mem_insert_of_mem) (ht.imp_right Finset.mem_insert_of_mem) fun u hu ↦ ?_
    obtain rfl | hu := Finset.mem_insert.mp hu
    · exact fun hu ↦ hcI ⟨has.trans_lt hu.1, hu.2.trans_le htb⟩
    exact hcut u hu
