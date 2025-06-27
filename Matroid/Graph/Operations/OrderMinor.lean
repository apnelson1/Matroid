import Matroid.Graph.Map
import Mathlib.SetTheory.Ordinal.Basic


variable {ι α β : Type*}

lemma LinearOrder_nonempty (α : Type*) : Nonempty (LinearOrder α) :=
  let ⟨_, wo, _⟩ := Cardinal.ord_eq α
  Nonempty.intro wo.linearOrder

noncomputable def extend_LinearOrder_of_LinearOrder_ne (x : α) [r : LinearOrder {a : α // a ≠ x}] :
    {r' : LinearOrder α // IsBot x ∧ ∀ a b, r.le a b ↔ r'.le a b} := by
  classical
  let Eqv : WithBot { b // b ≠ x } ≃ α := Equiv.optionSubtypeNe x
  refine ⟨LinearOrder.lift' Eqv.symm Eqv.symm.injective, fun a => ?_, fun a b => ?_⟩
  unfold instDistribLatticeOfLinearOrder LinearOrder.toLattice LinearOrder.lift' LinearOrder.lift
    PartialOrder.lift Preorder.lift
  simp only [Lattice.toSemilatticeInf, ne_eq, EmbeddingLike.apply_eq_iff_eq, Eqv]
  have : Eqv.symm x = ⊥ := Equiv.optionSubtypeNe_symm_self x
  exact this ▸ bot_le

  · change r.le a b ↔ Eqv.symm a ≤ Eqv.symm b
    have ha : Eqv.symm a = a := Equiv.optionSubtypeNe_symm_of_ne a.prop
    have hb : Eqv.symm b = b := Equiv.optionSubtypeNe_symm_of_ne b.prop
    simp [ha, hb]

lemma LinearOrder_nonempty_of_bot (x : α) : Nonempty {r : LinearOrder α // IsBot x} := by
  classical
  have := (LinearOrder_nonempty {a : α // a ≠ x}).some
  obtain ⟨r, hr, -⟩ := extend_LinearOrder_of_LinearOrder_ne x
  refine Nonempty.intro ⟨r, hr⟩

-- lemma LinerOrder_nonempty_of_list {α : Type*} (l : List α) :
--     Nonempty {r : LinearOrder α // Monotone l.idxOf} := by
--   classical
--   match l with
--   | [] =>
--     obtain ⟨r⟩ := LinearOrder_nonempty α
--     exact ⟨r, by simp [monotone_const]⟩
--   | x :: xs =>
--     let xs' : List {a : α // a ≠ x} := xs.filter (· ≠ x) |>.pmap Subtype.mk (fun a _ => by simp_all)
--     have : (List.filter (fun x_1 ↦ !decide (x_1 = x)) xs).length < xs.length + 1 := by
--       have := List.length_filter_le (fun x_1 ↦ !decide (x_1 = x)) xs
--       omega
--     obtain ⟨r, hr⟩ := LinerOrder_nonempty_of_list (α := {a : α // a ≠ x}) xs'
--     obtain ⟨r', hr', hr'eq⟩ := extend_LinearOrder_of_LinearOrder_ne x
--     refine ⟨r', fun a b hab => ?_⟩
--     obtain ha | ha := eq_or_ne a x
--     · subst a
--       simp only [List.idxOf_cons_self, zero_le]
--     change r'.le a b at hab
--     have hb : b ≠ x := by
--       rintro rfl
--       exact ha <| le_antisymm hab <| hr' a
--     have hiff : r.le ⟨a, ha⟩ ⟨b, hb⟩ ↔ r'.le a b := hr'eq ⟨a, ha⟩ ⟨b, hb⟩
--     have hle := hr <| hiff.mpr hab
--     simp only [ne_eq, decide_not, List.idxOf_cons_ne _ ha.symm, Nat.succ_eq_add_one,
--       List.idxOf_cons_ne _ hb.symm, add_le_add_iff_right, ge_iff_le, xs'] at hle ⊢
--     have hle' : List.idxOf a (xs.filter (· ≠ x)) ≤ List.idxOf b (xs.filter (· ≠ x)) := by sorry
--     sorry
-- termination_by l.length
-- decreasing_by simp; convert this

namespace Graph
open Set Function

variable [LinearOrder α] {G H : Graph α β} {C C' : Set β}


