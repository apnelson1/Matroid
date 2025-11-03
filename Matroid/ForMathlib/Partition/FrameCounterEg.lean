import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.Order.WithBot
import Matroid.ForMathlib.Partition.Basic


-- There is a complete lattice α where Partition α does not have a well-defined sup.
def counterExample' : Type := {x : Fin 3 × Fin 3 // x.1.val + x.2 ≤ 2}

instance : SemilatticeSup counterExample' where
  le x y := y.1.1 ≤ x.1.1 ∧ y.1.2 ≤ x.1.2
  le_refl x := ⟨le_rfl, le_rfl⟩
  le_trans x y z hxy hyz := ⟨hyz.1.trans hxy.1, hyz.2.trans hxy.2⟩
  le_antisymm x y hxy hyx := by
    cases x with | mk x₁ x₂ =>
    cases x₁ with | mk x₁₁ x₁₂ =>
    cases y with | mk y₁ y₂ =>
    cases y₁ with | mk y₁₁ y₁₂ =>
    congr
    · exact hyx.1.antisymm hxy.1
    · exact hyx.2.antisymm hxy.2
  sup x y := match x, y with
    | ⟨⟨x1, x2⟩, hx⟩, ⟨⟨y1, y2⟩, hy⟩ => ⟨⟨min x1 y1, min x2 y2⟩, by simp_all; omega⟩
  le_sup_left := by
    rintro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩
    simp
  le_sup_right := by
    rintro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩
    simp
  sup_le := by
    rintro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩ ⟨⟨z1, z2⟩, hz⟩
    simp only [le_inf_iff, and_imp]
    omega

instance : OrderTop counterExample' where
  top := ⟨(0, 0), by simp⟩
  le_top x := ⟨bot_le, bot_le⟩

instance : Fintype counterExample' := Subtype.fintype _

def counterExample : Type := WithBot counterExample'

namespace counterExample

instance : SemilatticeSup counterExample := WithBot.semilatticeSup

instance : OrderTop counterExample := WithBot.orderTop

instance : OrderBot counterExample := WithBot.orderBot

instance : Fintype counterExample := instFintypeWithTop

instance : BoundedOrder counterExample := WithBot.instBoundedOrder

instance : Lattice counterExample where
  inf x y := match x, y with
    | _, ⊥ => ⊥
    | ⊥, _ => ⊥
    | some ⟨⟨x1, x2⟩, hx⟩, some ⟨⟨y1, y2⟩, hy⟩ => by
      by_cases H : (max x1 y1).val + max x2 y2 ≤ 2
      case pos => exact some ⟨⟨max x1 y1, max x2 y2⟩, H⟩
      case neg => exact ⊥
  inf_le_left x y := match x, y with
    | ⊥, ⊥ => by simp
    | ⊥, some _ => by simp
    | some _, none => by simp
    | some ⟨⟨x1, x2⟩, hx⟩, some ⟨⟨y1, y2⟩, hy⟩ => by
      simp only
      split_ifs
      · refine WithBot.coe_le_coe.mpr ?_
        change _ ≤ _ ∧ _ ≤ _
        simp
      · exact bot_le
  inf_le_right x y := match x, y with
    | ⊥, ⊥ => by simp
    | ⊥, some _ => by simp
    | some _, none => by simp
    | some ⟨⟨x1, x2⟩, hx⟩, some ⟨⟨y1, y2⟩, hy⟩ => by
      simp only
      split_ifs
      · refine WithBot.coe_le_coe.mpr ?_
        change _ ≤ _ ∧ _ ≤ _
        simp
      · exact bot_le
  le_inf x y z hxz hyz := match y, z with
    | ⊥, ⊥ => by
      rw [le_bot_iff] at hxz
      simpa
    | ⊥, some _ => by
      rw [le_bot_iff] at hxz
      simpa
    | some _, ⊥ => by
      rw [le_bot_iff] at hyz
      subst x
      simp
    | some ⟨⟨x1, x2⟩, hx⟩, some ⟨⟨y1, y2⟩, hy⟩ => by
      simp only
      match x with
      | none => exact bot_le
      | some ⟨⟨z1, z2⟩, hz⟩ =>
        obtain ⟨hxz1, hxz2⟩ := WithBot.coe_le_coe.mp hxz
        obtain ⟨hyz1, hyz2⟩ := WithBot.coe_le_coe.mp hyz
        simp only at hxz1 hxz2 hyz1 hyz2
        have hzz : (max x1 y1).val + max x2 y2 ≤ 2 := by
          refine le_trans ?_ hz
          simp only [Fin.coe_max]
          omega
        simp only [hzz, ↓reduceDIte, ge_iff_le]
        refine WithBot.coe_le_coe.mpr ?_
        change _ ≤ _ ∧ _ ≤ _
        simp_all

noncomputable instance : CompleteLattice counterExample := Fintype.toCompleteLattice counterExample

def mk' (n m : Fin 3) : counterExample := if H : n.val + m ≤ 2 then some ⟨(n, m), H⟩ else ⊥
notation "c(" n "," m ")" => counterExample.mk' n m

@[simp]
lemma mk'_inj {n m n' m'} (hn : n.val + m.val ≤ 2) (hn' : n'.val + m'.val ≤ 2) :
    c(n, m) = c(n', m') ↔ n = n' ∧ m = m' := by
  unfold mk'
  simp [hn, hn']
  refine WithBot.coe_inj.trans ?_
  rw [Subtype.ext_iff]
  simp

lemma inf_eq {n n' m m'} (hn : n.val + m.val ≤ 2) (hn' : n'.val + m'.val ≤ 2) :
    c(n, m) ⊓ c(n', m') = c(max n n', max m m') := by
  unfold mk'
  simp [hn, hn']
  rfl

lemma sup_eq {n n' m m'} (hn : n.val + m.val ≤ 2) (hn' : n'.val + m'.val ≤ 2) :
    c(n, m) ⊔ c(n', m') = c(min n n', min m m') := by
  unfold mk'
  have H : (min n n').val + ↑(min m m') ≤ 2 := by simp_all; omega
  simp only [hn, ↓reduceDIte, hn', H]
  rfl

@[simp]
lemma eq_bot_iff {n m} : c(n, m) = ⊥ ↔ n.val + m.val > 2 := by
  unfold mk'
  simp

@[simp]
lemma bot_eq_iff {n m} : ⊥ = c(n, m) ↔ n.val + m.val > 2 := by
  rw [eq_comm]
  simp

@[simp]
lemma top_eq_00 : c(0, 0) = ⊤ := by rfl

lemma le_iff {n n' m m'} (hn : n.val + m.val ≤ 2) (hn' : n'.val + m'.val ≤ 2) :
    c(n, m) ≤ c(n', m') ↔ n' ≤ n ∧ m' ≤ m := by
  unfold mk'
  simp [hn, hn']
  refine WithBot.coe_le_coe.trans ?_
  rfl

def A : Partition counterExample where
  parts := {c(2, 0), c(1, 1)}
  indep := by
    have h1 : {c(2, 0), c(1, 1)} \ {c(2, 0)} = ({c(1, 1)} : Set _) := by aesop
    have h2 : {c(2, 0), c(1, 1)} \ {c(1, 1)} = ({c(2, 0)} : Set _) := by aesop
    rintro x (rfl | rfl) <;> simp only [disjoint_iff, h1, h2, sSup_singleton]
    <;> rw [inf_eq (by omega) (by omega)] <;> simp
  bot_not_mem := by simp

def B : Partition counterExample where
  parts := {c(1, 1), c(0, 2)}
  indep := by
    have h1 : {c(1, 1), c(0, 2)} \ {c(1, 1)} = ({c(0, 2)} : Set _) := by aesop
    have h2 : {c(1, 1), c(0, 2)} \ {c(0, 2)} = ({c(1, 1)} : Set _) := by aesop
    rintro x (rfl | rfl) <;> simp only [disjoint_iff, h1, h2, sSup_singleton]
    <;> rw [inf_eq (by omega) (by omega)] <;> simp
  bot_not_mem := by simp

lemma not_sSupIndep_20_11_02 : ¬ sSupIndep {c(2, 0), c(1, 1), c(0, 2)} := by
  intro H
  specialize H (by simp : c(1, 1) ∈ _)
  have h1 : {c(2, 0), c(1, 1), c(0, 2)} \ {c(1, 1)} = ({c(2, 0), c(0, 2)} : Set _) := by aesop
  rw [h1, sSup_pair, sup_eq (by omega) (by omega)] at H
  simp at H

def C : Partition counterExample where
  parts := {c(2, 0), c(0, 1)}
  indep := by
    have h1 : {c(2, 0), c(0, 1)} \ {c(2, 0)} = ({c(0, 1)} : Set _) := by aesop
    have h2 : {c(2, 0), c(0, 1)} \ {c(0, 1)} = ({c(2, 0)} : Set _) := by aesop
    rintro x (rfl | rfl) <;> simp only [disjoint_iff, h1, h2, sSup_singleton]
    <;> rw [inf_eq (by omega) (by omega)] <;> simp
  bot_not_mem := by simp

def D : Partition counterExample where
  parts := {c(1, 0), c(0, 2)}
  indep := by
    have h1 : {c(1, 0), c(0, 2)} \ {c(1, 0)} = ({c(0, 2)} : Set _) := by aesop
    have h2 : {c(1, 0), c(0, 2)} \ {c(0, 2)} = ({c(1, 0)} : Set _) := by aesop
    rintro x (rfl | rfl) <;> simp only [disjoint_iff, h1, h2, sSup_singleton]
    <;> rw [inf_eq (by omega) (by omega)] <;> simp
  bot_not_mem := by simp

lemma AC : A ≤ C := by
  intro x hxA
  change x ∈ ({c(2, 0), c(1, 1)} : Set _) at hxA
  change ∃ y ∈ ({c(2, 0), c(0, 1)} : Set _), x ≤ y
  obtain (rfl | rfl) := hxA
  · use c(2, 0)
    simp
  · use c(0, 1)
    simp [le_iff]

lemma BD : B ≤ D := by
  intro x hxB
  change x ∈ ({c(1, 1), c(0, 2)} : Set _) at hxB
  change ∃ y ∈ ({c(1, 0), c(0, 2)} : Set _), x ≤ y
  obtain (rfl | rfl) := hxB
  · use c(1, 0)
    simp [le_iff]
  · use c(0, 2)
    simp

lemma AD : A ≤ D := by
  intro x hxA
  change x ∈ ({c(2, 0), c(1, 1)} : Set _) at hxA
  change ∃ y ∈ ({c(1, 0), c(0, 2)} : Set _), x ≤ y
  obtain (rfl | rfl) := hxA
  · use c(1, 0)
    simp [le_iff]
  · use c(1, 0)
    simp [le_iff]

lemma BC : B ≤ C := by
  intro x hxB
  change x ∈ ({c(1, 1), c(0, 2)} : Set _) at hxB
  change ∃ y ∈ ({c(2, 0), c(0, 1)} : Set _), x ≤ y
  obtain (rfl | rfl) := hxB
  · use c(0, 1)
    simp [le_iff]
  · use c(0, 1)
    simp [le_iff]

lemma nCD : ¬ C ≤ D := by
  intro H
  obtain ⟨y, hyD, hy⟩ := H c(0, 1) (by simp : _ ∈ ({c(2, 0), c(0, 1)} : Set _))
  change y ∈ ({c(1, 0), c(0, 2)} : Set _) at hyD
  obtain (rfl | rfl) := hyD <;>
  · rw [le_iff (by omega) (by omega)] at hy
    simp at hy

lemma nDC : ¬ D ≤ C := by
  intro H
  obtain ⟨y, hyC, hy⟩ := H c(1, 0) (by simp : _ ∈ ({c(1, 0), c(0, 2)} : Set _))
  change y ∈ ({c(2, 0), c(0, 1)} : Set _) at hyC
  obtain (rfl | rfl) := hyC <;>
  · rw [le_iff (by omega) (by omega)] at hy
    simp at hy
