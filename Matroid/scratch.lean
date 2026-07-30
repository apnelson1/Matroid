import Mathlib.Data.List.Rotate
import Matroid.Connectivity.Separation.Tutte
import Matroid.ForMathlib.List.Basic
import Matroid.ForMathlib.Parity

set_option linter.style.longLine false

open Set List

namespace Matroid

-- variable {J : Bool → List α}

variable {α : Type*} {P : α → Prop}
     {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {J : List α} {b c : Bool} {L : List ℕ}

structure Fan (M : Matroid α) where
  toList : List α
  isNonloop' : ∀ i (hi : i < toList.length) (d : Bool), (M.bDual d).IsNonloop toList[i]

namespace Fan

instance coeList : CoeOut (M.Fan) (List α) where coe F := F.toList

instance : GetElem (M.Fan) Nat α (fun t i => i < t.toList.length) where
  getElem := fun t i h => t.toList[i]

def length (F : M.Fan) : ℕ := List.length (F : List α)

instance : Membership α (M.Fan) where mem F e := e ∈ (F : List α)

@[simp]
lemma getElem_toList (F : Fan M) (i : ℕ) {hi : i < F.length} : (F : List α)[i] = F[i] := rfl

attribute [coe] Fan.toList

@[simp]
lemma mem_coeList (F : M.Fan) : e ∈ (F : List α) ↔ e ∈ F := Iff.rfl

variable {F : M.Fan}


@[simp, grind =]
lemma coe_len (F : M.Fan) : (F : List α).length = F.length := rfl

@[simp]
lemma isNonloop {hi : i < F.length} {d : Bool} : (M.bDual d).IsNonloop F[i] :=
  F.isNonloop' i hi d

-- set_option pp.all true in
@[simps]
protected def cons (F : M.Fan) (henl : ∀ d, (M.bDual d).IsNonloop e) : M.Fan where
  toList := e :: F


  isNonloop' := by
    rintro (rfl | i) hi d
    · apply henl
    simp
    have := F.getElem_toList i (hi := by grind)


    -- simp only [getElem_cons_succ]
    rw [F.getElem_toList i]
    _

    sorry


#exit


variable {α : Type} {x : α} [Zero α] [LT α]

structure PosList (α : Type) [Zero α] [LT α] where
  toList : List α
  for_all : ∀ i (hi : i < toList.length), 0 < toList[i]

instance coeList : CoeOut (PosList α) (List α) where coe l := l.toList

instance : GetElem (PosList α) Nat α (fun t i => i < t.toList.length) where
  getElem := fun t i h => t.toList[i]

instance : Membership α (PosList α) where mem l x := x ∈ (l : List α)

@[simp]
lemma getElem_toList (l : PosList α) (i : ℕ) {hi : i < (l : List α).length} :
    (l : List α)[i] = l[i] := rfl

namespace Fan

instance coeList : CoeOut (PosList α) (List α) where coe l := l.toList

instance : GetElem (PosList α) Nat α (fun t i => i < t.toList.length) where
  getElem := fun t i h => t.toList[i]

def length (l : PosList α) : ℕ := List.length (l : List α)

instance : Membership α (PosList α) where mem l x := x ∈ (l : List α)


attribute [coe] PosList.toList

@[simp]
lemma mem_coeList (l : PosList α) {x : α} : x ∈ (l : List α) ↔ x ∈ l := Iff.rfl

variable {l : PosList α}


-- macro_rules
--   | `(tactic| get_elem_tactic_extensible) =>
--     `(tactic| grind[Fan.length_ge_two, Fan.length_ge_three,
--       List.length_rotate, Nat.add_one_lt_of_bodd_eq])

-- @[simp, grind =]
-- lemma coe_len (l : PosList α) : (l : List α).length = l.length := rfl

-- set_option pp.all true in
@[simps]
protected def cons (l : PosList α) (hxpos : 0 < x) : PosList α where
  toList := x :: l
  for_all := by
    rintro (rfl | i) hi
    · simpa


    simp at hi

    have := l.getElem_toList i (hi := by grind)


    -- simp only [getElem_cons_succ]
    rw [l.getElem_toList i]
    _

    sorry
  isTriangle' := sorry
