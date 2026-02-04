import Matroid.Connectivity.Triangle

-- induction h with
--   | of_empty b => sorry
--   | of_single b e he => sorry
--   | of_pair b e f h hef => sorry
--   | cons b c e x y J K hT heJ heK h IH => sorry

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y z : α} {b c : Bool}

namespace Matroid

def bDual (M : Matroid α) (b : Bool) : Matroid α := bif b then M✶ else M

@[simp]
lemma bDual_true (M : Matroid α) : M.bDual true = M✶ := rfl

@[simp]
lemma bDual_false (M : Matroid α) : M.bDual false = M := rfl

@[simp]
lemma bDual_dual (M : Matroid α) (b : Bool) : M✶.bDual b = M.bDual !b := by
  cases b with | _ => simp

@[simp]
lemma dual_bDual (M : Matroid α) (b : Bool) : (M.bDual b)✶ = M.bDual !b := by
  cases b with | _ => simp

lemma bDual_not_dual (M : Matroid α) (b : Bool) : M✶.bDual (!b) = M.bDual b := by
  simp

@[simp]
lemma bDual_isCocircuit_iff : (M.bDual b).IsCocircuit X ↔ (M.bDual (!b)).IsCircuit X := by
  simp [isCocircuit_def]

lemma bDual_isTriad_iff : (M.bDual b).IsTriad X ↔ (M.bDual (!b)).IsTriangle X := by
  simp [← dual_isTriad_iff]

lemma bDual_coindep_iff : (M.bDual b).Coindep X ↔ (M.bDual (!b)).Indep X := by
  simp [coindep_def]

@[simp]
lemma bDual_bDual : (M.bDual b).bDual c = M.bDual (b ^^ c) := by
  cases b <;> simp [bDual]

open List

variable {J : Bool → List α}

inductive IsFanAux (M : Matroid α) : List α → List α → Bool → Bool → Prop where
  | of_empty b : IsFanAux M [] [] b (!b)
  | of_single_false e (he : M.IsNonloop e) : IsFanAux M [e] [] false false
  | of_single_true e (he : M✶.IsNonloop e) : IsFanAux M [] [e] true true
  | of_pair_false e f (h : M✶.Indep {e,f}) (hef : e ≠ f) : IsFanAux M [e] [f] false true
  | of_pair_true e f (h : M.Indep {e,f}) (hef : e ≠ f) : IsFanAux M [e] [f] true false
  | cons_false e x y J K b (h : M.IsTriangle {e, x, y}) (heJ : e ∉ J) (heK : e ∉ K)
      (h_fan : IsFanAux M (y :: J) (x :: K) true b) : IsFanAux M (e :: y :: J) (x :: K) false b
  | cons_true e x y J K b (h : M✶.IsTriangle {e, x, y}) (heJ : e ∉ J) (heK : e ∉ K)
      (h_fun : IsFanAux M (y :: J) (x :: K) false b) : IsFanAux M (y :: J) (e :: x :: K) true b

def IsFan' (M : Matroid α) (J : Bool → List α) (b c : Bool) : Prop :=
    M.IsFanAux (J false) (J true) b c

lemma IsFanAux.dual {J K} (h : M.IsFanAux J K b c) : M✶.IsFanAux K J (!b) (!c) := by
  induction h with
  | of_empty b => exact IsFanAux.of_empty !b
  | of_single_false e he => exact of_single_true (M := M✶) e (by simpa)
  | of_single_true e he => exact of_single_false (M := M✶) e (by simpa)
  | of_pair_false e f h hef =>
      exact of_pair_true (M := M✶) f e (by simpa [Set.pair_comm] using h) hef.symm
  | of_pair_true e f h hef =>
      exact of_pair_false (M := M✶) f e (by simpa [Set.pair_comm] using h) hef.symm
  | cons_false e x y J K b h heJ heK h_fan IH =>
      exact cons_true (M := M✶) e y x K J (!b) (by simpa [Set.pair_comm] using h) heK heJ IH
  | cons_true e x y J K b h heJ heK h_fan IH =>
      exact cons_false (M := M✶) e y x K J (!b) (by simpa [Set.pair_comm] using h) heK heJ IH

@[simp]
lemma isFanAux_dual_iff {J K} : M✶.IsFanAux J K b c ↔ M.IsFanAux K J (!b) (!c) :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

lemma isFanAux_dual_not_iff {J K} : M✶.IsFanAux J K (!b) (!c) ↔ M.IsFanAux K J b c :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

alias ⟨IsFanAux.of_dual, _⟩ := isFanAux_dual_iff

lemma Indep.isFanAux (h : M.Indep {e,f}) (hef : e ≠ f) : M.IsFanAux [e] [f] true false :=
  IsFanAux.of_pair_true e f h hef

@[simp]
lemma isFanAux_empty_single_iff :
    M.IsFanAux [] [e] b c ↔ b = true ∧ c = true ∧ M✶.IsNonloop e := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases h with | _ => simpa
  rintro ⟨rfl, rfl, he⟩
  exact IsFanAux.of_single_true _ he

@[simp]
lemma isFanAux_single_empty_iff :
    M.IsFanAux [e] [] b c ↔ b = false ∧ c = false ∧ M.IsNonloop e := by
  rw [← isFanAux_dual_not_iff, isFanAux_empty_single_iff]
  simp

lemma isFanAux_single_single_iff : M.IsFanAux [e] [f] b c ↔ e ≠ f ∧
    ((b = true ∧ c = false ∧ M.Indep {e,f}) ∨ (b = false ∧ c = true ∧ M✶.Indep {e,f})) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases h with | _ => simp_all
  rintro ⟨hef, ⟨rfl, rfl, h_ind⟩ | ⟨rfl, rfl, h_ind⟩⟩
  · apply IsFanAux.of_pair_true <;> assumption
  apply IsFanAux.of_pair_false <;> assumption

lemma isFanAux_single_single_iff' :
    M.IsFanAux [e] [f] b c ↔ e ≠ f ∧ b = !c ∧ (M.bDual (!b)).Indep {e, f} := by
  cases b <;> simp [isFanAux_single_single_iff]

lemma IsTriangle.isFanAux (h : M.IsTriangle {e, f, g}) : M.IsFanAux [e,g] [f] false false :=
  IsFanAux.cons_false e f g [] [] false h (by simp) (by simp) <|
    by simp [isFanAux_single_single_iff', h.swap_right.indep₂₃, h.ne₂₃.symm]

lemma IsTriad.isFanAux (h : M.IsTriad {e, f, g}) : M.IsFanAux [f] [e,g] true true := by
  simpa using h.dual_isTriangle.isFanAux

lemma IsFanAux.isTriangle {J K : List α} (h : M.IsFanAux (e :: g :: J) (f :: K) false b) :
    M.IsTriangle {e, f, g} := by
  cases h with | _ => simp_all

lemma IsFanAux.isTriad {J K : List α} (h : M.IsFanAux (f :: J) (e :: g :: K) true b) :
    M.IsTriad {e, f, g} := by
  simpa using h.dual.isTriangle

lemma IsFanAux.nodup_left {J K} (h : M.IsFanAux J K b c) : J.Nodup := by
  induction h with | cons_false _ _ _ _ _ _ h => simp_all [h.ne₁₃] | _ => simp_all

lemma IsFanAux.nodup_right {J K} (h : M.IsFanAux J K b c) : K.Nodup :=
  h.dual.nodup_left

lemma IsFanAux.disjoint {J K} (h : M.IsFanAux J K b c) : Disjoint J K := by
  induction h with
  | of_pair_false e f h hef => simpa using hef.symm
  | of_pair_true e f h hef => simpa using hef.symm
  | cons_false e x y J K b h => simp_all [h.swap_left.ne₁₂]
  | cons_true e x y J K b h => simp_all [h.ne₁₃]
  | _ => simp





-- lemma IsFan'.dual (h : M.IsFan' J b c) : M✶.IsFan' (fun i ↦ J (!i)) (!b) (!c) := by
--   suffices aux : ∀ J L, M.IsFanAux J L b c → M✶.IsFanAux L J (!b) (!c) from aux _ _ h
--   clear h
--   intro J L h
--   induction h with
--   | of_empty b => exact IsFanAux.of_empty !b
--   | of_single_false e he => exact IsFanAux.of_single_true (M := M✶) e (by simpa)
--   | of_single_true e he => exact IsFanAux.of_single_false (M := M✶) e (by simpa)
--   | of_pair_false e f h hef =>
--       exact IsFanAux.of_pair_true (M := M✶) f e (by simpa [Set.pair_comm] using h) hef.symm
--   | of_pair_true e f h hef =>
--       exact IsFanAux.of_pair_false (M := M✶) f e (by simpa [Set.pair_comm] using h) hef.symm
--   | cons_false e x y J K b h h_fan IH =>
--       exact IsFanAux.cons_true (M := M✶) e y x K J (!b) (by simpa [Set.pair_comm] using h) IH
--   | cons_true e x y J K b h h_fan IH =>
--       exact IsFanAux.cons_false (M := M✶) e y x K J (!b) (by simpa [Set.pair_comm] using h) IH

-- @[simp]
-- lemma isFan'_dual_iff :

-- inductive IsFan (M : Matroid α) : (Bool → List α) → Bool → Bool → Prop where
--   | of_empty b : IsFan M (fun _ ↦ []) b (!b)
--   | of_single b e (he : (M.bDual b).IsNonloop e) :
--       IsFan M (fun i ↦ bif i == b then [e] else []) b b
--   | of_pair b e f (h : (M.bDual b).Indep {e,f}) (hef : e ≠ f) :
--       IsFan M (fun i ↦ bif i == b then [e] else [f]) (!b) b
--   | cons b c e x y (J K : List α) (hT : (M.bDual b).IsTriangle {e, x, y})
--       (heJ : e ∉ J) (heK : e ∉ K) (h : IsFan M (fun i ↦ bif (i == b) then x :: J else y :: K) b c) :
--       IsFan M (fun i ↦ bif (i == b) then e :: x :: J else y :: K) (!b) c

-- lemma IsFan.dual (h : M.IsFan J b c) : M✶.IsFan (fun i ↦ J (!i)) (!b) (!c) := by
--   induction h with
--   | of_empty b => simpa using of_empty (M := M✶) !b
--   | of_single b e he => convert of_single (M := M✶) (!b) e (by simpa) using 3; simp
--   | of_pair b e f h hef => convert of_pair (M := M✶) (!b) e f (by simpa) hef using 3; simp
--   | cons b c e x y J K hT heJ heK h IH =>
--     convert IsFan.cons (M := M✶) (!b) (!c) e x y J K (by simpa) heJ heK
--       (by convert IH using 3; simp) using 3; simp

-- @[simp]
-- lemma isFan_dual_iff : M✶.IsFan J b c ↔ M.IsFan (fun i ↦ J (!i)) (!b) (!c) :=
--   ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

-- @[simp]
-- lemma isFan_bDual_iff (d : Bool) :
--     (M.bDual d).IsFan J b c ↔ M.IsFan (fun i ↦ J (i ^^ d)) (b ^^ d) (c ^^ d) := by
--   cases d <;> simp

-- lemma Indep.isFan_pair (h : M.Indep {e,f}) (hef : e ≠ f) :
--     M.IsFan (fun i ↦ bif i then [e] else [f]) true false := by
--   rw [← M.bDual_false, Set.pair_comm] at h
--   simpa using IsFan.of_pair _ _ _ h hef.symm

-- lemma isFan_empty (M : Matroid α) (b : Bool) : M.IsFan (fun _ ↦ []) b (!b) :=
--   IsFan.of_empty b

-- lemma IsFan.nodup (h : M.IsFan J b c) (i : Bool) : Nodup (J i) := by
--   induction h with
--   | of_empty b => simp
--   | of_single b e he => simp [Bool.apply_cond]
--   | of_pair b e f h hef => simp [Bool.apply_cond]
--   | cons b c e x y J K hT heJ heK h IH =>
--     obtain rfl | rfl := i.eq_or_eq_not b
--     · simp_all [hT.ne₁₂]
--     simp_all

-- lemma IsFan.notMem_bnot_of_mem (h : M.IsFan J b c) {i} (hxi : x ∈ J i) : x ∉ J (!i) := by
--   induction h with
--   | of_empty b => simp
--   | of_single b e he => obtain rfl | rfl := b.eq_or_eq_not i <;> simp_all
--   | of_pair b e f h hef => obtain rfl | rfl := b.eq_or_eq_not i <;> simp_all [Ne.symm]
--   | cons b c e p q J K hT heJ heK h IH =>
--     obtain rfl | rfl := i.eq_or_eq_not b <;> grind [hT.ne₁₂, hT.ne₁₃]

-- lemma foo (φ : Bool → Bool) (a b : α) (i : Bool) :
--     (bif (φ i) then a else b) = bif i then (bif (φ true == true) then a else b)
--       else ((bif (φ true == true) then a else b)) := by
--   sorry


-- lemma isFan_singleton_singleton_iff {φ : Bool → Bool} :
--     M.IsFan (fun i ↦ bif i then [e] else [f]) b c ↔ e ≠ f ∧ M.Indep {e,f} := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · sorry








-- lemma IsTriangle.isFan (hM : M.IsTriangle {e,f,g}) :
--     M.IsFan (fun i ↦ bif i then [e] else [f,g]) true true := by
--   have := IsFan.cons (M := M) false true f g e [] [] ?_ (by simp) (by simp) ?_
--   simp at this

--   obtain rfl | rfl := d
--   · simpa
--   simp only [bDual_true, Bool.bne_true]
--   cases h with
--   | of_empty b => simpa using of_empty (M := M✶) (!b)
--   | of_single b e he =>
--     have := of_single (M := M✶) b e
--     convert of_single (M := M.bDual d) (b ^^ d) e ?_ using 3 with x
--     · cases b <;> cases x <;> simp
--     cases b <;> simpa using he
--   | of_pair b e f h hef =>

--     obtain rfl | rfl := c.eq_or_eq_not d
--     · have := of_pair (M := M.bDual c) true f e (by simpa) hef.symm
--       simp at this
--       simp
--     simp
--   | cons b c e x y J K hT heJ heK => sorry

  -- obtain (h1 | ⟨e, he⟩ | h3) := h
  -- · sorry

  -- cases h
  -- · convert of_empty _ (b ^^ d) using 1
  --   simp
  -- ·

  -- sorry
