import Matroid.Connectivity.Triangle

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g : α} {b c d : Bool}
    {J : Bool → List α} {x : Bool → α}

open Set List

@[simp]
lemma cond_self_left {α : Sort*} {i : Bool} {a b c : α} :
    (bif i then (bif i then a else b) else c : α) = bif i then a else c := by
  grind

@[simp]
lemma cond_self_right {α : Sort*} {i : Bool} {a b c : α} :
    (bif i then a else (bif i then b else c) : α) = bif i then a else c := by
  grind

namespace Matroid

def bDual (M : Matroid α) (b : Bool) : Matroid α := bif b then M✶ else M

@[simp]
lemma bDual_true (M : Matroid α) : M.bDual true = M✶ := rfl

@[simp]
lemma bDual_false (M : Matroid α) : M.bDual false = M := rfl

@[simp, grind =]
lemma bDual_ground (M : Matroid α) (b : Bool) : (M.bDual b).E = M.E := by cases b <;> simp

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

lemma IsTriangle.isNonloop_bDual_of_mem (h : M.IsTriangle T) (heT : e ∈ T) {b : Bool} :
    (M.bDual b).IsNonloop e := by
  cases b
  · exact h.isNonloop_of_mem heT
  exact h.dual_isTriad.isCocircuit.isNonloop_of_mem heT

variable {J : Bool → List α}

/-- A fan of a matroid `M` is a duplicate-free sequence `[e₀, f₀, e₁, f₁, ...]` of elements of `M`,
where consecutive triples alternate between being triangles and being triads.
The fan may start and end with either triangles or triads;
if each pair of consecutive `eᵢ` belongs to a common triangle,
then the `eᵢ` are the 'joints' of the fan, and the `fᵢ` are 'cojoints'.

Formally, if `J : Bool → List α` and `b c : Bool`, the predicate `M.IsFan J b c` means that
`J false` is the list of joints, `J true` is the list of cojoints, and `b c` indicate respectively
whether the first element is a cojoint, and whether the last element is a cojoint.

For example, if `{e,f,g}` is a triangle of `M`, then the fan `e, f, g` corresponds to the
statement `M.IsFan J false false`, with `J false = [e, g]` and `J true = [g]`.
(The `false false` means that the fan begins and ends on joints.)

If, additionally, `{f,g,h}` is a triad of `M`, then the fan `e, f, g, h` corresponds to the
statement `M.IsFan J false true`, with `J false = [e,g]` and `J true = [h,f]`. -/
inductive IsFan : Matroid α → (Bool → List α) → Bool → Bool → Prop where
  | of_isTriangle (M e f g) (hT : M.IsTriangle {e, f, g}) :
      IsFan M (fun i ↦ bif i then [f] else [e,g]) false false
  | of_dual' (M J c) (h : IsFan M✶ (fun i ↦ J (!i)) false (!c)) : IsFan M J true c
  | cons_triangle' (M) (J : Bool → List α) (x : Bool → α) (e c)
    (h : IsFan M (fun i ↦ x i :: J i) true c) (he : ∀ i, e ∉ J i)
    (hT : M.IsTriangle {e, x true, x false}) :
      IsFan M (fun i ↦ bif i then x i :: J i else e :: x i :: J i) false c

lemma IsFan.cons_triangle (h : IsFan M (fun i ↦ x i :: J i) true c) (he : ∀ i, e ∉ J i)
    (hT : M.IsTriangle {e, x true, x false}) :
    IsFan M (fun i ↦ bif i then x i :: J i else e :: x i :: J i) false c :=
  IsFan.cons_triangle' _ _ _ _ _ h he hT

lemma IsTriangle.isFan (hT : M.IsTriangle {e, f, g}) :
    M.IsFan (fun i ↦ bif i then [f] else [e,g]) false false :=
  IsFan.of_isTriangle _ _ _ _ hT

lemma IsFan.dual (h : M.IsFan J b c) : M✶.IsFan (fun i ↦ J (!i)) (!b) (!c) := by
  induction h with
  | of_isTriangle M e f g hT => exact of_dual' _ _ _ <| by simpa using hT.isFan
  | of_dual' M J c h ih => exact h
  | cons_triangle' M J x e c h he hT ih =>
    exact of_dual' _ _ _ <| by simpa using cons_triangle' _ _ _ _ _ h he hT

lemma isFan_dual_iff : M✶.IsFan J b c ↔ M.IsFan (fun i ↦ J (!i)) (!b) (!c) :=
  ⟨fun h ↦ by simpa using h.dual, fun h ↦ by simpa using h.dual⟩

alias ⟨IsFan.of_dual, _⟩ := isFan_dual_iff

lemma IsTriad.isFan (hT : M.IsTriad {e, f, g}) :
    M.IsFan (fun i ↦ bif i then [e, g] else [f]) true true := by
  simpa using hT.dual_isTriangle.isFan.dual

lemma IsFan.cons_triad (h : IsFan M (fun i ↦ x i :: J i) false c) (he : ∀ i, e ∉ J i)
    (hT : M.IsTriad {e, x true, x false}) :
    IsFan M (fun i ↦ bif i then e :: x i :: J i else x i :: J i) true c := by
  simpa using (h.dual.cons_triangle (fun i ↦ he (!i)) hT.dual_isTriangle.swap_right).of_dual

lemma IsFan.cons_isTriangle_bDual (h : IsFan M (fun i ↦ x i :: J i) b c) (he : ∀ i, e ∉ J i)
    (hT : (M.bDual (!b)).IsTriangle {e, x b, x (!b)}) :
    IsFan M (fun i ↦ bif (i == b) then x i :: J i else e :: x i :: J i) (!b) c := by
  cases b
  · simpa using h.cons_triad he <| by simpa using hT.swap_right
  simpa using h.cons_triangle he hT

lemma IsFan.ne_nil (h : M.IsFan J b c) {i : Bool} : (J i) ≠ [] := by
  induction h generalizing i with
  | of_dual' M J c h ih => simpa using @ih (!i)
  | _ => cases i <;> simp

lemma IsFan.exists_eq_cons_cons (h : M.IsFan J b c) : ∃ (y : Bool → α) (J' : Bool → List α),
    J = fun i ↦ y i :: J' i :=
  ⟨fun i ↦ (J i).head h.ne_nil, fun i ↦ (J i).tail, by simp⟩

lemma IsFan.cons_isTriangle_bDual_head (h : IsFan M J b c) (he : ∀ i, e ∉ J i)
    (hT : (M.bDual (!b)).IsTriangle {e, (J b).head h.ne_nil, (J !b).head h.ne_nil}) :
    M.IsFan (fun i ↦ bif (i == b) then J i else e :: J i) (!b) c := by
  obtain ⟨y, J, rfl⟩ := h.exists_eq_cons_cons
  simp only [List.mem_cons, not_or, List.head_cons] at *
  exact h.cons_isTriangle_bDual (fun i ↦ (he i).2) hT

lemma IsFan.length_eq_add (h : M.IsFan J b c) :
    (J b).length = (J (!b)).length + (bif (b == c) then 1 else 0) := by
  induction h with
  | of_isTriangle => simp
  | of_dual' M J c h ih => simpa using ih
  | cons_triangle' M J x e c => cases c <;> simp_all

lemma IsFan.length_eq_length_of_ne (h : M.IsFan J b c) (hbc : b ≠ c) (d₁ d₂ : Bool) :
    (J d₁).length = (J d₂).length := by
  obtain rfl : c = !b := by cases c <;> grind
  obtain rfl | rfl := d₁.eq_or_eq_not d₂
  · rfl
  obtain rfl | rfl := d₂.eq_or_eq_not b <;>
  simp [h.length_eq_add]

lemma IsFan.length_eq_length_of_bnot (h : M.IsFan J b (!b)) (d₁ d₂ : Bool) :
    (J d₁).length = (J d₂).length :=
  h.length_eq_length_of_ne (by simp) ..

lemma IsFan.length_eq_add_one (h : M.IsFan J b b) : (J b).length = (J (!b)).length + 1 := by
  simp [h.length_eq_add]

lemma IsFan.length_le_add_one (h : M.IsFan J b c) (d) : (J d).length ≤ (J (!d)).length + 1 := by
  obtain rfl | rfl := d.eq_or_eq_not b <;> grind [h.length_eq_add]

lemma IsFan.length_le (h : M.IsFan J b c) (hbc : ¬ (b = d ∧ b = c)) :
    (J d).length ≤ (J (!d)).length := by
  obtain rfl | rfl := b.eq_or_eq_not d <;> grind [h.length_eq_add]

lemma IsFan.two_le_length (h : M.IsFan J b c) : 2 ≤ (J b).length := by
  induction h with | _ => simp_all

lemma IsFan.cons_cons (h : M.IsFan J b c) (hxJ : ∀ i j, x i ∉ J j)
    (h1 : (M.bDual (!b)).IsTriangle {x (!b), (J b).head h.ne_nil, (J !b).head h.ne_nil})
    (h2 : (M.bDual b).IsTriangle {x b, x !b, (J b).head h.ne_nil}) :
    M.IsFan (fun i ↦ x i :: J i) b c := by
  obtain ⟨y, J, rfl⟩ := h.exists_eq_cons_cons
  simp only [List.head_cons] at h1 h2
  simp only [List.mem_cons, not_or] at hxJ
  have h' := h.cons_isTriangle_bDual (fun i ↦ (hxJ (!b) i).2) h1
  have h'' := h'.cons_isTriangle_bDual_head (e := x b) (fun i ↦ ?_) (by simpa)
  · convert h'' using 2 with i
    · obtain rfl | rfl := i.eq_or_eq_not b <;> simp
    simp
  obtain rfl | rfl := i.eq_or_eq_not b <;> simp [hxJ, h2.ne₁₂]

lemma IsFan.length_aux {d k} (h : M.IsFan J b c) (hlt : k + 1 < (J d).length) :
    (k + bif b == d then 0 else 1) < (J !d).length := by
  obtain rfl | rfl := b.eq_or_eq_not d
  · grw [h.length_le_add_one] at hlt
    lia
  simp only [Bool.not_beq_self, cond_false]
  grw [h.length_eq_add]
  lia

lemma IsFan.disjoint (h : M.IsFan J b c) (d : Bool) : Disjoint (J d) (J !d) := by
  wlog hd : d = false generalizing d with aux
  · cases d
    · apply aux _ rfl
    exact (aux _ rfl).symm
  subst hd
  induction h with
  | of_isTriangle M e f g hT => simp [hT.ne₁₂.symm, hT.ne₂₃]
  | of_dual' M J c h ih => simpa using ih.symm
  | cons_triangle' M J x e c h he hT ih => simp_all [hT.ne₁₂.symm]

lemma IsFan.isTriangle_bDual {d k} (h : M.IsFan J b c) (hk : k + 1 < (J d).length) :
    (M.bDual d).IsTriangle {(J d)[k], (J !d)[k + bif (b == d) then 0 else 1]'(h.length_aux hk),
      (J d)[k + 1]} := by
  induction h generalizing d k with
  | of_isTriangle M e f g hT =>
    obtain rfl | rfl := d
    · simpa [show k = 0 by grind]
    simp at hk
  | of_dual' M J c h ih => simpa using ih (d := !d) (by simpa)
  | cons_triangle' M J x e c h he hT ih =>
    obtain rfl | rfl := d
    · obtain rfl | k := k
      · simp_all
      simpa using ih (d := false) (by simpa using hk)
    simpa using ih (d := true) (by simpa using hk)

lemma IsFan.isTriangle_bDual_self {k} (h : M.IsFan J b c) (hk : k + 1 < (J b).length) :
    (M.bDual b).IsTriangle {(J b)[k], (J !b)[k]'(le_self_add.trans_lt (h.length_aux hk)),
      (J b)[k + 1]} := by
  simpa using h.isTriangle_bDual hk

lemma IsFan.isTriangle_bDual_not {k} (h : M.IsFan J b c) (hk : k + 1 < (J (!b)).length) :
    (M.bDual (!b)).IsTriangle {(J (!b))[k], (J b)[k + 1]'(by simpa using h.length_aux hk),
      (J (!b))[k + 1]} := by
  simpa using h.isTriangle_bDual hk

lemma IsFan.isTriangle_bDual_zero_one (h : M.IsFan J b c) :
    (M.bDual b).IsTriangle {(J b)[0]'(length_pos_iff.2 h.ne_nil),
      (J !b)[0]'(length_pos_iff.2 h.ne_nil), (J b)[1]'h.two_le_length} :=
  h.isTriangle_bDual_self (k := 0) (by simpa using h.two_le_length)

lemma IsFan.concat (h : M.IsFan J b c) (he : ∀ i, e ∉ J i)
    (hT : (M.bDual (!c)).IsTriangle {(J !c).getLast h.ne_nil, (J c).getLast h.ne_nil, e}) :
    M.IsFan (fun i ↦ bif (i == c) then J i else (J i).concat e) b (!c) := by
  induction h with
  | of_isTriangle M x y z hT' =>
    replace hT : M.IsTriad {y, z, e} := by simpa using hT
    simp_rw [Bool.apply_cond (f := fun L ↦ List.concat L e), beq_false, Bool.cond_not,
      cond_self_left, cond_self_right, concat_eq_append, cons_append, nil_append, Bool.not_false]
    convert hT.isFan.cons_isTriangle_bDual_head (e := x) ?_ (by simpa) using 2 with i
    · cases i <;> simp
    simp [hT'.ne₁₃, hT'.ne₁₂, show x ≠ e by rintro rfl; simp at he]
  | of_dual' M J c h ih =>
    simp only [he, not_false_eq_true, Bool.not_not, bDual_dual, hT, forall_const] at ih
    convert ih.of_dual using 2 with i
    obtain rfl | rfl := i.eq_or_eq_not c <;> simp
  | cons_triangle' M J x e' c h he' hT' ih =>
    simp only [Bool.forall_bool, cond_false, mem_cons, not_or, cond_true] at he
    specialize ih (by simp_all) ?_
    · convert hT using 1
      cases c <;> simp
    simp only [concat_eq_append, cons_append] at ih
    convert ih.cons_isTriangle_bDual_head (e := e') ?_ ?_ using 2 with i
    . cases c <;> cases i <;> simp
    · cases c <;> simp_all [hT'.ne₁₂, hT'.ne₁₃, Ne.symm he.1.1]
    cases c <;> simpa

lemma IsFan.reverse (h : M.IsFan J b c) : M.IsFan (fun i ↦ (J i).reverse) c b := by
  induction h with
  | of_isTriangle M e f g hT =>
    convert hT.reverse.isFan using 2 with i
    cases i <;> rfl
  | of_dual' M J c h ih => simpa using ih.of_dual
  | cons_triangle' M J x e c h he hT ih =>
    simpa [Bool.apply_cond] using ih.concat (by simp [he, hT.ne₁₂, hT.ne₁₃])
      (by simpa using hT.reverse)

  @[simp]
  lemma isFan_reverse_iff : M.IsFan (fun i ↦ (J i).reverse) b c ↔ M.IsFan J c b :=
    ⟨fun h ↦ by simpa using h.reverse, IsFan.reverse⟩

lemma IsFan.tail (h : M.IsFan J b c) (h_length : 1 < (J (!b)).length) :
    M.IsFan (fun i ↦ bif (i == b) then (J i).tail else J i) (!b) c := by
  induction h with
  | of_isTriangle => simp at h_length
  | of_dual' M J c h ih => simpa using (ih (by simpa using h_length)).of_dual
  | cons_triangle' M J x e c h => convert h using 2 with i; cases i <;> simp

lemma IsFan.length_eq_length (h : M.IsFan J b c) : (J b).length = (J c).length := by
  obtain rfl | rfl := b.eq_or_eq_not c <;> simp_all [h.length_eq_add]

lemma IsFan.length_bnot_eq_length_bnot (h : M.IsFan J b c) : (J (!b)).length = (J (!c)).length := by
  obtain rfl | rfl := b.eq_or_eq_not c <;> simp_all [h.length_eq_add]

lemma IsFan.tail_tail (h : M.IsFan J b c) (hlen : 1 + (bif b == c then 0 else 1) < (J (!b)).length) :
    M.IsFan (fun i ↦ (J i).tail) b c := by
  convert (h.tail (by lia)).tail ?_ using 2 with i
  · obtain rfl | rfl := i.eq_or_eq_not b <;> grind
  · simp
  obtain rfl | rfl := b.eq_or_eq_not c
  · simp_all [h.length_eq_add]
  simp_all only [Bool.not_beq_self, cond_false, Nat.reduceAdd, Bool.not_not, BEq.rfl, cond_true,
    length_tail, h.length_eq_add]
  lia

lemma IsFan.drop (h : M.IsFan J b c) {k} (hk : k + (bif b == c then 0 else 1) < (J !b).length) :
    M.IsFan (fun i ↦ (J i).drop k) b c := by
  induction k with
  | zero => simpa
  | succ k ih => simpa using (ih (by lia)).tail_tail <| by simp; lia

lemma IsFan.take_of_ne (h : M.IsFan J b c) (hbc : b ≠ c) {k} (hk : 2 ≤ k) :
    M.IsFan (fun i ↦ (J i).take k) b c := by
  obtain rfl : c = !b := by cases b <;> grind
  obtain hle | hlt := le_or_gt (J b).length k
  · convert h using 2 with i
    rw [take_of_length_le <| by rwa [h.length_eq_length_of_bnot i b]]
  obtain ⟨d, hd, hlen⟩ := exists_pos_add_of_lt hlt
  convert (h.reverse.drop (k := d) ?_).reverse using 2 with i
  · simp [drop_reverse, h.length_eq_length_of_bnot i b, ← hlen]
  simp only [Bool.not_beq_self, cond_false, Bool.not_not, length_reverse]
  lia

lemma IsFan.isNonloop_bDual_of_mem (h : M.IsFan J b c) {d : Bool} {d' : Bool} (he : e ∈ J d) :
    (M.bDual d').IsNonloop e := by
  induction h generalizing d d' with
  | of_isTriangle M x y z hT => apply hT.isNonloop_bDual_of_mem <| by grind
  | of_dual' M J c h ih => simpa using ih (d := !d) (d' := !d') (by simpa)
  | cons_triangle' M J x e' c h he' hT ih =>
    cases d
    · obtain rfl | he := mem_cons.1 he
      · exact hT.isNonloop_bDual_of_mem (by simp)
      exact ih he
    exact ih (by simpa using he)

lemma IsFan.isNonloop_of_mem (h : M.IsFan J b c) {d : Bool} (he : e ∈ J d) : M.IsNonloop e :=
  h.isNonloop_bDual_of_mem (d' := False) he

lemma IsFan.subset_ground (h : M.IsFan J b c) {d : Bool} : {x | x ∈ J d} ⊆ M.E :=
  fun _ he ↦ (h.isNonloop_bDual_of_mem (d' := false) he).mem_ground

lemma IsFan.subset_ground_bDual (h : M.IsFan J b c) {d' : Bool} :
    {x | x ∈ J d'} ⊆ (M.bDual d).E := by
  simpa using h.subset_ground (d := d')

lemma IsFan.indep_bDual (h : M.IsFan J b c) (d : Bool) (hd : ¬ (b = c ∧ c = d)) :
    (M.bDual d).Indep {x | x ∈ J d} := by
  wlog hdf : d = false generalizing M J b c d with aux
  · obtain rfl : d = true := by simpa using hdf
    simpa using aux h.dual false (by grind) rfl
  wlog hb : b = true generalizing J b c with aux
  · simpa using aux h.reverse (by grind) (by grind)
  subst hdf hb
  clear hd
  rw [indep_iff_forall_subset_not_isCircuit (by exact h.subset_ground_bDual)]
  intro C hCss hC
  obtain ⟨i, hi, hiC⟩ : ∃ (i : ℕ) (h0 : i + 1 < (J false).length), (J false)[i] ∈ C := by
    obtain h0 | ⟨K, u, hKu⟩ := (J false).eq_nil_or_concat; simp [h.ne_nil h0]
    obtain hC' : C ⊆ insert u {a | a ∈ K} := by simpa [hKu, setOf_or] using hCss
    obtain h0 | ⟨e, heC, heK⟩ := Set.disjoint_or_nonempty_inter C {x | x ∈ K}
    · rw [← union_singleton, ← diff_subset_iff, h0.sdiff_eq_left] at hC'
      exfalso
      exact ((h.isNonloop_of_mem (d := false) (by simp [hKu])).indep.subset hC').not_dep hC.dep
    obtain ⟨i, hi, hiC⟩ := (exists_mem_iff_getElem (p := (· ∈ C))).1 ⟨e, heK, heC⟩
    refine ⟨i, by simpa [hKu], ?_⟩
    simp_rw [hKu, concat_eq_append, getElem_append_left hi]
    assumption
  have hT : M✶.IsTriangle _ := h.isTriangle_bDual (d := true) (k := i) ?_
  · simp only [Bool.not_true, BEq.rfl, cond_true, add_zero, dual_isTriangle_iff] at hT
    have hnt := hC.isCocircuit_inter_nontrivial hT.isCocircuit ⟨_, hiC, by simp⟩
    obtain ⟨f, ⟨hfC, rfl | rfl | rfl⟩, hne⟩ := hnt.exists_ne (J false)[i]
    · exact List.disjoint_right.1 (h.disjoint true) (hCss hfC) (by simp)
    · exact hne rfl
    exact List.disjoint_right.1 (h.disjoint true) (hCss hfC) <| getElem_mem _
  grw [← Bool.not_false, ← h.length_le (by simp)]
  exact hi
